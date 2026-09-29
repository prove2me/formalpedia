-- Prove2me | solution 1 for syracuse_descends_range_1044610_1048610
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:24.916323+00:00
-- url     : https://prove2.me/submissions/0571d64b-87f7-4838-a5ff-12cd6217bb30

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


theorem B1572869 : Blo 1044610 1572869 := bbase (se 4 (by rfl) ⟨147456, by rfl⟩ : syracuseStep 1572869 = 294913) (by norm_num)
theorem B1769485 : Blo 1044610 1769485 := bbase (se 3 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 1769485 = 663557) (by norm_num)
theorem B1179661 : Blo 1044610 1179661 := bbase (se 3 (by rfl) ⟨221186, by rfl⟩ : syracuseStep 1179661 = 442373) (by norm_num)
theorem B1572893 : Blo 1044610 1572893 := bbase (se 3 (by rfl) ⟨294917, by rfl⟩ : syracuseStep 1572893 = 589835) (by norm_num)
theorem B3538997 : Blo 1044610 3538997 := bbase (se 5 (by rfl) ⟨165890, by rfl⟩ : syracuseStep 3538997 = 331781) (by norm_num)
theorem B2359349 : Blo 1044610 2359349 := bbase (se 5 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 2359349 = 221189) (by norm_num)
theorem B1343569 : Blo 1044610 1343569 := bbase (se 2 (by rfl) ⟨503838, by rfl⟩ : syracuseStep 1343569 = 1007677) (by norm_num)
theorem B5374421 : Blo 1044610 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B8946197 : Blo 1044610 8946197 := bbase (se 6 (by rfl) ⟨209676, by rfl⟩ : syracuseStep 8946197 = 419353) (by norm_num)
theorem B1344205 : Blo 1044610 1344205 := bbase (se 3 (by rfl) ⟨252038, by rfl⟩ : syracuseStep 1344205 = 504077) (by norm_num)
theorem B1508053 : Blo 1044610 1508053 := bbase (se 7 (by rfl) ⟨17672, by rfl⟩ : syracuseStep 1508053 = 35345) (by norm_num)
theorem B10322965 : Blo 1044610 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B7570613 : Blo 1044610 7570613 := bbase (se 5 (by rfl) ⟨354872, by rfl⟩ : syracuseStep 7570613 = 709745) (by norm_num)
theorem B2983205 : Blo 1044610 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B1115537 : Blo 1044610 1115537 := bbase (se 2 (by rfl) ⟨418326, by rfl⟩ : syracuseStep 1115537 = 836653) (by norm_num)
theorem B3179989 : Blo 1044610 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B5965589 : Blo 1044610 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B3966853 : Blo 1044610 3966853 := bbase (se 4 (by rfl) ⟨371892, by rfl⟩ : syracuseStep 3966853 = 743785) (by norm_num)
theorem B2295749 : Blo 1044610 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B2066485 : Blo 1044610 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B4294741 : Blo 1044610 4294741 := bbase (se 8 (by rfl) ⟨25164, by rfl⟩ : syracuseStep 4294741 = 50329) (by norm_num)
theorem B1116289 : Blo 1044610 1116289 := bbase (se 2 (by rfl) ⟨418608, by rfl⟩ : syracuseStep 1116289 = 837217) (by norm_num)
theorem B1673389 : Blo 1044610 1673389 := bbase (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) (by norm_num)
theorem B3967157 : Blo 1044610 3967157 := bbase (se 5 (by rfl) ⟨185960, by rfl⟩ : syracuseStep 3967157 = 371921) (by norm_num)
theorem B1116361 : Blo 1044610 1116361 := bbase (se 2 (by rfl) ⟨418635, by rfl⟩ : syracuseStep 1116361 = 837271) (by norm_num)
theorem B1116541 : Blo 1044610 1116541 := bbase (se 3 (by rfl) ⟨209351, by rfl⟩ : syracuseStep 1116541 = 418703) (by norm_num)
theorem B1149697 : Blo 1044610 1149697 := bbase (se 2 (by rfl) ⟨431136, by rfl⟩ : syracuseStep 1149697 = 862273) (by norm_num)
theorem B1116985 : Blo 1044610 1116985 := bbase (se 2 (by rfl) ⟨418869, by rfl⟩ : syracuseStep 1116985 = 837739) (by norm_num)
theorem B2984789 : Blo 1044610 2984789 := bbase (se 9 (by rfl) ⟨8744, by rfl⟩ : syracuseStep 2984789 = 17489) (by norm_num)
theorem B5376901 : Blo 1044610 5376901 := bbase (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) (by norm_num)
theorem B1117109 : Blo 1044610 1117109 := bbase (se 5 (by rfl) ⟨52364, by rfl⟩ : syracuseStep 1117109 = 104729) (by norm_num)
theorem B1117361 : Blo 1044610 1117361 := bbase (se 2 (by rfl) ⟨419010, by rfl⟩ : syracuseStep 1117361 = 838021) (by norm_num)
theorem B2231621 : Blo 1044610 2231621 := bbase (se 4 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 2231621 = 418429) (by norm_num)
theorem B3575285 : Blo 1044610 3575285 := bbase (se 5 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 3575285 = 335183) (by norm_num)
theorem B2985461 : Blo 1044610 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B2264573 : Blo 1044610 2264573 := bbase (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) (by norm_num)
theorem B1674773 : Blo 1044610 1674773 := bbase (se 6 (by rfl) ⟨39252, by rfl⟩ : syracuseStep 1674773 = 78505) (by norm_num)
theorem B1117805 : Blo 1044610 1117805 := bbase (se 3 (by rfl) ⟨209588, by rfl⟩ : syracuseStep 1117805 = 419177) (by norm_num)
theorem B11308693 : Blo 1044610 11308693 := bbase (se 6 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 11308693 = 530095) (by norm_num)
theorem B1674965 : Blo 1044610 1674965 := bbase (se 7 (by rfl) ⟨19628, by rfl⟩ : syracuseStep 1674965 = 39257) (by norm_num)
theorem B1118053 : Blo 1044610 1118053 := bbase (se 4 (by rfl) ⟨104817, by rfl⟩ : syracuseStep 1118053 = 209635) (by norm_num)
theorem B2985893 : Blo 1044610 2985893 := bbase (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) (by norm_num)
theorem B2265005 : Blo 1044610 2265005 := bbase (se 3 (by rfl) ⟨424688, by rfl⟩ : syracuseStep 2265005 = 849377) (by norm_num)
theorem B2232373 : Blo 1044610 2232373 := bbase (se 5 (by rfl) ⟨104642, by rfl⟩ : syracuseStep 2232373 = 209285) (by norm_num)
theorem B3772565 : Blo 1044610 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B2232517 : Blo 1044610 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B3969269 : Blo 1044610 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B1118497 : Blo 1044610 1118497 := bbase (se 2 (by rfl) ⟨419436, by rfl⟩ : syracuseStep 1118497 = 838873) (by norm_num)
theorem B2265421 : Blo 1044610 2265421 := bbase (se 3 (by rfl) ⟨424766, by rfl⟩ : syracuseStep 2265421 = 849533) (by norm_num)
theorem B1118557 : Blo 1044610 1118557 := bbase (se 3 (by rfl) ⟨209729, by rfl⟩ : syracuseStep 1118557 = 419459) (by norm_num)
theorem B3969557 : Blo 1044610 3969557 := bbase (se 6 (by rfl) ⟨93036, by rfl⟩ : syracuseStep 3969557 = 186073) (by norm_num)
theorem B2232893 : Blo 1044610 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B1118873 : Blo 1044610 1118873 := bbase (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) (by norm_num)
theorem B3773141 : Blo 1044610 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B2233261 : Blo 1044610 2233261 := bbase (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) (by norm_num)
theorem B2266061 : Blo 1044610 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B1676285 : Blo 1044610 1676285 := bbase (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) (by norm_num)
theorem B1119317 : Blo 1044610 1119317 := bbase (se 8 (by rfl) ⟨6558, by rfl⟩ : syracuseStep 1119317 = 13117) (by norm_num)
theorem B1676381 : Blo 1044610 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1676413 : Blo 1044610 1676413 := bbase (se 3 (by rfl) ⟨314327, by rfl⟩ : syracuseStep 1676413 = 628655) (by norm_num)
theorem B1119377 : Blo 1044610 1119377 := bbase (se 2 (by rfl) ⟨419766, by rfl⟩ : syracuseStep 1119377 = 839533) (by norm_num)
theorem B1938637 : Blo 1044610 1938637 := bbase (se 3 (by rfl) ⟨363494, by rfl⟩ : syracuseStep 1938637 = 726989) (by norm_num)
theorem B1119505 : Blo 1044610 1119505 := bbase (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) (by norm_num)
theorem B6034837 : Blo 1044610 6034837 := bbase (se 6 (by rfl) ⟨141441, by rfl⟩ : syracuseStep 6034837 = 282883) (by norm_num)
theorem B3970741 : Blo 1044610 3970741 := bbase (se 5 (by rfl) ⟨186128, by rfl⟩ : syracuseStep 3970741 = 372257) (by norm_num)
theorem B3774293 : Blo 1044610 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B7935893 : Blo 1044610 7935893 := bbase (se 6 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 7935893 = 371995) (by norm_num)
theorem B3971045 : Blo 1044610 3971045 := bbase (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) (by norm_num)
theorem B2234765 : Blo 1044610 2234765 := bbase (se 3 (by rfl) ⟨419018, by rfl⟩ : syracuseStep 2234765 = 838037) (by norm_num)
theorem B3578309 : Blo 1044610 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B2234909 : Blo 1044610 2234909 := bbase (se 3 (by rfl) ⟨419045, by rfl⟩ : syracuseStep 2234909 = 838091) (by norm_num)
theorem B1677925 : Blo 1044610 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B1940149 : Blo 1044610 1940149 := bbase (se 5 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 1940149 = 181889) (by norm_num)
theorem B11901653 : Blo 1044610 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B3021637 : Blo 1044610 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B2235269 : Blo 1044610 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B1678637 : Blo 1044610 1678637 := bbase (se 3 (by rfl) ⟨314744, by rfl⟩ : syracuseStep 1678637 = 629489) (by norm_num)
theorem B3776053 : Blo 1044610 3776053 := bbase (se 5 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 3776053 = 354005) (by norm_num)
theorem B2039357 : Blo 1044610 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B2236157 : Blo 1044610 2236157 := bbase (se 3 (by rfl) ⟨419279, by rfl⟩ : syracuseStep 2236157 = 838559) (by norm_num)
theorem B3776357 : Blo 1044610 3776357 := bbase (se 4 (by rfl) ⟨354033, by rfl⟩ : syracuseStep 3776357 = 708067) (by norm_num)
theorem B1679309 : Blo 1044610 1679309 := bbase (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) (by norm_num)
theorem B2236405 : Blo 1044610 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B3973157 : Blo 1044610 3973157 := bbase (se 4 (by rfl) ⟨372483, by rfl⟩ : syracuseStep 3973157 = 744967) (by norm_num)
theorem B3973445 : Blo 1044610 3973445 := bbase (se 4 (by rfl) ⟨372510, by rfl⟩ : syracuseStep 3973445 = 745021) (by norm_num)
theorem B2826677 : Blo 1044610 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B2236909 : Blo 1044610 2236909 := bbase (se 3 (by rfl) ⟨419420, by rfl⟩ : syracuseStep 2236909 = 838841) (by norm_num)
theorem B3580661 : Blo 1044610 3580661 := bbase (se 5 (by rfl) ⟨167843, by rfl⟩ : syracuseStep 3580661 = 335687) (by norm_num)
theorem B3351365 : Blo 1044610 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B3220469 : Blo 1044610 3220469 := bbase (se 5 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 3220469 = 301919) (by norm_num)
theorem B1909973 : Blo 1044610 1909973 := bbase (se 7 (by rfl) ⟨22382, by rfl⟩ : syracuseStep 1909973 = 44765) (by norm_num)
theorem B2237797 : Blo 1044610 2237797 := bbase (se 4 (by rfl) ⟨209793, by rfl⟩ : syracuseStep 2237797 = 419587) (by norm_num)
theorem B6694325 : Blo 1044610 6694325 := bbase (se 5 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 6694325 = 627593) (by norm_num)
theorem B5023205 : Blo 1044610 5023205 := bbase (se 4 (by rfl) ⟨470925, by rfl⟩ : syracuseStep 5023205 = 941851) (by norm_num)
theorem B3974629 : Blo 1044610 3974629 := bbase (se 4 (by rfl) ⟨372621, by rfl⟩ : syracuseStep 3974629 = 745243) (by norm_num)
theorem B4236869 : Blo 1044610 4236869 := bbase (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) (by norm_num)
theorem B1255061 : Blo 1044610 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B4236997 : Blo 1044610 4236997 := bbase (se 4 (by rfl) ⟨397218, by rfl⟩ : syracuseStep 4236997 = 794437) (by norm_num)
theorem B3352261 : Blo 1044610 3352261 := bbase (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) (by norm_num)
theorem B1255133 : Blo 1044610 1255133 := bbase (se 3 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 1255133 = 470675) (by norm_num)
theorem B3974933 : Blo 1044610 3974933 := bbase (se 6 (by rfl) ⟨93162, by rfl⟩ : syracuseStep 3974933 = 186325) (by norm_num)
theorem B2238293 : Blo 1044610 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B1255441 : Blo 1044610 1255441 := bbase (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) (by norm_num)
theorem B3352661 : Blo 1044610 3352661 := bbase (se 8 (by rfl) ⟨19644, by rfl⟩ : syracuseStep 3352661 = 39289) (by norm_num)
theorem B6367349 : Blo 1044610 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B1255609 : Blo 1044610 1255609 := bbase (se 2 (by rfl) ⟨470853, by rfl⟩ : syracuseStep 1255609 = 941707) (by norm_num)
theorem B1255657 : Blo 1044610 1255657 := bbase (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) (by norm_num)
theorem B4466933 : Blo 1044610 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B1255753 : Blo 1044610 1255753 := bbase (se 2 (by rfl) ⟨470907, by rfl⟩ : syracuseStep 1255753 = 941815) (by norm_num)
theorem B2828645 : Blo 1044610 2828645 := bbase (se 4 (by rfl) ⟨265185, by rfl⟩ : syracuseStep 2828645 = 530371) (by norm_num)
theorem B4467221 : Blo 1044610 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B1059485 : Blo 1044610 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B2239181 : Blo 1044610 2239181 := bbase (se 3 (by rfl) ⟨419846, by rfl⟩ : syracuseStep 2239181 = 839693) (by norm_num)
theorem B2239301 : Blo 1044610 2239301 := bbase (se 4 (by rfl) ⟨209934, by rfl⟩ : syracuseStep 2239301 = 419869) (by norm_num)
theorem B1256329 : Blo 1044610 1256329 := bbase (se 2 (by rfl) ⟨471123, by rfl⟩ : syracuseStep 1256329 = 942247) (by norm_num)
theorem B4533157 : Blo 1044610 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B1322173 : Blo 1044610 1322173 := bbase (se 3 (by rfl) ⟨247907, by rfl⟩ : syracuseStep 1322173 = 495815) (by norm_num)
theorem B2829509 : Blo 1044610 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B4467973 : Blo 1044610 4467973 := bbase (se 4 (by rfl) ⟨418872, by rfl⟩ : syracuseStep 4467973 = 837745) (by norm_num)
theorem B10071317 : Blo 1044610 10071317 := bbase (se 6 (by rfl) ⟨236046, by rfl⟩ : syracuseStep 10071317 = 472093) (by norm_num)
theorem B1322345 : Blo 1044610 1322345 := bbase (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) (by norm_num)
theorem B1322401 : Blo 1044610 1322401 := bbase (se 2 (by rfl) ⟨495900, by rfl⟩ : syracuseStep 1322401 = 991801) (by norm_num)
theorem B1322497 : Blo 1044610 1322497 := bbase (se 2 (by rfl) ⟨495936, by rfl⟩ : syracuseStep 1322497 = 991873) (by norm_num)
theorem B1060417 : Blo 1044610 1060417 := bbase (se 2 (by rfl) ⟨397656, by rfl⟩ : syracuseStep 1060417 = 795313) (by norm_num)
theorem B1322669 : Blo 1044610 1322669 := bbase (se 3 (by rfl) ⟨248000, by rfl⟩ : syracuseStep 1322669 = 496001) (by norm_num)
theorem B1191629 : Blo 1044610 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B1322725 : Blo 1044610 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B1060661 : Blo 1044610 1060661 := bbase (se 5 (by rfl) ⟨49718, by rfl⟩ : syracuseStep 1060661 = 99437) (by norm_num)
theorem B1322821 : Blo 1044610 1322821 := bbase (se 4 (by rfl) ⟨124014, by rfl⟩ : syracuseStep 1322821 = 248029) (by norm_num)
theorem B3977045 : Blo 1044610 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B1257329 : Blo 1044610 1257329 := bbase (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) (by norm_num)
theorem B1257377 : Blo 1044610 1257377 := bbase (se 2 (by rfl) ⟨471516, by rfl⟩ : syracuseStep 1257377 = 943033) (by norm_num)
theorem B4468709 : Blo 1044610 4468709 := bbase (se 4 (by rfl) ⟨418941, by rfl⟩ : syracuseStep 4468709 = 837883) (by norm_num)
theorem B1322993 : Blo 1044610 1322993 := bbase (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) (by norm_num)
theorem B1323049 : Blo 1044610 1323049 := bbase (se 2 (by rfl) ⟨496143, by rfl⟩ : syracuseStep 1323049 = 992287) (by norm_num)
theorem B3977333 : Blo 1044610 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B1323145 : Blo 1044610 1323145 := bbase (se 2 (by rfl) ⟨496179, by rfl⟩ : syracuseStep 1323145 = 992359) (by norm_num)
theorem B1323317 : Blo 1044610 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1323373 : Blo 1044610 1323373 := bbase (se 3 (by rfl) ⟨248132, by rfl⟩ : syracuseStep 1323373 = 496265) (by norm_num)
theorem B1257925 : Blo 1044610 1257925 := bbase (se 4 (by rfl) ⟨117930, by rfl⟩ : syracuseStep 1257925 = 235861) (by norm_num)
theorem B1323469 : Blo 1044610 1323469 := bbase (se 3 (by rfl) ⟨248150, by rfl⟩ : syracuseStep 1323469 = 496301) (by norm_num)
theorem B1192513 : Blo 1044610 1192513 := bbase (se 2 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 1192513 = 894385) (by norm_num)
theorem B1323641 : Blo 1044610 1323641 := bbase (se 2 (by rfl) ⟨496365, by rfl⟩ : syracuseStep 1323641 = 992731) (by norm_num)
theorem B1323697 : Blo 1044610 1323697 := bbase (se 2 (by rfl) ⟨496386, by rfl⟩ : syracuseStep 1323697 = 992773) (by norm_num)
theorem B1061569 : Blo 1044610 1061569 := bbase (se 2 (by rfl) ⟨398088, by rfl⟩ : syracuseStep 1061569 = 796177) (by norm_num)
theorem B1913597 : Blo 1044610 1913597 := bbase (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) (by norm_num)
theorem B1323793 : Blo 1044610 1323793 := bbase (se 2 (by rfl) ⟨496422, by rfl⟩ : syracuseStep 1323793 = 992845) (by norm_num)
theorem B8926037 : Blo 1044610 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B1258405 : Blo 1044610 1258405 := bbase (se 4 (by rfl) ⟨117975, by rfl⟩ : syracuseStep 1258405 = 235951) (by norm_num)
theorem B4240309 : Blo 1044610 4240309 := bbase (se 5 (by rfl) ⟨198764, by rfl⟩ : syracuseStep 4240309 = 397529) (by norm_num)
theorem B1323965 : Blo 1044610 1323965 := bbase (se 3 (by rfl) ⟨248243, by rfl⟩ : syracuseStep 1323965 = 496487) (by norm_num)
theorem B1487821 : Blo 1044610 1487821 := bbase (se 3 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 1487821 = 557933) (by norm_num)
theorem B1324021 : Blo 1044610 1324021 := bbase (se 5 (by rfl) ⟨62063, by rfl⟩ : syracuseStep 1324021 = 124127) (by norm_num)
theorem B1324117 : Blo 1044610 1324117 := bbase (se 8 (by rfl) ⟨7758, by rfl⟩ : syracuseStep 1324117 = 15517) (by norm_num)
theorem B1324289 : Blo 1044610 1324289 := bbase (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) (by norm_num)
theorem B3978517 : Blo 1044610 3978517 := bbase (se 6 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 3978517 = 186493) (by norm_num)
theorem B1324345 : Blo 1044610 1324345 := bbase (se 2 (by rfl) ⟨496629, by rfl⟩ : syracuseStep 1324345 = 993259) (by norm_num)
theorem B1324441 : Blo 1044610 1324441 := bbase (se 2 (by rfl) ⟨496665, by rfl⟩ : syracuseStep 1324441 = 993331) (by norm_num)
theorem B5289461 : Blo 1044610 5289461 := bbase (se 5 (by rfl) ⟨247943, by rfl⟩ : syracuseStep 5289461 = 495887) (by norm_num)
theorem B7943669 : Blo 1044610 7943669 := bbase (se 5 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 7943669 = 744719) (by norm_num)
theorem B1488413 : Blo 1044610 1488413 := bbase (se 3 (by rfl) ⟨279077, by rfl⟩ : syracuseStep 1488413 = 558155) (by norm_num)
theorem B3978821 : Blo 1044610 3978821 := bbase (se 4 (by rfl) ⟨373014, by rfl⟩ : syracuseStep 3978821 = 746029) (by norm_num)
theorem B1324613 : Blo 1044610 1324613 := bbase (se 4 (by rfl) ⟨124182, by rfl⟩ : syracuseStep 1324613 = 248365) (by norm_num)
theorem B1488493 : Blo 1044610 1488493 := bbase (se 3 (by rfl) ⟨279092, by rfl⟩ : syracuseStep 1488493 = 558185) (by norm_num)
theorem B1324669 : Blo 1044610 1324669 := bbase (se 3 (by rfl) ⟨248375, by rfl⟩ : syracuseStep 1324669 = 496751) (by norm_num)
theorem B1193681 : Blo 1044610 1193681 := bbase (se 2 (by rfl) ⟨447630, by rfl⟩ : syracuseStep 1193681 = 895261) (by norm_num)
theorem B1324765 : Blo 1044610 1324765 := bbase (se 3 (by rfl) ⟨248393, by rfl⟩ : syracuseStep 1324765 = 496787) (by norm_num)
theorem B1488613 : Blo 1044610 1488613 := bbase (se 4 (by rfl) ⟨139557, by rfl⟩ : syracuseStep 1488613 = 279115) (by norm_num)
theorem B1259285 : Blo 1044610 1259285 := bbase (se 6 (by rfl) ⟨29514, by rfl⟩ : syracuseStep 1259285 = 59029) (by norm_num)
theorem B3356453 : Blo 1044610 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B1193773 : Blo 1044610 1193773 := bbase (se 3 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 1193773 = 447665) (by norm_num)
theorem B1488709 : Blo 1044610 1488709 := bbase (se 4 (by rfl) ⟨139566, by rfl⟩ : syracuseStep 1488709 = 279133) (by norm_num)
theorem B1324937 : Blo 1044610 1324937 := bbase (se 2 (by rfl) ⟨496851, by rfl⟩ : syracuseStep 1324937 = 993703) (by norm_num)
theorem B1259401 : Blo 1044610 1259401 := bbase (se 2 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 1259401 = 944551) (by norm_num)
theorem B1324993 : Blo 1044610 1324993 := bbase (se 2 (by rfl) ⟨496872, by rfl⟩ : syracuseStep 1324993 = 993745) (by norm_num)
theorem B1325089 : Blo 1044610 1325089 := bbase (se 2 (by rfl) ⟨496908, by rfl⟩ : syracuseStep 1325089 = 993817) (by norm_num)
theorem B1259597 : Blo 1044610 1259597 := bbase (se 3 (by rfl) ⟨236174, by rfl⟩ : syracuseStep 1259597 = 472349) (by norm_num)
theorem B1325261 : Blo 1044610 1325261 := bbase (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) (by norm_num)
theorem B1325317 : Blo 1044610 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B1489205 : Blo 1044610 1489205 := bbase (se 5 (by rfl) ⟨69806, by rfl⟩ : syracuseStep 1489205 = 139613) (by norm_num)
theorem B1325413 : Blo 1044610 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B1325585 : Blo 1044610 1325585 := bbase (se 2 (by rfl) ⟨497094, by rfl⟩ : syracuseStep 1325585 = 994189) (by norm_num)
theorem B1325641 : Blo 1044610 1325641 := bbase (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) (by norm_num)
theorem B1325737 : Blo 1044610 1325737 := bbase (se 2 (by rfl) ⟨497151, by rfl⟩ : syracuseStep 1325737 = 994303) (by norm_num)
theorem B7551701 : Blo 1044610 7551701 := bbase (se 7 (by rfl) ⟨88496, by rfl⟩ : syracuseStep 7551701 = 176993) (by norm_num)
theorem B5290757 : Blo 1044610 5290757 := bbase (se 4 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 5290757 = 992017) (by norm_num)
theorem B1325909 : Blo 1044610 1325909 := bbase (se 9 (by rfl) ⟨3884, by rfl⟩ : syracuseStep 1325909 = 7769) (by norm_num)
theorem B1489757 : Blo 1044610 1489757 := bbase (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) (by norm_num)
theorem B3357541 : Blo 1044610 3357541 := bbase (se 4 (by rfl) ⟨314769, by rfl⟩ : syracuseStep 3357541 = 629539) (by norm_num)
theorem B1325965 : Blo 1044610 1325965 := bbase (se 3 (by rfl) ⟨248618, by rfl⟩ : syracuseStep 1325965 = 497237) (by norm_num)
theorem B1326061 : Blo 1044610 1326061 := bbase (se 3 (by rfl) ⟨248636, by rfl⟩ : syracuseStep 1326061 = 497273) (by norm_num)
theorem B10730485 : Blo 1044610 10730485 := bbase (se 5 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 10730485 = 1005983) (by norm_num)
theorem B1883197 : Blo 1044610 1883197 := bbase (se 3 (by rfl) ⟨353099, by rfl⟩ : syracuseStep 1883197 = 706199) (by norm_num)
theorem B1326233 : Blo 1044610 1326233 := bbase (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) (by norm_num)
theorem B4472005 : Blo 1044610 4472005 := bbase (se 4 (by rfl) ⟨419250, by rfl⟩ : syracuseStep 4472005 = 838501) (by norm_num)
theorem B1326289 : Blo 1044610 1326289 := bbase (se 2 (by rfl) ⟨497358, by rfl⟩ : syracuseStep 1326289 = 994717) (by norm_num)
theorem B7552277 : Blo 1044610 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B1326385 : Blo 1044610 1326385 := bbase (se 2 (by rfl) ⟨497394, by rfl⟩ : syracuseStep 1326385 = 994789) (by norm_num)
theorem B1326557 : Blo 1044610 1326557 := bbase (se 3 (by rfl) ⟨248729, by rfl⟩ : syracuseStep 1326557 = 497459) (by norm_num)
theorem B1326613 : Blo 1044610 1326613 := bbase (se 6 (by rfl) ⟨31092, by rfl⟩ : syracuseStep 1326613 = 62185) (by norm_num)
theorem B1490509 : Blo 1044610 1490509 := bbase (se 3 (by rfl) ⟨279470, by rfl⟩ : syracuseStep 1490509 = 558941) (by norm_num)
theorem B1326709 : Blo 1044610 1326709 := bbase (se 5 (by rfl) ⟨62189, by rfl⟩ : syracuseStep 1326709 = 124379) (by norm_num)
theorem B3980933 : Blo 1044610 3980933 := bbase (se 4 (by rfl) ⟨373212, by rfl⟩ : syracuseStep 3980933 = 746425) (by norm_num)
theorem B1883917 : Blo 1044610 1883917 := bbase (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) (by norm_num)
theorem B1326881 : Blo 1044610 1326881 := bbase (se 2 (by rfl) ⟨497580, by rfl⟩ : syracuseStep 1326881 = 995161) (by norm_num)
theorem B1589069 : Blo 1044610 1589069 := bbase (se 3 (by rfl) ⟨297950, by rfl⟩ : syracuseStep 1589069 = 595901) (by norm_num)
theorem B1326937 : Blo 1044610 1326937 := bbase (se 2 (by rfl) ⟨497601, by rfl⟩ : syracuseStep 1326937 = 995203) (by norm_num)
theorem B3981221 : Blo 1044610 3981221 := bbase (se 4 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 3981221 = 746479) (by norm_num)
theorem B1327033 : Blo 1044610 1327033 := bbase (se 2 (by rfl) ⟨497637, by rfl⟩ : syracuseStep 1327033 = 995275) (by norm_num)
theorem B1294321 : Blo 1044610 1294321 := bbase (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) (by norm_num)
theorem B3358709 : Blo 1044610 3358709 := bbase (se 5 (by rfl) ⟨157439, by rfl⟩ : syracuseStep 3358709 = 314879) (by norm_num)
theorem B5292053 : Blo 1044610 5292053 := bbase (se 6 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 5292053 = 248065) (by norm_num)
theorem B4145237 : Blo 1044610 4145237 := bbase (se 8 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 4145237 = 48577) (by norm_num)
theorem B5652661 : Blo 1044610 5652661 := bbase (se 5 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 5652661 = 529937) (by norm_num)
theorem B1130761 : Blo 1044610 1130761 := bbase (se 2 (by rfl) ⟨424035, by rfl⟩ : syracuseStep 1130761 = 848071) (by norm_num)
theorem B1491301 : Blo 1044610 1491301 := bbase (se 4 (by rfl) ⟨139809, by rfl⟩ : syracuseStep 1491301 = 279619) (by norm_num)
theorem B1884725 : Blo 1044610 1884725 := bbase (se 5 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 1884725 = 176693) (by norm_num)
theorem B1491637 : Blo 1044610 1491637 := bbase (se 5 (by rfl) ⟨69920, by rfl⟩ : syracuseStep 1491637 = 139841) (by norm_num)
theorem B1590085 : Blo 1044610 1590085 := bbase (se 4 (by rfl) ⟨149070, by rfl⟩ : syracuseStep 1590085 = 298141) (by norm_num)
theorem B1491853 : Blo 1044610 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B1983541 : Blo 1044610 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B1983685 : Blo 1044610 1983685 := bbase (se 4 (by rfl) ⟨185970, by rfl⟩ : syracuseStep 1983685 = 371941) (by norm_num)
theorem B1492229 : Blo 1044610 1492229 := bbase (se 4 (by rfl) ⟨139896, by rfl⟩ : syracuseStep 1492229 = 279793) (by norm_num)
theorem B5293349 : Blo 1044610 5293349 := bbase (se 4 (by rfl) ⟨496251, by rfl⟩ : syracuseStep 5293349 = 992503) (by norm_num)
theorem B1983845 : Blo 1044610 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B1590749 : Blo 1044610 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1983989 : Blo 1044610 1983989 := bbase (se 5 (by rfl) ⟨92999, by rfl⟩ : syracuseStep 1983989 = 185999) (by norm_num)
theorem B4769381 : Blo 1044610 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B4245173 : Blo 1044610 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B1984277 : Blo 1044610 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B1984429 : Blo 1044610 1984429 := bbase (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) (by norm_num)
theorem B20400149 : Blo 1044610 20400149 := bbase (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) (by norm_num)
theorem B4474997 : Blo 1044610 4474997 := bbase (se 5 (by rfl) ⟨209765, by rfl⟩ : syracuseStep 4474997 = 419531) (by norm_num)
theorem B1886333 : Blo 1044610 1886333 := bbase (se 3 (by rfl) ⟨353687, by rfl⟩ : syracuseStep 1886333 = 707375) (by norm_num)
theorem B1984733 : Blo 1044610 1984733 := bbase (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) (by norm_num)
theorem B5032277 : Blo 1044610 5032277 := bbase (se 10 (by rfl) ⟨7371, by rfl⟩ : syracuseStep 5032277 = 14743) (by norm_num)
theorem B1591709 : Blo 1044610 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B5032469 : Blo 1044610 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B5294645 : Blo 1044610 5294645 := bbase (se 5 (by rfl) ⟨248186, by rfl⟩ : syracuseStep 5294645 = 496373) (by norm_num)
theorem B1886989 : Blo 1044610 1886989 := bbase (se 3 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 1886989 = 707621) (by norm_num)
theorem B5032853 : Blo 1044610 5032853 := bbase (se 6 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 5032853 = 235915) (by norm_num)
theorem B1985485 : Blo 1044610 1985485 := bbase (se 3 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 1985485 = 744557) (by norm_num)
theorem B3525605 : Blo 1044610 3525605 := bbase (se 4 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 3525605 = 661051) (by norm_num)
theorem B1592341 : Blo 1044610 1592341 := bbase (se 6 (by rfl) ⟨37320, by rfl⟩ : syracuseStep 1592341 = 74641) (by norm_num)
theorem B1985629 : Blo 1044610 1985629 := bbase (se 3 (by rfl) ⟨372305, by rfl⟩ : syracuseStep 1985629 = 744611) (by norm_num)
theorem B4476005 : Blo 1044610 4476005 := bbase (se 4 (by rfl) ⟨419625, by rfl⟩ : syracuseStep 4476005 = 839251) (by norm_num)
theorem B2510045 : Blo 1044610 2510045 := bbase (se 3 (by rfl) ⟨470633, by rfl⟩ : syracuseStep 2510045 = 941267) (by norm_num)
theorem B1985789 : Blo 1044610 1985789 := bbase (se 3 (by rfl) ⟨372335, by rfl⟩ : syracuseStep 1985789 = 744671) (by norm_num)
theorem B1133897 : Blo 1044610 1133897 := bbase (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) (by norm_num)
theorem B1789285 : Blo 1044610 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B1985933 : Blo 1044610 1985933 := bbase (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) (by norm_num)
theorem B3526037 : Blo 1044610 3526037 := bbase (se 6 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 3526037 = 165283) (by norm_num)
theorem B1887781 : Blo 1044610 1887781 := bbase (se 4 (by rfl) ⟨176979, by rfl⟩ : syracuseStep 1887781 = 353959) (by norm_num)
theorem B1986221 : Blo 1044610 1986221 := bbase (se 3 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 1986221 = 744833) (by norm_num)
theorem B3526469 : Blo 1044610 3526469 := bbase (se 4 (by rfl) ⟨330606, by rfl⟩ : syracuseStep 3526469 = 661213) (by norm_num)
theorem B5295941 : Blo 1044610 5295941 := bbase (se 4 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 5295941 = 992989) (by norm_num)
theorem B1986373 : Blo 1044610 1986373 := bbase (se 4 (by rfl) ⟨186222, by rfl⟩ : syracuseStep 1986373 = 372445) (by norm_num)
theorem B1986677 : Blo 1044610 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B3526901 : Blo 1044610 3526901 := bbase (se 5 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 3526901 = 330647) (by norm_num)
theorem B1593589 : Blo 1044610 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1888589 : Blo 1044610 1888589 := bbase (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) (by norm_num)
theorem B2117981 : Blo 1044610 2117981 := bbase (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) (by norm_num)
theorem B1888733 : Blo 1044610 1888733 := bbase (se 3 (by rfl) ⟨354137, by rfl⟩ : syracuseStep 1888733 = 708275) (by norm_num)
theorem B5952149 : Blo 1044610 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B3527333 : Blo 1044610 3527333 := bbase (se 4 (by rfl) ⟨330687, by rfl⟩ : syracuseStep 3527333 = 661375) (by norm_num)
theorem B4477781 : Blo 1044610 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B1987429 : Blo 1044610 1987429 := bbase (se 4 (by rfl) ⟨186321, by rfl⟩ : syracuseStep 1987429 = 372643) (by norm_num)
theorem B2118565 : Blo 1044610 2118565 := bbase (se 4 (by rfl) ⟨198615, by rfl⟩ : syracuseStep 2118565 = 397231) (by norm_num)
theorem B1987573 : Blo 1044610 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B3527765 : Blo 1044610 3527765 := bbase (se 8 (by rfl) ⟨20670, by rfl⟩ : syracuseStep 3527765 = 41341) (by norm_num)
theorem B5297237 : Blo 1044610 5297237 := bbase (se 8 (by rfl) ⟨31038, by rfl⟩ : syracuseStep 5297237 = 62077) (by norm_num)
theorem B7951445 : Blo 1044610 7951445 := bbase (se 8 (by rfl) ⟨46590, by rfl⟩ : syracuseStep 7951445 = 93181) (by norm_num)
theorem B1987733 : Blo 1044610 1987733 := bbase (se 6 (by rfl) ⟨46587, by rfl⟩ : syracuseStep 1987733 = 93175) (by norm_num)
theorem B1889453 : Blo 1044610 1889453 := bbase (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) (by norm_num)
theorem B6706421 : Blo 1044610 6706421 := bbase (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) (by norm_num)
theorem B1987877 : Blo 1044610 1987877 := bbase (se 4 (by rfl) ⟨186363, by rfl⟩ : syracuseStep 1987877 = 372727) (by norm_num)
theorem B13620629 : Blo 1044610 13620629 := bbase (se 6 (by rfl) ⟨319233, by rfl⟩ : syracuseStep 13620629 = 638467) (by norm_num)
theorem B3528197 : Blo 1044610 3528197 := bbase (se 4 (by rfl) ⟨330768, by rfl⟩ : syracuseStep 3528197 = 661537) (by norm_num)
theorem B1988165 : Blo 1044610 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B1988317 : Blo 1044610 1988317 := bbase (se 3 (by rfl) ⟨372809, by rfl⟩ : syracuseStep 1988317 = 745619) (by norm_num)
theorem B3528629 : Blo 1044610 3528629 := bbase (se 5 (by rfl) ⟨165404, by rfl⟩ : syracuseStep 3528629 = 330809) (by norm_num)
theorem B1988621 : Blo 1044610 1988621 := bbase (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) (by norm_num)
theorem B5363765 : Blo 1044610 5363765 := bbase (se 5 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 5363765 = 502853) (by norm_num)
theorem B2119765 : Blo 1044610 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B22632533 : Blo 1044610 22632533 := bbase (se 8 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 22632533 = 265225) (by norm_num)
theorem B2119861 : Blo 1044610 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B2513197 : Blo 1044610 2513197 := bbase (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) (by norm_num)
theorem B2644285 : Blo 1044610 2644285 := bbase (se 3 (by rfl) ⟨495803, by rfl⟩ : syracuseStep 2644285 = 991607) (by norm_num)
theorem B3529061 : Blo 1044610 3529061 := bbase (se 4 (by rfl) ⟨330849, by rfl⟩ : syracuseStep 3529061 = 661699) (by norm_num)
theorem B5298533 : Blo 1044610 5298533 := bbase (se 4 (by rfl) ⟨496737, by rfl⟩ : syracuseStep 5298533 = 993475) (by norm_num)
theorem B2644397 : Blo 1044610 2644397 := bbase (se 3 (by rfl) ⟨495824, by rfl⟩ : syracuseStep 2644397 = 991649) (by norm_num)
theorem B2644589 : Blo 1044610 2644589 := bbase (se 3 (by rfl) ⟨495860, by rfl⟩ : syracuseStep 2644589 = 991721) (by norm_num)
theorem B1989373 : Blo 1044610 1989373 := bbase (se 3 (by rfl) ⟨373007, by rfl⟩ : syracuseStep 1989373 = 746015) (by norm_num)
theorem B3529493 : Blo 1044610 3529493 := bbase (se 6 (by rfl) ⟨82722, by rfl⟩ : syracuseStep 3529493 = 165445) (by norm_num)
theorem B2448181 : Blo 1044610 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B32168789 : Blo 1044610 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B6806389 : Blo 1044610 6806389 := bbase (se 5 (by rfl) ⟨319049, by rfl⟩ : syracuseStep 6806389 = 638099) (by norm_num)
theorem B1989517 : Blo 1044610 1989517 := bbase (se 3 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 1989517 = 746069) (by norm_num)
theorem B1792957 : Blo 1044610 1792957 := bbase (se 3 (by rfl) ⟨336179, by rfl⟩ : syracuseStep 1792957 = 672359) (by norm_num)
theorem B2644933 : Blo 1044610 2644933 := bbase (se 4 (by rfl) ⟨247962, by rfl⟩ : syracuseStep 2644933 = 495925) (by norm_num)
theorem B2153453 : Blo 1044610 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B1989677 : Blo 1044610 1989677 := bbase (se 3 (by rfl) ⟨373064, by rfl⟩ : syracuseStep 1989677 = 746129) (by norm_num)
theorem B2645045 : Blo 1044610 2645045 := bbase (se 5 (by rfl) ⟨123986, by rfl⟩ : syracuseStep 2645045 = 247973) (by norm_num)
theorem B5037157 : Blo 1044610 5037157 := bbase (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) (by norm_num)
theorem B5364917 : Blo 1044610 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B1989821 : Blo 1044610 1989821 := bbase (se 3 (by rfl) ⟨373091, by rfl⟩ : syracuseStep 1989821 = 746183) (by norm_num)
theorem B3529925 : Blo 1044610 3529925 := bbase (se 4 (by rfl) ⟨330930, by rfl⟩ : syracuseStep 3529925 = 661861) (by norm_num)
theorem B2645237 : Blo 1044610 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B3398933 : Blo 1044610 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B2350421 : Blo 1044610 2350421 := bbase (se 11 (by rfl) ⟨1721, by rfl⟩ : syracuseStep 2350421 = 3443) (by norm_num)
theorem B2350493 : Blo 1044610 2350493 := bbase (se 3 (by rfl) ⟨440717, by rfl⟩ : syracuseStep 2350493 = 881435) (by norm_num)
theorem B1990109 : Blo 1044610 1990109 := bbase (se 3 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 1990109 = 746291) (by norm_num)
theorem B2350565 : Blo 1044610 2350565 := bbase (se 4 (by rfl) ⟨220365, by rfl⟩ : syracuseStep 2350565 = 440731) (by norm_num)
theorem B2350637 : Blo 1044610 2350637 := bbase (se 3 (by rfl) ⟨440744, by rfl⟩ : syracuseStep 2350637 = 881489) (by norm_num)
theorem B2645581 : Blo 1044610 2645581 := bbase (se 3 (by rfl) ⟨496046, by rfl⟩ : syracuseStep 2645581 = 992093) (by norm_num)
theorem B2350709 : Blo 1044610 2350709 := bbase (se 5 (by rfl) ⟨110189, by rfl⟩ : syracuseStep 2350709 = 220379) (by norm_num)
theorem B3530357 : Blo 1044610 3530357 := bbase (se 5 (by rfl) ⟨165485, by rfl⟩ : syracuseStep 3530357 = 330971) (by norm_num)
theorem B5299829 : Blo 1044610 5299829 := bbase (se 5 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 5299829 = 496859) (by norm_num)
theorem B1990261 : Blo 1044610 1990261 := bbase (se 5 (by rfl) ⟨93293, by rfl⟩ : syracuseStep 1990261 = 186587) (by norm_num)
theorem B1793669 : Blo 1044610 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B2514581 : Blo 1044610 2514581 := bbase (se 6 (by rfl) ⟨58935, by rfl⟩ : syracuseStep 2514581 = 117871) (by norm_num)
theorem B2350781 : Blo 1044610 2350781 := bbase (se 3 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 2350781 = 881543) (by norm_num)
theorem B2645693 : Blo 1044610 2645693 := bbase (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) (by norm_num)
theorem B2350853 : Blo 1044610 2350853 := bbase (se 4 (by rfl) ⟨220392, by rfl⟩ : syracuseStep 2350853 = 440785) (by norm_num)
theorem B2350925 : Blo 1044610 2350925 := bbase (se 3 (by rfl) ⟨440798, by rfl⟩ : syracuseStep 2350925 = 881597) (by norm_num)
theorem B2514773 : Blo 1044610 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B2645885 : Blo 1044610 2645885 := bbase (se 3 (by rfl) ⟨496103, by rfl⟩ : syracuseStep 2645885 = 992207) (by norm_num)
theorem B2350997 : Blo 1044610 2350997 := bbase (se 6 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 2350997 = 110203) (by norm_num)
theorem B1990565 : Blo 1044610 1990565 := bbase (se 4 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 1990565 = 373231) (by norm_num)
theorem B2351069 : Blo 1044610 2351069 := bbase (se 3 (by rfl) ⟨440825, by rfl⟩ : syracuseStep 2351069 = 881651) (by norm_num)
theorem B2351141 : Blo 1044610 2351141 := bbase (se 4 (by rfl) ⟨220419, by rfl⟩ : syracuseStep 2351141 = 440839) (by norm_num)
theorem B3530789 : Blo 1044610 3530789 := bbase (se 4 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 3530789 = 662023) (by norm_num)
theorem B2351213 : Blo 1044610 2351213 := bbase (se 3 (by rfl) ⟨440852, by rfl⟩ : syracuseStep 2351213 = 881705) (by norm_num)
theorem B2351285 : Blo 1044610 2351285 := bbase (se 5 (by rfl) ⟨110216, by rfl⟩ : syracuseStep 2351285 = 220433) (by norm_num)
theorem B2646229 : Blo 1044610 2646229 := bbase (se 7 (by rfl) ⟨31010, by rfl⟩ : syracuseStep 2646229 = 62021) (by norm_num)
theorem B3236069 : Blo 1044610 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B2351357 : Blo 1044610 2351357 := bbase (se 3 (by rfl) ⟨440879, by rfl⟩ : syracuseStep 2351357 = 881759) (by norm_num)
theorem B2351429 : Blo 1044610 2351429 := bbase (se 4 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 2351429 = 440893) (by norm_num)
theorem B2646341 : Blo 1044610 2646341 := bbase (se 4 (by rfl) ⟨248094, by rfl⟩ : syracuseStep 2646341 = 496189) (by norm_num)
theorem B2351501 : Blo 1044610 2351501 := bbase (se 3 (by rfl) ⟨440906, by rfl⟩ : syracuseStep 2351501 = 881813) (by norm_num)
theorem B2351573 : Blo 1044610 2351573 := bbase (se 7 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 2351573 = 55115) (by norm_num)
theorem B3531221 : Blo 1044610 3531221 := bbase (se 7 (by rfl) ⟨41381, by rfl⟩ : syracuseStep 3531221 = 82763) (by norm_num)
theorem B2646533 : Blo 1044610 2646533 := bbase (se 4 (by rfl) ⟨248112, by rfl⟩ : syracuseStep 2646533 = 496225) (by norm_num)
theorem B2351645 : Blo 1044610 2351645 := bbase (se 3 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 2351645 = 881867) (by norm_num)
theorem B2351717 : Blo 1044610 2351717 := bbase (se 4 (by rfl) ⟨220473, by rfl⟩ : syracuseStep 2351717 = 440947) (by norm_num)
theorem B8938133 : Blo 1044610 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B2351789 : Blo 1044610 2351789 := bbase (se 3 (by rfl) ⟨440960, by rfl⟩ : syracuseStep 2351789 = 881921) (by norm_num)
theorem B13394645 : Blo 1044610 13394645 := bbase (se 7 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 13394645 = 313937) (by norm_num)
theorem B2351861 : Blo 1044610 2351861 := bbase (se 5 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 2351861 = 220487) (by norm_num)
theorem B6808373 : Blo 1044610 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B2351933 : Blo 1044610 2351933 := bbase (se 3 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 2351933 = 881975) (by norm_num)
theorem B2646877 : Blo 1044610 2646877 := bbase (se 3 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 2646877 = 992579) (by norm_num)
theorem B2352005 : Blo 1044610 2352005 := bbase (se 4 (by rfl) ⟨220500, by rfl⟩ : syracuseStep 2352005 = 441001) (by norm_num)
theorem B3531653 : Blo 1044610 3531653 := bbase (se 4 (by rfl) ⟨331092, by rfl⟩ : syracuseStep 3531653 = 662185) (by norm_num)
theorem B5301125 : Blo 1044610 5301125 := bbase (se 4 (by rfl) ⟨496980, by rfl⟩ : syracuseStep 5301125 = 993961) (by norm_num)
theorem B2352077 : Blo 1044610 2352077 := bbase (se 3 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 2352077 = 882029) (by norm_num)
theorem B2646989 : Blo 1044610 2646989 := bbase (se 3 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 2646989 = 992621) (by norm_num)
theorem B2352149 : Blo 1044610 2352149 := bbase (se 6 (by rfl) ⟨55128, by rfl⟩ : syracuseStep 2352149 = 110257) (by norm_num)
theorem B2352221 : Blo 1044610 2352221 := bbase (se 3 (by rfl) ⟨441041, by rfl⟩ : syracuseStep 2352221 = 882083) (by norm_num)
theorem B2647181 : Blo 1044610 2647181 := bbase (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) (by norm_num)
theorem B2352293 : Blo 1044610 2352293 := bbase (se 4 (by rfl) ⟨220527, by rfl⟩ : syracuseStep 2352293 = 441055) (by norm_num)
theorem B2352365 : Blo 1044610 2352365 := bbase (se 3 (by rfl) ⟨441068, by rfl⟩ : syracuseStep 2352365 = 882137) (by norm_num)
theorem B2974981 : Blo 1044610 2974981 := bbase (se 4 (by rfl) ⟨278904, by rfl⟩ : syracuseStep 2974981 = 557809) (by norm_num)
theorem B11330837 : Blo 1044610 11330837 := bbase (se 6 (by rfl) ⟨265566, by rfl⟩ : syracuseStep 11330837 = 531133) (by norm_num)
theorem B2352437 : Blo 1044610 2352437 := bbase (se 5 (by rfl) ⟨110270, by rfl⟩ : syracuseStep 2352437 = 220541) (by norm_num)
theorem B3532085 : Blo 1044610 3532085 := bbase (se 5 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 3532085 = 331133) (by norm_num)
theorem B2385229 : Blo 1044610 2385229 := bbase (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) (by norm_num)
theorem B2516341 : Blo 1044610 2516341 := bbase (se 5 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 2516341 = 235907) (by norm_num)
theorem B2352509 : Blo 1044610 2352509 := bbase (se 3 (by rfl) ⟨441095, by rfl⟩ : syracuseStep 2352509 = 882191) (by norm_num)
theorem B2385301 : Blo 1044610 2385301 := bbase (se 6 (by rfl) ⟨55905, by rfl⟩ : syracuseStep 2385301 = 111811) (by norm_num)
theorem B5662133 : Blo 1044610 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B2352581 : Blo 1044610 2352581 := bbase (se 4 (by rfl) ⟨220554, by rfl⟩ : syracuseStep 2352581 = 441109) (by norm_num)
theorem B1762789 : Blo 1044610 1762789 := bbase (se 4 (by rfl) ⟨165261, by rfl⟩ : syracuseStep 1762789 = 330523) (by norm_num)
theorem B2647525 : Blo 1044610 2647525 := bbase (se 4 (by rfl) ⟨248205, by rfl⟩ : syracuseStep 2647525 = 496411) (by norm_num)
theorem B2352653 : Blo 1044610 2352653 := bbase (se 3 (by rfl) ⟨441122, by rfl⟩ : syracuseStep 2352653 = 882245) (by norm_num)
theorem B6809141 : Blo 1044610 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B1762877 : Blo 1044610 1762877 := bbase (se 3 (by rfl) ⟨330539, by rfl⟩ : syracuseStep 1762877 = 661079) (by norm_num)
theorem B2352725 : Blo 1044610 2352725 := bbase (se 8 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 2352725 = 27571) (by norm_num)
theorem B2647637 : Blo 1044610 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B2123381 : Blo 1044610 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B2352797 : Blo 1044610 2352797 := bbase (se 3 (by rfl) ⟨441149, by rfl⟩ : syracuseStep 2352797 = 882299) (by norm_num)
theorem B2123429 : Blo 1044610 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B1763005 : Blo 1044610 1763005 := bbase (se 3 (by rfl) ⟨330563, by rfl⟩ : syracuseStep 1763005 = 661127) (by norm_num)
theorem B20113109 : Blo 1044610 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B2352869 : Blo 1044610 2352869 := bbase (se 4 (by rfl) ⟨220581, by rfl⟩ : syracuseStep 2352869 = 441163) (by norm_num)
theorem B3532517 : Blo 1044610 3532517 := bbase (se 4 (by rfl) ⟨331173, by rfl⟩ : syracuseStep 3532517 = 662347) (by norm_num)
theorem B1763093 : Blo 1044610 1763093 := bbase (se 6 (by rfl) ⟨41322, by rfl⟩ : syracuseStep 1763093 = 82645) (by norm_num)
theorem B2647829 : Blo 1044610 2647829 := bbase (se 6 (by rfl) ⟨62058, by rfl⟩ : syracuseStep 2647829 = 124117) (by norm_num)
theorem B2352941 : Blo 1044610 2352941 := bbase (se 3 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 2352941 = 882353) (by norm_num)
theorem B1632101 : Blo 1044610 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B2353013 : Blo 1044610 2353013 := bbase (se 5 (by rfl) ⟨110297, by rfl⟩ : syracuseStep 2353013 = 220595) (by norm_num)
theorem B1763221 : Blo 1044610 1763221 := bbase (se 6 (by rfl) ⟨41325, by rfl⟩ : syracuseStep 1763221 = 82651) (by norm_num)
theorem B20703125 : Blo 1044610 20703125 := bbase (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) (by norm_num)
theorem B10053557 : Blo 1044610 10053557 := bbase (se 5 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 10053557 = 942521) (by norm_num)
theorem B2353085 : Blo 1044610 2353085 := bbase (se 3 (by rfl) ⟨441203, by rfl⟩ : syracuseStep 2353085 = 882407) (by norm_num)
theorem B2516957 : Blo 1044610 2516957 := bbase (se 3 (by rfl) ⟨471929, by rfl⟩ : syracuseStep 2516957 = 943859) (by norm_num)
theorem B1763309 : Blo 1044610 1763309 := bbase (se 3 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 1763309 = 661241) (by norm_num)
theorem B2353157 : Blo 1044610 2353157 := bbase (se 4 (by rfl) ⟨220608, by rfl⟩ : syracuseStep 2353157 = 441217) (by norm_num)
theorem B2353229 : Blo 1044610 2353229 := bbase (se 3 (by rfl) ⟨441230, by rfl⟩ : syracuseStep 2353229 = 882461) (by norm_num)
theorem B1763437 : Blo 1044610 1763437 := bbase (se 3 (by rfl) ⟨330644, by rfl⟩ : syracuseStep 1763437 = 661289) (by norm_num)
theorem B2648173 : Blo 1044610 2648173 := bbase (se 3 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 2648173 = 993065) (by norm_num)
theorem B2353301 : Blo 1044610 2353301 := bbase (se 6 (by rfl) ⟨55155, by rfl⟩ : syracuseStep 2353301 = 110311) (by norm_num)
theorem B3532949 : Blo 1044610 3532949 := bbase (se 6 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 3532949 = 165607) (by norm_num)
theorem B5302421 : Blo 1044610 5302421 := bbase (se 6 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 5302421 = 248551) (by norm_num)
theorem B2418853 : Blo 1044610 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B1566917 : Blo 1044610 1566917 := bbase (se 4 (by rfl) ⟨146898, by rfl⟩ : syracuseStep 1566917 = 293797) (by norm_num)
theorem B1763525 : Blo 1044610 1763525 := bbase (se 4 (by rfl) ⟨165330, by rfl⟩ : syracuseStep 1763525 = 330661) (by norm_num)
theorem B1566941 : Blo 1044610 1566941 := bbase (se 3 (by rfl) ⟨293801, by rfl⟩ : syracuseStep 1566941 = 587603) (by norm_num)
theorem B2353373 : Blo 1044610 2353373 := bbase (se 3 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 2353373 = 882515) (by norm_num)
theorem B2648285 : Blo 1044610 2648285 := bbase (se 3 (by rfl) ⟨496553, by rfl⟩ : syracuseStep 2648285 = 993107) (by norm_num)
theorem B2124013 : Blo 1044610 2124013 := bbase (se 3 (by rfl) ⟨398252, by rfl⟩ : syracuseStep 2124013 = 796505) (by norm_num)
theorem B1566965 : Blo 1044610 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B1566989 : Blo 1044610 1566989 := bbase (se 3 (by rfl) ⟨293810, by rfl⟩ : syracuseStep 1566989 = 587621) (by norm_num)
theorem B1567013 : Blo 1044610 1567013 := bbase (se 4 (by rfl) ⟨146907, by rfl⟩ : syracuseStep 1567013 = 293815) (by norm_num)
theorem B2353445 : Blo 1044610 2353445 := bbase (se 4 (by rfl) ⟨220635, by rfl⟩ : syracuseStep 2353445 = 441271) (by norm_num)
theorem B1567037 : Blo 1044610 1567037 := bbase (se 3 (by rfl) ⟨293819, by rfl⟩ : syracuseStep 1567037 = 587639) (by norm_num)
theorem B1763653 : Blo 1044610 1763653 := bbase (se 4 (by rfl) ⟨165342, by rfl⟩ : syracuseStep 1763653 = 330685) (by norm_num)
theorem B1567061 : Blo 1044610 1567061 := bbase (se 10 (by rfl) ⟨2295, by rfl⟩ : syracuseStep 1567061 = 4591) (by norm_num)
theorem B1567085 : Blo 1044610 1567085 := bbase (se 3 (by rfl) ⟨293828, by rfl⟩ : syracuseStep 1567085 = 587657) (by norm_num)
theorem B2353517 : Blo 1044610 2353517 := bbase (se 3 (by rfl) ⟨441284, by rfl⟩ : syracuseStep 2353517 = 882569) (by norm_num)
theorem B1567109 : Blo 1044610 1567109 := bbase (se 4 (by rfl) ⟨146916, by rfl⟩ : syracuseStep 1567109 = 293833) (by norm_num)
theorem B1567133 : Blo 1044610 1567133 := bbase (se 3 (by rfl) ⟨293837, by rfl⟩ : syracuseStep 1567133 = 587675) (by norm_num)
theorem B1763741 : Blo 1044610 1763741 := bbase (se 3 (by rfl) ⟨330701, by rfl⟩ : syracuseStep 1763741 = 661403) (by norm_num)
theorem B2648477 : Blo 1044610 2648477 := bbase (se 3 (by rfl) ⟨496589, by rfl⟩ : syracuseStep 2648477 = 993179) (by norm_num)
theorem B1567157 : Blo 1044610 1567157 := bbase (se 5 (by rfl) ⟨73460, by rfl⟩ : syracuseStep 1567157 = 146921) (by norm_num)
theorem B2353589 : Blo 1044610 2353589 := bbase (se 5 (by rfl) ⟨110324, by rfl⟩ : syracuseStep 2353589 = 220649) (by norm_num)
theorem B1567181 : Blo 1044610 1567181 := bbase (se 3 (by rfl) ⟨293846, by rfl⟩ : syracuseStep 1567181 = 587693) (by norm_num)
theorem B1567205 : Blo 1044610 1567205 := bbase (se 4 (by rfl) ⟨146925, by rfl⟩ : syracuseStep 1567205 = 293851) (by norm_num)
theorem B1567229 : Blo 1044610 1567229 := bbase (se 3 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 1567229 = 587711) (by norm_num)
theorem B2353661 : Blo 1044610 2353661 := bbase (se 3 (by rfl) ⟨441311, by rfl⟩ : syracuseStep 2353661 = 882623) (by norm_num)
theorem B1567253 : Blo 1044610 1567253 := bbase (se 6 (by rfl) ⟨36732, by rfl⟩ : syracuseStep 1567253 = 73465) (by norm_num)
theorem B1763869 : Blo 1044610 1763869 := bbase (se 3 (by rfl) ⟨330725, by rfl⟩ : syracuseStep 1763869 = 661451) (by norm_num)
theorem B1567277 : Blo 1044610 1567277 := bbase (se 3 (by rfl) ⟨293864, by rfl⟩ : syracuseStep 1567277 = 587729) (by norm_num)
theorem B1567301 : Blo 1044610 1567301 := bbase (se 4 (by rfl) ⟨146934, by rfl⟩ : syracuseStep 1567301 = 293869) (by norm_num)
theorem B2353733 : Blo 1044610 2353733 := bbase (se 4 (by rfl) ⟨220662, by rfl⟩ : syracuseStep 2353733 = 441325) (by norm_num)
theorem B3533381 : Blo 1044610 3533381 := bbase (se 4 (by rfl) ⟨331254, by rfl⟩ : syracuseStep 3533381 = 662509) (by norm_num)
theorem B1567325 : Blo 1044610 1567325 := bbase (se 3 (by rfl) ⟨293873, by rfl⟩ : syracuseStep 1567325 = 587747) (by norm_num)
theorem B1567349 : Blo 1044610 1567349 := bbase (se 5 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 1567349 = 146939) (by norm_num)
theorem B1763957 : Blo 1044610 1763957 := bbase (se 5 (by rfl) ⟨82685, by rfl⟩ : syracuseStep 1763957 = 165371) (by norm_num)
theorem B1567373 : Blo 1044610 1567373 := bbase (se 3 (by rfl) ⟨293882, by rfl⟩ : syracuseStep 1567373 = 587765) (by norm_num)
theorem B2353805 : Blo 1044610 2353805 := bbase (se 3 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 2353805 = 882677) (by norm_num)
theorem B1567397 : Blo 1044610 1567397 := bbase (se 4 (by rfl) ⟨146943, by rfl⟩ : syracuseStep 1567397 = 293887) (by norm_num)
theorem B1567421 : Blo 1044610 1567421 := bbase (se 3 (by rfl) ⟨293891, by rfl⟩ : syracuseStep 1567421 = 587783) (by norm_num)
theorem B1567445 : Blo 1044610 1567445 := bbase (se 7 (by rfl) ⟨18368, by rfl⟩ : syracuseStep 1567445 = 36737) (by norm_num)
theorem B2353877 : Blo 1044610 2353877 := bbase (se 7 (by rfl) ⟨27584, by rfl⟩ : syracuseStep 2353877 = 55169) (by norm_num)
theorem B2517733 : Blo 1044610 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B1567469 : Blo 1044610 1567469 := bbase (se 3 (by rfl) ⟨293900, by rfl⟩ : syracuseStep 1567469 = 587801) (by norm_num)
theorem B1764085 : Blo 1044610 1764085 := bbase (se 5 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 1764085 = 165383) (by norm_num)
theorem B2648821 : Blo 1044610 2648821 := bbase (se 5 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 2648821 = 248327) (by norm_num)
theorem B1567493 : Blo 1044610 1567493 := bbase (se 4 (by rfl) ⟨146952, by rfl⟩ : syracuseStep 1567493 = 293905) (by norm_num)
theorem B6712085 : Blo 1044610 6712085 := bbase (se 6 (by rfl) ⟨157314, by rfl⟩ : syracuseStep 6712085 = 314629) (by norm_num)
theorem B1567517 : Blo 1044610 1567517 := bbase (se 3 (by rfl) ⟨293909, by rfl⟩ : syracuseStep 1567517 = 587819) (by norm_num)
theorem B2353949 : Blo 1044610 2353949 := bbase (se 3 (by rfl) ⟨441365, by rfl⟩ : syracuseStep 2353949 = 882731) (by norm_num)
theorem B1567541 : Blo 1044610 1567541 := bbase (se 5 (by rfl) ⟨73478, by rfl⟩ : syracuseStep 1567541 = 146957) (by norm_num)
theorem B1567565 : Blo 1044610 1567565 := bbase (se 3 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 1567565 = 587837) (by norm_num)
theorem B1764173 : Blo 1044610 1764173 := bbase (se 3 (by rfl) ⟨330782, by rfl⟩ : syracuseStep 1764173 = 661565) (by norm_num)
theorem B1272673 : Blo 1044610 1272673 := bbase (se 2 (by rfl) ⟨477252, by rfl⟩ : syracuseStep 1272673 = 954505) (by norm_num)
theorem B1567589 : Blo 1044610 1567589 := bbase (se 4 (by rfl) ⟨146961, by rfl⟩ : syracuseStep 1567589 = 293923) (by norm_num)
theorem B2354021 : Blo 1044610 2354021 := bbase (se 4 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 2354021 = 441379) (by norm_num)
theorem B2648933 : Blo 1044610 2648933 := bbase (se 4 (by rfl) ⟨248337, by rfl⟩ : syracuseStep 2648933 = 496675) (by norm_num)
theorem B5368693 : Blo 1044610 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B1567613 : Blo 1044610 1567613 := bbase (se 3 (by rfl) ⟨293927, by rfl⟩ : syracuseStep 1567613 = 587855) (by norm_num)
theorem B1567637 : Blo 1044610 1567637 := bbase (se 6 (by rfl) ⟨36741, by rfl⟩ : syracuseStep 1567637 = 73483) (by norm_num)
theorem B1567661 : Blo 1044610 1567661 := bbase (se 3 (by rfl) ⟨293936, by rfl⟩ : syracuseStep 1567661 = 587873) (by norm_num)
theorem B2354093 : Blo 1044610 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B1567685 : Blo 1044610 1567685 := bbase (se 4 (by rfl) ⟨146970, by rfl⟩ : syracuseStep 1567685 = 293941) (by norm_num)
theorem B1764301 : Blo 1044610 1764301 := bbase (se 3 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 1764301 = 661613) (by norm_num)
theorem B1567709 : Blo 1044610 1567709 := bbase (se 3 (by rfl) ⟨293945, by rfl⟩ : syracuseStep 1567709 = 587891) (by norm_num)
theorem B1567733 : Blo 1044610 1567733 := bbase (se 5 (by rfl) ⟨73487, by rfl⟩ : syracuseStep 1567733 = 146975) (by norm_num)
theorem B2354165 : Blo 1044610 2354165 := bbase (se 5 (by rfl) ⟨110351, by rfl⟩ : syracuseStep 2354165 = 220703) (by norm_num)
theorem B3533813 : Blo 1044610 3533813 := bbase (se 5 (by rfl) ⟨165647, by rfl⟩ : syracuseStep 3533813 = 331295) (by norm_num)
theorem B1567757 : Blo 1044610 1567757 := bbase (se 3 (by rfl) ⟨293954, by rfl⟩ : syracuseStep 1567757 = 587909) (by norm_num)
theorem B1567781 : Blo 1044610 1567781 := bbase (se 4 (by rfl) ⟨146979, by rfl⟩ : syracuseStep 1567781 = 293959) (by norm_num)
theorem B1764389 : Blo 1044610 1764389 := bbase (se 4 (by rfl) ⟨165411, by rfl⟩ : syracuseStep 1764389 = 330823) (by norm_num)
theorem B2649125 : Blo 1044610 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B1567805 : Blo 1044610 1567805 := bbase (se 3 (by rfl) ⟨293963, by rfl⟩ : syracuseStep 1567805 = 587927) (by norm_num)
theorem B2354237 : Blo 1044610 2354237 := bbase (se 3 (by rfl) ⟨441419, by rfl⟩ : syracuseStep 2354237 = 882839) (by norm_num)
theorem B1567829 : Blo 1044610 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B1567853 : Blo 1044610 1567853 := bbase (se 3 (by rfl) ⟨293972, by rfl⟩ : syracuseStep 1567853 = 587945) (by norm_num)
theorem B5663861 : Blo 1044610 5663861 := bbase (se 5 (by rfl) ⟨265493, by rfl⟩ : syracuseStep 5663861 = 530987) (by norm_num)
theorem B1567877 : Blo 1044610 1567877 := bbase (se 4 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 1567877 = 293977) (by norm_num)
theorem B2354309 : Blo 1044610 2354309 := bbase (se 4 (by rfl) ⟨220716, by rfl⟩ : syracuseStep 2354309 = 441433) (by norm_num)
theorem B1567901 : Blo 1044610 1567901 := bbase (se 3 (by rfl) ⟨293981, by rfl⟩ : syracuseStep 1567901 = 587963) (by norm_num)
theorem B1764517 : Blo 1044610 1764517 := bbase (se 4 (by rfl) ⟨165423, by rfl⟩ : syracuseStep 1764517 = 330847) (by norm_num)
theorem B1567925 : Blo 1044610 1567925 := bbase (se 5 (by rfl) ⟨73496, by rfl⟩ : syracuseStep 1567925 = 146993) (by norm_num)
theorem B1567949 : Blo 1044610 1567949 := bbase (se 3 (by rfl) ⟨293990, by rfl⟩ : syracuseStep 1567949 = 587981) (by norm_num)
theorem B2354381 : Blo 1044610 2354381 := bbase (se 3 (by rfl) ⟨441446, by rfl⟩ : syracuseStep 2354381 = 882893) (by norm_num)
theorem B1567973 : Blo 1044610 1567973 := bbase (se 4 (by rfl) ⟨146997, by rfl⟩ : syracuseStep 1567973 = 293995) (by norm_num)
theorem B1567997 : Blo 1044610 1567997 := bbase (se 3 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 1567997 = 587999) (by norm_num)
theorem B1764605 : Blo 1044610 1764605 := bbase (se 3 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 1764605 = 661727) (by norm_num)
theorem B1568021 : Blo 1044610 1568021 := bbase (se 6 (by rfl) ⟨36750, by rfl⟩ : syracuseStep 1568021 = 73501) (by norm_num)
theorem B2354453 : Blo 1044610 2354453 := bbase (se 6 (by rfl) ⟨55182, by rfl⟩ : syracuseStep 2354453 = 110365) (by norm_num)
theorem B1568045 : Blo 1044610 1568045 := bbase (se 3 (by rfl) ⟨294008, by rfl⟩ : syracuseStep 1568045 = 588017) (by norm_num)
theorem B1568069 : Blo 1044610 1568069 := bbase (se 4 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 1568069 = 294013) (by norm_num)
theorem B1568093 : Blo 1044610 1568093 := bbase (se 3 (by rfl) ⟨294017, by rfl⟩ : syracuseStep 1568093 = 588035) (by norm_num)
theorem B2354525 : Blo 1044610 2354525 := bbase (se 3 (by rfl) ⟨441473, by rfl⟩ : syracuseStep 2354525 = 882947) (by norm_num)
theorem B1568117 : Blo 1044610 1568117 := bbase (se 5 (by rfl) ⟨73505, by rfl⟩ : syracuseStep 1568117 = 147011) (by norm_num)
theorem B1764733 : Blo 1044610 1764733 := bbase (se 3 (by rfl) ⟨330887, by rfl⟩ : syracuseStep 1764733 = 661775) (by norm_num)
theorem B2649469 : Blo 1044610 2649469 := bbase (se 3 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 2649469 = 993551) (by norm_num)
theorem B1568141 : Blo 1044610 1568141 := bbase (se 3 (by rfl) ⟨294026, by rfl⟩ : syracuseStep 1568141 = 588053) (by norm_num)
theorem B1568165 : Blo 1044610 1568165 := bbase (se 4 (by rfl) ⟨147015, by rfl⟩ : syracuseStep 1568165 = 294031) (by norm_num)
theorem B2354597 : Blo 1044610 2354597 := bbase (se 4 (by rfl) ⟨220743, by rfl⟩ : syracuseStep 2354597 = 441487) (by norm_num)
theorem B3534245 : Blo 1044610 3534245 := bbase (se 4 (by rfl) ⟨331335, by rfl⟩ : syracuseStep 3534245 = 662671) (by norm_num)
theorem B5303717 : Blo 1044610 5303717 := bbase (se 4 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 5303717 = 994447) (by norm_num)
theorem B2518445 : Blo 1044610 2518445 := bbase (se 3 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 2518445 = 944417) (by norm_num)
theorem B1568189 : Blo 1044610 1568189 := bbase (se 3 (by rfl) ⟨294035, by rfl⟩ : syracuseStep 1568189 = 588071) (by norm_num)
theorem B1568213 : Blo 1044610 1568213 := bbase (se 7 (by rfl) ⟨18377, by rfl⟩ : syracuseStep 1568213 = 36755) (by norm_num)
theorem B1764821 : Blo 1044610 1764821 := bbase (se 7 (by rfl) ⟨20681, by rfl⟩ : syracuseStep 1764821 = 41363) (by norm_num)
theorem B1568237 : Blo 1044610 1568237 := bbase (se 3 (by rfl) ⟨294044, by rfl⟩ : syracuseStep 1568237 = 588089) (by norm_num)
theorem B2354669 : Blo 1044610 2354669 := bbase (se 3 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 2354669 = 883001) (by norm_num)
theorem B2649581 : Blo 1044610 2649581 := bbase (se 3 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 2649581 = 993593) (by norm_num)
theorem B1568261 : Blo 1044610 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B1568285 : Blo 1044610 1568285 := bbase (se 3 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 1568285 = 588107) (by norm_num)
theorem B1568309 : Blo 1044610 1568309 := bbase (se 5 (by rfl) ⟨73514, by rfl⟩ : syracuseStep 1568309 = 147029) (by norm_num)
theorem B2944565 : Blo 1044610 2944565 := bbase (se 5 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 2944565 = 276053) (by norm_num)
theorem B2354741 : Blo 1044610 2354741 := bbase (se 5 (by rfl) ⟨110378, by rfl⟩ : syracuseStep 2354741 = 220757) (by norm_num)
theorem B1568333 : Blo 1044610 1568333 := bbase (se 3 (by rfl) ⟨294062, by rfl⟩ : syracuseStep 1568333 = 588125) (by norm_num)
theorem B1764949 : Blo 1044610 1764949 := bbase (se 8 (by rfl) ⟨10341, by rfl⟩ : syracuseStep 1764949 = 20683) (by norm_num)
theorem B1568357 : Blo 1044610 1568357 := bbase (se 4 (by rfl) ⟨147033, by rfl⟩ : syracuseStep 1568357 = 294067) (by norm_num)
theorem B1568381 : Blo 1044610 1568381 := bbase (se 3 (by rfl) ⟨294071, by rfl⟩ : syracuseStep 1568381 = 588143) (by norm_num)
theorem B2354813 : Blo 1044610 2354813 := bbase (se 3 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 2354813 = 883055) (by norm_num)
theorem B1568405 : Blo 1044610 1568405 := bbase (se 6 (by rfl) ⟨36759, by rfl⟩ : syracuseStep 1568405 = 73519) (by norm_num)
theorem B1175197 : Blo 1044610 1175197 := bbase (se 3 (by rfl) ⟨220349, by rfl⟩ : syracuseStep 1175197 = 440699) (by norm_num)
theorem B1568429 : Blo 1044610 1568429 := bbase (se 3 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 1568429 = 588161) (by norm_num)
theorem B1765037 : Blo 1044610 1765037 := bbase (se 3 (by rfl) ⟨330944, by rfl⟩ : syracuseStep 1765037 = 661889) (by norm_num)
theorem B2649773 : Blo 1044610 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B1175233 : Blo 1044610 1175233 := bbase (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) (by norm_num)
theorem B1568453 : Blo 1044610 1568453 := bbase (se 4 (by rfl) ⟨147042, by rfl⟩ : syracuseStep 1568453 = 294085) (by norm_num)
theorem B2354885 : Blo 1044610 2354885 := bbase (se 4 (by rfl) ⟨220770, by rfl⟩ : syracuseStep 2354885 = 441541) (by norm_num)
theorem B1568477 : Blo 1044610 1568477 := bbase (se 3 (by rfl) ⟨294089, by rfl⟩ : syracuseStep 1568477 = 588179) (by norm_num)
theorem B1175269 : Blo 1044610 1175269 := bbase (se 4 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 1175269 = 220363) (by norm_num)
theorem B1568501 : Blo 1044610 1568501 := bbase (se 5 (by rfl) ⟨73523, by rfl⟩ : syracuseStep 1568501 = 147047) (by norm_num)
theorem B1175305 : Blo 1044610 1175305 := bbase (se 2 (by rfl) ⟨440739, by rfl⟩ : syracuseStep 1175305 = 881479) (by norm_num)
theorem B1568525 : Blo 1044610 1568525 := bbase (se 3 (by rfl) ⟨294098, by rfl⟩ : syracuseStep 1568525 = 588197) (by norm_num)
theorem B2354957 : Blo 1044610 2354957 := bbase (se 3 (by rfl) ⟨441554, by rfl⟩ : syracuseStep 2354957 = 883109) (by norm_num)
theorem B1568549 : Blo 1044610 1568549 := bbase (se 4 (by rfl) ⟨147051, by rfl⟩ : syracuseStep 1568549 = 294103) (by norm_num)
theorem B1175341 : Blo 1044610 1175341 := bbase (se 3 (by rfl) ⟨220376, by rfl⟩ : syracuseStep 1175341 = 440753) (by norm_num)
theorem B1765165 : Blo 1044610 1765165 := bbase (se 3 (by rfl) ⟨330968, by rfl⟩ : syracuseStep 1765165 = 661937) (by norm_num)
theorem B1568573 : Blo 1044610 1568573 := bbase (se 3 (by rfl) ⟨294107, by rfl⟩ : syracuseStep 1568573 = 588215) (by norm_num)
theorem B1208137 : Blo 1044610 1208137 := bbase (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) (by norm_num)
theorem B1175377 : Blo 1044610 1175377 := bbase (se 2 (by rfl) ⟨440766, by rfl⟩ : syracuseStep 1175377 = 881533) (by norm_num)
theorem B1568597 : Blo 1044610 1568597 := bbase (se 9 (by rfl) ⟨4595, by rfl⟩ : syracuseStep 1568597 = 9191) (by norm_num)
theorem B2355029 : Blo 1044610 2355029 := bbase (se 9 (by rfl) ⟨6899, by rfl⟩ : syracuseStep 2355029 = 13799) (by norm_num)
theorem B3534677 : Blo 1044610 3534677 := bbase (se 9 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 3534677 = 20711) (by norm_num)
theorem B1568621 : Blo 1044610 1568621 := bbase (se 3 (by rfl) ⟨294116, by rfl⟩ : syracuseStep 1568621 = 588233) (by norm_num)
theorem B1175413 : Blo 1044610 1175413 := bbase (se 5 (by rfl) ⟨55097, by rfl⟩ : syracuseStep 1175413 = 110195) (by norm_num)
theorem B1077121 : Blo 1044610 1077121 := bbase (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) (by norm_num)
theorem B1568645 : Blo 1044610 1568645 := bbase (se 4 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 1568645 = 294121) (by norm_num)
theorem B1765253 : Blo 1044610 1765253 := bbase (se 4 (by rfl) ⟨165492, by rfl⟩ : syracuseStep 1765253 = 330985) (by norm_num)
theorem B1175449 : Blo 1044610 1175449 := bbase (se 2 (by rfl) ⟨440793, by rfl⟩ : syracuseStep 1175449 = 881587) (by norm_num)
theorem B1568669 : Blo 1044610 1568669 := bbase (se 3 (by rfl) ⟨294125, by rfl⟩ : syracuseStep 1568669 = 588251) (by norm_num)
theorem B2355101 : Blo 1044610 2355101 := bbase (se 3 (by rfl) ⟨441581, by rfl⟩ : syracuseStep 2355101 = 883163) (by norm_num)
theorem B1568693 : Blo 1044610 1568693 := bbase (se 5 (by rfl) ⟨73532, by rfl⟩ : syracuseStep 1568693 = 147065) (by norm_num)
theorem B1175485 : Blo 1044610 1175485 := bbase (se 3 (by rfl) ⟨220403, by rfl⟩ : syracuseStep 1175485 = 440807) (by norm_num)
theorem B1568717 : Blo 1044610 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B1175521 : Blo 1044610 1175521 := bbase (se 2 (by rfl) ⟨440820, by rfl⟩ : syracuseStep 1175521 = 881641) (by norm_num)
theorem B1568741 : Blo 1044610 1568741 := bbase (se 4 (by rfl) ⟨147069, by rfl⟩ : syracuseStep 1568741 = 294139) (by norm_num)
theorem B2355173 : Blo 1044610 2355173 := bbase (se 4 (by rfl) ⟨220797, by rfl⟩ : syracuseStep 2355173 = 441595) (by norm_num)
theorem B1568765 : Blo 1044610 1568765 := bbase (se 3 (by rfl) ⟨294143, by rfl⟩ : syracuseStep 1568765 = 588287) (by norm_num)
theorem B1175557 : Blo 1044610 1175557 := bbase (se 4 (by rfl) ⟨110208, by rfl⟩ : syracuseStep 1175557 = 220417) (by norm_num)
theorem B1765381 : Blo 1044610 1765381 := bbase (se 4 (by rfl) ⟨165504, by rfl⟩ : syracuseStep 1765381 = 331009) (by norm_num)
theorem B2650117 : Blo 1044610 2650117 := bbase (se 4 (by rfl) ⟨248448, by rfl⟩ : syracuseStep 2650117 = 496897) (by norm_num)
theorem B1568789 : Blo 1044610 1568789 := bbase (se 6 (by rfl) ⟨36768, by rfl⟩ : syracuseStep 1568789 = 73537) (by norm_num)
theorem B2977829 : Blo 1044610 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B1175593 : Blo 1044610 1175593 := bbase (se 2 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 1175593 = 881695) (by norm_num)
theorem B1568813 : Blo 1044610 1568813 := bbase (se 3 (by rfl) ⟨294152, by rfl⟩ : syracuseStep 1568813 = 588305) (by norm_num)
theorem B2355245 : Blo 1044610 2355245 := bbase (se 3 (by rfl) ⟨441608, by rfl⟩ : syracuseStep 2355245 = 883217) (by norm_num)
theorem B1568837 : Blo 1044610 1568837 := bbase (se 4 (by rfl) ⟨147078, by rfl⟩ : syracuseStep 1568837 = 294157) (by norm_num)
theorem B1175629 : Blo 1044610 1175629 := bbase (se 3 (by rfl) ⟨220430, by rfl⟩ : syracuseStep 1175629 = 440861) (by norm_num)
theorem B2519117 : Blo 1044610 2519117 := bbase (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) (by norm_num)
theorem B1568861 : Blo 1044610 1568861 := bbase (se 3 (by rfl) ⟨294161, by rfl⟩ : syracuseStep 1568861 = 588323) (by norm_num)
theorem B1765469 : Blo 1044610 1765469 := bbase (se 3 (by rfl) ⟨331025, by rfl⟩ : syracuseStep 1765469 = 662051) (by norm_num)
theorem B1175665 : Blo 1044610 1175665 := bbase (se 2 (by rfl) ⟨440874, by rfl⟩ : syracuseStep 1175665 = 881749) (by norm_num)
theorem B1568885 : Blo 1044610 1568885 := bbase (se 5 (by rfl) ⟨73541, by rfl⟩ : syracuseStep 1568885 = 147083) (by norm_num)
theorem B2355317 : Blo 1044610 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B2650229 : Blo 1044610 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B1568909 : Blo 1044610 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B1175701 : Blo 1044610 1175701 := bbase (se 6 (by rfl) ⟨27555, by rfl⟩ : syracuseStep 1175701 = 55111) (by norm_num)
theorem B1568933 : Blo 1044610 1568933 := bbase (se 4 (by rfl) ⟨147087, by rfl⟩ : syracuseStep 1568933 = 294175) (by norm_num)
theorem B1175737 : Blo 1044610 1175737 := bbase (se 2 (by rfl) ⟨440901, by rfl⟩ : syracuseStep 1175737 = 881803) (by norm_num)
theorem B1568957 : Blo 1044610 1568957 := bbase (se 3 (by rfl) ⟨294179, by rfl⟩ : syracuseStep 1568957 = 588359) (by norm_num)
theorem B2355389 : Blo 1044610 2355389 := bbase (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) (by norm_num)
theorem B1241285 : Blo 1044610 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B1568981 : Blo 1044610 1568981 := bbase (se 7 (by rfl) ⟨18386, by rfl⟩ : syracuseStep 1568981 = 36773) (by norm_num)
theorem B1175773 : Blo 1044610 1175773 := bbase (se 3 (by rfl) ⟨220457, by rfl⟩ : syracuseStep 1175773 = 440915) (by norm_num)
theorem B1765597 : Blo 1044610 1765597 := bbase (se 3 (by rfl) ⟨331049, by rfl⟩ : syracuseStep 1765597 = 662099) (by norm_num)
theorem B1569005 : Blo 1044610 1569005 := bbase (se 3 (by rfl) ⟨294188, by rfl⟩ : syracuseStep 1569005 = 588377) (by norm_num)
theorem B1175809 : Blo 1044610 1175809 := bbase (se 2 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 1175809 = 881857) (by norm_num)
theorem B1569029 : Blo 1044610 1569029 := bbase (se 4 (by rfl) ⟨147096, by rfl⟩ : syracuseStep 1569029 = 294193) (by norm_num)
theorem B2355461 : Blo 1044610 2355461 := bbase (se 4 (by rfl) ⟨220824, by rfl⟩ : syracuseStep 2355461 = 441649) (by norm_num)
theorem B3535109 : Blo 1044610 3535109 := bbase (se 4 (by rfl) ⟨331416, by rfl⟩ : syracuseStep 3535109 = 662833) (by norm_num)
theorem B1569053 : Blo 1044610 1569053 := bbase (se 3 (by rfl) ⟨294197, by rfl⟩ : syracuseStep 1569053 = 588395) (by norm_num)
theorem B1175845 : Blo 1044610 1175845 := bbase (se 4 (by rfl) ⟨110235, by rfl⟩ : syracuseStep 1175845 = 220471) (by norm_num)
theorem B1569077 : Blo 1044610 1569077 := bbase (se 5 (by rfl) ⟨73550, by rfl⟩ : syracuseStep 1569077 = 147101) (by norm_num)
theorem B1765685 : Blo 1044610 1765685 := bbase (se 5 (by rfl) ⟨82766, by rfl⟩ : syracuseStep 1765685 = 165533) (by norm_num)
theorem B2650421 : Blo 1044610 2650421 := bbase (se 5 (by rfl) ⟨124238, by rfl⟩ : syracuseStep 2650421 = 248477) (by norm_num)
theorem B1175881 : Blo 1044610 1175881 := bbase (se 2 (by rfl) ⟨440955, by rfl⟩ : syracuseStep 1175881 = 881911) (by norm_num)
theorem B1569101 : Blo 1044610 1569101 := bbase (se 3 (by rfl) ⟨294206, by rfl⟩ : syracuseStep 1569101 = 588413) (by norm_num)
theorem B2355533 : Blo 1044610 2355533 := bbase (se 3 (by rfl) ⟨441662, by rfl⟩ : syracuseStep 2355533 = 883325) (by norm_num)
theorem B1569125 : Blo 1044610 1569125 := bbase (se 4 (by rfl) ⟨147105, by rfl⟩ : syracuseStep 1569125 = 294211) (by norm_num)
theorem B1175917 : Blo 1044610 1175917 := bbase (se 3 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 1175917 = 440969) (by norm_num)
theorem B1569149 : Blo 1044610 1569149 := bbase (se 3 (by rfl) ⟨294215, by rfl⟩ : syracuseStep 1569149 = 588431) (by norm_num)
theorem B1700221 : Blo 1044610 1700221 := bbase (se 3 (by rfl) ⟨318791, by rfl⟩ : syracuseStep 1700221 = 637583) (by norm_num)
theorem B1175953 : Blo 1044610 1175953 := bbase (se 2 (by rfl) ⟨440982, by rfl⟩ : syracuseStep 1175953 = 881965) (by norm_num)
theorem B1569173 : Blo 1044610 1569173 := bbase (se 6 (by rfl) ⟨36777, by rfl⟩ : syracuseStep 1569173 = 73555) (by norm_num)
theorem B2355605 : Blo 1044610 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B1569197 : Blo 1044610 1569197 := bbase (se 3 (by rfl) ⟨294224, by rfl⟩ : syracuseStep 1569197 = 588449) (by norm_num)
theorem B1175989 : Blo 1044610 1175989 := bbase (se 5 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 1175989 = 110249) (by norm_num)
theorem B1765813 : Blo 1044610 1765813 := bbase (se 5 (by rfl) ⟨82772, by rfl⟩ : syracuseStep 1765813 = 165545) (by norm_num)
theorem B1569221 : Blo 1044610 1569221 := bbase (se 4 (by rfl) ⟨147114, by rfl⟩ : syracuseStep 1569221 = 294229) (by norm_num)
theorem B1700293 : Blo 1044610 1700293 := bbase (se 4 (by rfl) ⟨159402, by rfl⟩ : syracuseStep 1700293 = 318805) (by norm_num)
theorem B1176025 : Blo 1044610 1176025 := bbase (se 2 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 1176025 = 882019) (by norm_num)
theorem B1569245 : Blo 1044610 1569245 := bbase (se 3 (by rfl) ⟨294233, by rfl⟩ : syracuseStep 1569245 = 588467) (by norm_num)
theorem B2355677 : Blo 1044610 2355677 := bbase (se 3 (by rfl) ⟨441689, by rfl⟩ : syracuseStep 2355677 = 883379) (by norm_num)
theorem B1569269 : Blo 1044610 1569269 := bbase (se 5 (by rfl) ⟨73559, by rfl⟩ : syracuseStep 1569269 = 147119) (by norm_num)
theorem B1176061 : Blo 1044610 1176061 := bbase (se 3 (by rfl) ⟨220511, by rfl⟩ : syracuseStep 1176061 = 441023) (by norm_num)
theorem B1569293 : Blo 1044610 1569293 := bbase (se 3 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 1569293 = 588485) (by norm_num)
theorem B1765901 : Blo 1044610 1765901 := bbase (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) (by norm_num)
theorem B5960213 : Blo 1044610 5960213 := bbase (se 6 (by rfl) ⟨139692, by rfl⟩ : syracuseStep 5960213 = 279385) (by norm_num)
theorem B1176097 : Blo 1044610 1176097 := bbase (se 2 (by rfl) ⟨441036, by rfl⟩ : syracuseStep 1176097 = 882073) (by norm_num)
theorem B1569317 : Blo 1044610 1569317 := bbase (se 4 (by rfl) ⟨147123, by rfl⟩ : syracuseStep 1569317 = 294247) (by norm_num)
theorem B1274405 : Blo 1044610 1274405 := bbase (se 4 (by rfl) ⟨119475, by rfl⟩ : syracuseStep 1274405 = 238951) (by norm_num)
theorem B2355749 : Blo 1044610 2355749 := bbase (se 4 (by rfl) ⟨220851, by rfl⟩ : syracuseStep 2355749 = 441703) (by norm_num)
theorem B1569341 : Blo 1044610 1569341 := bbase (se 3 (by rfl) ⟨294251, by rfl⟩ : syracuseStep 1569341 = 588503) (by norm_num)
theorem B1176133 : Blo 1044610 1176133 := bbase (se 4 (by rfl) ⟨110262, by rfl⟩ : syracuseStep 1176133 = 220525) (by norm_num)
theorem B1569365 : Blo 1044610 1569365 := bbase (se 8 (by rfl) ⟨9195, by rfl⟩ : syracuseStep 1569365 = 18391) (by norm_num)
theorem B1176169 : Blo 1044610 1176169 := bbase (se 2 (by rfl) ⟨441063, by rfl⟩ : syracuseStep 1176169 = 882127) (by norm_num)
theorem B1569389 : Blo 1044610 1569389 := bbase (se 3 (by rfl) ⟨294260, by rfl⟩ : syracuseStep 1569389 = 588521) (by norm_num)
theorem B2355821 : Blo 1044610 2355821 := bbase (se 3 (by rfl) ⟨441716, by rfl⟩ : syracuseStep 2355821 = 883433) (by norm_num)
theorem B1569413 : Blo 1044610 1569413 := bbase (se 4 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 1569413 = 294265) (by norm_num)
theorem B1176205 : Blo 1044610 1176205 := bbase (se 3 (by rfl) ⟨220538, by rfl⟩ : syracuseStep 1176205 = 441077) (by norm_num)
theorem B1766029 : Blo 1044610 1766029 := bbase (se 3 (by rfl) ⟨331130, by rfl⟩ : syracuseStep 1766029 = 662261) (by norm_num)
theorem B2650765 : Blo 1044610 2650765 := bbase (se 3 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 2650765 = 994037) (by norm_num)
theorem B1569437 : Blo 1044610 1569437 := bbase (se 3 (by rfl) ⟨294269, by rfl⟩ : syracuseStep 1569437 = 588539) (by norm_num)
theorem B1176241 : Blo 1044610 1176241 := bbase (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) (by norm_num)
theorem B1569461 : Blo 1044610 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B2355893 : Blo 1044610 2355893 := bbase (se 5 (by rfl) ⟨110432, by rfl⟩ : syracuseStep 2355893 = 220865) (by norm_num)
theorem B3535541 : Blo 1044610 3535541 := bbase (se 5 (by rfl) ⟨165728, by rfl⟩ : syracuseStep 3535541 = 331457) (by norm_num)
theorem B5305013 : Blo 1044610 5305013 := bbase (se 5 (by rfl) ⟨248672, by rfl⟩ : syracuseStep 5305013 = 497345) (by norm_num)
theorem B7959221 : Blo 1044610 7959221 := bbase (se 5 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 7959221 = 746177) (by norm_num)
theorem B1569485 : Blo 1044610 1569485 := bbase (se 3 (by rfl) ⟨294278, by rfl⟩ : syracuseStep 1569485 = 588557) (by norm_num)
theorem B1176277 : Blo 1044610 1176277 := bbase (se 7 (by rfl) ⟨13784, by rfl⟩ : syracuseStep 1176277 = 27569) (by norm_num)
theorem B1569509 : Blo 1044610 1569509 := bbase (se 4 (by rfl) ⟨147141, by rfl⟩ : syracuseStep 1569509 = 294283) (by norm_num)
theorem B1766117 : Blo 1044610 1766117 := bbase (se 4 (by rfl) ⟨165573, by rfl⟩ : syracuseStep 1766117 = 331147) (by norm_num)
theorem B3764981 : Blo 1044610 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B1176313 : Blo 1044610 1176313 := bbase (se 2 (by rfl) ⟨441117, by rfl⟩ : syracuseStep 1176313 = 882235) (by norm_num)
theorem B1569533 : Blo 1044610 1569533 := bbase (se 3 (by rfl) ⟨294287, by rfl⟩ : syracuseStep 1569533 = 588575) (by norm_num)
theorem B2355965 : Blo 1044610 2355965 := bbase (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) (by norm_num)
theorem B2650877 : Blo 1044610 2650877 := bbase (se 3 (by rfl) ⟨497039, by rfl⟩ : syracuseStep 2650877 = 994079) (by norm_num)
theorem B1569557 : Blo 1044610 1569557 := bbase (se 6 (by rfl) ⟨36786, by rfl⟩ : syracuseStep 1569557 = 73573) (by norm_num)
theorem B1176349 : Blo 1044610 1176349 := bbase (se 3 (by rfl) ⟨220565, by rfl⟩ : syracuseStep 1176349 = 441131) (by norm_num)
theorem B1569581 : Blo 1044610 1569581 := bbase (se 3 (by rfl) ⟨294296, by rfl⟩ : syracuseStep 1569581 = 588593) (by norm_num)
theorem B1176385 : Blo 1044610 1176385 := bbase (se 2 (by rfl) ⟨441144, by rfl⟩ : syracuseStep 1176385 = 882289) (by norm_num)
theorem B1569605 : Blo 1044610 1569605 := bbase (se 4 (by rfl) ⟨147150, by rfl⟩ : syracuseStep 1569605 = 294301) (by norm_num)
theorem B2356037 : Blo 1044610 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B1569629 : Blo 1044610 1569629 := bbase (se 3 (by rfl) ⟨294305, by rfl⟩ : syracuseStep 1569629 = 588611) (by norm_num)
theorem B1176421 : Blo 1044610 1176421 := bbase (se 4 (by rfl) ⟨110289, by rfl⟩ : syracuseStep 1176421 = 220579) (by norm_num)
theorem B1766245 : Blo 1044610 1766245 := bbase (se 4 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 1766245 = 331171) (by norm_num)
theorem B1569653 : Blo 1044610 1569653 := bbase (se 5 (by rfl) ⟨73577, by rfl⟩ : syracuseStep 1569653 = 147155) (by norm_num)
theorem B1176457 : Blo 1044610 1176457 := bbase (se 2 (by rfl) ⟨441171, by rfl⟩ : syracuseStep 1176457 = 882343) (by norm_num)
theorem B1569677 : Blo 1044610 1569677 := bbase (se 3 (by rfl) ⟨294314, by rfl⟩ : syracuseStep 1569677 = 588629) (by norm_num)
theorem B2356109 : Blo 1044610 2356109 := bbase (se 3 (by rfl) ⟨441770, by rfl⟩ : syracuseStep 2356109 = 883541) (by norm_num)
theorem B1569701 : Blo 1044610 1569701 := bbase (se 4 (by rfl) ⟨147159, by rfl⟩ : syracuseStep 1569701 = 294319) (by norm_num)
theorem B1176493 : Blo 1044610 1176493 := bbase (se 3 (by rfl) ⟨220592, by rfl⟩ : syracuseStep 1176493 = 441185) (by norm_num)
theorem B1569725 : Blo 1044610 1569725 := bbase (se 3 (by rfl) ⟨294323, by rfl⟩ : syracuseStep 1569725 = 588647) (by norm_num)
theorem B1766333 : Blo 1044610 1766333 := bbase (se 3 (by rfl) ⟨331187, by rfl⟩ : syracuseStep 1766333 = 662375) (by norm_num)
theorem B2651069 : Blo 1044610 2651069 := bbase (se 3 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 2651069 = 994151) (by norm_num)
theorem B1176529 : Blo 1044610 1176529 := bbase (se 2 (by rfl) ⟨441198, by rfl⟩ : syracuseStep 1176529 = 882397) (by norm_num)
theorem B1569749 : Blo 1044610 1569749 := bbase (se 7 (by rfl) ⟨18395, by rfl⟩ : syracuseStep 1569749 = 36791) (by norm_num)
theorem B2356181 : Blo 1044610 2356181 := bbase (se 7 (by rfl) ⟨27611, by rfl⟩ : syracuseStep 2356181 = 55223) (by norm_num)
theorem B1274845 : Blo 1044610 1274845 := bbase (se 3 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 1274845 = 478067) (by norm_num)
theorem B1569773 : Blo 1044610 1569773 := bbase (se 3 (by rfl) ⟨294332, by rfl⟩ : syracuseStep 1569773 = 588665) (by norm_num)
theorem B1176565 : Blo 1044610 1176565 := bbase (se 5 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 1176565 = 110303) (by norm_num)
theorem B1569797 : Blo 1044610 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B1700869 : Blo 1044610 1700869 := bbase (se 4 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 1700869 = 318913) (by norm_num)
theorem B1176601 : Blo 1044610 1176601 := bbase (se 2 (by rfl) ⟨441225, by rfl⟩ : syracuseStep 1176601 = 882451) (by norm_num)
theorem B1569821 : Blo 1044610 1569821 := bbase (se 3 (by rfl) ⟨294341, by rfl⟩ : syracuseStep 1569821 = 588683) (by norm_num)
theorem B2356253 : Blo 1044610 2356253 := bbase (se 3 (by rfl) ⟨441797, by rfl⟩ : syracuseStep 2356253 = 883595) (by norm_num)
theorem B1569845 : Blo 1044610 1569845 := bbase (se 5 (by rfl) ⟨73586, by rfl⟩ : syracuseStep 1569845 = 147173) (by norm_num)
theorem B1176637 : Blo 1044610 1176637 := bbase (se 3 (by rfl) ⟨220619, by rfl⟩ : syracuseStep 1176637 = 441239) (by norm_num)
theorem B1766461 : Blo 1044610 1766461 := bbase (se 3 (by rfl) ⟨331211, by rfl⟩ : syracuseStep 1766461 = 662423) (by norm_num)
theorem B1569869 : Blo 1044610 1569869 := bbase (se 3 (by rfl) ⟨294350, by rfl⟩ : syracuseStep 1569869 = 588701) (by norm_num)
theorem B1176673 : Blo 1044610 1176673 := bbase (se 2 (by rfl) ⟨441252, by rfl⟩ : syracuseStep 1176673 = 882505) (by norm_num)
theorem B1569893 : Blo 1044610 1569893 := bbase (se 4 (by rfl) ⟨147177, by rfl⟩ : syracuseStep 1569893 = 294355) (by norm_num)
theorem B2356325 : Blo 1044610 2356325 := bbase (se 4 (by rfl) ⟨220905, by rfl⟩ : syracuseStep 2356325 = 441811) (by norm_num)
theorem B3535973 : Blo 1044610 3535973 := bbase (se 4 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 3535973 = 662995) (by norm_num)
theorem B1569917 : Blo 1044610 1569917 := bbase (se 3 (by rfl) ⟨294359, by rfl⟩ : syracuseStep 1569917 = 588719) (by norm_num)
theorem B1176709 : Blo 1044610 1176709 := bbase (se 4 (by rfl) ⟨110316, by rfl⟩ : syracuseStep 1176709 = 220633) (by norm_num)
theorem B1569941 : Blo 1044610 1569941 := bbase (se 6 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 1569941 = 73591) (by norm_num)
theorem B1766549 : Blo 1044610 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B1176745 : Blo 1044610 1176745 := bbase (se 2 (by rfl) ⟨441279, by rfl⟩ : syracuseStep 1176745 = 882559) (by norm_num)
theorem B1569965 : Blo 1044610 1569965 := bbase (se 3 (by rfl) ⟨294368, by rfl⟩ : syracuseStep 1569965 = 588737) (by norm_num)
theorem B2356397 : Blo 1044610 2356397 := bbase (se 3 (by rfl) ⟨441824, by rfl⟩ : syracuseStep 2356397 = 883649) (by norm_num)
theorem B2979013 : Blo 1044610 2979013 := bbase (se 4 (by rfl) ⟨279282, by rfl⟩ : syracuseStep 2979013 = 558565) (by norm_num)
theorem B1569989 : Blo 1044610 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B1176781 : Blo 1044610 1176781 := bbase (se 3 (by rfl) ⟨220646, by rfl⟩ : syracuseStep 1176781 = 441293) (by norm_num)
theorem B1570013 : Blo 1044610 1570013 := bbase (se 3 (by rfl) ⟨294377, by rfl⟩ : syracuseStep 1570013 = 588755) (by norm_num)
theorem B1176817 : Blo 1044610 1176817 := bbase (se 2 (by rfl) ⟨441306, by rfl⟩ : syracuseStep 1176817 = 882613) (by norm_num)
theorem B1570037 : Blo 1044610 1570037 := bbase (se 5 (by rfl) ⟨73595, by rfl⟩ : syracuseStep 1570037 = 147191) (by norm_num)
theorem B2356469 : Blo 1044610 2356469 := bbase (se 5 (by rfl) ⟨110459, by rfl⟩ : syracuseStep 2356469 = 220919) (by norm_num)
theorem B1570061 : Blo 1044610 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B1176853 : Blo 1044610 1176853 := bbase (se 6 (by rfl) ⟨27582, by rfl⟩ : syracuseStep 1176853 = 55165) (by norm_num)
theorem B1766677 : Blo 1044610 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B2651413 : Blo 1044610 2651413 := bbase (se 6 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 2651413 = 124285) (by norm_num)
theorem B1570085 : Blo 1044610 1570085 := bbase (se 4 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 1570085 = 294391) (by norm_num)
theorem B1176889 : Blo 1044610 1176889 := bbase (se 2 (by rfl) ⟨441333, by rfl⟩ : syracuseStep 1176889 = 882667) (by norm_num)
theorem B1570109 : Blo 1044610 1570109 := bbase (se 3 (by rfl) ⟨294395, by rfl⟩ : syracuseStep 1570109 = 588791) (by norm_num)
theorem B2356541 : Blo 1044610 2356541 := bbase (se 3 (by rfl) ⟨441851, by rfl⟩ : syracuseStep 2356541 = 883703) (by norm_num)
theorem B1570133 : Blo 1044610 1570133 := bbase (se 13 (by rfl) ⟨287, by rfl⟩ : syracuseStep 1570133 = 575) (by norm_num)
theorem B1176925 : Blo 1044610 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B2979173 : Blo 1044610 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B1570157 : Blo 1044610 1570157 := bbase (se 3 (by rfl) ⟨294404, by rfl⟩ : syracuseStep 1570157 = 588809) (by norm_num)
theorem B1766765 : Blo 1044610 1766765 := bbase (se 3 (by rfl) ⟨331268, by rfl⟩ : syracuseStep 1766765 = 662537) (by norm_num)
theorem B1176961 : Blo 1044610 1176961 := bbase (se 2 (by rfl) ⟨441360, by rfl⟩ : syracuseStep 1176961 = 882721) (by norm_num)
theorem B1570181 : Blo 1044610 1570181 := bbase (se 4 (by rfl) ⟨147204, by rfl⟩ : syracuseStep 1570181 = 294409) (by norm_num)
theorem B2356613 : Blo 1044610 2356613 := bbase (se 4 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 2356613 = 441865) (by norm_num)
theorem B2651525 : Blo 1044610 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B1570205 : Blo 1044610 1570205 := bbase (se 3 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 1570205 = 588827) (by norm_num)
theorem B2553245 : Blo 1044610 2553245 := bbase (se 3 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 2553245 = 957467) (by norm_num)
theorem B1176997 : Blo 1044610 1176997 := bbase (se 4 (by rfl) ⟨110343, by rfl⟩ : syracuseStep 1176997 = 220687) (by norm_num)
theorem B1570229 : Blo 1044610 1570229 := bbase (se 5 (by rfl) ⟨73604, by rfl⟩ : syracuseStep 1570229 = 147209) (by norm_num)
theorem B1177033 : Blo 1044610 1177033 := bbase (se 2 (by rfl) ⟨441387, by rfl⟩ : syracuseStep 1177033 = 882775) (by norm_num)
theorem B1570253 : Blo 1044610 1570253 := bbase (se 3 (by rfl) ⟨294422, by rfl⟩ : syracuseStep 1570253 = 588845) (by norm_num)
theorem B2356685 : Blo 1044610 2356685 := bbase (se 3 (by rfl) ⟨441878, by rfl⟩ : syracuseStep 2356685 = 883757) (by norm_num)
theorem B1570277 : Blo 1044610 1570277 := bbase (se 4 (by rfl) ⟨147213, by rfl⟩ : syracuseStep 1570277 = 294427) (by norm_num)
theorem B1177069 : Blo 1044610 1177069 := bbase (se 3 (by rfl) ⟨220700, by rfl⟩ : syracuseStep 1177069 = 441401) (by norm_num)
theorem B1766893 : Blo 1044610 1766893 := bbase (se 3 (by rfl) ⟨331292, by rfl⟩ : syracuseStep 1766893 = 662585) (by norm_num)
theorem B1340921 : Blo 1044610 1340921 := bbase (se 2 (by rfl) ⟨502845, by rfl⟩ : syracuseStep 1340921 = 1005691) (by norm_num)
theorem B1570301 : Blo 1044610 1570301 := bbase (se 3 (by rfl) ⟨294431, by rfl⟩ : syracuseStep 1570301 = 588863) (by norm_num)
theorem B1177105 : Blo 1044610 1177105 := bbase (se 2 (by rfl) ⟨441414, by rfl⟩ : syracuseStep 1177105 = 882829) (by norm_num)
theorem B8484373 : Blo 1044610 8484373 := bbase (se 6 (by rfl) ⟨198852, by rfl⟩ : syracuseStep 8484373 = 397705) (by norm_num)
theorem B1570325 : Blo 1044610 1570325 := bbase (se 6 (by rfl) ⟨36804, by rfl⟩ : syracuseStep 1570325 = 73609) (by norm_num)
theorem B2356757 : Blo 1044610 2356757 := bbase (se 6 (by rfl) ⟨55236, by rfl⟩ : syracuseStep 2356757 = 110473) (by norm_num)
theorem B3536405 : Blo 1044610 3536405 := bbase (se 6 (by rfl) ⟨82884, by rfl⟩ : syracuseStep 3536405 = 165769) (by norm_num)
theorem B1570349 : Blo 1044610 1570349 := bbase (se 3 (by rfl) ⟨294440, by rfl⟩ : syracuseStep 1570349 = 588881) (by norm_num)
theorem B1177141 : Blo 1044610 1177141 := bbase (se 5 (by rfl) ⟨55178, by rfl⟩ : syracuseStep 1177141 = 110357) (by norm_num)
theorem B2651717 : Blo 1044610 2651717 := bbase (se 4 (by rfl) ⟨248598, by rfl⟩ : syracuseStep 2651717 = 497197) (by norm_num)
theorem B4355653 : Blo 1044610 4355653 := bbase (se 4 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 4355653 = 816685) (by norm_num)
theorem B1570373 : Blo 1044610 1570373 := bbase (se 4 (by rfl) ⟨147222, by rfl⟩ : syracuseStep 1570373 = 294445) (by norm_num)
theorem B1766981 : Blo 1044610 1766981 := bbase (se 4 (by rfl) ⟨165654, by rfl⟩ : syracuseStep 1766981 = 331309) (by norm_num)
theorem B2979413 : Blo 1044610 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B1177177 : Blo 1044610 1177177 := bbase (se 2 (by rfl) ⟨441441, by rfl⟩ : syracuseStep 1177177 = 882883) (by norm_num)
theorem B1570397 : Blo 1044610 1570397 := bbase (se 3 (by rfl) ⟨294449, by rfl⟩ : syracuseStep 1570397 = 588899) (by norm_num)
theorem B2356829 : Blo 1044610 2356829 := bbase (se 3 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 2356829 = 883811) (by norm_num)
theorem B1570421 : Blo 1044610 1570421 := bbase (se 5 (by rfl) ⟨73613, by rfl⟩ : syracuseStep 1570421 = 147227) (by norm_num)
theorem B1177213 : Blo 1044610 1177213 := bbase (se 3 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 1177213 = 441455) (by norm_num)
theorem B1570445 : Blo 1044610 1570445 := bbase (se 3 (by rfl) ⟨294458, by rfl⟩ : syracuseStep 1570445 = 588917) (by norm_num)
theorem B1177249 : Blo 1044610 1177249 := bbase (se 2 (by rfl) ⟨441468, by rfl⟩ : syracuseStep 1177249 = 882937) (by norm_num)
theorem B1570469 : Blo 1044610 1570469 := bbase (se 4 (by rfl) ⟨147231, by rfl⟩ : syracuseStep 1570469 = 294463) (by norm_num)
theorem B2356901 : Blo 1044610 2356901 := bbase (se 4 (by rfl) ⟨220959, by rfl⟩ : syracuseStep 2356901 = 441919) (by norm_num)
theorem B5732021 : Blo 1044610 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B5961397 : Blo 1044610 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B1570493 : Blo 1044610 1570493 := bbase (se 3 (by rfl) ⟨294467, by rfl⟩ : syracuseStep 1570493 = 588935) (by norm_num)
theorem B1177285 : Blo 1044610 1177285 := bbase (se 4 (by rfl) ⟨110370, by rfl⟩ : syracuseStep 1177285 = 220741) (by norm_num)
theorem B1767109 : Blo 1044610 1767109 := bbase (se 4 (by rfl) ⟨165666, by rfl⟩ : syracuseStep 1767109 = 331333) (by norm_num)
theorem B1570517 : Blo 1044610 1570517 := bbase (se 7 (by rfl) ⟨18404, by rfl⟩ : syracuseStep 1570517 = 36809) (by norm_num)
theorem B3765989 : Blo 1044610 3765989 := bbase (se 4 (by rfl) ⟨353061, by rfl⟩ : syracuseStep 3765989 = 706123) (by norm_num)
theorem B1177321 : Blo 1044610 1177321 := bbase (se 2 (by rfl) ⟨441495, by rfl⟩ : syracuseStep 1177321 = 882991) (by norm_num)
theorem B1570541 : Blo 1044610 1570541 := bbase (se 3 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 1570541 = 588953) (by norm_num)
theorem B2356973 : Blo 1044610 2356973 := bbase (se 3 (by rfl) ⟨441932, by rfl⟩ : syracuseStep 2356973 = 883865) (by norm_num)
theorem B1570565 : Blo 1044610 1570565 := bbase (se 4 (by rfl) ⟨147240, by rfl⟩ : syracuseStep 1570565 = 294481) (by norm_num)
theorem B1177357 : Blo 1044610 1177357 := bbase (se 3 (by rfl) ⟨220754, by rfl⟩ : syracuseStep 1177357 = 441509) (by norm_num)
theorem B2979605 : Blo 1044610 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B1570589 : Blo 1044610 1570589 := bbase (se 3 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 1570589 = 588971) (by norm_num)
theorem B1767197 : Blo 1044610 1767197 := bbase (se 3 (by rfl) ⟨331349, by rfl⟩ : syracuseStep 1767197 = 662699) (by norm_num)
theorem B1177393 : Blo 1044610 1177393 := bbase (se 2 (by rfl) ⟨441522, by rfl⟩ : syracuseStep 1177393 = 883045) (by norm_num)
theorem B1570613 : Blo 1044610 1570613 := bbase (se 5 (by rfl) ⟨73622, by rfl⟩ : syracuseStep 1570613 = 147245) (by norm_num)
theorem B2357045 : Blo 1044610 2357045 := bbase (se 5 (by rfl) ⟨110486, by rfl⟩ : syracuseStep 2357045 = 220973) (by norm_num)
theorem B1570637 : Blo 1044610 1570637 := bbase (se 3 (by rfl) ⟨294494, by rfl⟩ : syracuseStep 1570637 = 588989) (by norm_num)
theorem B1177429 : Blo 1044610 1177429 := bbase (se 9 (by rfl) ⟨3449, by rfl⟩ : syracuseStep 1177429 = 6899) (by norm_num)
theorem B1570661 : Blo 1044610 1570661 := bbase (se 4 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 1570661 = 294499) (by norm_num)
theorem B1177465 : Blo 1044610 1177465 := bbase (se 2 (by rfl) ⟨441549, by rfl⟩ : syracuseStep 1177465 = 883099) (by norm_num)
theorem B1570685 : Blo 1044610 1570685 := bbase (se 3 (by rfl) ⟨294503, by rfl⟩ : syracuseStep 1570685 = 589007) (by norm_num)
theorem B2357117 : Blo 1044610 2357117 := bbase (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) (by norm_num)
theorem B1570709 : Blo 1044610 1570709 := bbase (se 6 (by rfl) ⟨36813, by rfl⟩ : syracuseStep 1570709 = 73627) (by norm_num)
theorem B1177501 : Blo 1044610 1177501 := bbase (se 3 (by rfl) ⟨220781, by rfl⟩ : syracuseStep 1177501 = 441563) (by norm_num)
theorem B1767325 : Blo 1044610 1767325 := bbase (se 3 (by rfl) ⟨331373, by rfl⟩ : syracuseStep 1767325 = 662747) (by norm_num)
theorem B2652061 : Blo 1044610 2652061 := bbase (se 3 (by rfl) ⟨497261, by rfl⟩ : syracuseStep 2652061 = 994523) (by norm_num)
theorem B1570733 : Blo 1044610 1570733 := bbase (se 3 (by rfl) ⟨294512, by rfl⟩ : syracuseStep 1570733 = 589025) (by norm_num)
theorem B1177537 : Blo 1044610 1177537 := bbase (se 2 (by rfl) ⟨441576, by rfl⟩ : syracuseStep 1177537 = 883153) (by norm_num)
theorem B1570757 : Blo 1044610 1570757 := bbase (se 4 (by rfl) ⟨147258, by rfl⟩ : syracuseStep 1570757 = 294517) (by norm_num)
theorem B2357189 : Blo 1044610 2357189 := bbase (se 4 (by rfl) ⟨220986, by rfl⟩ : syracuseStep 2357189 = 441973) (by norm_num)
theorem B3536837 : Blo 1044610 3536837 := bbase (se 4 (by rfl) ⟨331578, by rfl⟩ : syracuseStep 3536837 = 663157) (by norm_num)
theorem B5306309 : Blo 1044610 5306309 := bbase (se 4 (by rfl) ⟨497466, by rfl⟩ : syracuseStep 5306309 = 994933) (by norm_num)
theorem B1570781 : Blo 1044610 1570781 := bbase (se 3 (by rfl) ⟨294521, by rfl⟩ : syracuseStep 1570781 = 589043) (by norm_num)
theorem B1177573 : Blo 1044610 1177573 := bbase (se 4 (by rfl) ⟨110397, by rfl⟩ : syracuseStep 1177573 = 220795) (by norm_num)
theorem B1570805 : Blo 1044610 1570805 := bbase (se 5 (by rfl) ⟨73631, by rfl⟩ : syracuseStep 1570805 = 147263) (by norm_num)
theorem B1767413 : Blo 1044610 1767413 := bbase (se 5 (by rfl) ⟨82847, by rfl⟩ : syracuseStep 1767413 = 165695) (by norm_num)
theorem B1177609 : Blo 1044610 1177609 := bbase (se 2 (by rfl) ⟨441603, by rfl⟩ : syracuseStep 1177609 = 883207) (by norm_num)
theorem B1570829 : Blo 1044610 1570829 := bbase (se 3 (by rfl) ⟨294530, by rfl⟩ : syracuseStep 1570829 = 589061) (by norm_num)
theorem B2357261 : Blo 1044610 2357261 := bbase (se 3 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 2357261 = 883973) (by norm_num)
theorem B2652173 : Blo 1044610 2652173 := bbase (se 3 (by rfl) ⟨497282, by rfl⟩ : syracuseStep 2652173 = 994565) (by norm_num)
theorem B1570853 : Blo 1044610 1570853 := bbase (se 4 (by rfl) ⟨147267, by rfl⟩ : syracuseStep 1570853 = 294535) (by norm_num)
theorem B1177645 : Blo 1044610 1177645 := bbase (se 3 (by rfl) ⟨220808, by rfl⟩ : syracuseStep 1177645 = 441617) (by norm_num)
theorem B1570877 : Blo 1044610 1570877 := bbase (se 3 (by rfl) ⟨294539, by rfl⟩ : syracuseStep 1570877 = 589079) (by norm_num)
theorem B1341517 : Blo 1044610 1341517 := bbase (se 3 (by rfl) ⟨251534, by rfl⟩ : syracuseStep 1341517 = 503069) (by norm_num)
theorem B1177681 : Blo 1044610 1177681 := bbase (se 2 (by rfl) ⟨441630, by rfl⟩ : syracuseStep 1177681 = 883261) (by norm_num)
theorem B1570901 : Blo 1044610 1570901 := bbase (se 8 (by rfl) ⟨9204, by rfl⟩ : syracuseStep 1570901 = 18409) (by norm_num)
theorem B2357333 : Blo 1044610 2357333 := bbase (se 8 (by rfl) ⟨13812, by rfl⟩ : syracuseStep 2357333 = 27625) (by norm_num)
theorem B1570925 : Blo 1044610 1570925 := bbase (se 3 (by rfl) ⟨294548, by rfl⟩ : syracuseStep 1570925 = 589097) (by norm_num)
theorem B1177717 : Blo 1044610 1177717 := bbase (se 5 (by rfl) ⟨55205, by rfl⟩ : syracuseStep 1177717 = 110411) (by norm_num)
theorem B1767541 : Blo 1044610 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B1570949 : Blo 1044610 1570949 := bbase (se 4 (by rfl) ⟨147276, by rfl⟩ : syracuseStep 1570949 = 294553) (by norm_num)
theorem B1177753 : Blo 1044610 1177753 := bbase (se 2 (by rfl) ⟨441657, by rfl⟩ : syracuseStep 1177753 = 883315) (by norm_num)
theorem B1570973 : Blo 1044610 1570973 := bbase (se 3 (by rfl) ⟨294557, by rfl⟩ : syracuseStep 1570973 = 589115) (by norm_num)
theorem B2357405 : Blo 1044610 2357405 := bbase (se 3 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 2357405 = 884027) (by norm_num)
theorem B1570997 : Blo 1044610 1570997 := bbase (se 5 (by rfl) ⟨73640, by rfl⟩ : syracuseStep 1570997 = 147281) (by norm_num)
theorem B1177789 : Blo 1044610 1177789 := bbase (se 3 (by rfl) ⟨220835, by rfl⟩ : syracuseStep 1177789 = 441671) (by norm_num)
theorem B1571021 : Blo 1044610 1571021 := bbase (se 3 (by rfl) ⟨294566, by rfl⟩ : syracuseStep 1571021 = 589133) (by norm_num)
theorem B1767629 : Blo 1044610 1767629 := bbase (se 3 (by rfl) ⟨331430, by rfl⟩ : syracuseStep 1767629 = 662861) (by norm_num)
theorem B2652365 : Blo 1044610 2652365 := bbase (se 3 (by rfl) ⟨497318, by rfl⟩ : syracuseStep 2652365 = 994637) (by norm_num)
theorem B1177825 : Blo 1044610 1177825 := bbase (se 2 (by rfl) ⟨441684, by rfl⟩ : syracuseStep 1177825 = 883369) (by norm_num)
theorem B1571045 : Blo 1044610 1571045 := bbase (se 4 (by rfl) ⟨147285, by rfl⟩ : syracuseStep 1571045 = 294571) (by norm_num)
theorem B2357477 : Blo 1044610 2357477 := bbase (se 4 (by rfl) ⟨221013, by rfl⟩ : syracuseStep 2357477 = 442027) (by norm_num)
theorem B1571069 : Blo 1044610 1571069 := bbase (se 3 (by rfl) ⟨294575, by rfl⟩ : syracuseStep 1571069 = 589151) (by norm_num)
theorem B1177861 : Blo 1044610 1177861 := bbase (se 4 (by rfl) ⟨110424, by rfl⟩ : syracuseStep 1177861 = 220849) (by norm_num)
theorem B1571093 : Blo 1044610 1571093 := bbase (se 6 (by rfl) ⟨36822, by rfl⟩ : syracuseStep 1571093 = 73645) (by norm_num)
theorem B1177897 : Blo 1044610 1177897 := bbase (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) (by norm_num)
theorem B1571117 : Blo 1044610 1571117 := bbase (se 3 (by rfl) ⟨294584, by rfl⟩ : syracuseStep 1571117 = 589169) (by norm_num)
theorem B2357549 : Blo 1044610 2357549 := bbase (se 3 (by rfl) ⟨442040, by rfl⟩ : syracuseStep 2357549 = 884081) (by norm_num)
theorem B2390317 : Blo 1044610 2390317 := bbase (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) (by norm_num)
theorem B1571141 : Blo 1044610 1571141 := bbase (se 4 (by rfl) ⟨147294, by rfl⟩ : syracuseStep 1571141 = 294589) (by norm_num)
theorem B1177933 : Blo 1044610 1177933 := bbase (se 3 (by rfl) ⟨220862, by rfl⟩ : syracuseStep 1177933 = 441725) (by norm_num)
theorem B1767757 : Blo 1044610 1767757 := bbase (se 3 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 1767757 = 662909) (by norm_num)
theorem B1571165 : Blo 1044610 1571165 := bbase (se 3 (by rfl) ⟨294593, by rfl⟩ : syracuseStep 1571165 = 589187) (by norm_num)
theorem B1177969 : Blo 1044610 1177969 := bbase (se 2 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 1177969 = 883477) (by norm_num)
theorem B1571189 : Blo 1044610 1571189 := bbase (se 5 (by rfl) ⟨73649, by rfl⟩ : syracuseStep 1571189 = 147299) (by norm_num)
theorem B2357621 : Blo 1044610 2357621 := bbase (se 5 (by rfl) ⟨110513, by rfl⟩ : syracuseStep 2357621 = 221027) (by norm_num)
theorem B3537269 : Blo 1044610 3537269 := bbase (se 5 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 3537269 = 331619) (by norm_num)
theorem B1571213 : Blo 1044610 1571213 := bbase (se 3 (by rfl) ⟨294602, by rfl⟩ : syracuseStep 1571213 = 589205) (by norm_num)
theorem B1178005 : Blo 1044610 1178005 := bbase (se 6 (by rfl) ⟨27609, by rfl⟩ : syracuseStep 1178005 = 55219) (by norm_num)
theorem B1571237 : Blo 1044610 1571237 := bbase (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) (by norm_num)
theorem B1767845 : Blo 1044610 1767845 := bbase (se 4 (by rfl) ⟨165735, by rfl⟩ : syracuseStep 1767845 = 331471) (by norm_num)
theorem B1178041 : Blo 1044610 1178041 := bbase (se 2 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 1178041 = 883531) (by norm_num)
theorem B2357693 : Blo 1044610 2357693 := bbase (se 3 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 2357693 = 884135) (by norm_num)
theorem B1571261 : Blo 1044610 1571261 := bbase (se 3 (by rfl) ⟨294611, by rfl⟩ : syracuseStep 1571261 = 589223) (by norm_num)
theorem B1571285 : Blo 1044610 1571285 := bbase (se 7 (by rfl) ⟨18413, by rfl⟩ : syracuseStep 1571285 = 36827) (by norm_num)
theorem B1178077 : Blo 1044610 1178077 := bbase (se 3 (by rfl) ⟨220889, by rfl⟩ : syracuseStep 1178077 = 441779) (by norm_num)
theorem B1571309 : Blo 1044610 1571309 := bbase (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) (by norm_num)
theorem B1178113 : Blo 1044610 1178113 := bbase (se 2 (by rfl) ⟨441792, by rfl⟩ : syracuseStep 1178113 = 883585) (by norm_num)
theorem B1571333 : Blo 1044610 1571333 := bbase (se 4 (by rfl) ⟨147312, by rfl⟩ : syracuseStep 1571333 = 294625) (by norm_num)
theorem B2357765 : Blo 1044610 2357765 := bbase (se 4 (by rfl) ⟨221040, by rfl⟩ : syracuseStep 2357765 = 442081) (by norm_num)
theorem B1571357 : Blo 1044610 1571357 := bbase (se 3 (by rfl) ⟨294629, by rfl⟩ : syracuseStep 1571357 = 589259) (by norm_num)
theorem B1178149 : Blo 1044610 1178149 := bbase (se 4 (by rfl) ⟨110451, by rfl⟩ : syracuseStep 1178149 = 220903) (by norm_num)
theorem B1767973 : Blo 1044610 1767973 := bbase (se 4 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 1767973 = 331495) (by norm_num)
theorem B2652709 : Blo 1044610 2652709 := bbase (se 4 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 2652709 = 497383) (by norm_num)
theorem B1571381 : Blo 1044610 1571381 := bbase (se 5 (by rfl) ⟨73658, by rfl⟩ : syracuseStep 1571381 = 147317) (by norm_num)
theorem B1178185 : Blo 1044610 1178185 := bbase (se 2 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 1178185 = 883639) (by norm_num)
theorem B1571405 : Blo 1044610 1571405 := bbase (se 3 (by rfl) ⟨294638, by rfl⟩ : syracuseStep 1571405 = 589277) (by norm_num)
theorem B2357837 : Blo 1044610 2357837 := bbase (se 3 (by rfl) ⟨442094, by rfl⟩ : syracuseStep 2357837 = 884189) (by norm_num)
theorem B1571429 : Blo 1044610 1571429 := bbase (se 4 (by rfl) ⟨147321, by rfl⟩ : syracuseStep 1571429 = 294643) (by norm_num)
theorem B1178221 : Blo 1044610 1178221 := bbase (se 3 (by rfl) ⟨220916, by rfl⟩ : syracuseStep 1178221 = 441833) (by norm_num)
theorem B1571453 : Blo 1044610 1571453 := bbase (se 3 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 1571453 = 589295) (by norm_num)
theorem B1768061 : Blo 1044610 1768061 := bbase (se 3 (by rfl) ⟨331511, by rfl⟩ : syracuseStep 1768061 = 663023) (by norm_num)
theorem B1178257 : Blo 1044610 1178257 := bbase (se 2 (by rfl) ⟨441846, by rfl⟩ : syracuseStep 1178257 = 883693) (by norm_num)
theorem B1571477 : Blo 1044610 1571477 := bbase (se 6 (by rfl) ⟨36831, by rfl⟩ : syracuseStep 1571477 = 73663) (by norm_num)
theorem B2357909 : Blo 1044610 2357909 := bbase (se 6 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 2357909 = 110527) (by norm_num)
theorem B2652821 : Blo 1044610 2652821 := bbase (se 6 (by rfl) ⟨62175, by rfl⟩ : syracuseStep 2652821 = 124351) (by norm_num)
theorem B1571501 : Blo 1044610 1571501 := bbase (se 3 (by rfl) ⟨294656, by rfl⟩ : syracuseStep 1571501 = 589313) (by norm_num)
theorem B1178293 : Blo 1044610 1178293 := bbase (se 5 (by rfl) ⟨55232, by rfl⟩ : syracuseStep 1178293 = 110465) (by norm_num)
theorem B1571525 : Blo 1044610 1571525 := bbase (se 4 (by rfl) ⟨147330, by rfl⟩ : syracuseStep 1571525 = 294661) (by norm_num)
theorem B1178329 : Blo 1044610 1178329 := bbase (se 2 (by rfl) ⟨441873, by rfl⟩ : syracuseStep 1178329 = 883747) (by norm_num)
theorem B1571549 : Blo 1044610 1571549 := bbase (se 3 (by rfl) ⟨294665, by rfl⟩ : syracuseStep 1571549 = 589331) (by norm_num)
theorem B2357981 : Blo 1044610 2357981 := bbase (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) (by norm_num)
theorem B2980597 : Blo 1044610 2980597 := bbase (se 5 (by rfl) ⟨139715, by rfl⟩ : syracuseStep 2980597 = 279431) (by norm_num)
theorem B1571573 : Blo 1044610 1571573 := bbase (se 5 (by rfl) ⟨73667, by rfl⟩ : syracuseStep 1571573 = 147335) (by norm_num)
theorem B1178365 : Blo 1044610 1178365 := bbase (se 3 (by rfl) ⟨220943, by rfl⟩ : syracuseStep 1178365 = 441887) (by norm_num)
theorem B1768189 : Blo 1044610 1768189 := bbase (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) (by norm_num)
theorem B1571597 : Blo 1044610 1571597 := bbase (se 3 (by rfl) ⟨294674, by rfl⟩ : syracuseStep 1571597 = 589349) (by norm_num)
theorem B1178401 : Blo 1044610 1178401 := bbase (se 2 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 1178401 = 883801) (by norm_num)
theorem B1571621 : Blo 1044610 1571621 := bbase (se 4 (by rfl) ⟨147339, by rfl⟩ : syracuseStep 1571621 = 294679) (by norm_num)
theorem B2358053 : Blo 1044610 2358053 := bbase (se 4 (by rfl) ⟨221067, by rfl⟩ : syracuseStep 2358053 = 442135) (by norm_num)
theorem B3537701 : Blo 1044610 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B4782901 : Blo 1044610 4782901 := bbase (se 5 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 4782901 = 448397) (by norm_num)
theorem B1571645 : Blo 1044610 1571645 := bbase (se 3 (by rfl) ⟨294683, by rfl⟩ : syracuseStep 1571645 = 589367) (by norm_num)
theorem B1178437 : Blo 1044610 1178437 := bbase (se 4 (by rfl) ⟨110478, by rfl⟩ : syracuseStep 1178437 = 220957) (by norm_num)
theorem B1571669 : Blo 1044610 1571669 := bbase (se 9 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 1571669 = 9209) (by norm_num)
theorem B1768277 : Blo 1044610 1768277 := bbase (se 9 (by rfl) ⟨5180, by rfl⟩ : syracuseStep 1768277 = 10361) (by norm_num)
theorem B2653013 : Blo 1044610 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B1178473 : Blo 1044610 1178473 := bbase (se 2 (by rfl) ⟨441927, by rfl⟩ : syracuseStep 1178473 = 883855) (by norm_num)
theorem B1571693 : Blo 1044610 1571693 := bbase (se 3 (by rfl) ⟨294692, by rfl⟩ : syracuseStep 1571693 = 589385) (by norm_num)
theorem B2358125 : Blo 1044610 2358125 := bbase (se 3 (by rfl) ⟨442148, by rfl⟩ : syracuseStep 2358125 = 884297) (by norm_num)
theorem B1571717 : Blo 1044610 1571717 := bbase (se 4 (by rfl) ⟨147348, by rfl⟩ : syracuseStep 1571717 = 294697) (by norm_num)
theorem B1178509 : Blo 1044610 1178509 := bbase (se 3 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 1178509 = 441941) (by norm_num)
theorem B1571741 : Blo 1044610 1571741 := bbase (se 3 (by rfl) ⟨294701, by rfl⟩ : syracuseStep 1571741 = 589403) (by norm_num)
theorem B1178545 : Blo 1044610 1178545 := bbase (se 2 (by rfl) ⟨441954, by rfl⟩ : syracuseStep 1178545 = 883909) (by norm_num)
theorem B1571765 : Blo 1044610 1571765 := bbase (se 5 (by rfl) ⟨73676, by rfl⟩ : syracuseStep 1571765 = 147353) (by norm_num)
theorem B2358197 : Blo 1044610 2358197 := bbase (se 5 (by rfl) ⟨110540, by rfl⟩ : syracuseStep 2358197 = 221081) (by norm_num)
theorem B1571789 : Blo 1044610 1571789 := bbase (se 3 (by rfl) ⟨294710, by rfl⟩ : syracuseStep 1571789 = 589421) (by norm_num)
theorem B1178581 : Blo 1044610 1178581 := bbase (se 7 (by rfl) ⟨13811, by rfl⟩ : syracuseStep 1178581 = 27623) (by norm_num)
theorem B1768405 : Blo 1044610 1768405 := bbase (se 7 (by rfl) ⟨20723, by rfl⟩ : syracuseStep 1768405 = 41447) (by norm_num)
theorem B1571813 : Blo 1044610 1571813 := bbase (se 4 (by rfl) ⟨147357, by rfl⟩ : syracuseStep 1571813 = 294715) (by norm_num)
theorem B1178617 : Blo 1044610 1178617 := bbase (se 2 (by rfl) ⟨441981, by rfl⟩ : syracuseStep 1178617 = 883963) (by norm_num)
theorem B1571837 : Blo 1044610 1571837 := bbase (se 3 (by rfl) ⟨294719, by rfl⟩ : syracuseStep 1571837 = 589439) (by norm_num)
theorem B2358269 : Blo 1044610 2358269 := bbase (se 3 (by rfl) ⟨442175, by rfl⟩ : syracuseStep 2358269 = 884351) (by norm_num)
theorem B1571861 : Blo 1044610 1571861 := bbase (se 6 (by rfl) ⟨36840, by rfl⟩ : syracuseStep 1571861 = 73681) (by norm_num)
theorem B1178653 : Blo 1044610 1178653 := bbase (se 3 (by rfl) ⟨220997, by rfl⟩ : syracuseStep 1178653 = 441995) (by norm_num)
theorem B1571885 : Blo 1044610 1571885 := bbase (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) (by norm_num)
theorem B1768493 : Blo 1044610 1768493 := bbase (se 3 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 1768493 = 663185) (by norm_num)
theorem B1178689 : Blo 1044610 1178689 := bbase (se 2 (by rfl) ⟨442008, by rfl⟩ : syracuseStep 1178689 = 884017) (by norm_num)
theorem B1571909 : Blo 1044610 1571909 := bbase (se 4 (by rfl) ⟨147366, by rfl⟩ : syracuseStep 1571909 = 294733) (by norm_num)
theorem B2358341 : Blo 1044610 2358341 := bbase (se 4 (by rfl) ⟨221094, by rfl⟩ : syracuseStep 2358341 = 442189) (by norm_num)
theorem B1571933 : Blo 1044610 1571933 := bbase (se 3 (by rfl) ⟨294737, by rfl⟩ : syracuseStep 1571933 = 589475) (by norm_num)
theorem B1178725 : Blo 1044610 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B1571957 : Blo 1044610 1571957 := bbase (se 5 (by rfl) ⟨73685, by rfl⟩ : syracuseStep 1571957 = 147371) (by norm_num)
theorem B1178761 : Blo 1044610 1178761 := bbase (se 2 (by rfl) ⟨442035, by rfl⟩ : syracuseStep 1178761 = 884071) (by norm_num)
theorem B1571981 : Blo 1044610 1571981 := bbase (se 3 (by rfl) ⟨294746, by rfl⟩ : syracuseStep 1571981 = 589493) (by norm_num)
theorem B2358413 : Blo 1044610 2358413 := bbase (se 3 (by rfl) ⟨442202, by rfl⟩ : syracuseStep 2358413 = 884405) (by norm_num)
theorem B1572005 : Blo 1044610 1572005 := bbase (se 4 (by rfl) ⟨147375, by rfl⟩ : syracuseStep 1572005 = 294751) (by norm_num)
theorem B1178797 : Blo 1044610 1178797 := bbase (se 3 (by rfl) ⟨221024, by rfl⟩ : syracuseStep 1178797 = 442049) (by norm_num)
theorem B1768621 : Blo 1044610 1768621 := bbase (se 3 (by rfl) ⟨331616, by rfl⟩ : syracuseStep 1768621 = 663233) (by norm_num)
theorem B2653357 : Blo 1044610 2653357 := bbase (se 3 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 2653357 = 995009) (by norm_num)
theorem B1572029 : Blo 1044610 1572029 := bbase (se 3 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 1572029 = 589511) (by norm_num)
theorem B1178833 : Blo 1044610 1178833 := bbase (se 2 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 1178833 = 884125) (by norm_num)
theorem B1572053 : Blo 1044610 1572053 := bbase (se 7 (by rfl) ⟨18422, by rfl⟩ : syracuseStep 1572053 = 36845) (by norm_num)
theorem B2358485 : Blo 1044610 2358485 := bbase (se 7 (by rfl) ⟨27638, by rfl⟩ : syracuseStep 2358485 = 55277) (by norm_num)
theorem B3538133 : Blo 1044610 3538133 := bbase (se 7 (by rfl) ⟨41462, by rfl⟩ : syracuseStep 3538133 = 82925) (by norm_num)
theorem B5307605 : Blo 1044610 5307605 := bbase (se 7 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 5307605 = 124397) (by norm_num)
theorem B1572077 : Blo 1044610 1572077 := bbase (se 3 (by rfl) ⟨294764, by rfl⟩ : syracuseStep 1572077 = 589529) (by norm_num)
theorem B1178869 : Blo 1044610 1178869 := bbase (se 5 (by rfl) ⟨55259, by rfl⟩ : syracuseStep 1178869 = 110519) (by norm_num)
theorem B1572101 : Blo 1044610 1572101 := bbase (se 4 (by rfl) ⟨147384, by rfl⟩ : syracuseStep 1572101 = 294769) (by norm_num)
theorem B1768709 : Blo 1044610 1768709 := bbase (se 4 (by rfl) ⟨165816, by rfl⟩ : syracuseStep 1768709 = 331633) (by norm_num)
theorem B1178905 : Blo 1044610 1178905 := bbase (se 2 (by rfl) ⟨442089, by rfl⟩ : syracuseStep 1178905 = 884179) (by norm_num)
theorem B1572125 : Blo 1044610 1572125 := bbase (se 3 (by rfl) ⟨294773, by rfl⟩ : syracuseStep 1572125 = 589547) (by norm_num)
theorem B2358557 : Blo 1044610 2358557 := bbase (se 3 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 2358557 = 884459) (by norm_num)
theorem B2653469 : Blo 1044610 2653469 := bbase (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) (by norm_num)
theorem B2424109 : Blo 1044610 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B1572149 : Blo 1044610 1572149 := bbase (se 5 (by rfl) ⟨73694, by rfl⟩ : syracuseStep 1572149 = 147389) (by norm_num)
theorem B1178941 : Blo 1044610 1178941 := bbase (se 3 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 1178941 = 442103) (by norm_num)
theorem B1572173 : Blo 1044610 1572173 := bbase (se 3 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 1572173 = 589565) (by norm_num)
theorem B1178977 : Blo 1044610 1178977 := bbase (se 2 (by rfl) ⟨442116, by rfl⟩ : syracuseStep 1178977 = 884233) (by norm_num)
theorem B1572197 : Blo 1044610 1572197 := bbase (se 4 (by rfl) ⟨147393, by rfl⟩ : syracuseStep 1572197 = 294787) (by norm_num)
theorem B2358629 : Blo 1044610 2358629 := bbase (se 4 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 2358629 = 442243) (by norm_num)
theorem B1572221 : Blo 1044610 1572221 := bbase (se 3 (by rfl) ⟨294791, by rfl⟩ : syracuseStep 1572221 = 589583) (by norm_num)
theorem B1179013 : Blo 1044610 1179013 := bbase (se 4 (by rfl) ⟨110532, by rfl⟩ : syracuseStep 1179013 = 221065) (by norm_num)
theorem B1768837 : Blo 1044610 1768837 := bbase (se 4 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 1768837 = 331657) (by norm_num)
theorem B1572245 : Blo 1044610 1572245 := bbase (se 6 (by rfl) ⟨36849, by rfl⟩ : syracuseStep 1572245 = 73699) (by norm_num)
theorem B1179049 : Blo 1044610 1179049 := bbase (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) (by norm_num)
theorem B1572269 : Blo 1044610 1572269 := bbase (se 3 (by rfl) ⟨294800, by rfl⟩ : syracuseStep 1572269 = 589601) (by norm_num)
theorem B2358701 : Blo 1044610 2358701 := bbase (se 3 (by rfl) ⟨442256, by rfl⟩ : syracuseStep 2358701 = 884513) (by norm_num)
theorem B1572293 : Blo 1044610 1572293 := bbase (se 4 (by rfl) ⟨147402, by rfl⟩ : syracuseStep 1572293 = 294805) (by norm_num)
theorem B1179085 : Blo 1044610 1179085 := bbase (se 3 (by rfl) ⟨221078, by rfl⟩ : syracuseStep 1179085 = 442157) (by norm_num)
theorem B1572317 : Blo 1044610 1572317 := bbase (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) (by norm_num)
theorem B1768925 : Blo 1044610 1768925 := bbase (se 3 (by rfl) ⟨331673, by rfl⟩ : syracuseStep 1768925 = 663347) (by norm_num)
theorem B2653661 : Blo 1044610 2653661 := bbase (se 3 (by rfl) ⟨497561, by rfl⟩ : syracuseStep 2653661 = 995123) (by norm_num)
theorem B1179121 : Blo 1044610 1179121 := bbase (se 2 (by rfl) ⟨442170, by rfl⟩ : syracuseStep 1179121 = 884341) (by norm_num)
theorem B1572341 : Blo 1044610 1572341 := bbase (se 5 (by rfl) ⟨73703, by rfl⟩ : syracuseStep 1572341 = 147407) (by norm_num)
theorem B2358773 : Blo 1044610 2358773 := bbase (se 5 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 2358773 = 221135) (by norm_num)
theorem B1572365 : Blo 1044610 1572365 := bbase (se 3 (by rfl) ⟨294818, by rfl⟩ : syracuseStep 1572365 = 589637) (by norm_num)
theorem B1179157 : Blo 1044610 1179157 := bbase (se 6 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 1179157 = 55273) (by norm_num)
theorem B1572389 : Blo 1044610 1572389 := bbase (se 4 (by rfl) ⟨147411, by rfl⟩ : syracuseStep 1572389 = 294823) (by norm_num)
theorem B1179193 : Blo 1044610 1179193 := bbase (se 2 (by rfl) ⟨442197, by rfl⟩ : syracuseStep 1179193 = 884395) (by norm_num)
theorem B1572413 : Blo 1044610 1572413 := bbase (se 3 (by rfl) ⟨294827, by rfl⟩ : syracuseStep 1572413 = 589655) (by norm_num)
theorem B2358845 : Blo 1044610 2358845 := bbase (se 3 (by rfl) ⟨442283, by rfl⟩ : syracuseStep 2358845 = 884567) (by norm_num)
theorem B1572437 : Blo 1044610 1572437 := bbase (se 8 (by rfl) ⟨9213, by rfl⟩ : syracuseStep 1572437 = 18427) (by norm_num)
theorem B1179229 : Blo 1044610 1179229 := bbase (se 3 (by rfl) ⟨221105, by rfl⟩ : syracuseStep 1179229 = 442211) (by norm_num)
theorem B1769053 : Blo 1044610 1769053 := bbase (se 3 (by rfl) ⟨331697, by rfl⟩ : syracuseStep 1769053 = 663395) (by norm_num)
theorem B1572461 : Blo 1044610 1572461 := bbase (se 3 (by rfl) ⟨294836, by rfl⟩ : syracuseStep 1572461 = 589673) (by norm_num)
theorem B5963381 : Blo 1044610 5963381 := bbase (se 5 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 5963381 = 559067) (by norm_num)
theorem B1179265 : Blo 1044610 1179265 := bbase (se 2 (by rfl) ⟨442224, by rfl⟩ : syracuseStep 1179265 = 884449) (by norm_num)
theorem B1572485 : Blo 1044610 1572485 := bbase (se 4 (by rfl) ⟨147420, by rfl⟩ : syracuseStep 1572485 = 294841) (by norm_num)
theorem B2358917 : Blo 1044610 2358917 := bbase (se 4 (by rfl) ⟨221148, by rfl⟩ : syracuseStep 2358917 = 442297) (by norm_num)
theorem B3538565 : Blo 1044610 3538565 := bbase (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) (by norm_num)
theorem B1572509 : Blo 1044610 1572509 := bbase (se 3 (by rfl) ⟨294845, by rfl⟩ : syracuseStep 1572509 = 589691) (by norm_num)
theorem B1179301 : Blo 1044610 1179301 := bbase (se 4 (by rfl) ⟨110559, by rfl⟩ : syracuseStep 1179301 = 221119) (by norm_num)
theorem B1572533 : Blo 1044610 1572533 := bbase (se 5 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 1572533 = 147425) (by norm_num)
theorem B1769141 : Blo 1044610 1769141 := bbase (se 5 (by rfl) ⟨82928, by rfl⟩ : syracuseStep 1769141 = 165857) (by norm_num)
theorem B1179337 : Blo 1044610 1179337 := bbase (se 2 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 1179337 = 884503) (by norm_num)
theorem B1572557 : Blo 1044610 1572557 := bbase (se 3 (by rfl) ⟨294854, by rfl⟩ : syracuseStep 1572557 = 589709) (by norm_num)
theorem B2358989 : Blo 1044610 2358989 := bbase (se 3 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 2358989 = 884621) (by norm_num)
theorem B1572581 : Blo 1044610 1572581 := bbase (se 4 (by rfl) ⟨147429, by rfl⟩ : syracuseStep 1572581 = 294859) (by norm_num)
theorem B1179373 : Blo 1044610 1179373 := bbase (se 3 (by rfl) ⟨221132, by rfl⟩ : syracuseStep 1179373 = 442265) (by norm_num)
theorem B1572605 : Blo 1044610 1572605 := bbase (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) (by norm_num)
theorem B1179409 : Blo 1044610 1179409 := bbase (se 2 (by rfl) ⟨442278, by rfl⟩ : syracuseStep 1179409 = 884557) (by norm_num)
theorem B1572629 : Blo 1044610 1572629 := bbase (se 6 (by rfl) ⟨36858, by rfl⟩ : syracuseStep 1572629 = 73717) (by norm_num)
theorem B2359061 : Blo 1044610 2359061 := bbase (se 6 (by rfl) ⟨55290, by rfl⟩ : syracuseStep 2359061 = 110581) (by norm_num)
theorem B1572653 : Blo 1044610 1572653 := bbase (se 3 (by rfl) ⟨294872, by rfl⟩ : syracuseStep 1572653 = 589745) (by norm_num)
theorem B1179445 : Blo 1044610 1179445 := bbase (se 5 (by rfl) ⟨55286, by rfl⟩ : syracuseStep 1179445 = 110573) (by norm_num)
theorem B1769269 : Blo 1044610 1769269 := bbase (se 5 (by rfl) ⟨82934, by rfl⟩ : syracuseStep 1769269 = 165869) (by norm_num)
theorem B2654005 : Blo 1044610 2654005 := bbase (se 5 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 2654005 = 248813) (by norm_num)
theorem B2981701 : Blo 1044610 2981701 := bbase (se 4 (by rfl) ⟨279534, by rfl⟩ : syracuseStep 2981701 = 559069) (by norm_num)
theorem B1572677 : Blo 1044610 1572677 := bbase (se 4 (by rfl) ⟨147438, by rfl⟩ : syracuseStep 1572677 = 294877) (by norm_num)
theorem B1179481 : Blo 1044610 1179481 := bbase (se 2 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 1179481 = 884611) (by norm_num)
theorem B1572701 : Blo 1044610 1572701 := bbase (se 3 (by rfl) ⟨294881, by rfl⟩ : syracuseStep 1572701 = 589763) (by norm_num)
theorem B2359133 : Blo 1044610 2359133 := bbase (se 3 (by rfl) ⟨442337, by rfl⟩ : syracuseStep 2359133 = 884675) (by norm_num)
theorem B1572725 : Blo 1044610 1572725 := bbase (se 5 (by rfl) ⟨73721, by rfl⟩ : syracuseStep 1572725 = 147443) (by norm_num)
theorem B1179517 : Blo 1044610 1179517 := bbase (se 3 (by rfl) ⟨221159, by rfl⟩ : syracuseStep 1179517 = 442319) (by norm_num)
theorem B1572749 : Blo 1044610 1572749 := bbase (se 3 (by rfl) ⟨294890, by rfl⟩ : syracuseStep 1572749 = 589781) (by norm_num)
theorem B1769357 : Blo 1044610 1769357 := bbase (se 3 (by rfl) ⟨331754, by rfl⟩ : syracuseStep 1769357 = 663509) (by norm_num)
theorem B1179553 : Blo 1044610 1179553 := bbase (se 2 (by rfl) ⟨442332, by rfl⟩ : syracuseStep 1179553 = 884665) (by norm_num)
theorem B1572773 : Blo 1044610 1572773 := bbase (se 4 (by rfl) ⟨147447, by rfl⟩ : syracuseStep 1572773 = 294895) (by norm_num)
theorem B2359205 : Blo 1044610 2359205 := bbase (se 4 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 2359205 = 442351) (by norm_num)
theorem B2654117 : Blo 1044610 2654117 := bbase (se 4 (by rfl) ⟨248823, by rfl⟩ : syracuseStep 2654117 = 497647) (by norm_num)
theorem B1343405 : Blo 1044610 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B1572797 : Blo 1044610 1572797 := bbase (se 3 (by rfl) ⟨294899, by rfl⟩ : syracuseStep 1572797 = 589799) (by norm_num)
theorem B1179589 : Blo 1044610 1179589 := bbase (se 4 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 1179589 = 221173) (by norm_num)
theorem B1572821 : Blo 1044610 1572821 := bbase (se 7 (by rfl) ⟨18431, by rfl⟩ : syracuseStep 1572821 = 36863) (by norm_num)
theorem B1179625 : Blo 1044610 1179625 := bbase (se 2 (by rfl) ⟨442359, by rfl⟩ : syracuseStep 1179625 = 884719) (by norm_num)
theorem B1572845 : Blo 1044610 1572845 := bbase (se 3 (by rfl) ⟨294908, by rfl⟩ : syracuseStep 1572845 = 589817) (by norm_num)
theorem B2359277 : Blo 1044610 2359277 := bbase (se 3 (by rfl) ⟨442364, by rfl⟩ : syracuseStep 2359277 = 884729) (by norm_num)
theorem B1048579 : Blo 1044610 1048579 := bstep (se 1 (by rfl) ⟨786434, by rfl⟩ : syracuseStep 1048579 = 1572869) B1572869
theorem B2359313 : Blo 1044610 2359313 := bstep (se 2 (by rfl) ⟨884742, by rfl⟩ : syracuseStep 2359313 = 1769485) B1769485
theorem B1572881 : Blo 1044610 1572881 := bstep (se 2 (by rfl) ⟨589830, by rfl⟩ : syracuseStep 1572881 = 1179661) B1179661
theorem B1048595 : Blo 1044610 1048595 := bstep (se 1 (by rfl) ⟨786446, by rfl⟩ : syracuseStep 1048595 = 1572893) B1572893
theorem B2359331 : Blo 1044610 2359331 := bstep (se 1 (by rfl) ⟨1769498, by rfl⟩ : syracuseStep 2359331 = 3538997) B3538997
theorem B1572899 : Blo 1044610 1572899 := bstep (se 1 (by rfl) ⟨1179674, by rfl⟩ : syracuseStep 1572899 = 2359349) B2359349
theorem B7536881 : Blo 1044610 7536881 := bstep (se 2 (by rfl) ⟨2826330, by rfl⟩ : syracuseStep 7536881 = 5652661) B5652661
theorem B1507681 : Blo 1044610 1507681 := bstep (se 2 (by rfl) ⟨565380, by rfl⟩ : syracuseStep 1507681 = 1130761) B1130761
theorem B5964131 : Blo 1044610 5964131 := bstep (se 1 (by rfl) ⟨4473098, by rfl⟩ : syracuseStep 5964131 = 8946197) B8946197
theorem B3310093 : Blo 1044610 3310093 := bstep (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) B1241285
theorem B2982545 : Blo 1044610 2982545 := bstep (se 2 (by rfl) ⟨1118454, by rfl⟩ : syracuseStep 2982545 = 2236909) B2236909
theorem B5047075 : Blo 1044610 5047075 := bstep (se 1 (by rfl) ⟨3785306, by rfl⟩ : syracuseStep 5047075 = 7570613) B7570613
theorem B11305925 : Blo 1044610 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B3179587 : Blo 1044610 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B7537805 : Blo 1044610 7537805 := bstep (se 3 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 7537805 = 2826677) B2826677
theorem B13600099 : Blo 1044610 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B13763953 : Blo 1044610 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B2983331 : Blo 1044610 2983331 := bstep (se 1 (by rfl) ⟨2237498, by rfl⟩ : syracuseStep 2983331 = 4474997) B4474997
theorem B12748357 : Blo 1044610 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B3966641 : Blo 1044610 3966641 := bstep (se 2 (by rfl) ⟨1487490, by rfl⟩ : syracuseStep 3966641 = 2974981) B2974981
theorem B2983661 : Blo 1044610 2983661 := bstep (se 3 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 2983661 = 1118873) B1118873
theorem B3180305 : Blo 1044610 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B2983729 : Blo 1044610 2983729 := bstep (se 2 (by rfl) ⟨1118898, by rfl⟩ : syracuseStep 2983729 = 2237797) B2237797
theorem B3180401 : Blo 1044610 3180401 := bstep (se 2 (by rfl) ⟨1192650, by rfl⟩ : syracuseStep 3180401 = 2385301) B2385301
theorem B2984003 : Blo 1044610 2984003 := bstep (se 1 (by rfl) ⟨2238002, by rfl⟩ : syracuseStep 2984003 = 4476005) B4476005
theorem B1673363 : Blo 1044610 1673363 := bstep (se 1 (by rfl) ⟨1255022, by rfl⟩ : syracuseStep 1673363 = 2510045) B2510045
theorem B125634773 : Blo 1044610 125634773 := bstep (se 7 (by rfl) ⟨1472282, by rfl⟩ : syracuseStep 125634773 = 2944565) B2944565
theorem B1509715 : Blo 1044610 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B1116515 : Blo 1044610 1116515 := bstep (se 1 (by rfl) ⟨837386, by rfl⟩ : syracuseStep 1116515 = 1674773) B1674773
theorem B1510003 : Blo 1044610 1510003 := bstep (se 1 (by rfl) ⟨1132502, by rfl⟩ : syracuseStep 1510003 = 2265005) B2265005
theorem B1673921 : Blo 1044610 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B2755313 : Blo 1044610 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2984845 : Blo 1044610 2984845 := bstep (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) B1119317
theorem B2231185 : Blo 1044610 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B1411987 : Blo 1044610 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B1674145 : Blo 1044610 1674145 := bstep (se 2 (by rfl) ⟨627804, by rfl⟩ : syracuseStep 1674145 = 1255609) B1255609
theorem B1674209 : Blo 1044610 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B2985005 : Blo 1044610 2985005 := bstep (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) B1119377
theorem B1674337 : Blo 1044610 1674337 := bstep (se 2 (by rfl) ⟨627876, by rfl⟩ : syracuseStep 1674337 = 1255753) B1255753
theorem B3968099 : Blo 1044610 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2985187 : Blo 1044610 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B1117523 : Blo 1044610 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B9080419 : Blo 1044610 9080419 := bstep (se 1 (by rfl) ⟨6810314, by rfl⟩ : syracuseStep 9080419 = 13620629) B13620629
theorem B3575789 : Blo 1044610 3575789 := bstep (se 3 (by rfl) ⟨670460, by rfl⟩ : syracuseStep 3575789 = 1340921) B1340921
theorem B6131717 : Blo 1044610 6131717 := bstep (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) B1149697
theorem B3575843 : Blo 1044610 3575843 := bstep (se 1 (by rfl) ⟨2681882, by rfl⟩ : syracuseStep 3575843 = 5363765) B5363765
theorem B3969101 : Blo 1044610 3969101 := bstep (se 3 (by rfl) ⟨744206, by rfl⟩ : syracuseStep 3969101 = 1488413) B1488413
theorem B18157709 : Blo 1044610 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B3346829 : Blo 1044610 3346829 := bstep (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) B1255061
theorem B7934435 : Blo 1044610 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B3183149 : Blo 1044610 3183149 := bstep (se 3 (by rfl) ⟨596840, by rfl⟩ : syracuseStep 3183149 = 1193681) B1193681
theorem B3347021 : Blo 1044610 3347021 := bstep (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) B1255133
theorem B3576611 : Blo 1044610 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B15078257 : Blo 1044610 15078257 := bstep (se 2 (by rfl) ⟨5654346, by rfl⟩ : syracuseStep 15078257 = 11308693) B11308693
theorem B1119091 : Blo 1044610 1119091 := bstep (se 1 (by rfl) ⟨839318, by rfl⟩ : syracuseStep 1119091 = 1678637) B1678637
theorem B1610849 : Blo 1044610 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B1676387 : Blo 1044610 1676387 := bstep (se 1 (by rfl) ⟨1257290, by rfl⟩ : syracuseStep 1676387 = 2514581) B2514581
theorem B1119539 : Blo 1044610 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B3020561 : Blo 1044610 3020561 := bstep (se 2 (by rfl) ⟨1132710, by rfl⟩ : syracuseStep 3020561 = 2265421) B2265421
theorem B2266961 : Blo 1044610 2266961 := bstep (se 2 (by rfl) ⟨850110, by rfl⟩ : syracuseStep 2266961 = 1700221) B1700221
theorem B2234243 : Blo 1044610 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B1677233 : Blo 1044610 1677233 := bstep (se 2 (by rfl) ⟨628962, by rfl⟩ : syracuseStep 1677233 = 1257925) B1257925
theorem B2267057 : Blo 1044610 2267057 := bstep (se 2 (by rfl) ⟨850146, by rfl⟩ : syracuseStep 2267057 = 1700293) B1700293
theorem B3971213 : Blo 1044610 3971213 := bstep (se 3 (by rfl) ⟨744602, by rfl⟩ : syracuseStep 3971213 = 1489205) B1489205
theorem B1415425 : Blo 1044610 1415425 := bstep (se 2 (by rfl) ⟨530784, by rfl⟩ : syracuseStep 1415425 = 1061569) B1061569
theorem B4462883 : Blo 1044610 4462883 := bstep (se 1 (by rfl) ⟨3347162, by rfl⟩ : syracuseStep 4462883 = 6694325) B6694325
theorem B3774755 : Blo 1044610 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B3348803 : Blo 1044610 3348803 := bstep (se 1 (by rfl) ⟨2511602, by rfl⟩ : syracuseStep 3348803 = 5023205) B5023205
theorem B2824579 : Blo 1044610 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B13408739 : Blo 1044610 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B2824753 : Blo 1044610 2824753 := bstep (se 2 (by rfl) ⟨1059282, by rfl⟩ : syracuseStep 2824753 = 2118565) B2118565
theorem B13802083 : Blo 1044610 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B1677971 : Blo 1044610 1677971 := bstep (se 1 (by rfl) ⟨1258478, by rfl⟩ : syracuseStep 1677971 = 2516957) B2516957
theorem B2235107 : Blo 1044610 2235107 := bstep (se 1 (by rfl) ⟨1676330, by rfl⟩ : syracuseStep 2235107 = 3352661) B3352661
theorem B2235217 : Blo 1044610 2235217 := bstep (se 2 (by rfl) ⟨838206, by rfl⟩ : syracuseStep 2235217 = 1676413) B1676413
theorem B3972017 : Blo 1044610 3972017 := bstep (se 2 (by rfl) ⟨1489506, by rfl⟩ : syracuseStep 3972017 = 2979013) B2979013
theorem B2825293 : Blo 1044610 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B11312497 : Blo 1044610 11312497 := bstep (se 2 (by rfl) ⟨4242186, by rfl⟩ : syracuseStep 11312497 = 8484373) B8484373
theorem B3775907 : Blo 1044610 3775907 := bstep (se 1 (by rfl) ⟨2831930, by rfl⟩ : syracuseStep 3775907 = 5663861) B5663861
theorem B5807537 : Blo 1044610 5807537 := bstep (se 2 (by rfl) ⟨2177826, by rfl⟩ : syracuseStep 5807537 = 4355653) B4355653
theorem B3972685 : Blo 1044610 3972685 := bstep (se 3 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 3972685 = 1489757) B1489757
theorem B1678963 : Blo 1044610 1678963 := bstep (se 1 (by rfl) ⟨1259222, by rfl⟩ : syracuseStep 1678963 = 2518445) B2518445
theorem B1679201 : Blo 1044610 1679201 := bstep (se 2 (by rfl) ⟨629700, by rfl⟩ : syracuseStep 1679201 = 1259401) B1259401
theorem B5742541 : Blo 1044610 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1679411 : Blo 1044610 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B2826353 : Blo 1044610 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B3973475 : Blo 1044610 3973475 := bstep (se 1 (by rfl) ⟨2980106, by rfl⟩ : syracuseStep 3973475 = 5960213) B5960213
theorem B3350929 : Blo 1044610 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B2237233 : Blo 1044610 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B3023725 : Blo 1044610 3023725 := bstep (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) B1133897
theorem B3974129 : Blo 1044610 3974129 := bstep (se 2 (by rfl) ⟨1490298, by rfl⟩ : syracuseStep 3974129 = 2980597) B2980597
theorem B17409077 : Blo 1044610 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B2237635 : Blo 1044610 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B7939781 : Blo 1044610 7939781 := bstep (se 4 (by rfl) ⟨744354, by rfl⟩ : syracuseStep 7939781 = 1488709) B1488709
theorem B4466573 : Blo 1044610 4466573 := bstep (se 3 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 4466573 = 1674965) B1674965
theorem B2828429 : Blo 1044610 2828429 := bstep (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) B1060661
theorem B3352877 : Blo 1044610 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B3975587 : Blo 1044610 3975587 := bstep (se 1 (by rfl) ⟨2981690, by rfl⟩ : syracuseStep 3975587 = 5963381) B5963381
theorem B3353005 : Blo 1044610 3353005 := bstep (se 3 (by rfl) ⟨628688, by rfl⟩ : syracuseStep 3353005 = 1257377) B1257377
theorem B3975601 : Blo 1044610 3975601 := bstep (se 2 (by rfl) ⟨1490850, by rfl⟩ : syracuseStep 3975601 = 2981701) B2981701
theorem B3582413 : Blo 1044610 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B1059379 : Blo 1044610 1059379 := bstep (se 1 (by rfl) ⟨794534, by rfl⟩ : syracuseStep 1059379 = 1589069) B1589069
theorem B2239139 : Blo 1044610 2239139 := bstep (se 1 (by rfl) ⟨1679354, by rfl⟩ : syracuseStep 2239139 = 3358709) B3358709
theorem B2763491 : Blo 1044610 2763491 := bstep (se 1 (by rfl) ⟨2072618, by rfl⟩ : syracuseStep 2763491 = 4145237) B4145237
theorem B36285205 : Blo 1044610 36285205 := bstep (se 6 (by rfl) ⟨850434, by rfl⟩ : syracuseStep 36285205 = 1700869) B1700869
theorem B3582947 : Blo 1044610 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B1256483 : Blo 1044610 1256483 := bstep (se 1 (by rfl) ⟨942362, by rfl⟩ : syracuseStep 1256483 = 1884725) B1884725
theorem B8629517 : Blo 1044610 8629517 := bstep (se 3 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 8629517 = 3236069) B3236069
theorem B1322563 : Blo 1044610 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B2010737 : Blo 1044610 2010737 := bstep (se 2 (by rfl) ⟨754026, by rfl⟩ : syracuseStep 2010737 = 1508053) B1508053
theorem B1060499 : Blo 1044610 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1322659 : Blo 1044610 1322659 := bstep (se 1 (by rfl) ⟨991994, by rfl⟩ : syracuseStep 1322659 = 1983989) B1983989
theorem B2830115 : Blo 1044610 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B3977059 : Blo 1044610 3977059 := bstep (se 1 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 3977059 = 5965589) B5965589
theorem B1323155 : Blo 1044610 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B3354851 : Blo 1044610 3354851 := bstep (se 1 (by rfl) ⟨2516138, by rfl⟩ : syracuseStep 3354851 = 5032277) B5032277
theorem B3354979 : Blo 1044610 3354979 := bstep (se 1 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 3354979 = 5032469) B5032469
theorem B3355121 : Blo 1044610 3355121 := bstep (se 2 (by rfl) ⟨1258170, by rfl⟩ : syracuseStep 3355121 = 2516341) B2516341
theorem B3355235 : Blo 1044610 3355235 := bstep (se 1 (by rfl) ⟨2516426, by rfl⟩ : syracuseStep 3355235 = 5032853) B5032853
theorem B4239985 : Blo 1044610 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B10039949 : Blo 1044610 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B1323859 : Blo 1044610 1323859 := bstep (se 1 (by rfl) ⟨992894, by rfl⟩ : syracuseStep 1323859 = 1985789) B1985789
theorem B1487747 : Blo 1044610 1487747 := bstep (se 1 (by rfl) ⟨1115810, by rfl⟩ : syracuseStep 1487747 = 2231621) B2231621
theorem B5649329 : Blo 1044610 5649329 := bstep (se 2 (by rfl) ⟨2118498, by rfl⟩ : syracuseStep 5649329 = 4236997) B4236997
theorem B4469681 : Blo 1044610 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B1323955 : Blo 1044610 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B5289137 : Blo 1044610 5289137 := bstep (se 2 (by rfl) ⟨1983426, by rfl⟩ : syracuseStep 5289137 = 3966853) B3966853
theorem B1324451 : Blo 1044610 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B1488385 : Blo 1044610 1488385 := bstep (se 2 (by rfl) ⟨558144, by rfl⟩ : syracuseStep 1488385 = 1116289) B1116289
theorem B1259059 : Blo 1044610 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B4470349 : Blo 1044610 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B2832017 : Blo 1044610 2832017 := bstep (se 2 (by rfl) ⟨1062006, by rfl⟩ : syracuseStep 2832017 = 2124013) B2124013
theorem B1259155 : Blo 1044610 1259155 := bstep (se 1 (by rfl) ⟨944366, by rfl⟩ : syracuseStep 1259155 = 1888733) B1888733
theorem B1488721 : Blo 1044610 1488721 := bstep (se 2 (by rfl) ⟨558270, by rfl⟩ : syracuseStep 1488721 = 1116541) B1116541
theorem B3979277 : Blo 1044610 3979277 := bstep (se 3 (by rfl) ⟨746114, by rfl⟩ : syracuseStep 3979277 = 1492229) B1492229
theorem B1325155 : Blo 1044610 1325155 := bstep (se 1 (by rfl) ⟨993866, by rfl⟩ : syracuseStep 1325155 = 1987733) B1987733
theorem B4470947 : Blo 1044610 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B1325251 : Blo 1044610 1325251 := bstep (se 1 (by rfl) ⟨993938, by rfl⟩ : syracuseStep 1325251 = 1987877) B1987877
theorem B3356977 : Blo 1044610 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B1489313 : Blo 1044610 1489313 := bstep (se 2 (by rfl) ⟨558492, by rfl⟩ : syracuseStep 1489313 = 1116985) B1116985
theorem B7158257 : Blo 1044610 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B5290595 : Blo 1044610 5290595 := bstep (se 1 (by rfl) ⟨3967946, by rfl⟩ : syracuseStep 5290595 = 7935893) B7935893
theorem B1325747 : Blo 1044610 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B15088355 : Blo 1044610 15088355 := bstep (se 1 (by rfl) ⟨11316266, by rfl⟩ : syracuseStep 15088355 = 22632533) B22632533
theorem B1489843 : Blo 1044610 1489843 := bstep (se 1 (by rfl) ⟨1117382, by rfl⟩ : syracuseStep 1489843 = 2234765) B2234765
theorem B21445859 : Blo 1044610 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B1490179 : Blo 1044610 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B1326451 : Blo 1044610 1326451 := bstep (se 1 (by rfl) ⟨994838, by rfl⟩ : syracuseStep 1326451 = 1989677) B1989677
theorem B6700421 : Blo 1044610 6700421 := bstep (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) B1256329
theorem B5291405 : Blo 1044610 5291405 := bstep (se 3 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 5291405 = 1984277) B1984277
theorem B7945613 : Blo 1044610 7945613 := bstep (se 3 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 7945613 = 2979605) B2979605
theorem B3358093 : Blo 1044610 3358093 := bstep (se 3 (by rfl) ⟨629642, by rfl⟩ : syracuseStep 3358093 = 1259285) B1259285
theorem B1326547 : Blo 1044610 1326547 := bstep (se 1 (by rfl) ⟨994910, by rfl⟩ : syracuseStep 1326547 = 1989821) B1989821
theorem B1490737 : Blo 1044610 1490737 := bstep (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) B1118053
theorem B1490771 : Blo 1044610 1490771 := bstep (se 1 (by rfl) ⟨1118078, by rfl⟩ : syracuseStep 1490771 = 2236157) B2236157
theorem B1327043 : Blo 1044610 1327043 := bstep (se 1 (by rfl) ⟨995282, by rfl⟩ : syracuseStep 1327043 = 1990565) B1990565
theorem B101761109 : Blo 1044610 101761109 := bstep (se 8 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 101761109 = 1192513) B1192513
theorem B3358925 : Blo 1044610 3358925 := bstep (se 3 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 3358925 = 1259597) B1259597
theorem B5030221 : Blo 1044610 5030221 := bstep (se 3 (by rfl) ⟨943166, by rfl⟩ : syracuseStep 5030221 = 1886333) B1886333
theorem B1491329 : Blo 1044610 1491329 := bstep (se 2 (by rfl) ⟨559248, by rfl⟩ : syracuseStep 1491329 = 1118497) B1118497
theorem B1491409 : Blo 1044610 1491409 := bstep (se 2 (by rfl) ⟨559278, by rfl⟩ : syracuseStep 1491409 = 1118557) B1118557
theorem B8929763 : Blo 1044610 8929763 := bstep (se 1 (by rfl) ⟨6697322, by rfl⟩ : syracuseStep 8929763 = 13394645) B13394645
theorem B4538915 : Blo 1044610 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B2146979 : Blo 1044610 2146979 := bstep (se 1 (by rfl) ⟨1610234, by rfl⟩ : syracuseStep 2146979 = 3220469) B3220469
theorem B7553891 : Blo 1044610 7553891 := bstep (se 1 (by rfl) ⟨5665418, by rfl⟩ : syracuseStep 7553891 = 11330837) B11330837
theorem B10339397 : Blo 1044610 10339397 := bstep (se 4 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 10339397 = 1938637) B1938637
theorem B4244557 : Blo 1044610 4244557 := bstep (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) B1591709
theorem B1492195 : Blo 1044610 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B5653745 : Blo 1044610 5653745 := bstep (se 2 (by rfl) ⟨2120154, by rfl⟩ : syracuseStep 5653745 = 4240309) B4240309
theorem B1983761 : Blo 1044610 1983761 := bstep (se 2 (by rfl) ⟨743910, by rfl⟩ : syracuseStep 1983761 = 1487821) B1487821
theorem B6702371 : Blo 1044610 6702371 := bstep (se 1 (by rfl) ⟨5026778, by rfl⟩ : syracuseStep 6702371 = 10053557) B10053557
theorem B4244899 : Blo 1044610 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B1885763 : Blo 1044610 1885763 := bstep (se 1 (by rfl) ⟨1414322, by rfl⟩ : syracuseStep 1885763 = 2828645) B2828645
theorem B1492673 : Blo 1044610 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1492787 : Blo 1044610 1492787 := bstep (se 1 (by rfl) ⟨1119590, by rfl⟩ : syracuseStep 1492787 = 2239181) B2239181
theorem B4474723 : Blo 1044610 4474723 := bstep (se 1 (by rfl) ⟨3356042, by rfl⟩ : syracuseStep 4474723 = 6712085) B6712085
theorem B8046449 : Blo 1044610 8046449 := bstep (se 2 (by rfl) ⟨3017418, by rfl⟩ : syracuseStep 8046449 = 6034837) B6034837
theorem B1492867 : Blo 1044610 1492867 := bstep (se 1 (by rfl) ⟨1119650, by rfl⟩ : syracuseStep 1492867 = 2239301) B2239301
theorem B1886339 : Blo 1044610 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B1984657 : Blo 1044610 1984657 := bstep (se 2 (by rfl) ⟨744246, by rfl⟩ : syracuseStep 1984657 = 1488493) B1488493
theorem B5294321 : Blo 1044610 5294321 := bstep (se 2 (by rfl) ⟨1985370, by rfl⟩ : syracuseStep 5294321 = 3970741) B3970741
theorem B7948529 : Blo 1044610 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B1984817 : Blo 1044610 1984817 := bstep (se 2 (by rfl) ⟨744306, by rfl⟩ : syracuseStep 1984817 = 1488613) B1488613
theorem B1591697 : Blo 1044610 1591697 := bstep (se 2 (by rfl) ⟨596886, by rfl⟩ : syracuseStep 1591697 = 1193773) B1193773
theorem B1985219 : Blo 1044610 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B1788689 : Blo 1044610 1788689 := bstep (se 2 (by rfl) ⟨670758, by rfl⟩ : syracuseStep 1788689 = 1341517) B1341517
theorem B5655557 : Blo 1044610 5655557 := bstep (se 4 (by rfl) ⟨530208, by rfl⟩ : syracuseStep 5655557 = 1060417) B1060417
theorem B3525713 : Blo 1044610 3525713 := bstep (se 2 (by rfl) ⟨1322142, by rfl⟩ : syracuseStep 3525713 = 2644285) B2644285
theorem B5950691 : Blo 1044610 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B9063821 : Blo 1044610 9063821 := bstep (se 3 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 9063821 = 3398933) B3398933
theorem B1986115 : Blo 1044610 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B3526253 : Blo 1044610 3526253 := bstep (se 3 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 3526253 = 1322345) B1322345
theorem B3526307 : Blo 1044610 3526307 := bstep (se 1 (by rfl) ⟨2644730, by rfl⟩ : syracuseStep 3526307 = 5289461) B5289461
theorem B5295779 : Blo 1044610 5295779 := bstep (se 1 (by rfl) ⟨3971834, by rfl⟩ : syracuseStep 5295779 = 7943669) B7943669
theorem B1986275 : Blo 1044610 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B3264241 : Blo 1044610 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B6377201 : Blo 1044610 6377201 := bstep (se 2 (by rfl) ⟨2391450, by rfl⟩ : syracuseStep 6377201 = 4782901) B4782901
theorem B3821347 : Blo 1044610 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B4476721 : Blo 1044610 4476721 := bstep (se 2 (by rfl) ⟨1678770, by rfl⟩ : syracuseStep 4476721 = 3357541) B3357541
theorem B2510659 : Blo 1044610 2510659 := bstep (se 1 (by rfl) ⟨1882994, by rfl⟩ : syracuseStep 2510659 = 3765989) B3765989
theorem B3526577 : Blo 1044610 3526577 := bstep (se 2 (by rfl) ⟨1322466, by rfl⟩ : syracuseStep 3526577 = 2644933) B2644933
theorem B14307313 : Blo 1044610 14307313 := bstep (se 2 (by rfl) ⟨5365242, by rfl⟩ : syracuseStep 14307313 = 10730485) B10730485
theorem B10047557 : Blo 1044610 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B2510929 : Blo 1044610 2510929 := bstep (se 2 (by rfl) ⟨941598, by rfl⟩ : syracuseStep 2510929 = 1883197) B1883197
theorem B3232145 : Blo 1044610 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B3527117 : Blo 1044610 3527117 := bstep (se 3 (by rfl) ⟨661334, by rfl⟩ : syracuseStep 3527117 = 1322669) B1322669
theorem B5296589 : Blo 1044610 5296589 := bstep (se 3 (by rfl) ⟨993110, by rfl⟩ : syracuseStep 5296589 = 1986221) B1986221
theorem B5034467 : Blo 1044610 5034467 := bstep (se 1 (by rfl) ⟨3775850, by rfl⟩ : syracuseStep 5034467 = 7551701) B7551701
theorem B3527171 : Blo 1044610 3527171 := bstep (se 1 (by rfl) ⟨2645378, by rfl⟩ : syracuseStep 3527171 = 5290757) B5290757
theorem B5034737 : Blo 1044610 5034737 := bstep (se 2 (by rfl) ⟨1888026, by rfl⟩ : syracuseStep 5034737 = 3776053) B3776053
theorem B3527441 : Blo 1044610 3527441 := bstep (se 2 (by rfl) ⟨1322790, by rfl⟩ : syracuseStep 3527441 = 2645581) B2645581
theorem B1987345 : Blo 1044610 1987345 := bstep (se 2 (by rfl) ⟨745254, by rfl⟩ : syracuseStep 1987345 = 1490509) B1490509
theorem B24171317 : Blo 1044610 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B5034851 : Blo 1044610 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B6706061 : Blo 1044610 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B3527981 : Blo 1044610 3527981 := bstep (se 3 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 3527981 = 1322993) B1322993
theorem B1725761 : Blo 1044610 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B3528035 : Blo 1044610 3528035 := bstep (se 1 (by rfl) ⟨2646026, by rfl⟩ : syracuseStep 3528035 = 5292053) B5292053
theorem B1791425 : Blo 1044610 1791425 := bstep (se 2 (by rfl) ⟨671784, by rfl⟩ : syracuseStep 1791425 = 1343569) B1343569
theorem B3528305 : Blo 1044610 3528305 := bstep (se 2 (by rfl) ⟨1323114, by rfl⟩ : syracuseStep 3528305 = 2646229) B2646229
theorem B33969941 : Blo 1044610 33969941 := bstep (se 6 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 33969941 = 1592341) B1592341
theorem B1988401 : Blo 1044610 1988401 := bstep (se 2 (by rfl) ⟨745650, by rfl⟩ : syracuseStep 1988401 = 1491301) B1491301
theorem B3528845 : Blo 1044610 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B3528899 : Blo 1044610 3528899 := bstep (se 1 (by rfl) ⟨2646674, by rfl⟩ : syracuseStep 3528899 = 5293349) B5293349
theorem B1988803 : Blo 1044610 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B1988849 : Blo 1044610 1988849 := bstep (se 2 (by rfl) ⟨745818, by rfl⟩ : syracuseStep 1988849 = 1491637) B1491637
theorem B5953925 : Blo 1044610 5953925 := bstep (se 4 (by rfl) ⟨558180, by rfl⟩ : syracuseStep 5953925 = 1116361) B1116361
theorem B2120113 : Blo 1044610 2120113 := bstep (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) B1590085
theorem B3529169 : Blo 1044610 3529169 := bstep (se 2 (by rfl) ⟨1323438, by rfl⟩ : syracuseStep 3529169 = 2646877) B2646877
theorem B1989137 : Blo 1044610 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1530499 : Blo 1044610 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B2644721 : Blo 1044610 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B2644771 : Blo 1044610 2644771 := bstep (se 1 (by rfl) ⟨1983578, by rfl⟩ : syracuseStep 2644771 = 3967157) B3967157
theorem B5954381 : Blo 1044610 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B2644913 : Blo 1044610 2644913 := bstep (se 2 (by rfl) ⟨991842, by rfl⟩ : syracuseStep 2644913 = 1983685) B1983685
theorem B3529709 : Blo 1044610 3529709 := bstep (se 3 (by rfl) ⟨661820, by rfl⟩ : syracuseStep 3529709 = 1323641) B1323641
theorem B3529763 : Blo 1044610 3529763 := bstep (se 1 (by rfl) ⟨2647322, by rfl⟩ : syracuseStep 3529763 = 5294645) B5294645
theorem B1989859 : Blo 1044610 1989859 := bstep (se 1 (by rfl) ⟨1492394, by rfl⟩ : syracuseStep 1989859 = 2984789) B2984789
theorem B2350385 : Blo 1044610 2350385 := bstep (se 2 (by rfl) ⟨881394, by rfl⟩ : syracuseStep 2350385 = 1762789) B1762789
theorem B3530033 : Blo 1044610 3530033 := bstep (se 2 (by rfl) ⟨1323762, by rfl⟩ : syracuseStep 3530033 = 2647525) B2647525
theorem B5299505 : Blo 1044610 5299505 := bstep (se 2 (by rfl) ⟨1987314, by rfl⟩ : syracuseStep 5299505 = 3974629) B3974629
theorem B2350403 : Blo 1044610 2350403 := bstep (se 1 (by rfl) ⟨1762802, by rfl⟩ : syracuseStep 2350403 = 3525605) B3525605
theorem B2350673 : Blo 1044610 2350673 := bstep (se 2 (by rfl) ⟨881502, by rfl⟩ : syracuseStep 2350673 = 1763005) B1763005
theorem B2350691 : Blo 1044610 2350691 := bstep (se 1 (by rfl) ⟨1763018, by rfl⟩ : syracuseStep 2350691 = 3526037) B3526037
theorem B2383523 : Blo 1044610 2383523 := bstep (se 1 (by rfl) ⟨1787642, by rfl⟩ : syracuseStep 2383523 = 3575285) B3575285
theorem B1990307 : Blo 1044610 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B3530573 : Blo 1044610 3530573 := bstep (se 3 (by rfl) ⟨661982, by rfl⟩ : syracuseStep 3530573 = 1323965) B1323965
theorem B2350961 : Blo 1044610 2350961 := bstep (se 2 (by rfl) ⟨881610, by rfl⟩ : syracuseStep 2350961 = 1763221) B1763221
theorem B2350979 : Blo 1044610 2350979 := bstep (se 1 (by rfl) ⟨1763234, by rfl⟩ : syracuseStep 2350979 = 3526469) B3526469
theorem B3530627 : Blo 1044610 3530627 := bstep (se 1 (by rfl) ⟨2647970, by rfl⟩ : syracuseStep 3530627 = 5295941) B5295941
theorem B2645905 : Blo 1044610 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B1990595 : Blo 1044610 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B2515043 : Blo 1044610 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B5726321 : Blo 1044610 5726321 := bstep (se 2 (by rfl) ⟨2147370, by rfl⟩ : syracuseStep 5726321 = 4294741) B4294741
theorem B2351249 : Blo 1044610 2351249 := bstep (se 2 (by rfl) ⟨881718, by rfl⟩ : syracuseStep 2351249 = 1763437) B1763437
theorem B3530897 : Blo 1044610 3530897 := bstep (se 2 (by rfl) ⟨1324086, by rfl⟩ : syracuseStep 3530897 = 2648173) B2648173
theorem B2351267 : Blo 1044610 2351267 := bstep (se 1 (by rfl) ⟨1763450, by rfl⟩ : syracuseStep 2351267 = 3526901) B3526901
theorem B2646179 : Blo 1044610 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B2646371 : Blo 1044610 2646371 := bstep (se 1 (by rfl) ⟨1984778, by rfl⟩ : syracuseStep 2646371 = 3969557) B3969557
theorem B2351537 : Blo 1044610 2351537 := bstep (se 2 (by rfl) ⟨881826, by rfl⟩ : syracuseStep 2351537 = 1763653) B1763653
theorem B2351555 : Blo 1044610 2351555 := bstep (se 1 (by rfl) ⟨1763666, by rfl⟩ : syracuseStep 2351555 = 3527333) B3527333
theorem B5038541 : Blo 1044610 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B2515427 : Blo 1044610 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B3531437 : Blo 1044610 3531437 := bstep (se 3 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 3531437 = 1324289) B1324289
theorem B2351825 : Blo 1044610 2351825 := bstep (se 2 (by rfl) ⟨881934, by rfl⟩ : syracuseStep 2351825 = 1763869) B1763869
theorem B2351843 : Blo 1044610 2351843 := bstep (se 1 (by rfl) ⟨1763882, by rfl⟩ : syracuseStep 2351843 = 3527765) B3527765
theorem B3531491 : Blo 1044610 3531491 := bstep (se 1 (by rfl) ⟨2648618, by rfl⟩ : syracuseStep 3531491 = 5297237) B5297237
theorem B5300963 : Blo 1044610 5300963 := bstep (se 1 (by rfl) ⟨3975722, by rfl⟩ : syracuseStep 5300963 = 7951445) B7951445
theorem B51602197 : Blo 1044610 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B2352113 : Blo 1044610 2352113 := bstep (se 2 (by rfl) ⟨882042, by rfl⟩ : syracuseStep 2352113 = 1764085) B1764085
theorem B3531761 : Blo 1044610 3531761 := bstep (se 2 (by rfl) ⟨1324410, by rfl⟩ : syracuseStep 3531761 = 2648821) B2648821
theorem B2352131 : Blo 1044610 2352131 := bstep (se 1 (by rfl) ⟨1764098, by rfl⟩ : syracuseStep 2352131 = 3528197) B3528197
theorem B2515985 : Blo 1044610 2515985 := bstep (se 2 (by rfl) ⟨943494, by rfl⟩ : syracuseStep 2515985 = 1886989) B1886989
theorem B2974765 : Blo 1044610 2974765 := bstep (se 3 (by rfl) ⟨557768, by rfl⟩ : syracuseStep 2974765 = 1115537) B1115537
theorem B7169093 : Blo 1044610 7169093 := bstep (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) B1344205
theorem B1696897 : Blo 1044610 1696897 := bstep (se 2 (by rfl) ⟨636336, by rfl⟩ : syracuseStep 1696897 = 1272673) B1272673
theorem B7169201 : Blo 1044610 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B2516195 : Blo 1044610 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B2352401 : Blo 1044610 2352401 := bstep (se 2 (by rfl) ⟨882150, by rfl⟩ : syracuseStep 2352401 = 1764301) B1764301
theorem B2647313 : Blo 1044610 2647313 := bstep (se 2 (by rfl) ⟨992742, by rfl⟩ : syracuseStep 2647313 = 1985485) B1985485
theorem B2352419 : Blo 1044610 2352419 := bstep (se 1 (by rfl) ⟨1764314, by rfl⟩ : syracuseStep 2352419 = 3528629) B3528629
theorem B2647363 : Blo 1044610 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B2647505 : Blo 1044610 2647505 := bstep (se 2 (by rfl) ⟨992814, by rfl⟩ : syracuseStep 2647505 = 1985629) B1985629
theorem B3532301 : Blo 1044610 3532301 := bstep (se 3 (by rfl) ⟨662306, by rfl⟩ : syracuseStep 3532301 = 1324613) B1324613
theorem B5301773 : Blo 1044610 5301773 := bstep (se 3 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 5301773 = 1988165) B1988165
theorem B2352689 : Blo 1044610 2352689 := bstep (se 2 (by rfl) ⟨882258, by rfl⟩ : syracuseStep 2352689 = 1764517) B1764517
theorem B2352707 : Blo 1044610 2352707 := bstep (se 1 (by rfl) ⟨1764530, by rfl⟩ : syracuseStep 2352707 = 3529061) B3529061
theorem B3532355 : Blo 1044610 3532355 := bstep (se 1 (by rfl) ⟨2649266, by rfl⟩ : syracuseStep 3532355 = 5298533) B5298533
theorem B1762897 : Blo 1044610 1762897 := bstep (se 2 (by rfl) ⟨661086, by rfl⟩ : syracuseStep 1762897 = 1322173) B1322173
theorem B1762931 : Blo 1044610 1762931 := bstep (se 1 (by rfl) ⟨1322198, by rfl⟩ : syracuseStep 1762931 = 2644397) B2644397
theorem B2385539 : Blo 1044610 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B5662349 : Blo 1044610 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B5957297 : Blo 1044610 5957297 := bstep (se 2 (by rfl) ⟨2233986, by rfl⟩ : syracuseStep 5957297 = 4467973) B4467973
theorem B1763059 : Blo 1044610 1763059 := bstep (se 1 (by rfl) ⟨1322294, by rfl⟩ : syracuseStep 1763059 = 2644589) B2644589
theorem B5662477 : Blo 1044610 5662477 := bstep (se 3 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 5662477 = 2123429) B2123429
theorem B2385713 : Blo 1044610 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B2352977 : Blo 1044610 2352977 := bstep (se 2 (by rfl) ⟨882366, by rfl⟩ : syracuseStep 2352977 = 1764733) B1764733
theorem B3532625 : Blo 1044610 3532625 := bstep (se 2 (by rfl) ⟨1324734, by rfl⟩ : syracuseStep 3532625 = 2649469) B2649469
theorem B2352995 : Blo 1044610 2352995 := bstep (se 1 (by rfl) ⟨1764746, by rfl⟩ : syracuseStep 2352995 = 3529493) B3529493
theorem B1763201 : Blo 1044610 1763201 := bstep (se 2 (by rfl) ⟨661200, by rfl⟩ : syracuseStep 1763201 = 1322401) B1322401
theorem B1763329 : Blo 1044610 1763329 := bstep (se 2 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 1763329 = 1322497) B1322497
theorem B1763363 : Blo 1044610 1763363 := bstep (se 1 (by rfl) ⟨1322522, by rfl⟩ : syracuseStep 1763363 = 2645045) B2645045
theorem B2517041 : Blo 1044610 2517041 := bstep (se 2 (by rfl) ⟨943890, by rfl⟩ : syracuseStep 2517041 = 1887781) B1887781
theorem B2353265 : Blo 1044610 2353265 := bstep (se 2 (by rfl) ⟨882474, by rfl⟩ : syracuseStep 2353265 = 1764949) B1764949
theorem B2353283 : Blo 1044610 2353283 := bstep (se 1 (by rfl) ⟨1764962, by rfl⟩ : syracuseStep 2353283 = 3529925) B3529925
theorem B1763491 : Blo 1044610 1763491 := bstep (se 1 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 1763491 = 2645237) B2645237
theorem B24176837 : Blo 1044610 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B6711493 : Blo 1044610 6711493 := bstep (se 4 (by rfl) ⟨629202, by rfl⟩ : syracuseStep 6711493 = 1258405) B1258405
theorem B1566929 : Blo 1044610 1566929 := bstep (se 2 (by rfl) ⟨587598, by rfl⟩ : syracuseStep 1566929 = 1175197) B1175197
theorem B1566947 : Blo 1044610 1566947 := bstep (se 1 (by rfl) ⟨1175210, by rfl⟩ : syracuseStep 1566947 = 2350421) B2350421
theorem B1566977 : Blo 1044610 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1566995 : Blo 1044610 1566995 := bstep (se 1 (by rfl) ⟨1175246, by rfl⟩ : syracuseStep 1566995 = 2350493) B2350493
theorem B1567025 : Blo 1044610 1567025 := bstep (se 2 (by rfl) ⟨587634, by rfl⟩ : syracuseStep 1567025 = 1175269) B1175269
theorem B1763633 : Blo 1044610 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B1567043 : Blo 1044610 1567043 := bstep (se 1 (by rfl) ⟨1175282, by rfl⟩ : syracuseStep 1567043 = 2350565) B2350565
theorem B1567073 : Blo 1044610 1567073 := bstep (se 2 (by rfl) ⟨587652, by rfl⟩ : syracuseStep 1567073 = 1175305) B1175305
theorem B3533165 : Blo 1044610 3533165 := bstep (se 3 (by rfl) ⟨662468, by rfl⟩ : syracuseStep 3533165 = 1324937) B1324937
theorem B1567091 : Blo 1044610 1567091 := bstep (se 1 (by rfl) ⟨1175318, by rfl⟩ : syracuseStep 1567091 = 2350637) B2350637
theorem B1567121 : Blo 1044610 1567121 := bstep (se 2 (by rfl) ⟨587670, by rfl⟩ : syracuseStep 1567121 = 1175341) B1175341
theorem B2353553 : Blo 1044610 2353553 := bstep (se 2 (by rfl) ⟨882582, by rfl⟩ : syracuseStep 2353553 = 1765165) B1765165
theorem B1567139 : Blo 1044610 1567139 := bstep (se 1 (by rfl) ⟨1175354, by rfl⟩ : syracuseStep 1567139 = 2350709) B2350709
theorem B2353571 : Blo 1044610 2353571 := bstep (se 1 (by rfl) ⟨1765178, by rfl⟩ : syracuseStep 2353571 = 3530357) B3530357
theorem B3533219 : Blo 1044610 3533219 := bstep (se 1 (by rfl) ⟨2649914, by rfl⟩ : syracuseStep 3533219 = 5299829) B5299829
theorem B1763761 : Blo 1044610 1763761 := bstep (se 2 (by rfl) ⟨661410, by rfl⟩ : syracuseStep 1763761 = 1322821) B1322821
theorem B2648497 : Blo 1044610 2648497 := bstep (se 2 (by rfl) ⟨993186, by rfl⟩ : syracuseStep 2648497 = 1986373) B1986373
theorem B1567169 : Blo 1044610 1567169 := bstep (se 2 (by rfl) ⟨587688, by rfl⟩ : syracuseStep 1567169 = 1175377) B1175377
theorem B1567187 : Blo 1044610 1567187 := bstep (se 1 (by rfl) ⟨1175390, by rfl⟩ : syracuseStep 1567187 = 2350781) B2350781
theorem B1763795 : Blo 1044610 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1567217 : Blo 1044610 1567217 := bstep (se 2 (by rfl) ⟨587706, by rfl⟩ : syracuseStep 1567217 = 1175413) B1175413
theorem B1436161 : Blo 1044610 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B1567235 : Blo 1044610 1567235 := bstep (se 1 (by rfl) ⟨1175426, by rfl⟩ : syracuseStep 1567235 = 2350853) B2350853
theorem B1567265 : Blo 1044610 1567265 := bstep (se 2 (by rfl) ⟨587724, by rfl⟩ : syracuseStep 1567265 = 1175449) B1175449
theorem B1567283 : Blo 1044610 1567283 := bstep (se 1 (by rfl) ⟨1175462, by rfl⟩ : syracuseStep 1567283 = 2350925) B2350925
theorem B2517571 : Blo 1044610 2517571 := bstep (se 1 (by rfl) ⟨1888178, by rfl⟩ : syracuseStep 2517571 = 3776357) B3776357
theorem B1567313 : Blo 1044610 1567313 := bstep (se 2 (by rfl) ⟨587742, by rfl⟩ : syracuseStep 1567313 = 1175485) B1175485
theorem B1763923 : Blo 1044610 1763923 := bstep (se 1 (by rfl) ⟨1322942, by rfl⟩ : syracuseStep 1763923 = 2645885) B2645885
theorem B1567331 : Blo 1044610 1567331 := bstep (se 1 (by rfl) ⟨1175498, by rfl⟩ : syracuseStep 1567331 = 2350997) B2350997
theorem B1567361 : Blo 1044610 1567361 := bstep (se 2 (by rfl) ⟨587760, by rfl⟩ : syracuseStep 1567361 = 1175521) B1175521
theorem B1567379 : Blo 1044610 1567379 := bstep (se 1 (by rfl) ⟨1175534, by rfl⟩ : syracuseStep 1567379 = 2351069) B2351069
theorem B1567409 : Blo 1044610 1567409 := bstep (se 2 (by rfl) ⟨587778, by rfl⟩ : syracuseStep 1567409 = 1175557) B1175557
theorem B2353841 : Blo 1044610 2353841 := bstep (se 2 (by rfl) ⟨882690, by rfl⟩ : syracuseStep 2353841 = 1765381) B1765381
theorem B3533489 : Blo 1044610 3533489 := bstep (se 2 (by rfl) ⟨1325058, by rfl⟩ : syracuseStep 3533489 = 2650117) B2650117
theorem B1567427 : Blo 1044610 1567427 := bstep (se 1 (by rfl) ⟨1175570, by rfl⟩ : syracuseStep 1567427 = 2351141) B2351141
theorem B2353859 : Blo 1044610 2353859 := bstep (se 1 (by rfl) ⟨1765394, by rfl⟩ : syracuseStep 2353859 = 3530789) B3530789
theorem B2648771 : Blo 1044610 2648771 := bstep (se 1 (by rfl) ⟨1986578, by rfl⟩ : syracuseStep 2648771 = 3973157) B3973157
theorem B1567457 : Blo 1044610 1567457 := bstep (se 2 (by rfl) ⟨587796, by rfl⟩ : syracuseStep 1567457 = 1175593) B1175593
theorem B1764065 : Blo 1044610 1764065 := bstep (se 2 (by rfl) ⟨661524, by rfl⟩ : syracuseStep 1764065 = 1323049) B1323049
theorem B2976497 : Blo 1044610 2976497 := bstep (se 2 (by rfl) ⟨1116186, by rfl⟩ : syracuseStep 2976497 = 2232373) B2232373
theorem B1567475 : Blo 1044610 1567475 := bstep (se 1 (by rfl) ⟨1175606, by rfl⟩ : syracuseStep 1567475 = 2351213) B2351213
theorem B1567505 : Blo 1044610 1567505 := bstep (se 2 (by rfl) ⟨587814, by rfl⟩ : syracuseStep 1567505 = 1175629) B1175629
theorem B1567523 : Blo 1044610 1567523 := bstep (se 1 (by rfl) ⟨1175642, by rfl⟩ : syracuseStep 1567523 = 2351285) B2351285
theorem B1567553 : Blo 1044610 1567553 := bstep (se 2 (by rfl) ⟨587832, by rfl⟩ : syracuseStep 1567553 = 1175665) B1175665
theorem B1567571 : Blo 1044610 1567571 := bstep (se 1 (by rfl) ⟨1175678, by rfl⟩ : syracuseStep 1567571 = 2351357) B2351357
theorem B1764193 : Blo 1044610 1764193 := bstep (se 2 (by rfl) ⟨661572, by rfl⟩ : syracuseStep 1764193 = 1323145) B1323145
theorem B1567601 : Blo 1044610 1567601 := bstep (se 2 (by rfl) ⟨587850, by rfl⟩ : syracuseStep 1567601 = 1175701) B1175701
theorem B1567619 : Blo 1044610 1567619 := bstep (se 1 (by rfl) ⟨1175714, by rfl⟩ : syracuseStep 1567619 = 2351429) B2351429
theorem B1764227 : Blo 1044610 1764227 := bstep (se 1 (by rfl) ⟨1323170, by rfl⟩ : syracuseStep 1764227 = 2646341) B2646341
theorem B2648963 : Blo 1044610 2648963 := bstep (se 1 (by rfl) ⟨1986722, by rfl⟩ : syracuseStep 2648963 = 3973445) B3973445
theorem B1567649 : Blo 1044610 1567649 := bstep (se 2 (by rfl) ⟨587868, by rfl⟩ : syracuseStep 1567649 = 1175737) B1175737
theorem B2976689 : Blo 1044610 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B1567667 : Blo 1044610 1567667 := bstep (se 1 (by rfl) ⟨1175750, by rfl⟩ : syracuseStep 1567667 = 2351501) B2351501
theorem B1567697 : Blo 1044610 1567697 := bstep (se 2 (by rfl) ⟨587886, by rfl⟩ : syracuseStep 1567697 = 1175773) B1175773
theorem B2354129 : Blo 1044610 2354129 := bstep (se 2 (by rfl) ⟨882798, by rfl⟩ : syracuseStep 2354129 = 1765597) B1765597
theorem B1567715 : Blo 1044610 1567715 := bstep (se 1 (by rfl) ⟨1175786, by rfl⟩ : syracuseStep 1567715 = 2351573) B2351573
theorem B2354147 : Blo 1044610 2354147 := bstep (se 1 (by rfl) ⟨1765610, by rfl⟩ : syracuseStep 2354147 = 3531221) B3531221
theorem B2124785 : Blo 1044610 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B1567745 : Blo 1044610 1567745 := bstep (se 2 (by rfl) ⟨587904, by rfl⟩ : syracuseStep 1567745 = 1175809) B1175809
theorem B1764355 : Blo 1044610 1764355 := bstep (se 1 (by rfl) ⟨1323266, by rfl⟩ : syracuseStep 1764355 = 2646533) B2646533
theorem B1567763 : Blo 1044610 1567763 := bstep (se 1 (by rfl) ⟨1175822, by rfl⟩ : syracuseStep 1567763 = 2351645) B2351645
theorem B1567793 : Blo 1044610 1567793 := bstep (se 2 (by rfl) ⟨587922, by rfl⟩ : syracuseStep 1567793 = 1175845) B1175845
theorem B13593653 : Blo 1044610 13593653 := bstep (se 5 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 13593653 = 1274405) B1274405
theorem B1567811 : Blo 1044610 1567811 := bstep (se 1 (by rfl) ⟨1175858, by rfl⟩ : syracuseStep 1567811 = 2351717) B2351717
theorem B1567841 : Blo 1044610 1567841 := bstep (se 2 (by rfl) ⟨587940, by rfl⟩ : syracuseStep 1567841 = 1175881) B1175881
theorem B5958755 : Blo 1044610 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B1567859 : Blo 1044610 1567859 := bstep (se 1 (by rfl) ⟨1175894, by rfl⟩ : syracuseStep 1567859 = 2351789) B2351789
theorem B1567889 : Blo 1044610 1567889 := bstep (se 2 (by rfl) ⟨587958, by rfl⟩ : syracuseStep 1567889 = 1175917) B1175917
theorem B1764497 : Blo 1044610 1764497 := bstep (se 2 (by rfl) ⟨661686, by rfl⟩ : syracuseStep 1764497 = 1323373) B1323373
theorem B1567907 : Blo 1044610 1567907 := bstep (se 1 (by rfl) ⟨1175930, by rfl⟩ : syracuseStep 1567907 = 2351861) B2351861
theorem B2387107 : Blo 1044610 2387107 := bstep (se 1 (by rfl) ⟨1790330, by rfl⟩ : syracuseStep 2387107 = 3580661) B3580661
theorem B1567937 : Blo 1044610 1567937 := bstep (se 2 (by rfl) ⟨587976, by rfl⟩ : syracuseStep 1567937 = 1175953) B1175953
theorem B3534029 : Blo 1044610 3534029 := bstep (se 3 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 3534029 = 1325261) B1325261
theorem B1567955 : Blo 1044610 1567955 := bstep (se 1 (by rfl) ⟨1175966, by rfl⟩ : syracuseStep 1567955 = 2351933) B2351933
theorem B1567985 : Blo 1044610 1567985 := bstep (se 2 (by rfl) ⟨587994, by rfl⟩ : syracuseStep 1567985 = 1175989) B1175989
theorem B2354417 : Blo 1044610 2354417 := bstep (se 2 (by rfl) ⟨882906, by rfl⟩ : syracuseStep 2354417 = 1765813) B1765813
theorem B1568003 : Blo 1044610 1568003 := bstep (se 1 (by rfl) ⟨1176002, by rfl⟩ : syracuseStep 1568003 = 2352005) B2352005
theorem B2354435 : Blo 1044610 2354435 := bstep (se 1 (by rfl) ⟨1765826, by rfl⟩ : syracuseStep 2354435 = 3531653) B3531653
theorem B3534083 : Blo 1044610 3534083 := bstep (se 1 (by rfl) ⟨2650562, by rfl⟩ : syracuseStep 3534083 = 5301125) B5301125
theorem B1764625 : Blo 1044610 1764625 := bstep (se 2 (by rfl) ⟨661734, by rfl⟩ : syracuseStep 1764625 = 1323469) B1323469
theorem B1568033 : Blo 1044610 1568033 := bstep (se 2 (by rfl) ⟨588012, by rfl⟩ : syracuseStep 1568033 = 1176025) B1176025
theorem B1568051 : Blo 1044610 1568051 := bstep (se 1 (by rfl) ⟨1176038, by rfl⟩ : syracuseStep 1568051 = 2352077) B2352077
theorem B1764659 : Blo 1044610 1764659 := bstep (se 1 (by rfl) ⟨1323494, by rfl⟩ : syracuseStep 1764659 = 2646989) B2646989
theorem B1568081 : Blo 1044610 1568081 := bstep (se 2 (by rfl) ⟨588030, by rfl⟩ : syracuseStep 1568081 = 1176061) B1176061
theorem B1568099 : Blo 1044610 1568099 := bstep (se 1 (by rfl) ⟨1176074, by rfl⟩ : syracuseStep 1568099 = 2352149) B2352149
theorem B1568129 : Blo 1044610 1568129 := bstep (se 2 (by rfl) ⟨588048, by rfl⟩ : syracuseStep 1568129 = 1176097) B1176097
theorem B1568147 : Blo 1044610 1568147 := bstep (se 1 (by rfl) ⟨1176110, by rfl⟩ : syracuseStep 1568147 = 2352221) B2352221
theorem B1568177 : Blo 1044610 1568177 := bstep (se 2 (by rfl) ⟨588066, by rfl⟩ : syracuseStep 1568177 = 1176133) B1176133
theorem B1764787 : Blo 1044610 1764787 := bstep (se 1 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 1764787 = 2647181) B2647181
theorem B1568195 : Blo 1044610 1568195 := bstep (se 1 (by rfl) ⟨1176146, by rfl⟩ : syracuseStep 1568195 = 2352293) B2352293
theorem B1568225 : Blo 1044610 1568225 := bstep (se 2 (by rfl) ⟨588084, by rfl⟩ : syracuseStep 1568225 = 1176169) B1176169
theorem B1273315 : Blo 1044610 1273315 := bstep (se 1 (by rfl) ⟨954986, by rfl⟩ : syracuseStep 1273315 = 1909973) B1909973
theorem B1568243 : Blo 1044610 1568243 := bstep (se 1 (by rfl) ⟨1176182, by rfl⟩ : syracuseStep 1568243 = 2352365) B2352365
theorem B1568273 : Blo 1044610 1568273 := bstep (se 2 (by rfl) ⟨588102, by rfl⟩ : syracuseStep 1568273 = 1176205) B1176205
theorem B2354705 : Blo 1044610 2354705 := bstep (se 2 (by rfl) ⟨883014, by rfl⟩ : syracuseStep 2354705 = 1766029) B1766029
theorem B3534353 : Blo 1044610 3534353 := bstep (se 2 (by rfl) ⟨1325382, by rfl⟩ : syracuseStep 3534353 = 2650765) B2650765
theorem B1568291 : Blo 1044610 1568291 := bstep (se 1 (by rfl) ⟨1176218, by rfl⟩ : syracuseStep 1568291 = 2352437) B2352437
theorem B2354723 : Blo 1044610 2354723 := bstep (se 1 (by rfl) ⟨1766042, by rfl⟩ : syracuseStep 2354723 = 3532085) B3532085
theorem B1568321 : Blo 1044610 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B1764929 : Blo 1044610 1764929 := bstep (se 2 (by rfl) ⟨661848, by rfl⟩ : syracuseStep 1764929 = 1323697) B1323697
theorem B1568339 : Blo 1044610 1568339 := bstep (se 1 (by rfl) ⟨1176254, by rfl⟩ : syracuseStep 1568339 = 2352509) B2352509
theorem B1568369 : Blo 1044610 1568369 := bstep (se 2 (by rfl) ⟨588138, by rfl⟩ : syracuseStep 1568369 = 1176277) B1176277
theorem B1568387 : Blo 1044610 1568387 := bstep (se 1 (by rfl) ⟨1176290, by rfl⟩ : syracuseStep 1568387 = 2352581) B2352581
theorem B1568417 : Blo 1044610 1568417 := bstep (se 2 (by rfl) ⟨588156, by rfl⟩ : syracuseStep 1568417 = 1176313) B1176313
theorem B1568435 : Blo 1044610 1568435 := bstep (se 1 (by rfl) ⟨1176326, by rfl⟩ : syracuseStep 1568435 = 2352653) B2352653
theorem B1765057 : Blo 1044610 1765057 := bstep (se 2 (by rfl) ⟨661896, by rfl⟩ : syracuseStep 1765057 = 1323793) B1323793
theorem B1568465 : Blo 1044610 1568465 := bstep (se 2 (by rfl) ⟨588174, by rfl⟩ : syracuseStep 1568465 = 1176349) B1176349
theorem B1175251 : Blo 1044610 1175251 := bstep (se 1 (by rfl) ⟨881438, by rfl⟩ : syracuseStep 1175251 = 1762877) B1762877
theorem B1568483 : Blo 1044610 1568483 := bstep (se 1 (by rfl) ⟨1176362, by rfl⟩ : syracuseStep 1568483 = 2352725) B2352725
theorem B1765091 : Blo 1044610 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B1568513 : Blo 1044610 1568513 := bstep (se 2 (by rfl) ⟨588192, by rfl⟩ : syracuseStep 1568513 = 1176385) B1176385
theorem B1568531 : Blo 1044610 1568531 := bstep (se 1 (by rfl) ⟨1176398, by rfl⟩ : syracuseStep 1568531 = 2352797) B2352797
theorem B1568561 : Blo 1044610 1568561 := bstep (se 2 (by rfl) ⟨588210, by rfl⟩ : syracuseStep 1568561 = 1176421) B1176421
theorem B2354993 : Blo 1044610 2354993 := bstep (se 2 (by rfl) ⟨883122, by rfl⟩ : syracuseStep 2354993 = 1766245) B1766245
theorem B2649905 : Blo 1044610 2649905 := bstep (se 2 (by rfl) ⟨993714, by rfl⟩ : syracuseStep 2649905 = 1987429) B1987429
theorem B1568579 : Blo 1044610 1568579 := bstep (se 1 (by rfl) ⟨1176434, by rfl⟩ : syracuseStep 1568579 = 2352869) B2352869
theorem B2355011 : Blo 1044610 2355011 := bstep (se 1 (by rfl) ⟨1766258, by rfl⟩ : syracuseStep 2355011 = 3532517) B3532517
theorem B1568609 : Blo 1044610 1568609 := bstep (se 2 (by rfl) ⟨588228, by rfl⟩ : syracuseStep 1568609 = 1176457) B1176457
theorem B1175395 : Blo 1044610 1175395 := bstep (se 1 (by rfl) ⟨881546, by rfl⟩ : syracuseStep 1175395 = 1763093) B1763093
theorem B1765219 : Blo 1044610 1765219 := bstep (se 1 (by rfl) ⟨1323914, by rfl⟩ : syracuseStep 1765219 = 2647829) B2647829
theorem B2649955 : Blo 1044610 2649955 := bstep (se 1 (by rfl) ⟨1987466, by rfl⟩ : syracuseStep 2649955 = 3974933) B3974933
theorem B1568627 : Blo 1044610 1568627 := bstep (se 1 (by rfl) ⟨1176470, by rfl⟩ : syracuseStep 1568627 = 2352941) B2352941
theorem B2977681 : Blo 1044610 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1568657 : Blo 1044610 1568657 := bstep (se 2 (by rfl) ⟨588246, by rfl⟩ : syracuseStep 1568657 = 1176493) B1176493
theorem B1568675 : Blo 1044610 1568675 := bstep (se 1 (by rfl) ⟨1176506, by rfl⟩ : syracuseStep 1568675 = 2353013) B2353013
theorem B1568705 : Blo 1044610 1568705 := bstep (se 2 (by rfl) ⟨588264, by rfl⟩ : syracuseStep 1568705 = 1176529) B1176529
theorem B1699793 : Blo 1044610 1699793 := bstep (se 2 (by rfl) ⟨637422, by rfl⟩ : syracuseStep 1699793 = 1274845) B1274845
theorem B1568723 : Blo 1044610 1568723 := bstep (se 1 (by rfl) ⟨1176542, by rfl⟩ : syracuseStep 1568723 = 2353085) B2353085
theorem B1568753 : Blo 1044610 1568753 := bstep (se 2 (by rfl) ⟨588282, by rfl⟩ : syracuseStep 1568753 = 1176565) B1176565
theorem B1765361 : Blo 1044610 1765361 := bstep (se 2 (by rfl) ⟨662010, by rfl⟩ : syracuseStep 1765361 = 1324021) B1324021
theorem B1175539 : Blo 1044610 1175539 := bstep (se 1 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 1175539 = 1763309) B1763309
theorem B2650097 : Blo 1044610 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B1568771 : Blo 1044610 1568771 := bstep (se 1 (by rfl) ⟨1176578, by rfl⟩ : syracuseStep 1568771 = 2353157) B2353157
theorem B1568801 : Blo 1044610 1568801 := bstep (se 2 (by rfl) ⟨588300, by rfl⟩ : syracuseStep 1568801 = 1176601) B1176601
theorem B3534893 : Blo 1044610 3534893 := bstep (se 3 (by rfl) ⟨662792, by rfl⟩ : syracuseStep 3534893 = 1325585) B1325585
theorem B1568819 : Blo 1044610 1568819 := bstep (se 1 (by rfl) ⟨1176614, by rfl⟩ : syracuseStep 1568819 = 2353229) B2353229
theorem B19132469 : Blo 1044610 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B5959757 : Blo 1044610 5959757 := bstep (se 3 (by rfl) ⟨1117454, by rfl⟩ : syracuseStep 5959757 = 2234909) B2234909
theorem B1568849 : Blo 1044610 1568849 := bstep (se 2 (by rfl) ⟨588318, by rfl⟩ : syracuseStep 1568849 = 1176637) B1176637
theorem B2355281 : Blo 1044610 2355281 := bstep (se 2 (by rfl) ⟨883230, by rfl⟩ : syracuseStep 2355281 = 1766461) B1766461
theorem B1568867 : Blo 1044610 1568867 := bstep (se 1 (by rfl) ⟨1176650, by rfl⟩ : syracuseStep 1568867 = 2353301) B2353301
theorem B2355299 : Blo 1044610 2355299 := bstep (se 1 (by rfl) ⟨1766474, by rfl⟩ : syracuseStep 2355299 = 3532949) B3532949
theorem B3534947 : Blo 1044610 3534947 := bstep (se 1 (by rfl) ⟨2651210, by rfl⟩ : syracuseStep 3534947 = 5302421) B5302421
theorem B1765489 : Blo 1044610 1765489 := bstep (se 2 (by rfl) ⟨662058, by rfl⟩ : syracuseStep 1765489 = 1324117) B1324117
theorem B1568897 : Blo 1044610 1568897 := bstep (se 2 (by rfl) ⟨588336, by rfl⟩ : syracuseStep 1568897 = 1176673) B1176673
theorem B1044611 : Blo 1044610 1044611 := bstep (se 1 (by rfl) ⟨783458, by rfl⟩ : syracuseStep 1044611 = 1566917) B1566917
theorem B1175683 : Blo 1044610 1175683 := bstep (se 1 (by rfl) ⟨881762, by rfl⟩ : syracuseStep 1175683 = 1763525) B1763525
theorem B1044627 : Blo 1044610 1044627 := bstep (se 1 (by rfl) ⟨783470, by rfl⟩ : syracuseStep 1044627 = 1566941) B1566941
theorem B1568915 : Blo 1044610 1568915 := bstep (se 1 (by rfl) ⟨1176686, by rfl⟩ : syracuseStep 1568915 = 2353373) B2353373
theorem B1765523 : Blo 1044610 1765523 := bstep (se 1 (by rfl) ⟨1324142, by rfl⟩ : syracuseStep 1765523 = 2648285) B2648285
theorem B1044643 : Blo 1044610 1044643 := bstep (se 1 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 1044643 = 1566965) B1566965
theorem B2977955 : Blo 1044610 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B1568945 : Blo 1044610 1568945 := bstep (se 2 (by rfl) ⟨588354, by rfl⟩ : syracuseStep 1568945 = 1176709) B1176709
theorem B1044659 : Blo 1044610 1044659 := bstep (se 1 (by rfl) ⟨783494, by rfl⟩ : syracuseStep 1044659 = 1566989) B1566989
theorem B1044675 : Blo 1044610 1044675 := bstep (se 1 (by rfl) ⟨783506, by rfl⟩ : syracuseStep 1044675 = 1567013) B1567013
theorem B1568963 : Blo 1044610 1568963 := bstep (se 1 (by rfl) ⟨1176722, by rfl⟩ : syracuseStep 1568963 = 2353445) B2353445
theorem B1044691 : Blo 1044610 1044691 := bstep (se 1 (by rfl) ⟨783518, by rfl⟩ : syracuseStep 1044691 = 1567037) B1567037
theorem B1568993 : Blo 1044610 1568993 := bstep (se 2 (by rfl) ⟨588372, by rfl⟩ : syracuseStep 1568993 = 1176745) B1176745
theorem B1044707 : Blo 1044610 1044707 := bstep (se 1 (by rfl) ⟨783530, by rfl⟩ : syracuseStep 1044707 = 1567061) B1567061
theorem B1044723 : Blo 1044610 1044723 := bstep (se 1 (by rfl) ⟨783542, by rfl⟩ : syracuseStep 1044723 = 1567085) B1567085
theorem B1569011 : Blo 1044610 1569011 := bstep (se 1 (by rfl) ⟨1176758, by rfl⟩ : syracuseStep 1569011 = 2353517) B2353517
theorem B1044739 : Blo 1044610 1044739 := bstep (se 1 (by rfl) ⟨783554, by rfl⟩ : syracuseStep 1044739 = 1567109) B1567109
theorem B1569041 : Blo 1044610 1569041 := bstep (se 2 (by rfl) ⟨588390, by rfl⟩ : syracuseStep 1569041 = 1176781) B1176781
theorem B1044755 : Blo 1044610 1044755 := bstep (se 1 (by rfl) ⟨783566, by rfl⟩ : syracuseStep 1044755 = 1567133) B1567133
theorem B1175827 : Blo 1044610 1175827 := bstep (se 1 (by rfl) ⟨881870, by rfl⟩ : syracuseStep 1175827 = 1763741) B1763741
theorem B1765651 : Blo 1044610 1765651 := bstep (se 1 (by rfl) ⟨1324238, by rfl⟩ : syracuseStep 1765651 = 2648477) B2648477
theorem B1044771 : Blo 1044610 1044771 := bstep (se 1 (by rfl) ⟨783578, by rfl⟩ : syracuseStep 1044771 = 1567157) B1567157
theorem B1569059 : Blo 1044610 1569059 := bstep (se 1 (by rfl) ⟨1176794, by rfl⟩ : syracuseStep 1569059 = 2353589) B2353589
theorem B1044787 : Blo 1044610 1044787 := bstep (se 1 (by rfl) ⟨783590, by rfl⟩ : syracuseStep 1044787 = 1567181) B1567181
theorem B1569089 : Blo 1044610 1569089 := bstep (se 2 (by rfl) ⟨588408, by rfl⟩ : syracuseStep 1569089 = 1176817) B1176817
theorem B1044803 : Blo 1044610 1044803 := bstep (se 1 (by rfl) ⟨783602, by rfl⟩ : syracuseStep 1044803 = 1567205) B1567205
theorem B1044819 : Blo 1044610 1044819 := bstep (se 1 (by rfl) ⟨783614, by rfl⟩ : syracuseStep 1044819 = 1567229) B1567229
theorem B1569107 : Blo 1044610 1569107 := bstep (se 1 (by rfl) ⟨1176830, by rfl⟩ : syracuseStep 1569107 = 2353661) B2353661
theorem B1044835 : Blo 1044610 1044835 := bstep (se 1 (by rfl) ⟨783626, by rfl⟩ : syracuseStep 1044835 = 1567253) B1567253
theorem B2978147 : Blo 1044610 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B1569137 : Blo 1044610 1569137 := bstep (se 2 (by rfl) ⟨588426, by rfl⟩ : syracuseStep 1569137 = 1176853) B1176853
theorem B2355569 : Blo 1044610 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B1044851 : Blo 1044610 1044851 := bstep (se 1 (by rfl) ⟨783638, by rfl⟩ : syracuseStep 1044851 = 1567277) B1567277
theorem B3535217 : Blo 1044610 3535217 := bstep (se 2 (by rfl) ⟨1325706, by rfl⟩ : syracuseStep 3535217 = 2651413) B2651413
theorem B5304689 : Blo 1044610 5304689 := bstep (se 2 (by rfl) ⟨1989258, by rfl⟩ : syracuseStep 5304689 = 3978517) B3978517
theorem B1044867 : Blo 1044610 1044867 := bstep (se 1 (by rfl) ⟨783650, by rfl⟩ : syracuseStep 1044867 = 1567301) B1567301
theorem B1569155 : Blo 1044610 1569155 := bstep (se 1 (by rfl) ⟨1176866, by rfl⟩ : syracuseStep 1569155 = 2353733) B2353733
theorem B2355587 : Blo 1044610 2355587 := bstep (se 1 (by rfl) ⟨1766690, by rfl⟩ : syracuseStep 2355587 = 3533381) B3533381
theorem B1044883 : Blo 1044610 1044883 := bstep (se 1 (by rfl) ⟨783662, by rfl⟩ : syracuseStep 1044883 = 1567325) B1567325
theorem B1569185 : Blo 1044610 1569185 := bstep (se 2 (by rfl) ⟨588444, by rfl⟩ : syracuseStep 1569185 = 1176889) B1176889
theorem B1765793 : Blo 1044610 1765793 := bstep (se 2 (by rfl) ⟨662172, by rfl⟩ : syracuseStep 1765793 = 1324345) B1324345
theorem B1044899 : Blo 1044610 1044899 := bstep (se 1 (by rfl) ⟨783674, by rfl⟩ : syracuseStep 1044899 = 1567349) B1567349
theorem B1175971 : Blo 1044610 1175971 := bstep (se 1 (by rfl) ⟨881978, by rfl⟩ : syracuseStep 1175971 = 1763957) B1763957
theorem B1044915 : Blo 1044610 1044915 := bstep (se 1 (by rfl) ⟨783686, by rfl⟩ : syracuseStep 1044915 = 1567373) B1567373
theorem B1569203 : Blo 1044610 1569203 := bstep (se 1 (by rfl) ⟨1176902, by rfl⟩ : syracuseStep 1569203 = 2353805) B2353805
theorem B1044931 : Blo 1044610 1044931 := bstep (se 1 (by rfl) ⟨783698, by rfl⟩ : syracuseStep 1044931 = 1567397) B1567397
theorem B1569233 : Blo 1044610 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B1044947 : Blo 1044610 1044947 := bstep (se 1 (by rfl) ⟨783710, by rfl⟩ : syracuseStep 1044947 = 1567421) B1567421
theorem B1044963 : Blo 1044610 1044963 := bstep (se 1 (by rfl) ⟨783722, by rfl⟩ : syracuseStep 1044963 = 1567445) B1567445
theorem B1569251 : Blo 1044610 1569251 := bstep (se 1 (by rfl) ⟨1176938, by rfl⟩ : syracuseStep 1569251 = 2353877) B2353877
theorem B1044979 : Blo 1044610 1044979 := bstep (se 1 (by rfl) ⟨783734, by rfl⟩ : syracuseStep 1044979 = 1567469) B1567469
theorem B1569281 : Blo 1044610 1569281 := bstep (se 2 (by rfl) ⟨588480, by rfl⟩ : syracuseStep 1569281 = 1176961) B1176961
theorem B1044995 : Blo 1044610 1044995 := bstep (se 1 (by rfl) ⟨783746, by rfl⟩ : syracuseStep 1044995 = 1567493) B1567493
theorem B1045011 : Blo 1044610 1045011 := bstep (se 1 (by rfl) ⟨783758, by rfl⟩ : syracuseStep 1045011 = 1567517) B1567517
theorem B1569299 : Blo 1044610 1569299 := bstep (se 1 (by rfl) ⟨1176974, by rfl⟩ : syracuseStep 1569299 = 2353949) B2353949
theorem B1765921 : Blo 1044610 1765921 := bstep (se 2 (by rfl) ⟨662220, by rfl⟩ : syracuseStep 1765921 = 1324441) B1324441
theorem B1045027 : Blo 1044610 1045027 := bstep (se 1 (by rfl) ⟨783770, by rfl⟩ : syracuseStep 1045027 = 1567541) B1567541
theorem B1569329 : Blo 1044610 1569329 := bstep (se 2 (by rfl) ⟨588498, by rfl⟩ : syracuseStep 1569329 = 1176997) B1176997
theorem B1045043 : Blo 1044610 1045043 := bstep (se 1 (by rfl) ⟨783782, by rfl⟩ : syracuseStep 1045043 = 1567565) B1567565
theorem B1176115 : Blo 1044610 1176115 := bstep (se 1 (by rfl) ⟨882086, by rfl⟩ : syracuseStep 1176115 = 1764173) B1764173
theorem B1045059 : Blo 1044610 1045059 := bstep (se 1 (by rfl) ⟨783794, by rfl⟩ : syracuseStep 1045059 = 1567589) B1567589
theorem B1569347 : Blo 1044610 1569347 := bstep (se 1 (by rfl) ⟨1177010, by rfl⟩ : syracuseStep 1569347 = 2354021) B2354021
theorem B1765955 : Blo 1044610 1765955 := bstep (se 1 (by rfl) ⟨1324466, by rfl⟩ : syracuseStep 1765955 = 2648933) B2648933
theorem B1045075 : Blo 1044610 1045075 := bstep (se 1 (by rfl) ⟨783806, by rfl⟩ : syracuseStep 1045075 = 1567613) B1567613
theorem B1569377 : Blo 1044610 1569377 := bstep (se 2 (by rfl) ⟨588516, by rfl⟩ : syracuseStep 1569377 = 1177033) B1177033
theorem B1045091 : Blo 1044610 1045091 := bstep (se 1 (by rfl) ⟨783818, by rfl⟩ : syracuseStep 1045091 = 1567637) B1567637
theorem B1045107 : Blo 1044610 1045107 := bstep (se 1 (by rfl) ⟨783830, by rfl⟩ : syracuseStep 1045107 = 1567661) B1567661
theorem B1569395 : Blo 1044610 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B1045123 : Blo 1044610 1045123 := bstep (se 1 (by rfl) ⟨783842, by rfl⟩ : syracuseStep 1045123 = 1567685) B1567685
theorem B1569425 : Blo 1044610 1569425 := bstep (se 2 (by rfl) ⟨588534, by rfl⟩ : syracuseStep 1569425 = 1177069) B1177069
theorem B2355857 : Blo 1044610 2355857 := bstep (se 2 (by rfl) ⟨883446, by rfl⟩ : syracuseStep 2355857 = 1766893) B1766893
theorem B1045139 : Blo 1044610 1045139 := bstep (se 1 (by rfl) ⟨783854, by rfl⟩ : syracuseStep 1045139 = 1567709) B1567709
theorem B1045155 : Blo 1044610 1045155 := bstep (se 1 (by rfl) ⟨783866, by rfl⟩ : syracuseStep 1045155 = 1567733) B1567733
theorem B1569443 : Blo 1044610 1569443 := bstep (se 1 (by rfl) ⟨1177082, by rfl⟩ : syracuseStep 1569443 = 2354165) B2354165
theorem B2355875 : Blo 1044610 2355875 := bstep (se 1 (by rfl) ⟨1766906, by rfl⟩ : syracuseStep 2355875 = 3533813) B3533813
theorem B1045171 : Blo 1044610 1045171 := bstep (se 1 (by rfl) ⟨783878, by rfl⟩ : syracuseStep 1045171 = 1567757) B1567757
theorem B1569473 : Blo 1044610 1569473 := bstep (se 2 (by rfl) ⟨588552, by rfl⟩ : syracuseStep 1569473 = 1177105) B1177105
theorem B1045187 : Blo 1044610 1045187 := bstep (se 1 (by rfl) ⟨783890, by rfl⟩ : syracuseStep 1045187 = 1567781) B1567781
theorem B1176259 : Blo 1044610 1176259 := bstep (se 1 (by rfl) ⟨882194, by rfl⟩ : syracuseStep 1176259 = 1764389) B1764389
theorem B1766083 : Blo 1044610 1766083 := bstep (se 1 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 1766083 = 2649125) B2649125
theorem B1045203 : Blo 1044610 1045203 := bstep (se 1 (by rfl) ⟨783902, by rfl⟩ : syracuseStep 1045203 = 1567805) B1567805
theorem B1569491 : Blo 1044610 1569491 := bstep (se 1 (by rfl) ⟨1177118, by rfl⟩ : syracuseStep 1569491 = 2354237) B2354237
theorem B1045219 : Blo 1044610 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B1569521 : Blo 1044610 1569521 := bstep (se 2 (by rfl) ⟨588570, by rfl⟩ : syracuseStep 1569521 = 1177141) B1177141
theorem B1045235 : Blo 1044610 1045235 := bstep (se 1 (by rfl) ⟨783926, by rfl⟩ : syracuseStep 1045235 = 1567853) B1567853
theorem B1045251 : Blo 1044610 1045251 := bstep (se 1 (by rfl) ⟨783938, by rfl⟩ : syracuseStep 1045251 = 1567877) B1567877
theorem B1569539 : Blo 1044610 1569539 := bstep (se 1 (by rfl) ⟨1177154, by rfl⟩ : syracuseStep 1569539 = 2354309) B2354309
theorem B1045267 : Blo 1044610 1045267 := bstep (se 1 (by rfl) ⟨783950, by rfl⟩ : syracuseStep 1045267 = 1567901) B1567901
theorem B1569569 : Blo 1044610 1569569 := bstep (se 2 (by rfl) ⟨588588, by rfl⟩ : syracuseStep 1569569 = 1177177) B1177177
theorem B1045283 : Blo 1044610 1045283 := bstep (se 1 (by rfl) ⟨783962, by rfl⟩ : syracuseStep 1045283 = 1567925) B1567925
theorem B1045299 : Blo 1044610 1045299 := bstep (se 1 (by rfl) ⟨783974, by rfl⟩ : syracuseStep 1045299 = 1567949) B1567949
theorem B1569587 : Blo 1044610 1569587 := bstep (se 1 (by rfl) ⟨1177190, by rfl⟩ : syracuseStep 1569587 = 2354381) B2354381
theorem B1045315 : Blo 1044610 1045315 := bstep (se 1 (by rfl) ⟨783986, by rfl⟩ : syracuseStep 1045315 = 1567973) B1567973
theorem B1569617 : Blo 1044610 1569617 := bstep (se 2 (by rfl) ⟨588606, by rfl⟩ : syracuseStep 1569617 = 1177213) B1177213
theorem B1766225 : Blo 1044610 1766225 := bstep (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) B1324669
theorem B1045331 : Blo 1044610 1045331 := bstep (se 1 (by rfl) ⟨783998, by rfl⟩ : syracuseStep 1045331 = 1567997) B1567997
theorem B1176403 : Blo 1044610 1176403 := bstep (se 1 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 1176403 = 1764605) B1764605
theorem B1045347 : Blo 1044610 1045347 := bstep (se 1 (by rfl) ⟨784010, by rfl⟩ : syracuseStep 1045347 = 1568021) B1568021
theorem B1569635 : Blo 1044610 1569635 := bstep (se 1 (by rfl) ⟨1177226, by rfl⟩ : syracuseStep 1569635 = 2354453) B2354453
theorem B6714211 : Blo 1044610 6714211 := bstep (se 1 (by rfl) ⟨5035658, by rfl⟩ : syracuseStep 6714211 = 10071317) B10071317
theorem B1045363 : Blo 1044610 1045363 := bstep (se 1 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 1045363 = 1568045) B1568045
theorem B1569665 : Blo 1044610 1569665 := bstep (se 2 (by rfl) ⟨588624, by rfl⟩ : syracuseStep 1569665 = 1177249) B1177249
theorem B1045379 : Blo 1044610 1045379 := bstep (se 1 (by rfl) ⟨784034, by rfl⟩ : syracuseStep 1045379 = 1568069) B1568069
theorem B3535757 : Blo 1044610 3535757 := bstep (se 3 (by rfl) ⟨662954, by rfl⟩ : syracuseStep 3535757 = 1325909) B1325909
theorem B1045395 : Blo 1044610 1045395 := bstep (se 1 (by rfl) ⟨784046, by rfl⟩ : syracuseStep 1045395 = 1568093) B1568093
theorem B1569683 : Blo 1044610 1569683 := bstep (se 1 (by rfl) ⟨1177262, by rfl⟩ : syracuseStep 1569683 = 2354525) B2354525
theorem B1045411 : Blo 1044610 1045411 := bstep (se 1 (by rfl) ⟨784058, by rfl⟩ : syracuseStep 1045411 = 1568117) B1568117
theorem B2356145 : Blo 1044610 2356145 := bstep (se 2 (by rfl) ⟨883554, by rfl⟩ : syracuseStep 2356145 = 1767109) B1767109
theorem B1569713 : Blo 1044610 1569713 := bstep (se 2 (by rfl) ⟨588642, by rfl⟩ : syracuseStep 1569713 = 1177285) B1177285
theorem B1045427 : Blo 1044610 1045427 := bstep (se 1 (by rfl) ⟨784070, by rfl⟩ : syracuseStep 1045427 = 1568141) B1568141
theorem B1045443 : Blo 1044610 1045443 := bstep (se 1 (by rfl) ⟨784082, by rfl⟩ : syracuseStep 1045443 = 1568165) B1568165
theorem B1569731 : Blo 1044610 1569731 := bstep (se 1 (by rfl) ⟨1177298, by rfl⟩ : syracuseStep 1569731 = 2354597) B2354597
theorem B2356163 : Blo 1044610 2356163 := bstep (se 1 (by rfl) ⟨1767122, by rfl⟩ : syracuseStep 2356163 = 3534245) B3534245
theorem B3535811 : Blo 1044610 3535811 := bstep (se 1 (by rfl) ⟨2651858, by rfl⟩ : syracuseStep 3535811 = 5303717) B5303717
theorem B1766353 : Blo 1044610 1766353 := bstep (se 2 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 1766353 = 1324765) B1324765
theorem B1045459 : Blo 1044610 1045459 := bstep (se 1 (by rfl) ⟨784094, by rfl⟩ : syracuseStep 1045459 = 1568189) B1568189
theorem B2651089 : Blo 1044610 2651089 := bstep (se 2 (by rfl) ⟨994158, by rfl⟩ : syracuseStep 2651089 = 1988317) B1988317
theorem B1569761 : Blo 1044610 1569761 := bstep (se 2 (by rfl) ⟨588660, by rfl⟩ : syracuseStep 1569761 = 1177321) B1177321
theorem B1045475 : Blo 1044610 1045475 := bstep (se 1 (by rfl) ⟨784106, by rfl⟩ : syracuseStep 1045475 = 1568213) B1568213
theorem B1176547 : Blo 1044610 1176547 := bstep (se 1 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 1176547 = 1764821) B1764821
theorem B1045491 : Blo 1044610 1045491 := bstep (se 1 (by rfl) ⟨784118, by rfl⟩ : syracuseStep 1045491 = 1568237) B1568237
theorem B1569779 : Blo 1044610 1569779 := bstep (se 1 (by rfl) ⟨1177334, by rfl⟩ : syracuseStep 1569779 = 2354669) B2354669
theorem B1766387 : Blo 1044610 1766387 := bstep (se 1 (by rfl) ⟨1324790, by rfl⟩ : syracuseStep 1766387 = 2649581) B2649581
theorem B1045507 : Blo 1044610 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B1569809 : Blo 1044610 1569809 := bstep (se 2 (by rfl) ⟨588678, by rfl⟩ : syracuseStep 1569809 = 1177357) B1177357
theorem B1045523 : Blo 1044610 1045523 := bstep (se 1 (by rfl) ⟨784142, by rfl⟩ : syracuseStep 1045523 = 1568285) B1568285
theorem B1045539 : Blo 1044610 1045539 := bstep (se 1 (by rfl) ⟨784154, by rfl⟩ : syracuseStep 1045539 = 1568309) B1568309
theorem B1569827 : Blo 1044610 1569827 := bstep (se 1 (by rfl) ⟨1177370, by rfl⟩ : syracuseStep 1569827 = 2354741) B2354741
theorem B1045555 : Blo 1044610 1045555 := bstep (se 1 (by rfl) ⟨784166, by rfl⟩ : syracuseStep 1045555 = 1568333) B1568333
theorem B1569857 : Blo 1044610 1569857 := bstep (se 2 (by rfl) ⟨588696, by rfl⟩ : syracuseStep 1569857 = 1177393) B1177393
theorem B1045571 : Blo 1044610 1045571 := bstep (se 1 (by rfl) ⟨784178, by rfl⟩ : syracuseStep 1045571 = 1568357) B1568357
theorem B1045587 : Blo 1044610 1045587 := bstep (se 1 (by rfl) ⟨784190, by rfl⟩ : syracuseStep 1045587 = 1568381) B1568381
theorem B1569875 : Blo 1044610 1569875 := bstep (se 1 (by rfl) ⟨1177406, by rfl⟩ : syracuseStep 1569875 = 2354813) B2354813
theorem B1045603 : Blo 1044610 1045603 := bstep (se 1 (by rfl) ⟨784202, by rfl⟩ : syracuseStep 1045603 = 1568405) B1568405
theorem B1569905 : Blo 1044610 1569905 := bstep (se 2 (by rfl) ⟨588714, by rfl⟩ : syracuseStep 1569905 = 1177429) B1177429
theorem B1045619 : Blo 1044610 1045619 := bstep (se 1 (by rfl) ⟨784214, by rfl⟩ : syracuseStep 1045619 = 1568429) B1568429
theorem B1176691 : Blo 1044610 1176691 := bstep (se 1 (by rfl) ⟨882518, by rfl⟩ : syracuseStep 1176691 = 1765037) B1765037
theorem B1766515 : Blo 1044610 1766515 := bstep (se 1 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 1766515 = 2649773) B2649773
theorem B1045635 : Blo 1044610 1045635 := bstep (se 1 (by rfl) ⟨784226, by rfl⟩ : syracuseStep 1045635 = 1568453) B1568453
theorem B1569923 : Blo 1044610 1569923 := bstep (se 1 (by rfl) ⟨1177442, by rfl⟩ : syracuseStep 1569923 = 2354885) B2354885
theorem B2978957 : Blo 1044610 2978957 := bstep (se 3 (by rfl) ⟨558554, by rfl⟩ : syracuseStep 2978957 = 1117109) B1117109
theorem B1045651 : Blo 1044610 1045651 := bstep (se 1 (by rfl) ⟨784238, by rfl⟩ : syracuseStep 1045651 = 1568477) B1568477
theorem B1569953 : Blo 1044610 1569953 := bstep (se 2 (by rfl) ⟨588732, by rfl⟩ : syracuseStep 1569953 = 1177465) B1177465
theorem B1045667 : Blo 1044610 1045667 := bstep (se 1 (by rfl) ⟨784250, by rfl⟩ : syracuseStep 1045667 = 1568501) B1568501
theorem B1045683 : Blo 1044610 1045683 := bstep (se 1 (by rfl) ⟨784262, by rfl⟩ : syracuseStep 1045683 = 1568525) B1568525
theorem B1569971 : Blo 1044610 1569971 := bstep (se 1 (by rfl) ⟨1177478, by rfl⟩ : syracuseStep 1569971 = 2354957) B2354957
theorem B1045699 : Blo 1044610 1045699 := bstep (se 1 (by rfl) ⟨784274, by rfl⟩ : syracuseStep 1045699 = 1568549) B1568549
theorem B1570001 : Blo 1044610 1570001 := bstep (se 2 (by rfl) ⟨588750, by rfl⟩ : syracuseStep 1570001 = 1177501) B1177501
theorem B2356433 : Blo 1044610 2356433 := bstep (se 2 (by rfl) ⟨883662, by rfl⟩ : syracuseStep 2356433 = 1767325) B1767325
theorem B1045715 : Blo 1044610 1045715 := bstep (se 1 (by rfl) ⟨784286, by rfl⟩ : syracuseStep 1045715 = 1568573) B1568573
theorem B3536081 : Blo 1044610 3536081 := bstep (se 2 (by rfl) ⟨1326030, by rfl⟩ : syracuseStep 3536081 = 2652061) B2652061
theorem B1045731 : Blo 1044610 1045731 := bstep (se 1 (by rfl) ⟨784298, by rfl⟩ : syracuseStep 1045731 = 1568597) B1568597
theorem B1570019 : Blo 1044610 1570019 := bstep (se 1 (by rfl) ⟨1177514, by rfl⟩ : syracuseStep 1570019 = 2355029) B2355029
theorem B2356451 : Blo 1044610 2356451 := bstep (se 1 (by rfl) ⟨1767338, by rfl⟩ : syracuseStep 2356451 = 3534677) B3534677
theorem B2651363 : Blo 1044610 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B1045747 : Blo 1044610 1045747 := bstep (se 1 (by rfl) ⟨784310, by rfl⟩ : syracuseStep 1045747 = 1568621) B1568621
theorem B1570049 : Blo 1044610 1570049 := bstep (se 2 (by rfl) ⟨588768, by rfl⟩ : syracuseStep 1570049 = 1177537) B1177537
theorem B1766657 : Blo 1044610 1766657 := bstep (se 2 (by rfl) ⟨662496, by rfl⟩ : syracuseStep 1766657 = 1324993) B1324993
theorem B1045763 : Blo 1044610 1045763 := bstep (se 1 (by rfl) ⟨784322, by rfl⟩ : syracuseStep 1045763 = 1568645) B1568645
theorem B1176835 : Blo 1044610 1176835 := bstep (se 1 (by rfl) ⟨882626, by rfl⟩ : syracuseStep 1176835 = 1765253) B1765253
theorem B1045779 : Blo 1044610 1045779 := bstep (se 1 (by rfl) ⟨784334, by rfl⟩ : syracuseStep 1045779 = 1568669) B1568669
theorem B1570067 : Blo 1044610 1570067 := bstep (se 1 (by rfl) ⟨1177550, by rfl⟩ : syracuseStep 1570067 = 2355101) B2355101
theorem B1045795 : Blo 1044610 1045795 := bstep (se 1 (by rfl) ⟨784346, by rfl⟩ : syracuseStep 1045795 = 1568693) B1568693
theorem B1570097 : Blo 1044610 1570097 := bstep (se 2 (by rfl) ⟨588786, by rfl⟩ : syracuseStep 1570097 = 1177573) B1177573
theorem B1045811 : Blo 1044610 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B1045827 : Blo 1044610 1045827 := bstep (se 1 (by rfl) ⟨784370, by rfl⟩ : syracuseStep 1045827 = 1568741) B1568741
theorem B2979139 : Blo 1044610 2979139 := bstep (se 1 (by rfl) ⟨2234354, by rfl⟩ : syracuseStep 2979139 = 4468709) B4468709
theorem B1570115 : Blo 1044610 1570115 := bstep (se 1 (by rfl) ⟨1177586, by rfl⟩ : syracuseStep 1570115 = 2355173) B2355173
theorem B1045843 : Blo 1044610 1045843 := bstep (se 1 (by rfl) ⟨784382, by rfl⟩ : syracuseStep 1045843 = 1568765) B1568765
theorem B1570145 : Blo 1044610 1570145 := bstep (se 2 (by rfl) ⟨588804, by rfl⟩ : syracuseStep 1570145 = 1177609) B1177609
theorem B1045859 : Blo 1044610 1045859 := bstep (se 1 (by rfl) ⟨784394, by rfl⟩ : syracuseStep 1045859 = 1568789) B1568789
theorem B1045875 : Blo 1044610 1045875 := bstep (se 1 (by rfl) ⟨784406, by rfl⟩ : syracuseStep 1045875 = 1568813) B1568813
theorem B1570163 : Blo 1044610 1570163 := bstep (se 1 (by rfl) ⟨1177622, by rfl⟩ : syracuseStep 1570163 = 2355245) B2355245
theorem B1766785 : Blo 1044610 1766785 := bstep (se 2 (by rfl) ⟨662544, by rfl⟩ : syracuseStep 1766785 = 1325089) B1325089
theorem B1045891 : Blo 1044610 1045891 := bstep (se 1 (by rfl) ⟨784418, by rfl⟩ : syracuseStep 1045891 = 1568837) B1568837
theorem B1570193 : Blo 1044610 1570193 := bstep (se 2 (by rfl) ⟨588822, by rfl⟩ : syracuseStep 1570193 = 1177645) B1177645
theorem B1045907 : Blo 1044610 1045907 := bstep (se 1 (by rfl) ⟨784430, by rfl⟩ : syracuseStep 1045907 = 1568861) B1568861
theorem B1176979 : Blo 1044610 1176979 := bstep (se 1 (by rfl) ⟨882734, by rfl⟩ : syracuseStep 1176979 = 1765469) B1765469
theorem B2651555 : Blo 1044610 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B1045923 : Blo 1044610 1045923 := bstep (se 1 (by rfl) ⟨784442, by rfl⟩ : syracuseStep 1045923 = 1568885) B1568885
theorem B1570211 : Blo 1044610 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B1766819 : Blo 1044610 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B1045939 : Blo 1044610 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B1570241 : Blo 1044610 1570241 := bstep (se 2 (by rfl) ⟨588840, by rfl⟩ : syracuseStep 1570241 = 1177681) B1177681
theorem B1045955 : Blo 1044610 1045955 := bstep (se 1 (by rfl) ⟨784466, by rfl⟩ : syracuseStep 1045955 = 1568933) B1568933
theorem B1045971 : Blo 1044610 1045971 := bstep (se 1 (by rfl) ⟨784478, by rfl⟩ : syracuseStep 1045971 = 1568957) B1568957
theorem B1570259 : Blo 1044610 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B1045987 : Blo 1044610 1045987 := bstep (se 1 (by rfl) ⟨784490, by rfl⟩ : syracuseStep 1045987 = 1568981) B1568981
theorem B2356721 : Blo 1044610 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B1570289 : Blo 1044610 1570289 := bstep (se 2 (by rfl) ⟨588858, by rfl⟩ : syracuseStep 1570289 = 1177717) B1177717
theorem B1046003 : Blo 1044610 1046003 := bstep (se 1 (by rfl) ⟨784502, by rfl⟩ : syracuseStep 1046003 = 1569005) B1569005
theorem B1046019 : Blo 1044610 1046019 := bstep (se 1 (by rfl) ⟨784514, by rfl⟩ : syracuseStep 1046019 = 1569029) B1569029
theorem B1570307 : Blo 1044610 1570307 := bstep (se 1 (by rfl) ⟨1177730, by rfl⟩ : syracuseStep 1570307 = 2355461) B2355461
theorem B2356739 : Blo 1044610 2356739 := bstep (se 1 (by rfl) ⟨1767554, by rfl⟩ : syracuseStep 2356739 = 3535109) B3535109
theorem B1046035 : Blo 1044610 1046035 := bstep (se 1 (by rfl) ⟨784526, by rfl⟩ : syracuseStep 1046035 = 1569053) B1569053
theorem B1570337 : Blo 1044610 1570337 := bstep (se 2 (by rfl) ⟨588876, by rfl⟩ : syracuseStep 1570337 = 1177753) B1177753
theorem B1046051 : Blo 1044610 1046051 := bstep (se 1 (by rfl) ⟨784538, by rfl⟩ : syracuseStep 1046051 = 1569077) B1569077
theorem B1177123 : Blo 1044610 1177123 := bstep (se 1 (by rfl) ⟨882842, by rfl⟩ : syracuseStep 1177123 = 1765685) B1765685
theorem B1766947 : Blo 1044610 1766947 := bstep (se 1 (by rfl) ⟨1325210, by rfl⟩ : syracuseStep 1766947 = 2650421) B2650421
theorem B1046067 : Blo 1044610 1046067 := bstep (se 1 (by rfl) ⟨784550, by rfl⟩ : syracuseStep 1046067 = 1569101) B1569101
theorem B1570355 : Blo 1044610 1570355 := bstep (se 1 (by rfl) ⟨1177766, by rfl⟩ : syracuseStep 1570355 = 2355533) B2355533
theorem B1046083 : Blo 1044610 1046083 := bstep (se 1 (by rfl) ⟨784562, by rfl⟩ : syracuseStep 1046083 = 1569125) B1569125
theorem B1570385 : Blo 1044610 1570385 := bstep (se 2 (by rfl) ⟨588894, by rfl⟩ : syracuseStep 1570385 = 1177789) B1177789
theorem B1046099 : Blo 1044610 1046099 := bstep (se 1 (by rfl) ⟨784574, by rfl⟩ : syracuseStep 1046099 = 1569149) B1569149
theorem B1046115 : Blo 1044610 1046115 := bstep (se 1 (by rfl) ⟨784586, by rfl⟩ : syracuseStep 1046115 = 1569173) B1569173
theorem B1570403 : Blo 1044610 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B1046131 : Blo 1044610 1046131 := bstep (se 1 (by rfl) ⟨784598, by rfl⟩ : syracuseStep 1046131 = 1569197) B1569197
theorem B1570433 : Blo 1044610 1570433 := bstep (se 2 (by rfl) ⟨588912, by rfl⟩ : syracuseStep 1570433 = 1177825) B1177825
theorem B1046147 : Blo 1044610 1046147 := bstep (se 1 (by rfl) ⟨784610, by rfl⟩ : syracuseStep 1046147 = 1569221) B1569221
theorem B1046163 : Blo 1044610 1046163 := bstep (se 1 (by rfl) ⟨784622, by rfl⟩ : syracuseStep 1046163 = 1569245) B1569245
theorem B1570451 : Blo 1044610 1570451 := bstep (se 1 (by rfl) ⟨1177838, by rfl⟩ : syracuseStep 1570451 = 2355677) B2355677
theorem B1046179 : Blo 1044610 1046179 := bstep (se 1 (by rfl) ⟨784634, by rfl⟩ : syracuseStep 1046179 = 1569269) B1569269
theorem B1570481 : Blo 1044610 1570481 := bstep (se 2 (by rfl) ⟨588930, by rfl⟩ : syracuseStep 1570481 = 1177861) B1177861
theorem B1767089 : Blo 1044610 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B1046195 : Blo 1044610 1046195 := bstep (se 1 (by rfl) ⟨784646, by rfl⟩ : syracuseStep 1046195 = 1569293) B1569293
theorem B1177267 : Blo 1044610 1177267 := bstep (se 1 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 1177267 = 1765901) B1765901
theorem B1046211 : Blo 1044610 1046211 := bstep (se 1 (by rfl) ⟨784658, by rfl⟩ : syracuseStep 1046211 = 1569317) B1569317
theorem B1570499 : Blo 1044610 1570499 := bstep (se 1 (by rfl) ⟨1177874, by rfl⟩ : syracuseStep 1570499 = 2355749) B2355749
theorem B1046227 : Blo 1044610 1046227 := bstep (se 1 (by rfl) ⟨784670, by rfl⟩ : syracuseStep 1046227 = 1569341) B1569341
theorem B1570529 : Blo 1044610 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B1046243 : Blo 1044610 1046243 := bstep (se 1 (by rfl) ⟨784682, by rfl⟩ : syracuseStep 1046243 = 1569365) B1569365
theorem B3536621 : Blo 1044610 3536621 := bstep (se 3 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 3536621 = 1326233) B1326233
theorem B1046259 : Blo 1044610 1046259 := bstep (se 1 (by rfl) ⟨784694, by rfl⟩ : syracuseStep 1046259 = 1569389) B1569389
theorem B1570547 : Blo 1044610 1570547 := bstep (se 1 (by rfl) ⟨1177910, by rfl⟩ : syracuseStep 1570547 = 2355821) B2355821
theorem B1046275 : Blo 1044610 1046275 := bstep (se 1 (by rfl) ⟨784706, by rfl⟩ : syracuseStep 1046275 = 1569413) B1569413
theorem B2357009 : Blo 1044610 2357009 := bstep (se 2 (by rfl) ⟨883878, by rfl⟩ : syracuseStep 2357009 = 1767757) B1767757
theorem B1570577 : Blo 1044610 1570577 := bstep (se 2 (by rfl) ⟨588966, by rfl⟩ : syracuseStep 1570577 = 1177933) B1177933
theorem B1046291 : Blo 1044610 1046291 := bstep (se 1 (by rfl) ⟨784718, by rfl⟩ : syracuseStep 1046291 = 1569437) B1569437
theorem B3536675 : Blo 1044610 3536675 := bstep (se 1 (by rfl) ⟨2652506, by rfl⟩ : syracuseStep 3536675 = 5305013) B5305013
theorem B1046307 : Blo 1044610 1046307 := bstep (se 1 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 1046307 = 1569461) B1569461
theorem B1570595 : Blo 1044610 1570595 := bstep (se 1 (by rfl) ⟨1177946, by rfl⟩ : syracuseStep 1570595 = 2355893) B2355893
theorem B2357027 : Blo 1044610 2357027 := bstep (se 1 (by rfl) ⟨1767770, by rfl⟩ : syracuseStep 2357027 = 3535541) B3535541
theorem B5306147 : Blo 1044610 5306147 := bstep (se 1 (by rfl) ⟨3979610, by rfl⟩ : syracuseStep 5306147 = 7959221) B7959221
theorem B2979629 : Blo 1044610 2979629 := bstep (se 3 (by rfl) ⟨558680, by rfl⟩ : syracuseStep 2979629 = 1117361) B1117361
theorem B1767217 : Blo 1044610 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B1046323 : Blo 1044610 1046323 := bstep (se 1 (by rfl) ⟨784742, by rfl⟩ : syracuseStep 1046323 = 1569485) B1569485
theorem B1570625 : Blo 1044610 1570625 := bstep (se 2 (by rfl) ⟨588984, by rfl⟩ : syracuseStep 1570625 = 1177969) B1177969
theorem B1046339 : Blo 1044610 1046339 := bstep (se 1 (by rfl) ⟨784754, by rfl⟩ : syracuseStep 1046339 = 1569509) B1569509
theorem B1177411 : Blo 1044610 1177411 := bstep (se 1 (by rfl) ⟨883058, by rfl⟩ : syracuseStep 1177411 = 1766117) B1766117
theorem B1767251 : Blo 1044610 1767251 := bstep (se 1 (by rfl) ⟨1325438, by rfl⟩ : syracuseStep 1767251 = 2650877) B2650877
theorem B1275731 : Blo 1044610 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B1046355 : Blo 1044610 1046355 := bstep (se 1 (by rfl) ⟨784766, by rfl⟩ : syracuseStep 1046355 = 1569533) B1569533
theorem B1570643 : Blo 1044610 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B1046371 : Blo 1044610 1046371 := bstep (se 1 (by rfl) ⟨784778, by rfl⟩ : syracuseStep 1046371 = 1569557) B1569557
theorem B1570673 : Blo 1044610 1570673 := bstep (se 2 (by rfl) ⟨589002, by rfl⟩ : syracuseStep 1570673 = 1178005) B1178005
theorem B1046387 : Blo 1044610 1046387 := bstep (se 1 (by rfl) ⟨784790, by rfl⟩ : syracuseStep 1046387 = 1569581) B1569581
theorem B1046403 : Blo 1044610 1046403 := bstep (se 1 (by rfl) ⟨784802, by rfl⟩ : syracuseStep 1046403 = 1569605) B1569605
theorem B1570691 : Blo 1044610 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B1046419 : Blo 1044610 1046419 := bstep (se 1 (by rfl) ⟨784814, by rfl⟩ : syracuseStep 1046419 = 1569629) B1569629
theorem B1570721 : Blo 1044610 1570721 := bstep (se 2 (by rfl) ⟨589020, by rfl⟩ : syracuseStep 1570721 = 1178041) B1178041
theorem B1046435 : Blo 1044610 1046435 := bstep (se 1 (by rfl) ⟨784826, by rfl⟩ : syracuseStep 1046435 = 1569653) B1569653
theorem B1046451 : Blo 1044610 1046451 := bstep (se 1 (by rfl) ⟨784838, by rfl⟩ : syracuseStep 1046451 = 1569677) B1569677
theorem B1570739 : Blo 1044610 1570739 := bstep (se 1 (by rfl) ⟨1178054, by rfl⟩ : syracuseStep 1570739 = 2356109) B2356109
theorem B1046467 : Blo 1044610 1046467 := bstep (se 1 (by rfl) ⟨784850, by rfl⟩ : syracuseStep 1046467 = 1569701) B1569701
theorem B1570769 : Blo 1044610 1570769 := bstep (se 2 (by rfl) ⟨589038, by rfl⟩ : syracuseStep 1570769 = 1178077) B1178077
theorem B1046483 : Blo 1044610 1046483 := bstep (se 1 (by rfl) ⟨784862, by rfl⟩ : syracuseStep 1046483 = 1569725) B1569725
theorem B1177555 : Blo 1044610 1177555 := bstep (se 1 (by rfl) ⟨883166, by rfl⟩ : syracuseStep 1177555 = 1766333) B1766333
theorem B1767379 : Blo 1044610 1767379 := bstep (se 1 (by rfl) ⟨1325534, by rfl⟩ : syracuseStep 1767379 = 2651069) B2651069
theorem B1046499 : Blo 1044610 1046499 := bstep (se 1 (by rfl) ⟨784874, by rfl⟩ : syracuseStep 1046499 = 1569749) B1569749
theorem B1570787 : Blo 1044610 1570787 := bstep (se 1 (by rfl) ⟨1178090, by rfl⟩ : syracuseStep 1570787 = 2356181) B2356181
theorem B1046515 : Blo 1044610 1046515 := bstep (se 1 (by rfl) ⟨784886, by rfl⟩ : syracuseStep 1046515 = 1569773) B1569773
theorem B1570817 : Blo 1044610 1570817 := bstep (se 2 (by rfl) ⟨589056, by rfl⟩ : syracuseStep 1570817 = 1178113) B1178113
theorem B1046531 : Blo 1044610 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B1046547 : Blo 1044610 1046547 := bstep (se 1 (by rfl) ⟨784910, by rfl⟩ : syracuseStep 1046547 = 1569821) B1569821
theorem B1570835 : Blo 1044610 1570835 := bstep (se 1 (by rfl) ⟨1178126, by rfl⟩ : syracuseStep 1570835 = 2356253) B2356253
theorem B1046563 : Blo 1044610 1046563 := bstep (se 1 (by rfl) ⟨784922, by rfl⟩ : syracuseStep 1046563 = 1569845) B1569845
theorem B1570865 : Blo 1044610 1570865 := bstep (se 2 (by rfl) ⟨589074, by rfl⟩ : syracuseStep 1570865 = 1178149) B1178149
theorem B2357297 : Blo 1044610 2357297 := bstep (se 2 (by rfl) ⟨883986, by rfl⟩ : syracuseStep 2357297 = 1767973) B1767973
theorem B1046579 : Blo 1044610 1046579 := bstep (se 1 (by rfl) ⟨784934, by rfl⟩ : syracuseStep 1046579 = 1569869) B1569869
theorem B3536945 : Blo 1044610 3536945 := bstep (se 2 (by rfl) ⟨1326354, by rfl⟩ : syracuseStep 3536945 = 2652709) B2652709
theorem B1046595 : Blo 1044610 1046595 := bstep (se 1 (by rfl) ⟨784946, by rfl⟩ : syracuseStep 1046595 = 1569893) B1569893
theorem B1570883 : Blo 1044610 1570883 := bstep (se 1 (by rfl) ⟨1178162, by rfl⟩ : syracuseStep 1570883 = 2356325) B2356325
theorem B2357315 : Blo 1044610 2357315 := bstep (se 1 (by rfl) ⟨1767986, by rfl⟩ : syracuseStep 2357315 = 3535973) B3535973
theorem B1046611 : Blo 1044610 1046611 := bstep (se 1 (by rfl) ⟨784958, by rfl⟩ : syracuseStep 1046611 = 1569917) B1569917
theorem B1570913 : Blo 1044610 1570913 := bstep (se 2 (by rfl) ⟨589092, by rfl⟩ : syracuseStep 1570913 = 1178185) B1178185
theorem B1767521 : Blo 1044610 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B1046627 : Blo 1044610 1046627 := bstep (se 1 (by rfl) ⟨784970, by rfl⟩ : syracuseStep 1046627 = 1569941) B1569941
theorem B1177699 : Blo 1044610 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B1046643 : Blo 1044610 1046643 := bstep (se 1 (by rfl) ⟨784982, by rfl⟩ : syracuseStep 1046643 = 1569965) B1569965
theorem B1570931 : Blo 1044610 1570931 := bstep (se 1 (by rfl) ⟨1178198, by rfl⟩ : syracuseStep 1570931 = 2356397) B2356397
theorem B1046659 : Blo 1044610 1046659 := bstep (se 1 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 1046659 = 1569989) B1569989
theorem B1570961 : Blo 1044610 1570961 := bstep (se 2 (by rfl) ⟨589110, by rfl⟩ : syracuseStep 1570961 = 1178221) B1178221
theorem B1046675 : Blo 1044610 1046675 := bstep (se 1 (by rfl) ⟨785006, by rfl⟩ : syracuseStep 1046675 = 1570013) B1570013
theorem B1046691 : Blo 1044610 1046691 := bstep (se 1 (by rfl) ⟨785018, by rfl⟩ : syracuseStep 1046691 = 1570037) B1570037
theorem B1570979 : Blo 1044610 1570979 := bstep (se 1 (by rfl) ⟨1178234, by rfl⟩ : syracuseStep 1570979 = 2356469) B2356469
theorem B1046707 : Blo 1044610 1046707 := bstep (se 1 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 1046707 = 1570061) B1570061
theorem B1571009 : Blo 1044610 1571009 := bstep (se 2 (by rfl) ⟨589128, by rfl⟩ : syracuseStep 1571009 = 1178257) B1178257
theorem B1046723 : Blo 1044610 1046723 := bstep (se 1 (by rfl) ⟨785042, by rfl⟩ : syracuseStep 1046723 = 1570085) B1570085
theorem B1046739 : Blo 1044610 1046739 := bstep (se 1 (by rfl) ⟨785054, by rfl⟩ : syracuseStep 1046739 = 1570109) B1570109
theorem B1571027 : Blo 1044610 1571027 := bstep (se 1 (by rfl) ⟨1178270, by rfl⟩ : syracuseStep 1571027 = 2356541) B2356541
theorem B1767649 : Blo 1044610 1767649 := bstep (se 2 (by rfl) ⟨662868, by rfl⟩ : syracuseStep 1767649 = 1325737) B1325737
theorem B1046755 : Blo 1044610 1046755 := bstep (se 1 (by rfl) ⟨785066, by rfl⟩ : syracuseStep 1046755 = 1570133) B1570133
theorem B2586865 : Blo 1044610 2586865 := bstep (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) B1940149
theorem B1571057 : Blo 1044610 1571057 := bstep (se 2 (by rfl) ⟨589146, by rfl⟩ : syracuseStep 1571057 = 1178293) B1178293
theorem B1046771 : Blo 1044610 1046771 := bstep (se 1 (by rfl) ⟨785078, by rfl⟩ : syracuseStep 1046771 = 1570157) B1570157
theorem B1177843 : Blo 1044610 1177843 := bstep (se 1 (by rfl) ⟨883382, by rfl⟩ : syracuseStep 1177843 = 1766765) B1766765
theorem B1046787 : Blo 1044610 1046787 := bstep (se 1 (by rfl) ⟨785090, by rfl⟩ : syracuseStep 1046787 = 1570181) B1570181
theorem B1571075 : Blo 1044610 1571075 := bstep (se 1 (by rfl) ⟨1178306, by rfl⟩ : syracuseStep 1571075 = 2356613) B2356613
theorem B1767683 : Blo 1044610 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B1046803 : Blo 1044610 1046803 := bstep (se 1 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 1046803 = 1570205) B1570205
theorem B1702163 : Blo 1044610 1702163 := bstep (se 1 (by rfl) ⟨1276622, by rfl⟩ : syracuseStep 1702163 = 2553245) B2553245
theorem B1571105 : Blo 1044610 1571105 := bstep (se 2 (by rfl) ⟨589164, by rfl⟩ : syracuseStep 1571105 = 1178329) B1178329
theorem B1046819 : Blo 1044610 1046819 := bstep (se 1 (by rfl) ⟨785114, by rfl⟩ : syracuseStep 1046819 = 1570229) B1570229
theorem B1046835 : Blo 1044610 1046835 := bstep (se 1 (by rfl) ⟨785126, by rfl⟩ : syracuseStep 1046835 = 1570253) B1570253
theorem B1571123 : Blo 1044610 1571123 := bstep (se 1 (by rfl) ⟨1178342, by rfl⟩ : syracuseStep 1571123 = 2356685) B2356685
theorem B1046851 : Blo 1044610 1046851 := bstep (se 1 (by rfl) ⟨785138, by rfl⟩ : syracuseStep 1046851 = 1570277) B1570277
theorem B1571153 : Blo 1044610 1571153 := bstep (se 2 (by rfl) ⟨589182, by rfl⟩ : syracuseStep 1571153 = 1178365) B1178365
theorem B2357585 : Blo 1044610 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B1046867 : Blo 1044610 1046867 := bstep (se 1 (by rfl) ⟨785150, by rfl⟩ : syracuseStep 1046867 = 1570301) B1570301
theorem B2652497 : Blo 1044610 2652497 := bstep (se 2 (by rfl) ⟨994686, by rfl⟩ : syracuseStep 2652497 = 1989373) B1989373
theorem B1046883 : Blo 1044610 1046883 := bstep (se 1 (by rfl) ⟨785162, by rfl⟩ : syracuseStep 1046883 = 1570325) B1570325
theorem B1571171 : Blo 1044610 1571171 := bstep (se 1 (by rfl) ⟨1178378, by rfl⟩ : syracuseStep 1571171 = 2356757) B2356757
theorem B2357603 : Blo 1044610 2357603 := bstep (se 1 (by rfl) ⟨1768202, by rfl⟩ : syracuseStep 2357603 = 3536405) B3536405
theorem B1046899 : Blo 1044610 1046899 := bstep (se 1 (by rfl) ⟨785174, by rfl⟩ : syracuseStep 1046899 = 1570349) B1570349
theorem B1571201 : Blo 1044610 1571201 := bstep (se 2 (by rfl) ⟨589200, by rfl⟩ : syracuseStep 1571201 = 1178401) B1178401
theorem B2652547 : Blo 1044610 2652547 := bstep (se 1 (by rfl) ⟨1989410, by rfl⟩ : syracuseStep 2652547 = 3978821) B3978821
theorem B1767811 : Blo 1044610 1767811 := bstep (se 1 (by rfl) ⟨1325858, by rfl⟩ : syracuseStep 1767811 = 2651717) B2651717
theorem B1046915 : Blo 1044610 1046915 := bstep (se 1 (by rfl) ⟨785186, by rfl⟩ : syracuseStep 1046915 = 1570373) B1570373
theorem B1177987 : Blo 1044610 1177987 := bstep (se 1 (by rfl) ⟨883490, by rfl⟩ : syracuseStep 1177987 = 1766981) B1766981
theorem B1046931 : Blo 1044610 1046931 := bstep (se 1 (by rfl) ⟨785198, by rfl⟩ : syracuseStep 1046931 = 1570397) B1570397
theorem B1571219 : Blo 1044610 1571219 := bstep (se 1 (by rfl) ⟨1178414, by rfl⟩ : syracuseStep 1571219 = 2356829) B2356829
theorem B1046947 : Blo 1044610 1046947 := bstep (se 1 (by rfl) ⟨785210, by rfl⟩ : syracuseStep 1046947 = 1570421) B1570421
theorem B4028849 : Blo 1044610 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B1571249 : Blo 1044610 1571249 := bstep (se 2 (by rfl) ⟨589218, by rfl⟩ : syracuseStep 1571249 = 1178437) B1178437
theorem B1046963 : Blo 1044610 1046963 := bstep (se 1 (by rfl) ⟨785222, by rfl⟩ : syracuseStep 1046963 = 1570445) B1570445
theorem B1046979 : Blo 1044610 1046979 := bstep (se 1 (by rfl) ⟨785234, by rfl⟩ : syracuseStep 1046979 = 1570469) B1570469
theorem B1571267 : Blo 1044610 1571267 := bstep (se 1 (by rfl) ⟨1178450, by rfl⟩ : syracuseStep 1571267 = 2356901) B2356901
theorem B1046995 : Blo 1044610 1046995 := bstep (se 1 (by rfl) ⟨785246, by rfl⟩ : syracuseStep 1046995 = 1570493) B1570493
theorem B1571297 : Blo 1044610 1571297 := bstep (se 2 (by rfl) ⟨589236, by rfl⟩ : syracuseStep 1571297 = 1178473) B1178473
theorem B1047011 : Blo 1044610 1047011 := bstep (se 1 (by rfl) ⟨785258, by rfl⟩ : syracuseStep 1047011 = 1570517) B1570517
theorem B9075185 : Blo 1044610 9075185 := bstep (se 2 (by rfl) ⟨3403194, by rfl⟩ : syracuseStep 9075185 = 6806389) B6806389
theorem B1047027 : Blo 1044610 1047027 := bstep (se 1 (by rfl) ⟨785270, by rfl⟩ : syracuseStep 1047027 = 1570541) B1570541
theorem B1571315 : Blo 1044610 1571315 := bstep (se 1 (by rfl) ⟨1178486, by rfl⟩ : syracuseStep 1571315 = 2356973) B2356973
theorem B1047043 : Blo 1044610 1047043 := bstep (se 1 (by rfl) ⟨785282, by rfl⟩ : syracuseStep 1047043 = 1570565) B1570565
theorem B1571345 : Blo 1044610 1571345 := bstep (se 2 (by rfl) ⟨589254, by rfl⟩ : syracuseStep 1571345 = 1178509) B1178509
theorem B1767953 : Blo 1044610 1767953 := bstep (se 2 (by rfl) ⟨662982, by rfl⟩ : syracuseStep 1767953 = 1325965) B1325965
theorem B1047059 : Blo 1044610 1047059 := bstep (se 1 (by rfl) ⟨785294, by rfl⟩ : syracuseStep 1047059 = 1570589) B1570589
theorem B1178131 : Blo 1044610 1178131 := bstep (se 1 (by rfl) ⟨883598, by rfl⟩ : syracuseStep 1178131 = 1767197) B1767197
theorem B2652689 : Blo 1044610 2652689 := bstep (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) B1989517
theorem B1047075 : Blo 1044610 1047075 := bstep (se 1 (by rfl) ⟨785306, by rfl⟩ : syracuseStep 1047075 = 1570613) B1570613
theorem B1571363 : Blo 1044610 1571363 := bstep (se 1 (by rfl) ⟨1178522, by rfl⟩ : syracuseStep 1571363 = 2357045) B2357045
theorem B1047091 : Blo 1044610 1047091 := bstep (se 1 (by rfl) ⟨785318, by rfl⟩ : syracuseStep 1047091 = 1570637) B1570637
theorem B1571393 : Blo 1044610 1571393 := bstep (se 2 (by rfl) ⟨589272, by rfl⟩ : syracuseStep 1571393 = 1178545) B1178545
theorem B1047107 : Blo 1044610 1047107 := bstep (se 1 (by rfl) ⟨785330, by rfl⟩ : syracuseStep 1047107 = 1570661) B1570661
theorem B3537485 : Blo 1044610 3537485 := bstep (se 3 (by rfl) ⟨663278, by rfl⟩ : syracuseStep 3537485 = 1326557) B1326557
theorem B2390609 : Blo 1044610 2390609 := bstep (se 2 (by rfl) ⟨896478, by rfl⟩ : syracuseStep 2390609 = 1792957) B1792957
theorem B5306957 : Blo 1044610 5306957 := bstep (se 3 (by rfl) ⟨995054, by rfl⟩ : syracuseStep 5306957 = 1990109) B1990109
theorem B1047123 : Blo 1044610 1047123 := bstep (se 1 (by rfl) ⟨785342, by rfl⟩ : syracuseStep 1047123 = 1570685) B1570685
theorem B1571411 : Blo 1044610 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B1047139 : Blo 1044610 1047139 := bstep (se 1 (by rfl) ⟨785354, by rfl⟩ : syracuseStep 1047139 = 1570709) B1570709
theorem B1571441 : Blo 1044610 1571441 := bstep (se 2 (by rfl) ⟨589290, by rfl⟩ : syracuseStep 1571441 = 1178581) B1178581
theorem B2357873 : Blo 1044610 2357873 := bstep (se 2 (by rfl) ⟨884202, by rfl⟩ : syracuseStep 2357873 = 1768405) B1768405
theorem B1047155 : Blo 1044610 1047155 := bstep (se 1 (by rfl) ⟨785366, by rfl⟩ : syracuseStep 1047155 = 1570733) B1570733
theorem B1047171 : Blo 1044610 1047171 := bstep (se 1 (by rfl) ⟨785378, by rfl⟩ : syracuseStep 1047171 = 1570757) B1570757
theorem B1571459 : Blo 1044610 1571459 := bstep (se 1 (by rfl) ⟨1178594, by rfl⟩ : syracuseStep 1571459 = 2357189) B2357189
theorem B2357891 : Blo 1044610 2357891 := bstep (se 1 (by rfl) ⟨1768418, by rfl⟩ : syracuseStep 2357891 = 3536837) B3536837
theorem B3537539 : Blo 1044610 3537539 := bstep (se 1 (by rfl) ⟨2653154, by rfl⟩ : syracuseStep 3537539 = 5306309) B5306309
theorem B1768081 : Blo 1044610 1768081 := bstep (se 2 (by rfl) ⟨663030, by rfl⟩ : syracuseStep 1768081 = 1326061) B1326061
theorem B1047187 : Blo 1044610 1047187 := bstep (se 1 (by rfl) ⟨785390, by rfl⟩ : syracuseStep 1047187 = 1570781) B1570781
theorem B1571489 : Blo 1044610 1571489 := bstep (se 2 (by rfl) ⟨589308, by rfl⟩ : syracuseStep 1571489 = 1178617) B1178617
theorem B1047203 : Blo 1044610 1047203 := bstep (se 1 (by rfl) ⟨785402, by rfl⟩ : syracuseStep 1047203 = 1570805) B1570805
theorem B1178275 : Blo 1044610 1178275 := bstep (se 1 (by rfl) ⟨883706, by rfl⟩ : syracuseStep 1178275 = 1767413) B1767413
theorem B1047219 : Blo 1044610 1047219 := bstep (se 1 (by rfl) ⟨785414, by rfl⟩ : syracuseStep 1047219 = 1570829) B1570829
theorem B1571507 : Blo 1044610 1571507 := bstep (se 1 (by rfl) ⟨1178630, by rfl⟩ : syracuseStep 1571507 = 2357261) B2357261
theorem B1768115 : Blo 1044610 1768115 := bstep (se 1 (by rfl) ⟨1326086, by rfl⟩ : syracuseStep 1768115 = 2652173) B2652173
theorem B1047235 : Blo 1044610 1047235 := bstep (se 1 (by rfl) ⟨785426, by rfl⟩ : syracuseStep 1047235 = 1570853) B1570853
theorem B1571537 : Blo 1044610 1571537 := bstep (se 2 (by rfl) ⟨589326, by rfl⟩ : syracuseStep 1571537 = 1178653) B1178653
theorem B1047251 : Blo 1044610 1047251 := bstep (se 1 (by rfl) ⟨785438, by rfl⟩ : syracuseStep 1047251 = 1570877) B1570877
theorem B1047267 : Blo 1044610 1047267 := bstep (se 1 (by rfl) ⟨785450, by rfl⟩ : syracuseStep 1047267 = 1570901) B1570901
theorem B1571555 : Blo 1044610 1571555 := bstep (se 1 (by rfl) ⟨1178666, by rfl⟩ : syracuseStep 1571555 = 2357333) B2357333
theorem B1047283 : Blo 1044610 1047283 := bstep (se 1 (by rfl) ⟨785462, by rfl⟩ : syracuseStep 1047283 = 1570925) B1570925
theorem B1571585 : Blo 1044610 1571585 := bstep (se 2 (by rfl) ⟨589344, by rfl⟩ : syracuseStep 1571585 = 1178689) B1178689
theorem B1047299 : Blo 1044610 1047299 := bstep (se 1 (by rfl) ⟨785474, by rfl⟩ : syracuseStep 1047299 = 1570949) B1570949
theorem B1047315 : Blo 1044610 1047315 := bstep (se 1 (by rfl) ⟨785486, by rfl⟩ : syracuseStep 1047315 = 1570973) B1570973
theorem B1571603 : Blo 1044610 1571603 := bstep (se 1 (by rfl) ⟨1178702, by rfl⟩ : syracuseStep 1571603 = 2357405) B2357405
theorem B1047331 : Blo 1044610 1047331 := bstep (se 1 (by rfl) ⟨785498, by rfl⟩ : syracuseStep 1047331 = 1570997) B1570997
theorem B1571633 : Blo 1044610 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B6716209 : Blo 1044610 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B1047347 : Blo 1044610 1047347 := bstep (se 1 (by rfl) ⟨785510, by rfl⟩ : syracuseStep 1047347 = 1571021) B1571021
theorem B1178419 : Blo 1044610 1178419 := bstep (se 1 (by rfl) ⟨883814, by rfl⟩ : syracuseStep 1178419 = 1767629) B1767629
theorem B1768243 : Blo 1044610 1768243 := bstep (se 1 (by rfl) ⟨1326182, by rfl⟩ : syracuseStep 1768243 = 2652365) B2652365
theorem B1047363 : Blo 1044610 1047363 := bstep (se 1 (by rfl) ⟨785522, by rfl⟩ : syracuseStep 1047363 = 1571045) B1571045
theorem B1571651 : Blo 1044610 1571651 := bstep (se 1 (by rfl) ⟨1178738, by rfl⟩ : syracuseStep 1571651 = 2357477) B2357477
theorem B5438285 : Blo 1044610 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B1047379 : Blo 1044610 1047379 := bstep (se 1 (by rfl) ⟨785534, by rfl⟩ : syracuseStep 1047379 = 1571069) B1571069
theorem B1571681 : Blo 1044610 1571681 := bstep (se 2 (by rfl) ⟨589380, by rfl⟩ : syracuseStep 1571681 = 1178761) B1178761
theorem B1047395 : Blo 1044610 1047395 := bstep (se 1 (by rfl) ⟨785546, by rfl⟩ : syracuseStep 1047395 = 1571093) B1571093
theorem B1047411 : Blo 1044610 1047411 := bstep (se 1 (by rfl) ⟨785558, by rfl⟩ : syracuseStep 1047411 = 1571117) B1571117
theorem B1571699 : Blo 1044610 1571699 := bstep (se 1 (by rfl) ⟨1178774, by rfl⟩ : syracuseStep 1571699 = 2357549) B2357549
theorem B1047427 : Blo 1044610 1047427 := bstep (se 1 (by rfl) ⟨785570, by rfl⟩ : syracuseStep 1047427 = 1571141) B1571141
theorem B1571729 : Blo 1044610 1571729 := bstep (se 2 (by rfl) ⟨589398, by rfl⟩ : syracuseStep 1571729 = 1178797) B1178797
theorem B2358161 : Blo 1044610 2358161 := bstep (se 2 (by rfl) ⟨884310, by rfl⟩ : syracuseStep 2358161 = 1768621) B1768621
theorem B1047443 : Blo 1044610 1047443 := bstep (se 1 (by rfl) ⟨785582, by rfl⟩ : syracuseStep 1047443 = 1571165) B1571165
theorem B3537809 : Blo 1044610 3537809 := bstep (se 2 (by rfl) ⟨1326678, by rfl⟩ : syracuseStep 3537809 = 2653357) B2653357
theorem B1047459 : Blo 1044610 1047459 := bstep (se 1 (by rfl) ⟨785594, by rfl⟩ : syracuseStep 1047459 = 1571189) B1571189
theorem B1571747 : Blo 1044610 1571747 := bstep (se 1 (by rfl) ⟨1178810, by rfl⟩ : syracuseStep 1571747 = 2357621) B2357621
theorem B2358179 : Blo 1044610 2358179 := bstep (se 1 (by rfl) ⟨1768634, by rfl⟩ : syracuseStep 2358179 = 3537269) B3537269
theorem B5962673 : Blo 1044610 5962673 := bstep (se 2 (by rfl) ⟨2236002, by rfl⟩ : syracuseStep 5962673 = 4472005) B4472005
theorem B1047475 : Blo 1044610 1047475 := bstep (se 1 (by rfl) ⟨785606, by rfl⟩ : syracuseStep 1047475 = 1571213) B1571213
theorem B1571777 : Blo 1044610 1571777 := bstep (se 2 (by rfl) ⟨589416, by rfl⟩ : syracuseStep 1571777 = 1178833) B1178833
theorem B1047491 : Blo 1044610 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B1178563 : Blo 1044610 1178563 := bstep (se 1 (by rfl) ⟨883922, by rfl⟩ : syracuseStep 1178563 = 1767845) B1767845
theorem B1768385 : Blo 1044610 1768385 := bstep (se 2 (by rfl) ⟨663144, by rfl⟩ : syracuseStep 1768385 = 1326289) B1326289
theorem B2980813 : Blo 1044610 2980813 := bstep (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) B1117805
theorem B1047507 : Blo 1044610 1047507 := bstep (se 1 (by rfl) ⟨785630, by rfl⟩ : syracuseStep 1047507 = 1571261) B1571261
theorem B1571795 : Blo 1044610 1571795 := bstep (se 1 (by rfl) ⟨1178846, by rfl⟩ : syracuseStep 1571795 = 2357693) B2357693
theorem B1047523 : Blo 1044610 1047523 := bstep (se 1 (by rfl) ⟨785642, by rfl⟩ : syracuseStep 1047523 = 1571285) B1571285
theorem B1571825 : Blo 1044610 1571825 := bstep (se 2 (by rfl) ⟨589434, by rfl⟩ : syracuseStep 1571825 = 1178869) B1178869
theorem B1047539 : Blo 1044610 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B1047555 : Blo 1044610 1047555 := bstep (se 1 (by rfl) ⟨785666, by rfl⟩ : syracuseStep 1047555 = 1571333) B1571333
theorem B1571843 : Blo 1044610 1571843 := bstep (se 1 (by rfl) ⟨1178882, by rfl⟩ : syracuseStep 1571843 = 2357765) B2357765
theorem B1047571 : Blo 1044610 1047571 := bstep (se 1 (by rfl) ⟨785678, by rfl⟩ : syracuseStep 1047571 = 1571357) B1571357
theorem B1571873 : Blo 1044610 1571873 := bstep (se 2 (by rfl) ⟨589452, by rfl⟩ : syracuseStep 1571873 = 1178905) B1178905
theorem B1047587 : Blo 1044610 1047587 := bstep (se 1 (by rfl) ⟨785690, by rfl⟩ : syracuseStep 1047587 = 1571381) B1571381
theorem B1047603 : Blo 1044610 1047603 := bstep (se 1 (by rfl) ⟨785702, by rfl⟩ : syracuseStep 1047603 = 1571405) B1571405
theorem B1571891 : Blo 1044610 1571891 := bstep (se 1 (by rfl) ⟨1178918, by rfl⟩ : syracuseStep 1571891 = 2357837) B2357837
theorem B1768513 : Blo 1044610 1768513 := bstep (se 2 (by rfl) ⟨663192, by rfl⟩ : syracuseStep 1768513 = 1326385) B1326385
theorem B1047619 : Blo 1044610 1047619 := bstep (se 1 (by rfl) ⟨785714, by rfl⟩ : syracuseStep 1047619 = 1571429) B1571429
theorem B1571921 : Blo 1044610 1571921 := bstep (se 2 (by rfl) ⟨589470, by rfl⟩ : syracuseStep 1571921 = 1178941) B1178941
theorem B1047635 : Blo 1044610 1047635 := bstep (se 1 (by rfl) ⟨785726, by rfl⟩ : syracuseStep 1047635 = 1571453) B1571453
theorem B1178707 : Blo 1044610 1178707 := bstep (se 1 (by rfl) ⟨884030, by rfl⟩ : syracuseStep 1178707 = 1768061) B1768061
theorem B1047651 : Blo 1044610 1047651 := bstep (se 1 (by rfl) ⟨785738, by rfl⟩ : syracuseStep 1047651 = 1571477) B1571477
theorem B1571939 : Blo 1044610 1571939 := bstep (se 1 (by rfl) ⟨1178954, by rfl⟩ : syracuseStep 1571939 = 2357909) B2357909
theorem B1768547 : Blo 1044610 1768547 := bstep (se 1 (by rfl) ⟨1326410, by rfl⟩ : syracuseStep 1768547 = 2652821) B2652821
theorem B1047667 : Blo 1044610 1047667 := bstep (se 1 (by rfl) ⟨785750, by rfl⟩ : syracuseStep 1047667 = 1571501) B1571501
theorem B1571969 : Blo 1044610 1571969 := bstep (se 2 (by rfl) ⟨589488, by rfl⟩ : syracuseStep 1571969 = 1178977) B1178977
theorem B1047683 : Blo 1044610 1047683 := bstep (se 1 (by rfl) ⟨785762, by rfl⟩ : syracuseStep 1047683 = 1571525) B1571525
theorem B1047699 : Blo 1044610 1047699 := bstep (se 1 (by rfl) ⟨785774, by rfl⟩ : syracuseStep 1047699 = 1571549) B1571549
theorem B1571987 : Blo 1044610 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B1047715 : Blo 1044610 1047715 := bstep (se 1 (by rfl) ⟨785786, by rfl⟩ : syracuseStep 1047715 = 1571573) B1571573
theorem B1572017 : Blo 1044610 1572017 := bstep (se 2 (by rfl) ⟨589506, by rfl⟩ : syracuseStep 1572017 = 1179013) B1179013
theorem B2358449 : Blo 1044610 2358449 := bstep (se 2 (by rfl) ⟨884418, by rfl⟩ : syracuseStep 2358449 = 1768837) B1768837
theorem B1047731 : Blo 1044610 1047731 := bstep (se 1 (by rfl) ⟨785798, by rfl⟩ : syracuseStep 1047731 = 1571597) B1571597
theorem B1047747 : Blo 1044610 1047747 := bstep (se 1 (by rfl) ⟨785810, by rfl⟩ : syracuseStep 1047747 = 1571621) B1571621
theorem B1572035 : Blo 1044610 1572035 := bstep (se 1 (by rfl) ⟨1179026, by rfl⟩ : syracuseStep 1572035 = 2358053) B2358053
theorem B2358467 : Blo 1044610 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B3177677 : Blo 1044610 3177677 := bstep (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) B1191629
theorem B1047763 : Blo 1044610 1047763 := bstep (se 1 (by rfl) ⟨785822, by rfl⟩ : syracuseStep 1047763 = 1571645) B1571645
theorem B1572065 : Blo 1044610 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B1047779 : Blo 1044610 1047779 := bstep (se 1 (by rfl) ⟨785834, by rfl⟩ : syracuseStep 1047779 = 1571669) B1571669
theorem B1178851 : Blo 1044610 1178851 := bstep (se 1 (by rfl) ⟨884138, by rfl⟩ : syracuseStep 1178851 = 1768277) B1768277
theorem B1768675 : Blo 1044610 1768675 := bstep (se 1 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 1768675 = 2653013) B2653013
theorem B1047795 : Blo 1044610 1047795 := bstep (se 1 (by rfl) ⟨785846, by rfl⟩ : syracuseStep 1047795 = 1571693) B1571693
theorem B1572083 : Blo 1044610 1572083 := bstep (se 1 (by rfl) ⟨1179062, by rfl⟩ : syracuseStep 1572083 = 2358125) B2358125
theorem B1047811 : Blo 1044610 1047811 := bstep (se 1 (by rfl) ⟨785858, by rfl⟩ : syracuseStep 1047811 = 1571717) B1571717
theorem B1572113 : Blo 1044610 1572113 := bstep (se 2 (by rfl) ⟨589542, by rfl⟩ : syracuseStep 1572113 = 1179085) B1179085
theorem B1047827 : Blo 1044610 1047827 := bstep (se 1 (by rfl) ⟨785870, by rfl⟩ : syracuseStep 1047827 = 1571741) B1571741
theorem B1047843 : Blo 1044610 1047843 := bstep (se 1 (by rfl) ⟨785882, by rfl⟩ : syracuseStep 1047843 = 1571765) B1571765
theorem B1572131 : Blo 1044610 1572131 := bstep (se 1 (by rfl) ⟨1179098, by rfl⟩ : syracuseStep 1572131 = 2358197) B2358197
theorem B1047859 : Blo 1044610 1047859 := bstep (se 1 (by rfl) ⟨785894, by rfl⟩ : syracuseStep 1047859 = 1571789) B1571789
theorem B1572161 : Blo 1044610 1572161 := bstep (se 2 (by rfl) ⟨589560, by rfl⟩ : syracuseStep 1572161 = 1179121) B1179121
theorem B1047875 : Blo 1044610 1047875 := bstep (se 1 (by rfl) ⟨785906, by rfl⟩ : syracuseStep 1047875 = 1571813) B1571813
theorem B1047891 : Blo 1044610 1047891 := bstep (se 1 (by rfl) ⟨785918, by rfl⟩ : syracuseStep 1047891 = 1571837) B1571837
theorem B1572179 : Blo 1044610 1572179 := bstep (se 1 (by rfl) ⟨1179134, by rfl⟩ : syracuseStep 1572179 = 2358269) B2358269
theorem B1047907 : Blo 1044610 1047907 := bstep (se 1 (by rfl) ⟨785930, by rfl⟩ : syracuseStep 1047907 = 1571861) B1571861
theorem B1572209 : Blo 1044610 1572209 := bstep (se 2 (by rfl) ⟨589578, by rfl⟩ : syracuseStep 1572209 = 1179157) B1179157
theorem B1768817 : Blo 1044610 1768817 := bstep (se 2 (by rfl) ⟨663306, by rfl⟩ : syracuseStep 1768817 = 1326613) B1326613
theorem B1047923 : Blo 1044610 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B1178995 : Blo 1044610 1178995 := bstep (se 1 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 1178995 = 1768493) B1768493
theorem B1047939 : Blo 1044610 1047939 := bstep (se 1 (by rfl) ⟨785954, by rfl⟩ : syracuseStep 1047939 = 1571909) B1571909
theorem B1572227 : Blo 1044610 1572227 := bstep (se 1 (by rfl) ⟨1179170, by rfl⟩ : syracuseStep 1572227 = 2358341) B2358341
theorem B1047955 : Blo 1044610 1047955 := bstep (se 1 (by rfl) ⟨785966, by rfl⟩ : syracuseStep 1047955 = 1571933) B1571933
theorem B1572257 : Blo 1044610 1572257 := bstep (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) B1179193
theorem B1047971 : Blo 1044610 1047971 := bstep (se 1 (by rfl) ⟨785978, by rfl⟩ : syracuseStep 1047971 = 1571957) B1571957
theorem B3538349 : Blo 1044610 3538349 := bstep (se 3 (by rfl) ⟨663440, by rfl⟩ : syracuseStep 3538349 = 1326881) B1326881
theorem B1047987 : Blo 1044610 1047987 := bstep (se 1 (by rfl) ⟨785990, by rfl⟩ : syracuseStep 1047987 = 1571981) B1571981
theorem B1572275 : Blo 1044610 1572275 := bstep (se 1 (by rfl) ⟨1179206, by rfl⟩ : syracuseStep 1572275 = 2358413) B2358413
theorem B1048003 : Blo 1044610 1048003 := bstep (se 1 (by rfl) ⟨786002, by rfl⟩ : syracuseStep 1048003 = 1572005) B1572005
theorem B1572305 : Blo 1044610 1572305 := bstep (se 2 (by rfl) ⟨589614, by rfl⟩ : syracuseStep 1572305 = 1179229) B1179229
theorem B2358737 : Blo 1044610 2358737 := bstep (se 2 (by rfl) ⟨884526, by rfl⟩ : syracuseStep 2358737 = 1769053) B1769053
theorem B1048019 : Blo 1044610 1048019 := bstep (se 1 (by rfl) ⟨786014, by rfl⟩ : syracuseStep 1048019 = 1572029) B1572029
theorem B1048035 : Blo 1044610 1048035 := bstep (se 1 (by rfl) ⟨786026, by rfl⟩ : syracuseStep 1048035 = 1572053) B1572053
theorem B1572323 : Blo 1044610 1572323 := bstep (se 1 (by rfl) ⟨1179242, by rfl⟩ : syracuseStep 1572323 = 2358485) B2358485
theorem B2358755 : Blo 1044610 2358755 := bstep (se 1 (by rfl) ⟨1769066, by rfl⟩ : syracuseStep 2358755 = 3538133) B3538133
theorem B3538403 : Blo 1044610 3538403 := bstep (se 1 (by rfl) ⟨2653802, by rfl⟩ : syracuseStep 3538403 = 5307605) B5307605
theorem B1768945 : Blo 1044610 1768945 := bstep (se 2 (by rfl) ⟨663354, by rfl⟩ : syracuseStep 1768945 = 1326709) B1326709
theorem B1048051 : Blo 1044610 1048051 := bstep (se 1 (by rfl) ⟨786038, by rfl⟩ : syracuseStep 1048051 = 1572077) B1572077
theorem B2653681 : Blo 1044610 2653681 := bstep (se 2 (by rfl) ⟨995130, by rfl⟩ : syracuseStep 2653681 = 1990261) B1990261
theorem B1572353 : Blo 1044610 1572353 := bstep (se 2 (by rfl) ⟨589632, by rfl⟩ : syracuseStep 1572353 = 1179265) B1179265
theorem B1048067 : Blo 1044610 1048067 := bstep (se 1 (by rfl) ⟨786050, by rfl⟩ : syracuseStep 1048067 = 1572101) B1572101
theorem B1179139 : Blo 1044610 1179139 := bstep (se 1 (by rfl) ⟨884354, by rfl⟩ : syracuseStep 1179139 = 1768709) B1768709
theorem B1048083 : Blo 1044610 1048083 := bstep (se 1 (by rfl) ⟨786062, by rfl⟩ : syracuseStep 1048083 = 1572125) B1572125
theorem B1572371 : Blo 1044610 1572371 := bstep (se 1 (by rfl) ⟨1179278, by rfl⟩ : syracuseStep 1572371 = 2358557) B2358557
theorem B1768979 : Blo 1044610 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B1048099 : Blo 1044610 1048099 := bstep (se 1 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 1048099 = 1572149) B1572149
theorem B1572401 : Blo 1044610 1572401 := bstep (se 2 (by rfl) ⟨589650, by rfl⟩ : syracuseStep 1572401 = 1179301) B1179301
theorem B1048115 : Blo 1044610 1048115 := bstep (se 1 (by rfl) ⟨786086, by rfl⟩ : syracuseStep 1048115 = 1572173) B1572173
theorem B1048131 : Blo 1044610 1048131 := bstep (se 1 (by rfl) ⟨786098, by rfl⟩ : syracuseStep 1048131 = 1572197) B1572197
theorem B1572419 : Blo 1044610 1572419 := bstep (se 1 (by rfl) ⟨1179314, by rfl⟩ : syracuseStep 1572419 = 2358629) B2358629
theorem B1048147 : Blo 1044610 1048147 := bstep (se 1 (by rfl) ⟨786110, by rfl⟩ : syracuseStep 1048147 = 1572221) B1572221
theorem B1572449 : Blo 1044610 1572449 := bstep (se 2 (by rfl) ⟨589668, by rfl⟩ : syracuseStep 1572449 = 1179337) B1179337
theorem B1048163 : Blo 1044610 1048163 := bstep (se 1 (by rfl) ⟨786122, by rfl⟩ : syracuseStep 1048163 = 1572245) B1572245
theorem B1048179 : Blo 1044610 1048179 := bstep (se 1 (by rfl) ⟨786134, by rfl⟩ : syracuseStep 1048179 = 1572269) B1572269
theorem B1572467 : Blo 1044610 1572467 := bstep (se 1 (by rfl) ⟨1179350, by rfl⟩ : syracuseStep 1572467 = 2358701) B2358701
theorem B1048195 : Blo 1044610 1048195 := bstep (se 1 (by rfl) ⟨786146, by rfl⟩ : syracuseStep 1048195 = 1572293) B1572293
theorem B1572497 : Blo 1044610 1572497 := bstep (se 2 (by rfl) ⟨589686, by rfl⟩ : syracuseStep 1572497 = 1179373) B1179373
theorem B1048211 : Blo 1044610 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B1179283 : Blo 1044610 1179283 := bstep (se 1 (by rfl) ⟨884462, by rfl⟩ : syracuseStep 1179283 = 1768925) B1768925
theorem B1769107 : Blo 1044610 1769107 := bstep (se 1 (by rfl) ⟨1326830, by rfl⟩ : syracuseStep 1769107 = 2653661) B2653661
theorem B1048227 : Blo 1044610 1048227 := bstep (se 1 (by rfl) ⟨786170, by rfl⟩ : syracuseStep 1048227 = 1572341) B1572341
theorem B1572515 : Blo 1044610 1572515 := bstep (se 1 (by rfl) ⟨1179386, by rfl⟩ : syracuseStep 1572515 = 2358773) B2358773
theorem B1048243 : Blo 1044610 1048243 := bstep (se 1 (by rfl) ⟨786182, by rfl⟩ : syracuseStep 1048243 = 1572365) B1572365
theorem B1572545 : Blo 1044610 1572545 := bstep (se 2 (by rfl) ⟨589704, by rfl⟩ : syracuseStep 1572545 = 1179409) B1179409
theorem B1048259 : Blo 1044610 1048259 := bstep (se 1 (by rfl) ⟨786194, by rfl⟩ : syracuseStep 1048259 = 1572389) B1572389
theorem B1048275 : Blo 1044610 1048275 := bstep (se 1 (by rfl) ⟨786206, by rfl⟩ : syracuseStep 1048275 = 1572413) B1572413
theorem B1572563 : Blo 1044610 1572563 := bstep (se 1 (by rfl) ⟨1179422, by rfl⟩ : syracuseStep 1572563 = 2358845) B2358845
theorem B1048291 : Blo 1044610 1048291 := bstep (se 1 (by rfl) ⟨786218, by rfl⟩ : syracuseStep 1048291 = 1572437) B1572437
theorem B1572593 : Blo 1044610 1572593 := bstep (se 2 (by rfl) ⟨589722, by rfl⟩ : syracuseStep 1572593 = 1179445) B1179445
theorem B2359025 : Blo 1044610 2359025 := bstep (se 2 (by rfl) ⟨884634, by rfl⟩ : syracuseStep 2359025 = 1769269) B1769269
theorem B1048307 : Blo 1044610 1048307 := bstep (se 1 (by rfl) ⟨786230, by rfl⟩ : syracuseStep 1048307 = 1572461) B1572461
theorem B3538673 : Blo 1044610 3538673 := bstep (se 2 (by rfl) ⟨1327002, by rfl⟩ : syracuseStep 3538673 = 2654005) B2654005
theorem B1048323 : Blo 1044610 1048323 := bstep (se 1 (by rfl) ⟨786242, by rfl⟩ : syracuseStep 1048323 = 1572485) B1572485
theorem B1572611 : Blo 1044610 1572611 := bstep (se 1 (by rfl) ⟨1179458, by rfl⟩ : syracuseStep 1572611 = 2358917) B2358917
theorem B2359043 : Blo 1044610 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B2653955 : Blo 1044610 2653955 := bstep (se 1 (by rfl) ⟨1990466, by rfl⟩ : syracuseStep 2653955 = 3980933) B3980933
theorem B1048339 : Blo 1044610 1048339 := bstep (se 1 (by rfl) ⟨786254, by rfl⟩ : syracuseStep 1048339 = 1572509) B1572509
theorem B1572641 : Blo 1044610 1572641 := bstep (se 2 (by rfl) ⟨589740, by rfl⟩ : syracuseStep 1572641 = 1179481) B1179481
theorem B1769249 : Blo 1044610 1769249 := bstep (se 2 (by rfl) ⟨663468, by rfl⟩ : syracuseStep 1769249 = 1326937) B1326937
theorem B1048355 : Blo 1044610 1048355 := bstep (se 1 (by rfl) ⟨786266, by rfl⟩ : syracuseStep 1048355 = 1572533) B1572533
theorem B1179427 : Blo 1044610 1179427 := bstep (se 1 (by rfl) ⟨884570, by rfl⟩ : syracuseStep 1179427 = 1769141) B1769141
theorem B1048371 : Blo 1044610 1048371 := bstep (se 1 (by rfl) ⟨786278, by rfl⟩ : syracuseStep 1048371 = 1572557) B1572557
theorem B1572659 : Blo 1044610 1572659 := bstep (se 1 (by rfl) ⟨1179494, by rfl⟩ : syracuseStep 1572659 = 2358989) B2358989
theorem B1048387 : Blo 1044610 1048387 := bstep (se 1 (by rfl) ⟨786290, by rfl⟩ : syracuseStep 1048387 = 1572581) B1572581
theorem B1572689 : Blo 1044610 1572689 := bstep (se 2 (by rfl) ⟨589758, by rfl⟩ : syracuseStep 1572689 = 1179517) B1179517
theorem B1048403 : Blo 1044610 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B1048419 : Blo 1044610 1048419 := bstep (se 1 (by rfl) ⟨786314, by rfl⟩ : syracuseStep 1048419 = 1572629) B1572629
theorem B1572707 : Blo 1044610 1572707 := bstep (se 1 (by rfl) ⟨1179530, by rfl⟩ : syracuseStep 1572707 = 2359061) B2359061
theorem B1048435 : Blo 1044610 1048435 := bstep (se 1 (by rfl) ⟨786326, by rfl⟩ : syracuseStep 1048435 = 1572653) B1572653
theorem B1572737 : Blo 1044610 1572737 := bstep (se 2 (by rfl) ⟨589776, by rfl⟩ : syracuseStep 1572737 = 1179553) B1179553
theorem B1048451 : Blo 1044610 1048451 := bstep (se 1 (by rfl) ⟨786338, by rfl⟩ : syracuseStep 1048451 = 1572677) B1572677
theorem B1048467 : Blo 1044610 1048467 := bstep (se 1 (by rfl) ⟨786350, by rfl⟩ : syracuseStep 1048467 = 1572701) B1572701
theorem B1572755 : Blo 1044610 1572755 := bstep (se 1 (by rfl) ⟨1179566, by rfl⟩ : syracuseStep 1572755 = 2359133) B2359133
theorem B1769377 : Blo 1044610 1769377 := bstep (se 2 (by rfl) ⟨663516, by rfl⟩ : syracuseStep 1769377 = 1327033) B1327033
theorem B1048483 : Blo 1044610 1048483 := bstep (se 1 (by rfl) ⟨786362, by rfl⟩ : syracuseStep 1048483 = 1572725) B1572725
theorem B1572785 : Blo 1044610 1572785 := bstep (se 2 (by rfl) ⟨589794, by rfl⟩ : syracuseStep 1572785 = 1179589) B1179589
theorem B1048499 : Blo 1044610 1048499 := bstep (se 1 (by rfl) ⟨786374, by rfl⟩ : syracuseStep 1048499 = 1572749) B1572749
theorem B1179571 : Blo 1044610 1179571 := bstep (se 1 (by rfl) ⟨884678, by rfl⟩ : syracuseStep 1179571 = 1769357) B1769357
theorem B1048515 : Blo 1044610 1048515 := bstep (se 1 (by rfl) ⟨786386, by rfl⟩ : syracuseStep 1048515 = 1572773) B1572773
theorem B1572803 : Blo 1044610 1572803 := bstep (se 1 (by rfl) ⟨1179602, by rfl⟩ : syracuseStep 1572803 = 2359205) B2359205
theorem B1769411 : Blo 1044610 1769411 := bstep (se 1 (by rfl) ⟨1327058, by rfl⟩ : syracuseStep 1769411 = 2654117) B2654117
theorem B2654147 : Blo 1044610 2654147 := bstep (se 1 (by rfl) ⟨1990610, by rfl⟩ : syracuseStep 2654147 = 3981221) B3981221
theorem B1048531 : Blo 1044610 1048531 := bstep (se 1 (by rfl) ⟨786398, by rfl⟩ : syracuseStep 1048531 = 1572797) B1572797
theorem B1572833 : Blo 1044610 1572833 := bstep (se 2 (by rfl) ⟨589812, by rfl⟩ : syracuseStep 1572833 = 1179625) B1179625
theorem B1048547 : Blo 1044610 1048547 := bstep (se 1 (by rfl) ⟨786410, by rfl⟩ : syracuseStep 1048547 = 1572821) B1572821
theorem B2981873 : Blo 1044610 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B1048563 : Blo 1044610 1048563 := bstep (se 1 (by rfl) ⟨786422, by rfl⟩ : syracuseStep 1048563 = 1572845) B1572845
theorem B1572851 : Blo 1044610 1572851 := bstep (se 1 (by rfl) ⟨1179638, by rfl⟩ : syracuseStep 1572851 = 2359277) B2359277
theorem B1572875 : Blo 1044610 1572875 := bstep (se 1 (by rfl) ⟨1179656, by rfl⟩ : syracuseStep 1572875 = 2359313) B2359313
theorem B1048587 : Blo 1044610 1048587 := bstep (se 1 (by rfl) ⟨786440, by rfl⟩ : syracuseStep 1048587 = 1572881) B1572881
theorem B1572887 : Blo 1044610 1572887 := bstep (se 1 (by rfl) ⟨1179665, by rfl⟩ : syracuseStep 1572887 = 2359331) B2359331
theorem B1048599 : Blo 1044610 1048599 := bstep (se 1 (by rfl) ⟨786449, by rfl⟩ : syracuseStep 1048599 = 1572899) B1572899
theorem B7537283 : Blo 1044610 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B3769163 : Blo 1044610 3769163 := bstep (se 1 (by rfl) ⟨2826872, by rfl⟩ : syracuseStep 3769163 = 5653745) B5653745
theorem B2982977 : Blo 1044610 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B4031633 : Blo 1044610 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B3966353 : Blo 1044610 3966353 := bstep (se 2 (by rfl) ⟨1487382, by rfl⟩ : syracuseStep 3966353 = 2974765) B2974765
theorem B1115575 : Blo 1044610 1115575 := bstep (se 1 (by rfl) ⟨836681, by rfl⟩ : syracuseStep 1115575 = 1673363) B1673363
theorem B8488397 : Blo 1044610 8488397 := bstep (se 3 (by rfl) ⟨1591574, by rfl⟩ : syracuseStep 8488397 = 3183149) B3183149
theorem B2262529 : Blo 1044610 2262529 := bstep (se 2 (by rfl) ⟨848448, by rfl⟩ : syracuseStep 2262529 = 1696897) B1696897
theorem B2983513 : Blo 1044610 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B1115947 : Blo 1044610 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B18351937 : Blo 1044610 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B1836875 : Blo 1044610 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B3770371 : Blo 1044610 3770371 := bstep (se 1 (by rfl) ⟨2827778, by rfl⟩ : syracuseStep 3770371 = 5655557) B5655557
theorem B3967127 : Blo 1044610 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B11307269 : Blo 1044610 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B3967325 : Blo 1044610 3967325 := bstep (se 3 (by rfl) ⟨743873, by rfl⟩ : syracuseStep 3967325 = 1487747) B1487747
theorem B5966297 : Blo 1044610 5966297 := bstep (se 2 (by rfl) ⟨2237361, by rfl⟩ : syracuseStep 5966297 = 4474723) B4474723
theorem B8948657 : Blo 1044610 8948657 := bstep (se 2 (by rfl) ⟨3355746, by rfl⟩ : syracuseStep 8948657 = 6711493) B6711493
theorem B2231219 : Blo 1044610 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B2985437 : Blo 1044610 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B1150507 : Blo 1044610 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B22646627 : Blo 1044610 22646627 := bstep (se 1 (by rfl) ⟨16984970, by rfl⟩ : syracuseStep 22646627 = 33969941) B33969941
theorem B2232193 : Blo 1044610 2232193 := bstep (se 2 (by rfl) ⟨837072, by rfl⟩ : syracuseStep 2232193 = 1674145) B1674145
theorem B1511371 : Blo 1044610 1511371 := bstep (se 1 (by rfl) ⟨1133528, by rfl⟩ : syracuseStep 1511371 = 2267057) B2267057
theorem B2232449 : Blo 1044610 2232449 := bstep (se 2 (by rfl) ⟨837168, by rfl⟩ : syracuseStep 2232449 = 1674337) B1674337
theorem B2232535 : Blo 1044610 2232535 := bstep (se 1 (by rfl) ⟨1674401, by rfl⟩ : syracuseStep 2232535 = 3348803) B3348803
theorem B3182809 : Blo 1044610 3182809 := bstep (se 2 (by rfl) ⟨1193553, by rfl⟩ : syracuseStep 3182809 = 2387107) B2387107
theorem B3969283 : Blo 1044610 3969283 := bstep (se 1 (by rfl) ⟨2976962, by rfl⟩ : syracuseStep 3969283 = 5953925) B5953925
theorem B1118647 : Blo 1044610 1118647 := bstep (se 1 (by rfl) ⟨838985, by rfl⟩ : syracuseStep 1118647 = 1677971) B1677971
theorem B3969587 : Blo 1044610 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B6361901 : Blo 1044610 6361901 := bstep (se 3 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 6361901 = 2385713) B2385713
theorem B3871691 : Blo 1044610 3871691 := bstep (se 1 (by rfl) ⟨2903768, by rfl⟩ : syracuseStep 3871691 = 5807537) B5807537
theorem B5968961 : Blo 1044610 5968961 := bstep (se 2 (by rfl) ⟨2238360, by rfl⟩ : syracuseStep 5968961 = 4476721) B4476721
theorem B3970241 : Blo 1044610 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B1119467 : Blo 1044610 1119467 := bstep (se 1 (by rfl) ⟨839600, by rfl⟩ : syracuseStep 1119467 = 1679201) B1679201
theorem B19076417 : Blo 1044610 19076417 := bstep (se 2 (by rfl) ⟨7153656, by rfl⟩ : syracuseStep 19076417 = 14307313) B14307313
theorem B1676695 : Blo 1044610 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B3347905 : Blo 1044610 3347905 := bstep (se 2 (by rfl) ⟨1255464, by rfl⟩ : syracuseStep 3347905 = 2510929) B2510929
theorem B1676951 : Blo 1044610 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B335026061 : Blo 1044610 335026061 := bstep (se 3 (by rfl) ⟨62817386, by rfl⟩ : syracuseStep 335026061 = 125634773) B125634773
theorem B1677323 : Blo 1044610 1677323 := bstep (se 1 (by rfl) ⟨1257992, by rfl⟩ : syracuseStep 1677323 = 2515985) B2515985
theorem B11606051 : Blo 1044610 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B3971501 : Blo 1044610 3971501 := bstep (se 3 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 3971501 = 1489313) B1489313
theorem B3774899 : Blo 1044610 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B3971531 : Blo 1044610 3971531 := bstep (se 1 (by rfl) ⟨2978648, by rfl⟩ : syracuseStep 3971531 = 5957297) B5957297
theorem B8952281 : Blo 1044610 8952281 := bstep (se 2 (by rfl) ⟨3357105, by rfl⟩ : syracuseStep 8952281 = 6714211) B6714211
theorem B2235251 : Blo 1044610 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B3972185 : Blo 1044610 3972185 := bstep (se 2 (by rfl) ⟨1489569, by rfl⟩ : syracuseStep 3972185 = 2979139) B2979139
theorem B1416523 : Blo 1044610 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B3972503 : Blo 1044610 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B1678745 : Blo 1044610 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B7937837 : Blo 1044610 7937837 := bstep (se 3 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 7937837 = 2976689) B2976689
theorem B4464557 : Blo 1044610 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B12754979 : Blo 1044610 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B3973171 : Blo 1044610 3973171 := bstep (se 1 (by rfl) ⟨2979878, by rfl⟩ : syracuseStep 3973171 = 5959757) B5959757
theorem B3350621 : Blo 1044610 3350621 := bstep (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) B1256483
theorem B2236567 : Blo 1044610 2236567 := bstep (se 1 (by rfl) ⟨1677425, by rfl⟩ : syracuseStep 2236567 = 3354851) B3354851
theorem B3449153 : Blo 1044610 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B2236747 : Blo 1044610 2236747 := bstep (se 1 (by rfl) ⟨1677560, by rfl⟩ : syracuseStep 2236747 = 3355121) B3355121
theorem B2236823 : Blo 1044610 2236823 := bstep (se 1 (by rfl) ⟨1677617, by rfl⟩ : syracuseStep 2236823 = 3355235) B3355235
theorem B6693299 : Blo 1044610 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B23012045 : Blo 1044610 23012045 := bstep (se 3 (by rfl) ⟨4314758, by rfl⟩ : syracuseStep 23012045 = 8629517) B8629517
theorem B2040665 : Blo 1044610 2040665 := bstep (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) B1530499
theorem B13607797 : Blo 1044610 13607797 := bstep (se 5 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 13607797 = 1275731) B1275731
theorem B17867789 : Blo 1044610 17867789 := bstep (se 3 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 17867789 = 6700421) B6700421
theorem B8954945 : Blo 1044610 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B10069085 : Blo 1044610 10069085 := bstep (se 3 (by rfl) ⟨1887953, by rfl⟩ : syracuseStep 10069085 = 3775907) B3775907
theorem B3974417 : Blo 1044610 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B2827997 : Blo 1044610 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B15083329 : Blo 1044610 15083329 := bstep (se 2 (by rfl) ⟨5656248, by rfl⟩ : syracuseStep 15083329 = 11312497) B11312497
theorem B3975115 : Blo 1044610 3975115 := bstep (se 1 (by rfl) ⟨2981336, by rfl⟩ : syracuseStep 3975115 = 5962673) B5962673
theorem B14297239 : Blo 1044610 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B2238617 : Blo 1044610 2238617 := bstep (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) B1678963
theorem B3975389 : Blo 1044610 3975389 := bstep (se 3 (by rfl) ⟨745385, by rfl⟩ : syracuseStep 3975389 = 1490771) B1490771
theorem B67840739 : Blo 1044610 67840739 := bstep (se 1 (by rfl) ⟨50880554, by rfl⟩ : syracuseStep 67840739 = 101761109) B101761109
theorem B2239283 : Blo 1044610 2239283 := bstep (se 1 (by rfl) ⟨1679462, by rfl⟩ : syracuseStep 2239283 = 3358925) B3358925
theorem B5024587 : Blo 1044610 5024587 := bstep (se 1 (by rfl) ⟨3768440, by rfl⟩ : syracuseStep 5024587 = 7536881) B7536881
theorem B3976087 : Blo 1044610 3976087 := bstep (se 1 (by rfl) ⟨2982065, by rfl⟩ : syracuseStep 3976087 = 5964131) B5964131
theorem B3025943 : Blo 1044610 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B4467905 : Blo 1044610 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B6892931 : Blo 1044610 6892931 := bstep (se 1 (by rfl) ⟨5169698, by rfl⟩ : syracuseStep 6892931 = 10339397) B10339397
theorem B5025203 : Blo 1044610 5025203 := bstep (se 1 (by rfl) ⟨3768902, by rfl⟩ : syracuseStep 5025203 = 7537805) B7537805
theorem B1322507 : Blo 1044610 1322507 := bstep (se 1 (by rfl) ⟨991880, by rfl⟩ : syracuseStep 1322507 = 1983761) B1983761
theorem B4468247 : Blo 1044610 4468247 := bstep (se 1 (by rfl) ⟨3351185, by rfl⟩ : syracuseStep 4468247 = 6702371) B6702371
theorem B7941725 : Blo 1044610 7941725 := bstep (se 3 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 7941725 = 2978147) B2978147
theorem B3976877 : Blo 1044610 3976877 := bstep (se 3 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 3976877 = 1491329) B1491329
theorem B1257175 : Blo 1044610 1257175 := bstep (se 1 (by rfl) ⟨942881, by rfl⟩ : syracuseStep 1257175 = 1885763) B1885763
theorem B4239449 : Blo 1044610 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B1323211 : Blo 1044610 1323211 := bstep (se 1 (by rfl) ⟨992408, by rfl⟩ : syracuseStep 1323211 = 1984817) B1984817
theorem B8925389 : Blo 1044610 8925389 := bstep (se 3 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 8925389 = 3347021) B3347021
theorem B1061131 : Blo 1044610 1061131 := bstep (se 1 (by rfl) ⟨795848, by rfl⟩ : syracuseStep 1061131 = 1591697) B1591697
theorem B1323479 : Blo 1044610 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B18133465 : Blo 1044610 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B8040965 : Blo 1044610 8040965 := bstep (se 4 (by rfl) ⟨753840, by rfl⟩ : syracuseStep 8040965 = 1507681) B1507681
theorem B6042547 : Blo 1044610 6042547 := bstep (se 1 (by rfl) ⟨4531910, by rfl⟩ : syracuseStep 6042547 = 9063821) B9063821
theorem B7549969 : Blo 1044610 7549969 := bstep (se 2 (by rfl) ⟨2831238, by rfl⟩ : syracuseStep 7549969 = 5662477) B5662477
theorem B3978305 : Blo 1044610 3978305 := bstep (se 2 (by rfl) ⟨1491864, by rfl⟩ : syracuseStep 3978305 = 2983729) B2983729
theorem B1324183 : Blo 1044610 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B6698371 : Blo 1044610 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B4470365 : Blo 1044610 4470365 := bstep (se 3 (by rfl) ⟨838193, by rfl⟩ : syracuseStep 4470365 = 1676387) B1676387
theorem B5650021 : Blo 1044610 5650021 := bstep (se 4 (by rfl) ⟨529689, by rfl⟩ : syracuseStep 5650021 = 1059379) B1059379
theorem B3356311 : Blo 1044610 3356311 := bstep (se 1 (by rfl) ⟨2517233, by rfl⟩ : syracuseStep 3356311 = 5034467) B5034467
theorem B5289623 : Blo 1044610 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B2012953 : Blo 1044610 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B3356491 : Blo 1044610 3356491 := bstep (se 1 (by rfl) ⟨2517368, by rfl⟩ : syracuseStep 3356491 = 5034737) B5034737
theorem B73611109 : Blo 1044610 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B4470673 : Blo 1044610 4470673 := bstep (se 2 (by rfl) ⟨1676502, by rfl⟩ : syracuseStep 4470673 = 3353005) B3353005
theorem B3356567 : Blo 1044610 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B4470707 : Blo 1044610 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B1914881 : Blo 1044610 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B3356761 : Blo 1044610 3356761 := bstep (se 2 (by rfl) ⟨1258785, by rfl⟩ : syracuseStep 3356761 = 2517571) B2517571
theorem B2013337 : Blo 1044610 2013337 := bstep (se 2 (by rfl) ⟨755001, by rfl⟩ : syracuseStep 2013337 = 1510003) B1510003
theorem B1194283 : Blo 1044610 1194283 := bstep (se 1 (by rfl) ⟨895712, by rfl⟩ : syracuseStep 1194283 = 1791425) B1791425
theorem B48380273 : Blo 1044610 48380273 := bstep (se 2 (by rfl) ⟨18142602, by rfl⟩ : syracuseStep 48380273 = 36285205) B36285205
theorem B2013707 : Blo 1044610 2013707 := bstep (se 1 (by rfl) ⟨1510280, by rfl⟩ : syracuseStep 2013707 = 3020561) B3020561
theorem B3979793 : Blo 1044610 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B1882649 : Blo 1044610 1882649 := bstep (se 2 (by rfl) ⟨705993, by rfl⟩ : syracuseStep 1882649 = 1411987) B1411987
theorem B1325899 : Blo 1044610 1325899 := bstep (se 1 (by rfl) ⟨994424, by rfl⟩ : syracuseStep 1325899 = 1988849) B1988849
theorem B26917733 : Blo 1044610 26917733 := bstep (se 4 (by rfl) ⟨2523537, by rfl⟩ : syracuseStep 26917733 = 5047075) B5047075
theorem B3980249 : Blo 1044610 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B7552045 : Blo 1044610 7552045 := bstep (se 3 (by rfl) ⟨1416008, by rfl⟩ : syracuseStep 7552045 = 2832017) B2832017
theorem B1490071 : Blo 1044610 1490071 := bstep (se 1 (by rfl) ⟨1117553, by rfl⟩ : syracuseStep 1490071 = 2235107) B2235107
theorem B3980461 : Blo 1044610 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B12107225 : Blo 1044610 12107225 := bstep (se 2 (by rfl) ⟨4540209, by rfl⟩ : syracuseStep 12107225 = 9080419) B9080419
theorem B3980765 : Blo 1044610 3980765 := bstep (se 3 (by rfl) ⟨746393, by rfl⟩ : syracuseStep 3980765 = 1492787) B1492787
theorem B6045229 : Blo 1044610 6045229 := bstep (se 3 (by rfl) ⟨1133480, by rfl⟩ : syracuseStep 6045229 = 2266961) B2266961
theorem B1589015 : Blo 1044610 1589015 := bstep (se 1 (by rfl) ⟨1191761, by rfl⟩ : syracuseStep 1589015 = 2383523) B2383523
theorem B1326871 : Blo 1044610 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B4472621 : Blo 1044610 4472621 := bstep (se 3 (by rfl) ⟨838616, by rfl⟩ : syracuseStep 4472621 = 1677233) B1677233
theorem B3817547 : Blo 1044610 3817547 := bstep (se 1 (by rfl) ⟨2863160, by rfl⟩ : syracuseStep 3817547 = 5726321) B5726321
theorem B1884235 : Blo 1044610 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B3359027 : Blo 1044610 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B5030237 : Blo 1044610 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B4473305 : Blo 1044610 4473305 := bstep (se 2 (by rfl) ⟨1677489, by rfl⟩ : syracuseStep 4473305 = 3354979) B3354979
theorem B64471565 : Blo 1044610 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B5653313 : Blo 1044610 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B1590359 : Blo 1044610 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B5293187 : Blo 1044610 5293187 := bstep (se 1 (by rfl) ⟨3969890, by rfl⟩ : syracuseStep 5293187 = 7939781) B7939781
theorem B1492121 : Blo 1044610 1492121 := bstep (se 2 (by rfl) ⟨559545, by rfl⟩ : syracuseStep 1492121 = 1119091) B1119091
theorem B1885619 : Blo 1044610 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B6374957 : Blo 1044610 6374957 := bstep (se 3 (by rfl) ⟨1195304, by rfl⟩ : syracuseStep 6374957 = 2390609) B2390609
theorem B1492759 : Blo 1044610 1492759 := bstep (se 1 (by rfl) ⟨1119569, by rfl⟩ : syracuseStep 1492759 = 2239139) B2239139
theorem B1984331 : Blo 1044610 1984331 := bstep (se 1 (by rfl) ⟨1488248, by rfl⟩ : syracuseStep 1984331 = 2976497) B2976497
theorem B1984513 : Blo 1044610 1984513 := bstep (se 2 (by rfl) ⟨744192, by rfl⟩ : syracuseStep 1984513 = 1488385) B1488385
theorem B9062435 : Blo 1044610 9062435 := bstep (se 1 (by rfl) ⟨6796826, by rfl⟩ : syracuseStep 9062435 = 13593653) B13593653
theorem B4769837 : Blo 1044610 4769837 := bstep (se 3 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 4769837 = 1788689) B1788689
theorem B1984961 : Blo 1044610 1984961 := bstep (se 2 (by rfl) ⟨744360, by rfl⟩ : syracuseStep 1984961 = 1488721) B1488721
theorem B1886743 : Blo 1044610 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B1133195 : Blo 1044610 1133195 := bstep (se 1 (by rfl) ⟨849896, by rfl⟩ : syracuseStep 1133195 = 1699793) B1699793
theorem B1985303 : Blo 1044610 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B1887233 : Blo 1044610 1887233 := bstep (se 2 (by rfl) ⟨707712, by rfl⟩ : syracuseStep 1887233 = 1415425) B1415425
theorem B4475969 : Blo 1044610 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B8473805 : Blo 1044610 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B1985971 : Blo 1044610 1985971 := bstep (se 1 (by rfl) ⟨1489478, by rfl⟩ : syracuseStep 1985971 = 2978957) B2978957
theorem B3526091 : Blo 1044610 3526091 := bstep (se 1 (by rfl) ⟨2644568, by rfl⟩ : syracuseStep 3526091 = 5289137) B5289137
theorem B3526361 : Blo 1044610 3526361 := bstep (se 2 (by rfl) ⟨1322385, by rfl⟩ : syracuseStep 3526361 = 2644771) B2644771
theorem B1986419 : Blo 1044610 1986419 := bstep (se 1 (by rfl) ⟨1489814, by rfl⟩ : syracuseStep 1986419 = 2979629) B2979629
theorem B1986457 : Blo 1044610 1986457 := bstep (se 2 (by rfl) ⟨744921, by rfl⟩ : syracuseStep 1986457 = 1489843) B1489843
theorem B1134775 : Blo 1044610 1134775 := bstep (se 1 (by rfl) ⟨851081, by rfl⟩ : syracuseStep 1134775 = 1702163) B1702163
theorem B4772171 : Blo 1044610 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B6050123 : Blo 1044610 6050123 := bstep (se 1 (by rfl) ⟨4537592, by rfl⟩ : syracuseStep 6050123 = 9075185) B9075185
theorem B1986905 : Blo 1044610 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B13390181 : Blo 1044610 13390181 := bstep (se 4 (by rfl) ⟨1255329, by rfl⟩ : syracuseStep 13390181 = 2510659) B2510659
theorem B3527063 : Blo 1044610 3527063 := bstep (se 1 (by rfl) ⟨2645297, by rfl⟩ : syracuseStep 3527063 = 5290595) B5290595
theorem B4477457 : Blo 1044610 4477457 := bstep (se 2 (by rfl) ⟨1679046, by rfl⟩ : syracuseStep 4477457 = 3358093) B3358093
theorem B3625523 : Blo 1044610 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B5296913 : Blo 1044610 5296913 := bstep (se 2 (by rfl) ⟨1986342, by rfl⟩ : syracuseStep 5296913 = 3972685) B3972685
theorem B3527603 : Blo 1044610 3527603 := bstep (se 1 (by rfl) ⟨2645702, by rfl⟩ : syracuseStep 3527603 = 5291405) B5291405
theorem B5297075 : Blo 1044610 5297075 := bstep (se 1 (by rfl) ⟨3972806, by rfl⟩ : syracuseStep 5297075 = 7945613) B7945613
theorem B1987649 : Blo 1044610 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B30626885 : Blo 1044610 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B3527873 : Blo 1044610 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B1987915 : Blo 1044610 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B4478429 : Blo 1044610 4478429 := bstep (se 3 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 4478429 = 1679411) B1679411
theorem B5953175 : Blo 1044610 5953175 := bstep (se 1 (by rfl) ⟨4464881, by rfl⟩ : syracuseStep 5953175 = 8929763) B8929763
theorem B48420557 : Blo 1044610 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B3528413 : Blo 1044610 3528413 := bstep (se 3 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 3528413 = 1323155) B1323155
theorem B1988363 : Blo 1044610 1988363 := bstep (se 1 (by rfl) ⟨1491272, by rfl⟩ : syracuseStep 1988363 = 2982545) B2982545
theorem B6706961 : Blo 1044610 6706961 := bstep (se 2 (by rfl) ⟨2515110, by rfl⟩ : syracuseStep 6706961 = 5030221) B5030221
theorem B1431319 : Blo 1044610 1431319 := bstep (se 1 (by rfl) ⟨1073489, by rfl⟩ : syracuseStep 1431319 = 2146979) B2146979
theorem B5035927 : Blo 1044610 5035927 := bstep (se 1 (by rfl) ⟨3776945, by rfl⟩ : syracuseStep 5035927 = 7553891) B7553891
theorem B1988545 : Blo 1044610 1988545 := bstep (se 2 (by rfl) ⟨745704, by rfl⟩ : syracuseStep 1988545 = 1491409) B1491409
theorem B4413457 : Blo 1044610 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B1988887 : Blo 1044610 1988887 := bstep (se 1 (by rfl) ⟨1491665, by rfl⟩ : syracuseStep 1988887 = 2983331) B2983331
theorem B68802929 : Blo 1044610 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B2644427 : Blo 1044610 2644427 := bstep (se 1 (by rfl) ⟨1983320, by rfl⟩ : syracuseStep 2644427 = 3966641) B3966641
theorem B1989107 : Blo 1044610 1989107 := bstep (se 1 (by rfl) ⟨1491830, by rfl⟩ : syracuseStep 1989107 = 2983661) B2983661
theorem B2120203 : Blo 1044610 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B5364299 : Blo 1044610 5364299 := bstep (se 1 (by rfl) ⟨4023224, by rfl⟩ : syracuseStep 5364299 = 8046449) B8046449
theorem B2120267 : Blo 1044610 2120267 := bstep (se 1 (by rfl) ⟨1590200, by rfl⟩ : syracuseStep 2120267 = 3180401) B3180401
theorem B1989335 : Blo 1044610 1989335 := bstep (se 1 (by rfl) ⟨1492001, by rfl⟩ : syracuseStep 1989335 = 2984003) B2984003
theorem B5659409 : Blo 1044610 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B3529547 : Blo 1044610 3529547 := bstep (se 1 (by rfl) ⟨2647160, by rfl⟩ : syracuseStep 3529547 = 5294321) B5294321
theorem B5299019 : Blo 1044610 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B1989593 : Blo 1044610 1989593 := bstep (se 2 (by rfl) ⟨746097, by rfl⟩ : syracuseStep 1989593 = 1492195) B1492195
theorem B3529817 : Blo 1044610 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B5659865 : Blo 1044610 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B1990003 : Blo 1044610 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B2350475 : Blo 1044610 2350475 := bstep (se 1 (by rfl) ⟨1762856, by rfl⟩ : syracuseStep 2350475 = 3525713) B3525713
theorem B2645399 : Blo 1044610 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B16997809 : Blo 1044610 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B2350529 : Blo 1044610 2350529 := bstep (se 2 (by rfl) ⟨881448, by rfl⟩ : syracuseStep 2350529 = 1762897) B1762897
theorem B2350745 : Blo 1044610 2350745 := bstep (se 2 (by rfl) ⟨881529, by rfl⟩ : syracuseStep 2350745 = 1763059) B1763059
theorem B2350835 : Blo 1044610 2350835 := bstep (se 1 (by rfl) ⟨1763126, by rfl⟩ : syracuseStep 2350835 = 3526253) B3526253
theorem B2350871 : Blo 1044610 2350871 := bstep (se 1 (by rfl) ⟨1763153, by rfl⟩ : syracuseStep 2350871 = 3526307) B3526307
theorem B3530519 : Blo 1044610 3530519 := bstep (se 1 (by rfl) ⟨2647889, by rfl⟩ : syracuseStep 3530519 = 5295779) B5295779
theorem B11919149 : Blo 1044610 11919149 := bstep (se 3 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 11919149 = 4469681) B4469681
theorem B4251467 : Blo 1044610 4251467 := bstep (se 1 (by rfl) ⟨3188600, by rfl⟩ : syracuseStep 4251467 = 6377201) B6377201
theorem B1990489 : Blo 1044610 1990489 := bstep (se 2 (by rfl) ⟨746433, by rfl⟩ : syracuseStep 1990489 = 1492867) B1492867
theorem B2351051 : Blo 1044610 2351051 := bstep (se 1 (by rfl) ⟨1763288, by rfl⟩ : syracuseStep 2351051 = 3526577) B3526577
theorem B2383859 : Blo 1044610 2383859 := bstep (se 1 (by rfl) ⟨1787894, by rfl⟩ : syracuseStep 2383859 = 3575789) B3575789
theorem B2351105 : Blo 1044610 2351105 := bstep (se 2 (by rfl) ⟨881664, by rfl⟩ : syracuseStep 2351105 = 1763329) B1763329
theorem B4087811 : Blo 1044610 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B2383895 : Blo 1044610 2383895 := bstep (se 1 (by rfl) ⟨1787921, by rfl⟩ : syracuseStep 2383895 = 3575843) B3575843
theorem B2646067 : Blo 1044610 2646067 := bstep (se 1 (by rfl) ⟨1984550, by rfl⟩ : syracuseStep 2646067 = 3969101) B3969101
theorem B2646209 : Blo 1044610 2646209 := bstep (se 2 (by rfl) ⟨992328, by rfl⟩ : syracuseStep 2646209 = 1984657) B1984657
theorem B2351321 : Blo 1044610 2351321 := bstep (se 2 (by rfl) ⟨881745, by rfl⟩ : syracuseStep 2351321 = 1763491) B1763491
theorem B2154763 : Blo 1044610 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B2351411 : Blo 1044610 2351411 := bstep (se 1 (by rfl) ⟨1763558, by rfl⟩ : syracuseStep 2351411 = 3527117) B3527117
theorem B3531059 : Blo 1044610 3531059 := bstep (se 1 (by rfl) ⟨2648294, by rfl⟩ : syracuseStep 3531059 = 5296589) B5296589
theorem B2351447 : Blo 1044610 2351447 := bstep (se 1 (by rfl) ⟨1763585, by rfl⟩ : syracuseStep 2351447 = 3527171) B3527171
theorem B2351627 : Blo 1044610 2351627 := bstep (se 1 (by rfl) ⟨1763720, by rfl⟩ : syracuseStep 2351627 = 3527441) B3527441
theorem B2384407 : Blo 1044610 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B16114211 : Blo 1044610 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B2351681 : Blo 1044610 2351681 := bstep (se 2 (by rfl) ⟨881880, by rfl⟩ : syracuseStep 2351681 = 1763761) B1763761
theorem B3531329 : Blo 1044610 3531329 := bstep (se 2 (by rfl) ⟨1324248, by rfl⟩ : syracuseStep 3531329 = 2648497) B2648497
theorem B5300801 : Blo 1044610 5300801 := bstep (se 2 (by rfl) ⟨1987800, by rfl⟩ : syracuseStep 5300801 = 3975601) B3975601
theorem B10052171 : Blo 1044610 10052171 := bstep (se 1 (by rfl) ⟨7539128, by rfl⟩ : syracuseStep 10052171 = 15078257) B15078257
theorem B6709853 : Blo 1044610 6709853 := bstep (se 3 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 6709853 = 2516195) B2516195
theorem B1073899 : Blo 1044610 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B2351897 : Blo 1044610 2351897 := bstep (se 2 (by rfl) ⟨881961, by rfl⟩ : syracuseStep 2351897 = 1763923) B1763923
theorem B2351987 : Blo 1044610 2351987 := bstep (se 1 (by rfl) ⟨1763990, by rfl⟩ : syracuseStep 2351987 = 3527981) B3527981
theorem B2352023 : Blo 1044610 2352023 := bstep (se 1 (by rfl) ⟨1764017, by rfl⟩ : syracuseStep 2352023 = 3528035) B3528035
theorem B2352203 : Blo 1044610 2352203 := bstep (se 1 (by rfl) ⟨1764152, by rfl⟩ : syracuseStep 2352203 = 3528305) B3528305
theorem B3531869 : Blo 1044610 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B2352257 : Blo 1044610 2352257 := bstep (se 2 (by rfl) ⟨882096, by rfl⟩ : syracuseStep 2352257 = 1764193) B1764193
theorem B2974913 : Blo 1044610 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B2352473 : Blo 1044610 2352473 := bstep (se 2 (by rfl) ⟨882177, by rfl⟩ : syracuseStep 2352473 = 1764355) B1764355
theorem B2352563 : Blo 1044610 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B2647475 : Blo 1044610 2647475 := bstep (se 1 (by rfl) ⟨1985606, by rfl⟩ : syracuseStep 2647475 = 3971213) B3971213
theorem B2352599 : Blo 1044610 2352599 := bstep (se 1 (by rfl) ⟨1764449, by rfl⟩ : syracuseStep 2352599 = 3528899) B3528899
theorem B2975255 : Blo 1044610 2975255 := bstep (se 1 (by rfl) ⟨2231441, by rfl⟩ : syracuseStep 2975255 = 4462883) B4462883
theorem B2516503 : Blo 1044610 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B2352779 : Blo 1044610 2352779 := bstep (se 1 (by rfl) ⟨1764584, by rfl⟩ : syracuseStep 2352779 = 3529169) B3529169
theorem B8939159 : Blo 1044610 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B2352833 : Blo 1044610 2352833 := bstep (se 2 (by rfl) ⟨882312, by rfl⟩ : syracuseStep 2352833 = 1764625) B1764625
theorem B1763147 : Blo 1044610 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B2353049 : Blo 1044610 2353049 := bstep (se 2 (by rfl) ⟨882393, by rfl⟩ : syracuseStep 2353049 = 1764787) B1764787
theorem B1763275 : Blo 1044610 1763275 := bstep (se 1 (by rfl) ⟨1322456, by rfl⟩ : syracuseStep 1763275 = 2644913) B2644913
theorem B2648011 : Blo 1044610 2648011 := bstep (se 1 (by rfl) ⟨1986008, by rfl⟩ : syracuseStep 2648011 = 3972017) B3972017
theorem B1697753 : Blo 1044610 1697753 := bstep (se 2 (by rfl) ⟨636657, by rfl⟩ : syracuseStep 1697753 = 1273315) B1273315
theorem B2353139 : Blo 1044610 2353139 := bstep (se 1 (by rfl) ⟨1764854, by rfl⟩ : syracuseStep 2353139 = 3529709) B3529709
theorem B2353175 : Blo 1044610 2353175 := bstep (se 1 (by rfl) ⟨1764881, by rfl⟩ : syracuseStep 2353175 = 3529763) B3529763
theorem B1763417 : Blo 1044610 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B2648153 : Blo 1044610 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B1566923 : Blo 1044610 1566923 := bstep (se 1 (by rfl) ⟨1175192, by rfl⟩ : syracuseStep 1566923 = 2350385) B2350385
theorem B2353355 : Blo 1044610 2353355 := bstep (se 1 (by rfl) ⟨1765016, by rfl⟩ : syracuseStep 2353355 = 3530033) B3530033
theorem B3533003 : Blo 1044610 3533003 := bstep (se 1 (by rfl) ⟨2649752, by rfl⟩ : syracuseStep 3533003 = 5299505) B5299505
theorem B1566935 : Blo 1044610 1566935 := bstep (se 1 (by rfl) ⟨1175201, by rfl⟩ : syracuseStep 1566935 = 2350403) B2350403
theorem B1763545 : Blo 1044610 1763545 := bstep (se 2 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 1763545 = 1322659) B1322659
theorem B2353409 : Blo 1044610 2353409 := bstep (se 2 (by rfl) ⟨882528, by rfl⟩ : syracuseStep 2353409 = 1765057) B1765057
theorem B1567001 : Blo 1044610 1567001 := bstep (se 2 (by rfl) ⟨587625, by rfl⟩ : syracuseStep 1567001 = 1175251) B1175251
theorem B4352321 : Blo 1044610 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B5957981 : Blo 1044610 5957981 := bstep (se 3 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 5957981 = 2234243) B2234243
theorem B1567115 : Blo 1044610 1567115 := bstep (se 1 (by rfl) ⟨1175336, by rfl⟩ : syracuseStep 1567115 = 2350673) B2350673
theorem B1567127 : Blo 1044610 1567127 := bstep (se 1 (by rfl) ⟨1175345, by rfl⟩ : syracuseStep 1567127 = 2350691) B2350691
theorem B1567193 : Blo 1044610 1567193 := bstep (se 2 (by rfl) ⟨587697, by rfl⟩ : syracuseStep 1567193 = 1175395) B1175395
theorem B2353625 : Blo 1044610 2353625 := bstep (se 2 (by rfl) ⟨882609, by rfl⟩ : syracuseStep 2353625 = 1765219) B1765219
theorem B3533273 : Blo 1044610 3533273 := bstep (se 2 (by rfl) ⟨1324977, by rfl⟩ : syracuseStep 3533273 = 2649955) B2649955
theorem B5302745 : Blo 1044610 5302745 := bstep (se 2 (by rfl) ⟨1988529, by rfl⟩ : syracuseStep 5302745 = 3977059) B3977059
theorem B2353715 : Blo 1044610 2353715 := bstep (se 1 (by rfl) ⟨1765286, by rfl⟩ : syracuseStep 2353715 = 3530573) B3530573
theorem B1567307 : Blo 1044610 1567307 := bstep (se 1 (by rfl) ⟨1175480, by rfl⟩ : syracuseStep 1567307 = 2350961) B2350961
theorem B1567319 : Blo 1044610 1567319 := bstep (se 1 (by rfl) ⟨1175489, by rfl⟩ : syracuseStep 1567319 = 2350979) B2350979
theorem B2353751 : Blo 1044610 2353751 := bstep (se 1 (by rfl) ⟨1765313, by rfl⟩ : syracuseStep 2353751 = 3530627) B3530627
theorem B1567385 : Blo 1044610 1567385 := bstep (se 2 (by rfl) ⟨587769, by rfl⟩ : syracuseStep 1567385 = 1175539) B1175539
theorem B1567499 : Blo 1044610 1567499 := bstep (se 1 (by rfl) ⟨1175624, by rfl⟩ : syracuseStep 1567499 = 2351249) B2351249
theorem B2353931 : Blo 1044610 2353931 := bstep (se 1 (by rfl) ⟨1765448, by rfl⟩ : syracuseStep 2353931 = 3530897) B3530897
theorem B1567511 : Blo 1044610 1567511 := bstep (se 1 (by rfl) ⟨1175633, by rfl⟩ : syracuseStep 1567511 = 2351267) B2351267
theorem B1764119 : Blo 1044610 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B6712109 : Blo 1044610 6712109 := bstep (se 3 (by rfl) ⟨1258520, by rfl⟩ : syracuseStep 6712109 = 2517041) B2517041
theorem B2353985 : Blo 1044610 2353985 := bstep (se 2 (by rfl) ⟨882744, by rfl⟩ : syracuseStep 2353985 = 1765489) B1765489
theorem B1567577 : Blo 1044610 1567577 := bstep (se 2 (by rfl) ⟨587841, by rfl⟩ : syracuseStep 1567577 = 1175683) B1175683
theorem B1764247 : Blo 1044610 1764247 := bstep (se 1 (by rfl) ⟨1323185, by rfl⟩ : syracuseStep 1764247 = 2646371) B2646371
theorem B2648983 : Blo 1044610 2648983 := bstep (se 1 (by rfl) ⟨1986737, by rfl⟩ : syracuseStep 2648983 = 3973475) B3973475
theorem B1567691 : Blo 1044610 1567691 := bstep (se 1 (by rfl) ⟨1175768, by rfl⟩ : syracuseStep 1567691 = 2351537) B2351537
theorem B1567703 : Blo 1044610 1567703 := bstep (se 1 (by rfl) ⟨1175777, by rfl⟩ : syracuseStep 1567703 = 2351555) B2351555
theorem B1567769 : Blo 1044610 1567769 := bstep (se 2 (by rfl) ⟨587913, by rfl⟩ : syracuseStep 1567769 = 1175827) B1175827
theorem B2354201 : Blo 1044610 2354201 := bstep (se 2 (by rfl) ⟨882825, by rfl⟩ : syracuseStep 2354201 = 1765651) B1765651
theorem B2354291 : Blo 1044610 2354291 := bstep (se 1 (by rfl) ⟨1765718, by rfl⟩ : syracuseStep 2354291 = 3531437) B3531437
theorem B1567883 : Blo 1044610 1567883 := bstep (se 1 (by rfl) ⟨1175912, by rfl⟩ : syracuseStep 1567883 = 2351825) B2351825
theorem B1567895 : Blo 1044610 1567895 := bstep (se 1 (by rfl) ⟨1175921, by rfl⟩ : syracuseStep 1567895 = 2351843) B2351843
theorem B2354327 : Blo 1044610 2354327 := bstep (se 1 (by rfl) ⟨1765745, by rfl⟩ : syracuseStep 2354327 = 3531491) B3531491
theorem B3533975 : Blo 1044610 3533975 := bstep (se 1 (by rfl) ⟨2650481, by rfl⟩ : syracuseStep 3533975 = 5300963) B5300963
theorem B1567961 : Blo 1044610 1567961 := bstep (se 2 (by rfl) ⟨587985, by rfl⟩ : syracuseStep 1567961 = 1175971) B1175971
theorem B1568075 : Blo 1044610 1568075 := bstep (se 1 (by rfl) ⟨1176056, by rfl⟩ : syracuseStep 1568075 = 2352113) B2352113
theorem B2354507 : Blo 1044610 2354507 := bstep (se 1 (by rfl) ⟨1765880, by rfl⟩ : syracuseStep 2354507 = 3531761) B3531761
theorem B2649419 : Blo 1044610 2649419 := bstep (se 1 (by rfl) ⟨1987064, by rfl⟩ : syracuseStep 2649419 = 3974129) B3974129
theorem B1568087 : Blo 1044610 1568087 := bstep (se 1 (by rfl) ⟨1176065, by rfl⟩ : syracuseStep 1568087 = 2352131) B2352131
theorem B2354561 : Blo 1044610 2354561 := bstep (se 2 (by rfl) ⟨882960, by rfl⟩ : syracuseStep 2354561 = 1765921) B1765921
theorem B4779395 : Blo 1044610 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B1568153 : Blo 1044610 1568153 := bstep (se 2 (by rfl) ⟨588057, by rfl⟩ : syracuseStep 1568153 = 1176115) B1176115
theorem B4779467 : Blo 1044610 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B1568267 : Blo 1044610 1568267 := bstep (se 1 (by rfl) ⟨1176200, by rfl⟩ : syracuseStep 1568267 = 2352401) B2352401
theorem B1764875 : Blo 1044610 1764875 := bstep (se 1 (by rfl) ⟨1323656, by rfl⟩ : syracuseStep 1764875 = 2647313) B2647313
theorem B1568279 : Blo 1044610 1568279 := bstep (se 1 (by rfl) ⟨1176209, by rfl⟩ : syracuseStep 1568279 = 2352419) B2352419
theorem B1568345 : Blo 1044610 1568345 := bstep (se 2 (by rfl) ⟨588129, by rfl⟩ : syracuseStep 1568345 = 1176259) B1176259
theorem B2354777 : Blo 1044610 2354777 := bstep (se 2 (by rfl) ⟨883041, by rfl⟩ : syracuseStep 2354777 = 1766083) B1766083
theorem B2977373 : Blo 1044610 2977373 := bstep (se 3 (by rfl) ⟨558257, by rfl⟩ : syracuseStep 2977373 = 1116515) B1116515
theorem B1765003 : Blo 1044610 1765003 := bstep (se 1 (by rfl) ⟨1323752, by rfl⟩ : syracuseStep 1765003 = 2647505) B2647505
theorem B2354867 : Blo 1044610 2354867 := bstep (se 1 (by rfl) ⟨1766150, by rfl⟩ : syracuseStep 2354867 = 3532301) B3532301
theorem B3534515 : Blo 1044610 3534515 := bstep (se 1 (by rfl) ⟨2650886, by rfl⟩ : syracuseStep 3534515 = 5301773) B5301773
theorem B2649793 : Blo 1044610 2649793 := bstep (se 2 (by rfl) ⟨993672, by rfl⟩ : syracuseStep 2649793 = 1987345) B1987345
theorem B1568459 : Blo 1044610 1568459 := bstep (se 1 (by rfl) ⟨1176344, by rfl⟩ : syracuseStep 1568459 = 2352689) B2352689
theorem B1568471 : Blo 1044610 1568471 := bstep (se 1 (by rfl) ⟨1176353, by rfl⟩ : syracuseStep 1568471 = 2352707) B2352707
theorem B2354903 : Blo 1044610 2354903 := bstep (se 1 (by rfl) ⟨1766177, by rfl⟩ : syracuseStep 2354903 = 3532355) B3532355
theorem B1175287 : Blo 1044610 1175287 := bstep (se 1 (by rfl) ⟨881465, by rfl⟩ : syracuseStep 1175287 = 1762931) B1762931
theorem B1568537 : Blo 1044610 1568537 := bstep (se 2 (by rfl) ⟨588201, by rfl⟩ : syracuseStep 1568537 = 1176403) B1176403
theorem B1765145 : Blo 1044610 1765145 := bstep (se 2 (by rfl) ⟨661929, by rfl⟩ : syracuseStep 1765145 = 1323859) B1323859
theorem B1568651 : Blo 1044610 1568651 := bstep (se 1 (by rfl) ⟨1176488, by rfl⟩ : syracuseStep 1568651 = 2352977) B2352977
theorem B2355083 : Blo 1044610 2355083 := bstep (se 1 (by rfl) ⟨1766312, by rfl⟩ : syracuseStep 2355083 = 3532625) B3532625
theorem B1568663 : Blo 1044610 1568663 := bstep (se 1 (by rfl) ⟨1176497, by rfl⟩ : syracuseStep 1568663 = 2352995) B2352995
theorem B1765273 : Blo 1044610 1765273 := bstep (se 2 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 1765273 = 1323955) B1323955
theorem B1175467 : Blo 1044610 1175467 := bstep (se 1 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 1175467 = 1763201) B1763201
theorem B2977715 : Blo 1044610 2977715 := bstep (se 1 (by rfl) ⟨2233286, by rfl⟩ : syracuseStep 2977715 = 4466573) B4466573
theorem B2355137 : Blo 1044610 2355137 := bstep (se 2 (by rfl) ⟨883176, by rfl⟩ : syracuseStep 2355137 = 1766353) B1766353
theorem B3534785 : Blo 1044610 3534785 := bstep (se 2 (by rfl) ⟨1325544, by rfl⟩ : syracuseStep 3534785 = 2651089) B2651089
theorem B1568729 : Blo 1044610 1568729 := bstep (se 2 (by rfl) ⟨588273, by rfl⟩ : syracuseStep 1568729 = 1176547) B1176547
theorem B1175575 : Blo 1044610 1175575 := bstep (se 1 (by rfl) ⟨881681, by rfl⟩ : syracuseStep 1175575 = 1763363) B1763363
theorem B5304365 : Blo 1044610 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B1568843 : Blo 1044610 1568843 := bstep (se 1 (by rfl) ⟨1176632, by rfl⟩ : syracuseStep 1568843 = 2353265) B2353265
theorem B1568855 : Blo 1044610 1568855 := bstep (se 1 (by rfl) ⟨1176641, by rfl⟩ : syracuseStep 1568855 = 2353283) B2353283
theorem B1044619 : Blo 1044610 1044619 := bstep (se 1 (by rfl) ⟨783464, by rfl⟩ : syracuseStep 1044619 = 1566929) B1566929
theorem B1044631 : Blo 1044610 1044631 := bstep (se 1 (by rfl) ⟨783473, by rfl⟩ : syracuseStep 1044631 = 1566947) B1566947
theorem B1568921 : Blo 1044610 1568921 := bstep (se 2 (by rfl) ⟨588345, by rfl⟩ : syracuseStep 1568921 = 1176691) B1176691
theorem B2355353 : Blo 1044610 2355353 := bstep (se 2 (by rfl) ⟨883257, by rfl⟩ : syracuseStep 2355353 = 1766515) B1766515
theorem B1044651 : Blo 1044610 1044651 := bstep (se 1 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 1044651 = 1566977) B1566977
theorem B1044663 : Blo 1044610 1044663 := bstep (se 1 (by rfl) ⟨783497, by rfl⟩ : syracuseStep 1044663 = 1566995) B1566995
theorem B1044683 : Blo 1044610 1044683 := bstep (se 1 (by rfl) ⟨783512, by rfl⟩ : syracuseStep 1044683 = 1567025) B1567025
theorem B1175755 : Blo 1044610 1175755 := bstep (se 1 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 1175755 = 1763633) B1763633
theorem B1044695 : Blo 1044610 1044695 := bstep (se 1 (by rfl) ⟨783521, by rfl⟩ : syracuseStep 1044695 = 1567043) B1567043
theorem B1044715 : Blo 1044610 1044715 := bstep (se 1 (by rfl) ⟨783536, by rfl⟩ : syracuseStep 1044715 = 1567073) B1567073
theorem B2355443 : Blo 1044610 2355443 := bstep (se 1 (by rfl) ⟨1766582, by rfl⟩ : syracuseStep 2355443 = 3533165) B3533165
theorem B1044727 : Blo 1044610 1044727 := bstep (se 1 (by rfl) ⟨783545, by rfl⟩ : syracuseStep 1044727 = 1567091) B1567091
theorem B1044747 : Blo 1044610 1044747 := bstep (se 1 (by rfl) ⟨783560, by rfl⟩ : syracuseStep 1044747 = 1567121) B1567121
theorem B1569035 : Blo 1044610 1569035 := bstep (se 1 (by rfl) ⟨1176776, by rfl⟩ : syracuseStep 1569035 = 2353553) B2353553
theorem B1044759 : Blo 1044610 1044759 := bstep (se 1 (by rfl) ⟨783569, by rfl⟩ : syracuseStep 1044759 = 1567139) B1567139
theorem B1569047 : Blo 1044610 1569047 := bstep (se 1 (by rfl) ⟨1176785, by rfl⟩ : syracuseStep 1569047 = 2353571) B2353571
theorem B2355479 : Blo 1044610 2355479 := bstep (se 1 (by rfl) ⟨1766609, by rfl⟩ : syracuseStep 2355479 = 3533219) B3533219
theorem B2650391 : Blo 1044610 2650391 := bstep (se 1 (by rfl) ⟨1987793, by rfl⟩ : syracuseStep 2650391 = 3975587) B3975587
theorem B1044779 : Blo 1044610 1044779 := bstep (se 1 (by rfl) ⟨783584, by rfl⟩ : syracuseStep 1044779 = 1567169) B1567169
theorem B2388275 : Blo 1044610 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1044791 : Blo 1044610 1044791 := bstep (se 1 (by rfl) ⟨783593, by rfl⟩ : syracuseStep 1044791 = 1567187) B1567187
theorem B1175863 : Blo 1044610 1175863 := bstep (se 1 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 1175863 = 1763795) B1763795
theorem B1044811 : Blo 1044610 1044811 := bstep (se 1 (by rfl) ⟨783608, by rfl⟩ : syracuseStep 1044811 = 1567217) B1567217
theorem B1044823 : Blo 1044610 1044823 := bstep (se 1 (by rfl) ⟨783617, by rfl⟩ : syracuseStep 1044823 = 1567235) B1567235
theorem B1569113 : Blo 1044610 1569113 := bstep (se 2 (by rfl) ⟨588417, by rfl⟩ : syracuseStep 1569113 = 1176835) B1176835
theorem B1044843 : Blo 1044610 1044843 := bstep (se 1 (by rfl) ⟨783632, by rfl⟩ : syracuseStep 1044843 = 1567265) B1567265
theorem B1044855 : Blo 1044610 1044855 := bstep (se 1 (by rfl) ⟨783641, by rfl⟩ : syracuseStep 1044855 = 1567283) B1567283
theorem B1044875 : Blo 1044610 1044875 := bstep (se 1 (by rfl) ⟨783656, by rfl⟩ : syracuseStep 1044875 = 1567313) B1567313
theorem B1044887 : Blo 1044610 1044887 := bstep (se 1 (by rfl) ⟨783665, by rfl⟩ : syracuseStep 1044887 = 1567331) B1567331
theorem B1044907 : Blo 1044610 1044907 := bstep (se 1 (by rfl) ⟨783680, by rfl⟩ : syracuseStep 1044907 = 1567361) B1567361
theorem B1044919 : Blo 1044610 1044919 := bstep (se 1 (by rfl) ⟨783689, by rfl⟩ : syracuseStep 1044919 = 1567379) B1567379
theorem B1044939 : Blo 1044610 1044939 := bstep (se 1 (by rfl) ⟨783704, by rfl⟩ : syracuseStep 1044939 = 1567409) B1567409
theorem B1569227 : Blo 1044610 1569227 := bstep (se 1 (by rfl) ⟨1176920, by rfl⟩ : syracuseStep 1569227 = 2353841) B2353841
theorem B2355659 : Blo 1044610 2355659 := bstep (se 1 (by rfl) ⟨1766744, by rfl⟩ : syracuseStep 2355659 = 3533489) B3533489
theorem B1044951 : Blo 1044610 1044951 := bstep (se 1 (by rfl) ⟨783713, by rfl⟩ : syracuseStep 1044951 = 1567427) B1567427
theorem B1569239 : Blo 1044610 1569239 := bstep (se 1 (by rfl) ⟨1176929, by rfl⟩ : syracuseStep 1569239 = 2353859) B2353859
theorem B1765847 : Blo 1044610 1765847 := bstep (se 1 (by rfl) ⟨1324385, by rfl⟩ : syracuseStep 1765847 = 2648771) B2648771
theorem B3535325 : Blo 1044610 3535325 := bstep (se 3 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 3535325 = 1325747) B1325747
theorem B1044971 : Blo 1044610 1044971 := bstep (se 1 (by rfl) ⟨783728, by rfl⟩ : syracuseStep 1044971 = 1567457) B1567457
theorem B1176043 : Blo 1044610 1176043 := bstep (se 1 (by rfl) ⟨882032, by rfl⟩ : syracuseStep 1176043 = 1764065) B1764065
theorem B1044983 : Blo 1044610 1044983 := bstep (se 1 (by rfl) ⟨783737, by rfl⟩ : syracuseStep 1044983 = 1567475) B1567475
theorem B2355713 : Blo 1044610 2355713 := bstep (se 2 (by rfl) ⟨883392, by rfl⟩ : syracuseStep 2355713 = 1766785) B1766785
theorem B1045003 : Blo 1044610 1045003 := bstep (se 1 (by rfl) ⟨783752, by rfl⟩ : syracuseStep 1045003 = 1567505) B1567505
theorem B1045015 : Blo 1044610 1045015 := bstep (se 1 (by rfl) ⟨783761, by rfl⟩ : syracuseStep 1045015 = 1567523) B1567523
theorem B1569305 : Blo 1044610 1569305 := bstep (se 2 (by rfl) ⟨588489, by rfl⟩ : syracuseStep 1569305 = 1176979) B1176979
theorem B1045035 : Blo 1044610 1045035 := bstep (se 1 (by rfl) ⟨783776, by rfl⟩ : syracuseStep 1045035 = 1567553) B1567553
theorem B1045047 : Blo 1044610 1045047 := bstep (se 1 (by rfl) ⟨783785, by rfl⟩ : syracuseStep 1045047 = 1567571) B1567571
theorem B1045067 : Blo 1044610 1045067 := bstep (se 1 (by rfl) ⟨783800, by rfl⟩ : syracuseStep 1045067 = 1567601) B1567601
theorem B1045079 : Blo 1044610 1045079 := bstep (se 1 (by rfl) ⟨783809, by rfl⟩ : syracuseStep 1045079 = 1567619) B1567619
theorem B1176151 : Blo 1044610 1176151 := bstep (se 1 (by rfl) ⟨882113, by rfl⟩ : syracuseStep 1176151 = 1764227) B1764227
theorem B1765975 : Blo 1044610 1765975 := bstep (se 1 (by rfl) ⟨1324481, by rfl⟩ : syracuseStep 1765975 = 2648963) B2648963
theorem B7369309 : Blo 1044610 7369309 := bstep (se 3 (by rfl) ⟨1381745, by rfl⟩ : syracuseStep 7369309 = 2763491) B2763491
theorem B1045099 : Blo 1044610 1045099 := bstep (se 1 (by rfl) ⟨783824, by rfl⟩ : syracuseStep 1045099 = 1567649) B1567649
theorem B1045111 : Blo 1044610 1045111 := bstep (se 1 (by rfl) ⟨783833, by rfl⟩ : syracuseStep 1045111 = 1567667) B1567667
theorem B1045131 : Blo 1044610 1045131 := bstep (se 1 (by rfl) ⟨783848, by rfl⟩ : syracuseStep 1045131 = 1567697) B1567697
theorem B1569419 : Blo 1044610 1569419 := bstep (se 1 (by rfl) ⟨1177064, by rfl⟩ : syracuseStep 1569419 = 2354129) B2354129
theorem B1045143 : Blo 1044610 1045143 := bstep (se 1 (by rfl) ⟨783857, by rfl⟩ : syracuseStep 1045143 = 1567715) B1567715
theorem B1569431 : Blo 1044610 1569431 := bstep (se 1 (by rfl) ⟨1177073, by rfl⟩ : syracuseStep 1569431 = 2354147) B2354147
theorem B2388631 : Blo 1044610 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B1045163 : Blo 1044610 1045163 := bstep (se 1 (by rfl) ⟨783872, by rfl⟩ : syracuseStep 1045163 = 1567745) B1567745
theorem B1045175 : Blo 1044610 1045175 := bstep (se 1 (by rfl) ⟨783881, by rfl⟩ : syracuseStep 1045175 = 1567763) B1567763
theorem B1045195 : Blo 1044610 1045195 := bstep (se 1 (by rfl) ⟨783896, by rfl⟩ : syracuseStep 1045195 = 1567793) B1567793
theorem B1045207 : Blo 1044610 1045207 := bstep (se 1 (by rfl) ⟨783905, by rfl⟩ : syracuseStep 1045207 = 1567811) B1567811
theorem B1569497 : Blo 1044610 1569497 := bstep (se 2 (by rfl) ⟨588561, by rfl⟩ : syracuseStep 1569497 = 1177123) B1177123
theorem B2355929 : Blo 1044610 2355929 := bstep (se 2 (by rfl) ⟨883473, by rfl⟩ : syracuseStep 2355929 = 1766947) B1766947
theorem B1045227 : Blo 1044610 1045227 := bstep (se 1 (by rfl) ⟨783920, by rfl⟩ : syracuseStep 1045227 = 1567841) B1567841
theorem B1045239 : Blo 1044610 1045239 := bstep (se 1 (by rfl) ⟨783929, by rfl⟩ : syracuseStep 1045239 = 1567859) B1567859
theorem B1045259 : Blo 1044610 1045259 := bstep (se 1 (by rfl) ⟨783944, by rfl⟩ : syracuseStep 1045259 = 1567889) B1567889
theorem B1176331 : Blo 1044610 1176331 := bstep (se 1 (by rfl) ⟨882248, by rfl⟩ : syracuseStep 1176331 = 1764497) B1764497
theorem B5960465 : Blo 1044610 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B1045271 : Blo 1044610 1045271 := bstep (se 1 (by rfl) ⟨783953, by rfl⟩ : syracuseStep 1045271 = 1567907) B1567907
theorem B1045291 : Blo 1044610 1045291 := bstep (se 1 (by rfl) ⟨783968, by rfl⟩ : syracuseStep 1045291 = 1567937) B1567937
theorem B2356019 : Blo 1044610 2356019 := bstep (se 1 (by rfl) ⟨1767014, by rfl⟩ : syracuseStep 2356019 = 3534029) B3534029
theorem B1045303 : Blo 1044610 1045303 := bstep (se 1 (by rfl) ⟨783977, by rfl⟩ : syracuseStep 1045303 = 1567955) B1567955
theorem B1045323 : Blo 1044610 1045323 := bstep (se 1 (by rfl) ⟨783992, by rfl⟩ : syracuseStep 1045323 = 1567985) B1567985
theorem B1569611 : Blo 1044610 1569611 := bstep (se 1 (by rfl) ⟨1177208, by rfl⟩ : syracuseStep 1569611 = 2354417) B2354417
theorem B1045335 : Blo 1044610 1045335 := bstep (se 1 (by rfl) ⟨784001, by rfl⟩ : syracuseStep 1045335 = 1568003) B1568003
theorem B1569623 : Blo 1044610 1569623 := bstep (se 1 (by rfl) ⟨1177217, by rfl⟩ : syracuseStep 1569623 = 2354435) B2354435
theorem B2356055 : Blo 1044610 2356055 := bstep (se 1 (by rfl) ⟨1767041, by rfl⟩ : syracuseStep 2356055 = 3534083) B3534083
theorem B1045355 : Blo 1044610 1045355 := bstep (se 1 (by rfl) ⟨784016, by rfl⟩ : syracuseStep 1045355 = 1568033) B1568033
theorem B1045367 : Blo 1044610 1045367 := bstep (se 1 (by rfl) ⟨784025, by rfl⟩ : syracuseStep 1045367 = 1568051) B1568051
theorem B1176439 : Blo 1044610 1176439 := bstep (se 1 (by rfl) ⟨882329, by rfl⟩ : syracuseStep 1176439 = 1764659) B1764659
theorem B1045387 : Blo 1044610 1045387 := bstep (se 1 (by rfl) ⟨784040, by rfl⟩ : syracuseStep 1045387 = 1568081) B1568081
theorem B1045399 : Blo 1044610 1045399 := bstep (se 1 (by rfl) ⟨784049, by rfl⟩ : syracuseStep 1045399 = 1568099) B1568099
theorem B1569689 : Blo 1044610 1569689 := bstep (se 2 (by rfl) ⟨588633, by rfl⟩ : syracuseStep 1569689 = 1177267) B1177267
theorem B1045419 : Blo 1044610 1045419 := bstep (se 1 (by rfl) ⟨784064, by rfl⟩ : syracuseStep 1045419 = 1568129) B1568129
theorem B1045431 : Blo 1044610 1045431 := bstep (se 1 (by rfl) ⟨784073, by rfl⟩ : syracuseStep 1045431 = 1568147) B1568147
theorem B1045451 : Blo 1044610 1045451 := bstep (se 1 (by rfl) ⟨784088, by rfl⟩ : syracuseStep 1045451 = 1568177) B1568177
theorem B1045463 : Blo 1044610 1045463 := bstep (se 1 (by rfl) ⟨784097, by rfl⟩ : syracuseStep 1045463 = 1568195) B1568195
theorem B1045483 : Blo 1044610 1045483 := bstep (se 1 (by rfl) ⟨784112, by rfl⟩ : syracuseStep 1045483 = 1568225) B1568225
theorem B1045495 : Blo 1044610 1045495 := bstep (se 1 (by rfl) ⟨784121, by rfl⟩ : syracuseStep 1045495 = 1568243) B1568243
theorem B1045515 : Blo 1044610 1045515 := bstep (se 1 (by rfl) ⟨784136, by rfl⟩ : syracuseStep 1045515 = 1568273) B1568273
theorem B1569803 : Blo 1044610 1569803 := bstep (se 1 (by rfl) ⟨1177352, by rfl⟩ : syracuseStep 1569803 = 2354705) B2354705
theorem B2356235 : Blo 1044610 2356235 := bstep (se 1 (by rfl) ⟨1767176, by rfl⟩ : syracuseStep 2356235 = 3534353) B3534353
theorem B1045527 : Blo 1044610 1045527 := bstep (se 1 (by rfl) ⟨784145, by rfl⟩ : syracuseStep 1045527 = 1568291) B1568291
theorem B1569815 : Blo 1044610 1569815 := bstep (se 1 (by rfl) ⟨1177361, by rfl⟩ : syracuseStep 1569815 = 2354723) B2354723
theorem B1045547 : Blo 1044610 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B1176619 : Blo 1044610 1176619 := bstep (se 1 (by rfl) ⟨882464, by rfl⟩ : syracuseStep 1176619 = 1764929) B1764929
theorem B1045559 : Blo 1044610 1045559 := bstep (se 1 (by rfl) ⟨784169, by rfl⟩ : syracuseStep 1045559 = 1568339) B1568339
theorem B2356289 : Blo 1044610 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B2651201 : Blo 1044610 2651201 := bstep (se 2 (by rfl) ⟨994200, by rfl⟩ : syracuseStep 2651201 = 1988401) B1988401
theorem B1340491 : Blo 1044610 1340491 := bstep (se 1 (by rfl) ⟨1005368, by rfl⟩ : syracuseStep 1340491 = 2010737) B2010737
theorem B1045579 : Blo 1044610 1045579 := bstep (se 1 (by rfl) ⟨784184, by rfl⟩ : syracuseStep 1045579 = 1568369) B1568369
theorem B1045591 : Blo 1044610 1045591 := bstep (se 1 (by rfl) ⟨784193, by rfl⟩ : syracuseStep 1045591 = 1568387) B1568387
theorem B1569881 : Blo 1044610 1569881 := bstep (se 2 (by rfl) ⟨588705, by rfl⟩ : syracuseStep 1569881 = 1177411) B1177411
theorem B1045611 : Blo 1044610 1045611 := bstep (se 1 (by rfl) ⟨784208, by rfl⟩ : syracuseStep 1045611 = 1568417) B1568417
theorem B1045623 : Blo 1044610 1045623 := bstep (se 1 (by rfl) ⟨784217, by rfl⟩ : syracuseStep 1045623 = 1568435) B1568435
theorem B1045643 : Blo 1044610 1045643 := bstep (se 1 (by rfl) ⟨784232, by rfl⟩ : syracuseStep 1045643 = 1568465) B1568465
theorem B1045655 : Blo 1044610 1045655 := bstep (se 1 (by rfl) ⟨784241, by rfl⟩ : syracuseStep 1045655 = 1568483) B1568483
theorem B1176727 : Blo 1044610 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B1045675 : Blo 1044610 1045675 := bstep (se 1 (by rfl) ⟨784256, by rfl⟩ : syracuseStep 1045675 = 1568513) B1568513
theorem B1045687 : Blo 1044610 1045687 := bstep (se 1 (by rfl) ⟨784265, by rfl⟩ : syracuseStep 1045687 = 1568531) B1568531
theorem B1045707 : Blo 1044610 1045707 := bstep (se 1 (by rfl) ⟨784280, by rfl⟩ : syracuseStep 1045707 = 1568561) B1568561
theorem B1569995 : Blo 1044610 1569995 := bstep (se 1 (by rfl) ⟨1177496, by rfl⟩ : syracuseStep 1569995 = 2354993) B2354993
theorem B1766603 : Blo 1044610 1766603 := bstep (se 1 (by rfl) ⟨1324952, by rfl⟩ : syracuseStep 1766603 = 2649905) B2649905
theorem B1045719 : Blo 1044610 1045719 := bstep (se 1 (by rfl) ⟨784289, by rfl⟩ : syracuseStep 1045719 = 1568579) B1568579
theorem B1570007 : Blo 1044610 1570007 := bstep (se 1 (by rfl) ⟨1177505, by rfl⟩ : syracuseStep 1570007 = 2355011) B2355011
theorem B1045739 : Blo 1044610 1045739 := bstep (se 1 (by rfl) ⟨784304, by rfl⟩ : syracuseStep 1045739 = 1568609) B1568609
theorem B1045751 : Blo 1044610 1045751 := bstep (se 1 (by rfl) ⟨784313, by rfl⟩ : syracuseStep 1045751 = 1568627) B1568627
theorem B1045771 : Blo 1044610 1045771 := bstep (se 1 (by rfl) ⟨784328, by rfl⟩ : syracuseStep 1045771 = 1568657) B1568657
theorem B1045783 : Blo 1044610 1045783 := bstep (se 1 (by rfl) ⟨784337, by rfl⟩ : syracuseStep 1045783 = 1568675) B1568675
theorem B1570073 : Blo 1044610 1570073 := bstep (se 2 (by rfl) ⟨588777, by rfl⟩ : syracuseStep 1570073 = 1177555) B1177555
theorem B2356505 : Blo 1044610 2356505 := bstep (se 2 (by rfl) ⟨883689, by rfl⟩ : syracuseStep 2356505 = 1767379) B1767379
theorem B1045803 : Blo 1044610 1045803 := bstep (se 1 (by rfl) ⟨784352, by rfl⟩ : syracuseStep 1045803 = 1568705) B1568705
theorem B1045815 : Blo 1044610 1045815 := bstep (se 1 (by rfl) ⟨784361, by rfl⟩ : syracuseStep 1045815 = 1568723) B1568723
theorem B1045835 : Blo 1044610 1045835 := bstep (se 1 (by rfl) ⟨784376, by rfl⟩ : syracuseStep 1045835 = 1568753) B1568753
theorem B1176907 : Blo 1044610 1176907 := bstep (se 1 (by rfl) ⟨882680, by rfl⟩ : syracuseStep 1176907 = 1765361) B1765361
theorem B1766731 : Blo 1044610 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B1045847 : Blo 1044610 1045847 := bstep (se 1 (by rfl) ⟨784385, by rfl⟩ : syracuseStep 1045847 = 1568771) B1568771
theorem B1045867 : Blo 1044610 1045867 := bstep (se 1 (by rfl) ⟨784400, by rfl⟩ : syracuseStep 1045867 = 1568801) B1568801
theorem B2356595 : Blo 1044610 2356595 := bstep (se 1 (by rfl) ⟨1767446, by rfl⟩ : syracuseStep 2356595 = 3534893) B3534893
theorem B1045879 : Blo 1044610 1045879 := bstep (se 1 (by rfl) ⟨784409, by rfl⟩ : syracuseStep 1045879 = 1568819) B1568819
theorem B1045899 : Blo 1044610 1045899 := bstep (se 1 (by rfl) ⟨784424, by rfl⟩ : syracuseStep 1045899 = 1568849) B1568849
theorem B1570187 : Blo 1044610 1570187 := bstep (se 1 (by rfl) ⟨1177640, by rfl⟩ : syracuseStep 1570187 = 2355281) B2355281
theorem B2356631 : Blo 1044610 2356631 := bstep (se 1 (by rfl) ⟨1767473, by rfl⟩ : syracuseStep 2356631 = 3534947) B3534947
theorem B1045911 : Blo 1044610 1045911 := bstep (se 1 (by rfl) ⟨784433, by rfl⟩ : syracuseStep 1045911 = 1568867) B1568867
theorem B1570199 : Blo 1044610 1570199 := bstep (se 1 (by rfl) ⟨1177649, by rfl⟩ : syracuseStep 1570199 = 2355299) B2355299
theorem B1045931 : Blo 1044610 1045931 := bstep (se 1 (by rfl) ⟨784448, by rfl⟩ : syracuseStep 1045931 = 1568897) B1568897
theorem B1045943 : Blo 1044610 1045943 := bstep (se 1 (by rfl) ⟨784457, by rfl⟩ : syracuseStep 1045943 = 1568915) B1568915
theorem B1177015 : Blo 1044610 1177015 := bstep (se 1 (by rfl) ⟨882761, by rfl⟩ : syracuseStep 1177015 = 1765523) B1765523
theorem B1045963 : Blo 1044610 1045963 := bstep (se 1 (by rfl) ⟨784472, by rfl⟩ : syracuseStep 1045963 = 1568945) B1568945
theorem B1045975 : Blo 1044610 1045975 := bstep (se 1 (by rfl) ⟨784481, by rfl⟩ : syracuseStep 1045975 = 1568963) B1568963
theorem B1570265 : Blo 1044610 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B1766873 : Blo 1044610 1766873 := bstep (se 2 (by rfl) ⟨662577, by rfl⟩ : syracuseStep 1766873 = 1325155) B1325155
theorem B1045995 : Blo 1044610 1045995 := bstep (se 1 (by rfl) ⟨784496, by rfl⟩ : syracuseStep 1045995 = 1568993) B1568993
theorem B1046007 : Blo 1044610 1046007 := bstep (se 1 (by rfl) ⟨784505, by rfl⟩ : syracuseStep 1046007 = 1569011) B1569011
theorem B1046027 : Blo 1044610 1046027 := bstep (se 1 (by rfl) ⟨784520, by rfl⟩ : syracuseStep 1046027 = 1569041) B1569041
theorem B1046039 : Blo 1044610 1046039 := bstep (se 1 (by rfl) ⟨784529, by rfl⟩ : syracuseStep 1046039 = 1569059) B1569059
theorem B1046059 : Blo 1044610 1046059 := bstep (se 1 (by rfl) ⟨784544, by rfl⟩ : syracuseStep 1046059 = 1569089) B1569089
theorem B1046071 : Blo 1044610 1046071 := bstep (se 1 (by rfl) ⟨784553, by rfl⟩ : syracuseStep 1046071 = 1569107) B1569107
theorem B2356811 : Blo 1044610 2356811 := bstep (se 1 (by rfl) ⟨1767608, by rfl⟩ : syracuseStep 2356811 = 3535217) B3535217
theorem B1046091 : Blo 1044610 1046091 := bstep (se 1 (by rfl) ⟨784568, by rfl⟩ : syracuseStep 1046091 = 1569137) B1569137
theorem B1570379 : Blo 1044610 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B3536459 : Blo 1044610 3536459 := bstep (se 1 (by rfl) ⟨2652344, by rfl⟩ : syracuseStep 3536459 = 5304689) B5304689
theorem B1046103 : Blo 1044610 1046103 := bstep (se 1 (by rfl) ⟨784577, by rfl⟩ : syracuseStep 1046103 = 1569155) B1569155
theorem B1570391 : Blo 1044610 1570391 := bstep (se 1 (by rfl) ⟨1177793, by rfl⟩ : syracuseStep 1570391 = 2355587) B2355587
theorem B1767001 : Blo 1044610 1767001 := bstep (se 2 (by rfl) ⟨662625, by rfl⟩ : syracuseStep 1767001 = 1325251) B1325251
theorem B2651737 : Blo 1044610 2651737 := bstep (se 2 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 2651737 = 1988803) B1988803
theorem B1046123 : Blo 1044610 1046123 := bstep (se 1 (by rfl) ⟨784592, by rfl⟩ : syracuseStep 1046123 = 1569185) B1569185
theorem B1177195 : Blo 1044610 1177195 := bstep (se 1 (by rfl) ⟨882896, by rfl⟩ : syracuseStep 1177195 = 1765793) B1765793
theorem B1046135 : Blo 1044610 1046135 := bstep (se 1 (by rfl) ⟨784601, by rfl⟩ : syracuseStep 1046135 = 1569203) B1569203
theorem B2356865 : Blo 1044610 2356865 := bstep (se 2 (by rfl) ⟨883824, by rfl⟩ : syracuseStep 2356865 = 1767649) B1767649
theorem B1046155 : Blo 1044610 1046155 := bstep (se 1 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 1046155 = 1569233) B1569233
theorem B1046167 : Blo 1044610 1046167 := bstep (se 1 (by rfl) ⟨784625, by rfl⟩ : syracuseStep 1046167 = 1569251) B1569251
theorem B1570457 : Blo 1044610 1570457 := bstep (se 2 (by rfl) ⟨588921, by rfl⟩ : syracuseStep 1570457 = 1177843) B1177843
theorem B1046187 : Blo 1044610 1046187 := bstep (se 1 (by rfl) ⟨784640, by rfl⟩ : syracuseStep 1046187 = 1569281) B1569281
theorem B1046199 : Blo 1044610 1046199 := bstep (se 1 (by rfl) ⟨784649, by rfl⟩ : syracuseStep 1046199 = 1569299) B1569299
theorem B1046219 : Blo 1044610 1046219 := bstep (se 1 (by rfl) ⟨784664, by rfl⟩ : syracuseStep 1046219 = 1569329) B1569329
theorem B1046231 : Blo 1044610 1046231 := bstep (se 1 (by rfl) ⟨784673, by rfl⟩ : syracuseStep 1046231 = 1569347) B1569347
theorem B1177303 : Blo 1044610 1177303 := bstep (se 1 (by rfl) ⟨882977, by rfl⟩ : syracuseStep 1177303 = 1765955) B1765955
theorem B1046251 : Blo 1044610 1046251 := bstep (se 1 (by rfl) ⟨784688, by rfl⟩ : syracuseStep 1046251 = 1569377) B1569377
theorem B1046263 : Blo 1044610 1046263 := bstep (se 1 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 1046263 = 1569395) B1569395
theorem B1046283 : Blo 1044610 1046283 := bstep (se 1 (by rfl) ⟨784712, by rfl⟩ : syracuseStep 1046283 = 1569425) B1569425
theorem B1570571 : Blo 1044610 1570571 := bstep (se 1 (by rfl) ⟨1177928, by rfl⟩ : syracuseStep 1570571 = 2355857) B2355857
theorem B1046295 : Blo 1044610 1046295 := bstep (se 1 (by rfl) ⟨784721, by rfl⟩ : syracuseStep 1046295 = 1569443) B1569443
theorem B1570583 : Blo 1044610 1570583 := bstep (se 1 (by rfl) ⟨1177937, by rfl⟩ : syracuseStep 1570583 = 2355875) B2355875
theorem B1046315 : Blo 1044610 1046315 := bstep (se 1 (by rfl) ⟨784736, by rfl⟩ : syracuseStep 1046315 = 1569473) B1569473
theorem B1046327 : Blo 1044610 1046327 := bstep (se 1 (by rfl) ⟨784745, by rfl⟩ : syracuseStep 1046327 = 1569491) B1569491
theorem B1046347 : Blo 1044610 1046347 := bstep (se 1 (by rfl) ⟨784760, by rfl⟩ : syracuseStep 1046347 = 1569521) B1569521
theorem B1046359 : Blo 1044610 1046359 := bstep (se 1 (by rfl) ⟨784769, by rfl⟩ : syracuseStep 1046359 = 1569539) B1569539
theorem B3536729 : Blo 1044610 3536729 := bstep (se 2 (by rfl) ⟨1326273, by rfl⟩ : syracuseStep 3536729 = 2652547) B2652547
theorem B3766105 : Blo 1044610 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B1570649 : Blo 1044610 1570649 := bstep (se 2 (by rfl) ⟨588993, by rfl⟩ : syracuseStep 1570649 = 1177987) B1177987
theorem B2357081 : Blo 1044610 2357081 := bstep (se 2 (by rfl) ⟨883905, by rfl⟩ : syracuseStep 2357081 = 1767811) B1767811
theorem B1046379 : Blo 1044610 1046379 := bstep (se 1 (by rfl) ⟨784784, by rfl⟩ : syracuseStep 1046379 = 1569569) B1569569
theorem B1046391 : Blo 1044610 1046391 := bstep (se 1 (by rfl) ⟨784793, by rfl⟩ : syracuseStep 1046391 = 1569587) B1569587
theorem B1046411 : Blo 1044610 1046411 := bstep (se 1 (by rfl) ⟨784808, by rfl⟩ : syracuseStep 1046411 = 1569617) B1569617
theorem B1177483 : Blo 1044610 1177483 := bstep (se 1 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 1177483 = 1766225) B1766225
theorem B1046423 : Blo 1044610 1046423 := bstep (se 1 (by rfl) ⟨784817, by rfl⟩ : syracuseStep 1046423 = 1569635) B1569635
theorem B1046443 : Blo 1044610 1046443 := bstep (se 1 (by rfl) ⟨784832, by rfl⟩ : syracuseStep 1046443 = 1569665) B1569665
theorem B2357171 : Blo 1044610 2357171 := bstep (se 1 (by rfl) ⟨1767878, by rfl⟩ : syracuseStep 2357171 = 3535757) B3535757
theorem B1046455 : Blo 1044610 1046455 := bstep (se 1 (by rfl) ⟨784841, by rfl⟩ : syracuseStep 1046455 = 1569683) B1569683
theorem B3766219 : Blo 1044610 3766219 := bstep (se 1 (by rfl) ⟨2824664, by rfl⟩ : syracuseStep 3766219 = 5649329) B5649329
theorem B1046475 : Blo 1044610 1046475 := bstep (se 1 (by rfl) ⟨784856, by rfl⟩ : syracuseStep 1046475 = 1569713) B1569713
theorem B1570763 : Blo 1044610 1570763 := bstep (se 1 (by rfl) ⟨1178072, by rfl⟩ : syracuseStep 1570763 = 2356145) B2356145
theorem B1046487 : Blo 1044610 1046487 := bstep (se 1 (by rfl) ⟨784865, by rfl⟩ : syracuseStep 1046487 = 1569731) B1569731
theorem B1570775 : Blo 1044610 1570775 := bstep (se 1 (by rfl) ⟨1178081, by rfl⟩ : syracuseStep 1570775 = 2356163) B2356163
theorem B2357207 : Blo 1044610 2357207 := bstep (se 1 (by rfl) ⟨1767905, by rfl⟩ : syracuseStep 2357207 = 3535811) B3535811
theorem B1046507 : Blo 1044610 1046507 := bstep (se 1 (by rfl) ⟨784880, by rfl⟩ : syracuseStep 1046507 = 1569761) B1569761
theorem B1046519 : Blo 1044610 1046519 := bstep (se 1 (by rfl) ⟨784889, by rfl⟩ : syracuseStep 1046519 = 1569779) B1569779
theorem B1177591 : Blo 1044610 1177591 := bstep (se 1 (by rfl) ⟨883193, by rfl⟩ : syracuseStep 1177591 = 1766387) B1766387
theorem B1046539 : Blo 1044610 1046539 := bstep (se 1 (by rfl) ⟨784904, by rfl⟩ : syracuseStep 1046539 = 1569809) B1569809
theorem B1046551 : Blo 1044610 1046551 := bstep (se 1 (by rfl) ⟨784913, by rfl⟩ : syracuseStep 1046551 = 1569827) B1569827
theorem B1570841 : Blo 1044610 1570841 := bstep (se 2 (by rfl) ⟨589065, by rfl⟩ : syracuseStep 1570841 = 1178131) B1178131
theorem B1046571 : Blo 1044610 1046571 := bstep (se 1 (by rfl) ⟨784928, by rfl⟩ : syracuseStep 1046571 = 1569857) B1569857
theorem B1046583 : Blo 1044610 1046583 := bstep (se 1 (by rfl) ⟨784937, by rfl⟩ : syracuseStep 1046583 = 1569875) B1569875
theorem B3766337 : Blo 1044610 3766337 := bstep (se 2 (by rfl) ⟨1412376, by rfl⟩ : syracuseStep 3766337 = 2824753) B2824753
theorem B1046603 : Blo 1044610 1046603 := bstep (se 1 (by rfl) ⟨784952, by rfl⟩ : syracuseStep 1046603 = 1569905) B1569905
theorem B1046615 : Blo 1044610 1046615 := bstep (se 1 (by rfl) ⟨784961, by rfl⟩ : syracuseStep 1046615 = 1569923) B1569923
theorem B6715493 : Blo 1044610 6715493 := bstep (se 4 (by rfl) ⟨629577, by rfl⟩ : syracuseStep 6715493 = 1259155) B1259155
theorem B1046635 : Blo 1044610 1046635 := bstep (se 1 (by rfl) ⟨784976, by rfl⟩ : syracuseStep 1046635 = 1569953) B1569953
theorem B1046647 : Blo 1044610 1046647 := bstep (se 1 (by rfl) ⟨784985, by rfl⟩ : syracuseStep 1046647 = 1569971) B1569971
theorem B1046667 : Blo 1044610 1046667 := bstep (se 1 (by rfl) ⟨785000, by rfl⟩ : syracuseStep 1046667 = 1570001) B1570001
theorem B1570955 : Blo 1044610 1570955 := bstep (se 1 (by rfl) ⟨1178216, by rfl⟩ : syracuseStep 1570955 = 2356433) B2356433
theorem B2357387 : Blo 1044610 2357387 := bstep (se 1 (by rfl) ⟨1768040, by rfl⟩ : syracuseStep 2357387 = 3536081) B3536081
theorem B1046679 : Blo 1044610 1046679 := bstep (se 1 (by rfl) ⟨785009, by rfl⟩ : syracuseStep 1046679 = 1570019) B1570019
theorem B1570967 : Blo 1044610 1570967 := bstep (se 1 (by rfl) ⟨1178225, by rfl⟩ : syracuseStep 1570967 = 2356451) B2356451
theorem B1767575 : Blo 1044610 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B1046699 : Blo 1044610 1046699 := bstep (se 1 (by rfl) ⟨785024, by rfl⟩ : syracuseStep 1046699 = 1570049) B1570049
theorem B1177771 : Blo 1044610 1177771 := bstep (se 1 (by rfl) ⟨883328, by rfl⟩ : syracuseStep 1177771 = 1766657) B1766657
theorem B1046711 : Blo 1044610 1046711 := bstep (se 1 (by rfl) ⟨785033, by rfl⟩ : syracuseStep 1046711 = 1570067) B1570067
theorem B2357441 : Blo 1044610 2357441 := bstep (se 2 (by rfl) ⟨884040, by rfl⟩ : syracuseStep 2357441 = 1768081) B1768081
theorem B1046731 : Blo 1044610 1046731 := bstep (se 1 (by rfl) ⟨785048, by rfl⟩ : syracuseStep 1046731 = 1570097) B1570097
theorem B1046743 : Blo 1044610 1046743 := bstep (se 1 (by rfl) ⟨785057, by rfl⟩ : syracuseStep 1046743 = 1570115) B1570115
theorem B1571033 : Blo 1044610 1571033 := bstep (se 2 (by rfl) ⟨589137, by rfl⟩ : syracuseStep 1571033 = 1178275) B1178275
theorem B2980061 : Blo 1044610 2980061 := bstep (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) B1117523
theorem B1046763 : Blo 1044610 1046763 := bstep (se 1 (by rfl) ⟨785072, by rfl⟩ : syracuseStep 1046763 = 1570145) B1570145
theorem B1046775 : Blo 1044610 1046775 := bstep (se 1 (by rfl) ⟨785081, by rfl⟩ : syracuseStep 1046775 = 1570163) B1570163
theorem B1046795 : Blo 1044610 1046795 := bstep (se 1 (by rfl) ⟨785096, by rfl⟩ : syracuseStep 1046795 = 1570193) B1570193
theorem B1046807 : Blo 1044610 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B1177879 : Blo 1044610 1177879 := bstep (se 1 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 1177879 = 1766819) B1766819
theorem B1767703 : Blo 1044610 1767703 := bstep (se 1 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 1767703 = 2651555) B2651555
theorem B1046827 : Blo 1044610 1046827 := bstep (se 1 (by rfl) ⟨785120, by rfl⟩ : syracuseStep 1046827 = 1570241) B1570241
theorem B1046839 : Blo 1044610 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B1046859 : Blo 1044610 1046859 := bstep (se 1 (by rfl) ⟨785144, by rfl⟩ : syracuseStep 1046859 = 1570289) B1570289
theorem B1571147 : Blo 1044610 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B1046871 : Blo 1044610 1046871 := bstep (se 1 (by rfl) ⟨785153, by rfl⟩ : syracuseStep 1046871 = 1570307) B1570307
theorem B1571159 : Blo 1044610 1571159 := bstep (se 1 (by rfl) ⟨1178369, by rfl⟩ : syracuseStep 1571159 = 2356739) B2356739
theorem B1046891 : Blo 1044610 1046891 := bstep (se 1 (by rfl) ⟨785168, by rfl⟩ : syracuseStep 1046891 = 1570337) B1570337
theorem B1046903 : Blo 1044610 1046903 := bstep (se 1 (by rfl) ⟨785177, by rfl⟩ : syracuseStep 1046903 = 1570355) B1570355
theorem B1046923 : Blo 1044610 1046923 := bstep (se 1 (by rfl) ⟨785192, by rfl⟩ : syracuseStep 1046923 = 1570385) B1570385
theorem B1046935 : Blo 1044610 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B1571225 : Blo 1044610 1571225 := bstep (se 2 (by rfl) ⟨589209, by rfl⟩ : syracuseStep 1571225 = 1178419) B1178419
theorem B2357657 : Blo 1044610 2357657 := bstep (se 2 (by rfl) ⟨884121, by rfl⟩ : syracuseStep 2357657 = 1768243) B1768243
theorem B1046955 : Blo 1044610 1046955 := bstep (se 1 (by rfl) ⟨785216, by rfl⟩ : syracuseStep 1046955 = 1570433) B1570433
theorem B1046967 : Blo 1044610 1046967 := bstep (se 1 (by rfl) ⟨785225, by rfl⟩ : syracuseStep 1046967 = 1570451) B1570451
theorem B2980289 : Blo 1044610 2980289 := bstep (se 2 (by rfl) ⟨1117608, by rfl⟩ : syracuseStep 2980289 = 2235217) B2235217
theorem B1046987 : Blo 1044610 1046987 := bstep (se 1 (by rfl) ⟨785240, by rfl⟩ : syracuseStep 1046987 = 1570481) B1570481
theorem B1178059 : Blo 1044610 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B1046999 : Blo 1044610 1046999 := bstep (se 1 (by rfl) ⟨785249, by rfl⟩ : syracuseStep 1046999 = 1570499) B1570499
theorem B1047019 : Blo 1044610 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B2357747 : Blo 1044610 2357747 := bstep (se 1 (by rfl) ⟨1768310, by rfl⟩ : syracuseStep 2357747 = 3536621) B3536621
theorem B1047031 : Blo 1044610 1047031 := bstep (se 1 (by rfl) ⟨785273, by rfl⟩ : syracuseStep 1047031 = 1570547) B1570547
theorem B1047051 : Blo 1044610 1047051 := bstep (se 1 (by rfl) ⟨785288, by rfl⟩ : syracuseStep 1047051 = 1570577) B1570577
theorem B1571339 : Blo 1044610 1571339 := bstep (se 1 (by rfl) ⟨1178504, by rfl⟩ : syracuseStep 1571339 = 2357009) B2357009
theorem B1047063 : Blo 1044610 1047063 := bstep (se 1 (by rfl) ⟨785297, by rfl⟩ : syracuseStep 1047063 = 1570595) B1570595
theorem B1571351 : Blo 1044610 1571351 := bstep (se 1 (by rfl) ⟨1178513, by rfl⟩ : syracuseStep 1571351 = 2357027) B2357027
theorem B2357783 : Blo 1044610 2357783 := bstep (se 1 (by rfl) ⟨1768337, by rfl⟩ : syracuseStep 2357783 = 3536675) B3536675
theorem B3537431 : Blo 1044610 3537431 := bstep (se 1 (by rfl) ⟨2653073, by rfl⟩ : syracuseStep 3537431 = 5306147) B5306147
theorem B1047083 : Blo 1044610 1047083 := bstep (se 1 (by rfl) ⟨785312, by rfl⟩ : syracuseStep 1047083 = 1570625) B1570625
theorem B1047095 : Blo 1044610 1047095 := bstep (se 1 (by rfl) ⟨785321, by rfl⟩ : syracuseStep 1047095 = 1570643) B1570643
theorem B1178167 : Blo 1044610 1178167 := bstep (se 1 (by rfl) ⟨883625, by rfl⟩ : syracuseStep 1178167 = 1767251) B1767251
theorem B1047115 : Blo 1044610 1047115 := bstep (se 1 (by rfl) ⟨785336, by rfl⟩ : syracuseStep 1047115 = 1570673) B1570673
theorem B1047127 : Blo 1044610 1047127 := bstep (se 1 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 1047127 = 1570691) B1570691
theorem B1571417 : Blo 1044610 1571417 := bstep (se 2 (by rfl) ⟨589281, by rfl⟩ : syracuseStep 1571417 = 1178563) B1178563
theorem B1047147 : Blo 1044610 1047147 := bstep (se 1 (by rfl) ⟨785360, by rfl⟩ : syracuseStep 1047147 = 1570721) B1570721
theorem B1047159 : Blo 1044610 1047159 := bstep (se 1 (by rfl) ⟨785369, by rfl⟩ : syracuseStep 1047159 = 1570739) B1570739
theorem B1047179 : Blo 1044610 1047179 := bstep (se 1 (by rfl) ⟨785384, by rfl⟩ : syracuseStep 1047179 = 1570769) B1570769
theorem B1047191 : Blo 1044610 1047191 := bstep (se 1 (by rfl) ⟨785393, by rfl⟩ : syracuseStep 1047191 = 1570787) B1570787
theorem B1047211 : Blo 1044610 1047211 := bstep (se 1 (by rfl) ⟨785408, by rfl⟩ : syracuseStep 1047211 = 1570817) B1570817
theorem B1047223 : Blo 1044610 1047223 := bstep (se 1 (by rfl) ⟨785417, by rfl⟩ : syracuseStep 1047223 = 1570835) B1570835
theorem B2652851 : Blo 1044610 2652851 := bstep (se 1 (by rfl) ⟨1989638, by rfl⟩ : syracuseStep 2652851 = 3979277) B3979277
theorem B1047243 : Blo 1044610 1047243 := bstep (se 1 (by rfl) ⟨785432, by rfl⟩ : syracuseStep 1047243 = 1570865) B1570865
theorem B1571531 : Blo 1044610 1571531 := bstep (se 1 (by rfl) ⟨1178648, by rfl⟩ : syracuseStep 1571531 = 2357297) B2357297
theorem B2357963 : Blo 1044610 2357963 := bstep (se 1 (by rfl) ⟨1768472, by rfl⟩ : syracuseStep 2357963 = 3536945) B3536945
theorem B1047255 : Blo 1044610 1047255 := bstep (se 1 (by rfl) ⟨785441, by rfl⟩ : syracuseStep 1047255 = 1570883) B1570883
theorem B1571543 : Blo 1044610 1571543 := bstep (se 1 (by rfl) ⟨1178657, by rfl⟩ : syracuseStep 1571543 = 2357315) B2357315
theorem B1047275 : Blo 1044610 1047275 := bstep (se 1 (by rfl) ⟨785456, by rfl⟩ : syracuseStep 1047275 = 1570913) B1570913
theorem B1178347 : Blo 1044610 1178347 := bstep (se 1 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 1178347 = 1767521) B1767521
theorem B1047287 : Blo 1044610 1047287 := bstep (se 1 (by rfl) ⟨785465, by rfl⟩ : syracuseStep 1047287 = 1570931) B1570931
theorem B2358017 : Blo 1044610 2358017 := bstep (se 2 (by rfl) ⟨884256, by rfl⟩ : syracuseStep 2358017 = 1768513) B1768513
theorem B1047307 : Blo 1044610 1047307 := bstep (se 1 (by rfl) ⟨785480, by rfl⟩ : syracuseStep 1047307 = 1570961) B1570961
theorem B3767057 : Blo 1044610 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2980631 : Blo 1044610 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B1047319 : Blo 1044610 1047319 := bstep (se 1 (by rfl) ⟨785489, by rfl⟩ : syracuseStep 1047319 = 1570979) B1570979
theorem B1571609 : Blo 1044610 1571609 := bstep (se 2 (by rfl) ⟨589353, by rfl⟩ : syracuseStep 1571609 = 1178707) B1178707
theorem B1047339 : Blo 1044610 1047339 := bstep (se 1 (by rfl) ⟨785504, by rfl⟩ : syracuseStep 1047339 = 1571009) B1571009
theorem B1047351 : Blo 1044610 1047351 := bstep (se 1 (by rfl) ⟨785513, by rfl⟩ : syracuseStep 1047351 = 1571027) B1571027
theorem B1047371 : Blo 1044610 1047371 := bstep (se 1 (by rfl) ⟨785528, by rfl⟩ : syracuseStep 1047371 = 1571057) B1571057
theorem B1047383 : Blo 1044610 1047383 := bstep (se 1 (by rfl) ⟨785537, by rfl⟩ : syracuseStep 1047383 = 1571075) B1571075
theorem B1178455 : Blo 1044610 1178455 := bstep (se 1 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 1178455 = 1767683) B1767683
theorem B20380517 : Blo 1044610 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B1047403 : Blo 1044610 1047403 := bstep (se 1 (by rfl) ⟨785552, by rfl⟩ : syracuseStep 1047403 = 1571105) B1571105
theorem B1047415 : Blo 1044610 1047415 := bstep (se 1 (by rfl) ⟨785561, by rfl⟩ : syracuseStep 1047415 = 1571123) B1571123
theorem B1768331 : Blo 1044610 1768331 := bstep (se 1 (by rfl) ⟨1326248, by rfl⟩ : syracuseStep 1768331 = 2652497) B2652497
theorem B1047435 : Blo 1044610 1047435 := bstep (se 1 (by rfl) ⟨785576, by rfl⟩ : syracuseStep 1047435 = 1571153) B1571153
theorem B1571723 : Blo 1044610 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B1047447 : Blo 1044610 1047447 := bstep (se 1 (by rfl) ⟨785585, by rfl⟩ : syracuseStep 1047447 = 1571171) B1571171
theorem B1571735 : Blo 1044610 1571735 := bstep (se 1 (by rfl) ⟨1178801, by rfl⟩ : syracuseStep 1571735 = 2357603) B2357603
theorem B1047467 : Blo 1044610 1047467 := bstep (se 1 (by rfl) ⟨785600, by rfl⟩ : syracuseStep 1047467 = 1571201) B1571201
theorem B1047479 : Blo 1044610 1047479 := bstep (se 1 (by rfl) ⟨785609, by rfl⟩ : syracuseStep 1047479 = 1571219) B1571219
theorem B2685899 : Blo 1044610 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B1047499 : Blo 1044610 1047499 := bstep (se 1 (by rfl) ⟨785624, by rfl⟩ : syracuseStep 1047499 = 1571249) B1571249
theorem B1047511 : Blo 1044610 1047511 := bstep (se 1 (by rfl) ⟨785633, by rfl⟩ : syracuseStep 1047511 = 1571267) B1571267
theorem B1571801 : Blo 1044610 1571801 := bstep (se 2 (by rfl) ⟨589425, by rfl⟩ : syracuseStep 1571801 = 1178851) B1178851
theorem B2358233 : Blo 1044610 2358233 := bstep (se 2 (by rfl) ⟨884337, by rfl⟩ : syracuseStep 2358233 = 1768675) B1768675
theorem B2653145 : Blo 1044610 2653145 := bstep (se 2 (by rfl) ⟨994929, by rfl⟩ : syracuseStep 2653145 = 1989859) B1989859
theorem B1047531 : Blo 1044610 1047531 := bstep (se 1 (by rfl) ⟨785648, by rfl⟩ : syracuseStep 1047531 = 1571297) B1571297
theorem B1047543 : Blo 1044610 1047543 := bstep (se 1 (by rfl) ⟨785657, by rfl⟩ : syracuseStep 1047543 = 1571315) B1571315
theorem B1047563 : Blo 1044610 1047563 := bstep (se 1 (by rfl) ⟨785672, by rfl⟩ : syracuseStep 1047563 = 1571345) B1571345
theorem B1178635 : Blo 1044610 1178635 := bstep (se 1 (by rfl) ⟨883976, by rfl⟩ : syracuseStep 1178635 = 1767953) B1767953
theorem B1768459 : Blo 1044610 1768459 := bstep (se 1 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 1768459 = 2652689) B2652689
theorem B1047575 : Blo 1044610 1047575 := bstep (se 1 (by rfl) ⟨785681, by rfl⟩ : syracuseStep 1047575 = 1571363) B1571363
theorem B1047595 : Blo 1044610 1047595 := bstep (se 1 (by rfl) ⟨785696, by rfl⟩ : syracuseStep 1047595 = 1571393) B1571393
theorem B2358323 : Blo 1044610 2358323 := bstep (se 1 (by rfl) ⟨1768742, by rfl⟩ : syracuseStep 2358323 = 3537485) B3537485
theorem B3537971 : Blo 1044610 3537971 := bstep (se 1 (by rfl) ⟨2653478, by rfl⟩ : syracuseStep 3537971 = 5306957) B5306957
theorem B1047607 : Blo 1044610 1047607 := bstep (se 1 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 1047607 = 1571411) B1571411
theorem B1047627 : Blo 1044610 1047627 := bstep (se 1 (by rfl) ⟨785720, by rfl⟩ : syracuseStep 1047627 = 1571441) B1571441
theorem B1571915 : Blo 1044610 1571915 := bstep (se 1 (by rfl) ⟨1178936, by rfl⟩ : syracuseStep 1571915 = 2357873) B2357873
theorem B1047639 : Blo 1044610 1047639 := bstep (se 1 (by rfl) ⟨785729, by rfl⟩ : syracuseStep 1047639 = 1571459) B1571459
theorem B1571927 : Blo 1044610 1571927 := bstep (se 1 (by rfl) ⟨1178945, by rfl⟩ : syracuseStep 1571927 = 2357891) B2357891
theorem B2358359 : Blo 1044610 2358359 := bstep (se 1 (by rfl) ⟨1768769, by rfl⟩ : syracuseStep 2358359 = 3537539) B3537539
theorem B1047659 : Blo 1044610 1047659 := bstep (se 1 (by rfl) ⟨785744, by rfl⟩ : syracuseStep 1047659 = 1571489) B1571489
theorem B1047671 : Blo 1044610 1047671 := bstep (se 1 (by rfl) ⟨785753, by rfl⟩ : syracuseStep 1047671 = 1571507) B1571507
theorem B1178743 : Blo 1044610 1178743 := bstep (se 1 (by rfl) ⟨884057, by rfl⟩ : syracuseStep 1178743 = 1768115) B1768115
theorem B1047691 : Blo 1044610 1047691 := bstep (se 1 (by rfl) ⟨785768, by rfl⟩ : syracuseStep 1047691 = 1571537) B1571537
theorem B10058903 : Blo 1044610 10058903 := bstep (se 1 (by rfl) ⟨7544177, by rfl⟩ : syracuseStep 10058903 = 15088355) B15088355
theorem B1047703 : Blo 1044610 1047703 := bstep (se 1 (by rfl) ⟨785777, by rfl⟩ : syracuseStep 1047703 = 1571555) B1571555
theorem B1571993 : Blo 1044610 1571993 := bstep (se 2 (by rfl) ⟨589497, by rfl⟩ : syracuseStep 1571993 = 1178995) B1178995
theorem B1768601 : Blo 1044610 1768601 := bstep (se 2 (by rfl) ⟨663225, by rfl⟩ : syracuseStep 1768601 = 1326451) B1326451
theorem B1047723 : Blo 1044610 1047723 := bstep (se 1 (by rfl) ⟨785792, by rfl⟩ : syracuseStep 1047723 = 1571585) B1571585
theorem B1047735 : Blo 1044610 1047735 := bstep (se 1 (by rfl) ⟨785801, by rfl⟩ : syracuseStep 1047735 = 1571603) B1571603
theorem B1047755 : Blo 1044610 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B1047767 : Blo 1044610 1047767 := bstep (se 1 (by rfl) ⟨785825, by rfl⟩ : syracuseStep 1047767 = 1571651) B1571651
theorem B1047787 : Blo 1044610 1047787 := bstep (se 1 (by rfl) ⟨785840, by rfl⟩ : syracuseStep 1047787 = 1571681) B1571681
theorem B1047799 : Blo 1044610 1047799 := bstep (se 1 (by rfl) ⟨785849, by rfl⟩ : syracuseStep 1047799 = 1571699) B1571699
theorem B1047819 : Blo 1044610 1047819 := bstep (se 1 (by rfl) ⟨785864, by rfl⟩ : syracuseStep 1047819 = 1571729) B1571729
theorem B1572107 : Blo 1044610 1572107 := bstep (se 1 (by rfl) ⟨1179080, by rfl⟩ : syracuseStep 1572107 = 2358161) B2358161
theorem B2358539 : Blo 1044610 2358539 := bstep (se 1 (by rfl) ⟨1768904, by rfl⟩ : syracuseStep 2358539 = 3537809) B3537809
theorem B1047831 : Blo 1044610 1047831 := bstep (se 1 (by rfl) ⟨785873, by rfl⟩ : syracuseStep 1047831 = 1571747) B1571747
theorem B1572119 : Blo 1044610 1572119 := bstep (se 1 (by rfl) ⟨1179089, by rfl⟩ : syracuseStep 1572119 = 2358179) B2358179
theorem B1768729 : Blo 1044610 1768729 := bstep (se 2 (by rfl) ⟨663273, by rfl⟩ : syracuseStep 1768729 = 1326547) B1326547
theorem B1047851 : Blo 1044610 1047851 := bstep (se 1 (by rfl) ⟨785888, by rfl⟩ : syracuseStep 1047851 = 1571777) B1571777
theorem B1178923 : Blo 1044610 1178923 := bstep (se 1 (by rfl) ⟨884192, by rfl⟩ : syracuseStep 1178923 = 1768385) B1768385
theorem B1047863 : Blo 1044610 1047863 := bstep (se 1 (by rfl) ⟨785897, by rfl⟩ : syracuseStep 1047863 = 1571795) B1571795
theorem B2358593 : Blo 1044610 2358593 := bstep (se 2 (by rfl) ⟨884472, by rfl⟩ : syracuseStep 2358593 = 1768945) B1768945
theorem B3538241 : Blo 1044610 3538241 := bstep (se 2 (by rfl) ⟨1326840, by rfl⟩ : syracuseStep 3538241 = 2653681) B2653681
theorem B1047883 : Blo 1044610 1047883 := bstep (se 1 (by rfl) ⟨785912, by rfl⟩ : syracuseStep 1047883 = 1571825) B1571825
theorem B1047895 : Blo 1044610 1047895 := bstep (se 1 (by rfl) ⟨785921, by rfl⟩ : syracuseStep 1047895 = 1571843) B1571843
theorem B1572185 : Blo 1044610 1572185 := bstep (se 2 (by rfl) ⟨589569, by rfl⟩ : syracuseStep 1572185 = 1179139) B1179139
theorem B1047915 : Blo 1044610 1047915 := bstep (se 1 (by rfl) ⟨785936, by rfl⟩ : syracuseStep 1047915 = 1571873) B1571873
theorem B1047927 : Blo 1044610 1047927 := bstep (se 1 (by rfl) ⟨785945, by rfl⟩ : syracuseStep 1047927 = 1571891) B1571891
theorem B1047947 : Blo 1044610 1047947 := bstep (se 1 (by rfl) ⟨785960, by rfl⟩ : syracuseStep 1047947 = 1571921) B1571921
theorem B1047959 : Blo 1044610 1047959 := bstep (se 1 (by rfl) ⟨785969, by rfl⟩ : syracuseStep 1047959 = 1571939) B1571939
theorem B1179031 : Blo 1044610 1179031 := bstep (se 1 (by rfl) ⟨884273, by rfl⟩ : syracuseStep 1179031 = 1768547) B1768547
theorem B1047979 : Blo 1044610 1047979 := bstep (se 1 (by rfl) ⟨785984, by rfl⟩ : syracuseStep 1047979 = 1571969) B1571969
theorem B1047991 : Blo 1044610 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B1048011 : Blo 1044610 1048011 := bstep (se 1 (by rfl) ⟨786008, by rfl⟩ : syracuseStep 1048011 = 1572017) B1572017
theorem B1572299 : Blo 1044610 1572299 := bstep (se 1 (by rfl) ⟨1179224, by rfl⟩ : syracuseStep 1572299 = 2358449) B2358449
theorem B1048023 : Blo 1044610 1048023 := bstep (se 1 (by rfl) ⟨786017, by rfl⟩ : syracuseStep 1048023 = 1572035) B1572035
theorem B1572311 : Blo 1044610 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B1048043 : Blo 1044610 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B1048055 : Blo 1044610 1048055 := bstep (se 1 (by rfl) ⟨786041, by rfl⟩ : syracuseStep 1048055 = 1572083) B1572083
theorem B1048075 : Blo 1044610 1048075 := bstep (se 1 (by rfl) ⟨786056, by rfl⟩ : syracuseStep 1048075 = 1572113) B1572113
theorem B1048087 : Blo 1044610 1048087 := bstep (se 1 (by rfl) ⟨786065, by rfl⟩ : syracuseStep 1048087 = 1572131) B1572131
theorem B1572377 : Blo 1044610 1572377 := bstep (se 2 (by rfl) ⟨589641, by rfl⟩ : syracuseStep 1572377 = 1179283) B1179283
theorem B2358809 : Blo 1044610 2358809 := bstep (se 2 (by rfl) ⟨884553, by rfl⟩ : syracuseStep 2358809 = 1769107) B1769107
theorem B1048107 : Blo 1044610 1048107 := bstep (se 1 (by rfl) ⟨786080, by rfl⟩ : syracuseStep 1048107 = 1572161) B1572161
theorem B1048119 : Blo 1044610 1048119 := bstep (se 1 (by rfl) ⟨786089, by rfl⟩ : syracuseStep 1048119 = 1572179) B1572179
theorem B1048139 : Blo 1044610 1048139 := bstep (se 1 (by rfl) ⟨786104, by rfl⟩ : syracuseStep 1048139 = 1572209) B1572209
theorem B1179211 : Blo 1044610 1179211 := bstep (se 1 (by rfl) ⟨884408, by rfl⟩ : syracuseStep 1179211 = 1768817) B1768817
theorem B1048151 : Blo 1044610 1048151 := bstep (se 1 (by rfl) ⟨786113, by rfl⟩ : syracuseStep 1048151 = 1572227) B1572227
theorem B1048171 : Blo 1044610 1048171 := bstep (se 1 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 1048171 = 1572257) B1572257
theorem B2358899 : Blo 1044610 2358899 := bstep (se 1 (by rfl) ⟨1769174, by rfl⟩ : syracuseStep 2358899 = 3538349) B3538349
theorem B1048183 : Blo 1044610 1048183 := bstep (se 1 (by rfl) ⟨786137, by rfl⟩ : syracuseStep 1048183 = 1572275) B1572275
theorem B1048203 : Blo 1044610 1048203 := bstep (se 1 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 1048203 = 1572305) B1572305
theorem B1572491 : Blo 1044610 1572491 := bstep (se 1 (by rfl) ⟨1179368, by rfl⟩ : syracuseStep 1572491 = 2358737) B2358737
theorem B1048215 : Blo 1044610 1048215 := bstep (se 1 (by rfl) ⟨786161, by rfl⟩ : syracuseStep 1048215 = 1572323) B1572323
theorem B1572503 : Blo 1044610 1572503 := bstep (se 1 (by rfl) ⟨1179377, by rfl⟩ : syracuseStep 1572503 = 2358755) B2358755
theorem B2358935 : Blo 1044610 2358935 := bstep (se 1 (by rfl) ⟨1769201, by rfl⟩ : syracuseStep 2358935 = 3538403) B3538403
theorem B1048235 : Blo 1044610 1048235 := bstep (se 1 (by rfl) ⟨786176, by rfl⟩ : syracuseStep 1048235 = 1572353) B1572353
theorem B1048247 : Blo 1044610 1048247 := bstep (se 1 (by rfl) ⟨786185, by rfl⟩ : syracuseStep 1048247 = 1572371) B1572371
theorem B1179319 : Blo 1044610 1179319 := bstep (se 1 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 1179319 = 1768979) B1768979
theorem B1048267 : Blo 1044610 1048267 := bstep (se 1 (by rfl) ⟨786200, by rfl⟩ : syracuseStep 1048267 = 1572401) B1572401
theorem B1048279 : Blo 1044610 1048279 := bstep (se 1 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 1048279 = 1572419) B1572419
theorem B1572569 : Blo 1044610 1572569 := bstep (se 2 (by rfl) ⟨589713, by rfl⟩ : syracuseStep 1572569 = 1179427) B1179427
theorem B1048299 : Blo 1044610 1048299 := bstep (se 1 (by rfl) ⟨786224, by rfl⟩ : syracuseStep 1048299 = 1572449) B1572449
theorem B1048311 : Blo 1044610 1048311 := bstep (se 1 (by rfl) ⟨786233, by rfl⟩ : syracuseStep 1048311 = 1572467) B1572467
theorem B1048331 : Blo 1044610 1048331 := bstep (se 1 (by rfl) ⟨786248, by rfl⟩ : syracuseStep 1048331 = 1572497) B1572497
theorem B1048343 : Blo 1044610 1048343 := bstep (se 1 (by rfl) ⟨786257, by rfl⟩ : syracuseStep 1048343 = 1572515) B1572515
theorem B1048363 : Blo 1044610 1048363 := bstep (se 1 (by rfl) ⟨786272, by rfl⟩ : syracuseStep 1048363 = 1572545) B1572545
theorem B1048375 : Blo 1044610 1048375 := bstep (se 1 (by rfl) ⟨786281, by rfl⟩ : syracuseStep 1048375 = 1572563) B1572563
theorem B1048395 : Blo 1044610 1048395 := bstep (se 1 (by rfl) ⟨786296, by rfl⟩ : syracuseStep 1048395 = 1572593) B1572593
theorem B1572683 : Blo 1044610 1572683 := bstep (se 1 (by rfl) ⟨1179512, by rfl⟩ : syracuseStep 1572683 = 2359025) B2359025
theorem B2359115 : Blo 1044610 2359115 := bstep (se 1 (by rfl) ⟨1769336, by rfl⟩ : syracuseStep 2359115 = 3538673) B3538673
theorem B1048407 : Blo 1044610 1048407 := bstep (se 1 (by rfl) ⟨786305, by rfl⟩ : syracuseStep 1048407 = 1572611) B1572611
theorem B1572695 : Blo 1044610 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B1769303 : Blo 1044610 1769303 := bstep (se 1 (by rfl) ⟨1326977, by rfl⟩ : syracuseStep 1769303 = 2653955) B2653955
theorem B3538781 : Blo 1044610 3538781 := bstep (se 3 (by rfl) ⟨663521, by rfl⟩ : syracuseStep 3538781 = 1327043) B1327043
theorem B5308253 : Blo 1044610 5308253 := bstep (se 3 (by rfl) ⟨995297, by rfl⟩ : syracuseStep 5308253 = 1990595) B1990595
theorem B1048427 : Blo 1044610 1048427 := bstep (se 1 (by rfl) ⟨786320, by rfl⟩ : syracuseStep 1048427 = 1572641) B1572641
theorem B1179499 : Blo 1044610 1179499 := bstep (se 1 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 1179499 = 1769249) B1769249
theorem B1048439 : Blo 1044610 1048439 := bstep (se 1 (by rfl) ⟨786329, by rfl⟩ : syracuseStep 1048439 = 1572659) B1572659
theorem B2359169 : Blo 1044610 2359169 := bstep (se 2 (by rfl) ⟨884688, by rfl⟩ : syracuseStep 2359169 = 1769377) B1769377
theorem B1048459 : Blo 1044610 1048459 := bstep (se 1 (by rfl) ⟨786344, by rfl⟩ : syracuseStep 1048459 = 1572689) B1572689
theorem B1048471 : Blo 1044610 1048471 := bstep (se 1 (by rfl) ⟨786353, by rfl⟩ : syracuseStep 1048471 = 1572707) B1572707
theorem B1572761 : Blo 1044610 1572761 := bstep (se 2 (by rfl) ⟨589785, by rfl⟩ : syracuseStep 1572761 = 1179571) B1179571
theorem B1048491 : Blo 1044610 1048491 := bstep (se 1 (by rfl) ⟨786368, by rfl⟩ : syracuseStep 1048491 = 1572737) B1572737
theorem B1048503 : Blo 1044610 1048503 := bstep (se 1 (by rfl) ⟨786377, by rfl⟩ : syracuseStep 1048503 = 1572755) B1572755
theorem B1048523 : Blo 1044610 1048523 := bstep (se 1 (by rfl) ⟨786392, by rfl⟩ : syracuseStep 1048523 = 1572785) B1572785
theorem B1048535 : Blo 1044610 1048535 := bstep (se 1 (by rfl) ⟨786401, by rfl⟩ : syracuseStep 1048535 = 1572803) B1572803
theorem B1179607 : Blo 1044610 1179607 := bstep (se 1 (by rfl) ⟨884705, by rfl⟩ : syracuseStep 1179607 = 1769411) B1769411
theorem B1769431 : Blo 1044610 1769431 := bstep (se 1 (by rfl) ⟨1327073, by rfl⟩ : syracuseStep 1769431 = 2654147) B2654147
theorem B1048555 : Blo 1044610 1048555 := bstep (se 1 (by rfl) ⟨786416, by rfl⟩ : syracuseStep 1048555 = 1572833) B1572833
theorem B1048567 : Blo 1044610 1048567 := bstep (se 1 (by rfl) ⟨786425, by rfl⟩ : syracuseStep 1048567 = 1572851) B1572851
theorem B1048583 : Blo 1044610 1048583 := bstep (se 1 (by rfl) ⟨786437, by rfl⟩ : syracuseStep 1048583 = 1572875) B1572875
theorem B1048591 : Blo 1044610 1048591 := bstep (se 1 (by rfl) ⟨786443, by rfl⟩ : syracuseStep 1048591 = 1572887) B1572887
theorem B2982089 : Blo 1044610 2982089 := bstep (se 2 (by rfl) ⟨1118283, by rfl⟩ : syracuseStep 2982089 = 2236567) B2236567
theorem B2982203 : Blo 1044610 2982203 := bstep (se 1 (by rfl) ⟨2236652, by rfl⟩ : syracuseStep 2982203 = 4473305) B4473305
theorem B2982329 : Blo 1044610 2982329 := bstep (se 2 (by rfl) ⟨1118373, by rfl⟩ : syracuseStep 2982329 = 2236747) B2236747
theorem B3768875 : Blo 1044610 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B2687755 : Blo 1044610 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B76251941 : Blo 1044610 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B3179891 : Blo 1044610 3179891 := bstep (se 1 (by rfl) ⟨2384918, by rfl⟩ : syracuseStep 3179891 = 4769837) B4769837
theorem B7538179 : Blo 1044610 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B5965771 : Blo 1044610 5965771 := bstep (se 1 (by rfl) ⟨4474328, by rfl⟩ : syracuseStep 5965771 = 8948657) B8948657
theorem B3016705 : Blo 1044610 3016705 := bstep (se 2 (by rfl) ⟨1131264, by rfl⟩ : syracuseStep 3016705 = 2262529) B2262529
theorem B2983979 : Blo 1044610 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B12716837 : Blo 1044610 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B10062629 : Blo 1044610 10062629 := bstep (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) B1886743
theorem B3181447 : Blo 1044610 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B4033415 : Blo 1044610 4033415 := bstep (se 1 (by rfl) ⟨3025061, by rfl⟩ : syracuseStep 4033415 = 6050123) B6050123
theorem B2984971 : Blo 1044610 2984971 := bstep (se 1 (by rfl) ⟨2238728, by rfl⟩ : syracuseStep 2984971 = 4477457) B4477457
theorem B2985245 : Blo 1044610 2985245 := bstep (se 3 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 2985245 = 1119467) B1119467
theorem B20417923 : Blo 1044610 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B12717611 : Blo 1044610 12717611 := bstep (se 1 (by rfl) ⟨9538208, by rfl⟩ : syracuseStep 12717611 = 19076417) B19076417
theorem B3968783 : Blo 1044610 3968783 := bstep (se 1 (by rfl) ⟨2976587, by rfl⟩ : syracuseStep 3968783 = 5953175) B5953175
theorem B1117967 : Blo 1044610 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B32280371 : Blo 1044610 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B223350707 : Blo 1044610 223350707 := bstep (se 1 (by rfl) ⟨167513030, by rfl⟩ : syracuseStep 223350707 = 335026061) B335026061
theorem B1118215 : Blo 1044610 1118215 := bstep (se 1 (by rfl) ⟨838661, by rfl⟩ : syracuseStep 1118215 = 1677323) B1677323
theorem B7737367 : Blo 1044610 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B5968187 : Blo 1044610 5968187 := bstep (se 1 (by rfl) ⟨4476140, by rfl⟩ : syracuseStep 5968187 = 8952281) B8952281
theorem B3576199 : Blo 1044610 3576199 := bstep (se 1 (by rfl) ⟨2682149, by rfl⟩ : syracuseStep 3576199 = 5364299) B5364299
theorem B3773243 : Blo 1044610 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B1676233 : Blo 1044610 1676233 := bstep (se 2 (by rfl) ⟨628587, by rfl⟩ : syracuseStep 1676233 = 1257175) B1257175
theorem B4527341 : Blo 1044610 4527341 := bstep (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) B1697753
theorem B2725207 : Blo 1044610 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B2233747 : Blo 1044610 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B2299435 : Blo 1044610 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B1513033 : Blo 1044610 1513033 := bstep (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) B1134775
theorem B4462199 : Blo 1044610 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B1414841 : Blo 1044610 1414841 := bstep (se 2 (by rfl) ⟨530565, by rfl⟩ : syracuseStep 1414841 = 1061131) B1061131
theorem B5969645 : Blo 1044610 5969645 := bstep (se 3 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 5969645 = 2238617) B2238617
theorem B15341363 : Blo 1044610 15341363 := bstep (se 1 (by rfl) ⟨11506022, by rfl⟩ : syracuseStep 15341363 = 23012045) B23012045
theorem B5969963 : Blo 1044610 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B3184841 : Blo 1044610 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B10066625 : Blo 1044610 10066625 := bstep (se 2 (by rfl) ⟨3774984, by rfl⟩ : syracuseStep 10066625 = 7549969) B7549969
theorem B3971987 : Blo 1044610 3971987 := bstep (se 1 (by rfl) ⟨2978990, by rfl⟩ : syracuseStep 3971987 = 5957981) B5957981
theorem B45227159 : Blo 1044610 45227159 := bstep (se 1 (by rfl) ⟨33920369, by rfl⟩ : syracuseStep 45227159 = 67840739) B67840739
theorem B2235593 : Blo 1044610 2235593 := bstep (se 2 (by rfl) ⟨838347, by rfl⟩ : syracuseStep 2235593 = 1676695) B1676695
theorem B4463873 : Blo 1044610 4463873 := bstep (se 2 (by rfl) ⟨1673952, by rfl⟩ : syracuseStep 4463873 = 3347905) B3347905
theorem B5971421 : Blo 1044610 5971421 := bstep (se 3 (by rfl) ⟨1119641, by rfl⟩ : syracuseStep 5971421 = 2239283) B2239283
theorem B4595287 : Blo 1044610 4595287 := bstep (se 1 (by rfl) ⟨3446465, by rfl⟩ : syracuseStep 4595287 = 6892931) B6892931
theorem B3186263 : Blo 1044610 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B3350135 : Blo 1044610 3350135 := bstep (se 1 (by rfl) ⟨2512601, by rfl⟩ : syracuseStep 3350135 = 5025203) B5025203
theorem B3186311 : Blo 1044610 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B1908425 : Blo 1044610 1908425 := bstep (se 2 (by rfl) ⟨715659, by rfl⟩ : syracuseStep 1908425 = 1431319) B1431319
theorem B5021473 : Blo 1044610 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B98148145 : Blo 1044610 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B2826299 : Blo 1044610 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B3973643 : Blo 1044610 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B2826937 : Blo 1044610 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B21767093 : Blo 1044610 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B2237711 : Blo 1044610 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B10069393 : Blo 1044610 10069393 := bstep (se 2 (by rfl) ⟨3776022, by rfl⟩ : syracuseStep 10069393 = 7552045) B7552045
theorem B32253515 : Blo 1044610 32253515 := bstep (se 1 (by rfl) ⟨24190136, by rfl⟩ : syracuseStep 32253515 = 48380273) B48380273
theorem B1255099 : Blo 1044610 1255099 := bstep (se 1 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 1255099 = 1882649) B1882649
theorem B4237373 : Blo 1044610 4237373 := bstep (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) B1589015
theorem B8071483 : Blo 1044610 8071483 := bstep (se 1 (by rfl) ⟨6053612, by rfl⟩ : syracuseStep 8071483 = 12107225) B12107225
theorem B23538437 : Blo 1044610 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B3353491 : Blo 1044610 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B5024855 : Blo 1044610 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B8957405 : Blo 1044610 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B1322887 : Blo 1044610 1322887 := bstep (se 1 (by rfl) ⟨992165, by rfl⟩ : syracuseStep 1322887 = 1984331) B1984331
theorem B21442573 : Blo 1044610 21442573 := bstep (se 3 (by rfl) ⟨4020482, by rfl⟩ : syracuseStep 21442573 = 8040965) B8040965
theorem B6041623 : Blo 1044610 6041623 := bstep (se 1 (by rfl) ⟨4531217, by rfl⟩ : syracuseStep 6041623 = 9062435) B9062435
theorem B6369509 : Blo 1044610 6369509 := bstep (se 4 (by rfl) ⟨597141, by rfl⟩ : syracuseStep 6369509 = 1194283) B1194283
theorem B1323307 : Blo 1044610 1323307 := bstep (se 1 (by rfl) ⟨992480, by rfl⟩ : syracuseStep 1323307 = 1984961) B1984961
theorem B3977531 : Blo 1044610 3977531 := bstep (se 1 (by rfl) ⟨2983148, by rfl⟩ : syracuseStep 3977531 = 5966297) B5966297
theorem B1323535 : Blo 1044610 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B1487479 : Blo 1044610 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B3355337 : Blo 1044610 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B3978017 : Blo 1044610 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B5649203 : Blo 1044610 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B1324279 : Blo 1044610 1324279 := bstep (se 1 (by rfl) ⟨993209, by rfl⟩ : syracuseStep 1324279 = 1986419) B1986419
theorem B1488299 : Blo 1044610 1488299 := bstep (se 1 (by rfl) ⟨1116224, by rfl⟩ : syracuseStep 1488299 = 2232449) B2232449
theorem B1324603 : Blo 1044610 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B8926787 : Blo 1044610 8926787 := bstep (se 1 (by rfl) ⟨6695090, by rfl⟩ : syracuseStep 8926787 = 13390181) B13390181
theorem B3978989 : Blo 1044610 3978989 := bstep (se 3 (by rfl) ⟨746060, by rfl⟩ : syracuseStep 3978989 = 1492121) B1492121
theorem B39302981 : Blo 1044610 39302981 := bstep (se 4 (by rfl) ⟨3684654, by rfl⟩ : syracuseStep 39302981 = 7369309) B7369309
theorem B4241267 : Blo 1044610 4241267 := bstep (se 1 (by rfl) ⟨3180950, by rfl⟩ : syracuseStep 4241267 = 6361901) B6361901
theorem B1325099 : Blo 1044610 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B3979307 : Blo 1044610 3979307 := bstep (se 1 (by rfl) ⟨2984480, by rfl⟩ : syracuseStep 3979307 = 5968961) B5968961
theorem B6699449 : Blo 1044610 6699449 := bstep (se 2 (by rfl) ⟨2512293, by rfl⟩ : syracuseStep 6699449 = 5024587) B5024587
theorem B5028317 : Blo 1044610 5028317 := bstep (se 3 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 5028317 = 1885619) B1885619
theorem B1325575 : Blo 1044610 1325575 := bstep (se 1 (by rfl) ⟨994181, by rfl⟩ : syracuseStep 1325575 = 1988363) B1988363
theorem B4471307 : Blo 1044610 4471307 := bstep (se 1 (by rfl) ⟨3353480, by rfl⟩ : syracuseStep 4471307 = 6706961) B6706961
theorem B11942477 : Blo 1044610 11942477 := bstep (se 3 (by rfl) ⟨2239214, by rfl⟩ : syracuseStep 11942477 = 4478429) B4478429
theorem B1326071 : Blo 1044610 1326071 := bstep (se 1 (by rfl) ⟨994553, by rfl⟩ : syracuseStep 1326071 = 1989107) B1989107
theorem B1326223 : Blo 1044610 1326223 := bstep (se 1 (by rfl) ⟨994667, by rfl⟩ : syracuseStep 1326223 = 1989335) B1989335
theorem B1490167 : Blo 1044610 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B1326395 : Blo 1044610 1326395 := bstep (se 1 (by rfl) ⟨994796, by rfl⟩ : syracuseStep 1326395 = 1989593) B1989593
theorem B4898333 : Blo 1044610 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B5291891 : Blo 1044610 5291891 := bstep (se 1 (by rfl) ⟨3968918, by rfl⟩ : syracuseStep 5291891 = 7937837) B7937837
theorem B7946099 : Blo 1044610 7946099 := bstep (se 1 (by rfl) ⟨5959574, by rfl⟩ : syracuseStep 7946099 = 11919149) B11919149
theorem B2834311 : Blo 1044610 2834311 := bstep (se 1 (by rfl) ⟨2125733, by rfl⟩ : syracuseStep 2834311 = 4251467) B4251467
theorem B2015161 : Blo 1044610 2015161 := bstep (se 2 (by rfl) ⟨755685, by rfl⟩ : syracuseStep 2015161 = 1511371) B1511371
theorem B1589239 : Blo 1044610 1589239 := bstep (se 1 (by rfl) ⟨1191929, by rfl⟩ : syracuseStep 1589239 = 2383859) B2383859
theorem B1589263 : Blo 1044610 1589263 := bstep (se 1 (by rfl) ⟨1191947, by rfl⟩ : syracuseStep 1589263 = 2383895) B2383895
theorem B8503319 : Blo 1044610 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B1491215 : Blo 1044610 1491215 := bstep (se 1 (by rfl) ⟨1118411, by rfl⟩ : syracuseStep 1491215 = 2236823) B2236823
theorem B4243745 : Blo 1044610 4243745 := bstep (se 2 (by rfl) ⟨1591404, by rfl⟩ : syracuseStep 4243745 = 3182809) B3182809
theorem B5292377 : Blo 1044610 5292377 := bstep (se 2 (by rfl) ⟨1984641, by rfl⟩ : syracuseStep 5292377 = 3969283) B3969283
theorem B6701447 : Blo 1044610 6701447 := bstep (se 1 (by rfl) ⟨5026085, by rfl⟩ : syracuseStep 6701447 = 10052171) B10052171
theorem B4473235 : Blo 1044610 4473235 := bstep (se 1 (by rfl) ⟨3354926, by rfl⟩ : syracuseStep 4473235 = 6709853) B6709853
theorem B1491529 : Blo 1044610 1491529 := bstep (se 2 (by rfl) ⟨559323, by rfl⟩ : syracuseStep 1491529 = 1118647) B1118647
theorem B11911859 : Blo 1044610 11911859 := bstep (se 1 (by rfl) ⟨8933894, by rfl⟩ : syracuseStep 11911859 = 17867789) B17867789
theorem B1983275 : Blo 1044610 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B1983503 : Blo 1044610 1983503 := bstep (se 1 (by rfl) ⟨1487627, by rfl⟩ : syracuseStep 1983503 = 2975255) B2975255
theorem B1885331 : Blo 1044610 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1787321 : Blo 1044610 1787321 := bstep (se 2 (by rfl) ⟨670245, by rfl⟩ : syracuseStep 1787321 = 1340491) B1340491
theorem B5654045 : Blo 1044610 5654045 := bstep (se 3 (by rfl) ⟨1060133, by rfl⟩ : syracuseStep 5654045 = 2120267) B2120267
theorem B2901547 : Blo 1044610 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B8931161 : Blo 1044610 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B4474739 : Blo 1044610 4474739 := bstep (se 1 (by rfl) ⟨3356054, by rfl⟩ : syracuseStep 4474739 = 6712109) B6712109
theorem B2017295 : Blo 1044610 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B15091757 : Blo 1044610 15091757 := bstep (se 3 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 15091757 = 5659409) B5659409
theorem B4475081 : Blo 1044610 4475081 := bstep (se 2 (by rfl) ⟨1678155, by rfl⟩ : syracuseStep 4475081 = 3356311) B3356311
theorem B5949733 : Blo 1044610 5949733 := bstep (se 4 (by rfl) ⟨557787, by rfl⟩ : syracuseStep 5949733 = 1115575) B1115575
theorem B1984915 : Blo 1044610 1984915 := bstep (se 1 (by rfl) ⟨1488686, by rfl⟩ : syracuseStep 1984915 = 2977373) B2977373
theorem B5294483 : Blo 1044610 5294483 := bstep (se 1 (by rfl) ⟨3970862, by rfl⟩ : syracuseStep 5294483 = 7941725) B7941725
theorem B4475321 : Blo 1044610 4475321 := bstep (se 2 (by rfl) ⟨1678245, by rfl⟩ : syracuseStep 4475321 = 3356491) B3356491
theorem B1985143 : Blo 1044610 1985143 := bstep (se 1 (by rfl) ⟨1488857, by rfl⟩ : syracuseStep 1985143 = 2977715) B2977715
theorem B5032621 : Blo 1044610 5032621 := bstep (se 3 (by rfl) ⟨943616, by rfl⟩ : syracuseStep 5032621 = 1887233) B1887233
theorem B4475681 : Blo 1044610 4475681 := bstep (se 2 (by rfl) ⟨1678380, by rfl⟩ : syracuseStep 4475681 = 3356761) B3356761
theorem B5950259 : Blo 1044610 5950259 := bstep (se 1 (by rfl) ⟨4462694, by rfl⟩ : syracuseStep 5950259 = 8925389) B8925389
theorem B1592183 : Blo 1044610 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B4476653 : Blo 1044610 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B3526415 : Blo 1044610 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B3526685 : Blo 1044610 3526685 := bstep (se 3 (by rfl) ⟨661253, by rfl⟩ : syracuseStep 3526685 = 1322507) B1322507
theorem B2510891 : Blo 1044610 2510891 := bstep (se 1 (by rfl) ⟨1883168, by rfl⟩ : syracuseStep 2510891 = 3766337) B3766337
theorem B4476995 : Blo 1044610 4476995 := bstep (se 1 (by rfl) ⟨3357746, by rfl⟩ : syracuseStep 4476995 = 6715493) B6715493
theorem B1986707 : Blo 1044610 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B1986761 : Blo 1044610 1986761 := bstep (se 2 (by rfl) ⟨745035, by rfl⟩ : syracuseStep 1986761 = 1490071) B1490071
theorem B5951717 : Blo 1044610 5951717 := bstep (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) B1115947
theorem B1986859 : Blo 1044610 1986859 := bstep (se 1 (by rfl) ⟨1490144, by rfl⟩ : syracuseStep 1986859 = 2980289) B2980289
theorem B1888697 : Blo 1044610 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B2511371 : Blo 1044610 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1987087 : Blo 1044610 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B22663745 : Blo 1044610 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B13587011 : Blo 1044610 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B17945155 : Blo 1044610 17945155 := bstep (se 1 (by rfl) ⟨13458866, by rfl⟩ : syracuseStep 17945155 = 26917733) B26917733
theorem B1790599 : Blo 1044610 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B6705935 : Blo 1044610 6705935 := bstep (se 1 (by rfl) ⟨5029451, by rfl⟩ : syracuseStep 6705935 = 10058903) B10058903
theorem B20108645 : Blo 1044610 20108645 := bstep (se 4 (by rfl) ⟨1885185, by rfl⟩ : syracuseStep 20108645 = 3770371) B3770371
theorem B2545031 : Blo 1044610 2545031 := bstep (se 1 (by rfl) ⟨1908773, by rfl⟩ : syracuseStep 2545031 = 3817547) B3817547
theorem B3528089 : Blo 1044610 3528089 := bstep (se 2 (by rfl) ⟨1323033, by rfl⟩ : syracuseStep 3528089 = 2646067) B2646067
theorem B5297561 : Blo 1044610 5297561 := bstep (se 2 (by rfl) ⟨1986585, by rfl⟩ : syracuseStep 5297561 = 3973171) B3973171
theorem B2512313 : Blo 1044610 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B42981043 : Blo 1044610 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B2873017 : Blo 1044610 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B2512775 : Blo 1044610 2512775 := bstep (se 1 (by rfl) ⟨1884581, by rfl⟩ : syracuseStep 2512775 = 3769163) B3769163
theorem B1988651 : Blo 1044610 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B3528791 : Blo 1044610 3528791 := bstep (se 1 (by rfl) ⟨2646593, by rfl⟩ : syracuseStep 3528791 = 5293187) B5293187
theorem B16963829 : Blo 1044610 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B2644235 : Blo 1044610 2644235 := bstep (se 1 (by rfl) ⟨1983176, by rfl⟩ : syracuseStep 2644235 = 3966353) B3966353
theorem B5658931 : Blo 1044610 5658931 := bstep (se 1 (by rfl) ⟨4244198, by rfl⟩ : syracuseStep 5658931 = 8488397) B8488397
theorem B1431865 : Blo 1044610 1431865 := bstep (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) B1073899
theorem B18143729 : Blo 1044610 18143729 := bstep (se 2 (by rfl) ⟨6803898, by rfl⟩ : syracuseStep 18143729 = 13607797) B13607797
theorem B3529277 : Blo 1044610 3529277 := bstep (se 3 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 3529277 = 1323479) B1323479
theorem B2644751 : Blo 1044610 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B2644883 : Blo 1044610 2644883 := bstep (se 1 (by rfl) ⟨1983662, by rfl⟩ : syracuseStep 2644883 = 3967325) B3967325
theorem B2350727 : Blo 1044610 2350727 := bstep (se 1 (by rfl) ⟨1763045, by rfl⟩ : syracuseStep 2350727 = 3526091) B3526091
theorem B1990345 : Blo 1044610 1990345 := bstep (se 2 (by rfl) ⟨746379, by rfl⟩ : syracuseStep 1990345 = 1492759) B1492759
theorem B20111105 : Blo 1044610 20111105 := bstep (se 2 (by rfl) ⟨7541664, by rfl⟩ : syracuseStep 20111105 = 15083329) B15083329
theorem B2350907 : Blo 1044610 2350907 := bstep (se 1 (by rfl) ⟨1763180, by rfl⟩ : syracuseStep 2350907 = 3526361) B3526361
theorem B15097751 : Blo 1044610 15097751 := bstep (se 1 (by rfl) ⟨11323313, by rfl⟩ : syracuseStep 15097751 = 22646627) B22646627
theorem B2351033 : Blo 1044610 2351033 := bstep (se 2 (by rfl) ⟨881637, by rfl⟩ : syracuseStep 2351033 = 1763275) B1763275
theorem B3530681 : Blo 1044610 3530681 := bstep (se 2 (by rfl) ⟨1324005, by rfl⟩ : syracuseStep 3530681 = 2648011) B2648011
theorem B5300153 : Blo 1044610 5300153 := bstep (se 2 (by rfl) ⟨1987557, by rfl⟩ : syracuseStep 5300153 = 3975115) B3975115
theorem B2646017 : Blo 1044610 2646017 := bstep (se 2 (by rfl) ⟨992256, by rfl⟩ : syracuseStep 2646017 = 1984513) B1984513
theorem B2351375 : Blo 1044610 2351375 := bstep (se 1 (by rfl) ⟨1763531, by rfl⟩ : syracuseStep 2351375 = 3527063) B3527063
theorem B2351393 : Blo 1044610 2351393 := bstep (se 2 (by rfl) ⟨881772, by rfl⟩ : syracuseStep 2351393 = 1763545) B1763545
theorem B2646391 : Blo 1044610 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B2417015 : Blo 1044610 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B3531275 : Blo 1044610 3531275 := bstep (se 1 (by rfl) ⟨2648456, by rfl⟩ : syracuseStep 3531275 = 5296913) B5296913
theorem B2351735 : Blo 1044610 2351735 := bstep (se 1 (by rfl) ⟨1763801, by rfl⟩ : syracuseStep 2351735 = 3527603) B3527603
theorem B3531383 : Blo 1044610 3531383 := bstep (se 1 (by rfl) ⟨2648537, by rfl⟩ : syracuseStep 3531383 = 5297075) B5297075
theorem B2581127 : Blo 1044610 2581127 := bstep (se 1 (by rfl) ⟨1935845, by rfl⟩ : syracuseStep 2581127 = 3871691) B3871691
theorem B2351915 : Blo 1044610 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B2646827 : Blo 1044610 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B2352275 : Blo 1044610 2352275 := bstep (se 1 (by rfl) ⟨1764206, by rfl⟩ : syracuseStep 2352275 = 3528413) B3528413
theorem B2352329 : Blo 1044610 2352329 := bstep (se 2 (by rfl) ⟨882123, by rfl⟩ : syracuseStep 2352329 = 1764247) B1764247
theorem B3531977 : Blo 1044610 3531977 := bstep (se 2 (by rfl) ⟨1324491, by rfl⟩ : syracuseStep 3531977 = 2648983) B2648983
theorem B5301449 : Blo 1044610 5301449 := bstep (se 2 (by rfl) ⟨1988043, by rfl⟩ : syracuseStep 5301449 = 3976087) B3976087
theorem B16999885 : Blo 1044610 16999885 := bstep (se 3 (by rfl) ⟨3187478, by rfl⟩ : syracuseStep 16999885 = 6374957) B6374957
theorem B45868619 : Blo 1044610 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B2647667 : Blo 1044610 2647667 := bstep (se 1 (by rfl) ⟨1985750, by rfl⟩ : syracuseStep 2647667 = 3971501) B3971501
theorem B2516599 : Blo 1044610 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B1762951 : Blo 1044610 1762951 := bstep (se 1 (by rfl) ⟨1322213, by rfl⟩ : syracuseStep 1762951 = 2644427) B2644427
theorem B2647687 : Blo 1044610 2647687 := bstep (se 1 (by rfl) ⟨1985765, by rfl⟩ : syracuseStep 2647687 = 3971531) B3971531
theorem B2353031 : Blo 1044610 2353031 := bstep (se 1 (by rfl) ⟨1764773, by rfl⟩ : syracuseStep 2353031 = 3529547) B3529547
theorem B3532679 : Blo 1044610 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B2647961 : Blo 1044610 2647961 := bstep (se 2 (by rfl) ⟨992985, by rfl⟩ : syracuseStep 2647961 = 1985971) B1985971
theorem B1534009 : Blo 1044610 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B2353211 : Blo 1044610 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B2648123 : Blo 1044610 2648123 := bstep (se 1 (by rfl) ⟨1986092, by rfl⟩ : syracuseStep 2648123 = 3972185) B3972185
theorem B2353337 : Blo 1044610 2353337 := bstep (se 2 (by rfl) ⟨882501, by rfl⟩ : syracuseStep 2353337 = 1765003) B1765003
theorem B3533057 : Blo 1044610 3533057 := bstep (se 2 (by rfl) ⟨1324896, by rfl⟩ : syracuseStep 3533057 = 2649793) B2649793
theorem B1566983 : Blo 1044610 1566983 := bstep (se 1 (by rfl) ⟨1175237, by rfl⟩ : syracuseStep 1566983 = 2350475) B2350475
theorem B1763599 : Blo 1044610 1763599 := bstep (se 1 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 1763599 = 2645399) B2645399
theorem B2648335 : Blo 1044610 2648335 := bstep (se 1 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 2648335 = 3972503) B3972503
theorem B1567019 : Blo 1044610 1567019 := bstep (se 1 (by rfl) ⟨1175264, by rfl⟩ : syracuseStep 1567019 = 2350529) B2350529
theorem B1567049 : Blo 1044610 1567049 := bstep (se 2 (by rfl) ⟨587643, by rfl⟩ : syracuseStep 1567049 = 1175287) B1175287
theorem B1567163 : Blo 1044610 1567163 := bstep (se 1 (by rfl) ⟨1175372, by rfl⟩ : syracuseStep 1567163 = 2350745) B2350745
theorem B1567223 : Blo 1044610 1567223 := bstep (se 1 (by rfl) ⟨1175417, by rfl⟩ : syracuseStep 1567223 = 2350835) B2350835
theorem B2976257 : Blo 1044610 2976257 := bstep (se 2 (by rfl) ⟨1116096, by rfl⟩ : syracuseStep 2976257 = 2232193) B2232193
theorem B1567247 : Blo 1044610 1567247 := bstep (se 1 (by rfl) ⟨1175435, by rfl⟩ : syracuseStep 1567247 = 2350871) B2350871
theorem B2353679 : Blo 1044610 2353679 := bstep (se 1 (by rfl) ⟨1765259, by rfl⟩ : syracuseStep 2353679 = 3530519) B3530519
theorem B2353697 : Blo 1044610 2353697 := bstep (se 2 (by rfl) ⟨882636, by rfl⟩ : syracuseStep 2353697 = 1765273) B1765273
theorem B2648609 : Blo 1044610 2648609 := bstep (se 2 (by rfl) ⟨993228, by rfl⟩ : syracuseStep 2648609 = 1986457) B1986457
theorem B1567289 : Blo 1044610 1567289 := bstep (se 2 (by rfl) ⟨587733, by rfl⟩ : syracuseStep 1567289 = 1175467) B1175467
theorem B2976371 : Blo 1044610 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1567367 : Blo 1044610 1567367 := bstep (se 1 (by rfl) ⟨1175525, by rfl⟩ : syracuseStep 1567367 = 2351051) B2351051
theorem B1567403 : Blo 1044610 1567403 := bstep (se 1 (by rfl) ⟨1175552, by rfl⟩ : syracuseStep 1567403 = 2351105) B2351105
theorem B5106349 : Blo 1044610 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B1567433 : Blo 1044610 1567433 := bstep (se 2 (by rfl) ⟨587787, by rfl⟩ : syracuseStep 1567433 = 1175575) B1175575
theorem B1764139 : Blo 1044610 1764139 := bstep (se 1 (by rfl) ⟨1323104, by rfl⟩ : syracuseStep 1764139 = 2646209) B2646209
theorem B1567547 : Blo 1044610 1567547 := bstep (se 1 (by rfl) ⟨1175660, by rfl⟩ : syracuseStep 1567547 = 2351321) B2351321
theorem B1567607 : Blo 1044610 1567607 := bstep (se 1 (by rfl) ⟨1175705, by rfl⟩ : syracuseStep 1567607 = 2351411) B2351411
theorem B2354039 : Blo 1044610 2354039 := bstep (se 1 (by rfl) ⟨1765529, by rfl⟩ : syracuseStep 2354039 = 3531059) B3531059
theorem B1567631 : Blo 1044610 1567631 := bstep (se 1 (by rfl) ⟨1175723, by rfl⟩ : syracuseStep 1567631 = 2351447) B2351447
theorem B1567673 : Blo 1044610 1567673 := bstep (se 2 (by rfl) ⟨587877, by rfl⟩ : syracuseStep 1567673 = 1175755) B1175755
theorem B1764281 : Blo 1044610 1764281 := bstep (se 2 (by rfl) ⟨661605, by rfl⟩ : syracuseStep 1764281 = 1323211) B1323211
theorem B2976713 : Blo 1044610 2976713 := bstep (se 2 (by rfl) ⟨1116267, by rfl⟩ : syracuseStep 2976713 = 2232535) B2232535
theorem B1567751 : Blo 1044610 1567751 := bstep (se 1 (by rfl) ⟨1175813, by rfl⟩ : syracuseStep 1567751 = 2351627) B2351627
theorem B10742807 : Blo 1044610 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B1567787 : Blo 1044610 1567787 := bstep (se 1 (by rfl) ⟨1175840, by rfl⟩ : syracuseStep 1567787 = 2351681) B2351681
theorem B2354219 : Blo 1044610 2354219 := bstep (se 1 (by rfl) ⟨1765664, by rfl⟩ : syracuseStep 2354219 = 3531329) B3531329
theorem B3533867 : Blo 1044610 3533867 := bstep (se 1 (by rfl) ⟨2650400, by rfl⟩ : syracuseStep 3533867 = 5300801) B5300801
theorem B1567817 : Blo 1044610 1567817 := bstep (se 2 (by rfl) ⟨587931, by rfl⟩ : syracuseStep 1567817 = 1175863) B1175863
theorem B1567931 : Blo 1044610 1567931 := bstep (se 1 (by rfl) ⟨1175948, by rfl⟩ : syracuseStep 1567931 = 2351897) B2351897
theorem B1567991 : Blo 1044610 1567991 := bstep (se 1 (by rfl) ⟨1175993, by rfl⟩ : syracuseStep 1567991 = 2351987) B2351987
theorem B1568015 : Blo 1044610 1568015 := bstep (se 1 (by rfl) ⟨1176011, by rfl⟩ : syracuseStep 1568015 = 2352023) B2352023
theorem B24177953 : Blo 1044610 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B1568057 : Blo 1044610 1568057 := bstep (se 2 (by rfl) ⟨588021, by rfl⟩ : syracuseStep 1568057 = 1176043) B1176043
theorem B1568135 : Blo 1044610 1568135 := bstep (se 1 (by rfl) ⟨1176101, by rfl⟩ : syracuseStep 1568135 = 2352203) B2352203
theorem B2354579 : Blo 1044610 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B6712723 : Blo 1044610 6712723 := bstep (se 1 (by rfl) ⟨5034542, by rfl⟩ : syracuseStep 6712723 = 10069085) B10069085
theorem B1568171 : Blo 1044610 1568171 := bstep (se 1 (by rfl) ⟨1176128, by rfl⟩ : syracuseStep 1568171 = 2352257) B2352257
theorem B1568201 : Blo 1044610 1568201 := bstep (se 2 (by rfl) ⟨588075, by rfl⟩ : syracuseStep 1568201 = 1176151) B1176151
theorem B2354633 : Blo 1044610 2354633 := bstep (se 2 (by rfl) ⟨882987, by rfl⟩ : syracuseStep 2354633 = 1765975) B1765975
theorem B2649611 : Blo 1044610 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B1568315 : Blo 1044610 1568315 := bstep (se 1 (by rfl) ⟨1176236, by rfl⟩ : syracuseStep 1568315 = 2352473) B2352473
theorem B1568375 : Blo 1044610 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B1764983 : Blo 1044610 1764983 := bstep (se 1 (by rfl) ⟨1323737, by rfl⟩ : syracuseStep 1764983 = 2647475) B2647475
theorem B1568399 : Blo 1044610 1568399 := bstep (se 1 (by rfl) ⟨1176299, by rfl⟩ : syracuseStep 1568399 = 2352599) B2352599
theorem B1568441 : Blo 1044610 1568441 := bstep (se 2 (by rfl) ⟨588165, by rfl⟩ : syracuseStep 1568441 = 1176331) B1176331
theorem B1568519 : Blo 1044610 1568519 := bstep (se 1 (by rfl) ⟨1176389, by rfl⟩ : syracuseStep 1568519 = 2352779) B2352779
theorem B5959439 : Blo 1044610 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B1568555 : Blo 1044610 1568555 := bstep (se 1 (by rfl) ⟨1176416, by rfl⟩ : syracuseStep 1568555 = 2352833) B2352833
theorem B1568585 : Blo 1044610 1568585 := bstep (se 2 (by rfl) ⟨588219, by rfl⟩ : syracuseStep 1568585 = 1176439) B1176439
theorem B1175431 : Blo 1044610 1175431 := bstep (se 1 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 1175431 = 1763147) B1763147
theorem B8056729 : Blo 1044610 8056729 := bstep (se 2 (by rfl) ⟨3021273, by rfl⟩ : syracuseStep 8056729 = 6042547) B6042547
theorem B1568699 : Blo 1044610 1568699 := bstep (se 1 (by rfl) ⟨1176524, by rfl⟩ : syracuseStep 1568699 = 2353049) B2353049
theorem B1568759 : Blo 1044610 1568759 := bstep (se 1 (by rfl) ⟨1176569, by rfl⟩ : syracuseStep 1568759 = 2353139) B2353139
theorem B1568783 : Blo 1044610 1568783 := bstep (se 1 (by rfl) ⟨1176587, by rfl⟩ : syracuseStep 1568783 = 2353175) B2353175
theorem B5369885 : Blo 1044610 5369885 := bstep (se 3 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 5369885 = 2013707) B2013707
theorem B1568825 : Blo 1044610 1568825 := bstep (se 2 (by rfl) ⟨588309, by rfl⟩ : syracuseStep 1568825 = 1176619) B1176619
theorem B1175611 : Blo 1044610 1175611 := bstep (se 1 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 1175611 = 1763417) B1763417
theorem B1765435 : Blo 1044610 1765435 := bstep (se 1 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 1765435 = 2648153) B2648153
theorem B12087413 : Blo 1044610 12087413 := bstep (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) B1133195
theorem B1044615 : Blo 1044610 1044615 := bstep (se 1 (by rfl) ⟨783461, by rfl⟩ : syracuseStep 1044615 = 1566923) B1566923
theorem B1568903 : Blo 1044610 1568903 := bstep (se 1 (by rfl) ⟨1176677, by rfl⟩ : syracuseStep 1568903 = 2353355) B2353355
theorem B2355335 : Blo 1044610 2355335 := bstep (se 1 (by rfl) ⟨1766501, by rfl⟩ : syracuseStep 2355335 = 3533003) B3533003
theorem B1044623 : Blo 1044610 1044623 := bstep (se 1 (by rfl) ⟨783467, by rfl⟩ : syracuseStep 1044623 = 1566935) B1566935
theorem B2650259 : Blo 1044610 2650259 := bstep (se 1 (by rfl) ⟨1987694, by rfl⟩ : syracuseStep 2650259 = 3975389) B3975389
theorem B1568939 : Blo 1044610 1568939 := bstep (se 1 (by rfl) ⟨1176704, by rfl⟩ : syracuseStep 1568939 = 2353409) B2353409
theorem B1044667 : Blo 1044610 1044667 := bstep (se 1 (by rfl) ⟨783500, by rfl⟩ : syracuseStep 1044667 = 1567001) B1567001
theorem B1568969 : Blo 1044610 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B1765577 : Blo 1044610 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B1044743 : Blo 1044610 1044743 := bstep (se 1 (by rfl) ⟨783557, by rfl⟩ : syracuseStep 1044743 = 1567115) B1567115
theorem B1044751 : Blo 1044610 1044751 := bstep (se 1 (by rfl) ⟨783563, by rfl⟩ : syracuseStep 1044751 = 1567127) B1567127
theorem B1044795 : Blo 1044610 1044795 := bstep (se 1 (by rfl) ⟨783596, by rfl⟩ : syracuseStep 1044795 = 1567193) B1567193
theorem B1569083 : Blo 1044610 1569083 := bstep (se 1 (by rfl) ⟨1176812, by rfl⟩ : syracuseStep 1569083 = 2353625) B2353625
theorem B2355515 : Blo 1044610 2355515 := bstep (se 1 (by rfl) ⟨1766636, by rfl⟩ : syracuseStep 2355515 = 3533273) B3533273
theorem B3535163 : Blo 1044610 3535163 := bstep (se 1 (by rfl) ⟨2651372, by rfl⟩ : syracuseStep 3535163 = 5302745) B5302745
theorem B1569143 : Blo 1044610 1569143 := bstep (se 1 (by rfl) ⟨1176857, by rfl⟩ : syracuseStep 1569143 = 2353715) B2353715
theorem B1044871 : Blo 1044610 1044871 := bstep (se 1 (by rfl) ⟨783653, by rfl⟩ : syracuseStep 1044871 = 1567307) B1567307
theorem B1044879 : Blo 1044610 1044879 := bstep (se 1 (by rfl) ⟨783659, by rfl⟩ : syracuseStep 1044879 = 1567319) B1567319
theorem B1569167 : Blo 1044610 1569167 := bstep (se 1 (by rfl) ⟨1176875, by rfl⟩ : syracuseStep 1569167 = 2353751) B2353751
theorem B1569209 : Blo 1044610 1569209 := bstep (se 2 (by rfl) ⟨588453, by rfl⟩ : syracuseStep 1569209 = 1176907) B1176907
theorem B2355641 : Blo 1044610 2355641 := bstep (se 2 (by rfl) ⟨883365, by rfl⟩ : syracuseStep 2355641 = 1766731) B1766731
theorem B1044923 : Blo 1044610 1044923 := bstep (se 1 (by rfl) ⟨783692, by rfl⟩ : syracuseStep 1044923 = 1567385) B1567385
theorem B2650553 : Blo 1044610 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B1044999 : Blo 1044610 1044999 := bstep (se 1 (by rfl) ⟨783749, by rfl⟩ : syracuseStep 1044999 = 1567499) B1567499
theorem B1569287 : Blo 1044610 1569287 := bstep (se 1 (by rfl) ⟨1176965, by rfl⟩ : syracuseStep 1569287 = 2353931) B2353931
theorem B1045007 : Blo 1044610 1045007 := bstep (se 1 (by rfl) ⟨783755, by rfl⟩ : syracuseStep 1045007 = 1567511) B1567511
theorem B1176079 : Blo 1044610 1176079 := bstep (se 1 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 1176079 = 1764119) B1764119
theorem B1569323 : Blo 1044610 1569323 := bstep (se 1 (by rfl) ⟨1176992, by rfl⟩ : syracuseStep 1569323 = 2353985) B2353985
theorem B1045051 : Blo 1044610 1045051 := bstep (se 1 (by rfl) ⟨783788, by rfl⟩ : syracuseStep 1045051 = 1567577) B1567577
theorem B1569353 : Blo 1044610 1569353 := bstep (se 2 (by rfl) ⟨588507, by rfl⟩ : syracuseStep 1569353 = 1177015) B1177015
theorem B1045127 : Blo 1044610 1045127 := bstep (se 1 (by rfl) ⟨783845, by rfl⟩ : syracuseStep 1045127 = 1567691) B1567691
theorem B1045135 : Blo 1044610 1045135 := bstep (se 1 (by rfl) ⟨783851, by rfl⟩ : syracuseStep 1045135 = 1567703) B1567703
theorem B1045179 : Blo 1044610 1045179 := bstep (se 1 (by rfl) ⟨783884, by rfl⟩ : syracuseStep 1045179 = 1567769) B1567769
theorem B1569467 : Blo 1044610 1569467 := bstep (se 1 (by rfl) ⟨1177100, by rfl⟩ : syracuseStep 1569467 = 2354201) B2354201
theorem B1569527 : Blo 1044610 1569527 := bstep (se 1 (by rfl) ⟨1177145, by rfl⟩ : syracuseStep 1569527 = 2354291) B2354291
theorem B1045255 : Blo 1044610 1045255 := bstep (se 1 (by rfl) ⟨783941, by rfl⟩ : syracuseStep 1045255 = 1567883) B1567883
theorem B1045263 : Blo 1044610 1045263 := bstep (se 1 (by rfl) ⟨783947, by rfl⟩ : syracuseStep 1045263 = 1567895) B1567895
theorem B1569551 : Blo 1044610 1569551 := bstep (se 1 (by rfl) ⟨1177163, by rfl⟩ : syracuseStep 1569551 = 2354327) B2354327
theorem B2355983 : Blo 1044610 2355983 := bstep (se 1 (by rfl) ⟨1766987, by rfl⟩ : syracuseStep 2355983 = 3533975) B3533975
theorem B2356001 : Blo 1044610 2356001 := bstep (se 2 (by rfl) ⟨883500, by rfl⟩ : syracuseStep 2356001 = 1767001) B1767001
theorem B3535649 : Blo 1044610 3535649 := bstep (se 2 (by rfl) ⟨1325868, by rfl⟩ : syracuseStep 3535649 = 2651737) B2651737
theorem B2978603 : Blo 1044610 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B7533361 : Blo 1044610 7533361 := bstep (se 2 (by rfl) ⟨2825010, by rfl⟩ : syracuseStep 7533361 = 5650021) B5650021
theorem B1569593 : Blo 1044610 1569593 := bstep (se 2 (by rfl) ⟨588597, by rfl⟩ : syracuseStep 1569593 = 1177195) B1177195
theorem B1045307 : Blo 1044610 1045307 := bstep (se 1 (by rfl) ⟨783980, by rfl⟩ : syracuseStep 1045307 = 1567961) B1567961
theorem B1045383 : Blo 1044610 1045383 := bstep (se 1 (by rfl) ⟨784037, by rfl⟩ : syracuseStep 1045383 = 1568075) B1568075
theorem B1569671 : Blo 1044610 1569671 := bstep (se 1 (by rfl) ⟨1177253, by rfl⟩ : syracuseStep 1569671 = 2354507) B2354507
theorem B1766279 : Blo 1044610 1766279 := bstep (se 1 (by rfl) ⟨1324709, by rfl⟩ : syracuseStep 1766279 = 2649419) B2649419
theorem B1045391 : Blo 1044610 1045391 := bstep (se 1 (by rfl) ⟨784043, by rfl⟩ : syracuseStep 1045391 = 1568087) B1568087
theorem B1569707 : Blo 1044610 1569707 := bstep (se 1 (by rfl) ⟨1177280, by rfl⟩ : syracuseStep 1569707 = 2354561) B2354561
theorem B1045435 : Blo 1044610 1045435 := bstep (se 1 (by rfl) ⟨784076, by rfl⟩ : syracuseStep 1045435 = 1568153) B1568153
theorem B1569737 : Blo 1044610 1569737 := bstep (se 2 (by rfl) ⟨588651, by rfl⟩ : syracuseStep 1569737 = 1177303) B1177303
theorem B1045511 : Blo 1044610 1045511 := bstep (se 1 (by rfl) ⟨784133, by rfl⟩ : syracuseStep 1045511 = 1568267) B1568267
theorem B1176583 : Blo 1044610 1176583 := bstep (se 1 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 1176583 = 1764875) B1764875
theorem B1045519 : Blo 1044610 1045519 := bstep (se 1 (by rfl) ⟨784139, by rfl⟩ : syracuseStep 1045519 = 1568279) B1568279
theorem B2978831 : Blo 1044610 2978831 := bstep (se 1 (by rfl) ⟨2234123, by rfl⟩ : syracuseStep 2978831 = 4468247) B4468247
theorem B2683937 : Blo 1044610 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B1045563 : Blo 1044610 1045563 := bstep (se 1 (by rfl) ⟨784172, by rfl⟩ : syracuseStep 1045563 = 1568345) B1568345
theorem B1569851 : Blo 1044610 1569851 := bstep (se 1 (by rfl) ⟨1177388, by rfl⟩ : syracuseStep 1569851 = 2354777) B2354777
theorem B2651251 : Blo 1044610 2651251 := bstep (se 1 (by rfl) ⟨1988438, by rfl⟩ : syracuseStep 2651251 = 3976877) B3976877
theorem B1569911 : Blo 1044610 1569911 := bstep (se 1 (by rfl) ⟨1177433, by rfl⟩ : syracuseStep 1569911 = 2354867) B2354867
theorem B2356343 : Blo 1044610 2356343 := bstep (se 1 (by rfl) ⟨1767257, by rfl⟩ : syracuseStep 2356343 = 3534515) B3534515
theorem B1045639 : Blo 1044610 1045639 := bstep (se 1 (by rfl) ⟨784229, by rfl⟩ : syracuseStep 1045639 = 1568459) B1568459
theorem B1045647 : Blo 1044610 1045647 := bstep (se 1 (by rfl) ⟨784235, by rfl⟩ : syracuseStep 1045647 = 1568471) B1568471
theorem B1569935 : Blo 1044610 1569935 := bstep (se 1 (by rfl) ⟨1177451, by rfl⟩ : syracuseStep 1569935 = 2354903) B2354903
theorem B1569977 : Blo 1044610 1569977 := bstep (se 2 (by rfl) ⟨588741, by rfl⟩ : syracuseStep 1569977 = 1177483) B1177483
theorem B1045691 : Blo 1044610 1045691 := bstep (se 1 (by rfl) ⟨784268, by rfl⟩ : syracuseStep 1045691 = 1568537) B1568537
theorem B1176763 : Blo 1044610 1176763 := bstep (se 1 (by rfl) ⟨882572, by rfl⟩ : syracuseStep 1176763 = 1765145) B1765145
theorem B5960897 : Blo 1044610 5960897 := bstep (se 2 (by rfl) ⟨2235336, by rfl⟩ : syracuseStep 5960897 = 4470673) B4470673
theorem B6714569 : Blo 1044610 6714569 := bstep (se 2 (by rfl) ⟨2517963, by rfl⟩ : syracuseStep 6714569 = 5035927) B5035927
theorem B2651393 : Blo 1044610 2651393 := bstep (se 2 (by rfl) ⟨994272, by rfl⟩ : syracuseStep 2651393 = 1988545) B1988545
theorem B1045767 : Blo 1044610 1045767 := bstep (se 1 (by rfl) ⟨784325, by rfl⟩ : syracuseStep 1045767 = 1568651) B1568651
theorem B1570055 : Blo 1044610 1570055 := bstep (se 1 (by rfl) ⟨1177541, by rfl⟩ : syracuseStep 1570055 = 2355083) B2355083
theorem B1045775 : Blo 1044610 1045775 := bstep (se 1 (by rfl) ⟨784331, by rfl⟩ : syracuseStep 1045775 = 1568663) B1568663
theorem B1570091 : Blo 1044610 1570091 := bstep (se 1 (by rfl) ⟨1177568, by rfl⟩ : syracuseStep 1570091 = 2355137) B2355137
theorem B2356523 : Blo 1044610 2356523 := bstep (se 1 (by rfl) ⟨1767392, by rfl⟩ : syracuseStep 2356523 = 3534785) B3534785
theorem B1045819 : Blo 1044610 1045819 := bstep (se 1 (by rfl) ⟨784364, by rfl⟩ : syracuseStep 1045819 = 1568729) B1568729
theorem B1570121 : Blo 1044610 1570121 := bstep (se 2 (by rfl) ⟨588795, by rfl⟩ : syracuseStep 1570121 = 1177591) B1177591
theorem B3536243 : Blo 1044610 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1045895 : Blo 1044610 1045895 := bstep (se 1 (by rfl) ⟨784421, by rfl⟩ : syracuseStep 1045895 = 1568843) B1568843
theorem B1045903 : Blo 1044610 1045903 := bstep (se 1 (by rfl) ⟨784427, by rfl⟩ : syracuseStep 1045903 = 1568855) B1568855
theorem B1045947 : Blo 1044610 1045947 := bstep (se 1 (by rfl) ⟨784460, by rfl⟩ : syracuseStep 1045947 = 1568921) B1568921
theorem B1570235 : Blo 1044610 1570235 := bstep (se 1 (by rfl) ⟨1177676, by rfl⟩ : syracuseStep 1570235 = 2355353) B2355353
theorem B1570295 : Blo 1044610 1570295 := bstep (se 1 (by rfl) ⟨1177721, by rfl⟩ : syracuseStep 1570295 = 2355443) B2355443
theorem B1046023 : Blo 1044610 1046023 := bstep (se 1 (by rfl) ⟨784517, by rfl⟩ : syracuseStep 1046023 = 1569035) B1569035
theorem B1046031 : Blo 1044610 1046031 := bstep (se 1 (by rfl) ⟨784523, by rfl⟩ : syracuseStep 1046031 = 1569047) B1569047
theorem B1570319 : Blo 1044610 1570319 := bstep (se 1 (by rfl) ⟨1177739, by rfl⟩ : syracuseStep 1570319 = 2355479) B2355479
theorem B1766927 : Blo 1044610 1766927 := bstep (se 1 (by rfl) ⟨1325195, by rfl⟩ : syracuseStep 1766927 = 2650391) B2650391
theorem B2684449 : Blo 1044610 2684449 := bstep (se 2 (by rfl) ⟨1006668, by rfl⟩ : syracuseStep 2684449 = 2013337) B2013337
theorem B1570361 : Blo 1044610 1570361 := bstep (se 2 (by rfl) ⟨588885, by rfl⟩ : syracuseStep 1570361 = 1177771) B1177771
theorem B1046075 : Blo 1044610 1046075 := bstep (se 1 (by rfl) ⟨784556, by rfl⟩ : syracuseStep 1046075 = 1569113) B1569113
theorem B1046151 : Blo 1044610 1046151 := bstep (se 1 (by rfl) ⟨784613, by rfl⟩ : syracuseStep 1046151 = 1569227) B1569227
theorem B1570439 : Blo 1044610 1570439 := bstep (se 1 (by rfl) ⟨1177829, by rfl⟩ : syracuseStep 1570439 = 2355659) B2355659
theorem B1046159 : Blo 1044610 1046159 := bstep (se 1 (by rfl) ⟨784619, by rfl⟩ : syracuseStep 1046159 = 1569239) B1569239
theorem B1177231 : Blo 1044610 1177231 := bstep (se 1 (by rfl) ⟨882923, by rfl⟩ : syracuseStep 1177231 = 1765847) B1765847
theorem B2356883 : Blo 1044610 2356883 := bstep (se 1 (by rfl) ⟨1767662, by rfl⟩ : syracuseStep 2356883 = 3535325) B3535325
theorem B1570475 : Blo 1044610 1570475 := bstep (se 1 (by rfl) ⟨1177856, by rfl⟩ : syracuseStep 1570475 = 2355713) B2355713
theorem B1046203 : Blo 1044610 1046203 := bstep (se 1 (by rfl) ⟨784652, by rfl⟩ : syracuseStep 1046203 = 1569305) B1569305
theorem B1570505 : Blo 1044610 1570505 := bstep (se 2 (by rfl) ⟨588939, by rfl⟩ : syracuseStep 1570505 = 1177879) B1177879
theorem B2356937 : Blo 1044610 2356937 := bstep (se 2 (by rfl) ⟨883851, by rfl⟩ : syracuseStep 2356937 = 1767703) B1767703
theorem B2651849 : Blo 1044610 2651849 := bstep (se 2 (by rfl) ⟨994443, by rfl⟩ : syracuseStep 2651849 = 1988887) B1988887
theorem B1046279 : Blo 1044610 1046279 := bstep (se 1 (by rfl) ⟨784709, by rfl⟩ : syracuseStep 1046279 = 1569419) B1569419
theorem B1046287 : Blo 1044610 1046287 := bstep (se 1 (by rfl) ⟨784715, by rfl⟩ : syracuseStep 1046287 = 1569431) B1569431
theorem B1046331 : Blo 1044610 1046331 := bstep (se 1 (by rfl) ⟨784748, by rfl⟩ : syracuseStep 1046331 = 1569497) B1569497
theorem B1570619 : Blo 1044610 1570619 := bstep (se 1 (by rfl) ⟨1177964, by rfl⟩ : syracuseStep 1570619 = 2355929) B2355929
theorem B1570679 : Blo 1044610 1570679 := bstep (se 1 (by rfl) ⟨1178009, by rfl⟩ : syracuseStep 1570679 = 2356019) B2356019
theorem B1046407 : Blo 1044610 1046407 := bstep (se 1 (by rfl) ⟨784805, by rfl⟩ : syracuseStep 1046407 = 1569611) B1569611
theorem B1046415 : Blo 1044610 1046415 := bstep (se 1 (by rfl) ⟨784811, by rfl⟩ : syracuseStep 1046415 = 1569623) B1569623
theorem B1570703 : Blo 1044610 1570703 := bstep (se 1 (by rfl) ⟨1178027, by rfl⟩ : syracuseStep 1570703 = 2356055) B2356055
theorem B1570745 : Blo 1044610 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B1046459 : Blo 1044610 1046459 := bstep (se 1 (by rfl) ⟨784844, by rfl⟩ : syracuseStep 1046459 = 1569689) B1569689
theorem B1046535 : Blo 1044610 1046535 := bstep (se 1 (by rfl) ⟨784901, by rfl⟩ : syracuseStep 1046535 = 1569803) B1569803
theorem B1570823 : Blo 1044610 1570823 := bstep (se 1 (by rfl) ⟨1178117, by rfl⟩ : syracuseStep 1570823 = 2356235) B2356235
theorem B1046543 : Blo 1044610 1046543 := bstep (se 1 (by rfl) ⟨784907, by rfl⟩ : syracuseStep 1046543 = 1569815) B1569815
theorem B1570859 : Blo 1044610 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B1767467 : Blo 1044610 1767467 := bstep (se 1 (by rfl) ⟨1325600, by rfl⟩ : syracuseStep 1767467 = 2651201) B2651201
theorem B2652203 : Blo 1044610 2652203 := bstep (se 1 (by rfl) ⟨1989152, by rfl⟩ : syracuseStep 2652203 = 3978305) B3978305
theorem B1046587 : Blo 1044610 1046587 := bstep (se 1 (by rfl) ⟨784940, by rfl⟩ : syracuseStep 1046587 = 1569881) B1569881
theorem B1570889 : Blo 1044610 1570889 := bstep (se 2 (by rfl) ⟨589083, by rfl⟩ : syracuseStep 1570889 = 1178167) B1178167
theorem B1046663 : Blo 1044610 1046663 := bstep (se 1 (by rfl) ⟨784997, by rfl⟩ : syracuseStep 1046663 = 1569995) B1569995
theorem B1177735 : Blo 1044610 1177735 := bstep (se 1 (by rfl) ⟨883301, by rfl⟩ : syracuseStep 1177735 = 1766603) B1766603
theorem B1046671 : Blo 1044610 1046671 := bstep (se 1 (by rfl) ⟨785003, by rfl⟩ : syracuseStep 1046671 = 1570007) B1570007
theorem B1046715 : Blo 1044610 1046715 := bstep (se 1 (by rfl) ⟨785036, by rfl⟩ : syracuseStep 1046715 = 1570073) B1570073
theorem B1571003 : Blo 1044610 1571003 := bstep (se 1 (by rfl) ⟨1178252, by rfl⟩ : syracuseStep 1571003 = 2356505) B2356505
theorem B1571063 : Blo 1044610 1571063 := bstep (se 1 (by rfl) ⟨1178297, by rfl⟩ : syracuseStep 1571063 = 2356595) B2356595
theorem B1046791 : Blo 1044610 1046791 := bstep (se 1 (by rfl) ⟨785093, by rfl⟩ : syracuseStep 1046791 = 1570187) B1570187
theorem B1046799 : Blo 1044610 1046799 := bstep (se 1 (by rfl) ⟨785099, by rfl⟩ : syracuseStep 1046799 = 1570199) B1570199
theorem B1571087 : Blo 1044610 1571087 := bstep (se 1 (by rfl) ⟨1178315, by rfl⟩ : syracuseStep 1571087 = 2356631) B2356631
theorem B1571129 : Blo 1044610 1571129 := bstep (se 2 (by rfl) ⟨589173, by rfl⟩ : syracuseStep 1571129 = 1178347) B1178347
theorem B1046843 : Blo 1044610 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B1177915 : Blo 1044610 1177915 := bstep (se 1 (by rfl) ⟨883436, by rfl⟩ : syracuseStep 1177915 = 1766873) B1766873
theorem B1046919 : Blo 1044610 1046919 := bstep (se 1 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 1046919 = 1570379) B1570379
theorem B1571207 : Blo 1044610 1571207 := bstep (se 1 (by rfl) ⟨1178405, by rfl⟩ : syracuseStep 1571207 = 2356811) B2356811
theorem B2357639 : Blo 1044610 2357639 := bstep (se 1 (by rfl) ⟨1768229, by rfl⟩ : syracuseStep 2357639 = 3536459) B3536459
theorem B1046927 : Blo 1044610 1046927 := bstep (se 1 (by rfl) ⟨785195, by rfl⟩ : syracuseStep 1046927 = 1570391) B1570391
theorem B2980243 : Blo 1044610 2980243 := bstep (se 1 (by rfl) ⟨2235182, by rfl⟩ : syracuseStep 2980243 = 4470365) B4470365
theorem B1571243 : Blo 1044610 1571243 := bstep (se 1 (by rfl) ⟨1178432, by rfl⟩ : syracuseStep 1571243 = 2356865) B2356865
theorem B1767865 : Blo 1044610 1767865 := bstep (se 2 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 1767865 = 1325899) B1325899
theorem B1046971 : Blo 1044610 1046971 := bstep (se 1 (by rfl) ⟨785228, by rfl⟩ : syracuseStep 1046971 = 1570457) B1570457
theorem B1571273 : Blo 1044610 1571273 := bstep (se 2 (by rfl) ⟨589227, by rfl⟩ : syracuseStep 1571273 = 1178455) B1178455
theorem B1047047 : Blo 1044610 1047047 := bstep (se 1 (by rfl) ⟨785285, by rfl⟩ : syracuseStep 1047047 = 1570571) B1570571
theorem B1047055 : Blo 1044610 1047055 := bstep (se 1 (by rfl) ⟨785291, by rfl⟩ : syracuseStep 1047055 = 1570583) B1570583
theorem B1047099 : Blo 1044610 1047099 := bstep (se 1 (by rfl) ⟨785324, by rfl⟩ : syracuseStep 1047099 = 1570649) B1570649
theorem B1571387 : Blo 1044610 1571387 := bstep (se 1 (by rfl) ⟨1178540, by rfl⟩ : syracuseStep 1571387 = 2357081) B2357081
theorem B2357819 : Blo 1044610 2357819 := bstep (se 1 (by rfl) ⟨1768364, by rfl⟩ : syracuseStep 2357819 = 3536729) B3536729
theorem B7961165 : Blo 1044610 7961165 := bstep (se 3 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 7961165 = 2985437) B2985437
theorem B2980471 : Blo 1044610 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B1571447 : Blo 1044610 1571447 := bstep (se 1 (by rfl) ⟨1178585, by rfl⟩ : syracuseStep 1571447 = 2357171) B2357171
theorem B1047175 : Blo 1044610 1047175 := bstep (se 1 (by rfl) ⟨785381, by rfl⟩ : syracuseStep 1047175 = 1570763) B1570763
theorem B1047183 : Blo 1044610 1047183 := bstep (se 1 (by rfl) ⟨785387, by rfl⟩ : syracuseStep 1047183 = 1570775) B1570775
theorem B1571471 : Blo 1044610 1571471 := bstep (se 1 (by rfl) ⟨1178603, by rfl⟩ : syracuseStep 1571471 = 2357207) B2357207
theorem B1571513 : Blo 1044610 1571513 := bstep (se 2 (by rfl) ⟨589317, by rfl⟩ : syracuseStep 1571513 = 1178635) B1178635
theorem B2357945 : Blo 1044610 2357945 := bstep (se 2 (by rfl) ⟨884229, by rfl⟩ : syracuseStep 2357945 = 1768459) B1768459
theorem B1047227 : Blo 1044610 1047227 := bstep (se 1 (by rfl) ⟨785420, by rfl⟩ : syracuseStep 1047227 = 1570841) B1570841
theorem B1047303 : Blo 1044610 1047303 := bstep (se 1 (by rfl) ⟨785477, by rfl⟩ : syracuseStep 1047303 = 1570955) B1570955
theorem B1571591 : Blo 1044610 1571591 := bstep (se 1 (by rfl) ⟨1178693, by rfl⟩ : syracuseStep 1571591 = 2357387) B2357387
theorem B1047311 : Blo 1044610 1047311 := bstep (se 1 (by rfl) ⟨785483, by rfl⟩ : syracuseStep 1047311 = 1570967) B1570967
theorem B1178383 : Blo 1044610 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B1571627 : Blo 1044610 1571627 := bstep (se 1 (by rfl) ⟨1178720, by rfl⟩ : syracuseStep 1571627 = 2357441) B2357441
theorem B1047355 : Blo 1044610 1047355 := bstep (se 1 (by rfl) ⟨785516, by rfl⟩ : syracuseStep 1047355 = 1571033) B1571033
theorem B1571657 : Blo 1044610 1571657 := bstep (se 2 (by rfl) ⟨589371, by rfl⟩ : syracuseStep 1571657 = 1178743) B1178743
theorem B1047431 : Blo 1044610 1047431 := bstep (se 1 (by rfl) ⟨785573, by rfl⟩ : syracuseStep 1047431 = 1571147) B1571147
theorem B1047439 : Blo 1044610 1047439 := bstep (se 1 (by rfl) ⟨785579, by rfl⟩ : syracuseStep 1047439 = 1571159) B1571159
theorem B5307281 : Blo 1044610 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B1047483 : Blo 1044610 1047483 := bstep (se 1 (by rfl) ⟨785612, by rfl⟩ : syracuseStep 1047483 = 1571225) B1571225
theorem B1571771 : Blo 1044610 1571771 := bstep (se 1 (by rfl) ⟨1178828, by rfl⟩ : syracuseStep 1571771 = 2357657) B2357657
theorem B1571831 : Blo 1044610 1571831 := bstep (se 1 (by rfl) ⟨1178873, by rfl⟩ : syracuseStep 1571831 = 2357747) B2357747
theorem B97876997 : Blo 1044610 97876997 := bstep (se 4 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 97876997 = 18351937) B18351937
theorem B1047559 : Blo 1044610 1047559 := bstep (se 1 (by rfl) ⟨785669, by rfl⟩ : syracuseStep 1047559 = 1571339) B1571339
theorem B2653195 : Blo 1044610 2653195 := bstep (se 1 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 2653195 = 3979793) B3979793
theorem B1047567 : Blo 1044610 1047567 := bstep (se 1 (by rfl) ⟨785675, by rfl⟩ : syracuseStep 1047567 = 1571351) B1571351
theorem B1571855 : Blo 1044610 1571855 := bstep (se 1 (by rfl) ⟨1178891, by rfl⟩ : syracuseStep 1571855 = 2357783) B2357783
theorem B2358287 : Blo 1044610 2358287 := bstep (se 1 (by rfl) ⟨1768715, by rfl⟩ : syracuseStep 2358287 = 3537431) B3537431
theorem B2358305 : Blo 1044610 2358305 := bstep (se 2 (by rfl) ⟨884364, by rfl⟩ : syracuseStep 2358305 = 1768729) B1768729
theorem B1571897 : Blo 1044610 1571897 := bstep (se 2 (by rfl) ⟨589461, by rfl⟩ : syracuseStep 1571897 = 1178923) B1178923
theorem B1047611 : Blo 1044610 1047611 := bstep (se 1 (by rfl) ⟨785708, by rfl⟩ : syracuseStep 1047611 = 1571417) B1571417
theorem B1768567 : Blo 1044610 1768567 := bstep (se 1 (by rfl) ⟨1326425, by rfl⟩ : syracuseStep 1768567 = 2652851) B2652851
theorem B1047687 : Blo 1044610 1047687 := bstep (se 1 (by rfl) ⟨785765, by rfl⟩ : syracuseStep 1047687 = 1571531) B1571531
theorem B1571975 : Blo 1044610 1571975 := bstep (se 1 (by rfl) ⟨1178981, by rfl⟩ : syracuseStep 1571975 = 2357963) B2357963
theorem B1047695 : Blo 1044610 1047695 := bstep (se 1 (by rfl) ⟨785771, by rfl⟩ : syracuseStep 1047695 = 1571543) B1571543
theorem B2653337 : Blo 1044610 2653337 := bstep (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) B1990003
theorem B1572011 : Blo 1044610 1572011 := bstep (se 1 (by rfl) ⟨1179008, by rfl⟩ : syracuseStep 1572011 = 2358017) B2358017
theorem B1047739 : Blo 1044610 1047739 := bstep (se 1 (by rfl) ⟨785804, by rfl⟩ : syracuseStep 1047739 = 1571609) B1571609
theorem B1572041 : Blo 1044610 1572041 := bstep (se 2 (by rfl) ⟨589515, by rfl⟩ : syracuseStep 1572041 = 1179031) B1179031
theorem B1047815 : Blo 1044610 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B1178887 : Blo 1044610 1178887 := bstep (se 1 (by rfl) ⟨884165, by rfl⟩ : syracuseStep 1178887 = 1768331) B1768331
theorem B1047823 : Blo 1044610 1047823 := bstep (se 1 (by rfl) ⟨785867, by rfl⟩ : syracuseStep 1047823 = 1571735) B1571735
theorem B1047867 : Blo 1044610 1047867 := bstep (se 1 (by rfl) ⟨785900, by rfl⟩ : syracuseStep 1047867 = 1571801) B1571801
theorem B1572155 : Blo 1044610 1572155 := bstep (se 1 (by rfl) ⟨1179116, by rfl⟩ : syracuseStep 1572155 = 2358233) B2358233
theorem B1768763 : Blo 1044610 1768763 := bstep (se 1 (by rfl) ⟨1326572, by rfl⟩ : syracuseStep 1768763 = 2653145) B2653145
theorem B2653499 : Blo 1044610 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B1572215 : Blo 1044610 1572215 := bstep (se 1 (by rfl) ⟨1179161, by rfl⟩ : syracuseStep 1572215 = 2358323) B2358323
theorem B2358647 : Blo 1044610 2358647 := bstep (se 1 (by rfl) ⟨1768985, by rfl⟩ : syracuseStep 2358647 = 3537971) B3537971
theorem B1047943 : Blo 1044610 1047943 := bstep (se 1 (by rfl) ⟨785957, by rfl⟩ : syracuseStep 1047943 = 1571915) B1571915
theorem B1047951 : Blo 1044610 1047951 := bstep (se 1 (by rfl) ⟨785963, by rfl⟩ : syracuseStep 1047951 = 1571927) B1571927
theorem B1572239 : Blo 1044610 1572239 := bstep (se 1 (by rfl) ⟨1179179, by rfl⟩ : syracuseStep 1572239 = 2358359) B2358359
theorem B8060305 : Blo 1044610 8060305 := bstep (se 2 (by rfl) ⟨3022614, by rfl⟩ : syracuseStep 8060305 = 6045229) B6045229
theorem B1572281 : Blo 1044610 1572281 := bstep (se 2 (by rfl) ⟨589605, by rfl⟩ : syracuseStep 1572281 = 1179211) B1179211
theorem B1047995 : Blo 1044610 1047995 := bstep (se 1 (by rfl) ⟨785996, by rfl⟩ : syracuseStep 1047995 = 1571993) B1571993
theorem B1179067 : Blo 1044610 1179067 := bstep (se 1 (by rfl) ⟨884300, by rfl⟩ : syracuseStep 1179067 = 1768601) B1768601
theorem B1048071 : Blo 1044610 1048071 := bstep (se 1 (by rfl) ⟨786053, by rfl⟩ : syracuseStep 1048071 = 1572107) B1572107
theorem B1572359 : Blo 1044610 1572359 := bstep (se 1 (by rfl) ⟨1179269, by rfl⟩ : syracuseStep 1572359 = 2358539) B2358539
theorem B1048079 : Blo 1044610 1048079 := bstep (se 1 (by rfl) ⟨786059, by rfl⟩ : syracuseStep 1048079 = 1572119) B1572119
theorem B1572395 : Blo 1044610 1572395 := bstep (se 1 (by rfl) ⟨1179296, by rfl⟩ : syracuseStep 1572395 = 2358593) B2358593
theorem B2358827 : Blo 1044610 2358827 := bstep (se 1 (by rfl) ⟨1769120, by rfl⟩ : syracuseStep 2358827 = 3538241) B3538241
theorem B1048123 : Blo 1044610 1048123 := bstep (se 1 (by rfl) ⟨786092, by rfl⟩ : syracuseStep 1048123 = 1572185) B1572185
theorem B1572425 : Blo 1044610 1572425 := bstep (se 2 (by rfl) ⟨589659, by rfl⟩ : syracuseStep 1572425 = 1179319) B1179319
theorem B1048199 : Blo 1044610 1048199 := bstep (se 1 (by rfl) ⟨786149, by rfl⟩ : syracuseStep 1048199 = 1572299) B1572299
theorem B1048207 : Blo 1044610 1048207 := bstep (se 1 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 1048207 = 1572311) B1572311
theorem B2653843 : Blo 1044610 2653843 := bstep (se 1 (by rfl) ⟨1990382, by rfl⟩ : syracuseStep 2653843 = 3980765) B3980765
theorem B1048251 : Blo 1044610 1048251 := bstep (se 1 (by rfl) ⟨786188, by rfl⟩ : syracuseStep 1048251 = 1572377) B1572377
theorem B1572539 : Blo 1044610 1572539 := bstep (se 1 (by rfl) ⟨1179404, by rfl⟩ : syracuseStep 1572539 = 2358809) B2358809
theorem B1769161 : Blo 1044610 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B20086501 : Blo 1044610 20086501 := bstep (se 4 (by rfl) ⟨1883109, by rfl⟩ : syracuseStep 20086501 = 3766219) B3766219
theorem B1572599 : Blo 1044610 1572599 := bstep (se 1 (by rfl) ⟨1179449, by rfl⟩ : syracuseStep 1572599 = 2358899) B2358899
theorem B1048327 : Blo 1044610 1048327 := bstep (se 1 (by rfl) ⟨786245, by rfl⟩ : syracuseStep 1048327 = 1572491) B1572491
theorem B1048335 : Blo 1044610 1048335 := bstep (se 1 (by rfl) ⟨786251, by rfl⟩ : syracuseStep 1048335 = 1572503) B1572503
theorem B1572623 : Blo 1044610 1572623 := bstep (se 1 (by rfl) ⟨1179467, by rfl⟩ : syracuseStep 1572623 = 2358935) B2358935
theorem B2653985 : Blo 1044610 2653985 := bstep (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) B1990489
theorem B1572665 : Blo 1044610 1572665 := bstep (se 2 (by rfl) ⟨589749, by rfl⟩ : syracuseStep 1572665 = 1179499) B1179499
theorem B1048379 : Blo 1044610 1048379 := bstep (se 1 (by rfl) ⟨786284, by rfl⟩ : syracuseStep 1048379 = 1572569) B1572569
theorem B2981747 : Blo 1044610 2981747 := bstep (se 1 (by rfl) ⟨2236310, by rfl⟩ : syracuseStep 2981747 = 4472621) B4472621
theorem B1048455 : Blo 1044610 1048455 := bstep (se 1 (by rfl) ⟨786341, by rfl⟩ : syracuseStep 1048455 = 1572683) B1572683
theorem B1572743 : Blo 1044610 1572743 := bstep (se 1 (by rfl) ⟨1179557, by rfl⟩ : syracuseStep 1572743 = 2359115) B2359115
theorem B1048463 : Blo 1044610 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B1179535 : Blo 1044610 1179535 := bstep (se 1 (by rfl) ⟨884651, by rfl⟩ : syracuseStep 1179535 = 1769303) B1769303
theorem B2359187 : Blo 1044610 2359187 := bstep (se 1 (by rfl) ⟨1769390, by rfl⟩ : syracuseStep 2359187 = 3538781) B3538781
theorem B3538835 : Blo 1044610 3538835 := bstep (se 1 (by rfl) ⟨2654126, by rfl⟩ : syracuseStep 3538835 = 5308253) B5308253
theorem B1572779 : Blo 1044610 1572779 := bstep (se 1 (by rfl) ⟨1179584, by rfl⟩ : syracuseStep 1572779 = 2359169) B2359169
theorem B1048507 : Blo 1044610 1048507 := bstep (se 1 (by rfl) ⟨786380, by rfl⟩ : syracuseStep 1048507 = 1572761) B1572761
theorem B1572809 : Blo 1044610 1572809 := bstep (se 2 (by rfl) ⟨589803, by rfl⟩ : syracuseStep 1572809 = 1179607) B1179607
theorem B2359241 : Blo 1044610 2359241 := bstep (se 2 (by rfl) ⟨884715, by rfl⟩ : syracuseStep 2359241 = 1769431) B1769431
theorem B5668879 : Blo 1044610 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B5963813 : Blo 1044610 5963813 := bstep (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) B1118215
theorem B7536797 : Blo 1044610 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B5964313 : Blo 1044610 5964313 := bstep (se 2 (by rfl) ⟨2236617, by rfl⟩ : syracuseStep 5964313 = 4473235) B4473235
theorem B3769249 : Blo 1044610 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B3769363 : Blo 1044610 3769363 := bstep (se 1 (by rfl) ⟨2827022, by rfl⟩ : syracuseStep 3769363 = 5654045) B5654045
theorem B2983159 : Blo 1044610 2983159 := bstep (se 1 (by rfl) ⟨2237369, by rfl⟩ : syracuseStep 2983159 = 4474739) B4474739
theorem B1344863 : Blo 1044610 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B10061171 : Blo 1044610 10061171 := bstep (se 1 (by rfl) ⟨7545878, by rfl⟩ : syracuseStep 10061171 = 15091757) B15091757
theorem B2983387 : Blo 1044610 2983387 := bstep (se 1 (by rfl) ⟨2237540, by rfl⟩ : syracuseStep 2983387 = 4475081) B4475081
theorem B2983547 : Blo 1044610 2983547 := bstep (se 1 (by rfl) ⟨2237660, by rfl⟩ : syracuseStep 2983547 = 4475321) B4475321
theorem B2983787 : Blo 1044610 2983787 := bstep (se 1 (by rfl) ⟨2237840, by rfl⟩ : syracuseStep 2983787 = 4475681) B4475681
theorem B3966839 : Blo 1044610 3966839 := bstep (se 1 (by rfl) ⟨2975129, by rfl⟩ : syracuseStep 3966839 = 5950259) B5950259
theorem B3868729 : Blo 1044610 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B1673465 : Blo 1044610 1673465 := bstep (se 2 (by rfl) ⟨627549, by rfl⟩ : syracuseStep 1673465 = 1255099) B1255099
theorem B2984435 : Blo 1044610 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B1673927 : Blo 1044610 1673927 := bstep (se 1 (by rfl) ⟨1255445, by rfl⟩ : syracuseStep 1673927 = 2510891) B2510891
theorem B2984663 : Blo 1044610 2984663 := bstep (se 1 (by rfl) ⟨2238497, by rfl⟩ : syracuseStep 2984663 = 4476995) B4476995
theorem B3967811 : Blo 1044610 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B15109163 : Blo 1044610 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B7932977 : Blo 1044610 7932977 := bstep (se 2 (by rfl) ⟨2974866, by rfl⟩ : syracuseStep 7932977 = 5949733) B5949733
theorem B5967229 : Blo 1044610 5967229 := bstep (se 3 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 5967229 = 2237711) B2237711
theorem B3018227 : Blo 1044610 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B13405763 : Blo 1044610 13405763 := bstep (se 1 (by rfl) ⟨10054322, by rfl⟩ : syracuseStep 13405763 = 20108645) B20108645
theorem B1674875 : Blo 1044610 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B6786749 : Blo 1044610 6786749 := bstep (se 3 (by rfl) ⟨1272515, by rfl⟩ : syracuseStep 6786749 = 2545031) B2545031
theorem B3968797 : Blo 1044610 3968797 := bstep (se 3 (by rfl) ⟨744149, by rfl⟩ : syracuseStep 3968797 = 1488299) B1488299
theorem B10227575 : Blo 1044610 10227575 := bstep (se 1 (by rfl) ⟨7670681, by rfl⟩ : syracuseStep 10227575 = 15341363) B15341363
theorem B1675183 : Blo 1044610 1675183 := bstep (se 1 (by rfl) ⟨1256387, by rfl⟩ : syracuseStep 1675183 = 2512775) B2512775
theorem B11309219 : Blo 1044610 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B12095819 : Blo 1044610 12095819 := bstep (se 1 (by rfl) ⟨9071864, by rfl⟩ : syracuseStep 12095819 = 18143729) B18143729
theorem B3772909 : Blo 1044610 3772909 := bstep (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) B1414841
theorem B8950297 : Blo 1044610 8950297 := bstep (se 2 (by rfl) ⟨3356361, by rfl⟩ : syracuseStep 8950297 = 6712723) B6712723
theorem B30151439 : Blo 1044610 30151439 := bstep (se 1 (by rfl) ⟨22613579, by rfl⟩ : syracuseStep 30151439 = 45227159) B45227159
theorem B2233423 : Blo 1044610 2233423 := bstep (se 1 (by rfl) ⟨1675067, by rfl⟩ : syracuseStep 2233423 = 3350135) B3350135
theorem B13407403 : Blo 1044610 13407403 := bstep (se 1 (by rfl) ⟨10055552, by rfl⟩ : syracuseStep 13407403 = 20111105) B20111105
theorem B10065167 : Blo 1044610 10065167 := bstep (se 1 (by rfl) ⟨7548875, by rfl⟩ : syracuseStep 10065167 = 15097751) B15097751
theorem B1611343 : Blo 1044610 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B23926873 : Blo 1044610 23926873 := bstep (se 2 (by rfl) ⟨8972577, by rfl⟩ : syracuseStep 23926873 = 17945155) B17945155
theorem B30579079 : Blo 1044610 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B21502343 : Blo 1044610 21502343 := bstep (se 1 (by rfl) ⟨16126757, by rfl⟩ : syracuseStep 21502343 = 32253515) B32253515
theorem B27532021 : Blo 1044610 27532021 := bstep (se 5 (by rfl) ⟨1290563, by rfl⟩ : syracuseStep 27532021 = 2581127) B2581127
theorem B3579265 : Blo 1044610 3579265 := bstep (se 2 (by rfl) ⟨1342224, by rfl⟩ : syracuseStep 3579265 = 2684449) B2684449
theorem B5971603 : Blo 1044610 5971603 := bstep (se 1 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 5971603 = 8957405) B8957405
theorem B10755773 : Blo 1044610 10755773 := bstep (se 3 (by rfl) ⟨2016707, by rfl⟩ : syracuseStep 10755773 = 4033415) B4033415
theorem B3972959 : Blo 1044610 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B3579923 : Blo 1044610 3579923 := bstep (se 1 (by rfl) ⟨2684942, by rfl⟩ : syracuseStep 3579923 = 5369885) B5369885
theorem B12263653 : Blo 1044610 12263653 := bstep (se 4 (by rfl) ⟨1149717, by rfl⟩ : syracuseStep 12263653 = 2299435) B2299435
theorem B8069509 : Blo 1044610 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B7545241 : Blo 1044610 7545241 := bstep (se 2 (by rfl) ⟨2829465, by rfl⟩ : syracuseStep 7545241 = 5658931) B5658931
theorem B1909153 : Blo 1044610 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B2236891 : Blo 1044610 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B3973657 : Blo 1044610 3973657 := bstep (se 2 (by rfl) ⟨1490121, by rfl⟩ : syracuseStep 3973657 = 2980243) B2980243
theorem B3973931 : Blo 1044610 3973931 := bstep (se 1 (by rfl) ⟨2980448, by rfl⟩ : syracuseStep 3973931 = 5960897) B5960897
theorem B3973961 : Blo 1044610 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B2827511 : Blo 1044610 2827511 := bstep (se 1 (by rfl) ⟨2120633, by rfl⟩ : syracuseStep 2827511 = 4241267) B4241267
theorem B8496701 : Blo 1044610 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B4466299 : Blo 1044610 4466299 := bstep (se 1 (by rfl) ⟨3349724, by rfl⟩ : syracuseStep 4466299 = 6699449) B6699449
theorem B3352211 : Blo 1044610 3352211 := bstep (se 1 (by rfl) ⟨2514158, by rfl⟩ : syracuseStep 3352211 = 5028317) B5028317
theorem B8496829 : Blo 1044610 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B65251331 : Blo 1044610 65251331 := bstep (se 1 (by rfl) ⟨48938498, by rfl⟩ : syracuseStep 65251331 = 97876997) B97876997
theorem B26782001 : Blo 1044610 26782001 := bstep (se 2 (by rfl) ⟨10043250, by rfl⟩ : syracuseStep 26782001 = 20086501) B20086501
theorem B6695297 : Blo 1044610 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B595601885 : Blo 1044610 595601885 := bstep (se 3 (by rfl) ⟨111675353, by rfl⟩ : syracuseStep 595601885 = 223350707) B223350707
theorem B3779081 : Blo 1044610 3779081 := bstep (se 2 (by rfl) ⟨1417155, by rfl⟩ : syracuseStep 3779081 = 2834311) B2834311
theorem B2829163 : Blo 1044610 2829163 := bstep (se 1 (by rfl) ⟨2121872, by rfl⟩ : syracuseStep 2829163 = 4243745) B4243745
theorem B4467631 : Blo 1044610 4467631 := bstep (se 1 (by rfl) ⟨3350723, by rfl⟩ : syracuseStep 4467631 = 6701447) B6701447
theorem B7941239 : Blo 1044610 7941239 := bstep (se 1 (by rfl) ⟨5955929, by rfl⟩ : syracuseStep 7941239 = 11911859) B11911859
theorem B50834627 : Blo 1044610 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B1322183 : Blo 1044610 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1322335 : Blo 1044610 1322335 := bstep (se 1 (by rfl) ⟨991751, by rfl⟩ : syracuseStep 1322335 = 1983503) B1983503
theorem B3976573 : Blo 1044610 3976573 := bstep (se 3 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 3976573 = 1491215) B1491215
theorem B1256887 : Blo 1044610 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B1191547 : Blo 1044610 1191547 := bstep (se 1 (by rfl) ⟨893660, by rfl⟩ : syracuseStep 1191547 = 1787321) B1787321
theorem B3583673 : Blo 1044610 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B6696989 : Blo 1044610 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B2045345 : Blo 1044610 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B1324507 : Blo 1044610 1324507 := bstep (se 1 (by rfl) ⟨993380, by rfl⟩ : syracuseStep 1324507 = 1986761) B1986761
theorem B3978791 : Blo 1044610 3978791 := bstep (se 1 (by rfl) ⟨2984093, by rfl⟩ : syracuseStep 3978791 = 5968187) B5968187
theorem B9058007 : Blo 1044610 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B10761977 : Blo 1044610 10761977 := bstep (se 2 (by rfl) ⟨4035741, by rfl⟩ : syracuseStep 10761977 = 8071483) B8071483
theorem B4470623 : Blo 1044610 4470623 := bstep (se 1 (by rfl) ⟨3352967, by rfl⟩ : syracuseStep 4470623 = 6705935) B6705935
theorem B3979763 : Blo 1044610 3979763 := bstep (se 1 (by rfl) ⟨2984822, by rfl⟩ : syracuseStep 3979763 = 5969645) B5969645
theorem B4241929 : Blo 1044610 4241929 := bstep (se 2 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 4241929 = 3181447) B3181447
theorem B3979961 : Blo 1044610 3979961 := bstep (se 2 (by rfl) ⟨1492485, by rfl⟩ : syracuseStep 3979961 = 2984971) B2984971
theorem B3979975 : Blo 1044610 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B1490395 : Blo 1044610 1490395 := bstep (se 1 (by rfl) ⟨1117796, by rfl⟩ : syracuseStep 1490395 = 2235593) B2235593
theorem B3980947 : Blo 1044610 3980947 := bstep (se 1 (by rfl) ⟨2985710, by rfl⟩ : syracuseStep 3980947 = 5971421) B5971421
theorem B28590097 : Blo 1044610 28590097 := bstep (se 2 (by rfl) ⟨10721286, by rfl⟩ : syracuseStep 28590097 = 21442573) B21442573
theorem B4768265 : Blo 1044610 4768265 := bstep (se 2 (by rfl) ⟨1788099, by rfl⟩ : syracuseStep 4768265 = 3576199) B3576199
theorem B1983305 : Blo 1044610 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B10044481 : Blo 1044610 10044481 := bstep (se 2 (by rfl) ⟨3766680, by rfl⟩ : syracuseStep 10044481 = 7533361) B7533361
theorem B7947557 : Blo 1044610 7947557 := bstep (se 4 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 7947557 = 1490167) B1490167
theorem B1984171 : Blo 1044610 1984171 := bstep (se 1 (by rfl) ⟨1488128, by rfl⟩ : syracuseStep 1984171 = 2976257) B2976257
theorem B1984247 : Blo 1044610 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B14534437 : Blo 1044610 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B1984475 : Blo 1044610 1984475 := bstep (se 1 (by rfl) ⟨1488356, by rfl⟩ : syracuseStep 1984475 = 2976713) B2976713
theorem B7161871 : Blo 1044610 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B11913317 : Blo 1044610 11913317 := bstep (se 4 (by rfl) ⟨1116873, by rfl⟩ : syracuseStep 11913317 = 2233747) B2233747
theorem B4245821 : Blo 1044610 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B4246339 : Blo 1044610 4246339 := bstep (se 1 (by rfl) ⟨3184754, by rfl⟩ : syracuseStep 4246339 = 6369509) B6369509
theorem B1985735 : Blo 1044610 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B13421861 : Blo 1044610 13421861 := bstep (se 4 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 13421861 = 2516599) B2516599
theorem B1985887 : Blo 1044610 1985887 := bstep (se 1 (by rfl) ⟨1489415, by rfl⟩ : syracuseStep 1985887 = 2978831) B2978831
theorem B1789291 : Blo 1044610 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B4476379 : Blo 1044610 4476379 := bstep (se 1 (by rfl) ⟨3357284, by rfl⟩ : syracuseStep 4476379 = 6714569) B6714569
theorem B5951191 : Blo 1044610 5951191 := bstep (se 1 (by rfl) ⟨4463393, by rfl⟩ : syracuseStep 5951191 = 8926787) B8926787
theorem B26201987 : Blo 1044610 26201987 := bstep (se 1 (by rfl) ⟨19651490, by rfl⟩ : syracuseStep 26201987 = 39302981) B39302981
theorem B13062221 : Blo 1044610 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B130864193 : Blo 1044610 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B3527927 : Blo 1044610 3527927 := bstep (se 1 (by rfl) ⟨2645945, by rfl⟩ : syracuseStep 3527927 = 5291891) B5291891
theorem B5297399 : Blo 1044610 5297399 := bstep (se 1 (by rfl) ⟨3973049, by rfl⟩ : syracuseStep 5297399 = 7946099) B7946099
theorem B1987831 : Blo 1044610 1987831 := bstep (se 1 (by rfl) ⟨1490873, by rfl⟩ : syracuseStep 1987831 = 2981747) B2981747
theorem B8475941 : Blo 1044610 8475941 := bstep (se 4 (by rfl) ⟨794619, by rfl⟩ : syracuseStep 8475941 = 1589239) B1589239
theorem B1988059 : Blo 1044610 1988059 := bstep (se 1 (by rfl) ⟨1491044, by rfl⟩ : syracuseStep 1988059 = 2982089) B2982089
theorem B1988135 : Blo 1044610 1988135 := bstep (se 1 (by rfl) ⟨1491101, by rfl⟩ : syracuseStep 1988135 = 2982203) B2982203
theorem B3528251 : Blo 1044610 3528251 := bstep (se 1 (by rfl) ⟨2646188, by rfl⟩ : syracuseStep 3528251 = 5292377) B5292377
theorem B1988219 : Blo 1044610 1988219 := bstep (se 1 (by rfl) ⟨1491164, by rfl⟩ : syracuseStep 1988219 = 2982329) B2982329
theorem B33904277 : Blo 1044610 33904277 := bstep (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) B1589263
theorem B2512583 : Blo 1044610 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B5297885 : Blo 1044610 5297885 := bstep (se 3 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 5297885 = 1986707) B1986707
theorem B3528521 : Blo 1044610 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B1988705 : Blo 1044610 1988705 := bstep (se 2 (by rfl) ⟨745764, by rfl⟩ : syracuseStep 1988705 = 1491529) B1491529
theorem B2119927 : Blo 1044610 2119927 := bstep (se 1 (by rfl) ⟨1589945, by rfl⟩ : syracuseStep 2119927 = 3179891) B3179891
theorem B5036525 : Blo 1044610 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B5954107 : Blo 1044610 5954107 := bstep (se 1 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 5954107 = 8931161) B8931161
theorem B3529655 : Blo 1044610 3529655 := bstep (se 1 (by rfl) ⟨2647241, by rfl⟩ : syracuseStep 3529655 = 5294483) B5294483
theorem B13425857 : Blo 1044610 13425857 := bstep (se 2 (by rfl) ⟨5034696, by rfl⟩ : syracuseStep 13425857 = 10069393) B10069393
theorem B8477891 : Blo 1044610 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B6708419 : Blo 1044610 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B22666513 : Blo 1044610 22666513 := bstep (se 2 (by rfl) ⟨8499942, by rfl⟩ : syracuseStep 22666513 = 16999885) B16999885
theorem B10050905 : Blo 1044610 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B2350601 : Blo 1044610 2350601 := bstep (se 2 (by rfl) ⟨881475, by rfl⟩ : syracuseStep 2350601 = 1762951) B1762951
theorem B3530249 : Blo 1044610 3530249 := bstep (se 2 (by rfl) ⟨1323843, by rfl⟩ : syracuseStep 3530249 = 2647687) B2647687
theorem B1990163 : Blo 1044610 1990163 := bstep (se 1 (by rfl) ⟨1492622, by rfl⟩ : syracuseStep 1990163 = 2985245) B2985245
theorem B8478407 : Blo 1044610 8478407 := bstep (se 1 (by rfl) ⟨6358805, by rfl⟩ : syracuseStep 8478407 = 12717611) B12717611
theorem B2350943 : Blo 1044610 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B2645855 : Blo 1044610 2645855 := bstep (se 1 (by rfl) ⟨1984391, by rfl⟩ : syracuseStep 2645855 = 3968783) B3968783
theorem B21520247 : Blo 1044610 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B7954361 : Blo 1044610 7954361 := bstep (se 2 (by rfl) ⟨2982885, by rfl⟩ : syracuseStep 7954361 = 5965771) B5965771
theorem B4022273 : Blo 1044610 4022273 := bstep (se 2 (by rfl) ⟨1508352, by rfl⟩ : syracuseStep 4022273 = 3016705) B3016705
theorem B2351123 : Blo 1044610 2351123 := bstep (se 1 (by rfl) ⟨1763342, by rfl⟩ : syracuseStep 2351123 = 3526685) B3526685
theorem B2351465 : Blo 1044610 2351465 := bstep (se 2 (by rfl) ⟨881799, by rfl⟩ : syracuseStep 2351465 = 1763599) B1763599
theorem B3531113 : Blo 1044610 3531113 := bstep (se 2 (by rfl) ⟨1324167, by rfl⟩ : syracuseStep 3531113 = 2648335) B2648335
theorem B2646553 : Blo 1044610 2646553 := bstep (se 2 (by rfl) ⟨992457, by rfl⟩ : syracuseStep 2646553 = 1984915) B1984915
theorem B2515495 : Blo 1044610 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B2646857 : Blo 1044610 2646857 := bstep (se 2 (by rfl) ⟨992571, by rfl⟩ : syracuseStep 2646857 = 1985143) B1985143
theorem B6710161 : Blo 1044610 6710161 := bstep (se 2 (by rfl) ⟨2516310, by rfl⟩ : syracuseStep 6710161 = 5032621) B5032621
theorem B6808465 : Blo 1044610 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B2352059 : Blo 1044610 2352059 := bstep (se 1 (by rfl) ⟨1764044, by rfl⟩ : syracuseStep 2352059 = 3528089) B3528089
theorem B3531707 : Blo 1044610 3531707 := bstep (se 1 (by rfl) ⟨2648780, by rfl⟩ : syracuseStep 3531707 = 5297561) B5297561
theorem B2352185 : Blo 1044610 2352185 := bstep (se 2 (by rfl) ⟨882069, by rfl⟩ : syracuseStep 2352185 = 1764139) B1764139
theorem B2974799 : Blo 1044610 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B2352527 : Blo 1044610 2352527 := bstep (se 1 (by rfl) ⟨1764395, by rfl⟩ : syracuseStep 2352527 = 3528791) B3528791
theorem B2123227 : Blo 1044610 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B1762823 : Blo 1044610 1762823 := bstep (se 1 (by rfl) ⟨1322117, by rfl⟩ : syracuseStep 1762823 = 2644235) B2644235
theorem B2352851 : Blo 1044610 2352851 := bstep (se 1 (by rfl) ⟨1764638, by rfl⟩ : syracuseStep 2352851 = 3529277) B3529277
theorem B6711083 : Blo 1044610 6711083 := bstep (se 1 (by rfl) ⟨5033312, by rfl⟩ : syracuseStep 6711083 = 10066625) B10066625
theorem B27223897 : Blo 1044610 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B1763167 : Blo 1044610 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B1763255 : Blo 1044610 1763255 := bstep (se 1 (by rfl) ⟨1322441, by rfl⟩ : syracuseStep 1763255 = 2644883) B2644883
theorem B2647991 : Blo 1044610 2647991 := bstep (se 1 (by rfl) ⟨1985993, by rfl⟩ : syracuseStep 2647991 = 3971987) B3971987
theorem B17885285 : Blo 1044610 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B2975915 : Blo 1044610 2975915 := bstep (se 1 (by rfl) ⟨2231936, by rfl⟩ : syracuseStep 2975915 = 4463873) B4463873
theorem B8939909 : Blo 1044610 8939909 := bstep (se 4 (by rfl) ⟨838116, by rfl⟩ : syracuseStep 8939909 = 1676233) B1676233
theorem B1567151 : Blo 1044610 1567151 := bstep (se 1 (by rfl) ⟨1175363, by rfl⟩ : syracuseStep 1567151 = 2350727) B2350727
theorem B1272283 : Blo 1044610 1272283 := bstep (se 1 (by rfl) ⟨954212, by rfl⟩ : syracuseStep 1272283 = 1908425) B1908425
theorem B1567241 : Blo 1044610 1567241 := bstep (se 2 (by rfl) ⟨587715, by rfl⟩ : syracuseStep 1567241 = 1175431) B1175431
theorem B1763849 : Blo 1044610 1763849 := bstep (se 2 (by rfl) ⟨661443, by rfl⟩ : syracuseStep 1763849 = 1322887) B1322887
theorem B10742305 : Blo 1044610 10742305 := bstep (se 2 (by rfl) ⟨4028364, by rfl⟩ : syracuseStep 10742305 = 8056729) B8056729
theorem B1567271 : Blo 1044610 1567271 := bstep (se 1 (by rfl) ⟨1175453, by rfl⟩ : syracuseStep 1567271 = 2350907) B2350907
theorem B1567355 : Blo 1044610 1567355 := bstep (se 1 (by rfl) ⟨1175516, by rfl⟩ : syracuseStep 1567355 = 2351033) B2351033
theorem B2353787 : Blo 1044610 2353787 := bstep (se 1 (by rfl) ⟨1765340, by rfl⟩ : syracuseStep 2353787 = 3530681) B3530681
theorem B3533435 : Blo 1044610 3533435 := bstep (se 1 (by rfl) ⟨2650076, by rfl⟩ : syracuseStep 3533435 = 5300153) B5300153
theorem B1764011 : Blo 1044610 1764011 := bstep (se 1 (by rfl) ⟨1323008, by rfl⟩ : syracuseStep 1764011 = 2646017) B2646017
theorem B10316489 : Blo 1044610 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B8055497 : Blo 1044610 8055497 := bstep (se 2 (by rfl) ⟨3020811, by rfl⟩ : syracuseStep 8055497 = 6041623) B6041623
theorem B1567481 : Blo 1044610 1567481 := bstep (se 2 (by rfl) ⟨587805, by rfl⟩ : syracuseStep 1567481 = 1175611) B1175611
theorem B2353913 : Blo 1044610 2353913 := bstep (se 2 (by rfl) ⟨882717, by rfl⟩ : syracuseStep 2353913 = 1765435) B1765435
theorem B7957277 : Blo 1044610 7957277 := bstep (se 3 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 7957277 = 2983979) B2983979
theorem B3533597 : Blo 1044610 3533597 := bstep (se 3 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 3533597 = 1325099) B1325099
theorem B5303069 : Blo 1044610 5303069 := bstep (se 3 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 5303069 = 1988651) B1988651
theorem B11299661 : Blo 1044610 11299661 := bstep (se 3 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 11299661 = 4237373) B4237373
theorem B1567583 : Blo 1044610 1567583 := bstep (se 1 (by rfl) ⟨1175687, by rfl⟩ : syracuseStep 1567583 = 2351375) B2351375
theorem B1567595 : Blo 1044610 1567595 := bstep (se 1 (by rfl) ⟨1175696, by rfl⟩ : syracuseStep 1567595 = 2351393) B2351393
theorem B2354183 : Blo 1044610 2354183 := bstep (se 1 (by rfl) ⟨1765637, by rfl⟩ : syracuseStep 2354183 = 3531275) B3531275
theorem B2649095 : Blo 1044610 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B1764409 : Blo 1044610 1764409 := bstep (se 2 (by rfl) ⟨661653, by rfl⟩ : syracuseStep 1764409 = 1323307) B1323307
theorem B2649145 : Blo 1044610 2649145 := bstep (se 2 (by rfl) ⟨993429, by rfl⟩ : syracuseStep 2649145 = 1986859) B1986859
theorem B1567823 : Blo 1044610 1567823 := bstep (se 1 (by rfl) ⟨1175867, by rfl⟩ : syracuseStep 1567823 = 2351735) B2351735
theorem B2354255 : Blo 1044610 2354255 := bstep (se 1 (by rfl) ⟨1765691, by rfl⟩ : syracuseStep 2354255 = 3531383) B3531383
theorem B1567943 : Blo 1044610 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B1764551 : Blo 1044610 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B14511395 : Blo 1044610 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B1568105 : Blo 1044610 1568105 := bstep (se 2 (by rfl) ⟨588039, by rfl⟩ : syracuseStep 1568105 = 1176079) B1176079
theorem B1764713 : Blo 1044610 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B2649449 : Blo 1044610 2649449 := bstep (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) B1987087
theorem B1568183 : Blo 1044610 1568183 := bstep (se 1 (by rfl) ⟨1176137, by rfl⟩ : syracuseStep 1568183 = 2352275) B2352275
theorem B1568219 : Blo 1044610 1568219 := bstep (se 1 (by rfl) ⟨1176164, by rfl⟩ : syracuseStep 1568219 = 2352329) B2352329
theorem B2354651 : Blo 1044610 2354651 := bstep (se 1 (by rfl) ⟨1765988, by rfl⟩ : syracuseStep 2354651 = 3531977) B3531977
theorem B3534299 : Blo 1044610 3534299 := bstep (se 1 (by rfl) ⟨2650724, by rfl⟩ : syracuseStep 3534299 = 5301449) B5301449
theorem B2387465 : Blo 1044610 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B1765111 : Blo 1044610 1765111 := bstep (se 1 (by rfl) ⟨1323833, by rfl⟩ : syracuseStep 1765111 = 2647667) B2647667
theorem B1568687 : Blo 1044610 1568687 := bstep (se 1 (by rfl) ⟨1176515, by rfl⟩ : syracuseStep 1568687 = 2353031) B2353031
theorem B2355119 : Blo 1044610 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B1765307 : Blo 1044610 1765307 := bstep (se 1 (by rfl) ⟨1323980, by rfl⟩ : syracuseStep 1765307 = 2647961) B2647961
theorem B1568777 : Blo 1044610 1568777 := bstep (se 2 (by rfl) ⟨588291, by rfl⟩ : syracuseStep 1568777 = 1176583) B1176583
theorem B1568807 : Blo 1044610 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B1765415 : Blo 1044610 1765415 := bstep (se 1 (by rfl) ⟨1324061, by rfl⟩ : syracuseStep 1765415 = 2648123) B2648123
theorem B1568891 : Blo 1044610 1568891 := bstep (se 1 (by rfl) ⟨1176668, by rfl⟩ : syracuseStep 1568891 = 2353337) B2353337
theorem B3535001 : Blo 1044610 3535001 := bstep (se 2 (by rfl) ⟨1325625, by rfl⟩ : syracuseStep 3535001 = 2651251) B2651251
theorem B2355371 : Blo 1044610 2355371 := bstep (se 1 (by rfl) ⟨1766528, by rfl⟩ : syracuseStep 2355371 = 3533057) B3533057
theorem B1044655 : Blo 1044610 1044655 := bstep (se 1 (by rfl) ⟨783491, by rfl⟩ : syracuseStep 1044655 = 1566983) B1566983
theorem B1044679 : Blo 1044610 1044679 := bstep (se 1 (by rfl) ⟨783509, by rfl⟩ : syracuseStep 1044679 = 1567019) B1567019
theorem B1044699 : Blo 1044610 1044699 := bstep (se 1 (by rfl) ⟨783524, by rfl⟩ : syracuseStep 1044699 = 1567049) B1567049
theorem B1569017 : Blo 1044610 1569017 := bstep (se 2 (by rfl) ⟨588381, by rfl⟩ : syracuseStep 1569017 = 1176763) B1176763
theorem B1044775 : Blo 1044610 1044775 := bstep (se 1 (by rfl) ⟨783581, by rfl⟩ : syracuseStep 1044775 = 1567163) B1567163
theorem B1765705 : Blo 1044610 1765705 := bstep (se 2 (by rfl) ⟨662139, by rfl⟩ : syracuseStep 1765705 = 1324279) B1324279
theorem B1044815 : Blo 1044610 1044815 := bstep (se 1 (by rfl) ⟨783611, by rfl⟩ : syracuseStep 1044815 = 1567223) B1567223
theorem B1044831 : Blo 1044610 1044831 := bstep (se 1 (by rfl) ⟨783623, by rfl⟩ : syracuseStep 1044831 = 1567247) B1567247
theorem B1569119 : Blo 1044610 1569119 := bstep (se 1 (by rfl) ⟨1176839, by rfl⟩ : syracuseStep 1569119 = 2353679) B2353679
theorem B1569131 : Blo 1044610 1569131 := bstep (se 1 (by rfl) ⟨1176848, by rfl⟩ : syracuseStep 1569131 = 2353697) B2353697
theorem B1765739 : Blo 1044610 1765739 := bstep (se 1 (by rfl) ⟨1324304, by rfl⟩ : syracuseStep 1765739 = 2648609) B2648609
theorem B1044859 : Blo 1044610 1044859 := bstep (se 1 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 1044859 = 1567289) B1567289
theorem B1044911 : Blo 1044610 1044911 := bstep (se 1 (by rfl) ⟨783683, by rfl⟩ : syracuseStep 1044911 = 1567367) B1567367
theorem B1044935 : Blo 1044610 1044935 := bstep (se 1 (by rfl) ⟨783701, by rfl⟩ : syracuseStep 1044935 = 1567403) B1567403
theorem B1044955 : Blo 1044610 1044955 := bstep (se 1 (by rfl) ⟨783716, by rfl⟩ : syracuseStep 1044955 = 1567433) B1567433
theorem B15692291 : Blo 1044610 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B1045031 : Blo 1044610 1045031 := bstep (se 1 (by rfl) ⟨783773, by rfl⟩ : syracuseStep 1045031 = 1567547) B1567547
theorem B1045071 : Blo 1044610 1045071 := bstep (se 1 (by rfl) ⟨783803, by rfl⟩ : syracuseStep 1045071 = 1567607) B1567607
theorem B1569359 : Blo 1044610 1569359 := bstep (se 1 (by rfl) ⟨1177019, by rfl⟩ : syracuseStep 1569359 = 2354039) B2354039
theorem B1045087 : Blo 1044610 1045087 := bstep (se 1 (by rfl) ⟨783815, by rfl⟩ : syracuseStep 1045087 = 1567631) B1567631
theorem B1045115 : Blo 1044610 1045115 := bstep (se 1 (by rfl) ⟨783836, by rfl⟩ : syracuseStep 1045115 = 1567673) B1567673
theorem B1176187 : Blo 1044610 1176187 := bstep (se 1 (by rfl) ⟨882140, by rfl⟩ : syracuseStep 1176187 = 1764281) B1764281
theorem B1045167 : Blo 1044610 1045167 := bstep (se 1 (by rfl) ⟨783875, by rfl⟩ : syracuseStep 1045167 = 1567751) B1567751
theorem B1045191 : Blo 1044610 1045191 := bstep (se 1 (by rfl) ⟨783893, by rfl⟩ : syracuseStep 1045191 = 1567787) B1567787
theorem B1569479 : Blo 1044610 1569479 := bstep (se 1 (by rfl) ⟨1177109, by rfl⟩ : syracuseStep 1569479 = 2354219) B2354219
theorem B2355911 : Blo 1044610 2355911 := bstep (se 1 (by rfl) ⟨1766933, by rfl⟩ : syracuseStep 2355911 = 3533867) B3533867
theorem B1045211 : Blo 1044610 1045211 := bstep (se 1 (by rfl) ⟨783908, by rfl⟩ : syracuseStep 1045211 = 1567817) B1567817
theorem B1766137 : Blo 1044610 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B1045287 : Blo 1044610 1045287 := bstep (se 1 (by rfl) ⟨783965, by rfl⟩ : syracuseStep 1045287 = 1567931) B1567931
theorem B1045327 : Blo 1044610 1045327 := bstep (se 1 (by rfl) ⟨783995, by rfl⟩ : syracuseStep 1045327 = 1567991) B1567991
theorem B1045343 : Blo 1044610 1045343 := bstep (se 1 (by rfl) ⟨784007, by rfl⟩ : syracuseStep 1045343 = 1568015) B1568015
theorem B1569641 : Blo 1044610 1569641 := bstep (se 2 (by rfl) ⟨588615, by rfl⟩ : syracuseStep 1569641 = 1177231) B1177231
theorem B16118635 : Blo 1044610 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B1045371 : Blo 1044610 1045371 := bstep (se 1 (by rfl) ⟨784028, by rfl⟩ : syracuseStep 1045371 = 1568057) B1568057
theorem B57308057 : Blo 1044610 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B3830689 : Blo 1044610 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B1045423 : Blo 1044610 1045423 := bstep (se 1 (by rfl) ⟨784067, by rfl⟩ : syracuseStep 1045423 = 1568135) B1568135
theorem B1569719 : Blo 1044610 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B1045447 : Blo 1044610 1045447 := bstep (se 1 (by rfl) ⟨784085, by rfl⟩ : syracuseStep 1045447 = 1568171) B1568171
theorem B1045467 : Blo 1044610 1045467 := bstep (se 1 (by rfl) ⟨784100, by rfl⟩ : syracuseStep 1045467 = 1568201) B1568201
theorem B1569755 : Blo 1044610 1569755 := bstep (se 1 (by rfl) ⟨1177316, by rfl⟩ : syracuseStep 1569755 = 2354633) B2354633
theorem B1766407 : Blo 1044610 1766407 := bstep (se 1 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 1766407 = 2649611) B2649611
theorem B1045543 : Blo 1044610 1045543 := bstep (se 1 (by rfl) ⟨784157, by rfl⟩ : syracuseStep 1045543 = 1568315) B1568315
theorem B1045583 : Blo 1044610 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B1176655 : Blo 1044610 1176655 := bstep (se 1 (by rfl) ⟨882491, by rfl⟩ : syracuseStep 1176655 = 1764983) B1764983
theorem B1045599 : Blo 1044610 1045599 := bstep (se 1 (by rfl) ⟨784199, by rfl⟩ : syracuseStep 1045599 = 1568399) B1568399
theorem B1045627 : Blo 1044610 1045627 := bstep (se 1 (by rfl) ⟨784220, by rfl⟩ : syracuseStep 1045627 = 1568441) B1568441
theorem B1045679 : Blo 1044610 1045679 := bstep (se 1 (by rfl) ⟨784259, by rfl⟩ : syracuseStep 1045679 = 1568519) B1568519
theorem B1045703 : Blo 1044610 1045703 := bstep (se 1 (by rfl) ⟨784277, by rfl⟩ : syracuseStep 1045703 = 1568555) B1568555
theorem B1045723 : Blo 1044610 1045723 := bstep (se 1 (by rfl) ⟨784292, by rfl⟩ : syracuseStep 1045723 = 1568585) B1568585
theorem B1045799 : Blo 1044610 1045799 := bstep (se 1 (by rfl) ⟨784349, by rfl⟩ : syracuseStep 1045799 = 1568699) B1568699
theorem B3536189 : Blo 1044610 3536189 := bstep (se 3 (by rfl) ⟨663035, by rfl⟩ : syracuseStep 3536189 = 1326071) B1326071
theorem B1045839 : Blo 1044610 1045839 := bstep (se 1 (by rfl) ⟨784379, by rfl⟩ : syracuseStep 1045839 = 1568759) B1568759
theorem B1045855 : Blo 1044610 1045855 := bstep (se 1 (by rfl) ⟨784391, by rfl⟩ : syracuseStep 1045855 = 1568783) B1568783
theorem B1045883 : Blo 1044610 1045883 := bstep (se 1 (by rfl) ⟨784412, by rfl⟩ : syracuseStep 1045883 = 1568825) B1568825
theorem B8058275 : Blo 1044610 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B1045935 : Blo 1044610 1045935 := bstep (se 1 (by rfl) ⟨784451, by rfl⟩ : syracuseStep 1045935 = 1568903) B1568903
theorem B1570223 : Blo 1044610 1570223 := bstep (se 1 (by rfl) ⟨1177667, by rfl⟩ : syracuseStep 1570223 = 2355335) B2355335
theorem B1766839 : Blo 1044610 1766839 := bstep (se 1 (by rfl) ⟨1325129, by rfl⟩ : syracuseStep 1766839 = 2650259) B2650259
theorem B1045959 : Blo 1044610 1045959 := bstep (se 1 (by rfl) ⟨784469, by rfl⟩ : syracuseStep 1045959 = 1568939) B1568939
theorem B1045979 : Blo 1044610 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B1177051 : Blo 1044610 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B11924981 : Blo 1044610 11924981 := bstep (se 5 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 11924981 = 1117967) B1117967
theorem B1570313 : Blo 1044610 1570313 := bstep (se 2 (by rfl) ⟨588867, by rfl⟩ : syracuseStep 1570313 = 1177735) B1177735
theorem B1046055 : Blo 1044610 1046055 := bstep (se 1 (by rfl) ⟨784541, by rfl⟩ : syracuseStep 1046055 = 1569083) B1569083
theorem B1570343 : Blo 1044610 1570343 := bstep (se 1 (by rfl) ⟨1177757, by rfl⟩ : syracuseStep 1570343 = 2355515) B2355515
theorem B2356775 : Blo 1044610 2356775 := bstep (se 1 (by rfl) ⟨1767581, by rfl⟩ : syracuseStep 2356775 = 3535163) B3535163
theorem B2651687 : Blo 1044610 2651687 := bstep (se 1 (by rfl) ⟨1988765, by rfl⟩ : syracuseStep 2651687 = 3977531) B3977531
theorem B13399613 : Blo 1044610 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B1046095 : Blo 1044610 1046095 := bstep (se 1 (by rfl) ⟨784571, by rfl⟩ : syracuseStep 1046095 = 1569143) B1569143
theorem B1046111 : Blo 1044610 1046111 := bstep (se 1 (by rfl) ⟨784583, by rfl⟩ : syracuseStep 1046111 = 1569167) B1569167
theorem B1046139 : Blo 1044610 1046139 := bstep (se 1 (by rfl) ⟨784604, by rfl⟩ : syracuseStep 1046139 = 1569209) B1569209
theorem B1570427 : Blo 1044610 1570427 := bstep (se 1 (by rfl) ⟨1177820, by rfl⟩ : syracuseStep 1570427 = 2355641) B2355641
theorem B1767035 : Blo 1044610 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B1046191 : Blo 1044610 1046191 := bstep (se 1 (by rfl) ⟨784643, by rfl⟩ : syracuseStep 1046191 = 1569287) B1569287
theorem B1046215 : Blo 1044610 1046215 := bstep (se 1 (by rfl) ⟨784661, by rfl⟩ : syracuseStep 1046215 = 1569323) B1569323
theorem B1046235 : Blo 1044610 1046235 := bstep (se 1 (by rfl) ⟨784676, by rfl⟩ : syracuseStep 1046235 = 1569353) B1569353
theorem B1570553 : Blo 1044610 1570553 := bstep (se 2 (by rfl) ⟨588957, by rfl⟩ : syracuseStep 1570553 = 1177915) B1177915
theorem B1046311 : Blo 1044610 1046311 := bstep (se 1 (by rfl) ⟨784733, by rfl⟩ : syracuseStep 1046311 = 1569467) B1569467
theorem B1046351 : Blo 1044610 1046351 := bstep (se 1 (by rfl) ⟨784763, by rfl⟩ : syracuseStep 1046351 = 1569527) B1569527
theorem B1046367 : Blo 1044610 1046367 := bstep (se 1 (by rfl) ⟨784775, by rfl⟩ : syracuseStep 1046367 = 1569551) B1569551
theorem B1570655 : Blo 1044610 1570655 := bstep (se 1 (by rfl) ⟨1177991, by rfl⟩ : syracuseStep 1570655 = 2355983) B2355983
theorem B1570667 : Blo 1044610 1570667 := bstep (se 1 (by rfl) ⟨1178000, by rfl⟩ : syracuseStep 1570667 = 2356001) B2356001
theorem B2357099 : Blo 1044610 2357099 := bstep (se 1 (by rfl) ⟨1767824, by rfl⟩ : syracuseStep 2357099 = 3535649) B3535649
theorem B2652011 : Blo 1044610 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B3766135 : Blo 1044610 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B1046395 : Blo 1044610 1046395 := bstep (se 1 (by rfl) ⟨784796, by rfl⟩ : syracuseStep 1046395 = 1569593) B1569593
theorem B2357153 : Blo 1044610 2357153 := bstep (se 2 (by rfl) ⟨883932, by rfl⟩ : syracuseStep 2357153 = 1767865) B1767865
theorem B1046447 : Blo 1044610 1046447 := bstep (se 1 (by rfl) ⟨784835, by rfl⟩ : syracuseStep 1046447 = 1569671) B1569671
theorem B1177519 : Blo 1044610 1177519 := bstep (se 1 (by rfl) ⟨883139, by rfl⟩ : syracuseStep 1177519 = 1766279) B1766279
theorem B1046471 : Blo 1044610 1046471 := bstep (se 1 (by rfl) ⟨784853, by rfl⟩ : syracuseStep 1046471 = 1569707) B1569707
theorem B1046491 : Blo 1044610 1046491 := bstep (se 1 (by rfl) ⟨784868, by rfl⟩ : syracuseStep 1046491 = 1569737) B1569737
theorem B1767433 : Blo 1044610 1767433 := bstep (se 2 (by rfl) ⟨662787, by rfl⟩ : syracuseStep 1767433 = 1325575) B1325575
theorem B1046567 : Blo 1044610 1046567 := bstep (se 1 (by rfl) ⟨784925, by rfl⟩ : syracuseStep 1046567 = 1569851) B1569851
theorem B1046607 : Blo 1044610 1046607 := bstep (se 1 (by rfl) ⟨784955, by rfl⟩ : syracuseStep 1046607 = 1569911) B1569911
theorem B1570895 : Blo 1044610 1570895 := bstep (se 1 (by rfl) ⟨1178171, by rfl⟩ : syracuseStep 1570895 = 2356343) B2356343
theorem B1046623 : Blo 1044610 1046623 := bstep (se 1 (by rfl) ⟨784967, by rfl⟩ : syracuseStep 1046623 = 1569935) B1569935
theorem B1046651 : Blo 1044610 1046651 := bstep (se 1 (by rfl) ⟨784988, by rfl⟩ : syracuseStep 1046651 = 1569977) B1569977
theorem B3537053 : Blo 1044610 3537053 := bstep (se 3 (by rfl) ⟨663197, by rfl⟩ : syracuseStep 3537053 = 1326395) B1326395
theorem B1767595 : Blo 1044610 1767595 := bstep (se 1 (by rfl) ⟨1325696, by rfl⟩ : syracuseStep 1767595 = 2651393) B2651393
theorem B1046703 : Blo 1044610 1046703 := bstep (se 1 (by rfl) ⟨785027, by rfl⟩ : syracuseStep 1046703 = 1570055) B1570055
theorem B1046727 : Blo 1044610 1046727 := bstep (se 1 (by rfl) ⟨785045, by rfl⟩ : syracuseStep 1046727 = 1570091) B1570091
theorem B1571015 : Blo 1044610 1571015 := bstep (se 1 (by rfl) ⟨1178261, by rfl⟩ : syracuseStep 1571015 = 2356523) B2356523
theorem B1046747 : Blo 1044610 1046747 := bstep (se 1 (by rfl) ⟨785060, by rfl⟩ : syracuseStep 1046747 = 1570121) B1570121
theorem B2357495 : Blo 1044610 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B1046823 : Blo 1044610 1046823 := bstep (se 1 (by rfl) ⟨785117, by rfl⟩ : syracuseStep 1046823 = 1570235) B1570235
theorem B1046863 : Blo 1044610 1046863 := bstep (se 1 (by rfl) ⟨785147, by rfl⟩ : syracuseStep 1046863 = 1570295) B1570295
theorem B1046879 : Blo 1044610 1046879 := bstep (se 1 (by rfl) ⟨785159, by rfl⟩ : syracuseStep 1046879 = 1570319) B1570319
theorem B1177951 : Blo 1044610 1177951 := bstep (se 1 (by rfl) ⟨883463, by rfl⟩ : syracuseStep 1177951 = 1766927) B1766927
theorem B1571177 : Blo 1044610 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B1046907 : Blo 1044610 1046907 := bstep (se 1 (by rfl) ⟨785180, by rfl⟩ : syracuseStep 1046907 = 1570361) B1570361
theorem B1046959 : Blo 1044610 1046959 := bstep (se 1 (by rfl) ⟨785219, by rfl⟩ : syracuseStep 1046959 = 1570439) B1570439
theorem B1571255 : Blo 1044610 1571255 := bstep (se 1 (by rfl) ⟨1178441, by rfl⟩ : syracuseStep 1571255 = 2356883) B2356883
theorem B1046983 : Blo 1044610 1046983 := bstep (se 1 (by rfl) ⟨785237, by rfl⟩ : syracuseStep 1046983 = 1570475) B1570475
theorem B1047003 : Blo 1044610 1047003 := bstep (se 1 (by rfl) ⟨785252, by rfl⟩ : syracuseStep 1047003 = 1570505) B1570505
theorem B1571291 : Blo 1044610 1571291 := bstep (se 1 (by rfl) ⟨1178468, by rfl⟩ : syracuseStep 1571291 = 2356937) B2356937
theorem B1767899 : Blo 1044610 1767899 := bstep (se 1 (by rfl) ⟨1325924, by rfl⟩ : syracuseStep 1767899 = 2651849) B2651849
theorem B2652659 : Blo 1044610 2652659 := bstep (se 1 (by rfl) ⟨1989494, by rfl⟩ : syracuseStep 2652659 = 3978989) B3978989
theorem B42990101 : Blo 1044610 42990101 := bstep (se 6 (by rfl) ⟨1007580, by rfl⟩ : syracuseStep 42990101 = 2015161) B2015161
theorem B1047079 : Blo 1044610 1047079 := bstep (se 1 (by rfl) ⟨785309, by rfl⟩ : syracuseStep 1047079 = 1570619) B1570619
theorem B1047119 : Blo 1044610 1047119 := bstep (se 1 (by rfl) ⟨785339, by rfl⟩ : syracuseStep 1047119 = 1570679) B1570679
theorem B1047135 : Blo 1044610 1047135 := bstep (se 1 (by rfl) ⟨785351, by rfl⟩ : syracuseStep 1047135 = 1570703) B1570703
theorem B1047163 : Blo 1044610 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B1047215 : Blo 1044610 1047215 := bstep (se 1 (by rfl) ⟨785411, by rfl⟩ : syracuseStep 1047215 = 1570823) B1570823
theorem B3537593 : Blo 1044610 3537593 := bstep (se 2 (by rfl) ⟨1326597, by rfl⟩ : syracuseStep 3537593 = 2653195) B2653195
theorem B1047239 : Blo 1044610 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B1178311 : Blo 1044610 1178311 := bstep (se 1 (by rfl) ⟨883733, by rfl⟩ : syracuseStep 1178311 = 1767467) B1767467
theorem B1768135 : Blo 1044610 1768135 := bstep (se 1 (by rfl) ⟨1326101, by rfl⟩ : syracuseStep 1768135 = 2652203) B2652203
theorem B2652871 : Blo 1044610 2652871 := bstep (se 1 (by rfl) ⟨1989653, by rfl⟩ : syracuseStep 2652871 = 3979307) B3979307
theorem B1047259 : Blo 1044610 1047259 := bstep (se 1 (by rfl) ⟨785444, by rfl⟩ : syracuseStep 1047259 = 1570889) B1570889
theorem B1047335 : Blo 1044610 1047335 := bstep (se 1 (by rfl) ⟨785501, by rfl⟩ : syracuseStep 1047335 = 1571003) B1571003
theorem B2358089 : Blo 1044610 2358089 := bstep (se 2 (by rfl) ⟨884283, by rfl⟩ : syracuseStep 2358089 = 1768567) B1768567
theorem B1047375 : Blo 1044610 1047375 := bstep (se 1 (by rfl) ⟨785531, by rfl⟩ : syracuseStep 1047375 = 1571063) B1571063
theorem B1047391 : Blo 1044610 1047391 := bstep (se 1 (by rfl) ⟨785543, by rfl⟩ : syracuseStep 1047391 = 1571087) B1571087
theorem B1768297 : Blo 1044610 1768297 := bstep (se 2 (by rfl) ⟨663111, by rfl⟩ : syracuseStep 1768297 = 1326223) B1326223
theorem B1047419 : Blo 1044610 1047419 := bstep (se 1 (by rfl) ⟨785564, by rfl⟩ : syracuseStep 1047419 = 1571129) B1571129
theorem B1571759 : Blo 1044610 1571759 := bstep (se 1 (by rfl) ⟨1178819, by rfl⟩ : syracuseStep 1571759 = 2357639) B2357639
theorem B1047471 : Blo 1044610 1047471 := bstep (se 1 (by rfl) ⟨785603, by rfl⟩ : syracuseStep 1047471 = 1571207) B1571207
theorem B1047495 : Blo 1044610 1047495 := bstep (se 1 (by rfl) ⟨785621, by rfl⟩ : syracuseStep 1047495 = 1571243) B1571243
theorem B1047515 : Blo 1044610 1047515 := bstep (se 1 (by rfl) ⟨785636, by rfl⟩ : syracuseStep 1047515 = 1571273) B1571273
theorem B2980871 : Blo 1044610 2980871 := bstep (se 1 (by rfl) ⟨2235653, by rfl⟩ : syracuseStep 2980871 = 4471307) B4471307
theorem B1571849 : Blo 1044610 1571849 := bstep (se 2 (by rfl) ⟨589443, by rfl⟩ : syracuseStep 1571849 = 1178887) B1178887
theorem B1047591 : Blo 1044610 1047591 := bstep (se 1 (by rfl) ⟨785693, by rfl⟩ : syracuseStep 1047591 = 1571387) B1571387
theorem B1571879 : Blo 1044610 1571879 := bstep (se 1 (by rfl) ⟨1178909, by rfl⟩ : syracuseStep 1571879 = 2357819) B2357819
theorem B5307443 : Blo 1044610 5307443 := bstep (se 1 (by rfl) ⟨3980582, by rfl⟩ : syracuseStep 5307443 = 7961165) B7961165
theorem B7961651 : Blo 1044610 7961651 := bstep (se 1 (by rfl) ⟨5971238, by rfl⟩ : syracuseStep 7961651 = 11942477) B11942477
theorem B1047631 : Blo 1044610 1047631 := bstep (se 1 (by rfl) ⟨785723, by rfl⟩ : syracuseStep 1047631 = 1571447) B1571447
theorem B1047647 : Blo 1044610 1047647 := bstep (se 1 (by rfl) ⟨785735, by rfl⟩ : syracuseStep 1047647 = 1571471) B1571471
theorem B1047675 : Blo 1044610 1047675 := bstep (se 1 (by rfl) ⟨785756, by rfl⟩ : syracuseStep 1047675 = 1571513) B1571513
theorem B1571963 : Blo 1044610 1571963 := bstep (se 1 (by rfl) ⟨1178972, by rfl⟩ : syracuseStep 1571963 = 2357945) B2357945
theorem B1047727 : Blo 1044610 1047727 := bstep (se 1 (by rfl) ⟨785795, by rfl⟩ : syracuseStep 1047727 = 1571591) B1571591
theorem B10747073 : Blo 1044610 10747073 := bstep (se 2 (by rfl) ⟨4030152, by rfl⟩ : syracuseStep 10747073 = 8060305) B8060305
theorem B1047751 : Blo 1044610 1047751 := bstep (se 1 (by rfl) ⟨785813, by rfl⟩ : syracuseStep 1047751 = 1571627) B1571627
theorem B1047771 : Blo 1044610 1047771 := bstep (se 1 (by rfl) ⟨785828, by rfl⟩ : syracuseStep 1047771 = 1571657) B1571657
theorem B1572089 : Blo 1044610 1572089 := bstep (se 2 (by rfl) ⟨589533, by rfl⟩ : syracuseStep 1572089 = 1179067) B1179067
theorem B3538187 : Blo 1044610 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B1047847 : Blo 1044610 1047847 := bstep (se 1 (by rfl) ⟨785885, by rfl⟩ : syracuseStep 1047847 = 1571771) B1571771
theorem B1047887 : Blo 1044610 1047887 := bstep (se 1 (by rfl) ⟨785915, by rfl⟩ : syracuseStep 1047887 = 1571831) B1571831
theorem B1047903 : Blo 1044610 1047903 := bstep (se 1 (by rfl) ⟨785927, by rfl⟩ : syracuseStep 1047903 = 1571855) B1571855
theorem B1572191 : Blo 1044610 1572191 := bstep (se 1 (by rfl) ⟨1179143, by rfl⟩ : syracuseStep 1572191 = 2358287) B2358287
theorem B1572203 : Blo 1044610 1572203 := bstep (se 1 (by rfl) ⟨1179152, by rfl⟩ : syracuseStep 1572203 = 2358305) B2358305
theorem B1047931 : Blo 1044610 1047931 := bstep (se 1 (by rfl) ⟨785948, by rfl⟩ : syracuseStep 1047931 = 1571897) B1571897
theorem B1047983 : Blo 1044610 1047983 := bstep (se 1 (by rfl) ⟨785987, by rfl⟩ : syracuseStep 1047983 = 1571975) B1571975
theorem B1768891 : Blo 1044610 1768891 := bstep (se 1 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 1768891 = 2653337) B2653337
theorem B1048007 : Blo 1044610 1048007 := bstep (se 1 (by rfl) ⟨786005, by rfl⟩ : syracuseStep 1048007 = 1572011) B1572011
theorem B6127049 : Blo 1044610 6127049 := bstep (se 2 (by rfl) ⟨2297643, by rfl⟩ : syracuseStep 6127049 = 4595287) B4595287
theorem B1048027 : Blo 1044610 1048027 := bstep (se 1 (by rfl) ⟨786020, by rfl⟩ : syracuseStep 1048027 = 1572041) B1572041
theorem B3538457 : Blo 1044610 3538457 := bstep (se 2 (by rfl) ⟨1326921, by rfl⟩ : syracuseStep 3538457 = 2653843) B2653843
theorem B1048103 : Blo 1044610 1048103 := bstep (se 1 (by rfl) ⟨786077, by rfl⟩ : syracuseStep 1048103 = 1572155) B1572155
theorem B1179175 : Blo 1044610 1179175 := bstep (se 1 (by rfl) ⟨884381, by rfl⟩ : syracuseStep 1179175 = 1768763) B1768763
theorem B1768999 : Blo 1044610 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B1048143 : Blo 1044610 1048143 := bstep (se 1 (by rfl) ⟨786107, by rfl⟩ : syracuseStep 1048143 = 1572215) B1572215
theorem B1572431 : Blo 1044610 1572431 := bstep (se 1 (by rfl) ⟨1179323, by rfl⟩ : syracuseStep 1572431 = 2358647) B2358647
theorem B1048159 : Blo 1044610 1048159 := bstep (se 1 (by rfl) ⟨786119, by rfl⟩ : syracuseStep 1048159 = 1572239) B1572239
theorem B2358881 : Blo 1044610 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B2653793 : Blo 1044610 2653793 := bstep (se 2 (by rfl) ⟨995172, by rfl⟩ : syracuseStep 2653793 = 1990345) B1990345
theorem B1048187 : Blo 1044610 1048187 := bstep (se 1 (by rfl) ⟨786140, by rfl⟩ : syracuseStep 1048187 = 1572281) B1572281
theorem B1048239 : Blo 1044610 1048239 := bstep (se 1 (by rfl) ⟨786179, by rfl⟩ : syracuseStep 1048239 = 1572359) B1572359
theorem B1048263 : Blo 1044610 1048263 := bstep (se 1 (by rfl) ⟨786197, by rfl⟩ : syracuseStep 1048263 = 1572395) B1572395
theorem B1572551 : Blo 1044610 1572551 := bstep (se 1 (by rfl) ⟨1179413, by rfl⟩ : syracuseStep 1572551 = 2358827) B2358827
theorem B1048283 : Blo 1044610 1048283 := bstep (se 1 (by rfl) ⟨786212, by rfl⟩ : syracuseStep 1048283 = 1572425) B1572425
theorem B1048359 : Blo 1044610 1048359 := bstep (se 1 (by rfl) ⟨786269, by rfl⟩ : syracuseStep 1048359 = 1572539) B1572539
theorem B1048399 : Blo 1044610 1048399 := bstep (se 1 (by rfl) ⟨786299, by rfl⟩ : syracuseStep 1048399 = 1572599) B1572599
theorem B1048415 : Blo 1044610 1048415 := bstep (se 1 (by rfl) ⟨786311, by rfl⟩ : syracuseStep 1048415 = 1572623) B1572623
theorem B1572713 : Blo 1044610 1572713 := bstep (se 2 (by rfl) ⟨589767, by rfl⟩ : syracuseStep 1572713 = 1179535) B1179535
theorem B1769323 : Blo 1044610 1769323 := bstep (se 1 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 1769323 = 2653985) B2653985
theorem B1048443 : Blo 1044610 1048443 := bstep (se 1 (by rfl) ⟨786332, by rfl⟩ : syracuseStep 1048443 = 1572665) B1572665
theorem B1048495 : Blo 1044610 1048495 := bstep (se 1 (by rfl) ⟨786371, by rfl⟩ : syracuseStep 1048495 = 1572743) B1572743
theorem B1572791 : Blo 1044610 1572791 := bstep (se 1 (by rfl) ⟨1179593, by rfl⟩ : syracuseStep 1572791 = 2359187) B2359187
theorem B2359223 : Blo 1044610 2359223 := bstep (se 1 (by rfl) ⟨1769417, by rfl⟩ : syracuseStep 2359223 = 3538835) B3538835
theorem B1048519 : Blo 1044610 1048519 := bstep (se 1 (by rfl) ⟨786389, by rfl⟩ : syracuseStep 1048519 = 1572779) B1572779
theorem B1048539 : Blo 1044610 1048539 := bstep (se 1 (by rfl) ⟨786404, by rfl⟩ : syracuseStep 1048539 = 1572809) B1572809
theorem B1572827 : Blo 1044610 1572827 := bstep (se 1 (by rfl) ⟨1179620, by rfl⟩ : syracuseStep 1572827 = 2359241) B2359241
theorem B10060321 : Blo 1044610 10060321 := bstep (se 2 (by rfl) ⟨3772620, by rfl⟩ : syracuseStep 10060321 = 7545241) B7545241
theorem B2982521 : Blo 1044610 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B8946881 : Blo 1044610 8946881 := bstep (se 2 (by rfl) ⟨3355080, by rfl⟩ : syracuseStep 8946881 = 6710161) B6710161
theorem B9077953 : Blo 1044610 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B65406149 : Blo 1044610 65406149 := bstep (se 4 (by rfl) ⟨6131826, by rfl⟩ : syracuseStep 65406149 = 12263653) B12263653
theorem B12715373 : Blo 1044610 12715373 := bstep (se 3 (by rfl) ⟨2384132, by rfl⟩ : syracuseStep 12715373 = 4768265) B4768265
theorem B1115951 : Blo 1044610 1115951 := bstep (se 1 (by rfl) ⟨836963, by rfl⟩ : syracuseStep 1115951 = 1673927) B1673927
theorem B8947907 : Blo 1044610 8947907 := bstep (se 1 (by rfl) ⟨6710930, by rfl⟩ : syracuseStep 8947907 = 13421861) B13421861
theorem B4524499 : Blo 1044610 4524499 := bstep (se 1 (by rfl) ⟨3393374, by rfl⟩ : syracuseStep 4524499 = 6786749) B6786749
theorem B6818383 : Blo 1044610 6818383 := bstep (se 1 (by rfl) ⟨5113787, by rfl⟩ : syracuseStep 6818383 = 10227575) B10227575
theorem B17467991 : Blo 1044610 17467991 := bstep (se 1 (by rfl) ⟨13100993, by rfl⟩ : syracuseStep 17467991 = 26201987) B26201987
theorem B7539479 : Blo 1044610 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B8063879 : Blo 1044610 8063879 := bstep (se 1 (by rfl) ⟨6047909, by rfl⟩ : syracuseStep 8063879 = 12095819) B12095819
theorem B14323073 : Blo 1044610 14323073 := bstep (se 2 (by rfl) ⟨5371152, by rfl⟩ : syracuseStep 14323073 = 10742305) B10742305
theorem B1675055 : Blo 1044610 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B3772217 : Blo 1044610 3772217 := bstep (se 2 (by rfl) ⟨1414581, by rfl⟩ : syracuseStep 3772217 = 2829163) B2829163
theorem B24154685 : Blo 1044610 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B5968505 : Blo 1044610 5968505 := bstep (se 2 (by rfl) ⟨2238189, by rfl⟩ : syracuseStep 5968505 = 4476379) B4476379
theorem B8950571 : Blo 1044610 8950571 := bstep (se 1 (by rfl) ⟨6712928, by rfl⟩ : syracuseStep 8950571 = 13425857) B13425857
theorem B7934921 : Blo 1044610 7934921 := bstep (se 2 (by rfl) ⟨2975595, by rfl⟩ : syracuseStep 7934921 = 5951191) B5951191
theorem B2233577 : Blo 1044610 2233577 := bstep (se 2 (by rfl) ⟨837591, by rfl⟩ : syracuseStep 2233577 = 1675183) B1675183
theorem B11933729 : Blo 1044610 11933729 := bstep (se 2 (by rfl) ⟨4475148, by rfl⟩ : syracuseStep 11933729 = 8950297) B8950297
theorem B2234807 : Blo 1044610 2234807 := bstep (se 1 (by rfl) ⟨1676105, by rfl⟩ : syracuseStep 2234807 = 3352211) B3352211
theorem B4463531 : Blo 1044610 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B110042549 : Blo 1044610 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B33889751 : Blo 1044610 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B9674263 : Blo 1044610 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B5021513 : Blo 1044610 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B4464659 : Blo 1044610 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B2826569 : Blo 1044610 2826569 := bstep (se 2 (by rfl) ⟨1059963, by rfl⟩ : syracuseStep 2826569 = 2119927) B2119927
theorem B10461527 : Blo 1044610 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B40772105 : Blo 1044610 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B7938809 : Blo 1044610 7938809 := bstep (se 2 (by rfl) ⟨2977053, by rfl⟩ : syracuseStep 7938809 = 5954107) B5954107
theorem B36709361 : Blo 1044610 36709361 := bstep (se 2 (by rfl) ⟨13766010, by rfl⟩ : syracuseStep 36709361 = 27532021) B27532021
theorem B4466333 : Blo 1044610 4466333 := bstep (se 3 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 4466333 = 1674875) B1674875
theorem B30222017 : Blo 1044610 30222017 := bstep (se 2 (by rfl) ⟨11333256, by rfl⟩ : syracuseStep 30222017 = 22666513) B22666513
theorem B27142037 : Blo 1044610 27142037 := bstep (se 6 (by rfl) ⟨636141, by rfl⟩ : syracuseStep 27142037 = 1272283) B1272283
theorem B57387325 : Blo 1044610 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B38120129 : Blo 1044610 38120129 := bstep (se 2 (by rfl) ⟨14295048, by rfl⟩ : syracuseStep 38120129 = 28590097) B28590097
theorem B3975875 : Blo 1044610 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B9546461 : Blo 1044610 9546461 := bstep (se 3 (by rfl) ⟨1789961, by rfl⟩ : syracuseStep 9546461 = 3579923) B3579923
theorem B5024531 : Blo 1044610 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B3353993 : Blo 1044610 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B1322831 : Blo 1044610 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B5025665 : Blo 1044610 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B1322983 : Blo 1044610 1322983 := bstep (se 1 (by rfl) ⟨992237, by rfl⟩ : syracuseStep 1322983 = 1984475) B1984475
theorem B5025817 : Blo 1044610 5025817 := bstep (se 2 (by rfl) ⟨1884681, by rfl⟩ : syracuseStep 5025817 = 3769363) B3769363
theorem B7942211 : Blo 1044610 7942211 := bstep (se 1 (by rfl) ⟨5956658, by rfl⟩ : syracuseStep 7942211 = 11913317) B11913317
theorem B2830547 : Blo 1044610 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B3977545 : Blo 1044610 3977545 := bstep (se 2 (by rfl) ⟨1491579, by rfl⟩ : syracuseStep 3977545 = 2983159) B2983159
theorem B3977849 : Blo 1044610 3977849 := bstep (se 2 (by rfl) ⟨1491693, by rfl⟩ : syracuseStep 3977849 = 2983387) B2983387
theorem B2830969 : Blo 1044610 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B43037381 : Blo 1044610 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B10072775 : Blo 1044610 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B5288651 : Blo 1044610 5288651 := bstep (se 1 (by rfl) ⟨3966488, by rfl⟩ : syracuseStep 5288651 = 7932977) B7932977
theorem B5288813 : Blo 1044610 5288813 := bstep (se 3 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 5288813 = 1983305) B1983305
theorem B19379249 : Blo 1044610 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B9549161 : Blo 1044610 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B20100959 : Blo 1044610 20100959 := bstep (se 1 (by rfl) ⟨15075719, by rfl⟩ : syracuseStep 20100959 = 30151439) B30151439
theorem B87242795 : Blo 1044610 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B3586301 : Blo 1044610 3586301 := bstep (se 3 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 3586301 = 1344863) B1344863
theorem B1325423 : Blo 1044610 1325423 := bstep (se 1 (by rfl) ⟨994067, by rfl⟩ : syracuseStep 1325423 = 1988135) B1988135
theorem B1325479 : Blo 1044610 1325479 := bstep (se 1 (by rfl) ⟨994109, by rfl⟩ : syracuseStep 1325479 = 1988219) B1988219
theorem B5454253 : Blo 1044610 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B1325803 : Blo 1044610 1325803 := bstep (se 1 (by rfl) ⟨994352, by rfl⟩ : syracuseStep 1325803 = 1988705) B1988705
theorem B14334895 : Blo 1044610 14334895 := bstep (se 1 (by rfl) ⟨10751171, by rfl⟩ : syracuseStep 14334895 = 21502343) B21502343
theorem B3357683 : Blo 1044610 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B5651927 : Blo 1044610 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B4472279 : Blo 1044610 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B1588729 : Blo 1044610 1588729 := bstep (se 2 (by rfl) ⟨595773, by rfl⟩ : syracuseStep 1588729 = 1191547) B1191547
theorem B6700603 : Blo 1044610 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B1326775 : Blo 1044610 1326775 := bstep (se 1 (by rfl) ⟨995081, by rfl⟩ : syracuseStep 1326775 = 1990163) B1990163
theorem B5291729 : Blo 1044610 5291729 := bstep (se 2 (by rfl) ⟨1984398, by rfl⟩ : syracuseStep 5291729 = 3968797) B3968797
theorem B5652271 : Blo 1044610 5652271 := bstep (se 1 (by rfl) ⟨4239203, by rfl⟩ : syracuseStep 5652271 = 8478407) B8478407
theorem B5030545 : Blo 1044610 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B1983199 : Blo 1044610 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B1885007 : Blo 1044610 1885007 := bstep (se 1 (by rfl) ⟨1413755, by rfl⟩ : syracuseStep 1885007 = 2827511) B2827511
theorem B4474055 : Blo 1044610 4474055 := bstep (se 1 (by rfl) ⟨3355541, by rfl⟩ : syracuseStep 4474055 = 6711083) B6711083
theorem B43500887 : Blo 1044610 43500887 := bstep (se 1 (by rfl) ⟨32625665, by rfl⟩ : syracuseStep 43500887 = 65251331) B65251331
theorem B1983943 : Blo 1044610 1983943 := bstep (se 1 (by rfl) ⟨1487957, by rfl⟩ : syracuseStep 1983943 = 2975915) B2975915
theorem B17876537 : Blo 1044610 17876537 := bstep (se 2 (by rfl) ⟨6703701, by rfl⟩ : syracuseStep 17876537 = 13407403) B13407403
theorem B397067923 : Blo 1044610 397067923 := bstep (se 1 (by rfl) ⟨297800942, by rfl⟩ : syracuseStep 397067923 = 595601885) B595601885
theorem B21481325 : Blo 1044610 21481325 := bstep (se 3 (by rfl) ⟨4027748, by rfl⟩ : syracuseStep 21481325 = 8055497) B8055497
theorem B5294159 : Blo 1044610 5294159 := bstep (se 1 (by rfl) ⟨3970619, by rfl⟩ : syracuseStep 5294159 = 7941239) B7941239
theorem B2148457 : Blo 1044610 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B6703397 : Blo 1044610 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1591643 : Blo 1044610 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B31902497 : Blo 1044610 31902497 := bstep (se 2 (by rfl) ⟨11963436, by rfl⟩ : syracuseStep 31902497 = 23926873) B23926873
theorem B3525821 : Blo 1044610 3525821 := bstep (se 3 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 3525821 = 1322183) B1322183
theorem B5295293 : Blo 1044610 5295293 := bstep (se 3 (by rfl) ⟨992867, by rfl⟩ : syracuseStep 5295293 = 1985735) B1985735
theorem B5655905 : Blo 1044610 5655905 := bstep (se 2 (by rfl) ⟨2120964, by rfl⟩ : syracuseStep 5655905 = 4241929) B4241929
theorem B7949987 : Blo 1044610 7949987 := bstep (se 1 (by rfl) ⟨5962490, by rfl⟩ : syracuseStep 7949987 = 11924981) B11924981
theorem B8933075 : Blo 1044610 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B16338797 : Blo 1044610 16338797 := bstep (se 3 (by rfl) ⟨3063524, by rfl⟩ : syracuseStep 16338797 = 6127049) B6127049
theorem B8048605 : Blo 1044610 8048605 := bstep (se 3 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 8048605 = 3018227) B3018227
theorem B28660067 : Blo 1044610 28660067 := bstep (se 1 (by rfl) ⟨21495050, by rfl⟩ : syracuseStep 28660067 = 42990101) B42990101
theorem B4772353 : Blo 1044610 4772353 := bstep (se 2 (by rfl) ⟨1789632, by rfl⟩ : syracuseStep 4772353 = 3579265) B3579265
theorem B1987193 : Blo 1044610 1987193 := bstep (se 2 (by rfl) ⟨745197, by rfl⟩ : syracuseStep 1987193 = 1490395) B1490395
theorem B1987247 : Blo 1044610 1987247 := bstep (se 1 (by rfl) ⟨1490435, by rfl⟩ : syracuseStep 1987247 = 2980871) B2980871
theorem B7164715 : Blo 1044610 7164715 := bstep (se 1 (by rfl) ⟨5373536, by rfl⟩ : syracuseStep 7164715 = 10747073) B10747073
theorem B7558505 : Blo 1044610 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B20633221 : Blo 1044610 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B2545537 : Blo 1044610 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B3528737 : Blo 1044610 3528737 := bstep (se 2 (by rfl) ⟨1323276, by rfl⟩ : syracuseStep 3528737 = 2646553) B2646553
theorem B5298209 : Blo 1044610 5298209 := bstep (se 2 (by rfl) ⟨1986828, by rfl⟩ : syracuseStep 5298209 = 3973657) B3973657
theorem B7952417 : Blo 1044610 7952417 := bstep (se 2 (by rfl) ⟨2982156, by rfl⟩ : syracuseStep 7952417 = 5964313) B5964313
theorem B5298371 : Blo 1044610 5298371 := bstep (se 1 (by rfl) ⟨3973778, by rfl⟩ : syracuseStep 5298371 = 7947557) B7947557
theorem B6707447 : Blo 1044610 6707447 := bstep (se 1 (by rfl) ⟨5030585, by rfl⟩ : syracuseStep 6707447 = 10061171) B10061171
theorem B1989031 : Blo 1044610 1989031 := bstep (se 1 (by rfl) ⟨1491773, by rfl⟩ : syracuseStep 1989031 = 2983547) B2983547
theorem B1989191 : Blo 1044610 1989191 := bstep (se 1 (by rfl) ⟨1491893, by rfl⟩ : syracuseStep 1989191 = 2983787) B2983787
theorem B2644559 : Blo 1044610 2644559 := bstep (se 1 (by rfl) ⟨1983419, by rfl⟩ : syracuseStep 2644559 = 3966839) B3966839
theorem B13392641 : Blo 1044610 13392641 := bstep (se 2 (by rfl) ⟨5022240, by rfl⟩ : syracuseStep 13392641 = 10044481) B10044481
theorem B1989623 : Blo 1044610 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B1989775 : Blo 1044610 1989775 := bstep (se 1 (by rfl) ⟨1492331, by rfl⟩ : syracuseStep 1989775 = 2984663) B2984663
theorem B2645207 : Blo 1044610 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B5955065 : Blo 1044610 5955065 := bstep (se 2 (by rfl) ⟨2233149, by rfl⟩ : syracuseStep 5955065 = 4466299) B4466299
theorem B2645561 : Blo 1044610 2645561 := bstep (se 2 (by rfl) ⟨992085, by rfl⟩ : syracuseStep 2645561 = 1984171) B1984171
theorem B11329105 : Blo 1044610 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B8937175 : Blo 1044610 8937175 := bstep (se 1 (by rfl) ⟨6702881, by rfl⟩ : syracuseStep 8937175 = 13405763) B13405763
theorem B36298529 : Blo 1044610 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B2350889 : Blo 1044610 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B17850293 : Blo 1044610 17850293 := bstep (se 5 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 17850293 = 1673465) B1673465
theorem B8708147 : Blo 1044610 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B22602509 : Blo 1044610 22602509 := bstep (se 3 (by rfl) ⟨4237970, by rfl⟩ : syracuseStep 22602509 = 8475941) B8475941
theorem B2351951 : Blo 1044610 2351951 := bstep (se 1 (by rfl) ⟨1763963, by rfl⟩ : syracuseStep 2351951 = 3527927) B3527927
theorem B3531599 : Blo 1044610 3531599 := bstep (se 1 (by rfl) ⟨2648699, by rfl⟩ : syracuseStep 3531599 = 5297399) B5297399
theorem B6710111 : Blo 1044610 6710111 := bstep (se 1 (by rfl) ⟨5032583, by rfl⟩ : syracuseStep 6710111 = 10065167) B10065167
theorem B2352167 : Blo 1044610 2352167 := bstep (se 1 (by rfl) ⟨1764125, by rfl⟩ : syracuseStep 2352167 = 3528251) B3528251
theorem B5661785 : Blo 1044610 5661785 := bstep (se 2 (by rfl) ⟨2123169, by rfl⟩ : syracuseStep 5661785 = 4246339) B4246339
theorem B22602851 : Blo 1044610 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B3531923 : Blo 1044610 3531923 := bstep (se 1 (by rfl) ⟨2648942, by rfl⟩ : syracuseStep 3531923 = 5297885) B5297885
theorem B2352347 : Blo 1044610 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B5956841 : Blo 1044610 5956841 := bstep (se 2 (by rfl) ⟨2233815, by rfl⟩ : syracuseStep 5956841 = 4467631) B4467631
theorem B2352545 : Blo 1044610 2352545 := bstep (se 2 (by rfl) ⟨882204, by rfl⟩ : syracuseStep 2352545 = 1764409) B1764409
theorem B3532193 : Blo 1044610 3532193 := bstep (se 2 (by rfl) ⟨1324572, by rfl⟩ : syracuseStep 3532193 = 2649145) B2649145
theorem B1763113 : Blo 1044610 1763113 := bstep (se 2 (by rfl) ⟨661167, by rfl⟩ : syracuseStep 1763113 = 1322335) B1322335
theorem B2647849 : Blo 1044610 2647849 := bstep (se 2 (by rfl) ⟨992943, by rfl⟩ : syracuseStep 2647849 = 1985887) B1985887
theorem B2385721 : Blo 1044610 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B5302097 : Blo 1044610 5302097 := bstep (se 2 (by rfl) ⟨1988286, by rfl⟩ : syracuseStep 5302097 = 3976573) B3976573
theorem B7956305 : Blo 1044610 7956305 := bstep (se 2 (by rfl) ⟨2983614, by rfl⟩ : syracuseStep 7956305 = 5967229) B5967229
theorem B2353103 : Blo 1044610 2353103 := bstep (se 1 (by rfl) ⟨1764827, by rfl⟩ : syracuseStep 2353103 = 3529655) B3529655
theorem B2353481 : Blo 1044610 2353481 := bstep (se 2 (by rfl) ⟨882555, by rfl⟩ : syracuseStep 2353481 = 1765111) B1765111
theorem B1567067 : Blo 1044610 1567067 := bstep (se 1 (by rfl) ⟨1175300, by rfl⟩ : syracuseStep 1567067 = 2350601) B2350601
theorem B2353499 : Blo 1044610 2353499 := bstep (se 1 (by rfl) ⟨1765124, by rfl⟩ : syracuseStep 2353499 = 3530249) B3530249
theorem B7170515 : Blo 1044610 7170515 := bstep (se 1 (by rfl) ⟨5377886, by rfl⟩ : syracuseStep 7170515 = 10755773) B10755773
theorem B1567295 : Blo 1044610 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B1763903 : Blo 1044610 1763903 := bstep (se 1 (by rfl) ⟨1322927, by rfl⟩ : syracuseStep 1763903 = 2645855) B2645855
theorem B2648639 : Blo 1044610 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B5302907 : Blo 1044610 5302907 := bstep (se 1 (by rfl) ⟨3977180, by rfl⟩ : syracuseStep 5302907 = 7954361) B7954361
theorem B2681515 : Blo 1044610 2681515 := bstep (se 1 (by rfl) ⟨2011136, by rfl⟩ : syracuseStep 2681515 = 4022273) B4022273
theorem B1567415 : Blo 1044610 1567415 := bstep (se 1 (by rfl) ⟨1175561, by rfl⟩ : syracuseStep 1567415 = 2351123) B2351123
theorem B1567643 : Blo 1044610 1567643 := bstep (se 1 (by rfl) ⟨1175732, by rfl⟩ : syracuseStep 1567643 = 2351465) B2351465
theorem B2354075 : Blo 1044610 2354075 := bstep (se 1 (by rfl) ⟨1765556, by rfl⟩ : syracuseStep 2354075 = 3531113) B3531113
theorem B2354273 : Blo 1044610 2354273 := bstep (se 2 (by rfl) ⟨882852, by rfl⟩ : syracuseStep 2354273 = 1765705) B1765705
theorem B2649287 : Blo 1044610 2649287 := bstep (se 1 (by rfl) ⟨1986965, by rfl⟩ : syracuseStep 2649287 = 3973931) B3973931
theorem B1764571 : Blo 1044610 1764571 := bstep (se 1 (by rfl) ⟨1323428, by rfl⟩ : syracuseStep 1764571 = 2646857) B2646857
theorem B2649307 : Blo 1044610 2649307 := bstep (se 1 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 2649307 = 3973961) B3973961
theorem B1568039 : Blo 1044610 1568039 := bstep (se 1 (by rfl) ⟨1176029, by rfl⟩ : syracuseStep 1568039 = 2352059) B2352059
theorem B2354471 : Blo 1044610 2354471 := bstep (se 1 (by rfl) ⟨1765853, by rfl⟩ : syracuseStep 2354471 = 3531707) B3531707
theorem B1568123 : Blo 1044610 1568123 := bstep (se 1 (by rfl) ⟨1176092, by rfl⟩ : syracuseStep 1568123 = 2352185) B2352185
theorem B1568249 : Blo 1044610 1568249 := bstep (se 2 (by rfl) ⟨588093, by rfl⟩ : syracuseStep 1568249 = 1176187) B1176187
theorem B1568351 : Blo 1044610 1568351 := bstep (se 1 (by rfl) ⟨1176263, by rfl⟩ : syracuseStep 1568351 = 2352527) B2352527
theorem B2354849 : Blo 1044610 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B1175215 : Blo 1044610 1175215 := bstep (se 1 (by rfl) ⟨881411, by rfl⟩ : syracuseStep 1175215 = 1762823) B1762823
theorem B5664467 : Blo 1044610 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B1568567 : Blo 1044610 1568567 := bstep (se 1 (by rfl) ⟨1176425, by rfl⟩ : syracuseStep 1568567 = 2352851) B2352851
theorem B21491513 : Blo 1044610 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B5107585 : Blo 1044610 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B1175503 : Blo 1044610 1175503 := bstep (se 1 (by rfl) ⟨881627, by rfl⟩ : syracuseStep 1175503 = 1763255) B1763255
theorem B1765327 : Blo 1044610 1765327 := bstep (se 1 (by rfl) ⟨1323995, by rfl⟩ : syracuseStep 1765327 = 2647991) B2647991
theorem B2355209 : Blo 1044610 2355209 := bstep (se 2 (by rfl) ⟨883203, by rfl⟩ : syracuseStep 2355209 = 1766407) B1766407
theorem B11923523 : Blo 1044610 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B2977897 : Blo 1044610 2977897 := bstep (se 2 (by rfl) ⟨1116711, by rfl⟩ : syracuseStep 2977897 = 2233423) B2233423
theorem B1568873 : Blo 1044610 1568873 := bstep (se 2 (by rfl) ⟨588327, by rfl⟩ : syracuseStep 1568873 = 1176655) B1176655
theorem B17854667 : Blo 1044610 17854667 := bstep (se 1 (by rfl) ⟨13391000, by rfl⟩ : syracuseStep 17854667 = 26782001) B26782001
theorem B5959939 : Blo 1044610 5959939 := bstep (se 1 (by rfl) ⟨4469954, by rfl⟩ : syracuseStep 5959939 = 8939909) B8939909
theorem B1044767 : Blo 1044610 1044767 := bstep (se 1 (by rfl) ⟨783575, by rfl⟩ : syracuseStep 1044767 = 1567151) B1567151
theorem B2650441 : Blo 1044610 2650441 := bstep (se 2 (by rfl) ⟨993915, by rfl⟩ : syracuseStep 2650441 = 1987831) B1987831
theorem B1044827 : Blo 1044610 1044827 := bstep (se 1 (by rfl) ⟨783620, by rfl⟩ : syracuseStep 1044827 = 1567241) B1567241
theorem B1175899 : Blo 1044610 1175899 := bstep (se 1 (by rfl) ⟨881924, by rfl⟩ : syracuseStep 1175899 = 1763849) B1763849
theorem B2519387 : Blo 1044610 2519387 := bstep (se 1 (by rfl) ⟨1889540, by rfl⟩ : syracuseStep 2519387 = 3779081) B3779081
theorem B1044847 : Blo 1044610 1044847 := bstep (se 1 (by rfl) ⟨783635, by rfl⟩ : syracuseStep 1044847 = 1567271) B1567271
theorem B1044903 : Blo 1044610 1044903 := bstep (se 1 (by rfl) ⟨783677, by rfl⟩ : syracuseStep 1044903 = 1567355) B1567355
theorem B1569191 : Blo 1044610 1569191 := bstep (se 1 (by rfl) ⟨1176893, by rfl⟩ : syracuseStep 1569191 = 2353787) B2353787
theorem B2355623 : Blo 1044610 2355623 := bstep (se 1 (by rfl) ⟨1766717, by rfl⟩ : syracuseStep 2355623 = 3533435) B3533435
theorem B1176007 : Blo 1044610 1176007 := bstep (se 1 (by rfl) ⟨882005, by rfl⟩ : syracuseStep 1176007 = 1764011) B1764011
theorem B1044987 : Blo 1044610 1044987 := bstep (se 1 (by rfl) ⟨783740, by rfl⟩ : syracuseStep 1044987 = 1567481) B1567481
theorem B1569275 : Blo 1044610 1569275 := bstep (se 1 (by rfl) ⟨1176956, by rfl⟩ : syracuseStep 1569275 = 2353913) B2353913
theorem B5304851 : Blo 1044610 5304851 := bstep (se 1 (by rfl) ⟨3978638, by rfl⟩ : syracuseStep 5304851 = 7957277) B7957277
theorem B3535379 : Blo 1044610 3535379 := bstep (se 1 (by rfl) ⟨2651534, by rfl⟩ : syracuseStep 3535379 = 5303069) B5303069
theorem B2355731 : Blo 1044610 2355731 := bstep (se 1 (by rfl) ⟨1766798, by rfl⟩ : syracuseStep 2355731 = 3533597) B3533597
theorem B7533107 : Blo 1044610 7533107 := bstep (se 1 (by rfl) ⟨5649830, by rfl⟩ : syracuseStep 7533107 = 11299661) B11299661
theorem B1045055 : Blo 1044610 1045055 := bstep (se 1 (by rfl) ⟨783791, by rfl⟩ : syracuseStep 1045055 = 1567583) B1567583
theorem B1045063 : Blo 1044610 1045063 := bstep (se 1 (by rfl) ⟨783797, by rfl⟩ : syracuseStep 1045063 = 1567595) B1567595
theorem B2355785 : Blo 1044610 2355785 := bstep (se 2 (by rfl) ⟨883419, by rfl⟩ : syracuseStep 2355785 = 1766839) B1766839
theorem B1569401 : Blo 1044610 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B1766009 : Blo 1044610 1766009 := bstep (se 2 (by rfl) ⟨662253, by rfl⟩ : syracuseStep 1766009 = 1324507) B1324507
theorem B2650745 : Blo 1044610 2650745 := bstep (se 2 (by rfl) ⟨994029, by rfl⟩ : syracuseStep 2650745 = 1988059) B1988059
theorem B1569455 : Blo 1044610 1569455 := bstep (se 1 (by rfl) ⟨1177091, by rfl⟩ : syracuseStep 1569455 = 2354183) B2354183
theorem B1766063 : Blo 1044610 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B1045215 : Blo 1044610 1045215 := bstep (se 1 (by rfl) ⟨783911, by rfl⟩ : syracuseStep 1045215 = 1567823) B1567823
theorem B1569503 : Blo 1044610 1569503 := bstep (se 1 (by rfl) ⟨1177127, by rfl⟩ : syracuseStep 1569503 = 2354255) B2354255
theorem B1045295 : Blo 1044610 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B1176367 : Blo 1044610 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B1045403 : Blo 1044610 1045403 := bstep (se 1 (by rfl) ⟨784052, by rfl⟩ : syracuseStep 1045403 = 1568105) B1568105
theorem B1176475 : Blo 1044610 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B1766299 : Blo 1044610 1766299 := bstep (se 1 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 1766299 = 2649449) B2649449
theorem B1045455 : Blo 1044610 1045455 := bstep (se 1 (by rfl) ⟨784091, by rfl⟩ : syracuseStep 1045455 = 1568183) B1568183
theorem B1045479 : Blo 1044610 1045479 := bstep (se 1 (by rfl) ⟨784109, by rfl⟩ : syracuseStep 1045479 = 1568219) B1568219
theorem B1569767 : Blo 1044610 1569767 := bstep (se 1 (by rfl) ⟨1177325, by rfl⟩ : syracuseStep 1569767 = 2354651) B2354651
theorem B2356199 : Blo 1044610 2356199 := bstep (se 1 (by rfl) ⟨1767149, by rfl⟩ : syracuseStep 2356199 = 3534299) B3534299
theorem B2389115 : Blo 1044610 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B1570025 : Blo 1044610 1570025 := bstep (se 2 (by rfl) ⟨588759, by rfl⟩ : syracuseStep 1570025 = 1177519) B1177519
theorem B1045791 : Blo 1044610 1045791 := bstep (se 1 (by rfl) ⟨784343, by rfl⟩ : syracuseStep 1045791 = 1568687) B1568687
theorem B1570079 : Blo 1044610 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B1176871 : Blo 1044610 1176871 := bstep (se 1 (by rfl) ⟨882653, by rfl⟩ : syracuseStep 1176871 = 1765307) B1765307
theorem B1045851 : Blo 1044610 1045851 := bstep (se 1 (by rfl) ⟨784388, by rfl⟩ : syracuseStep 1045851 = 1568777) B1568777
theorem B2356577 : Blo 1044610 2356577 := bstep (se 2 (by rfl) ⟨883716, by rfl⟩ : syracuseStep 2356577 = 1767433) B1767433
theorem B1045871 : Blo 1044610 1045871 := bstep (se 1 (by rfl) ⟨784403, by rfl⟩ : syracuseStep 1045871 = 1568807) B1568807
theorem B1176943 : Blo 1044610 1176943 := bstep (se 1 (by rfl) ⟨882707, by rfl⟩ : syracuseStep 1176943 = 1765415) B1765415
theorem B1045927 : Blo 1044610 1045927 := bstep (se 1 (by rfl) ⟨784445, by rfl⟩ : syracuseStep 1045927 = 1568891) B1568891
theorem B2356667 : Blo 1044610 2356667 := bstep (se 1 (by rfl) ⟨1767500, by rfl⟩ : syracuseStep 2356667 = 3535001) B3535001
theorem B1570247 : Blo 1044610 1570247 := bstep (se 1 (by rfl) ⟨1177685, by rfl⟩ : syracuseStep 1570247 = 2355371) B2355371
theorem B1046011 : Blo 1044610 1046011 := bstep (se 1 (by rfl) ⟨784508, by rfl⟩ : syracuseStep 1046011 = 1569017) B1569017
theorem B2356793 : Blo 1044610 2356793 := bstep (se 2 (by rfl) ⟨883797, by rfl⟩ : syracuseStep 2356793 = 1767595) B1767595
theorem B1046079 : Blo 1044610 1046079 := bstep (se 1 (by rfl) ⟨784559, by rfl⟩ : syracuseStep 1046079 = 1569119) B1569119
theorem B1046087 : Blo 1044610 1046087 := bstep (se 1 (by rfl) ⟨784565, by rfl⟩ : syracuseStep 1046087 = 1569131) B1569131
theorem B1177159 : Blo 1044610 1177159 := bstep (se 1 (by rfl) ⟨882869, by rfl⟩ : syracuseStep 1177159 = 1765739) B1765739
theorem B1046239 : Blo 1044610 1046239 := bstep (se 1 (by rfl) ⟨784679, by rfl⟩ : syracuseStep 1046239 = 1569359) B1569359
theorem B1570601 : Blo 1044610 1570601 := bstep (se 2 (by rfl) ⟨588975, by rfl⟩ : syracuseStep 1570601 = 1177951) B1177951
theorem B1046319 : Blo 1044610 1046319 := bstep (se 1 (by rfl) ⟨784739, by rfl⟩ : syracuseStep 1046319 = 1569479) B1569479
theorem B1570607 : Blo 1044610 1570607 := bstep (se 1 (by rfl) ⟨1177955, by rfl⟩ : syracuseStep 1570607 = 2355911) B2355911
theorem B1046427 : Blo 1044610 1046427 := bstep (se 1 (by rfl) ⟨784820, by rfl⟩ : syracuseStep 1046427 = 1569641) B1569641
theorem B38205371 : Blo 1044610 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B1046479 : Blo 1044610 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B1046503 : Blo 1044610 1046503 := bstep (se 1 (by rfl) ⟨784877, by rfl⟩ : syracuseStep 1046503 = 1569755) B1569755
theorem B2357459 : Blo 1044610 2357459 := bstep (se 1 (by rfl) ⟨1768094, by rfl⟩ : syracuseStep 2357459 = 3536189) B3536189
theorem B1571081 : Blo 1044610 1571081 := bstep (se 2 (by rfl) ⟨589155, by rfl⟩ : syracuseStep 1571081 = 1178311) B1178311
theorem B2357513 : Blo 1044610 2357513 := bstep (se 2 (by rfl) ⟨884067, by rfl⟩ : syracuseStep 2357513 = 1768135) B1768135
theorem B3537161 : Blo 1044610 3537161 := bstep (se 2 (by rfl) ⟨1326435, by rfl⟩ : syracuseStep 3537161 = 2652871) B2652871
theorem B5306633 : Blo 1044610 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B5372183 : Blo 1044610 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B1046815 : Blo 1044610 1046815 := bstep (se 1 (by rfl) ⟨785111, by rfl⟩ : syracuseStep 1046815 = 1570223) B1570223
theorem B1046875 : Blo 1044610 1046875 := bstep (se 1 (by rfl) ⟨785156, by rfl⟩ : syracuseStep 1046875 = 1570313) B1570313
theorem B2652527 : Blo 1044610 2652527 := bstep (se 1 (by rfl) ⟨1989395, by rfl⟩ : syracuseStep 2652527 = 3978791) B3978791
theorem B1046895 : Blo 1044610 1046895 := bstep (se 1 (by rfl) ⟨785171, by rfl⟩ : syracuseStep 1046895 = 1570343) B1570343
theorem B1571183 : Blo 1044610 1571183 := bstep (se 1 (by rfl) ⟨1178387, by rfl⟩ : syracuseStep 1571183 = 2356775) B2356775
theorem B1767791 : Blo 1044610 1767791 := bstep (se 1 (by rfl) ⟨1325843, by rfl⟩ : syracuseStep 1767791 = 2651687) B2651687
theorem B1046951 : Blo 1044610 1046951 := bstep (se 1 (by rfl) ⟨785213, by rfl⟩ : syracuseStep 1046951 = 1570427) B1570427
theorem B1178023 : Blo 1044610 1178023 := bstep (se 1 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 1178023 = 1767035) B1767035
theorem B2357729 : Blo 1044610 2357729 := bstep (se 2 (by rfl) ⟨884148, by rfl⟩ : syracuseStep 2357729 = 1768297) B1768297
theorem B1047035 : Blo 1044610 1047035 := bstep (se 1 (by rfl) ⟨785276, by rfl⟩ : syracuseStep 1047035 = 1570553) B1570553
theorem B7174651 : Blo 1044610 7174651 := bstep (se 1 (by rfl) ⟨5380988, by rfl⟩ : syracuseStep 7174651 = 10761977) B10761977
theorem B2980415 : Blo 1044610 2980415 := bstep (se 1 (by rfl) ⟨2235311, by rfl⟩ : syracuseStep 2980415 = 4470623) B4470623
theorem B1047103 : Blo 1044610 1047103 := bstep (se 1 (by rfl) ⟨785327, by rfl⟩ : syracuseStep 1047103 = 1570655) B1570655
theorem B1047111 : Blo 1044610 1047111 := bstep (se 1 (by rfl) ⟨785333, by rfl⟩ : syracuseStep 1047111 = 1570667) B1570667
theorem B1571399 : Blo 1044610 1571399 := bstep (se 1 (by rfl) ⟨1178549, by rfl⟩ : syracuseStep 1571399 = 2357099) B2357099
theorem B1768007 : Blo 1044610 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B1571435 : Blo 1044610 1571435 := bstep (se 1 (by rfl) ⟨1178576, by rfl⟩ : syracuseStep 1571435 = 2357153) B2357153
theorem B1047263 : Blo 1044610 1047263 := bstep (se 1 (by rfl) ⟨785447, by rfl⟩ : syracuseStep 1047263 = 1570895) B1570895
theorem B2358035 : Blo 1044610 2358035 := bstep (se 1 (by rfl) ⟨1768526, by rfl⟩ : syracuseStep 2358035 = 3537053) B3537053
theorem B1047343 : Blo 1044610 1047343 := bstep (se 1 (by rfl) ⟨785507, by rfl⟩ : syracuseStep 1047343 = 1571015) B1571015
theorem B1571663 : Blo 1044610 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B1047451 : Blo 1044610 1047451 := bstep (se 1 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 1047451 = 1571177) B1571177
theorem B1047503 : Blo 1044610 1047503 := bstep (se 1 (by rfl) ⟨785627, by rfl⟩ : syracuseStep 1047503 = 1571255) B1571255
theorem B1047527 : Blo 1044610 1047527 := bstep (se 1 (by rfl) ⟨785645, by rfl⟩ : syracuseStep 1047527 = 1571291) B1571291
theorem B1178599 : Blo 1044610 1178599 := bstep (se 1 (by rfl) ⟨883949, by rfl⟩ : syracuseStep 1178599 = 1767899) B1767899
theorem B1768439 : Blo 1044610 1768439 := bstep (se 1 (by rfl) ⟨1326329, by rfl⟩ : syracuseStep 1768439 = 2652659) B2652659
theorem B2653175 : Blo 1044610 2653175 := bstep (se 1 (by rfl) ⟨1989881, by rfl⟩ : syracuseStep 2653175 = 3979763) B3979763
theorem B2358395 : Blo 1044610 2358395 := bstep (se 1 (by rfl) ⟨1768796, by rfl⟩ : syracuseStep 2358395 = 3537593) B3537593
theorem B2653307 : Blo 1044610 2653307 := bstep (se 1 (by rfl) ⟨1989980, by rfl⟩ : syracuseStep 2653307 = 3979961) B3979961
theorem B1572059 : Blo 1044610 1572059 := bstep (se 1 (by rfl) ⟨1179044, by rfl⟩ : syracuseStep 1572059 = 2358089) B2358089
theorem B2358521 : Blo 1044610 2358521 := bstep (se 2 (by rfl) ⟨884445, by rfl⟩ : syracuseStep 2358521 = 1768891) B1768891
theorem B1047839 : Blo 1044610 1047839 := bstep (se 1 (by rfl) ⟨785879, by rfl⟩ : syracuseStep 1047839 = 1571759) B1571759
theorem B1047899 : Blo 1044610 1047899 := bstep (se 1 (by rfl) ⟨785924, by rfl⟩ : syracuseStep 1047899 = 1571849) B1571849
theorem B1047919 : Blo 1044610 1047919 := bstep (se 1 (by rfl) ⟨785939, by rfl⟩ : syracuseStep 1047919 = 1571879) B1571879
theorem B3538295 : Blo 1044610 3538295 := bstep (se 1 (by rfl) ⟨2653721, by rfl⟩ : syracuseStep 3538295 = 5307443) B5307443
theorem B5307767 : Blo 1044610 5307767 := bstep (se 1 (by rfl) ⟨3980825, by rfl⟩ : syracuseStep 5307767 = 7961651) B7961651
theorem B1572233 : Blo 1044610 1572233 := bstep (se 2 (by rfl) ⟨589587, by rfl⟩ : syracuseStep 1572233 = 1179175) B1179175
theorem B2358665 : Blo 1044610 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B1047975 : Blo 1044610 1047975 := bstep (se 1 (by rfl) ⟨785981, by rfl⟩ : syracuseStep 1047975 = 1571963) B1571963
theorem B1048059 : Blo 1044610 1048059 := bstep (se 1 (by rfl) ⟨786044, by rfl⟩ : syracuseStep 1048059 = 1572089) B1572089
theorem B2358791 : Blo 1044610 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B5307929 : Blo 1044610 5307929 := bstep (se 2 (by rfl) ⟨1990473, by rfl⟩ : syracuseStep 5307929 = 3980947) B3980947
theorem B7962137 : Blo 1044610 7962137 := bstep (se 2 (by rfl) ⟨2985801, by rfl⟩ : syracuseStep 7962137 = 5971603) B5971603
theorem B1048127 : Blo 1044610 1048127 := bstep (se 1 (by rfl) ⟨786095, by rfl⟩ : syracuseStep 1048127 = 1572191) B1572191
theorem B1048135 : Blo 1044610 1048135 := bstep (se 1 (by rfl) ⟨786101, by rfl⟩ : syracuseStep 1048135 = 1572203) B1572203
theorem B2358971 : Blo 1044610 2358971 := bstep (se 1 (by rfl) ⟨1769228, by rfl⟩ : syracuseStep 2358971 = 3538457) B3538457
theorem B1048287 : Blo 1044610 1048287 := bstep (se 1 (by rfl) ⟨786215, by rfl⟩ : syracuseStep 1048287 = 1572431) B1572431
theorem B1572587 : Blo 1044610 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B1769195 : Blo 1044610 1769195 := bstep (se 1 (by rfl) ⟨1326896, by rfl⟩ : syracuseStep 1769195 = 2653793) B2653793
theorem B1048367 : Blo 1044610 1048367 := bstep (se 1 (by rfl) ⟨786275, by rfl⟩ : syracuseStep 1048367 = 1572551) B1572551
theorem B2359097 : Blo 1044610 2359097 := bstep (se 2 (by rfl) ⟨884661, by rfl⟩ : syracuseStep 2359097 = 1769323) B1769323
theorem B1048475 : Blo 1044610 1048475 := bstep (se 1 (by rfl) ⟨786356, by rfl⟩ : syracuseStep 1048475 = 1572713) B1572713
theorem B1048527 : Blo 1044610 1048527 := bstep (se 1 (by rfl) ⟨786395, by rfl⟩ : syracuseStep 1048527 = 1572791) B1572791
theorem B1572815 : Blo 1044610 1572815 := bstep (se 1 (by rfl) ⟨1179611, by rfl⟩ : syracuseStep 1572815 = 2359223) B2359223
theorem B1048551 : Blo 1044610 1048551 := bstep (se 1 (by rfl) ⟨786413, by rfl⟩ : syracuseStep 1048551 = 1572827) B1572827
theorem B5964587 : Blo 1044610 5964587 := bstep (se 1 (by rfl) ⟨4473440, by rfl⟩ : syracuseStep 5964587 = 8946881) B8946881
theorem B29000591 : Blo 1044610 29000591 := bstep (se 1 (by rfl) ⟨21750443, by rfl⟩ : syracuseStep 29000591 = 43500887) B43500887
theorem B14320883 : Blo 1044610 14320883 := bstep (se 1 (by rfl) ⟨10740662, by rfl⟩ : syracuseStep 14320883 = 21481325) B21481325
theorem B5965271 : Blo 1044610 5965271 := bstep (se 1 (by rfl) ⟨4473953, by rfl⟩ : syracuseStep 5965271 = 8947907) B8947907
theorem B21268331 : Blo 1044610 21268331 := bstep (se 1 (by rfl) ⟨15951248, by rfl⟩ : syracuseStep 21268331 = 31902497) B31902497
theorem B3770603 : Blo 1044610 3770603 := bstep (se 1 (by rfl) ⟨2827952, by rfl⟩ : syracuseStep 3770603 = 5655905) B5655905
theorem B3180961 : Blo 1044610 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B1116703 : Blo 1044610 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B19106711 : Blo 1044610 19106711 := bstep (se 1 (by rfl) ⟨14330033, by rfl⟩ : syracuseStep 19106711 = 28660067) B28660067
theorem B76516433 : Blo 1044610 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B11930813 : Blo 1044610 11930813 := bstep (se 3 (by rfl) ⟨2237027, by rfl⟩ : syracuseStep 11930813 = 4474055) B4474055
theorem B5967047 : Blo 1044610 5967047 := bstep (se 1 (by rfl) ⟨4475285, by rfl⟩ : syracuseStep 5967047 = 8950571) B8950571
theorem B6032665 : Blo 1044610 6032665 := bstep (se 2 (by rfl) ⟨2262249, by rfl⟩ : syracuseStep 6032665 = 4524499) B4524499
theorem B3575353 : Blo 1044610 3575353 := bstep (se 2 (by rfl) ⟨1340757, by rfl⟩ : syracuseStep 3575353 = 2681515) B2681515
theorem B3970043 : Blo 1044610 3970043 := bstep (se 1 (by rfl) ⟨2977532, by rfl⟩ : syracuseStep 3970043 = 5955065) B5955065
theorem B3347675 : Blo 1044610 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B11900195 : Blo 1044610 11900195 := bstep (se 1 (by rfl) ⟨8925146, by rfl⟩ : syracuseStep 11900195 = 17850293) B17850293
theorem B5805431 : Blo 1044610 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B3970529 : Blo 1044610 3970529 := bstep (se 2 (by rfl) ⟨1488948, by rfl⟩ : syracuseStep 3970529 = 2977897) B2977897
theorem B6363137 : Blo 1044610 6363137 := bstep (se 2 (by rfl) ⟨2386176, by rfl⟩ : syracuseStep 6363137 = 4772353) B4772353
theorem B3774523 : Blo 1044610 3774523 := bstep (se 1 (by rfl) ⟨2830892, by rfl⟩ : syracuseStep 3774523 = 5661785) B5661785
theorem B14325821 : Blo 1044610 14325821 := bstep (se 3 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 14325821 = 5372183) B5372183
theorem B3971227 : Blo 1044610 3971227 := bstep (se 1 (by rfl) ⟨2978420, by rfl⟩ : syracuseStep 3971227 = 5956841) B5956841
theorem B18094691 : Blo 1044610 18094691 := bstep (se 1 (by rfl) ⟨13571018, by rfl⟩ : syracuseStep 18094691 = 27142037) B27142037
theorem B6364307 : Blo 1044610 6364307 := bstep (se 1 (by rfl) ⟨4773230, by rfl⟩ : syracuseStep 6364307 = 9546461) B9546461
theorem B3349687 : Blo 1044610 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B2235995 : Blo 1044610 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B21503677 : Blo 1044610 21503677 := bstep (se 3 (by rfl) ⟨4031939, by rfl⟩ : syracuseStep 21503677 = 8063879) B8063879
theorem B3776311 : Blo 1044610 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B14327675 : Blo 1044610 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B3350443 : Blo 1044610 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B11903111 : Blo 1044610 11903111 := bstep (se 1 (by rfl) ⟨8927333, by rfl⟩ : syracuseStep 11903111 = 17854667) B17854667
theorem B1679591 : Blo 1044610 1679591 := bstep (se 1 (by rfl) ⟨1259693, by rfl⟩ : syracuseStep 1679591 = 2519387) B2519387
theorem B5022071 : Blo 1044610 5022071 := bstep (se 1 (by rfl) ⟨3766553, by rfl⟩ : syracuseStep 5022071 = 7533107) B7533107
theorem B12919499 : Blo 1044610 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B6366107 : Blo 1044610 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B19113193 : Blo 1044610 19113193 := bstep (se 2 (by rfl) ⟨7167447, by rfl⟩ : syracuseStep 19113193 = 14334895) B14334895
theorem B25470247 : Blo 1044610 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B2238455 : Blo 1044610 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B1256671 : Blo 1044610 1256671 := bstep (se 1 (by rfl) ⟨942503, by rfl⟩ : syracuseStep 1256671 = 1885007) B1885007
theorem B13413761 : Blo 1044610 13413761 := bstep (se 2 (by rfl) ⟨5030160, by rfl⟩ : syracuseStep 13413761 = 10060321) B10060321
theorem B4468931 : Blo 1044610 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1061095 : Blo 1044610 1061095 := bstep (se 1 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 1061095 = 1591643) B1591643
theorem B12103937 : Blo 1044610 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B11645327 : Blo 1044610 11645327 := bstep (se 1 (by rfl) ⟨8733995, by rfl⟩ : syracuseStep 11645327 = 17467991) B17467991
theorem B5026319 : Blo 1044610 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B10892531 : Blo 1044610 10892531 := bstep (se 1 (by rfl) ⟨8169398, by rfl⟩ : syracuseStep 10892531 = 16338797) B16338797
theorem B2864609 : Blo 1044610 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B6370973 : Blo 1044610 6370973 := bstep (se 3 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 6370973 = 2389115) B2389115
theorem B16103123 : Blo 1044610 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B3979003 : Blo 1044610 3979003 := bstep (se 1 (by rfl) ⟨2984252, by rfl⟩ : syracuseStep 3979003 = 5968505) B5968505
theorem B1324831 : Blo 1044610 1324831 := bstep (se 1 (by rfl) ⟨993623, by rfl⟩ : syracuseStep 1324831 = 1987247) B1987247
theorem B5289947 : Blo 1044610 5289947 := bstep (se 1 (by rfl) ⟨3967460, by rfl⟩ : syracuseStep 5289947 = 7934921) B7934921
theorem B9091177 : Blo 1044610 9091177 := bstep (se 2 (by rfl) ⟨3409191, by rfl⟩ : syracuseStep 9091177 = 6818383) B6818383
theorem B1489051 : Blo 1044610 1489051 := bstep (se 1 (by rfl) ⟨1116788, by rfl⟩ : syracuseStep 1489051 = 2233577) B2233577
theorem B152779445 : Blo 1044610 152779445 := bstep (se 5 (by rfl) ⟨7161536, by rfl⟩ : syracuseStep 152779445 = 14323073) B14323073
theorem B4471631 : Blo 1044610 4471631 := bstep (se 1 (by rfl) ⟨3353723, by rfl⟩ : syracuseStep 4471631 = 6707447) B6707447
theorem B1489871 : Blo 1044610 1489871 := bstep (se 1 (by rfl) ⟨1117403, by rfl⟩ : syracuseStep 1489871 = 2234807) B2234807
theorem B1326127 : Blo 1044610 1326127 := bstep (se 1 (by rfl) ⟨994595, by rfl⟩ : syracuseStep 1326127 = 1989191) B1989191
theorem B8928427 : Blo 1044610 8928427 := bstep (se 1 (by rfl) ⟨6696320, by rfl⟩ : syracuseStep 8928427 = 13392641) B13392641
theorem B22593167 : Blo 1044610 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B24199019 : Blo 1044610 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B10731473 : Blo 1044610 10731473 := bstep (se 2 (by rfl) ⟨4024302, by rfl⟩ : syracuseStep 10731473 = 8048605) B8048605
theorem B6701089 : Blo 1044610 6701089 := bstep (se 2 (by rfl) ⟨2512908, by rfl⟩ : syracuseStep 6701089 = 5025817) B5025817
theorem B1884379 : Blo 1044610 1884379 := bstep (se 1 (by rfl) ⟨1413284, by rfl⟩ : syracuseStep 1884379 = 2826569) B2826569
theorem B7946585 : Blo 1044610 7946585 := bstep (se 2 (by rfl) ⟨2979969, by rfl⟩ : syracuseStep 7946585 = 5959939) B5959939
theorem B27181403 : Blo 1044610 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B5292539 : Blo 1044610 5292539 := bstep (se 1 (by rfl) ⟨3969404, by rfl⟩ : syracuseStep 5292539 = 7938809) B7938809
theorem B4473407 : Blo 1044610 4473407 := bstep (se 1 (by rfl) ⟨3355055, by rfl⟩ : syracuseStep 4473407 = 6710111) B6710111
theorem B9552953 : Blo 1044610 9552953 := bstep (se 2 (by rfl) ⟨3582357, by rfl⟩ : syracuseStep 9552953 = 7164715) B7164715
theorem B25413419 : Blo 1044610 25413419 := bstep (se 1 (by rfl) ⟨19060064, by rfl⟩ : syracuseStep 25413419 = 38120129) B38120129
theorem B27510961 : Blo 1044610 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B3394049 : Blo 1044610 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B5294807 : Blo 1044610 5294807 := bstep (se 1 (by rfl) ⟨3971105, by rfl⟩ : syracuseStep 5294807 = 7942211) B7942211
theorem B7949015 : Blo 1044610 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B1887031 : Blo 1044610 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B28691587 : Blo 1044610 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B3525767 : Blo 1044610 3525767 := bstep (se 1 (by rfl) ⟨2644325, by rfl⟩ : syracuseStep 3525767 = 5288651) B5288651
theorem B3525875 : Blo 1044610 3525875 := bstep (se 1 (by rfl) ⟨2644406, by rfl⟩ : syracuseStep 3525875 = 5288813) B5288813
theorem B1986943 : Blo 1044610 1986943 := bstep (se 1 (by rfl) ⟨1490207, by rfl⟩ : syracuseStep 1986943 = 2980415) B2980415
theorem B2118305 : Blo 1044610 2118305 := bstep (se 2 (by rfl) ⟨794364, by rfl⟩ : syracuseStep 2118305 = 1588729) B1588729
theorem B12899017 : Blo 1044610 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B8934137 : Blo 1044610 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B3527549 : Blo 1044610 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B11916233 : Blo 1044610 11916233 := bstep (se 2 (by rfl) ⟨4468587, by rfl⟩ : syracuseStep 11916233 = 8937175) B8937175
theorem B3527819 : Blo 1044610 3527819 := bstep (se 1 (by rfl) ⟨2645864, by rfl⟩ : syracuseStep 3527819 = 5291729) B5291729
theorem B43604099 : Blo 1044610 43604099 := bstep (se 1 (by rfl) ⟨32703074, by rfl⟩ : syracuseStep 43604099 = 65406149) B65406149
theorem B6707393 : Blo 1044610 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B8476915 : Blo 1044610 8476915 := bstep (se 1 (by rfl) ⟨6357686, by rfl⟩ : syracuseStep 8476915 = 12715373) B12715373
theorem B2644265 : Blo 1044610 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B11917691 : Blo 1044610 11917691 := bstep (se 1 (by rfl) ⟨8938268, by rfl⟩ : syracuseStep 11917691 = 17876537) B17876537
theorem B3529439 : Blo 1044610 3529439 := bstep (se 1 (by rfl) ⟨2647079, by rfl⟩ : syracuseStep 3529439 = 5294159) B5294159
theorem B5299181 : Blo 1044610 5299181 := bstep (se 3 (by rfl) ⟨993596, by rfl⟩ : syracuseStep 5299181 = 1987193) B1987193
theorem B7953389 : Blo 1044610 7953389 := bstep (se 3 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 7953389 = 2982521) B2982521
theorem B26860733 : Blo 1044610 26860733 := bstep (se 3 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 26860733 = 10072775) B10072775
theorem B2645257 : Blo 1044610 2645257 := bstep (se 2 (by rfl) ⟨991971, by rfl⟩ : syracuseStep 2645257 = 1983943) B1983943
theorem B2350547 : Blo 1044610 2350547 := bstep (se 1 (by rfl) ⟨1762910, by rfl⟩ : syracuseStep 2350547 = 3525821) B3525821
theorem B3530195 : Blo 1044610 3530195 := bstep (se 1 (by rfl) ⟨2647646, by rfl⟩ : syracuseStep 3530195 = 5295293) B5295293
theorem B2350817 : Blo 1044610 2350817 := bstep (se 2 (by rfl) ⟨881556, by rfl⟩ : syracuseStep 2350817 = 1763113) B1763113
theorem B3530465 : Blo 1044610 3530465 := bstep (se 2 (by rfl) ⟨1323924, by rfl⟩ : syracuseStep 3530465 = 2647849) B2647849
theorem B5299991 : Blo 1044610 5299991 := bstep (se 1 (by rfl) ⟨3974993, by rfl⟩ : syracuseStep 5299991 = 7949987) B7949987
theorem B5955383 : Blo 1044610 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B2514811 : Blo 1044610 2514811 := bstep (se 1 (by rfl) ⟨1886108, by rfl⟩ : syracuseStep 2514811 = 3772217) B3772217
theorem B15098501 : Blo 1044610 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B5039003 : Blo 1044610 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B2352491 : Blo 1044610 2352491 := bstep (se 1 (by rfl) ⟨1764368, by rfl⟩ : syracuseStep 2352491 = 3528737) B3528737
theorem B3532139 : Blo 1044610 3532139 := bstep (se 1 (by rfl) ⟨2649104, by rfl⟩ : syracuseStep 3532139 = 5298209) B5298209
theorem B5301611 : Blo 1044610 5301611 := bstep (se 1 (by rfl) ⟨3976208, by rfl⟩ : syracuseStep 5301611 = 7952417) B7952417
theorem B7955819 : Blo 1044610 7955819 := bstep (se 1 (by rfl) ⟨5966864, by rfl⟩ : syracuseStep 7955819 = 11933729) B11933729
theorem B3532247 : Blo 1044610 3532247 := bstep (se 1 (by rfl) ⟨2649185, by rfl⟩ : syracuseStep 3532247 = 5298371) B5298371
theorem B2352761 : Blo 1044610 2352761 := bstep (se 2 (by rfl) ⟨882285, by rfl⟩ : syracuseStep 2352761 = 1764571) B1764571
theorem B3532409 : Blo 1044610 3532409 := bstep (se 2 (by rfl) ⟨1324653, by rfl⟩ : syracuseStep 3532409 = 2649307) B2649307
theorem B1763039 : Blo 1044610 1763039 := bstep (se 1 (by rfl) ⟨1322279, by rfl⟩ : syracuseStep 1763039 = 2644559) B2644559
theorem B2975687 : Blo 1044610 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B2975869 : Blo 1044610 2975869 := bstep (se 3 (by rfl) ⟨557975, by rfl⟩ : syracuseStep 2975869 = 1115951) B1115951
theorem B1763471 : Blo 1044610 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B1566953 : Blo 1044610 1566953 := bstep (se 2 (by rfl) ⟨587607, by rfl⟩ : syracuseStep 1566953 = 1175215) B1175215
theorem B73361699 : Blo 1044610 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B1763707 : Blo 1044610 1763707 := bstep (se 1 (by rfl) ⟨1322780, by rfl⟩ : syracuseStep 1763707 = 2645561) B2645561
theorem B6810113 : Blo 1044610 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B1567259 : Blo 1044610 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B1567337 : Blo 1044610 1567337 := bstep (se 2 (by rfl) ⟨587751, by rfl⟩ : syracuseStep 1567337 = 1175503) B1175503
theorem B2353769 : Blo 1044610 2353769 := bstep (se 2 (by rfl) ⟨882663, by rfl⟩ : syracuseStep 2353769 = 1765327) B1765327
theorem B1763977 : Blo 1044610 1763977 := bstep (se 2 (by rfl) ⟨661491, by rfl⟩ : syracuseStep 1763977 = 1322983) B1322983
theorem B2976439 : Blo 1044610 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B6974351 : Blo 1044610 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B3533921 : Blo 1044610 3533921 := bstep (se 2 (by rfl) ⟨1325220, by rfl⟩ : syracuseStep 3533921 = 2650441) B2650441
theorem B5303393 : Blo 1044610 5303393 := bstep (se 2 (by rfl) ⟨1988772, by rfl⟩ : syracuseStep 5303393 = 3977545) B3977545
theorem B1567865 : Blo 1044610 1567865 := bstep (se 2 (by rfl) ⟨587949, by rfl⟩ : syracuseStep 1567865 = 1175899) B1175899
theorem B15068339 : Blo 1044610 15068339 := bstep (se 1 (by rfl) ⟨11301254, by rfl⟩ : syracuseStep 15068339 = 22602509) B22602509
theorem B1567967 : Blo 1044610 1567967 := bstep (se 1 (by rfl) ⟨1175975, by rfl⟩ : syracuseStep 1567967 = 2351951) B2351951
theorem B2354399 : Blo 1044610 2354399 := bstep (se 1 (by rfl) ⟨1765799, by rfl⟩ : syracuseStep 2354399 = 3531599) B3531599
theorem B1568009 : Blo 1044610 1568009 := bstep (se 2 (by rfl) ⟨588003, by rfl⟩ : syracuseStep 1568009 = 1176007) B1176007
theorem B24472907 : Blo 1044610 24472907 := bstep (se 1 (by rfl) ⟨18354680, by rfl⟩ : syracuseStep 24472907 = 36709361) B36709361
theorem B1568111 : Blo 1044610 1568111 := bstep (se 1 (by rfl) ⟨1176083, by rfl⟩ : syracuseStep 1568111 = 2352167) B2352167
theorem B15068567 : Blo 1044610 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B2354615 : Blo 1044610 2354615 := bstep (se 1 (by rfl) ⟨1765961, by rfl⟩ : syracuseStep 2354615 = 3531923) B3531923
theorem B1568231 : Blo 1044610 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B1568363 : Blo 1044610 1568363 := bstep (se 1 (by rfl) ⟨1176272, by rfl⟩ : syracuseStep 1568363 = 2352545) B2352545
theorem B2354795 : Blo 1044610 2354795 := bstep (se 1 (by rfl) ⟨1766096, by rfl⟩ : syracuseStep 2354795 = 3532193) B3532193
theorem B3534461 : Blo 1044610 3534461 := bstep (se 3 (by rfl) ⟨662711, by rfl⟩ : syracuseStep 3534461 = 1325423) B1325423
theorem B1568489 : Blo 1044610 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B2977555 : Blo 1044610 2977555 := bstep (se 1 (by rfl) ⟨2233166, by rfl⟩ : syracuseStep 2977555 = 4466333) B4466333
theorem B20148011 : Blo 1044610 20148011 := bstep (se 1 (by rfl) ⟨15111008, by rfl⟩ : syracuseStep 20148011 = 30222017) B30222017
theorem B1568633 : Blo 1044610 1568633 := bstep (se 2 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 1568633 = 1176475) B1176475
theorem B2355065 : Blo 1044610 2355065 := bstep (se 2 (by rfl) ⟨883149, by rfl⟩ : syracuseStep 2355065 = 1766299) B1766299
theorem B3534731 : Blo 1044610 3534731 := bstep (se 1 (by rfl) ⟨2651048, by rfl⟩ : syracuseStep 3534731 = 5302097) B5302097
theorem B5304203 : Blo 1044610 5304203 := bstep (se 1 (by rfl) ⟨3978152, by rfl⟩ : syracuseStep 5304203 = 7956305) B7956305
theorem B1568735 : Blo 1044610 1568735 := bstep (se 1 (by rfl) ⟨1176551, by rfl⟩ : syracuseStep 1568735 = 2353103) B2353103
theorem B1568987 : Blo 1044610 1568987 := bstep (se 1 (by rfl) ⟨1176740, by rfl⟩ : syracuseStep 1568987 = 2353481) B2353481
theorem B1044711 : Blo 1044610 1044711 := bstep (se 1 (by rfl) ⟨783533, by rfl⟩ : syracuseStep 1044711 = 1567067) B1567067
theorem B1568999 : Blo 1044610 1568999 := bstep (se 1 (by rfl) ⟨1176749, by rfl⟩ : syracuseStep 1568999 = 2353499) B2353499
theorem B4780343 : Blo 1044610 4780343 := bstep (se 1 (by rfl) ⟨3585257, by rfl⟩ : syracuseStep 4780343 = 7170515) B7170515
theorem B1044863 : Blo 1044610 1044863 := bstep (se 1 (by rfl) ⟨783647, by rfl⟩ : syracuseStep 1044863 = 1567295) B1567295
theorem B1175935 : Blo 1044610 1175935 := bstep (se 1 (by rfl) ⟨881951, by rfl⟩ : syracuseStep 1175935 = 1763903) B1763903
theorem B1765759 : Blo 1044610 1765759 := bstep (se 1 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 1765759 = 2648639) B2648639
theorem B1569161 : Blo 1044610 1569161 := bstep (se 2 (by rfl) ⟨588435, by rfl⟩ : syracuseStep 1569161 = 1176871) B1176871
theorem B3535271 : Blo 1044610 3535271 := bstep (se 1 (by rfl) ⟨2651453, by rfl⟩ : syracuseStep 3535271 = 5302907) B5302907
theorem B1044943 : Blo 1044610 1044943 := bstep (se 1 (by rfl) ⟨783707, by rfl⟩ : syracuseStep 1044943 = 1567415) B1567415
theorem B2650583 : Blo 1044610 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B1569257 : Blo 1044610 1569257 := bstep (se 2 (by rfl) ⟨588471, by rfl⟩ : syracuseStep 1569257 = 1176943) B1176943
theorem B1045095 : Blo 1044610 1045095 := bstep (se 1 (by rfl) ⟨783821, by rfl⟩ : syracuseStep 1045095 = 1567643) B1567643
theorem B1569383 : Blo 1044610 1569383 := bstep (se 1 (by rfl) ⟨1177037, by rfl⟩ : syracuseStep 1569383 = 2354075) B2354075
theorem B1569515 : Blo 1044610 1569515 := bstep (se 1 (by rfl) ⟨1177136, by rfl⟩ : syracuseStep 1569515 = 2354273) B2354273
theorem B1569545 : Blo 1044610 1569545 := bstep (se 2 (by rfl) ⟨588579, by rfl⟩ : syracuseStep 1569545 = 1177159) B1177159
theorem B1766191 : Blo 1044610 1766191 := bstep (se 1 (by rfl) ⟨1324643, by rfl⟩ : syracuseStep 1766191 = 2649287) B2649287
theorem B1045359 : Blo 1044610 1045359 := bstep (se 1 (by rfl) ⟨784019, by rfl⟩ : syracuseStep 1045359 = 1568039) B1568039
theorem B1569647 : Blo 1044610 1569647 := bstep (se 1 (by rfl) ⟨1177235, by rfl⟩ : syracuseStep 1569647 = 2354471) B2354471
theorem B1045415 : Blo 1044610 1045415 := bstep (se 1 (by rfl) ⟨784061, by rfl⟩ : syracuseStep 1045415 = 1568123) B1568123
theorem B1045499 : Blo 1044610 1045499 := bstep (se 1 (by rfl) ⟨784124, by rfl⟩ : syracuseStep 1045499 = 1568249) B1568249
theorem B1045567 : Blo 1044610 1045567 := bstep (se 1 (by rfl) ⟨784175, by rfl⟩ : syracuseStep 1045567 = 1568351) B1568351
theorem B1569899 : Blo 1044610 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B1045711 : Blo 1044610 1045711 := bstep (se 1 (by rfl) ⟨784283, by rfl⟩ : syracuseStep 1045711 = 1568567) B1568567
theorem B5305661 : Blo 1044610 5305661 := bstep (se 3 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 5305661 = 1989623) B1989623
theorem B1570139 : Blo 1044610 1570139 := bstep (se 1 (by rfl) ⟨1177604, by rfl⟩ : syracuseStep 1570139 = 2355209) B2355209
theorem B1045915 : Blo 1044610 1045915 := bstep (se 1 (by rfl) ⟨784436, by rfl⟩ : syracuseStep 1045915 = 1568873) B1568873
theorem B1046127 : Blo 1044610 1046127 := bstep (se 1 (by rfl) ⟨784595, by rfl⟩ : syracuseStep 1046127 = 1569191) B1569191
theorem B1570415 : Blo 1044610 1570415 := bstep (se 1 (by rfl) ⟨1177811, by rfl⟩ : syracuseStep 1570415 = 2355623) B2355623
theorem B1046183 : Blo 1044610 1046183 := bstep (se 1 (by rfl) ⟨784637, by rfl⟩ : syracuseStep 1046183 = 1569275) B1569275
theorem B1570487 : Blo 1044610 1570487 := bstep (se 1 (by rfl) ⟨1177865, by rfl⟩ : syracuseStep 1570487 = 2355731) B2355731
theorem B2356919 : Blo 1044610 2356919 := bstep (se 1 (by rfl) ⟨1767689, by rfl⟩ : syracuseStep 2356919 = 3535379) B3535379
theorem B3536567 : Blo 1044610 3536567 := bstep (se 1 (by rfl) ⟨2652425, by rfl⟩ : syracuseStep 3536567 = 5304851) B5304851
theorem B1570523 : Blo 1044610 1570523 := bstep (se 1 (by rfl) ⟨1177892, by rfl⟩ : syracuseStep 1570523 = 2355785) B2355785
theorem B1046267 : Blo 1044610 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B1177339 : Blo 1044610 1177339 := bstep (se 1 (by rfl) ⟨883004, by rfl⟩ : syracuseStep 1177339 = 1766009) B1766009
theorem B1767163 : Blo 1044610 1767163 := bstep (se 1 (by rfl) ⟨1325372, by rfl⟩ : syracuseStep 1767163 = 2650745) B2650745
theorem B2651899 : Blo 1044610 2651899 := bstep (se 1 (by rfl) ⟨1988924, by rfl⟩ : syracuseStep 2651899 = 3977849) B3977849
theorem B1046303 : Blo 1044610 1046303 := bstep (se 1 (by rfl) ⟨784727, by rfl⟩ : syracuseStep 1046303 = 1569455) B1569455
theorem B1177375 : Blo 1044610 1177375 := bstep (se 1 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 1177375 = 1766063) B1766063
theorem B1046335 : Blo 1044610 1046335 := bstep (se 1 (by rfl) ⟨784751, by rfl⟩ : syracuseStep 1046335 = 1569503) B1569503
theorem B1570697 : Blo 1044610 1570697 := bstep (se 2 (by rfl) ⟨589011, by rfl⟩ : syracuseStep 1570697 = 1178023) B1178023
theorem B1767305 : Blo 1044610 1767305 := bstep (se 2 (by rfl) ⟨662739, by rfl⟩ : syracuseStep 1767305 = 1325479) B1325479
theorem B2652041 : Blo 1044610 2652041 := bstep (se 2 (by rfl) ⟨994515, by rfl⟩ : syracuseStep 2652041 = 1989031) B1989031
theorem B7272337 : Blo 1044610 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B1046511 : Blo 1044610 1046511 := bstep (se 1 (by rfl) ⟨784883, by rfl⟩ : syracuseStep 1046511 = 1569767) B1569767
theorem B1570799 : Blo 1044610 1570799 := bstep (se 1 (by rfl) ⟨1178099, by rfl⟩ : syracuseStep 1570799 = 2356199) B2356199
theorem B9566201 : Blo 1044610 9566201 := bstep (se 2 (by rfl) ⟨3587325, by rfl⟩ : syracuseStep 9566201 = 7174651) B7174651
theorem B2117695589 : Blo 1044610 2117695589 := bstep (se 4 (by rfl) ⟨198533961, by rfl⟩ : syracuseStep 2117695589 = 397067923) B397067923
theorem B1046683 : Blo 1044610 1046683 := bstep (se 1 (by rfl) ⟨785012, by rfl⟩ : syracuseStep 1046683 = 1570025) B1570025
theorem B1046719 : Blo 1044610 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B1571051 : Blo 1044610 1571051 := bstep (se 1 (by rfl) ⟨1178288, by rfl⟩ : syracuseStep 1571051 = 2356577) B2356577
theorem B1571111 : Blo 1044610 1571111 := bstep (se 1 (by rfl) ⟨1178333, by rfl⟩ : syracuseStep 1571111 = 2356667) B2356667
theorem B1046831 : Blo 1044610 1046831 := bstep (se 1 (by rfl) ⟨785123, by rfl⟩ : syracuseStep 1046831 = 1570247) B1570247
theorem B1767737 : Blo 1044610 1767737 := bstep (se 2 (by rfl) ⟨662901, by rfl⟩ : syracuseStep 1767737 = 1325803) B1325803
theorem B1571195 : Blo 1044610 1571195 := bstep (se 1 (by rfl) ⟨1178396, by rfl⟩ : syracuseStep 1571195 = 2356793) B2356793
theorem B1047067 : Blo 1044610 1047067 := bstep (se 1 (by rfl) ⟨785300, by rfl⟩ : syracuseStep 1047067 = 1570601) B1570601
theorem B1047071 : Blo 1044610 1047071 := bstep (se 1 (by rfl) ⟨785303, by rfl⟩ : syracuseStep 1047071 = 1570607) B1570607
theorem B13400639 : Blo 1044610 13400639 := bstep (se 1 (by rfl) ⟨10050479, by rfl⟩ : syracuseStep 13400639 = 20100959) B20100959
theorem B1571465 : Blo 1044610 1571465 := bstep (se 2 (by rfl) ⟨589299, by rfl⟩ : syracuseStep 1571465 = 1178599) B1178599
theorem B58161863 : Blo 1044610 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B1571639 : Blo 1044610 1571639 := bstep (se 1 (by rfl) ⟨1178729, by rfl⟩ : syracuseStep 1571639 = 2357459) B2357459
theorem B2390867 : Blo 1044610 2390867 := bstep (se 1 (by rfl) ⟨1793150, by rfl⟩ : syracuseStep 2390867 = 3586301) B3586301
theorem B1047387 : Blo 1044610 1047387 := bstep (se 1 (by rfl) ⟨785540, by rfl⟩ : syracuseStep 1047387 = 1571081) B1571081
theorem B1571675 : Blo 1044610 1571675 := bstep (se 1 (by rfl) ⟨1178756, by rfl⟩ : syracuseStep 1571675 = 2357513) B2357513
theorem B2358107 : Blo 1044610 2358107 := bstep (se 1 (by rfl) ⟨1768580, by rfl⟩ : syracuseStep 2358107 = 3537161) B3537161
theorem B3537755 : Blo 1044610 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B2653033 : Blo 1044610 2653033 := bstep (se 2 (by rfl) ⟨994887, by rfl⟩ : syracuseStep 2653033 = 1989775) B1989775
theorem B1047455 : Blo 1044610 1047455 := bstep (se 1 (by rfl) ⟨785591, by rfl⟩ : syracuseStep 1047455 = 1571183) B1571183
theorem B1178527 : Blo 1044610 1178527 := bstep (se 1 (by rfl) ⟨883895, by rfl⟩ : syracuseStep 1178527 = 1767791) B1767791
theorem B1768351 : Blo 1044610 1768351 := bstep (se 1 (by rfl) ⟨1326263, by rfl⟩ : syracuseStep 1768351 = 2652527) B2652527
theorem B1571819 : Blo 1044610 1571819 := bstep (se 1 (by rfl) ⟨1178864, by rfl⟩ : syracuseStep 1571819 = 2357729) B2357729
theorem B1047599 : Blo 1044610 1047599 := bstep (se 1 (by rfl) ⟨785699, by rfl⟩ : syracuseStep 1047599 = 1571399) B1571399
theorem B1178671 : Blo 1044610 1178671 := bstep (se 1 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 1178671 = 1768007) B1768007
theorem B1047623 : Blo 1044610 1047623 := bstep (se 1 (by rfl) ⟨785717, by rfl⟩ : syracuseStep 1047623 = 1571435) B1571435
theorem B1572023 : Blo 1044610 1572023 := bstep (se 1 (by rfl) ⟨1179017, by rfl⟩ : syracuseStep 1572023 = 2358035) B2358035
theorem B1047775 : Blo 1044610 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B1178959 : Blo 1044610 1178959 := bstep (se 1 (by rfl) ⟨884219, by rfl⟩ : syracuseStep 1178959 = 1768439) B1768439
theorem B1768783 : Blo 1044610 1768783 := bstep (se 1 (by rfl) ⟨1326587, by rfl⟩ : syracuseStep 1768783 = 2653175) B2653175
theorem B1572263 : Blo 1044610 1572263 := bstep (se 1 (by rfl) ⟨1179197, by rfl⟩ : syracuseStep 1572263 = 2358395) B2358395
theorem B1768871 : Blo 1044610 1768871 := bstep (se 1 (by rfl) ⟨1326653, by rfl⟩ : syracuseStep 1768871 = 2653307) B2653307
theorem B15105473 : Blo 1044610 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B1048039 : Blo 1044610 1048039 := bstep (se 1 (by rfl) ⟨786029, by rfl⟩ : syracuseStep 1048039 = 1572059) B1572059
theorem B1572347 : Blo 1044610 1572347 := bstep (se 1 (by rfl) ⟨1179260, by rfl⟩ : syracuseStep 1572347 = 2358521) B2358521
theorem B1769033 : Blo 1044610 1769033 := bstep (se 2 (by rfl) ⟨663387, by rfl⟩ : syracuseStep 1769033 = 1326775) B1326775
theorem B2358863 : Blo 1044610 2358863 := bstep (se 1 (by rfl) ⟨1769147, by rfl⟩ : syracuseStep 2358863 = 3538295) B3538295
theorem B3538511 : Blo 1044610 3538511 := bstep (se 1 (by rfl) ⟨2653883, by rfl⟩ : syracuseStep 3538511 = 5307767) B5307767
theorem B1048155 : Blo 1044610 1048155 := bstep (se 1 (by rfl) ⟨786116, by rfl⟩ : syracuseStep 1048155 = 1572233) B1572233
theorem B1572443 : Blo 1044610 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B3767951 : Blo 1044610 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2981519 : Blo 1044610 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B1572527 : Blo 1044610 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B3538619 : Blo 1044610 3538619 := bstep (se 1 (by rfl) ⟨2653964, by rfl⟩ : syracuseStep 3538619 = 5307929) B5307929
theorem B5308091 : Blo 1044610 5308091 := bstep (se 1 (by rfl) ⟨3981068, by rfl⟩ : syracuseStep 5308091 = 7962137) B7962137
theorem B7536361 : Blo 1044610 7536361 := bstep (se 2 (by rfl) ⟨2826135, by rfl⟩ : syracuseStep 7536361 = 5652271) B5652271
theorem B1572647 : Blo 1044610 1572647 := bstep (se 1 (by rfl) ⟨1179485, by rfl⟩ : syracuseStep 1572647 = 2358971) B2358971
theorem B1048391 : Blo 1044610 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B1179463 : Blo 1044610 1179463 := bstep (se 1 (by rfl) ⟨884597, by rfl⟩ : syracuseStep 1179463 = 1769195) B1769195
theorem B1572731 : Blo 1044610 1572731 := bstep (se 1 (by rfl) ⟨1179548, by rfl⟩ : syracuseStep 1572731 = 2359097) B2359097
theorem B1048543 : Blo 1044610 1048543 := bstep (se 1 (by rfl) ⟨786407, by rfl⟩ : syracuseStep 1048543 = 1572815) B1572815
theorem B18120935 : Blo 1044610 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B2982271 : Blo 1044610 2982271 := bstep (se 1 (by rfl) ⟨2236703, by rfl⟩ : syracuseStep 2982271 = 4473407) B4473407
theorem B19333727 : Blo 1044610 19333727 := bstep (se 1 (by rfl) ⟨14500295, by rfl⟩ : syracuseStep 19333727 = 29000591) B29000591
theorem B16942279 : Blo 1044610 16942279 := bstep (se 1 (by rfl) ⟨12706709, by rfl⟩ : syracuseStep 16942279 = 25413419) B25413419
theorem B3967825 : Blo 1044610 3967825 := bstep (se 2 (by rfl) ⟨1487934, by rfl⟩ : syracuseStep 3967825 = 2975869) B2975869
theorem B1412203 : Blo 1044610 1412203 := bstep (se 1 (by rfl) ⟨1059152, by rfl⟩ : syracuseStep 1412203 = 2118305) B2118305
theorem B2231783 : Blo 1044610 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B7933463 : Blo 1044610 7933463 := bstep (se 1 (by rfl) ⟨5950097, by rfl⟩ : syracuseStep 7933463 = 11900195) B11900195
theorem B3968585 : Blo 1044610 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B3870287 : Blo 1044610 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B29069399 : Blo 1044610 29069399 := bstep (se 1 (by rfl) ⟨21802049, by rfl⟩ : syracuseStep 29069399 = 43604099) B43604099
theorem B1675561 : Blo 1044610 1675561 := bstep (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) B1256671
theorem B12063127 : Blo 1044610 12063127 := bstep (se 1 (by rfl) ⟨9047345, by rfl⟩ : syracuseStep 12063127 = 18094691) B18094691
theorem B3970073 : Blo 1044610 3970073 := bstep (se 2 (by rfl) ⟨1488777, by rfl⟩ : syracuseStep 3970073 = 2977555) B2977555
theorem B3970255 : Blo 1044610 3970255 := bstep (se 1 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 3970255 = 5955383) B5955383
theorem B5969213 : Blo 1044610 5969213 := bstep (se 3 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 5969213 = 2238455) B2238455
theorem B7935407 : Blo 1044610 7935407 := bstep (se 1 (by rfl) ⟨5951555, by rfl⟩ : syracuseStep 7935407 = 11903111) B11903111
theorem B1119727 : Blo 1044610 1119727 := bstep (se 1 (by rfl) ⟨839795, by rfl⟩ : syracuseStep 1119727 = 1679591) B1679591
theorem B3348047 : Blo 1044610 3348047 := bstep (se 1 (by rfl) ⟨2511035, by rfl⟩ : syracuseStep 3348047 = 5022071) B5022071
theorem B1414793 : Blo 1044610 1414793 := bstep (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) B1061095
theorem B10065667 : Blo 1044610 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B9050797 : Blo 1044610 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B18160301 : Blo 1044610 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B3972989 : Blo 1044610 3972989 := bstep (se 3 (by rfl) ⟨744935, by rfl⟩ : syracuseStep 3972989 = 1489871) B1489871
theorem B8069291 : Blo 1044610 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B3186895 : Blo 1044610 3186895 := bstep (se 1 (by rfl) ⟨2390171, by rfl⟩ : syracuseStep 3186895 = 4780343) B4780343
theorem B3350879 : Blo 1044610 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B1909739 : Blo 1044610 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B11904569 : Blo 1044610 11904569 := bstep (se 2 (by rfl) ⟨4464213, by rfl⟩ : syracuseStep 11904569 = 8928427) B8928427
theorem B4466249 : Blo 1044610 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B101852963 : Blo 1044610 101852963 := bstep (se 1 (by rfl) ⟨76389722, by rfl⟩ : syracuseStep 101852963 = 152779445) B152779445
theorem B38774575 : Blo 1044610 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B10070315 : Blo 1044610 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B3353081 : Blo 1044610 3353081 := bstep (se 2 (by rfl) ⟨1257405, by rfl⟩ : syracuseStep 3353081 = 2514811) B2514811
theorem B4467257 : Blo 1044610 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B16132679 : Blo 1044610 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B7154315 : Blo 1044610 7154315 := bstep (se 1 (by rfl) ⟨5365736, by rfl⟩ : syracuseStep 7154315 = 10731473) B10731473
theorem B3976391 : Blo 1044610 3976391 := bstep (se 1 (by rfl) ⟨2982293, by rfl⟩ : syracuseStep 3976391 = 5964587) B5964587
theorem B6368635 : Blo 1044610 6368635 := bstep (se 1 (by rfl) ⟨4776476, by rfl⟩ : syracuseStep 6368635 = 9552953) B9552953
theorem B9547255 : Blo 1044610 9547255 := bstep (se 1 (by rfl) ⟨7160441, by rfl⟩ : syracuseStep 9547255 = 14320883) B14320883
theorem B3976847 : Blo 1044610 3976847 := bstep (se 1 (by rfl) ⟨2982635, by rfl⟩ : syracuseStep 3976847 = 5965271) B5965271
theorem B33960329 : Blo 1044610 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B3978031 : Blo 1044610 3978031 := bstep (se 1 (by rfl) ⟨2983523, by rfl⟩ : syracuseStep 3978031 = 5967047) B5967047
theorem B36681281 : Blo 1044610 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B4241281 : Blo 1044610 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B7944155 : Blo 1044610 7944155 := bstep (se 1 (by rfl) ⟨5958116, by rfl⟩ : syracuseStep 7944155 = 11916233) B11916233
theorem B1488937 : Blo 1044610 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B9550547 : Blo 1044610 9550547 := bstep (se 1 (by rfl) ⟨7162910, by rfl⟩ : syracuseStep 9550547 = 14325821) B14325821
theorem B4471595 : Blo 1044610 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B38255449 : Blo 1044610 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B7945127 : Blo 1044610 7945127 := bstep (se 1 (by rfl) ⟨5958845, by rfl⟩ : syracuseStep 7945127 = 11917691) B11917691
theorem B8043553 : Blo 1044610 8043553 := bstep (se 2 (by rfl) ⟨3016332, by rfl⟩ : syracuseStep 8043553 = 6032665) B6032665
theorem B4767137 : Blo 1044610 4767137 := bstep (se 2 (by rfl) ⟨1787676, by rfl⟩ : syracuseStep 4767137 = 3575353) B3575353
theorem B4242871 : Blo 1044610 4242871 := bstep (se 1 (by rfl) ⟨3182153, by rfl⟩ : syracuseStep 4242871 = 6364307) B6364307
theorem B17907155 : Blo 1044610 17907155 := bstep (se 1 (by rfl) ⟨13430366, by rfl⟩ : syracuseStep 17907155 = 26860733) B26860733
theorem B1490663 : Blo 1044610 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B9551783 : Blo 1044610 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B4244071 : Blo 1044610 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B3359335 : Blo 1044610 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1983791 : Blo 1044610 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B48907799 : Blo 1044610 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B10045559 : Blo 1044610 10045559 := bstep (se 1 (by rfl) ⟨7534169, by rfl⟩ : syracuseStep 10045559 = 15068339) B15068339
theorem B10045711 : Blo 1044610 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B5032697 : Blo 1044610 5032697 := bstep (se 2 (by rfl) ⟨1887261, by rfl⟩ : syracuseStep 5032697 = 3774523) B3774523
theorem B1985401 : Blo 1044610 1985401 := bstep (se 2 (by rfl) ⟨744525, by rfl⟩ : syracuseStep 1985401 = 1489051) B1489051
theorem B5294969 : Blo 1044610 5294969 := bstep (se 2 (by rfl) ⟨1985613, by rfl⟩ : syracuseStep 5294969 = 3971227) B3971227
theorem B7261687 : Blo 1044610 7261687 := bstep (se 1 (by rfl) ⟨5446265, by rfl⟩ : syracuseStep 7261687 = 10892531) B10892531
theorem B4247315 : Blo 1044610 4247315 := bstep (se 1 (by rfl) ⟨3185486, by rfl⟩ : syracuseStep 4247315 = 6370973) B6370973
theorem B10735415 : Blo 1044610 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B3526631 : Blo 1044610 3526631 := bstep (se 1 (by rfl) ⟨2644973, by rfl⟩ : syracuseStep 3526631 = 5289947) B5289947
theorem B6377467 : Blo 1044610 6377467 := bstep (se 1 (by rfl) ⟨4783100, by rfl⟩ : syracuseStep 6377467 = 9566201) B9566201
theorem B1411797059 : Blo 1044610 1411797059 := bstep (se 1 (by rfl) ⟨1058847794, by rfl⟩ : syracuseStep 1411797059 = 2117695589) B2117695589
theorem B20140325 : Blo 1044610 20140325 := bstep (se 4 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 20140325 = 3776311) B3776311
theorem B3527009 : Blo 1044610 3527009 := bstep (se 2 (by rfl) ⟨1322628, by rfl⟩ : syracuseStep 3527009 = 2645257) B2645257
theorem B8933759 : Blo 1044610 8933759 := bstep (se 1 (by rfl) ⟨6700319, by rfl⟩ : syracuseStep 8933759 = 13400639) B13400639
theorem B1593911 : Blo 1044610 1593911 := bstep (se 1 (by rfl) ⟨1195433, by rfl⟩ : syracuseStep 1593911 = 2390867) B2390867
theorem B10048481 : Blo 1044610 10048481 := bstep (se 2 (by rfl) ⟨3768180, by rfl⟩ : syracuseStep 10048481 = 7536361) B7536361
theorem B15062111 : Blo 1044610 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B2511967 : Blo 1044610 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B1987679 : Blo 1044610 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B8934785 : Blo 1044610 8934785 := bstep (se 2 (by rfl) ⟨3350544, by rfl⟩ : syracuseStep 8934785 = 6701089) B6701089
theorem B5297723 : Blo 1044610 5297723 := bstep (se 1 (by rfl) ⟨3973292, by rfl⟩ : syracuseStep 5297723 = 7946585) B7946585
theorem B2512505 : Blo 1044610 2512505 := bstep (se 2 (by rfl) ⟨942189, by rfl⟩ : syracuseStep 2512505 = 1884379) B1884379
theorem B3528359 : Blo 1044610 3528359 := bstep (se 1 (by rfl) ⟨2646269, by rfl⟩ : syracuseStep 3528359 = 5292539) B5292539
theorem B48486277 : Blo 1044610 48486277 := bstep (se 4 (by rfl) ⟨4545588, by rfl⟩ : syracuseStep 48486277 = 9091177) B9091177
theorem B14178887 : Blo 1044610 14178887 := bstep (se 1 (by rfl) ⟨10634165, by rfl⟩ : syracuseStep 14178887 = 21268331) B21268331
theorem B2513735 : Blo 1044610 2513735 := bstep (se 1 (by rfl) ⟨1885301, by rfl⟩ : syracuseStep 2513735 = 3770603) B3770603
theorem B25484257 : Blo 1044610 25484257 := bstep (se 2 (by rfl) ⟨9556596, by rfl⟩ : syracuseStep 25484257 = 19113193) B19113193
theorem B3529871 : Blo 1044610 3529871 := bstep (se 1 (by rfl) ⟨2647403, by rfl⟩ : syracuseStep 3529871 = 5294807) B5294807
theorem B5299343 : Blo 1044610 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B12737807 : Blo 1044610 12737807 := bstep (se 1 (by rfl) ⟨9553355, by rfl⟩ : syracuseStep 12737807 = 19106711) B19106711
theorem B51010955 : Blo 1044610 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B2350511 : Blo 1044610 2350511 := bstep (se 1 (by rfl) ⟨1762883, by rfl⟩ : syracuseStep 2350511 = 3525767) B3525767
theorem B7953875 : Blo 1044610 7953875 := bstep (se 1 (by rfl) ⟨5965406, by rfl⟩ : syracuseStep 7953875 = 11930813) B11930813
theorem B2350583 : Blo 1044610 2350583 := bstep (se 1 (by rfl) ⟨1762937, by rfl⟩ : syracuseStep 2350583 = 3525875) B3525875
theorem B2351609 : Blo 1044610 2351609 := bstep (se 2 (by rfl) ⟨881853, by rfl⟩ : syracuseStep 2351609 = 1763707) B1763707
theorem B5956091 : Blo 1044610 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B2351699 : Blo 1044610 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B2646695 : Blo 1044610 2646695 := bstep (se 1 (by rfl) ⟨1985021, by rfl⟩ : syracuseStep 2646695 = 3970043) B3970043
theorem B2351879 : Blo 1044610 2351879 := bstep (se 1 (by rfl) ⟨1763909, by rfl⟩ : syracuseStep 2351879 = 3527819) B3527819
theorem B2351969 : Blo 1044610 2351969 := bstep (se 2 (by rfl) ⟨881988, by rfl⟩ : syracuseStep 2351969 = 1763977) B1763977
theorem B2647019 : Blo 1044610 2647019 := bstep (se 1 (by rfl) ⟨1985264, by rfl⟩ : syracuseStep 2647019 = 3970529) B3970529
theorem B2516041 : Blo 1044610 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B1762843 : Blo 1044610 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B2352959 : Blo 1044610 2352959 := bstep (se 1 (by rfl) ⟨1764719, by rfl⟩ : syracuseStep 2352959 = 3529439) B3529439
theorem B3532787 : Blo 1044610 3532787 := bstep (se 1 (by rfl) ⟨2649590, by rfl⟩ : syracuseStep 3532787 = 5299181) B5299181
theorem B5302259 : Blo 1044610 5302259 := bstep (se 1 (by rfl) ⟨3976694, by rfl⟩ : syracuseStep 5302259 = 7953389) B7953389
theorem B1567031 : Blo 1044610 1567031 := bstep (se 1 (by rfl) ⟨1175273, by rfl⟩ : syracuseStep 1567031 = 2350547) B2350547
theorem B2353463 : Blo 1044610 2353463 := bstep (se 1 (by rfl) ⟨1765097, by rfl⟩ : syracuseStep 2353463 = 3530195) B3530195
theorem B1567211 : Blo 1044610 1567211 := bstep (se 1 (by rfl) ⟨1175408, by rfl⟩ : syracuseStep 1567211 = 2350817) B2350817
theorem B2353643 : Blo 1044610 2353643 := bstep (se 1 (by rfl) ⟨1765232, by rfl⟩ : syracuseStep 2353643 = 3530465) B3530465
theorem B3533327 : Blo 1044610 3533327 := bstep (se 1 (by rfl) ⟨2649995, by rfl⟩ : syracuseStep 3533327 = 5299991) B5299991
theorem B16968365 : Blo 1044610 16968365 := bstep (se 3 (by rfl) ⟨3181568, by rfl⟩ : syracuseStep 16968365 = 6363137) B6363137
theorem B8612999 : Blo 1044610 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B1567913 : Blo 1044610 1567913 := bstep (se 2 (by rfl) ⟨587967, by rfl⟩ : syracuseStep 1567913 = 1175935) B1175935
theorem B2354345 : Blo 1044610 2354345 := bstep (se 2 (by rfl) ⟨882879, by rfl⟩ : syracuseStep 2354345 = 1765759) B1765759
theorem B2649257 : Blo 1044610 2649257 := bstep (se 2 (by rfl) ⟨993471, by rfl⟩ : syracuseStep 2649257 = 1986943) B1986943
theorem B1568327 : Blo 1044610 1568327 := bstep (se 1 (by rfl) ⟨1176245, by rfl⟩ : syracuseStep 1568327 = 2352491) B2352491
theorem B2354759 : Blo 1044610 2354759 := bstep (se 1 (by rfl) ⟨1766069, by rfl⟩ : syracuseStep 2354759 = 3532139) B3532139
theorem B3534407 : Blo 1044610 3534407 := bstep (se 1 (by rfl) ⟨2650805, by rfl⟩ : syracuseStep 3534407 = 5301611) B5301611
theorem B5303879 : Blo 1044610 5303879 := bstep (se 1 (by rfl) ⟨3977909, by rfl⟩ : syracuseStep 5303879 = 7955819) B7955819
theorem B17198689 : Blo 1044610 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B2354831 : Blo 1044610 2354831 := bstep (se 1 (by rfl) ⟨1766123, by rfl⟩ : syracuseStep 2354831 = 3532247) B3532247
theorem B2354921 : Blo 1044610 2354921 := bstep (se 2 (by rfl) ⟨883095, by rfl⟩ : syracuseStep 2354921 = 1766191) B1766191
theorem B1568507 : Blo 1044610 1568507 := bstep (se 1 (by rfl) ⟨1176380, by rfl⟩ : syracuseStep 1568507 = 2352761) B2352761
theorem B2354939 : Blo 1044610 2354939 := bstep (se 1 (by rfl) ⟨1766204, by rfl⟩ : syracuseStep 2354939 = 3532409) B3532409
theorem B1175359 : Blo 1044610 1175359 := bstep (se 1 (by rfl) ⟨881519, by rfl⟩ : syracuseStep 1175359 = 1763039) B1763039
theorem B1175647 : Blo 1044610 1175647 := bstep (se 1 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 1175647 = 1763471) B1763471
theorem B1044635 : Blo 1044610 1044635 := bstep (se 1 (by rfl) ⟨783476, by rfl⟩ : syracuseStep 1044635 = 1566953) B1566953
theorem B1044839 : Blo 1044610 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B1044891 : Blo 1044610 1044891 := bstep (se 1 (by rfl) ⟨783668, by rfl⟩ : syracuseStep 1044891 = 1567337) B1567337
theorem B1569179 : Blo 1044610 1569179 := bstep (se 1 (by rfl) ⟨1176884, by rfl⟩ : syracuseStep 1569179 = 2353769) B2353769
theorem B4649567 : Blo 1044610 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B2355947 : Blo 1044610 2355947 := bstep (se 1 (by rfl) ⟨1766960, by rfl⟩ : syracuseStep 2355947 = 3533921) B3533921
theorem B3535595 : Blo 1044610 3535595 := bstep (se 1 (by rfl) ⟨2651696, by rfl⟩ : syracuseStep 3535595 = 5303393) B5303393
theorem B1045243 : Blo 1044610 1045243 := bstep (se 1 (by rfl) ⟨783932, by rfl⟩ : syracuseStep 1045243 = 1567865) B1567865
theorem B1045311 : Blo 1044610 1045311 := bstep (se 1 (by rfl) ⟨783983, by rfl⟩ : syracuseStep 1045311 = 1567967) B1567967
theorem B1569599 : Blo 1044610 1569599 := bstep (se 1 (by rfl) ⟨1177199, by rfl⟩ : syracuseStep 1569599 = 2354399) B2354399
theorem B1045339 : Blo 1044610 1045339 := bstep (se 1 (by rfl) ⟨784004, by rfl⟩ : syracuseStep 1045339 = 1568009) B1568009
theorem B16315271 : Blo 1044610 16315271 := bstep (se 1 (by rfl) ⟨12236453, by rfl⟩ : syracuseStep 16315271 = 24472907) B24472907
theorem B1045407 : Blo 1044610 1045407 := bstep (se 1 (by rfl) ⟨784055, by rfl⟩ : syracuseStep 1045407 = 1568111) B1568111
theorem B8942507 : Blo 1044610 8942507 := bstep (se 1 (by rfl) ⟨6706880, by rfl⟩ : syracuseStep 8942507 = 13413761) B13413761
theorem B1569743 : Blo 1044610 1569743 := bstep (se 1 (by rfl) ⟨1177307, by rfl⟩ : syracuseStep 1569743 = 2354615) B2354615
theorem B1045487 : Blo 1044610 1045487 := bstep (se 1 (by rfl) ⟨784115, by rfl⟩ : syracuseStep 1045487 = 1568231) B1568231
theorem B1569785 : Blo 1044610 1569785 := bstep (se 2 (by rfl) ⟨588669, by rfl⟩ : syracuseStep 1569785 = 1177339) B1177339
theorem B2356217 : Blo 1044610 2356217 := bstep (se 2 (by rfl) ⟨883581, by rfl⟩ : syracuseStep 2356217 = 1767163) B1767163
theorem B3535865 : Blo 1044610 3535865 := bstep (se 2 (by rfl) ⟨1325949, by rfl⟩ : syracuseStep 3535865 = 2651899) B2651899
theorem B5305337 : Blo 1044610 5305337 := bstep (se 2 (by rfl) ⟨1989501, by rfl⟩ : syracuseStep 5305337 = 3979003) B3979003
theorem B1569833 : Blo 1044610 1569833 := bstep (se 2 (by rfl) ⟨588687, by rfl⟩ : syracuseStep 1569833 = 1177375) B1177375
theorem B1766441 : Blo 1044610 1766441 := bstep (se 2 (by rfl) ⟨662415, by rfl⟩ : syracuseStep 1766441 = 1324831) B1324831
theorem B1045575 : Blo 1044610 1045575 := bstep (se 1 (by rfl) ⟨784181, by rfl⟩ : syracuseStep 1045575 = 1568363) B1568363
theorem B1569863 : Blo 1044610 1569863 := bstep (se 1 (by rfl) ⟨1177397, by rfl⟩ : syracuseStep 1569863 = 2354795) B2354795
theorem B2356307 : Blo 1044610 2356307 := bstep (se 1 (by rfl) ⟨1767230, by rfl⟩ : syracuseStep 2356307 = 3534461) B3534461
theorem B1045659 : Blo 1044610 1045659 := bstep (se 1 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 1045659 = 1568489) B1568489
theorem B9696449 : Blo 1044610 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B13432007 : Blo 1044610 13432007 := bstep (se 1 (by rfl) ⟨10074005, by rfl⟩ : syracuseStep 13432007 = 20148011) B20148011
theorem B1045755 : Blo 1044610 1045755 := bstep (se 1 (by rfl) ⟨784316, by rfl⟩ : syracuseStep 1045755 = 1568633) B1568633
theorem B1570043 : Blo 1044610 1570043 := bstep (se 1 (by rfl) ⟨1177532, by rfl⟩ : syracuseStep 1570043 = 2355065) B2355065
theorem B2356487 : Blo 1044610 2356487 := bstep (se 1 (by rfl) ⟨1767365, by rfl⟩ : syracuseStep 2356487 = 3534731) B3534731
theorem B3536135 : Blo 1044610 3536135 := bstep (se 1 (by rfl) ⟨2652101, by rfl⟩ : syracuseStep 3536135 = 5304203) B5304203
theorem B1045823 : Blo 1044610 1045823 := bstep (se 1 (by rfl) ⟨784367, by rfl⟩ : syracuseStep 1045823 = 1568735) B1568735
theorem B2979287 : Blo 1044610 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1045991 : Blo 1044610 1045991 := bstep (se 1 (by rfl) ⟨784493, by rfl⟩ : syracuseStep 1045991 = 1568987) B1568987
theorem B1045999 : Blo 1044610 1045999 := bstep (se 1 (by rfl) ⟨784499, by rfl⟩ : syracuseStep 1045999 = 1568999) B1568999
theorem B1046107 : Blo 1044610 1046107 := bstep (se 1 (by rfl) ⟨784580, by rfl⟩ : syracuseStep 1046107 = 1569161) B1569161
theorem B7763551 : Blo 1044610 7763551 := bstep (se 1 (by rfl) ⟨5822663, by rfl⟩ : syracuseStep 7763551 = 11645327) B11645327
theorem B2356847 : Blo 1044610 2356847 := bstep (se 1 (by rfl) ⟨1767635, by rfl⟩ : syracuseStep 2356847 = 3535271) B3535271
theorem B1767055 : Blo 1044610 1767055 := bstep (se 1 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 1767055 = 2650583) B2650583
theorem B11302553 : Blo 1044610 11302553 := bstep (se 2 (by rfl) ⟨4238457, by rfl⟩ : syracuseStep 11302553 = 8476915) B8476915
theorem B1046171 : Blo 1044610 1046171 := bstep (se 1 (by rfl) ⟨784628, by rfl⟩ : syracuseStep 1046171 = 1569257) B1569257
theorem B1046255 : Blo 1044610 1046255 := bstep (se 1 (by rfl) ⟨784691, by rfl⟩ : syracuseStep 1046255 = 1569383) B1569383
theorem B1046343 : Blo 1044610 1046343 := bstep (se 1 (by rfl) ⟨784757, by rfl⟩ : syracuseStep 1046343 = 1569515) B1569515
theorem B1046363 : Blo 1044610 1046363 := bstep (se 1 (by rfl) ⟨784772, by rfl⟩ : syracuseStep 1046363 = 1569545) B1569545
theorem B1046431 : Blo 1044610 1046431 := bstep (se 1 (by rfl) ⟨784823, by rfl⟩ : syracuseStep 1046431 = 1569647) B1569647
theorem B1046599 : Blo 1044610 1046599 := bstep (se 1 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 1046599 = 1569899) B1569899
theorem B3537107 : Blo 1044610 3537107 := bstep (se 1 (by rfl) ⟨2652830, by rfl⟩ : syracuseStep 3537107 = 5305661) B5305661
theorem B1046759 : Blo 1044610 1046759 := bstep (se 1 (by rfl) ⟨785069, by rfl⟩ : syracuseStep 1046759 = 1570139) B1570139
theorem B1046943 : Blo 1044610 1046943 := bstep (se 1 (by rfl) ⟨785207, by rfl⟩ : syracuseStep 1046943 = 1570415) B1570415
theorem B1046991 : Blo 1044610 1046991 := bstep (se 1 (by rfl) ⟨785243, by rfl⟩ : syracuseStep 1046991 = 1570487) B1570487
theorem B1571279 : Blo 1044610 1571279 := bstep (se 1 (by rfl) ⟨1178459, by rfl⟩ : syracuseStep 1571279 = 2356919) B2356919
theorem B2357711 : Blo 1044610 2357711 := bstep (se 1 (by rfl) ⟨1768283, by rfl⟩ : syracuseStep 2357711 = 3536567) B3536567
theorem B3537377 : Blo 1044610 3537377 := bstep (se 2 (by rfl) ⟨1326516, by rfl⟩ : syracuseStep 3537377 = 2653033) B2653033
theorem B1047015 : Blo 1044610 1047015 := bstep (se 1 (by rfl) ⟨785261, by rfl⟩ : syracuseStep 1047015 = 1570523) B1570523
theorem B1571369 : Blo 1044610 1571369 := bstep (se 2 (by rfl) ⟨589263, by rfl⟩ : syracuseStep 1571369 = 1178527) B1178527
theorem B2357801 : Blo 1044610 2357801 := bstep (se 2 (by rfl) ⟨884175, by rfl⟩ : syracuseStep 2357801 = 1768351) B1768351
theorem B1047131 : Blo 1044610 1047131 := bstep (se 1 (by rfl) ⟨785348, by rfl⟩ : syracuseStep 1047131 = 1570697) B1570697
theorem B1178203 : Blo 1044610 1178203 := bstep (se 1 (by rfl) ⟨883652, by rfl⟩ : syracuseStep 1178203 = 1767305) B1767305
theorem B1768027 : Blo 1044610 1768027 := bstep (se 1 (by rfl) ⟨1326020, by rfl⟩ : syracuseStep 1768027 = 2652041) B2652041
theorem B1047199 : Blo 1044610 1047199 := bstep (se 1 (by rfl) ⟨785399, by rfl⟩ : syracuseStep 1047199 = 1570799) B1570799
theorem B1571561 : Blo 1044610 1571561 := bstep (se 2 (by rfl) ⟨589335, by rfl⟩ : syracuseStep 1571561 = 1178671) B1178671
theorem B1768169 : Blo 1044610 1768169 := bstep (se 2 (by rfl) ⟨663063, by rfl⟩ : syracuseStep 1768169 = 1326127) B1326127
theorem B1047367 : Blo 1044610 1047367 := bstep (se 1 (by rfl) ⟨785525, by rfl⟩ : syracuseStep 1047367 = 1571051) B1571051
theorem B1047407 : Blo 1044610 1047407 := bstep (se 1 (by rfl) ⟨785555, by rfl⟩ : syracuseStep 1047407 = 1571111) B1571111
theorem B1178491 : Blo 1044610 1178491 := bstep (se 1 (by rfl) ⟨883868, by rfl⟩ : syracuseStep 1178491 = 1767737) B1767737
theorem B1047463 : Blo 1044610 1047463 := bstep (se 1 (by rfl) ⟨785597, by rfl⟩ : syracuseStep 1047463 = 1571195) B1571195
theorem B1047643 : Blo 1044610 1047643 := bstep (se 1 (by rfl) ⟨785732, by rfl⟩ : syracuseStep 1047643 = 1571465) B1571465
theorem B1571945 : Blo 1044610 1571945 := bstep (se 2 (by rfl) ⟨589479, by rfl⟩ : syracuseStep 1571945 = 1178959) B1178959
theorem B2358377 : Blo 1044610 2358377 := bstep (se 2 (by rfl) ⟨884391, by rfl⟩ : syracuseStep 2358377 = 1768783) B1768783
theorem B1047759 : Blo 1044610 1047759 := bstep (se 1 (by rfl) ⟨785819, by rfl⟩ : syracuseStep 1047759 = 1571639) B1571639
theorem B2981087 : Blo 1044610 2981087 := bstep (se 1 (by rfl) ⟨2235815, by rfl⟩ : syracuseStep 2981087 = 4471631) B4471631
theorem B1047783 : Blo 1044610 1047783 := bstep (se 1 (by rfl) ⟨785837, by rfl⟩ : syracuseStep 1047783 = 1571675) B1571675
theorem B1572071 : Blo 1044610 1572071 := bstep (se 1 (by rfl) ⟨1179053, by rfl⟩ : syracuseStep 1572071 = 2358107) B2358107
theorem B2358503 : Blo 1044610 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B1047879 : Blo 1044610 1047879 := bstep (se 1 (by rfl) ⟨785909, by rfl⟩ : syracuseStep 1047879 = 1571819) B1571819
theorem B1048015 : Blo 1044610 1048015 := bstep (se 1 (by rfl) ⟨786011, by rfl⟩ : syracuseStep 1048015 = 1572023) B1572023
theorem B28671569 : Blo 1044610 28671569 := bstep (se 2 (by rfl) ⟨10751838, by rfl⟩ : syracuseStep 28671569 = 21503677) B21503677
theorem B1048175 : Blo 1044610 1048175 := bstep (se 1 (by rfl) ⟨786131, by rfl⟩ : syracuseStep 1048175 = 1572263) B1572263
theorem B1179247 : Blo 1044610 1179247 := bstep (se 1 (by rfl) ⟨884435, by rfl⟩ : syracuseStep 1179247 = 1768871) B1768871
theorem B1048231 : Blo 1044610 1048231 := bstep (se 1 (by rfl) ⟨786173, by rfl⟩ : syracuseStep 1048231 = 1572347) B1572347
theorem B1179355 : Blo 1044610 1179355 := bstep (se 1 (by rfl) ⟨884516, by rfl⟩ : syracuseStep 1179355 = 1769033) B1769033
theorem B1572575 : Blo 1044610 1572575 := bstep (se 1 (by rfl) ⟨1179431, by rfl⟩ : syracuseStep 1572575 = 2358863) B2358863
theorem B2359007 : Blo 1044610 2359007 := bstep (se 1 (by rfl) ⟨1769255, by rfl⟩ : syracuseStep 2359007 = 3538511) B3538511
theorem B1048295 : Blo 1044610 1048295 := bstep (se 1 (by rfl) ⟨786221, by rfl⟩ : syracuseStep 1048295 = 1572443) B1572443
theorem B1572617 : Blo 1044610 1572617 := bstep (se 2 (by rfl) ⟨589731, by rfl⟩ : syracuseStep 1572617 = 1179463) B1179463
theorem B1048351 : Blo 1044610 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B2359079 : Blo 1044610 2359079 := bstep (se 1 (by rfl) ⟨1769309, by rfl⟩ : syracuseStep 2359079 = 3538619) B3538619
theorem B3538727 : Blo 1044610 3538727 := bstep (se 1 (by rfl) ⟨2654045, by rfl⟩ : syracuseStep 3538727 = 5308091) B5308091
theorem B1048431 : Blo 1044610 1048431 := bstep (se 1 (by rfl) ⟨786323, by rfl⟩ : syracuseStep 1048431 = 1572647) B1572647
theorem B1048487 : Blo 1044610 1048487 := bstep (se 1 (by rfl) ⟨786365, by rfl⟩ : syracuseStep 1048487 = 1572731) B1572731
theorem B32605199 : Blo 1044610 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B941198039 : Blo 1044610 941198039 := bstep (se 1 (by rfl) ⟨705898529, by rfl⟩ : syracuseStep 941198039 = 1411797059) B1411797059
theorem B25857197 : Blo 1044610 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B48270917 : Blo 1044610 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B2232031 : Blo 1044610 2232031 := bstep (se 1 (by rfl) ⟨1674023, by rfl⟩ : syracuseStep 2232031 = 3348047) B3348047
theorem B1675003 : Blo 1044610 1675003 := bstep (se 1 (by rfl) ⟨1256252, by rfl⟩ : syracuseStep 1675003 = 2512505) B2512505
theorem B3772781 : Blo 1044610 3772781 := bstep (se 3 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 3772781 = 1414793) B1414793
theorem B8491513 : Blo 1044610 8491513 := bstep (se 2 (by rfl) ⟨3184317, by rfl⟩ : syracuseStep 8491513 = 6368635) B6368635
theorem B1675823 : Blo 1044610 1675823 := bstep (se 1 (by rfl) ⟨1256867, by rfl⟩ : syracuseStep 1675823 = 2513735) B2513735
theorem B8491871 : Blo 1044610 8491871 := bstep (se 1 (by rfl) ⟨6368903, by rfl⟩ : syracuseStep 8491871 = 12737807) B12737807
theorem B5379527 : Blo 1044610 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B2233919 : Blo 1044610 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B3970727 : Blo 1044610 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B2234081 : Blo 1044610 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B7936379 : Blo 1044610 7936379 := bstep (se 1 (by rfl) ⟨5952284, by rfl⟩ : syracuseStep 7936379 = 11904569) B11904569
theorem B67901975 : Blo 1044610 67901975 := bstep (se 1 (by rfl) ⟨50926481, by rfl⟩ : syracuseStep 67901975 = 101852963) B101852963
theorem B3349289 : Blo 1044610 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B10755119 : Blo 1044610 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B11312243 : Blo 1044610 11312243 := bstep (se 1 (by rfl) ⟨8484182, by rfl⟩ : syracuseStep 11312243 = 16968365) B16968365
theorem B5741999 : Blo 1044610 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B5971877 : Blo 1044610 5971877 := bstep (se 4 (by rfl) ⟨559863, by rfl⟩ : syracuseStep 5971877 = 1119727) B1119727
theorem B8954671 : Blo 1044610 8954671 := bstep (se 1 (by rfl) ⟨6716003, by rfl⟩ : syracuseStep 8954671 = 13432007) B13432007
theorem B24454187 : Blo 1044610 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B10724737 : Blo 1044610 10724737 := bstep (se 2 (by rfl) ⟨4021776, by rfl⟩ : syracuseStep 10724737 = 8043553) B8043553
theorem B6367031 : Blo 1044610 6367031 := bstep (se 1 (by rfl) ⟨4775273, by rfl⟩ : syracuseStep 6367031 = 9550547) B9550547
theorem B3975101 : Blo 1044610 3975101 := bstep (se 3 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 3975101 = 1490663) B1490663
theorem B11938103 : Blo 1044610 11938103 := bstep (se 1 (by rfl) ⟨8953577, by rfl⟩ : syracuseStep 11938103 = 17907155) B17907155
theorem B19114379 : Blo 1044610 19114379 := bstep (se 1 (by rfl) ⟨14335784, by rfl⟩ : syracuseStep 19114379 = 28671569) B28671569
theorem B25471421 : Blo 1044610 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B12889151 : Blo 1044610 12889151 := bstep (se 1 (by rfl) ⟨9666863, by rfl⟩ : syracuseStep 12889151 = 19333727) B19333727
theorem B3976361 : Blo 1044610 3976361 := bstep (se 2 (by rfl) ⟨1491135, by rfl⟩ : syracuseStep 3976361 = 2982271) B2982271
theorem B6697039 : Blo 1044610 6697039 := bstep (se 1 (by rfl) ⟨5022779, by rfl⟩ : syracuseStep 6697039 = 10045559) B10045559
theorem B12398845 : Blo 1044610 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B22589705 : Blo 1044610 22589705 := bstep (se 2 (by rfl) ⟨8471139, by rfl⟩ : syracuseStep 22589705 = 16942279) B16942279
theorem B165622421 : Blo 1044610 165622421 := bstep (se 6 (by rfl) ⟨3881775, by rfl⟩ : syracuseStep 165622421 = 7763551) B7763551
theorem B1487855 : Blo 1044610 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B5288975 : Blo 1044610 5288975 := bstep (se 1 (by rfl) ⟨3966731, by rfl⟩ : syracuseStep 5288975 = 7933463) B7933463
theorem B2831543 : Blo 1044610 2831543 := bstep (se 1 (by rfl) ⟨2123657, by rfl⟩ : syracuseStep 2831543 = 4247315) B4247315
theorem B7156943 : Blo 1044610 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B1062607 : Blo 1044610 1062607 := bstep (se 1 (by rfl) ⟨796955, by rfl⟩ : syracuseStep 1062607 = 1593911) B1593911
theorem B6698987 : Blo 1044610 6698987 := bstep (se 1 (by rfl) ⟨5024240, by rfl⟩ : syracuseStep 6698987 = 10048481) B10048481
theorem B10041407 : Blo 1044610 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B5290109 : Blo 1044610 5290109 := bstep (se 3 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 5290109 = 1983791) B1983791
theorem B3979475 : Blo 1044610 3979475 := bstep (se 1 (by rfl) ⟨2984606, by rfl⟩ : syracuseStep 3979475 = 5969213) B5969213
theorem B5290271 : Blo 1044610 5290271 := bstep (se 1 (by rfl) ⟨3967703, by rfl⟩ : syracuseStep 5290271 = 7935407) B7935407
theorem B5290433 : Blo 1044610 5290433 := bstep (se 2 (by rfl) ⟨1983912, by rfl⟩ : syracuseStep 5290433 = 3967825) B3967825
theorem B1882937 : Blo 1044610 1882937 := bstep (se 2 (by rfl) ⟨706101, by rfl⟩ : syracuseStep 1882937 = 1412203) B1412203
theorem B9452591 : Blo 1044610 9452591 := bstep (se 1 (by rfl) ⟨7089443, by rfl⟩ : syracuseStep 9452591 = 14178887) B14178887
theorem B12106867 : Blo 1044610 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B12729673 : Blo 1044610 12729673 := bstep (se 2 (by rfl) ⟨4773627, by rfl⟩ : syracuseStep 12729673 = 9547255) B9547255
theorem B9682249 : Blo 1044610 9682249 := bstep (se 2 (by rfl) ⟨3630843, by rfl⟩ : syracuseStep 9682249 = 7261687) B7261687
theorem B8503289 : Blo 1044610 8503289 := bstep (se 2 (by rfl) ⟨3188733, by rfl⟩ : syracuseStep 8503289 = 6377467) B6377467
theorem B13418885 : Blo 1044610 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B5293673 : Blo 1044610 5293673 := bstep (se 2 (by rfl) ⟨1985127, by rfl⟩ : syracuseStep 5293673 = 3970255) B3970255
theorem B4769543 : Blo 1044610 4769543 := bstep (se 1 (by rfl) ⟨3577157, by rfl⟩ : syracuseStep 4769543 = 7154315) B7154315
theorem B13420525 : Blo 1044610 13420525 := bstep (se 3 (by rfl) ⟨2516348, by rfl⟩ : syracuseStep 13420525 = 5032697) B5032697
theorem B13420889 : Blo 1044610 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B5655041 : Blo 1044610 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B1985249 : Blo 1044610 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B1986191 : Blo 1044610 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B51007265 : Blo 1044610 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B5296103 : Blo 1044610 5296103 := bstep (se 1 (by rfl) ⟨3972077, by rfl⟩ : syracuseStep 5296103 = 7944155) B7944155
theorem B5657161 : Blo 1044610 5657161 := bstep (se 2 (by rfl) ⟨2121435, by rfl⟩ : syracuseStep 5657161 = 4242871) B4242871
theorem B5296751 : Blo 1044610 5296751 := bstep (se 1 (by rfl) ⟨3972563, by rfl⟩ : syracuseStep 5296751 = 7945127) B7945127
theorem B258593477 : Blo 1044610 258593477 := bstep (se 4 (by rfl) ⟨24243138, by rfl⟩ : syracuseStep 258593477 = 48486277) B48486277
theorem B1987391 : Blo 1044610 1987391 := bstep (se 1 (by rfl) ⟨1490543, by rfl⟩ : syracuseStep 1987391 = 2981087) B2981087
theorem B12080623 : Blo 1044610 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B77518397 : Blo 1044610 77518397 := bstep (se 3 (by rfl) ⟨14534699, by rfl⟩ : syracuseStep 77518397 = 29069399) B29069399
theorem B4249193 : Blo 1044610 4249193 := bstep (se 2 (by rfl) ⟨1593447, by rfl⟩ : syracuseStep 4249193 = 3186895) B3186895
theorem B5658761 : Blo 1044610 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B4479113 : Blo 1044610 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B3529979 : Blo 1044610 3529979 := bstep (se 1 (by rfl) ⟨2647484, by rfl⟩ : syracuseStep 3529979 = 5294969) B5294969
theorem B2350457 : Blo 1044610 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B2645723 : Blo 1044610 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B2580191 : Blo 1044610 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B51699433 : Blo 1044610 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B2351087 : Blo 1044610 2351087 := bstep (se 1 (by rfl) ⟨1763315, by rfl⟩ : syracuseStep 2351087 = 3526631) B3526631
theorem B13426883 : Blo 1044610 13426883 := bstep (se 1 (by rfl) ⟨10070162, by rfl⟩ : syracuseStep 13426883 = 20140325) B20140325
theorem B2351339 : Blo 1044610 2351339 := bstep (se 1 (by rfl) ⟨1763504, by rfl⟩ : syracuseStep 2351339 = 3527009) B3527009
theorem B5955839 : Blo 1044610 5955839 := bstep (se 1 (by rfl) ⟨4466879, by rfl⟩ : syracuseStep 5955839 = 8933759) B8933759
theorem B5300477 : Blo 1044610 5300477 := bstep (se 3 (by rfl) ⟨993839, by rfl⟩ : syracuseStep 5300477 = 1987679) B1987679
theorem B13394281 : Blo 1044610 13394281 := bstep (se 2 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 13394281 = 10045711) B10045711
theorem B2646715 : Blo 1044610 2646715 := bstep (se 1 (by rfl) ⟨1985036, by rfl⟩ : syracuseStep 2646715 = 3970073) B3970073
theorem B5956523 : Blo 1044610 5956523 := bstep (se 1 (by rfl) ⟨4467392, by rfl⟩ : syracuseStep 5956523 = 8934785) B8934785
theorem B3531815 : Blo 1044610 3531815 := bstep (se 1 (by rfl) ⟨2648861, by rfl⟩ : syracuseStep 3531815 = 5297723) B5297723
theorem B2352239 : Blo 1044610 2352239 := bstep (se 1 (by rfl) ⟨1764179, by rfl⟩ : syracuseStep 2352239 = 3528359) B3528359
theorem B2647201 : Blo 1044610 2647201 := bstep (se 2 (by rfl) ⟨992700, by rfl⟩ : syracuseStep 2647201 = 1985401) B1985401
theorem B2353247 : Blo 1044610 2353247 := bstep (se 1 (by rfl) ⟨1764935, by rfl⟩ : syracuseStep 2353247 = 3529871) B3529871
theorem B3532895 : Blo 1044610 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B22931585 : Blo 1044610 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B34007303 : Blo 1044610 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B1567007 : Blo 1044610 1567007 := bstep (se 1 (by rfl) ⟨1175255, by rfl⟩ : syracuseStep 1567007 = 2350511) B2350511
theorem B5302583 : Blo 1044610 5302583 := bstep (se 1 (by rfl) ⟨3976937, by rfl⟩ : syracuseStep 5302583 = 7953875) B7953875
theorem B1567055 : Blo 1044610 1567055 := bstep (se 1 (by rfl) ⟨1175291, by rfl⟩ : syracuseStep 1567055 = 2350583) B2350583
theorem B1567145 : Blo 1044610 1567145 := bstep (se 2 (by rfl) ⟨587679, by rfl⟩ : syracuseStep 1567145 = 1175359) B1175359
theorem B2648659 : Blo 1044610 2648659 := bstep (se 1 (by rfl) ⟨1986494, by rfl⟩ : syracuseStep 2648659 = 3972989) B3972989
theorem B1567529 : Blo 1044610 1567529 := bstep (se 2 (by rfl) ⟨587823, by rfl⟩ : syracuseStep 1567529 = 1175647) B1175647
theorem B1567739 : Blo 1044610 1567739 := bstep (se 1 (by rfl) ⟨1175804, by rfl⟩ : syracuseStep 1567739 = 2351609) B2351609
theorem B1567799 : Blo 1044610 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B1764463 : Blo 1044610 1764463 := bstep (se 1 (by rfl) ⟨1323347, by rfl⟩ : syracuseStep 1764463 = 2646695) B2646695
theorem B1567919 : Blo 1044610 1567919 := bstep (se 1 (by rfl) ⟨1175939, by rfl⟩ : syracuseStep 1567919 = 2351879) B2351879
theorem B16084169 : Blo 1044610 16084169 := bstep (se 2 (by rfl) ⟨6031563, by rfl⟩ : syracuseStep 16084169 = 12063127) B12063127
theorem B1567979 : Blo 1044610 1567979 := bstep (se 1 (by rfl) ⟨1175984, by rfl⟩ : syracuseStep 1567979 = 2351969) B2351969
theorem B1273159 : Blo 1044610 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B1764679 : Blo 1044610 1764679 := bstep (se 1 (by rfl) ⟨1323509, by rfl⟩ : syracuseStep 1764679 = 2647019) B2647019
theorem B2977499 : Blo 1044610 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B5304041 : Blo 1044610 5304041 := bstep (se 2 (by rfl) ⟨1989015, by rfl⟩ : syracuseStep 5304041 = 3978031) B3978031
theorem B1568639 : Blo 1044610 1568639 := bstep (se 1 (by rfl) ⟨1176479, by rfl⟩ : syracuseStep 1568639 = 2352959) B2352959
theorem B8941549 : Blo 1044610 8941549 := bstep (se 3 (by rfl) ⟨1676540, by rfl⟩ : syracuseStep 8941549 = 3353081) B3353081
theorem B2355191 : Blo 1044610 2355191 := bstep (se 1 (by rfl) ⟨1766393, by rfl⟩ : syracuseStep 2355191 = 3532787) B3532787
theorem B3534839 : Blo 1044610 3534839 := bstep (se 1 (by rfl) ⟨2651129, by rfl⟩ : syracuseStep 3534839 = 5302259) B5302259
theorem B6713543 : Blo 1044610 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B1044687 : Blo 1044610 1044687 := bstep (se 1 (by rfl) ⟨783515, by rfl⟩ : syracuseStep 1044687 = 1567031) B1567031
theorem B1568975 : Blo 1044610 1568975 := bstep (se 1 (by rfl) ⟨1176731, by rfl⟩ : syracuseStep 1568975 = 2353463) B2353463
theorem B1044807 : Blo 1044610 1044807 := bstep (se 1 (by rfl) ⟨783605, by rfl⟩ : syracuseStep 1044807 = 1567211) B1567211
theorem B1569095 : Blo 1044610 1569095 := bstep (se 1 (by rfl) ⟨1176821, by rfl⟩ : syracuseStep 1569095 = 2353643) B2353643
theorem B2355551 : Blo 1044610 2355551 := bstep (se 1 (by rfl) ⟨1766663, by rfl⟩ : syracuseStep 2355551 = 3533327) B3533327
theorem B2978171 : Blo 1044610 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B1045275 : Blo 1044610 1045275 := bstep (se 1 (by rfl) ⟨783956, by rfl⟩ : syracuseStep 1045275 = 1567913) B1567913
theorem B1569563 : Blo 1044610 1569563 := bstep (se 1 (by rfl) ⟨1177172, by rfl⟩ : syracuseStep 1569563 = 2354345) B2354345
theorem B1766171 : Blo 1044610 1766171 := bstep (se 1 (by rfl) ⟨1324628, by rfl⟩ : syracuseStep 1766171 = 2649257) B2649257
theorem B2650927 : Blo 1044610 2650927 := bstep (se 1 (by rfl) ⟨1988195, by rfl⟩ : syracuseStep 2650927 = 3976391) B3976391
theorem B2356073 : Blo 1044610 2356073 := bstep (se 2 (by rfl) ⟨883527, by rfl⟩ : syracuseStep 2356073 = 1767055) B1767055
theorem B1045551 : Blo 1044610 1045551 := bstep (se 1 (by rfl) ⟨784163, by rfl⟩ : syracuseStep 1045551 = 1568327) B1568327
theorem B1569839 : Blo 1044610 1569839 := bstep (se 1 (by rfl) ⟨1177379, by rfl⟩ : syracuseStep 1569839 = 2354759) B2354759
theorem B2356271 : Blo 1044610 2356271 := bstep (se 1 (by rfl) ⟨1767203, by rfl⟩ : syracuseStep 2356271 = 3534407) B3534407
theorem B3535919 : Blo 1044610 3535919 := bstep (se 1 (by rfl) ⟨2651939, by rfl⟩ : syracuseStep 3535919 = 5303879) B5303879
theorem B2651231 : Blo 1044610 2651231 := bstep (se 1 (by rfl) ⟨1988423, by rfl⟩ : syracuseStep 2651231 = 3976847) B3976847
theorem B1569887 : Blo 1044610 1569887 := bstep (se 1 (by rfl) ⟨1177415, by rfl⟩ : syracuseStep 1569887 = 2354831) B2354831
theorem B1569947 : Blo 1044610 1569947 := bstep (se 1 (by rfl) ⟨1177460, by rfl⟩ : syracuseStep 1569947 = 2354921) B2354921
theorem B1045671 : Blo 1044610 1045671 := bstep (se 1 (by rfl) ⟨784253, by rfl⟩ : syracuseStep 1045671 = 1568507) B1568507
theorem B1569959 : Blo 1044610 1569959 := bstep (se 1 (by rfl) ⟨1177469, by rfl⟩ : syracuseStep 1569959 = 2354939) B2354939
theorem B22640219 : Blo 1044610 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B1046119 : Blo 1044610 1046119 := bstep (se 1 (by rfl) ⟨784589, by rfl⟩ : syracuseStep 1046119 = 1569179) B1569179
theorem B1570631 : Blo 1044610 1570631 := bstep (se 1 (by rfl) ⟨1177973, by rfl⟩ : syracuseStep 1570631 = 2355947) B2355947
theorem B2357063 : Blo 1044610 2357063 := bstep (se 1 (by rfl) ⟨1767797, by rfl⟩ : syracuseStep 2357063 = 3535595) B3535595
theorem B1046399 : Blo 1044610 1046399 := bstep (se 1 (by rfl) ⟨784799, by rfl⟩ : syracuseStep 1046399 = 1569599) B1569599
theorem B10876847 : Blo 1044610 10876847 := bstep (se 1 (by rfl) ⟨8157635, by rfl⟩ : syracuseStep 10876847 = 16315271) B16315271
theorem B5961671 : Blo 1044610 5961671 := bstep (se 1 (by rfl) ⟨4471253, by rfl⟩ : syracuseStep 5961671 = 8942507) B8942507
theorem B1046495 : Blo 1044610 1046495 := bstep (se 1 (by rfl) ⟨784871, by rfl⟩ : syracuseStep 1046495 = 1569743) B1569743
theorem B1046523 : Blo 1044610 1046523 := bstep (se 1 (by rfl) ⟨784892, by rfl⟩ : syracuseStep 1046523 = 1569785) B1569785
theorem B1570811 : Blo 1044610 1570811 := bstep (se 1 (by rfl) ⟨1178108, by rfl⟩ : syracuseStep 1570811 = 2356217) B2356217
theorem B2357243 : Blo 1044610 2357243 := bstep (se 1 (by rfl) ⟨1767932, by rfl⟩ : syracuseStep 2357243 = 3535865) B3535865
theorem B3536891 : Blo 1044610 3536891 := bstep (se 1 (by rfl) ⟨2652668, by rfl⟩ : syracuseStep 3536891 = 5305337) B5305337
theorem B1046555 : Blo 1044610 1046555 := bstep (se 1 (by rfl) ⟨784916, by rfl⟩ : syracuseStep 1046555 = 1569833) B1569833
theorem B1177627 : Blo 1044610 1177627 := bstep (se 1 (by rfl) ⟨883220, by rfl⟩ : syracuseStep 1177627 = 1766441) B1766441
theorem B1046575 : Blo 1044610 1046575 := bstep (se 1 (by rfl) ⟨784931, by rfl⟩ : syracuseStep 1046575 = 1569863) B1569863
theorem B1570871 : Blo 1044610 1570871 := bstep (se 1 (by rfl) ⟨1178153, by rfl⟩ : syracuseStep 1570871 = 2356307) B2356307
theorem B1570937 : Blo 1044610 1570937 := bstep (se 2 (by rfl) ⟨589101, by rfl⟩ : syracuseStep 1570937 = 1178203) B1178203
theorem B2357369 : Blo 1044610 2357369 := bstep (se 2 (by rfl) ⟨884013, by rfl⟩ : syracuseStep 2357369 = 1768027) B1768027
theorem B1046695 : Blo 1044610 1046695 := bstep (se 1 (by rfl) ⟨785021, by rfl⟩ : syracuseStep 1046695 = 1570043) B1570043
theorem B1570991 : Blo 1044610 1570991 := bstep (se 1 (by rfl) ⟨1178243, by rfl⟩ : syracuseStep 1570991 = 2356487) B2356487
theorem B2357423 : Blo 1044610 2357423 := bstep (se 1 (by rfl) ⟨1768067, by rfl⟩ : syracuseStep 2357423 = 3536135) B3536135
theorem B1571231 : Blo 1044610 1571231 := bstep (se 1 (by rfl) ⟨1178423, by rfl⟩ : syracuseStep 1571231 = 2356847) B2356847
theorem B7535035 : Blo 1044610 7535035 := bstep (se 1 (by rfl) ⟨5651276, by rfl⟩ : syracuseStep 7535035 = 11302553) B11302553
theorem B1571321 : Blo 1044610 1571321 := bstep (se 2 (by rfl) ⟨589245, by rfl⟩ : syracuseStep 1571321 = 1178491) B1178491
theorem B33979009 : Blo 1044610 33979009 := bstep (se 2 (by rfl) ⟨12742128, by rfl⟩ : syracuseStep 33979009 = 25484257) B25484257
theorem B2358071 : Blo 1044610 2358071 := bstep (se 1 (by rfl) ⟨1768553, by rfl⟩ : syracuseStep 2358071 = 3537107) B3537107
theorem B1047519 : Blo 1044610 1047519 := bstep (se 1 (by rfl) ⟨785639, by rfl⟩ : syracuseStep 1047519 = 1571279) B1571279
theorem B1571807 : Blo 1044610 1571807 := bstep (se 1 (by rfl) ⟨1178855, by rfl⟩ : syracuseStep 1571807 = 2357711) B2357711
theorem B2358251 : Blo 1044610 2358251 := bstep (se 1 (by rfl) ⟨1768688, by rfl⟩ : syracuseStep 2358251 = 3537377) B3537377
theorem B1047579 : Blo 1044610 1047579 := bstep (se 1 (by rfl) ⟨785684, by rfl⟩ : syracuseStep 1047579 = 1571369) B1571369
theorem B1571867 : Blo 1044610 1571867 := bstep (se 1 (by rfl) ⟨1178900, by rfl⟩ : syracuseStep 1571867 = 2357801) B2357801
theorem B1047707 : Blo 1044610 1047707 := bstep (se 1 (by rfl) ⟨785780, by rfl⟩ : syracuseStep 1047707 = 1571561) B1571561
theorem B1178779 : Blo 1044610 1178779 := bstep (se 1 (by rfl) ⟨884084, by rfl⟩ : syracuseStep 1178779 = 1768169) B1768169
theorem B2981063 : Blo 1044610 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B1047963 : Blo 1044610 1047963 := bstep (se 1 (by rfl) ⟨785972, by rfl⟩ : syracuseStep 1047963 = 1571945) B1571945
theorem B1572251 : Blo 1044610 1572251 := bstep (se 1 (by rfl) ⟨1179188, by rfl⟩ : syracuseStep 1572251 = 2358377) B2358377
theorem B1572329 : Blo 1044610 1572329 := bstep (se 2 (by rfl) ⟨589623, by rfl⟩ : syracuseStep 1572329 = 1179247) B1179247
theorem B1048047 : Blo 1044610 1048047 := bstep (se 1 (by rfl) ⟨786035, by rfl⟩ : syracuseStep 1048047 = 1572071) B1572071
theorem B1572335 : Blo 1044610 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B3178091 : Blo 1044610 3178091 := bstep (se 1 (by rfl) ⟨2383568, by rfl⟩ : syracuseStep 3178091 = 4767137) B4767137
theorem B1572473 : Blo 1044610 1572473 := bstep (se 2 (by rfl) ⟨589677, by rfl⟩ : syracuseStep 1572473 = 1179355) B1179355
theorem B1048383 : Blo 1044610 1048383 := bstep (se 1 (by rfl) ⟨786287, by rfl⟩ : syracuseStep 1048383 = 1572575) B1572575
theorem B1572671 : Blo 1044610 1572671 := bstep (se 1 (by rfl) ⟨1179503, by rfl⟩ : syracuseStep 1572671 = 2359007) B2359007
theorem B1048411 : Blo 1044610 1048411 := bstep (se 1 (by rfl) ⟨786308, by rfl⟩ : syracuseStep 1048411 = 1572617) B1572617
theorem B1572719 : Blo 1044610 1572719 := bstep (se 1 (by rfl) ⟨1179539, by rfl⟩ : syracuseStep 1572719 = 2359079) B2359079
theorem B2359151 : Blo 1044610 2359151 := bstep (se 1 (by rfl) ⟨1769363, by rfl⟩ : syracuseStep 2359151 = 3538727) B3538727
theorem B8945923 : Blo 1044610 8945923 := bstep (se 1 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 8945923 = 13418885) B13418885
theorem B17859041 : Blo 1044610 17859041 := bstep (se 2 (by rfl) ⟨6697140, by rfl⟩ : syracuseStep 17859041 = 13394281) B13394281
theorem B3179695 : Blo 1044610 3179695 := bstep (se 1 (by rfl) ⟨2384771, by rfl⟩ : syracuseStep 3179695 = 4769543) B4769543
theorem B8947259 : Blo 1044610 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B3770027 : Blo 1044610 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B17238131 : Blo 1044610 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B3967613 : Blo 1044610 3967613 := bstep (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) B1487855
theorem B17894033 : Blo 1044610 17894033 := bstep (se 2 (by rfl) ⟨6710262, by rfl⟩ : syracuseStep 17894033 = 13420525) B13420525
theorem B51678931 : Blo 1044610 51678931 := bstep (se 1 (by rfl) ⟨38759198, by rfl⟩ : syracuseStep 51678931 = 77518397) B77518397
theorem B3772507 : Blo 1044610 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B2986075 : Blo 1044610 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B2232859 : Blo 1044610 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B7541495 : Blo 1044610 7541495 := bstep (se 1 (by rfl) ⟨5656121, by rfl⟩ : syracuseStep 7541495 = 11312243) B11312243
theorem B2233337 : Blo 1044610 2233337 := bstep (se 2 (by rfl) ⟨837501, by rfl⟩ : syracuseStep 2233337 = 1675003) B1675003
theorem B29004925 : Blo 1044610 29004925 := bstep (se 3 (by rfl) ⟨5438423, by rfl⟩ : syracuseStep 29004925 = 10876847) B10876847
theorem B8951255 : Blo 1044610 8951255 := bstep (se 1 (by rfl) ⟨6713441, by rfl⟩ : syracuseStep 8951255 = 13426883) B13426883
theorem B3970559 : Blo 1044610 3970559 := bstep (se 1 (by rfl) ⟨2977919, by rfl⟩ : syracuseStep 3970559 = 5955839) B5955839
theorem B3971015 : Blo 1044610 3971015 := bstep (se 1 (by rfl) ⟨2978261, by rfl⟩ : syracuseStep 3971015 = 5956523) B5956523
theorem B7542881 : Blo 1044610 7542881 := bstep (se 2 (by rfl) ⟨2828580, by rfl⟩ : syracuseStep 7542881 = 5657161) B5657161
theorem B16980947 : Blo 1044610 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B8592767 : Blo 1044610 8592767 := bstep (se 1 (by rfl) ⟨6444575, by rfl⟩ : syracuseStep 8592767 = 12889151) B12889151
theorem B10722779 : Blo 1044610 10722779 := bstep (se 1 (by rfl) ⟨8042084, by rfl⟩ : syracuseStep 10722779 = 16084169) B16084169
theorem B5021165 : Blo 1044610 5021165 := bstep (se 3 (by rfl) ⟨941468, by rfl⟩ : syracuseStep 5021165 = 1882937) B1882937
theorem B1416809 : Blo 1044610 1416809 := bstep (se 2 (by rfl) ⟨531303, by rfl⟩ : syracuseStep 1416809 = 1062607) B1062607
theorem B28680317 : Blo 1044610 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B3974447 : Blo 1044610 3974447 := bstep (se 1 (by rfl) ⟨2980835, by rfl⟩ : syracuseStep 3974447 = 5961671) B5961671
theorem B4465991 : Blo 1044610 4465991 := bstep (se 1 (by rfl) ⟨3349493, by rfl⟩ : syracuseStep 4465991 = 6698987) B6698987
theorem B6694271 : Blo 1044610 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B128722445 : Blo 1044610 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B6301727 : Blo 1044610 6301727 := bstep (se 1 (by rfl) ⟨4726295, by rfl⟩ : syracuseStep 6301727 = 9452591) B9452591
theorem B17902781 : Blo 1044610 17902781 := bstep (se 3 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 17902781 = 6713543) B6713543
theorem B21736799 : Blo 1044610 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B11939561 : Blo 1044610 11939561 := bstep (se 2 (by rfl) ⟨4477335, by rfl⟩ : syracuseStep 11939561 = 8954671) B8954671
theorem B4468861 : Blo 1044610 4468861 := bstep (se 3 (by rfl) ⟨837911, by rfl⟩ : syracuseStep 4468861 = 1675823) B1675823
theorem B14299649 : Blo 1044610 14299649 := bstep (se 2 (by rfl) ⟨5362368, by rfl⟩ : syracuseStep 14299649 = 10724737) B10724737
theorem B689582605 : Blo 1044610 689582605 := bstep (se 3 (by rfl) ⟨129296738, by rfl⟩ : syracuseStep 689582605 = 258593477) B258593477
theorem B5668859 : Blo 1044610 5668859 := bstep (se 1 (by rfl) ⟨4251644, by rfl⟩ : syracuseStep 5668859 = 8503289) B8503289
theorem B1324127 : Blo 1044610 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B1324927 : Blo 1044610 1324927 := bstep (se 1 (by rfl) ⟨993695, by rfl⟩ : syracuseStep 1324927 = 1987391) B1987391
theorem B1489279 : Blo 1044610 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B5290919 : Blo 1044610 5290919 := bstep (se 1 (by rfl) ⟨3968189, by rfl⟩ : syracuseStep 5290919 = 7936379) B7936379
theorem B45267983 : Blo 1044610 45267983 := bstep (se 1 (by rfl) ⟨33950987, by rfl⟩ : syracuseStep 45267983 = 67901975) B67901975
theorem B1720127 : Blo 1044610 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B3981251 : Blo 1044610 3981251 := bstep (se 1 (by rfl) ⟨2985938, by rfl⟩ : syracuseStep 3981251 = 5971877) B5971877
theorem B8929385 : Blo 1044610 8929385 := bstep (se 2 (by rfl) ⟨3348519, by rfl⟩ : syracuseStep 8929385 = 6697039) B6697039
theorem B16531793 : Blo 1044610 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B11322017 : Blo 1044610 11322017 := bstep (se 2 (by rfl) ⟨4245756, by rfl⟩ : syracuseStep 11322017 = 8491513) B8491513
theorem B16302791 : Blo 1044610 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B4244687 : Blo 1044610 4244687 := bstep (se 1 (by rfl) ⟨3183515, by rfl⟩ : syracuseStep 4244687 = 6367031) B6367031
theorem B15287723 : Blo 1044610 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B5293997 : Blo 1044610 5293997 := bstep (se 3 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 5293997 = 1985249) B1985249
theorem B16107497 : Blo 1044610 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B1984999 : Blo 1044610 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B15059803 : Blo 1044610 15059803 := bstep (se 1 (by rfl) ⟨11294852, by rfl⟩ : syracuseStep 15059803 = 22589705) B22589705
theorem B1985447 : Blo 1044610 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B110414947 : Blo 1044610 110414947 := bstep (se 1 (by rfl) ⟨82811210, by rfl⟩ : syracuseStep 110414947 = 165622421) B165622421
theorem B7949501 : Blo 1044610 7949501 := bstep (se 3 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 7949501 = 2981063) B2981063
theorem B10046713 : Blo 1044610 10046713 := bstep (se 2 (by rfl) ⟨3767517, by rfl⟩ : syracuseStep 10046713 = 7535035) B7535035
theorem B3525983 : Blo 1044610 3525983 := bstep (se 1 (by rfl) ⟨2644487, by rfl⟩ : syracuseStep 3525983 = 5288975) B5288975
theorem B1887695 : Blo 1044610 1887695 := bstep (se 1 (by rfl) ⟨1415771, by rfl⟩ : syracuseStep 1887695 = 2831543) B2831543
theorem B4771295 : Blo 1044610 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B45305345 : Blo 1044610 45305345 := bstep (se 2 (by rfl) ⟨16989504, by rfl⟩ : syracuseStep 45305345 = 33979009) B33979009
theorem B15093479 : Blo 1044610 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B3526739 : Blo 1044610 3526739 := bstep (se 1 (by rfl) ⟨2645054, by rfl⟩ : syracuseStep 3526739 = 5290109) B5290109
theorem B16142489 : Blo 1044610 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B3526847 : Blo 1044610 3526847 := bstep (se 1 (by rfl) ⟨2645135, by rfl⟩ : syracuseStep 3526847 = 5290271) B5290271
theorem B3526955 : Blo 1044610 3526955 := bstep (se 1 (by rfl) ⟨2645216, by rfl⟩ : syracuseStep 3526955 = 5290433) B5290433
theorem B68932577 : Blo 1044610 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B2118727 : Blo 1044610 2118727 := bstep (se 1 (by rfl) ⟨1589045, by rfl⟩ : syracuseStep 2118727 = 3178091) B3178091
theorem B3528953 : Blo 1044610 3528953 := bstep (se 2 (by rfl) ⟨1323357, by rfl⟩ : syracuseStep 3528953 = 2646715) B2646715
theorem B3529115 : Blo 1044610 3529115 := bstep (se 1 (by rfl) ⟨2646836, by rfl⟩ : syracuseStep 3529115 = 5293673) B5293673
theorem B3529601 : Blo 1044610 3529601 := bstep (se 2 (by rfl) ⟨1323600, by rfl⟩ : syracuseStep 3529601 = 2647201) B2647201
theorem B627465359 : Blo 1044610 627465359 := bstep (se 1 (by rfl) ⟨470599019, by rfl⟩ : syracuseStep 627465359 = 941198039) B941198039
theorem B34004843 : Blo 1044610 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B3530735 : Blo 1044610 3530735 := bstep (se 1 (by rfl) ⟨2648051, by rfl⟩ : syracuseStep 3530735 = 5296103) B5296103
theorem B2515187 : Blo 1044610 2515187 := bstep (se 1 (by rfl) ⟨1886390, by rfl⟩ : syracuseStep 2515187 = 3772781) B3772781
theorem B3531167 : Blo 1044610 3531167 := bstep (se 1 (by rfl) ⟨2648375, by rfl⟩ : syracuseStep 3531167 = 5296751) B5296751
theorem B5661247 : Blo 1044610 5661247 := bstep (se 1 (by rfl) ⟨4245935, by rfl⟩ : syracuseStep 5661247 = 8491871) B8491871
theorem B3531545 : Blo 1044610 3531545 := bstep (se 2 (by rfl) ⟨1324329, by rfl⟩ : syracuseStep 3531545 = 2648659) B2648659
theorem B2647151 : Blo 1044610 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B14345405 : Blo 1044610 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B2352617 : Blo 1044610 2352617 := bstep (se 2 (by rfl) ⟨882231, by rfl⟩ : syracuseStep 2352617 = 1764463) B1764463
theorem B11331181 : Blo 1044610 11331181 := bstep (se 3 (by rfl) ⟨2124596, by rfl⟩ : syracuseStep 11331181 = 4249193) B4249193
theorem B1697545 : Blo 1044610 1697545 := bstep (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) B1273159
theorem B2352905 : Blo 1044610 2352905 := bstep (se 2 (by rfl) ⟨882339, by rfl⟩ : syracuseStep 2352905 = 1764679) B1764679
theorem B5957549 : Blo 1044610 5957549 := bstep (se 3 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 5957549 = 2234081) B2234081
theorem B2353319 : Blo 1044610 2353319 := bstep (se 1 (by rfl) ⟨1764989, by rfl⟩ : syracuseStep 2353319 = 3529979) B3529979
theorem B1566971 : Blo 1044610 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B3827999 : Blo 1044610 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B2976041 : Blo 1044610 2976041 := bstep (se 2 (by rfl) ⟨1116015, by rfl⟩ : syracuseStep 2976041 = 2232031) B2232031
theorem B1763815 : Blo 1044610 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B11922065 : Blo 1044610 11922065 := bstep (se 2 (by rfl) ⟨4470774, by rfl⟩ : syracuseStep 11922065 = 8941549) B8941549
theorem B1567391 : Blo 1044610 1567391 := bstep (se 1 (by rfl) ⟨1175543, by rfl⟩ : syracuseStep 1567391 = 2351087) B2351087
theorem B1567559 : Blo 1044610 1567559 := bstep (se 1 (by rfl) ⟨1175669, by rfl⟩ : syracuseStep 1567559 = 2351339) B2351339
theorem B3533651 : Blo 1044610 3533651 := bstep (se 1 (by rfl) ⟨2650238, by rfl⟩ : syracuseStep 3533651 = 5300477) B5300477
theorem B2354543 : Blo 1044610 2354543 := bstep (se 1 (by rfl) ⟨1765907, by rfl⟩ : syracuseStep 2354543 = 3531815) B3531815
theorem B1568159 : Blo 1044610 1568159 := bstep (se 1 (by rfl) ⟨1176119, by rfl⟩ : syracuseStep 1568159 = 2352239) B2352239
theorem B3534569 : Blo 1044610 3534569 := bstep (se 2 (by rfl) ⟨1325463, by rfl⟩ : syracuseStep 3534569 = 2650927) B2650927
theorem B2650067 : Blo 1044610 2650067 := bstep (se 1 (by rfl) ⟨1987550, by rfl⟩ : syracuseStep 2650067 = 3975101) B3975101
theorem B1568831 : Blo 1044610 1568831 := bstep (se 1 (by rfl) ⟨1176623, by rfl⟩ : syracuseStep 1568831 = 2353247) B2353247
theorem B2355263 : Blo 1044610 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B22671535 : Blo 1044610 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B1044671 : Blo 1044610 1044671 := bstep (se 1 (by rfl) ⟨783503, by rfl⟩ : syracuseStep 1044671 = 1567007) B1567007
theorem B3535055 : Blo 1044610 3535055 := bstep (se 1 (by rfl) ⟨2651291, by rfl⟩ : syracuseStep 3535055 = 5302583) B5302583
theorem B7958735 : Blo 1044610 7958735 := bstep (se 1 (by rfl) ⟨5969051, by rfl⟩ : syracuseStep 7958735 = 11938103) B11938103
theorem B1044703 : Blo 1044610 1044703 := bstep (se 1 (by rfl) ⟨783527, by rfl⟩ : syracuseStep 1044703 = 1567055) B1567055
theorem B12742919 : Blo 1044610 12742919 := bstep (se 1 (by rfl) ⟨9557189, by rfl⟩ : syracuseStep 12742919 = 19114379) B19114379
theorem B1044763 : Blo 1044610 1044763 := bstep (se 1 (by rfl) ⟨783572, by rfl⟩ : syracuseStep 1044763 = 1567145) B1567145
theorem B1045019 : Blo 1044610 1045019 := bstep (se 1 (by rfl) ⟨783764, by rfl⟩ : syracuseStep 1045019 = 1567529) B1567529
theorem B1045159 : Blo 1044610 1045159 := bstep (se 1 (by rfl) ⟨783869, by rfl⟩ : syracuseStep 1045159 = 1567739) B1567739
theorem B1045199 : Blo 1044610 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B2650907 : Blo 1044610 2650907 := bstep (se 1 (by rfl) ⟨1988180, by rfl⟩ : syracuseStep 2650907 = 3976361) B3976361
theorem B1045279 : Blo 1044610 1045279 := bstep (se 1 (by rfl) ⟨783959, by rfl⟩ : syracuseStep 1045279 = 1567919) B1567919
theorem B1045319 : Blo 1044610 1045319 := bstep (se 1 (by rfl) ⟨783989, by rfl⟩ : syracuseStep 1045319 = 1567979) B1567979
theorem B3536027 : Blo 1044610 3536027 := bstep (se 1 (by rfl) ⟨2652020, by rfl⟩ : syracuseStep 3536027 = 5304041) B5304041
theorem B1045759 : Blo 1044610 1045759 := bstep (se 1 (by rfl) ⟨784319, by rfl⟩ : syracuseStep 1045759 = 1568639) B1568639
theorem B1570127 : Blo 1044610 1570127 := bstep (se 1 (by rfl) ⟨1177595, by rfl⟩ : syracuseStep 1570127 = 2355191) B2355191
theorem B2356559 : Blo 1044610 2356559 := bstep (se 1 (by rfl) ⟨1767419, by rfl⟩ : syracuseStep 2356559 = 3534839) B3534839
theorem B1570169 : Blo 1044610 1570169 := bstep (se 2 (by rfl) ⟨588813, by rfl⟩ : syracuseStep 1570169 = 1177627) B1177627
theorem B1045983 : Blo 1044610 1045983 := bstep (se 1 (by rfl) ⟨784487, by rfl⟩ : syracuseStep 1045983 = 1568975) B1568975
theorem B1046063 : Blo 1044610 1046063 := bstep (se 1 (by rfl) ⟨784547, by rfl⟩ : syracuseStep 1046063 = 1569095) B1569095
theorem B1570367 : Blo 1044610 1570367 := bstep (se 1 (by rfl) ⟨1177775, by rfl⟩ : syracuseStep 1570367 = 2355551) B2355551
theorem B1046375 : Blo 1044610 1046375 := bstep (se 1 (by rfl) ⟨784781, by rfl⟩ : syracuseStep 1046375 = 1569563) B1569563
theorem B1177447 : Blo 1044610 1177447 := bstep (se 1 (by rfl) ⟨883085, by rfl⟩ : syracuseStep 1177447 = 1766171) B1766171
theorem B1570715 : Blo 1044610 1570715 := bstep (se 1 (by rfl) ⟨1178036, by rfl⟩ : syracuseStep 1570715 = 2356073) B2356073
theorem B1046559 : Blo 1044610 1046559 := bstep (se 1 (by rfl) ⟨784919, by rfl⟩ : syracuseStep 1046559 = 1569839) B1569839
theorem B1570847 : Blo 1044610 1570847 := bstep (se 1 (by rfl) ⟨1178135, by rfl⟩ : syracuseStep 1570847 = 2356271) B2356271
theorem B2357279 : Blo 1044610 2357279 := bstep (se 1 (by rfl) ⟨1767959, by rfl⟩ : syracuseStep 2357279 = 3535919) B3535919
theorem B1046591 : Blo 1044610 1046591 := bstep (se 1 (by rfl) ⟨784943, by rfl⟩ : syracuseStep 1046591 = 1569887) B1569887
theorem B1767487 : Blo 1044610 1767487 := bstep (se 1 (by rfl) ⟨1325615, by rfl⟩ : syracuseStep 1767487 = 2651231) B2651231
theorem B1046631 : Blo 1044610 1046631 := bstep (se 1 (by rfl) ⟨784973, by rfl⟩ : syracuseStep 1046631 = 1569947) B1569947
theorem B1046639 : Blo 1044610 1046639 := bstep (se 1 (by rfl) ⟨784979, by rfl⟩ : syracuseStep 1046639 = 1569959) B1569959
theorem B1047087 : Blo 1044610 1047087 := bstep (se 1 (by rfl) ⟨785315, by rfl⟩ : syracuseStep 1047087 = 1570631) B1570631
theorem B1571375 : Blo 1044610 1571375 := bstep (se 1 (by rfl) ⟨1178531, by rfl⟩ : syracuseStep 1571375 = 2357063) B2357063
theorem B1047207 : Blo 1044610 1047207 := bstep (se 1 (by rfl) ⟨785405, by rfl⟩ : syracuseStep 1047207 = 1570811) B1570811
theorem B1571495 : Blo 1044610 1571495 := bstep (se 1 (by rfl) ⟨1178621, by rfl⟩ : syracuseStep 1571495 = 2357243) B2357243
theorem B2357927 : Blo 1044610 2357927 := bstep (se 1 (by rfl) ⟨1768445, by rfl⟩ : syracuseStep 2357927 = 3536891) B3536891
theorem B1047247 : Blo 1044610 1047247 := bstep (se 1 (by rfl) ⟨785435, by rfl⟩ : syracuseStep 1047247 = 1570871) B1570871
theorem B1047291 : Blo 1044610 1047291 := bstep (se 1 (by rfl) ⟨785468, by rfl⟩ : syracuseStep 1047291 = 1570937) B1570937
theorem B1571579 : Blo 1044610 1571579 := bstep (se 1 (by rfl) ⟨1178684, by rfl⟩ : syracuseStep 1571579 = 2357369) B2357369
theorem B1047327 : Blo 1044610 1047327 := bstep (se 1 (by rfl) ⟨785495, by rfl⟩ : syracuseStep 1047327 = 1570991) B1570991
theorem B1571615 : Blo 1044610 1571615 := bstep (se 1 (by rfl) ⟨1178711, by rfl⟩ : syracuseStep 1571615 = 2357423) B2357423
theorem B2652983 : Blo 1044610 2652983 := bstep (se 1 (by rfl) ⟨1989737, by rfl⟩ : syracuseStep 2652983 = 3979475) B3979475
theorem B1571705 : Blo 1044610 1571705 := bstep (se 2 (by rfl) ⟨589389, by rfl⟩ : syracuseStep 1571705 = 1178779) B1178779
theorem B1047487 : Blo 1044610 1047487 := bstep (se 1 (by rfl) ⟨785615, by rfl⟩ : syracuseStep 1047487 = 1571231) B1571231
theorem B1047547 : Blo 1044610 1047547 := bstep (se 1 (by rfl) ⟨785660, by rfl⟩ : syracuseStep 1047547 = 1571321) B1571321
theorem B16972897 : Blo 1044610 16972897 := bstep (se 2 (by rfl) ⟨6364836, by rfl⟩ : syracuseStep 16972897 = 12729673) B12729673
theorem B12909665 : Blo 1044610 12909665 := bstep (se 2 (by rfl) ⟨4841124, by rfl⟩ : syracuseStep 12909665 = 9682249) B9682249
theorem B1572047 : Blo 1044610 1572047 := bstep (se 1 (by rfl) ⟨1179035, by rfl⟩ : syracuseStep 1572047 = 2358071) B2358071
theorem B1047871 : Blo 1044610 1047871 := bstep (se 1 (by rfl) ⟨785903, by rfl⟩ : syracuseStep 1047871 = 1571807) B1571807
theorem B1572167 : Blo 1044610 1572167 := bstep (se 1 (by rfl) ⟨1179125, by rfl⟩ : syracuseStep 1572167 = 2358251) B2358251
theorem B1047911 : Blo 1044610 1047911 := bstep (se 1 (by rfl) ⟨785933, by rfl⟩ : syracuseStep 1047911 = 1571867) B1571867
theorem B1048167 : Blo 1044610 1048167 := bstep (se 1 (by rfl) ⟨786125, by rfl⟩ : syracuseStep 1048167 = 1572251) B1572251
theorem B1048219 : Blo 1044610 1048219 := bstep (se 1 (by rfl) ⟨786164, by rfl⟩ : syracuseStep 1048219 = 1572329) B1572329
theorem B1048223 : Blo 1044610 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B1048315 : Blo 1044610 1048315 := bstep (se 1 (by rfl) ⟨786236, by rfl⟩ : syracuseStep 1048315 = 1572473) B1572473
theorem B1048447 : Blo 1044610 1048447 := bstep (se 1 (by rfl) ⟨786335, by rfl⟩ : syracuseStep 1048447 = 1572671) B1572671
theorem B1048479 : Blo 1044610 1048479 := bstep (se 1 (by rfl) ⟨786359, by rfl⟩ : syracuseStep 1048479 = 1572719) B1572719
theorem B1572767 : Blo 1044610 1572767 := bstep (se 1 (by rfl) ⟨1179575, by rfl⟩ : syracuseStep 1572767 = 2359151) B2359151
theorem B11927897 : Blo 1044610 11927897 := bstep (se 2 (by rfl) ⟨4472961, by rfl⟩ : syracuseStep 11927897 = 8945923) B8945923
theorem B10191815 : Blo 1044610 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B5964839 : Blo 1044610 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B11929355 : Blo 1044610 11929355 := bstep (se 1 (by rfl) ⟨8947016, by rfl⟩ : syracuseStep 11929355 = 17894033) B17894033
theorem B15108241 : Blo 1044610 15108241 := bstep (se 2 (by rfl) ⟨5665590, by rfl⟩ : syracuseStep 15108241 = 11331181) B11331181
theorem B3180863 : Blo 1044610 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B2263393 : Blo 1044610 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B10062319 : Blo 1044610 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B5967503 : Blo 1044610 5967503 := bstep (se 1 (by rfl) ⟨4475627, by rfl⟩ : syracuseStep 5967503 = 8951255) B8951255
theorem B7148519 : Blo 1044610 7148519 := bstep (se 1 (by rfl) ⟨5361389, by rfl⟩ : syracuseStep 7148519 = 10722779) B10722779
theorem B3347443 : Blo 1044610 3347443 := bstep (se 1 (by rfl) ⟨2510582, by rfl⟩ : syracuseStep 3347443 = 5021165) B5021165
theorem B1676791 : Blo 1044610 1676791 := bstep (se 1 (by rfl) ⟨1257593, by rfl⟩ : syracuseStep 1676791 = 2515187) B2515187
theorem B919443473 : Blo 1044610 919443473 := bstep (se 2 (by rfl) ⟨344791302, by rfl⟩ : syracuseStep 919443473 = 689582605) B689582605
theorem B4462847 : Blo 1044610 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B3971699 : Blo 1044610 3971699 := bstep (se 1 (by rfl) ⟨2978774, by rfl⟩ : syracuseStep 3971699 = 5957549) B5957549
theorem B4201151 : Blo 1044610 4201151 := bstep (se 1 (by rfl) ⟨3150863, by rfl⟩ : syracuseStep 4201151 = 6301727) B6301727
theorem B2824969 : Blo 1044610 2824969 := bstep (se 2 (by rfl) ⟨1059363, by rfl⟩ : syracuseStep 2824969 = 2118727) B2118727
theorem B38673233 : Blo 1044610 38673233 := bstep (se 2 (by rfl) ⟨14502462, by rfl⟩ : syracuseStep 38673233 = 29004925) B29004925
theorem B11935187 : Blo 1044610 11935187 := bstep (se 1 (by rfl) ⟨8951390, by rfl⟩ : syracuseStep 11935187 = 17902781) B17902781
theorem B14491199 : Blo 1044610 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B8495279 : Blo 1044610 8495279 := bstep (se 1 (by rfl) ⟨6371459, by rfl⟩ : syracuseStep 8495279 = 12742919) B12742919
theorem B3778157 : Blo 1044610 3778157 := bstep (se 3 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 3778157 = 1416809) B1416809
theorem B3779239 : Blo 1044610 3779239 := bstep (se 1 (by rfl) ⟨2834429, by rfl⟩ : syracuseStep 3779239 = 5668859) B5668859
theorem B11021195 : Blo 1044610 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B11906027 : Blo 1044610 11906027 := bstep (se 1 (by rfl) ⟨8929520, by rfl⟩ : syracuseStep 11906027 = 17859041) B17859041
theorem B7548011 : Blo 1044610 7548011 := bstep (se 1 (by rfl) ⟨5661008, by rfl⟩ : syracuseStep 7548011 = 11322017) B11322017
theorem B7548329 : Blo 1044610 7548329 := bstep (se 2 (by rfl) ⟨2830623, by rfl⟩ : syracuseStep 7548329 = 5661247) B5661247
theorem B2829791 : Blo 1044610 2829791 := bstep (se 1 (by rfl) ⟨2122343, by rfl⟩ : syracuseStep 2829791 = 4244687) B4244687
theorem B183873397 : Blo 1044610 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B4239593 : Blo 1044610 4239593 := bstep (se 2 (by rfl) ⟨1589847, by rfl⟩ : syracuseStep 4239593 = 3179695) B3179695
theorem B1323631 : Blo 1044610 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B1258463 : Blo 1044610 1258463 := bstep (se 1 (by rfl) ⟨943847, by rfl⟩ : syracuseStep 1258463 = 1887695) B1887695
theorem B10761659 : Blo 1044610 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B5027663 : Blo 1044610 5027663 := bstep (se 1 (by rfl) ⟨3770747, by rfl⟩ : syracuseStep 5027663 = 7541495) B7541495
theorem B5028587 : Blo 1044610 5028587 := bstep (se 1 (by rfl) ⟨3771440, by rfl⟩ : syracuseStep 5028587 = 7542881) B7542881
theorem B11320631 : Blo 1044610 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B19120211 : Blo 1044610 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B5030009 : Blo 1044610 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B3981433 : Blo 1044610 3981433 := bstep (se 2 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 3981433 = 2986075) B2986075
theorem B30228713 : Blo 1044610 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B1984027 : Blo 1044610 1984027 := bstep (se 1 (by rfl) ⟨1488020, by rfl⟩ : syracuseStep 1984027 = 2976041) B2976041
theorem B7948043 : Blo 1044610 7948043 := bstep (se 1 (by rfl) ⟨5961032, by rfl⟩ : syracuseStep 7948043 = 11922065) B11922065
theorem B34425773 : Blo 1044610 34425773 := bstep (se 3 (by rfl) ⟨6454832, by rfl⟩ : syracuseStep 34425773 = 12909665) B12909665
theorem B1985705 : Blo 1044610 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B22630529 : Blo 1044610 22630529 := bstep (se 2 (by rfl) ⟨8486448, by rfl⟩ : syracuseStep 22630529 = 16972897) B16972897
theorem B3527279 : Blo 1044610 3527279 := bstep (se 1 (by rfl) ⟨2645459, by rfl⟩ : syracuseStep 3527279 = 5290919) B5290919
theorem B5952923 : Blo 1044610 5952923 := bstep (se 1 (by rfl) ⟨4464692, by rfl⟩ : syracuseStep 5952923 = 8929385) B8929385
theorem B10868527 : Blo 1044610 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B2513351 : Blo 1044610 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B3529331 : Blo 1044610 3529331 := bstep (se 1 (by rfl) ⟨2646998, by rfl⟩ : syracuseStep 3529331 = 5293997) B5293997
theorem B10738331 : Blo 1044610 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B2645075 : Blo 1044610 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B5299667 : Blo 1044610 5299667 := bstep (se 1 (by rfl) ⟨3974750, by rfl⟩ : syracuseStep 5299667 = 7949501) B7949501
theorem B2350655 : Blo 1044610 2350655 := bstep (se 1 (by rfl) ⟨1762991, by rfl⟩ : syracuseStep 2350655 = 3525983) B3525983
theorem B30203563 : Blo 1044610 30203563 := bstep (se 1 (by rfl) ⟨22652672, by rfl⟩ : syracuseStep 30203563 = 45305345) B45305345
theorem B183820205 : Blo 1044610 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B5955565 : Blo 1044610 5955565 := bstep (se 3 (by rfl) ⟨1116668, by rfl⟩ : syracuseStep 5955565 = 2233337) B2233337
theorem B2351159 : Blo 1044610 2351159 := bstep (se 1 (by rfl) ⟨1763369, by rfl⟩ : syracuseStep 2351159 = 3526739) B3526739
theorem B2351231 : Blo 1044610 2351231 := bstep (se 1 (by rfl) ⟨1763423, by rfl⟩ : syracuseStep 2351231 = 3526847) B3526847
theorem B2351303 : Blo 1044610 2351303 := bstep (se 1 (by rfl) ⟨1763477, by rfl⟩ : syracuseStep 2351303 = 3526955) B3526955
theorem B3531005 : Blo 1044610 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B2351753 : Blo 1044610 2351753 := bstep (se 2 (by rfl) ⟨881907, by rfl⟩ : syracuseStep 2351753 = 1763815) B1763815
theorem B2646665 : Blo 1044610 2646665 := bstep (se 2 (by rfl) ⟨992499, by rfl⟩ : syracuseStep 2646665 = 1984999) B1984999
theorem B2647039 : Blo 1044610 2647039 := bstep (se 1 (by rfl) ⟨1985279, by rfl⟩ : syracuseStep 2647039 = 3970559) B3970559
theorem B20079737 : Blo 1044610 20079737 := bstep (se 2 (by rfl) ⟨7529901, by rfl⟩ : syracuseStep 20079737 = 15059803) B15059803
theorem B2647343 : Blo 1044610 2647343 := bstep (se 1 (by rfl) ⟨1985507, by rfl⟩ : syracuseStep 2647343 = 3971015) B3971015
theorem B147219929 : Blo 1044610 147219929 := bstep (se 2 (by rfl) ⟨55207473, by rfl⟩ : syracuseStep 147219929 = 110414947) B110414947
theorem B2352635 : Blo 1044610 2352635 := bstep (se 1 (by rfl) ⟨1764476, by rfl⟩ : syracuseStep 2352635 = 3528953) B3528953
theorem B2352743 : Blo 1044610 2352743 := bstep (se 1 (by rfl) ⟨1764557, by rfl⟩ : syracuseStep 2352743 = 3529115) B3529115
theorem B13395617 : Blo 1044610 13395617 := bstep (se 2 (by rfl) ⟨5023356, by rfl⟩ : syracuseStep 13395617 = 10046713) B10046713
theorem B2353067 : Blo 1044610 2353067 := bstep (se 1 (by rfl) ⟨1764800, by rfl⟩ : syracuseStep 2353067 = 3529601) B3529601
theorem B418310239 : Blo 1044610 418310239 := bstep (se 1 (by rfl) ⟨313732679, by rfl⟩ : syracuseStep 418310239 = 627465359) B627465359
theorem B5728511 : Blo 1044610 5728511 := bstep (se 1 (by rfl) ⟨4296383, by rfl⟩ : syracuseStep 5728511 = 8592767) B8592767
theorem B68905241 : Blo 1044610 68905241 := bstep (se 2 (by rfl) ⟨25839465, by rfl⟩ : syracuseStep 68905241 = 51678931) B51678931
theorem B22669895 : Blo 1044610 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B2353823 : Blo 1044610 2353823 := bstep (se 1 (by rfl) ⟨1765367, by rfl⟩ : syracuseStep 2353823 = 3530735) B3530735
theorem B5958481 : Blo 1044610 5958481 := bstep (se 2 (by rfl) ⟨2234430, by rfl⟩ : syracuseStep 5958481 = 4468861) B4468861
theorem B2354111 : Blo 1044610 2354111 := bstep (se 1 (by rfl) ⟨1765583, by rfl⟩ : syracuseStep 2354111 = 3531167) B3531167
theorem B2354363 : Blo 1044610 2354363 := bstep (se 1 (by rfl) ⟨1765772, by rfl⟩ : syracuseStep 2354363 = 3531545) B3531545
theorem B2977145 : Blo 1044610 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B1764767 : Blo 1044610 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B9563603 : Blo 1044610 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B2649631 : Blo 1044610 2649631 := bstep (se 1 (by rfl) ⟨1987223, by rfl⟩ : syracuseStep 2649631 = 3974447) B3974447
theorem B2977327 : Blo 1044610 2977327 := bstep (se 1 (by rfl) ⟨2232995, by rfl⟩ : syracuseStep 2977327 = 4465991) B4465991
theorem B1568411 : Blo 1044610 1568411 := bstep (se 1 (by rfl) ⟨1176308, by rfl⟩ : syracuseStep 1568411 = 2352617) B2352617
theorem B85814963 : Blo 1044610 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B1568603 : Blo 1044610 1568603 := bstep (se 1 (by rfl) ⟨1176452, by rfl⟩ : syracuseStep 1568603 = 2352905) B2352905
theorem B1568879 : Blo 1044610 1568879 := bstep (se 1 (by rfl) ⟨1176659, by rfl⟩ : syracuseStep 1568879 = 2353319) B2353319
theorem B1044647 : Blo 1044610 1044647 := bstep (se 1 (by rfl) ⟨783485, by rfl⟩ : syracuseStep 1044647 = 1566971) B1566971
theorem B2551999 : Blo 1044610 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B1044927 : Blo 1044610 1044927 := bstep (se 1 (by rfl) ⟨783695, by rfl⟩ : syracuseStep 1044927 = 1567391) B1567391
theorem B1045039 : Blo 1044610 1045039 := bstep (se 1 (by rfl) ⟨783779, by rfl⟩ : syracuseStep 1045039 = 1567559) B1567559
theorem B2355767 : Blo 1044610 2355767 := bstep (se 1 (by rfl) ⟨1766825, by rfl⟩ : syracuseStep 2355767 = 3533651) B3533651
theorem B1569695 : Blo 1044610 1569695 := bstep (se 1 (by rfl) ⟨1177271, by rfl⟩ : syracuseStep 1569695 = 2354543) B2354543
theorem B1045439 : Blo 1044610 1045439 := bstep (se 1 (by rfl) ⟨784079, by rfl⟩ : syracuseStep 1045439 = 1568159) B1568159
theorem B1569929 : Blo 1044610 1569929 := bstep (se 2 (by rfl) ⟨588723, by rfl⟩ : syracuseStep 1569929 = 1177447) B1177447
theorem B2356379 : Blo 1044610 2356379 := bstep (se 1 (by rfl) ⟨1767284, by rfl⟩ : syracuseStep 2356379 = 3534569) B3534569
theorem B7959707 : Blo 1044610 7959707 := bstep (se 1 (by rfl) ⟨5969780, by rfl⟩ : syracuseStep 7959707 = 11939561) B11939561
theorem B1766569 : Blo 1044610 1766569 := bstep (se 2 (by rfl) ⟨662463, by rfl⟩ : syracuseStep 1766569 = 1324927) B1324927
theorem B1766711 : Blo 1044610 1766711 := bstep (se 1 (by rfl) ⟨1325033, by rfl⟩ : syracuseStep 1766711 = 2650067) B2650067
theorem B1045887 : Blo 1044610 1045887 := bstep (se 1 (by rfl) ⟨784415, by rfl⟩ : syracuseStep 1045887 = 1568831) B1568831
theorem B1570175 : Blo 1044610 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B2356649 : Blo 1044610 2356649 := bstep (se 2 (by rfl) ⟨883743, by rfl⟩ : syracuseStep 2356649 = 1767487) B1767487
theorem B2356703 : Blo 1044610 2356703 := bstep (se 1 (by rfl) ⟨1767527, by rfl⟩ : syracuseStep 2356703 = 3535055) B3535055
theorem B5305823 : Blo 1044610 5305823 := bstep (se 1 (by rfl) ⟨3979367, by rfl⟩ : syracuseStep 5305823 = 7958735) B7958735
theorem B9533099 : Blo 1044610 9533099 := bstep (se 1 (by rfl) ⟨7149824, by rfl⟩ : syracuseStep 9533099 = 14299649) B14299649
theorem B1767271 : Blo 1044610 1767271 := bstep (se 1 (by rfl) ⟨1325453, by rfl⟩ : syracuseStep 1767271 = 2650907) B2650907
theorem B2357351 : Blo 1044610 2357351 := bstep (se 1 (by rfl) ⟨1768013, by rfl⟩ : syracuseStep 2357351 = 3536027) B3536027
theorem B1046751 : Blo 1044610 1046751 := bstep (se 1 (by rfl) ⟨785063, by rfl⟩ : syracuseStep 1046751 = 1570127) B1570127
theorem B1571039 : Blo 1044610 1571039 := bstep (se 1 (by rfl) ⟨1178279, by rfl⟩ : syracuseStep 1571039 = 2356559) B2356559
theorem B1046779 : Blo 1044610 1046779 := bstep (se 1 (by rfl) ⟨785084, by rfl⟩ : syracuseStep 1046779 = 1570169) B1570169
theorem B1046911 : Blo 1044610 1046911 := bstep (se 1 (by rfl) ⟨785183, by rfl⟩ : syracuseStep 1046911 = 1570367) B1570367
theorem B1047143 : Blo 1044610 1047143 := bstep (se 1 (by rfl) ⟨785357, by rfl⟩ : syracuseStep 1047143 = 1570715) B1570715
theorem B1047231 : Blo 1044610 1047231 := bstep (se 1 (by rfl) ⟨785423, by rfl⟩ : syracuseStep 1047231 = 1570847) B1570847
theorem B1571519 : Blo 1044610 1571519 := bstep (se 1 (by rfl) ⟨1178639, by rfl⟩ : syracuseStep 1571519 = 2357279) B2357279
theorem B1047583 : Blo 1044610 1047583 := bstep (se 1 (by rfl) ⟨785687, by rfl⟩ : syracuseStep 1047583 = 1571375) B1571375
theorem B1047663 : Blo 1044610 1047663 := bstep (se 1 (by rfl) ⟨785747, by rfl⟩ : syracuseStep 1047663 = 1571495) B1571495
theorem B1571951 : Blo 1044610 1571951 := bstep (se 1 (by rfl) ⟨1178963, by rfl⟩ : syracuseStep 1571951 = 2357927) B2357927
theorem B1047719 : Blo 1044610 1047719 := bstep (se 1 (by rfl) ⟨785789, by rfl⟩ : syracuseStep 1047719 = 1571579) B1571579
theorem B1047743 : Blo 1044610 1047743 := bstep (se 1 (by rfl) ⟨785807, by rfl⟩ : syracuseStep 1047743 = 1571615) B1571615
theorem B1768655 : Blo 1044610 1768655 := bstep (se 1 (by rfl) ⟨1326491, by rfl⟩ : syracuseStep 1768655 = 2652983) B2652983
theorem B1047803 : Blo 1044610 1047803 := bstep (se 1 (by rfl) ⟨785852, by rfl⟩ : syracuseStep 1047803 = 1571705) B1571705
theorem B30178655 : Blo 1044610 30178655 := bstep (se 1 (by rfl) ⟨22633991, by rfl⟩ : syracuseStep 30178655 = 45267983) B45267983
theorem B1048031 : Blo 1044610 1048031 := bstep (se 1 (by rfl) ⟨786023, by rfl⟩ : syracuseStep 1048031 = 1572047) B1572047
theorem B4587005 : Blo 1044610 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B1048111 : Blo 1044610 1048111 := bstep (se 1 (by rfl) ⟨786083, by rfl⟩ : syracuseStep 1048111 = 1572167) B1572167
theorem B1048511 : Blo 1044610 1048511 := bstep (se 1 (by rfl) ⟨786383, by rfl⟩ : syracuseStep 1048511 = 1572767) B1572767
theorem B2654167 : Blo 1044610 2654167 := bstep (se 1 (by rfl) ⟨1990625, by rfl⟩ : syracuseStep 2654167 = 3981251) B3981251
theorem B12746807 : Blo 1044610 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B20152475 : Blo 1044610 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B5308577 : Blo 1044610 5308577 := bstep (se 2 (by rfl) ⟨1990716, by rfl⟩ : syracuseStep 5308577 = 3981433) B3981433
theorem B557746985 : Blo 1044610 557746985 := bstep (se 2 (by rfl) ⟨209155119, by rfl⟩ : syracuseStep 557746985 = 418310239) B418310239
theorem B3017857 : Blo 1044610 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B3968615 : Blo 1044610 3968615 := bstep (se 1 (by rfl) ⟨2976461, by rfl⟩ : syracuseStep 3968615 = 5952923) B5952923
theorem B612962315 : Blo 1044610 612962315 := bstep (se 1 (by rfl) ⟨459721736, by rfl⟩ : syracuseStep 612962315 = 919443473) B919443473
theorem B1675567 : Blo 1044610 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B3969769 : Blo 1044610 3969769 := bstep (se 2 (by rfl) ⟨1488663, by rfl⟩ : syracuseStep 3969769 = 2977327) B2977327
theorem B98146619 : Blo 1044610 98146619 := bstep (se 1 (by rfl) ⟨73609964, by rfl⟩ : syracuseStep 98146619 = 147219929) B147219929
theorem B4463257 : Blo 1044610 4463257 := bstep (se 2 (by rfl) ⟨1673721, by rfl⟩ : syracuseStep 4463257 = 3347443) B3347443
theorem B15113263 : Blo 1044610 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B7937351 : Blo 1044610 7937351 := bstep (se 1 (by rfl) ⟨5953013, by rfl⟩ : syracuseStep 7937351 = 11906027) B11906027
theorem B14491369 : Blo 1044610 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B2826395 : Blo 1044610 2826395 := bstep (se 1 (by rfl) ⟨2119796, by rfl⟩ : syracuseStep 2826395 = 4239593) B4239593
theorem B25502941 : Blo 1044610 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B3351775 : Blo 1044610 3351775 := bstep (se 1 (by rfl) ⟨2513831, by rfl⟩ : syracuseStep 3351775 = 5027663) B5027663
theorem B3352391 : Blo 1044610 3352391 := bstep (se 1 (by rfl) ⟨2514293, by rfl⟩ : syracuseStep 3352391 = 5028587) B5028587
theorem B7547087 : Blo 1044610 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B3058003 : Blo 1044610 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B7940753 : Blo 1044610 7940753 := bstep (se 2 (by rfl) ⟨2977782, by rfl⟩ : syracuseStep 7940753 = 5955565) B5955565
theorem B3353339 : Blo 1044610 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B6794543 : Blo 1044610 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B3976559 : Blo 1044610 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B22950515 : Blo 1044610 22950515 := bstep (se 1 (by rfl) ⟨17212886, by rfl⟩ : syracuseStep 22950515 = 34425773) B34425773
theorem B1323803 : Blo 1044610 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B3978335 : Blo 1044610 3978335 := bstep (se 1 (by rfl) ⟨2983751, by rfl⟩ : syracuseStep 3978335 = 5967503) B5967503
theorem B3355901 : Blo 1044610 3355901 := bstep (se 3 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 3355901 = 1258463) B1258463
theorem B13416425 : Blo 1044610 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B4765679 : Blo 1044610 4765679 := bstep (se 1 (by rfl) ⟨3574259, by rfl⟩ : syracuseStep 4765679 = 7148519) B7148519
theorem B7944641 : Blo 1044610 7944641 := bstep (se 2 (by rfl) ⟨2979240, by rfl⟩ : syracuseStep 7944641 = 5958481) B5958481
theorem B7158887 : Blo 1044610 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B13386491 : Blo 1044610 13386491 := bstep (se 1 (by rfl) ⟨10039868, by rfl⟩ : syracuseStep 13386491 = 20079737) B20079737
theorem B8930411 : Blo 1044610 8930411 := bstep (se 1 (by rfl) ⟨6697808, by rfl⟩ : syracuseStep 8930411 = 13395617) B13395617
theorem B3819007 : Blo 1044610 3819007 := bstep (se 1 (by rfl) ⟨2864255, by rfl⟩ : syracuseStep 3819007 = 5728511) B5728511
theorem B5032007 : Blo 1044610 5032007 := bstep (se 1 (by rfl) ⟨3774005, by rfl⟩ : syracuseStep 5032007 = 7548011) B7548011
theorem B1984763 : Blo 1044610 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B5032219 : Blo 1044610 5032219 := bstep (se 1 (by rfl) ⟨3774164, by rfl⟩ : syracuseStep 5032219 = 7548329) B7548329
theorem B1886527 : Blo 1044610 1886527 := bstep (se 1 (by rfl) ⟨1414895, by rfl⟩ : syracuseStep 1886527 = 2829791) B2829791
theorem B7951931 : Blo 1044610 7951931 := bstep (se 1 (by rfl) ⟨5963948, by rfl⟩ : syracuseStep 7951931 = 11927897) B11927897
theorem B60348077 : Blo 1044610 60348077 := bstep (se 3 (by rfl) ⟨11315264, by rfl⟩ : syracuseStep 60348077 = 22630529) B22630529
theorem B5298695 : Blo 1044610 5298695 := bstep (se 1 (by rfl) ⟨3974021, by rfl⟩ : syracuseStep 5298695 = 7948043) B7948043
theorem B7952903 : Blo 1044610 7952903 := bstep (se 1 (by rfl) ⟨5964677, by rfl⟩ : syracuseStep 7952903 = 11929355) B11929355
theorem B3529385 : Blo 1044610 3529385 := bstep (se 2 (by rfl) ⟨1323519, by rfl⟩ : syracuseStep 3529385 = 2647039) B2647039
theorem B2120575 : Blo 1044610 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B2645369 : Blo 1044610 2645369 := bstep (se 2 (by rfl) ⟨992013, by rfl⟩ : syracuseStep 2645369 = 1984027) B1984027
theorem B20144321 : Blo 1044610 20144321 := bstep (se 2 (by rfl) ⟨7554120, by rfl⟩ : syracuseStep 20144321 = 15108241) B15108241
theorem B2351519 : Blo 1044610 2351519 := bstep (se 1 (by rfl) ⟨1763639, by rfl⟩ : syracuseStep 2351519 = 3527279) B3527279
theorem B5038985 : Blo 1044610 5038985 := bstep (se 2 (by rfl) ⟨1889619, by rfl⟩ : syracuseStep 5038985 = 3779239) B3779239
theorem B2975231 : Blo 1044610 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B2352887 : Blo 1044610 2352887 := bstep (se 1 (by rfl) ⟨1764665, by rfl⟩ : syracuseStep 2352887 = 3529331) B3529331
theorem B2647799 : Blo 1044610 2647799 := bstep (se 1 (by rfl) ⟨1985849, by rfl⟩ : syracuseStep 2647799 = 3971699) B3971699
theorem B25421597 : Blo 1044610 25421597 := bstep (se 3 (by rfl) ⟨4766549, by rfl⟩ : syracuseStep 25421597 = 9533099) B9533099
theorem B25782155 : Blo 1044610 25782155 := bstep (se 1 (by rfl) ⟨19336616, by rfl⟩ : syracuseStep 25782155 = 38673233) B38673233
theorem B3532841 : Blo 1044610 3532841 := bstep (se 2 (by rfl) ⟨1324815, by rfl⟩ : syracuseStep 3532841 = 2649631) B2649631
theorem B1763383 : Blo 1044610 1763383 := bstep (se 1 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 1763383 = 2645075) B2645075
theorem B3533111 : Blo 1044610 3533111 := bstep (se 1 (by rfl) ⟨2649833, by rfl⟩ : syracuseStep 3533111 = 5299667) B5299667
theorem B7956791 : Blo 1044610 7956791 := bstep (se 1 (by rfl) ⟨5967593, by rfl⟩ : syracuseStep 7956791 = 11935187) B11935187
theorem B9660799 : Blo 1044610 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B1567103 : Blo 1044610 1567103 := bstep (se 1 (by rfl) ⟨1175327, by rfl⟩ : syracuseStep 1567103 = 2350655) B2350655
theorem B245164529 : Blo 1044610 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B122546803 : Blo 1044610 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B1567439 : Blo 1044610 1567439 := bstep (se 1 (by rfl) ⟨1175579, by rfl⟩ : syracuseStep 1567439 = 2351159) B2351159
theorem B1567487 : Blo 1044610 1567487 := bstep (se 1 (by rfl) ⟨1175615, by rfl⟩ : syracuseStep 1567487 = 2351231) B2351231
theorem B5663519 : Blo 1044610 5663519 := bstep (se 1 (by rfl) ⟨4247639, by rfl⟩ : syracuseStep 5663519 = 8495279) B8495279
theorem B1567535 : Blo 1044610 1567535 := bstep (se 1 (by rfl) ⟨1175651, by rfl⟩ : syracuseStep 1567535 = 2351303) B2351303
theorem B2354003 : Blo 1044610 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B3402665 : Blo 1044610 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B1567835 : Blo 1044610 1567835 := bstep (se 1 (by rfl) ⟨1175876, by rfl⟩ : syracuseStep 1567835 = 2351753) B2351753
theorem B1764443 : Blo 1044610 1764443 := bstep (se 1 (by rfl) ⟨1323332, by rfl⟩ : syracuseStep 1764443 = 2646665) B2646665
theorem B1764841 : Blo 1044610 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B1764895 : Blo 1044610 1764895 := bstep (se 1 (by rfl) ⟨1323671, by rfl⟩ : syracuseStep 1764895 = 2647343) B2647343
theorem B1568423 : Blo 1044610 1568423 := bstep (se 1 (by rfl) ⟨1176317, by rfl⟩ : syracuseStep 1568423 = 2352635) B2352635
theorem B1568495 : Blo 1044610 1568495 := bstep (se 1 (by rfl) ⟨1176371, by rfl⟩ : syracuseStep 1568495 = 2352743) B2352743
theorem B2518771 : Blo 1044610 2518771 := bstep (se 1 (by rfl) ⟨1889078, by rfl⟩ : syracuseStep 2518771 = 3778157) B3778157
theorem B1568711 : Blo 1044610 1568711 := bstep (se 1 (by rfl) ⟨1176533, by rfl⟩ : syracuseStep 1568711 = 2353067) B2353067
theorem B45936827 : Blo 1044610 45936827 := bstep (se 1 (by rfl) ⟨34452620, by rfl⟩ : syracuseStep 45936827 = 68905241) B68905241
theorem B2355425 : Blo 1044610 2355425 := bstep (se 2 (by rfl) ⟨883284, by rfl⟩ : syracuseStep 2355425 = 1766569) B1766569
theorem B1569215 : Blo 1044610 1569215 := bstep (se 1 (by rfl) ⟨1176911, by rfl⟩ : syracuseStep 1569215 = 2353823) B2353823
theorem B11203069 : Blo 1044610 11203069 := bstep (se 3 (by rfl) ⟨2100575, by rfl⟩ : syracuseStep 11203069 = 4201151) B4201151
theorem B1569407 : Blo 1044610 1569407 := bstep (se 1 (by rfl) ⟨1177055, by rfl⟩ : syracuseStep 1569407 = 2354111) B2354111
theorem B1569575 : Blo 1044610 1569575 := bstep (se 1 (by rfl) ⟨1177181, by rfl⟩ : syracuseStep 1569575 = 2354363) B2354363
theorem B1176511 : Blo 1044610 1176511 := bstep (se 1 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 1176511 = 1764767) B1764767
theorem B29389853 : Blo 1044610 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B1045607 : Blo 1044610 1045607 := bstep (se 1 (by rfl) ⟨784205, by rfl⟩ : syracuseStep 1045607 = 1568411) B1568411
theorem B57209975 : Blo 1044610 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B2356361 : Blo 1044610 2356361 := bstep (se 2 (by rfl) ⟨883635, by rfl⟩ : syracuseStep 2356361 = 1767271) B1767271
theorem B1045735 : Blo 1044610 1045735 := bstep (se 1 (by rfl) ⟨784301, by rfl⟩ : syracuseStep 1045735 = 1568603) B1568603
theorem B8942885 : Blo 1044610 8942885 := bstep (se 4 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 8942885 = 1676791) B1676791
theorem B1045919 : Blo 1044610 1045919 := bstep (se 1 (by rfl) ⟨784439, by rfl⟩ : syracuseStep 1045919 = 1568879) B1568879
theorem B1570511 : Blo 1044610 1570511 := bstep (se 1 (by rfl) ⟨1177883, by rfl⟩ : syracuseStep 1570511 = 2355767) B2355767
theorem B1046463 : Blo 1044610 1046463 := bstep (se 1 (by rfl) ⟨784847, by rfl⟩ : syracuseStep 1046463 = 1569695) B1569695
theorem B1046619 : Blo 1044610 1046619 := bstep (se 1 (by rfl) ⟨784964, by rfl⟩ : syracuseStep 1046619 = 1569929) B1569929
theorem B1570919 : Blo 1044610 1570919 := bstep (se 1 (by rfl) ⟨1178189, by rfl⟩ : syracuseStep 1570919 = 2356379) B2356379
theorem B5306471 : Blo 1044610 5306471 := bstep (se 1 (by rfl) ⟨3979853, by rfl⟩ : syracuseStep 5306471 = 7959707) B7959707
theorem B1177807 : Blo 1044610 1177807 := bstep (se 1 (by rfl) ⟨883355, by rfl⟩ : syracuseStep 1177807 = 1766711) B1766711
theorem B1046783 : Blo 1044610 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B1571099 : Blo 1044610 1571099 := bstep (se 1 (by rfl) ⟨1178324, by rfl⟩ : syracuseStep 1571099 = 2356649) B2356649
theorem B7174439 : Blo 1044610 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B1571135 : Blo 1044610 1571135 := bstep (se 1 (by rfl) ⟨1178351, by rfl⟩ : syracuseStep 1571135 = 2356703) B2356703
theorem B3537215 : Blo 1044610 3537215 := bstep (se 1 (by rfl) ⟨2652911, by rfl⟩ : syracuseStep 3537215 = 5305823) B5305823
theorem B3766625 : Blo 1044610 3766625 := bstep (se 2 (by rfl) ⟨1412484, by rfl⟩ : syracuseStep 3766625 = 2824969) B2824969
theorem B1571567 : Blo 1044610 1571567 := bstep (se 1 (by rfl) ⟨1178675, by rfl⟩ : syracuseStep 1571567 = 2357351) B2357351
theorem B1047359 : Blo 1044610 1047359 := bstep (se 1 (by rfl) ⟨785519, by rfl⟩ : syracuseStep 1047359 = 1571039) B1571039
theorem B1047679 : Blo 1044610 1047679 := bstep (se 1 (by rfl) ⟨785759, by rfl⟩ : syracuseStep 1047679 = 1571519) B1571519
theorem B1047967 : Blo 1044610 1047967 := bstep (se 1 (by rfl) ⟨785975, by rfl⟩ : syracuseStep 1047967 = 1571951) B1571951
theorem B1179103 : Blo 1044610 1179103 := bstep (se 1 (by rfl) ⟨884327, by rfl⟩ : syracuseStep 1179103 = 1768655) B1768655
theorem B40271417 : Blo 1044610 40271417 := bstep (se 2 (by rfl) ⟨15101781, by rfl⟩ : syracuseStep 40271417 = 30203563) B30203563
theorem B20119103 : Blo 1044610 20119103 := bstep (se 1 (by rfl) ⟨15089327, by rfl⟩ : syracuseStep 20119103 = 30178655) B30178655
theorem B3538889 : Blo 1044610 3538889 := bstep (se 2 (by rfl) ⟨1327083, by rfl⟩ : syracuseStep 3538889 = 2654167) B2654167
theorem B13434983 : Blo 1044610 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B3539051 : Blo 1044610 3539051 := bstep (se 1 (by rfl) ⟨2654288, by rfl⟩ : syracuseStep 3539051 = 5308577) B5308577
theorem B12881065 : Blo 1044610 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B7933949 : Blo 1044610 7933949 := bstep (se 3 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 7933949 = 2975231) B2975231
theorem B2234089 : Blo 1044610 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B16947731 : Blo 1044610 16947731 := bstep (se 1 (by rfl) ⟨12710798, by rfl⟩ : syracuseStep 16947731 = 25421597) B25421597
theorem B2234927 : Blo 1044610 2234927 := bstep (se 1 (by rfl) ⟨1676195, by rfl⟩ : syracuseStep 2234927 = 3352391) B3352391
theorem B2235559 : Blo 1044610 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B3775679 : Blo 1044610 3775679 := bstep (se 1 (by rfl) ⟨2831759, by rfl⟩ : syracuseStep 3775679 = 5663519) B5663519
theorem B2268443 : Blo 1044610 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B4529695 : Blo 1044610 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B2237267 : Blo 1044610 2237267 := bstep (se 1 (by rfl) ⟨1677950, by rfl⟩ : syracuseStep 2237267 = 3355901) B3355901
theorem B2827433 : Blo 1044610 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B26847611 : Blo 1044610 26847611 := bstep (se 1 (by rfl) ⟨20135708, by rfl⟩ : syracuseStep 26847611 = 40271417) B40271417
theorem B13412735 : Blo 1044610 13412735 := bstep (se 1 (by rfl) ⟨10059551, by rfl⟩ : syracuseStep 13412735 = 20119103) B20119103
theorem B8497871 : Blo 1044610 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B8924327 : Blo 1044610 8924327 := bstep (se 1 (by rfl) ⟨6693245, by rfl⟩ : syracuseStep 8924327 = 13386491) B13386491
theorem B3354671 : Blo 1044610 3354671 := bstep (se 1 (by rfl) ⟨2516003, by rfl⟩ : syracuseStep 3354671 = 5032007) B5032007
theorem B4469033 : Blo 1044610 4469033 := bstep (se 2 (by rfl) ⟨1675887, by rfl⟩ : syracuseStep 4469033 = 3351775) B3351775
theorem B371831323 : Blo 1044610 371831323 := bstep (se 1 (by rfl) ⟨278873492, by rfl⟩ : syracuseStep 371831323 = 557746985) B557746985
theorem B163395737 : Blo 1044610 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B5291567 : Blo 1044610 5291567 := bstep (se 1 (by rfl) ⟨3968675, by rfl⟩ : syracuseStep 5291567 = 7937351) B7937351
theorem B3358361 : Blo 1044610 3358361 := bstep (se 2 (by rfl) ⟨1259385, by rfl⟩ : syracuseStep 3358361 = 2518771) B2518771
theorem B1884263 : Blo 1044610 1884263 := bstep (se 1 (by rfl) ⟨1413197, by rfl⟩ : syracuseStep 1884263 = 2826395) B2826395
theorem B3359323 : Blo 1044610 3359323 := bstep (se 1 (by rfl) ⟨2519492, by rfl⟩ : syracuseStep 3359323 = 5038985) B5038985
theorem B5292701 : Blo 1044610 5292701 := bstep (se 3 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 5292701 = 1984763) B1984763
theorem B5293025 : Blo 1044610 5293025 := bstep (se 2 (by rfl) ⟨1984884, by rfl⟩ : syracuseStep 5293025 = 3969769) B3969769
theorem B17188103 : Blo 1044610 17188103 := bstep (se 1 (by rfl) ⟨12891077, by rfl⟩ : syracuseStep 17188103 = 25782155) B25782155
theorem B5031391 : Blo 1044610 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B5293835 : Blo 1044610 5293835 := bstep (se 1 (by rfl) ⟨3970376, by rfl⟩ : syracuseStep 5293835 = 7940753) B7940753
theorem B20368037 : Blo 1044610 20368037 := bstep (se 4 (by rfl) ⟨1909503, by rfl⟩ : syracuseStep 20368037 = 3819007) B3819007
theorem B30624551 : Blo 1044610 30624551 := bstep (se 1 (by rfl) ⟨22968413, by rfl⟩ : syracuseStep 30624551 = 45936827) B45936827
theorem B5951009 : Blo 1044610 5951009 := bstep (se 2 (by rfl) ⟨2231628, by rfl⟩ : syracuseStep 5951009 = 4463257) B4463257
theorem B2511083 : Blo 1044610 2511083 := bstep (se 1 (by rfl) ⟨1883312, by rfl⟩ : syracuseStep 2511083 = 3766625) B3766625
theorem B5296427 : Blo 1044610 5296427 := bstep (se 1 (by rfl) ⟨3972320, by rfl⟩ : syracuseStep 5296427 = 7944641) B7944641
theorem B4772591 : Blo 1044610 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B19321825 : Blo 1044610 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B5953607 : Blo 1044610 5953607 := bstep (se 1 (by rfl) ⟨4465205, by rfl⟩ : syracuseStep 5953607 = 8930411) B8930411
theorem B34003921 : Blo 1044610 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B16309349 : Blo 1044610 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B3530141 : Blo 1044610 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B2645743 : Blo 1044610 2645743 := bstep (se 1 (by rfl) ⟨1984307, by rfl⟩ : syracuseStep 2645743 = 3968615) B3968615
theorem B408641543 : Blo 1044610 408641543 := bstep (se 1 (by rfl) ⟨306481157, by rfl⟩ : syracuseStep 408641543 = 612962315) B612962315
theorem B2351177 : Blo 1044610 2351177 := bstep (se 2 (by rfl) ⟨881691, by rfl⟩ : syracuseStep 2351177 = 1763383) B1763383
theorem B6709625 : Blo 1044610 6709625 := bstep (se 2 (by rfl) ⟨2516109, by rfl⟩ : syracuseStep 6709625 = 5032219) B5032219
theorem B2515369 : Blo 1044610 2515369 := bstep (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) B1886527
theorem B5301287 : Blo 1044610 5301287 := bstep (se 1 (by rfl) ⟨3975965, by rfl⟩ : syracuseStep 5301287 = 7951931) B7951931
theorem B40232051 : Blo 1044610 40232051 := bstep (se 1 (by rfl) ⟨30174038, by rfl⟩ : syracuseStep 40232051 = 60348077) B60348077
theorem B4023809 : Blo 1044610 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B65431079 : Blo 1044610 65431079 := bstep (se 1 (by rfl) ⟨49073309, by rfl⟩ : syracuseStep 65431079 = 98146619) B98146619
theorem B3532463 : Blo 1044610 3532463 := bstep (se 1 (by rfl) ⟨2649347, by rfl⟩ : syracuseStep 3532463 = 5298695) B5298695
theorem B5301935 : Blo 1044610 5301935 := bstep (se 1 (by rfl) ⟨3976451, by rfl⟩ : syracuseStep 5301935 = 7952903) B7952903
theorem B2352923 : Blo 1044610 2352923 := bstep (se 1 (by rfl) ⟨1764692, by rfl⟩ : syracuseStep 2352923 = 3529385) B3529385
theorem B2353121 : Blo 1044610 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B2353193 : Blo 1044610 2353193 := bstep (se 2 (by rfl) ⟨882447, by rfl⟩ : syracuseStep 2353193 = 1764895) B1764895
theorem B1763579 : Blo 1044610 1763579 := bstep (se 1 (by rfl) ⟨1322684, by rfl⟩ : syracuseStep 1763579 = 2645369) B2645369
theorem B13429547 : Blo 1044610 13429547 := bstep (se 1 (by rfl) ⟨10072160, by rfl⟩ : syracuseStep 13429547 = 20144321) B20144321
theorem B1567679 : Blo 1044610 1567679 := bstep (se 1 (by rfl) ⟨1175759, by rfl⟩ : syracuseStep 1567679 = 2351519) B2351519
theorem B14937425 : Blo 1044610 14937425 := bstep (se 2 (by rfl) ⟨5601534, by rfl⟩ : syracuseStep 14937425 = 11203069) B11203069
theorem B1568591 : Blo 1044610 1568591 := bstep (se 1 (by rfl) ⟨1176443, by rfl⟩ : syracuseStep 1568591 = 2352887) B2352887
theorem B1765199 : Blo 1044610 1765199 := bstep (se 1 (by rfl) ⟨1323899, by rfl⟩ : syracuseStep 1765199 = 2647799) B2647799
theorem B1568681 : Blo 1044610 1568681 := bstep (se 2 (by rfl) ⟨588255, by rfl⟩ : syracuseStep 1568681 = 1176511) B1176511
theorem B2355227 : Blo 1044610 2355227 := bstep (se 1 (by rfl) ⟨1766420, by rfl⟩ : syracuseStep 2355227 = 3532841) B3532841
theorem B2355407 : Blo 1044610 2355407 := bstep (se 1 (by rfl) ⟨1766555, by rfl⟩ : syracuseStep 2355407 = 3533111) B3533111
theorem B5304527 : Blo 1044610 5304527 := bstep (se 1 (by rfl) ⟨3978395, by rfl⟩ : syracuseStep 5304527 = 7956791) B7956791
theorem B1044735 : Blo 1044610 1044735 := bstep (se 1 (by rfl) ⟨783551, by rfl⟩ : syracuseStep 1044735 = 1567103) B1567103
theorem B163443019 : Blo 1044610 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B1044959 : Blo 1044610 1044959 := bstep (se 1 (by rfl) ⟨783719, by rfl⟩ : syracuseStep 1044959 = 1567439) B1567439
theorem B1044991 : Blo 1044610 1044991 := bstep (se 1 (by rfl) ⟨783743, by rfl⟩ : syracuseStep 1044991 = 1567487) B1567487
theorem B1045023 : Blo 1044610 1045023 := bstep (se 1 (by rfl) ⟨783767, by rfl⟩ : syracuseStep 1045023 = 1567535) B1567535
theorem B1569335 : Blo 1044610 1569335 := bstep (se 1 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 1569335 = 2354003) B2354003
theorem B1045223 : Blo 1044610 1045223 := bstep (se 1 (by rfl) ⟨783917, by rfl⟩ : syracuseStep 1045223 = 1567835) B1567835
theorem B1176295 : Blo 1044610 1176295 := bstep (se 1 (by rfl) ⟨882221, by rfl⟩ : syracuseStep 1176295 = 1764443) B1764443
theorem B2651039 : Blo 1044610 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B1045615 : Blo 1044610 1045615 := bstep (se 1 (by rfl) ⟨784211, by rfl⟩ : syracuseStep 1045615 = 1568423) B1568423
theorem B1045663 : Blo 1044610 1045663 := bstep (se 1 (by rfl) ⟨784247, by rfl⟩ : syracuseStep 1045663 = 1568495) B1568495
theorem B1045807 : Blo 1044610 1045807 := bstep (se 1 (by rfl) ⟨784355, by rfl⟩ : syracuseStep 1045807 = 1568711) B1568711
theorem B1570283 : Blo 1044610 1570283 := bstep (se 1 (by rfl) ⟨1177712, by rfl⟩ : syracuseStep 1570283 = 2355425) B2355425
theorem B1570409 : Blo 1044610 1570409 := bstep (se 2 (by rfl) ⟨588903, by rfl⟩ : syracuseStep 1570409 = 1177807) B1177807
theorem B1046143 : Blo 1044610 1046143 := bstep (se 1 (by rfl) ⟨784607, by rfl⟩ : syracuseStep 1046143 = 1569215) B1569215
theorem B15300343 : Blo 1044610 15300343 := bstep (se 1 (by rfl) ⟨11475257, by rfl⟩ : syracuseStep 15300343 = 22950515) B22950515
theorem B1046271 : Blo 1044610 1046271 := bstep (se 1 (by rfl) ⟨784703, by rfl⟩ : syracuseStep 1046271 = 1569407) B1569407
theorem B1046383 : Blo 1044610 1046383 := bstep (se 1 (by rfl) ⟨784787, by rfl⟩ : syracuseStep 1046383 = 1569575) B1569575
theorem B19593235 : Blo 1044610 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B2652223 : Blo 1044610 2652223 := bstep (se 1 (by rfl) ⟨1989167, by rfl⟩ : syracuseStep 2652223 = 3978335) B3978335
theorem B38139983 : Blo 1044610 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B1570907 : Blo 1044610 1570907 := bstep (se 1 (by rfl) ⟨1178180, by rfl⟩ : syracuseStep 1570907 = 2356361) B2356361
theorem B5961923 : Blo 1044610 5961923 := bstep (se 1 (by rfl) ⟨4471442, by rfl⟩ : syracuseStep 5961923 = 8942885) B8942885
theorem B1047007 : Blo 1044610 1047007 := bstep (se 1 (by rfl) ⟨785255, by rfl⟩ : syracuseStep 1047007 = 1570511) B1570511
theorem B8944283 : Blo 1044610 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B3177119 : Blo 1044610 3177119 := bstep (se 1 (by rfl) ⟨2382839, by rfl⟩ : syracuseStep 3177119 = 4765679) B4765679
theorem B20151017 : Blo 1044610 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B1047279 : Blo 1044610 1047279 := bstep (se 1 (by rfl) ⟨785459, by rfl⟩ : syracuseStep 1047279 = 1570919) B1570919
theorem B3537647 : Blo 1044610 3537647 := bstep (se 1 (by rfl) ⟨2653235, by rfl⟩ : syracuseStep 3537647 = 5306471) B5306471
theorem B1047399 : Blo 1044610 1047399 := bstep (se 1 (by rfl) ⟨785549, by rfl⟩ : syracuseStep 1047399 = 1571099) B1571099
theorem B4782959 : Blo 1044610 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B1047423 : Blo 1044610 1047423 := bstep (se 1 (by rfl) ⟨785567, by rfl⟩ : syracuseStep 1047423 = 1571135) B1571135
theorem B2358143 : Blo 1044610 2358143 := bstep (se 1 (by rfl) ⟨1768607, by rfl⟩ : syracuseStep 2358143 = 3537215) B3537215
theorem B1047711 : Blo 1044610 1047711 := bstep (se 1 (by rfl) ⟨785783, by rfl⟩ : syracuseStep 1047711 = 1571567) B1571567
theorem B1572137 : Blo 1044610 1572137 := bstep (se 2 (by rfl) ⟨589551, by rfl⟩ : syracuseStep 1572137 = 1179103) B1179103
theorem B2359259 : Blo 1044610 2359259 := bstep (se 1 (by rfl) ⟨1769444, by rfl⟩ : syracuseStep 2359259 = 3538889) B3538889
theorem B2359367 : Blo 1044610 2359367 := bstep (se 1 (by rfl) ⟨1769525, by rfl⟩ : syracuseStep 2359367 = 3539051) B3539051
theorem B104497253 : Blo 1044610 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B20416367 : Blo 1044610 20416367 := bstep (se 1 (by rfl) ⟨15312275, by rfl⟩ : syracuseStep 20416367 = 30624551) B30624551
theorem B5966045 : Blo 1044610 5966045 := bstep (se 3 (by rfl) ⟨1118633, by rfl⟩ : syracuseStep 5966045 = 2237267) B2237267
theorem B3967339 : Blo 1044610 3967339 := bstep (se 1 (by rfl) ⟨2975504, by rfl⟩ : syracuseStep 3967339 = 5951009) B5951009
theorem B1674055 : Blo 1044610 1674055 := bstep (se 1 (by rfl) ⟨1255541, by rfl⟩ : syracuseStep 1674055 = 2511083) B2511083
theorem B3181727 : Blo 1044610 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B3969071 : Blo 1044610 3969071 := bstep (se 1 (by rfl) ⟨2976803, by rfl⟩ : syracuseStep 3969071 = 5953607) B5953607
theorem B17174753 : Blo 1044610 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B43620719 : Blo 1044610 43620719 := bstep (se 1 (by rfl) ⟨32715539, by rfl⟩ : syracuseStep 43620719 = 65431079) B65431079
theorem B25762433 : Blo 1044610 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B17898407 : Blo 1044610 17898407 := bstep (se 1 (by rfl) ⟨13423805, by rfl⟩ : syracuseStep 17898407 = 26847611) B26847611
theorem B8953031 : Blo 1044610 8953031 := bstep (se 1 (by rfl) ⟨6714773, by rfl⟩ : syracuseStep 8953031 = 13429547) B13429547
theorem B2236447 : Blo 1044610 2236447 := bstep (se 1 (by rfl) ⟨1677335, by rfl⟩ : syracuseStep 2236447 = 3354671) B3354671
theorem B108930491 : Blo 1044610 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B3974615 : Blo 1044610 3974615 := bstep (se 1 (by rfl) ⟨2980961, by rfl⟩ : syracuseStep 3974615 = 5961923) B5961923
theorem B8955629 : Blo 1044610 8955629 := bstep (se 3 (by rfl) ⟨1679180, by rfl⟩ : syracuseStep 8955629 = 3358361) B3358361
theorem B3188639 : Blo 1044610 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B6039593 : Blo 1044610 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B8956655 : Blo 1044610 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B5024701 : Blo 1044610 5024701 := bstep (se 3 (by rfl) ⟨942131, by rfl⟩ : syracuseStep 5024701 = 1884263) B1884263
theorem B3353825 : Blo 1044610 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B13578691 : Blo 1044610 13578691 := bstep (se 1 (by rfl) ⟨10184018, by rfl⟩ : syracuseStep 13578691 = 20368037) B20368037
theorem B5289299 : Blo 1044610 5289299 := bstep (se 1 (by rfl) ⟨3966974, by rfl⟩ : syracuseStep 5289299 = 7933949) B7933949
theorem B1489951 : Blo 1044610 1489951 := bstep (se 1 (by rfl) ⟨1117463, by rfl⟩ : syracuseStep 1489951 = 2234927) B2234927
theorem B4473083 : Blo 1044610 4473083 := bstep (se 1 (by rfl) ⟨3354812, by rfl⟩ : syracuseStep 4473083 = 6709625) B6709625
theorem B217924025 : Blo 1044610 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B26821367 : Blo 1044610 26821367 := bstep (se 1 (by rfl) ⟨20116025, by rfl⟩ : syracuseStep 26821367 = 40232051) B40232051
theorem B1884955 : Blo 1044610 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B5949551 : Blo 1044610 5949551 := bstep (se 1 (by rfl) ⟨4462163, by rfl⟩ : syracuseStep 5949551 = 8924327) B8924327
theorem B20400457 : Blo 1044610 20400457 := bstep (se 2 (by rfl) ⟨7650171, by rfl⟩ : syracuseStep 20400457 = 15300343) B15300343
theorem B6049181 : Blo 1044610 6049181 := bstep (se 3 (by rfl) ⟨1134221, by rfl⟩ : syracuseStep 6049181 = 2268443) B2268443
theorem B45338561 : Blo 1044610 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B2118079 : Blo 1044610 2118079 := bstep (se 1 (by rfl) ⟨1588559, by rfl⟩ : syracuseStep 2118079 = 3177119) B3177119
theorem B3527657 : Blo 1044610 3527657 := bstep (se 2 (by rfl) ⟨1322871, by rfl⟩ : syracuseStep 3527657 = 2645743) B2645743
theorem B3527711 : Blo 1044610 3527711 := bstep (se 1 (by rfl) ⟨2645783, by rfl⟩ : syracuseStep 3527711 = 5291567) B5291567
theorem B3528467 : Blo 1044610 3528467 := bstep (se 1 (by rfl) ⟨2646350, by rfl⟩ : syracuseStep 3528467 = 5292701) B5292701
theorem B3528683 : Blo 1044610 3528683 := bstep (se 1 (by rfl) ⟨2646512, by rfl⟩ : syracuseStep 3528683 = 5293025) B5293025
theorem B4479097 : Blo 1044610 4479097 := bstep (se 2 (by rfl) ⟨1679661, by rfl⟩ : syracuseStep 4479097 = 3359323) B3359323
theorem B3529223 : Blo 1044610 3529223 := bstep (se 1 (by rfl) ⟨2646917, by rfl⟩ : syracuseStep 3529223 = 5293835) B5293835
theorem B6708521 : Blo 1044610 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B3530951 : Blo 1044610 3530951 := bstep (se 1 (by rfl) ⟨2648213, by rfl⟩ : syracuseStep 3530951 = 5296427) B5296427
theorem B45834941 : Blo 1044610 45834941 := bstep (se 3 (by rfl) ⟨8594051, by rfl⟩ : syracuseStep 45834941 = 17188103) B17188103
theorem B11298487 : Blo 1044610 11298487 := bstep (se 1 (by rfl) ⟨8473865, by rfl⟩ : syracuseStep 11298487 = 16947731) B16947731
theorem B10872899 : Blo 1044610 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B2517119 : Blo 1044610 2517119 := bstep (se 1 (by rfl) ⟨1887839, by rfl⟩ : syracuseStep 2517119 = 3775679) B3775679
theorem B2353427 : Blo 1044610 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B272427695 : Blo 1044610 272427695 := bstep (se 1 (by rfl) ⟨204320771, by rfl⟩ : syracuseStep 272427695 = 408641543) B408641543
theorem B1567451 : Blo 1044610 1567451 := bstep (se 1 (by rfl) ⟨1175588, by rfl⟩ : syracuseStep 1567451 = 2351177) B2351177
theorem B3534191 : Blo 1044610 3534191 := bstep (se 1 (by rfl) ⟨2650643, by rfl⟩ : syracuseStep 3534191 = 5301287) B5301287
theorem B495775097 : Blo 1044610 495775097 := bstep (se 2 (by rfl) ⟨185915661, by rfl⟩ : syracuseStep 495775097 = 371831323) B371831323
theorem B1568393 : Blo 1044610 1568393 := bstep (se 2 (by rfl) ⟨588147, by rfl⟩ : syracuseStep 1568393 = 1176295) B1176295
theorem B2682539 : Blo 1044610 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B2354975 : Blo 1044610 2354975 := bstep (se 1 (by rfl) ⟨1766231, by rfl⟩ : syracuseStep 2354975 = 3532463) B3532463
theorem B3534623 : Blo 1044610 3534623 := bstep (se 1 (by rfl) ⟨2650967, by rfl⟩ : syracuseStep 3534623 = 5301935) B5301935
theorem B1568615 : Blo 1044610 1568615 := bstep (se 1 (by rfl) ⟨1176461, by rfl⟩ : syracuseStep 1568615 = 2352923) B2352923
theorem B1568747 : Blo 1044610 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B1568795 : Blo 1044610 1568795 := bstep (se 1 (by rfl) ⟨1176596, by rfl⟩ : syracuseStep 1568795 = 2353193) B2353193
theorem B1175719 : Blo 1044610 1175719 := bstep (se 1 (by rfl) ⟨881789, by rfl⟩ : syracuseStep 1175719 = 1763579) B1763579
theorem B8941823 : Blo 1044610 8941823 := bstep (se 1 (by rfl) ⟨6706367, by rfl⟩ : syracuseStep 8941823 = 13412735) B13412735
theorem B5665247 : Blo 1044610 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B1045119 : Blo 1044610 1045119 := bstep (se 1 (by rfl) ⟨783839, by rfl⟩ : syracuseStep 1045119 = 1567679) B1567679
theorem B9958283 : Blo 1044610 9958283 := bstep (se 1 (by rfl) ⟨7468712, by rfl⟩ : syracuseStep 9958283 = 14937425) B14937425
theorem B2978785 : Blo 1044610 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B1045727 : Blo 1044610 1045727 := bstep (se 1 (by rfl) ⟨784295, by rfl⟩ : syracuseStep 1045727 = 1568591) B1568591
theorem B1176799 : Blo 1044610 1176799 := bstep (se 1 (by rfl) ⟨882599, by rfl⟩ : syracuseStep 1176799 = 1765199) B1765199
theorem B1045787 : Blo 1044610 1045787 := bstep (se 1 (by rfl) ⟨784340, by rfl⟩ : syracuseStep 1045787 = 1568681) B1568681
theorem B1570151 : Blo 1044610 1570151 := bstep (se 1 (by rfl) ⟨1177613, by rfl⟩ : syracuseStep 1570151 = 2355227) B2355227
theorem B3536297 : Blo 1044610 3536297 := bstep (se 2 (by rfl) ⟨1326111, by rfl⟩ : syracuseStep 3536297 = 2652223) B2652223
theorem B1570271 : Blo 1044610 1570271 := bstep (se 1 (by rfl) ⟨1177703, by rfl⟩ : syracuseStep 1570271 = 2355407) B2355407
theorem B3536351 : Blo 1044610 3536351 := bstep (se 1 (by rfl) ⟨2652263, by rfl⟩ : syracuseStep 3536351 = 5304527) B5304527
theorem B2979355 : Blo 1044610 2979355 := bstep (se 1 (by rfl) ⟨2234516, by rfl⟩ : syracuseStep 2979355 = 4469033) B4469033
theorem B1046223 : Blo 1044610 1046223 := bstep (se 1 (by rfl) ⟨784667, by rfl⟩ : syracuseStep 1046223 = 1569335) B1569335
theorem B1767359 : Blo 1044610 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B1046855 : Blo 1044610 1046855 := bstep (se 1 (by rfl) ⟨785141, by rfl⟩ : syracuseStep 1046855 = 1570283) B1570283
theorem B1046939 : Blo 1044610 1046939 := bstep (se 1 (by rfl) ⟨785204, by rfl⟩ : syracuseStep 1046939 = 1570409) B1570409
theorem B25426655 : Blo 1044610 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B1047271 : Blo 1044610 1047271 := bstep (se 1 (by rfl) ⟨785453, by rfl⟩ : syracuseStep 1047271 = 1570907) B1570907
theorem B2980745 : Blo 1044610 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B5962855 : Blo 1044610 5962855 := bstep (se 1 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 5962855 = 8944283) B8944283
theorem B13434011 : Blo 1044610 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B2358431 : Blo 1044610 2358431 := bstep (se 1 (by rfl) ⟨1768823, by rfl⟩ : syracuseStep 2358431 = 3537647) B3537647
theorem B1572095 : Blo 1044610 1572095 := bstep (se 1 (by rfl) ⟨1179071, by rfl⟩ : syracuseStep 1572095 = 2358143) B2358143
theorem B1048091 : Blo 1044610 1048091 := bstep (se 1 (by rfl) ⟨786068, by rfl⟩ : syracuseStep 1048091 = 1572137) B1572137
theorem B1572839 : Blo 1044610 1572839 := bstep (se 1 (by rfl) ⟨1179629, by rfl⟩ : syracuseStep 1572839 = 2359259) B2359259
theorem B2981929 : Blo 1044610 2981929 := bstep (se 2 (by rfl) ⟨1118223, by rfl⟩ : syracuseStep 2981929 = 2236447) B2236447
theorem B1572911 : Blo 1044610 1572911 := bstep (se 1 (by rfl) ⟨1179683, by rfl⟩ : syracuseStep 1572911 = 2359367) B2359367
theorem B69664835 : Blo 1044610 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B2982055 : Blo 1044610 2982055 := bstep (se 1 (by rfl) ⟨2236541, by rfl⟩ : syracuseStep 2982055 = 4473083) B4473083
theorem B3966367 : Blo 1044610 3966367 := bstep (se 1 (by rfl) ⟨2974775, by rfl⟩ : syracuseStep 3966367 = 5949551) B5949551
theorem B122226509 : Blo 1044610 122226509 := bstep (se 3 (by rfl) ⟨22917470, by rfl⟩ : syracuseStep 122226509 = 45834941) B45834941
theorem B4032787 : Blo 1044610 4032787 := bstep (se 1 (by rfl) ⟨3024590, by rfl⟩ : syracuseStep 4032787 = 6049181) B6049181
theorem B27200609 : Blo 1044610 27200609 := bstep (se 2 (by rfl) ⟨10200228, by rfl⟩ : syracuseStep 27200609 = 20400457) B20400457
theorem B2232073 : Blo 1044610 2232073 := bstep (se 2 (by rfl) ⟨837027, by rfl⟩ : syracuseStep 2232073 = 1674055) B1674055
theorem B11932271 : Blo 1044610 11932271 := bstep (se 1 (by rfl) ⟨8949203, by rfl⟩ : syracuseStep 11932271 = 17898407) B17898407
theorem B5968687 : Blo 1044610 5968687 := bstep (se 1 (by rfl) ⟨4476515, by rfl⟩ : syracuseStep 5968687 = 8953031) B8953031
theorem B2824105 : Blo 1044610 2824105 := bstep (se 2 (by rfl) ⟨1059039, by rfl⟩ : syracuseStep 2824105 = 2118079) B2118079
theorem B72620327 : Blo 1044610 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B5970419 : Blo 1044610 5970419 := bstep (se 1 (by rfl) ⟨4477814, by rfl⟩ : syracuseStep 5970419 = 8955629) B8955629
theorem B3971713 : Blo 1044610 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B7248599 : Blo 1044610 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B1678079 : Blo 1044610 1678079 := bstep (se 1 (by rfl) ⟨1258559, by rfl⟩ : syracuseStep 1678079 = 2517119) B2517119
theorem B5971103 : Blo 1044610 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B3972473 : Blo 1044610 3972473 := bstep (se 2 (by rfl) ⟨1489677, by rfl⟩ : syracuseStep 3972473 = 2979355) B2979355
theorem B5972129 : Blo 1044610 5972129 := bstep (se 2 (by rfl) ⟨2239548, by rfl⟩ : syracuseStep 5972129 = 4479097) B4479097
theorem B3776831 : Blo 1044610 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B16951103 : Blo 1044610 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B8956007 : Blo 1044610 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B13610911 : Blo 1044610 13610911 := bstep (se 1 (by rfl) ⟨10208183, by rfl⟩ : syracuseStep 13610911 = 20416367) B20416367
theorem B3977363 : Blo 1044610 3977363 := bstep (se 1 (by rfl) ⟨2983022, by rfl⟩ : syracuseStep 3977363 = 5966045) B5966045
theorem B30225707 : Blo 1044610 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B11449835 : Blo 1044610 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B5289785 : Blo 1044610 5289785 := bstep (se 2 (by rfl) ⟨1983669, by rfl⟩ : syracuseStep 5289785 = 3967339) B3967339
theorem B6699601 : Blo 1044610 6699601 := bstep (se 2 (by rfl) ⟨2512350, by rfl⟩ : syracuseStep 6699601 = 5024701) B5024701
theorem B4472347 : Blo 1044610 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B18104921 : Blo 1044610 18104921 := bstep (se 2 (by rfl) ⟨6789345, by rfl⟩ : syracuseStep 18104921 = 13578691) B13578691
theorem B68699821 : Blo 1044610 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B181618463 : Blo 1044610 181618463 := bstep (se 1 (by rfl) ⟨136213847, by rfl⟩ : syracuseStep 181618463 = 272427695) B272427695
theorem B330516731 : Blo 1044610 330516731 := bstep (se 1 (by rfl) ⟨247887548, by rfl⟩ : syracuseStep 330516731 = 495775097) B495775097
theorem B1788359 : Blo 1044610 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B6638855 : Blo 1044610 6638855 := bstep (se 1 (by rfl) ⟨4979141, by rfl⟩ : syracuseStep 6638855 = 9958283) B9958283
theorem B3526199 : Blo 1044610 3526199 := bstep (se 1 (by rfl) ⟨2644649, by rfl⟩ : syracuseStep 3526199 = 5289299) B5289299
theorem B1986601 : Blo 1044610 1986601 := bstep (se 2 (by rfl) ⟨744975, by rfl⟩ : syracuseStep 1986601 = 1489951) B1489951
theorem B7950473 : Blo 1044610 7950473 := bstep (se 2 (by rfl) ⟨2981427, by rfl⟩ : syracuseStep 7950473 = 5962855) B5962855
theorem B1987163 : Blo 1044610 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B17880911 : Blo 1044610 17880911 := bstep (se 1 (by rfl) ⟨13410683, by rfl⟩ : syracuseStep 17880911 = 26821367) B26821367
theorem B2513273 : Blo 1044610 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B2121151 : Blo 1044610 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B15064649 : Blo 1044610 15064649 := bstep (se 2 (by rfl) ⟨5649243, by rfl⟩ : syracuseStep 15064649 = 11298487) B11298487
theorem B2646047 : Blo 1044610 2646047 := bstep (se 1 (by rfl) ⟨1984535, by rfl⟩ : syracuseStep 2646047 = 3969071) B3969071
theorem B2351771 : Blo 1044610 2351771 := bstep (se 1 (by rfl) ⟨1763828, by rfl⟩ : syracuseStep 2351771 = 3527657) B3527657
theorem B2351807 : Blo 1044610 2351807 := bstep (se 1 (by rfl) ⟨1763855, by rfl⟩ : syracuseStep 2351807 = 3527711) B3527711
theorem B2352311 : Blo 1044610 2352311 := bstep (se 1 (by rfl) ⟨1764233, by rfl⟩ : syracuseStep 2352311 = 3528467) B3528467
theorem B2352455 : Blo 1044610 2352455 := bstep (se 1 (by rfl) ⟨1764341, by rfl⟩ : syracuseStep 2352455 = 3528683) B3528683
theorem B2352815 : Blo 1044610 2352815 := bstep (se 1 (by rfl) ⟨1764611, by rfl⟩ : syracuseStep 2352815 = 3529223) B3529223
theorem B2324522933 : Blo 1044610 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B2353967 : Blo 1044610 2353967 := bstep (se 1 (by rfl) ⟨1765475, by rfl⟩ : syracuseStep 2353967 = 3530951) B3530951
theorem B1567625 : Blo 1044610 1567625 := bstep (se 2 (by rfl) ⟨587859, by rfl⟩ : syracuseStep 1567625 = 1175719) B1175719
theorem B116321917 : Blo 1044610 116321917 := bstep (se 3 (by rfl) ⟨21810359, by rfl⟩ : syracuseStep 116321917 = 43620719) B43620719
theorem B2649743 : Blo 1044610 2649743 := bstep (se 1 (by rfl) ⟨1987307, by rfl⟩ : syracuseStep 2649743 = 3974615) B3974615
theorem B2125759 : Blo 1044610 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B4026395 : Blo 1044610 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B1568951 : Blo 1044610 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B1569065 : Blo 1044610 1569065 := bstep (se 2 (by rfl) ⟨588399, by rfl⟩ : syracuseStep 1569065 = 1176799) B1176799
theorem B1044967 : Blo 1044610 1044967 := bstep (se 1 (by rfl) ⟨783725, by rfl⟩ : syracuseStep 1044967 = 1567451) B1567451
theorem B2356127 : Blo 1044610 2356127 := bstep (se 1 (by rfl) ⟨1767095, by rfl⟩ : syracuseStep 2356127 = 3534191) B3534191
theorem B1045595 : Blo 1044610 1045595 := bstep (se 1 (by rfl) ⟨784196, by rfl⟩ : syracuseStep 1045595 = 1568393) B1568393
theorem B1569983 : Blo 1044610 1569983 := bstep (se 1 (by rfl) ⟨1177487, by rfl⟩ : syracuseStep 1569983 = 2354975) B2354975
theorem B2356415 : Blo 1044610 2356415 := bstep (se 1 (by rfl) ⟨1767311, by rfl⟩ : syracuseStep 2356415 = 3534623) B3534623
theorem B1045743 : Blo 1044610 1045743 := bstep (se 1 (by rfl) ⟨784307, by rfl⟩ : syracuseStep 1045743 = 1568615) B1568615
theorem B1045831 : Blo 1044610 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B1045863 : Blo 1044610 1045863 := bstep (se 1 (by rfl) ⟨784397, by rfl⟩ : syracuseStep 1045863 = 1568795) B1568795
theorem B5961215 : Blo 1044610 5961215 := bstep (se 1 (by rfl) ⟨4470911, by rfl⟩ : syracuseStep 5961215 = 8941823) B8941823
theorem B8943533 : Blo 1044610 8943533 := bstep (se 3 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 8943533 = 3353825) B3353825
theorem B1046767 : Blo 1044610 1046767 := bstep (se 1 (by rfl) ⟨785075, by rfl⟩ : syracuseStep 1046767 = 1570151) B1570151
theorem B2357531 : Blo 1044610 2357531 := bstep (se 1 (by rfl) ⟨1768148, by rfl⟩ : syracuseStep 2357531 = 3536297) B3536297
theorem B1046847 : Blo 1044610 1046847 := bstep (se 1 (by rfl) ⟨785135, by rfl⟩ : syracuseStep 1046847 = 1570271) B1570271
theorem B2357567 : Blo 1044610 2357567 := bstep (se 1 (by rfl) ⟨1768175, by rfl⟩ : syracuseStep 2357567 = 3536351) B3536351
theorem B1178239 : Blo 1044610 1178239 := bstep (se 1 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 1178239 = 1767359) B1767359
theorem B1572287 : Blo 1044610 1572287 := bstep (se 1 (by rfl) ⟨1179215, by rfl⟩ : syracuseStep 1572287 = 2358431) B2358431
theorem B1048063 : Blo 1044610 1048063 := bstep (se 1 (by rfl) ⟨786047, by rfl⟩ : syracuseStep 1048063 = 1572095) B1572095
theorem B1048559 : Blo 1044610 1048559 := bstep (se 1 (by rfl) ⟨786419, by rfl⟩ : syracuseStep 1048559 = 1572839) B1572839
theorem B1048607 : Blo 1044610 1048607 := bstep (se 1 (by rfl) ⟨786455, by rfl⟩ : syracuseStep 1048607 = 1572911) B1572911
theorem B5377049 : Blo 1044610 5377049 := bstep (se 2 (by rfl) ⟨2016393, by rfl⟩ : syracuseStep 5377049 = 4032787) B4032787
theorem B26808245 : Blo 1044610 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B1118719 : Blo 1044610 1118719 := bstep (se 1 (by rfl) ⟨839039, by rfl⟩ : syracuseStep 1118719 = 1678079) B1678079
theorem B484315901 : Blo 1044610 484315901 := bstep (se 3 (by rfl) ⟨90809231, by rfl⟩ : syracuseStep 484315901 = 181618463) B181618463
theorem B155095889 : Blo 1044610 155095889 := bstep (se 2 (by rfl) ⟨58160958, by rfl⟩ : syracuseStep 155095889 = 116321917) B116321917
theorem B5970671 : Blo 1044610 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B17703613 : Blo 1044610 17703613 := bstep (se 3 (by rfl) ⟨3319427, by rfl⟩ : syracuseStep 17703613 = 6638855) B6638855
theorem B3974143 : Blo 1044610 3974143 := bstep (se 1 (by rfl) ⟨2980607, by rfl⟩ : syracuseStep 3974143 = 5961215) B5961215
theorem B2828201 : Blo 1044610 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B46443223 : Blo 1044610 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B3975905 : Blo 1044610 3975905 := bstep (se 2 (by rfl) ⟨1490964, by rfl⟩ : syracuseStep 3975905 = 2981929) B2981929
theorem B3976073 : Blo 1044610 3976073 := bstep (se 2 (by rfl) ⟨1491027, by rfl⟩ : syracuseStep 3976073 = 2982055) B2982055
theorem B12069947 : Blo 1044610 12069947 := bstep (se 1 (by rfl) ⟨9052460, by rfl⟩ : syracuseStep 12069947 = 18104921) B18104921
theorem B5288489 : Blo 1044610 5288489 := bstep (se 2 (by rfl) ⟨1983183, by rfl⟩ : syracuseStep 5288489 = 3966367) B3966367
theorem B18133739 : Blo 1044610 18133739 := bstep (se 1 (by rfl) ⟨13600304, by rfl⟩ : syracuseStep 18133739 = 27200609) B27200609
theorem B91599761 : Blo 1044610 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B1324775 : Blo 1044610 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B48413551 : Blo 1044610 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B3980279 : Blo 1044610 3980279 := bstep (se 1 (by rfl) ⟨2985209, by rfl⟩ : syracuseStep 3980279 = 5970419) B5970419
theorem B4832399 : Blo 1044610 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B3980735 : Blo 1044610 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B10043099 : Blo 1044610 10043099 := bstep (se 1 (by rfl) ⟨7532324, by rfl⟩ : syracuseStep 10043099 = 15064649) B15064649
theorem B2834345 : Blo 1044610 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B3981419 : Blo 1044610 3981419 := bstep (se 1 (by rfl) ⟨2986064, by rfl⟩ : syracuseStep 3981419 = 5972129) B5972129
theorem B881377949 : Blo 1044610 881377949 := bstep (se 3 (by rfl) ⟨165258365, by rfl⟩ : syracuseStep 881377949 = 330516731) B330516731
theorem B4768957 : Blo 1044610 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B1549681955 : Blo 1044610 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B8932801 : Blo 1044610 8932801 := bstep (se 2 (by rfl) ⟨3349800, by rfl⟩ : syracuseStep 8932801 = 6699601) B6699601
theorem B5295617 : Blo 1044610 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B3526523 : Blo 1044610 3526523 := bstep (se 1 (by rfl) ⟨2644892, by rfl⟩ : syracuseStep 3526523 = 5289785) B5289785
theorem B81484339 : Blo 1044610 81484339 := bstep (se 1 (by rfl) ⟨61113254, by rfl⟩ : syracuseStep 81484339 = 122226509) B122226509
theorem B2350799 : Blo 1044610 2350799 := bstep (se 1 (by rfl) ⟨1763099, by rfl⟩ : syracuseStep 2350799 = 3526199) B3526199
theorem B5300315 : Blo 1044610 5300315 := bstep (se 1 (by rfl) ⟨3975236, by rfl⟩ : syracuseStep 5300315 = 7950473) B7950473
theorem B7954847 : Blo 1044610 7954847 := bstep (se 1 (by rfl) ⟨5966135, by rfl⟩ : syracuseStep 7954847 = 11932271) B11932271
theorem B11920607 : Blo 1044610 11920607 := bstep (se 1 (by rfl) ⟨8940455, by rfl⟩ : syracuseStep 11920607 = 17880911) B17880911
theorem B2648315 : Blo 1044610 2648315 := bstep (se 1 (by rfl) ⟨1986236, by rfl⟩ : syracuseStep 2648315 = 3972473) B3972473
theorem B2976097 : Blo 1044610 2976097 := bstep (se 2 (by rfl) ⟨1116036, by rfl⟩ : syracuseStep 2976097 = 2232073) B2232073
theorem B18147881 : Blo 1044610 18147881 := bstep (se 2 (by rfl) ⟨6805455, by rfl⟩ : syracuseStep 18147881 = 13610911) B13610911
theorem B1764031 : Blo 1044610 1764031 := bstep (se 1 (by rfl) ⟨1323023, by rfl⟩ : syracuseStep 1764031 = 2646047) B2646047
theorem B2648801 : Blo 1044610 2648801 := bstep (se 2 (by rfl) ⟨993300, by rfl⟩ : syracuseStep 2648801 = 1986601) B1986601
theorem B2517887 : Blo 1044610 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B1567847 : Blo 1044610 1567847 := bstep (se 1 (by rfl) ⟨1175885, by rfl⟩ : syracuseStep 1567847 = 2351771) B2351771
theorem B1567871 : Blo 1044610 1567871 := bstep (se 1 (by rfl) ⟨1175903, by rfl⟩ : syracuseStep 1567871 = 2351807) B2351807
theorem B1568207 : Blo 1044610 1568207 := bstep (se 1 (by rfl) ⟨1176155, by rfl⟩ : syracuseStep 1568207 = 2352311) B2352311
theorem B1568303 : Blo 1044610 1568303 := bstep (se 1 (by rfl) ⟨1176227, by rfl⟩ : syracuseStep 1568303 = 2352455) B2352455
theorem B7958249 : Blo 1044610 7958249 := bstep (se 2 (by rfl) ⟨2984343, by rfl⟩ : syracuseStep 7958249 = 5968687) B5968687
theorem B1568543 : Blo 1044610 1568543 := bstep (se 1 (by rfl) ⟨1176407, by rfl⟩ : syracuseStep 1568543 = 2352815) B2352815
theorem B11300735 : Blo 1044610 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B1569311 : Blo 1044610 1569311 := bstep (se 1 (by rfl) ⟨1176983, by rfl⟩ : syracuseStep 1569311 = 2353967) B2353967
theorem B1045083 : Blo 1044610 1045083 := bstep (se 1 (by rfl) ⟨783812, by rfl⟩ : syracuseStep 1045083 = 1567625) B1567625
theorem B1766495 : Blo 1044610 1766495 := bstep (se 1 (by rfl) ⟨1324871, by rfl⟩ : syracuseStep 1766495 = 2649743) B2649743
theorem B3765473 : Blo 1044610 3765473 := bstep (se 2 (by rfl) ⟨1412052, by rfl⟩ : syracuseStep 3765473 = 2824105) B2824105
theorem B2684263 : Blo 1044610 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B2651575 : Blo 1044610 2651575 := bstep (se 1 (by rfl) ⟨1988681, by rfl⟩ : syracuseStep 2651575 = 3977363) B3977363
theorem B1045967 : Blo 1044610 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B1046043 : Blo 1044610 1046043 := bstep (se 1 (by rfl) ⟨784532, by rfl⟩ : syracuseStep 1046043 = 1569065) B1569065
theorem B1570751 : Blo 1044610 1570751 := bstep (se 1 (by rfl) ⟨1178063, by rfl⟩ : syracuseStep 1570751 = 2356127) B2356127
theorem B1046655 : Blo 1044610 1046655 := bstep (se 1 (by rfl) ⟨784991, by rfl⟩ : syracuseStep 1046655 = 1569983) B1569983
theorem B1570943 : Blo 1044610 1570943 := bstep (se 1 (by rfl) ⟨1178207, by rfl⟩ : syracuseStep 1570943 = 2356415) B2356415
theorem B1570985 : Blo 1044610 1570985 := bstep (se 2 (by rfl) ⟨589119, by rfl⟩ : syracuseStep 1570985 = 1178239) B1178239
theorem B20150471 : Blo 1044610 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B7633223 : Blo 1044610 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B5962355 : Blo 1044610 5962355 := bstep (se 1 (by rfl) ⟨4471766, by rfl⟩ : syracuseStep 5962355 = 8943533) B8943533
theorem B1571687 : Blo 1044610 1571687 := bstep (se 1 (by rfl) ⟨1178765, by rfl⟩ : syracuseStep 1571687 = 2357531) B2357531
theorem B1571711 : Blo 1044610 1571711 := bstep (se 1 (by rfl) ⟨1178783, by rfl⟩ : syracuseStep 1571711 = 2357567) B2357567
theorem B5963129 : Blo 1044610 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B1048191 : Blo 1044610 1048191 := bstep (se 1 (by rfl) ⟨786143, by rfl⟩ : syracuseStep 1048191 = 1572287) B1572287
theorem B2654279 : Blo 1044610 2654279 := bstep (se 1 (by rfl) ⟨1990709, by rfl⟩ : syracuseStep 2654279 = 3981419) B3981419
theorem B6358609 : Blo 1044610 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B3968129 : Blo 1044610 3968129 := bstep (se 2 (by rfl) ⟨1488048, by rfl⟩ : syracuseStep 3968129 = 2976097) B2976097
theorem B12098587 : Blo 1044610 12098587 := bstep (se 1 (by rfl) ⟨9073940, by rfl⟩ : syracuseStep 12098587 = 18147881) B18147881
theorem B3579017 : Blo 1044610 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B1678591 : Blo 1044610 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B12886397 : Blo 1044610 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B5088815 : Blo 1044610 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B3974903 : Blo 1044610 3974903 := bstep (se 1 (by rfl) ⟨2981177, by rfl⟩ : syracuseStep 3974903 = 5962355) B5962355
theorem B3975419 : Blo 1044610 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B6695399 : Blo 1044610 6695399 := bstep (se 1 (by rfl) ⟨5021549, by rfl⟩ : syracuseStep 6695399 = 10043099) B10043099
theorem B1033121303 : Blo 1044610 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B3584699 : Blo 1044610 3584699 := bstep (se 1 (by rfl) ⟨2688524, by rfl⟩ : syracuseStep 3584699 = 5377049) B5377049
theorem B17872163 : Blo 1044610 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B322877267 : Blo 1044610 322877267 := bstep (se 1 (by rfl) ⟨242157950, by rfl⟩ : syracuseStep 322877267 = 484315901) B484315901
theorem B94419269 : Blo 1044610 94419269 := bstep (se 4 (by rfl) ⟨8851806, by rfl⟩ : syracuseStep 94419269 = 17703613) B17703613
theorem B3980447 : Blo 1044610 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B11910401 : Blo 1044610 11910401 := bstep (se 2 (by rfl) ⟨4466400, by rfl⟩ : syracuseStep 11910401 = 8932801) B8932801
theorem B1491625 : Blo 1044610 1491625 := bstep (se 2 (by rfl) ⟨559359, by rfl⟩ : syracuseStep 1491625 = 1118719) B1118719
theorem B7947071 : Blo 1044610 7947071 := bstep (se 1 (by rfl) ⟨5960303, by rfl⟩ : syracuseStep 7947071 = 11920607) B11920607
theorem B8046631 : Blo 1044610 8046631 := bstep (se 1 (by rfl) ⟨6034973, by rfl⟩ : syracuseStep 8046631 = 12069947) B12069947
theorem B3525659 : Blo 1044610 3525659 := bstep (se 1 (by rfl) ⟨2644244, by rfl⟩ : syracuseStep 3525659 = 5288489) B5288489
theorem B61066507 : Blo 1044610 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B108645785 : Blo 1044610 108645785 := bstep (se 2 (by rfl) ⟨40742169, by rfl⟩ : syracuseStep 108645785 = 81484339) B81484339
theorem B2510315 : Blo 1044610 2510315 := bstep (se 1 (by rfl) ⟨1882736, by rfl⟩ : syracuseStep 2510315 = 3765473) B3765473
theorem B30167477 : Blo 1044610 30167477 := bstep (se 5 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 30167477 = 2828201) B2828201
theorem B1889563 : Blo 1044610 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B587585299 : Blo 1044610 587585299 := bstep (se 1 (by rfl) ⟨440688974, by rfl⟩ : syracuseStep 587585299 = 881377949) B881377949
theorem B5298857 : Blo 1044610 5298857 := bstep (se 2 (by rfl) ⟨1987071, by rfl⟩ : syracuseStep 5298857 = 3974143) B3974143
theorem B413589037 : Blo 1044610 413589037 := bstep (se 3 (by rfl) ⟨77547944, by rfl⟩ : syracuseStep 413589037 = 155095889) B155095889
theorem B3530411 : Blo 1044610 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B2351015 : Blo 1044610 2351015 := bstep (se 1 (by rfl) ⟨1763261, by rfl⟩ : syracuseStep 2351015 = 3526523) B3526523
theorem B2352041 : Blo 1044610 2352041 := bstep (se 2 (by rfl) ⟨882015, by rfl⟩ : syracuseStep 2352041 = 1764031) B1764031
theorem B61924297 : Blo 1044610 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B3532733 : Blo 1044610 3532733 := bstep (se 3 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 3532733 = 1324775) B1324775
theorem B1567199 : Blo 1044610 1567199 := bstep (se 1 (by rfl) ⟨1175399, by rfl⟩ : syracuseStep 1567199 = 2350799) B2350799
theorem B3533543 : Blo 1044610 3533543 := bstep (se 1 (by rfl) ⟨2650157, by rfl⟩ : syracuseStep 3533543 = 5300315) B5300315
theorem B5303231 : Blo 1044610 5303231 := bstep (se 1 (by rfl) ⟨3977423, by rfl⟩ : syracuseStep 5303231 = 7954847) B7954847
theorem B1765543 : Blo 1044610 1765543 := bstep (se 1 (by rfl) ⟨1324157, by rfl⟩ : syracuseStep 1765543 = 2648315) B2648315
theorem B1765867 : Blo 1044610 1765867 := bstep (se 1 (by rfl) ⟨1324400, by rfl⟩ : syracuseStep 1765867 = 2648801) B2648801
theorem B2650603 : Blo 1044610 2650603 := bstep (se 1 (by rfl) ⟨1987952, by rfl⟩ : syracuseStep 2650603 = 3975905) B3975905
theorem B3535433 : Blo 1044610 3535433 := bstep (se 2 (by rfl) ⟨1325787, by rfl⟩ : syracuseStep 3535433 = 2651575) B2651575
theorem B2650715 : Blo 1044610 2650715 := bstep (se 1 (by rfl) ⟨1988036, by rfl⟩ : syracuseStep 2650715 = 3976073) B3976073
theorem B1045231 : Blo 1044610 1045231 := bstep (se 1 (by rfl) ⟨783923, by rfl⟩ : syracuseStep 1045231 = 1567847) B1567847
theorem B1045247 : Blo 1044610 1045247 := bstep (se 1 (by rfl) ⟨783935, by rfl⟩ : syracuseStep 1045247 = 1567871) B1567871
theorem B1045471 : Blo 1044610 1045471 := bstep (se 1 (by rfl) ⟨784103, by rfl⟩ : syracuseStep 1045471 = 1568207) B1568207
theorem B1045535 : Blo 1044610 1045535 := bstep (se 1 (by rfl) ⟨784151, by rfl⟩ : syracuseStep 1045535 = 1568303) B1568303
theorem B5305499 : Blo 1044610 5305499 := bstep (se 1 (by rfl) ⟨3979124, by rfl⟩ : syracuseStep 5305499 = 7958249) B7958249
theorem B1045695 : Blo 1044610 1045695 := bstep (se 1 (by rfl) ⟨784271, by rfl⟩ : syracuseStep 1045695 = 1568543) B1568543
theorem B7533823 : Blo 1044610 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B1046207 : Blo 1044610 1046207 := bstep (se 1 (by rfl) ⟨784655, by rfl⟩ : syracuseStep 1046207 = 1569311) B1569311
theorem B12089159 : Blo 1044610 12089159 := bstep (se 1 (by rfl) ⟨9066869, by rfl⟩ : syracuseStep 12089159 = 18133739) B18133739
theorem B1177663 : Blo 1044610 1177663 := bstep (se 1 (by rfl) ⟨883247, by rfl⟩ : syracuseStep 1177663 = 1766495) B1766495
theorem B64551401 : Blo 1044610 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B1047167 : Blo 1044610 1047167 := bstep (se 1 (by rfl) ⟨785375, by rfl⟩ : syracuseStep 1047167 = 1570751) B1570751
theorem B1047295 : Blo 1044610 1047295 := bstep (se 1 (by rfl) ⟨785471, by rfl⟩ : syracuseStep 1047295 = 1570943) B1570943
theorem B1047323 : Blo 1044610 1047323 := bstep (se 1 (by rfl) ⟨785492, by rfl⟩ : syracuseStep 1047323 = 1570985) B1570985
theorem B13433647 : Blo 1044610 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B1047791 : Blo 1044610 1047791 := bstep (se 1 (by rfl) ⟨785843, by rfl⟩ : syracuseStep 1047791 = 1571687) B1571687
theorem B1047807 : Blo 1044610 1047807 := bstep (se 1 (by rfl) ⟨785855, by rfl⟩ : syracuseStep 1047807 = 1571711) B1571711
theorem B2653519 : Blo 1044610 2653519 := bstep (se 1 (by rfl) ⟨1990139, by rfl⟩ : syracuseStep 2653519 = 3980279) B3980279
theorem B2653823 : Blo 1044610 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B1769519 : Blo 1044610 1769519 := bstep (se 1 (by rfl) ⟨1327139, by rfl⟩ : syracuseStep 1769519 = 2654279) B2654279
theorem B38176181 : Blo 1044610 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B1673543 : Blo 1044610 1673543 := bstep (se 1 (by rfl) ⟨1255157, by rfl⟩ : syracuseStep 1673543 = 2510315) B2510315
theorem B8590931 : Blo 1044610 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B4463599 : Blo 1044610 4463599 := bstep (se 1 (by rfl) ⟨3347699, by rfl⟩ : syracuseStep 4463599 = 6695399) B6695399
theorem B16131449 : Blo 1044610 16131449 := bstep (se 2 (by rfl) ⟨6049293, by rfl⟩ : syracuseStep 16131449 = 12098587) B12098587
theorem B43034267 : Blo 1044610 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B2238121 : Blo 1044610 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B7940267 : Blo 1044610 7940267 := bstep (se 1 (by rfl) ⟨5955200, by rfl⟩ : syracuseStep 7940267 = 11910401) B11910401
theorem B72430523 : Blo 1044610 72430523 := bstep (se 1 (by rfl) ⟨54322892, by rfl⟩ : syracuseStep 72430523 = 108645785) B108645785
theorem B3392543 : Blo 1044610 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B10045097 : Blo 1044610 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B11914775 : Blo 1044610 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B17911529 : Blo 1044610 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B42915365 : Blo 1044610 42915365 := bstep (se 4 (by rfl) ⟨4023315, by rfl⟩ : syracuseStep 42915365 = 8046631) B8046631
theorem B5298047 : Blo 1044610 5298047 := bstep (se 1 (by rfl) ⟨3973535, by rfl⟩ : syracuseStep 5298047 = 7947071) B7947071
theorem B82565729 : Blo 1044610 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B2350439 : Blo 1044610 2350439 := bstep (se 1 (by rfl) ⟨1762829, by rfl⟩ : syracuseStep 2350439 = 3525659) B3525659
theorem B2645419 : Blo 1044610 2645419 := bstep (se 1 (by rfl) ⟨1984064, by rfl⟩ : syracuseStep 2645419 = 3968129) B3968129
theorem B8478145 : Blo 1044610 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B20111651 : Blo 1044610 20111651 := bstep (se 1 (by rfl) ⟨15083738, by rfl⟩ : syracuseStep 20111651 = 30167477) B30167477
theorem B7955333 : Blo 1044610 7955333 := bstep (se 4 (by rfl) ⟨745812, by rfl⟩ : syracuseStep 7955333 = 1491625) B1491625
theorem B81422009 : Blo 1044610 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B3532571 : Blo 1044610 3532571 := bstep (se 1 (by rfl) ⟨2649428, by rfl⟩ : syracuseStep 3532571 = 5298857) B5298857
theorem B2353607 : Blo 1044610 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B1567343 : Blo 1044610 1567343 := bstep (se 1 (by rfl) ⟨1175507, by rfl⟩ : syracuseStep 1567343 = 2351015) B2351015
theorem B2354057 : Blo 1044610 2354057 := bstep (se 2 (by rfl) ⟨882771, by rfl⟩ : syracuseStep 2354057 = 1765543) B1765543
theorem B1568027 : Blo 1044610 1568027 := bstep (se 1 (by rfl) ⟨1176020, by rfl⟩ : syracuseStep 1568027 = 2352041) B2352041
theorem B2354489 : Blo 1044610 2354489 := bstep (se 2 (by rfl) ⟨882933, by rfl⟩ : syracuseStep 2354489 = 1765867) B1765867
theorem B3534137 : Blo 1044610 3534137 := bstep (se 2 (by rfl) ⟨1325301, by rfl⟩ : syracuseStep 3534137 = 2650603) B2650603
theorem B2649935 : Blo 1044610 2649935 := bstep (se 1 (by rfl) ⟨1987451, by rfl⟩ : syracuseStep 2649935 = 3974903) B3974903
theorem B2355155 : Blo 1044610 2355155 := bstep (se 1 (by rfl) ⟨1766366, by rfl⟩ : syracuseStep 2355155 = 3532733) B3532733
theorem B2650279 : Blo 1044610 2650279 := bstep (se 1 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 2650279 = 3975419) B3975419
theorem B1044799 : Blo 1044610 1044799 := bstep (se 1 (by rfl) ⟨783599, by rfl⟩ : syracuseStep 1044799 = 1567199) B1567199
theorem B2519417 : Blo 1044610 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B2355695 : Blo 1044610 2355695 := bstep (se 1 (by rfl) ⟨1766771, by rfl⟩ : syracuseStep 2355695 = 3533543) B3533543
theorem B3535487 : Blo 1044610 3535487 := bstep (se 1 (by rfl) ⟨2651615, by rfl⟩ : syracuseStep 3535487 = 5303231) B5303231
theorem B688747535 : Blo 1044610 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B783447065 : Blo 1044610 783447065 := bstep (se 2 (by rfl) ⟨293792649, by rfl⟩ : syracuseStep 783447065 = 587585299) B587585299
theorem B1570217 : Blo 1044610 1570217 := bstep (se 2 (by rfl) ⟨588831, by rfl⟩ : syracuseStep 1570217 = 1177663) B1177663
theorem B2356955 : Blo 1044610 2356955 := bstep (se 1 (by rfl) ⟨1767716, by rfl⟩ : syracuseStep 2356955 = 3535433) B3535433
theorem B1767143 : Blo 1044610 1767143 := bstep (se 1 (by rfl) ⟨1325357, by rfl⟩ : syracuseStep 1767143 = 2650715) B2650715
theorem B2389799 : Blo 1044610 2389799 := bstep (se 1 (by rfl) ⟨1792349, by rfl⟩ : syracuseStep 2389799 = 3584699) B3584699
theorem B3536999 : Blo 1044610 3536999 := bstep (se 1 (by rfl) ⟨2652749, by rfl⟩ : syracuseStep 3536999 = 5305499) B5305499
theorem B8059439 : Blo 1044610 8059439 := bstep (se 1 (by rfl) ⟨6044579, by rfl⟩ : syracuseStep 8059439 = 12089159) B12089159
theorem B215251511 : Blo 1044610 215251511 := bstep (se 1 (by rfl) ⟨161438633, by rfl⟩ : syracuseStep 215251511 = 322877267) B322877267
theorem B62946179 : Blo 1044610 62946179 := bstep (se 1 (by rfl) ⟨47209634, by rfl⟩ : syracuseStep 62946179 = 94419269) B94419269
theorem B3538025 : Blo 1044610 3538025 := bstep (se 2 (by rfl) ⟨1326759, by rfl⟩ : syracuseStep 3538025 = 2653519) B2653519
theorem B551452049 : Blo 1044610 551452049 := bstep (se 2 (by rfl) ⟨206794518, by rfl⟩ : syracuseStep 551452049 = 413589037) B413589037
theorem B2653631 : Blo 1044610 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B1769215 : Blo 1044610 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B1179679 : Blo 1044610 1179679 := bstep (se 1 (by rfl) ⟨884759, by rfl⟩ : syracuseStep 1179679 = 1769519) B1769519
theorem B1115695 : Blo 1044610 1115695 := bstep (se 1 (by rfl) ⟨836771, by rfl⟩ : syracuseStep 1115695 = 1673543) B1673543
theorem B9046781 : Blo 1044610 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B28610243 : Blo 1044610 28610243 := bstep (se 1 (by rfl) ⟨21457682, by rfl⟩ : syracuseStep 28610243 = 42915365) B42915365
theorem B13407767 : Blo 1044610 13407767 := bstep (se 1 (by rfl) ⟨10055825, by rfl⟩ : syracuseStep 13407767 = 20111651) B20111651
theorem B10754299 : Blo 1044610 10754299 := bstep (se 1 (by rfl) ⟨8065724, by rfl⟩ : syracuseStep 10754299 = 16131449) B16131449
theorem B574004029 : Blo 1044610 574004029 := bstep (se 3 (by rfl) ⟨107625755, by rfl⟩ : syracuseStep 574004029 = 215251511) B215251511
theorem B1679611 : Blo 1044610 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B522298043 : Blo 1044610 522298043 := bstep (se 1 (by rfl) ⟨391723532, by rfl⟩ : syracuseStep 522298043 = 783447065) B783447065
theorem B11936645 : Blo 1044610 11936645 := bstep (se 4 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 11936645 = 2238121) B2238121
theorem B367634699 : Blo 1044610 367634699 := bstep (se 1 (by rfl) ⟨275726024, by rfl⟩ : syracuseStep 367634699 = 551452049) B551452049
theorem B6696731 : Blo 1044610 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B7943183 : Blo 1044610 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B11941019 : Blo 1044610 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B28689511 : Blo 1044610 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B54281339 : Blo 1044610 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B5293511 : Blo 1044610 5293511 := bstep (se 1 (by rfl) ⟨3970133, by rfl⟩ : syracuseStep 5293511 = 7940267) B7940267
theorem B48287015 : Blo 1044610 48287015 := bstep (se 1 (by rfl) ⟨36215261, by rfl⟩ : syracuseStep 48287015 = 72430523) B72430523
theorem B459165023 : Blo 1044610 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B1593199 : Blo 1044610 1593199 := bstep (se 1 (by rfl) ⟨1194899, by rfl⟩ : syracuseStep 1593199 = 2389799) B2389799
theorem B5951465 : Blo 1044610 5951465 := bstep (se 2 (by rfl) ⟨2231799, by rfl⟩ : syracuseStep 5951465 = 4463599) B4463599
theorem B3527225 : Blo 1044610 3527225 := bstep (se 2 (by rfl) ⟨1322709, by rfl⟩ : syracuseStep 3527225 = 2645419) B2645419
theorem B41964119 : Blo 1044610 41964119 := bstep (se 1 (by rfl) ⟨31473089, by rfl⟩ : syracuseStep 41964119 = 62946179) B62946179
theorem B25450787 : Blo 1044610 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B5727287 : Blo 1044610 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3532031 : Blo 1044610 3532031 := bstep (se 1 (by rfl) ⟨2649023, by rfl⟩ : syracuseStep 3532031 = 5298047) B5298047
theorem B55043819 : Blo 1044610 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B1566959 : Blo 1044610 1566959 := bstep (se 1 (by rfl) ⟨1175219, by rfl⟩ : syracuseStep 1566959 = 2350439) B2350439
theorem B3533705 : Blo 1044610 3533705 := bstep (se 2 (by rfl) ⟨1325139, by rfl⟩ : syracuseStep 3533705 = 2650279) B2650279
theorem B5303555 : Blo 1044610 5303555 := bstep (se 1 (by rfl) ⟨3977666, by rfl⟩ : syracuseStep 5303555 = 7955333) B7955333
theorem B2355047 : Blo 1044610 2355047 := bstep (se 1 (by rfl) ⟨1766285, by rfl⟩ : syracuseStep 2355047 = 3532571) B3532571
theorem B1569071 : Blo 1044610 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B1044895 : Blo 1044610 1044895 := bstep (se 1 (by rfl) ⟨783671, by rfl⟩ : syracuseStep 1044895 = 1567343) B1567343
theorem B1569371 : Blo 1044610 1569371 := bstep (se 1 (by rfl) ⟨1177028, by rfl⟩ : syracuseStep 1569371 = 2354057) B2354057
theorem B1045351 : Blo 1044610 1045351 := bstep (se 1 (by rfl) ⟨784013, by rfl⟩ : syracuseStep 1045351 = 1568027) B1568027
theorem B1569659 : Blo 1044610 1569659 := bstep (se 1 (by rfl) ⟨1177244, by rfl⟩ : syracuseStep 1569659 = 2354489) B2354489
theorem B2356091 : Blo 1044610 2356091 := bstep (se 1 (by rfl) ⟨1767068, by rfl⟩ : syracuseStep 2356091 = 3534137) B3534137
theorem B1766623 : Blo 1044610 1766623 := bstep (se 1 (by rfl) ⟨1324967, by rfl⟩ : syracuseStep 1766623 = 2649935) B2649935
theorem B1570103 : Blo 1044610 1570103 := bstep (se 1 (by rfl) ⟨1177577, by rfl⟩ : syracuseStep 1570103 = 2355155) B2355155
theorem B1570463 : Blo 1044610 1570463 := bstep (se 1 (by rfl) ⟨1177847, by rfl⟩ : syracuseStep 1570463 = 2355695) B2355695
theorem B2356991 : Blo 1044610 2356991 := bstep (se 1 (by rfl) ⟨1767743, by rfl⟩ : syracuseStep 2356991 = 3535487) B3535487
theorem B1046811 : Blo 1044610 1046811 := bstep (se 1 (by rfl) ⟨785108, by rfl⟩ : syracuseStep 1046811 = 1570217) B1570217
theorem B1571303 : Blo 1044610 1571303 := bstep (se 1 (by rfl) ⟨1178477, by rfl⟩ : syracuseStep 1571303 = 2356955) B2356955
theorem B1178095 : Blo 1044610 1178095 := bstep (se 1 (by rfl) ⟨883571, by rfl⟩ : syracuseStep 1178095 = 1767143) B1767143
theorem B2357999 : Blo 1044610 2357999 := bstep (se 1 (by rfl) ⟨1768499, by rfl⟩ : syracuseStep 2357999 = 3536999) B3536999
theorem B5372959 : Blo 1044610 5372959 := bstep (se 1 (by rfl) ⟨4029719, by rfl⟩ : syracuseStep 5372959 = 8059439) B8059439
theorem B11304193 : Blo 1044610 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B2358683 : Blo 1044610 2358683 := bstep (se 1 (by rfl) ⟨1769012, by rfl⟩ : syracuseStep 2358683 = 3538025) B3538025
theorem B1769087 : Blo 1044610 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B2358953 : Blo 1044610 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B1572905 : Blo 1044610 1572905 := bstep (se 2 (by rfl) ⟨589839, by rfl⟩ : syracuseStep 1572905 = 1179679) B1179679
theorem B6031187 : Blo 1044610 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B19073495 : Blo 1044610 19073495 := bstep (se 1 (by rfl) ⟨14305121, by rfl⟩ : syracuseStep 19073495 = 28610243) B28610243
theorem B3967643 : Blo 1044610 3967643 := bstep (se 1 (by rfl) ⟨2975732, by rfl⟩ : syracuseStep 3967643 = 5951465) B5951465
theorem B348198695 : Blo 1044610 348198695 := bstep (se 1 (by rfl) ⟨261149021, by rfl⟩ : syracuseStep 348198695 = 522298043) B522298043
theorem B4464487 : Blo 1044610 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B765338705 : Blo 1044610 765338705 := bstep (se 2 (by rfl) ⟨287002014, by rfl⟩ : syracuseStep 765338705 = 574004029) B574004029
theorem B8497061 : Blo 1044610 8497061 := bstep (se 4 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 8497061 = 1593199) B1593199
theorem B2239481 : Blo 1044610 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B36187559 : Blo 1044610 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B57356261 : Blo 1044610 57356261 := bstep (se 4 (by rfl) ⟨5377149, by rfl⟩ : syracuseStep 57356261 = 10754299) B10754299
theorem B38252681 : Blo 1044610 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B1487593 : Blo 1044610 1487593 := bstep (se 2 (by rfl) ⟨557847, by rfl⟩ : syracuseStep 1487593 = 1115695) B1115695
theorem B32191343 : Blo 1044610 32191343 := bstep (se 1 (by rfl) ⟨24143507, by rfl⟩ : syracuseStep 32191343 = 48287015) B48287015
theorem B3818191 : Blo 1044610 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B245089799 : Blo 1044610 245089799 := bstep (se 1 (by rfl) ⟨183817349, by rfl⟩ : syracuseStep 245089799 = 367634699) B367634699
theorem B5295455 : Blo 1044610 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B7163945 : Blo 1044610 7163945 := bstep (se 2 (by rfl) ⟨2686479, by rfl⟩ : syracuseStep 7163945 = 5372959) B5372959
theorem B3529007 : Blo 1044610 3529007 := bstep (se 1 (by rfl) ⟨2646755, by rfl⟩ : syracuseStep 3529007 = 5293511) B5293511
theorem B306110015 : Blo 1044610 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B2351483 : Blo 1044610 2351483 := bstep (se 1 (by rfl) ⟨1763612, by rfl⟩ : syracuseStep 2351483 = 3527225) B3527225
theorem B27976079 : Blo 1044610 27976079 := bstep (se 1 (by rfl) ⟨20982059, by rfl⟩ : syracuseStep 27976079 = 41964119) B41964119
theorem B8938511 : Blo 1044610 8938511 := bstep (se 1 (by rfl) ⟨6703883, by rfl⟩ : syracuseStep 8938511 = 13407767) B13407767
theorem B16967191 : Blo 1044610 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B7957763 : Blo 1044610 7957763 := bstep (se 1 (by rfl) ⟨5968322, by rfl⟩ : syracuseStep 7957763 = 11936645) B11936645
theorem B2354687 : Blo 1044610 2354687 := bstep (se 1 (by rfl) ⟨1766015, by rfl⟩ : syracuseStep 2354687 = 3532031) B3532031
theorem B36695879 : Blo 1044610 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B1044639 : Blo 1044610 1044639 := bstep (se 1 (by rfl) ⟨783479, by rfl⟩ : syracuseStep 1044639 = 1566959) B1566959
theorem B2355497 : Blo 1044610 2355497 := bstep (se 2 (by rfl) ⟨883311, by rfl⟩ : syracuseStep 2355497 = 1766623) B1766623
theorem B2355803 : Blo 1044610 2355803 := bstep (se 1 (by rfl) ⟨1766852, by rfl⟩ : syracuseStep 2355803 = 3533705) B3533705
theorem B3535703 : Blo 1044610 3535703 := bstep (se 1 (by rfl) ⟨2651777, by rfl⟩ : syracuseStep 3535703 = 5303555) B5303555
theorem B1570031 : Blo 1044610 1570031 := bstep (se 1 (by rfl) ⟨1177523, by rfl⟩ : syracuseStep 1570031 = 2355047) B2355047
theorem B1046047 : Blo 1044610 1046047 := bstep (se 1 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 1046047 = 1569071) B1569071
theorem B1046247 : Blo 1044610 1046247 := bstep (se 1 (by rfl) ⟨784685, by rfl⟩ : syracuseStep 1046247 = 1569371) B1569371
theorem B1046439 : Blo 1044610 1046439 := bstep (se 1 (by rfl) ⟨784829, by rfl⟩ : syracuseStep 1046439 = 1569659) B1569659
theorem B1570727 : Blo 1044610 1570727 := bstep (se 1 (by rfl) ⟨1178045, by rfl⟩ : syracuseStep 1570727 = 2356091) B2356091
theorem B1570793 : Blo 1044610 1570793 := bstep (se 2 (by rfl) ⟨589047, by rfl⟩ : syracuseStep 1570793 = 1178095) B1178095
theorem B7960679 : Blo 1044610 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B1046735 : Blo 1044610 1046735 := bstep (se 1 (by rfl) ⟨785051, by rfl⟩ : syracuseStep 1046735 = 1570103) B1570103
theorem B1046975 : Blo 1044610 1046975 := bstep (se 1 (by rfl) ⟨785231, by rfl⟩ : syracuseStep 1046975 = 1570463) B1570463
theorem B1571327 : Blo 1044610 1571327 := bstep (se 1 (by rfl) ⟨1178495, by rfl⟩ : syracuseStep 1571327 = 2356991) B2356991
theorem B1047535 : Blo 1044610 1047535 := bstep (se 1 (by rfl) ⟨785651, by rfl⟩ : syracuseStep 1047535 = 1571303) B1571303
theorem B15072257 : Blo 1044610 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B1571999 : Blo 1044610 1571999 := bstep (se 1 (by rfl) ⟨1178999, by rfl⟩ : syracuseStep 1571999 = 2357999) B2357999
theorem B1572455 : Blo 1044610 1572455 := bstep (se 1 (by rfl) ⟨1179341, by rfl⟩ : syracuseStep 1572455 = 2358683) B2358683
theorem B1179391 : Blo 1044610 1179391 := bstep (se 1 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 1179391 = 1769087) B1769087
theorem B1572635 : Blo 1044610 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B1048603 : Blo 1044610 1048603 := bstep (se 1 (by rfl) ⟨786452, by rfl⟩ : syracuseStep 1048603 = 1572905) B1572905
theorem B12715663 : Blo 1044610 12715663 := bstep (se 1 (by rfl) ⟨9536747, by rfl⟩ : syracuseStep 12715663 = 19073495) B19073495
theorem B232132463 : Blo 1044610 232132463 := bstep (se 1 (by rfl) ⟨174099347, by rfl⟩ : syracuseStep 232132463 = 348198695) B348198695
theorem B18650719 : Blo 1044610 18650719 := bstep (se 1 (by rfl) ⟨13988039, by rfl⟩ : syracuseStep 18650719 = 27976079) B27976079
theorem B24125039 : Blo 1044610 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B25501787 : Blo 1044610 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B5090921 : Blo 1044610 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B163393199 : Blo 1044610 163393199 := bstep (se 1 (by rfl) ⟨122544899, by rfl⟩ : syracuseStep 163393199 = 245089799) B245089799
theorem B22622921 : Blo 1044610 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B1983457 : Blo 1044610 1983457 := bstep (se 2 (by rfl) ⟨743796, by rfl⟩ : syracuseStep 1983457 = 1487593) B1487593
theorem B1492987 : Blo 1044610 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B24463919 : Blo 1044610 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B40192685 : Blo 1044610 40192685 := bstep (se 3 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 40192685 = 15072257) B15072257
theorem B5952649 : Blo 1044610 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B4020791 : Blo 1044610 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B2645095 : Blo 1044610 2645095 := bstep (se 1 (by rfl) ⟨1983821, by rfl⟩ : syracuseStep 2645095 = 3967643) B3967643
theorem B3530303 : Blo 1044610 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B4775963 : Blo 1044610 4775963 := bstep (se 1 (by rfl) ⟨3581972, by rfl⟩ : syracuseStep 4775963 = 7163945) B7163945
theorem B2352671 : Blo 1044610 2352671 := bstep (se 1 (by rfl) ⟨1764503, by rfl⟩ : syracuseStep 2352671 = 3529007) B3529007
theorem B204073343 : Blo 1044610 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B1567655 : Blo 1044610 1567655 := bstep (se 1 (by rfl) ⟨1175741, by rfl⟩ : syracuseStep 1567655 = 2351483) B2351483
theorem B5959007 : Blo 1044610 5959007 := bstep (se 1 (by rfl) ⟨4469255, by rfl⟩ : syracuseStep 5959007 = 8938511) B8938511
theorem B510225803 : Blo 1044610 510225803 := bstep (se 1 (by rfl) ⟨382669352, by rfl⟩ : syracuseStep 510225803 = 765338705) B765338705
theorem B5664707 : Blo 1044610 5664707 := bstep (se 1 (by rfl) ⟨4248530, by rfl⟩ : syracuseStep 5664707 = 8497061) B8497061
theorem B5305175 : Blo 1044610 5305175 := bstep (se 1 (by rfl) ⟨3978881, by rfl⟩ : syracuseStep 5305175 = 7957763) B7957763
theorem B1569791 : Blo 1044610 1569791 := bstep (se 1 (by rfl) ⟨1177343, by rfl⟩ : syracuseStep 1569791 = 2354687) B2354687
theorem B38237507 : Blo 1044610 38237507 := bstep (se 1 (by rfl) ⟨28678130, by rfl⟩ : syracuseStep 38237507 = 57356261) B57356261
theorem B1570331 : Blo 1044610 1570331 := bstep (se 1 (by rfl) ⟨1177748, by rfl⟩ : syracuseStep 1570331 = 2355497) B2355497
theorem B1570535 : Blo 1044610 1570535 := bstep (se 1 (by rfl) ⟨1177901, by rfl⟩ : syracuseStep 1570535 = 2355803) B2355803
theorem B2357135 : Blo 1044610 2357135 := bstep (se 1 (by rfl) ⟨1767851, by rfl⟩ : syracuseStep 2357135 = 3535703) B3535703
theorem B21460895 : Blo 1044610 21460895 := bstep (se 1 (by rfl) ⟨16095671, by rfl⟩ : syracuseStep 21460895 = 32191343) B32191343
theorem B1046687 : Blo 1044610 1046687 := bstep (se 1 (by rfl) ⟨785015, by rfl⟩ : syracuseStep 1046687 = 1570031) B1570031
theorem B1047151 : Blo 1044610 1047151 := bstep (se 1 (by rfl) ⟨785363, by rfl⟩ : syracuseStep 1047151 = 1570727) B1570727
theorem B1047195 : Blo 1044610 1047195 := bstep (se 1 (by rfl) ⟨785396, by rfl⟩ : syracuseStep 1047195 = 1570793) B1570793
theorem B5307119 : Blo 1044610 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B1047551 : Blo 1044610 1047551 := bstep (se 1 (by rfl) ⟨785663, by rfl⟩ : syracuseStep 1047551 = 1571327) B1571327
theorem B1047999 : Blo 1044610 1047999 := bstep (se 1 (by rfl) ⟨785999, by rfl⟩ : syracuseStep 1047999 = 1571999) B1571999
theorem B1572521 : Blo 1044610 1572521 := bstep (se 2 (by rfl) ⟨589695, by rfl⟩ : syracuseStep 1572521 = 1179391) B1179391
theorem B1048303 : Blo 1044610 1048303 := bstep (se 1 (by rfl) ⟨786227, by rfl⟩ : syracuseStep 1048303 = 1572455) B1572455
theorem B1048423 : Blo 1044610 1048423 := bstep (se 1 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 1048423 = 1572635) B1572635
theorem B136048895 : Blo 1044610 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B7936865 : Blo 1044610 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B3972671 : Blo 1044610 3972671 := bstep (se 1 (by rfl) ⟨2979503, by rfl⟩ : syracuseStep 3972671 = 5959007) B5959007
theorem B108928799 : Blo 1044610 108928799 := bstep (se 1 (by rfl) ⟨81696599, by rfl⟩ : syracuseStep 108928799 = 163393199) B163393199
theorem B3776471 : Blo 1044610 3776471 := bstep (se 1 (by rfl) ⟨2832353, by rfl⟩ : syracuseStep 3776471 = 5664707) B5664707
theorem B15081947 : Blo 1044610 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B16954217 : Blo 1044610 16954217 := bstep (se 2 (by rfl) ⟨6357831, by rfl⟩ : syracuseStep 16954217 = 12715663) B12715663
theorem B340150535 : Blo 1044610 340150535 := bstep (se 1 (by rfl) ⟨255112901, by rfl⟩ : syracuseStep 340150535 = 510225803) B510225803
theorem B3393947 : Blo 1044610 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B99470501 : Blo 1044610 99470501 := bstep (se 4 (by rfl) ⟨9325359, by rfl⟩ : syracuseStep 99470501 = 18650719) B18650719
theorem B14307263 : Blo 1044610 14307263 := bstep (se 1 (by rfl) ⟨10730447, by rfl⟩ : syracuseStep 14307263 = 21460895) B21460895
theorem B3526793 : Blo 1044610 3526793 := bstep (se 2 (by rfl) ⟨1322547, by rfl⟩ : syracuseStep 3526793 = 2645095) B2645095
theorem B12735901 : Blo 1044610 12735901 := bstep (se 3 (by rfl) ⟨2387981, by rfl⟩ : syracuseStep 12735901 = 4775963) B4775963
theorem B2644609 : Blo 1044610 2644609 := bstep (se 2 (by rfl) ⟨991728, by rfl⟩ : syracuseStep 2644609 = 1983457) B1983457
theorem B16309279 : Blo 1044610 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B26795123 : Blo 1044610 26795123 := bstep (se 1 (by rfl) ⟨20096342, by rfl⟩ : syracuseStep 26795123 = 40192685) B40192685
theorem B154754975 : Blo 1044610 154754975 := bstep (se 1 (by rfl) ⟨116066231, by rfl⟩ : syracuseStep 154754975 = 232132463) B232132463
theorem B1990649 : Blo 1044610 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B2353535 : Blo 1044610 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B16083359 : Blo 1044610 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B17001191 : Blo 1044610 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B42888437 : Blo 1044610 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B1568447 : Blo 1044610 1568447 := bstep (se 1 (by rfl) ⟨1176335, by rfl⟩ : syracuseStep 1568447 = 2352671) B2352671
theorem B1045103 : Blo 1044610 1045103 := bstep (se 1 (by rfl) ⟨783827, by rfl⟩ : syracuseStep 1045103 = 1567655) B1567655
theorem B3536783 : Blo 1044610 3536783 := bstep (se 1 (by rfl) ⟨2652587, by rfl⟩ : syracuseStep 3536783 = 5305175) B5305175
theorem B1046527 : Blo 1044610 1046527 := bstep (se 1 (by rfl) ⟨784895, by rfl⟩ : syracuseStep 1046527 = 1569791) B1569791
theorem B25491671 : Blo 1044610 25491671 := bstep (se 1 (by rfl) ⟨19118753, by rfl⟩ : syracuseStep 25491671 = 38237507) B38237507
theorem B1046887 : Blo 1044610 1046887 := bstep (se 1 (by rfl) ⟨785165, by rfl⟩ : syracuseStep 1046887 = 1570331) B1570331
theorem B1047023 : Blo 1044610 1047023 := bstep (se 1 (by rfl) ⟨785267, by rfl⟩ : syracuseStep 1047023 = 1570535) B1570535
theorem B1571423 : Blo 1044610 1571423 := bstep (se 1 (by rfl) ⟨1178567, by rfl⟩ : syracuseStep 1571423 = 2357135) B2357135
theorem B3538079 : Blo 1044610 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B1048347 : Blo 1044610 1048347 := bstep (se 1 (by rfl) ⟨786260, by rfl⟩ : syracuseStep 1048347 = 1572521) B1572521
theorem B9538175 : Blo 1044610 9538175 := bstep (se 1 (by rfl) ⟨7153631, by rfl⟩ : syracuseStep 9538175 = 14307263) B14307263
theorem B17863415 : Blo 1044610 17863415 := bstep (se 1 (by rfl) ⟨13397561, by rfl⟩ : syracuseStep 17863415 = 26795123) B26795123
theorem B72619199 : Blo 1044610 72619199 := bstep (se 1 (by rfl) ⟨54464399, by rfl⟩ : syracuseStep 72619199 = 108928799) B108928799
theorem B9050525 : Blo 1044610 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B10722239 : Blo 1044610 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B16981201 : Blo 1044610 16981201 := bstep (se 2 (by rfl) ⟨6367950, by rfl⟩ : syracuseStep 16981201 = 12735901) B12735901
theorem B226767023 : Blo 1044610 226767023 := bstep (se 1 (by rfl) ⟨170075267, by rfl⟩ : syracuseStep 226767023 = 340150535) B340150535
theorem B5291243 : Blo 1044610 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B103169983 : Blo 1044610 103169983 := bstep (se 1 (by rfl) ⟨77377487, by rfl⟩ : syracuseStep 103169983 = 154754975) B154754975
theorem B1327099 : Blo 1044610 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B28592291 : Blo 1044610 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B3526145 : Blo 1044610 3526145 := bstep (se 2 (by rfl) ⟨1322304, by rfl⟩ : syracuseStep 3526145 = 2644609) B2644609
theorem B21745705 : Blo 1044610 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B16994447 : Blo 1044610 16994447 := bstep (se 1 (by rfl) ⟨12745835, by rfl⟩ : syracuseStep 16994447 = 25491671) B25491671
theorem B66313667 : Blo 1044610 66313667 := bstep (se 1 (by rfl) ⟨49735250, by rfl⟩ : syracuseStep 66313667 = 99470501) B99470501
theorem B2351195 : Blo 1044610 2351195 := bstep (se 1 (by rfl) ⟨1763396, by rfl⟩ : syracuseStep 2351195 = 3526793) B3526793
theorem B2648447 : Blo 1044610 2648447 := bstep (se 1 (by rfl) ⟨1986335, by rfl⟩ : syracuseStep 2648447 = 3972671) B3972671
theorem B2517647 : Blo 1044610 2517647 := bstep (se 1 (by rfl) ⟨1888235, by rfl⟩ : syracuseStep 2517647 = 3776471) B3776471
theorem B10054631 : Blo 1044610 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B1569023 : Blo 1044610 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B11334127 : Blo 1044610 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B1045631 : Blo 1044610 1045631 := bstep (se 1 (by rfl) ⟨784223, by rfl⟩ : syracuseStep 1045631 = 1568447) B1568447
theorem B90699263 : Blo 1044610 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B11302811 : Blo 1044610 11302811 := bstep (se 1 (by rfl) ⟨8477108, by rfl⟩ : syracuseStep 11302811 = 16954217) B16954217
theorem B2357855 : Blo 1044610 2357855 := bstep (se 1 (by rfl) ⟨1768391, by rfl⟩ : syracuseStep 2357855 = 3536783) B3536783
theorem B1047615 : Blo 1044610 1047615 := bstep (se 1 (by rfl) ⟨785711, by rfl⟩ : syracuseStep 1047615 = 1571423) B1571423
theorem B2358719 : Blo 1044610 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B6358783 : Blo 1044610 6358783 := bstep (se 1 (by rfl) ⟨4769087, by rfl⟩ : syracuseStep 6358783 = 9538175) B9538175
theorem B6033683 : Blo 1044610 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B7148159 : Blo 1044610 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B44209111 : Blo 1044610 44209111 := bstep (se 1 (by rfl) ⟨33156833, by rfl⟩ : syracuseStep 44209111 = 66313667) B66313667
theorem B15112169 : Blo 1044610 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B60466175 : Blo 1044610 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B11908943 : Blo 1044610 11908943 := bstep (se 1 (by rfl) ⟨8931707, by rfl⟩ : syracuseStep 11908943 = 17863415) B17863415
theorem B48412799 : Blo 1044610 48412799 := bstep (se 1 (by rfl) ⟨36309599, by rfl⟩ : syracuseStep 48412799 = 72619199) B72619199
theorem B6703087 : Blo 1044610 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B151178015 : Blo 1044610 151178015 := bstep (se 1 (by rfl) ⟨113383511, by rfl⟩ : syracuseStep 151178015 = 226767023) B226767023
theorem B3527495 : Blo 1044610 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B1769465 : Blo 1044610 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B19061527 : Blo 1044610 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B2350763 : Blo 1044610 2350763 := bstep (se 1 (by rfl) ⟨1763072, by rfl⟩ : syracuseStep 2350763 = 3526145) B3526145
theorem B11329631 : Blo 1044610 11329631 := bstep (se 1 (by rfl) ⟨8497223, by rfl⟩ : syracuseStep 11329631 = 16994447) B16994447
theorem B28994273 : Blo 1044610 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B1567463 : Blo 1044610 1567463 := bstep (se 1 (by rfl) ⟨1175597, by rfl⟩ : syracuseStep 1567463 = 2351195) B2351195
theorem B1765631 : Blo 1044610 1765631 := bstep (se 1 (by rfl) ⟨1324223, by rfl⟩ : syracuseStep 1765631 = 2648447) B2648447
theorem B6713725 : Blo 1044610 6713725 := bstep (se 3 (by rfl) ⟨1258823, by rfl⟩ : syracuseStep 6713725 = 2517647) B2517647
theorem B1046015 : Blo 1044610 1046015 := bstep (se 1 (by rfl) ⟨784511, by rfl⟩ : syracuseStep 1046015 = 1569023) B1569023
theorem B7535207 : Blo 1044610 7535207 := bstep (se 1 (by rfl) ⟨5651405, by rfl⟩ : syracuseStep 7535207 = 11302811) B11302811
theorem B22641601 : Blo 1044610 22641601 := bstep (se 2 (by rfl) ⟨8490600, by rfl⟩ : syracuseStep 22641601 = 16981201) B16981201
theorem B1571903 : Blo 1044610 1571903 := bstep (se 1 (by rfl) ⟨1178927, by rfl⟩ : syracuseStep 1571903 = 2357855) B2357855
theorem B1572479 : Blo 1044610 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B137559977 : Blo 1044610 137559977 := bstep (se 2 (by rfl) ⟨51584991, by rfl⟩ : syracuseStep 137559977 = 103169983) B103169983
theorem B1179643 : Blo 1044610 1179643 := bstep (se 1 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 1179643 = 1769465) B1769465
theorem B8951633 : Blo 1044610 8951633 := bstep (se 2 (by rfl) ⟨3356862, by rfl⟩ : syracuseStep 8951633 = 6713725) B6713725
theorem B40310783 : Blo 1044610 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B7939295 : Blo 1044610 7939295 := bstep (se 1 (by rfl) ⟨5954471, by rfl⟩ : syracuseStep 7939295 = 11908943) B11908943
theorem B30188801 : Blo 1044610 30188801 := bstep (se 2 (by rfl) ⟨11320800, by rfl⟩ : syracuseStep 30188801 = 22641601) B22641601
theorem B5023471 : Blo 1044610 5023471 := bstep (se 1 (by rfl) ⟨3767603, by rfl⟩ : syracuseStep 5023471 = 7535207) B7535207
theorem B4765439 : Blo 1044610 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B10074779 : Blo 1044610 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B7553087 : Blo 1044610 7553087 := bstep (se 1 (by rfl) ⟨5664815, by rfl⟩ : syracuseStep 7553087 = 11329631) B11329631
theorem B25415369 : Blo 1044610 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B91706651 : Blo 1044610 91706651 := bstep (se 1 (by rfl) ⟨68779988, by rfl⟩ : syracuseStep 91706651 = 137559977) B137559977
theorem B100785343 : Blo 1044610 100785343 := bstep (se 1 (by rfl) ⟨75589007, by rfl⟩ : syracuseStep 100785343 = 151178015) B151178015
theorem B8478377 : Blo 1044610 8478377 := bstep (se 2 (by rfl) ⟨3179391, by rfl⟩ : syracuseStep 8478377 = 6358783) B6358783
theorem B8937449 : Blo 1044610 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B4022455 : Blo 1044610 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B2351663 : Blo 1044610 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B1567175 : Blo 1044610 1567175 := bstep (se 1 (by rfl) ⟨1175381, by rfl⟩ : syracuseStep 1567175 = 2350763) B2350763
theorem B58945481 : Blo 1044610 58945481 := bstep (se 2 (by rfl) ⟨22104555, by rfl⟩ : syracuseStep 58945481 = 44209111) B44209111
theorem B19329515 : Blo 1044610 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B1044975 : Blo 1044610 1044975 := bstep (se 1 (by rfl) ⟨783731, by rfl⟩ : syracuseStep 1044975 = 1567463) B1567463
theorem B1177087 : Blo 1044610 1177087 := bstep (se 1 (by rfl) ⟨882815, by rfl⟩ : syracuseStep 1177087 = 1765631) B1765631
theorem B32275199 : Blo 1044610 32275199 := bstep (se 1 (by rfl) ⟨24206399, by rfl⟩ : syracuseStep 32275199 = 48412799) B48412799
theorem B1047935 : Blo 1044610 1047935 := bstep (se 1 (by rfl) ⟨785951, by rfl⟩ : syracuseStep 1047935 = 1571903) B1571903
theorem B1048319 : Blo 1044610 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B16943579 : Blo 1044610 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B5967755 : Blo 1044610 5967755 := bstep (se 1 (by rfl) ⟨4475816, by rfl⟩ : syracuseStep 5967755 = 8951633) B8951633
theorem B26873855 : Blo 1044610 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B20125867 : Blo 1044610 20125867 := bstep (se 1 (by rfl) ⟨15094400, by rfl⟩ : syracuseStep 20125867 = 30188801) B30188801
theorem B39296987 : Blo 1044610 39296987 := bstep (se 1 (by rfl) ⟨29472740, by rfl⟩ : syracuseStep 39296987 = 58945481) B58945481
theorem B12886343 : Blo 1044610 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B6697961 : Blo 1044610 6697961 := bstep (se 2 (by rfl) ⟨2511735, by rfl⟩ : syracuseStep 6697961 = 5023471) B5023471
theorem B5652251 : Blo 1044610 5652251 := bstep (se 1 (by rfl) ⟨4239188, by rfl⟩ : syracuseStep 5652251 = 8478377) B8478377
theorem B5292863 : Blo 1044610 5292863 := bstep (se 1 (by rfl) ⟨3969647, by rfl⟩ : syracuseStep 5292863 = 7939295) B7939295
theorem B86067197 : Blo 1044610 86067197 := bstep (se 3 (by rfl) ⟨16137599, by rfl⟩ : syracuseStep 86067197 = 32275199) B32275199
theorem B5035391 : Blo 1044610 5035391 := bstep (se 1 (by rfl) ⟨3776543, by rfl⟩ : syracuseStep 5035391 = 7553087) B7553087
theorem B5363273 : Blo 1044610 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B61137767 : Blo 1044610 61137767 := bstep (se 1 (by rfl) ⟨45853325, by rfl⟩ : syracuseStep 61137767 = 91706651) B91706651
theorem B12707837 : Blo 1044610 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B5958299 : Blo 1044610 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B1567775 : Blo 1044610 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B1044783 : Blo 1044610 1044783 := bstep (se 1 (by rfl) ⟨783587, by rfl⟩ : syracuseStep 1044783 = 1567175) B1567175
theorem B1569449 : Blo 1044610 1569449 := bstep (se 2 (by rfl) ⟨588543, by rfl⟩ : syracuseStep 1569449 = 1177087) B1177087
theorem B134380457 : Blo 1044610 134380457 := bstep (se 2 (by rfl) ⟨50392671, by rfl⟩ : syracuseStep 134380457 = 100785343) B100785343
theorem B6716519 : Blo 1044610 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B1572857 : Blo 1044610 1572857 := bstep (se 2 (by rfl) ⟨589821, by rfl⟩ : syracuseStep 1572857 = 1179643) B1179643
theorem B57378131 : Blo 1044610 57378131 := bstep (se 1 (by rfl) ⟨43033598, by rfl⟩ : syracuseStep 57378131 = 86067197) B86067197
theorem B3575515 : Blo 1044610 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B8590895 : Blo 1044610 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B3972199 : Blo 1044610 3972199 := bstep (se 1 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 3972199 = 5958299) B5958299
theorem B4465307 : Blo 1044610 4465307 := bstep (se 1 (by rfl) ⟨3348980, by rfl⟩ : syracuseStep 4465307 = 6697961) B6697961
theorem B3978503 : Blo 1044610 3978503 := bstep (se 1 (by rfl) ⟨2983877, by rfl⟩ : syracuseStep 3978503 = 5967755) B5967755
theorem B3356927 : Blo 1044610 3356927 := bstep (se 1 (by rfl) ⟨2517695, by rfl⟩ : syracuseStep 3356927 = 5035391) B5035391
theorem B26197991 : Blo 1044610 26197991 := bstep (se 1 (by rfl) ⟨19648493, by rfl⟩ : syracuseStep 26197991 = 39296987) B39296987
theorem B8471891 : Blo 1044610 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B4477679 : Blo 1044610 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B3528575 : Blo 1044610 3528575 := bstep (se 1 (by rfl) ⟨2646431, by rfl⟩ : syracuseStep 3528575 = 5292863) B5292863
theorem B11295719 : Blo 1044610 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B17915903 : Blo 1044610 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B40758511 : Blo 1044610 40758511 := bstep (se 1 (by rfl) ⟨30568883, by rfl⟩ : syracuseStep 40758511 = 61137767) B61137767
theorem B1045183 : Blo 1044610 1045183 := bstep (se 1 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 1045183 = 1567775) B1567775
theorem B26834489 : Blo 1044610 26834489 := bstep (se 2 (by rfl) ⟨10062933, by rfl⟩ : syracuseStep 26834489 = 20125867) B20125867
theorem B1046299 : Blo 1044610 1046299 := bstep (se 1 (by rfl) ⟨784724, by rfl⟩ : syracuseStep 1046299 = 1569449) B1569449
theorem B89586971 : Blo 1044610 89586971 := bstep (se 1 (by rfl) ⟨67190228, by rfl⟩ : syracuseStep 89586971 = 134380457) B134380457
theorem B3768167 : Blo 1044610 3768167 := bstep (se 1 (by rfl) ⟨2826125, by rfl⟩ : syracuseStep 3768167 = 5652251) B5652251
theorem B1048571 : Blo 1044610 1048571 := bstep (se 1 (by rfl) ⟨786428, by rfl⟩ : syracuseStep 1048571 = 1572857) B1572857
theorem B2985119 : Blo 1044610 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B2237951 : Blo 1044610 2237951 := bstep (se 1 (by rfl) ⟨1678463, by rfl⟩ : syracuseStep 2237951 = 3356927) B3356927
theorem B38252087 : Blo 1044610 38252087 := bstep (se 1 (by rfl) ⟨28689065, by rfl⟩ : syracuseStep 38252087 = 57378131) B57378131
theorem B11907485 : Blo 1044610 11907485 := bstep (se 3 (by rfl) ⟨2232653, by rfl⟩ : syracuseStep 11907485 = 4465307) B4465307
theorem B22591709 : Blo 1044610 22591709 := bstep (se 3 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 22591709 = 8471891) B8471891
theorem B54344681 : Blo 1044610 54344681 := bstep (se 2 (by rfl) ⟨20379255, by rfl⟩ : syracuseStep 54344681 = 40758511) B40758511
theorem B4767353 : Blo 1044610 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B11943935 : Blo 1044610 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B5296265 : Blo 1044610 5296265 := bstep (se 2 (by rfl) ⟨1986099, by rfl⟩ : syracuseStep 5296265 = 3972199) B3972199
theorem B59724647 : Blo 1044610 59724647 := bstep (se 1 (by rfl) ⟨44793485, by rfl⟩ : syracuseStep 59724647 = 89586971) B89586971
theorem B10048445 : Blo 1044610 10048445 := bstep (se 3 (by rfl) ⟨1884083, by rfl⟩ : syracuseStep 10048445 = 3768167) B3768167
theorem B5727263 : Blo 1044610 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B2352383 : Blo 1044610 2352383 := bstep (se 1 (by rfl) ⟨1764287, by rfl⟩ : syracuseStep 2352383 = 3528575) B3528575
theorem B7530479 : Blo 1044610 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B2652335 : Blo 1044610 2652335 := bstep (se 1 (by rfl) ⟨1989251, by rfl⟩ : syracuseStep 2652335 = 3978503) B3978503
theorem B17889659 : Blo 1044610 17889659 := bstep (se 1 (by rfl) ⟨13417244, by rfl⟩ : syracuseStep 17889659 = 26834489) B26834489
theorem B17465327 : Blo 1044610 17465327 := bstep (se 1 (by rfl) ⟨13098995, by rfl⟩ : syracuseStep 17465327 = 26197991) B26197991
theorem B15272701 : Blo 1044610 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B39816431 : Blo 1044610 39816431 := bstep (se 1 (by rfl) ⟨29862323, by rfl⟩ : syracuseStep 39816431 = 59724647) B59724647
theorem B5020319 : Blo 1044610 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B25501391 : Blo 1044610 25501391 := bstep (se 1 (by rfl) ⟨19126043, by rfl⟩ : syracuseStep 25501391 = 38252087) B38252087
theorem B7938323 : Blo 1044610 7938323 := bstep (se 1 (by rfl) ⟨5953742, by rfl⟩ : syracuseStep 7938323 = 11907485) B11907485
theorem B11643551 : Blo 1044610 11643551 := bstep (se 1 (by rfl) ⟨8732663, by rfl⟩ : syracuseStep 11643551 = 17465327) B17465327
theorem B6698963 : Blo 1044610 6698963 := bstep (se 1 (by rfl) ⟨5024222, by rfl⟩ : syracuseStep 6698963 = 10048445) B10048445
theorem B1491967 : Blo 1044610 1491967 := bstep (se 1 (by rfl) ⟨1118975, by rfl⟩ : syracuseStep 1491967 = 2237951) B2237951
theorem B7962623 : Blo 1044610 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B15061139 : Blo 1044610 15061139 := bstep (se 1 (by rfl) ⟨11295854, by rfl⟩ : syracuseStep 15061139 = 22591709) B22591709
theorem B36229787 : Blo 1044610 36229787 := bstep (se 1 (by rfl) ⟨27172340, by rfl⟩ : syracuseStep 36229787 = 54344681) B54344681
theorem B1990079 : Blo 1044610 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B3530843 : Blo 1044610 3530843 := bstep (se 1 (by rfl) ⟨2648132, by rfl⟩ : syracuseStep 3530843 = 5296265) B5296265
theorem B1568255 : Blo 1044610 1568255 := bstep (se 1 (by rfl) ⟨1176191, by rfl⟩ : syracuseStep 1568255 = 2352383) B2352383
theorem B1768223 : Blo 1044610 1768223 := bstep (se 1 (by rfl) ⟨1326167, by rfl⟩ : syracuseStep 1768223 = 2652335) B2652335
theorem B11926439 : Blo 1044610 11926439 := bstep (se 1 (by rfl) ⟨8944829, by rfl⟩ : syracuseStep 11926439 = 17889659) B17889659
theorem B3178235 : Blo 1044610 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B5308415 : Blo 1044610 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B26544287 : Blo 1044610 26544287 := bstep (se 1 (by rfl) ⟨19908215, by rfl⟩ : syracuseStep 26544287 = 39816431) B39816431
theorem B24153191 : Blo 1044610 24153191 := bstep (se 1 (by rfl) ⟨18114893, by rfl⟩ : syracuseStep 24153191 = 36229787) B36229787
theorem B124197877 : Blo 1044610 124197877 := bstep (se 5 (by rfl) ⟨5821775, by rfl⟩ : syracuseStep 124197877 = 11643551) B11643551
theorem B4465975 : Blo 1044610 4465975 := bstep (se 1 (by rfl) ⟨3349481, by rfl⟩ : syracuseStep 4465975 = 6698963) B6698963
theorem B10040759 : Blo 1044610 10040759 := bstep (se 1 (by rfl) ⟨7530569, by rfl⟩ : syracuseStep 10040759 = 15061139) B15061139
theorem B1326719 : Blo 1044610 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B5292215 : Blo 1044610 5292215 := bstep (se 1 (by rfl) ⟨3969161, by rfl⟩ : syracuseStep 5292215 = 7938323) B7938323
theorem B13387517 : Blo 1044610 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B7950959 : Blo 1044610 7950959 := bstep (se 1 (by rfl) ⟨5963219, by rfl⟩ : syracuseStep 7950959 = 11926439) B11926439
theorem B8475293 : Blo 1044610 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B1989289 : Blo 1044610 1989289 := bstep (se 2 (by rfl) ⟨745983, by rfl⟩ : syracuseStep 1989289 = 1491967) B1491967
theorem B81454405 : Blo 1044610 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B17000927 : Blo 1044610 17000927 := bstep (se 1 (by rfl) ⟨12750695, by rfl⟩ : syracuseStep 17000927 = 25501391) B25501391
theorem B2353895 : Blo 1044610 2353895 := bstep (se 1 (by rfl) ⟨1765421, by rfl⟩ : syracuseStep 2353895 = 3530843) B3530843
theorem B1045503 : Blo 1044610 1045503 := bstep (se 1 (by rfl) ⟨784127, by rfl⟩ : syracuseStep 1045503 = 1568255) B1568255
theorem B1178815 : Blo 1044610 1178815 := bstep (se 1 (by rfl) ⟨884111, by rfl⟩ : syracuseStep 1178815 = 1768223) B1768223
theorem B17696191 : Blo 1044610 17696191 := bstep (se 1 (by rfl) ⟨13272143, by rfl⟩ : syracuseStep 17696191 = 26544287) B26544287
theorem B6693839 : Blo 1044610 6693839 := bstep (se 1 (by rfl) ⟨5020379, by rfl⟩ : syracuseStep 6693839 = 10040759) B10040759
theorem B8925011 : Blo 1044610 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B3538943 : Blo 1044610 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B108605873 : Blo 1044610 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B16102127 : Blo 1044610 16102127 := bstep (se 1 (by rfl) ⟨12076595, by rfl⟩ : syracuseStep 16102127 = 24153191) B24153191
theorem B5650195 : Blo 1044610 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B165597169 : Blo 1044610 165597169 := bstep (se 2 (by rfl) ⟨62098938, by rfl⟩ : syracuseStep 165597169 = 124197877) B124197877
theorem B3528143 : Blo 1044610 3528143 := bstep (se 1 (by rfl) ⟨2646107, by rfl⟩ : syracuseStep 3528143 = 5292215) B5292215
theorem B5954633 : Blo 1044610 5954633 := bstep (se 2 (by rfl) ⟨2232987, by rfl⟩ : syracuseStep 5954633 = 4465975) B4465975
theorem B5300639 : Blo 1044610 5300639 := bstep (se 1 (by rfl) ⟨3975479, by rfl⟩ : syracuseStep 5300639 = 7950959) B7950959
theorem B11333951 : Blo 1044610 11333951 := bstep (se 1 (by rfl) ⟨8500463, by rfl⟩ : syracuseStep 11333951 = 17000927) B17000927
theorem B1569263 : Blo 1044610 1569263 := bstep (se 1 (by rfl) ⟨1176947, by rfl⟩ : syracuseStep 1569263 = 2353895) B2353895
theorem B2652385 : Blo 1044610 2652385 := bstep (se 2 (by rfl) ⟨994644, by rfl⟩ : syracuseStep 2652385 = 1989289) B1989289
theorem B1571753 : Blo 1044610 1571753 := bstep (se 2 (by rfl) ⟨589407, by rfl⟩ : syracuseStep 1571753 = 1178815) B1178815
theorem B3537917 : Blo 1044610 3537917 := bstep (se 3 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 3537917 = 1326719) B1326719
theorem B23594921 : Blo 1044610 23594921 := bstep (se 2 (by rfl) ⟨8848095, by rfl⟩ : syracuseStep 23594921 = 17696191) B17696191
theorem B3969755 : Blo 1044610 3969755 := bstep (se 1 (by rfl) ⟨2977316, by rfl⟩ : syracuseStep 3969755 = 5954633) B5954633
theorem B220796225 : Blo 1044610 220796225 := bstep (se 2 (by rfl) ⟨82798584, by rfl⟩ : syracuseStep 220796225 = 165597169) B165597169
theorem B4462559 : Blo 1044610 4462559 := bstep (se 1 (by rfl) ⟨3346919, by rfl⟩ : syracuseStep 4462559 = 6693839) B6693839
theorem B2359295 : Blo 1044610 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B5950007 : Blo 1044610 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B7555967 : Blo 1044610 7555967 := bstep (se 1 (by rfl) ⟨5666975, by rfl⟩ : syracuseStep 7555967 = 11333951) B11333951
theorem B72403915 : Blo 1044610 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B10734751 : Blo 1044610 10734751 := bstep (se 1 (by rfl) ⟨8051063, by rfl⟩ : syracuseStep 10734751 = 16102127) B16102127
theorem B2352095 : Blo 1044610 2352095 := bstep (se 1 (by rfl) ⟨1764071, by rfl⟩ : syracuseStep 2352095 = 3528143) B3528143
theorem B3533759 : Blo 1044610 3533759 := bstep (se 1 (by rfl) ⟨2650319, by rfl⟩ : syracuseStep 3533759 = 5300639) B5300639
theorem B7533593 : Blo 1044610 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B3536513 : Blo 1044610 3536513 := bstep (se 2 (by rfl) ⟨1326192, by rfl⟩ : syracuseStep 3536513 = 2652385) B2652385
theorem B1046175 : Blo 1044610 1046175 := bstep (se 1 (by rfl) ⟨784631, by rfl⟩ : syracuseStep 1046175 = 1569263) B1569263
theorem B1047835 : Blo 1044610 1047835 := bstep (se 1 (by rfl) ⟨785876, by rfl⟩ : syracuseStep 1047835 = 1571753) B1571753
theorem B2358611 : Blo 1044610 2358611 := bstep (se 1 (by rfl) ⟨1768958, by rfl⟩ : syracuseStep 2358611 = 3537917) B3537917
theorem B15729947 : Blo 1044610 15729947 := bstep (se 1 (by rfl) ⟨11797460, by rfl⟩ : syracuseStep 15729947 = 23594921) B23594921
theorem B3966671 : Blo 1044610 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B147197483 : Blo 1044610 147197483 := bstep (se 1 (by rfl) ⟨110398112, by rfl⟩ : syracuseStep 147197483 = 220796225) B220796225
theorem B96538553 : Blo 1044610 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B57252005 : Blo 1044610 57252005 := bstep (se 4 (by rfl) ⟨5367375, by rfl⟩ : syracuseStep 57252005 = 10734751) B10734751
theorem B5022395 : Blo 1044610 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B1572863 : Blo 1044610 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B5037311 : Blo 1044610 5037311 := bstep (se 1 (by rfl) ⟨3777983, by rfl⟩ : syracuseStep 5037311 = 7555967) B7555967
theorem B2646503 : Blo 1044610 2646503 := bstep (se 1 (by rfl) ⟨1984877, by rfl⟩ : syracuseStep 2646503 = 3969755) B3969755
theorem B2975039 : Blo 1044610 2975039 := bstep (se 1 (by rfl) ⟨2231279, by rfl⟩ : syracuseStep 2975039 = 4462559) B4462559
theorem B1568063 : Blo 1044610 1568063 := bstep (se 1 (by rfl) ⟨1176047, by rfl⟩ : syracuseStep 1568063 = 2352095) B2352095
theorem B2355839 : Blo 1044610 2355839 := bstep (se 1 (by rfl) ⟨1766879, by rfl⟩ : syracuseStep 2355839 = 3533759) B3533759
theorem B2357675 : Blo 1044610 2357675 := bstep (se 1 (by rfl) ⟨1768256, by rfl⟩ : syracuseStep 2357675 = 3536513) B3536513
theorem B1572407 : Blo 1044610 1572407 := bstep (se 1 (by rfl) ⟨1179305, by rfl⟩ : syracuseStep 1572407 = 2358611) B2358611
theorem B10486631 : Blo 1044610 10486631 := bstep (se 1 (by rfl) ⟨7864973, by rfl⟩ : syracuseStep 10486631 = 15729947) B15729947
theorem B64359035 : Blo 1044610 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B3348263 : Blo 1044610 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B3358207 : Blo 1044610 3358207 := bstep (se 1 (by rfl) ⟨2518655, by rfl⟩ : syracuseStep 3358207 = 5037311) B5037311
theorem B1983359 : Blo 1044610 1983359 := bstep (se 1 (by rfl) ⟨1487519, by rfl⟩ : syracuseStep 1983359 = 2975039) B2975039
theorem B2644447 : Blo 1044610 2644447 := bstep (se 1 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 2644447 = 3966671) B3966671
theorem B98131655 : Blo 1044610 98131655 := bstep (se 1 (by rfl) ⟨73598741, by rfl⟩ : syracuseStep 98131655 = 147197483) B147197483
theorem B38168003 : Blo 1044610 38168003 := bstep (se 1 (by rfl) ⟨28626002, by rfl⟩ : syracuseStep 38168003 = 57252005) B57252005
theorem B1764335 : Blo 1044610 1764335 := bstep (se 1 (by rfl) ⟨1323251, by rfl⟩ : syracuseStep 1764335 = 2646503) B2646503
theorem B1045375 : Blo 1044610 1045375 := bstep (se 1 (by rfl) ⟨784031, by rfl⟩ : syracuseStep 1045375 = 1568063) B1568063
theorem B1570559 : Blo 1044610 1570559 := bstep (se 1 (by rfl) ⟨1177919, by rfl⟩ : syracuseStep 1570559 = 2355839) B2355839
theorem B1571783 : Blo 1044610 1571783 := bstep (se 1 (by rfl) ⟨1178837, by rfl⟩ : syracuseStep 1571783 = 2357675) B2357675
theorem B1048271 : Blo 1044610 1048271 := bstep (se 1 (by rfl) ⟨786203, by rfl⟩ : syracuseStep 1048271 = 1572407) B1572407
theorem B1048575 : Blo 1044610 1048575 := bstep (se 1 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 1048575 = 1572863) B1572863
theorem B1322239 : Blo 1044610 1322239 := bstep (se 1 (by rfl) ⟨991679, by rfl⟩ : syracuseStep 1322239 = 1983359) B1983359
theorem B42906023 : Blo 1044610 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B27964349 : Blo 1044610 27964349 := bstep (se 3 (by rfl) ⟨5243315, by rfl⟩ : syracuseStep 27964349 = 10486631) B10486631
theorem B8928701 : Blo 1044610 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B65421103 : Blo 1044610 65421103 := bstep (se 1 (by rfl) ⟨49065827, by rfl⟩ : syracuseStep 65421103 = 98131655) B98131655
theorem B25445335 : Blo 1044610 25445335 := bstep (se 1 (by rfl) ⟨19084001, by rfl⟩ : syracuseStep 25445335 = 38168003) B38168003
theorem B3525929 : Blo 1044610 3525929 := bstep (se 2 (by rfl) ⟨1322223, by rfl⟩ : syracuseStep 3525929 = 2644447) B2644447
theorem B4477609 : Blo 1044610 4477609 := bstep (se 2 (by rfl) ⟨1679103, by rfl⟩ : syracuseStep 4477609 = 3358207) B3358207
theorem B1176223 : Blo 1044610 1176223 := bstep (se 1 (by rfl) ⟨882167, by rfl⟩ : syracuseStep 1176223 = 1764335) B1764335
theorem B1047039 : Blo 1044610 1047039 := bstep (se 1 (by rfl) ⟨785279, by rfl⟩ : syracuseStep 1047039 = 1570559) B1570559
theorem B1047855 : Blo 1044610 1047855 := bstep (se 1 (by rfl) ⟨785891, by rfl⟩ : syracuseStep 1047855 = 1571783) B1571783
theorem B5970145 : Blo 1044610 5970145 := bstep (se 2 (by rfl) ⟨2238804, by rfl⟩ : syracuseStep 5970145 = 4477609) B4477609
theorem B33927113 : Blo 1044610 33927113 := bstep (se 2 (by rfl) ⟨12722667, by rfl⟩ : syracuseStep 33927113 = 25445335) B25445335
theorem B5952467 : Blo 1044610 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B2350619 : Blo 1044610 2350619 := bstep (se 1 (by rfl) ⟨1762964, by rfl⟩ : syracuseStep 2350619 = 3525929) B3525929
theorem B1762985 : Blo 1044610 1762985 := bstep (se 2 (by rfl) ⟨661119, by rfl⟩ : syracuseStep 1762985 = 1322239) B1322239
theorem B1568297 : Blo 1044610 1568297 := bstep (se 2 (by rfl) ⟨588111, by rfl⟩ : syracuseStep 1568297 = 1176223) B1176223
theorem B28604015 : Blo 1044610 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B18642899 : Blo 1044610 18642899 := bstep (se 1 (by rfl) ⟨13982174, by rfl⟩ : syracuseStep 18642899 = 27964349) B27964349
theorem B87228137 : Blo 1044610 87228137 := bstep (se 2 (by rfl) ⟨32710551, by rfl⟩ : syracuseStep 87228137 = 65421103) B65421103
theorem B3968311 : Blo 1044610 3968311 := bstep (se 1 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 3968311 = 5952467) B5952467
theorem B22618075 : Blo 1044610 22618075 := bstep (se 1 (by rfl) ⟨16963556, by rfl⟩ : syracuseStep 22618075 = 33927113) B33927113
theorem B12428599 : Blo 1044610 12428599 := bstep (se 1 (by rfl) ⟨9321449, by rfl⟩ : syracuseStep 12428599 = 18642899) B18642899
theorem B58152091 : Blo 1044610 58152091 := bstep (se 1 (by rfl) ⟨43614068, by rfl⟩ : syracuseStep 58152091 = 87228137) B87228137
theorem B1567079 : Blo 1044610 1567079 := bstep (se 1 (by rfl) ⟨1175309, by rfl⟩ : syracuseStep 1567079 = 2350619) B2350619
theorem B1175323 : Blo 1044610 1175323 := bstep (se 1 (by rfl) ⟨881492, by rfl⟩ : syracuseStep 1175323 = 1762985) B1762985
theorem B1045531 : Blo 1044610 1045531 := bstep (se 1 (by rfl) ⟨784148, by rfl⟩ : syracuseStep 1045531 = 1568297) B1568297
theorem B7960193 : Blo 1044610 7960193 := bstep (se 2 (by rfl) ⟨2985072, by rfl⟩ : syracuseStep 7960193 = 5970145) B5970145
theorem B19069343 : Blo 1044610 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B77536121 : Blo 1044610 77536121 := bstep (se 2 (by rfl) ⟨29076045, by rfl⟩ : syracuseStep 77536121 = 58152091) B58152091
theorem B30157433 : Blo 1044610 30157433 := bstep (se 2 (by rfl) ⟨11309037, by rfl⟩ : syracuseStep 30157433 = 22618075) B22618075
theorem B5291081 : Blo 1044610 5291081 := bstep (se 2 (by rfl) ⟨1984155, by rfl⟩ : syracuseStep 5291081 = 3968311) B3968311
theorem B16571465 : Blo 1044610 16571465 := bstep (se 2 (by rfl) ⟨6214299, by rfl⟩ : syracuseStep 16571465 = 12428599) B12428599
theorem B1567097 : Blo 1044610 1567097 := bstep (se 2 (by rfl) ⟨587661, by rfl⟩ : syracuseStep 1567097 = 1175323) B1175323
theorem B1044719 : Blo 1044610 1044719 := bstep (se 1 (by rfl) ⟨783539, by rfl⟩ : syracuseStep 1044719 = 1567079) B1567079
theorem B5306795 : Blo 1044610 5306795 := bstep (se 1 (by rfl) ⟨3980096, by rfl⟩ : syracuseStep 5306795 = 7960193) B7960193
theorem B12712895 : Blo 1044610 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B11047643 : Blo 1044610 11047643 := bstep (se 1 (by rfl) ⟨8285732, by rfl⟩ : syracuseStep 11047643 = 16571465) B16571465
theorem B20104955 : Blo 1044610 20104955 := bstep (se 1 (by rfl) ⟨15078716, by rfl⟩ : syracuseStep 20104955 = 30157433) B30157433
theorem B8475263 : Blo 1044610 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B3527387 : Blo 1044610 3527387 := bstep (se 1 (by rfl) ⟨2645540, by rfl⟩ : syracuseStep 3527387 = 5291081) B5291081
theorem B1044731 : Blo 1044610 1044731 := bstep (se 1 (by rfl) ⟨783548, by rfl⟩ : syracuseStep 1044731 = 1567097) B1567097
theorem B206762989 : Blo 1044610 206762989 := bstep (se 3 (by rfl) ⟨38768060, by rfl⟩ : syracuseStep 206762989 = 77536121) B77536121
theorem B3537863 : Blo 1044610 3537863 := bstep (se 1 (by rfl) ⟨2653397, by rfl⟩ : syracuseStep 3537863 = 5306795) B5306795
theorem B13403303 : Blo 1044610 13403303 := bstep (se 1 (by rfl) ⟨10052477, by rfl⟩ : syracuseStep 13403303 = 20104955) B20104955
theorem B275683985 : Blo 1044610 275683985 := bstep (se 2 (by rfl) ⟨103381494, by rfl⟩ : syracuseStep 275683985 = 206762989) B206762989
theorem B5650175 : Blo 1044610 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B2351591 : Blo 1044610 2351591 := bstep (se 1 (by rfl) ⟨1763693, by rfl⟩ : syracuseStep 2351591 = 3527387) B3527387
theorem B7365095 : Blo 1044610 7365095 := bstep (se 1 (by rfl) ⟨5523821, by rfl⟩ : syracuseStep 7365095 = 11047643) B11047643
theorem B2358575 : Blo 1044610 2358575 := bstep (se 1 (by rfl) ⟨1768931, by rfl⟩ : syracuseStep 2358575 = 3537863) B3537863
theorem B8935535 : Blo 1044610 8935535 := bstep (se 1 (by rfl) ⟨6701651, by rfl⟩ : syracuseStep 8935535 = 13403303) B13403303
theorem B183789323 : Blo 1044610 183789323 := bstep (se 1 (by rfl) ⟨137841992, by rfl⟩ : syracuseStep 183789323 = 275683985) B275683985
theorem B15067133 : Blo 1044610 15067133 := bstep (se 3 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 15067133 = 5650175) B5650175
theorem B1567727 : Blo 1044610 1567727 := bstep (se 1 (by rfl) ⟨1175795, by rfl⟩ : syracuseStep 1567727 = 2351591) B2351591
theorem B4910063 : Blo 1044610 4910063 := bstep (se 1 (by rfl) ⟨3682547, by rfl⟩ : syracuseStep 4910063 = 7365095) B7365095
theorem B1572383 : Blo 1044610 1572383 := bstep (se 1 (by rfl) ⟨1179287, by rfl⟩ : syracuseStep 1572383 = 2358575) B2358575
theorem B122526215 : Blo 1044610 122526215 := bstep (se 1 (by rfl) ⟨91894661, by rfl⟩ : syracuseStep 122526215 = 183789323) B183789323
theorem B10044755 : Blo 1044610 10044755 := bstep (se 1 (by rfl) ⟨7533566, by rfl⟩ : syracuseStep 10044755 = 15067133) B15067133
theorem B13093501 : Blo 1044610 13093501 := bstep (se 3 (by rfl) ⟨2455031, by rfl⟩ : syracuseStep 13093501 = 4910063) B4910063
theorem B5957023 : Blo 1044610 5957023 := bstep (se 1 (by rfl) ⟨4467767, by rfl⟩ : syracuseStep 5957023 = 8935535) B8935535
theorem B1045151 : Blo 1044610 1045151 := bstep (se 1 (by rfl) ⟨783863, by rfl⟩ : syracuseStep 1045151 = 1567727) B1567727
theorem B1048255 : Blo 1044610 1048255 := bstep (se 1 (by rfl) ⟨786191, by rfl⟩ : syracuseStep 1048255 = 1572383) B1572383
theorem B6696503 : Blo 1044610 6696503 := bstep (se 1 (by rfl) ⟨5022377, by rfl⟩ : syracuseStep 6696503 = 10044755) B10044755
theorem B7942697 : Blo 1044610 7942697 := bstep (se 2 (by rfl) ⟨2978511, by rfl⟩ : syracuseStep 7942697 = 5957023) B5957023
theorem B17458001 : Blo 1044610 17458001 := bstep (se 2 (by rfl) ⟨6546750, by rfl⟩ : syracuseStep 17458001 = 13093501) B13093501
theorem B81684143 : Blo 1044610 81684143 := bstep (se 1 (by rfl) ⟨61263107, by rfl⟩ : syracuseStep 81684143 = 122526215) B122526215
theorem B11638667 : Blo 1044610 11638667 := bstep (se 1 (by rfl) ⟨8729000, by rfl⟩ : syracuseStep 11638667 = 17458001) B17458001
theorem B4464335 : Blo 1044610 4464335 := bstep (se 1 (by rfl) ⟨3348251, by rfl⟩ : syracuseStep 4464335 = 6696503) B6696503
theorem B5295131 : Blo 1044610 5295131 := bstep (se 1 (by rfl) ⟨3971348, by rfl⟩ : syracuseStep 5295131 = 7942697) B7942697
theorem B54456095 : Blo 1044610 54456095 := bstep (se 1 (by rfl) ⟨40842071, by rfl⟩ : syracuseStep 54456095 = 81684143) B81684143
theorem B145216253 : Blo 1044610 145216253 := bstep (se 3 (by rfl) ⟨27228047, by rfl⟩ : syracuseStep 145216253 = 54456095) B54456095
theorem B3530087 : Blo 1044610 3530087 := bstep (se 1 (by rfl) ⟨2647565, by rfl⟩ : syracuseStep 3530087 = 5295131) B5295131
theorem B7759111 : Blo 1044610 7759111 := bstep (se 1 (by rfl) ⟨5819333, by rfl⟩ : syracuseStep 7759111 = 11638667) B11638667
theorem B2976223 : Blo 1044610 2976223 := bstep (se 1 (by rfl) ⟨2232167, by rfl⟩ : syracuseStep 2976223 = 4464335) B4464335
theorem B3968297 : Blo 1044610 3968297 := bstep (se 2 (by rfl) ⟨1488111, by rfl⟩ : syracuseStep 3968297 = 2976223) B2976223
theorem B96810835 : Blo 1044610 96810835 := bstep (se 1 (by rfl) ⟨72608126, by rfl⟩ : syracuseStep 96810835 = 145216253) B145216253
theorem B10345481 : Blo 1044610 10345481 := bstep (se 2 (by rfl) ⟨3879555, by rfl⟩ : syracuseStep 10345481 = 7759111) B7759111
theorem B2353391 : Blo 1044610 2353391 := bstep (se 1 (by rfl) ⟨1765043, by rfl⟩ : syracuseStep 2353391 = 3530087) B3530087
theorem B129081113 : Blo 1044610 129081113 := bstep (se 2 (by rfl) ⟨48405417, by rfl⟩ : syracuseStep 129081113 = 96810835) B96810835
theorem B6896987 : Blo 1044610 6896987 := bstep (se 1 (by rfl) ⟨5172740, by rfl⟩ : syracuseStep 6896987 = 10345481) B10345481
theorem B2645531 : Blo 1044610 2645531 := bstep (se 1 (by rfl) ⟨1984148, by rfl⟩ : syracuseStep 2645531 = 3968297) B3968297
theorem B1568927 : Blo 1044610 1568927 := bstep (se 1 (by rfl) ⟨1176695, by rfl⟩ : syracuseStep 1568927 = 2353391) B2353391
theorem B86054075 : Blo 1044610 86054075 := bstep (se 1 (by rfl) ⟨64540556, by rfl⟩ : syracuseStep 86054075 = 129081113) B129081113
theorem B4597991 : Blo 1044610 4597991 := bstep (se 1 (by rfl) ⟨3448493, by rfl⟩ : syracuseStep 4597991 = 6896987) B6896987
theorem B1763687 : Blo 1044610 1763687 := bstep (se 1 (by rfl) ⟨1322765, by rfl⟩ : syracuseStep 1763687 = 2645531) B2645531
theorem B1045951 : Blo 1044610 1045951 := bstep (se 1 (by rfl) ⟨784463, by rfl⟩ : syracuseStep 1045951 = 1568927) B1568927
theorem B3065327 : Blo 1044610 3065327 := bstep (se 1 (by rfl) ⟨2298995, by rfl⟩ : syracuseStep 3065327 = 4597991) B4597991
theorem B57369383 : Blo 1044610 57369383 := bstep (se 1 (by rfl) ⟨43027037, by rfl⟩ : syracuseStep 57369383 = 86054075) B86054075
theorem B1175791 : Blo 1044610 1175791 := bstep (se 1 (by rfl) ⟨881843, by rfl⟩ : syracuseStep 1175791 = 1763687) B1763687
theorem B38246255 : Blo 1044610 38246255 := bstep (se 1 (by rfl) ⟨28684691, by rfl⟩ : syracuseStep 38246255 = 57369383) B57369383
theorem B32696821 : Blo 1044610 32696821 := bstep (se 5 (by rfl) ⟨1532663, by rfl⟩ : syracuseStep 32696821 = 3065327) B3065327
theorem B1567721 : Blo 1044610 1567721 := bstep (se 2 (by rfl) ⟨587895, by rfl⟩ : syracuseStep 1567721 = 1175791) B1175791
theorem B25497503 : Blo 1044610 25497503 := bstep (se 1 (by rfl) ⟨19123127, by rfl⟩ : syracuseStep 25497503 = 38246255) B38246255
theorem B43595761 : Blo 1044610 43595761 := bstep (se 2 (by rfl) ⟨16348410, by rfl⟩ : syracuseStep 43595761 = 32696821) B32696821
theorem B1045147 : Blo 1044610 1045147 := bstep (se 1 (by rfl) ⟨783860, by rfl⟩ : syracuseStep 1045147 = 1567721) B1567721
theorem B16998335 : Blo 1044610 16998335 := bstep (se 1 (by rfl) ⟨12748751, by rfl⟩ : syracuseStep 16998335 = 25497503) B25497503
theorem B58127681 : Blo 1044610 58127681 := bstep (se 2 (by rfl) ⟨21797880, by rfl⟩ : syracuseStep 58127681 = 43595761) B43595761
theorem B38751787 : Blo 1044610 38751787 := bstep (se 1 (by rfl) ⟨29063840, by rfl⟩ : syracuseStep 38751787 = 58127681) B58127681
theorem B11332223 : Blo 1044610 11332223 := bstep (se 1 (by rfl) ⟨8499167, by rfl⟩ : syracuseStep 11332223 = 16998335) B16998335
theorem B7554815 : Blo 1044610 7554815 := bstep (se 1 (by rfl) ⟨5666111, by rfl⟩ : syracuseStep 7554815 = 11332223) B11332223
theorem B51669049 : Blo 1044610 51669049 := bstep (se 2 (by rfl) ⟨19375893, by rfl⟩ : syracuseStep 51669049 = 38751787) B38751787
theorem B68892065 : Blo 1044610 68892065 := bstep (se 2 (by rfl) ⟨25834524, by rfl⟩ : syracuseStep 68892065 = 51669049) B51669049
theorem B5036543 : Blo 1044610 5036543 := bstep (se 1 (by rfl) ⟨3777407, by rfl⟩ : syracuseStep 5036543 = 7554815) B7554815
theorem B3357695 : Blo 1044610 3357695 := bstep (se 1 (by rfl) ⟨2518271, by rfl⟩ : syracuseStep 3357695 = 5036543) B5036543
theorem B45928043 : Blo 1044610 45928043 := bstep (se 1 (by rfl) ⟨34446032, by rfl⟩ : syracuseStep 45928043 = 68892065) B68892065
theorem B2238463 : Blo 1044610 2238463 := bstep (se 1 (by rfl) ⟨1678847, by rfl⟩ : syracuseStep 2238463 = 3357695) B3357695
theorem B30618695 : Blo 1044610 30618695 := bstep (se 1 (by rfl) ⟨22964021, by rfl⟩ : syracuseStep 30618695 = 45928043) B45928043
theorem B2984617 : Blo 1044610 2984617 := bstep (se 2 (by rfl) ⟨1119231, by rfl⟩ : syracuseStep 2984617 = 2238463) B2238463
theorem B81649853 : Blo 1044610 81649853 := bstep (se 3 (by rfl) ⟨15309347, by rfl⟩ : syracuseStep 81649853 = 30618695) B30618695
theorem B54433235 : Blo 1044610 54433235 := bstep (se 1 (by rfl) ⟨40824926, by rfl⟩ : syracuseStep 54433235 = 81649853) B81649853
theorem B3979489 : Blo 1044610 3979489 := bstep (se 2 (by rfl) ⟨1492308, by rfl⟩ : syracuseStep 3979489 = 2984617) B2984617
theorem B36288823 : Blo 1044610 36288823 := bstep (se 1 (by rfl) ⟨27216617, by rfl⟩ : syracuseStep 36288823 = 54433235) B54433235
theorem B5305985 : Blo 1044610 5305985 := bstep (se 2 (by rfl) ⟨1989744, by rfl⟩ : syracuseStep 5305985 = 3979489) B3979489
theorem B48385097 : Blo 1044610 48385097 := bstep (se 2 (by rfl) ⟨18144411, by rfl⟩ : syracuseStep 48385097 = 36288823) B36288823
theorem B3537323 : Blo 1044610 3537323 := bstep (se 1 (by rfl) ⟨2652992, by rfl⟩ : syracuseStep 3537323 = 5305985) B5305985
theorem B32256731 : Blo 1044610 32256731 := bstep (se 1 (by rfl) ⟨24192548, by rfl⟩ : syracuseStep 32256731 = 48385097) B48385097
theorem B2358215 : Blo 1044610 2358215 := bstep (se 1 (by rfl) ⟨1768661, by rfl⟩ : syracuseStep 2358215 = 3537323) B3537323
theorem B21504487 : Blo 1044610 21504487 := bstep (se 1 (by rfl) ⟨16128365, by rfl⟩ : syracuseStep 21504487 = 32256731) B32256731
theorem B1572143 : Blo 1044610 1572143 := bstep (se 1 (by rfl) ⟨1179107, by rfl⟩ : syracuseStep 1572143 = 2358215) B2358215
theorem B28672649 : Blo 1044610 28672649 := bstep (se 2 (by rfl) ⟨10752243, by rfl⟩ : syracuseStep 28672649 = 21504487) B21504487
theorem B1048095 : Blo 1044610 1048095 := bstep (se 1 (by rfl) ⟨786071, by rfl⟩ : syracuseStep 1048095 = 1572143) B1572143
theorem B19115099 : Blo 1044610 19115099 := bstep (se 1 (by rfl) ⟨14336324, by rfl⟩ : syracuseStep 19115099 = 28672649) B28672649
theorem B12743399 : Blo 1044610 12743399 := bstep (se 1 (by rfl) ⟨9557549, by rfl⟩ : syracuseStep 12743399 = 19115099) B19115099
theorem B8495599 : Blo 1044610 8495599 := bstep (se 1 (by rfl) ⟨6371699, by rfl⟩ : syracuseStep 8495599 = 12743399) B12743399
theorem B11327465 : Blo 1044610 11327465 := bstep (se 2 (by rfl) ⟨4247799, by rfl⟩ : syracuseStep 11327465 = 8495599) B8495599
theorem B7551643 : Blo 1044610 7551643 := bstep (se 1 (by rfl) ⟨5663732, by rfl⟩ : syracuseStep 7551643 = 11327465) B11327465
theorem B10068857 : Blo 1044610 10068857 := bstep (se 2 (by rfl) ⟨3775821, by rfl⟩ : syracuseStep 10068857 = 7551643) B7551643
theorem B6712571 : Blo 1044610 6712571 := bstep (se 1 (by rfl) ⟨5034428, by rfl⟩ : syracuseStep 6712571 = 10068857) B10068857
theorem B4475047 : Blo 1044610 4475047 := bstep (se 1 (by rfl) ⟨3356285, by rfl⟩ : syracuseStep 4475047 = 6712571) B6712571
theorem B5966729 : Blo 1044610 5966729 := bstep (se 2 (by rfl) ⟨2237523, by rfl⟩ : syracuseStep 5966729 = 4475047) B4475047
theorem B3977819 : Blo 1044610 3977819 := bstep (se 1 (by rfl) ⟨2983364, by rfl⟩ : syracuseStep 3977819 = 5966729) B5966729
theorem B2651879 : Blo 1044610 2651879 := bstep (se 1 (by rfl) ⟨1988909, by rfl⟩ : syracuseStep 2651879 = 3977819) B3977819
theorem B1767919 : Blo 1044610 1767919 := bstep (se 1 (by rfl) ⟨1325939, by rfl⟩ : syracuseStep 1767919 = 2651879) B2651879
theorem B2357225 : Blo 1044610 2357225 := bstep (se 2 (by rfl) ⟨883959, by rfl⟩ : syracuseStep 2357225 = 1767919) B1767919
theorem B1571483 : Blo 1044610 1571483 := bstep (se 1 (by rfl) ⟨1178612, by rfl⟩ : syracuseStep 1571483 = 2357225) B2357225
theorem B1047655 : Blo 1044610 1047655 := bstep (se 1 (by rfl) ⟨785741, by rfl⟩ : syracuseStep 1047655 = 1571483) B1571483

theorem C0 (j : ℕ) (h1 : 261152 ≤ j) (h2 : j ≤ 261851) : Blo 1044610 (4 * j + 3) := by
  interval_cases j
  · exact B1044611
  · exact B1044615
  · exact B1044619
  · exact B1044623
  · exact B1044627
  · exact B1044631
  · exact B1044635
  · exact B1044639
  · exact B1044643
  · exact B1044647
  · exact B1044651
  · exact B1044655
  · exact B1044659
  · exact B1044663
  · exact B1044667
  · exact B1044671
  · exact B1044675
  · exact B1044679
  · exact B1044683
  · exact B1044687
  · exact B1044691
  · exact B1044695
  · exact B1044699
  · exact B1044703
  · exact B1044707
  · exact B1044711
  · exact B1044715
  · exact B1044719
  · exact B1044723
  · exact B1044727
  · exact B1044731
  · exact B1044735
  · exact B1044739
  · exact B1044743
  · exact B1044747
  · exact B1044751
  · exact B1044755
  · exact B1044759
  · exact B1044763
  · exact B1044767
  · exact B1044771
  · exact B1044775
  · exact B1044779
  · exact B1044783
  · exact B1044787
  · exact B1044791
  · exact B1044795
  · exact B1044799
  · exact B1044803
  · exact B1044807
  · exact B1044811
  · exact B1044815
  · exact B1044819
  · exact B1044823
  · exact B1044827
  · exact B1044831
  · exact B1044835
  · exact B1044839
  · exact B1044843
  · exact B1044847
  · exact B1044851
  · exact B1044855
  · exact B1044859
  · exact B1044863
  · exact B1044867
  · exact B1044871
  · exact B1044875
  · exact B1044879
  · exact B1044883
  · exact B1044887
  · exact B1044891
  · exact B1044895
  · exact B1044899
  · exact B1044903
  · exact B1044907
  · exact B1044911
  · exact B1044915
  · exact B1044919
  · exact B1044923
  · exact B1044927
  · exact B1044931
  · exact B1044935
  · exact B1044939
  · exact B1044943
  · exact B1044947
  · exact B1044951
  · exact B1044955
  · exact B1044959
  · exact B1044963
  · exact B1044967
  · exact B1044971
  · exact B1044975
  · exact B1044979
  · exact B1044983
  · exact B1044987
  · exact B1044991
  · exact B1044995
  · exact B1044999
  · exact B1045003
  · exact B1045007
  · exact B1045011
  · exact B1045015
  · exact B1045019
  · exact B1045023
  · exact B1045027
  · exact B1045031
  · exact B1045035
  · exact B1045039
  · exact B1045043
  · exact B1045047
  · exact B1045051
  · exact B1045055
  · exact B1045059
  · exact B1045063
  · exact B1045067
  · exact B1045071
  · exact B1045075
  · exact B1045079
  · exact B1045083
  · exact B1045087
  · exact B1045091
  · exact B1045095
  · exact B1045099
  · exact B1045103
  · exact B1045107
  · exact B1045111
  · exact B1045115
  · exact B1045119
  · exact B1045123
  · exact B1045127
  · exact B1045131
  · exact B1045135
  · exact B1045139
  · exact B1045143
  · exact B1045147
  · exact B1045151
  · exact B1045155
  · exact B1045159
  · exact B1045163
  · exact B1045167
  · exact B1045171
  · exact B1045175
  · exact B1045179
  · exact B1045183
  · exact B1045187
  · exact B1045191
  · exact B1045195
  · exact B1045199
  · exact B1045203
  · exact B1045207
  · exact B1045211
  · exact B1045215
  · exact B1045219
  · exact B1045223
  · exact B1045227
  · exact B1045231
  · exact B1045235
  · exact B1045239
  · exact B1045243
  · exact B1045247
  · exact B1045251
  · exact B1045255
  · exact B1045259
  · exact B1045263
  · exact B1045267
  · exact B1045271
  · exact B1045275
  · exact B1045279
  · exact B1045283
  · exact B1045287
  · exact B1045291
  · exact B1045295
  · exact B1045299
  · exact B1045303
  · exact B1045307
  · exact B1045311
  · exact B1045315
  · exact B1045319
  · exact B1045323
  · exact B1045327
  · exact B1045331
  · exact B1045335
  · exact B1045339
  · exact B1045343
  · exact B1045347
  · exact B1045351
  · exact B1045355
  · exact B1045359
  · exact B1045363
  · exact B1045367
  · exact B1045371
  · exact B1045375
  · exact B1045379
  · exact B1045383
  · exact B1045387
  · exact B1045391
  · exact B1045395
  · exact B1045399
  · exact B1045403
  · exact B1045407
  · exact B1045411
  · exact B1045415
  · exact B1045419
  · exact B1045423
  · exact B1045427
  · exact B1045431
  · exact B1045435
  · exact B1045439
  · exact B1045443
  · exact B1045447
  · exact B1045451
  · exact B1045455
  · exact B1045459
  · exact B1045463
  · exact B1045467
  · exact B1045471
  · exact B1045475
  · exact B1045479
  · exact B1045483
  · exact B1045487
  · exact B1045491
  · exact B1045495
  · exact B1045499
  · exact B1045503
  · exact B1045507
  · exact B1045511
  · exact B1045515
  · exact B1045519
  · exact B1045523
  · exact B1045527
  · exact B1045531
  · exact B1045535
  · exact B1045539
  · exact B1045543
  · exact B1045547
  · exact B1045551
  · exact B1045555
  · exact B1045559
  · exact B1045563
  · exact B1045567
  · exact B1045571
  · exact B1045575
  · exact B1045579
  · exact B1045583
  · exact B1045587
  · exact B1045591
  · exact B1045595
  · exact B1045599
  · exact B1045603
  · exact B1045607
  · exact B1045611
  · exact B1045615
  · exact B1045619
  · exact B1045623
  · exact B1045627
  · exact B1045631
  · exact B1045635
  · exact B1045639
  · exact B1045643
  · exact B1045647
  · exact B1045651
  · exact B1045655
  · exact B1045659
  · exact B1045663
  · exact B1045667
  · exact B1045671
  · exact B1045675
  · exact B1045679
  · exact B1045683
  · exact B1045687
  · exact B1045691
  · exact B1045695
  · exact B1045699
  · exact B1045703
  · exact B1045707
  · exact B1045711
  · exact B1045715
  · exact B1045719
  · exact B1045723
  · exact B1045727
  · exact B1045731
  · exact B1045735
  · exact B1045739
  · exact B1045743
  · exact B1045747
  · exact B1045751
  · exact B1045755
  · exact B1045759
  · exact B1045763
  · exact B1045767
  · exact B1045771
  · exact B1045775
  · exact B1045779
  · exact B1045783
  · exact B1045787
  · exact B1045791
  · exact B1045795
  · exact B1045799
  · exact B1045803
  · exact B1045807
  · exact B1045811
  · exact B1045815
  · exact B1045819
  · exact B1045823
  · exact B1045827
  · exact B1045831
  · exact B1045835
  · exact B1045839
  · exact B1045843
  · exact B1045847
  · exact B1045851
  · exact B1045855
  · exact B1045859
  · exact B1045863
  · exact B1045867
  · exact B1045871
  · exact B1045875
  · exact B1045879
  · exact B1045883
  · exact B1045887
  · exact B1045891
  · exact B1045895
  · exact B1045899
  · exact B1045903
  · exact B1045907
  · exact B1045911
  · exact B1045915
  · exact B1045919
  · exact B1045923
  · exact B1045927
  · exact B1045931
  · exact B1045935
  · exact B1045939
  · exact B1045943
  · exact B1045947
  · exact B1045951
  · exact B1045955
  · exact B1045959
  · exact B1045963
  · exact B1045967
  · exact B1045971
  · exact B1045975
  · exact B1045979
  · exact B1045983
  · exact B1045987
  · exact B1045991
  · exact B1045995
  · exact B1045999
  · exact B1046003
  · exact B1046007
  · exact B1046011
  · exact B1046015
  · exact B1046019
  · exact B1046023
  · exact B1046027
  · exact B1046031
  · exact B1046035
  · exact B1046039
  · exact B1046043
  · exact B1046047
  · exact B1046051
  · exact B1046055
  · exact B1046059
  · exact B1046063
  · exact B1046067
  · exact B1046071
  · exact B1046075
  · exact B1046079
  · exact B1046083
  · exact B1046087
  · exact B1046091
  · exact B1046095
  · exact B1046099
  · exact B1046103
  · exact B1046107
  · exact B1046111
  · exact B1046115
  · exact B1046119
  · exact B1046123
  · exact B1046127
  · exact B1046131
  · exact B1046135
  · exact B1046139
  · exact B1046143
  · exact B1046147
  · exact B1046151
  · exact B1046155
  · exact B1046159
  · exact B1046163
  · exact B1046167
  · exact B1046171
  · exact B1046175
  · exact B1046179
  · exact B1046183
  · exact B1046187
  · exact B1046191
  · exact B1046195
  · exact B1046199
  · exact B1046203
  · exact B1046207
  · exact B1046211
  · exact B1046215
  · exact B1046219
  · exact B1046223
  · exact B1046227
  · exact B1046231
  · exact B1046235
  · exact B1046239
  · exact B1046243
  · exact B1046247
  · exact B1046251
  · exact B1046255
  · exact B1046259
  · exact B1046263
  · exact B1046267
  · exact B1046271
  · exact B1046275
  · exact B1046279
  · exact B1046283
  · exact B1046287
  · exact B1046291
  · exact B1046295
  · exact B1046299
  · exact B1046303
  · exact B1046307
  · exact B1046311
  · exact B1046315
  · exact B1046319
  · exact B1046323
  · exact B1046327
  · exact B1046331
  · exact B1046335
  · exact B1046339
  · exact B1046343
  · exact B1046347
  · exact B1046351
  · exact B1046355
  · exact B1046359
  · exact B1046363
  · exact B1046367
  · exact B1046371
  · exact B1046375
  · exact B1046379
  · exact B1046383
  · exact B1046387
  · exact B1046391
  · exact B1046395
  · exact B1046399
  · exact B1046403
  · exact B1046407
  · exact B1046411
  · exact B1046415
  · exact B1046419
  · exact B1046423
  · exact B1046427
  · exact B1046431
  · exact B1046435
  · exact B1046439
  · exact B1046443
  · exact B1046447
  · exact B1046451
  · exact B1046455
  · exact B1046459
  · exact B1046463
  · exact B1046467
  · exact B1046471
  · exact B1046475
  · exact B1046479
  · exact B1046483
  · exact B1046487
  · exact B1046491
  · exact B1046495
  · exact B1046499
  · exact B1046503
  · exact B1046507
  · exact B1046511
  · exact B1046515
  · exact B1046519
  · exact B1046523
  · exact B1046527
  · exact B1046531
  · exact B1046535
  · exact B1046539
  · exact B1046543
  · exact B1046547
  · exact B1046551
  · exact B1046555
  · exact B1046559
  · exact B1046563
  · exact B1046567
  · exact B1046571
  · exact B1046575
  · exact B1046579
  · exact B1046583
  · exact B1046587
  · exact B1046591
  · exact B1046595
  · exact B1046599
  · exact B1046603
  · exact B1046607
  · exact B1046611
  · exact B1046615
  · exact B1046619
  · exact B1046623
  · exact B1046627
  · exact B1046631
  · exact B1046635
  · exact B1046639
  · exact B1046643
  · exact B1046647
  · exact B1046651
  · exact B1046655
  · exact B1046659
  · exact B1046663
  · exact B1046667
  · exact B1046671
  · exact B1046675
  · exact B1046679
  · exact B1046683
  · exact B1046687
  · exact B1046691
  · exact B1046695
  · exact B1046699
  · exact B1046703
  · exact B1046707
  · exact B1046711
  · exact B1046715
  · exact B1046719
  · exact B1046723
  · exact B1046727
  · exact B1046731
  · exact B1046735
  · exact B1046739
  · exact B1046743
  · exact B1046747
  · exact B1046751
  · exact B1046755
  · exact B1046759
  · exact B1046763
  · exact B1046767
  · exact B1046771
  · exact B1046775
  · exact B1046779
  · exact B1046783
  · exact B1046787
  · exact B1046791
  · exact B1046795
  · exact B1046799
  · exact B1046803
  · exact B1046807
  · exact B1046811
  · exact B1046815
  · exact B1046819
  · exact B1046823
  · exact B1046827
  · exact B1046831
  · exact B1046835
  · exact B1046839
  · exact B1046843
  · exact B1046847
  · exact B1046851
  · exact B1046855
  · exact B1046859
  · exact B1046863
  · exact B1046867
  · exact B1046871
  · exact B1046875
  · exact B1046879
  · exact B1046883
  · exact B1046887
  · exact B1046891
  · exact B1046895
  · exact B1046899
  · exact B1046903
  · exact B1046907
  · exact B1046911
  · exact B1046915
  · exact B1046919
  · exact B1046923
  · exact B1046927
  · exact B1046931
  · exact B1046935
  · exact B1046939
  · exact B1046943
  · exact B1046947
  · exact B1046951
  · exact B1046955
  · exact B1046959
  · exact B1046963
  · exact B1046967
  · exact B1046971
  · exact B1046975
  · exact B1046979
  · exact B1046983
  · exact B1046987
  · exact B1046991
  · exact B1046995
  · exact B1046999
  · exact B1047003
  · exact B1047007
  · exact B1047011
  · exact B1047015
  · exact B1047019
  · exact B1047023
  · exact B1047027
  · exact B1047031
  · exact B1047035
  · exact B1047039
  · exact B1047043
  · exact B1047047
  · exact B1047051
  · exact B1047055
  · exact B1047059
  · exact B1047063
  · exact B1047067
  · exact B1047071
  · exact B1047075
  · exact B1047079
  · exact B1047083
  · exact B1047087
  · exact B1047091
  · exact B1047095
  · exact B1047099
  · exact B1047103
  · exact B1047107
  · exact B1047111
  · exact B1047115
  · exact B1047119
  · exact B1047123
  · exact B1047127
  · exact B1047131
  · exact B1047135
  · exact B1047139
  · exact B1047143
  · exact B1047147
  · exact B1047151
  · exact B1047155
  · exact B1047159
  · exact B1047163
  · exact B1047167
  · exact B1047171
  · exact B1047175
  · exact B1047179
  · exact B1047183
  · exact B1047187
  · exact B1047191
  · exact B1047195
  · exact B1047199
  · exact B1047203
  · exact B1047207
  · exact B1047211
  · exact B1047215
  · exact B1047219
  · exact B1047223
  · exact B1047227
  · exact B1047231
  · exact B1047235
  · exact B1047239
  · exact B1047243
  · exact B1047247
  · exact B1047251
  · exact B1047255
  · exact B1047259
  · exact B1047263
  · exact B1047267
  · exact B1047271
  · exact B1047275
  · exact B1047279
  · exact B1047283
  · exact B1047287
  · exact B1047291
  · exact B1047295
  · exact B1047299
  · exact B1047303
  · exact B1047307
  · exact B1047311
  · exact B1047315
  · exact B1047319
  · exact B1047323
  · exact B1047327
  · exact B1047331
  · exact B1047335
  · exact B1047339
  · exact B1047343
  · exact B1047347
  · exact B1047351
  · exact B1047355
  · exact B1047359
  · exact B1047363
  · exact B1047367
  · exact B1047371
  · exact B1047375
  · exact B1047379
  · exact B1047383
  · exact B1047387
  · exact B1047391
  · exact B1047395
  · exact B1047399
  · exact B1047403
  · exact B1047407

theorem C1 (j : ℕ) (h1 : 261852 ≤ j) (h2 : j ≤ 262151) : Blo 1044610 (4 * j + 3) := by
  interval_cases j
  · exact B1047411
  · exact B1047415
  · exact B1047419
  · exact B1047423
  · exact B1047427
  · exact B1047431
  · exact B1047435
  · exact B1047439
  · exact B1047443
  · exact B1047447
  · exact B1047451
  · exact B1047455
  · exact B1047459
  · exact B1047463
  · exact B1047467
  · exact B1047471
  · exact B1047475
  · exact B1047479
  · exact B1047483
  · exact B1047487
  · exact B1047491
  · exact B1047495
  · exact B1047499
  · exact B1047503
  · exact B1047507
  · exact B1047511
  · exact B1047515
  · exact B1047519
  · exact B1047523
  · exact B1047527
  · exact B1047531
  · exact B1047535
  · exact B1047539
  · exact B1047543
  · exact B1047547
  · exact B1047551
  · exact B1047555
  · exact B1047559
  · exact B1047563
  · exact B1047567
  · exact B1047571
  · exact B1047575
  · exact B1047579
  · exact B1047583
  · exact B1047587
  · exact B1047591
  · exact B1047595
  · exact B1047599
  · exact B1047603
  · exact B1047607
  · exact B1047611
  · exact B1047615
  · exact B1047619
  · exact B1047623
  · exact B1047627
  · exact B1047631
  · exact B1047635
  · exact B1047639
  · exact B1047643
  · exact B1047647
  · exact B1047651
  · exact B1047655
  · exact B1047659
  · exact B1047663
  · exact B1047667
  · exact B1047671
  · exact B1047675
  · exact B1047679
  · exact B1047683
  · exact B1047687
  · exact B1047691
  · exact B1047695
  · exact B1047699
  · exact B1047703
  · exact B1047707
  · exact B1047711
  · exact B1047715
  · exact B1047719
  · exact B1047723
  · exact B1047727
  · exact B1047731
  · exact B1047735
  · exact B1047739
  · exact B1047743
  · exact B1047747
  · exact B1047751
  · exact B1047755
  · exact B1047759
  · exact B1047763
  · exact B1047767
  · exact B1047771
  · exact B1047775
  · exact B1047779
  · exact B1047783
  · exact B1047787
  · exact B1047791
  · exact B1047795
  · exact B1047799
  · exact B1047803
  · exact B1047807
  · exact B1047811
  · exact B1047815
  · exact B1047819
  · exact B1047823
  · exact B1047827
  · exact B1047831
  · exact B1047835
  · exact B1047839
  · exact B1047843
  · exact B1047847
  · exact B1047851
  · exact B1047855
  · exact B1047859
  · exact B1047863
  · exact B1047867
  · exact B1047871
  · exact B1047875
  · exact B1047879
  · exact B1047883
  · exact B1047887
  · exact B1047891
  · exact B1047895
  · exact B1047899
  · exact B1047903
  · exact B1047907
  · exact B1047911
  · exact B1047915
  · exact B1047919
  · exact B1047923
  · exact B1047927
  · exact B1047931
  · exact B1047935
  · exact B1047939
  · exact B1047943
  · exact B1047947
  · exact B1047951
  · exact B1047955
  · exact B1047959
  · exact B1047963
  · exact B1047967
  · exact B1047971
  · exact B1047975
  · exact B1047979
  · exact B1047983
  · exact B1047987
  · exact B1047991
  · exact B1047995
  · exact B1047999
  · exact B1048003
  · exact B1048007
  · exact B1048011
  · exact B1048015
  · exact B1048019
  · exact B1048023
  · exact B1048027
  · exact B1048031
  · exact B1048035
  · exact B1048039
  · exact B1048043
  · exact B1048047
  · exact B1048051
  · exact B1048055
  · exact B1048059
  · exact B1048063
  · exact B1048067
  · exact B1048071
  · exact B1048075
  · exact B1048079
  · exact B1048083
  · exact B1048087
  · exact B1048091
  · exact B1048095
  · exact B1048099
  · exact B1048103
  · exact B1048107
  · exact B1048111
  · exact B1048115
  · exact B1048119
  · exact B1048123
  · exact B1048127
  · exact B1048131
  · exact B1048135
  · exact B1048139
  · exact B1048143
  · exact B1048147
  · exact B1048151
  · exact B1048155
  · exact B1048159
  · exact B1048163
  · exact B1048167
  · exact B1048171
  · exact B1048175
  · exact B1048179
  · exact B1048183
  · exact B1048187
  · exact B1048191
  · exact B1048195
  · exact B1048199
  · exact B1048203
  · exact B1048207
  · exact B1048211
  · exact B1048215
  · exact B1048219
  · exact B1048223
  · exact B1048227
  · exact B1048231
  · exact B1048235
  · exact B1048239
  · exact B1048243
  · exact B1048247
  · exact B1048251
  · exact B1048255
  · exact B1048259
  · exact B1048263
  · exact B1048267
  · exact B1048271
  · exact B1048275
  · exact B1048279
  · exact B1048283
  · exact B1048287
  · exact B1048291
  · exact B1048295
  · exact B1048299
  · exact B1048303
  · exact B1048307
  · exact B1048311
  · exact B1048315
  · exact B1048319
  · exact B1048323
  · exact B1048327
  · exact B1048331
  · exact B1048335
  · exact B1048339
  · exact B1048343
  · exact B1048347
  · exact B1048351
  · exact B1048355
  · exact B1048359
  · exact B1048363
  · exact B1048367
  · exact B1048371
  · exact B1048375
  · exact B1048379
  · exact B1048383
  · exact B1048387
  · exact B1048391
  · exact B1048395
  · exact B1048399
  · exact B1048403
  · exact B1048407
  · exact B1048411
  · exact B1048415
  · exact B1048419
  · exact B1048423
  · exact B1048427
  · exact B1048431
  · exact B1048435
  · exact B1048439
  · exact B1048443
  · exact B1048447
  · exact B1048451
  · exact B1048455
  · exact B1048459
  · exact B1048463
  · exact B1048467
  · exact B1048471
  · exact B1048475
  · exact B1048479
  · exact B1048483
  · exact B1048487
  · exact B1048491
  · exact B1048495
  · exact B1048499
  · exact B1048503
  · exact B1048507
  · exact B1048511
  · exact B1048515
  · exact B1048519
  · exact B1048523
  · exact B1048527
  · exact B1048531
  · exact B1048535
  · exact B1048539
  · exact B1048543
  · exact B1048547
  · exact B1048551
  · exact B1048555
  · exact B1048559
  · exact B1048563
  · exact B1048567
  · exact B1048571
  · exact B1048575
  · exact B1048579
  · exact B1048583
  · exact B1048587
  · exact B1048591
  · exact B1048595
  · exact B1048599
  · exact B1048603
  · exact B1048607

theorem solution (m : ℕ) (hlo : 1044610 ≤ m) (hhi : m ≤ 1048610) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 261152 ≤ j := by omega
    have hj2 : j ≤ 262151 := by omega
    have hb : Blo 1044610 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 261852 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
