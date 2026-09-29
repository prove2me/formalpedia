-- Prove2me | solution 1 for syracuse_descends_range_818347_822347
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:44.803035+00:00
-- url     : https://prove2.me/submissions/2e3dfc58-7527-4afd-8da6-374597b41313

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


theorem B9469973 : Blo 818347 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B1474957 : Blo 818347 1474957 := bbase (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) (by norm_num)
theorem B3506581 : Blo 818347 3506581 := bbase (se 6 (by rfl) ⟨82185, by rfl⟩ : syracuseStep 3506581 = 164371) (by norm_num)
theorem B4161941 : Blo 818347 4161941 := bbase (se 6 (by rfl) ⟨97545, by rfl⟩ : syracuseStep 4161941 = 195091) (by norm_num)
theorem B983497 : Blo 818347 983497 := bbase (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) (by norm_num)
theorem B1475029 : Blo 818347 1475029 := bbase (se 7 (by rfl) ⟨17285, by rfl⟩ : syracuseStep 1475029 = 34571) (by norm_num)
theorem B1311221 : Blo 818347 1311221 := bbase (se 5 (by rfl) ⟨61463, by rfl⟩ : syracuseStep 1311221 = 122927) (by norm_num)
theorem B983593 : Blo 818347 983593 := bbase (se 2 (by rfl) ⟨368847, by rfl⟩ : syracuseStep 983593 = 737695) (by norm_num)
theorem B820129 : Blo 818347 820129 := bbase (se 2 (by rfl) ⟨307548, by rfl⟩ : syracuseStep 820129 = 615097) (by norm_num)
theorem B3113909 : Blo 818347 3113909 := bbase (se 5 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 3113909 = 291929) (by norm_num)
theorem B1311893 : Blo 818347 1311893 := bbase (se 6 (by rfl) ⟨30747, by rfl⟩ : syracuseStep 1311893 = 61495) (by norm_num)
theorem B3114197 : Blo 818347 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B2622709 : Blo 818347 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B2491813 : Blo 818347 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B3737029 : Blo 818347 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B1476053 : Blo 818347 1476053 := bbase (se 7 (by rfl) ⟨17297, by rfl⟩ : syracuseStep 1476053 = 34595) (by norm_num)
theorem B13469141 : Blo 818347 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B1246709 : Blo 818347 1246709 := bbase (se 5 (by rfl) ⟨58439, by rfl⟩ : syracuseStep 1246709 = 116879) (by norm_num)
theorem B3737173 : Blo 818347 3737173 := bbase (se 8 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 3737173 = 43795) (by norm_num)
theorem B1312405 : Blo 818347 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2000533 : Blo 818347 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B984737 : Blo 818347 984737 := bbase (se 2 (by rfl) ⟨369276, by rfl⟩ : syracuseStep 984737 = 738553) (by norm_num)
theorem B3508069 : Blo 818347 3508069 := bbase (se 4 (by rfl) ⟨328881, by rfl⟩ : syracuseStep 3508069 = 657763) (by norm_num)
theorem B3508085 : Blo 818347 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B985069 : Blo 818347 985069 := bbase (se 3 (by rfl) ⟨184700, by rfl⟩ : syracuseStep 985069 = 369401) (by norm_num)
theorem B3934277 : Blo 818347 3934277 := bbase (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) (by norm_num)
theorem B1312861 : Blo 818347 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B1968293 : Blo 818347 1968293 := bbase (se 4 (by rfl) ⟨184527, by rfl⟩ : syracuseStep 1968293 = 369055) (by norm_num)
theorem B3115381 : Blo 818347 3115381 := bbase (se 5 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 3115381 = 292067) (by norm_num)
theorem B2623877 : Blo 818347 2623877 := bbase (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) (by norm_num)
theorem B7473653 : Blo 818347 7473653 := bbase (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) (by norm_num)
theorem B1968677 : Blo 818347 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B985765 : Blo 818347 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B3115685 : Blo 818347 3115685 := bbase (se 4 (by rfl) ⟨292095, by rfl⟩ : syracuseStep 3115685 = 584191) (by norm_num)
theorem B985813 : Blo 818347 985813 := bbase (se 7 (by rfl) ⟨11552, by rfl⟩ : syracuseStep 985813 = 23105) (by norm_num)
theorem B1968877 : Blo 818347 1968877 := bbase (se 3 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 1968877 = 738329) (by norm_num)
theorem B1313533 : Blo 818347 1313533 := bbase (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) (by norm_num)
theorem B2362229 : Blo 818347 2362229 := bbase (se 5 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 2362229 = 221459) (by norm_num)
theorem B1870757 : Blo 818347 1870757 := bbase (se 4 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 1870757 = 350767) (by norm_num)
theorem B7015349 : Blo 818347 7015349 := bbase (se 5 (by rfl) ⟨328844, by rfl⟩ : syracuseStep 7015349 = 657689) (by norm_num)
theorem B920641 : Blo 818347 920641 := bbase (se 2 (by rfl) ⟨345240, by rfl⟩ : syracuseStep 920641 = 690481) (by norm_num)
theorem B920677 : Blo 818347 920677 := bbase (se 4 (by rfl) ⟨86313, by rfl⟩ : syracuseStep 920677 = 172627) (by norm_num)
theorem B920713 : Blo 818347 920713 := bbase (se 2 (by rfl) ⟨345267, by rfl⟩ : syracuseStep 920713 = 690535) (by norm_num)
theorem B1313957 : Blo 818347 1313957 := bbase (se 4 (by rfl) ⟨123183, by rfl⟩ : syracuseStep 1313957 = 246367) (by norm_num)
theorem B920749 : Blo 818347 920749 := bbase (se 3 (by rfl) ⟨172640, by rfl⟩ : syracuseStep 920749 = 345281) (by norm_num)
theorem B1051849 : Blo 818347 1051849 := bbase (se 2 (by rfl) ⟨394443, by rfl⟩ : syracuseStep 1051849 = 788887) (by norm_num)
theorem B920785 : Blo 818347 920785 := bbase (se 2 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 920785 = 690589) (by norm_num)
theorem B920821 : Blo 818347 920821 := bbase (se 5 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 920821 = 86327) (by norm_num)
theorem B920857 : Blo 818347 920857 := bbase (se 2 (by rfl) ⟨345321, by rfl⟩ : syracuseStep 920857 = 690643) (by norm_num)
theorem B920893 : Blo 818347 920893 := bbase (se 3 (by rfl) ⟨172667, by rfl⟩ : syracuseStep 920893 = 345335) (by norm_num)
theorem B920929 : Blo 818347 920929 := bbase (se 2 (by rfl) ⟨345348, by rfl⟩ : syracuseStep 920929 = 690697) (by norm_num)
theorem B920965 : Blo 818347 920965 := bbase (se 4 (by rfl) ⟨86340, by rfl⟩ : syracuseStep 920965 = 172681) (by norm_num)
theorem B921001 : Blo 818347 921001 := bbase (se 2 (by rfl) ⟨345375, by rfl⟩ : syracuseStep 921001 = 690751) (by norm_num)
theorem B1314245 : Blo 818347 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B921037 : Blo 818347 921037 := bbase (se 3 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 921037 = 345389) (by norm_num)
theorem B921073 : Blo 818347 921073 := bbase (se 2 (by rfl) ⟨345402, by rfl⟩ : syracuseStep 921073 = 690805) (by norm_num)
theorem B921109 : Blo 818347 921109 := bbase (se 6 (by rfl) ⟨21588, by rfl⟩ : syracuseStep 921109 = 43177) (by norm_num)
theorem B2428453 : Blo 818347 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1183285 : Blo 818347 1183285 := bbase (se 5 (by rfl) ⟨55466, by rfl⟩ : syracuseStep 1183285 = 110933) (by norm_num)
theorem B921145 : Blo 818347 921145 := bbase (se 2 (by rfl) ⟨345429, by rfl⟩ : syracuseStep 921145 = 690859) (by norm_num)
theorem B921181 : Blo 818347 921181 := bbase (se 3 (by rfl) ⟨172721, by rfl⟩ : syracuseStep 921181 = 345443) (by norm_num)
theorem B921217 : Blo 818347 921217 := bbase (se 2 (by rfl) ⟨345456, by rfl⟩ : syracuseStep 921217 = 690913) (by norm_num)
theorem B921253 : Blo 818347 921253 := bbase (se 4 (by rfl) ⟨86367, by rfl⟩ : syracuseStep 921253 = 172735) (by norm_num)
theorem B921289 : Blo 818347 921289 := bbase (se 2 (by rfl) ⟨345483, by rfl⟩ : syracuseStep 921289 = 690967) (by norm_num)
theorem B921325 : Blo 818347 921325 := bbase (se 3 (by rfl) ⟨172748, by rfl⟩ : syracuseStep 921325 = 345497) (by norm_num)
theorem B986861 : Blo 818347 986861 := bbase (se 3 (by rfl) ⟨185036, by rfl⟩ : syracuseStep 986861 = 370073) (by norm_num)
theorem B921361 : Blo 818347 921361 := bbase (se 2 (by rfl) ⟨345510, by rfl⟩ : syracuseStep 921361 = 691021) (by norm_num)
theorem B921397 : Blo 818347 921397 := bbase (se 5 (by rfl) ⟨43190, by rfl⟩ : syracuseStep 921397 = 86381) (by norm_num)
theorem B1183573 : Blo 818347 1183573 := bbase (se 9 (by rfl) ⟨3467, by rfl⟩ : syracuseStep 1183573 = 6935) (by norm_num)
theorem B17764181 : Blo 818347 17764181 := bbase (se 9 (by rfl) ⟨52043, by rfl⟩ : syracuseStep 17764181 = 104087) (by norm_num)
theorem B921433 : Blo 818347 921433 := bbase (se 2 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 921433 = 691075) (by norm_num)
theorem B6655861 : Blo 818347 6655861 := bbase (se 5 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 6655861 = 623987) (by norm_num)
theorem B921469 : Blo 818347 921469 := bbase (se 3 (by rfl) ⟨172775, by rfl⟩ : syracuseStep 921469 = 345551) (by norm_num)
theorem B921505 : Blo 818347 921505 := bbase (se 2 (by rfl) ⟨345564, by rfl⟩ : syracuseStep 921505 = 691129) (by norm_num)
theorem B921541 : Blo 818347 921541 := bbase (se 4 (by rfl) ⟨86394, by rfl⟩ : syracuseStep 921541 = 172789) (by norm_num)
theorem B921577 : Blo 818347 921577 := bbase (se 2 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 921577 = 691183) (by norm_num)
theorem B2101229 : Blo 818347 2101229 := bbase (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) (by norm_num)
theorem B921613 : Blo 818347 921613 := bbase (se 3 (by rfl) ⟨172802, by rfl⟩ : syracuseStep 921613 = 345605) (by norm_num)
theorem B987169 : Blo 818347 987169 := bbase (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) (by norm_num)
theorem B3936293 : Blo 818347 3936293 := bbase (se 4 (by rfl) ⟨369027, by rfl⟩ : syracuseStep 3936293 = 738055) (by norm_num)
theorem B921649 : Blo 818347 921649 := bbase (se 2 (by rfl) ⟨345618, by rfl⟩ : syracuseStep 921649 = 691237) (by norm_num)
theorem B3510341 : Blo 818347 3510341 := bbase (se 4 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 3510341 = 658189) (by norm_num)
theorem B921685 : Blo 818347 921685 := bbase (se 8 (by rfl) ⟨5400, by rfl⟩ : syracuseStep 921685 = 10801) (by norm_num)
theorem B921721 : Blo 818347 921721 := bbase (se 2 (by rfl) ⟨345645, by rfl⟩ : syracuseStep 921721 = 691291) (by norm_num)
theorem B888953 : Blo 818347 888953 := bbase (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) (by norm_num)
theorem B921757 : Blo 818347 921757 := bbase (se 3 (by rfl) ⟨172829, by rfl⟩ : syracuseStep 921757 = 345659) (by norm_num)
theorem B921793 : Blo 818347 921793 := bbase (se 2 (by rfl) ⟨345672, by rfl⟩ : syracuseStep 921793 = 691345) (by norm_num)
theorem B2625733 : Blo 818347 2625733 := bbase (se 4 (by rfl) ⟨246162, by rfl⟩ : syracuseStep 2625733 = 492325) (by norm_num)
theorem B987337 : Blo 818347 987337 := bbase (se 2 (by rfl) ⟨370251, by rfl⟩ : syracuseStep 987337 = 740503) (by norm_num)
theorem B921829 : Blo 818347 921829 := bbase (se 4 (by rfl) ⟨86421, by rfl⟩ : syracuseStep 921829 = 172843) (by norm_num)
theorem B1315045 : Blo 818347 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B921865 : Blo 818347 921865 := bbase (se 2 (by rfl) ⟨345699, by rfl⟩ : syracuseStep 921865 = 691399) (by norm_num)
theorem B1970453 : Blo 818347 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B921901 : Blo 818347 921901 := bbase (se 3 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 921901 = 345713) (by norm_num)
theorem B1478965 : Blo 818347 1478965 := bbase (se 5 (by rfl) ⟨69326, by rfl⟩ : syracuseStep 1478965 = 138653) (by norm_num)
theorem B2101565 : Blo 818347 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B921937 : Blo 818347 921937 := bbase (se 2 (by rfl) ⟨345726, by rfl⟩ : syracuseStep 921937 = 691453) (by norm_num)
theorem B1053037 : Blo 818347 1053037 := bbase (se 3 (by rfl) ⟨197444, by rfl⟩ : syracuseStep 1053037 = 394889) (by norm_num)
theorem B921973 : Blo 818347 921973 := bbase (se 5 (by rfl) ⟨43217, by rfl⟩ : syracuseStep 921973 = 86435) (by norm_num)
theorem B3379589 : Blo 818347 3379589 := bbase (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) (by norm_num)
theorem B987533 : Blo 818347 987533 := bbase (se 3 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 987533 = 370325) (by norm_num)
theorem B922009 : Blo 818347 922009 := bbase (se 2 (by rfl) ⟨345753, by rfl⟩ : syracuseStep 922009 = 691507) (by norm_num)
theorem B922045 : Blo 818347 922045 := bbase (se 3 (by rfl) ⟨172883, by rfl⟩ : syracuseStep 922045 = 345767) (by norm_num)
theorem B922081 : Blo 818347 922081 := bbase (se 2 (by rfl) ⟨345780, by rfl⟩ : syracuseStep 922081 = 691561) (by norm_num)
theorem B922117 : Blo 818347 922117 := bbase (se 4 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 922117 = 172897) (by norm_num)
theorem B922153 : Blo 818347 922153 := bbase (se 2 (by rfl) ⟨345807, by rfl⟩ : syracuseStep 922153 = 691615) (by norm_num)
theorem B922189 : Blo 818347 922189 := bbase (se 3 (by rfl) ⟨172910, by rfl⟩ : syracuseStep 922189 = 345821) (by norm_num)
theorem B1053281 : Blo 818347 1053281 := bbase (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) (by norm_num)
theorem B922225 : Blo 818347 922225 := bbase (se 2 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 922225 = 691669) (by norm_num)
theorem B1380989 : Blo 818347 1380989 := bbase (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) (by norm_num)
theorem B922261 : Blo 818347 922261 := bbase (se 6 (by rfl) ⟨21615, by rfl⟩ : syracuseStep 922261 = 43231) (by norm_num)
theorem B922297 : Blo 818347 922297 := bbase (se 2 (by rfl) ⟨345861, by rfl⟩ : syracuseStep 922297 = 691723) (by norm_num)
theorem B922333 : Blo 818347 922333 := bbase (se 3 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 922333 = 345875) (by norm_num)
theorem B3117797 : Blo 818347 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1381117 : Blo 818347 1381117 := bbase (se 3 (by rfl) ⟨258959, by rfl⟩ : syracuseStep 1381117 = 517919) (by norm_num)
theorem B922369 : Blo 818347 922369 := bbase (se 2 (by rfl) ⟨345888, by rfl⟩ : syracuseStep 922369 = 691777) (by norm_num)
theorem B1315597 : Blo 818347 1315597 := bbase (se 3 (by rfl) ⟨246674, by rfl⟩ : syracuseStep 1315597 = 493349) (by norm_num)
theorem B3937045 : Blo 818347 3937045 := bbase (se 6 (by rfl) ⟨92274, by rfl⟩ : syracuseStep 3937045 = 184549) (by norm_num)
theorem B922405 : Blo 818347 922405 := bbase (se 4 (by rfl) ⟨86475, by rfl⟩ : syracuseStep 922405 = 172951) (by norm_num)
theorem B922441 : Blo 818347 922441 := bbase (se 2 (by rfl) ⟨345915, by rfl⟩ : syracuseStep 922441 = 691831) (by norm_num)
theorem B1381205 : Blo 818347 1381205 := bbase (se 9 (by rfl) ⟨4046, by rfl⟩ : syracuseStep 1381205 = 8093) (by norm_num)
theorem B922477 : Blo 818347 922477 := bbase (se 3 (by rfl) ⟨172964, by rfl⟩ : syracuseStep 922477 = 345929) (by norm_num)
theorem B922513 : Blo 818347 922513 := bbase (se 2 (by rfl) ⟨345942, by rfl⟩ : syracuseStep 922513 = 691885) (by norm_num)
theorem B922549 : Blo 818347 922549 := bbase (se 5 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 922549 = 86489) (by norm_num)
theorem B1872821 : Blo 818347 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B1381333 : Blo 818347 1381333 := bbase (se 7 (by rfl) ⟨16187, by rfl⟩ : syracuseStep 1381333 = 32375) (by norm_num)
theorem B2331605 : Blo 818347 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B922585 : Blo 818347 922585 := bbase (se 2 (by rfl) ⟨345969, by rfl⟩ : syracuseStep 922585 = 691939) (by norm_num)
theorem B922621 : Blo 818347 922621 := bbase (se 3 (by rfl) ⟨172991, by rfl⟩ : syracuseStep 922621 = 345983) (by norm_num)
theorem B3118085 : Blo 818347 3118085 := bbase (se 4 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 3118085 = 584641) (by norm_num)
theorem B1315853 : Blo 818347 1315853 := bbase (se 3 (by rfl) ⟨246722, by rfl⟩ : syracuseStep 1315853 = 493445) (by norm_num)
theorem B922657 : Blo 818347 922657 := bbase (se 2 (by rfl) ⟨345996, by rfl⟩ : syracuseStep 922657 = 691993) (by norm_num)
theorem B1381421 : Blo 818347 1381421 := bbase (se 3 (by rfl) ⟨259016, by rfl⟩ : syracuseStep 1381421 = 518033) (by norm_num)
theorem B922693 : Blo 818347 922693 := bbase (se 4 (by rfl) ⟨86502, by rfl⟩ : syracuseStep 922693 = 173005) (by norm_num)
theorem B8983637 : Blo 818347 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B922729 : Blo 818347 922729 := bbase (se 2 (by rfl) ⟨346023, by rfl⟩ : syracuseStep 922729 = 692047) (by norm_num)
theorem B922765 : Blo 818347 922765 := bbase (se 3 (by rfl) ⟨173018, by rfl⟩ : syracuseStep 922765 = 346037) (by norm_num)
theorem B1381549 : Blo 818347 1381549 := bbase (se 3 (by rfl) ⟨259040, by rfl⟩ : syracuseStep 1381549 = 518081) (by norm_num)
theorem B922801 : Blo 818347 922801 := bbase (se 2 (by rfl) ⟨346050, by rfl⟩ : syracuseStep 922801 = 692101) (by norm_num)
theorem B922837 : Blo 818347 922837 := bbase (se 7 (by rfl) ⟨10814, by rfl⟩ : syracuseStep 922837 = 21629) (by norm_num)
theorem B922873 : Blo 818347 922873 := bbase (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) (by norm_num)
theorem B1381637 : Blo 818347 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B922909 : Blo 818347 922909 := bbase (se 3 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 922909 = 346091) (by norm_num)
theorem B922945 : Blo 818347 922945 := bbase (se 2 (by rfl) ⟨346104, by rfl⟩ : syracuseStep 922945 = 692209) (by norm_num)
theorem B922981 : Blo 818347 922981 := bbase (se 4 (by rfl) ⟨86529, by rfl⟩ : syracuseStep 922981 = 173059) (by norm_num)
theorem B1381765 : Blo 818347 1381765 := bbase (se 4 (by rfl) ⟨129540, by rfl⟩ : syracuseStep 1381765 = 259081) (by norm_num)
theorem B923017 : Blo 818347 923017 := bbase (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) (by norm_num)
theorem B923053 : Blo 818347 923053 := bbase (se 3 (by rfl) ⟨173072, by rfl⟩ : syracuseStep 923053 = 346145) (by norm_num)
theorem B923089 : Blo 818347 923089 := bbase (se 2 (by rfl) ⟨346158, by rfl⟩ : syracuseStep 923089 = 692317) (by norm_num)
theorem B1381853 : Blo 818347 1381853 := bbase (se 3 (by rfl) ⟨259097, by rfl⟩ : syracuseStep 1381853 = 518195) (by norm_num)
theorem B923125 : Blo 818347 923125 := bbase (se 5 (by rfl) ⟨43271, by rfl⟩ : syracuseStep 923125 = 86543) (by norm_num)
theorem B1054201 : Blo 818347 1054201 := bbase (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) (by norm_num)
theorem B2627093 : Blo 818347 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B923161 : Blo 818347 923161 := bbase (se 2 (by rfl) ⟨346185, by rfl⟩ : syracuseStep 923161 = 692371) (by norm_num)
theorem B923197 : Blo 818347 923197 := bbase (se 3 (by rfl) ⟨173099, by rfl⟩ : syracuseStep 923197 = 346199) (by norm_num)
theorem B1381981 : Blo 818347 1381981 := bbase (se 3 (by rfl) ⟨259121, by rfl⟩ : syracuseStep 1381981 = 518243) (by norm_num)
theorem B923233 : Blo 818347 923233 := bbase (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) (by norm_num)
theorem B2332277 : Blo 818347 2332277 := bbase (se 5 (by rfl) ⟨109325, by rfl⟩ : syracuseStep 2332277 = 218651) (by norm_num)
theorem B923269 : Blo 818347 923269 := bbase (se 4 (by rfl) ⟨86556, by rfl⟩ : syracuseStep 923269 = 173113) (by norm_num)
theorem B1971877 : Blo 818347 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B923305 : Blo 818347 923305 := bbase (se 2 (by rfl) ⟨346239, by rfl⟩ : syracuseStep 923305 = 692479) (by norm_num)
theorem B1382069 : Blo 818347 1382069 := bbase (se 5 (by rfl) ⟨64784, by rfl⟩ : syracuseStep 1382069 = 129569) (by norm_num)
theorem B923341 : Blo 818347 923341 := bbase (se 3 (by rfl) ⟨173126, by rfl⟩ : syracuseStep 923341 = 346253) (by norm_num)
theorem B1316557 : Blo 818347 1316557 := bbase (se 3 (by rfl) ⟨246854, by rfl⟩ : syracuseStep 1316557 = 493709) (by norm_num)
theorem B923377 : Blo 818347 923377 := bbase (se 2 (by rfl) ⟨346266, by rfl⟩ : syracuseStep 923377 = 692533) (by norm_num)
theorem B923413 : Blo 818347 923413 := bbase (se 6 (by rfl) ⟨21642, by rfl⟩ : syracuseStep 923413 = 43285) (by norm_num)
theorem B1480493 : Blo 818347 1480493 := bbase (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) (by norm_num)
theorem B1382197 : Blo 818347 1382197 := bbase (se 5 (by rfl) ⟨64790, by rfl⟩ : syracuseStep 1382197 = 129581) (by norm_num)
theorem B923449 : Blo 818347 923449 := bbase (se 2 (by rfl) ⟨346293, by rfl⟩ : syracuseStep 923449 = 692587) (by norm_num)
theorem B7018325 : Blo 818347 7018325 := bbase (se 9 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 7018325 = 41123) (by norm_num)
theorem B923485 : Blo 818347 923485 := bbase (se 3 (by rfl) ⟨173153, by rfl⟩ : syracuseStep 923485 = 346307) (by norm_num)
theorem B1480565 : Blo 818347 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B923521 : Blo 818347 923521 := bbase (se 2 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 923521 = 692641) (by norm_num)
theorem B1382285 : Blo 818347 1382285 := bbase (se 3 (by rfl) ⟨259178, by rfl⟩ : syracuseStep 1382285 = 518357) (by norm_num)
theorem B923557 : Blo 818347 923557 := bbase (se 4 (by rfl) ⟨86583, by rfl⟩ : syracuseStep 923557 = 173167) (by norm_num)
theorem B923593 : Blo 818347 923593 := bbase (se 2 (by rfl) ⟨346347, by rfl⟩ : syracuseStep 923593 = 692695) (by norm_num)
theorem B923629 : Blo 818347 923629 := bbase (se 3 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 923629 = 346361) (by norm_num)
theorem B1382413 : Blo 818347 1382413 := bbase (se 3 (by rfl) ⟨259202, by rfl⟩ : syracuseStep 1382413 = 518405) (by norm_num)
theorem B923665 : Blo 818347 923665 := bbase (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) (by norm_num)
theorem B2332709 : Blo 818347 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B923701 : Blo 818347 923701 := bbase (se 5 (by rfl) ⟨43298, by rfl⟩ : syracuseStep 923701 = 86597) (by norm_num)
theorem B923737 : Blo 818347 923737 := bbase (se 2 (by rfl) ⟨346401, by rfl⟩ : syracuseStep 923737 = 692803) (by norm_num)
theorem B1382501 : Blo 818347 1382501 := bbase (se 4 (by rfl) ⟨129609, by rfl⟩ : syracuseStep 1382501 = 259219) (by norm_num)
theorem B1316981 : Blo 818347 1316981 := bbase (se 5 (by rfl) ⟨61733, by rfl⟩ : syracuseStep 1316981 = 123467) (by norm_num)
theorem B923773 : Blo 818347 923773 := bbase (se 3 (by rfl) ⟨173207, by rfl⟩ : syracuseStep 923773 = 346415) (by norm_num)
theorem B1841309 : Blo 818347 1841309 := bbase (se 3 (by rfl) ⟨345245, by rfl⟩ : syracuseStep 1841309 = 690491) (by norm_num)
theorem B923809 : Blo 818347 923809 := bbase (se 2 (by rfl) ⟨346428, by rfl⟩ : syracuseStep 923809 = 692857) (by norm_num)
theorem B3119269 : Blo 818347 3119269 := bbase (se 4 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 3119269 = 584863) (by norm_num)
theorem B923845 : Blo 818347 923845 := bbase (se 4 (by rfl) ⟨86610, by rfl⟩ : syracuseStep 923845 = 173221) (by norm_num)
theorem B1841381 : Blo 818347 1841381 := bbase (se 4 (by rfl) ⟨172629, by rfl⟩ : syracuseStep 1841381 = 345259) (by norm_num)
theorem B1382629 : Blo 818347 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B923881 : Blo 818347 923881 := bbase (se 2 (by rfl) ⟨346455, by rfl⟩ : syracuseStep 923881 = 692911) (by norm_num)
theorem B923917 : Blo 818347 923917 := bbase (se 3 (by rfl) ⟨173234, by rfl⟩ : syracuseStep 923917 = 346469) (by norm_num)
theorem B1841453 : Blo 818347 1841453 := bbase (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) (by norm_num)
theorem B923953 : Blo 818347 923953 := bbase (se 2 (by rfl) ⟨346482, by rfl⟩ : syracuseStep 923953 = 692965) (by norm_num)
theorem B1382717 : Blo 818347 1382717 := bbase (se 3 (by rfl) ⟨259259, by rfl⟩ : syracuseStep 1382717 = 518519) (by norm_num)
theorem B1972549 : Blo 818347 1972549 := bbase (se 4 (by rfl) ⟨184926, by rfl⟩ : syracuseStep 1972549 = 369853) (by norm_num)
theorem B923989 : Blo 818347 923989 := bbase (se 10 (by rfl) ⟨1353, by rfl⟩ : syracuseStep 923989 = 2707) (by norm_num)
theorem B1481069 : Blo 818347 1481069 := bbase (se 3 (by rfl) ⟨277700, by rfl⟩ : syracuseStep 1481069 = 555401) (by norm_num)
theorem B1841525 : Blo 818347 1841525 := bbase (se 5 (by rfl) ⟨86321, by rfl⟩ : syracuseStep 1841525 = 172643) (by norm_num)
theorem B924025 : Blo 818347 924025 := bbase (se 2 (by rfl) ⟨346509, by rfl⟩ : syracuseStep 924025 = 693019) (by norm_num)
theorem B924061 : Blo 818347 924061 := bbase (se 3 (by rfl) ⟨173261, by rfl⟩ : syracuseStep 924061 = 346523) (by norm_num)
theorem B1841597 : Blo 818347 1841597 := bbase (se 3 (by rfl) ⟨345299, by rfl⟩ : syracuseStep 1841597 = 690599) (by norm_num)
theorem B1382845 : Blo 818347 1382845 := bbase (se 3 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 1382845 = 518567) (by norm_num)
theorem B924097 : Blo 818347 924097 := bbase (se 2 (by rfl) ⟨346536, by rfl⟩ : syracuseStep 924097 = 693073) (by norm_num)
theorem B3119573 : Blo 818347 3119573 := bbase (se 7 (by rfl) ⟨36557, by rfl⟩ : syracuseStep 3119573 = 73115) (by norm_num)
theorem B924133 : Blo 818347 924133 := bbase (se 4 (by rfl) ⟨86637, by rfl⟩ : syracuseStep 924133 = 173275) (by norm_num)
theorem B1841669 : Blo 818347 1841669 := bbase (se 4 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 1841669 = 345313) (by norm_num)
theorem B924169 : Blo 818347 924169 := bbase (se 2 (by rfl) ⟨346563, by rfl⟩ : syracuseStep 924169 = 693127) (by norm_num)
theorem B1382933 : Blo 818347 1382933 := bbase (se 6 (by rfl) ⟨32412, by rfl⟩ : syracuseStep 1382933 = 64825) (by norm_num)
theorem B2955797 : Blo 818347 2955797 := bbase (se 6 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 2955797 = 138553) (by norm_num)
theorem B1972781 : Blo 818347 1972781 := bbase (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) (by norm_num)
theorem B924205 : Blo 818347 924205 := bbase (se 3 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 924205 = 346577) (by norm_num)
theorem B1841741 : Blo 818347 1841741 := bbase (se 3 (by rfl) ⟨345326, by rfl⟩ : syracuseStep 1841741 = 690653) (by norm_num)
theorem B924241 : Blo 818347 924241 := bbase (se 2 (by rfl) ⟨346590, by rfl⟩ : syracuseStep 924241 = 693181) (by norm_num)
theorem B1972829 : Blo 818347 1972829 := bbase (se 3 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 1972829 = 739811) (by norm_num)
theorem B924277 : Blo 818347 924277 := bbase (se 5 (by rfl) ⟨43325, by rfl⟩ : syracuseStep 924277 = 86651) (by norm_num)
theorem B1841813 : Blo 818347 1841813 := bbase (se 6 (by rfl) ⟨43167, by rfl⟩ : syracuseStep 1841813 = 86335) (by norm_num)
theorem B1383061 : Blo 818347 1383061 := bbase (se 6 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 1383061 = 64831) (by norm_num)
theorem B924313 : Blo 818347 924313 := bbase (se 2 (by rfl) ⟨346617, by rfl⟩ : syracuseStep 924313 = 693235) (by norm_num)
theorem B2136749 : Blo 818347 2136749 := bbase (se 3 (by rfl) ⟨400640, by rfl⟩ : syracuseStep 2136749 = 801281) (by norm_num)
theorem B924349 : Blo 818347 924349 := bbase (se 3 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 924349 = 346631) (by norm_num)
theorem B1841885 : Blo 818347 1841885 := bbase (se 3 (by rfl) ⟨345353, by rfl⟩ : syracuseStep 1841885 = 690707) (by norm_num)
theorem B924385 : Blo 818347 924385 := bbase (se 2 (by rfl) ⟨346644, by rfl⟩ : syracuseStep 924385 = 693289) (by norm_num)
theorem B1383149 : Blo 818347 1383149 := bbase (se 3 (by rfl) ⟨259340, by rfl⟩ : syracuseStep 1383149 = 518681) (by norm_num)
theorem B924421 : Blo 818347 924421 := bbase (se 4 (by rfl) ⟨86664, by rfl⟩ : syracuseStep 924421 = 173329) (by norm_num)
theorem B2333461 : Blo 818347 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B1841957 : Blo 818347 1841957 := bbase (se 4 (by rfl) ⟨172683, by rfl⟩ : syracuseStep 1841957 = 345367) (by norm_num)
theorem B924457 : Blo 818347 924457 := bbase (se 2 (by rfl) ⟨346671, by rfl⟩ : syracuseStep 924457 = 693343) (by norm_num)
theorem B2956085 : Blo 818347 2956085 := bbase (se 5 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 2956085 = 277133) (by norm_num)
theorem B2497349 : Blo 818347 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B924493 : Blo 818347 924493 := bbase (se 3 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 924493 = 346685) (by norm_num)
theorem B3545957 : Blo 818347 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B1842029 : Blo 818347 1842029 := bbase (se 3 (by rfl) ⟨345380, by rfl⟩ : syracuseStep 1842029 = 690761) (by norm_num)
theorem B1383277 : Blo 818347 1383277 := bbase (se 3 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 1383277 = 518729) (by norm_num)
theorem B924529 : Blo 818347 924529 := bbase (se 2 (by rfl) ⟨346698, by rfl⟩ : syracuseStep 924529 = 693397) (by norm_num)
theorem B6232949 : Blo 818347 6232949 := bbase (se 5 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 6232949 = 584339) (by norm_num)
theorem B924565 : Blo 818347 924565 := bbase (se 6 (by rfl) ⟨21669, by rfl⟩ : syracuseStep 924565 = 43339) (by norm_num)
theorem B2071453 : Blo 818347 2071453 := bbase (se 3 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 2071453 = 776795) (by norm_num)
theorem B1842101 : Blo 818347 1842101 := bbase (se 5 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 1842101 = 172697) (by norm_num)
theorem B924601 : Blo 818347 924601 := bbase (se 2 (by rfl) ⟨346725, by rfl⟩ : syracuseStep 924601 = 693451) (by norm_num)
theorem B1383365 : Blo 818347 1383365 := bbase (se 4 (by rfl) ⟨129690, by rfl⟩ : syracuseStep 1383365 = 259381) (by norm_num)
theorem B924637 : Blo 818347 924637 := bbase (se 3 (by rfl) ⟨173369, by rfl⟩ : syracuseStep 924637 = 346739) (by norm_num)
theorem B1874917 : Blo 818347 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B1776629 : Blo 818347 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B1842173 : Blo 818347 1842173 := bbase (se 3 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 1842173 = 690815) (by norm_num)
theorem B924673 : Blo 818347 924673 := bbase (se 2 (by rfl) ⟨346752, by rfl⟩ : syracuseStep 924673 = 693505) (by norm_num)
theorem B2071565 : Blo 818347 2071565 := bbase (se 3 (by rfl) ⟨388418, by rfl⟩ : syracuseStep 2071565 = 776837) (by norm_num)
theorem B924709 : Blo 818347 924709 := bbase (se 4 (by rfl) ⟨86691, by rfl⟩ : syracuseStep 924709 = 173383) (by norm_num)
theorem B1842245 : Blo 818347 1842245 := bbase (se 4 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 1842245 = 345421) (by norm_num)
theorem B1383493 : Blo 818347 1383493 := bbase (se 4 (by rfl) ⟨129702, by rfl⟩ : syracuseStep 1383493 = 259405) (by norm_num)
theorem B924745 : Blo 818347 924745 := bbase (se 2 (by rfl) ⟨346779, by rfl⟩ : syracuseStep 924745 = 693559) (by norm_num)
theorem B924781 : Blo 818347 924781 := bbase (se 3 (by rfl) ⟨173396, by rfl⟩ : syracuseStep 924781 = 346793) (by norm_num)
theorem B1842317 : Blo 818347 1842317 := bbase (se 3 (by rfl) ⟨345434, by rfl⟩ : syracuseStep 1842317 = 690869) (by norm_num)
theorem B924817 : Blo 818347 924817 := bbase (se 2 (by rfl) ⟨346806, by rfl⟩ : syracuseStep 924817 = 693613) (by norm_num)
theorem B1383581 : Blo 818347 1383581 := bbase (se 3 (by rfl) ⟨259421, by rfl⟩ : syracuseStep 1383581 = 518843) (by norm_num)
theorem B924853 : Blo 818347 924853 := bbase (se 5 (by rfl) ⟨43352, by rfl⟩ : syracuseStep 924853 = 86705) (by norm_num)
theorem B2071757 : Blo 818347 2071757 := bbase (se 3 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 2071757 = 776909) (by norm_num)
theorem B1842389 : Blo 818347 1842389 := bbase (se 7 (by rfl) ⟨21590, by rfl⟩ : syracuseStep 1842389 = 43181) (by norm_num)
theorem B924889 : Blo 818347 924889 := bbase (se 2 (by rfl) ⟨346833, by rfl⟩ : syracuseStep 924889 = 693667) (by norm_num)
theorem B2956517 : Blo 818347 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B924925 : Blo 818347 924925 := bbase (se 3 (by rfl) ⟨173423, by rfl⟩ : syracuseStep 924925 = 346847) (by norm_num)
theorem B1842461 : Blo 818347 1842461 := bbase (se 3 (by rfl) ⟨345461, by rfl⟩ : syracuseStep 1842461 = 690923) (by norm_num)
theorem B1383709 : Blo 818347 1383709 := bbase (se 3 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 1383709 = 518891) (by norm_num)
theorem B924961 : Blo 818347 924961 := bbase (se 2 (by rfl) ⟨346860, by rfl⟩ : syracuseStep 924961 = 693721) (by norm_num)
theorem B924997 : Blo 818347 924997 := bbase (se 4 (by rfl) ⟨86718, by rfl⟩ : syracuseStep 924997 = 173437) (by norm_num)
theorem B1842533 : Blo 818347 1842533 := bbase (se 4 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 1842533 = 345475) (by norm_num)
theorem B925033 : Blo 818347 925033 := bbase (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) (by norm_num)
theorem B1383797 : Blo 818347 1383797 := bbase (se 5 (by rfl) ⟨64865, by rfl⟩ : syracuseStep 1383797 = 129731) (by norm_num)
theorem B925069 : Blo 818347 925069 := bbase (se 3 (by rfl) ⟨173450, by rfl⟩ : syracuseStep 925069 = 346901) (by norm_num)
theorem B1842605 : Blo 818347 1842605 := bbase (se 3 (by rfl) ⟨345488, by rfl⟩ : syracuseStep 1842605 = 690977) (by norm_num)
theorem B925105 : Blo 818347 925105 := bbase (se 2 (by rfl) ⟨346914, by rfl⟩ : syracuseStep 925105 = 693829) (by norm_num)
theorem B925141 : Blo 818347 925141 := bbase (se 7 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 925141 = 21683) (by norm_num)
theorem B1842677 : Blo 818347 1842677 := bbase (se 5 (by rfl) ⟨86375, by rfl⟩ : syracuseStep 1842677 = 172751) (by norm_num)
theorem B1383925 : Blo 818347 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B2072101 : Blo 818347 2072101 := bbase (se 4 (by rfl) ⟨194259, by rfl⟩ : syracuseStep 2072101 = 388519) (by norm_num)
theorem B1842749 : Blo 818347 1842749 := bbase (se 3 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 1842749 = 691031) (by norm_num)
theorem B1384013 : Blo 818347 1384013 := bbase (se 3 (by rfl) ⟨259502, by rfl⟩ : syracuseStep 1384013 = 519005) (by norm_num)
theorem B1842821 : Blo 818347 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B2072213 : Blo 818347 2072213 := bbase (se 6 (by rfl) ⟨48567, by rfl⟩ : syracuseStep 2072213 = 97135) (by norm_num)
theorem B1842893 : Blo 818347 1842893 := bbase (se 3 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 1842893 = 691085) (by norm_num)
theorem B1384141 : Blo 818347 1384141 := bbase (se 3 (by rfl) ⟨259526, by rfl⟩ : syracuseStep 1384141 = 519053) (by norm_num)
theorem B1842965 : Blo 818347 1842965 := bbase (se 6 (by rfl) ⟨43194, by rfl⟩ : syracuseStep 1842965 = 86389) (by norm_num)
theorem B1384229 : Blo 818347 1384229 := bbase (se 4 (by rfl) ⟨129771, by rfl⟩ : syracuseStep 1384229 = 259543) (by norm_num)
theorem B2072405 : Blo 818347 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B1843037 : Blo 818347 1843037 := bbase (se 3 (by rfl) ⟨345569, by rfl⟩ : syracuseStep 1843037 = 691139) (by norm_num)
theorem B4202389 : Blo 818347 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B1843109 : Blo 818347 1843109 := bbase (se 4 (by rfl) ⟨172791, by rfl⟩ : syracuseStep 1843109 = 345583) (by norm_num)
theorem B1384357 : Blo 818347 1384357 := bbase (se 4 (by rfl) ⟨129783, by rfl⟩ : syracuseStep 1384357 = 259567) (by norm_num)
theorem B1974221 : Blo 818347 1974221 := bbase (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) (by norm_num)
theorem B1843181 : Blo 818347 1843181 := bbase (se 3 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 1843181 = 691193) (by norm_num)
theorem B1384445 : Blo 818347 1384445 := bbase (se 3 (by rfl) ⟨259583, by rfl⟩ : syracuseStep 1384445 = 519167) (by norm_num)
theorem B1843253 : Blo 818347 1843253 := bbase (se 5 (by rfl) ⟨86402, by rfl⟩ : syracuseStep 1843253 = 172805) (by norm_num)
theorem B1843325 : Blo 818347 1843325 := bbase (se 3 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 1843325 = 691247) (by norm_num)
theorem B1384573 : Blo 818347 1384573 := bbase (se 3 (by rfl) ⟨259607, by rfl⟩ : syracuseStep 1384573 = 519215) (by norm_num)
theorem B1974413 : Blo 818347 1974413 := bbase (se 3 (by rfl) ⟨370202, by rfl⟩ : syracuseStep 1974413 = 740405) (by norm_num)
theorem B2072749 : Blo 818347 2072749 := bbase (se 3 (by rfl) ⟨388640, by rfl⟩ : syracuseStep 2072749 = 777281) (by norm_num)
theorem B1843397 : Blo 818347 1843397 := bbase (se 4 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 1843397 = 345637) (by norm_num)
theorem B1384661 : Blo 818347 1384661 := bbase (se 7 (by rfl) ⟨16226, by rfl⟩ : syracuseStep 1384661 = 32453) (by norm_num)
theorem B1843469 : Blo 818347 1843469 := bbase (se 3 (by rfl) ⟨345650, by rfl⟩ : syracuseStep 1843469 = 691301) (by norm_num)
theorem B2072861 : Blo 818347 2072861 := bbase (se 3 (by rfl) ⟨388661, by rfl⟩ : syracuseStep 2072861 = 777323) (by norm_num)
theorem B1843541 : Blo 818347 1843541 := bbase (se 10 (by rfl) ⟨2700, by rfl⟩ : syracuseStep 1843541 = 5401) (by norm_num)
theorem B1384789 : Blo 818347 1384789 := bbase (se 10 (by rfl) ⟨2028, by rfl⟩ : syracuseStep 1384789 = 4057) (by norm_num)
theorem B1843613 : Blo 818347 1843613 := bbase (se 3 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 1843613 = 691355) (by norm_num)
theorem B1384877 : Blo 818347 1384877 := bbase (se 3 (by rfl) ⟨259664, by rfl⟩ : syracuseStep 1384877 = 519329) (by norm_num)
theorem B2073053 : Blo 818347 2073053 := bbase (se 3 (by rfl) ⟨388697, by rfl⟩ : syracuseStep 2073053 = 777395) (by norm_num)
theorem B1843685 : Blo 818347 1843685 := bbase (se 4 (by rfl) ⟨172845, by rfl⟩ : syracuseStep 1843685 = 345691) (by norm_num)
theorem B3121685 : Blo 818347 3121685 := bbase (se 6 (by rfl) ⟨73164, by rfl⟩ : syracuseStep 3121685 = 146329) (by norm_num)
theorem B1843757 : Blo 818347 1843757 := bbase (se 3 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 1843757 = 691409) (by norm_num)
theorem B1385005 : Blo 818347 1385005 := bbase (se 3 (by rfl) ⟨259688, by rfl⟩ : syracuseStep 1385005 = 519377) (by norm_num)
theorem B1843829 : Blo 818347 1843829 := bbase (se 5 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 1843829 = 172859) (by norm_num)
theorem B3154565 : Blo 818347 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B1385093 : Blo 818347 1385093 := bbase (se 4 (by rfl) ⟨129852, by rfl⟩ : syracuseStep 1385093 = 259705) (by norm_num)
theorem B1843901 : Blo 818347 1843901 := bbase (se 3 (by rfl) ⟨345731, by rfl⟩ : syracuseStep 1843901 = 691463) (by norm_num)
theorem B1843973 : Blo 818347 1843973 := bbase (se 4 (by rfl) ⟨172872, by rfl⟩ : syracuseStep 1843973 = 345745) (by norm_num)
theorem B1385221 : Blo 818347 1385221 := bbase (se 4 (by rfl) ⟨129864, by rfl⟩ : syracuseStep 1385221 = 259729) (by norm_num)
theorem B2073397 : Blo 818347 2073397 := bbase (se 5 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 2073397 = 194381) (by norm_num)
theorem B3121973 : Blo 818347 3121973 := bbase (se 5 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 3121973 = 292685) (by norm_num)
theorem B1844045 : Blo 818347 1844045 := bbase (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) (by norm_num)
theorem B1385309 : Blo 818347 1385309 := bbase (se 3 (by rfl) ⟨259745, by rfl⟩ : syracuseStep 1385309 = 519491) (by norm_num)
theorem B2630501 : Blo 818347 2630501 := bbase (se 4 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 2630501 = 493219) (by norm_num)
theorem B1844117 : Blo 818347 1844117 := bbase (se 6 (by rfl) ⟨43221, by rfl⟩ : syracuseStep 1844117 = 86443) (by norm_num)
theorem B2073509 : Blo 818347 2073509 := bbase (se 4 (by rfl) ⟨194391, by rfl⟩ : syracuseStep 2073509 = 388783) (by norm_num)
theorem B1844189 : Blo 818347 1844189 := bbase (se 3 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 1844189 = 691571) (by norm_num)
theorem B1385437 : Blo 818347 1385437 := bbase (se 3 (by rfl) ⟨259769, by rfl⟩ : syracuseStep 1385437 = 519539) (by norm_num)
theorem B14001173 : Blo 818347 14001173 := bbase (se 6 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 14001173 = 656305) (by norm_num)
theorem B1844261 : Blo 818347 1844261 := bbase (se 4 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 1844261 = 345799) (by norm_num)
theorem B1385525 : Blo 818347 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B4432981 : Blo 818347 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B2073701 : Blo 818347 2073701 := bbase (se 4 (by rfl) ⟨194409, by rfl⟩ : syracuseStep 2073701 = 388819) (by norm_num)
theorem B1844333 : Blo 818347 1844333 := bbase (se 3 (by rfl) ⟨345812, by rfl⟩ : syracuseStep 1844333 = 691625) (by norm_num)
theorem B1844405 : Blo 818347 1844405 := bbase (se 5 (by rfl) ⟨86456, by rfl⟩ : syracuseStep 1844405 = 172913) (by norm_num)
theorem B2368693 : Blo 818347 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B1385653 : Blo 818347 1385653 := bbase (se 5 (by rfl) ⟨64952, by rfl⟩ : syracuseStep 1385653 = 129905) (by norm_num)
theorem B1582301 : Blo 818347 1582301 := bbase (se 3 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 1582301 = 593363) (by norm_num)
theorem B1844477 : Blo 818347 1844477 := bbase (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) (by norm_num)
theorem B1385741 : Blo 818347 1385741 := bbase (se 3 (by rfl) ⟨259826, by rfl⟩ : syracuseStep 1385741 = 519653) (by norm_num)
theorem B1844549 : Blo 818347 1844549 := bbase (se 4 (by rfl) ⟨172926, by rfl⟩ : syracuseStep 1844549 = 345853) (by norm_num)
theorem B2106757 : Blo 818347 2106757 := bbase (se 4 (by rfl) ⟨197508, by rfl⟩ : syracuseStep 2106757 = 395017) (by norm_num)
theorem B1844621 : Blo 818347 1844621 := bbase (se 3 (by rfl) ⟨345866, by rfl⟩ : syracuseStep 1844621 = 691733) (by norm_num)
theorem B1385869 : Blo 818347 1385869 := bbase (se 3 (by rfl) ⟨259850, by rfl⟩ : syracuseStep 1385869 = 519701) (by norm_num)
theorem B2074045 : Blo 818347 2074045 := bbase (se 3 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 2074045 = 777767) (by norm_num)
theorem B1844693 : Blo 818347 1844693 := bbase (se 7 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 1844693 = 43235) (by norm_num)
theorem B2368997 : Blo 818347 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B1385957 : Blo 818347 1385957 := bbase (se 4 (by rfl) ⟨129933, by rfl⟩ : syracuseStep 1385957 = 259867) (by norm_num)
theorem B2762261 : Blo 818347 2762261 := bbase (se 6 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 2762261 = 129481) (by norm_num)
theorem B1844765 : Blo 818347 1844765 := bbase (se 3 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 1844765 = 691787) (by norm_num)
theorem B2074157 : Blo 818347 2074157 := bbase (se 3 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 2074157 = 777809) (by norm_num)
theorem B2336309 : Blo 818347 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B1844837 : Blo 818347 1844837 := bbase (se 4 (by rfl) ⟨172953, by rfl⟩ : syracuseStep 1844837 = 345907) (by norm_num)
theorem B1386085 : Blo 818347 1386085 := bbase (se 4 (by rfl) ⟨129945, by rfl⟩ : syracuseStep 1386085 = 259891) (by norm_num)
theorem B1844909 : Blo 818347 1844909 := bbase (se 3 (by rfl) ⟨345920, by rfl⟩ : syracuseStep 1844909 = 691841) (by norm_num)
theorem B1386173 : Blo 818347 1386173 := bbase (se 3 (by rfl) ⟨259907, by rfl⟩ : syracuseStep 1386173 = 519815) (by norm_num)
theorem B2074349 : Blo 818347 2074349 := bbase (se 3 (by rfl) ⟨388940, by rfl⟩ : syracuseStep 2074349 = 777881) (by norm_num)
theorem B1844981 : Blo 818347 1844981 := bbase (se 5 (by rfl) ⟨86483, by rfl⟩ : syracuseStep 1844981 = 172967) (by norm_num)
theorem B1845053 : Blo 818347 1845053 := bbase (se 3 (by rfl) ⟨345947, by rfl⟩ : syracuseStep 1845053 = 691895) (by norm_num)
theorem B1386301 : Blo 818347 1386301 := bbase (se 3 (by rfl) ⟨259931, by rfl⟩ : syracuseStep 1386301 = 519863) (by norm_num)
theorem B1845125 : Blo 818347 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B1386389 : Blo 818347 1386389 := bbase (se 6 (by rfl) ⟨32493, by rfl⟩ : syracuseStep 1386389 = 64987) (by norm_num)
theorem B2762693 : Blo 818347 2762693 := bbase (se 4 (by rfl) ⟨259002, by rfl⟩ : syracuseStep 2762693 = 518005) (by norm_num)
theorem B1845197 : Blo 818347 1845197 := bbase (se 3 (by rfl) ⟨345974, by rfl⟩ : syracuseStep 1845197 = 691949) (by norm_num)
theorem B1845269 : Blo 818347 1845269 := bbase (se 6 (by rfl) ⟨43248, by rfl⟩ : syracuseStep 1845269 = 86497) (by norm_num)
theorem B1386517 : Blo 818347 1386517 := bbase (se 6 (by rfl) ⟨32496, by rfl⟩ : syracuseStep 1386517 = 64993) (by norm_num)
theorem B2074693 : Blo 818347 2074693 := bbase (se 4 (by rfl) ⟨194502, by rfl⟩ : syracuseStep 2074693 = 389005) (by norm_num)
theorem B6006869 : Blo 818347 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B1845341 : Blo 818347 1845341 := bbase (se 3 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 1845341 = 692003) (by norm_num)
theorem B2631781 : Blo 818347 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B1386605 : Blo 818347 1386605 := bbase (se 3 (by rfl) ⟨259988, by rfl⟩ : syracuseStep 1386605 = 519977) (by norm_num)
theorem B1845413 : Blo 818347 1845413 := bbase (se 4 (by rfl) ⟨173007, by rfl⟩ : syracuseStep 1845413 = 346015) (by norm_num)
theorem B2074805 : Blo 818347 2074805 := bbase (se 5 (by rfl) ⟨97256, by rfl⟩ : syracuseStep 2074805 = 194513) (by norm_num)
theorem B1845485 : Blo 818347 1845485 := bbase (se 3 (by rfl) ⟨346028, by rfl⟩ : syracuseStep 1845485 = 692057) (by norm_num)
theorem B1386733 : Blo 818347 1386733 := bbase (se 3 (by rfl) ⟨260012, by rfl⟩ : syracuseStep 1386733 = 520025) (by norm_num)
theorem B1845557 : Blo 818347 1845557 := bbase (se 5 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 1845557 = 173021) (by norm_num)
theorem B1386821 : Blo 818347 1386821 := bbase (se 4 (by rfl) ⟨130014, by rfl⟩ : syracuseStep 1386821 = 260029) (by norm_num)
theorem B2763125 : Blo 818347 2763125 := bbase (se 5 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 2763125 = 259043) (by norm_num)
theorem B2074997 : Blo 818347 2074997 := bbase (se 5 (by rfl) ⟨97265, by rfl⟩ : syracuseStep 2074997 = 194531) (by norm_num)
theorem B1845629 : Blo 818347 1845629 := bbase (se 3 (by rfl) ⟨346055, by rfl⟩ : syracuseStep 1845629 = 692111) (by norm_num)
theorem B1845701 : Blo 818347 1845701 := bbase (se 4 (by rfl) ⟨173034, by rfl⟩ : syracuseStep 1845701 = 346069) (by norm_num)
theorem B1386949 : Blo 818347 1386949 := bbase (se 4 (by rfl) ⟨130026, by rfl⟩ : syracuseStep 1386949 = 260053) (by norm_num)
theorem B1845773 : Blo 818347 1845773 := bbase (se 3 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 1845773 = 692165) (by norm_num)
theorem B1387037 : Blo 818347 1387037 := bbase (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) (by norm_num)
theorem B3156533 : Blo 818347 3156533 := bbase (se 5 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 3156533 = 295925) (by norm_num)
theorem B830017 : Blo 818347 830017 := bbase (se 2 (by rfl) ⟨311256, by rfl⟩ : syracuseStep 830017 = 622513) (by norm_num)
theorem B1845845 : Blo 818347 1845845 := bbase (se 8 (by rfl) ⟨10815, by rfl⟩ : syracuseStep 1845845 = 21631) (by norm_num)
theorem B830069 : Blo 818347 830069 := bbase (se 5 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 830069 = 77819) (by norm_num)
theorem B1845917 : Blo 818347 1845917 := bbase (se 3 (by rfl) ⟨346109, by rfl⟩ : syracuseStep 1845917 = 692219) (by norm_num)
theorem B1387165 : Blo 818347 1387165 := bbase (se 3 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 1387165 = 520187) (by norm_num)
theorem B2632357 : Blo 818347 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B2075341 : Blo 818347 2075341 := bbase (se 3 (by rfl) ⟨389126, by rfl⟩ : syracuseStep 2075341 = 778253) (by norm_num)
theorem B2337493 : Blo 818347 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B1845989 : Blo 818347 1845989 := bbase (se 4 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 1845989 = 346123) (by norm_num)
theorem B1387253 : Blo 818347 1387253 := bbase (se 5 (by rfl) ⟨65027, by rfl⟩ : syracuseStep 1387253 = 130055) (by norm_num)
theorem B2763557 : Blo 818347 2763557 := bbase (se 4 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 2763557 = 518167) (by norm_num)
theorem B2960165 : Blo 818347 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B1846061 : Blo 818347 1846061 := bbase (se 3 (by rfl) ⟨346136, by rfl⟩ : syracuseStep 1846061 = 692273) (by norm_num)
theorem B2075453 : Blo 818347 2075453 := bbase (se 3 (by rfl) ⟨389147, by rfl⟩ : syracuseStep 2075453 = 778295) (by norm_num)
theorem B1846133 : Blo 818347 1846133 := bbase (se 5 (by rfl) ⟨86537, by rfl⟩ : syracuseStep 1846133 = 173075) (by norm_num)
theorem B2337653 : Blo 818347 2337653 := bbase (se 5 (by rfl) ⟨109577, by rfl⟩ : syracuseStep 2337653 = 219155) (by norm_num)
theorem B1387381 : Blo 818347 1387381 := bbase (se 5 (by rfl) ⟨65033, by rfl⟩ : syracuseStep 1387381 = 130067) (by norm_num)
theorem B2960293 : Blo 818347 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B1846205 : Blo 818347 1846205 := bbase (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) (by norm_num)
theorem B1747909 : Blo 818347 1747909 := bbase (se 4 (by rfl) ⟨163866, by rfl⟩ : syracuseStep 1747909 = 327733) (by norm_num)
theorem B1387469 : Blo 818347 1387469 := bbase (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) (by norm_num)
theorem B2075645 : Blo 818347 2075645 := bbase (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) (by norm_num)
theorem B1846277 : Blo 818347 1846277 := bbase (se 4 (by rfl) ⟨173088, by rfl⟩ : syracuseStep 1846277 = 346177) (by norm_num)
theorem B1846349 : Blo 818347 1846349 := bbase (se 3 (by rfl) ⟨346190, by rfl⟩ : syracuseStep 1846349 = 692381) (by norm_num)
theorem B1387597 : Blo 818347 1387597 := bbase (se 3 (by rfl) ⟨260174, by rfl⟩ : syracuseStep 1387597 = 520349) (by norm_num)
theorem B2337893 : Blo 818347 2337893 := bbase (se 4 (by rfl) ⟨219177, by rfl⟩ : syracuseStep 2337893 = 438355) (by norm_num)
theorem B1846421 : Blo 818347 1846421 := bbase (se 6 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 1846421 = 86551) (by norm_num)
theorem B1387685 : Blo 818347 1387685 := bbase (se 4 (by rfl) ⟨130095, by rfl⟩ : syracuseStep 1387685 = 260191) (by norm_num)
theorem B830633 : Blo 818347 830633 := bbase (se 2 (by rfl) ⟨311487, by rfl⟩ : syracuseStep 830633 = 622975) (by norm_num)
theorem B2763989 : Blo 818347 2763989 := bbase (se 7 (by rfl) ⟨32390, by rfl⟩ : syracuseStep 2763989 = 64781) (by norm_num)
theorem B1846493 : Blo 818347 1846493 := bbase (se 3 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 1846493 = 692435) (by norm_num)
theorem B1846565 : Blo 818347 1846565 := bbase (se 4 (by rfl) ⟨173115, by rfl⟩ : syracuseStep 1846565 = 346231) (by norm_num)
theorem B2338085 : Blo 818347 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B5680469 : Blo 818347 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B2075989 : Blo 818347 2075989 := bbase (se 11 (by rfl) ⟨1520, by rfl⟩ : syracuseStep 2075989 = 3041) (by norm_num)
theorem B1846637 : Blo 818347 1846637 := bbase (se 3 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 1846637 = 692489) (by norm_num)
theorem B3943829 : Blo 818347 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B1748405 : Blo 818347 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B1846709 : Blo 818347 1846709 := bbase (se 5 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 1846709 = 173129) (by norm_num)
theorem B2633141 : Blo 818347 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B2076101 : Blo 818347 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B830945 : Blo 818347 830945 := bbase (se 2 (by rfl) ⟨311604, by rfl⟩ : syracuseStep 830945 = 623209) (by norm_num)
theorem B1846781 : Blo 818347 1846781 := bbase (se 3 (by rfl) ⟨346271, by rfl⟩ : syracuseStep 1846781 = 692543) (by norm_num)
theorem B2633269 : Blo 818347 2633269 := bbase (se 5 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 2633269 = 246869) (by norm_num)
theorem B1846853 : Blo 818347 1846853 := bbase (se 4 (by rfl) ⟨173142, by rfl⟩ : syracuseStep 1846853 = 346285) (by norm_num)
theorem B3321445 : Blo 818347 3321445 := bbase (se 4 (by rfl) ⟨311385, by rfl⟩ : syracuseStep 3321445 = 622771) (by norm_num)
theorem B2764421 : Blo 818347 2764421 := bbase (se 4 (by rfl) ⟨259164, by rfl⟩ : syracuseStep 2764421 = 518329) (by norm_num)
theorem B2076293 : Blo 818347 2076293 := bbase (se 4 (by rfl) ⟨194652, by rfl⟩ : syracuseStep 2076293 = 389305) (by norm_num)
theorem B1846925 : Blo 818347 1846925 := bbase (se 3 (by rfl) ⟨346298, by rfl⟩ : syracuseStep 1846925 = 692597) (by norm_num)
theorem B7876277 : Blo 818347 7876277 := bbase (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) (by norm_num)
theorem B1846997 : Blo 818347 1846997 := bbase (se 7 (by rfl) ⟨21644, by rfl⟩ : syracuseStep 1846997 = 43289) (by norm_num)
theorem B1847069 : Blo 818347 1847069 := bbase (se 3 (by rfl) ⟨346325, by rfl⟩ : syracuseStep 1847069 = 692651) (by norm_num)
theorem B2633525 : Blo 818347 2633525 := bbase (se 5 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 2633525 = 246893) (by norm_num)
theorem B1847141 : Blo 818347 1847141 := bbase (se 4 (by rfl) ⟨173169, by rfl⟩ : syracuseStep 1847141 = 346339) (by norm_num)
theorem B1847213 : Blo 818347 1847213 := bbase (se 3 (by rfl) ⟨346352, by rfl⟩ : syracuseStep 1847213 = 692705) (by norm_num)
theorem B2076637 : Blo 818347 2076637 := bbase (se 3 (by rfl) ⟨389369, by rfl⟩ : syracuseStep 2076637 = 778739) (by norm_num)
theorem B1847285 : Blo 818347 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B2109445 : Blo 818347 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B2764853 : Blo 818347 2764853 := bbase (se 5 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 2764853 = 259205) (by norm_num)
theorem B1847357 : Blo 818347 1847357 := bbase (se 3 (by rfl) ⟨346379, by rfl⟩ : syracuseStep 1847357 = 692759) (by norm_num)
theorem B2076749 : Blo 818347 2076749 := bbase (se 3 (by rfl) ⟨389390, by rfl⟩ : syracuseStep 2076749 = 778781) (by norm_num)
theorem B1847429 : Blo 818347 1847429 := bbase (se 4 (by rfl) ⟨173196, by rfl⟩ : syracuseStep 1847429 = 346393) (by norm_num)
theorem B1847501 : Blo 818347 1847501 := bbase (se 3 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 1847501 = 692813) (by norm_num)
theorem B2339077 : Blo 818347 2339077 := bbase (se 4 (by rfl) ⟨219288, by rfl⟩ : syracuseStep 2339077 = 438577) (by norm_num)
theorem B2076941 : Blo 818347 2076941 := bbase (se 3 (by rfl) ⟨389426, by rfl⟩ : syracuseStep 2076941 = 778853) (by norm_num)
theorem B1847573 : Blo 818347 1847573 := bbase (se 6 (by rfl) ⟨43302, by rfl⟩ : syracuseStep 1847573 = 86605) (by norm_num)
theorem B1749293 : Blo 818347 1749293 := bbase (se 3 (by rfl) ⟨327992, by rfl⟩ : syracuseStep 1749293 = 655985) (by norm_num)
theorem B1847645 : Blo 818347 1847645 := bbase (se 3 (by rfl) ⟨346433, by rfl⟩ : syracuseStep 1847645 = 692867) (by norm_num)
theorem B1749413 : Blo 818347 1749413 := bbase (se 4 (by rfl) ⟨164007, by rfl⟩ : syracuseStep 1749413 = 328015) (by norm_num)
theorem B1847717 : Blo 818347 1847717 := bbase (se 4 (by rfl) ⟨173223, by rfl⟩ : syracuseStep 1847717 = 346447) (by norm_num)
theorem B2765285 : Blo 818347 2765285 := bbase (se 4 (by rfl) ⟨259245, by rfl⟩ : syracuseStep 2765285 = 518491) (by norm_num)
theorem B1847789 : Blo 818347 1847789 := bbase (se 3 (by rfl) ⟨346460, by rfl⟩ : syracuseStep 1847789 = 692921) (by norm_num)
theorem B3748373 : Blo 818347 3748373 := bbase (se 6 (by rfl) ⟨87852, by rfl⟩ : syracuseStep 3748373 = 175705) (by norm_num)
theorem B1847861 : Blo 818347 1847861 := bbase (se 5 (by rfl) ⟨86618, by rfl⟩ : syracuseStep 1847861 = 173237) (by norm_num)
theorem B2077285 : Blo 818347 2077285 := bbase (se 4 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 2077285 = 389491) (by norm_num)
theorem B1847933 : Blo 818347 1847933 := bbase (se 3 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 1847933 = 692975) (by norm_num)
theorem B832145 : Blo 818347 832145 := bbase (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) (by norm_num)
theorem B1848005 : Blo 818347 1848005 := bbase (se 4 (by rfl) ⟨173250, by rfl⟩ : syracuseStep 1848005 = 346501) (by norm_num)
theorem B2077397 : Blo 818347 2077397 := bbase (se 7 (by rfl) ⟨24344, by rfl⟩ : syracuseStep 2077397 = 48689) (by norm_num)
theorem B1848077 : Blo 818347 1848077 := bbase (se 3 (by rfl) ⟨346514, by rfl⟩ : syracuseStep 1848077 = 693029) (by norm_num)
theorem B1848149 : Blo 818347 1848149 := bbase (se 9 (by rfl) ⟨5414, by rfl⟩ : syracuseStep 1848149 = 10829) (by norm_num)
theorem B2765717 : Blo 818347 2765717 := bbase (se 6 (by rfl) ⟨64821, by rfl⟩ : syracuseStep 2765717 = 129643) (by norm_num)
theorem B2077589 : Blo 818347 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B1848221 : Blo 818347 1848221 := bbase (se 3 (by rfl) ⟨346541, by rfl⟩ : syracuseStep 1848221 = 693083) (by norm_num)
theorem B1848293 : Blo 818347 1848293 := bbase (se 4 (by rfl) ⟨173277, by rfl⟩ : syracuseStep 1848293 = 346555) (by norm_num)
theorem B5256181 : Blo 818347 5256181 := bbase (se 5 (by rfl) ⟨246383, by rfl⟩ : syracuseStep 5256181 = 492767) (by norm_num)
theorem B1750045 : Blo 818347 1750045 := bbase (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) (by norm_num)
theorem B1848365 : Blo 818347 1848365 := bbase (se 3 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 1848365 = 693137) (by norm_num)
theorem B1848437 : Blo 818347 1848437 := bbase (se 5 (by rfl) ⟨86645, by rfl⟩ : syracuseStep 1848437 = 173291) (by norm_num)
theorem B1848509 : Blo 818347 1848509 := bbase (se 3 (by rfl) ⟨346595, by rfl⟩ : syracuseStep 1848509 = 693191) (by norm_num)
theorem B2077933 : Blo 818347 2077933 := bbase (se 3 (by rfl) ⟨389612, by rfl⟩ : syracuseStep 2077933 = 779225) (by norm_num)
theorem B1848581 : Blo 818347 1848581 := bbase (se 4 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 1848581 = 346609) (by norm_num)
theorem B2766149 : Blo 818347 2766149 := bbase (se 4 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 2766149 = 518653) (by norm_num)
theorem B1848653 : Blo 818347 1848653 := bbase (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) (by norm_num)
theorem B2340181 : Blo 818347 2340181 := bbase (se 13 (by rfl) ⟨428, by rfl⟩ : syracuseStep 2340181 = 857) (by norm_num)
theorem B2078045 : Blo 818347 2078045 := bbase (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) (by norm_num)
theorem B1848725 : Blo 818347 1848725 := bbase (se 6 (by rfl) ⟨43329, by rfl⟩ : syracuseStep 1848725 = 86659) (by norm_num)
theorem B1848797 : Blo 818347 1848797 := bbase (se 3 (by rfl) ⟨346649, by rfl⟩ : syracuseStep 1848797 = 693299) (by norm_num)
theorem B1553917 : Blo 818347 1553917 := bbase (se 3 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 1553917 = 582719) (by norm_num)
theorem B2078237 : Blo 818347 2078237 := bbase (se 3 (by rfl) ⟨389669, by rfl⟩ : syracuseStep 2078237 = 779339) (by norm_num)
theorem B1848869 : Blo 818347 1848869 := bbase (se 4 (by rfl) ⟨173331, by rfl⟩ : syracuseStep 1848869 = 346663) (by norm_num)
theorem B1848941 : Blo 818347 1848941 := bbase (se 3 (by rfl) ⟨346676, by rfl⟩ : syracuseStep 1848941 = 693353) (by norm_num)
theorem B1554061 : Blo 818347 1554061 := bbase (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) (by norm_num)
theorem B1849013 : Blo 818347 1849013 := bbase (se 5 (by rfl) ⟨86672, by rfl⟩ : syracuseStep 1849013 = 173345) (by norm_num)
theorem B2766581 : Blo 818347 2766581 := bbase (se 5 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 2766581 = 259367) (by norm_num)
theorem B1849085 : Blo 818347 1849085 := bbase (se 3 (by rfl) ⟨346703, by rfl⟩ : syracuseStep 1849085 = 693407) (by norm_num)
theorem B1554221 : Blo 818347 1554221 := bbase (se 3 (by rfl) ⟨291416, by rfl⟩ : syracuseStep 1554221 = 582833) (by norm_num)
theorem B1849157 : Blo 818347 1849157 := bbase (se 4 (by rfl) ⟨173358, by rfl⟩ : syracuseStep 1849157 = 346717) (by norm_num)
theorem B4437845 : Blo 818347 4437845 := bbase (se 9 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 4437845 = 26003) (by norm_num)
theorem B2078581 : Blo 818347 2078581 := bbase (se 5 (by rfl) ⟨97433, by rfl⟩ : syracuseStep 2078581 = 194867) (by norm_num)
theorem B1849229 : Blo 818347 1849229 := bbase (se 3 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 1849229 = 693461) (by norm_num)
theorem B1750933 : Blo 818347 1750933 := bbase (se 6 (by rfl) ⟨41037, by rfl⟩ : syracuseStep 1750933 = 82075) (by norm_num)
theorem B1554365 : Blo 818347 1554365 := bbase (se 3 (by rfl) ⟨291443, by rfl⟩ : syracuseStep 1554365 = 582887) (by norm_num)
theorem B1849301 : Blo 818347 1849301 := bbase (se 7 (by rfl) ⟨21671, by rfl⟩ : syracuseStep 1849301 = 43343) (by norm_num)
theorem B2078693 : Blo 818347 2078693 := bbase (se 4 (by rfl) ⟨194877, by rfl⟩ : syracuseStep 2078693 = 389755) (by norm_num)
theorem B1751053 : Blo 818347 1751053 := bbase (se 3 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 1751053 = 656645) (by norm_num)
theorem B1849373 : Blo 818347 1849373 := bbase (se 3 (by rfl) ⟨346757, by rfl⟩ : syracuseStep 1849373 = 693515) (by norm_num)
theorem B1849445 : Blo 818347 1849445 := bbase (se 4 (by rfl) ⟨173385, by rfl⟩ : syracuseStep 1849445 = 346771) (by norm_num)
theorem B2767013 : Blo 818347 2767013 := bbase (se 4 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 2767013 = 518815) (by norm_num)
theorem B2078885 : Blo 818347 2078885 := bbase (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) (by norm_num)
theorem B1849517 : Blo 818347 1849517 := bbase (se 3 (by rfl) ⟨346784, by rfl⟩ : syracuseStep 1849517 = 693569) (by norm_num)
theorem B17742037 : Blo 818347 17742037 := bbase (se 7 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 17742037 = 415829) (by norm_num)
theorem B1554653 : Blo 818347 1554653 := bbase (se 3 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 1554653 = 582995) (by norm_num)
theorem B1849589 : Blo 818347 1849589 := bbase (se 5 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 1849589 = 173399) (by norm_num)
theorem B1751309 : Blo 818347 1751309 := bbase (se 3 (by rfl) ⟨328370, by rfl⟩ : syracuseStep 1751309 = 656741) (by norm_num)
theorem B1849661 : Blo 818347 1849661 := bbase (se 3 (by rfl) ⟨346811, by rfl⟩ : syracuseStep 1849661 = 693623) (by norm_num)
theorem B2242885 : Blo 818347 2242885 := bbase (se 4 (by rfl) ⟨210270, by rfl⟩ : syracuseStep 2242885 = 420541) (by norm_num)
theorem B1554805 : Blo 818347 1554805 := bbase (se 5 (by rfl) ⟨72881, by rfl⟩ : syracuseStep 1554805 = 145763) (by norm_num)
theorem B1849733 : Blo 818347 1849733 := bbase (se 4 (by rfl) ⟨173412, by rfl⟩ : syracuseStep 1849733 = 346825) (by norm_num)
theorem B1423765 : Blo 818347 1423765 := bbase (se 6 (by rfl) ⟨33369, by rfl⟩ : syracuseStep 1423765 = 66739) (by norm_num)
theorem B1849805 : Blo 818347 1849805 := bbase (se 3 (by rfl) ⟨346838, by rfl⟩ : syracuseStep 1849805 = 693677) (by norm_num)
theorem B6240725 : Blo 818347 6240725 := bbase (se 7 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 6240725 = 146267) (by norm_num)
theorem B3946981 : Blo 818347 3946981 := bbase (se 4 (by rfl) ⟨370029, by rfl⟩ : syracuseStep 3946981 = 740059) (by norm_num)
theorem B2079229 : Blo 818347 2079229 := bbase (se 3 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 2079229 = 779711) (by norm_num)
theorem B1849877 : Blo 818347 1849877 := bbase (se 6 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 1849877 = 86713) (by norm_num)
theorem B2767445 : Blo 818347 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B1686101 : Blo 818347 1686101 := bbase (se 8 (by rfl) ⟨9879, by rfl⟩ : syracuseStep 1686101 = 19759) (by norm_num)
theorem B1849949 : Blo 818347 1849949 := bbase (se 3 (by rfl) ⟨346865, by rfl⟩ : syracuseStep 1849949 = 693731) (by norm_num)
theorem B2079341 : Blo 818347 2079341 := bbase (se 3 (by rfl) ⟨389876, by rfl⟩ : syracuseStep 2079341 = 779753) (by norm_num)
theorem B1555109 : Blo 818347 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1850021 : Blo 818347 1850021 := bbase (se 4 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 1850021 = 346879) (by norm_num)
theorem B4143797 : Blo 818347 4143797 := bbase (se 5 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 4143797 = 388481) (by norm_num)
theorem B1850093 : Blo 818347 1850093 := bbase (se 3 (by rfl) ⟨346892, by rfl⟩ : syracuseStep 1850093 = 693785) (by norm_num)
theorem B1227533 : Blo 818347 1227533 := bbase (se 3 (by rfl) ⟨230162, by rfl⟩ : syracuseStep 1227533 = 460325) (by norm_num)
theorem B1227557 : Blo 818347 1227557 := bbase (se 4 (by rfl) ⟨115083, by rfl⟩ : syracuseStep 1227557 = 230167) (by norm_num)
theorem B2079533 : Blo 818347 2079533 := bbase (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) (by norm_num)
theorem B1850165 : Blo 818347 1850165 := bbase (se 5 (by rfl) ⟨86726, by rfl⟩ : syracuseStep 1850165 = 173453) (by norm_num)
theorem B2341685 : Blo 818347 2341685 := bbase (se 5 (by rfl) ⟨109766, by rfl⟩ : syracuseStep 2341685 = 219533) (by norm_num)
theorem B1227581 : Blo 818347 1227581 := bbase (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) (by norm_num)
theorem B1227605 : Blo 818347 1227605 := bbase (se 9 (by rfl) ⟨3596, by rfl⟩ : syracuseStep 1227605 = 7193) (by norm_num)
theorem B1227629 : Blo 818347 1227629 := bbase (se 3 (by rfl) ⟨230180, by rfl⟩ : syracuseStep 1227629 = 460361) (by norm_num)
theorem B1850237 : Blo 818347 1850237 := bbase (se 3 (by rfl) ⟨346919, by rfl⟩ : syracuseStep 1850237 = 693839) (by norm_num)
theorem B1227653 : Blo 818347 1227653 := bbase (se 4 (by rfl) ⟨115092, by rfl⟩ : syracuseStep 1227653 = 230185) (by norm_num)
theorem B1227677 : Blo 818347 1227677 := bbase (se 3 (by rfl) ⟨230189, by rfl⟩ : syracuseStep 1227677 = 460379) (by norm_num)
theorem B1227701 : Blo 818347 1227701 := bbase (se 5 (by rfl) ⟨57548, by rfl⟩ : syracuseStep 1227701 = 115097) (by norm_num)
theorem B1227725 : Blo 818347 1227725 := bbase (se 3 (by rfl) ⟨230198, by rfl⟩ : syracuseStep 1227725 = 460397) (by norm_num)
theorem B998357 : Blo 818347 998357 := bbase (se 7 (by rfl) ⟨11699, by rfl⟩ : syracuseStep 998357 = 23399) (by norm_num)
theorem B1227749 : Blo 818347 1227749 := bbase (se 4 (by rfl) ⟨115101, by rfl⟩ : syracuseStep 1227749 = 230203) (by norm_num)
theorem B1227773 : Blo 818347 1227773 := bbase (se 3 (by rfl) ⟨230207, by rfl⟩ : syracuseStep 1227773 = 460415) (by norm_num)
theorem B2767877 : Blo 818347 2767877 := bbase (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) (by norm_num)
theorem B1227797 : Blo 818347 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B1227821 : Blo 818347 1227821 := bbase (se 3 (by rfl) ⟨230216, by rfl⟩ : syracuseStep 1227821 = 460433) (by norm_num)
theorem B1227845 : Blo 818347 1227845 := bbase (se 4 (by rfl) ⟨115110, by rfl⟩ : syracuseStep 1227845 = 230221) (by norm_num)
theorem B1227869 : Blo 818347 1227869 := bbase (se 3 (by rfl) ⟨230225, by rfl⟩ : syracuseStep 1227869 = 460451) (by norm_num)
theorem B1227893 : Blo 818347 1227893 := bbase (se 5 (by rfl) ⟨57557, by rfl⟩ : syracuseStep 1227893 = 115115) (by norm_num)
theorem B1752197 : Blo 818347 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B2079877 : Blo 818347 2079877 := bbase (se 4 (by rfl) ⟨194988, by rfl⟩ : syracuseStep 2079877 = 389977) (by norm_num)
theorem B1227917 : Blo 818347 1227917 := bbase (se 3 (by rfl) ⟨230234, by rfl⟩ : syracuseStep 1227917 = 460469) (by norm_num)
theorem B1227941 : Blo 818347 1227941 := bbase (se 4 (by rfl) ⟨115119, by rfl⟩ : syracuseStep 1227941 = 230239) (by norm_num)
theorem B1227965 : Blo 818347 1227965 := bbase (se 3 (by rfl) ⟨230243, by rfl⟩ : syracuseStep 1227965 = 460487) (by norm_num)
theorem B1227989 : Blo 818347 1227989 := bbase (se 7 (by rfl) ⟨14390, by rfl⟩ : syracuseStep 1227989 = 28781) (by norm_num)
theorem B3849445 : Blo 818347 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B1228013 : Blo 818347 1228013 := bbase (se 3 (by rfl) ⟨230252, by rfl⟩ : syracuseStep 1228013 = 460505) (by norm_num)
theorem B2079989 : Blo 818347 2079989 := bbase (se 5 (by rfl) ⟨97499, by rfl⟩ : syracuseStep 2079989 = 194999) (by norm_num)
theorem B1228037 : Blo 818347 1228037 := bbase (se 4 (by rfl) ⟨115128, by rfl⟩ : syracuseStep 1228037 = 230257) (by norm_num)
theorem B1228061 : Blo 818347 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B1228085 : Blo 818347 1228085 := bbase (se 5 (by rfl) ⟨57566, by rfl⟩ : syracuseStep 1228085 = 115133) (by norm_num)
theorem B1228109 : Blo 818347 1228109 := bbase (se 3 (by rfl) ⟨230270, by rfl⟩ : syracuseStep 1228109 = 460541) (by norm_num)
theorem B1228133 : Blo 818347 1228133 := bbase (se 4 (by rfl) ⟨115137, by rfl⟩ : syracuseStep 1228133 = 230275) (by norm_num)
theorem B1752437 : Blo 818347 1752437 := bbase (se 5 (by rfl) ⟨82145, by rfl⟩ : syracuseStep 1752437 = 164291) (by norm_num)
theorem B1228157 : Blo 818347 1228157 := bbase (se 3 (by rfl) ⟨230279, by rfl⟩ : syracuseStep 1228157 = 460559) (by norm_num)
theorem B1228181 : Blo 818347 1228181 := bbase (se 6 (by rfl) ⟨28785, by rfl⟩ : syracuseStep 1228181 = 57571) (by norm_num)
theorem B1555861 : Blo 818347 1555861 := bbase (se 6 (by rfl) ⟨36465, by rfl⟩ : syracuseStep 1555861 = 72931) (by norm_num)
theorem B1228205 : Blo 818347 1228205 := bbase (se 3 (by rfl) ⟨230288, by rfl⟩ : syracuseStep 1228205 = 460577) (by norm_num)
theorem B2768309 : Blo 818347 2768309 := bbase (se 5 (by rfl) ⟨129764, by rfl⟩ : syracuseStep 2768309 = 259529) (by norm_num)
theorem B2080181 : Blo 818347 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B1228229 : Blo 818347 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B1228253 : Blo 818347 1228253 := bbase (se 3 (by rfl) ⟨230297, by rfl⟩ : syracuseStep 1228253 = 460595) (by norm_num)
theorem B1228277 : Blo 818347 1228277 := bbase (se 5 (by rfl) ⟨57575, by rfl⟩ : syracuseStep 1228277 = 115151) (by norm_num)
theorem B1228301 : Blo 818347 1228301 := bbase (se 3 (by rfl) ⟨230306, by rfl⟩ : syracuseStep 1228301 = 460613) (by norm_num)
theorem B1228325 : Blo 818347 1228325 := bbase (se 4 (by rfl) ⟨115155, by rfl⟩ : syracuseStep 1228325 = 230311) (by norm_num)
theorem B1556005 : Blo 818347 1556005 := bbase (se 4 (by rfl) ⟨145875, by rfl⟩ : syracuseStep 1556005 = 291751) (by norm_num)
theorem B1228349 : Blo 818347 1228349 := bbase (se 3 (by rfl) ⟨230315, by rfl⟩ : syracuseStep 1228349 = 460631) (by norm_num)
theorem B933445 : Blo 818347 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B1228373 : Blo 818347 1228373 := bbase (se 8 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 1228373 = 14395) (by norm_num)
theorem B1228397 : Blo 818347 1228397 := bbase (se 3 (by rfl) ⟨230324, by rfl⟩ : syracuseStep 1228397 = 460649) (by norm_num)
theorem B1228421 : Blo 818347 1228421 := bbase (se 4 (by rfl) ⟨115164, by rfl⟩ : syracuseStep 1228421 = 230329) (by norm_num)
theorem B933517 : Blo 818347 933517 := bbase (se 3 (by rfl) ⟨175034, by rfl⟩ : syracuseStep 933517 = 350069) (by norm_num)
theorem B1228445 : Blo 818347 1228445 := bbase (se 3 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 1228445 = 460667) (by norm_num)
theorem B1228469 : Blo 818347 1228469 := bbase (se 5 (by rfl) ⟨57584, by rfl⟩ : syracuseStep 1228469 = 115169) (by norm_num)
theorem B4669109 : Blo 818347 4669109 := bbase (se 5 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 4669109 = 437729) (by norm_num)
theorem B1556165 : Blo 818347 1556165 := bbase (se 4 (by rfl) ⟨145890, by rfl⟩ : syracuseStep 1556165 = 291781) (by norm_num)
theorem B1228493 : Blo 818347 1228493 := bbase (se 3 (by rfl) ⟨230342, by rfl⟩ : syracuseStep 1228493 = 460685) (by norm_num)
theorem B1228517 : Blo 818347 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B1228541 : Blo 818347 1228541 := bbase (se 3 (by rfl) ⟨230351, by rfl⟩ : syracuseStep 1228541 = 460703) (by norm_num)
theorem B2080525 : Blo 818347 2080525 := bbase (se 3 (by rfl) ⟨390098, by rfl⟩ : syracuseStep 2080525 = 780197) (by norm_num)
theorem B2801429 : Blo 818347 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1228565 : Blo 818347 1228565 := bbase (se 6 (by rfl) ⟨28794, by rfl⟩ : syracuseStep 1228565 = 57589) (by norm_num)
theorem B1228589 : Blo 818347 1228589 := bbase (se 3 (by rfl) ⟨230360, by rfl⟩ : syracuseStep 1228589 = 460721) (by norm_num)
theorem B1228613 : Blo 818347 1228613 := bbase (se 4 (by rfl) ⟨115182, by rfl⟩ : syracuseStep 1228613 = 230365) (by norm_num)
theorem B1556309 : Blo 818347 1556309 := bbase (se 9 (by rfl) ⟨4559, by rfl⟩ : syracuseStep 1556309 = 9119) (by norm_num)
theorem B1228637 : Blo 818347 1228637 := bbase (se 3 (by rfl) ⟨230369, by rfl⟩ : syracuseStep 1228637 = 460739) (by norm_num)
theorem B2768741 : Blo 818347 2768741 := bbase (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) (by norm_num)
theorem B1752941 : Blo 818347 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B3030901 : Blo 818347 3030901 := bbase (se 5 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 3030901 = 284147) (by norm_num)
theorem B1228661 : Blo 818347 1228661 := bbase (se 5 (by rfl) ⟨57593, by rfl⟩ : syracuseStep 1228661 = 115187) (by norm_num)
theorem B1752949 : Blo 818347 1752949 := bbase (se 5 (by rfl) ⟨82169, by rfl⟩ : syracuseStep 1752949 = 164339) (by norm_num)
theorem B2080637 : Blo 818347 2080637 := bbase (se 3 (by rfl) ⟨390119, by rfl⟩ : syracuseStep 2080637 = 780239) (by norm_num)
theorem B1228685 : Blo 818347 1228685 := bbase (se 3 (by rfl) ⟨230378, by rfl⟩ : syracuseStep 1228685 = 460757) (by norm_num)
theorem B933773 : Blo 818347 933773 := bbase (se 3 (by rfl) ⟨175082, by rfl⟩ : syracuseStep 933773 = 350165) (by norm_num)
theorem B1228709 : Blo 818347 1228709 := bbase (se 4 (by rfl) ⟨115191, by rfl⟩ : syracuseStep 1228709 = 230383) (by norm_num)
theorem B1228733 : Blo 818347 1228733 := bbase (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) (by norm_num)
theorem B4145093 : Blo 818347 4145093 := bbase (se 4 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 4145093 = 777205) (by norm_num)
theorem B1228757 : Blo 818347 1228757 := bbase (se 7 (by rfl) ⟨14399, by rfl⟩ : syracuseStep 1228757 = 28799) (by norm_num)
theorem B1228781 : Blo 818347 1228781 := bbase (se 3 (by rfl) ⟨230396, by rfl⟩ : syracuseStep 1228781 = 460793) (by norm_num)
theorem B1228805 : Blo 818347 1228805 := bbase (se 4 (by rfl) ⟨115200, by rfl⟩ : syracuseStep 1228805 = 230401) (by norm_num)
theorem B1228829 : Blo 818347 1228829 := bbase (se 3 (by rfl) ⟨230405, by rfl⟩ : syracuseStep 1228829 = 460811) (by norm_num)
theorem B1228853 : Blo 818347 1228853 := bbase (se 5 (by rfl) ⟨57602, by rfl⟩ : syracuseStep 1228853 = 115205) (by norm_num)
theorem B2080829 : Blo 818347 2080829 := bbase (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) (by norm_num)
theorem B1228877 : Blo 818347 1228877 := bbase (se 3 (by rfl) ⟨230414, by rfl⟩ : syracuseStep 1228877 = 460829) (by norm_num)
theorem B1228901 : Blo 818347 1228901 := bbase (se 4 (by rfl) ⟨115209, by rfl⟩ : syracuseStep 1228901 = 230419) (by norm_num)
theorem B1556597 : Blo 818347 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B1228925 : Blo 818347 1228925 := bbase (se 3 (by rfl) ⟨230423, by rfl⟩ : syracuseStep 1228925 = 460847) (by norm_num)
theorem B1228949 : Blo 818347 1228949 := bbase (se 6 (by rfl) ⟨28803, by rfl⟩ : syracuseStep 1228949 = 57607) (by norm_num)
theorem B1228973 : Blo 818347 1228973 := bbase (se 3 (by rfl) ⟨230432, by rfl⟩ : syracuseStep 1228973 = 460865) (by norm_num)
theorem B1228997 : Blo 818347 1228997 := bbase (se 4 (by rfl) ⟨115218, by rfl⟩ : syracuseStep 1228997 = 230437) (by norm_num)
theorem B1229021 : Blo 818347 1229021 := bbase (se 3 (by rfl) ⟨230441, by rfl⟩ : syracuseStep 1229021 = 460883) (by norm_num)
theorem B1229045 : Blo 818347 1229045 := bbase (se 5 (by rfl) ⟨57611, by rfl⟩ : syracuseStep 1229045 = 115223) (by norm_num)
theorem B1229069 : Blo 818347 1229069 := bbase (se 3 (by rfl) ⟨230450, by rfl⟩ : syracuseStep 1229069 = 460901) (by norm_num)
theorem B1556749 : Blo 818347 1556749 := bbase (se 3 (by rfl) ⟨291890, by rfl⟩ : syracuseStep 1556749 = 583781) (by norm_num)
theorem B2769173 : Blo 818347 2769173 := bbase (se 6 (by rfl) ⟨64902, by rfl⟩ : syracuseStep 2769173 = 129805) (by norm_num)
theorem B1229093 : Blo 818347 1229093 := bbase (se 4 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 1229093 = 230455) (by norm_num)
theorem B1229117 : Blo 818347 1229117 := bbase (se 3 (by rfl) ⟨230459, by rfl⟩ : syracuseStep 1229117 = 460919) (by norm_num)
theorem B1229141 : Blo 818347 1229141 := bbase (se 10 (by rfl) ⟨1800, by rfl⟩ : syracuseStep 1229141 = 3601) (by norm_num)
theorem B3326309 : Blo 818347 3326309 := bbase (se 4 (by rfl) ⟨311841, by rfl⟩ : syracuseStep 3326309 = 623683) (by norm_num)
theorem B1229165 : Blo 818347 1229165 := bbase (se 3 (by rfl) ⟨230468, by rfl⟩ : syracuseStep 1229165 = 460937) (by norm_num)
theorem B1229189 : Blo 818347 1229189 := bbase (se 4 (by rfl) ⟨115236, by rfl⟩ : syracuseStep 1229189 = 230473) (by norm_num)
theorem B2245013 : Blo 818347 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B2081173 : Blo 818347 2081173 := bbase (se 6 (by rfl) ⟨48777, by rfl⟩ : syracuseStep 2081173 = 97555) (by norm_num)
theorem B1229213 : Blo 818347 1229213 := bbase (se 3 (by rfl) ⟨230477, by rfl⟩ : syracuseStep 1229213 = 460955) (by norm_num)
theorem B1229237 : Blo 818347 1229237 := bbase (se 5 (by rfl) ⟨57620, by rfl⟩ : syracuseStep 1229237 = 115241) (by norm_num)
theorem B1229261 : Blo 818347 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B934357 : Blo 818347 934357 := bbase (se 7 (by rfl) ⟨10949, by rfl⟩ : syracuseStep 934357 = 21899) (by norm_num)
theorem B10961365 : Blo 818347 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B1229285 : Blo 818347 1229285 := bbase (se 4 (by rfl) ⟨115245, by rfl⟩ : syracuseStep 1229285 = 230491) (by norm_num)
theorem B1229309 : Blo 818347 1229309 := bbase (se 3 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 1229309 = 460991) (by norm_num)
theorem B2081285 : Blo 818347 2081285 := bbase (se 4 (by rfl) ⟨195120, by rfl⟩ : syracuseStep 2081285 = 390241) (by norm_num)
theorem B1229333 : Blo 818347 1229333 := bbase (se 6 (by rfl) ⟨28812, by rfl⟩ : syracuseStep 1229333 = 57625) (by norm_num)
theorem B1229357 : Blo 818347 1229357 := bbase (se 3 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 1229357 = 461009) (by norm_num)
theorem B1557053 : Blo 818347 1557053 := bbase (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) (by norm_num)
theorem B1229381 : Blo 818347 1229381 := bbase (se 4 (by rfl) ⟨115254, by rfl⟩ : syracuseStep 1229381 = 230509) (by norm_num)
theorem B1229405 : Blo 818347 1229405 := bbase (se 3 (by rfl) ⟨230513, by rfl⟩ : syracuseStep 1229405 = 461027) (by norm_num)
theorem B1229429 : Blo 818347 1229429 := bbase (se 5 (by rfl) ⟨57629, by rfl⟩ : syracuseStep 1229429 = 115259) (by norm_num)
theorem B1229453 : Blo 818347 1229453 := bbase (se 3 (by rfl) ⟨230522, by rfl⟩ : syracuseStep 1229453 = 461045) (by norm_num)
theorem B1229477 : Blo 818347 1229477 := bbase (se 4 (by rfl) ⟨115263, by rfl⟩ : syracuseStep 1229477 = 230527) (by norm_num)
theorem B1229501 : Blo 818347 1229501 := bbase (se 3 (by rfl) ⟨230531, by rfl⟩ : syracuseStep 1229501 = 461063) (by norm_num)
theorem B2769605 : Blo 818347 2769605 := bbase (se 4 (by rfl) ⟨259650, by rfl⟩ : syracuseStep 2769605 = 519301) (by norm_num)
theorem B2081477 : Blo 818347 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B1229525 : Blo 818347 1229525 := bbase (se 7 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 1229525 = 28817) (by norm_num)
theorem B1229549 : Blo 818347 1229549 := bbase (se 3 (by rfl) ⟨230540, by rfl⟩ : syracuseStep 1229549 = 461081) (by norm_num)
theorem B1229573 : Blo 818347 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B1229597 : Blo 818347 1229597 := bbase (se 3 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 1229597 = 461099) (by norm_num)
theorem B1229621 : Blo 818347 1229621 := bbase (se 5 (by rfl) ⟨57638, by rfl⟩ : syracuseStep 1229621 = 115277) (by norm_num)
theorem B1229645 : Blo 818347 1229645 := bbase (se 3 (by rfl) ⟨230558, by rfl⟩ : syracuseStep 1229645 = 461117) (by norm_num)
theorem B1229669 : Blo 818347 1229669 := bbase (se 4 (by rfl) ⟨115281, by rfl⟩ : syracuseStep 1229669 = 230563) (by norm_num)
theorem B1229693 : Blo 818347 1229693 := bbase (se 3 (by rfl) ⟨230567, by rfl⟩ : syracuseStep 1229693 = 461135) (by norm_num)
theorem B1229717 : Blo 818347 1229717 := bbase (se 6 (by rfl) ⟨28821, by rfl⟩ : syracuseStep 1229717 = 57643) (by norm_num)
theorem B1229741 : Blo 818347 1229741 := bbase (se 3 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 1229741 = 461153) (by norm_num)
theorem B1229765 : Blo 818347 1229765 := bbase (se 4 (by rfl) ⟨115290, by rfl⟩ : syracuseStep 1229765 = 230581) (by norm_num)
theorem B1229789 : Blo 818347 1229789 := bbase (se 3 (by rfl) ⟨230585, by rfl⟩ : syracuseStep 1229789 = 461171) (by norm_num)
theorem B1754077 : Blo 818347 1754077 := bbase (se 3 (by rfl) ⟨328889, by rfl⟩ : syracuseStep 1754077 = 657779) (by norm_num)
theorem B1229813 : Blo 818347 1229813 := bbase (se 5 (by rfl) ⟨57647, by rfl⟩ : syracuseStep 1229813 = 115295) (by norm_num)
theorem B1229837 : Blo 818347 1229837 := bbase (se 3 (by rfl) ⟨230594, by rfl⟩ : syracuseStep 1229837 = 461189) (by norm_num)
theorem B1229861 : Blo 818347 1229861 := bbase (se 4 (by rfl) ⟨115299, by rfl⟩ : syracuseStep 1229861 = 230599) (by norm_num)
theorem B1229885 : Blo 818347 1229885 := bbase (se 3 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 1229885 = 461207) (by norm_num)
theorem B1229909 : Blo 818347 1229909 := bbase (se 8 (by rfl) ⟨7206, by rfl⟩ : syracuseStep 1229909 = 14413) (by norm_num)
theorem B1229933 : Blo 818347 1229933 := bbase (se 3 (by rfl) ⟨230612, by rfl⟩ : syracuseStep 1229933 = 461225) (by norm_num)
theorem B2770037 : Blo 818347 2770037 := bbase (se 5 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 2770037 = 259691) (by norm_num)
theorem B1229957 : Blo 818347 1229957 := bbase (se 4 (by rfl) ⟨115308, by rfl⟩ : syracuseStep 1229957 = 230617) (by norm_num)
theorem B1229981 : Blo 818347 1229981 := bbase (se 3 (by rfl) ⟨230621, by rfl⟩ : syracuseStep 1229981 = 461243) (by norm_num)
theorem B1230005 : Blo 818347 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B1230029 : Blo 818347 1230029 := bbase (se 3 (by rfl) ⟨230630, by rfl⟩ : syracuseStep 1230029 = 461261) (by norm_num)
theorem B4146389 : Blo 818347 4146389 := bbase (se 7 (by rfl) ⟨48590, by rfl⟩ : syracuseStep 4146389 = 97181) (by norm_num)
theorem B1230053 : Blo 818347 1230053 := bbase (se 4 (by rfl) ⟨115317, by rfl⟩ : syracuseStep 1230053 = 230635) (by norm_num)
theorem B1230077 : Blo 818347 1230077 := bbase (se 3 (by rfl) ⟨230639, by rfl⟩ : syracuseStep 1230077 = 461279) (by norm_num)
theorem B1230101 : Blo 818347 1230101 := bbase (se 6 (by rfl) ⟨28830, by rfl⟩ : syracuseStep 1230101 = 57661) (by norm_num)
theorem B1230125 : Blo 818347 1230125 := bbase (se 3 (by rfl) ⟨230648, by rfl⟩ : syracuseStep 1230125 = 461297) (by norm_num)
theorem B1557805 : Blo 818347 1557805 := bbase (se 3 (by rfl) ⟨292088, by rfl⟩ : syracuseStep 1557805 = 584177) (by norm_num)
theorem B1230149 : Blo 818347 1230149 := bbase (se 4 (by rfl) ⟨115326, by rfl⟩ : syracuseStep 1230149 = 230653) (by norm_num)
theorem B1754453 : Blo 818347 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B1230173 : Blo 818347 1230173 := bbase (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) (by norm_num)
theorem B2213237 : Blo 818347 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B1230197 : Blo 818347 1230197 := bbase (se 5 (by rfl) ⟨57665, by rfl⟩ : syracuseStep 1230197 = 115331) (by norm_num)
theorem B1230221 : Blo 818347 1230221 := bbase (se 3 (by rfl) ⟨230666, by rfl⟩ : syracuseStep 1230221 = 461333) (by norm_num)
theorem B1230245 : Blo 818347 1230245 := bbase (se 4 (by rfl) ⟨115335, by rfl⟩ : syracuseStep 1230245 = 230671) (by norm_num)
theorem B1230269 : Blo 818347 1230269 := bbase (se 3 (by rfl) ⟨230675, by rfl⟩ : syracuseStep 1230269 = 461351) (by norm_num)
theorem B1557949 : Blo 818347 1557949 := bbase (se 3 (by rfl) ⟨292115, by rfl⟩ : syracuseStep 1557949 = 584231) (by norm_num)
theorem B1230293 : Blo 818347 1230293 := bbase (se 7 (by rfl) ⟨14417, by rfl⟩ : syracuseStep 1230293 = 28835) (by norm_num)
theorem B1230317 : Blo 818347 1230317 := bbase (se 3 (by rfl) ⟨230684, by rfl⟩ : syracuseStep 1230317 = 461369) (by norm_num)
theorem B1230341 : Blo 818347 1230341 := bbase (se 4 (by rfl) ⟨115344, by rfl⟩ : syracuseStep 1230341 = 230689) (by norm_num)
theorem B1230365 : Blo 818347 1230365 := bbase (se 3 (by rfl) ⟨230693, by rfl⟩ : syracuseStep 1230365 = 461387) (by norm_num)
theorem B2770469 : Blo 818347 2770469 := bbase (se 4 (by rfl) ⟨259731, by rfl⟩ : syracuseStep 2770469 = 519463) (by norm_num)
theorem B3950117 : Blo 818347 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B1230389 : Blo 818347 1230389 := bbase (se 5 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 1230389 = 115349) (by norm_num)
theorem B1230413 : Blo 818347 1230413 := bbase (se 3 (by rfl) ⟨230702, by rfl⟩ : syracuseStep 1230413 = 461405) (by norm_num)
theorem B1558109 : Blo 818347 1558109 := bbase (se 3 (by rfl) ⟨292145, by rfl⟩ : syracuseStep 1558109 = 584291) (by norm_num)
theorem B1230437 : Blo 818347 1230437 := bbase (se 4 (by rfl) ⟨115353, by rfl⟩ : syracuseStep 1230437 = 230707) (by norm_num)
theorem B1230461 : Blo 818347 1230461 := bbase (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) (by norm_num)
theorem B1230485 : Blo 818347 1230485 := bbase (se 6 (by rfl) ⟨28839, by rfl⟩ : syracuseStep 1230485 = 57679) (by norm_num)
theorem B1230509 : Blo 818347 1230509 := bbase (se 3 (by rfl) ⟨230720, by rfl⟩ : syracuseStep 1230509 = 461441) (by norm_num)
theorem B1230533 : Blo 818347 1230533 := bbase (se 4 (by rfl) ⟨115362, by rfl⟩ : syracuseStep 1230533 = 230725) (by norm_num)
theorem B1230557 : Blo 818347 1230557 := bbase (se 3 (by rfl) ⟨230729, by rfl⟩ : syracuseStep 1230557 = 461459) (by norm_num)
theorem B1558253 : Blo 818347 1558253 := bbase (se 3 (by rfl) ⟨292172, by rfl⟩ : syracuseStep 1558253 = 584345) (by norm_num)
theorem B1230581 : Blo 818347 1230581 := bbase (se 5 (by rfl) ⟨57683, by rfl⟩ : syracuseStep 1230581 = 115367) (by norm_num)
theorem B1230605 : Blo 818347 1230605 := bbase (se 3 (by rfl) ⟨230738, by rfl⟩ : syracuseStep 1230605 = 461477) (by norm_num)
theorem B1230629 : Blo 818347 1230629 := bbase (se 4 (by rfl) ⟨115371, by rfl⟩ : syracuseStep 1230629 = 230743) (by norm_num)
theorem B935717 : Blo 818347 935717 := bbase (se 4 (by rfl) ⟨87723, by rfl⟩ : syracuseStep 935717 = 175447) (by norm_num)
theorem B1230653 : Blo 818347 1230653 := bbase (se 3 (by rfl) ⟨230747, by rfl⟩ : syracuseStep 1230653 = 461495) (by norm_num)
theorem B1230677 : Blo 818347 1230677 := bbase (se 9 (by rfl) ⟨3605, by rfl⟩ : syracuseStep 1230677 = 7211) (by norm_num)
theorem B1230701 : Blo 818347 1230701 := bbase (se 3 (by rfl) ⟨230756, by rfl⟩ : syracuseStep 1230701 = 461513) (by norm_num)
theorem B1230725 : Blo 818347 1230725 := bbase (se 4 (by rfl) ⟨115380, by rfl⟩ : syracuseStep 1230725 = 230761) (by norm_num)
theorem B1230749 : Blo 818347 1230749 := bbase (se 3 (by rfl) ⟨230765, by rfl⟩ : syracuseStep 1230749 = 461531) (by norm_num)
theorem B1230773 : Blo 818347 1230773 := bbase (se 5 (by rfl) ⟨57692, by rfl⟩ : syracuseStep 1230773 = 115385) (by norm_num)
theorem B1165261 : Blo 818347 1165261 := bbase (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) (by norm_num)
theorem B1230797 : Blo 818347 1230797 := bbase (se 3 (by rfl) ⟨230774, by rfl⟩ : syracuseStep 1230797 = 461549) (by norm_num)
theorem B2770901 : Blo 818347 2770901 := bbase (se 7 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 2770901 = 64943) (by norm_num)
theorem B1230821 : Blo 818347 1230821 := bbase (se 4 (by rfl) ⟨115389, by rfl⟩ : syracuseStep 1230821 = 230779) (by norm_num)
theorem B1230845 : Blo 818347 1230845 := bbase (se 3 (by rfl) ⟨230783, by rfl⟩ : syracuseStep 1230845 = 461567) (by norm_num)
theorem B1558541 : Blo 818347 1558541 := bbase (se 3 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 1558541 = 584453) (by norm_num)
theorem B1230869 : Blo 818347 1230869 := bbase (se 6 (by rfl) ⟨28848, by rfl⟩ : syracuseStep 1230869 = 57697) (by norm_num)
theorem B1230893 : Blo 818347 1230893 := bbase (se 3 (by rfl) ⟨230792, by rfl⟩ : syracuseStep 1230893 = 461585) (by norm_num)
theorem B5916725 : Blo 818347 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B1230917 : Blo 818347 1230917 := bbase (se 4 (by rfl) ⟨115398, by rfl⟩ : syracuseStep 1230917 = 230797) (by norm_num)
theorem B1230941 : Blo 818347 1230941 := bbase (se 3 (by rfl) ⟨230801, by rfl⟩ : syracuseStep 1230941 = 461603) (by norm_num)
theorem B1230965 : Blo 818347 1230965 := bbase (se 5 (by rfl) ⟨57701, by rfl⟩ : syracuseStep 1230965 = 115403) (by norm_num)
theorem B1230989 : Blo 818347 1230989 := bbase (se 3 (by rfl) ⟨230810, by rfl⟩ : syracuseStep 1230989 = 461621) (by norm_num)
theorem B1231013 : Blo 818347 1231013 := bbase (se 4 (by rfl) ⟨115407, by rfl⟩ : syracuseStep 1231013 = 230815) (by norm_num)
theorem B1558693 : Blo 818347 1558693 := bbase (se 4 (by rfl) ⟨146127, by rfl⟩ : syracuseStep 1558693 = 292255) (by norm_num)
theorem B1231037 : Blo 818347 1231037 := bbase (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) (by norm_num)
theorem B1231061 : Blo 818347 1231061 := bbase (se 7 (by rfl) ⟨14426, by rfl⟩ : syracuseStep 1231061 = 28853) (by norm_num)
theorem B1231085 : Blo 818347 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B1231109 : Blo 818347 1231109 := bbase (se 4 (by rfl) ⟨115416, by rfl⟩ : syracuseStep 1231109 = 230833) (by norm_num)
theorem B1231133 : Blo 818347 1231133 := bbase (se 3 (by rfl) ⟨230837, by rfl⟩ : syracuseStep 1231133 = 461675) (by norm_num)
theorem B1231157 : Blo 818347 1231157 := bbase (se 5 (by rfl) ⟨57710, by rfl⟩ : syracuseStep 1231157 = 115421) (by norm_num)
theorem B1165637 : Blo 818347 1165637 := bbase (se 4 (by rfl) ⟨109278, by rfl⟩ : syracuseStep 1165637 = 218557) (by norm_num)
theorem B1231181 : Blo 818347 1231181 := bbase (se 3 (by rfl) ⟨230846, by rfl⟩ : syracuseStep 1231181 = 461693) (by norm_num)
theorem B1231205 : Blo 818347 1231205 := bbase (se 4 (by rfl) ⟨115425, by rfl⟩ : syracuseStep 1231205 = 230851) (by norm_num)
theorem B1231229 : Blo 818347 1231229 := bbase (se 3 (by rfl) ⟨230855, by rfl⟩ : syracuseStep 1231229 = 461711) (by norm_num)
theorem B2771333 : Blo 818347 2771333 := bbase (se 4 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 2771333 = 519625) (by norm_num)
theorem B1231253 : Blo 818347 1231253 := bbase (se 6 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 1231253 = 57715) (by norm_num)
theorem B1231277 : Blo 818347 1231277 := bbase (se 3 (by rfl) ⟨230864, by rfl⟩ : syracuseStep 1231277 = 461729) (by norm_num)
theorem B1231301 : Blo 818347 1231301 := bbase (se 4 (by rfl) ⟨115434, by rfl⟩ : syracuseStep 1231301 = 230869) (by norm_num)
theorem B1558997 : Blo 818347 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B1231325 : Blo 818347 1231325 := bbase (se 3 (by rfl) ⟨230873, by rfl⟩ : syracuseStep 1231325 = 461747) (by norm_num)
theorem B4147685 : Blo 818347 4147685 := bbase (se 4 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 4147685 = 777691) (by norm_num)
theorem B1231349 : Blo 818347 1231349 := bbase (se 5 (by rfl) ⟨57719, by rfl⟩ : syracuseStep 1231349 = 115439) (by norm_num)
theorem B1231373 : Blo 818347 1231373 := bbase (se 3 (by rfl) ⟨230882, by rfl⟩ : syracuseStep 1231373 = 461765) (by norm_num)
theorem B1231397 : Blo 818347 1231397 := bbase (se 4 (by rfl) ⟨115443, by rfl⟩ : syracuseStep 1231397 = 230887) (by norm_num)
theorem B1231421 : Blo 818347 1231421 := bbase (se 3 (by rfl) ⟨230891, by rfl⟩ : syracuseStep 1231421 = 461783) (by norm_num)
theorem B2214469 : Blo 818347 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B1231445 : Blo 818347 1231445 := bbase (se 8 (by rfl) ⟨7215, by rfl⟩ : syracuseStep 1231445 = 14431) (by norm_num)
theorem B1231469 : Blo 818347 1231469 := bbase (se 3 (by rfl) ⟨230900, by rfl⟩ : syracuseStep 1231469 = 461801) (by norm_num)
theorem B1231493 : Blo 818347 1231493 := bbase (se 4 (by rfl) ⟨115452, by rfl⟩ : syracuseStep 1231493 = 230905) (by norm_num)
theorem B1231517 : Blo 818347 1231517 := bbase (se 3 (by rfl) ⟨230909, by rfl⟩ : syracuseStep 1231517 = 461819) (by norm_num)
theorem B1231541 : Blo 818347 1231541 := bbase (se 5 (by rfl) ⟨57728, by rfl⟩ : syracuseStep 1231541 = 115457) (by norm_num)
theorem B1231565 : Blo 818347 1231565 := bbase (se 3 (by rfl) ⟨230918, by rfl⟩ : syracuseStep 1231565 = 461837) (by norm_num)
theorem B1231589 : Blo 818347 1231589 := bbase (se 4 (by rfl) ⟨115461, by rfl⟩ : syracuseStep 1231589 = 230923) (by norm_num)
theorem B1231613 : Blo 818347 1231613 := bbase (se 3 (by rfl) ⟨230927, by rfl⟩ : syracuseStep 1231613 = 461855) (by norm_num)
theorem B1231637 : Blo 818347 1231637 := bbase (se 6 (by rfl) ⟨28866, by rfl⟩ : syracuseStep 1231637 = 57733) (by norm_num)
theorem B1231661 : Blo 818347 1231661 := bbase (se 3 (by rfl) ⟨230936, by rfl⟩ : syracuseStep 1231661 = 461873) (by norm_num)
theorem B5327669 : Blo 818347 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B2771765 : Blo 818347 2771765 := bbase (se 5 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 2771765 = 259853) (by norm_num)
theorem B1231685 : Blo 818347 1231685 := bbase (se 4 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 1231685 = 230941) (by norm_num)
theorem B1231709 : Blo 818347 1231709 := bbase (se 3 (by rfl) ⟨230945, by rfl⟩ : syracuseStep 1231709 = 461891) (by norm_num)
theorem B1231733 : Blo 818347 1231733 := bbase (se 5 (by rfl) ⟨57737, by rfl⟩ : syracuseStep 1231733 = 115475) (by norm_num)
theorem B1231757 : Blo 818347 1231757 := bbase (se 3 (by rfl) ⟨230954, by rfl⟩ : syracuseStep 1231757 = 461909) (by norm_num)
theorem B1231781 : Blo 818347 1231781 := bbase (se 4 (by rfl) ⟨115479, by rfl⟩ : syracuseStep 1231781 = 230959) (by norm_num)
theorem B1231805 : Blo 818347 1231805 := bbase (se 3 (by rfl) ⟨230963, by rfl⟩ : syracuseStep 1231805 = 461927) (by norm_num)
theorem B1756093 : Blo 818347 1756093 := bbase (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) (by norm_num)
theorem B1231829 : Blo 818347 1231829 := bbase (se 7 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 1231829 = 28871) (by norm_num)
theorem B1231853 : Blo 818347 1231853 := bbase (se 3 (by rfl) ⟨230972, by rfl⟩ : syracuseStep 1231853 = 461945) (by norm_num)
theorem B1231877 : Blo 818347 1231877 := bbase (se 4 (by rfl) ⟨115488, by rfl⟩ : syracuseStep 1231877 = 230977) (by norm_num)
theorem B1231901 : Blo 818347 1231901 := bbase (se 3 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 1231901 = 461963) (by norm_num)
theorem B1231925 : Blo 818347 1231925 := bbase (se 5 (by rfl) ⟨57746, by rfl⟩ : syracuseStep 1231925 = 115493) (by norm_num)
theorem B937021 : Blo 818347 937021 := bbase (se 3 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 937021 = 351383) (by norm_num)
theorem B1231949 : Blo 818347 1231949 := bbase (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) (by norm_num)
theorem B1231973 : Blo 818347 1231973 := bbase (se 4 (by rfl) ⟨115497, by rfl⟩ : syracuseStep 1231973 = 230995) (by norm_num)
theorem B1231997 : Blo 818347 1231997 := bbase (se 3 (by rfl) ⟨230999, by rfl⟩ : syracuseStep 1231997 = 461999) (by norm_num)
theorem B1068169 : Blo 818347 1068169 := bbase (se 2 (by rfl) ⟨400563, by rfl⟩ : syracuseStep 1068169 = 801127) (by norm_num)
theorem B1232021 : Blo 818347 1232021 := bbase (se 6 (by rfl) ⟨28875, by rfl⟩ : syracuseStep 1232021 = 57751) (by norm_num)
theorem B1232045 : Blo 818347 1232045 := bbase (se 3 (by rfl) ⟨231008, by rfl⟩ : syracuseStep 1232045 = 462017) (by norm_num)
theorem B1232069 : Blo 818347 1232069 := bbase (se 4 (by rfl) ⟨115506, by rfl⟩ : syracuseStep 1232069 = 231013) (by norm_num)
theorem B1559749 : Blo 818347 1559749 := bbase (se 4 (by rfl) ⟨146226, by rfl⟩ : syracuseStep 1559749 = 292453) (by norm_num)
theorem B1232093 : Blo 818347 1232093 := bbase (se 3 (by rfl) ⟨231017, by rfl⟩ : syracuseStep 1232093 = 462035) (by norm_num)
theorem B2772197 : Blo 818347 2772197 := bbase (se 4 (by rfl) ⟨259893, by rfl⟩ : syracuseStep 2772197 = 519787) (by norm_num)
theorem B1232117 : Blo 818347 1232117 := bbase (se 5 (by rfl) ⟨57755, by rfl⟩ : syracuseStep 1232117 = 115511) (by norm_num)
theorem B1232141 : Blo 818347 1232141 := bbase (se 3 (by rfl) ⟨231026, by rfl⟩ : syracuseStep 1232141 = 462053) (by norm_num)
theorem B1232165 : Blo 818347 1232165 := bbase (se 4 (by rfl) ⟨115515, by rfl⟩ : syracuseStep 1232165 = 231031) (by norm_num)
theorem B1232189 : Blo 818347 1232189 := bbase (se 3 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 1232189 = 462071) (by norm_num)
theorem B1232213 : Blo 818347 1232213 := bbase (se 11 (by rfl) ⟨902, by rfl⟩ : syracuseStep 1232213 = 1805) (by norm_num)
theorem B1559893 : Blo 818347 1559893 := bbase (se 11 (by rfl) ⟨1142, by rfl⟩ : syracuseStep 1559893 = 2285) (by norm_num)
theorem B1232237 : Blo 818347 1232237 := bbase (se 3 (by rfl) ⟨231044, by rfl⟩ : syracuseStep 1232237 = 462089) (by norm_num)
theorem B1232261 : Blo 818347 1232261 := bbase (se 4 (by rfl) ⟨115524, by rfl⟩ : syracuseStep 1232261 = 231049) (by norm_num)
theorem B1232285 : Blo 818347 1232285 := bbase (se 3 (by rfl) ⟨231053, by rfl⟩ : syracuseStep 1232285 = 462107) (by norm_num)
theorem B1232309 : Blo 818347 1232309 := bbase (se 5 (by rfl) ⟨57764, by rfl⟩ : syracuseStep 1232309 = 115529) (by norm_num)
theorem B1068485 : Blo 818347 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B1232333 : Blo 818347 1232333 := bbase (se 3 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 1232333 = 462125) (by norm_num)
theorem B1232357 : Blo 818347 1232357 := bbase (se 4 (by rfl) ⟨115533, by rfl⟩ : syracuseStep 1232357 = 231067) (by norm_num)
theorem B1035757 : Blo 818347 1035757 := bbase (se 3 (by rfl) ⟨194204, by rfl⟩ : syracuseStep 1035757 = 388409) (by norm_num)
theorem B1560053 : Blo 818347 1560053 := bbase (se 5 (by rfl) ⟨73127, by rfl⟩ : syracuseStep 1560053 = 146255) (by norm_num)
theorem B1232381 : Blo 818347 1232381 := bbase (se 3 (by rfl) ⟨231071, by rfl⟩ : syracuseStep 1232381 = 462143) (by norm_num)
theorem B1232405 : Blo 818347 1232405 := bbase (se 6 (by rfl) ⟨28884, by rfl⟩ : syracuseStep 1232405 = 57769) (by norm_num)
theorem B1232429 : Blo 818347 1232429 := bbase (se 3 (by rfl) ⟨231080, by rfl⟩ : syracuseStep 1232429 = 462161) (by norm_num)
theorem B1232453 : Blo 818347 1232453 := bbase (se 4 (by rfl) ⟨115542, by rfl⟩ : syracuseStep 1232453 = 231085) (by norm_num)
theorem B1232477 : Blo 818347 1232477 := bbase (se 3 (by rfl) ⟨231089, by rfl⟩ : syracuseStep 1232477 = 462179) (by norm_num)
theorem B1232501 : Blo 818347 1232501 := bbase (se 5 (by rfl) ⟨57773, by rfl⟩ : syracuseStep 1232501 = 115547) (by norm_num)
theorem B1560197 : Blo 818347 1560197 := bbase (se 4 (by rfl) ⟨146268, by rfl⟩ : syracuseStep 1560197 = 292537) (by norm_num)
theorem B1232525 : Blo 818347 1232525 := bbase (se 3 (by rfl) ⟨231098, by rfl⟩ : syracuseStep 1232525 = 462197) (by norm_num)
theorem B2772629 : Blo 818347 2772629 := bbase (se 6 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 2772629 = 129967) (by norm_num)
theorem B1035929 : Blo 818347 1035929 := bbase (se 2 (by rfl) ⟨388473, by rfl⟩ : syracuseStep 1035929 = 776947) (by norm_num)
theorem B1232549 : Blo 818347 1232549 := bbase (se 4 (by rfl) ⟨115551, by rfl⟩ : syracuseStep 1232549 = 231103) (by norm_num)
theorem B1232573 : Blo 818347 1232573 := bbase (se 3 (by rfl) ⟨231107, by rfl⟩ : syracuseStep 1232573 = 462215) (by norm_num)
theorem B1035985 : Blo 818347 1035985 := bbase (se 2 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 1035985 = 776989) (by norm_num)
theorem B19910357 : Blo 818347 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B1167061 : Blo 818347 1167061 := bbase (se 7 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 1167061 = 27353) (by norm_num)
theorem B2215637 : Blo 818347 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B1232597 : Blo 818347 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B1232621 : Blo 818347 1232621 := bbase (se 3 (by rfl) ⟨231116, by rfl⟩ : syracuseStep 1232621 = 462233) (by norm_num)
theorem B4148981 : Blo 818347 4148981 := bbase (se 5 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 4148981 = 388967) (by norm_num)
theorem B1232645 : Blo 818347 1232645 := bbase (se 4 (by rfl) ⟨115560, by rfl⟩ : syracuseStep 1232645 = 231121) (by norm_num)
theorem B1232669 : Blo 818347 1232669 := bbase (se 3 (by rfl) ⟨231125, by rfl⟩ : syracuseStep 1232669 = 462251) (by norm_num)
theorem B1036081 : Blo 818347 1036081 := bbase (se 2 (by rfl) ⟨388530, by rfl⟩ : syracuseStep 1036081 = 777061) (by norm_num)
theorem B1232693 : Blo 818347 1232693 := bbase (se 5 (by rfl) ⟨57782, by rfl⟩ : syracuseStep 1232693 = 115565) (by norm_num)
theorem B1232717 : Blo 818347 1232717 := bbase (se 3 (by rfl) ⟨231134, by rfl⟩ : syracuseStep 1232717 = 462269) (by norm_num)
theorem B1232741 : Blo 818347 1232741 := bbase (se 4 (by rfl) ⟨115569, by rfl⟩ : syracuseStep 1232741 = 231139) (by norm_num)
theorem B1232765 : Blo 818347 1232765 := bbase (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) (by norm_num)
theorem B1232789 : Blo 818347 1232789 := bbase (se 6 (by rfl) ⟨28893, by rfl⟩ : syracuseStep 1232789 = 57787) (by norm_num)
theorem B1560485 : Blo 818347 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B1232813 : Blo 818347 1232813 := bbase (se 3 (by rfl) ⟨231152, by rfl⟩ : syracuseStep 1232813 = 462305) (by norm_num)
theorem B1232837 : Blo 818347 1232837 := bbase (se 4 (by rfl) ⟨115578, by rfl⟩ : syracuseStep 1232837 = 231157) (by norm_num)
theorem B1036253 : Blo 818347 1036253 := bbase (se 3 (by rfl) ⟨194297, by rfl⟩ : syracuseStep 1036253 = 388595) (by norm_num)
theorem B1232861 : Blo 818347 1232861 := bbase (se 3 (by rfl) ⟨231161, by rfl⟩ : syracuseStep 1232861 = 462323) (by norm_num)
theorem B1232885 : Blo 818347 1232885 := bbase (se 5 (by rfl) ⟨57791, by rfl⟩ : syracuseStep 1232885 = 115583) (by norm_num)
theorem B1232909 : Blo 818347 1232909 := bbase (se 3 (by rfl) ⟨231170, by rfl⟩ : syracuseStep 1232909 = 462341) (by norm_num)
theorem B1036309 : Blo 818347 1036309 := bbase (se 6 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 1036309 = 48577) (by norm_num)
theorem B5918741 : Blo 818347 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B2215973 : Blo 818347 2215973 := bbase (se 4 (by rfl) ⟨207747, by rfl⟩ : syracuseStep 2215973 = 415495) (by norm_num)
theorem B1232933 : Blo 818347 1232933 := bbase (se 4 (by rfl) ⟨115587, by rfl⟩ : syracuseStep 1232933 = 231175) (by norm_num)
theorem B1232957 : Blo 818347 1232957 := bbase (se 3 (by rfl) ⟨231179, by rfl⟩ : syracuseStep 1232957 = 462359) (by norm_num)
theorem B1560637 : Blo 818347 1560637 := bbase (se 3 (by rfl) ⟨292619, by rfl⟩ : syracuseStep 1560637 = 585239) (by norm_num)
theorem B2773061 : Blo 818347 2773061 := bbase (se 4 (by rfl) ⟨259974, by rfl⟩ : syracuseStep 2773061 = 519949) (by norm_num)
theorem B1232981 : Blo 818347 1232981 := bbase (se 8 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 1232981 = 14449) (by norm_num)
theorem B1233005 : Blo 818347 1233005 := bbase (se 3 (by rfl) ⟨231188, by rfl⟩ : syracuseStep 1233005 = 462377) (by norm_num)
theorem B1036405 : Blo 818347 1036405 := bbase (se 5 (by rfl) ⟨48581, by rfl⟩ : syracuseStep 1036405 = 97163) (by norm_num)
theorem B1233029 : Blo 818347 1233029 := bbase (se 4 (by rfl) ⟨115596, by rfl⟩ : syracuseStep 1233029 = 231193) (by norm_num)
theorem B1233053 : Blo 818347 1233053 := bbase (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) (by norm_num)
theorem B5263541 : Blo 818347 5263541 := bbase (se 5 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 5263541 = 493457) (by norm_num)
theorem B1233077 : Blo 818347 1233077 := bbase (se 5 (by rfl) ⟨57800, by rfl⟩ : syracuseStep 1233077 = 115601) (by norm_num)
theorem B1233101 : Blo 818347 1233101 := bbase (se 3 (by rfl) ⟨231206, by rfl⟩ : syracuseStep 1233101 = 462413) (by norm_num)
theorem B1233125 : Blo 818347 1233125 := bbase (se 4 (by rfl) ⟨115605, by rfl⟩ : syracuseStep 1233125 = 231211) (by norm_num)
theorem B1233149 : Blo 818347 1233149 := bbase (se 3 (by rfl) ⟨231215, by rfl⟩ : syracuseStep 1233149 = 462431) (by norm_num)
theorem B1233173 : Blo 818347 1233173 := bbase (se 6 (by rfl) ⟨28902, by rfl⟩ : syracuseStep 1233173 = 57805) (by norm_num)
theorem B1036577 : Blo 818347 1036577 := bbase (se 2 (by rfl) ⟨388716, by rfl⟩ : syracuseStep 1036577 = 777433) (by norm_num)
theorem B1167653 : Blo 818347 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B1233197 : Blo 818347 1233197 := bbase (se 3 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 1233197 = 462449) (by norm_num)
theorem B1233221 : Blo 818347 1233221 := bbase (se 4 (by rfl) ⟨115614, by rfl⟩ : syracuseStep 1233221 = 231229) (by norm_num)
theorem B1036633 : Blo 818347 1036633 := bbase (se 2 (by rfl) ⟨388737, by rfl⟩ : syracuseStep 1036633 = 777475) (by norm_num)
theorem B1233245 : Blo 818347 1233245 := bbase (se 3 (by rfl) ⟨231233, by rfl⟩ : syracuseStep 1233245 = 462467) (by norm_num)
theorem B1560941 : Blo 818347 1560941 := bbase (se 3 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 1560941 = 585353) (by norm_num)
theorem B1167733 : Blo 818347 1167733 := bbase (se 5 (by rfl) ⟨54737, by rfl⟩ : syracuseStep 1167733 = 109475) (by norm_num)
theorem B1233269 : Blo 818347 1233269 := bbase (se 5 (by rfl) ⟨57809, by rfl⟩ : syracuseStep 1233269 = 115619) (by norm_num)
theorem B1233293 : Blo 818347 1233293 := bbase (se 3 (by rfl) ⟨231242, by rfl⟩ : syracuseStep 1233293 = 462485) (by norm_num)
theorem B1233317 : Blo 818347 1233317 := bbase (se 4 (by rfl) ⟨115623, by rfl⟩ : syracuseStep 1233317 = 231247) (by norm_num)
theorem B1036729 : Blo 818347 1036729 := bbase (se 2 (by rfl) ⟨388773, by rfl⟩ : syracuseStep 1036729 = 777547) (by norm_num)
theorem B1233341 : Blo 818347 1233341 := bbase (se 3 (by rfl) ⟨231251, by rfl⟩ : syracuseStep 1233341 = 462503) (by norm_num)
theorem B1233365 : Blo 818347 1233365 := bbase (se 7 (by rfl) ⟨14453, by rfl⟩ : syracuseStep 1233365 = 28907) (by norm_num)
theorem B1167853 : Blo 818347 1167853 := bbase (se 3 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 1167853 = 437945) (by norm_num)
theorem B1233389 : Blo 818347 1233389 := bbase (se 3 (by rfl) ⟨231260, by rfl⟩ : syracuseStep 1233389 = 462521) (by norm_num)
theorem B2773493 : Blo 818347 2773493 := bbase (se 5 (by rfl) ⟨130007, by rfl⟩ : syracuseStep 2773493 = 260015) (by norm_num)
theorem B1233413 : Blo 818347 1233413 := bbase (se 4 (by rfl) ⟨115632, by rfl⟩ : syracuseStep 1233413 = 231265) (by norm_num)
theorem B1233437 : Blo 818347 1233437 := bbase (se 3 (by rfl) ⟨231269, by rfl⟩ : syracuseStep 1233437 = 462539) (by norm_num)
theorem B1233461 : Blo 818347 1233461 := bbase (se 5 (by rfl) ⟨57818, by rfl⟩ : syracuseStep 1233461 = 115637) (by norm_num)
theorem B1167949 : Blo 818347 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B1233485 : Blo 818347 1233485 := bbase (se 3 (by rfl) ⟨231278, by rfl⟩ : syracuseStep 1233485 = 462557) (by norm_num)
theorem B1036901 : Blo 818347 1036901 := bbase (se 4 (by rfl) ⟨97209, by rfl⟩ : syracuseStep 1036901 = 194419) (by norm_num)
theorem B1331813 : Blo 818347 1331813 := bbase (se 4 (by rfl) ⟨124857, by rfl⟩ : syracuseStep 1331813 = 249715) (by norm_num)
theorem B1233509 : Blo 818347 1233509 := bbase (se 4 (by rfl) ⟨115641, by rfl⟩ : syracuseStep 1233509 = 231283) (by norm_num)
theorem B1036957 : Blo 818347 1036957 := bbase (se 3 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 1036957 = 388859) (by norm_num)
theorem B2249461 : Blo 818347 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B1037053 : Blo 818347 1037053 := bbase (se 3 (by rfl) ⟨194447, by rfl⟩ : syracuseStep 1037053 = 388895) (by norm_num)
theorem B1659781 : Blo 818347 1659781 := bbase (se 4 (by rfl) ⟨155604, by rfl⟩ : syracuseStep 1659781 = 311209) (by norm_num)
theorem B2773925 : Blo 818347 2773925 := bbase (se 4 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 2773925 = 520111) (by norm_num)
theorem B1037225 : Blo 818347 1037225 := bbase (se 2 (by rfl) ⟨388959, by rfl⟩ : syracuseStep 1037225 = 777919) (by norm_num)
theorem B1037281 : Blo 818347 1037281 := bbase (se 2 (by rfl) ⟨388980, by rfl⟩ : syracuseStep 1037281 = 777961) (by norm_num)
theorem B4150277 : Blo 818347 4150277 := bbase (se 4 (by rfl) ⟨389088, by rfl⟩ : syracuseStep 4150277 = 778177) (by norm_num)
theorem B1168445 : Blo 818347 1168445 := bbase (se 3 (by rfl) ⟨219083, by rfl⟩ : syracuseStep 1168445 = 438167) (by norm_num)
theorem B1037377 : Blo 818347 1037377 := bbase (se 2 (by rfl) ⟨389016, by rfl⟩ : syracuseStep 1037377 = 778033) (by norm_num)
theorem B2806901 : Blo 818347 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B1037549 : Blo 818347 1037549 := bbase (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) (by norm_num)
theorem B1037605 : Blo 818347 1037605 := bbase (se 4 (by rfl) ⟨97275, by rfl⟩ : syracuseStep 1037605 = 194551) (by norm_num)
theorem B2774357 : Blo 818347 2774357 := bbase (se 16 (by rfl) ⟨63, by rfl⟩ : syracuseStep 2774357 = 127) (by norm_num)
theorem B1037701 : Blo 818347 1037701 := bbase (se 4 (by rfl) ⟨97284, by rfl⟩ : syracuseStep 1037701 = 194569) (by norm_num)
theorem B873929 : Blo 818347 873929 := bbase (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) (by norm_num)
theorem B1037873 : Blo 818347 1037873 := bbase (se 2 (by rfl) ⟨389202, by rfl⟩ : syracuseStep 1037873 = 778405) (by norm_num)
theorem B1168997 : Blo 818347 1168997 := bbase (se 4 (by rfl) ⟨109593, by rfl⟩ : syracuseStep 1168997 = 219187) (by norm_num)
theorem B1037929 : Blo 818347 1037929 := bbase (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) (by norm_num)
theorem B1038025 : Blo 818347 1038025 := bbase (se 2 (by rfl) ⟨389259, by rfl⟩ : syracuseStep 1038025 = 778519) (by norm_num)
theorem B2807557 : Blo 818347 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B2774789 : Blo 818347 2774789 := bbase (se 4 (by rfl) ⟨260136, by rfl⟩ : syracuseStep 2774789 = 520273) (by norm_num)
theorem B1038197 : Blo 818347 1038197 := bbase (se 5 (by rfl) ⟨48665, by rfl⟩ : syracuseStep 1038197 = 97331) (by norm_num)
theorem B874373 : Blo 818347 874373 := bbase (se 4 (by rfl) ⟨81972, by rfl⟩ : syracuseStep 874373 = 163945) (by norm_num)
theorem B1038253 : Blo 818347 1038253 := bbase (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) (by norm_num)
theorem B874433 : Blo 818347 874433 := bbase (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) (by norm_num)
theorem B1038349 : Blo 818347 1038349 := bbase (se 3 (by rfl) ⟨194690, by rfl⟩ : syracuseStep 1038349 = 389381) (by norm_num)
theorem B874561 : Blo 818347 874561 := bbase (se 2 (by rfl) ⟨327960, by rfl⟩ : syracuseStep 874561 = 655921) (by norm_num)
theorem B2775221 : Blo 818347 2775221 := bbase (se 5 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 2775221 = 260177) (by norm_num)
theorem B1038521 : Blo 818347 1038521 := bbase (se 2 (by rfl) ⟨389445, by rfl⟩ : syracuseStep 1038521 = 778891) (by norm_num)
theorem B1038577 : Blo 818347 1038577 := bbase (se 2 (by rfl) ⟨389466, by rfl⟩ : syracuseStep 1038577 = 778933) (by norm_num)
theorem B4151573 : Blo 818347 4151573 := bbase (se 6 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 4151573 = 194605) (by norm_num)
theorem B5331221 : Blo 818347 5331221 := bbase (se 6 (by rfl) ⟨124950, by rfl⟩ : syracuseStep 5331221 = 249901) (by norm_num)
theorem B3496229 : Blo 818347 3496229 := bbase (se 4 (by rfl) ⟨327771, by rfl⟩ : syracuseStep 3496229 = 655543) (by norm_num)
theorem B1038673 : Blo 818347 1038673 := bbase (se 2 (by rfl) ⟨389502, by rfl⟩ : syracuseStep 1038673 = 779005) (by norm_num)
theorem B1169749 : Blo 818347 1169749 := bbase (se 10 (by rfl) ⟨1713, by rfl⟩ : syracuseStep 1169749 = 3427) (by norm_num)
theorem B875005 : Blo 818347 875005 := bbase (se 3 (by rfl) ⟨164063, by rfl⟩ : syracuseStep 875005 = 328127) (by norm_num)
theorem B1038845 : Blo 818347 1038845 := bbase (se 3 (by rfl) ⟨194783, by rfl⟩ : syracuseStep 1038845 = 389567) (by norm_num)
theorem B1661485 : Blo 818347 1661485 := bbase (se 3 (by rfl) ⟨311528, by rfl⟩ : syracuseStep 1661485 = 623057) (by norm_num)
theorem B1038901 : Blo 818347 1038901 := bbase (se 5 (by rfl) ⟨48698, by rfl⟩ : syracuseStep 1038901 = 97397) (by norm_num)
theorem B2808389 : Blo 818347 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B875125 : Blo 818347 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B1038997 : Blo 818347 1038997 := bbase (se 6 (by rfl) ⟨24351, by rfl⟩ : syracuseStep 1038997 = 48703) (by norm_num)
theorem B2251477 : Blo 818347 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B1039169 : Blo 818347 1039169 := bbase (se 2 (by rfl) ⟨389688, by rfl⟩ : syracuseStep 1039169 = 779377) (by norm_num)
theorem B875377 : Blo 818347 875377 := bbase (se 2 (by rfl) ⟨328266, by rfl⟩ : syracuseStep 875377 = 656533) (by norm_num)
theorem B875381 : Blo 818347 875381 := bbase (se 5 (by rfl) ⟨41033, by rfl⟩ : syracuseStep 875381 = 82067) (by norm_num)
theorem B1039225 : Blo 818347 1039225 := bbase (se 2 (by rfl) ⟨389709, by rfl⟩ : syracuseStep 1039225 = 779419) (by norm_num)
theorem B1039321 : Blo 818347 1039321 := bbase (se 2 (by rfl) ⟨389745, by rfl⟩ : syracuseStep 1039321 = 779491) (by norm_num)
theorem B3333221 : Blo 818347 3333221 := bbase (se 4 (by rfl) ⟨312489, by rfl⟩ : syracuseStep 3333221 = 624979) (by norm_num)
theorem B1170541 : Blo 818347 1170541 := bbase (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) (by norm_num)
theorem B1039493 : Blo 818347 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B2841749 : Blo 818347 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B1399997 : Blo 818347 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1039549 : Blo 818347 1039549 := bbase (se 3 (by rfl) ⟨194915, by rfl⟩ : syracuseStep 1039549 = 389831) (by norm_num)
theorem B1039645 : Blo 818347 1039645 := bbase (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) (by norm_num)
theorem B5266741 : Blo 818347 5266741 := bbase (se 5 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 5266741 = 493757) (by norm_num)
theorem B875945 : Blo 818347 875945 := bbase (se 2 (by rfl) ⟨328479, by rfl⟩ : syracuseStep 875945 = 656959) (by norm_num)
theorem B1170877 : Blo 818347 1170877 := bbase (se 3 (by rfl) ⟨219539, by rfl⟩ : syracuseStep 1170877 = 439079) (by norm_num)
theorem B1039817 : Blo 818347 1039817 := bbase (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) (by norm_num)
theorem B1039873 : Blo 818347 1039873 := bbase (se 2 (by rfl) ⟨389952, by rfl⟩ : syracuseStep 1039873 = 779905) (by norm_num)
theorem B4152869 : Blo 818347 4152869 := bbase (se 4 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 4152869 = 778663) (by norm_num)
theorem B4677173 : Blo 818347 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B1334845 : Blo 818347 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B1039969 : Blo 818347 1039969 := bbase (se 2 (by rfl) ⟨389988, by rfl⟩ : syracuseStep 1039969 = 779977) (by norm_num)
theorem B876133 : Blo 818347 876133 := bbase (se 4 (by rfl) ⟨82137, by rfl⟩ : syracuseStep 876133 = 164275) (by norm_num)
theorem B8412821 : Blo 818347 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B6217397 : Blo 818347 6217397 := bbase (se 5 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 6217397 = 582881) (by norm_num)
theorem B1040141 : Blo 818347 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B1040197 : Blo 818347 1040197 := bbase (se 4 (by rfl) ⟨97518, by rfl⟩ : syracuseStep 1040197 = 195037) (by norm_num)
theorem B1040293 : Blo 818347 1040293 := bbase (se 4 (by rfl) ⟨97527, by rfl⟩ : syracuseStep 1040293 = 195055) (by norm_num)
theorem B3498005 : Blo 818347 3498005 := bbase (se 6 (by rfl) ⟨81984, by rfl⟩ : syracuseStep 3498005 = 163969) (by norm_num)
theorem B1040465 : Blo 818347 1040465 := bbase (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) (by norm_num)
theorem B1040521 : Blo 818347 1040521 := bbase (se 2 (by rfl) ⟨390195, by rfl⟩ : syracuseStep 1040521 = 780391) (by norm_num)
theorem B1040617 : Blo 818347 1040617 := bbase (se 2 (by rfl) ⟨390231, by rfl⟩ : syracuseStep 1040617 = 780463) (by norm_num)
theorem B1663301 : Blo 818347 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B876953 : Blo 818347 876953 := bbase (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) (by norm_num)
theorem B1401317 : Blo 818347 1401317 := bbase (se 4 (by rfl) ⟨131373, by rfl⟩ : syracuseStep 1401317 = 262747) (by norm_num)
theorem B2024029 : Blo 818347 2024029 := bbase (se 3 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 2024029 = 759011) (by norm_num)
theorem B4678357 : Blo 818347 4678357 := bbase (se 7 (by rfl) ⟨54824, by rfl⟩ : syracuseStep 4678357 = 109649) (by norm_num)
theorem B4154165 : Blo 818347 4154165 := bbase (se 5 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 4154165 = 389453) (by norm_num)
theorem B877397 : Blo 818347 877397 := bbase (se 9 (by rfl) ⟨2570, by rfl⟩ : syracuseStep 877397 = 5141) (by norm_num)
theorem B877645 : Blo 818347 877645 := bbase (se 3 (by rfl) ⟨164558, by rfl⟩ : syracuseStep 877645 = 329117) (by norm_num)
theorem B878077 : Blo 818347 878077 := bbase (se 3 (by rfl) ⟨164639, by rfl⟩ : syracuseStep 878077 = 329279) (by norm_num)
theorem B878149 : Blo 818347 878149 := bbase (se 4 (by rfl) ⟨82326, by rfl⟩ : syracuseStep 878149 = 164653) (by norm_num)
theorem B1893989 : Blo 818347 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B1107613 : Blo 818347 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B4155461 : Blo 818347 4155461 := bbase (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) (by norm_num)
theorem B1108333 : Blo 818347 1108333 := bbase (se 3 (by rfl) ⟨207812, by rfl⟩ : syracuseStep 1108333 = 415625) (by norm_num)
theorem B4680341 : Blo 818347 4680341 := bbase (se 6 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 4680341 = 219391) (by norm_num)
theorem B3107605 : Blo 818347 3107605 := bbase (se 6 (by rfl) ⟨72834, by rfl⟩ : syracuseStep 3107605 = 145669) (by norm_num)
theorem B1108765 : Blo 818347 1108765 := bbase (se 3 (by rfl) ⟨207893, by rfl⟩ : syracuseStep 1108765 = 415787) (by norm_num)
theorem B1403725 : Blo 818347 1403725 := bbase (se 3 (by rfl) ⟨263198, by rfl⟩ : syracuseStep 1403725 = 526397) (by norm_num)
theorem B3107909 : Blo 818347 3107909 := bbase (se 4 (by rfl) ⟨291366, by rfl⟩ : syracuseStep 3107909 = 582733) (by norm_num)
theorem B1666261 : Blo 818347 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B1109245 : Blo 818347 1109245 := bbase (se 3 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 1109245 = 415967) (by norm_num)
theorem B1404157 : Blo 818347 1404157 := bbase (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) (by norm_num)
theorem B1666333 : Blo 818347 1666333 := bbase (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) (by norm_num)
theorem B4156757 : Blo 818347 4156757 := bbase (se 11 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4156757 = 6089) (by norm_num)
theorem B7466357 : Blo 818347 7466357 := bbase (se 5 (by rfl) ⟨349985, by rfl⟩ : syracuseStep 7466357 = 699971) (by norm_num)
theorem B4747157 : Blo 818347 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B1666981 : Blo 818347 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B33747029 : Blo 818347 33747029 := bbase (se 8 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 33747029 = 395473) (by norm_num)
theorem B3502277 : Blo 818347 3502277 := bbase (se 4 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 3502277 = 656677) (by norm_num)
theorem B3993941 : Blo 818347 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B4158053 : Blo 818347 4158053 := bbase (se 4 (by rfl) ⟨389817, by rfl⟩ : syracuseStep 4158053 = 779635) (by norm_num)
theorem B1110781 : Blo 818347 1110781 := bbase (se 3 (by rfl) ⟨208271, by rfl⟩ : syracuseStep 1110781 = 416543) (by norm_num)
theorem B9335573 : Blo 818347 9335573 := bbase (se 6 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 9335573 = 437605) (by norm_num)
theorem B4682549 : Blo 818347 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B3110021 : Blo 818347 3110021 := bbase (se 4 (by rfl) ⟨291564, by rfl⟩ : syracuseStep 3110021 = 583129) (by norm_num)
theorem B3110309 : Blo 818347 3110309 := bbase (se 4 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 3110309 = 583183) (by norm_num)
theorem B4159349 : Blo 818347 4159349 := bbase (se 5 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 4159349 = 389939) (by norm_num)
theorem B3504053 : Blo 818347 3504053 := bbase (se 5 (by rfl) ⟨164252, by rfl⟩ : syracuseStep 3504053 = 328505) (by norm_num)
theorem B3504293 : Blo 818347 3504293 := bbase (se 4 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 3504293 = 657055) (by norm_num)
theorem B2029805 : Blo 818347 2029805 := bbase (se 3 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 2029805 = 761177) (by norm_num)
theorem B3111493 : Blo 818347 3111493 := bbase (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) (by norm_num)
theorem B3111797 : Blo 818347 3111797 := bbase (se 5 (by rfl) ⟨145865, by rfl⟩ : syracuseStep 3111797 = 291731) (by norm_num)
theorem B4160645 : Blo 818347 4160645 := bbase (se 4 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 4160645 = 780121) (by norm_num)
theorem B2489573 : Blo 818347 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B6225173 : Blo 818347 6225173 := bbase (se 6 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 6225173 = 291805) (by norm_num)
theorem B6651317 : Blo 818347 6651317 := bbase (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) (by norm_num)
theorem B950149 : Blo 818347 950149 := bbase (se 4 (by rfl) ⟨89076, by rfl⟩ : syracuseStep 950149 = 178153) (by norm_num)
theorem B819203 : Blo 818347 819203 := bstep (se 1 (by rfl) ⟨614402, by rfl⟩ : syracuseStep 819203 = 1228805) B1228805
theorem B819219 : Blo 818347 819219 := bstep (se 1 (by rfl) ⟨614414, by rfl⟩ : syracuseStep 819219 = 1228829) B1228829
theorem B819235 : Blo 818347 819235 := bstep (se 1 (by rfl) ⟨614426, by rfl⟩ : syracuseStep 819235 = 1228853) B1228853
theorem B819251 : Blo 818347 819251 := bstep (se 1 (by rfl) ⟨614438, by rfl⟩ : syracuseStep 819251 = 1228877) B1228877
theorem B819267 : Blo 818347 819267 := bstep (se 1 (by rfl) ⟨614450, by rfl⟩ : syracuseStep 819267 = 1228901) B1228901
theorem B819283 : Blo 818347 819283 := bstep (se 1 (by rfl) ⟨614462, by rfl⟩ : syracuseStep 819283 = 1228925) B1228925
theorem B819299 : Blo 818347 819299 := bstep (se 1 (by rfl) ⟨614474, by rfl⟩ : syracuseStep 819299 = 1228949) B1228949
theorem B819315 : Blo 818347 819315 := bstep (se 1 (by rfl) ⟨614486, by rfl⟩ : syracuseStep 819315 = 1228973) B1228973
theorem B819331 : Blo 818347 819331 := bstep (se 1 (by rfl) ⟨614498, by rfl⟩ : syracuseStep 819331 = 1228997) B1228997
theorem B819347 : Blo 818347 819347 := bstep (se 1 (by rfl) ⟨614510, by rfl⟩ : syracuseStep 819347 = 1229021) B1229021
theorem B819363 : Blo 818347 819363 := bstep (se 1 (by rfl) ⟨614522, by rfl⟩ : syracuseStep 819363 = 1229045) B1229045
theorem B819379 : Blo 818347 819379 := bstep (se 1 (by rfl) ⟨614534, by rfl⟩ : syracuseStep 819379 = 1229069) B1229069
theorem B819395 : Blo 818347 819395 := bstep (se 1 (by rfl) ⟨614546, by rfl⟩ : syracuseStep 819395 = 1229093) B1229093
theorem B819411 : Blo 818347 819411 := bstep (se 1 (by rfl) ⟨614558, by rfl⟩ : syracuseStep 819411 = 1229117) B1229117
theorem B819427 : Blo 818347 819427 := bstep (se 1 (by rfl) ⟨614570, by rfl⟩ : syracuseStep 819427 = 1229141) B1229141
theorem B819443 : Blo 818347 819443 := bstep (se 1 (by rfl) ⟨614582, by rfl⟩ : syracuseStep 819443 = 1229165) B1229165
theorem B819459 : Blo 818347 819459 := bstep (se 1 (by rfl) ⟨614594, by rfl⟩ : syracuseStep 819459 = 1229189) B1229189
theorem B819475 : Blo 818347 819475 := bstep (se 1 (by rfl) ⟨614606, by rfl⟩ : syracuseStep 819475 = 1229213) B1229213
theorem B819491 : Blo 818347 819491 := bstep (se 1 (by rfl) ⟨614618, by rfl⟩ : syracuseStep 819491 = 1229237) B1229237
theorem B819507 : Blo 818347 819507 := bstep (se 1 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 819507 = 1229261) B1229261
theorem B819523 : Blo 818347 819523 := bstep (se 1 (by rfl) ⟨614642, by rfl⟩ : syracuseStep 819523 = 1229285) B1229285
theorem B819539 : Blo 818347 819539 := bstep (se 1 (by rfl) ⟨614654, by rfl⟩ : syracuseStep 819539 = 1229309) B1229309
theorem B819555 : Blo 818347 819555 := bstep (se 1 (by rfl) ⟨614666, by rfl⟩ : syracuseStep 819555 = 1229333) B1229333
theorem B819571 : Blo 818347 819571 := bstep (se 1 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 819571 = 1229357) B1229357
theorem B819587 : Blo 818347 819587 := bstep (se 1 (by rfl) ⟨614690, by rfl⟩ : syracuseStep 819587 = 1229381) B1229381
theorem B819603 : Blo 818347 819603 := bstep (se 1 (by rfl) ⟨614702, by rfl⟩ : syracuseStep 819603 = 1229405) B1229405
theorem B819619 : Blo 818347 819619 := bstep (se 1 (by rfl) ⟨614714, by rfl⟩ : syracuseStep 819619 = 1229429) B1229429
theorem B819635 : Blo 818347 819635 := bstep (se 1 (by rfl) ⟨614726, by rfl⟩ : syracuseStep 819635 = 1229453) B1229453
theorem B819651 : Blo 818347 819651 := bstep (se 1 (by rfl) ⟨614738, by rfl⟩ : syracuseStep 819651 = 1229477) B1229477
theorem B819667 : Blo 818347 819667 := bstep (se 1 (by rfl) ⟨614750, by rfl⟩ : syracuseStep 819667 = 1229501) B1229501
theorem B819683 : Blo 818347 819683 := bstep (se 1 (by rfl) ⟨614762, by rfl⟩ : syracuseStep 819683 = 1229525) B1229525
theorem B819699 : Blo 818347 819699 := bstep (se 1 (by rfl) ⟨614774, by rfl⟩ : syracuseStep 819699 = 1229549) B1229549
theorem B819715 : Blo 818347 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B1966609 : Blo 818347 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B819731 : Blo 818347 819731 := bstep (se 1 (by rfl) ⟨614798, by rfl⟩ : syracuseStep 819731 = 1229597) B1229597
theorem B819747 : Blo 818347 819747 := bstep (se 1 (by rfl) ⟨614810, by rfl⟩ : syracuseStep 819747 = 1229621) B1229621
theorem B819763 : Blo 818347 819763 := bstep (se 1 (by rfl) ⟨614822, by rfl⟩ : syracuseStep 819763 = 1229645) B1229645
theorem B819779 : Blo 818347 819779 := bstep (se 1 (by rfl) ⟨614834, by rfl⟩ : syracuseStep 819779 = 1229669) B1229669
theorem B819795 : Blo 818347 819795 := bstep (se 1 (by rfl) ⟨614846, by rfl⟩ : syracuseStep 819795 = 1229693) B1229693
theorem B1311329 : Blo 818347 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B819811 : Blo 818347 819811 := bstep (se 1 (by rfl) ⟨614858, by rfl⟩ : syracuseStep 819811 = 1229717) B1229717
theorem B1245809 : Blo 818347 1245809 := bstep (se 2 (by rfl) ⟨467178, by rfl⟩ : syracuseStep 1245809 = 934357) B934357
theorem B14615153 : Blo 818347 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B819827 : Blo 818347 819827 := bstep (se 1 (by rfl) ⟨614870, by rfl⟩ : syracuseStep 819827 = 1229741) B1229741
theorem B819843 : Blo 818347 819843 := bstep (se 1 (by rfl) ⟨614882, by rfl⟩ : syracuseStep 819843 = 1229765) B1229765
theorem B819859 : Blo 818347 819859 := bstep (se 1 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 819859 = 1229789) B1229789
theorem B819875 : Blo 818347 819875 := bstep (se 1 (by rfl) ⟨614906, by rfl⟩ : syracuseStep 819875 = 1229813) B1229813
theorem B819891 : Blo 818347 819891 := bstep (se 1 (by rfl) ⟨614918, by rfl⟩ : syracuseStep 819891 = 1229837) B1229837
theorem B819907 : Blo 818347 819907 := bstep (se 1 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 819907 = 1229861) B1229861
theorem B819923 : Blo 818347 819923 := bstep (se 1 (by rfl) ⟨614942, by rfl⟩ : syracuseStep 819923 = 1229885) B1229885
theorem B819939 : Blo 818347 819939 := bstep (se 1 (by rfl) ⟨614954, by rfl⟩ : syracuseStep 819939 = 1229909) B1229909
theorem B819955 : Blo 818347 819955 := bstep (se 1 (by rfl) ⟨614966, by rfl⟩ : syracuseStep 819955 = 1229933) B1229933
theorem B819971 : Blo 818347 819971 := bstep (se 1 (by rfl) ⟨614978, by rfl⟩ : syracuseStep 819971 = 1229957) B1229957
theorem B3113741 : Blo 818347 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B819987 : Blo 818347 819987 := bstep (se 1 (by rfl) ⟨614990, by rfl⟩ : syracuseStep 819987 = 1229981) B1229981
theorem B820003 : Blo 818347 820003 := bstep (se 1 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 820003 = 1230005) B1230005
theorem B820019 : Blo 818347 820019 := bstep (se 1 (by rfl) ⟨615014, by rfl⟩ : syracuseStep 820019 = 1230029) B1230029
theorem B820035 : Blo 818347 820035 := bstep (se 1 (by rfl) ⟨615026, by rfl⟩ : syracuseStep 820035 = 1230053) B1230053
theorem B5604173 : Blo 818347 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B820051 : Blo 818347 820051 := bstep (se 1 (by rfl) ⟨615038, by rfl⟩ : syracuseStep 820051 = 1230077) B1230077
theorem B820067 : Blo 818347 820067 := bstep (se 1 (by rfl) ⟨615050, by rfl⟩ : syracuseStep 820067 = 1230101) B1230101
theorem B820083 : Blo 818347 820083 := bstep (se 1 (by rfl) ⟨615062, by rfl⟩ : syracuseStep 820083 = 1230125) B1230125
theorem B820099 : Blo 818347 820099 := bstep (se 1 (by rfl) ⟨615074, by rfl⟩ : syracuseStep 820099 = 1230149) B1230149
theorem B820115 : Blo 818347 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B1475491 : Blo 818347 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B820131 : Blo 818347 820131 := bstep (se 1 (by rfl) ⟨615098, by rfl⟩ : syracuseStep 820131 = 1230197) B1230197
theorem B820147 : Blo 818347 820147 := bstep (se 1 (by rfl) ⟨615110, by rfl⟩ : syracuseStep 820147 = 1230221) B1230221
theorem B820163 : Blo 818347 820163 := bstep (se 1 (by rfl) ⟨615122, by rfl⟩ : syracuseStep 820163 = 1230245) B1230245
theorem B820179 : Blo 818347 820179 := bstep (se 1 (by rfl) ⟨615134, by rfl⟩ : syracuseStep 820179 = 1230269) B1230269
theorem B984035 : Blo 818347 984035 := bstep (se 1 (by rfl) ⟨738026, by rfl⟩ : syracuseStep 984035 = 1476053) B1476053
theorem B8979427 : Blo 818347 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B820195 : Blo 818347 820195 := bstep (se 1 (by rfl) ⟨615146, by rfl⟩ : syracuseStep 820195 = 1230293) B1230293
theorem B820211 : Blo 818347 820211 := bstep (se 1 (by rfl) ⟨615158, by rfl⟩ : syracuseStep 820211 = 1230317) B1230317
theorem B820227 : Blo 818347 820227 := bstep (se 1 (by rfl) ⟨615170, by rfl⟩ : syracuseStep 820227 = 1230341) B1230341
theorem B820243 : Blo 818347 820243 := bstep (se 1 (by rfl) ⟨615182, by rfl⟩ : syracuseStep 820243 = 1230365) B1230365
theorem B820259 : Blo 818347 820259 := bstep (se 1 (by rfl) ⟨615194, by rfl⟩ : syracuseStep 820259 = 1230389) B1230389
theorem B820275 : Blo 818347 820275 := bstep (se 1 (by rfl) ⟨615206, by rfl⟩ : syracuseStep 820275 = 1230413) B1230413
theorem B820291 : Blo 818347 820291 := bstep (se 1 (by rfl) ⟨615218, by rfl⟩ : syracuseStep 820291 = 1230437) B1230437
theorem B820307 : Blo 818347 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B820323 : Blo 818347 820323 := bstep (se 1 (by rfl) ⟨615242, by rfl⟩ : syracuseStep 820323 = 1230485) B1230485
theorem B820339 : Blo 818347 820339 := bstep (se 1 (by rfl) ⟨615254, by rfl⟩ : syracuseStep 820339 = 1230509) B1230509
theorem B820355 : Blo 818347 820355 := bstep (se 1 (by rfl) ⟨615266, by rfl⟩ : syracuseStep 820355 = 1230533) B1230533
theorem B820371 : Blo 818347 820371 := bstep (se 1 (by rfl) ⟨615278, by rfl⟩ : syracuseStep 820371 = 1230557) B1230557
theorem B820387 : Blo 818347 820387 := bstep (se 1 (by rfl) ⟨615290, by rfl⟩ : syracuseStep 820387 = 1230581) B1230581
theorem B820403 : Blo 818347 820403 := bstep (se 1 (by rfl) ⟨615302, by rfl⟩ : syracuseStep 820403 = 1230605) B1230605
theorem B820419 : Blo 818347 820419 := bstep (se 1 (by rfl) ⟨615314, by rfl⟩ : syracuseStep 820419 = 1230629) B1230629
theorem B7013573 : Blo 818347 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B820435 : Blo 818347 820435 := bstep (se 1 (by rfl) ⟨615326, by rfl⟩ : syracuseStep 820435 = 1230653) B1230653
theorem B820451 : Blo 818347 820451 := bstep (se 1 (by rfl) ⟨615338, by rfl⟩ : syracuseStep 820451 = 1230677) B1230677
theorem B820467 : Blo 818347 820467 := bstep (se 1 (by rfl) ⟨615350, by rfl⟩ : syracuseStep 820467 = 1230701) B1230701
theorem B820483 : Blo 818347 820483 := bstep (se 1 (by rfl) ⟨615362, by rfl⟩ : syracuseStep 820483 = 1230725) B1230725
theorem B820499 : Blo 818347 820499 := bstep (se 1 (by rfl) ⟨615374, by rfl⟩ : syracuseStep 820499 = 1230749) B1230749
theorem B820515 : Blo 818347 820515 := bstep (se 1 (by rfl) ⟨615386, by rfl⟩ : syracuseStep 820515 = 1230773) B1230773
theorem B820531 : Blo 818347 820531 := bstep (se 1 (by rfl) ⟨615398, by rfl⟩ : syracuseStep 820531 = 1230797) B1230797
theorem B820547 : Blo 818347 820547 := bstep (se 1 (by rfl) ⟨615410, by rfl⟩ : syracuseStep 820547 = 1230821) B1230821
theorem B820563 : Blo 818347 820563 := bstep (se 1 (by rfl) ⟨615422, by rfl⟩ : syracuseStep 820563 = 1230845) B1230845
theorem B820579 : Blo 818347 820579 := bstep (se 1 (by rfl) ⟨615434, by rfl⟩ : syracuseStep 820579 = 1230869) B1230869
theorem B820595 : Blo 818347 820595 := bstep (se 1 (by rfl) ⟨615446, by rfl⟩ : syracuseStep 820595 = 1230893) B1230893
theorem B2622851 : Blo 818347 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B820611 : Blo 818347 820611 := bstep (se 1 (by rfl) ⟨615458, by rfl⟩ : syracuseStep 820611 = 1230917) B1230917
theorem B820627 : Blo 818347 820627 := bstep (se 1 (by rfl) ⟨615470, by rfl⟩ : syracuseStep 820627 = 1230941) B1230941
theorem B820643 : Blo 818347 820643 := bstep (se 1 (by rfl) ⟨615482, by rfl⟩ : syracuseStep 820643 = 1230965) B1230965
theorem B820659 : Blo 818347 820659 := bstep (se 1 (by rfl) ⟨615494, by rfl⟩ : syracuseStep 820659 = 1230989) B1230989
theorem B1312195 : Blo 818347 1312195 := bstep (se 1 (by rfl) ⟨984146, by rfl⟩ : syracuseStep 1312195 = 1968293) B1968293
theorem B820675 : Blo 818347 820675 := bstep (se 1 (by rfl) ⟨615506, by rfl⟩ : syracuseStep 820675 = 1231013) B1231013
theorem B820691 : Blo 818347 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B820707 : Blo 818347 820707 := bstep (se 1 (by rfl) ⟨615530, by rfl⟩ : syracuseStep 820707 = 1231061) B1231061
theorem B820723 : Blo 818347 820723 := bstep (se 1 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 820723 = 1231085) B1231085
theorem B820739 : Blo 818347 820739 := bstep (se 1 (by rfl) ⟨615554, by rfl⟩ : syracuseStep 820739 = 1231109) B1231109
theorem B820755 : Blo 818347 820755 := bstep (se 1 (by rfl) ⟨615566, by rfl⟩ : syracuseStep 820755 = 1231133) B1231133
theorem B820771 : Blo 818347 820771 := bstep (se 1 (by rfl) ⟨615578, by rfl⟩ : syracuseStep 820771 = 1231157) B1231157
theorem B820787 : Blo 818347 820787 := bstep (se 1 (by rfl) ⟨615590, by rfl⟩ : syracuseStep 820787 = 1231181) B1231181
theorem B820803 : Blo 818347 820803 := bstep (se 1 (by rfl) ⟨615602, by rfl⟩ : syracuseStep 820803 = 1231205) B1231205
theorem B820819 : Blo 818347 820819 := bstep (se 1 (by rfl) ⟨615614, by rfl⟩ : syracuseStep 820819 = 1231229) B1231229
theorem B820835 : Blo 818347 820835 := bstep (se 1 (by rfl) ⟨615626, by rfl⟩ : syracuseStep 820835 = 1231253) B1231253
theorem B820851 : Blo 818347 820851 := bstep (se 1 (by rfl) ⟨615638, by rfl⟩ : syracuseStep 820851 = 1231277) B1231277
theorem B820867 : Blo 818347 820867 := bstep (se 1 (by rfl) ⟨615650, by rfl⟩ : syracuseStep 820867 = 1231301) B1231301
theorem B820883 : Blo 818347 820883 := bstep (se 1 (by rfl) ⟨615662, by rfl⟩ : syracuseStep 820883 = 1231325) B1231325
theorem B4982435 : Blo 818347 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B820899 : Blo 818347 820899 := bstep (se 1 (by rfl) ⟨615674, by rfl⟩ : syracuseStep 820899 = 1231349) B1231349
theorem B820915 : Blo 818347 820915 := bstep (se 1 (by rfl) ⟨615686, by rfl⟩ : syracuseStep 820915 = 1231373) B1231373
theorem B1312451 : Blo 818347 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B820931 : Blo 818347 820931 := bstep (se 1 (by rfl) ⟨615698, by rfl⟩ : syracuseStep 820931 = 1231397) B1231397
theorem B820947 : Blo 818347 820947 := bstep (se 1 (by rfl) ⟨615710, by rfl⟩ : syracuseStep 820947 = 1231421) B1231421
theorem B820963 : Blo 818347 820963 := bstep (se 1 (by rfl) ⟨615722, by rfl⟩ : syracuseStep 820963 = 1231445) B1231445
theorem B820979 : Blo 818347 820979 := bstep (se 1 (by rfl) ⟨615734, by rfl⟩ : syracuseStep 820979 = 1231469) B1231469
theorem B820995 : Blo 818347 820995 := bstep (se 1 (by rfl) ⟨615746, by rfl⟩ : syracuseStep 820995 = 1231493) B1231493
theorem B821011 : Blo 818347 821011 := bstep (se 1 (by rfl) ⟨615758, by rfl⟩ : syracuseStep 821011 = 1231517) B1231517
theorem B821027 : Blo 818347 821027 := bstep (se 1 (by rfl) ⟨615770, by rfl⟩ : syracuseStep 821027 = 1231541) B1231541
theorem B821043 : Blo 818347 821043 := bstep (se 1 (by rfl) ⟨615782, by rfl⟩ : syracuseStep 821043 = 1231565) B1231565
theorem B821059 : Blo 818347 821059 := bstep (se 1 (by rfl) ⟨615794, by rfl⟩ : syracuseStep 821059 = 1231589) B1231589
theorem B821075 : Blo 818347 821075 := bstep (se 1 (by rfl) ⟨615806, by rfl⟩ : syracuseStep 821075 = 1231613) B1231613
theorem B821091 : Blo 818347 821091 := bstep (se 1 (by rfl) ⟨615818, by rfl⟩ : syracuseStep 821091 = 1231637) B1231637
theorem B821107 : Blo 818347 821107 := bstep (se 1 (by rfl) ⟨615830, by rfl⟩ : syracuseStep 821107 = 1231661) B1231661
theorem B821123 : Blo 818347 821123 := bstep (se 1 (by rfl) ⟨615842, by rfl⟩ : syracuseStep 821123 = 1231685) B1231685
theorem B821139 : Blo 818347 821139 := bstep (se 1 (by rfl) ⟨615854, by rfl⟩ : syracuseStep 821139 = 1231709) B1231709
theorem B1574819 : Blo 818347 1574819 := bstep (se 1 (by rfl) ⟨1181114, by rfl⟩ : syracuseStep 1574819 = 2362229) B2362229
theorem B821155 : Blo 818347 821155 := bstep (se 1 (by rfl) ⟨615866, by rfl⟩ : syracuseStep 821155 = 1231733) B1231733
theorem B4982705 : Blo 818347 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B821171 : Blo 818347 821171 := bstep (se 1 (by rfl) ⟨615878, by rfl⟩ : syracuseStep 821171 = 1231757) B1231757
theorem B1247171 : Blo 818347 1247171 := bstep (se 1 (by rfl) ⟨935378, by rfl⟩ : syracuseStep 1247171 = 1870757) B1870757
theorem B821187 : Blo 818347 821187 := bstep (se 1 (by rfl) ⟨615890, by rfl⟩ : syracuseStep 821187 = 1231781) B1231781
theorem B821203 : Blo 818347 821203 := bstep (se 1 (by rfl) ⟨615902, by rfl⟩ : syracuseStep 821203 = 1231805) B1231805
theorem B821219 : Blo 818347 821219 := bstep (se 1 (by rfl) ⟨615914, by rfl⟩ : syracuseStep 821219 = 1231829) B1231829
theorem B821235 : Blo 818347 821235 := bstep (se 1 (by rfl) ⟨615926, by rfl⟩ : syracuseStep 821235 = 1231853) B1231853
theorem B821251 : Blo 818347 821251 := bstep (se 1 (by rfl) ⟨615938, by rfl⟩ : syracuseStep 821251 = 1231877) B1231877
theorem B821267 : Blo 818347 821267 := bstep (se 1 (by rfl) ⟨615950, by rfl⟩ : syracuseStep 821267 = 1231901) B1231901
theorem B821283 : Blo 818347 821283 := bstep (se 1 (by rfl) ⟨615962, by rfl⟩ : syracuseStep 821283 = 1231925) B1231925
theorem B821299 : Blo 818347 821299 := bstep (se 1 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 821299 = 1231949) B1231949
theorem B821315 : Blo 818347 821315 := bstep (se 1 (by rfl) ⟨615986, by rfl⟩ : syracuseStep 821315 = 1231973) B1231973
theorem B821331 : Blo 818347 821331 := bstep (se 1 (by rfl) ⟨615998, by rfl⟩ : syracuseStep 821331 = 1231997) B1231997
theorem B821347 : Blo 818347 821347 := bstep (se 1 (by rfl) ⟨616010, by rfl⟩ : syracuseStep 821347 = 1232021) B1232021
theorem B4982897 : Blo 818347 4982897 := bstep (se 2 (by rfl) ⟨1868586, by rfl⟩ : syracuseStep 4982897 = 3737173) B3737173
theorem B821363 : Blo 818347 821363 := bstep (se 1 (by rfl) ⟨616022, by rfl⟩ : syracuseStep 821363 = 1232045) B1232045
theorem B821379 : Blo 818347 821379 := bstep (se 1 (by rfl) ⟨616034, by rfl⟩ : syracuseStep 821379 = 1232069) B1232069
theorem B821395 : Blo 818347 821395 := bstep (se 1 (by rfl) ⟨616046, by rfl⟩ : syracuseStep 821395 = 1232093) B1232093
theorem B821411 : Blo 818347 821411 := bstep (se 1 (by rfl) ⟨616058, by rfl⟩ : syracuseStep 821411 = 1232117) B1232117
theorem B821427 : Blo 818347 821427 := bstep (se 1 (by rfl) ⟨616070, by rfl⟩ : syracuseStep 821427 = 1232141) B1232141
theorem B821443 : Blo 818347 821443 := bstep (se 1 (by rfl) ⟨616082, by rfl⟩ : syracuseStep 821443 = 1232165) B1232165
theorem B821459 : Blo 818347 821459 := bstep (se 1 (by rfl) ⟨616094, by rfl⟩ : syracuseStep 821459 = 1232189) B1232189
theorem B821475 : Blo 818347 821475 := bstep (se 1 (by rfl) ⟨616106, by rfl⟩ : syracuseStep 821475 = 1232213) B1232213
theorem B821491 : Blo 818347 821491 := bstep (se 1 (by rfl) ⟨616118, by rfl⟩ : syracuseStep 821491 = 1232237) B1232237
theorem B821507 : Blo 818347 821507 := bstep (se 1 (by rfl) ⟨616130, by rfl⟩ : syracuseStep 821507 = 1232261) B1232261
theorem B821523 : Blo 818347 821523 := bstep (se 1 (by rfl) ⟨616142, by rfl⟩ : syracuseStep 821523 = 1232285) B1232285
theorem B821539 : Blo 818347 821539 := bstep (se 1 (by rfl) ⟨616154, by rfl⟩ : syracuseStep 821539 = 1232309) B1232309
theorem B821555 : Blo 818347 821555 := bstep (se 1 (by rfl) ⟨616166, by rfl⟩ : syracuseStep 821555 = 1232333) B1232333
theorem B821571 : Blo 818347 821571 := bstep (se 1 (by rfl) ⟨616178, by rfl⟩ : syracuseStep 821571 = 1232357) B1232357
theorem B821587 : Blo 818347 821587 := bstep (se 1 (by rfl) ⟨616190, by rfl⟩ : syracuseStep 821587 = 1232381) B1232381
theorem B821603 : Blo 818347 821603 := bstep (se 1 (by rfl) ⟨616202, by rfl⟩ : syracuseStep 821603 = 1232405) B1232405
theorem B821619 : Blo 818347 821619 := bstep (se 1 (by rfl) ⟨616214, by rfl⟩ : syracuseStep 821619 = 1232429) B1232429
theorem B821635 : Blo 818347 821635 := bstep (se 1 (by rfl) ⟨616226, by rfl⟩ : syracuseStep 821635 = 1232453) B1232453
theorem B821651 : Blo 818347 821651 := bstep (se 1 (by rfl) ⟨616238, by rfl⟩ : syracuseStep 821651 = 1232477) B1232477
theorem B821667 : Blo 818347 821667 := bstep (se 1 (by rfl) ⟨616250, by rfl⟩ : syracuseStep 821667 = 1232501) B1232501
theorem B821683 : Blo 818347 821683 := bstep (se 1 (by rfl) ⟨616262, by rfl⟩ : syracuseStep 821683 = 1232525) B1232525
theorem B821699 : Blo 818347 821699 := bstep (se 1 (by rfl) ⟨616274, by rfl⟩ : syracuseStep 821699 = 1232549) B1232549
theorem B7866821 : Blo 818347 7866821 := bstep (se 4 (by rfl) ⟨737514, by rfl⟩ : syracuseStep 7866821 = 1475029) B1475029
theorem B821715 : Blo 818347 821715 := bstep (se 1 (by rfl) ⟨616286, by rfl⟩ : syracuseStep 821715 = 1232573) B1232573
theorem B13273571 : Blo 818347 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B1477091 : Blo 818347 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B821731 : Blo 818347 821731 := bstep (se 1 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 821731 = 1232597) B1232597
theorem B821747 : Blo 818347 821747 := bstep (se 1 (by rfl) ⟨616310, by rfl⟩ : syracuseStep 821747 = 1232621) B1232621
theorem B821763 : Blo 818347 821763 := bstep (se 1 (by rfl) ⟨616322, by rfl⟩ : syracuseStep 821763 = 1232645) B1232645
theorem B821779 : Blo 818347 821779 := bstep (se 1 (by rfl) ⟨616334, by rfl⟩ : syracuseStep 821779 = 1232669) B1232669
theorem B821795 : Blo 818347 821795 := bstep (se 1 (by rfl) ⟨616346, by rfl⟩ : syracuseStep 821795 = 1232693) B1232693
theorem B821811 : Blo 818347 821811 := bstep (se 1 (by rfl) ⟨616358, by rfl⟩ : syracuseStep 821811 = 1232717) B1232717
theorem B821827 : Blo 818347 821827 := bstep (se 1 (by rfl) ⟨616370, by rfl⟩ : syracuseStep 821827 = 1232741) B1232741
theorem B821843 : Blo 818347 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B821859 : Blo 818347 821859 := bstep (se 1 (by rfl) ⟨616394, by rfl⟩ : syracuseStep 821859 = 1232789) B1232789
theorem B821875 : Blo 818347 821875 := bstep (se 1 (by rfl) ⟨616406, by rfl⟩ : syracuseStep 821875 = 1232813) B1232813
theorem B821891 : Blo 818347 821891 := bstep (se 1 (by rfl) ⟨616418, by rfl⟩ : syracuseStep 821891 = 1232837) B1232837
theorem B1313425 : Blo 818347 1313425 := bstep (se 2 (by rfl) ⟨492534, by rfl⟩ : syracuseStep 1313425 = 985069) B985069
theorem B821907 : Blo 818347 821907 := bstep (se 1 (by rfl) ⟨616430, by rfl⟩ : syracuseStep 821907 = 1232861) B1232861
theorem B821923 : Blo 818347 821923 := bstep (se 1 (by rfl) ⟨616442, by rfl⟩ : syracuseStep 821923 = 1232885) B1232885
theorem B821939 : Blo 818347 821939 := bstep (se 1 (by rfl) ⟨616454, by rfl⟩ : syracuseStep 821939 = 1232909) B1232909
theorem B2624195 : Blo 818347 2624195 := bstep (se 1 (by rfl) ⟨1968146, by rfl⟩ : syracuseStep 2624195 = 3936293) B3936293
theorem B1477315 : Blo 818347 1477315 := bstep (se 1 (by rfl) ⟨1107986, by rfl⟩ : syracuseStep 1477315 = 2215973) B2215973
theorem B821955 : Blo 818347 821955 := bstep (se 1 (by rfl) ⟨616466, by rfl⟩ : syracuseStep 821955 = 1232933) B1232933
theorem B821971 : Blo 818347 821971 := bstep (se 1 (by rfl) ⟨616478, by rfl⟩ : syracuseStep 821971 = 1232957) B1232957
theorem B821987 : Blo 818347 821987 := bstep (se 1 (by rfl) ⟨616490, by rfl⟩ : syracuseStep 821987 = 1232981) B1232981
theorem B822003 : Blo 818347 822003 := bstep (se 1 (by rfl) ⟨616502, by rfl⟩ : syracuseStep 822003 = 1233005) B1233005
theorem B822019 : Blo 818347 822019 := bstep (se 1 (by rfl) ⟨616514, by rfl⟩ : syracuseStep 822019 = 1233029) B1233029
theorem B822035 : Blo 818347 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B3509027 : Blo 818347 3509027 := bstep (se 1 (by rfl) ⟨2631770, by rfl⟩ : syracuseStep 3509027 = 5263541) B5263541
theorem B822051 : Blo 818347 822051 := bstep (se 1 (by rfl) ⟨616538, by rfl⟩ : syracuseStep 822051 = 1233077) B1233077
theorem B822067 : Blo 818347 822067 := bstep (se 1 (by rfl) ⟨616550, by rfl⟩ : syracuseStep 822067 = 1233101) B1233101
theorem B822083 : Blo 818347 822083 := bstep (se 1 (by rfl) ⟨616562, by rfl⟩ : syracuseStep 822083 = 1233125) B1233125
theorem B3115853 : Blo 818347 3115853 := bstep (se 3 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 3115853 = 1168445) B1168445
theorem B822099 : Blo 818347 822099 := bstep (se 1 (by rfl) ⟨616574, by rfl⟩ : syracuseStep 822099 = 1233149) B1233149
theorem B822115 : Blo 818347 822115 := bstep (se 1 (by rfl) ⟨616586, by rfl⟩ : syracuseStep 822115 = 1233173) B1233173
theorem B822131 : Blo 818347 822131 := bstep (se 1 (by rfl) ⟨616598, by rfl⟩ : syracuseStep 822131 = 1233197) B1233197
theorem B822147 : Blo 818347 822147 := bstep (se 1 (by rfl) ⟨616610, by rfl⟩ : syracuseStep 822147 = 1233221) B1233221
theorem B5245829 : Blo 818347 5245829 := bstep (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) B983593
theorem B822163 : Blo 818347 822163 := bstep (se 1 (by rfl) ⟨616622, by rfl⟩ : syracuseStep 822163 = 1233245) B1233245
theorem B822179 : Blo 818347 822179 := bstep (se 1 (by rfl) ⟨616634, by rfl⟩ : syracuseStep 822179 = 1233269) B1233269
theorem B822195 : Blo 818347 822195 := bstep (se 1 (by rfl) ⟨616646, by rfl⟩ : syracuseStep 822195 = 1233293) B1233293
theorem B822211 : Blo 818347 822211 := bstep (se 1 (by rfl) ⟨616658, by rfl⟩ : syracuseStep 822211 = 1233317) B1233317
theorem B822227 : Blo 818347 822227 := bstep (se 1 (by rfl) ⟨616670, by rfl⟩ : syracuseStep 822227 = 1233341) B1233341
theorem B822243 : Blo 818347 822243 := bstep (se 1 (by rfl) ⟨616682, by rfl⟩ : syracuseStep 822243 = 1233365) B1233365
theorem B822259 : Blo 818347 822259 := bstep (se 1 (by rfl) ⟨616694, by rfl⟩ : syracuseStep 822259 = 1233389) B1233389
theorem B822275 : Blo 818347 822275 := bstep (se 1 (by rfl) ⟨616706, by rfl⟩ : syracuseStep 822275 = 1233413) B1233413
theorem B822291 : Blo 818347 822291 := bstep (se 1 (by rfl) ⟨616718, by rfl⟩ : syracuseStep 822291 = 1233437) B1233437
theorem B822307 : Blo 818347 822307 := bstep (se 1 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 822307 = 1233461) B1233461
theorem B822323 : Blo 818347 822323 := bstep (se 1 (by rfl) ⟨616742, by rfl⟩ : syracuseStep 822323 = 1233485) B1233485
theorem B822339 : Blo 818347 822339 := bstep (se 1 (by rfl) ⟨616754, by rfl⟩ : syracuseStep 822339 = 1233509) B1233509
theorem B6229061 : Blo 818347 6229061 := bstep (se 4 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 6229061 = 1167949) B1167949
theorem B920659 : Blo 818347 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B1477777 : Blo 818347 1477777 := bstep (se 2 (by rfl) ⟨554166, by rfl⟩ : syracuseStep 1477777 = 1108333) B1108333
theorem B920803 : Blo 818347 920803 := bstep (se 1 (by rfl) ⟨690602, by rfl⟩ : syracuseStep 920803 = 1381205) B1381205
theorem B1248547 : Blo 818347 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B920947 : Blo 818347 920947 := bstep (se 1 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 920947 = 1381421) B1381421
theorem B1871267 : Blo 818347 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B2952625 : Blo 818347 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B921091 : Blo 818347 921091 := bstep (se 1 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 921091 = 1381637) B1381637
theorem B1314353 : Blo 818347 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B3116657 : Blo 818347 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B921235 : Blo 818347 921235 := bstep (se 1 (by rfl) ⟨690926, by rfl⟩ : syracuseStep 921235 = 1381853) B1381853
theorem B1478353 : Blo 818347 1478353 := bstep (se 2 (by rfl) ⟨554382, by rfl⟩ : syracuseStep 1478353 = 1108765) B1108765
theorem B1871633 : Blo 818347 1871633 := bstep (se 2 (by rfl) ⟨701862, by rfl⟩ : syracuseStep 1871633 = 1403725) B1403725
theorem B921379 : Blo 818347 921379 := bstep (se 1 (by rfl) ⟨691034, by rfl⟩ : syracuseStep 921379 = 1382069) B1382069
theorem B2330477 : Blo 818347 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B986995 : Blo 818347 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B2330545 : Blo 818347 2330545 := bstep (se 2 (by rfl) ⟨873954, by rfl⟩ : syracuseStep 2330545 = 1747909) B1747909
theorem B921523 : Blo 818347 921523 := bstep (se 1 (by rfl) ⟨691142, by rfl⟩ : syracuseStep 921523 = 1382285) B1382285
theorem B921667 : Blo 818347 921667 := bstep (se 1 (by rfl) ⟨691250, by rfl⟩ : syracuseStep 921667 = 1382501) B1382501
theorem B1249361 : Blo 818347 1249361 := bstep (se 2 (by rfl) ⟨468510, by rfl⟩ : syracuseStep 1249361 = 937021) B937021
theorem B2330819 : Blo 818347 2330819 := bstep (se 1 (by rfl) ⟨1748114, by rfl⟩ : syracuseStep 2330819 = 3496229) B3496229
theorem B921811 : Blo 818347 921811 := bstep (se 1 (by rfl) ⟨691358, by rfl⟩ : syracuseStep 921811 = 1382717) B1382717
theorem B3117325 : Blo 818347 3117325 := bstep (se 3 (by rfl) ⟨584498, by rfl⟩ : syracuseStep 3117325 = 1168997) B1168997
theorem B1478993 : Blo 818347 1478993 := bstep (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) B1109245
theorem B1872209 : Blo 818347 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B921955 : Blo 818347 921955 := bstep (se 1 (by rfl) ⟨691466, by rfl⟩ : syracuseStep 921955 = 1382933) B1382933
theorem B1970531 : Blo 818347 1970531 := bstep (se 1 (by rfl) ⟨1477898, by rfl⟩ : syracuseStep 1970531 = 2955797) B2955797
theorem B1315187 : Blo 818347 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B1315219 : Blo 818347 1315219 := bstep (se 1 (by rfl) ⟨986414, by rfl⟩ : syracuseStep 1315219 = 1972829) B1972829
theorem B2625965 : Blo 818347 2625965 := bstep (se 3 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 2625965 = 984737) B984737
theorem B922099 : Blo 818347 922099 := bstep (se 1 (by rfl) ⟨691574, by rfl⟩ : syracuseStep 922099 = 1383149) B1383149
theorem B1970723 : Blo 818347 1970723 := bstep (se 1 (by rfl) ⟨1478042, by rfl⟩ : syracuseStep 1970723 = 2956085) B2956085
theorem B2363971 : Blo 818347 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B922243 : Blo 818347 922243 := bstep (se 1 (by rfl) ⟨691682, by rfl⟩ : syracuseStep 922243 = 1383365) B1383365
theorem B1381009 : Blo 818347 1381009 := bstep (se 2 (by rfl) ⟨517878, by rfl⟩ : syracuseStep 1381009 = 1035757) B1035757
theorem B1184419 : Blo 818347 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B1381043 : Blo 818347 1381043 := bstep (se 1 (by rfl) ⟨1035782, by rfl⟩ : syracuseStep 1381043 = 2071565) B2071565
theorem B8852165 : Blo 818347 8852165 := bstep (se 4 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 8852165 = 1659781) B1659781
theorem B1577713 : Blo 818347 1577713 := bstep (se 2 (by rfl) ⟨591642, by rfl⟩ : syracuseStep 1577713 = 1183285) B1183285
theorem B3511025 : Blo 818347 3511025 := bstep (se 2 (by rfl) ⟨1316634, by rfl⟩ : syracuseStep 3511025 = 2633269) B2633269
theorem B2495245 : Blo 818347 2495245 := bstep (se 3 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 2495245 = 935717) B935717
theorem B922387 : Blo 818347 922387 := bstep (se 1 (by rfl) ⟨691790, by rfl⟩ : syracuseStep 922387 = 1383581) B1383581
theorem B4428593 : Blo 818347 4428593 := bstep (se 2 (by rfl) ⟨1660722, by rfl⟩ : syracuseStep 4428593 = 3321445) B3321445
theorem B1381171 : Blo 818347 1381171 := bstep (se 1 (by rfl) ⟨1035878, by rfl⟩ : syracuseStep 1381171 = 2071757) B2071757
theorem B1971011 : Blo 818347 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B922531 : Blo 818347 922531 := bstep (se 1 (by rfl) ⟨691898, by rfl⟩ : syracuseStep 922531 = 1383797) B1383797
theorem B1381313 : Blo 818347 1381313 := bstep (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) B1035985
theorem B2331661 : Blo 818347 2331661 := bstep (se 3 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 2331661 = 874373) B874373
theorem B3118115 : Blo 818347 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B922675 : Blo 818347 922675 := bstep (se 1 (by rfl) ⟨692006, by rfl⟩ : syracuseStep 922675 = 1384013) B1384013
theorem B1381441 : Blo 818347 1381441 := bstep (se 2 (by rfl) ⟨518040, by rfl⟩ : syracuseStep 1381441 = 1036081) B1036081
theorem B1381475 : Blo 818347 1381475 := bstep (se 1 (by rfl) ⟨1036106, by rfl⟩ : syracuseStep 1381475 = 2072213) B2072213
theorem B5608547 : Blo 818347 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B1578097 : Blo 818347 1578097 := bstep (se 2 (by rfl) ⟨591786, by rfl⟩ : syracuseStep 1578097 = 1183573) B1183573
theorem B2331821 : Blo 818347 2331821 := bstep (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) B874433
theorem B922819 : Blo 818347 922819 := bstep (se 1 (by rfl) ⟨692114, by rfl⟩ : syracuseStep 922819 = 1384229) B1384229
theorem B9999557 : Blo 818347 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B1381603 : Blo 818347 1381603 := bstep (se 1 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 1381603 = 2072405) B2072405
theorem B1316147 : Blo 818347 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B922963 : Blo 818347 922963 := bstep (se 1 (by rfl) ⟨692222, by rfl⟩ : syracuseStep 922963 = 1384445) B1384445
theorem B2332003 : Blo 818347 2332003 := bstep (se 1 (by rfl) ⟨1749002, by rfl⟩ : syracuseStep 2332003 = 3498005) B3498005
theorem B1381745 : Blo 818347 1381745 := bstep (se 2 (by rfl) ⟨518154, by rfl⟩ : syracuseStep 1381745 = 1036309) B1036309
theorem B1316225 : Blo 818347 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B923107 : Blo 818347 923107 := bstep (se 1 (by rfl) ⟨692330, by rfl⟩ : syracuseStep 923107 = 1384661) B1384661
theorem B1381873 : Blo 818347 1381873 := bstep (se 2 (by rfl) ⟨518202, by rfl⟩ : syracuseStep 1381873 = 1036405) B1036405
theorem B1381907 : Blo 818347 1381907 := bstep (se 1 (by rfl) ⟨1036430, by rfl⟩ : syracuseStep 1381907 = 2072861) B2072861
theorem B1316449 : Blo 818347 1316449 := bstep (se 2 (by rfl) ⟨493668, by rfl⟩ : syracuseStep 1316449 = 987337) B987337
theorem B923251 : Blo 818347 923251 := bstep (se 1 (by rfl) ⟨692438, by rfl⟩ : syracuseStep 923251 = 1384877) B1384877
theorem B1382035 : Blo 818347 1382035 := bstep (se 1 (by rfl) ⟨1036526, by rfl⟩ : syracuseStep 1382035 = 2073053) B2073053
theorem B3118769 : Blo 818347 3118769 := bstep (se 2 (by rfl) ⟨1169538, by rfl⟩ : syracuseStep 3118769 = 2339077) B2339077
theorem B1971953 : Blo 818347 1971953 := bstep (se 2 (by rfl) ⟨739482, by rfl⟩ : syracuseStep 1971953 = 1478965) B1478965
theorem B2103043 : Blo 818347 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B923395 : Blo 818347 923395 := bstep (se 1 (by rfl) ⟨692546, by rfl⟩ : syracuseStep 923395 = 1385093) B1385093
theorem B1382177 : Blo 818347 1382177 := bstep (se 2 (by rfl) ⟨518316, by rfl⟩ : syracuseStep 1382177 = 1036633) B1036633
theorem B923539 : Blo 818347 923539 := bstep (se 1 (by rfl) ⟨692654, by rfl⟩ : syracuseStep 923539 = 1385309) B1385309
theorem B1382305 : Blo 818347 1382305 := bstep (se 2 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 1382305 = 1036729) B1036729
theorem B1382339 : Blo 818347 1382339 := bstep (se 1 (by rfl) ⟨1036754, by rfl⟩ : syracuseStep 1382339 = 2073509) B2073509
theorem B923683 : Blo 818347 923683 := bstep (se 1 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 923683 = 1385525) B1385525
theorem B1382467 : Blo 818347 1382467 := bstep (se 1 (by rfl) ⟨1036850, by rfl⟩ : syracuseStep 1382467 = 2073701) B2073701
theorem B1054867 : Blo 818347 1054867 := bstep (se 1 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 1054867 = 1582301) B1582301
theorem B923827 : Blo 818347 923827 := bstep (se 1 (by rfl) ⟨692870, by rfl⟩ : syracuseStep 923827 = 1385741) B1385741
theorem B1382609 : Blo 818347 1382609 := bstep (se 2 (by rfl) ⟨518478, by rfl⟩ : syracuseStep 1382609 = 1036957) B1036957
theorem B1579331 : Blo 818347 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B923971 : Blo 818347 923971 := bstep (se 1 (by rfl) ⟨692978, by rfl⟩ : syracuseStep 923971 = 1385957) B1385957
theorem B1841489 : Blo 818347 1841489 := bstep (se 2 (by rfl) ⟨690558, by rfl⟩ : syracuseStep 1841489 = 1381117) B1381117
theorem B1382737 : Blo 818347 1382737 := bstep (se 2 (by rfl) ⟨518526, by rfl⟩ : syracuseStep 1382737 = 1037053) B1037053
theorem B1481041 : Blo 818347 1481041 := bstep (se 2 (by rfl) ⟨555390, by rfl⟩ : syracuseStep 1481041 = 1110781) B1110781
theorem B1841507 : Blo 818347 1841507 := bstep (se 1 (by rfl) ⟨1381130, by rfl⟩ : syracuseStep 1841507 = 2762261) B2762261
theorem B5249393 : Blo 818347 5249393 := bstep (se 2 (by rfl) ⟨1968522, by rfl⟩ : syracuseStep 5249393 = 3937045) B3937045
theorem B1382771 : Blo 818347 1382771 := bstep (se 1 (by rfl) ⟨1037078, by rfl⟩ : syracuseStep 1382771 = 2074157) B2074157
theorem B924115 : Blo 818347 924115 := bstep (se 1 (by rfl) ⟨693086, by rfl⟩ : syracuseStep 924115 = 1386173) B1386173
theorem B1382899 : Blo 818347 1382899 := bstep (se 1 (by rfl) ⟨1037174, by rfl⟩ : syracuseStep 1382899 = 2074349) B2074349
theorem B8854069 : Blo 818347 8854069 := bstep (se 5 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 8854069 = 830069) B830069
theorem B924259 : Blo 818347 924259 := bstep (se 1 (by rfl) ⟨693194, by rfl⟩ : syracuseStep 924259 = 1386389) B1386389
theorem B1841777 : Blo 818347 1841777 := bstep (se 2 (by rfl) ⟨690666, by rfl⟩ : syracuseStep 1841777 = 1381333) B1381333
theorem B1383041 : Blo 818347 1383041 := bstep (se 2 (by rfl) ⟨518640, by rfl⟩ : syracuseStep 1383041 = 1037281) B1037281
theorem B1841795 : Blo 818347 1841795 := bstep (se 1 (by rfl) ⟨1381346, by rfl⟩ : syracuseStep 1841795 = 2762693) B2762693
theorem B2333393 : Blo 818347 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B4004579 : Blo 818347 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B924403 : Blo 818347 924403 := bstep (se 1 (by rfl) ⟨693302, by rfl⟩ : syracuseStep 924403 = 1386605) B1386605
theorem B1383169 : Blo 818347 1383169 := bstep (se 2 (by rfl) ⟨518688, by rfl⟩ : syracuseStep 1383169 = 1037377) B1037377
theorem B1383203 : Blo 818347 1383203 := bstep (se 1 (by rfl) ⟨1037402, by rfl⟩ : syracuseStep 1383203 = 2074805) B2074805
theorem B924547 : Blo 818347 924547 := bstep (se 1 (by rfl) ⟨693410, by rfl⟩ : syracuseStep 924547 = 1386821) B1386821
theorem B1842065 : Blo 818347 1842065 := bstep (se 2 (by rfl) ⟨690774, by rfl⟩ : syracuseStep 1842065 = 1381549) B1381549
theorem B1842083 : Blo 818347 1842083 := bstep (se 1 (by rfl) ⟨1381562, by rfl⟩ : syracuseStep 1842083 = 2763125) B2763125
theorem B1383331 : Blo 818347 1383331 := bstep (se 1 (by rfl) ⟨1037498, by rfl⟩ : syracuseStep 1383331 = 2074997) B2074997
theorem B924691 : Blo 818347 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B2104355 : Blo 818347 2104355 := bstep (se 1 (by rfl) ⟨1578266, by rfl⟩ : syracuseStep 2104355 = 3156533) B3156533
theorem B1383473 : Blo 818347 1383473 := bstep (se 2 (by rfl) ⟨518802, by rfl⟩ : syracuseStep 1383473 = 1037605) B1037605
theorem B3120227 : Blo 818347 3120227 := bstep (se 1 (by rfl) ⟨2340170, by rfl⟩ : syracuseStep 3120227 = 4680341) B4680341
theorem B3120241 : Blo 818347 3120241 := bstep (se 2 (by rfl) ⟨1170090, by rfl⟩ : syracuseStep 3120241 = 2340181) B2340181
theorem B924835 : Blo 818347 924835 := bstep (se 1 (by rfl) ⟨693626, by rfl⟩ : syracuseStep 924835 = 1387253) B1387253
theorem B1842353 : Blo 818347 1842353 := bstep (se 2 (by rfl) ⟨690882, by rfl⟩ : syracuseStep 1842353 = 1381765) B1381765
theorem B1383601 : Blo 818347 1383601 := bstep (se 2 (by rfl) ⟨518850, by rfl⟩ : syracuseStep 1383601 = 1037701) B1037701
theorem B1842371 : Blo 818347 1842371 := bstep (se 1 (by rfl) ⟨1381778, by rfl⟩ : syracuseStep 1842371 = 2763557) B2763557
theorem B1383635 : Blo 818347 1383635 := bstep (se 1 (by rfl) ⟨1037726, by rfl⟩ : syracuseStep 1383635 = 2075453) B2075453
theorem B924979 : Blo 818347 924979 := bstep (se 1 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 924979 = 1387469) B1387469
theorem B2071889 : Blo 818347 2071889 := bstep (se 2 (by rfl) ⟨776958, by rfl⟩ : syracuseStep 2071889 = 1553917) B1553917
theorem B1383763 : Blo 818347 1383763 := bstep (se 1 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 1383763 = 2075645) B2075645
theorem B2071939 : Blo 818347 2071939 := bstep (se 1 (by rfl) ⟨1553954, by rfl⟩ : syracuseStep 2071939 = 3107909) B3107909
theorem B925123 : Blo 818347 925123 := bstep (se 1 (by rfl) ⟨693842, by rfl⟩ : syracuseStep 925123 = 1387685) B1387685
theorem B1842641 : Blo 818347 1842641 := bstep (se 2 (by rfl) ⟨690990, by rfl⟩ : syracuseStep 1842641 = 1381981) B1381981
theorem B1383905 : Blo 818347 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B1842659 : Blo 818347 1842659 := bstep (se 1 (by rfl) ⟨1381994, by rfl⟩ : syracuseStep 1842659 = 2763989) B2763989
theorem B6659597 : Blo 818347 6659597 := bstep (se 3 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 6659597 = 2497349) B2497349
theorem B2072081 : Blo 818347 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B2629169 : Blo 818347 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B1384033 : Blo 818347 1384033 := bstep (se 2 (by rfl) ⟨519012, by rfl⟩ : syracuseStep 1384033 = 1038025) B1038025
theorem B2629219 : Blo 818347 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B1384067 : Blo 818347 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B2334349 : Blo 818347 2334349 := bstep (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) B875381
theorem B1842929 : Blo 818347 1842929 := bstep (se 2 (by rfl) ⟨691098, by rfl⟩ : syracuseStep 1842929 = 1382197) B1382197
theorem B1842947 : Blo 818347 1842947 := bstep (se 1 (by rfl) ⟨1382210, by rfl⟩ : syracuseStep 1842947 = 2764421) B2764421
theorem B1384195 : Blo 818347 1384195 := bstep (se 1 (by rfl) ⟨1038146, by rfl⟩ : syracuseStep 1384195 = 2076293) B2076293
theorem B64659221 : Blo 818347 64659221 := bstep (se 6 (by rfl) ⟨1515450, by rfl⟩ : syracuseStep 64659221 = 3030901) B3030901
theorem B5250851 : Blo 818347 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B2334577 : Blo 818347 2334577 := bstep (se 2 (by rfl) ⟨875466, by rfl⟩ : syracuseStep 2334577 = 1750933) B1750933
theorem B1384337 : Blo 818347 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B1843217 : Blo 818347 1843217 := bstep (se 2 (by rfl) ⟨691206, by rfl⟩ : syracuseStep 1843217 = 1382413) B1382413
theorem B2334737 : Blo 818347 2334737 := bstep (se 2 (by rfl) ⟨875526, by rfl⟩ : syracuseStep 2334737 = 1751053) B1751053
theorem B1384465 : Blo 818347 1384465 := bstep (se 2 (by rfl) ⟨519174, by rfl⟩ : syracuseStep 1384465 = 1038349) B1038349
theorem B1843235 : Blo 818347 1843235 := bstep (se 1 (by rfl) ⟨1382426, by rfl⟩ : syracuseStep 1843235 = 2764853) B2764853
theorem B1384499 : Blo 818347 1384499 := bstep (se 1 (by rfl) ⟨1038374, by rfl⟩ : syracuseStep 1384499 = 2076749) B2076749
theorem B2334851 : Blo 818347 2334851 := bstep (se 1 (by rfl) ⟨1751138, by rfl⟩ : syracuseStep 2334851 = 3502277) B3502277
theorem B1384627 : Blo 818347 1384627 := bstep (se 1 (by rfl) ⟨1038470, by rfl⟩ : syracuseStep 1384627 = 2076941) B2076941
theorem B2662627 : Blo 818347 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B1843505 : Blo 818347 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B1384769 : Blo 818347 1384769 := bstep (se 2 (by rfl) ⟨519288, by rfl⟩ : syracuseStep 1384769 = 1038577) B1038577
theorem B1843523 : Blo 818347 1843523 := bstep (se 1 (by rfl) ⟨1382642, by rfl⟩ : syracuseStep 1843523 = 2765285) B2765285
theorem B7119173 : Blo 818347 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B2498915 : Blo 818347 2498915 := bstep (se 1 (by rfl) ⟨1874186, by rfl⟩ : syracuseStep 2498915 = 3748373) B3748373
theorem B2990513 : Blo 818347 2990513 := bstep (se 2 (by rfl) ⟨1121442, by rfl⟩ : syracuseStep 2990513 = 2242885) B2242885
theorem B2630065 : Blo 818347 2630065 := bstep (se 2 (by rfl) ⟨986274, by rfl⟩ : syracuseStep 2630065 = 1972549) B1972549
theorem B1384897 : Blo 818347 1384897 := bstep (se 2 (by rfl) ⟨519336, by rfl⟩ : syracuseStep 1384897 = 1038673) B1038673
theorem B1384931 : Blo 818347 1384931 := bstep (se 1 (by rfl) ⟨1038698, by rfl⟩ : syracuseStep 1384931 = 2077397) B2077397
theorem B2073073 : Blo 818347 2073073 := bstep (se 2 (by rfl) ⟨777402, by rfl⟩ : syracuseStep 2073073 = 1554805) B1554805
theorem B3121699 : Blo 818347 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B1843793 : Blo 818347 1843793 := bstep (se 2 (by rfl) ⟨691422, by rfl⟩ : syracuseStep 1843793 = 1382845) B1382845
theorem B1843811 : Blo 818347 1843811 := bstep (se 1 (by rfl) ⟨1382858, by rfl⟩ : syracuseStep 1843811 = 2765717) B2765717
theorem B1385059 : Blo 818347 1385059 := bstep (se 1 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 1385059 = 2077589) B2077589
theorem B1385201 : Blo 818347 1385201 := bstep (se 2 (by rfl) ⟨519450, by rfl⟩ : syracuseStep 1385201 = 1038901) B1038901
theorem B2073347 : Blo 818347 2073347 := bstep (se 1 (by rfl) ⟨1555010, by rfl⟩ : syracuseStep 2073347 = 3110021) B3110021
theorem B6234893 : Blo 818347 6234893 := bstep (se 3 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 6234893 = 2338085) B2338085
theorem B5907269 : Blo 818347 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B1844081 : Blo 818347 1844081 := bstep (se 2 (by rfl) ⟨691530, by rfl⟩ : syracuseStep 1844081 = 1383061) B1383061
theorem B1385329 : Blo 818347 1385329 := bstep (se 2 (by rfl) ⟨519498, by rfl⟩ : syracuseStep 1385329 = 1038997) B1038997
theorem B1844099 : Blo 818347 1844099 := bstep (se 1 (by rfl) ⟨1383074, by rfl⟩ : syracuseStep 1844099 = 2766149) B2766149
theorem B1385363 : Blo 818347 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B2073539 : Blo 818347 2073539 := bstep (se 1 (by rfl) ⟨1555154, by rfl⟩ : syracuseStep 2073539 = 3110309) B3110309
theorem B1385491 : Blo 818347 1385491 := bstep (se 1 (by rfl) ⟨1039118, by rfl⟩ : syracuseStep 1385491 = 2078237) B2078237
theorem B7021637 : Blo 818347 7021637 := bstep (se 4 (by rfl) ⟨658278, by rfl⟩ : syracuseStep 7021637 = 1316557) B1316557
theorem B2335853 : Blo 818347 2335853 := bstep (se 3 (by rfl) ⟨437972, by rfl⟩ : syracuseStep 2335853 = 875945) B875945
theorem B1844369 : Blo 818347 1844369 := bstep (se 2 (by rfl) ⟨691638, by rfl⟩ : syracuseStep 1844369 = 1383277) B1383277
theorem B1385633 : Blo 818347 1385633 := bstep (se 2 (by rfl) ⟨519612, by rfl⟩ : syracuseStep 1385633 = 1039225) B1039225
theorem B1844387 : Blo 818347 1844387 := bstep (se 1 (by rfl) ⟨1383290, by rfl⟩ : syracuseStep 1844387 = 2766581) B2766581
theorem B2761937 : Blo 818347 2761937 := bstep (se 2 (by rfl) ⟨1035726, by rfl⟩ : syracuseStep 2761937 = 2071453) B2071453
theorem B2958563 : Blo 818347 2958563 := bstep (se 1 (by rfl) ⟨2218922, by rfl⟩ : syracuseStep 2958563 = 4437845) B4437845
theorem B1385761 : Blo 818347 1385761 := bstep (se 2 (by rfl) ⟨519660, by rfl⟩ : syracuseStep 1385761 = 1039321) B1039321
theorem B2336035 : Blo 818347 2336035 := bstep (se 1 (by rfl) ⟨1752026, by rfl⟩ : syracuseStep 2336035 = 3504053) B3504053
theorem B1385795 : Blo 818347 1385795 := bstep (se 1 (by rfl) ⟨1039346, by rfl⟩ : syracuseStep 1385795 = 2078693) B2078693
theorem B1844657 : Blo 818347 1844657 := bstep (se 2 (by rfl) ⟨691746, by rfl⟩ : syracuseStep 1844657 = 1383493) B1383493
theorem B1844675 : Blo 818347 1844675 := bstep (se 1 (by rfl) ⟨1383506, by rfl⟩ : syracuseStep 1844675 = 2767013) B2767013
theorem B2336195 : Blo 818347 2336195 := bstep (se 1 (by rfl) ⟨1752146, by rfl⟩ : syracuseStep 2336195 = 3504293) B3504293
theorem B1385923 : Blo 818347 1385923 := bstep (se 1 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 1385923 = 2078885) B2078885
theorem B1353203 : Blo 818347 1353203 := bstep (se 1 (by rfl) ⟨1014902, by rfl⟩ : syracuseStep 1353203 = 2029805) B2029805
theorem B1386065 : Blo 818347 1386065 := bstep (se 2 (by rfl) ⟨519774, by rfl⟩ : syracuseStep 1386065 = 1039549) B1039549
theorem B1844945 : Blo 818347 1844945 := bstep (se 2 (by rfl) ⟨691854, by rfl⟩ : syracuseStep 1844945 = 1383709) B1383709
theorem B1386193 : Blo 818347 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B1844963 : Blo 818347 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B2762477 : Blo 818347 2762477 := bstep (se 3 (by rfl) ⟨517964, by rfl⟩ : syracuseStep 2762477 = 1035929) B1035929
theorem B7022321 : Blo 818347 7022321 := bstep (se 2 (by rfl) ⟨2633370, by rfl⟩ : syracuseStep 7022321 = 5266741) B5266741
theorem B1386227 : Blo 818347 1386227 := bstep (se 1 (by rfl) ⟨1039670, by rfl⟩ : syracuseStep 1386227 = 2079341) B2079341
theorem B2762531 : Blo 818347 2762531 := bstep (se 1 (by rfl) ⟨2071898, by rfl⟩ : syracuseStep 2762531 = 4143797) B4143797
theorem B2074481 : Blo 818347 2074481 := bstep (se 2 (by rfl) ⟨777930, by rfl⟩ : syracuseStep 2074481 = 1555861) B1555861
theorem B1386355 : Blo 818347 1386355 := bstep (se 1 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 1386355 = 2079533) B2079533
theorem B2074531 : Blo 818347 2074531 := bstep (se 1 (by rfl) ⟨1555898, by rfl⟩ : syracuseStep 2074531 = 3111797) B3111797
theorem B2631629 : Blo 818347 2631629 := bstep (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) B986861
theorem B1845233 : Blo 818347 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B1386497 : Blo 818347 1386497 := bstep (se 2 (by rfl) ⟨519936, by rfl⟩ : syracuseStep 1386497 = 1039873) B1039873
theorem B1845251 : Blo 818347 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B2762801 : Blo 818347 2762801 := bstep (se 2 (by rfl) ⟨1036050, by rfl⟩ : syracuseStep 2762801 = 2072101) B2072101
theorem B2074673 : Blo 818347 2074673 := bstep (se 2 (by rfl) ⟨778002, by rfl⟩ : syracuseStep 2074673 = 1556005) B1556005
theorem B1386625 : Blo 818347 1386625 := bstep (se 2 (by rfl) ⟨519984, by rfl⟩ : syracuseStep 1386625 = 1039969) B1039969
theorem B1386659 : Blo 818347 1386659 := bstep (se 1 (by rfl) ⟨1039994, by rfl⟩ : syracuseStep 1386659 = 2079989) B2079989
theorem B8890565 : Blo 818347 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B1845521 : Blo 818347 1845521 := bstep (se 2 (by rfl) ⟨692070, by rfl⟩ : syracuseStep 1845521 = 1384141) B1384141
theorem B4434211 : Blo 818347 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B1845539 : Blo 818347 1845539 := bstep (se 1 (by rfl) ⟨1384154, by rfl⟩ : syracuseStep 1845539 = 2768309) B2768309
theorem B1386787 : Blo 818347 1386787 := bstep (se 1 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 1386787 = 2080181) B2080181
theorem B1386929 : Blo 818347 1386929 := bstep (se 2 (by rfl) ⟨520098, by rfl⟩ : syracuseStep 1386929 = 1040197) B1040197
theorem B2337265 : Blo 818347 2337265 := bstep (se 2 (by rfl) ⟨876474, by rfl⟩ : syracuseStep 2337265 = 1752949) B1752949
theorem B1845809 : Blo 818347 1845809 := bstep (se 2 (by rfl) ⟨692178, by rfl⟩ : syracuseStep 1845809 = 1384357) B1384357
theorem B1387057 : Blo 818347 1387057 := bstep (se 2 (by rfl) ⟨520146, by rfl⟩ : syracuseStep 1387057 = 1040293) B1040293
theorem B1845827 : Blo 818347 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B2763341 : Blo 818347 2763341 := bstep (se 3 (by rfl) ⟨518126, by rfl⟩ : syracuseStep 2763341 = 1036253) B1036253
theorem B1387091 : Blo 818347 1387091 := bstep (se 1 (by rfl) ⟨1040318, by rfl⟩ : syracuseStep 1387091 = 2080637) B2080637
theorem B2763395 : Blo 818347 2763395 := bstep (se 1 (by rfl) ⟨2072546, by rfl⟩ : syracuseStep 2763395 = 4145093) B4145093
theorem B11250373 : Blo 818347 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B1387219 : Blo 818347 1387219 := bstep (se 1 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 1387219 = 2080829) B2080829
theorem B1846097 : Blo 818347 1846097 := bstep (se 2 (by rfl) ⟨692286, by rfl⟩ : syracuseStep 1846097 = 1384573) B1384573
theorem B1387361 : Blo 818347 1387361 := bstep (se 2 (by rfl) ⟨520260, by rfl⟩ : syracuseStep 1387361 = 1040521) B1040521
theorem B1846115 : Blo 818347 1846115 := bstep (se 1 (by rfl) ⟨1384586, by rfl⟩ : syracuseStep 1846115 = 2769173) B2769173
theorem B2763665 : Blo 818347 2763665 := bstep (se 2 (by rfl) ⟨1036374, by rfl⟩ : syracuseStep 2763665 = 2072749) B2072749
theorem B1387489 : Blo 818347 1387489 := bstep (se 2 (by rfl) ⟨520308, by rfl⟩ : syracuseStep 1387489 = 1040617) B1040617
theorem B2370541 : Blo 818347 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B1387523 : Blo 818347 1387523 := bstep (se 1 (by rfl) ⟨1040642, by rfl⟩ : syracuseStep 1387523 = 2081285) B2081285
theorem B2075665 : Blo 818347 2075665 := bstep (se 2 (by rfl) ⟨778374, by rfl⟩ : syracuseStep 2075665 = 1556749) B1556749
theorem B1846385 : Blo 818347 1846385 := bstep (se 2 (by rfl) ⟨692394, by rfl⟩ : syracuseStep 1846385 = 1384789) B1384789
theorem B1846403 : Blo 818347 1846403 := bstep (se 1 (by rfl) ⟨1384802, by rfl⟩ : syracuseStep 1846403 = 2769605) B2769605
theorem B1387651 : Blo 818347 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B14036165 : Blo 818347 14036165 := bstep (se 4 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 14036165 = 2631781) B2631781
theorem B2075939 : Blo 818347 2075939 := bstep (se 1 (by rfl) ⟨1556954, by rfl⟩ : syracuseStep 2075939 = 3113909) B3113909
theorem B5254541 : Blo 818347 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B1846673 : Blo 818347 1846673 := bstep (se 2 (by rfl) ⟨692502, by rfl⟩ : syracuseStep 1846673 = 1385005) B1385005
theorem B1846691 : Blo 818347 1846691 := bstep (se 1 (by rfl) ⟨1385018, by rfl⟩ : syracuseStep 1846691 = 2770037) B2770037
theorem B2764205 : Blo 818347 2764205 := bstep (se 3 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 2764205 = 1036577) B1036577
theorem B2698705 : Blo 818347 2698705 := bstep (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) B2024029
theorem B2764259 : Blo 818347 2764259 := bstep (se 1 (by rfl) ⟨2073194, by rfl⟩ : syracuseStep 2764259 = 4146389) B4146389
theorem B2076131 : Blo 818347 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B4435469 : Blo 818347 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B6237809 : Blo 818347 6237809 := bstep (se 2 (by rfl) ⟨2339178, by rfl⟩ : syracuseStep 6237809 = 4678357) B4678357
theorem B1846961 : Blo 818347 1846961 := bstep (se 2 (by rfl) ⟨692610, by rfl⟩ : syracuseStep 1846961 = 1385221) B1385221
theorem B1846979 : Blo 818347 1846979 := bstep (se 1 (by rfl) ⟨1385234, by rfl⟩ : syracuseStep 1846979 = 2770469) B2770469
theorem B2633411 : Blo 818347 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B2338541 : Blo 818347 2338541 := bstep (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) B876953
theorem B2764529 : Blo 818347 2764529 := bstep (se 2 (by rfl) ⟨1036698, by rfl⟩ : syracuseStep 2764529 = 2073397) B2073397
theorem B1093505 : Blo 818347 1093505 := bstep (se 2 (by rfl) ⟨410064, by rfl⟩ : syracuseStep 1093505 = 820129) B820129
theorem B2338723 : Blo 818347 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1847249 : Blo 818347 1847249 := bstep (se 2 (by rfl) ⟨692718, by rfl⟩ : syracuseStep 1847249 = 1385437) B1385437
theorem B2338769 : Blo 818347 2338769 := bstep (se 2 (by rfl) ⟨877038, by rfl⟩ : syracuseStep 2338769 = 1754077) B1754077
theorem B1847267 : Blo 818347 1847267 := bstep (se 1 (by rfl) ⟨1385450, by rfl⟩ : syracuseStep 1847267 = 2770901) B2770901
theorem B3944483 : Blo 818347 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B5910641 : Blo 818347 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B1847537 : Blo 818347 1847537 := bstep (se 2 (by rfl) ⟨692826, by rfl⟩ : syracuseStep 1847537 = 1385653) B1385653
theorem B1749251 : Blo 818347 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B1847555 : Blo 818347 1847555 := bstep (se 1 (by rfl) ⟨1385666, by rfl⟩ : syracuseStep 1847555 = 2771333) B2771333
theorem B2765069 : Blo 818347 2765069 := bstep (se 3 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 2765069 = 1036901) B1036901
theorem B3551501 : Blo 818347 3551501 := bstep (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) B1331813
theorem B2765123 : Blo 818347 2765123 := bstep (se 1 (by rfl) ⟨2073842, by rfl⟩ : syracuseStep 2765123 = 4147685) B4147685
theorem B2077073 : Blo 818347 2077073 := bstep (se 2 (by rfl) ⟨778902, by rfl⟩ : syracuseStep 2077073 = 1557805) B1557805
theorem B2077123 : Blo 818347 2077123 := bstep (se 1 (by rfl) ⟨1557842, by rfl⟩ : syracuseStep 2077123 = 3115685) B3115685
theorem B1847825 : Blo 818347 1847825 := bstep (se 2 (by rfl) ⟨692934, by rfl⟩ : syracuseStep 1847825 = 1385869) B1385869
theorem B3551779 : Blo 818347 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B1847843 : Blo 818347 1847843 := bstep (se 1 (by rfl) ⟨1385882, by rfl⟩ : syracuseStep 1847843 = 2771765) B2771765
theorem B2765393 : Blo 818347 2765393 := bstep (se 2 (by rfl) ⟨1037022, by rfl⟩ : syracuseStep 2765393 = 2074045) B2074045
theorem B2077265 : Blo 818347 2077265 := bstep (se 2 (by rfl) ⟨778974, by rfl⟩ : syracuseStep 2077265 = 1557949) B1557949
theorem B1848113 : Blo 818347 1848113 := bstep (se 2 (by rfl) ⟨693042, by rfl⟩ : syracuseStep 1848113 = 1386085) B1386085
theorem B1848131 : Blo 818347 1848131 := bstep (se 1 (by rfl) ⟨1386098, by rfl⟩ : syracuseStep 1848131 = 2772197) B2772197
theorem B2667377 : Blo 818347 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B1848401 : Blo 818347 1848401 := bstep (se 2 (by rfl) ⟨693150, by rfl⟩ : syracuseStep 1848401 = 1386301) B1386301
theorem B1848419 : Blo 818347 1848419 := bstep (se 1 (by rfl) ⟨1386314, by rfl⟩ : syracuseStep 1848419 = 2772629) B2772629
theorem B2765933 : Blo 818347 2765933 := bstep (se 3 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 2765933 = 1037225) B1037225
theorem B2765987 : Blo 818347 2765987 := bstep (se 1 (by rfl) ⟨2074490, by rfl⟩ : syracuseStep 2765987 = 4148981) B4148981
theorem B11842787 : Blo 818347 11842787 := bstep (se 1 (by rfl) ⟨8882090, by rfl⟩ : syracuseStep 11842787 = 17764181) B17764181
theorem B1553681 : Blo 818347 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B4666693 : Blo 818347 4666693 := bstep (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) B875005
theorem B3945827 : Blo 818347 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B1848689 : Blo 818347 1848689 := bstep (se 2 (by rfl) ⟨693258, by rfl⟩ : syracuseStep 1848689 = 1386517) B1386517
theorem B1848707 : Blo 818347 1848707 := bstep (se 1 (by rfl) ⟨1386530, by rfl⟩ : syracuseStep 1848707 = 2773061) B2773061
theorem B2340227 : Blo 818347 2340227 := bstep (se 1 (by rfl) ⟨1755170, by rfl⟩ : syracuseStep 2340227 = 3510341) B3510341
theorem B2766257 : Blo 818347 2766257 := bstep (se 2 (by rfl) ⟨1037346, by rfl⟩ : syracuseStep 2766257 = 2074693) B2074693
theorem B1750481 : Blo 818347 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B2078257 : Blo 818347 2078257 := bstep (se 2 (by rfl) ⟨779346, by rfl⟩ : syracuseStep 2078257 = 1558693) B1558693
theorem B1848977 : Blo 818347 1848977 := bstep (se 2 (by rfl) ⟨693366, by rfl⟩ : syracuseStep 1848977 = 1386733) B1386733
theorem B1848995 : Blo 818347 1848995 := bstep (se 1 (by rfl) ⟨1386746, by rfl⟩ : syracuseStep 1848995 = 2773493) B2773493
theorem B2078531 : Blo 818347 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1849265 : Blo 818347 1849265 := bstep (se 2 (by rfl) ⟨693474, by rfl⟩ : syracuseStep 1849265 = 1386949) B1386949
theorem B1849283 : Blo 818347 1849283 := bstep (se 1 (by rfl) ⟨1386962, by rfl⟩ : syracuseStep 1849283 = 2773925) B2773925
theorem B2766797 : Blo 818347 2766797 := bstep (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) B1037549
theorem B1554403 : Blo 818347 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B2766851 : Blo 818347 2766851 := bstep (se 1 (by rfl) ⟨2075138, by rfl⟩ : syracuseStep 2766851 = 4150277) B4150277
theorem B2078723 : Blo 818347 2078723 := bstep (se 1 (by rfl) ⟨1559042, by rfl⟩ : syracuseStep 2078723 = 3118085) B3118085
theorem B14039237 : Blo 818347 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B1849553 : Blo 818347 1849553 := bstep (se 2 (by rfl) ⟨693582, by rfl⟩ : syracuseStep 1849553 = 1387165) B1387165
theorem B1849571 : Blo 818347 1849571 := bstep (se 1 (by rfl) ⟨1387178, by rfl⟩ : syracuseStep 1849571 = 2774357) B2774357
theorem B2767121 : Blo 818347 2767121 := bstep (se 2 (by rfl) ⟨1037670, by rfl⟩ : syracuseStep 2767121 = 2075341) B2075341
theorem B1751377 : Blo 818347 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B1751395 : Blo 818347 1751395 := bstep (se 1 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 1751395 = 2627093) B2627093
theorem B4143473 : Blo 818347 4143473 := bstep (se 2 (by rfl) ⟨1553802, by rfl⟩ : syracuseStep 4143473 = 3107605) B3107605
theorem B1554851 : Blo 818347 1554851 := bstep (se 1 (by rfl) ⟨1166138, by rfl⟩ : syracuseStep 1554851 = 2332277) B2332277
theorem B5257669 : Blo 818347 5257669 := bstep (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) B985813
theorem B1849841 : Blo 818347 1849841 := bstep (se 2 (by rfl) ⟨693690, by rfl⟩ : syracuseStep 1849841 = 1387381) B1387381
theorem B1849859 : Blo 818347 1849859 := bstep (se 1 (by rfl) ⟨1387394, by rfl⟩ : syracuseStep 1849859 = 2774789) B2774789
theorem B3947057 : Blo 818347 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B10500677 : Blo 818347 10500677 := bstep (se 4 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 10500677 = 1968877) B1968877
theorem B2341457 : Blo 818347 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B3324557 : Blo 818347 3324557 := bstep (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) B1246709
theorem B1555139 : Blo 818347 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1227521 : Blo 818347 1227521 := bstep (se 2 (by rfl) ⟨460320, by rfl⟩ : syracuseStep 1227521 = 920641) B920641
theorem B1850129 : Blo 818347 1850129 := bstep (se 2 (by rfl) ⟨693798, by rfl⟩ : syracuseStep 1850129 = 1387597) B1387597
theorem B1227539 : Blo 818347 1227539 := bstep (se 1 (by rfl) ⟨920654, by rfl⟩ : syracuseStep 1227539 = 1841309) B1841309
theorem B1850147 : Blo 818347 1850147 := bstep (se 1 (by rfl) ⟨1387610, by rfl⟩ : syracuseStep 1850147 = 2775221) B2775221
theorem B2767661 : Blo 818347 2767661 := bstep (se 3 (by rfl) ⟨518936, by rfl⟩ : syracuseStep 2767661 = 1037873) B1037873
theorem B1227569 : Blo 818347 1227569 := bstep (se 2 (by rfl) ⟨460338, by rfl⟩ : syracuseStep 1227569 = 920677) B920677
theorem B10533685 : Blo 818347 10533685 := bstep (se 5 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 10533685 = 987533) B987533
theorem B1227587 : Blo 818347 1227587 := bstep (se 1 (by rfl) ⟨920690, by rfl⟩ : syracuseStep 1227587 = 1841381) B1841381
theorem B1227617 : Blo 818347 1227617 := bstep (se 2 (by rfl) ⟨460356, by rfl⟩ : syracuseStep 1227617 = 920713) B920713
theorem B1424225 : Blo 818347 1424225 := bstep (se 2 (by rfl) ⟨534084, by rfl⟩ : syracuseStep 1424225 = 1068169) B1068169
theorem B2767715 : Blo 818347 2767715 := bstep (se 1 (by rfl) ⟨2075786, by rfl⟩ : syracuseStep 2767715 = 4151573) B4151573
theorem B3554147 : Blo 818347 3554147 := bstep (se 1 (by rfl) ⟨2665610, by rfl⟩ : syracuseStep 3554147 = 5331221) B5331221
theorem B1227635 : Blo 818347 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B1227665 : Blo 818347 1227665 := bstep (se 2 (by rfl) ⟨460374, by rfl⟩ : syracuseStep 1227665 = 920749) B920749
theorem B1227683 : Blo 818347 1227683 := bstep (se 1 (by rfl) ⟨920762, by rfl⟩ : syracuseStep 1227683 = 1841525) B1841525
theorem B2079665 : Blo 818347 2079665 := bstep (se 2 (by rfl) ⟨779874, by rfl⟩ : syracuseStep 2079665 = 1559749) B1559749
theorem B1227713 : Blo 818347 1227713 := bstep (se 2 (by rfl) ⟨460392, by rfl⟩ : syracuseStep 1227713 = 920785) B920785
theorem B1227731 : Blo 818347 1227731 := bstep (se 1 (by rfl) ⟨920798, by rfl⟩ : syracuseStep 1227731 = 1841597) B1841597
theorem B2079715 : Blo 818347 2079715 := bstep (se 1 (by rfl) ⟨1559786, by rfl⟩ : syracuseStep 2079715 = 3119573) B3119573
theorem B1227761 : Blo 818347 1227761 := bstep (se 2 (by rfl) ⟨460410, by rfl⟩ : syracuseStep 1227761 = 920821) B920821
theorem B1227779 : Blo 818347 1227779 := bstep (se 1 (by rfl) ⟨920834, by rfl⟩ : syracuseStep 1227779 = 1841669) B1841669
theorem B1227809 : Blo 818347 1227809 := bstep (se 2 (by rfl) ⟨460428, by rfl⟩ : syracuseStep 1227809 = 920857) B920857
theorem B1227827 : Blo 818347 1227827 := bstep (se 1 (by rfl) ⟨920870, by rfl⟩ : syracuseStep 1227827 = 1841741) B1841741
theorem B1227857 : Blo 818347 1227857 := bstep (se 2 (by rfl) ⟨460446, by rfl⟩ : syracuseStep 1227857 = 920893) B920893
theorem B1227875 : Blo 818347 1227875 := bstep (se 1 (by rfl) ⟨920906, by rfl⟩ : syracuseStep 1227875 = 1841813) B1841813
theorem B2767985 : Blo 818347 2767985 := bstep (se 2 (by rfl) ⟨1037994, by rfl⟩ : syracuseStep 2767985 = 2075989) B2075989
theorem B2079857 : Blo 818347 2079857 := bstep (se 2 (by rfl) ⟨779946, by rfl⟩ : syracuseStep 2079857 = 1559893) B1559893
theorem B1227905 : Blo 818347 1227905 := bstep (se 2 (by rfl) ⟨460464, by rfl⟩ : syracuseStep 1227905 = 920929) B920929
theorem B1227923 : Blo 818347 1227923 := bstep (se 1 (by rfl) ⟨920942, by rfl⟩ : syracuseStep 1227923 = 1841885) B1841885
theorem B1227953 : Blo 818347 1227953 := bstep (se 2 (by rfl) ⟨460482, by rfl⟩ : syracuseStep 1227953 = 920965) B920965
theorem B1227971 : Blo 818347 1227971 := bstep (se 1 (by rfl) ⟨920978, by rfl⟩ : syracuseStep 1227971 = 1841957) B1841957
theorem B1228001 : Blo 818347 1228001 := bstep (se 2 (by rfl) ⟨460500, by rfl⟩ : syracuseStep 1228001 = 921001) B921001
theorem B1228019 : Blo 818347 1228019 := bstep (se 1 (by rfl) ⟨921014, by rfl⟩ : syracuseStep 1228019 = 1842029) B1842029
theorem B4668677 : Blo 818347 4668677 := bstep (se 4 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 4668677 = 875377) B875377
theorem B1228049 : Blo 818347 1228049 := bstep (se 2 (by rfl) ⟨460518, by rfl⟩ : syracuseStep 1228049 = 921037) B921037
theorem B1228067 : Blo 818347 1228067 := bstep (se 1 (by rfl) ⟨921050, by rfl⟩ : syracuseStep 1228067 = 1842101) B1842101
theorem B1228097 : Blo 818347 1228097 := bstep (se 2 (by rfl) ⟨460536, by rfl⟩ : syracuseStep 1228097 = 921073) B921073
theorem B1228115 : Blo 818347 1228115 := bstep (se 1 (by rfl) ⟨921086, by rfl⟩ : syracuseStep 1228115 = 1842173) B1842173
theorem B1228145 : Blo 818347 1228145 := bstep (se 2 (by rfl) ⟨460554, by rfl⟩ : syracuseStep 1228145 = 921109) B921109
theorem B1228163 : Blo 818347 1228163 := bstep (se 1 (by rfl) ⟨921122, by rfl⟩ : syracuseStep 1228163 = 1842245) B1842245
theorem B1228193 : Blo 818347 1228193 := bstep (se 2 (by rfl) ⟨460572, by rfl⟩ : syracuseStep 1228193 = 921145) B921145
theorem B1228211 : Blo 818347 1228211 := bstep (se 1 (by rfl) ⟨921158, by rfl⟩ : syracuseStep 1228211 = 1842317) B1842317
theorem B1228241 : Blo 818347 1228241 := bstep (se 2 (by rfl) ⟨460590, by rfl⟩ : syracuseStep 1228241 = 921181) B921181
theorem B933331 : Blo 818347 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1228259 : Blo 818347 1228259 := bstep (se 1 (by rfl) ⟨921194, by rfl⟩ : syracuseStep 1228259 = 1842389) B1842389
theorem B1228289 : Blo 818347 1228289 := bstep (se 2 (by rfl) ⟨460608, by rfl⟩ : syracuseStep 1228289 = 921217) B921217
theorem B1228307 : Blo 818347 1228307 := bstep (se 1 (by rfl) ⟨921230, by rfl⟩ : syracuseStep 1228307 = 1842461) B1842461
theorem B1228337 : Blo 818347 1228337 := bstep (se 2 (by rfl) ⟨460626, by rfl⟩ : syracuseStep 1228337 = 921253) B921253
theorem B1228355 : Blo 818347 1228355 := bstep (se 1 (by rfl) ⟨921266, by rfl⟩ : syracuseStep 1228355 = 1842533) B1842533
theorem B1228385 : Blo 818347 1228385 := bstep (se 2 (by rfl) ⟨460644, by rfl⟩ : syracuseStep 1228385 = 921289) B921289
theorem B1556081 : Blo 818347 1556081 := bstep (se 2 (by rfl) ⟨583530, by rfl⟩ : syracuseStep 1556081 = 1167061) B1167061
theorem B1228403 : Blo 818347 1228403 := bstep (se 1 (by rfl) ⟨921302, by rfl⟩ : syracuseStep 1228403 = 1842605) B1842605
theorem B2768525 : Blo 818347 2768525 := bstep (se 3 (by rfl) ⟨519098, by rfl⟩ : syracuseStep 2768525 = 1038197) B1038197
theorem B3948173 : Blo 818347 3948173 := bstep (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) B1480565
theorem B1228433 : Blo 818347 1228433 := bstep (se 2 (by rfl) ⟨460662, by rfl⟩ : syracuseStep 1228433 = 921325) B921325
theorem B1228451 : Blo 818347 1228451 := bstep (se 1 (by rfl) ⟨921338, by rfl⟩ : syracuseStep 1228451 = 1842677) B1842677
theorem B1228481 : Blo 818347 1228481 := bstep (se 2 (by rfl) ⟨460680, by rfl⟩ : syracuseStep 1228481 = 921361) B921361
theorem B2768579 : Blo 818347 2768579 := bstep (se 1 (by rfl) ⟨2076434, by rfl⟩ : syracuseStep 2768579 = 4152869) B4152869
theorem B1228499 : Blo 818347 1228499 := bstep (se 1 (by rfl) ⟨921374, by rfl⟩ : syracuseStep 1228499 = 1842749) B1842749
theorem B1228529 : Blo 818347 1228529 := bstep (se 2 (by rfl) ⟨460698, by rfl⟩ : syracuseStep 1228529 = 921397) B921397
theorem B1228547 : Blo 818347 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B1228577 : Blo 818347 1228577 := bstep (se 2 (by rfl) ⟨460716, by rfl⟩ : syracuseStep 1228577 = 921433) B921433
theorem B4144931 : Blo 818347 4144931 := bstep (se 1 (by rfl) ⟨3108698, by rfl⟩ : syracuseStep 4144931 = 6217397) B6217397
theorem B1228595 : Blo 818347 1228595 := bstep (se 1 (by rfl) ⟨921446, by rfl⟩ : syracuseStep 1228595 = 1842893) B1842893
theorem B1228625 : Blo 818347 1228625 := bstep (se 2 (by rfl) ⟨460734, by rfl⟩ : syracuseStep 1228625 = 921469) B921469
theorem B1228643 : Blo 818347 1228643 := bstep (se 1 (by rfl) ⟨921482, by rfl⟩ : syracuseStep 1228643 = 1842965) B1842965
theorem B1228673 : Blo 818347 1228673 := bstep (se 2 (by rfl) ⟨460752, by rfl⟩ : syracuseStep 1228673 = 921505) B921505
theorem B1228691 : Blo 818347 1228691 := bstep (se 1 (by rfl) ⟨921518, by rfl⟩ : syracuseStep 1228691 = 1843037) B1843037
theorem B1228721 : Blo 818347 1228721 := bstep (se 2 (by rfl) ⟨460770, by rfl⟩ : syracuseStep 1228721 = 921541) B921541
theorem B1228739 : Blo 818347 1228739 := bstep (se 1 (by rfl) ⟨921554, by rfl⟩ : syracuseStep 1228739 = 1843109) B1843109
theorem B2768849 : Blo 818347 2768849 := bstep (se 2 (by rfl) ⟨1038318, by rfl⟩ : syracuseStep 2768849 = 2076637) B2076637
theorem B1228769 : Blo 818347 1228769 := bstep (se 2 (by rfl) ⟨460788, by rfl⟩ : syracuseStep 1228769 = 921577) B921577
theorem B1228787 : Blo 818347 1228787 := bstep (se 1 (by rfl) ⟨921590, by rfl⟩ : syracuseStep 1228787 = 1843181) B1843181
theorem B1228817 : Blo 818347 1228817 := bstep (se 2 (by rfl) ⟨460806, by rfl⟩ : syracuseStep 1228817 = 921613) B921613
theorem B1228835 : Blo 818347 1228835 := bstep (se 1 (by rfl) ⟨921626, by rfl⟩ : syracuseStep 1228835 = 1843253) B1843253
theorem B1228865 : Blo 818347 1228865 := bstep (se 2 (by rfl) ⟨460824, by rfl⟩ : syracuseStep 1228865 = 921649) B921649
theorem B2080849 : Blo 818347 2080849 := bstep (se 2 (by rfl) ⟨780318, by rfl⟩ : syracuseStep 2080849 = 1560637) B1560637
theorem B1228883 : Blo 818347 1228883 := bstep (se 1 (by rfl) ⟨921662, by rfl⟩ : syracuseStep 1228883 = 1843325) B1843325
theorem B1228913 : Blo 818347 1228913 := bstep (se 2 (by rfl) ⟨460842, by rfl⟩ : syracuseStep 1228913 = 921685) B921685
theorem B1228931 : Blo 818347 1228931 := bstep (se 1 (by rfl) ⟨921698, by rfl⟩ : syracuseStep 1228931 = 1843397) B1843397
theorem B1228961 : Blo 818347 1228961 := bstep (se 2 (by rfl) ⟨460860, by rfl⟩ : syracuseStep 1228961 = 921721) B921721
theorem B1228979 : Blo 818347 1228979 := bstep (se 1 (by rfl) ⟨921734, by rfl⟩ : syracuseStep 1228979 = 1843469) B1843469
theorem B1229009 : Blo 818347 1229009 := bstep (se 2 (by rfl) ⟨460878, by rfl⟩ : syracuseStep 1229009 = 921757) B921757
theorem B1229027 : Blo 818347 1229027 := bstep (se 1 (by rfl) ⟨921770, by rfl⟩ : syracuseStep 1229027 = 1843541) B1843541
theorem B1229057 : Blo 818347 1229057 := bstep (se 2 (by rfl) ⟨460896, by rfl⟩ : syracuseStep 1229057 = 921793) B921793
theorem B1229075 : Blo 818347 1229075 := bstep (se 1 (by rfl) ⟨921806, by rfl⟩ : syracuseStep 1229075 = 1843613) B1843613
theorem B1229105 : Blo 818347 1229105 := bstep (se 2 (by rfl) ⟨460914, by rfl⟩ : syracuseStep 1229105 = 921829) B921829
theorem B934211 : Blo 818347 934211 := bstep (se 1 (by rfl) ⟨700658, by rfl⟩ : syracuseStep 934211 = 1401317) B1401317
theorem B1229123 : Blo 818347 1229123 := bstep (se 1 (by rfl) ⟨921842, by rfl⟩ : syracuseStep 1229123 = 1843685) B1843685
theorem B1229153 : Blo 818347 1229153 := bstep (se 2 (by rfl) ⟨460932, by rfl⟩ : syracuseStep 1229153 = 921865) B921865
theorem B2081123 : Blo 818347 2081123 := bstep (se 1 (by rfl) ⟨1560842, by rfl⟩ : syracuseStep 2081123 = 3121685) B3121685
theorem B1229171 : Blo 818347 1229171 := bstep (se 1 (by rfl) ⟨921878, by rfl⟩ : syracuseStep 1229171 = 1843757) B1843757
theorem B1229201 : Blo 818347 1229201 := bstep (se 2 (by rfl) ⟨460950, by rfl⟩ : syracuseStep 1229201 = 921901) B921901
theorem B1229219 : Blo 818347 1229219 := bstep (se 1 (by rfl) ⟨921914, by rfl⟩ : syracuseStep 1229219 = 1843829) B1843829
theorem B1229249 : Blo 818347 1229249 := bstep (se 2 (by rfl) ⟨460968, by rfl⟩ : syracuseStep 1229249 = 921937) B921937
theorem B1229267 : Blo 818347 1229267 := bstep (se 1 (by rfl) ⟨921950, by rfl⟩ : syracuseStep 1229267 = 1843901) B1843901
theorem B2769389 : Blo 818347 2769389 := bstep (se 3 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 2769389 = 1038521) B1038521
theorem B1229297 : Blo 818347 1229297 := bstep (se 2 (by rfl) ⟨460986, by rfl⟩ : syracuseStep 1229297 = 921973) B921973
theorem B1556977 : Blo 818347 1556977 := bstep (se 2 (by rfl) ⟨583866, by rfl⟩ : syracuseStep 1556977 = 1167733) B1167733
theorem B1229315 : Blo 818347 1229315 := bstep (se 1 (by rfl) ⟨921986, by rfl⟩ : syracuseStep 1229315 = 1843973) B1843973
theorem B1229345 : Blo 818347 1229345 := bstep (se 2 (by rfl) ⟨461004, by rfl⟩ : syracuseStep 1229345 = 922009) B922009
theorem B2769443 : Blo 818347 2769443 := bstep (se 1 (by rfl) ⟨2077082, by rfl⟩ : syracuseStep 2769443 = 4154165) B4154165
theorem B2081315 : Blo 818347 2081315 := bstep (se 1 (by rfl) ⟨1560986, by rfl⟩ : syracuseStep 2081315 = 3121973) B3121973
theorem B1229363 : Blo 818347 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B1753667 : Blo 818347 1753667 := bstep (se 1 (by rfl) ⟨1315250, by rfl⟩ : syracuseStep 1753667 = 2630501) B2630501
theorem B4145741 : Blo 818347 4145741 := bstep (se 3 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 4145741 = 1554653) B1554653
theorem B1229393 : Blo 818347 1229393 := bstep (se 2 (by rfl) ⟨461022, by rfl⟩ : syracuseStep 1229393 = 922045) B922045
theorem B1229411 : Blo 818347 1229411 := bstep (se 1 (by rfl) ⟨922058, by rfl⟩ : syracuseStep 1229411 = 1844117) B1844117
theorem B1229441 : Blo 818347 1229441 := bstep (se 2 (by rfl) ⟨461040, by rfl⟩ : syracuseStep 1229441 = 922081) B922081
theorem B1557137 : Blo 818347 1557137 := bstep (se 2 (by rfl) ⟨583926, by rfl⟩ : syracuseStep 1557137 = 1167853) B1167853
theorem B1229459 : Blo 818347 1229459 := bstep (se 1 (by rfl) ⟨922094, by rfl⟩ : syracuseStep 1229459 = 1844189) B1844189
theorem B1229489 : Blo 818347 1229489 := bstep (se 2 (by rfl) ⟨461058, by rfl⟩ : syracuseStep 1229489 = 922117) B922117
theorem B1229507 : Blo 818347 1229507 := bstep (se 1 (by rfl) ⟨922130, by rfl⟩ : syracuseStep 1229507 = 1844261) B1844261
theorem B1229537 : Blo 818347 1229537 := bstep (se 2 (by rfl) ⟨461076, by rfl⟩ : syracuseStep 1229537 = 922153) B922153
theorem B1229555 : Blo 818347 1229555 := bstep (se 1 (by rfl) ⟨922166, by rfl⟩ : syracuseStep 1229555 = 1844333) B1844333
theorem B1229585 : Blo 818347 1229585 := bstep (se 2 (by rfl) ⟨461094, by rfl⟩ : syracuseStep 1229585 = 922189) B922189
theorem B1229603 : Blo 818347 1229603 := bstep (se 1 (by rfl) ⟨922202, by rfl⟩ : syracuseStep 1229603 = 1844405) B1844405
theorem B2769713 : Blo 818347 2769713 := bstep (se 2 (by rfl) ⟨1038642, by rfl⟩ : syracuseStep 2769713 = 2077285) B2077285
theorem B1229633 : Blo 818347 1229633 := bstep (se 2 (by rfl) ⟨461112, by rfl⟩ : syracuseStep 1229633 = 922225) B922225
theorem B1229651 : Blo 818347 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B1229681 : Blo 818347 1229681 := bstep (se 2 (by rfl) ⟨461130, by rfl⟩ : syracuseStep 1229681 = 922261) B922261
theorem B1229699 : Blo 818347 1229699 := bstep (se 1 (by rfl) ⟨922274, by rfl⟩ : syracuseStep 1229699 = 1844549) B1844549
theorem B1229729 : Blo 818347 1229729 := bstep (se 2 (by rfl) ⟨461148, by rfl⟩ : syracuseStep 1229729 = 922297) B922297
theorem B1229747 : Blo 818347 1229747 := bstep (se 1 (by rfl) ⟨922310, by rfl⟩ : syracuseStep 1229747 = 1844621) B1844621
theorem B12633029 : Blo 818347 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B3949517 : Blo 818347 3949517 := bstep (se 3 (by rfl) ⟨740534, by rfl⟩ : syracuseStep 3949517 = 1481069) B1481069
theorem B1229777 : Blo 818347 1229777 := bstep (se 2 (by rfl) ⟨461166, by rfl⟩ : syracuseStep 1229777 = 922333) B922333
theorem B1229795 : Blo 818347 1229795 := bstep (se 1 (by rfl) ⟨922346, by rfl⟩ : syracuseStep 1229795 = 1844693) B1844693
theorem B2999281 : Blo 818347 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B1229825 : Blo 818347 1229825 := bstep (se 2 (by rfl) ⟨461184, by rfl⟩ : syracuseStep 1229825 = 922369) B922369
theorem B1754129 : Blo 818347 1754129 := bstep (se 2 (by rfl) ⟨657798, by rfl⟩ : syracuseStep 1754129 = 1315597) B1315597
theorem B1229843 : Blo 818347 1229843 := bstep (se 1 (by rfl) ⟨922382, by rfl⟩ : syracuseStep 1229843 = 1844765) B1844765
theorem B1557539 : Blo 818347 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1229873 : Blo 818347 1229873 := bstep (se 2 (by rfl) ⟨461202, by rfl⟩ : syracuseStep 1229873 = 922405) B922405
theorem B1262659 : Blo 818347 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B1229891 : Blo 818347 1229891 := bstep (se 1 (by rfl) ⟨922418, by rfl⟩ : syracuseStep 1229891 = 1844837) B1844837
theorem B1229921 : Blo 818347 1229921 := bstep (se 2 (by rfl) ⟨461220, by rfl⟩ : syracuseStep 1229921 = 922441) B922441
theorem B1229939 : Blo 818347 1229939 := bstep (se 1 (by rfl) ⟨922454, by rfl⟩ : syracuseStep 1229939 = 1844909) B1844909
theorem B1229969 : Blo 818347 1229969 := bstep (se 2 (by rfl) ⟨461238, by rfl⟩ : syracuseStep 1229969 = 922477) B922477
theorem B1229987 : Blo 818347 1229987 := bstep (se 1 (by rfl) ⟨922490, by rfl⟩ : syracuseStep 1229987 = 1844981) B1844981
theorem B1230017 : Blo 818347 1230017 := bstep (se 2 (by rfl) ⟨461256, by rfl⟩ : syracuseStep 1230017 = 922513) B922513
theorem B1230035 : Blo 818347 1230035 := bstep (se 1 (by rfl) ⟨922526, by rfl⟩ : syracuseStep 1230035 = 1845053) B1845053
theorem B1230065 : Blo 818347 1230065 := bstep (se 2 (by rfl) ⟨461274, by rfl⟩ : syracuseStep 1230065 = 922549) B922549
theorem B1230083 : Blo 818347 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B1230113 : Blo 818347 1230113 := bstep (se 2 (by rfl) ⟨461292, by rfl⟩ : syracuseStep 1230113 = 922585) B922585
theorem B1230131 : Blo 818347 1230131 := bstep (se 1 (by rfl) ⟨922598, by rfl⟩ : syracuseStep 1230131 = 1845197) B1845197
theorem B2770253 : Blo 818347 2770253 := bstep (se 3 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 2770253 = 1038845) B1038845
theorem B1230161 : Blo 818347 1230161 := bstep (se 2 (by rfl) ⟨461310, by rfl⟩ : syracuseStep 1230161 = 922621) B922621
theorem B1230179 : Blo 818347 1230179 := bstep (se 1 (by rfl) ⟨922634, by rfl⟩ : syracuseStep 1230179 = 1845269) B1845269
theorem B1230209 : Blo 818347 1230209 := bstep (se 2 (by rfl) ⟨461328, by rfl⟩ : syracuseStep 1230209 = 922657) B922657
theorem B2770307 : Blo 818347 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B1230227 : Blo 818347 1230227 := bstep (se 1 (by rfl) ⟨922670, by rfl⟩ : syracuseStep 1230227 = 1845341) B1845341
theorem B1230257 : Blo 818347 1230257 := bstep (se 2 (by rfl) ⟨461346, by rfl⟩ : syracuseStep 1230257 = 922693) B922693
theorem B1230275 : Blo 818347 1230275 := bstep (se 1 (by rfl) ⟨922706, by rfl⟩ : syracuseStep 1230275 = 1845413) B1845413
theorem B1230305 : Blo 818347 1230305 := bstep (se 2 (by rfl) ⟨461364, by rfl⟩ : syracuseStep 1230305 = 922729) B922729
theorem B1230323 : Blo 818347 1230323 := bstep (se 1 (by rfl) ⟨922742, by rfl⟩ : syracuseStep 1230323 = 1845485) B1845485
theorem B7489037 : Blo 818347 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B1230353 : Blo 818347 1230353 := bstep (se 2 (by rfl) ⟨461382, by rfl⟩ : syracuseStep 1230353 = 922765) B922765
theorem B1230371 : Blo 818347 1230371 := bstep (se 1 (by rfl) ⟨922778, by rfl⟩ : syracuseStep 1230371 = 1845557) B1845557
theorem B1230401 : Blo 818347 1230401 := bstep (se 2 (by rfl) ⟨461400, by rfl⟩ : syracuseStep 1230401 = 922801) B922801
theorem B1230419 : Blo 818347 1230419 := bstep (se 1 (by rfl) ⟨922814, by rfl⟩ : syracuseStep 1230419 = 1845629) B1845629
theorem B1230449 : Blo 818347 1230449 := bstep (se 2 (by rfl) ⟨461418, by rfl⟩ : syracuseStep 1230449 = 922837) B922837
theorem B1230467 : Blo 818347 1230467 := bstep (se 1 (by rfl) ⟨922850, by rfl⟩ : syracuseStep 1230467 = 1845701) B1845701
theorem B2770577 : Blo 818347 2770577 := bstep (se 2 (by rfl) ⟨1038966, by rfl⟩ : syracuseStep 2770577 = 2077933) B2077933
theorem B1230497 : Blo 818347 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B1230515 : Blo 818347 1230515 := bstep (se 1 (by rfl) ⟨922886, by rfl⟩ : syracuseStep 1230515 = 1845773) B1845773
theorem B1230545 : Blo 818347 1230545 := bstep (se 2 (by rfl) ⟨461454, by rfl⟩ : syracuseStep 1230545 = 922909) B922909
theorem B1230563 : Blo 818347 1230563 := bstep (se 1 (by rfl) ⟨922922, by rfl⟩ : syracuseStep 1230563 = 1845845) B1845845
theorem B1230593 : Blo 818347 1230593 := bstep (se 2 (by rfl) ⟨461472, by rfl⟩ : syracuseStep 1230593 = 922945) B922945
theorem B1230611 : Blo 818347 1230611 := bstep (se 1 (by rfl) ⟨922958, by rfl⟩ : syracuseStep 1230611 = 1845917) B1845917
theorem B1230641 : Blo 818347 1230641 := bstep (se 2 (by rfl) ⟨461490, by rfl⟩ : syracuseStep 1230641 = 922981) B922981
theorem B22791989 : Blo 818347 22791989 := bstep (se 5 (by rfl) ⟨1068374, by rfl⟩ : syracuseStep 22791989 = 2136749) B2136749
theorem B1230659 : Blo 818347 1230659 := bstep (se 1 (by rfl) ⟨922994, by rfl⟩ : syracuseStep 1230659 = 1845989) B1845989
theorem B1230689 : Blo 818347 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B1230707 : Blo 818347 1230707 := bstep (se 1 (by rfl) ⟨923030, by rfl⟩ : syracuseStep 1230707 = 1846061) B1846061
theorem B1230737 : Blo 818347 1230737 := bstep (se 2 (by rfl) ⟨461526, by rfl⟩ : syracuseStep 1230737 = 923053) B923053
theorem B1230755 : Blo 818347 1230755 := bstep (se 1 (by rfl) ⟨923066, by rfl⟩ : syracuseStep 1230755 = 1846133) B1846133
theorem B1558435 : Blo 818347 1558435 := bstep (se 1 (by rfl) ⟨1168826, by rfl⟩ : syracuseStep 1558435 = 2337653) B2337653
theorem B1230785 : Blo 818347 1230785 := bstep (se 2 (by rfl) ⟨461544, by rfl⟩ : syracuseStep 1230785 = 923089) B923089
theorem B1230803 : Blo 818347 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B1230833 : Blo 818347 1230833 := bstep (se 2 (by rfl) ⟨461562, by rfl⟩ : syracuseStep 1230833 = 923125) B923125
theorem B1230851 : Blo 818347 1230851 := bstep (se 1 (by rfl) ⟨923138, by rfl⟩ : syracuseStep 1230851 = 1846277) B1846277
theorem B1230881 : Blo 818347 1230881 := bstep (se 2 (by rfl) ⟨461580, by rfl⟩ : syracuseStep 1230881 = 923161) B923161
theorem B1230899 : Blo 818347 1230899 := bstep (se 1 (by rfl) ⟨923174, by rfl⟩ : syracuseStep 1230899 = 1846349) B1846349
theorem B1558595 : Blo 818347 1558595 := bstep (se 1 (by rfl) ⟨1168946, by rfl⟩ : syracuseStep 1558595 = 2337893) B2337893
theorem B1230929 : Blo 818347 1230929 := bstep (se 2 (by rfl) ⟨461598, by rfl⟩ : syracuseStep 1230929 = 923197) B923197
theorem B1230947 : Blo 818347 1230947 := bstep (se 1 (by rfl) ⟨923210, by rfl⟩ : syracuseStep 1230947 = 1846421) B1846421
theorem B1230977 : Blo 818347 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B1230995 : Blo 818347 1230995 := bstep (se 1 (by rfl) ⟨923246, by rfl⟩ : syracuseStep 1230995 = 1846493) B1846493
theorem B2771117 : Blo 818347 2771117 := bstep (se 3 (by rfl) ⟨519584, by rfl⟩ : syracuseStep 2771117 = 1039169) B1039169
theorem B1231025 : Blo 818347 1231025 := bstep (se 2 (by rfl) ⟨461634, by rfl⟩ : syracuseStep 1231025 = 923269) B923269
theorem B1231043 : Blo 818347 1231043 := bstep (se 1 (by rfl) ⟨923282, by rfl⟩ : syracuseStep 1231043 = 1846565) B1846565
theorem B13289669 : Blo 818347 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B1231073 : Blo 818347 1231073 := bstep (se 2 (by rfl) ⟨461652, by rfl⟩ : syracuseStep 1231073 = 923305) B923305
theorem B3786979 : Blo 818347 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B2771171 : Blo 818347 2771171 := bstep (se 1 (by rfl) ⟨2078378, by rfl⟩ : syracuseStep 2771171 = 4156757) B4156757
theorem B1231091 : Blo 818347 1231091 := bstep (se 1 (by rfl) ⟨923318, by rfl⟩ : syracuseStep 1231091 = 1846637) B1846637
theorem B1231121 : Blo 818347 1231121 := bstep (se 2 (by rfl) ⟨461670, by rfl⟩ : syracuseStep 1231121 = 923341) B923341
theorem B1165603 : Blo 818347 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B1231139 : Blo 818347 1231139 := bstep (se 1 (by rfl) ⟨923354, by rfl⟩ : syracuseStep 1231139 = 1846709) B1846709
theorem B1755427 : Blo 818347 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B1231169 : Blo 818347 1231169 := bstep (se 2 (by rfl) ⟨461688, by rfl⟩ : syracuseStep 1231169 = 923377) B923377
theorem B1231187 : Blo 818347 1231187 := bstep (se 1 (by rfl) ⟨923390, by rfl⟩ : syracuseStep 1231187 = 1846781) B1846781
theorem B1231217 : Blo 818347 1231217 := bstep (se 2 (by rfl) ⟨461706, by rfl⟩ : syracuseStep 1231217 = 923413) B923413
theorem B1231235 : Blo 818347 1231235 := bstep (se 1 (by rfl) ⟨923426, by rfl⟩ : syracuseStep 1231235 = 1846853) B1846853
theorem B1231265 : Blo 818347 1231265 := bstep (se 2 (by rfl) ⟨461724, by rfl⟩ : syracuseStep 1231265 = 923449) B923449
theorem B1231283 : Blo 818347 1231283 := bstep (se 1 (by rfl) ⟨923462, by rfl⟩ : syracuseStep 1231283 = 1846925) B1846925
theorem B1231313 : Blo 818347 1231313 := bstep (se 2 (by rfl) ⟨461742, by rfl⟩ : syracuseStep 1231313 = 923485) B923485
theorem B1231331 : Blo 818347 1231331 := bstep (se 1 (by rfl) ⟨923498, by rfl⟩ : syracuseStep 1231331 = 1846997) B1846997
theorem B2771441 : Blo 818347 2771441 := bstep (se 2 (by rfl) ⟨1039290, by rfl⟩ : syracuseStep 2771441 = 2078581) B2078581
theorem B1231361 : Blo 818347 1231361 := bstep (se 2 (by rfl) ⟨461760, by rfl⟩ : syracuseStep 1231361 = 923521) B923521
theorem B1231379 : Blo 818347 1231379 := bstep (se 1 (by rfl) ⟨923534, by rfl⟩ : syracuseStep 1231379 = 1847069) B1847069
theorem B1755683 : Blo 818347 1755683 := bstep (se 1 (by rfl) ⟨1316762, by rfl⟩ : syracuseStep 1755683 = 2633525) B2633525
theorem B1231409 : Blo 818347 1231409 := bstep (se 2 (by rfl) ⟨461778, by rfl⟩ : syracuseStep 1231409 = 923557) B923557
theorem B1231427 : Blo 818347 1231427 := bstep (se 1 (by rfl) ⟨923570, by rfl⟩ : syracuseStep 1231427 = 1847141) B1847141
theorem B1231457 : Blo 818347 1231457 := bstep (se 2 (by rfl) ⟨461796, by rfl⟩ : syracuseStep 1231457 = 923593) B923593
theorem B3164771 : Blo 818347 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B1231475 : Blo 818347 1231475 := bstep (se 1 (by rfl) ⟨923606, by rfl⟩ : syracuseStep 1231475 = 1847213) B1847213
theorem B1231505 : Blo 818347 1231505 := bstep (se 2 (by rfl) ⟨461814, by rfl⟩ : syracuseStep 1231505 = 923629) B923629
theorem B1231523 : Blo 818347 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B1231553 : Blo 818347 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B1231571 : Blo 818347 1231571 := bstep (se 1 (by rfl) ⟨923678, by rfl⟩ : syracuseStep 1231571 = 1847357) B1847357
theorem B22498019 : Blo 818347 22498019 := bstep (se 1 (by rfl) ⟨16873514, by rfl⟩ : syracuseStep 22498019 = 33747029) B33747029
theorem B1231601 : Blo 818347 1231601 := bstep (se 2 (by rfl) ⟨461850, by rfl⟩ : syracuseStep 1231601 = 923701) B923701
theorem B1166081 : Blo 818347 1166081 := bstep (se 2 (by rfl) ⟨437280, by rfl⟩ : syracuseStep 1166081 = 874561) B874561
theorem B1231619 : Blo 818347 1231619 := bstep (se 1 (by rfl) ⟨923714, by rfl⟩ : syracuseStep 1231619 = 1847429) B1847429
theorem B1231649 : Blo 818347 1231649 := bstep (se 2 (by rfl) ⟨461868, by rfl⟩ : syracuseStep 1231649 = 923737) B923737
theorem B1231667 : Blo 818347 1231667 := bstep (se 1 (by rfl) ⟨923750, by rfl⟩ : syracuseStep 1231667 = 1847501) B1847501
theorem B1231697 : Blo 818347 1231697 := bstep (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) B923773
theorem B1231715 : Blo 818347 1231715 := bstep (se 1 (by rfl) ⟨923786, by rfl⟩ : syracuseStep 1231715 = 1847573) B1847573
theorem B1166195 : Blo 818347 1166195 := bstep (se 1 (by rfl) ⟨874646, by rfl⟩ : syracuseStep 1166195 = 1749293) B1749293
theorem B1231745 : Blo 818347 1231745 := bstep (se 2 (by rfl) ⟨461904, by rfl⟩ : syracuseStep 1231745 = 923809) B923809
theorem B1231763 : Blo 818347 1231763 := bstep (se 1 (by rfl) ⟨923822, by rfl⟩ : syracuseStep 1231763 = 1847645) B1847645
theorem B1231793 : Blo 818347 1231793 := bstep (se 2 (by rfl) ⟨461922, by rfl⟩ : syracuseStep 1231793 = 923845) B923845
theorem B1166275 : Blo 818347 1166275 := bstep (se 1 (by rfl) ⟨874706, by rfl⟩ : syracuseStep 1166275 = 1749413) B1749413
theorem B1231811 : Blo 818347 1231811 := bstep (se 1 (by rfl) ⟨923858, by rfl⟩ : syracuseStep 1231811 = 1847717) B1847717
theorem B1231841 : Blo 818347 1231841 := bstep (se 2 (by rfl) ⟨461940, by rfl⟩ : syracuseStep 1231841 = 923881) B923881
theorem B1231859 : Blo 818347 1231859 := bstep (se 1 (by rfl) ⟨923894, by rfl⟩ : syracuseStep 1231859 = 1847789) B1847789
theorem B4672525 : Blo 818347 4672525 := bstep (se 3 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 4672525 = 1752197) B1752197
theorem B2771981 : Blo 818347 2771981 := bstep (se 3 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 2771981 = 1039493) B1039493
theorem B1231889 : Blo 818347 1231889 := bstep (se 2 (by rfl) ⟨461958, by rfl⟩ : syracuseStep 1231889 = 923917) B923917
theorem B1231907 : Blo 818347 1231907 := bstep (se 1 (by rfl) ⟨923930, by rfl⟩ : syracuseStep 1231907 = 1847861) B1847861
theorem B1231937 : Blo 818347 1231937 := bstep (se 2 (by rfl) ⟨461976, by rfl⟩ : syracuseStep 1231937 = 923953) B923953
theorem B2772035 : Blo 818347 2772035 := bstep (se 1 (by rfl) ⟨2079026, by rfl⟩ : syracuseStep 2772035 = 4158053) B4158053
theorem B1231955 : Blo 818347 1231955 := bstep (se 1 (by rfl) ⟨923966, by rfl⟩ : syracuseStep 1231955 = 1847933) B1847933
theorem B2215021 : Blo 818347 2215021 := bstep (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) B830633
theorem B1231985 : Blo 818347 1231985 := bstep (se 2 (by rfl) ⟨461994, by rfl⟩ : syracuseStep 1231985 = 923989) B923989
theorem B1559665 : Blo 818347 1559665 := bstep (se 2 (by rfl) ⟨584874, by rfl⟩ : syracuseStep 1559665 = 1169749) B1169749
theorem B1232003 : Blo 818347 1232003 := bstep (se 1 (by rfl) ⟨924002, by rfl⟩ : syracuseStep 1232003 = 1848005) B1848005
theorem B1232033 : Blo 818347 1232033 := bstep (se 2 (by rfl) ⟨462012, by rfl⟩ : syracuseStep 1232033 = 924025) B924025
theorem B1232051 : Blo 818347 1232051 := bstep (se 1 (by rfl) ⟨924038, by rfl⟩ : syracuseStep 1232051 = 1848077) B1848077
theorem B1232081 : Blo 818347 1232081 := bstep (se 2 (by rfl) ⟨462030, by rfl⟩ : syracuseStep 1232081 = 924061) B924061
theorem B1232099 : Blo 818347 1232099 := bstep (se 1 (by rfl) ⟨924074, by rfl⟩ : syracuseStep 1232099 = 1848149) B1848149
theorem B1232129 : Blo 818347 1232129 := bstep (se 2 (by rfl) ⟨462048, by rfl⟩ : syracuseStep 1232129 = 924097) B924097
theorem B6638861 : Blo 818347 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B1232147 : Blo 818347 1232147 := bstep (se 1 (by rfl) ⟨924110, by rfl⟩ : syracuseStep 1232147 = 1848221) B1848221
theorem B5262641 : Blo 818347 5262641 := bstep (se 2 (by rfl) ⟨1973490, by rfl⟩ : syracuseStep 5262641 = 3946981) B3946981
theorem B1232177 : Blo 818347 1232177 := bstep (se 2 (by rfl) ⟨462066, by rfl⟩ : syracuseStep 1232177 = 924133) B924133
theorem B1232195 : Blo 818347 1232195 := bstep (se 1 (by rfl) ⟨924146, by rfl⟩ : syracuseStep 1232195 = 1848293) B1848293
theorem B2772305 : Blo 818347 2772305 := bstep (se 2 (by rfl) ⟨1039614, by rfl⟩ : syracuseStep 2772305 = 2079229) B2079229
theorem B1232225 : Blo 818347 1232225 := bstep (se 2 (by rfl) ⟨462084, by rfl⟩ : syracuseStep 1232225 = 924169) B924169
theorem B1232243 : Blo 818347 1232243 := bstep (se 1 (by rfl) ⟨924182, by rfl⟩ : syracuseStep 1232243 = 1848365) B1848365
theorem B2215313 : Blo 818347 2215313 := bstep (se 2 (by rfl) ⟨830742, by rfl⟩ : syracuseStep 2215313 = 1661485) B1661485
theorem B1232273 : Blo 818347 1232273 := bstep (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) B924205
theorem B1232291 : Blo 818347 1232291 := bstep (se 1 (by rfl) ⟨924218, by rfl⟩ : syracuseStep 1232291 = 1848437) B1848437
theorem B4148657 : Blo 818347 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B1232321 : Blo 818347 1232321 := bstep (se 2 (by rfl) ⟨462120, by rfl⟩ : syracuseStep 1232321 = 924241) B924241
theorem B6999493 : Blo 818347 6999493 := bstep (se 4 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 6999493 = 1312405) B1312405
theorem B1232339 : Blo 818347 1232339 := bstep (se 1 (by rfl) ⟨924254, by rfl⟩ : syracuseStep 1232339 = 1848509) B1848509
theorem B1166833 : Blo 818347 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B1232369 : Blo 818347 1232369 := bstep (se 2 (by rfl) ⟨462138, by rfl⟩ : syracuseStep 1232369 = 924277) B924277
theorem B1232387 : Blo 818347 1232387 := bstep (se 1 (by rfl) ⟨924290, by rfl⟩ : syracuseStep 1232387 = 1848581) B1848581
theorem B1232417 : Blo 818347 1232417 := bstep (se 2 (by rfl) ⟨462156, by rfl⟩ : syracuseStep 1232417 = 924313) B924313
theorem B1232435 : Blo 818347 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B9358901 : Blo 818347 9358901 := bstep (se 5 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 9358901 = 877397) B877397
theorem B1232465 : Blo 818347 1232465 := bstep (se 2 (by rfl) ⟨462174, by rfl⟩ : syracuseStep 1232465 = 924349) B924349
theorem B1232483 : Blo 818347 1232483 := bstep (se 1 (by rfl) ⟨924362, by rfl⟩ : syracuseStep 1232483 = 1848725) B1848725
theorem B3001969 : Blo 818347 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B1232513 : Blo 818347 1232513 := bstep (se 2 (by rfl) ⟨462192, by rfl⟩ : syracuseStep 1232513 = 924385) B924385
theorem B1232531 : Blo 818347 1232531 := bstep (se 1 (by rfl) ⟨924398, by rfl⟩ : syracuseStep 1232531 = 1848797) B1848797
theorem B1232561 : Blo 818347 1232561 := bstep (se 2 (by rfl) ⟨462210, by rfl⟩ : syracuseStep 1232561 = 924421) B924421
theorem B1232579 : Blo 818347 1232579 := bstep (se 1 (by rfl) ⟨924434, by rfl⟩ : syracuseStep 1232579 = 1848869) B1848869
theorem B1232609 : Blo 818347 1232609 := bstep (se 2 (by rfl) ⟨462228, by rfl⟩ : syracuseStep 1232609 = 924457) B924457
theorem B1232627 : Blo 818347 1232627 := bstep (se 1 (by rfl) ⟨924470, by rfl⟩ : syracuseStep 1232627 = 1848941) B1848941
theorem B1232657 : Blo 818347 1232657 := bstep (se 2 (by rfl) ⟨462246, by rfl⟩ : syracuseStep 1232657 = 924493) B924493
theorem B1232675 : Blo 818347 1232675 := bstep (se 1 (by rfl) ⟨924506, by rfl⟩ : syracuseStep 1232675 = 1849013) B1849013
theorem B1232705 : Blo 818347 1232705 := bstep (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) B924529
theorem B1232723 : Blo 818347 1232723 := bstep (se 1 (by rfl) ⟨924542, by rfl⟩ : syracuseStep 1232723 = 1849085) B1849085
theorem B2772845 : Blo 818347 2772845 := bstep (se 3 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 2772845 = 1039817) B1039817
theorem B1232753 : Blo 818347 1232753 := bstep (se 2 (by rfl) ⟨462282, by rfl⟩ : syracuseStep 1232753 = 924565) B924565
theorem B1036147 : Blo 818347 1036147 := bstep (se 1 (by rfl) ⟨777110, by rfl⟩ : syracuseStep 1036147 = 1554221) B1554221
theorem B1232771 : Blo 818347 1232771 := bstep (se 1 (by rfl) ⟨924578, by rfl⟩ : syracuseStep 1232771 = 1849157) B1849157
theorem B1232801 : Blo 818347 1232801 := bstep (se 2 (by rfl) ⟨462300, by rfl⟩ : syracuseStep 1232801 = 924601) B924601
theorem B2772899 : Blo 818347 2772899 := bstep (se 1 (by rfl) ⟨2079674, by rfl⟩ : syracuseStep 2772899 = 4159349) B4159349
theorem B2215853 : Blo 818347 2215853 := bstep (se 3 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 2215853 = 830945) B830945
theorem B1232819 : Blo 818347 1232819 := bstep (se 1 (by rfl) ⟨924614, by rfl⟩ : syracuseStep 1232819 = 1849229) B1849229
theorem B1232849 : Blo 818347 1232849 := bstep (se 2 (by rfl) ⟨462318, by rfl⟩ : syracuseStep 1232849 = 924637) B924637
theorem B1036243 : Blo 818347 1036243 := bstep (se 1 (by rfl) ⟨777182, by rfl⟩ : syracuseStep 1036243 = 1554365) B1554365
theorem B1232867 : Blo 818347 1232867 := bstep (se 1 (by rfl) ⟨924650, by rfl⟩ : syracuseStep 1232867 = 1849301) B1849301
theorem B1232897 : Blo 818347 1232897 := bstep (se 2 (by rfl) ⟨462336, by rfl⟩ : syracuseStep 1232897 = 924673) B924673
theorem B1232915 : Blo 818347 1232915 := bstep (se 1 (by rfl) ⟨924686, by rfl⟩ : syracuseStep 1232915 = 1849373) B1849373
theorem B1232945 : Blo 818347 1232945 := bstep (se 2 (by rfl) ⟨462354, by rfl⟩ : syracuseStep 1232945 = 924709) B924709
theorem B1232963 : Blo 818347 1232963 := bstep (se 1 (by rfl) ⟨924722, by rfl⟩ : syracuseStep 1232963 = 1849445) B1849445
theorem B1232993 : Blo 818347 1232993 := bstep (se 2 (by rfl) ⟨462372, by rfl⟩ : syracuseStep 1232993 = 924745) B924745
theorem B1233011 : Blo 818347 1233011 := bstep (se 1 (by rfl) ⟨924758, by rfl⟩ : syracuseStep 1233011 = 1849517) B1849517
theorem B1233041 : Blo 818347 1233041 := bstep (se 2 (by rfl) ⟨462390, by rfl⟩ : syracuseStep 1233041 = 924781) B924781
theorem B1560721 : Blo 818347 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B1233059 : Blo 818347 1233059 := bstep (se 1 (by rfl) ⟨924794, by rfl⟩ : syracuseStep 1233059 = 1849589) B1849589
theorem B2773169 : Blo 818347 2773169 := bstep (se 2 (by rfl) ⟨1039938, by rfl⟩ : syracuseStep 2773169 = 2079877) B2079877
theorem B1167539 : Blo 818347 1167539 := bstep (se 1 (by rfl) ⟨875654, by rfl⟩ : syracuseStep 1167539 = 1751309) B1751309
theorem B1233089 : Blo 818347 1233089 := bstep (se 2 (by rfl) ⟨462408, by rfl⟩ : syracuseStep 1233089 = 924817) B924817
theorem B1233107 : Blo 818347 1233107 := bstep (se 1 (by rfl) ⟨924830, by rfl⟩ : syracuseStep 1233107 = 1849661) B1849661
theorem B1233137 : Blo 818347 1233137 := bstep (se 2 (by rfl) ⟨462426, by rfl⟩ : syracuseStep 1233137 = 924853) B924853
theorem B1233155 : Blo 818347 1233155 := bstep (se 1 (by rfl) ⟨924866, by rfl⟩ : syracuseStep 1233155 = 1849733) B1849733
theorem B1233185 : Blo 818347 1233185 := bstep (se 2 (by rfl) ⟨462444, by rfl⟩ : syracuseStep 1233185 = 924889) B924889
theorem B5132593 : Blo 818347 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1233203 : Blo 818347 1233203 := bstep (se 1 (by rfl) ⟨924902, by rfl⟩ : syracuseStep 1233203 = 1849805) B1849805
theorem B1233233 : Blo 818347 1233233 := bstep (se 2 (by rfl) ⟨462462, by rfl⟩ : syracuseStep 1233233 = 924925) B924925
theorem B1233251 : Blo 818347 1233251 := bstep (se 1 (by rfl) ⟨924938, by rfl⟩ : syracuseStep 1233251 = 1849877) B1849877
theorem B1233281 : Blo 818347 1233281 := bstep (se 2 (by rfl) ⟨462480, by rfl⟩ : syracuseStep 1233281 = 924961) B924961
theorem B1233299 : Blo 818347 1233299 := bstep (se 1 (by rfl) ⟨924974, by rfl⟩ : syracuseStep 1233299 = 1849949) B1849949
theorem B1233329 : Blo 818347 1233329 := bstep (se 2 (by rfl) ⟨462498, by rfl⟩ : syracuseStep 1233329 = 924997) B924997
theorem B1036739 : Blo 818347 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B1233347 : Blo 818347 1233347 := bstep (se 1 (by rfl) ⟨925010, by rfl⟩ : syracuseStep 1233347 = 1850021) B1850021
theorem B1233377 : Blo 818347 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B1233395 : Blo 818347 1233395 := bstep (se 1 (by rfl) ⟨925046, by rfl⟩ : syracuseStep 1233395 = 1850093) B1850093
theorem B1233425 : Blo 818347 1233425 := bstep (se 2 (by rfl) ⟨462534, by rfl⟩ : syracuseStep 1233425 = 925069) B925069
theorem B1233443 : Blo 818347 1233443 := bstep (se 1 (by rfl) ⟨925082, by rfl⟩ : syracuseStep 1233443 = 1850165) B1850165
theorem B1561123 : Blo 818347 1561123 := bstep (se 1 (by rfl) ⟨1170842, by rfl⟩ : syracuseStep 1561123 = 2341685) B2341685
theorem B1233473 : Blo 818347 1233473 := bstep (se 2 (by rfl) ⟨462552, by rfl⟩ : syracuseStep 1233473 = 925105) B925105
theorem B1561169 : Blo 818347 1561169 := bstep (se 2 (by rfl) ⟨585438, by rfl⟩ : syracuseStep 1561169 = 1170877) B1170877
theorem B1233491 : Blo 818347 1233491 := bstep (se 1 (by rfl) ⟨925118, by rfl⟩ : syracuseStep 1233491 = 1850237) B1850237
theorem B1233521 : Blo 818347 1233521 := bstep (se 2 (by rfl) ⟨462570, by rfl⟩ : syracuseStep 1233521 = 925141) B925141
theorem B5067461 : Blo 818347 5067461 := bstep (se 4 (by rfl) ⟨475074, by rfl⟩ : syracuseStep 5067461 = 950149) B950149
theorem B2773709 : Blo 818347 2773709 := bstep (se 3 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 2773709 = 1040141) B1040141
theorem B2773763 : Blo 818347 2773763 := bstep (se 1 (by rfl) ⟨2080322, by rfl⟩ : syracuseStep 2773763 = 4160645) B4160645
theorem B1168177 : Blo 818347 1168177 := bstep (se 2 (by rfl) ⟨438066, by rfl⟩ : syracuseStep 1168177 = 876133) B876133
theorem B4150115 : Blo 818347 4150115 := bstep (se 1 (by rfl) ⟨3112586, by rfl⟩ : syracuseStep 4150115 = 6225173) B6225173
theorem B1168291 : Blo 818347 1168291 := bstep (se 1 (by rfl) ⟨876218, by rfl⟩ : syracuseStep 1168291 = 1752437) B1752437
theorem B4674509 : Blo 818347 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B2774033 : Blo 818347 2774033 := bstep (se 2 (by rfl) ⟨1040262, by rfl⟩ : syracuseStep 2774033 = 2080525) B2080525
theorem B1037443 : Blo 818347 1037443 := bstep (se 1 (by rfl) ⟨778082, by rfl⟩ : syracuseStep 1037443 = 1556165) B1556165
theorem B1037539 : Blo 818347 1037539 := bstep (se 1 (by rfl) ⟨778154, by rfl⟩ : syracuseStep 1037539 = 1556309) B1556309
theorem B6313315 : Blo 818347 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B2774573 : Blo 818347 2774573 := bstep (se 3 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 2774573 = 1040465) B1040465
theorem B2217539 : Blo 818347 2217539 := bstep (se 1 (by rfl) ⟨1663154, by rfl⟩ : syracuseStep 2217539 = 3326309) B3326309
theorem B1496675 : Blo 818347 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B2774627 : Blo 818347 2774627 := bstep (se 1 (by rfl) ⟨2080970, by rfl⟩ : syracuseStep 2774627 = 4161941) B4161941
theorem B4150925 : Blo 818347 4150925 := bstep (se 3 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 4150925 = 1556597) B1556597
theorem B874147 : Blo 818347 874147 := bstep (se 1 (by rfl) ⟨655610, by rfl⟩ : syracuseStep 874147 = 1311221) B1311221
theorem B5265101 : Blo 818347 5265101 := bstep (se 3 (by rfl) ⟨987206, by rfl⟩ : syracuseStep 5265101 = 1974413) B1974413
theorem B1038035 : Blo 818347 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B4675441 : Blo 818347 4675441 := bstep (se 2 (by rfl) ⟨1753290, by rfl⟩ : syracuseStep 4675441 = 3506581) B3506581
theorem B2774897 : Blo 818347 2774897 := bstep (se 2 (by rfl) ⟨1040586, by rfl⟩ : syracuseStep 2774897 = 2081173) B2081173
theorem B874595 : Blo 818347 874595 := bstep (se 1 (by rfl) ⟨655946, by rfl⟩ : syracuseStep 874595 = 1311893) B1311893
theorem B1169635 : Blo 818347 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B1038739 : Blo 818347 1038739 := bstep (se 1 (by rfl) ⟨779054, by rfl⟩ : syracuseStep 1038739 = 1558109) B1558109
theorem B1038835 : Blo 818347 1038835 := bstep (se 1 (by rfl) ⟨779126, by rfl⟩ : syracuseStep 1038835 = 1558253) B1558253
theorem B2808749 : Blo 818347 2808749 := bstep (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) B1053281
theorem B1039331 : Blo 818347 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B3496945 : Blo 818347 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B2809009 : Blo 818347 2809009 := bstep (se 2 (by rfl) ⟨1053378, by rfl⟩ : syracuseStep 2809009 = 2106757) B2106757
theorem B4676899 : Blo 818347 4676899 := bstep (se 1 (by rfl) ⟨3507674, by rfl⟩ : syracuseStep 4676899 = 7015349) B7015349
theorem B1170769 : Blo 818347 1170769 := bstep (se 2 (by rfl) ⟨439038, by rfl⟩ : syracuseStep 1170769 = 878077) B878077
theorem B1170865 : Blo 818347 1170865 := bstep (se 2 (by rfl) ⟨439074, by rfl⟩ : syracuseStep 1170865 = 878149) B878149
theorem B875971 : Blo 818347 875971 := bstep (se 1 (by rfl) ⟨656978, by rfl⟩ : syracuseStep 875971 = 1313957) B1313957
theorem B1040035 : Blo 818347 1040035 := bstep (se 1 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 1040035 = 1560053) B1560053
theorem B1040131 : Blo 818347 1040131 := bstep (se 1 (by rfl) ⟨780098, by rfl⟩ : syracuseStep 1040131 = 1560197) B1560197
theorem B4677425 : Blo 818347 4677425 := bstep (se 2 (by rfl) ⟨1754034, by rfl⟩ : syracuseStep 4677425 = 3508069) B3508069
theorem B1400819 : Blo 818347 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B1040627 : Blo 818347 1040627 := bstep (se 1 (by rfl) ⟨780470, by rfl⟩ : syracuseStep 1040627 = 1560941) B1560941
theorem B2253059 : Blo 818347 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B4153841 : Blo 818347 4153841 := bstep (se 2 (by rfl) ⟨1557690, by rfl⟩ : syracuseStep 4153841 = 3115381) B3115381
theorem B877235 : Blo 818347 877235 := bstep (se 1 (by rfl) ⟨657926, by rfl⟩ : syracuseStep 877235 = 1315853) B1315853
theorem B5989091 : Blo 818347 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B1106689 : Blo 818347 1106689 := bstep (se 2 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 1106689 = 830017) B830017
theorem B4678883 : Blo 818347 4678883 := bstep (se 1 (by rfl) ⟨3509162, by rfl⟩ : syracuseStep 4678883 = 7018325) B7018325
theorem B877987 : Blo 818347 877987 := bstep (se 1 (by rfl) ⟨658490, by rfl⟩ : syracuseStep 877987 = 1316981) B1316981
theorem B1402465 : Blo 818347 1402465 := bstep (se 2 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 1402465 = 1051849) B1051849
theorem B2221681 : Blo 818347 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B2221777 : Blo 818347 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B4155299 : Blo 818347 4155299 := bstep (se 1 (by rfl) ⟨3116474, by rfl⟩ : syracuseStep 4155299 = 6232949) B6232949
theorem B3237937 : Blo 818347 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B2222147 : Blo 818347 2222147 := bstep (se 1 (by rfl) ⟨1666610, by rfl⟩ : syracuseStep 2222147 = 3333221) B3333221
theorem B1894499 : Blo 818347 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B8874481 : Blo 818347 8874481 := bstep (se 2 (by rfl) ⟨3327930, by rfl⟩ : syracuseStep 8874481 = 6655861) B6655861
theorem B4156109 : Blo 818347 4156109 := bstep (se 3 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 4156109 = 1558541) B1558541
theorem B59894549 : Blo 818347 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B3500977 : Blo 818347 3500977 := bstep (se 2 (by rfl) ⟨1312866, by rfl⟩ : syracuseStep 3500977 = 2625733) B2625733
theorem B4680773 : Blo 818347 4680773 := bstep (se 4 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 4680773 = 877645) B877645
theorem B1404049 : Blo 818347 1404049 := bstep (se 2 (by rfl) ⟨526518, by rfl⟩ : syracuseStep 1404049 = 1053037) B1053037
theorem B9334115 : Blo 818347 9334115 := bstep (se 1 (by rfl) ⟨7000586, by rfl⟩ : syracuseStep 9334115 = 14001173) B14001173
theorem B3108365 : Blo 818347 3108365 := bstep (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) B1165637
theorem B17985077 : Blo 818347 17985077 := bstep (se 5 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 17985077 = 1686101) B1686101
theorem B7008241 : Blo 818347 7008241 := bstep (se 2 (by rfl) ⟨2628090, by rfl⟩ : syracuseStep 7008241 = 5256181) B5256181
theorem B8876213 : Blo 818347 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B1405601 : Blo 818347 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B7893773 : Blo 818347 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B4977571 : Blo 818347 4977571 := bstep (se 1 (by rfl) ⟨3733178, by rfl⟩ : syracuseStep 4977571 = 7466357) B7466357
theorem B4159025 : Blo 818347 4159025 := bstep (se 2 (by rfl) ⟨1559634, by rfl⟩ : syracuseStep 4159025 = 3119269) B3119269
theorem B23656049 : Blo 818347 23656049 := bstep (se 2 (by rfl) ⟨8871018, by rfl⟩ : syracuseStep 23656049 = 17742037) B17742037
theorem B6223715 : Blo 818347 6223715 := bstep (se 1 (by rfl) ⟨4667786, by rfl⟩ : syracuseStep 6223715 = 9335573) B9335573
theorem B1898353 : Blo 818347 1898353 := bstep (se 2 (by rfl) ⟨711882, by rfl⟩ : syracuseStep 1898353 = 1423765) B1423765
theorem B4978757 : Blo 818347 4978757 := bstep (se 4 (by rfl) ⟨466758, by rfl⟩ : syracuseStep 4978757 = 933517) B933517
theorem B3111281 : Blo 818347 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B3504653 : Blo 818347 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B2849293 : Blo 818347 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B4160483 : Blo 818347 4160483 := bstep (se 1 (by rfl) ⟨3120362, by rfl⟩ : syracuseStep 4160483 = 6240725) B6240725
theorem B818355 : Blo 818347 818355 := bstep (se 1 (by rfl) ⟨613766, by rfl⟩ : syracuseStep 818355 = 1227533) B1227533
theorem B818371 : Blo 818347 818371 := bstep (se 1 (by rfl) ⟨613778, by rfl⟩ : syracuseStep 818371 = 1227557) B1227557
theorem B818387 : Blo 818347 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B818403 : Blo 818347 818403 := bstep (se 1 (by rfl) ⟨613802, by rfl⟩ : syracuseStep 818403 = 1227605) B1227605
theorem B818419 : Blo 818347 818419 := bstep (se 1 (by rfl) ⟨613814, by rfl⟩ : syracuseStep 818419 = 1227629) B1227629
theorem B818435 : Blo 818347 818435 := bstep (se 1 (by rfl) ⟨613826, by rfl⟩ : syracuseStep 818435 = 1227653) B1227653
theorem B818451 : Blo 818347 818451 := bstep (se 1 (by rfl) ⟨613838, by rfl⟩ : syracuseStep 818451 = 1227677) B1227677
theorem B818467 : Blo 818347 818467 := bstep (se 1 (by rfl) ⟨613850, by rfl⟩ : syracuseStep 818467 = 1227701) B1227701
theorem B818483 : Blo 818347 818483 := bstep (se 1 (by rfl) ⟨613862, by rfl⟩ : syracuseStep 818483 = 1227725) B1227725
theorem B818499 : Blo 818347 818499 := bstep (se 1 (by rfl) ⟨613874, by rfl⟩ : syracuseStep 818499 = 1227749) B1227749
theorem B818515 : Blo 818347 818515 := bstep (se 1 (by rfl) ⟨613886, by rfl⟩ : syracuseStep 818515 = 1227773) B1227773
theorem B818531 : Blo 818347 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B818547 : Blo 818347 818547 := bstep (se 1 (by rfl) ⟨613910, by rfl⟩ : syracuseStep 818547 = 1227821) B1227821
theorem B818563 : Blo 818347 818563 := bstep (se 1 (by rfl) ⟨613922, by rfl⟩ : syracuseStep 818563 = 1227845) B1227845
theorem B818579 : Blo 818347 818579 := bstep (se 1 (by rfl) ⟨613934, by rfl⟩ : syracuseStep 818579 = 1227869) B1227869
theorem B818595 : Blo 818347 818595 := bstep (se 1 (by rfl) ⟨613946, by rfl⟩ : syracuseStep 818595 = 1227893) B1227893
theorem B1244593 : Blo 818347 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B818611 : Blo 818347 818611 := bstep (se 1 (by rfl) ⟨613958, by rfl⟩ : syracuseStep 818611 = 1227917) B1227917
theorem B818627 : Blo 818347 818627 := bstep (se 1 (by rfl) ⟨613970, by rfl⟩ : syracuseStep 818627 = 1227941) B1227941
theorem B818643 : Blo 818347 818643 := bstep (se 1 (by rfl) ⟨613982, by rfl⟩ : syracuseStep 818643 = 1227965) B1227965
theorem B818659 : Blo 818347 818659 := bstep (se 1 (by rfl) ⟨613994, by rfl⟩ : syracuseStep 818659 = 1227989) B1227989
theorem B818675 : Blo 818347 818675 := bstep (se 1 (by rfl) ⟨614006, by rfl⟩ : syracuseStep 818675 = 1228013) B1228013
theorem B818691 : Blo 818347 818691 := bstep (se 1 (by rfl) ⟨614018, by rfl⟩ : syracuseStep 818691 = 1228037) B1228037
theorem B818707 : Blo 818347 818707 := bstep (se 1 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 818707 = 1228061) B1228061
theorem B818723 : Blo 818347 818723 := bstep (se 1 (by rfl) ⟨614042, by rfl⟩ : syracuseStep 818723 = 1228085) B1228085
theorem B818739 : Blo 818347 818739 := bstep (se 1 (by rfl) ⟨614054, by rfl⟩ : syracuseStep 818739 = 1228109) B1228109
theorem B10649141 : Blo 818347 10649141 := bstep (se 5 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 10649141 = 998357) B998357
theorem B818755 : Blo 818347 818755 := bstep (se 1 (by rfl) ⟨614066, by rfl⟩ : syracuseStep 818755 = 1228133) B1228133
theorem B818771 : Blo 818347 818771 := bstep (se 1 (by rfl) ⟨614078, by rfl⟩ : syracuseStep 818771 = 1228157) B1228157
theorem B818787 : Blo 818347 818787 := bstep (se 1 (by rfl) ⟨614090, by rfl⟩ : syracuseStep 818787 = 1228181) B1228181
theorem B818803 : Blo 818347 818803 := bstep (se 1 (by rfl) ⟨614102, by rfl⟩ : syracuseStep 818803 = 1228205) B1228205
theorem B818819 : Blo 818347 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B818835 : Blo 818347 818835 := bstep (se 1 (by rfl) ⟨614126, by rfl⟩ : syracuseStep 818835 = 1228253) B1228253
theorem B818851 : Blo 818347 818851 := bstep (se 1 (by rfl) ⟨614138, by rfl⟩ : syracuseStep 818851 = 1228277) B1228277
theorem B818867 : Blo 818347 818867 := bstep (se 1 (by rfl) ⟨614150, by rfl⟩ : syracuseStep 818867 = 1228301) B1228301
theorem B818883 : Blo 818347 818883 := bstep (se 1 (by rfl) ⟨614162, by rfl⟩ : syracuseStep 818883 = 1228325) B1228325
theorem B2490061 : Blo 818347 2490061 := bstep (se 3 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 2490061 = 933773) B933773
theorem B818899 : Blo 818347 818899 := bstep (se 1 (by rfl) ⟨614174, by rfl⟩ : syracuseStep 818899 = 1228349) B1228349
theorem B818915 : Blo 818347 818915 := bstep (se 1 (by rfl) ⟨614186, by rfl⟩ : syracuseStep 818915 = 1228373) B1228373
theorem B818931 : Blo 818347 818931 := bstep (se 1 (by rfl) ⟨614198, by rfl⟩ : syracuseStep 818931 = 1228397) B1228397
theorem B818947 : Blo 818347 818947 := bstep (se 1 (by rfl) ⟨614210, by rfl⟩ : syracuseStep 818947 = 1228421) B1228421
theorem B4161293 : Blo 818347 4161293 := bstep (se 3 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 4161293 = 1560485) B1560485
theorem B818963 : Blo 818347 818963 := bstep (se 1 (by rfl) ⟨614222, by rfl⟩ : syracuseStep 818963 = 1228445) B1228445
theorem B3112739 : Blo 818347 3112739 := bstep (se 1 (by rfl) ⟨2334554, by rfl⟩ : syracuseStep 3112739 = 4669109) B4669109
theorem B818979 : Blo 818347 818979 := bstep (se 1 (by rfl) ⟨614234, by rfl⟩ : syracuseStep 818979 = 1228469) B1228469
theorem B818995 : Blo 818347 818995 := bstep (se 1 (by rfl) ⟨614246, by rfl⟩ : syracuseStep 818995 = 1228493) B1228493
theorem B819011 : Blo 818347 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B819027 : Blo 818347 819027 := bstep (se 1 (by rfl) ⟨614270, by rfl⟩ : syracuseStep 819027 = 1228541) B1228541
theorem B1867619 : Blo 818347 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B819043 : Blo 818347 819043 := bstep (se 1 (by rfl) ⟨614282, by rfl⟩ : syracuseStep 819043 = 1228565) B1228565
theorem B5603185 : Blo 818347 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B819059 : Blo 818347 819059 := bstep (se 1 (by rfl) ⟨614294, by rfl⟩ : syracuseStep 819059 = 1228589) B1228589
theorem B819075 : Blo 818347 819075 := bstep (se 1 (by rfl) ⟨614306, by rfl⟩ : syracuseStep 819075 = 1228613) B1228613
theorem B819091 : Blo 818347 819091 := bstep (se 1 (by rfl) ⟨614318, by rfl⟩ : syracuseStep 819091 = 1228637) B1228637
theorem B819107 : Blo 818347 819107 := bstep (se 1 (by rfl) ⟨614330, by rfl⟩ : syracuseStep 819107 = 1228661) B1228661
theorem B819123 : Blo 818347 819123 := bstep (se 1 (by rfl) ⟨614342, by rfl⟩ : syracuseStep 819123 = 1228685) B1228685
theorem B819139 : Blo 818347 819139 := bstep (se 1 (by rfl) ⟨614354, by rfl⟩ : syracuseStep 819139 = 1228709) B1228709
theorem B819155 : Blo 818347 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B819171 : Blo 818347 819171 := bstep (se 1 (by rfl) ⟨614378, by rfl⟩ : syracuseStep 819171 = 1228757) B1228757
theorem B819187 : Blo 818347 819187 := bstep (se 1 (by rfl) ⟨614390, by rfl⟩ : syracuseStep 819187 = 1228781) B1228781
theorem B819211 : Blo 818347 819211 := bstep (se 1 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 819211 = 1228817) B1228817
theorem B819223 : Blo 818347 819223 := bstep (se 1 (by rfl) ⟨614417, by rfl⟩ : syracuseStep 819223 = 1228835) B1228835
theorem B819243 : Blo 818347 819243 := bstep (se 1 (by rfl) ⟨614432, by rfl⟩ : syracuseStep 819243 = 1228865) B1228865
theorem B819255 : Blo 818347 819255 := bstep (se 1 (by rfl) ⟨614441, by rfl⟩ : syracuseStep 819255 = 1228883) B1228883
theorem B819275 : Blo 818347 819275 := bstep (se 1 (by rfl) ⟨614456, by rfl⟩ : syracuseStep 819275 = 1228913) B1228913
theorem B819287 : Blo 818347 819287 := bstep (se 1 (by rfl) ⟨614465, by rfl⟩ : syracuseStep 819287 = 1228931) B1228931
theorem B819307 : Blo 818347 819307 := bstep (se 1 (by rfl) ⟨614480, by rfl⟩ : syracuseStep 819307 = 1228961) B1228961
theorem B819319 : Blo 818347 819319 := bstep (se 1 (by rfl) ⟨614489, by rfl⟩ : syracuseStep 819319 = 1228979) B1228979
theorem B819339 : Blo 818347 819339 := bstep (se 1 (by rfl) ⟨614504, by rfl⟩ : syracuseStep 819339 = 1229009) B1229009
theorem B819351 : Blo 818347 819351 := bstep (se 1 (by rfl) ⟨614513, by rfl⟩ : syracuseStep 819351 = 1229027) B1229027
theorem B819371 : Blo 818347 819371 := bstep (se 1 (by rfl) ⟨614528, by rfl⟩ : syracuseStep 819371 = 1229057) B1229057
theorem B819383 : Blo 818347 819383 := bstep (se 1 (by rfl) ⟨614537, by rfl⟩ : syracuseStep 819383 = 1229075) B1229075
theorem B819403 : Blo 818347 819403 := bstep (se 1 (by rfl) ⟨614552, by rfl⟩ : syracuseStep 819403 = 1229105) B1229105
theorem B819415 : Blo 818347 819415 := bstep (se 1 (by rfl) ⟨614561, by rfl⟩ : syracuseStep 819415 = 1229123) B1229123
theorem B819435 : Blo 818347 819435 := bstep (se 1 (by rfl) ⟨614576, by rfl⟩ : syracuseStep 819435 = 1229153) B1229153
theorem B819447 : Blo 818347 819447 := bstep (se 1 (by rfl) ⟨614585, by rfl⟩ : syracuseStep 819447 = 1229171) B1229171
theorem B17268997 : Blo 818347 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B819467 : Blo 818347 819467 := bstep (se 1 (by rfl) ⟨614600, by rfl⟩ : syracuseStep 819467 = 1229201) B1229201
theorem B819479 : Blo 818347 819479 := bstep (se 1 (by rfl) ⟨614609, by rfl⟩ : syracuseStep 819479 = 1229219) B1229219
theorem B819499 : Blo 818347 819499 := bstep (se 1 (by rfl) ⟨614624, by rfl⟩ : syracuseStep 819499 = 1229249) B1229249
theorem B819511 : Blo 818347 819511 := bstep (se 1 (by rfl) ⟨614633, by rfl⟩ : syracuseStep 819511 = 1229267) B1229267
theorem B819531 : Blo 818347 819531 := bstep (se 1 (by rfl) ⟨614648, by rfl⟩ : syracuseStep 819531 = 1229297) B1229297
theorem B819543 : Blo 818347 819543 := bstep (se 1 (by rfl) ⟨614657, by rfl⟩ : syracuseStep 819543 = 1229315) B1229315
theorem B819563 : Blo 818347 819563 := bstep (se 1 (by rfl) ⟨614672, by rfl⟩ : syracuseStep 819563 = 1229345) B1229345
theorem B819575 : Blo 818347 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B819595 : Blo 818347 819595 := bstep (se 1 (by rfl) ⟨614696, by rfl⟩ : syracuseStep 819595 = 1229393) B1229393
theorem B819607 : Blo 818347 819607 := bstep (se 1 (by rfl) ⟨614705, by rfl⟩ : syracuseStep 819607 = 1229411) B1229411
theorem B819627 : Blo 818347 819627 := bstep (se 1 (by rfl) ⟨614720, by rfl⟩ : syracuseStep 819627 = 1229441) B1229441
theorem B819639 : Blo 818347 819639 := bstep (se 1 (by rfl) ⟨614729, by rfl⟩ : syracuseStep 819639 = 1229459) B1229459
theorem B819659 : Blo 818347 819659 := bstep (se 1 (by rfl) ⟨614744, by rfl⟩ : syracuseStep 819659 = 1229489) B1229489
theorem B819671 : Blo 818347 819671 := bstep (se 1 (by rfl) ⟨614753, by rfl⟩ : syracuseStep 819671 = 1229507) B1229507
theorem B3113437 : Blo 818347 3113437 := bstep (se 3 (by rfl) ⟨583769, by rfl⟩ : syracuseStep 3113437 = 1167539) B1167539
theorem B819691 : Blo 818347 819691 := bstep (se 1 (by rfl) ⟨614768, by rfl⟩ : syracuseStep 819691 = 1229537) B1229537
theorem B819703 : Blo 818347 819703 := bstep (se 1 (by rfl) ⟨614777, by rfl⟩ : syracuseStep 819703 = 1229555) B1229555
theorem B819723 : Blo 818347 819723 := bstep (se 1 (by rfl) ⟨614792, by rfl⟩ : syracuseStep 819723 = 1229585) B1229585
theorem B819735 : Blo 818347 819735 := bstep (se 1 (by rfl) ⟨614801, by rfl⟩ : syracuseStep 819735 = 1229603) B1229603
theorem B819755 : Blo 818347 819755 := bstep (se 1 (by rfl) ⟨614816, by rfl⟩ : syracuseStep 819755 = 1229633) B1229633
theorem B3736115 : Blo 818347 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B819767 : Blo 818347 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B3506753 : Blo 818347 3506753 := bstep (se 2 (by rfl) ⟨1315032, by rfl⟩ : syracuseStep 3506753 = 2630065) B2630065
theorem B819787 : Blo 818347 819787 := bstep (se 1 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 819787 = 1229681) B1229681
theorem B819799 : Blo 818347 819799 := bstep (se 1 (by rfl) ⟨614849, by rfl⟩ : syracuseStep 819799 = 1229699) B1229699
theorem B819819 : Blo 818347 819819 := bstep (se 1 (by rfl) ⟨614864, by rfl⟩ : syracuseStep 819819 = 1229729) B1229729
theorem B819831 : Blo 818347 819831 := bstep (se 1 (by rfl) ⟨614873, by rfl⟩ : syracuseStep 819831 = 1229747) B1229747
theorem B8422019 : Blo 818347 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B819851 : Blo 818347 819851 := bstep (se 1 (by rfl) ⟨614888, by rfl⟩ : syracuseStep 819851 = 1229777) B1229777
theorem B819863 : Blo 818347 819863 := bstep (se 1 (by rfl) ⟨614897, by rfl⟩ : syracuseStep 819863 = 1229795) B1229795
theorem B819883 : Blo 818347 819883 := bstep (se 1 (by rfl) ⟨614912, by rfl⟩ : syracuseStep 819883 = 1229825) B1229825
theorem B819895 : Blo 818347 819895 := bstep (se 1 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 819895 = 1229843) B1229843
theorem B2622145 : Blo 818347 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B819915 : Blo 818347 819915 := bstep (se 1 (by rfl) ⟨614936, by rfl⟩ : syracuseStep 819915 = 1229873) B1229873
theorem B819927 : Blo 818347 819927 := bstep (se 1 (by rfl) ⟨614945, by rfl⟩ : syracuseStep 819927 = 1229891) B1229891
theorem B4162265 : Blo 818347 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B819947 : Blo 818347 819947 := bstep (se 1 (by rfl) ⟨614960, by rfl⟩ : syracuseStep 819947 = 1229921) B1229921
theorem B819959 : Blo 818347 819959 := bstep (se 1 (by rfl) ⟨614969, by rfl⟩ : syracuseStep 819959 = 1229939) B1229939
theorem B819979 : Blo 818347 819979 := bstep (se 1 (by rfl) ⟨614984, by rfl⟩ : syracuseStep 819979 = 1229969) B1229969
theorem B819991 : Blo 818347 819991 := bstep (se 1 (by rfl) ⟨614993, by rfl⟩ : syracuseStep 819991 = 1229987) B1229987
theorem B820011 : Blo 818347 820011 := bstep (se 1 (by rfl) ⟨615008, by rfl⟩ : syracuseStep 820011 = 1230017) B1230017
theorem B820023 : Blo 818347 820023 := bstep (se 1 (by rfl) ⟨615017, by rfl⟩ : syracuseStep 820023 = 1230035) B1230035
theorem B820043 : Blo 818347 820043 := bstep (se 1 (by rfl) ⟨615032, by rfl⟩ : syracuseStep 820043 = 1230065) B1230065
theorem B820055 : Blo 818347 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B2491229 : Blo 818347 2491229 := bstep (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) B934211
theorem B820075 : Blo 818347 820075 := bstep (se 1 (by rfl) ⟨615056, by rfl⟩ : syracuseStep 820075 = 1230113) B1230113
theorem B820087 : Blo 818347 820087 := bstep (se 1 (by rfl) ⟨615065, by rfl⟩ : syracuseStep 820087 = 1230131) B1230131
theorem B820107 : Blo 818347 820107 := bstep (se 1 (by rfl) ⟨615080, by rfl⟩ : syracuseStep 820107 = 1230161) B1230161
theorem B820119 : Blo 818347 820119 := bstep (se 1 (by rfl) ⟨615089, by rfl⟩ : syracuseStep 820119 = 1230179) B1230179
theorem B820139 : Blo 818347 820139 := bstep (se 1 (by rfl) ⟨615104, by rfl⟩ : syracuseStep 820139 = 1230209) B1230209
theorem B820151 : Blo 818347 820151 := bstep (se 1 (by rfl) ⟨615113, by rfl⟩ : syracuseStep 820151 = 1230227) B1230227
theorem B820171 : Blo 818347 820171 := bstep (se 1 (by rfl) ⟨615128, by rfl⟩ : syracuseStep 820171 = 1230257) B1230257
theorem B820183 : Blo 818347 820183 := bstep (se 1 (by rfl) ⟨615137, by rfl⟩ : syracuseStep 820183 = 1230275) B1230275
theorem B820203 : Blo 818347 820203 := bstep (se 1 (by rfl) ⟨615152, by rfl⟩ : syracuseStep 820203 = 1230305) B1230305
theorem B820215 : Blo 818347 820215 := bstep (se 1 (by rfl) ⟨615161, by rfl⟩ : syracuseStep 820215 = 1230323) B1230323
theorem B1475585 : Blo 818347 1475585 := bstep (se 2 (by rfl) ⟨553344, by rfl⟩ : syracuseStep 1475585 = 1106689) B1106689
theorem B820235 : Blo 818347 820235 := bstep (se 1 (by rfl) ⟨615176, by rfl⟩ : syracuseStep 820235 = 1230353) B1230353
theorem B820247 : Blo 818347 820247 := bstep (se 1 (by rfl) ⟨615185, by rfl⟩ : syracuseStep 820247 = 1230371) B1230371
theorem B820267 : Blo 818347 820267 := bstep (se 1 (by rfl) ⟨615200, by rfl⟩ : syracuseStep 820267 = 1230401) B1230401
theorem B820279 : Blo 818347 820279 := bstep (se 1 (by rfl) ⟨615209, by rfl⟩ : syracuseStep 820279 = 1230419) B1230419
theorem B820299 : Blo 818347 820299 := bstep (se 1 (by rfl) ⟨615224, by rfl⟩ : syracuseStep 820299 = 1230449) B1230449
theorem B820311 : Blo 818347 820311 := bstep (se 1 (by rfl) ⟨615233, by rfl⟩ : syracuseStep 820311 = 1230467) B1230467
theorem B820331 : Blo 818347 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B820343 : Blo 818347 820343 := bstep (se 1 (by rfl) ⟨615257, by rfl⟩ : syracuseStep 820343 = 1230515) B1230515
theorem B820363 : Blo 818347 820363 := bstep (se 1 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 820363 = 1230545) B1230545
theorem B820375 : Blo 818347 820375 := bstep (se 1 (by rfl) ⟨615281, by rfl⟩ : syracuseStep 820375 = 1230563) B1230563
theorem B820395 : Blo 818347 820395 := bstep (se 1 (by rfl) ⟨615296, by rfl⟩ : syracuseStep 820395 = 1230593) B1230593
theorem B820407 : Blo 818347 820407 := bstep (se 1 (by rfl) ⟨615305, by rfl⟩ : syracuseStep 820407 = 1230611) B1230611
theorem B820427 : Blo 818347 820427 := bstep (se 1 (by rfl) ⟨615320, by rfl⟩ : syracuseStep 820427 = 1230641) B1230641
theorem B820439 : Blo 818347 820439 := bstep (se 1 (by rfl) ⟨615329, by rfl⟩ : syracuseStep 820439 = 1230659) B1230659
theorem B1967321 : Blo 818347 1967321 := bstep (se 2 (by rfl) ⟨737745, by rfl⟩ : syracuseStep 1967321 = 1475491) B1475491
theorem B820459 : Blo 818347 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B820471 : Blo 818347 820471 := bstep (se 1 (by rfl) ⟨615353, by rfl⟩ : syracuseStep 820471 = 1230707) B1230707
theorem B820491 : Blo 818347 820491 := bstep (se 1 (by rfl) ⟨615368, by rfl⟩ : syracuseStep 820491 = 1230737) B1230737
theorem B1049879 : Blo 818347 1049879 := bstep (se 1 (by rfl) ⟨787409, by rfl⟩ : syracuseStep 1049879 = 1574819) B1574819
theorem B820503 : Blo 818347 820503 := bstep (se 1 (by rfl) ⟨615377, by rfl⟩ : syracuseStep 820503 = 1230755) B1230755
theorem B820523 : Blo 818347 820523 := bstep (se 1 (by rfl) ⟨615392, by rfl⟩ : syracuseStep 820523 = 1230785) B1230785
theorem B820535 : Blo 818347 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B3999041 : Blo 818347 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B820555 : Blo 818347 820555 := bstep (se 1 (by rfl) ⟨615416, by rfl⟩ : syracuseStep 820555 = 1230833) B1230833
theorem B820567 : Blo 818347 820567 := bstep (se 1 (by rfl) ⟨615425, by rfl⟩ : syracuseStep 820567 = 1230851) B1230851
theorem B820587 : Blo 818347 820587 := bstep (se 1 (by rfl) ⟨615440, by rfl⟩ : syracuseStep 820587 = 1230881) B1230881
theorem B820599 : Blo 818347 820599 := bstep (se 1 (by rfl) ⟨615449, by rfl⟩ : syracuseStep 820599 = 1230899) B1230899
theorem B820619 : Blo 818347 820619 := bstep (se 1 (by rfl) ⟨615464, by rfl⟩ : syracuseStep 820619 = 1230929) B1230929
theorem B26936725 : Blo 818347 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B820631 : Blo 818347 820631 := bstep (se 1 (by rfl) ⟨615473, by rfl⟩ : syracuseStep 820631 = 1230947) B1230947
theorem B820651 : Blo 818347 820651 := bstep (se 1 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 820651 = 1230977) B1230977
theorem B820663 : Blo 818347 820663 := bstep (se 1 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 820663 = 1230995) B1230995
theorem B820683 : Blo 818347 820683 := bstep (se 1 (by rfl) ⟨615512, by rfl⟩ : syracuseStep 820683 = 1231025) B1231025
theorem B820695 : Blo 818347 820695 := bstep (se 1 (by rfl) ⟨615521, by rfl⟩ : syracuseStep 820695 = 1231043) B1231043
theorem B820715 : Blo 818347 820715 := bstep (se 1 (by rfl) ⟨615536, by rfl⟩ : syracuseStep 820715 = 1231073) B1231073
theorem B820727 : Blo 818347 820727 := bstep (se 1 (by rfl) ⟨615545, by rfl⟩ : syracuseStep 820727 = 1231091) B1231091
theorem B820747 : Blo 818347 820747 := bstep (se 1 (by rfl) ⟨615560, by rfl⟩ : syracuseStep 820747 = 1231121) B1231121
theorem B820759 : Blo 818347 820759 := bstep (se 1 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 820759 = 1231139) B1231139
theorem B820779 : Blo 818347 820779 := bstep (se 1 (by rfl) ⟨615584, by rfl⟩ : syracuseStep 820779 = 1231169) B1231169
theorem B820791 : Blo 818347 820791 := bstep (se 1 (by rfl) ⟨615593, by rfl⟩ : syracuseStep 820791 = 1231187) B1231187
theorem B820811 : Blo 818347 820811 := bstep (se 1 (by rfl) ⟨615608, by rfl⟩ : syracuseStep 820811 = 1231217) B1231217
theorem B820823 : Blo 818347 820823 := bstep (se 1 (by rfl) ⟨615617, by rfl⟩ : syracuseStep 820823 = 1231235) B1231235
theorem B820843 : Blo 818347 820843 := bstep (se 1 (by rfl) ⟨615632, by rfl⟩ : syracuseStep 820843 = 1231265) B1231265
theorem B820855 : Blo 818347 820855 := bstep (se 1 (by rfl) ⟨615641, by rfl⟩ : syracuseStep 820855 = 1231283) B1231283
theorem B5244547 : Blo 818347 5244547 := bstep (se 1 (by rfl) ⟨3933410, by rfl⟩ : syracuseStep 5244547 = 7866821) B7866821
theorem B820875 : Blo 818347 820875 := bstep (se 1 (by rfl) ⟨615656, by rfl⟩ : syracuseStep 820875 = 1231313) B1231313
theorem B8849047 : Blo 818347 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B984727 : Blo 818347 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B820887 : Blo 818347 820887 := bstep (se 1 (by rfl) ⟨615665, by rfl⟩ : syracuseStep 820887 = 1231331) B1231331
theorem B820907 : Blo 818347 820907 := bstep (se 1 (by rfl) ⟨615680, by rfl⟩ : syracuseStep 820907 = 1231361) B1231361
theorem B820919 : Blo 818347 820919 := bstep (se 1 (by rfl) ⟨615689, by rfl⟩ : syracuseStep 820919 = 1231379) B1231379
theorem B820939 : Blo 818347 820939 := bstep (se 1 (by rfl) ⟨615704, by rfl⟩ : syracuseStep 820939 = 1231409) B1231409
theorem B820951 : Blo 818347 820951 := bstep (se 1 (by rfl) ⟨615713, by rfl⟩ : syracuseStep 820951 = 1231427) B1231427
theorem B3114713 : Blo 818347 3114713 := bstep (se 2 (by rfl) ⟨1168017, by rfl⟩ : syracuseStep 3114713 = 2336035) B2336035
theorem B820971 : Blo 818347 820971 := bstep (se 1 (by rfl) ⟨615728, by rfl⟩ : syracuseStep 820971 = 1231457) B1231457
theorem B820983 : Blo 818347 820983 := bstep (se 1 (by rfl) ⟨615737, by rfl⟩ : syracuseStep 820983 = 1231475) B1231475
theorem B821003 : Blo 818347 821003 := bstep (se 1 (by rfl) ⟨615752, by rfl⟩ : syracuseStep 821003 = 1231505) B1231505
theorem B821015 : Blo 818347 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B821035 : Blo 818347 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B821047 : Blo 818347 821047 := bstep (se 1 (by rfl) ⟨615785, by rfl⟩ : syracuseStep 821047 = 1231571) B1231571
theorem B821067 : Blo 818347 821067 := bstep (se 1 (by rfl) ⟨615800, by rfl⟩ : syracuseStep 821067 = 1231601) B1231601
theorem B821079 : Blo 818347 821079 := bstep (se 1 (by rfl) ⟨615809, by rfl⟩ : syracuseStep 821079 = 1231619) B1231619
theorem B821099 : Blo 818347 821099 := bstep (se 1 (by rfl) ⟨615824, by rfl⟩ : syracuseStep 821099 = 1231649) B1231649
theorem B821111 : Blo 818347 821111 := bstep (se 1 (by rfl) ⟨615833, by rfl⟩ : syracuseStep 821111 = 1231667) B1231667
theorem B821131 : Blo 818347 821131 := bstep (se 1 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 821131 = 1231697) B1231697
theorem B821143 : Blo 818347 821143 := bstep (se 1 (by rfl) ⟨615857, by rfl⟩ : syracuseStep 821143 = 1231715) B1231715
theorem B821163 : Blo 818347 821163 := bstep (se 1 (by rfl) ⟨615872, by rfl⟩ : syracuseStep 821163 = 1231745) B1231745
theorem B821175 : Blo 818347 821175 := bstep (se 1 (by rfl) ⟨615881, by rfl⟩ : syracuseStep 821175 = 1231763) B1231763
theorem B821195 : Blo 818347 821195 := bstep (se 1 (by rfl) ⟨615896, by rfl⟩ : syracuseStep 821195 = 1231793) B1231793
theorem B821207 : Blo 818347 821207 := bstep (se 1 (by rfl) ⟨615905, by rfl⟩ : syracuseStep 821207 = 1231811) B1231811
theorem B821227 : Blo 818347 821227 := bstep (se 1 (by rfl) ⟨615920, by rfl⟩ : syracuseStep 821227 = 1231841) B1231841
theorem B821239 : Blo 818347 821239 := bstep (se 1 (by rfl) ⟨615929, by rfl⟩ : syracuseStep 821239 = 1231859) B1231859
theorem B821259 : Blo 818347 821259 := bstep (se 1 (by rfl) ⟨615944, by rfl⟩ : syracuseStep 821259 = 1231889) B1231889
theorem B29919253 : Blo 818347 29919253 := bstep (se 6 (by rfl) ⟨701232, by rfl⟩ : syracuseStep 29919253 = 1402465) B1402465
theorem B821271 : Blo 818347 821271 := bstep (se 1 (by rfl) ⟨615953, by rfl⟩ : syracuseStep 821271 = 1231907) B1231907
theorem B821291 : Blo 818347 821291 := bstep (se 1 (by rfl) ⟨615968, by rfl⟩ : syracuseStep 821291 = 1231937) B1231937
theorem B821303 : Blo 818347 821303 := bstep (se 1 (by rfl) ⟨615977, by rfl⟩ : syracuseStep 821303 = 1231955) B1231955
theorem B821323 : Blo 818347 821323 := bstep (se 1 (by rfl) ⟨615992, by rfl⟩ : syracuseStep 821323 = 1231985) B1231985
theorem B821335 : Blo 818347 821335 := bstep (se 1 (by rfl) ⟨616001, by rfl⟩ : syracuseStep 821335 = 1232003) B1232003
theorem B821355 : Blo 818347 821355 := bstep (se 1 (by rfl) ⟨616016, by rfl⟩ : syracuseStep 821355 = 1232033) B1232033
theorem B821367 : Blo 818347 821367 := bstep (se 1 (by rfl) ⟨616025, by rfl⟩ : syracuseStep 821367 = 1232051) B1232051
theorem B821387 : Blo 818347 821387 := bstep (se 1 (by rfl) ⟨616040, by rfl⟩ : syracuseStep 821387 = 1232081) B1232081
theorem B821399 : Blo 818347 821399 := bstep (se 1 (by rfl) ⟨616049, by rfl⟩ : syracuseStep 821399 = 1232099) B1232099
theorem B821419 : Blo 818347 821419 := bstep (se 1 (by rfl) ⟨616064, by rfl⟩ : syracuseStep 821419 = 1232129) B1232129
theorem B821431 : Blo 818347 821431 := bstep (se 1 (by rfl) ⟨616073, by rfl⟩ : syracuseStep 821431 = 1232147) B1232147
theorem B3508427 : Blo 818347 3508427 := bstep (se 1 (by rfl) ⟨2631320, by rfl⟩ : syracuseStep 3508427 = 5262641) B5262641
theorem B821451 : Blo 818347 821451 := bstep (se 1 (by rfl) ⟨616088, by rfl⟩ : syracuseStep 821451 = 1232177) B1232177
theorem B821463 : Blo 818347 821463 := bstep (se 1 (by rfl) ⟨616097, by rfl⟩ : syracuseStep 821463 = 1232195) B1232195
theorem B821483 : Blo 818347 821483 := bstep (se 1 (by rfl) ⟨616112, by rfl⟩ : syracuseStep 821483 = 1232225) B1232225
theorem B821495 : Blo 818347 821495 := bstep (se 1 (by rfl) ⟨616121, by rfl⟩ : syracuseStep 821495 = 1232243) B1232243
theorem B1476875 : Blo 818347 1476875 := bstep (se 1 (by rfl) ⟨1107656, by rfl⟩ : syracuseStep 1476875 = 2215313) B2215313
theorem B821515 : Blo 818347 821515 := bstep (se 1 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 821515 = 1232273) B1232273
theorem B821527 : Blo 818347 821527 := bstep (se 1 (by rfl) ⟨616145, by rfl⟩ : syracuseStep 821527 = 1232291) B1232291
theorem B821547 : Blo 818347 821547 := bstep (se 1 (by rfl) ⟨616160, by rfl⟩ : syracuseStep 821547 = 1232321) B1232321
theorem B7113005 : Blo 818347 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B821559 : Blo 818347 821559 := bstep (se 1 (by rfl) ⟨616169, by rfl⟩ : syracuseStep 821559 = 1232339) B1232339
theorem B821579 : Blo 818347 821579 := bstep (se 1 (by rfl) ⟨616184, by rfl⟩ : syracuseStep 821579 = 1232369) B1232369
theorem B821591 : Blo 818347 821591 := bstep (se 1 (by rfl) ⟨616193, by rfl⟩ : syracuseStep 821591 = 1232387) B1232387
theorem B821611 : Blo 818347 821611 := bstep (se 1 (by rfl) ⟨616208, by rfl⟩ : syracuseStep 821611 = 1232417) B1232417
theorem B821623 : Blo 818347 821623 := bstep (se 1 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 821623 = 1232435) B1232435
theorem B821643 : Blo 818347 821643 := bstep (se 1 (by rfl) ⟨616232, by rfl⟩ : syracuseStep 821643 = 1232465) B1232465
theorem B821655 : Blo 818347 821655 := bstep (se 1 (by rfl) ⟨616241, by rfl⟩ : syracuseStep 821655 = 1232483) B1232483
theorem B821675 : Blo 818347 821675 := bstep (se 1 (by rfl) ⟨616256, by rfl⟩ : syracuseStep 821675 = 1232513) B1232513
theorem B821687 : Blo 818347 821687 := bstep (se 1 (by rfl) ⟨616265, by rfl⟩ : syracuseStep 821687 = 1232531) B1232531
theorem B821707 : Blo 818347 821707 := bstep (se 1 (by rfl) ⟨616280, by rfl⟩ : syracuseStep 821707 = 1232561) B1232561
theorem B821719 : Blo 818347 821719 := bstep (se 1 (by rfl) ⟨616289, by rfl⟩ : syracuseStep 821719 = 1232579) B1232579
theorem B821739 : Blo 818347 821739 := bstep (se 1 (by rfl) ⟨616304, by rfl⟩ : syracuseStep 821739 = 1232609) B1232609
theorem B821751 : Blo 818347 821751 := bstep (se 1 (by rfl) ⟨616313, by rfl⟩ : syracuseStep 821751 = 1232627) B1232627
theorem B1247755 : Blo 818347 1247755 := bstep (se 1 (by rfl) ⟨935816, by rfl⟩ : syracuseStep 1247755 = 1871633) B1871633
theorem B821771 : Blo 818347 821771 := bstep (se 1 (by rfl) ⟨616328, by rfl⟩ : syracuseStep 821771 = 1232657) B1232657
theorem B821783 : Blo 818347 821783 := bstep (se 1 (by rfl) ⟨616337, by rfl⟩ : syracuseStep 821783 = 1232675) B1232675
theorem B821803 : Blo 818347 821803 := bstep (se 1 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 821803 = 1232705) B1232705
theorem B821815 : Blo 818347 821815 := bstep (se 1 (by rfl) ⟨616361, by rfl⟩ : syracuseStep 821815 = 1232723) B1232723
theorem B821835 : Blo 818347 821835 := bstep (se 1 (by rfl) ⟨616376, by rfl⟩ : syracuseStep 821835 = 1232753) B1232753
theorem B821847 : Blo 818347 821847 := bstep (se 1 (by rfl) ⟨616385, by rfl⟩ : syracuseStep 821847 = 1232771) B1232771
theorem B2624093 : Blo 818347 2624093 := bstep (se 3 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 2624093 = 984035) B984035
theorem B821867 : Blo 818347 821867 := bstep (se 1 (by rfl) ⟨616400, by rfl⟩ : syracuseStep 821867 = 1232801) B1232801
theorem B1477235 : Blo 818347 1477235 := bstep (se 1 (by rfl) ⟨1107926, by rfl⟩ : syracuseStep 1477235 = 2215853) B2215853
theorem B821879 : Blo 818347 821879 := bstep (se 1 (by rfl) ⟨616409, by rfl⟩ : syracuseStep 821879 = 1232819) B1232819
theorem B821899 : Blo 818347 821899 := bstep (se 1 (by rfl) ⟨616424, by rfl⟩ : syracuseStep 821899 = 1232849) B1232849
theorem B821911 : Blo 818347 821911 := bstep (se 1 (by rfl) ⟨616433, by rfl⟩ : syracuseStep 821911 = 1232867) B1232867
theorem B821931 : Blo 818347 821931 := bstep (se 1 (by rfl) ⟨616448, by rfl⟩ : syracuseStep 821931 = 1232897) B1232897
theorem B821943 : Blo 818347 821943 := bstep (se 1 (by rfl) ⟨616457, by rfl⟩ : syracuseStep 821943 = 1232915) B1232915
theorem B821963 : Blo 818347 821963 := bstep (se 1 (by rfl) ⟨616472, by rfl⟩ : syracuseStep 821963 = 1232945) B1232945
theorem B821975 : Blo 818347 821975 := bstep (se 1 (by rfl) ⟨616481, by rfl⟩ : syracuseStep 821975 = 1232963) B1232963
theorem B821995 : Blo 818347 821995 := bstep (se 1 (by rfl) ⟨616496, by rfl⟩ : syracuseStep 821995 = 1232993) B1232993
theorem B822007 : Blo 818347 822007 := bstep (se 1 (by rfl) ⟨616505, by rfl⟩ : syracuseStep 822007 = 1233011) B1233011
theorem B822027 : Blo 818347 822027 := bstep (se 1 (by rfl) ⟨616520, by rfl⟩ : syracuseStep 822027 = 1233041) B1233041
theorem B822039 : Blo 818347 822039 := bstep (se 1 (by rfl) ⟨616529, by rfl⟩ : syracuseStep 822039 = 1233059) B1233059
theorem B822059 : Blo 818347 822059 := bstep (se 1 (by rfl) ⟨616544, by rfl⟩ : syracuseStep 822059 = 1233089) B1233089
theorem B822071 : Blo 818347 822071 := bstep (se 1 (by rfl) ⟨616553, by rfl⟩ : syracuseStep 822071 = 1233107) B1233107
theorem B822091 : Blo 818347 822091 := bstep (se 1 (by rfl) ⟨616568, by rfl⟩ : syracuseStep 822091 = 1233137) B1233137
theorem B822103 : Blo 818347 822103 := bstep (se 1 (by rfl) ⟨616577, by rfl⟩ : syracuseStep 822103 = 1233155) B1233155
theorem B822123 : Blo 818347 822123 := bstep (se 1 (by rfl) ⟨616592, by rfl⟩ : syracuseStep 822123 = 1233185) B1233185
theorem B822135 : Blo 818347 822135 := bstep (se 1 (by rfl) ⟨616601, by rfl⟩ : syracuseStep 822135 = 1233203) B1233203
theorem B1248139 : Blo 818347 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B822155 : Blo 818347 822155 := bstep (se 1 (by rfl) ⟨616616, by rfl⟩ : syracuseStep 822155 = 1233233) B1233233
theorem B1313687 : Blo 818347 1313687 := bstep (se 1 (by rfl) ⟨985265, by rfl⟩ : syracuseStep 1313687 = 1970531) B1970531
theorem B822167 : Blo 818347 822167 := bstep (se 1 (by rfl) ⟨616625, by rfl⟩ : syracuseStep 822167 = 1233251) B1233251
theorem B822187 : Blo 818347 822187 := bstep (se 1 (by rfl) ⟨616640, by rfl⟩ : syracuseStep 822187 = 1233281) B1233281
theorem B822199 : Blo 818347 822199 := bstep (se 1 (by rfl) ⟨616649, by rfl⟩ : syracuseStep 822199 = 1233299) B1233299
theorem B822219 : Blo 818347 822219 := bstep (se 1 (by rfl) ⟨616664, by rfl⟩ : syracuseStep 822219 = 1233329) B1233329
theorem B822231 : Blo 818347 822231 := bstep (se 1 (by rfl) ⟨616673, by rfl⟩ : syracuseStep 822231 = 1233347) B1233347
theorem B5049305 : Blo 818347 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B822251 : Blo 818347 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B822263 : Blo 818347 822263 := bstep (se 1 (by rfl) ⟨616697, by rfl⟩ : syracuseStep 822263 = 1233395) B1233395
theorem B822283 : Blo 818347 822283 := bstep (se 1 (by rfl) ⟨616712, by rfl⟩ : syracuseStep 822283 = 1233425) B1233425
theorem B1313815 : Blo 818347 1313815 := bstep (se 1 (by rfl) ⟨985361, by rfl⟩ : syracuseStep 1313815 = 1970723) B1970723
theorem B822295 : Blo 818347 822295 := bstep (se 1 (by rfl) ⟨616721, by rfl⟩ : syracuseStep 822295 = 1233443) B1233443
theorem B822315 : Blo 818347 822315 := bstep (se 1 (by rfl) ⟨616736, by rfl⟩ : syracuseStep 822315 = 1233473) B1233473
theorem B822327 : Blo 818347 822327 := bstep (se 1 (by rfl) ⟨616745, by rfl⟩ : syracuseStep 822327 = 1233491) B1233491
theorem B822347 : Blo 818347 822347 := bstep (se 1 (by rfl) ⟨616760, by rfl⟩ : syracuseStep 822347 = 1233521) B1233521
theorem B920695 : Blo 818347 920695 := bstep (se 1 (by rfl) ⟨690521, by rfl⟩ : syracuseStep 920695 = 1381043) B1381043
theorem B5901443 : Blo 818347 5901443 := bstep (se 1 (by rfl) ⟨4426082, by rfl⟩ : syracuseStep 5901443 = 8852165) B8852165
theorem B3378307 : Blo 818347 3378307 := bstep (se 1 (by rfl) ⟨2533730, by rfl⟩ : syracuseStep 3378307 = 5067461) B5067461
theorem B2952395 : Blo 818347 2952395 := bstep (se 1 (by rfl) ⟨2214296, by rfl⟩ : syracuseStep 2952395 = 4428593) B4428593
theorem B920875 : Blo 818347 920875 := bstep (se 1 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 920875 = 1381313) B1381313
theorem B3116339 : Blo 818347 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B3116353 : Blo 818347 3116353 := bstep (se 2 (by rfl) ⟨1168632, by rfl⟩ : syracuseStep 3116353 = 2337265) B2337265
theorem B11832641 : Blo 818347 11832641 := bstep (se 2 (by rfl) ⟨4437240, by rfl⟩ : syracuseStep 11832641 = 8874481) B8874481
theorem B920983 : Blo 818347 920983 := bstep (se 1 (by rfl) ⟨690737, by rfl⟩ : syracuseStep 920983 = 1381475) B1381475
theorem B3739031 : Blo 818347 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B3509725 : Blo 818347 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B921163 : Blo 818347 921163 := bstep (se 1 (by rfl) ⟨690872, by rfl⟩ : syracuseStep 921163 = 1381745) B1381745
theorem B1969753 : Blo 818347 1969753 := bstep (se 2 (by rfl) ⟨738657, by rfl⟩ : syracuseStep 1969753 = 1477315) B1477315
theorem B921271 : Blo 818347 921271 := bstep (se 1 (by rfl) ⟨690953, by rfl⟩ : syracuseStep 921271 = 1381907) B1381907
theorem B1478359 : Blo 818347 1478359 := bstep (se 1 (by rfl) ⟨1108769, by rfl⟩ : syracuseStep 1478359 = 2217539) B2217539
theorem B3510067 : Blo 818347 3510067 := bstep (se 1 (by rfl) ⟨2632550, by rfl⟩ : syracuseStep 3510067 = 5265101) B5265101
theorem B1314635 : Blo 818347 1314635 := bstep (se 1 (by rfl) ⟨985976, by rfl⟩ : syracuseStep 1314635 = 1971953) B1971953
theorem B921451 : Blo 818347 921451 := bstep (se 1 (by rfl) ⟨691088, by rfl⟩ : syracuseStep 921451 = 1382177) B1382177
theorem B921559 : Blo 818347 921559 := bstep (se 1 (by rfl) ⟨691169, by rfl⟩ : syracuseStep 921559 = 1382339) B1382339
theorem B6230033 : Blo 818347 6230033 := bstep (se 2 (by rfl) ⟨2336262, by rfl⟩ : syracuseStep 6230033 = 4672525) B4672525
theorem B921739 : Blo 818347 921739 := bstep (se 1 (by rfl) ⟨691304, by rfl⟩ : syracuseStep 921739 = 1382609) B1382609
theorem B2953361 : Blo 818347 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B1970369 : Blo 818347 1970369 := bstep (se 2 (by rfl) ⟨738888, by rfl⟩ : syracuseStep 1970369 = 1477777) B1477777
theorem B1872065 : Blo 818347 1872065 := bstep (se 2 (by rfl) ⟨702024, by rfl⟩ : syracuseStep 1872065 = 1404049) B1404049
theorem B1052887 : Blo 818347 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B921847 : Blo 818347 921847 := bstep (se 1 (by rfl) ⟨691385, by rfl⟩ : syracuseStep 921847 = 1382771) B1382771
theorem B19960181 : Blo 818347 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B922027 : Blo 818347 922027 := bstep (se 1 (by rfl) ⟨691520, by rfl⟩ : syracuseStep 922027 = 1383041) B1383041
theorem B922135 : Blo 818347 922135 := bstep (se 1 (by rfl) ⟨691601, by rfl⟩ : syracuseStep 922135 = 1383203) B1383203
theorem B3936833 : Blo 818347 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B922315 : Blo 818347 922315 := bstep (se 1 (by rfl) ⟨691736, by rfl⟩ : syracuseStep 922315 = 1383473) B1383473
theorem B922423 : Blo 818347 922423 := bstep (se 1 (by rfl) ⟨691817, by rfl⟩ : syracuseStep 922423 = 1383635) B1383635
theorem B4002625 : Blo 818347 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B1381259 : Blo 818347 1381259 := bstep (se 1 (by rfl) ⟨1035944, by rfl⟩ : syracuseStep 1381259 = 2071889) B2071889
theorem B1971137 : Blo 818347 1971137 := bstep (se 2 (by rfl) ⟨739176, by rfl⟩ : syracuseStep 1971137 = 1478353) B1478353
theorem B922603 : Blo 818347 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B1381387 : Blo 818347 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B922711 : Blo 818347 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B1381529 : Blo 818347 1381529 := bstep (se 2 (by rfl) ⟨518073, by rfl⟩ : syracuseStep 1381529 = 1036147) B1036147
theorem B3118283 : Blo 818347 3118283 := bstep (se 1 (by rfl) ⟨2338712, by rfl⟩ : syracuseStep 3118283 = 4677425) B4677425
theorem B3118297 : Blo 818347 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B922891 : Blo 818347 922891 := bstep (se 1 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 922891 = 1384337) B1384337
theorem B1381657 : Blo 818347 1381657 := bstep (se 2 (by rfl) ⟨518121, by rfl⟩ : syracuseStep 1381657 = 1036243) B1036243
theorem B9344321 : Blo 818347 9344321 := bstep (se 2 (by rfl) ⟨3504120, by rfl⟩ : syracuseStep 9344321 = 7008241) B7008241
theorem B922999 : Blo 818347 922999 := bstep (se 1 (by rfl) ⟨692249, by rfl⟩ : syracuseStep 922999 = 1384499) B1384499
theorem B13276685 : Blo 818347 13276685 := bstep (se 3 (by rfl) ⟨2489378, by rfl⟩ : syracuseStep 13276685 = 4978757) B4978757
theorem B923179 : Blo 818347 923179 := bstep (se 1 (by rfl) ⟨692384, by rfl⟩ : syracuseStep 923179 = 1384769) B1384769
theorem B2332253 : Blo 818347 2332253 := bstep (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) B874595
theorem B923287 : Blo 818347 923287 := bstep (se 1 (by rfl) ⟨692465, by rfl⟩ : syracuseStep 923287 = 1384931) B1384931
theorem B923467 : Blo 818347 923467 := bstep (se 1 (by rfl) ⟨692600, by rfl⟩ : syracuseStep 923467 = 1385201) B1385201
theorem B1382231 : Blo 818347 1382231 := bstep (se 1 (by rfl) ⟨1036673, by rfl⟩ : syracuseStep 1382231 = 2073347) B2073347
theorem B3938179 : Blo 818347 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B923575 : Blo 818347 923575 := bstep (se 1 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 923575 = 1385363) B1385363
theorem B1382359 : Blo 818347 1382359 := bstep (se 1 (by rfl) ⟨1036769, by rfl⟩ : syracuseStep 1382359 = 2073539) B2073539
theorem B3151961 : Blo 818347 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B923755 : Blo 818347 923755 := bstep (se 1 (by rfl) ⟨692816, by rfl⟩ : syracuseStep 923755 = 1385633) B1385633
theorem B1841291 : Blo 818347 1841291 := bstep (se 1 (by rfl) ⟨1380968, by rfl⟩ : syracuseStep 1841291 = 2761937) B2761937
theorem B3119255 : Blo 818347 3119255 := bstep (se 1 (by rfl) ⟨2339441, by rfl⟩ : syracuseStep 3119255 = 4678883) B4678883
theorem B1841345 : Blo 818347 1841345 := bstep (se 2 (by rfl) ⟨690504, by rfl⟩ : syracuseStep 1841345 = 1381009) B1381009
theorem B923863 : Blo 818347 923863 := bstep (se 1 (by rfl) ⟨692897, by rfl⟩ : syracuseStep 923863 = 1385795) B1385795
theorem B1579225 : Blo 818347 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B2103617 : Blo 818347 2103617 := bstep (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) B1577713
theorem B924043 : Blo 818347 924043 := bstep (se 1 (by rfl) ⟨693032, by rfl⟩ : syracuseStep 924043 = 1386065) B1386065
theorem B1841561 : Blo 818347 1841561 := bstep (se 2 (by rfl) ⟨690585, by rfl⟩ : syracuseStep 1841561 = 1381171) B1381171
theorem B1841651 : Blo 818347 1841651 := bstep (se 1 (by rfl) ⟨1381238, by rfl⟩ : syracuseStep 1841651 = 2762477) B2762477
theorem B924151 : Blo 818347 924151 := bstep (se 1 (by rfl) ⟨693113, by rfl⟩ : syracuseStep 924151 = 1386227) B1386227
theorem B1841687 : Blo 818347 1841687 := bstep (se 1 (by rfl) ⟨1381265, by rfl⟩ : syracuseStep 1841687 = 2762531) B2762531
theorem B1382987 : Blo 818347 1382987 := bstep (se 1 (by rfl) ⟨1037240, by rfl⟩ : syracuseStep 1382987 = 2074481) B2074481
theorem B924331 : Blo 818347 924331 := bstep (se 1 (by rfl) ⟨693248, by rfl⟩ : syracuseStep 924331 = 1386497) B1386497
theorem B1841867 : Blo 818347 1841867 := bstep (se 1 (by rfl) ⟨1381400, by rfl⟩ : syracuseStep 1841867 = 2762801) B2762801
theorem B1383115 : Blo 818347 1383115 := bstep (se 1 (by rfl) ⟨1037336, by rfl⟩ : syracuseStep 1383115 = 2074673) B2074673
theorem B1481431 : Blo 818347 1481431 := bstep (se 1 (by rfl) ⟨1111073, by rfl⟩ : syracuseStep 1481431 = 2222147) B2222147
theorem B1841921 : Blo 818347 1841921 := bstep (se 2 (by rfl) ⟨690720, by rfl⟩ : syracuseStep 1841921 = 1381441) B1381441
theorem B924439 : Blo 818347 924439 := bstep (se 1 (by rfl) ⟨693329, by rfl⟩ : syracuseStep 924439 = 1386659) B1386659
theorem B2104129 : Blo 818347 2104129 := bstep (se 2 (by rfl) ⟨789048, by rfl⟩ : syracuseStep 2104129 = 1578097) B1578097
theorem B1383257 : Blo 818347 1383257 := bstep (se 2 (by rfl) ⟨518721, by rfl⟩ : syracuseStep 1383257 = 1037443) B1037443
theorem B924619 : Blo 818347 924619 := bstep (se 1 (by rfl) ⟨693464, by rfl⟩ : syracuseStep 924619 = 1386929) B1386929
theorem B1842137 : Blo 818347 1842137 := bstep (se 2 (by rfl) ⟨690801, by rfl⟩ : syracuseStep 1842137 = 1381603) B1381603
theorem B1383385 : Blo 818347 1383385 := bstep (se 2 (by rfl) ⟨518769, by rfl⟩ : syracuseStep 1383385 = 1037539) B1037539
theorem B1842227 : Blo 818347 1842227 := bstep (se 1 (by rfl) ⟨1381670, by rfl⟩ : syracuseStep 1842227 = 2763341) B2763341
theorem B924727 : Blo 818347 924727 := bstep (se 1 (by rfl) ⟨693545, by rfl⟩ : syracuseStep 924727 = 1387091) B1387091
theorem B1842263 : Blo 818347 1842263 := bstep (se 1 (by rfl) ⟨1381697, by rfl⟩ : syracuseStep 1842263 = 2763395) B2763395
theorem B924907 : Blo 818347 924907 := bstep (se 1 (by rfl) ⟨693680, by rfl⟩ : syracuseStep 924907 = 1387361) B1387361
theorem B1842443 : Blo 818347 1842443 := bstep (se 1 (by rfl) ⟨1381832, by rfl⟩ : syracuseStep 1842443 = 2763665) B2763665
theorem B1842497 : Blo 818347 1842497 := bstep (se 2 (by rfl) ⟨690936, by rfl⟩ : syracuseStep 1842497 = 1381873) B1381873
theorem B925015 : Blo 818347 925015 := bstep (se 1 (by rfl) ⟨693761, by rfl⟩ : syracuseStep 925015 = 1387523) B1387523
theorem B3120515 : Blo 818347 3120515 := bstep (se 1 (by rfl) ⟨2340386, by rfl⟩ : syracuseStep 3120515 = 4680773) B4680773
theorem B1383959 : Blo 818347 1383959 := bstep (se 1 (by rfl) ⟨1037969, by rfl⟩ : syracuseStep 1383959 = 2075939) B2075939
theorem B1842713 : Blo 818347 1842713 := bstep (se 2 (by rfl) ⟨691017, by rfl⟩ : syracuseStep 1842713 = 1382035) B1382035
theorem B1842803 : Blo 818347 1842803 := bstep (se 1 (by rfl) ⟨1382102, by rfl⟩ : syracuseStep 1842803 = 2764205) B2764205
theorem B1842839 : Blo 818347 1842839 := bstep (se 1 (by rfl) ⟨1382129, by rfl⟩ : syracuseStep 1842839 = 2764259) B2764259
theorem B1384087 : Blo 818347 1384087 := bstep (se 1 (by rfl) ⟨1038065, by rfl⟩ : syracuseStep 1384087 = 2076131) B2076131
theorem B2072243 : Blo 818347 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B2956979 : Blo 818347 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B6233921 : Blo 818347 6233921 := bstep (se 2 (by rfl) ⟨2337720, by rfl⟩ : syracuseStep 6233921 = 4675441) B4675441
theorem B2531137 : Blo 818347 2531137 := bstep (se 2 (by rfl) ⟨949176, by rfl⟩ : syracuseStep 2531137 = 1898353) B1898353
theorem B1843019 : Blo 818347 1843019 := bstep (se 1 (by rfl) ⟨1382264, by rfl⟩ : syracuseStep 1843019 = 2764529) B2764529
theorem B1843073 : Blo 818347 1843073 := bstep (se 2 (by rfl) ⟨691152, by rfl⟩ : syracuseStep 1843073 = 1382305) B1382305
theorem B2072537 : Blo 818347 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B2629655 : Blo 818347 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B3940427 : Blo 818347 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1843289 : Blo 818347 1843289 := bstep (se 2 (by rfl) ⟨691233, by rfl⟩ : syracuseStep 1843289 = 1382467) B1382467
theorem B1843379 : Blo 818347 1843379 := bstep (se 1 (by rfl) ⟨1382534, by rfl⟩ : syracuseStep 1843379 = 2765069) B2765069
theorem B2367667 : Blo 818347 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B1843415 : Blo 818347 1843415 := bstep (se 1 (by rfl) ⟨1382561, by rfl⟩ : syracuseStep 1843415 = 2765123) B2765123
theorem B1384715 : Blo 818347 1384715 := bstep (se 1 (by rfl) ⟨1038536, by rfl⟩ : syracuseStep 1384715 = 2077073) B2077073
theorem B1843595 : Blo 818347 1843595 := bstep (se 1 (by rfl) ⟨1382696, by rfl⟩ : syracuseStep 1843595 = 2765393) B2765393
theorem B1384843 : Blo 818347 1384843 := bstep (se 1 (by rfl) ⟨1038632, by rfl⟩ : syracuseStep 1384843 = 2077265) B2077265
theorem B1843649 : Blo 818347 1843649 := bstep (se 2 (by rfl) ⟨691368, by rfl⟩ : syracuseStep 1843649 = 1382737) B1382737
theorem B2335169 : Blo 818347 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1974721 : Blo 818347 1974721 := bstep (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) B1481041
theorem B2335193 : Blo 818347 2335193 := bstep (se 2 (by rfl) ⟨875697, by rfl⟩ : syracuseStep 2335193 = 1751395) B1751395
theorem B1384985 : Blo 818347 1384985 := bstep (se 2 (by rfl) ⟨519369, by rfl⟩ : syracuseStep 1384985 = 1038739) B1038739
theorem B1843865 : Blo 818347 1843865 := bstep (se 2 (by rfl) ⟨691449, by rfl⟩ : syracuseStep 1843865 = 1382899) B1382899
theorem B1385113 : Blo 818347 1385113 := bstep (se 2 (by rfl) ⟨519417, by rfl⟩ : syracuseStep 1385113 = 1038835) B1038835
theorem B17703629 : Blo 818347 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B11805425 : Blo 818347 11805425 := bstep (se 2 (by rfl) ⟨4427034, by rfl⟩ : syracuseStep 11805425 = 8854069) B8854069
theorem B1843955 : Blo 818347 1843955 := bstep (se 1 (by rfl) ⟨1382966, by rfl⟩ : syracuseStep 1843955 = 2765933) B2765933
theorem B1843991 : Blo 818347 1843991 := bstep (se 1 (by rfl) ⟨1382993, by rfl⟩ : syracuseStep 1843991 = 2765987) B2765987
theorem B2630551 : Blo 818347 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B1844171 : Blo 818347 1844171 := bstep (se 1 (by rfl) ⟨1383128, by rfl⟩ : syracuseStep 1844171 = 2766257) B2766257
theorem B1844225 : Blo 818347 1844225 := bstep (se 2 (by rfl) ⟨691584, by rfl⟩ : syracuseStep 1844225 = 1383169) B1383169
theorem B15770699 : Blo 818347 15770699 := bstep (se 1 (by rfl) ⟨11828024, by rfl⟩ : syracuseStep 15770699 = 23656049) B23656049
theorem B1385687 : Blo 818347 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B1844441 : Blo 818347 1844441 := bstep (se 2 (by rfl) ⟨691665, by rfl⟩ : syracuseStep 1844441 = 1383331) B1383331
theorem B1844531 : Blo 818347 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B4662593 : Blo 818347 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B1844567 : Blo 818347 1844567 := bstep (se 1 (by rfl) ⟨1383425, by rfl⟩ : syracuseStep 1844567 = 2766851) B2766851
theorem B1385815 : Blo 818347 1385815 := bstep (se 1 (by rfl) ⟨1039361, by rfl⟩ : syracuseStep 1385815 = 2078723) B2078723
theorem B1844747 : Blo 818347 1844747 := bstep (se 1 (by rfl) ⟨1383560, by rfl⟩ : syracuseStep 1844747 = 2767121) B2767121
theorem B1844801 : Blo 818347 1844801 := bstep (se 2 (by rfl) ⟨691800, by rfl⟩ : syracuseStep 1844801 = 1383601) B1383601
theorem B3745345 : Blo 818347 3745345 := bstep (se 2 (by rfl) ⟨1404504, by rfl⟩ : syracuseStep 3745345 = 2809009) B2809009
theorem B2762315 : Blo 818347 2762315 := bstep (se 1 (by rfl) ⟨2071736, by rfl⟩ : syracuseStep 2762315 = 4143473) B4143473
theorem B2074187 : Blo 818347 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B2336435 : Blo 818347 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B2631371 : Blo 818347 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B6235865 : Blo 818347 6235865 := bstep (se 2 (by rfl) ⟨2338449, by rfl⟩ : syracuseStep 6235865 = 4676899) B4676899
theorem B1845017 : Blo 818347 1845017 := bstep (se 2 (by rfl) ⟨691881, by rfl⟩ : syracuseStep 1845017 = 1383763) B1383763
theorem B2762585 : Blo 818347 2762585 := bstep (se 2 (by rfl) ⟨1035969, by rfl⟩ : syracuseStep 2762585 = 2071939) B2071939
theorem B1845107 : Blo 818347 1845107 := bstep (se 1 (by rfl) ⟨1383830, by rfl⟩ : syracuseStep 1845107 = 2767661) B2767661
theorem B1845143 : Blo 818347 1845143 := bstep (se 1 (by rfl) ⟨1383857, by rfl⟩ : syracuseStep 1845143 = 2767715) B2767715
theorem B2369431 : Blo 818347 2369431 := bstep (se 1 (by rfl) ⟨1777073, by rfl⟩ : syracuseStep 2369431 = 3554147) B3554147
theorem B1386443 : Blo 818347 1386443 := bstep (se 1 (by rfl) ⟨1039832, by rfl⟩ : syracuseStep 1386443 = 2079665) B2079665
theorem B1845323 : Blo 818347 1845323 := bstep (se 1 (by rfl) ⟨1383992, by rfl⟩ : syracuseStep 1845323 = 2767985) B2767985
theorem B1386571 : Blo 818347 1386571 := bstep (se 1 (by rfl) ⟨1039928, by rfl⟩ : syracuseStep 1386571 = 2079857) B2079857
theorem B1845377 : Blo 818347 1845377 := bstep (se 2 (by rfl) ⟨692016, by rfl⟩ : syracuseStep 1845377 = 1384033) B1384033
theorem B1386713 : Blo 818347 1386713 := bstep (se 2 (by rfl) ⟨520017, by rfl⟩ : syracuseStep 1386713 = 1040035) B1040035
theorem B3320081 : Blo 818347 3320081 := bstep (se 2 (by rfl) ⟨1245030, by rfl⟩ : syracuseStep 3320081 = 2490061) B2490061
theorem B1845593 : Blo 818347 1845593 := bstep (se 2 (by rfl) ⟨692097, by rfl⟩ : syracuseStep 1845593 = 1384195) B1384195
theorem B1386841 : Blo 818347 1386841 := bstep (se 2 (by rfl) ⟨520065, by rfl⟩ : syracuseStep 1386841 = 1040131) B1040131
theorem B1845683 : Blo 818347 1845683 := bstep (se 1 (by rfl) ⟨1384262, by rfl⟩ : syracuseStep 1845683 = 2768525) B2768525
theorem B2632115 : Blo 818347 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1845719 : Blo 818347 1845719 := bstep (se 1 (by rfl) ⟨1384289, by rfl⟩ : syracuseStep 1845719 = 2768579) B2768579
theorem B2763287 : Blo 818347 2763287 := bstep (se 1 (by rfl) ⟨2072465, by rfl⟩ : syracuseStep 2763287 = 4144931) B4144931
theorem B2075159 : Blo 818347 2075159 := bstep (se 1 (by rfl) ⟨1556369, by rfl⟩ : syracuseStep 2075159 = 3112739) B3112739
theorem B1845899 : Blo 818347 1845899 := bstep (se 1 (by rfl) ⟨1384424, by rfl⟩ : syracuseStep 1845899 = 2768849) B2768849
theorem B1845953 : Blo 818347 1845953 := bstep (se 2 (by rfl) ⟨692232, by rfl⟩ : syracuseStep 1845953 = 1384465) B1384465
theorem B1387415 : Blo 818347 1387415 := bstep (se 1 (by rfl) ⟨1040561, by rfl⟩ : syracuseStep 1387415 = 2081123) B2081123
theorem B1846169 : Blo 818347 1846169 := bstep (se 2 (by rfl) ⟨692313, by rfl⟩ : syracuseStep 1846169 = 1384627) B1384627
theorem B3550169 : Blo 818347 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B1846259 : Blo 818347 1846259 := bstep (se 1 (by rfl) ⟨1384694, by rfl⟩ : syracuseStep 1846259 = 2769389) B2769389
theorem B1846295 : Blo 818347 1846295 := bstep (se 1 (by rfl) ⟨1384721, by rfl⟩ : syracuseStep 1846295 = 2769443) B2769443
theorem B1387543 : Blo 818347 1387543 := bstep (se 1 (by rfl) ⟨1040657, by rfl⟩ : syracuseStep 1387543 = 2081315) B2081315
theorem B2763827 : Blo 818347 2763827 := bstep (se 1 (by rfl) ⟨2072870, by rfl⟩ : syracuseStep 2763827 = 4145741) B4145741
theorem B830539 : Blo 818347 830539 := bstep (se 1 (by rfl) ⟨622904, by rfl⟩ : syracuseStep 830539 = 1245809) B1245809
theorem B9743435 : Blo 818347 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B2075827 : Blo 818347 2075827 := bstep (se 1 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 2075827 = 3113741) B3113741
theorem B1846475 : Blo 818347 1846475 := bstep (se 1 (by rfl) ⟨1384856, by rfl⟩ : syracuseStep 1846475 = 2769713) B2769713
theorem B1846529 : Blo 818347 1846529 := bstep (se 2 (by rfl) ⟨692448, by rfl⟩ : syracuseStep 1846529 = 1384897) B1384897
theorem B2764097 : Blo 818347 2764097 := bstep (se 2 (by rfl) ⟨1036536, by rfl⟩ : syracuseStep 2764097 = 2073073) B2073073
theorem B2075969 : Blo 818347 2075969 := bstep (se 2 (by rfl) ⟨778488, by rfl⟩ : syracuseStep 2075969 = 1556977) B1556977
theorem B1846745 : Blo 818347 1846745 := bstep (se 2 (by rfl) ⟨692529, by rfl⟩ : syracuseStep 1846745 = 1385059) B1385059
theorem B3943981 : Blo 818347 3943981 := bstep (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) B1478993
theorem B1846835 : Blo 818347 1846835 := bstep (se 1 (by rfl) ⟨1385126, by rfl⟩ : syracuseStep 1846835 = 2770253) B2770253
theorem B1748567 : Blo 818347 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B1846871 : Blo 818347 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B4992691 : Blo 818347 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B1847051 : Blo 818347 1847051 := bstep (se 1 (by rfl) ⟨1385288, by rfl⟩ : syracuseStep 1847051 = 2770577) B2770577
theorem B3321623 : Blo 818347 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B1847105 : Blo 818347 1847105 := bstep (se 2 (by rfl) ⟨692664, by rfl⟩ : syracuseStep 1847105 = 1385329) B1385329
theorem B2764637 : Blo 818347 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B3321803 : Blo 818347 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B11972569 : Blo 818347 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B1847321 : Blo 818347 1847321 := bstep (se 2 (by rfl) ⟨692745, by rfl⟩ : syracuseStep 1847321 = 1385491) B1385491
theorem B3321931 : Blo 818347 3321931 := bstep (se 1 (by rfl) ⟨2491448, by rfl⟩ : syracuseStep 3321931 = 4982897) B4982897
theorem B1847411 : Blo 818347 1847411 := bstep (se 1 (by rfl) ⟨1385558, by rfl⟩ : syracuseStep 1847411 = 2771117) B2771117
theorem B8859779 : Blo 818347 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B1847447 : Blo 818347 1847447 := bstep (se 1 (by rfl) ⟨1385585, by rfl⟩ : syracuseStep 1847447 = 2771171) B2771171
theorem B1847627 : Blo 818347 1847627 := bstep (se 1 (by rfl) ⟨1385720, by rfl⟩ : syracuseStep 1847627 = 2771441) B2771441
theorem B1847681 : Blo 818347 1847681 := bstep (se 2 (by rfl) ⟨692880, by rfl⟩ : syracuseStep 1847681 = 1385761) B1385761
theorem B2339293 : Blo 818347 2339293 := bstep (se 3 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 2339293 = 877235) B877235
theorem B2339351 : Blo 818347 2339351 := bstep (se 1 (by rfl) ⟨1754513, by rfl⟩ : syracuseStep 2339351 = 3509027) B3509027
theorem B2077235 : Blo 818347 2077235 := bstep (se 1 (by rfl) ⟨1557926, by rfl⟩ : syracuseStep 2077235 = 3115853) B3115853
theorem B1749593 : Blo 818347 1749593 := bstep (se 2 (by rfl) ⟨656097, by rfl⟩ : syracuseStep 1749593 = 1312195) B1312195
theorem B1847897 : Blo 818347 1847897 := bstep (se 2 (by rfl) ⟨692961, by rfl⟩ : syracuseStep 1847897 = 1385923) B1385923
theorem B1847987 : Blo 818347 1847987 := bstep (se 1 (by rfl) ⟨1385990, by rfl⟩ : syracuseStep 1847987 = 2771981) B2771981
theorem B1848023 : Blo 818347 1848023 := bstep (se 1 (by rfl) ⟨1386017, by rfl⟩ : syracuseStep 1848023 = 2772035) B2772035
theorem B2962241 : Blo 818347 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B5256029 : Blo 818347 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B1848203 : Blo 818347 1848203 := bstep (se 1 (by rfl) ⟨1386152, by rfl⟩ : syracuseStep 1848203 = 2772305) B2772305
theorem B1848257 : Blo 818347 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B2962369 : Blo 818347 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B2765771 : Blo 818347 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B6239267 : Blo 818347 6239267 := bstep (se 1 (by rfl) ⟨4679450, by rfl⟩ : syracuseStep 6239267 = 9358901) B9358901
theorem B2077771 : Blo 818347 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B1848473 : Blo 818347 1848473 := bstep (se 2 (by rfl) ⟨693177, by rfl⟩ : syracuseStep 1848473 = 1386355) B1386355
theorem B10532045 : Blo 818347 10532045 := bstep (se 3 (by rfl) ⟨1974758, by rfl⟩ : syracuseStep 10532045 = 3949517) B3949517
theorem B2766041 : Blo 818347 2766041 := bstep (se 2 (by rfl) ⟨1037265, by rfl⟩ : syracuseStep 2766041 = 2074531) B2074531
theorem B2077913 : Blo 818347 2077913 := bstep (se 2 (by rfl) ⟨779217, by rfl⟩ : syracuseStep 2077913 = 1558435) B1558435
theorem B1553651 : Blo 818347 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1848563 : Blo 818347 1848563 := bstep (se 1 (by rfl) ⟨1386422, by rfl⟩ : syracuseStep 1848563 = 2772845) B2772845
theorem B1848599 : Blo 818347 1848599 := bstep (se 1 (by rfl) ⟨1386449, by rfl⟩ : syracuseStep 1848599 = 2772899) B2772899
theorem B832907 : Blo 818347 832907 := bstep (se 1 (by rfl) ⟨624680, by rfl⟩ : syracuseStep 832907 = 1249361) B1249361
theorem B1848779 : Blo 818347 1848779 := bstep (se 1 (by rfl) ⟨1386584, by rfl⟩ : syracuseStep 1848779 = 2773169) B2773169
theorem B1553879 : Blo 818347 1553879 := bstep (se 1 (by rfl) ⟨1165409, by rfl⟩ : syracuseStep 1553879 = 2330819) B2330819
theorem B1848833 : Blo 818347 1848833 := bstep (se 2 (by rfl) ⟨693312, by rfl⟩ : syracuseStep 1848833 = 1386625) B1386625
theorem B1750643 : Blo 818347 1750643 := bstep (se 1 (by rfl) ⟨1312982, by rfl⟩ : syracuseStep 1750643 = 2625965) B2625965
theorem B1554137 : Blo 818347 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B5912281 : Blo 818347 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B1849049 : Blo 818347 1849049 := bstep (se 2 (by rfl) ⟨693393, by rfl⟩ : syracuseStep 1849049 = 1386787) B1386787
theorem B2340569 : Blo 818347 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B1849139 : Blo 818347 1849139 := bstep (se 1 (by rfl) ⟨1386854, by rfl⟩ : syracuseStep 1849139 = 2773709) B2773709
theorem B2340683 : Blo 818347 2340683 := bstep (se 1 (by rfl) ⟨1755512, by rfl⟩ : syracuseStep 2340683 = 3511025) B3511025
theorem B1849175 : Blo 818347 1849175 := bstep (se 1 (by rfl) ⟨1386881, by rfl⟩ : syracuseStep 1849175 = 2773763) B2773763
theorem B2766743 : Blo 818347 2766743 := bstep (se 1 (by rfl) ⟨2075057, by rfl⟩ : syracuseStep 2766743 = 4150115) B4150115
theorem B1849355 : Blo 818347 1849355 := bstep (se 1 (by rfl) ⟨1387016, by rfl⟩ : syracuseStep 1849355 = 2774033) B2774033
theorem B2078743 : Blo 818347 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B4143149 : Blo 818347 4143149 := bstep (se 3 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 4143149 = 1553681) B1553681
theorem B1849409 : Blo 818347 1849409 := bstep (se 2 (by rfl) ⟨693528, by rfl⟩ : syracuseStep 1849409 = 1387057) B1387057
theorem B1554547 : Blo 818347 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B6666371 : Blo 818347 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B1751233 : Blo 818347 1751233 := bstep (se 2 (by rfl) ⟨656712, by rfl⟩ : syracuseStep 1751233 = 1313425) B1313425
theorem B1849625 : Blo 818347 1849625 := bstep (se 2 (by rfl) ⟨693609, by rfl⟩ : syracuseStep 1849625 = 1387219) B1387219
theorem B1849715 : Blo 818347 1849715 := bstep (se 1 (by rfl) ⟨1387286, by rfl⟩ : syracuseStep 1849715 = 2774573) B2774573
theorem B1849751 : Blo 818347 1849751 := bstep (se 1 (by rfl) ⟨1387313, by rfl⟩ : syracuseStep 1849751 = 2774627) B2774627
theorem B2767283 : Blo 818347 2767283 := bstep (se 1 (by rfl) ⟨2075462, by rfl⟩ : syracuseStep 2767283 = 4150925) B4150925
theorem B2079179 : Blo 818347 2079179 := bstep (se 1 (by rfl) ⟨1559384, by rfl⟩ : syracuseStep 2079179 = 3118769) B3118769
theorem B4667969 : Blo 818347 4667969 := bstep (se 2 (by rfl) ⟨1750488, by rfl⟩ : syracuseStep 4667969 = 3500977) B3500977
theorem B1849931 : Blo 818347 1849931 := bstep (se 1 (by rfl) ⟨1387448, by rfl⟩ : syracuseStep 1849931 = 2774897) B2774897
theorem B1555033 : Blo 818347 1555033 := bstep (se 2 (by rfl) ⟨583137, by rfl⟩ : syracuseStep 1555033 = 1166275) B1166275
theorem B1849985 : Blo 818347 1849985 := bstep (se 2 (by rfl) ⟨693744, by rfl⟩ : syracuseStep 1849985 = 1387489) B1387489
theorem B3160721 : Blo 818347 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B2767553 : Blo 818347 2767553 := bstep (se 2 (by rfl) ⟨1037832, by rfl⟩ : syracuseStep 2767553 = 2075665) B2075665
theorem B1227545 : Blo 818347 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B2079553 : Blo 818347 2079553 := bstep (se 2 (by rfl) ⟨779832, by rfl⟩ : syracuseStep 2079553 = 1559665) B1559665
theorem B1850201 : Blo 818347 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B1227659 : Blo 818347 1227659 := bstep (se 1 (by rfl) ⟨920744, by rfl⟩ : syracuseStep 1227659 = 1841489) B1841489
theorem B1227671 : Blo 818347 1227671 := bstep (se 1 (by rfl) ⟨920753, by rfl⟩ : syracuseStep 1227671 = 1841507) B1841507
theorem B1227737 : Blo 818347 1227737 := bstep (se 2 (by rfl) ⟨460401, by rfl⟩ : syracuseStep 1227737 = 920803) B920803
theorem B1227851 : Blo 818347 1227851 := bstep (se 1 (by rfl) ⟨920888, by rfl⟩ : syracuseStep 1227851 = 1841777) B1841777
theorem B1227863 : Blo 818347 1227863 := bstep (se 1 (by rfl) ⟨920897, by rfl⟩ : syracuseStep 1227863 = 1841795) B1841795
theorem B1555595 : Blo 818347 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B1227929 : Blo 818347 1227929 := bstep (se 2 (by rfl) ⟨460473, by rfl⟩ : syracuseStep 1227929 = 920947) B920947
theorem B2768093 : Blo 818347 2768093 := bstep (se 3 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 2768093 = 1038035) B1038035
theorem B1228043 : Blo 818347 1228043 := bstep (se 1 (by rfl) ⟨921032, by rfl⟩ : syracuseStep 1228043 = 1842065) B1842065
theorem B1228055 : Blo 818347 1228055 := bstep (se 1 (by rfl) ⟨921041, by rfl⟩ : syracuseStep 1228055 = 1842083) B1842083
theorem B1555777 : Blo 818347 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B1228121 : Blo 818347 1228121 := bstep (se 2 (by rfl) ⟨460545, by rfl⟩ : syracuseStep 1228121 = 921091) B921091
theorem B2080151 : Blo 818347 2080151 := bstep (se 1 (by rfl) ⟨1560113, by rfl⟩ : syracuseStep 2080151 = 3120227) B3120227
theorem B1228235 : Blo 818347 1228235 := bstep (se 1 (by rfl) ⟨921176, by rfl⟩ : syracuseStep 1228235 = 1842353) B1842353
theorem B1228247 : Blo 818347 1228247 := bstep (se 1 (by rfl) ⟨921185, by rfl⟩ : syracuseStep 1228247 = 1842371) B1842371
theorem B1228313 : Blo 818347 1228313 := bstep (se 2 (by rfl) ⟨460617, by rfl⟩ : syracuseStep 1228313 = 921235) B921235
theorem B1228427 : Blo 818347 1228427 := bstep (se 1 (by rfl) ⟨921320, by rfl⟩ : syracuseStep 1228427 = 1842641) B1842641
theorem B1228439 : Blo 818347 1228439 := bstep (se 1 (by rfl) ⟨921329, by rfl⟩ : syracuseStep 1228439 = 1842659) B1842659
theorem B4439731 : Blo 818347 4439731 := bstep (se 1 (by rfl) ⟨3329798, by rfl⟩ : syracuseStep 4439731 = 6659597) B6659597
theorem B1752779 : Blo 818347 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1228505 : Blo 818347 1228505 := bstep (se 2 (by rfl) ⟨460689, by rfl⟩ : syracuseStep 1228505 = 921379) B921379
theorem B1228619 : Blo 818347 1228619 := bstep (se 1 (by rfl) ⟨921464, by rfl⟩ : syracuseStep 1228619 = 1842929) B1842929
theorem B1228631 : Blo 818347 1228631 := bstep (se 1 (by rfl) ⟨921473, by rfl⟩ : syracuseStep 1228631 = 1842947) B1842947
theorem B3325789 : Blo 818347 3325789 := bstep (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) B1247171
theorem B43106147 : Blo 818347 43106147 := bstep (se 1 (by rfl) ⟨32329610, by rfl⟩ : syracuseStep 43106147 = 64659221) B64659221
theorem B1228697 : Blo 818347 1228697 := bstep (se 2 (by rfl) ⟨460761, by rfl⟩ : syracuseStep 1228697 = 921523) B921523
theorem B1228811 : Blo 818347 1228811 := bstep (se 1 (by rfl) ⟨921608, by rfl⟩ : syracuseStep 1228811 = 1843217) B1843217
theorem B1556491 : Blo 818347 1556491 := bstep (se 1 (by rfl) ⟨1167368, by rfl⟩ : syracuseStep 1556491 = 2334737) B2334737
theorem B1228823 : Blo 818347 1228823 := bstep (se 1 (by rfl) ⟨921617, by rfl⟩ : syracuseStep 1228823 = 1843235) B1843235
theorem B1556567 : Blo 818347 1556567 := bstep (se 1 (by rfl) ⟨1167425, by rfl⟩ : syracuseStep 1556567 = 2334851) B2334851
theorem B1228889 : Blo 818347 1228889 := bstep (se 2 (by rfl) ⟨460833, by rfl⟩ : syracuseStep 1228889 = 921667) B921667
theorem B2080961 : Blo 818347 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B1229003 : Blo 818347 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B1229015 : Blo 818347 1229015 := bstep (se 1 (by rfl) ⟨921761, by rfl⟩ : syracuseStep 1229015 = 1843523) B1843523
theorem B1229081 : Blo 818347 1229081 := bstep (se 2 (by rfl) ⟨460905, by rfl⟩ : syracuseStep 1229081 = 921811) B921811
theorem B2769227 : Blo 818347 2769227 := bstep (se 1 (by rfl) ⟨2076920, by rfl⟩ : syracuseStep 2769227 = 4153841) B4153841
theorem B1229195 : Blo 818347 1229195 := bstep (se 1 (by rfl) ⟨921896, by rfl⟩ : syracuseStep 1229195 = 1843793) B1843793
theorem B1229207 : Blo 818347 1229207 := bstep (se 1 (by rfl) ⟨921905, by rfl⟩ : syracuseStep 1229207 = 1843811) B1843811
theorem B1229273 : Blo 818347 1229273 := bstep (se 2 (by rfl) ⟨460977, by rfl⟩ : syracuseStep 1229273 = 921955) B921955
theorem B23708173 : Blo 818347 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1753625 : Blo 818347 1753625 := bstep (se 2 (by rfl) ⟨657609, by rfl⟩ : syracuseStep 1753625 = 1315219) B1315219
theorem B1229387 : Blo 818347 1229387 := bstep (se 1 (by rfl) ⟨922040, by rfl⟩ : syracuseStep 1229387 = 1844081) B1844081
theorem B1229399 : Blo 818347 1229399 := bstep (se 1 (by rfl) ⟨922049, by rfl⟩ : syracuseStep 1229399 = 1844099) B1844099
theorem B2769497 : Blo 818347 2769497 := bstep (se 2 (by rfl) ⟨1038561, by rfl⟩ : syracuseStep 2769497 = 2077123) B2077123
theorem B1229465 : Blo 818347 1229465 := bstep (se 2 (by rfl) ⟨461049, by rfl⟩ : syracuseStep 1229465 = 922099) B922099
theorem B4735705 : Blo 818347 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B2081497 : Blo 818347 2081497 := bstep (se 2 (by rfl) ⟨780561, by rfl⟩ : syracuseStep 2081497 = 1561123) B1561123
theorem B1557235 : Blo 818347 1557235 := bstep (se 1 (by rfl) ⟨1167926, by rfl⟩ : syracuseStep 1557235 = 2335853) B2335853
theorem B1229579 : Blo 818347 1229579 := bstep (se 1 (by rfl) ⟨922184, by rfl⟩ : syracuseStep 1229579 = 1844369) B1844369
theorem B1229591 : Blo 818347 1229591 := bstep (se 1 (by rfl) ⟨922193, by rfl⟩ : syracuseStep 1229591 = 1844387) B1844387
theorem B1229657 : Blo 818347 1229657 := bstep (se 2 (by rfl) ⟨461121, by rfl⟩ : syracuseStep 1229657 = 922243) B922243
theorem B1229771 : Blo 818347 1229771 := bstep (se 1 (by rfl) ⟨922328, by rfl⟩ : syracuseStep 1229771 = 1844657) B1844657
theorem B1229783 : Blo 818347 1229783 := bstep (se 1 (by rfl) ⟨922337, by rfl⟩ : syracuseStep 1229783 = 1844675) B1844675
theorem B1557463 : Blo 818347 1557463 := bstep (se 1 (by rfl) ⟨1168097, by rfl⟩ : syracuseStep 1557463 = 2336195) B2336195
theorem B902135 : Blo 818347 902135 := bstep (se 1 (by rfl) ⟨676601, by rfl⟩ : syracuseStep 902135 = 1353203) B1353203
theorem B3326993 : Blo 818347 3326993 := bstep (se 2 (by rfl) ⟨1247622, by rfl⟩ : syracuseStep 3326993 = 2495245) B2495245
theorem B1229849 : Blo 818347 1229849 := bstep (se 2 (by rfl) ⟨461193, by rfl⟩ : syracuseStep 1229849 = 922387) B922387
theorem B1557569 : Blo 818347 1557569 := bstep (se 2 (by rfl) ⟨584088, by rfl⟩ : syracuseStep 1557569 = 1168177) B1168177
theorem B1229963 : Blo 818347 1229963 := bstep (se 1 (by rfl) ⟨922472, by rfl⟩ : syracuseStep 1229963 = 1844945) B1844945
theorem B1229975 : Blo 818347 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B6636761 : Blo 818347 6636761 := bstep (se 2 (by rfl) ⟨2488785, by rfl⟩ : syracuseStep 6636761 = 4977571) B4977571
theorem B1230041 : Blo 818347 1230041 := bstep (se 2 (by rfl) ⟨461265, by rfl⟩ : syracuseStep 1230041 = 922531) B922531
theorem B1557721 : Blo 818347 1557721 := bstep (se 2 (by rfl) ⟨584145, by rfl⟩ : syracuseStep 1557721 = 1168291) B1168291
theorem B2770199 : Blo 818347 2770199 := bstep (se 1 (by rfl) ⟨2077649, by rfl⟩ : syracuseStep 2770199 = 4155299) B4155299
theorem B1754419 : Blo 818347 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B1230155 : Blo 818347 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B1230167 : Blo 818347 1230167 := bstep (se 1 (by rfl) ⟨922625, by rfl⟩ : syracuseStep 1230167 = 1845251) B1845251
theorem B1262999 : Blo 818347 1262999 := bstep (se 1 (by rfl) ⟨947249, by rfl⟩ : syracuseStep 1262999 = 1894499) B1894499
theorem B1230233 : Blo 818347 1230233 := bstep (se 2 (by rfl) ⟨461337, by rfl⟩ : syracuseStep 1230233 = 922675) B922675
theorem B1230347 : Blo 818347 1230347 := bstep (se 1 (by rfl) ⟨922760, by rfl⟩ : syracuseStep 1230347 = 1845521) B1845521
theorem B1230359 : Blo 818347 1230359 := bstep (se 1 (by rfl) ⟨922769, by rfl⟩ : syracuseStep 1230359 = 1845539) B1845539
theorem B1230425 : Blo 818347 1230425 := bstep (se 2 (by rfl) ⟨461409, by rfl⟩ : syracuseStep 1230425 = 922819) B922819
theorem B8439389 : Blo 818347 8439389 := bstep (se 3 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 8439389 = 3164771) B3164771
theorem B1230539 : Blo 818347 1230539 := bstep (se 1 (by rfl) ⟨922904, by rfl⟩ : syracuseStep 1230539 = 1845809) B1845809
theorem B1230551 : Blo 818347 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B1230617 : Blo 818347 1230617 := bstep (se 2 (by rfl) ⟨461481, by rfl⟩ : syracuseStep 1230617 = 922963) B922963
theorem B2770739 : Blo 818347 2770739 := bstep (se 1 (by rfl) ⟨2078054, by rfl⟩ : syracuseStep 2770739 = 4156109) B4156109
theorem B6997853 : Blo 818347 6997853 := bstep (se 3 (by rfl) ⟨1312097, by rfl⟩ : syracuseStep 6997853 = 2624195) B2624195
theorem B4147037 : Blo 818347 4147037 := bstep (se 3 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 4147037 = 1555139) B1555139
theorem B39929699 : Blo 818347 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B1230731 : Blo 818347 1230731 := bstep (se 1 (by rfl) ⟨923048, by rfl⟩ : syracuseStep 1230731 = 1846097) B1846097
theorem B1230743 : Blo 818347 1230743 := bstep (se 1 (by rfl) ⟨923057, by rfl⟩ : syracuseStep 1230743 = 1846115) B1846115
theorem B1230809 : Blo 818347 1230809 := bstep (se 2 (by rfl) ⟨461553, by rfl⟩ : syracuseStep 1230809 = 923107) B923107
theorem B2771009 : Blo 818347 2771009 := bstep (se 2 (by rfl) ⟨1039128, by rfl⟩ : syracuseStep 2771009 = 2078257) B2078257
theorem B1230923 : Blo 818347 1230923 := bstep (se 1 (by rfl) ⟨923192, by rfl⟩ : syracuseStep 1230923 = 1846385) B1846385
theorem B1230935 : Blo 818347 1230935 := bstep (se 1 (by rfl) ⟨923201, by rfl⟩ : syracuseStep 1230935 = 1846403) B1846403
theorem B1755265 : Blo 818347 1755265 := bstep (se 2 (by rfl) ⟨658224, by rfl⟩ : syracuseStep 1755265 = 1316449) B1316449
theorem B9357443 : Blo 818347 9357443 := bstep (se 1 (by rfl) ⟨7018082, by rfl⟩ : syracuseStep 9357443 = 14036165) B14036165
theorem B1231001 : Blo 818347 1231001 := bstep (se 2 (by rfl) ⟨461625, by rfl⟩ : syracuseStep 1231001 = 923251) B923251
theorem B1165529 : Blo 818347 1165529 := bstep (se 2 (by rfl) ⟨437073, by rfl⟩ : syracuseStep 1165529 = 874147) B874147
theorem B6244613 : Blo 818347 6244613 := bstep (se 4 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 6244613 = 1170865) B1170865
theorem B1231115 : Blo 818347 1231115 := bstep (se 1 (by rfl) ⟨923336, by rfl⟩ : syracuseStep 1231115 = 1846673) B1846673
theorem B1231127 : Blo 818347 1231127 := bstep (se 1 (by rfl) ⟨923345, by rfl⟩ : syracuseStep 1231127 = 1846691) B1846691
theorem B2804057 : Blo 818347 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B1231193 : Blo 818347 1231193 := bstep (se 2 (by rfl) ⟨461697, by rfl⟩ : syracuseStep 1231193 = 923395) B923395
theorem B63883637 : Blo 818347 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B1231307 : Blo 818347 1231307 := bstep (se 1 (by rfl) ⟨923480, by rfl⟩ : syracuseStep 1231307 = 1846961) B1846961
theorem B7489997 : Blo 818347 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B1231319 : Blo 818347 1231319 := bstep (se 1 (by rfl) ⟨923489, by rfl⟩ : syracuseStep 1231319 = 1846979) B1846979
theorem B1755607 : Blo 818347 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B1559027 : Blo 818347 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B1231385 : Blo 818347 1231385 := bstep (se 2 (by rfl) ⟨461769, by rfl⟩ : syracuseStep 1231385 = 923539) B923539
theorem B2771549 : Blo 818347 2771549 := bstep (se 3 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 2771549 = 1039331) B1039331
theorem B1231499 : Blo 818347 1231499 := bstep (se 1 (by rfl) ⟨923624, by rfl⟩ : syracuseStep 1231499 = 1847249) B1847249
theorem B1559179 : Blo 818347 1559179 := bstep (se 1 (by rfl) ⟨1169384, by rfl⟩ : syracuseStep 1559179 = 2338769) B2338769
theorem B1231511 : Blo 818347 1231511 := bstep (se 1 (by rfl) ⟨923633, by rfl⟩ : syracuseStep 1231511 = 1847267) B1847267
theorem B1231577 : Blo 818347 1231577 := bstep (se 2 (by rfl) ⟨461841, by rfl⟩ : syracuseStep 1231577 = 923683) B923683
theorem B5917475 : Blo 818347 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B1231691 : Blo 818347 1231691 := bstep (se 1 (by rfl) ⟨923768, by rfl⟩ : syracuseStep 1231691 = 1847537) B1847537
theorem B1166167 : Blo 818347 1166167 := bstep (se 1 (by rfl) ⟨874625, by rfl⟩ : syracuseStep 1166167 = 1749251) B1749251
theorem B1231703 : Blo 818347 1231703 := bstep (se 1 (by rfl) ⟨923777, by rfl⟩ : syracuseStep 1231703 = 1847555) B1847555
theorem B1231769 : Blo 818347 1231769 := bstep (se 2 (by rfl) ⟨461913, by rfl⟩ : syracuseStep 1231769 = 923827) B923827
theorem B1559513 : Blo 818347 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B1231883 : Blo 818347 1231883 := bstep (se 1 (by rfl) ⟨923912, by rfl⟩ : syracuseStep 1231883 = 1847825) B1847825
theorem B1231895 : Blo 818347 1231895 := bstep (se 1 (by rfl) ⟨923921, by rfl⟩ : syracuseStep 1231895 = 1847843) B1847843
theorem B1231961 : Blo 818347 1231961 := bstep (se 2 (by rfl) ⟨461985, by rfl⟩ : syracuseStep 1231961 = 923971) B923971
theorem B937067 : Blo 818347 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B5262515 : Blo 818347 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B1232075 : Blo 818347 1232075 := bstep (se 1 (by rfl) ⟨924056, by rfl⟩ : syracuseStep 1232075 = 1848113) B1848113
theorem B1232087 : Blo 818347 1232087 := bstep (se 1 (by rfl) ⟨924065, by rfl⟩ : syracuseStep 1232087 = 1848131) B1848131
theorem B1232153 : Blo 818347 1232153 := bstep (se 2 (by rfl) ⟨462057, by rfl⟩ : syracuseStep 1232153 = 924115) B924115
theorem B1232267 : Blo 818347 1232267 := bstep (se 1 (by rfl) ⟨924200, by rfl⟩ : syracuseStep 1232267 = 1848401) B1848401
theorem B1232279 : Blo 818347 1232279 := bstep (se 1 (by rfl) ⟨924209, by rfl⟩ : syracuseStep 1232279 = 1848419) B1848419
theorem B1232345 : Blo 818347 1232345 := bstep (se 2 (by rfl) ⟨462129, by rfl⟩ : syracuseStep 1232345 = 924259) B924259
theorem B1232459 : Blo 818347 1232459 := bstep (se 1 (by rfl) ⟨924344, by rfl⟩ : syracuseStep 1232459 = 1848689) B1848689
theorem B1232471 : Blo 818347 1232471 := bstep (se 1 (by rfl) ⟨924353, by rfl⟩ : syracuseStep 1232471 = 1848707) B1848707
theorem B1560151 : Blo 818347 1560151 := bstep (se 1 (by rfl) ⟨1170113, by rfl⟩ : syracuseStep 1560151 = 2340227) B2340227
theorem B1166987 : Blo 818347 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B1232537 : Blo 818347 1232537 := bstep (se 2 (by rfl) ⟨462201, by rfl⟩ : syracuseStep 1232537 = 924403) B924403
theorem B2772683 : Blo 818347 2772683 := bstep (se 1 (by rfl) ⟨2079512, by rfl⟩ : syracuseStep 2772683 = 4159025) B4159025
theorem B14044913 : Blo 818347 14044913 := bstep (se 2 (by rfl) ⟨5266842, by rfl⟩ : syracuseStep 14044913 = 10533685) B10533685
theorem B1232651 : Blo 818347 1232651 := bstep (se 1 (by rfl) ⟨924488, by rfl⟩ : syracuseStep 1232651 = 1848977) B1848977
theorem B1232663 : Blo 818347 1232663 := bstep (se 1 (by rfl) ⟨924497, by rfl⟩ : syracuseStep 1232663 = 1848995) B1848995
theorem B1232729 : Blo 818347 1232729 := bstep (se 2 (by rfl) ⟨462273, by rfl⟩ : syracuseStep 1232729 = 924547) B924547
theorem B4149143 : Blo 818347 4149143 := bstep (se 1 (by rfl) ⟨3111857, by rfl⟩ : syracuseStep 4149143 = 6223715) B6223715
theorem B1232843 : Blo 818347 1232843 := bstep (se 1 (by rfl) ⟨924632, by rfl⟩ : syracuseStep 1232843 = 1849265) B1849265
theorem B1232855 : Blo 818347 1232855 := bstep (se 1 (by rfl) ⟨924641, by rfl⟩ : syracuseStep 1232855 = 1849283) B1849283
theorem B2772953 : Blo 818347 2772953 := bstep (se 2 (by rfl) ⟨1039857, by rfl⟩ : syracuseStep 2772953 = 2079715) B2079715
theorem B1232921 : Blo 818347 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B9359491 : Blo 818347 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B1233035 : Blo 818347 1233035 := bstep (se 1 (by rfl) ⟨924776, by rfl⟩ : syracuseStep 1233035 = 1849553) B1849553
theorem B1233047 : Blo 818347 1233047 := bstep (se 1 (by rfl) ⟨924785, by rfl⟩ : syracuseStep 1233047 = 1849571) B1849571
theorem B1233113 : Blo 818347 1233113 := bstep (se 2 (by rfl) ⟨462417, by rfl⟩ : syracuseStep 1233113 = 924835) B924835
theorem B1036567 : Blo 818347 1036567 := bstep (se 1 (by rfl) ⟨777425, by rfl⟩ : syracuseStep 1036567 = 1554851) B1554851
theorem B1233227 : Blo 818347 1233227 := bstep (se 1 (by rfl) ⟨924920, by rfl⟩ : syracuseStep 1233227 = 1849841) B1849841
theorem B1233239 : Blo 818347 1233239 := bstep (se 1 (by rfl) ⟨924929, by rfl⟩ : syracuseStep 1233239 = 1849859) B1849859
theorem B7000451 : Blo 818347 7000451 := bstep (se 1 (by rfl) ⟨5250338, by rfl⟩ : syracuseStep 7000451 = 10500677) B10500677
theorem B1560971 : Blo 818347 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B1233305 : Blo 818347 1233305 := bstep (se 2 (by rfl) ⟨462489, by rfl⟩ : syracuseStep 1233305 = 924979) B924979
theorem B2216371 : Blo 818347 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B1561025 : Blo 818347 1561025 := bstep (se 2 (by rfl) ⟨585384, by rfl⟩ : syracuseStep 1561025 = 1170769) B1170769
theorem B1233419 : Blo 818347 1233419 := bstep (se 1 (by rfl) ⟨925064, by rfl⟩ : syracuseStep 1233419 = 1850129) B1850129
theorem B1233431 : Blo 818347 1233431 := bstep (se 1 (by rfl) ⟨925073, by rfl⟩ : syracuseStep 1233431 = 1850147) B1850147
theorem B1659457 : Blo 818347 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B1167961 : Blo 818347 1167961 := bstep (se 2 (by rfl) ⟨437985, by rfl⟩ : syracuseStep 1167961 = 875971) B875971
theorem B1233497 : Blo 818347 1233497 := bstep (se 2 (by rfl) ⟨462561, by rfl⟩ : syracuseStep 1233497 = 925123) B925123
theorem B5263973 : Blo 818347 5263973 := bstep (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) B986995
theorem B2773655 : Blo 818347 2773655 := bstep (se 1 (by rfl) ⟨2080241, by rfl⟩ : syracuseStep 2773655 = 4160483) B4160483
theorem B7099427 : Blo 818347 7099427 := bstep (se 1 (by rfl) ⟨5324570, by rfl⟩ : syracuseStep 7099427 = 10649141) B10649141
theorem B1037387 : Blo 818347 1037387 := bstep (se 1 (by rfl) ⟨778040, by rfl⟩ : syracuseStep 1037387 = 1556081) B1556081
theorem B2774195 : Blo 818347 2774195 := bstep (se 1 (by rfl) ⟨2080646, by rfl⟩ : syracuseStep 2774195 = 4161293) B4161293
theorem B2774465 : Blo 818347 2774465 := bstep (se 2 (by rfl) ⟨1040424, by rfl⟩ : syracuseStep 2774465 = 2080849) B2080849
theorem B1169111 : Blo 818347 1169111 := bstep (se 1 (by rfl) ⟨876833, by rfl⟩ : syracuseStep 1169111 = 1753667) B1753667
theorem B1038091 : Blo 818347 1038091 := bstep (se 1 (by rfl) ⟨778568, by rfl⟩ : syracuseStep 1038091 = 1557137) B1557137
theorem B2775005 : Blo 818347 2775005 := bstep (se 3 (by rfl) ⟨520313, by rfl⟩ : syracuseStep 2775005 = 1040627) B1040627
theorem B1169419 : Blo 818347 1169419 := bstep (se 1 (by rfl) ⟨877064, by rfl⟩ : syracuseStep 1169419 = 1754129) B1754129
theorem B1038359 : Blo 818347 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B4675715 : Blo 818347 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B874967 : Blo 818347 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B1039063 : Blo 818347 1039063 := bstep (se 1 (by rfl) ⟨779297, by rfl⟩ : syracuseStep 1039063 = 1558595) B1558595
theorem B3496877 : Blo 818347 3496877 := bstep (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) B1311329
theorem B1170455 : Blo 818347 1170455 := bstep (se 1 (by rfl) ⟨877841, by rfl⟩ : syracuseStep 1170455 = 1755683) B1755683
theorem B14998679 : Blo 818347 14998679 := bstep (se 1 (by rfl) ⟨11249009, by rfl⟩ : syracuseStep 14998679 = 22498019) B22498019
theorem B1170649 : Blo 818347 1170649 := bstep (se 2 (by rfl) ⟨438993, by rfl⟩ : syracuseStep 1170649 = 877987) B877987
theorem B3497219 : Blo 818347 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B4152707 : Blo 818347 4152707 := bstep (se 1 (by rfl) ⟨3114530, by rfl⟩ : syracuseStep 4152707 = 6229061) B6229061
theorem B876791 : Blo 818347 876791 := bstep (se 1 (by rfl) ⟨657593, by rfl⟩ : syracuseStep 876791 = 1315187) B1315187
theorem B1040779 : Blo 818347 1040779 := bstep (se 1 (by rfl) ⟨780584, by rfl⟩ : syracuseStep 1040779 = 1561169) B1561169
theorem B7889501 : Blo 818347 7889501 := bstep (se 3 (by rfl) ⟨1479281, by rfl⟩ : syracuseStep 7889501 = 2958563) B2958563
theorem B877483 : Blo 818347 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B15000497 : Blo 818347 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B3499595 : Blo 818347 3499595 := bstep (se 1 (by rfl) ⟨2624696, by rfl⟩ : syracuseStep 3499595 = 5249393) B5249393
theorem B3991133 : Blo 818347 3991133 := bstep (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) B1496675
theorem B1664729 : Blo 818347 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B9332657 : Blo 818347 9332657 := bstep (se 2 (by rfl) ⟨3499746, by rfl⟩ : syracuseStep 9332657 = 6999493) B6999493
theorem B3598273 : Blo 818347 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B1402903 : Blo 818347 1402903 := bstep (se 1 (by rfl) ⟨1052177, by rfl⟩ : syracuseStep 1402903 = 2104355) B2104355
theorem B60778637 : Blo 818347 60778637 := bstep (se 3 (by rfl) ⟨11395994, by rfl⟩ : syracuseStep 60778637 = 22791989) B22791989
theorem B3500567 : Blo 818347 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B3107393 : Blo 818347 3107393 := bstep (se 2 (by rfl) ⟨1165272, by rfl⟩ : syracuseStep 3107393 = 2330545) B2330545
theorem B1502039 : Blo 818347 1502039 := bstep (se 1 (by rfl) ⟨1126529, by rfl⟩ : syracuseStep 1502039 = 2253059) B2253059
theorem B4746115 : Blo 818347 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B1665943 : Blo 818347 1665943 := bstep (se 1 (by rfl) ⟨1249457, by rfl⟩ : syracuseStep 1665943 = 2498915) B2498915
theorem B1993675 : Blo 818347 1993675 := bstep (se 1 (by rfl) ⟨1495256, by rfl⟩ : syracuseStep 1993675 = 2990513) B2990513
theorem B4156433 : Blo 818347 4156433 := bstep (se 2 (by rfl) ⟨1558662, by rfl⟩ : syracuseStep 4156433 = 3117325) B3117325
theorem B6843457 : Blo 818347 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B4156595 : Blo 818347 4156595 := bstep (se 1 (by rfl) ⟨3117446, by rfl⟩ : syracuseStep 4156595 = 6234893) B6234893
theorem B4681091 : Blo 818347 4681091 := bstep (se 1 (by rfl) ⟨3510818, by rfl⟩ : syracuseStep 4681091 = 7021637) B7021637
theorem B4681547 : Blo 818347 4681547 := bstep (se 1 (by rfl) ⟨3511160, by rfl⟩ : syracuseStep 4681547 = 7022321) B7022321
theorem B3108881 : Blo 818347 3108881 := bstep (se 2 (by rfl) ⟨1165830, by rfl⟩ : syracuseStep 3108881 = 2331661) B2331661
theorem B6222257 : Blo 818347 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B3109337 : Blo 818347 3109337 := bstep (se 2 (by rfl) ⟨1166001, by rfl⟩ : syracuseStep 3109337 = 2332003) B2332003
theorem B8417753 : Blo 818347 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B10678877 : Blo 818347 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B3109549 : Blo 818347 3109549 := bstep (se 3 (by rfl) ⟨583040, by rfl⟩ : syracuseStep 3109549 = 1166081) B1166081
theorem B6222743 : Blo 818347 6222743 := bstep (se 1 (by rfl) ⟨4667057, by rfl⟩ : syracuseStep 6222743 = 9334115) B9334115
theorem B3503027 : Blo 818347 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B3109853 : Blo 818347 3109853 := bstep (se 3 (by rfl) ⟨583097, by rfl⟩ : syracuseStep 3109853 = 1166195) B1166195
theorem B11990051 : Blo 818347 11990051 := bstep (se 1 (by rfl) ⟨8992538, by rfl⟩ : syracuseStep 11990051 = 17985077) B17985077
theorem B4158539 : Blo 818347 4158539 := bstep (se 1 (by rfl) ⟨3118904, by rfl⟩ : syracuseStep 4158539 = 6237809) B6237809
theorem B1406489 : Blo 818347 1406489 := bstep (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) B1054867
theorem B7010225 : Blo 818347 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B3799057 : Blo 818347 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B7895191 : Blo 818347 7895191 := bstep (se 1 (by rfl) ⟨5921393, by rfl⟩ : syracuseStep 7895191 = 11842787) B11842787
theorem B3504941 : Blo 818347 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B4160321 : Blo 818347 4160321 := bstep (se 2 (by rfl) ⟨1560120, by rfl⟩ : syracuseStep 4160321 = 3120241) B3120241
theorem B818347 : Blo 818347 818347 := bstep (se 1 (by rfl) ⟨613760, by rfl⟩ : syracuseStep 818347 = 1227521) B1227521
theorem B818359 : Blo 818347 818359 := bstep (se 1 (by rfl) ⟨613769, by rfl⟩ : syracuseStep 818359 = 1227539) B1227539
theorem B818379 : Blo 818347 818379 := bstep (se 1 (by rfl) ⟨613784, by rfl⟩ : syracuseStep 818379 = 1227569) B1227569
theorem B818391 : Blo 818347 818391 := bstep (se 1 (by rfl) ⟨613793, by rfl⟩ : syracuseStep 818391 = 1227587) B1227587
theorem B818411 : Blo 818347 818411 := bstep (se 1 (by rfl) ⟨613808, by rfl⟩ : syracuseStep 818411 = 1227617) B1227617
theorem B949483 : Blo 818347 949483 := bstep (se 1 (by rfl) ⟨712112, by rfl⟩ : syracuseStep 949483 = 1424225) B1424225
theorem B818423 : Blo 818347 818423 := bstep (se 1 (by rfl) ⟨613817, by rfl⟩ : syracuseStep 818423 = 1227635) B1227635
theorem B818443 : Blo 818347 818443 := bstep (se 1 (by rfl) ⟨613832, by rfl⟩ : syracuseStep 818443 = 1227665) B1227665
theorem B818455 : Blo 818347 818455 := bstep (se 1 (by rfl) ⟨613841, by rfl⟩ : syracuseStep 818455 = 1227683) B1227683
theorem B1244441 : Blo 818347 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B818475 : Blo 818347 818475 := bstep (se 1 (by rfl) ⟨613856, by rfl⟩ : syracuseStep 818475 = 1227713) B1227713
theorem B818487 : Blo 818347 818487 := bstep (se 1 (by rfl) ⟨613865, by rfl⟩ : syracuseStep 818487 = 1227731) B1227731
theorem B818507 : Blo 818347 818507 := bstep (se 1 (by rfl) ⟨613880, by rfl⟩ : syracuseStep 818507 = 1227761) B1227761
theorem B818519 : Blo 818347 818519 := bstep (se 1 (by rfl) ⟨613889, by rfl⟩ : syracuseStep 818519 = 1227779) B1227779
theorem B818539 : Blo 818347 818539 := bstep (se 1 (by rfl) ⟨613904, by rfl⟩ : syracuseStep 818539 = 1227809) B1227809
theorem B818551 : Blo 818347 818551 := bstep (se 1 (by rfl) ⟨613913, by rfl⟩ : syracuseStep 818551 = 1227827) B1227827
theorem B818571 : Blo 818347 818571 := bstep (se 1 (by rfl) ⟨613928, by rfl⟩ : syracuseStep 818571 = 1227857) B1227857
theorem B818583 : Blo 818347 818583 := bstep (se 1 (by rfl) ⟨613937, by rfl⟩ : syracuseStep 818583 = 1227875) B1227875
theorem B818603 : Blo 818347 818603 := bstep (se 1 (by rfl) ⟨613952, by rfl⟩ : syracuseStep 818603 = 1227905) B1227905
theorem B818615 : Blo 818347 818615 := bstep (se 1 (by rfl) ⟨613961, by rfl⟩ : syracuseStep 818615 = 1227923) B1227923
theorem B818635 : Blo 818347 818635 := bstep (se 1 (by rfl) ⟨613976, by rfl⟩ : syracuseStep 818635 = 1227953) B1227953
theorem B818647 : Blo 818347 818647 := bstep (se 1 (by rfl) ⟨613985, by rfl⟩ : syracuseStep 818647 = 1227971) B1227971
theorem B3505625 : Blo 818347 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B818667 : Blo 818347 818667 := bstep (se 1 (by rfl) ⟨614000, by rfl⟩ : syracuseStep 818667 = 1228001) B1228001
theorem B818679 : Blo 818347 818679 := bstep (se 1 (by rfl) ⟨614009, by rfl⟩ : syracuseStep 818679 = 1228019) B1228019
theorem B3112451 : Blo 818347 3112451 := bstep (se 1 (by rfl) ⟨2334338, by rfl⟩ : syracuseStep 3112451 = 4668677) B4668677
theorem B818699 : Blo 818347 818699 := bstep (se 1 (by rfl) ⟨614024, by rfl⟩ : syracuseStep 818699 = 1228049) B1228049
theorem B3112465 : Blo 818347 3112465 := bstep (se 2 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 3112465 = 2334349) B2334349
theorem B818711 : Blo 818347 818711 := bstep (se 1 (by rfl) ⟨614033, by rfl⟩ : syracuseStep 818711 = 1228067) B1228067
theorem B818731 : Blo 818347 818731 := bstep (se 1 (by rfl) ⟨614048, by rfl⟩ : syracuseStep 818731 = 1228097) B1228097
theorem B818743 : Blo 818347 818743 := bstep (se 1 (by rfl) ⟨614057, by rfl⟩ : syracuseStep 818743 = 1228115) B1228115
theorem B818763 : Blo 818347 818763 := bstep (se 1 (by rfl) ⟨614072, by rfl⟩ : syracuseStep 818763 = 1228145) B1228145
theorem B818775 : Blo 818347 818775 := bstep (se 1 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 818775 = 1228163) B1228163
theorem B818795 : Blo 818347 818795 := bstep (se 1 (by rfl) ⟨614096, by rfl⟩ : syracuseStep 818795 = 1228193) B1228193
theorem B818807 : Blo 818347 818807 := bstep (se 1 (by rfl) ⟨614105, by rfl⟩ : syracuseStep 818807 = 1228211) B1228211
theorem B818827 : Blo 818347 818827 := bstep (se 1 (by rfl) ⟨614120, by rfl⟩ : syracuseStep 818827 = 1228241) B1228241
theorem B818839 : Blo 818347 818839 := bstep (se 1 (by rfl) ⟨614129, by rfl⟩ : syracuseStep 818839 = 1228259) B1228259
theorem B818859 : Blo 818347 818859 := bstep (se 1 (by rfl) ⟨614144, by rfl⟩ : syracuseStep 818859 = 1228289) B1228289
theorem B2916013 : Blo 818347 2916013 := bstep (se 3 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 2916013 = 1093505) B1093505
theorem B818871 : Blo 818347 818871 := bstep (se 1 (by rfl) ⟨614153, by rfl⟩ : syracuseStep 818871 = 1228307) B1228307
theorem B818891 : Blo 818347 818891 := bstep (se 1 (by rfl) ⟨614168, by rfl⟩ : syracuseStep 818891 = 1228337) B1228337
theorem B818903 : Blo 818347 818903 := bstep (se 1 (by rfl) ⟨614177, by rfl⟩ : syracuseStep 818903 = 1228355) B1228355
theorem B818923 : Blo 818347 818923 := bstep (se 1 (by rfl) ⟨614192, by rfl⟩ : syracuseStep 818923 = 1228385) B1228385
theorem B818935 : Blo 818347 818935 := bstep (se 1 (by rfl) ⟨614201, by rfl⟩ : syracuseStep 818935 = 1228403) B1228403
theorem B818955 : Blo 818347 818955 := bstep (se 1 (by rfl) ⟨614216, by rfl⟩ : syracuseStep 818955 = 1228433) B1228433
theorem B818967 : Blo 818347 818967 := bstep (se 1 (by rfl) ⟨614225, by rfl⟩ : syracuseStep 818967 = 1228451) B1228451
theorem B818987 : Blo 818347 818987 := bstep (se 1 (by rfl) ⟨614240, by rfl⟩ : syracuseStep 818987 = 1228481) B1228481
theorem B818999 : Blo 818347 818999 := bstep (se 1 (by rfl) ⟨614249, by rfl⟩ : syracuseStep 818999 = 1228499) B1228499
theorem B7470913 : Blo 818347 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B3112769 : Blo 818347 3112769 := bstep (se 2 (by rfl) ⟨1167288, by rfl⟩ : syracuseStep 3112769 = 2334577) B2334577
theorem B819019 : Blo 818347 819019 := bstep (se 1 (by rfl) ⟨614264, by rfl⟩ : syracuseStep 819019 = 1228529) B1228529
theorem B819031 : Blo 818347 819031 := bstep (se 1 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 819031 = 1228547) B1228547
theorem B819051 : Blo 818347 819051 := bstep (se 1 (by rfl) ⟨614288, by rfl⟩ : syracuseStep 819051 = 1228577) B1228577
theorem B819063 : Blo 818347 819063 := bstep (se 1 (by rfl) ⟨614297, by rfl⟩ : syracuseStep 819063 = 1228595) B1228595
theorem B819083 : Blo 818347 819083 := bstep (se 1 (by rfl) ⟨614312, by rfl⟩ : syracuseStep 819083 = 1228625) B1228625
theorem B1245079 : Blo 818347 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B819095 : Blo 818347 819095 := bstep (se 1 (by rfl) ⟨614321, by rfl⟩ : syracuseStep 819095 = 1228643) B1228643
theorem B819115 : Blo 818347 819115 := bstep (se 1 (by rfl) ⟨614336, by rfl⟩ : syracuseStep 819115 = 1228673) B1228673
theorem B819127 : Blo 818347 819127 := bstep (se 1 (by rfl) ⟨614345, by rfl⟩ : syracuseStep 819127 = 1228691) B1228691
theorem B819147 : Blo 818347 819147 := bstep (se 1 (by rfl) ⟨614360, by rfl⟩ : syracuseStep 819147 = 1228721) B1228721
theorem B819159 : Blo 818347 819159 := bstep (se 1 (by rfl) ⟨614369, by rfl⟩ : syracuseStep 819159 = 1228739) B1228739
theorem B3735517 : Blo 818347 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B819179 : Blo 818347 819179 := bstep (se 1 (by rfl) ⟨614384, by rfl⟩ : syracuseStep 819179 = 1228769) B1228769
theorem B819191 : Blo 818347 819191 := bstep (se 1 (by rfl) ⟨614393, by rfl⟩ : syracuseStep 819191 = 1228787) B1228787
theorem B819207 : Blo 818347 819207 := bstep (se 1 (by rfl) ⟨614405, by rfl⟩ : syracuseStep 819207 = 1228811) B1228811
theorem B819215 : Blo 818347 819215 := bstep (se 1 (by rfl) ⟨614411, by rfl⟩ : syracuseStep 819215 = 1228823) B1228823
theorem B819259 : Blo 818347 819259 := bstep (se 1 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 819259 = 1228889) B1228889
theorem B819335 : Blo 818347 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B819343 : Blo 818347 819343 := bstep (se 1 (by rfl) ⟨614507, by rfl⟩ : syracuseStep 819343 = 1229015) B1229015
theorem B819387 : Blo 818347 819387 := bstep (se 1 (by rfl) ⟨614540, by rfl⟩ : syracuseStep 819387 = 1229081) B1229081
theorem B819463 : Blo 818347 819463 := bstep (se 1 (by rfl) ⟨614597, by rfl⟩ : syracuseStep 819463 = 1229195) B1229195
theorem B819471 : Blo 818347 819471 := bstep (se 1 (by rfl) ⟨614603, by rfl⟩ : syracuseStep 819471 = 1229207) B1229207
theorem B819515 : Blo 818347 819515 := bstep (se 1 (by rfl) ⟨614636, by rfl⟩ : syracuseStep 819515 = 1229273) B1229273
theorem B2490743 : Blo 818347 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B819591 : Blo 818347 819591 := bstep (se 1 (by rfl) ⟨614693, by rfl⟩ : syracuseStep 819591 = 1229387) B1229387
theorem B819599 : Blo 818347 819599 := bstep (se 1 (by rfl) ⟨614699, by rfl⟩ : syracuseStep 819599 = 1229399) B1229399
theorem B819643 : Blo 818347 819643 := bstep (se 1 (by rfl) ⟨614732, by rfl⟩ : syracuseStep 819643 = 1229465) B1229465
theorem B819719 : Blo 818347 819719 := bstep (se 1 (by rfl) ⟨614789, by rfl⟩ : syracuseStep 819719 = 1229579) B1229579
theorem B819727 : Blo 818347 819727 := bstep (se 1 (by rfl) ⟨614795, by rfl⟩ : syracuseStep 819727 = 1229591) B1229591
theorem B819771 : Blo 818347 819771 := bstep (se 1 (by rfl) ⟨614828, by rfl⟩ : syracuseStep 819771 = 1229657) B1229657
theorem B819847 : Blo 818347 819847 := bstep (se 1 (by rfl) ⟨614885, by rfl⟩ : syracuseStep 819847 = 1229771) B1229771
theorem B819855 : Blo 818347 819855 := bstep (se 1 (by rfl) ⟨614891, by rfl⟩ : syracuseStep 819855 = 1229783) B1229783
theorem B983723 : Blo 818347 983723 := bstep (se 1 (by rfl) ⟨737792, by rfl⟩ : syracuseStep 983723 = 1475585) B1475585
theorem B819899 : Blo 818347 819899 := bstep (se 1 (by rfl) ⟨614924, by rfl⟩ : syracuseStep 819899 = 1229849) B1229849
theorem B819975 : Blo 818347 819975 := bstep (se 1 (by rfl) ⟨614981, by rfl⟩ : syracuseStep 819975 = 1229963) B1229963
theorem B819983 : Blo 818347 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B4424507 : Blo 818347 4424507 := bstep (se 1 (by rfl) ⟨3318380, by rfl⟩ : syracuseStep 4424507 = 6636761) B6636761
theorem B1311547 : Blo 818347 1311547 := bstep (se 1 (by rfl) ⟨983660, by rfl⟩ : syracuseStep 1311547 = 1967321) B1967321
theorem B820027 : Blo 818347 820027 := bstep (se 1 (by rfl) ⟨615020, by rfl⟩ : syracuseStep 820027 = 1230041) B1230041
theorem B820103 : Blo 818347 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B820111 : Blo 818347 820111 := bstep (se 1 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 820111 = 1230167) B1230167
theorem B820155 : Blo 818347 820155 := bstep (se 1 (by rfl) ⟨615116, by rfl⟩ : syracuseStep 820155 = 1230233) B1230233
theorem B820231 : Blo 818347 820231 := bstep (se 1 (by rfl) ⟨615173, by rfl⟩ : syracuseStep 820231 = 1230347) B1230347
theorem B820239 : Blo 818347 820239 := bstep (se 1 (by rfl) ⟨615179, by rfl⟩ : syracuseStep 820239 = 1230359) B1230359
theorem B4162589 : Blo 818347 4162589 := bstep (se 3 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 4162589 = 1560971) B1560971
theorem B820283 : Blo 818347 820283 := bstep (se 1 (by rfl) ⟨615212, by rfl⟩ : syracuseStep 820283 = 1230425) B1230425
theorem B820359 : Blo 818347 820359 := bstep (se 1 (by rfl) ⟨615269, by rfl⟩ : syracuseStep 820359 = 1230539) B1230539
theorem B820367 : Blo 818347 820367 := bstep (se 1 (by rfl) ⟨615275, by rfl⟩ : syracuseStep 820367 = 1230551) B1230551
theorem B6227117 : Blo 818347 6227117 := bstep (se 3 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 6227117 = 2335169) B2335169
theorem B820411 : Blo 818347 820411 := bstep (se 1 (by rfl) ⟨615308, by rfl⟩ : syracuseStep 820411 = 1230617) B1230617
theorem B3507401 : Blo 818347 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B820487 : Blo 818347 820487 := bstep (se 1 (by rfl) ⟨615365, by rfl⟩ : syracuseStep 820487 = 1230731) B1230731
theorem B820495 : Blo 818347 820495 := bstep (se 1 (by rfl) ⟨615371, by rfl⟩ : syracuseStep 820495 = 1230743) B1230743
theorem B820539 : Blo 818347 820539 := bstep (se 1 (by rfl) ⟨615404, by rfl⟩ : syracuseStep 820539 = 1230809) B1230809
theorem B820615 : Blo 818347 820615 := bstep (se 1 (by rfl) ⟨615461, by rfl⟩ : syracuseStep 820615 = 1230923) B1230923
theorem B820623 : Blo 818347 820623 := bstep (se 1 (by rfl) ⟨615467, by rfl⟩ : syracuseStep 820623 = 1230935) B1230935
theorem B820667 : Blo 818347 820667 := bstep (se 1 (by rfl) ⟨615500, by rfl⟩ : syracuseStep 820667 = 1231001) B1231001
theorem B4163075 : Blo 818347 4163075 := bstep (se 1 (by rfl) ⟨3122306, by rfl⟩ : syracuseStep 4163075 = 6244613) B6244613
theorem B984583 : Blo 818347 984583 := bstep (se 1 (by rfl) ⟨738437, by rfl⟩ : syracuseStep 984583 = 1476875) B1476875
theorem B820743 : Blo 818347 820743 := bstep (se 1 (by rfl) ⟨615557, by rfl⟩ : syracuseStep 820743 = 1231115) B1231115
theorem B820751 : Blo 818347 820751 := bstep (se 1 (by rfl) ⟨615563, by rfl⟩ : syracuseStep 820751 = 1231127) B1231127
theorem B1869371 : Blo 818347 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B820795 : Blo 818347 820795 := bstep (se 1 (by rfl) ⟨615596, by rfl⟩ : syracuseStep 820795 = 1231193) B1231193
theorem B820871 : Blo 818347 820871 := bstep (se 1 (by rfl) ⟨615653, by rfl⟩ : syracuseStep 820871 = 1231307) B1231307
theorem B820879 : Blo 818347 820879 := bstep (se 1 (by rfl) ⟨615659, by rfl⟩ : syracuseStep 820879 = 1231319) B1231319
theorem B820923 : Blo 818347 820923 := bstep (se 1 (by rfl) ⟨615692, by rfl⟩ : syracuseStep 820923 = 1231385) B1231385
theorem B820999 : Blo 818347 820999 := bstep (se 1 (by rfl) ⟨615749, by rfl⟩ : syracuseStep 820999 = 1231499) B1231499
theorem B821007 : Blo 818347 821007 := bstep (se 1 (by rfl) ⟨615755, by rfl⟩ : syracuseStep 821007 = 1231511) B1231511
theorem B821051 : Blo 818347 821051 := bstep (se 1 (by rfl) ⟨615788, by rfl⟩ : syracuseStep 821051 = 1231577) B1231577
theorem B35915633 : Blo 818347 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B821127 : Blo 818347 821127 := bstep (se 1 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 821127 = 1231691) B1231691
theorem B821135 : Blo 818347 821135 := bstep (se 1 (by rfl) ⟨615851, by rfl⟩ : syracuseStep 821135 = 1231703) B1231703
theorem B821179 : Blo 818347 821179 := bstep (se 1 (by rfl) ⟨615884, by rfl⟩ : syracuseStep 821179 = 1231769) B1231769
theorem B821255 : Blo 818347 821255 := bstep (se 1 (by rfl) ⟨615941, by rfl⟩ : syracuseStep 821255 = 1231883) B1231883
theorem B821263 : Blo 818347 821263 := bstep (se 1 (by rfl) ⟨615947, by rfl⟩ : syracuseStep 821263 = 1231895) B1231895
theorem B821307 : Blo 818347 821307 := bstep (se 1 (by rfl) ⟨615980, by rfl⟩ : syracuseStep 821307 = 1231961) B1231961
theorem B3934295 : Blo 818347 3934295 := bstep (se 1 (by rfl) ⟨2950721, by rfl⟩ : syracuseStep 3934295 = 5901443) B5901443
theorem B3508343 : Blo 818347 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B1968263 : Blo 818347 1968263 := bstep (se 1 (by rfl) ⟨1476197, by rfl⟩ : syracuseStep 1968263 = 2952395) B2952395
theorem B821383 : Blo 818347 821383 := bstep (se 1 (by rfl) ⟨616037, by rfl⟩ : syracuseStep 821383 = 1232075) B1232075
theorem B821391 : Blo 818347 821391 := bstep (se 1 (by rfl) ⟨616043, by rfl⟩ : syracuseStep 821391 = 1232087) B1232087
theorem B821435 : Blo 818347 821435 := bstep (se 1 (by rfl) ⟨616076, by rfl⟩ : syracuseStep 821435 = 1232153) B1232153
theorem B11798729 : Blo 818347 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B821511 : Blo 818347 821511 := bstep (se 1 (by rfl) ⟨616133, by rfl⟩ : syracuseStep 821511 = 1232267) B1232267
theorem B2492687 : Blo 818347 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B821519 : Blo 818347 821519 := bstep (se 1 (by rfl) ⟨616139, by rfl⟩ : syracuseStep 821519 = 1232279) B1232279
theorem B821563 : Blo 818347 821563 := bstep (se 1 (by rfl) ⟨616172, by rfl⟩ : syracuseStep 821563 = 1232345) B1232345
theorem B821639 : Blo 818347 821639 := bstep (se 1 (by rfl) ⟨616229, by rfl⟩ : syracuseStep 821639 = 1232459) B1232459
theorem B821647 : Blo 818347 821647 := bstep (se 1 (by rfl) ⟨616235, by rfl⟩ : syracuseStep 821647 = 1232471) B1232471
theorem B821691 : Blo 818347 821691 := bstep (se 1 (by rfl) ⟨616268, by rfl⟩ : syracuseStep 821691 = 1232537) B1232537
theorem B9341405 : Blo 818347 9341405 := bstep (se 3 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 9341405 = 3503027) B3503027
theorem B821767 : Blo 818347 821767 := bstep (se 1 (by rfl) ⟨616325, by rfl⟩ : syracuseStep 821767 = 1232651) B1232651
theorem B821775 : Blo 818347 821775 := bstep (se 1 (by rfl) ⟨616331, by rfl⟩ : syracuseStep 821775 = 1232663) B1232663
theorem B821819 : Blo 818347 821819 := bstep (se 1 (by rfl) ⟨616364, by rfl⟩ : syracuseStep 821819 = 1232729) B1232729
theorem B821895 : Blo 818347 821895 := bstep (se 1 (by rfl) ⟨616421, by rfl⟩ : syracuseStep 821895 = 1232843) B1232843
theorem B821903 : Blo 818347 821903 := bstep (se 1 (by rfl) ⟨616427, by rfl⟩ : syracuseStep 821903 = 1232855) B1232855
theorem B821947 : Blo 818347 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B822023 : Blo 818347 822023 := bstep (se 1 (by rfl) ⟨616517, by rfl⟩ : syracuseStep 822023 = 1233035) B1233035
theorem B822031 : Blo 818347 822031 := bstep (se 1 (by rfl) ⟨616523, by rfl⟩ : syracuseStep 822031 = 1233047) B1233047
theorem B1313579 : Blo 818347 1313579 := bstep (se 1 (by rfl) ⟨985184, by rfl⟩ : syracuseStep 1313579 = 1970369) B1970369
theorem B1248043 : Blo 818347 1248043 := bstep (se 1 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 1248043 = 1872065) B1872065
theorem B822075 : Blo 818347 822075 := bstep (se 1 (by rfl) ⟨616556, by rfl⟩ : syracuseStep 822075 = 1233113) B1233113
theorem B822151 : Blo 818347 822151 := bstep (se 1 (by rfl) ⟨616613, by rfl⟩ : syracuseStep 822151 = 1233227) B1233227
theorem B822159 : Blo 818347 822159 := bstep (se 1 (by rfl) ⟨616619, by rfl⟩ : syracuseStep 822159 = 1233239) B1233239
theorem B13306787 : Blo 818347 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B822203 : Blo 818347 822203 := bstep (se 1 (by rfl) ⟨616652, by rfl⟩ : syracuseStep 822203 = 1233305) B1233305
theorem B822279 : Blo 818347 822279 := bstep (se 1 (by rfl) ⟨616709, by rfl⟩ : syracuseStep 822279 = 1233419) B1233419
theorem B822287 : Blo 818347 822287 := bstep (se 1 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 822287 = 1233431) B1233431
theorem B2624555 : Blo 818347 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B822331 : Blo 818347 822331 := bstep (se 1 (by rfl) ⟨616748, by rfl⟩ : syracuseStep 822331 = 1233497) B1233497
theorem B3509315 : Blo 818347 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B920839 : Blo 818347 920839 := bstep (se 1 (by rfl) ⟨690629, by rfl⟩ : syracuseStep 920839 = 1381259) B1381259
theorem B1314091 : Blo 818347 1314091 := bstep (se 1 (by rfl) ⟨985568, by rfl⟩ : syracuseStep 1314091 = 1971137) B1971137
theorem B921019 : Blo 818347 921019 := bstep (se 1 (by rfl) ⟨690764, by rfl⟩ : syracuseStep 921019 = 1381529) B1381529
theorem B6229547 : Blo 818347 6229547 := bstep (se 1 (by rfl) ⟨4672160, by rfl⟩ : syracuseStep 6229547 = 9344321) B9344321
theorem B8851123 : Blo 818347 8851123 := bstep (se 1 (by rfl) ⟨6638342, by rfl⟩ : syracuseStep 8851123 = 13276685) B13276685
theorem B6328153 : Blo 818347 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B921487 : Blo 818347 921487 := bstep (se 1 (by rfl) ⟨691115, by rfl⟩ : syracuseStep 921487 = 1382231) B1382231
theorem B2658233 : Blo 818347 2658233 := bstep (se 2 (by rfl) ⟨996837, by rfl⟩ : syracuseStep 2658233 = 1993675) B1993675
theorem B2101307 : Blo 818347 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B3117143 : Blo 818347 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B921991 : Blo 818347 921991 := bstep (se 1 (by rfl) ⟨691493, by rfl⟩ : syracuseStep 921991 = 1382987) B1382987
theorem B7016989 : Blo 818347 7016989 := bstep (se 3 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 7016989 = 2631371) B2631371
theorem B922171 : Blo 818347 922171 := bstep (se 1 (by rfl) ⟨691628, by rfl⟩ : syracuseStep 922171 = 1383257) B1383257
theorem B3117629 : Blo 818347 3117629 := bstep (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) B1169111
theorem B2331251 : Blo 818347 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B6656741 : Blo 818347 6656741 := bstep (se 4 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 6656741 = 1248139) B1248139
theorem B9999119 : Blo 818347 9999119 := bstep (se 1 (by rfl) ⟨7499339, by rfl⟩ : syracuseStep 9999119 = 14998679) B14998679
theorem B2626337 : Blo 818347 2626337 := bstep (se 2 (by rfl) ⟨984876, by rfl⟩ : syracuseStep 2626337 = 1969753) B1969753
theorem B2331479 : Blo 818347 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B6656921 : Blo 818347 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B1971145 : Blo 818347 1971145 := bstep (se 2 (by rfl) ⟨739179, by rfl⟩ : syracuseStep 1971145 = 1478359) B1478359
theorem B922639 : Blo 818347 922639 := bstep (se 1 (by rfl) ⟨691979, by rfl⟩ : syracuseStep 922639 = 1383959) B1383959
theorem B1381495 : Blo 818347 1381495 := bstep (se 1 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 1381495 = 2072243) B2072243
theorem B1971319 : Blo 818347 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B15963425 : Blo 818347 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B1381691 : Blo 818347 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B4429241 : Blo 818347 4429241 := bstep (se 2 (by rfl) ⟨1660965, by rfl⟩ : syracuseStep 4429241 = 3321931) B3321931
theorem B923143 : Blo 818347 923143 := bstep (se 1 (by rfl) ⟨692357, by rfl⟩ : syracuseStep 923143 = 1384715) B1384715
theorem B923323 : Blo 818347 923323 := bstep (se 1 (by rfl) ⟨692492, by rfl⟩ : syracuseStep 923323 = 1384985) B1384985
theorem B1382089 : Blo 818347 1382089 := bstep (se 2 (by rfl) ⟨518283, by rfl⟩ : syracuseStep 1382089 = 1036567) B1036567
theorem B4429541 : Blo 818347 4429541 := bstep (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) B830539
theorem B11802419 : Blo 818347 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B7870283 : Blo 818347 7870283 := bstep (se 1 (by rfl) ⟨5902712, by rfl⟩ : syracuseStep 7870283 = 11805425) B11805425
theorem B2955161 : Blo 818347 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B10000331 : Blo 818347 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B3119057 : Blo 818347 3119057 := bstep (se 2 (by rfl) ⟨1169646, by rfl⟩ : syracuseStep 3119057 = 2339293) B2339293
theorem B923791 : Blo 818347 923791 := bstep (se 1 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 923791 = 1385687) B1385687
theorem B5609645 : Blo 818347 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B1841543 : Blo 818347 1841543 := bstep (se 1 (by rfl) ⟨1381157, by rfl⟩ : syracuseStep 1841543 = 2762315) B2762315
theorem B2333063 : Blo 818347 2333063 := bstep (se 1 (by rfl) ⟨1749797, by rfl⟩ : syracuseStep 2333063 = 3499595) B3499595
theorem B1382791 : Blo 818347 1382791 := bstep (se 1 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 1382791 = 2074187) B2074187
theorem B7018973 : Blo 818347 7018973 := bstep (se 3 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 7018973 = 2632115) B2632115
theorem B1841723 : Blo 818347 1841723 := bstep (se 1 (by rfl) ⟨1381292, by rfl⟩ : syracuseStep 1841723 = 2762585) B2762585
theorem B2333245 : Blo 818347 2333245 := bstep (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) B874967
theorem B924295 : Blo 818347 924295 := bstep (se 1 (by rfl) ⟨693221, by rfl⟩ : syracuseStep 924295 = 1386443) B1386443
theorem B1841849 : Blo 818347 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B924475 : Blo 818347 924475 := bstep (se 1 (by rfl) ⟨693356, by rfl⟩ : syracuseStep 924475 = 1386713) B1386713
theorem B3939293 : Blo 818347 3939293 := bstep (se 3 (by rfl) ⟨738617, by rfl⟩ : syracuseStep 3939293 = 1477235) B1477235
theorem B1842191 : Blo 818347 1842191 := bstep (se 1 (by rfl) ⟨1381643, by rfl⟩ : syracuseStep 1842191 = 2763287) B2763287
theorem B2333711 : Blo 818347 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B1383439 : Blo 818347 1383439 := bstep (se 1 (by rfl) ⟨1037579, by rfl⟩ : syracuseStep 1383439 = 2075159) B2075159
theorem B1842209 : Blo 818347 1842209 := bstep (se 2 (by rfl) ⟨690828, by rfl⟩ : syracuseStep 1842209 = 1381657) B1381657
theorem B2071595 : Blo 818347 2071595 := bstep (se 1 (by rfl) ⟨1553696, by rfl⟩ : syracuseStep 2071595 = 3107393) B3107393
theorem B924943 : Blo 818347 924943 := bstep (se 1 (by rfl) ⟨693707, by rfl⟩ : syracuseStep 924943 = 1387415) B1387415
theorem B2366779 : Blo 818347 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B1842551 : Blo 818347 1842551 := bstep (se 1 (by rfl) ⟨1381913, by rfl⟩ : syracuseStep 1842551 = 2763827) B2763827
theorem B6495623 : Blo 818347 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1842731 : Blo 818347 1842731 := bstep (se 1 (by rfl) ⟨1382048, by rfl⟩ : syracuseStep 1842731 = 2764097) B2764097
theorem B1383979 : Blo 818347 1383979 := bstep (se 1 (by rfl) ⟨1037984, by rfl⟩ : syracuseStep 1383979 = 2075969) B2075969
theorem B3120727 : Blo 818347 3120727 := bstep (se 1 (by rfl) ⟨2340545, by rfl⟩ : syracuseStep 3120727 = 4681091) B4681091
theorem B1384121 : Blo 818347 1384121 := bstep (se 2 (by rfl) ⟨519045, by rfl⟩ : syracuseStep 1384121 = 1038091) B1038091
theorem B5250905 : Blo 818347 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B3121031 : Blo 818347 3121031 := bstep (se 1 (by rfl) ⟨2340773, by rfl⟩ : syracuseStep 3121031 = 4681547) B4681547
theorem B1843091 : Blo 818347 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1843145 : Blo 818347 1843145 := bstep (se 2 (by rfl) ⟨691179, by rfl⟩ : syracuseStep 1843145 = 1382359) B1382359
theorem B2072587 : Blo 818347 2072587 := bstep (se 1 (by rfl) ⟨1554440, by rfl⟩ : syracuseStep 2072587 = 3108881) B3108881
theorem B3121213 : Blo 818347 3121213 := bstep (se 3 (by rfl) ⟨585227, by rfl⟩ : syracuseStep 3121213 = 1170455) B1170455
theorem B5906519 : Blo 818347 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B2072729 : Blo 818347 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B10526921 : Blo 818347 10526921 := bstep (se 2 (by rfl) ⟨3947595, by rfl⟩ : syracuseStep 10526921 = 7895191) B7895191
theorem B2334977 : Blo 818347 2334977 := bstep (se 2 (by rfl) ⟨875616, by rfl⟩ : syracuseStep 2334977 = 1751233) B1751233
theorem B2498845 : Blo 818347 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B2105633 : Blo 818347 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B2072891 : Blo 818347 2072891 := bstep (se 1 (by rfl) ⟨1554668, by rfl⟩ : syracuseStep 2072891 = 3109337) B3109337
theorem B5611835 : Blo 818347 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B1384823 : Blo 818347 1384823 := bstep (se 1 (by rfl) ⟨1038617, by rfl⟩ : syracuseStep 1384823 = 2077235) B2077235
theorem B7119251 : Blo 818347 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B1974827 : Blo 818347 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B1843847 : Blo 818347 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B2073235 : Blo 818347 2073235 := bstep (se 1 (by rfl) ⟨1554926, by rfl⟩ : syracuseStep 2073235 = 3109853) B3109853
theorem B3318509 : Blo 818347 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B2073377 : Blo 818347 2073377 := bstep (se 2 (by rfl) ⟨777516, by rfl⟩ : syracuseStep 2073377 = 1555033) B1555033
theorem B5251877 : Blo 818347 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B7021363 : Blo 818347 7021363 := bstep (se 1 (by rfl) ⟨5266022, by rfl⟩ : syracuseStep 7021363 = 10532045) B10532045
theorem B1844027 : Blo 818347 1844027 := bstep (se 1 (by rfl) ⟨1383020, by rfl⟩ : syracuseStep 1844027 = 2766041) B2766041
theorem B1385275 : Blo 818347 1385275 := bstep (se 1 (by rfl) ⟨1038956, by rfl⟩ : syracuseStep 1385275 = 2077913) B2077913
theorem B1844153 : Blo 818347 1844153 := bstep (se 2 (by rfl) ⟨691557, by rfl⟩ : syracuseStep 1844153 = 1383115) B1383115
theorem B1385417 : Blo 818347 1385417 := bstep (se 2 (by rfl) ⟨519531, by rfl⟩ : syracuseStep 1385417 = 1039063) B1039063
theorem B1975241 : Blo 818347 1975241 := bstep (se 2 (by rfl) ⟨740715, by rfl⟩ : syracuseStep 1975241 = 1481431) B1481431
theorem B31532165 : Blo 818347 31532165 := bstep (se 4 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 31532165 = 5912281) B5912281
theorem B1844495 : Blo 818347 1844495 := bstep (se 1 (by rfl) ⟨1383371, by rfl⟩ : syracuseStep 1844495 = 2766743) B2766743
theorem B1844513 : Blo 818347 1844513 := bstep (se 2 (by rfl) ⟨691692, by rfl⟩ : syracuseStep 1844513 = 1383385) B1383385
theorem B2762099 : Blo 818347 2762099 := bstep (se 1 (by rfl) ⟨2071574, by rfl⟩ : syracuseStep 2762099 = 4143149) B4143149
theorem B4662845 : Blo 818347 4662845 := bstep (se 3 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 4662845 = 1748567) B1748567
theorem B1844855 : Blo 818347 1844855 := bstep (se 1 (by rfl) ⟨1383641, by rfl⟩ : syracuseStep 1844855 = 2767283) B2767283
theorem B1386119 : Blo 818347 1386119 := bstep (se 1 (by rfl) ⟨1039589, by rfl⟩ : syracuseStep 1386119 = 2079179) B2079179
theorem B2074369 : Blo 818347 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B2107147 : Blo 818347 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B1845035 : Blo 818347 1845035 := bstep (se 1 (by rfl) ⟨1383776, by rfl⟩ : syracuseStep 1845035 = 2767553) B2767553
theorem B17737541 : Blo 818347 17737541 := bstep (se 4 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 17737541 = 3325789) B3325789
theorem B2336627 : Blo 818347 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1845395 : Blo 818347 1845395 := bstep (se 1 (by rfl) ⟨1384046, by rfl⟩ : syracuseStep 1845395 = 2768093) B2768093
theorem B1845449 : Blo 818347 1845449 := bstep (se 2 (by rfl) ⟨692043, by rfl⟩ : syracuseStep 1845449 = 1384087) B1384087
theorem B1386767 : Blo 818347 1386767 := bstep (se 1 (by rfl) ⟨1040075, by rfl⟩ : syracuseStep 1386767 = 2080151) B2080151
theorem B2337083 : Blo 818347 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B2074967 : Blo 818347 2074967 := bstep (se 1 (by rfl) ⟨1556225, by rfl⟩ : syracuseStep 2074967 = 3112451) B3112451
theorem B2075179 : Blo 818347 2075179 := bstep (se 1 (by rfl) ⟨1556384, by rfl⟩ : syracuseStep 2075179 = 3112769) B3112769
theorem B2075321 : Blo 818347 2075321 := bstep (se 2 (by rfl) ⟨778245, by rfl⟩ : syracuseStep 2075321 = 1556491) B1556491
theorem B7482149 : Blo 818347 7482149 := bstep (se 4 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 7482149 = 1402903) B1402903
theorem B1387307 : Blo 818347 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B1846151 : Blo 818347 1846151 := bstep (se 1 (by rfl) ⟨1384613, by rfl⟩ : syracuseStep 1846151 = 2769227) B2769227
theorem B3156889 : Blo 818347 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B2337835 : Blo 818347 2337835 := bstep (se 1 (by rfl) ⟨1753376, by rfl⟩ : syracuseStep 2337835 = 3506753) B3506753
theorem B7875629 : Blo 818347 7875629 := bstep (se 3 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 7875629 = 2953361) B2953361
theorem B1846331 : Blo 818347 1846331 := bstep (se 1 (by rfl) ⟨1384748, by rfl⟩ : syracuseStep 1846331 = 2769497) B2769497
theorem B5614679 : Blo 818347 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B1846457 : Blo 818347 1846457 := bstep (se 2 (by rfl) ⟨692421, by rfl⟩ : syracuseStep 1846457 = 1384843) B1384843
theorem B1387705 : Blo 818347 1387705 := bstep (se 2 (by rfl) ⟨520389, by rfl⟩ : syracuseStep 1387705 = 1040779) B1040779
theorem B2632961 : Blo 818347 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B2338109 : Blo 818347 2338109 := bstep (se 3 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 2338109 = 876791) B876791
theorem B1846799 : Blo 818347 1846799 := bstep (se 1 (by rfl) ⟨1385099, by rfl⟩ : syracuseStep 1846799 = 2770199) B2770199
theorem B1846817 : Blo 818347 1846817 := bstep (se 2 (by rfl) ⟨692556, by rfl⟩ : syracuseStep 1846817 = 1385113) B1385113
theorem B2666027 : Blo 818347 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B2076313 : Blo 818347 2076313 := bstep (se 2 (by rfl) ⟨778617, by rfl⟩ : syracuseStep 2076313 = 1557235) B1557235
theorem B2076475 : Blo 818347 2076475 := bstep (se 1 (by rfl) ⟨1557356, by rfl⟩ : syracuseStep 2076475 = 3114713) B3114713
theorem B1847159 : Blo 818347 1847159 := bstep (se 1 (by rfl) ⟨1385369, by rfl⟩ : syracuseStep 1847159 = 2770739) B2770739
theorem B4665235 : Blo 818347 4665235 := bstep (se 1 (by rfl) ⟨3498926, by rfl⟩ : syracuseStep 4665235 = 6997853) B6997853
theorem B2764691 : Blo 818347 2764691 := bstep (se 1 (by rfl) ⟨2073518, by rfl⟩ : syracuseStep 2764691 = 4147037) B4147037
theorem B26619799 : Blo 818347 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B2076617 : Blo 818347 2076617 := bstep (se 2 (by rfl) ⟨778731, by rfl⟩ : syracuseStep 2076617 = 1557463) B1557463
theorem B1847339 : Blo 818347 1847339 := bstep (se 1 (by rfl) ⟨1385504, by rfl⟩ : syracuseStep 1847339 = 2771009) B2771009
theorem B6238295 : Blo 818347 6238295 := bstep (se 1 (by rfl) ⟨4678721, by rfl⟩ : syracuseStep 6238295 = 9357443) B9357443
theorem B2338951 : Blo 818347 2338951 := bstep (se 1 (by rfl) ⟨1754213, by rfl⟩ : syracuseStep 2338951 = 3508427) B3508427
theorem B2076961 : Blo 818347 2076961 := bstep (se 2 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 2076961 = 1557721) B1557721
theorem B4993331 : Blo 818347 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B1749395 : Blo 818347 1749395 := bstep (se 1 (by rfl) ⟨1312046, by rfl⟩ : syracuseStep 1749395 = 2624093) B2624093
theorem B1847699 : Blo 818347 1847699 := bstep (se 1 (by rfl) ⟨1385774, by rfl⟩ : syracuseStep 1847699 = 2771549) B2771549
theorem B2339225 : Blo 818347 2339225 := bstep (se 2 (by rfl) ⟨877209, by rfl⟩ : syracuseStep 2339225 = 1754419) B1754419
theorem B1847753 : Blo 818347 1847753 := bstep (se 2 (by rfl) ⟨692907, by rfl⟩ : syracuseStep 1847753 = 1385815) B1385815
theorem B3944983 : Blo 818347 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B4993793 : Blo 818347 4993793 := bstep (se 2 (by rfl) ⟨1872672, by rfl⟩ : syracuseStep 4993793 = 3745345) B3745345
theorem B6992729 : Blo 818347 6992729 := bstep (se 2 (by rfl) ⟨2622273, by rfl⟩ : syracuseStep 6992729 = 5244547) B5244547
theorem B2077559 : Blo 818347 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B1848455 : Blo 818347 1848455 := bstep (se 1 (by rfl) ⟨1386341, by rfl⟩ : syracuseStep 1848455 = 2772683) B2772683
theorem B2766095 : Blo 818347 2766095 := bstep (se 1 (by rfl) ⟨2074571, by rfl⟩ : syracuseStep 2766095 = 4149143) B4149143
theorem B1848635 : Blo 818347 1848635 := bstep (se 1 (by rfl) ⟨1386476, by rfl⟩ : syracuseStep 1848635 = 2772953) B2772953
theorem B2405693 : Blo 818347 2405693 := bstep (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) B902135
theorem B39892337 : Blo 818347 39892337 := bstep (se 2 (by rfl) ⟨14959626, by rfl⟩ : syracuseStep 39892337 = 29919253) B29919253
theorem B1848761 : Blo 818347 1848761 := bstep (se 2 (by rfl) ⟨693285, by rfl⟩ : syracuseStep 1848761 = 1386571) B1386571
theorem B2340353 : Blo 818347 2340353 := bstep (se 2 (by rfl) ⟨877632, by rfl⟩ : syracuseStep 2340353 = 1755265) B1755265
theorem B2766365 : Blo 818347 2766365 := bstep (se 3 (by rfl) ⟨518693, by rfl⟩ : syracuseStep 2766365 = 1037387) B1037387
theorem B4666967 : Blo 818347 4666967 := bstep (se 1 (by rfl) ⟨3500225, by rfl⟩ : syracuseStep 4666967 = 7000451) B7000451
theorem B1849103 : Blo 818347 1849103 := bstep (se 1 (by rfl) ⟨1386827, by rfl⟩ : syracuseStep 1849103 = 2773655) B2773655
theorem B1849121 : Blo 818347 1849121 := bstep (se 2 (by rfl) ⟨693420, by rfl⟩ : syracuseStep 1849121 = 1386841) B1386841
theorem B2340809 : Blo 818347 2340809 := bstep (se 2 (by rfl) ⟨877803, by rfl⟩ : syracuseStep 2340809 = 1755607) B1755607
theorem B4732951 : Blo 818347 4732951 := bstep (se 1 (by rfl) ⟨3549713, by rfl⟩ : syracuseStep 4732951 = 7099427) B7099427
theorem B2799677 : Blo 818347 2799677 := bstep (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) B1049879
theorem B1849463 : Blo 818347 1849463 := bstep (se 1 (by rfl) ⟨1387097, by rfl⟩ : syracuseStep 1849463 = 2774195) B2774195
theorem B2078855 : Blo 818347 2078855 := bstep (se 1 (by rfl) ⟨1559141, by rfl⟩ : syracuseStep 2078855 = 3118283) B3118283
theorem B2078905 : Blo 818347 2078905 := bstep (se 2 (by rfl) ⟨779589, by rfl⟩ : syracuseStep 2078905 = 1559179) B1559179
theorem B1849643 : Blo 818347 1849643 := bstep (se 1 (by rfl) ⟨1387232, by rfl⟩ : syracuseStep 1849643 = 2774465) B2774465
theorem B1554889 : Blo 818347 1554889 := bstep (se 2 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 1554889 = 1166167) B1166167
theorem B1850003 : Blo 818347 1850003 := bstep (se 1 (by rfl) ⟨1387502, by rfl⟩ : syracuseStep 1850003 = 2775005) B2775005
theorem B1751753 : Blo 818347 1751753 := bstep (se 2 (by rfl) ⟨656907, by rfl⟩ : syracuseStep 1751753 = 1313815) B1313815
theorem B1850057 : Blo 818347 1850057 := bstep (se 2 (by rfl) ⟨693771, by rfl⟩ : syracuseStep 1850057 = 1387543) B1387543
theorem B3750637 : Blo 818347 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B9124609 : Blo 818347 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B1227527 : Blo 818347 1227527 := bstep (se 1 (by rfl) ⟨920645, by rfl⟩ : syracuseStep 1227527 = 1841291) B1841291
theorem B2079503 : Blo 818347 2079503 := bstep (se 1 (by rfl) ⟨1559627, by rfl⟩ : syracuseStep 2079503 = 3119255) B3119255
theorem B1227563 : Blo 818347 1227563 := bstep (se 1 (by rfl) ⟨920672, by rfl⟩ : syracuseStep 1227563 = 1841345) B1841345
theorem B1227593 : Blo 818347 1227593 := bstep (se 2 (by rfl) ⟨460347, by rfl⟩ : syracuseStep 1227593 = 920695) B920695
theorem B4504409 : Blo 818347 4504409 := bstep (se 2 (by rfl) ⟨1689153, by rfl⟩ : syracuseStep 4504409 = 3378307) B3378307
theorem B2767769 : Blo 818347 2767769 := bstep (se 2 (by rfl) ⟨1037913, by rfl⟩ : syracuseStep 2767769 = 2075827) B2075827
theorem B1227707 : Blo 818347 1227707 := bstep (se 1 (by rfl) ⟨920780, by rfl⟩ : syracuseStep 1227707 = 1841561) B1841561
theorem B1227767 : Blo 818347 1227767 := bstep (se 1 (by rfl) ⟨920825, by rfl⟩ : syracuseStep 1227767 = 1841651) B1841651
theorem B11222021 : Blo 818347 11222021 := bstep (se 4 (by rfl) ⟨1052064, by rfl⟩ : syracuseStep 11222021 = 2104129) B2104129
theorem B1227791 : Blo 818347 1227791 := bstep (se 1 (by rfl) ⟨920843, by rfl⟩ : syracuseStep 1227791 = 1841687) B1841687
theorem B1227833 : Blo 818347 1227833 := bstep (se 2 (by rfl) ⟨460437, by rfl⟩ : syracuseStep 1227833 = 920875) B920875
theorem B1227911 : Blo 818347 1227911 := bstep (se 1 (by rfl) ⟨920933, by rfl⟩ : syracuseStep 1227911 = 1841867) B1841867
theorem B1227947 : Blo 818347 1227947 := bstep (se 1 (by rfl) ⟨920960, by rfl⟩ : syracuseStep 1227947 = 1841921) B1841921
theorem B1227977 : Blo 818347 1227977 := bstep (se 2 (by rfl) ⟨460491, by rfl⟩ : syracuseStep 1227977 = 920983) B920983
theorem B1228091 : Blo 818347 1228091 := bstep (se 1 (by rfl) ⟨921068, by rfl⟩ : syracuseStep 1228091 = 1842137) B1842137
theorem B1228151 : Blo 818347 1228151 := bstep (se 1 (by rfl) ⟨921113, by rfl⟩ : syracuseStep 1228151 = 1842227) B1842227
theorem B1228175 : Blo 818347 1228175 := bstep (se 1 (by rfl) ⟨921131, by rfl⟩ : syracuseStep 1228175 = 1842263) B1842263
theorem B1228217 : Blo 818347 1228217 := bstep (se 2 (by rfl) ⟨460581, by rfl⟩ : syracuseStep 1228217 = 921163) B921163
theorem B2080201 : Blo 818347 2080201 := bstep (se 2 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 2080201 = 1560151) B1560151
theorem B1228295 : Blo 818347 1228295 := bstep (se 1 (by rfl) ⟨921221, by rfl⟩ : syracuseStep 1228295 = 1842443) B1842443
theorem B1228331 : Blo 818347 1228331 := bstep (se 1 (by rfl) ⟨921248, by rfl⟩ : syracuseStep 1228331 = 1842497) B1842497
theorem B1228361 : Blo 818347 1228361 := bstep (se 2 (by rfl) ⟨460635, by rfl⟩ : syracuseStep 1228361 = 921271) B921271
theorem B2768471 : Blo 818347 2768471 := bstep (se 1 (by rfl) ⟨2076353, by rfl⟩ : syracuseStep 2768471 = 4152707) B4152707
theorem B2080343 : Blo 818347 2080343 := bstep (se 1 (by rfl) ⟨1560257, by rfl⟩ : syracuseStep 2080343 = 3120515) B3120515
theorem B1228475 : Blo 818347 1228475 := bstep (se 1 (by rfl) ⟨921356, by rfl⟩ : syracuseStep 1228475 = 1842713) B1842713
theorem B1228535 : Blo 818347 1228535 := bstep (se 1 (by rfl) ⟨921401, by rfl⟩ : syracuseStep 1228535 = 1842803) B1842803
theorem B1228559 : Blo 818347 1228559 := bstep (se 1 (by rfl) ⟨921419, by rfl⟩ : syracuseStep 1228559 = 1842839) B1842839
theorem B1228601 : Blo 818347 1228601 := bstep (se 2 (by rfl) ⟨460725, by rfl⟩ : syracuseStep 1228601 = 921451) B921451
theorem B1228679 : Blo 818347 1228679 := bstep (se 1 (by rfl) ⟨921509, by rfl⟩ : syracuseStep 1228679 = 1843019) B1843019
theorem B1228715 : Blo 818347 1228715 := bstep (se 1 (by rfl) ⟨921536, by rfl⟩ : syracuseStep 1228715 = 1843073) B1843073
theorem B1228745 : Blo 818347 1228745 := bstep (se 2 (by rfl) ⟨460779, by rfl⟩ : syracuseStep 1228745 = 921559) B921559
theorem B1753103 : Blo 818347 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B1228859 : Blo 818347 1228859 := bstep (se 1 (by rfl) ⟨921644, by rfl⟩ : syracuseStep 1228859 = 1843289) B1843289
theorem B2768957 : Blo 818347 2768957 := bstep (se 3 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 2768957 = 1038359) B1038359
theorem B1228919 : Blo 818347 1228919 := bstep (se 1 (by rfl) ⟨921689, by rfl⟩ : syracuseStep 1228919 = 1843379) B1843379
theorem B1228943 : Blo 818347 1228943 := bstep (se 1 (by rfl) ⟨921707, by rfl⟩ : syracuseStep 1228943 = 1843415) B1843415
theorem B1228985 : Blo 818347 1228985 := bstep (se 2 (by rfl) ⟨460869, by rfl⟩ : syracuseStep 1228985 = 921739) B921739
theorem B1229063 : Blo 818347 1229063 := bstep (se 1 (by rfl) ⟨921797, by rfl⟩ : syracuseStep 1229063 = 1843595) B1843595
theorem B1229099 : Blo 818347 1229099 := bstep (se 1 (by rfl) ⟨921824, by rfl⟩ : syracuseStep 1229099 = 1843649) B1843649
theorem B1556795 : Blo 818347 1556795 := bstep (se 1 (by rfl) ⟨1167596, by rfl⟩ : syracuseStep 1556795 = 2335193) B2335193
theorem B1229129 : Blo 818347 1229129 := bstep (se 2 (by rfl) ⟨460923, by rfl⟩ : syracuseStep 1229129 = 921847) B921847
theorem B5259667 : Blo 818347 5259667 := bstep (se 1 (by rfl) ⟨3944750, by rfl⟩ : syracuseStep 5259667 = 7889501) B7889501
theorem B1229243 : Blo 818347 1229243 := bstep (se 1 (by rfl) ⟨921932, by rfl⟩ : syracuseStep 1229243 = 1843865) B1843865
theorem B1229303 : Blo 818347 1229303 := bstep (se 1 (by rfl) ⟨921977, by rfl⟩ : syracuseStep 1229303 = 1843955) B1843955
theorem B1229327 : Blo 818347 1229327 := bstep (se 1 (by rfl) ⟨921995, by rfl⟩ : syracuseStep 1229327 = 1843991) B1843991
theorem B1229369 : Blo 818347 1229369 := bstep (se 2 (by rfl) ⟨461013, by rfl⟩ : syracuseStep 1229369 = 922027) B922027
theorem B1229447 : Blo 818347 1229447 := bstep (se 1 (by rfl) ⟨922085, by rfl⟩ : syracuseStep 1229447 = 1844171) B1844171
theorem B1229483 : Blo 818347 1229483 := bstep (se 1 (by rfl) ⟨922112, by rfl⟩ : syracuseStep 1229483 = 1844225) B1844225
theorem B1229513 : Blo 818347 1229513 := bstep (se 2 (by rfl) ⟨461067, by rfl⟩ : syracuseStep 1229513 = 922135) B922135
theorem B2212609 : Blo 818347 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B1557281 : Blo 818347 1557281 := bstep (se 2 (by rfl) ⟨583980, by rfl⟩ : syracuseStep 1557281 = 1167961) B1167961
theorem B1229627 : Blo 818347 1229627 := bstep (se 1 (by rfl) ⟨922220, by rfl⟩ : syracuseStep 1229627 = 1844441) B1844441
theorem B1229687 : Blo 818347 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1229711 : Blo 818347 1229711 := bstep (se 1 (by rfl) ⟨922283, by rfl⟩ : syracuseStep 1229711 = 1844567) B1844567
theorem B4146065 : Blo 818347 4146065 := bstep (se 2 (by rfl) ⟨1554774, by rfl⟩ : syracuseStep 4146065 = 3109549) B3109549
theorem B1229753 : Blo 818347 1229753 := bstep (se 2 (by rfl) ⟨461157, by rfl⟩ : syracuseStep 1229753 = 922315) B922315
theorem B1229831 : Blo 818347 1229831 := bstep (se 1 (by rfl) ⟨922373, by rfl⟩ : syracuseStep 1229831 = 1844747) B1844747
theorem B1229867 : Blo 818347 1229867 := bstep (se 1 (by rfl) ⟨922400, by rfl⟩ : syracuseStep 1229867 = 1844801) B1844801
theorem B1229897 : Blo 818347 1229897 := bstep (se 2 (by rfl) ⟨461211, by rfl⟩ : syracuseStep 1229897 = 922423) B922423
theorem B1557623 : Blo 818347 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B1230011 : Blo 818347 1230011 := bstep (se 1 (by rfl) ⟨922508, by rfl⟩ : syracuseStep 1230011 = 1845017) B1845017
theorem B1230071 : Blo 818347 1230071 := bstep (se 1 (by rfl) ⟨922553, by rfl⟩ : syracuseStep 1230071 = 1845107) B1845107
theorem B3949825 : Blo 818347 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B1230095 : Blo 818347 1230095 := bstep (se 1 (by rfl) ⟨922571, by rfl⟩ : syracuseStep 1230095 = 1845143) B1845143
theorem B1230137 : Blo 818347 1230137 := bstep (se 2 (by rfl) ⟨461301, by rfl⟩ : syracuseStep 1230137 = 922603) B922603
theorem B1230215 : Blo 818347 1230215 := bstep (se 1 (by rfl) ⟨922661, by rfl⟩ : syracuseStep 1230215 = 1845323) B1845323
theorem B1230251 : Blo 818347 1230251 := bstep (se 1 (by rfl) ⟨922688, by rfl⟩ : syracuseStep 1230251 = 1845377) B1845377
theorem B40519091 : Blo 818347 40519091 := bstep (se 1 (by rfl) ⟨30389318, by rfl⟩ : syracuseStep 40519091 = 60778637) B60778637
theorem B2770361 : Blo 818347 2770361 := bstep (se 2 (by rfl) ⟨1038885, by rfl⟩ : syracuseStep 2770361 = 2077771) B2077771
theorem B1230281 : Blo 818347 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B2213387 : Blo 818347 2213387 := bstep (se 1 (by rfl) ⟨1660040, by rfl⟩ : syracuseStep 2213387 = 3320081) B3320081
theorem B1230395 : Blo 818347 1230395 := bstep (se 1 (by rfl) ⟨922796, by rfl⟩ : syracuseStep 1230395 = 1845593) B1845593
theorem B1230455 : Blo 818347 1230455 := bstep (se 1 (by rfl) ⟨922841, by rfl⟩ : syracuseStep 1230455 = 1845683) B1845683
theorem B1230479 : Blo 818347 1230479 := bstep (se 1 (by rfl) ⟨922859, by rfl⟩ : syracuseStep 1230479 = 1845719) B1845719
theorem B1230521 : Blo 818347 1230521 := bstep (se 2 (by rfl) ⟨461445, by rfl⟩ : syracuseStep 1230521 = 922891) B922891
theorem B1230599 : Blo 818347 1230599 := bstep (se 1 (by rfl) ⟨922949, by rfl⟩ : syracuseStep 1230599 = 1845899) B1845899
theorem B1230635 : Blo 818347 1230635 := bstep (se 1 (by rfl) ⟨922976, by rfl⟩ : syracuseStep 1230635 = 1845953) B1845953
theorem B1230665 : Blo 818347 1230665 := bstep (se 2 (by rfl) ⟨461499, by rfl⟩ : syracuseStep 1230665 = 922999) B922999
theorem B1001359 : Blo 818347 1001359 := bstep (se 1 (by rfl) ⟨751019, by rfl⟩ : syracuseStep 1001359 = 1502039) B1502039
theorem B1230779 : Blo 818347 1230779 := bstep (se 1 (by rfl) ⟨923084, by rfl⟩ : syracuseStep 1230779 = 1846169) B1846169
theorem B1230839 : Blo 818347 1230839 := bstep (se 1 (by rfl) ⟨923129, by rfl⟩ : syracuseStep 1230839 = 1846259) B1846259
theorem B2770955 : Blo 818347 2770955 := bstep (se 1 (by rfl) ⟨2078216, by rfl⟩ : syracuseStep 2770955 = 4156433) B4156433
theorem B1230863 : Blo 818347 1230863 := bstep (se 1 (by rfl) ⟨923147, by rfl⟩ : syracuseStep 1230863 = 1846295) B1846295
theorem B1230905 : Blo 818347 1230905 := bstep (se 2 (by rfl) ⟨461589, by rfl⟩ : syracuseStep 1230905 = 923179) B923179
theorem B2771063 : Blo 818347 2771063 := bstep (se 1 (by rfl) ⟨2078297, by rfl⟩ : syracuseStep 2771063 = 4156595) B4156595
theorem B1230983 : Blo 818347 1230983 := bstep (se 1 (by rfl) ⟨923237, by rfl⟩ : syracuseStep 1230983 = 1846475) B1846475
theorem B1231019 : Blo 818347 1231019 := bstep (se 1 (by rfl) ⟨923264, by rfl⟩ : syracuseStep 1231019 = 1846529) B1846529
theorem B1231049 : Blo 818347 1231049 := bstep (se 2 (by rfl) ⟨461643, by rfl⟩ : syracuseStep 1231049 = 923287) B923287
theorem B1231163 : Blo 818347 1231163 := bstep (se 1 (by rfl) ⟨923372, by rfl⟩ : syracuseStep 1231163 = 1846745) B1846745
theorem B1231223 : Blo 818347 1231223 := bstep (se 1 (by rfl) ⟨923417, by rfl⟩ : syracuseStep 1231223 = 1846835) B1846835
theorem B1231247 : Blo 818347 1231247 := bstep (se 1 (by rfl) ⟨923435, by rfl⟩ : syracuseStep 1231247 = 1846871) B1846871
theorem B1231289 : Blo 818347 1231289 := bstep (se 2 (by rfl) ⟨461733, by rfl⟩ : syracuseStep 1231289 = 923467) B923467
theorem B1231367 : Blo 818347 1231367 := bstep (se 1 (by rfl) ⟨923525, by rfl⟩ : syracuseStep 1231367 = 1847051) B1847051
theorem B2214415 : Blo 818347 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B1231403 : Blo 818347 1231403 := bstep (se 1 (by rfl) ⟨923552, by rfl⟩ : syracuseStep 1231403 = 1847105) B1847105
theorem B1231433 : Blo 818347 1231433 := bstep (se 2 (by rfl) ⟨461787, by rfl⟩ : syracuseStep 1231433 = 923575) B923575
theorem B2214535 : Blo 818347 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B1559225 : Blo 818347 1559225 := bstep (se 2 (by rfl) ⟨584709, by rfl⟩ : syracuseStep 1559225 = 1169419) B1169419
theorem B1231547 : Blo 818347 1231547 := bstep (se 1 (by rfl) ⟨923660, by rfl⟩ : syracuseStep 1231547 = 1847321) B1847321
theorem B5065409 : Blo 818347 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B2771657 : Blo 818347 2771657 := bstep (se 2 (by rfl) ⟨1039371, by rfl⟩ : syracuseStep 2771657 = 2078743) B2078743
theorem B1231607 : Blo 818347 1231607 := bstep (se 1 (by rfl) ⟨923705, by rfl⟩ : syracuseStep 1231607 = 1847411) B1847411
theorem B1231631 : Blo 818347 1231631 := bstep (se 1 (by rfl) ⟨923723, by rfl⟩ : syracuseStep 1231631 = 1847447) B1847447
theorem B1231673 : Blo 818347 1231673 := bstep (se 2 (by rfl) ⟨461877, by rfl⟩ : syracuseStep 1231673 = 923755) B923755
theorem B1231751 : Blo 818347 1231751 := bstep (se 1 (by rfl) ⟨923813, by rfl⟩ : syracuseStep 1231751 = 1847627) B1847627
theorem B1231787 : Blo 818347 1231787 := bstep (se 1 (by rfl) ⟨923840, by rfl⟩ : syracuseStep 1231787 = 1847681) B1847681
theorem B1231817 : Blo 818347 1231817 := bstep (se 2 (by rfl) ⟨461931, by rfl⟩ : syracuseStep 1231817 = 923863) B923863
theorem B4148171 : Blo 818347 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B1559567 : Blo 818347 1559567 := bstep (se 1 (by rfl) ⟨1169675, by rfl⟩ : syracuseStep 1559567 = 2339351) B2339351
theorem B1166395 : Blo 818347 1166395 := bstep (se 1 (by rfl) ⟨874796, by rfl⟩ : syracuseStep 1166395 = 1749593) B1749593
theorem B1231931 : Blo 818347 1231931 := bstep (se 1 (by rfl) ⟨923948, by rfl⟩ : syracuseStep 1231931 = 1847897) B1847897
theorem B1231991 : Blo 818347 1231991 := bstep (se 1 (by rfl) ⟨923993, by rfl⟩ : syracuseStep 1231991 = 1847987) B1847987
theorem B1232015 : Blo 818347 1232015 := bstep (se 1 (by rfl) ⟨924011, by rfl⟩ : syracuseStep 1232015 = 1848023) B1848023
theorem B35540117 : Blo 818347 35540117 := bstep (se 6 (by rfl) ⟨832971, by rfl⟩ : syracuseStep 35540117 = 1665943) B1665943
theorem B1232057 : Blo 818347 1232057 := bstep (se 2 (by rfl) ⟨462021, by rfl⟩ : syracuseStep 1232057 = 924043) B924043
theorem B1232135 : Blo 818347 1232135 := bstep (se 1 (by rfl) ⟨924101, by rfl⟩ : syracuseStep 1232135 = 1848203) B1848203
theorem B4148495 : Blo 818347 4148495 := bstep (se 1 (by rfl) ⟨3111371, by rfl⟩ : syracuseStep 4148495 = 6222743) B6222743
theorem B1232171 : Blo 818347 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B1232201 : Blo 818347 1232201 := bstep (se 2 (by rfl) ⟨462075, by rfl⟩ : syracuseStep 1232201 = 924151) B924151
theorem B2772359 : Blo 818347 2772359 := bstep (se 1 (by rfl) ⟨2079269, by rfl⟩ : syracuseStep 2772359 = 4158539) B4158539
theorem B1232315 : Blo 818347 1232315 := bstep (se 1 (by rfl) ⟨924236, by rfl⟩ : syracuseStep 1232315 = 1848473) B1848473
theorem B1035767 : Blo 818347 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B1232375 : Blo 818347 1232375 := bstep (se 1 (by rfl) ⟨924281, by rfl⟩ : syracuseStep 1232375 = 1848563) B1848563
theorem B1232399 : Blo 818347 1232399 := bstep (se 1 (by rfl) ⟨924299, by rfl⟩ : syracuseStep 1232399 = 1848599) B1848599
theorem B1232441 : Blo 818347 1232441 := bstep (se 2 (by rfl) ⟨462165, by rfl⟩ : syracuseStep 1232441 = 924331) B924331
theorem B1232519 : Blo 818347 1232519 := bstep (se 1 (by rfl) ⟨924389, by rfl⟩ : syracuseStep 1232519 = 1848779) B1848779
theorem B1035919 : Blo 818347 1035919 := bstep (se 1 (by rfl) ⟨776939, by rfl⟩ : syracuseStep 1035919 = 1553879) B1553879
theorem B1232555 : Blo 818347 1232555 := bstep (se 1 (by rfl) ⟨924416, by rfl⟩ : syracuseStep 1232555 = 1848833) B1848833
theorem B1232585 : Blo 818347 1232585 := bstep (se 2 (by rfl) ⟨462219, by rfl⟩ : syracuseStep 1232585 = 924439) B924439
theorem B1167095 : Blo 818347 1167095 := bstep (se 1 (by rfl) ⟨875321, by rfl⟩ : syracuseStep 1167095 = 1750643) B1750643
theorem B2772737 : Blo 818347 2772737 := bstep (se 2 (by rfl) ⟨1039776, by rfl⟩ : syracuseStep 2772737 = 2079553) B2079553
theorem B1036091 : Blo 818347 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B1232699 : Blo 818347 1232699 := bstep (se 1 (by rfl) ⟨924524, by rfl⟩ : syracuseStep 1232699 = 1849049) B1849049
theorem B1560379 : Blo 818347 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B1232759 : Blo 818347 1232759 := bstep (se 1 (by rfl) ⟨924569, by rfl⟩ : syracuseStep 1232759 = 1849139) B1849139
theorem B1560455 : Blo 818347 1560455 := bstep (se 1 (by rfl) ⟨1170341, by rfl⟩ : syracuseStep 1560455 = 2340683) B2340683
theorem B1232783 : Blo 818347 1232783 := bstep (se 1 (by rfl) ⟨924587, by rfl⟩ : syracuseStep 1232783 = 1849175) B1849175
theorem B1232825 : Blo 818347 1232825 := bstep (se 2 (by rfl) ⟨462309, by rfl⟩ : syracuseStep 1232825 = 924619) B924619
theorem B4673483 : Blo 818347 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B1232903 : Blo 818347 1232903 := bstep (se 1 (by rfl) ⟨924677, by rfl⟩ : syracuseStep 1232903 = 1849355) B1849355
theorem B1232939 : Blo 818347 1232939 := bstep (se 1 (by rfl) ⟨924704, by rfl⟩ : syracuseStep 1232939 = 1849409) B1849409
theorem B1232969 : Blo 818347 1232969 := bstep (se 2 (by rfl) ⟨462363, by rfl⟩ : syracuseStep 1232969 = 924727) B924727
theorem B4444247 : Blo 818347 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B1233083 : Blo 818347 1233083 := bstep (se 1 (by rfl) ⟨924812, by rfl⟩ : syracuseStep 1233083 = 1849625) B1849625
theorem B1233143 : Blo 818347 1233143 := bstep (se 1 (by rfl) ⟨924857, by rfl⟩ : syracuseStep 1233143 = 1849715) B1849715
theorem B1233167 : Blo 818347 1233167 := bstep (se 1 (by rfl) ⟨924875, by rfl⟩ : syracuseStep 1233167 = 1849751) B1849751
theorem B1560865 : Blo 818347 1560865 := bstep (se 2 (by rfl) ⟨585324, by rfl⟩ : syracuseStep 1560865 = 1170649) B1170649
theorem B1265977 : Blo 818347 1265977 := bstep (se 2 (by rfl) ⟨474741, by rfl⟩ : syracuseStep 1265977 = 949483) B949483
theorem B1233209 : Blo 818347 1233209 := bstep (se 2 (by rfl) ⟨462453, by rfl⟩ : syracuseStep 1233209 = 924907) B924907
theorem B1233287 : Blo 818347 1233287 := bstep (se 1 (by rfl) ⟨924965, by rfl⟩ : syracuseStep 1233287 = 1849931) B1849931
theorem B1233323 : Blo 818347 1233323 := bstep (se 1 (by rfl) ⟨924992, by rfl⟩ : syracuseStep 1233323 = 1849985) B1849985
theorem B1233353 : Blo 818347 1233353 := bstep (se 2 (by rfl) ⟨462507, by rfl⟩ : syracuseStep 1233353 = 925015) B925015
theorem B2773547 : Blo 818347 2773547 := bstep (se 1 (by rfl) ⟨2080160, by rfl⟩ : syracuseStep 2773547 = 4160321) B4160321
theorem B1233467 : Blo 818347 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B4149953 : Blo 818347 4149953 := bstep (se 2 (by rfl) ⟨1556232, by rfl⟩ : syracuseStep 4149953 = 3112465) B3112465
theorem B1037063 : Blo 818347 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B12636965 : Blo 818347 12636965 := bstep (se 4 (by rfl) ⟨1184715, by rfl⟩ : syracuseStep 12636965 = 2369431) B2369431
theorem B3888017 : Blo 818347 3888017 := bstep (se 2 (by rfl) ⟨1458006, by rfl⟩ : syracuseStep 3888017 = 2916013) B2916013
theorem B5919641 : Blo 818347 5919641 := bstep (se 2 (by rfl) ⟨2219865, by rfl⟩ : syracuseStep 5919641 = 4439731) B4439731
theorem B19190789 : Blo 818347 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B1168519 : Blo 818347 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B1660105 : Blo 818347 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B1037711 : Blo 818347 1037711 := bstep (se 1 (by rfl) ⟨778283, by rfl⟩ : syracuseStep 1037711 = 1556567) B1556567
theorem B10507805 : Blo 818347 10507805 := bstep (se 3 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 10507805 = 3940427) B3940427
theorem B23025329 : Blo 818347 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B1169083 : Blo 818347 1169083 := bstep (se 1 (by rfl) ⟨876812, by rfl⟩ : syracuseStep 1169083 = 1753625) B1753625
theorem B2774843 : Blo 818347 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B1660819 : Blo 818347 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B4151249 : Blo 818347 4151249 := bstep (se 2 (by rfl) ⟨1556718, by rfl⟩ : syracuseStep 4151249 = 3113437) B3113437
theorem B2217995 : Blo 818347 2217995 := bstep (se 1 (by rfl) ⟨1663496, by rfl⟩ : syracuseStep 2217995 = 3326993) B3326993
theorem B31610897 : Blo 818347 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B3496193 : Blo 818347 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B841999 : Blo 818347 841999 := bstep (se 1 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 841999 = 1262999) B1262999
theorem B6314273 : Blo 818347 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B2775329 : Blo 818347 2775329 := bstep (se 2 (by rfl) ⟨1040748, by rfl⟩ : syracuseStep 2775329 = 2081497) B2081497
theorem B5626259 : Blo 818347 5626259 := bstep (se 1 (by rfl) ⟨4219694, by rfl⟩ : syracuseStep 5626259 = 8439389) B8439389
theorem B1169977 : Blo 818347 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B4742003 : Blo 818347 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B42589091 : Blo 818347 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B875791 : Blo 818347 875791 := bstep (se 1 (by rfl) ⟨656843, by rfl⟩ : syracuseStep 875791 = 1313687) B1313687
theorem B3366203 : Blo 818347 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B7888427 : Blo 818347 7888427 := bstep (se 1 (by rfl) ⟨5916320, by rfl⟩ : syracuseStep 7888427 = 11832641) B11832641
theorem B9363275 : Blo 818347 9363275 := bstep (se 1 (by rfl) ⟨7022456, by rfl⟩ : syracuseStep 9363275 = 14044913) B14044913
theorem B4153355 : Blo 818347 4153355 := bstep (se 1 (by rfl) ⟨3115016, by rfl⟩ : syracuseStep 4153355 = 6230033) B6230033
theorem B4153517 : Blo 818347 4153517 := bstep (se 3 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 4153517 = 1557569) B1557569
theorem B1040683 : Blo 818347 1040683 := bstep (se 1 (by rfl) ⟨780512, by rfl⟩ : syracuseStep 1040683 = 1561025) B1561025
theorem B1663673 : Blo 818347 1663673 := bstep (se 2 (by rfl) ⟨623877, by rfl⟩ : syracuseStep 1663673 = 1247755) B1247755
theorem B2221085 : Blo 818347 2221085 := bstep (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) B832907
theorem B6219341 : Blo 818347 6219341 := bstep (se 3 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 6219341 = 2332253) B2332253
theorem B10643021 : Blo 818347 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B4155137 : Blo 818347 4155137 := bstep (se 2 (by rfl) ⟨1558176, by rfl⟩ : syracuseStep 4155137 = 3116353) B3116353
theorem B4679633 : Blo 818347 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B4680089 : Blo 818347 4680089 := bstep (se 2 (by rfl) ⟨1755033, by rfl⟩ : syracuseStep 4680089 = 3510067) B3510067
theorem B4155947 : Blo 818347 4155947 := bstep (se 1 (by rfl) ⟨3116960, by rfl⟩ : syracuseStep 4155947 = 6233921) B6233921
theorem B12479321 : Blo 818347 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B1403849 : Blo 818347 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B3108077 : Blo 818347 3108077 := bstep (se 3 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 3108077 = 1165529) B1165529
theorem B10513799 : Blo 818347 10513799 := bstep (se 1 (by rfl) ⟨7885349, by rfl⟩ : syracuseStep 10513799 = 15770699) B15770699
theorem B3108395 : Blo 818347 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B5336833 : Blo 818347 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B1109819 : Blo 818347 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B4157243 : Blo 818347 4157243 := bstep (se 1 (by rfl) ⟨3117932, by rfl⟩ : syracuseStep 4157243 = 6235865) B6235865
theorem B6221771 : Blo 818347 6221771 := bstep (se 1 (by rfl) ⟨4666328, by rfl⟩ : syracuseStep 6221771 = 9332657) B9332657
theorem B4157405 : Blo 818347 4157405 := bstep (se 3 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 4157405 = 1559027) B1559027
theorem B4157729 : Blo 818347 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B4158701 : Blo 818347 4158701 := bstep (se 3 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 4158701 = 1559513) B1559513
theorem B21034565 : Blo 818347 21034565 := bstep (se 4 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 21034565 = 3943981) B3943981
theorem B3504019 : Blo 818347 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B7993367 : Blo 818347 7993367 := bstep (se 1 (by rfl) ⟨5995025, by rfl⟩ : syracuseStep 7993367 = 11990051) B11990051
theorem B4159511 : Blo 818347 4159511 := bstep (se 1 (by rfl) ⟨3119633, by rfl⟩ : syracuseStep 4159511 = 6239267) B6239267
theorem B3111965 : Blo 818347 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B3111979 : Blo 818347 3111979 := bstep (se 1 (by rfl) ⟨2333984, by rfl⟩ : syracuseStep 3111979 = 4667969) B4667969
theorem B818363 : Blo 818347 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B818439 : Blo 818347 818439 := bstep (se 1 (by rfl) ⟨613829, by rfl⟩ : syracuseStep 818439 = 1227659) B1227659
theorem B818447 : Blo 818347 818447 := bstep (se 1 (by rfl) ⟨613835, by rfl⟩ : syracuseStep 818447 = 1227671) B1227671
theorem B818491 : Blo 818347 818491 := bstep (se 1 (by rfl) ⟨613868, by rfl⟩ : syracuseStep 818491 = 1227737) B1227737
theorem B818567 : Blo 818347 818567 := bstep (se 1 (by rfl) ⟨613925, by rfl⟩ : syracuseStep 818567 = 1227851) B1227851
theorem B818575 : Blo 818347 818575 := bstep (se 1 (by rfl) ⟨613931, by rfl⟩ : syracuseStep 818575 = 1227863) B1227863
theorem B818619 : Blo 818347 818619 := bstep (se 1 (by rfl) ⟨613964, by rfl⟩ : syracuseStep 818619 = 1227929) B1227929
theorem B818695 : Blo 818347 818695 := bstep (se 1 (by rfl) ⟨614021, by rfl⟩ : syracuseStep 818695 = 1228043) B1228043
theorem B818703 : Blo 818347 818703 := bstep (se 1 (by rfl) ⟨614027, by rfl⟩ : syracuseStep 818703 = 1228055) B1228055
theorem B3505693 : Blo 818347 3505693 := bstep (se 3 (by rfl) ⟨657317, by rfl⟩ : syracuseStep 3505693 = 1314635) B1314635
theorem B818747 : Blo 818347 818747 := bstep (se 1 (by rfl) ⟨614060, by rfl⟩ : syracuseStep 818747 = 1228121) B1228121
theorem B818823 : Blo 818347 818823 := bstep (se 1 (by rfl) ⟨614117, by rfl⟩ : syracuseStep 818823 = 1228235) B1228235
theorem B818831 : Blo 818347 818831 := bstep (se 1 (by rfl) ⟨614123, by rfl⟩ : syracuseStep 818831 = 1228247) B1228247
theorem B818875 : Blo 818347 818875 := bstep (se 1 (by rfl) ⟨614156, by rfl⟩ : syracuseStep 818875 = 1228313) B1228313
theorem B9961217 : Blo 818347 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B3374849 : Blo 818347 3374849 := bstep (se 2 (by rfl) ⟨1265568, by rfl⟩ : syracuseStep 3374849 = 2531137) B2531137
theorem B818951 : Blo 818347 818951 := bstep (se 1 (by rfl) ⟨614213, by rfl⟩ : syracuseStep 818951 = 1228427) B1228427
theorem B818959 : Blo 818347 818959 := bstep (se 1 (by rfl) ⟨614219, by rfl⟩ : syracuseStep 818959 = 1228439) B1228439
theorem B819003 : Blo 818347 819003 := bstep (se 1 (by rfl) ⟨614252, by rfl⟩ : syracuseStep 819003 = 1228505) B1228505
theorem B819079 : Blo 818347 819079 := bstep (se 1 (by rfl) ⟨614309, by rfl⟩ : syracuseStep 819079 = 1228619) B1228619
theorem B819087 : Blo 818347 819087 := bstep (se 1 (by rfl) ⟨614315, by rfl⟩ : syracuseStep 819087 = 1228631) B1228631
theorem B28737431 : Blo 818347 28737431 := bstep (se 1 (by rfl) ⟨21553073, by rfl⟩ : syracuseStep 28737431 = 43106147) B43106147
theorem B819131 : Blo 818347 819131 := bstep (se 1 (by rfl) ⟨614348, by rfl⟩ : syracuseStep 819131 = 1228697) B1228697
theorem B4980689 : Blo 818347 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B819239 : Blo 818347 819239 := bstep (se 1 (by rfl) ⟨614429, by rfl⟩ : syracuseStep 819239 = 1228859) B1228859
theorem B819279 : Blo 818347 819279 := bstep (se 1 (by rfl) ⟨614459, by rfl⟩ : syracuseStep 819279 = 1228919) B1228919
theorem B4161617 : Blo 818347 4161617 := bstep (se 2 (by rfl) ⟨1560606, by rfl⟩ : syracuseStep 4161617 = 3121213) B3121213
theorem B819295 : Blo 818347 819295 := bstep (se 1 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 819295 = 1228943) B1228943
theorem B819323 : Blo 818347 819323 := bstep (se 1 (by rfl) ⟨614492, by rfl⟩ : syracuseStep 819323 = 1228985) B1228985
theorem B819375 : Blo 818347 819375 := bstep (se 1 (by rfl) ⟨614531, by rfl⟩ : syracuseStep 819375 = 1229063) B1229063
theorem B819399 : Blo 818347 819399 := bstep (se 1 (by rfl) ⟨614549, by rfl⟩ : syracuseStep 819399 = 1229099) B1229099
theorem B819419 : Blo 818347 819419 := bstep (se 1 (by rfl) ⟨614564, by rfl⟩ : syracuseStep 819419 = 1229129) B1229129
theorem B819495 : Blo 818347 819495 := bstep (se 1 (by rfl) ⟨614621, by rfl⟩ : syracuseStep 819495 = 1229243) B1229243
theorem B819535 : Blo 818347 819535 := bstep (se 1 (by rfl) ⟨614651, by rfl⟩ : syracuseStep 819535 = 1229303) B1229303
theorem B819551 : Blo 818347 819551 := bstep (se 1 (by rfl) ⟨614663, by rfl⟩ : syracuseStep 819551 = 1229327) B1229327
theorem B819579 : Blo 818347 819579 := bstep (se 1 (by rfl) ⟨614684, by rfl⟩ : syracuseStep 819579 = 1229369) B1229369
theorem B819631 : Blo 818347 819631 := bstep (se 1 (by rfl) ⟨614723, by rfl⟩ : syracuseStep 819631 = 1229447) B1229447
theorem B819655 : Blo 818347 819655 := bstep (se 1 (by rfl) ⟨614741, by rfl⟩ : syracuseStep 819655 = 1229483) B1229483
theorem B819675 : Blo 818347 819675 := bstep (se 1 (by rfl) ⟨614756, by rfl⟩ : syracuseStep 819675 = 1229513) B1229513
theorem B7012889 : Blo 818347 7012889 := bstep (se 2 (by rfl) ⟨2629833, by rfl⟩ : syracuseStep 7012889 = 5259667) B5259667
theorem B2949671 : Blo 818347 2949671 := bstep (se 1 (by rfl) ⟨2212253, by rfl⟩ : syracuseStep 2949671 = 4424507) B4424507
theorem B819751 : Blo 818347 819751 := bstep (se 1 (by rfl) ⟨614813, by rfl⟩ : syracuseStep 819751 = 1229627) B1229627
theorem B819791 : Blo 818347 819791 := bstep (se 1 (by rfl) ⟨614843, by rfl⟩ : syracuseStep 819791 = 1229687) B1229687
theorem B819807 : Blo 818347 819807 := bstep (se 1 (by rfl) ⟨614855, by rfl⟩ : syracuseStep 819807 = 1229711) B1229711
theorem B22413941 : Blo 818347 22413941 := bstep (se 5 (by rfl) ⟨1050653, by rfl⟩ : syracuseStep 22413941 = 2101307) B2101307
theorem B819835 : Blo 818347 819835 := bstep (se 1 (by rfl) ⟨614876, by rfl⟩ : syracuseStep 819835 = 1229753) B1229753
theorem B819887 : Blo 818347 819887 := bstep (se 1 (by rfl) ⟨614915, by rfl⟩ : syracuseStep 819887 = 1229831) B1229831
theorem B819911 : Blo 818347 819911 := bstep (se 1 (by rfl) ⟨614933, by rfl⟩ : syracuseStep 819911 = 1229867) B1229867
theorem B819931 : Blo 818347 819931 := bstep (se 1 (by rfl) ⟨614948, by rfl⟩ : syracuseStep 819931 = 1229897) B1229897
theorem B820007 : Blo 818347 820007 := bstep (se 1 (by rfl) ⟨615005, by rfl⟩ : syracuseStep 820007 = 1230011) B1230011
theorem B820047 : Blo 818347 820047 := bstep (se 1 (by rfl) ⟨615035, by rfl⟩ : syracuseStep 820047 = 1230071) B1230071
theorem B820063 : Blo 818347 820063 := bstep (se 1 (by rfl) ⟨615047, by rfl⟩ : syracuseStep 820063 = 1230095) B1230095
theorem B820091 : Blo 818347 820091 := bstep (se 1 (by rfl) ⟨615068, by rfl⟩ : syracuseStep 820091 = 1230137) B1230137
theorem B820143 : Blo 818347 820143 := bstep (se 1 (by rfl) ⟨615107, by rfl⟩ : syracuseStep 820143 = 1230215) B1230215
theorem B820167 : Blo 818347 820167 := bstep (se 1 (by rfl) ⟨615125, by rfl⟩ : syracuseStep 820167 = 1230251) B1230251
theorem B820187 : Blo 818347 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B2950145 : Blo 818347 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1475591 : Blo 818347 1475591 := bstep (se 1 (by rfl) ⟨1106693, by rfl⟩ : syracuseStep 1475591 = 2213387) B2213387
theorem B1246247 : Blo 818347 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B820263 : Blo 818347 820263 := bstep (se 1 (by rfl) ⟨615197, by rfl⟩ : syracuseStep 820263 = 1230395) B1230395
theorem B820303 : Blo 818347 820303 := bstep (se 1 (by rfl) ⟨615227, by rfl⟩ : syracuseStep 820303 = 1230455) B1230455
theorem B820319 : Blo 818347 820319 := bstep (se 1 (by rfl) ⟨615239, by rfl⟩ : syracuseStep 820319 = 1230479) B1230479
theorem B820347 : Blo 818347 820347 := bstep (se 1 (by rfl) ⟨615260, by rfl⟩ : syracuseStep 820347 = 1230521) B1230521
theorem B820399 : Blo 818347 820399 := bstep (se 1 (by rfl) ⟨615299, by rfl⟩ : syracuseStep 820399 = 1230599) B1230599
theorem B820423 : Blo 818347 820423 := bstep (se 1 (by rfl) ⟨615317, by rfl⟩ : syracuseStep 820423 = 1230635) B1230635
theorem B820443 : Blo 818347 820443 := bstep (se 1 (by rfl) ⟨615332, by rfl⟩ : syracuseStep 820443 = 1230665) B1230665
theorem B820519 : Blo 818347 820519 := bstep (se 1 (by rfl) ⟨615389, by rfl⟩ : syracuseStep 820519 = 1230779) B1230779
theorem B820559 : Blo 818347 820559 := bstep (se 1 (by rfl) ⟨615419, by rfl⟩ : syracuseStep 820559 = 1230839) B1230839
theorem B820575 : Blo 818347 820575 := bstep (se 1 (by rfl) ⟨615431, by rfl⟩ : syracuseStep 820575 = 1230863) B1230863
theorem B820603 : Blo 818347 820603 := bstep (se 1 (by rfl) ⟨615452, by rfl⟩ : syracuseStep 820603 = 1230905) B1230905
theorem B2622863 : Blo 818347 2622863 := bstep (se 1 (by rfl) ⟨1967147, by rfl⟩ : syracuseStep 2622863 = 3934295) B3934295
theorem B1312175 : Blo 818347 1312175 := bstep (se 1 (by rfl) ⟨984131, by rfl⟩ : syracuseStep 1312175 = 1968263) B1968263
theorem B820655 : Blo 818347 820655 := bstep (se 1 (by rfl) ⟨615491, by rfl⟩ : syracuseStep 820655 = 1230983) B1230983
theorem B820679 : Blo 818347 820679 := bstep (se 1 (by rfl) ⟨615509, by rfl⟩ : syracuseStep 820679 = 1231019) B1231019
theorem B7865819 : Blo 818347 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B820699 : Blo 818347 820699 := bstep (se 1 (by rfl) ⟨615524, by rfl⟩ : syracuseStep 820699 = 1231049) B1231049
theorem B820775 : Blo 818347 820775 := bstep (se 1 (by rfl) ⟨615581, by rfl⟩ : syracuseStep 820775 = 1231163) B1231163
theorem B820815 : Blo 818347 820815 := bstep (se 1 (by rfl) ⟨615611, by rfl⟩ : syracuseStep 820815 = 1231223) B1231223
theorem B820831 : Blo 818347 820831 := bstep (se 1 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 820831 = 1231247) B1231247
theorem B820859 : Blo 818347 820859 := bstep (se 1 (by rfl) ⟨615644, by rfl⟩ : syracuseStep 820859 = 1231289) B1231289
theorem B6227603 : Blo 818347 6227603 := bstep (se 1 (by rfl) ⟨4670702, by rfl⟩ : syracuseStep 6227603 = 9341405) B9341405
theorem B820911 : Blo 818347 820911 := bstep (se 1 (by rfl) ⟨615683, by rfl⟩ : syracuseStep 820911 = 1231367) B1231367
theorem B820935 : Blo 818347 820935 := bstep (se 1 (by rfl) ⟨615701, by rfl⟩ : syracuseStep 820935 = 1231403) B1231403
theorem B820955 : Blo 818347 820955 := bstep (se 1 (by rfl) ⟨615716, by rfl⟩ : syracuseStep 820955 = 1231433) B1231433
theorem B2623261 : Blo 818347 2623261 := bstep (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) B983723
theorem B821031 : Blo 818347 821031 := bstep (se 1 (by rfl) ⟨615773, by rfl⟩ : syracuseStep 821031 = 1231547) B1231547
theorem B3376939 : Blo 818347 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B821071 : Blo 818347 821071 := bstep (se 1 (by rfl) ⟨615803, by rfl⟩ : syracuseStep 821071 = 1231607) B1231607
theorem B821087 : Blo 818347 821087 := bstep (se 1 (by rfl) ⟨615815, by rfl⟩ : syracuseStep 821087 = 1231631) B1231631
theorem B821115 : Blo 818347 821115 := bstep (se 1 (by rfl) ⟨615836, by rfl⟩ : syracuseStep 821115 = 1231673) B1231673
theorem B821167 : Blo 818347 821167 := bstep (se 1 (by rfl) ⟨615875, by rfl⟩ : syracuseStep 821167 = 1231751) B1231751
theorem B821191 : Blo 818347 821191 := bstep (se 1 (by rfl) ⟨615893, by rfl⟩ : syracuseStep 821191 = 1231787) B1231787
theorem B821211 : Blo 818347 821211 := bstep (se 1 (by rfl) ⟨615908, by rfl⟩ : syracuseStep 821211 = 1231817) B1231817
theorem B1312777 : Blo 818347 1312777 := bstep (se 2 (by rfl) ⟨492291, by rfl⟩ : syracuseStep 1312777 = 984583) B984583
theorem B821287 : Blo 818347 821287 := bstep (se 1 (by rfl) ⟨615965, by rfl⟩ : syracuseStep 821287 = 1231931) B1231931
theorem B821327 : Blo 818347 821327 := bstep (se 1 (by rfl) ⟨615995, by rfl⟩ : syracuseStep 821327 = 1231991) B1231991
theorem B821343 : Blo 818347 821343 := bstep (se 1 (by rfl) ⟨616007, by rfl⟩ : syracuseStep 821343 = 1232015) B1232015
theorem B23693411 : Blo 818347 23693411 := bstep (se 1 (by rfl) ⟨17770058, by rfl⟩ : syracuseStep 23693411 = 35540117) B35540117
theorem B821371 : Blo 818347 821371 := bstep (se 1 (by rfl) ⟨616028, by rfl⟩ : syracuseStep 821371 = 1232057) B1232057
theorem B821423 : Blo 818347 821423 := bstep (se 1 (by rfl) ⟨616067, by rfl⟩ : syracuseStep 821423 = 1232135) B1232135
theorem B821447 : Blo 818347 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B821467 : Blo 818347 821467 := bstep (se 1 (by rfl) ⟨616100, by rfl⟩ : syracuseStep 821467 = 1232201) B1232201
theorem B821543 : Blo 818347 821543 := bstep (se 1 (by rfl) ⟨616157, by rfl⟩ : syracuseStep 821543 = 1232315) B1232315
theorem B821583 : Blo 818347 821583 := bstep (se 1 (by rfl) ⟨616187, by rfl⟩ : syracuseStep 821583 = 1232375) B1232375
theorem B821599 : Blo 818347 821599 := bstep (se 1 (by rfl) ⟨616199, by rfl⟩ : syracuseStep 821599 = 1232399) B1232399
theorem B821627 : Blo 818347 821627 := bstep (se 1 (by rfl) ⟨616220, by rfl⟩ : syracuseStep 821627 = 1232441) B1232441
theorem B821679 : Blo 818347 821679 := bstep (se 1 (by rfl) ⟨616259, by rfl⟩ : syracuseStep 821679 = 1232519) B1232519
theorem B821703 : Blo 818347 821703 := bstep (se 1 (by rfl) ⟨616277, by rfl⟩ : syracuseStep 821703 = 1232555) B1232555
theorem B821723 : Blo 818347 821723 := bstep (se 1 (by rfl) ⟨616292, by rfl⟩ : syracuseStep 821723 = 1232585) B1232585
theorem B821799 : Blo 818347 821799 := bstep (se 1 (by rfl) ⟨616349, by rfl⟩ : syracuseStep 821799 = 1232699) B1232699
theorem B821839 : Blo 818347 821839 := bstep (se 1 (by rfl) ⟨616379, by rfl⟩ : syracuseStep 821839 = 1232759) B1232759
theorem B821855 : Blo 818347 821855 := bstep (se 1 (by rfl) ⟨616391, by rfl⟩ : syracuseStep 821855 = 1232783) B1232783
theorem B1772155 : Blo 818347 1772155 := bstep (se 1 (by rfl) ⟨1329116, by rfl⟩ : syracuseStep 1772155 = 2658233) B2658233
theorem B821883 : Blo 818347 821883 := bstep (se 1 (by rfl) ⟨616412, by rfl⟩ : syracuseStep 821883 = 1232825) B1232825
theorem B3115655 : Blo 818347 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B821935 : Blo 818347 821935 := bstep (se 1 (by rfl) ⟨616451, by rfl⟩ : syracuseStep 821935 = 1232903) B1232903
theorem B821959 : Blo 818347 821959 := bstep (se 1 (by rfl) ⟨616469, by rfl⟩ : syracuseStep 821959 = 1232939) B1232939
theorem B821979 : Blo 818347 821979 := bstep (se 1 (by rfl) ⟨616484, by rfl⟩ : syracuseStep 821979 = 1232969) B1232969
theorem B822055 : Blo 818347 822055 := bstep (se 1 (by rfl) ⟨616541, by rfl⟩ : syracuseStep 822055 = 1233083) B1233083
theorem B822095 : Blo 818347 822095 := bstep (se 1 (by rfl) ⟨616571, by rfl⟩ : syracuseStep 822095 = 1233143) B1233143
theorem B822111 : Blo 818347 822111 := bstep (se 1 (by rfl) ⟨616583, by rfl⟩ : syracuseStep 822111 = 1233167) B1233167
theorem B822139 : Blo 818347 822139 := bstep (se 1 (by rfl) ⟨616604, by rfl⟩ : syracuseStep 822139 = 1233209) B1233209
theorem B822191 : Blo 818347 822191 := bstep (se 1 (by rfl) ⟨616643, by rfl⟩ : syracuseStep 822191 = 1233287) B1233287
theorem B822215 : Blo 818347 822215 := bstep (se 1 (by rfl) ⟨616661, by rfl⟩ : syracuseStep 822215 = 1233323) B1233323
theorem B822235 : Blo 818347 822235 := bstep (se 1 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 822235 = 1233353) B1233353
theorem B822311 : Blo 818347 822311 := bstep (se 1 (by rfl) ⟨616733, by rfl⟩ : syracuseStep 822311 = 1233467) B1233467
theorem B8424643 : Blo 818347 8424643 := bstep (se 1 (by rfl) ⟨6318482, by rfl⟩ : syracuseStep 8424643 = 12636965) B12636965
theorem B2592011 : Blo 818347 2592011 := bstep (se 1 (by rfl) ⟨1944008, by rfl⟩ : syracuseStep 2592011 = 3888017) B3888017
theorem B2952553 : Blo 818347 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B2952713 : Blo 818347 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B921127 : Blo 818347 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B2952827 : Blo 818347 2952827 := bstep (se 1 (by rfl) ⟨2214620, by rfl⟩ : syracuseStep 2952827 = 4429241) B4429241
theorem B2953027 : Blo 818347 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B7868279 : Blo 818347 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B5246855 : Blo 818347 5246855 := bstep (se 1 (by rfl) ⟨3935141, by rfl⟩ : syracuseStep 5246855 = 7870283) B7870283
theorem B1478663 : Blo 818347 1478663 := bstep (se 1 (by rfl) ⟨1108997, by rfl⟩ : syracuseStep 1478663 = 2217995) B2217995
theorem B21073931 : Blo 818347 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B3117113 : Blo 818347 3117113 := bstep (se 2 (by rfl) ⟨1168917, by rfl⟩ : syracuseStep 3117113 = 2337835) B2337835
theorem B3739763 : Blo 818347 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B2330795 : Blo 818347 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B2626195 : Blo 818347 2626195 := bstep (se 1 (by rfl) ⟨1969646, by rfl⟩ : syracuseStep 2626195 = 3939293) B3939293
theorem B1381063 : Blo 818347 1381063 := bstep (se 1 (by rfl) ⟨1035797, by rfl⟩ : syracuseStep 1381063 = 2071595) B2071595
theorem B1381225 : Blo 818347 1381225 := bstep (se 2 (by rfl) ⟨517959, by rfl⟩ : syracuseStep 1381225 = 1035919) B1035919
theorem B11801497 : Blo 818347 11801497 := bstep (se 2 (by rfl) ⟨4425561, by rfl⟩ : syracuseStep 11801497 = 8851123) B8851123
theorem B4330415 : Blo 818347 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B6231005 : Blo 818347 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B7115777 : Blo 818347 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B922747 : Blo 818347 922747 := bstep (se 1 (by rfl) ⟨692060, by rfl⟩ : syracuseStep 922747 = 1384121) B1384121
theorem B35493065 : Blo 818347 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B3937679 : Blo 818347 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B1381819 : Blo 818347 1381819 := bstep (se 1 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 1381819 = 2072729) B2072729
theorem B7017947 : Blo 818347 7017947 := bstep (se 1 (by rfl) ⟨5263460, by rfl⟩ : syracuseStep 7017947 = 10526921) B10526921
theorem B3118601 : Blo 818347 3118601 := bstep (se 2 (by rfl) ⟨1169475, by rfl⟩ : syracuseStep 3118601 = 2338951) B2338951
theorem B1381927 : Blo 818347 1381927 := bstep (se 1 (by rfl) ⟨1036445, by rfl⟩ : syracuseStep 1381927 = 2072891) B2072891
theorem B3741223 : Blo 818347 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B923215 : Blo 818347 923215 := bstep (se 1 (by rfl) ⟨692411, by rfl⟩ : syracuseStep 923215 = 1384823) B1384823
theorem B1382251 : Blo 818347 1382251 := bstep (se 1 (by rfl) ⟨1036688, by rfl⟩ : syracuseStep 1382251 = 2073377) B2073377
theorem B923611 : Blo 818347 923611 := bstep (se 1 (by rfl) ⟨692708, by rfl⟩ : syracuseStep 923611 = 1385417) B1385417
theorem B1316827 : Blo 818347 1316827 := bstep (se 1 (by rfl) ⟨987620, by rfl⟩ : syracuseStep 1316827 = 1975241) B1975241
theorem B1480723 : Blo 818347 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B1841399 : Blo 818347 1841399 := bstep (se 1 (by rfl) ⟨1381049, by rfl⟩ : syracuseStep 1841399 = 2762099) B2762099
theorem B8853893 : Blo 818347 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B924079 : Blo 818347 924079 := bstep (se 1 (by rfl) ⟨693059, by rfl⟩ : syracuseStep 924079 = 1386119) B1386119
theorem B3119755 : Blo 818347 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B1841993 : Blo 818347 1841993 := bstep (se 2 (by rfl) ⟨690747, by rfl⟩ : syracuseStep 1841993 = 1381495) B1381495
theorem B2628425 : Blo 818347 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B924511 : Blo 818347 924511 := bstep (se 1 (by rfl) ⟨693383, by rfl⟩ : syracuseStep 924511 = 1386767) B1386767
theorem B1383311 : Blo 818347 1383311 := bstep (se 1 (by rfl) ⟨1037483, by rfl⟩ : syracuseStep 1383311 = 2074967) B2074967
theorem B3120059 : Blo 818347 3120059 := bstep (se 1 (by rfl) ⟨2340044, by rfl⟩ : syracuseStep 3120059 = 4680089) B4680089
theorem B1383547 : Blo 818347 1383547 := bstep (se 1 (by rfl) ⟨1037660, by rfl⟩ : syracuseStep 1383547 = 2075321) B2075321
theorem B4988099 : Blo 818347 4988099 := bstep (se 1 (by rfl) ⟨3741074, by rfl⟩ : syracuseStep 4988099 = 7482149) B7482149
theorem B924871 : Blo 818347 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B5250419 : Blo 818347 5250419 := bstep (se 1 (by rfl) ⟨3937814, by rfl⟩ : syracuseStep 5250419 = 7875629) B7875629
theorem B3743119 : Blo 818347 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B2072051 : Blo 818347 2072051 := bstep (se 1 (by rfl) ⟨1554038, by rfl⟩ : syracuseStep 2072051 = 3108077) B3108077
theorem B1842785 : Blo 818347 1842785 := bstep (se 2 (by rfl) ⟨691044, by rfl⟩ : syracuseStep 1842785 = 1382089) B1382089
theorem B1777351 : Blo 818347 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B2072263 : Blo 818347 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B3743597 : Blo 818347 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B1843127 : Blo 818347 1843127 := bstep (se 1 (by rfl) ⟨1382345, by rfl⟩ : syracuseStep 1843127 = 2764691) B2764691
theorem B1384411 : Blo 818347 1384411 := bstep (se 1 (by rfl) ⟨1038308, by rfl⟩ : syracuseStep 1384411 = 2076617) B2076617
theorem B29925389 : Blo 818347 29925389 := bstep (se 3 (by rfl) ⟨5611010, by rfl⟩ : syracuseStep 29925389 = 11222021) B11222021
theorem B1122665 : Blo 818347 1122665 := bstep (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) B841999
theorem B1843721 : Blo 818347 1843721 := bstep (se 2 (by rfl) ⟨691395, by rfl⟩ : syracuseStep 1843721 = 1382791) B1382791
theorem B4661819 : Blo 818347 4661819 := bstep (se 1 (by rfl) ⟨3496364, by rfl⟩ : syracuseStep 4661819 = 6992729) B6992729
theorem B1385039 : Blo 818347 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B2073185 : Blo 818347 2073185 := bstep (se 2 (by rfl) ⟨777444, by rfl⟩ : syracuseStep 2073185 = 1554889) B1554889
theorem B1844063 : Blo 818347 1844063 := bstep (se 1 (by rfl) ⟨1383047, by rfl⟩ : syracuseStep 1844063 = 2766095) B2766095
theorem B12166145 : Blo 818347 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B1844243 : Blo 818347 1844243 := bstep (se 1 (by rfl) ⟨1383182, by rfl⟩ : syracuseStep 1844243 = 2766365) B2766365
theorem B2762045 : Blo 818347 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B1844585 : Blo 818347 1844585 := bstep (se 2 (by rfl) ⟨691719, by rfl⟩ : syracuseStep 1844585 = 1383439) B1383439
theorem B1385903 : Blo 818347 1385903 := bstep (se 1 (by rfl) ⟨1039427, by rfl⟩ : syracuseStep 1385903 = 2078855) B2078855
theorem B3155705 : Blo 818347 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B1386335 : Blo 818347 1386335 := bstep (se 1 (by rfl) ⟨1039751, by rfl⟩ : syracuseStep 1386335 = 2079503) B2079503
theorem B1845179 : Blo 818347 1845179 := bstep (se 1 (by rfl) ⟨1383884, by rfl⟩ : syracuseStep 1845179 = 2767769) B2767769
theorem B2074643 : Blo 818347 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B1845305 : Blo 818347 1845305 := bstep (se 2 (by rfl) ⟨691989, by rfl⟩ : syracuseStep 1845305 = 1383979) B1383979
theorem B2762909 : Blo 818347 2762909 := bstep (se 3 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 2762909 = 1036091) B1036091
theorem B2959517 : Blo 818347 2959517 := bstep (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) B1109819
theorem B1845647 : Blo 818347 1845647 := bstep (se 1 (by rfl) ⟨1384235, by rfl⟩ : syracuseStep 1845647 = 2768471) B2768471
theorem B1386895 : Blo 818347 1386895 := bstep (se 1 (by rfl) ⟨1040171, by rfl⟩ : syracuseStep 1386895 = 2080343) B2080343
theorem B3320459 : Blo 818347 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B2763449 : Blo 818347 2763449 := bstep (se 2 (by rfl) ⟨1036293, by rfl⟩ : syracuseStep 2763449 = 2072587) B2072587
theorem B1845971 : Blo 818347 1845971 := bstep (se 1 (by rfl) ⟨1384478, by rfl⟩ : syracuseStep 1845971 = 2768957) B2768957
theorem B1387577 : Blo 818347 1387577 := bstep (se 2 (by rfl) ⟨520341, by rfl⟩ : syracuseStep 1387577 = 1040683) B1040683
theorem B2764043 : Blo 818347 2764043 := bstep (se 1 (by rfl) ⟨2073032, by rfl⟩ : syracuseStep 2764043 = 4146065) B4146065
theorem B5615021 : Blo 818347 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B2764313 : Blo 818347 2764313 := bstep (se 2 (by rfl) ⟨1036617, by rfl⟩ : syracuseStep 2764313 = 2073235) B2073235
theorem B27012727 : Blo 818347 27012727 := bstep (se 1 (by rfl) ⟨20259545, by rfl⟩ : syracuseStep 27012727 = 40519091) B40519091
theorem B1846907 : Blo 818347 1846907 := bstep (se 1 (by rfl) ⟨1385180, by rfl⟩ : syracuseStep 1846907 = 2770361) B2770361
theorem B4665053 : Blo 818347 4665053 := bstep (se 3 (by rfl) ⟨874697, by rfl⟩ : syracuseStep 4665053 = 1749395) B1749395
theorem B1748729 : Blo 818347 1748729 := bstep (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) B1311547
theorem B1847033 : Blo 818347 1847033 := bstep (se 2 (by rfl) ⟨692637, by rfl⟩ : syracuseStep 1847033 = 1385275) B1385275
theorem B1847303 : Blo 818347 1847303 := bstep (se 1 (by rfl) ⟨1385477, by rfl⟩ : syracuseStep 1847303 = 2770955) B2770955
theorem B1847375 : Blo 818347 1847375 := bstep (se 1 (by rfl) ⟨1385531, by rfl⟩ : syracuseStep 1847375 = 2771063) B2771063
theorem B2338895 : Blo 818347 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B1847771 : Blo 818347 1847771 := bstep (se 1 (by rfl) ⟨1385828, by rfl⟩ : syracuseStep 1847771 = 2771657) B2771657
theorem B4436461 : Blo 818347 4436461 := bstep (se 3 (by rfl) ⟨831836, by rfl⟩ : syracuseStep 4436461 = 1663673) B1663673
theorem B2765447 : Blo 818347 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B2765501 : Blo 818347 2765501 := bstep (se 3 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 2765501 = 1037063) B1037063
theorem B1749703 : Blo 818347 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B2339543 : Blo 818347 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B2765663 : Blo 818347 2765663 := bstep (se 1 (by rfl) ⟨2074247, by rfl⟩ : syracuseStep 2765663 = 4148495) B4148495
theorem B1848239 : Blo 818347 1848239 := bstep (se 1 (by rfl) ⟨1386179, by rfl⟩ : syracuseStep 1848239 = 2772359) B2772359
theorem B2765825 : Blo 818347 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B1848491 : Blo 818347 1848491 := bstep (se 1 (by rfl) ⟨1386368, by rfl⟩ : syracuseStep 1848491 = 2772737) B2772737
theorem B2078095 : Blo 818347 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B2962831 : Blo 818347 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B1849031 : Blo 818347 1849031 := bstep (se 1 (by rfl) ⟨1386773, by rfl⟩ : syracuseStep 1849031 = 2773547) B2773547
theorem B2078419 : Blo 818347 2078419 := bstep (se 1 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 2078419 = 3117629) B3117629
theorem B1554167 : Blo 818347 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B2766635 : Blo 818347 2766635 := bstep (se 1 (by rfl) ⟨2074976, by rfl⟩ : syracuseStep 2766635 = 4149953) B4149953
theorem B4437827 : Blo 818347 4437827 := bstep (se 1 (by rfl) ⟨3328370, by rfl⟩ : syracuseStep 4437827 = 6656741) B6656741
theorem B6666079 : Blo 818347 6666079 := bstep (se 1 (by rfl) ⟨4999559, by rfl⟩ : syracuseStep 6666079 = 9999119) B9999119
theorem B1750891 : Blo 818347 1750891 := bstep (se 1 (by rfl) ⟨1313168, by rfl⟩ : syracuseStep 1750891 = 2626337) B2626337
theorem B9353069 : Blo 818347 9353069 := bstep (se 3 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 9353069 = 3507401) B3507401
theorem B53262197 : Blo 818347 53262197 := bstep (se 5 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 53262197 = 4993331) B4993331
theorem B1554319 : Blo 818347 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B4437947 : Blo 818347 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B3946427 : Blo 818347 3946427 := bstep (se 1 (by rfl) ⟨2959820, by rfl⟩ : syracuseStep 3946427 = 5919641) B5919641
theorem B12793859 : Blo 818347 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B2766905 : Blo 818347 2766905 := bstep (se 2 (by rfl) ⟨1037589, by rfl⟩ : syracuseStep 2766905 = 2075179) B2075179
theorem B2767229 : Blo 818347 2767229 := bstep (se 3 (by rfl) ⟨518855, by rfl⟩ : syracuseStep 2767229 = 1037711) B1037711
theorem B15350219 : Blo 818347 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B4209185 : Blo 818347 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B1849895 : Blo 818347 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B6666887 : Blo 818347 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B2767499 : Blo 818347 2767499 := bstep (se 1 (by rfl) ⟨2075624, by rfl⟩ : syracuseStep 2767499 = 4151249) B4151249
theorem B2079371 : Blo 818347 2079371 := bstep (se 1 (by rfl) ⟨1559528, by rfl⟩ : syracuseStep 2079371 = 3119057) B3119057
theorem B1555193 : Blo 818347 1555193 := bstep (se 2 (by rfl) ⟨583197, by rfl⟩ : syracuseStep 1555193 = 1166395) B1166395
theorem B4209515 : Blo 818347 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B1850219 : Blo 818347 1850219 := bstep (se 1 (by rfl) ⟨1387664, by rfl⟩ : syracuseStep 1850219 = 2775329) B2775329
theorem B1850273 : Blo 818347 1850273 := bstep (se 2 (by rfl) ⟨693852, by rfl⟩ : syracuseStep 1850273 = 1387705) B1387705
theorem B1227695 : Blo 818347 1227695 := bstep (se 1 (by rfl) ⟨920771, by rfl⟩ : syracuseStep 1227695 = 1841543) B1841543
theorem B1555375 : Blo 818347 1555375 := bstep (se 1 (by rfl) ⟨1166531, by rfl⟩ : syracuseStep 1555375 = 2333063) B2333063
theorem B3750839 : Blo 818347 3750839 := bstep (se 1 (by rfl) ⟨2813129, by rfl⟩ : syracuseStep 3750839 = 5626259) B5626259
theorem B1227785 : Blo 818347 1227785 := bstep (se 2 (by rfl) ⟨460419, by rfl⟩ : syracuseStep 1227785 = 920839) B920839
theorem B1227815 : Blo 818347 1227815 := bstep (se 1 (by rfl) ⟨920861, by rfl⟩ : syracuseStep 1227815 = 1841723) B1841723
theorem B1752121 : Blo 818347 1752121 := bstep (se 2 (by rfl) ⟨657045, by rfl⟩ : syracuseStep 1752121 = 1314091) B1314091
theorem B1227899 : Blo 818347 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1228025 : Blo 818347 1228025 := bstep (se 2 (by rfl) ⟨460509, by rfl⟩ : syracuseStep 1228025 = 921019) B921019
theorem B28392727 : Blo 818347 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B1228127 : Blo 818347 1228127 := bstep (se 1 (by rfl) ⟨921095, by rfl⟩ : syracuseStep 1228127 = 1842191) B1842191
theorem B1228139 : Blo 818347 1228139 := bstep (se 1 (by rfl) ⟨921104, by rfl⟩ : syracuseStep 1228139 = 1842209) B1842209
theorem B2768417 : Blo 818347 2768417 := bstep (se 2 (by rfl) ⟨1038156, by rfl⟩ : syracuseStep 2768417 = 2076313) B2076313
theorem B1228367 : Blo 818347 1228367 := bstep (se 1 (by rfl) ⟨921275, by rfl⟩ : syracuseStep 1228367 = 1842551) B1842551
theorem B5258951 : Blo 818347 5258951 := bstep (se 1 (by rfl) ⟨3944213, by rfl⟩ : syracuseStep 5258951 = 7888427) B7888427
theorem B1228487 : Blo 818347 1228487 := bstep (se 1 (by rfl) ⟨921365, by rfl⟩ : syracuseStep 1228487 = 1842731) B1842731
theorem B7880429 : Blo 818347 7880429 := bstep (se 3 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 7880429 = 2955161) B2955161
theorem B2768633 : Blo 818347 2768633 := bstep (se 2 (by rfl) ⟨1038237, by rfl⟩ : syracuseStep 2768633 = 2076475) B2076475
theorem B2080505 : Blo 818347 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B8437537 : Blo 818347 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B1228649 : Blo 818347 1228649 := bstep (se 2 (by rfl) ⟨460743, by rfl⟩ : syracuseStep 1228649 = 921487) B921487
theorem B6242183 : Blo 818347 6242183 := bstep (se 1 (by rfl) ⟨4681637, by rfl⟩ : syracuseStep 6242183 = 9363275) B9363275
theorem B2080687 : Blo 818347 2080687 := bstep (se 1 (by rfl) ⟨1560515, by rfl⟩ : syracuseStep 2080687 = 3121031) B3121031
theorem B1228727 : Blo 818347 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B1228763 : Blo 818347 1228763 := bstep (se 1 (by rfl) ⟨921572, by rfl⟩ : syracuseStep 1228763 = 1843145) B1843145
theorem B2768903 : Blo 818347 2768903 := bstep (se 1 (by rfl) ⟨2076677, by rfl⟩ : syracuseStep 2768903 = 4153355) B4153355
theorem B2769011 : Blo 818347 2769011 := bstep (se 1 (by rfl) ⟨2076758, by rfl⟩ : syracuseStep 2769011 = 4153517) B4153517
theorem B1556651 : Blo 818347 1556651 := bstep (se 1 (by rfl) ⟨1167488, by rfl⟩ : syracuseStep 1556651 = 2334977) B2334977
theorem B2769281 : Blo 818347 2769281 := bstep (se 2 (by rfl) ⟨1038480, by rfl⟩ : syracuseStep 2769281 = 2076961) B2076961
theorem B2081153 : Blo 818347 2081153 := bstep (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) B1560865
theorem B1687969 : Blo 818347 1687969 := bstep (se 2 (by rfl) ⟨632988, by rfl⟩ : syracuseStep 1687969 = 1265977) B1265977
theorem B1229231 : Blo 818347 1229231 := bstep (se 1 (by rfl) ⟨921923, by rfl⟩ : syracuseStep 1229231 = 1843847) B1843847
theorem B2212339 : Blo 818347 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1229321 : Blo 818347 1229321 := bstep (se 2 (by rfl) ⟨460995, by rfl⟩ : syracuseStep 1229321 = 921991) B921991
theorem B1229351 : Blo 818347 1229351 := bstep (se 1 (by rfl) ⟨922013, by rfl⟩ : syracuseStep 1229351 = 1844027) B1844027
theorem B1229435 : Blo 818347 1229435 := bstep (se 1 (by rfl) ⟨922076, by rfl⟩ : syracuseStep 1229435 = 1844153) B1844153
theorem B5259977 : Blo 818347 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B9355985 : Blo 818347 9355985 := bstep (se 2 (by rfl) ⟨3508494, by rfl⟩ : syracuseStep 9355985 = 7016989) B7016989
theorem B1229561 : Blo 818347 1229561 := bstep (se 2 (by rfl) ⟨461085, by rfl⟩ : syracuseStep 1229561 = 922171) B922171
theorem B21021443 : Blo 818347 21021443 := bstep (se 1 (by rfl) ⟨15766082, by rfl⟩ : syracuseStep 21021443 = 31532165) B31532165
theorem B1229663 : Blo 818347 1229663 := bstep (se 1 (by rfl) ⟨922247, by rfl⟩ : syracuseStep 1229663 = 1844495) B1844495
theorem B1229675 : Blo 818347 1229675 := bstep (se 1 (by rfl) ⟨922256, by rfl⟩ : syracuseStep 1229675 = 1844513) B1844513
theorem B4146227 : Blo 818347 4146227 := bstep (se 1 (by rfl) ⟨3109670, by rfl⟩ : syracuseStep 4146227 = 6219341) B6219341
theorem B7095347 : Blo 818347 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B1229903 : Blo 818347 1229903 := bstep (se 1 (by rfl) ⟨922427, by rfl⟩ : syracuseStep 1229903 = 1844855) B1844855
theorem B2770091 : Blo 818347 2770091 := bstep (se 1 (by rfl) ⟨2077568, by rfl⟩ : syracuseStep 2770091 = 4155137) B4155137
theorem B1230023 : Blo 818347 1230023 := bstep (se 1 (by rfl) ⟨922517, by rfl⟩ : syracuseStep 1230023 = 1845035) B1845035
theorem B1230185 : Blo 818347 1230185 := bstep (se 2 (by rfl) ⟨461319, by rfl⟩ : syracuseStep 1230185 = 922639) B922639
theorem B4670885 : Blo 818347 4670885 := bstep (se 4 (by rfl) ⟨437895, by rfl⟩ : syracuseStep 4670885 = 875791) B875791
theorem B1230263 : Blo 818347 1230263 := bstep (se 1 (by rfl) ⟨922697, by rfl⟩ : syracuseStep 1230263 = 1845395) B1845395
theorem B1230299 : Blo 818347 1230299 := bstep (se 1 (by rfl) ⟨922724, by rfl⟩ : syracuseStep 1230299 = 1845449) B1845449
theorem B1558025 : Blo 818347 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B1558055 : Blo 818347 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B2770631 : Blo 818347 2770631 := bstep (se 1 (by rfl) ⟨2077973, by rfl⟩ : syracuseStep 2770631 = 4155947) B4155947
theorem B4671341 : Blo 818347 4671341 := bstep (se 3 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 4671341 = 1751753) B1751753
theorem B1230767 : Blo 818347 1230767 := bstep (se 1 (by rfl) ⟨923075, by rfl⟩ : syracuseStep 1230767 = 1846151) B1846151
theorem B1230857 : Blo 818347 1230857 := bstep (se 2 (by rfl) ⟨461571, by rfl⟩ : syracuseStep 1230857 = 923143) B923143
theorem B1230887 : Blo 818347 1230887 := bstep (se 1 (by rfl) ⟨923165, by rfl⟩ : syracuseStep 1230887 = 1846331) B1846331
theorem B1230971 : Blo 818347 1230971 := bstep (se 1 (by rfl) ⟨923228, by rfl⟩ : syracuseStep 1230971 = 1846457) B1846457
theorem B1755307 : Blo 818347 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B1558739 : Blo 818347 1558739 := bstep (se 1 (by rfl) ⟨1169054, by rfl⟩ : syracuseStep 1558739 = 2338109) B2338109
theorem B1231097 : Blo 818347 1231097 := bstep (se 2 (by rfl) ⟨461661, by rfl⟩ : syracuseStep 1231097 = 923323) B923323
theorem B1558777 : Blo 818347 1558777 := bstep (se 2 (by rfl) ⟨584541, by rfl⟩ : syracuseStep 1558777 = 1169083) B1169083
theorem B1231199 : Blo 818347 1231199 := bstep (se 1 (by rfl) ⟨923399, by rfl⟩ : syracuseStep 1231199 = 1846799) B1846799
theorem B1231211 : Blo 818347 1231211 := bstep (se 1 (by rfl) ⟨923408, by rfl⟩ : syracuseStep 1231211 = 1846817) B1846817
theorem B2214425 : Blo 818347 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B4672025 : Blo 818347 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B2771495 : Blo 818347 2771495 := bstep (se 1 (by rfl) ⟨2078621, by rfl⟩ : syracuseStep 2771495 = 4157243) B4157243
theorem B1231439 : Blo 818347 1231439 := bstep (se 1 (by rfl) ⟨923579, by rfl⟩ : syracuseStep 1231439 = 1847159) B1847159
theorem B4147847 : Blo 818347 4147847 := bstep (se 1 (by rfl) ⟨3110885, by rfl⟩ : syracuseStep 4147847 = 6221771) B6221771
theorem B2771603 : Blo 818347 2771603 := bstep (se 1 (by rfl) ⟨2078702, by rfl⟩ : syracuseStep 2771603 = 4157405) B4157405
theorem B1231559 : Blo 818347 1231559 := bstep (se 1 (by rfl) ⟨923669, by rfl⟩ : syracuseStep 1231559 = 1847339) B1847339
theorem B6310601 : Blo 818347 6310601 := bstep (se 2 (by rfl) ⟨2366475, by rfl⟩ : syracuseStep 6310601 = 4732951) B4732951
theorem B1231721 : Blo 818347 1231721 := bstep (se 2 (by rfl) ⟨461895, by rfl⟩ : syracuseStep 1231721 = 923791) B923791
theorem B2771819 : Blo 818347 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B2771873 : Blo 818347 2771873 := bstep (se 2 (by rfl) ⟨1039452, by rfl⟩ : syracuseStep 2771873 = 2078905) B2078905
theorem B1231799 : Blo 818347 1231799 := bstep (se 1 (by rfl) ⟨923849, by rfl⟩ : syracuseStep 1231799 = 1847699) B1847699
theorem B1559483 : Blo 818347 1559483 := bstep (se 1 (by rfl) ⟨1169612, by rfl⟩ : syracuseStep 1559483 = 2339225) B2339225
theorem B1231835 : Blo 818347 1231835 := bstep (se 1 (by rfl) ⟨923876, by rfl⟩ : syracuseStep 1231835 = 1847753) B1847753
theorem B3329195 : Blo 818347 3329195 := bstep (se 1 (by rfl) ⟨2496896, by rfl⟩ : syracuseStep 3329195 = 4993793) B4993793
theorem B1559969 : Blo 818347 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B1232303 : Blo 818347 1232303 := bstep (se 1 (by rfl) ⟨924227, by rfl⟩ : syracuseStep 1232303 = 1848455) B1848455
theorem B2772467 : Blo 818347 2772467 := bstep (se 1 (by rfl) ⟨2079350, by rfl⟩ : syracuseStep 2772467 = 4158701) B4158701
theorem B1232393 : Blo 818347 1232393 := bstep (se 2 (by rfl) ⟨462147, by rfl⟩ : syracuseStep 1232393 = 924295) B924295
theorem B1232423 : Blo 818347 1232423 := bstep (se 1 (by rfl) ⟨924317, by rfl⟩ : syracuseStep 1232423 = 1848635) B1848635
theorem B26594891 : Blo 818347 26594891 := bstep (se 1 (by rfl) ⟨19946168, by rfl⟩ : syracuseStep 26594891 = 39892337) B39892337
theorem B1232507 : Blo 818347 1232507 := bstep (se 1 (by rfl) ⟨924380, by rfl⟩ : syracuseStep 1232507 = 1848761) B1848761
theorem B5000849 : Blo 818347 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B1560235 : Blo 818347 1560235 := bstep (se 1 (by rfl) ⟨1170176, by rfl⟩ : syracuseStep 1560235 = 2340353) B2340353
theorem B1232633 : Blo 818347 1232633 := bstep (se 2 (by rfl) ⟨462237, by rfl⟩ : syracuseStep 1232633 = 924475) B924475
theorem B1232735 : Blo 818347 1232735 := bstep (se 1 (by rfl) ⟨924551, by rfl⟩ : syracuseStep 1232735 = 1849103) B1849103
theorem B1232747 : Blo 818347 1232747 := bstep (se 1 (by rfl) ⟨924560, by rfl⟩ : syracuseStep 1232747 = 1849121) B1849121
theorem B1560539 : Blo 818347 1560539 := bstep (se 1 (by rfl) ⟨1170404, by rfl⟩ : syracuseStep 1560539 = 2340809) B2340809
theorem B5328911 : Blo 818347 5328911 := bstep (se 1 (by rfl) ⟨3996683, by rfl⟩ : syracuseStep 5328911 = 7993367) B7993367
theorem B2773007 : Blo 818347 2773007 := bstep (se 1 (by rfl) ⟨2079755, by rfl⟩ : syracuseStep 2773007 = 4159511) B4159511
theorem B4149305 : Blo 818347 4149305 := bstep (se 2 (by rfl) ⟨1555989, by rfl⟩ : syracuseStep 4149305 = 3111979) B3111979
theorem B1232975 : Blo 818347 1232975 := bstep (se 1 (by rfl) ⟨924731, by rfl⟩ : syracuseStep 1232975 = 1849463) B1849463
theorem B1233095 : Blo 818347 1233095 := bstep (se 1 (by rfl) ⟨924821, by rfl⟩ : syracuseStep 1233095 = 1849643) B1849643
theorem B1233257 : Blo 818347 1233257 := bstep (se 2 (by rfl) ⟨462471, by rfl⟩ : syracuseStep 1233257 = 924943) B924943
theorem B1233335 : Blo 818347 1233335 := bstep (se 1 (by rfl) ⟨925001, by rfl⟩ : syracuseStep 1233335 = 1850003) B1850003
theorem B1233371 : Blo 818347 1233371 := bstep (se 1 (by rfl) ⟨925028, by rfl⟩ : syracuseStep 1233371 = 1850057) B1850057
theorem B3002939 : Blo 818347 3002939 := bstep (se 1 (by rfl) ⟨2252204, by rfl⟩ : syracuseStep 3002939 = 4504409) B4504409
theorem B2773601 : Blo 818347 2773601 := bstep (se 2 (by rfl) ⟨1040100, by rfl⟩ : syracuseStep 2773601 = 2080201) B2080201
theorem B4674257 : Blo 818347 4674257 := bstep (se 2 (by rfl) ⟨1752846, by rfl⟩ : syracuseStep 4674257 = 3505693) B3505693
theorem B6640811 : Blo 818347 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B2249899 : Blo 818347 2249899 := bstep (se 1 (by rfl) ⟨1687424, by rfl⟩ : syracuseStep 2249899 = 3374849) B3374849
theorem B19158287 : Blo 818347 19158287 := bstep (se 1 (by rfl) ⟨14368715, by rfl⟩ : syracuseStep 19158287 = 28737431) B28737431
theorem B4674941 : Blo 818347 4674941 := bstep (se 3 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 4674941 = 1753103) B1753103
theorem B1037863 : Blo 818347 1037863 := bstep (se 1 (by rfl) ⟨778397, by rfl⟩ : syracuseStep 1037863 = 1556795) B1556795
theorem B1660495 : Blo 818347 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B3331793 : Blo 818347 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1038187 : Blo 818347 1038187 := bstep (se 1 (by rfl) ⟨778640, by rfl⟩ : syracuseStep 1038187 = 1557281) B1557281
theorem B2775059 : Blo 818347 2775059 := bstep (se 1 (by rfl) ⟨2081294, by rfl⟩ : syracuseStep 2775059 = 4162589) B4162589
theorem B1038415 : Blo 818347 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B4151411 : Blo 818347 4151411 := bstep (se 1 (by rfl) ⟨3113558, by rfl⟩ : syracuseStep 4151411 = 6227117) B6227117
theorem B2775383 : Blo 818347 2775383 := bstep (se 1 (by rfl) ⟨2081537, by rfl⟩ : syracuseStep 2775383 = 4163075) B4163075
theorem B9361817 : Blo 818347 9361817 := bstep (se 2 (by rfl) ⟨3510681, by rfl⟩ : syracuseStep 9361817 = 7021363) B7021363
theorem B23943755 : Blo 818347 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B5266205 : Blo 818347 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B5266433 : Blo 818347 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B1039483 : Blo 818347 1039483 := bstep (se 1 (by rfl) ⟨779612, by rfl⟩ : syracuseStep 1039483 = 1559225) B1559225
theorem B875719 : Blo 818347 875719 := bstep (se 1 (by rfl) ⟨656789, by rfl⟩ : syracuseStep 875719 = 1313579) B1313579
theorem B8871191 : Blo 818347 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B1039711 : Blo 818347 1039711 := bstep (se 1 (by rfl) ⟨779783, by rfl⟩ : syracuseStep 1039711 = 1559567) B1559567
theorem B2809529 : Blo 818347 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B4153031 : Blo 818347 4153031 := bstep (se 1 (by rfl) ⟨3114773, by rfl⟩ : syracuseStep 4153031 = 6229547) B6229547
theorem B1335145 : Blo 818347 1335145 := bstep (se 2 (by rfl) ⟨500679, by rfl⟩ : syracuseStep 1335145 = 1001359) B1001359
theorem B1040303 : Blo 818347 1040303 := bstep (se 1 (by rfl) ⟨780227, by rfl⟩ : syracuseStep 1040303 = 1560455) B1560455
theorem B10642283 : Blo 818347 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B7005203 : Blo 818347 7005203 := bstep (se 1 (by rfl) ⟨5253902, by rfl⟩ : syracuseStep 7005203 = 10507805) B10507805
theorem B1664057 : Blo 818347 1664057 := bstep (se 2 (by rfl) ⟨624021, by rfl⟩ : syracuseStep 1664057 = 1248043) B1248043
theorem B4679315 : Blo 818347 4679315 := bstep (se 1 (by rfl) ⟨3509486, by rfl⟩ : syracuseStep 4679315 = 7018973) B7018973
theorem B10512773 : Blo 818347 10512773 := bstep (se 4 (by rfl) ⟨985572, by rfl⟩ : syracuseStep 10512773 = 1971145) B1971145
theorem B6220313 : Blo 818347 6220313 := bstep (se 2 (by rfl) ⟨2332617, by rfl⟩ : syracuseStep 6220313 = 4665235) B4665235
theorem B3500603 : Blo 818347 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B4746167 : Blo 818347 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B3501251 : Blo 818347 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B6647165 : Blo 818347 6647165 := bstep (se 3 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 6647165 = 2492687) B2492687
theorem B3108563 : Blo 818347 3108563 := bstep (se 1 (by rfl) ⟨2331422, by rfl⟩ : syracuseStep 3108563 = 4662845) B4662845
theorem B11825027 : Blo 818347 11825027 := bstep (se 1 (by rfl) ⟨8868770, by rfl⟩ : syracuseStep 11825027 = 17737541) B17737541
theorem B8319547 : Blo 818347 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B7009199 : Blo 818347 7009199 := bstep (se 1 (by rfl) ⟨5256899, by rfl⟩ : syracuseStep 7009199 = 10513799) B10513799
theorem B12645341 : Blo 818347 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B6223229 : Blo 818347 6223229 := bstep (se 3 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 6223229 = 2333711) B2333711
theorem B4158863 : Blo 818347 4158863 := bstep (se 1 (by rfl) ⟨3119147, by rfl⟩ : syracuseStep 4158863 = 6238295) B6238295
theorem B3110993 : Blo 818347 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B8976541 : Blo 818347 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B1603795 : Blo 818347 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B14023043 : Blo 818347 14023043 := bstep (se 1 (by rfl) ⟨10517282, by rfl⟩ : syracuseStep 14023043 = 21034565) B21034565
theorem B3111311 : Blo 818347 3111311 := bstep (se 1 (by rfl) ⟨2333483, by rfl⟩ : syracuseStep 3111311 = 4666967) B4666967
theorem B1866451 : Blo 818347 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B818351 : Blo 818347 818351 := bstep (se 1 (by rfl) ⟨613763, by rfl⟩ : syracuseStep 818351 = 1227527) B1227527
theorem B818375 : Blo 818347 818375 := bstep (se 1 (by rfl) ⟨613781, by rfl⟩ : syracuseStep 818375 = 1227563) B1227563
theorem B818395 : Blo 818347 818395 := bstep (se 1 (by rfl) ⟨613796, by rfl⟩ : syracuseStep 818395 = 1227593) B1227593
theorem B818471 : Blo 818347 818471 := bstep (se 1 (by rfl) ⟨613853, by rfl⟩ : syracuseStep 818471 = 1227707) B1227707
theorem B3112253 : Blo 818347 3112253 := bstep (se 3 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 3112253 = 1167095) B1167095
theorem B818511 : Blo 818347 818511 := bstep (se 1 (by rfl) ⟨613883, by rfl⟩ : syracuseStep 818511 = 1227767) B1227767
theorem B818527 : Blo 818347 818527 := bstep (se 1 (by rfl) ⟨613895, by rfl⟩ : syracuseStep 818527 = 1227791) B1227791
theorem B818555 : Blo 818347 818555 := bstep (se 1 (by rfl) ⟨613916, by rfl⟩ : syracuseStep 818555 = 1227833) B1227833
theorem B818607 : Blo 818347 818607 := bstep (se 1 (by rfl) ⟨613955, by rfl⟩ : syracuseStep 818607 = 1227911) B1227911
theorem B818631 : Blo 818347 818631 := bstep (se 1 (by rfl) ⟨613973, by rfl⟩ : syracuseStep 818631 = 1227947) B1227947
theorem B4160969 : Blo 818347 4160969 := bstep (se 2 (by rfl) ⟨1560363, by rfl⟩ : syracuseStep 4160969 = 3120727) B3120727
theorem B818651 : Blo 818347 818651 := bstep (se 1 (by rfl) ⟨613988, by rfl⟩ : syracuseStep 818651 = 1227977) B1227977
theorem B818727 : Blo 818347 818727 := bstep (se 1 (by rfl) ⟨614045, by rfl⟩ : syracuseStep 818727 = 1228091) B1228091
theorem B818767 : Blo 818347 818767 := bstep (se 1 (by rfl) ⟨614075, by rfl⟩ : syracuseStep 818767 = 1228151) B1228151
theorem B818783 : Blo 818347 818783 := bstep (se 1 (by rfl) ⟨614087, by rfl⟩ : syracuseStep 818783 = 1228175) B1228175
theorem B818811 : Blo 818347 818811 := bstep (se 1 (by rfl) ⟨614108, by rfl⟩ : syracuseStep 818811 = 1228217) B1228217
theorem B818863 : Blo 818347 818863 := bstep (se 1 (by rfl) ⟨614147, by rfl⟩ : syracuseStep 818863 = 1228295) B1228295
theorem B818887 : Blo 818347 818887 := bstep (se 1 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 818887 = 1228331) B1228331
theorem B818907 : Blo 818347 818907 := bstep (se 1 (by rfl) ⟨614180, by rfl⟩ : syracuseStep 818907 = 1228361) B1228361
theorem B818983 : Blo 818347 818983 := bstep (se 1 (by rfl) ⟨614237, by rfl⟩ : syracuseStep 818983 = 1228475) B1228475
theorem B819023 : Blo 818347 819023 := bstep (se 1 (by rfl) ⟨614267, by rfl⟩ : syracuseStep 819023 = 1228535) B1228535
theorem B819039 : Blo 818347 819039 := bstep (se 1 (by rfl) ⟨614279, by rfl⟩ : syracuseStep 819039 = 1228559) B1228559
theorem B819067 : Blo 818347 819067 := bstep (se 1 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 819067 = 1228601) B1228601
theorem B819119 : Blo 818347 819119 := bstep (se 1 (by rfl) ⟨614339, by rfl⟩ : syracuseStep 819119 = 1228679) B1228679
theorem B819143 : Blo 818347 819143 := bstep (se 1 (by rfl) ⟨614357, by rfl⟩ : syracuseStep 819143 = 1228715) B1228715
theorem B819163 : Blo 818347 819163 := bstep (se 1 (by rfl) ⟨614372, by rfl⟩ : syracuseStep 819163 = 1228745) B1228745
theorem B7897189 : Blo 818347 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B819487 : Blo 818347 819487 := bstep (se 1 (by rfl) ⟨614615, by rfl⟩ : syracuseStep 819487 = 1229231) B1229231
theorem B819547 : Blo 818347 819547 := bstep (se 1 (by rfl) ⟨614660, by rfl⟩ : syracuseStep 819547 = 1229321) B1229321
theorem B1966447 : Blo 818347 1966447 := bstep (se 1 (by rfl) ⟨1474835, by rfl⟩ : syracuseStep 1966447 = 2949671) B2949671
theorem B819567 : Blo 818347 819567 := bstep (se 1 (by rfl) ⟨614675, by rfl⟩ : syracuseStep 819567 = 1229351) B1229351
theorem B14942627 : Blo 818347 14942627 := bstep (se 1 (by rfl) ⟨11206970, by rfl⟩ : syracuseStep 14942627 = 22413941) B22413941
theorem B819623 : Blo 818347 819623 := bstep (se 1 (by rfl) ⟨614717, by rfl⟩ : syracuseStep 819623 = 1229435) B1229435
theorem B3506651 : Blo 818347 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B819707 : Blo 818347 819707 := bstep (se 1 (by rfl) ⟨614780, by rfl⟩ : syracuseStep 819707 = 1229561) B1229561
theorem B819775 : Blo 818347 819775 := bstep (se 1 (by rfl) ⟨614831, by rfl⟩ : syracuseStep 819775 = 1229663) B1229663
theorem B819783 : Blo 818347 819783 := bstep (se 1 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 819783 = 1229675) B1229675
theorem B2949785 : Blo 818347 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1966763 : Blo 818347 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B819935 : Blo 818347 819935 := bstep (se 1 (by rfl) ⟨614951, by rfl⟩ : syracuseStep 819935 = 1229903) B1229903
theorem B820015 : Blo 818347 820015 := bstep (se 1 (by rfl) ⟨615011, by rfl⟩ : syracuseStep 820015 = 1230023) B1230023
theorem B820123 : Blo 818347 820123 := bstep (se 1 (by rfl) ⟨615092, by rfl⟩ : syracuseStep 820123 = 1230185) B1230185
theorem B3113923 : Blo 818347 3113923 := bstep (se 1 (by rfl) ⟨2335442, by rfl⟩ : syracuseStep 3113923 = 4670885) B4670885
theorem B820175 : Blo 818347 820175 := bstep (se 1 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 820175 = 1230263) B1230263
theorem B5243879 : Blo 818347 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B820199 : Blo 818347 820199 := bstep (se 1 (by rfl) ⟨615149, by rfl⟩ : syracuseStep 820199 = 1230299) B1230299
theorem B3114227 : Blo 818347 3114227 := bstep (se 1 (by rfl) ⟨2335670, by rfl⟩ : syracuseStep 3114227 = 4671341) B4671341
theorem B820511 : Blo 818347 820511 := bstep (se 1 (by rfl) ⟨615383, by rfl⟩ : syracuseStep 820511 = 1230767) B1230767
theorem B820571 : Blo 818347 820571 := bstep (se 1 (by rfl) ⟨615428, by rfl⟩ : syracuseStep 820571 = 1230857) B1230857
theorem B820591 : Blo 818347 820591 := bstep (se 1 (by rfl) ⟨615443, by rfl⟩ : syracuseStep 820591 = 1230887) B1230887
theorem B15795607 : Blo 818347 15795607 := bstep (se 1 (by rfl) ⟨11846705, by rfl⟩ : syracuseStep 15795607 = 23693411) B23693411
theorem B820647 : Blo 818347 820647 := bstep (se 1 (by rfl) ⟨615485, by rfl⟩ : syracuseStep 820647 = 1230971) B1230971
theorem B820731 : Blo 818347 820731 := bstep (se 1 (by rfl) ⟨615548, by rfl⟩ : syracuseStep 820731 = 1231097) B1231097
theorem B820799 : Blo 818347 820799 := bstep (se 1 (by rfl) ⟨615599, by rfl⟩ : syracuseStep 820799 = 1231199) B1231199
theorem B820807 : Blo 818347 820807 := bstep (se 1 (by rfl) ⟨615605, by rfl⟩ : syracuseStep 820807 = 1231211) B1231211
theorem B3114683 : Blo 818347 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B820959 : Blo 818347 820959 := bstep (se 1 (by rfl) ⟨615719, by rfl⟩ : syracuseStep 820959 = 1231439) B1231439
theorem B821039 : Blo 818347 821039 := bstep (se 1 (by rfl) ⟨615779, by rfl⟩ : syracuseStep 821039 = 1231559) B1231559
theorem B821147 : Blo 818347 821147 := bstep (se 1 (by rfl) ⟨615860, by rfl⟩ : syracuseStep 821147 = 1231721) B1231721
theorem B821199 : Blo 818347 821199 := bstep (se 1 (by rfl) ⟨615899, by rfl⟩ : syracuseStep 821199 = 1231799) B1231799
theorem B821223 : Blo 818347 821223 := bstep (se 1 (by rfl) ⟨615917, by rfl⟩ : syracuseStep 821223 = 1231835) B1231835
theorem B821535 : Blo 818347 821535 := bstep (se 1 (by rfl) ⟨616151, by rfl⟩ : syracuseStep 821535 = 1232303) B1232303
theorem B1968475 : Blo 818347 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B821595 : Blo 818347 821595 := bstep (se 1 (by rfl) ⟨616196, by rfl⟩ : syracuseStep 821595 = 1232393) B1232393
theorem B821615 : Blo 818347 821615 := bstep (se 1 (by rfl) ⟨616211, by rfl⟩ : syracuseStep 821615 = 1232423) B1232423
theorem B17729927 : Blo 818347 17729927 := bstep (se 1 (by rfl) ⟨13297445, by rfl⟩ : syracuseStep 17729927 = 26594891) B26594891
theorem B1968551 : Blo 818347 1968551 := bstep (se 1 (by rfl) ⟨1476413, by rfl⟩ : syracuseStep 1968551 = 2952827) B2952827
theorem B821671 : Blo 818347 821671 := bstep (se 1 (by rfl) ⟨616253, by rfl⟩ : syracuseStep 821671 = 1232507) B1232507
theorem B821755 : Blo 818347 821755 := bstep (se 1 (by rfl) ⟨616316, by rfl⟩ : syracuseStep 821755 = 1232633) B1232633
theorem B821823 : Blo 818347 821823 := bstep (se 1 (by rfl) ⟨616367, by rfl⟩ : syracuseStep 821823 = 1232735) B1232735
theorem B821831 : Blo 818347 821831 := bstep (se 1 (by rfl) ⟨616373, by rfl⟩ : syracuseStep 821831 = 1232747) B1232747
theorem B985775 : Blo 818347 985775 := bstep (se 1 (by rfl) ⟨739331, by rfl⟩ : syracuseStep 985775 = 1478663) B1478663
theorem B3934909 : Blo 818347 3934909 := bstep (se 3 (by rfl) ⟨737795, by rfl⟩ : syracuseStep 3934909 = 1475591) B1475591
theorem B821983 : Blo 818347 821983 := bstep (se 1 (by rfl) ⟨616487, by rfl⟩ : syracuseStep 821983 = 1232975) B1232975
theorem B2493175 : Blo 818347 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B822063 : Blo 818347 822063 := bstep (se 1 (by rfl) ⟨616547, by rfl⟩ : syracuseStep 822063 = 1233095) B1233095
theorem B822171 : Blo 818347 822171 := bstep (se 1 (by rfl) ⟨616628, by rfl⟩ : syracuseStep 822171 = 1233257) B1233257
theorem B822223 : Blo 818347 822223 := bstep (se 1 (by rfl) ⟨616667, by rfl⟩ : syracuseStep 822223 = 1233335) B1233335
theorem B822247 : Blo 818347 822247 := bstep (se 1 (by rfl) ⟨616685, by rfl⟩ : syracuseStep 822247 = 1233371) B1233371
theorem B2001959 : Blo 818347 2001959 := bstep (se 1 (by rfl) ⟨1501469, by rfl⟩ : syracuseStep 2001959 = 3002939) B3002939
theorem B3116171 : Blo 818347 3116171 := bstep (se 1 (by rfl) ⟨2337128, by rfl⟩ : syracuseStep 3116171 = 4674257) B4674257
theorem B2886943 : Blo 818347 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B51088765 : Blo 818347 51088765 := bstep (se 3 (by rfl) ⟨9579143, by rfl⟩ : syracuseStep 51088765 = 19158287) B19158287
theorem B4427207 : Blo 818347 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B23662043 : Blo 818347 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B3116627 : Blo 818347 3116627 := bstep (se 1 (by rfl) ⟨2337470, by rfl⟩ : syracuseStep 3116627 = 4674941) B4674941
theorem B2625119 : Blo 818347 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B5902595 : Blo 818347 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B15962503 : Blo 818347 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B3936737 : Blo 818347 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B3510803 : Blo 818347 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B922207 : Blo 818347 922207 := bstep (se 1 (by rfl) ⟨691655, by rfl⟩ : syracuseStep 922207 = 1383311) B1383311
theorem B3510955 : Blo 818347 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B36016969 : Blo 818347 36016969 := bstep (se 2 (by rfl) ⟨13506363, by rfl⟩ : syracuseStep 36016969 = 27012727) B27012727
theorem B1381367 : Blo 818347 1381367 := bstep (se 1 (by rfl) ⟨1036025, by rfl⟩ : syracuseStep 1381367 = 2072051) B2072051
theorem B1873019 : Blo 818347 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B11834525 : Blo 818347 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B923359 : Blo 818347 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B1382123 : Blo 818347 1382123 := bstep (se 1 (by rfl) ⟨1036592, by rfl⟩ : syracuseStep 1382123 = 2073185) B2073185
theorem B1841363 : Blo 818347 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B1841417 : Blo 818347 1841417 := bstep (se 2 (by rfl) ⟨690531, by rfl⟩ : syracuseStep 1841417 = 1381063) B1381063
theorem B2332937 : Blo 818347 2332937 := bstep (se 2 (by rfl) ⟨874851, by rfl⟩ : syracuseStep 2332937 = 1749703) B1749703
theorem B923935 : Blo 818347 923935 := bstep (se 1 (by rfl) ⟨692951, by rfl⟩ : syracuseStep 923935 = 1385903) B1385903
theorem B3119543 : Blo 818347 3119543 := bstep (se 1 (by rfl) ⟨2339657, by rfl⟩ : syracuseStep 3119543 = 4679315) B4679315
theorem B1841633 : Blo 818347 1841633 := bstep (se 2 (by rfl) ⟨690612, by rfl⟩ : syracuseStep 1841633 = 1381225) B1381225
theorem B2103803 : Blo 818347 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B15735329 : Blo 818347 15735329 := bstep (se 2 (by rfl) ⟨5900748, by rfl⟩ : syracuseStep 15735329 = 11801497) B11801497
theorem B924223 : Blo 818347 924223 := bstep (se 1 (by rfl) ⟨693167, by rfl⟩ : syracuseStep 924223 = 1386335) B1386335
theorem B1383095 : Blo 818347 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B5905133 : Blo 818347 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B1841939 : Blo 818347 1841939 := bstep (se 1 (by rfl) ⟨1381454, by rfl⟩ : syracuseStep 1841939 = 2762909) B2762909
theorem B1973011 : Blo 818347 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B2333735 : Blo 818347 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B1842299 : Blo 818347 1842299 := bstep (se 1 (by rfl) ⟨1381724, by rfl⟩ : syracuseStep 1842299 = 2763449) B2763449
theorem B1842425 : Blo 818347 1842425 := bstep (se 2 (by rfl) ⟨690909, by rfl⟩ : syracuseStep 1842425 = 1381819) B1381819
theorem B925051 : Blo 818347 925051 := bstep (se 1 (by rfl) ⟨693788, by rfl⟩ : syracuseStep 925051 = 1387577) B1387577
theorem B1842569 : Blo 818347 1842569 := bstep (se 2 (by rfl) ⟨690963, by rfl⟩ : syracuseStep 1842569 = 1381927) B1381927
theorem B1383817 : Blo 818347 1383817 := bstep (se 2 (by rfl) ⟨518931, by rfl⟩ : syracuseStep 1383817 = 1037863) B1037863
theorem B4988297 : Blo 818347 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B2334167 : Blo 818347 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1842695 : Blo 818347 1842695 := bstep (se 1 (by rfl) ⟨1382021, by rfl⟩ : syracuseStep 1842695 = 2764043) B2764043
theorem B4431443 : Blo 818347 4431443 := bstep (se 1 (by rfl) ⟨3323582, by rfl⟩ : syracuseStep 4431443 = 6647165) B6647165
theorem B3743347 : Blo 818347 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1842875 : Blo 818347 1842875 := bstep (se 1 (by rfl) ⟨1382156, by rfl⟩ : syracuseStep 1842875 = 2764313) B2764313
theorem B8888105 : Blo 818347 8888105 := bstep (se 2 (by rfl) ⟨3333039, by rfl⟩ : syracuseStep 8888105 = 6666079) B6666079
theorem B2072375 : Blo 818347 2072375 := bstep (se 1 (by rfl) ⟨1554281, by rfl⟩ : syracuseStep 2072375 = 3108563) B3108563
theorem B1843001 : Blo 818347 1843001 := bstep (se 2 (by rfl) ⟨691125, by rfl⟩ : syracuseStep 1843001 = 1382251) B1382251
theorem B2334521 : Blo 818347 2334521 := bstep (se 2 (by rfl) ⟨875445, by rfl⟩ : syracuseStep 2334521 = 1750891) B1750891
theorem B1384249 : Blo 818347 1384249 := bstep (se 2 (by rfl) ⟨519093, by rfl⟩ : syracuseStep 1384249 = 1038187) B1038187
theorem B2072425 : Blo 818347 2072425 := bstep (se 2 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 2072425 = 1554319) B1554319
theorem B1384553 : Blo 818347 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B11968721 : Blo 818347 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B2138393 : Blo 818347 2138393 := bstep (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) B1603795
theorem B1843631 : Blo 818347 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B1843667 : Blo 818347 1843667 := bstep (se 1 (by rfl) ⟨1382750, by rfl⟩ : syracuseStep 1843667 = 2765501) B2765501
theorem B1843775 : Blo 818347 1843775 := bstep (se 1 (by rfl) ⟨1382831, by rfl⟩ : syracuseStep 1843775 = 2765663) B2765663
theorem B8430227 : Blo 818347 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B1843883 : Blo 818347 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B1844423 : Blo 818347 1844423 := bstep (se 1 (by rfl) ⟨1383317, by rfl⟩ : syracuseStep 1844423 = 2766635) B2766635
theorem B2958551 : Blo 818347 2958551 := bstep (se 1 (by rfl) ⟨2218913, by rfl⟩ : syracuseStep 2958551 = 4437827) B4437827
theorem B2073833 : Blo 818347 2073833 := bstep (se 2 (by rfl) ⟨777687, by rfl⟩ : syracuseStep 2073833 = 1555375) B1555375
theorem B6235379 : Blo 818347 6235379 := bstep (se 1 (by rfl) ⟨4676534, by rfl⟩ : syracuseStep 6235379 = 9353069) B9353069
theorem B2630951 : Blo 818347 2630951 := bstep (se 1 (by rfl) ⟨1973213, by rfl⟩ : syracuseStep 2630951 = 3946427) B3946427
theorem B8529239 : Blo 818347 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B1844603 : Blo 818347 1844603 := bstep (se 1 (by rfl) ⟨1383452, by rfl⟩ : syracuseStep 1844603 = 2766905) B2766905
theorem B2073995 : Blo 818347 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B2336161 : Blo 818347 2336161 := bstep (se 2 (by rfl) ⟨876060, by rfl⟩ : syracuseStep 2336161 = 1752121) B1752121
theorem B1844729 : Blo 818347 1844729 := bstep (se 2 (by rfl) ⟨691773, by rfl⟩ : syracuseStep 1844729 = 1383547) B1383547
theorem B1385977 : Blo 818347 1385977 := bstep (se 2 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 1385977 = 1039483) B1039483
theorem B1844819 : Blo 818347 1844819 := bstep (se 1 (by rfl) ⟨1383614, by rfl⟩ : syracuseStep 1844819 = 2767229) B2767229
theorem B9348695 : Blo 818347 9348695 := bstep (se 1 (by rfl) ⟨7011521, by rfl⟩ : syracuseStep 9348695 = 14023043) B14023043
theorem B2074207 : Blo 818347 2074207 := bstep (se 1 (by rfl) ⟨1555655, by rfl⟩ : syracuseStep 2074207 = 3111311) B3111311
theorem B10233479 : Blo 818347 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B37856969 : Blo 818347 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B1844999 : Blo 818347 1844999 := bstep (se 1 (by rfl) ⟨1383749, by rfl⟩ : syracuseStep 1844999 = 2767499) B2767499
theorem B1386247 : Blo 818347 1386247 := bstep (se 1 (by rfl) ⟨1039685, by rfl⟩ : syracuseStep 1386247 = 2079371) B2079371
theorem B1386281 : Blo 818347 1386281 := bstep (se 2 (by rfl) ⟨519855, by rfl⟩ : syracuseStep 1386281 = 1039711) B1039711
theorem B4990825 : Blo 818347 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B2500559 : Blo 818347 2500559 := bstep (se 1 (by rfl) ⟨1875419, by rfl⟩ : syracuseStep 2500559 = 3750839) B3750839
theorem B4663277 : Blo 818347 4663277 := bstep (se 3 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 4663277 = 1748729) B1748729
theorem B2074835 : Blo 818347 2074835 := bstep (se 1 (by rfl) ⟨1556126, by rfl⟩ : syracuseStep 2074835 = 3112253) B3112253
theorem B2763017 : Blo 818347 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B2369801 : Blo 818347 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B20982077 : Blo 818347 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B1845611 : Blo 818347 1845611 := bstep (se 1 (by rfl) ⟨1384208, by rfl⟩ : syracuseStep 1845611 = 2768417) B2768417
theorem B11250049 : Blo 818347 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B1780193 : Blo 818347 1780193 := bstep (se 2 (by rfl) ⟨667572, by rfl⟩ : syracuseStep 1780193 = 1335145) B1335145
theorem B5253619 : Blo 818347 5253619 := bstep (se 1 (by rfl) ⟨3940214, by rfl⟩ : syracuseStep 5253619 = 7880429) B7880429
theorem B1845755 : Blo 818347 1845755 := bstep (se 1 (by rfl) ⟨1384316, by rfl⟩ : syracuseStep 1845755 = 2768633) B2768633
theorem B1387003 : Blo 818347 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B1845881 : Blo 818347 1845881 := bstep (se 2 (by rfl) ⟨692205, by rfl⟩ : syracuseStep 1845881 = 1384411) B1384411
theorem B1845935 : Blo 818347 1845935 := bstep (se 1 (by rfl) ⟨1384451, by rfl⟩ : syracuseStep 1845935 = 2768903) B2768903
theorem B1846007 : Blo 818347 1846007 := bstep (se 1 (by rfl) ⟨1384505, by rfl⟩ : syracuseStep 1846007 = 2769011) B2769011
theorem B1846187 : Blo 818347 1846187 := bstep (se 1 (by rfl) ⟨1384640, by rfl⟩ : syracuseStep 1846187 = 2769281) B2769281
theorem B1387435 : Blo 818347 1387435 := bstep (se 1 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 1387435 = 2081153) B2081153
theorem B6237323 : Blo 818347 6237323 := bstep (se 1 (by rfl) ⟨4677992, by rfl⟩ : syracuseStep 6237323 = 9355985) B9355985
theorem B830831 : Blo 818347 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B2764151 : Blo 818347 2764151 := bstep (se 1 (by rfl) ⟨2073113, by rfl⟩ : syracuseStep 2764151 = 4146227) B4146227
theorem B4730231 : Blo 818347 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B1846727 : Blo 818347 1846727 := bstep (se 1 (by rfl) ⟨1385045, by rfl⟩ : syracuseStep 1846727 = 2770091) B2770091
theorem B1748575 : Blo 818347 1748575 := bstep (se 1 (by rfl) ⟨1311431, by rfl⟩ : syracuseStep 1748575 = 2622863) B2622863
theorem B2993773 : Blo 818347 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B1847087 : Blo 818347 1847087 := bstep (se 1 (by rfl) ⟨1385315, by rfl⟩ : syracuseStep 1847087 = 2770631) B2770631
theorem B1847663 : Blo 818347 1847663 := bstep (se 1 (by rfl) ⟨1385747, by rfl⟩ : syracuseStep 1847663 = 2771495) B2771495
theorem B2765231 : Blo 818347 2765231 := bstep (se 1 (by rfl) ⟨2073923, by rfl⟩ : syracuseStep 2765231 = 4147847) B4147847
theorem B2077103 : Blo 818347 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B1847735 : Blo 818347 1847735 := bstep (se 1 (by rfl) ⟨1385801, by rfl⟩ : syracuseStep 1847735 = 2771603) B2771603
theorem B4207067 : Blo 818347 4207067 := bstep (se 1 (by rfl) ⟨3155300, by rfl⟩ : syracuseStep 4207067 = 6310601) B6310601
theorem B6238781 : Blo 818347 6238781 := bstep (se 3 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 6238781 = 2339543) B2339543
theorem B1847879 : Blo 818347 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1847915 : Blo 818347 1847915 := bstep (se 1 (by rfl) ⟨1385936, by rfl⟩ : syracuseStep 1847915 = 2771873) B2771873
theorem B1848311 : Blo 818347 1848311 := bstep (se 1 (by rfl) ⟨1386233, by rfl⟩ : syracuseStep 1848311 = 2772467) B2772467
theorem B4502585 : Blo 818347 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B3552607 : Blo 818347 3552607 := bstep (se 1 (by rfl) ⟨2664455, by rfl⟩ : syracuseStep 3552607 = 5328911) B5328911
theorem B1848671 : Blo 818347 1848671 := bstep (se 1 (by rfl) ⟨1386503, by rfl⟩ : syracuseStep 1848671 = 2773007) B2773007
theorem B2766203 : Blo 818347 2766203 := bstep (se 1 (by rfl) ⟨2074652, by rfl⟩ : syracuseStep 2766203 = 4149305) B4149305
theorem B2078075 : Blo 818347 2078075 := bstep (se 1 (by rfl) ⟨1558556, by rfl⟩ : syracuseStep 2078075 = 3117113) B3117113
theorem B2340409 : Blo 818347 2340409 := bstep (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) B1755307
theorem B2078369 : Blo 818347 2078369 := bstep (se 2 (by rfl) ⟨779388, by rfl⟩ : syracuseStep 2078369 = 1558777) B1558777
theorem B1849067 : Blo 818347 1849067 := bstep (se 1 (by rfl) ⟨1386800, by rfl⟩ : syracuseStep 1849067 = 2773601) B2773601
theorem B1849193 : Blo 818347 1849193 := bstep (se 2 (by rfl) ⟨693447, by rfl⟩ : syracuseStep 1849193 = 1386895) B1386895
theorem B9451493 : Blo 818347 9451493 := bstep (se 4 (by rfl) ⟨886077, by rfl⟩ : syracuseStep 9451493 = 1772155) B1772155
theorem B2079067 : Blo 818347 2079067 := bstep (se 1 (by rfl) ⟨1559300, by rfl⟩ : syracuseStep 2079067 = 3118601) B3118601
theorem B1850039 : Blo 818347 1850039 := bstep (se 1 (by rfl) ⟨1387529, by rfl⟩ : syracuseStep 1850039 = 2775059) B2775059
theorem B2767607 : Blo 818347 2767607 := bstep (se 1 (by rfl) ⟨2075705, by rfl⟩ : syracuseStep 2767607 = 4151411) B4151411
theorem B1227599 : Blo 818347 1227599 := bstep (se 1 (by rfl) ⟨920699, by rfl⟩ : syracuseStep 1227599 = 1841399) B1841399
theorem B1850255 : Blo 818347 1850255 := bstep (se 1 (by rfl) ⟨1387691, by rfl⟩ : syracuseStep 1850255 = 2775383) B2775383
theorem B6241211 : Blo 818347 6241211 := bstep (se 1 (by rfl) ⟨4680908, by rfl⟩ : syracuseStep 6241211 = 9361817) B9361817
theorem B1227995 : Blo 818347 1227995 := bstep (se 1 (by rfl) ⟨920996, by rfl⟩ : syracuseStep 1227995 = 1841993) B1841993
theorem B1752283 : Blo 818347 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B2080039 : Blo 818347 2080039 := bstep (se 1 (by rfl) ⟨1560029, by rfl⟩ : syracuseStep 2080039 = 3120059) B3120059
theorem B4144445 : Blo 818347 4144445 := bstep (se 3 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 4144445 = 1554167) B1554167
theorem B1228169 : Blo 818347 1228169 := bstep (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) B921127
theorem B5914127 : Blo 818347 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B2080313 : Blo 818347 2080313 := bstep (se 2 (by rfl) ⟨780117, by rfl⟩ : syracuseStep 2080313 = 1560235) B1560235
theorem B1228523 : Blo 818347 1228523 := bstep (se 1 (by rfl) ⟨921392, by rfl⟩ : syracuseStep 1228523 = 1842785) B1842785
theorem B2768687 : Blo 818347 2768687 := bstep (se 1 (by rfl) ⟨2076515, by rfl⟩ : syracuseStep 2768687 = 4153031) B4153031
theorem B1228751 : Blo 818347 1228751 := bstep (se 1 (by rfl) ⟨921563, by rfl⟩ : syracuseStep 1228751 = 1843127) B1843127
theorem B1229147 : Blo 818347 1229147 := bstep (se 1 (by rfl) ⟨921860, by rfl⟩ : syracuseStep 1229147 = 1843721) B1843721
theorem B1229375 : Blo 818347 1229375 := bstep (se 1 (by rfl) ⟨922031, by rfl⟩ : syracuseStep 1229375 = 1844063) B1844063
theorem B7094855 : Blo 818347 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B5915281 : Blo 818347 5915281 := bstep (se 2 (by rfl) ⟨2218230, by rfl⟩ : syracuseStep 5915281 = 4436461) B4436461
theorem B8110763 : Blo 818347 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B1229495 : Blo 818347 1229495 := bstep (se 1 (by rfl) ⟨922121, by rfl⟩ : syracuseStep 1229495 = 1844243) B1844243
theorem B4670135 : Blo 818347 4670135 := bstep (se 1 (by rfl) ⟨3502601, by rfl⟩ : syracuseStep 4670135 = 7005203) B7005203
theorem B11092729 : Blo 818347 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B1229723 : Blo 818347 1229723 := bstep (se 1 (by rfl) ⟨922292, by rfl⟩ : syracuseStep 1229723 = 1844585) B1844585
theorem B1230119 : Blo 818347 1230119 := bstep (se 1 (by rfl) ⟨922589, by rfl⟩ : syracuseStep 1230119 = 1845179) B1845179
theorem B1230203 : Blo 818347 1230203 := bstep (se 1 (by rfl) ⟨922652, by rfl⟩ : syracuseStep 1230203 = 1845305) B1845305
theorem B1230329 : Blo 818347 1230329 := bstep (se 2 (by rfl) ⟨461373, by rfl⟩ : syracuseStep 1230329 = 922747) B922747
theorem B1230431 : Blo 818347 1230431 := bstep (se 1 (by rfl) ⟨922823, by rfl⟩ : syracuseStep 1230431 = 1845647) B1845647
theorem B4146875 : Blo 818347 4146875 := bstep (se 1 (by rfl) ⟨3110156, by rfl⟩ : syracuseStep 4146875 = 6220313) B6220313
theorem B17778365 : Blo 818347 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B2213639 : Blo 818347 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B1230647 : Blo 818347 1230647 := bstep (se 1 (by rfl) ⟨922985, by rfl⟩ : syracuseStep 1230647 = 1845971) B1845971
theorem B2770793 : Blo 818347 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B3950441 : Blo 818347 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B3164111 : Blo 818347 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B2213993 : Blo 818347 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B1230953 : Blo 818347 1230953 := bstep (se 2 (by rfl) ⟨461607, by rfl⟩ : syracuseStep 1230953 = 923215) B923215
theorem B2771225 : Blo 818347 2771225 := bstep (se 2 (by rfl) ⟨1039209, by rfl⟩ : syracuseStep 2771225 = 2078419) B2078419
theorem B1231271 : Blo 818347 1231271 := bstep (se 1 (by rfl) ⟨923453, by rfl⟩ : syracuseStep 1231271 = 1846907) B1846907
theorem B1231355 : Blo 818347 1231355 := bstep (se 1 (by rfl) ⟨923516, by rfl⟩ : syracuseStep 1231355 = 1847033) B1847033
theorem B7883351 : Blo 818347 7883351 := bstep (se 1 (by rfl) ⟨5912513, by rfl⟩ : syracuseStep 7883351 = 11825027) B11825027
theorem B1231481 : Blo 818347 1231481 := bstep (se 2 (by rfl) ⟨461805, by rfl⟩ : syracuseStep 1231481 = 923611) B923611
theorem B1755769 : Blo 818347 1755769 := bstep (se 2 (by rfl) ⟨658413, by rfl⟩ : syracuseStep 1755769 = 1316827) B1316827
theorem B1231535 : Blo 818347 1231535 := bstep (se 1 (by rfl) ⟨923651, by rfl⟩ : syracuseStep 1231535 = 1847303) B1847303
theorem B1231583 : Blo 818347 1231583 := bstep (se 1 (by rfl) ⟨923687, by rfl⟩ : syracuseStep 1231583 = 1847375) B1847375
theorem B1559263 : Blo 818347 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B1231847 : Blo 818347 1231847 := bstep (se 1 (by rfl) ⟨923885, by rfl⟩ : syracuseStep 1231847 = 1847771) B1847771
theorem B1232105 : Blo 818347 1232105 := bstep (se 2 (by rfl) ⟨462039, by rfl⟩ : syracuseStep 1232105 = 924079) B924079
theorem B4672799 : Blo 818347 4672799 := bstep (se 1 (by rfl) ⟨3504599, by rfl⟩ : syracuseStep 4672799 = 7009199) B7009199
theorem B1232159 : Blo 818347 1232159 := bstep (se 1 (by rfl) ⟨924119, by rfl⟩ : syracuseStep 1232159 = 1848239) B1848239
theorem B1232327 : Blo 818347 1232327 := bstep (se 1 (by rfl) ⟨924245, by rfl⟩ : syracuseStep 1232327 = 1848491) B1848491
theorem B4148819 : Blo 818347 4148819 := bstep (se 1 (by rfl) ⟨3111614, by rfl⟩ : syracuseStep 4148819 = 6223229) B6223229
theorem B2772575 : Blo 818347 2772575 := bstep (se 1 (by rfl) ⟨2079431, by rfl⟩ : syracuseStep 2772575 = 4158863) B4158863
theorem B1232681 : Blo 818347 1232681 := bstep (se 2 (by rfl) ⟨462255, by rfl⟩ : syracuseStep 1232681 = 924511) B924511
theorem B1232687 : Blo 818347 1232687 := bstep (se 1 (by rfl) ⟨924515, by rfl⟩ : syracuseStep 1232687 = 1849031) B1849031
theorem B35508131 : Blo 818347 35508131 := bstep (se 1 (by rfl) ⟨26631098, by rfl⟩ : syracuseStep 35508131 = 53262197) B53262197
theorem B1167625 : Blo 818347 1167625 := bstep (se 2 (by rfl) ⟨437859, by rfl⟩ : syracuseStep 1167625 = 875719) B875719
theorem B1233161 : Blo 818347 1233161 := bstep (se 2 (by rfl) ⟨462435, by rfl⟩ : syracuseStep 1233161 = 924871) B924871
theorem B15749477 : Blo 818347 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B2806123 : Blo 818347 2806123 := bstep (se 1 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 2806123 = 4209185) B4209185
theorem B1233263 : Blo 818347 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B1036795 : Blo 818347 1036795 := bstep (se 1 (by rfl) ⟨777596, by rfl⟩ : syracuseStep 1036795 = 1555193) B1555193
theorem B2806343 : Blo 818347 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1233479 : Blo 818347 1233479 := bstep (se 1 (by rfl) ⟨925109, by rfl⟩ : syracuseStep 1233479 = 1850219) B1850219
theorem B1233515 : Blo 818347 1233515 := bstep (se 1 (by rfl) ⟨925136, by rfl⟩ : syracuseStep 1233515 = 1850273) B1850273
theorem B9982925 : Blo 818347 9982925 := bstep (se 3 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 9982925 = 3743597) B3743597
theorem B2773979 : Blo 818347 2773979 := bstep (se 1 (by rfl) ⟨2080484, by rfl⟩ : syracuseStep 2773979 = 4160969) B4160969
theorem B2774141 : Blo 818347 2774141 := bstep (se 3 (by rfl) ⟨520151, by rfl⟩ : syracuseStep 2774141 = 1040303) B1040303
theorem B2774249 : Blo 818347 2774249 := bstep (se 2 (by rfl) ⟨1040343, by rfl⟩ : syracuseStep 2774249 = 2080687) B2080687
theorem B7001477 : Blo 818347 7001477 := bstep (se 4 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 7001477 = 1312777) B1312777
theorem B2774411 : Blo 818347 2774411 := bstep (se 1 (by rfl) ⟨2080808, by rfl⟩ : syracuseStep 2774411 = 4161617) B4161617
theorem B1037767 : Blo 818347 1037767 := bstep (se 1 (by rfl) ⟨778325, by rfl⟩ : syracuseStep 1037767 = 1556651) B1556651
theorem B4675259 : Blo 818347 4675259 := bstep (se 1 (by rfl) ⟨3506444, by rfl⟩ : syracuseStep 4675259 = 7012889) B7012889
theorem B6215453 : Blo 818347 6215453 := bstep (se 3 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 6215453 = 2330795) B2330795
theorem B14014295 : Blo 818347 14014295 := bstep (se 1 (by rfl) ⟨10510721, by rfl⟩ : syracuseStep 14014295 = 21021443) B21021443
theorem B2250625 : Blo 818347 2250625 := bstep (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) B1687969
theorem B874783 : Blo 818347 874783 := bstep (se 1 (by rfl) ⟨656087, by rfl⟩ : syracuseStep 874783 = 1312175) B1312175
theorem B1038683 : Blo 818347 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B4151735 : Blo 818347 4151735 := bstep (se 1 (by rfl) ⟨3113801, by rfl⟩ : syracuseStep 4151735 = 6227603) B6227603
theorem B1039159 : Blo 818347 1039159 := bstep (se 1 (by rfl) ⟨779369, by rfl⟩ : syracuseStep 1039159 = 1558739) B1558739
theorem B1039655 : Blo 818347 1039655 := bstep (se 1 (by rfl) ⟨779741, by rfl⟩ : syracuseStep 1039655 = 1559483) B1559483
theorem B1039979 : Blo 818347 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B3497681 : Blo 818347 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B3333899 : Blo 818347 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B3497903 : Blo 818347 3497903 := bstep (se 1 (by rfl) ⟨2623427, by rfl⟩ : syracuseStep 3497903 = 5246855) B5246855
theorem B1040359 : Blo 818347 1040359 := bstep (se 1 (by rfl) ⟨780269, by rfl⟩ : syracuseStep 1040359 = 1560539) B1560539
theorem B14049287 : Blo 818347 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B4154003 : Blo 818347 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B4743851 : Blo 818347 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B47997845 : Blo 818347 47997845 := bstep (se 6 (by rfl) ⟨1124949, by rfl⟩ : syracuseStep 47997845 = 2249899) B2249899
theorem B4678631 : Blo 818347 4678631 := bstep (se 1 (by rfl) ⟨3508973, by rfl⟩ : syracuseStep 4678631 = 7017947) B7017947
theorem B2221195 : Blo 818347 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B4154813 : Blo 818347 4154813 := bstep (se 3 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 4154813 = 1558055) B1558055
theorem B11232857 : Blo 818347 11232857 := bstep (se 2 (by rfl) ⟨4212321, by rfl⟩ : syracuseStep 11232857 = 8424643) B8424643
theorem B3500279 : Blo 818347 3500279 := bstep (se 1 (by rfl) ⟨2625209, by rfl⟩ : syracuseStep 3500279 = 5250419) B5250419
theorem B19950259 : Blo 818347 19950259 := bstep (se 1 (by rfl) ⟨14962694, by rfl⟩ : syracuseStep 19950259 = 29925389) B29925389
theorem B3107879 : Blo 818347 3107879 := bstep (se 1 (by rfl) ⟨2330909, by rfl⟩ : syracuseStep 3107879 = 4661819) B4661819
theorem B1109371 : Blo 818347 1109371 := bstep (se 1 (by rfl) ⟨832028, by rfl⟩ : syracuseStep 1109371 = 1664057) B1664057
theorem B3501593 : Blo 818347 3501593 := bstep (se 2 (by rfl) ⟨1313097, by rfl⟩ : syracuseStep 3501593 = 2626195) B2626195
theorem B7008515 : Blo 818347 7008515 := bstep (se 1 (by rfl) ⟨5256386, by rfl⟩ : syracuseStep 7008515 = 10512773) B10512773
theorem B3110035 : Blo 818347 3110035 := bstep (se 1 (by rfl) ⟨2332526, by rfl⟩ : syracuseStep 3110035 = 4665053) B4665053
theorem B8877853 : Blo 818347 8877853 := bstep (se 3 (by rfl) ⟨1664597, by rfl⟩ : syracuseStep 8877853 = 3329195) B3329195
theorem B13301597 : Blo 818347 13301597 := bstep (se 3 (by rfl) ⟨2494049, by rfl⟩ : syracuseStep 13301597 = 4988099) B4988099
theorem B6912029 : Blo 818347 6912029 := bstep (se 3 (by rfl) ⟨1296005, by rfl⟩ : syracuseStep 6912029 = 2592011) B2592011
theorem B4159673 : Blo 818347 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B2488601 : Blo 818347 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B818463 : Blo 818347 818463 := bstep (se 1 (by rfl) ⟨613847, by rfl⟩ : syracuseStep 818463 = 1227695) B1227695
theorem B818523 : Blo 818347 818523 := bstep (se 1 (by rfl) ⟨613892, by rfl⟩ : syracuseStep 818523 = 1227785) B1227785
theorem B818543 : Blo 818347 818543 := bstep (se 1 (by rfl) ⟨613907, by rfl⟩ : syracuseStep 818543 = 1227815) B1227815
theorem B818599 : Blo 818347 818599 := bstep (se 1 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 818599 = 1227899) B1227899
theorem B818683 : Blo 818347 818683 := bstep (se 1 (by rfl) ⟨614012, by rfl⟩ : syracuseStep 818683 = 1228025) B1228025
theorem B818751 : Blo 818347 818751 := bstep (se 1 (by rfl) ⟨614063, by rfl⟩ : syracuseStep 818751 = 1228127) B1228127
theorem B818759 : Blo 818347 818759 := bstep (se 1 (by rfl) ⟨614069, by rfl⟩ : syracuseStep 818759 = 1228139) B1228139
theorem B818911 : Blo 818347 818911 := bstep (se 1 (by rfl) ⟨614183, by rfl⟩ : syracuseStep 818911 = 1228367) B1228367
theorem B818991 : Blo 818347 818991 := bstep (se 1 (by rfl) ⟨614243, by rfl⟩ : syracuseStep 818991 = 1228487) B1228487
theorem B3505967 : Blo 818347 3505967 := bstep (se 1 (by rfl) ⟨2629475, by rfl⟩ : syracuseStep 3505967 = 5258951) B5258951
theorem B819099 : Blo 818347 819099 := bstep (se 1 (by rfl) ⟨614324, by rfl⟩ : syracuseStep 819099 = 1228649) B1228649
theorem B4161455 : Blo 818347 4161455 := bstep (se 1 (by rfl) ⟨3121091, by rfl⟩ : syracuseStep 4161455 = 6242183) B6242183
theorem B819151 : Blo 818347 819151 := bstep (se 1 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 819151 = 1228727) B1228727
theorem B819175 : Blo 818347 819175 := bstep (se 1 (by rfl) ⟨614381, by rfl⟩ : syracuseStep 819175 = 1228763) B1228763
theorem B819431 : Blo 818347 819431 := bstep (se 1 (by rfl) ⟨614573, by rfl⟩ : syracuseStep 819431 = 1229147) B1229147
theorem B9961751 : Blo 818347 9961751 := bstep (se 1 (by rfl) ⟨7471313, by rfl⟩ : syracuseStep 9961751 = 14942627) B14942627
theorem B819583 : Blo 818347 819583 := bstep (se 1 (by rfl) ⟨614687, by rfl⟩ : syracuseStep 819583 = 1229375) B1229375
theorem B1966523 : Blo 818347 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B1311175 : Blo 818347 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B5407175 : Blo 818347 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B819663 : Blo 818347 819663 := bstep (se 1 (by rfl) ⟨614747, by rfl⟩ : syracuseStep 819663 = 1229495) B1229495
theorem B3113423 : Blo 818347 3113423 := bstep (se 1 (by rfl) ⟨2335067, by rfl⟩ : syracuseStep 3113423 = 4670135) B4670135
theorem B2621929 : Blo 818347 2621929 := bstep (se 2 (by rfl) ⟨983223, by rfl⟩ : syracuseStep 2621929 = 1966447) B1966447
theorem B819815 : Blo 818347 819815 := bstep (se 1 (by rfl) ⟨614861, by rfl⟩ : syracuseStep 819815 = 1229723) B1229723
theorem B5702381 : Blo 818347 5702381 := bstep (se 3 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 5702381 = 2138393) B2138393
theorem B820079 : Blo 818347 820079 := bstep (se 1 (by rfl) ⟨615059, by rfl⟩ : syracuseStep 820079 = 1230119) B1230119
theorem B820135 : Blo 818347 820135 := bstep (se 1 (by rfl) ⟨615101, by rfl⟩ : syracuseStep 820135 = 1230203) B1230203
theorem B820219 : Blo 818347 820219 := bstep (se 1 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 820219 = 1230329) B1230329
theorem B820287 : Blo 818347 820287 := bstep (se 1 (by rfl) ⟨615215, by rfl⟩ : syracuseStep 820287 = 1230431) B1230431
theorem B1475759 : Blo 818347 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B820431 : Blo 818347 820431 := bstep (se 1 (by rfl) ⟨615323, by rfl⟩ : syracuseStep 820431 = 1230647) B1230647
theorem B1475995 : Blo 818347 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B820635 : Blo 818347 820635 := bstep (se 1 (by rfl) ⟨615476, by rfl⟩ : syracuseStep 820635 = 1230953) B1230953
theorem B1312367 : Blo 818347 1312367 := bstep (se 1 (by rfl) ⟨984275, by rfl⟩ : syracuseStep 1312367 = 1968551) B1968551
theorem B820847 : Blo 818347 820847 := bstep (se 1 (by rfl) ⟨615635, by rfl⟩ : syracuseStep 820847 = 1231271) B1231271
theorem B820903 : Blo 818347 820903 := bstep (se 1 (by rfl) ⟨615677, by rfl⟩ : syracuseStep 820903 = 1231355) B1231355
theorem B820987 : Blo 818347 820987 := bstep (se 1 (by rfl) ⟨615740, by rfl⟩ : syracuseStep 820987 = 1231481) B1231481
theorem B12650269 : Blo 818347 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B821023 : Blo 818347 821023 := bstep (se 1 (by rfl) ⟨615767, by rfl⟩ : syracuseStep 821023 = 1231535) B1231535
theorem B821055 : Blo 818347 821055 := bstep (se 1 (by rfl) ⟨615791, by rfl⟩ : syracuseStep 821055 = 1231583) B1231583
theorem B3114881 : Blo 818347 3114881 := bstep (se 2 (by rfl) ⟨1168080, by rfl⟩ : syracuseStep 3114881 = 2336161) B2336161
theorem B821231 : Blo 818347 821231 := bstep (se 1 (by rfl) ⟨615923, by rfl⟩ : syracuseStep 821231 = 1231847) B1231847
theorem B821403 : Blo 818347 821403 := bstep (se 1 (by rfl) ⟨616052, by rfl⟩ : syracuseStep 821403 = 1232105) B1232105
theorem B3115199 : Blo 818347 3115199 := bstep (se 1 (by rfl) ⟨2336399, by rfl⟩ : syracuseStep 3115199 = 4672799) B4672799
theorem B821439 : Blo 818347 821439 := bstep (se 1 (by rfl) ⟨616079, by rfl⟩ : syracuseStep 821439 = 1232159) B1232159
theorem B2951471 : Blo 818347 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B821551 : Blo 818347 821551 := bstep (se 1 (by rfl) ⟨616163, by rfl⟩ : syracuseStep 821551 = 1232327) B1232327
theorem B6654433 : Blo 818347 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B821787 : Blo 818347 821787 := bstep (se 1 (by rfl) ⟨616340, by rfl⟩ : syracuseStep 821787 = 1232681) B1232681
theorem B821791 : Blo 818347 821791 := bstep (se 1 (by rfl) ⟨616343, by rfl⟩ : syracuseStep 821791 = 1232687) B1232687
theorem B3935063 : Blo 818347 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B822107 : Blo 818347 822107 := bstep (se 1 (by rfl) ⟨616580, by rfl⟩ : syracuseStep 822107 = 1233161) B1233161
theorem B822175 : Blo 818347 822175 := bstep (se 1 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 822175 = 1233263) B1233263
theorem B2624491 : Blo 818347 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B1870895 : Blo 818347 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B822319 : Blo 818347 822319 := bstep (se 1 (by rfl) ⟨616739, by rfl⟩ : syracuseStep 822319 = 1233479) B1233479
theorem B822343 : Blo 818347 822343 := bstep (se 1 (by rfl) ⟨616757, by rfl⟩ : syracuseStep 822343 = 1233515) B1233515
theorem B2624633 : Blo 818347 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B6655283 : Blo 818347 6655283 := bstep (se 1 (by rfl) ⟨4991462, by rfl⟩ : syracuseStep 6655283 = 9982925) B9982925
theorem B920911 : Blo 818347 920911 := bstep (se 1 (by rfl) ⟨690683, by rfl⟩ : syracuseStep 920911 = 1381367) B1381367
theorem B1248679 : Blo 818347 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B5246545 : Blo 818347 5246545 := bstep (se 2 (by rfl) ⟨1967454, by rfl⟩ : syracuseStep 5246545 = 3934909) B3934909
theorem B3116839 : Blo 818347 3116839 := bstep (se 1 (by rfl) ⟨2337629, by rfl⟩ : syracuseStep 3116839 = 4675259) B4675259
theorem B921415 : Blo 818347 921415 := bstep (se 1 (by rfl) ⟨691061, by rfl⟩ : syracuseStep 921415 = 1382123) B1382123
theorem B9342863 : Blo 818347 9342863 := bstep (se 1 (by rfl) ⟨7007147, by rfl⟩ : syracuseStep 9342863 = 14014295) B14014295
theorem B10490219 : Blo 818347 10490219 := bstep (se 1 (by rfl) ⟨7867664, by rfl⟩ : syracuseStep 10490219 = 15735329) B15735329
theorem B922063 : Blo 818347 922063 := bstep (se 1 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 922063 = 1383095) B1383095
theorem B3936755 : Blo 818347 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B1479161 : Blo 818347 1479161 := bstep (se 2 (by rfl) ⟨554685, by rfl⟩ : syracuseStep 1479161 = 1109371) B1109371
theorem B2331433 : Blo 818347 2331433 := bstep (se 2 (by rfl) ⟨874287, by rfl⟩ : syracuseStep 2331433 = 1748575) B1748575
theorem B2331787 : Blo 818347 2331787 := bstep (se 1 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 2331787 = 3497681) B3497681
theorem B1381583 : Blo 818347 1381583 := bstep (se 1 (by rfl) ⟨1036187, by rfl⟩ : syracuseStep 1381583 = 2072375) B2072375
theorem B2331935 : Blo 818347 2331935 := bstep (se 1 (by rfl) ⟨1748951, by rfl⟩ : syracuseStep 2331935 = 3497903) B3497903
theorem B923035 : Blo 818347 923035 := bstep (se 1 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 923035 = 1384553) B1384553
theorem B3741497 : Blo 818347 3741497 := bstep (se 2 (by rfl) ⟨1403061, by rfl⟩ : syracuseStep 3741497 = 2806123) B2806123
theorem B3119087 : Blo 818347 3119087 := bstep (se 1 (by rfl) ⟨2339315, by rfl⟩ : syracuseStep 3119087 = 4678631) B4678631
theorem B1382393 : Blo 818347 1382393 := bstep (se 2 (by rfl) ⟨518397, by rfl⟩ : syracuseStep 1382393 = 1036795) B1036795
theorem B1972367 : Blo 818347 1972367 := bstep (se 1 (by rfl) ⟨1479275, by rfl⟩ : syracuseStep 1972367 = 2958551) B2958551
theorem B1382555 : Blo 818347 1382555 := bstep (se 1 (by rfl) ⟨1036916, by rfl⟩ : syracuseStep 1382555 = 2073833) B2073833
theorem B1382663 : Blo 818347 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B6232463 : Blo 818347 6232463 := bstep (se 1 (by rfl) ⟨4674347, by rfl⟩ : syracuseStep 6232463 = 9348695) B9348695
theorem B6822319 : Blo 818347 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B25237979 : Blo 818347 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B924187 : Blo 818347 924187 := bstep (se 1 (by rfl) ⟨693140, by rfl⟩ : syracuseStep 924187 = 1386281) B1386281
theorem B1383223 : Blo 818347 1383223 := bstep (se 1 (by rfl) ⟨1037417, by rfl⟩ : syracuseStep 1383223 = 2074835) B2074835
theorem B2333519 : Blo 818347 2333519 := bstep (se 1 (by rfl) ⟨1750139, by rfl⟩ : syracuseStep 2333519 = 3500279) B3500279
theorem B1842011 : Blo 818347 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B1579867 : Blo 818347 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B1186795 : Blo 818347 1186795 := bstep (se 1 (by rfl) ⟨890096, by rfl⟩ : syracuseStep 1186795 = 1780193) B1780193
theorem B2628733 : Blo 818347 2628733 := bstep (se 3 (by rfl) ⟨492887, by rfl⟩ : syracuseStep 2628733 = 985775) B985775
theorem B1383689 : Blo 818347 1383689 := bstep (se 2 (by rfl) ⟨518883, by rfl⟩ : syracuseStep 1383689 = 1037767) B1037767
theorem B2071919 : Blo 818347 2071919 := bstep (se 1 (by rfl) ⟨1553939, by rfl⟩ : syracuseStep 2071919 = 3107879) B3107879
theorem B3120545 : Blo 818347 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B1842767 : Blo 818347 1842767 := bstep (se 1 (by rfl) ⟨1382075, by rfl⟩ : syracuseStep 1842767 = 2764151) B2764151
theorem B3153487 : Blo 818347 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B2334395 : Blo 818347 2334395 := bstep (se 1 (by rfl) ⟨1750796, by rfl⟩ : syracuseStep 2334395 = 3501593) B3501593
theorem B11837137 : Blo 818347 11837137 := bstep (se 2 (by rfl) ⟨4438926, by rfl⟩ : syracuseStep 11837137 = 8877853) B8877853
theorem B1843487 : Blo 818347 1843487 := bstep (se 1 (by rfl) ⟨1382615, by rfl⟩ : syracuseStep 1843487 = 2765231) B2765231
theorem B1384735 : Blo 818347 1384735 := bstep (se 1 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 1384735 = 2077103) B2077103
theorem B1844135 : Blo 818347 1844135 := bstep (se 1 (by rfl) ⟨1383101, by rfl⟩ : syracuseStep 1844135 = 2766203) B2766203
theorem B1385383 : Blo 818347 1385383 := bstep (se 1 (by rfl) ⟨1039037, by rfl⟩ : syracuseStep 1385383 = 2078075) B2078075
theorem B2630681 : Blo 818347 2630681 := bstep (se 2 (by rfl) ⟨986505, by rfl⟩ : syracuseStep 2630681 = 1973011) B1973011
theorem B1385545 : Blo 818347 1385545 := bstep (se 2 (by rfl) ⟨519579, by rfl⟩ : syracuseStep 1385545 = 1039159) B1039159
theorem B1385579 : Blo 818347 1385579 := bstep (se 1 (by rfl) ⟨1039184, by rfl⟩ : syracuseStep 1385579 = 2078369) B2078369
theorem B6300995 : Blo 818347 6300995 := bstep (se 1 (by rfl) ⟨4725746, by rfl⟩ : syracuseStep 6300995 = 9451493) B9451493
theorem B2336377 : Blo 818347 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B1845071 : Blo 818347 1845071 := bstep (se 1 (by rfl) ⟨1383803, by rfl⟩ : syracuseStep 1845071 = 2767607) B2767607
theorem B1845089 : Blo 818347 1845089 := bstep (se 2 (by rfl) ⟨691908, by rfl⟩ : syracuseStep 1845089 = 1383817) B1383817
theorem B8890397 : Blo 818347 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B4991129 : Blo 818347 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B2762963 : Blo 818347 2762963 := bstep (se 1 (by rfl) ⟨2072222, by rfl⟩ : syracuseStep 2762963 = 4144445) B4144445
theorem B3942751 : Blo 818347 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B1386875 : Blo 818347 1386875 := bstep (se 1 (by rfl) ⟨1040156, by rfl⟩ : syracuseStep 1386875 = 2080313) B2080313
theorem B1845665 : Blo 818347 1845665 := bstep (se 2 (by rfl) ⟨692124, by rfl⟩ : syracuseStep 1845665 = 1384249) B1384249
theorem B2763233 : Blo 818347 2763233 := bstep (se 2 (by rfl) ⟨1036212, by rfl⟩ : syracuseStep 2763233 = 2072425) B2072425
theorem B1845791 : Blo 818347 1845791 := bstep (se 1 (by rfl) ⟨1384343, by rfl⟩ : syracuseStep 1845791 = 2768687) B2768687
theorem B2337311 : Blo 818347 2337311 := bstep (se 1 (by rfl) ⟨1752983, by rfl⟩ : syracuseStep 2337311 = 3505967) B3505967
theorem B1387145 : Blo 818347 1387145 := bstep (se 2 (by rfl) ⟨520179, by rfl⟩ : syracuseStep 1387145 = 1040359) B1040359
theorem B10529585 : Blo 818347 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B2337767 : Blo 818347 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B4729903 : Blo 818347 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B2076151 : Blo 818347 2076151 := bstep (se 1 (by rfl) ⟨1557113, by rfl⟩ : syracuseStep 2076151 = 3114227) B3114227
theorem B14790305 : Blo 818347 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B2764583 : Blo 818347 2764583 := bstep (se 1 (by rfl) ⟨2073437, by rfl⟩ : syracuseStep 2764583 = 4146875) B4146875
theorem B2076455 : Blo 818347 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B1847195 : Blo 818347 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B2633627 : Blo 818347 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B2109407 : Blo 818347 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B4665509 : Blo 818347 4665509 := bstep (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) B874783
theorem B2961593 : Blo 818347 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B1847483 : Blo 818347 1847483 := bstep (se 1 (by rfl) ⟨1385612, by rfl⟩ : syracuseStep 1847483 = 2771225) B2771225
theorem B5255567 : Blo 818347 5255567 := bstep (se 1 (by rfl) ⟨3941675, by rfl⟩ : syracuseStep 5255567 = 7883351) B7883351
theorem B1847969 : Blo 818347 1847969 := bstep (se 2 (by rfl) ⟨692988, by rfl⟩ : syracuseStep 1847969 = 1385977) B1385977
theorem B2077447 : Blo 818347 2077447 := bstep (se 1 (by rfl) ⟨1558085, by rfl⟩ : syracuseStep 2077447 = 3116171) B3116171
theorem B2765609 : Blo 818347 2765609 := bstep (se 2 (by rfl) ⟨1037103, by rfl⟩ : syracuseStep 2765609 = 2074207) B2074207
theorem B15774695 : Blo 818347 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B1848329 : Blo 818347 1848329 := bstep (se 2 (by rfl) ⟨693123, by rfl⟩ : syracuseStep 1848329 = 1386247) B1386247
theorem B2765879 : Blo 818347 2765879 := bstep (se 1 (by rfl) ⟨2074409, by rfl⟩ : syracuseStep 2765879 = 4148819) B4148819
theorem B2077751 : Blo 818347 2077751 := bstep (se 1 (by rfl) ⟨1558313, by rfl⟩ : syracuseStep 2077751 = 3116627) B3116627
theorem B1750079 : Blo 818347 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B1848383 : Blo 818347 1848383 := bstep (se 1 (by rfl) ⟨1386287, by rfl⟩ : syracuseStep 1848383 = 2772575) B2772575
theorem B23672087 : Blo 818347 23672087 := bstep (se 1 (by rfl) ⟨17754065, by rfl⟩ : syracuseStep 23672087 = 35508131) B35508131
theorem B12006893 : Blo 818347 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B10499651 : Blo 818347 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B2340535 : Blo 818347 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B1849319 : Blo 818347 1849319 := bstep (se 1 (by rfl) ⟨1386989, by rfl⟩ : syracuseStep 1849319 = 2773979) B2773979
theorem B1849337 : Blo 818347 1849337 := bstep (se 2 (by rfl) ⟨693501, by rfl⟩ : syracuseStep 1849337 = 1387003) B1387003
theorem B1849427 : Blo 818347 1849427 := bstep (se 1 (by rfl) ⟨1387070, by rfl⟩ : syracuseStep 1849427 = 2774141) B2774141
theorem B1849499 : Blo 818347 1849499 := bstep (se 1 (by rfl) ⟨1387124, by rfl⟩ : syracuseStep 1849499 = 2774249) B2774249
theorem B2341025 : Blo 818347 2341025 := bstep (se 2 (by rfl) ⟨877884, by rfl⟩ : syracuseStep 2341025 = 1755769) B1755769
theorem B4667651 : Blo 818347 4667651 := bstep (se 1 (by rfl) ⟨3500738, by rfl⟩ : syracuseStep 4667651 = 7001477) B7001477
theorem B1849607 : Blo 818347 1849607 := bstep (se 1 (by rfl) ⟨1387205, by rfl⟩ : syracuseStep 1849607 = 2774411) B2774411
theorem B2079017 : Blo 818347 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B3324233 : Blo 818347 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B4143635 : Blo 818347 4143635 := bstep (se 1 (by rfl) ⟨3107726, by rfl⟩ : syracuseStep 4143635 = 6215453) B6215453
theorem B1849913 : Blo 818347 1849913 := bstep (se 2 (by rfl) ⟨693717, by rfl⟩ : syracuseStep 1849913 = 1387435) B1387435
theorem B1227575 : Blo 818347 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B1227611 : Blo 818347 1227611 := bstep (se 1 (by rfl) ⟨920708, by rfl⟩ : syracuseStep 1227611 = 1841417) B1841417
theorem B1555291 : Blo 818347 1555291 := bstep (se 1 (by rfl) ⟨1166468, by rfl⟩ : syracuseStep 1555291 = 2332937) B2332937
theorem B2767823 : Blo 818347 2767823 := bstep (se 1 (by rfl) ⟨2075867, by rfl⟩ : syracuseStep 2767823 = 4151735) B4151735
theorem B2079695 : Blo 818347 2079695 := bstep (se 1 (by rfl) ⟨1559771, by rfl⟩ : syracuseStep 2079695 = 3119543) B3119543
theorem B1227755 : Blo 818347 1227755 := bstep (se 1 (by rfl) ⟨920816, by rfl⟩ : syracuseStep 1227755 = 1841633) B1841633
theorem B3849257 : Blo 818347 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1227959 : Blo 818347 1227959 := bstep (se 1 (by rfl) ⟨920969, by rfl⟩ : syracuseStep 1227959 = 1841939) B1841939
theorem B1555823 : Blo 818347 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B1228199 : Blo 818347 1228199 := bstep (se 1 (by rfl) ⟨921149, by rfl⟩ : syracuseStep 1228199 = 1842299) B1842299
theorem B1228283 : Blo 818347 1228283 := bstep (se 1 (by rfl) ⟨921212, by rfl⟩ : syracuseStep 1228283 = 1842425) B1842425
theorem B1228379 : Blo 818347 1228379 := bstep (se 1 (by rfl) ⟨921284, by rfl⟩ : syracuseStep 1228379 = 1842569) B1842569
theorem B3325531 : Blo 818347 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B1556111 : Blo 818347 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1228463 : Blo 818347 1228463 := bstep (se 1 (by rfl) ⟨921347, by rfl⟩ : syracuseStep 1228463 = 1842695) B1842695
theorem B1228583 : Blo 818347 1228583 := bstep (se 1 (by rfl) ⟨921437, by rfl⟩ : syracuseStep 1228583 = 1842875) B1842875
theorem B1228667 : Blo 818347 1228667 := bstep (se 1 (by rfl) ⟨921500, by rfl⟩ : syracuseStep 1228667 = 1843001) B1843001
theorem B1556347 : Blo 818347 1556347 := bstep (se 1 (by rfl) ⟨1167260, by rfl⟩ : syracuseStep 1556347 = 2334521) B2334521
theorem B7979147 : Blo 818347 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1229087 : Blo 818347 1229087 := bstep (se 1 (by rfl) ⟨921815, by rfl⟩ : syracuseStep 1229087 = 1843631) B1843631
theorem B1229111 : Blo 818347 1229111 := bstep (se 1 (by rfl) ⟨921833, by rfl⟩ : syracuseStep 1229111 = 1843667) B1843667
theorem B1556833 : Blo 818347 1556833 := bstep (se 2 (by rfl) ⟨583812, by rfl⟩ : syracuseStep 1556833 = 1167625) B1167625
theorem B1229183 : Blo 818347 1229183 := bstep (se 1 (by rfl) ⟨921887, by rfl⟩ : syracuseStep 1229183 = 1843775) B1843775
theorem B2769335 : Blo 818347 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B5620151 : Blo 818347 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B1229255 : Blo 818347 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B21283337 : Blo 818347 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B31998563 : Blo 818347 31998563 := bstep (se 1 (by rfl) ⟨23998922, by rfl⟩ : syracuseStep 31998563 = 47997845) B47997845
theorem B6636269 : Blo 818347 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B1229609 : Blo 818347 1229609 := bstep (se 2 (by rfl) ⟨461103, by rfl⟩ : syracuseStep 1229609 = 922207) B922207
theorem B1229615 : Blo 818347 1229615 := bstep (se 1 (by rfl) ⟨922211, by rfl⟩ : syracuseStep 1229615 = 1844423) B1844423
theorem B1753967 : Blo 818347 1753967 := bstep (se 1 (by rfl) ⟨1315475, by rfl⟩ : syracuseStep 1753967 = 2630951) B2630951
theorem B5686159 : Blo 818347 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B2769821 : Blo 818347 2769821 := bstep (se 3 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 2769821 = 1038683) B1038683
theorem B1229735 : Blo 818347 1229735 := bstep (se 1 (by rfl) ⟨922301, by rfl⟩ : syracuseStep 1229735 = 1844603) B1844603
theorem B2769875 : Blo 818347 2769875 := bstep (se 1 (by rfl) ⟨2077406, by rfl⟩ : syracuseStep 2769875 = 4154813) B4154813
theorem B1229819 : Blo 818347 1229819 := bstep (se 1 (by rfl) ⟨922364, by rfl⟩ : syracuseStep 1229819 = 1844729) B1844729
theorem B1229879 : Blo 818347 1229879 := bstep (se 1 (by rfl) ⟨922409, by rfl⟩ : syracuseStep 1229879 = 1844819) B1844819
theorem B7488571 : Blo 818347 7488571 := bstep (se 1 (by rfl) ⟨5616428, by rfl⟩ : syracuseStep 7488571 = 11232857) B11232857
theorem B48022625 : Blo 818347 48022625 := bstep (se 2 (by rfl) ⟨18008484, by rfl⟩ : syracuseStep 48022625 = 36016969) B36016969
theorem B1229999 : Blo 818347 1229999 := bstep (se 1 (by rfl) ⟨922499, by rfl⟩ : syracuseStep 1229999 = 1844999) B1844999
theorem B4146713 : Blo 818347 4146713 := bstep (se 2 (by rfl) ⟨1555017, by rfl⟩ : syracuseStep 4146713 = 3110035) B3110035
theorem B1230407 : Blo 818347 1230407 := bstep (se 1 (by rfl) ⟨922805, by rfl⟩ : syracuseStep 1230407 = 1845611) B1845611
theorem B1230503 : Blo 818347 1230503 := bstep (se 1 (by rfl) ⟨922877, by rfl⟩ : syracuseStep 1230503 = 1845755) B1845755
theorem B1230587 : Blo 818347 1230587 := bstep (se 1 (by rfl) ⟨922940, by rfl⟩ : syracuseStep 1230587 = 1845881) B1845881
theorem B1230623 : Blo 818347 1230623 := bstep (se 1 (by rfl) ⟨922967, by rfl⟩ : syracuseStep 1230623 = 1845935) B1845935
theorem B4736809 : Blo 818347 4736809 := bstep (se 2 (by rfl) ⟨1776303, by rfl⟩ : syracuseStep 4736809 = 3552607) B3552607
theorem B1230671 : Blo 818347 1230671 := bstep (se 1 (by rfl) ⟨923003, by rfl⟩ : syracuseStep 1230671 = 1846007) B1846007
theorem B1230791 : Blo 818347 1230791 := bstep (se 1 (by rfl) ⟨923093, by rfl⟩ : syracuseStep 1230791 = 1846187) B1846187
theorem B1231145 : Blo 818347 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B1231151 : Blo 818347 1231151 := bstep (se 1 (by rfl) ⟨923363, by rfl⟩ : syracuseStep 1231151 = 1846727) B1846727
theorem B3000833 : Blo 818347 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B1231391 : Blo 818347 1231391 := bstep (se 1 (by rfl) ⟨923543, by rfl⟩ : syracuseStep 1231391 = 1847087) B1847087
theorem B4672343 : Blo 818347 4672343 := bstep (se 1 (by rfl) ⟨3504257, by rfl⟩ : syracuseStep 4672343 = 7008515) B7008515
theorem B1231775 : Blo 818347 1231775 := bstep (se 1 (by rfl) ⟨923831, by rfl⟩ : syracuseStep 1231775 = 1847663) B1847663
theorem B1231823 : Blo 818347 1231823 := bstep (se 1 (by rfl) ⟨923867, by rfl⟩ : syracuseStep 1231823 = 1847735) B1847735
theorem B2804711 : Blo 818347 2804711 := bstep (se 1 (by rfl) ⟨2103533, by rfl⟩ : syracuseStep 2804711 = 4207067) B4207067
theorem B1231913 : Blo 818347 1231913 := bstep (se 2 (by rfl) ⟨461967, by rfl⟩ : syracuseStep 1231913 = 923935) B923935
theorem B1231919 : Blo 818347 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B1231943 : Blo 818347 1231943 := bstep (se 1 (by rfl) ⟨923957, by rfl⟩ : syracuseStep 1231943 = 1847915) B1847915
theorem B2772089 : Blo 818347 2772089 := bstep (se 2 (by rfl) ⟨1039533, by rfl⟩ : syracuseStep 2772089 = 2079067) B2079067
theorem B1232207 : Blo 818347 1232207 := bstep (se 1 (by rfl) ⟨924155, by rfl⟩ : syracuseStep 1232207 = 1848311) B1848311
theorem B1232297 : Blo 818347 1232297 := bstep (se 2 (by rfl) ⟨462111, by rfl⟩ : syracuseStep 1232297 = 924223) B924223
theorem B2772413 : Blo 818347 2772413 := bstep (se 3 (by rfl) ⟨519827, by rfl⟩ : syracuseStep 2772413 = 1039655) B1039655
theorem B1232447 : Blo 818347 1232447 := bstep (se 1 (by rfl) ⟨924335, by rfl⟩ : syracuseStep 1232447 = 1848671) B1848671
theorem B2215549 : Blo 818347 2215549 := bstep (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) B830831
theorem B1232711 : Blo 818347 1232711 := bstep (se 1 (by rfl) ⟨924533, by rfl⟩ : syracuseStep 1232711 = 1849067) B1849067
theorem B8867731 : Blo 818347 8867731 := bstep (se 1 (by rfl) ⟨6650798, by rfl⟩ : syracuseStep 8867731 = 13301597) B13301597
theorem B1232795 : Blo 818347 1232795 := bstep (se 1 (by rfl) ⟨924596, by rfl⟩ : syracuseStep 1232795 = 1849193) B1849193
theorem B4608019 : Blo 818347 4608019 := bstep (se 1 (by rfl) ⟨3456014, by rfl⟩ : syracuseStep 4608019 = 6912029) B6912029
theorem B2773115 : Blo 818347 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B11817181 : Blo 818347 11817181 := bstep (se 3 (by rfl) ⟨2215721, by rfl⟩ : syracuseStep 11817181 = 4431443) B4431443
theorem B2773277 : Blo 818347 2773277 := bstep (se 3 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 2773277 = 1039979) B1039979
theorem B2773385 : Blo 818347 2773385 := bstep (se 2 (by rfl) ⟨1040019, by rfl⟩ : syracuseStep 2773385 = 2080039) B2080039
theorem B1233359 : Blo 818347 1233359 := bstep (se 1 (by rfl) ⟨925019, by rfl⟩ : syracuseStep 1233359 = 1850039) B1850039
theorem B1233401 : Blo 818347 1233401 := bstep (se 2 (by rfl) ⟨462525, by rfl⟩ : syracuseStep 1233401 = 925051) B925051
theorem B1233503 : Blo 818347 1233503 := bstep (se 1 (by rfl) ⟨925127, by rfl⟩ : syracuseStep 1233503 = 1850255) B1850255
theorem B2774303 : Blo 818347 2774303 := bstep (se 1 (by rfl) ⟨2080727, by rfl⟩ : syracuseStep 2774303 = 4161455) B4161455
theorem B7887041 : Blo 818347 7887041 := bstep (se 2 (by rfl) ⟨2957640, by rfl⟩ : syracuseStep 7887041 = 5915281) B5915281
theorem B11852243 : Blo 818347 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B4151897 : Blo 818347 4151897 := bstep (se 2 (by rfl) ⟨1556961, by rfl⟩ : syracuseStep 4151897 = 3113923) B3113923
theorem B11819951 : Blo 818347 11819951 := bstep (se 1 (by rfl) ⟨8864963, by rfl⟩ : syracuseStep 11819951 = 17729927) B17729927
theorem B21060809 : Blo 818347 21060809 := bstep (se 2 (by rfl) ⟨7897803, by rfl⟩ : syracuseStep 21060809 = 15795607) B15795607
theorem B1334639 : Blo 818347 1334639 := bstep (se 1 (by rfl) ⟨1000979, by rfl⟩ : syracuseStep 1334639 = 2001959) B2001959
theorem B13983677 : Blo 818347 13983677 := bstep (se 3 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 13983677 = 5243879) B5243879
theorem B15000065 : Blo 818347 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B7004825 : Blo 818347 7004825 := bstep (se 2 (by rfl) ⟨2626809, by rfl⟩ : syracuseStep 7004825 = 5253619) B5253619
theorem B7889683 : Blo 818347 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B26600345 : Blo 818347 26600345 := bstep (se 2 (by rfl) ⟨9975129, by rfl⟩ : syracuseStep 26600345 = 19950259) B19950259
theorem B1402535 : Blo 818347 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B68118353 : Blo 818347 68118353 := bstep (se 2 (by rfl) ⟨25544382, by rfl⟩ : syracuseStep 68118353 = 51088765) B51088765
theorem B3991697 : Blo 818347 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B5925403 : Blo 818347 5925403 := bstep (se 1 (by rfl) ⟨4444052, by rfl⟩ : syracuseStep 5925403 = 8888105) B8888105
theorem B9366191 : Blo 818347 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B4156919 : Blo 818347 4156919 := bstep (se 1 (by rfl) ⟨3117689, by rfl⟩ : syracuseStep 4156919 = 6235379) B6235379
theorem B4681273 : Blo 818347 4681273 := bstep (se 2 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 4681273 = 3510955) B3510955
theorem B1667039 : Blo 818347 1667039 := bstep (se 1 (by rfl) ⟨1250279, by rfl⟩ : syracuseStep 1667039 = 2500559) B2500559
theorem B3108851 : Blo 818347 3108851 := bstep (se 1 (by rfl) ⟨2331638, by rfl⟩ : syracuseStep 3108851 = 4663277) B4663277
theorem B13988051 : Blo 818347 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B4158215 : Blo 818347 4158215 := bstep (se 1 (by rfl) ⟨3118661, by rfl⟩ : syracuseStep 4158215 = 6237323) B6237323
theorem B4159187 : Blo 818347 4159187 := bstep (se 1 (by rfl) ⟨3119390, by rfl⟩ : syracuseStep 4159187 = 6238781) B6238781
theorem B818399 : Blo 818347 818399 := bstep (se 1 (by rfl) ⟨613799, by rfl⟩ : syracuseStep 818399 = 1227599) B1227599
theorem B4160807 : Blo 818347 4160807 := bstep (se 1 (by rfl) ⟨3120605, by rfl⟩ : syracuseStep 4160807 = 6241211) B6241211
theorem B818663 : Blo 818347 818663 := bstep (se 1 (by rfl) ⟨613997, by rfl⟩ : syracuseStep 818663 = 1227995) B1227995
theorem B818779 : Blo 818347 818779 := bstep (se 1 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 818779 = 1228169) B1228169
theorem B819015 : Blo 818347 819015 := bstep (se 1 (by rfl) ⟨614261, by rfl⟩ : syracuseStep 819015 = 1228523) B1228523
theorem B819167 : Blo 818347 819167 := bstep (se 1 (by rfl) ⟨614375, by rfl⟩ : syracuseStep 819167 = 1228751) B1228751
theorem B819391 : Blo 818347 819391 := bstep (se 1 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 819391 = 1229087) B1229087
theorem B819407 : Blo 818347 819407 := bstep (se 1 (by rfl) ⟨614555, by rfl⟩ : syracuseStep 819407 = 1229111) B1229111
theorem B819455 : Blo 818347 819455 := bstep (se 1 (by rfl) ⟨614591, by rfl⟩ : syracuseStep 819455 = 1229183) B1229183
theorem B819503 : Blo 818347 819503 := bstep (se 1 (by rfl) ⟨614627, by rfl⟩ : syracuseStep 819503 = 1229255) B1229255
theorem B14188891 : Blo 818347 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B21332375 : Blo 818347 21332375 := bstep (se 1 (by rfl) ⟨15999281, by rfl⟩ : syracuseStep 21332375 = 31998563) B31998563
theorem B4424179 : Blo 818347 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B3801587 : Blo 818347 3801587 := bstep (se 1 (by rfl) ⟨2851190, by rfl⟩ : syracuseStep 3801587 = 5702381) B5702381
theorem B819739 : Blo 818347 819739 := bstep (se 1 (by rfl) ⟨614804, by rfl⟩ : syracuseStep 819739 = 1229609) B1229609
theorem B819743 : Blo 818347 819743 := bstep (se 1 (by rfl) ⟨614807, by rfl⟩ : syracuseStep 819743 = 1229615) B1229615
theorem B819823 : Blo 818347 819823 := bstep (se 1 (by rfl) ⟨614867, by rfl⟩ : syracuseStep 819823 = 1229735) B1229735
theorem B819879 : Blo 818347 819879 := bstep (se 1 (by rfl) ⟨614909, by rfl⟩ : syracuseStep 819879 = 1229819) B1229819
theorem B819919 : Blo 818347 819919 := bstep (se 1 (by rfl) ⟨614939, by rfl⟩ : syracuseStep 819919 = 1229879) B1229879
theorem B32015083 : Blo 818347 32015083 := bstep (se 1 (by rfl) ⟨24011312, by rfl⟩ : syracuseStep 32015083 = 48022625) B48022625
theorem B983839 : Blo 818347 983839 := bstep (se 1 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 983839 = 1475759) B1475759
theorem B819999 : Blo 818347 819999 := bstep (se 1 (by rfl) ⟨614999, by rfl⟩ : syracuseStep 819999 = 1229999) B1229999
theorem B10519577 : Blo 818347 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B820271 : Blo 818347 820271 := bstep (se 1 (by rfl) ⟨615203, by rfl⟩ : syracuseStep 820271 = 1230407) B1230407
theorem B820335 : Blo 818347 820335 := bstep (se 1 (by rfl) ⟨615251, by rfl⟩ : syracuseStep 820335 = 1230503) B1230503
theorem B5244061 : Blo 818347 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B820391 : Blo 818347 820391 := bstep (se 1 (by rfl) ⟨615293, by rfl⟩ : syracuseStep 820391 = 1230587) B1230587
theorem B14419133 : Blo 818347 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B820415 : Blo 818347 820415 := bstep (se 1 (by rfl) ⟨615311, by rfl⟩ : syracuseStep 820415 = 1230623) B1230623
theorem B820447 : Blo 818347 820447 := bstep (se 1 (by rfl) ⟨615335, by rfl⟩ : syracuseStep 820447 = 1230671) B1230671
theorem B820527 : Blo 818347 820527 := bstep (se 1 (by rfl) ⟨615395, by rfl⟩ : syracuseStep 820527 = 1230791) B1230791
theorem B820763 : Blo 818347 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B1967647 : Blo 818347 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B820767 : Blo 818347 820767 := bstep (se 1 (by rfl) ⟨615575, by rfl⟩ : syracuseStep 820767 = 1231151) B1231151
theorem B2000555 : Blo 818347 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B820927 : Blo 818347 820927 := bstep (se 1 (by rfl) ⟨615695, by rfl⟩ : syracuseStep 820927 = 1231391) B1231391
theorem B1967993 : Blo 818347 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B2623375 : Blo 818347 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B3114895 : Blo 818347 3114895 := bstep (se 1 (by rfl) ⟨2336171, by rfl⟩ : syracuseStep 3114895 = 4672343) B4672343
theorem B821183 : Blo 818347 821183 := bstep (se 1 (by rfl) ⟨615887, by rfl⟩ : syracuseStep 821183 = 1231775) B1231775
theorem B821215 : Blo 818347 821215 := bstep (se 1 (by rfl) ⟨615911, by rfl⟩ : syracuseStep 821215 = 1231823) B1231823
theorem B821275 : Blo 818347 821275 := bstep (se 1 (by rfl) ⟨615956, by rfl⟩ : syracuseStep 821275 = 1231913) B1231913
theorem B821279 : Blo 818347 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B821295 : Blo 818347 821295 := bstep (se 1 (by rfl) ⟨615971, by rfl⟩ : syracuseStep 821295 = 1231943) B1231943
theorem B3115169 : Blo 818347 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B821471 : Blo 818347 821471 := bstep (se 1 (by rfl) ⟨616103, by rfl⟩ : syracuseStep 821471 = 1232207) B1232207
theorem B821531 : Blo 818347 821531 := bstep (se 1 (by rfl) ⟨616148, by rfl⟩ : syracuseStep 821531 = 1232297) B1232297
theorem B821631 : Blo 818347 821631 := bstep (se 1 (by rfl) ⟨616223, by rfl⟩ : syracuseStep 821631 = 1232447) B1232447
theorem B821807 : Blo 818347 821807 := bstep (se 1 (by rfl) ⟨616355, by rfl⟩ : syracuseStep 821807 = 1232711) B1232711
theorem B6228575 : Blo 818347 6228575 := bstep (se 1 (by rfl) ⟨4671431, by rfl⟩ : syracuseStep 6228575 = 9342863) B9342863
theorem B821863 : Blo 818347 821863 := bstep (se 1 (by rfl) ⟨616397, by rfl⟩ : syracuseStep 821863 = 1232795) B1232795
theorem B822239 : Blo 818347 822239 := bstep (se 1 (by rfl) ⟨616679, by rfl⟩ : syracuseStep 822239 = 1233359) B1233359
theorem B2624503 : Blo 818347 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B986107 : Blo 818347 986107 := bstep (se 1 (by rfl) ⟨739580, by rfl⟩ : syracuseStep 986107 = 1479161) B1479161
theorem B822267 : Blo 818347 822267 := bstep (se 1 (by rfl) ⟨616700, by rfl⟩ : syracuseStep 822267 = 1233401) B1233401
theorem B822335 : Blo 818347 822335 := bstep (se 1 (by rfl) ⟨616751, by rfl⟩ : syracuseStep 822335 = 1233503) B1233503
theorem B7900537 : Blo 818347 7900537 := bstep (se 2 (by rfl) ⟨2962701, by rfl⟩ : syracuseStep 7900537 = 5925403) B5925403
theorem B921055 : Blo 818347 921055 := bstep (se 1 (by rfl) ⟨690791, by rfl⟩ : syracuseStep 921055 = 1381583) B1381583
theorem B2494331 : Blo 818347 2494331 := bstep (se 1 (by rfl) ⟨1870748, by rfl⟩ : syracuseStep 2494331 = 3741497) B3741497
theorem B921595 : Blo 818347 921595 := bstep (se 1 (by rfl) ⟨691196, by rfl⟩ : syracuseStep 921595 = 1382393) B1382393
theorem B1314911 : Blo 818347 1314911 := bstep (se 1 (by rfl) ⟨986183, by rfl⟩ : syracuseStep 1314911 = 1972367) B1972367
theorem B921703 : Blo 818347 921703 := bstep (se 1 (by rfl) ⟨691277, by rfl⟩ : syracuseStep 921703 = 1382555) B1382555
theorem B921775 : Blo 818347 921775 := bstep (se 1 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 921775 = 1382663) B1382663
theorem B7901495 : Blo 818347 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B3740093 : Blo 818347 3740093 := bstep (se 3 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 3740093 = 1402535) B1402535
theorem B8425957 : Blo 818347 8425957 := bstep (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) B1579867
theorem B2954065 : Blo 818347 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B922459 : Blo 818347 922459 := bstep (se 1 (by rfl) ⟨691844, by rfl⟩ : syracuseStep 922459 = 1383689) B1383689
theorem B1381279 : Blo 818347 1381279 := bstep (se 1 (by rfl) ⟨1035959, by rfl⟩ : syracuseStep 1381279 = 2071919) B2071919
theorem B889759 : Blo 818347 889759 := bstep (se 1 (by rfl) ⟨667319, by rfl⟩ : syracuseStep 889759 = 1334639) B1334639
theorem B6329573 : Blo 818347 6329573 := bstep (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) B1186795
theorem B10000043 : Blo 818347 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B17733563 : Blo 818347 17733563 := bstep (se 1 (by rfl) ⟨13300172, by rfl⟩ : syracuseStep 17733563 = 26600345) B26600345
theorem B923719 : Blo 818347 923719 := bstep (se 1 (by rfl) ⟨692789, by rfl⟩ : syracuseStep 923719 = 1385579) B1385579
theorem B2661131 : Blo 818347 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B1841975 : Blo 818347 1841975 := bstep (se 1 (by rfl) ⟨1381481, by rfl⟩ : syracuseStep 1841975 = 2762963) B2762963
theorem B924583 : Blo 818347 924583 := bstep (se 1 (by rfl) ⟨693437, by rfl⟩ : syracuseStep 924583 = 1386875) B1386875
theorem B1842155 : Blo 818347 1842155 := bstep (se 1 (by rfl) ⟨1381616, by rfl⟩ : syracuseStep 1842155 = 2763233) B2763233
theorem B924763 : Blo 818347 924763 := bstep (se 1 (by rfl) ⟨693572, by rfl⟩ : syracuseStep 924763 = 1387145) B1387145
theorem B7019723 : Blo 818347 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B3120713 : Blo 818347 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B1843055 : Blo 818347 1843055 := bstep (se 1 (by rfl) ⟨1382291, by rfl⟩ : syracuseStep 1843055 = 2764583) B2764583
theorem B1384303 : Blo 818347 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B7479229 : Blo 818347 7479229 := bstep (se 3 (by rfl) ⟨1402355, by rfl⟩ : syracuseStep 7479229 = 2804711) B2804711
theorem B2072567 : Blo 818347 2072567 := bstep (se 1 (by rfl) ⟨1554425, by rfl⟩ : syracuseStep 2072567 = 3108851) B3108851
theorem B1974395 : Blo 818347 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B4989053 : Blo 818347 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1843739 : Blo 818347 1843739 := bstep (se 1 (by rfl) ⟨1382804, by rfl⟩ : syracuseStep 1843739 = 2765609) B2765609
theorem B1843919 : Blo 818347 1843919 := bstep (se 1 (by rfl) ⟨1382939, by rfl⟩ : syracuseStep 1843919 = 2765879) B2765879
theorem B1385167 : Blo 818347 1385167 := bstep (se 1 (by rfl) ⟨1038875, by rfl⟩ : syracuseStep 1385167 = 2077751) B2077751
theorem B8004595 : Blo 818347 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B1844297 : Blo 818347 1844297 := bstep (se 2 (by rfl) ⟨691611, by rfl⟩ : syracuseStep 1844297 = 1383223) B1383223
theorem B2073721 : Blo 818347 2073721 := bstep (se 2 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 2073721 = 1555291) B1555291
theorem B1386011 : Blo 818347 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B2762423 : Blo 818347 2762423 := bstep (se 1 (by rfl) ⟨2071817, by rfl⟩ : syracuseStep 2762423 = 4143635) B4143635
theorem B1845215 : Blo 818347 1845215 := bstep (se 1 (by rfl) ⟨1383911, by rfl⟩ : syracuseStep 1845215 = 2767823) B2767823
theorem B1386463 : Blo 818347 1386463 := bstep (se 1 (by rfl) ⟨1039847, by rfl⟩ : syracuseStep 1386463 = 2079695) B2079695
theorem B2566171 : Blo 818347 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B4204649 : Blo 818347 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B4434041 : Blo 818347 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B2075129 : Blo 818347 2075129 := bstep (se 2 (by rfl) ⟨778173, by rfl⟩ : syracuseStep 2075129 = 1556347) B1556347
theorem B5319431 : Blo 818347 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B1846223 : Blo 818347 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B3746767 : Blo 818347 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B2075615 : Blo 818347 2075615 := bstep (se 1 (by rfl) ⟨1556711, by rfl⟩ : syracuseStep 2075615 = 3113423) B3113423
theorem B1846313 : Blo 818347 1846313 := bstep (se 2 (by rfl) ⟨692367, by rfl⟩ : syracuseStep 1846313 = 1384735) B1384735
theorem B2075777 : Blo 818347 2075777 := bstep (se 2 (by rfl) ⟨778416, by rfl⟩ : syracuseStep 2075777 = 1556833) B1556833
theorem B1748233 : Blo 818347 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B1846547 : Blo 818347 1846547 := bstep (se 1 (by rfl) ⟨1384910, by rfl⟩ : syracuseStep 1846547 = 2769821) B2769821
theorem B1846583 : Blo 818347 1846583 := bstep (se 1 (by rfl) ⟨1384937, by rfl⟩ : syracuseStep 1846583 = 2769875) B2769875
theorem B2764475 : Blo 818347 2764475 := bstep (se 1 (by rfl) ⟨2073356, by rfl⟩ : syracuseStep 2764475 = 4146713) B4146713
theorem B7581545 : Blo 818347 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B1847177 : Blo 818347 1847177 := bstep (se 2 (by rfl) ⟨692691, by rfl⟩ : syracuseStep 1847177 = 1385383) B1385383
theorem B2076587 : Blo 818347 2076587 := bstep (se 1 (by rfl) ⟨1557440, by rfl⟩ : syracuseStep 2076587 = 3114881) B3114881
theorem B1847393 : Blo 818347 1847393 := bstep (se 2 (by rfl) ⟨692772, by rfl⟩ : syracuseStep 1847393 = 1385545) B1385545
theorem B2076799 : Blo 818347 2076799 := bstep (se 1 (by rfl) ⟨1557599, by rfl⟩ : syracuseStep 2076799 = 3115199) B3115199
theorem B1749755 : Blo 818347 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B1848059 : Blo 818347 1848059 := bstep (se 1 (by rfl) ⟨1386044, by rfl⟩ : syracuseStep 1848059 = 2772089) B2772089
theorem B4436855 : Blo 818347 4436855 := bstep (se 1 (by rfl) ⟨3327641, by rfl⟩ : syracuseStep 4436855 = 6655283) B6655283
theorem B1848275 : Blo 818347 1848275 := bstep (se 1 (by rfl) ⟨1386206, by rfl⟩ : syracuseStep 1848275 = 2772413) B2772413
theorem B1848743 : Blo 818347 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B1848851 : Blo 818347 1848851 := bstep (se 1 (by rfl) ⟨1386638, by rfl⟩ : syracuseStep 1848851 = 2773277) B2773277
theorem B6993479 : Blo 818347 6993479 := bstep (se 1 (by rfl) ⟨5245109, by rfl⟩ : syracuseStep 6993479 = 10490219) B10490219
theorem B1848923 : Blo 818347 1848923 := bstep (se 1 (by rfl) ⟨1386692, by rfl⟩ : syracuseStep 1848923 = 2773385) B2773385
theorem B5257001 : Blo 818347 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B1554623 : Blo 818347 1554623 := bstep (se 1 (by rfl) ⟨1165967, by rfl⟩ : syracuseStep 1554623 = 2331935) B2331935
theorem B1849535 : Blo 818347 1849535 := bstep (se 1 (by rfl) ⟨1387151, by rfl⟩ : syracuseStep 1849535 = 2774303) B2774303
theorem B2079391 : Blo 818347 2079391 := bstep (se 1 (by rfl) ⟨1559543, by rfl⟩ : syracuseStep 2079391 = 3119087) B3119087
theorem B5258027 : Blo 818347 5258027 := bstep (se 1 (by rfl) ⟨3943520, by rfl⟩ : syracuseStep 5258027 = 7887041) B7887041
theorem B16825319 : Blo 818347 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B2767931 : Blo 818347 2767931 := bstep (se 1 (by rfl) ⟨2075948, by rfl⟩ : syracuseStep 2767931 = 4151897) B4151897
theorem B1227881 : Blo 818347 1227881 := bstep (se 2 (by rfl) ⟨460455, by rfl⟩ : syracuseStep 1227881 = 920911) B920911
theorem B1555679 : Blo 818347 1555679 := bstep (se 1 (by rfl) ⟨1166759, by rfl⟩ : syracuseStep 1555679 = 2333519) B2333519
theorem B1228007 : Blo 818347 1228007 := bstep (se 1 (by rfl) ⟨921005, by rfl⟩ : syracuseStep 1228007 = 1842011) B1842011
theorem B7879967 : Blo 818347 7879967 := bstep (se 1 (by rfl) ⟨5909975, by rfl⟩ : syracuseStep 7879967 = 11819951) B11819951
theorem B2768201 : Blo 818347 2768201 := bstep (se 2 (by rfl) ⟨1038075, by rfl⟩ : syracuseStep 2768201 = 2076151) B2076151
theorem B6241697 : Blo 818347 6241697 := bstep (se 2 (by rfl) ⟨2340636, by rfl⟩ : syracuseStep 6241697 = 4681273) B4681273
theorem B6995393 : Blo 818347 6995393 := bstep (se 2 (by rfl) ⟨2623272, by rfl⟩ : syracuseStep 6995393 = 5246545) B5246545
theorem B14040539 : Blo 818347 14040539 := bstep (se 1 (by rfl) ⟨10530404, by rfl⟩ : syracuseStep 14040539 = 21060809) B21060809
theorem B2080363 : Blo 818347 2080363 := bstep (se 1 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 2080363 = 3120545) B3120545
theorem B1228511 : Blo 818347 1228511 := bstep (se 1 (by rfl) ⟨921383, by rfl⟩ : syracuseStep 1228511 = 1842767) B1842767
theorem B1228553 : Blo 818347 1228553 := bstep (se 2 (by rfl) ⟨460707, by rfl⟩ : syracuseStep 1228553 = 921415) B921415
theorem B1556263 : Blo 818347 1556263 := bstep (se 1 (by rfl) ⟨1167197, by rfl⟩ : syracuseStep 1556263 = 2334395) B2334395
theorem B9322451 : Blo 818347 9322451 := bstep (se 1 (by rfl) ⟨6991838, by rfl⟩ : syracuseStep 9322451 = 13983677) B13983677
theorem B6144025 : Blo 818347 6144025 := bstep (se 2 (by rfl) ⟨2304009, by rfl⟩ : syracuseStep 6144025 = 4608019) B4608019
theorem B1228991 : Blo 818347 1228991 := bstep (se 1 (by rfl) ⟨921743, by rfl⟩ : syracuseStep 1228991 = 1843487) B1843487
theorem B4669883 : Blo 818347 4669883 := bstep (se 1 (by rfl) ⟨3502412, by rfl⟩ : syracuseStep 4669883 = 7004825) B7004825
theorem B1229417 : Blo 818347 1229417 := bstep (se 2 (by rfl) ⟨461031, by rfl⟩ : syracuseStep 1229417 = 922063) B922063
theorem B1229423 : Blo 818347 1229423 := bstep (se 1 (by rfl) ⟨922067, by rfl⟩ : syracuseStep 1229423 = 1844135) B1844135
theorem B1753787 : Blo 818347 1753787 := bstep (se 1 (by rfl) ⟨1315340, by rfl⟩ : syracuseStep 1753787 = 2630681) B2630681
theorem B2769929 : Blo 818347 2769929 := bstep (se 2 (by rfl) ⟨1038723, by rfl⟩ : syracuseStep 2769929 = 2077447) B2077447
theorem B1230047 : Blo 818347 1230047 := bstep (se 1 (by rfl) ⟨922535, by rfl⟩ : syracuseStep 1230047 = 1845071) B1845071
theorem B1230059 : Blo 818347 1230059 := bstep (se 1 (by rfl) ⟨922544, by rfl⟩ : syracuseStep 1230059 = 1845089) B1845089
theorem B3327419 : Blo 818347 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B1230443 : Blo 818347 1230443 := bstep (se 1 (by rfl) ⟨922832, by rfl⟩ : syracuseStep 1230443 = 1845665) B1845665
theorem B1230527 : Blo 818347 1230527 := bstep (se 1 (by rfl) ⟨922895, by rfl⟩ : syracuseStep 1230527 = 1845791) B1845791
theorem B1558207 : Blo 818347 1558207 := bstep (se 1 (by rfl) ⟨1168655, by rfl⟩ : syracuseStep 1558207 = 2337311) B2337311
theorem B6244127 : Blo 818347 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B1230713 : Blo 818347 1230713 := bstep (se 2 (by rfl) ⟨461517, by rfl⟩ : syracuseStep 1230713 = 923035) B923035
theorem B1558511 : Blo 818347 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B2771279 : Blo 818347 2771279 := bstep (se 1 (by rfl) ⟨2078459, by rfl⟩ : syracuseStep 2771279 = 4156919) B4156919
theorem B1231463 : Blo 818347 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B1755751 : Blo 818347 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B1231655 : Blo 818347 1231655 := bstep (se 1 (by rfl) ⟨923741, by rfl⟩ : syracuseStep 1231655 = 1847483) B1847483
theorem B9325367 : Blo 818347 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B1231979 : Blo 818347 1231979 := bstep (se 1 (by rfl) ⟨923984, by rfl⟩ : syracuseStep 1231979 = 1847969) B1847969
theorem B2772143 : Blo 818347 2772143 := bstep (se 1 (by rfl) ⟨2079107, by rfl⟩ : syracuseStep 2772143 = 4158215) B4158215
theorem B9096425 : Blo 818347 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1232219 : Blo 818347 1232219 := bstep (se 1 (by rfl) ⟨924164, by rfl⟩ : syracuseStep 1232219 = 1848329) B1848329
theorem B1232249 : Blo 818347 1232249 := bstep (se 2 (by rfl) ⟨462093, by rfl⟩ : syracuseStep 1232249 = 924187) B924187
theorem B1166719 : Blo 818347 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B1232255 : Blo 818347 1232255 := bstep (se 1 (by rfl) ⟨924191, by rfl⟩ : syracuseStep 1232255 = 1848383) B1848383
theorem B15781391 : Blo 818347 15781391 := bstep (se 1 (by rfl) ⟨11836043, by rfl⟩ : syracuseStep 15781391 = 23672087) B23672087
theorem B6999767 : Blo 818347 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B2772791 : Blo 818347 2772791 := bstep (se 1 (by rfl) ⟨2079593, by rfl⟩ : syracuseStep 2772791 = 4159187) B4159187
theorem B1232879 : Blo 818347 1232879 := bstep (se 1 (by rfl) ⟨924659, by rfl⟩ : syracuseStep 1232879 = 1849319) B1849319
theorem B1232891 : Blo 818347 1232891 := bstep (se 1 (by rfl) ⟨924668, by rfl⟩ : syracuseStep 1232891 = 1849337) B1849337
theorem B1232951 : Blo 818347 1232951 := bstep (se 1 (by rfl) ⟨924713, by rfl⟩ : syracuseStep 1232951 = 1849427) B1849427
theorem B1232999 : Blo 818347 1232999 := bstep (se 1 (by rfl) ⟨924749, by rfl⟩ : syracuseStep 1232999 = 1849499) B1849499
theorem B1560683 : Blo 818347 1560683 := bstep (se 1 (by rfl) ⟨1170512, by rfl⟩ : syracuseStep 1560683 = 2341025) B2341025
theorem B1233071 : Blo 818347 1233071 := bstep (se 1 (by rfl) ⟨924803, by rfl⟩ : syracuseStep 1233071 = 1849607) B1849607
theorem B2216155 : Blo 818347 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B1233275 : Blo 818347 1233275 := bstep (se 1 (by rfl) ⟨924956, by rfl⟩ : syracuseStep 1233275 = 1849913) B1849913
theorem B4149629 : Blo 818347 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B2773871 : Blo 818347 2773871 := bstep (se 1 (by rfl) ⟨2080403, by rfl⟩ : syracuseStep 2773871 = 4160807) B4160807
theorem B1037215 : Blo 818347 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B15782849 : Blo 818347 15782849 := bstep (se 2 (by rfl) ⟨5918568, by rfl⟩ : syracuseStep 15782849 = 11837137) B11837137
theorem B5625085 : Blo 818347 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B4445437 : Blo 818347 4445437 := bstep (se 3 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 4445437 = 1667039) B1667039
theorem B1169311 : Blo 818347 1169311 := bstep (se 1 (by rfl) ⟨876983, by rfl⟩ : syracuseStep 1169311 = 1753967) B1753967
theorem B3495905 : Blo 818347 3495905 := bstep (se 2 (by rfl) ⟨1310964, by rfl⟩ : syracuseStep 3495905 = 2621929) B2621929
theorem B26564669 : Blo 818347 26564669 := bstep (se 3 (by rfl) ⟨4980875, by rfl⟩ : syracuseStep 26564669 = 9961751) B9961751
theorem B9984761 : Blo 818347 9984761 := bstep (se 2 (by rfl) ⟨3744285, by rfl⟩ : syracuseStep 9984761 = 7488571) B7488571
theorem B16867025 : Blo 818347 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B6315745 : Blo 818347 6315745 := bstep (se 2 (by rfl) ⟨2368404, by rfl⟩ : syracuseStep 6315745 = 4736809) B4736809
theorem B8872577 : Blo 818347 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B16802653 : Blo 818347 16802653 := bstep (se 3 (by rfl) ⟨3150497, by rfl⟩ : syracuseStep 16802653 = 6300995) B6300995
theorem B3499321 : Blo 818347 3499321 := bstep (se 2 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 3499321 = 2624491) B2624491
theorem B4154975 : Blo 818347 4154975 := bstep (se 1 (by rfl) ⟨3116231, by rfl⟩ : syracuseStep 4154975 = 6232463) B6232463
theorem B3499645 : Blo 818347 3499645 := bstep (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) B1312367
theorem B1664905 : Blo 818347 1664905 := bstep (se 2 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 1664905 = 1248679) B1248679
theorem B4155785 : Blo 818347 4155785 := bstep (se 2 (by rfl) ⟨1558419, by rfl⟩ : syracuseStep 4155785 = 3116839) B3116839
theorem B11823641 : Blo 818347 11823641 := bstep (se 2 (by rfl) ⟨4433865, by rfl⟩ : syracuseStep 11823641 = 8867731) B8867731
theorem B25226149 : Blo 818347 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B15756241 : Blo 818347 15756241 := bstep (se 2 (by rfl) ⟨5908590, by rfl⟩ : syracuseStep 15756241 = 11817181) B11817181
theorem B3108577 : Blo 818347 3108577 := bstep (se 2 (by rfl) ⟨1165716, by rfl⟩ : syracuseStep 3108577 = 2331433) B2331433
theorem B45412235 : Blo 818347 45412235 := bstep (se 1 (by rfl) ⟨34059176, by rfl⟩ : syracuseStep 45412235 = 68118353) B68118353
theorem B5926931 : Blo 818347 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B3109049 : Blo 818347 3109049 := bstep (se 2 (by rfl) ⟨1165893, by rfl⟩ : syracuseStep 3109049 = 2331787) B2331787
theorem B9860203 : Blo 818347 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B3110339 : Blo 818347 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B3503711 : Blo 818347 3503711 := bstep (se 1 (by rfl) ⟨2627783, by rfl⟩ : syracuseStep 3503711 = 5255567) B5255567
theorem B10516463 : Blo 818347 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B3504977 : Blo 818347 3504977 := bstep (se 2 (by rfl) ⟨1314366, by rfl⟩ : syracuseStep 3504977 = 2628733) B2628733
theorem B3111767 : Blo 818347 3111767 := bstep (se 1 (by rfl) ⟨2333825, by rfl⟩ : syracuseStep 3111767 = 4667651) B4667651
theorem B818383 : Blo 818347 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B818407 : Blo 818347 818407 := bstep (se 1 (by rfl) ⟨613805, by rfl⟩ : syracuseStep 818407 = 1227611) B1227611
theorem B818503 : Blo 818347 818503 := bstep (se 1 (by rfl) ⟨613877, by rfl⟩ : syracuseStep 818503 = 1227755) B1227755
theorem B818639 : Blo 818347 818639 := bstep (se 1 (by rfl) ⟨613979, by rfl⟩ : syracuseStep 818639 = 1227959) B1227959
theorem B818799 : Blo 818347 818799 := bstep (se 1 (by rfl) ⟨614099, by rfl⟩ : syracuseStep 818799 = 1228199) B1228199
theorem B818855 : Blo 818347 818855 := bstep (se 1 (by rfl) ⟨614141, by rfl⟩ : syracuseStep 818855 = 1228283) B1228283
theorem B818919 : Blo 818347 818919 := bstep (se 1 (by rfl) ⟨614189, by rfl⟩ : syracuseStep 818919 = 1228379) B1228379
theorem B818975 : Blo 818347 818975 := bstep (se 1 (by rfl) ⟨614231, by rfl⟩ : syracuseStep 818975 = 1228463) B1228463
theorem B819055 : Blo 818347 819055 := bstep (se 1 (by rfl) ⟨614291, by rfl⟩ : syracuseStep 819055 = 1228583) B1228583
theorem B819111 : Blo 818347 819111 := bstep (se 1 (by rfl) ⟨614333, by rfl⟩ : syracuseStep 819111 = 1228667) B1228667
theorem B8192033 : Blo 818347 8192033 := bstep (se 2 (by rfl) ⟨3072012, by rfl⟩ : syracuseStep 8192033 = 6144025) B6144025
theorem B819327 : Blo 818347 819327 := bstep (se 1 (by rfl) ⟨614495, by rfl⟩ : syracuseStep 819327 = 1228991) B1228991
theorem B3506429 : Blo 818347 3506429 := bstep (se 3 (by rfl) ⟨657455, by rfl⟩ : syracuseStep 3506429 = 1314911) B1314911
theorem B14221583 : Blo 818347 14221583 := bstep (se 1 (by rfl) ⟨10666187, by rfl⟩ : syracuseStep 14221583 = 21332375) B21332375
theorem B3113255 : Blo 818347 3113255 := bstep (se 1 (by rfl) ⟨2334941, by rfl⟩ : syracuseStep 3113255 = 4669883) B4669883
theorem B819611 : Blo 818347 819611 := bstep (se 1 (by rfl) ⟨614708, by rfl⟩ : syracuseStep 819611 = 1229417) B1229417
theorem B819615 : Blo 818347 819615 := bstep (se 1 (by rfl) ⟨614711, by rfl⟩ : syracuseStep 819615 = 1229423) B1229423
theorem B5898905 : Blo 818347 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B7013051 : Blo 818347 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B820031 : Blo 818347 820031 := bstep (se 1 (by rfl) ⟨615023, by rfl⟩ : syracuseStep 820031 = 1230047) B1230047
theorem B820039 : Blo 818347 820039 := bstep (se 1 (by rfl) ⟨615029, by rfl⟩ : syracuseStep 820039 = 1230059) B1230059
theorem B1311785 : Blo 818347 1311785 := bstep (se 2 (by rfl) ⟨491919, by rfl⟩ : syracuseStep 1311785 = 983839) B983839
theorem B820295 : Blo 818347 820295 := bstep (se 1 (by rfl) ⟨615221, by rfl⟩ : syracuseStep 820295 = 1230443) B1230443
theorem B820351 : Blo 818347 820351 := bstep (se 1 (by rfl) ⟨615263, by rfl⟩ : syracuseStep 820351 = 1230527) B1230527
theorem B4162751 : Blo 818347 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B1311995 : Blo 818347 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B820475 : Blo 818347 820475 := bstep (se 1 (by rfl) ⟨615356, by rfl⟩ : syracuseStep 820475 = 1230713) B1230713
theorem B820975 : Blo 818347 820975 := bstep (se 1 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 820975 = 1231463) B1231463
theorem B821103 : Blo 818347 821103 := bstep (se 1 (by rfl) ⟨615827, by rfl⟩ : syracuseStep 821103 = 1231655) B1231655
theorem B2623529 : Blo 818347 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B821319 : Blo 818347 821319 := bstep (se 1 (by rfl) ⟨615989, by rfl⟩ : syracuseStep 821319 = 1231979) B1231979
theorem B6064283 : Blo 818347 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B821479 : Blo 818347 821479 := bstep (se 1 (by rfl) ⟨616109, by rfl⟩ : syracuseStep 821479 = 1232219) B1232219
theorem B821499 : Blo 818347 821499 := bstep (se 1 (by rfl) ⟨616124, by rfl⟩ : syracuseStep 821499 = 1232249) B1232249
theorem B821503 : Blo 818347 821503 := bstep (se 1 (by rfl) ⟨616127, by rfl⟩ : syracuseStep 821503 = 1232255) B1232255
theorem B10520927 : Blo 818347 10520927 := bstep (se 1 (by rfl) ⟨7890695, by rfl⟩ : syracuseStep 10520927 = 15781391) B15781391
theorem B821919 : Blo 818347 821919 := bstep (se 1 (by rfl) ⟨616439, by rfl⟩ : syracuseStep 821919 = 1232879) B1232879
theorem B821927 : Blo 818347 821927 := bstep (se 1 (by rfl) ⟨616445, by rfl⟩ : syracuseStep 821927 = 1232891) B1232891
theorem B821967 : Blo 818347 821967 := bstep (se 1 (by rfl) ⟨616475, by rfl⟩ : syracuseStep 821967 = 1232951) B1232951
theorem B821999 : Blo 818347 821999 := bstep (se 1 (by rfl) ⟨616499, by rfl⟩ : syracuseStep 821999 = 1232999) B1232999
theorem B822047 : Blo 818347 822047 := bstep (se 1 (by rfl) ⟨616535, by rfl⟩ : syracuseStep 822047 = 1233071) B1233071
theorem B822183 : Blo 818347 822183 := bstep (se 1 (by rfl) ⟨616637, by rfl⟩ : syracuseStep 822183 = 1233275) B1233275
theorem B2493395 : Blo 818347 2493395 := bstep (se 1 (by rfl) ⟨1870046, by rfl⟩ : syracuseStep 2493395 = 3740093) B3740093
theorem B10521899 : Blo 818347 10521899 := bstep (se 1 (by rfl) ⟨7891424, by rfl⟩ : syracuseStep 10521899 = 15782849) B15782849
theorem B21008321 : Blo 818347 21008321 := bstep (se 2 (by rfl) ⟨7878120, by rfl⟩ : syracuseStep 21008321 = 15756241) B15756241
theorem B2330603 : Blo 818347 2330603 := bstep (se 1 (by rfl) ⟨1747952, by rfl⟩ : syracuseStep 2330603 = 3495905) B3495905
theorem B1314809 : Blo 818347 1314809 := bstep (se 2 (by rfl) ⟨493053, by rfl⟩ : syracuseStep 1314809 = 986107) B986107
theorem B6656507 : Blo 818347 6656507 := bstep (se 1 (by rfl) ⟨4992380, by rfl⟩ : syracuseStep 6656507 = 9984761) B9984761
theorem B11244683 : Blo 818347 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B1381711 : Blo 818347 1381711 := bstep (se 1 (by rfl) ⟨1036283, by rfl⟩ : syracuseStep 1381711 = 2072567) B2072567
theorem B1316263 : Blo 818347 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B2954873 : Blo 818347 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B924007 : Blo 818347 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B3938753 : Blo 818347 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B1841615 : Blo 818347 1841615 := bstep (se 1 (by rfl) ⟨1381211, by rfl⟩ : syracuseStep 1841615 = 2762423) B2762423
theorem B1841705 : Blo 818347 1841705 := bstep (se 2 (by rfl) ⟨690639, by rfl⟩ : syracuseStep 1841705 = 1381279) B1381279
theorem B1382953 : Blo 818347 1382953 := bstep (se 2 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 1382953 = 1037215) B1037215
theorem B1186345 : Blo 818347 1186345 := bstep (se 2 (by rfl) ⟨444879, by rfl⟩ : syracuseStep 1186345 = 889759) B889759
theorem B2956027 : Blo 818347 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B13146937 : Blo 818347 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B1383419 : Blo 818347 1383419 := bstep (se 1 (by rfl) ⟨1037564, by rfl⟩ : syracuseStep 1383419 = 2075129) B2075129
theorem B3546287 : Blo 818347 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B1383743 : Blo 818347 1383743 := bstep (se 1 (by rfl) ⟨1037807, by rfl⟩ : syracuseStep 1383743 = 2075615) B2075615
theorem B1383851 : Blo 818347 1383851 := bstep (se 1 (by rfl) ⟨1037888, by rfl⟩ : syracuseStep 1383851 = 2075777) B2075777
theorem B1842983 : Blo 818347 1842983 := bstep (se 1 (by rfl) ⟨1382237, by rfl⟩ : syracuseStep 1842983 = 2764475) B2764475
theorem B5054363 : Blo 818347 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B1384391 : Blo 818347 1384391 := bstep (se 1 (by rfl) ⟨1038293, by rfl⟩ : syracuseStep 1384391 = 2076587) B2076587
theorem B2072699 : Blo 818347 2072699 := bstep (se 1 (by rfl) ⟨1554524, by rfl⟩ : syracuseStep 2072699 = 3109049) B3109049
theorem B2957903 : Blo 818347 2957903 := bstep (se 1 (by rfl) ⟨2218427, by rfl⟩ : syracuseStep 2957903 = 4436855) B4436855
theorem B2073559 : Blo 818347 2073559 := bstep (se 1 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 2073559 = 3110339) B3110339
theorem B4662319 : Blo 818347 4662319 := bstep (se 1 (by rfl) ⟨3496739, by rfl⟩ : syracuseStep 4662319 = 6993479) B6993479
theorem B2335807 : Blo 818347 2335807 := bstep (se 1 (by rfl) ⟨1751855, by rfl⟩ : syracuseStep 2335807 = 3503711) B3503711
theorem B2336651 : Blo 818347 2336651 := bstep (se 1 (by rfl) ⟨1752488, by rfl⟩ : syracuseStep 2336651 = 3504977) B3504977
theorem B2074511 : Blo 818347 2074511 := bstep (se 1 (by rfl) ⟨1555883, by rfl⟩ : syracuseStep 2074511 = 3111767) B3111767
theorem B11216879 : Blo 818347 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B1845287 : Blo 818347 1845287 := bstep (se 1 (by rfl) ⟨1383965, by rfl⟩ : syracuseStep 1845287 = 2767931) B2767931
theorem B5253311 : Blo 818347 5253311 := bstep (se 1 (by rfl) ⟨3939983, by rfl⟩ : syracuseStep 5253311 = 7879967) B7879967
theorem B1845467 : Blo 818347 1845467 := bstep (se 1 (by rfl) ⟨1384100, by rfl⟩ : syracuseStep 1845467 = 2768201) B2768201
theorem B4663595 : Blo 818347 4663595 := bstep (se 1 (by rfl) ⟨3497696, by rfl⟩ : syracuseStep 4663595 = 6995393) B6995393
theorem B2075017 : Blo 818347 2075017 := bstep (se 2 (by rfl) ⟨778131, by rfl⟩ : syracuseStep 2075017 = 1556263) B1556263
theorem B1845737 : Blo 818347 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B9972305 : Blo 818347 9972305 := bstep (se 2 (by rfl) ⟨3739614, by rfl⟩ : syracuseStep 9972305 = 7479229) B7479229
theorem B18918521 : Blo 818347 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B1846619 : Blo 818347 1846619 := bstep (se 1 (by rfl) ⟨1384964, by rfl⟩ : syracuseStep 1846619 = 2769929) B2769929
theorem B9612755 : Blo 818347 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B1846889 : Blo 818347 1846889 := bstep (se 2 (by rfl) ⟨692583, by rfl⟩ : syracuseStep 1846889 = 1385167) B1385167
theorem B10137565 : Blo 818347 10137565 := bstep (se 3 (by rfl) ⟨1900793, by rfl⟩ : syracuseStep 10137565 = 3801587) B3801587
theorem B2076779 : Blo 818347 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B2764961 : Blo 818347 2764961 := bstep (se 2 (by rfl) ⟨1036860, by rfl⟩ : syracuseStep 2764961 = 2073721) B2073721
theorem B6992081 : Blo 818347 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B1847519 : Blo 818347 1847519 := bstep (se 1 (by rfl) ⟨1385639, by rfl⟩ : syracuseStep 1847519 = 2771279) B2771279
theorem B4665761 : Blo 818347 4665761 := bstep (se 2 (by rfl) ⟨1749660, by rfl⟩ : syracuseStep 4665761 = 3499321) B3499321
theorem B1848095 : Blo 818347 1848095 := bstep (se 1 (by rfl) ⟨1386071, by rfl⟩ : syracuseStep 1848095 = 2772143) B2772143
theorem B4666193 : Blo 818347 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B2077609 : Blo 818347 2077609 := bstep (se 2 (by rfl) ⟨779103, by rfl⟩ : syracuseStep 2077609 = 1558207) B1558207
theorem B4666511 : Blo 818347 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B1848527 : Blo 818347 1848527 := bstep (se 1 (by rfl) ⟨1386395, by rfl⟩ : syracuseStep 1848527 = 2772791) B2772791
theorem B1848617 : Blo 818347 1848617 := bstep (se 2 (by rfl) ⟨693231, by rfl⟩ : syracuseStep 1848617 = 1386463) B1386463
theorem B2766419 : Blo 818347 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B1849247 : Blo 818347 1849247 := bstep (se 1 (by rfl) ⟨1386935, by rfl⟩ : syracuseStep 1849247 = 2773871) B2773871
theorem B2341001 : Blo 818347 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B6666695 : Blo 818347 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B33634865 : Blo 818347 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B4995689 : Blo 818347 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B17709779 : Blo 818347 17709779 := bstep (se 1 (by rfl) ⟨13282334, by rfl⟩ : syracuseStep 17709779 = 26564669) B26564669
theorem B10534049 : Blo 818347 10534049 := bstep (se 2 (by rfl) ⟨3950268, by rfl⟩ : syracuseStep 10534049 = 7900537) B7900537
theorem B1555625 : Blo 818347 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B1227983 : Blo 818347 1227983 := bstep (se 1 (by rfl) ⟨920987, by rfl⟩ : syracuseStep 1227983 = 1841975) B1841975
theorem B1228073 : Blo 818347 1228073 := bstep (se 2 (by rfl) ⟨460527, by rfl⟩ : syracuseStep 1228073 = 921055) B921055
theorem B1228103 : Blo 818347 1228103 := bstep (se 1 (by rfl) ⟨921077, by rfl⟩ : syracuseStep 1228103 = 1842155) B1842155
theorem B4144769 : Blo 818347 4144769 := bstep (se 2 (by rfl) ⟨1554288, by rfl⟩ : syracuseStep 4144769 = 3108577) B3108577
theorem B2080475 : Blo 818347 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B1228703 : Blo 818347 1228703 := bstep (se 1 (by rfl) ⟨921527, by rfl⟩ : syracuseStep 1228703 = 1843055) B1843055
theorem B1228793 : Blo 818347 1228793 := bstep (se 2 (by rfl) ⟨460797, by rfl⟩ : syracuseStep 1228793 = 921595) B921595
theorem B3326035 : Blo 818347 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B1228937 : Blo 818347 1228937 := bstep (se 2 (by rfl) ⟨460851, by rfl⟩ : syracuseStep 1228937 = 921703) B921703
theorem B2769065 : Blo 818347 2769065 := bstep (se 2 (by rfl) ⟨1038399, by rfl⟩ : syracuseStep 2769065 = 2076799) B2076799
theorem B1229033 : Blo 818347 1229033 := bstep (se 2 (by rfl) ⟨460887, by rfl⟩ : syracuseStep 1229033 = 921775) B921775
theorem B1229159 : Blo 818347 1229159 := bstep (se 1 (by rfl) ⟨921869, by rfl⟩ : syracuseStep 1229159 = 1843739) B1843739
theorem B5915051 : Blo 818347 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B1229279 : Blo 818347 1229279 := bstep (se 1 (by rfl) ⟨921959, by rfl⟩ : syracuseStep 1229279 = 1843919) B1843919
theorem B1229531 : Blo 818347 1229531 := bstep (se 1 (by rfl) ⟨922148, by rfl⟩ : syracuseStep 1229531 = 1844297) B1844297
theorem B2769983 : Blo 818347 2769983 := bstep (se 1 (by rfl) ⟨2077487, by rfl⟩ : syracuseStep 2769983 = 4154975) B4154975
theorem B1229945 : Blo 818347 1229945 := bstep (se 2 (by rfl) ⟨461229, by rfl⟩ : syracuseStep 1229945 = 922459) B922459
theorem B1230143 : Blo 818347 1230143 := bstep (se 1 (by rfl) ⟨922607, by rfl⟩ : syracuseStep 1230143 = 1845215) B1845215
theorem B9323909 : Blo 818347 9323909 := bstep (se 4 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 9323909 = 1748233) B1748233
theorem B2803099 : Blo 818347 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B2770523 : Blo 818347 2770523 := bstep (se 1 (by rfl) ⟨2077892, by rfl⟩ : syracuseStep 2770523 = 4155785) B4155785
theorem B7882427 : Blo 818347 7882427 := bstep (se 1 (by rfl) ⟨5911820, by rfl⟩ : syracuseStep 7882427 = 11823641) B11823641
theorem B1230815 : Blo 818347 1230815 := bstep (se 1 (by rfl) ⟨923111, by rfl⟩ : syracuseStep 1230815 = 1846223) B1846223
theorem B1230875 : Blo 818347 1230875 := bstep (se 1 (by rfl) ⟨923156, by rfl⟩ : syracuseStep 1230875 = 1846313) B1846313
theorem B7096349 : Blo 818347 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B1231031 : Blo 818347 1231031 := bstep (se 1 (by rfl) ⟨923273, by rfl⟩ : syracuseStep 1231031 = 1846547) B1846547
theorem B1231055 : Blo 818347 1231055 := bstep (se 1 (by rfl) ⟨923291, by rfl⟩ : syracuseStep 1231055 = 1846583) B1846583
theorem B1559081 : Blo 818347 1559081 := bstep (se 2 (by rfl) ⟨584655, by rfl⟩ : syracuseStep 1559081 = 1169311) B1169311
theorem B1231451 : Blo 818347 1231451 := bstep (se 1 (by rfl) ⟨923588, by rfl⟩ : syracuseStep 1231451 = 1847177) B1847177
theorem B3951287 : Blo 818347 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B1231595 : Blo 818347 1231595 := bstep (se 1 (by rfl) ⟨923696, by rfl⟩ : syracuseStep 1231595 = 1847393) B1847393
theorem B1231625 : Blo 818347 1231625 := bstep (se 2 (by rfl) ⟨461859, by rfl⟩ : syracuseStep 1231625 = 923719) B923719
theorem B1166503 : Blo 818347 1166503 := bstep (se 1 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 1166503 = 1749755) B1749755
theorem B1232039 : Blo 818347 1232039 := bstep (se 1 (by rfl) ⟨924029, by rfl⟩ : syracuseStep 1232039 = 1848059) B1848059
theorem B1232183 : Blo 818347 1232183 := bstep (se 1 (by rfl) ⟨924137, by rfl⟩ : syracuseStep 1232183 = 1848275) B1848275
theorem B2772521 : Blo 818347 2772521 := bstep (se 2 (by rfl) ⟨1039695, by rfl⟩ : syracuseStep 2772521 = 2079391) B2079391
theorem B1232495 : Blo 818347 1232495 := bstep (se 1 (by rfl) ⟨924371, by rfl⟩ : syracuseStep 1232495 = 1848743) B1848743
theorem B1232567 : Blo 818347 1232567 := bstep (se 1 (by rfl) ⟨924425, by rfl⟩ : syracuseStep 1232567 = 1848851) B1848851
theorem B1232615 : Blo 818347 1232615 := bstep (se 1 (by rfl) ⟨924461, by rfl⟩ : syracuseStep 1232615 = 1848923) B1848923
theorem B1232777 : Blo 818347 1232777 := bstep (se 2 (by rfl) ⟨462291, by rfl⟩ : syracuseStep 1232777 = 924583) B924583
theorem B1233017 : Blo 818347 1233017 := bstep (se 2 (by rfl) ⟨462381, by rfl⟩ : syracuseStep 1233017 = 924763) B924763
theorem B1036415 : Blo 818347 1036415 := bstep (se 1 (by rfl) ⟨777311, by rfl⟩ : syracuseStep 1036415 = 1554623) B1554623
theorem B1233023 : Blo 818347 1233023 := bstep (se 1 (by rfl) ⟨924767, by rfl⟩ : syracuseStep 1233023 = 1849535) B1849535
theorem B2773817 : Blo 818347 2773817 := bstep (se 2 (by rfl) ⟨1040181, by rfl⟩ : syracuseStep 2773817 = 2080363) B2080363
theorem B1037119 : Blo 818347 1037119 := bstep (se 1 (by rfl) ⟨777839, by rfl⟩ : syracuseStep 1037119 = 1555679) B1555679
theorem B9360359 : Blo 818347 9360359 := bstep (se 1 (by rfl) ⟨7020269, by rfl⟩ : syracuseStep 9360359 = 14040539) B14040539
theorem B6214967 : Blo 818347 6214967 := bstep (se 1 (by rfl) ⟨4661225, by rfl⟩ : syracuseStep 6214967 = 9322451) B9322451
theorem B13686245 : Blo 818347 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B1169191 : Blo 818347 1169191 := bstep (se 1 (by rfl) ⟨876893, by rfl⟩ : syracuseStep 1169191 = 1753787) B1753787
theorem B2218279 : Blo 818347 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B42686777 : Blo 818347 42686777 := bstep (se 2 (by rfl) ⟨16007541, by rfl⟩ : syracuseStep 42686777 = 32015083) B32015083
theorem B1333703 : Blo 818347 1333703 := bstep (se 1 (by rfl) ⟨1000277, by rfl⟩ : syracuseStep 1333703 = 2000555) B2000555
theorem B22403537 : Blo 818347 22403537 := bstep (se 2 (by rfl) ⟨8401326, by rfl⟩ : syracuseStep 22403537 = 16802653) B16802653
theorem B10672793 : Blo 818347 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B1039007 : Blo 818347 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B4152383 : Blo 818347 4152383 := bstep (se 1 (by rfl) ⟨3114287, by rfl⟩ : syracuseStep 4152383 = 6228575) B6228575
theorem B6216911 : Blo 818347 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B3497833 : Blo 818347 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B4153193 : Blo 818347 4153193 := bstep (se 2 (by rfl) ⟨1557447, by rfl⟩ : syracuseStep 4153193 = 3114895) B3114895
theorem B1662887 : Blo 818347 1662887 := bstep (se 1 (by rfl) ⟨1247165, by rfl⟩ : syracuseStep 1662887 = 2494331) B2494331
theorem B1040455 : Blo 818347 1040455 := bstep (se 1 (by rfl) ⟨780341, by rfl⟩ : syracuseStep 1040455 = 1560683) B1560683
theorem B5267663 : Blo 818347 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B4219715 : Blo 818347 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B11822375 : Blo 818347 11822375 := bstep (se 1 (by rfl) ⟨8866781, by rfl⟩ : syracuseStep 11822375 = 17733563) B17733563
theorem B3499337 : Blo 818347 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B14018669 : Blo 818347 14018669 := bstep (se 3 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 14018669 = 5257001) B5257001
theorem B4679815 : Blo 818347 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B11234609 : Blo 818347 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B7500113 : Blo 818347 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B5927249 : Blo 818347 5927249 := bstep (se 2 (by rfl) ⟨2222718, by rfl⟩ : syracuseStep 5927249 = 4445437) B4445437
theorem B30274823 : Blo 818347 30274823 := bstep (se 1 (by rfl) ⟨22706117, by rfl⟩ : syracuseStep 30274823 = 45412235) B45412235
theorem B35517973 : Blo 818347 35517973 := bstep (se 6 (by rfl) ⟨832452, by rfl⟩ : syracuseStep 35517973 = 1664905) B1664905
theorem B7010975 : Blo 818347 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B3505351 : Blo 818347 3505351 := bstep (se 1 (by rfl) ⟨2629013, by rfl⟩ : syracuseStep 3505351 = 5258027) B5258027
theorem B818587 : Blo 818347 818587 := bstep (se 1 (by rfl) ⟨613940, by rfl⟩ : syracuseStep 818587 = 1227881) B1227881
theorem B818671 : Blo 818347 818671 := bstep (se 1 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 818671 = 1228007) B1228007
theorem B4161131 : Blo 818347 4161131 := bstep (se 1 (by rfl) ⟨3120848, by rfl⟩ : syracuseStep 4161131 = 6241697) B6241697
theorem B8420993 : Blo 818347 8420993 := bstep (se 2 (by rfl) ⟨3157872, by rfl⟩ : syracuseStep 8420993 = 6315745) B6315745
theorem B819007 : Blo 818347 819007 := bstep (se 1 (by rfl) ⟨614255, by rfl⟩ : syracuseStep 819007 = 1228511) B1228511
theorem B819035 : Blo 818347 819035 := bstep (se 1 (by rfl) ⟨614276, by rfl⟩ : syracuseStep 819035 = 1228553) B1228553
theorem B819291 : Blo 818347 819291 := bstep (se 1 (by rfl) ⟨614468, by rfl⟩ : syracuseStep 819291 = 1228937) B1228937
theorem B819355 : Blo 818347 819355 := bstep (se 1 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 819355 = 1229033) B1229033
theorem B819439 : Blo 818347 819439 := bstep (se 1 (by rfl) ⟨614579, by rfl⟩ : syracuseStep 819439 = 1229159) B1229159
theorem B819519 : Blo 818347 819519 := bstep (se 1 (by rfl) ⟨614639, by rfl⟩ : syracuseStep 819519 = 1229279) B1229279
theorem B3932603 : Blo 818347 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B819687 : Blo 818347 819687 := bstep (se 1 (by rfl) ⟨614765, by rfl⟩ : syracuseStep 819687 = 1229531) B1229531
theorem B819963 : Blo 818347 819963 := bstep (se 1 (by rfl) ⟨614972, by rfl⟩ : syracuseStep 819963 = 1229945) B1229945
theorem B820095 : Blo 818347 820095 := bstep (se 1 (by rfl) ⟨615071, by rfl⟩ : syracuseStep 820095 = 1230143) B1230143
theorem B820543 : Blo 818347 820543 := bstep (se 1 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 820543 = 1230815) B1230815
theorem B820583 : Blo 818347 820583 := bstep (se 1 (by rfl) ⟨615437, by rfl⟩ : syracuseStep 820583 = 1230875) B1230875
theorem B3114409 : Blo 818347 3114409 := bstep (se 2 (by rfl) ⟨1167903, by rfl⟩ : syracuseStep 3114409 = 2335807) B2335807
theorem B820687 : Blo 818347 820687 := bstep (se 1 (by rfl) ⟨615515, by rfl⟩ : syracuseStep 820687 = 1231031) B1231031
theorem B820703 : Blo 818347 820703 := bstep (se 1 (by rfl) ⟨615527, by rfl⟩ : syracuseStep 820703 = 1231055) B1231055
theorem B7013951 : Blo 818347 7013951 := bstep (se 1 (by rfl) ⟨5260463, by rfl⟩ : syracuseStep 7013951 = 10520927) B10520927
theorem B820967 : Blo 818347 820967 := bstep (se 1 (by rfl) ⟨615725, by rfl⟩ : syracuseStep 820967 = 1231451) B1231451
theorem B821063 : Blo 818347 821063 := bstep (se 1 (by rfl) ⟨615797, by rfl⟩ : syracuseStep 821063 = 1231595) B1231595
theorem B821083 : Blo 818347 821083 := bstep (se 1 (by rfl) ⟨615812, by rfl⟩ : syracuseStep 821083 = 1231625) B1231625
theorem B3737465 : Blo 818347 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B821359 : Blo 818347 821359 := bstep (se 1 (by rfl) ⟨616019, by rfl⟩ : syracuseStep 821359 = 1232039) B1232039
theorem B7014599 : Blo 818347 7014599 := bstep (se 1 (by rfl) ⟨5260949, by rfl⟩ : syracuseStep 7014599 = 10521899) B10521899
theorem B821455 : Blo 818347 821455 := bstep (se 1 (by rfl) ⟨616091, by rfl⟩ : syracuseStep 821455 = 1232183) B1232183
theorem B821663 : Blo 818347 821663 := bstep (se 1 (by rfl) ⟨616247, by rfl⟩ : syracuseStep 821663 = 1232495) B1232495
theorem B821711 : Blo 818347 821711 := bstep (se 1 (by rfl) ⟨616283, by rfl⟩ : syracuseStep 821711 = 1232567) B1232567
theorem B821743 : Blo 818347 821743 := bstep (se 1 (by rfl) ⟨616307, by rfl⟩ : syracuseStep 821743 = 1232615) B1232615
theorem B821851 : Blo 818347 821851 := bstep (se 1 (by rfl) ⟨616388, by rfl⟩ : syracuseStep 821851 = 1232777) B1232777
theorem B822011 : Blo 818347 822011 := bstep (se 1 (by rfl) ⟨616508, by rfl⟩ : syracuseStep 822011 = 1233017) B1233017
theorem B822015 : Blo 818347 822015 := bstep (se 1 (by rfl) ⟨616511, by rfl⟩ : syracuseStep 822015 = 1233023) B1233023
theorem B6327173 : Blo 818347 6327173 := bstep (se 4 (by rfl) ⟨593172, by rfl⟩ : syracuseStep 6327173 = 1186345) B1186345
theorem B29985821 : Blo 818347 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B1969915 : Blo 818347 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B7115195 : Blo 818347 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B922279 : Blo 818347 922279 := bstep (se 1 (by rfl) ⟨691709, by rfl⟩ : syracuseStep 922279 = 1383419) B1383419
theorem B2364191 : Blo 818347 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B922495 : Blo 818347 922495 := bstep (se 1 (by rfl) ⟨691871, by rfl⟩ : syracuseStep 922495 = 1383743) B1383743
theorem B922567 : Blo 818347 922567 := bstep (se 1 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 922567 = 1383851) B1383851
theorem B922927 : Blo 818347 922927 := bstep (se 1 (by rfl) ⟨692195, by rfl⟩ : syracuseStep 922927 = 1384391) B1384391
theorem B1381799 : Blo 818347 1381799 := bstep (se 1 (by rfl) ⟨1036349, by rfl⟩ : syracuseStep 1381799 = 2072699) B2072699
theorem B3511775 : Blo 818347 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B1971935 : Blo 818347 1971935 := bstep (se 1 (by rfl) ⟨1478951, by rfl⟩ : syracuseStep 1971935 = 2957903) B2957903
theorem B2332891 : Blo 818347 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B1382825 : Blo 818347 1382825 := bstep (se 2 (by rfl) ⟨518559, by rfl⟩ : syracuseStep 1382825 = 1037119) B1037119
theorem B1383007 : Blo 818347 1383007 := bstep (se 1 (by rfl) ⟨1037255, by rfl⟩ : syracuseStep 1383007 = 2074511) B2074511
theorem B7477919 : Blo 818347 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B9345779 : Blo 818347 9345779 := bstep (se 1 (by rfl) ⟨7009334, by rfl⟩ : syracuseStep 9345779 = 14018669) B14018669
theorem B1842281 : Blo 818347 1842281 := bstep (se 2 (by rfl) ⟨690855, by rfl⟩ : syracuseStep 1842281 = 1381711) B1381711
theorem B47357297 : Blo 818347 47357297 := bstep (se 2 (by rfl) ⟨17758986, by rfl⟩ : syracuseStep 47357297 = 35517973) B35517973
theorem B1384519 : Blo 818347 1384519 := bstep (se 1 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 1384519 = 2076779) B2076779
theorem B1843307 : Blo 818347 1843307 := bstep (se 1 (by rfl) ⟨1382480, by rfl⟩ : syracuseStep 1843307 = 2764961) B2764961
theorem B4661387 : Blo 818347 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B2957705 : Blo 818347 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B1843937 : Blo 818347 1843937 := bstep (se 2 (by rfl) ⟨691476, by rfl⟩ : syracuseStep 1843937 = 1382953) B1382953
theorem B3941369 : Blo 818347 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B1844279 : Blo 818347 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B22423243 : Blo 818347 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B11806519 : Blo 818347 11806519 := bstep (se 1 (by rfl) ⟨8854889, by rfl⟩ : syracuseStep 11806519 = 17709779) B17709779
theorem B7022699 : Blo 818347 7022699 := bstep (se 1 (by rfl) ⟨5267024, by rfl⟩ : syracuseStep 7022699 = 10534049) B10534049
theorem B2763179 : Blo 818347 2763179 := bstep (se 1 (by rfl) ⟨2072384, by rfl⟩ : syracuseStep 2763179 = 4144769) B4144769
theorem B5613995 : Blo 818347 5613995 := bstep (se 1 (by rfl) ⟨4210496, by rfl⟩ : syracuseStep 5613995 = 8420993) B8420993
theorem B4434365 : Blo 818347 4434365 := bstep (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) B1662887
theorem B4663777 : Blo 818347 4663777 := bstep (se 2 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 4663777 = 3497833) B3497833
theorem B1386983 : Blo 818347 1386983 := bstep (se 1 (by rfl) ⟨1040237, by rfl⟩ : syracuseStep 1386983 = 2080475) B2080475
theorem B1387273 : Blo 818347 1387273 := bstep (se 2 (by rfl) ⟨520227, by rfl⟩ : syracuseStep 1387273 = 1040455) B1040455
theorem B4434713 : Blo 818347 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B1846043 : Blo 818347 1846043 := bstep (se 1 (by rfl) ⟨1384532, by rfl⟩ : syracuseStep 1846043 = 2769065) B2769065
theorem B2337619 : Blo 818347 2337619 := bstep (se 1 (by rfl) ⟨1753214, by rfl⟩ : syracuseStep 2337619 = 3506429) B3506429
theorem B9481055 : Blo 818347 9481055 := bstep (se 1 (by rfl) ⟨7110791, by rfl⟩ : syracuseStep 9481055 = 14221583) B14221583
theorem B2075503 : Blo 818347 2075503 := bstep (se 1 (by rfl) ⟨1556627, by rfl⟩ : syracuseStep 2075503 = 3113255) B3113255
theorem B3943367 : Blo 818347 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B2763773 : Blo 818347 2763773 := bstep (se 3 (by rfl) ⟨518207, by rfl⟩ : syracuseStep 2763773 = 1036415) B1036415
theorem B1846655 : Blo 818347 1846655 := bstep (se 1 (by rfl) ⟨1384991, by rfl⟩ : syracuseStep 1846655 = 2769983) B2769983
theorem B1847015 : Blo 818347 1847015 := bstep (se 1 (by rfl) ⟨1385261, by rfl⟩ : syracuseStep 1847015 = 2770523) B2770523
theorem B5254951 : Blo 818347 5254951 := bstep (se 1 (by rfl) ⟨3941213, by rfl⟩ : syracuseStep 5254951 = 7882427) B7882427
theorem B2764745 : Blo 818347 2764745 := bstep (se 2 (by rfl) ⟨1036779, by rfl⟩ : syracuseStep 2764745 = 2073559) B2073559
theorem B4730899 : Blo 818347 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B4042855 : Blo 818347 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B2634191 : Blo 818347 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B1848347 : Blo 818347 1848347 := bstep (se 1 (by rfl) ⟨1386260, by rfl⟩ : syracuseStep 1848347 = 2772521) B2772521
theorem B14005547 : Blo 818347 14005547 := bstep (se 1 (by rfl) ⟨10504160, by rfl⟩ : syracuseStep 14005547 = 21008321) B21008321
theorem B1553735 : Blo 818347 1553735 := bstep (se 1 (by rfl) ⟨1165301, by rfl⟩ : syracuseStep 1553735 = 2330603) B2330603
theorem B6239753 : Blo 818347 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B4437671 : Blo 818347 4437671 := bstep (se 1 (by rfl) ⟨3328253, by rfl⟩ : syracuseStep 4437671 = 6656507) B6656507
theorem B2766689 : Blo 818347 2766689 := bstep (se 2 (by rfl) ⟨1037508, by rfl⟩ : syracuseStep 2766689 = 2075017) B2075017
theorem B1849211 : Blo 818347 1849211 := bstep (se 1 (by rfl) ⟨1386908, by rfl⟩ : syracuseStep 1849211 = 2773817) B2773817
theorem B6240239 : Blo 818347 6240239 := bstep (se 1 (by rfl) ⟨4680179, by rfl⟩ : syracuseStep 6240239 = 9360359) B9360359
theorem B4143311 : Blo 818347 4143311 := bstep (se 1 (by rfl) ⟨3107483, by rfl⟩ : syracuseStep 4143311 = 6214967) B6214967
theorem B9124163 : Blo 818347 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B1555337 : Blo 818347 1555337 := bstep (se 2 (by rfl) ⟨583251, by rfl⟩ : syracuseStep 1555337 = 1166503) B1166503
theorem B1227743 : Blo 818347 1227743 := bstep (se 1 (by rfl) ⟨920807, by rfl⟩ : syracuseStep 1227743 = 1841615) B1841615
theorem B1227803 : Blo 818347 1227803 := bstep (se 1 (by rfl) ⟨920852, by rfl⟩ : syracuseStep 1227803 = 1841705) B1841705
theorem B2768255 : Blo 818347 2768255 := bstep (se 1 (by rfl) ⟨2076191, by rfl⟩ : syracuseStep 2768255 = 4152383) B4152383
theorem B4144607 : Blo 818347 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B1228655 : Blo 818347 1228655 := bstep (se 1 (by rfl) ⟨921491, by rfl⟩ : syracuseStep 1228655 = 1842983) B1842983
theorem B2768795 : Blo 818347 2768795 := bstep (se 1 (by rfl) ⟨2076596, by rfl⟩ : syracuseStep 2768795 = 4153193) B4153193
theorem B13516753 : Blo 818347 13516753 := bstep (se 2 (by rfl) ⟨5068782, by rfl⟩ : syracuseStep 13516753 = 10137565) B10137565
theorem B6996077 : Blo 818347 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B6242669 : Blo 818347 6242669 := bstep (se 3 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 6242669 = 2341001) B2341001
theorem B7881583 : Blo 818347 7881583 := bstep (se 1 (by rfl) ⟨5911187, by rfl⟩ : syracuseStep 7881583 = 11822375) B11822375
theorem B10503341 : Blo 818347 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B3556541 : Blo 818347 3556541 := bstep (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) B1333703
theorem B2770145 : Blo 818347 2770145 := bstep (se 2 (by rfl) ⟨1038804, by rfl⟩ : syracuseStep 2770145 = 2077609) B2077609
theorem B1557767 : Blo 818347 1557767 := bstep (se 1 (by rfl) ⟨1168325, by rfl⟩ : syracuseStep 1557767 = 2336651) B2336651
theorem B1230191 : Blo 818347 1230191 := bstep (se 1 (by rfl) ⟨922643, by rfl⟩ : syracuseStep 1230191 = 1845287) B1845287
theorem B1230311 : Blo 818347 1230311 := bstep (se 1 (by rfl) ⟨922733, by rfl⟩ : syracuseStep 1230311 = 1845467) B1845467
theorem B13321837 : Blo 818347 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B1230491 : Blo 818347 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B2770685 : Blo 818347 2770685 := bstep (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) B1039007
theorem B1755017 : Blo 818347 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B7489739 : Blo 818347 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B1231079 : Blo 818347 1231079 := bstep (se 1 (by rfl) ⟨923309, by rfl⟩ : syracuseStep 1231079 = 1846619) B1846619
theorem B6408503 : Blo 818347 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B1558921 : Blo 818347 1558921 := bstep (se 2 (by rfl) ⟨584595, by rfl⟩ : syracuseStep 1558921 = 1169191) B1169191
theorem B1231259 : Blo 818347 1231259 := bstep (se 1 (by rfl) ⟨923444, by rfl⟩ : syracuseStep 1231259 = 1846889) B1846889
theorem B1231679 : Blo 818347 1231679 := bstep (se 1 (by rfl) ⟨923759, by rfl⟩ : syracuseStep 1231679 = 1847519) B1847519
theorem B5000075 : Blo 818347 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B3951499 : Blo 818347 3951499 := bstep (se 1 (by rfl) ⟨2963624, by rfl⟩ : syracuseStep 3951499 = 5927249) B5927249
theorem B4148333 : Blo 818347 4148333 := bstep (se 3 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 4148333 = 1555625) B1555625
theorem B1232009 : Blo 818347 1232009 := bstep (se 2 (by rfl) ⟨462003, by rfl⟩ : syracuseStep 1232009 = 924007) B924007
theorem B1232063 : Blo 818347 1232063 := bstep (se 1 (by rfl) ⟨924047, by rfl⟩ : syracuseStep 1232063 = 1848095) B1848095
theorem B1232351 : Blo 818347 1232351 := bstep (se 1 (by rfl) ⟨924263, by rfl⟩ : syracuseStep 1232351 = 1848527) B1848527
theorem B1232411 : Blo 818347 1232411 := bstep (se 1 (by rfl) ⟨924308, by rfl⟩ : syracuseStep 1232411 = 1848617) B1848617
theorem B1232831 : Blo 818347 1232831 := bstep (se 1 (by rfl) ⟨924623, by rfl⟩ : syracuseStep 1232831 = 1849247) B1849247
theorem B4673801 : Blo 818347 4673801 := bstep (se 2 (by rfl) ⟨1752675, by rfl⟩ : syracuseStep 4673801 = 3505351) B3505351
theorem B4444463 : Blo 818347 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B4673983 : Blo 818347 4673983 := bstep (se 1 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 4673983 = 7010975) B7010975
theorem B2774087 : Blo 818347 2774087 := bstep (se 1 (by rfl) ⟨2080565, by rfl⟩ : syracuseStep 2774087 = 4161131) B4161131
theorem B5461355 : Blo 818347 5461355 := bstep (se 1 (by rfl) ⟨4096016, by rfl⟩ : syracuseStep 5461355 = 8192033) B8192033
theorem B4675367 : Blo 818347 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B874523 : Blo 818347 874523 := bstep (se 1 (by rfl) ⟨655892, by rfl⟩ : syracuseStep 874523 = 1311785) B1311785
theorem B2775167 : Blo 818347 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B6215939 : Blo 818347 6215939 := bstep (se 1 (by rfl) ⟨4661954, by rfl⟩ : syracuseStep 6215939 = 9323909) B9323909
theorem B6216425 : Blo 818347 6216425 := bstep (se 2 (by rfl) ⟨2331159, by rfl⟩ : syracuseStep 6216425 = 4662319) B4662319
theorem B1039387 : Blo 818347 1039387 := bstep (se 1 (by rfl) ⟨779540, by rfl⟩ : syracuseStep 1039387 = 1559081) B1559081
theorem B1662263 : Blo 818347 1662263 := bstep (se 1 (by rfl) ⟨1246697, by rfl⟩ : syracuseStep 1662263 = 2493395) B2493395
theorem B876539 : Blo 818347 876539 := bstep (se 1 (by rfl) ⟨657404, by rfl⟩ : syracuseStep 876539 = 1314809) B1314809
theorem B3498653 : Blo 818347 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B70116997 : Blo 818347 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B14935691 : Blo 818347 14935691 := bstep (se 1 (by rfl) ⟨11201768, by rfl⟩ : syracuseStep 14935691 = 22403537) B22403537
theorem B3369575 : Blo 818347 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B2813143 : Blo 818347 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B113831405 : Blo 818347 113831405 := bstep (se 3 (by rfl) ⟨21343388, by rfl⟩ : syracuseStep 113831405 = 42686777) B42686777
theorem B3502207 : Blo 818347 3502207 := bstep (se 1 (by rfl) ⟨2626655, by rfl⟩ : syracuseStep 3502207 = 5253311) B5253311
theorem B3109063 : Blo 818347 3109063 := bstep (se 1 (by rfl) ⟨2331797, by rfl⟩ : syracuseStep 3109063 = 4663595) B4663595
theorem B6648203 : Blo 818347 6648203 := bstep (se 1 (by rfl) ⟨4986152, by rfl⟩ : syracuseStep 6648203 = 9972305) B9972305
theorem B12612347 : Blo 818347 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B3110507 : Blo 818347 3110507 := bstep (se 1 (by rfl) ⟨2332880, by rfl⟩ : syracuseStep 3110507 = 4665761) B4665761
theorem B3110795 : Blo 818347 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B3111007 : Blo 818347 3111007 := bstep (se 1 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 3111007 = 4666511) B4666511
theorem B20183215 : Blo 818347 20183215 := bstep (se 1 (by rfl) ⟨15137411, by rfl⟩ : syracuseStep 20183215 = 30274823) B30274823
theorem B818655 : Blo 818347 818655 := bstep (se 1 (by rfl) ⟨613991, by rfl⟩ : syracuseStep 818655 = 1227983) B1227983
theorem B818715 : Blo 818347 818715 := bstep (se 1 (by rfl) ⟨614036, by rfl⟩ : syracuseStep 818715 = 1228073) B1228073
theorem B818735 : Blo 818347 818735 := bstep (se 1 (by rfl) ⟨614051, by rfl⟩ : syracuseStep 818735 = 1228103) B1228103
theorem B819135 : Blo 818347 819135 := bstep (se 1 (by rfl) ⟨614351, by rfl⟩ : syracuseStep 819135 = 1228703) B1228703
theorem B819195 : Blo 818347 819195 := bstep (se 1 (by rfl) ⟨614396, by rfl⟩ : syracuseStep 819195 = 1228793) B1228793
theorem B4161779 : Blo 818347 4161779 := bstep (se 1 (by rfl) ⟨3121334, by rfl⟩ : syracuseStep 4161779 = 6242669) B6242669
theorem B2621735 : Blo 818347 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B820127 : Blo 818347 820127 := bstep (se 1 (by rfl) ⟨615095, by rfl⟩ : syracuseStep 820127 = 1230191) B1230191
theorem B820207 : Blo 818347 820207 := bstep (se 1 (by rfl) ⟨615155, by rfl⟩ : syracuseStep 820207 = 1230311) B1230311
theorem B17728541 : Blo 818347 17728541 := bstep (se 3 (by rfl) ⟨3324101, by rfl⟩ : syracuseStep 17728541 = 6648203) B6648203
theorem B820327 : Blo 818347 820327 := bstep (se 1 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 820327 = 1230491) B1230491
theorem B2491643 : Blo 818347 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B820719 : Blo 818347 820719 := bstep (se 1 (by rfl) ⟨615539, by rfl⟩ : syracuseStep 820719 = 1231079) B1231079
theorem B820839 : Blo 818347 820839 := bstep (se 1 (by rfl) ⟨615629, by rfl⟩ : syracuseStep 820839 = 1231259) B1231259
theorem B821119 : Blo 818347 821119 := bstep (se 1 (by rfl) ⟨615839, by rfl⟩ : syracuseStep 821119 = 1231679) B1231679
theorem B19990547 : Blo 818347 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B821339 : Blo 818347 821339 := bstep (se 1 (by rfl) ⟨616004, by rfl⟩ : syracuseStep 821339 = 1232009) B1232009
theorem B821375 : Blo 818347 821375 := bstep (se 1 (by rfl) ⟨616031, by rfl⟩ : syracuseStep 821375 = 1232063) B1232063
theorem B17762449 : Blo 818347 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B93489329 : Blo 818347 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B821567 : Blo 818347 821567 := bstep (se 1 (by rfl) ⟨616175, by rfl⟩ : syracuseStep 821567 = 1232351) B1232351
theorem B821607 : Blo 818347 821607 := bstep (se 1 (by rfl) ⟨616205, by rfl⟩ : syracuseStep 821607 = 1232411) B1232411
theorem B821887 : Blo 818347 821887 := bstep (se 1 (by rfl) ⟨616415, by rfl⟩ : syracuseStep 821887 = 1232831) B1232831
theorem B3115867 : Blo 818347 3115867 := bstep (se 1 (by rfl) ⟨2336900, by rfl⟩ : syracuseStep 3115867 = 4673801) B4673801
theorem B1576127 : Blo 818347 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B921199 : Blo 818347 921199 := bstep (se 1 (by rfl) ⟨690899, by rfl⟩ : syracuseStep 921199 = 1381799) B1381799
theorem B3116825 : Blo 818347 3116825 := bstep (se 2 (by rfl) ⟨1168809, by rfl⟩ : syracuseStep 3116825 = 2337619) B2337619
theorem B1314623 : Blo 818347 1314623 := bstep (se 1 (by rfl) ⟨985967, by rfl⟩ : syracuseStep 1314623 = 1971935) B1971935
theorem B3116911 : Blo 818347 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B921883 : Blo 818347 921883 := bstep (se 1 (by rfl) ⟨691412, by rfl⟩ : syracuseStep 921883 = 1382825) B1382825
theorem B4985279 : Blo 818347 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B11833789 : Blo 818347 11833789 := bstep (se 3 (by rfl) ⟨2218835, by rfl⟩ : syracuseStep 11833789 = 4437671) B4437671
theorem B6230519 : Blo 818347 6230519 := bstep (se 1 (by rfl) ⟨4672889, by rfl⟩ : syracuseStep 6230519 = 9345779) B9345779
theorem B2626553 : Blo 818347 2626553 := bstep (se 2 (by rfl) ⟨984957, by rfl⟩ : syracuseStep 2626553 = 1969915) B1969915
theorem B2332061 : Blo 818347 2332061 := bstep (se 3 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 2332061 = 874523) B874523
theorem B1971803 : Blo 818347 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B6231977 : Blo 818347 6231977 := bstep (se 2 (by rfl) ⟨2336991, by rfl⟩ : syracuseStep 6231977 = 4673983) B4673983
theorem B2627579 : Blo 818347 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B1842119 : Blo 818347 1842119 := bstep (se 1 (by rfl) ⟨1381589, by rfl⟩ : syracuseStep 1842119 = 2763179) B2763179
theorem B924655 : Blo 818347 924655 := bstep (se 1 (by rfl) ⟨693491, by rfl⟩ : syracuseStep 924655 = 1386983) B1386983
theorem B2956475 : Blo 818347 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B2628911 : Blo 818347 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B1842515 : Blo 818347 1842515 := bstep (se 1 (by rfl) ⟨1381886, by rfl⟩ : syracuseStep 1842515 = 2763773) B2763773
theorem B1843163 : Blo 818347 1843163 := bstep (se 1 (by rfl) ⟨1382372, by rfl⟩ : syracuseStep 1843163 = 2764745) B2764745
theorem B26910953 : Blo 818347 26910953 := bstep (se 2 (by rfl) ⟨10091607, by rfl⟩ : syracuseStep 26910953 = 20183215) B20183215
theorem B1844009 : Blo 818347 1844009 := bstep (se 2 (by rfl) ⟨691503, by rfl⟩ : syracuseStep 1844009 = 1383007) B1383007
theorem B2073671 : Blo 818347 2073671 := bstep (se 1 (by rfl) ⟨1555253, by rfl⟩ : syracuseStep 2073671 = 3110507) B3110507
theorem B1844459 : Blo 818347 1844459 := bstep (se 1 (by rfl) ⟨1383344, by rfl⟩ : syracuseStep 1844459 = 2766689) B2766689
theorem B2073863 : Blo 818347 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B1385849 : Blo 818347 1385849 := bstep (se 2 (by rfl) ⟨519693, by rfl⟩ : syracuseStep 1385849 = 1039387) B1039387
theorem B2762207 : Blo 818347 2762207 := bstep (se 1 (by rfl) ⟨2071655, by rfl⟩ : syracuseStep 2762207 = 4143311) B4143311
theorem B1845503 : Blo 818347 1845503 := bstep (se 1 (by rfl) ⟨1384127, by rfl⟩ : syracuseStep 1845503 = 2768255) B2768255
theorem B2763071 : Blo 818347 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B1845863 : Blo 818347 1845863 := bstep (se 1 (by rfl) ⟨1384397, by rfl⟩ : syracuseStep 1845863 = 2768795) B2768795
theorem B2337437 : Blo 818347 2337437 := bstep (se 3 (by rfl) ⟨438269, by rfl⟩ : syracuseStep 2337437 = 876539) B876539
theorem B4664051 : Blo 818347 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B1846025 : Blo 818347 1846025 := bstep (se 2 (by rfl) ⟨692259, by rfl⟩ : syracuseStep 1846025 = 1384519) B1384519
theorem B2371027 : Blo 818347 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B1846763 : Blo 818347 1846763 := bstep (se 1 (by rfl) ⟨1385072, by rfl⟩ : syracuseStep 1846763 = 2770145) B2770145
theorem B1847123 : Blo 818347 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B4993159 : Blo 818347 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B4272335 : Blo 818347 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B2765555 : Blo 818347 2765555 := bstep (se 1 (by rfl) ⟨2074166, by rfl⟩ : syracuseStep 2765555 = 4148333) B4148333
theorem B29897657 : Blo 818347 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B15742025 : Blo 818347 15742025 := bstep (se 2 (by rfl) ⟨5903259, by rfl⟩ : syracuseStep 15742025 = 11806519) B11806519
theorem B2962975 : Blo 818347 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B2078561 : Blo 818347 2078561 := bstep (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) B1558921
theorem B1849391 : Blo 818347 1849391 := bstep (se 1 (by rfl) ⟨1387043, by rfl⟩ : syracuseStep 1849391 = 2774087) B2774087
theorem B14563613 : Blo 818347 14563613 := bstep (se 3 (by rfl) ⟨2730677, by rfl⟩ : syracuseStep 14563613 = 5461355) B5461355
theorem B1849697 : Blo 818347 1849697 := bstep (se 2 (by rfl) ⟨693636, by rfl⟩ : syracuseStep 1849697 = 1387273) B1387273
theorem B2767337 : Blo 818347 2767337 := bstep (se 2 (by rfl) ⟨1037751, by rfl⟩ : syracuseStep 2767337 = 2075503) B2075503
theorem B1850111 : Blo 818347 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B4143959 : Blo 818347 4143959 := bstep (se 1 (by rfl) ⟨3107969, by rfl⟩ : syracuseStep 4143959 = 6215939) B6215939
theorem B3750857 : Blo 818347 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B4144283 : Blo 818347 4144283 := bstep (se 1 (by rfl) ⟨3108212, by rfl⟩ : syracuseStep 4144283 = 6216425) B6216425
theorem B1228187 : Blo 818347 1228187 := bstep (se 1 (by rfl) ⟨921140, by rfl⟩ : syracuseStep 1228187 = 1842281) B1842281
theorem B31571531 : Blo 818347 31571531 := bstep (se 1 (by rfl) ⟨23678648, by rfl⟩ : syracuseStep 31571531 = 47357297) B47357297
theorem B6307865 : Blo 818347 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B1228871 : Blo 818347 1228871 := bstep (se 1 (by rfl) ⟨921653, by rfl⟩ : syracuseStep 1228871 = 1843307) B1843307
theorem B5390473 : Blo 818347 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B4669609 : Blo 818347 4669609 := bstep (se 2 (by rfl) ⟨1751103, by rfl⟩ : syracuseStep 4669609 = 3502207) B3502207
theorem B4145417 : Blo 818347 4145417 := bstep (se 2 (by rfl) ⟨1554531, by rfl⟩ : syracuseStep 4145417 = 3109063) B3109063
theorem B1229291 : Blo 818347 1229291 := bstep (se 1 (by rfl) ⟨921968, by rfl⟩ : syracuseStep 1229291 = 1843937) B1843937
theorem B1229519 : Blo 818347 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B1229705 : Blo 818347 1229705 := bstep (se 2 (by rfl) ⟨461139, by rfl⟩ : syracuseStep 1229705 = 922279) B922279
theorem B1229993 : Blo 818347 1229993 := bstep (se 2 (by rfl) ⟨461247, by rfl⟩ : syracuseStep 1229993 = 922495) B922495
theorem B1230089 : Blo 818347 1230089 := bstep (se 2 (by rfl) ⟨461283, by rfl⟩ : syracuseStep 1230089 = 922567) B922567
theorem B1230569 : Blo 818347 1230569 := bstep (se 2 (by rfl) ⟨461463, by rfl⟩ : syracuseStep 1230569 = 922927) B922927
theorem B2246383 : Blo 818347 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B1230695 : Blo 818347 1230695 := bstep (se 1 (by rfl) ⟨923021, by rfl⟩ : syracuseStep 1230695 = 1846043) B1846043
theorem B25282813 : Blo 818347 25282813 := bstep (se 3 (by rfl) ⟨4740527, by rfl⟩ : syracuseStep 25282813 = 9481055) B9481055
theorem B1231103 : Blo 818347 1231103 := bstep (se 1 (by rfl) ⟨923327, by rfl⟩ : syracuseStep 1231103 = 1846655) B1846655
theorem B1231343 : Blo 818347 1231343 := bstep (se 1 (by rfl) ⟨923507, by rfl⟩ : syracuseStep 1231343 = 1847015) B1847015
theorem B4148009 : Blo 818347 4148009 := bstep (se 2 (by rfl) ⟨1555503, by rfl⟩ : syracuseStep 4148009 = 3111007) B3111007
theorem B1756127 : Blo 818347 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B8408231 : Blo 818347 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B1232231 : Blo 818347 1232231 := bstep (se 1 (by rfl) ⟨924173, by rfl⟩ : syracuseStep 1232231 = 1848347) B1848347
theorem B1035823 : Blo 818347 1035823 := bstep (se 1 (by rfl) ⟨776867, by rfl⟩ : syracuseStep 1035823 = 1553735) B1553735
theorem B1232807 : Blo 818347 1232807 := bstep (se 1 (by rfl) ⟨924605, by rfl⟩ : syracuseStep 1232807 = 1849211) B1849211
theorem B6082775 : Blo 818347 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B1036891 : Blo 818347 1036891 := bstep (se 1 (by rfl) ⟨777668, by rfl⟩ : syracuseStep 1036891 = 1555337) B1555337
theorem B7002227 : Blo 818347 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B1038511 : Blo 818347 1038511 := bstep (se 1 (by rfl) ⟨778883, by rfl⟩ : syracuseStep 1038511 = 1557767) B1557767
theorem B4675967 : Blo 818347 4675967 := bstep (se 1 (by rfl) ⟨3506975, by rfl⟩ : syracuseStep 4675967 = 7013951) B7013951
theorem B10508777 : Blo 818347 10508777 := bstep (se 2 (by rfl) ⟨3940791, by rfl⟩ : syracuseStep 10508777 = 7881583) B7881583
theorem B1170011 : Blo 818347 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B4676399 : Blo 818347 4676399 := bstep (se 1 (by rfl) ⟨3507299, by rfl⟩ : syracuseStep 4676399 = 7014599) B7014599
theorem B9329741 : Blo 818347 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B4152545 : Blo 818347 4152545 := bstep (se 2 (by rfl) ⟨1557204, by rfl⟩ : syracuseStep 4152545 = 3114409) B3114409
theorem B4218115 : Blo 818347 4218115 := bstep (se 1 (by rfl) ⟨3163586, by rfl⟩ : syracuseStep 4218115 = 6327173) B6327173
theorem B3333383 : Blo 818347 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B4743463 : Blo 818347 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B6218369 : Blo 818347 6218369 := bstep (se 2 (by rfl) ⟨2331888, by rfl⟩ : syracuseStep 6218369 = 4663777) B4663777
theorem B5268665 : Blo 818347 5268665 := bstep (se 2 (by rfl) ⟨1975749, by rfl⟩ : syracuseStep 5268665 = 3951499) B3951499
theorem B9364733 : Blo 818347 9364733 := bstep (se 3 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 9364733 = 3511775) B3511775
theorem B1108175 : Blo 818347 1108175 := bstep (se 1 (by rfl) ⟨831131, by rfl⟩ : syracuseStep 1108175 = 1662263) B1662263
theorem B7006601 : Blo 818347 7006601 := bstep (se 2 (by rfl) ⟨2627475, by rfl⟩ : syracuseStep 7006601 = 5254951) B5254951
theorem B3107591 : Blo 818347 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B9957127 : Blo 818347 9957127 := bstep (se 1 (by rfl) ⟨7467845, by rfl⟩ : syracuseStep 9957127 = 14935691) B14935691
theorem B14970653 : Blo 818347 14970653 := bstep (se 3 (by rfl) ⟨2806997, by rfl⟩ : syracuseStep 14970653 = 5613995) B5613995
theorem B11824973 : Blo 818347 11824973 := bstep (se 3 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 11824973 = 4434365) B4434365
theorem B4681799 : Blo 818347 4681799 := bstep (se 1 (by rfl) ⟨3511349, by rfl⟩ : syracuseStep 4681799 = 7022699) B7022699
theorem B75887603 : Blo 818347 75887603 := bstep (se 1 (by rfl) ⟨56915702, by rfl⟩ : syracuseStep 75887603 = 113831405) B113831405
theorem B3110521 : Blo 818347 3110521 := bstep (se 2 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 3110521 = 2332891) B2332891
theorem B9337031 : Blo 818347 9337031 := bstep (se 1 (by rfl) ⟨7002773, by rfl⟩ : syracuseStep 9337031 = 14005547) B14005547
theorem B4159835 : Blo 818347 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B4160159 : Blo 818347 4160159 := bstep (se 1 (by rfl) ⟨3120119, by rfl⟩ : syracuseStep 4160159 = 6240239) B6240239
theorem B818495 : Blo 818347 818495 := bstep (se 1 (by rfl) ⟨613871, by rfl⟩ : syracuseStep 818495 = 1227743) B1227743
theorem B818535 : Blo 818347 818535 := bstep (se 1 (by rfl) ⟨613901, by rfl⟩ : syracuseStep 818535 = 1227803) B1227803
theorem B819103 : Blo 818347 819103 := bstep (se 1 (by rfl) ⟨614327, by rfl⟩ : syracuseStep 819103 = 1228655) B1228655
theorem B18022337 : Blo 818347 18022337 := bstep (se 2 (by rfl) ⟨6758376, by rfl⟩ : syracuseStep 18022337 = 13516753) B13516753
theorem B819247 : Blo 818347 819247 := bstep (se 1 (by rfl) ⟨614435, by rfl⟩ : syracuseStep 819247 = 1228871) B1228871
theorem B6226145 : Blo 818347 6226145 := bstep (se 2 (by rfl) ⟨2334804, by rfl⟩ : syracuseStep 6226145 = 4669609) B4669609
theorem B819527 : Blo 818347 819527 := bstep (se 1 (by rfl) ⟨614645, by rfl⟩ : syracuseStep 819527 = 1229291) B1229291
theorem B6324617 : Blo 818347 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B819679 : Blo 818347 819679 := bstep (se 1 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 819679 = 1229519) B1229519
theorem B819803 : Blo 818347 819803 := bstep (se 1 (by rfl) ⟨614852, by rfl⟩ : syracuseStep 819803 = 1229705) B1229705
theorem B819995 : Blo 818347 819995 := bstep (se 1 (by rfl) ⟨614996, by rfl⟩ : syracuseStep 819995 = 1229993) B1229993
theorem B820059 : Blo 818347 820059 := bstep (se 1 (by rfl) ⟨615044, by rfl⟩ : syracuseStep 820059 = 1230089) B1230089
theorem B820379 : Blo 818347 820379 := bstep (se 1 (by rfl) ⟨615284, by rfl⟩ : syracuseStep 820379 = 1230569) B1230569
theorem B820463 : Blo 818347 820463 := bstep (se 1 (by rfl) ⟨615347, by rfl⟩ : syracuseStep 820463 = 1230695) B1230695
theorem B62326219 : Blo 818347 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B820735 : Blo 818347 820735 := bstep (se 1 (by rfl) ⟨615551, by rfl⟩ : syracuseStep 820735 = 1231103) B1231103
theorem B820895 : Blo 818347 820895 := bstep (se 1 (by rfl) ⟨615671, by rfl⟩ : syracuseStep 820895 = 1231343) B1231343
theorem B5605487 : Blo 818347 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B1050751 : Blo 818347 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B821487 : Blo 818347 821487 := bstep (se 1 (by rfl) ⟨616115, by rfl⟩ : syracuseStep 821487 = 1232231) B1232231
theorem B821871 : Blo 818347 821871 := bstep (se 1 (by rfl) ⟨616403, by rfl⟩ : syracuseStep 821871 = 1232807) B1232807
theorem B3117311 : Blo 818347 3117311 := bstep (se 1 (by rfl) ⟨2337983, by rfl⟩ : syracuseStep 3117311 = 4675967) B4675967
theorem B3117599 : Blo 818347 3117599 := bstep (se 1 (by rfl) ⟨2338199, by rfl⟩ : syracuseStep 3117599 = 4676399) B4676399
theorem B1381097 : Blo 818347 1381097 := bstep (se 2 (by rfl) ⟨517911, by rfl⟩ : syracuseStep 1381097 = 1035823) B1035823
theorem B1970983 : Blo 818347 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B13276169 : Blo 818347 13276169 := bstep (se 2 (by rfl) ⟨4978563, by rfl⟩ : syracuseStep 13276169 = 9957127) B9957127
theorem B6657545 : Blo 818347 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B2955133 : Blo 818347 2955133 := bstep (se 3 (by rfl) ⟨554087, by rfl⟩ : syracuseStep 2955133 = 1108175) B1108175
theorem B1382447 : Blo 818347 1382447 := bstep (se 1 (by rfl) ⟨1036835, by rfl⟩ : syracuseStep 1382447 = 2073671) B2073671
theorem B1382521 : Blo 818347 1382521 := bstep (se 2 (by rfl) ⟨518445, by rfl⟩ : syracuseStep 1382521 = 1036891) B1036891
theorem B3512443 : Blo 818347 3512443 := bstep (se 1 (by rfl) ⟨2634332, by rfl⟩ : syracuseStep 3512443 = 5268665) B5268665
theorem B1382575 : Blo 818347 1382575 := bstep (se 1 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 1382575 = 2073863) B2073863
theorem B923899 : Blo 818347 923899 := bstep (se 1 (by rfl) ⟨692924, by rfl⟩ : syracuseStep 923899 = 1385849) B1385849
theorem B1841471 : Blo 818347 1841471 := bstep (se 1 (by rfl) ⟨1381103, by rfl⟩ : syracuseStep 1841471 = 2762207) B2762207
theorem B1842047 : Blo 818347 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B3120029 : Blo 818347 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B2071727 : Blo 818347 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B3121199 : Blo 818347 3121199 := bstep (se 1 (by rfl) ⟨2340899, by rfl⟩ : syracuseStep 3121199 = 4681799) B4681799
theorem B1384681 : Blo 818347 1384681 := bstep (se 2 (by rfl) ⟨519255, by rfl⟩ : syracuseStep 1384681 = 1038511) B1038511
theorem B1843703 : Blo 818347 1843703 := bstep (se 1 (by rfl) ⟨1382777, by rfl⟩ : syracuseStep 1843703 = 2765555) B2765555
theorem B19931771 : Blo 818347 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B10494683 : Blo 818347 10494683 := bstep (se 1 (by rfl) ⟨7871012, by rfl⟩ : syracuseStep 10494683 = 15742025) B15742025
theorem B1385707 : Blo 818347 1385707 := bstep (se 1 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 1385707 = 2078561) B2078561
theorem B9709075 : Blo 818347 9709075 := bstep (se 1 (by rfl) ⟨7281806, by rfl⟩ : syracuseStep 9709075 = 14563613) B14563613
theorem B1844891 : Blo 818347 1844891 := bstep (se 1 (by rfl) ⟨1383668, by rfl⟩ : syracuseStep 1844891 = 2767337) B2767337
theorem B2762639 : Blo 818347 2762639 := bstep (se 1 (by rfl) ⟨2071979, by rfl⟩ : syracuseStep 2762639 = 4143959) B4143959
theorem B2500571 : Blo 818347 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B2762855 : Blo 818347 2762855 := bstep (se 1 (by rfl) ⟨2072141, by rfl⟩ : syracuseStep 2762855 = 4144283) B4144283
theorem B21047687 : Blo 818347 21047687 := bstep (se 1 (by rfl) ⟨15785765, by rfl⟩ : syracuseStep 21047687 = 31571531) B31571531
theorem B4205243 : Blo 818347 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B2763611 : Blo 818347 2763611 := bstep (se 1 (by rfl) ⟨2072708, by rfl⟩ : syracuseStep 2763611 = 4145417) B4145417
theorem B7187297 : Blo 818347 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B1747823 : Blo 818347 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B2765339 : Blo 818347 2765339 := bstep (se 1 (by rfl) ⟨2074004, by rfl⟩ : syracuseStep 2765339 = 4148009) B4148009
theorem B2995177 : Blo 818347 2995177 := bstep (se 2 (by rfl) ⟨1123191, by rfl⟩ : syracuseStep 2995177 = 2246383) B2246383
theorem B2077883 : Blo 818347 2077883 := bstep (se 1 (by rfl) ⟨1558412, by rfl⟩ : syracuseStep 2077883 = 3116825) B3116825
theorem B3323519 : Blo 818347 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B1554707 : Blo 818347 1554707 := bstep (se 1 (by rfl) ⟨1166030, by rfl⟩ : syracuseStep 1554707 = 2332061) B2332061
theorem B1751719 : Blo 818347 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B4668151 : Blo 818347 4668151 := bstep (se 1 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 4668151 = 7002227) B7002227
theorem B5258141 : Blo 818347 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B3161369 : Blo 818347 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B1228079 : Blo 818347 1228079 := bstep (se 1 (by rfl) ⟨921059, by rfl⟩ : syracuseStep 1228079 = 1842119) B1842119
theorem B1228265 : Blo 818347 1228265 := bstep (se 2 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 1228265 = 921199) B921199
theorem B2768363 : Blo 818347 2768363 := bstep (se 1 (by rfl) ⟨2076272, by rfl⟩ : syracuseStep 2768363 = 4152545) B4152545
theorem B1752607 : Blo 818347 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B1228343 : Blo 818347 1228343 := bstep (se 1 (by rfl) ⟨921257, by rfl⟩ : syracuseStep 1228343 = 1842515) B1842515
theorem B1228775 : Blo 818347 1228775 := bstep (se 1 (by rfl) ⟨921581, by rfl⟩ : syracuseStep 1228775 = 1843163) B1843163
theorem B17940635 : Blo 818347 17940635 := bstep (se 1 (by rfl) ⟨13455476, by rfl⟩ : syracuseStep 17940635 = 26910953) B26910953
theorem B1229177 : Blo 818347 1229177 := bstep (se 2 (by rfl) ⟨460941, by rfl⟩ : syracuseStep 1229177 = 921883) B921883
theorem B4145579 : Blo 818347 4145579 := bstep (se 1 (by rfl) ⟨3109184, by rfl⟩ : syracuseStep 4145579 = 6218369) B6218369
theorem B1229339 : Blo 818347 1229339 := bstep (se 1 (by rfl) ⟨922004, by rfl⟩ : syracuseStep 1229339 = 1844009) B1844009
theorem B15778385 : Blo 818347 15778385 := bstep (se 2 (by rfl) ⟨5916894, by rfl⟩ : syracuseStep 15778385 = 11833789) B11833789
theorem B1229639 : Blo 818347 1229639 := bstep (se 1 (by rfl) ⟨922229, by rfl⟩ : syracuseStep 1229639 = 1844459) B1844459
theorem B6243155 : Blo 818347 6243155 := bstep (se 1 (by rfl) ⟨4682366, by rfl⟩ : syracuseStep 6243155 = 9364733) B9364733
theorem B1230335 : Blo 818347 1230335 := bstep (se 1 (by rfl) ⟨922751, by rfl⟩ : syracuseStep 1230335 = 1845503) B1845503
theorem B4671067 : Blo 818347 4671067 := bstep (se 1 (by rfl) ⟨3503300, by rfl⟩ : syracuseStep 4671067 = 7006601) B7006601
theorem B1230575 : Blo 818347 1230575 := bstep (se 1 (by rfl) ⟨922931, by rfl⟩ : syracuseStep 1230575 = 1845863) B1845863
theorem B1558291 : Blo 818347 1558291 := bstep (se 1 (by rfl) ⟨1168718, by rfl⟩ : syracuseStep 1558291 = 2337437) B2337437
theorem B1230683 : Blo 818347 1230683 := bstep (se 1 (by rfl) ⟨923012, by rfl⟩ : syracuseStep 1230683 = 1846025) B1846025
theorem B3950633 : Blo 818347 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B4147361 : Blo 818347 4147361 := bstep (se 2 (by rfl) ⟨1555260, by rfl⟩ : syracuseStep 4147361 = 3110521) B3110521
theorem B1231175 : Blo 818347 1231175 := bstep (se 1 (by rfl) ⟨923381, by rfl⟩ : syracuseStep 1231175 = 1846763) B1846763
theorem B9980435 : Blo 818347 9980435 := bstep (se 1 (by rfl) ⟨7485326, by rfl⟩ : syracuseStep 9980435 = 14970653) B14970653
theorem B7883315 : Blo 818347 7883315 := bstep (se 1 (by rfl) ⟨5912486, by rfl⟩ : syracuseStep 7883315 = 11824973) B11824973
theorem B1231415 : Blo 818347 1231415 := bstep (se 1 (by rfl) ⟨923561, by rfl⟩ : syracuseStep 1231415 = 1847123) B1847123
theorem B1232873 : Blo 818347 1232873 := bstep (se 2 (by rfl) ⟨462327, by rfl⟩ : syracuseStep 1232873 = 924655) B924655
theorem B1232927 : Blo 818347 1232927 := bstep (se 1 (by rfl) ⟨924695, by rfl⟩ : syracuseStep 1232927 = 1849391) B1849391
theorem B2773223 : Blo 818347 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B1233131 : Blo 818347 1233131 := bstep (se 1 (by rfl) ⟨924848, by rfl⟩ : syracuseStep 1233131 = 1849697) B1849697
theorem B5624153 : Blo 818347 5624153 := bstep (se 2 (by rfl) ⟨2109057, by rfl⟩ : syracuseStep 5624153 = 4218115) B4218115
theorem B2773439 : Blo 818347 2773439 := bstep (se 1 (by rfl) ⟨2080079, by rfl⟩ : syracuseStep 2773439 = 4160159) B4160159
theorem B1233407 : Blo 818347 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B12014891 : Blo 818347 12014891 := bstep (se 1 (by rfl) ⟨9011168, by rfl⟩ : syracuseStep 12014891 = 18022337) B18022337
theorem B2774519 : Blo 818347 2774519 := bstep (se 1 (by rfl) ⟨2080889, by rfl⟩ : syracuseStep 2774519 = 4161779) B4161779
theorem B11819027 : Blo 818347 11819027 := bstep (se 1 (by rfl) ⟨8864270, by rfl⟩ : syracuseStep 11819027 = 17728541) B17728541
theorem B1661095 : Blo 818347 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B13327031 : Blo 818347 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B876415 : Blo 818347 876415 := bstep (se 1 (by rfl) ⟨657311, by rfl⟩ : syracuseStep 876415 = 1314623) B1314623
theorem B7004141 : Blo 818347 7004141 := bstep (se 3 (by rfl) ⟨1313276, by rfl⟩ : syracuseStep 7004141 = 2626553) B2626553
theorem B4055183 : Blo 818347 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B23683265 : Blo 818347 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B4153679 : Blo 818347 4153679 := bstep (se 1 (by rfl) ⟨3115259, by rfl⟩ : syracuseStep 4153679 = 6230519) B6230519
theorem B33710417 : Blo 818347 33710417 := bstep (se 2 (by rfl) ⟨12641406, by rfl⟩ : syracuseStep 33710417 = 25282813) B25282813
theorem B4154489 : Blo 818347 4154489 := bstep (se 2 (by rfl) ⟨1557933, by rfl⟩ : syracuseStep 4154489 = 3115867) B3115867
theorem B4154651 : Blo 818347 4154651 := bstep (se 1 (by rfl) ⟨3115988, by rfl⟩ : syracuseStep 4154651 = 6231977) B6231977
theorem B7005851 : Blo 818347 7005851 := bstep (se 1 (by rfl) ⟨5254388, by rfl⟩ : syracuseStep 7005851 = 10508777) B10508777
theorem B6219827 : Blo 818347 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B2222255 : Blo 818347 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B4155881 : Blo 818347 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B3109367 : Blo 818347 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B4683005 : Blo 818347 4683005 := bstep (se 3 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 4683005 = 1756127) B1756127
theorem B2848223 : Blo 818347 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B50591735 : Blo 818347 50591735 := bstep (se 1 (by rfl) ⟨37943801, by rfl⟩ : syracuseStep 50591735 = 75887603) B75887603
theorem B6224687 : Blo 818347 6224687 := bstep (se 1 (by rfl) ⟨4668515, by rfl⟩ : syracuseStep 6224687 = 9337031) B9337031
theorem B818791 : Blo 818347 818791 := bstep (se 1 (by rfl) ⟨614093, by rfl⟩ : syracuseStep 818791 = 1228187) B1228187
theorem B11960423 : Blo 818347 11960423 := bstep (se 1 (by rfl) ⟨8970317, by rfl⟩ : syracuseStep 11960423 = 17940635) B17940635
theorem B819451 : Blo 818347 819451 := bstep (se 1 (by rfl) ⟨614588, by rfl⟩ : syracuseStep 819451 = 1229177) B1229177
theorem B819559 : Blo 818347 819559 := bstep (se 1 (by rfl) ⟨614669, by rfl⟩ : syracuseStep 819559 = 1229339) B1229339
theorem B10518923 : Blo 818347 10518923 := bstep (se 1 (by rfl) ⟨7889192, by rfl⟩ : syracuseStep 10518923 = 15778385) B15778385
theorem B819759 : Blo 818347 819759 := bstep (se 1 (by rfl) ⟨614819, by rfl⟩ : syracuseStep 819759 = 1229639) B1229639
theorem B4162103 : Blo 818347 4162103 := bstep (se 1 (by rfl) ⟨3121577, by rfl⟩ : syracuseStep 4162103 = 6243155) B6243155
theorem B820223 : Blo 818347 820223 := bstep (se 1 (by rfl) ⟨615167, by rfl⟩ : syracuseStep 820223 = 1230335) B1230335
theorem B820383 : Blo 818347 820383 := bstep (se 1 (by rfl) ⟨615287, by rfl⟩ : syracuseStep 820383 = 1230575) B1230575
theorem B820455 : Blo 818347 820455 := bstep (se 1 (by rfl) ⟨615341, by rfl⟩ : syracuseStep 820455 = 1230683) B1230683
theorem B3736991 : Blo 818347 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B820783 : Blo 818347 820783 := bstep (se 1 (by rfl) ⟨615587, by rfl⟩ : syracuseStep 820783 = 1231175) B1231175
theorem B820943 : Blo 818347 820943 := bstep (se 1 (by rfl) ⟨615707, by rfl⟩ : syracuseStep 820943 = 1231415) B1231415
theorem B83101625 : Blo 818347 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B6228089 : Blo 818347 6228089 := bstep (se 2 (by rfl) ⟨2335533, by rfl⟩ : syracuseStep 6228089 = 4671067) B4671067
theorem B821915 : Blo 818347 821915 := bstep (se 1 (by rfl) ⟨616436, by rfl⟩ : syracuseStep 821915 = 1232873) B1232873
theorem B821951 : Blo 818347 821951 := bstep (se 1 (by rfl) ⟨616463, by rfl⟩ : syracuseStep 821951 = 1232927) B1232927
theorem B822087 : Blo 818347 822087 := bstep (se 1 (by rfl) ⟨616565, by rfl⟩ : syracuseStep 822087 = 1233131) B1233131
theorem B822271 : Blo 818347 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B920731 : Blo 818347 920731 := bstep (se 1 (by rfl) ⟨690548, by rfl⟩ : syracuseStep 920731 = 1381097) B1381097
theorem B8850779 : Blo 818347 8850779 := bstep (se 1 (by rfl) ⟨6638084, by rfl⟩ : syracuseStep 8850779 = 13276169) B13276169
theorem B921631 : Blo 818347 921631 := bstep (se 1 (by rfl) ⟨691223, by rfl⟩ : syracuseStep 921631 = 1382447) B1382447
theorem B8884687 : Blo 818347 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B1381151 : Blo 818347 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B2627977 : Blo 818347 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B1841759 : Blo 818347 1841759 := bstep (se 1 (by rfl) ⟨1381319, by rfl⟩ : syracuseStep 1841759 = 2762639) B2762639
theorem B11082349 : Blo 818347 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B26614493 : Blo 818347 26614493 := bstep (se 3 (by rfl) ⟨4990217, by rfl⟩ : syracuseStep 26614493 = 9980435) B9980435
theorem B1841903 : Blo 818347 1841903 := bstep (se 1 (by rfl) ⟨1381427, by rfl⟩ : syracuseStep 1841903 = 2762855) B2762855
theorem B1481503 : Blo 818347 1481503 := bstep (se 1 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 1481503 = 2222255) B2222255
theorem B14031791 : Blo 818347 14031791 := bstep (se 1 (by rfl) ⟨10523843, by rfl⟩ : syracuseStep 14031791 = 21047687) B21047687
theorem B1842407 : Blo 818347 1842407 := bstep (se 1 (by rfl) ⟨1381805, by rfl⟩ : syracuseStep 1842407 = 2763611) B2763611
theorem B4660861 : Blo 818347 4660861 := bstep (se 3 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 4660861 = 1747823) B1747823
theorem B3940177 : Blo 818347 3940177 := bstep (se 2 (by rfl) ⟨1477566, by rfl⟩ : syracuseStep 3940177 = 2955133) B2955133
theorem B51781733 : Blo 818347 51781733 := bstep (se 4 (by rfl) ⟨4854537, by rfl⟩ : syracuseStep 51781733 = 9709075) B9709075
theorem B1843361 : Blo 818347 1843361 := bstep (se 2 (by rfl) ⟨691260, by rfl⟩ : syracuseStep 1843361 = 1382521) B1382521
theorem B9347237 : Blo 818347 9347237 := bstep (se 4 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 9347237 = 1752607) B1752607
theorem B1843433 : Blo 818347 1843433 := bstep (se 2 (by rfl) ⟨691287, by rfl⟩ : syracuseStep 1843433 = 1382575) B1382575
theorem B2072911 : Blo 818347 2072911 := bstep (se 1 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 2072911 = 3109367) B3109367
theorem B1843559 : Blo 818347 1843559 := bstep (se 1 (by rfl) ⟨1382669, by rfl⟩ : syracuseStep 1843559 = 2765339) B2765339
theorem B8430317 : Blo 818347 8430317 := bstep (se 3 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 8430317 = 3161369) B3161369
theorem B1385255 : Blo 818347 1385255 := bstep (se 1 (by rfl) ⟨1038941, by rfl⟩ : syracuseStep 1385255 = 2077883) B2077883
theorem B3122003 : Blo 818347 3122003 := bstep (se 1 (by rfl) ⟨2341502, by rfl⟩ : syracuseStep 3122003 = 4683005) B4683005
theorem B2335625 : Blo 818347 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B33727823 : Blo 818347 33727823 := bstep (se 1 (by rfl) ⟨25295867, by rfl⟩ : syracuseStep 33727823 = 50591735) B50591735
theorem B1845575 : Blo 818347 1845575 := bstep (se 1 (by rfl) ⟨1384181, by rfl⟩ : syracuseStep 1845575 = 2768363) B2768363
theorem B2763719 : Blo 818347 2763719 := bstep (se 1 (by rfl) ⟨2072789, by rfl⟩ : syracuseStep 2763719 = 4145579) B4145579
theorem B1846241 : Blo 818347 1846241 := bstep (se 2 (by rfl) ⟨692340, by rfl⟩ : syracuseStep 1846241 = 1384681) B1384681
theorem B2764907 : Blo 818347 2764907 := bstep (se 1 (by rfl) ⟨2073680, by rfl⟩ : syracuseStep 2764907 = 4147361) B4147361
theorem B1847609 : Blo 818347 1847609 := bstep (se 2 (by rfl) ⟨692853, by rfl⟩ : syracuseStep 1847609 = 1385707) B1385707
theorem B5255543 : Blo 818347 5255543 := bstep (se 1 (by rfl) ⟨3941657, by rfl⟩ : syracuseStep 5255543 = 7883315) B7883315
theorem B2077721 : Blo 818347 2077721 := bstep (se 2 (by rfl) ⟨779145, by rfl⟩ : syracuseStep 2077721 = 1558291) B1558291
theorem B1848815 : Blo 818347 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B2078207 : Blo 818347 2078207 := bstep (se 1 (by rfl) ⟨1558655, by rfl⟩ : syracuseStep 2078207 = 3117311) B3117311
theorem B3749435 : Blo 818347 3749435 := bstep (se 1 (by rfl) ⟨2812076, by rfl⟩ : syracuseStep 3749435 = 5624153) B5624153
theorem B1848959 : Blo 818347 1848959 := bstep (se 1 (by rfl) ⟨1386719, by rfl⟩ : syracuseStep 1848959 = 2773439) B2773439
theorem B2078399 : Blo 818347 2078399 := bstep (se 1 (by rfl) ⟨1558799, by rfl⟩ : syracuseStep 2078399 = 3117599) B3117599
theorem B8009927 : Blo 818347 8009927 := bstep (se 1 (by rfl) ⟨6007445, by rfl⟩ : syracuseStep 8009927 = 12014891) B12014891
theorem B1849679 : Blo 818347 1849679 := bstep (se 1 (by rfl) ⟨1387259, by rfl⟩ : syracuseStep 1849679 = 2774519) B2774519
theorem B4438363 : Blo 818347 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B7879351 : Blo 818347 7879351 := bstep (se 1 (by rfl) ⟨5909513, by rfl⟩ : syracuseStep 7879351 = 11819027) B11819027
theorem B1227647 : Blo 818347 1227647 := bstep (se 1 (by rfl) ⟨920735, by rfl⟩ : syracuseStep 1227647 = 1841471) B1841471
theorem B1228031 : Blo 818347 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B2080019 : Blo 818347 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B4669427 : Blo 818347 4669427 := bstep (se 1 (by rfl) ⟨3502070, by rfl⟩ : syracuseStep 4669427 = 7004141) B7004141
theorem B2080799 : Blo 818347 2080799 := bstep (se 1 (by rfl) ⟨1560599, by rfl⟩ : syracuseStep 2080799 = 3121199) B3121199
theorem B2703455 : Blo 818347 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B10535021 : Blo 818347 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B2769119 : Blo 818347 2769119 := bstep (se 1 (by rfl) ⟨2076839, by rfl⟩ : syracuseStep 2769119 = 4153679) B4153679
theorem B1229135 : Blo 818347 1229135 := bstep (se 1 (by rfl) ⟨921851, by rfl⟩ : syracuseStep 1229135 = 1843703) B1843703
theorem B13287847 : Blo 818347 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B6996455 : Blo 818347 6996455 := bstep (se 1 (by rfl) ⟨5247341, by rfl⟩ : syracuseStep 6996455 = 10494683) B10494683
theorem B2769659 : Blo 818347 2769659 := bstep (se 1 (by rfl) ⟨2077244, by rfl⟩ : syracuseStep 2769659 = 4154489) B4154489
theorem B2769767 : Blo 818347 2769767 := bstep (se 1 (by rfl) ⟨2077325, by rfl⟩ : syracuseStep 2769767 = 4154651) B4154651
theorem B1229927 : Blo 818347 1229927 := bstep (se 1 (by rfl) ⟨922445, by rfl⟩ : syracuseStep 1229927 = 1844891) B1844891
theorem B4670567 : Blo 818347 4670567 := bstep (se 1 (by rfl) ⟨3502925, by rfl⟩ : syracuseStep 4670567 = 7005851) B7005851
theorem B4146551 : Blo 818347 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B2803495 : Blo 818347 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B2214793 : Blo 818347 2214793 := bstep (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) B1661095
theorem B1231865 : Blo 818347 1231865 := bstep (se 2 (by rfl) ⟨461949, by rfl⟩ : syracuseStep 1231865 = 923899) B923899
theorem B76664501 : Blo 818347 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B2215679 : Blo 818347 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B1036471 : Blo 818347 1036471 := bstep (se 1 (by rfl) ⟨777353, by rfl⟩ : syracuseStep 1036471 = 1554707) B1554707
theorem B4149791 : Blo 818347 4149791 := bstep (se 1 (by rfl) ⟨3112343, by rfl⟩ : syracuseStep 4149791 = 6224687) B6224687
theorem B1168553 : Blo 818347 1168553 := bstep (se 2 (by rfl) ⟨438207, by rfl⟩ : syracuseStep 1168553 = 876415) B876415
theorem B4150763 : Blo 818347 4150763 := bstep (se 1 (by rfl) ⟨3113072, by rfl⟩ : syracuseStep 4150763 = 6226145) B6226145
theorem B4216411 : Blo 818347 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1401001 : Blo 818347 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B15788843 : Blo 818347 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B22473611 : Blo 818347 22473611 := bstep (se 1 (by rfl) ⟨16855208, by rfl⟩ : syracuseStep 22473611 = 33710417) B33710417
theorem B3993569 : Blo 818347 3993569 := bstep (se 2 (by rfl) ⟨1497588, by rfl⟩ : syracuseStep 3993569 = 2995177) B2995177
theorem B1667047 : Blo 818347 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B4683257 : Blo 818347 4683257 := bstep (se 2 (by rfl) ⟨1756221, by rfl⟩ : syracuseStep 4683257 = 3512443) B3512443
theorem B1898815 : Blo 818347 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B6224201 : Blo 818347 6224201 := bstep (se 2 (by rfl) ⟨2334075, by rfl⟩ : syracuseStep 6224201 = 4668151) B4668151
theorem B3505427 : Blo 818347 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B818719 : Blo 818347 818719 := bstep (se 1 (by rfl) ⟨614039, by rfl⟩ : syracuseStep 818719 = 1228079) B1228079
theorem B818843 : Blo 818347 818843 := bstep (se 1 (by rfl) ⟨614132, by rfl⟩ : syracuseStep 818843 = 1228265) B1228265
theorem B818895 : Blo 818347 818895 := bstep (se 1 (by rfl) ⟨614171, by rfl⟩ : syracuseStep 818895 = 1228343) B1228343
theorem B819183 : Blo 818347 819183 := bstep (se 1 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 819183 = 1228775) B1228775
theorem B1802303 : Blo 818347 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B819423 : Blo 818347 819423 := bstep (se 1 (by rfl) ⟨614567, by rfl⟩ : syracuseStep 819423 = 1229135) B1229135
theorem B7012615 : Blo 818347 7012615 := bstep (se 1 (by rfl) ⟨5259461, by rfl⟩ : syracuseStep 7012615 = 10518923) B10518923
theorem B819951 : Blo 818347 819951 := bstep (se 1 (by rfl) ⟨614963, by rfl⟩ : syracuseStep 819951 = 1229927) B1229927
theorem B3113711 : Blo 818347 3113711 := bstep (se 1 (by rfl) ⟨2335283, by rfl⟩ : syracuseStep 3113711 = 4670567) B4670567
theorem B2491327 : Blo 818347 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B821243 : Blo 818347 821243 := bstep (se 1 (by rfl) ⟨615932, by rfl⟩ : syracuseStep 821243 = 1231865) B1231865
theorem B5900519 : Blo 818347 5900519 := bstep (se 1 (by rfl) ⟨4425389, by rfl⟩ : syracuseStep 5900519 = 8850779) B8850779
theorem B3737993 : Blo 818347 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B3116141 : Blo 818347 3116141 := bstep (se 3 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 3116141 = 1168553) B1168553
theorem B920767 : Blo 818347 920767 := bstep (se 1 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 920767 = 1381151) B1381151
theorem B29888021 : Blo 818347 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B6231491 : Blo 818347 6231491 := bstep (se 1 (by rfl) ⟨4673618, by rfl⟩ : syracuseStep 6231491 = 9347237) B9347237
theorem B1381961 : Blo 818347 1381961 := bstep (se 2 (by rfl) ⟨518235, by rfl⟩ : syracuseStep 1381961 = 1036471) B1036471
theorem B923503 : Blo 818347 923503 := bstep (se 1 (by rfl) ⟨692627, by rfl⟩ : syracuseStep 923503 = 1385255) B1385255
theorem B22485215 : Blo 818347 22485215 := bstep (se 1 (by rfl) ⟨16863911, by rfl⟩ : syracuseStep 22485215 = 33727823) B33727823
theorem B10525895 : Blo 818347 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B14982407 : Blo 818347 14982407 := bstep (se 1 (by rfl) ⟨11236805, by rfl⟩ : syracuseStep 14982407 = 22473611) B22473611
theorem B1842479 : Blo 818347 1842479 := bstep (se 1 (by rfl) ⟨1381859, by rfl⟩ : syracuseStep 1842479 = 2763719) B2763719
theorem B2662379 : Blo 818347 2662379 := bstep (se 1 (by rfl) ⟨1996784, by rfl⟩ : syracuseStep 2662379 = 3993569) B3993569
theorem B1843271 : Blo 818347 1843271 := bstep (se 1 (by rfl) ⟨1382453, by rfl⟩ : syracuseStep 1843271 = 2764907) B2764907
theorem B2531753 : Blo 818347 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B1385147 : Blo 818347 1385147 := bstep (se 1 (by rfl) ⟨1038860, by rfl⟩ : syracuseStep 1385147 = 2077721) B2077721
theorem B3122171 : Blo 818347 3122171 := bstep (se 1 (by rfl) ⟨2341628, by rfl⟩ : syracuseStep 3122171 = 4683257) B4683257
theorem B1385471 : Blo 818347 1385471 := bstep (se 1 (by rfl) ⟨1039103, by rfl⟩ : syracuseStep 1385471 = 2078207) B2078207
theorem B2499623 : Blo 818347 2499623 := bstep (se 1 (by rfl) ⟨1874717, by rfl⟩ : syracuseStep 2499623 = 3749435) B3749435
theorem B1975337 : Blo 818347 1975337 := bstep (se 2 (by rfl) ⟨740751, by rfl⟩ : syracuseStep 1975337 = 1481503) B1481503
theorem B1385599 : Blo 818347 1385599 := bstep (se 1 (by rfl) ⟨1039199, by rfl⟩ : syracuseStep 1385599 = 2078399) B2078399
theorem B5908477 : Blo 818347 5908477 := bstep (se 3 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 5908477 = 2215679) B2215679
theorem B2336951 : Blo 818347 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B1386679 : Blo 818347 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B5253569 : Blo 818347 5253569 := bstep (se 2 (by rfl) ⟨1970088, by rfl⟩ : syracuseStep 5253569 = 3940177) B3940177
theorem B1387199 : Blo 818347 1387199 := bstep (se 1 (by rfl) ⟨1040399, by rfl⟩ : syracuseStep 1387199 = 2080799) B2080799
theorem B7973615 : Blo 818347 7973615 := bstep (se 1 (by rfl) ⟨5980211, by rfl⟩ : syracuseStep 7973615 = 11960423) B11960423
theorem B7023347 : Blo 818347 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B1846079 : Blo 818347 1846079 := bstep (se 1 (by rfl) ⟨1384559, by rfl⟩ : syracuseStep 1846079 = 2769119) B2769119
theorem B4664303 : Blo 818347 4664303 := bstep (se 1 (by rfl) ⟨3498227, by rfl⟩ : syracuseStep 4664303 = 6996455) B6996455
theorem B2763881 : Blo 818347 2763881 := bstep (se 2 (by rfl) ⟨1036455, by rfl⟩ : syracuseStep 2763881 = 2072911) B2072911
theorem B1846439 : Blo 818347 1846439 := bstep (se 1 (by rfl) ⟨1384829, by rfl⟩ : syracuseStep 1846439 = 2769659) B2769659
theorem B1846511 : Blo 818347 1846511 := bstep (se 1 (by rfl) ⟨1384883, by rfl⟩ : syracuseStep 1846511 = 2769767) B2769767
theorem B2764367 : Blo 818347 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B2766527 : Blo 818347 2766527 := bstep (se 1 (by rfl) ⟨2074895, by rfl⟩ : syracuseStep 2766527 = 4149791) B4149791
theorem B2767175 : Blo 818347 2767175 := bstep (se 1 (by rfl) ⟨2075381, by rfl⟩ : syracuseStep 2767175 = 4150763) B4150763
theorem B1227641 : Blo 818347 1227641 := bstep (se 2 (by rfl) ⟨460365, by rfl⟩ : syracuseStep 1227641 = 920731) B920731
theorem B1227839 : Blo 818347 1227839 := bstep (se 1 (by rfl) ⟨920879, by rfl⟩ : syracuseStep 1227839 = 1841759) B1841759
theorem B17742995 : Blo 818347 17742995 := bstep (se 1 (by rfl) ⟨13307246, by rfl⟩ : syracuseStep 17742995 = 26614493) B26614493
theorem B1227935 : Blo 818347 1227935 := bstep (se 1 (by rfl) ⟨920951, by rfl⟩ : syracuseStep 1227935 = 1841903) B1841903
theorem B9354527 : Blo 818347 9354527 := bstep (se 1 (by rfl) ⟨7015895, by rfl⟩ : syracuseStep 9354527 = 14031791) B14031791
theorem B11812229 : Blo 818347 11812229 := bstep (se 4 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 11812229 = 2214793) B2214793
theorem B1228271 : Blo 818347 1228271 := bstep (se 1 (by rfl) ⟨921203, by rfl⟩ : syracuseStep 1228271 = 1842407) B1842407
theorem B1228841 : Blo 818347 1228841 := bstep (se 2 (by rfl) ⟨460815, by rfl⟩ : syracuseStep 1228841 = 921631) B921631
theorem B34521155 : Blo 818347 34521155 := bstep (se 1 (by rfl) ⟨25890866, by rfl⟩ : syracuseStep 34521155 = 51781733) B51781733
theorem B1228907 : Blo 818347 1228907 := bstep (se 1 (by rfl) ⟨921680, by rfl⟩ : syracuseStep 1228907 = 1843361) B1843361
theorem B1228955 : Blo 818347 1228955 := bstep (se 1 (by rfl) ⟨921716, by rfl⟩ : syracuseStep 1228955 = 1843433) B1843433
theorem B1229039 : Blo 818347 1229039 := bstep (se 1 (by rfl) ⟨921779, by rfl⟩ : syracuseStep 1229039 = 1843559) B1843559
theorem B5620211 : Blo 818347 5620211 := bstep (se 1 (by rfl) ⟨4215158, by rfl⟩ : syracuseStep 5620211 = 8430317) B8430317
theorem B2081335 : Blo 818347 2081335 := bstep (se 1 (by rfl) ⟨1561001, by rfl⟩ : syracuseStep 2081335 = 3122003) B3122003
theorem B1557083 : Blo 818347 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B11846249 : Blo 818347 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B1230383 : Blo 818347 1230383 := bstep (se 1 (by rfl) ⟨922787, by rfl⟩ : syracuseStep 1230383 = 1845575) B1845575
theorem B1230827 : Blo 818347 1230827 := bstep (se 1 (by rfl) ⟨923120, by rfl⟩ : syracuseStep 1230827 = 1846241) B1846241
theorem B5621881 : Blo 818347 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B1231739 : Blo 818347 1231739 := bstep (se 1 (by rfl) ⟨923804, by rfl⟩ : syracuseStep 1231739 = 1847609) B1847609
theorem B5917817 : Blo 818347 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B10505801 : Blo 818347 10505801 := bstep (se 2 (by rfl) ⟨3939675, by rfl⟩ : syracuseStep 10505801 = 7879351) B7879351
theorem B1232543 : Blo 818347 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B1232639 : Blo 818347 1232639 := bstep (se 1 (by rfl) ⟨924479, by rfl⟩ : syracuseStep 1232639 = 1848959) B1848959
theorem B4149467 : Blo 818347 4149467 := bstep (se 1 (by rfl) ⟨3112100, by rfl⟩ : syracuseStep 4149467 = 6224201) B6224201
theorem B1233119 : Blo 818347 1233119 := bstep (se 1 (by rfl) ⟨924839, by rfl⟩ : syracuseStep 1233119 = 1849679) B1849679
theorem B6214481 : Blo 818347 6214481 := bstep (se 2 (by rfl) ⟨2330430, by rfl⟩ : syracuseStep 6214481 = 4660861) B4660861
theorem B2774735 : Blo 818347 2774735 := bstep (se 1 (by rfl) ⟨2081051, by rfl⟩ : syracuseStep 2774735 = 4162103) B4162103
theorem B17717129 : Blo 818347 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B55401083 : Blo 818347 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B4152059 : Blo 818347 4152059 := bstep (se 1 (by rfl) ⟨3114044, by rfl⟩ : syracuseStep 4152059 = 6228089) B6228089
theorem B51109667 : Blo 818347 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B2222729 : Blo 818347 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B3503695 : Blo 818347 3503695 := bstep (se 1 (by rfl) ⟨2627771, by rfl⟩ : syracuseStep 3503695 = 5255543) B5255543
theorem B3503969 : Blo 818347 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B14776465 : Blo 818347 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B5339951 : Blo 818347 5339951 := bstep (se 1 (by rfl) ⟨4004963, by rfl⟩ : syracuseStep 5339951 = 8009927) B8009927
theorem B3112951 : Blo 818347 3112951 := bstep (se 1 (by rfl) ⟨2334713, by rfl⟩ : syracuseStep 3112951 = 4669427) B4669427
theorem B818431 : Blo 818347 818431 := bstep (se 1 (by rfl) ⟨613823, by rfl⟩ : syracuseStep 818431 = 1227647) B1227647
theorem B818687 : Blo 818347 818687 := bstep (se 1 (by rfl) ⟨614015, by rfl⟩ : syracuseStep 818687 = 1228031) B1228031
theorem B819227 : Blo 818347 819227 := bstep (se 1 (by rfl) ⟨614420, by rfl⟩ : syracuseStep 819227 = 1228841) B1228841
theorem B819271 : Blo 818347 819271 := bstep (se 1 (by rfl) ⟨614453, by rfl⟩ : syracuseStep 819271 = 1228907) B1228907
theorem B819303 : Blo 818347 819303 := bstep (se 1 (by rfl) ⟨614477, by rfl⟩ : syracuseStep 819303 = 1228955) B1228955
theorem B819359 : Blo 818347 819359 := bstep (se 1 (by rfl) ⟨614519, by rfl⟩ : syracuseStep 819359 = 1229039) B1229039
theorem B7897499 : Blo 818347 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B820255 : Blo 818347 820255 := bstep (se 1 (by rfl) ⟨615191, by rfl⟩ : syracuseStep 820255 = 1230383) B1230383
theorem B820551 : Blo 818347 820551 := bstep (se 1 (by rfl) ⟨615413, by rfl⟩ : syracuseStep 820551 = 1230827) B1230827
theorem B3933679 : Blo 818347 3933679 := bstep (se 1 (by rfl) ⟨2950259, by rfl⟩ : syracuseStep 3933679 = 5900519) B5900519
theorem B821159 : Blo 818347 821159 := bstep (se 1 (by rfl) ⟨615869, by rfl⟩ : syracuseStep 821159 = 1231739) B1231739
theorem B19925347 : Blo 818347 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B821695 : Blo 818347 821695 := bstep (se 1 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 821695 = 1232543) B1232543
theorem B821759 : Blo 818347 821759 := bstep (se 1 (by rfl) ⟨616319, by rfl⟩ : syracuseStep 821759 = 1232639) B1232639
theorem B822079 : Blo 818347 822079 := bstep (se 1 (by rfl) ⟨616559, by rfl⟩ : syracuseStep 822079 = 1233119) B1233119
theorem B921307 : Blo 818347 921307 := bstep (se 1 (by rfl) ⟨690980, by rfl⟩ : syracuseStep 921307 = 1381961) B1381961
theorem B36934055 : Blo 818347 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B7017263 : Blo 818347 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B1774919 : Blo 818347 1774919 := bstep (se 1 (by rfl) ⟨1331189, by rfl⟩ : syracuseStep 1774919 = 2662379) B2662379
theorem B923431 : Blo 818347 923431 := bstep (se 1 (by rfl) ⟨692573, by rfl⟩ : syracuseStep 923431 = 1385147) B1385147
theorem B6231869 : Blo 818347 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B923647 : Blo 818347 923647 := bstep (se 1 (by rfl) ⟨692735, by rfl⟩ : syracuseStep 923647 = 1385471) B1385471
theorem B1316891 : Blo 818347 1316891 := bstep (se 1 (by rfl) ⟨987668, by rfl⟩ : syracuseStep 1316891 = 1975337) B1975337
theorem B9967981 : Blo 818347 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B1481819 : Blo 818347 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B924799 : Blo 818347 924799 := bstep (se 1 (by rfl) ⟨693599, by rfl⟩ : syracuseStep 924799 = 1387199) B1387199
theorem B5315743 : Blo 818347 5315743 := bstep (se 1 (by rfl) ⟨3986807, by rfl⟩ : syracuseStep 5315743 = 7973615) B7973615
theorem B1842587 : Blo 818347 1842587 := bstep (se 1 (by rfl) ⟨1381940, by rfl⟩ : syracuseStep 1842587 = 2763881) B2763881
theorem B1842911 : Blo 818347 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B19701953 : Blo 818347 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B1844351 : Blo 818347 1844351 := bstep (se 1 (by rfl) ⟨1383263, by rfl⟩ : syracuseStep 1844351 = 2766527) B2766527
theorem B2335979 : Blo 818347 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B1844783 : Blo 818347 1844783 := bstep (se 1 (by rfl) ⟨1383587, by rfl⟩ : syracuseStep 1844783 = 2767175) B2767175
theorem B6236351 : Blo 818347 6236351 := bstep (se 1 (by rfl) ⟨4677263, by rfl⟩ : syracuseStep 6236351 = 9354527) B9354527
theorem B7874819 : Blo 818347 7874819 := bstep (se 1 (by rfl) ⟨5906114, by rfl⟩ : syracuseStep 7874819 = 11812229) B11812229
theorem B23014103 : Blo 818347 23014103 := bstep (se 1 (by rfl) ⟨17260577, by rfl⟩ : syracuseStep 23014103 = 34521155) B34521155
theorem B3746807 : Blo 818347 3746807 := bstep (se 1 (by rfl) ⟨2810105, by rfl⟩ : syracuseStep 3746807 = 5620211) B5620211
theorem B9350153 : Blo 818347 9350153 := bstep (se 2 (by rfl) ⟨3506307, by rfl⟩ : syracuseStep 9350153 = 7012615) B7012615
theorem B2075807 : Blo 818347 2075807 := bstep (se 1 (by rfl) ⟨1556855, by rfl⟩ : syracuseStep 2075807 = 3113711) B3113711
theorem B3321769 : Blo 818347 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B1847465 : Blo 818347 1847465 := bstep (se 2 (by rfl) ⟨692799, by rfl⟩ : syracuseStep 1847465 = 1385599) B1385599
theorem B2077427 : Blo 818347 2077427 := bstep (se 1 (by rfl) ⟨1558070, by rfl⟩ : syracuseStep 2077427 = 3116141) B3116141
theorem B7877969 : Blo 818347 7877969 := bstep (se 2 (by rfl) ⟨2954238, by rfl⟩ : syracuseStep 7877969 = 5908477) B5908477
theorem B2766311 : Blo 818347 2766311 := bstep (se 1 (by rfl) ⟨2074733, by rfl⟩ : syracuseStep 2766311 = 4149467) B4149467
theorem B1848905 : Blo 818347 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B4142987 : Blo 818347 4142987 := bstep (se 1 (by rfl) ⟨3107240, by rfl⟩ : syracuseStep 4142987 = 6214481) B6214481
theorem B1849823 : Blo 818347 1849823 := bstep (se 1 (by rfl) ⟨1387367, by rfl⟩ : syracuseStep 1849823 = 2774735) B2774735
theorem B11811419 : Blo 818347 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B14990143 : Blo 818347 14990143 := bstep (se 1 (by rfl) ⟨11242607, by rfl⟩ : syracuseStep 14990143 = 22485215) B22485215
theorem B1227689 : Blo 818347 1227689 := bstep (se 2 (by rfl) ⟨460383, by rfl⟩ : syracuseStep 1227689 = 920767) B920767
theorem B2768039 : Blo 818347 2768039 := bstep (se 1 (by rfl) ⟨2076029, by rfl⟩ : syracuseStep 2768039 = 4152059) B4152059
theorem B1228319 : Blo 818347 1228319 := bstep (se 1 (by rfl) ⟨921239, by rfl⟩ : syracuseStep 1228319 = 1842479) B1842479
theorem B1228847 : Blo 818347 1228847 := bstep (se 1 (by rfl) ⟨921635, by rfl⟩ : syracuseStep 1228847 = 1843271) B1843271
theorem B1687835 : Blo 818347 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B2081447 : Blo 818347 2081447 := bstep (se 1 (by rfl) ⟨1561085, by rfl⟩ : syracuseStep 2081447 = 3122171) B3122171
theorem B1230719 : Blo 818347 1230719 := bstep (se 1 (by rfl) ⟨923039, by rfl⟩ : syracuseStep 1230719 = 1846079) B1846079
theorem B4671593 : Blo 818347 4671593 := bstep (se 2 (by rfl) ⟨1751847, by rfl⟩ : syracuseStep 4671593 = 3503695) B3503695
theorem B1230959 : Blo 818347 1230959 := bstep (se 1 (by rfl) ⟨923219, by rfl⟩ : syracuseStep 1230959 = 1846439) B1846439
theorem B1231007 : Blo 818347 1231007 := bstep (se 1 (by rfl) ⟨923255, by rfl⟩ : syracuseStep 1231007 = 1846511) B1846511
theorem B1231337 : Blo 818347 1231337 := bstep (se 2 (by rfl) ⟨461751, by rfl⟩ : syracuseStep 1231337 = 923503) B923503
theorem B15780845 : Blo 818347 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B3559967 : Blo 818347 3559967 := bstep (se 1 (by rfl) ⟨2669975, by rfl⟩ : syracuseStep 3559967 = 5339951) B5339951
theorem B4150601 : Blo 818347 4150601 := bstep (se 2 (by rfl) ⟨1556475, by rfl⟩ : syracuseStep 4150601 = 3112951) B3112951
theorem B1201535 : Blo 818347 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B2775113 : Blo 818347 2775113 := bstep (se 2 (by rfl) ⟨1040667, by rfl⟩ : syracuseStep 2775113 = 2081335) B2081335
theorem B4152221 : Blo 818347 4152221 := bstep (se 3 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 4152221 = 1557083) B1557083
theorem B7003867 : Blo 818347 7003867 := bstep (se 1 (by rfl) ⟨5252900, by rfl⟩ : syracuseStep 7003867 = 10505801) B10505801
theorem B7495841 : Blo 818347 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B4154327 : Blo 818347 4154327 := bstep (se 1 (by rfl) ⟨3115745, by rfl⟩ : syracuseStep 4154327 = 6231491) B6231491
theorem B9988271 : Blo 818347 9988271 := bstep (se 1 (by rfl) ⟨7491203, by rfl⟩ : syracuseStep 9988271 = 14982407) B14982407
theorem B34073111 : Blo 818347 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B1666415 : Blo 818347 1666415 := bstep (se 1 (by rfl) ⟨1249811, by rfl⟩ : syracuseStep 1666415 = 2499623) B2499623
theorem B3502379 : Blo 818347 3502379 := bstep (se 1 (by rfl) ⟨2626784, by rfl⟩ : syracuseStep 3502379 = 5253569) B5253569
theorem B4682231 : Blo 818347 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B3109535 : Blo 818347 3109535 := bstep (se 1 (by rfl) ⟨2332151, by rfl⟩ : syracuseStep 3109535 = 4664303) B4664303
theorem B818427 : Blo 818347 818427 := bstep (se 1 (by rfl) ⟨613820, by rfl⟩ : syracuseStep 818427 = 1227641) B1227641
theorem B818559 : Blo 818347 818559 := bstep (se 1 (by rfl) ⟨613919, by rfl⟩ : syracuseStep 818559 = 1227839) B1227839
theorem B11828663 : Blo 818347 11828663 := bstep (se 1 (by rfl) ⟨8871497, by rfl⟩ : syracuseStep 11828663 = 17742995) B17742995
theorem B818623 : Blo 818347 818623 := bstep (se 1 (by rfl) ⟨613967, by rfl⟩ : syracuseStep 818623 = 1227935) B1227935
theorem B818847 : Blo 818347 818847 := bstep (se 1 (by rfl) ⟨614135, by rfl⟩ : syracuseStep 818847 = 1228271) B1228271
theorem B819231 : Blo 818347 819231 := bstep (se 1 (by rfl) ⟨614423, by rfl⟩ : syracuseStep 819231 = 1228847) B1228847
theorem B820479 : Blo 818347 820479 := bstep (se 1 (by rfl) ⟨615359, by rfl⟩ : syracuseStep 820479 = 1230719) B1230719
theorem B3114395 : Blo 818347 3114395 := bstep (se 1 (by rfl) ⟨2335796, by rfl⟩ : syracuseStep 3114395 = 4671593) B4671593
theorem B820639 : Blo 818347 820639 := bstep (se 1 (by rfl) ⟨615479, by rfl⟩ : syracuseStep 820639 = 1230959) B1230959
theorem B820671 : Blo 818347 820671 := bstep (se 1 (by rfl) ⟨615503, by rfl⟩ : syracuseStep 820671 = 1231007) B1231007
theorem B820891 : Blo 818347 820891 := bstep (se 1 (by rfl) ⟨615668, by rfl⟩ : syracuseStep 820891 = 1231337) B1231337
theorem B5244905 : Blo 818347 5244905 := bstep (se 2 (by rfl) ⟨1966839, by rfl⟩ : syracuseStep 5244905 = 3933679) B3933679
theorem B10520563 : Blo 818347 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B12816373 : Blo 818347 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B4429025 : Blo 818347 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B6658847 : Blo 818347 6658847 := bstep (se 1 (by rfl) ⟨4994135, by rfl⟩ : syracuseStep 6658847 = 9988271) B9988271
theorem B5249879 : Blo 818347 5249879 := bstep (se 1 (by rfl) ⟨3937409, by rfl⟩ : syracuseStep 5249879 = 7874819) B7874819
theorem B22715407 : Blo 818347 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B2497871 : Blo 818347 2497871 := bstep (se 1 (by rfl) ⟨1873403, by rfl⟩ : syracuseStep 2497871 = 3746807) B3746807
theorem B6233435 : Blo 818347 6233435 := bstep (se 1 (by rfl) ⟨4675076, by rfl⟩ : syracuseStep 6233435 = 9350153) B9350153
theorem B1383871 : Blo 818347 1383871 := bstep (se 1 (by rfl) ⟨1037903, by rfl⟩ : syracuseStep 1383871 = 2075807) B2075807
theorem B2334919 : Blo 818347 2334919 := bstep (se 1 (by rfl) ⟨1751189, by rfl⟩ : syracuseStep 2334919 = 3502379) B3502379
theorem B3121487 : Blo 818347 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B2073023 : Blo 818347 2073023 := bstep (se 1 (by rfl) ⟨1554767, by rfl⟩ : syracuseStep 2073023 = 3109535) B3109535
theorem B1384951 : Blo 818347 1384951 := bstep (se 1 (by rfl) ⟨1038713, by rfl⟩ : syracuseStep 1384951 = 2077427) B2077427
theorem B5251979 : Blo 818347 5251979 := bstep (se 1 (by rfl) ⟨3938984, by rfl⟩ : syracuseStep 5251979 = 7877969) B7877969
theorem B1844207 : Blo 818347 1844207 := bstep (se 1 (by rfl) ⟨1383155, by rfl⟩ : syracuseStep 1844207 = 2766311) B2766311
theorem B2761991 : Blo 818347 2761991 := bstep (se 1 (by rfl) ⟨2071493, by rfl⟩ : syracuseStep 2761991 = 4142987) B4142987
theorem B7087657 : Blo 818347 7087657 := bstep (se 2 (by rfl) ⟨2657871, by rfl⟩ : syracuseStep 7087657 = 5315743) B5315743
theorem B7874279 : Blo 818347 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B1845359 : Blo 818347 1845359 := bstep (se 1 (by rfl) ⟨1384019, by rfl⟩ : syracuseStep 1845359 = 2768039) B2768039
theorem B1387631 : Blo 818347 1387631 := bstep (se 1 (by rfl) ⟨1040723, by rfl⟩ : syracuseStep 1387631 = 2081447) B2081447
theorem B4500893 : Blo 818347 4500893 := bstep (se 3 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 4500893 = 1687835) B1687835
theorem B24622703 : Blo 818347 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B2373311 : Blo 818347 2373311 := bstep (se 1 (by rfl) ⟨1779983, by rfl⟩ : syracuseStep 2373311 = 3559967) B3559967
theorem B4733117 : Blo 818347 4733117 := bstep (se 3 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 4733117 = 1774919) B1774919
theorem B2767067 : Blo 818347 2767067 := bstep (se 1 (by rfl) ⟨2075300, by rfl⟩ : syracuseStep 2767067 = 4150601) B4150601
theorem B1850075 : Blo 818347 1850075 := bstep (se 1 (by rfl) ⟨1387556, by rfl⟩ : syracuseStep 1850075 = 2775113) B2775113
theorem B2768147 : Blo 818347 2768147 := bstep (se 1 (by rfl) ⟨2076110, by rfl⟩ : syracuseStep 2768147 = 4152221) B4152221
theorem B1228391 : Blo 818347 1228391 := bstep (se 1 (by rfl) ⟨921293, by rfl⟩ : syracuseStep 1228391 = 1842587) B1842587
theorem B1228409 : Blo 818347 1228409 := bstep (se 2 (by rfl) ⟨460653, by rfl⟩ : syracuseStep 1228409 = 921307) B921307
theorem B1228607 : Blo 818347 1228607 := bstep (se 1 (by rfl) ⟨921455, by rfl⟩ : syracuseStep 1228607 = 1842911) B1842911
theorem B4997227 : Blo 818347 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B2769551 : Blo 818347 2769551 := bstep (se 1 (by rfl) ⟨2077163, by rfl⟩ : syracuseStep 2769551 = 4154327) B4154327
theorem B1229567 : Blo 818347 1229567 := bstep (se 1 (by rfl) ⟨922175, by rfl⟩ : syracuseStep 1229567 = 1844351) B1844351
theorem B1557319 : Blo 818347 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1229855 : Blo 818347 1229855 := bstep (se 1 (by rfl) ⟨922391, by rfl⟩ : syracuseStep 1229855 = 1844783) B1844783
theorem B1231241 : Blo 818347 1231241 := bstep (se 2 (by rfl) ⟨461715, by rfl⟩ : syracuseStep 1231241 = 923431) B923431
theorem B1231529 : Blo 818347 1231529 := bstep (se 2 (by rfl) ⟨461823, by rfl⟩ : syracuseStep 1231529 = 923647) B923647
theorem B1231643 : Blo 818347 1231643 := bstep (se 1 (by rfl) ⟨923732, by rfl⟩ : syracuseStep 1231643 = 1847465) B1847465
theorem B3951517 : Blo 818347 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B13290641 : Blo 818347 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B1232603 : Blo 818347 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B1233065 : Blo 818347 1233065 := bstep (se 2 (by rfl) ⟨462399, by rfl⟩ : syracuseStep 1233065 = 924799) B924799
theorem B1233215 : Blo 818347 1233215 := bstep (se 1 (by rfl) ⟨924911, by rfl⟩ : syracuseStep 1233215 = 1849823) B1849823
theorem B7885775 : Blo 818347 7885775 := bstep (se 1 (by rfl) ⟨5914331, by rfl⟩ : syracuseStep 7885775 = 11828663) B11828663
theorem B5264999 : Blo 818347 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B26567129 : Blo 818347 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B4678175 : Blo 818347 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B4154579 : Blo 818347 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B877927 : Blo 818347 877927 := bstep (se 1 (by rfl) ⟨658445, by rfl⟩ : syracuseStep 877927 = 1316891) B1316891
theorem B13134635 : Blo 818347 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B4157567 : Blo 818347 4157567 := bstep (se 1 (by rfl) ⟨3118175, by rfl⟩ : syracuseStep 4157567 = 6236351) B6236351
theorem B61370941 : Blo 818347 61370941 := bstep (se 3 (by rfl) ⟨11507051, by rfl⟩ : syracuseStep 61370941 = 23014103) B23014103
theorem B1110943 : Blo 818347 1110943 := bstep (se 1 (by rfl) ⟨833207, by rfl⟩ : syracuseStep 1110943 = 1666415) B1666415
theorem B19986857 : Blo 818347 19986857 := bstep (se 2 (by rfl) ⟨7495071, by rfl⟩ : syracuseStep 19986857 = 14990143) B14990143
theorem B818459 : Blo 818347 818459 := bstep (se 1 (by rfl) ⟨613844, by rfl⟩ : syracuseStep 818459 = 1227689) B1227689
theorem B9338489 : Blo 818347 9338489 := bstep (se 2 (by rfl) ⟨3501933, by rfl⟩ : syracuseStep 9338489 = 7003867) B7003867
theorem B818879 : Blo 818347 818879 := bstep (se 1 (by rfl) ⟨614159, by rfl⟩ : syracuseStep 818879 = 1228319) B1228319
theorem B3113225 : Blo 818347 3113225 := bstep (se 2 (by rfl) ⟨1167459, by rfl⟩ : syracuseStep 3113225 = 2334919) B2334919
theorem B819711 : Blo 818347 819711 := bstep (se 1 (by rfl) ⟨614783, by rfl⟩ : syracuseStep 819711 = 1229567) B1229567
theorem B819903 : Blo 818347 819903 := bstep (se 1 (by rfl) ⟨614927, by rfl⟩ : syracuseStep 819903 = 1229855) B1229855
theorem B820827 : Blo 818347 820827 := bstep (se 1 (by rfl) ⟨615620, by rfl⟩ : syracuseStep 820827 = 1231241) B1231241
theorem B821019 : Blo 818347 821019 := bstep (se 1 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 821019 = 1231529) B1231529
theorem B821095 : Blo 818347 821095 := bstep (se 1 (by rfl) ⟨615821, by rfl⟩ : syracuseStep 821095 = 1231643) B1231643
theorem B821735 : Blo 818347 821735 := bstep (se 1 (by rfl) ⟨616301, by rfl⟩ : syracuseStep 821735 = 1232603) B1232603
theorem B14027417 : Blo 818347 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B822043 : Blo 818347 822043 := bstep (se 1 (by rfl) ⟨616532, by rfl⟩ : syracuseStep 822043 = 1233065) B1233065
theorem B822143 : Blo 818347 822143 := bstep (se 1 (by rfl) ⟨616607, by rfl⟩ : syracuseStep 822143 = 1233215) B1233215
theorem B2952683 : Blo 818347 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B3509999 : Blo 818347 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B6328829 : Blo 818347 6328829 := bstep (se 3 (by rfl) ⟨1186655, by rfl⟩ : syracuseStep 6328829 = 2373311) B2373311
theorem B1382015 : Blo 818347 1382015 := bstep (se 1 (by rfl) ⟨1036511, by rfl⟩ : syracuseStep 1382015 = 2073023) B2073023
theorem B3118783 : Blo 818347 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B81827921 : Blo 818347 81827921 := bstep (se 2 (by rfl) ⟨30685470, by rfl⟩ : syracuseStep 81827921 = 61370941) B61370941
theorem B1841327 : Blo 818347 1841327 := bstep (se 1 (by rfl) ⟨1380995, by rfl⟩ : syracuseStep 1841327 = 2761991) B2761991
theorem B5249519 : Blo 818347 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B1481257 : Blo 818347 1481257 := bstep (se 2 (by rfl) ⟨555471, by rfl⟩ : syracuseStep 1481257 = 1110943) B1110943
theorem B8756423 : Blo 818347 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B925087 : Blo 818347 925087 := bstep (se 1 (by rfl) ⟨693815, by rfl⟩ : syracuseStep 925087 = 1387631) B1387631
theorem B30287209 : Blo 818347 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B3155411 : Blo 818347 3155411 := bstep (se 1 (by rfl) ⟨2366558, by rfl⟩ : syracuseStep 3155411 = 4733117) B4733117
theorem B1844711 : Blo 818347 1844711 := bstep (se 1 (by rfl) ⟨1383533, by rfl⟩ : syracuseStep 1844711 = 2767067) B2767067
theorem B1845161 : Blo 818347 1845161 := bstep (se 2 (by rfl) ⟨691935, by rfl⟩ : syracuseStep 1845161 = 1383871) B1383871
theorem B1845431 : Blo 818347 1845431 := bstep (se 1 (by rfl) ⟨1384073, by rfl⟩ : syracuseStep 1845431 = 2768147) B2768147
theorem B6662969 : Blo 818347 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B1846367 : Blo 818347 1846367 := bstep (se 1 (by rfl) ⟨1384775, by rfl⟩ : syracuseStep 1846367 = 2769551) B2769551
theorem B1846601 : Blo 818347 1846601 := bstep (se 2 (by rfl) ⟨692475, by rfl⟩ : syracuseStep 1846601 = 1384951) B1384951
theorem B2076263 : Blo 818347 2076263 := bstep (se 1 (by rfl) ⟨1557197, by rfl⟩ : syracuseStep 2076263 = 3114395) B3114395
theorem B2076425 : Blo 818347 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B9450209 : Blo 818347 9450209 := bstep (se 2 (by rfl) ⟨3543828, by rfl⟩ : syracuseStep 9450209 = 7087657) B7087657
theorem B8860427 : Blo 818347 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B5257183 : Blo 818347 5257183 := bstep (se 1 (by rfl) ⟨3942887, by rfl⟩ : syracuseStep 5257183 = 7885775) B7885775
theorem B4439231 : Blo 818347 4439231 := bstep (se 1 (by rfl) ⟨3329423, by rfl⟩ : syracuseStep 4439231 = 6658847) B6658847
theorem B17088497 : Blo 818347 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B2080991 : Blo 818347 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B17711419 : Blo 818347 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B1229471 : Blo 818347 1229471 := bstep (se 1 (by rfl) ⟨922103, by rfl⟩ : syracuseStep 1229471 = 1844207) B1844207
theorem B2769719 : Blo 818347 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B1230239 : Blo 818347 1230239 := bstep (se 1 (by rfl) ⟨922679, by rfl⟩ : syracuseStep 1230239 = 1845359) B1845359
theorem B3000595 : Blo 818347 3000595 := bstep (se 1 (by rfl) ⟨2250446, by rfl⟩ : syracuseStep 3000595 = 4500893) B4500893
theorem B2771711 : Blo 818347 2771711 := bstep (se 1 (by rfl) ⟨2078783, by rfl⟩ : syracuseStep 2771711 = 4157567) B4157567
theorem B13324571 : Blo 818347 13324571 := bstep (se 1 (by rfl) ⟨9993428, by rfl⟩ : syracuseStep 13324571 = 19986857) B19986857
theorem B1233383 : Blo 818347 1233383 := bstep (se 1 (by rfl) ⟨925037, by rfl⟩ : syracuseStep 1233383 = 1850075) B1850075
theorem B3496603 : Blo 818347 3496603 := bstep (se 1 (by rfl) ⟨2622452, by rfl⟩ : syracuseStep 3496603 = 5244905) B5244905
theorem B1170569 : Blo 818347 1170569 := bstep (se 2 (by rfl) ⟨438963, by rfl⟩ : syracuseStep 1170569 = 877927) B877927
theorem B5268689 : Blo 818347 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B3499919 : Blo 818347 3499919 := bstep (se 1 (by rfl) ⟨2624939, by rfl⟩ : syracuseStep 3499919 = 5249879) B5249879
theorem B1665247 : Blo 818347 1665247 := bstep (se 1 (by rfl) ⟨1248935, by rfl⟩ : syracuseStep 1665247 = 2497871) B2497871
theorem B4155623 : Blo 818347 4155623 := bstep (se 1 (by rfl) ⟨3116717, by rfl⟩ : syracuseStep 4155623 = 6233435) B6233435
theorem B3501319 : Blo 818347 3501319 := bstep (se 1 (by rfl) ⟨2625989, by rfl⟩ : syracuseStep 3501319 = 5251979) B5251979
theorem B16415135 : Blo 818347 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B818927 : Blo 818347 818927 := bstep (se 1 (by rfl) ⟨614195, by rfl⟩ : syracuseStep 818927 = 1228391) B1228391
theorem B818939 : Blo 818347 818939 := bstep (se 1 (by rfl) ⟨614204, by rfl⟩ : syracuseStep 818939 = 1228409) B1228409
theorem B6225659 : Blo 818347 6225659 := bstep (se 1 (by rfl) ⟨4669244, by rfl⟩ : syracuseStep 6225659 = 9338489) B9338489
theorem B819071 : Blo 818347 819071 := bstep (se 1 (by rfl) ⟨614303, by rfl⟩ : syracuseStep 819071 = 1228607) B1228607
theorem B819647 : Blo 818347 819647 := bstep (se 1 (by rfl) ⟨614735, by rfl⟩ : syracuseStep 819647 = 1229471) B1229471
theorem B820159 : Blo 818347 820159 := bstep (se 1 (by rfl) ⟨615119, by rfl⟩ : syracuseStep 820159 = 1230239) B1230239
theorem B1968455 : Blo 818347 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B8883047 : Blo 818347 8883047 := bstep (se 1 (by rfl) ⟨6662285, by rfl⟩ : syracuseStep 8883047 = 13324571) B13324571
theorem B7900037 : Blo 818347 7900037 := bstep (se 4 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 7900037 = 1481257) B1481257
theorem B822255 : Blo 818347 822255 := bstep (se 1 (by rfl) ⟨616691, by rfl⟩ : syracuseStep 822255 = 1233383) B1233383
theorem B921343 : Blo 818347 921343 := bstep (se 1 (by rfl) ⟨691007, by rfl⟩ : syracuseStep 921343 = 1382015) B1382015
theorem B5837615 : Blo 818347 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B218207789 : Blo 818347 218207789 := bstep (se 3 (by rfl) ⟨40913960, by rfl⟩ : syracuseStep 218207789 = 81827921) B81827921
theorem B3512459 : Blo 818347 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B2103607 : Blo 818347 2103607 := bstep (se 1 (by rfl) ⟨1577705, by rfl⟩ : syracuseStep 2103607 = 3155411) B3155411
theorem B2333279 : Blo 818347 2333279 := bstep (se 1 (by rfl) ⟨1749959, by rfl⟩ : syracuseStep 2333279 = 3499919) B3499919
theorem B1384175 : Blo 818347 1384175 := bstep (se 1 (by rfl) ⟨1038131, by rfl⟩ : syracuseStep 1384175 = 2076263) B2076263
theorem B1384283 : Blo 818347 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B3121517 : Blo 818347 3121517 := bstep (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) B1170569
theorem B6300139 : Blo 818347 6300139 := bstep (se 1 (by rfl) ⟨4725104, by rfl⟩ : syracuseStep 6300139 = 9450209) B9450209
theorem B5906951 : Blo 818347 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B4662137 : Blo 818347 4662137 := bstep (se 2 (by rfl) ⟨1748301, by rfl⟩ : syracuseStep 4662137 = 3496603) B3496603
theorem B2959487 : Blo 818347 2959487 := bstep (se 1 (by rfl) ⟨2219615, by rfl⟩ : syracuseStep 2959487 = 4439231) B4439231
theorem B1387327 : Blo 818347 1387327 := bstep (se 1 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 1387327 = 2080991) B2080991
theorem B2075483 : Blo 818347 2075483 := bstep (se 1 (by rfl) ⟨1556612, by rfl⟩ : syracuseStep 2075483 = 3113225) B3113225
theorem B9351611 : Blo 818347 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B40382945 : Blo 818347 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1847807 : Blo 818347 1847807 := bstep (se 1 (by rfl) ⟨1385855, by rfl⟩ : syracuseStep 1847807 = 2771711) B2771711
theorem B7385917 : Blo 818347 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B2339999 : Blo 818347 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B1227551 : Blo 818347 1227551 := bstep (se 1 (by rfl) ⟨920663, by rfl⟩ : syracuseStep 1227551 = 1841327) B1841327
theorem B4668425 : Blo 818347 4668425 := bstep (se 2 (by rfl) ⟨1750659, by rfl⟩ : syracuseStep 4668425 = 3501319) B3501319
theorem B64012693 : Blo 818347 64012693 := bstep (se 6 (by rfl) ⟨1500297, by rfl⟩ : syracuseStep 64012693 = 3000595) B3000595
theorem B1229807 : Blo 818347 1229807 := bstep (se 1 (by rfl) ⟨922355, by rfl⟩ : syracuseStep 1229807 = 1844711) B1844711
theorem B1230107 : Blo 818347 1230107 := bstep (se 1 (by rfl) ⟨922580, by rfl⟩ : syracuseStep 1230107 = 1845161) B1845161
theorem B1230287 : Blo 818347 1230287 := bstep (se 1 (by rfl) ⟨922715, by rfl⟩ : syracuseStep 1230287 = 1845431) B1845431
theorem B2770415 : Blo 818347 2770415 := bstep (se 1 (by rfl) ⟨2077811, by rfl⟩ : syracuseStep 2770415 = 4155623) B4155623
theorem B4441979 : Blo 818347 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1230911 : Blo 818347 1230911 := bstep (se 1 (by rfl) ⟨923183, by rfl⟩ : syracuseStep 1230911 = 1846367) B1846367
theorem B1231067 : Blo 818347 1231067 := bstep (se 1 (by rfl) ⟨923300, by rfl⟩ : syracuseStep 1231067 = 1846601) B1846601
theorem B1233449 : Blo 818347 1233449 := bstep (se 2 (by rfl) ⟨462543, by rfl⟩ : syracuseStep 1233449 = 925087) B925087
theorem B4150439 : Blo 818347 4150439 := bstep (se 1 (by rfl) ⟨3112829, by rfl⟩ : syracuseStep 4150439 = 6225659) B6225659
theorem B11392331 : Blo 818347 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B23615225 : Blo 818347 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B2220329 : Blo 818347 2220329 := bstep (se 2 (by rfl) ⟨832623, by rfl⟩ : syracuseStep 2220329 = 1665247) B1665247
theorem B4219219 : Blo 818347 4219219 := bstep (se 1 (by rfl) ⟨3164414, by rfl⟩ : syracuseStep 4219219 = 6328829) B6328829
theorem B3499679 : Blo 818347 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B4158377 : Blo 818347 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B7009577 : Blo 818347 7009577 := bstep (se 2 (by rfl) ⟨2628591, by rfl⟩ : syracuseStep 7009577 = 5257183) B5257183
theorem B10943423 : Blo 818347 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B819871 : Blo 818347 819871 := bstep (se 1 (by rfl) ⟨614903, by rfl⟩ : syracuseStep 819871 = 1229807) B1229807
theorem B820071 : Blo 818347 820071 := bstep (se 1 (by rfl) ⟨615053, by rfl⟩ : syracuseStep 820071 = 1230107) B1230107
theorem B820191 : Blo 818347 820191 := bstep (se 1 (by rfl) ⟨615143, by rfl⟩ : syracuseStep 820191 = 1230287) B1230287
theorem B820607 : Blo 818347 820607 := bstep (se 1 (by rfl) ⟨615455, by rfl⟩ : syracuseStep 820607 = 1230911) B1230911
theorem B820711 : Blo 818347 820711 := bstep (se 1 (by rfl) ⟨615533, by rfl⟩ : syracuseStep 820711 = 1231067) B1231067
theorem B1312303 : Blo 818347 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B822299 : Blo 818347 822299 := bstep (se 1 (by rfl) ⟨616724, by rfl⟩ : syracuseStep 822299 = 1233449) B1233449
theorem B30379549 : Blo 818347 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B922783 : Blo 818347 922783 := bstep (se 1 (by rfl) ⟨692087, by rfl⟩ : syracuseStep 922783 = 1384175) B1384175
theorem B922855 : Blo 818347 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B3937967 : Blo 818347 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B2333119 : Blo 818347 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B1972991 : Blo 818347 1972991 := bstep (se 1 (by rfl) ⟨1479743, by rfl⟩ : syracuseStep 1972991 = 2959487) B2959487
theorem B1383655 : Blo 818347 1383655 := bstep (se 1 (by rfl) ⟨1037741, by rfl⟩ : syracuseStep 1383655 = 2075483) B2075483
theorem B6234407 : Blo 818347 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B8400185 : Blo 818347 8400185 := bstep (se 2 (by rfl) ⟨3150069, by rfl⟩ : syracuseStep 8400185 = 6300139) B6300139
theorem B1846943 : Blo 818347 1846943 := bstep (se 1 (by rfl) ⟨1385207, by rfl⟩ : syracuseStep 1846943 = 2770415) B2770415
theorem B2961319 : Blo 818347 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B2766959 : Blo 818347 2766959 := bstep (se 1 (by rfl) ⟨2075219, by rfl⟩ : syracuseStep 2766959 = 4150439) B4150439
theorem B145471859 : Blo 818347 145471859 := bstep (se 1 (by rfl) ⟨109103894, by rfl⟩ : syracuseStep 145471859 = 218207789) B218207789
theorem B1849769 : Blo 818347 1849769 := bstep (se 2 (by rfl) ⟨693663, by rfl⟩ : syracuseStep 1849769 = 1387327) B1387327
theorem B15743483 : Blo 818347 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B2341639 : Blo 818347 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B1555519 : Blo 818347 1555519 := bstep (se 1 (by rfl) ⟨1166639, by rfl⟩ : syracuseStep 1555519 = 2333279) B2333279
theorem B1228457 : Blo 818347 1228457 := bstep (se 2 (by rfl) ⟨460671, by rfl⟩ : syracuseStep 1228457 = 921343) B921343
theorem B2081011 : Blo 818347 2081011 := bstep (se 1 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 2081011 = 3121517) B3121517
theorem B9847889 : Blo 818347 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B26921963 : Blo 818347 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B1231871 : Blo 818347 1231871 := bstep (se 1 (by rfl) ⟨923903, by rfl⟩ : syracuseStep 1231871 = 1847807) B1847807
theorem B2804809 : Blo 818347 2804809 := bstep (se 2 (by rfl) ⟨1051803, by rfl⟩ : syracuseStep 2804809 = 2103607) B2103607
theorem B2772251 : Blo 818347 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B1559999 : Blo 818347 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B4673051 : Blo 818347 4673051 := bstep (se 1 (by rfl) ⟨3504788, by rfl⟩ : syracuseStep 4673051 = 7009577) B7009577
theorem B7295615 : Blo 818347 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B5625625 : Blo 818347 5625625 := bstep (se 2 (by rfl) ⟨2109609, by rfl⟩ : syracuseStep 5625625 = 4219219) B4219219
theorem B85350257 : Blo 818347 85350257 := bstep (se 2 (by rfl) ⟨32006346, by rfl⟩ : syracuseStep 85350257 = 64012693) B64012693
theorem B5920877 : Blo 818347 5920877 := bstep (se 3 (by rfl) ⟨1110164, by rfl⟩ : syracuseStep 5920877 = 2220329) B2220329
theorem B5922031 : Blo 818347 5922031 := bstep (se 1 (by rfl) ⟨4441523, by rfl⟩ : syracuseStep 5922031 = 8883047) B8883047
theorem B5266691 : Blo 818347 5266691 := bstep (se 1 (by rfl) ⟨3950018, by rfl⟩ : syracuseStep 5266691 = 7900037) B7900037
theorem B3891743 : Blo 818347 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B3108091 : Blo 818347 3108091 := bstep (se 1 (by rfl) ⟨2331068, by rfl⟩ : syracuseStep 3108091 = 4662137) B4662137
theorem B818367 : Blo 818347 818367 := bstep (se 1 (by rfl) ⟨613775, by rfl⟩ : syracuseStep 818367 = 1227551) B1227551
theorem B3112283 : Blo 818347 3112283 := bstep (se 1 (by rfl) ⟨2334212, by rfl⟩ : syracuseStep 3112283 = 4668425) B4668425
theorem B821247 : Blo 818347 821247 := bstep (se 1 (by rfl) ⟨615935, by rfl⟩ : syracuseStep 821247 = 1231871) B1231871
theorem B3115367 : Blo 818347 3115367 := bstep (se 1 (by rfl) ⟨2336525, by rfl⟩ : syracuseStep 3115367 = 4673051) B4673051
theorem B2625311 : Blo 818347 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B3739745 : Blo 818347 3739745 := bstep (se 2 (by rfl) ⟨1402404, by rfl⟩ : syracuseStep 3739745 = 2804809) B2804809
theorem B1315327 : Blo 818347 1315327 := bstep (se 1 (by rfl) ⟨986495, by rfl⟩ : syracuseStep 1315327 = 1972991) B1972991
theorem B40506065 : Blo 818347 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B3511127 : Blo 818347 3511127 := bstep (se 1 (by rfl) ⟨2633345, by rfl⟩ : syracuseStep 3511127 = 5266691) B5266691
theorem B2594495 : Blo 818347 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B3122185 : Blo 818347 3122185 := bstep (se 2 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 3122185 = 2341639) B2341639
theorem B1844639 : Blo 818347 1844639 := bstep (se 1 (by rfl) ⟨1383479, by rfl⟩ : syracuseStep 1844639 = 2766959) B2766959
theorem B2074025 : Blo 818347 2074025 := bstep (se 2 (by rfl) ⟨777759, by rfl⟩ : syracuseStep 2074025 = 1555519) B1555519
theorem B1844873 : Blo 818347 1844873 := bstep (se 2 (by rfl) ⟨691827, by rfl⟩ : syracuseStep 1844873 = 1383655) B1383655
theorem B10495655 : Blo 818347 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B2074855 : Blo 818347 2074855 := bstep (se 1 (by rfl) ⟨1556141, by rfl⟩ : syracuseStep 2074855 = 3112283) B3112283
theorem B6565259 : Blo 818347 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B1749737 : Blo 818347 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B1848167 : Blo 818347 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B4863743 : Blo 818347 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B56900171 : Blo 818347 56900171 := bstep (se 1 (by rfl) ⟨42675128, by rfl⟩ : syracuseStep 56900171 = 85350257) B85350257
theorem B3947251 : Blo 818347 3947251 := bstep (se 1 (by rfl) ⟨2960438, by rfl⟩ : syracuseStep 3947251 = 5920877) B5920877
theorem B4144121 : Blo 818347 4144121 := bstep (se 2 (by rfl) ⟨1554045, by rfl⟩ : syracuseStep 4144121 = 3108091) B3108091
theorem B3948425 : Blo 818347 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B1230377 : Blo 818347 1230377 := bstep (se 2 (by rfl) ⟨461391, by rfl⟩ : syracuseStep 1230377 = 922783) B922783
theorem B1230473 : Blo 818347 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B1231295 : Blo 818347 1231295 := bstep (se 1 (by rfl) ⟨923471, by rfl⟩ : syracuseStep 1231295 = 1846943) B1846943
theorem B96981239 : Blo 818347 96981239 := bstep (se 1 (by rfl) ⟨72735929, by rfl⟩ : syracuseStep 96981239 = 145471859) B145471859
theorem B1233179 : Blo 818347 1233179 := bstep (se 1 (by rfl) ⟨924884, by rfl⟩ : syracuseStep 1233179 = 1849769) B1849769
theorem B2774681 : Blo 818347 2774681 := bstep (se 2 (by rfl) ⟨1040505, by rfl⟩ : syracuseStep 2774681 = 2081011) B2081011
theorem B17947975 : Blo 818347 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B4156271 : Blo 818347 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B5600123 : Blo 818347 5600123 := bstep (se 1 (by rfl) ⟨4200092, by rfl⟩ : syracuseStep 5600123 = 8400185) B8400185
theorem B7500833 : Blo 818347 7500833 := bstep (se 2 (by rfl) ⟨2812812, by rfl⟩ : syracuseStep 7500833 = 5625625) B5625625
theorem B3110825 : Blo 818347 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B4159997 : Blo 818347 4159997 := bstep (se 3 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 4159997 = 1559999) B1559999
theorem B7896041 : Blo 818347 7896041 := bstep (se 2 (by rfl) ⟨2961015, by rfl⟩ : syracuseStep 7896041 = 5922031) B5922031
theorem B818971 : Blo 818347 818971 := bstep (se 1 (by rfl) ⟨614228, by rfl⟩ : syracuseStep 818971 = 1228457) B1228457
theorem B820251 : Blo 818347 820251 := bstep (se 1 (by rfl) ⟨615188, by rfl⟩ : syracuseStep 820251 = 1230377) B1230377
theorem B820315 : Blo 818347 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B4162913 : Blo 818347 4162913 := bstep (se 2 (by rfl) ⟨1561092, by rfl⟩ : syracuseStep 4162913 = 3122185) B3122185
theorem B820863 : Blo 818347 820863 := bstep (se 1 (by rfl) ⟨615647, by rfl⟩ : syracuseStep 820863 = 1231295) B1231295
theorem B2493163 : Blo 818347 2493163 := bstep (se 1 (by rfl) ⟨1869872, by rfl⟩ : syracuseStep 2493163 = 3739745) B3739745
theorem B64654159 : Blo 818347 64654159 := bstep (se 1 (by rfl) ⟨48490619, by rfl⟩ : syracuseStep 64654159 = 96981239) B96981239
theorem B822119 : Blo 818347 822119 := bstep (se 1 (by rfl) ⟨616589, by rfl⟩ : syracuseStep 822119 = 1233179) B1233179
theorem B27004043 : Blo 818347 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B1382683 : Blo 818347 1382683 := bstep (se 1 (by rfl) ⟨1037012, by rfl⟩ : syracuseStep 1382683 = 2074025) B2074025
theorem B17507357 : Blo 818347 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B2073883 : Blo 818347 2073883 := bstep (se 1 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 2073883 = 3110825) B3110825
theorem B23930633 : Blo 818347 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B2762747 : Blo 818347 2762747 := bstep (se 1 (by rfl) ⟨2072060, by rfl⟩ : syracuseStep 2762747 = 4144121) B4144121
theorem B2632283 : Blo 818347 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B2076911 : Blo 818347 2076911 := bstep (se 1 (by rfl) ⟨1557683, by rfl⟩ : syracuseStep 2076911 = 3115367) B3115367
theorem B2766473 : Blo 818347 2766473 := bstep (se 2 (by rfl) ⟨1037427, by rfl⟩ : syracuseStep 2766473 = 2074855) B2074855
theorem B2340751 : Blo 818347 2340751 := bstep (se 1 (by rfl) ⟨1755563, by rfl⟩ : syracuseStep 2340751 = 3511127) B3511127
theorem B1849787 : Blo 818347 1849787 := bstep (se 1 (by rfl) ⟨1387340, by rfl⟩ : syracuseStep 1849787 = 2774681) B2774681
theorem B1753769 : Blo 818347 1753769 := bstep (se 2 (by rfl) ⟨657663, by rfl⟩ : syracuseStep 1753769 = 1315327) B1315327
theorem B1229759 : Blo 818347 1229759 := bstep (se 1 (by rfl) ⟨922319, by rfl⟩ : syracuseStep 1229759 = 1844639) B1844639
theorem B1229915 : Blo 818347 1229915 := bstep (se 1 (by rfl) ⟨922436, by rfl⟩ : syracuseStep 1229915 = 1844873) B1844873
theorem B6997103 : Blo 818347 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B2770847 : Blo 818347 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B1166491 : Blo 818347 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B1232111 : Blo 818347 1232111 := bstep (se 1 (by rfl) ⟨924083, by rfl⟩ : syracuseStep 1232111 = 1848167) B1848167
theorem B5000555 : Blo 818347 5000555 := bstep (se 1 (by rfl) ⟨3750416, by rfl⟩ : syracuseStep 5000555 = 7500833) B7500833
theorem B5263001 : Blo 818347 5263001 := bstep (se 2 (by rfl) ⟨1973625, by rfl⟩ : syracuseStep 5263001 = 3947251) B3947251
theorem B2773331 : Blo 818347 2773331 := bstep (se 1 (by rfl) ⟨2079998, by rfl⟩ : syracuseStep 2773331 = 4159997) B4159997
theorem B37933447 : Blo 818347 37933447 := bstep (se 1 (by rfl) ⟨28450085, by rfl⟩ : syracuseStep 37933447 = 56900171) B56900171
theorem B5264027 : Blo 818347 5264027 := bstep (se 1 (by rfl) ⟨3948020, by rfl⟩ : syracuseStep 5264027 = 7896041) B7896041
theorem B7000829 : Blo 818347 7000829 := bstep (se 3 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 7000829 = 2625311) B2625311
theorem B1729663 : Blo 818347 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B3733415 : Blo 818347 3733415 := bstep (se 1 (by rfl) ⟨2800061, by rfl⟩ : syracuseStep 3733415 = 5600123) B5600123
theorem B3242495 : Blo 818347 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B819839 : Blo 818347 819839 := bstep (se 1 (by rfl) ⟨614879, by rfl⟩ : syracuseStep 819839 = 1229759) B1229759
theorem B819943 : Blo 818347 819943 := bstep (se 1 (by rfl) ⟨614957, by rfl⟩ : syracuseStep 819943 = 1229915) B1229915
theorem B821407 : Blo 818347 821407 := bstep (se 1 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 821407 = 1232111) B1232111
theorem B3508667 : Blo 818347 3508667 := bstep (se 1 (by rfl) ⟨2631500, by rfl⟩ : syracuseStep 3508667 = 5263001) B5263001
theorem B3509351 : Blo 818347 3509351 := bstep (se 1 (by rfl) ⟨2632013, by rfl⟩ : syracuseStep 3509351 = 5264027) B5264027
theorem B11671571 : Blo 818347 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B1841831 : Blo 818347 1841831 := bstep (se 1 (by rfl) ⟨1381373, by rfl⟩ : syracuseStep 1841831 = 2762747) B2762747
theorem B3121001 : Blo 818347 3121001 := bstep (se 2 (by rfl) ⟨1170375, by rfl⟩ : syracuseStep 3121001 = 2340751) B2340751
theorem B1384607 : Blo 818347 1384607 := bstep (se 1 (by rfl) ⟨1038455, by rfl⟩ : syracuseStep 1384607 = 2076911) B2076911
theorem B1843577 : Blo 818347 1843577 := bstep (se 2 (by rfl) ⟨691341, by rfl⟩ : syracuseStep 1843577 = 1382683) B1382683
theorem B1844315 : Blo 818347 1844315 := bstep (se 1 (by rfl) ⟨1383236, by rfl⟩ : syracuseStep 1844315 = 2766473) B2766473
theorem B4664735 : Blo 818347 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B1847231 : Blo 818347 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B2765177 : Blo 818347 2765177 := bstep (se 2 (by rfl) ⟨1036941, by rfl⟩ : syracuseStep 2765177 = 2073883) B2073883
theorem B1848887 : Blo 818347 1848887 := bstep (se 1 (by rfl) ⟨1386665, by rfl⟩ : syracuseStep 1848887 = 2773331) B2773331
theorem B4667219 : Blo 818347 4667219 := bstep (se 1 (by rfl) ⟨3500414, by rfl⟩ : syracuseStep 4667219 = 7000829) B7000829
theorem B50577929 : Blo 818347 50577929 := bstep (se 2 (by rfl) ⟨18966723, by rfl⟩ : syracuseStep 50577929 = 37933447) B37933447
theorem B9224869 : Blo 818347 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B1754855 : Blo 818347 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B72010781 : Blo 818347 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B1233191 : Blo 818347 1233191 := bstep (se 1 (by rfl) ⟨924893, by rfl⟩ : syracuseStep 1233191 = 1849787) B1849787
theorem B2775275 : Blo 818347 2775275 := bstep (se 1 (by rfl) ⟨2081456, by rfl⟩ : syracuseStep 2775275 = 4162913) B4162913
theorem B4676717 : Blo 818347 4676717 := bstep (se 3 (by rfl) ⟨876884, by rfl⟩ : syracuseStep 4676717 = 1753769) B1753769
theorem B86205545 : Blo 818347 86205545 := bstep (se 2 (by rfl) ⟨32327079, by rfl⟩ : syracuseStep 86205545 = 64654159) B64654159
theorem B13296869 : Blo 818347 13296869 := bstep (se 4 (by rfl) ⟨1246581, by rfl⟩ : syracuseStep 13296869 = 2493163) B2493163
theorem B6221285 : Blo 818347 6221285 := bstep (se 4 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 6221285 = 1166491) B1166491
theorem B15953755 : Blo 818347 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B8646653 : Blo 818347 8646653 := bstep (se 3 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 8646653 = 3242495) B3242495
theorem B13334813 : Blo 818347 13334813 := bstep (se 3 (by rfl) ⟨2500277, by rfl⟩ : syracuseStep 13334813 = 5000555) B5000555
theorem B2488943 : Blo 818347 2488943 := bstep (se 1 (by rfl) ⟨1866707, by rfl⟩ : syracuseStep 2488943 = 3733415) B3733415
theorem B33718619 : Blo 818347 33718619 := bstep (se 1 (by rfl) ⟨25288964, by rfl⟩ : syracuseStep 33718619 = 50577929) B50577929
theorem B48007187 : Blo 818347 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B822127 : Blo 818347 822127 := bstep (se 1 (by rfl) ⟨616595, by rfl⟩ : syracuseStep 822127 = 1233191) B1233191
theorem B3117811 : Blo 818347 3117811 := bstep (se 1 (by rfl) ⟨2338358, by rfl⟩ : syracuseStep 3117811 = 4676717) B4676717
theorem B21271673 : Blo 818347 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B923071 : Blo 818347 923071 := bstep (se 1 (by rfl) ⟨692303, by rfl⟩ : syracuseStep 923071 = 1384607) B1384607
theorem B1843451 : Blo 818347 1843451 := bstep (se 1 (by rfl) ⟨1382588, by rfl⟩ : syracuseStep 1843451 = 2765177) B2765177
theorem B8889875 : Blo 818347 8889875 := bstep (se 1 (by rfl) ⟨6667406, by rfl⟩ : syracuseStep 8889875 = 13334813) B13334813
theorem B12299825 : Blo 818347 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B2339111 : Blo 818347 2339111 := bstep (se 1 (by rfl) ⟨1754333, by rfl⟩ : syracuseStep 2339111 = 3508667) B3508667
theorem B2339567 : Blo 818347 2339567 := bstep (se 1 (by rfl) ⟨1754675, by rfl⟩ : syracuseStep 2339567 = 3509351) B3509351
theorem B1850183 : Blo 818347 1850183 := bstep (se 1 (by rfl) ⟨1387637, by rfl⟩ : syracuseStep 1850183 = 2775275) B2775275
theorem B1227887 : Blo 818347 1227887 := bstep (se 1 (by rfl) ⟨920915, by rfl⟩ : syracuseStep 1227887 = 1841831) B1841831
theorem B2080667 : Blo 818347 2080667 := bstep (se 1 (by rfl) ⟨1560500, by rfl⟩ : syracuseStep 2080667 = 3121001) B3121001
theorem B1229051 : Blo 818347 1229051 := bstep (se 1 (by rfl) ⟨921788, by rfl⟩ : syracuseStep 1229051 = 1843577) B1843577
theorem B1229543 : Blo 818347 1229543 := bstep (se 1 (by rfl) ⟨922157, by rfl⟩ : syracuseStep 1229543 = 1844315) B1844315
theorem B8864579 : Blo 818347 8864579 := bstep (se 1 (by rfl) ⟨6648434, by rfl⟩ : syracuseStep 8864579 = 13296869) B13296869
theorem B4147523 : Blo 818347 4147523 := bstep (se 1 (by rfl) ⟨3110642, by rfl⟩ : syracuseStep 4147523 = 6221285) B6221285
theorem B1231487 : Blo 818347 1231487 := bstep (se 1 (by rfl) ⟨923615, by rfl⟩ : syracuseStep 1231487 = 1847231) B1847231
theorem B1232591 : Blo 818347 1232591 := bstep (se 1 (by rfl) ⟨924443, by rfl⟩ : syracuseStep 1232591 = 1848887) B1848887
theorem B1659295 : Blo 818347 1659295 := bstep (se 1 (by rfl) ⟨1244471, by rfl⟩ : syracuseStep 1659295 = 2488943) B2488943
theorem B23057741 : Blo 818347 23057741 := bstep (se 3 (by rfl) ⟨4323326, by rfl⟩ : syracuseStep 23057741 = 8646653) B8646653
theorem B1169903 : Blo 818347 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B31124189 : Blo 818347 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B57470363 : Blo 818347 57470363 := bstep (se 1 (by rfl) ⟨43102772, by rfl⟩ : syracuseStep 57470363 = 86205545) B86205545
theorem B3109823 : Blo 818347 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B3111479 : Blo 818347 3111479 := bstep (se 1 (by rfl) ⟨2333609, by rfl⟩ : syracuseStep 3111479 = 4667219) B4667219
theorem B819367 : Blo 818347 819367 := bstep (se 1 (by rfl) ⟨614525, by rfl⟩ : syracuseStep 819367 = 1229051) B1229051
theorem B22479079 : Blo 818347 22479079 := bstep (se 1 (by rfl) ⟨16859309, by rfl⟩ : syracuseStep 22479079 = 33718619) B33718619
theorem B819695 : Blo 818347 819695 := bstep (se 1 (by rfl) ⟨614771, by rfl⟩ : syracuseStep 819695 = 1229543) B1229543
theorem B820991 : Blo 818347 820991 := bstep (se 1 (by rfl) ⟨615743, by rfl⟩ : syracuseStep 820991 = 1231487) B1231487
theorem B8849573 : Blo 818347 8849573 := bstep (se 4 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 8849573 = 1659295) B1659295
theorem B821727 : Blo 818347 821727 := bstep (se 1 (by rfl) ⟨616295, by rfl⟩ : syracuseStep 821727 = 1232591) B1232591
theorem B56724461 : Blo 818347 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B3119741 : Blo 818347 3119741 := bstep (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) B1169903
theorem B20749459 : Blo 818347 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B38313575 : Blo 818347 38313575 := bstep (se 1 (by rfl) ⟨28735181, by rfl⟩ : syracuseStep 38313575 = 57470363) B57470363
theorem B8199883 : Blo 818347 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B2073215 : Blo 818347 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B2074319 : Blo 818347 2074319 := bstep (se 1 (by rfl) ⟨1555739, by rfl⟩ : syracuseStep 2074319 = 3111479) B3111479
theorem B1387111 : Blo 818347 1387111 := bstep (se 1 (by rfl) ⟨1040333, by rfl⟩ : syracuseStep 1387111 = 2080667) B2080667
theorem B5909719 : Blo 818347 5909719 := bstep (se 1 (by rfl) ⟨4432289, by rfl⟩ : syracuseStep 5909719 = 8864579) B8864579
theorem B2765015 : Blo 818347 2765015 := bstep (se 1 (by rfl) ⟨2073761, by rfl⟩ : syracuseStep 2765015 = 4147523) B4147523
theorem B61487309 : Blo 818347 61487309 := bstep (se 3 (by rfl) ⟨11528870, by rfl⟩ : syracuseStep 61487309 = 23057741) B23057741
theorem B1228967 : Blo 818347 1228967 := bstep (se 1 (by rfl) ⟨921725, by rfl⟩ : syracuseStep 1228967 = 1843451) B1843451
theorem B1230761 : Blo 818347 1230761 := bstep (se 2 (by rfl) ⟨461535, by rfl⟩ : syracuseStep 1230761 = 923071) B923071
theorem B1559407 : Blo 818347 1559407 := bstep (se 1 (by rfl) ⟨1169555, by rfl⟩ : syracuseStep 1559407 = 2339111) B2339111
theorem B1559711 : Blo 818347 1559711 := bstep (se 1 (by rfl) ⟨1169783, by rfl⟩ : syracuseStep 1559711 = 2339567) B2339567
theorem B1233455 : Blo 818347 1233455 := bstep (se 1 (by rfl) ⟨925091, by rfl⟩ : syracuseStep 1233455 = 1850183) B1850183
theorem B32004791 : Blo 818347 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B4157081 : Blo 818347 4157081 := bstep (se 2 (by rfl) ⟨1558905, by rfl⟩ : syracuseStep 4157081 = 3117811) B3117811
theorem B5926583 : Blo 818347 5926583 := bstep (se 1 (by rfl) ⟨4444937, by rfl⟩ : syracuseStep 5926583 = 8889875) B8889875
theorem B818591 : Blo 818347 818591 := bstep (se 1 (by rfl) ⟨613943, by rfl⟩ : syracuseStep 818591 = 1227887) B1227887
theorem B819311 : Blo 818347 819311 := bstep (se 1 (by rfl) ⟨614483, by rfl⟩ : syracuseStep 819311 = 1228967) B1228967
theorem B820507 : Blo 818347 820507 := bstep (se 1 (by rfl) ⟨615380, by rfl⟩ : syracuseStep 820507 = 1230761) B1230761
theorem B5899715 : Blo 818347 5899715 := bstep (se 1 (by rfl) ⟨4424786, by rfl⟩ : syracuseStep 5899715 = 8849573) B8849573
theorem B37816307 : Blo 818347 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B822303 : Blo 818347 822303 := bstep (se 1 (by rfl) ⟨616727, by rfl⟩ : syracuseStep 822303 = 1233455) B1233455
theorem B21336527 : Blo 818347 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B1382143 : Blo 818347 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B1382879 : Blo 818347 1382879 := bstep (se 1 (by rfl) ⟨1037159, by rfl⟩ : syracuseStep 1382879 = 2074319) B2074319
theorem B1843343 : Blo 818347 1843343 := bstep (se 1 (by rfl) ⟨1382507, by rfl⟩ : syracuseStep 1843343 = 2765015) B2765015
theorem B27665945 : Blo 818347 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B1849481 : Blo 818347 1849481 := bstep (se 2 (by rfl) ⟨693555, by rfl⟩ : syracuseStep 1849481 = 1387111) B1387111
theorem B2079209 : Blo 818347 2079209 := bstep (se 2 (by rfl) ⟨779703, by rfl⟩ : syracuseStep 2079209 = 1559407) B1559407
theorem B7879625 : Blo 818347 7879625 := bstep (se 2 (by rfl) ⟨2954859, by rfl⟩ : syracuseStep 7879625 = 5909719) B5909719
theorem B2079827 : Blo 818347 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B25542383 : Blo 818347 25542383 := bstep (se 1 (by rfl) ⟨19156787, by rfl⟩ : syracuseStep 25542383 = 38313575) B38313575
theorem B2771387 : Blo 818347 2771387 := bstep (se 1 (by rfl) ⟨2078540, by rfl⟩ : syracuseStep 2771387 = 4157081) B4157081
theorem B3951055 : Blo 818347 3951055 := bstep (se 1 (by rfl) ⟨2963291, by rfl⟩ : syracuseStep 3951055 = 5926583) B5926583
theorem B43732709 : Blo 818347 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B29972105 : Blo 818347 29972105 := bstep (se 2 (by rfl) ⟨11239539, by rfl⟩ : syracuseStep 29972105 = 22479079) B22479079
theorem B1039807 : Blo 818347 1039807 := bstep (se 1 (by rfl) ⟨779855, by rfl⟩ : syracuseStep 1039807 = 1559711) B1559711
theorem B163966157 : Blo 818347 163966157 := bstep (se 3 (by rfl) ⟨30743654, by rfl⟩ : syracuseStep 163966157 = 61487309) B61487309
theorem B3933143 : Blo 818347 3933143 := bstep (se 1 (by rfl) ⟨2949857, by rfl⟩ : syracuseStep 3933143 = 5899715) B5899715
theorem B14224351 : Blo 818347 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B921919 : Blo 818347 921919 := bstep (se 1 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 921919 = 1382879) B1382879
theorem B1842857 : Blo 818347 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B1386139 : Blo 818347 1386139 := bstep (se 1 (by rfl) ⟨1039604, by rfl⟩ : syracuseStep 1386139 = 2079209) B2079209
theorem B1386409 : Blo 818347 1386409 := bstep (se 2 (by rfl) ⟨519903, by rfl⟩ : syracuseStep 1386409 = 1039807) B1039807
theorem B5253083 : Blo 818347 5253083 := bstep (se 1 (by rfl) ⟨3939812, by rfl⟩ : syracuseStep 5253083 = 7879625) B7879625
theorem B1386551 : Blo 818347 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B25210871 : Blo 818347 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1847591 : Blo 818347 1847591 := bstep (se 1 (by rfl) ⟨1385693, by rfl⟩ : syracuseStep 1847591 = 2771387) B2771387
theorem B1228895 : Blo 818347 1228895 := bstep (se 1 (by rfl) ⟨921671, by rfl⟩ : syracuseStep 1228895 = 1843343) B1843343
theorem B1232987 : Blo 818347 1232987 := bstep (se 1 (by rfl) ⟨924740, by rfl⟩ : syracuseStep 1232987 = 1849481) B1849481
theorem B68113021 : Blo 818347 68113021 := bstep (se 3 (by rfl) ⟨12771191, by rfl⟩ : syracuseStep 68113021 = 25542383) B25542383
theorem B29155139 : Blo 818347 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B5268073 : Blo 818347 5268073 := bstep (se 2 (by rfl) ⟨1975527, by rfl⟩ : syracuseStep 5268073 = 3951055) B3951055
theorem B19981403 : Blo 818347 19981403 := bstep (se 1 (by rfl) ⟨14986052, by rfl⟩ : syracuseStep 19981403 = 29972105) B29972105
theorem B18443963 : Blo 818347 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B109310771 : Blo 818347 109310771 := bstep (se 1 (by rfl) ⟨81983078, by rfl⟩ : syracuseStep 109310771 = 163966157) B163966157
theorem B819263 : Blo 818347 819263 := bstep (se 1 (by rfl) ⟨614447, by rfl⟩ : syracuseStep 819263 = 1228895) B1228895
theorem B2622095 : Blo 818347 2622095 := bstep (se 1 (by rfl) ⟨1966571, by rfl⟩ : syracuseStep 2622095 = 3933143) B3933143
theorem B821991 : Blo 818347 821991 := bstep (se 1 (by rfl) ⟨616493, by rfl⟩ : syracuseStep 821991 = 1232987) B1232987
theorem B19436759 : Blo 818347 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B924367 : Blo 818347 924367 := bstep (se 1 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 924367 = 1386551) B1386551
theorem B12295975 : Blo 818347 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B7024097 : Blo 818347 7024097 := bstep (se 2 (by rfl) ⟨2634036, by rfl⟩ : syracuseStep 7024097 = 5268073) B5268073
theorem B1848185 : Blo 818347 1848185 := bstep (se 2 (by rfl) ⟨693069, by rfl⟩ : syracuseStep 1848185 = 1386139) B1386139
theorem B1848545 : Blo 818347 1848545 := bstep (se 2 (by rfl) ⟨693204, by rfl⟩ : syracuseStep 1848545 = 1386409) B1386409
theorem B1228571 : Blo 818347 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B1229225 : Blo 818347 1229225 := bstep (se 2 (by rfl) ⟨460959, by rfl⟩ : syracuseStep 1229225 = 921919) B921919
theorem B13320935 : Blo 818347 13320935 := bstep (se 1 (by rfl) ⟨9990701, by rfl⟩ : syracuseStep 13320935 = 19981403) B19981403
theorem B90817361 : Blo 818347 90817361 := bstep (se 2 (by rfl) ⟨34056510, by rfl⟩ : syracuseStep 90817361 = 68113021) B68113021
theorem B1231727 : Blo 818347 1231727 := bstep (se 1 (by rfl) ⟨923795, by rfl⟩ : syracuseStep 1231727 = 1847591) B1847591
theorem B18965801 : Blo 818347 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B3502055 : Blo 818347 3502055 := bstep (se 1 (by rfl) ⟨2626541, by rfl⟩ : syracuseStep 3502055 = 5253083) B5253083
theorem B16807247 : Blo 818347 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B72873847 : Blo 818347 72873847 := bstep (se 1 (by rfl) ⟨54655385, by rfl⟩ : syracuseStep 72873847 = 109310771) B109310771
theorem B819483 : Blo 818347 819483 := bstep (se 1 (by rfl) ⟨614612, by rfl⟩ : syracuseStep 819483 = 1229225) B1229225
theorem B8880623 : Blo 818347 8880623 := bstep (se 1 (by rfl) ⟨6660467, by rfl⟩ : syracuseStep 8880623 = 13320935) B13320935
theorem B821151 : Blo 818347 821151 := bstep (se 1 (by rfl) ⟨615863, by rfl⟩ : syracuseStep 821151 = 1231727) B1231727
theorem B2334703 : Blo 818347 2334703 := bstep (se 1 (by rfl) ⟨1751027, by rfl⟩ : syracuseStep 2334703 = 3502055) B3502055
theorem B16394633 : Blo 818347 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B1748063 : Blo 818347 1748063 := bstep (se 1 (by rfl) ⟨1311047, by rfl⟩ : syracuseStep 1748063 = 2622095) B2622095
theorem B12957839 : Blo 818347 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B1232123 : Blo 818347 1232123 := bstep (se 1 (by rfl) ⟨924092, by rfl⟩ : syracuseStep 1232123 = 1848185) B1848185
theorem B1232363 : Blo 818347 1232363 := bstep (se 1 (by rfl) ⟨924272, by rfl⟩ : syracuseStep 1232363 = 1848545) B1848545
theorem B1232489 : Blo 818347 1232489 := bstep (se 2 (by rfl) ⟨462183, by rfl⟩ : syracuseStep 1232489 = 924367) B924367
theorem B60544907 : Blo 818347 60544907 := bstep (se 1 (by rfl) ⟨45408680, by rfl⟩ : syracuseStep 60544907 = 90817361) B90817361
theorem B12643867 : Blo 818347 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B4682731 : Blo 818347 4682731 := bstep (se 1 (by rfl) ⟨3512048, by rfl⟩ : syracuseStep 4682731 = 7024097) B7024097
theorem B11204831 : Blo 818347 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B388660517 : Blo 818347 388660517 := bstep (se 4 (by rfl) ⟨36436923, by rfl⟩ : syracuseStep 388660517 = 72873847) B72873847
theorem B819047 : Blo 818347 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B821415 : Blo 818347 821415 := bstep (se 1 (by rfl) ⟨616061, by rfl⟩ : syracuseStep 821415 = 1232123) B1232123
theorem B821575 : Blo 818347 821575 := bstep (se 1 (by rfl) ⟨616181, by rfl⟩ : syracuseStep 821575 = 1232363) B1232363
theorem B821659 : Blo 818347 821659 := bstep (se 1 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 821659 = 1232489) B1232489
theorem B259107011 : Blo 818347 259107011 := bstep (se 1 (by rfl) ⟨194330258, by rfl⟩ : syracuseStep 259107011 = 388660517) B388660517
theorem B6243641 : Blo 818347 6243641 := bstep (se 2 (by rfl) ⟨2341365, by rfl⟩ : syracuseStep 6243641 = 4682731) B4682731
theorem B10929755 : Blo 818347 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B1165375 : Blo 818347 1165375 := bstep (se 1 (by rfl) ⟨874031, by rfl⟩ : syracuseStep 1165375 = 1748063) B1748063
theorem B8638559 : Blo 818347 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B5920415 : Blo 818347 5920415 := bstep (se 1 (by rfl) ⟨4440311, by rfl⟩ : syracuseStep 5920415 = 8880623) B8880623
theorem B40363271 : Blo 818347 40363271 := bstep (se 1 (by rfl) ⟨30272453, by rfl⟩ : syracuseStep 40363271 = 60544907) B60544907
theorem B67433957 : Blo 818347 67433957 := bstep (se 4 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 67433957 = 12643867) B12643867
theorem B7469887 : Blo 818347 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B3112937 : Blo 818347 3112937 := bstep (se 2 (by rfl) ⟨1167351, by rfl⟩ : syracuseStep 3112937 = 2334703) B2334703
theorem B4162427 : Blo 818347 4162427 := bstep (se 1 (by rfl) ⟨3121820, by rfl⟩ : syracuseStep 4162427 = 6243641) B6243641
theorem B26908847 : Blo 818347 26908847 := bstep (se 1 (by rfl) ⟨20181635, by rfl⟩ : syracuseStep 26908847 = 40363271) B40363271
theorem B2075291 : Blo 818347 2075291 := bstep (se 1 (by rfl) ⟨1556468, by rfl⟩ : syracuseStep 2075291 = 3112937) B3112937
theorem B1553833 : Blo 818347 1553833 := bstep (se 2 (by rfl) ⟨582687, by rfl⟩ : syracuseStep 1553833 = 1165375) B1165375
theorem B3946943 : Blo 818347 3946943 := bstep (se 1 (by rfl) ⟨2960207, by rfl⟩ : syracuseStep 3946943 = 5920415) B5920415
theorem B29146013 : Blo 818347 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B172738007 : Blo 818347 172738007 := bstep (se 1 (by rfl) ⟨129553505, by rfl⟩ : syracuseStep 172738007 = 259107011) B259107011
theorem B5759039 : Blo 818347 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B44955971 : Blo 818347 44955971 := bstep (se 1 (by rfl) ⟨33716978, by rfl⟩ : syracuseStep 44955971 = 67433957) B67433957
theorem B9959849 : Blo 818347 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B3839359 : Blo 818347 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B1383527 : Blo 818347 1383527 := bstep (se 1 (by rfl) ⟨1037645, by rfl⟩ : syracuseStep 1383527 = 2075291) B2075291
theorem B2071777 : Blo 818347 2071777 := bstep (se 2 (by rfl) ⟨776916, by rfl⟩ : syracuseStep 2071777 = 1553833) B1553833
theorem B2631295 : Blo 818347 2631295 := bstep (se 1 (by rfl) ⟨1973471, by rfl⟩ : syracuseStep 2631295 = 3946943) B3946943
theorem B115158671 : Blo 818347 115158671 := bstep (se 1 (by rfl) ⟨86369003, by rfl⟩ : syracuseStep 115158671 = 172738007) B172738007
theorem B17939231 : Blo 818347 17939231 := bstep (se 1 (by rfl) ⟨13454423, by rfl⟩ : syracuseStep 17939231 = 26908847) B26908847
theorem B29970647 : Blo 818347 29970647 := bstep (se 1 (by rfl) ⟨22477985, by rfl⟩ : syracuseStep 29970647 = 44955971) B44955971
theorem B6639899 : Blo 818347 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B2774951 : Blo 818347 2774951 := bstep (se 1 (by rfl) ⟨2081213, by rfl⟩ : syracuseStep 2774951 = 4162427) B4162427
theorem B19430675 : Blo 818347 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B3508393 : Blo 818347 3508393 := bstep (se 2 (by rfl) ⟨1315647, by rfl⟩ : syracuseStep 3508393 = 2631295) B2631295
theorem B922351 : Blo 818347 922351 := bstep (se 1 (by rfl) ⟨691763, by rfl⟩ : syracuseStep 922351 = 1383527) B1383527
theorem B5119145 : Blo 818347 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B2762369 : Blo 818347 2762369 := bstep (se 2 (by rfl) ⟨1035888, by rfl⟩ : syracuseStep 2762369 = 2071777) B2071777
theorem B12953783 : Blo 818347 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B17706397 : Blo 818347 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B1849967 : Blo 818347 1849967 := bstep (se 1 (by rfl) ⟨1387475, by rfl⟩ : syracuseStep 1849967 = 2774951) B2774951
theorem B19980431 : Blo 818347 19980431 := bstep (se 1 (by rfl) ⟨14985323, by rfl⟩ : syracuseStep 19980431 = 29970647) B29970647
theorem B76772447 : Blo 818347 76772447 := bstep (se 1 (by rfl) ⟨57579335, by rfl⟩ : syracuseStep 76772447 = 115158671) B115158671
theorem B11959487 : Blo 818347 11959487 := bstep (se 1 (by rfl) ⟨8969615, by rfl⟩ : syracuseStep 11959487 = 17939231) B17939231
theorem B3412763 : Blo 818347 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B1841579 : Blo 818347 1841579 := bstep (se 1 (by rfl) ⟨1381184, by rfl⟩ : syracuseStep 1841579 = 2762369) B2762369
theorem B7972991 : Blo 818347 7972991 := bstep (se 1 (by rfl) ⟨5979743, by rfl⟩ : syracuseStep 7972991 = 11959487) B11959487
theorem B23608529 : Blo 818347 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B13320287 : Blo 818347 13320287 := bstep (se 1 (by rfl) ⟨9990215, by rfl⟩ : syracuseStep 13320287 = 19980431) B19980431
theorem B1229801 : Blo 818347 1229801 := bstep (se 2 (by rfl) ⟨461175, by rfl⟩ : syracuseStep 1229801 = 922351) B922351
theorem B8635855 : Blo 818347 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B1233311 : Blo 818347 1233311 := bstep (se 1 (by rfl) ⟨924983, by rfl⟩ : syracuseStep 1233311 = 1849967) B1849967
theorem B4677857 : Blo 818347 4677857 := bstep (se 2 (by rfl) ⟨1754196, by rfl⟩ : syracuseStep 4677857 = 3508393) B3508393
theorem B51181631 : Blo 818347 51181631 := bstep (se 1 (by rfl) ⟨38386223, by rfl⟩ : syracuseStep 51181631 = 76772447) B76772447
theorem B8880191 : Blo 818347 8880191 := bstep (se 1 (by rfl) ⟨6660143, by rfl⟩ : syracuseStep 8880191 = 13320287) B13320287
theorem B819867 : Blo 818347 819867 := bstep (se 1 (by rfl) ⟨614900, by rfl⟩ : syracuseStep 819867 = 1229801) B1229801
theorem B822207 : Blo 818347 822207 := bstep (se 1 (by rfl) ⟨616655, by rfl⟩ : syracuseStep 822207 = 1233311) B1233311
theorem B3118571 : Blo 818347 3118571 := bstep (se 1 (by rfl) ⟨2338928, by rfl⟩ : syracuseStep 3118571 = 4677857) B4677857
theorem B5315327 : Blo 818347 5315327 := bstep (se 1 (by rfl) ⟨3986495, by rfl⟩ : syracuseStep 5315327 = 7972991) B7972991
theorem B34121087 : Blo 818347 34121087 := bstep (se 1 (by rfl) ⟨25590815, by rfl⟩ : syracuseStep 34121087 = 51181631) B51181631
theorem B15739019 : Blo 818347 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B11514473 : Blo 818347 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B2275175 : Blo 818347 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B1227719 : Blo 818347 1227719 := bstep (se 1 (by rfl) ⟨920789, by rfl⟩ : syracuseStep 1227719 = 1841579) B1841579
theorem B3543551 : Blo 818347 3543551 := bstep (se 1 (by rfl) ⟨2657663, by rfl⟩ : syracuseStep 3543551 = 5315327) B5315327
theorem B6067133 : Blo 818347 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B22747391 : Blo 818347 22747391 := bstep (se 1 (by rfl) ⟨17060543, by rfl⟩ : syracuseStep 22747391 = 34121087) B34121087
theorem B10492679 : Blo 818347 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B7676315 : Blo 818347 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B2079047 : Blo 818347 2079047 := bstep (se 1 (by rfl) ⟨1559285, by rfl⟩ : syracuseStep 2079047 = 3118571) B3118571
theorem B5920127 : Blo 818347 5920127 := bstep (se 1 (by rfl) ⟨4440095, by rfl⟩ : syracuseStep 5920127 = 8880191) B8880191
theorem B818479 : Blo 818347 818479 := bstep (se 1 (by rfl) ⟨613859, by rfl⟩ : syracuseStep 818479 = 1227719) B1227719
theorem B2362367 : Blo 818347 2362367 := bstep (se 1 (by rfl) ⟨1771775, by rfl⟩ : syracuseStep 2362367 = 3543551) B3543551
theorem B5117543 : Blo 818347 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B1386031 : Blo 818347 1386031 := bstep (se 1 (by rfl) ⟨1039523, by rfl⟩ : syracuseStep 1386031 = 2079047) B2079047
theorem B4044755 : Blo 818347 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B3946751 : Blo 818347 3946751 := bstep (se 1 (by rfl) ⟨2960063, by rfl⟩ : syracuseStep 3946751 = 5920127) B5920127
theorem B6995119 : Blo 818347 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B15164927 : Blo 818347 15164927 := bstep (se 1 (by rfl) ⟨11373695, by rfl⟩ : syracuseStep 15164927 = 22747391) B22747391
theorem B1574911 : Blo 818347 1574911 := bstep (se 1 (by rfl) ⟨1181183, by rfl⟩ : syracuseStep 1574911 = 2362367) B2362367
theorem B3411695 : Blo 818347 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B2696503 : Blo 818347 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B2631167 : Blo 818347 2631167 := bstep (se 1 (by rfl) ⟨1973375, by rfl⟩ : syracuseStep 2631167 = 3946751) B3946751
theorem B1848041 : Blo 818347 1848041 := bstep (se 2 (by rfl) ⟨693015, by rfl⟩ : syracuseStep 1848041 = 1386031) B1386031
theorem B10109951 : Blo 818347 10109951 := bstep (se 1 (by rfl) ⟨7582463, by rfl⟩ : syracuseStep 10109951 = 15164927) B15164927
theorem B9326825 : Blo 818347 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B2099881 : Blo 818347 2099881 := bstep (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) B1574911
theorem B2274463 : Blo 818347 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B1754111 : Blo 818347 1754111 := bstep (se 1 (by rfl) ⟨1315583, by rfl⟩ : syracuseStep 1754111 = 2631167) B2631167
theorem B1232027 : Blo 818347 1232027 := bstep (se 1 (by rfl) ⟨924020, by rfl⟩ : syracuseStep 1232027 = 1848041) B1848041
theorem B6739967 : Blo 818347 6739967 := bstep (se 1 (by rfl) ⟨5054975, by rfl⟩ : syracuseStep 6739967 = 10109951) B10109951
theorem B3595337 : Blo 818347 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B6217883 : Blo 818347 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B821351 : Blo 818347 821351 := bstep (se 1 (by rfl) ⟨616013, by rfl⟩ : syracuseStep 821351 = 1232027) B1232027
theorem B2396891 : Blo 818347 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B12130469 : Blo 818347 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B2799841 : Blo 818347 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B17973245 : Blo 818347 17973245 := bstep (se 3 (by rfl) ⟨3369983, by rfl⟩ : syracuseStep 17973245 = 6739967) B6739967
theorem B4145255 : Blo 818347 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B1169407 : Blo 818347 1169407 := bstep (se 1 (by rfl) ⟨877055, by rfl⟩ : syracuseStep 1169407 = 1754111) B1754111
theorem B6236837 : Blo 818347 6236837 := bstep (se 4 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 6236837 = 1169407) B1169407
theorem B2763503 : Blo 818347 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B11982163 : Blo 818347 11982163 := bstep (se 1 (by rfl) ⟨8986622, by rfl⟩ : syracuseStep 11982163 = 17973245) B17973245
theorem B1597927 : Blo 818347 1597927 := bstep (se 1 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 1597927 = 2396891) B2396891
theorem B8086979 : Blo 818347 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B3733121 : Blo 818347 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B2130569 : Blo 818347 2130569 := bstep (se 2 (by rfl) ⟨798963, by rfl⟩ : syracuseStep 2130569 = 1597927) B1597927
theorem B21565277 : Blo 818347 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B1842335 : Blo 818347 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B15976217 : Blo 818347 15976217 := bstep (se 2 (by rfl) ⟨5991081, by rfl⟩ : syracuseStep 15976217 = 11982163) B11982163
theorem B4157891 : Blo 818347 4157891 := bstep (se 1 (by rfl) ⟨3118418, by rfl⟩ : syracuseStep 4157891 = 6236837) B6236837
theorem B2488747 : Blo 818347 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B10650811 : Blo 818347 10650811 := bstep (se 1 (by rfl) ⟨7988108, by rfl⟩ : syracuseStep 10650811 = 15976217) B15976217
theorem B3318329 : Blo 818347 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B1420379 : Blo 818347 1420379 := bstep (se 1 (by rfl) ⟨1065284, by rfl⟩ : syracuseStep 1420379 = 2130569) B2130569
theorem B1228223 : Blo 818347 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B2771927 : Blo 818347 2771927 := bstep (se 1 (by rfl) ⟨2078945, by rfl⟩ : syracuseStep 2771927 = 4157891) B4157891
theorem B14376851 : Blo 818347 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B14201081 : Blo 818347 14201081 := bstep (se 2 (by rfl) ⟨5325405, by rfl⟩ : syracuseStep 14201081 = 10650811) B10650811
theorem B1847951 : Blo 818347 1847951 := bstep (se 1 (by rfl) ⟨1385963, by rfl⟩ : syracuseStep 1847951 = 2771927) B2771927
theorem B9584567 : Blo 818347 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B2212219 : Blo 818347 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B946919 : Blo 818347 946919 := bstep (se 1 (by rfl) ⟨710189, by rfl⟩ : syracuseStep 946919 = 1420379) B1420379
theorem B818815 : Blo 818347 818815 := bstep (se 1 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 818815 = 1228223) B1228223
theorem B2949625 : Blo 818347 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B2525117 : Blo 818347 2525117 := bstep (se 3 (by rfl) ⟨473459, by rfl⟩ : syracuseStep 2525117 = 946919) B946919
theorem B1231967 : Blo 818347 1231967 := bstep (se 1 (by rfl) ⟨923975, by rfl⟩ : syracuseStep 1231967 = 1847951) B1847951
theorem B9467387 : Blo 818347 9467387 := bstep (se 1 (by rfl) ⟨7100540, by rfl⟩ : syracuseStep 9467387 = 14201081) B14201081
theorem B6389711 : Blo 818347 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B821311 : Blo 818347 821311 := bstep (se 1 (by rfl) ⟨615983, by rfl⟩ : syracuseStep 821311 = 1231967) B1231967
theorem B15731333 : Blo 818347 15731333 := bstep (se 4 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 15731333 = 2949625) B2949625
theorem B6311591 : Blo 818347 6311591 := bstep (se 1 (by rfl) ⟨4733693, by rfl⟩ : syracuseStep 6311591 = 9467387) B9467387
theorem B26934581 : Blo 818347 26934581 := bstep (se 5 (by rfl) ⟨1262558, by rfl⟩ : syracuseStep 26934581 = 2525117) B2525117
theorem B4259807 : Blo 818347 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B10487555 : Blo 818347 10487555 := bstep (se 1 (by rfl) ⟨7865666, by rfl⟩ : syracuseStep 10487555 = 15731333) B15731333
theorem B4207727 : Blo 818347 4207727 := bstep (se 1 (by rfl) ⟨3155795, by rfl⟩ : syracuseStep 4207727 = 6311591) B6311591
theorem B2839871 : Blo 818347 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B17956387 : Blo 818347 17956387 := bstep (se 1 (by rfl) ⟨13467290, by rfl⟩ : syracuseStep 17956387 = 26934581) B26934581
theorem B7572989 : Blo 818347 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B6991703 : Blo 818347 6991703 := bstep (se 1 (by rfl) ⟨5243777, by rfl⟩ : syracuseStep 6991703 = 10487555) B10487555
theorem B2805151 : Blo 818347 2805151 := bstep (se 1 (by rfl) ⟨2103863, by rfl⟩ : syracuseStep 2805151 = 4207727) B4207727
theorem B23941849 : Blo 818347 23941849 := bstep (se 2 (by rfl) ⟨8978193, by rfl⟩ : syracuseStep 23941849 = 17956387) B17956387
theorem B5048659 : Blo 818347 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B3740201 : Blo 818347 3740201 := bstep (se 2 (by rfl) ⟨1402575, by rfl⟩ : syracuseStep 3740201 = 2805151) B2805151
theorem B31922465 : Blo 818347 31922465 := bstep (se 2 (by rfl) ⟨11970924, by rfl⟩ : syracuseStep 31922465 = 23941849) B23941849
theorem B4661135 : Blo 818347 4661135 := bstep (se 1 (by rfl) ⟨3495851, by rfl⟩ : syracuseStep 4661135 = 6991703) B6991703
theorem B2493467 : Blo 818347 2493467 := bstep (se 1 (by rfl) ⟨1870100, by rfl⟩ : syracuseStep 2493467 = 3740201) B3740201
theorem B6731545 : Blo 818347 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B3107423 : Blo 818347 3107423 := bstep (se 1 (by rfl) ⟨2330567, by rfl⟩ : syracuseStep 3107423 = 4661135) B4661135
theorem B85126573 : Blo 818347 85126573 := bstep (se 3 (by rfl) ⟨15961232, by rfl⟩ : syracuseStep 85126573 = 31922465) B31922465
theorem B2071615 : Blo 818347 2071615 := bstep (se 1 (by rfl) ⟨1553711, by rfl⟩ : syracuseStep 2071615 = 3107423) B3107423
theorem B1662311 : Blo 818347 1662311 := bstep (se 1 (by rfl) ⟨1246733, by rfl⟩ : syracuseStep 1662311 = 2493467) B2493467
theorem B113502097 : Blo 818347 113502097 := bstep (se 2 (by rfl) ⟨42563286, by rfl⟩ : syracuseStep 113502097 = 85126573) B85126573
theorem B8975393 : Blo 818347 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B2762153 : Blo 818347 2762153 := bstep (se 2 (by rfl) ⟨1035807, by rfl⟩ : syracuseStep 2762153 = 2071615) B2071615
theorem B151336129 : Blo 818347 151336129 := bstep (se 2 (by rfl) ⟨56751048, by rfl⟩ : syracuseStep 151336129 = 113502097) B113502097
theorem B5983595 : Blo 818347 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B1108207 : Blo 818347 1108207 := bstep (se 1 (by rfl) ⟨831155, by rfl⟩ : syracuseStep 1108207 = 1662311) B1662311
theorem B1477609 : Blo 818347 1477609 := bstep (se 2 (by rfl) ⟨554103, by rfl⟩ : syracuseStep 1477609 = 1108207) B1108207
theorem B1841435 : Blo 818347 1841435 := bstep (se 1 (by rfl) ⟨1381076, by rfl⟩ : syracuseStep 1841435 = 2762153) B2762153
theorem B3989063 : Blo 818347 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B201781505 : Blo 818347 201781505 := bstep (se 2 (by rfl) ⟨75668064, by rfl⟩ : syracuseStep 201781505 = 151336129) B151336129
theorem B2659375 : Blo 818347 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B134521003 : Blo 818347 134521003 := bstep (se 1 (by rfl) ⟨100890752, by rfl⟩ : syracuseStep 134521003 = 201781505) B201781505
theorem B1227623 : Blo 818347 1227623 := bstep (se 1 (by rfl) ⟨920717, by rfl⟩ : syracuseStep 1227623 = 1841435) B1841435
theorem B7880581 : Blo 818347 7880581 := bstep (se 4 (by rfl) ⟨738804, by rfl⟩ : syracuseStep 7880581 = 1477609) B1477609
theorem B10507441 : Blo 818347 10507441 := bstep (se 2 (by rfl) ⟨3940290, by rfl⟩ : syracuseStep 10507441 = 7880581) B7880581
theorem B179361337 : Blo 818347 179361337 := bstep (se 2 (by rfl) ⟨67260501, by rfl⟩ : syracuseStep 179361337 = 134521003) B134521003
theorem B14183333 : Blo 818347 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B818415 : Blo 818347 818415 := bstep (se 1 (by rfl) ⟨613811, by rfl⟩ : syracuseStep 818415 = 1227623) B1227623
theorem B239148449 : Blo 818347 239148449 := bstep (se 2 (by rfl) ⟨89680668, by rfl⟩ : syracuseStep 239148449 = 179361337) B179361337
theorem B14009921 : Blo 818347 14009921 := bstep (se 2 (by rfl) ⟨5253720, by rfl⟩ : syracuseStep 14009921 = 10507441) B10507441
theorem B9455555 : Blo 818347 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B9339947 : Blo 818347 9339947 := bstep (se 1 (by rfl) ⟨7004960, by rfl⟩ : syracuseStep 9339947 = 14009921) B14009921
theorem B6303703 : Blo 818347 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B159432299 : Blo 818347 159432299 := bstep (se 1 (by rfl) ⟨119574224, by rfl⟩ : syracuseStep 159432299 = 239148449) B239148449
theorem B6226631 : Blo 818347 6226631 := bstep (se 1 (by rfl) ⟨4669973, by rfl⟩ : syracuseStep 6226631 = 9339947) B9339947
theorem B8404937 : Blo 818347 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B106288199 : Blo 818347 106288199 := bstep (se 1 (by rfl) ⟨79716149, by rfl⟩ : syracuseStep 106288199 = 159432299) B159432299
theorem B70858799 : Blo 818347 70858799 := bstep (se 1 (by rfl) ⟨53144099, by rfl⟩ : syracuseStep 70858799 = 106288199) B106288199
theorem B4151087 : Blo 818347 4151087 := bstep (se 1 (by rfl) ⟨3113315, by rfl⟩ : syracuseStep 4151087 = 6226631) B6226631
theorem B5603291 : Blo 818347 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B2767391 : Blo 818347 2767391 := bstep (se 1 (by rfl) ⟨2075543, by rfl⟩ : syracuseStep 2767391 = 4151087) B4151087
theorem B47239199 : Blo 818347 47239199 := bstep (se 1 (by rfl) ⟨35429399, by rfl⟩ : syracuseStep 47239199 = 70858799) B70858799
theorem B3735527 : Blo 818347 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B31492799 : Blo 818347 31492799 := bstep (se 1 (by rfl) ⟨23619599, by rfl⟩ : syracuseStep 31492799 = 47239199) B47239199
theorem B1844927 : Blo 818347 1844927 := bstep (se 1 (by rfl) ⟨1383695, by rfl⟩ : syracuseStep 1844927 = 2767391) B2767391
theorem B39845621 : Blo 818347 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B1229951 : Blo 818347 1229951 := bstep (se 1 (by rfl) ⟨922463, by rfl⟩ : syracuseStep 1229951 = 1844927) B1844927
theorem B26563747 : Blo 818347 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B20995199 : Blo 818347 20995199 := bstep (se 1 (by rfl) ⟨15746399, by rfl⟩ : syracuseStep 20995199 = 31492799) B31492799
theorem B819967 : Blo 818347 819967 := bstep (se 1 (by rfl) ⟨614975, by rfl⟩ : syracuseStep 819967 = 1229951) B1229951
theorem B13996799 : Blo 818347 13996799 := bstep (se 1 (by rfl) ⟨10497599, by rfl⟩ : syracuseStep 13996799 = 20995199) B20995199
theorem B35418329 : Blo 818347 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B23612219 : Blo 818347 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B9331199 : Blo 818347 9331199 := bstep (se 1 (by rfl) ⟨6998399, by rfl⟩ : syracuseStep 9331199 = 13996799) B13996799
theorem B15741479 : Blo 818347 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B6220799 : Blo 818347 6220799 := bstep (se 1 (by rfl) ⟨4665599, by rfl⟩ : syracuseStep 6220799 = 9331199) B9331199
theorem B10494319 : Blo 818347 10494319 := bstep (se 1 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 10494319 = 15741479) B15741479
theorem B4147199 : Blo 818347 4147199 := bstep (se 1 (by rfl) ⟨3110399, by rfl⟩ : syracuseStep 4147199 = 6220799) B6220799
theorem B13992425 : Blo 818347 13992425 := bstep (se 2 (by rfl) ⟨5247159, by rfl⟩ : syracuseStep 13992425 = 10494319) B10494319
theorem B2764799 : Blo 818347 2764799 := bstep (se 1 (by rfl) ⟨2073599, by rfl⟩ : syracuseStep 2764799 = 4147199) B4147199
theorem B1843199 : Blo 818347 1843199 := bstep (se 1 (by rfl) ⟨1382399, by rfl⟩ : syracuseStep 1843199 = 2764799) B2764799
theorem B9328283 : Blo 818347 9328283 := bstep (se 1 (by rfl) ⟨6996212, by rfl⟩ : syracuseStep 9328283 = 13992425) B13992425
theorem B1228799 : Blo 818347 1228799 := bstep (se 1 (by rfl) ⟨921599, by rfl⟩ : syracuseStep 1228799 = 1843199) B1843199
theorem B6218855 : Blo 818347 6218855 := bstep (se 1 (by rfl) ⟨4664141, by rfl⟩ : syracuseStep 6218855 = 9328283) B9328283
theorem B4145903 : Blo 818347 4145903 := bstep (se 1 (by rfl) ⟨3109427, by rfl⟩ : syracuseStep 4145903 = 6218855) B6218855
theorem B819199 : Blo 818347 819199 := bstep (se 1 (by rfl) ⟨614399, by rfl⟩ : syracuseStep 819199 = 1228799) B1228799
theorem B2763935 : Blo 818347 2763935 := bstep (se 1 (by rfl) ⟨2072951, by rfl⟩ : syracuseStep 2763935 = 4145903) B4145903
theorem B1842623 : Blo 818347 1842623 := bstep (se 1 (by rfl) ⟨1381967, by rfl⟩ : syracuseStep 1842623 = 2763935) B2763935
theorem B1228415 : Blo 818347 1228415 := bstep (se 1 (by rfl) ⟨921311, by rfl⟩ : syracuseStep 1228415 = 1842623) B1842623
theorem B818943 : Blo 818347 818943 := bstep (se 1 (by rfl) ⟨614207, by rfl⟩ : syracuseStep 818943 = 1228415) B1228415

theorem C0 (j : ℕ) (h1 : 204586 ≤ j) (h2 : j ≤ 205285) : Blo 818347 (4 * j + 3) := by
  interval_cases j
  · exact B818347
  · exact B818351
  · exact B818355
  · exact B818359
  · exact B818363
  · exact B818367
  · exact B818371
  · exact B818375
  · exact B818379
  · exact B818383
  · exact B818387
  · exact B818391
  · exact B818395
  · exact B818399
  · exact B818403
  · exact B818407
  · exact B818411
  · exact B818415
  · exact B818419
  · exact B818423
  · exact B818427
  · exact B818431
  · exact B818435
  · exact B818439
  · exact B818443
  · exact B818447
  · exact B818451
  · exact B818455
  · exact B818459
  · exact B818463
  · exact B818467
  · exact B818471
  · exact B818475
  · exact B818479
  · exact B818483
  · exact B818487
  · exact B818491
  · exact B818495
  · exact B818499
  · exact B818503
  · exact B818507
  · exact B818511
  · exact B818515
  · exact B818519
  · exact B818523
  · exact B818527
  · exact B818531
  · exact B818535
  · exact B818539
  · exact B818543
  · exact B818547
  · exact B818551
  · exact B818555
  · exact B818559
  · exact B818563
  · exact B818567
  · exact B818571
  · exact B818575
  · exact B818579
  · exact B818583
  · exact B818587
  · exact B818591
  · exact B818595
  · exact B818599
  · exact B818603
  · exact B818607
  · exact B818611
  · exact B818615
  · exact B818619
  · exact B818623
  · exact B818627
  · exact B818631
  · exact B818635
  · exact B818639
  · exact B818643
  · exact B818647
  · exact B818651
  · exact B818655
  · exact B818659
  · exact B818663
  · exact B818667
  · exact B818671
  · exact B818675
  · exact B818679
  · exact B818683
  · exact B818687
  · exact B818691
  · exact B818695
  · exact B818699
  · exact B818703
  · exact B818707
  · exact B818711
  · exact B818715
  · exact B818719
  · exact B818723
  · exact B818727
  · exact B818731
  · exact B818735
  · exact B818739
  · exact B818743
  · exact B818747
  · exact B818751
  · exact B818755
  · exact B818759
  · exact B818763
  · exact B818767
  · exact B818771
  · exact B818775
  · exact B818779
  · exact B818783
  · exact B818787
  · exact B818791
  · exact B818795
  · exact B818799
  · exact B818803
  · exact B818807
  · exact B818811
  · exact B818815
  · exact B818819
  · exact B818823
  · exact B818827
  · exact B818831
  · exact B818835
  · exact B818839
  · exact B818843
  · exact B818847
  · exact B818851
  · exact B818855
  · exact B818859
  · exact B818863
  · exact B818867
  · exact B818871
  · exact B818875
  · exact B818879
  · exact B818883
  · exact B818887
  · exact B818891
  · exact B818895
  · exact B818899
  · exact B818903
  · exact B818907
  · exact B818911
  · exact B818915
  · exact B818919
  · exact B818923
  · exact B818927
  · exact B818931
  · exact B818935
  · exact B818939
  · exact B818943
  · exact B818947
  · exact B818951
  · exact B818955
  · exact B818959
  · exact B818963
  · exact B818967
  · exact B818971
  · exact B818975
  · exact B818979
  · exact B818983
  · exact B818987
  · exact B818991
  · exact B818995
  · exact B818999
  · exact B819003
  · exact B819007
  · exact B819011
  · exact B819015
  · exact B819019
  · exact B819023
  · exact B819027
  · exact B819031
  · exact B819035
  · exact B819039
  · exact B819043
  · exact B819047
  · exact B819051
  · exact B819055
  · exact B819059
  · exact B819063
  · exact B819067
  · exact B819071
  · exact B819075
  · exact B819079
  · exact B819083
  · exact B819087
  · exact B819091
  · exact B819095
  · exact B819099
  · exact B819103
  · exact B819107
  · exact B819111
  · exact B819115
  · exact B819119
  · exact B819123
  · exact B819127
  · exact B819131
  · exact B819135
  · exact B819139
  · exact B819143
  · exact B819147
  · exact B819151
  · exact B819155
  · exact B819159
  · exact B819163
  · exact B819167
  · exact B819171
  · exact B819175
  · exact B819179
  · exact B819183
  · exact B819187
  · exact B819191
  · exact B819195
  · exact B819199
  · exact B819203
  · exact B819207
  · exact B819211
  · exact B819215
  · exact B819219
  · exact B819223
  · exact B819227
  · exact B819231
  · exact B819235
  · exact B819239
  · exact B819243
  · exact B819247
  · exact B819251
  · exact B819255
  · exact B819259
  · exact B819263
  · exact B819267
  · exact B819271
  · exact B819275
  · exact B819279
  · exact B819283
  · exact B819287
  · exact B819291
  · exact B819295
  · exact B819299
  · exact B819303
  · exact B819307
  · exact B819311
  · exact B819315
  · exact B819319
  · exact B819323
  · exact B819327
  · exact B819331
  · exact B819335
  · exact B819339
  · exact B819343
  · exact B819347
  · exact B819351
  · exact B819355
  · exact B819359
  · exact B819363
  · exact B819367
  · exact B819371
  · exact B819375
  · exact B819379
  · exact B819383
  · exact B819387
  · exact B819391
  · exact B819395
  · exact B819399
  · exact B819403
  · exact B819407
  · exact B819411
  · exact B819415
  · exact B819419
  · exact B819423
  · exact B819427
  · exact B819431
  · exact B819435
  · exact B819439
  · exact B819443
  · exact B819447
  · exact B819451
  · exact B819455
  · exact B819459
  · exact B819463
  · exact B819467
  · exact B819471
  · exact B819475
  · exact B819479
  · exact B819483
  · exact B819487
  · exact B819491
  · exact B819495
  · exact B819499
  · exact B819503
  · exact B819507
  · exact B819511
  · exact B819515
  · exact B819519
  · exact B819523
  · exact B819527
  · exact B819531
  · exact B819535
  · exact B819539
  · exact B819543
  · exact B819547
  · exact B819551
  · exact B819555
  · exact B819559
  · exact B819563
  · exact B819567
  · exact B819571
  · exact B819575
  · exact B819579
  · exact B819583
  · exact B819587
  · exact B819591
  · exact B819595
  · exact B819599
  · exact B819603
  · exact B819607
  · exact B819611
  · exact B819615
  · exact B819619
  · exact B819623
  · exact B819627
  · exact B819631
  · exact B819635
  · exact B819639
  · exact B819643
  · exact B819647
  · exact B819651
  · exact B819655
  · exact B819659
  · exact B819663
  · exact B819667
  · exact B819671
  · exact B819675
  · exact B819679
  · exact B819683
  · exact B819687
  · exact B819691
  · exact B819695
  · exact B819699
  · exact B819703
  · exact B819707
  · exact B819711
  · exact B819715
  · exact B819719
  · exact B819723
  · exact B819727
  · exact B819731
  · exact B819735
  · exact B819739
  · exact B819743
  · exact B819747
  · exact B819751
  · exact B819755
  · exact B819759
  · exact B819763
  · exact B819767
  · exact B819771
  · exact B819775
  · exact B819779
  · exact B819783
  · exact B819787
  · exact B819791
  · exact B819795
  · exact B819799
  · exact B819803
  · exact B819807
  · exact B819811
  · exact B819815
  · exact B819819
  · exact B819823
  · exact B819827
  · exact B819831
  · exact B819835
  · exact B819839
  · exact B819843
  · exact B819847
  · exact B819851
  · exact B819855
  · exact B819859
  · exact B819863
  · exact B819867
  · exact B819871
  · exact B819875
  · exact B819879
  · exact B819883
  · exact B819887
  · exact B819891
  · exact B819895
  · exact B819899
  · exact B819903
  · exact B819907
  · exact B819911
  · exact B819915
  · exact B819919
  · exact B819923
  · exact B819927
  · exact B819931
  · exact B819935
  · exact B819939
  · exact B819943
  · exact B819947
  · exact B819951
  · exact B819955
  · exact B819959
  · exact B819963
  · exact B819967
  · exact B819971
  · exact B819975
  · exact B819979
  · exact B819983
  · exact B819987
  · exact B819991
  · exact B819995
  · exact B819999
  · exact B820003
  · exact B820007
  · exact B820011
  · exact B820015
  · exact B820019
  · exact B820023
  · exact B820027
  · exact B820031
  · exact B820035
  · exact B820039
  · exact B820043
  · exact B820047
  · exact B820051
  · exact B820055
  · exact B820059
  · exact B820063
  · exact B820067
  · exact B820071
  · exact B820075
  · exact B820079
  · exact B820083
  · exact B820087
  · exact B820091
  · exact B820095
  · exact B820099
  · exact B820103
  · exact B820107
  · exact B820111
  · exact B820115
  · exact B820119
  · exact B820123
  · exact B820127
  · exact B820131
  · exact B820135
  · exact B820139
  · exact B820143
  · exact B820147
  · exact B820151
  · exact B820155
  · exact B820159
  · exact B820163
  · exact B820167
  · exact B820171
  · exact B820175
  · exact B820179
  · exact B820183
  · exact B820187
  · exact B820191
  · exact B820195
  · exact B820199
  · exact B820203
  · exact B820207
  · exact B820211
  · exact B820215
  · exact B820219
  · exact B820223
  · exact B820227
  · exact B820231
  · exact B820235
  · exact B820239
  · exact B820243
  · exact B820247
  · exact B820251
  · exact B820255
  · exact B820259
  · exact B820263
  · exact B820267
  · exact B820271
  · exact B820275
  · exact B820279
  · exact B820283
  · exact B820287
  · exact B820291
  · exact B820295
  · exact B820299
  · exact B820303
  · exact B820307
  · exact B820311
  · exact B820315
  · exact B820319
  · exact B820323
  · exact B820327
  · exact B820331
  · exact B820335
  · exact B820339
  · exact B820343
  · exact B820347
  · exact B820351
  · exact B820355
  · exact B820359
  · exact B820363
  · exact B820367
  · exact B820371
  · exact B820375
  · exact B820379
  · exact B820383
  · exact B820387
  · exact B820391
  · exact B820395
  · exact B820399
  · exact B820403
  · exact B820407
  · exact B820411
  · exact B820415
  · exact B820419
  · exact B820423
  · exact B820427
  · exact B820431
  · exact B820435
  · exact B820439
  · exact B820443
  · exact B820447
  · exact B820451
  · exact B820455
  · exact B820459
  · exact B820463
  · exact B820467
  · exact B820471
  · exact B820475
  · exact B820479
  · exact B820483
  · exact B820487
  · exact B820491
  · exact B820495
  · exact B820499
  · exact B820503
  · exact B820507
  · exact B820511
  · exact B820515
  · exact B820519
  · exact B820523
  · exact B820527
  · exact B820531
  · exact B820535
  · exact B820539
  · exact B820543
  · exact B820547
  · exact B820551
  · exact B820555
  · exact B820559
  · exact B820563
  · exact B820567
  · exact B820571
  · exact B820575
  · exact B820579
  · exact B820583
  · exact B820587
  · exact B820591
  · exact B820595
  · exact B820599
  · exact B820603
  · exact B820607
  · exact B820611
  · exact B820615
  · exact B820619
  · exact B820623
  · exact B820627
  · exact B820631
  · exact B820635
  · exact B820639
  · exact B820643
  · exact B820647
  · exact B820651
  · exact B820655
  · exact B820659
  · exact B820663
  · exact B820667
  · exact B820671
  · exact B820675
  · exact B820679
  · exact B820683
  · exact B820687
  · exact B820691
  · exact B820695
  · exact B820699
  · exact B820703
  · exact B820707
  · exact B820711
  · exact B820715
  · exact B820719
  · exact B820723
  · exact B820727
  · exact B820731
  · exact B820735
  · exact B820739
  · exact B820743
  · exact B820747
  · exact B820751
  · exact B820755
  · exact B820759
  · exact B820763
  · exact B820767
  · exact B820771
  · exact B820775
  · exact B820779
  · exact B820783
  · exact B820787
  · exact B820791
  · exact B820795
  · exact B820799
  · exact B820803
  · exact B820807
  · exact B820811
  · exact B820815
  · exact B820819
  · exact B820823
  · exact B820827
  · exact B820831
  · exact B820835
  · exact B820839
  · exact B820843
  · exact B820847
  · exact B820851
  · exact B820855
  · exact B820859
  · exact B820863
  · exact B820867
  · exact B820871
  · exact B820875
  · exact B820879
  · exact B820883
  · exact B820887
  · exact B820891
  · exact B820895
  · exact B820899
  · exact B820903
  · exact B820907
  · exact B820911
  · exact B820915
  · exact B820919
  · exact B820923
  · exact B820927
  · exact B820931
  · exact B820935
  · exact B820939
  · exact B820943
  · exact B820947
  · exact B820951
  · exact B820955
  · exact B820959
  · exact B820963
  · exact B820967
  · exact B820971
  · exact B820975
  · exact B820979
  · exact B820983
  · exact B820987
  · exact B820991
  · exact B820995
  · exact B820999
  · exact B821003
  · exact B821007
  · exact B821011
  · exact B821015
  · exact B821019
  · exact B821023
  · exact B821027
  · exact B821031
  · exact B821035
  · exact B821039
  · exact B821043
  · exact B821047
  · exact B821051
  · exact B821055
  · exact B821059
  · exact B821063
  · exact B821067
  · exact B821071
  · exact B821075
  · exact B821079
  · exact B821083
  · exact B821087
  · exact B821091
  · exact B821095
  · exact B821099
  · exact B821103
  · exact B821107
  · exact B821111
  · exact B821115
  · exact B821119
  · exact B821123
  · exact B821127
  · exact B821131
  · exact B821135
  · exact B821139
  · exact B821143

theorem C1 (j : ℕ) (h1 : 205286 ≤ j) (h2 : j ≤ 205586) : Blo 818347 (4 * j + 3) := by
  interval_cases j
  · exact B821147
  · exact B821151
  · exact B821155
  · exact B821159
  · exact B821163
  · exact B821167
  · exact B821171
  · exact B821175
  · exact B821179
  · exact B821183
  · exact B821187
  · exact B821191
  · exact B821195
  · exact B821199
  · exact B821203
  · exact B821207
  · exact B821211
  · exact B821215
  · exact B821219
  · exact B821223
  · exact B821227
  · exact B821231
  · exact B821235
  · exact B821239
  · exact B821243
  · exact B821247
  · exact B821251
  · exact B821255
  · exact B821259
  · exact B821263
  · exact B821267
  · exact B821271
  · exact B821275
  · exact B821279
  · exact B821283
  · exact B821287
  · exact B821291
  · exact B821295
  · exact B821299
  · exact B821303
  · exact B821307
  · exact B821311
  · exact B821315
  · exact B821319
  · exact B821323
  · exact B821327
  · exact B821331
  · exact B821335
  · exact B821339
  · exact B821343
  · exact B821347
  · exact B821351
  · exact B821355
  · exact B821359
  · exact B821363
  · exact B821367
  · exact B821371
  · exact B821375
  · exact B821379
  · exact B821383
  · exact B821387
  · exact B821391
  · exact B821395
  · exact B821399
  · exact B821403
  · exact B821407
  · exact B821411
  · exact B821415
  · exact B821419
  · exact B821423
  · exact B821427
  · exact B821431
  · exact B821435
  · exact B821439
  · exact B821443
  · exact B821447
  · exact B821451
  · exact B821455
  · exact B821459
  · exact B821463
  · exact B821467
  · exact B821471
  · exact B821475
  · exact B821479
  · exact B821483
  · exact B821487
  · exact B821491
  · exact B821495
  · exact B821499
  · exact B821503
  · exact B821507
  · exact B821511
  · exact B821515
  · exact B821519
  · exact B821523
  · exact B821527
  · exact B821531
  · exact B821535
  · exact B821539
  · exact B821543
  · exact B821547
  · exact B821551
  · exact B821555
  · exact B821559
  · exact B821563
  · exact B821567
  · exact B821571
  · exact B821575
  · exact B821579
  · exact B821583
  · exact B821587
  · exact B821591
  · exact B821595
  · exact B821599
  · exact B821603
  · exact B821607
  · exact B821611
  · exact B821615
  · exact B821619
  · exact B821623
  · exact B821627
  · exact B821631
  · exact B821635
  · exact B821639
  · exact B821643
  · exact B821647
  · exact B821651
  · exact B821655
  · exact B821659
  · exact B821663
  · exact B821667
  · exact B821671
  · exact B821675
  · exact B821679
  · exact B821683
  · exact B821687
  · exact B821691
  · exact B821695
  · exact B821699
  · exact B821703
  · exact B821707
  · exact B821711
  · exact B821715
  · exact B821719
  · exact B821723
  · exact B821727
  · exact B821731
  · exact B821735
  · exact B821739
  · exact B821743
  · exact B821747
  · exact B821751
  · exact B821755
  · exact B821759
  · exact B821763
  · exact B821767
  · exact B821771
  · exact B821775
  · exact B821779
  · exact B821783
  · exact B821787
  · exact B821791
  · exact B821795
  · exact B821799
  · exact B821803
  · exact B821807
  · exact B821811
  · exact B821815
  · exact B821819
  · exact B821823
  · exact B821827
  · exact B821831
  · exact B821835
  · exact B821839
  · exact B821843
  · exact B821847
  · exact B821851
  · exact B821855
  · exact B821859
  · exact B821863
  · exact B821867
  · exact B821871
  · exact B821875
  · exact B821879
  · exact B821883
  · exact B821887
  · exact B821891
  · exact B821895
  · exact B821899
  · exact B821903
  · exact B821907
  · exact B821911
  · exact B821915
  · exact B821919
  · exact B821923
  · exact B821927
  · exact B821931
  · exact B821935
  · exact B821939
  · exact B821943
  · exact B821947
  · exact B821951
  · exact B821955
  · exact B821959
  · exact B821963
  · exact B821967
  · exact B821971
  · exact B821975
  · exact B821979
  · exact B821983
  · exact B821987
  · exact B821991
  · exact B821995
  · exact B821999
  · exact B822003
  · exact B822007
  · exact B822011
  · exact B822015
  · exact B822019
  · exact B822023
  · exact B822027
  · exact B822031
  · exact B822035
  · exact B822039
  · exact B822043
  · exact B822047
  · exact B822051
  · exact B822055
  · exact B822059
  · exact B822063
  · exact B822067
  · exact B822071
  · exact B822075
  · exact B822079
  · exact B822083
  · exact B822087
  · exact B822091
  · exact B822095
  · exact B822099
  · exact B822103
  · exact B822107
  · exact B822111
  · exact B822115
  · exact B822119
  · exact B822123
  · exact B822127
  · exact B822131
  · exact B822135
  · exact B822139
  · exact B822143
  · exact B822147
  · exact B822151
  · exact B822155
  · exact B822159
  · exact B822163
  · exact B822167
  · exact B822171
  · exact B822175
  · exact B822179
  · exact B822183
  · exact B822187
  · exact B822191
  · exact B822195
  · exact B822199
  · exact B822203
  · exact B822207
  · exact B822211
  · exact B822215
  · exact B822219
  · exact B822223
  · exact B822227
  · exact B822231
  · exact B822235
  · exact B822239
  · exact B822243
  · exact B822247
  · exact B822251
  · exact B822255
  · exact B822259
  · exact B822263
  · exact B822267
  · exact B822271
  · exact B822275
  · exact B822279
  · exact B822283
  · exact B822287
  · exact B822291
  · exact B822295
  · exact B822299
  · exact B822303
  · exact B822307
  · exact B822311
  · exact B822315
  · exact B822319
  · exact B822323
  · exact B822327
  · exact B822331
  · exact B822335
  · exact B822339
  · exact B822343
  · exact B822347

theorem solution (m : ℕ) (hlo : 818347 ≤ m) (hhi : m ≤ 822347) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 204586 ≤ j := by omega
    have hj2 : j ≤ 205586 := by omega
    have hb : Blo 818347 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 205286 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
