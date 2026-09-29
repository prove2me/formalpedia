-- Prove2me | solution 1 for syracuse_descends_range_1275956_1277956
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:30.722301+00:00
-- url     : https://prove2.me/submissions/71a8842b-ac74-4d20-be24-b6815fbc21b8

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


theorem B1916933 : Blo 1275956 1916933 := bbase (se 4 (by rfl) ⟨179712, by rfl⟩ : syracuseStep 1916933 = 359425) (by norm_num)
theorem B1638409 : Blo 1275956 1638409 := bbase (se 2 (by rfl) ⟨614403, by rfl⟩ : syracuseStep 1638409 = 1228807) (by norm_num)
theorem B4849733 : Blo 1275956 4849733 := bbase (se 4 (by rfl) ⟨454662, by rfl⟩ : syracuseStep 4849733 = 909325) (by norm_num)
theorem B2154613 : Blo 1275956 2154613 := bbase (se 5 (by rfl) ⟨100997, by rfl⟩ : syracuseStep 2154613 = 201995) (by norm_num)
theorem B2424973 : Blo 1275956 2424973 := bbase (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) (by norm_num)
theorem B6463637 : Blo 1275956 6463637 := bbase (se 6 (by rfl) ⟨151491, by rfl⟩ : syracuseStep 6463637 = 302983) (by norm_num)
theorem B1818821 : Blo 1275956 1818821 := bbase (se 4 (by rfl) ⟨170514, by rfl⟩ : syracuseStep 1818821 = 341029) (by norm_num)
theorem B2154701 : Blo 1275956 2154701 := bbase (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) (by norm_num)
theorem B1638625 : Blo 1275956 1638625 := bbase (se 2 (by rfl) ⟨614484, by rfl⟩ : syracuseStep 1638625 = 1228969) (by norm_num)
theorem B2728181 : Blo 1275956 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B4309253 : Blo 1275956 4309253 := bbase (se 4 (by rfl) ⟨403992, by rfl⟩ : syracuseStep 4309253 = 807985) (by norm_num)
theorem B1941781 : Blo 1275956 1941781 := bbase (se 6 (by rfl) ⟨45510, by rfl⟩ : syracuseStep 1941781 = 91021) (by norm_num)
theorem B2425133 : Blo 1275956 2425133 := bbase (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) (by norm_num)
theorem B2302277 : Blo 1275956 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B2154829 : Blo 1275956 2154829 := bbase (se 3 (by rfl) ⟨404030, by rfl⟩ : syracuseStep 2154829 = 808061) (by norm_num)
theorem B2154917 : Blo 1275956 2154917 := bbase (se 4 (by rfl) ⟨202023, by rfl⟩ : syracuseStep 2154917 = 404047) (by norm_num)
theorem B2425277 : Blo 1275956 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B8176085 : Blo 1275956 8176085 := bbase (se 7 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 8176085 = 191627) (by norm_num)
theorem B2302445 : Blo 1275956 2302445 := bbase (se 3 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 2302445 = 863417) (by norm_num)
theorem B6644213 : Blo 1275956 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B2155045 : Blo 1275956 2155045 := bbase (se 4 (by rfl) ⟨202035, by rfl⟩ : syracuseStep 2155045 = 404071) (by norm_num)
theorem B2155133 : Blo 1275956 2155133 := bbase (se 3 (by rfl) ⟨404087, by rfl⟩ : syracuseStep 2155133 = 808175) (by norm_num)
theorem B2589349 : Blo 1275956 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B4309685 : Blo 1275956 4309685 := bbase (se 5 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 4309685 = 404033) (by norm_num)
theorem B3637973 : Blo 1275956 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B2425565 : Blo 1275956 2425565 := bbase (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) (by norm_num)
theorem B2155261 : Blo 1275956 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B2155349 : Blo 1275956 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B2425717 : Blo 1275956 2425717 := bbase (se 5 (by rfl) ⟨113705, by rfl⟩ : syracuseStep 2425717 = 227411) (by norm_num)
theorem B2155477 : Blo 1275956 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B2155565 : Blo 1275956 2155565 := bbase (se 3 (by rfl) ⟨404168, by rfl⟩ : syracuseStep 2155565 = 808337) (by norm_num)
theorem B1614917 : Blo 1275956 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B4310117 : Blo 1275956 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B2729069 : Blo 1275956 2729069 := bbase (se 3 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 2729069 = 1023401) (by norm_num)
theorem B1614973 : Blo 1275956 1614973 := bbase (se 3 (by rfl) ⟨302807, by rfl⟩ : syracuseStep 1614973 = 605615) (by norm_num)
theorem B2426021 : Blo 1275956 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B2155693 : Blo 1275956 2155693 := bbase (se 3 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 2155693 = 808385) (by norm_num)
theorem B3933365 : Blo 1275956 3933365 := bbase (se 5 (by rfl) ⟨184376, by rfl⟩ : syracuseStep 3933365 = 368753) (by norm_num)
theorem B1615069 : Blo 1275956 1615069 := bbase (se 3 (by rfl) ⟨302825, by rfl⟩ : syracuseStep 1615069 = 605651) (by norm_num)
theorem B2729189 : Blo 1275956 2729189 := bbase (se 4 (by rfl) ⟨255861, by rfl⟩ : syracuseStep 2729189 = 511723) (by norm_num)
theorem B2155781 : Blo 1275956 2155781 := bbase (se 4 (by rfl) ⟨202104, by rfl⟩ : syracuseStep 2155781 = 404209) (by norm_num)
theorem B3638645 : Blo 1275956 3638645 := bbase (se 5 (by rfl) ⟨170561, by rfl⟩ : syracuseStep 3638645 = 341123) (by norm_num)
theorem B2155909 : Blo 1275956 2155909 := bbase (se 4 (by rfl) ⟨202116, by rfl⟩ : syracuseStep 2155909 = 404233) (by norm_num)
theorem B1615241 : Blo 1275956 1615241 := bbase (se 2 (by rfl) ⟨605715, by rfl⟩ : syracuseStep 1615241 = 1211431) (by norm_num)
theorem B6464933 : Blo 1275956 6464933 := bbase (se 4 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 6464933 = 1212175) (by norm_num)
theorem B7267765 : Blo 1275956 7267765 := bbase (se 5 (by rfl) ⟨340676, by rfl⟩ : syracuseStep 7267765 = 681353) (by norm_num)
theorem B1615297 : Blo 1275956 1615297 := bbase (se 2 (by rfl) ⟨605736, by rfl⟩ : syracuseStep 1615297 = 1211473) (by norm_num)
theorem B2155997 : Blo 1275956 2155997 := bbase (se 3 (by rfl) ⟨404249, by rfl⟩ : syracuseStep 2155997 = 808499) (by norm_num)
theorem B4310549 : Blo 1275956 4310549 := bbase (se 6 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 4310549 = 202057) (by norm_num)
theorem B1615393 : Blo 1275956 1615393 := bbase (se 2 (by rfl) ⟨605772, by rfl⟩ : syracuseStep 1615393 = 1211545) (by norm_num)
theorem B5678629 : Blo 1275956 5678629 := bbase (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) (by norm_num)
theorem B2156125 : Blo 1275956 2156125 := bbase (se 3 (by rfl) ⟨404273, by rfl⟩ : syracuseStep 2156125 = 808547) (by norm_num)
theorem B3688037 : Blo 1275956 3688037 := bbase (se 4 (by rfl) ⟨345753, by rfl⟩ : syracuseStep 3688037 = 691507) (by norm_num)
theorem B2762381 : Blo 1275956 2762381 := bbase (se 3 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 2762381 = 1035893) (by norm_num)
theorem B1312405 : Blo 1275956 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B5457557 : Blo 1275956 5457557 := bbase (se 6 (by rfl) ⟨127911, by rfl⟩ : syracuseStep 5457557 = 255823) (by norm_num)
theorem B9701045 : Blo 1275956 9701045 := bbase (se 5 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 9701045 = 909473) (by norm_num)
theorem B2156213 : Blo 1275956 2156213 := bbase (se 5 (by rfl) ⟨101072, by rfl⟩ : syracuseStep 2156213 = 202145) (by norm_num)
theorem B1615565 : Blo 1275956 1615565 := bbase (se 3 (by rfl) ⟨302918, by rfl⟩ : syracuseStep 1615565 = 605837) (by norm_num)
theorem B8406773 : Blo 1275956 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B1615621 : Blo 1275956 1615621 := bbase (se 4 (by rfl) ⟨151464, by rfl⟩ : syracuseStep 1615621 = 302929) (by norm_num)
theorem B3639077 : Blo 1275956 3639077 := bbase (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) (by norm_num)
theorem B2590517 : Blo 1275956 2590517 := bbase (se 5 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 2590517 = 242861) (by norm_num)
theorem B2156341 : Blo 1275956 2156341 := bbase (se 5 (by rfl) ⟨101078, by rfl⟩ : syracuseStep 2156341 = 202157) (by norm_num)
theorem B1435477 : Blo 1275956 1435477 := bbase (se 9 (by rfl) ⟨4205, by rfl⟩ : syracuseStep 1435477 = 8411) (by norm_num)
theorem B1615717 : Blo 1275956 1615717 := bbase (se 4 (by rfl) ⟨151473, by rfl⟩ : syracuseStep 1615717 = 302947) (by norm_num)
theorem B1435513 : Blo 1275956 1435513 := bbase (se 2 (by rfl) ⟨538317, by rfl⟩ : syracuseStep 1435513 = 1076635) (by norm_num)
theorem B2156429 : Blo 1275956 2156429 := bbase (se 3 (by rfl) ⟨404330, by rfl⟩ : syracuseStep 2156429 = 808661) (by norm_num)
theorem B1435549 : Blo 1275956 1435549 := bbase (se 3 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 1435549 = 538331) (by norm_num)
theorem B2762669 : Blo 1275956 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B1312697 : Blo 1275956 1312697 := bbase (se 2 (by rfl) ⟨492261, by rfl⟩ : syracuseStep 1312697 = 984523) (by norm_num)
theorem B1435585 : Blo 1275956 1435585 := bbase (se 2 (by rfl) ⟨538344, by rfl⟩ : syracuseStep 1435585 = 1076689) (by norm_num)
theorem B4310981 : Blo 1275956 4310981 := bbase (se 4 (by rfl) ⟨404154, by rfl⟩ : syracuseStep 4310981 = 808309) (by norm_num)
theorem B1435621 : Blo 1275956 1435621 := bbase (se 4 (by rfl) ⟨134589, by rfl⟩ : syracuseStep 1435621 = 269179) (by norm_num)
theorem B1435657 : Blo 1275956 1435657 := bbase (se 2 (by rfl) ⟨538371, by rfl⟩ : syracuseStep 1435657 = 1076743) (by norm_num)
theorem B1615889 : Blo 1275956 1615889 := bbase (se 2 (by rfl) ⟨605958, by rfl⟩ : syracuseStep 1615889 = 1211917) (by norm_num)
theorem B1435693 : Blo 1275956 1435693 := bbase (se 3 (by rfl) ⟨269192, by rfl⟩ : syracuseStep 1435693 = 538385) (by norm_num)
theorem B1615945 : Blo 1275956 1615945 := bbase (se 2 (by rfl) ⟨605979, by rfl⟩ : syracuseStep 1615945 = 1211959) (by norm_num)
theorem B1534025 : Blo 1275956 1534025 := bbase (se 2 (by rfl) ⟨575259, by rfl⟩ : syracuseStep 1534025 = 1150519) (by norm_num)
theorem B1435729 : Blo 1275956 1435729 := bbase (se 2 (by rfl) ⟨538398, by rfl⟩ : syracuseStep 1435729 = 1076797) (by norm_num)
theorem B9693269 : Blo 1275956 9693269 := bbase (se 8 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 9693269 = 113593) (by norm_num)
theorem B1435765 : Blo 1275956 1435765 := bbase (se 5 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 1435765 = 134603) (by norm_num)
theorem B4851845 : Blo 1275956 4851845 := bbase (se 4 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 4851845 = 909721) (by norm_num)
theorem B10905749 : Blo 1275956 10905749 := bbase (se 6 (by rfl) ⟨255603, by rfl⟩ : syracuseStep 10905749 = 511207) (by norm_num)
theorem B1435801 : Blo 1275956 1435801 := bbase (se 2 (by rfl) ⟨538425, by rfl⟩ : syracuseStep 1435801 = 1076851) (by norm_num)
theorem B1616041 : Blo 1275956 1616041 := bbase (se 2 (by rfl) ⟨606015, by rfl⟩ : syracuseStep 1616041 = 1212031) (by norm_num)
theorem B1435837 : Blo 1275956 1435837 := bbase (se 3 (by rfl) ⟨269219, by rfl⟩ : syracuseStep 1435837 = 538439) (by norm_num)
theorem B1435873 : Blo 1275956 1435873 := bbase (se 2 (by rfl) ⟨538452, by rfl⟩ : syracuseStep 1435873 = 1076905) (by norm_num)
theorem B1435909 : Blo 1275956 1435909 := bbase (se 4 (by rfl) ⟨134616, by rfl⟩ : syracuseStep 1435909 = 269233) (by norm_num)
theorem B1435945 : Blo 1275956 1435945 := bbase (se 2 (by rfl) ⟨538479, by rfl⟩ : syracuseStep 1435945 = 1076959) (by norm_num)
theorem B3451189 : Blo 1275956 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B1435981 : Blo 1275956 1435981 := bbase (se 3 (by rfl) ⟨269246, by rfl⟩ : syracuseStep 1435981 = 538493) (by norm_num)
theorem B1616213 : Blo 1275956 1616213 := bbase (se 10 (by rfl) ⟨2367, by rfl⟩ : syracuseStep 1616213 = 4735) (by norm_num)
theorem B1436017 : Blo 1275956 1436017 := bbase (se 2 (by rfl) ⟨538506, by rfl⟩ : syracuseStep 1436017 = 1077013) (by norm_num)
theorem B3451253 : Blo 1275956 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B4311413 : Blo 1275956 4311413 := bbase (se 5 (by rfl) ⟨202097, by rfl⟩ : syracuseStep 4311413 = 404195) (by norm_num)
theorem B3230077 : Blo 1275956 3230077 := bbase (se 3 (by rfl) ⟨605639, by rfl⟩ : syracuseStep 3230077 = 1211279) (by norm_num)
theorem B1616269 : Blo 1275956 1616269 := bbase (se 3 (by rfl) ⟨303050, by rfl⟩ : syracuseStep 1616269 = 606101) (by norm_num)
theorem B1436053 : Blo 1275956 1436053 := bbase (se 6 (by rfl) ⟨33657, by rfl⟩ : syracuseStep 1436053 = 67315) (by norm_num)
theorem B4852133 : Blo 1275956 4852133 := bbase (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) (by norm_num)
theorem B2992565 : Blo 1275956 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B1436089 : Blo 1275956 1436089 := bbase (se 2 (by rfl) ⟨538533, by rfl⟩ : syracuseStep 1436089 = 1077067) (by norm_num)
theorem B1436125 : Blo 1275956 1436125 := bbase (se 3 (by rfl) ⟨269273, by rfl⟩ : syracuseStep 1436125 = 538547) (by norm_num)
theorem B3230189 : Blo 1275956 3230189 := bbase (se 3 (by rfl) ⟨605660, by rfl⟩ : syracuseStep 3230189 = 1211321) (by norm_num)
theorem B2910701 : Blo 1275956 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B1616365 : Blo 1275956 1616365 := bbase (se 3 (by rfl) ⟨303068, by rfl⟩ : syracuseStep 1616365 = 606137) (by norm_num)
theorem B1436161 : Blo 1275956 1436161 := bbase (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) (by norm_num)
theorem B1436197 : Blo 1275956 1436197 := bbase (se 4 (by rfl) ⟨134643, by rfl⟩ : syracuseStep 1436197 = 269287) (by norm_num)
theorem B1436233 : Blo 1275956 1436233 := bbase (se 2 (by rfl) ⟨538587, by rfl⟩ : syracuseStep 1436233 = 1077175) (by norm_num)
theorem B2910829 : Blo 1275956 2910829 := bbase (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) (by norm_num)
theorem B1436269 : Blo 1275956 1436269 := bbase (se 3 (by rfl) ⟨269300, by rfl⟩ : syracuseStep 1436269 = 538601) (by norm_num)
theorem B3066493 : Blo 1275956 3066493 := bbase (se 3 (by rfl) ⟨574967, by rfl⟩ : syracuseStep 3066493 = 1149935) (by norm_num)
theorem B3885701 : Blo 1275956 3885701 := bbase (se 4 (by rfl) ⟨364284, by rfl⟩ : syracuseStep 3885701 = 728569) (by norm_num)
theorem B1436305 : Blo 1275956 1436305 := bbase (se 2 (by rfl) ⟨538614, by rfl⟩ : syracuseStep 1436305 = 1077229) (by norm_num)
theorem B1616537 : Blo 1275956 1616537 := bbase (se 2 (by rfl) ⟨606201, by rfl⟩ : syracuseStep 1616537 = 1212403) (by norm_num)
theorem B1534621 : Blo 1275956 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B3230381 : Blo 1275956 3230381 := bbase (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) (by norm_num)
theorem B1436341 : Blo 1275956 1436341 := bbase (se 5 (by rfl) ⟨67328, by rfl⟩ : syracuseStep 1436341 = 134657) (by norm_num)
theorem B6466229 : Blo 1275956 6466229 := bbase (se 5 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 6466229 = 606209) (by norm_num)
theorem B1616593 : Blo 1275956 1616593 := bbase (se 2 (by rfl) ⟨606222, by rfl⟩ : syracuseStep 1616593 = 1212445) (by norm_num)
theorem B1436377 : Blo 1275956 1436377 := bbase (se 2 (by rfl) ⟨538641, by rfl⟩ : syracuseStep 1436377 = 1077283) (by norm_num)
theorem B1436413 : Blo 1275956 1436413 := bbase (se 3 (by rfl) ⟨269327, by rfl⟩ : syracuseStep 1436413 = 538655) (by norm_num)
theorem B1534717 : Blo 1275956 1534717 := bbase (se 3 (by rfl) ⟨287759, by rfl⟩ : syracuseStep 1534717 = 575519) (by norm_num)
theorem B1436449 : Blo 1275956 1436449 := bbase (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) (by norm_num)
theorem B4311845 : Blo 1275956 4311845 := bbase (se 4 (by rfl) ⟨404235, by rfl⟩ : syracuseStep 4311845 = 808471) (by norm_num)
theorem B1616689 : Blo 1275956 1616689 := bbase (se 2 (by rfl) ⟨606258, by rfl⟩ : syracuseStep 1616689 = 1212517) (by norm_num)
theorem B1362749 : Blo 1275956 1362749 := bbase (se 3 (by rfl) ⟨255515, by rfl⟩ : syracuseStep 1362749 = 511031) (by norm_num)
theorem B1436485 : Blo 1275956 1436485 := bbase (se 4 (by rfl) ⟨134670, by rfl⟩ : syracuseStep 1436485 = 269341) (by norm_num)
theorem B7875413 : Blo 1275956 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B1436521 : Blo 1275956 1436521 := bbase (se 2 (by rfl) ⟨538695, by rfl⟩ : syracuseStep 1436521 = 1077391) (by norm_num)
theorem B1436557 : Blo 1275956 1436557 := bbase (se 3 (by rfl) ⟨269354, by rfl⟩ : syracuseStep 1436557 = 538709) (by norm_num)
theorem B6138773 : Blo 1275956 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B5827493 : Blo 1275956 5827493 := bbase (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) (by norm_num)
theorem B1436593 : Blo 1275956 1436593 := bbase (se 2 (by rfl) ⟨538722, by rfl⟩ : syracuseStep 1436593 = 1077445) (by norm_num)
theorem B1436629 : Blo 1275956 1436629 := bbase (se 7 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 1436629 = 33671) (by norm_num)
theorem B1616861 : Blo 1275956 1616861 := bbase (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) (by norm_num)
theorem B1436665 : Blo 1275956 1436665 := bbase (se 2 (by rfl) ⟨538749, by rfl⟩ : syracuseStep 1436665 = 1077499) (by norm_num)
theorem B3230725 : Blo 1275956 3230725 := bbase (se 4 (by rfl) ⟨302880, by rfl⟩ : syracuseStep 3230725 = 605761) (by norm_num)
theorem B14740501 : Blo 1275956 14740501 := bbase (se 6 (by rfl) ⟨345480, by rfl⟩ : syracuseStep 14740501 = 690961) (by norm_num)
theorem B1616917 : Blo 1275956 1616917 := bbase (se 6 (by rfl) ⟨37896, by rfl⟩ : syracuseStep 1616917 = 75793) (by norm_num)
theorem B1436701 : Blo 1275956 1436701 := bbase (se 3 (by rfl) ⟨269381, by rfl⟩ : syracuseStep 1436701 = 538763) (by norm_num)
theorem B4148261 : Blo 1275956 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B1362997 : Blo 1275956 1362997 := bbase (se 5 (by rfl) ⟨63890, by rfl⟩ : syracuseStep 1362997 = 127781) (by norm_num)
theorem B1436737 : Blo 1275956 1436737 := bbase (se 2 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 1436737 = 1077553) (by norm_num)
theorem B1436773 : Blo 1275956 1436773 := bbase (se 4 (by rfl) ⟨134697, by rfl⟩ : syracuseStep 1436773 = 269395) (by norm_num)
theorem B3230837 : Blo 1275956 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B1617013 : Blo 1275956 1617013 := bbase (se 5 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 1617013 = 151595) (by norm_num)
theorem B1436809 : Blo 1275956 1436809 := bbase (se 2 (by rfl) ⟨538803, by rfl⟩ : syracuseStep 1436809 = 1077607) (by norm_num)
theorem B1436845 : Blo 1275956 1436845 := bbase (se 3 (by rfl) ⟨269408, by rfl⟩ : syracuseStep 1436845 = 538817) (by norm_num)
theorem B1436881 : Blo 1275956 1436881 := bbase (se 2 (by rfl) ⟨538830, by rfl⟩ : syracuseStep 1436881 = 1077661) (by norm_num)
theorem B4312277 : Blo 1275956 4312277 := bbase (se 7 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 4312277 = 101069) (by norm_num)
theorem B3067109 : Blo 1275956 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B2911477 : Blo 1275956 2911477 := bbase (se 5 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 2911477 = 272951) (by norm_num)
theorem B1436917 : Blo 1275956 1436917 := bbase (se 5 (by rfl) ⟨67355, by rfl⟩ : syracuseStep 1436917 = 134711) (by norm_num)
theorem B1436953 : Blo 1275956 1436953 := bbase (se 2 (by rfl) ⟨538857, by rfl⟩ : syracuseStep 1436953 = 1077715) (by norm_num)
theorem B3067165 : Blo 1275956 3067165 := bbase (se 3 (by rfl) ⟨575093, by rfl⟩ : syracuseStep 3067165 = 1150187) (by norm_num)
theorem B1617185 : Blo 1275956 1617185 := bbase (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) (by norm_num)
theorem B3108149 : Blo 1275956 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B3231029 : Blo 1275956 3231029 := bbase (se 5 (by rfl) ⟨151454, by rfl⟩ : syracuseStep 3231029 = 302909) (by norm_num)
theorem B1436989 : Blo 1275956 1436989 := bbase (se 3 (by rfl) ⟨269435, by rfl⟩ : syracuseStep 1436989 = 538871) (by norm_num)
theorem B1617241 : Blo 1275956 1617241 := bbase (se 2 (by rfl) ⟨606465, by rfl⟩ : syracuseStep 1617241 = 1212931) (by norm_num)
theorem B1437025 : Blo 1275956 1437025 := bbase (se 2 (by rfl) ⟨538884, by rfl⟩ : syracuseStep 1437025 = 1077769) (by norm_num)
theorem B7269749 : Blo 1275956 7269749 := bbase (se 5 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 7269749 = 681539) (by norm_num)
theorem B1437061 : Blo 1275956 1437061 := bbase (se 4 (by rfl) ⟨134724, by rfl⟩ : syracuseStep 1437061 = 269449) (by norm_num)
theorem B4091285 : Blo 1275956 4091285 := bbase (se 6 (by rfl) ⟨95889, by rfl⟩ : syracuseStep 4091285 = 191779) (by norm_num)
theorem B1437097 : Blo 1275956 1437097 := bbase (se 2 (by rfl) ⟨538911, by rfl⟩ : syracuseStep 1437097 = 1077823) (by norm_num)
theorem B1617337 : Blo 1275956 1617337 := bbase (se 2 (by rfl) ⟨606501, by rfl⟩ : syracuseStep 1617337 = 1213003) (by norm_num)
theorem B1437133 : Blo 1275956 1437133 := bbase (se 3 (by rfl) ⟨269462, by rfl⟩ : syracuseStep 1437133 = 538925) (by norm_num)
theorem B2215397 : Blo 1275956 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B1363441 : Blo 1275956 1363441 := bbase (se 2 (by rfl) ⟨511290, by rfl⟩ : syracuseStep 1363441 = 1022581) (by norm_num)
theorem B1437169 : Blo 1275956 1437169 := bbase (se 2 (by rfl) ⟨538938, by rfl⟩ : syracuseStep 1437169 = 1077877) (by norm_num)
theorem B1437205 : Blo 1275956 1437205 := bbase (se 6 (by rfl) ⟨33684, by rfl⟩ : syracuseStep 1437205 = 67369) (by norm_num)
theorem B1330709 : Blo 1275956 1330709 := bbase (se 6 (by rfl) ⟨31188, by rfl⟩ : syracuseStep 1330709 = 62377) (by norm_num)
theorem B1363501 : Blo 1275956 1363501 := bbase (se 3 (by rfl) ⟨255656, by rfl⟩ : syracuseStep 1363501 = 511313) (by norm_num)
theorem B1437241 : Blo 1275956 1437241 := bbase (se 2 (by rfl) ⟨538965, by rfl⟩ : syracuseStep 1437241 = 1077931) (by norm_num)
theorem B1437277 : Blo 1275956 1437277 := bbase (se 3 (by rfl) ⟨269489, by rfl⟩ : syracuseStep 1437277 = 538979) (by norm_num)
theorem B2764397 : Blo 1275956 2764397 := bbase (se 3 (by rfl) ⟨518324, by rfl⟩ : syracuseStep 2764397 = 1036649) (by norm_num)
theorem B12267125 : Blo 1275956 12267125 := bbase (se 5 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 12267125 = 1150043) (by norm_num)
theorem B2870909 : Blo 1275956 2870909 := bbase (se 3 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 2870909 = 1076591) (by norm_num)
theorem B1437313 : Blo 1275956 1437313 := bbase (se 2 (by rfl) ⟨538992, by rfl⟩ : syracuseStep 1437313 = 1077985) (by norm_num)
theorem B4312709 : Blo 1275956 4312709 := bbase (se 4 (by rfl) ⟨404316, by rfl⟩ : syracuseStep 4312709 = 808633) (by norm_num)
theorem B3231373 : Blo 1275956 3231373 := bbase (se 3 (by rfl) ⟨605882, by rfl⟩ : syracuseStep 3231373 = 1211765) (by norm_num)
theorem B1437349 : Blo 1275956 1437349 := bbase (se 4 (by rfl) ⟨134751, by rfl⟩ : syracuseStep 1437349 = 269503) (by norm_num)
theorem B2870981 : Blo 1275956 2870981 := bbase (se 4 (by rfl) ⟨269154, by rfl⟩ : syracuseStep 2870981 = 538309) (by norm_num)
theorem B1437385 : Blo 1275956 1437385 := bbase (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) (by norm_num)
theorem B1437421 : Blo 1275956 1437421 := bbase (se 3 (by rfl) ⟨269516, by rfl⟩ : syracuseStep 1437421 = 539033) (by norm_num)
theorem B3231485 : Blo 1275956 3231485 := bbase (se 3 (by rfl) ⟨605903, by rfl⟩ : syracuseStep 3231485 = 1211807) (by norm_num)
theorem B2871053 : Blo 1275956 2871053 := bbase (se 3 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 2871053 = 1076645) (by norm_num)
theorem B1437457 : Blo 1275956 1437457 := bbase (se 2 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 1437457 = 1078093) (by norm_num)
theorem B1437493 : Blo 1275956 1437493 := bbase (se 5 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 1437493 = 134765) (by norm_num)
theorem B2871125 : Blo 1275956 2871125 := bbase (se 9 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 2871125 = 16823) (by norm_num)
theorem B1437529 : Blo 1275956 1437529 := bbase (se 2 (by rfl) ⟨539073, by rfl⟩ : syracuseStep 1437529 = 1078147) (by norm_num)
theorem B1363817 : Blo 1275956 1363817 := bbase (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) (by norm_num)
theorem B1437565 : Blo 1275956 1437565 := bbase (se 3 (by rfl) ⟨269543, by rfl⟩ : syracuseStep 1437565 = 539087) (by norm_num)
theorem B9834389 : Blo 1275956 9834389 := bbase (se 6 (by rfl) ⟨230493, by rfl⟩ : syracuseStep 9834389 = 460987) (by norm_num)
theorem B2871197 : Blo 1275956 2871197 := bbase (se 3 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 2871197 = 1076699) (by norm_num)
theorem B1437601 : Blo 1275956 1437601 := bbase (se 2 (by rfl) ⟨539100, by rfl⟩ : syracuseStep 1437601 = 1078201) (by norm_num)
theorem B10350517 : Blo 1275956 10350517 := bbase (se 5 (by rfl) ⟨485180, by rfl⟩ : syracuseStep 10350517 = 970361) (by norm_num)
theorem B3231677 : Blo 1275956 3231677 := bbase (se 3 (by rfl) ⟨605939, by rfl⟩ : syracuseStep 3231677 = 1211879) (by norm_num)
theorem B6467525 : Blo 1275956 6467525 := bbase (se 4 (by rfl) ⟨606330, by rfl⟩ : syracuseStep 6467525 = 1212661) (by norm_num)
theorem B1437637 : Blo 1275956 1437637 := bbase (se 4 (by rfl) ⟨134778, by rfl⟩ : syracuseStep 1437637 = 269557) (by norm_num)
theorem B2871269 : Blo 1275956 2871269 := bbase (se 4 (by rfl) ⟨269181, by rfl⟩ : syracuseStep 2871269 = 538363) (by norm_num)
theorem B4845541 : Blo 1275956 4845541 := bbase (se 4 (by rfl) ⟨454269, by rfl⟩ : syracuseStep 4845541 = 908539) (by norm_num)
theorem B1437673 : Blo 1275956 1437673 := bbase (se 2 (by rfl) ⟨539127, by rfl⟩ : syracuseStep 1437673 = 1078255) (by norm_num)
theorem B5451781 : Blo 1275956 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B2871341 : Blo 1275956 2871341 := bbase (se 3 (by rfl) ⟨538376, by rfl⟩ : syracuseStep 2871341 = 1076753) (by norm_num)
theorem B2871413 : Blo 1275956 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B1724557 : Blo 1275956 1724557 := bbase (se 3 (by rfl) ⟨323354, by rfl⟩ : syracuseStep 1724557 = 646709) (by norm_num)
theorem B2330797 : Blo 1275956 2330797 := bbase (se 3 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 2330797 = 874049) (by norm_num)
theorem B2871485 : Blo 1275956 2871485 := bbase (se 3 (by rfl) ⟨538403, by rfl⟩ : syracuseStep 2871485 = 1076807) (by norm_num)
theorem B2871557 : Blo 1275956 2871557 := bbase (se 4 (by rfl) ⟨269208, by rfl⟩ : syracuseStep 2871557 = 538417) (by norm_num)
theorem B3068165 : Blo 1275956 3068165 := bbase (se 4 (by rfl) ⟨287640, by rfl⟩ : syracuseStep 3068165 = 575281) (by norm_num)
theorem B2912525 : Blo 1275956 2912525 := bbase (se 3 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 2912525 = 1092197) (by norm_num)
theorem B4845845 : Blo 1275956 4845845 := bbase (se 6 (by rfl) ⟨113574, by rfl⟩ : syracuseStep 4845845 = 227149) (by norm_num)
theorem B3232021 : Blo 1275956 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B1364261 : Blo 1275956 1364261 := bbase (se 4 (by rfl) ⟨127899, by rfl⟩ : syracuseStep 1364261 = 255799) (by norm_num)
theorem B5902645 : Blo 1275956 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B2871629 : Blo 1275956 2871629 := bbase (se 3 (by rfl) ⟨538430, by rfl⟩ : syracuseStep 2871629 = 1076861) (by norm_num)
theorem B34959701 : Blo 1275956 34959701 := bbase (se 10 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 34959701 = 102421) (by norm_num)
theorem B1364321 : Blo 1275956 1364321 := bbase (se 2 (by rfl) ⟨511620, by rfl⟩ : syracuseStep 1364321 = 1023241) (by norm_num)
theorem B6459749 : Blo 1275956 6459749 := bbase (se 4 (by rfl) ⟨605601, by rfl⟩ : syracuseStep 6459749 = 1211203) (by norm_num)
theorem B3232133 : Blo 1275956 3232133 := bbase (se 4 (by rfl) ⟨303012, by rfl⟩ : syracuseStep 3232133 = 606025) (by norm_num)
theorem B2871701 : Blo 1275956 2871701 := bbase (se 6 (by rfl) ⟨67305, by rfl⟩ : syracuseStep 2871701 = 134611) (by norm_num)
theorem B4092373 : Blo 1275956 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B2871773 : Blo 1275956 2871773 := bbase (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) (by norm_num)
theorem B1364449 : Blo 1275956 1364449 := bbase (se 2 (by rfl) ⟨511668, by rfl⟩ : syracuseStep 1364449 = 1023337) (by norm_num)
theorem B2183669 : Blo 1275956 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B2871845 : Blo 1275956 2871845 := bbase (se 4 (by rfl) ⟨269235, by rfl⟩ : syracuseStep 2871845 = 538471) (by norm_num)
theorem B3232325 : Blo 1275956 3232325 := bbase (se 4 (by rfl) ⟨303030, by rfl⟩ : syracuseStep 3232325 = 606061) (by norm_num)
theorem B2183773 : Blo 1275956 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B2871917 : Blo 1275956 2871917 := bbase (se 3 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 2871917 = 1076969) (by norm_num)
theorem B3633781 : Blo 1275956 3633781 := bbase (se 5 (by rfl) ⟨170333, by rfl⟩ : syracuseStep 3633781 = 340667) (by norm_num)
theorem B2871989 : Blo 1275956 2871989 := bbase (se 5 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 2871989 = 269249) (by norm_num)
theorem B6132469 : Blo 1275956 6132469 := bbase (se 5 (by rfl) ⟨287459, by rfl⟩ : syracuseStep 6132469 = 574919) (by norm_num)
theorem B2872061 : Blo 1275956 2872061 := bbase (se 3 (by rfl) ⟨538511, by rfl⟩ : syracuseStep 2872061 = 1077023) (by norm_num)
theorem B6132485 : Blo 1275956 6132485 := bbase (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) (by norm_num)
theorem B2872133 : Blo 1275956 2872133 := bbase (se 4 (by rfl) ⟨269262, by rfl⟩ : syracuseStep 2872133 = 538525) (by norm_num)
theorem B6140789 : Blo 1275956 6140789 := bbase (se 5 (by rfl) ⟨287849, by rfl⟩ : syracuseStep 6140789 = 575699) (by norm_num)
theorem B2872205 : Blo 1275956 2872205 := bbase (se 3 (by rfl) ⟨538538, by rfl⟩ : syracuseStep 2872205 = 1077077) (by norm_num)
theorem B3232669 : Blo 1275956 3232669 := bbase (se 3 (by rfl) ⟨606125, by rfl⟩ : syracuseStep 3232669 = 1212251) (by norm_num)
theorem B2872277 : Blo 1275956 2872277 := bbase (se 7 (by rfl) ⟨33659, by rfl⟩ : syracuseStep 2872277 = 67319) (by norm_num)
theorem B3232781 : Blo 1275956 3232781 := bbase (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) (by norm_num)
theorem B2872349 : Blo 1275956 2872349 := bbase (se 3 (by rfl) ⟨538565, by rfl⟩ : syracuseStep 2872349 = 1077131) (by norm_num)
theorem B1913957 : Blo 1275956 1913957 := bbase (se 4 (by rfl) ⟨179433, by rfl⟩ : syracuseStep 1913957 = 358867) (by norm_num)
theorem B2872421 : Blo 1275956 2872421 := bbase (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) (by norm_num)
theorem B1913981 : Blo 1275956 1913981 := bbase (se 3 (by rfl) ⟨358871, by rfl⟩ : syracuseStep 1913981 = 717743) (by norm_num)
theorem B2765957 : Blo 1275956 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B1914005 : Blo 1275956 1914005 := bbase (se 6 (by rfl) ⟨44859, by rfl⟩ : syracuseStep 1914005 = 89719) (by norm_num)
theorem B1914029 : Blo 1275956 1914029 := bbase (se 3 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 1914029 = 717761) (by norm_num)
theorem B2872493 : Blo 1275956 2872493 := bbase (se 3 (by rfl) ⟨538592, by rfl⟩ : syracuseStep 2872493 = 1077185) (by norm_num)
theorem B3880133 : Blo 1275956 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B1914053 : Blo 1275956 1914053 := bbase (se 4 (by rfl) ⟨179442, by rfl⟩ : syracuseStep 1914053 = 358885) (by norm_num)
theorem B3232973 : Blo 1275956 3232973 := bbase (se 3 (by rfl) ⟨606182, by rfl⟩ : syracuseStep 3232973 = 1212365) (by norm_num)
theorem B6468821 : Blo 1275956 6468821 := bbase (se 7 (by rfl) ⟨75806, by rfl⟩ : syracuseStep 6468821 = 151613) (by norm_num)
theorem B1914077 : Blo 1275956 1914077 := bbase (se 3 (by rfl) ⟨358889, by rfl⟩ : syracuseStep 1914077 = 717779) (by norm_num)
theorem B1455341 : Blo 1275956 1455341 := bbase (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) (by norm_num)
theorem B1914101 : Blo 1275956 1914101 := bbase (se 5 (by rfl) ⟨89723, by rfl⟩ : syracuseStep 1914101 = 179447) (by norm_num)
theorem B2872565 : Blo 1275956 2872565 := bbase (se 5 (by rfl) ⟨134651, by rfl⟩ : syracuseStep 2872565 = 269303) (by norm_num)
theorem B1914125 : Blo 1275956 1914125 := bbase (se 3 (by rfl) ⟨358898, by rfl⟩ : syracuseStep 1914125 = 717797) (by norm_num)
theorem B2725157 : Blo 1275956 2725157 := bbase (se 4 (by rfl) ⟨255483, by rfl⟩ : syracuseStep 2725157 = 510967) (by norm_num)
theorem B1914149 : Blo 1275956 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B1914173 : Blo 1275956 1914173 := bbase (se 3 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 1914173 = 717815) (by norm_num)
theorem B2872637 : Blo 1275956 2872637 := bbase (se 3 (by rfl) ⟨538619, by rfl⟩ : syracuseStep 2872637 = 1077239) (by norm_num)
theorem B1914197 : Blo 1275956 1914197 := bbase (se 13 (by rfl) ⟨350, by rfl⟩ : syracuseStep 1914197 = 701) (by norm_num)
theorem B6550885 : Blo 1275956 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B1914221 : Blo 1275956 1914221 := bbase (se 3 (by rfl) ⟨358916, by rfl⟩ : syracuseStep 1914221 = 717833) (by norm_num)
theorem B3880325 : Blo 1275956 3880325 := bbase (se 4 (by rfl) ⟨363780, by rfl⟩ : syracuseStep 3880325 = 727561) (by norm_num)
theorem B1914245 : Blo 1275956 1914245 := bbase (se 4 (by rfl) ⟨179460, by rfl⟩ : syracuseStep 1914245 = 358921) (by norm_num)
theorem B2872709 : Blo 1275956 2872709 := bbase (se 4 (by rfl) ⟨269316, by rfl⟩ : syracuseStep 2872709 = 538633) (by norm_num)
theorem B2332045 : Blo 1275956 2332045 := bbase (se 3 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 2332045 = 874517) (by norm_num)
theorem B1914269 : Blo 1275956 1914269 := bbase (se 3 (by rfl) ⟨358925, by rfl⟩ : syracuseStep 1914269 = 717851) (by norm_num)
theorem B2045341 : Blo 1275956 2045341 := bbase (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) (by norm_num)
theorem B1914293 : Blo 1275956 1914293 := bbase (se 5 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 1914293 = 179465) (by norm_num)
theorem B1914317 : Blo 1275956 1914317 := bbase (se 3 (by rfl) ⟨358934, by rfl⟩ : syracuseStep 1914317 = 717869) (by norm_num)
theorem B2872781 : Blo 1275956 2872781 := bbase (se 3 (by rfl) ⟨538646, by rfl⟩ : syracuseStep 2872781 = 1077293) (by norm_num)
theorem B2184653 : Blo 1275956 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B1914341 : Blo 1275956 1914341 := bbase (se 4 (by rfl) ⟨179469, by rfl⟩ : syracuseStep 1914341 = 358939) (by norm_num)
theorem B1914365 : Blo 1275956 1914365 := bbase (se 3 (by rfl) ⟨358943, by rfl⟩ : syracuseStep 1914365 = 717887) (by norm_num)
theorem B2397701 : Blo 1275956 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B1914389 : Blo 1275956 1914389 := bbase (se 6 (by rfl) ⟨44868, by rfl⟩ : syracuseStep 1914389 = 89737) (by norm_num)
theorem B2872853 : Blo 1275956 2872853 := bbase (se 6 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 2872853 = 134665) (by norm_num)
theorem B7271957 : Blo 1275956 7271957 := bbase (se 6 (by rfl) ⟨170436, by rfl⟩ : syracuseStep 7271957 = 340873) (by norm_num)
theorem B3233317 : Blo 1275956 3233317 := bbase (se 4 (by rfl) ⟨303123, by rfl⟩ : syracuseStep 3233317 = 606247) (by norm_num)
theorem B1914413 : Blo 1275956 1914413 := bbase (se 3 (by rfl) ⟨358952, by rfl⟩ : syracuseStep 1914413 = 717905) (by norm_num)
theorem B1914437 : Blo 1275956 1914437 := bbase (se 4 (by rfl) ⟨179478, by rfl⟩ : syracuseStep 1914437 = 358957) (by norm_num)
theorem B1914461 : Blo 1275956 1914461 := bbase (se 3 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 1914461 = 717923) (by norm_num)
theorem B2872925 : Blo 1275956 2872925 := bbase (se 3 (by rfl) ⟨538673, by rfl⟩ : syracuseStep 2872925 = 1077347) (by norm_num)
theorem B4093541 : Blo 1275956 4093541 := bbase (se 4 (by rfl) ⟨383769, by rfl⟩ : syracuseStep 4093541 = 767539) (by norm_num)
theorem B6461045 : Blo 1275956 6461045 := bbase (se 5 (by rfl) ⟨302861, by rfl⟩ : syracuseStep 6461045 = 605723) (by norm_num)
theorem B1914485 : Blo 1275956 1914485 := bbase (se 5 (by rfl) ⟨89741, by rfl⟩ : syracuseStep 1914485 = 179483) (by norm_num)
theorem B1914509 : Blo 1275956 1914509 := bbase (se 3 (by rfl) ⟨358970, by rfl⟩ : syracuseStep 1914509 = 717941) (by norm_num)
theorem B3233429 : Blo 1275956 3233429 := bbase (se 6 (by rfl) ⟨75783, by rfl⟩ : syracuseStep 3233429 = 151567) (by norm_num)
theorem B1914533 : Blo 1275956 1914533 := bbase (se 4 (by rfl) ⟨179487, by rfl⟩ : syracuseStep 1914533 = 358975) (by norm_num)
theorem B2872997 : Blo 1275956 2872997 := bbase (se 4 (by rfl) ⟨269343, by rfl⟩ : syracuseStep 2872997 = 538687) (by norm_num)
theorem B1914557 : Blo 1275956 1914557 := bbase (se 3 (by rfl) ⟨358979, by rfl⟩ : syracuseStep 1914557 = 717959) (by norm_num)
theorem B3634885 : Blo 1275956 3634885 := bbase (se 4 (by rfl) ⟨340770, by rfl⟩ : syracuseStep 3634885 = 681541) (by norm_num)
theorem B1914581 : Blo 1275956 1914581 := bbase (se 7 (by rfl) ⟨22436, by rfl⟩ : syracuseStep 1914581 = 44873) (by norm_num)
theorem B4306661 : Blo 1275956 4306661 := bbase (se 4 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 4306661 = 807499) (by norm_num)
theorem B1914605 : Blo 1275956 1914605 := bbase (se 3 (by rfl) ⟨358988, by rfl⟩ : syracuseStep 1914605 = 717977) (by norm_num)
theorem B2873069 : Blo 1275956 2873069 := bbase (se 3 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 2873069 = 1077401) (by norm_num)
theorem B1914629 : Blo 1275956 1914629 := bbase (se 4 (by rfl) ⟨179496, by rfl⟩ : syracuseStep 1914629 = 358993) (by norm_num)
theorem B1455889 : Blo 1275956 1455889 := bbase (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) (by norm_num)
theorem B1914653 : Blo 1275956 1914653 := bbase (se 3 (by rfl) ⟨358997, by rfl⟩ : syracuseStep 1914653 = 717995) (by norm_num)
theorem B1914677 : Blo 1275956 1914677 := bbase (se 5 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 1914677 = 179501) (by norm_num)
theorem B2873141 : Blo 1275956 2873141 := bbase (se 5 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 2873141 = 269357) (by norm_num)
theorem B1914701 : Blo 1275956 1914701 := bbase (se 3 (by rfl) ⟨359006, by rfl⟩ : syracuseStep 1914701 = 718013) (by norm_num)
theorem B3233621 : Blo 1275956 3233621 := bbase (se 9 (by rfl) ⟨9473, by rfl⟩ : syracuseStep 3233621 = 18947) (by norm_num)
theorem B1914725 : Blo 1275956 1914725 := bbase (se 4 (by rfl) ⟨179505, by rfl⟩ : syracuseStep 1914725 = 359011) (by norm_num)
theorem B1914749 : Blo 1275956 1914749 := bbase (se 3 (by rfl) ⟨359015, by rfl⟩ : syracuseStep 1914749 = 718031) (by norm_num)
theorem B2873213 : Blo 1275956 2873213 := bbase (se 3 (by rfl) ⟨538727, by rfl⟩ : syracuseStep 2873213 = 1077455) (by norm_num)
theorem B1914773 : Blo 1275956 1914773 := bbase (se 6 (by rfl) ⟨44877, by rfl⟩ : syracuseStep 1914773 = 89755) (by norm_num)
theorem B1914797 : Blo 1275956 1914797 := bbase (se 3 (by rfl) ⟨359024, by rfl⟩ : syracuseStep 1914797 = 718049) (by norm_num)
theorem B1914821 : Blo 1275956 1914821 := bbase (se 4 (by rfl) ⟨179514, by rfl⟩ : syracuseStep 1914821 = 359029) (by norm_num)
theorem B2873285 : Blo 1275956 2873285 := bbase (se 4 (by rfl) ⟨269370, by rfl⟩ : syracuseStep 2873285 = 538741) (by norm_num)
theorem B1914845 : Blo 1275956 1914845 := bbase (se 3 (by rfl) ⟨359033, by rfl⟩ : syracuseStep 1914845 = 718067) (by norm_num)
theorem B1914869 : Blo 1275956 1914869 := bbase (se 5 (by rfl) ⟨89759, by rfl⟩ : syracuseStep 1914869 = 179519) (by norm_num)
theorem B8181749 : Blo 1275956 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B1914893 : Blo 1275956 1914893 := bbase (se 3 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 1914893 = 718085) (by norm_num)
theorem B2873357 : Blo 1275956 2873357 := bbase (se 3 (by rfl) ⟨538754, by rfl⟩ : syracuseStep 2873357 = 1077509) (by norm_num)
theorem B1914917 : Blo 1275956 1914917 := bbase (se 4 (by rfl) ⟨179523, by rfl⟩ : syracuseStep 1914917 = 359047) (by norm_num)
theorem B1914941 : Blo 1275956 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B1914965 : Blo 1275956 1914965 := bbase (se 8 (by rfl) ⟨11220, by rfl⟩ : syracuseStep 1914965 = 22441) (by norm_num)
theorem B2873429 : Blo 1275956 2873429 := bbase (se 8 (by rfl) ⟨16836, by rfl⟩ : syracuseStep 2873429 = 33673) (by norm_num)
theorem B2422885 : Blo 1275956 2422885 := bbase (se 4 (by rfl) ⟨227145, by rfl⟩ : syracuseStep 2422885 = 454291) (by norm_num)
theorem B2046053 : Blo 1275956 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B1914989 : Blo 1275956 1914989 := bbase (se 3 (by rfl) ⟨359060, by rfl⟩ : syracuseStep 1914989 = 718121) (by norm_num)
theorem B1915013 : Blo 1275956 1915013 := bbase (se 4 (by rfl) ⟨179532, by rfl⟩ : syracuseStep 1915013 = 359065) (by norm_num)
theorem B4307093 : Blo 1275956 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B2726045 : Blo 1275956 2726045 := bbase (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) (by norm_num)
theorem B1915037 : Blo 1275956 1915037 := bbase (se 3 (by rfl) ⟨359069, by rfl⟩ : syracuseStep 1915037 = 718139) (by norm_num)
theorem B2873501 : Blo 1275956 2873501 := bbase (se 3 (by rfl) ⟨538781, by rfl⟩ : syracuseStep 2873501 = 1077563) (by norm_num)
theorem B3233965 : Blo 1275956 3233965 := bbase (se 3 (by rfl) ⟨606368, by rfl⟩ : syracuseStep 3233965 = 1212737) (by norm_num)
theorem B1915061 : Blo 1275956 1915061 := bbase (se 5 (by rfl) ⟨89768, by rfl⟩ : syracuseStep 1915061 = 179537) (by norm_num)
theorem B1915085 : Blo 1275956 1915085 := bbase (se 3 (by rfl) ⟨359078, by rfl⟩ : syracuseStep 1915085 = 718157) (by norm_num)
theorem B1915109 : Blo 1275956 1915109 := bbase (se 4 (by rfl) ⟨179541, by rfl⟩ : syracuseStep 1915109 = 359083) (by norm_num)
theorem B2873573 : Blo 1275956 2873573 := bbase (se 4 (by rfl) ⟨269397, by rfl⟩ : syracuseStep 2873573 = 538795) (by norm_num)
theorem B2423029 : Blo 1275956 2423029 := bbase (se 5 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 2423029 = 227159) (by norm_num)
theorem B1915133 : Blo 1275956 1915133 := bbase (se 3 (by rfl) ⟨359087, by rfl⟩ : syracuseStep 1915133 = 718175) (by norm_num)
theorem B1915157 : Blo 1275956 1915157 := bbase (se 6 (by rfl) ⟨44886, by rfl⟩ : syracuseStep 1915157 = 89773) (by norm_num)
theorem B3234077 : Blo 1275956 3234077 := bbase (se 3 (by rfl) ⟨606389, by rfl⟩ : syracuseStep 3234077 = 1212779) (by norm_num)
theorem B1915181 : Blo 1275956 1915181 := bbase (se 3 (by rfl) ⟨359096, by rfl⟩ : syracuseStep 1915181 = 718193) (by norm_num)
theorem B2873645 : Blo 1275956 2873645 := bbase (se 3 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 2873645 = 1077617) (by norm_num)
theorem B1915205 : Blo 1275956 1915205 := bbase (se 4 (by rfl) ⟨179550, by rfl⟩ : syracuseStep 1915205 = 359101) (by norm_num)
theorem B16578901 : Blo 1275956 16578901 := bbase (se 10 (by rfl) ⟨24285, by rfl⟩ : syracuseStep 16578901 = 48571) (by norm_num)
theorem B4847957 : Blo 1275956 4847957 := bbase (se 10 (by rfl) ⟨7101, by rfl⟩ : syracuseStep 4847957 = 14203) (by norm_num)
theorem B1915229 : Blo 1275956 1915229 := bbase (se 3 (by rfl) ⟨359105, by rfl⟩ : syracuseStep 1915229 = 718211) (by norm_num)
theorem B1915253 : Blo 1275956 1915253 := bbase (se 5 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 1915253 = 179555) (by norm_num)
theorem B2873717 : Blo 1275956 2873717 := bbase (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) (by norm_num)
theorem B1915277 : Blo 1275956 1915277 := bbase (se 3 (by rfl) ⟨359114, by rfl⟩ : syracuseStep 1915277 = 718229) (by norm_num)
theorem B2423189 : Blo 1275956 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B2726293 : Blo 1275956 2726293 := bbase (se 6 (by rfl) ⟨63897, by rfl⟩ : syracuseStep 2726293 = 127795) (by norm_num)
theorem B1915301 : Blo 1275956 1915301 := bbase (se 4 (by rfl) ⟨179559, by rfl⟩ : syracuseStep 1915301 = 359119) (by norm_num)
theorem B1915325 : Blo 1275956 1915325 := bbase (se 3 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 1915325 = 718247) (by norm_num)
theorem B2873789 : Blo 1275956 2873789 := bbase (se 3 (by rfl) ⟨538835, by rfl⟩ : syracuseStep 2873789 = 1077671) (by norm_num)
theorem B1915349 : Blo 1275956 1915349 := bbase (se 7 (by rfl) ⟨22445, by rfl⟩ : syracuseStep 1915349 = 44891) (by norm_num)
theorem B3234269 : Blo 1275956 3234269 := bbase (se 3 (by rfl) ⟨606425, by rfl⟩ : syracuseStep 3234269 = 1212851) (by norm_num)
theorem B1915373 : Blo 1275956 1915373 := bbase (se 3 (by rfl) ⟨359132, by rfl⟩ : syracuseStep 1915373 = 718265) (by norm_num)
theorem B1915397 : Blo 1275956 1915397 := bbase (se 4 (by rfl) ⟨179568, by rfl⟩ : syracuseStep 1915397 = 359137) (by norm_num)
theorem B2873861 : Blo 1275956 2873861 := bbase (se 4 (by rfl) ⟨269424, by rfl⟩ : syracuseStep 2873861 = 538849) (by norm_num)
theorem B1817101 : Blo 1275956 1817101 := bbase (se 3 (by rfl) ⟨340706, by rfl⟩ : syracuseStep 1817101 = 681413) (by norm_num)
theorem B1915421 : Blo 1275956 1915421 := bbase (se 3 (by rfl) ⟨359141, by rfl⟩ : syracuseStep 1915421 = 718283) (by norm_num)
theorem B2423333 : Blo 1275956 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B1915445 : Blo 1275956 1915445 := bbase (se 5 (by rfl) ⟨89786, by rfl⟩ : syracuseStep 1915445 = 179573) (by norm_num)
theorem B4307525 : Blo 1275956 4307525 := bbase (se 4 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 4307525 = 807661) (by norm_num)
theorem B1915469 : Blo 1275956 1915469 := bbase (se 3 (by rfl) ⟨359150, by rfl⟩ : syracuseStep 1915469 = 718301) (by norm_num)
theorem B2873933 : Blo 1275956 2873933 := bbase (se 3 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 2873933 = 1077725) (by norm_num)
theorem B2185805 : Blo 1275956 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B3070541 : Blo 1275956 3070541 := bbase (se 3 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 3070541 = 1151453) (by norm_num)
theorem B1915493 : Blo 1275956 1915493 := bbase (se 4 (by rfl) ⟨179577, by rfl⟩ : syracuseStep 1915493 = 359155) (by norm_num)
theorem B4848245 : Blo 1275956 4848245 := bbase (se 5 (by rfl) ⟨227261, by rfl⟩ : syracuseStep 4848245 = 454523) (by norm_num)
theorem B1915517 : Blo 1275956 1915517 := bbase (se 3 (by rfl) ⟨359159, by rfl⟩ : syracuseStep 1915517 = 718319) (by norm_num)
theorem B1915541 : Blo 1275956 1915541 := bbase (se 6 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 1915541 = 89791) (by norm_num)
theorem B2874005 : Blo 1275956 2874005 := bbase (se 6 (by rfl) ⟨67359, by rfl⟩ : syracuseStep 2874005 = 134719) (by norm_num)
theorem B1915565 : Blo 1275956 1915565 := bbase (se 3 (by rfl) ⟨359168, by rfl⟩ : syracuseStep 1915565 = 718337) (by norm_num)
theorem B1915589 : Blo 1275956 1915589 := bbase (se 4 (by rfl) ⟨179586, by rfl⟩ : syracuseStep 1915589 = 359173) (by norm_num)
theorem B1915613 : Blo 1275956 1915613 := bbase (se 3 (by rfl) ⟨359177, by rfl⟩ : syracuseStep 1915613 = 718355) (by norm_num)
theorem B2874077 : Blo 1275956 2874077 := bbase (se 3 (by rfl) ⟨538889, by rfl⟩ : syracuseStep 2874077 = 1077779) (by norm_num)
theorem B2153189 : Blo 1275956 2153189 := bbase (se 4 (by rfl) ⟨201861, by rfl⟩ : syracuseStep 2153189 = 403723) (by norm_num)
theorem B1915637 : Blo 1275956 1915637 := bbase (se 5 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 1915637 = 179591) (by norm_num)
theorem B6904565 : Blo 1275956 6904565 := bbase (se 5 (by rfl) ⟨323651, by rfl⟩ : syracuseStep 6904565 = 647303) (by norm_num)
theorem B2046725 : Blo 1275956 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B1915661 : Blo 1275956 1915661 := bbase (se 3 (by rfl) ⟨359186, by rfl⟩ : syracuseStep 1915661 = 718373) (by norm_num)
theorem B1915685 : Blo 1275956 1915685 := bbase (se 4 (by rfl) ⟨179595, by rfl⟩ : syracuseStep 1915685 = 359191) (by norm_num)
theorem B2874149 : Blo 1275956 2874149 := bbase (se 4 (by rfl) ⟨269451, by rfl⟩ : syracuseStep 2874149 = 538903) (by norm_num)
theorem B3234613 : Blo 1275956 3234613 := bbase (se 5 (by rfl) ⟨151622, by rfl⟩ : syracuseStep 3234613 = 303245) (by norm_num)
theorem B1940285 : Blo 1275956 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B1915709 : Blo 1275956 1915709 := bbase (se 3 (by rfl) ⟨359195, by rfl⟩ : syracuseStep 1915709 = 718391) (by norm_num)
theorem B2423621 : Blo 1275956 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B3275605 : Blo 1275956 3275605 := bbase (se 9 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 3275605 = 19193) (by norm_num)
theorem B1915733 : Blo 1275956 1915733 := bbase (se 9 (by rfl) ⟨5612, by rfl⟩ : syracuseStep 1915733 = 11225) (by norm_num)
theorem B2153317 : Blo 1275956 2153317 := bbase (se 4 (by rfl) ⟨201873, by rfl⟩ : syracuseStep 2153317 = 403747) (by norm_num)
theorem B1915757 : Blo 1275956 1915757 := bbase (se 3 (by rfl) ⟨359204, by rfl⟩ : syracuseStep 1915757 = 718409) (by norm_num)
theorem B2874221 : Blo 1275956 2874221 := bbase (se 3 (by rfl) ⟨538916, by rfl⟩ : syracuseStep 2874221 = 1077833) (by norm_num)
theorem B6462341 : Blo 1275956 6462341 := bbase (se 4 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 6462341 = 1211689) (by norm_num)
theorem B3152773 : Blo 1275956 3152773 := bbase (se 4 (by rfl) ⟨295572, by rfl⟩ : syracuseStep 3152773 = 591145) (by norm_num)
theorem B1915781 : Blo 1275956 1915781 := bbase (se 4 (by rfl) ⟨179604, by rfl⟩ : syracuseStep 1915781 = 359209) (by norm_num)
theorem B2726797 : Blo 1275956 2726797 := bbase (se 3 (by rfl) ⟨511274, by rfl⟩ : syracuseStep 2726797 = 1022549) (by norm_num)
theorem B1555345 : Blo 1275956 1555345 := bbase (se 2 (by rfl) ⟨583254, by rfl⟩ : syracuseStep 1555345 = 1166509) (by norm_num)
theorem B1915805 : Blo 1275956 1915805 := bbase (se 3 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 1915805 = 718427) (by norm_num)
theorem B3234725 : Blo 1275956 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B5454773 : Blo 1275956 5454773 := bbase (se 5 (by rfl) ⟨255692, by rfl⟩ : syracuseStep 5454773 = 511385) (by norm_num)
theorem B1915829 : Blo 1275956 1915829 := bbase (se 5 (by rfl) ⟨89804, by rfl⟩ : syracuseStep 1915829 = 179609) (by norm_num)
theorem B2874293 : Blo 1275956 2874293 := bbase (se 5 (by rfl) ⟨134732, by rfl⟩ : syracuseStep 2874293 = 269465) (by norm_num)
theorem B2153405 : Blo 1275956 2153405 := bbase (se 3 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 2153405 = 807527) (by norm_num)
theorem B1915853 : Blo 1275956 1915853 := bbase (se 3 (by rfl) ⟨359222, by rfl⟩ : syracuseStep 1915853 = 718445) (by norm_num)
theorem B2423773 : Blo 1275956 2423773 := bbase (se 3 (by rfl) ⟨454457, by rfl⟩ : syracuseStep 2423773 = 908915) (by norm_num)
theorem B1915877 : Blo 1275956 1915877 := bbase (se 4 (by rfl) ⟨179613, by rfl⟩ : syracuseStep 1915877 = 359227) (by norm_num)
theorem B4307957 : Blo 1275956 4307957 := bbase (se 5 (by rfl) ⟨201935, by rfl⟩ : syracuseStep 4307957 = 403871) (by norm_num)
theorem B1915901 : Blo 1275956 1915901 := bbase (se 3 (by rfl) ⟨359231, by rfl⟩ : syracuseStep 1915901 = 718463) (by norm_num)
theorem B2874365 : Blo 1275956 2874365 := bbase (se 3 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 2874365 = 1077887) (by norm_num)
theorem B2587661 : Blo 1275956 2587661 := bbase (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) (by norm_num)
theorem B9198613 : Blo 1275956 9198613 := bbase (se 6 (by rfl) ⟨215592, by rfl⟩ : syracuseStep 9198613 = 431185) (by norm_num)
theorem B1915925 : Blo 1275956 1915925 := bbase (se 6 (by rfl) ⟨44904, by rfl⟩ : syracuseStep 1915925 = 89809) (by norm_num)
theorem B1915949 : Blo 1275956 1915949 := bbase (se 3 (by rfl) ⟨359240, by rfl⟩ : syracuseStep 1915949 = 718481) (by norm_num)
theorem B2153533 : Blo 1275956 2153533 := bbase (se 3 (by rfl) ⟨403787, by rfl⟩ : syracuseStep 2153533 = 807575) (by norm_num)
theorem B1915973 : Blo 1275956 1915973 := bbase (se 4 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 1915973 = 359245) (by norm_num)
theorem B2874437 : Blo 1275956 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B6134869 : Blo 1275956 6134869 := bbase (se 8 (by rfl) ⟨35946, by rfl⟩ : syracuseStep 6134869 = 71893) (by norm_num)
theorem B1915997 : Blo 1275956 1915997 := bbase (se 3 (by rfl) ⟨359249, by rfl⟩ : syracuseStep 1915997 = 718499) (by norm_num)
theorem B4602997 : Blo 1275956 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B1916021 : Blo 1275956 1916021 := bbase (se 5 (by rfl) ⟨89813, by rfl⟩ : syracuseStep 1916021 = 179627) (by norm_num)
theorem B2301061 : Blo 1275956 2301061 := bbase (se 4 (by rfl) ⟨215724, by rfl⟩ : syracuseStep 2301061 = 431449) (by norm_num)
theorem B1916045 : Blo 1275956 1916045 := bbase (se 3 (by rfl) ⟨359258, by rfl⟩ : syracuseStep 1916045 = 718517) (by norm_num)
theorem B2874509 : Blo 1275956 2874509 := bbase (se 3 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 2874509 = 1077941) (by norm_num)
theorem B2153621 : Blo 1275956 2153621 := bbase (se 6 (by rfl) ⟨50475, by rfl⟩ : syracuseStep 2153621 = 100951) (by norm_num)
theorem B3636389 : Blo 1275956 3636389 := bbase (se 4 (by rfl) ⟨340911, by rfl⟩ : syracuseStep 3636389 = 681823) (by norm_num)
theorem B1916069 : Blo 1275956 1916069 := bbase (se 4 (by rfl) ⟨179631, by rfl⟩ : syracuseStep 1916069 = 359263) (by norm_num)
theorem B1916093 : Blo 1275956 1916093 := bbase (se 3 (by rfl) ⟨359267, by rfl⟩ : syracuseStep 1916093 = 718535) (by norm_num)
theorem B5823701 : Blo 1275956 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B1916117 : Blo 1275956 1916117 := bbase (se 7 (by rfl) ⟨22454, by rfl⟩ : syracuseStep 1916117 = 44909) (by norm_num)
theorem B2874581 : Blo 1275956 2874581 := bbase (se 7 (by rfl) ⟨33686, by rfl⟩ : syracuseStep 2874581 = 67373) (by norm_num)
theorem B1916141 : Blo 1275956 1916141 := bbase (se 3 (by rfl) ⟨359276, by rfl⟩ : syracuseStep 1916141 = 718553) (by norm_num)
theorem B4668661 : Blo 1275956 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B1916165 : Blo 1275956 1916165 := bbase (se 4 (by rfl) ⟨179640, by rfl⟩ : syracuseStep 1916165 = 359281) (by norm_num)
theorem B2424077 : Blo 1275956 2424077 := bbase (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) (by norm_num)
theorem B2153749 : Blo 1275956 2153749 := bbase (se 6 (by rfl) ⟨50478, by rfl⟩ : syracuseStep 2153749 = 100957) (by norm_num)
theorem B4603157 : Blo 1275956 4603157 := bbase (se 6 (by rfl) ⟨107886, by rfl⟩ : syracuseStep 4603157 = 215773) (by norm_num)
theorem B1916189 : Blo 1275956 1916189 := bbase (se 3 (by rfl) ⟨359285, by rfl⟩ : syracuseStep 1916189 = 718571) (by norm_num)
theorem B2874653 : Blo 1275956 2874653 := bbase (se 3 (by rfl) ⟨538997, by rfl⟩ : syracuseStep 2874653 = 1077995) (by norm_num)
theorem B1817893 : Blo 1275956 1817893 := bbase (se 4 (by rfl) ⟨170427, by rfl⟩ : syracuseStep 1817893 = 340855) (by norm_num)
theorem B1916213 : Blo 1275956 1916213 := bbase (se 5 (by rfl) ⟨89822, by rfl⟩ : syracuseStep 1916213 = 179645) (by norm_num)
theorem B1916237 : Blo 1275956 1916237 := bbase (se 3 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 1916237 = 718589) (by norm_num)
theorem B1916261 : Blo 1275956 1916261 := bbase (se 4 (by rfl) ⟨179649, by rfl⟩ : syracuseStep 1916261 = 359299) (by norm_num)
theorem B2874725 : Blo 1275956 2874725 := bbase (se 4 (by rfl) ⟨269505, by rfl⟩ : syracuseStep 2874725 = 539011) (by norm_num)
theorem B2153837 : Blo 1275956 2153837 := bbase (se 3 (by rfl) ⟨403844, by rfl⟩ : syracuseStep 2153837 = 807689) (by norm_num)
theorem B1916285 : Blo 1275956 1916285 := bbase (se 3 (by rfl) ⟨359303, by rfl⟩ : syracuseStep 1916285 = 718607) (by norm_num)
theorem B1916309 : Blo 1275956 1916309 := bbase (se 6 (by rfl) ⟨44913, by rfl⟩ : syracuseStep 1916309 = 89827) (by norm_num)
theorem B4308389 : Blo 1275956 4308389 := bbase (se 4 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 4308389 = 807823) (by norm_num)
theorem B1916333 : Blo 1275956 1916333 := bbase (se 3 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 1916333 = 718625) (by norm_num)
theorem B2874797 : Blo 1275956 2874797 := bbase (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) (by norm_num)
theorem B1916357 : Blo 1275956 1916357 := bbase (se 4 (by rfl) ⟨179658, by rfl⟩ : syracuseStep 1916357 = 359317) (by norm_num)
theorem B1916381 : Blo 1275956 1916381 := bbase (se 3 (by rfl) ⟨359321, by rfl⟩ : syracuseStep 1916381 = 718643) (by norm_num)
theorem B4144613 : Blo 1275956 4144613 := bbase (se 4 (by rfl) ⟨388557, by rfl⟩ : syracuseStep 4144613 = 777115) (by norm_num)
theorem B2153965 : Blo 1275956 2153965 := bbase (se 3 (by rfl) ⟨403868, by rfl⟩ : syracuseStep 2153965 = 807737) (by norm_num)
theorem B1916405 : Blo 1275956 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B2874869 : Blo 1275956 2874869 := bbase (se 5 (by rfl) ⟨134759, by rfl⟩ : syracuseStep 2874869 = 269519) (by norm_num)
theorem B1916429 : Blo 1275956 1916429 := bbase (se 3 (by rfl) ⟨359330, by rfl⟩ : syracuseStep 1916429 = 718661) (by norm_num)
theorem B1916453 : Blo 1275956 1916453 := bbase (se 4 (by rfl) ⟨179667, by rfl⟩ : syracuseStep 1916453 = 359335) (by norm_num)
theorem B1916477 : Blo 1275956 1916477 := bbase (se 3 (by rfl) ⟨359339, by rfl⟩ : syracuseStep 1916477 = 718679) (by norm_num)
theorem B2874941 : Blo 1275956 2874941 := bbase (se 3 (by rfl) ⟨539051, by rfl⟩ : syracuseStep 2874941 = 1078103) (by norm_num)
theorem B2154053 : Blo 1275956 2154053 := bbase (se 4 (by rfl) ⟨201942, by rfl⟩ : syracuseStep 2154053 = 403885) (by norm_num)
theorem B1916501 : Blo 1275956 1916501 := bbase (se 8 (by rfl) ⟨11229, by rfl⟩ : syracuseStep 1916501 = 22459) (by norm_num)
theorem B1916525 : Blo 1275956 1916525 := bbase (se 3 (by rfl) ⟨359348, by rfl⟩ : syracuseStep 1916525 = 718697) (by norm_num)
theorem B1818229 : Blo 1275956 1818229 := bbase (se 5 (by rfl) ⟨85229, by rfl⟩ : syracuseStep 1818229 = 170459) (by norm_num)
theorem B1916549 : Blo 1275956 1916549 := bbase (se 4 (by rfl) ⟨179676, by rfl⟩ : syracuseStep 1916549 = 359353) (by norm_num)
theorem B2875013 : Blo 1275956 2875013 := bbase (se 4 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 2875013 = 539065) (by norm_num)
theorem B1916573 : Blo 1275956 1916573 := bbase (se 3 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 1916573 = 718715) (by norm_num)
theorem B1916597 : Blo 1275956 1916597 := bbase (se 5 (by rfl) ⟨89840, by rfl⟩ : syracuseStep 1916597 = 179681) (by norm_num)
theorem B2154181 : Blo 1275956 2154181 := bbase (se 4 (by rfl) ⟨201954, by rfl⟩ : syracuseStep 2154181 = 403909) (by norm_num)
theorem B1916621 : Blo 1275956 1916621 := bbase (se 3 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 1916621 = 718733) (by norm_num)
theorem B2875085 : Blo 1275956 2875085 := bbase (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) (by norm_num)
theorem B1867493 : Blo 1275956 1867493 := bbase (se 4 (by rfl) ⟨175077, by rfl⟩ : syracuseStep 1867493 = 350155) (by norm_num)
theorem B1916645 : Blo 1275956 1916645 := bbase (se 4 (by rfl) ⟨179685, by rfl⟩ : syracuseStep 1916645 = 359371) (by norm_num)
theorem B1916669 : Blo 1275956 1916669 := bbase (se 3 (by rfl) ⟨359375, by rfl⟩ : syracuseStep 1916669 = 718751) (by norm_num)
theorem B2727685 : Blo 1275956 2727685 := bbase (se 4 (by rfl) ⟨255720, by rfl⟩ : syracuseStep 2727685 = 511441) (by norm_num)
theorem B4849429 : Blo 1275956 4849429 := bbase (se 6 (by rfl) ⟨113658, by rfl⟩ : syracuseStep 4849429 = 227317) (by norm_num)
theorem B1916693 : Blo 1275956 1916693 := bbase (se 6 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 1916693 = 89845) (by norm_num)
theorem B2875157 : Blo 1275956 2875157 := bbase (se 6 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 2875157 = 134773) (by norm_num)
theorem B2154269 : Blo 1275956 2154269 := bbase (se 3 (by rfl) ⟨403925, by rfl⟩ : syracuseStep 2154269 = 807851) (by norm_num)
theorem B1916717 : Blo 1275956 1916717 := bbase (se 3 (by rfl) ⟨359384, by rfl⟩ : syracuseStep 1916717 = 718769) (by norm_num)
theorem B5177141 : Blo 1275956 5177141 := bbase (se 5 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 5177141 = 485357) (by norm_num)
theorem B1916741 : Blo 1275956 1916741 := bbase (se 4 (by rfl) ⟨179694, by rfl⟩ : syracuseStep 1916741 = 359389) (by norm_num)
theorem B1818445 : Blo 1275956 1818445 := bbase (se 3 (by rfl) ⟨340958, by rfl⟩ : syracuseStep 1818445 = 681917) (by norm_num)
theorem B4308821 : Blo 1275956 4308821 := bbase (se 9 (by rfl) ⟨12623, by rfl⟩ : syracuseStep 4308821 = 25247) (by norm_num)
theorem B1916765 : Blo 1275956 1916765 := bbase (se 3 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 1916765 = 718787) (by norm_num)
theorem B2875229 : Blo 1275956 2875229 := bbase (se 3 (by rfl) ⟨539105, by rfl⟩ : syracuseStep 2875229 = 1078211) (by norm_num)
theorem B1916789 : Blo 1275956 1916789 := bbase (se 5 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 1916789 = 179699) (by norm_num)
theorem B1916813 : Blo 1275956 1916813 := bbase (se 3 (by rfl) ⟨359402, by rfl⟩ : syracuseStep 1916813 = 718805) (by norm_num)
theorem B2154397 : Blo 1275956 2154397 := bbase (se 3 (by rfl) ⟨403949, by rfl⟩ : syracuseStep 2154397 = 807899) (by norm_num)
theorem B5455781 : Blo 1275956 5455781 := bbase (se 4 (by rfl) ⟨511479, by rfl⟩ : syracuseStep 5455781 = 1022959) (by norm_num)
theorem B1916837 : Blo 1275956 1916837 := bbase (se 4 (by rfl) ⟨179703, by rfl⟩ : syracuseStep 1916837 = 359407) (by norm_num)
theorem B2875301 : Blo 1275956 2875301 := bbase (se 4 (by rfl) ⟨269559, by rfl⟩ : syracuseStep 2875301 = 539119) (by norm_num)
theorem B1843117 : Blo 1275956 1843117 := bbase (se 3 (by rfl) ⟨345584, by rfl⟩ : syracuseStep 1843117 = 691169) (by norm_num)
theorem B1916861 : Blo 1275956 1916861 := bbase (se 3 (by rfl) ⟨359411, by rfl⟩ : syracuseStep 1916861 = 718823) (by norm_num)
theorem B1916885 : Blo 1275956 1916885 := bbase (se 7 (by rfl) ⟨22463, by rfl⟩ : syracuseStep 1916885 = 44927) (by norm_num)
theorem B2842589 : Blo 1275956 2842589 := bbase (se 3 (by rfl) ⟨532985, by rfl⟩ : syracuseStep 2842589 = 1065971) (by norm_num)
theorem B1916909 : Blo 1275956 1916909 := bbase (se 3 (by rfl) ⟨359420, by rfl⟩ : syracuseStep 1916909 = 718841) (by norm_num)
theorem B2875373 : Blo 1275956 2875373 := bbase (se 3 (by rfl) ⟨539132, by rfl⟩ : syracuseStep 2875373 = 1078265) (by norm_num)
theorem B2154485 : Blo 1275956 2154485 := bbase (se 5 (by rfl) ⟨100991, by rfl⟩ : syracuseStep 2154485 = 201983) (by norm_num)
theorem B2424829 : Blo 1275956 2424829 := bbase (se 3 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 2424829 = 909311) (by norm_num)
theorem B1277955 : Blo 1275956 1277955 := bstep (se 1 (by rfl) ⟨958466, by rfl⟩ : syracuseStep 1277955 = 1916933) B1916933
theorem B4309037 : Blo 1275956 4309037 := bstep (se 3 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 4309037 = 1615889) B1615889
theorem B2154593 : Blo 1275956 2154593 := bstep (se 2 (by rfl) ⟨807972, by rfl⟩ : syracuseStep 2154593 = 1615945) B1615945
theorem B4309091 : Blo 1275956 4309091 := bstep (se 1 (by rfl) ⟨3231818, by rfl⟩ : syracuseStep 4309091 = 6463637) B6463637
theorem B1818787 : Blo 1275956 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B1941683 : Blo 1275956 1941683 := bstep (se 1 (by rfl) ⟨1456262, by rfl⟩ : syracuseStep 1941683 = 2912525) B2912525
theorem B30286021 : Blo 1275956 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B2154721 : Blo 1275956 2154721 := bstep (se 2 (by rfl) ⟨808020, by rfl⟩ : syracuseStep 2154721 = 1616041) B1616041
theorem B23306467 : Blo 1275956 23306467 := bstep (se 1 (by rfl) ⟨17479850, by rfl⟩ : syracuseStep 23306467 = 34959701) B34959701
theorem B2154755 : Blo 1275956 2154755 := bstep (se 1 (by rfl) ⟨1616066, by rfl⟩ : syracuseStep 2154755 = 3232133) B3232133
theorem B4309361 : Blo 1275956 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B2589041 : Blo 1275956 2589041 := bstep (se 2 (by rfl) ⟨970890, by rfl⟩ : syracuseStep 2589041 = 1941781) B1941781
theorem B2154883 : Blo 1275956 2154883 := bstep (se 1 (by rfl) ⟨1616162, by rfl⟩ : syracuseStep 2154883 = 3232325) B3232325
theorem B2425315 : Blo 1275956 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B4088323 : Blo 1275956 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B4850189 : Blo 1275956 4850189 := bstep (se 3 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 4850189 = 1818821) B1818821
theorem B2155025 : Blo 1275956 2155025 := bstep (se 2 (by rfl) ⟨808134, by rfl⟩ : syracuseStep 2155025 = 1616269) B1616269
theorem B5456497 : Blo 1275956 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B1819265 : Blo 1275956 1819265 := bstep (se 2 (by rfl) ⟨682224, by rfl⟩ : syracuseStep 1819265 = 1364449) B1364449
theorem B2155153 : Blo 1275956 2155153 := bstep (se 2 (by rfl) ⟨808182, by rfl⟩ : syracuseStep 2155153 = 1616365) B1616365
theorem B2155187 : Blo 1275956 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B1819379 : Blo 1275956 1819379 := bstep (se 1 (by rfl) ⟨1364534, by rfl⟩ : syracuseStep 1819379 = 2729069) B2729069
theorem B3638029 : Blo 1275956 3638029 := bstep (se 3 (by rfl) ⟨682130, by rfl⟩ : syracuseStep 3638029 = 1364261) B1364261
theorem B2155315 : Blo 1275956 2155315 := bstep (se 1 (by rfl) ⟨1616486, by rfl⟩ : syracuseStep 2155315 = 3232973) B3232973
theorem B1819459 : Blo 1275956 1819459 := bstep (se 1 (by rfl) ⟨1364594, by rfl⟩ : syracuseStep 1819459 = 2729189) B2729189
theorem B4088657 : Blo 1275956 4088657 := bstep (se 2 (by rfl) ⟨1533246, by rfl⟩ : syracuseStep 4088657 = 3066493) B3066493
theorem B4309901 : Blo 1275956 4309901 := bstep (se 3 (by rfl) ⟨808106, by rfl⟩ : syracuseStep 4309901 = 1616213) B1616213
theorem B2425763 : Blo 1275956 2425763 := bstep (se 1 (by rfl) ⟨1819322, by rfl⟩ : syracuseStep 2425763 = 3638645) B3638645
theorem B3638189 : Blo 1275956 3638189 := bstep (se 3 (by rfl) ⟨682160, by rfl⟩ : syracuseStep 3638189 = 1364321) B1364321
theorem B2155457 : Blo 1275956 2155457 := bstep (se 2 (by rfl) ⟨808296, by rfl⟩ : syracuseStep 2155457 = 1616593) B1616593
theorem B4309955 : Blo 1275956 4309955 := bstep (se 1 (by rfl) ⟨3232466, by rfl⟩ : syracuseStep 4309955 = 6464933) B6464933
theorem B8176625 : Blo 1275956 8176625 := bstep (se 2 (by rfl) ⟨3066234, by rfl⟩ : syracuseStep 8176625 = 6132469) B6132469
theorem B1598467 : Blo 1275956 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B10347533 : Blo 1275956 10347533 := bstep (se 3 (by rfl) ⟨1940162, by rfl⟩ : syracuseStep 10347533 = 3880325) B3880325
theorem B2155585 : Blo 1275956 2155585 := bstep (se 2 (by rfl) ⟨808344, by rfl⟩ : syracuseStep 2155585 = 1616689) B1616689
theorem B2458691 : Blo 1275956 2458691 := bstep (se 1 (by rfl) ⟨1844018, by rfl⟩ : syracuseStep 2458691 = 3688037) B3688037
theorem B2729027 : Blo 1275956 2729027 := bstep (se 1 (by rfl) ⟨2046770, by rfl⟩ : syracuseStep 2729027 = 4093541) B4093541
theorem B2155619 : Blo 1275956 2155619 := bstep (se 1 (by rfl) ⟨1616714, by rfl⟩ : syracuseStep 2155619 = 3233429) B3233429
theorem B3638371 : Blo 1275956 3638371 := bstep (se 1 (by rfl) ⟨2728778, by rfl⟩ : syracuseStep 3638371 = 5457557) B5457557
theorem B5604515 : Blo 1275956 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B2426051 : Blo 1275956 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B5825741 : Blo 1275956 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B4310225 : Blo 1275956 4310225 := bstep (se 2 (by rfl) ⟨1616334, by rfl⟩ : syracuseStep 4310225 = 3232669) B3232669
theorem B2155747 : Blo 1275956 2155747 := bstep (se 1 (by rfl) ⟨1616810, by rfl⟩ : syracuseStep 2155747 = 3233621) B3233621
theorem B11052301 : Blo 1275956 11052301 := bstep (se 3 (by rfl) ⟨2072306, by rfl⟩ : syracuseStep 11052301 = 4144613) B4144613
theorem B5907725 : Blo 1275956 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B8185157 : Blo 1275956 8185157 := bstep (se 4 (by rfl) ⟨767358, by rfl⟩ : syracuseStep 8185157 = 1534717) B1534717
theorem B12264817 : Blo 1275956 12264817 := bstep (se 2 (by rfl) ⟨4599306, by rfl⟩ : syracuseStep 12264817 = 9198613) B9198613
theorem B19654001 : Blo 1275956 19654001 := bstep (se 2 (by rfl) ⟨7370250, by rfl⟩ : syracuseStep 19654001 = 14740501) B14740501
theorem B2155889 : Blo 1275956 2155889 := bstep (se 2 (by rfl) ⟨808458, by rfl⟩ : syracuseStep 2155889 = 1616917) B1616917
theorem B3548557 : Blo 1275956 3548557 := bstep (se 3 (by rfl) ⟨665354, by rfl⟩ : syracuseStep 3548557 = 1330709) B1330709
theorem B2156017 : Blo 1275956 2156017 := bstep (se 2 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 2156017 = 1617013) B1617013
theorem B2156051 : Blo 1275956 2156051 := bstep (se 1 (by rfl) ⟨1617038, by rfl⟩ : syracuseStep 2156051 = 3234077) B3234077
theorem B1615459 : Blo 1275956 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B2156179 : Blo 1275956 2156179 := bstep (se 1 (by rfl) ⟨1617134, by rfl⟩ : syracuseStep 2156179 = 3234269) B3234269
theorem B1615555 : Blo 1275956 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B7366349 : Blo 1275956 7366349 := bstep (se 3 (by rfl) ⟨1381190, by rfl⟩ : syracuseStep 7366349 = 2762381) B2762381
theorem B4310765 : Blo 1275956 4310765 := bstep (se 3 (by rfl) ⟨808268, by rfl⟩ : syracuseStep 4310765 = 1616537) B1616537
theorem B2156321 : Blo 1275956 2156321 := bstep (se 2 (by rfl) ⟨808620, by rfl⟩ : syracuseStep 2156321 = 1617241) B1617241
theorem B4310819 : Blo 1275956 4310819 := bstep (se 1 (by rfl) ⟨3233114, by rfl⟩ : syracuseStep 4310819 = 6466229) B6466229
theorem B8734513 : Blo 1275956 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B1435459 : Blo 1275956 1435459 := bstep (se 1 (by rfl) ⟨1076594, by rfl⟩ : syracuseStep 1435459 = 2153189) B2153189
theorem B2156449 : Blo 1275956 2156449 := bstep (se 2 (by rfl) ⟨808668, by rfl⟩ : syracuseStep 2156449 = 1617337) B1617337
theorem B3884995 : Blo 1275956 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B2156483 : Blo 1275956 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B1435603 : Blo 1275956 1435603 := bstep (se 1 (by rfl) ⟨1076702, by rfl⟩ : syracuseStep 1435603 = 2153405) B2153405
theorem B4311089 : Blo 1275956 4311089 := bstep (se 2 (by rfl) ⟨1616658, by rfl⟩ : syracuseStep 4311089 = 3233317) B3233317
theorem B1435747 : Blo 1275956 1435747 := bstep (se 1 (by rfl) ⟨1076810, by rfl⟩ : syracuseStep 1435747 = 2153621) B2153621
theorem B1616051 : Blo 1275956 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B1435891 : Blo 1275956 1435891 := bstep (se 1 (by rfl) ⟨1076918, by rfl⟩ : syracuseStep 1435891 = 2153837) B2153837
theorem B6465905 : Blo 1275956 6465905 := bstep (se 2 (by rfl) ⟨2424714, by rfl⟩ : syracuseStep 6465905 = 4849429) B4849429
theorem B1436035 : Blo 1275956 1436035 := bstep (se 1 (by rfl) ⟨1077026, by rfl⟩ : syracuseStep 1436035 = 2154053) B2154053
theorem B8178083 : Blo 1275956 8178083 := bstep (se 1 (by rfl) ⟨6133562, by rfl⟩ : syracuseStep 8178083 = 12267125) B12267125
theorem B3500525 : Blo 1275956 3500525 := bstep (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) B1312697
theorem B1436179 : Blo 1275956 1436179 := bstep (se 1 (by rfl) ⟨1077134, by rfl⟩ : syracuseStep 1436179 = 2154269) B2154269
theorem B3451427 : Blo 1275956 3451427 := bstep (se 1 (by rfl) ⟨2588570, by rfl⟩ : syracuseStep 3451427 = 5177141) B5177141
theorem B4311629 : Blo 1275956 4311629 := bstep (se 3 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 4311629 = 1616861) B1616861
theorem B6556259 : Blo 1275956 6556259 := bstep (se 1 (by rfl) ⟨4917194, by rfl⟩ : syracuseStep 6556259 = 9834389) B9834389
theorem B4311683 : Blo 1275956 4311683 := bstep (se 1 (by rfl) ⟨3233762, by rfl⟩ : syracuseStep 4311683 = 6467525) B6467525
theorem B1895059 : Blo 1275956 1895059 := bstep (se 1 (by rfl) ⟨1421294, by rfl⟩ : syracuseStep 1895059 = 2842589) B2842589
theorem B1436323 : Blo 1275956 1436323 := bstep (se 1 (by rfl) ⟨1077242, by rfl⟩ : syracuseStep 1436323 = 2154485) B2154485
theorem B7269041 : Blo 1275956 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B3230513 : Blo 1275956 3230513 := bstep (se 2 (by rfl) ⟨1211442, by rfl⟩ : syracuseStep 3230513 = 2422885) B2422885
theorem B1436467 : Blo 1275956 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B27601717 : Blo 1275956 27601717 := bstep (se 5 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 27601717 = 2587661) B2587661
theorem B3230563 : Blo 1275956 3230563 := bstep (se 1 (by rfl) ⟨2422922, by rfl⟩ : syracuseStep 3230563 = 4845845) B4845845
theorem B4090733 : Blo 1275956 4090733 := bstep (se 3 (by rfl) ⟨767012, by rfl⟩ : syracuseStep 4090733 = 1534025) B1534025
theorem B1616755 : Blo 1275956 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B3107729 : Blo 1275956 3107729 := bstep (se 2 (by rfl) ⟨1165398, by rfl⟩ : syracuseStep 3107729 = 2330797) B2330797
theorem B4311953 : Blo 1275956 4311953 := bstep (se 2 (by rfl) ⟨1616982, by rfl⟩ : syracuseStep 4311953 = 3233965) B3233965
theorem B1436611 : Blo 1275956 1436611 := bstep (se 1 (by rfl) ⟨1077458, by rfl⟩ : syracuseStep 1436611 = 2154917) B2154917
theorem B1616851 : Blo 1275956 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B5450723 : Blo 1275956 5450723 := bstep (se 1 (by rfl) ⟨4088042, by rfl⟩ : syracuseStep 5450723 = 8176085) B8176085
theorem B3230705 : Blo 1275956 3230705 := bstep (se 2 (by rfl) ⟨1211514, by rfl⟩ : syracuseStep 3230705 = 2423029) B2423029
theorem B1534963 : Blo 1275956 1534963 := bstep (se 1 (by rfl) ⟨1151222, by rfl⟩ : syracuseStep 1534963 = 2302445) B2302445
theorem B1436755 : Blo 1275956 1436755 := bstep (se 1 (by rfl) ⟨1077566, by rfl⟩ : syracuseStep 1436755 = 2155133) B2155133
theorem B10488973 : Blo 1275956 10488973 := bstep (se 3 (by rfl) ⟨1966682, by rfl⟩ : syracuseStep 10488973 = 3933365) B3933365
theorem B1436899 : Blo 1275956 1436899 := bstep (se 1 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 1436899 = 2155349) B2155349
theorem B1437043 : Blo 1275956 1437043 := bstep (se 1 (by rfl) ⟨1077782, by rfl⟩ : syracuseStep 1437043 = 2155565) B2155565
theorem B4312493 : Blo 1275956 4312493 := bstep (se 3 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 4312493 = 1617185) B1617185
theorem B1617347 : Blo 1275956 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B2911697 : Blo 1275956 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B4312547 : Blo 1275956 4312547 := bstep (se 1 (by rfl) ⟨3234410, by rfl⟩ : syracuseStep 4312547 = 6468821) B6468821
theorem B4845041 : Blo 1275956 4845041 := bstep (se 2 (by rfl) ⟨1816890, by rfl⟩ : syracuseStep 4845041 = 3633781) B3633781
theorem B1437187 : Blo 1275956 1437187 := bstep (se 1 (by rfl) ⟨1077890, by rfl⟩ : syracuseStep 1437187 = 2155781) B2155781
theorem B6139405 : Blo 1275956 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B3452465 : Blo 1275956 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B9203341 : Blo 1275956 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B1437331 : Blo 1275956 1437331 := bstep (se 1 (by rfl) ⟨1077998, by rfl⟩ : syracuseStep 1437331 = 2155997) B2155997
theorem B4312817 : Blo 1275956 4312817 := bstep (se 2 (by rfl) ⟨1617306, by rfl⟩ : syracuseStep 4312817 = 3234613) B3234613
theorem B6467363 : Blo 1275956 6467363 := bstep (se 1 (by rfl) ⟨4850522, by rfl⟩ : syracuseStep 6467363 = 9701045) B9701045
theorem B1437475 : Blo 1275956 1437475 := bstep (se 1 (by rfl) ⟨1078106, by rfl⟩ : syracuseStep 1437475 = 2156213) B2156213
theorem B2871089 : Blo 1275956 2871089 := bstep (se 2 (by rfl) ⟨1076658, by rfl⟩ : syracuseStep 2871089 = 2153317) B2153317
theorem B2871107 : Blo 1275956 2871107 := bstep (se 1 (by rfl) ⟨2153330, by rfl⟩ : syracuseStep 2871107 = 4306661) B4306661
theorem B1437619 : Blo 1275956 1437619 := bstep (se 1 (by rfl) ⟨1078214, by rfl⟩ : syracuseStep 1437619 = 2156429) B2156429
theorem B7761869 : Blo 1275956 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B3231697 : Blo 1275956 3231697 := bstep (se 2 (by rfl) ⟨1211886, by rfl⟩ : syracuseStep 3231697 = 2423773) B2423773
theorem B29503541 : Blo 1275956 29503541 := bstep (se 5 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 29503541 = 2765957) B2765957
theorem B41447477 : Blo 1275956 41447477 := bstep (se 5 (by rfl) ⟨1942850, by rfl⟩ : syracuseStep 41447477 = 3885701) B3885701
theorem B1364035 : Blo 1275956 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B2871377 : Blo 1275956 2871377 := bstep (se 2 (by rfl) ⟨1076766, by rfl⟩ : syracuseStep 2871377 = 2153533) B2153533
theorem B2871395 : Blo 1275956 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B7270499 : Blo 1275956 7270499 := bstep (se 1 (by rfl) ⟨5452874, by rfl⟩ : syracuseStep 7270499 = 10905749) B10905749
theorem B8179825 : Blo 1275956 8179825 := bstep (se 2 (by rfl) ⟨3067434, by rfl⟩ : syracuseStep 8179825 = 6134869) B6134869
theorem B3068081 : Blo 1275956 3068081 := bstep (se 2 (by rfl) ⟨1150530, by rfl⟩ : syracuseStep 3068081 = 2301061) B2301061
theorem B3231971 : Blo 1275956 3231971 := bstep (se 1 (by rfl) ⟨2423978, by rfl⟩ : syracuseStep 3231971 = 4847957) B4847957
theorem B1995043 : Blo 1275956 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2871665 : Blo 1275956 2871665 := bstep (se 2 (by rfl) ⟨1076874, by rfl⟩ : syracuseStep 2871665 = 2153749) B2153749
theorem B2871683 : Blo 1275956 2871683 := bstep (se 1 (by rfl) ⟨2153762, by rfl⟩ : syracuseStep 2871683 = 4307525) B4307525
theorem B3232163 : Blo 1275956 3232163 := bstep (se 1 (by rfl) ⟨2424122, by rfl⟩ : syracuseStep 3232163 = 4848245) B4848245
theorem B88420805 : Blo 1275956 88420805 := bstep (se 4 (by rfl) ⟨8289450, by rfl⟩ : syracuseStep 88420805 = 16578901) B16578901
theorem B17469893 : Blo 1275956 17469893 := bstep (se 4 (by rfl) ⟨1637802, by rfl⟩ : syracuseStep 17469893 = 3275605) B3275605
theorem B1364483 : Blo 1275956 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B3109393 : Blo 1275956 3109393 := bstep (se 2 (by rfl) ⟨1166022, by rfl⟩ : syracuseStep 3109393 = 2332045) B2332045
theorem B6468173 : Blo 1275956 6468173 := bstep (se 3 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 6468173 = 2425565) B2425565
theorem B4092515 : Blo 1275956 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B2871953 : Blo 1275956 2871953 := bstep (se 2 (by rfl) ⟨1076982, by rfl⟩ : syracuseStep 2871953 = 2153965) B2153965
theorem B2871971 : Blo 1275956 2871971 := bstep (se 1 (by rfl) ⟨2153978, by rfl⟩ : syracuseStep 2871971 = 4307957) B4307957
theorem B2765507 : Blo 1275956 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B16814789 : Blo 1275956 16814789 := bstep (se 4 (by rfl) ⟨1576386, by rfl⟩ : syracuseStep 16814789 = 3152773) B3152773
theorem B8295173 : Blo 1275956 8295173 := bstep (se 4 (by rfl) ⟨777672, by rfl⟩ : syracuseStep 8295173 = 1555345) B1555345
theorem B2044739 : Blo 1275956 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B5174093 : Blo 1275956 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B3633997 : Blo 1275956 3633997 := bstep (se 3 (by rfl) ⟨681374, by rfl⟩ : syracuseStep 3633997 = 1362749) B1362749
theorem B3068771 : Blo 1275956 3068771 := bstep (se 1 (by rfl) ⟨2301578, by rfl⟩ : syracuseStep 3068771 = 4603157) B4603157
theorem B4846499 : Blo 1275956 4846499 := bstep (se 1 (by rfl) ⟨3634874, by rfl⟩ : syracuseStep 4846499 = 7269749) B7269749
theorem B4846513 : Blo 1275956 4846513 := bstep (se 2 (by rfl) ⟨1817442, by rfl⟩ : syracuseStep 4846513 = 3634885) B3634885
theorem B2872241 : Blo 1275956 2872241 := bstep (se 2 (by rfl) ⟨1077090, by rfl⟩ : syracuseStep 2872241 = 2154181) B2154181
theorem B2872259 : Blo 1275956 2872259 := bstep (se 1 (by rfl) ⟨2154194, by rfl⟩ : syracuseStep 2872259 = 4308389) B4308389
theorem B1913939 : Blo 1275956 1913939 := bstep (se 1 (by rfl) ⟨1435454, by rfl⟩ : syracuseStep 1913939 = 2870909) B2870909
theorem B1913969 : Blo 1275956 1913969 := bstep (se 2 (by rfl) ⟨717738, by rfl⟩ : syracuseStep 1913969 = 1435477) B1435477
theorem B1913987 : Blo 1275956 1913987 := bstep (se 1 (by rfl) ⟨1435490, by rfl⟩ : syracuseStep 1913987 = 2870981) B2870981
theorem B1914017 : Blo 1275956 1914017 := bstep (se 2 (by rfl) ⟨717756, by rfl⟩ : syracuseStep 1914017 = 1435513) B1435513
theorem B1914035 : Blo 1275956 1914035 := bstep (se 1 (by rfl) ⟨1435526, by rfl⟩ : syracuseStep 1914035 = 2871053) B2871053
theorem B1914065 : Blo 1275956 1914065 := bstep (se 2 (by rfl) ⟨717774, by rfl⟩ : syracuseStep 1914065 = 1435549) B1435549
theorem B2872529 : Blo 1275956 2872529 := bstep (se 2 (by rfl) ⟨1077198, by rfl⟩ : syracuseStep 2872529 = 2154397) B2154397
theorem B1914083 : Blo 1275956 1914083 := bstep (se 1 (by rfl) ⟨1435562, by rfl⟩ : syracuseStep 1914083 = 2871125) B2871125
theorem B2872547 : Blo 1275956 2872547 := bstep (se 1 (by rfl) ⟨2154410, by rfl⟩ : syracuseStep 2872547 = 4308821) B4308821
theorem B13800689 : Blo 1275956 13800689 := bstep (se 2 (by rfl) ⟨5175258, by rfl⟩ : syracuseStep 13800689 = 10350517) B10350517
theorem B1914113 : Blo 1275956 1914113 := bstep (se 2 (by rfl) ⟨717792, by rfl⟩ : syracuseStep 1914113 = 1435585) B1435585
theorem B1914131 : Blo 1275956 1914131 := bstep (se 1 (by rfl) ⟨1435598, by rfl⟩ : syracuseStep 1914131 = 2871197) B2871197
theorem B1914161 : Blo 1275956 1914161 := bstep (se 2 (by rfl) ⟨717810, by rfl⟩ : syracuseStep 1914161 = 1435621) B1435621
theorem B6460721 : Blo 1275956 6460721 := bstep (se 2 (by rfl) ⟨2422770, by rfl⟩ : syracuseStep 6460721 = 4845541) B4845541
theorem B1914179 : Blo 1275956 1914179 := bstep (se 1 (by rfl) ⟨1435634, by rfl⟩ : syracuseStep 1914179 = 2871269) B2871269
theorem B3233105 : Blo 1275956 3233105 := bstep (se 2 (by rfl) ⟨1212414, by rfl⟩ : syracuseStep 3233105 = 2424829) B2424829
theorem B1914209 : Blo 1275956 1914209 := bstep (se 2 (by rfl) ⟨717828, by rfl⟩ : syracuseStep 1914209 = 1435657) B1435657
theorem B2184545 : Blo 1275956 2184545 := bstep (se 2 (by rfl) ⟨819204, by rfl⟩ : syracuseStep 2184545 = 1638409) B1638409
theorem B1914227 : Blo 1275956 1914227 := bstep (se 1 (by rfl) ⟨1435670, by rfl⟩ : syracuseStep 1914227 = 2871341) B2871341
theorem B3233155 : Blo 1275956 3233155 := bstep (se 1 (by rfl) ⟨2424866, by rfl⟩ : syracuseStep 3233155 = 4849733) B4849733
theorem B1914257 : Blo 1275956 1914257 := bstep (se 2 (by rfl) ⟨717846, by rfl⟩ : syracuseStep 1914257 = 1435693) B1435693
theorem B1914275 : Blo 1275956 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B1914305 : Blo 1275956 1914305 := bstep (se 2 (by rfl) ⟨717864, by rfl⟩ : syracuseStep 1914305 = 1435729) B1435729
theorem B1914323 : Blo 1275956 1914323 := bstep (se 1 (by rfl) ⟨1435742, by rfl⟩ : syracuseStep 1914323 = 2871485) B2871485
theorem B1914353 : Blo 1275956 1914353 := bstep (se 2 (by rfl) ⟨717882, by rfl⟩ : syracuseStep 1914353 = 1435765) B1435765
theorem B2872817 : Blo 1275956 2872817 := bstep (se 2 (by rfl) ⟨1077306, by rfl⟩ : syracuseStep 2872817 = 2154613) B2154613
theorem B1914371 : Blo 1275956 1914371 := bstep (se 1 (by rfl) ⟨1435778, by rfl⟩ : syracuseStep 1914371 = 2871557) B2871557
theorem B2872835 : Blo 1275956 2872835 := bstep (se 1 (by rfl) ⟨2154626, by rfl⟩ : syracuseStep 2872835 = 4309253) B4309253
theorem B4306445 : Blo 1275956 4306445 := bstep (se 3 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 4306445 = 1614917) B1614917
theorem B2299409 : Blo 1275956 2299409 := bstep (se 2 (by rfl) ⟨862278, by rfl⟩ : syracuseStep 2299409 = 1724557) B1724557
theorem B3233297 : Blo 1275956 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B1914401 : Blo 1275956 1914401 := bstep (se 2 (by rfl) ⟨717900, by rfl⟩ : syracuseStep 1914401 = 1435801) B1435801
theorem B1914419 : Blo 1275956 1914419 := bstep (se 1 (by rfl) ⟨1435814, by rfl⟩ : syracuseStep 1914419 = 2871629) B2871629
theorem B4306499 : Blo 1275956 4306499 := bstep (se 1 (by rfl) ⟨3229874, by rfl⟩ : syracuseStep 4306499 = 6459749) B6459749
theorem B1914449 : Blo 1275956 1914449 := bstep (se 2 (by rfl) ⟨717918, by rfl⟩ : syracuseStep 1914449 = 1435837) B1435837
theorem B1914467 : Blo 1275956 1914467 := bstep (se 1 (by rfl) ⟨1435850, by rfl⟩ : syracuseStep 1914467 = 2871701) B2871701
theorem B1914497 : Blo 1275956 1914497 := bstep (se 2 (by rfl) ⟨717936, by rfl⟩ : syracuseStep 1914497 = 1435873) B1435873
theorem B2184833 : Blo 1275956 2184833 := bstep (se 2 (by rfl) ⟨819312, by rfl⟩ : syracuseStep 2184833 = 1638625) B1638625
theorem B1914515 : Blo 1275956 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B1455779 : Blo 1275956 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B4429475 : Blo 1275956 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B1914545 : Blo 1275956 1914545 := bstep (se 2 (by rfl) ⟨717954, by rfl⟩ : syracuseStep 1914545 = 1435909) B1435909
theorem B1914563 : Blo 1275956 1914563 := bstep (se 1 (by rfl) ⟨1435922, by rfl⟩ : syracuseStep 1914563 = 2871845) B2871845
theorem B1914593 : Blo 1275956 1914593 := bstep (se 2 (by rfl) ⟨717972, by rfl⟩ : syracuseStep 1914593 = 1435945) B1435945
theorem B7870193 : Blo 1275956 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B4601585 : Blo 1275956 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1914611 : Blo 1275956 1914611 := bstep (se 1 (by rfl) ⟨1435958, by rfl⟩ : syracuseStep 1914611 = 2871917) B2871917
theorem B1914641 : Blo 1275956 1914641 := bstep (se 2 (by rfl) ⟨717990, by rfl⟩ : syracuseStep 1914641 = 1435981) B1435981
theorem B2873105 : Blo 1275956 2873105 := bstep (se 2 (by rfl) ⟨1077414, by rfl⟩ : syracuseStep 2873105 = 2154829) B2154829
theorem B27997973 : Blo 1275956 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1914659 : Blo 1275956 1914659 := bstep (se 1 (by rfl) ⟨1435994, by rfl⟩ : syracuseStep 1914659 = 2871989) B2871989
theorem B2873123 : Blo 1275956 2873123 := bstep (se 1 (by rfl) ⟨2154842, by rfl⟩ : syracuseStep 2873123 = 4309685) B4309685
theorem B1914689 : Blo 1275956 1914689 := bstep (se 2 (by rfl) ⟨718008, by rfl⟩ : syracuseStep 1914689 = 1436017) B1436017
theorem B4306769 : Blo 1275956 4306769 := bstep (se 2 (by rfl) ⟨1615038, by rfl⟩ : syracuseStep 4306769 = 3230077) B3230077
theorem B1914707 : Blo 1275956 1914707 := bstep (se 1 (by rfl) ⟨1436030, by rfl⟩ : syracuseStep 1914707 = 2872061) B2872061
theorem B1914737 : Blo 1275956 1914737 := bstep (se 2 (by rfl) ⟨718026, by rfl⟩ : syracuseStep 1914737 = 1436053) B1436053
theorem B3635057 : Blo 1275956 3635057 := bstep (se 2 (by rfl) ⟨1363146, by rfl⟩ : syracuseStep 3635057 = 2726293) B2726293
theorem B1914755 : Blo 1275956 1914755 := bstep (se 1 (by rfl) ⟨1436066, by rfl⟩ : syracuseStep 1914755 = 2872133) B2872133
theorem B1914785 : Blo 1275956 1914785 := bstep (se 2 (by rfl) ⟨718044, by rfl⟩ : syracuseStep 1914785 = 1436089) B1436089
theorem B4093859 : Blo 1275956 4093859 := bstep (se 1 (by rfl) ⟨3070394, by rfl⟩ : syracuseStep 4093859 = 6140789) B6140789
theorem B1914803 : Blo 1275956 1914803 := bstep (se 1 (by rfl) ⟨1436102, by rfl⟩ : syracuseStep 1914803 = 2872205) B2872205
theorem B24549317 : Blo 1275956 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B3880909 : Blo 1275956 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B1914833 : Blo 1275956 1914833 := bstep (se 2 (by rfl) ⟨718062, by rfl⟩ : syracuseStep 1914833 = 1436125) B1436125
theorem B1914851 : Blo 1275956 1914851 := bstep (se 1 (by rfl) ⟨1436138, by rfl⟩ : syracuseStep 1914851 = 2872277) B2872277
theorem B1914881 : Blo 1275956 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B8181773 : Blo 1275956 8181773 := bstep (se 3 (by rfl) ⟨1534082, by rfl⟩ : syracuseStep 8181773 = 3068165) B3068165
theorem B2422801 : Blo 1275956 2422801 := bstep (se 2 (by rfl) ⟨908550, by rfl⟩ : syracuseStep 2422801 = 1817101) B1817101
theorem B1914899 : Blo 1275956 1914899 := bstep (se 1 (by rfl) ⟨1436174, by rfl⟩ : syracuseStep 1914899 = 2872349) B2872349
theorem B1914929 : Blo 1275956 1914929 := bstep (se 2 (by rfl) ⟨718098, by rfl⟩ : syracuseStep 1914929 = 1436197) B1436197
theorem B2873393 : Blo 1275956 2873393 := bstep (se 2 (by rfl) ⟨1077522, by rfl⟩ : syracuseStep 2873393 = 2155045) B2155045
theorem B1275971 : Blo 1275956 1275971 := bstep (se 1 (by rfl) ⟨956978, by rfl⟩ : syracuseStep 1275971 = 1913957) B1913957
theorem B1914947 : Blo 1275956 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B2873411 : Blo 1275956 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B1275987 : Blo 1275956 1275987 := bstep (se 1 (by rfl) ⟨956990, by rfl⟩ : syracuseStep 1275987 = 1913981) B1913981
theorem B1914977 : Blo 1275956 1914977 := bstep (se 2 (by rfl) ⟨718116, by rfl⟩ : syracuseStep 1914977 = 1436233) B1436233
theorem B1276003 : Blo 1275956 1276003 := bstep (se 1 (by rfl) ⟨957002, by rfl⟩ : syracuseStep 1276003 = 1914005) B1914005
theorem B1276019 : Blo 1275956 1276019 := bstep (se 1 (by rfl) ⟨957014, by rfl⟩ : syracuseStep 1276019 = 1914029) B1914029
theorem B1914995 : Blo 1275956 1914995 := bstep (se 1 (by rfl) ⟨1436246, by rfl⟩ : syracuseStep 1914995 = 2872493) B2872493
theorem B2586755 : Blo 1275956 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B1276035 : Blo 1275956 1276035 := bstep (se 1 (by rfl) ⟨957026, by rfl⟩ : syracuseStep 1276035 = 1914053) B1914053
theorem B3881105 : Blo 1275956 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B1915025 : Blo 1275956 1915025 := bstep (se 2 (by rfl) ⟨718134, by rfl⟩ : syracuseStep 1915025 = 1436269) B1436269
theorem B1276051 : Blo 1275956 1276051 := bstep (se 1 (by rfl) ⟨957038, by rfl⟩ : syracuseStep 1276051 = 1914077) B1914077
theorem B1276067 : Blo 1275956 1276067 := bstep (se 1 (by rfl) ⟨957050, by rfl⟩ : syracuseStep 1276067 = 1914101) B1914101
theorem B1915043 : Blo 1275956 1915043 := bstep (se 1 (by rfl) ⟨1436282, by rfl⟩ : syracuseStep 1915043 = 2872565) B2872565
theorem B1276083 : Blo 1275956 1276083 := bstep (se 1 (by rfl) ⟨957062, by rfl⟩ : syracuseStep 1276083 = 1914125) B1914125
theorem B1915073 : Blo 1275956 1915073 := bstep (se 2 (by rfl) ⟨718152, by rfl⟩ : syracuseStep 1915073 = 1436305) B1436305
theorem B1816771 : Blo 1275956 1816771 := bstep (se 1 (by rfl) ⟨1362578, by rfl⟩ : syracuseStep 1816771 = 2725157) B2725157
theorem B1276099 : Blo 1275956 1276099 := bstep (se 1 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 1276099 = 1914149) B1914149
theorem B2046161 : Blo 1275956 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B1276115 : Blo 1275956 1276115 := bstep (se 1 (by rfl) ⟨957086, by rfl⟩ : syracuseStep 1276115 = 1914173) B1914173
theorem B1915091 : Blo 1275956 1915091 := bstep (se 1 (by rfl) ⟨1436318, by rfl⟩ : syracuseStep 1915091 = 2872637) B2872637
theorem B1276131 : Blo 1275956 1276131 := bstep (se 1 (by rfl) ⟨957098, by rfl⟩ : syracuseStep 1276131 = 1914197) B1914197
theorem B1915121 : Blo 1275956 1915121 := bstep (se 2 (by rfl) ⟨718170, by rfl⟩ : syracuseStep 1915121 = 1436341) B1436341
theorem B1276147 : Blo 1275956 1276147 := bstep (se 1 (by rfl) ⟨957110, by rfl⟩ : syracuseStep 1276147 = 1914221) B1914221
theorem B1276163 : Blo 1275956 1276163 := bstep (se 1 (by rfl) ⟨957122, by rfl⟩ : syracuseStep 1276163 = 1914245) B1914245
theorem B1915139 : Blo 1275956 1915139 := bstep (se 1 (by rfl) ⟨1436354, by rfl⟩ : syracuseStep 1915139 = 2872709) B2872709
theorem B1276179 : Blo 1275956 1276179 := bstep (se 1 (by rfl) ⟨957134, by rfl⟩ : syracuseStep 1276179 = 1914269) B1914269
theorem B1915169 : Blo 1275956 1915169 := bstep (se 2 (by rfl) ⟨718188, by rfl⟩ : syracuseStep 1915169 = 1436377) B1436377
theorem B1276195 : Blo 1275956 1276195 := bstep (se 1 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 1276195 = 1914293) B1914293
theorem B1276211 : Blo 1275956 1276211 := bstep (se 1 (by rfl) ⟨957158, by rfl⟩ : syracuseStep 1276211 = 1914317) B1914317
theorem B1915187 : Blo 1275956 1915187 := bstep (se 1 (by rfl) ⟨1436390, by rfl⟩ : syracuseStep 1915187 = 2872781) B2872781
theorem B1276227 : Blo 1275956 1276227 := bstep (se 1 (by rfl) ⟨957170, by rfl⟩ : syracuseStep 1276227 = 1914341) B1914341
theorem B1915217 : Blo 1275956 1915217 := bstep (se 2 (by rfl) ⟨718206, by rfl⟩ : syracuseStep 1915217 = 1436413) B1436413
theorem B2873681 : Blo 1275956 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B1276243 : Blo 1275956 1276243 := bstep (se 1 (by rfl) ⟨957182, by rfl⟩ : syracuseStep 1276243 = 1914365) B1914365
theorem B1276259 : Blo 1275956 1276259 := bstep (se 1 (by rfl) ⟨957194, by rfl⟩ : syracuseStep 1276259 = 1914389) B1914389
theorem B1915235 : Blo 1275956 1915235 := bstep (se 1 (by rfl) ⟨1436426, by rfl⟩ : syracuseStep 1915235 = 2872853) B2872853
theorem B4847971 : Blo 1275956 4847971 := bstep (se 1 (by rfl) ⟨3635978, by rfl⟩ : syracuseStep 4847971 = 7271957) B7271957
theorem B2873699 : Blo 1275956 2873699 := bstep (se 1 (by rfl) ⟨2155274, by rfl⟩ : syracuseStep 2873699 = 4310549) B4310549
theorem B4307309 : Blo 1275956 4307309 := bstep (se 3 (by rfl) ⟨807620, by rfl⟩ : syracuseStep 4307309 = 1615241) B1615241
theorem B1276275 : Blo 1275956 1276275 := bstep (se 1 (by rfl) ⟨957206, by rfl⟩ : syracuseStep 1276275 = 1914413) B1914413
theorem B1915265 : Blo 1275956 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B1276291 : Blo 1275956 1276291 := bstep (se 1 (by rfl) ⟨957218, by rfl⟩ : syracuseStep 1276291 = 1914437) B1914437
theorem B1276307 : Blo 1275956 1276307 := bstep (se 1 (by rfl) ⟨957230, by rfl⟩ : syracuseStep 1276307 = 1914461) B1914461
theorem B1915283 : Blo 1275956 1915283 := bstep (se 1 (by rfl) ⟨1436462, by rfl⟩ : syracuseStep 1915283 = 2872925) B2872925
theorem B4307363 : Blo 1275956 4307363 := bstep (se 1 (by rfl) ⟨3230522, by rfl⟩ : syracuseStep 4307363 = 6461045) B6461045
theorem B1276323 : Blo 1275956 1276323 := bstep (se 1 (by rfl) ⟨957242, by rfl⟩ : syracuseStep 1276323 = 1914485) B1914485
theorem B1915313 : Blo 1275956 1915313 := bstep (se 2 (by rfl) ⟨718242, by rfl⟩ : syracuseStep 1915313 = 1436485) B1436485
theorem B1276339 : Blo 1275956 1276339 := bstep (se 1 (by rfl) ⟨957254, by rfl⟩ : syracuseStep 1276339 = 1914509) B1914509
theorem B1276355 : Blo 1275956 1276355 := bstep (se 1 (by rfl) ⟨957266, by rfl⟩ : syracuseStep 1276355 = 1914533) B1914533
theorem B1915331 : Blo 1275956 1915331 := bstep (se 1 (by rfl) ⟨1436498, by rfl⟩ : syracuseStep 1915331 = 2872997) B2872997
theorem B1276371 : Blo 1275956 1276371 := bstep (se 1 (by rfl) ⟨957278, by rfl⟩ : syracuseStep 1276371 = 1914557) B1914557
theorem B1915361 : Blo 1275956 1915361 := bstep (se 2 (by rfl) ⟨718260, by rfl⟩ : syracuseStep 1915361 = 1436521) B1436521
theorem B1276387 : Blo 1275956 1276387 := bstep (se 1 (by rfl) ⟨957290, by rfl⟩ : syracuseStep 1276387 = 1914581) B1914581
theorem B3234289 : Blo 1275956 3234289 := bstep (se 2 (by rfl) ⟨1212858, by rfl⟩ : syracuseStep 3234289 = 2425717) B2425717
theorem B1276403 : Blo 1275956 1276403 := bstep (se 1 (by rfl) ⟨957302, by rfl⟩ : syracuseStep 1276403 = 1914605) B1914605
theorem B1915379 : Blo 1275956 1915379 := bstep (se 1 (by rfl) ⟨1436534, by rfl⟩ : syracuseStep 1915379 = 2873069) B2873069
theorem B1276419 : Blo 1275956 1276419 := bstep (se 1 (by rfl) ⟨957314, by rfl⟩ : syracuseStep 1276419 = 1914629) B1914629
theorem B3635729 : Blo 1275956 3635729 := bstep (se 2 (by rfl) ⟨1363398, by rfl⟩ : syracuseStep 3635729 = 2726797) B2726797
theorem B1915409 : Blo 1275956 1915409 := bstep (se 2 (by rfl) ⟨718278, by rfl⟩ : syracuseStep 1915409 = 1436557) B1436557
theorem B1276435 : Blo 1275956 1276435 := bstep (se 1 (by rfl) ⟨957326, by rfl⟩ : syracuseStep 1276435 = 1914653) B1914653
theorem B1276451 : Blo 1275956 1276451 := bstep (se 1 (by rfl) ⟨957338, by rfl⟩ : syracuseStep 1276451 = 1914677) B1914677
theorem B1915427 : Blo 1275956 1915427 := bstep (se 1 (by rfl) ⟨1436570, by rfl⟩ : syracuseStep 1915427 = 2873141) B2873141
theorem B1727011 : Blo 1275956 1727011 := bstep (se 1 (by rfl) ⟨1295258, by rfl⟩ : syracuseStep 1727011 = 2590517) B2590517
theorem B1276467 : Blo 1275956 1276467 := bstep (se 1 (by rfl) ⟨957350, by rfl⟩ : syracuseStep 1276467 = 1914701) B1914701
theorem B1915457 : Blo 1275956 1915457 := bstep (se 2 (by rfl) ⟨718296, by rfl⟩ : syracuseStep 1915457 = 1436593) B1436593
theorem B1276483 : Blo 1275956 1276483 := bstep (se 1 (by rfl) ⟨957362, by rfl⟩ : syracuseStep 1276483 = 1914725) B1914725
theorem B1276499 : Blo 1275956 1276499 := bstep (se 1 (by rfl) ⟨957374, by rfl⟩ : syracuseStep 1276499 = 1914749) B1914749
theorem B1915475 : Blo 1275956 1915475 := bstep (se 1 (by rfl) ⟨1436606, by rfl⟩ : syracuseStep 1915475 = 2873213) B2873213
theorem B1276515 : Blo 1275956 1276515 := bstep (se 1 (by rfl) ⟨957386, by rfl⟩ : syracuseStep 1276515 = 1914773) B1914773
theorem B1915505 : Blo 1275956 1915505 := bstep (se 2 (by rfl) ⟨718314, by rfl⟩ : syracuseStep 1915505 = 1436629) B1436629
theorem B2873969 : Blo 1275956 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1841779 : Blo 1275956 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B1276531 : Blo 1275956 1276531 := bstep (se 1 (by rfl) ⟨957398, by rfl⟩ : syracuseStep 1276531 = 1914797) B1914797
theorem B1276547 : Blo 1275956 1276547 := bstep (se 1 (by rfl) ⟨957410, by rfl⟩ : syracuseStep 1276547 = 1914821) B1914821
theorem B1915523 : Blo 1275956 1915523 := bstep (se 1 (by rfl) ⟨1436642, by rfl⟩ : syracuseStep 1915523 = 2873285) B2873285
theorem B2873987 : Blo 1275956 2873987 := bstep (se 1 (by rfl) ⟨2155490, by rfl⟩ : syracuseStep 2873987 = 4310981) B4310981
theorem B1276563 : Blo 1275956 1276563 := bstep (se 1 (by rfl) ⟨957422, by rfl⟩ : syracuseStep 1276563 = 1914845) B1914845
theorem B1915553 : Blo 1275956 1915553 := bstep (se 2 (by rfl) ⟨718332, by rfl⟩ : syracuseStep 1915553 = 1436665) B1436665
theorem B1276579 : Blo 1275956 1276579 := bstep (se 1 (by rfl) ⟨957434, by rfl⟩ : syracuseStep 1276579 = 1914869) B1914869
theorem B5454499 : Blo 1275956 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B4307633 : Blo 1275956 4307633 := bstep (se 2 (by rfl) ⟨1615362, by rfl⟩ : syracuseStep 4307633 = 3230725) B3230725
theorem B1276595 : Blo 1275956 1276595 := bstep (se 1 (by rfl) ⟨957446, by rfl⟩ : syracuseStep 1276595 = 1914893) B1914893
theorem B1915571 : Blo 1275956 1915571 := bstep (se 1 (by rfl) ⟨1436678, by rfl⟩ : syracuseStep 1915571 = 2873357) B2873357
theorem B1276611 : Blo 1275956 1276611 := bstep (se 1 (by rfl) ⟨957458, by rfl⟩ : syracuseStep 1276611 = 1914917) B1914917
theorem B1915601 : Blo 1275956 1915601 := bstep (se 2 (by rfl) ⟨718350, by rfl⟩ : syracuseStep 1915601 = 1436701) B1436701
theorem B1276627 : Blo 1275956 1276627 := bstep (se 1 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 1276627 = 1914941) B1914941
theorem B6462179 : Blo 1275956 6462179 := bstep (se 1 (by rfl) ⟨4846634, by rfl⟩ : syracuseStep 6462179 = 9693269) B9693269
theorem B1276643 : Blo 1275956 1276643 := bstep (se 1 (by rfl) ⟨957482, by rfl⟩ : syracuseStep 1276643 = 1914965) B1914965
theorem B1915619 : Blo 1275956 1915619 := bstep (se 1 (by rfl) ⟨1436714, by rfl⟩ : syracuseStep 1915619 = 2873429) B2873429
theorem B1817329 : Blo 1275956 1817329 := bstep (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) B1362997
theorem B1276659 : Blo 1275956 1276659 := bstep (se 1 (by rfl) ⟨957494, by rfl⟩ : syracuseStep 1276659 = 1914989) B1914989
theorem B1915649 : Blo 1275956 1915649 := bstep (se 2 (by rfl) ⟨718368, by rfl⟩ : syracuseStep 1915649 = 1436737) B1436737
theorem B1276675 : Blo 1275956 1276675 := bstep (se 1 (by rfl) ⟨957506, by rfl⟩ : syracuseStep 1276675 = 1915013) B1915013
theorem B3234563 : Blo 1275956 3234563 := bstep (se 1 (by rfl) ⟨2425922, by rfl⟩ : syracuseStep 3234563 = 4851845) B4851845
theorem B1817363 : Blo 1275956 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B1276691 : Blo 1275956 1276691 := bstep (se 1 (by rfl) ⟨957518, by rfl⟩ : syracuseStep 1276691 = 1915037) B1915037
theorem B1915667 : Blo 1275956 1915667 := bstep (se 1 (by rfl) ⟨1436750, by rfl⟩ : syracuseStep 1915667 = 2873501) B2873501
theorem B1276707 : Blo 1275956 1276707 := bstep (se 1 (by rfl) ⟨957530, by rfl⟩ : syracuseStep 1276707 = 1915061) B1915061
theorem B1915697 : Blo 1275956 1915697 := bstep (se 2 (by rfl) ⟨718386, by rfl⟩ : syracuseStep 1915697 = 1436773) B1436773
theorem B1276723 : Blo 1275956 1276723 := bstep (se 1 (by rfl) ⟨957542, by rfl⟩ : syracuseStep 1276723 = 1915085) B1915085
theorem B1276739 : Blo 1275956 1276739 := bstep (se 1 (by rfl) ⟨957554, by rfl⟩ : syracuseStep 1276739 = 1915109) B1915109
theorem B1915715 : Blo 1275956 1915715 := bstep (se 1 (by rfl) ⟨1436786, by rfl⟩ : syracuseStep 1915715 = 2873573) B2873573
theorem B16358213 : Blo 1275956 16358213 := bstep (se 4 (by rfl) ⟨1533582, by rfl⟩ : syracuseStep 16358213 = 3067165) B3067165
theorem B2153297 : Blo 1275956 2153297 := bstep (se 2 (by rfl) ⟨807486, by rfl⟩ : syracuseStep 2153297 = 1614973) B1614973
theorem B1276755 : Blo 1275956 1276755 := bstep (se 1 (by rfl) ⟨957566, by rfl⟩ : syracuseStep 1276755 = 1915133) B1915133
theorem B1915745 : Blo 1275956 1915745 := bstep (se 2 (by rfl) ⟨718404, by rfl⟩ : syracuseStep 1915745 = 1436809) B1436809
theorem B1276771 : Blo 1275956 1276771 := bstep (se 1 (by rfl) ⟨957578, by rfl⟩ : syracuseStep 1276771 = 1915157) B1915157
theorem B1276787 : Blo 1275956 1276787 := bstep (se 1 (by rfl) ⟨957590, by rfl⟩ : syracuseStep 1276787 = 1915181) B1915181
theorem B1915763 : Blo 1275956 1915763 := bstep (se 1 (by rfl) ⟨1436822, by rfl⟩ : syracuseStep 1915763 = 2873645) B2873645
theorem B1276803 : Blo 1275956 1276803 := bstep (se 1 (by rfl) ⟨957602, by rfl⟩ : syracuseStep 1276803 = 1915205) B1915205
theorem B1915793 : Blo 1275956 1915793 := bstep (se 2 (by rfl) ⟨718422, by rfl⟩ : syracuseStep 1915793 = 1436845) B1436845
theorem B1276819 : Blo 1275956 1276819 := bstep (se 1 (by rfl) ⟨957614, by rfl⟩ : syracuseStep 1276819 = 1915229) B1915229
theorem B2874257 : Blo 1275956 2874257 := bstep (se 2 (by rfl) ⟨1077846, by rfl⟩ : syracuseStep 2874257 = 2155693) B2155693
theorem B1276835 : Blo 1275956 1276835 := bstep (se 1 (by rfl) ⟨957626, by rfl⟩ : syracuseStep 1276835 = 1915253) B1915253
theorem B1915811 : Blo 1275956 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B2874275 : Blo 1275956 2874275 := bstep (se 1 (by rfl) ⟨2155706, by rfl⟩ : syracuseStep 2874275 = 4311413) B4311413
theorem B1276851 : Blo 1275956 1276851 := bstep (se 1 (by rfl) ⟨957638, by rfl⟩ : syracuseStep 1276851 = 1915277) B1915277
theorem B1915841 : Blo 1275956 1915841 := bstep (se 2 (by rfl) ⟨718440, by rfl⟩ : syracuseStep 1915841 = 1436881) B1436881
theorem B1276867 : Blo 1275956 1276867 := bstep (se 1 (by rfl) ⟨957650, by rfl⟩ : syracuseStep 1276867 = 1915301) B1915301
theorem B3234755 : Blo 1275956 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B7371725 : Blo 1275956 7371725 := bstep (se 3 (by rfl) ⟨1382198, by rfl⟩ : syracuseStep 7371725 = 2764397) B2764397
theorem B2153425 : Blo 1275956 2153425 := bstep (se 2 (by rfl) ⟨807534, by rfl⟩ : syracuseStep 2153425 = 1615069) B1615069
theorem B1276883 : Blo 1275956 1276883 := bstep (se 1 (by rfl) ⟨957662, by rfl⟩ : syracuseStep 1276883 = 1915325) B1915325
theorem B1915859 : Blo 1275956 1915859 := bstep (se 1 (by rfl) ⟨1436894, by rfl⟩ : syracuseStep 1915859 = 2873789) B2873789
theorem B1276899 : Blo 1275956 1276899 := bstep (se 1 (by rfl) ⟨957674, by rfl⟩ : syracuseStep 1276899 = 1915349) B1915349
theorem B3881969 : Blo 1275956 3881969 := bstep (se 2 (by rfl) ⟨1455738, by rfl⟩ : syracuseStep 3881969 = 2911477) B2911477
theorem B1915889 : Blo 1275956 1915889 := bstep (se 2 (by rfl) ⟨718458, by rfl⟩ : syracuseStep 1915889 = 1436917) B1436917
theorem B2153459 : Blo 1275956 2153459 := bstep (se 1 (by rfl) ⟨1615094, by rfl⟩ : syracuseStep 2153459 = 3230189) B3230189
theorem B1276915 : Blo 1275956 1276915 := bstep (se 1 (by rfl) ⟨957686, by rfl⟩ : syracuseStep 1276915 = 1915373) B1915373
theorem B6224881 : Blo 1275956 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B1276931 : Blo 1275956 1276931 := bstep (se 1 (by rfl) ⟨957698, by rfl⟩ : syracuseStep 1276931 = 1915397) B1915397
theorem B1915907 : Blo 1275956 1915907 := bstep (se 1 (by rfl) ⟨1436930, by rfl⟩ : syracuseStep 1915907 = 2873861) B2873861
theorem B1276947 : Blo 1275956 1276947 := bstep (se 1 (by rfl) ⟨957710, by rfl⟩ : syracuseStep 1276947 = 1915421) B1915421
theorem B1915937 : Blo 1275956 1915937 := bstep (se 2 (by rfl) ⟨718476, by rfl⟩ : syracuseStep 1915937 = 1436953) B1436953
theorem B1276963 : Blo 1275956 1276963 := bstep (se 1 (by rfl) ⟨957722, by rfl⟩ : syracuseStep 1276963 = 1915445) B1915445
theorem B2423857 : Blo 1275956 2423857 := bstep (se 2 (by rfl) ⟨908946, by rfl⟩ : syracuseStep 2423857 = 1817893) B1817893
theorem B1276979 : Blo 1275956 1276979 := bstep (se 1 (by rfl) ⟨957734, by rfl⟩ : syracuseStep 1276979 = 1915469) B1915469
theorem B1915955 : Blo 1275956 1915955 := bstep (se 1 (by rfl) ⟨1436966, by rfl⟩ : syracuseStep 1915955 = 2873933) B2873933
theorem B1457203 : Blo 1275956 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B2047027 : Blo 1275956 2047027 := bstep (se 1 (by rfl) ⟨1535270, by rfl⟩ : syracuseStep 2047027 = 3070541) B3070541
theorem B1276995 : Blo 1275956 1276995 := bstep (se 1 (by rfl) ⟨957746, by rfl⟩ : syracuseStep 1276995 = 1915493) B1915493
theorem B1915985 : Blo 1275956 1915985 := bstep (se 2 (by rfl) ⟨718494, by rfl⟩ : syracuseStep 1915985 = 1436989) B1436989
theorem B1277011 : Blo 1275956 1277011 := bstep (se 1 (by rfl) ⟨957758, by rfl⟩ : syracuseStep 1277011 = 1915517) B1915517
theorem B1277027 : Blo 1275956 1277027 := bstep (se 1 (by rfl) ⟨957770, by rfl⟩ : syracuseStep 1277027 = 1915541) B1915541
theorem B1916003 : Blo 1275956 1916003 := bstep (se 1 (by rfl) ⟨1437002, by rfl⟩ : syracuseStep 1916003 = 2874005) B2874005
theorem B2153587 : Blo 1275956 2153587 := bstep (se 1 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 2153587 = 3230381) B3230381
theorem B1277043 : Blo 1275956 1277043 := bstep (se 1 (by rfl) ⟨957782, by rfl⟩ : syracuseStep 1277043 = 1915565) B1915565
theorem B1916033 : Blo 1275956 1916033 := bstep (se 2 (by rfl) ⟨718512, by rfl⟩ : syracuseStep 1916033 = 1437025) B1437025
theorem B1277059 : Blo 1275956 1277059 := bstep (se 1 (by rfl) ⟨957794, by rfl⟩ : syracuseStep 1277059 = 1915589) B1915589
theorem B1277075 : Blo 1275956 1277075 := bstep (se 1 (by rfl) ⟨957806, by rfl⟩ : syracuseStep 1277075 = 1915613) B1915613
theorem B1916051 : Blo 1275956 1916051 := bstep (se 1 (by rfl) ⟨1437038, by rfl⟩ : syracuseStep 1916051 = 2874077) B2874077
theorem B1277091 : Blo 1275956 1277091 := bstep (se 1 (by rfl) ⟨957818, by rfl⟩ : syracuseStep 1277091 = 1915637) B1915637
theorem B4603043 : Blo 1275956 4603043 := bstep (se 1 (by rfl) ⟨3452282, by rfl⟩ : syracuseStep 4603043 = 6904565) B6904565
theorem B1916081 : Blo 1275956 1916081 := bstep (se 2 (by rfl) ⟨718530, by rfl⟩ : syracuseStep 1916081 = 1437061) B1437061
theorem B2874545 : Blo 1275956 2874545 := bstep (se 2 (by rfl) ⟨1077954, by rfl⟩ : syracuseStep 2874545 = 2155909) B2155909
theorem B1277107 : Blo 1275956 1277107 := bstep (se 1 (by rfl) ⟨957830, by rfl⟩ : syracuseStep 1277107 = 1915661) B1915661
theorem B1277123 : Blo 1275956 1277123 := bstep (se 1 (by rfl) ⟨957842, by rfl⟩ : syracuseStep 1277123 = 1915685) B1915685
theorem B1916099 : Blo 1275956 1916099 := bstep (se 1 (by rfl) ⟨1437074, by rfl⟩ : syracuseStep 1916099 = 2874149) B2874149
theorem B2874563 : Blo 1275956 2874563 := bstep (se 1 (by rfl) ⟨2155922, by rfl⟩ : syracuseStep 2874563 = 4311845) B4311845
theorem B4308173 : Blo 1275956 4308173 := bstep (se 3 (by rfl) ⟨807782, by rfl⟩ : syracuseStep 4308173 = 1615565) B1615565
theorem B2727121 : Blo 1275956 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B1277139 : Blo 1275956 1277139 := bstep (se 1 (by rfl) ⟨957854, by rfl⟩ : syracuseStep 1277139 = 1915709) B1915709
theorem B1916129 : Blo 1275956 1916129 := bstep (se 2 (by rfl) ⟨718548, by rfl⟩ : syracuseStep 1916129 = 1437097) B1437097
theorem B1277155 : Blo 1275956 1277155 := bstep (se 1 (by rfl) ⟨957866, by rfl⟩ : syracuseStep 1277155 = 1915733) B1915733
theorem B5250275 : Blo 1275956 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B9690353 : Blo 1275956 9690353 := bstep (se 2 (by rfl) ⟨3633882, by rfl⟩ : syracuseStep 9690353 = 7267765) B7267765
theorem B1277171 : Blo 1275956 1277171 := bstep (se 1 (by rfl) ⟨957878, by rfl⟩ : syracuseStep 1277171 = 1915757) B1915757
theorem B1916147 : Blo 1275956 1916147 := bstep (se 1 (by rfl) ⟨1437110, by rfl⟩ : syracuseStep 1916147 = 2874221) B2874221
theorem B2153729 : Blo 1275956 2153729 := bstep (se 2 (by rfl) ⟨807648, by rfl⟩ : syracuseStep 2153729 = 1615297) B1615297
theorem B4308227 : Blo 1275956 4308227 := bstep (se 1 (by rfl) ⟨3231170, by rfl⟩ : syracuseStep 4308227 = 6462341) B6462341
theorem B1277187 : Blo 1275956 1277187 := bstep (se 1 (by rfl) ⟨957890, by rfl⟩ : syracuseStep 1277187 = 1915781) B1915781
theorem B4979981 : Blo 1275956 4979981 := bstep (se 3 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 4979981 = 1867493) B1867493
theorem B1916177 : Blo 1275956 1916177 := bstep (se 2 (by rfl) ⟨718566, by rfl⟩ : syracuseStep 1916177 = 1437133) B1437133
theorem B1277203 : Blo 1275956 1277203 := bstep (se 1 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 1277203 = 1915805) B1915805
theorem B3636515 : Blo 1275956 3636515 := bstep (se 1 (by rfl) ⟨2727386, by rfl⟩ : syracuseStep 3636515 = 5454773) B5454773
theorem B1277219 : Blo 1275956 1277219 := bstep (se 1 (by rfl) ⟨957914, by rfl⟩ : syracuseStep 1277219 = 1915829) B1915829
theorem B1916195 : Blo 1275956 1916195 := bstep (se 1 (by rfl) ⟨1437146, by rfl⟩ : syracuseStep 1916195 = 2874293) B2874293
theorem B1277235 : Blo 1275956 1277235 := bstep (se 1 (by rfl) ⟨957926, by rfl⟩ : syracuseStep 1277235 = 1915853) B1915853
theorem B1817921 : Blo 1275956 1817921 := bstep (se 2 (by rfl) ⟨681720, by rfl⟩ : syracuseStep 1817921 = 1363441) B1363441
theorem B1916225 : Blo 1275956 1916225 := bstep (se 2 (by rfl) ⟨718584, by rfl⟩ : syracuseStep 1916225 = 1437169) B1437169
theorem B1277251 : Blo 1275956 1277251 := bstep (se 1 (by rfl) ⟨957938, by rfl⟩ : syracuseStep 1277251 = 1915877) B1915877
theorem B1277267 : Blo 1275956 1277267 := bstep (se 1 (by rfl) ⟨957950, by rfl⟩ : syracuseStep 1277267 = 1915901) B1915901
theorem B1916243 : Blo 1275956 1916243 := bstep (se 1 (by rfl) ⟨1437182, by rfl⟩ : syracuseStep 1916243 = 2874365) B2874365
theorem B1277283 : Blo 1275956 1277283 := bstep (se 1 (by rfl) ⟨957962, by rfl⟩ : syracuseStep 1277283 = 1915925) B1915925
theorem B1916273 : Blo 1275956 1916273 := bstep (se 2 (by rfl) ⟨718602, by rfl⟩ : syracuseStep 1916273 = 1437205) B1437205
theorem B1277299 : Blo 1275956 1277299 := bstep (se 1 (by rfl) ⟨957974, by rfl⟩ : syracuseStep 1277299 = 1915949) B1915949
theorem B2153857 : Blo 1275956 2153857 := bstep (se 2 (by rfl) ⟨807696, by rfl⟩ : syracuseStep 2153857 = 1615393) B1615393
theorem B1277315 : Blo 1275956 1277315 := bstep (se 1 (by rfl) ⟨957986, by rfl⟩ : syracuseStep 1277315 = 1915973) B1915973
theorem B1916291 : Blo 1275956 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B1818001 : Blo 1275956 1818001 := bstep (se 2 (by rfl) ⟨681750, by rfl⟩ : syracuseStep 1818001 = 1363501) B1363501
theorem B1277331 : Blo 1275956 1277331 := bstep (se 1 (by rfl) ⟨957998, by rfl⟩ : syracuseStep 1277331 = 1915997) B1915997
theorem B1916321 : Blo 1275956 1916321 := bstep (se 2 (by rfl) ⟨718620, by rfl⟩ : syracuseStep 1916321 = 1437241) B1437241
theorem B2153891 : Blo 1275956 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B1277347 : Blo 1275956 1277347 := bstep (se 1 (by rfl) ⟨958010, by rfl⟩ : syracuseStep 1277347 = 1916021) B1916021
theorem B1277363 : Blo 1275956 1277363 := bstep (se 1 (by rfl) ⟨958022, by rfl⟩ : syracuseStep 1277363 = 1916045) B1916045
theorem B1916339 : Blo 1275956 1916339 := bstep (se 1 (by rfl) ⟨1437254, by rfl⟩ : syracuseStep 1916339 = 2874509) B2874509
theorem B2424259 : Blo 1275956 2424259 := bstep (se 1 (by rfl) ⟨1818194, by rfl⟩ : syracuseStep 2424259 = 3636389) B3636389
theorem B1277379 : Blo 1275956 1277379 := bstep (se 1 (by rfl) ⟨958034, by rfl⟩ : syracuseStep 1277379 = 1916069) B1916069
theorem B1916369 : Blo 1275956 1916369 := bstep (se 2 (by rfl) ⟨718638, by rfl⟩ : syracuseStep 1916369 = 1437277) B1437277
theorem B1277395 : Blo 1275956 1277395 := bstep (se 1 (by rfl) ⟨958046, by rfl⟩ : syracuseStep 1277395 = 1916093) B1916093
theorem B2874833 : Blo 1275956 2874833 := bstep (se 2 (by rfl) ⟨1078062, by rfl⟩ : syracuseStep 2874833 = 2156125) B2156125
theorem B3882467 : Blo 1275956 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B1277411 : Blo 1275956 1277411 := bstep (se 1 (by rfl) ⟨958058, by rfl⟩ : syracuseStep 1277411 = 1916117) B1916117
theorem B1916387 : Blo 1275956 1916387 := bstep (se 1 (by rfl) ⟨1437290, by rfl⟩ : syracuseStep 1916387 = 2874581) B2874581
theorem B2874851 : Blo 1275956 2874851 := bstep (se 1 (by rfl) ⟨2156138, by rfl⟩ : syracuseStep 2874851 = 4312277) B4312277
theorem B2424305 : Blo 1275956 2424305 := bstep (se 2 (by rfl) ⟨909114, by rfl⟩ : syracuseStep 2424305 = 1818229) B1818229
theorem B1277427 : Blo 1275956 1277427 := bstep (se 1 (by rfl) ⟨958070, by rfl⟩ : syracuseStep 1277427 = 1916141) B1916141
theorem B1916417 : Blo 1275956 1916417 := bstep (se 2 (by rfl) ⟨718656, by rfl⟩ : syracuseStep 1916417 = 1437313) B1437313
theorem B1277443 : Blo 1275956 1277443 := bstep (se 1 (by rfl) ⟨958082, by rfl⟩ : syracuseStep 1277443 = 1916165) B1916165
theorem B6462989 : Blo 1275956 6462989 := bstep (se 3 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 6462989 = 2423621) B2423621
theorem B4308497 : Blo 1275956 4308497 := bstep (se 2 (by rfl) ⟨1615686, by rfl⟩ : syracuseStep 4308497 = 3231373) B3231373
theorem B1277459 : Blo 1275956 1277459 := bstep (se 1 (by rfl) ⟨958094, by rfl⟩ : syracuseStep 1277459 = 1916189) B1916189
theorem B1916435 : Blo 1275956 1916435 := bstep (se 1 (by rfl) ⟨1437326, by rfl⟩ : syracuseStep 1916435 = 2874653) B2874653
theorem B2072099 : Blo 1275956 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B2154019 : Blo 1275956 2154019 := bstep (se 1 (by rfl) ⟨1615514, by rfl⟩ : syracuseStep 2154019 = 3231029) B3231029
theorem B1277475 : Blo 1275956 1277475 := bstep (se 1 (by rfl) ⟨958106, by rfl⟩ : syracuseStep 1277475 = 1916213) B1916213
theorem B1916465 : Blo 1275956 1916465 := bstep (se 2 (by rfl) ⟨718674, by rfl⟩ : syracuseStep 1916465 = 1437349) B1437349
theorem B1277491 : Blo 1275956 1277491 := bstep (se 1 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 1277491 = 1916237) B1916237
theorem B1277507 : Blo 1275956 1277507 := bstep (se 1 (by rfl) ⟨958130, by rfl⟩ : syracuseStep 1277507 = 1916261) B1916261
theorem B9829957 : Blo 1275956 9829957 := bstep (se 4 (by rfl) ⟨921558, by rfl⟩ : syracuseStep 9829957 = 1843117) B1843117
theorem B1916483 : Blo 1275956 1916483 := bstep (se 1 (by rfl) ⟨1437362, by rfl⟩ : syracuseStep 1916483 = 2874725) B2874725
theorem B1277523 : Blo 1275956 1277523 := bstep (se 1 (by rfl) ⟨958142, by rfl⟩ : syracuseStep 1277523 = 1916285) B1916285
theorem B1916513 : Blo 1275956 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B2727523 : Blo 1275956 2727523 := bstep (se 1 (by rfl) ⟨2045642, by rfl⟩ : syracuseStep 2727523 = 4091285) B4091285
theorem B1277539 : Blo 1275956 1277539 := bstep (se 1 (by rfl) ⟨958154, by rfl⟩ : syracuseStep 1277539 = 1916309) B1916309
theorem B3636845 : Blo 1275956 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B1277555 : Blo 1275956 1277555 := bstep (se 1 (by rfl) ⟨958166, by rfl⟩ : syracuseStep 1277555 = 1916333) B1916333
theorem B1916531 : Blo 1275956 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B1277571 : Blo 1275956 1277571 := bstep (se 1 (by rfl) ⟨958178, by rfl⟩ : syracuseStep 1277571 = 1916357) B1916357
theorem B1916561 : Blo 1275956 1916561 := bstep (se 2 (by rfl) ⟨718710, by rfl⟩ : syracuseStep 1916561 = 1437421) B1437421
theorem B1277587 : Blo 1275956 1277587 := bstep (se 1 (by rfl) ⟨958190, by rfl⟩ : syracuseStep 1277587 = 1916381) B1916381
theorem B1277603 : Blo 1275956 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B1916579 : Blo 1275956 1916579 := bstep (se 1 (by rfl) ⟨1437434, by rfl⟩ : syracuseStep 1916579 = 2874869) B2874869
theorem B2154161 : Blo 1275956 2154161 := bstep (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) B1615621
theorem B3636913 : Blo 1275956 3636913 := bstep (se 2 (by rfl) ⟨1363842, by rfl⟩ : syracuseStep 3636913 = 2727685) B2727685
theorem B1277619 : Blo 1275956 1277619 := bstep (se 1 (by rfl) ⟨958214, by rfl⟩ : syracuseStep 1277619 = 1916429) B1916429
theorem B1941185 : Blo 1275956 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1916609 : Blo 1275956 1916609 := bstep (se 2 (by rfl) ⟨718728, by rfl⟩ : syracuseStep 1916609 = 1437457) B1437457
theorem B1277635 : Blo 1275956 1277635 := bstep (se 1 (by rfl) ⟨958226, by rfl⟩ : syracuseStep 1277635 = 1916453) B1916453
theorem B1277651 : Blo 1275956 1277651 := bstep (se 1 (by rfl) ⟨958238, by rfl⟩ : syracuseStep 1277651 = 1916477) B1916477
theorem B1916627 : Blo 1275956 1916627 := bstep (se 1 (by rfl) ⟨1437470, by rfl⟩ : syracuseStep 1916627 = 2874941) B2874941
theorem B1277667 : Blo 1275956 1277667 := bstep (se 1 (by rfl) ⟨958250, by rfl⟩ : syracuseStep 1277667 = 1916501) B1916501
theorem B1916657 : Blo 1275956 1916657 := bstep (se 2 (by rfl) ⟨718746, by rfl⟩ : syracuseStep 1916657 = 1437493) B1437493
theorem B2875121 : Blo 1275956 2875121 := bstep (se 2 (by rfl) ⟨1078170, by rfl⟩ : syracuseStep 2875121 = 2156341) B2156341
theorem B1277683 : Blo 1275956 1277683 := bstep (se 1 (by rfl) ⟨958262, by rfl⟩ : syracuseStep 1277683 = 1916525) B1916525
theorem B1277699 : Blo 1275956 1277699 := bstep (se 1 (by rfl) ⟨958274, by rfl⟩ : syracuseStep 1277699 = 1916549) B1916549
theorem B1916675 : Blo 1275956 1916675 := bstep (se 1 (by rfl) ⟨1437506, by rfl⟩ : syracuseStep 1916675 = 2875013) B2875013
theorem B2875139 : Blo 1275956 2875139 := bstep (se 1 (by rfl) ⟨2156354, by rfl⟩ : syracuseStep 2875139 = 4312709) B4312709
theorem B2424593 : Blo 1275956 2424593 := bstep (se 2 (by rfl) ⟨909222, by rfl⟩ : syracuseStep 2424593 = 1818445) B1818445
theorem B1277715 : Blo 1275956 1277715 := bstep (se 1 (by rfl) ⟨958286, by rfl⟩ : syracuseStep 1277715 = 1916573) B1916573
theorem B1916705 : Blo 1275956 1916705 := bstep (se 2 (by rfl) ⟨718764, by rfl⟩ : syracuseStep 1916705 = 1437529) B1437529
theorem B1277731 : Blo 1275956 1277731 := bstep (se 1 (by rfl) ⟨958298, by rfl⟩ : syracuseStep 1277731 = 1916597) B1916597
theorem B2154289 : Blo 1275956 2154289 := bstep (se 2 (by rfl) ⟨807858, by rfl⟩ : syracuseStep 2154289 = 1615717) B1615717
theorem B1277747 : Blo 1275956 1277747 := bstep (se 1 (by rfl) ⟨958310, by rfl⟩ : syracuseStep 1277747 = 1916621) B1916621
theorem B1916723 : Blo 1275956 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B1277763 : Blo 1275956 1277763 := bstep (se 1 (by rfl) ⟨958322, by rfl⟩ : syracuseStep 1277763 = 1916645) B1916645
theorem B1916753 : Blo 1275956 1916753 := bstep (se 2 (by rfl) ⟨718782, by rfl⟩ : syracuseStep 1916753 = 1437565) B1437565
theorem B2154323 : Blo 1275956 2154323 := bstep (se 1 (by rfl) ⟨1615742, by rfl⟩ : syracuseStep 2154323 = 3231485) B3231485
theorem B1277779 : Blo 1275956 1277779 := bstep (se 1 (by rfl) ⟨958334, by rfl⟩ : syracuseStep 1277779 = 1916669) B1916669
theorem B1277795 : Blo 1275956 1277795 := bstep (se 1 (by rfl) ⟨958346, by rfl⟩ : syracuseStep 1277795 = 1916693) B1916693
theorem B1916771 : Blo 1275956 1916771 := bstep (se 1 (by rfl) ⟨1437578, by rfl⟩ : syracuseStep 1916771 = 2875157) B2875157
theorem B1277811 : Blo 1275956 1277811 := bstep (se 1 (by rfl) ⟨958358, by rfl⟩ : syracuseStep 1277811 = 1916717) B1916717
theorem B1916801 : Blo 1275956 1916801 := bstep (se 2 (by rfl) ⟨718800, by rfl⟩ : syracuseStep 1916801 = 1437601) B1437601
theorem B1277827 : Blo 1275956 1277827 := bstep (se 1 (by rfl) ⟨958370, by rfl⟩ : syracuseStep 1277827 = 1916741) B1916741
theorem B1277843 : Blo 1275956 1277843 := bstep (se 1 (by rfl) ⟨958382, by rfl⟩ : syracuseStep 1277843 = 1916765) B1916765
theorem B1916819 : Blo 1275956 1916819 := bstep (se 1 (by rfl) ⟨1437614, by rfl⟩ : syracuseStep 1916819 = 2875229) B2875229
theorem B1277859 : Blo 1275956 1277859 := bstep (se 1 (by rfl) ⟨958394, by rfl⟩ : syracuseStep 1277859 = 1916789) B1916789
theorem B1916849 : Blo 1275956 1916849 := bstep (se 2 (by rfl) ⟨718818, by rfl⟩ : syracuseStep 1916849 = 1437637) B1437637
theorem B1277875 : Blo 1275956 1277875 := bstep (se 1 (by rfl) ⟨958406, by rfl⟩ : syracuseStep 1277875 = 1916813) B1916813
theorem B3637187 : Blo 1275956 3637187 := bstep (se 1 (by rfl) ⟨2727890, by rfl⟩ : syracuseStep 3637187 = 5455781) B5455781
theorem B1277891 : Blo 1275956 1277891 := bstep (se 1 (by rfl) ⟨958418, by rfl⟩ : syracuseStep 1277891 = 1916837) B1916837
theorem B1916867 : Blo 1275956 1916867 := bstep (se 1 (by rfl) ⟨1437650, by rfl⟩ : syracuseStep 1916867 = 2875301) B2875301
theorem B2154451 : Blo 1275956 2154451 := bstep (se 1 (by rfl) ⟨1615838, by rfl⟩ : syracuseStep 2154451 = 3231677) B3231677
theorem B1277907 : Blo 1275956 1277907 := bstep (se 1 (by rfl) ⟨958430, by rfl⟩ : syracuseStep 1277907 = 1916861) B1916861
theorem B1916897 : Blo 1275956 1916897 := bstep (se 2 (by rfl) ⟨718836, by rfl⟩ : syracuseStep 1916897 = 1437673) B1437673
theorem B1277923 : Blo 1275956 1277923 := bstep (se 1 (by rfl) ⟨958442, by rfl⟩ : syracuseStep 1277923 = 1916885) B1916885
theorem B1277939 : Blo 1275956 1277939 := bstep (se 1 (by rfl) ⟨958454, by rfl⟩ : syracuseStep 1277939 = 1916909) B1916909
theorem B1916915 : Blo 1275956 1916915 := bstep (se 1 (by rfl) ⟨1437686, by rfl⟩ : syracuseStep 1916915 = 2875373) B2875373
theorem B27631651 : Blo 1275956 27631651 := bstep (se 1 (by rfl) ⟨20723738, by rfl⟩ : syracuseStep 27631651 = 41447477) B41447477
theorem B1818713 : Blo 1275956 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B78676109 : Blo 1275956 78676109 := bstep (se 3 (by rfl) ⟨14751770, by rfl⟩ : syracuseStep 78676109 = 29503541) B29503541
theorem B2154647 : Blo 1275956 2154647 := bstep (se 1 (by rfl) ⟨1615985, by rfl⟩ : syracuseStep 2154647 = 3231971) B3231971
theorem B2425049 : Blo 1275956 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B2154775 : Blo 1275956 2154775 := bstep (se 1 (by rfl) ⟨1616081, by rfl⟩ : syracuseStep 2154775 = 3232163) B3232163
theorem B2728343 : Blo 1275956 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B6463961 : Blo 1275956 6463961 := bstep (se 2 (by rfl) ⟨2423985, by rfl⟩ : syracuseStep 6463961 = 4847971) B4847971
theorem B4309469 : Blo 1275956 4309469 := bstep (se 3 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 4309469 = 1616051) B1616051
theorem B5530115 : Blo 1275956 5530115 := bstep (se 1 (by rfl) ⟨4147586, by rfl⟩ : syracuseStep 5530115 = 8295173) B8295173
theorem B5456429 : Blo 1275956 5456429 := bstep (se 3 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 5456429 = 2046161) B2046161
theorem B3449395 : Blo 1275956 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B2425459 : Blo 1275956 2425459 := bstep (se 1 (by rfl) ⟨1819094, by rfl⟩ : syracuseStep 2425459 = 3638189) B3638189
theorem B6898355 : Blo 1275956 6898355 := bstep (se 1 (by rfl) ⟨5173766, by rfl⟩ : syracuseStep 6898355 = 10347533) B10347533
theorem B1639127 : Blo 1275956 1639127 := bstep (se 1 (by rfl) ⟨1229345, by rfl⟩ : syracuseStep 1639127 = 2458691) B2458691
theorem B1819351 : Blo 1275956 1819351 := bstep (se 1 (by rfl) ⟨1364513, by rfl⟩ : syracuseStep 1819351 = 2729027) B2729027
theorem B2302681 : Blo 1275956 2302681 := bstep (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) B1727011
theorem B3736343 : Blo 1275956 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B7275329 : Blo 1275956 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B9200459 : Blo 1275956 9200459 := bstep (se 1 (by rfl) ⟨6900344, by rfl⟩ : syracuseStep 9200459 = 13800689) B13800689
theorem B5456771 : Blo 1275956 5456771 := bstep (se 1 (by rfl) ⟨4092578, by rfl⟩ : syracuseStep 5456771 = 8185157) B8185157
theorem B2155403 : Blo 1275956 2155403 := bstep (se 1 (by rfl) ⟨1616552, by rfl⟩ : syracuseStep 2155403 = 3233105) B3233105
theorem B1532939 : Blo 1275956 1532939 := bstep (se 1 (by rfl) ⟨1149704, by rfl⟩ : syracuseStep 1532939 = 2299409) B2299409
theorem B2155531 : Blo 1275956 2155531 := bstep (se 1 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 2155531 = 3233297) B3233297
theorem B4850705 : Blo 1275956 4850705 := bstep (se 2 (by rfl) ⟨1819014, by rfl⟩ : syracuseStep 4850705 = 3638029) B3638029
theorem B2425945 : Blo 1275956 2425945 := bstep (se 2 (by rfl) ⟨909729, by rfl⟩ : syracuseStep 2425945 = 1819459) B1819459
theorem B2155673 : Blo 1275956 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B2155801 : Blo 1275956 2155801 := bstep (se 2 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 2155801 = 1616851) B1616851
theorem B8299841 : Blo 1275956 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B2131289 : Blo 1275956 2131289 := bstep (se 2 (by rfl) ⟨799233, by rfl⟩ : syracuseStep 2131289 = 1598467) B1598467
theorem B3638621 : Blo 1275956 3638621 := bstep (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) B1364483
theorem B1942937 : Blo 1275956 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B2729369 : Blo 1275956 2729369 := bstep (se 2 (by rfl) ⟨1023513, by rfl⟩ : syracuseStep 2729369 = 2047027) B2047027
theorem B4851161 : Blo 1275956 4851161 := bstep (se 2 (by rfl) ⟨1819185, by rfl⟩ : syracuseStep 4851161 = 3638371) B3638371
theorem B13985297 : Blo 1275956 13985297 := bstep (se 2 (by rfl) ⟨5244486, by rfl⟩ : syracuseStep 13985297 = 10488973) B10488973
theorem B4310603 : Blo 1275956 4310603 := bstep (se 1 (by rfl) ⟨3232952, by rfl⟩ : syracuseStep 4310603 = 6465905) B6465905
theorem B17483357 : Blo 1275956 17483357 := bstep (se 3 (by rfl) ⟨3278129, by rfl⟩ : syracuseStep 17483357 = 6556259) B6556259
theorem B4851373 : Blo 1275956 4851373 := bstep (se 3 (by rfl) ⟨909632, by rfl⟩ : syracuseStep 4851373 = 1819265) B1819265
theorem B16353089 : Blo 1275956 16353089 := bstep (se 2 (by rfl) ⟨6132408, by rfl⟩ : syracuseStep 16353089 = 12264817) B12264817
theorem B2156375 : Blo 1275956 2156375 := bstep (se 1 (by rfl) ⟨1617281, by rfl⟩ : syracuseStep 2156375 = 3234563) B3234563
theorem B4310873 : Blo 1275956 4310873 := bstep (se 2 (by rfl) ⟨1616577, by rfl⟩ : syracuseStep 4310873 = 3233155) B3233155
theorem B7374685 : Blo 1275956 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B20711285 : Blo 1275956 20711285 := bstep (se 5 (by rfl) ⟨970841, by rfl⟩ : syracuseStep 20711285 = 1941683) B1941683
theorem B10905475 : Blo 1275956 10905475 := bstep (se 1 (by rfl) ⟨8179106, by rfl⟩ : syracuseStep 10905475 = 16358213) B16358213
theorem B1435531 : Blo 1275956 1435531 := bstep (se 1 (by rfl) ⟨1076648, by rfl⟩ : syracuseStep 1435531 = 2153297) B2153297
theorem B2156503 : Blo 1275956 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B4851677 : Blo 1275956 4851677 := bstep (se 3 (by rfl) ⟨909689, by rfl⟩ : syracuseStep 4851677 = 1819379) B1819379
theorem B1435639 : Blo 1275956 1435639 := bstep (se 1 (by rfl) ⟨1076729, by rfl⟩ : syracuseStep 1435639 = 2153459) B2153459
theorem B8185873 : Blo 1275956 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B6465581 : Blo 1275956 6465581 := bstep (se 3 (by rfl) ⟨1212296, by rfl⟩ : syracuseStep 6465581 = 2424593) B2424593
theorem B3500183 : Blo 1275956 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B1435819 : Blo 1275956 1435819 := bstep (se 1 (by rfl) ⟨1076864, by rfl⟩ : syracuseStep 1435819 = 2153729) B2153729
theorem B3319987 : Blo 1275956 3319987 := bstep (se 1 (by rfl) ⟨2489990, by rfl⟩ : syracuseStep 3319987 = 4979981) B4979981
theorem B1435927 : Blo 1275956 1435927 := bstep (se 1 (by rfl) ⟨1076945, by rfl⟩ : syracuseStep 1435927 = 2153891) B2153891
theorem B3230027 : Blo 1275956 3230027 := bstep (se 1 (by rfl) ⟨2422520, by rfl⟩ : syracuseStep 3230027 = 4845041) B4845041
theorem B1616203 : Blo 1275956 1616203 := bstep (se 1 (by rfl) ⟨1212152, by rfl⟩ : syracuseStep 1616203 = 2424305) B2424305
theorem B1436107 : Blo 1275956 1436107 := bstep (se 1 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 1436107 = 2154161) B2154161
theorem B4311575 : Blo 1275956 4311575 := bstep (se 1 (by rfl) ⟨3233681, by rfl⟩ : syracuseStep 4311575 = 6467363) B6467363
theorem B1436215 : Blo 1275956 1436215 := bstep (se 1 (by rfl) ⟨1077161, by rfl⟩ : syracuseStep 1436215 = 2154323) B2154323
theorem B5179993 : Blo 1275956 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B3230401 : Blo 1275956 3230401 := bstep (se 2 (by rfl) ⟨1211400, by rfl⟩ : syracuseStep 3230401 = 2422801) B2422801
theorem B1436395 : Blo 1275956 1436395 := bstep (se 1 (by rfl) ⟨1077296, by rfl⟩ : syracuseStep 1436395 = 2154593) B2154593
theorem B16583429 : Blo 1275956 16583429 := bstep (se 4 (by rfl) ⟨1554696, by rfl⟩ : syracuseStep 16583429 = 3109393) B3109393
theorem B10906433 : Blo 1275956 10906433 := bstep (se 2 (by rfl) ⟨4089912, by rfl⟩ : syracuseStep 10906433 = 8179825) B8179825
theorem B1436503 : Blo 1275956 1436503 := bstep (se 1 (by rfl) ⟨1077377, by rfl⟩ : syracuseStep 1436503 = 2154755) B2154755
theorem B40381361 : Blo 1275956 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B31075289 : Blo 1275956 31075289 := bstep (se 2 (by rfl) ⟨11653233, by rfl⟩ : syracuseStep 31075289 = 23306467) B23306467
theorem B1436683 : Blo 1275956 1436683 := bstep (se 1 (by rfl) ⟨1077512, by rfl⟩ : syracuseStep 1436683 = 2155025) B2155025
theorem B4312115 : Blo 1275956 4312115 := bstep (se 1 (by rfl) ⟨3234086, by rfl⟩ : syracuseStep 4312115 = 6468173) B6468173
theorem B1436791 : Blo 1275956 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B11209859 : Blo 1275956 11209859 := bstep (se 1 (by rfl) ⟨8407394, by rfl⟩ : syracuseStep 11209859 = 16814789) B16814789
theorem B15535309 : Blo 1275956 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B1363159 : Blo 1275956 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B3230999 : Blo 1275956 3230999 := bstep (se 1 (by rfl) ⟨2423249, by rfl⟩ : syracuseStep 3230999 = 4846499) B4846499
theorem B1617175 : Blo 1275956 1617175 := bstep (se 1 (by rfl) ⟨1212881, by rfl⟩ : syracuseStep 1617175 = 2425763) B2425763
theorem B1436971 : Blo 1275956 1436971 := bstep (se 1 (by rfl) ⟨1077728, by rfl⟩ : syracuseStep 1436971 = 2155457) B2155457
theorem B4312385 : Blo 1275956 4312385 := bstep (se 2 (by rfl) ⟨1617144, by rfl⟩ : syracuseStep 4312385 = 3234289) B3234289
theorem B5451083 : Blo 1275956 5451083 := bstep (se 1 (by rfl) ⟨4088312, by rfl⟩ : syracuseStep 5451083 = 8176625) B8176625
theorem B1437079 : Blo 1275956 1437079 := bstep (se 1 (by rfl) ⟨1077809, by rfl⟩ : syracuseStep 1437079 = 2155619) B2155619
theorem B13102667 : Blo 1275956 13102667 := bstep (se 1 (by rfl) ⟨9827000, by rfl⟩ : syracuseStep 13102667 = 19654001) B19654001
theorem B1437259 : Blo 1275956 1437259 := bstep (se 1 (by rfl) ⟨1077944, by rfl⟩ : syracuseStep 1437259 = 2155889) B2155889
theorem B2870963 : Blo 1275956 2870963 := bstep (se 1 (by rfl) ⟨2153222, by rfl⟩ : syracuseStep 2870963 = 4306445) B4306445
theorem B1437367 : Blo 1275956 1437367 := bstep (se 1 (by rfl) ⟨1078025, by rfl⟩ : syracuseStep 1437367 = 2156051) B2156051
theorem B2870999 : Blo 1275956 2870999 := bstep (se 1 (by rfl) ⟨2153249, by rfl⟩ : syracuseStep 2870999 = 4306499) B4306499
theorem B36802289 : Blo 1275956 36802289 := bstep (se 2 (by rfl) ⟨13800858, by rfl⟩ : syracuseStep 36802289 = 27601717) B27601717
theorem B4845329 : Blo 1275956 4845329 := bstep (se 2 (by rfl) ⟨1816998, by rfl⟩ : syracuseStep 4845329 = 3633997) B3633997
theorem B2952983 : Blo 1275956 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B5246795 : Blo 1275956 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B3067723 : Blo 1275956 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B4312925 : Blo 1275956 4312925 := bstep (se 3 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 4312925 = 1617347) B1617347
theorem B18665315 : Blo 1275956 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B1437547 : Blo 1275956 1437547 := bstep (se 1 (by rfl) ⟨1078160, by rfl⟩ : syracuseStep 1437547 = 2156321) B2156321
theorem B2871179 : Blo 1275956 2871179 := bstep (se 1 (by rfl) ⟨2153384, by rfl⟩ : syracuseStep 2871179 = 4306769) B4306769
theorem B2871233 : Blo 1275956 2871233 := bstep (se 2 (by rfl) ⟨1076712, by rfl⟩ : syracuseStep 2871233 = 2153425) B2153425
theorem B1437655 : Blo 1275956 1437655 := bstep (se 1 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 1437655 = 2156483) B2156483
theorem B3231809 : Blo 1275956 3231809 := bstep (se 2 (by rfl) ⟨1211928, by rfl⟩ : syracuseStep 3231809 = 2423857) B2423857
theorem B1724503 : Blo 1275956 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B5525597 : Blo 1275956 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B2871449 : Blo 1275956 2871449 := bstep (se 2 (by rfl) ⟨1076793, by rfl⟩ : syracuseStep 2871449 = 2153587) B2153587
theorem B2871539 : Blo 1275956 2871539 := bstep (se 1 (by rfl) ⟨2153654, by rfl⟩ : syracuseStep 2871539 = 4307309) B4307309
theorem B2871575 : Blo 1275956 2871575 := bstep (se 1 (by rfl) ⟨2153681, by rfl⟩ : syracuseStep 2871575 = 4307363) B4307363
theorem B5452055 : Blo 1275956 5452055 := bstep (se 1 (by rfl) ⟨4089041, by rfl⟩ : syracuseStep 5452055 = 8178083) B8178083
theorem B4846027 : Blo 1275956 4846027 := bstep (se 1 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 4846027 = 7269041) B7269041
theorem B2871755 : Blo 1275956 2871755 := bstep (se 1 (by rfl) ⟨2153816, by rfl⟩ : syracuseStep 2871755 = 4307633) B4307633
theorem B2871809 : Blo 1275956 2871809 := bstep (se 2 (by rfl) ⟨1076928, by rfl⟩ : syracuseStep 2871809 = 2153857) B2153857
theorem B4731409 : Blo 1275956 4731409 := bstep (se 2 (by rfl) ⟨1774278, by rfl⟩ : syracuseStep 4731409 = 3548557) B3548557
theorem B3232345 : Blo 1275956 3232345 := bstep (se 2 (by rfl) ⟨1212129, by rfl⟩ : syracuseStep 3232345 = 2424259) B2424259
theorem B3633815 : Blo 1275956 3633815 := bstep (se 1 (by rfl) ⟨2725361, by rfl⟩ : syracuseStep 3633815 = 5450723) B5450723
theorem B2872025 : Blo 1275956 2872025 := bstep (se 2 (by rfl) ⟨1077009, by rfl⟩ : syracuseStep 2872025 = 2154019) B2154019
theorem B4846301 : Blo 1275956 4846301 := bstep (se 3 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 4846301 = 1817363) B1817363
theorem B3068695 : Blo 1275956 3068695 := bstep (se 1 (by rfl) ⟨2301521, by rfl⟩ : syracuseStep 3068695 = 4603043) B4603043
theorem B2872115 : Blo 1275956 2872115 := bstep (se 1 (by rfl) ⟨2154086, by rfl⟩ : syracuseStep 2872115 = 4308173) B4308173
theorem B6460235 : Blo 1275956 6460235 := bstep (se 1 (by rfl) ⟨4845176, by rfl⟩ : syracuseStep 6460235 = 9690353) B9690353
theorem B2872151 : Blo 1275956 2872151 := bstep (se 1 (by rfl) ⟨2154113, by rfl⟩ : syracuseStep 2872151 = 4308227) B4308227
theorem B2872331 : Blo 1275956 2872331 := bstep (se 1 (by rfl) ⟨2154248, by rfl⟩ : syracuseStep 2872331 = 4308497) B4308497
theorem B11646017 : Blo 1275956 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B2872385 : Blo 1275956 2872385 := bstep (se 2 (by rfl) ⟨1077144, by rfl⟩ : syracuseStep 2872385 = 2154289) B2154289
theorem B1913945 : Blo 1275956 1913945 := bstep (se 2 (by rfl) ⟨717729, by rfl⟩ : syracuseStep 1913945 = 1435459) B1435459
theorem B10916957 : Blo 1275956 10916957 := bstep (se 3 (by rfl) ⟨2046929, by rfl⟩ : syracuseStep 10916957 = 4093859) B4093859
theorem B1914059 : Blo 1275956 1914059 := bstep (se 1 (by rfl) ⟨1435544, by rfl⟩ : syracuseStep 1914059 = 2871089) B2871089
theorem B19657933 : Blo 1275956 19657933 := bstep (se 3 (by rfl) ⟨3685862, by rfl⟩ : syracuseStep 19657933 = 7371725) B7371725
theorem B1914071 : Blo 1275956 1914071 := bstep (se 1 (by rfl) ⟨1435553, by rfl⟩ : syracuseStep 1914071 = 2871107) B2871107
theorem B5174545 : Blo 1275956 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B1914137 : Blo 1275956 1914137 := bstep (se 2 (by rfl) ⟨717801, by rfl⟩ : syracuseStep 1914137 = 1435603) B1435603
theorem B2872601 : Blo 1275956 2872601 := bstep (se 2 (by rfl) ⟨1077225, by rfl⟩ : syracuseStep 2872601 = 2154451) B2154451
theorem B5174579 : Blo 1275956 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B21804389 : Blo 1275956 21804389 := bstep (se 4 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 21804389 = 4088323) B4088323
theorem B2872691 : Blo 1275956 2872691 := bstep (se 1 (by rfl) ⟨2154518, by rfl⟩ : syracuseStep 2872691 = 4309037) B4309037
theorem B1914251 : Blo 1275956 1914251 := bstep (se 1 (by rfl) ⟨1435688, by rfl⟩ : syracuseStep 1914251 = 2871377) B2871377
theorem B1914263 : Blo 1275956 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B4846999 : Blo 1275956 4846999 := bstep (se 1 (by rfl) ⟨3635249, by rfl⟩ : syracuseStep 4846999 = 7270499) B7270499
theorem B2872727 : Blo 1275956 2872727 := bstep (se 1 (by rfl) ⟨2154545, by rfl⟩ : syracuseStep 2872727 = 4309091) B4309091
theorem B2045387 : Blo 1275956 2045387 := bstep (se 1 (by rfl) ⟨1534040, by rfl⟩ : syracuseStep 2045387 = 3068081) B3068081
theorem B1914329 : Blo 1275956 1914329 := bstep (se 2 (by rfl) ⟨717873, by rfl⟩ : syracuseStep 1914329 = 1435747) B1435747
theorem B1914443 : Blo 1275956 1914443 := bstep (se 1 (by rfl) ⟨1435832, by rfl⟩ : syracuseStep 1914443 = 2871665) B2871665
theorem B2872907 : Blo 1275956 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B1914455 : Blo 1275956 1914455 := bstep (se 1 (by rfl) ⟨1435841, by rfl⟩ : syracuseStep 1914455 = 2871683) B2871683
theorem B2422361 : Blo 1275956 2422361 := bstep (se 2 (by rfl) ⟨908385, by rfl⟩ : syracuseStep 2422361 = 1816771) B1816771
theorem B2872961 : Blo 1275956 2872961 := bstep (se 2 (by rfl) ⟨1077360, by rfl⟩ : syracuseStep 2872961 = 2154721) B2154721
theorem B58947203 : Blo 1275956 58947203 := bstep (se 1 (by rfl) ⟨44210402, by rfl⟩ : syracuseStep 58947203 = 88420805) B88420805
theorem B11646595 : Blo 1275956 11646595 := bstep (se 1 (by rfl) ⟨8734946, by rfl⟩ : syracuseStep 11646595 = 17469893) B17469893
theorem B1914521 : Blo 1275956 1914521 := bstep (se 2 (by rfl) ⟨717945, by rfl⟩ : syracuseStep 1914521 = 1435891) B1435891
theorem B3233459 : Blo 1275956 3233459 := bstep (se 1 (by rfl) ⟨2425094, by rfl⟩ : syracuseStep 3233459 = 4850189) B4850189
theorem B2660057 : Blo 1275956 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B1914635 : Blo 1275956 1914635 := bstep (se 1 (by rfl) ⟨1435976, by rfl⟩ : syracuseStep 1914635 = 2871953) B2871953
theorem B1914647 : Blo 1275956 1914647 := bstep (se 1 (by rfl) ⟨1435985, by rfl⟩ : syracuseStep 1914647 = 2871971) B2871971
theorem B1914713 : Blo 1275956 1914713 := bstep (se 2 (by rfl) ⟨718017, by rfl⟩ : syracuseStep 1914713 = 1436035) B1436035
theorem B2873177 : Blo 1275956 2873177 := bstep (se 2 (by rfl) ⟨1077441, by rfl⟩ : syracuseStep 2873177 = 2154883) B2154883
theorem B6469469 : Blo 1275956 6469469 := bstep (se 3 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 6469469 = 2426051) B2426051
theorem B2873267 : Blo 1275956 2873267 := bstep (se 1 (by rfl) ⟨2154950, by rfl⟩ : syracuseStep 2873267 = 4309901) B4309901
theorem B1914827 : Blo 1275956 1914827 := bstep (se 1 (by rfl) ⟨1436120, by rfl⟩ : syracuseStep 1914827 = 2872241) B2872241
theorem B1914839 : Blo 1275956 1914839 := bstep (se 1 (by rfl) ⟨1436129, by rfl⟩ : syracuseStep 1914839 = 2872259) B2872259
theorem B2873303 : Blo 1275956 2873303 := bstep (se 1 (by rfl) ⟨2154977, by rfl⟩ : syracuseStep 2873303 = 4309955) B4309955
theorem B3233753 : Blo 1275956 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B1914905 : Blo 1275956 1914905 := bstep (se 2 (by rfl) ⟨718089, by rfl⟩ : syracuseStep 1914905 = 1436179) B1436179
theorem B1275959 : Blo 1275956 1275959 := bstep (se 1 (by rfl) ⟨956969, by rfl⟩ : syracuseStep 1275959 = 1913939) B1913939
theorem B1275979 : Blo 1275956 1275979 := bstep (se 1 (by rfl) ⟨956984, by rfl⟩ : syracuseStep 1275979 = 1913969) B1913969
theorem B1275991 : Blo 1275956 1275991 := bstep (se 1 (by rfl) ⟨956993, by rfl⟩ : syracuseStep 1275991 = 1913987) B1913987
theorem B10106981 : Blo 1275956 10106981 := bstep (se 4 (by rfl) ⟨947529, by rfl⟩ : syracuseStep 10106981 = 1895059) B1895059
theorem B1276011 : Blo 1275956 1276011 := bstep (se 1 (by rfl) ⟨957008, by rfl⟩ : syracuseStep 1276011 = 1914017) B1914017
theorem B1276023 : Blo 1275956 1276023 := bstep (se 1 (by rfl) ⟨957017, by rfl⟩ : syracuseStep 1276023 = 1914035) B1914035
theorem B1276043 : Blo 1275956 1276043 := bstep (se 1 (by rfl) ⟨957032, by rfl⟩ : syracuseStep 1276043 = 1914065) B1914065
theorem B1915019 : Blo 1275956 1915019 := bstep (se 1 (by rfl) ⟨1436264, by rfl⟩ : syracuseStep 1915019 = 2872529) B2872529
theorem B2873483 : Blo 1275956 2873483 := bstep (se 1 (by rfl) ⟨2155112, by rfl⟩ : syracuseStep 2873483 = 4310225) B4310225
theorem B1276055 : Blo 1275956 1276055 := bstep (se 1 (by rfl) ⟨957041, by rfl⟩ : syracuseStep 1276055 = 1914083) B1914083
theorem B1915031 : Blo 1275956 1915031 := bstep (se 1 (by rfl) ⟨1436273, by rfl⟩ : syracuseStep 1915031 = 2872547) B2872547
theorem B2455705 : Blo 1275956 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1276075 : Blo 1275956 1276075 := bstep (se 1 (by rfl) ⟨957056, by rfl⟩ : syracuseStep 1276075 = 1914113) B1914113
theorem B4847789 : Blo 1275956 4847789 := bstep (se 3 (by rfl) ⟨908960, by rfl⟩ : syracuseStep 4847789 = 1817921) B1817921
theorem B3938483 : Blo 1275956 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B1276087 : Blo 1275956 1276087 := bstep (se 1 (by rfl) ⟨957065, by rfl⟩ : syracuseStep 1276087 = 1914131) B1914131
theorem B2873537 : Blo 1275956 2873537 := bstep (se 2 (by rfl) ⟨1077576, by rfl⟩ : syracuseStep 2873537 = 2155153) B2155153
theorem B1276107 : Blo 1275956 1276107 := bstep (se 1 (by rfl) ⟨957080, by rfl⟩ : syracuseStep 1276107 = 1914161) B1914161
theorem B4307147 : Blo 1275956 4307147 := bstep (se 1 (by rfl) ⟨3230360, by rfl⟩ : syracuseStep 4307147 = 6460721) B6460721
theorem B1276119 : Blo 1275956 1276119 := bstep (se 1 (by rfl) ⟨957089, by rfl⟩ : syracuseStep 1276119 = 1914179) B1914179
theorem B1915097 : Blo 1275956 1915097 := bstep (se 2 (by rfl) ⟨718161, by rfl⟩ : syracuseStep 1915097 = 1436323) B1436323
theorem B7272665 : Blo 1275956 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B1276139 : Blo 1275956 1276139 := bstep (se 1 (by rfl) ⟨957104, by rfl⟩ : syracuseStep 1276139 = 1914209) B1914209
theorem B1456363 : Blo 1275956 1456363 := bstep (se 1 (by rfl) ⟨1092272, by rfl⟩ : syracuseStep 1456363 = 2184545) B2184545
theorem B1276151 : Blo 1275956 1276151 := bstep (se 1 (by rfl) ⟨957113, by rfl⟩ : syracuseStep 1276151 = 1914227) B1914227
theorem B1276171 : Blo 1275956 1276171 := bstep (se 1 (by rfl) ⟨957128, by rfl⟩ : syracuseStep 1276171 = 1914257) B1914257
theorem B1276183 : Blo 1275956 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B1276203 : Blo 1275956 1276203 := bstep (se 1 (by rfl) ⟨957152, by rfl⟩ : syracuseStep 1276203 = 1914305) B1914305
theorem B6904109 : Blo 1275956 6904109 := bstep (se 3 (by rfl) ⟨1294520, by rfl⟩ : syracuseStep 6904109 = 2589041) B2589041
theorem B1276215 : Blo 1275956 1276215 := bstep (se 1 (by rfl) ⟨957161, by rfl⟩ : syracuseStep 1276215 = 1914323) B1914323
theorem B2423105 : Blo 1275956 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B1276235 : Blo 1275956 1276235 := bstep (se 1 (by rfl) ⟨957176, by rfl⟩ : syracuseStep 1276235 = 1914353) B1914353
theorem B1915211 : Blo 1275956 1915211 := bstep (se 1 (by rfl) ⟨1436408, by rfl⟩ : syracuseStep 1915211 = 2872817) B2872817
theorem B1276247 : Blo 1275956 1276247 := bstep (se 1 (by rfl) ⟨957185, by rfl⟩ : syracuseStep 1276247 = 1914371) B1914371
theorem B1915223 : Blo 1275956 1915223 := bstep (se 1 (by rfl) ⟨1436417, by rfl⟩ : syracuseStep 1915223 = 2872835) B2872835
theorem B1276267 : Blo 1275956 1276267 := bstep (se 1 (by rfl) ⟨957200, by rfl⟩ : syracuseStep 1276267 = 1914401) B1914401
theorem B1276279 : Blo 1275956 1276279 := bstep (se 1 (by rfl) ⟨957209, by rfl⟩ : syracuseStep 1276279 = 1914419) B1914419
theorem B1276299 : Blo 1275956 1276299 := bstep (se 1 (by rfl) ⟨957224, by rfl⟩ : syracuseStep 1276299 = 1914449) B1914449
theorem B1276311 : Blo 1275956 1276311 := bstep (se 1 (by rfl) ⟨957233, by rfl⟩ : syracuseStep 1276311 = 1914467) B1914467
theorem B1915289 : Blo 1275956 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B2873753 : Blo 1275956 2873753 := bstep (se 2 (by rfl) ⟨1077657, by rfl⟩ : syracuseStep 2873753 = 2155315) B2155315
theorem B1276331 : Blo 1275956 1276331 := bstep (se 1 (by rfl) ⟨957248, by rfl⟩ : syracuseStep 1276331 = 1914497) B1914497
theorem B1456555 : Blo 1275956 1456555 := bstep (se 1 (by rfl) ⟨1092416, by rfl⟩ : syracuseStep 1456555 = 2184833) B2184833
theorem B1276343 : Blo 1275956 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B1276363 : Blo 1275956 1276363 := bstep (se 1 (by rfl) ⟨957272, by rfl⟩ : syracuseStep 1276363 = 1914545) B1914545
theorem B1276375 : Blo 1275956 1276375 := bstep (se 1 (by rfl) ⟨957281, by rfl⟩ : syracuseStep 1276375 = 1914563) B1914563
theorem B4307417 : Blo 1275956 4307417 := bstep (se 2 (by rfl) ⟨1615281, by rfl⟩ : syracuseStep 4307417 = 3230563) B3230563
theorem B1276395 : Blo 1275956 1276395 := bstep (se 1 (by rfl) ⟨957296, by rfl⟩ : syracuseStep 1276395 = 1914593) B1914593
theorem B2873843 : Blo 1275956 2873843 := bstep (se 1 (by rfl) ⟨2155382, by rfl⟩ : syracuseStep 2873843 = 4310765) B4310765
theorem B1276407 : Blo 1275956 1276407 := bstep (se 1 (by rfl) ⟨957305, by rfl⟩ : syracuseStep 1276407 = 1914611) B1914611
theorem B1276427 : Blo 1275956 1276427 := bstep (se 1 (by rfl) ⟨957320, by rfl⟩ : syracuseStep 1276427 = 1914641) B1914641
theorem B1915403 : Blo 1275956 1915403 := bstep (se 1 (by rfl) ⟨1436552, by rfl⟩ : syracuseStep 1915403 = 2873105) B2873105
theorem B1276439 : Blo 1275956 1276439 := bstep (se 1 (by rfl) ⟨957329, by rfl⟩ : syracuseStep 1276439 = 1914659) B1914659
theorem B1915415 : Blo 1275956 1915415 := bstep (se 1 (by rfl) ⟨1436561, by rfl⟩ : syracuseStep 1915415 = 2873123) B2873123
theorem B2873879 : Blo 1275956 2873879 := bstep (se 1 (by rfl) ⟨2155409, by rfl⟩ : syracuseStep 2873879 = 4310819) B4310819
theorem B1276459 : Blo 1275956 1276459 := bstep (se 1 (by rfl) ⟨957344, by rfl⟩ : syracuseStep 1276459 = 1914689) B1914689
theorem B1276471 : Blo 1275956 1276471 := bstep (se 1 (by rfl) ⟨957353, by rfl⟩ : syracuseStep 1276471 = 1914707) B1914707
theorem B6462017 : Blo 1275956 6462017 := bstep (se 2 (by rfl) ⟨2423256, by rfl⟩ : syracuseStep 6462017 = 4846513) B4846513
theorem B1276491 : Blo 1275956 1276491 := bstep (se 1 (by rfl) ⟨957368, by rfl⟩ : syracuseStep 1276491 = 1914737) B1914737
theorem B2423371 : Blo 1275956 2423371 := bstep (se 1 (by rfl) ⟨1817528, by rfl⟩ : syracuseStep 2423371 = 3635057) B3635057
theorem B1276503 : Blo 1275956 1276503 := bstep (se 1 (by rfl) ⟨957377, by rfl⟩ : syracuseStep 1276503 = 1914755) B1914755
theorem B1915481 : Blo 1275956 1915481 := bstep (se 2 (by rfl) ⟨718305, by rfl⟩ : syracuseStep 1915481 = 1436611) B1436611
theorem B1276523 : Blo 1275956 1276523 := bstep (se 1 (by rfl) ⟨957392, by rfl⟩ : syracuseStep 1276523 = 1914785) B1914785
theorem B1276535 : Blo 1275956 1276535 := bstep (se 1 (by rfl) ⟨957401, by rfl⟩ : syracuseStep 1276535 = 1914803) B1914803
theorem B16366211 : Blo 1275956 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B1276555 : Blo 1275956 1276555 := bstep (se 1 (by rfl) ⟨957416, by rfl⟩ : syracuseStep 1276555 = 1914833) B1914833
theorem B1276567 : Blo 1275956 1276567 := bstep (se 1 (by rfl) ⟨957425, by rfl⟩ : syracuseStep 1276567 = 1914851) B1914851
theorem B2046617 : Blo 1275956 2046617 := bstep (se 2 (by rfl) ⟨767481, by rfl⟩ : syracuseStep 2046617 = 1534963) B1534963
theorem B1276587 : Blo 1275956 1276587 := bstep (se 1 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 1276587 = 1914881) B1914881
theorem B5454515 : Blo 1275956 5454515 := bstep (se 1 (by rfl) ⟨4090886, by rfl⟩ : syracuseStep 5454515 = 8181773) B8181773
theorem B1276599 : Blo 1275956 1276599 := bstep (se 1 (by rfl) ⟨957449, by rfl⟩ : syracuseStep 1276599 = 1914899) B1914899
theorem B1276619 : Blo 1275956 1276619 := bstep (se 1 (by rfl) ⟨957464, by rfl⟩ : syracuseStep 1276619 = 1914929) B1914929
theorem B1915595 : Blo 1275956 1915595 := bstep (se 1 (by rfl) ⟨1436696, by rfl⟩ : syracuseStep 1915595 = 2873393) B2873393
theorem B2874059 : Blo 1275956 2874059 := bstep (se 1 (by rfl) ⟨2155544, by rfl⟩ : syracuseStep 2874059 = 4311089) B4311089
theorem B1276631 : Blo 1275956 1276631 := bstep (se 1 (by rfl) ⟨957473, by rfl⟩ : syracuseStep 1276631 = 1914947) B1914947
theorem B1915607 : Blo 1275956 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B1276651 : Blo 1275956 1276651 := bstep (se 1 (by rfl) ⟨957488, by rfl⟩ : syracuseStep 1276651 = 1914977) B1914977
theorem B1276663 : Blo 1275956 1276663 := bstep (se 1 (by rfl) ⟨957497, by rfl⟩ : syracuseStep 1276663 = 1914995) B1914995
theorem B2874113 : Blo 1275956 2874113 := bstep (se 2 (by rfl) ⟨1077792, by rfl⟩ : syracuseStep 2874113 = 2155585) B2155585
theorem B2587403 : Blo 1275956 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B1276683 : Blo 1275956 1276683 := bstep (se 1 (by rfl) ⟨957512, by rfl⟩ : syracuseStep 1276683 = 1915025) B1915025
theorem B1276695 : Blo 1275956 1276695 := bstep (se 1 (by rfl) ⟨957521, by rfl⟩ : syracuseStep 1276695 = 1915043) B1915043
theorem B1915673 : Blo 1275956 1915673 := bstep (se 2 (by rfl) ⟨718377, by rfl⟩ : syracuseStep 1915673 = 1436755) B1436755
theorem B1276715 : Blo 1275956 1276715 := bstep (se 1 (by rfl) ⟨957536, by rfl⟩ : syracuseStep 1276715 = 1915073) B1915073
theorem B1276727 : Blo 1275956 1276727 := bstep (se 1 (by rfl) ⟨957545, by rfl⟩ : syracuseStep 1276727 = 1915091) B1915091
theorem B1276747 : Blo 1275956 1276747 := bstep (se 1 (by rfl) ⟨957560, by rfl⟩ : syracuseStep 1276747 = 1915121) B1915121
theorem B1276759 : Blo 1275956 1276759 := bstep (se 1 (by rfl) ⟨957569, by rfl⟩ : syracuseStep 1276759 = 1915139) B1915139
theorem B1276779 : Blo 1275956 1276779 := bstep (se 1 (by rfl) ⟨957584, by rfl⟩ : syracuseStep 1276779 = 1915169) B1915169
theorem B1276791 : Blo 1275956 1276791 := bstep (se 1 (by rfl) ⟨957593, by rfl⟩ : syracuseStep 1276791 = 1915187) B1915187
theorem B1276811 : Blo 1275956 1276811 := bstep (se 1 (by rfl) ⟨957608, by rfl⟩ : syracuseStep 1276811 = 1915217) B1915217
theorem B1915787 : Blo 1275956 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B1276823 : Blo 1275956 1276823 := bstep (se 1 (by rfl) ⟨957617, by rfl⟩ : syracuseStep 1276823 = 1915235) B1915235
theorem B1915799 : Blo 1275956 1915799 := bstep (se 1 (by rfl) ⟨1436849, by rfl⟩ : syracuseStep 1915799 = 2873699) B2873699
theorem B1276843 : Blo 1275956 1276843 := bstep (se 1 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 1276843 = 1915265) B1915265
theorem B1276855 : Blo 1275956 1276855 := bstep (se 1 (by rfl) ⟨957641, by rfl⟩ : syracuseStep 1276855 = 1915283) B1915283
theorem B3636161 : Blo 1275956 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B1276875 : Blo 1275956 1276875 := bstep (se 1 (by rfl) ⟨957656, by rfl⟩ : syracuseStep 1276875 = 1915313) B1915313
theorem B1277943 : Blo 1275956 1277943 := bstep (se 1 (by rfl) ⟨958457, by rfl⟩ : syracuseStep 1277943 = 1916915) B1916915
theorem B1276887 : Blo 1275956 1276887 := bstep (se 1 (by rfl) ⟨957665, by rfl⟩ : syracuseStep 1276887 = 1915331) B1915331
theorem B1915865 : Blo 1275956 1915865 := bstep (se 2 (by rfl) ⟨718449, by rfl⟩ : syracuseStep 1915865 = 1436899) B1436899
theorem B2874329 : Blo 1275956 2874329 := bstep (se 2 (by rfl) ⟨1077873, by rfl⟩ : syracuseStep 2874329 = 2155747) B2155747
theorem B1276907 : Blo 1275956 1276907 := bstep (se 1 (by rfl) ⟨957680, by rfl⟩ : syracuseStep 1276907 = 1915361) B1915361
theorem B2333683 : Blo 1275956 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B1276919 : Blo 1275956 1276919 := bstep (se 1 (by rfl) ⟨957689, by rfl⟩ : syracuseStep 1276919 = 1915379) B1915379
theorem B2423819 : Blo 1275956 2423819 := bstep (se 1 (by rfl) ⟨1817864, by rfl⟩ : syracuseStep 2423819 = 3635729) B3635729
theorem B1276939 : Blo 1275956 1276939 := bstep (se 1 (by rfl) ⟨957704, by rfl⟩ : syracuseStep 1276939 = 1915409) B1915409
theorem B14736401 : Blo 1275956 14736401 := bstep (se 2 (by rfl) ⟨5526150, by rfl⟩ : syracuseStep 14736401 = 11052301) B11052301
theorem B2300951 : Blo 1275956 2300951 := bstep (se 1 (by rfl) ⟨1725713, by rfl⟩ : syracuseStep 2300951 = 3451427) B3451427
theorem B1276951 : Blo 1275956 1276951 := bstep (se 1 (by rfl) ⟨957713, by rfl⟩ : syracuseStep 1276951 = 1915427) B1915427
theorem B1276971 : Blo 1275956 1276971 := bstep (se 1 (by rfl) ⟨957728, by rfl⟩ : syracuseStep 1276971 = 1915457) B1915457
theorem B2874419 : Blo 1275956 2874419 := bstep (se 1 (by rfl) ⟨2155814, by rfl⟩ : syracuseStep 2874419 = 4311629) B4311629
theorem B1276983 : Blo 1275956 1276983 := bstep (se 1 (by rfl) ⟨957737, by rfl⟩ : syracuseStep 1276983 = 1915475) B1915475
theorem B1277003 : Blo 1275956 1277003 := bstep (se 1 (by rfl) ⟨957752, by rfl⟩ : syracuseStep 1277003 = 1915505) B1915505
theorem B1915979 : Blo 1275956 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B1277015 : Blo 1275956 1277015 := bstep (se 1 (by rfl) ⟨957761, by rfl⟩ : syracuseStep 1277015 = 1915523) B1915523
theorem B1915991 : Blo 1275956 1915991 := bstep (se 1 (by rfl) ⟨1436993, by rfl⟩ : syracuseStep 1915991 = 2873987) B2873987
theorem B2874455 : Blo 1275956 2874455 := bstep (se 1 (by rfl) ⟨2155841, by rfl⟩ : syracuseStep 2874455 = 4311683) B4311683
theorem B3882077 : Blo 1275956 3882077 := bstep (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) B1455779
theorem B1277035 : Blo 1275956 1277035 := bstep (se 1 (by rfl) ⟨957776, by rfl⟩ : syracuseStep 1277035 = 1915553) B1915553
theorem B1277047 : Blo 1275956 1277047 := bstep (se 1 (by rfl) ⟨957785, by rfl⟩ : syracuseStep 1277047 = 1915571) B1915571
theorem B1277067 : Blo 1275956 1277067 := bstep (se 1 (by rfl) ⟨957800, by rfl⟩ : syracuseStep 1277067 = 1915601) B1915601
theorem B4308119 : Blo 1275956 4308119 := bstep (se 1 (by rfl) ⟨3231089, by rfl⟩ : syracuseStep 4308119 = 6462179) B6462179
theorem B1277079 : Blo 1275956 1277079 := bstep (se 1 (by rfl) ⟨957809, by rfl⟩ : syracuseStep 1277079 = 1915619) B1915619
theorem B1916057 : Blo 1275956 1916057 := bstep (se 2 (by rfl) ⟨718521, by rfl⟩ : syracuseStep 1916057 = 1437043) B1437043
theorem B1277099 : Blo 1275956 1277099 := bstep (se 1 (by rfl) ⟨957824, by rfl⟩ : syracuseStep 1277099 = 1915649) B1915649
theorem B5176493 : Blo 1275956 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B1277111 : Blo 1275956 1277111 := bstep (se 1 (by rfl) ⟨957833, by rfl⟩ : syracuseStep 1277111 = 1915667) B1915667
theorem B2424001 : Blo 1275956 2424001 := bstep (se 2 (by rfl) ⟨909000, by rfl⟩ : syracuseStep 2424001 = 1818001) B1818001
theorem B2153675 : Blo 1275956 2153675 := bstep (se 1 (by rfl) ⟨1615256, by rfl⟩ : syracuseStep 2153675 = 3230513) B3230513
theorem B1277131 : Blo 1275956 1277131 := bstep (se 1 (by rfl) ⟨957848, by rfl⟩ : syracuseStep 1277131 = 1915697) B1915697
theorem B19643597 : Blo 1275956 19643597 := bstep (se 3 (by rfl) ⟨3683174, by rfl⟩ : syracuseStep 19643597 = 7366349) B7366349
theorem B1277143 : Blo 1275956 1277143 := bstep (se 1 (by rfl) ⟨957857, by rfl⟩ : syracuseStep 1277143 = 1915715) B1915715
theorem B1277163 : Blo 1275956 1277163 := bstep (se 1 (by rfl) ⟨957872, by rfl⟩ : syracuseStep 1277163 = 1915745) B1915745
theorem B2727155 : Blo 1275956 2727155 := bstep (se 1 (by rfl) ⟨2045366, by rfl⟩ : syracuseStep 2727155 = 4090733) B4090733
theorem B1277175 : Blo 1275956 1277175 := bstep (se 1 (by rfl) ⟨957881, by rfl⟩ : syracuseStep 1277175 = 1915763) B1915763
theorem B2071819 : Blo 1275956 2071819 := bstep (se 1 (by rfl) ⟨1553864, by rfl⟩ : syracuseStep 2071819 = 3107729) B3107729
theorem B1277195 : Blo 1275956 1277195 := bstep (se 1 (by rfl) ⟨957896, by rfl⟩ : syracuseStep 1277195 = 1915793) B1915793
theorem B1916171 : Blo 1275956 1916171 := bstep (se 1 (by rfl) ⟨1437128, by rfl⟩ : syracuseStep 1916171 = 2874257) B2874257
theorem B2874635 : Blo 1275956 2874635 := bstep (se 1 (by rfl) ⟨2155976, by rfl⟩ : syracuseStep 2874635 = 4311953) B4311953
theorem B1277207 : Blo 1275956 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B1916183 : Blo 1275956 1916183 := bstep (se 1 (by rfl) ⟨1437137, by rfl⟩ : syracuseStep 1916183 = 2874275) B2874275
theorem B1277227 : Blo 1275956 1277227 := bstep (se 1 (by rfl) ⟨957920, by rfl⟩ : syracuseStep 1277227 = 1915841) B1915841
theorem B1277239 : Blo 1275956 1277239 := bstep (se 1 (by rfl) ⟨957929, by rfl⟩ : syracuseStep 1277239 = 1915859) B1915859
theorem B2874689 : Blo 1275956 2874689 := bstep (se 2 (by rfl) ⟨1078008, by rfl⟩ : syracuseStep 2874689 = 2156017) B2156017
theorem B2153803 : Blo 1275956 2153803 := bstep (se 1 (by rfl) ⟨1615352, by rfl⟩ : syracuseStep 2153803 = 3230705) B3230705
theorem B2587979 : Blo 1275956 2587979 := bstep (se 1 (by rfl) ⟨1940984, by rfl⟩ : syracuseStep 2587979 = 3881969) B3881969
theorem B1277259 : Blo 1275956 1277259 := bstep (se 1 (by rfl) ⟨957944, by rfl⟩ : syracuseStep 1277259 = 1915889) B1915889
theorem B1277271 : Blo 1275956 1277271 := bstep (se 1 (by rfl) ⟨957953, by rfl⟩ : syracuseStep 1277271 = 1915907) B1915907
theorem B1916249 : Blo 1275956 1916249 := bstep (se 2 (by rfl) ⟨718593, by rfl⟩ : syracuseStep 1916249 = 1437187) B1437187
theorem B1277291 : Blo 1275956 1277291 := bstep (se 1 (by rfl) ⟨957968, by rfl⟩ : syracuseStep 1277291 = 1915937) B1915937
theorem B1277303 : Blo 1275956 1277303 := bstep (se 1 (by rfl) ⟨957977, by rfl⟩ : syracuseStep 1277303 = 1915955) B1915955
theorem B1277323 : Blo 1275956 1277323 := bstep (se 1 (by rfl) ⟨957992, by rfl⟩ : syracuseStep 1277323 = 1915985) B1915985
theorem B1277335 : Blo 1275956 1277335 := bstep (se 1 (by rfl) ⟨958001, by rfl⟩ : syracuseStep 1277335 = 1916003) B1916003
theorem B1277355 : Blo 1275956 1277355 := bstep (se 1 (by rfl) ⟨958016, by rfl⟩ : syracuseStep 1277355 = 1916033) B1916033
theorem B13106609 : Blo 1275956 13106609 := bstep (se 2 (by rfl) ⟨4914978, by rfl⟩ : syracuseStep 13106609 = 9829957) B9829957
theorem B1277367 : Blo 1275956 1277367 := bstep (se 1 (by rfl) ⟨958025, by rfl⟩ : syracuseStep 1277367 = 1916051) B1916051
theorem B1277387 : Blo 1275956 1277387 := bstep (se 1 (by rfl) ⟨958040, by rfl⟩ : syracuseStep 1277387 = 1916081) B1916081
theorem B1916363 : Blo 1275956 1916363 := bstep (se 1 (by rfl) ⟨1437272, by rfl⟩ : syracuseStep 1916363 = 2874545) B2874545
theorem B1277399 : Blo 1275956 1277399 := bstep (se 1 (by rfl) ⟨958049, by rfl⟩ : syracuseStep 1277399 = 1916099) B1916099
theorem B1916375 : Blo 1275956 1916375 := bstep (se 1 (by rfl) ⟨1437281, by rfl⟩ : syracuseStep 1916375 = 2874563) B2874563
theorem B2153945 : Blo 1275956 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B3636697 : Blo 1275956 3636697 := bstep (se 2 (by rfl) ⟨1363761, by rfl⟩ : syracuseStep 3636697 = 2727523) B2727523
theorem B1277419 : Blo 1275956 1277419 := bstep (se 1 (by rfl) ⟨958064, by rfl⟩ : syracuseStep 1277419 = 1916129) B1916129
theorem B1277431 : Blo 1275956 1277431 := bstep (se 1 (by rfl) ⟨958073, by rfl⟩ : syracuseStep 1277431 = 1916147) B1916147
theorem B1277451 : Blo 1275956 1277451 := bstep (se 1 (by rfl) ⟨958088, by rfl⟩ : syracuseStep 1277451 = 1916177) B1916177
theorem B12271121 : Blo 1275956 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B2424343 : Blo 1275956 2424343 := bstep (se 1 (by rfl) ⟨1818257, by rfl⟩ : syracuseStep 2424343 = 3636515) B3636515
theorem B1277463 : Blo 1275956 1277463 := bstep (se 1 (by rfl) ⟨958097, by rfl⟩ : syracuseStep 1277463 = 1916195) B1916195
theorem B1916441 : Blo 1275956 1916441 := bstep (se 2 (by rfl) ⟨718665, by rfl⟩ : syracuseStep 1916441 = 1437331) B1437331
theorem B2874905 : Blo 1275956 2874905 := bstep (se 2 (by rfl) ⟨1078089, by rfl⟩ : syracuseStep 2874905 = 2156179) B2156179
theorem B1277483 : Blo 1275956 1277483 := bstep (se 1 (by rfl) ⟨958112, by rfl⟩ : syracuseStep 1277483 = 1916225) B1916225
theorem B10903085 : Blo 1275956 10903085 := bstep (se 3 (by rfl) ⟨2044328, by rfl⟩ : syracuseStep 10903085 = 4088657) B4088657
theorem B1277495 : Blo 1275956 1277495 := bstep (se 1 (by rfl) ⟨958121, by rfl⟩ : syracuseStep 1277495 = 1916243) B1916243
theorem B4849217 : Blo 1275956 4849217 := bstep (se 2 (by rfl) ⟨1818456, by rfl⟩ : syracuseStep 4849217 = 3636913) B3636913
theorem B1277515 : Blo 1275956 1277515 := bstep (se 1 (by rfl) ⟨958136, by rfl⟩ : syracuseStep 1277515 = 1916273) B1916273
theorem B1277527 : Blo 1275956 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B2154073 : Blo 1275956 2154073 := bstep (se 2 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 2154073 = 1615555) B1615555
theorem B8183389 : Blo 1275956 8183389 := bstep (se 3 (by rfl) ⟨1534385, by rfl⟩ : syracuseStep 8183389 = 3068771) B3068771
theorem B1277547 : Blo 1275956 1277547 := bstep (se 1 (by rfl) ⟨958160, by rfl⟩ : syracuseStep 1277547 = 1916321) B1916321
theorem B2874995 : Blo 1275956 2874995 := bstep (se 1 (by rfl) ⟨2156246, by rfl⟩ : syracuseStep 2874995 = 4312493) B4312493
theorem B1277559 : Blo 1275956 1277559 := bstep (se 1 (by rfl) ⟨958169, by rfl⟩ : syracuseStep 1277559 = 1916339) B1916339
theorem B1941131 : Blo 1275956 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B1277579 : Blo 1275956 1277579 := bstep (se 1 (by rfl) ⟨958184, by rfl⟩ : syracuseStep 1277579 = 1916369) B1916369
theorem B1916555 : Blo 1275956 1916555 := bstep (se 1 (by rfl) ⟨1437416, by rfl⟩ : syracuseStep 1916555 = 2874833) B2874833
theorem B2588311 : Blo 1275956 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B1277591 : Blo 1275956 1277591 := bstep (se 1 (by rfl) ⟨958193, by rfl⟩ : syracuseStep 1277591 = 1916387) B1916387
theorem B1916567 : Blo 1275956 1916567 := bstep (se 1 (by rfl) ⟨1437425, by rfl⟩ : syracuseStep 1916567 = 2874851) B2874851
theorem B2875031 : Blo 1275956 2875031 := bstep (se 1 (by rfl) ⟨2156273, by rfl⟩ : syracuseStep 2875031 = 4312547) B4312547
theorem B1277611 : Blo 1275956 1277611 := bstep (se 1 (by rfl) ⟨958208, by rfl⟩ : syracuseStep 1277611 = 1916417) B1916417
theorem B4308659 : Blo 1275956 4308659 := bstep (se 1 (by rfl) ⟨3231494, by rfl⟩ : syracuseStep 4308659 = 6462989) B6462989
theorem B1277623 : Blo 1275956 1277623 := bstep (se 1 (by rfl) ⟨958217, by rfl⟩ : syracuseStep 1277623 = 1916435) B1916435
theorem B2301643 : Blo 1275956 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B1277643 : Blo 1275956 1277643 := bstep (se 1 (by rfl) ⟨958232, by rfl⟩ : syracuseStep 1277643 = 1916465) B1916465
theorem B1277655 : Blo 1275956 1277655 := bstep (se 1 (by rfl) ⟨958241, by rfl⟩ : syracuseStep 1277655 = 1916483) B1916483
theorem B1916633 : Blo 1275956 1916633 := bstep (se 2 (by rfl) ⟨718737, by rfl⟩ : syracuseStep 1916633 = 1437475) B1437475
theorem B1277675 : Blo 1275956 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B2424563 : Blo 1275956 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B1277687 : Blo 1275956 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B1277707 : Blo 1275956 1277707 := bstep (se 1 (by rfl) ⟨958280, by rfl⟩ : syracuseStep 1277707 = 1916561) B1916561
theorem B1277719 : Blo 1275956 1277719 := bstep (se 1 (by rfl) ⟨958289, by rfl⟩ : syracuseStep 1277719 = 1916579) B1916579
theorem B1277739 : Blo 1275956 1277739 := bstep (se 1 (by rfl) ⟨958304, by rfl⟩ : syracuseStep 1277739 = 1916609) B1916609
theorem B1277751 : Blo 1275956 1277751 := bstep (se 1 (by rfl) ⟨958313, by rfl⟩ : syracuseStep 1277751 = 1916627) B1916627
theorem B1277771 : Blo 1275956 1277771 := bstep (se 1 (by rfl) ⟨958328, by rfl⟩ : syracuseStep 1277771 = 1916657) B1916657
theorem B1916747 : Blo 1275956 1916747 := bstep (se 1 (by rfl) ⟨1437560, by rfl⟩ : syracuseStep 1916747 = 2875121) B2875121
theorem B2875211 : Blo 1275956 2875211 := bstep (se 1 (by rfl) ⟨2156408, by rfl⟩ : syracuseStep 2875211 = 4312817) B4312817
theorem B1277783 : Blo 1275956 1277783 := bstep (se 1 (by rfl) ⟨958337, by rfl⟩ : syracuseStep 1277783 = 1916675) B1916675
theorem B1916759 : Blo 1275956 1916759 := bstep (se 1 (by rfl) ⟨1437569, by rfl⟩ : syracuseStep 1916759 = 2875139) B2875139
theorem B1277803 : Blo 1275956 1277803 := bstep (se 1 (by rfl) ⟨958352, by rfl⟩ : syracuseStep 1277803 = 1916705) B1916705
theorem B1277815 : Blo 1275956 1277815 := bstep (se 1 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 1277815 = 1916723) B1916723
theorem B2875265 : Blo 1275956 2875265 := bstep (se 2 (by rfl) ⟨1078224, by rfl⟩ : syracuseStep 2875265 = 2156449) B2156449
theorem B1277835 : Blo 1275956 1277835 := bstep (se 1 (by rfl) ⟨958376, by rfl⟩ : syracuseStep 1277835 = 1916753) B1916753
theorem B1277847 : Blo 1275956 1277847 := bstep (se 1 (by rfl) ⟨958385, by rfl⟩ : syracuseStep 1277847 = 1916771) B1916771
theorem B1916825 : Blo 1275956 1916825 := bstep (se 2 (by rfl) ⟨718809, by rfl⟩ : syracuseStep 1916825 = 1437619) B1437619
theorem B1277867 : Blo 1275956 1277867 := bstep (se 1 (by rfl) ⟨958400, by rfl⟩ : syracuseStep 1277867 = 1916801) B1916801
theorem B1277879 : Blo 1275956 1277879 := bstep (se 1 (by rfl) ⟨958409, by rfl⟩ : syracuseStep 1277879 = 1916819) B1916819
theorem B4308929 : Blo 1275956 4308929 := bstep (se 2 (by rfl) ⟨1615848, by rfl⟩ : syracuseStep 4308929 = 3231697) B3231697
theorem B1277899 : Blo 1275956 1277899 := bstep (se 1 (by rfl) ⟨958424, by rfl⟩ : syracuseStep 1277899 = 1916849) B1916849
theorem B2424791 : Blo 1275956 2424791 := bstep (se 1 (by rfl) ⟨1818593, by rfl⟩ : syracuseStep 2424791 = 3637187) B3637187
theorem B1277911 : Blo 1275956 1277911 := bstep (se 1 (by rfl) ⟨958433, by rfl⟩ : syracuseStep 1277911 = 1916867) B1916867
theorem B1277931 : Blo 1275956 1277931 := bstep (se 1 (by rfl) ⟨958448, by rfl⟩ : syracuseStep 1277931 = 1916897) B1916897
theorem B4087837 : Blo 1275956 4087837 := bstep (se 3 (by rfl) ⟨766469, by rfl⟩ : syracuseStep 4087837 = 1532939) B1532939
theorem B2154539 : Blo 1275956 2154539 := bstep (se 1 (by rfl) ⟨1615904, by rfl⟩ : syracuseStep 2154539 = 3231809) B3231809
theorem B4849901 : Blo 1275956 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B1941817 : Blo 1275956 1941817 := bstep (se 2 (by rfl) ⟨728181, by rfl⟩ : syracuseStep 1941817 = 1456363) B1456363
theorem B4309307 : Blo 1275956 4309307 := bstep (se 1 (by rfl) ⟨3231980, by rfl⟩ : syracuseStep 4309307 = 6463961) B6463961
theorem B3686743 : Blo 1275956 3686743 := bstep (se 1 (by rfl) ⟨2765057, by rfl⟩ : syracuseStep 3686743 = 5530115) B5530115
theorem B3637619 : Blo 1275956 3637619 := bstep (se 1 (by rfl) ⟨2728214, by rfl⟩ : syracuseStep 3637619 = 5456429) B5456429
theorem B2154937 : Blo 1275956 2154937 := bstep (se 2 (by rfl) ⟨808101, by rfl⟩ : syracuseStep 2154937 = 1616203) B1616203
theorem B10502621 : Blo 1275956 10502621 := bstep (se 3 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 10502621 = 3938483) B3938483
theorem B2490895 : Blo 1275956 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B4850219 : Blo 1275956 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B1942073 : Blo 1275956 1942073 := bstep (se 2 (by rfl) ⟨728277, by rfl⟩ : syracuseStep 1942073 = 1456555) B1456555
theorem B3637847 : Blo 1275956 3637847 := bstep (se 1 (by rfl) ⟨2728385, by rfl⟩ : syracuseStep 3637847 = 5456771) B5456771
theorem B6308545 : Blo 1275956 6308545 := bstep (se 2 (by rfl) ⟨2365704, by rfl⟩ : syracuseStep 6308545 = 4731409) B4731409
theorem B4309793 : Blo 1275956 4309793 := bstep (se 2 (by rfl) ⟨1616172, by rfl⟩ : syracuseStep 4309793 = 3232345) B3232345
theorem B3449719 : Blo 1275956 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B1295291 : Blo 1275956 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B1819579 : Blo 1275956 1819579 := bstep (se 1 (by rfl) ⟨1364684, by rfl⟩ : syracuseStep 1819579 = 2729369) B2729369
theorem B2425801 : Blo 1275956 2425801 := bstep (se 2 (by rfl) ⟨909675, by rfl⟩ : syracuseStep 2425801 = 1819351) B1819351
theorem B9323531 : Blo 1275956 9323531 := bstep (se 1 (by rfl) ⟨6992648, by rfl⟩ : syracuseStep 9323531 = 13985297) B13985297
theorem B1614907 : Blo 1275956 1614907 := bstep (se 1 (by rfl) ⟨1211180, by rfl⟩ : syracuseStep 1614907 = 2422361) B2422361
theorem B7275581 : Blo 1275956 7275581 := bstep (se 3 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 7275581 = 2728343) B2728343
theorem B104842309 : Blo 1275956 104842309 := bstep (se 4 (by rfl) ⟨9828966, by rfl⟩ : syracuseStep 104842309 = 19657933) B19657933
theorem B39298135 : Blo 1275956 39298135 := bstep (se 1 (by rfl) ⟨29473601, by rfl⟩ : syracuseStep 39298135 = 58947203) B58947203
theorem B2155639 : Blo 1275956 2155639 := bstep (se 1 (by rfl) ⟨1616729, by rfl⟩ : syracuseStep 2155639 = 3233459) B3233459
theorem B2155835 : Blo 1275956 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B4310387 : Blo 1275956 4310387 := bstep (se 1 (by rfl) ⟨3232790, by rfl⟩ : syracuseStep 4310387 = 6465581) B6465581
theorem B1615403 : Blo 1275956 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B2762425 : Blo 1275956 2762425 := bstep (se 2 (by rfl) ⟨1035909, by rfl⟩ : syracuseStep 2762425 = 2071819) B2071819
theorem B6899393 : Blo 1275956 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B2156233 : Blo 1275956 2156233 := bstep (se 2 (by rfl) ⟨808587, by rfl⟩ : syracuseStep 2156233 = 1617175) B1617175
theorem B16361189 : Blo 1275956 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B26920907 : Blo 1275956 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B1615879 : Blo 1275956 1615879 := bstep (se 1 (by rfl) ⟨1211909, by rfl⟩ : syracuseStep 1615879 = 2423819) B2423819
theorem B9824267 : Blo 1275956 9824267 := bstep (se 1 (by rfl) ⟨7368200, by rfl⟩ : syracuseStep 9824267 = 14736401) B14736401
theorem B1533967 : Blo 1275956 1533967 := bstep (se 1 (by rfl) ⟨1150475, by rfl⟩ : syracuseStep 1533967 = 2300951) B2300951
theorem B6899741 : Blo 1275956 6899741 := bstep (se 3 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 6899741 = 2587403) B2587403
theorem B7874621 : Blo 1275956 7874621 := bstep (se 3 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 7874621 = 2952983) B2952983
theorem B7473239 : Blo 1275956 7473239 := bstep (se 1 (by rfl) ⟨5604929, by rfl⟩ : syracuseStep 7473239 = 11209859) B11209859
theorem B3450995 : Blo 1275956 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B1435783 : Blo 1275956 1435783 := bstep (se 1 (by rfl) ⟨1076837, by rfl⟩ : syracuseStep 1435783 = 2153675) B2153675
theorem B3451081 : Blo 1275956 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B1435963 : Blo 1275956 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B7268723 : Blo 1275956 7268723 := bstep (se 1 (by rfl) ⟨5451542, by rfl⟩ : syracuseStep 7268723 = 10903085) B10903085
theorem B8735111 : Blo 1275956 8735111 := bstep (se 1 (by rfl) ⟨6551333, by rfl⟩ : syracuseStep 8735111 = 13102667) B13102667
theorem B9832913 : Blo 1275956 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B1616375 : Blo 1275956 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B3230219 : Blo 1275956 3230219 := bstep (se 1 (by rfl) ⟨2422664, by rfl⟩ : syracuseStep 3230219 = 4845329) B4845329
theorem B1616527 : Blo 1275956 1616527 := bstep (se 1 (by rfl) ⟨1212395, by rfl⟩ : syracuseStep 1616527 = 2424791) B2424791
theorem B10914497 : Blo 1275956 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B36842201 : Blo 1275956 36842201 := bstep (se 2 (by rfl) ⟨13815825, by rfl⟩ : syracuseStep 36842201 = 27631651) B27631651
theorem B1436431 : Blo 1275956 1436431 := bstep (se 1 (by rfl) ⟨1077323, by rfl⟩ : syracuseStep 1436431 = 2154647) B2154647
theorem B1616699 : Blo 1275956 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B4426649 : Blo 1275956 4426649 := bstep (se 2 (by rfl) ⟨1659993, by rfl⟩ : syracuseStep 4426649 = 3319987) B3319987
theorem B4598903 : Blo 1275956 4598903 := bstep (se 1 (by rfl) ⟨3449177, by rfl⟩ : syracuseStep 4598903 = 6898355) B6898355
theorem B27626629 : Blo 1275956 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B3230867 : Blo 1275956 3230867 := bstep (se 1 (by rfl) ⟨2423150, by rfl⟩ : syracuseStep 3230867 = 4846301) B4846301
theorem B1436935 : Blo 1275956 1436935 := bstep (se 1 (by rfl) ⟨1077701, by rfl⟩ : syracuseStep 1436935 = 2155403) B2155403
theorem B62115173 : Blo 1275956 62115173 := bstep (se 4 (by rfl) ⟨5823297, by rfl⟩ : syracuseStep 62115173 = 11646595) B11646595
theorem B7277971 : Blo 1275956 7277971 := bstep (se 1 (by rfl) ⟨5458478, by rfl⟩ : syracuseStep 7277971 = 10916957) B10916957
theorem B4599193 : Blo 1275956 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B3231161 : Blo 1275956 3231161 := bstep (se 2 (by rfl) ⟨1211685, by rfl⟩ : syracuseStep 3231161 = 2423371) B2423371
theorem B1437115 : Blo 1275956 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B1420859 : Blo 1275956 1420859 := bstep (se 1 (by rfl) ⟨1065644, by rfl⟩ : syracuseStep 1420859 = 2131289) B2131289
theorem B14536259 : Blo 1275956 14536259 := bstep (se 1 (by rfl) ⟨10902194, by rfl⟩ : syracuseStep 14536259 = 21804389) B21804389
theorem B9702989 : Blo 1275956 9702989 := bstep (se 3 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 9702989 = 3638621) B3638621
theorem B1363591 : Blo 1275956 1363591 := bstep (se 1 (by rfl) ⟨1022693, by rfl⟩ : syracuseStep 1363591 = 2045387) B2045387
theorem B4091593 : Blo 1275956 4091593 := bstep (se 2 (by rfl) ⟨1534347, by rfl⟩ : syracuseStep 4091593 = 3068695) B3068695
theorem B7270181 : Blo 1275956 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B1773371 : Blo 1275956 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B1437583 : Blo 1275956 1437583 := bstep (se 1 (by rfl) ⟨1078187, by rfl⟩ : syracuseStep 1437583 = 2156375) B2156375
theorem B4312979 : Blo 1275956 4312979 := bstep (se 1 (by rfl) ⟨3234734, by rfl⟩ : syracuseStep 4312979 = 6469469) B6469469
theorem B13807523 : Blo 1275956 13807523 := bstep (se 1 (by rfl) ⟨10355642, by rfl⟩ : syracuseStep 13807523 = 20711285) B20711285
theorem B6737987 : Blo 1275956 6737987 := bstep (se 1 (by rfl) ⟨5053490, by rfl⟩ : syracuseStep 6737987 = 10106981) B10106981
theorem B3231859 : Blo 1275956 3231859 := bstep (se 1 (by rfl) ⟨2423894, by rfl⟩ : syracuseStep 3231859 = 4847789) B4847789
theorem B2871431 : Blo 1275956 2871431 := bstep (se 1 (by rfl) ⟨2153573, by rfl⟩ : syracuseStep 2871431 = 4307147) B4307147
theorem B3232001 : Blo 1275956 3232001 := bstep (se 2 (by rfl) ⟨1212000, by rfl⟩ : syracuseStep 3232001 = 2424001) B2424001
theorem B20713745 : Blo 1275956 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B2871611 : Blo 1275956 2871611 := bstep (se 1 (by rfl) ⟨2153708, by rfl⟩ : syracuseStep 2871611 = 4307417) B4307417
theorem B2871737 : Blo 1275956 2871737 := bstep (se 2 (by rfl) ⟨1076901, by rfl⟩ : syracuseStep 2871737 = 2153803) B2153803
theorem B1364411 : Blo 1275956 1364411 := bstep (se 1 (by rfl) ⟨1023308, by rfl⟩ : syracuseStep 1364411 = 2046617) B2046617
theorem B11055619 : Blo 1275956 11055619 := bstep (se 1 (by rfl) ⟨8291714, by rfl⟩ : syracuseStep 11055619 = 16583429) B16583429
theorem B7270955 : Blo 1275956 7270955 := bstep (se 1 (by rfl) ⟨5453216, by rfl⟩ : syracuseStep 7270955 = 10906433) B10906433
theorem B4371005 : Blo 1275956 4371005 := bstep (se 3 (by rfl) ⟨819563, by rfl⟩ : syracuseStep 4371005 = 1639127) B1639127
theorem B3232457 : Blo 1275956 3232457 := bstep (se 2 (by rfl) ⟨1212171, by rfl⟩ : syracuseStep 3232457 = 2424343) B2424343
theorem B2872079 : Blo 1275956 2872079 := bstep (se 1 (by rfl) ⟨2154059, by rfl⟩ : syracuseStep 2872079 = 4308119) B4308119
theorem B2872097 : Blo 1275956 2872097 := bstep (se 2 (by rfl) ⟨1077036, by rfl⟩ : syracuseStep 2872097 = 2154073) B2154073
theorem B13095731 : Blo 1275956 13095731 := bstep (se 1 (by rfl) ⟨9821798, by rfl⟩ : syracuseStep 13095731 = 19643597) B19643597
theorem B3634055 : Blo 1275956 3634055 := bstep (se 1 (by rfl) ⟨2725541, by rfl⟩ : syracuseStep 3634055 = 5451083) B5451083
theorem B1725319 : Blo 1275956 1725319 := bstep (se 1 (by rfl) ⟨1293989, by rfl⟩ : syracuseStep 1725319 = 2587979) B2587979
theorem B6468497 : Blo 1275956 6468497 := bstep (se 2 (by rfl) ⟨2425686, by rfl⟩ : syracuseStep 6468497 = 4851373) B4851373
theorem B3068857 : Blo 1275956 3068857 := bstep (se 2 (by rfl) ⟨1150821, by rfl⟩ : syracuseStep 3068857 = 2301643) B2301643
theorem B8737739 : Blo 1275956 8737739 := bstep (se 1 (by rfl) ⟨6553304, by rfl⟩ : syracuseStep 8737739 = 13106609) B13106609
theorem B8180747 : Blo 1275956 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B3232811 : Blo 1275956 3232811 := bstep (se 1 (by rfl) ⟨2424608, by rfl⟩ : syracuseStep 3232811 = 4849217) B4849217
theorem B1913975 : Blo 1275956 1913975 := bstep (se 1 (by rfl) ⟨1435481, by rfl⟩ : syracuseStep 1913975 = 2870963) B2870963
theorem B2872439 : Blo 1275956 2872439 := bstep (se 1 (by rfl) ⟨2154329, by rfl⟩ : syracuseStep 2872439 = 4308659) B4308659
theorem B1913999 : Blo 1275956 1913999 := bstep (se 1 (by rfl) ⟨1435499, by rfl⟩ : syracuseStep 1913999 = 2870999) B2870999
theorem B1914041 : Blo 1275956 1914041 := bstep (se 2 (by rfl) ⟨717765, by rfl⟩ : syracuseStep 1914041 = 1435531) B1435531
theorem B1914119 : Blo 1275956 1914119 := bstep (se 1 (by rfl) ⟨1435589, by rfl⟩ : syracuseStep 1914119 = 2871179) B2871179
theorem B1914155 : Blo 1275956 1914155 := bstep (se 1 (by rfl) ⟨1435616, by rfl⟩ : syracuseStep 1914155 = 2871233) B2871233
theorem B2872619 : Blo 1275956 2872619 := bstep (se 1 (by rfl) ⟨2154464, by rfl⟩ : syracuseStep 2872619 = 4308929) B4308929
theorem B1914185 : Blo 1275956 1914185 := bstep (se 2 (by rfl) ⟨717819, by rfl⟩ : syracuseStep 1914185 = 1435639) B1435639
theorem B3683731 : Blo 1275956 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B52450739 : Blo 1275956 52450739 := bstep (se 1 (by rfl) ⟨39338054, by rfl⟩ : syracuseStep 52450739 = 78676109) B78676109
theorem B1914299 : Blo 1275956 1914299 := bstep (se 1 (by rfl) ⟨1435724, by rfl⟩ : syracuseStep 1914299 = 2871449) B2871449
theorem B2299337 : Blo 1275956 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B1914359 : Blo 1275956 1914359 := bstep (se 1 (by rfl) ⟨1435769, by rfl⟩ : syracuseStep 1914359 = 2871539) B2871539
theorem B1914383 : Blo 1275956 1914383 := bstep (se 1 (by rfl) ⟨1435787, by rfl⟩ : syracuseStep 1914383 = 2871575) B2871575
theorem B3634703 : Blo 1275956 3634703 := bstep (se 1 (by rfl) ⟨2726027, by rfl⟩ : syracuseStep 3634703 = 5452055) B5452055
theorem B3274273 : Blo 1275956 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B1914425 : Blo 1275956 1914425 := bstep (se 2 (by rfl) ⟨717909, by rfl⟩ : syracuseStep 1914425 = 1435819) B1435819
theorem B1914503 : Blo 1275956 1914503 := bstep (se 1 (by rfl) ⟨1435877, by rfl⟩ : syracuseStep 1914503 = 2871755) B2871755
theorem B2872979 : Blo 1275956 2872979 := bstep (se 1 (by rfl) ⟨2154734, by rfl⟩ : syracuseStep 2872979 = 4309469) B4309469
theorem B1914539 : Blo 1275956 1914539 := bstep (se 1 (by rfl) ⟨1435904, by rfl⟩ : syracuseStep 1914539 = 2871809) B2871809
theorem B1914569 : Blo 1275956 1914569 := bstep (se 2 (by rfl) ⟨717963, by rfl⟩ : syracuseStep 1914569 = 1435927) B1435927
theorem B2873033 : Blo 1275956 2873033 := bstep (se 2 (by rfl) ⟨1077387, by rfl⟩ : syracuseStep 2873033 = 2154775) B2154775
theorem B2422543 : Blo 1275956 2422543 := bstep (se 1 (by rfl) ⟨1816907, by rfl⟩ : syracuseStep 2422543 = 3633815) B3633815
theorem B1914683 : Blo 1275956 1914683 := bstep (se 1 (by rfl) ⟨1436012, by rfl⟩ : syracuseStep 1914683 = 2872025) B2872025
theorem B1914743 : Blo 1275956 1914743 := bstep (se 1 (by rfl) ⟨1436057, by rfl⟩ : syracuseStep 1914743 = 2872115) B2872115
theorem B4306823 : Blo 1275956 4306823 := bstep (se 1 (by rfl) ⟨3230117, by rfl⟩ : syracuseStep 4306823 = 6460235) B6460235
theorem B6133639 : Blo 1275956 6133639 := bstep (se 1 (by rfl) ⟨4600229, by rfl⟩ : syracuseStep 6133639 = 9200459) B9200459
theorem B1914767 : Blo 1275956 1914767 := bstep (se 1 (by rfl) ⟨1436075, by rfl⟩ : syracuseStep 1914767 = 2872151) B2872151
theorem B6461369 : Blo 1275956 6461369 := bstep (se 2 (by rfl) ⟨2423013, by rfl⟩ : syracuseStep 6461369 = 4846027) B4846027
theorem B1914809 : Blo 1275956 1914809 := bstep (se 2 (by rfl) ⟨718053, by rfl⟩ : syracuseStep 1914809 = 1436107) B1436107
theorem B7272413 : Blo 1275956 7272413 := bstep (se 3 (by rfl) ⟨1363577, by rfl⟩ : syracuseStep 7272413 = 2727155) B2727155
theorem B1914887 : Blo 1275956 1914887 := bstep (se 1 (by rfl) ⟨1436165, by rfl⟩ : syracuseStep 1914887 = 2872331) B2872331
theorem B3233803 : Blo 1275956 3233803 := bstep (se 1 (by rfl) ⟨2425352, by rfl⟩ : syracuseStep 3233803 = 4850705) B4850705
theorem B7764011 : Blo 1275956 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B1914923 : Blo 1275956 1914923 := bstep (se 1 (by rfl) ⟨1436192, by rfl⟩ : syracuseStep 1914923 = 2872385) B2872385
theorem B1275963 : Blo 1275956 1275963 := bstep (se 1 (by rfl) ⟨956972, by rfl⟩ : syracuseStep 1275963 = 1913945) B1913945
theorem B1914953 : Blo 1275956 1914953 := bstep (se 2 (by rfl) ⟨718107, by rfl⟩ : syracuseStep 1914953 = 1436215) B1436215
theorem B1276039 : Blo 1275956 1276039 := bstep (se 1 (by rfl) ⟨957029, by rfl⟩ : syracuseStep 1276039 = 1914059) B1914059
theorem B1276047 : Blo 1275956 1276047 := bstep (se 1 (by rfl) ⟨957035, by rfl⟩ : syracuseStep 1276047 = 1914071) B1914071
theorem B3233945 : Blo 1275956 3233945 := bstep (se 2 (by rfl) ⟨1212729, by rfl⟩ : syracuseStep 3233945 = 2425459) B2425459
theorem B22132909 : Blo 1275956 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B1276091 : Blo 1275956 1276091 := bstep (se 1 (by rfl) ⟨957068, by rfl⟩ : syracuseStep 1276091 = 1914137) B1914137
theorem B1915067 : Blo 1275956 1915067 := bstep (se 1 (by rfl) ⟨1436300, by rfl⟩ : syracuseStep 1915067 = 2872601) B2872601
theorem B1915127 : Blo 1275956 1915127 := bstep (se 1 (by rfl) ⟨1436345, by rfl⟩ : syracuseStep 1915127 = 2872691) B2872691
theorem B4307201 : Blo 1275956 4307201 := bstep (se 2 (by rfl) ⟨1615200, by rfl⟩ : syracuseStep 4307201 = 3230401) B3230401
theorem B1276167 : Blo 1275956 1276167 := bstep (se 1 (by rfl) ⟨957125, by rfl⟩ : syracuseStep 1276167 = 1914251) B1914251
theorem B1276175 : Blo 1275956 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B1915151 : Blo 1275956 1915151 := bstep (se 1 (by rfl) ⟨1436363, by rfl⟩ : syracuseStep 1915151 = 2872727) B2872727
theorem B3070241 : Blo 1275956 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B1276219 : Blo 1275956 1276219 := bstep (se 1 (by rfl) ⟨957164, by rfl⟩ : syracuseStep 1276219 = 1914329) B1914329
theorem B1915193 : Blo 1275956 1915193 := bstep (se 2 (by rfl) ⟨718197, by rfl⟩ : syracuseStep 1915193 = 1436395) B1436395
theorem B3234107 : Blo 1275956 3234107 := bstep (se 1 (by rfl) ⟨2425580, by rfl⟩ : syracuseStep 3234107 = 4851161) B4851161
theorem B1276295 : Blo 1275956 1276295 := bstep (se 1 (by rfl) ⟨957221, by rfl⟩ : syracuseStep 1276295 = 1914443) B1914443
theorem B1915271 : Blo 1275956 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B2873735 : Blo 1275956 2873735 := bstep (se 1 (by rfl) ⟨2155301, by rfl⟩ : syracuseStep 2873735 = 4310603) B4310603
theorem B1276303 : Blo 1275956 1276303 := bstep (se 1 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 1276303 = 1914455) B1914455
theorem B11655571 : Blo 1275956 11655571 := bstep (se 1 (by rfl) ⟨8741678, by rfl⟩ : syracuseStep 11655571 = 17483357) B17483357
theorem B1915307 : Blo 1275956 1915307 := bstep (se 1 (by rfl) ⟨1436480, by rfl⟩ : syracuseStep 1915307 = 2872961) B2872961
theorem B1276347 : Blo 1275956 1276347 := bstep (se 1 (by rfl) ⟨957260, by rfl⟩ : syracuseStep 1276347 = 1914521) B1914521
theorem B1915337 : Blo 1275956 1915337 := bstep (se 2 (by rfl) ⟨718251, by rfl⟩ : syracuseStep 1915337 = 1436503) B1436503
theorem B1276423 : Blo 1275956 1276423 := bstep (se 1 (by rfl) ⟨957317, by rfl⟩ : syracuseStep 1276423 = 1914635) B1914635
theorem B1276431 : Blo 1275956 1276431 := bstep (se 1 (by rfl) ⟨957323, by rfl⟩ : syracuseStep 1276431 = 1914647) B1914647
theorem B10902059 : Blo 1275956 10902059 := bstep (se 1 (by rfl) ⟨8176544, by rfl⟩ : syracuseStep 10902059 = 16353089) B16353089
theorem B1276475 : Blo 1275956 1276475 := bstep (se 1 (by rfl) ⟨957356, by rfl⟩ : syracuseStep 1276475 = 1914713) B1914713
theorem B1915451 : Blo 1275956 1915451 := bstep (se 1 (by rfl) ⟨1436588, by rfl⟩ : syracuseStep 1915451 = 2873177) B2873177
theorem B2873915 : Blo 1275956 2873915 := bstep (se 1 (by rfl) ⟨2155436, by rfl⟩ : syracuseStep 2873915 = 4310873) B4310873
theorem B1915511 : Blo 1275956 1915511 := bstep (se 1 (by rfl) ⟨1436633, by rfl⟩ : syracuseStep 1915511 = 2873267) B2873267
theorem B1276551 : Blo 1275956 1276551 := bstep (se 1 (by rfl) ⟨957413, by rfl⟩ : syracuseStep 1276551 = 1914827) B1914827
theorem B1276559 : Blo 1275956 1276559 := bstep (se 1 (by rfl) ⟨957419, by rfl⟩ : syracuseStep 1276559 = 1914839) B1914839
theorem B1915535 : Blo 1275956 1915535 := bstep (se 1 (by rfl) ⟨1436651, by rfl⟩ : syracuseStep 1915535 = 2873303) B2873303
theorem B3234451 : Blo 1275956 3234451 := bstep (se 1 (by rfl) ⟨2425838, by rfl⟩ : syracuseStep 3234451 = 4851677) B4851677
theorem B3111577 : Blo 1275956 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B1915577 : Blo 1275956 1915577 := bstep (se 2 (by rfl) ⟨718341, by rfl⟩ : syracuseStep 1915577 = 1436683) B1436683
theorem B2874041 : Blo 1275956 2874041 := bstep (se 2 (by rfl) ⟨1077765, by rfl⟩ : syracuseStep 2874041 = 2155531) B2155531
theorem B1276603 : Blo 1275956 1276603 := bstep (se 1 (by rfl) ⟨957452, by rfl⟩ : syracuseStep 1276603 = 1914905) B1914905
theorem B1276679 : Blo 1275956 1276679 := bstep (se 1 (by rfl) ⟨957509, by rfl⟩ : syracuseStep 1276679 = 1915019) B1915019
theorem B1915655 : Blo 1275956 1915655 := bstep (se 1 (by rfl) ⟨1436741, by rfl⟩ : syracuseStep 1915655 = 2873483) B2873483
theorem B1276687 : Blo 1275956 1276687 := bstep (se 1 (by rfl) ⟨957515, by rfl⟩ : syracuseStep 1276687 = 1915031) B1915031
theorem B2333455 : Blo 1275956 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B3234593 : Blo 1275956 3234593 := bstep (se 2 (by rfl) ⟨1212972, by rfl⟩ : syracuseStep 3234593 = 2425945) B2425945
theorem B1915691 : Blo 1275956 1915691 := bstep (se 1 (by rfl) ⟨1436768, by rfl⟩ : syracuseStep 1915691 = 2873537) B2873537
theorem B1276731 : Blo 1275956 1276731 := bstep (se 1 (by rfl) ⟨957548, by rfl⟩ : syracuseStep 1276731 = 1915097) B1915097
theorem B4848443 : Blo 1275956 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B1915721 : Blo 1275956 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B4602739 : Blo 1275956 4602739 := bstep (se 1 (by rfl) ⟨3452054, by rfl⟩ : syracuseStep 4602739 = 6904109) B6904109
theorem B2153351 : Blo 1275956 2153351 := bstep (se 1 (by rfl) ⟨1615013, by rfl⟩ : syracuseStep 2153351 = 3230027) B3230027
theorem B1276807 : Blo 1275956 1276807 := bstep (se 1 (by rfl) ⟨957605, by rfl⟩ : syracuseStep 1276807 = 1915211) B1915211
theorem B1276815 : Blo 1275956 1276815 := bstep (se 1 (by rfl) ⟨957611, by rfl⟩ : syracuseStep 1276815 = 1915223) B1915223
theorem B1276859 : Blo 1275956 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B1915835 : Blo 1275956 1915835 := bstep (se 1 (by rfl) ⟨1436876, by rfl⟩ : syracuseStep 1915835 = 2873753) B2873753
theorem B1915895 : Blo 1275956 1915895 := bstep (se 1 (by rfl) ⟨1436921, by rfl⟩ : syracuseStep 1915895 = 2873843) B2873843
theorem B1276935 : Blo 1275956 1276935 := bstep (se 1 (by rfl) ⟨957701, by rfl⟩ : syracuseStep 1276935 = 1915403) B1915403
theorem B1276943 : Blo 1275956 1276943 := bstep (se 1 (by rfl) ⟨957707, by rfl⟩ : syracuseStep 1276943 = 1915415) B1915415
theorem B1915919 : Blo 1275956 1915919 := bstep (se 1 (by rfl) ⟨1436939, by rfl⟩ : syracuseStep 1915919 = 2873879) B2873879
theorem B2874383 : Blo 1275956 2874383 := bstep (se 1 (by rfl) ⟨2155787, by rfl⟩ : syracuseStep 2874383 = 4311575) B4311575
theorem B5176349 : Blo 1275956 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B2874401 : Blo 1275956 2874401 := bstep (se 2 (by rfl) ⟨1077900, by rfl⟩ : syracuseStep 2874401 = 2155801) B2155801
theorem B4308011 : Blo 1275956 4308011 := bstep (se 1 (by rfl) ⟨3231008, by rfl⟩ : syracuseStep 4308011 = 6462017) B6462017
theorem B1915961 : Blo 1275956 1915961 := bstep (se 2 (by rfl) ⟨718485, by rfl⟩ : syracuseStep 1915961 = 1436971) B1436971
theorem B1276987 : Blo 1275956 1276987 := bstep (se 1 (by rfl) ⟨957740, by rfl⟩ : syracuseStep 1276987 = 1915481) B1915481
theorem B10910807 : Blo 1275956 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B3636343 : Blo 1275956 3636343 := bstep (se 1 (by rfl) ⟨2727257, by rfl⟩ : syracuseStep 3636343 = 5454515) B5454515
theorem B1277063 : Blo 1275956 1277063 := bstep (se 1 (by rfl) ⟨957797, by rfl⟩ : syracuseStep 1277063 = 1915595) B1915595
theorem B1916039 : Blo 1275956 1916039 := bstep (se 1 (by rfl) ⟨1437029, by rfl⟩ : syracuseStep 1916039 = 2874059) B2874059
theorem B1277071 : Blo 1275956 1277071 := bstep (se 1 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 1277071 = 1915607) B1915607
theorem B1916075 : Blo 1275956 1916075 := bstep (se 1 (by rfl) ⟨1437056, by rfl⟩ : syracuseStep 1916075 = 2874113) B2874113
theorem B1277115 : Blo 1275956 1277115 := bstep (se 1 (by rfl) ⟨957836, by rfl⟩ : syracuseStep 1277115 = 1915673) B1915673
theorem B6462665 : Blo 1275956 6462665 := bstep (se 2 (by rfl) ⟨2423499, by rfl⟩ : syracuseStep 6462665 = 4846999) B4846999
theorem B1916105 : Blo 1275956 1916105 := bstep (se 2 (by rfl) ⟨718539, by rfl⟩ : syracuseStep 1916105 = 1437079) B1437079
theorem B1277191 : Blo 1275956 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B1277199 : Blo 1275956 1277199 := bstep (se 1 (by rfl) ⟨957899, by rfl⟩ : syracuseStep 1277199 = 1915799) B1915799
theorem B4848929 : Blo 1275956 4848929 := bstep (se 2 (by rfl) ⟨1818348, by rfl⟩ : syracuseStep 4848929 = 3636697) B3636697
theorem B2424107 : Blo 1275956 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B1277243 : Blo 1275956 1277243 := bstep (se 1 (by rfl) ⟨957932, by rfl⟩ : syracuseStep 1277243 = 1915865) B1915865
theorem B20716859 : Blo 1275956 20716859 := bstep (se 1 (by rfl) ⟨15537644, by rfl⟩ : syracuseStep 20716859 = 31075289) B31075289
theorem B1916219 : Blo 1275956 1916219 := bstep (se 1 (by rfl) ⟨1437164, by rfl⟩ : syracuseStep 1916219 = 2874329) B2874329
theorem B1916279 : Blo 1275956 1916279 := bstep (se 1 (by rfl) ⟨1437209, by rfl⟩ : syracuseStep 1916279 = 2874419) B2874419
theorem B2874743 : Blo 1275956 2874743 := bstep (se 1 (by rfl) ⟨2156057, by rfl⟩ : syracuseStep 2874743 = 4312115) B4312115
theorem B1277319 : Blo 1275956 1277319 := bstep (se 1 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 1277319 = 1915979) B1915979
theorem B1277327 : Blo 1275956 1277327 := bstep (se 1 (by rfl) ⟨957995, by rfl⟩ : syracuseStep 1277327 = 1915991) B1915991
theorem B1916303 : Blo 1275956 1916303 := bstep (se 1 (by rfl) ⟨1437227, by rfl⟩ : syracuseStep 1916303 = 2874455) B2874455
theorem B2588051 : Blo 1275956 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B1916345 : Blo 1275956 1916345 := bstep (se 2 (by rfl) ⟨718629, by rfl⟩ : syracuseStep 1916345 = 1437259) B1437259
theorem B1277371 : Blo 1275956 1277371 := bstep (se 1 (by rfl) ⟨958028, by rfl⟩ : syracuseStep 1277371 = 1916057) B1916057
theorem B10911185 : Blo 1275956 10911185 := bstep (se 2 (by rfl) ⟨4091694, by rfl⟩ : syracuseStep 10911185 = 8183389) B8183389
theorem B1277447 : Blo 1275956 1277447 := bstep (se 1 (by rfl) ⟨958085, by rfl⟩ : syracuseStep 1277447 = 1916171) B1916171
theorem B1916423 : Blo 1275956 1916423 := bstep (se 1 (by rfl) ⟨1437317, by rfl⟩ : syracuseStep 1916423 = 2874635) B2874635
theorem B2153999 : Blo 1275956 2153999 := bstep (se 1 (by rfl) ⟨1615499, by rfl⟩ : syracuseStep 2153999 = 3230999) B3230999
theorem B1277455 : Blo 1275956 1277455 := bstep (se 1 (by rfl) ⟨958091, by rfl⟩ : syracuseStep 1277455 = 1916183) B1916183
theorem B1916459 : Blo 1275956 1916459 := bstep (se 1 (by rfl) ⟨1437344, by rfl⟩ : syracuseStep 1916459 = 2874689) B2874689
theorem B2874923 : Blo 1275956 2874923 := bstep (se 1 (by rfl) ⟨2156192, by rfl⟩ : syracuseStep 2874923 = 4312385) B4312385
theorem B1277499 : Blo 1275956 1277499 := bstep (se 1 (by rfl) ⟨958124, by rfl⟩ : syracuseStep 1277499 = 1916249) B1916249
theorem B1916489 : Blo 1275956 1916489 := bstep (se 2 (by rfl) ⟨718683, by rfl⟩ : syracuseStep 1916489 = 1437367) B1437367
theorem B1277575 : Blo 1275956 1277575 := bstep (se 1 (by rfl) ⟨958181, by rfl⟩ : syracuseStep 1277575 = 1916363) B1916363
theorem B1277583 : Blo 1275956 1277583 := bstep (se 1 (by rfl) ⟨958187, by rfl⟩ : syracuseStep 1277583 = 1916375) B1916375
theorem B1277627 : Blo 1275956 1277627 := bstep (se 1 (by rfl) ⟨958220, by rfl⟩ : syracuseStep 1277627 = 1916441) B1916441
theorem B1916603 : Blo 1275956 1916603 := bstep (se 1 (by rfl) ⟨1437452, by rfl⟩ : syracuseStep 1916603 = 2874905) B2874905
theorem B1916663 : Blo 1275956 1916663 := bstep (se 1 (by rfl) ⟨1437497, by rfl⟩ : syracuseStep 1916663 = 2874995) B2874995
theorem B1277703 : Blo 1275956 1277703 := bstep (se 1 (by rfl) ⟨958277, by rfl⟩ : syracuseStep 1277703 = 1916555) B1916555
theorem B1277711 : Blo 1275956 1277711 := bstep (se 1 (by rfl) ⟨958283, by rfl⟩ : syracuseStep 1277711 = 1916567) B1916567
theorem B1916687 : Blo 1275956 1916687 := bstep (se 1 (by rfl) ⟨1437515, by rfl⟩ : syracuseStep 1916687 = 2875031) B2875031
theorem B1916729 : Blo 1275956 1916729 := bstep (se 2 (by rfl) ⟨718773, by rfl⟩ : syracuseStep 1916729 = 1437547) B1437547
theorem B1277755 : Blo 1275956 1277755 := bstep (se 1 (by rfl) ⟨958316, by rfl⟩ : syracuseStep 1277755 = 1916633) B1916633
theorem B24534859 : Blo 1275956 24534859 := bstep (se 1 (by rfl) ⟨18401144, by rfl⟩ : syracuseStep 24534859 = 36802289) B36802289
theorem B14540633 : Blo 1275956 14540633 := bstep (se 2 (by rfl) ⟨5452737, by rfl⟩ : syracuseStep 14540633 = 10905475) B10905475
theorem B3497863 : Blo 1275956 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B1277831 : Blo 1275956 1277831 := bstep (se 1 (by rfl) ⟨958373, by rfl⟩ : syracuseStep 1277831 = 1916747) B1916747
theorem B1916807 : Blo 1275956 1916807 := bstep (se 1 (by rfl) ⟨1437605, by rfl⟩ : syracuseStep 1916807 = 2875211) B2875211
theorem B1277839 : Blo 1275956 1277839 := bstep (se 1 (by rfl) ⟨958379, by rfl⟩ : syracuseStep 1277839 = 1916759) B1916759
theorem B2875283 : Blo 1275956 2875283 := bstep (se 1 (by rfl) ⟨2156462, by rfl⟩ : syracuseStep 2875283 = 4312925) B4312925
theorem B12443543 : Blo 1275956 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B1916843 : Blo 1275956 1916843 := bstep (se 1 (by rfl) ⟨1437632, by rfl⟩ : syracuseStep 1916843 = 2875265) B2875265
theorem B1277883 : Blo 1275956 1277883 := bstep (se 1 (by rfl) ⟨958412, by rfl⟩ : syracuseStep 1277883 = 1916825) B1916825
theorem B1916873 : Blo 1275956 1916873 := bstep (se 2 (by rfl) ⟨718827, by rfl⟩ : syracuseStep 1916873 = 1437655) B1437655
theorem B2875337 : Blo 1275956 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B2154505 : Blo 1275956 2154505 := bstep (se 2 (by rfl) ⟨807939, by rfl⟩ : syracuseStep 2154505 = 1615879) B1615879
theorem B4309145 : Blo 1275956 4309145 := bstep (se 2 (by rfl) ⟨1615929, by rfl⟩ : syracuseStep 4309145 = 3231859) B3231859
theorem B2154667 : Blo 1275956 2154667 := bstep (se 1 (by rfl) ⟨1616000, by rfl⟩ : syracuseStep 2154667 = 3232001) B3232001
theorem B2425079 : Blo 1275956 2425079 := bstep (se 1 (by rfl) ⟨1818809, by rfl⟩ : syracuseStep 2425079 = 3637619) B3637619
theorem B1294715 : Blo 1275956 1294715 := bstep (se 1 (by rfl) ⟨971036, by rfl⟩ : syracuseStep 1294715 = 1942073) B1942073
theorem B2425231 : Blo 1275956 2425231 := bstep (se 1 (by rfl) ⟨1818923, by rfl⟩ : syracuseStep 2425231 = 3637847) B3637847
theorem B2589089 : Blo 1275956 2589089 := bstep (se 2 (by rfl) ⟨970908, by rfl⟩ : syracuseStep 2589089 = 1941817) B1941817
theorem B4915657 : Blo 1275956 4915657 := bstep (se 2 (by rfl) ⟨1843371, by rfl⟩ : syracuseStep 4915657 = 3686743) B3686743
theorem B2154971 : Blo 1275956 2154971 := bstep (se 1 (by rfl) ⟨1616228, by rfl⟩ : syracuseStep 2154971 = 3232457) B3232457
theorem B15540761 : Blo 1275956 15540761 := bstep (se 2 (by rfl) ⟨5827785, by rfl⟩ : syracuseStep 15540761 = 11655571) B11655571
theorem B5825159 : Blo 1275956 5825159 := bstep (se 1 (by rfl) ⟨4368869, by rfl⟩ : syracuseStep 5825159 = 8737739) B8737739
theorem B2155207 : Blo 1275956 2155207 := bstep (se 1 (by rfl) ⟨1616405, by rfl⟩ : syracuseStep 2155207 = 3232811) B3232811
theorem B4850387 : Blo 1275956 4850387 := bstep (se 1 (by rfl) ⟨3637790, by rfl⟩ : syracuseStep 4850387 = 7275581) B7275581
theorem B6464285 : Blo 1275956 6464285 := bstep (se 3 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 6464285 = 2424107) B2424107
theorem B2155369 : Blo 1275956 2155369 := bstep (se 2 (by rfl) ⟨808263, by rfl⟩ : syracuseStep 2155369 = 1616527) B1616527
theorem B1532891 : Blo 1275956 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B6136985 : Blo 1275956 6136985 := bstep (se 2 (by rfl) ⟨2301369, by rfl⟩ : syracuseStep 6136985 = 4602739) B4602739
theorem B3638429 : Blo 1275956 3638429 := bstep (se 3 (by rfl) ⟨682205, by rfl⟩ : syracuseStep 3638429 = 1364411) B1364411
theorem B2426105 : Blo 1275956 2426105 := bstep (se 2 (by rfl) ⟨909789, by rfl⟩ : syracuseStep 2426105 = 1819579) B1819579
theorem B4310333 : Blo 1275956 4310333 := bstep (se 3 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 4310333 = 1616375) B1616375
theorem B4982159 : Blo 1275956 4982159 := bstep (se 1 (by rfl) ⟨3736619, by rfl⟩ : syracuseStep 4982159 = 7473239) B7473239
theorem B12445093 : Blo 1275956 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B139789745 : Blo 1275956 139789745 := bstep (se 2 (by rfl) ⟨52421154, by rfl⟩ : syracuseStep 139789745 = 104842309) B104842309
theorem B2155963 : Blo 1275956 2155963 := bstep (se 1 (by rfl) ⟨1616972, by rfl⟩ : syracuseStep 2155963 = 3233945) B3233945
theorem B52397513 : Blo 1275956 52397513 := bstep (se 2 (by rfl) ⟨19649067, by rfl⟩ : syracuseStep 52397513 = 39298135) B39298135
theorem B2156071 : Blo 1275956 2156071 := bstep (se 1 (by rfl) ⟨1617053, by rfl⟩ : syracuseStep 2156071 = 3234107) B3234107
theorem B6555275 : Blo 1275956 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B7268039 : Blo 1275956 7268039 := bstep (se 1 (by rfl) ⟨5451029, by rfl⟩ : syracuseStep 7268039 = 10902059) B10902059
theorem B7276331 : Blo 1275956 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B24561467 : Blo 1275956 24561467 := bstep (se 1 (by rfl) ⟨18421100, by rfl⟩ : syracuseStep 24561467 = 36842201) B36842201
theorem B2156395 : Blo 1275956 2156395 := bstep (se 1 (by rfl) ⟨1617296, by rfl⟩ : syracuseStep 2156395 = 3234593) B3234593
theorem B1435567 : Blo 1275956 1435567 := bstep (se 1 (by rfl) ⟨1076675, by rfl⟩ : syracuseStep 1435567 = 2153351) B2153351
theorem B2951099 : Blo 1275956 2951099 := bstep (se 1 (by rfl) ⟨2213324, by rfl⟩ : syracuseStep 2951099 = 4426649) B4426649
theorem B3450899 : Blo 1275956 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B9201701 : Blo 1275956 9201701 := bstep (se 4 (by rfl) ⟨862659, by rfl⟩ : syracuseStep 9201701 = 1725319) B1725319
theorem B3065935 : Blo 1275956 3065935 := bstep (se 1 (by rfl) ⟨2299451, by rfl⟩ : syracuseStep 3065935 = 4598903) B4598903
theorem B4728989 : Blo 1275956 4728989 := bstep (se 3 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 4728989 = 1773371) B1773371
theorem B4311197 : Blo 1275956 4311197 := bstep (se 3 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 4311197 = 1616699) B1616699
theorem B1435999 : Blo 1275956 1435999 := bstep (se 1 (by rfl) ⟨1076999, by rfl⟩ : syracuseStep 1435999 = 2153999) B2153999
theorem B3230057 : Blo 1275956 3230057 := bstep (se 2 (by rfl) ⟨1211271, by rfl⟩ : syracuseStep 3230057 = 2422543) B2422543
theorem B32713145 : Blo 1275956 32713145 := bstep (se 2 (by rfl) ⟨12267429, by rfl⟩ : syracuseStep 32713145 = 24534859) B24534859
theorem B8178185 : Blo 1275956 8178185 := bstep (se 2 (by rfl) ⟨3066819, by rfl⟩ : syracuseStep 8178185 = 6133639) B6133639
theorem B4663817 : Blo 1275956 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B9693755 : Blo 1275956 9693755 := bstep (se 1 (by rfl) ⟨7270316, by rfl⟩ : syracuseStep 9693755 = 14540633) B14540633
theorem B4311737 : Blo 1275956 4311737 := bstep (se 2 (by rfl) ⟨1616901, by rfl⟩ : syracuseStep 4311737 = 3233803) B3233803
theorem B1436359 : Blo 1275956 1436359 := bstep (se 1 (by rfl) ⟨1077269, by rfl⟩ : syracuseStep 1436359 = 2154539) B2154539
theorem B5450449 : Blo 1275956 5450449 := bstep (se 2 (by rfl) ⟨2043918, by rfl⟩ : syracuseStep 5450449 = 4087837) B4087837
theorem B17967965 : Blo 1275956 17967965 := bstep (se 3 (by rfl) ⟨3368993, by rfl⟩ : syracuseStep 17967965 = 6737987) B6737987
theorem B4312331 : Blo 1275956 4312331 := bstep (se 1 (by rfl) ⟨3234248, by rfl⟩ : syracuseStep 4312331 = 6468497) B6468497
theorem B14740825 : Blo 1275956 14740825 := bstep (se 2 (by rfl) ⟨5527809, by rfl⟩ : syracuseStep 14740825 = 11055619) B11055619
theorem B4312601 : Blo 1275956 4312601 := bstep (se 2 (by rfl) ⟨1617225, by rfl⟩ : syracuseStep 4312601 = 3234451) B3234451
theorem B1437223 : Blo 1275956 1437223 := bstep (se 1 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 1437223 = 2155835) B2155835
theorem B118042181 : Blo 1275956 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B34967159 : Blo 1275956 34967159 := bstep (se 1 (by rfl) ⟨26225369, by rfl⟩ : syracuseStep 34967159 = 52450739) B52450739
theorem B6901469 : Blo 1275956 6901469 := bstep (se 3 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 6901469 = 2588051) B2588051
theorem B4599595 : Blo 1275956 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B10907459 : Blo 1275956 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B4091809 : Blo 1275956 4091809 := bstep (se 2 (by rfl) ⟨1534428, by rfl⟩ : syracuseStep 4091809 = 3068857) B3068857
theorem B2871215 : Blo 1275956 2871215 := bstep (se 1 (by rfl) ⟨2153411, by rfl⟩ : syracuseStep 2871215 = 4306823) B4306823
theorem B6549511 : Blo 1275956 6549511 := bstep (se 1 (by rfl) ⟨4912133, by rfl⟩ : syracuseStep 6549511 = 9824267) B9824267
theorem B4599827 : Blo 1275956 4599827 := bstep (se 1 (by rfl) ⟨3449870, by rfl⟩ : syracuseStep 4599827 = 6899741) B6899741
theorem B3788957 : Blo 1275956 3788957 := bstep (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) B1420859
theorem B2871467 : Blo 1275956 2871467 := bstep (se 1 (by rfl) ⟨2153600, by rfl⟩ : syracuseStep 2871467 = 4307201) B4307201
theorem B36835505 : Blo 1275956 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B4845815 : Blo 1275956 4845815 := bstep (se 1 (by rfl) ⟨3634361, by rfl⟩ : syracuseStep 4845815 = 7268723) B7268723
theorem B4911641 : Blo 1275956 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B9703961 : Blo 1275956 9703961 := bstep (se 2 (by rfl) ⟨3638985, by rfl⟩ : syracuseStep 9703961 = 7277971) B7277971
theorem B6132257 : Blo 1275956 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B3232295 : Blo 1275956 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B2872007 : Blo 1275956 2872007 := bstep (se 1 (by rfl) ⟨2154005, by rfl⟩ : syracuseStep 2872007 = 4308011) B4308011
theorem B3232619 : Blo 1275956 3232619 := bstep (se 1 (by rfl) ⟨2424464, by rfl⟩ : syracuseStep 3232619 = 4848929) B4848929
theorem B3683233 : Blo 1275956 3683233 := bstep (se 2 (by rfl) ⟨1381212, by rfl⟩ : syracuseStep 3683233 = 2762425) B2762425
theorem B6468659 : Blo 1275956 6468659 := bstep (se 1 (by rfl) ⟨4851494, by rfl⟩ : syracuseStep 6468659 = 9702989) B9702989
theorem B3454109 : Blo 1275956 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B4846787 : Blo 1275956 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B8295695 : Blo 1275956 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B9205015 : Blo 1275956 9205015 := bstep (se 1 (by rfl) ⟨6903761, by rfl⟩ : syracuseStep 9205015 = 13807523) B13807523
theorem B8181157 : Blo 1275956 8181157 := bstep (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) B1533967
theorem B13284773 : Blo 1275956 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B1914287 : Blo 1275956 1914287 := bstep (se 1 (by rfl) ⟨1435715, by rfl⟩ : syracuseStep 1914287 = 2871431) B2871431
theorem B3233267 : Blo 1275956 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1914377 : Blo 1275956 1914377 := bstep (se 2 (by rfl) ⟨717891, by rfl⟩ : syracuseStep 1914377 = 1435783) B1435783
theorem B13809163 : Blo 1275956 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B1914407 : Blo 1275956 1914407 := bstep (se 1 (by rfl) ⟨1435805, by rfl⟩ : syracuseStep 1914407 = 2871611) B2871611
theorem B2872871 : Blo 1275956 2872871 := bstep (se 1 (by rfl) ⟨2154653, by rfl⟩ : syracuseStep 2872871 = 4309307) B4309307
theorem B4601441 : Blo 1275956 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B1914491 : Blo 1275956 1914491 := bstep (se 1 (by rfl) ⟨1435868, by rfl⟩ : syracuseStep 1914491 = 2871737) B2871737
theorem B7001747 : Blo 1275956 7001747 := bstep (se 1 (by rfl) ⟨5251310, by rfl⟩ : syracuseStep 7001747 = 10502621) B10502621
theorem B4847303 : Blo 1275956 4847303 := bstep (se 1 (by rfl) ⟨3635477, by rfl⟩ : syracuseStep 4847303 = 7270955) B7270955
theorem B3233479 : Blo 1275956 3233479 := bstep (se 1 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 3233479 = 4850219) B4850219
theorem B2914003 : Blo 1275956 2914003 := bstep (se 1 (by rfl) ⟨2185502, by rfl⟩ : syracuseStep 2914003 = 4371005) B4371005
theorem B1914617 : Blo 1275956 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B1914719 : Blo 1275956 1914719 := bstep (se 1 (by rfl) ⟨1436039, by rfl⟩ : syracuseStep 1914719 = 2872079) B2872079
theorem B1914731 : Blo 1275956 1914731 := bstep (se 1 (by rfl) ⟨1436048, by rfl⟩ : syracuseStep 1914731 = 2872097) B2872097
theorem B2873195 : Blo 1275956 2873195 := bstep (se 1 (by rfl) ⟨2154896, by rfl⟩ : syracuseStep 2873195 = 4309793) B4309793
theorem B8730487 : Blo 1275956 8730487 := bstep (se 1 (by rfl) ⟨6547865, by rfl⟩ : syracuseStep 8730487 = 13095731) B13095731
theorem B2873249 : Blo 1275956 2873249 := bstep (se 2 (by rfl) ⟨1077468, by rfl⟩ : syracuseStep 2873249 = 2154937) B2154937
theorem B2422703 : Blo 1275956 2422703 := bstep (se 1 (by rfl) ⟨1817027, by rfl⟩ : syracuseStep 2422703 = 3634055) B3634055
theorem B6215687 : Blo 1275956 6215687 := bstep (se 1 (by rfl) ⟨4661765, by rfl⟩ : syracuseStep 6215687 = 9323531) B9323531
theorem B5453831 : Blo 1275956 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B1275983 : Blo 1275956 1275983 := bstep (se 1 (by rfl) ⟨956987, by rfl⟩ : syracuseStep 1275983 = 1913975) B1913975
theorem B1914959 : Blo 1275956 1914959 := bstep (se 1 (by rfl) ⟨1436219, by rfl⟩ : syracuseStep 1914959 = 2872439) B2872439
theorem B1275999 : Blo 1275956 1275999 := bstep (se 1 (by rfl) ⟨956999, by rfl⟩ : syracuseStep 1275999 = 1913999) B1913999
theorem B1276027 : Blo 1275956 1276027 := bstep (se 1 (by rfl) ⟨957020, by rfl⟩ : syracuseStep 1276027 = 1914041) B1914041
theorem B16595077 : Blo 1275956 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B1276079 : Blo 1275956 1276079 := bstep (se 1 (by rfl) ⟨957059, by rfl⟩ : syracuseStep 1276079 = 1914119) B1914119
theorem B1276103 : Blo 1275956 1276103 := bstep (se 1 (by rfl) ⟨957077, by rfl⟩ : syracuseStep 1276103 = 1914155) B1914155
theorem B1915079 : Blo 1275956 1915079 := bstep (se 1 (by rfl) ⟨1436309, by rfl⟩ : syracuseStep 1915079 = 2872619) B2872619
theorem B1276123 : Blo 1275956 1276123 := bstep (se 1 (by rfl) ⟨957092, by rfl⟩ : syracuseStep 1276123 = 1914185) B1914185
theorem B2873591 : Blo 1275956 2873591 := bstep (se 1 (by rfl) ⟨2155193, by rfl⟩ : syracuseStep 2873591 = 4310387) B4310387
theorem B8411393 : Blo 1275956 8411393 := bstep (se 2 (by rfl) ⟨3154272, by rfl⟩ : syracuseStep 8411393 = 6308545) B6308545
theorem B1276199 : Blo 1275956 1276199 := bstep (se 1 (by rfl) ⟨957149, by rfl⟩ : syracuseStep 1276199 = 1914299) B1914299
theorem B1276239 : Blo 1275956 1276239 := bstep (se 1 (by rfl) ⟨957179, by rfl⟩ : syracuseStep 1276239 = 1914359) B1914359
theorem B1276255 : Blo 1275956 1276255 := bstep (se 1 (by rfl) ⟨957191, by rfl⟩ : syracuseStep 1276255 = 1914383) B1914383
theorem B2423135 : Blo 1275956 2423135 := bstep (se 1 (by rfl) ⟨1817351, by rfl⟩ : syracuseStep 2423135 = 3634703) B3634703
theorem B1915241 : Blo 1275956 1915241 := bstep (se 2 (by rfl) ⟨718215, by rfl⟩ : syracuseStep 1915241 = 1436431) B1436431
theorem B1276283 : Blo 1275956 1276283 := bstep (se 1 (by rfl) ⟨957212, by rfl⟩ : syracuseStep 1276283 = 1914425) B1914425
theorem B1276335 : Blo 1275956 1276335 := bstep (se 1 (by rfl) ⟨957251, by rfl⟩ : syracuseStep 1276335 = 1914503) B1914503
theorem B1915319 : Blo 1275956 1915319 := bstep (se 1 (by rfl) ⟨1436489, by rfl⟩ : syracuseStep 1915319 = 2872979) B2872979
theorem B1276359 : Blo 1275956 1276359 := bstep (se 1 (by rfl) ⟨957269, by rfl⟩ : syracuseStep 1276359 = 1914539) B1914539
theorem B1276379 : Blo 1275956 1276379 := bstep (se 1 (by rfl) ⟨957284, by rfl⟩ : syracuseStep 1276379 = 1914569) B1914569
theorem B1915355 : Blo 1275956 1915355 := bstep (se 1 (by rfl) ⟨1436516, by rfl⟩ : syracuseStep 1915355 = 2873033) B2873033
theorem B1276455 : Blo 1275956 1276455 := bstep (se 1 (by rfl) ⟨957341, by rfl⟩ : syracuseStep 1276455 = 1914683) B1914683
theorem B1276495 : Blo 1275956 1276495 := bstep (se 1 (by rfl) ⟨957371, by rfl⟩ : syracuseStep 1276495 = 1914743) B1914743
theorem B1276511 : Blo 1275956 1276511 := bstep (se 1 (by rfl) ⟨957383, by rfl⟩ : syracuseStep 1276511 = 1914767) B1914767
theorem B3234401 : Blo 1275956 3234401 := bstep (se 2 (by rfl) ⟨1212900, by rfl⟩ : syracuseStep 3234401 = 2425801) B2425801
theorem B4307579 : Blo 1275956 4307579 := bstep (se 1 (by rfl) ⟨3230684, by rfl⟩ : syracuseStep 4307579 = 6461369) B6461369
theorem B1276539 : Blo 1275956 1276539 := bstep (se 1 (by rfl) ⟨957404, by rfl⟩ : syracuseStep 1276539 = 1914809) B1914809
theorem B17947271 : Blo 1275956 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B4848275 : Blo 1275956 4848275 := bstep (se 1 (by rfl) ⟨3636206, by rfl⟩ : syracuseStep 4848275 = 7272413) B7272413
theorem B1276591 : Blo 1275956 1276591 := bstep (se 1 (by rfl) ⟨957443, by rfl⟩ : syracuseStep 1276591 = 1914887) B1914887
theorem B5176007 : Blo 1275956 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B1276615 : Blo 1275956 1276615 := bstep (se 1 (by rfl) ⟨957461, by rfl⟩ : syracuseStep 1276615 = 1914923) B1914923
theorem B5249747 : Blo 1275956 5249747 := bstep (se 1 (by rfl) ⟨3937310, by rfl⟩ : syracuseStep 5249747 = 7874621) B7874621
theorem B1276635 : Blo 1275956 1276635 := bstep (se 1 (by rfl) ⟨957476, by rfl⟩ : syracuseStep 1276635 = 1914953) B1914953
theorem B2153209 : Blo 1275956 2153209 := bstep (se 2 (by rfl) ⟨807453, by rfl⟩ : syracuseStep 2153209 = 1614907) B1614907
theorem B2300663 : Blo 1275956 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B4307741 : Blo 1275956 4307741 := bstep (se 3 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 4307741 = 1615403) B1615403
theorem B1276711 : Blo 1275956 1276711 := bstep (se 1 (by rfl) ⟨957533, by rfl⟩ : syracuseStep 1276711 = 1915067) B1915067
theorem B4848457 : Blo 1275956 4848457 := bstep (se 2 (by rfl) ⟨1818171, by rfl⟩ : syracuseStep 4848457 = 3636343) B3636343
theorem B2874185 : Blo 1275956 2874185 := bstep (se 2 (by rfl) ⟨1077819, by rfl⟩ : syracuseStep 2874185 = 2155639) B2155639
theorem B1276751 : Blo 1275956 1276751 := bstep (se 1 (by rfl) ⟨957563, by rfl⟩ : syracuseStep 1276751 = 1915127) B1915127
theorem B1276767 : Blo 1275956 1276767 := bstep (se 1 (by rfl) ⟨957575, by rfl⟩ : syracuseStep 1276767 = 1915151) B1915151
theorem B2046827 : Blo 1275956 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B1276795 : Blo 1275956 1276795 := bstep (se 1 (by rfl) ⟨957596, by rfl⟩ : syracuseStep 1276795 = 1915193) B1915193
theorem B5823407 : Blo 1275956 5823407 := bstep (se 1 (by rfl) ⟨4367555, by rfl⟩ : syracuseStep 5823407 = 8735111) B8735111
theorem B1276847 : Blo 1275956 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B1915823 : Blo 1275956 1915823 := bstep (se 1 (by rfl) ⟨1436867, by rfl⟩ : syracuseStep 1915823 = 2873735) B2873735
theorem B1276871 : Blo 1275956 1276871 := bstep (se 1 (by rfl) ⟨957653, by rfl⟩ : syracuseStep 1276871 = 1915307) B1915307
theorem B1276891 : Blo 1275956 1276891 := bstep (se 1 (by rfl) ⟨957668, by rfl⟩ : syracuseStep 1276891 = 1915337) B1915337
theorem B2153479 : Blo 1275956 2153479 := bstep (se 1 (by rfl) ⟨1615109, by rfl⟩ : syracuseStep 2153479 = 3230219) B3230219
theorem B1915913 : Blo 1275956 1915913 := bstep (se 2 (by rfl) ⟨718467, by rfl⟩ : syracuseStep 1915913 = 1436935) B1436935
theorem B1276967 : Blo 1275956 1276967 := bstep (se 1 (by rfl) ⟨957725, by rfl⟩ : syracuseStep 1276967 = 1915451) B1915451
theorem B1915943 : Blo 1275956 1915943 := bstep (se 1 (by rfl) ⟨1436957, by rfl⟩ : syracuseStep 1915943 = 2873915) B2873915
theorem B1277007 : Blo 1275956 1277007 := bstep (se 1 (by rfl) ⟨957755, by rfl⟩ : syracuseStep 1277007 = 1915511) B1915511
theorem B1277023 : Blo 1275956 1277023 := bstep (se 1 (by rfl) ⟨957767, by rfl⟩ : syracuseStep 1277023 = 1915535) B1915535
theorem B1277051 : Blo 1275956 1277051 := bstep (se 1 (by rfl) ⟨957788, by rfl⟩ : syracuseStep 1277051 = 1915577) B1915577
theorem B1916027 : Blo 1275956 1916027 := bstep (se 1 (by rfl) ⟨1437020, by rfl⟩ : syracuseStep 1916027 = 2874041) B2874041
theorem B1277103 : Blo 1275956 1277103 := bstep (se 1 (by rfl) ⟨957827, by rfl⟩ : syracuseStep 1277103 = 1915655) B1915655
theorem B1277127 : Blo 1275956 1277127 := bstep (se 1 (by rfl) ⟨957845, by rfl⟩ : syracuseStep 1277127 = 1915691) B1915691
theorem B1277147 : Blo 1275956 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B1916153 : Blo 1275956 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B18398501 : Blo 1275956 18398501 := bstep (se 4 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 18398501 = 3449719) B3449719
theorem B1277223 : Blo 1275956 1277223 := bstep (se 1 (by rfl) ⟨957917, by rfl⟩ : syracuseStep 1277223 = 1915835) B1915835
theorem B1277263 : Blo 1275956 1277263 := bstep (se 1 (by rfl) ⟨957947, by rfl⟩ : syracuseStep 1277263 = 1915895) B1915895
theorem B1277279 : Blo 1275956 1277279 := bstep (se 1 (by rfl) ⟨957959, by rfl⟩ : syracuseStep 1277279 = 1915919) B1915919
theorem B1916255 : Blo 1275956 1916255 := bstep (se 1 (by rfl) ⟨1437191, by rfl⟩ : syracuseStep 1916255 = 2874383) B2874383
theorem B1916267 : Blo 1275956 1916267 := bstep (se 1 (by rfl) ⟨1437200, by rfl⟩ : syracuseStep 1916267 = 2874401) B2874401
theorem B1277307 : Blo 1275956 1277307 := bstep (se 1 (by rfl) ⟨957980, by rfl⟩ : syracuseStep 1277307 = 1915961) B1915961
theorem B4365697 : Blo 1275956 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B7273871 : Blo 1275956 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B1277359 : Blo 1275956 1277359 := bstep (se 1 (by rfl) ⟨958019, by rfl⟩ : syracuseStep 1277359 = 1916039) B1916039
theorem B2153911 : Blo 1275956 2153911 := bstep (se 1 (by rfl) ⟨1615433, by rfl⟩ : syracuseStep 2153911 = 3230867) B3230867
theorem B1277383 : Blo 1275956 1277383 := bstep (se 1 (by rfl) ⟨958037, by rfl⟩ : syracuseStep 1277383 = 1916075) B1916075
theorem B4308443 : Blo 1275956 4308443 := bstep (se 1 (by rfl) ⟨3231332, by rfl⟩ : syracuseStep 4308443 = 6462665) B6462665
theorem B1277403 : Blo 1275956 1277403 := bstep (se 1 (by rfl) ⟨958052, by rfl⟩ : syracuseStep 1277403 = 1916105) B1916105
theorem B1818121 : Blo 1275956 1818121 := bstep (se 2 (by rfl) ⟨681795, by rfl⟩ : syracuseStep 1818121 = 1363591) B1363591
theorem B13811239 : Blo 1275956 13811239 := bstep (se 1 (by rfl) ⟨10358429, by rfl⟩ : syracuseStep 13811239 = 20716859) B20716859
theorem B1277479 : Blo 1275956 1277479 := bstep (se 1 (by rfl) ⟨958109, by rfl⟩ : syracuseStep 1277479 = 1916219) B1916219
theorem B41410115 : Blo 1275956 41410115 := bstep (se 1 (by rfl) ⟨31057586, by rfl⟩ : syracuseStep 41410115 = 62115173) B62115173
theorem B1277519 : Blo 1275956 1277519 := bstep (se 1 (by rfl) ⟨958139, by rfl⟩ : syracuseStep 1277519 = 1916279) B1916279
theorem B1916495 : Blo 1275956 1916495 := bstep (se 1 (by rfl) ⟨1437371, by rfl⟩ : syracuseStep 1916495 = 2874743) B2874743
theorem B1277535 : Blo 1275956 1277535 := bstep (se 1 (by rfl) ⟨958151, by rfl⟩ : syracuseStep 1277535 = 1916303) B1916303
theorem B5455457 : Blo 1275956 5455457 := bstep (se 2 (by rfl) ⟨2045796, by rfl⟩ : syracuseStep 5455457 = 4091593) B4091593
theorem B2874977 : Blo 1275956 2874977 := bstep (se 2 (by rfl) ⟨1078116, by rfl⟩ : syracuseStep 2874977 = 2156233) B2156233
theorem B2154107 : Blo 1275956 2154107 := bstep (se 1 (by rfl) ⟨1615580, by rfl⟩ : syracuseStep 2154107 = 3231161) B3231161
theorem B1277563 : Blo 1275956 1277563 := bstep (se 1 (by rfl) ⟨958172, by rfl⟩ : syracuseStep 1277563 = 1916345) B1916345
theorem B7274123 : Blo 1275956 7274123 := bstep (se 1 (by rfl) ⟨5455592, by rfl⟩ : syracuseStep 7274123 = 10911185) B10911185
theorem B1277615 : Blo 1275956 1277615 := bstep (se 1 (by rfl) ⟨958211, by rfl⟩ : syracuseStep 1277615 = 1916423) B1916423
theorem B1277639 : Blo 1275956 1277639 := bstep (se 1 (by rfl) ⟨958229, by rfl⟩ : syracuseStep 1277639 = 1916459) B1916459
theorem B1916615 : Blo 1275956 1916615 := bstep (se 1 (by rfl) ⟨1437461, by rfl⟩ : syracuseStep 1916615 = 2874923) B2874923
theorem B9690839 : Blo 1275956 9690839 := bstep (se 1 (by rfl) ⟨7268129, by rfl⟩ : syracuseStep 9690839 = 14536259) B14536259
theorem B1277659 : Blo 1275956 1277659 := bstep (se 1 (by rfl) ⟨958244, by rfl⟩ : syracuseStep 1277659 = 1916489) B1916489
theorem B1277735 : Blo 1275956 1277735 := bstep (se 1 (by rfl) ⟨958301, by rfl⟩ : syracuseStep 1277735 = 1916603) B1916603
theorem B1277775 : Blo 1275956 1277775 := bstep (se 1 (by rfl) ⟨958331, by rfl⟩ : syracuseStep 1277775 = 1916663) B1916663
theorem B1277791 : Blo 1275956 1277791 := bstep (se 1 (by rfl) ⟨958343, by rfl⟩ : syracuseStep 1277791 = 1916687) B1916687
theorem B1916777 : Blo 1275956 1916777 := bstep (se 2 (by rfl) ⟨718791, by rfl⟩ : syracuseStep 1916777 = 1437583) B1437583
theorem B1277819 : Blo 1275956 1277819 := bstep (se 1 (by rfl) ⟨958364, by rfl⟩ : syracuseStep 1277819 = 1916729) B1916729
theorem B1277871 : Blo 1275956 1277871 := bstep (se 1 (by rfl) ⟨958403, by rfl⟩ : syracuseStep 1277871 = 1916807) B1916807
theorem B1916855 : Blo 1275956 1916855 := bstep (se 1 (by rfl) ⟨1437641, by rfl⟩ : syracuseStep 1916855 = 2875283) B2875283
theorem B2875319 : Blo 1275956 2875319 := bstep (se 1 (by rfl) ⟨2156489, by rfl⟩ : syracuseStep 2875319 = 4312979) B4312979
theorem B1277895 : Blo 1275956 1277895 := bstep (se 1 (by rfl) ⟨958421, by rfl⟩ : syracuseStep 1277895 = 1916843) B1916843
theorem B1277915 : Blo 1275956 1277915 := bstep (se 1 (by rfl) ⟨958436, by rfl⟩ : syracuseStep 1277915 = 1916873) B1916873
theorem B1916891 : Blo 1275956 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B8732681 : Blo 1275956 8732681 := bstep (se 2 (by rfl) ⟨3274755, by rfl⟩ : syracuseStep 8732681 = 6549511) B6549511
theorem B4087913 : Blo 1275956 4087913 := bstep (se 2 (by rfl) ⟨1532967, by rfl⟩ : syracuseStep 4087913 = 3065935) B3065935
theorem B22126769 : Blo 1275956 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B4088171 : Blo 1275956 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B2154863 : Blo 1275956 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B3883439 : Blo 1275956 3883439 := bstep (se 1 (by rfl) ⟨2912579, by rfl⟩ : syracuseStep 3883439 = 5825159) B5825159
theorem B4309523 : Blo 1275956 4309523 := bstep (se 1 (by rfl) ⟨3232142, by rfl⟩ : syracuseStep 4309523 = 6464285) B6464285
theorem B2155079 : Blo 1275956 2155079 := bstep (se 1 (by rfl) ⟨1616309, by rfl⟩ : syracuseStep 2155079 = 3232619) B3232619
theorem B6554209 : Blo 1275956 6554209 := bstep (se 2 (by rfl) ⟨2457828, by rfl⟩ : syracuseStep 6554209 = 4915657) B4915657
theorem B22430381 : Blo 1275956 22430381 := bstep (se 3 (by rfl) ⟨4205696, by rfl⟩ : syracuseStep 22430381 = 8411393) B8411393
theorem B2425619 : Blo 1275956 2425619 := bstep (se 1 (by rfl) ⟨1819214, by rfl⟩ : syracuseStep 2425619 = 3638429) B3638429
theorem B2302739 : Blo 1275956 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B5530463 : Blo 1275956 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B7267265 : Blo 1275956 7267265 := bstep (se 2 (by rfl) ⟨2725224, by rfl⟩ : syracuseStep 7267265 = 5450449) B5450449
theorem B8856515 : Blo 1275956 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B93193163 : Blo 1275956 93193163 := bstep (se 1 (by rfl) ⟨69894872, by rfl⟩ : syracuseStep 93193163 = 139789745) B139789745
theorem B34931675 : Blo 1275956 34931675 := bstep (se 1 (by rfl) ⟨26198756, by rfl⟩ : syracuseStep 34931675 = 52397513) B52397513
theorem B2155511 : Blo 1275956 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B6464609 : Blo 1275956 6464609 := bstep (se 2 (by rfl) ⟨2424228, by rfl⟩ : syracuseStep 6464609 = 4848457) B4848457
theorem B4850887 : Blo 1275956 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B1615135 : Blo 1275956 1615135 := bstep (se 1 (by rfl) ⟨1211351, by rfl⟩ : syracuseStep 1615135 = 2422703) B2422703
theorem B1967399 : Blo 1275956 1967399 := bstep (se 1 (by rfl) ⟨1475549, by rfl⟩ : syracuseStep 1967399 = 2951099) B2951099
theorem B21808763 : Blo 1275956 21808763 := bstep (se 1 (by rfl) ⟨16356572, by rfl⟩ : syracuseStep 21808763 = 32713145) B32713145
theorem B12273353 : Blo 1275956 12273353 := bstep (se 2 (by rfl) ⟨4602507, by rfl⟩ : syracuseStep 12273353 = 9205015) B9205015
theorem B2156267 : Blo 1275956 2156267 := bstep (se 1 (by rfl) ⟨1617200, by rfl⟩ : syracuseStep 2156267 = 3234401) B3234401
theorem B19654433 : Blo 1275956 19654433 := bstep (se 2 (by rfl) ⟨7370412, by rfl⟩ : syracuseStep 19654433 = 14740825) B14740825
theorem B3450671 : Blo 1275956 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B3499831 : Blo 1275956 3499831 := bstep (se 1 (by rfl) ⟨2624873, by rfl⟩ : syracuseStep 3499831 = 5249747) B5249747
theorem B12265667 : Blo 1275956 12265667 := bstep (se 1 (by rfl) ⟨9199250, by rfl⟩ : syracuseStep 12265667 = 18398501) B18398501
theorem B4311305 : Blo 1275956 4311305 := bstep (se 2 (by rfl) ⟨1616739, by rfl⟩ : syracuseStep 4311305 = 3233479) B3233479
theorem B3885337 : Blo 1275956 3885337 := bstep (se 2 (by rfl) ⟨1457001, by rfl⟩ : syracuseStep 3885337 = 2914003) B2914003
theorem B5458205 : Blo 1275956 5458205 := bstep (se 3 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 5458205 = 2046827) B2046827
theorem B78694787 : Blo 1275956 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B1436071 : Blo 1275956 1436071 := bstep (se 1 (by rfl) ⟨1077053, by rfl⟩ : syracuseStep 1436071 = 2154107) B2154107
theorem B3066551 : Blo 1275956 3066551 := bstep (se 1 (by rfl) ⟨2299913, by rfl⟩ : syracuseStep 3066551 = 4599827) B4599827
theorem B14543549 : Blo 1275956 14543549 := bstep (se 3 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 14543549 = 5453831) B5453831
theorem B2525971 : Blo 1275956 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B3230543 : Blo 1275956 3230543 := bstep (se 1 (by rfl) ⟨2422907, by rfl⟩ : syracuseStep 3230543 = 4845815) B4845815
theorem B1436647 : Blo 1275956 1436647 := bstep (se 1 (by rfl) ⟨1077485, by rfl⟩ : syracuseStep 1436647 = 2154971) B2154971
theorem B12610637 : Blo 1275956 12610637 := bstep (se 3 (by rfl) ⟨2364494, by rfl⟩ : syracuseStep 12610637 = 4728989) B4728989
theorem B6466877 : Blo 1275956 6466877 := bstep (se 3 (by rfl) ⟨1212539, by rfl⟩ : syracuseStep 6466877 = 2425079) B2425079
theorem B4312439 : Blo 1275956 4312439 := bstep (se 1 (by rfl) ⟨3234329, by rfl⟩ : syracuseStep 4312439 = 6468659) B6468659
theorem B4091323 : Blo 1275956 4091323 := bstep (se 1 (by rfl) ⟨3068492, by rfl⟩ : syracuseStep 4091323 = 6136985) B6136985
theorem B3231191 : Blo 1275956 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B1617403 : Blo 1275956 1617403 := bstep (se 1 (by rfl) ⟨1213052, by rfl⟩ : syracuseStep 1617403 = 2426105) B2426105
theorem B3452573 : Blo 1275956 3452573 := bstep (se 3 (by rfl) ⟨647357, by rfl⟩ : syracuseStep 3452573 = 1294715) B1294715
theorem B2870945 : Blo 1275956 2870945 := bstep (se 2 (by rfl) ⟨1076604, by rfl⟩ : syracuseStep 2870945 = 2153209) B2153209
theorem B3067627 : Blo 1275956 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B4370183 : Blo 1275956 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B4845359 : Blo 1275956 4845359 := bstep (se 1 (by rfl) ⟨3634019, by rfl⟩ : syracuseStep 4845359 = 7268039) B7268039
theorem B3231535 : Blo 1275956 3231535 := bstep (se 1 (by rfl) ⟨2423651, by rfl⟩ : syracuseStep 3231535 = 4847303) B4847303
theorem B4910977 : Blo 1275956 4910977 := bstep (se 2 (by rfl) ⟨1841616, by rfl⟩ : syracuseStep 4910977 = 3683233) B3683233
theorem B2871305 : Blo 1275956 2871305 := bstep (se 2 (by rfl) ⟨1076739, by rfl⟩ : syracuseStep 2871305 = 2153479) B2153479
theorem B5452123 : Blo 1275956 5452123 := bstep (se 1 (by rfl) ⟨4089092, by rfl⟩ : syracuseStep 5452123 = 8178185) B8178185
theorem B3109211 : Blo 1275956 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B2871719 : Blo 1275956 2871719 := bstep (se 1 (by rfl) ⟨2153789, by rfl⟩ : syracuseStep 2871719 = 4307579) B4307579
theorem B11964847 : Blo 1275956 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B3232183 : Blo 1275956 3232183 := bstep (se 1 (by rfl) ⟨2424137, by rfl⟩ : syracuseStep 3232183 = 4848275) B4848275
theorem B5820929 : Blo 1275956 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B2871827 : Blo 1275956 2871827 := bstep (se 1 (by rfl) ⟨2153870, by rfl⟩ : syracuseStep 2871827 = 4307741) B4307741
theorem B10908209 : Blo 1275956 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B16593457 : Blo 1275956 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B2871881 : Blo 1275956 2871881 := bstep (se 2 (by rfl) ⟨1076955, by rfl⟩ : syracuseStep 2871881 = 2153911) B2153911
theorem B18412217 : Blo 1275956 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B2872295 : Blo 1275956 2872295 := bstep (se 1 (by rfl) ⟨2154221, by rfl⟩ : syracuseStep 2872295 = 4308443) B4308443
theorem B6132793 : Blo 1275956 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B23311439 : Blo 1275956 23311439 := bstep (se 1 (by rfl) ⟨17483579, by rfl⟩ : syracuseStep 23311439 = 34967159) B34967159
theorem B6460559 : Blo 1275956 6460559 := bstep (se 1 (by rfl) ⟨4845419, by rfl⟩ : syracuseStep 6460559 = 9690839) B9690839
theorem B4600979 : Blo 1275956 4600979 := bstep (se 1 (by rfl) ⟨3450734, by rfl⟩ : syracuseStep 4600979 = 6901469) B6901469
theorem B7271639 : Blo 1275956 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B1914089 : Blo 1275956 1914089 := bstep (se 2 (by rfl) ⟨717783, by rfl⟩ : syracuseStep 1914089 = 1435567) B1435567
theorem B1914143 : Blo 1275956 1914143 := bstep (se 1 (by rfl) ⟨1435607, by rfl⟩ : syracuseStep 1914143 = 2871215) B2871215
theorem B2872673 : Blo 1275956 2872673 := bstep (se 2 (by rfl) ⟨1077252, by rfl⟩ : syracuseStep 2872673 = 2154505) B2154505
theorem B2872763 : Blo 1275956 2872763 := bstep (se 1 (by rfl) ⟨2154572, by rfl⟩ : syracuseStep 2872763 = 4309145) B4309145
theorem B1914311 : Blo 1275956 1914311 := bstep (se 1 (by rfl) ⟨1435733, by rfl⟩ : syracuseStep 1914311 = 2871467) B2871467
theorem B24557003 : Blo 1275956 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B2872889 : Blo 1275956 2872889 := bstep (se 2 (by rfl) ⟨1077333, by rfl⟩ : syracuseStep 2872889 = 2154667) B2154667
theorem B3274427 : Blo 1275956 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B10360507 : Blo 1275956 10360507 := bstep (se 1 (by rfl) ⟨7770380, by rfl⟩ : syracuseStep 10360507 = 15540761) B15540761
theorem B6469307 : Blo 1275956 6469307 := bstep (se 1 (by rfl) ⟨4851980, by rfl⟩ : syracuseStep 6469307 = 9703961) B9703961
theorem B1914665 : Blo 1275956 1914665 := bstep (se 2 (by rfl) ⟨717999, by rfl⟩ : syracuseStep 1914665 = 1435999) B1435999
theorem B1914671 : Blo 1275956 1914671 := bstep (se 1 (by rfl) ⟨1436003, by rfl⟩ : syracuseStep 1914671 = 2872007) B2872007
theorem B3233591 : Blo 1275956 3233591 := bstep (se 1 (by rfl) ⟨2425193, by rfl⟩ : syracuseStep 3233591 = 4850387) B4850387
theorem B3233641 : Blo 1275956 3233641 := bstep (se 2 (by rfl) ⟨1212615, by rfl⟩ : syracuseStep 3233641 = 2425231) B2425231
theorem B2873555 : Blo 1275956 2873555 := bstep (se 1 (by rfl) ⟨2155166, by rfl⟩ : syracuseStep 2873555 = 4310333) B4310333
theorem B6461693 : Blo 1275956 6461693 := bstep (se 3 (by rfl) ⟨1211567, by rfl⟩ : syracuseStep 6461693 = 2423135) B2423135
theorem B1915145 : Blo 1275956 1915145 := bstep (se 2 (by rfl) ⟨718179, by rfl⟩ : syracuseStep 1915145 = 1436359) B1436359
theorem B2873609 : Blo 1275956 2873609 := bstep (se 2 (by rfl) ⟨1077603, by rfl⟩ : syracuseStep 2873609 = 2155207) B2155207
theorem B1276191 : Blo 1275956 1276191 := bstep (se 1 (by rfl) ⟨957143, by rfl⟩ : syracuseStep 1276191 = 1914287) B1914287
theorem B1276251 : Blo 1275956 1276251 := bstep (se 1 (by rfl) ⟨957188, by rfl⟩ : syracuseStep 1276251 = 1914377) B1914377
theorem B1276271 : Blo 1275956 1276271 := bstep (se 1 (by rfl) ⟨957203, by rfl⟩ : syracuseStep 1276271 = 1914407) B1914407
theorem B1915247 : Blo 1275956 1915247 := bstep (se 1 (by rfl) ⟨1436435, by rfl⟩ : syracuseStep 1915247 = 2872871) B2872871
theorem B13285757 : Blo 1275956 13285757 := bstep (se 3 (by rfl) ⟨2491079, by rfl⟩ : syracuseStep 13285757 = 4982159) B4982159
theorem B1276327 : Blo 1275956 1276327 := bstep (se 1 (by rfl) ⟨957245, by rfl⟩ : syracuseStep 1276327 = 1914491) B1914491
theorem B6904237 : Blo 1275956 6904237 := bstep (se 3 (by rfl) ⟨1294544, by rfl⟩ : syracuseStep 6904237 = 2589089) B2589089
theorem B4667831 : Blo 1275956 4667831 := bstep (se 1 (by rfl) ⟨3500873, by rfl⟩ : syracuseStep 4667831 = 7001747) B7001747
theorem B2873825 : Blo 1275956 2873825 := bstep (se 2 (by rfl) ⟨1077684, by rfl⟩ : syracuseStep 2873825 = 2155369) B2155369
theorem B1276411 : Blo 1275956 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B16374311 : Blo 1275956 16374311 := bstep (se 1 (by rfl) ⟨12280733, by rfl⟩ : syracuseStep 16374311 = 24561467) B24561467
theorem B1276479 : Blo 1275956 1276479 := bstep (se 1 (by rfl) ⟨957359, by rfl⟩ : syracuseStep 1276479 = 1914719) B1914719
theorem B1276487 : Blo 1275956 1276487 := bstep (se 1 (by rfl) ⟨957365, by rfl⟩ : syracuseStep 1276487 = 1914731) B1914731
theorem B1915463 : Blo 1275956 1915463 := bstep (se 1 (by rfl) ⟨1436597, by rfl⟩ : syracuseStep 1915463 = 2873195) B2873195
theorem B1915499 : Blo 1275956 1915499 := bstep (se 1 (by rfl) ⟨1436624, by rfl⟩ : syracuseStep 1915499 = 2873249) B2873249
theorem B4143791 : Blo 1275956 4143791 := bstep (se 1 (by rfl) ⟨3107843, by rfl⟩ : syracuseStep 4143791 = 6215687) B6215687
theorem B2300599 : Blo 1275956 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B6134467 : Blo 1275956 6134467 := bstep (se 1 (by rfl) ⟨4600850, by rfl⟩ : syracuseStep 6134467 = 9201701) B9201701
theorem B1276639 : Blo 1275956 1276639 := bstep (se 1 (by rfl) ⟨957479, by rfl⟩ : syracuseStep 1276639 = 1914959) B1914959
theorem B2874131 : Blo 1275956 2874131 := bstep (se 1 (by rfl) ⟨2155598, by rfl⟩ : syracuseStep 2874131 = 4311197) B4311197
theorem B1276719 : Blo 1275956 1276719 := bstep (se 1 (by rfl) ⟨957539, by rfl⟩ : syracuseStep 1276719 = 1915079) B1915079
theorem B1915727 : Blo 1275956 1915727 := bstep (se 1 (by rfl) ⟨1436795, by rfl⟩ : syracuseStep 1915727 = 2873591) B2873591
theorem B2153371 : Blo 1275956 2153371 := bstep (se 1 (by rfl) ⟨1615028, by rfl⟩ : syracuseStep 2153371 = 3230057) B3230057
theorem B1276827 : Blo 1275956 1276827 := bstep (se 1 (by rfl) ⟨957620, by rfl⟩ : syracuseStep 1276827 = 1915241) B1915241
theorem B1276879 : Blo 1275956 1276879 := bstep (se 1 (by rfl) ⟨957659, by rfl⟩ : syracuseStep 1276879 = 1915319) B1915319
theorem B1276903 : Blo 1275956 1276903 := bstep (se 1 (by rfl) ⟨957677, by rfl⟩ : syracuseStep 1276903 = 1915355) B1915355
theorem B6462503 : Blo 1275956 6462503 := bstep (se 1 (by rfl) ⟨4846877, by rfl⟩ : syracuseStep 6462503 = 9693755) B9693755
theorem B2874491 : Blo 1275956 2874491 := bstep (se 1 (by rfl) ⟨2155868, by rfl⟩ : syracuseStep 2874491 = 4311737) B4311737
theorem B1916123 : Blo 1275956 1916123 := bstep (se 1 (by rfl) ⟨1437092, by rfl⟩ : syracuseStep 1916123 = 2874185) B2874185
theorem B2874617 : Blo 1275956 2874617 := bstep (se 2 (by rfl) ⟨1077981, by rfl⟩ : syracuseStep 2874617 = 2155963) B2155963
theorem B3882271 : Blo 1275956 3882271 := bstep (se 1 (by rfl) ⟨2911703, by rfl⟩ : syracuseStep 3882271 = 5823407) B5823407
theorem B1277215 : Blo 1275956 1277215 := bstep (se 1 (by rfl) ⟨957911, by rfl⟩ : syracuseStep 1277215 = 1915823) B1915823
theorem B46562597 : Blo 1275956 46562597 := bstep (se 4 (by rfl) ⟨4365243, by rfl⟩ : syracuseStep 46562597 = 8730487) B8730487
theorem B6135101 : Blo 1275956 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B1277275 : Blo 1275956 1277275 := bstep (se 1 (by rfl) ⟨957956, by rfl⟩ : syracuseStep 1277275 = 1915913) B1915913
theorem B2424161 : Blo 1275956 2424161 := bstep (se 2 (by rfl) ⟨909060, by rfl⟩ : syracuseStep 2424161 = 1818121) B1818121
theorem B1277295 : Blo 1275956 1277295 := bstep (se 1 (by rfl) ⟨957971, by rfl⟩ : syracuseStep 1277295 = 1915943) B1915943
theorem B18414985 : Blo 1275956 18414985 := bstep (se 2 (by rfl) ⟨6905619, by rfl⟩ : syracuseStep 18414985 = 13811239) B13811239
theorem B1916297 : Blo 1275956 1916297 := bstep (se 2 (by rfl) ⟨718611, by rfl⟩ : syracuseStep 1916297 = 1437223) B1437223
theorem B2874761 : Blo 1275956 2874761 := bstep (se 2 (by rfl) ⟨1078035, by rfl⟩ : syracuseStep 2874761 = 2156071) B2156071
theorem B1277351 : Blo 1275956 1277351 := bstep (se 1 (by rfl) ⟨958013, by rfl⟩ : syracuseStep 1277351 = 1916027) B1916027
theorem B1277435 : Blo 1275956 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B2874887 : Blo 1275956 2874887 := bstep (se 1 (by rfl) ⟨2156165, by rfl⟩ : syracuseStep 2874887 = 4312331) B4312331
theorem B1277503 : Blo 1275956 1277503 := bstep (se 1 (by rfl) ⟨958127, by rfl⟩ : syracuseStep 1277503 = 1916255) B1916255
theorem B1277511 : Blo 1275956 1277511 := bstep (se 1 (by rfl) ⟨958133, by rfl⟩ : syracuseStep 1277511 = 1916267) B1916267
theorem B47914573 : Blo 1275956 47914573 := bstep (se 3 (by rfl) ⟨8983982, by rfl⟩ : syracuseStep 47914573 = 17967965) B17967965
theorem B4849247 : Blo 1275956 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B2875067 : Blo 1275956 2875067 := bstep (se 1 (by rfl) ⟨2156300, by rfl⟩ : syracuseStep 2875067 = 4312601) B4312601
theorem B27606743 : Blo 1275956 27606743 := bstep (se 1 (by rfl) ⟨20705057, by rfl⟩ : syracuseStep 27606743 = 41410115) B41410115
theorem B1277663 : Blo 1275956 1277663 := bstep (se 1 (by rfl) ⟨958247, by rfl⟩ : syracuseStep 1277663 = 1916495) B1916495
theorem B3636971 : Blo 1275956 3636971 := bstep (se 1 (by rfl) ⟨2727728, by rfl⟩ : syracuseStep 3636971 = 5455457) B5455457
theorem B1916651 : Blo 1275956 1916651 := bstep (se 1 (by rfl) ⟨1437488, by rfl⟩ : syracuseStep 1916651 = 2874977) B2874977
theorem B4849415 : Blo 1275956 4849415 := bstep (se 1 (by rfl) ⟨3637061, by rfl⟩ : syracuseStep 4849415 = 7274123) B7274123
theorem B1277743 : Blo 1275956 1277743 := bstep (se 1 (by rfl) ⟨958307, by rfl⟩ : syracuseStep 1277743 = 1916615) B1916615
theorem B2875193 : Blo 1275956 2875193 := bstep (se 2 (by rfl) ⟨1078197, by rfl⟩ : syracuseStep 2875193 = 2156395) B2156395
theorem B5455745 : Blo 1275956 5455745 := bstep (se 2 (by rfl) ⟨2045904, by rfl⟩ : syracuseStep 5455745 = 4091809) B4091809
theorem B1277851 : Blo 1275956 1277851 := bstep (se 1 (by rfl) ⟨958388, by rfl⟩ : syracuseStep 1277851 = 1916777) B1916777
theorem B4087709 : Blo 1275956 4087709 := bstep (se 3 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 4087709 = 1532891) B1532891
theorem B1277903 : Blo 1275956 1277903 := bstep (se 1 (by rfl) ⟨958427, by rfl⟩ : syracuseStep 1277903 = 1916855) B1916855
theorem B1916879 : Blo 1275956 1916879 := bstep (se 1 (by rfl) ⟨1437659, by rfl⟩ : syracuseStep 1916879 = 2875319) B2875319
theorem B1277927 : Blo 1275956 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B2072807 : Blo 1275956 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B2588959 : Blo 1275956 2588959 := bstep (se 1 (by rfl) ⟨1941719, by rfl⟩ : syracuseStep 2588959 = 3883439) B3883439
theorem B3686975 : Blo 1275956 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B4309577 : Blo 1275956 4309577 := bstep (se 2 (by rfl) ⟨1616091, by rfl⟩ : syracuseStep 4309577 = 3232183) B3232183
theorem B62128775 : Blo 1275956 62128775 := bstep (se 1 (by rfl) ⟨46596581, by rfl⟩ : syracuseStep 62128775 = 93193163) B93193163
theorem B15540959 : Blo 1275956 15540959 := bstep (se 1 (by rfl) ⟨11655719, by rfl⟩ : syracuseStep 15540959 = 23311439) B23311439
theorem B4309739 : Blo 1275956 4309739 := bstep (se 1 (by rfl) ⟨3232304, by rfl⟩ : syracuseStep 4309739 = 6464609) B6464609
theorem B1311599 : Blo 1275956 1311599 := bstep (se 1 (by rfl) ⟨983699, by rfl⟩ : syracuseStep 1311599 = 1967399) B1967399
theorem B2155727 : Blo 1275956 2155727 := bstep (se 1 (by rfl) ⟨1616795, by rfl⟩ : syracuseStep 2155727 = 3233591) B3233591
theorem B8177057 : Blo 1275956 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B8177111 : Blo 1275956 8177111 := bstep (se 1 (by rfl) ⟨6132833, by rfl⟩ : syracuseStep 8177111 = 12265667) B12265667
theorem B8857171 : Blo 1275956 8857171 := bstep (se 1 (by rfl) ⟨6642878, by rfl⟩ : syracuseStep 8857171 = 13285757) B13285757
theorem B215549525 : Blo 1275956 215549525 := bstep (se 8 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 215549525 = 2525971) B2525971
theorem B2762527 : Blo 1275956 2762527 := bstep (se 1 (by rfl) ⟨2071895, by rfl⟩ : syracuseStep 2762527 = 4143791) B4143791
theorem B24553313 : Blo 1275956 24553313 := bstep (se 2 (by rfl) ⟨9207492, by rfl⟩ : syracuseStep 24553313 = 18414985) B18414985
theorem B2156537 : Blo 1275956 2156537 := bstep (se 2 (by rfl) ⟨808701, by rfl⟩ : syracuseStep 2156537 = 1617403) B1617403
theorem B8407091 : Blo 1275956 8407091 := bstep (se 1 (by rfl) ⟨6305318, by rfl⟩ : syracuseStep 8407091 = 12610637) B12610637
theorem B31041731 : Blo 1275956 31041731 := bstep (se 1 (by rfl) ⟨23281298, by rfl⟩ : syracuseStep 31041731 = 46562597) B46562597
theorem B4090067 : Blo 1275956 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B4311251 : Blo 1275956 4311251 := bstep (se 1 (by rfl) ⟨3233438, by rfl⟩ : syracuseStep 4311251 = 6466877) B6466877
theorem B1616107 : Blo 1275956 1616107 := bstep (se 1 (by rfl) ⟨1212080, by rfl⟩ : syracuseStep 1616107 = 2424161) B2424161
theorem B13814009 : Blo 1275956 13814009 := bstep (se 2 (by rfl) ⟨5180253, by rfl⟩ : syracuseStep 13814009 = 10360507) B10360507
theorem B4090169 : Blo 1275956 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B4311521 : Blo 1275956 4311521 := bstep (se 2 (by rfl) ⟨1616820, by rfl⟩ : syracuseStep 4311521 = 3233641) B3233641
theorem B6547969 : Blo 1275956 6547969 := bstep (se 2 (by rfl) ⟨2455488, by rfl⟩ : syracuseStep 6547969 = 4910977) B4910977
theorem B3230239 : Blo 1275956 3230239 := bstep (se 1 (by rfl) ⟨2422679, by rfl⟩ : syracuseStep 3230239 = 4845359) B4845359
theorem B1436575 : Blo 1275956 1436575 := bstep (se 1 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 1436575 = 2154863) B2154863
theorem B5180449 : Blo 1275956 5180449 := bstep (se 2 (by rfl) ⟨1942668, by rfl⟩ : syracuseStep 5180449 = 3885337) B3885337
theorem B1436719 : Blo 1275956 1436719 := bstep (se 1 (by rfl) ⟨1077539, by rfl⟩ : syracuseStep 1436719 = 2155079) B2155079
theorem B7269497 : Blo 1275956 7269497 := bstep (se 2 (by rfl) ⟨2726061, by rfl⟩ : syracuseStep 7269497 = 5452123) B5452123
theorem B12274811 : Blo 1275956 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B1617079 : Blo 1275956 1617079 := bstep (se 1 (by rfl) ⟨1212809, by rfl⟩ : syracuseStep 1617079 = 2425619) B2425619
theorem B1535159 : Blo 1275956 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B15953129 : Blo 1275956 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B4844843 : Blo 1275956 4844843 := bstep (se 1 (by rfl) ⟨3633632, by rfl⟩ : syracuseStep 4844843 = 7267265) B7267265
theorem B1437007 : Blo 1275956 1437007 := bstep (se 1 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 1437007 = 2155511) B2155511
theorem B3067319 : Blo 1275956 3067319 := bstep (se 1 (by rfl) ⟨2300489, by rfl⟩ : syracuseStep 3067319 = 4600979) B4600979
theorem B3067465 : Blo 1275956 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B8179289 : Blo 1275956 8179289 := bstep (se 2 (by rfl) ⟨3067233, by rfl⟩ : syracuseStep 8179289 = 6134467) B6134467
theorem B16371335 : Blo 1275956 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B2182951 : Blo 1275956 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B4312871 : Blo 1275956 4312871 := bstep (se 1 (by rfl) ⟨3234653, by rfl⟩ : syracuseStep 4312871 = 6469307) B6469307
theorem B1437511 : Blo 1275956 1437511 := bstep (se 1 (by rfl) ⟨1078133, by rfl⟩ : syracuseStep 1437511 = 2156267) B2156267
theorem B13102955 : Blo 1275956 13102955 := bstep (se 1 (by rfl) ⟨9827216, by rfl⟩ : syracuseStep 13102955 = 19654433) B19654433
theorem B2871161 : Blo 1275956 2871161 := bstep (se 2 (by rfl) ⟨1076685, by rfl⟩ : syracuseStep 2871161 = 2153371) B2153371
theorem B6467849 : Blo 1275956 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B18665765 : Blo 1275956 18665765 := bstep (se 4 (by rfl) ⟨1749915, by rfl⟩ : syracuseStep 18665765 = 3499831) B3499831
theorem B10916207 : Blo 1275956 10916207 := bstep (se 1 (by rfl) ⟨8187155, by rfl⟩ : syracuseStep 10916207 = 16374311) B16374311
theorem B59814349 : Blo 1275956 59814349 := bstep (se 3 (by rfl) ⟨11215190, by rfl⟩ : syracuseStep 59814349 = 22430381) B22430381
theorem B2044367 : Blo 1275956 2044367 := bstep (se 1 (by rfl) ⟨1533275, by rfl⟩ : syracuseStep 2044367 = 3066551) B3066551
theorem B9695699 : Blo 1275956 9695699 := bstep (se 1 (by rfl) ⟨7271774, by rfl⟩ : syracuseStep 9695699 = 14543549) B14543549
theorem B63886097 : Blo 1275956 63886097 := bstep (se 2 (by rfl) ⟨23957286, by rfl⟩ : syracuseStep 63886097 = 47914573) B47914573
theorem B3232831 : Blo 1275956 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B1913963 : Blo 1275956 1913963 := bstep (se 1 (by rfl) ⟨1435472, by rfl⟩ : syracuseStep 1913963 = 2870945) B2870945
theorem B18404495 : Blo 1275956 18404495 := bstep (se 1 (by rfl) ⟨13803371, by rfl⟩ : syracuseStep 18404495 = 27606743) B27606743
theorem B3232943 : Blo 1275956 3232943 := bstep (se 1 (by rfl) ⟨2424707, by rfl⟩ : syracuseStep 3232943 = 4849415) B4849415
theorem B2913455 : Blo 1275956 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B2725139 : Blo 1275956 2725139 := bstep (se 1 (by rfl) ⟨2043854, by rfl⟩ : syracuseStep 2725139 = 4087709) B4087709
theorem B1914203 : Blo 1275956 1914203 := bstep (se 1 (by rfl) ⟨1435652, by rfl⟩ : syracuseStep 1914203 = 2871305) B2871305
theorem B5821787 : Blo 1275956 5821787 := bstep (se 1 (by rfl) ⟨4366340, by rfl⟩ : syracuseStep 5821787 = 8732681) B8732681
theorem B14751179 : Blo 1275956 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B2725447 : Blo 1275956 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B10901101 : Blo 1275956 10901101 := bstep (se 3 (by rfl) ⟨2043956, by rfl⟩ : syracuseStep 10901101 = 4087913) B4087913
theorem B1914479 : Blo 1275956 1914479 := bstep (se 1 (by rfl) ⟨1435859, by rfl⟩ : syracuseStep 1914479 = 2871719) B2871719
theorem B3880619 : Blo 1275956 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B1914551 : Blo 1275956 1914551 := bstep (se 1 (by rfl) ⟨1435913, by rfl⟩ : syracuseStep 1914551 = 2871827) B2871827
theorem B2873015 : Blo 1275956 2873015 := bstep (se 1 (by rfl) ⟨2154761, by rfl⟩ : syracuseStep 2873015 = 4309523) B4309523
theorem B7272139 : Blo 1275956 7272139 := bstep (se 1 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 7272139 = 10908209) B10908209
theorem B1914587 : Blo 1275956 1914587 := bstep (se 1 (by rfl) ⟨1435940, by rfl⟩ : syracuseStep 1914587 = 2871881) B2871881
theorem B1914761 : Blo 1275956 1914761 := bstep (se 2 (by rfl) ⟨718035, by rfl⟩ : syracuseStep 1914761 = 1436071) B1436071
theorem B9205649 : Blo 1275956 9205649 := bstep (se 2 (by rfl) ⟨3452118, by rfl⟩ : syracuseStep 9205649 = 6904237) B6904237
theorem B5904343 : Blo 1275956 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B1914863 : Blo 1275956 1914863 := bstep (se 1 (by rfl) ⟨1436147, by rfl⟩ : syracuseStep 1914863 = 2872295) B2872295
theorem B22124609 : Blo 1275956 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B14555213 : Blo 1275956 14555213 := bstep (se 3 (by rfl) ⟨2729102, by rfl⟩ : syracuseStep 14555213 = 5458205) B5458205
theorem B4307039 : Blo 1275956 4307039 := bstep (se 1 (by rfl) ⟨3230279, by rfl⟩ : syracuseStep 4307039 = 6460559) B6460559
theorem B8738945 : Blo 1275956 8738945 := bstep (se 2 (by rfl) ⟨3277104, by rfl⟩ : syracuseStep 8738945 = 6554209) B6554209
theorem B4847759 : Blo 1275956 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1276059 : Blo 1275956 1276059 := bstep (se 1 (by rfl) ⟨957044, by rfl⟩ : syracuseStep 1276059 = 1914089) B1914089
theorem B1276095 : Blo 1275956 1276095 := bstep (se 1 (by rfl) ⟨957071, by rfl⟩ : syracuseStep 1276095 = 1914143) B1914143
theorem B1915115 : Blo 1275956 1915115 := bstep (se 1 (by rfl) ⟨1436336, by rfl⟩ : syracuseStep 1915115 = 2872673) B2872673
theorem B1915175 : Blo 1275956 1915175 := bstep (se 1 (by rfl) ⟨1436381, by rfl⟩ : syracuseStep 1915175 = 2872763) B2872763
theorem B1276207 : Blo 1275956 1276207 := bstep (se 1 (by rfl) ⟨957155, by rfl⟩ : syracuseStep 1276207 = 1914311) B1914311
theorem B209852765 : Blo 1275956 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B1915259 : Blo 1275956 1915259 := bstep (se 1 (by rfl) ⟨1436444, by rfl⟩ : syracuseStep 1915259 = 2872889) B2872889
theorem B14539175 : Blo 1275956 14539175 := bstep (se 1 (by rfl) ⟨10904381, by rfl⟩ : syracuseStep 14539175 = 21808763) B21808763
theorem B8182235 : Blo 1275956 8182235 := bstep (se 1 (by rfl) ⟨6136676, by rfl⟩ : syracuseStep 8182235 = 12273353) B12273353
theorem B1276443 : Blo 1275956 1276443 := bstep (se 1 (by rfl) ⟨957332, by rfl⟩ : syracuseStep 1276443 = 1914665) B1914665
theorem B1276447 : Blo 1275956 1276447 := bstep (se 1 (by rfl) ⟨957335, by rfl⟩ : syracuseStep 1276447 = 1914671) B1914671
theorem B2300447 : Blo 1275956 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B1915529 : Blo 1275956 1915529 := bstep (se 2 (by rfl) ⟨718323, by rfl⟩ : syracuseStep 1915529 = 1436647) B1436647
theorem B1915703 : Blo 1275956 1915703 := bstep (se 1 (by rfl) ⟨1436777, by rfl⟩ : syracuseStep 1915703 = 2873555) B2873555
theorem B4307795 : Blo 1275956 4307795 := bstep (se 1 (by rfl) ⟨3230846, by rfl⟩ : syracuseStep 4307795 = 6461693) B6461693
theorem B1276763 : Blo 1275956 1276763 := bstep (se 1 (by rfl) ⟨957572, by rfl⟩ : syracuseStep 1276763 = 1915145) B1915145
theorem B1915739 : Blo 1275956 1915739 := bstep (se 1 (by rfl) ⟨1436804, by rfl⟩ : syracuseStep 1915739 = 2873609) B2873609
theorem B2874203 : Blo 1275956 2874203 := bstep (se 1 (by rfl) ⟨2155652, by rfl⟩ : syracuseStep 2874203 = 4311305) B4311305
theorem B1276831 : Blo 1275956 1276831 := bstep (se 1 (by rfl) ⟨957623, by rfl⟩ : syracuseStep 1276831 = 1915247) B1915247
theorem B3111887 : Blo 1275956 3111887 := bstep (se 1 (by rfl) ⟨2333915, by rfl⟩ : syracuseStep 3111887 = 4667831) B4667831
theorem B1915883 : Blo 1275956 1915883 := bstep (se 1 (by rfl) ⟨1436912, by rfl⟩ : syracuseStep 1915883 = 2873825) B2873825
theorem B2153513 : Blo 1275956 2153513 := bstep (se 2 (by rfl) ⟨807567, by rfl⟩ : syracuseStep 2153513 = 1615135) B1615135
theorem B5176361 : Blo 1275956 5176361 := bstep (se 2 (by rfl) ⟨1941135, by rfl⟩ : syracuseStep 5176361 = 3882271) B3882271
theorem B1276975 : Blo 1275956 1276975 := bstep (se 1 (by rfl) ⟨957731, by rfl⟩ : syracuseStep 1276975 = 1915463) B1915463
theorem B1276999 : Blo 1275956 1276999 := bstep (se 1 (by rfl) ⟨957749, by rfl⟩ : syracuseStep 1276999 = 1915499) B1915499
theorem B1916087 : Blo 1275956 1916087 := bstep (se 1 (by rfl) ⟨1437065, by rfl⟩ : syracuseStep 1916087 = 2874131) B2874131
theorem B2153695 : Blo 1275956 2153695 := bstep (se 1 (by rfl) ⟨1615271, by rfl⟩ : syracuseStep 2153695 = 3230543) B3230543
theorem B1277151 : Blo 1275956 1277151 := bstep (se 1 (by rfl) ⟨957863, by rfl⟩ : syracuseStep 1277151 = 1915727) B1915727
theorem B5455097 : Blo 1275956 5455097 := bstep (se 2 (by rfl) ⟨2045661, by rfl⟩ : syracuseStep 5455097 = 4091323) B4091323
theorem B4308335 : Blo 1275956 4308335 := bstep (se 1 (by rfl) ⟨3231251, by rfl⟩ : syracuseStep 4308335 = 6462503) B6462503
theorem B1916327 : Blo 1275956 1916327 := bstep (se 1 (by rfl) ⟨1437245, by rfl⟩ : syracuseStep 1916327 = 2874491) B2874491
theorem B1277415 : Blo 1275956 1277415 := bstep (se 1 (by rfl) ⟨958061, by rfl⟩ : syracuseStep 1277415 = 1916123) B1916123
theorem B1916411 : Blo 1275956 1916411 := bstep (se 1 (by rfl) ⟨1437308, by rfl⟩ : syracuseStep 1916411 = 2874617) B2874617
theorem B2874959 : Blo 1275956 2874959 := bstep (se 1 (by rfl) ⟨2156219, by rfl⟩ : syracuseStep 2874959 = 4312439) B4312439
theorem B1277531 : Blo 1275956 1277531 := bstep (se 1 (by rfl) ⟨958148, by rfl⟩ : syracuseStep 1277531 = 1916297) B1916297
theorem B1916507 : Blo 1275956 1916507 := bstep (se 1 (by rfl) ⟨1437380, by rfl⟩ : syracuseStep 1916507 = 2874761) B2874761
theorem B2154127 : Blo 1275956 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B1916591 : Blo 1275956 1916591 := bstep (se 1 (by rfl) ⟨1437443, by rfl⟩ : syracuseStep 1916591 = 2874887) B2874887
theorem B4308713 : Blo 1275956 4308713 := bstep (se 2 (by rfl) ⟨1615767, by rfl⟩ : syracuseStep 4308713 = 3231535) B3231535
theorem B2301715 : Blo 1275956 2301715 := bstep (se 1 (by rfl) ⟨1726286, by rfl⟩ : syracuseStep 2301715 = 3452573) B3452573
theorem B1916711 : Blo 1275956 1916711 := bstep (se 1 (by rfl) ⟨1437533, by rfl⟩ : syracuseStep 1916711 = 2875067) B2875067
theorem B2424647 : Blo 1275956 2424647 := bstep (se 1 (by rfl) ⟨1818485, by rfl⟩ : syracuseStep 2424647 = 3636971) B3636971
theorem B1277767 : Blo 1275956 1277767 := bstep (se 1 (by rfl) ⟨958325, by rfl⟩ : syracuseStep 1277767 = 1916651) B1916651
theorem B1916795 : Blo 1275956 1916795 := bstep (se 1 (by rfl) ⟨1437596, by rfl⟩ : syracuseStep 1916795 = 2875193) B2875193
theorem B93151133 : Blo 1275956 93151133 := bstep (se 3 (by rfl) ⟨17465837, by rfl⟩ : syracuseStep 93151133 = 34931675) B34931675
theorem B3637163 : Blo 1275956 3637163 := bstep (se 1 (by rfl) ⟨2727872, by rfl⟩ : syracuseStep 3637163 = 5455745) B5455745
theorem B1277919 : Blo 1275956 1277919 := bstep (se 1 (by rfl) ⟨958439, by rfl⟩ : syracuseStep 1277919 = 1916879) B1916879
theorem B12443843 : Blo 1275956 12443843 := bstep (se 1 (by rfl) ⟨9332882, by rfl⟩ : syracuseStep 12443843 = 18665765) B18665765
theorem B6463799 : Blo 1275956 6463799 := bstep (se 1 (by rfl) ⟨4847849, by rfl⟩ : syracuseStep 6463799 = 9695699) B9695699
theorem B2154809 : Blo 1275956 2154809 := bstep (se 2 (by rfl) ⟨808053, by rfl⟩ : syracuseStep 2154809 = 1616107) B1616107
theorem B2457983 : Blo 1275956 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B41419183 : Blo 1275956 41419183 := bstep (se 1 (by rfl) ⟨31064387, by rfl⟩ : syracuseStep 41419183 = 62128775) B62128775
theorem B2155295 : Blo 1275956 2155295 := bstep (se 1 (by rfl) ⟨1616471, by rfl⟩ : syracuseStep 2155295 = 3232943) B3232943
theorem B1942303 : Blo 1275956 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B16368875 : Blo 1275956 16368875 := bstep (se 1 (by rfl) ⟨12276656, by rfl⟩ : syracuseStep 16368875 = 24553313) B24553313
theorem B6137099 : Blo 1275956 6137099 := bstep (se 1 (by rfl) ⟨4602824, by rfl⟩ : syracuseStep 6137099 = 9205649) B9205649
theorem B5604727 : Blo 1275956 5604727 := bstep (se 1 (by rfl) ⟨4203545, by rfl⟩ : syracuseStep 5604727 = 8407091) B8407091
theorem B6907265 : Blo 1275956 6907265 := bstep (se 2 (by rfl) ⟨2590224, by rfl⟩ : syracuseStep 6907265 = 5180449) B5180449
theorem B4310441 : Blo 1275956 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B5825963 : Blo 1275956 5825963 := bstep (se 1 (by rfl) ⟨4369472, by rfl⟩ : syracuseStep 5825963 = 8738945) B8738945
theorem B20694487 : Blo 1275956 20694487 := bstep (se 1 (by rfl) ⟨15520865, by rfl⟩ : syracuseStep 20694487 = 31041731) B31041731
theorem B9209339 : Blo 1275956 9209339 := bstep (se 1 (by rfl) ⟨6907004, by rfl⟩ : syracuseStep 9209339 = 13814009) B13814009
theorem B2156105 : Blo 1275956 2156105 := bstep (se 2 (by rfl) ⟨808539, by rfl⟩ : syracuseStep 2156105 = 1617079) B1617079
theorem B9692783 : Blo 1275956 9692783 := bstep (se 1 (by rfl) ⟨7269587, by rfl⟩ : syracuseStep 9692783 = 14539175) B14539175
theorem B2074591 : Blo 1275956 2074591 := bstep (se 1 (by rfl) ⟨1555943, by rfl⟩ : syracuseStep 2074591 = 3111887) B3111887
theorem B1435675 : Blo 1275956 1435675 := bstep (se 1 (by rfl) ⟨1076756, by rfl⟩ : syracuseStep 1435675 = 2153513) B2153513
theorem B3450907 : Blo 1275956 3450907 := bstep (se 1 (by rfl) ⟨2588180, by rfl⟩ : syracuseStep 3450907 = 5176361) B5176361
theorem B170362925 : Blo 1275956 170362925 := bstep (se 3 (by rfl) ⟨31943048, by rfl⟩ : syracuseStep 170362925 = 63886097) B63886097
theorem B4089953 : Blo 1275956 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B14534801 : Blo 1275956 14534801 := bstep (se 2 (by rfl) ⟨5450550, by rfl⟩ : syracuseStep 14534801 = 10901101) B10901101
theorem B10635419 : Blo 1275956 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B3229895 : Blo 1275956 3229895 := bstep (se 1 (by rfl) ⟨2422421, by rfl⟩ : syracuseStep 3229895 = 4844843) B4844843
theorem B2910601 : Blo 1275956 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B10914223 : Blo 1275956 10914223 := bstep (se 1 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 10914223 = 16371335) B16371335
theorem B1616431 : Blo 1275956 1616431 := bstep (se 1 (by rfl) ⟨1212323, by rfl⟩ : syracuseStep 1616431 = 2424647) B2424647
theorem B8735303 : Blo 1275956 8735303 := bstep (se 1 (by rfl) ⟨6551477, by rfl⟩ : syracuseStep 8735303 = 13102955) B13102955
theorem B4311899 : Blo 1275956 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B7277471 : Blo 1275956 7277471 := bstep (se 1 (by rfl) ⟨5458103, by rfl⟩ : syracuseStep 7277471 = 10916207) B10916207
theorem B1362911 : Blo 1275956 1362911 := bstep (se 1 (by rfl) ⟨1022183, by rfl⟩ : syracuseStep 1362911 = 2044367) B2044367
theorem B3451945 : Blo 1275956 3451945 := bstep (se 2 (by rfl) ⟨1294479, by rfl⟩ : syracuseStep 3451945 = 2588959) B2588959
theorem B1437151 : Blo 1275956 1437151 := bstep (se 1 (by rfl) ⟨1077863, by rfl⟩ : syracuseStep 1437151 = 2155727) B2155727
theorem B5451371 : Blo 1275956 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B9834119 : Blo 1275956 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B5451407 : Blo 1275956 5451407 := bstep (se 1 (by rfl) ⟨4088555, by rfl⟩ : syracuseStep 5451407 = 8177111) B8177111
theorem B143699683 : Blo 1275956 143699683 := bstep (se 1 (by rfl) ⟨107774762, by rfl⟩ : syracuseStep 143699683 = 215549525) B215549525
theorem B8179517 : Blo 1275956 8179517 := bstep (se 3 (by rfl) ⟨1533659, by rfl⟩ : syracuseStep 8179517 = 3067319) B3067319
theorem B1437691 : Blo 1275956 1437691 := bstep (se 1 (by rfl) ⟨1078268, by rfl⟩ : syracuseStep 1437691 = 2156537) B2156537
theorem B14749739 : Blo 1275956 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B9703475 : Blo 1275956 9703475 := bstep (se 1 (by rfl) ⟨7277606, by rfl⟩ : syracuseStep 9703475 = 14555213) B14555213
theorem B2871359 : Blo 1275956 2871359 := bstep (se 1 (by rfl) ⟨2153519, by rfl⟩ : syracuseStep 2871359 = 4307039) B4307039
theorem B3231839 : Blo 1275956 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B12275813 : Blo 1275956 12275813 := bstep (se 4 (by rfl) ⟨1150857, by rfl⟩ : syracuseStep 12275813 = 2301715) B2301715
theorem B2871593 : Blo 1275956 2871593 := bstep (se 2 (by rfl) ⟨1076847, by rfl⟩ : syracuseStep 2871593 = 2153695) B2153695
theorem B2871863 : Blo 1275956 2871863 := bstep (se 1 (by rfl) ⟨2153897, by rfl⟩ : syracuseStep 2871863 = 4307795) B4307795
theorem B4846331 : Blo 1275956 4846331 := bstep (se 1 (by rfl) ⟨3634748, by rfl⟩ : syracuseStep 4846331 = 7269497) B7269497
theorem B3633929 : Blo 1275956 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B11809561 : Blo 1275956 11809561 := bstep (se 2 (by rfl) ⟨4428585, by rfl⟩ : syracuseStep 11809561 = 8857171) B8857171
theorem B2872169 : Blo 1275956 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B2872223 : Blo 1275956 2872223 := bstep (se 1 (by rfl) ⟨2154167, by rfl⟩ : syracuseStep 2872223 = 4308335) B4308335
theorem B9696185 : Blo 1275956 9696185 := bstep (se 2 (by rfl) ⟨3636069, by rfl⟩ : syracuseStep 9696185 = 7272139) B7272139
theorem B3683369 : Blo 1275956 3683369 := bstep (se 2 (by rfl) ⟨1381263, by rfl⟩ : syracuseStep 3683369 = 2762527) B2762527
theorem B5452859 : Blo 1275956 5452859 := bstep (se 1 (by rfl) ⟨4089644, by rfl⟩ : syracuseStep 5452859 = 8179289) B8179289
theorem B319009861 : Blo 1275956 319009861 := bstep (se 4 (by rfl) ⟨29907174, by rfl⟩ : syracuseStep 319009861 = 59814349) B59814349
theorem B2872475 : Blo 1275956 2872475 := bstep (se 1 (by rfl) ⟨2154356, by rfl⟩ : syracuseStep 2872475 = 4308713) B4308713
theorem B1914107 : Blo 1275956 1914107 := bstep (se 1 (by rfl) ⟨1435580, by rfl⟩ : syracuseStep 1914107 = 2871161) B2871161
theorem B62100755 : Blo 1275956 62100755 := bstep (se 1 (by rfl) ⟨46575566, by rfl⟩ : syracuseStep 62100755 = 93151133) B93151133
theorem B1381871 : Blo 1275956 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B2873051 : Blo 1275956 2873051 := bstep (se 1 (by rfl) ⟨2154788, by rfl⟩ : syracuseStep 2873051 = 4309577) B4309577
theorem B4093757 : Blo 1275956 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B10360639 : Blo 1275956 10360639 := bstep (se 1 (by rfl) ⟨7770479, by rfl⟩ : syracuseStep 10360639 = 15540959) B15540959
theorem B2873159 : Blo 1275956 2873159 := bstep (se 1 (by rfl) ⟨2154869, by rfl⟩ : syracuseStep 2873159 = 4309739) B4309739
theorem B8730625 : Blo 1275956 8730625 := bstep (se 2 (by rfl) ⟨3273984, by rfl⟩ : syracuseStep 8730625 = 6547969) B6547969
theorem B4306985 : Blo 1275956 4306985 := bstep (se 2 (by rfl) ⟨1615119, by rfl⟩ : syracuseStep 4306985 = 3230239) B3230239
theorem B1275975 : Blo 1275956 1275975 := bstep (se 1 (by rfl) ⟨956981, by rfl⟩ : syracuseStep 1275975 = 1913963) B1913963
theorem B12269663 : Blo 1275956 12269663 := bstep (se 1 (by rfl) ⟨9202247, by rfl⟩ : syracuseStep 12269663 = 18404495) B18404495
theorem B1816759 : Blo 1275956 1816759 := bstep (se 1 (by rfl) ⟨1362569, by rfl⟩ : syracuseStep 1816759 = 2725139) B2725139
theorem B1276135 : Blo 1275956 1276135 := bstep (se 1 (by rfl) ⟨957101, by rfl⟩ : syracuseStep 1276135 = 1914203) B1914203
theorem B3881191 : Blo 1275956 3881191 := bstep (se 1 (by rfl) ⟨2910893, by rfl⟩ : syracuseStep 3881191 = 5821787) B5821787
theorem B1276319 : Blo 1275956 1276319 := bstep (se 1 (by rfl) ⟨957239, by rfl⟩ : syracuseStep 1276319 = 1914479) B1914479
theorem B2587079 : Blo 1275956 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B1276367 : Blo 1275956 1276367 := bstep (se 1 (by rfl) ⟨957275, by rfl⟩ : syracuseStep 1276367 = 1914551) B1914551
theorem B1915343 : Blo 1275956 1915343 := bstep (se 1 (by rfl) ⟨1436507, by rfl⟩ : syracuseStep 1915343 = 2873015) B2873015
theorem B1276391 : Blo 1275956 1276391 := bstep (se 1 (by rfl) ⟨957293, by rfl⟩ : syracuseStep 1276391 = 1914587) B1914587
theorem B1915433 : Blo 1275956 1915433 := bstep (se 2 (by rfl) ⟨718287, by rfl⟩ : syracuseStep 1915433 = 1436575) B1436575
theorem B1276507 : Blo 1275956 1276507 := bstep (se 1 (by rfl) ⟨957380, by rfl⟩ : syracuseStep 1276507 = 1914761) B1914761
theorem B1276575 : Blo 1275956 1276575 := bstep (se 1 (by rfl) ⟨957431, by rfl⟩ : syracuseStep 1276575 = 1914863) B1914863
theorem B1915625 : Blo 1275956 1915625 := bstep (se 2 (by rfl) ⟨718359, by rfl⟩ : syracuseStep 1915625 = 1436719) B1436719
theorem B6134525 : Blo 1275956 6134525 := bstep (se 3 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 6134525 = 2300447) B2300447
theorem B2726711 : Blo 1275956 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B2874167 : Blo 1275956 2874167 := bstep (se 1 (by rfl) ⟨2155625, by rfl⟩ : syracuseStep 2874167 = 4311251) B4311251
theorem B1276743 : Blo 1275956 1276743 := bstep (se 1 (by rfl) ⟨957557, by rfl⟩ : syracuseStep 1276743 = 1915115) B1915115
theorem B1276783 : Blo 1275956 1276783 := bstep (se 1 (by rfl) ⟨957587, by rfl⟩ : syracuseStep 1276783 = 1915175) B1915175
theorem B2726779 : Blo 1275956 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B139901843 : Blo 1275956 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B1276839 : Blo 1275956 1276839 := bstep (se 1 (by rfl) ⟨957629, by rfl⟩ : syracuseStep 1276839 = 1915259) B1915259
theorem B5454823 : Blo 1275956 5454823 := bstep (se 1 (by rfl) ⟨4091117, by rfl⟩ : syracuseStep 5454823 = 8182235) B8182235
theorem B2874347 : Blo 1275956 2874347 := bstep (se 1 (by rfl) ⟨2155760, by rfl⟩ : syracuseStep 2874347 = 4311521) B4311521
theorem B1277019 : Blo 1275956 1277019 := bstep (se 1 (by rfl) ⟨957764, by rfl⟩ : syracuseStep 1277019 = 1915529) B1915529
theorem B1916009 : Blo 1275956 1916009 := bstep (se 2 (by rfl) ⟨718503, by rfl⟩ : syracuseStep 1916009 = 1437007) B1437007
theorem B1277135 : Blo 1275956 1277135 := bstep (se 1 (by rfl) ⟨957851, by rfl⟩ : syracuseStep 1277135 = 1915703) B1915703
theorem B1277159 : Blo 1275956 1277159 := bstep (se 1 (by rfl) ⟨957869, by rfl⟩ : syracuseStep 1277159 = 1915739) B1915739
theorem B1916135 : Blo 1275956 1916135 := bstep (se 1 (by rfl) ⟨1437101, by rfl⟩ : syracuseStep 1916135 = 2874203) B2874203
theorem B1277255 : Blo 1275956 1277255 := bstep (se 1 (by rfl) ⟨957941, by rfl⟩ : syracuseStep 1277255 = 1915883) B1915883
theorem B8183207 : Blo 1275956 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B1277391 : Blo 1275956 1277391 := bstep (se 1 (by rfl) ⟨958043, by rfl⟩ : syracuseStep 1277391 = 1916087) B1916087
theorem B3636731 : Blo 1275956 3636731 := bstep (se 1 (by rfl) ⟨2727548, by rfl⟩ : syracuseStep 3636731 = 5455097) B5455097
theorem B1277551 : Blo 1275956 1277551 := bstep (se 1 (by rfl) ⟨958163, by rfl⟩ : syracuseStep 1277551 = 1916327) B1916327
theorem B3497597 : Blo 1275956 3497597 := bstep (se 3 (by rfl) ⟨655799, by rfl⟩ : syracuseStep 3497597 = 1311599) B1311599
theorem B1277607 : Blo 1275956 1277607 := bstep (se 1 (by rfl) ⟨958205, by rfl⟩ : syracuseStep 1277607 = 1916411) B1916411
theorem B1916639 : Blo 1275956 1916639 := bstep (se 1 (by rfl) ⟨1437479, by rfl⟩ : syracuseStep 1916639 = 2874959) B2874959
theorem B1277671 : Blo 1275956 1277671 := bstep (se 1 (by rfl) ⟨958253, by rfl⟩ : syracuseStep 1277671 = 1916507) B1916507
theorem B1916681 : Blo 1275956 1916681 := bstep (se 2 (by rfl) ⟨718755, by rfl⟩ : syracuseStep 1916681 = 1437511) B1437511
theorem B9699101 : Blo 1275956 9699101 := bstep (se 3 (by rfl) ⟨1818581, by rfl⟩ : syracuseStep 9699101 = 3637163) B3637163
theorem B1277727 : Blo 1275956 1277727 := bstep (se 1 (by rfl) ⟨958295, by rfl⟩ : syracuseStep 1277727 = 1916591) B1916591
theorem B31489829 : Blo 1275956 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B1277807 : Blo 1275956 1277807 := bstep (se 1 (by rfl) ⟨958355, by rfl⟩ : syracuseStep 1277807 = 1916711) B1916711
theorem B2875247 : Blo 1275956 2875247 := bstep (se 1 (by rfl) ⟨2156435, by rfl⟩ : syracuseStep 2875247 = 4312871) B4312871
theorem B1277863 : Blo 1275956 1277863 := bstep (se 1 (by rfl) ⟨958397, by rfl⟩ : syracuseStep 1277863 = 1916795) B1916795
theorem B11640833 : Blo 1275956 11640833 := bstep (se 2 (by rfl) ⟨4365312, by rfl⟩ : syracuseStep 11640833 = 8730625) B8730625
theorem B2154559 : Blo 1275956 2154559 := bstep (se 1 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 2154559 = 3231839) B3231839
theorem B8183875 : Blo 1275956 8183875 := bstep (se 1 (by rfl) ⟨6137906, by rfl⟩ : syracuseStep 8183875 = 12275813) B12275813
theorem B9822317 : Blo 1275956 9822317 := bstep (se 3 (by rfl) ⟨1841684, by rfl⟩ : syracuseStep 9822317 = 3683369) B3683369
theorem B4309199 : Blo 1275956 4309199 := bstep (se 1 (by rfl) ⟨3231899, by rfl⟩ : syracuseStep 4309199 = 6463799) B6463799
theorem B28361117 : Blo 1275956 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B6464123 : Blo 1275956 6464123 := bstep (se 1 (by rfl) ⟨4848092, by rfl⟩ : syracuseStep 6464123 = 9696185) B9696185
theorem B2155241 : Blo 1275956 2155241 := bstep (se 2 (by rfl) ⟨808215, by rfl⟩ : syracuseStep 2155241 = 1616431) B1616431
theorem B10912583 : Blo 1275956 10912583 := bstep (se 1 (by rfl) ⟨8184437, by rfl⟩ : syracuseStep 10912583 = 16368875) B16368875
theorem B4604843 : Blo 1275956 4604843 := bstep (se 1 (by rfl) ⟨3453632, by rfl⟩ : syracuseStep 4604843 = 6907265) B6907265
theorem B6554621 : Blo 1275956 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B15746081 : Blo 1275956 15746081 := bstep (se 2 (by rfl) ⟨5904780, by rfl⟩ : syracuseStep 15746081 = 11809561) B11809561
theorem B2589737 : Blo 1275956 2589737 := bstep (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) B1942303
theorem B6898877 : Blo 1275956 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B2729171 : Blo 1275956 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B113575283 : Blo 1275956 113575283 := bstep (se 1 (by rfl) ⟨85181462, by rfl⟩ : syracuseStep 113575283 = 170362925) B170362925
theorem B425346481 : Blo 1275956 425346481 := bstep (se 2 (by rfl) ⟨159504930, by rfl⟩ : syracuseStep 425346481 = 319009861) B319009861
theorem B7472969 : Blo 1275956 7472969 := bstep (se 2 (by rfl) ⟨2802363, by rfl⟩ : syracuseStep 7472969 = 5604727) B5604727
theorem B4089683 : Blo 1275956 4089683 := bstep (se 1 (by rfl) ⟨3067262, by rfl⟩ : syracuseStep 4089683 = 6134525) B6134525
theorem B4851647 : Blo 1275956 4851647 := bstep (se 1 (by rfl) ⟨3638735, by rfl⟩ : syracuseStep 4851647 = 7277471) B7277471
theorem B27592649 : Blo 1275956 27592649 := bstep (se 2 (by rfl) ⟨10347243, by rfl⟩ : syracuseStep 27592649 = 20694487) B20694487
theorem B13814185 : Blo 1275956 13814185 := bstep (se 2 (by rfl) ⟨5180319, by rfl⟩ : syracuseStep 13814185 = 10360639) B10360639
theorem B6556079 : Blo 1275956 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B6466067 : Blo 1275956 6466067 := bstep (se 1 (by rfl) ⟨4849550, by rfl⟩ : syracuseStep 6466067 = 9699101) B9699101
theorem B9833159 : Blo 1275956 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B1436539 : Blo 1275956 1436539 := bstep (se 1 (by rfl) ⟨1077404, by rfl⟩ : syracuseStep 1436539 = 2154809) B2154809
theorem B3230887 : Blo 1275956 3230887 := bstep (se 1 (by rfl) ⟨2423165, by rfl⟩ : syracuseStep 3230887 = 4846331) B4846331
theorem B1436863 : Blo 1275956 1436863 := bstep (se 1 (by rfl) ⟨1077647, by rfl⟩ : syracuseStep 1436863 = 2155295) B2155295
theorem B55225577 : Blo 1275956 55225577 := bstep (se 2 (by rfl) ⟨20709591, by rfl⟩ : syracuseStep 55225577 = 41419183) B41419183
theorem B14552297 : Blo 1275956 14552297 := bstep (se 2 (by rfl) ⟨5457111, by rfl⟩ : syracuseStep 14552297 = 10914223) B10914223
theorem B4091399 : Blo 1275956 4091399 := bstep (se 1 (by rfl) ⟨3068549, by rfl⟩ : syracuseStep 4091399 = 6137099) B6137099
theorem B6139559 : Blo 1275956 6139559 := bstep (se 1 (by rfl) ⟨4604669, by rfl⟩ : syracuseStep 6139559 = 9209339) B9209339
theorem B1437403 : Blo 1275956 1437403 := bstep (se 1 (by rfl) ⟨1078052, by rfl⟩ : syracuseStep 1437403 = 2156105) B2156105
theorem B15535901 : Blo 1275956 15535901 := bstep (se 3 (by rfl) ⟨2912981, by rfl⟩ : syracuseStep 15535901 = 5825963) B5825963
theorem B2871323 : Blo 1275956 2871323 := bstep (se 1 (by rfl) ⟨2153492, by rfl⟩ : syracuseStep 2871323 = 4306985) B4306985
theorem B8179775 : Blo 1275956 8179775 := bstep (se 1 (by rfl) ⟨6134831, by rfl⟩ : syracuseStep 8179775 = 12269663) B12269663
theorem B23294141 : Blo 1275956 23294141 := bstep (se 3 (by rfl) ⟨4367651, by rfl⟩ : syracuseStep 23294141 = 8735303) B8735303
theorem B191599577 : Blo 1275956 191599577 := bstep (se 2 (by rfl) ⟨71849841, by rfl⟩ : syracuseStep 191599577 = 143699683) B143699683
theorem B14537717 : Blo 1275956 14537717 := bstep (se 5 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 14537717 = 1362911) B1362911
theorem B3634247 : Blo 1275956 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B2331731 : Blo 1275956 2331731 := bstep (se 1 (by rfl) ⟨1748798, by rfl⟩ : syracuseStep 2331731 = 3497597) B3497597
theorem B3634271 : Blo 1275956 3634271 := bstep (se 1 (by rfl) ⟨2725703, by rfl⟩ : syracuseStep 3634271 = 5451407) B5451407
theorem B11064485 : Blo 1275956 11064485 := bstep (se 4 (by rfl) ⟨1037295, by rfl⟩ : syracuseStep 11064485 = 2074591) B2074591
theorem B20993219 : Blo 1275956 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B5453011 : Blo 1275956 5453011 := bstep (se 1 (by rfl) ⟨4089758, by rfl⟩ : syracuseStep 5453011 = 8179517) B8179517
theorem B6468983 : Blo 1275956 6468983 := bstep (se 1 (by rfl) ⟨4851737, by rfl⟩ : syracuseStep 6468983 = 9703475) B9703475
theorem B1914233 : Blo 1275956 1914233 := bstep (se 2 (by rfl) ⟨717837, by rfl⟩ : syracuseStep 1914233 = 1435675) B1435675
theorem B4601209 : Blo 1275956 4601209 := bstep (se 2 (by rfl) ⟨1725453, by rfl⟩ : syracuseStep 4601209 = 3450907) B3450907
theorem B1914239 : Blo 1275956 1914239 := bstep (se 1 (by rfl) ⟨1435679, by rfl⟩ : syracuseStep 1914239 = 2871359) B2871359
theorem B8295895 : Blo 1275956 8295895 := bstep (se 1 (by rfl) ⟨6221921, by rfl⟩ : syracuseStep 8295895 = 12443843) B12443843
theorem B1914395 : Blo 1275956 1914395 := bstep (se 1 (by rfl) ⟨1435796, by rfl⟩ : syracuseStep 1914395 = 2871593) B2871593
theorem B5174921 : Blo 1275956 5174921 := bstep (se 2 (by rfl) ⟨1940595, by rfl⟩ : syracuseStep 5174921 = 3881191) B3881191
theorem B1914575 : Blo 1275956 1914575 := bstep (se 1 (by rfl) ⟨1435931, by rfl⟩ : syracuseStep 1914575 = 2871863) B2871863
theorem B2422619 : Blo 1275956 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B3880801 : Blo 1275956 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B1914779 : Blo 1275956 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B1914815 : Blo 1275956 1914815 := bstep (se 1 (by rfl) ⟨1436111, by rfl⟩ : syracuseStep 1914815 = 2872223) B2872223
theorem B3635239 : Blo 1275956 3635239 := bstep (se 1 (by rfl) ⟨2726429, by rfl⟩ : syracuseStep 3635239 = 5452859) B5452859
theorem B1914983 : Blo 1275956 1914983 := bstep (se 1 (by rfl) ⟨1436237, by rfl⟩ : syracuseStep 1914983 = 2872475) B2872475
theorem B1276071 : Blo 1275956 1276071 := bstep (se 1 (by rfl) ⟨957053, by rfl⟩ : syracuseStep 1276071 = 1914107) B1914107
theorem B41400503 : Blo 1275956 41400503 := bstep (se 1 (by rfl) ⟨31050377, by rfl⟩ : syracuseStep 41400503 = 62100755) B62100755
theorem B2873627 : Blo 1275956 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B9689381 : Blo 1275956 9689381 := bstep (se 4 (by rfl) ⟨908379, by rfl⟩ : syracuseStep 9689381 = 1816759) B1816759
theorem B6461855 : Blo 1275956 6461855 := bstep (se 1 (by rfl) ⟨4846391, by rfl⟩ : syracuseStep 6461855 = 9692783) B9692783
theorem B21821885 : Blo 1275956 21821885 := bstep (se 3 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 21821885 = 8183207) B8183207
theorem B1915367 : Blo 1275956 1915367 := bstep (se 1 (by rfl) ⟨1436525, by rfl⟩ : syracuseStep 1915367 = 2873051) B2873051
theorem B3635705 : Blo 1275956 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B1915439 : Blo 1275956 1915439 := bstep (se 1 (by rfl) ⟨1436579, by rfl⟩ : syracuseStep 1915439 = 2873159) B2873159
theorem B3684989 : Blo 1275956 3684989 := bstep (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) B1381871
theorem B7273097 : Blo 1275956 7273097 := bstep (se 2 (by rfl) ⟨2727411, by rfl⟩ : syracuseStep 7273097 = 5454823) B5454823
theorem B4602593 : Blo 1275956 4602593 := bstep (se 2 (by rfl) ⟨1725972, by rfl⟩ : syracuseStep 4602593 = 3451945) B3451945
theorem B2726635 : Blo 1275956 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B9689867 : Blo 1275956 9689867 := bstep (se 1 (by rfl) ⟨7267400, by rfl⟩ : syracuseStep 9689867 = 14534801) B14534801
theorem B2153263 : Blo 1275956 2153263 := bstep (se 1 (by rfl) ⟨1614947, by rfl⟩ : syracuseStep 2153263 = 3229895) B3229895
theorem B1276895 : Blo 1275956 1276895 := bstep (se 1 (by rfl) ⟨957671, by rfl⟩ : syracuseStep 1276895 = 1915343) B1915343
theorem B1276955 : Blo 1275956 1276955 := bstep (se 1 (by rfl) ⟨957716, by rfl⟩ : syracuseStep 1276955 = 1915433) B1915433
theorem B1277083 : Blo 1275956 1277083 := bstep (se 1 (by rfl) ⟨957812, by rfl⟩ : syracuseStep 1277083 = 1915625) B1915625
theorem B1817807 : Blo 1275956 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B1916111 : Blo 1275956 1916111 := bstep (se 1 (by rfl) ⟨1437083, by rfl⟩ : syracuseStep 1916111 = 2874167) B2874167
theorem B2874599 : Blo 1275956 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B1916201 : Blo 1275956 1916201 := bstep (se 2 (by rfl) ⟨718575, by rfl⟩ : syracuseStep 1916201 = 1437151) B1437151
theorem B1916231 : Blo 1275956 1916231 := bstep (se 1 (by rfl) ⟨1437173, by rfl⟩ : syracuseStep 1916231 = 2874347) B2874347
theorem B1277339 : Blo 1275956 1277339 := bstep (se 1 (by rfl) ⟨958004, by rfl⟩ : syracuseStep 1277339 = 1916009) B1916009
theorem B1277423 : Blo 1275956 1277423 := bstep (se 1 (by rfl) ⟨958067, by rfl⟩ : syracuseStep 1277423 = 1916135) B1916135
theorem B2424487 : Blo 1275956 2424487 := bstep (se 1 (by rfl) ⟨1818365, by rfl⟩ : syracuseStep 2424487 = 3636731) B3636731
theorem B373071581 : Blo 1275956 373071581 := bstep (se 3 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 373071581 = 139901843) B139901843
theorem B1277759 : Blo 1275956 1277759 := bstep (se 1 (by rfl) ⟨958319, by rfl⟩ : syracuseStep 1277759 = 1916639) B1916639
theorem B1277787 : Blo 1275956 1277787 := bstep (se 1 (by rfl) ⟨958340, by rfl⟩ : syracuseStep 1277787 = 1916681) B1916681
theorem B1916831 : Blo 1275956 1916831 := bstep (se 1 (by rfl) ⟨1437623, by rfl⟩ : syracuseStep 1916831 = 2875247) B2875247
theorem B1916921 : Blo 1275956 1916921 := bstep (se 2 (by rfl) ⟨718845, by rfl⟩ : syracuseStep 1916921 = 1437691) B1437691
theorem B10911833 : Blo 1275956 10911833 := bstep (se 2 (by rfl) ⟨4091937, by rfl⟩ : syracuseStep 10911833 = 8183875) B8183875
theorem B9691325 : Blo 1275956 9691325 := bstep (se 3 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 9691325 = 3634247) B3634247
theorem B18907411 : Blo 1275956 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B4309415 : Blo 1275956 4309415 := bstep (se 1 (by rfl) ⟨3232061, by rfl⟩ : syracuseStep 4309415 = 6464123) B6464123
theorem B27623861 : Blo 1275956 27623861 := bstep (se 5 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 27623861 = 2589737) B2589737
theorem B7275055 : Blo 1275956 7275055 := bstep (se 1 (by rfl) ⟨5456291, by rfl⟩ : syracuseStep 7275055 = 10912583) B10912583
theorem B9691811 : Blo 1275956 9691811 := bstep (se 1 (by rfl) ⟨7268858, by rfl⟩ : syracuseStep 9691811 = 14537717) B14537717
theorem B3449947 : Blo 1275956 3449947 := bstep (se 1 (by rfl) ⟨2587460, by rfl⟩ : syracuseStep 3449947 = 5174921) B5174921
theorem B17482877 : Blo 1275956 17482877 := bstep (se 3 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 17482877 = 6556079) B6556079
theorem B4981979 : Blo 1275956 4981979 := bstep (se 1 (by rfl) ⟨3736484, by rfl⟩ : syracuseStep 4981979 = 7472969) B7472969
theorem B1615079 : Blo 1275956 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B27600335 : Blo 1275956 27600335 := bstep (se 1 (by rfl) ⟨20700251, by rfl⟩ : syracuseStep 27600335 = 41400503) B41400503
theorem B4310711 : Blo 1275956 4310711 := bstep (se 1 (by rfl) ⟨3233033, by rfl⟩ : syracuseStep 4310711 = 6466067) B6466067
theorem B6555439 : Blo 1275956 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B12273581 : Blo 1275956 12273581 := bstep (se 3 (by rfl) ⟨2301296, by rfl⟩ : syracuseStep 12273581 = 4602593) B4602593
theorem B11061193 : Blo 1275956 11061193 := bstep (se 2 (by rfl) ⟨4147947, by rfl⟩ : syracuseStep 11061193 = 8295895) B8295895
theorem B36817051 : Blo 1275956 36817051 := bstep (se 1 (by rfl) ⟨27612788, by rfl⟩ : syracuseStep 36817051 = 55225577) B55225577
theorem B9701531 : Blo 1275956 9701531 := bstep (se 1 (by rfl) ⟨7276148, by rfl⟩ : syracuseStep 9701531 = 14552297) B14552297
theorem B10357267 : Blo 1275956 10357267 := bstep (se 1 (by rfl) ⟨7767950, by rfl⟩ : syracuseStep 10357267 = 15535901) B15535901
theorem B7760555 : Blo 1275956 7760555 := bstep (se 1 (by rfl) ⟨5820416, by rfl⟩ : syracuseStep 7760555 = 11640833) B11640833
theorem B26192845 : Blo 1275956 26192845 := bstep (se 3 (by rfl) ⟨4911158, by rfl⟩ : syracuseStep 26192845 = 9822317) B9822317
theorem B1436827 : Blo 1275956 1436827 := bstep (se 1 (by rfl) ⟨1077620, by rfl⟩ : syracuseStep 1436827 = 2155241) B2155241
theorem B7277789 : Blo 1275956 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B18418913 : Blo 1275956 18418913 := bstep (se 2 (by rfl) ⟨6907092, by rfl⟩ : syracuseStep 18418913 = 13814185) B13814185
theorem B127733051 : Blo 1275956 127733051 := bstep (se 1 (by rfl) ⟨95799788, by rfl⟩ : syracuseStep 127733051 = 191599577) B191599577
theorem B4369747 : Blo 1275956 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B4599251 : Blo 1275956 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B13995479 : Blo 1275956 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B4312655 : Blo 1275956 4312655 := bstep (se 1 (by rfl) ⟨3234491, by rfl⟩ : syracuseStep 4312655 = 6468983) B6468983
theorem B2871017 : Blo 1275956 2871017 := bstep (se 2 (by rfl) ⟨1076631, by rfl⟩ : syracuseStep 2871017 = 2153263) B2153263
theorem B18395099 : Blo 1275956 18395099 := bstep (se 1 (by rfl) ⟨13796324, by rfl⟩ : syracuseStep 18395099 = 27592649) B27592649
theorem B9695213 : Blo 1275956 9695213 := bstep (se 3 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 9695213 = 3635705) B3635705
theorem B6459587 : Blo 1275956 6459587 := bstep (se 1 (by rfl) ⟨4844690, by rfl⟩ : syracuseStep 6459587 = 9689381) B9689381
theorem B7270681 : Blo 1275956 7270681 := bstep (se 2 (by rfl) ⟨2726505, by rfl⟩ : syracuseStep 7270681 = 5453011) B5453011
theorem B6459911 : Blo 1275956 6459911 := bstep (se 1 (by rfl) ⟨4844933, by rfl⟩ : syracuseStep 6459911 = 9689867) B9689867
theorem B567128641 : Blo 1275956 567128641 := bstep (se 2 (by rfl) ⟨212673240, by rfl⟩ : syracuseStep 567128641 = 425346481) B425346481
theorem B3232649 : Blo 1275956 3232649 := bstep (se 2 (by rfl) ⟨1212243, by rfl⟩ : syracuseStep 3232649 = 2424487) B2424487
theorem B4093039 : Blo 1275956 4093039 := bstep (se 1 (by rfl) ⟨3069779, by rfl⟩ : syracuseStep 4093039 = 6139559) B6139559
theorem B5174401 : Blo 1275956 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B248714387 : Blo 1275956 248714387 := bstep (se 1 (by rfl) ⟨186535790, by rfl⟩ : syracuseStep 248714387 = 373071581) B373071581
theorem B1914215 : Blo 1275956 1914215 := bstep (se 1 (by rfl) ⟨1435661, by rfl⟩ : syracuseStep 1914215 = 2871323) B2871323
theorem B5453183 : Blo 1275956 5453183 := bstep (se 1 (by rfl) ⟨4089887, by rfl⟩ : syracuseStep 5453183 = 8179775) B8179775
theorem B4846985 : Blo 1275956 4846985 := bstep (se 2 (by rfl) ⟨1817619, by rfl⟩ : syracuseStep 4846985 = 3635239) B3635239
theorem B2872745 : Blo 1275956 2872745 := bstep (se 2 (by rfl) ⟨1077279, by rfl⟩ : syracuseStep 2872745 = 2154559) B2154559
theorem B15529427 : Blo 1275956 15529427 := bstep (se 1 (by rfl) ⟨11647070, by rfl⟩ : syracuseStep 15529427 = 23294141) B23294141
theorem B2872799 : Blo 1275956 2872799 := bstep (se 1 (by rfl) ⟨2154599, by rfl⟩ : syracuseStep 2872799 = 4309199) B4309199
theorem B167958197 : Blo 1275956 167958197 := bstep (se 5 (by rfl) ⟨7873040, by rfl⟩ : syracuseStep 167958197 = 15746081) B15746081
theorem B29505293 : Blo 1275956 29505293 := bstep (se 3 (by rfl) ⟨5532242, by rfl⟩ : syracuseStep 29505293 = 11064485) B11064485
theorem B4847485 : Blo 1275956 4847485 := bstep (se 3 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 4847485 = 1817807) B1817807
theorem B3069895 : Blo 1275956 3069895 := bstep (se 1 (by rfl) ⟨2302421, by rfl⟩ : syracuseStep 3069895 = 4604843) B4604843
theorem B1554487 : Blo 1275956 1554487 := bstep (se 1 (by rfl) ⟨1165865, by rfl⟩ : syracuseStep 1554487 = 2331731) B2331731
theorem B2422847 : Blo 1275956 2422847 := bstep (se 1 (by rfl) ⟨1817135, by rfl⟩ : syracuseStep 2422847 = 3634271) B3634271
theorem B75716855 : Blo 1275956 75716855 := bstep (se 1 (by rfl) ⟨56787641, by rfl⟩ : syracuseStep 75716855 = 113575283) B113575283
theorem B1276155 : Blo 1275956 1276155 := bstep (se 1 (by rfl) ⟨957116, by rfl⟩ : syracuseStep 1276155 = 1914233) B1914233
theorem B1276159 : Blo 1275956 1276159 := bstep (se 1 (by rfl) ⟨957119, by rfl⟩ : syracuseStep 1276159 = 1914239) B1914239
theorem B3635513 : Blo 1275956 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B1276263 : Blo 1275956 1276263 := bstep (se 1 (by rfl) ⟨957197, by rfl⟩ : syracuseStep 1276263 = 1914395) B1914395
theorem B1276383 : Blo 1275956 1276383 := bstep (se 1 (by rfl) ⟨957287, by rfl⟩ : syracuseStep 1276383 = 1914575) B1914575
theorem B1915385 : Blo 1275956 1915385 := bstep (se 2 (by rfl) ⟨718269, by rfl⟩ : syracuseStep 1915385 = 1436539) B1436539
theorem B2726455 : Blo 1275956 2726455 := bstep (se 1 (by rfl) ⟨2044841, by rfl⟩ : syracuseStep 2726455 = 4089683) B4089683
theorem B1276519 : Blo 1275956 1276519 := bstep (se 1 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 1276519 = 1914779) B1914779
theorem B1276543 : Blo 1275956 1276543 := bstep (se 1 (by rfl) ⟨957407, by rfl⟩ : syracuseStep 1276543 = 1914815) B1914815
theorem B3234431 : Blo 1275956 3234431 := bstep (se 1 (by rfl) ⟨2425823, by rfl⟩ : syracuseStep 3234431 = 4851647) B4851647
theorem B1276655 : Blo 1275956 1276655 := bstep (se 1 (by rfl) ⟨957491, by rfl⟩ : syracuseStep 1276655 = 1914983) B1914983
theorem B1915751 : Blo 1275956 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B4307849 : Blo 1275956 4307849 := bstep (se 2 (by rfl) ⟨1615443, by rfl⟩ : syracuseStep 4307849 = 3230887) B3230887
theorem B1915817 : Blo 1275956 1915817 := bstep (se 2 (by rfl) ⟨718431, by rfl⟩ : syracuseStep 1915817 = 1436863) B1436863
theorem B4307903 : Blo 1275956 4307903 := bstep (se 1 (by rfl) ⟨3230927, by rfl⟩ : syracuseStep 4307903 = 6461855) B6461855
theorem B14547923 : Blo 1275956 14547923 := bstep (se 1 (by rfl) ⟨10910942, by rfl⟩ : syracuseStep 14547923 = 21821885) B21821885
theorem B1276911 : Blo 1275956 1276911 := bstep (se 1 (by rfl) ⟨957683, by rfl⟩ : syracuseStep 1276911 = 1915367) B1915367
theorem B1276959 : Blo 1275956 1276959 := bstep (se 1 (by rfl) ⟨957719, by rfl⟩ : syracuseStep 1276959 = 1915439) B1915439
theorem B2456659 : Blo 1275956 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B4848731 : Blo 1275956 4848731 := bstep (se 1 (by rfl) ⟨3636548, by rfl⟩ : syracuseStep 4848731 = 7273097) B7273097
theorem B6134945 : Blo 1275956 6134945 := bstep (se 2 (by rfl) ⟨2300604, by rfl⟩ : syracuseStep 6134945 = 4601209) B4601209
theorem B1277407 : Blo 1275956 1277407 := bstep (se 1 (by rfl) ⟨958055, by rfl⟩ : syracuseStep 1277407 = 1916111) B1916111
theorem B1916399 : Blo 1275956 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B1277467 : Blo 1275956 1277467 := bstep (se 1 (by rfl) ⟨958100, by rfl⟩ : syracuseStep 1277467 = 1916201) B1916201
theorem B1277487 : Blo 1275956 1277487 := bstep (se 1 (by rfl) ⟨958115, by rfl⟩ : syracuseStep 1277487 = 1916231) B1916231
theorem B1916537 : Blo 1275956 1916537 := bstep (se 2 (by rfl) ⟨718701, by rfl⟩ : syracuseStep 1916537 = 1437403) B1437403
theorem B2727599 : Blo 1275956 2727599 := bstep (se 1 (by rfl) ⟨2045699, by rfl⟩ : syracuseStep 2727599 = 4091399) B4091399
theorem B1277887 : Blo 1275956 1277887 := bstep (se 1 (by rfl) ⟨958415, by rfl⟩ : syracuseStep 1277887 = 1916831) B1916831
theorem B1277947 : Blo 1275956 1277947 := bstep (se 1 (by rfl) ⟨958460, by rfl⟩ : syracuseStep 1277947 = 1916921) B1916921
theorem B7274555 : Blo 1275956 7274555 := bstep (se 1 (by rfl) ⟨5455916, by rfl⟩ : syracuseStep 7274555 = 10911833) B10911833
theorem B18415907 : Blo 1275956 18415907 := bstep (se 1 (by rfl) ⟨13811930, by rfl⟩ : syracuseStep 18415907 = 27623861) B27623861
theorem B8290597 : Blo 1275956 8290597 := bstep (se 4 (by rfl) ⟨777243, by rfl⟩ : syracuseStep 8290597 = 1554487) B1554487
theorem B16359853 : Blo 1275956 16359853 := bstep (se 3 (by rfl) ⟨3067472, by rfl⟩ : syracuseStep 16359853 = 6134945) B6134945
theorem B2155099 : Blo 1275956 2155099 := bstep (se 1 (by rfl) ⟨1616324, by rfl⟩ : syracuseStep 2155099 = 3232649) B3232649
theorem B9700073 : Blo 1275956 9700073 := bstep (se 2 (by rfl) ⟨3637527, by rfl⟩ : syracuseStep 9700073 = 7275055) B7275055
theorem B756171521 : Blo 1275956 756171521 := bstep (se 2 (by rfl) ⟨283564320, by rfl⟩ : syracuseStep 756171521 = 567128641) B567128641
theorem B18400223 : Blo 1275956 18400223 := bstep (se 1 (by rfl) ⟨13800167, by rfl⟩ : syracuseStep 18400223 = 27600335) B27600335
theorem B19670195 : Blo 1275956 19670195 := bstep (se 1 (by rfl) ⟨14752646, by rfl⟩ : syracuseStep 19670195 = 29505293) B29505293
theorem B34923793 : Blo 1275956 34923793 := bstep (se 2 (by rfl) ⟨13096422, by rfl⟩ : syracuseStep 34923793 = 26192845) B26192845
theorem B1615231 : Blo 1275956 1615231 := bstep (se 1 (by rfl) ⟨1211423, by rfl⟩ : syracuseStep 1615231 = 2422847) B2422847
theorem B5457385 : Blo 1275956 5457385 := bstep (se 2 (by rfl) ⟨2046519, by rfl⟩ : syracuseStep 5457385 = 4093039) B4093039
theorem B6899201 : Blo 1275956 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B2156287 : Blo 1275956 2156287 := bstep (se 1 (by rfl) ⟨1617215, by rfl⟩ : syracuseStep 2156287 = 3234431) B3234431
theorem B5826329 : Blo 1275956 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B4851859 : Blo 1275956 4851859 := bstep (se 1 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 4851859 = 7277789) B7277789
theorem B3066167 : Blo 1275956 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B14748257 : Blo 1275956 14748257 := bstep (se 2 (by rfl) ⟨5530596, by rfl⟩ : syracuseStep 14748257 = 11061193) B11061193
theorem B49089401 : Blo 1275956 49089401 := bstep (se 2 (by rfl) ⟨18408525, by rfl⟩ : syracuseStep 49089401 = 36817051) B36817051
theorem B25209881 : Blo 1275956 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B9694241 : Blo 1275956 9694241 := bstep (se 2 (by rfl) ⟨3635340, by rfl⟩ : syracuseStep 9694241 = 7270681) B7270681
theorem B13102181 : Blo 1275956 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B165809591 : Blo 1275956 165809591 := bstep (se 1 (by rfl) ⟨124357193, by rfl⟩ : syracuseStep 165809591 = 248714387) B248714387
theorem B3321319 : Blo 1275956 3321319 := bstep (se 1 (by rfl) ⟨2490989, by rfl⟩ : syracuseStep 3321319 = 4981979) B4981979
theorem B3231323 : Blo 1275956 3231323 := bstep (se 1 (by rfl) ⟨2423492, by rfl⟩ : syracuseStep 3231323 = 4846985) B4846985
theorem B111972131 : Blo 1275956 111972131 := bstep (se 1 (by rfl) ⟨83979098, by rfl⟩ : syracuseStep 111972131 = 167958197) B167958197
theorem B6467687 : Blo 1275956 6467687 := bstep (se 1 (by rfl) ⟨4850765, by rfl⟩ : syracuseStep 6467687 = 9701531) B9701531
theorem B4599929 : Blo 1275956 4599929 := bstep (se 2 (by rfl) ⟨1724973, by rfl⟩ : syracuseStep 4599929 = 3449947) B3449947
theorem B5173703 : Blo 1275956 5173703 := bstep (se 1 (by rfl) ⟨3880277, by rfl⟩ : syracuseStep 5173703 = 7760555) B7760555
theorem B2871899 : Blo 1275956 2871899 := bstep (se 1 (by rfl) ⟨2153924, by rfl⟩ : syracuseStep 2871899 = 4307849) B4307849
theorem B2871935 : Blo 1275956 2871935 := bstep (se 1 (by rfl) ⟨2153951, by rfl⟩ : syracuseStep 2871935 = 4307903) B4307903
theorem B3232487 : Blo 1275956 3232487 := bstep (se 1 (by rfl) ⟨2424365, by rfl⟩ : syracuseStep 3232487 = 4848731) B4848731
theorem B1914011 : Blo 1275956 1914011 := bstep (se 1 (by rfl) ⟨1435508, by rfl⟩ : syracuseStep 1914011 = 2871017) B2871017
theorem B4093193 : Blo 1275956 4093193 := bstep (se 2 (by rfl) ⟨1534947, by rfl⟩ : syracuseStep 4093193 = 3069895) B3069895
theorem B6460883 : Blo 1275956 6460883 := bstep (se 1 (by rfl) ⟨4845662, by rfl⟩ : syracuseStep 6460883 = 9691325) B9691325
theorem B4306391 : Blo 1275956 4306391 := bstep (se 1 (by rfl) ⟨3229793, by rfl⟩ : syracuseStep 4306391 = 6459587) B6459587
theorem B2872943 : Blo 1275956 2872943 := bstep (se 1 (by rfl) ⟨2154707, by rfl⟩ : syracuseStep 2872943 = 4309415) B4309415
theorem B4306607 : Blo 1275956 4306607 := bstep (se 1 (by rfl) ⟨3229955, by rfl⟩ : syracuseStep 4306607 = 6459911) B6459911
theorem B6461207 : Blo 1275956 6461207 := bstep (se 1 (by rfl) ⟨4845905, by rfl⟩ : syracuseStep 6461207 = 9691811) B9691811
theorem B4306877 : Blo 1275956 4306877 := bstep (se 3 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 4306877 = 1615079) B1615079
theorem B13809689 : Blo 1275956 13809689 := bstep (se 2 (by rfl) ⟨5178633, by rfl⟩ : syracuseStep 13809689 = 10357267) B10357267
theorem B3635273 : Blo 1275956 3635273 := bstep (se 2 (by rfl) ⟨1363227, by rfl⟩ : syracuseStep 3635273 = 2726455) B2726455
theorem B11655251 : Blo 1275956 11655251 := bstep (se 1 (by rfl) ⟨8741438, by rfl⟩ : syracuseStep 11655251 = 17482877) B17482877
theorem B340621469 : Blo 1275956 340621469 := bstep (se 3 (by rfl) ⟨63866525, by rfl⟩ : syracuseStep 340621469 = 127733051) B127733051
theorem B1276143 : Blo 1275956 1276143 := bstep (se 1 (by rfl) ⟨957107, by rfl⟩ : syracuseStep 1276143 = 1914215) B1914215
theorem B3635455 : Blo 1275956 3635455 := bstep (se 1 (by rfl) ⟨2726591, by rfl⟩ : syracuseStep 3635455 = 5453183) B5453183
theorem B1915163 : Blo 1275956 1915163 := bstep (se 1 (by rfl) ⟨1436372, by rfl⟩ : syracuseStep 1915163 = 2872745) B2872745
theorem B10352951 : Blo 1275956 10352951 := bstep (se 1 (by rfl) ⟨7764713, by rfl⟩ : syracuseStep 10352951 = 15529427) B15529427
theorem B1915199 : Blo 1275956 1915199 := bstep (se 1 (by rfl) ⟨1436399, by rfl⟩ : syracuseStep 1915199 = 2872799) B2872799
theorem B2873807 : Blo 1275956 2873807 := bstep (se 1 (by rfl) ⟨2155355, by rfl⟩ : syracuseStep 2873807 = 4310711) B4310711
theorem B8182387 : Blo 1275956 8182387 := bstep (se 1 (by rfl) ⟨6136790, by rfl⟩ : syracuseStep 8182387 = 12273581) B12273581
theorem B50477903 : Blo 1275956 50477903 := bstep (se 1 (by rfl) ⟨37858427, by rfl⟩ : syracuseStep 50477903 = 75716855) B75716855
theorem B1915769 : Blo 1275956 1915769 := bstep (se 2 (by rfl) ⟨718413, by rfl⟩ : syracuseStep 1915769 = 1436827) B1436827
theorem B2423675 : Blo 1275956 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B1276923 : Blo 1275956 1276923 := bstep (se 1 (by rfl) ⟨957692, by rfl⟩ : syracuseStep 1276923 = 1915385) B1915385
theorem B7273597 : Blo 1275956 7273597 := bstep (se 3 (by rfl) ⟨1363799, by rfl⟩ : syracuseStep 7273597 = 2727599) B2727599
theorem B1277167 : Blo 1275956 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B1277211 : Blo 1275956 1277211 := bstep (se 1 (by rfl) ⟨957908, by rfl⟩ : syracuseStep 1277211 = 1915817) B1915817
theorem B9698615 : Blo 1275956 9698615 := bstep (se 1 (by rfl) ⟨7273961, by rfl⟩ : syracuseStep 9698615 = 14547923) B14547923
theorem B12279275 : Blo 1275956 12279275 := bstep (se 1 (by rfl) ⟨9209456, by rfl⟩ : syracuseStep 12279275 = 18418913) B18418913
theorem B9330319 : Blo 1275956 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B1277599 : Blo 1275956 1277599 := bstep (se 1 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 1277599 = 1916399) B1916399
theorem B2875103 : Blo 1275956 2875103 := bstep (se 1 (by rfl) ⟨2156327, by rfl⟩ : syracuseStep 2875103 = 4312655) B4312655
theorem B8740585 : Blo 1275956 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B1277691 : Blo 1275956 1277691 := bstep (se 1 (by rfl) ⟨958268, by rfl⟩ : syracuseStep 1277691 = 1916537) B1916537
theorem B6463313 : Blo 1275956 6463313 := bstep (se 2 (by rfl) ⟨2423742, by rfl⟩ : syracuseStep 6463313 = 4847485) B4847485
theorem B12263399 : Blo 1275956 12263399 := bstep (se 1 (by rfl) ⟨9197549, by rfl⟩ : syracuseStep 12263399 = 18395099) B18395099
theorem B6463475 : Blo 1275956 6463475 := bstep (se 1 (by rfl) ⟨4847606, by rfl⟩ : syracuseStep 6463475 = 9695213) B9695213
theorem B4849703 : Blo 1275956 4849703 := bstep (se 1 (by rfl) ⟨3637277, by rfl⟩ : syracuseStep 4849703 = 7274555) B7274555
theorem B3449135 : Blo 1275956 3449135 := bstep (se 1 (by rfl) ⟨2586851, by rfl⟩ : syracuseStep 3449135 = 5173703) B5173703
theorem B2154991 : Blo 1275956 2154991 := bstep (se 1 (by rfl) ⟨1616243, by rfl⟩ : syracuseStep 2154991 = 3232487) B3232487
theorem B3884219 : Blo 1275956 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B46565057 : Blo 1275956 46565057 := bstep (se 2 (by rfl) ⟨17461896, by rfl⟩ : syracuseStep 46565057 = 34923793) B34923793
theorem B1615783 : Blo 1275956 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B7276513 : Blo 1275956 7276513 := bstep (se 2 (by rfl) ⟨2728692, by rfl⟩ : syracuseStep 7276513 = 5457385) B5457385
theorem B8734787 : Blo 1275956 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B6465743 : Blo 1275956 6465743 := bstep (se 1 (by rfl) ⟨4849307, by rfl⟩ : syracuseStep 6465743 = 9698615) B9698615
theorem B8186183 : Blo 1275956 8186183 := bstep (se 1 (by rfl) ⟨6139637, by rfl⟩ : syracuseStep 8186183 = 12279275) B12279275
theorem B74648087 : Blo 1275956 74648087 := bstep (se 1 (by rfl) ⟨55986065, by rfl⟩ : syracuseStep 74648087 = 111972131) B111972131
theorem B4311791 : Blo 1275956 4311791 := bstep (se 1 (by rfl) ⟨3233843, by rfl⟩ : syracuseStep 4311791 = 6467687) B6467687
theorem B3066619 : Blo 1275956 3066619 := bstep (se 1 (by rfl) ⟨2299964, by rfl⟩ : syracuseStep 3066619 = 4599929) B4599929
theorem B11054129 : Blo 1275956 11054129 := bstep (se 2 (by rfl) ⟨4145298, by rfl⟩ : syracuseStep 11054129 = 8290597) B8290597
theorem B6466715 : Blo 1275956 6466715 := bstep (se 1 (by rfl) ⟨4850036, by rfl⟩ : syracuseStep 6466715 = 9700073) B9700073
theorem B504114347 : Blo 1275956 504114347 := bstep (se 1 (by rfl) ⟨378085760, by rfl⟩ : syracuseStep 504114347 = 756171521) B756171521
theorem B12266815 : Blo 1275956 12266815 := bstep (se 1 (by rfl) ⟨9200111, by rfl⟩ : syracuseStep 12266815 = 18400223) B18400223
theorem B10915181 : Blo 1275956 10915181 := bstep (se 3 (by rfl) ⟨2046596, by rfl⟩ : syracuseStep 10915181 = 4093193) B4093193
theorem B49761701 : Blo 1275956 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B2870927 : Blo 1275956 2870927 := bstep (se 1 (by rfl) ⟨2153195, by rfl⟩ : syracuseStep 2870927 = 4306391) B4306391
theorem B4599467 : Blo 1275956 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B2871071 : Blo 1275956 2871071 := bstep (se 1 (by rfl) ⟨2153303, by rfl⟩ : syracuseStep 2871071 = 4306607) B4306607
theorem B2871251 : Blo 1275956 2871251 := bstep (se 1 (by rfl) ⟨2153438, by rfl⟩ : syracuseStep 2871251 = 4306877) B4306877
theorem B7770167 : Blo 1275956 7770167 := bstep (se 1 (by rfl) ⟨5827625, by rfl⟩ : syracuseStep 7770167 = 11655251) B11655251
theorem B2044111 : Blo 1275956 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B6901967 : Blo 1275956 6901967 := bstep (se 1 (by rfl) ⟨5176475, by rfl⟩ : syracuseStep 6901967 = 10352951) B10352951
theorem B4428425 : Blo 1275956 4428425 := bstep (se 2 (by rfl) ⟨1660659, by rfl⟩ : syracuseStep 4428425 = 3321319) B3321319
theorem B16806587 : Blo 1275956 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B110539727 : Blo 1275956 110539727 := bstep (se 1 (by rfl) ⟨82904795, by rfl⟩ : syracuseStep 110539727 = 165809591) B165809591
theorem B11654113 : Blo 1275956 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B12277271 : Blo 1275956 12277271 := bstep (se 1 (by rfl) ⟨9207953, by rfl⟩ : syracuseStep 12277271 = 18415907) B18415907
theorem B6469145 : Blo 1275956 6469145 := bstep (se 2 (by rfl) ⟨2425929, by rfl⟩ : syracuseStep 6469145 = 4851859) B4851859
theorem B4847273 : Blo 1275956 4847273 := bstep (se 2 (by rfl) ⟨1817727, by rfl⟩ : syracuseStep 4847273 = 3635455) B3635455
theorem B1914599 : Blo 1275956 1914599 := bstep (se 1 (by rfl) ⟨1435949, by rfl⟩ : syracuseStep 1914599 = 2871899) B2871899
theorem B1914623 : Blo 1275956 1914623 := bstep (se 1 (by rfl) ⟨1435967, by rfl⟩ : syracuseStep 1914623 = 2871935) B2871935
theorem B21813137 : Blo 1275956 21813137 := bstep (se 2 (by rfl) ⟨8179926, by rfl⟩ : syracuseStep 21813137 = 16359853) B16359853
theorem B1276007 : Blo 1275956 1276007 := bstep (se 1 (by rfl) ⟨957005, by rfl⟩ : syracuseStep 1276007 = 1914011) B1914011
theorem B13113463 : Blo 1275956 13113463 := bstep (se 1 (by rfl) ⟨9835097, by rfl⟩ : syracuseStep 13113463 = 19670195) B19670195
theorem B2873465 : Blo 1275956 2873465 := bstep (se 2 (by rfl) ⟨1077549, by rfl⟩ : syracuseStep 2873465 = 2155099) B2155099
theorem B10909849 : Blo 1275956 10909849 := bstep (se 2 (by rfl) ⟨4091193, by rfl⟩ : syracuseStep 10909849 = 8182387) B8182387
theorem B4307255 : Blo 1275956 4307255 := bstep (se 1 (by rfl) ⟨3230441, by rfl⟩ : syracuseStep 4307255 = 6460883) B6460883
theorem B1915295 : Blo 1275956 1915295 := bstep (se 1 (by rfl) ⟨1436471, by rfl⟩ : syracuseStep 1915295 = 2872943) B2872943
theorem B4307471 : Blo 1275956 4307471 := bstep (se 1 (by rfl) ⟨3230603, by rfl⟩ : syracuseStep 4307471 = 6461207) B6461207
theorem B9206459 : Blo 1275956 9206459 := bstep (se 1 (by rfl) ⟨6904844, by rfl⟩ : syracuseStep 9206459 = 13809689) B13809689
theorem B2423515 : Blo 1275956 2423515 := bstep (se 1 (by rfl) ⟨1817636, by rfl⟩ : syracuseStep 2423515 = 3635273) B3635273
theorem B227080979 : Blo 1275956 227080979 := bstep (se 1 (by rfl) ⟨170310734, by rfl⟩ : syracuseStep 227080979 = 340621469) B340621469
theorem B9698129 : Blo 1275956 9698129 := bstep (se 2 (by rfl) ⟨3636798, by rfl⟩ : syracuseStep 9698129 = 7273597) B7273597
theorem B1276775 : Blo 1275956 1276775 := bstep (se 1 (by rfl) ⟨957581, by rfl⟩ : syracuseStep 1276775 = 1915163) B1915163
theorem B1276799 : Blo 1275956 1276799 := bstep (se 1 (by rfl) ⟨957599, by rfl⟩ : syracuseStep 1276799 = 1915199) B1915199
theorem B39328685 : Blo 1275956 39328685 := bstep (se 3 (by rfl) ⟨7374128, by rfl⟩ : syracuseStep 39328685 = 14748257) B14748257
theorem B1915871 : Blo 1275956 1915871 := bstep (se 1 (by rfl) ⟨1436903, by rfl⟩ : syracuseStep 1915871 = 2873807) B2873807
theorem B2153641 : Blo 1275956 2153641 := bstep (se 2 (by rfl) ⟨807615, by rfl⟩ : syracuseStep 2153641 = 1615231) B1615231
theorem B33651935 : Blo 1275956 33651935 := bstep (se 1 (by rfl) ⟨25238951, by rfl⟩ : syracuseStep 33651935 = 50477903) B50477903
theorem B32726267 : Blo 1275956 32726267 := bstep (se 1 (by rfl) ⟨24544700, by rfl⟩ : syracuseStep 32726267 = 49089401) B49089401
theorem B1277179 : Blo 1275956 1277179 := bstep (se 1 (by rfl) ⟨957884, by rfl⟩ : syracuseStep 1277179 = 1915769) B1915769
theorem B6462827 : Blo 1275956 6462827 := bstep (se 1 (by rfl) ⟨4847120, by rfl⟩ : syracuseStep 6462827 = 9694241) B9694241
theorem B2875049 : Blo 1275956 2875049 := bstep (se 2 (by rfl) ⟨1078143, by rfl⟩ : syracuseStep 2875049 = 2156287) B2156287
theorem B2154215 : Blo 1275956 2154215 := bstep (se 1 (by rfl) ⟨1615661, by rfl⟩ : syracuseStep 2154215 = 3231323) B3231323
theorem B1916735 : Blo 1275956 1916735 := bstep (se 1 (by rfl) ⟨1437551, by rfl⟩ : syracuseStep 1916735 = 2875103) B2875103
theorem B4308875 : Blo 1275956 4308875 := bstep (se 1 (by rfl) ⟨3231656, by rfl⟩ : syracuseStep 4308875 = 6463313) B6463313
theorem B8175599 : Blo 1275956 8175599 := bstep (se 1 (by rfl) ⟨6131699, by rfl⟩ : syracuseStep 8175599 = 12263399) B12263399
theorem B4308983 : Blo 1275956 4308983 := bstep (se 1 (by rfl) ⟨3231737, by rfl⟩ : syracuseStep 4308983 = 6463475) B6463475
theorem B2589479 : Blo 1275956 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B4088825 : Blo 1275956 4088825 := bstep (se 2 (by rfl) ⟨1533309, by rfl⟩ : syracuseStep 4088825 = 3066619) B3066619
theorem B14542091 : Blo 1275956 14542091 := bstep (se 1 (by rfl) ⟨10906568, by rfl⟩ : syracuseStep 14542091 = 21813137) B21813137
theorem B4310495 : Blo 1275956 4310495 := bstep (se 1 (by rfl) ⟨3232871, by rfl⟩ : syracuseStep 4310495 = 6465743) B6465743
theorem B5457455 : Blo 1275956 5457455 := bstep (se 1 (by rfl) ⟨4093091, by rfl⟩ : syracuseStep 5457455 = 8186183) B8186183
theorem B6137639 : Blo 1275956 6137639 := bstep (se 1 (by rfl) ⟨4603229, by rfl⟩ : syracuseStep 6137639 = 9206459) B9206459
theorem B6465419 : Blo 1275956 6465419 := bstep (se 1 (by rfl) ⟨4849064, by rfl⟩ : syracuseStep 6465419 = 9698129) B9698129
theorem B4311143 : Blo 1275956 4311143 := bstep (se 1 (by rfl) ⟨3233357, by rfl⟩ : syracuseStep 4311143 = 6466715) B6466715
theorem B21817511 : Blo 1275956 21817511 := bstep (se 1 (by rfl) ⟨16363133, by rfl⟩ : syracuseStep 21817511 = 32726267) B32726267
theorem B7276787 : Blo 1275956 7276787 := bstep (se 1 (by rfl) ⟨5457590, by rfl⟩ : syracuseStep 7276787 = 10915181) B10915181
theorem B3066311 : Blo 1275956 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B1436143 : Blo 1275956 1436143 := bstep (se 1 (by rfl) ⟨1077107, by rfl⟩ : syracuseStep 1436143 = 2154215) B2154215
theorem B9702017 : Blo 1275956 9702017 := bstep (se 2 (by rfl) ⟨3638256, by rfl⟩ : syracuseStep 9702017 = 7276513) B7276513
theorem B5450399 : Blo 1275956 5450399 := bstep (se 1 (by rfl) ⟨4087799, by rfl⟩ : syracuseStep 5450399 = 8175599) B8175599
theorem B5180111 : Blo 1275956 5180111 := bstep (se 1 (by rfl) ⟨3885083, by rfl⟩ : syracuseStep 5180111 = 7770167) B7770167
theorem B29477677 : Blo 1275956 29477677 := bstep (se 3 (by rfl) ⟨5527064, by rfl⟩ : syracuseStep 29477677 = 11054129) B11054129
theorem B17484617 : Blo 1275956 17484617 := bstep (se 2 (by rfl) ⟨6556731, by rfl⟩ : syracuseStep 17484617 = 13113463) B13113463
theorem B2952283 : Blo 1275956 2952283 := bstep (se 1 (by rfl) ⟨2214212, by rfl⟩ : syracuseStep 2952283 = 4428425) B4428425
theorem B3231353 : Blo 1275956 3231353 := bstep (se 2 (by rfl) ⟨1211757, by rfl⟩ : syracuseStep 3231353 = 2423515) B2423515
theorem B4312763 : Blo 1275956 4312763 := bstep (se 1 (by rfl) ⟨3234572, by rfl⟩ : syracuseStep 4312763 = 6469145) B6469145
theorem B3231515 : Blo 1275956 3231515 := bstep (se 1 (by rfl) ⟨2423636, by rfl⟩ : syracuseStep 3231515 = 4847273) B4847273
theorem B32739389 : Blo 1275956 32739389 := bstep (se 3 (by rfl) ⟨6138635, by rfl⟩ : syracuseStep 32739389 = 12277271) B12277271
theorem B2871503 : Blo 1275956 2871503 := bstep (se 1 (by rfl) ⟨2153627, by rfl⟩ : syracuseStep 2871503 = 4307255) B4307255
theorem B2871521 : Blo 1275956 2871521 := bstep (se 2 (by rfl) ⟨1076820, by rfl⟩ : syracuseStep 2871521 = 2153641) B2153641
theorem B2871647 : Blo 1275956 2871647 := bstep (se 1 (by rfl) ⟨2153735, by rfl⟩ : syracuseStep 2871647 = 4307471) B4307471
theorem B16355753 : Blo 1275956 16355753 := bstep (se 2 (by rfl) ⟨6133407, by rfl⟩ : syracuseStep 16355753 = 12266815) B12266815
theorem B26219123 : Blo 1275956 26219123 := bstep (se 1 (by rfl) ⟨19664342, by rfl⟩ : syracuseStep 26219123 = 39328685) B39328685
theorem B22434623 : Blo 1275956 22434623 := bstep (se 1 (by rfl) ⟨16825967, by rfl⟩ : syracuseStep 22434623 = 33651935) B33651935
theorem B33174467 : Blo 1275956 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B1913951 : Blo 1275956 1913951 := bstep (se 1 (by rfl) ⟨1435463, by rfl⟩ : syracuseStep 1913951 = 2870927) B2870927
theorem B1914047 : Blo 1275956 1914047 := bstep (se 1 (by rfl) ⟨1435535, by rfl⟩ : syracuseStep 1914047 = 2871071) B2871071
theorem B2872583 : Blo 1275956 2872583 := bstep (se 1 (by rfl) ⟨2154437, by rfl⟩ : syracuseStep 2872583 = 4308875) B4308875
theorem B1914167 : Blo 1275956 1914167 := bstep (se 1 (by rfl) ⟨1435625, by rfl⟩ : syracuseStep 1914167 = 2871251) B2871251
theorem B2872655 : Blo 1275956 2872655 := bstep (se 1 (by rfl) ⟨2154491, by rfl⟩ : syracuseStep 2872655 = 4308983) B4308983
theorem B3233135 : Blo 1275956 3233135 := bstep (se 1 (by rfl) ⟨2424851, by rfl⟩ : syracuseStep 3233135 = 4849703) B4849703
theorem B2299423 : Blo 1275956 2299423 := bstep (se 1 (by rfl) ⟨1724567, by rfl⟩ : syracuseStep 2299423 = 3449135) B3449135
theorem B14546465 : Blo 1275956 14546465 := bstep (se 2 (by rfl) ⟨5454924, by rfl⟩ : syracuseStep 14546465 = 10909849) B10909849
theorem B2725481 : Blo 1275956 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B18405245 : Blo 1275956 18405245 := bstep (se 3 (by rfl) ⟨3450983, by rfl⟩ : syracuseStep 18405245 = 6901967) B6901967
theorem B73693151 : Blo 1275956 73693151 := bstep (se 1 (by rfl) ⟨55269863, by rfl⟩ : syracuseStep 73693151 = 110539727) B110539727
theorem B2873321 : Blo 1275956 2873321 := bstep (se 2 (by rfl) ⟨1077495, by rfl⟩ : syracuseStep 2873321 = 2154991) B2154991
theorem B1276399 : Blo 1275956 1276399 := bstep (se 1 (by rfl) ⟨957299, by rfl⟩ : syracuseStep 1276399 = 1914599) B1914599
theorem B1276415 : Blo 1275956 1276415 := bstep (se 1 (by rfl) ⟨957311, by rfl⟩ : syracuseStep 1276415 = 1914623) B1914623
theorem B15538817 : Blo 1275956 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B5823191 : Blo 1275956 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B1915643 : Blo 1275956 1915643 := bstep (se 1 (by rfl) ⟨1436732, by rfl⟩ : syracuseStep 1915643 = 2873465) B2873465
theorem B1276863 : Blo 1275956 1276863 := bstep (se 1 (by rfl) ⟨957647, by rfl⟩ : syracuseStep 1276863 = 1915295) B1915295
theorem B49765391 : Blo 1275956 49765391 := bstep (se 1 (by rfl) ⟨37324043, by rfl⟩ : syracuseStep 49765391 = 74648087) B74648087
theorem B44817565 : Blo 1275956 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B2874527 : Blo 1275956 2874527 := bstep (se 1 (by rfl) ⟨2155895, by rfl⟩ : syracuseStep 2874527 = 4311791) B4311791
theorem B124173485 : Blo 1275956 124173485 := bstep (se 3 (by rfl) ⟨23282528, by rfl⟩ : syracuseStep 124173485 = 46565057) B46565057
theorem B151387319 : Blo 1275956 151387319 := bstep (se 1 (by rfl) ⟨113540489, by rfl⟩ : syracuseStep 151387319 = 227080979) B227080979
theorem B1277247 : Blo 1275956 1277247 := bstep (se 1 (by rfl) ⟨957935, by rfl⟩ : syracuseStep 1277247 = 1915871) B1915871
theorem B336076231 : Blo 1275956 336076231 := bstep (se 1 (by rfl) ⟨252057173, by rfl⟩ : syracuseStep 336076231 = 504114347) B504114347
theorem B4308551 : Blo 1275956 4308551 := bstep (se 1 (by rfl) ⟨3231413, by rfl⟩ : syracuseStep 4308551 = 6462827) B6462827
theorem B1916699 : Blo 1275956 1916699 := bstep (se 1 (by rfl) ⟨1437524, by rfl⟩ : syracuseStep 1916699 = 2875049) B2875049
theorem B1277823 : Blo 1275956 1277823 := bstep (se 1 (by rfl) ⟨958367, by rfl⟩ : syracuseStep 1277823 = 1916735) B1916735
theorem B2154377 : Blo 1275956 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B10903835 : Blo 1275956 10903835 := bstep (se 1 (by rfl) ⟨8177876, by rfl⟩ : syracuseStep 10903835 = 16355753) B16355753
theorem B2155423 : Blo 1275956 2155423 := bstep (se 1 (by rfl) ⟨1616567, by rfl⟩ : syracuseStep 2155423 = 3233135) B3233135
theorem B3638303 : Blo 1275956 3638303 := bstep (se 1 (by rfl) ⟨2728727, by rfl⟩ : syracuseStep 3638303 = 5457455) B5457455
theorem B4310279 : Blo 1275956 4310279 := bstep (se 1 (by rfl) ⟨3232709, by rfl⟩ : syracuseStep 4310279 = 6465419) B6465419
theorem B49128767 : Blo 1275956 49128767 := bstep (se 1 (by rfl) ⟨36846575, by rfl⟩ : syracuseStep 49128767 = 73693151) B73693151
theorem B4851191 : Blo 1275956 4851191 := bstep (se 1 (by rfl) ⟨3638393, by rfl⟩ : syracuseStep 4851191 = 7276787) B7276787
theorem B3065897 : Blo 1275956 3065897 := bstep (se 2 (by rfl) ⟨1149711, by rfl⟩ : syracuseStep 3065897 = 2299423) B2299423
theorem B82782323 : Blo 1275956 82782323 := bstep (se 1 (by rfl) ⟨62086742, by rfl⟩ : syracuseStep 82782323 = 124173485) B124173485
theorem B1436251 : Blo 1275956 1436251 := bstep (se 1 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 1436251 = 2154377) B2154377
theorem B21826259 : Blo 1275956 21826259 := bstep (se 1 (by rfl) ⟨16369694, by rfl⟩ : syracuseStep 21826259 = 32739389) B32739389
theorem B9694727 : Blo 1275956 9694727 := bstep (se 1 (by rfl) ⟨7271045, by rfl⟩ : syracuseStep 9694727 = 14542091) B14542091
theorem B4091759 : Blo 1275956 4091759 := bstep (se 1 (by rfl) ⟨3068819, by rfl⟩ : syracuseStep 4091759 = 6137639) B6137639
theorem B14545007 : Blo 1275956 14545007 := bstep (se 1 (by rfl) ⟨10908755, by rfl⟩ : syracuseStep 14545007 = 21817511) B21817511
theorem B3936377 : Blo 1275956 3936377 := bstep (se 2 (by rfl) ⟨1476141, by rfl⟩ : syracuseStep 3936377 = 2952283) B2952283
theorem B59756753 : Blo 1275956 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B2044207 : Blo 1275956 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B10359211 : Blo 1275956 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B6468011 : Blo 1275956 6468011 := bstep (se 1 (by rfl) ⟨4851008, by rfl⟩ : syracuseStep 6468011 = 9702017) B9702017
theorem B3633599 : Blo 1275956 3633599 := bstep (se 1 (by rfl) ⟨2725199, by rfl⟩ : syracuseStep 3633599 = 5450399) B5450399
theorem B3453407 : Blo 1275956 3453407 := bstep (se 1 (by rfl) ⟨2590055, by rfl⟩ : syracuseStep 3453407 = 5180111) B5180111
theorem B46625645 : Blo 1275956 46625645 := bstep (se 3 (by rfl) ⟨8742308, by rfl⟩ : syracuseStep 46625645 = 17484617) B17484617
theorem B2872367 : Blo 1275956 2872367 := bstep (se 1 (by rfl) ⟨2154275, by rfl⟩ : syracuseStep 2872367 = 4308551) B4308551
theorem B1914335 : Blo 1275956 1914335 := bstep (se 1 (by rfl) ⟨1435751, by rfl⟩ : syracuseStep 1914335 = 2871503) B2871503
theorem B1914347 : Blo 1275956 1914347 := bstep (se 1 (by rfl) ⟨1435760, by rfl⟩ : syracuseStep 1914347 = 2871521) B2871521
theorem B1914431 : Blo 1275956 1914431 := bstep (se 1 (by rfl) ⟨1435823, by rfl⟩ : syracuseStep 1914431 = 2871647) B2871647
theorem B17479415 : Blo 1275956 17479415 := bstep (se 1 (by rfl) ⟨13109561, by rfl⟩ : syracuseStep 17479415 = 26219123) B26219123
theorem B1726319 : Blo 1275956 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B14956415 : Blo 1275956 14956415 := bstep (se 1 (by rfl) ⟨11217311, by rfl⟩ : syracuseStep 14956415 = 22434623) B22434623
theorem B22116311 : Blo 1275956 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B1914857 : Blo 1275956 1914857 := bstep (se 2 (by rfl) ⟨718071, by rfl⟩ : syracuseStep 1914857 = 1436143) B1436143
theorem B2725883 : Blo 1275956 2725883 := bstep (se 1 (by rfl) ⟨2044412, by rfl⟩ : syracuseStep 2725883 = 4088825) B4088825
theorem B1275967 : Blo 1275956 1275967 := bstep (se 1 (by rfl) ⟨956975, by rfl⟩ : syracuseStep 1275967 = 1913951) B1913951
theorem B1276031 : Blo 1275956 1276031 := bstep (se 1 (by rfl) ⟨957023, by rfl⟩ : syracuseStep 1276031 = 1914047) B1914047
theorem B1915055 : Blo 1275956 1915055 := bstep (se 1 (by rfl) ⟨1436291, by rfl⟩ : syracuseStep 1915055 = 2872583) B2872583
theorem B1276111 : Blo 1275956 1276111 := bstep (se 1 (by rfl) ⟨957083, by rfl⟩ : syracuseStep 1276111 = 1914167) B1914167
theorem B1915103 : Blo 1275956 1915103 := bstep (se 1 (by rfl) ⟨1436327, by rfl⟩ : syracuseStep 1915103 = 2872655) B2872655
theorem B2873663 : Blo 1275956 2873663 := bstep (se 1 (by rfl) ⟨2155247, by rfl⟩ : syracuseStep 2873663 = 4310495) B4310495
theorem B9697643 : Blo 1275956 9697643 := bstep (se 1 (by rfl) ⟨7273232, by rfl⟩ : syracuseStep 9697643 = 14546465) B14546465
theorem B39303569 : Blo 1275956 39303569 := bstep (se 2 (by rfl) ⟨14738838, by rfl⟩ : syracuseStep 39303569 = 29477677) B29477677
theorem B1816987 : Blo 1275956 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B12270163 : Blo 1275956 12270163 := bstep (se 1 (by rfl) ⟨9202622, by rfl⟩ : syracuseStep 12270163 = 18405245) B18405245
theorem B1915547 : Blo 1275956 1915547 := bstep (se 1 (by rfl) ⟨1436660, by rfl⟩ : syracuseStep 1915547 = 2873321) B2873321
theorem B2874095 : Blo 1275956 2874095 := bstep (se 1 (by rfl) ⟨2155571, by rfl⟩ : syracuseStep 2874095 = 4311143) B4311143
theorem B3882127 : Blo 1275956 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B1277095 : Blo 1275956 1277095 := bstep (se 1 (by rfl) ⟨957821, by rfl⟩ : syracuseStep 1277095 = 1915643) B1915643
theorem B448101641 : Blo 1275956 448101641 := bstep (se 2 (by rfl) ⟨168038115, by rfl⟩ : syracuseStep 448101641 = 336076231) B336076231
theorem B33176927 : Blo 1275956 33176927 := bstep (se 1 (by rfl) ⟨24882695, by rfl⟩ : syracuseStep 33176927 = 49765391) B49765391
theorem B1916351 : Blo 1275956 1916351 := bstep (se 1 (by rfl) ⟨1437263, by rfl⟩ : syracuseStep 1916351 = 2874527) B2874527
theorem B100924879 : Blo 1275956 100924879 := bstep (se 1 (by rfl) ⟨75693659, by rfl⟩ : syracuseStep 100924879 = 151387319) B151387319
theorem B2154235 : Blo 1275956 2154235 := bstep (se 1 (by rfl) ⟨1615676, by rfl⟩ : syracuseStep 2154235 = 3231353) B3231353
theorem B2875175 : Blo 1275956 2875175 := bstep (se 1 (by rfl) ⟨2156381, by rfl⟩ : syracuseStep 2875175 = 4312763) B4312763
theorem B2154343 : Blo 1275956 2154343 := bstep (se 1 (by rfl) ⟨1615757, by rfl⟩ : syracuseStep 2154343 = 3231515) B3231515
theorem B1277799 : Blo 1275956 1277799 := bstep (se 1 (by rfl) ⟨958349, by rfl⟩ : syracuseStep 1277799 = 1916699) B1916699
theorem B8175725 : Blo 1275956 8175725 := bstep (se 3 (by rfl) ⟨1532948, by rfl⟩ : syracuseStep 8175725 = 3065897) B3065897
theorem B39837835 : Blo 1275956 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B2302271 : Blo 1275956 2302271 := bstep (se 1 (by rfl) ⟨1726703, by rfl⟩ : syracuseStep 2302271 = 3453407) B3453407
theorem B13812281 : Blo 1275956 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B2425535 : Blo 1275956 2425535 := bstep (se 1 (by rfl) ⟨1819151, by rfl⟩ : syracuseStep 2425535 = 3638303) B3638303
theorem B16360217 : Blo 1275956 16360217 := bstep (se 2 (by rfl) ⟨6135081, by rfl⟩ : syracuseStep 16360217 = 12270163) B12270163
theorem B32752511 : Blo 1275956 32752511 := bstep (se 1 (by rfl) ⟨24564383, by rfl⟩ : syracuseStep 32752511 = 49128767) B49128767
theorem B9970943 : Blo 1275956 9970943 := bstep (se 1 (by rfl) ⟨7478207, by rfl⟩ : syracuseStep 9970943 = 14956415) B14956415
theorem B6465095 : Blo 1275956 6465095 := bstep (se 1 (by rfl) ⟨4848821, by rfl⟩ : syracuseStep 6465095 = 9697643) B9697643
theorem B14550839 : Blo 1275956 14550839 := bstep (se 1 (by rfl) ⟨10913129, by rfl⟩ : syracuseStep 14550839 = 21826259) B21826259
theorem B2624251 : Blo 1275956 2624251 := bstep (se 1 (by rfl) ⟨1968188, by rfl⟩ : syracuseStep 2624251 = 3936377) B3936377
theorem B7269223 : Blo 1275956 7269223 := bstep (se 1 (by rfl) ⟨5451917, by rfl⟩ : syracuseStep 7269223 = 10903835) B10903835
theorem B4312007 : Blo 1275956 4312007 := bstep (se 1 (by rfl) ⟨3234005, by rfl⟩ : syracuseStep 4312007 = 6468011) B6468011
theorem B31083763 : Blo 1275956 31083763 := bstep (se 1 (by rfl) ⟨23312822, by rfl⟩ : syracuseStep 31083763 = 46625645) B46625645
theorem B26202379 : Blo 1275956 26202379 := bstep (se 1 (by rfl) ⟨19651784, by rfl⟩ : syracuseStep 26202379 = 39303569) B39303569
theorem B134566505 : Blo 1275956 134566505 := bstep (se 2 (by rfl) ⟨50462439, by rfl⟩ : syracuseStep 134566505 = 100924879) B100924879
theorem B298734427 : Blo 1275956 298734427 := bstep (se 1 (by rfl) ⟨224050820, by rfl⟩ : syracuseStep 298734427 = 448101641) B448101641
theorem B2872313 : Blo 1275956 2872313 := bstep (se 2 (by rfl) ⟨1077117, by rfl⟩ : syracuseStep 2872313 = 2154235) B2154235
theorem B2872457 : Blo 1275956 2872457 := bstep (se 2 (by rfl) ⟨1077171, by rfl⟩ : syracuseStep 2872457 = 2154343) B2154343
theorem B9696671 : Blo 1275956 9696671 := bstep (se 1 (by rfl) ⟨7272503, by rfl⟩ : syracuseStep 9696671 = 14545007) B14545007
theorem B2422399 : Blo 1275956 2422399 := bstep (se 1 (by rfl) ⟨1816799, by rfl⟩ : syracuseStep 2422399 = 3633599) B3633599
theorem B2422649 : Blo 1275956 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B1914911 : Blo 1275956 1914911 := bstep (se 1 (by rfl) ⟨1436183, by rfl⟩ : syracuseStep 1914911 = 2872367) B2872367
theorem B1915001 : Blo 1275956 1915001 := bstep (se 2 (by rfl) ⟨718125, by rfl⟩ : syracuseStep 1915001 = 1436251) B1436251
theorem B2873519 : Blo 1275956 2873519 := bstep (se 1 (by rfl) ⟨2155139, by rfl⟩ : syracuseStep 2873519 = 4310279) B4310279
theorem B1276223 : Blo 1275956 1276223 := bstep (se 1 (by rfl) ⟨957167, by rfl⟩ : syracuseStep 1276223 = 1914335) B1914335
theorem B1276231 : Blo 1275956 1276231 := bstep (se 1 (by rfl) ⟨957173, by rfl⟩ : syracuseStep 1276231 = 1914347) B1914347
theorem B3234127 : Blo 1275956 3234127 := bstep (se 1 (by rfl) ⟨2425595, by rfl⟩ : syracuseStep 3234127 = 4851191) B4851191
theorem B1276287 : Blo 1275956 1276287 := bstep (se 1 (by rfl) ⟨957215, by rfl⟩ : syracuseStep 1276287 = 1914431) B1914431
theorem B2873897 : Blo 1275956 2873897 := bstep (se 2 (by rfl) ⟨1077711, by rfl⟩ : syracuseStep 2873897 = 2155423) B2155423
theorem B14744207 : Blo 1275956 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B1276571 : Blo 1275956 1276571 := bstep (se 1 (by rfl) ⟨957428, by rfl⟩ : syracuseStep 1276571 = 1914857) B1914857
theorem B1817255 : Blo 1275956 1817255 := bstep (se 1 (by rfl) ⟨1362941, by rfl⟩ : syracuseStep 1817255 = 2725883) B2725883
theorem B55188215 : Blo 1275956 55188215 := bstep (se 1 (by rfl) ⟨41391161, by rfl⟩ : syracuseStep 55188215 = 82782323) B82782323
theorem B1276703 : Blo 1275956 1276703 := bstep (se 1 (by rfl) ⟨957527, by rfl⟩ : syracuseStep 1276703 = 1915055) B1915055
theorem B1276735 : Blo 1275956 1276735 := bstep (se 1 (by rfl) ⟨957551, by rfl⟩ : syracuseStep 1276735 = 1915103) B1915103
theorem B5176169 : Blo 1275956 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B1915775 : Blo 1275956 1915775 := bstep (se 1 (by rfl) ⟨1436831, by rfl⟩ : syracuseStep 1915775 = 2873663) B2873663
theorem B10902437 : Blo 1275956 10902437 := bstep (se 4 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 10902437 = 2044207) B2044207
theorem B1277031 : Blo 1275956 1277031 := bstep (se 1 (by rfl) ⟨957773, by rfl⟩ : syracuseStep 1277031 = 1915547) B1915547
theorem B1916063 : Blo 1275956 1916063 := bstep (se 1 (by rfl) ⟨1437047, by rfl⟩ : syracuseStep 1916063 = 2874095) B2874095
theorem B46611773 : Blo 1275956 46611773 := bstep (se 3 (by rfl) ⟨8739707, by rfl⟩ : syracuseStep 46611773 = 17479415) B17479415
theorem B22117951 : Blo 1275956 22117951 := bstep (se 1 (by rfl) ⟨16588463, by rfl⟩ : syracuseStep 22117951 = 33176927) B33176927
theorem B4603517 : Blo 1275956 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B1277567 : Blo 1275956 1277567 := bstep (se 1 (by rfl) ⟨958175, by rfl⟩ : syracuseStep 1277567 = 1916351) B1916351
theorem B6463151 : Blo 1275956 6463151 := bstep (se 1 (by rfl) ⟨4847363, by rfl⟩ : syracuseStep 6463151 = 9694727) B9694727
theorem B1916783 : Blo 1275956 1916783 := bstep (se 1 (by rfl) ⟨1437587, by rfl⟩ : syracuseStep 1916783 = 2875175) B2875175
theorem B2727839 : Blo 1275956 2727839 := bstep (se 1 (by rfl) ⟨2045879, by rfl⟩ : syracuseStep 2727839 = 4091759) B4091759
theorem B9208187 : Blo 1275956 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B89711003 : Blo 1275956 89711003 := bstep (se 1 (by rfl) ⟨67283252, by rfl⟩ : syracuseStep 89711003 = 134566505) B134566505
theorem B212468453 : Blo 1275956 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B6464447 : Blo 1275956 6464447 := bstep (se 1 (by rfl) ⟨4848335, by rfl⟩ : syracuseStep 6464447 = 9696671) B9696671
theorem B3499001 : Blo 1275956 3499001 := bstep (se 2 (by rfl) ⟨1312125, by rfl⟩ : syracuseStep 3499001 = 2624251) B2624251
theorem B4310063 : Blo 1275956 4310063 := bstep (se 1 (by rfl) ⟨3232547, by rfl⟩ : syracuseStep 4310063 = 6465095) B6465095
theorem B398312569 : Blo 1275956 398312569 := bstep (se 2 (by rfl) ⟨149367213, by rfl⟩ : syracuseStep 398312569 = 298734427) B298734427
theorem B9692297 : Blo 1275956 9692297 := bstep (se 2 (by rfl) ⟨3634611, by rfl⟩ : syracuseStep 9692297 = 7269223) B7269223
theorem B9700559 : Blo 1275956 9700559 := bstep (se 1 (by rfl) ⟨7275419, by rfl⟩ : syracuseStep 9700559 = 14550839) B14550839
theorem B41445017 : Blo 1275956 41445017 := bstep (se 2 (by rfl) ⟨15541881, by rfl⟩ : syracuseStep 41445017 = 31083763) B31083763
theorem B36792143 : Blo 1275956 36792143 := bstep (se 1 (by rfl) ⟨27594107, by rfl⟩ : syracuseStep 36792143 = 55188215) B55188215
theorem B3450779 : Blo 1275956 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B7268291 : Blo 1275956 7268291 := bstep (se 1 (by rfl) ⟨5451218, by rfl⟩ : syracuseStep 7268291 = 10902437) B10902437
theorem B3229865 : Blo 1275956 3229865 := bstep (se 2 (by rfl) ⟨1211199, by rfl⟩ : syracuseStep 3229865 = 2422399) B2422399
theorem B31074515 : Blo 1275956 31074515 := bstep (se 1 (by rfl) ⟨23305886, by rfl⟩ : syracuseStep 31074515 = 46611773) B46611773
theorem B5450483 : Blo 1275956 5450483 := bstep (se 1 (by rfl) ⟨4087862, by rfl⟩ : syracuseStep 5450483 = 8175725) B8175725
theorem B1534847 : Blo 1275956 1534847 := bstep (se 1 (by rfl) ⟨1151135, by rfl⟩ : syracuseStep 1534847 = 2302271) B2302271
theorem B4312169 : Blo 1275956 4312169 := bstep (se 2 (by rfl) ⟨1617063, by rfl⟩ : syracuseStep 4312169 = 3234127) B3234127
theorem B1617023 : Blo 1275956 1617023 := bstep (se 1 (by rfl) ⟨1212767, by rfl⟩ : syracuseStep 1617023 = 2425535) B2425535
theorem B10906811 : Blo 1275956 10906811 := bstep (se 1 (by rfl) ⟨8180108, by rfl⟩ : syracuseStep 10906811 = 16360217) B16360217
theorem B21835007 : Blo 1275956 21835007 := bstep (se 1 (by rfl) ⟨16376255, by rfl⟩ : syracuseStep 21835007 = 32752511) B32752511
theorem B4846013 : Blo 1275956 4846013 := bstep (se 3 (by rfl) ⟨908627, by rfl⟩ : syracuseStep 4846013 = 1817255) B1817255
theorem B6460397 : Blo 1275956 6460397 := bstep (se 3 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 6460397 = 2422649) B2422649
theorem B3069011 : Blo 1275956 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B117962405 : Blo 1275956 117962405 := bstep (se 4 (by rfl) ⟨11058975, by rfl⟩ : syracuseStep 117962405 = 22117951) B22117951
theorem B34936505 : Blo 1275956 34936505 := bstep (se 2 (by rfl) ⟨13101189, by rfl⟩ : syracuseStep 34936505 = 26202379) B26202379
theorem B1914875 : Blo 1275956 1914875 := bstep (se 1 (by rfl) ⟨1436156, by rfl⟩ : syracuseStep 1914875 = 2872313) B2872313
theorem B26589181 : Blo 1275956 26589181 := bstep (se 3 (by rfl) ⟨4985471, by rfl⟩ : syracuseStep 26589181 = 9970943) B9970943
theorem B1914971 : Blo 1275956 1914971 := bstep (se 1 (by rfl) ⟨1436228, by rfl⟩ : syracuseStep 1914971 = 2872457) B2872457
theorem B1276607 : Blo 1275956 1276607 := bstep (se 1 (by rfl) ⟨957455, by rfl⟩ : syracuseStep 1276607 = 1914911) B1914911
theorem B1276667 : Blo 1275956 1276667 := bstep (se 1 (by rfl) ⟨957500, by rfl⟩ : syracuseStep 1276667 = 1915001) B1915001
theorem B1915679 : Blo 1275956 1915679 := bstep (se 1 (by rfl) ⟨1436759, by rfl⟩ : syracuseStep 1915679 = 2873519) B2873519
theorem B1915931 : Blo 1275956 1915931 := bstep (se 1 (by rfl) ⟨1436948, by rfl⟩ : syracuseStep 1915931 = 2873897) B2873897
theorem B9829471 : Blo 1275956 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B1277183 : Blo 1275956 1277183 := bstep (se 1 (by rfl) ⟨957887, by rfl⟩ : syracuseStep 1277183 = 1915775) B1915775
theorem B2874671 : Blo 1275956 2874671 := bstep (se 1 (by rfl) ⟨2156003, by rfl⟩ : syracuseStep 2874671 = 4312007) B4312007
theorem B1277375 : Blo 1275956 1277375 := bstep (se 1 (by rfl) ⟨958031, by rfl⟩ : syracuseStep 1277375 = 1916063) B1916063
theorem B4308767 : Blo 1275956 4308767 := bstep (se 1 (by rfl) ⟨3231575, by rfl⟩ : syracuseStep 4308767 = 6463151) B6463151
theorem B1277855 : Blo 1275956 1277855 := bstep (se 1 (by rfl) ⟨958391, by rfl⟩ : syracuseStep 1277855 = 1916783) B1916783
theorem B1818559 : Blo 1275956 1818559 := bstep (se 1 (by rfl) ⟨1363919, by rfl⟩ : syracuseStep 1818559 = 2727839) B2727839
theorem B4309631 : Blo 1275956 4309631 := bstep (se 1 (by rfl) ⟨3232223, by rfl⟩ : syracuseStep 4309631 = 6464447) B6464447
theorem B23291003 : Blo 1275956 23291003 := bstep (se 1 (by rfl) ⟨17468252, by rfl⟩ : syracuseStep 23291003 = 34936505) B34936505
theorem B24528095 : Blo 1275956 24528095 := bstep (se 1 (by rfl) ⟨18396071, by rfl⟩ : syracuseStep 24528095 = 36792143) B36792143
theorem B6138791 : Blo 1275956 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B3230675 : Blo 1275956 3230675 := bstep (se 1 (by rfl) ⟨2423006, by rfl⟩ : syracuseStep 3230675 = 4846013) B4846013
theorem B4312061 : Blo 1275956 4312061 := bstep (se 3 (by rfl) ⟨808511, by rfl⟩ : syracuseStep 4312061 = 1617023) B1617023
theorem B6467039 : Blo 1275956 6467039 := bstep (se 1 (by rfl) ⟨4850279, by rfl⟩ : syracuseStep 6467039 = 9700559) B9700559
theorem B4845527 : Blo 1275956 4845527 := bstep (se 1 (by rfl) ⟨3634145, by rfl⟩ : syracuseStep 4845527 = 7268291) B7268291
theorem B531083425 : Blo 1275956 531083425 := bstep (se 2 (by rfl) ⟨199156284, by rfl⟩ : syracuseStep 531083425 = 398312569) B398312569
theorem B3633655 : Blo 1275956 3633655 := bstep (se 1 (by rfl) ⟨2725241, by rfl⟩ : syracuseStep 3633655 = 5450483) B5450483
theorem B7271207 : Blo 1275956 7271207 := bstep (se 1 (by rfl) ⟨5453405, by rfl⟩ : syracuseStep 7271207 = 10906811) B10906811
theorem B4092925 : Blo 1275956 4092925 := bstep (se 3 (by rfl) ⟨767423, by rfl⟩ : syracuseStep 4092925 = 1534847) B1534847
theorem B2872511 : Blo 1275956 2872511 := bstep (se 1 (by rfl) ⟨2154383, by rfl⟩ : syracuseStep 2872511 = 4308767) B4308767
theorem B35452241 : Blo 1275956 35452241 := bstep (se 2 (by rfl) ⟨13294590, by rfl⟩ : syracuseStep 35452241 = 26589181) B26589181
theorem B59807335 : Blo 1275956 59807335 := bstep (se 1 (by rfl) ⟨44855501, by rfl⟩ : syracuseStep 59807335 = 89711003) B89711003
theorem B141645635 : Blo 1275956 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B4306931 : Blo 1275956 4306931 := bstep (se 1 (by rfl) ⟨3230198, by rfl⟩ : syracuseStep 4306931 = 6460397) B6460397
theorem B2332667 : Blo 1275956 2332667 := bstep (se 1 (by rfl) ⟨1749500, by rfl⟩ : syracuseStep 2332667 = 3499001) B3499001
theorem B2873375 : Blo 1275956 2873375 := bstep (se 1 (by rfl) ⟨2155031, by rfl⟩ : syracuseStep 2873375 = 4310063) B4310063
theorem B2046007 : Blo 1275956 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B6461531 : Blo 1275956 6461531 := bstep (se 1 (by rfl) ⟨4846148, by rfl⟩ : syracuseStep 6461531 = 9692297) B9692297
theorem B27630011 : Blo 1275956 27630011 := bstep (se 1 (by rfl) ⟨20722508, by rfl⟩ : syracuseStep 27630011 = 41445017) B41445017
theorem B78641603 : Blo 1275956 78641603 := bstep (se 1 (by rfl) ⟨58981202, by rfl⟩ : syracuseStep 78641603 = 117962405) B117962405
theorem B2300519 : Blo 1275956 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B1276583 : Blo 1275956 1276583 := bstep (se 1 (by rfl) ⟨957437, by rfl⟩ : syracuseStep 1276583 = 1914875) B1914875
theorem B1276647 : Blo 1275956 1276647 := bstep (se 1 (by rfl) ⟨957485, by rfl⟩ : syracuseStep 1276647 = 1914971) B1914971
theorem B2153243 : Blo 1275956 2153243 := bstep (se 1 (by rfl) ⟨1614932, by rfl⟩ : syracuseStep 2153243 = 3229865) B3229865
theorem B13105961 : Blo 1275956 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B20716343 : Blo 1275956 20716343 := bstep (se 1 (by rfl) ⟨15537257, by rfl⟩ : syracuseStep 20716343 = 31074515) B31074515
theorem B1277119 : Blo 1275956 1277119 := bstep (se 1 (by rfl) ⟨957839, by rfl⟩ : syracuseStep 1277119 = 1915679) B1915679
theorem B1277287 : Blo 1275956 1277287 := bstep (se 1 (by rfl) ⟨957965, by rfl⟩ : syracuseStep 1277287 = 1915931) B1915931
theorem B2874779 : Blo 1275956 2874779 := bstep (se 1 (by rfl) ⟨2156084, by rfl⟩ : syracuseStep 2874779 = 4312169) B4312169
theorem B14556671 : Blo 1275956 14556671 := bstep (se 1 (by rfl) ⟨10917503, by rfl⟩ : syracuseStep 14556671 = 21835007) B21835007
theorem B1916447 : Blo 1275956 1916447 := bstep (se 1 (by rfl) ⟨1437335, by rfl⟩ : syracuseStep 1916447 = 2874671) B2874671
theorem B2424745 : Blo 1275956 2424745 := bstep (se 2 (by rfl) ⟨909279, by rfl⟩ : syracuseStep 2424745 = 1818559) B1818559
theorem B2728009 : Blo 1275956 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B16352063 : Blo 1275956 16352063 := bstep (se 1 (by rfl) ⟨12264047, by rfl⟩ : syracuseStep 16352063 = 24528095) B24528095
theorem B23634827 : Blo 1275956 23634827 := bstep (se 1 (by rfl) ⟨17726120, by rfl⟩ : syracuseStep 23634827 = 35452241) B35452241
theorem B94430423 : Blo 1275956 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B5457233 : Blo 1275956 5457233 := bstep (se 2 (by rfl) ⟨2046462, by rfl⟩ : syracuseStep 5457233 = 4092925) B4092925
theorem B1435495 : Blo 1275956 1435495 := bstep (se 1 (by rfl) ⟨1076621, by rfl⟩ : syracuseStep 1435495 = 2153243) B2153243
theorem B79743113 : Blo 1275956 79743113 := bstep (se 2 (by rfl) ⟨29903667, by rfl⟩ : syracuseStep 79743113 = 59807335) B59807335
theorem B4311359 : Blo 1275956 4311359 := bstep (se 1 (by rfl) ⟨3233519, by rfl⟩ : syracuseStep 4311359 = 6467039) B6467039
theorem B3230351 : Blo 1275956 3230351 := bstep (se 1 (by rfl) ⟨2422763, by rfl⟩ : syracuseStep 3230351 = 4845527) B4845527
theorem B708111233 : Blo 1275956 708111233 := bstep (se 2 (by rfl) ⟨265541712, by rfl⟩ : syracuseStep 708111233 = 531083425) B531083425
theorem B4844873 : Blo 1275956 4844873 := bstep (se 2 (by rfl) ⟨1816827, by rfl⟩ : syracuseStep 4844873 = 3633655) B3633655
theorem B15527335 : Blo 1275956 15527335 := bstep (se 1 (by rfl) ⟨11645501, by rfl⟩ : syracuseStep 15527335 = 23291003) B23291003
theorem B2871287 : Blo 1275956 2871287 := bstep (se 1 (by rfl) ⟨2153465, by rfl⟩ : syracuseStep 2871287 = 4306931) B4306931
theorem B18420007 : Blo 1275956 18420007 := bstep (se 1 (by rfl) ⟨13815005, by rfl⟩ : syracuseStep 18420007 = 27630011) B27630011
theorem B8737307 : Blo 1275956 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B4092527 : Blo 1275956 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B9704447 : Blo 1275956 9704447 := bstep (se 1 (by rfl) ⟨7278335, by rfl⟩ : syracuseStep 9704447 = 14556671) B14556671
theorem B3232993 : Blo 1275956 3232993 := bstep (se 2 (by rfl) ⟨1212372, by rfl⟩ : syracuseStep 3232993 = 2424745) B2424745
theorem B2873087 : Blo 1275956 2873087 := bstep (se 1 (by rfl) ⟨2154815, by rfl⟩ : syracuseStep 2873087 = 4309631) B4309631
theorem B4847471 : Blo 1275956 4847471 := bstep (se 1 (by rfl) ⟨3635603, by rfl⟩ : syracuseStep 4847471 = 7271207) B7271207
theorem B1915007 : Blo 1275956 1915007 := bstep (se 1 (by rfl) ⟨1436255, by rfl⟩ : syracuseStep 1915007 = 2872511) B2872511
theorem B1555111 : Blo 1275956 1555111 := bstep (se 1 (by rfl) ⟨1166333, by rfl⟩ : syracuseStep 1555111 = 2332667) B2332667
theorem B1915583 : Blo 1275956 1915583 := bstep (se 1 (by rfl) ⟨1436687, by rfl⟩ : syracuseStep 1915583 = 2873375) B2873375
theorem B4307687 : Blo 1275956 4307687 := bstep (se 1 (by rfl) ⟨3230765, by rfl⟩ : syracuseStep 4307687 = 6461531) B6461531
theorem B6134717 : Blo 1275956 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B52427735 : Blo 1275956 52427735 := bstep (se 1 (by rfl) ⟨39320801, by rfl⟩ : syracuseStep 52427735 = 78641603) B78641603
theorem B13810895 : Blo 1275956 13810895 := bstep (se 1 (by rfl) ⟨10358171, by rfl⟩ : syracuseStep 13810895 = 20716343) B20716343
theorem B2153783 : Blo 1275956 2153783 := bstep (se 1 (by rfl) ⟨1615337, by rfl⟩ : syracuseStep 2153783 = 3230675) B3230675
theorem B2874707 : Blo 1275956 2874707 := bstep (se 1 (by rfl) ⟨2156030, by rfl⟩ : syracuseStep 2874707 = 4312061) B4312061
theorem B1916519 : Blo 1275956 1916519 := bstep (se 1 (by rfl) ⟨1437389, by rfl⟩ : syracuseStep 1916519 = 2874779) B2874779
theorem B1277631 : Blo 1275956 1277631 := bstep (se 1 (by rfl) ⟨958223, by rfl⟩ : syracuseStep 1277631 = 1916447) B1916447
theorem B5824871 : Blo 1275956 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B14549381 : Blo 1275956 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B24560009 : Blo 1275956 24560009 := bstep (se 2 (by rfl) ⟨9210003, by rfl⟩ : syracuseStep 24560009 = 18420007) B18420007
theorem B2728351 : Blo 1275956 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B2073481 : Blo 1275956 2073481 := bstep (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) B1555111
theorem B3638155 : Blo 1275956 3638155 := bstep (se 1 (by rfl) ⟨2728616, by rfl⟩ : syracuseStep 3638155 = 5457233) B5457233
theorem B4310657 : Blo 1275956 4310657 := bstep (se 2 (by rfl) ⟨1616496, by rfl⟩ : syracuseStep 4310657 = 3232993) B3232993
theorem B20703113 : Blo 1275956 20703113 := bstep (se 2 (by rfl) ⟨7763667, by rfl⟩ : syracuseStep 20703113 = 15527335) B15527335
theorem B472074155 : Blo 1275956 472074155 := bstep (se 1 (by rfl) ⟨354055616, by rfl⟩ : syracuseStep 472074155 = 708111233) B708111233
theorem B4089811 : Blo 1275956 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B1435855 : Blo 1275956 1435855 := bstep (se 1 (by rfl) ⟨1076891, by rfl⟩ : syracuseStep 1435855 = 2153783) B2153783
theorem B3229915 : Blo 1275956 3229915 := bstep (se 1 (by rfl) ⟨2422436, by rfl⟩ : syracuseStep 3229915 = 4844873) B4844873
theorem B15756551 : Blo 1275956 15756551 := bstep (se 1 (by rfl) ⟨11817413, by rfl⟩ : syracuseStep 15756551 = 23634827) B23634827
theorem B3231647 : Blo 1275956 3231647 := bstep (se 1 (by rfl) ⟨2423735, by rfl⟩ : syracuseStep 3231647 = 4847471) B4847471
theorem B53162075 : Blo 1275956 53162075 := bstep (se 1 (by rfl) ⟨39871556, by rfl⟩ : syracuseStep 53162075 = 79743113) B79743113
theorem B2871791 : Blo 1275956 2871791 := bstep (se 1 (by rfl) ⟨2153843, by rfl⟩ : syracuseStep 2871791 = 4307687) B4307687
theorem B34951823 : Blo 1275956 34951823 := bstep (se 1 (by rfl) ⟨26213867, by rfl⟩ : syracuseStep 34951823 = 52427735) B52427735
theorem B1913993 : Blo 1275956 1913993 := bstep (se 2 (by rfl) ⟨717747, by rfl⟩ : syracuseStep 1913993 = 1435495) B1435495
theorem B1914191 : Blo 1275956 1914191 := bstep (se 1 (by rfl) ⟨1435643, by rfl⟩ : syracuseStep 1914191 = 2871287) B2871287
theorem B10901375 : Blo 1275956 10901375 := bstep (se 1 (by rfl) ⟨8176031, by rfl⟩ : syracuseStep 10901375 = 16352063) B16352063
theorem B6469631 : Blo 1275956 6469631 := bstep (se 1 (by rfl) ⟨4852223, by rfl⟩ : syracuseStep 6469631 = 9704447) B9704447
theorem B62953615 : Blo 1275956 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B1915391 : Blo 1275956 1915391 := bstep (se 1 (by rfl) ⟨1436543, by rfl⟩ : syracuseStep 1915391 = 2873087) B2873087
theorem B1276671 : Blo 1275956 1276671 := bstep (se 1 (by rfl) ⟨957503, by rfl⟩ : syracuseStep 1276671 = 1915007) B1915007
theorem B2874239 : Blo 1275956 2874239 := bstep (se 1 (by rfl) ⟨2155679, by rfl⟩ : syracuseStep 2874239 = 4311359) B4311359
theorem B2153567 : Blo 1275956 2153567 := bstep (se 1 (by rfl) ⟨1615175, by rfl⟩ : syracuseStep 2153567 = 3230351) B3230351
theorem B1277055 : Blo 1275956 1277055 := bstep (se 1 (by rfl) ⟨957791, by rfl⟩ : syracuseStep 1277055 = 1915583) B1915583
theorem B9207263 : Blo 1275956 9207263 := bstep (se 1 (by rfl) ⟨6905447, by rfl⟩ : syracuseStep 9207263 = 13810895) B13810895
theorem B1916471 : Blo 1275956 1916471 := bstep (se 1 (by rfl) ⟨1437353, by rfl⟩ : syracuseStep 1916471 = 2874707) B2874707
theorem B1277679 : Blo 1275956 1277679 := bstep (se 1 (by rfl) ⟨958259, by rfl⟩ : syracuseStep 1277679 = 1916519) B1916519
theorem B3883247 : Blo 1275956 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B9699587 : Blo 1275956 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B3637801 : Blo 1275956 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B4850873 : Blo 1275956 4850873 := bstep (se 2 (by rfl) ⟨1819077, by rfl⟩ : syracuseStep 4850873 = 3638155) B3638155
theorem B7267583 : Blo 1275956 7267583 := bstep (se 1 (by rfl) ⟨5450687, by rfl⟩ : syracuseStep 7267583 = 10901375) B10901375
theorem B1435711 : Blo 1275956 1435711 := bstep (se 1 (by rfl) ⟨1076783, by rfl⟩ : syracuseStep 1435711 = 2153567) B2153567
theorem B10504367 : Blo 1275956 10504367 := bstep (se 1 (by rfl) ⟨7878275, by rfl⟩ : syracuseStep 10504367 = 15756551) B15756551
theorem B6138175 : Blo 1275956 6138175 := bstep (se 1 (by rfl) ⟨4603631, by rfl⟩ : syracuseStep 6138175 = 9207263) B9207263
theorem B35441383 : Blo 1275956 35441383 := bstep (se 1 (by rfl) ⟨26581037, by rfl⟩ : syracuseStep 35441383 = 53162075) B53162075
theorem B83938153 : Blo 1275956 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B23301215 : Blo 1275956 23301215 := bstep (se 1 (by rfl) ⟨17475911, by rfl⟩ : syracuseStep 23301215 = 34951823) B34951823
theorem B314716103 : Blo 1275956 314716103 := bstep (se 1 (by rfl) ⟨236037077, by rfl⟩ : syracuseStep 314716103 = 472074155) B472074155
theorem B4313087 : Blo 1275956 4313087 := bstep (se 1 (by rfl) ⟨3234815, by rfl⟩ : syracuseStep 4313087 = 6469631) B6469631
theorem B5453081 : Blo 1275956 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B44234261 : Blo 1275956 44234261 := bstep (se 6 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 44234261 = 2073481) B2073481
theorem B16373339 : Blo 1275956 16373339 := bstep (se 1 (by rfl) ⟨12280004, by rfl⟩ : syracuseStep 16373339 = 24560009) B24560009
theorem B1914473 : Blo 1275956 1914473 := bstep (se 2 (by rfl) ⟨717927, by rfl⟩ : syracuseStep 1914473 = 1435855) B1435855
theorem B4306553 : Blo 1275956 4306553 := bstep (se 2 (by rfl) ⟨1614957, by rfl⟩ : syracuseStep 4306553 = 3229915) B3229915
theorem B1914527 : Blo 1275956 1914527 := bstep (se 1 (by rfl) ⟨1435895, by rfl⟩ : syracuseStep 1914527 = 2871791) B2871791
theorem B1275995 : Blo 1275956 1275995 := bstep (se 1 (by rfl) ⟨956996, by rfl⟩ : syracuseStep 1275995 = 1913993) B1913993
theorem B1276127 : Blo 1275956 1276127 := bstep (se 1 (by rfl) ⟨957095, by rfl⟩ : syracuseStep 1276127 = 1914191) B1914191
theorem B2873771 : Blo 1275956 2873771 := bstep (se 1 (by rfl) ⟨2155328, by rfl⟩ : syracuseStep 2873771 = 4310657) B4310657
theorem B13802075 : Blo 1275956 13802075 := bstep (se 1 (by rfl) ⟨10351556, by rfl⟩ : syracuseStep 13802075 = 20703113) B20703113
theorem B1276927 : Blo 1275956 1276927 := bstep (se 1 (by rfl) ⟨957695, by rfl⟩ : syracuseStep 1276927 = 1915391) B1915391
theorem B1916159 : Blo 1275956 1916159 := bstep (se 1 (by rfl) ⟨1437119, by rfl⟩ : syracuseStep 1916159 = 2874239) B2874239
theorem B1277647 : Blo 1275956 1277647 := bstep (se 1 (by rfl) ⟨958235, by rfl⟩ : syracuseStep 1277647 = 1916471) B1916471
theorem B2154431 : Blo 1275956 2154431 := bstep (se 1 (by rfl) ⟨1615823, by rfl⟩ : syracuseStep 2154431 = 3231647) B3231647
theorem B2588831 : Blo 1275956 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B8184233 : Blo 1275956 8184233 := bstep (se 2 (by rfl) ⟨3069087, by rfl⟩ : syracuseStep 8184233 = 6138175) B6138175
theorem B4850401 : Blo 1275956 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B9201383 : Blo 1275956 9201383 := bstep (se 1 (by rfl) ⟨6901037, by rfl⟩ : syracuseStep 9201383 = 13802075) B13802075
theorem B15534143 : Blo 1275956 15534143 := bstep (se 1 (by rfl) ⟨11650607, by rfl⟩ : syracuseStep 15534143 = 23301215) B23301215
theorem B1436287 : Blo 1275956 1436287 := bstep (se 1 (by rfl) ⟨1077215, by rfl⟩ : syracuseStep 1436287 = 2154431) B2154431
theorem B6466391 : Blo 1275956 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B4845055 : Blo 1275956 4845055 := bstep (se 1 (by rfl) ⟨3633791, by rfl⟩ : syracuseStep 4845055 = 7267583) B7267583
theorem B47255177 : Blo 1275956 47255177 := bstep (se 2 (by rfl) ⟨17720691, by rfl⟩ : syracuseStep 47255177 = 35441383) B35441383
theorem B10915559 : Blo 1275956 10915559 := bstep (se 1 (by rfl) ⟨8186669, by rfl⟩ : syracuseStep 10915559 = 16373339) B16373339
theorem B2871035 : Blo 1275956 2871035 := bstep (se 1 (by rfl) ⟨2153276, by rfl⟩ : syracuseStep 2871035 = 4306553) B4306553
theorem B209810735 : Blo 1275956 209810735 := bstep (se 1 (by rfl) ⟨157358051, by rfl⟩ : syracuseStep 209810735 = 314716103) B314716103
theorem B1914281 : Blo 1275956 1914281 := bstep (se 2 (by rfl) ⟨717855, by rfl⟩ : syracuseStep 1914281 = 1435711) B1435711
theorem B3233915 : Blo 1275956 3233915 := bstep (se 1 (by rfl) ⟨2425436, by rfl⟩ : syracuseStep 3233915 = 4850873) B4850873
theorem B3635387 : Blo 1275956 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B29489507 : Blo 1275956 29489507 := bstep (se 1 (by rfl) ⟨22117130, by rfl⟩ : syracuseStep 29489507 = 44234261) B44234261
theorem B1276315 : Blo 1275956 1276315 := bstep (se 1 (by rfl) ⟨957236, by rfl⟩ : syracuseStep 1276315 = 1914473) B1914473
theorem B1276351 : Blo 1275956 1276351 := bstep (se 1 (by rfl) ⟨957263, by rfl⟩ : syracuseStep 1276351 = 1914527) B1914527
theorem B111917537 : Blo 1275956 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B7002911 : Blo 1275956 7002911 := bstep (se 1 (by rfl) ⟨5252183, by rfl⟩ : syracuseStep 7002911 = 10504367) B10504367
theorem B1915847 : Blo 1275956 1915847 := bstep (se 1 (by rfl) ⟨1436885, by rfl⟩ : syracuseStep 1915847 = 2873771) B2873771
theorem B1277439 : Blo 1275956 1277439 := bstep (se 1 (by rfl) ⟨958079, by rfl⟩ : syracuseStep 1277439 = 1916159) B1916159
theorem B2875391 : Blo 1275956 2875391 := bstep (se 1 (by rfl) ⟨2156543, by rfl⟩ : syracuseStep 2875391 = 4313087) B4313087
theorem B5456155 : Blo 1275956 5456155 := bstep (se 1 (by rfl) ⟨4092116, by rfl⟩ : syracuseStep 5456155 = 8184233) B8184233
theorem B10356095 : Blo 1275956 10356095 := bstep (se 1 (by rfl) ⟨7767071, by rfl⟩ : syracuseStep 10356095 = 15534143) B15534143
theorem B2155943 : Blo 1275956 2155943 := bstep (se 1 (by rfl) ⟨1616957, by rfl⟩ : syracuseStep 2155943 = 3233915) B3233915
theorem B4310927 : Blo 1275956 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B7277039 : Blo 1275956 7277039 := bstep (se 1 (by rfl) ⟨5457779, by rfl⟩ : syracuseStep 7277039 = 10915559) B10915559
theorem B1916927 : Blo 1275956 1916927 := bstep (se 1 (by rfl) ⟨1437695, by rfl⟩ : syracuseStep 1916927 = 2875391) B2875391
theorem B139873823 : Blo 1275956 139873823 := bstep (se 1 (by rfl) ⟨104905367, by rfl⟩ : syracuseStep 139873823 = 209810735) B209810735
theorem B6467201 : Blo 1275956 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B6460073 : Blo 1275956 6460073 := bstep (se 2 (by rfl) ⟨2422527, by rfl⟩ : syracuseStep 6460073 = 4845055) B4845055
theorem B31503451 : Blo 1275956 31503451 := bstep (se 1 (by rfl) ⟨23627588, by rfl⟩ : syracuseStep 31503451 = 47255177) B47255177
theorem B1914023 : Blo 1275956 1914023 := bstep (se 1 (by rfl) ⟨1435517, by rfl⟩ : syracuseStep 1914023 = 2871035) B2871035
theorem B1725887 : Blo 1275956 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B1915049 : Blo 1275956 1915049 := bstep (se 2 (by rfl) ⟨718143, by rfl⟩ : syracuseStep 1915049 = 1436287) B1436287
theorem B1276187 : Blo 1275956 1276187 := bstep (se 1 (by rfl) ⟨957140, by rfl⟩ : syracuseStep 1276187 = 1914281) B1914281
theorem B6134255 : Blo 1275956 6134255 := bstep (se 1 (by rfl) ⟨4600691, by rfl⟩ : syracuseStep 6134255 = 9201383) B9201383
theorem B2423591 : Blo 1275956 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B19659671 : Blo 1275956 19659671 := bstep (se 1 (by rfl) ⟨14744753, by rfl⟩ : syracuseStep 19659671 = 29489507) B29489507
theorem B74611691 : Blo 1275956 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B4668607 : Blo 1275956 4668607 := bstep (se 1 (by rfl) ⟨3501455, by rfl⟩ : syracuseStep 4668607 = 7002911) B7002911
theorem B1277231 : Blo 1275956 1277231 := bstep (se 1 (by rfl) ⟨957923, by rfl⟩ : syracuseStep 1277231 = 1915847) B1915847
theorem B7274873 : Blo 1275956 7274873 := bstep (se 2 (by rfl) ⟨2728077, by rfl⟩ : syracuseStep 7274873 = 5456155) B5456155
theorem B4089503 : Blo 1275956 4089503 := bstep (se 1 (by rfl) ⟨3067127, by rfl⟩ : syracuseStep 4089503 = 6134255) B6134255
theorem B4851359 : Blo 1275956 4851359 := bstep (se 1 (by rfl) ⟨3638519, by rfl⟩ : syracuseStep 4851359 = 7277039) B7277039
theorem B1615727 : Blo 1275956 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B4311467 : Blo 1275956 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B1437295 : Blo 1275956 1437295 := bstep (se 1 (by rfl) ⟨1077971, by rfl⟩ : syracuseStep 1437295 = 2155943) B2155943
theorem B24899237 : Blo 1275956 24899237 := bstep (se 4 (by rfl) ⟨2334303, by rfl⟩ : syracuseStep 24899237 = 4668607) B4668607
theorem B42004601 : Blo 1275956 42004601 := bstep (se 2 (by rfl) ⟨15751725, by rfl⟩ : syracuseStep 42004601 = 31503451) B31503451
theorem B4306715 : Blo 1275956 4306715 := bstep (se 1 (by rfl) ⟨3230036, by rfl⟩ : syracuseStep 4306715 = 6460073) B6460073
theorem B1276015 : Blo 1275956 1276015 := bstep (se 1 (by rfl) ⟨957011, by rfl⟩ : syracuseStep 1276015 = 1914023) B1914023
theorem B6904063 : Blo 1275956 6904063 := bstep (se 1 (by rfl) ⟨5178047, by rfl⟩ : syracuseStep 6904063 = 10356095) B10356095
theorem B4602365 : Blo 1275956 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B2873951 : Blo 1275956 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B1276699 : Blo 1275956 1276699 := bstep (se 1 (by rfl) ⟨957524, by rfl⟩ : syracuseStep 1276699 = 1915049) B1915049
theorem B13106447 : Blo 1275956 13106447 := bstep (se 1 (by rfl) ⟨9829835, by rfl⟩ : syracuseStep 13106447 = 19659671) B19659671
theorem B49741127 : Blo 1275956 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B93249215 : Blo 1275956 93249215 := bstep (se 1 (by rfl) ⟨69936911, by rfl⟩ : syracuseStep 93249215 = 139873823) B139873823
theorem B1277951 : Blo 1275956 1277951 := bstep (se 1 (by rfl) ⟨958463, by rfl⟩ : syracuseStep 1277951 = 1916927) B1916927
theorem B4849915 : Blo 1275956 4849915 := bstep (se 1 (by rfl) ⟨3637436, by rfl⟩ : syracuseStep 4849915 = 7274873) B7274873
theorem B16599491 : Blo 1275956 16599491 := bstep (se 1 (by rfl) ⟨12449618, by rfl⟩ : syracuseStep 16599491 = 24899237) B24899237
theorem B28003067 : Blo 1275956 28003067 := bstep (se 1 (by rfl) ⟨21002300, by rfl⟩ : syracuseStep 28003067 = 42004601) B42004601
theorem B2871143 : Blo 1275956 2871143 := bstep (se 1 (by rfl) ⟨2153357, by rfl⟩ : syracuseStep 2871143 = 4306715) B4306715
theorem B3068243 : Blo 1275956 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B8737631 : Blo 1275956 8737631 := bstep (se 1 (by rfl) ⟨6553223, by rfl⟩ : syracuseStep 8737631 = 13106447) B13106447
theorem B62166143 : Blo 1275956 62166143 := bstep (se 1 (by rfl) ⟨46624607, by rfl⟩ : syracuseStep 62166143 = 93249215) B93249215
theorem B9205417 : Blo 1275956 9205417 := bstep (se 2 (by rfl) ⟨3452031, by rfl⟩ : syracuseStep 9205417 = 6904063) B6904063
theorem B2726335 : Blo 1275956 2726335 := bstep (se 1 (by rfl) ⟨2044751, by rfl⟩ : syracuseStep 2726335 = 4089503) B4089503
theorem B3234239 : Blo 1275956 3234239 := bstep (se 1 (by rfl) ⟨2425679, by rfl⟩ : syracuseStep 3234239 = 4851359) B4851359
theorem B2874311 : Blo 1275956 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B1915967 : Blo 1275956 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B1916393 : Blo 1275956 1916393 := bstep (se 2 (by rfl) ⟨718647, by rfl⟩ : syracuseStep 1916393 = 1437295) B1437295
theorem B33160751 : Blo 1275956 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B4308605 : Blo 1275956 4308605 := bstep (se 3 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 4308605 = 1615727) B1615727
theorem B5825087 : Blo 1275956 5825087 := bstep (se 1 (by rfl) ⟨4368815, by rfl⟩ : syracuseStep 5825087 = 8737631) B8737631
theorem B41444095 : Blo 1275956 41444095 := bstep (se 1 (by rfl) ⟨31083071, by rfl⟩ : syracuseStep 41444095 = 62166143) B62166143
theorem B2156159 : Blo 1275956 2156159 := bstep (se 1 (by rfl) ⟨1617119, by rfl⟩ : syracuseStep 2156159 = 3234239) B3234239
theorem B12273889 : Blo 1275956 12273889 := bstep (se 2 (by rfl) ⟨4602708, by rfl⟩ : syracuseStep 12273889 = 9205417) B9205417
theorem B6466553 : Blo 1275956 6466553 := bstep (se 2 (by rfl) ⟨2424957, by rfl⟩ : syracuseStep 6466553 = 4849915) B4849915
theorem B22107167 : Blo 1275956 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B2872403 : Blo 1275956 2872403 := bstep (se 1 (by rfl) ⟨2154302, by rfl⟩ : syracuseStep 2872403 = 4308605) B4308605
theorem B1914095 : Blo 1275956 1914095 := bstep (se 1 (by rfl) ⟨1435571, by rfl⟩ : syracuseStep 1914095 = 2871143) B2871143
theorem B2045495 : Blo 1275956 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B3635113 : Blo 1275956 3635113 := bstep (se 2 (by rfl) ⟨1363167, by rfl⟩ : syracuseStep 3635113 = 2726335) B2726335
theorem B11066327 : Blo 1275956 11066327 := bstep (se 1 (by rfl) ⟨8299745, by rfl⟩ : syracuseStep 11066327 = 16599491) B16599491
theorem B18668711 : Blo 1275956 18668711 := bstep (se 1 (by rfl) ⟨14001533, by rfl⟩ : syracuseStep 18668711 = 28003067) B28003067
theorem B1916207 : Blo 1275956 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B1277311 : Blo 1275956 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B1277595 : Blo 1275956 1277595 := bstep (se 1 (by rfl) ⟨958196, by rfl⟩ : syracuseStep 1277595 = 1916393) B1916393
theorem B3883391 : Blo 1275956 3883391 := bstep (se 1 (by rfl) ⟨2912543, by rfl⟩ : syracuseStep 3883391 = 5825087) B5825087
theorem B14738111 : Blo 1275956 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B4311035 : Blo 1275956 4311035 := bstep (se 1 (by rfl) ⟨3233276, by rfl⟩ : syracuseStep 4311035 = 6466553) B6466553
theorem B12445807 : Blo 1275956 12445807 := bstep (se 1 (by rfl) ⟨9334355, by rfl⟩ : syracuseStep 12445807 = 18668711) B18668711
theorem B55258793 : Blo 1275956 55258793 := bstep (se 2 (by rfl) ⟨20722047, by rfl⟩ : syracuseStep 55258793 = 41444095) B41444095
theorem B1363663 : Blo 1275956 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B1437439 : Blo 1275956 1437439 := bstep (se 1 (by rfl) ⟨1078079, by rfl⟩ : syracuseStep 1437439 = 2156159) B2156159
theorem B7377551 : Blo 1275956 7377551 := bstep (se 1 (by rfl) ⟨5533163, by rfl⟩ : syracuseStep 7377551 = 11066327) B11066327
theorem B4846817 : Blo 1275956 4846817 := bstep (se 2 (by rfl) ⟨1817556, by rfl⟩ : syracuseStep 4846817 = 3635113) B3635113
theorem B16365185 : Blo 1275956 16365185 := bstep (se 2 (by rfl) ⟨6136944, by rfl⟩ : syracuseStep 16365185 = 12273889) B12273889
theorem B1914935 : Blo 1275956 1914935 := bstep (se 1 (by rfl) ⟨1436201, by rfl⟩ : syracuseStep 1914935 = 2872403) B2872403
theorem B1276063 : Blo 1275956 1276063 := bstep (se 1 (by rfl) ⟨957047, by rfl⟩ : syracuseStep 1276063 = 1914095) B1914095
theorem B1277471 : Blo 1275956 1277471 := bstep (se 1 (by rfl) ⟨958103, by rfl⟩ : syracuseStep 1277471 = 1916207) B1916207
theorem B2588927 : Blo 1275956 2588927 := bstep (se 1 (by rfl) ⟨1941695, by rfl⟩ : syracuseStep 2588927 = 3883391) B3883391
theorem B4918367 : Blo 1275956 4918367 := bstep (se 1 (by rfl) ⟨3688775, by rfl⟩ : syracuseStep 4918367 = 7377551) B7377551
theorem B9825407 : Blo 1275956 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B3231211 : Blo 1275956 3231211 := bstep (se 1 (by rfl) ⟨2423408, by rfl⟩ : syracuseStep 3231211 = 4846817) B4846817
theorem B16594409 : Blo 1275956 16594409 := bstep (se 2 (by rfl) ⟨6222903, by rfl⟩ : syracuseStep 16594409 = 12445807) B12445807
theorem B10910123 : Blo 1275956 10910123 := bstep (se 1 (by rfl) ⟨8182592, by rfl⟩ : syracuseStep 10910123 = 16365185) B16365185
theorem B2874023 : Blo 1275956 2874023 := bstep (se 1 (by rfl) ⟨2155517, by rfl⟩ : syracuseStep 2874023 = 4311035) B4311035
theorem B1276623 : Blo 1275956 1276623 := bstep (se 1 (by rfl) ⟨957467, by rfl⟩ : syracuseStep 1276623 = 1914935) B1914935
theorem B1818217 : Blo 1275956 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B1916585 : Blo 1275956 1916585 := bstep (se 2 (by rfl) ⟨718719, by rfl⟩ : syracuseStep 1916585 = 1437439) B1437439
theorem B36839195 : Blo 1275956 36839195 := bstep (se 1 (by rfl) ⟨27629396, by rfl⟩ : syracuseStep 36839195 = 55258793) B55258793
theorem B13115645 : Blo 1275956 13115645 := bstep (se 3 (by rfl) ⟨2459183, by rfl⟩ : syracuseStep 13115645 = 4918367) B4918367
theorem B11062939 : Blo 1275956 11062939 := bstep (se 1 (by rfl) ⟨8297204, by rfl⟩ : syracuseStep 11062939 = 16594409) B16594409
theorem B6550271 : Blo 1275956 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B9697157 : Blo 1275956 9697157 := bstep (se 4 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 9697157 = 1818217) B1818217
theorem B6903805 : Blo 1275956 6903805 := bstep (se 3 (by rfl) ⟨1294463, by rfl⟩ : syracuseStep 6903805 = 2588927) B2588927
theorem B7273415 : Blo 1275956 7273415 := bstep (se 1 (by rfl) ⟨5455061, by rfl⟩ : syracuseStep 7273415 = 10910123) B10910123
theorem B1916015 : Blo 1275956 1916015 := bstep (se 1 (by rfl) ⟨1437011, by rfl⟩ : syracuseStep 1916015 = 2874023) B2874023
theorem B4308281 : Blo 1275956 4308281 := bstep (se 2 (by rfl) ⟨1615605, by rfl⟩ : syracuseStep 4308281 = 3231211) B3231211
theorem B1277723 : Blo 1275956 1277723 := bstep (se 1 (by rfl) ⟨958292, by rfl⟩ : syracuseStep 1277723 = 1916585) B1916585
theorem B24559463 : Blo 1275956 24559463 := bstep (se 1 (by rfl) ⟨18419597, by rfl⟩ : syracuseStep 24559463 = 36839195) B36839195
theorem B4366847 : Blo 1275956 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B6464771 : Blo 1275956 6464771 := bstep (se 1 (by rfl) ⟨4848578, by rfl⟩ : syracuseStep 6464771 = 9697157) B9697157
theorem B8743763 : Blo 1275956 8743763 := bstep (se 1 (by rfl) ⟨6557822, by rfl⟩ : syracuseStep 8743763 = 13115645) B13115645
theorem B14750585 : Blo 1275956 14750585 := bstep (se 2 (by rfl) ⟨5531469, by rfl⟩ : syracuseStep 14750585 = 11062939) B11062939
theorem B2872187 : Blo 1275956 2872187 := bstep (se 1 (by rfl) ⟨2154140, by rfl⟩ : syracuseStep 2872187 = 4308281) B4308281
theorem B16372975 : Blo 1275956 16372975 := bstep (se 1 (by rfl) ⟨12279731, by rfl⟩ : syracuseStep 16372975 = 24559463) B24559463
theorem B9205073 : Blo 1275956 9205073 := bstep (se 2 (by rfl) ⟨3451902, by rfl⟩ : syracuseStep 9205073 = 6903805) B6903805
theorem B4848943 : Blo 1275956 4848943 := bstep (se 1 (by rfl) ⟨3636707, by rfl⟩ : syracuseStep 4848943 = 7273415) B7273415
theorem B1277343 : Blo 1275956 1277343 := bstep (se 1 (by rfl) ⟨958007, by rfl⟩ : syracuseStep 1277343 = 1916015) B1916015
theorem B4309847 : Blo 1275956 4309847 := bstep (se 1 (by rfl) ⟨3232385, by rfl⟩ : syracuseStep 4309847 = 6464771) B6464771
theorem B6136715 : Blo 1275956 6136715 := bstep (se 1 (by rfl) ⟨4602536, by rfl⟩ : syracuseStep 6136715 = 9205073) B9205073
theorem B6465257 : Blo 1275956 6465257 := bstep (se 2 (by rfl) ⟨2424471, by rfl⟩ : syracuseStep 6465257 = 4848943) B4848943
theorem B2911231 : Blo 1275956 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B9833723 : Blo 1275956 9833723 := bstep (se 1 (by rfl) ⟨7375292, by rfl⟩ : syracuseStep 9833723 = 14750585) B14750585
theorem B5829175 : Blo 1275956 5829175 := bstep (se 1 (by rfl) ⟨4371881, by rfl⟩ : syracuseStep 5829175 = 8743763) B8743763
theorem B1914791 : Blo 1275956 1914791 := bstep (se 1 (by rfl) ⟨1436093, by rfl⟩ : syracuseStep 1914791 = 2872187) B2872187
theorem B21830633 : Blo 1275956 21830633 := bstep (se 2 (by rfl) ⟨8186487, by rfl⟩ : syracuseStep 21830633 = 16372975) B16372975
theorem B4310171 : Blo 1275956 4310171 := bstep (se 1 (by rfl) ⟨3232628, by rfl⟩ : syracuseStep 4310171 = 6465257) B6465257
theorem B6555815 : Blo 1275956 6555815 := bstep (se 1 (by rfl) ⟨4916861, by rfl⟩ : syracuseStep 6555815 = 9833723) B9833723
theorem B4091143 : Blo 1275956 4091143 := bstep (se 1 (by rfl) ⟨3068357, by rfl⟩ : syracuseStep 4091143 = 6136715) B6136715
theorem B14553755 : Blo 1275956 14553755 := bstep (se 1 (by rfl) ⟨10915316, by rfl⟩ : syracuseStep 14553755 = 21830633) B21830633
theorem B2873231 : Blo 1275956 2873231 := bstep (se 1 (by rfl) ⟨2154923, by rfl⟩ : syracuseStep 2873231 = 4309847) B4309847
theorem B7772233 : Blo 1275956 7772233 := bstep (se 2 (by rfl) ⟨2914587, by rfl⟩ : syracuseStep 7772233 = 5829175) B5829175
theorem B1276527 : Blo 1275956 1276527 := bstep (se 1 (by rfl) ⟨957395, by rfl⟩ : syracuseStep 1276527 = 1914791) B1914791
theorem B3881641 : Blo 1275956 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B10362977 : Blo 1275956 10362977 := bstep (se 2 (by rfl) ⟨3886116, by rfl⟩ : syracuseStep 10362977 = 7772233) B7772233
theorem B9702503 : Blo 1275956 9702503 := bstep (se 1 (by rfl) ⟨7276877, by rfl⟩ : syracuseStep 9702503 = 14553755) B14553755
theorem B4370543 : Blo 1275956 4370543 := bstep (se 1 (by rfl) ⟨3277907, by rfl⟩ : syracuseStep 4370543 = 6555815) B6555815
theorem B2873447 : Blo 1275956 2873447 := bstep (se 1 (by rfl) ⟨2155085, by rfl⟩ : syracuseStep 2873447 = 4310171) B4310171
theorem B5175521 : Blo 1275956 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B1915487 : Blo 1275956 1915487 := bstep (se 1 (by rfl) ⟨1436615, by rfl⟩ : syracuseStep 1915487 = 2873231) B2873231
theorem B5454857 : Blo 1275956 5454857 := bstep (se 2 (by rfl) ⟨2045571, by rfl⟩ : syracuseStep 5454857 = 4091143) B4091143
theorem B3450347 : Blo 1275956 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B6908651 : Blo 1275956 6908651 := bstep (se 1 (by rfl) ⟨5181488, by rfl⟩ : syracuseStep 6908651 = 10362977) B10362977
theorem B6468335 : Blo 1275956 6468335 := bstep (se 1 (by rfl) ⟨4851251, by rfl⟩ : syracuseStep 6468335 = 9702503) B9702503
theorem B2913695 : Blo 1275956 2913695 := bstep (se 1 (by rfl) ⟨2185271, by rfl⟩ : syracuseStep 2913695 = 4370543) B4370543
theorem B1915631 : Blo 1275956 1915631 := bstep (se 1 (by rfl) ⟨1436723, by rfl⟩ : syracuseStep 1915631 = 2873447) B2873447
theorem B1276991 : Blo 1275956 1276991 := bstep (se 1 (by rfl) ⟨957743, by rfl⟩ : syracuseStep 1276991 = 1915487) B1915487
theorem B3636571 : Blo 1275956 3636571 := bstep (se 1 (by rfl) ⟨2727428, by rfl⟩ : syracuseStep 3636571 = 5454857) B5454857
theorem B1942463 : Blo 1275956 1942463 := bstep (se 1 (by rfl) ⟨1456847, by rfl⟩ : syracuseStep 1942463 = 2913695) B2913695
theorem B4605767 : Blo 1275956 4605767 := bstep (se 1 (by rfl) ⟨3454325, by rfl⟩ : syracuseStep 4605767 = 6908651) B6908651
theorem B4312223 : Blo 1275956 4312223 := bstep (se 1 (by rfl) ⟨3234167, by rfl⟩ : syracuseStep 4312223 = 6468335) B6468335
theorem B2300231 : Blo 1275956 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B4848761 : Blo 1275956 4848761 := bstep (se 2 (by rfl) ⟨1818285, by rfl⟩ : syracuseStep 4848761 = 3636571) B3636571
theorem B1277087 : Blo 1275956 1277087 := bstep (se 1 (by rfl) ⟨957815, by rfl⟩ : syracuseStep 1277087 = 1915631) B1915631
theorem B1294975 : Blo 1275956 1294975 := bstep (se 1 (by rfl) ⟨971231, by rfl⟩ : syracuseStep 1294975 = 1942463) B1942463
theorem B1533487 : Blo 1275956 1533487 := bstep (se 1 (by rfl) ⟨1150115, by rfl⟩ : syracuseStep 1533487 = 2300231) B2300231
theorem B3232507 : Blo 1275956 3232507 := bstep (se 1 (by rfl) ⟨2424380, by rfl⟩ : syracuseStep 3232507 = 4848761) B4848761
theorem B3070511 : Blo 1275956 3070511 := bstep (se 1 (by rfl) ⟨2302883, by rfl⟩ : syracuseStep 3070511 = 4605767) B4605767
theorem B2874815 : Blo 1275956 2874815 := bstep (se 1 (by rfl) ⟨2156111, by rfl⟩ : syracuseStep 2874815 = 4312223) B4312223
theorem B4310009 : Blo 1275956 4310009 := bstep (se 2 (by rfl) ⟨1616253, by rfl⟩ : syracuseStep 4310009 = 3232507) B3232507
theorem B2044649 : Blo 1275956 2044649 := bstep (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) B1533487
theorem B1726633 : Blo 1275956 1726633 := bstep (se 2 (by rfl) ⟨647487, by rfl⟩ : syracuseStep 1726633 = 1294975) B1294975
theorem B2047007 : Blo 1275956 2047007 := bstep (se 1 (by rfl) ⟨1535255, by rfl⟩ : syracuseStep 2047007 = 3070511) B3070511
theorem B1916543 : Blo 1275956 1916543 := bstep (se 1 (by rfl) ⟨1437407, by rfl⟩ : syracuseStep 1916543 = 2874815) B2874815
theorem B2302177 : Blo 1275956 2302177 := bstep (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) B1726633
theorem B5452397 : Blo 1275956 5452397 := bstep (se 3 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 5452397 = 2044649) B2044649
theorem B1364671 : Blo 1275956 1364671 := bstep (se 1 (by rfl) ⟨1023503, by rfl⟩ : syracuseStep 1364671 = 2047007) B2047007
theorem B2873339 : Blo 1275956 2873339 := bstep (se 1 (by rfl) ⟨2155004, by rfl⟩ : syracuseStep 2873339 = 4310009) B4310009
theorem B1277695 : Blo 1275956 1277695 := bstep (se 1 (by rfl) ⟨958271, by rfl⟩ : syracuseStep 1277695 = 1916543) B1916543
theorem B7278245 : Blo 1275956 7278245 := bstep (se 4 (by rfl) ⟨682335, by rfl⟩ : syracuseStep 7278245 = 1364671) B1364671
theorem B3069569 : Blo 1275956 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B3634931 : Blo 1275956 3634931 := bstep (se 1 (by rfl) ⟨2726198, by rfl⟩ : syracuseStep 3634931 = 5452397) B5452397
theorem B1915559 : Blo 1275956 1915559 := bstep (se 1 (by rfl) ⟨1436669, by rfl⟩ : syracuseStep 1915559 = 2873339) B2873339
theorem B4852163 : Blo 1275956 4852163 := bstep (se 1 (by rfl) ⟨3639122, by rfl⟩ : syracuseStep 4852163 = 7278245) B7278245
theorem B2046379 : Blo 1275956 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B2423287 : Blo 1275956 2423287 := bstep (se 1 (by rfl) ⟨1817465, by rfl⟩ : syracuseStep 2423287 = 3634931) B3634931
theorem B1277039 : Blo 1275956 1277039 := bstep (se 1 (by rfl) ⟨957779, by rfl⟩ : syracuseStep 1277039 = 1915559) B1915559
theorem B2728505 : Blo 1275956 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B3231049 : Blo 1275956 3231049 := bstep (se 2 (by rfl) ⟨1211643, by rfl⟩ : syracuseStep 3231049 = 2423287) B2423287
theorem B3234775 : Blo 1275956 3234775 := bstep (se 1 (by rfl) ⟨2426081, by rfl⟩ : syracuseStep 3234775 = 4852163) B4852163
theorem B7276013 : Blo 1275956 7276013 := bstep (se 3 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 7276013 = 2728505) B2728505
theorem B4313033 : Blo 1275956 4313033 := bstep (se 2 (by rfl) ⟨1617387, by rfl⟩ : syracuseStep 4313033 = 3234775) B3234775
theorem B4308065 : Blo 1275956 4308065 := bstep (se 2 (by rfl) ⟨1615524, by rfl⟩ : syracuseStep 4308065 = 3231049) B3231049
theorem B4850675 : Blo 1275956 4850675 := bstep (se 1 (by rfl) ⟨3638006, by rfl⟩ : syracuseStep 4850675 = 7276013) B7276013
theorem B2872043 : Blo 1275956 2872043 := bstep (se 1 (by rfl) ⟨2154032, by rfl⟩ : syracuseStep 2872043 = 4308065) B4308065
theorem B2875355 : Blo 1275956 2875355 := bstep (se 1 (by rfl) ⟨2156516, by rfl⟩ : syracuseStep 2875355 = 4313033) B4313033
theorem B1914695 : Blo 1275956 1914695 := bstep (se 1 (by rfl) ⟨1436021, by rfl⟩ : syracuseStep 1914695 = 2872043) B2872043
theorem B3233783 : Blo 1275956 3233783 := bstep (se 1 (by rfl) ⟨2425337, by rfl⟩ : syracuseStep 3233783 = 4850675) B4850675
theorem B1916903 : Blo 1275956 1916903 := bstep (se 1 (by rfl) ⟨1437677, by rfl⟩ : syracuseStep 1916903 = 2875355) B2875355
theorem B2155855 : Blo 1275956 2155855 := bstep (se 1 (by rfl) ⟨1616891, by rfl⟩ : syracuseStep 2155855 = 3233783) B3233783
theorem B1276463 : Blo 1275956 1276463 := bstep (se 1 (by rfl) ⟨957347, by rfl⟩ : syracuseStep 1276463 = 1914695) B1914695
theorem B1277935 : Blo 1275956 1277935 := bstep (se 1 (by rfl) ⟨958451, by rfl⟩ : syracuseStep 1277935 = 1916903) B1916903
theorem B2874473 : Blo 1275956 2874473 := bstep (se 2 (by rfl) ⟨1077927, by rfl⟩ : syracuseStep 2874473 = 2155855) B2155855
theorem B1916315 : Blo 1275956 1916315 := bstep (se 1 (by rfl) ⟨1437236, by rfl⟩ : syracuseStep 1916315 = 2874473) B2874473
theorem B1277543 : Blo 1275956 1277543 := bstep (se 1 (by rfl) ⟨958157, by rfl⟩ : syracuseStep 1277543 = 1916315) B1916315

theorem C0 (j : ℕ) (h1 : 318989 ≤ j) (h2 : j ≤ 319488) : Blo 1275956 (4 * j + 3) := by
  interval_cases j
  · exact B1275959
  · exact B1275963
  · exact B1275967
  · exact B1275971
  · exact B1275975
  · exact B1275979
  · exact B1275983
  · exact B1275987
  · exact B1275991
  · exact B1275995
  · exact B1275999
  · exact B1276003
  · exact B1276007
  · exact B1276011
  · exact B1276015
  · exact B1276019
  · exact B1276023
  · exact B1276027
  · exact B1276031
  · exact B1276035
  · exact B1276039
  · exact B1276043
  · exact B1276047
  · exact B1276051
  · exact B1276055
  · exact B1276059
  · exact B1276063
  · exact B1276067
  · exact B1276071
  · exact B1276075
  · exact B1276079
  · exact B1276083
  · exact B1276087
  · exact B1276091
  · exact B1276095
  · exact B1276099
  · exact B1276103
  · exact B1276107
  · exact B1276111
  · exact B1276115
  · exact B1276119
  · exact B1276123
  · exact B1276127
  · exact B1276131
  · exact B1276135
  · exact B1276139
  · exact B1276143
  · exact B1276147
  · exact B1276151
  · exact B1276155
  · exact B1276159
  · exact B1276163
  · exact B1276167
  · exact B1276171
  · exact B1276175
  · exact B1276179
  · exact B1276183
  · exact B1276187
  · exact B1276191
  · exact B1276195
  · exact B1276199
  · exact B1276203
  · exact B1276207
  · exact B1276211
  · exact B1276215
  · exact B1276219
  · exact B1276223
  · exact B1276227
  · exact B1276231
  · exact B1276235
  · exact B1276239
  · exact B1276243
  · exact B1276247
  · exact B1276251
  · exact B1276255
  · exact B1276259
  · exact B1276263
  · exact B1276267
  · exact B1276271
  · exact B1276275
  · exact B1276279
  · exact B1276283
  · exact B1276287
  · exact B1276291
  · exact B1276295
  · exact B1276299
  · exact B1276303
  · exact B1276307
  · exact B1276311
  · exact B1276315
  · exact B1276319
  · exact B1276323
  · exact B1276327
  · exact B1276331
  · exact B1276335
  · exact B1276339
  · exact B1276343
  · exact B1276347
  · exact B1276351
  · exact B1276355
  · exact B1276359
  · exact B1276363
  · exact B1276367
  · exact B1276371
  · exact B1276375
  · exact B1276379
  · exact B1276383
  · exact B1276387
  · exact B1276391
  · exact B1276395
  · exact B1276399
  · exact B1276403
  · exact B1276407
  · exact B1276411
  · exact B1276415
  · exact B1276419
  · exact B1276423
  · exact B1276427
  · exact B1276431
  · exact B1276435
  · exact B1276439
  · exact B1276443
  · exact B1276447
  · exact B1276451
  · exact B1276455
  · exact B1276459
  · exact B1276463
  · exact B1276467
  · exact B1276471
  · exact B1276475
  · exact B1276479
  · exact B1276483
  · exact B1276487
  · exact B1276491
  · exact B1276495
  · exact B1276499
  · exact B1276503
  · exact B1276507
  · exact B1276511
  · exact B1276515
  · exact B1276519
  · exact B1276523
  · exact B1276527
  · exact B1276531
  · exact B1276535
  · exact B1276539
  · exact B1276543
  · exact B1276547
  · exact B1276551
  · exact B1276555
  · exact B1276559
  · exact B1276563
  · exact B1276567
  · exact B1276571
  · exact B1276575
  · exact B1276579
  · exact B1276583
  · exact B1276587
  · exact B1276591
  · exact B1276595
  · exact B1276599
  · exact B1276603
  · exact B1276607
  · exact B1276611
  · exact B1276615
  · exact B1276619
  · exact B1276623
  · exact B1276627
  · exact B1276631
  · exact B1276635
  · exact B1276639
  · exact B1276643
  · exact B1276647
  · exact B1276651
  · exact B1276655
  · exact B1276659
  · exact B1276663
  · exact B1276667
  · exact B1276671
  · exact B1276675
  · exact B1276679
  · exact B1276683
  · exact B1276687
  · exact B1276691
  · exact B1276695
  · exact B1276699
  · exact B1276703
  · exact B1276707
  · exact B1276711
  · exact B1276715
  · exact B1276719
  · exact B1276723
  · exact B1276727
  · exact B1276731
  · exact B1276735
  · exact B1276739
  · exact B1276743
  · exact B1276747
  · exact B1276751
  · exact B1276755
  · exact B1276759
  · exact B1276763
  · exact B1276767
  · exact B1276771
  · exact B1276775
  · exact B1276779
  · exact B1276783
  · exact B1276787
  · exact B1276791
  · exact B1276795
  · exact B1276799
  · exact B1276803
  · exact B1276807
  · exact B1276811
  · exact B1276815
  · exact B1276819
  · exact B1276823
  · exact B1276827
  · exact B1276831
  · exact B1276835
  · exact B1276839
  · exact B1276843
  · exact B1276847
  · exact B1276851
  · exact B1276855
  · exact B1276859
  · exact B1276863
  · exact B1276867
  · exact B1276871
  · exact B1276875
  · exact B1276879
  · exact B1276883
  · exact B1276887
  · exact B1276891
  · exact B1276895
  · exact B1276899
  · exact B1276903
  · exact B1276907
  · exact B1276911
  · exact B1276915
  · exact B1276919
  · exact B1276923
  · exact B1276927
  · exact B1276931
  · exact B1276935
  · exact B1276939
  · exact B1276943
  · exact B1276947
  · exact B1276951
  · exact B1276955
  · exact B1276959
  · exact B1276963
  · exact B1276967
  · exact B1276971
  · exact B1276975
  · exact B1276979
  · exact B1276983
  · exact B1276987
  · exact B1276991
  · exact B1276995
  · exact B1276999
  · exact B1277003
  · exact B1277007
  · exact B1277011
  · exact B1277015
  · exact B1277019
  · exact B1277023
  · exact B1277027
  · exact B1277031
  · exact B1277035
  · exact B1277039
  · exact B1277043
  · exact B1277047
  · exact B1277051
  · exact B1277055
  · exact B1277059
  · exact B1277063
  · exact B1277067
  · exact B1277071
  · exact B1277075
  · exact B1277079
  · exact B1277083
  · exact B1277087
  · exact B1277091
  · exact B1277095
  · exact B1277099
  · exact B1277103
  · exact B1277107
  · exact B1277111
  · exact B1277115
  · exact B1277119
  · exact B1277123
  · exact B1277127
  · exact B1277131
  · exact B1277135
  · exact B1277139
  · exact B1277143
  · exact B1277147
  · exact B1277151
  · exact B1277155
  · exact B1277159
  · exact B1277163
  · exact B1277167
  · exact B1277171
  · exact B1277175
  · exact B1277179
  · exact B1277183
  · exact B1277187
  · exact B1277191
  · exact B1277195
  · exact B1277199
  · exact B1277203
  · exact B1277207
  · exact B1277211
  · exact B1277215
  · exact B1277219
  · exact B1277223
  · exact B1277227
  · exact B1277231
  · exact B1277235
  · exact B1277239
  · exact B1277243
  · exact B1277247
  · exact B1277251
  · exact B1277255
  · exact B1277259
  · exact B1277263
  · exact B1277267
  · exact B1277271
  · exact B1277275
  · exact B1277279
  · exact B1277283
  · exact B1277287
  · exact B1277291
  · exact B1277295
  · exact B1277299
  · exact B1277303
  · exact B1277307
  · exact B1277311
  · exact B1277315
  · exact B1277319
  · exact B1277323
  · exact B1277327
  · exact B1277331
  · exact B1277335
  · exact B1277339
  · exact B1277343
  · exact B1277347
  · exact B1277351
  · exact B1277355
  · exact B1277359
  · exact B1277363
  · exact B1277367
  · exact B1277371
  · exact B1277375
  · exact B1277379
  · exact B1277383
  · exact B1277387
  · exact B1277391
  · exact B1277395
  · exact B1277399
  · exact B1277403
  · exact B1277407
  · exact B1277411
  · exact B1277415
  · exact B1277419
  · exact B1277423
  · exact B1277427
  · exact B1277431
  · exact B1277435
  · exact B1277439
  · exact B1277443
  · exact B1277447
  · exact B1277451
  · exact B1277455
  · exact B1277459
  · exact B1277463
  · exact B1277467
  · exact B1277471
  · exact B1277475
  · exact B1277479
  · exact B1277483
  · exact B1277487
  · exact B1277491
  · exact B1277495
  · exact B1277499
  · exact B1277503
  · exact B1277507
  · exact B1277511
  · exact B1277515
  · exact B1277519
  · exact B1277523
  · exact B1277527
  · exact B1277531
  · exact B1277535
  · exact B1277539
  · exact B1277543
  · exact B1277547
  · exact B1277551
  · exact B1277555
  · exact B1277559
  · exact B1277563
  · exact B1277567
  · exact B1277571
  · exact B1277575
  · exact B1277579
  · exact B1277583
  · exact B1277587
  · exact B1277591
  · exact B1277595
  · exact B1277599
  · exact B1277603
  · exact B1277607
  · exact B1277611
  · exact B1277615
  · exact B1277619
  · exact B1277623
  · exact B1277627
  · exact B1277631
  · exact B1277635
  · exact B1277639
  · exact B1277643
  · exact B1277647
  · exact B1277651
  · exact B1277655
  · exact B1277659
  · exact B1277663
  · exact B1277667
  · exact B1277671
  · exact B1277675
  · exact B1277679
  · exact B1277683
  · exact B1277687
  · exact B1277691
  · exact B1277695
  · exact B1277699
  · exact B1277703
  · exact B1277707
  · exact B1277711
  · exact B1277715
  · exact B1277719
  · exact B1277723
  · exact B1277727
  · exact B1277731
  · exact B1277735
  · exact B1277739
  · exact B1277743
  · exact B1277747
  · exact B1277751
  · exact B1277755
  · exact B1277759
  · exact B1277763
  · exact B1277767
  · exact B1277771
  · exact B1277775
  · exact B1277779
  · exact B1277783
  · exact B1277787
  · exact B1277791
  · exact B1277795
  · exact B1277799
  · exact B1277803
  · exact B1277807
  · exact B1277811
  · exact B1277815
  · exact B1277819
  · exact B1277823
  · exact B1277827
  · exact B1277831
  · exact B1277835
  · exact B1277839
  · exact B1277843
  · exact B1277847
  · exact B1277851
  · exact B1277855
  · exact B1277859
  · exact B1277863
  · exact B1277867
  · exact B1277871
  · exact B1277875
  · exact B1277879
  · exact B1277883
  · exact B1277887
  · exact B1277891
  · exact B1277895
  · exact B1277899
  · exact B1277903
  · exact B1277907
  · exact B1277911
  · exact B1277915
  · exact B1277919
  · exact B1277923
  · exact B1277927
  · exact B1277931
  · exact B1277935
  · exact B1277939
  · exact B1277943
  · exact B1277947
  · exact B1277951
  · exact B1277955

theorem solution (m : ℕ) (hlo : 1275956 ≤ m) (hhi : m ≤ 1277956) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 318989 ≤ j := by omega
    have hj2 : j ≤ 319488 := by omega
    have hb : Blo 1275956 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
