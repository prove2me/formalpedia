-- Prove2me | solution 1 for syracuse_descends_range_1036608_1040608
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:23.200187+00:00
-- url     : https://prove2.me/submissions/4286473e-d189-47b2-9fdb-981450b12455

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


theorem B9469973 : Blo 1036608 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B1802549 : Blo 1036608 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B14975381 : Blo 1036608 14975381 := bbase (se 6 (by rfl) ⟨350985, by rfl⟩ : syracuseStep 14975381 = 701971) (by norm_num)
theorem B3506597 : Blo 1036608 3506597 := bbase (se 4 (by rfl) ⟨328743, by rfl⟩ : syracuseStep 3506597 = 657487) (by norm_num)
theorem B1999421 : Blo 1036608 1999421 := bbase (se 3 (by rfl) ⟨374891, by rfl⟩ : syracuseStep 1999421 = 749783) (by norm_num)
theorem B8422069 : Blo 1036608 8422069 := bbase (se 5 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 8422069 = 789569) (by norm_num)
theorem B3507029 : Blo 1036608 3507029 := bbase (se 9 (by rfl) ⟨10274, by rfl⟩ : syracuseStep 3507029 = 20549) (by norm_num)
theorem B1311977 : Blo 1036608 1311977 := bbase (se 2 (by rfl) ⟨491991, by rfl⟩ : syracuseStep 1311977 = 983983) (by norm_num)
theorem B3507461 : Blo 1036608 3507461 := bbase (se 4 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 3507461 = 657649) (by norm_num)
theorem B1312033 : Blo 1036608 1312033 := bbase (se 2 (by rfl) ⟨492012, by rfl⟩ : syracuseStep 1312033 = 984025) (by norm_num)
theorem B1312129 : Blo 1036608 1312129 := bbase (se 2 (by rfl) ⟨492048, by rfl⟩ : syracuseStep 1312129 = 984097) (by norm_num)
theorem B2491813 : Blo 1036608 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B3737029 : Blo 1036608 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B1246757 : Blo 1036608 1246757 := bbase (se 4 (by rfl) ⟨116883, by rfl⟩ : syracuseStep 1246757 = 233767) (by norm_num)
theorem B1312301 : Blo 1036608 1312301 := bbase (se 3 (by rfl) ⟨246056, by rfl⟩ : syracuseStep 1312301 = 492113) (by norm_num)
theorem B1476157 : Blo 1036608 1476157 := bbase (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) (by norm_num)
theorem B1312357 : Blo 1036608 1312357 := bbase (se 4 (by rfl) ⟨123033, by rfl⟩ : syracuseStep 1312357 = 246067) (by norm_num)
theorem B1869437 : Blo 1036608 1869437 := bbase (se 3 (by rfl) ⟨350519, by rfl⟩ : syracuseStep 1869437 = 701039) (by norm_num)
theorem B3507893 : Blo 1036608 3507893 := bbase (se 5 (by rfl) ⟨164432, by rfl⟩ : syracuseStep 3507893 = 328865) (by norm_num)
theorem B1312453 : Blo 1036608 1312453 := bbase (se 4 (by rfl) ⟨123042, by rfl⟩ : syracuseStep 1312453 = 246085) (by norm_num)
theorem B1312625 : Blo 1036608 1312625 := bbase (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) (by norm_num)
theorem B1967989 : Blo 1036608 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B1312681 : Blo 1036608 1312681 := bbase (se 2 (by rfl) ⟨492255, by rfl⟩ : syracuseStep 1312681 = 984511) (by norm_num)
theorem B1968133 : Blo 1036608 1968133 := bbase (se 4 (by rfl) ⟨184512, by rfl⟩ : syracuseStep 1968133 = 369025) (by norm_num)
theorem B1312777 : Blo 1036608 1312777 := bbase (se 2 (by rfl) ⟨492291, by rfl⟩ : syracuseStep 1312777 = 984583) (by norm_num)
theorem B2492477 : Blo 1036608 2492477 := bbase (se 3 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 2492477 = 934679) (by norm_num)
theorem B3508325 : Blo 1036608 3508325 := bbase (se 4 (by rfl) ⟨328905, by rfl⟩ : syracuseStep 3508325 = 657811) (by norm_num)
theorem B1476749 : Blo 1036608 1476749 := bbase (se 3 (by rfl) ⟨276890, by rfl⟩ : syracuseStep 1476749 = 553781) (by norm_num)
theorem B1968293 : Blo 1036608 1968293 := bbase (se 4 (by rfl) ⟨184527, by rfl⟩ : syracuseStep 1968293 = 369055) (by norm_num)
theorem B1312949 : Blo 1036608 1312949 := bbase (se 5 (by rfl) ⟨61544, by rfl⟩ : syracuseStep 1312949 = 123089) (by norm_num)
theorem B10651829 : Blo 1036608 10651829 := bbase (se 5 (by rfl) ⟨499304, by rfl⟩ : syracuseStep 10651829 = 998609) (by norm_num)
theorem B1247449 : Blo 1036608 1247449 := bbase (se 2 (by rfl) ⟨467793, by rfl⟩ : syracuseStep 1247449 = 935587) (by norm_num)
theorem B1476829 : Blo 1036608 1476829 := bbase (se 3 (by rfl) ⟨276905, by rfl⟩ : syracuseStep 1476829 = 553811) (by norm_num)
theorem B1313005 : Blo 1036608 1313005 := bbase (se 3 (by rfl) ⟨246188, by rfl⟩ : syracuseStep 1313005 = 492377) (by norm_num)
theorem B4983029 : Blo 1036608 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B1968437 : Blo 1036608 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B1247545 : Blo 1036608 1247545 := bbase (se 2 (by rfl) ⟨467829, by rfl⟩ : syracuseStep 1247545 = 935659) (by norm_num)
theorem B1313101 : Blo 1036608 1313101 := bbase (se 3 (by rfl) ⟨246206, by rfl⟩ : syracuseStep 1313101 = 492413) (by norm_num)
theorem B1476949 : Blo 1036608 1476949 := bbase (se 10 (by rfl) ⟨2163, by rfl⟩ : syracuseStep 1476949 = 4327) (by norm_num)
theorem B2492765 : Blo 1036608 2492765 := bbase (se 3 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 2492765 = 934787) (by norm_num)
theorem B1477045 : Blo 1036608 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B1313273 : Blo 1036608 1313273 := bbase (se 2 (by rfl) ⟨492477, by rfl⟩ : syracuseStep 1313273 = 984955) (by norm_num)
theorem B2132477 : Blo 1036608 2132477 := bbase (se 3 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 2132477 = 799679) (by norm_num)
theorem B3508757 : Blo 1036608 3508757 := bbase (se 6 (by rfl) ⟨82236, by rfl⟩ : syracuseStep 3508757 = 164473) (by norm_num)
theorem B2001437 : Blo 1036608 2001437 := bbase (se 3 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 2001437 = 750539) (by norm_num)
theorem B1870381 : Blo 1036608 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B1313329 : Blo 1036608 1313329 := bbase (se 2 (by rfl) ⟨492498, by rfl⟩ : syracuseStep 1313329 = 984997) (by norm_num)
theorem B1051205 : Blo 1036608 1051205 := bbase (se 4 (by rfl) ⟨98550, by rfl⟩ : syracuseStep 1051205 = 197101) (by norm_num)
theorem B1968725 : Blo 1036608 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B1313425 : Blo 1036608 1313425 := bbase (se 2 (by rfl) ⟨492534, by rfl⟩ : syracuseStep 1313425 = 985069) (by norm_num)
theorem B2624197 : Blo 1036608 2624197 := bbase (se 4 (by rfl) ⟨246018, by rfl⟩ : syracuseStep 2624197 = 492037) (by norm_num)
theorem B1968877 : Blo 1036608 1968877 := bbase (se 3 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 1968877 = 738329) (by norm_num)
theorem B2624309 : Blo 1036608 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B4000565 : Blo 1036608 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B1313597 : Blo 1036608 1313597 := bbase (se 3 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 1313597 = 492599) (by norm_num)
theorem B1182533 : Blo 1036608 1182533 := bbase (se 4 (by rfl) ⟨110862, by rfl⟩ : syracuseStep 1182533 = 221725) (by norm_num)
theorem B1313653 : Blo 1036608 1313653 := bbase (se 5 (by rfl) ⟨61577, by rfl⟩ : syracuseStep 1313653 = 123155) (by norm_num)
theorem B1477541 : Blo 1036608 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B3509189 : Blo 1036608 3509189 := bbase (se 4 (by rfl) ⟨328986, by rfl⟩ : syracuseStep 3509189 = 657973) (by norm_num)
theorem B1313749 : Blo 1036608 1313749 := bbase (se 7 (by rfl) ⟨15395, by rfl⟩ : syracuseStep 1313749 = 30791) (by norm_num)
theorem B2624501 : Blo 1036608 2624501 := bbase (se 5 (by rfl) ⟨123023, by rfl⟩ : syracuseStep 2624501 = 246047) (by norm_num)
theorem B1969181 : Blo 1036608 1969181 := bbase (se 3 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 1969181 = 738443) (by norm_num)
theorem B1870885 : Blo 1036608 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B1248329 : Blo 1036608 1248329 := bbase (se 2 (by rfl) ⟨468123, by rfl⟩ : syracuseStep 1248329 = 936247) (by norm_num)
theorem B1051753 : Blo 1036608 1051753 := bbase (se 2 (by rfl) ⟨394407, by rfl⟩ : syracuseStep 1051753 = 788815) (by norm_num)
theorem B1313921 : Blo 1036608 1313921 := bbase (se 2 (by rfl) ⟨492720, by rfl⟩ : syracuseStep 1313921 = 985441) (by norm_num)
theorem B2526365 : Blo 1036608 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B1313977 : Blo 1036608 1313977 := bbase (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) (by norm_num)
theorem B1314073 : Blo 1036608 1314073 := bbase (se 2 (by rfl) ⟨492777, by rfl⟩ : syracuseStep 1314073 = 985555) (by norm_num)
theorem B2624845 : Blo 1036608 2624845 := bbase (se 3 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 2624845 = 984317) (by norm_num)
theorem B1183081 : Blo 1036608 1183081 := bbase (se 2 (by rfl) ⟨443655, by rfl⟩ : syracuseStep 1183081 = 887311) (by norm_num)
theorem B3509621 : Blo 1036608 3509621 := bbase (se 5 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 3509621 = 329027) (by norm_num)
theorem B1248637 : Blo 1036608 1248637 := bbase (se 3 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 1248637 = 468239) (by norm_num)
theorem B2624957 : Blo 1036608 2624957 := bbase (se 3 (by rfl) ⟨492179, by rfl⟩ : syracuseStep 2624957 = 984359) (by norm_num)
theorem B1314245 : Blo 1036608 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B1478093 : Blo 1036608 1478093 := bbase (se 3 (by rfl) ⟨277142, by rfl⟩ : syracuseStep 1478093 = 554285) (by norm_num)
theorem B7114229 : Blo 1036608 7114229 := bbase (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) (by norm_num)
theorem B1314301 : Blo 1036608 1314301 := bbase (se 3 (by rfl) ⟨246431, by rfl⟩ : syracuseStep 1314301 = 492863) (by norm_num)
theorem B1576493 : Blo 1036608 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B1314397 : Blo 1036608 1314397 := bbase (se 3 (by rfl) ⟨246449, by rfl⟩ : syracuseStep 1314397 = 492899) (by norm_num)
theorem B2625149 : Blo 1036608 2625149 := bbase (se 3 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 2625149 = 984431) (by norm_num)
theorem B1052357 : Blo 1036608 1052357 := bbase (se 4 (by rfl) ⟨98658, by rfl⟩ : syracuseStep 1052357 = 197317) (by norm_num)
theorem B2526949 : Blo 1036608 2526949 := bbase (se 4 (by rfl) ⟨236901, by rfl⟩ : syracuseStep 2526949 = 473803) (by norm_num)
theorem B1249025 : Blo 1036608 1249025 := bbase (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) (by norm_num)
theorem B1314569 : Blo 1036608 1314569 := bbase (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) (by norm_num)
theorem B1969933 : Blo 1036608 1969933 := bbase (se 3 (by rfl) ⟨369362, by rfl⟩ : syracuseStep 1969933 = 738725) (by norm_num)
theorem B3510053 : Blo 1036608 3510053 := bbase (se 4 (by rfl) ⟨329067, by rfl⟩ : syracuseStep 3510053 = 658135) (by norm_num)
theorem B3936053 : Blo 1036608 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B1314625 : Blo 1036608 1314625 := bbase (se 2 (by rfl) ⟨492984, by rfl⟩ : syracuseStep 1314625 = 985969) (by norm_num)
theorem B1871765 : Blo 1036608 1871765 := bbase (se 6 (by rfl) ⟨43869, by rfl⟩ : syracuseStep 1871765 = 87739) (by norm_num)
theorem B1970077 : Blo 1036608 1970077 := bbase (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) (by norm_num)
theorem B1314721 : Blo 1036608 1314721 := bbase (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) (by norm_num)
theorem B2625493 : Blo 1036608 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B29921237 : Blo 1036608 29921237 := bbase (se 7 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 29921237 = 701279) (by norm_num)
theorem B1970237 : Blo 1036608 1970237 := bbase (se 3 (by rfl) ⟨369419, by rfl⟩ : syracuseStep 1970237 = 738839) (by norm_num)
theorem B2625605 : Blo 1036608 2625605 := bbase (se 4 (by rfl) ⟨246150, by rfl⟩ : syracuseStep 2625605 = 492301) (by norm_num)
theorem B1314893 : Blo 1036608 1314893 := bbase (se 3 (by rfl) ⟨246542, by rfl⟩ : syracuseStep 1314893 = 493085) (by norm_num)
theorem B1249381 : Blo 1036608 1249381 := bbase (se 4 (by rfl) ⟨117129, by rfl⟩ : syracuseStep 1249381 = 234259) (by norm_num)
theorem B1314949 : Blo 1036608 1314949 := bbase (se 4 (by rfl) ⟨123276, by rfl⟩ : syracuseStep 1314949 = 246553) (by norm_num)
theorem B9965749 : Blo 1036608 9965749 := bbase (se 5 (by rfl) ⟨467144, by rfl⟩ : syracuseStep 9965749 = 934289) (by norm_num)
theorem B1478845 : Blo 1036608 1478845 := bbase (se 3 (by rfl) ⟨277283, by rfl⟩ : syracuseStep 1478845 = 554567) (by norm_num)
theorem B1970381 : Blo 1036608 1970381 := bbase (se 3 (by rfl) ⟨369446, by rfl⟩ : syracuseStep 1970381 = 738893) (by norm_num)
theorem B8523989 : Blo 1036608 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B3510485 : Blo 1036608 3510485 := bbase (se 7 (by rfl) ⟨41138, by rfl⟩ : syracuseStep 3510485 = 82277) (by norm_num)
theorem B1315045 : Blo 1036608 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B2625797 : Blo 1036608 2625797 := bbase (se 4 (by rfl) ⟨246168, by rfl⟩ : syracuseStep 2625797 = 492337) (by norm_num)
theorem B3739925 : Blo 1036608 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B2494813 : Blo 1036608 2494813 := bbase (se 3 (by rfl) ⟨467777, by rfl⟩ : syracuseStep 2494813 = 935555) (by norm_num)
theorem B4985221 : Blo 1036608 4985221 := bbase (se 4 (by rfl) ⟨467364, by rfl⟩ : syracuseStep 4985221 = 934729) (by norm_num)
theorem B1773965 : Blo 1036608 1773965 := bbase (se 3 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 1773965 = 665237) (by norm_num)
theorem B1872269 : Blo 1036608 1872269 := bbase (se 3 (by rfl) ⟨351050, by rfl⟩ : syracuseStep 1872269 = 702101) (by norm_num)
theorem B1315217 : Blo 1036608 1315217 := bbase (se 2 (by rfl) ⟨493206, by rfl⟩ : syracuseStep 1315217 = 986413) (by norm_num)
theorem B1249717 : Blo 1036608 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B1315273 : Blo 1036608 1315273 := bbase (se 2 (by rfl) ⟨493227, by rfl⟩ : syracuseStep 1315273 = 986455) (by norm_num)
theorem B1970669 : Blo 1036608 1970669 := bbase (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) (by norm_num)
theorem B1315369 : Blo 1036608 1315369 := bbase (se 2 (by rfl) ⟨493263, by rfl⟩ : syracuseStep 1315369 = 986527) (by norm_num)
theorem B1053257 : Blo 1036608 1053257 := bbase (se 2 (by rfl) ⟨394971, by rfl⟩ : syracuseStep 1053257 = 789943) (by norm_num)
theorem B2626141 : Blo 1036608 2626141 := bbase (se 3 (by rfl) ⟨492401, by rfl⟩ : syracuseStep 2626141 = 984803) (by norm_num)
theorem B1053281 : Blo 1036608 1053281 := bbase (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) (by norm_num)
theorem B1970821 : Blo 1036608 1970821 := bbase (se 4 (by rfl) ⟨184764, by rfl⟩ : syracuseStep 1970821 = 369529) (by norm_num)
theorem B3510917 : Blo 1036608 3510917 := bbase (se 4 (by rfl) ⟨329148, by rfl⟩ : syracuseStep 3510917 = 658297) (by norm_num)
theorem B2626253 : Blo 1036608 2626253 := bbase (se 3 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 2626253 = 984845) (by norm_num)
theorem B1315541 : Blo 1036608 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B1315597 : Blo 1036608 1315597 := bbase (se 3 (by rfl) ⟨246674, by rfl⟩ : syracuseStep 1315597 = 493349) (by norm_num)
theorem B1315693 : Blo 1036608 1315693 := bbase (se 3 (by rfl) ⟨246692, by rfl⟩ : syracuseStep 1315693 = 493385) (by norm_num)
theorem B2626445 : Blo 1036608 2626445 := bbase (se 3 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 2626445 = 984917) (by norm_num)
theorem B1971125 : Blo 1036608 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B1774541 : Blo 1036608 1774541 := bbase (se 3 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 1774541 = 665453) (by norm_num)
theorem B1479637 : Blo 1036608 1479637 := bbase (se 7 (by rfl) ⟨17339, by rfl⟩ : syracuseStep 1479637 = 34679) (by norm_num)
theorem B5247989 : Blo 1036608 5247989 := bbase (se 5 (by rfl) ⟨245999, by rfl⟩ : syracuseStep 5247989 = 491999) (by norm_num)
theorem B1315865 : Blo 1036608 1315865 := bbase (se 2 (by rfl) ⟨493449, by rfl⟩ : syracuseStep 1315865 = 986899) (by norm_num)
theorem B3511349 : Blo 1036608 3511349 := bbase (se 5 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 3511349 = 329189) (by norm_num)
theorem B1315921 : Blo 1036608 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B1316017 : Blo 1036608 1316017 := bbase (se 2 (by rfl) ⟨493506, by rfl⟩ : syracuseStep 1316017 = 987013) (by norm_num)
theorem B2626789 : Blo 1036608 2626789 := bbase (se 4 (by rfl) ⟨246261, by rfl⟩ : syracuseStep 2626789 = 492523) (by norm_num)
theorem B2954501 : Blo 1036608 2954501 := bbase (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) (by norm_num)
theorem B1479973 : Blo 1036608 1479973 := bbase (se 4 (by rfl) ⟨138747, by rfl⟩ : syracuseStep 1479973 = 277495) (by norm_num)
theorem B1578293 : Blo 1036608 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B1774909 : Blo 1036608 1774909 := bbase (se 3 (by rfl) ⟨332795, by rfl⟩ : syracuseStep 1774909 = 665591) (by norm_num)
theorem B2626901 : Blo 1036608 2626901 := bbase (se 14 (by rfl) ⟨240, by rfl⟩ : syracuseStep 2626901 = 481) (by norm_num)
theorem B6657365 : Blo 1036608 6657365 := bbase (se 14 (by rfl) ⟨609, by rfl⟩ : syracuseStep 6657365 = 1219) (by norm_num)
theorem B1316189 : Blo 1036608 1316189 := bbase (se 3 (by rfl) ⟨246785, by rfl⟩ : syracuseStep 1316189 = 493571) (by norm_num)
theorem B1316245 : Blo 1036608 1316245 := bbase (se 6 (by rfl) ⟨30849, by rfl⟩ : syracuseStep 1316245 = 61699) (by norm_num)
theorem B16848341 : Blo 1036608 16848341 := bbase (se 7 (by rfl) ⟨197441, by rfl⟩ : syracuseStep 16848341 = 394883) (by norm_num)
theorem B3511781 : Blo 1036608 3511781 := bbase (se 4 (by rfl) ⟨329229, by rfl⟩ : syracuseStep 3511781 = 658459) (by norm_num)
theorem B1316341 : Blo 1036608 1316341 := bbase (se 5 (by rfl) ⟨61703, by rfl⟩ : syracuseStep 1316341 = 123407) (by norm_num)
theorem B1480189 : Blo 1036608 1480189 := bbase (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) (by norm_num)
theorem B2627093 : Blo 1036608 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B2365013 : Blo 1036608 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B1316513 : Blo 1036608 1316513 := bbase (se 2 (by rfl) ⟨493692, by rfl⟩ : syracuseStep 1316513 = 987385) (by norm_num)
theorem B1971877 : Blo 1036608 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B1316569 : Blo 1036608 1316569 := bbase (se 2 (by rfl) ⟨493713, by rfl⟩ : syracuseStep 1316569 = 987427) (by norm_num)
theorem B2332421 : Blo 1036608 2332421 := bbase (se 4 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 2332421 = 437329) (by norm_num)
theorem B2660125 : Blo 1036608 2660125 := bbase (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) (by norm_num)
theorem B1972021 : Blo 1036608 1972021 := bbase (se 5 (by rfl) ⟨92438, by rfl⟩ : syracuseStep 1972021 = 184877) (by norm_num)
theorem B1316665 : Blo 1036608 1316665 := bbase (se 2 (by rfl) ⟨493749, by rfl⟩ : syracuseStep 1316665 = 987499) (by norm_num)
theorem B2332493 : Blo 1036608 2332493 := bbase (se 3 (by rfl) ⟨437342, by rfl⟩ : syracuseStep 2332493 = 874685) (by norm_num)
theorem B2627437 : Blo 1036608 2627437 := bbase (se 3 (by rfl) ⟨492644, by rfl⟩ : syracuseStep 2627437 = 985289) (by norm_num)
theorem B3938165 : Blo 1036608 3938165 := bbase (se 5 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 3938165 = 369203) (by norm_num)
theorem B1480565 : Blo 1036608 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B2332565 : Blo 1036608 2332565 := bbase (se 6 (by rfl) ⟨54669, by rfl⟩ : syracuseStep 2332565 = 109339) (by norm_num)
theorem B1972181 : Blo 1036608 1972181 := bbase (se 7 (by rfl) ⟨23111, by rfl⟩ : syracuseStep 1972181 = 46223) (by norm_num)
theorem B2332637 : Blo 1036608 2332637 := bbase (se 3 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 2332637 = 874739) (by norm_num)
theorem B2627549 : Blo 1036608 2627549 := bbase (se 3 (by rfl) ⟨492665, by rfl⟩ : syracuseStep 2627549 = 985331) (by norm_num)
theorem B1316837 : Blo 1036608 1316837 := bbase (se 4 (by rfl) ⟨123453, by rfl⟩ : syracuseStep 1316837 = 246907) (by norm_num)
theorem B1185817 : Blo 1036608 1185817 := bbase (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) (by norm_num)
theorem B1316893 : Blo 1036608 1316893 := bbase (se 3 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 1316893 = 493835) (by norm_num)
theorem B2332709 : Blo 1036608 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B1972325 : Blo 1036608 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B2332781 : Blo 1036608 2332781 := bbase (se 3 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 2332781 = 874793) (by norm_num)
theorem B1316989 : Blo 1036608 1316989 := bbase (se 3 (by rfl) ⟨246935, by rfl⟩ : syracuseStep 1316989 = 493871) (by norm_num)
theorem B3938453 : Blo 1036608 3938453 := bbase (se 6 (by rfl) ⟨92307, by rfl⟩ : syracuseStep 3938453 = 184615) (by norm_num)
theorem B2627741 : Blo 1036608 2627741 := bbase (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) (by norm_num)
theorem B2332853 : Blo 1036608 2332853 := bbase (se 5 (by rfl) ⟨109352, by rfl⟩ : syracuseStep 2332853 = 218705) (by norm_num)
theorem B2332925 : Blo 1036608 2332925 := bbase (se 3 (by rfl) ⟨437423, by rfl⟩ : syracuseStep 2332925 = 874847) (by norm_num)
theorem B5249285 : Blo 1036608 5249285 := bbase (se 4 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 5249285 = 984241) (by norm_num)
theorem B2332997 : Blo 1036608 2332997 := bbase (se 4 (by rfl) ⟨218718, by rfl⟩ : syracuseStep 2332997 = 437437) (by norm_num)
theorem B1972613 : Blo 1036608 1972613 := bbase (se 4 (by rfl) ⟨184932, by rfl⟩ : syracuseStep 1972613 = 369865) (by norm_num)
theorem B2333069 : Blo 1036608 2333069 := bbase (se 3 (by rfl) ⟨437450, by rfl⟩ : syracuseStep 2333069 = 874901) (by norm_num)
theorem B2365861 : Blo 1036608 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B2955685 : Blo 1036608 2955685 := bbase (se 4 (by rfl) ⟨277095, by rfl⟩ : syracuseStep 2955685 = 554191) (by norm_num)
theorem B2333141 : Blo 1036608 2333141 := bbase (se 7 (by rfl) ⟨27341, by rfl⟩ : syracuseStep 2333141 = 54683) (by norm_num)
theorem B2628085 : Blo 1036608 2628085 := bbase (se 5 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 2628085 = 246383) (by norm_num)
theorem B2333213 : Blo 1036608 2333213 := bbase (se 3 (by rfl) ⟨437477, by rfl⟩ : syracuseStep 2333213 = 874955) (by norm_num)
theorem B1972765 : Blo 1036608 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B1874461 : Blo 1036608 1874461 := bbase (se 3 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 1874461 = 702923) (by norm_num)
theorem B2955845 : Blo 1036608 2955845 := bbase (se 4 (by rfl) ⟨277110, by rfl⟩ : syracuseStep 2955845 = 554221) (by norm_num)
theorem B2333285 : Blo 1036608 2333285 := bbase (se 4 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 2333285 = 437491) (by norm_num)
theorem B2628197 : Blo 1036608 2628197 := bbase (se 4 (by rfl) ⟨246393, by rfl⟩ : syracuseStep 2628197 = 492787) (by norm_num)
theorem B1776277 : Blo 1036608 1776277 := bbase (se 6 (by rfl) ⟨41631, by rfl⟩ : syracuseStep 1776277 = 83263) (by norm_num)
theorem B2333357 : Blo 1036608 2333357 := bbase (se 3 (by rfl) ⟨437504, by rfl⟩ : syracuseStep 2333357 = 875009) (by norm_num)
theorem B2136749 : Blo 1036608 2136749 := bbase (se 3 (by rfl) ⟨400640, by rfl⟩ : syracuseStep 2136749 = 801281) (by norm_num)
theorem B2497205 : Blo 1036608 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B2333429 : Blo 1036608 2333429 := bbase (se 5 (by rfl) ⟨109379, by rfl⟩ : syracuseStep 2333429 = 218759) (by norm_num)
theorem B2628389 : Blo 1036608 2628389 := bbase (se 4 (by rfl) ⟨246411, by rfl⟩ : syracuseStep 2628389 = 492823) (by norm_num)
theorem B2956085 : Blo 1036608 2956085 := bbase (se 5 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 2956085 = 277133) (by norm_num)
theorem B2333501 : Blo 1036608 2333501 := bbase (se 3 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 2333501 = 875063) (by norm_num)
theorem B2497349 : Blo 1036608 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B1973069 : Blo 1036608 1973069 := bbase (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) (by norm_num)
theorem B2333573 : Blo 1036608 2333573 := bbase (se 4 (by rfl) ⟨218772, by rfl⟩ : syracuseStep 2333573 = 437545) (by norm_num)
theorem B3152837 : Blo 1036608 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B2333645 : Blo 1036608 2333645 := bbase (se 3 (by rfl) ⟨437558, by rfl⟩ : syracuseStep 2333645 = 875117) (by norm_num)
theorem B2956277 : Blo 1036608 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B2333717 : Blo 1036608 2333717 := bbase (se 6 (by rfl) ⟨54696, by rfl⟩ : syracuseStep 2333717 = 109393) (by norm_num)
theorem B2530381 : Blo 1036608 2530381 := bbase (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) (by norm_num)
theorem B5905493 : Blo 1036608 5905493 := bbase (se 8 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 5905493 = 69205) (by norm_num)
theorem B2333789 : Blo 1036608 2333789 := bbase (se 3 (by rfl) ⟨437585, by rfl⟩ : syracuseStep 2333789 = 875171) (by norm_num)
theorem B1875037 : Blo 1036608 1875037 := bbase (se 3 (by rfl) ⟨351569, by rfl⟩ : syracuseStep 1875037 = 703139) (by norm_num)
theorem B2137205 : Blo 1036608 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B2628733 : Blo 1036608 2628733 := bbase (se 3 (by rfl) ⟨492887, by rfl⟩ : syracuseStep 2628733 = 985775) (by norm_num)
theorem B2333861 : Blo 1036608 2333861 := bbase (se 4 (by rfl) ⟨218799, by rfl⟩ : syracuseStep 2333861 = 437599) (by norm_num)
theorem B2333933 : Blo 1036608 2333933 := bbase (se 3 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 2333933 = 875225) (by norm_num)
theorem B2628845 : Blo 1036608 2628845 := bbase (se 3 (by rfl) ⟨492908, by rfl⟩ : syracuseStep 2628845 = 985817) (by norm_num)
theorem B2334005 : Blo 1036608 2334005 := bbase (se 5 (by rfl) ⟨109406, by rfl⟩ : syracuseStep 2334005 = 218813) (by norm_num)
theorem B3939637 : Blo 1036608 3939637 := bbase (se 5 (by rfl) ⟨184670, by rfl⟩ : syracuseStep 3939637 = 369341) (by norm_num)
theorem B2334077 : Blo 1036608 2334077 := bbase (se 3 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 2334077 = 875279) (by norm_num)
theorem B2629037 : Blo 1036608 2629037 := bbase (se 3 (by rfl) ⟨492944, by rfl⟩ : syracuseStep 2629037 = 985889) (by norm_num)
theorem B2334149 : Blo 1036608 2334149 := bbase (se 4 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 2334149 = 437653) (by norm_num)
theorem B2334221 : Blo 1036608 2334221 := bbase (se 3 (by rfl) ⟨437666, by rfl⟩ : syracuseStep 2334221 = 875333) (by norm_num)
theorem B5250581 : Blo 1036608 5250581 := bbase (se 6 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 5250581 = 246121) (by norm_num)
theorem B2367029 : Blo 1036608 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1973821 : Blo 1036608 1973821 := bbase (se 3 (by rfl) ⟨370091, by rfl⟩ : syracuseStep 1973821 = 740183) (by norm_num)
theorem B2334293 : Blo 1036608 2334293 := bbase (se 8 (by rfl) ⟨13677, by rfl⟩ : syracuseStep 2334293 = 27355) (by norm_num)
theorem B3939941 : Blo 1036608 3939941 := bbase (se 4 (by rfl) ⟨369369, by rfl⟩ : syracuseStep 3939941 = 738739) (by norm_num)
theorem B2334365 : Blo 1036608 2334365 := bbase (se 3 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 2334365 = 875387) (by norm_num)
theorem B1973965 : Blo 1036608 1973965 := bbase (se 3 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 1973965 = 740237) (by norm_num)
theorem B2334437 : Blo 1036608 2334437 := bbase (se 4 (by rfl) ⟨218853, by rfl⟩ : syracuseStep 2334437 = 437707) (by norm_num)
theorem B2629381 : Blo 1036608 2629381 := bbase (se 4 (by rfl) ⟨246504, by rfl⟩ : syracuseStep 2629381 = 493009) (by norm_num)
theorem B2334509 : Blo 1036608 2334509 := bbase (se 3 (by rfl) ⟨437720, by rfl⟩ : syracuseStep 2334509 = 875441) (by norm_num)
theorem B1974125 : Blo 1036608 1974125 := bbase (se 3 (by rfl) ⟨370148, by rfl⟩ : syracuseStep 1974125 = 740297) (by norm_num)
theorem B2334581 : Blo 1036608 2334581 := bbase (se 5 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 2334581 = 218867) (by norm_num)
theorem B2629493 : Blo 1036608 2629493 := bbase (se 5 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 2629493 = 246515) (by norm_num)
theorem B2334653 : Blo 1036608 2334653 := bbase (se 3 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 2334653 = 875495) (by norm_num)
theorem B2957269 : Blo 1036608 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B1974269 : Blo 1036608 1974269 := bbase (se 3 (by rfl) ⟨370175, by rfl⟩ : syracuseStep 1974269 = 740351) (by norm_num)
theorem B2334725 : Blo 1036608 2334725 := bbase (se 4 (by rfl) ⟨218880, by rfl⟩ : syracuseStep 2334725 = 437761) (by norm_num)
theorem B2662445 : Blo 1036608 2662445 := bbase (se 3 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 2662445 = 998417) (by norm_num)
theorem B2629685 : Blo 1036608 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B4431941 : Blo 1036608 4431941 := bbase (se 4 (by rfl) ⟨415494, by rfl⟩ : syracuseStep 4431941 = 830989) (by norm_num)
theorem B2334797 : Blo 1036608 2334797 := bbase (se 3 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 2334797 = 875549) (by norm_num)
theorem B9969749 : Blo 1036608 9969749 := bbase (se 8 (by rfl) ⟨58416, by rfl⟩ : syracuseStep 9969749 = 116833) (by norm_num)
theorem B2334869 : Blo 1036608 2334869 := bbase (se 6 (by rfl) ⟨54723, by rfl⟩ : syracuseStep 2334869 = 109447) (by norm_num)
theorem B2334941 : Blo 1036608 2334941 := bbase (se 3 (by rfl) ⟨437801, by rfl⟩ : syracuseStep 2334941 = 875603) (by norm_num)
theorem B1974557 : Blo 1036608 1974557 := bbase (se 3 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 1974557 = 740459) (by norm_num)
theorem B2335013 : Blo 1036608 2335013 := bbase (se 4 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 2335013 = 437815) (by norm_num)
theorem B4989221 : Blo 1036608 4989221 := bbase (se 4 (by rfl) ⟨467739, by rfl⟩ : syracuseStep 4989221 = 935479) (by norm_num)
theorem B4432229 : Blo 1036608 4432229 := bbase (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) (by norm_num)
theorem B1122665 : Blo 1036608 1122665 := bbase (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) (by norm_num)
theorem B2335085 : Blo 1036608 2335085 := bbase (se 3 (by rfl) ⟨437828, by rfl⟩ : syracuseStep 2335085 = 875657) (by norm_num)
theorem B2630029 : Blo 1036608 2630029 := bbase (se 3 (by rfl) ⟨493130, by rfl⟩ : syracuseStep 2630029 = 986261) (by norm_num)
theorem B1778069 : Blo 1036608 1778069 := bbase (se 6 (by rfl) ⟨41673, by rfl⟩ : syracuseStep 1778069 = 83347) (by norm_num)
theorem B2335157 : Blo 1036608 2335157 := bbase (se 5 (by rfl) ⟨109460, by rfl⟩ : syracuseStep 2335157 = 218921) (by norm_num)
theorem B1974709 : Blo 1036608 1974709 := bbase (se 5 (by rfl) ⟨92564, by rfl⟩ : syracuseStep 1974709 = 185129) (by norm_num)
theorem B1778125 : Blo 1036608 1778125 := bbase (se 3 (by rfl) ⟨333398, by rfl⟩ : syracuseStep 1778125 = 666797) (by norm_num)
theorem B8856053 : Blo 1036608 8856053 := bbase (se 5 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 8856053 = 830255) (by norm_num)
theorem B2335229 : Blo 1036608 2335229 := bbase (se 3 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 2335229 = 875711) (by norm_num)
theorem B2630141 : Blo 1036608 2630141 := bbase (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) (by norm_num)
theorem B2368061 : Blo 1036608 2368061 := bbase (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) (by norm_num)
theorem B2335301 : Blo 1036608 2335301 := bbase (se 4 (by rfl) ⟨218934, by rfl⟩ : syracuseStep 2335301 = 437869) (by norm_num)
theorem B1581637 : Blo 1036608 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B2335373 : Blo 1036608 2335373 := bbase (se 3 (by rfl) ⟨437882, by rfl⟩ : syracuseStep 2335373 = 875765) (by norm_num)
theorem B2630333 : Blo 1036608 2630333 := bbase (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) (by norm_num)
theorem B2335445 : Blo 1036608 2335445 := bbase (se 7 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 2335445 = 54737) (by norm_num)
theorem B1975013 : Blo 1036608 1975013 := bbase (se 4 (by rfl) ⟨185157, by rfl⟩ : syracuseStep 1975013 = 370315) (by norm_num)
theorem B2499349 : Blo 1036608 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B2335517 : Blo 1036608 2335517 := bbase (se 3 (by rfl) ⟨437909, by rfl⟩ : syracuseStep 2335517 = 875819) (by norm_num)
theorem B5251877 : Blo 1036608 5251877 := bbase (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) (by norm_num)
theorem B2335589 : Blo 1036608 2335589 := bbase (se 4 (by rfl) ⟨218961, by rfl⟩ : syracuseStep 2335589 = 437923) (by norm_num)
theorem B2335661 : Blo 1036608 2335661 := bbase (se 3 (by rfl) ⟨437936, by rfl⟩ : syracuseStep 2335661 = 875873) (by norm_num)
theorem B2335733 : Blo 1036608 2335733 := bbase (se 5 (by rfl) ⟨109487, by rfl⟩ : syracuseStep 2335733 = 218975) (by norm_num)
theorem B2630677 : Blo 1036608 2630677 := bbase (se 6 (by rfl) ⟨61656, by rfl⟩ : syracuseStep 2630677 = 123313) (by norm_num)
theorem B2958373 : Blo 1036608 2958373 := bbase (se 4 (by rfl) ⟨277347, by rfl⟩ : syracuseStep 2958373 = 554695) (by norm_num)
theorem B2335805 : Blo 1036608 2335805 := bbase (se 3 (by rfl) ⟨437963, by rfl⟩ : syracuseStep 2335805 = 875927) (by norm_num)
theorem B4432981 : Blo 1036608 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B6661237 : Blo 1036608 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B2335877 : Blo 1036608 2335877 := bbase (se 4 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 2335877 = 437977) (by norm_num)
theorem B2630789 : Blo 1036608 2630789 := bbase (se 4 (by rfl) ⟨246636, by rfl⟩ : syracuseStep 2630789 = 493273) (by norm_num)
theorem B7873685 : Blo 1036608 7873685 := bbase (se 6 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 7873685 = 369079) (by norm_num)
theorem B2335949 : Blo 1036608 2335949 := bbase (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) (by norm_num)
theorem B2336021 : Blo 1036608 2336021 := bbase (se 6 (by rfl) ⟨54750, by rfl⟩ : syracuseStep 2336021 = 109501) (by norm_num)
theorem B2630981 : Blo 1036608 2630981 := bbase (se 4 (by rfl) ⟨246654, by rfl⟩ : syracuseStep 2630981 = 493309) (by norm_num)
theorem B2336093 : Blo 1036608 2336093 := bbase (se 3 (by rfl) ⟨438017, by rfl⟩ : syracuseStep 2336093 = 876035) (by norm_num)
theorem B2336165 : Blo 1036608 2336165 := bbase (se 4 (by rfl) ⟨219015, by rfl⟩ : syracuseStep 2336165 = 438031) (by norm_num)
theorem B2336237 : Blo 1036608 2336237 := bbase (se 3 (by rfl) ⟨438044, by rfl⟩ : syracuseStep 2336237 = 876089) (by norm_num)
theorem B2336309 : Blo 1036608 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B2336381 : Blo 1036608 2336381 := bbase (se 3 (by rfl) ⟨438071, by rfl⟩ : syracuseStep 2336381 = 876143) (by norm_num)
theorem B2631325 : Blo 1036608 2631325 := bbase (se 3 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 2631325 = 986747) (by norm_num)
theorem B3942053 : Blo 1036608 3942053 := bbase (se 4 (by rfl) ⟨369567, by rfl⟩ : syracuseStep 3942053 = 739135) (by norm_num)
theorem B2336453 : Blo 1036608 2336453 := bbase (se 4 (by rfl) ⟨219042, by rfl⟩ : syracuseStep 2336453 = 438085) (by norm_num)
theorem B2336525 : Blo 1036608 2336525 := bbase (se 3 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 2336525 = 876197) (by norm_num)
theorem B2631437 : Blo 1036608 2631437 := bbase (se 3 (by rfl) ⟨493394, by rfl⟩ : syracuseStep 2631437 = 986789) (by norm_num)
theorem B4433717 : Blo 1036608 4433717 := bbase (se 5 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 4433717 = 415661) (by norm_num)
theorem B2336597 : Blo 1036608 2336597 := bbase (se 9 (by rfl) ⟨6845, by rfl⟩ : syracuseStep 2336597 = 13691) (by norm_num)
theorem B2336669 : Blo 1036608 2336669 := bbase (se 3 (by rfl) ⟨438125, by rfl⟩ : syracuseStep 2336669 = 876251) (by norm_num)
theorem B2107309 : Blo 1036608 2107309 := bbase (se 3 (by rfl) ⟨395120, by rfl⟩ : syracuseStep 2107309 = 790241) (by norm_num)
theorem B1124285 : Blo 1036608 1124285 := bbase (se 3 (by rfl) ⟨210803, by rfl⟩ : syracuseStep 1124285 = 421607) (by norm_num)
theorem B3942341 : Blo 1036608 3942341 := bbase (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) (by norm_num)
theorem B2631629 : Blo 1036608 2631629 := bbase (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) (by norm_num)
theorem B5056469 : Blo 1036608 5056469 := bbase (se 7 (by rfl) ⟨59255, by rfl⟩ : syracuseStep 5056469 = 118511) (by norm_num)
theorem B2336741 : Blo 1036608 2336741 := bbase (se 4 (by rfl) ⟨219069, by rfl⟩ : syracuseStep 2336741 = 438139) (by norm_num)
theorem B2336813 : Blo 1036608 2336813 := bbase (se 3 (by rfl) ⟨438152, by rfl⟩ : syracuseStep 2336813 = 876305) (by norm_num)
theorem B5253173 : Blo 1036608 5253173 := bbase (se 5 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 5253173 = 492485) (by norm_num)
theorem B2336885 : Blo 1036608 2336885 := bbase (se 5 (by rfl) ⟨109541, by rfl⟩ : syracuseStep 2336885 = 219083) (by norm_num)
theorem B2336957 : Blo 1036608 2336957 := bbase (se 3 (by rfl) ⟨438179, by rfl⟩ : syracuseStep 2336957 = 876359) (by norm_num)
theorem B2337029 : Blo 1036608 2337029 := bbase (se 4 (by rfl) ⟨219096, by rfl⟩ : syracuseStep 2337029 = 438193) (by norm_num)
theorem B2631973 : Blo 1036608 2631973 := bbase (se 4 (by rfl) ⟨246747, by rfl⟩ : syracuseStep 2631973 = 493495) (by norm_num)
theorem B2337101 : Blo 1036608 2337101 := bbase (se 3 (by rfl) ⟨438206, by rfl⟩ : syracuseStep 2337101 = 876413) (by norm_num)
theorem B26978645 : Blo 1036608 26978645 := bbase (se 10 (by rfl) ⟨39519, by rfl⟩ : syracuseStep 26978645 = 79039) (by norm_num)
theorem B2337173 : Blo 1036608 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B2632085 : Blo 1036608 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B2337245 : Blo 1036608 2337245 := bbase (se 3 (by rfl) ⟨438233, by rfl⟩ : syracuseStep 2337245 = 876467) (by norm_num)
theorem B2959877 : Blo 1036608 2959877 := bbase (se 4 (by rfl) ⟨277488, by rfl⟩ : syracuseStep 2959877 = 554977) (by norm_num)
theorem B2107925 : Blo 1036608 2107925 := bbase (se 6 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 2107925 = 98809) (by norm_num)
theorem B2337317 : Blo 1036608 2337317 := bbase (se 4 (by rfl) ⟨219123, by rfl⟩ : syracuseStep 2337317 = 438247) (by norm_num)
theorem B2632277 : Blo 1036608 2632277 := bbase (se 8 (by rfl) ⟨15423, by rfl⟩ : syracuseStep 2632277 = 30847) (by norm_num)
theorem B2337389 : Blo 1036608 2337389 := bbase (se 3 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 2337389 = 876521) (by norm_num)
theorem B1124977 : Blo 1036608 1124977 := bbase (se 2 (by rfl) ⟨421866, by rfl⟩ : syracuseStep 1124977 = 843733) (by norm_num)
theorem B2337461 : Blo 1036608 2337461 := bbase (se 5 (by rfl) ⟨109568, by rfl⟩ : syracuseStep 2337461 = 219137) (by norm_num)
theorem B2337533 : Blo 1036608 2337533 := bbase (se 3 (by rfl) ⟨438287, by rfl⟩ : syracuseStep 2337533 = 876575) (by norm_num)
theorem B2337605 : Blo 1036608 2337605 := bbase (se 4 (by rfl) ⟨219150, by rfl⟩ : syracuseStep 2337605 = 438301) (by norm_num)
theorem B2337677 : Blo 1036608 2337677 := bbase (se 3 (by rfl) ⟨438314, by rfl⟩ : syracuseStep 2337677 = 876629) (by norm_num)
theorem B4795301 : Blo 1036608 4795301 := bbase (se 4 (by rfl) ⟨449559, by rfl⟩ : syracuseStep 4795301 = 899119) (by norm_num)
theorem B2632621 : Blo 1036608 2632621 := bbase (se 3 (by rfl) ⟨493616, by rfl⟩ : syracuseStep 2632621 = 987233) (by norm_num)
theorem B2337749 : Blo 1036608 2337749 := bbase (se 7 (by rfl) ⟨27395, by rfl⟩ : syracuseStep 2337749 = 54791) (by norm_num)
theorem B2370541 : Blo 1036608 2370541 := bbase (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) (by norm_num)
theorem B2337821 : Blo 1036608 2337821 := bbase (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) (by norm_num)
theorem B2632733 : Blo 1036608 2632733 := bbase (se 3 (by rfl) ⟨493637, by rfl⟩ : syracuseStep 2632733 = 987275) (by norm_num)
theorem B3943525 : Blo 1036608 3943525 := bbase (se 4 (by rfl) ⟨369705, by rfl⟩ : syracuseStep 3943525 = 739411) (by norm_num)
theorem B2337893 : Blo 1036608 2337893 := bbase (se 4 (by rfl) ⟨219177, by rfl⟩ : syracuseStep 2337893 = 438355) (by norm_num)
theorem B2337965 : Blo 1036608 2337965 := bbase (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) (by norm_num)
theorem B2632925 : Blo 1036608 2632925 := bbase (se 3 (by rfl) ⟨493673, by rfl⟩ : syracuseStep 2632925 = 987347) (by norm_num)
theorem B2338037 : Blo 1036608 2338037 := bbase (se 5 (by rfl) ⟨109595, by rfl⟩ : syracuseStep 2338037 = 219191) (by norm_num)
theorem B2338109 : Blo 1036608 2338109 := bbase (se 3 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 2338109 = 876791) (by norm_num)
theorem B5254469 : Blo 1036608 5254469 := bbase (se 4 (by rfl) ⟨492606, by rfl⟩ : syracuseStep 5254469 = 985213) (by norm_num)
theorem B2338181 : Blo 1036608 2338181 := bbase (se 4 (by rfl) ⟨219204, by rfl⟩ : syracuseStep 2338181 = 438409) (by norm_num)
theorem B1125773 : Blo 1036608 1125773 := bbase (se 3 (by rfl) ⟨211082, by rfl⟩ : syracuseStep 1125773 = 422165) (by norm_num)
theorem B3943829 : Blo 1036608 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B2338253 : Blo 1036608 2338253 := bbase (se 3 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 2338253 = 876845) (by norm_num)
theorem B2665997 : Blo 1036608 2665997 := bbase (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) (by norm_num)
theorem B2338325 : Blo 1036608 2338325 := bbase (se 6 (by rfl) ⟨54804, by rfl⟩ : syracuseStep 2338325 = 109609) (by norm_num)
theorem B2633269 : Blo 1036608 2633269 := bbase (se 5 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 2633269 = 246869) (by norm_num)
theorem B11808341 : Blo 1036608 11808341 := bbase (se 8 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 11808341 = 138379) (by norm_num)
theorem B2666077 : Blo 1036608 2666077 := bbase (se 3 (by rfl) ⟨499889, by rfl⟩ : syracuseStep 2666077 = 999779) (by norm_num)
theorem B2338397 : Blo 1036608 2338397 := bbase (se 3 (by rfl) ⟨438449, by rfl⟩ : syracuseStep 2338397 = 876899) (by norm_num)
theorem B2338469 : Blo 1036608 2338469 := bbase (se 4 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 2338469 = 438463) (by norm_num)
theorem B2633381 : Blo 1036608 2633381 := bbase (se 4 (by rfl) ⟨246879, by rfl⟩ : syracuseStep 2633381 = 493759) (by norm_num)
theorem B2338541 : Blo 1036608 2338541 := bbase (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) (by norm_num)
theorem B2338613 : Blo 1036608 2338613 := bbase (se 5 (by rfl) ⟨109622, by rfl⟩ : syracuseStep 2338613 = 219245) (by norm_num)
theorem B3747653 : Blo 1036608 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B4992853 : Blo 1036608 4992853 := bbase (se 9 (by rfl) ⟨14627, by rfl⟩ : syracuseStep 4992853 = 29255) (by norm_num)
theorem B2633573 : Blo 1036608 2633573 := bbase (se 4 (by rfl) ⟨246897, by rfl⟩ : syracuseStep 2633573 = 493795) (by norm_num)
theorem B2338685 : Blo 1036608 2338685 := bbase (se 3 (by rfl) ⟨438503, by rfl⟩ : syracuseStep 2338685 = 877007) (by norm_num)
theorem B2338757 : Blo 1036608 2338757 := bbase (se 4 (by rfl) ⟨219258, by rfl⟩ : syracuseStep 2338757 = 438517) (by norm_num)
theorem B3158021 : Blo 1036608 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B2338829 : Blo 1036608 2338829 := bbase (se 3 (by rfl) ⟨438530, by rfl⟩ : syracuseStep 2338829 = 877061) (by norm_num)
theorem B2961461 : Blo 1036608 2961461 := bbase (se 5 (by rfl) ⟨138818, by rfl⟩ : syracuseStep 2961461 = 277637) (by norm_num)
theorem B2338901 : Blo 1036608 2338901 := bbase (se 8 (by rfl) ⟨13704, by rfl⟩ : syracuseStep 2338901 = 27409) (by norm_num)
theorem B3747941 : Blo 1036608 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B2338973 : Blo 1036608 2338973 := bbase (se 3 (by rfl) ⟨438557, by rfl⟩ : syracuseStep 2338973 = 877115) (by norm_num)
theorem B2633917 : Blo 1036608 2633917 := bbase (se 3 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 2633917 = 987719) (by norm_num)
theorem B2339045 : Blo 1036608 2339045 := bbase (se 4 (by rfl) ⟨219285, by rfl⟩ : syracuseStep 2339045 = 438571) (by norm_num)
theorem B2339117 : Blo 1036608 2339117 := bbase (se 3 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 2339117 = 877169) (by norm_num)
theorem B2634029 : Blo 1036608 2634029 := bbase (se 3 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 2634029 = 987761) (by norm_num)
theorem B2339189 : Blo 1036608 2339189 := bbase (se 5 (by rfl) ⟨109649, by rfl⟩ : syracuseStep 2339189 = 219299) (by norm_num)
theorem B1749397 : Blo 1036608 1749397 := bbase (se 6 (by rfl) ⟨41001, by rfl⟩ : syracuseStep 1749397 = 82003) (by norm_num)
theorem B2339261 : Blo 1036608 2339261 := bbase (se 3 (by rfl) ⟨438611, by rfl⟩ : syracuseStep 2339261 = 877223) (by norm_num)
theorem B1749485 : Blo 1036608 1749485 := bbase (se 3 (by rfl) ⟨328028, by rfl⟩ : syracuseStep 1749485 = 656057) (by norm_num)
theorem B2339333 : Blo 1036608 2339333 := bbase (se 4 (by rfl) ⟨219312, by rfl⟩ : syracuseStep 2339333 = 438625) (by norm_num)
theorem B2339405 : Blo 1036608 2339405 := bbase (se 3 (by rfl) ⟨438638, by rfl⟩ : syracuseStep 2339405 = 877277) (by norm_num)
theorem B5255765 : Blo 1036608 5255765 := bbase (se 8 (by rfl) ⟨30795, by rfl⟩ : syracuseStep 5255765 = 61591) (by norm_num)
theorem B1749613 : Blo 1036608 1749613 := bbase (se 3 (by rfl) ⟨328052, by rfl⟩ : syracuseStep 1749613 = 656105) (by norm_num)
theorem B2339477 : Blo 1036608 2339477 := bbase (se 6 (by rfl) ⟨54831, by rfl⟩ : syracuseStep 2339477 = 109663) (by norm_num)
theorem B1749701 : Blo 1036608 1749701 := bbase (se 4 (by rfl) ⟨164034, by rfl⟩ : syracuseStep 1749701 = 328069) (by norm_num)
theorem B2962133 : Blo 1036608 2962133 := bbase (se 7 (by rfl) ⟨34712, by rfl⟩ : syracuseStep 2962133 = 69425) (by norm_num)
theorem B2339549 : Blo 1036608 2339549 := bbase (se 3 (by rfl) ⟨438665, by rfl⟩ : syracuseStep 2339549 = 877331) (by norm_num)
theorem B2667269 : Blo 1036608 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B15971093 : Blo 1036608 15971093 := bbase (se 6 (by rfl) ⟨374322, by rfl⟩ : syracuseStep 15971093 = 748645) (by norm_num)
theorem B13316885 : Blo 1036608 13316885 := bbase (se 6 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 13316885 = 624229) (by norm_num)
theorem B2339621 : Blo 1036608 2339621 := bbase (se 4 (by rfl) ⟨219339, by rfl⟩ : syracuseStep 2339621 = 438679) (by norm_num)
theorem B1749829 : Blo 1036608 1749829 := bbase (se 4 (by rfl) ⟨164046, by rfl⟩ : syracuseStep 1749829 = 328093) (by norm_num)
theorem B2700101 : Blo 1036608 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B2339693 : Blo 1036608 2339693 := bbase (se 3 (by rfl) ⟨438692, by rfl⟩ : syracuseStep 2339693 = 877385) (by norm_num)
theorem B1749917 : Blo 1036608 1749917 := bbase (se 3 (by rfl) ⟨328109, by rfl⟩ : syracuseStep 1749917 = 656219) (by norm_num)
theorem B2339765 : Blo 1036608 2339765 := bbase (se 5 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 2339765 = 219353) (by norm_num)
theorem B2339837 : Blo 1036608 2339837 := bbase (se 3 (by rfl) ⟨438719, by rfl⟩ : syracuseStep 2339837 = 877439) (by norm_num)
theorem B4437013 : Blo 1036608 4437013 := bbase (se 6 (by rfl) ⟨103992, by rfl⟩ : syracuseStep 4437013 = 207985) (by norm_num)
theorem B1750045 : Blo 1036608 1750045 := bbase (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) (by norm_num)
theorem B2339909 : Blo 1036608 2339909 := bbase (se 4 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 2339909 = 438733) (by norm_num)
theorem B1750133 : Blo 1036608 1750133 := bbase (se 5 (by rfl) ⟨82037, by rfl⟩ : syracuseStep 1750133 = 164075) (by norm_num)
theorem B2962565 : Blo 1036608 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B2339981 : Blo 1036608 2339981 := bbase (se 3 (by rfl) ⟨438746, by rfl⟩ : syracuseStep 2339981 = 877493) (by norm_num)
theorem B3323045 : Blo 1036608 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B2340053 : Blo 1036608 2340053 := bbase (se 7 (by rfl) ⟨27422, by rfl⟩ : syracuseStep 2340053 = 54845) (by norm_num)
theorem B1750261 : Blo 1036608 1750261 := bbase (se 5 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 1750261 = 164087) (by norm_num)
theorem B2340125 : Blo 1036608 2340125 := bbase (se 3 (by rfl) ⟨438773, by rfl⟩ : syracuseStep 2340125 = 877547) (by norm_num)
theorem B1750349 : Blo 1036608 1750349 := bbase (se 3 (by rfl) ⟨328190, by rfl⟩ : syracuseStep 1750349 = 656381) (by norm_num)
theorem B2340197 : Blo 1036608 2340197 := bbase (se 4 (by rfl) ⟨219393, by rfl⟩ : syracuseStep 2340197 = 438787) (by norm_num)
theorem B2373013 : Blo 1036608 2373013 := bbase (se 6 (by rfl) ⟨55617, by rfl⟩ : syracuseStep 2373013 = 111235) (by norm_num)
theorem B2340269 : Blo 1036608 2340269 := bbase (se 3 (by rfl) ⟨438800, by rfl⟩ : syracuseStep 2340269 = 877601) (by norm_num)
theorem B1750477 : Blo 1036608 1750477 := bbase (se 3 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 1750477 = 656429) (by norm_num)
theorem B3945941 : Blo 1036608 3945941 := bbase (se 7 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 3945941 = 92483) (by norm_num)
theorem B2340341 : Blo 1036608 2340341 := bbase (se 5 (by rfl) ⟨109703, by rfl⟩ : syracuseStep 2340341 = 219407) (by norm_num)
theorem B1750565 : Blo 1036608 1750565 := bbase (se 4 (by rfl) ⟨164115, by rfl⟩ : syracuseStep 1750565 = 328231) (by norm_num)
theorem B2340413 : Blo 1036608 2340413 := bbase (se 3 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 2340413 = 877655) (by norm_num)
theorem B40416853 : Blo 1036608 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B2340485 : Blo 1036608 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B1750693 : Blo 1036608 1750693 := bbase (se 4 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 1750693 = 328255) (by norm_num)
theorem B2340557 : Blo 1036608 2340557 := bbase (se 3 (by rfl) ⟨438854, by rfl⟩ : syracuseStep 2340557 = 877709) (by norm_num)
theorem B3946229 : Blo 1036608 3946229 := bbase (se 5 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 3946229 = 369959) (by norm_num)
theorem B1750781 : Blo 1036608 1750781 := bbase (se 3 (by rfl) ⟨328271, by rfl⟩ : syracuseStep 1750781 = 656543) (by norm_num)
theorem B2340629 : Blo 1036608 2340629 := bbase (se 6 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 2340629 = 109717) (by norm_num)
theorem B4208453 : Blo 1036608 4208453 := bbase (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) (by norm_num)
theorem B13285205 : Blo 1036608 13285205 := bbase (se 9 (by rfl) ⟨38921, by rfl⟩ : syracuseStep 13285205 = 77843) (by norm_num)
theorem B2340701 : Blo 1036608 2340701 := bbase (se 3 (by rfl) ⟨438881, by rfl⟩ : syracuseStep 2340701 = 877763) (by norm_num)
theorem B5257061 : Blo 1036608 5257061 := bbase (se 4 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 5257061 = 985699) (by norm_num)
theorem B1750909 : Blo 1036608 1750909 := bbase (se 3 (by rfl) ⟨328295, by rfl⟩ : syracuseStep 1750909 = 656591) (by norm_num)
theorem B2340773 : Blo 1036608 2340773 := bbase (se 4 (by rfl) ⟨219447, by rfl⟩ : syracuseStep 2340773 = 438895) (by norm_num)
theorem B1750997 : Blo 1036608 1750997 := bbase (se 7 (by rfl) ⟨20519, by rfl⟩ : syracuseStep 1750997 = 41039) (by norm_num)
theorem B4503509 : Blo 1036608 4503509 := bbase (se 7 (by rfl) ⟨52775, by rfl⟩ : syracuseStep 4503509 = 105551) (by norm_num)
theorem B2340845 : Blo 1036608 2340845 := bbase (se 3 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 2340845 = 877817) (by norm_num)
theorem B2340917 : Blo 1036608 2340917 := bbase (se 5 (by rfl) ⟨109730, by rfl⟩ : syracuseStep 2340917 = 219461) (by norm_num)
theorem B1751125 : Blo 1036608 1751125 := bbase (se 8 (by rfl) ⟨10260, by rfl⟩ : syracuseStep 1751125 = 20521) (by norm_num)
theorem B2340989 : Blo 1036608 2340989 := bbase (se 3 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 2340989 = 877871) (by norm_num)
theorem B1751213 : Blo 1036608 1751213 := bbase (se 3 (by rfl) ⟨328352, by rfl⟩ : syracuseStep 1751213 = 656705) (by norm_num)
theorem B2341061 : Blo 1036608 2341061 := bbase (se 4 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 2341061 = 438949) (by norm_num)
theorem B2341133 : Blo 1036608 2341133 := bbase (se 3 (by rfl) ⟨438962, by rfl⟩ : syracuseStep 2341133 = 877925) (by norm_num)
theorem B1751341 : Blo 1036608 1751341 := bbase (se 3 (by rfl) ⟨328376, by rfl⟩ : syracuseStep 1751341 = 656753) (by norm_num)
theorem B2341205 : Blo 1036608 2341205 := bbase (se 10 (by rfl) ⟨3429, by rfl⟩ : syracuseStep 2341205 = 6859) (by norm_num)
theorem B1751429 : Blo 1036608 1751429 := bbase (se 4 (by rfl) ⟨164196, by rfl⟩ : syracuseStep 1751429 = 328393) (by norm_num)
theorem B2341277 : Blo 1036608 2341277 := bbase (se 3 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 2341277 = 877979) (by norm_num)
theorem B1554917 : Blo 1036608 1554917 := bbase (se 4 (by rfl) ⟨145773, by rfl⟩ : syracuseStep 1554917 = 291547) (by norm_num)
theorem B2341349 : Blo 1036608 2341349 := bbase (se 4 (by rfl) ⟨219501, by rfl⟩ : syracuseStep 2341349 = 439003) (by norm_num)
theorem B1554941 : Blo 1036608 1554941 := bbase (se 3 (by rfl) ⟨291551, by rfl⟩ : syracuseStep 1554941 = 583103) (by norm_num)
theorem B1751557 : Blo 1036608 1751557 := bbase (se 4 (by rfl) ⟨164208, by rfl⟩ : syracuseStep 1751557 = 328417) (by norm_num)
theorem B1554965 : Blo 1036608 1554965 := bbase (se 6 (by rfl) ⟨36444, by rfl⟩ : syracuseStep 1554965 = 72889) (by norm_num)
theorem B3750421 : Blo 1036608 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B1554989 : Blo 1036608 1554989 := bbase (se 3 (by rfl) ⟨291560, by rfl⟩ : syracuseStep 1554989 = 583121) (by norm_num)
theorem B1555013 : Blo 1036608 1555013 := bbase (se 4 (by rfl) ⟨145782, by rfl⟩ : syracuseStep 1555013 = 291565) (by norm_num)
theorem B1555037 : Blo 1036608 1555037 := bbase (se 3 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 1555037 = 583139) (by norm_num)
theorem B1751645 : Blo 1036608 1751645 := bbase (se 3 (by rfl) ⟨328433, by rfl⟩ : syracuseStep 1751645 = 656867) (by norm_num)
theorem B1555061 : Blo 1036608 1555061 := bbase (se 5 (by rfl) ⟨72893, by rfl⟩ : syracuseStep 1555061 = 145787) (by norm_num)
theorem B1555085 : Blo 1036608 1555085 := bbase (se 3 (by rfl) ⟨291578, by rfl⟩ : syracuseStep 1555085 = 583157) (by norm_num)
theorem B1555109 : Blo 1036608 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1555133 : Blo 1036608 1555133 := bbase (se 3 (by rfl) ⟨291587, by rfl⟩ : syracuseStep 1555133 = 583175) (by norm_num)
theorem B1555157 : Blo 1036608 1555157 := bbase (se 7 (by rfl) ⟨18224, by rfl⟩ : syracuseStep 1555157 = 36449) (by norm_num)
theorem B1751773 : Blo 1036608 1751773 := bbase (se 3 (by rfl) ⟨328457, by rfl⟩ : syracuseStep 1751773 = 656915) (by norm_num)
theorem B1555181 : Blo 1036608 1555181 := bbase (se 3 (by rfl) ⟨291596, by rfl⟩ : syracuseStep 1555181 = 583193) (by norm_num)
theorem B1555205 : Blo 1036608 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B1555229 : Blo 1036608 1555229 := bbase (se 3 (by rfl) ⟨291605, by rfl⟩ : syracuseStep 1555229 = 583211) (by norm_num)
theorem B1555253 : Blo 1036608 1555253 := bbase (se 5 (by rfl) ⟨72902, by rfl⟩ : syracuseStep 1555253 = 145805) (by norm_num)
theorem B1751861 : Blo 1036608 1751861 := bbase (se 5 (by rfl) ⟨82118, by rfl⟩ : syracuseStep 1751861 = 164237) (by norm_num)
theorem B1555277 : Blo 1036608 1555277 := bbase (se 3 (by rfl) ⟨291614, by rfl⟩ : syracuseStep 1555277 = 583229) (by norm_num)
theorem B1555301 : Blo 1036608 1555301 := bbase (se 4 (by rfl) ⟨145809, by rfl⟩ : syracuseStep 1555301 = 291619) (by norm_num)
theorem B1555325 : Blo 1036608 1555325 := bbase (se 3 (by rfl) ⟨291623, by rfl⟩ : syracuseStep 1555325 = 583247) (by norm_num)
theorem B1555349 : Blo 1036608 1555349 := bbase (se 6 (by rfl) ⟨36453, by rfl⟩ : syracuseStep 1555349 = 72907) (by norm_num)
theorem B3947413 : Blo 1036608 3947413 := bbase (se 6 (by rfl) ⟨92517, by rfl⟩ : syracuseStep 3947413 = 185035) (by norm_num)
theorem B1555373 : Blo 1036608 1555373 := bbase (se 3 (by rfl) ⟨291632, by rfl⟩ : syracuseStep 1555373 = 583265) (by norm_num)
theorem B1751989 : Blo 1036608 1751989 := bbase (se 5 (by rfl) ⟨82124, by rfl⟩ : syracuseStep 1751989 = 164249) (by norm_num)
theorem B1555397 : Blo 1036608 1555397 := bbase (se 4 (by rfl) ⟨145818, by rfl⟩ : syracuseStep 1555397 = 291637) (by norm_num)
theorem B5913557 : Blo 1036608 5913557 := bbase (se 7 (by rfl) ⟨69299, by rfl⟩ : syracuseStep 5913557 = 138599) (by norm_num)
theorem B1555421 : Blo 1036608 1555421 := bbase (se 3 (by rfl) ⟨291641, by rfl⟩ : syracuseStep 1555421 = 583283) (by norm_num)
theorem B1555445 : Blo 1036608 1555445 := bbase (se 5 (by rfl) ⟨72911, by rfl⟩ : syracuseStep 1555445 = 145823) (by norm_num)
theorem B2341885 : Blo 1036608 2341885 := bbase (se 3 (by rfl) ⟨439103, by rfl⟩ : syracuseStep 2341885 = 878207) (by norm_num)
theorem B1555469 : Blo 1036608 1555469 := bbase (se 3 (by rfl) ⟨291650, by rfl⟩ : syracuseStep 1555469 = 583301) (by norm_num)
theorem B1752077 : Blo 1036608 1752077 := bbase (se 3 (by rfl) ⟨328514, by rfl⟩ : syracuseStep 1752077 = 657029) (by norm_num)
theorem B1555493 : Blo 1036608 1555493 := bbase (se 4 (by rfl) ⟨145827, by rfl⟩ : syracuseStep 1555493 = 291655) (by norm_num)
theorem B1555517 : Blo 1036608 1555517 := bbase (se 3 (by rfl) ⟨291659, by rfl⟩ : syracuseStep 1555517 = 583319) (by norm_num)
theorem B1555541 : Blo 1036608 1555541 := bbase (se 8 (by rfl) ⟨9114, by rfl⟩ : syracuseStep 1555541 = 18229) (by norm_num)
theorem B1555565 : Blo 1036608 1555565 := bbase (se 3 (by rfl) ⟨291668, by rfl⟩ : syracuseStep 1555565 = 583337) (by norm_num)
theorem B5258357 : Blo 1036608 5258357 := bbase (se 5 (by rfl) ⟨246485, by rfl⟩ : syracuseStep 5258357 = 492971) (by norm_num)
theorem B1555589 : Blo 1036608 1555589 := bbase (se 4 (by rfl) ⟨145836, by rfl⟩ : syracuseStep 1555589 = 291673) (by norm_num)
theorem B1752205 : Blo 1036608 1752205 := bbase (se 3 (by rfl) ⟨328538, by rfl⟩ : syracuseStep 1752205 = 657077) (by norm_num)
theorem B1555613 : Blo 1036608 1555613 := bbase (se 3 (by rfl) ⟨291677, by rfl⟩ : syracuseStep 1555613 = 583355) (by norm_num)
theorem B1555637 : Blo 1036608 1555637 := bbase (se 5 (by rfl) ⟨72920, by rfl⟩ : syracuseStep 1555637 = 145841) (by norm_num)
theorem B3947717 : Blo 1036608 3947717 := bbase (se 4 (by rfl) ⟨370098, by rfl⟩ : syracuseStep 3947717 = 740197) (by norm_num)
theorem B1555661 : Blo 1036608 1555661 := bbase (se 3 (by rfl) ⟨291686, by rfl⟩ : syracuseStep 1555661 = 583373) (by norm_num)
theorem B1555685 : Blo 1036608 1555685 := bbase (se 4 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 1555685 = 291691) (by norm_num)
theorem B1752293 : Blo 1036608 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B1555709 : Blo 1036608 1555709 := bbase (se 3 (by rfl) ⟨291695, by rfl⟩ : syracuseStep 1555709 = 583391) (by norm_num)
theorem B1555733 : Blo 1036608 1555733 := bbase (se 6 (by rfl) ⟨36462, by rfl⟩ : syracuseStep 1555733 = 72925) (by norm_num)
theorem B1555757 : Blo 1036608 1555757 := bbase (se 3 (by rfl) ⟨291704, by rfl⟩ : syracuseStep 1555757 = 583409) (by norm_num)
theorem B1555781 : Blo 1036608 1555781 := bbase (se 4 (by rfl) ⟨145854, by rfl⟩ : syracuseStep 1555781 = 291709) (by norm_num)
theorem B27344213 : Blo 1036608 27344213 := bbase (se 11 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 27344213 = 40055) (by norm_num)
theorem B1555805 : Blo 1036608 1555805 := bbase (se 3 (by rfl) ⟨291713, by rfl⟩ : syracuseStep 1555805 = 583427) (by norm_num)
theorem B1752421 : Blo 1036608 1752421 := bbase (se 4 (by rfl) ⟨164289, by rfl⟩ : syracuseStep 1752421 = 328579) (by norm_num)
theorem B1555829 : Blo 1036608 1555829 := bbase (se 5 (by rfl) ⟨72929, by rfl⟩ : syracuseStep 1555829 = 145859) (by norm_num)
theorem B1555853 : Blo 1036608 1555853 := bbase (se 3 (by rfl) ⟨291722, by rfl⟩ : syracuseStep 1555853 = 583445) (by norm_num)
theorem B1555877 : Blo 1036608 1555877 := bbase (se 4 (by rfl) ⟨145863, by rfl⟩ : syracuseStep 1555877 = 291727) (by norm_num)
theorem B1555901 : Blo 1036608 1555901 := bbase (se 3 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 1555901 = 583463) (by norm_num)
theorem B1752509 : Blo 1036608 1752509 := bbase (se 3 (by rfl) ⟨328595, by rfl⟩ : syracuseStep 1752509 = 657191) (by norm_num)
theorem B1555925 : Blo 1036608 1555925 := bbase (se 7 (by rfl) ⟨18233, by rfl⟩ : syracuseStep 1555925 = 36467) (by norm_num)
theorem B1555949 : Blo 1036608 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B1555973 : Blo 1036608 1555973 := bbase (se 4 (by rfl) ⟨145872, by rfl⟩ : syracuseStep 1555973 = 291745) (by norm_num)
theorem B1555997 : Blo 1036608 1555997 := bbase (se 3 (by rfl) ⟨291749, by rfl⟩ : syracuseStep 1555997 = 583499) (by norm_num)
theorem B1556021 : Blo 1036608 1556021 := bbase (se 5 (by rfl) ⟨72938, by rfl⟩ : syracuseStep 1556021 = 145877) (by norm_num)
theorem B1752637 : Blo 1036608 1752637 := bbase (se 3 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 1752637 = 657239) (by norm_num)
theorem B1556045 : Blo 1036608 1556045 := bbase (se 3 (by rfl) ⟨291758, by rfl⟩ : syracuseStep 1556045 = 583517) (by norm_num)
theorem B1556069 : Blo 1036608 1556069 := bbase (se 4 (by rfl) ⟨145881, by rfl⟩ : syracuseStep 1556069 = 291763) (by norm_num)
theorem B1556093 : Blo 1036608 1556093 := bbase (se 3 (by rfl) ⟨291767, by rfl⟩ : syracuseStep 1556093 = 583535) (by norm_num)
theorem B1556117 : Blo 1036608 1556117 := bbase (se 6 (by rfl) ⟨36471, by rfl⟩ : syracuseStep 1556117 = 72943) (by norm_num)
theorem B1752725 : Blo 1036608 1752725 := bbase (se 6 (by rfl) ⟨41079, by rfl⟩ : syracuseStep 1752725 = 82159) (by norm_num)
theorem B1556141 : Blo 1036608 1556141 := bbase (se 3 (by rfl) ⟨291776, by rfl⟩ : syracuseStep 1556141 = 583553) (by norm_num)
theorem B1556165 : Blo 1036608 1556165 := bbase (se 4 (by rfl) ⟨145890, by rfl⟩ : syracuseStep 1556165 = 291781) (by norm_num)
theorem B1556189 : Blo 1036608 1556189 := bbase (se 3 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 1556189 = 583571) (by norm_num)
theorem B1556213 : Blo 1036608 1556213 := bbase (se 5 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 1556213 = 145895) (by norm_num)
theorem B1556237 : Blo 1036608 1556237 := bbase (se 3 (by rfl) ⟨291794, by rfl⟩ : syracuseStep 1556237 = 583589) (by norm_num)
theorem B1752853 : Blo 1036608 1752853 := bbase (se 6 (by rfl) ⟨41082, by rfl⟩ : syracuseStep 1752853 = 82165) (by norm_num)
theorem B4275989 : Blo 1036608 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B1556261 : Blo 1036608 1556261 := bbase (se 4 (by rfl) ⟨145899, by rfl⟩ : syracuseStep 1556261 = 291799) (by norm_num)
theorem B1556285 : Blo 1036608 1556285 := bbase (se 3 (by rfl) ⟨291803, by rfl⟩ : syracuseStep 1556285 = 583607) (by norm_num)
theorem B1556309 : Blo 1036608 1556309 := bbase (se 9 (by rfl) ⟨4559, by rfl⟩ : syracuseStep 1556309 = 9119) (by norm_num)
theorem B1556333 : Blo 1036608 1556333 := bbase (se 3 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 1556333 = 583625) (by norm_num)
theorem B1752941 : Blo 1036608 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B1556357 : Blo 1036608 1556357 := bbase (se 4 (by rfl) ⟨145908, by rfl⟩ : syracuseStep 1556357 = 291817) (by norm_num)
theorem B1556381 : Blo 1036608 1556381 := bbase (se 3 (by rfl) ⟨291821, by rfl⟩ : syracuseStep 1556381 = 583643) (by norm_num)
theorem B1556405 : Blo 1036608 1556405 := bbase (se 5 (by rfl) ⟨72956, by rfl⟩ : syracuseStep 1556405 = 145913) (by norm_num)
theorem B4440005 : Blo 1036608 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B1556429 : Blo 1036608 1556429 := bbase (se 3 (by rfl) ⟨291830, by rfl⟩ : syracuseStep 1556429 = 583661) (by norm_num)
theorem B1556453 : Blo 1036608 1556453 := bbase (se 4 (by rfl) ⟨145917, by rfl⟩ : syracuseStep 1556453 = 291835) (by norm_num)
theorem B1753069 : Blo 1036608 1753069 := bbase (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) (by norm_num)
theorem B1556477 : Blo 1036608 1556477 := bbase (se 3 (by rfl) ⟨291839, by rfl⟩ : syracuseStep 1556477 = 583679) (by norm_num)
theorem B1556501 : Blo 1036608 1556501 := bbase (se 6 (by rfl) ⟨36480, by rfl⟩ : syracuseStep 1556501 = 72961) (by norm_num)
theorem B1556525 : Blo 1036608 1556525 := bbase (se 3 (by rfl) ⟨291848, by rfl⟩ : syracuseStep 1556525 = 583697) (by norm_num)
theorem B1556549 : Blo 1036608 1556549 := bbase (se 4 (by rfl) ⟨145926, by rfl⟩ : syracuseStep 1556549 = 291853) (by norm_num)
theorem B1753157 : Blo 1036608 1753157 := bbase (se 4 (by rfl) ⟨164358, by rfl⟩ : syracuseStep 1753157 = 328717) (by norm_num)
theorem B1556573 : Blo 1036608 1556573 := bbase (se 3 (by rfl) ⟨291857, by rfl⟩ : syracuseStep 1556573 = 583715) (by norm_num)
theorem B1556597 : Blo 1036608 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B5914741 : Blo 1036608 5914741 := bbase (se 5 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 5914741 = 554507) (by norm_num)
theorem B1556621 : Blo 1036608 1556621 := bbase (se 3 (by rfl) ⟨291866, by rfl⟩ : syracuseStep 1556621 = 583733) (by norm_num)
theorem B1556645 : Blo 1036608 1556645 := bbase (se 4 (by rfl) ⟨145935, by rfl⟩ : syracuseStep 1556645 = 291871) (by norm_num)
theorem B3162277 : Blo 1036608 3162277 := bbase (se 4 (by rfl) ⟨296463, by rfl⟩ : syracuseStep 3162277 = 592927) (by norm_num)
theorem B1556669 : Blo 1036608 1556669 := bbase (se 3 (by rfl) ⟨291875, by rfl⟩ : syracuseStep 1556669 = 583751) (by norm_num)
theorem B1753285 : Blo 1036608 1753285 := bbase (se 4 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 1753285 = 328741) (by norm_num)
theorem B1851589 : Blo 1036608 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B1556693 : Blo 1036608 1556693 := bbase (se 7 (by rfl) ⟨18242, by rfl⟩ : syracuseStep 1556693 = 36485) (by norm_num)
theorem B1556717 : Blo 1036608 1556717 := bbase (se 3 (by rfl) ⟨291884, by rfl⟩ : syracuseStep 1556717 = 583769) (by norm_num)
theorem B1556741 : Blo 1036608 1556741 := bbase (se 4 (by rfl) ⟨145944, by rfl⟩ : syracuseStep 1556741 = 291889) (by norm_num)
theorem B1556765 : Blo 1036608 1556765 := bbase (se 3 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 1556765 = 583787) (by norm_num)
theorem B2736413 : Blo 1036608 2736413 := bbase (se 3 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 2736413 = 1026155) (by norm_num)
theorem B1753373 : Blo 1036608 1753373 := bbase (se 3 (by rfl) ⟨328757, by rfl⟩ : syracuseStep 1753373 = 657515) (by norm_num)
theorem B1556789 : Blo 1036608 1556789 := bbase (se 5 (by rfl) ⟨72974, by rfl⟩ : syracuseStep 1556789 = 145949) (by norm_num)
theorem B1556813 : Blo 1036608 1556813 := bbase (se 3 (by rfl) ⟨291902, by rfl⟩ : syracuseStep 1556813 = 583805) (by norm_num)
theorem B1556837 : Blo 1036608 1556837 := bbase (se 4 (by rfl) ⟨145953, by rfl⟩ : syracuseStep 1556837 = 291907) (by norm_num)
theorem B1556861 : Blo 1036608 1556861 := bbase (se 3 (by rfl) ⟨291911, by rfl⟩ : syracuseStep 1556861 = 583823) (by norm_num)
theorem B5259653 : Blo 1036608 5259653 := bbase (se 4 (by rfl) ⟨493092, by rfl⟩ : syracuseStep 5259653 = 986185) (by norm_num)
theorem B1556885 : Blo 1036608 1556885 := bbase (se 6 (by rfl) ⟨36489, by rfl⟩ : syracuseStep 1556885 = 72979) (by norm_num)
theorem B1753501 : Blo 1036608 1753501 := bbase (se 3 (by rfl) ⟨328781, by rfl⟩ : syracuseStep 1753501 = 657563) (by norm_num)
theorem B1556909 : Blo 1036608 1556909 := bbase (se 3 (by rfl) ⟨291920, by rfl⟩ : syracuseStep 1556909 = 583841) (by norm_num)
theorem B1556933 : Blo 1036608 1556933 := bbase (se 4 (by rfl) ⟨145962, by rfl⟩ : syracuseStep 1556933 = 291925) (by norm_num)
theorem B2245069 : Blo 1036608 2245069 := bbase (se 3 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 2245069 = 841901) (by norm_num)
theorem B1556957 : Blo 1036608 1556957 := bbase (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) (by norm_num)
theorem B1556981 : Blo 1036608 1556981 := bbase (se 5 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 1556981 = 145967) (by norm_num)
theorem B1753589 : Blo 1036608 1753589 := bbase (se 5 (by rfl) ⟨82199, by rfl⟩ : syracuseStep 1753589 = 164399) (by norm_num)
theorem B1557005 : Blo 1036608 1557005 := bbase (se 3 (by rfl) ⟨291938, by rfl⟩ : syracuseStep 1557005 = 583877) (by norm_num)
theorem B1557029 : Blo 1036608 1557029 := bbase (se 4 (by rfl) ⟨145971, by rfl⟩ : syracuseStep 1557029 = 291943) (by norm_num)
theorem B1557053 : Blo 1036608 1557053 := bbase (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) (by norm_num)
theorem B1557077 : Blo 1036608 1557077 := bbase (se 8 (by rfl) ⟨9123, by rfl⟩ : syracuseStep 1557077 = 18247) (by norm_num)
theorem B1557101 : Blo 1036608 1557101 := bbase (se 3 (by rfl) ⟨291956, by rfl⟩ : syracuseStep 1557101 = 583913) (by norm_num)
theorem B1753717 : Blo 1036608 1753717 := bbase (se 5 (by rfl) ⟨82205, by rfl⟩ : syracuseStep 1753717 = 164411) (by norm_num)
theorem B1557125 : Blo 1036608 1557125 := bbase (se 4 (by rfl) ⟨145980, by rfl⟩ : syracuseStep 1557125 = 291961) (by norm_num)
theorem B1557149 : Blo 1036608 1557149 := bbase (se 3 (by rfl) ⟨291965, by rfl⟩ : syracuseStep 1557149 = 583931) (by norm_num)
theorem B1557173 : Blo 1036608 1557173 := bbase (se 5 (by rfl) ⟨72992, by rfl⟩ : syracuseStep 1557173 = 145985) (by norm_num)
theorem B1557197 : Blo 1036608 1557197 := bbase (se 3 (by rfl) ⟨291974, by rfl⟩ : syracuseStep 1557197 = 583949) (by norm_num)
theorem B1753805 : Blo 1036608 1753805 := bbase (se 3 (by rfl) ⟨328838, by rfl⟩ : syracuseStep 1753805 = 657677) (by norm_num)
theorem B1557221 : Blo 1036608 1557221 := bbase (se 4 (by rfl) ⟨145989, by rfl⟩ : syracuseStep 1557221 = 291979) (by norm_num)
theorem B7881461 : Blo 1036608 7881461 := bbase (se 5 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 7881461 = 738887) (by norm_num)
theorem B1557245 : Blo 1036608 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B1557269 : Blo 1036608 1557269 := bbase (se 6 (by rfl) ⟨36498, by rfl⟩ : syracuseStep 1557269 = 72997) (by norm_num)
theorem B1557293 : Blo 1036608 1557293 := bbase (se 3 (by rfl) ⟨291992, by rfl⟩ : syracuseStep 1557293 = 583985) (by norm_num)
theorem B1557317 : Blo 1036608 1557317 := bbase (se 4 (by rfl) ⟨145998, by rfl⟩ : syracuseStep 1557317 = 291997) (by norm_num)
theorem B1753933 : Blo 1036608 1753933 := bbase (se 3 (by rfl) ⟨328862, by rfl⟩ : syracuseStep 1753933 = 657725) (by norm_num)
theorem B1557341 : Blo 1036608 1557341 := bbase (se 3 (by rfl) ⟨292001, by rfl⟩ : syracuseStep 1557341 = 584003) (by norm_num)
theorem B1557365 : Blo 1036608 1557365 := bbase (se 5 (by rfl) ⟨73001, by rfl⟩ : syracuseStep 1557365 = 146003) (by norm_num)
theorem B3326837 : Blo 1036608 3326837 := bbase (se 5 (by rfl) ⟨155945, by rfl⟩ : syracuseStep 3326837 = 311891) (by norm_num)
theorem B1557389 : Blo 1036608 1557389 := bbase (se 3 (by rfl) ⟨292010, by rfl⟩ : syracuseStep 1557389 = 584021) (by norm_num)
theorem B1557413 : Blo 1036608 1557413 := bbase (se 4 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 1557413 = 292015) (by norm_num)
theorem B1754021 : Blo 1036608 1754021 := bbase (se 4 (by rfl) ⟨164439, by rfl⟩ : syracuseStep 1754021 = 328879) (by norm_num)
theorem B3556277 : Blo 1036608 3556277 := bbase (se 5 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 3556277 = 333401) (by norm_num)
theorem B4441013 : Blo 1036608 4441013 := bbase (se 5 (by rfl) ⟨208172, by rfl⟩ : syracuseStep 4441013 = 416345) (by norm_num)
theorem B1557437 : Blo 1036608 1557437 := bbase (se 3 (by rfl) ⟨292019, by rfl⟩ : syracuseStep 1557437 = 584039) (by norm_num)
theorem B1557461 : Blo 1036608 1557461 := bbase (se 7 (by rfl) ⟨18251, by rfl⟩ : syracuseStep 1557461 = 36503) (by norm_num)
theorem B1557485 : Blo 1036608 1557485 := bbase (se 3 (by rfl) ⟨292028, by rfl⟩ : syracuseStep 1557485 = 584057) (by norm_num)
theorem B1557509 : Blo 1036608 1557509 := bbase (se 4 (by rfl) ⟨146016, by rfl⟩ : syracuseStep 1557509 = 292033) (by norm_num)
theorem B1557533 : Blo 1036608 1557533 := bbase (se 3 (by rfl) ⟨292037, by rfl⟩ : syracuseStep 1557533 = 584075) (by norm_num)
theorem B1754149 : Blo 1036608 1754149 := bbase (se 4 (by rfl) ⟨164451, by rfl⟩ : syracuseStep 1754149 = 328903) (by norm_num)
theorem B1557557 : Blo 1036608 1557557 := bbase (se 5 (by rfl) ⟨73010, by rfl⟩ : syracuseStep 1557557 = 146021) (by norm_num)
theorem B1557581 : Blo 1036608 1557581 := bbase (se 3 (by rfl) ⟨292046, by rfl⟩ : syracuseStep 1557581 = 584093) (by norm_num)
theorem B1557605 : Blo 1036608 1557605 := bbase (se 4 (by rfl) ⟨146025, by rfl⟩ : syracuseStep 1557605 = 292051) (by norm_num)
theorem B1557629 : Blo 1036608 1557629 := bbase (se 3 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 1557629 = 584111) (by norm_num)
theorem B1754237 : Blo 1036608 1754237 := bbase (se 3 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 1754237 = 657839) (by norm_num)
theorem B1557653 : Blo 1036608 1557653 := bbase (se 6 (by rfl) ⟨36507, by rfl⟩ : syracuseStep 1557653 = 73015) (by norm_num)
theorem B1557677 : Blo 1036608 1557677 := bbase (se 3 (by rfl) ⟨292064, by rfl⟩ : syracuseStep 1557677 = 584129) (by norm_num)
theorem B2999477 : Blo 1036608 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B1557701 : Blo 1036608 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B1557725 : Blo 1036608 1557725 := bbase (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) (by norm_num)
theorem B1557749 : Blo 1036608 1557749 := bbase (se 5 (by rfl) ⟨73019, by rfl⟩ : syracuseStep 1557749 = 146039) (by norm_num)
theorem B4211957 : Blo 1036608 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B1754365 : Blo 1036608 1754365 := bbase (se 3 (by rfl) ⟨328943, by rfl⟩ : syracuseStep 1754365 = 657887) (by norm_num)
theorem B4736261 : Blo 1036608 4736261 := bbase (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) (by norm_num)
theorem B3949829 : Blo 1036608 3949829 := bbase (se 4 (by rfl) ⟨370296, by rfl⟩ : syracuseStep 3949829 = 740593) (by norm_num)
theorem B1557773 : Blo 1036608 1557773 := bbase (se 3 (by rfl) ⟨292082, by rfl⟩ : syracuseStep 1557773 = 584165) (by norm_num)
theorem B1557797 : Blo 1036608 1557797 := bbase (se 4 (by rfl) ⟨146043, by rfl⟩ : syracuseStep 1557797 = 292087) (by norm_num)
theorem B3163445 : Blo 1036608 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B1557821 : Blo 1036608 1557821 := bbase (se 3 (by rfl) ⟨292091, by rfl⟩ : syracuseStep 1557821 = 584183) (by norm_num)
theorem B1557845 : Blo 1036608 1557845 := bbase (se 12 (by rfl) ⟨570, by rfl⟩ : syracuseStep 1557845 = 1141) (by norm_num)
theorem B1754453 : Blo 1036608 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B1557869 : Blo 1036608 1557869 := bbase (se 3 (by rfl) ⟨292100, by rfl⟩ : syracuseStep 1557869 = 584201) (by norm_num)
theorem B1557893 : Blo 1036608 1557893 := bbase (se 4 (by rfl) ⟨146052, by rfl⟩ : syracuseStep 1557893 = 292105) (by norm_num)
theorem B3163541 : Blo 1036608 3163541 := bbase (se 6 (by rfl) ⟨74145, by rfl⟩ : syracuseStep 3163541 = 148291) (by norm_num)
theorem B1557917 : Blo 1036608 1557917 := bbase (se 3 (by rfl) ⟨292109, by rfl⟩ : syracuseStep 1557917 = 584219) (by norm_num)
theorem B1557941 : Blo 1036608 1557941 := bbase (se 5 (by rfl) ⟨73028, by rfl⟩ : syracuseStep 1557941 = 146057) (by norm_num)
theorem B1557965 : Blo 1036608 1557965 := bbase (se 3 (by rfl) ⟨292118, by rfl⟩ : syracuseStep 1557965 = 584237) (by norm_num)
theorem B1754581 : Blo 1036608 1754581 := bbase (se 7 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 1754581 = 41123) (by norm_num)
theorem B1557989 : Blo 1036608 1557989 := bbase (se 4 (by rfl) ⟨146061, by rfl⟩ : syracuseStep 1557989 = 292123) (by norm_num)
theorem B1558013 : Blo 1036608 1558013 := bbase (se 3 (by rfl) ⟨292127, by rfl⟩ : syracuseStep 1558013 = 584255) (by norm_num)
theorem B1558037 : Blo 1036608 1558037 := bbase (se 6 (by rfl) ⟨36516, by rfl⟩ : syracuseStep 1558037 = 73033) (by norm_num)
theorem B3950117 : Blo 1036608 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B1558061 : Blo 1036608 1558061 := bbase (se 3 (by rfl) ⟨292136, by rfl⟩ : syracuseStep 1558061 = 584273) (by norm_num)
theorem B1754669 : Blo 1036608 1754669 := bbase (se 3 (by rfl) ⟨329000, by rfl⟩ : syracuseStep 1754669 = 658001) (by norm_num)
theorem B2246213 : Blo 1036608 2246213 := bbase (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) (by norm_num)
theorem B1558085 : Blo 1036608 1558085 := bbase (se 4 (by rfl) ⟨146070, by rfl⟩ : syracuseStep 1558085 = 292141) (by norm_num)
theorem B1558109 : Blo 1036608 1558109 := bbase (se 3 (by rfl) ⟨292145, by rfl⟩ : syracuseStep 1558109 = 584291) (by norm_num)
theorem B1558133 : Blo 1036608 1558133 := bbase (se 5 (by rfl) ⟨73037, by rfl⟩ : syracuseStep 1558133 = 146075) (by norm_num)
theorem B1558157 : Blo 1036608 1558157 := bbase (se 3 (by rfl) ⟨292154, by rfl⟩ : syracuseStep 1558157 = 584309) (by norm_num)
theorem B5260949 : Blo 1036608 5260949 := bbase (se 6 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 5260949 = 246607) (by norm_num)
theorem B1558181 : Blo 1036608 1558181 := bbase (se 4 (by rfl) ⟨146079, by rfl⟩ : syracuseStep 1558181 = 292159) (by norm_num)
theorem B1754797 : Blo 1036608 1754797 := bbase (se 3 (by rfl) ⟨329024, by rfl⟩ : syracuseStep 1754797 = 658049) (by norm_num)
theorem B1558205 : Blo 1036608 1558205 := bbase (se 3 (by rfl) ⟨292163, by rfl⟩ : syracuseStep 1558205 = 584327) (by norm_num)
theorem B1558229 : Blo 1036608 1558229 := bbase (se 7 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 1558229 = 36521) (by norm_num)
theorem B1558253 : Blo 1036608 1558253 := bbase (se 3 (by rfl) ⟨292172, by rfl⟩ : syracuseStep 1558253 = 584345) (by norm_num)
theorem B3327749 : Blo 1036608 3327749 := bbase (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) (by norm_num)
theorem B1558277 : Blo 1036608 1558277 := bbase (se 4 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 1558277 = 292177) (by norm_num)
theorem B1754885 : Blo 1036608 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B1558301 : Blo 1036608 1558301 := bbase (se 3 (by rfl) ⟨292181, by rfl⟩ : syracuseStep 1558301 = 584363) (by norm_num)
theorem B1558325 : Blo 1036608 1558325 := bbase (se 5 (by rfl) ⟨73046, by rfl⟩ : syracuseStep 1558325 = 146093) (by norm_num)
theorem B1558349 : Blo 1036608 1558349 := bbase (se 3 (by rfl) ⟨292190, by rfl⟩ : syracuseStep 1558349 = 584381) (by norm_num)
theorem B15976277 : Blo 1036608 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B1558373 : Blo 1036608 1558373 := bbase (se 4 (by rfl) ⟨146097, by rfl⟩ : syracuseStep 1558373 = 292195) (by norm_num)
theorem B1558397 : Blo 1036608 1558397 := bbase (se 3 (by rfl) ⟨292199, by rfl⟩ : syracuseStep 1558397 = 584399) (by norm_num)
theorem B1755013 : Blo 1036608 1755013 := bbase (se 4 (by rfl) ⟨164532, by rfl⟩ : syracuseStep 1755013 = 329065) (by norm_num)
theorem B1558421 : Blo 1036608 1558421 := bbase (se 6 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 1558421 = 73051) (by norm_num)
theorem B1558445 : Blo 1036608 1558445 := bbase (se 3 (by rfl) ⟨292208, by rfl⟩ : syracuseStep 1558445 = 584417) (by norm_num)
theorem B1558469 : Blo 1036608 1558469 := bbase (se 4 (by rfl) ⟨146106, by rfl⟩ : syracuseStep 1558469 = 292213) (by norm_num)
theorem B33736661 : Blo 1036608 33736661 := bbase (se 7 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 33736661 = 790703) (by norm_num)
theorem B1558493 : Blo 1036608 1558493 := bbase (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) (by norm_num)
theorem B1755101 : Blo 1036608 1755101 := bbase (se 3 (by rfl) ⟨329081, by rfl⟩ : syracuseStep 1755101 = 658163) (by norm_num)
theorem B1558517 : Blo 1036608 1558517 := bbase (se 5 (by rfl) ⟨73055, by rfl⟩ : syracuseStep 1558517 = 146111) (by norm_num)
theorem B1558541 : Blo 1036608 1558541 := bbase (se 3 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 1558541 = 584453) (by norm_num)
theorem B1558565 : Blo 1036608 1558565 := bbase (se 4 (by rfl) ⟨146115, by rfl⟩ : syracuseStep 1558565 = 292231) (by norm_num)
theorem B5916725 : Blo 1036608 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B1558589 : Blo 1036608 1558589 := bbase (se 3 (by rfl) ⟨292235, by rfl⟩ : syracuseStep 1558589 = 584471) (by norm_num)
theorem B1558613 : Blo 1036608 1558613 := bbase (se 8 (by rfl) ⟨9132, by rfl⟩ : syracuseStep 1558613 = 18265) (by norm_num)
theorem B1755229 : Blo 1036608 1755229 := bbase (se 3 (by rfl) ⟨329105, by rfl⟩ : syracuseStep 1755229 = 658211) (by norm_num)
theorem B1558637 : Blo 1036608 1558637 := bbase (se 3 (by rfl) ⟨292244, by rfl⟩ : syracuseStep 1558637 = 584489) (by norm_num)
theorem B1558661 : Blo 1036608 1558661 := bbase (se 4 (by rfl) ⟨146124, by rfl⟩ : syracuseStep 1558661 = 292249) (by norm_num)
theorem B1558685 : Blo 1036608 1558685 := bbase (se 3 (by rfl) ⟨292253, by rfl⟩ : syracuseStep 1558685 = 584507) (by norm_num)
theorem B1558709 : Blo 1036608 1558709 := bbase (se 5 (by rfl) ⟨73064, by rfl⟩ : syracuseStep 1558709 = 146129) (by norm_num)
theorem B1755317 : Blo 1036608 1755317 := bbase (se 5 (by rfl) ⟨82280, by rfl⟩ : syracuseStep 1755317 = 164561) (by norm_num)
theorem B1558733 : Blo 1036608 1558733 := bbase (se 3 (by rfl) ⟨292262, by rfl⟩ : syracuseStep 1558733 = 584525) (by norm_num)
theorem B1558757 : Blo 1036608 1558757 := bbase (se 4 (by rfl) ⟨146133, by rfl⟩ : syracuseStep 1558757 = 292267) (by norm_num)
theorem B2214125 : Blo 1036608 2214125 := bbase (se 3 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 2214125 = 830297) (by norm_num)
theorem B1558781 : Blo 1036608 1558781 := bbase (se 3 (by rfl) ⟨292271, by rfl⟩ : syracuseStep 1558781 = 584543) (by norm_num)
theorem B1558805 : Blo 1036608 1558805 := bbase (se 6 (by rfl) ⟨36534, by rfl⟩ : syracuseStep 1558805 = 73069) (by norm_num)
theorem B1558829 : Blo 1036608 1558829 := bbase (se 3 (by rfl) ⟨292280, by rfl⟩ : syracuseStep 1558829 = 584561) (by norm_num)
theorem B1755445 : Blo 1036608 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B1558853 : Blo 1036608 1558853 := bbase (se 4 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 1558853 = 292285) (by norm_num)
theorem B1558877 : Blo 1036608 1558877 := bbase (se 3 (by rfl) ⟨292289, by rfl⟩ : syracuseStep 1558877 = 584579) (by norm_num)
theorem B1558901 : Blo 1036608 1558901 := bbase (se 5 (by rfl) ⟨73073, by rfl⟩ : syracuseStep 1558901 = 146147) (by norm_num)
theorem B1558925 : Blo 1036608 1558925 := bbase (se 3 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 1558925 = 584597) (by norm_num)
theorem B1755533 : Blo 1036608 1755533 := bbase (se 3 (by rfl) ⟨329162, by rfl⟩ : syracuseStep 1755533 = 658325) (by norm_num)
theorem B1558949 : Blo 1036608 1558949 := bbase (se 4 (by rfl) ⟨146151, by rfl⟩ : syracuseStep 1558949 = 292303) (by norm_num)
theorem B1558973 : Blo 1036608 1558973 := bbase (se 3 (by rfl) ⟨292307, by rfl⟩ : syracuseStep 1558973 = 584615) (by norm_num)
theorem B1558997 : Blo 1036608 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B4999637 : Blo 1036608 4999637 := bbase (se 7 (by rfl) ⟨58589, by rfl⟩ : syracuseStep 4999637 = 117179) (by norm_num)
theorem B1559021 : Blo 1036608 1559021 := bbase (se 3 (by rfl) ⟨292316, by rfl⟩ : syracuseStep 1559021 = 584633) (by norm_num)
theorem B1559045 : Blo 1036608 1559045 := bbase (se 4 (by rfl) ⟨146160, by rfl⟩ : syracuseStep 1559045 = 292321) (by norm_num)
theorem B1755661 : Blo 1036608 1755661 := bbase (se 3 (by rfl) ⟨329186, by rfl⟩ : syracuseStep 1755661 = 658373) (by norm_num)
theorem B1264153 : Blo 1036608 1264153 := bbase (se 2 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 1264153 = 948115) (by norm_num)
theorem B1559069 : Blo 1036608 1559069 := bbase (se 3 (by rfl) ⟨292325, by rfl⟩ : syracuseStep 1559069 = 584651) (by norm_num)
theorem B1559093 : Blo 1036608 1559093 := bbase (se 5 (by rfl) ⟨73082, by rfl⟩ : syracuseStep 1559093 = 146165) (by norm_num)
theorem B1559117 : Blo 1036608 1559117 := bbase (se 3 (by rfl) ⟨292334, by rfl⟩ : syracuseStep 1559117 = 584669) (by norm_num)
theorem B1559141 : Blo 1036608 1559141 := bbase (se 4 (by rfl) ⟨146169, by rfl⟩ : syracuseStep 1559141 = 292339) (by norm_num)
theorem B1755749 : Blo 1036608 1755749 := bbase (se 4 (by rfl) ⟨164601, by rfl⟩ : syracuseStep 1755749 = 329203) (by norm_num)
theorem B7096949 : Blo 1036608 7096949 := bbase (se 5 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 7096949 = 665339) (by norm_num)
theorem B1559165 : Blo 1036608 1559165 := bbase (se 3 (by rfl) ⟨292343, by rfl⟩ : syracuseStep 1559165 = 584687) (by norm_num)
theorem B1559189 : Blo 1036608 1559189 := bbase (se 6 (by rfl) ⟨36543, by rfl⟩ : syracuseStep 1559189 = 73087) (by norm_num)
theorem B4442789 : Blo 1036608 4442789 := bbase (se 4 (by rfl) ⟨416511, by rfl⟩ : syracuseStep 4442789 = 833023) (by norm_num)
theorem B1559213 : Blo 1036608 1559213 := bbase (se 3 (by rfl) ⟨292352, by rfl⟩ : syracuseStep 1559213 = 584705) (by norm_num)
theorem B1559237 : Blo 1036608 1559237 := bbase (se 4 (by rfl) ⟨146178, by rfl⟩ : syracuseStep 1559237 = 292357) (by norm_num)
theorem B1559261 : Blo 1036608 1559261 := bbase (se 3 (by rfl) ⟨292361, by rfl⟩ : syracuseStep 1559261 = 584723) (by norm_num)
theorem B1755877 : Blo 1036608 1755877 := bbase (se 4 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 1755877 = 329227) (by norm_num)
theorem B1559285 : Blo 1036608 1559285 := bbase (se 5 (by rfl) ⟨73091, by rfl⟩ : syracuseStep 1559285 = 146183) (by norm_num)
theorem B1559309 : Blo 1036608 1559309 := bbase (se 3 (by rfl) ⟨292370, by rfl⟩ : syracuseStep 1559309 = 584741) (by norm_num)
theorem B1559333 : Blo 1036608 1559333 := bbase (se 4 (by rfl) ⟨146187, by rfl⟩ : syracuseStep 1559333 = 292375) (by norm_num)
theorem B1559357 : Blo 1036608 1559357 := bbase (se 3 (by rfl) ⟨292379, by rfl⟩ : syracuseStep 1559357 = 584759) (by norm_num)
theorem B1755965 : Blo 1036608 1755965 := bbase (se 3 (by rfl) ⟨329243, by rfl⟩ : syracuseStep 1755965 = 658487) (by norm_num)
theorem B1264465 : Blo 1036608 1264465 := bbase (se 2 (by rfl) ⟨474174, by rfl⟩ : syracuseStep 1264465 = 948349) (by norm_num)
theorem B1559381 : Blo 1036608 1559381 := bbase (se 9 (by rfl) ⟨4568, by rfl⟩ : syracuseStep 1559381 = 9137) (by norm_num)
theorem B1559405 : Blo 1036608 1559405 := bbase (se 3 (by rfl) ⟨292388, by rfl⟩ : syracuseStep 1559405 = 584777) (by norm_num)
theorem B1166197 : Blo 1036608 1166197 := bbase (se 5 (by rfl) ⟨54665, by rfl⟩ : syracuseStep 1166197 = 109331) (by norm_num)
theorem B1559429 : Blo 1036608 1559429 := bbase (se 4 (by rfl) ⟨146196, by rfl⟩ : syracuseStep 1559429 = 292393) (by norm_num)
theorem B1166233 : Blo 1036608 1166233 := bbase (se 2 (by rfl) ⟨437337, by rfl⟩ : syracuseStep 1166233 = 874675) (by norm_num)
theorem B1559453 : Blo 1036608 1559453 := bbase (se 3 (by rfl) ⟨292397, by rfl⟩ : syracuseStep 1559453 = 584795) (by norm_num)
theorem B5262245 : Blo 1036608 5262245 := bbase (se 4 (by rfl) ⟨493335, by rfl⟩ : syracuseStep 5262245 = 986671) (by norm_num)
theorem B1559477 : Blo 1036608 1559477 := bbase (se 5 (by rfl) ⟨73100, by rfl⟩ : syracuseStep 1559477 = 146201) (by norm_num)
theorem B1166269 : Blo 1036608 1166269 := bbase (se 3 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 1166269 = 437351) (by norm_num)
theorem B1559501 : Blo 1036608 1559501 := bbase (se 3 (by rfl) ⟨292406, by rfl⟩ : syracuseStep 1559501 = 584813) (by norm_num)
theorem B2214877 : Blo 1036608 2214877 := bbase (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) (by norm_num)
theorem B1166305 : Blo 1036608 1166305 := bbase (se 2 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 1166305 = 874729) (by norm_num)
theorem B1559525 : Blo 1036608 1559525 := bbase (se 4 (by rfl) ⟨146205, by rfl⟩ : syracuseStep 1559525 = 292411) (by norm_num)
theorem B1559549 : Blo 1036608 1559549 := bbase (se 3 (by rfl) ⟨292415, by rfl⟩ : syracuseStep 1559549 = 584831) (by norm_num)
theorem B1166341 : Blo 1036608 1166341 := bbase (se 4 (by rfl) ⟨109344, by rfl⟩ : syracuseStep 1166341 = 218689) (by norm_num)
theorem B1559573 : Blo 1036608 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B1166377 : Blo 1036608 1166377 := bbase (se 2 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 1166377 = 874783) (by norm_num)
theorem B1559597 : Blo 1036608 1559597 := bbase (se 3 (by rfl) ⟨292424, by rfl⟩ : syracuseStep 1559597 = 584849) (by norm_num)
theorem B3329093 : Blo 1036608 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B1559621 : Blo 1036608 1559621 := bbase (se 4 (by rfl) ⟨146214, by rfl⟩ : syracuseStep 1559621 = 292429) (by norm_num)
theorem B1166413 : Blo 1036608 1166413 := bbase (se 3 (by rfl) ⟨218702, by rfl⟩ : syracuseStep 1166413 = 437405) (by norm_num)
theorem B1559645 : Blo 1036608 1559645 := bbase (se 3 (by rfl) ⟨292433, by rfl⟩ : syracuseStep 1559645 = 584867) (by norm_num)
theorem B2215021 : Blo 1036608 2215021 := bbase (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) (by norm_num)
theorem B1166449 : Blo 1036608 1166449 := bbase (se 2 (by rfl) ⟨437418, by rfl⟩ : syracuseStep 1166449 = 874837) (by norm_num)
theorem B1559669 : Blo 1036608 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B1559693 : Blo 1036608 1559693 := bbase (se 3 (by rfl) ⟨292442, by rfl⟩ : syracuseStep 1559693 = 584885) (by norm_num)
theorem B1166485 : Blo 1036608 1166485 := bbase (se 6 (by rfl) ⟨27339, by rfl⟩ : syracuseStep 1166485 = 54679) (by norm_num)
theorem B1559717 : Blo 1036608 1559717 := bbase (se 4 (by rfl) ⟨146223, by rfl⟩ : syracuseStep 1559717 = 292447) (by norm_num)
theorem B1166521 : Blo 1036608 1166521 := bbase (se 2 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 1166521 = 874891) (by norm_num)
theorem B1559741 : Blo 1036608 1559741 := bbase (se 3 (by rfl) ⟨292451, by rfl⟩ : syracuseStep 1559741 = 584903) (by norm_num)
theorem B1559765 : Blo 1036608 1559765 := bbase (se 7 (by rfl) ⟨18278, by rfl⟩ : syracuseStep 1559765 = 36557) (by norm_num)
theorem B1166557 : Blo 1036608 1166557 := bbase (se 3 (by rfl) ⟨218729, by rfl⟩ : syracuseStep 1166557 = 437459) (by norm_num)
theorem B1559789 : Blo 1036608 1559789 := bbase (se 3 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 1559789 = 584921) (by norm_num)
theorem B1166593 : Blo 1036608 1166593 := bbase (se 2 (by rfl) ⟨437472, by rfl⟩ : syracuseStep 1166593 = 874945) (by norm_num)
theorem B1559813 : Blo 1036608 1559813 := bbase (se 4 (by rfl) ⟨146232, by rfl⟩ : syracuseStep 1559813 = 292465) (by norm_num)
theorem B1559837 : Blo 1036608 1559837 := bbase (se 3 (by rfl) ⟨292469, by rfl⟩ : syracuseStep 1559837 = 584939) (by norm_num)
theorem B1166629 : Blo 1036608 1166629 := bbase (se 4 (by rfl) ⟨109371, by rfl⟩ : syracuseStep 1166629 = 218743) (by norm_num)
theorem B1559861 : Blo 1036608 1559861 := bbase (se 5 (by rfl) ⟨73118, by rfl⟩ : syracuseStep 1559861 = 146237) (by norm_num)
theorem B1166665 : Blo 1036608 1166665 := bbase (se 2 (by rfl) ⟨437499, by rfl⟩ : syracuseStep 1166665 = 874999) (by norm_num)
theorem B1559885 : Blo 1036608 1559885 := bbase (se 3 (by rfl) ⟨292478, by rfl⟩ : syracuseStep 1559885 = 584957) (by norm_num)
theorem B1559909 : Blo 1036608 1559909 := bbase (se 4 (by rfl) ⟨146241, by rfl⟩ : syracuseStep 1559909 = 292483) (by norm_num)
theorem B1166701 : Blo 1036608 1166701 := bbase (se 3 (by rfl) ⟨218756, by rfl⟩ : syracuseStep 1166701 = 437513) (by norm_num)
theorem B1559933 : Blo 1036608 1559933 := bbase (se 3 (by rfl) ⟨292487, by rfl⟩ : syracuseStep 1559933 = 584975) (by norm_num)
theorem B1166737 : Blo 1036608 1166737 := bbase (se 2 (by rfl) ⟨437526, by rfl⟩ : syracuseStep 1166737 = 875053) (by norm_num)
theorem B1559957 : Blo 1036608 1559957 := bbase (se 6 (by rfl) ⟨36561, by rfl⟩ : syracuseStep 1559957 = 73123) (by norm_num)
theorem B1559981 : Blo 1036608 1559981 := bbase (se 3 (by rfl) ⟨292496, by rfl⟩ : syracuseStep 1559981 = 584993) (by norm_num)
theorem B1166773 : Blo 1036608 1166773 := bbase (se 5 (by rfl) ⟨54692, by rfl⟩ : syracuseStep 1166773 = 109385) (by norm_num)
theorem B1560005 : Blo 1036608 1560005 := bbase (se 4 (by rfl) ⟨146250, by rfl⟩ : syracuseStep 1560005 = 292501) (by norm_num)
theorem B1166809 : Blo 1036608 1166809 := bbase (se 2 (by rfl) ⟨437553, by rfl⟩ : syracuseStep 1166809 = 875107) (by norm_num)
theorem B1560029 : Blo 1036608 1560029 := bbase (se 3 (by rfl) ⟨292505, by rfl⟩ : syracuseStep 1560029 = 585011) (by norm_num)
theorem B2215397 : Blo 1036608 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B1560053 : Blo 1036608 1560053 := bbase (se 5 (by rfl) ⟨73127, by rfl⟩ : syracuseStep 1560053 = 146255) (by norm_num)
theorem B1166845 : Blo 1036608 1166845 := bbase (se 3 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 1166845 = 437567) (by norm_num)
theorem B1560077 : Blo 1036608 1560077 := bbase (se 3 (by rfl) ⟨292514, by rfl⟩ : syracuseStep 1560077 = 585029) (by norm_num)
theorem B1166881 : Blo 1036608 1166881 := bbase (se 2 (by rfl) ⟨437580, by rfl⟩ : syracuseStep 1166881 = 875161) (by norm_num)
theorem B1560101 : Blo 1036608 1560101 := bbase (se 4 (by rfl) ⟨146259, by rfl⟩ : syracuseStep 1560101 = 292519) (by norm_num)
theorem B1560125 : Blo 1036608 1560125 := bbase (se 3 (by rfl) ⟨292523, by rfl⟩ : syracuseStep 1560125 = 585047) (by norm_num)
theorem B1166917 : Blo 1036608 1166917 := bbase (se 4 (by rfl) ⟨109398, by rfl⟩ : syracuseStep 1166917 = 218797) (by norm_num)
theorem B1560149 : Blo 1036608 1560149 := bbase (se 8 (by rfl) ⟨9141, by rfl⟩ : syracuseStep 1560149 = 18283) (by norm_num)
theorem B1166953 : Blo 1036608 1166953 := bbase (se 2 (by rfl) ⟨437607, by rfl⟩ : syracuseStep 1166953 = 875215) (by norm_num)
theorem B1560173 : Blo 1036608 1560173 := bbase (se 3 (by rfl) ⟨292532, by rfl⟩ : syracuseStep 1560173 = 585065) (by norm_num)
theorem B1560197 : Blo 1036608 1560197 := bbase (se 4 (by rfl) ⟨146268, by rfl⟩ : syracuseStep 1560197 = 292537) (by norm_num)
theorem B1166989 : Blo 1036608 1166989 := bbase (se 3 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 1166989 = 437621) (by norm_num)
theorem B9981589 : Blo 1036608 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B1068701 : Blo 1036608 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B1560221 : Blo 1036608 1560221 := bbase (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) (by norm_num)
theorem B1167025 : Blo 1036608 1167025 := bbase (se 2 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 1167025 = 875269) (by norm_num)
theorem B1560245 : Blo 1036608 1560245 := bbase (se 5 (by rfl) ⟨73136, by rfl⟩ : syracuseStep 1560245 = 146273) (by norm_num)
theorem B1560269 : Blo 1036608 1560269 := bbase (se 3 (by rfl) ⟨292550, by rfl⟩ : syracuseStep 1560269 = 585101) (by norm_num)
theorem B1167061 : Blo 1036608 1167061 := bbase (se 7 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 1167061 = 27353) (by norm_num)
theorem B1560293 : Blo 1036608 1560293 := bbase (se 4 (by rfl) ⟨146277, by rfl⟩ : syracuseStep 1560293 = 292555) (by norm_num)
theorem B1167097 : Blo 1036608 1167097 := bbase (se 2 (by rfl) ⟨437661, by rfl⟩ : syracuseStep 1167097 = 875323) (by norm_num)
theorem B1560317 : Blo 1036608 1560317 := bbase (se 3 (by rfl) ⟨292559, by rfl⟩ : syracuseStep 1560317 = 585119) (by norm_num)
theorem B1560341 : Blo 1036608 1560341 := bbase (se 6 (by rfl) ⟨36570, by rfl⟩ : syracuseStep 1560341 = 73141) (by norm_num)
theorem B1167133 : Blo 1036608 1167133 := bbase (se 3 (by rfl) ⟨218837, by rfl⟩ : syracuseStep 1167133 = 437675) (by norm_num)
theorem B1560365 : Blo 1036608 1560365 := bbase (se 3 (by rfl) ⟨292568, by rfl⟩ : syracuseStep 1560365 = 585137) (by norm_num)
theorem B1167169 : Blo 1036608 1167169 := bbase (se 2 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 1167169 = 875377) (by norm_num)
theorem B1560389 : Blo 1036608 1560389 := bbase (se 4 (by rfl) ⟨146286, by rfl⟩ : syracuseStep 1560389 = 292573) (by norm_num)
theorem B2215765 : Blo 1036608 2215765 := bbase (se 9 (by rfl) ⟨6491, by rfl⟩ : syracuseStep 2215765 = 12983) (by norm_num)
theorem B1560413 : Blo 1036608 1560413 := bbase (se 3 (by rfl) ⟨292577, by rfl⟩ : syracuseStep 1560413 = 585155) (by norm_num)
theorem B1167205 : Blo 1036608 1167205 := bbase (se 4 (by rfl) ⟨109425, by rfl⟩ : syracuseStep 1167205 = 218851) (by norm_num)
theorem B1560437 : Blo 1036608 1560437 := bbase (se 5 (by rfl) ⟨73145, by rfl⟩ : syracuseStep 1560437 = 146291) (by norm_num)
theorem B1167241 : Blo 1036608 1167241 := bbase (se 2 (by rfl) ⟨437715, by rfl⟩ : syracuseStep 1167241 = 875431) (by norm_num)
theorem B1560461 : Blo 1036608 1560461 := bbase (se 3 (by rfl) ⟨292586, by rfl⟩ : syracuseStep 1560461 = 585173) (by norm_num)
theorem B1560485 : Blo 1036608 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B1167277 : Blo 1036608 1167277 := bbase (se 3 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 1167277 = 437729) (by norm_num)
theorem B1560509 : Blo 1036608 1560509 := bbase (se 3 (by rfl) ⟨292595, by rfl⟩ : syracuseStep 1560509 = 585191) (by norm_num)
theorem B1167313 : Blo 1036608 1167313 := bbase (se 2 (by rfl) ⟨437742, by rfl⟩ : syracuseStep 1167313 = 875485) (by norm_num)
theorem B1560533 : Blo 1036608 1560533 := bbase (se 7 (by rfl) ⟨18287, by rfl⟩ : syracuseStep 1560533 = 36575) (by norm_num)
theorem B1560557 : Blo 1036608 1560557 := bbase (se 3 (by rfl) ⟨292604, by rfl⟩ : syracuseStep 1560557 = 585209) (by norm_num)
theorem B1167349 : Blo 1036608 1167349 := bbase (se 5 (by rfl) ⟨54719, by rfl⟩ : syracuseStep 1167349 = 109439) (by norm_num)
theorem B1560581 : Blo 1036608 1560581 := bbase (se 4 (by rfl) ⟨146304, by rfl⟩ : syracuseStep 1560581 = 292609) (by norm_num)
theorem B1167385 : Blo 1036608 1167385 := bbase (se 2 (by rfl) ⟨437769, by rfl⟩ : syracuseStep 1167385 = 875539) (by norm_num)
theorem B1560605 : Blo 1036608 1560605 := bbase (se 3 (by rfl) ⟨292613, by rfl⟩ : syracuseStep 1560605 = 585227) (by norm_num)
theorem B1560629 : Blo 1036608 1560629 := bbase (se 5 (by rfl) ⟨73154, by rfl⟩ : syracuseStep 1560629 = 146309) (by norm_num)
theorem B1167421 : Blo 1036608 1167421 := bbase (se 3 (by rfl) ⟨218891, by rfl⟩ : syracuseStep 1167421 = 437783) (by norm_num)
theorem B1560653 : Blo 1036608 1560653 := bbase (se 3 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 1560653 = 585245) (by norm_num)
theorem B1167457 : Blo 1036608 1167457 := bbase (se 2 (by rfl) ⟨437796, by rfl⟩ : syracuseStep 1167457 = 875593) (by norm_num)
theorem B1560677 : Blo 1036608 1560677 := bbase (se 4 (by rfl) ⟨146313, by rfl⟩ : syracuseStep 1560677 = 292627) (by norm_num)
theorem B1560701 : Blo 1036608 1560701 := bbase (se 3 (by rfl) ⟨292631, by rfl⟩ : syracuseStep 1560701 = 585263) (by norm_num)
theorem B1167493 : Blo 1036608 1167493 := bbase (se 4 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 1167493 = 218905) (by norm_num)
theorem B1560725 : Blo 1036608 1560725 := bbase (se 6 (by rfl) ⟨36579, by rfl⟩ : syracuseStep 1560725 = 73159) (by norm_num)
theorem B1167529 : Blo 1036608 1167529 := bbase (se 2 (by rfl) ⟨437823, by rfl⟩ : syracuseStep 1167529 = 875647) (by norm_num)
theorem B1560749 : Blo 1036608 1560749 := bbase (se 3 (by rfl) ⟨292640, by rfl⟩ : syracuseStep 1560749 = 585281) (by norm_num)
theorem B5263541 : Blo 1036608 5263541 := bbase (se 5 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 5263541 = 493457) (by norm_num)
theorem B1560773 : Blo 1036608 1560773 := bbase (se 4 (by rfl) ⟨146322, by rfl⟩ : syracuseStep 1560773 = 292645) (by norm_num)
theorem B1167565 : Blo 1036608 1167565 := bbase (se 3 (by rfl) ⟨218918, by rfl⟩ : syracuseStep 1167565 = 437837) (by norm_num)
theorem B5918933 : Blo 1036608 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B1560797 : Blo 1036608 1560797 := bbase (se 3 (by rfl) ⟨292649, by rfl⟩ : syracuseStep 1560797 = 585299) (by norm_num)
theorem B1167601 : Blo 1036608 1167601 := bbase (se 2 (by rfl) ⟨437850, by rfl⟩ : syracuseStep 1167601 = 875701) (by norm_num)
theorem B1560821 : Blo 1036608 1560821 := bbase (se 5 (by rfl) ⟨73163, by rfl⟩ : syracuseStep 1560821 = 146327) (by norm_num)
theorem B1560845 : Blo 1036608 1560845 := bbase (se 3 (by rfl) ⟨292658, by rfl⟩ : syracuseStep 1560845 = 585317) (by norm_num)
theorem B1167637 : Blo 1036608 1167637 := bbase (se 6 (by rfl) ⟨27366, by rfl⟩ : syracuseStep 1167637 = 54733) (by norm_num)
theorem B1560869 : Blo 1036608 1560869 := bbase (se 4 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 1560869 = 292663) (by norm_num)
theorem B8868149 : Blo 1036608 8868149 := bbase (se 5 (by rfl) ⟨415694, by rfl⟩ : syracuseStep 8868149 = 831389) (by norm_num)
theorem B1167673 : Blo 1036608 1167673 := bbase (se 2 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 1167673 = 875755) (by norm_num)
theorem B1560893 : Blo 1036608 1560893 := bbase (se 3 (by rfl) ⟨292667, by rfl⟩ : syracuseStep 1560893 = 585335) (by norm_num)
theorem B1167709 : Blo 1036608 1167709 := bbase (se 3 (by rfl) ⟨218945, by rfl⟩ : syracuseStep 1167709 = 437891) (by norm_num)
theorem B1167745 : Blo 1036608 1167745 := bbase (se 2 (by rfl) ⟨437904, by rfl⟩ : syracuseStep 1167745 = 875809) (by norm_num)
theorem B1167781 : Blo 1036608 1167781 := bbase (se 4 (by rfl) ⟨109479, by rfl⟩ : syracuseStep 1167781 = 218959) (by norm_num)
theorem B1167817 : Blo 1036608 1167817 := bbase (se 2 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 1167817 = 875863) (by norm_num)
theorem B3330517 : Blo 1036608 3330517 := bbase (se 7 (by rfl) ⟨39029, by rfl⟩ : syracuseStep 3330517 = 78059) (by norm_num)
theorem B1167853 : Blo 1036608 1167853 := bbase (se 3 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 1167853 = 437945) (by norm_num)
theorem B1167889 : Blo 1036608 1167889 := bbase (se 2 (by rfl) ⟨437958, by rfl⟩ : syracuseStep 1167889 = 875917) (by norm_num)
theorem B1167925 : Blo 1036608 1167925 := bbase (se 5 (by rfl) ⟨54746, by rfl⟩ : syracuseStep 1167925 = 109493) (by norm_num)
theorem B1167961 : Blo 1036608 1167961 := bbase (se 2 (by rfl) ⟨437985, by rfl⟩ : syracuseStep 1167961 = 875971) (by norm_num)
theorem B4215397 : Blo 1036608 4215397 := bbase (se 4 (by rfl) ⟨395193, by rfl⟩ : syracuseStep 4215397 = 790387) (by norm_num)
theorem B1167997 : Blo 1036608 1167997 := bbase (se 3 (by rfl) ⟨218999, by rfl⟩ : syracuseStep 1167997 = 437999) (by norm_num)
theorem B1168033 : Blo 1036608 1168033 := bbase (se 2 (by rfl) ⟨438012, by rfl⟩ : syracuseStep 1168033 = 876025) (by norm_num)
theorem B1168069 : Blo 1036608 1168069 := bbase (se 4 (by rfl) ⟨109506, by rfl⟩ : syracuseStep 1168069 = 219013) (by norm_num)
theorem B2806501 : Blo 1036608 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B1168105 : Blo 1036608 1168105 := bbase (se 2 (by rfl) ⟨438039, by rfl⟩ : syracuseStep 1168105 = 876079) (by norm_num)
theorem B1168141 : Blo 1036608 1168141 := bbase (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) (by norm_num)
theorem B1168177 : Blo 1036608 1168177 := bbase (se 2 (by rfl) ⟨438066, by rfl⟩ : syracuseStep 1168177 = 876133) (by norm_num)
theorem B1168213 : Blo 1036608 1168213 := bbase (se 9 (by rfl) ⟨3422, by rfl⟩ : syracuseStep 1168213 = 6845) (by norm_num)
theorem B1168249 : Blo 1036608 1168249 := bbase (se 2 (by rfl) ⟨438093, by rfl⟩ : syracuseStep 1168249 = 876187) (by norm_num)
theorem B1168285 : Blo 1036608 1168285 := bbase (se 3 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 1168285 = 438107) (by norm_num)
theorem B1168321 : Blo 1036608 1168321 := bbase (se 2 (by rfl) ⟨438120, by rfl⟩ : syracuseStep 1168321 = 876241) (by norm_num)
theorem B1332193 : Blo 1036608 1332193 := bbase (se 2 (by rfl) ⟨499572, by rfl⟩ : syracuseStep 1332193 = 999145) (by norm_num)
theorem B1168357 : Blo 1036608 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B1168393 : Blo 1036608 1168393 := bbase (se 2 (by rfl) ⟨438147, by rfl⟩ : syracuseStep 1168393 = 876295) (by norm_num)
theorem B2806805 : Blo 1036608 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B1168429 : Blo 1036608 1168429 := bbase (se 3 (by rfl) ⟨219080, by rfl⟩ : syracuseStep 1168429 = 438161) (by norm_num)
theorem B1168465 : Blo 1036608 1168465 := bbase (se 2 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 1168465 = 876349) (by norm_num)
theorem B1168501 : Blo 1036608 1168501 := bbase (se 5 (by rfl) ⟨54773, by rfl⟩ : syracuseStep 1168501 = 109547) (by norm_num)
theorem B1168537 : Blo 1036608 1168537 := bbase (se 2 (by rfl) ⟨438201, by rfl⟩ : syracuseStep 1168537 = 876403) (by norm_num)
theorem B1168573 : Blo 1036608 1168573 := bbase (se 3 (by rfl) ⟨219107, by rfl⟩ : syracuseStep 1168573 = 438215) (by norm_num)
theorem B1168609 : Blo 1036608 1168609 := bbase (se 2 (by rfl) ⟨438228, by rfl⟩ : syracuseStep 1168609 = 876457) (by norm_num)
theorem B1168645 : Blo 1036608 1168645 := bbase (se 4 (by rfl) ⟨109560, by rfl⟩ : syracuseStep 1168645 = 219121) (by norm_num)
theorem B1168681 : Blo 1036608 1168681 := bbase (se 2 (by rfl) ⟨438255, by rfl⟩ : syracuseStep 1168681 = 876511) (by norm_num)
theorem B2217269 : Blo 1036608 2217269 := bbase (se 5 (by rfl) ⟨103934, by rfl⟩ : syracuseStep 2217269 = 207869) (by norm_num)
theorem B1168717 : Blo 1036608 1168717 := bbase (se 3 (by rfl) ⟨219134, by rfl⟩ : syracuseStep 1168717 = 438269) (by norm_num)
theorem B1168753 : Blo 1036608 1168753 := bbase (se 2 (by rfl) ⟨438282, by rfl⟩ : syracuseStep 1168753 = 876565) (by norm_num)
theorem B1168789 : Blo 1036608 1168789 := bbase (se 6 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 1168789 = 54787) (by norm_num)
theorem B1168825 : Blo 1036608 1168825 := bbase (se 2 (by rfl) ⟨438309, by rfl⟩ : syracuseStep 1168825 = 876619) (by norm_num)
theorem B2217413 : Blo 1036608 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B2807237 : Blo 1036608 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B5264837 : Blo 1036608 5264837 := bbase (se 4 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 5264837 = 987157) (by norm_num)
theorem B1168861 : Blo 1036608 1168861 := bbase (se 3 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 1168861 = 438323) (by norm_num)
theorem B1168897 : Blo 1036608 1168897 := bbase (se 2 (by rfl) ⟨438336, by rfl⟩ : syracuseStep 1168897 = 876673) (by norm_num)
theorem B1168933 : Blo 1036608 1168933 := bbase (se 4 (by rfl) ⟨109587, by rfl⟩ : syracuseStep 1168933 = 219175) (by norm_num)
theorem B1332793 : Blo 1036608 1332793 := bbase (se 2 (by rfl) ⟨499797, by rfl⟩ : syracuseStep 1332793 = 999595) (by norm_num)
theorem B1168969 : Blo 1036608 1168969 := bbase (se 2 (by rfl) ⟨438363, by rfl⟩ : syracuseStep 1168969 = 876727) (by norm_num)
theorem B1169005 : Blo 1036608 1169005 := bbase (se 3 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 1169005 = 438377) (by norm_num)
theorem B1169041 : Blo 1036608 1169041 := bbase (se 2 (by rfl) ⟨438390, by rfl⟩ : syracuseStep 1169041 = 876781) (by norm_num)
theorem B1169077 : Blo 1036608 1169077 := bbase (se 5 (by rfl) ⟨54800, by rfl⟩ : syracuseStep 1169077 = 109601) (by norm_num)
theorem B1169113 : Blo 1036608 1169113 := bbase (se 2 (by rfl) ⟨438417, by rfl⟩ : syracuseStep 1169113 = 876835) (by norm_num)
theorem B1169149 : Blo 1036608 1169149 := bbase (se 3 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 1169149 = 438431) (by norm_num)
theorem B1169185 : Blo 1036608 1169185 := bbase (se 2 (by rfl) ⟨438444, by rfl⟩ : syracuseStep 1169185 = 876889) (by norm_num)
theorem B2217773 : Blo 1036608 2217773 := bbase (se 3 (by rfl) ⟨415832, by rfl⟩ : syracuseStep 2217773 = 831665) (by norm_num)
theorem B1169221 : Blo 1036608 1169221 := bbase (se 4 (by rfl) ⟨109614, by rfl⟩ : syracuseStep 1169221 = 219229) (by norm_num)
theorem B1169257 : Blo 1036608 1169257 := bbase (se 2 (by rfl) ⟨438471, by rfl⟩ : syracuseStep 1169257 = 876943) (by norm_num)
theorem B1660805 : Blo 1036608 1660805 := bbase (se 4 (by rfl) ⟨155700, by rfl⟩ : syracuseStep 1660805 = 311401) (by norm_num)
theorem B1169293 : Blo 1036608 1169293 := bbase (se 3 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 1169293 = 438485) (by norm_num)
theorem B1169329 : Blo 1036608 1169329 := bbase (se 2 (by rfl) ⟨438498, by rfl⟩ : syracuseStep 1169329 = 876997) (by norm_num)
theorem B1169365 : Blo 1036608 1169365 := bbase (se 7 (by rfl) ⟨13703, by rfl⟩ : syracuseStep 1169365 = 27407) (by norm_num)
theorem B1169401 : Blo 1036608 1169401 := bbase (se 2 (by rfl) ⟨438525, by rfl⟩ : syracuseStep 1169401 = 877051) (by norm_num)
theorem B1660933 : Blo 1036608 1660933 := bbase (se 4 (by rfl) ⟨155712, by rfl⟩ : syracuseStep 1660933 = 311425) (by norm_num)
theorem B3332117 : Blo 1036608 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B1169437 : Blo 1036608 1169437 := bbase (se 3 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 1169437 = 438539) (by norm_num)
theorem B1169473 : Blo 1036608 1169473 := bbase (se 2 (by rfl) ⟨438552, by rfl⟩ : syracuseStep 1169473 = 877105) (by norm_num)
theorem B1169509 : Blo 1036608 1169509 := bbase (se 4 (by rfl) ⟨109641, by rfl⟩ : syracuseStep 1169509 = 219283) (by norm_num)
theorem B1169545 : Blo 1036608 1169545 := bbase (se 2 (by rfl) ⟨438579, by rfl⟩ : syracuseStep 1169545 = 877159) (by norm_num)
theorem B1169581 : Blo 1036608 1169581 := bbase (se 3 (by rfl) ⟨219296, by rfl⟩ : syracuseStep 1169581 = 438593) (by norm_num)
theorem B1169617 : Blo 1036608 1169617 := bbase (se 2 (by rfl) ⟨438606, by rfl⟩ : syracuseStep 1169617 = 877213) (by norm_num)
theorem B1169653 : Blo 1036608 1169653 := bbase (se 5 (by rfl) ⟨54827, by rfl⟩ : syracuseStep 1169653 = 109655) (by norm_num)
theorem B11229461 : Blo 1036608 11229461 := bbase (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) (by norm_num)
theorem B1169689 : Blo 1036608 1169689 := bbase (se 2 (by rfl) ⟨438633, by rfl⟩ : syracuseStep 1169689 = 877267) (by norm_num)
theorem B1169725 : Blo 1036608 1169725 := bbase (se 3 (by rfl) ⟨219323, by rfl⟩ : syracuseStep 1169725 = 438647) (by norm_num)
theorem B1333589 : Blo 1036608 1333589 := bbase (se 10 (by rfl) ⟨1953, by rfl⟩ : syracuseStep 1333589 = 3907) (by norm_num)
theorem B1169761 : Blo 1036608 1169761 := bbase (se 2 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 1169761 = 877321) (by norm_num)
theorem B1169797 : Blo 1036608 1169797 := bbase (se 4 (by rfl) ⟨109668, by rfl⟩ : syracuseStep 1169797 = 219337) (by norm_num)
theorem B1169833 : Blo 1036608 1169833 := bbase (se 2 (by rfl) ⟨438687, by rfl⟩ : syracuseStep 1169833 = 877375) (by norm_num)
theorem B1169869 : Blo 1036608 1169869 := bbase (se 3 (by rfl) ⟨219350, by rfl⟩ : syracuseStep 1169869 = 438701) (by norm_num)
theorem B1169905 : Blo 1036608 1169905 := bbase (se 2 (by rfl) ⟨438714, by rfl⟩ : syracuseStep 1169905 = 877429) (by norm_num)
theorem B2808341 : Blo 1036608 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B1169941 : Blo 1036608 1169941 := bbase (se 6 (by rfl) ⟨27420, by rfl⟩ : syracuseStep 1169941 = 54841) (by norm_num)
theorem B1169977 : Blo 1036608 1169977 := bbase (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) (by norm_num)
theorem B1170013 : Blo 1036608 1170013 := bbase (se 3 (by rfl) ⟨219377, by rfl⟩ : syracuseStep 1170013 = 438755) (by norm_num)
theorem B1170049 : Blo 1036608 1170049 := bbase (se 2 (by rfl) ⟨438768, by rfl⟩ : syracuseStep 1170049 = 877537) (by norm_num)
theorem B2218661 : Blo 1036608 2218661 := bbase (se 4 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 2218661 = 415999) (by norm_num)
theorem B1170085 : Blo 1036608 1170085 := bbase (se 4 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 1170085 = 219391) (by norm_num)
theorem B1170121 : Blo 1036608 1170121 := bbase (se 2 (by rfl) ⟨438795, by rfl⟩ : syracuseStep 1170121 = 877591) (by norm_num)
theorem B2251477 : Blo 1036608 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B5266133 : Blo 1036608 5266133 := bbase (se 7 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 5266133 = 123425) (by norm_num)
theorem B1170157 : Blo 1036608 1170157 := bbase (se 3 (by rfl) ⟨219404, by rfl⟩ : syracuseStep 1170157 = 438809) (by norm_num)
theorem B1170193 : Blo 1036608 1170193 := bbase (se 2 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 1170193 = 877645) (by norm_num)
theorem B1170229 : Blo 1036608 1170229 := bbase (se 5 (by rfl) ⟨54854, by rfl⟩ : syracuseStep 1170229 = 109709) (by norm_num)
theorem B1334081 : Blo 1036608 1334081 := bbase (se 2 (by rfl) ⟨500280, by rfl⟩ : syracuseStep 1334081 = 1000561) (by norm_num)
theorem B1170265 : Blo 1036608 1170265 := bbase (se 2 (by rfl) ⟨438849, by rfl⟩ : syracuseStep 1170265 = 877699) (by norm_num)
theorem B1170301 : Blo 1036608 1170301 := bbase (se 3 (by rfl) ⟨219431, by rfl⟩ : syracuseStep 1170301 = 438863) (by norm_num)
theorem B2218909 : Blo 1036608 2218909 := bbase (se 3 (by rfl) ⟨416045, by rfl⟩ : syracuseStep 2218909 = 832091) (by norm_num)
theorem B1923997 : Blo 1036608 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B1170337 : Blo 1036608 1170337 := bbase (se 2 (by rfl) ⟨438876, by rfl⟩ : syracuseStep 1170337 = 877753) (by norm_num)
theorem B1170373 : Blo 1036608 1170373 := bbase (se 4 (by rfl) ⟨109722, by rfl⟩ : syracuseStep 1170373 = 219445) (by norm_num)
theorem B1170409 : Blo 1036608 1170409 := bbase (se 2 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 1170409 = 877807) (by norm_num)
theorem B1661933 : Blo 1036608 1661933 := bbase (se 3 (by rfl) ⟨311612, by rfl⟩ : syracuseStep 1661933 = 623225) (by norm_num)
theorem B1170445 : Blo 1036608 1170445 := bbase (se 3 (by rfl) ⟨219458, by rfl⟩ : syracuseStep 1170445 = 438917) (by norm_num)
theorem B1170481 : Blo 1036608 1170481 := bbase (se 2 (by rfl) ⟨438930, by rfl⟩ : syracuseStep 1170481 = 877861) (by norm_num)
theorem B1170517 : Blo 1036608 1170517 := bbase (se 8 (by rfl) ⟨6858, by rfl⟩ : syracuseStep 1170517 = 13717) (by norm_num)
theorem B3333221 : Blo 1036608 3333221 := bbase (se 4 (by rfl) ⟨312489, by rfl⟩ : syracuseStep 3333221 = 624979) (by norm_num)
theorem B1662061 : Blo 1036608 1662061 := bbase (se 3 (by rfl) ⟨311636, by rfl⟩ : syracuseStep 1662061 = 623273) (by norm_num)
theorem B1170553 : Blo 1036608 1170553 := bbase (se 2 (by rfl) ⟨438957, by rfl⟩ : syracuseStep 1170553 = 877915) (by norm_num)
theorem B1170589 : Blo 1036608 1170589 := bbase (se 3 (by rfl) ⟨219485, by rfl⟩ : syracuseStep 1170589 = 438971) (by norm_num)
theorem B1170625 : Blo 1036608 1170625 := bbase (se 2 (by rfl) ⟨438984, by rfl⟩ : syracuseStep 1170625 = 877969) (by norm_num)
theorem B1170661 : Blo 1036608 1170661 := bbase (se 4 (by rfl) ⟨109749, by rfl⟩ : syracuseStep 1170661 = 219499) (by norm_num)
theorem B2219413 : Blo 1036608 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B1662445 : Blo 1036608 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B1334845 : Blo 1036608 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B3595877 : Blo 1036608 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B1334917 : Blo 1036608 1334917 := bbase (se 4 (by rfl) ⟨125148, by rfl⟩ : syracuseStep 1334917 = 250297) (by norm_num)
theorem B1662701 : Blo 1036608 1662701 := bbase (se 3 (by rfl) ⟨311756, by rfl⟩ : syracuseStep 1662701 = 623513) (by norm_num)
theorem B3366773 : Blo 1036608 3366773 := bbase (se 5 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 3366773 = 315635) (by norm_num)
theorem B5267429 : Blo 1036608 5267429 := bbase (se 4 (by rfl) ⟨493821, by rfl⟩ : syracuseStep 5267429 = 987643) (by norm_num)
theorem B1401013 : Blo 1036608 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B2220301 : Blo 1036608 2220301 := bbase (se 3 (by rfl) ⟨416306, by rfl⟩ : syracuseStep 2220301 = 832613) (by norm_num)
theorem B1597781 : Blo 1036608 1597781 := bbase (se 10 (by rfl) ⟨2340, by rfl⟩ : syracuseStep 1597781 = 4681) (by norm_num)
theorem B7889237 : Blo 1036608 7889237 := bbase (se 10 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 7889237 = 23113) (by norm_num)
theorem B1401229 : Blo 1036608 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B1663573 : Blo 1036608 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B1663669 : Blo 1036608 1663669 := bbase (se 5 (by rfl) ⟨77984, by rfl⟩ : syracuseStep 1663669 = 155969) (by norm_num)
theorem B2220797 : Blo 1036608 2220797 := bbase (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) (by norm_num)
theorem B6644501 : Blo 1036608 6644501 := bbase (se 6 (by rfl) ⟨155730, by rfl⟩ : syracuseStep 6644501 = 311461) (by norm_num)
theorem B3498821 : Blo 1036608 3498821 := bbase (se 4 (by rfl) ⟨328014, by rfl⟩ : syracuseStep 3498821 = 656029) (by norm_num)
theorem B1663829 : Blo 1036608 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B3990421 : Blo 1036608 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B1500061 : Blo 1036608 1500061 := bbase (se 3 (by rfl) ⟨281261, by rfl⟩ : syracuseStep 1500061 = 562523) (by norm_num)
theorem B1926317 : Blo 1036608 1926317 := bbase (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) (by norm_num)
theorem B1369325 : Blo 1036608 1369325 := bbase (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) (by norm_num)
theorem B3499253 : Blo 1036608 3499253 := bbase (se 5 (by rfl) ⟨164027, by rfl⟩ : syracuseStep 3499253 = 328055) (by norm_num)
theorem B1402213 : Blo 1036608 1402213 := bbase (se 4 (by rfl) ⟨131457, by rfl⟩ : syracuseStep 1402213 = 262915) (by norm_num)
theorem B4744565 : Blo 1036608 4744565 := bbase (se 5 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 4744565 = 444803) (by norm_num)
theorem B1107541 : Blo 1036608 1107541 := bbase (se 8 (by rfl) ⟨6489, by rfl⟩ : syracuseStep 1107541 = 12979) (by norm_num)
theorem B2221685 : Blo 1036608 2221685 := bbase (se 5 (by rfl) ⟨104141, by rfl⟩ : syracuseStep 2221685 = 208283) (by norm_num)
theorem B1107613 : Blo 1036608 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B3499685 : Blo 1036608 3499685 := bbase (se 4 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 3499685 = 656191) (by norm_num)
theorem B2221805 : Blo 1036608 2221805 := bbase (se 3 (by rfl) ⟨416588, by rfl⟩ : syracuseStep 2221805 = 833177) (by norm_num)
theorem B1402645 : Blo 1036608 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B9987893 : Blo 1036608 9987893 := bbase (se 5 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 9987893 = 936365) (by norm_num)
theorem B1107793 : Blo 1036608 1107793 := bbase (se 2 (by rfl) ⟨415422, by rfl⟩ : syracuseStep 1107793 = 830845) (by norm_num)
theorem B1664957 : Blo 1036608 1664957 := bbase (se 3 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 1664957 = 624359) (by norm_num)
theorem B3500117 : Blo 1036608 3500117 := bbase (se 8 (by rfl) ⟨20508, by rfl⟩ : syracuseStep 3500117 = 41017) (by norm_num)
theorem B1108237 : Blo 1036608 1108237 := bbase (se 3 (by rfl) ⟨207794, by rfl⟩ : syracuseStep 1108237 = 415589) (by norm_num)
theorem B4811093 : Blo 1036608 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B2222437 : Blo 1036608 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B1108361 : Blo 1036608 1108361 := bbase (se 2 (by rfl) ⟨415635, by rfl⟩ : syracuseStep 1108361 = 831271) (by norm_num)
theorem B1665469 : Blo 1036608 1665469 := bbase (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) (by norm_num)
theorem B3500549 : Blo 1036608 3500549 := bbase (se 4 (by rfl) ⟨328176, by rfl⟩ : syracuseStep 3500549 = 656353) (by norm_num)
theorem B1108613 : Blo 1036608 1108613 := bbase (se 4 (by rfl) ⟨103932, by rfl⟩ : syracuseStep 1108613 = 207865) (by norm_num)
theorem B3500981 : Blo 1036608 3500981 := bbase (se 5 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 3500981 = 328217) (by norm_num)
theorem B1109057 : Blo 1036608 1109057 := bbase (se 2 (by rfl) ⟨415896, by rfl⟩ : syracuseStep 1109057 = 831793) (by norm_num)
theorem B1109305 : Blo 1036608 1109305 := bbase (se 2 (by rfl) ⟨415989, by rfl⟩ : syracuseStep 1109305 = 831979) (by norm_num)
theorem B3501413 : Blo 1036608 3501413 := bbase (se 4 (by rfl) ⟨328257, by rfl⟩ : syracuseStep 3501413 = 656515) (by norm_num)
theorem B1666469 : Blo 1036608 1666469 := bbase (se 4 (by rfl) ⟨156231, by rfl⟩ : syracuseStep 1666469 = 312463) (by norm_num)
theorem B1666597 : Blo 1036608 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B1666661 : Blo 1036608 1666661 := bbase (se 4 (by rfl) ⟨156249, by rfl⟩ : syracuseStep 1666661 = 312499) (by norm_num)
theorem B1109749 : Blo 1036608 1109749 := bbase (se 5 (by rfl) ⟨52019, by rfl⟩ : syracuseStep 1109749 = 104039) (by norm_num)
theorem B3501845 : Blo 1036608 3501845 := bbase (se 6 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 3501845 = 164149) (by norm_num)
theorem B1109809 : Blo 1036608 1109809 := bbase (se 2 (by rfl) ⟨416178, by rfl⟩ : syracuseStep 1109809 = 832357) (by norm_num)
theorem B7499573 : Blo 1036608 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B1110125 : Blo 1036608 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1405045 : Blo 1036608 1405045 := bbase (se 5 (by rfl) ⟨65861, by rfl⟩ : syracuseStep 1405045 = 131723) (by norm_num)
theorem B8876213 : Blo 1036608 8876213 := bbase (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) (by norm_num)
theorem B3502277 : Blo 1036608 3502277 := bbase (se 4 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 3502277 = 656677) (by norm_num)
theorem B1110569 : Blo 1036608 1110569 := bbase (se 2 (by rfl) ⟨416463, by rfl⟩ : syracuseStep 1110569 = 832927) (by norm_num)
theorem B1110629 : Blo 1036608 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B3502709 : Blo 1036608 3502709 := bbase (se 5 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 3502709 = 328379) (by norm_num)
theorem B1110757 : Blo 1036608 1110757 := bbase (se 4 (by rfl) ⟨104133, by rfl⟩ : syracuseStep 1110757 = 208267) (by norm_num)
theorem B2028341 : Blo 1036608 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B3503141 : Blo 1036608 3503141 := bbase (se 4 (by rfl) ⟨328419, by rfl⟩ : syracuseStep 3503141 = 656839) (by norm_num)
theorem B1406101 : Blo 1036608 1406101 := bbase (se 6 (by rfl) ⟨32955, by rfl⟩ : syracuseStep 1406101 = 65911) (by norm_num)
theorem B1111201 : Blo 1036608 1111201 := bbase (se 2 (by rfl) ⟨416700, by rfl⟩ : syracuseStep 1111201 = 833401) (by norm_num)
theorem B1406317 : Blo 1036608 1406317 := bbase (se 3 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 1406317 = 527369) (by norm_num)
theorem B3503573 : Blo 1036608 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B1996589 : Blo 1036608 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B3504005 : Blo 1036608 3504005 := bbase (se 4 (by rfl) ⟨328500, by rfl⟩ : syracuseStep 3504005 = 657001) (by norm_num)
theorem B3504437 : Blo 1036608 3504437 := bbase (se 5 (by rfl) ⟨164270, by rfl⟩ : syracuseStep 3504437 = 328541) (by norm_num)
theorem B1899173 : Blo 1036608 1899173 := bbase (se 4 (by rfl) ⟨178047, by rfl⟩ : syracuseStep 1899173 = 356095) (by norm_num)
theorem B3504869 : Blo 1036608 3504869 := bbase (se 4 (by rfl) ⟨328581, by rfl⟩ : syracuseStep 3504869 = 657163) (by norm_num)
theorem B3505301 : Blo 1036608 3505301 := bbase (se 6 (by rfl) ⟨82155, by rfl⟩ : syracuseStep 3505301 = 164311) (by norm_num)
theorem B3505733 : Blo 1036608 3505733 := bbase (se 4 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 3505733 = 657325) (by norm_num)
theorem B7897013 : Blo 1036608 7897013 := bbase (se 5 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 7897013 = 740345) (by norm_num)
theorem B3506165 : Blo 1036608 3506165 := bbase (se 5 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 3506165 = 328703) (by norm_num)
theorem B3506381 : Blo 1036608 3506381 := bstep (se 3 (by rfl) ⟨657446, by rfl⟩ : syracuseStep 3506381 = 1314893) B1314893
theorem B1868017 : Blo 1036608 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B3506435 : Blo 1036608 3506435 := bstep (se 1 (by rfl) ⟨2629826, by rfl⟩ : syracuseStep 3506435 = 5259653) B5259653
theorem B3506705 : Blo 1036608 3506705 := bstep (se 2 (by rfl) ⟨1315014, by rfl⟩ : syracuseStep 3506705 = 2630029) B2630029
theorem B1999651 : Blo 1036608 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B3507245 : Blo 1036608 3507245 := bstep (se 3 (by rfl) ⟨657608, by rfl⟩ : syracuseStep 3507245 = 1315217) B1315217
theorem B3507299 : Blo 1036608 3507299 := bstep (se 1 (by rfl) ⟨2630474, by rfl⟩ : syracuseStep 3507299 = 5260949) B5260949
theorem B2000081 : Blo 1036608 2000081 := bstep (se 2 (by rfl) ⟨750030, by rfl⟩ : syracuseStep 2000081 = 1500061) B1500061
theorem B10650851 : Blo 1036608 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B3507569 : Blo 1036608 3507569 := bstep (se 2 (by rfl) ⟨1315338, by rfl⟩ : syracuseStep 3507569 = 2630677) B2630677
theorem B1312195 : Blo 1036608 1312195 := bstep (se 1 (by rfl) ⟨984146, by rfl⟩ : syracuseStep 1312195 = 1968293) B1968293
theorem B8881649 : Blo 1036608 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B1476083 : Blo 1036608 1476083 := bstep (se 1 (by rfl) ⟨1107062, by rfl⟩ : syracuseStep 1476083 = 2214125) B2214125
theorem B1312291 : Blo 1036608 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B6653573 : Blo 1036608 6653573 := bstep (se 4 (by rfl) ⟨623772, by rfl⟩ : syracuseStep 6653573 = 1247545) B1247545
theorem B1869617 : Blo 1036608 1869617 := bstep (se 2 (by rfl) ⟨701106, by rfl⟩ : syracuseStep 1869617 = 1402213) B1402213
theorem B3508109 : Blo 1036608 3508109 := bstep (se 3 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 3508109 = 1315541) B1315541
theorem B4982705 : Blo 1036608 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B3508163 : Blo 1036608 3508163 := bstep (se 1 (by rfl) ⟨2631122, by rfl⟩ : syracuseStep 3508163 = 5262245) B5262245
theorem B7112717 : Blo 1036608 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B1312787 : Blo 1036608 1312787 := bstep (se 1 (by rfl) ⟨984590, by rfl⟩ : syracuseStep 1312787 = 1969181) B1969181
theorem B7473221 : Blo 1036608 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1968209 : Blo 1036608 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B1476721 : Blo 1036608 1476721 := bstep (se 2 (by rfl) ⟨553770, by rfl⟩ : syracuseStep 1476721 = 1107541) B1107541
theorem B3508433 : Blo 1036608 3508433 := bstep (se 2 (by rfl) ⟨1315662, by rfl⟩ : syracuseStep 3508433 = 2631325) B2631325
theorem B1870193 : Blo 1036608 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B1050995 : Blo 1036608 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B1477057 : Blo 1036608 1477057 := bstep (se 2 (by rfl) ⟨553896, by rfl⟩ : syracuseStep 1477057 = 1107793) B1107793
theorem B2623985 : Blo 1036608 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B2624035 : Blo 1036608 2624035 := bstep (se 1 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 2624035 = 3936053) B3936053
theorem B1247843 : Blo 1036608 1247843 := bstep (se 1 (by rfl) ⟨935882, by rfl⟩ : syracuseStep 1247843 = 1871765) B1871765
theorem B2624177 : Blo 1036608 2624177 := bstep (se 2 (by rfl) ⟨984066, by rfl⟩ : syracuseStep 2624177 = 1968133) B1968133
theorem B1313491 : Blo 1036608 1313491 := bstep (se 1 (by rfl) ⟨985118, by rfl⟩ : syracuseStep 1313491 = 1970237) B1970237
theorem B3508973 : Blo 1036608 3508973 := bstep (se 3 (by rfl) ⟨657932, by rfl⟩ : syracuseStep 3508973 = 1315865) B1315865
theorem B3509027 : Blo 1036608 3509027 := bstep (se 1 (by rfl) ⟨2631770, by rfl⟩ : syracuseStep 3509027 = 5263541) B5263541
theorem B1313587 : Blo 1036608 1313587 := bstep (se 1 (by rfl) ⟨985190, by rfl⟩ : syracuseStep 1313587 = 1970381) B1970381
theorem B2493283 : Blo 1036608 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B1182643 : Blo 1036608 1182643 := bstep (se 1 (by rfl) ⟨886982, by rfl⟩ : syracuseStep 1182643 = 1773965) B1773965
theorem B1248179 : Blo 1036608 1248179 := bstep (se 1 (by rfl) ⟨936134, by rfl⟩ : syracuseStep 1248179 = 1872269) B1872269
theorem B1969105 : Blo 1036608 1969105 := bstep (se 2 (by rfl) ⟨738414, by rfl⟩ : syracuseStep 1969105 = 1476829) B1476829
theorem B1477649 : Blo 1036608 1477649 := bstep (se 2 (by rfl) ⟨554118, by rfl⟩ : syracuseStep 1477649 = 1108237) B1108237
theorem B3509297 : Blo 1036608 3509297 := bstep (se 2 (by rfl) ⟨1315986, by rfl⟩ : syracuseStep 3509297 = 2631973) B2631973
theorem B1969265 : Blo 1036608 1969265 := bstep (se 2 (by rfl) ⟨738474, by rfl⟩ : syracuseStep 1969265 = 1476949) B1476949
theorem B1314083 : Blo 1036608 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B1183027 : Blo 1036608 1183027 := bstep (se 1 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 1183027 = 1774541) B1774541
theorem B1871203 : Blo 1036608 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B2493841 : Blo 1036608 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B1969667 : Blo 1036608 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B1052195 : Blo 1036608 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B1478179 : Blo 1036608 1478179 := bstep (se 1 (by rfl) ⟨1108634, by rfl⟩ : syracuseStep 1478179 = 2217269) B2217269
theorem B3509837 : Blo 1036608 3509837 := bstep (se 3 (by rfl) ⟨658094, by rfl⟩ : syracuseStep 3509837 = 1316189) B1316189
theorem B3509891 : Blo 1036608 3509891 := bstep (se 1 (by rfl) ⟨2632418, by rfl⟩ : syracuseStep 3509891 = 5264837) B5264837
theorem B2625169 : Blo 1036608 2625169 := bstep (se 2 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 2625169 = 1968877) B1968877
theorem B1576675 : Blo 1036608 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B1478515 : Blo 1036608 1478515 := bstep (se 1 (by rfl) ⟨1108886, by rfl⟩ : syracuseStep 1478515 = 2217773) B2217773
theorem B3510161 : Blo 1036608 3510161 := bstep (se 2 (by rfl) ⟨1316310, by rfl⟩ : syracuseStep 3510161 = 2632621) B2632621
theorem B2625443 : Blo 1036608 2625443 := bstep (se 1 (by rfl) ⟨1969082, by rfl⟩ : syracuseStep 2625443 = 3938165) B3938165
theorem B2953169 : Blo 1036608 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B1314787 : Blo 1036608 1314787 := bstep (se 1 (by rfl) ⟨986090, by rfl⟩ : syracuseStep 1314787 = 1972181) B1972181
theorem B2494513 : Blo 1036608 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B1314883 : Blo 1036608 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B2625635 : Blo 1036608 2625635 := bstep (se 1 (by rfl) ⟨1969226, by rfl⟩ : syracuseStep 2625635 = 3938453) B3938453
theorem B2953361 : Blo 1036608 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B4985165 : Blo 1036608 4985165 := bstep (se 3 (by rfl) ⟨934718, by rfl⟩ : syracuseStep 4985165 = 1869437) B1869437
theorem B1872227 : Blo 1036608 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B1970563 : Blo 1036608 1970563 := bstep (se 1 (by rfl) ⟨1477922, by rfl⟩ : syracuseStep 1970563 = 2955845) B2955845
theorem B1479073 : Blo 1036608 1479073 := bstep (se 2 (by rfl) ⟨554652, by rfl⟩ : syracuseStep 1479073 = 1109305) B1109305
theorem B3510701 : Blo 1036608 3510701 := bstep (se 3 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 3510701 = 1316513) B1316513
theorem B1479107 : Blo 1036608 1479107 := bstep (se 1 (by rfl) ⟨1109330, by rfl⟩ : syracuseStep 1479107 = 2218661) B2218661
theorem B1577441 : Blo 1036608 1577441 := bstep (se 2 (by rfl) ⟨591540, by rfl⟩ : syracuseStep 1577441 = 1183081) B1183081
theorem B3510755 : Blo 1036608 3510755 := bstep (se 1 (by rfl) ⟨2633066, by rfl⟩ : syracuseStep 3510755 = 5266133) B5266133
theorem B1970723 : Blo 1036608 1970723 := bstep (se 1 (by rfl) ⟨1478042, by rfl⟩ : syracuseStep 1970723 = 2956085) B2956085
theorem B1315379 : Blo 1036608 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B2101891 : Blo 1036608 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B3936995 : Blo 1036608 3936995 := bstep (se 1 (by rfl) ⟨2952746, by rfl⟩ : syracuseStep 3936995 = 5905493) B5905493
theorem B3511025 : Blo 1036608 3511025 := bstep (se 2 (by rfl) ⟨1316634, by rfl⟩ : syracuseStep 3511025 = 2633269) B2633269
theorem B13308785 : Blo 1036608 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B1479665 : Blo 1036608 1479665 := bstep (se 2 (by rfl) ⟨554874, by rfl⟩ : syracuseStep 1479665 = 1109749) B1109749
theorem B2626577 : Blo 1036608 2626577 := bstep (se 2 (by rfl) ⟨984966, by rfl⟩ : syracuseStep 2626577 = 1969933) B1969933
theorem B1479745 : Blo 1036608 1479745 := bstep (se 2 (by rfl) ⟨554904, by rfl⟩ : syracuseStep 1479745 = 1109809) B1109809
theorem B2397251 : Blo 1036608 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B2626627 : Blo 1036608 2626627 := bstep (se 1 (by rfl) ⟨1969970, by rfl⟩ : syracuseStep 2626627 = 3939941) B3939941
theorem B2954353 : Blo 1036608 2954353 := bstep (se 2 (by rfl) ⟨1107882, by rfl⟩ : syracuseStep 2954353 = 2215765) B2215765
theorem B6657137 : Blo 1036608 6657137 := bstep (se 2 (by rfl) ⟨2496426, by rfl⟩ : syracuseStep 6657137 = 4992853) B4992853
theorem B2626769 : Blo 1036608 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B1316083 : Blo 1036608 1316083 := bstep (se 1 (by rfl) ⟨987062, by rfl⟩ : syracuseStep 1316083 = 1974125) B1974125
theorem B3511565 : Blo 1036608 3511565 := bstep (se 3 (by rfl) ⟨658418, by rfl⟩ : syracuseStep 3511565 = 1316837) B1316837
theorem B3511619 : Blo 1036608 3511619 := bstep (se 1 (by rfl) ⟨2633714, by rfl⟩ : syracuseStep 3511619 = 5267429) B5267429
theorem B1316179 : Blo 1036608 1316179 := bstep (se 1 (by rfl) ⟨987134, by rfl⟩ : syracuseStep 1316179 = 1974269) B1974269
theorem B1774963 : Blo 1036608 1774963 := bstep (se 1 (by rfl) ⟨1331222, by rfl⟩ : syracuseStep 1774963 = 2662445) B2662445
theorem B2954627 : Blo 1036608 2954627 := bstep (se 1 (by rfl) ⟨2215970, by rfl⟩ : syracuseStep 2954627 = 4431941) B4431941
theorem B8885645 : Blo 1036608 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B2954819 : Blo 1036608 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B1971793 : Blo 1036608 1971793 := bstep (se 2 (by rfl) ⟨739422, by rfl⟩ : syracuseStep 1971793 = 1478845) B1478845
theorem B3511889 : Blo 1036608 3511889 := bstep (se 2 (by rfl) ⟨1316958, by rfl⟩ : syracuseStep 3511889 = 2633917) B2633917
theorem B5904035 : Blo 1036608 5904035 := bstep (se 1 (by rfl) ⟨4428026, by rfl⟩ : syracuseStep 5904035 = 8856053) B8856053
theorem B3937997 : Blo 1036608 3937997 := bstep (se 3 (by rfl) ⟨738374, by rfl⟩ : syracuseStep 3937997 = 1476749) B1476749
theorem B1578707 : Blo 1036608 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B1316675 : Blo 1036608 1316675 := bstep (se 1 (by rfl) ⟨987506, by rfl⟩ : syracuseStep 1316675 = 1975013) B1975013
theorem B1480531 : Blo 1036608 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B4429667 : Blo 1036608 4429667 := bstep (se 1 (by rfl) ⟨3322250, by rfl⟩ : syracuseStep 4429667 = 6644501) B6644501
theorem B2332529 : Blo 1036608 2332529 := bstep (se 2 (by rfl) ⟨874698, by rfl⟩ : syracuseStep 2332529 = 1749397) B1749397
theorem B2332547 : Blo 1036608 2332547 := bstep (se 1 (by rfl) ⟨1749410, by rfl⟩ : syracuseStep 2332547 = 3498821) B3498821
theorem B5249123 : Blo 1036608 5249123 := bstep (se 1 (by rfl) ⟨3936842, by rfl⟩ : syracuseStep 5249123 = 7873685) B7873685
theorem B1284211 : Blo 1036608 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B2332817 : Blo 1036608 2332817 := bstep (se 2 (by rfl) ⟨874806, by rfl⟩ : syracuseStep 2332817 = 1749613) B1749613
theorem B2332835 : Blo 1036608 2332835 := bstep (se 1 (by rfl) ⟨1749626, by rfl⟩ : syracuseStep 2332835 = 3499253) B3499253
theorem B2627761 : Blo 1036608 2627761 := bstep (se 2 (by rfl) ⟨985410, by rfl⟩ : syracuseStep 2627761 = 1970821) B1970821
theorem B3742001 : Blo 1036608 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B1481009 : Blo 1036608 1481009 := bstep (se 2 (by rfl) ⟨555378, by rfl⟩ : syracuseStep 1481009 = 1110757) B1110757
theorem B2955629 : Blo 1036608 2955629 := bstep (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) B1108361
theorem B1481123 : Blo 1036608 1481123 := bstep (se 1 (by rfl) ⟨1110842, by rfl⟩ : syracuseStep 1481123 = 2221685) B2221685
theorem B2333105 : Blo 1036608 2333105 := bstep (se 2 (by rfl) ⟨874914, by rfl⟩ : syracuseStep 2333105 = 1749829) B1749829
theorem B2333123 : Blo 1036608 2333123 := bstep (se 1 (by rfl) ⟨1749842, by rfl⟩ : syracuseStep 2333123 = 3499685) B3499685
theorem B2628035 : Blo 1036608 2628035 := bstep (se 1 (by rfl) ⟨1971026, by rfl⟩ : syracuseStep 2628035 = 3942053) B3942053
theorem B1481203 : Blo 1036608 1481203 := bstep (se 1 (by rfl) ⟨1110902, by rfl⟩ : syracuseStep 1481203 = 2221805) B2221805
theorem B2955811 : Blo 1036608 2955811 := bstep (se 1 (by rfl) ⟨2216858, by rfl⟩ : syracuseStep 2955811 = 4433717) B4433717
theorem B6658595 : Blo 1036608 6658595 := bstep (se 1 (by rfl) ⟨4993946, by rfl⟩ : syracuseStep 6658595 = 9987893) B9987893
theorem B1972849 : Blo 1036608 1972849 := bstep (se 2 (by rfl) ⟨739818, by rfl⟩ : syracuseStep 1972849 = 1479637) B1479637
theorem B1776257 : Blo 1036608 1776257 := bstep (se 2 (by rfl) ⟨666096, by rfl⟩ : syracuseStep 1776257 = 1332193) B1332193
theorem B2628227 : Blo 1036608 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B2333393 : Blo 1036608 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B2333411 : Blo 1036608 2333411 := bstep (se 1 (by rfl) ⟨1750058, by rfl⟩ : syracuseStep 2333411 = 3500117) B3500117
theorem B1874801 : Blo 1036608 1874801 := bstep (se 2 (by rfl) ⟨703050, by rfl⟩ : syracuseStep 1874801 = 1406101) B1406101
theorem B5249933 : Blo 1036608 5249933 := bstep (se 3 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 5249933 = 1968725) B1968725
theorem B2333681 : Blo 1036608 2333681 := bstep (se 2 (by rfl) ⟨875130, by rfl⟩ : syracuseStep 2333681 = 1750261) B1750261
theorem B2333699 : Blo 1036608 2333699 := bstep (se 1 (by rfl) ⟨1750274, by rfl⟩ : syracuseStep 2333699 = 3500549) B3500549
theorem B1973251 : Blo 1036608 1973251 := bstep (se 1 (by rfl) ⟨1479938, by rfl⟩ : syracuseStep 1973251 = 2959877) B2959877
theorem B2956301 : Blo 1036608 2956301 := bstep (se 3 (by rfl) ⟨554306, by rfl⟩ : syracuseStep 2956301 = 1108613) B1108613
theorem B1973297 : Blo 1036608 1973297 := bstep (se 2 (by rfl) ⟨739986, by rfl⟩ : syracuseStep 1973297 = 1479973) B1479973
theorem B2366545 : Blo 1036608 2366545 := bstep (se 2 (by rfl) ⟨887454, by rfl⟩ : syracuseStep 2366545 = 1774909) B1774909
theorem B1875089 : Blo 1036608 1875089 := bstep (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) B1406317
theorem B2333969 : Blo 1036608 2333969 := bstep (se 2 (by rfl) ⟨875238, by rfl⟩ : syracuseStep 2333969 = 1750477) B1750477
theorem B2333987 : Blo 1036608 2333987 := bstep (se 1 (by rfl) ⟨1750490, by rfl⟩ : syracuseStep 2333987 = 3500981) B3500981
theorem B1973585 : Blo 1036608 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B3153421 : Blo 1036608 3153421 := bstep (se 3 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 3153421 = 1182533) B1182533
theorem B6659597 : Blo 1036608 6659597 := bstep (se 3 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 6659597 = 2497349) B2497349
theorem B2334257 : Blo 1036608 2334257 := bstep (se 2 (by rfl) ⟨875346, by rfl⟩ : syracuseStep 2334257 = 1750693) B1750693
theorem B2629169 : Blo 1036608 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B2334275 : Blo 1036608 2334275 := bstep (se 1 (by rfl) ⟨1750706, by rfl⟩ : syracuseStep 2334275 = 3501413) B3501413
theorem B2629219 : Blo 1036608 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B1777331 : Blo 1036608 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B3546833 : Blo 1036608 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B7872227 : Blo 1036608 7872227 := bstep (se 1 (by rfl) ⟨5904170, by rfl⟩ : syracuseStep 7872227 = 11808341) B11808341
theorem B2629361 : Blo 1036608 2629361 := bstep (se 2 (by rfl) ⟨986010, by rfl⟩ : syracuseStep 2629361 = 1972021) B1972021
theorem B3940109 : Blo 1036608 3940109 := bstep (se 3 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 3940109 = 1477541) B1477541
theorem B2334545 : Blo 1036608 2334545 := bstep (se 2 (by rfl) ⟨875454, by rfl⟩ : syracuseStep 2334545 = 1750909) B1750909
theorem B2334563 : Blo 1036608 2334563 := bstep (se 1 (by rfl) ⟨1750922, by rfl⟩ : syracuseStep 2334563 = 3501845) B3501845
theorem B2498435 : Blo 1036608 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B2105347 : Blo 1036608 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B1581089 : Blo 1036608 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B1974307 : Blo 1036608 1974307 := bstep (se 1 (by rfl) ⟨1480730, by rfl⟩ : syracuseStep 1974307 = 2961461) B2961461
theorem B2498627 : Blo 1036608 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B2334833 : Blo 1036608 2334833 := bstep (se 2 (by rfl) ⟨875562, by rfl⟩ : syracuseStep 2334833 = 1751125) B1751125
theorem B2334851 : Blo 1036608 2334851 := bstep (se 1 (by rfl) ⟨1751138, by rfl⟩ : syracuseStep 2334851 = 3502277) B3502277
theorem B2957485 : Blo 1036608 2957485 := bstep (se 3 (by rfl) ⟨554528, by rfl⟩ : syracuseStep 2957485 = 1109057) B1109057
theorem B7119173 : Blo 1036608 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B2335121 : Blo 1036608 2335121 := bstep (se 2 (by rfl) ⟨875670, by rfl⟩ : syracuseStep 2335121 = 1751341) B1751341
theorem B2335139 : Blo 1036608 2335139 := bstep (se 1 (by rfl) ⟨1751354, by rfl⟩ : syracuseStep 2335139 = 3502709) B3502709
theorem B1974755 : Blo 1036608 1974755 := bstep (se 1 (by rfl) ⟨1481066, by rfl⟩ : syracuseStep 1974755 = 2962133) B2962133
theorem B1352227 : Blo 1036608 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B3154481 : Blo 1036608 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B3940913 : Blo 1036608 3940913 := bstep (se 2 (by rfl) ⟨1477842, by rfl⟩ : syracuseStep 3940913 = 2955685) B2955685
theorem B2335409 : Blo 1036608 2335409 := bstep (se 2 (by rfl) ⟨875778, by rfl⟩ : syracuseStep 2335409 = 1751557) B1751557
theorem B2335427 : Blo 1036608 2335427 := bstep (se 1 (by rfl) ⟨1751570, by rfl⟩ : syracuseStep 2335427 = 3503141) B3503141
theorem B7119557 : Blo 1036608 7119557 := bstep (se 4 (by rfl) ⟨667458, by rfl⟩ : syracuseStep 7119557 = 1334917) B1334917
theorem B2630353 : Blo 1036608 2630353 := bstep (se 2 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 2630353 = 1972765) B1972765
theorem B2499281 : Blo 1036608 2499281 := bstep (se 2 (by rfl) ⟨937230, by rfl⟩ : syracuseStep 2499281 = 1874461) B1874461
theorem B1975043 : Blo 1036608 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B5907269 : Blo 1036608 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B307635029 : Blo 1036608 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B2368369 : Blo 1036608 2368369 := bstep (se 2 (by rfl) ⟨888138, by rfl⟩ : syracuseStep 2368369 = 1776277) B1776277
theorem B2335697 : Blo 1036608 2335697 := bstep (se 2 (by rfl) ⟨875886, by rfl⟩ : syracuseStep 2335697 = 1751773) B1751773
theorem B2335715 : Blo 1036608 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B2630627 : Blo 1036608 2630627 := bstep (se 1 (by rfl) ⟨1972970, by rfl⟩ : syracuseStep 2630627 = 3945941) B3945941
theorem B2630819 : Blo 1036608 2630819 := bstep (se 1 (by rfl) ⟨1973114, by rfl⟩ : syracuseStep 2630819 = 3946229) B3946229
theorem B13477061 : Blo 1036608 13477061 := bstep (se 4 (by rfl) ⟨1263474, by rfl⟩ : syracuseStep 13477061 = 2526949) B2526949
theorem B3941581 : Blo 1036608 3941581 := bstep (se 3 (by rfl) ⟨739046, by rfl⟩ : syracuseStep 3941581 = 1478093) B1478093
theorem B2958545 : Blo 1036608 2958545 := bstep (se 2 (by rfl) ⟨1109454, by rfl⟩ : syracuseStep 2958545 = 2218909) B2218909
theorem B2565329 : Blo 1036608 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B8856803 : Blo 1036608 8856803 := bstep (se 1 (by rfl) ⟨6642602, by rfl⟩ : syracuseStep 8856803 = 13285205) B13285205
theorem B2335985 : Blo 1036608 2335985 := bstep (se 2 (by rfl) ⟨875994, by rfl⟩ : syracuseStep 2335985 = 1751989) B1751989
theorem B2336003 : Blo 1036608 2336003 := bstep (se 1 (by rfl) ⟨1752002, by rfl⟩ : syracuseStep 2336003 = 3504005) B3504005
theorem B5907725 : Blo 1036608 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B3122513 : Blo 1036608 3122513 := bstep (se 2 (by rfl) ⟨1170942, by rfl⟩ : syracuseStep 3122513 = 2341885) B2341885
theorem B2500049 : Blo 1036608 2500049 := bstep (se 2 (by rfl) ⟨937518, by rfl⟩ : syracuseStep 2500049 = 1875037) B1875037
theorem B2336273 : Blo 1036608 2336273 := bstep (se 2 (by rfl) ⟨876102, by rfl⟩ : syracuseStep 2336273 = 1752205) B1752205
theorem B2336291 : Blo 1036608 2336291 := bstep (se 1 (by rfl) ⟨1752218, by rfl⟩ : syracuseStep 2336291 = 3504437) B3504437
theorem B5252849 : Blo 1036608 5252849 := bstep (se 2 (by rfl) ⟨1969818, by rfl⟩ : syracuseStep 5252849 = 3939637) B3939637
theorem B2336561 : Blo 1036608 2336561 := bstep (se 2 (by rfl) ⟨876210, by rfl⟩ : syracuseStep 2336561 = 1752421) B1752421
theorem B2336579 : Blo 1036608 2336579 := bstep (se 1 (by rfl) ⟨1752434, by rfl⟩ : syracuseStep 2336579 = 3504869) B3504869
theorem B2959217 : Blo 1036608 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B4433869 : Blo 1036608 4433869 := bstep (se 3 (by rfl) ⟨831350, by rfl⟩ : syracuseStep 4433869 = 1662701) B1662701
theorem B3942371 : Blo 1036608 3942371 := bstep (se 1 (by rfl) ⟨2956778, by rfl⟩ : syracuseStep 3942371 = 5913557) B5913557
theorem B2336849 : Blo 1036608 2336849 := bstep (se 2 (by rfl) ⟨876318, by rfl⟩ : syracuseStep 2336849 = 1752637) B1752637
theorem B2631761 : Blo 1036608 2631761 := bstep (se 2 (by rfl) ⟨986910, by rfl⟩ : syracuseStep 2631761 = 1973821) B1973821
theorem B2336867 : Blo 1036608 2336867 := bstep (se 1 (by rfl) ⟨1752650, by rfl⟩ : syracuseStep 2336867 = 3505301) B3505301
theorem B2631811 : Blo 1036608 2631811 := bstep (se 1 (by rfl) ⟨1973858, by rfl⟩ : syracuseStep 2631811 = 3947717) B3947717
theorem B18229475 : Blo 1036608 18229475 := bstep (se 1 (by rfl) ⟨13672106, by rfl⟩ : syracuseStep 18229475 = 27344213) B27344213
theorem B2631953 : Blo 1036608 2631953 := bstep (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) B1973965
theorem B2337137 : Blo 1036608 2337137 := bstep (se 2 (by rfl) ⟨876426, by rfl⟩ : syracuseStep 2337137 = 1752853) B1752853
theorem B2337155 : Blo 1036608 2337155 := bstep (se 1 (by rfl) ⟨1752866, by rfl⟩ : syracuseStep 2337155 = 3505733) B3505733
theorem B3943025 : Blo 1036608 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B2960003 : Blo 1036608 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B2337425 : Blo 1036608 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B2337443 : Blo 1036608 2337443 := bstep (se 1 (by rfl) ⟨1753082, by rfl⟩ : syracuseStep 2337443 = 3506165) B3506165
theorem B2337713 : Blo 1036608 2337713 := bstep (se 2 (by rfl) ⟨876642, by rfl⟩ : syracuseStep 2337713 = 1753285) B1753285
theorem B2337731 : Blo 1036608 2337731 := bstep (se 1 (by rfl) ⟨1753298, by rfl⟩ : syracuseStep 2337731 = 3506597) B3506597
theorem B2960333 : Blo 1036608 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B2960401 : Blo 1036608 2960401 := bstep (se 2 (by rfl) ⟨1110150, by rfl⟩ : syracuseStep 2960401 = 2220301) B2220301
theorem B5254307 : Blo 1036608 5254307 := bstep (se 1 (by rfl) ⟨3940730, by rfl⟩ : syracuseStep 5254307 = 7881461) B7881461
theorem B2338001 : Blo 1036608 2338001 := bstep (se 2 (by rfl) ⟨876750, by rfl⟩ : syracuseStep 2338001 = 1753501) B1753501
theorem B2338019 : Blo 1036608 2338019 := bstep (se 1 (by rfl) ⟨1753514, by rfl⟩ : syracuseStep 2338019 = 3507029) B3507029
theorem B2632945 : Blo 1036608 2632945 := bstep (se 2 (by rfl) ⟨987354, by rfl⟩ : syracuseStep 2632945 = 1974709) B1974709
theorem B2993425 : Blo 1036608 2993425 := bstep (se 2 (by rfl) ⟨1122534, by rfl⟩ : syracuseStep 2993425 = 2245069) B2245069
theorem B2370833 : Blo 1036608 2370833 := bstep (se 2 (by rfl) ⟨889062, by rfl⟩ : syracuseStep 2370833 = 1778125) B1778125
theorem B2370851 : Blo 1036608 2370851 := bstep (se 1 (by rfl) ⟨1778138, by rfl⟩ : syracuseStep 2370851 = 3556277) B3556277
theorem B2960675 : Blo 1036608 2960675 := bstep (se 1 (by rfl) ⟨2220506, by rfl⟩ : syracuseStep 2960675 = 4441013) B4441013
theorem B2108849 : Blo 1036608 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B2338289 : Blo 1036608 2338289 := bstep (se 2 (by rfl) ⟨876858, by rfl⟩ : syracuseStep 2338289 = 1753717) B1753717
theorem B3157507 : Blo 1036608 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B2338307 : Blo 1036608 2338307 := bstep (se 1 (by rfl) ⟨1753730, by rfl⟩ : syracuseStep 2338307 = 3507461) B3507461
theorem B2633219 : Blo 1036608 2633219 := bstep (se 1 (by rfl) ⟨1974914, by rfl⟩ : syracuseStep 2633219 = 3949829) B3949829
theorem B2108963 : Blo 1036608 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B2993773 : Blo 1036608 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B2633411 : Blo 1036608 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B9875141 : Blo 1036608 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B2338577 : Blo 1036608 2338577 := bstep (se 2 (by rfl) ⟨876966, by rfl⟩ : syracuseStep 2338577 = 1753933) B1753933
theorem B2338595 : Blo 1036608 2338595 := bstep (se 1 (by rfl) ⟨1753946, by rfl⟩ : syracuseStep 2338595 = 3507893) B3507893
theorem B5320561 : Blo 1036608 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B5255117 : Blo 1036608 5255117 := bstep (se 3 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 5255117 = 1970669) B1970669
theorem B22491107 : Blo 1036608 22491107 := bstep (se 1 (by rfl) ⟨16868330, by rfl⟩ : syracuseStep 22491107 = 33736661) B33736661
theorem B3944483 : Blo 1036608 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B3944497 : Blo 1036608 3944497 := bstep (se 2 (by rfl) ⟨1479186, by rfl⟩ : syracuseStep 3944497 = 2958373) B2958373
theorem B2338865 : Blo 1036608 2338865 := bstep (se 2 (by rfl) ⟨877074, by rfl⟩ : syracuseStep 2338865 = 1754149) B1754149
theorem B2338883 : Blo 1036608 2338883 := bstep (se 1 (by rfl) ⟨1754162, by rfl⟩ : syracuseStep 2338883 = 3508325) B3508325
theorem B2961517 : Blo 1036608 2961517 := bstep (se 3 (by rfl) ⟨555284, by rfl⟩ : syracuseStep 2961517 = 1110569) B1110569
theorem B5910641 : Blo 1036608 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B3322019 : Blo 1036608 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B2961677 : Blo 1036608 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B2339153 : Blo 1036608 2339153 := bstep (se 2 (by rfl) ⟨877182, by rfl⟩ : syracuseStep 2339153 = 1754365) B1754365
theorem B1421651 : Blo 1036608 1421651 := bstep (se 1 (by rfl) ⟨1066238, by rfl⟩ : syracuseStep 1421651 = 2132477) B2132477
theorem B2339171 : Blo 1036608 2339171 := bstep (se 1 (by rfl) ⟨1754378, by rfl⟩ : syracuseStep 2339171 = 3508757) B3508757
theorem B1749377 : Blo 1036608 1749377 := bstep (se 2 (by rfl) ⟨656016, by rfl⟩ : syracuseStep 1749377 = 1312033) B1312033
theorem B4731299 : Blo 1036608 4731299 := bstep (se 1 (by rfl) ⟨3548474, by rfl⟩ : syracuseStep 4731299 = 7096949) B7096949
theorem B2961859 : Blo 1036608 2961859 := bstep (se 1 (by rfl) ⟨2221394, by rfl⟩ : syracuseStep 2961859 = 4442789) B4442789
theorem B1749505 : Blo 1036608 1749505 := bstep (se 2 (by rfl) ⟨656064, by rfl⟩ : syracuseStep 1749505 = 1312129) B1312129
theorem B1749539 : Blo 1036608 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B2667043 : Blo 1036608 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B2339441 : Blo 1036608 2339441 := bstep (se 2 (by rfl) ⟨877290, by rfl⟩ : syracuseStep 2339441 = 1754581) B1754581
theorem B2339459 : Blo 1036608 2339459 := bstep (se 1 (by rfl) ⟨1754594, by rfl⟩ : syracuseStep 2339459 = 3509189) B3509189
theorem B1749667 : Blo 1036608 1749667 := bstep (se 1 (by rfl) ⟨1312250, by rfl⟩ : syracuseStep 1749667 = 2624501) B2624501
theorem B1684243 : Blo 1036608 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B1749809 : Blo 1036608 1749809 := bstep (se 2 (by rfl) ⟨656178, by rfl⟩ : syracuseStep 1749809 = 1312357) B1312357
theorem B2339729 : Blo 1036608 2339729 := bstep (se 2 (by rfl) ⟨877398, by rfl⟩ : syracuseStep 2339729 = 1754797) B1754797
theorem B2339747 : Blo 1036608 2339747 := bstep (se 1 (by rfl) ⟨1754810, by rfl⟩ : syracuseStep 2339747 = 3509621) B3509621
theorem B1749937 : Blo 1036608 1749937 := bstep (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) B1312453
theorem B7877573 : Blo 1036608 7877573 := bstep (se 4 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 7877573 = 1477045) B1477045
theorem B1749971 : Blo 1036608 1749971 := bstep (se 1 (by rfl) ⟨1312478, by rfl⟩ : syracuseStep 1749971 = 2624957) B2624957
theorem B1750099 : Blo 1036608 1750099 := bstep (se 1 (by rfl) ⟨1312574, by rfl⟩ : syracuseStep 1750099 = 2625149) B2625149
theorem B2340017 : Blo 1036608 2340017 := bstep (se 2 (by rfl) ⟨877506, by rfl⟩ : syracuseStep 2340017 = 1755013) B1755013
theorem B2340035 : Blo 1036608 2340035 := bstep (se 1 (by rfl) ⟨1755026, by rfl⟩ : syracuseStep 2340035 = 3510053) B3510053
theorem B1750241 : Blo 1036608 1750241 := bstep (se 2 (by rfl) ⟨656340, by rfl⟩ : syracuseStep 1750241 = 1312681) B1312681
theorem B1750369 : Blo 1036608 1750369 := bstep (se 2 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 1750369 = 1312777) B1312777
theorem B1750403 : Blo 1036608 1750403 := bstep (se 1 (by rfl) ⟨1312802, by rfl⟩ : syracuseStep 1750403 = 2625605) B2625605
theorem B2340305 : Blo 1036608 2340305 := bstep (se 2 (by rfl) ⟨877614, by rfl⟩ : syracuseStep 2340305 = 1755229) B1755229
theorem B5682659 : Blo 1036608 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B3945955 : Blo 1036608 3945955 := bstep (se 1 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 3945955 = 5918933) B5918933
theorem B2340323 : Blo 1036608 2340323 := bstep (se 1 (by rfl) ⟨1755242, by rfl⟩ : syracuseStep 2340323 = 3510485) B3510485
theorem B1750531 : Blo 1036608 1750531 := bstep (se 1 (by rfl) ⟨1312898, by rfl⟩ : syracuseStep 1750531 = 2625797) B2625797
theorem B5912099 : Blo 1036608 5912099 := bstep (se 1 (by rfl) ⟨4434074, by rfl⟩ : syracuseStep 5912099 = 8868149) B8868149
theorem B1750673 : Blo 1036608 1750673 := bstep (se 2 (by rfl) ⟨656502, by rfl⟩ : syracuseStep 1750673 = 1313005) B1313005
theorem B2340593 : Blo 1036608 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B2340611 : Blo 1036608 2340611 := bstep (se 1 (by rfl) ⟨1755458, by rfl⟩ : syracuseStep 2340611 = 3510917) B3510917
theorem B1750801 : Blo 1036608 1750801 := bstep (se 2 (by rfl) ⟨656550, by rfl⟩ : syracuseStep 1750801 = 1313101) B1313101
theorem B2963249 : Blo 1036608 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B1750835 : Blo 1036608 1750835 := bstep (se 1 (by rfl) ⟨1313126, by rfl⟩ : syracuseStep 1750835 = 2626253) B2626253
theorem B1750963 : Blo 1036608 1750963 := bstep (se 1 (by rfl) ⟨1313222, by rfl⟩ : syracuseStep 1750963 = 2626445) B2626445
theorem B3651533 : Blo 1036608 3651533 := bstep (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) B1369325
theorem B2340881 : Blo 1036608 2340881 := bstep (se 2 (by rfl) ⟨877830, by rfl⟩ : syracuseStep 2340881 = 1755661) B1755661
theorem B1685537 : Blo 1036608 1685537 := bstep (se 2 (by rfl) ⟨632076, by rfl⟩ : syracuseStep 1685537 = 1264153) B1264153
theorem B2340899 : Blo 1036608 2340899 := bstep (se 1 (by rfl) ⟨1755674, by rfl⟩ : syracuseStep 2340899 = 3511349) B3511349
theorem B1751105 : Blo 1036608 1751105 := bstep (se 2 (by rfl) ⟨656664, by rfl⟩ : syracuseStep 1751105 = 1313329) B1313329
theorem B1751233 : Blo 1036608 1751233 := bstep (se 2 (by rfl) ⟨656712, by rfl⟩ : syracuseStep 1751233 = 1313425) B1313425
theorem B1751267 : Blo 1036608 1751267 := bstep (se 1 (by rfl) ⟨1313450, by rfl⟩ : syracuseStep 1751267 = 2626901) B2626901
theorem B4438243 : Blo 1036608 4438243 := bstep (se 1 (by rfl) ⟨3328682, by rfl⟩ : syracuseStep 4438243 = 6657365) B6657365
theorem B2341169 : Blo 1036608 2341169 := bstep (se 2 (by rfl) ⟨877938, by rfl⟩ : syracuseStep 2341169 = 1755877) B1755877
theorem B2341187 : Blo 1036608 2341187 := bstep (se 1 (by rfl) ⟨1755890, by rfl⟩ : syracuseStep 2341187 = 3511781) B3511781
theorem B1751395 : Blo 1036608 1751395 := bstep (se 1 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 1751395 = 2627093) B2627093
theorem B8436109 : Blo 1036608 8436109 := bstep (se 3 (by rfl) ⟨1581770, by rfl⟩ : syracuseStep 8436109 = 3163541) B3163541
theorem B1685953 : Blo 1036608 1685953 := bstep (se 2 (by rfl) ⟨632232, by rfl⟩ : syracuseStep 1685953 = 1264465) B1264465
theorem B1554929 : Blo 1036608 1554929 := bstep (se 2 (by rfl) ⟨583098, by rfl⟩ : syracuseStep 1554929 = 1166197) B1166197
theorem B1751537 : Blo 1036608 1751537 := bstep (se 2 (by rfl) ⟨656826, by rfl⟩ : syracuseStep 1751537 = 1313653) B1313653
theorem B1554947 : Blo 1036608 1554947 := bstep (se 1 (by rfl) ⟨1166210, by rfl⟩ : syracuseStep 1554947 = 2332421) B2332421
theorem B5913101 : Blo 1036608 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B7485965 : Blo 1036608 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B1554977 : Blo 1036608 1554977 := bstep (se 2 (by rfl) ⟨583116, by rfl⟩ : syracuseStep 1554977 = 1166233) B1166233
theorem B1554995 : Blo 1036608 1554995 := bstep (se 1 (by rfl) ⟨1166246, by rfl⟩ : syracuseStep 1554995 = 2332493) B2332493
theorem B1555025 : Blo 1036608 1555025 := bstep (se 2 (by rfl) ⟨583134, by rfl⟩ : syracuseStep 1555025 = 1166269) B1166269
theorem B1555043 : Blo 1036608 1555043 := bstep (se 1 (by rfl) ⟨1166282, by rfl⟩ : syracuseStep 1555043 = 2332565) B2332565
theorem B1751665 : Blo 1036608 1751665 := bstep (se 2 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 1751665 = 1313749) B1313749
theorem B1555073 : Blo 1036608 1555073 := bstep (se 2 (by rfl) ⟨583152, by rfl⟩ : syracuseStep 1555073 = 1166305) B1166305
theorem B3160721 : Blo 1036608 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B1555091 : Blo 1036608 1555091 := bstep (se 1 (by rfl) ⟨1166318, by rfl⟩ : syracuseStep 1555091 = 2332637) B2332637
theorem B1751699 : Blo 1036608 1751699 := bstep (se 1 (by rfl) ⟨1313774, by rfl⟩ : syracuseStep 1751699 = 2627549) B2627549
theorem B1555121 : Blo 1036608 1555121 := bstep (se 2 (by rfl) ⟨583170, by rfl⟩ : syracuseStep 1555121 = 1166341) B1166341
theorem B1555139 : Blo 1036608 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1555169 : Blo 1036608 1555169 := bstep (se 2 (by rfl) ⟨583188, by rfl⟩ : syracuseStep 1555169 = 1166377) B1166377
theorem B1555187 : Blo 1036608 1555187 := bstep (se 1 (by rfl) ⟨1166390, by rfl⟩ : syracuseStep 1555187 = 2332781) B2332781
theorem B3324685 : Blo 1036608 3324685 := bstep (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) B1246757
theorem B1555217 : Blo 1036608 1555217 := bstep (se 2 (by rfl) ⟨583206, by rfl⟩ : syracuseStep 1555217 = 1166413) B1166413
theorem B1751827 : Blo 1036608 1751827 := bstep (se 1 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 1751827 = 2627741) B2627741
theorem B1555235 : Blo 1036608 1555235 := bstep (se 1 (by rfl) ⟨1166426, by rfl⟩ : syracuseStep 1555235 = 2332853) B2332853
theorem B5258033 : Blo 1036608 5258033 := bstep (se 2 (by rfl) ⟨1971762, by rfl⟩ : syracuseStep 5258033 = 3943525) B3943525
theorem B12008245 : Blo 1036608 12008245 := bstep (se 5 (by rfl) ⟨562886, by rfl⟩ : syracuseStep 12008245 = 1125773) B1125773
theorem B1555265 : Blo 1036608 1555265 := bstep (se 2 (by rfl) ⟨583224, by rfl⟩ : syracuseStep 1555265 = 1166449) B1166449
theorem B1555283 : Blo 1036608 1555283 := bstep (se 1 (by rfl) ⟨1166462, by rfl⟩ : syracuseStep 1555283 = 2332925) B2332925
theorem B7486307 : Blo 1036608 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B1555313 : Blo 1036608 1555313 := bstep (se 2 (by rfl) ⟨583242, by rfl⟩ : syracuseStep 1555313 = 1166485) B1166485
theorem B1555331 : Blo 1036608 1555331 := bstep (se 1 (by rfl) ⟨1166498, by rfl⟩ : syracuseStep 1555331 = 2332997) B2332997
theorem B1555361 : Blo 1036608 1555361 := bstep (se 2 (by rfl) ⟨583260, by rfl⟩ : syracuseStep 1555361 = 1166521) B1166521
theorem B1751969 : Blo 1036608 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1555379 : Blo 1036608 1555379 := bstep (se 1 (by rfl) ⟨1166534, by rfl⟩ : syracuseStep 1555379 = 2333069) B2333069
theorem B1555409 : Blo 1036608 1555409 := bstep (se 2 (by rfl) ⟨583278, by rfl⟩ : syracuseStep 1555409 = 1166557) B1166557
theorem B1555427 : Blo 1036608 1555427 := bstep (se 1 (by rfl) ⟨1166570, by rfl⟩ : syracuseStep 1555427 = 2333141) B2333141
theorem B1555457 : Blo 1036608 1555457 := bstep (se 2 (by rfl) ⟨583296, by rfl⟩ : syracuseStep 1555457 = 1166593) B1166593
theorem B1555475 : Blo 1036608 1555475 := bstep (se 1 (by rfl) ⟨1166606, by rfl⟩ : syracuseStep 1555475 = 2333213) B2333213
theorem B1752097 : Blo 1036608 1752097 := bstep (se 2 (by rfl) ⟨657036, by rfl⟩ : syracuseStep 1752097 = 1314073) B1314073
theorem B1555505 : Blo 1036608 1555505 := bstep (se 2 (by rfl) ⟨583314, by rfl⟩ : syracuseStep 1555505 = 1166629) B1166629
theorem B1555523 : Blo 1036608 1555523 := bstep (se 1 (by rfl) ⟨1166642, by rfl⟩ : syracuseStep 1555523 = 2333285) B2333285
theorem B1752131 : Blo 1036608 1752131 := bstep (se 1 (by rfl) ⟨1314098, by rfl⟩ : syracuseStep 1752131 = 2628197) B2628197
theorem B1555553 : Blo 1036608 1555553 := bstep (se 2 (by rfl) ⟨583332, by rfl⟩ : syracuseStep 1555553 = 1166665) B1166665
theorem B1555571 : Blo 1036608 1555571 := bstep (se 1 (by rfl) ⟨1166678, by rfl⟩ : syracuseStep 1555571 = 2333357) B2333357
theorem B1555601 : Blo 1036608 1555601 := bstep (se 2 (by rfl) ⟨583350, by rfl⟩ : syracuseStep 1555601 = 1166701) B1166701
theorem B1555619 : Blo 1036608 1555619 := bstep (se 1 (by rfl) ⟨1166714, by rfl⟩ : syracuseStep 1555619 = 2333429) B2333429
theorem B1555649 : Blo 1036608 1555649 := bstep (se 2 (by rfl) ⟨583368, by rfl⟩ : syracuseStep 1555649 = 1166737) B1166737
theorem B1752259 : Blo 1036608 1752259 := bstep (se 1 (by rfl) ⟨1314194, by rfl⟩ : syracuseStep 1752259 = 2628389) B2628389
theorem B1555667 : Blo 1036608 1555667 := bstep (se 1 (by rfl) ⟨1166750, by rfl⟩ : syracuseStep 1555667 = 2333501) B2333501
theorem B1555697 : Blo 1036608 1555697 := bstep (se 2 (by rfl) ⟨583386, by rfl⟩ : syracuseStep 1555697 = 1166773) B1166773
theorem B1555715 : Blo 1036608 1555715 := bstep (se 1 (by rfl) ⟨1166786, by rfl⟩ : syracuseStep 1555715 = 2333573) B2333573
theorem B1555745 : Blo 1036608 1555745 := bstep (se 2 (by rfl) ⟨583404, by rfl⟩ : syracuseStep 1555745 = 1166809) B1166809
theorem B1555763 : Blo 1036608 1555763 := bstep (se 1 (by rfl) ⟨1166822, by rfl⟩ : syracuseStep 1555763 = 2333645) B2333645
theorem B1555793 : Blo 1036608 1555793 := bstep (se 2 (by rfl) ⟨583422, by rfl⟩ : syracuseStep 1555793 = 1166845) B1166845
theorem B1752401 : Blo 1036608 1752401 := bstep (se 2 (by rfl) ⟨657150, by rfl⟩ : syracuseStep 1752401 = 1314301) B1314301
theorem B1555811 : Blo 1036608 1555811 := bstep (se 1 (by rfl) ⟨1166858, by rfl⟩ : syracuseStep 1555811 = 2333717) B2333717
theorem B1555841 : Blo 1036608 1555841 := bstep (se 2 (by rfl) ⟨583440, by rfl⟩ : syracuseStep 1555841 = 1166881) B1166881
theorem B1555859 : Blo 1036608 1555859 := bstep (se 1 (by rfl) ⟨1166894, by rfl⟩ : syracuseStep 1555859 = 2333789) B2333789
theorem B1424803 : Blo 1036608 1424803 := bstep (se 1 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 1424803 = 2137205) B2137205
theorem B1555889 : Blo 1036608 1555889 := bstep (se 2 (by rfl) ⟨583458, by rfl⟩ : syracuseStep 1555889 = 1166917) B1166917
theorem B1555907 : Blo 1036608 1555907 := bstep (se 1 (by rfl) ⟨1166930, by rfl⟩ : syracuseStep 1555907 = 2333861) B2333861
theorem B5324237 : Blo 1036608 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B1752529 : Blo 1036608 1752529 := bstep (se 2 (by rfl) ⟨657198, by rfl⟩ : syracuseStep 1752529 = 1314397) B1314397
theorem B1555937 : Blo 1036608 1555937 := bstep (se 2 (by rfl) ⟨583476, by rfl⟩ : syracuseStep 1555937 = 1166953) B1166953
theorem B1555955 : Blo 1036608 1555955 := bstep (se 1 (by rfl) ⟨1166966, by rfl⟩ : syracuseStep 1555955 = 2333933) B2333933
theorem B1752563 : Blo 1036608 1752563 := bstep (se 1 (by rfl) ⟨1314422, by rfl⟩ : syracuseStep 1752563 = 2628845) B2628845
theorem B1555985 : Blo 1036608 1555985 := bstep (se 2 (by rfl) ⟨583494, by rfl⟩ : syracuseStep 1555985 = 1166989) B1166989
theorem B1556003 : Blo 1036608 1556003 := bstep (se 1 (by rfl) ⟨1167002, by rfl⟩ : syracuseStep 1556003 = 2334005) B2334005
theorem B1556033 : Blo 1036608 1556033 := bstep (se 2 (by rfl) ⟨583512, by rfl⟩ : syracuseStep 1556033 = 1167025) B1167025
theorem B1556051 : Blo 1036608 1556051 := bstep (se 1 (by rfl) ⟨1167038, by rfl⟩ : syracuseStep 1556051 = 2334077) B2334077
theorem B1556081 : Blo 1036608 1556081 := bstep (se 2 (by rfl) ⟨583530, by rfl⟩ : syracuseStep 1556081 = 1167061) B1167061
theorem B1752691 : Blo 1036608 1752691 := bstep (se 1 (by rfl) ⟨1314518, by rfl⟩ : syracuseStep 1752691 = 2629037) B2629037
theorem B1556099 : Blo 1036608 1556099 := bstep (se 1 (by rfl) ⟨1167074, by rfl⟩ : syracuseStep 1556099 = 2334149) B2334149
theorem B3948173 : Blo 1036608 3948173 := bstep (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) B1480565
theorem B1556129 : Blo 1036608 1556129 := bstep (se 2 (by rfl) ⟨583548, by rfl⟩ : syracuseStep 1556129 = 1167097) B1167097
theorem B1556147 : Blo 1036608 1556147 := bstep (se 1 (by rfl) ⟨1167110, by rfl⟩ : syracuseStep 1556147 = 2334221) B2334221
theorem B1556177 : Blo 1036608 1556177 := bstep (se 2 (by rfl) ⟨583566, by rfl⟩ : syracuseStep 1556177 = 1167133) B1167133
theorem B1556195 : Blo 1036608 1556195 := bstep (se 1 (by rfl) ⟨1167146, by rfl⟩ : syracuseStep 1556195 = 2334293) B2334293
theorem B1556225 : Blo 1036608 1556225 := bstep (se 2 (by rfl) ⟨583584, by rfl⟩ : syracuseStep 1556225 = 1167169) B1167169
theorem B1752833 : Blo 1036608 1752833 := bstep (se 2 (by rfl) ⟨657312, by rfl⟩ : syracuseStep 1752833 = 1314625) B1314625
theorem B1556243 : Blo 1036608 1556243 := bstep (se 1 (by rfl) ⟨1167182, by rfl⟩ : syracuseStep 1556243 = 2334365) B2334365
theorem B1556273 : Blo 1036608 1556273 := bstep (se 2 (by rfl) ⟨583602, by rfl⟩ : syracuseStep 1556273 = 1167205) B1167205
theorem B1556291 : Blo 1036608 1556291 := bstep (se 1 (by rfl) ⟨1167218, by rfl⟩ : syracuseStep 1556291 = 2334437) B2334437
theorem B2998093 : Blo 1036608 2998093 := bstep (se 3 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 2998093 = 1124285) B1124285
theorem B1556321 : Blo 1036608 1556321 := bstep (se 2 (by rfl) ⟨583620, by rfl⟩ : syracuseStep 1556321 = 1167241) B1167241
theorem B1556339 : Blo 1036608 1556339 := bstep (se 1 (by rfl) ⟨1167254, by rfl⟩ : syracuseStep 1556339 = 2334509) B2334509
theorem B1752961 : Blo 1036608 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B1556369 : Blo 1036608 1556369 := bstep (se 2 (by rfl) ⟨583638, by rfl⟩ : syracuseStep 1556369 = 1167277) B1167277
theorem B2244515 : Blo 1036608 2244515 := bstep (se 1 (by rfl) ⟨1683386, by rfl⟩ : syracuseStep 2244515 = 3366773) B3366773
theorem B1556387 : Blo 1036608 1556387 := bstep (se 1 (by rfl) ⟨1167290, by rfl⟩ : syracuseStep 1556387 = 2334581) B2334581
theorem B1752995 : Blo 1036608 1752995 := bstep (se 1 (by rfl) ⟨1314746, by rfl⟩ : syracuseStep 1752995 = 2629493) B2629493
theorem B1556417 : Blo 1036608 1556417 := bstep (se 2 (by rfl) ⟨583656, by rfl⟩ : syracuseStep 1556417 = 1167313) B1167313
theorem B1556435 : Blo 1036608 1556435 := bstep (se 1 (by rfl) ⟨1167326, by rfl⟩ : syracuseStep 1556435 = 2334653) B2334653
theorem B1556465 : Blo 1036608 1556465 := bstep (se 2 (by rfl) ⟨583674, by rfl⟩ : syracuseStep 1556465 = 1167349) B1167349
theorem B1556483 : Blo 1036608 1556483 := bstep (se 1 (by rfl) ⟨1167362, by rfl⟩ : syracuseStep 1556483 = 2334725) B2334725
theorem B1556513 : Blo 1036608 1556513 := bstep (se 2 (by rfl) ⟨583692, by rfl⟩ : syracuseStep 1556513 = 1167385) B1167385
theorem B1753123 : Blo 1036608 1753123 := bstep (se 1 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 1753123 = 2629685) B2629685
theorem B1556531 : Blo 1036608 1556531 := bstep (se 1 (by rfl) ⟨1167398, by rfl⟩ : syracuseStep 1556531 = 2334797) B2334797
theorem B1556561 : Blo 1036608 1556561 := bstep (se 2 (by rfl) ⟨583710, by rfl⟩ : syracuseStep 1556561 = 1167421) B1167421
theorem B1556579 : Blo 1036608 1556579 := bstep (se 1 (by rfl) ⟨1167434, by rfl⟩ : syracuseStep 1556579 = 2334869) B2334869
theorem B1556609 : Blo 1036608 1556609 := bstep (se 2 (by rfl) ⟨583728, by rfl⟩ : syracuseStep 1556609 = 1167457) B1167457
theorem B1556627 : Blo 1036608 1556627 := bstep (se 1 (by rfl) ⟨1167470, by rfl⟩ : syracuseStep 1556627 = 2334941) B2334941
theorem B1556657 : Blo 1036608 1556657 := bstep (se 2 (by rfl) ⟨583746, by rfl⟩ : syracuseStep 1556657 = 1167493) B1167493
theorem B1753265 : Blo 1036608 1753265 := bstep (se 2 (by rfl) ⟨657474, by rfl⟩ : syracuseStep 1753265 = 1314949) B1314949
theorem B1556675 : Blo 1036608 1556675 := bstep (se 1 (by rfl) ⟨1167506, by rfl⟩ : syracuseStep 1556675 = 2335013) B2335013
theorem B3326147 : Blo 1036608 3326147 := bstep (se 1 (by rfl) ⟨2494610, by rfl⟩ : syracuseStep 3326147 = 4989221) B4989221
theorem B1556705 : Blo 1036608 1556705 := bstep (se 2 (by rfl) ⟨583764, by rfl⟩ : syracuseStep 1556705 = 1167529) B1167529
theorem B1065187 : Blo 1036608 1065187 := bstep (se 1 (by rfl) ⟨798890, by rfl⟩ : syracuseStep 1065187 = 1597781) B1597781
theorem B5259491 : Blo 1036608 5259491 := bstep (se 1 (by rfl) ⟨3944618, by rfl⟩ : syracuseStep 5259491 = 7889237) B7889237
theorem B13287665 : Blo 1036608 13287665 := bstep (se 2 (by rfl) ⟨4982874, by rfl⟩ : syracuseStep 13287665 = 9965749) B9965749
theorem B1556723 : Blo 1036608 1556723 := bstep (se 1 (by rfl) ⟨1167542, by rfl⟩ : syracuseStep 1556723 = 2335085) B2335085
theorem B1556753 : Blo 1036608 1556753 := bstep (se 2 (by rfl) ⟨583782, by rfl⟩ : syracuseStep 1556753 = 1167565) B1167565
theorem B1556771 : Blo 1036608 1556771 := bstep (se 1 (by rfl) ⟨1167578, by rfl⟩ : syracuseStep 1556771 = 2335157) B2335157
theorem B1753393 : Blo 1036608 1753393 := bstep (se 2 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 1753393 = 1315045) B1315045
theorem B1556801 : Blo 1036608 1556801 := bstep (se 2 (by rfl) ⟨583800, by rfl⟩ : syracuseStep 1556801 = 1167601) B1167601
theorem B1556819 : Blo 1036608 1556819 := bstep (se 1 (by rfl) ⟨1167614, by rfl⟩ : syracuseStep 1556819 = 2335229) B2335229
theorem B1753427 : Blo 1036608 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B1556849 : Blo 1036608 1556849 := bstep (se 2 (by rfl) ⟨583818, by rfl⟩ : syracuseStep 1556849 = 1167637) B1167637
theorem B1556867 : Blo 1036608 1556867 := bstep (se 1 (by rfl) ⟨1167650, by rfl⟩ : syracuseStep 1556867 = 2335301) B2335301
theorem B1556897 : Blo 1036608 1556897 := bstep (se 2 (by rfl) ⟨583836, by rfl⟩ : syracuseStep 1556897 = 1167673) B1167673
theorem B1556915 : Blo 1036608 1556915 := bstep (se 1 (by rfl) ⟨1167686, by rfl⟩ : syracuseStep 1556915 = 2335373) B2335373
theorem B1556945 : Blo 1036608 1556945 := bstep (se 2 (by rfl) ⟨583854, by rfl⟩ : syracuseStep 1556945 = 1167709) B1167709
theorem B3326417 : Blo 1036608 3326417 := bstep (se 2 (by rfl) ⟨1247406, by rfl⟩ : syracuseStep 3326417 = 2494813) B2494813
theorem B1753555 : Blo 1036608 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B1556963 : Blo 1036608 1556963 := bstep (se 1 (by rfl) ⟨1167722, by rfl⟩ : syracuseStep 1556963 = 2335445) B2335445
theorem B1556993 : Blo 1036608 1556993 := bstep (se 2 (by rfl) ⟨583872, by rfl⟩ : syracuseStep 1556993 = 1167745) B1167745
theorem B1557011 : Blo 1036608 1557011 := bstep (se 1 (by rfl) ⟨1167758, by rfl⟩ : syracuseStep 1557011 = 2335517) B2335517
theorem B1557041 : Blo 1036608 1557041 := bstep (se 2 (by rfl) ⟨583890, by rfl⟩ : syracuseStep 1557041 = 1167781) B1167781
theorem B1557059 : Blo 1036608 1557059 := bstep (se 1 (by rfl) ⟨1167794, by rfl⟩ : syracuseStep 1557059 = 2335589) B2335589
theorem B1557089 : Blo 1036608 1557089 := bstep (se 2 (by rfl) ⟨583908, by rfl⟩ : syracuseStep 1557089 = 1167817) B1167817
theorem B1753697 : Blo 1036608 1753697 := bstep (se 2 (by rfl) ⟨657636, by rfl⟩ : syracuseStep 1753697 = 1315273) B1315273
theorem B4440689 : Blo 1036608 4440689 := bstep (se 2 (by rfl) ⟨1665258, by rfl⟩ : syracuseStep 4440689 = 3330517) B3330517
theorem B1557107 : Blo 1036608 1557107 := bstep (se 1 (by rfl) ⟨1167830, by rfl⟩ : syracuseStep 1557107 = 2335661) B2335661
theorem B1557137 : Blo 1036608 1557137 := bstep (se 2 (by rfl) ⟨583926, by rfl⟩ : syracuseStep 1557137 = 1167853) B1167853
theorem B1557155 : Blo 1036608 1557155 := bstep (se 1 (by rfl) ⟨1167866, by rfl⟩ : syracuseStep 1557155 = 2335733) B2335733
theorem B1557185 : Blo 1036608 1557185 := bstep (se 2 (by rfl) ⟨583944, by rfl⟩ : syracuseStep 1557185 = 1167889) B1167889
theorem B1557203 : Blo 1036608 1557203 := bstep (se 1 (by rfl) ⟨1167902, by rfl⟩ : syracuseStep 1557203 = 2335805) B2335805
theorem B1753825 : Blo 1036608 1753825 := bstep (se 2 (by rfl) ⟨657684, by rfl⟩ : syracuseStep 1753825 = 1315369) B1315369
theorem B1557233 : Blo 1036608 1557233 := bstep (se 2 (by rfl) ⟨583962, by rfl⟩ : syracuseStep 1557233 = 1167925) B1167925
theorem B1557251 : Blo 1036608 1557251 := bstep (se 1 (by rfl) ⟨1167938, by rfl⟩ : syracuseStep 1557251 = 2335877) B2335877
theorem B1753859 : Blo 1036608 1753859 := bstep (se 1 (by rfl) ⟨1315394, by rfl⟩ : syracuseStep 1753859 = 2630789) B2630789
theorem B1557281 : Blo 1036608 1557281 := bstep (se 2 (by rfl) ⟨583980, by rfl⟩ : syracuseStep 1557281 = 1167961) B1167961
theorem B5620529 : Blo 1036608 5620529 := bstep (se 2 (by rfl) ⟨2107698, by rfl⟩ : syracuseStep 5620529 = 4215397) B4215397
theorem B1557299 : Blo 1036608 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B1557329 : Blo 1036608 1557329 := bstep (se 2 (by rfl) ⟨583998, by rfl⟩ : syracuseStep 1557329 = 1167997) B1167997
theorem B1557347 : Blo 1036608 1557347 := bstep (se 1 (by rfl) ⟨1168010, by rfl⟩ : syracuseStep 1557347 = 2336021) B2336021
theorem B1557377 : Blo 1036608 1557377 := bstep (se 2 (by rfl) ⟨584016, by rfl⟩ : syracuseStep 1557377 = 1168033) B1168033
theorem B1753987 : Blo 1036608 1753987 := bstep (se 1 (by rfl) ⟨1315490, by rfl⟩ : syracuseStep 1753987 = 2630981) B2630981
theorem B3556237 : Blo 1036608 3556237 := bstep (se 3 (by rfl) ⟨666794, by rfl⟩ : syracuseStep 3556237 = 1333589) B1333589
theorem B1557395 : Blo 1036608 1557395 := bstep (se 1 (by rfl) ⟨1168046, by rfl⟩ : syracuseStep 1557395 = 2336093) B2336093
theorem B3163043 : Blo 1036608 3163043 := bstep (se 1 (by rfl) ⟨2372282, by rfl⟩ : syracuseStep 3163043 = 4744565) B4744565
theorem B1557425 : Blo 1036608 1557425 := bstep (se 2 (by rfl) ⟨584034, by rfl⟩ : syracuseStep 1557425 = 1168069) B1168069
theorem B1557443 : Blo 1036608 1557443 := bstep (se 1 (by rfl) ⟨1168082, by rfl⟩ : syracuseStep 1557443 = 2336165) B2336165
theorem B1557473 : Blo 1036608 1557473 := bstep (se 2 (by rfl) ⟨584052, by rfl⟩ : syracuseStep 1557473 = 1168105) B1168105
theorem B1557491 : Blo 1036608 1557491 := bstep (se 1 (by rfl) ⟨1168118, by rfl⟩ : syracuseStep 1557491 = 2336237) B2336237
theorem B5260301 : Blo 1036608 5260301 := bstep (se 3 (by rfl) ⟨986306, by rfl⟩ : syracuseStep 5260301 = 1972613) B1972613
theorem B1557521 : Blo 1036608 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B1754129 : Blo 1036608 1754129 := bstep (se 2 (by rfl) ⟨657798, by rfl⟩ : syracuseStep 1754129 = 1315597) B1315597
theorem B1557539 : Blo 1036608 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1557569 : Blo 1036608 1557569 := bstep (se 2 (by rfl) ⟨584088, by rfl⟩ : syracuseStep 1557569 = 1168177) B1168177
theorem B1557587 : Blo 1036608 1557587 := bstep (se 1 (by rfl) ⟨1168190, by rfl⟩ : syracuseStep 1557587 = 2336381) B2336381
theorem B1557617 : Blo 1036608 1557617 := bstep (se 2 (by rfl) ⟨584106, by rfl⟩ : syracuseStep 1557617 = 1168213) B1168213
theorem B1557635 : Blo 1036608 1557635 := bstep (se 1 (by rfl) ⟨1168226, by rfl⟩ : syracuseStep 1557635 = 2336453) B2336453
theorem B1754257 : Blo 1036608 1754257 := bstep (se 2 (by rfl) ⟨657846, by rfl⟩ : syracuseStep 1754257 = 1315693) B1315693
theorem B1557665 : Blo 1036608 1557665 := bstep (se 2 (by rfl) ⟨584124, by rfl⟩ : syracuseStep 1557665 = 1168249) B1168249
theorem B1557683 : Blo 1036608 1557683 := bstep (se 1 (by rfl) ⟨1168262, by rfl⟩ : syracuseStep 1557683 = 2336525) B2336525
theorem B1754291 : Blo 1036608 1754291 := bstep (se 1 (by rfl) ⟨1315718, by rfl⟩ : syracuseStep 1754291 = 2631437) B2631437
theorem B1557713 : Blo 1036608 1557713 := bstep (se 2 (by rfl) ⟨584142, by rfl⟩ : syracuseStep 1557713 = 1168285) B1168285
theorem B1557731 : Blo 1036608 1557731 := bstep (se 1 (by rfl) ⟨1168298, by rfl⟩ : syracuseStep 1557731 = 2336597) B2336597
theorem B1557761 : Blo 1036608 1557761 := bstep (se 2 (by rfl) ⟨584160, by rfl⟩ : syracuseStep 1557761 = 1168321) B1168321
theorem B1557779 : Blo 1036608 1557779 := bstep (se 1 (by rfl) ⟨1168334, by rfl⟩ : syracuseStep 1557779 = 2336669) B2336669
theorem B1557809 : Blo 1036608 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B1754419 : Blo 1036608 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B1557827 : Blo 1036608 1557827 := bstep (se 1 (by rfl) ⟨1168370, by rfl⟩ : syracuseStep 1557827 = 2336741) B2336741
theorem B1557857 : Blo 1036608 1557857 := bstep (se 2 (by rfl) ⟨584196, by rfl⟩ : syracuseStep 1557857 = 1168393) B1168393
theorem B5916017 : Blo 1036608 5916017 := bstep (se 2 (by rfl) ⟨2218506, by rfl⟩ : syracuseStep 5916017 = 4437013) B4437013
theorem B1557875 : Blo 1036608 1557875 := bstep (se 1 (by rfl) ⟨1168406, by rfl⟩ : syracuseStep 1557875 = 2336813) B2336813
theorem B1557905 : Blo 1036608 1557905 := bstep (se 2 (by rfl) ⟨584214, by rfl⟩ : syracuseStep 1557905 = 1168429) B1168429
theorem B1557923 : Blo 1036608 1557923 := bstep (se 1 (by rfl) ⟨1168442, by rfl⟩ : syracuseStep 1557923 = 2336885) B2336885
theorem B1557953 : Blo 1036608 1557953 := bstep (se 2 (by rfl) ⟨584232, by rfl⟩ : syracuseStep 1557953 = 1168465) B1168465
theorem B1754561 : Blo 1036608 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1557971 : Blo 1036608 1557971 := bstep (se 1 (by rfl) ⟨1168478, by rfl⟩ : syracuseStep 1557971 = 2336957) B2336957
theorem B1558001 : Blo 1036608 1558001 := bstep (se 2 (by rfl) ⟨584250, by rfl⟩ : syracuseStep 1558001 = 1168501) B1168501
theorem B1558019 : Blo 1036608 1558019 := bstep (se 1 (by rfl) ⟨1168514, by rfl⟩ : syracuseStep 1558019 = 2337029) B2337029
theorem B2803213 : Blo 1036608 2803213 := bstep (se 3 (by rfl) ⟨525602, by rfl⟩ : syracuseStep 2803213 = 1051205) B1051205
theorem B1558049 : Blo 1036608 1558049 := bstep (se 2 (by rfl) ⟨584268, by rfl⟩ : syracuseStep 1558049 = 1168537) B1168537
theorem B1558067 : Blo 1036608 1558067 := bstep (se 1 (by rfl) ⟨1168550, by rfl⟩ : syracuseStep 1558067 = 2337101) B2337101
theorem B1754689 : Blo 1036608 1754689 := bstep (se 2 (by rfl) ⟨658008, by rfl⟩ : syracuseStep 1754689 = 1316017) B1316017
theorem B1558097 : Blo 1036608 1558097 := bstep (se 2 (by rfl) ⟨584286, by rfl⟩ : syracuseStep 1558097 = 1168573) B1168573
theorem B1558115 : Blo 1036608 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B1754723 : Blo 1036608 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B1558145 : Blo 1036608 1558145 := bstep (se 2 (by rfl) ⟨584304, by rfl⟩ : syracuseStep 1558145 = 1168609) B1168609
theorem B1558163 : Blo 1036608 1558163 := bstep (se 1 (by rfl) ⟨1168622, by rfl⟩ : syracuseStep 1558163 = 2337245) B2337245
theorem B1558193 : Blo 1036608 1558193 := bstep (se 2 (by rfl) ⟨584322, by rfl⟩ : syracuseStep 1558193 = 1168645) B1168645
theorem B1558211 : Blo 1036608 1558211 := bstep (se 1 (by rfl) ⟨1168658, by rfl⟩ : syracuseStep 1558211 = 2337317) B2337317
theorem B1558241 : Blo 1036608 1558241 := bstep (se 2 (by rfl) ⟨584340, by rfl⟩ : syracuseStep 1558241 = 1168681) B1168681
theorem B1754851 : Blo 1036608 1754851 := bstep (se 1 (by rfl) ⟨1316138, by rfl⟩ : syracuseStep 1754851 = 2632277) B2632277
theorem B1558259 : Blo 1036608 1558259 := bstep (se 1 (by rfl) ⟨1168694, by rfl⟩ : syracuseStep 1558259 = 2337389) B2337389
theorem B5064461 : Blo 1036608 5064461 := bstep (se 3 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 5064461 = 1899173) B1899173
theorem B1558289 : Blo 1036608 1558289 := bstep (se 2 (by rfl) ⟨584358, by rfl⟩ : syracuseStep 1558289 = 1168717) B1168717
theorem B1558307 : Blo 1036608 1558307 := bstep (se 1 (by rfl) ⟨1168730, by rfl⟩ : syracuseStep 1558307 = 2337461) B2337461
theorem B22791989 : Blo 1036608 22791989 := bstep (se 5 (by rfl) ⟨1068374, by rfl⟩ : syracuseStep 22791989 = 2136749) B2136749
theorem B1558337 : Blo 1036608 1558337 := bstep (se 2 (by rfl) ⟨584376, by rfl⟩ : syracuseStep 1558337 = 1168753) B1168753
theorem B1558355 : Blo 1036608 1558355 := bstep (se 1 (by rfl) ⟨1168766, by rfl⟩ : syracuseStep 1558355 = 2337533) B2337533
theorem B1558385 : Blo 1036608 1558385 := bstep (se 2 (by rfl) ⟨584394, by rfl⟩ : syracuseStep 1558385 = 1168789) B1168789
theorem B1754993 : Blo 1036608 1754993 := bstep (se 2 (by rfl) ⟨658122, by rfl⟩ : syracuseStep 1754993 = 1316245) B1316245
theorem B3164017 : Blo 1036608 3164017 := bstep (se 2 (by rfl) ⟨1186506, by rfl⟩ : syracuseStep 3164017 = 2373013) B2373013
theorem B1558403 : Blo 1036608 1558403 := bstep (se 1 (by rfl) ⟨1168802, by rfl⟩ : syracuseStep 1558403 = 2337605) B2337605
theorem B1558433 : Blo 1036608 1558433 := bstep (se 2 (by rfl) ⟨584412, by rfl⟩ : syracuseStep 1558433 = 1168825) B1168825
theorem B1558451 : Blo 1036608 1558451 := bstep (se 1 (by rfl) ⟨1168838, by rfl⟩ : syracuseStep 1558451 = 2337677) B2337677
theorem B3196867 : Blo 1036608 3196867 := bstep (se 1 (by rfl) ⟨2397650, by rfl⟩ : syracuseStep 3196867 = 4795301) B4795301
theorem B1558481 : Blo 1036608 1558481 := bstep (se 2 (by rfl) ⟨584430, by rfl⟩ : syracuseStep 1558481 = 1168861) B1168861
theorem B1558499 : Blo 1036608 1558499 := bstep (se 1 (by rfl) ⟨1168874, by rfl⟩ : syracuseStep 1558499 = 2337749) B2337749
theorem B1755121 : Blo 1036608 1755121 := bstep (se 2 (by rfl) ⟨658170, by rfl⟩ : syracuseStep 1755121 = 1316341) B1316341
theorem B1558529 : Blo 1036608 1558529 := bstep (se 2 (by rfl) ⟨584448, by rfl⟩ : syracuseStep 1558529 = 1168897) B1168897
theorem B1558547 : Blo 1036608 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B1755155 : Blo 1036608 1755155 := bstep (se 1 (by rfl) ⟨1316366, by rfl⟩ : syracuseStep 1755155 = 2632733) B2632733
theorem B1558577 : Blo 1036608 1558577 := bstep (se 2 (by rfl) ⟨584466, by rfl⟩ : syracuseStep 1558577 = 1168933) B1168933
theorem B11225141 : Blo 1036608 11225141 := bstep (se 5 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 11225141 = 1052357) B1052357
theorem B1558595 : Blo 1036608 1558595 := bstep (se 1 (by rfl) ⟨1168946, by rfl⟩ : syracuseStep 1558595 = 2337893) B2337893
theorem B1558625 : Blo 1036608 1558625 := bstep (se 2 (by rfl) ⟨584484, by rfl⟩ : syracuseStep 1558625 = 1168969) B1168969
theorem B53889137 : Blo 1036608 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B1558643 : Blo 1036608 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B1558673 : Blo 1036608 1558673 := bstep (se 2 (by rfl) ⟨584502, by rfl⟩ : syracuseStep 1558673 = 1169005) B1169005
theorem B1755283 : Blo 1036608 1755283 := bstep (se 1 (by rfl) ⟨1316462, by rfl⟩ : syracuseStep 1755283 = 2632925) B2632925
theorem B1558691 : Blo 1036608 1558691 := bstep (se 1 (by rfl) ⟨1169018, by rfl⟩ : syracuseStep 1558691 = 2338037) B2338037
theorem B3557549 : Blo 1036608 3557549 := bstep (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) B1334081
theorem B1558721 : Blo 1036608 1558721 := bstep (se 2 (by rfl) ⟨584520, by rfl⟩ : syracuseStep 1558721 = 1169041) B1169041
theorem B13289669 : Blo 1036608 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B1558739 : Blo 1036608 1558739 := bstep (se 1 (by rfl) ⟨1169054, by rfl⟩ : syracuseStep 1558739 = 2338109) B2338109
theorem B1558769 : Blo 1036608 1558769 := bstep (se 2 (by rfl) ⟨584538, by rfl⟩ : syracuseStep 1558769 = 1169077) B1169077
theorem B1558787 : Blo 1036608 1558787 := bstep (se 1 (by rfl) ⟨1169090, by rfl⟩ : syracuseStep 1558787 = 2338181) B2338181
theorem B1558817 : Blo 1036608 1558817 := bstep (se 2 (by rfl) ⟨584556, by rfl⟩ : syracuseStep 1558817 = 1169113) B1169113
theorem B1755425 : Blo 1036608 1755425 := bstep (se 2 (by rfl) ⟨658284, by rfl⟩ : syracuseStep 1755425 = 1316569) B1316569
theorem B1558835 : Blo 1036608 1558835 := bstep (se 1 (by rfl) ⟨1169126, by rfl⟩ : syracuseStep 1558835 = 2338253) B2338253
theorem B1558865 : Blo 1036608 1558865 := bstep (se 2 (by rfl) ⟨584574, by rfl⟩ : syracuseStep 1558865 = 1169149) B1169149
theorem B1558883 : Blo 1036608 1558883 := bstep (se 1 (by rfl) ⟨1169162, by rfl⟩ : syracuseStep 1558883 = 2338325) B2338325
theorem B1558913 : Blo 1036608 1558913 := bstep (se 2 (by rfl) ⟨584592, by rfl⟩ : syracuseStep 1558913 = 1169185) B1169185
theorem B1558931 : Blo 1036608 1558931 := bstep (se 1 (by rfl) ⟨1169198, by rfl⟩ : syracuseStep 1558931 = 2338397) B2338397
theorem B1755553 : Blo 1036608 1755553 := bstep (se 2 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 1755553 = 1316665) B1316665
theorem B1558961 : Blo 1036608 1558961 := bstep (se 2 (by rfl) ⟨584610, by rfl⟩ : syracuseStep 1558961 = 1169221) B1169221
theorem B1558979 : Blo 1036608 1558979 := bstep (se 1 (by rfl) ⟨1169234, by rfl⟩ : syracuseStep 1558979 = 2338469) B2338469
theorem B1755587 : Blo 1036608 1755587 := bstep (se 1 (by rfl) ⟨1316690, by rfl⟩ : syracuseStep 1755587 = 2633381) B2633381
theorem B1559009 : Blo 1036608 1559009 := bstep (se 2 (by rfl) ⟨584628, by rfl⟩ : syracuseStep 1559009 = 1169257) B1169257
theorem B1559027 : Blo 1036608 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B1559057 : Blo 1036608 1559057 := bstep (se 2 (by rfl) ⟨584646, by rfl⟩ : syracuseStep 1559057 = 1169293) B1169293
theorem B1559075 : Blo 1036608 1559075 := bstep (se 1 (by rfl) ⟨1169306, by rfl⟩ : syracuseStep 1559075 = 2338613) B2338613
theorem B4999715 : Blo 1036608 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B1559105 : Blo 1036608 1559105 := bstep (se 2 (by rfl) ⟨584664, by rfl⟩ : syracuseStep 1559105 = 1169329) B1169329
theorem B1755715 : Blo 1036608 1755715 := bstep (se 1 (by rfl) ⟨1316786, by rfl⟩ : syracuseStep 1755715 = 2633573) B2633573
theorem B1559123 : Blo 1036608 1559123 := bstep (se 1 (by rfl) ⟨1169342, by rfl⟩ : syracuseStep 1559123 = 2338685) B2338685
theorem B1559153 : Blo 1036608 1559153 := bstep (se 2 (by rfl) ⟨584682, by rfl⟩ : syracuseStep 1559153 = 1169365) B1169365
theorem B1559171 : Blo 1036608 1559171 := bstep (se 1 (by rfl) ⟨1169378, by rfl⟩ : syracuseStep 1559171 = 2338757) B2338757
theorem B7883405 : Blo 1036608 7883405 := bstep (se 3 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 7883405 = 2956277) B2956277
theorem B1559201 : Blo 1036608 1559201 := bstep (se 2 (by rfl) ⟨584700, by rfl⟩ : syracuseStep 1559201 = 1169401) B1169401
theorem B2214577 : Blo 1036608 2214577 := bstep (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) B1660933
theorem B1559219 : Blo 1036608 1559219 := bstep (se 1 (by rfl) ⟨1169414, by rfl⟩ : syracuseStep 1559219 = 2338829) B2338829
theorem B1559249 : Blo 1036608 1559249 := bstep (se 2 (by rfl) ⟨584718, by rfl⟩ : syracuseStep 1559249 = 1169437) B1169437
theorem B1755857 : Blo 1036608 1755857 := bstep (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) B1316893
theorem B1559267 : Blo 1036608 1559267 := bstep (se 1 (by rfl) ⟨1169450, by rfl⟩ : syracuseStep 1559267 = 2338901) B2338901
theorem B1559297 : Blo 1036608 1559297 := bstep (se 2 (by rfl) ⟨584736, by rfl⟩ : syracuseStep 1559297 = 1169473) B1169473
theorem B1559315 : Blo 1036608 1559315 := bstep (se 1 (by rfl) ⟨1169486, by rfl⟩ : syracuseStep 1559315 = 2338973) B2338973
theorem B5917475 : Blo 1036608 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B1559345 : Blo 1036608 1559345 := bstep (se 2 (by rfl) ⟨584754, by rfl⟩ : syracuseStep 1559345 = 1169509) B1169509
theorem B1559363 : Blo 1036608 1559363 := bstep (se 1 (by rfl) ⟨1169522, by rfl⟩ : syracuseStep 1559363 = 2339045) B2339045
theorem B1755985 : Blo 1036608 1755985 := bstep (se 2 (by rfl) ⟨658494, by rfl⟩ : syracuseStep 1755985 = 1316989) B1316989
theorem B1559393 : Blo 1036608 1559393 := bstep (se 2 (by rfl) ⟨584772, by rfl⟩ : syracuseStep 1559393 = 1169545) B1169545
theorem B3328877 : Blo 1036608 3328877 := bstep (se 3 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 3328877 = 1248329) B1248329
theorem B1559411 : Blo 1036608 1559411 := bstep (se 1 (by rfl) ⟨1169558, by rfl⟩ : syracuseStep 1559411 = 2339117) B2339117
theorem B1756019 : Blo 1036608 1756019 := bstep (se 1 (by rfl) ⟨1317014, by rfl⟩ : syracuseStep 1756019 = 2634029) B2634029
theorem B1559441 : Blo 1036608 1559441 := bstep (se 2 (by rfl) ⟨584790, by rfl⟩ : syracuseStep 1559441 = 1169581) B1169581
theorem B1559459 : Blo 1036608 1559459 := bstep (se 1 (by rfl) ⟨1169594, by rfl⟩ : syracuseStep 1559459 = 2339189) B2339189
theorem B1559489 : Blo 1036608 1559489 := bstep (se 2 (by rfl) ⟨584808, by rfl⟩ : syracuseStep 1559489 = 1169617) B1169617
theorem B1559507 : Blo 1036608 1559507 := bstep (se 1 (by rfl) ⟨1169630, by rfl⟩ : syracuseStep 1559507 = 2339261) B2339261
theorem B1559537 : Blo 1036608 1559537 := bstep (se 2 (by rfl) ⟨584826, by rfl⟩ : syracuseStep 1559537 = 1169653) B1169653
theorem B1166323 : Blo 1036608 1166323 := bstep (se 1 (by rfl) ⟨874742, by rfl⟩ : syracuseStep 1166323 = 1749485) B1749485
theorem B1559555 : Blo 1036608 1559555 := bstep (se 1 (by rfl) ⟨1169666, by rfl⟩ : syracuseStep 1559555 = 2339333) B2339333
theorem B1559585 : Blo 1036608 1559585 := bstep (se 2 (by rfl) ⟨584844, by rfl⟩ : syracuseStep 1559585 = 1169689) B1169689
theorem B1559603 : Blo 1036608 1559603 := bstep (se 1 (by rfl) ⟨1169702, by rfl⟩ : syracuseStep 1559603 = 2339405) B2339405
theorem B1559633 : Blo 1036608 1559633 := bstep (se 2 (by rfl) ⟨584862, by rfl⟩ : syracuseStep 1559633 = 1169725) B1169725
theorem B1559651 : Blo 1036608 1559651 := bstep (se 1 (by rfl) ⟨1169738, by rfl⟩ : syracuseStep 1559651 = 2339477) B2339477
theorem B1559681 : Blo 1036608 1559681 := bstep (se 2 (by rfl) ⟨584880, by rfl⟩ : syracuseStep 1559681 = 1169761) B1169761
theorem B1166467 : Blo 1036608 1166467 := bstep (se 1 (by rfl) ⟨874850, by rfl⟩ : syracuseStep 1166467 = 1749701) B1749701
theorem B1559699 : Blo 1036608 1559699 := bstep (se 1 (by rfl) ⟨1169774, by rfl⟩ : syracuseStep 1559699 = 2339549) B2339549
theorem B1559729 : Blo 1036608 1559729 := bstep (se 2 (by rfl) ⟨584898, by rfl⟩ : syracuseStep 1559729 = 1169797) B1169797
theorem B1559747 : Blo 1036608 1559747 := bstep (se 1 (by rfl) ⟨1169810, by rfl⟩ : syracuseStep 1559747 = 2339621) B2339621
theorem B1559777 : Blo 1036608 1559777 := bstep (se 2 (by rfl) ⟨584916, by rfl⟩ : syracuseStep 1559777 = 1169833) B1169833
theorem B1559795 : Blo 1036608 1559795 := bstep (se 1 (by rfl) ⟨1169846, by rfl⟩ : syracuseStep 1559795 = 2339693) B2339693
theorem B1559825 : Blo 1036608 1559825 := bstep (se 2 (by rfl) ⟨584934, by rfl⟩ : syracuseStep 1559825 = 1169869) B1169869
theorem B1166611 : Blo 1036608 1166611 := bstep (se 1 (by rfl) ⟨874958, by rfl⟩ : syracuseStep 1166611 = 1749917) B1749917
theorem B1559843 : Blo 1036608 1559843 := bstep (se 1 (by rfl) ⟨1169882, by rfl⟩ : syracuseStep 1559843 = 2339765) B2339765
theorem B1559873 : Blo 1036608 1559873 := bstep (se 2 (by rfl) ⟨584952, by rfl⟩ : syracuseStep 1559873 = 1169905) B1169905
theorem B1559891 : Blo 1036608 1559891 := bstep (se 1 (by rfl) ⟨1169918, by rfl⟩ : syracuseStep 1559891 = 2339837) B2339837
theorem B1559921 : Blo 1036608 1559921 := bstep (se 2 (by rfl) ⟨584970, by rfl⟩ : syracuseStep 1559921 = 1169941) B1169941
theorem B5000561 : Blo 1036608 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B1559939 : Blo 1036608 1559939 := bstep (se 1 (by rfl) ⟨1169954, by rfl⟩ : syracuseStep 1559939 = 2339909) B2339909
theorem B1559969 : Blo 1036608 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B1166755 : Blo 1036608 1166755 := bstep (se 1 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 1166755 = 1750133) B1750133
theorem B1559987 : Blo 1036608 1559987 := bstep (se 1 (by rfl) ⟨1169990, by rfl⟩ : syracuseStep 1559987 = 2339981) B2339981
theorem B2215363 : Blo 1036608 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B1560017 : Blo 1036608 1560017 := bstep (se 2 (by rfl) ⟨585006, by rfl⟩ : syracuseStep 1560017 = 1170013) B1170013
theorem B1560035 : Blo 1036608 1560035 := bstep (se 1 (by rfl) ⟨1170026, by rfl⟩ : syracuseStep 1560035 = 2340053) B2340053
theorem B1560065 : Blo 1036608 1560065 := bstep (se 2 (by rfl) ⟨585024, by rfl⟩ : syracuseStep 1560065 = 1170049) B1170049
theorem B1560083 : Blo 1036608 1560083 := bstep (se 1 (by rfl) ⟨1170062, by rfl⟩ : syracuseStep 1560083 = 2340125) B2340125
theorem B1560113 : Blo 1036608 1560113 := bstep (se 2 (by rfl) ⟨585042, by rfl⟩ : syracuseStep 1560113 = 1170085) B1170085
theorem B1166899 : Blo 1036608 1166899 := bstep (se 1 (by rfl) ⟨875174, by rfl⟩ : syracuseStep 1166899 = 1750349) B1750349
theorem B1560131 : Blo 1036608 1560131 := bstep (se 1 (by rfl) ⟨1170098, by rfl⟩ : syracuseStep 1560131 = 2340197) B2340197
theorem B1560161 : Blo 1036608 1560161 := bstep (se 2 (by rfl) ⟨585060, by rfl⟩ : syracuseStep 1560161 = 1170121) B1170121
theorem B3001969 : Blo 1036608 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B1560179 : Blo 1036608 1560179 := bstep (se 1 (by rfl) ⟨1170134, by rfl⟩ : syracuseStep 1560179 = 2340269) B2340269
theorem B1560209 : Blo 1036608 1560209 := bstep (se 2 (by rfl) ⟨585078, by rfl⟩ : syracuseStep 1560209 = 1170157) B1170157
theorem B1560227 : Blo 1036608 1560227 := bstep (se 1 (by rfl) ⟨1170170, by rfl⟩ : syracuseStep 1560227 = 2340341) B2340341
theorem B1560257 : Blo 1036608 1560257 := bstep (se 2 (by rfl) ⟨585096, by rfl⟩ : syracuseStep 1560257 = 1170193) B1170193
theorem B1167043 : Blo 1036608 1167043 := bstep (se 1 (by rfl) ⟨875282, by rfl⟩ : syracuseStep 1167043 = 1750565) B1750565
theorem B1560275 : Blo 1036608 1560275 := bstep (se 1 (by rfl) ⟨1170206, by rfl⟩ : syracuseStep 1560275 = 2340413) B2340413
theorem B1560305 : Blo 1036608 1560305 := bstep (se 2 (by rfl) ⟨585114, by rfl⟩ : syracuseStep 1560305 = 1170229) B1170229
theorem B1560323 : Blo 1036608 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B1560353 : Blo 1036608 1560353 := bstep (se 2 (by rfl) ⟨585132, by rfl⟩ : syracuseStep 1560353 = 1170265) B1170265
theorem B1560371 : Blo 1036608 1560371 := bstep (se 1 (by rfl) ⟨1170278, by rfl⟩ : syracuseStep 1560371 = 2340557) B2340557
theorem B1560401 : Blo 1036608 1560401 := bstep (se 2 (by rfl) ⟨585150, by rfl⟩ : syracuseStep 1560401 = 1170301) B1170301
theorem B1167187 : Blo 1036608 1167187 := bstep (se 1 (by rfl) ⟨875390, by rfl⟩ : syracuseStep 1167187 = 1750781) B1750781
theorem B1560419 : Blo 1036608 1560419 := bstep (se 1 (by rfl) ⟨1170314, by rfl⟩ : syracuseStep 1560419 = 2340629) B2340629
theorem B5263217 : Blo 1036608 5263217 := bstep (se 2 (by rfl) ⟨1973706, by rfl⟩ : syracuseStep 5263217 = 3947413) B3947413
theorem B1560449 : Blo 1036608 1560449 := bstep (se 2 (by rfl) ⟨585168, by rfl⟩ : syracuseStep 1560449 = 1170337) B1170337
theorem B2805635 : Blo 1036608 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B1560467 : Blo 1036608 1560467 := bstep (se 1 (by rfl) ⟨1170350, by rfl⟩ : syracuseStep 1560467 = 2340701) B2340701
theorem B1560497 : Blo 1036608 1560497 := bstep (se 2 (by rfl) ⟨585186, by rfl⟩ : syracuseStep 1560497 = 1170373) B1170373
theorem B1560515 : Blo 1036608 1560515 := bstep (se 1 (by rfl) ⟨1170386, by rfl⟩ : syracuseStep 1560515 = 2340773) B2340773
theorem B1560545 : Blo 1036608 1560545 := bstep (se 2 (by rfl) ⟨585204, by rfl⟩ : syracuseStep 1560545 = 1170409) B1170409
theorem B1167331 : Blo 1036608 1167331 := bstep (se 1 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 1167331 = 1750997) B1750997
theorem B3002339 : Blo 1036608 3002339 := bstep (se 1 (by rfl) ⟨2251754, by rfl⟩ : syracuseStep 3002339 = 4503509) B4503509
theorem B1560563 : Blo 1036608 1560563 := bstep (se 1 (by rfl) ⟨1170422, by rfl⟩ : syracuseStep 1560563 = 2340845) B2340845
theorem B1560593 : Blo 1036608 1560593 := bstep (se 2 (by rfl) ⟨585222, by rfl⟩ : syracuseStep 1560593 = 1170445) B1170445
theorem B1560611 : Blo 1036608 1560611 := bstep (se 1 (by rfl) ⟨1170458, by rfl⟩ : syracuseStep 1560611 = 2340917) B2340917
theorem B1560641 : Blo 1036608 1560641 := bstep (se 2 (by rfl) ⟨585240, by rfl⟩ : syracuseStep 1560641 = 1170481) B1170481
theorem B1560659 : Blo 1036608 1560659 := bstep (se 1 (by rfl) ⟨1170494, by rfl⟩ : syracuseStep 1560659 = 2340989) B2340989
theorem B1560689 : Blo 1036608 1560689 := bstep (se 2 (by rfl) ⟨585258, by rfl⟩ : syracuseStep 1560689 = 1170517) B1170517
theorem B1167475 : Blo 1036608 1167475 := bstep (se 1 (by rfl) ⟨875606, by rfl⟩ : syracuseStep 1167475 = 1751213) B1751213
theorem B1560707 : Blo 1036608 1560707 := bstep (se 1 (by rfl) ⟨1170530, by rfl⟩ : syracuseStep 1560707 = 2341061) B2341061
theorem B6312077 : Blo 1036608 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B2216081 : Blo 1036608 2216081 := bstep (se 2 (by rfl) ⟨831030, by rfl⟩ : syracuseStep 2216081 = 1662061) B1662061
theorem B1560737 : Blo 1036608 1560737 := bstep (se 2 (by rfl) ⟨585276, by rfl⟩ : syracuseStep 1560737 = 1170553) B1170553
theorem B1560755 : Blo 1036608 1560755 := bstep (se 1 (by rfl) ⟨1170566, by rfl⟩ : syracuseStep 1560755 = 2341133) B2341133
theorem B1560785 : Blo 1036608 1560785 := bstep (se 2 (by rfl) ⟨585294, by rfl⟩ : syracuseStep 1560785 = 1170589) B1170589
theorem B1560803 : Blo 1036608 1560803 := bstep (se 1 (by rfl) ⟨1170602, by rfl⟩ : syracuseStep 1560803 = 2341205) B2341205
theorem B1560833 : Blo 1036608 1560833 := bstep (se 2 (by rfl) ⟨585312, by rfl⟩ : syracuseStep 1560833 = 1170625) B1170625
theorem B1167619 : Blo 1036608 1167619 := bstep (se 1 (by rfl) ⟨875714, by rfl⟩ : syracuseStep 1167619 = 1751429) B1751429
theorem B4444429 : Blo 1036608 4444429 := bstep (se 3 (by rfl) ⟨833330, by rfl⟩ : syracuseStep 4444429 = 1666661) B1666661
theorem B1560851 : Blo 1036608 1560851 := bstep (se 1 (by rfl) ⟨1170638, by rfl⟩ : syracuseStep 1560851 = 2341277) B2341277
theorem B1560881 : Blo 1036608 1560881 := bstep (se 2 (by rfl) ⟨585330, by rfl⟩ : syracuseStep 1560881 = 1170661) B1170661
theorem B1036611 : Blo 1036608 1036611 := bstep (se 1 (by rfl) ⟨777458, by rfl⟩ : syracuseStep 1036611 = 1554917) B1554917
theorem B1560899 : Blo 1036608 1560899 := bstep (se 1 (by rfl) ⟨1170674, by rfl⟩ : syracuseStep 1560899 = 2341349) B2341349
theorem B1036627 : Blo 1036608 1036627 := bstep (se 1 (by rfl) ⟨777470, by rfl⟩ : syracuseStep 1036627 = 1554941) B1554941
theorem B1036643 : Blo 1036608 1036643 := bstep (se 1 (by rfl) ⟨777482, by rfl⟩ : syracuseStep 1036643 = 1554965) B1554965
theorem B1036659 : Blo 1036608 1036659 := bstep (se 1 (by rfl) ⟨777494, by rfl⟩ : syracuseStep 1036659 = 1554989) B1554989
theorem B1036675 : Blo 1036608 1036675 := bstep (se 1 (by rfl) ⟨777506, by rfl⟩ : syracuseStep 1036675 = 1555013) B1555013
theorem B1036691 : Blo 1036608 1036691 := bstep (se 1 (by rfl) ⟨777518, by rfl⟩ : syracuseStep 1036691 = 1555037) B1555037
theorem B1167763 : Blo 1036608 1167763 := bstep (se 1 (by rfl) ⟨875822, by rfl⟩ : syracuseStep 1167763 = 1751645) B1751645
theorem B1036707 : Blo 1036608 1036707 := bstep (se 1 (by rfl) ⟨777530, by rfl⟩ : syracuseStep 1036707 = 1555061) B1555061
theorem B1036723 : Blo 1036608 1036723 := bstep (se 1 (by rfl) ⟨777542, by rfl⟩ : syracuseStep 1036723 = 1555085) B1555085
theorem B1036739 : Blo 1036608 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B1036755 : Blo 1036608 1036755 := bstep (se 1 (by rfl) ⟨777566, by rfl⟩ : syracuseStep 1036755 = 1555133) B1555133
theorem B1036771 : Blo 1036608 1036771 := bstep (se 1 (by rfl) ⟨777578, by rfl⟩ : syracuseStep 1036771 = 1555157) B1555157
theorem B1036787 : Blo 1036608 1036787 := bstep (se 1 (by rfl) ⟨777590, by rfl⟩ : syracuseStep 1036787 = 1555181) B1555181
theorem B1036803 : Blo 1036608 1036803 := bstep (se 1 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 1036803 = 1555205) B1555205
theorem B1036819 : Blo 1036608 1036819 := bstep (se 1 (by rfl) ⟨777614, by rfl⟩ : syracuseStep 1036819 = 1555229) B1555229
theorem B1036835 : Blo 1036608 1036835 := bstep (se 1 (by rfl) ⟨777626, by rfl⟩ : syracuseStep 1036835 = 1555253) B1555253
theorem B1167907 : Blo 1036608 1167907 := bstep (se 1 (by rfl) ⟨875930, by rfl⟩ : syracuseStep 1167907 = 1751861) B1751861
theorem B1036851 : Blo 1036608 1036851 := bstep (se 1 (by rfl) ⟨777638, by rfl⟩ : syracuseStep 1036851 = 1555277) B1555277
theorem B1036867 : Blo 1036608 1036867 := bstep (se 1 (by rfl) ⟨777650, by rfl⟩ : syracuseStep 1036867 = 1555301) B1555301
theorem B1036883 : Blo 1036608 1036883 := bstep (se 1 (by rfl) ⟨777662, by rfl⟩ : syracuseStep 1036883 = 1555325) B1555325
theorem B1036899 : Blo 1036608 1036899 := bstep (se 1 (by rfl) ⟨777674, by rfl⟩ : syracuseStep 1036899 = 1555349) B1555349
theorem B1036915 : Blo 1036608 1036915 := bstep (se 1 (by rfl) ⟨777686, by rfl⟩ : syracuseStep 1036915 = 1555373) B1555373
theorem B1036931 : Blo 1036608 1036931 := bstep (se 1 (by rfl) ⟨777698, by rfl⟩ : syracuseStep 1036931 = 1555397) B1555397
theorem B2216593 : Blo 1036608 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B1036947 : Blo 1036608 1036947 := bstep (se 1 (by rfl) ⟨777710, by rfl⟩ : syracuseStep 1036947 = 1555421) B1555421
theorem B1036963 : Blo 1036608 1036963 := bstep (se 1 (by rfl) ⟨777722, by rfl⟩ : syracuseStep 1036963 = 1555445) B1555445
theorem B3330733 : Blo 1036608 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B1036979 : Blo 1036608 1036979 := bstep (se 1 (by rfl) ⟨777734, by rfl⟩ : syracuseStep 1036979 = 1555469) B1555469
theorem B1168051 : Blo 1036608 1168051 := bstep (se 1 (by rfl) ⟨876038, by rfl⟩ : syracuseStep 1168051 = 1752077) B1752077
theorem B1036995 : Blo 1036608 1036995 := bstep (se 1 (by rfl) ⟨777746, by rfl⟩ : syracuseStep 1036995 = 1555493) B1555493
theorem B1037011 : Blo 1036608 1037011 := bstep (se 1 (by rfl) ⟨777758, by rfl⟩ : syracuseStep 1037011 = 1555517) B1555517
theorem B1037027 : Blo 1036608 1037027 := bstep (se 1 (by rfl) ⟨777770, by rfl⟩ : syracuseStep 1037027 = 1555541) B1555541
theorem B1037043 : Blo 1036608 1037043 := bstep (se 1 (by rfl) ⟨777782, by rfl⟩ : syracuseStep 1037043 = 1555565) B1555565
theorem B1037059 : Blo 1036608 1037059 := bstep (se 1 (by rfl) ⟨777794, by rfl⟩ : syracuseStep 1037059 = 1555589) B1555589
theorem B1037075 : Blo 1036608 1037075 := bstep (se 1 (by rfl) ⟨777806, by rfl⟩ : syracuseStep 1037075 = 1555613) B1555613
theorem B1037091 : Blo 1036608 1037091 := bstep (se 1 (by rfl) ⟨777818, by rfl⟩ : syracuseStep 1037091 = 1555637) B1555637
theorem B1037107 : Blo 1036608 1037107 := bstep (se 1 (by rfl) ⟨777830, by rfl⟩ : syracuseStep 1037107 = 1555661) B1555661
theorem B1037123 : Blo 1036608 1037123 := bstep (se 1 (by rfl) ⟨777842, by rfl⟩ : syracuseStep 1037123 = 1555685) B1555685
theorem B1168195 : Blo 1036608 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B1037139 : Blo 1036608 1037139 := bstep (se 1 (by rfl) ⟨777854, by rfl⟩ : syracuseStep 1037139 = 1555709) B1555709
theorem B1037155 : Blo 1036608 1037155 := bstep (se 1 (by rfl) ⟨777866, by rfl⟩ : syracuseStep 1037155 = 1555733) B1555733
theorem B1037171 : Blo 1036608 1037171 := bstep (se 1 (by rfl) ⟨777878, by rfl⟩ : syracuseStep 1037171 = 1555757) B1555757
theorem B1037187 : Blo 1036608 1037187 := bstep (se 1 (by rfl) ⟨777890, by rfl⟩ : syracuseStep 1037187 = 1555781) B1555781
theorem B1037203 : Blo 1036608 1037203 := bstep (se 1 (by rfl) ⟨777902, by rfl⟩ : syracuseStep 1037203 = 1555805) B1555805
theorem B1037219 : Blo 1036608 1037219 := bstep (se 1 (by rfl) ⟨777914, by rfl⟩ : syracuseStep 1037219 = 1555829) B1555829
theorem B1037235 : Blo 1036608 1037235 := bstep (se 1 (by rfl) ⟨777926, by rfl⟩ : syracuseStep 1037235 = 1555853) B1555853
theorem B1037251 : Blo 1036608 1037251 := bstep (se 1 (by rfl) ⟨777938, by rfl⟩ : syracuseStep 1037251 = 1555877) B1555877
theorem B1037267 : Blo 1036608 1037267 := bstep (se 1 (by rfl) ⟨777950, by rfl⟩ : syracuseStep 1037267 = 1555901) B1555901
theorem B1168339 : Blo 1036608 1168339 := bstep (se 1 (by rfl) ⟨876254, by rfl⟩ : syracuseStep 1168339 = 1752509) B1752509
theorem B1037283 : Blo 1036608 1037283 := bstep (se 1 (by rfl) ⟨777962, by rfl⟩ : syracuseStep 1037283 = 1555925) B1555925
theorem B1037299 : Blo 1036608 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B1037315 : Blo 1036608 1037315 := bstep (se 1 (by rfl) ⟨777986, by rfl⟩ : syracuseStep 1037315 = 1555973) B1555973
theorem B1037331 : Blo 1036608 1037331 := bstep (se 1 (by rfl) ⟨777998, by rfl⟩ : syracuseStep 1037331 = 1555997) B1555997
theorem B1037347 : Blo 1036608 1037347 := bstep (se 1 (by rfl) ⟨778010, by rfl⟩ : syracuseStep 1037347 = 1556021) B1556021
theorem B1037363 : Blo 1036608 1037363 := bstep (se 1 (by rfl) ⟨778022, by rfl⟩ : syracuseStep 1037363 = 1556045) B1556045
theorem B1037379 : Blo 1036608 1037379 := bstep (se 1 (by rfl) ⟨778034, by rfl⟩ : syracuseStep 1037379 = 1556069) B1556069
theorem B1037395 : Blo 1036608 1037395 := bstep (se 1 (by rfl) ⟨778046, by rfl⟩ : syracuseStep 1037395 = 1556093) B1556093
theorem B1037411 : Blo 1036608 1037411 := bstep (se 1 (by rfl) ⟨778058, by rfl⟩ : syracuseStep 1037411 = 1556117) B1556117
theorem B1168483 : Blo 1036608 1168483 := bstep (se 1 (by rfl) ⟨876362, by rfl⟩ : syracuseStep 1168483 = 1752725) B1752725
theorem B1037427 : Blo 1036608 1037427 := bstep (se 1 (by rfl) ⟨778070, by rfl⟩ : syracuseStep 1037427 = 1556141) B1556141
theorem B1037443 : Blo 1036608 1037443 := bstep (se 1 (by rfl) ⟨778082, by rfl⟩ : syracuseStep 1037443 = 1556165) B1556165
theorem B1037459 : Blo 1036608 1037459 := bstep (se 1 (by rfl) ⟨778094, by rfl⟩ : syracuseStep 1037459 = 1556189) B1556189
theorem B1037475 : Blo 1036608 1037475 := bstep (se 1 (by rfl) ⟨778106, by rfl⟩ : syracuseStep 1037475 = 1556213) B1556213
theorem B1037491 : Blo 1036608 1037491 := bstep (se 1 (by rfl) ⟨778118, by rfl⟩ : syracuseStep 1037491 = 1556237) B1556237
theorem B1037507 : Blo 1036608 1037507 := bstep (se 1 (by rfl) ⟨778130, by rfl⟩ : syracuseStep 1037507 = 1556261) B1556261
theorem B1037523 : Blo 1036608 1037523 := bstep (se 1 (by rfl) ⟨778142, by rfl⟩ : syracuseStep 1037523 = 1556285) B1556285
theorem B1037539 : Blo 1036608 1037539 := bstep (se 1 (by rfl) ⟨778154, by rfl⟩ : syracuseStep 1037539 = 1556309) B1556309
theorem B1037555 : Blo 1036608 1037555 := bstep (se 1 (by rfl) ⟨778166, by rfl⟩ : syracuseStep 1037555 = 1556333) B1556333
theorem B1168627 : Blo 1036608 1168627 := bstep (se 1 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 1168627 = 1752941) B1752941
theorem B1037571 : Blo 1036608 1037571 := bstep (se 1 (by rfl) ⟨778178, by rfl⟩ : syracuseStep 1037571 = 1556357) B1556357
theorem B1037587 : Blo 1036608 1037587 := bstep (se 1 (by rfl) ⟨778190, by rfl⟩ : syracuseStep 1037587 = 1556381) B1556381
theorem B1037603 : Blo 1036608 1037603 := bstep (se 1 (by rfl) ⟨778202, by rfl⟩ : syracuseStep 1037603 = 1556405) B1556405
theorem B5264675 : Blo 1036608 5264675 := bstep (se 1 (by rfl) ⟨3948506, by rfl⟩ : syracuseStep 5264675 = 7897013) B7897013
theorem B1037619 : Blo 1036608 1037619 := bstep (se 1 (by rfl) ⟨778214, by rfl⟩ : syracuseStep 1037619 = 1556429) B1556429
theorem B1037635 : Blo 1036608 1037635 := bstep (se 1 (by rfl) ⟨778226, by rfl⟩ : syracuseStep 1037635 = 1556453) B1556453
theorem B1037651 : Blo 1036608 1037651 := bstep (se 1 (by rfl) ⟨778238, by rfl⟩ : syracuseStep 1037651 = 1556477) B1556477
theorem B1037667 : Blo 1036608 1037667 := bstep (se 1 (by rfl) ⟨778250, by rfl⟩ : syracuseStep 1037667 = 1556501) B1556501
theorem B6313315 : Blo 1036608 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B1037683 : Blo 1036608 1037683 := bstep (se 1 (by rfl) ⟨778262, by rfl⟩ : syracuseStep 1037683 = 1556525) B1556525
theorem B1037699 : Blo 1036608 1037699 := bstep (se 1 (by rfl) ⟨778274, by rfl⟩ : syracuseStep 1037699 = 1556549) B1556549
theorem B1168771 : Blo 1036608 1168771 := bstep (se 1 (by rfl) ⟨876578, by rfl⟩ : syracuseStep 1168771 = 1753157) B1753157
theorem B1037715 : Blo 1036608 1037715 := bstep (se 1 (by rfl) ⟨778286, by rfl⟩ : syracuseStep 1037715 = 1556573) B1556573
theorem B1037731 : Blo 1036608 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B1037747 : Blo 1036608 1037747 := bstep (se 1 (by rfl) ⟨778310, by rfl⟩ : syracuseStep 1037747 = 1556621) B1556621
theorem B1037763 : Blo 1036608 1037763 := bstep (se 1 (by rfl) ⟨778322, by rfl⟩ : syracuseStep 1037763 = 1556645) B1556645
theorem B1037779 : Blo 1036608 1037779 := bstep (se 1 (by rfl) ⟨778334, by rfl⟩ : syracuseStep 1037779 = 1556669) B1556669
theorem B1037795 : Blo 1036608 1037795 := bstep (se 1 (by rfl) ⟨778346, by rfl⟩ : syracuseStep 1037795 = 1556693) B1556693
theorem B7886321 : Blo 1036608 7886321 := bstep (se 2 (by rfl) ⟨2957370, by rfl⟩ : syracuseStep 7886321 = 5914741) B5914741
theorem B1037811 : Blo 1036608 1037811 := bstep (se 1 (by rfl) ⟨778358, by rfl⟩ : syracuseStep 1037811 = 1556717) B1556717
theorem B1037827 : Blo 1036608 1037827 := bstep (se 1 (by rfl) ⟨778370, by rfl⟩ : syracuseStep 1037827 = 1556741) B1556741
theorem B1037843 : Blo 1036608 1037843 := bstep (se 1 (by rfl) ⟨778382, by rfl⟩ : syracuseStep 1037843 = 1556765) B1556765
theorem B1824275 : Blo 1036608 1824275 := bstep (se 1 (by rfl) ⟨1368206, by rfl⟩ : syracuseStep 1824275 = 2736413) B2736413
theorem B1168915 : Blo 1036608 1168915 := bstep (se 1 (by rfl) ⟨876686, by rfl⟩ : syracuseStep 1168915 = 1753373) B1753373
theorem B1037859 : Blo 1036608 1037859 := bstep (se 1 (by rfl) ⟨778394, by rfl⟩ : syracuseStep 1037859 = 1556789) B1556789
theorem B4216369 : Blo 1036608 4216369 := bstep (se 2 (by rfl) ⟨1581138, by rfl⟩ : syracuseStep 4216369 = 3162277) B3162277
theorem B1037875 : Blo 1036608 1037875 := bstep (se 1 (by rfl) ⟨778406, by rfl⟩ : syracuseStep 1037875 = 1556813) B1556813
theorem B1037891 : Blo 1036608 1037891 := bstep (se 1 (by rfl) ⟨778418, by rfl⟩ : syracuseStep 1037891 = 1556837) B1556837
theorem B1037907 : Blo 1036608 1037907 := bstep (se 1 (by rfl) ⟨778430, by rfl⟩ : syracuseStep 1037907 = 1556861) B1556861
theorem B1037923 : Blo 1036608 1037923 := bstep (se 1 (by rfl) ⟨778442, by rfl⟩ : syracuseStep 1037923 = 1556885) B1556885
theorem B9983587 : Blo 1036608 9983587 := bstep (se 1 (by rfl) ⟨7487690, by rfl⟩ : syracuseStep 9983587 = 14975381) B14975381
theorem B1037939 : Blo 1036608 1037939 := bstep (se 1 (by rfl) ⟨778454, by rfl⟩ : syracuseStep 1037939 = 1556909) B1556909
theorem B1037955 : Blo 1036608 1037955 := bstep (se 1 (by rfl) ⟨778466, by rfl⟩ : syracuseStep 1037955 = 1556933) B1556933
theorem B1037971 : Blo 1036608 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B1037987 : Blo 1036608 1037987 := bstep (se 1 (by rfl) ⟨778490, by rfl⟩ : syracuseStep 1037987 = 1556981) B1556981
theorem B1169059 : Blo 1036608 1169059 := bstep (se 1 (by rfl) ⟨876794, by rfl⟩ : syracuseStep 1169059 = 1753589) B1753589
theorem B1038003 : Blo 1036608 1038003 := bstep (se 1 (by rfl) ⟨778502, by rfl⟩ : syracuseStep 1038003 = 1557005) B1557005
theorem B1038019 : Blo 1036608 1038019 := bstep (se 1 (by rfl) ⟨778514, by rfl⟩ : syracuseStep 1038019 = 1557029) B1557029
theorem B1038035 : Blo 1036608 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B1332947 : Blo 1036608 1332947 := bstep (se 1 (by rfl) ⟨999710, by rfl⟩ : syracuseStep 1332947 = 1999421) B1999421
theorem B1038051 : Blo 1036608 1038051 := bstep (se 1 (by rfl) ⟨778538, by rfl⟩ : syracuseStep 1038051 = 1557077) B1557077
theorem B1038067 : Blo 1036608 1038067 := bstep (se 1 (by rfl) ⟨778550, by rfl⟩ : syracuseStep 1038067 = 1557101) B1557101
theorem B1038083 : Blo 1036608 1038083 := bstep (se 1 (by rfl) ⟨778562, by rfl⟩ : syracuseStep 1038083 = 1557125) B1557125
theorem B1038099 : Blo 1036608 1038099 := bstep (se 1 (by rfl) ⟨778574, by rfl⟩ : syracuseStep 1038099 = 1557149) B1557149
theorem B1038115 : Blo 1036608 1038115 := bstep (se 1 (by rfl) ⟨778586, by rfl⟩ : syracuseStep 1038115 = 1557173) B1557173
theorem B1038131 : Blo 1036608 1038131 := bstep (se 1 (by rfl) ⟨778598, by rfl⟩ : syracuseStep 1038131 = 1557197) B1557197
theorem B1169203 : Blo 1036608 1169203 := bstep (se 1 (by rfl) ⟨876902, by rfl⟩ : syracuseStep 1169203 = 1753805) B1753805
theorem B1038147 : Blo 1036608 1038147 := bstep (se 1 (by rfl) ⟨778610, by rfl⟩ : syracuseStep 1038147 = 1557221) B1557221
theorem B1038163 : Blo 1036608 1038163 := bstep (se 1 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 1038163 = 1557245) B1557245
theorem B1038179 : Blo 1036608 1038179 := bstep (se 1 (by rfl) ⟨778634, by rfl⟩ : syracuseStep 1038179 = 1557269) B1557269
theorem B1038195 : Blo 1036608 1038195 := bstep (se 1 (by rfl) ⟨778646, by rfl⟩ : syracuseStep 1038195 = 1557293) B1557293
theorem B1038211 : Blo 1036608 1038211 := bstep (se 1 (by rfl) ⟨778658, by rfl⟩ : syracuseStep 1038211 = 1557317) B1557317
theorem B1038227 : Blo 1036608 1038227 := bstep (se 1 (by rfl) ⟨778670, by rfl⟩ : syracuseStep 1038227 = 1557341) B1557341
theorem B1038243 : Blo 1036608 1038243 := bstep (se 1 (by rfl) ⟨778682, by rfl⟩ : syracuseStep 1038243 = 1557365) B1557365
theorem B1038259 : Blo 1036608 1038259 := bstep (se 1 (by rfl) ⟨778694, by rfl⟩ : syracuseStep 1038259 = 1557389) B1557389
theorem B1038275 : Blo 1036608 1038275 := bstep (se 1 (by rfl) ⟨778706, by rfl⟩ : syracuseStep 1038275 = 1557413) B1557413
theorem B1169347 : Blo 1036608 1169347 := bstep (se 1 (by rfl) ⟨877010, by rfl⟩ : syracuseStep 1169347 = 1754021) B1754021
theorem B7493573 : Blo 1036608 7493573 := bstep (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) B1405045
theorem B1038291 : Blo 1036608 1038291 := bstep (se 1 (by rfl) ⟨778718, by rfl⟩ : syracuseStep 1038291 = 1557437) B1557437
theorem B1038307 : Blo 1036608 1038307 := bstep (se 1 (by rfl) ⟨778730, by rfl⟩ : syracuseStep 1038307 = 1557461) B1557461
theorem B1038323 : Blo 1036608 1038323 := bstep (se 1 (by rfl) ⟨778742, by rfl⟩ : syracuseStep 1038323 = 1557485) B1557485
theorem B1038339 : Blo 1036608 1038339 := bstep (se 1 (by rfl) ⟨778754, by rfl⟩ : syracuseStep 1038339 = 1557509) B1557509
theorem B1038355 : Blo 1036608 1038355 := bstep (se 1 (by rfl) ⟨778766, by rfl⟩ : syracuseStep 1038355 = 1557533) B1557533
theorem B1038371 : Blo 1036608 1038371 := bstep (se 1 (by rfl) ⟨778778, by rfl⟩ : syracuseStep 1038371 = 1557557) B1557557
theorem B1038387 : Blo 1036608 1038387 := bstep (se 1 (by rfl) ⟨778790, by rfl⟩ : syracuseStep 1038387 = 1557581) B1557581
theorem B1038403 : Blo 1036608 1038403 := bstep (se 1 (by rfl) ⟨778802, by rfl⟩ : syracuseStep 1038403 = 1557605) B1557605
theorem B5265485 : Blo 1036608 5265485 := bstep (se 3 (by rfl) ⟨987278, by rfl⟩ : syracuseStep 5265485 = 1974557) B1974557
theorem B1038419 : Blo 1036608 1038419 := bstep (se 1 (by rfl) ⟨778814, by rfl⟩ : syracuseStep 1038419 = 1557629) B1557629
theorem B1169491 : Blo 1036608 1169491 := bstep (se 1 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 1169491 = 1754237) B1754237
theorem B1038435 : Blo 1036608 1038435 := bstep (se 1 (by rfl) ⟨778826, by rfl⟩ : syracuseStep 1038435 = 1557653) B1557653
theorem B2218097 : Blo 1036608 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B1038451 : Blo 1036608 1038451 := bstep (se 1 (by rfl) ⟨778838, by rfl⟩ : syracuseStep 1038451 = 1557677) B1557677
theorem B1038467 : Blo 1036608 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B1038483 : Blo 1036608 1038483 := bstep (se 1 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 1038483 = 1557725) B1557725
theorem B1038499 : Blo 1036608 1038499 := bstep (se 1 (by rfl) ⟨778874, by rfl⟩ : syracuseStep 1038499 = 1557749) B1557749
theorem B1038515 : Blo 1036608 1038515 := bstep (se 1 (by rfl) ⟨778886, by rfl⟩ : syracuseStep 1038515 = 1557773) B1557773
theorem B1038531 : Blo 1036608 1038531 := bstep (se 1 (by rfl) ⟨778898, by rfl⟩ : syracuseStep 1038531 = 1557797) B1557797
theorem B1038547 : Blo 1036608 1038547 := bstep (se 1 (by rfl) ⟨778910, by rfl⟩ : syracuseStep 1038547 = 1557821) B1557821
theorem B1038563 : Blo 1036608 1038563 := bstep (se 1 (by rfl) ⟨778922, by rfl⟩ : syracuseStep 1038563 = 1557845) B1557845
theorem B1169635 : Blo 1036608 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B11229425 : Blo 1036608 11229425 := bstep (se 2 (by rfl) ⟨4211034, by rfl⟩ : syracuseStep 11229425 = 8422069) B8422069
theorem B1038579 : Blo 1036608 1038579 := bstep (se 1 (by rfl) ⟨778934, by rfl⟩ : syracuseStep 1038579 = 1557869) B1557869
theorem B1038595 : Blo 1036608 1038595 := bstep (se 1 (by rfl) ⟨778946, by rfl⟩ : syracuseStep 1038595 = 1557893) B1557893
theorem B1038611 : Blo 1036608 1038611 := bstep (se 1 (by rfl) ⟨778958, by rfl⟩ : syracuseStep 1038611 = 1557917) B1557917
theorem B1038627 : Blo 1036608 1038627 := bstep (se 1 (by rfl) ⟨778970, by rfl⟩ : syracuseStep 1038627 = 1557941) B1557941
theorem B1038643 : Blo 1036608 1038643 := bstep (se 1 (by rfl) ⟨778982, by rfl⟩ : syracuseStep 1038643 = 1557965) B1557965
theorem B1038659 : Blo 1036608 1038659 := bstep (se 1 (by rfl) ⟨778994, by rfl⟩ : syracuseStep 1038659 = 1557989) B1557989
theorem B1038675 : Blo 1036608 1038675 := bstep (se 1 (by rfl) ⟨779006, by rfl⟩ : syracuseStep 1038675 = 1558013) B1558013
theorem B1038691 : Blo 1036608 1038691 := bstep (se 1 (by rfl) ⟨779018, by rfl⟩ : syracuseStep 1038691 = 1558037) B1558037
theorem B3332465 : Blo 1036608 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B1038707 : Blo 1036608 1038707 := bstep (se 1 (by rfl) ⟨779030, by rfl⟩ : syracuseStep 1038707 = 1558061) B1558061
theorem B1169779 : Blo 1036608 1169779 := bstep (se 1 (by rfl) ⟨877334, by rfl⟩ : syracuseStep 1169779 = 1754669) B1754669
theorem B1497475 : Blo 1036608 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B1038723 : Blo 1036608 1038723 := bstep (se 1 (by rfl) ⟨779042, by rfl⟩ : syracuseStep 1038723 = 1558085) B1558085
theorem B4741517 : Blo 1036608 4741517 := bstep (se 3 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 4741517 = 1778069) B1778069
theorem B1038739 : Blo 1036608 1038739 := bstep (se 1 (by rfl) ⟨779054, by rfl⟩ : syracuseStep 1038739 = 1558109) B1558109
theorem B1038755 : Blo 1036608 1038755 := bstep (se 1 (by rfl) ⟨779066, by rfl⟩ : syracuseStep 1038755 = 1558133) B1558133
theorem B1038771 : Blo 1036608 1038771 := bstep (se 1 (by rfl) ⟨779078, by rfl⟩ : syracuseStep 1038771 = 1558157) B1558157
theorem B1038787 : Blo 1036608 1038787 := bstep (se 1 (by rfl) ⟨779090, by rfl⟩ : syracuseStep 1038787 = 1558181) B1558181
theorem B1038803 : Blo 1036608 1038803 := bstep (se 1 (by rfl) ⟨779102, by rfl⟩ : syracuseStep 1038803 = 1558205) B1558205
theorem B1038819 : Blo 1036608 1038819 := bstep (se 1 (by rfl) ⟨779114, by rfl⟩ : syracuseStep 1038819 = 1558229) B1558229
theorem B1038835 : Blo 1036608 1038835 := bstep (se 1 (by rfl) ⟨779126, by rfl⟩ : syracuseStep 1038835 = 1558253) B1558253
theorem B2218499 : Blo 1036608 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B1038851 : Blo 1036608 1038851 := bstep (se 1 (by rfl) ⟨779138, by rfl⟩ : syracuseStep 1038851 = 1558277) B1558277
theorem B1169923 : Blo 1036608 1169923 := bstep (se 1 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 1169923 = 1754885) B1754885
theorem B1038867 : Blo 1036608 1038867 := bstep (se 1 (by rfl) ⟨779150, by rfl⟩ : syracuseStep 1038867 = 1558301) B1558301
theorem B1038883 : Blo 1036608 1038883 := bstep (se 1 (by rfl) ⟨779162, by rfl⟩ : syracuseStep 1038883 = 1558325) B1558325
theorem B1038899 : Blo 1036608 1038899 := bstep (se 1 (by rfl) ⟨779174, by rfl⟩ : syracuseStep 1038899 = 1558349) B1558349
theorem B1038915 : Blo 1036608 1038915 := bstep (se 1 (by rfl) ⟨779186, by rfl⟩ : syracuseStep 1038915 = 1558373) B1558373
theorem B1038931 : Blo 1036608 1038931 := bstep (se 1 (by rfl) ⟨779198, by rfl⟩ : syracuseStep 1038931 = 1558397) B1558397
theorem B1038947 : Blo 1036608 1038947 := bstep (se 1 (by rfl) ⟨779210, by rfl⟩ : syracuseStep 1038947 = 1558421) B1558421
theorem B1038963 : Blo 1036608 1038963 := bstep (se 1 (by rfl) ⟨779222, by rfl⟩ : syracuseStep 1038963 = 1558445) B1558445
theorem B1038979 : Blo 1036608 1038979 := bstep (se 1 (by rfl) ⟨779234, by rfl⟩ : syracuseStep 1038979 = 1558469) B1558469
theorem B1038995 : Blo 1036608 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B1170067 : Blo 1036608 1170067 := bstep (se 1 (by rfl) ⟨877550, by rfl⟩ : syracuseStep 1170067 = 1755101) B1755101
theorem B1039011 : Blo 1036608 1039011 := bstep (se 1 (by rfl) ⟨779258, by rfl⟩ : syracuseStep 1039011 = 1558517) B1558517
theorem B1039027 : Blo 1036608 1039027 := bstep (se 1 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 1039027 = 1558541) B1558541
theorem B1039043 : Blo 1036608 1039043 := bstep (se 1 (by rfl) ⟨779282, by rfl⟩ : syracuseStep 1039043 = 1558565) B1558565
theorem B1661651 : Blo 1036608 1661651 := bstep (se 1 (by rfl) ⟨1246238, by rfl⟩ : syracuseStep 1661651 = 2492477) B2492477
theorem B1039059 : Blo 1036608 1039059 := bstep (se 1 (by rfl) ⟨779294, by rfl⟩ : syracuseStep 1039059 = 1558589) B1558589
theorem B1039075 : Blo 1036608 1039075 := bstep (se 1 (by rfl) ⟨779306, by rfl⟩ : syracuseStep 1039075 = 1558613) B1558613
theorem B1039091 : Blo 1036608 1039091 := bstep (se 1 (by rfl) ⟨779318, by rfl⟩ : syracuseStep 1039091 = 1558637) B1558637
theorem B1039107 : Blo 1036608 1039107 := bstep (se 1 (by rfl) ⟨779330, by rfl⟩ : syracuseStep 1039107 = 1558661) B1558661
theorem B1039123 : Blo 1036608 1039123 := bstep (se 1 (by rfl) ⟨779342, by rfl⟩ : syracuseStep 1039123 = 1558685) B1558685
theorem B1039139 : Blo 1036608 1039139 := bstep (se 1 (by rfl) ⟨779354, by rfl⟩ : syracuseStep 1039139 = 1558709) B1558709
theorem B1170211 : Blo 1036608 1170211 := bstep (se 1 (by rfl) ⟨877658, by rfl⟩ : syracuseStep 1170211 = 1755317) B1755317
theorem B1039155 : Blo 1036608 1039155 := bstep (se 1 (by rfl) ⟨779366, by rfl⟩ : syracuseStep 1039155 = 1558733) B1558733
theorem B1039171 : Blo 1036608 1039171 := bstep (se 1 (by rfl) ⟨779378, by rfl⟩ : syracuseStep 1039171 = 1558757) B1558757
theorem B1039187 : Blo 1036608 1039187 := bstep (se 1 (by rfl) ⟨779390, by rfl⟩ : syracuseStep 1039187 = 1558781) B1558781
theorem B1039203 : Blo 1036608 1039203 := bstep (se 1 (by rfl) ⟨779402, by rfl⟩ : syracuseStep 1039203 = 1558805) B1558805
theorem B2808685 : Blo 1036608 2808685 := bstep (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) B1053257
theorem B1039219 : Blo 1036608 1039219 := bstep (se 1 (by rfl) ⟨779414, by rfl⟩ : syracuseStep 1039219 = 1558829) B1558829
theorem B1039235 : Blo 1036608 1039235 := bstep (se 1 (by rfl) ⟨779426, by rfl⟩ : syracuseStep 1039235 = 1558853) B1558853
theorem B1661843 : Blo 1036608 1661843 := bstep (se 1 (by rfl) ⟨1246382, by rfl⟩ : syracuseStep 1661843 = 2492765) B2492765
theorem B1039251 : Blo 1036608 1039251 := bstep (se 1 (by rfl) ⟨779438, by rfl⟩ : syracuseStep 1039251 = 1558877) B1558877
theorem B1039267 : Blo 1036608 1039267 := bstep (se 1 (by rfl) ⟨779450, by rfl⟩ : syracuseStep 1039267 = 1558901) B1558901
theorem B2808749 : Blo 1036608 2808749 := bstep (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) B1053281
theorem B1039283 : Blo 1036608 1039283 := bstep (se 1 (by rfl) ⟨779462, by rfl⟩ : syracuseStep 1039283 = 1558925) B1558925
theorem B1170355 : Blo 1036608 1170355 := bstep (se 1 (by rfl) ⟨877766, by rfl⟩ : syracuseStep 1170355 = 1755533) B1755533
theorem B1039299 : Blo 1036608 1039299 := bstep (se 1 (by rfl) ⟨779474, by rfl⟩ : syracuseStep 1039299 = 1558949) B1558949
theorem B1039315 : Blo 1036608 1039315 := bstep (se 1 (by rfl) ⟨779486, by rfl⟩ : syracuseStep 1039315 = 1558973) B1558973
theorem B1039331 : Blo 1036608 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B3333091 : Blo 1036608 3333091 := bstep (se 1 (by rfl) ⟨2499818, by rfl⟩ : syracuseStep 3333091 = 4999637) B4999637
theorem B1039347 : Blo 1036608 1039347 := bstep (se 1 (by rfl) ⟨779510, by rfl⟩ : syracuseStep 1039347 = 1559021) B1559021
theorem B1039363 : Blo 1036608 1039363 := bstep (se 1 (by rfl) ⟨779522, by rfl⟩ : syracuseStep 1039363 = 1559045) B1559045
theorem B1039379 : Blo 1036608 1039379 := bstep (se 1 (by rfl) ⟨779534, by rfl⟩ : syracuseStep 1039379 = 1559069) B1559069
theorem B1334291 : Blo 1036608 1334291 := bstep (se 1 (by rfl) ⟨1000718, by rfl⟩ : syracuseStep 1334291 = 2001437) B2001437
theorem B1039395 : Blo 1036608 1039395 := bstep (se 1 (by rfl) ⟨779546, by rfl⟩ : syracuseStep 1039395 = 1559093) B1559093
theorem B1039411 : Blo 1036608 1039411 := bstep (se 1 (by rfl) ⟨779558, by rfl⟩ : syracuseStep 1039411 = 1559117) B1559117
theorem B1039427 : Blo 1036608 1039427 := bstep (se 1 (by rfl) ⟨779570, by rfl⟩ : syracuseStep 1039427 = 1559141) B1559141
theorem B1170499 : Blo 1036608 1170499 := bstep (se 1 (by rfl) ⟨877874, by rfl⟩ : syracuseStep 1170499 = 1755749) B1755749
theorem B1039443 : Blo 1036608 1039443 := bstep (se 1 (by rfl) ⟨779582, by rfl⟩ : syracuseStep 1039443 = 1559165) B1559165
theorem B1039459 : Blo 1036608 1039459 := bstep (se 1 (by rfl) ⟨779594, by rfl⟩ : syracuseStep 1039459 = 1559189) B1559189
theorem B1039475 : Blo 1036608 1039475 := bstep (se 1 (by rfl) ⟨779606, by rfl⟩ : syracuseStep 1039475 = 1559213) B1559213
theorem B1039491 : Blo 1036608 1039491 := bstep (se 1 (by rfl) ⟨779618, by rfl⟩ : syracuseStep 1039491 = 1559237) B1559237
theorem B1039507 : Blo 1036608 1039507 := bstep (se 1 (by rfl) ⟨779630, by rfl⟩ : syracuseStep 1039507 = 1559261) B1559261
theorem B1039523 : Blo 1036608 1039523 := bstep (se 1 (by rfl) ⟨779642, by rfl⟩ : syracuseStep 1039523 = 1559285) B1559285
theorem B1039539 : Blo 1036608 1039539 := bstep (se 1 (by rfl) ⟨779654, by rfl⟩ : syracuseStep 1039539 = 1559309) B1559309
theorem B1039555 : Blo 1036608 1039555 := bstep (se 1 (by rfl) ⟨779666, by rfl⟩ : syracuseStep 1039555 = 1559333) B1559333
theorem B1039571 : Blo 1036608 1039571 := bstep (se 1 (by rfl) ⟨779678, by rfl⟩ : syracuseStep 1039571 = 1559357) B1559357
theorem B1170643 : Blo 1036608 1170643 := bstep (se 1 (by rfl) ⟨877982, by rfl⟩ : syracuseStep 1170643 = 1755965) B1755965
theorem B1039587 : Blo 1036608 1039587 := bstep (se 1 (by rfl) ⟨779690, by rfl⟩ : syracuseStep 1039587 = 1559381) B1559381
theorem B1039603 : Blo 1036608 1039603 := bstep (se 1 (by rfl) ⟨779702, by rfl⟩ : syracuseStep 1039603 = 1559405) B1559405
theorem B1039619 : Blo 1036608 1039619 := bstep (se 1 (by rfl) ⟨779714, by rfl⟩ : syracuseStep 1039619 = 1559429) B1559429
theorem B1039635 : Blo 1036608 1039635 := bstep (se 1 (by rfl) ⟨779726, by rfl⟩ : syracuseStep 1039635 = 1559453) B1559453
theorem B1039651 : Blo 1036608 1039651 := bstep (se 1 (by rfl) ⟨779738, by rfl⟩ : syracuseStep 1039651 = 1559477) B1559477
theorem B1039667 : Blo 1036608 1039667 := bstep (se 1 (by rfl) ⟨779750, by rfl⟩ : syracuseStep 1039667 = 1559501) B1559501
theorem B1039683 : Blo 1036608 1039683 := bstep (se 1 (by rfl) ⟨779762, by rfl⟩ : syracuseStep 1039683 = 1559525) B1559525
theorem B1039699 : Blo 1036608 1039699 := bstep (se 1 (by rfl) ⟨779774, by rfl⟩ : syracuseStep 1039699 = 1559549) B1559549
theorem B1039715 : Blo 1036608 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B1039731 : Blo 1036608 1039731 := bstep (se 1 (by rfl) ⟨779798, by rfl⟩ : syracuseStep 1039731 = 1559597) B1559597
theorem B2219395 : Blo 1036608 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B1039747 : Blo 1036608 1039747 := bstep (se 1 (by rfl) ⟨779810, by rfl⟩ : syracuseStep 1039747 = 1559621) B1559621
theorem B1039763 : Blo 1036608 1039763 := bstep (se 1 (by rfl) ⟨779822, by rfl⟩ : syracuseStep 1039763 = 1559645) B1559645
theorem B1039779 : Blo 1036608 1039779 := bstep (se 1 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 1039779 = 1559669) B1559669
theorem B1039795 : Blo 1036608 1039795 := bstep (se 1 (by rfl) ⟨779846, by rfl⟩ : syracuseStep 1039795 = 1559693) B1559693
theorem B1039811 : Blo 1036608 1039811 := bstep (se 1 (by rfl) ⟨779858, by rfl⟩ : syracuseStep 1039811 = 1559717) B1559717
theorem B1039827 : Blo 1036608 1039827 := bstep (se 1 (by rfl) ⟨779870, by rfl⟩ : syracuseStep 1039827 = 1559741) B1559741
theorem B1039843 : Blo 1036608 1039843 := bstep (se 1 (by rfl) ⟨779882, by rfl⟩ : syracuseStep 1039843 = 1559765) B1559765
theorem B1039859 : Blo 1036608 1039859 := bstep (se 1 (by rfl) ⟨779894, by rfl⟩ : syracuseStep 1039859 = 1559789) B1559789
theorem B1039875 : Blo 1036608 1039875 := bstep (se 1 (by rfl) ⟨779906, by rfl⟩ : syracuseStep 1039875 = 1559813) B1559813
theorem B7200269 : Blo 1036608 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B1039891 : Blo 1036608 1039891 := bstep (se 1 (by rfl) ⟨779918, by rfl⟩ : syracuseStep 1039891 = 1559837) B1559837
theorem B1039907 : Blo 1036608 1039907 := bstep (se 1 (by rfl) ⟨779930, by rfl⟩ : syracuseStep 1039907 = 1559861) B1559861
theorem B1039923 : Blo 1036608 1039923 := bstep (se 1 (by rfl) ⟨779942, by rfl⟩ : syracuseStep 1039923 = 1559885) B1559885
theorem B1039939 : Blo 1036608 1039939 := bstep (se 1 (by rfl) ⟨779954, by rfl⟩ : syracuseStep 1039939 = 1559909) B1559909
theorem B1039955 : Blo 1036608 1039955 := bstep (se 1 (by rfl) ⟨779966, by rfl⟩ : syracuseStep 1039955 = 1559933) B1559933
theorem B1039971 : Blo 1036608 1039971 := bstep (se 1 (by rfl) ⟨779978, by rfl⟩ : syracuseStep 1039971 = 1559957) B1559957
theorem B1039987 : Blo 1036608 1039987 := bstep (se 1 (by rfl) ⟨779990, by rfl⟩ : syracuseStep 1039987 = 1559981) B1559981
theorem B1040003 : Blo 1036608 1040003 := bstep (se 1 (by rfl) ⟨780002, by rfl⟩ : syracuseStep 1040003 = 1560005) B1560005
theorem B8871565 : Blo 1036608 8871565 := bstep (se 3 (by rfl) ⟨1663418, by rfl⟩ : syracuseStep 8871565 = 3326837) B3326837
theorem B1040019 : Blo 1036608 1040019 := bstep (se 1 (by rfl) ⟨780014, by rfl⟩ : syracuseStep 1040019 = 1560029) B1560029
theorem B4742819 : Blo 1036608 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B1040035 : Blo 1036608 1040035 := bstep (se 1 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 1040035 = 1560053) B1560053
theorem B1040051 : Blo 1036608 1040051 := bstep (se 1 (by rfl) ⟨780038, by rfl⟩ : syracuseStep 1040051 = 1560077) B1560077
theorem B1040067 : Blo 1036608 1040067 := bstep (se 1 (by rfl) ⟨780050, by rfl⟩ : syracuseStep 1040067 = 1560101) B1560101
theorem B1040083 : Blo 1036608 1040083 := bstep (se 1 (by rfl) ⟨780062, by rfl⟩ : syracuseStep 1040083 = 1560125) B1560125
theorem B1040099 : Blo 1036608 1040099 := bstep (se 1 (by rfl) ⟨780074, by rfl⟩ : syracuseStep 1040099 = 1560149) B1560149
theorem B1040115 : Blo 1036608 1040115 := bstep (se 1 (by rfl) ⟨780086, by rfl⟩ : syracuseStep 1040115 = 1560173) B1560173
theorem B1040131 : Blo 1036608 1040131 := bstep (se 1 (by rfl) ⟨780098, by rfl⟩ : syracuseStep 1040131 = 1560197) B1560197
theorem B1040147 : Blo 1036608 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B1040163 : Blo 1036608 1040163 := bstep (se 1 (by rfl) ⟨780122, by rfl⟩ : syracuseStep 1040163 = 1560245) B1560245
theorem B1040179 : Blo 1036608 1040179 := bstep (se 1 (by rfl) ⟨780134, by rfl⟩ : syracuseStep 1040179 = 1560269) B1560269
theorem B1040195 : Blo 1036608 1040195 := bstep (se 1 (by rfl) ⟨780146, by rfl⟩ : syracuseStep 1040195 = 1560293) B1560293
theorem B1040211 : Blo 1036608 1040211 := bstep (se 1 (by rfl) ⟨780158, by rfl⟩ : syracuseStep 1040211 = 1560317) B1560317
theorem B1040227 : Blo 1036608 1040227 := bstep (se 1 (by rfl) ⟨780170, by rfl⟩ : syracuseStep 1040227 = 1560341) B1560341
theorem B1040243 : Blo 1036608 1040243 := bstep (se 1 (by rfl) ⟨780182, by rfl⟩ : syracuseStep 1040243 = 1560365) B1560365
theorem B1040259 : Blo 1036608 1040259 := bstep (se 1 (by rfl) ⟨780194, by rfl⟩ : syracuseStep 1040259 = 1560389) B1560389
theorem B2809745 : Blo 1036608 2809745 := bstep (se 2 (by rfl) ⟨1053654, by rfl⟩ : syracuseStep 2809745 = 2107309) B2107309
theorem B1040275 : Blo 1036608 1040275 := bstep (se 1 (by rfl) ⟨780206, by rfl⟩ : syracuseStep 1040275 = 1560413) B1560413
theorem B1040291 : Blo 1036608 1040291 := bstep (se 1 (by rfl) ⟨780218, by rfl⟩ : syracuseStep 1040291 = 1560437) B1560437
theorem B1040307 : Blo 1036608 1040307 := bstep (se 1 (by rfl) ⟨780230, by rfl⟩ : syracuseStep 1040307 = 1560461) B1560461
theorem B1040323 : Blo 1036608 1040323 := bstep (se 1 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 1040323 = 1560485) B1560485
theorem B1040339 : Blo 1036608 1040339 := bstep (se 1 (by rfl) ⟨780254, by rfl⟩ : syracuseStep 1040339 = 1560509) B1560509
theorem B19947491 : Blo 1036608 19947491 := bstep (se 1 (by rfl) ⟨14960618, by rfl⟩ : syracuseStep 19947491 = 29921237) B29921237
theorem B1040355 : Blo 1036608 1040355 := bstep (se 1 (by rfl) ⟨780266, by rfl⟩ : syracuseStep 1040355 = 1560533) B1560533
theorem B1040371 : Blo 1036608 1040371 := bstep (se 1 (by rfl) ⟨780278, by rfl⟩ : syracuseStep 1040371 = 1560557) B1560557
theorem B1040387 : Blo 1036608 1040387 := bstep (se 1 (by rfl) ⟨780290, by rfl⟩ : syracuseStep 1040387 = 1560581) B1560581
theorem B1040403 : Blo 1036608 1040403 := bstep (se 1 (by rfl) ⟨780302, by rfl⟩ : syracuseStep 1040403 = 1560605) B1560605
theorem B1040419 : Blo 1036608 1040419 := bstep (se 1 (by rfl) ⟨780314, by rfl⟩ : syracuseStep 1040419 = 1560629) B1560629
theorem B1040435 : Blo 1036608 1040435 := bstep (se 1 (by rfl) ⟨780326, by rfl⟩ : syracuseStep 1040435 = 1560653) B1560653
theorem B1040451 : Blo 1036608 1040451 := bstep (se 1 (by rfl) ⟨780338, by rfl⟩ : syracuseStep 1040451 = 1560677) B1560677
theorem B1040467 : Blo 1036608 1040467 := bstep (se 1 (by rfl) ⟨780350, by rfl⟩ : syracuseStep 1040467 = 1560701) B1560701
theorem B1040483 : Blo 1036608 1040483 := bstep (se 1 (by rfl) ⟨780362, by rfl⟩ : syracuseStep 1040483 = 1560725) B1560725
theorem B1040499 : Blo 1036608 1040499 := bstep (se 1 (by rfl) ⟨780374, by rfl⟩ : syracuseStep 1040499 = 1560749) B1560749
theorem B1040515 : Blo 1036608 1040515 := bstep (se 1 (by rfl) ⟨780386, by rfl⟩ : syracuseStep 1040515 = 1560773) B1560773
theorem B1040531 : Blo 1036608 1040531 := bstep (se 1 (by rfl) ⟨780398, by rfl⟩ : syracuseStep 1040531 = 1560797) B1560797
theorem B1040547 : Blo 1036608 1040547 := bstep (se 1 (by rfl) ⟨780410, by rfl⟩ : syracuseStep 1040547 = 1560821) B1560821
theorem B1040563 : Blo 1036608 1040563 := bstep (se 1 (by rfl) ⟨780422, by rfl⟩ : syracuseStep 1040563 = 1560845) B1560845
theorem B1040579 : Blo 1036608 1040579 := bstep (se 1 (by rfl) ⟨780434, by rfl⟩ : syracuseStep 1040579 = 1560869) B1560869
theorem B1040595 : Blo 1036608 1040595 := bstep (se 1 (by rfl) ⟨780446, by rfl⟩ : syracuseStep 1040595 = 1560893) B1560893
theorem B1663265 : Blo 1036608 1663265 := bstep (se 2 (by rfl) ⟨623724, by rfl⟩ : syracuseStep 1663265 = 1247449) B1247449
theorem B2220625 : Blo 1036608 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B3498605 : Blo 1036608 3498605 := bstep (se 3 (by rfl) ⟨655988, by rfl⟩ : syracuseStep 3498605 = 1311977) B1311977
theorem B11231885 : Blo 1036608 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B3498659 : Blo 1036608 3498659 := bstep (se 1 (by rfl) ⟨2623994, by rfl⟩ : syracuseStep 3498659 = 5247989) B5247989
theorem B1499969 : Blo 1036608 1499969 := bstep (se 2 (by rfl) ⟨562488, by rfl⟩ : syracuseStep 1499969 = 1124977) B1124977
theorem B3498929 : Blo 1036608 3498929 := bstep (se 2 (by rfl) ⟨1312098, by rfl⟩ : syracuseStep 3498929 = 2624197) B2624197
theorem B8872901 : Blo 1036608 8872901 := bstep (se 4 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 8872901 = 1663669) B1663669
theorem B11232227 : Blo 1036608 11232227 := bstep (se 1 (by rfl) ⟨8424170, by rfl⟩ : syracuseStep 11232227 = 16848341) B16848341
theorem B1107203 : Blo 1036608 1107203 := bstep (se 1 (by rfl) ⟨830402, by rfl⟩ : syracuseStep 1107203 = 1660805) B1660805
theorem B3499469 : Blo 1036608 3499469 := bstep (se 3 (by rfl) ⟨656150, by rfl⟩ : syracuseStep 3499469 = 1312301) B1312301
theorem B1402337 : Blo 1036608 1402337 := bstep (se 2 (by rfl) ⟨525876, by rfl⟩ : syracuseStep 1402337 = 1051753) B1051753
theorem B3499523 : Blo 1036608 3499523 := bstep (se 1 (by rfl) ⟨2624642, by rfl⟩ : syracuseStep 3499523 = 5249285) B5249285
theorem B3499793 : Blo 1036608 3499793 := bstep (se 2 (by rfl) ⟨1312422, by rfl⟩ : syracuseStep 3499793 = 2624845) B2624845
theorem B1664803 : Blo 1036608 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B1664849 : Blo 1036608 1664849 := bstep (se 2 (by rfl) ⟨624318, by rfl⟩ : syracuseStep 1664849 = 1248637) B1248637
theorem B1107955 : Blo 1036608 1107955 := bstep (se 1 (by rfl) ⟨830966, by rfl⟩ : syracuseStep 1107955 = 1661933) B1661933
theorem B2222129 : Blo 1036608 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B2222147 : Blo 1036608 2222147 := bstep (se 1 (by rfl) ⟨1666610, by rfl⟩ : syracuseStep 2222147 = 3333221) B3333221
theorem B3500333 : Blo 1036608 3500333 := bstep (se 3 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 3500333 = 1312625) B1312625
theorem B3500387 : Blo 1036608 3500387 := bstep (se 1 (by rfl) ⟨2625290, by rfl⟩ : syracuseStep 3500387 = 5250581) B5250581
theorem B3500657 : Blo 1036608 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B6646499 : Blo 1036608 6646499 := bstep (se 1 (by rfl) ⟨4984874, by rfl⟩ : syracuseStep 6646499 = 9969749) B9969749
theorem B1665841 : Blo 1036608 1665841 := bstep (se 2 (by rfl) ⟨624690, by rfl⟩ : syracuseStep 1665841 = 1249381) B1249381
theorem B3501197 : Blo 1036608 3501197 := bstep (se 3 (by rfl) ⟨656474, by rfl⟩ : syracuseStep 3501197 = 1312949) B1312949
theorem B28404877 : Blo 1036608 28404877 := bstep (se 3 (by rfl) ⟨5325914, by rfl⟩ : syracuseStep 28404877 = 10651829) B10651829
theorem B6646961 : Blo 1036608 6646961 := bstep (se 2 (by rfl) ⟨2492610, by rfl⟩ : syracuseStep 6646961 = 4985221) B4985221
theorem B3501251 : Blo 1036608 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B1109219 : Blo 1036608 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B1666289 : Blo 1036608 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B3501521 : Blo 1036608 3501521 := bstep (se 2 (by rfl) ⟨1313070, by rfl⟩ : syracuseStep 3501521 = 2626141) B2626141
theorem B5926405 : Blo 1036608 5926405 := bstep (se 4 (by rfl) ⟨555600, by rfl⟩ : syracuseStep 5926405 = 1111201) B1111201
theorem B1109971 : Blo 1036608 1109971 := bstep (se 1 (by rfl) ⟨832478, by rfl⟩ : syracuseStep 1109971 = 1664957) B1664957
theorem B3502061 : Blo 1036608 3502061 := bstep (se 3 (by rfl) ⟨656636, by rfl⟩ : syracuseStep 3502061 = 1313273) B1313273
theorem B3502115 : Blo 1036608 3502115 := bstep (se 1 (by rfl) ⟨2626586, by rfl⟩ : syracuseStep 3502115 = 5253173) B5253173
theorem B17985763 : Blo 1036608 17985763 := bstep (se 1 (by rfl) ⟨13489322, by rfl⟩ : syracuseStep 17985763 = 26978645) B26978645
theorem B3207395 : Blo 1036608 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B3502385 : Blo 1036608 3502385 := bstep (se 2 (by rfl) ⟨1313394, by rfl⟩ : syracuseStep 3502385 = 2626789) B2626789
theorem B1405283 : Blo 1036608 1405283 := bstep (se 1 (by rfl) ⟨1053962, by rfl⟩ : syracuseStep 1405283 = 2107925) B2107925
theorem B3502925 : Blo 1036608 3502925 := bstep (se 3 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 3502925 = 1313597) B1313597
theorem B3502979 : Blo 1036608 3502979 := bstep (se 1 (by rfl) ⟨2627234, by rfl⟩ : syracuseStep 3502979 = 5254469) B5254469
theorem B1110979 : Blo 1036608 1110979 := bstep (se 1 (by rfl) ⟨833234, by rfl⟩ : syracuseStep 1110979 = 1666469) B1666469
theorem B3503249 : Blo 1036608 3503249 := bstep (se 2 (by rfl) ⟨1313718, by rfl⟩ : syracuseStep 3503249 = 2627437) B2627437
theorem B7108229 : Blo 1036608 7108229 := bstep (se 4 (by rfl) ⟨666396, by rfl⟩ : syracuseStep 7108229 = 1332793) B1332793
theorem B3503789 : Blo 1036608 3503789 := bstep (se 3 (by rfl) ⟨656960, by rfl⟩ : syracuseStep 3503789 = 1313921) B1313921
theorem B3503843 : Blo 1036608 3503843 := bstep (se 1 (by rfl) ⟨2627882, by rfl⟩ : syracuseStep 3503843 = 5255765) B5255765
theorem B14219077 : Blo 1036608 14219077 := bstep (se 4 (by rfl) ⟨1333038, by rfl⟩ : syracuseStep 14219077 = 2666077) B2666077
theorem B10647395 : Blo 1036608 10647395 := bstep (se 1 (by rfl) ⟨7985546, by rfl⟩ : syracuseStep 10647395 = 15971093) B15971093
theorem B8877923 : Blo 1036608 8877923 := bstep (se 1 (by rfl) ⟨6658442, by rfl⟩ : syracuseStep 8877923 = 13316885) B13316885
theorem B3504113 : Blo 1036608 3504113 := bstep (se 2 (by rfl) ⟨1314042, by rfl⟩ : syracuseStep 3504113 = 2628085) B2628085
theorem B3504653 : Blo 1036608 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B3504707 : Blo 1036608 3504707 := bstep (se 1 (by rfl) ⟨2628530, by rfl⟩ : syracuseStep 3504707 = 5257061) B5257061
theorem B3373841 : Blo 1036608 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B3504977 : Blo 1036608 3504977 := bstep (se 2 (by rfl) ⟨1314366, by rfl⟩ : syracuseStep 3504977 = 2628733) B2628733
theorem B2849869 : Blo 1036608 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B3505517 : Blo 1036608 3505517 := bstep (se 3 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 3505517 = 1314569) B1314569
theorem B3505571 : Blo 1036608 3505571 := bstep (se 1 (by rfl) ⟨2629178, by rfl⟩ : syracuseStep 3505571 = 5258357) B5258357
theorem B53935669 : Blo 1036608 53935669 := bstep (se 5 (by rfl) ⟨2528234, by rfl⟩ : syracuseStep 53935669 = 5056469) B5056469
theorem B3505841 : Blo 1036608 3505841 := bstep (se 2 (by rfl) ⟨1314690, by rfl⟩ : syracuseStep 3505841 = 2629381) B2629381
theorem B2850659 : Blo 1036608 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B3506327 : Blo 1036608 3506327 := bstep (se 1 (by rfl) ⟨2629745, by rfl⟩ : syracuseStep 3506327 = 5259491) B5259491
theorem B2490689 : Blo 1036608 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B8553053 : Blo 1036608 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B3506867 : Blo 1036608 3506867 := bstep (se 1 (by rfl) ⟨2630150, by rfl⟩ : syracuseStep 3506867 = 5260301) B5260301
theorem B1802969 : Blo 1036608 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B3507137 : Blo 1036608 3507137 := bstep (se 2 (by rfl) ⟨1315176, by rfl⟩ : syracuseStep 3507137 = 2630353) B2630353
theorem B3376307 : Blo 1036608 3376307 := bstep (se 1 (by rfl) ⟨2532230, by rfl⟩ : syracuseStep 3376307 = 5064461) B5064461
theorem B1246411 : Blo 1036608 1246411 := bstep (se 1 (by rfl) ⟨934808, by rfl⟩ : syracuseStep 1246411 = 1869617) B1869617
theorem B4982147 : Blo 1036608 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B1312139 : Blo 1036608 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B3507677 : Blo 1036608 3507677 := bstep (se 3 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 3507677 = 1315379) B1315379
theorem B1246795 : Blo 1036608 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B1312843 : Blo 1036608 1312843 := bstep (se 1 (by rfl) ⟨984632, by rfl⟩ : syracuseStep 1312843 = 1969265) B1969265
theorem B3999917 : Blo 1036608 3999917 := bstep (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) B1499969
theorem B1313111 : Blo 1036608 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B11831669 : Blo 1036608 11831669 := bstep (se 5 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 11831669 = 1109219) B1109219
theorem B3508811 : Blo 1036608 3508811 := bstep (se 1 (by rfl) ⟨2631608, by rfl⟩ : syracuseStep 3508811 = 5263217) B5263217
theorem B4262489 : Blo 1036608 4262489 := bstep (se 2 (by rfl) ⟨1598433, by rfl⟩ : syracuseStep 4262489 = 3196867) B3196867
theorem B29952605 : Blo 1036608 29952605 := bstep (se 3 (by rfl) ⟨5616113, by rfl⟩ : syracuseStep 29952605 = 11232227) B11232227
theorem B1968779 : Blo 1036608 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B2001559 : Blo 1036608 2001559 := bstep (se 1 (by rfl) ⟨1501169, by rfl⟩ : syracuseStep 2001559 = 3002339) B3002339
theorem B1477273 : Blo 1036608 1477273 := bstep (se 2 (by rfl) ⟨553977, by rfl⟩ : syracuseStep 1477273 = 1107955) B1107955
theorem B1477387 : Blo 1036608 1477387 := bstep (se 1 (by rfl) ⟨1108040, by rfl⟩ : syracuseStep 1477387 = 2216081) B2216081
theorem B1968961 : Blo 1036608 1968961 := bstep (se 2 (by rfl) ⟨738360, by rfl⟩ : syracuseStep 1968961 = 1476721) B1476721
theorem B3509081 : Blo 1036608 3509081 := bstep (se 2 (by rfl) ⟨1315905, by rfl⟩ : syracuseStep 3509081 = 2631811) B2631811
theorem B1248151 : Blo 1036608 1248151 := bstep (se 1 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 1248151 = 1872227) B1872227
theorem B1051627 : Blo 1036608 1051627 := bstep (se 1 (by rfl) ⟨788720, by rfl⟩ : syracuseStep 1051627 = 1577441) B1577441
theorem B1313815 : Blo 1036608 1313815 := bstep (se 1 (by rfl) ⟨985361, by rfl⟩ : syracuseStep 1313815 = 1970723) B1970723
theorem B2624663 : Blo 1036608 2624663 := bstep (se 1 (by rfl) ⟨1968497, by rfl⟩ : syracuseStep 2624663 = 3936995) B3936995
theorem B1969409 : Blo 1036608 1969409 := bstep (se 2 (by rfl) ⟨738528, by rfl⟩ : syracuseStep 1969409 = 1477057) B1477057
theorem B2952541 : Blo 1036608 2952541 := bstep (se 3 (by rfl) ⟨553601, by rfl⟩ : syracuseStep 2952541 = 1107203) B1107203
theorem B3509783 : Blo 1036608 3509783 := bstep (se 1 (by rfl) ⟨2632337, by rfl⟩ : syracuseStep 3509783 = 5264675) B5264675
theorem B2952769 : Blo 1036608 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B1969751 : Blo 1036608 1969751 := bstep (se 1 (by rfl) ⟨1477313, by rfl⟩ : syracuseStep 1969751 = 2954627) B2954627
theorem B1216183 : Blo 1036608 1216183 := bstep (se 1 (by rfl) ⟨912137, by rfl⟩ : syracuseStep 1216183 = 1824275) B1824275
theorem B3936023 : Blo 1036608 3936023 := bstep (se 1 (by rfl) ⟨2952017, by rfl⟩ : syracuseStep 3936023 = 5904035) B5904035
theorem B2625331 : Blo 1036608 2625331 := bstep (se 1 (by rfl) ⟨1968998, by rfl⟩ : syracuseStep 2625331 = 3937997) B3937997
theorem B1052471 : Blo 1036608 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B2953111 : Blo 1036608 2953111 := bstep (se 1 (by rfl) ⟨2214833, by rfl⟩ : syracuseStep 2953111 = 4429667) B4429667
theorem B3739565 : Blo 1036608 3739565 := bstep (se 3 (by rfl) ⟨701168, by rfl⟩ : syracuseStep 3739565 = 1402337) B1402337
theorem B2625473 : Blo 1036608 2625473 := bstep (se 2 (by rfl) ⟨984552, by rfl⟩ : syracuseStep 2625473 = 1969105) B1969105
theorem B3936221 : Blo 1036608 3936221 := bstep (se 3 (by rfl) ⟨738041, by rfl⟩ : syracuseStep 3936221 = 1476083) B1476083
theorem B3510323 : Blo 1036608 3510323 := bstep (se 1 (by rfl) ⟨2632742, by rfl⟩ : syracuseStep 3510323 = 5265485) B5265485
theorem B1478731 : Blo 1036608 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B8982629 : Blo 1036608 8982629 := bstep (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) B1684243
theorem B2494667 : Blo 1036608 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B1970419 : Blo 1036608 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B3510593 : Blo 1036608 3510593 := bstep (se 2 (by rfl) ⟨1316472, by rfl⟩ : syracuseStep 3510593 = 2632945) B2632945
theorem B1478999 : Blo 1036608 1478999 := bstep (se 1 (by rfl) ⟨1109249, by rfl⟩ : syracuseStep 1478999 = 2218499) B2218499
theorem B1577369 : Blo 1036608 1577369 := bstep (se 2 (by rfl) ⟨591513, by rfl⟩ : syracuseStep 1577369 = 1183027) B1183027
theorem B1184171 : Blo 1036608 1184171 := bstep (se 1 (by rfl) ⟨888128, by rfl⟩ : syracuseStep 1184171 = 1776257) B1776257
theorem B2494937 : Blo 1036608 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B14979653 : Blo 1036608 14979653 := bstep (se 4 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 14979653 = 2808685) B2808685
theorem B1249867 : Blo 1036608 1249867 := bstep (se 1 (by rfl) ⟨937400, by rfl⟩ : syracuseStep 1249867 = 1874801) B1874801
theorem B2953817 : Blo 1036608 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B7901873 : Blo 1036608 7901873 := bstep (se 2 (by rfl) ⟨2963202, by rfl⟩ : syracuseStep 7901873 = 5926405) B5926405
theorem B1970867 : Blo 1036608 1970867 := bstep (se 1 (by rfl) ⟨1478150, by rfl⟩ : syracuseStep 1970867 = 2956301) B2956301
theorem B1315531 : Blo 1036608 1315531 := bstep (se 1 (by rfl) ⟨986648, by rfl⟩ : syracuseStep 1315531 = 1973297) B1973297
theorem B1970905 : Blo 1036608 1970905 := bstep (se 2 (by rfl) ⟨739089, by rfl⟩ : syracuseStep 1970905 = 1478179) B1478179
theorem B1250059 : Blo 1036608 1250059 := bstep (se 1 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 1250059 = 1875089) B1875089
theorem B4002625 : Blo 1036608 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B3511133 : Blo 1036608 3511133 := bstep (se 3 (by rfl) ⟨658337, by rfl⟩ : syracuseStep 3511133 = 1316675) B1316675
theorem B1184887 : Blo 1036608 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B5248151 : Blo 1036608 5248151 := bstep (se 1 (by rfl) ⟨3936113, by rfl⟩ : syracuseStep 5248151 = 7872227) B7872227
theorem B1971353 : Blo 1036608 1971353 := bstep (se 2 (by rfl) ⟨739257, by rfl⟩ : syracuseStep 1971353 = 1478515) B1478515
theorem B2626739 : Blo 1036608 2626739 := bstep (se 1 (by rfl) ⟨1970054, by rfl⟩ : syracuseStep 2626739 = 3940109) B3940109
theorem B1873163 : Blo 1036608 1873163 := bstep (se 1 (by rfl) ⟨1404872, by rfl⟩ : syracuseStep 1873163 = 2809745) B2809745
theorem B1479961 : Blo 1036608 1479961 := bstep (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) B1109971
theorem B1316503 : Blo 1036608 1316503 := bstep (se 1 (by rfl) ⟨987377, by rfl⟩ : syracuseStep 1316503 = 1974755) B1974755
theorem B2102987 : Blo 1036608 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B2627275 : Blo 1036608 2627275 := bstep (se 1 (by rfl) ⟨1970456, by rfl⟩ : syracuseStep 2627275 = 3940913) B3940913
theorem B2332403 : Blo 1036608 2332403 := bstep (se 1 (by rfl) ⟨1749302, by rfl⟩ : syracuseStep 2332403 = 3498605) B3498605
theorem B2332439 : Blo 1036608 2332439 := bstep (se 1 (by rfl) ⟨1749329, by rfl⟩ : syracuseStep 2332439 = 3498659) B3498659
theorem B2627417 : Blo 1036608 2627417 := bstep (se 2 (by rfl) ⟨985281, by rfl⟩ : syracuseStep 2627417 = 1970563) B1970563
theorem B1972097 : Blo 1036608 1972097 := bstep (se 2 (by rfl) ⟨739536, by rfl⟩ : syracuseStep 1972097 = 1479073) B1479073
theorem B3938179 : Blo 1036608 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B2332619 : Blo 1036608 2332619 := bstep (se 1 (by rfl) ⟨1749464, by rfl⟩ : syracuseStep 2332619 = 3498929) B3498929
theorem B2332673 : Blo 1036608 2332673 := bstep (se 2 (by rfl) ⟨874752, by rfl⟩ : syracuseStep 2332673 = 1749505) B1749505
theorem B1972363 : Blo 1036608 1972363 := bstep (se 1 (by rfl) ⟨1479272, by rfl⟩ : syracuseStep 1972363 = 2958545) B2958545
theorem B5904535 : Blo 1036608 5904535 := bstep (se 1 (by rfl) ⟨4428401, by rfl⟩ : syracuseStep 5904535 = 8856803) B8856803
theorem B3938483 : Blo 1036608 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B2955457 : Blo 1036608 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B2332889 : Blo 1036608 2332889 := bstep (se 2 (by rfl) ⟨874833, by rfl⟩ : syracuseStep 2332889 = 1749667) B1749667
theorem B2332979 : Blo 1036608 2332979 := bstep (se 1 (by rfl) ⟨1749734, by rfl⟩ : syracuseStep 2332979 = 3499469) B3499469
theorem B2333015 : Blo 1036608 2333015 := bstep (se 1 (by rfl) ⟨1749761, by rfl⟩ : syracuseStep 2333015 = 3499523) B3499523
theorem B2333195 : Blo 1036608 2333195 := bstep (se 1 (by rfl) ⟨1749896, by rfl⟩ : syracuseStep 2333195 = 3499793) B3499793
theorem B2333249 : Blo 1036608 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B1972811 : Blo 1036608 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B2628247 : Blo 1036608 2628247 := bstep (se 1 (by rfl) ⟨1971185, by rfl⟩ : syracuseStep 2628247 = 3942371) B3942371
theorem B1481419 : Blo 1036608 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B1481431 : Blo 1036608 1481431 := bstep (se 1 (by rfl) ⟨1111073, by rfl⟩ : syracuseStep 1481431 = 2222147) B2222147
theorem B1972993 : Blo 1036608 1972993 := bstep (se 2 (by rfl) ⟨739872, by rfl⟩ : syracuseStep 1972993 = 1479745) B1479745
theorem B15964933 : Blo 1036608 15964933 := bstep (se 4 (by rfl) ⟨1496712, by rfl⟩ : syracuseStep 15964933 = 2993425) B2993425
theorem B2333465 : Blo 1036608 2333465 := bstep (se 2 (by rfl) ⟨875049, by rfl⟩ : syracuseStep 2333465 = 1750099) B1750099
theorem B3939137 : Blo 1036608 3939137 := bstep (se 2 (by rfl) ⟨1477176, by rfl⟩ : syracuseStep 3939137 = 2954353) B2954353
theorem B2333555 : Blo 1036608 2333555 := bstep (se 1 (by rfl) ⟨1750166, by rfl⟩ : syracuseStep 2333555 = 3500333) B3500333
theorem B2333591 : Blo 1036608 2333591 := bstep (se 1 (by rfl) ⟨1750193, by rfl⟩ : syracuseStep 2333591 = 3500387) B3500387
theorem B2333771 : Blo 1036608 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B2628683 : Blo 1036608 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1973335 : Blo 1036608 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B2333825 : Blo 1036608 2333825 := bstep (se 2 (by rfl) ⟨875184, by rfl⟩ : syracuseStep 2333825 = 1750369) B1750369
theorem B4430999 : Blo 1036608 4430999 := bstep (se 1 (by rfl) ⟨3323249, by rfl⟩ : syracuseStep 4430999 = 6646499) B6646499
theorem B1973555 : Blo 1036608 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B2334041 : Blo 1036608 2334041 := bstep (se 2 (by rfl) ⟨875265, by rfl⟩ : syracuseStep 2334041 = 1750531) B1750531
theorem B2334131 : Blo 1036608 2334131 := bstep (se 1 (by rfl) ⟨1750598, by rfl⟩ : syracuseStep 2334131 = 3501197) B3501197
theorem B2629057 : Blo 1036608 2629057 := bstep (se 2 (by rfl) ⟨985896, by rfl⟩ : syracuseStep 2629057 = 1971793) B1971793
theorem B4431307 : Blo 1036608 4431307 := bstep (se 1 (by rfl) ⟨3323480, by rfl⟩ : syracuseStep 4431307 = 6646961) B6646961
theorem B2334167 : Blo 1036608 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B13311449 : Blo 1036608 13311449 := bstep (se 2 (by rfl) ⟨4991793, by rfl⟩ : syracuseStep 13311449 = 9983587) B9983587
theorem B1580555 : Blo 1036608 1580555 := bstep (se 1 (by rfl) ⟨1185416, by rfl⟩ : syracuseStep 1580555 = 2370833) B2370833
theorem B1580567 : Blo 1036608 1580567 := bstep (se 1 (by rfl) ⟨1185425, by rfl⟩ : syracuseStep 1580567 = 2370851) B2370851
theorem B1973783 : Blo 1036608 1973783 := bstep (se 1 (by rfl) ⟨1480337, by rfl⟩ : syracuseStep 1973783 = 2960675) B2960675
theorem B2334347 : Blo 1036608 2334347 := bstep (se 1 (by rfl) ⟨1750760, by rfl⟩ : syracuseStep 2334347 = 3501521) B3501521
theorem B2334401 : Blo 1036608 2334401 := bstep (se 2 (by rfl) ⟨875400, by rfl⟩ : syracuseStep 2334401 = 1750801) B1750801
theorem B4431581 : Blo 1036608 4431581 := bstep (se 3 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 4431581 = 1661843) B1661843
theorem B1974041 : Blo 1036608 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B2334617 : Blo 1036608 2334617 := bstep (se 2 (by rfl) ⟨875481, by rfl⟩ : syracuseStep 2334617 = 1750963) B1750963
theorem B2334707 : Blo 1036608 2334707 := bstep (se 1 (by rfl) ⟨1751030, by rfl⟩ : syracuseStep 2334707 = 3502061) B3502061
theorem B2334743 : Blo 1036608 2334743 := bstep (se 1 (by rfl) ⟨1751057, by rfl⟩ : syracuseStep 2334743 = 3502115) B3502115
theorem B2629655 : Blo 1036608 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B3940397 : Blo 1036608 3940397 := bstep (se 3 (by rfl) ⟨738824, by rfl⟩ : syracuseStep 3940397 = 1477649) B1477649
theorem B14950469 : Blo 1036608 14950469 := bstep (se 4 (by rfl) ⟨1401606, by rfl⟩ : syracuseStep 14950469 = 2803213) B2803213
theorem B3940427 : Blo 1036608 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1712281 : Blo 1036608 1712281 := bstep (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) B1284211
theorem B1974451 : Blo 1036608 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B2334923 : Blo 1036608 2334923 := bstep (se 1 (by rfl) ⟨1751192, by rfl⟩ : syracuseStep 2334923 = 3502385) B3502385
theorem B2334977 : Blo 1036608 2334977 := bstep (se 2 (by rfl) ⟨875616, by rfl⟩ : syracuseStep 2334977 = 1751233) B1751233
theorem B3154199 : Blo 1036608 3154199 := bstep (se 1 (by rfl) ⟨2365649, by rfl⟩ : syracuseStep 3154199 = 4731299) B4731299
theorem B2335193 : Blo 1036608 2335193 := bstep (se 2 (by rfl) ⟨875697, by rfl⟩ : syracuseStep 2335193 = 1751395) B1751395
theorem B11248145 : Blo 1036608 11248145 := bstep (se 2 (by rfl) ⟨4218054, by rfl⟩ : syracuseStep 11248145 = 8436109) B8436109
theorem B2335283 : Blo 1036608 2335283 := bstep (se 1 (by rfl) ⟨1751462, by rfl⟩ : syracuseStep 2335283 = 3502925) B3502925
theorem B2335319 : Blo 1036608 2335319 := bstep (se 1 (by rfl) ⟨1751489, by rfl⟩ : syracuseStep 2335319 = 3502979) B3502979
theorem B5251715 : Blo 1036608 5251715 := bstep (se 1 (by rfl) ⟨3938786, by rfl⟩ : syracuseStep 5251715 = 7877573) B7877573
theorem B1974937 : Blo 1036608 1974937 := bstep (se 2 (by rfl) ⟨740601, by rfl⟩ : syracuseStep 1974937 = 1481203) B1481203
theorem B3941081 : Blo 1036608 3941081 := bstep (se 2 (by rfl) ⟨1477905, by rfl⟩ : syracuseStep 3941081 = 2955811) B2955811
theorem B2335499 : Blo 1036608 2335499 := bstep (se 1 (by rfl) ⟨1751624, by rfl⟩ : syracuseStep 2335499 = 3503249) B3503249
theorem B2335553 : Blo 1036608 2335553 := bstep (se 2 (by rfl) ⟨875832, by rfl⟩ : syracuseStep 2335553 = 1751665) B1751665
theorem B2630465 : Blo 1036608 2630465 := bstep (se 2 (by rfl) ⟨986424, by rfl⟩ : syracuseStep 2630465 = 1972849) B1972849
theorem B4432913 : Blo 1036608 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B3941399 : Blo 1036608 3941399 := bstep (se 1 (by rfl) ⟨2956049, by rfl⟩ : syracuseStep 3941399 = 5912099) B5912099
theorem B2335769 : Blo 1036608 2335769 := bstep (se 2 (by rfl) ⟨875913, by rfl⟩ : syracuseStep 2335769 = 1751827) B1751827
theorem B2335859 : Blo 1036608 2335859 := bstep (se 1 (by rfl) ⟨1751894, by rfl⟩ : syracuseStep 2335859 = 3503789) B3503789
theorem B2335895 : Blo 1036608 2335895 := bstep (se 1 (by rfl) ⟨1751921, by rfl⟩ : syracuseStep 2335895 = 3503843) B3503843
theorem B1975499 : Blo 1036608 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B2434355 : Blo 1036608 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B2336075 : Blo 1036608 2336075 := bstep (se 1 (by rfl) ⟨1752056, by rfl⟩ : syracuseStep 2336075 = 3504113) B3504113
theorem B2631001 : Blo 1036608 2631001 := bstep (se 2 (by rfl) ⟨986625, by rfl⟩ : syracuseStep 2631001 = 1973251) B1973251
theorem B1123691 : Blo 1036608 1123691 := bstep (se 1 (by rfl) ⟨842768, by rfl⟩ : syracuseStep 1123691 = 1685537) B1685537
theorem B2336129 : Blo 1036608 2336129 := bstep (se 2 (by rfl) ⟨876048, by rfl⟩ : syracuseStep 2336129 = 1752097) B1752097
theorem B3155393 : Blo 1036608 3155393 := bstep (se 2 (by rfl) ⟨1183272, by rfl⟩ : syracuseStep 3155393 = 2366545) B2366545
theorem B2336345 : Blo 1036608 2336345 := bstep (se 2 (by rfl) ⟨876129, by rfl⟩ : syracuseStep 2336345 = 1752259) B1752259
theorem B3942067 : Blo 1036608 3942067 := bstep (se 1 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 3942067 = 5913101) B5913101
theorem B2336435 : Blo 1036608 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B4990643 : Blo 1036608 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B2336471 : Blo 1036608 2336471 := bstep (se 1 (by rfl) ⟨1752353, by rfl⟩ : syracuseStep 2336471 = 3504707) B3504707
theorem B2107147 : Blo 1036608 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B2959193 : Blo 1036608 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B13313909 : Blo 1036608 13313909 := bstep (se 5 (by rfl) ⟨624089, by rfl⟩ : syracuseStep 13313909 = 1248179) B1248179
theorem B2336651 : Blo 1036608 2336651 := bstep (se 1 (by rfl) ⟨1752488, by rfl⟩ : syracuseStep 2336651 = 3504977) B3504977
theorem B4990871 : Blo 1036608 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B2336705 : Blo 1036608 2336705 := bstep (se 2 (by rfl) ⟨876264, by rfl⟩ : syracuseStep 2336705 = 1752529) B1752529
theorem B4204561 : Blo 1036608 4204561 := bstep (se 2 (by rfl) ⟨1576710, by rfl⟩ : syracuseStep 4204561 = 3153421) B3153421
theorem B2336921 : Blo 1036608 2336921 := bstep (se 2 (by rfl) ⟨876345, by rfl⟩ : syracuseStep 2336921 = 1752691) B1752691
theorem B2337011 : Blo 1036608 2337011 := bstep (se 1 (by rfl) ⟨1752758, by rfl⟩ : syracuseStep 2337011 = 3505517) B3505517
theorem B2337047 : Blo 1036608 2337047 := bstep (se 1 (by rfl) ⟨1752785, by rfl⟩ : syracuseStep 2337047 = 3505571) B3505571
theorem B3549491 : Blo 1036608 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B7481693 : Blo 1036608 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B2632115 : Blo 1036608 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B2337227 : Blo 1036608 2337227 := bstep (se 1 (by rfl) ⟨1752920, by rfl⟩ : syracuseStep 2337227 = 3505841) B3505841
theorem B2337281 : Blo 1036608 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B2337497 : Blo 1036608 2337497 := bstep (se 2 (by rfl) ⟨876561, by rfl⟩ : syracuseStep 2337497 = 1753123) B1753123
theorem B2632409 : Blo 1036608 2632409 := bstep (se 2 (by rfl) ⟨987153, by rfl⟩ : syracuseStep 2632409 = 1974307) B1974307
theorem B2337587 : Blo 1036608 2337587 := bstep (se 1 (by rfl) ⟨1753190, by rfl⟩ : syracuseStep 2337587 = 3506381) B3506381
theorem B8858443 : Blo 1036608 8858443 := bstep (se 1 (by rfl) ⟨6643832, by rfl⟩ : syracuseStep 8858443 = 13287665) B13287665
theorem B2337623 : Blo 1036608 2337623 := bstep (se 1 (by rfl) ⟨1753217, by rfl⟩ : syracuseStep 2337623 = 3506435) B3506435
theorem B6663005 : Blo 1036608 6663005 := bstep (se 3 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 6663005 = 2498627) B2498627
theorem B3943313 : Blo 1036608 3943313 := bstep (se 2 (by rfl) ⟨1478742, by rfl⟩ : syracuseStep 3943313 = 2957485) B2957485
theorem B1420249 : Blo 1036608 1420249 := bstep (se 2 (by rfl) ⟨532593, by rfl⟩ : syracuseStep 1420249 = 1065187) B1065187
theorem B2337803 : Blo 1036608 2337803 := bstep (se 1 (by rfl) ⟨1753352, by rfl⟩ : syracuseStep 2337803 = 3506705) B3506705
theorem B7875629 : Blo 1036608 7875629 := bstep (se 3 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 7875629 = 2953361) B2953361
theorem B2337857 : Blo 1036608 2337857 := bstep (se 2 (by rfl) ⟨876696, by rfl⟩ : syracuseStep 2337857 = 1753393) B1753393
theorem B2960459 : Blo 1036608 2960459 := bstep (se 1 (by rfl) ⟨2220344, by rfl⟩ : syracuseStep 2960459 = 4440689) B4440689
theorem B8858717 : Blo 1036608 8858717 := bstep (se 3 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 8858717 = 3322019) B3322019
theorem B3747019 : Blo 1036608 3747019 := bstep (se 1 (by rfl) ⟨2810264, by rfl⟩ : syracuseStep 3747019 = 5620529) B5620529
theorem B2338073 : Blo 1036608 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B2338163 : Blo 1036608 2338163 := bstep (se 1 (by rfl) ⟨1753622, by rfl⟩ : syracuseStep 2338163 = 3507245) B3507245
theorem B2338199 : Blo 1036608 2338199 := bstep (se 1 (by rfl) ⟨1753649, by rfl⟩ : syracuseStep 2338199 = 3507299) B3507299
theorem B4435373 : Blo 1036608 4435373 := bstep (se 3 (by rfl) ⟨831632, by rfl⟩ : syracuseStep 4435373 = 1663265) B1663265
theorem B3944011 : Blo 1036608 3944011 := bstep (se 1 (by rfl) ⟨2958008, by rfl⟩ : syracuseStep 3944011 = 5916017) B5916017
theorem B2338379 : Blo 1036608 2338379 := bstep (se 1 (by rfl) ⟨1753784, by rfl⟩ : syracuseStep 2338379 = 3507569) B3507569
theorem B3747421 : Blo 1036608 3747421 := bstep (se 3 (by rfl) ⟨702641, by rfl⟩ : syracuseStep 3747421 = 1405283) B1405283
theorem B2338433 : Blo 1036608 2338433 := bstep (se 2 (by rfl) ⟨876912, by rfl⟩ : syracuseStep 2338433 = 1753825) B1753825
theorem B2666201 : Blo 1036608 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B4435715 : Blo 1036608 4435715 := bstep (se 1 (by rfl) ⟨3326786, by rfl⟩ : syracuseStep 4435715 = 6653573) B6653573
theorem B2338649 : Blo 1036608 2338649 := bstep (se 2 (by rfl) ⟨876993, by rfl⟩ : syracuseStep 2338649 = 1753987) B1753987
theorem B3944285 : Blo 1036608 3944285 := bstep (se 3 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 3944285 = 1479107) B1479107
theorem B2338739 : Blo 1036608 2338739 := bstep (se 1 (by rfl) ⟨1754054, by rfl⟩ : syracuseStep 2338739 = 3508109) B3508109
theorem B3321803 : Blo 1036608 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B2338775 : Blo 1036608 2338775 := bstep (se 1 (by rfl) ⟨1754081, by rfl⟩ : syracuseStep 2338775 = 3508163) B3508163
theorem B7483427 : Blo 1036608 7483427 := bstep (se 1 (by rfl) ⟨5612570, by rfl⟩ : syracuseStep 7483427 = 11225141) B11225141
theorem B35926091 : Blo 1036608 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B2371699 : Blo 1036608 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B8859779 : Blo 1036608 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B2338955 : Blo 1036608 2338955 := bstep (se 1 (by rfl) ⟨1754216, by rfl⟩ : syracuseStep 2338955 = 3508433) B3508433
theorem B2339009 : Blo 1036608 2339009 := bstep (se 2 (by rfl) ⟨877128, by rfl⟩ : syracuseStep 2339009 = 1754257) B1754257
theorem B5255441 : Blo 1036608 5255441 := bstep (se 2 (by rfl) ⟨1970790, by rfl⟩ : syracuseStep 5255441 = 3941581) B3941581
theorem B1749323 : Blo 1036608 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B2339225 : Blo 1036608 2339225 := bstep (se 2 (by rfl) ⟨877209, by rfl⟩ : syracuseStep 2339225 = 1754419) B1754419
theorem B5255603 : Blo 1036608 5255603 := bstep (se 1 (by rfl) ⟨3941702, by rfl⟩ : syracuseStep 5255603 = 7883405) B7883405
theorem B1749451 : Blo 1036608 1749451 := bstep (se 1 (by rfl) ⟨1312088, by rfl⟩ : syracuseStep 1749451 = 2624177) B2624177
theorem B2339315 : Blo 1036608 2339315 := bstep (se 1 (by rfl) ⟨1754486, by rfl⟩ : syracuseStep 2339315 = 3508973) B3508973
theorem B3944983 : Blo 1036608 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B2339351 : Blo 1036608 2339351 := bstep (se 1 (by rfl) ⟨1754513, by rfl⟩ : syracuseStep 2339351 = 3509027) B3509027
theorem B1749593 : Blo 1036608 1749593 := bstep (se 2 (by rfl) ⟨656097, by rfl⟩ : syracuseStep 1749593 = 1312195) B1312195
theorem B2339531 : Blo 1036608 2339531 := bstep (se 1 (by rfl) ⟨1754648, by rfl⟩ : syracuseStep 2339531 = 3509297) B3509297
theorem B1749721 : Blo 1036608 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B2339585 : Blo 1036608 2339585 := bstep (se 2 (by rfl) ⟨877344, by rfl⟩ : syracuseStep 2339585 = 1754689) B1754689
theorem B2339801 : Blo 1036608 2339801 := bstep (se 2 (by rfl) ⟨877425, by rfl⟩ : syracuseStep 2339801 = 1754851) B1754851
theorem B8991749 : Blo 1036608 8991749 := bstep (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) B1685953
theorem B2339891 : Blo 1036608 2339891 := bstep (se 1 (by rfl) ⟨1754918, by rfl⟩ : syracuseStep 2339891 = 3509837) B3509837
theorem B2339927 : Blo 1036608 2339927 := bstep (se 1 (by rfl) ⟨1754945, by rfl⟩ : syracuseStep 2339927 = 3509891) B3509891
theorem B8434781 : Blo 1036608 8434781 := bstep (se 3 (by rfl) ⟨1581521, by rfl⟩ : syracuseStep 8434781 = 3163043) B3163043
theorem B2340107 : Blo 1036608 2340107 := bstep (se 1 (by rfl) ⟨1755080, by rfl⟩ : syracuseStep 2340107 = 3510161) B3510161
theorem B5911825 : Blo 1036608 5911825 := bstep (se 2 (by rfl) ⟨2216934, by rfl⟩ : syracuseStep 5911825 = 4433869) B4433869
theorem B1750295 : Blo 1036608 1750295 := bstep (se 1 (by rfl) ⟨1312721, by rfl⟩ : syracuseStep 1750295 = 2625443) B2625443
theorem B3945773 : Blo 1036608 3945773 := bstep (se 3 (by rfl) ⟨739832, by rfl⟩ : syracuseStep 3945773 = 1479665) B1479665
theorem B2340161 : Blo 1036608 2340161 := bstep (se 2 (by rfl) ⟨877560, by rfl⟩ : syracuseStep 2340161 = 1755121) B1755121
theorem B1750423 : Blo 1036608 1750423 := bstep (se 1 (by rfl) ⟨1312817, by rfl⟩ : syracuseStep 1750423 = 2625635) B2625635
theorem B4208051 : Blo 1036608 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B102282709 : Blo 1036608 102282709 := bstep (se 7 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 102282709 = 2397251) B2397251
theorem B2340377 : Blo 1036608 2340377 := bstep (se 2 (by rfl) ⟨877641, by rfl⟩ : syracuseStep 2340377 = 1755283) B1755283
theorem B3323443 : Blo 1036608 3323443 := bstep (se 1 (by rfl) ⟨2492582, by rfl⟩ : syracuseStep 3323443 = 4985165) B4985165
theorem B2340467 : Blo 1036608 2340467 := bstep (se 1 (by rfl) ⟨1755350, by rfl⟩ : syracuseStep 2340467 = 3510701) B3510701
theorem B2340503 : Blo 1036608 2340503 := bstep (se 1 (by rfl) ⟨1755377, by rfl⟩ : syracuseStep 2340503 = 3510755) B3510755
theorem B11843333 : Blo 1036608 11843333 := bstep (se 4 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 11843333 = 2220625) B2220625
theorem B2340683 : Blo 1036608 2340683 := bstep (se 1 (by rfl) ⟨1755512, by rfl⟩ : syracuseStep 2340683 = 3511025) B3511025
theorem B2340737 : Blo 1036608 2340737 := bstep (se 2 (by rfl) ⟨877776, by rfl⟩ : syracuseStep 2340737 = 1755553) B1755553
theorem B1751051 : Blo 1036608 1751051 := bstep (se 1 (by rfl) ⟨1313288, by rfl⟩ : syracuseStep 1751051 = 2626577) B2626577
theorem B4438091 : Blo 1036608 4438091 := bstep (se 1 (by rfl) ⟨3328568, by rfl⟩ : syracuseStep 4438091 = 6657137) B6657137
theorem B2340953 : Blo 1036608 2340953 := bstep (se 2 (by rfl) ⟨877857, by rfl⟩ : syracuseStep 2340953 = 1755715) B1755715
theorem B1751179 : Blo 1036608 1751179 := bstep (se 1 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 1751179 = 2626769) B2626769
theorem B2341043 : Blo 1036608 2341043 := bstep (se 1 (by rfl) ⟨1755782, by rfl⟩ : syracuseStep 2341043 = 3511565) B3511565
theorem B2341079 : Blo 1036608 2341079 := bstep (se 1 (by rfl) ⟨1755809, by rfl⟩ : syracuseStep 2341079 = 3511619) B3511619
theorem B1751321 : Blo 1036608 1751321 := bstep (se 2 (by rfl) ⟨656745, by rfl⟩ : syracuseStep 1751321 = 1313491) B1313491
theorem B5257547 : Blo 1036608 5257547 := bstep (se 1 (by rfl) ⟨3943160, by rfl⟩ : syracuseStep 5257547 = 7886321) B7886321
theorem B2341259 : Blo 1036608 2341259 := bstep (se 1 (by rfl) ⟨1755944, by rfl⟩ : syracuseStep 2341259 = 3511889) B3511889
theorem B1751449 : Blo 1036608 1751449 := bstep (se 2 (by rfl) ⟨656793, by rfl⟩ : syracuseStep 1751449 = 1313587) B1313587
theorem B2341313 : Blo 1036608 2341313 := bstep (se 2 (by rfl) ⟨877992, by rfl⟩ : syracuseStep 2341313 = 1755985) B1755985
theorem B3324377 : Blo 1036608 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B1555019 : Blo 1036608 1555019 := bstep (se 1 (by rfl) ⟨1166264, by rfl⟩ : syracuseStep 1555019 = 2332529) B2332529
theorem B1555031 : Blo 1036608 1555031 := bstep (se 1 (by rfl) ⟨1166273, by rfl⟩ : syracuseStep 1555031 = 2332547) B2332547
theorem B1555097 : Blo 1036608 1555097 := bstep (se 2 (by rfl) ⟨583161, by rfl⟩ : syracuseStep 1555097 = 1166323) B1166323
theorem B3947201 : Blo 1036608 3947201 := bstep (se 2 (by rfl) ⟨1480200, by rfl⟩ : syracuseStep 3947201 = 2960401) B2960401
theorem B1555211 : Blo 1036608 1555211 := bstep (se 1 (by rfl) ⟨1166408, by rfl⟩ : syracuseStep 1555211 = 2332817) B2332817
theorem B1555223 : Blo 1036608 1555223 := bstep (se 1 (by rfl) ⟨1166417, by rfl⟩ : syracuseStep 1555223 = 2332835) B2332835
theorem B7486283 : Blo 1036608 7486283 := bstep (se 1 (by rfl) ⟨5614712, by rfl⟩ : syracuseStep 7486283 = 11229425) B11229425
theorem B1555289 : Blo 1036608 1555289 := bstep (se 2 (by rfl) ⟨583233, by rfl⟩ : syracuseStep 1555289 = 1166467) B1166467
theorem B7879517 : Blo 1036608 7879517 := bstep (se 3 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 7879517 = 2954819) B2954819
theorem B3161011 : Blo 1036608 3161011 := bstep (se 1 (by rfl) ⟨2370758, by rfl⟩ : syracuseStep 3161011 = 4741517) B4741517
theorem B1555403 : Blo 1036608 1555403 := bstep (se 1 (by rfl) ⟨1166552, by rfl⟩ : syracuseStep 1555403 = 2333105) B2333105
theorem B1555415 : Blo 1036608 1555415 := bstep (se 1 (by rfl) ⟨1166561, by rfl⟩ : syracuseStep 1555415 = 2333123) B2333123
theorem B1752023 : Blo 1036608 1752023 := bstep (se 1 (by rfl) ⟨1314017, by rfl⟩ : syracuseStep 1752023 = 2628035) B2628035
theorem B4439063 : Blo 1036608 4439063 := bstep (se 1 (by rfl) ⟨3329297, by rfl⟩ : syracuseStep 4439063 = 6658595) B6658595
theorem B1555481 : Blo 1036608 1555481 := bstep (se 2 (by rfl) ⟨583305, by rfl⟩ : syracuseStep 1555481 = 1166611) B1166611
theorem B1752151 : Blo 1036608 1752151 := bstep (se 1 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 1752151 = 2628227) B2628227
theorem B1555595 : Blo 1036608 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B1555607 : Blo 1036608 1555607 := bstep (se 1 (by rfl) ⟨1166705, by rfl⟩ : syracuseStep 1555607 = 2333411) B2333411
theorem B3325121 : Blo 1036608 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B1555673 : Blo 1036608 1555673 := bstep (se 2 (by rfl) ⟨583377, by rfl⟩ : syracuseStep 1555673 = 1166755) B1166755
theorem B3554525 : Blo 1036608 3554525 := bstep (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) B1332947
theorem B12631301 : Blo 1036608 12631301 := bstep (se 4 (by rfl) ⟨1184184, by rfl⟩ : syracuseStep 12631301 = 2368369) B2368369
theorem B1555787 : Blo 1036608 1555787 := bstep (se 1 (by rfl) ⟨1166840, by rfl⟩ : syracuseStep 1555787 = 2333681) B2333681
theorem B1555799 : Blo 1036608 1555799 := bstep (se 1 (by rfl) ⟨1166849, by rfl⟩ : syracuseStep 1555799 = 2333699) B2333699
theorem B1555865 : Blo 1036608 1555865 := bstep (se 2 (by rfl) ⟨583449, by rfl⟩ : syracuseStep 1555865 = 1166899) B1166899
theorem B1555979 : Blo 1036608 1555979 := bstep (se 1 (by rfl) ⟨1166984, by rfl⟩ : syracuseStep 1555979 = 2333969) B2333969
theorem B1555991 : Blo 1036608 1555991 := bstep (se 1 (by rfl) ⟨1166993, by rfl⟩ : syracuseStep 1555991 = 2333987) B2333987
theorem B1556057 : Blo 1036608 1556057 := bstep (se 2 (by rfl) ⟨583521, by rfl⟩ : syracuseStep 1556057 = 1167043) B1167043
theorem B6307429 : Blo 1036608 6307429 := bstep (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) B1182643
theorem B4800179 : Blo 1036608 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B4439731 : Blo 1036608 4439731 := bstep (se 1 (by rfl) ⟨3329798, by rfl⟩ : syracuseStep 4439731 = 6659597) B6659597
theorem B1556171 : Blo 1036608 1556171 := bstep (se 1 (by rfl) ⟨1167128, by rfl⟩ : syracuseStep 1556171 = 2334257) B2334257
theorem B1752779 : Blo 1036608 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1556183 : Blo 1036608 1556183 := bstep (se 1 (by rfl) ⟨1167137, by rfl⟩ : syracuseStep 1556183 = 2334275) B2334275
theorem B3161879 : Blo 1036608 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B1556249 : Blo 1036608 1556249 := bstep (se 2 (by rfl) ⟨583593, by rfl⟩ : syracuseStep 1556249 = 1167187) B1167187
theorem B7094081 : Blo 1036608 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B1752907 : Blo 1036608 1752907 := bstep (se 1 (by rfl) ⟨1314680, by rfl⟩ : syracuseStep 1752907 = 2629361) B2629361
theorem B1556363 : Blo 1036608 1556363 := bstep (se 1 (by rfl) ⟨1167272, by rfl⟩ : syracuseStep 1556363 = 2334545) B2334545
theorem B1556375 : Blo 1036608 1556375 := bstep (se 1 (by rfl) ⟨1167281, by rfl⟩ : syracuseStep 1556375 = 2334563) B2334563
theorem B1556441 : Blo 1036608 1556441 := bstep (se 2 (by rfl) ⟨583665, by rfl⟩ : syracuseStep 1556441 = 1167331) B1167331
theorem B1753049 : Blo 1036608 1753049 := bstep (se 2 (by rfl) ⟨657393, by rfl⟩ : syracuseStep 1753049 = 1314787) B1314787
theorem B3326017 : Blo 1036608 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B5259329 : Blo 1036608 5259329 := bstep (se 2 (by rfl) ⟨1972248, by rfl⟩ : syracuseStep 5259329 = 3944497) B3944497
theorem B1556555 : Blo 1036608 1556555 := bstep (se 1 (by rfl) ⟨1167416, by rfl⟩ : syracuseStep 1556555 = 2334833) B2334833
theorem B1556567 : Blo 1036608 1556567 := bstep (se 1 (by rfl) ⟨1167425, by rfl⟩ : syracuseStep 1556567 = 2334851) B2334851
theorem B1753177 : Blo 1036608 1753177 := bstep (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) B1314883
theorem B3948689 : Blo 1036608 3948689 := bstep (se 2 (by rfl) ⟨1480758, by rfl⟩ : syracuseStep 3948689 = 2961517) B2961517
theorem B1556633 : Blo 1036608 1556633 := bstep (se 2 (by rfl) ⟨583737, by rfl⟩ : syracuseStep 1556633 = 1167475) B1167475
theorem B1556747 : Blo 1036608 1556747 := bstep (se 1 (by rfl) ⟨1167560, by rfl⟩ : syracuseStep 1556747 = 2335121) B2335121
theorem B1556759 : Blo 1036608 1556759 := bstep (se 1 (by rfl) ⟨1167569, by rfl⟩ : syracuseStep 1556759 = 2335139) B2335139
theorem B1556825 : Blo 1036608 1556825 := bstep (se 2 (by rfl) ⟨583809, by rfl⟩ : syracuseStep 1556825 = 1167619) B1167619
theorem B7487923 : Blo 1036608 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B1556939 : Blo 1036608 1556939 := bstep (se 1 (by rfl) ⟨1167704, by rfl⟩ : syracuseStep 1556939 = 2335409) B2335409
theorem B1556951 : Blo 1036608 1556951 := bstep (se 1 (by rfl) ⟨1167713, by rfl⟩ : syracuseStep 1556951 = 2335427) B2335427
theorem B1557017 : Blo 1036608 1557017 := bstep (se 2 (by rfl) ⟨583881, by rfl⟩ : syracuseStep 1557017 = 1167763) B1167763
theorem B3949145 : Blo 1036608 3949145 := bstep (se 2 (by rfl) ⟨1480929, by rfl⟩ : syracuseStep 3949145 = 2961859) B2961859
theorem B48611933 : Blo 1036608 48611933 := bstep (se 3 (by rfl) ⟨9114737, by rfl⟩ : syracuseStep 48611933 = 18229475) B18229475
theorem B5915267 : Blo 1036608 5915267 := bstep (se 1 (by rfl) ⟨4436450, by rfl⟩ : syracuseStep 5915267 = 8872901) B8872901
theorem B1557131 : Blo 1036608 1557131 := bstep (se 1 (by rfl) ⟨1167848, by rfl⟩ : syracuseStep 1557131 = 2335697) B2335697
theorem B1557143 : Blo 1036608 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B1753751 : Blo 1036608 1753751 := bstep (se 1 (by rfl) ⟨1315313, by rfl⟩ : syracuseStep 1753751 = 2630627) B2630627
theorem B1557209 : Blo 1036608 1557209 := bstep (se 2 (by rfl) ⟨583953, by rfl⟩ : syracuseStep 1557209 = 1167907) B1167907
theorem B3556057 : Blo 1036608 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B1753879 : Blo 1036608 1753879 := bstep (se 1 (by rfl) ⟨1315409, by rfl⟩ : syracuseStep 1753879 = 2630819) B2630819
theorem B3949357 : Blo 1036608 3949357 := bstep (se 3 (by rfl) ⟨740504, by rfl⟩ : syracuseStep 3949357 = 1481009) B1481009
theorem B1557323 : Blo 1036608 1557323 := bstep (se 1 (by rfl) ⟨1167992, by rfl⟩ : syracuseStep 1557323 = 2335985) B2335985
theorem B1557335 : Blo 1036608 1557335 := bstep (se 1 (by rfl) ⟨1168001, by rfl⟩ : syracuseStep 1557335 = 2336003) B2336003
theorem B2802521 : Blo 1036608 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B2081675 : Blo 1036608 2081675 := bstep (se 1 (by rfl) ⟨1561256, by rfl⟩ : syracuseStep 2081675 = 3122513) B3122513
theorem B4440977 : Blo 1036608 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1557401 : Blo 1036608 1557401 := bstep (se 2 (by rfl) ⟨584025, by rfl⟩ : syracuseStep 1557401 = 1168051) B1168051
theorem B2802653 : Blo 1036608 2802653 := bstep (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) B1050995
theorem B1557515 : Blo 1036608 1557515 := bstep (se 1 (by rfl) ⟨1168136, by rfl⟩ : syracuseStep 1557515 = 2336273) B2336273
theorem B1557527 : Blo 1036608 1557527 := bstep (se 1 (by rfl) ⟨1168145, by rfl⟩ : syracuseStep 1557527 = 2336291) B2336291
theorem B1557593 : Blo 1036608 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B3949661 : Blo 1036608 3949661 := bstep (se 3 (by rfl) ⟨740561, by rfl⟩ : syracuseStep 3949661 = 1481123) B1481123
theorem B1557707 : Blo 1036608 1557707 := bstep (se 1 (by rfl) ⟨1168280, by rfl⟩ : syracuseStep 1557707 = 2336561) B2336561
theorem B1557719 : Blo 1036608 1557719 := bstep (se 1 (by rfl) ⟨1168289, by rfl⟩ : syracuseStep 1557719 = 2336579) B2336579
theorem B1557785 : Blo 1036608 1557785 := bstep (se 2 (by rfl) ⟨584169, by rfl⟩ : syracuseStep 1557785 = 1168339) B1168339
theorem B1557899 : Blo 1036608 1557899 := bstep (se 1 (by rfl) ⟨1168424, by rfl⟩ : syracuseStep 1557899 = 2336849) B2336849
theorem B1754507 : Blo 1036608 1754507 := bstep (se 1 (by rfl) ⟨1315880, by rfl⟩ : syracuseStep 1754507 = 2631761) B2631761
theorem B1557911 : Blo 1036608 1557911 := bstep (se 1 (by rfl) ⟨1168433, by rfl⟩ : syracuseStep 1557911 = 2336867) B2336867
theorem B1557977 : Blo 1036608 1557977 := bstep (se 2 (by rfl) ⟨584241, by rfl⟩ : syracuseStep 1557977 = 1168483) B1168483
theorem B1754635 : Blo 1036608 1754635 := bstep (se 1 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 1754635 = 2631953) B2631953
theorem B1558091 : Blo 1036608 1558091 := bstep (se 1 (by rfl) ⟨1168568, by rfl⟩ : syracuseStep 1558091 = 2337137) B2337137
theorem B1558103 : Blo 1036608 1558103 := bstep (se 1 (by rfl) ⟨1168577, by rfl⟩ : syracuseStep 1558103 = 2337155) B2337155
theorem B3327581 : Blo 1036608 3327581 := bstep (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) B1247843
theorem B1558169 : Blo 1036608 1558169 := bstep (se 2 (by rfl) ⟨584313, by rfl⟩ : syracuseStep 1558169 = 1168627) B1168627
theorem B1754777 : Blo 1036608 1754777 := bstep (se 2 (by rfl) ⟨658041, by rfl⟩ : syracuseStep 1754777 = 1316083) B1316083
theorem B1558283 : Blo 1036608 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1558295 : Blo 1036608 1558295 := bstep (se 1 (by rfl) ⟨1168721, by rfl⟩ : syracuseStep 1558295 = 2337443) B2337443
theorem B1754905 : Blo 1036608 1754905 := bstep (se 2 (by rfl) ⟨658089, by rfl⟩ : syracuseStep 1754905 = 1316179) B1316179
theorem B1558361 : Blo 1036608 1558361 := bstep (se 2 (by rfl) ⟨584385, by rfl⟩ : syracuseStep 1558361 = 1168771) B1168771
theorem B1558475 : Blo 1036608 1558475 := bstep (se 1 (by rfl) ⟨1168856, by rfl⟩ : syracuseStep 1558475 = 2337713) B2337713
theorem B1558487 : Blo 1036608 1558487 := bstep (se 1 (by rfl) ⟨1168865, by rfl⟩ : syracuseStep 1558487 = 2337731) B2337731
theorem B5261273 : Blo 1036608 5261273 := bstep (se 2 (by rfl) ⟨1972977, by rfl⟩ : syracuseStep 5261273 = 3945955) B3945955
theorem B1558553 : Blo 1036608 1558553 := bstep (se 2 (by rfl) ⟨584457, by rfl⟩ : syracuseStep 1558553 = 1168915) B1168915
theorem B5621825 : Blo 1036608 5621825 := bstep (se 2 (by rfl) ⟨2108184, by rfl⟩ : syracuseStep 5621825 = 4216369) B4216369
theorem B1558667 : Blo 1036608 1558667 := bstep (se 1 (by rfl) ⟨1169000, by rfl⟩ : syracuseStep 1558667 = 2338001) B2338001
theorem B1558679 : Blo 1036608 1558679 := bstep (se 1 (by rfl) ⟨1169009, by rfl⟩ : syracuseStep 1558679 = 2338019) B2338019
theorem B1558745 : Blo 1036608 1558745 := bstep (se 2 (by rfl) ⟨584529, by rfl⟩ : syracuseStep 1558745 = 1169059) B1169059
theorem B1558859 : Blo 1036608 1558859 := bstep (se 1 (by rfl) ⟨1169144, by rfl⟩ : syracuseStep 1558859 = 2338289) B2338289
theorem B1558871 : Blo 1036608 1558871 := bstep (se 1 (by rfl) ⟨1169153, by rfl⟩ : syracuseStep 1558871 = 2338307) B2338307
theorem B1755479 : Blo 1036608 1755479 := bstep (se 1 (by rfl) ⟨1316609, by rfl⟩ : syracuseStep 1755479 = 2633219) B2633219
theorem B1558937 : Blo 1036608 1558937 := bstep (se 2 (by rfl) ⟨584601, by rfl⟩ : syracuseStep 1558937 = 1169203) B1169203
theorem B18958769 : Blo 1036608 18958769 := bstep (se 2 (by rfl) ⟨7109538, by rfl⟩ : syracuseStep 18958769 = 14219077) B14219077
theorem B7489997 : Blo 1036608 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B1755607 : Blo 1036608 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B1559051 : Blo 1036608 1559051 := bstep (se 1 (by rfl) ⟨1169288, by rfl⟩ : syracuseStep 1559051 = 2338577) B2338577
theorem B1559063 : Blo 1036608 1559063 := bstep (se 1 (by rfl) ⟨1169297, by rfl⟩ : syracuseStep 1559063 = 2338595) B2338595
theorem B1559129 : Blo 1036608 1559129 := bstep (se 2 (by rfl) ⟨584673, by rfl⟩ : syracuseStep 1559129 = 1169347) B1169347
theorem B14994071 : Blo 1036608 14994071 := bstep (se 1 (by rfl) ⟨11245553, by rfl⟩ : syracuseStep 14994071 = 22491107) B22491107
theorem B1559243 : Blo 1036608 1559243 := bstep (se 1 (by rfl) ⟨1169432, by rfl⟩ : syracuseStep 1559243 = 2338865) B2338865
theorem B1559255 : Blo 1036608 1559255 := bstep (se 1 (by rfl) ⟨1169441, by rfl⟩ : syracuseStep 1559255 = 2338883) B2338883
theorem B3558109 : Blo 1036608 3558109 := bstep (se 3 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 3558109 = 1334291) B1334291
theorem B1559321 : Blo 1036608 1559321 := bstep (se 2 (by rfl) ⟨584745, by rfl⟩ : syracuseStep 1559321 = 1169491) B1169491
theorem B1559435 : Blo 1036608 1559435 := bstep (se 1 (by rfl) ⟨1169576, by rfl⟩ : syracuseStep 1559435 = 2339153) B2339153
theorem B1559447 : Blo 1036608 1559447 := bstep (se 1 (by rfl) ⟨1169585, by rfl⟩ : syracuseStep 1559447 = 2339171) B2339171
theorem B1166251 : Blo 1036608 1166251 := bstep (se 1 (by rfl) ⟨874688, by rfl⟩ : syracuseStep 1166251 = 1749377) B1749377
theorem B5917657 : Blo 1036608 5917657 := bstep (se 2 (by rfl) ⟨2219121, by rfl⟩ : syracuseStep 5917657 = 4438243) B4438243
theorem B1559513 : Blo 1036608 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B1166359 : Blo 1036608 1166359 := bstep (se 1 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 1166359 = 1749539) B1749539
theorem B1559627 : Blo 1036608 1559627 := bstep (se 1 (by rfl) ⟨1169720, by rfl⟩ : syracuseStep 1559627 = 2339441) B2339441
theorem B1559639 : Blo 1036608 1559639 := bstep (se 1 (by rfl) ⟨1169729, by rfl⟩ : syracuseStep 1559639 = 2339459) B2339459
theorem B1559705 : Blo 1036608 1559705 := bstep (se 2 (by rfl) ⟨584889, by rfl⟩ : syracuseStep 1559705 = 1169779) B1169779
theorem B1166539 : Blo 1036608 1166539 := bstep (se 1 (by rfl) ⟨874904, by rfl⟩ : syracuseStep 1166539 = 1749809) B1749809
theorem B1559819 : Blo 1036608 1559819 := bstep (se 1 (by rfl) ⟨1169864, by rfl⟩ : syracuseStep 1559819 = 2339729) B2339729
theorem B1559831 : Blo 1036608 1559831 := bstep (se 1 (by rfl) ⟨1169873, by rfl⟩ : syracuseStep 1559831 = 2339747) B2339747
theorem B4443437 : Blo 1036608 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B1166647 : Blo 1036608 1166647 := bstep (se 1 (by rfl) ⟨874985, by rfl⟩ : syracuseStep 1166647 = 1749971) B1749971
theorem B1559897 : Blo 1036608 1559897 := bstep (se 2 (by rfl) ⟨584961, by rfl⟩ : syracuseStep 1559897 = 1169923) B1169923
theorem B1560011 : Blo 1036608 1560011 := bstep (se 1 (by rfl) ⟨1170008, by rfl⟩ : syracuseStep 1560011 = 2340017) B2340017
theorem B1560023 : Blo 1036608 1560023 := bstep (se 1 (by rfl) ⟨1170017, by rfl⟩ : syracuseStep 1560023 = 2340035) B2340035
theorem B1166827 : Blo 1036608 1166827 := bstep (se 1 (by rfl) ⟨875120, by rfl⟩ : syracuseStep 1166827 = 1750241) B1750241
theorem B1560089 : Blo 1036608 1560089 := bstep (se 2 (by rfl) ⟨585033, by rfl⟩ : syracuseStep 1560089 = 1170067) B1170067
theorem B5262893 : Blo 1036608 5262893 := bstep (se 3 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 5262893 = 1973585) B1973585
theorem B1166935 : Blo 1036608 1166935 := bstep (se 1 (by rfl) ⟨875201, by rfl⟩ : syracuseStep 1166935 = 1750403) B1750403
theorem B1560203 : Blo 1036608 1560203 := bstep (se 1 (by rfl) ⟨1170152, by rfl⟩ : syracuseStep 1560203 = 2340305) B2340305
theorem B1560215 : Blo 1036608 1560215 := bstep (se 1 (by rfl) ⟨1170161, by rfl⟩ : syracuseStep 1560215 = 2340323) B2340323
theorem B1560281 : Blo 1036608 1560281 := bstep (se 2 (by rfl) ⟨585105, by rfl⟩ : syracuseStep 1560281 = 1170211) B1170211
theorem B16010993 : Blo 1036608 16010993 := bstep (se 2 (by rfl) ⟨6004122, by rfl⟩ : syracuseStep 16010993 = 12008245) B12008245
theorem B4738819 : Blo 1036608 4738819 := bstep (se 1 (by rfl) ⟨3554114, by rfl⟩ : syracuseStep 4738819 = 7108229) B7108229
theorem B1167115 : Blo 1036608 1167115 := bstep (se 1 (by rfl) ⟨875336, by rfl⟩ : syracuseStep 1167115 = 1750673) B1750673
theorem B5623597 : Blo 1036608 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B1560395 : Blo 1036608 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B1560407 : Blo 1036608 1560407 := bstep (se 1 (by rfl) ⟨1170305, by rfl⟩ : syracuseStep 1560407 = 2340611) B2340611
theorem B8408933 : Blo 1036608 8408933 := bstep (se 4 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 8408933 = 1576675) B1576675
theorem B1167223 : Blo 1036608 1167223 := bstep (se 1 (by rfl) ⟨875417, by rfl⟩ : syracuseStep 1167223 = 1750835) B1750835
theorem B7098263 : Blo 1036608 7098263 := bstep (se 1 (by rfl) ⟨5323697, by rfl⟩ : syracuseStep 7098263 = 10647395) B10647395
theorem B5918615 : Blo 1036608 5918615 := bstep (se 1 (by rfl) ⟨4438961, by rfl⟩ : syracuseStep 5918615 = 8877923) B8877923
theorem B1560473 : Blo 1036608 1560473 := bstep (se 2 (by rfl) ⟨585177, by rfl⟩ : syracuseStep 1560473 = 1170355) B1170355
theorem B4444121 : Blo 1036608 4444121 := bstep (se 2 (by rfl) ⟨1666545, by rfl⟩ : syracuseStep 4444121 = 3333091) B3333091
theorem B1560587 : Blo 1036608 1560587 := bstep (se 1 (by rfl) ⟨1170440, by rfl⟩ : syracuseStep 1560587 = 2340881) B2340881
theorem B1560599 : Blo 1036608 1560599 := bstep (se 1 (by rfl) ⟨1170449, by rfl⟩ : syracuseStep 1560599 = 2340899) B2340899
theorem B1167403 : Blo 1036608 1167403 := bstep (se 1 (by rfl) ⟨875552, by rfl⟩ : syracuseStep 1167403 = 1751105) B1751105
theorem B1560665 : Blo 1036608 1560665 := bstep (se 2 (by rfl) ⟨585249, by rfl⟩ : syracuseStep 1560665 = 1170499) B1170499
theorem B2805853 : Blo 1036608 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B5623901 : Blo 1036608 5623901 := bstep (se 3 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 5623901 = 2108963) B2108963
theorem B1167511 : Blo 1036608 1167511 := bstep (se 1 (by rfl) ⟨875633, by rfl⟩ : syracuseStep 1167511 = 1751267) B1751267
theorem B1560779 : Blo 1036608 1560779 := bstep (se 1 (by rfl) ⟨1170584, by rfl⟩ : syracuseStep 1560779 = 2341169) B2341169
theorem B1560791 : Blo 1036608 1560791 := bstep (se 1 (by rfl) ⟨1170593, by rfl⟩ : syracuseStep 1560791 = 2341187) B2341187
theorem B1560857 : Blo 1036608 1560857 := bstep (se 2 (by rfl) ⟨585321, by rfl⟩ : syracuseStep 1560857 = 1170643) B1170643
theorem B1036619 : Blo 1036608 1036619 := bstep (se 1 (by rfl) ⟨777464, by rfl⟩ : syracuseStep 1036619 = 1554929) B1554929
theorem B1167691 : Blo 1036608 1167691 := bstep (se 1 (by rfl) ⟨875768, by rfl⟩ : syracuseStep 1167691 = 1751537) B1751537
theorem B1036631 : Blo 1036608 1036631 := bstep (se 1 (by rfl) ⟨777473, by rfl⟩ : syracuseStep 1036631 = 1554947) B1554947
theorem B1036651 : Blo 1036608 1036651 := bstep (se 1 (by rfl) ⟨777488, by rfl⟩ : syracuseStep 1036651 = 1554977) B1554977
theorem B1036663 : Blo 1036608 1036663 := bstep (se 1 (by rfl) ⟨777497, by rfl⟩ : syracuseStep 1036663 = 1554995) B1554995
theorem B1036683 : Blo 1036608 1036683 := bstep (se 1 (by rfl) ⟨777512, by rfl⟩ : syracuseStep 1036683 = 1555025) B1555025
theorem B1036695 : Blo 1036608 1036695 := bstep (se 1 (by rfl) ⟨777521, by rfl⟩ : syracuseStep 1036695 = 1555043) B1555043
theorem B1036715 : Blo 1036608 1036715 := bstep (se 1 (by rfl) ⟨777536, by rfl⟩ : syracuseStep 1036715 = 1555073) B1555073
theorem B1036727 : Blo 1036608 1036727 := bstep (se 1 (by rfl) ⟨777545, by rfl⟩ : syracuseStep 1036727 = 1555091) B1555091
theorem B1167799 : Blo 1036608 1167799 := bstep (se 1 (by rfl) ⟨875849, by rfl⟩ : syracuseStep 1167799 = 1751699) B1751699
theorem B1036747 : Blo 1036608 1036747 := bstep (se 1 (by rfl) ⟨777560, by rfl⟩ : syracuseStep 1036747 = 1555121) B1555121
theorem B1036759 : Blo 1036608 1036759 := bstep (se 1 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 1036759 = 1555139) B1555139
theorem B1036779 : Blo 1036608 1036779 := bstep (se 1 (by rfl) ⟨777584, by rfl⟩ : syracuseStep 1036779 = 1555169) B1555169
theorem B1036791 : Blo 1036608 1036791 := bstep (se 1 (by rfl) ⟨777593, by rfl⟩ : syracuseStep 1036791 = 1555187) B1555187
theorem B1036811 : Blo 1036608 1036811 := bstep (se 1 (by rfl) ⟨777608, by rfl⟩ : syracuseStep 1036811 = 1555217) B1555217
theorem B2249227 : Blo 1036608 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1036823 : Blo 1036608 1036823 := bstep (se 1 (by rfl) ⟨777617, by rfl⟩ : syracuseStep 1036823 = 1555235) B1555235
theorem B1036843 : Blo 1036608 1036843 := bstep (se 1 (by rfl) ⟨777632, by rfl⟩ : syracuseStep 1036843 = 1555265) B1555265
theorem B9458221 : Blo 1036608 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B1036855 : Blo 1036608 1036855 := bstep (se 1 (by rfl) ⟨777641, by rfl⟩ : syracuseStep 1036855 = 1555283) B1555283
theorem B1036875 : Blo 1036608 1036875 := bstep (se 1 (by rfl) ⟨777656, by rfl⟩ : syracuseStep 1036875 = 1555313) B1555313
theorem B1036887 : Blo 1036608 1036887 := bstep (se 1 (by rfl) ⟨777665, by rfl⟩ : syracuseStep 1036887 = 1555331) B1555331
theorem B1036907 : Blo 1036608 1036907 := bstep (se 1 (by rfl) ⟨777680, by rfl⟩ : syracuseStep 1036907 = 1555361) B1555361
theorem B1167979 : Blo 1036608 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B1036919 : Blo 1036608 1036919 := bstep (se 1 (by rfl) ⟨777689, by rfl⟩ : syracuseStep 1036919 = 1555379) B1555379
theorem B1036939 : Blo 1036608 1036939 := bstep (se 1 (by rfl) ⟨777704, by rfl⟩ : syracuseStep 1036939 = 1555409) B1555409
theorem B1036951 : Blo 1036608 1036951 := bstep (se 1 (by rfl) ⟨777713, by rfl⟩ : syracuseStep 1036951 = 1555427) B1555427
theorem B1036971 : Blo 1036608 1036971 := bstep (se 1 (by rfl) ⟨777728, by rfl⟩ : syracuseStep 1036971 = 1555457) B1555457
theorem B1036983 : Blo 1036608 1036983 := bstep (se 1 (by rfl) ⟨777737, by rfl⟩ : syracuseStep 1036983 = 1555475) B1555475
theorem B1037003 : Blo 1036608 1037003 := bstep (se 1 (by rfl) ⟨777752, by rfl⟩ : syracuseStep 1037003 = 1555505) B1555505
theorem B1037015 : Blo 1036608 1037015 := bstep (se 1 (by rfl) ⟨777761, by rfl⟩ : syracuseStep 1037015 = 1555523) B1555523
theorem B1168087 : Blo 1036608 1168087 := bstep (se 1 (by rfl) ⟨876065, by rfl⟩ : syracuseStep 1168087 = 1752131) B1752131
theorem B1037035 : Blo 1036608 1037035 := bstep (se 1 (by rfl) ⟨777776, by rfl⟩ : syracuseStep 1037035 = 1555553) B1555553
theorem B71914225 : Blo 1036608 71914225 := bstep (se 2 (by rfl) ⟨26967834, by rfl⟩ : syracuseStep 71914225 = 53935669) B53935669
theorem B1037047 : Blo 1036608 1037047 := bstep (se 1 (by rfl) ⟨777785, by rfl⟩ : syracuseStep 1037047 = 1555571) B1555571
theorem B1037067 : Blo 1036608 1037067 := bstep (se 1 (by rfl) ⟨777800, by rfl⟩ : syracuseStep 1037067 = 1555601) B1555601
theorem B1037079 : Blo 1036608 1037079 := bstep (se 1 (by rfl) ⟨777809, by rfl⟩ : syracuseStep 1037079 = 1555619) B1555619
theorem B1037099 : Blo 1036608 1037099 := bstep (se 1 (by rfl) ⟨777824, by rfl⟩ : syracuseStep 1037099 = 1555649) B1555649
theorem B1037111 : Blo 1036608 1037111 := bstep (se 1 (by rfl) ⟨777833, by rfl⟩ : syracuseStep 1037111 = 1555667) B1555667
theorem B1037131 : Blo 1036608 1037131 := bstep (se 1 (by rfl) ⟨777848, by rfl⟩ : syracuseStep 1037131 = 1555697) B1555697
theorem B1037143 : Blo 1036608 1037143 := bstep (se 1 (by rfl) ⟨777857, by rfl⟩ : syracuseStep 1037143 = 1555715) B1555715
theorem B1037163 : Blo 1036608 1037163 := bstep (se 1 (by rfl) ⟨777872, by rfl⟩ : syracuseStep 1037163 = 1555745) B1555745
theorem B1037175 : Blo 1036608 1037175 := bstep (se 1 (by rfl) ⟨777881, by rfl⟩ : syracuseStep 1037175 = 1555763) B1555763
theorem B1037195 : Blo 1036608 1037195 := bstep (se 1 (by rfl) ⟨777896, by rfl⟩ : syracuseStep 1037195 = 1555793) B1555793
theorem B1168267 : Blo 1036608 1168267 := bstep (se 1 (by rfl) ⟨876200, by rfl⟩ : syracuseStep 1168267 = 1752401) B1752401
theorem B1037207 : Blo 1036608 1037207 := bstep (se 1 (by rfl) ⟨777905, by rfl⟩ : syracuseStep 1037207 = 1555811) B1555811
theorem B1037227 : Blo 1036608 1037227 := bstep (se 1 (by rfl) ⟨777920, by rfl⟩ : syracuseStep 1037227 = 1555841) B1555841
theorem B1037239 : Blo 1036608 1037239 := bstep (se 1 (by rfl) ⟨777929, by rfl⟩ : syracuseStep 1037239 = 1555859) B1555859
theorem B1037259 : Blo 1036608 1037259 := bstep (se 1 (by rfl) ⟨777944, by rfl⟩ : syracuseStep 1037259 = 1555889) B1555889
theorem B1037271 : Blo 1036608 1037271 := bstep (se 1 (by rfl) ⟨777953, by rfl⟩ : syracuseStep 1037271 = 1555907) B1555907
theorem B1037291 : Blo 1036608 1037291 := bstep (se 1 (by rfl) ⟨777968, by rfl⟩ : syracuseStep 1037291 = 1555937) B1555937
theorem B1037303 : Blo 1036608 1037303 := bstep (se 1 (by rfl) ⟨777977, by rfl⟩ : syracuseStep 1037303 = 1555955) B1555955
theorem B1168375 : Blo 1036608 1168375 := bstep (se 1 (by rfl) ⟨876281, by rfl⟩ : syracuseStep 1168375 = 1752563) B1752563
theorem B1037323 : Blo 1036608 1037323 := bstep (se 1 (by rfl) ⟨777992, by rfl⟩ : syracuseStep 1037323 = 1555985) B1555985
theorem B1037335 : Blo 1036608 1037335 := bstep (se 1 (by rfl) ⟨778001, by rfl⟩ : syracuseStep 1037335 = 1556003) B1556003
theorem B1037355 : Blo 1036608 1037355 := bstep (se 1 (by rfl) ⟨778016, by rfl⟩ : syracuseStep 1037355 = 1556033) B1556033
theorem B1037367 : Blo 1036608 1037367 := bstep (se 1 (by rfl) ⟨778025, by rfl⟩ : syracuseStep 1037367 = 1556051) B1556051
theorem B1037387 : Blo 1036608 1037387 := bstep (se 1 (by rfl) ⟨778040, by rfl⟩ : syracuseStep 1037387 = 1556081) B1556081
theorem B1037399 : Blo 1036608 1037399 := bstep (se 1 (by rfl) ⟨778049, by rfl⟩ : syracuseStep 1037399 = 1556099) B1556099
theorem B5985373 : Blo 1036608 5985373 := bstep (se 3 (by rfl) ⟨1122257, by rfl⟩ : syracuseStep 5985373 = 2244515) B2244515
theorem B1037419 : Blo 1036608 1037419 := bstep (se 1 (by rfl) ⟨778064, by rfl⟩ : syracuseStep 1037419 = 1556129) B1556129
theorem B1037431 : Blo 1036608 1037431 := bstep (se 1 (by rfl) ⟨778073, by rfl⟩ : syracuseStep 1037431 = 1556147) B1556147
theorem B1037451 : Blo 1036608 1037451 := bstep (se 1 (by rfl) ⟨778088, by rfl⟩ : syracuseStep 1037451 = 1556177) B1556177
theorem B1037463 : Blo 1036608 1037463 := bstep (se 1 (by rfl) ⟨778097, by rfl⟩ : syracuseStep 1037463 = 1556195) B1556195
theorem B1037483 : Blo 1036608 1037483 := bstep (se 1 (by rfl) ⟨778112, by rfl⟩ : syracuseStep 1037483 = 1556225) B1556225
theorem B1168555 : Blo 1036608 1168555 := bstep (se 1 (by rfl) ⟨876416, by rfl⟩ : syracuseStep 1168555 = 1752833) B1752833
theorem B1037495 : Blo 1036608 1037495 := bstep (se 1 (by rfl) ⟨778121, by rfl⟩ : syracuseStep 1037495 = 1556243) B1556243
theorem B1037515 : Blo 1036608 1037515 := bstep (se 1 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 1037515 = 1556273) B1556273
theorem B1037527 : Blo 1036608 1037527 := bstep (se 1 (by rfl) ⟨778145, by rfl⟩ : syracuseStep 1037527 = 1556291) B1556291
theorem B1037547 : Blo 1036608 1037547 := bstep (se 1 (by rfl) ⟨778160, by rfl⟩ : syracuseStep 1037547 = 1556321) B1556321
theorem B1037559 : Blo 1036608 1037559 := bstep (se 1 (by rfl) ⟨778169, by rfl⟩ : syracuseStep 1037559 = 1556339) B1556339
theorem B1037579 : Blo 1036608 1037579 := bstep (se 1 (by rfl) ⟨778184, by rfl⟩ : syracuseStep 1037579 = 1556369) B1556369
theorem B1037591 : Blo 1036608 1037591 := bstep (se 1 (by rfl) ⟨778193, by rfl⟩ : syracuseStep 1037591 = 1556387) B1556387
theorem B1168663 : Blo 1036608 1168663 := bstep (se 1 (by rfl) ⟨876497, by rfl⟩ : syracuseStep 1168663 = 1752995) B1752995
theorem B1037611 : Blo 1036608 1037611 := bstep (se 1 (by rfl) ⟨778208, by rfl⟩ : syracuseStep 1037611 = 1556417) B1556417
theorem B1037623 : Blo 1036608 1037623 := bstep (se 1 (by rfl) ⟨778217, by rfl⟩ : syracuseStep 1037623 = 1556435) B1556435
theorem B1037643 : Blo 1036608 1037643 := bstep (se 1 (by rfl) ⟨778232, by rfl⟩ : syracuseStep 1037643 = 1556465) B1556465
theorem B1037655 : Blo 1036608 1037655 := bstep (se 1 (by rfl) ⟨778241, by rfl⟩ : syracuseStep 1037655 = 1556483) B1556483
theorem B2807129 : Blo 1036608 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B1037675 : Blo 1036608 1037675 := bstep (se 1 (by rfl) ⟨778256, by rfl⟩ : syracuseStep 1037675 = 1556513) B1556513
theorem B1037687 : Blo 1036608 1037687 := bstep (se 1 (by rfl) ⟨778265, by rfl⟩ : syracuseStep 1037687 = 1556531) B1556531
theorem B1037707 : Blo 1036608 1037707 := bstep (se 1 (by rfl) ⟨778280, by rfl⟩ : syracuseStep 1037707 = 1556561) B1556561
theorem B1037719 : Blo 1036608 1037719 := bstep (se 1 (by rfl) ⟨778289, by rfl⟩ : syracuseStep 1037719 = 1556579) B1556579
theorem B1037739 : Blo 1036608 1037739 := bstep (se 1 (by rfl) ⟨778304, by rfl⟩ : syracuseStep 1037739 = 1556609) B1556609
theorem B1037751 : Blo 1036608 1037751 := bstep (se 1 (by rfl) ⟨778313, by rfl⟩ : syracuseStep 1037751 = 1556627) B1556627
theorem B1037771 : Blo 1036608 1037771 := bstep (se 1 (by rfl) ⟨778328, by rfl⟩ : syracuseStep 1037771 = 1556657) B1556657
theorem B1168843 : Blo 1036608 1168843 := bstep (se 1 (by rfl) ⟨876632, by rfl⟩ : syracuseStep 1168843 = 1753265) B1753265
theorem B1037783 : Blo 1036608 1037783 := bstep (se 1 (by rfl) ⟨778337, by rfl⟩ : syracuseStep 1037783 = 1556675) B1556675
theorem B2217431 : Blo 1036608 2217431 := bstep (se 1 (by rfl) ⟨1663073, by rfl⟩ : syracuseStep 2217431 = 3326147) B3326147
theorem B1037803 : Blo 1036608 1037803 := bstep (se 1 (by rfl) ⟨778352, by rfl⟩ : syracuseStep 1037803 = 1556705) B1556705
theorem B1037815 : Blo 1036608 1037815 := bstep (se 1 (by rfl) ⟨778361, by rfl⟩ : syracuseStep 1037815 = 1556723) B1556723
theorem B1037835 : Blo 1036608 1037835 := bstep (se 1 (by rfl) ⟨778376, by rfl⟩ : syracuseStep 1037835 = 1556753) B1556753
theorem B1037847 : Blo 1036608 1037847 := bstep (se 1 (by rfl) ⟨778385, by rfl⟩ : syracuseStep 1037847 = 1556771) B1556771
theorem B1037867 : Blo 1036608 1037867 := bstep (se 1 (by rfl) ⟨778400, by rfl⟩ : syracuseStep 1037867 = 1556801) B1556801
theorem B1037879 : Blo 1036608 1037879 := bstep (se 1 (by rfl) ⟨778409, by rfl⟩ : syracuseStep 1037879 = 1556819) B1556819
theorem B1168951 : Blo 1036608 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B1037899 : Blo 1036608 1037899 := bstep (se 1 (by rfl) ⟨778424, by rfl⟩ : syracuseStep 1037899 = 1556849) B1556849
theorem B1037911 : Blo 1036608 1037911 := bstep (se 1 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 1037911 = 1556867) B1556867
theorem B1037931 : Blo 1036608 1037931 := bstep (se 1 (by rfl) ⟨778448, by rfl⟩ : syracuseStep 1037931 = 1556897) B1556897
theorem B1037943 : Blo 1036608 1037943 := bstep (se 1 (by rfl) ⟨778457, by rfl⟩ : syracuseStep 1037943 = 1556915) B1556915
theorem B1037963 : Blo 1036608 1037963 := bstep (se 1 (by rfl) ⟨778472, by rfl⟩ : syracuseStep 1037963 = 1556945) B1556945
theorem B2217611 : Blo 1036608 2217611 := bstep (se 1 (by rfl) ⟨1663208, by rfl⟩ : syracuseStep 2217611 = 3326417) B3326417
theorem B1037975 : Blo 1036608 1037975 := bstep (se 1 (by rfl) ⟨778481, by rfl⟩ : syracuseStep 1037975 = 1556963) B1556963
theorem B1037995 : Blo 1036608 1037995 := bstep (se 1 (by rfl) ⟨778496, by rfl⟩ : syracuseStep 1037995 = 1556993) B1556993
theorem B16864949 : Blo 1036608 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B1038007 : Blo 1036608 1038007 := bstep (se 1 (by rfl) ⟨778505, by rfl⟩ : syracuseStep 1038007 = 1557011) B1557011
theorem B1038027 : Blo 1036608 1038027 := bstep (se 1 (by rfl) ⟨778520, by rfl⟩ : syracuseStep 1038027 = 1557041) B1557041
theorem B1038039 : Blo 1036608 1038039 := bstep (se 1 (by rfl) ⟨778529, by rfl⟩ : syracuseStep 1038039 = 1557059) B1557059
theorem B1038059 : Blo 1036608 1038059 := bstep (se 1 (by rfl) ⟨778544, by rfl⟩ : syracuseStep 1038059 = 1557089) B1557089
theorem B1169131 : Blo 1036608 1169131 := bstep (se 1 (by rfl) ⟨876848, by rfl⟩ : syracuseStep 1169131 = 1753697) B1753697
theorem B1038071 : Blo 1036608 1038071 := bstep (se 1 (by rfl) ⟨778553, by rfl⟩ : syracuseStep 1038071 = 1557107) B1557107
theorem B1038091 : Blo 1036608 1038091 := bstep (se 1 (by rfl) ⟨778568, by rfl⟩ : syracuseStep 1038091 = 1557137) B1557137
theorem B1038103 : Blo 1036608 1038103 := bstep (se 1 (by rfl) ⟨778577, by rfl⟩ : syracuseStep 1038103 = 1557155) B1557155
theorem B1038123 : Blo 1036608 1038123 := bstep (se 1 (by rfl) ⟨778592, by rfl⟩ : syracuseStep 1038123 = 1557185) B1557185
theorem B1038135 : Blo 1036608 1038135 := bstep (se 1 (by rfl) ⟨778601, by rfl⟩ : syracuseStep 1038135 = 1557203) B1557203
theorem B1038155 : Blo 1036608 1038155 := bstep (se 1 (by rfl) ⟨778616, by rfl⟩ : syracuseStep 1038155 = 1557233) B1557233
theorem B1038167 : Blo 1036608 1038167 := bstep (se 1 (by rfl) ⟨778625, by rfl⟩ : syracuseStep 1038167 = 1557251) B1557251
theorem B1169239 : Blo 1036608 1169239 := bstep (se 1 (by rfl) ⟨876929, by rfl⟩ : syracuseStep 1169239 = 1753859) B1753859
theorem B1038187 : Blo 1036608 1038187 := bstep (se 1 (by rfl) ⟨778640, by rfl⟩ : syracuseStep 1038187 = 1557281) B1557281
theorem B1038199 : Blo 1036608 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B1038219 : Blo 1036608 1038219 := bstep (se 1 (by rfl) ⟨778664, by rfl⟩ : syracuseStep 1038219 = 1557329) B1557329
theorem B1038231 : Blo 1036608 1038231 := bstep (se 1 (by rfl) ⟨778673, by rfl⟩ : syracuseStep 1038231 = 1557347) B1557347
theorem B1038251 : Blo 1036608 1038251 := bstep (se 1 (by rfl) ⟨778688, by rfl⟩ : syracuseStep 1038251 = 1557377) B1557377
theorem B1038263 : Blo 1036608 1038263 := bstep (se 1 (by rfl) ⟨778697, by rfl⟩ : syracuseStep 1038263 = 1557395) B1557395
theorem B1038283 : Blo 1036608 1038283 := bstep (se 1 (by rfl) ⟨778712, by rfl⟩ : syracuseStep 1038283 = 1557425) B1557425
theorem B1038295 : Blo 1036608 1038295 := bstep (se 1 (by rfl) ⟨778721, by rfl⟩ : syracuseStep 1038295 = 1557443) B1557443
theorem B1038315 : Blo 1036608 1038315 := bstep (se 1 (by rfl) ⟨778736, by rfl⟩ : syracuseStep 1038315 = 1557473) B1557473
theorem B1038327 : Blo 1036608 1038327 := bstep (se 1 (by rfl) ⟨778745, by rfl⟩ : syracuseStep 1038327 = 1557491) B1557491
theorem B1038347 : Blo 1036608 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B1169419 : Blo 1036608 1169419 := bstep (se 1 (by rfl) ⟨877064, by rfl⟩ : syracuseStep 1169419 = 1754129) B1754129
theorem B1038359 : Blo 1036608 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B1038379 : Blo 1036608 1038379 := bstep (se 1 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 1038379 = 1557569) B1557569
theorem B1038391 : Blo 1036608 1038391 := bstep (se 1 (by rfl) ⟨778793, by rfl⟩ : syracuseStep 1038391 = 1557587) B1557587
theorem B1038411 : Blo 1036608 1038411 := bstep (se 1 (by rfl) ⟨778808, by rfl⟩ : syracuseStep 1038411 = 1557617) B1557617
theorem B1038423 : Blo 1036608 1038423 := bstep (se 1 (by rfl) ⟨778817, by rfl⟩ : syracuseStep 1038423 = 1557635) B1557635
theorem B1038443 : Blo 1036608 1038443 := bstep (se 1 (by rfl) ⟨778832, by rfl⟩ : syracuseStep 1038443 = 1557665) B1557665
theorem B1038455 : Blo 1036608 1038455 := bstep (se 1 (by rfl) ⟨778841, by rfl⟩ : syracuseStep 1038455 = 1557683) B1557683
theorem B1169527 : Blo 1036608 1169527 := bstep (se 1 (by rfl) ⟨877145, by rfl⟩ : syracuseStep 1169527 = 1754291) B1754291
theorem B1038475 : Blo 1036608 1038475 := bstep (se 1 (by rfl) ⟨778856, by rfl⟩ : syracuseStep 1038475 = 1557713) B1557713
theorem B1333387 : Blo 1036608 1333387 := bstep (se 1 (by rfl) ⟨1000040, by rfl⟩ : syracuseStep 1333387 = 2000081) B2000081
theorem B7100567 : Blo 1036608 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B1038487 : Blo 1036608 1038487 := bstep (se 1 (by rfl) ⟨778865, by rfl⟩ : syracuseStep 1038487 = 1557731) B1557731
theorem B1038507 : Blo 1036608 1038507 := bstep (se 1 (by rfl) ⟨778880, by rfl⟩ : syracuseStep 1038507 = 1557761) B1557761
theorem B1038519 : Blo 1036608 1038519 := bstep (se 1 (by rfl) ⟨778889, by rfl⟩ : syracuseStep 1038519 = 1557779) B1557779
theorem B1038539 : Blo 1036608 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B1038551 : Blo 1036608 1038551 := bstep (se 1 (by rfl) ⟨778913, by rfl⟩ : syracuseStep 1038551 = 1557827) B1557827
theorem B3791069 : Blo 1036608 3791069 := bstep (se 3 (by rfl) ⟨710825, by rfl⟩ : syracuseStep 3791069 = 1421651) B1421651
theorem B1038571 : Blo 1036608 1038571 := bstep (se 1 (by rfl) ⟨778928, by rfl⟩ : syracuseStep 1038571 = 1557857) B1557857
theorem B1038583 : Blo 1036608 1038583 := bstep (se 1 (by rfl) ⟨778937, by rfl⟩ : syracuseStep 1038583 = 1557875) B1557875
theorem B1038603 : Blo 1036608 1038603 := bstep (se 1 (by rfl) ⟨778952, by rfl⟩ : syracuseStep 1038603 = 1557905) B1557905
theorem B1038615 : Blo 1036608 1038615 := bstep (se 1 (by rfl) ⟨778961, by rfl⟩ : syracuseStep 1038615 = 1557923) B1557923
theorem B1038635 : Blo 1036608 1038635 := bstep (se 1 (by rfl) ⟨778976, by rfl⟩ : syracuseStep 1038635 = 1557953) B1557953
theorem B1169707 : Blo 1036608 1169707 := bstep (se 1 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 1169707 = 1754561) B1754561
theorem B1038647 : Blo 1036608 1038647 := bstep (se 1 (by rfl) ⟨778985, by rfl⟩ : syracuseStep 1038647 = 1557971) B1557971
theorem B1038667 : Blo 1036608 1038667 := bstep (se 1 (by rfl) ⟨779000, by rfl⟩ : syracuseStep 1038667 = 1558001) B1558001
theorem B5921099 : Blo 1036608 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B1038679 : Blo 1036608 1038679 := bstep (se 1 (by rfl) ⟨779009, by rfl⟩ : syracuseStep 1038679 = 1558019) B1558019
theorem B1038699 : Blo 1036608 1038699 := bstep (se 1 (by rfl) ⟨779024, by rfl⟩ : syracuseStep 1038699 = 1558049) B1558049
theorem B1038711 : Blo 1036608 1038711 := bstep (se 1 (by rfl) ⟨779033, by rfl⟩ : syracuseStep 1038711 = 1558067) B1558067
theorem B1038731 : Blo 1036608 1038731 := bstep (se 1 (by rfl) ⟨779048, by rfl⟩ : syracuseStep 1038731 = 1558097) B1558097
theorem B1038743 : Blo 1036608 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B1169815 : Blo 1036608 1169815 := bstep (se 1 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 1169815 = 1754723) B1754723
theorem B1038763 : Blo 1036608 1038763 := bstep (se 1 (by rfl) ⟨779072, by rfl⟩ : syracuseStep 1038763 = 1558145) B1558145
theorem B1038775 : Blo 1036608 1038775 := bstep (se 1 (by rfl) ⟨779081, by rfl⟩ : syracuseStep 1038775 = 1558163) B1558163
theorem B1038795 : Blo 1036608 1038795 := bstep (se 1 (by rfl) ⟨779096, by rfl⟩ : syracuseStep 1038795 = 1558193) B1558193
theorem B1038807 : Blo 1036608 1038807 := bstep (se 1 (by rfl) ⟨779105, by rfl⟩ : syracuseStep 1038807 = 1558211) B1558211
theorem B1038827 : Blo 1036608 1038827 := bstep (se 1 (by rfl) ⟨779120, by rfl⟩ : syracuseStep 1038827 = 1558241) B1558241
theorem B1038839 : Blo 1036608 1038839 := bstep (se 1 (by rfl) ⟨779129, by rfl⟩ : syracuseStep 1038839 = 1558259) B1558259
theorem B1038859 : Blo 1036608 1038859 := bstep (se 1 (by rfl) ⟨779144, by rfl⟩ : syracuseStep 1038859 = 1558289) B1558289
theorem B4741649 : Blo 1036608 4741649 := bstep (se 2 (by rfl) ⟨1778118, by rfl⟩ : syracuseStep 4741649 = 3556237) B3556237
theorem B1038871 : Blo 1036608 1038871 := bstep (se 1 (by rfl) ⟨779153, by rfl⟩ : syracuseStep 1038871 = 1558307) B1558307
theorem B1038891 : Blo 1036608 1038891 := bstep (se 1 (by rfl) ⟨779168, by rfl⟩ : syracuseStep 1038891 = 1558337) B1558337
theorem B1038903 : Blo 1036608 1038903 := bstep (se 1 (by rfl) ⟨779177, by rfl⟩ : syracuseStep 1038903 = 1558355) B1558355
theorem B1038923 : Blo 1036608 1038923 := bstep (se 1 (by rfl) ⟨779192, by rfl⟩ : syracuseStep 1038923 = 1558385) B1558385
theorem B1169995 : Blo 1036608 1169995 := bstep (se 1 (by rfl) ⟨877496, by rfl⟩ : syracuseStep 1169995 = 1754993) B1754993
theorem B1038935 : Blo 1036608 1038935 := bstep (se 1 (by rfl) ⟨779201, by rfl⟩ : syracuseStep 1038935 = 1558403) B1558403
theorem B1038955 : Blo 1036608 1038955 := bstep (se 1 (by rfl) ⟨779216, by rfl⟩ : syracuseStep 1038955 = 1558433) B1558433
theorem B1038967 : Blo 1036608 1038967 := bstep (se 1 (by rfl) ⟨779225, by rfl⟩ : syracuseStep 1038967 = 1558451) B1558451
theorem B1038987 : Blo 1036608 1038987 := bstep (se 1 (by rfl) ⟨779240, by rfl⟩ : syracuseStep 1038987 = 1558481) B1558481
theorem B1038999 : Blo 1036608 1038999 := bstep (se 1 (by rfl) ⟨779249, by rfl⟩ : syracuseStep 1038999 = 1558499) B1558499
theorem B1039019 : Blo 1036608 1039019 := bstep (se 1 (by rfl) ⟨779264, by rfl⟩ : syracuseStep 1039019 = 1558529) B1558529
theorem B4741811 : Blo 1036608 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B1039031 : Blo 1036608 1039031 := bstep (se 1 (by rfl) ⟨779273, by rfl⟩ : syracuseStep 1039031 = 1558547) B1558547
theorem B1170103 : Blo 1036608 1170103 := bstep (se 1 (by rfl) ⟨877577, by rfl⟩ : syracuseStep 1170103 = 1755155) B1755155
theorem B1039051 : Blo 1036608 1039051 := bstep (se 1 (by rfl) ⟨779288, by rfl⟩ : syracuseStep 1039051 = 1558577) B1558577
theorem B1039063 : Blo 1036608 1039063 := bstep (se 1 (by rfl) ⟨779297, by rfl⟩ : syracuseStep 1039063 = 1558595) B1558595
theorem B1039083 : Blo 1036608 1039083 := bstep (se 1 (by rfl) ⟨779312, by rfl⟩ : syracuseStep 1039083 = 1558625) B1558625
theorem B1039095 : Blo 1036608 1039095 := bstep (se 1 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 1039095 = 1558643) B1558643
theorem B1039115 : Blo 1036608 1039115 := bstep (se 1 (by rfl) ⟨779336, by rfl⟩ : syracuseStep 1039115 = 1558673) B1558673
theorem B1039127 : Blo 1036608 1039127 := bstep (se 1 (by rfl) ⟨779345, by rfl⟩ : syracuseStep 1039127 = 1558691) B1558691
theorem B1039147 : Blo 1036608 1039147 := bstep (se 1 (by rfl) ⟨779360, by rfl⟩ : syracuseStep 1039147 = 1558721) B1558721
theorem B1039159 : Blo 1036608 1039159 := bstep (se 1 (by rfl) ⟨779369, by rfl⟩ : syracuseStep 1039159 = 1558739) B1558739
theorem B1039179 : Blo 1036608 1039179 := bstep (se 1 (by rfl) ⟨779384, by rfl⟩ : syracuseStep 1039179 = 1558769) B1558769
theorem B1039191 : Blo 1036608 1039191 := bstep (se 1 (by rfl) ⟨779393, by rfl⟩ : syracuseStep 1039191 = 1558787) B1558787
theorem B1039211 : Blo 1036608 1039211 := bstep (se 1 (by rfl) ⟨779408, by rfl⟩ : syracuseStep 1039211 = 1558817) B1558817
theorem B1170283 : Blo 1036608 1170283 := bstep (se 1 (by rfl) ⟨877712, by rfl⟩ : syracuseStep 1170283 = 1755425) B1755425
theorem B1039223 : Blo 1036608 1039223 := bstep (se 1 (by rfl) ⟨779417, by rfl⟩ : syracuseStep 1039223 = 1558835) B1558835
theorem B1039243 : Blo 1036608 1039243 := bstep (se 1 (by rfl) ⟨779432, by rfl⟩ : syracuseStep 1039243 = 1558865) B1558865
theorem B1039255 : Blo 1036608 1039255 := bstep (se 1 (by rfl) ⟨779441, by rfl⟩ : syracuseStep 1039255 = 1558883) B1558883
theorem B1039275 : Blo 1036608 1039275 := bstep (se 1 (by rfl) ⟨779456, by rfl⟩ : syracuseStep 1039275 = 1558913) B1558913
theorem B1039287 : Blo 1036608 1039287 := bstep (se 1 (by rfl) ⟨779465, by rfl⟩ : syracuseStep 1039287 = 1558931) B1558931
theorem B1039307 : Blo 1036608 1039307 := bstep (se 1 (by rfl) ⟨779480, by rfl⟩ : syracuseStep 1039307 = 1558961) B1558961
theorem B1039319 : Blo 1036608 1039319 := bstep (se 1 (by rfl) ⟨779489, by rfl⟩ : syracuseStep 1039319 = 1558979) B1558979
theorem B1170391 : Blo 1036608 1170391 := bstep (se 1 (by rfl) ⟨877793, by rfl⟩ : syracuseStep 1170391 = 1755587) B1755587
theorem B1039339 : Blo 1036608 1039339 := bstep (se 1 (by rfl) ⟨779504, by rfl⟩ : syracuseStep 1039339 = 1559009) B1559009
theorem B1039351 : Blo 1036608 1039351 := bstep (se 1 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 1039351 = 1559027) B1559027
theorem B1039371 : Blo 1036608 1039371 := bstep (se 1 (by rfl) ⟨779528, by rfl⟩ : syracuseStep 1039371 = 1559057) B1559057
theorem B1039383 : Blo 1036608 1039383 := bstep (se 1 (by rfl) ⟨779537, by rfl⟩ : syracuseStep 1039383 = 1559075) B1559075
theorem B3333143 : Blo 1036608 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1039403 : Blo 1036608 1039403 := bstep (se 1 (by rfl) ⟨779552, by rfl⟩ : syracuseStep 1039403 = 1559105) B1559105
theorem B1039415 : Blo 1036608 1039415 := bstep (se 1 (by rfl) ⟨779561, by rfl⟩ : syracuseStep 1039415 = 1559123) B1559123
theorem B1039435 : Blo 1036608 1039435 := bstep (se 1 (by rfl) ⟨779576, by rfl⟩ : syracuseStep 1039435 = 1559153) B1559153
theorem B1039447 : Blo 1036608 1039447 := bstep (se 1 (by rfl) ⟨779585, by rfl⟩ : syracuseStep 1039447 = 1559171) B1559171
theorem B1039467 : Blo 1036608 1039467 := bstep (se 1 (by rfl) ⟨779600, by rfl⟩ : syracuseStep 1039467 = 1559201) B1559201
theorem B1039479 : Blo 1036608 1039479 := bstep (se 1 (by rfl) ⟨779609, by rfl⟩ : syracuseStep 1039479 = 1559219) B1559219
theorem B1039499 : Blo 1036608 1039499 := bstep (se 1 (by rfl) ⟨779624, by rfl⟩ : syracuseStep 1039499 = 1559249) B1559249
theorem B1170571 : Blo 1036608 1170571 := bstep (se 1 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 1170571 = 1755857) B1755857
theorem B1039511 : Blo 1036608 1039511 := bstep (se 1 (by rfl) ⟨779633, by rfl⟩ : syracuseStep 1039511 = 1559267) B1559267
theorem B1039531 : Blo 1036608 1039531 := bstep (se 1 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 1039531 = 1559297) B1559297
theorem B1039543 : Blo 1036608 1039543 := bstep (se 1 (by rfl) ⟨779657, by rfl⟩ : syracuseStep 1039543 = 1559315) B1559315
theorem B1039563 : Blo 1036608 1039563 := bstep (se 1 (by rfl) ⟨779672, by rfl⟩ : syracuseStep 1039563 = 1559345) B1559345
theorem B1039575 : Blo 1036608 1039575 := bstep (se 1 (by rfl) ⟨779681, by rfl⟩ : syracuseStep 1039575 = 1559363) B1559363
theorem B1039595 : Blo 1036608 1039595 := bstep (se 1 (by rfl) ⟨779696, by rfl⟩ : syracuseStep 1039595 = 1559393) B1559393
theorem B2219251 : Blo 1036608 2219251 := bstep (se 1 (by rfl) ⟨1664438, by rfl⟩ : syracuseStep 2219251 = 3328877) B3328877
theorem B1039607 : Blo 1036608 1039607 := bstep (se 1 (by rfl) ⟨779705, by rfl⟩ : syracuseStep 1039607 = 1559411) B1559411
theorem B1170679 : Blo 1036608 1170679 := bstep (se 1 (by rfl) ⟨878009, by rfl⟩ : syracuseStep 1170679 = 1756019) B1756019
theorem B1039627 : Blo 1036608 1039627 := bstep (se 1 (by rfl) ⟨779720, by rfl⟩ : syracuseStep 1039627 = 1559441) B1559441
theorem B1039639 : Blo 1036608 1039639 := bstep (se 1 (by rfl) ⟨779729, by rfl⟩ : syracuseStep 1039639 = 1559459) B1559459
theorem B1039659 : Blo 1036608 1039659 := bstep (se 1 (by rfl) ⟨779744, by rfl⟩ : syracuseStep 1039659 = 1559489) B1559489
theorem B1039671 : Blo 1036608 1039671 := bstep (se 1 (by rfl) ⟨779753, by rfl⟩ : syracuseStep 1039671 = 1559507) B1559507
theorem B1039691 : Blo 1036608 1039691 := bstep (se 1 (by rfl) ⟨779768, by rfl⟩ : syracuseStep 1039691 = 1559537) B1559537
theorem B1039703 : Blo 1036608 1039703 := bstep (se 1 (by rfl) ⟨779777, by rfl⟩ : syracuseStep 1039703 = 1559555) B1559555
theorem B5266781 : Blo 1036608 5266781 := bstep (se 3 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 5266781 = 1975043) B1975043
theorem B1039723 : Blo 1036608 1039723 := bstep (se 1 (by rfl) ⟨779792, by rfl⟩ : syracuseStep 1039723 = 1559585) B1559585
theorem B1039735 : Blo 1036608 1039735 := bstep (se 1 (by rfl) ⟨779801, by rfl⟩ : syracuseStep 1039735 = 1559603) B1559603
theorem B1039755 : Blo 1036608 1039755 := bstep (se 1 (by rfl) ⟨779816, by rfl⟩ : syracuseStep 1039755 = 1559633) B1559633
theorem B1039767 : Blo 1036608 1039767 := bstep (se 1 (by rfl) ⟨779825, by rfl⟩ : syracuseStep 1039767 = 1559651) B1559651
theorem B1039787 : Blo 1036608 1039787 := bstep (se 1 (by rfl) ⟨779840, by rfl⟩ : syracuseStep 1039787 = 1559681) B1559681
theorem B1039799 : Blo 1036608 1039799 := bstep (se 1 (by rfl) ⟨779849, by rfl⟩ : syracuseStep 1039799 = 1559699) B1559699
theorem B1039819 : Blo 1036608 1039819 := bstep (se 1 (by rfl) ⟨779864, by rfl⟩ : syracuseStep 1039819 = 1559729) B1559729
theorem B1039831 : Blo 1036608 1039831 := bstep (se 1 (by rfl) ⟨779873, by rfl⟩ : syracuseStep 1039831 = 1559747) B1559747
theorem B1039851 : Blo 1036608 1039851 := bstep (se 1 (by rfl) ⟨779888, by rfl⟩ : syracuseStep 1039851 = 1559777) B1559777
theorem B1039863 : Blo 1036608 1039863 := bstep (se 1 (by rfl) ⟨779897, by rfl⟩ : syracuseStep 1039863 = 1559795) B1559795
theorem B1039883 : Blo 1036608 1039883 := bstep (se 1 (by rfl) ⟨779912, by rfl⟩ : syracuseStep 1039883 = 1559825) B1559825
theorem B1039895 : Blo 1036608 1039895 := bstep (se 1 (by rfl) ⟨779921, by rfl⟩ : syracuseStep 1039895 = 1559843) B1559843
theorem B1039915 : Blo 1036608 1039915 := bstep (se 1 (by rfl) ⟨779936, by rfl⟩ : syracuseStep 1039915 = 1559873) B1559873
theorem B1039927 : Blo 1036608 1039927 := bstep (se 1 (by rfl) ⟨779945, by rfl⟩ : syracuseStep 1039927 = 1559891) B1559891
theorem B1039947 : Blo 1036608 1039947 := bstep (se 1 (by rfl) ⟨779960, by rfl⟩ : syracuseStep 1039947 = 1559921) B1559921
theorem B3333707 : Blo 1036608 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1039959 : Blo 1036608 1039959 := bstep (se 1 (by rfl) ⟨779969, by rfl⟩ : syracuseStep 1039959 = 1559939) B1559939
theorem B1039979 : Blo 1036608 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B1039991 : Blo 1036608 1039991 := bstep (se 1 (by rfl) ⟨779993, by rfl⟩ : syracuseStep 1039991 = 1559987) B1559987
theorem B1040011 : Blo 1036608 1040011 := bstep (se 1 (by rfl) ⟨780008, by rfl⟩ : syracuseStep 1040011 = 1560017) B1560017
theorem B1040023 : Blo 1036608 1040023 := bstep (se 1 (by rfl) ⟨780017, by rfl⟩ : syracuseStep 1040023 = 1560035) B1560035
theorem B1040043 : Blo 1036608 1040043 := bstep (se 1 (by rfl) ⟨780032, by rfl⟩ : syracuseStep 1040043 = 1560065) B1560065
theorem B1040055 : Blo 1036608 1040055 := bstep (se 1 (by rfl) ⟨780041, by rfl⟩ : syracuseStep 1040055 = 1560083) B1560083
theorem B1040075 : Blo 1036608 1040075 := bstep (se 1 (by rfl) ⟨780056, by rfl⟩ : syracuseStep 1040075 = 1560113) B1560113
theorem B1040087 : Blo 1036608 1040087 := bstep (se 1 (by rfl) ⟨780065, by rfl⟩ : syracuseStep 1040087 = 1560131) B1560131
theorem B2219737 : Blo 1036608 2219737 := bstep (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) B1664803
theorem B1040107 : Blo 1036608 1040107 := bstep (se 1 (by rfl) ⟨780080, by rfl⟩ : syracuseStep 1040107 = 1560161) B1560161
theorem B1040119 : Blo 1036608 1040119 := bstep (se 1 (by rfl) ⟨780089, by rfl⟩ : syracuseStep 1040119 = 1560179) B1560179
theorem B1040139 : Blo 1036608 1040139 := bstep (se 1 (by rfl) ⟨780104, by rfl⟩ : syracuseStep 1040139 = 1560209) B1560209
theorem B1040151 : Blo 1036608 1040151 := bstep (se 1 (by rfl) ⟨780113, by rfl⟩ : syracuseStep 1040151 = 1560227) B1560227
theorem B1040171 : Blo 1036608 1040171 := bstep (se 1 (by rfl) ⟨780128, by rfl⟩ : syracuseStep 1040171 = 1560257) B1560257
theorem B1040183 : Blo 1036608 1040183 := bstep (se 1 (by rfl) ⟨780137, by rfl⟩ : syracuseStep 1040183 = 1560275) B1560275
theorem B4218689 : Blo 1036608 4218689 := bstep (se 2 (by rfl) ⟨1582008, by rfl⟩ : syracuseStep 4218689 = 3164017) B3164017
theorem B1040203 : Blo 1036608 1040203 := bstep (se 1 (by rfl) ⟨780152, by rfl⟩ : syracuseStep 1040203 = 1560305) B1560305
theorem B1040215 : Blo 1036608 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B1040235 : Blo 1036608 1040235 := bstep (se 1 (by rfl) ⟨780176, by rfl⟩ : syracuseStep 1040235 = 1560353) B1560353
theorem B1040247 : Blo 1036608 1040247 := bstep (se 1 (by rfl) ⟨780185, by rfl⟩ : syracuseStep 1040247 = 1560371) B1560371
theorem B1040267 : Blo 1036608 1040267 := bstep (se 1 (by rfl) ⟨780200, by rfl⟩ : syracuseStep 1040267 = 1560401) B1560401
theorem B1040279 : Blo 1036608 1040279 := bstep (se 1 (by rfl) ⟨780209, by rfl⟩ : syracuseStep 1040279 = 1560419) B1560419
theorem B1040299 : Blo 1036608 1040299 := bstep (se 1 (by rfl) ⟨780224, by rfl⟩ : syracuseStep 1040299 = 1560449) B1560449
theorem B1040311 : Blo 1036608 1040311 := bstep (se 1 (by rfl) ⟨780233, by rfl⟩ : syracuseStep 1040311 = 1560467) B1560467
theorem B1040331 : Blo 1036608 1040331 := bstep (se 1 (by rfl) ⟨780248, by rfl⟩ : syracuseStep 1040331 = 1560497) B1560497
theorem B1040343 : Blo 1036608 1040343 := bstep (se 1 (by rfl) ⟨780257, by rfl⟩ : syracuseStep 1040343 = 1560515) B1560515
theorem B1040363 : Blo 1036608 1040363 := bstep (se 1 (by rfl) ⟨780272, by rfl⟩ : syracuseStep 1040363 = 1560545) B1560545
theorem B1040375 : Blo 1036608 1040375 := bstep (se 1 (by rfl) ⟨780281, by rfl⟩ : syracuseStep 1040375 = 1560563) B1560563
theorem B1040395 : Blo 1036608 1040395 := bstep (se 1 (by rfl) ⟨780296, by rfl⟩ : syracuseStep 1040395 = 1560593) B1560593
theorem B1040407 : Blo 1036608 1040407 := bstep (se 1 (by rfl) ⟨780305, by rfl⟩ : syracuseStep 1040407 = 1560611) B1560611
theorem B1040427 : Blo 1036608 1040427 := bstep (se 1 (by rfl) ⟨780320, by rfl⟩ : syracuseStep 1040427 = 1560641) B1560641
theorem B1040439 : Blo 1036608 1040439 := bstep (se 1 (by rfl) ⟨780329, by rfl⟩ : syracuseStep 1040439 = 1560659) B1560659
theorem B1040459 : Blo 1036608 1040459 := bstep (se 1 (by rfl) ⟨780344, by rfl⟩ : syracuseStep 1040459 = 1560689) B1560689
theorem B1040471 : Blo 1036608 1040471 := bstep (se 1 (by rfl) ⟨780353, by rfl⟩ : syracuseStep 1040471 = 1560707) B1560707
theorem B1040491 : Blo 1036608 1040491 := bstep (se 1 (by rfl) ⟨780368, by rfl⟩ : syracuseStep 1040491 = 1560737) B1560737
theorem B1040503 : Blo 1036608 1040503 := bstep (se 1 (by rfl) ⟨780377, by rfl⟩ : syracuseStep 1040503 = 1560755) B1560755
theorem B1040523 : Blo 1036608 1040523 := bstep (se 1 (by rfl) ⟨780392, by rfl⟩ : syracuseStep 1040523 = 1560785) B1560785
theorem B1040535 : Blo 1036608 1040535 := bstep (se 1 (by rfl) ⟨780401, by rfl⟩ : syracuseStep 1040535 = 1560803) B1560803
theorem B1040555 : Blo 1036608 1040555 := bstep (se 1 (by rfl) ⟨780416, by rfl⟩ : syracuseStep 1040555 = 1560833) B1560833
theorem B1040567 : Blo 1036608 1040567 := bstep (se 1 (by rfl) ⟨780425, by rfl⟩ : syracuseStep 1040567 = 1560851) B1560851
theorem B1040587 : Blo 1036608 1040587 := bstep (se 1 (by rfl) ⟨780440, by rfl⟩ : syracuseStep 1040587 = 1560881) B1560881
theorem B1040599 : Blo 1036608 1040599 := bstep (se 1 (by rfl) ⟨780449, by rfl⟩ : syracuseStep 1040599 = 1560899) B1560899
theorem B35938829 : Blo 1036608 35938829 := bstep (se 3 (by rfl) ⟨6738530, by rfl⟩ : syracuseStep 35938829 = 13477061) B13477061
theorem B6840877 : Blo 1036608 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B8872523 : Blo 1036608 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B3498713 : Blo 1036608 3498713 := bstep (se 2 (by rfl) ⟨1312017, by rfl⟩ : syracuseStep 3498713 = 2624035) B2624035
theorem B5923763 : Blo 1036608 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B2221121 : Blo 1036608 2221121 := bstep (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) B1665841
theorem B3499415 : Blo 1036608 3499415 := bstep (se 1 (by rfl) ⟨2624561, by rfl⟩ : syracuseStep 3499415 = 5249123) B5249123
theorem B37873169 : Blo 1036608 37873169 := bstep (se 2 (by rfl) ⟨14202438, by rfl⟩ : syracuseStep 37873169 = 28404877) B28404877
theorem B2221643 : Blo 1036608 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B1107767 : Blo 1036608 1107767 := bstep (se 1 (by rfl) ⟨830825, by rfl⟩ : syracuseStep 1107767 = 1661651) B1661651
theorem B3499955 : Blo 1036608 3499955 := bstep (se 1 (by rfl) ⟨2624966, by rfl⟩ : syracuseStep 3499955 = 5249933) B5249933
theorem B60778637 : Blo 1036608 60778637 := bstep (se 3 (by rfl) ⟨11395994, by rfl⟩ : syracuseStep 60778637 = 22791989) B22791989
theorem B3991697 : Blo 1036608 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B3500225 : Blo 1036608 3500225 := bstep (se 2 (by rfl) ⟨1312584, by rfl⟩ : syracuseStep 3500225 = 2625169) B2625169
theorem B5925221 : Blo 1036608 5925221 := bstep (se 4 (by rfl) ⟨555489, by rfl⟩ : syracuseStep 5925221 = 1110979) B1110979
theorem B60615029 : Blo 1036608 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B19982861 : Blo 1036608 19982861 := bstep (se 3 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 19982861 = 7493573) B7493573
theorem B1665623 : Blo 1036608 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B13298327 : Blo 1036608 13298327 := bstep (se 1 (by rfl) ⟨9973745, by rfl⟩ : syracuseStep 13298327 = 19947491) B19947491
theorem B3500765 : Blo 1036608 3500765 := bstep (se 3 (by rfl) ⟨656393, by rfl⟩ : syracuseStep 3500765 = 1312787) B1312787
theorem B4746115 : Blo 1036608 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B23981017 : Blo 1036608 23981017 := bstep (se 2 (by rfl) ⟨8992881, by rfl⟩ : syracuseStep 23981017 = 17985763) B17985763
theorem B5925905 : Blo 1036608 5925905 := bstep (se 2 (by rfl) ⟨2222214, by rfl⟩ : syracuseStep 5925905 = 4444429) B4444429
theorem B15199301 : Blo 1036608 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B4746371 : Blo 1036608 4746371 := bstep (se 1 (by rfl) ⟨3559778, by rfl⟩ : syracuseStep 4746371 = 7119557) B7119557
theorem B1666187 : Blo 1036608 1666187 := bstep (se 1 (by rfl) ⟨1249640, by rfl⟩ : syracuseStep 1666187 = 2499281) B2499281
theorem B205090019 : Blo 1036608 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B1666699 : Blo 1036608 1666699 := bstep (se 1 (by rfl) ⟨1250024, by rfl⟩ : syracuseStep 1666699 = 2500049) B2500049
theorem B3501899 : Blo 1036608 3501899 := bstep (se 1 (by rfl) ⟨2626424, by rfl⟩ : syracuseStep 3501899 = 5252849) B5252849
theorem B1109899 : Blo 1036608 1109899 := bstep (se 1 (by rfl) ⟨832424, by rfl⟩ : syracuseStep 1109899 = 1664849) B1664849
theorem B3502169 : Blo 1036608 3502169 := bstep (se 2 (by rfl) ⟨1313313, by rfl⟩ : syracuseStep 3502169 = 2626627) B2626627
theorem B8417753 : Blo 1036608 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B9466469 : Blo 1036608 9466469 := bstep (se 4 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 9466469 = 1774963) B1774963
theorem B3502871 : Blo 1036608 3502871 := bstep (se 1 (by rfl) ⟨2627153, by rfl⟩ : syracuseStep 3502871 = 5254307) B5254307
theorem B6583427 : Blo 1036608 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B3503411 : Blo 1036608 3503411 := bstep (se 1 (by rfl) ⟨2627558, by rfl⟩ : syracuseStep 3503411 = 5255117) B5255117
theorem B16840037 : Blo 1036608 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B3503681 : Blo 1036608 3503681 := bstep (se 2 (by rfl) ⟨1313880, by rfl⟩ : syracuseStep 3503681 = 2627761) B2627761
theorem B1996633 : Blo 1036608 1996633 := bstep (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) B1497475
theorem B3504221 : Blo 1036608 3504221 := bstep (se 3 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 3504221 = 1314083) B1314083
theorem B3505355 : Blo 1036608 3505355 := bstep (se 1 (by rfl) ⟨2629016, by rfl⟩ : syracuseStep 3505355 = 5258033) B5258033
theorem B1899737 : Blo 1036608 1899737 := bstep (se 2 (by rfl) ⟨712401, by rfl⟩ : syracuseStep 1899737 = 1424803) B1424803
theorem B3505625 : Blo 1036608 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B11828753 : Blo 1036608 11828753 := bstep (se 2 (by rfl) ⟨4435782, by rfl⟩ : syracuseStep 11828753 = 8871565) B8871565
theorem B3997457 : Blo 1036608 3997457 := bstep (se 2 (by rfl) ⟨1499046, by rfl⟩ : syracuseStep 3997457 = 2998093) B2998093
theorem B1900439 : Blo 1036608 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B3506219 : Blo 1036608 3506219 := bstep (se 1 (by rfl) ⟨2629664, by rfl⟩ : syracuseStep 3506219 = 5259329) B5259329
theorem B32407955 : Blo 1036608 32407955 := bstep (se 1 (by rfl) ⟨24305966, by rfl⟩ : syracuseStep 32407955 = 48611933) B48611933
theorem B12649061 : Blo 1036608 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B1868435 : Blo 1036608 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B7111397 : Blo 1036608 7111397 := bstep (se 4 (by rfl) ⟨666693, by rfl⟩ : syracuseStep 7111397 = 1333387) B1333387
theorem B3507515 : Blo 1036608 3507515 := bstep (se 1 (by rfl) ⟨2630636, by rfl⟩ : syracuseStep 3507515 = 5261273) B5261273
theorem B22808141 : Blo 1036608 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B1312519 : Blo 1036608 1312519 := bstep (se 1 (by rfl) ⟨984389, by rfl⟩ : syracuseStep 1312519 = 1968779) B1968779
theorem B9996047 : Blo 1036608 9996047 := bstep (se 1 (by rfl) ⟨7497035, by rfl⟩ : syracuseStep 9996047 = 14994071) B14994071
theorem B3508001 : Blo 1036608 3508001 := bstep (se 2 (by rfl) ⟨1315500, by rfl⟩ : syracuseStep 3508001 = 2631001) B2631001
theorem B1312939 : Blo 1036608 1312939 := bstep (se 1 (by rfl) ⟨984704, by rfl⟩ : syracuseStep 1312939 = 1969409) B1969409
theorem B7473389 : Blo 1036608 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B3508595 : Blo 1036608 3508595 := bstep (se 1 (by rfl) ⟨2631446, by rfl⟩ : syracuseStep 3508595 = 5262893) B5262893
theorem B1313167 : Blo 1036608 1313167 := bstep (se 1 (by rfl) ⟨984875, by rfl⟩ : syracuseStep 1313167 = 1969751) B1969751
theorem B2624015 : Blo 1036608 2624015 := bstep (se 1 (by rfl) ⟨1968011, by rfl⟩ : syracuseStep 2624015 = 3936023) B3936023
theorem B5605955 : Blo 1036608 5605955 := bstep (se 1 (by rfl) ⟨4204466, by rfl⟩ : syracuseStep 5605955 = 8408933) B8408933
theorem B2624147 : Blo 1036608 2624147 := bstep (se 1 (by rfl) ⟨1968110, by rfl⟩ : syracuseStep 2624147 = 3936221) B3936221
theorem B5606081 : Blo 1036608 5606081 := bstep (se 2 (by rfl) ⟨2102280, by rfl⟩ : syracuseStep 5606081 = 4204561) B4204561
theorem B11995877 : Blo 1036608 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B1051579 : Blo 1036608 1051579 := bstep (se 1 (by rfl) ⟨788684, by rfl⟩ : syracuseStep 1051579 = 1577369) B1577369
theorem B1969211 : Blo 1036608 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B1313911 : Blo 1036608 1313911 := bstep (se 1 (by rfl) ⟨985433, by rfl⟩ : syracuseStep 1313911 = 1970867) B1970867
theorem B1314235 : Blo 1036608 1314235 := bstep (se 1 (by rfl) ⟨985676, by rfl⟩ : syracuseStep 1314235 = 1971353) B1971353
theorem B1969697 : Blo 1036608 1969697 := bstep (se 2 (by rfl) ⟨738636, by rfl⟩ : syracuseStep 1969697 = 1477273) B1477273
theorem B1871419 : Blo 1036608 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B1478287 : Blo 1036608 1478287 := bstep (se 1 (by rfl) ⟨1108715, by rfl⟩ : syracuseStep 1478287 = 2217431) B2217431
theorem B1969849 : Blo 1036608 1969849 := bstep (se 2 (by rfl) ⟨738693, by rfl⟩ : syracuseStep 1969849 = 1477387) B1477387
theorem B7900901 : Blo 1036608 7900901 := bstep (se 4 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 7900901 = 1481419) B1481419
theorem B2625281 : Blo 1036608 2625281 := bstep (se 2 (by rfl) ⟨984480, by rfl⟩ : syracuseStep 2625281 = 1968961) B1968961
theorem B1478407 : Blo 1036608 1478407 := bstep (se 1 (by rfl) ⟨1108805, by rfl⟩ : syracuseStep 1478407 = 2217611) B2217611
theorem B11243299 : Blo 1036608 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B6328153 : Blo 1036608 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B1314731 : Blo 1036608 1314731 := bstep (se 1 (by rfl) ⟨986048, by rfl⟩ : syracuseStep 1314731 = 1972097) B1972097
theorem B2625655 : Blo 1036608 2625655 := bstep (se 1 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 2625655 = 3938483) B3938483
theorem B2527379 : Blo 1036608 2527379 := bstep (se 1 (by rfl) ⟨1895534, by rfl⟩ : syracuseStep 2527379 = 3791069) B3791069
theorem B1315207 : Blo 1036608 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B3936721 : Blo 1036608 3936721 := bstep (se 2 (by rfl) ⟨1476270, by rfl⟩ : syracuseStep 3936721 = 2952541) B2952541
theorem B2626091 : Blo 1036608 2626091 := bstep (se 1 (by rfl) ⟨1969568, by rfl⟩ : syracuseStep 2626091 = 3939137) B3939137
theorem B3937025 : Blo 1036608 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B2953999 : Blo 1036608 2953999 := bstep (se 1 (by rfl) ⟨2215499, by rfl⟩ : syracuseStep 2953999 = 4430999) B4430999
theorem B2954045 : Blo 1036608 2954045 := bstep (se 3 (by rfl) ⟨553883, by rfl⟩ : syracuseStep 2954045 = 1107767) B1107767
theorem B1315703 : Blo 1036608 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B3511187 : Blo 1036608 3511187 := bstep (se 1 (by rfl) ⟨2633390, by rfl⟩ : syracuseStep 3511187 = 5266781) B5266781
theorem B1053703 : Blo 1036608 1053703 := bstep (se 1 (by rfl) ⟨790277, by rfl⟩ : syracuseStep 1053703 = 1580555) B1580555
theorem B1315855 : Blo 1036608 1315855 := bstep (se 1 (by rfl) ⟨986891, by rfl⟩ : syracuseStep 1315855 = 1973783) B1973783
theorem B2954387 : Blo 1036608 2954387 := bstep (se 1 (by rfl) ⟨2215790, by rfl⟩ : syracuseStep 2954387 = 4431581) B4431581
theorem B1479865 : Blo 1036608 1479865 := bstep (se 2 (by rfl) ⟨554949, by rfl⟩ : syracuseStep 1479865 = 1109899) B1109899
theorem B1316027 : Blo 1036608 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B3937481 : Blo 1036608 3937481 := bstep (se 2 (by rfl) ⟨1476555, by rfl⟩ : syracuseStep 3937481 = 2953111) B2953111
theorem B2626931 : Blo 1036608 2626931 := bstep (se 1 (by rfl) ⟨1970198, by rfl⟩ : syracuseStep 2626931 = 3940397) B3940397
theorem B9966979 : Blo 1036608 9966979 := bstep (se 1 (by rfl) ⟨7475234, by rfl⟩ : syracuseStep 9966979 = 14950469) B14950469
theorem B2626951 : Blo 1036608 2626951 := bstep (se 1 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 2626951 = 3940427) B3940427
theorem B1971641 : Blo 1036608 1971641 := bstep (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) B1478731
theorem B3741137 : Blo 1036608 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B2627225 : Blo 1036608 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B2332475 : Blo 1036608 2332475 := bstep (se 1 (by rfl) ⟨1749356, by rfl⟩ : syracuseStep 2332475 = 3498713) B3498713
theorem B2627387 : Blo 1036608 2627387 := bstep (se 1 (by rfl) ⟨1970540, by rfl⟩ : syracuseStep 2627387 = 3941081) B3941081
theorem B2332601 : Blo 1036608 2332601 := bstep (se 2 (by rfl) ⟨874725, by rfl⟩ : syracuseStep 2332601 = 1749451) B1749451
theorem B2955275 : Blo 1036608 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B2627599 : Blo 1036608 2627599 := bstep (se 1 (by rfl) ⟨1970699, by rfl⟩ : syracuseStep 2627599 = 3941399) B3941399
theorem B1316999 : Blo 1036608 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B2332943 : Blo 1036608 2332943 := bstep (se 1 (by rfl) ⟨1749707, by rfl⟩ : syracuseStep 2332943 = 3499415) B3499415
theorem B2332961 : Blo 1036608 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B2627873 : Blo 1036608 2627873 := bstep (se 2 (by rfl) ⟨985452, by rfl⟩ : syracuseStep 2627873 = 1970905) B1970905
theorem B95885633 : Blo 1036608 95885633 := bstep (se 2 (by rfl) ⟨35957112, by rfl⟩ : syracuseStep 95885633 = 71914225) B71914225
theorem B1481095 : Blo 1036608 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B2333303 : Blo 1036608 2333303 := bstep (se 1 (by rfl) ⟨1749977, by rfl⟩ : syracuseStep 2333303 = 3499955) B3499955
theorem B2661131 : Blo 1036608 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B2333483 : Blo 1036608 2333483 := bstep (se 1 (by rfl) ⟨1750112, by rfl⟩ : syracuseStep 2333483 = 3500225) B3500225
theorem B2366327 : Blo 1036608 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B40410019 : Blo 1036608 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B2333843 : Blo 1036608 2333843 := bstep (se 1 (by rfl) ⟨1750382, by rfl⟩ : syracuseStep 2333843 = 3500765) B3500765
theorem B2333897 : Blo 1036608 2333897 := bstep (se 2 (by rfl) ⟨875211, by rfl⟩ : syracuseStep 2333897 = 1750423) B1750423
theorem B2628875 : Blo 1036608 2628875 := bstep (se 1 (by rfl) ⟨1971656, by rfl⟩ : syracuseStep 2628875 = 3943313) B3943313
theorem B5250419 : Blo 1036608 5250419 := bstep (se 1 (by rfl) ⟨3937814, by rfl⟩ : syracuseStep 5250419 = 7875629) B7875629
theorem B10132867 : Blo 1036608 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B1973639 : Blo 1036608 1973639 := bstep (se 1 (by rfl) ⟨1480229, by rfl⟩ : syracuseStep 1973639 = 2960459) B2960459
theorem B5905811 : Blo 1036608 5905811 := bstep (se 1 (by rfl) ⟨4429358, by rfl⟩ : syracuseStep 5905811 = 8858717) B8858717
theorem B4431257 : Blo 1036608 4431257 := bstep (se 2 (by rfl) ⟨1661721, by rfl⟩ : syracuseStep 4431257 = 3323443) B3323443
theorem B2956915 : Blo 1036608 2956915 := bstep (se 1 (by rfl) ⟨2217686, by rfl⟩ : syracuseStep 2956915 = 4435373) B4435373
theorem B2957143 : Blo 1036608 2957143 := bstep (se 1 (by rfl) ⟨2217857, by rfl⟩ : syracuseStep 2957143 = 4435715) B4435715
theorem B5250905 : Blo 1036608 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B2334599 : Blo 1036608 2334599 := bstep (se 1 (by rfl) ⟨1750949, by rfl⟩ : syracuseStep 2334599 = 3501899) B3501899
theorem B2629523 : Blo 1036608 2629523 := bstep (se 1 (by rfl) ⟨1972142, by rfl⟩ : syracuseStep 2629523 = 3944285) B3944285
theorem B4988951 : Blo 1036608 4988951 := bstep (se 1 (by rfl) ⟨3741713, by rfl⟩ : syracuseStep 4988951 = 7483427) B7483427
theorem B2334779 : Blo 1036608 2334779 := bstep (se 1 (by rfl) ⟨1751084, by rfl⟩ : syracuseStep 2334779 = 3502169) B3502169
theorem B11837501 : Blo 1036608 11837501 := bstep (se 3 (by rfl) ⟨2219531, by rfl⟩ : syracuseStep 11837501 = 4439063) B4439063
theorem B5906519 : Blo 1036608 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B2334905 : Blo 1036608 2334905 := bstep (se 2 (by rfl) ⟨875589, by rfl⟩ : syracuseStep 2334905 = 1751179) B1751179
theorem B2629817 : Blo 1036608 2629817 := bstep (se 2 (by rfl) ⟨986181, by rfl⟩ : syracuseStep 2629817 = 1972363) B1972363
theorem B7872713 : Blo 1036608 7872713 := bstep (se 2 (by rfl) ⟨2952267, by rfl⟩ : syracuseStep 7872713 = 5904535) B5904535
theorem B3940609 : Blo 1036608 3940609 := bstep (se 2 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 3940609 = 2955457) B2955457
theorem B5611835 : Blo 1036608 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B12656989 : Blo 1036608 12656989 := bstep (se 3 (by rfl) ⟨2373185, by rfl⟩ : syracuseStep 12656989 = 4746371) B4746371
theorem B2335247 : Blo 1036608 2335247 := bstep (se 1 (by rfl) ⟨1751435, by rfl⟩ : syracuseStep 2335247 = 3502871) B3502871
theorem B2335265 : Blo 1036608 2335265 := bstep (se 2 (by rfl) ⟨875724, by rfl⟩ : syracuseStep 2335265 = 1751449) B1751449
theorem B8889061 : Blo 1036608 8889061 := bstep (se 4 (by rfl) ⟨833349, by rfl⟩ : syracuseStep 8889061 = 1666699) B1666699
theorem B2630515 : Blo 1036608 2630515 := bstep (se 1 (by rfl) ⟨1972886, by rfl⟩ : syracuseStep 2630515 = 3945773) B3945773
theorem B2335607 : Blo 1036608 2335607 := bstep (se 1 (by rfl) ⟨1751705, by rfl⟩ : syracuseStep 2335607 = 3503411) B3503411
theorem B1975241 : Blo 1036608 1975241 := bstep (se 2 (by rfl) ⟨740715, by rfl⟩ : syracuseStep 1975241 = 1481431) B1481431
theorem B2630657 : Blo 1036608 2630657 := bstep (se 2 (by rfl) ⟨986496, by rfl⟩ : syracuseStep 2630657 = 1972993) B1972993
theorem B2335787 : Blo 1036608 2335787 := bstep (se 1 (by rfl) ⟨1751840, by rfl⟩ : syracuseStep 2335787 = 3503681) B3503681
theorem B2958727 : Blo 1036608 2958727 := bstep (se 1 (by rfl) ⟨2219045, by rfl⟩ : syracuseStep 2958727 = 4438091) B4438091
theorem B2336147 : Blo 1036608 2336147 := bstep (se 1 (by rfl) ⟨1752110, by rfl⟩ : syracuseStep 2336147 = 3504221) B3504221
theorem B2336201 : Blo 1036608 2336201 := bstep (se 2 (by rfl) ⟨876075, by rfl⟩ : syracuseStep 2336201 = 1752151) B1752151
theorem B2631113 : Blo 1036608 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B29992517 : Blo 1036608 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B2959001 : Blo 1036608 2959001 := bstep (se 2 (by rfl) ⟨1109625, by rfl⟩ : syracuseStep 2959001 = 2219251) B2219251
theorem B2631467 : Blo 1036608 2631467 := bstep (se 1 (by rfl) ⟨1973600, by rfl⟩ : syracuseStep 2631467 = 3947201) B3947201
theorem B4990855 : Blo 1036608 4990855 := bstep (se 1 (by rfl) ⟨3743141, by rfl⟩ : syracuseStep 4990855 = 7486283) B7486283
theorem B5253011 : Blo 1036608 5253011 := bstep (se 1 (by rfl) ⟨3939758, by rfl⟩ : syracuseStep 5253011 = 7879517) B7879517
theorem B5908409 : Blo 1036608 5908409 := bstep (se 2 (by rfl) ⟨2215653, by rfl⟩ : syracuseStep 5908409 = 4431307) B4431307
theorem B2336903 : Blo 1036608 2336903 := bstep (se 1 (by rfl) ⟨1752677, by rfl⟩ : syracuseStep 2336903 = 3505355) B3505355
theorem B2369683 : Blo 1036608 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B18917549 : Blo 1036608 18917549 := bstep (se 3 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 18917549 = 7094081) B7094081
theorem B11249837 : Blo 1036608 11249837 := bstep (se 3 (by rfl) ⟨2109344, by rfl⟩ : syracuseStep 11249837 = 4218689) B4218689
theorem B2959649 : Blo 1036608 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B2337083 : Blo 1036608 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B2337209 : Blo 1036608 2337209 := bstep (se 2 (by rfl) ⟨876453, by rfl⟩ : syracuseStep 2337209 = 1752907) B1752907
theorem B9972173 : Blo 1036608 9972173 := bstep (se 3 (by rfl) ⟨1869782, by rfl⟩ : syracuseStep 9972173 = 3739565) B3739565
theorem B2664971 : Blo 1036608 2664971 := bstep (se 1 (by rfl) ⟨1998728, by rfl⟩ : syracuseStep 2664971 = 3997457) B3997457
theorem B2107919 : Blo 1036608 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B4434689 : Blo 1036608 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B2632459 : Blo 1036608 2632459 := bstep (se 1 (by rfl) ⟨1974344, by rfl⟩ : syracuseStep 2632459 = 3948689) B3948689
theorem B2337551 : Blo 1036608 2337551 := bstep (se 1 (by rfl) ⟨1753163, by rfl⟩ : syracuseStep 2337551 = 3506327) B3506327
theorem B2337569 : Blo 1036608 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B2632601 : Blo 1036608 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B2632763 : Blo 1036608 2632763 := bstep (se 1 (by rfl) ⟨1974572, by rfl⟩ : syracuseStep 2632763 = 3949145) B3949145
theorem B3943511 : Blo 1036608 3943511 := bstep (se 1 (by rfl) ⟨2957633, by rfl⟩ : syracuseStep 3943511 = 5915267) B5915267
theorem B2337911 : Blo 1036608 2337911 := bstep (se 1 (by rfl) ⟨1753433, by rfl⟩ : syracuseStep 2337911 = 3506867) B3506867
theorem B1387783 : Blo 1036608 1387783 := bstep (se 1 (by rfl) ⟨1040837, by rfl⟩ : syracuseStep 1387783 = 2081675) B2081675
theorem B2960651 : Blo 1036608 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B2338091 : Blo 1036608 2338091 := bstep (se 1 (by rfl) ⟨1753568, by rfl⟩ : syracuseStep 2338091 = 3507137) B3507137
theorem B9121169 : Blo 1036608 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B2633107 : Blo 1036608 2633107 := bstep (se 1 (by rfl) ⟨1974830, by rfl⟩ : syracuseStep 2633107 = 3949661) B3949661
theorem B2633249 : Blo 1036608 2633249 := bstep (se 2 (by rfl) ⟨987468, by rfl⟩ : syracuseStep 2633249 = 1974937) B1974937
theorem B3943997 : Blo 1036608 3943997 := bstep (se 3 (by rfl) ⟨739499, by rfl⟩ : syracuseStep 3943997 = 1478999) B1478999
theorem B3321431 : Blo 1036608 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B2338451 : Blo 1036608 2338451 := bstep (se 1 (by rfl) ⟨1753838, by rfl⟩ : syracuseStep 2338451 = 3507677) B3507677
theorem B2338505 : Blo 1036608 2338505 := bstep (se 2 (by rfl) ⟨876939, by rfl⟩ : syracuseStep 2338505 = 1753879) B1753879
theorem B3157789 : Blo 1036608 3157789 := bstep (se 3 (by rfl) ⟨592085, by rfl⟩ : syracuseStep 3157789 = 1184171) B1184171
theorem B3747883 : Blo 1036608 3747883 := bstep (se 1 (by rfl) ⟨2810912, by rfl⟩ : syracuseStep 3747883 = 5621825) B5621825
theorem B2666611 : Blo 1036608 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B4993331 : Blo 1036608 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B2339207 : Blo 1036608 2339207 := bstep (se 1 (by rfl) ⟨1754405, by rfl⟩ : syracuseStep 2339207 = 3508811) B3508811
theorem B19968403 : Blo 1036608 19968403 := bstep (se 1 (by rfl) ⟨14976302, by rfl⟩ : syracuseStep 19968403 = 29952605) B29952605
theorem B2339387 : Blo 1036608 2339387 := bstep (se 1 (by rfl) ⟨1754540, by rfl⟩ : syracuseStep 2339387 = 3509081) B3509081
theorem B2339513 : Blo 1036608 2339513 := bstep (se 2 (by rfl) ⟨877317, by rfl⟩ : syracuseStep 2339513 = 1754635) B1754635
theorem B1749775 : Blo 1036608 1749775 := bstep (se 1 (by rfl) ⟨1312331, by rfl⟩ : syracuseStep 1749775 = 2624663) B2624663
theorem B5256089 : Blo 1036608 5256089 := bstep (se 2 (by rfl) ⟨1971033, by rfl⟩ : syracuseStep 5256089 = 3942067) B3942067
theorem B2339855 : Blo 1036608 2339855 := bstep (se 1 (by rfl) ⟨1754891, by rfl⟩ : syracuseStep 2339855 = 3509783) B3509783
theorem B2339873 : Blo 1036608 2339873 := bstep (se 2 (by rfl) ⟨877452, by rfl⟩ : syracuseStep 2339873 = 1754905) B1754905
theorem B4732175 : Blo 1036608 4732175 := bstep (se 1 (by rfl) ⟨3549131, by rfl⟩ : syracuseStep 4732175 = 7098263) B7098263
theorem B3945743 : Blo 1036608 3945743 := bstep (se 1 (by rfl) ⟨2959307, by rfl⟩ : syracuseStep 3945743 = 5918615) B5918615
theorem B1750315 : Blo 1036608 1750315 := bstep (se 1 (by rfl) ⟨1312736, by rfl⟩ : syracuseStep 1750315 = 2625473) B2625473
theorem B2962747 : Blo 1036608 2962747 := bstep (se 1 (by rfl) ⟨2222060, by rfl⟩ : syracuseStep 2962747 = 4444121) B4444121
theorem B2340215 : Blo 1036608 2340215 := bstep (se 1 (by rfl) ⟨1755161, by rfl⟩ : syracuseStep 2340215 = 3510323) B3510323
theorem B3749267 : Blo 1036608 3749267 := bstep (se 1 (by rfl) ⟨2811950, by rfl⟩ : syracuseStep 3749267 = 5623901) B5623901
theorem B1750457 : Blo 1036608 1750457 := bstep (se 2 (by rfl) ⟨656421, by rfl⟩ : syracuseStep 1750457 = 1312843) B1312843
theorem B2340395 : Blo 1036608 2340395 := bstep (se 1 (by rfl) ⟨1755296, by rfl⟩ : syracuseStep 2340395 = 3510593) B3510593
theorem B25966453 : Blo 1036608 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B2340755 : Blo 1036608 2340755 := bstep (se 1 (by rfl) ⟨1755566, by rfl⟩ : syracuseStep 2340755 = 3511133) B3511133
theorem B2340809 : Blo 1036608 2340809 := bstep (se 2 (by rfl) ⟨877803, by rfl⟩ : syracuseStep 2340809 = 1755607) B1755607
theorem B4995101 : Blo 1036608 4995101 := bstep (se 3 (by rfl) ⟨936581, by rfl⟩ : syracuseStep 4995101 = 1873163) B1873163
theorem B1751159 : Blo 1036608 1751159 := bstep (se 1 (by rfl) ⟨1313369, by rfl⟩ : syracuseStep 1751159 = 2626739) B2626739
theorem B2668745 : Blo 1036608 2668745 := bstep (se 2 (by rfl) ⟨1000779, by rfl⟩ : syracuseStep 2668745 = 2001559) B2001559
theorem B2996509 : Blo 1036608 2996509 := bstep (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) B1123691
theorem B11811257 : Blo 1036608 11811257 := bstep (se 2 (by rfl) ⟨4429221, by rfl⟩ : syracuseStep 11811257 = 8858443) B8858443
theorem B1554935 : Blo 1036608 1554935 := bstep (se 1 (by rfl) ⟨1166201, by rfl⟩ : syracuseStep 1554935 = 2332403) B2332403
theorem B1554959 : Blo 1036608 1554959 := bstep (se 1 (by rfl) ⟨1166219, by rfl⟩ : syracuseStep 1554959 = 2332439) B2332439
theorem B1555001 : Blo 1036608 1555001 := bstep (se 2 (by rfl) ⟨583125, by rfl⟩ : syracuseStep 1555001 = 1166251) B1166251
theorem B1751611 : Blo 1036608 1751611 := bstep (se 1 (by rfl) ⟨1313708, by rfl⟩ : syracuseStep 1751611 = 2627417) B2627417
theorem B1555079 : Blo 1036608 1555079 := bstep (se 1 (by rfl) ⟨1166309, by rfl⟩ : syracuseStep 1555079 = 2332619) B2332619
theorem B1555115 : Blo 1036608 1555115 := bstep (se 1 (by rfl) ⟨1166336, by rfl⟩ : syracuseStep 1555115 = 2332673) B2332673
theorem B1555145 : Blo 1036608 1555145 := bstep (se 2 (by rfl) ⟨583179, by rfl⟩ : syracuseStep 1555145 = 1166359) B1166359
theorem B1751753 : Blo 1036608 1751753 := bstep (se 2 (by rfl) ⟨656907, by rfl⟩ : syracuseStep 1751753 = 1313815) B1313815
theorem B4733711 : Blo 1036608 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B1555259 : Blo 1036608 1555259 := bstep (se 1 (by rfl) ⟨1166444, by rfl⟩ : syracuseStep 1555259 = 2332889) B2332889
theorem B1555319 : Blo 1036608 1555319 := bstep (se 1 (by rfl) ⟨1166489, by rfl⟩ : syracuseStep 1555319 = 2332979) B2332979
theorem B3947399 : Blo 1036608 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B1555343 : Blo 1036608 1555343 := bstep (se 1 (by rfl) ⟨1166507, by rfl⟩ : syracuseStep 1555343 = 2333015) B2333015
theorem B1555385 : Blo 1036608 1555385 := bstep (se 2 (by rfl) ⟨583269, by rfl⟩ : syracuseStep 1555385 = 1166539) B1166539
theorem B4996025 : Blo 1036608 4996025 := bstep (se 2 (by rfl) ⟨1873509, by rfl⟩ : syracuseStep 4996025 = 3747019) B3747019
theorem B1555463 : Blo 1036608 1555463 := bstep (se 1 (by rfl) ⟨1166597, by rfl⟩ : syracuseStep 1555463 = 2333195) B2333195
theorem B3161099 : Blo 1036608 3161099 := bstep (se 1 (by rfl) ⟨2370824, by rfl⟩ : syracuseStep 3161099 = 4741649) B4741649
theorem B1555499 : Blo 1036608 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B1555529 : Blo 1036608 1555529 := bstep (se 2 (by rfl) ⟨583323, by rfl⟩ : syracuseStep 1555529 = 1166647) B1166647
theorem B3161207 : Blo 1036608 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B1555643 : Blo 1036608 1555643 := bstep (se 1 (by rfl) ⟨1166732, by rfl⟩ : syracuseStep 1555643 = 2333465) B2333465
theorem B1555703 : Blo 1036608 1555703 := bstep (se 1 (by rfl) ⟨1166777, by rfl⟩ : syracuseStep 1555703 = 2333555) B2333555
theorem B1555727 : Blo 1036608 1555727 := bstep (se 1 (by rfl) ⟨1166795, by rfl⟩ : syracuseStep 1555727 = 2333591) B2333591
theorem B1555769 : Blo 1036608 1555769 := bstep (se 2 (by rfl) ⟨583413, by rfl⟩ : syracuseStep 1555769 = 1166827) B1166827
theorem B1555847 : Blo 1036608 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1752455 : Blo 1036608 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B1555883 : Blo 1036608 1555883 := bstep (se 1 (by rfl) ⟨1166912, by rfl⟩ : syracuseStep 1555883 = 2333825) B2333825
theorem B5258681 : Blo 1036608 5258681 := bstep (se 2 (by rfl) ⟨1972005, by rfl⟩ : syracuseStep 5258681 = 3944011) B3944011
theorem B1555913 : Blo 1036608 1555913 := bstep (se 2 (by rfl) ⟨583467, by rfl⟩ : syracuseStep 1555913 = 1166935) B1166935
theorem B4996561 : Blo 1036608 4996561 := bstep (se 2 (by rfl) ⟨1873710, by rfl⟩ : syracuseStep 4996561 = 3747421) B3747421
theorem B1556027 : Blo 1036608 1556027 := bstep (se 1 (by rfl) ⟨1167020, by rfl⟩ : syracuseStep 1556027 = 2334041) B2334041
theorem B1621577 : Blo 1036608 1621577 := bstep (se 2 (by rfl) ⟨608091, by rfl⟩ : syracuseStep 1621577 = 1216183) B1216183
theorem B1556087 : Blo 1036608 1556087 := bstep (se 1 (by rfl) ⟨1167065, by rfl⟩ : syracuseStep 1556087 = 2334131) B2334131
theorem B1556111 : Blo 1036608 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1556153 : Blo 1036608 1556153 := bstep (se 2 (by rfl) ⟨583557, by rfl⟩ : syracuseStep 1556153 = 1167115) B1167115
theorem B1556231 : Blo 1036608 1556231 := bstep (se 1 (by rfl) ⟨1167173, by rfl⟩ : syracuseStep 1556231 = 2334347) B2334347
theorem B1556267 : Blo 1036608 1556267 := bstep (se 1 (by rfl) ⟨1167200, by rfl⟩ : syracuseStep 1556267 = 2334401) B2334401
theorem B1556297 : Blo 1036608 1556297 := bstep (se 2 (by rfl) ⟨583611, by rfl⟩ : syracuseStep 1556297 = 1167223) B1167223
theorem B1556411 : Blo 1036608 1556411 := bstep (se 1 (by rfl) ⟨1167308, by rfl⟩ : syracuseStep 1556411 = 2334617) B2334617
theorem B1556471 : Blo 1036608 1556471 := bstep (se 1 (by rfl) ⟨1167353, by rfl⟩ : syracuseStep 1556471 = 2334707) B2334707
theorem B1556495 : Blo 1036608 1556495 := bstep (se 1 (by rfl) ⟨1167371, by rfl⟩ : syracuseStep 1556495 = 2334743) B2334743
theorem B1753103 : Blo 1036608 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B1556537 : Blo 1036608 1556537 := bstep (se 2 (by rfl) ⟨583701, by rfl⟩ : syracuseStep 1556537 = 1167403) B1167403
theorem B1556615 : Blo 1036608 1556615 := bstep (se 1 (by rfl) ⟨1167461, by rfl⟩ : syracuseStep 1556615 = 2334923) B2334923
theorem B1556651 : Blo 1036608 1556651 := bstep (se 1 (by rfl) ⟨1167488, by rfl⟩ : syracuseStep 1556651 = 2334977) B2334977
theorem B1556681 : Blo 1036608 1556681 := bstep (se 2 (by rfl) ⟨583755, by rfl⟩ : syracuseStep 1556681 = 1167511) B1167511
theorem B1556795 : Blo 1036608 1556795 := bstep (se 1 (by rfl) ⟨1167596, by rfl⟩ : syracuseStep 1556795 = 2335193) B2335193
theorem B1556855 : Blo 1036608 1556855 := bstep (se 1 (by rfl) ⟨1167641, by rfl⟩ : syracuseStep 1556855 = 2335283) B2335283
theorem B5915015 : Blo 1036608 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B1556879 : Blo 1036608 1556879 := bstep (se 1 (by rfl) ⟨1167659, by rfl⟩ : syracuseStep 1556879 = 2335319) B2335319
theorem B1556921 : Blo 1036608 1556921 := bstep (se 2 (by rfl) ⟨583845, by rfl⟩ : syracuseStep 1556921 = 1167691) B1167691
theorem B1556999 : Blo 1036608 1556999 := bstep (se 1 (by rfl) ⟨1167749, by rfl⟩ : syracuseStep 1556999 = 2335499) B2335499
theorem B1557035 : Blo 1036608 1557035 := bstep (se 1 (by rfl) ⟨1167776, by rfl⟩ : syracuseStep 1557035 = 2335553) B2335553
theorem B1753643 : Blo 1036608 1753643 := bstep (se 1 (by rfl) ⟨1315232, by rfl⟩ : syracuseStep 1753643 = 2630465) B2630465
theorem B1557065 : Blo 1036608 1557065 := bstep (se 2 (by rfl) ⟨583899, by rfl⟩ : syracuseStep 1557065 = 1167799) B1167799
theorem B3949175 : Blo 1036608 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B1557179 : Blo 1036608 1557179 := bstep (se 1 (by rfl) ⟨1167884, by rfl⟩ : syracuseStep 1557179 = 2335769) B2335769
theorem B5259977 : Blo 1036608 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B1557239 : Blo 1036608 1557239 := bstep (se 1 (by rfl) ⟨1167929, by rfl⟩ : syracuseStep 1557239 = 2335859) B2335859
theorem B1557263 : Blo 1036608 1557263 := bstep (se 1 (by rfl) ⟨1167947, by rfl⟩ : syracuseStep 1557263 = 2335895) B2335895
theorem B1557305 : Blo 1036608 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1557383 : Blo 1036608 1557383 := bstep (se 1 (by rfl) ⟨1168037, by rfl⟩ : syracuseStep 1557383 = 2336075) B2336075
theorem B1557419 : Blo 1036608 1557419 := bstep (se 1 (by rfl) ⟨1168064, by rfl⟩ : syracuseStep 1557419 = 2336129) B2336129
theorem B1754041 : Blo 1036608 1754041 := bstep (se 2 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 1754041 = 1315531) B1315531
theorem B1557449 : Blo 1036608 1557449 := bstep (se 2 (by rfl) ⟨584043, by rfl⟩ : syracuseStep 1557449 = 1168087) B1168087
theorem B25248779 : Blo 1036608 25248779 := bstep (se 1 (by rfl) ⟨18936584, by rfl⟩ : syracuseStep 25248779 = 37873169) B37873169
theorem B1557563 : Blo 1036608 1557563 := bstep (se 1 (by rfl) ⟨1168172, by rfl⟩ : syracuseStep 1557563 = 2336345) B2336345
theorem B1557623 : Blo 1036608 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B3327095 : Blo 1036608 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B1557647 : Blo 1036608 1557647 := bstep (se 1 (by rfl) ⟨1168235, by rfl⟩ : syracuseStep 1557647 = 2336471) B2336471
theorem B1557689 : Blo 1036608 1557689 := bstep (se 2 (by rfl) ⟨584133, by rfl⟩ : syracuseStep 1557689 = 1168267) B1168267
theorem B1557767 : Blo 1036608 1557767 := bstep (se 1 (by rfl) ⟨1168325, by rfl⟩ : syracuseStep 1557767 = 2336651) B2336651
theorem B3327247 : Blo 1036608 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B1557803 : Blo 1036608 1557803 := bstep (se 1 (by rfl) ⟨1168352, by rfl⟩ : syracuseStep 1557803 = 2336705) B2336705
theorem B1557833 : Blo 1036608 1557833 := bstep (se 2 (by rfl) ⟨584187, by rfl⟩ : syracuseStep 1557833 = 1168375) B1168375
theorem B40519091 : Blo 1036608 40519091 := bstep (se 1 (by rfl) ⟨30389318, by rfl⟩ : syracuseStep 40519091 = 60778637) B60778637
theorem B1557947 : Blo 1036608 1557947 := bstep (se 1 (by rfl) ⟨1168460, by rfl⟩ : syracuseStep 1557947 = 2336921) B2336921
theorem B7980497 : Blo 1036608 7980497 := bstep (se 2 (by rfl) ⟨2992686, by rfl⟩ : syracuseStep 7980497 = 5985373) B5985373
theorem B1558007 : Blo 1036608 1558007 := bstep (se 1 (by rfl) ⟨1168505, by rfl⟩ : syracuseStep 1558007 = 2337011) B2337011
theorem B1558031 : Blo 1036608 1558031 := bstep (se 1 (by rfl) ⟨1168523, by rfl⟩ : syracuseStep 1558031 = 2337047) B2337047
theorem B1558073 : Blo 1036608 1558073 := bstep (se 2 (by rfl) ⟨584277, by rfl⟩ : syracuseStep 1558073 = 1168555) B1168555
theorem B4441661 : Blo 1036608 4441661 := bstep (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) B1665623
theorem B3950147 : Blo 1036608 3950147 := bstep (se 1 (by rfl) ⟨2962610, by rfl⟩ : syracuseStep 3950147 = 5925221) B5925221
theorem B1754743 : Blo 1036608 1754743 := bstep (se 1 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 1754743 = 2632115) B2632115
theorem B1558151 : Blo 1036608 1558151 := bstep (se 1 (by rfl) ⟨1168613, by rfl⟩ : syracuseStep 1558151 = 2337227) B2337227
theorem B1558187 : Blo 1036608 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B13321907 : Blo 1036608 13321907 := bstep (se 1 (by rfl) ⟨9991430, by rfl⟩ : syracuseStep 13321907 = 19982861) B19982861
theorem B7882433 : Blo 1036608 7882433 := bstep (se 2 (by rfl) ⟨2955912, by rfl⟩ : syracuseStep 7882433 = 5911825) B5911825
theorem B1558217 : Blo 1036608 1558217 := bstep (se 2 (by rfl) ⟨584331, by rfl⟩ : syracuseStep 1558217 = 1168663) B1168663
theorem B8865551 : Blo 1036608 8865551 := bstep (se 1 (by rfl) ⟨6649163, by rfl⟩ : syracuseStep 8865551 = 13298327) B13298327
theorem B1558331 : Blo 1036608 1558331 := bstep (se 1 (by rfl) ⟨1168748, by rfl⟩ : syracuseStep 1558331 = 2337497) B2337497
theorem B1754939 : Blo 1036608 1754939 := bstep (se 1 (by rfl) ⟨1316204, by rfl⟩ : syracuseStep 1754939 = 2632409) B2632409
theorem B1558391 : Blo 1036608 1558391 := bstep (se 1 (by rfl) ⟨1168793, by rfl⟩ : syracuseStep 1558391 = 2337587) B2337587
theorem B1558415 : Blo 1036608 1558415 := bstep (se 1 (by rfl) ⟨1168811, by rfl⟩ : syracuseStep 1558415 = 2337623) B2337623
theorem B4442003 : Blo 1036608 4442003 := bstep (se 1 (by rfl) ⟨3331502, by rfl⟩ : syracuseStep 4442003 = 6663005) B6663005
theorem B1558457 : Blo 1036608 1558457 := bstep (se 2 (by rfl) ⟨584421, by rfl⟩ : syracuseStep 1558457 = 1168843) B1168843
theorem B1558535 : Blo 1036608 1558535 := bstep (se 1 (by rfl) ⟨1168901, by rfl⟩ : syracuseStep 1558535 = 2337803) B2337803
theorem B3950603 : Blo 1036608 3950603 := bstep (se 1 (by rfl) ⟨2962952, by rfl⟩ : syracuseStep 3950603 = 5925905) B5925905
theorem B1558571 : Blo 1036608 1558571 := bstep (se 1 (by rfl) ⟨1168928, by rfl⟩ : syracuseStep 1558571 = 2337857) B2337857
theorem B1558601 : Blo 1036608 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B136726679 : Blo 1036608 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B1558715 : Blo 1036608 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B1755337 : Blo 1036608 1755337 := bstep (se 2 (by rfl) ⟨658251, by rfl⟩ : syracuseStep 1755337 = 1316503) B1316503
theorem B1558775 : Blo 1036608 1558775 := bstep (se 1 (by rfl) ⟨1169081, by rfl⟩ : syracuseStep 1558775 = 2338163) B2338163
theorem B1558799 : Blo 1036608 1558799 := bstep (se 1 (by rfl) ⟨1169099, by rfl⟩ : syracuseStep 1558799 = 2338199) B2338199
theorem B1558841 : Blo 1036608 1558841 := bstep (se 2 (by rfl) ⟨584565, by rfl⟩ : syracuseStep 1558841 = 1169131) B1169131
theorem B1558919 : Blo 1036608 1558919 := bstep (se 1 (by rfl) ⟨1169189, by rfl⟩ : syracuseStep 1558919 = 2338379) B2338379
theorem B1558955 : Blo 1036608 1558955 := bstep (se 1 (by rfl) ⟨1169216, by rfl⟩ : syracuseStep 1558955 = 2338433) B2338433
theorem B1558985 : Blo 1036608 1558985 := bstep (se 2 (by rfl) ⟨584619, by rfl⟩ : syracuseStep 1558985 = 1169239) B1169239
theorem B1559099 : Blo 1036608 1559099 := bstep (se 1 (by rfl) ⟨1169324, by rfl⟩ : syracuseStep 1559099 = 2338649) B2338649
theorem B1559159 : Blo 1036608 1559159 := bstep (se 1 (by rfl) ⟨1169369, by rfl⟩ : syracuseStep 1559159 = 2338739) B2338739
theorem B2214535 : Blo 1036608 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B1559183 : Blo 1036608 1559183 := bstep (se 1 (by rfl) ⟨1169387, by rfl⟩ : syracuseStep 1559183 = 2338775) B2338775
theorem B1559225 : Blo 1036608 1559225 := bstep (se 2 (by rfl) ⟨584709, by rfl⟩ : syracuseStep 1559225 = 1169419) B1169419
theorem B1559303 : Blo 1036608 1559303 := bstep (se 1 (by rfl) ⟨1169477, by rfl⟩ : syracuseStep 1559303 = 2338955) B2338955
theorem B1559339 : Blo 1036608 1559339 := bstep (se 1 (by rfl) ⟨1169504, by rfl⟩ : syracuseStep 1559339 = 2339009) B2339009
theorem B1559369 : Blo 1036608 1559369 := bstep (se 2 (by rfl) ⟨584763, by rfl⟩ : syracuseStep 1559369 = 1169527) B1169527
theorem B1166215 : Blo 1036608 1166215 := bstep (se 1 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 1166215 = 1749323) B1749323
theorem B1559483 : Blo 1036608 1559483 := bstep (se 1 (by rfl) ⟨1169612, by rfl⟩ : syracuseStep 1559483 = 2339225) B2339225
theorem B1559543 : Blo 1036608 1559543 := bstep (se 1 (by rfl) ⟨1169657, by rfl⟩ : syracuseStep 1559543 = 2339315) B2339315
theorem B1559567 : Blo 1036608 1559567 := bstep (se 1 (by rfl) ⟨1169675, by rfl⟩ : syracuseStep 1559567 = 2339351) B2339351
theorem B1559609 : Blo 1036608 1559609 := bstep (se 2 (by rfl) ⟨584853, by rfl⟩ : syracuseStep 1559609 = 1169707) B1169707
theorem B1166395 : Blo 1036608 1166395 := bstep (se 1 (by rfl) ⟨874796, by rfl⟩ : syracuseStep 1166395 = 1749593) B1749593
theorem B6310979 : Blo 1036608 6310979 := bstep (se 1 (by rfl) ⟨4733234, by rfl⟩ : syracuseStep 6310979 = 9466469) B9466469
theorem B1559687 : Blo 1036608 1559687 := bstep (se 1 (by rfl) ⟨1169765, by rfl⟩ : syracuseStep 1559687 = 2339531) B2339531
theorem B1559723 : Blo 1036608 1559723 := bstep (se 1 (by rfl) ⟨1169792, by rfl⟩ : syracuseStep 1559723 = 2339585) B2339585
theorem B1559753 : Blo 1036608 1559753 := bstep (se 2 (by rfl) ⟨584907, by rfl⟩ : syracuseStep 1559753 = 1169815) B1169815
theorem B1559867 : Blo 1036608 1559867 := bstep (se 1 (by rfl) ⟨1169900, by rfl⟩ : syracuseStep 1559867 = 2339801) B2339801
theorem B1559927 : Blo 1036608 1559927 := bstep (se 1 (by rfl) ⟨1169945, by rfl⟩ : syracuseStep 1559927 = 2339891) B2339891
theorem B1559951 : Blo 1036608 1559951 := bstep (se 1 (by rfl) ⟨1169963, by rfl⟩ : syracuseStep 1559951 = 2339927) B2339927
theorem B5623187 : Blo 1036608 5623187 := bstep (se 1 (by rfl) ⟨4217390, by rfl⟩ : syracuseStep 5623187 = 8434781) B8434781
theorem B1559993 : Blo 1036608 1559993 := bstep (se 2 (by rfl) ⟨584997, by rfl⟩ : syracuseStep 1559993 = 1169995) B1169995
theorem B11849165 : Blo 1036608 11849165 := bstep (se 3 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 11849165 = 4443437) B4443437
theorem B1560071 : Blo 1036608 1560071 := bstep (se 1 (by rfl) ⟨1170053, by rfl⟩ : syracuseStep 1560071 = 2340107) B2340107
theorem B1166863 : Blo 1036608 1166863 := bstep (se 1 (by rfl) ⟨875147, by rfl⟩ : syracuseStep 1166863 = 1750295) B1750295
theorem B1560107 : Blo 1036608 1560107 := bstep (se 1 (by rfl) ⟨1170080, by rfl⟩ : syracuseStep 1560107 = 2340161) B2340161
theorem B11226691 : Blo 1036608 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B1560137 : Blo 1036608 1560137 := bstep (se 2 (by rfl) ⟨585051, by rfl⟩ : syracuseStep 1560137 = 1170103) B1170103
theorem B2805367 : Blo 1036608 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B21286577 : Blo 1036608 21286577 := bstep (se 2 (by rfl) ⟨7982466, by rfl⟩ : syracuseStep 21286577 = 15964933) B15964933
theorem B1560251 : Blo 1036608 1560251 := bstep (se 1 (by rfl) ⟨1170188, by rfl⟩ : syracuseStep 1560251 = 2340377) B2340377
theorem B1560311 : Blo 1036608 1560311 := bstep (se 1 (by rfl) ⟨1170233, by rfl⟩ : syracuseStep 1560311 = 2340467) B2340467
theorem B1560335 : Blo 1036608 1560335 := bstep (se 1 (by rfl) ⟨1170251, by rfl⟩ : syracuseStep 1560335 = 2340503) B2340503
theorem B1560377 : Blo 1036608 1560377 := bstep (se 2 (by rfl) ⟨585141, by rfl⟩ : syracuseStep 1560377 = 1170283) B1170283
theorem B1560455 : Blo 1036608 1560455 := bstep (se 1 (by rfl) ⟨1170341, by rfl⟩ : syracuseStep 1560455 = 2340683) B2340683
theorem B4214681 : Blo 1036608 4214681 := bstep (se 2 (by rfl) ⟨1580505, by rfl⟩ : syracuseStep 4214681 = 3161011) B3161011
theorem B1560491 : Blo 1036608 1560491 := bstep (se 1 (by rfl) ⟨1170368, by rfl⟩ : syracuseStep 1560491 = 2340737) B2340737
theorem B1560521 : Blo 1036608 1560521 := bstep (se 2 (by rfl) ⟨585195, by rfl⟩ : syracuseStep 1560521 = 1170391) B1170391
theorem B1167367 : Blo 1036608 1167367 := bstep (se 1 (by rfl) ⟨875525, by rfl⟩ : syracuseStep 1167367 = 1751051) B1751051
theorem B1560635 : Blo 1036608 1560635 := bstep (se 1 (by rfl) ⟨1170476, by rfl⟩ : syracuseStep 1560635 = 2340953) B2340953
theorem B4214845 : Blo 1036608 4214845 := bstep (se 3 (by rfl) ⟨790283, by rfl⟩ : syracuseStep 4214845 = 1580567) B1580567
theorem B1560695 : Blo 1036608 1560695 := bstep (se 1 (by rfl) ⟨1170521, by rfl⟩ : syracuseStep 1560695 = 2341043) B2341043
theorem B1560719 : Blo 1036608 1560719 := bstep (se 1 (by rfl) ⟨1170539, by rfl⟩ : syracuseStep 1560719 = 2341079) B2341079
theorem B1560761 : Blo 1036608 1560761 := bstep (se 2 (by rfl) ⟨585285, by rfl⟩ : syracuseStep 1560761 = 1170571) B1170571
theorem B1167547 : Blo 1036608 1167547 := bstep (se 1 (by rfl) ⟨875660, by rfl⟩ : syracuseStep 1167547 = 1751321) B1751321
theorem B1560839 : Blo 1036608 1560839 := bstep (se 1 (by rfl) ⟨1170629, by rfl⟩ : syracuseStep 1560839 = 2341259) B2341259
theorem B1560875 : Blo 1036608 1560875 := bstep (se 1 (by rfl) ⟨1170656, by rfl⟩ : syracuseStep 1560875 = 2341313) B2341313
theorem B2216251 : Blo 1036608 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B1560905 : Blo 1036608 1560905 := bstep (se 2 (by rfl) ⟨585339, by rfl⟩ : syracuseStep 1560905 = 1170679) B1170679
theorem B1036679 : Blo 1036608 1036679 := bstep (se 1 (by rfl) ⟨777509, by rfl⟩ : syracuseStep 1036679 = 1555019) B1555019
theorem B1036687 : Blo 1036608 1036687 := bstep (se 1 (by rfl) ⟨777515, by rfl⟩ : syracuseStep 1036687 = 1555031) B1555031
theorem B1036731 : Blo 1036608 1036731 := bstep (se 1 (by rfl) ⟨777548, by rfl⟩ : syracuseStep 1036731 = 1555097) B1555097
theorem B12800477 : Blo 1036608 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B1036807 : Blo 1036608 1036807 := bstep (se 1 (by rfl) ⟨777605, by rfl⟩ : syracuseStep 1036807 = 1555211) B1555211
theorem B1036815 : Blo 1036608 1036815 := bstep (se 1 (by rfl) ⟨777611, by rfl⟩ : syracuseStep 1036815 = 1555223) B1555223
theorem B1036859 : Blo 1036608 1036859 := bstep (se 1 (by rfl) ⟨777644, by rfl⟩ : syracuseStep 1036859 = 1555289) B1555289
theorem B1036935 : Blo 1036608 1036935 := bstep (se 1 (by rfl) ⟨777701, by rfl⟩ : syracuseStep 1036935 = 1555403) B1555403
theorem B1036943 : Blo 1036608 1036943 := bstep (se 1 (by rfl) ⟨777707, by rfl⟩ : syracuseStep 1036943 = 1555415) B1555415
theorem B1168015 : Blo 1036608 1168015 := bstep (se 1 (by rfl) ⟨876011, by rfl⟩ : syracuseStep 1168015 = 1752023) B1752023
theorem B1036987 : Blo 1036608 1036987 := bstep (se 1 (by rfl) ⟨777740, by rfl⟩ : syracuseStep 1036987 = 1555481) B1555481
theorem B1037063 : Blo 1036608 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B1037071 : Blo 1036608 1037071 := bstep (se 1 (by rfl) ⟨777803, by rfl⟩ : syracuseStep 1037071 = 1555607) B1555607
theorem B2216747 : Blo 1036608 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B8409905 : Blo 1036608 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B1037115 : Blo 1036608 1037115 := bstep (se 1 (by rfl) ⟨777836, by rfl⟩ : syracuseStep 1037115 = 1555673) B1555673
theorem B1266491 : Blo 1036608 1266491 := bstep (se 1 (by rfl) ⟨949868, by rfl⟩ : syracuseStep 1266491 = 1899737) B1899737
theorem B2806589 : Blo 1036608 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B1037191 : Blo 1036608 1037191 := bstep (se 1 (by rfl) ⟨777893, by rfl⟩ : syracuseStep 1037191 = 1555787) B1555787
theorem B1037199 : Blo 1036608 1037199 := bstep (se 1 (by rfl) ⟨777899, by rfl⟩ : syracuseStep 1037199 = 1555799) B1555799
theorem B5919641 : Blo 1036608 5919641 := bstep (se 2 (by rfl) ⟨2219865, by rfl⟩ : syracuseStep 5919641 = 4439731) B4439731
theorem B1037243 : Blo 1036608 1037243 := bstep (se 1 (by rfl) ⟨777932, by rfl⟩ : syracuseStep 1037243 = 1555865) B1555865
theorem B1037319 : Blo 1036608 1037319 := bstep (se 1 (by rfl) ⟨777989, by rfl⟩ : syracuseStep 1037319 = 1555979) B1555979
theorem B7885835 : Blo 1036608 7885835 := bstep (se 1 (by rfl) ⟨5914376, by rfl⟩ : syracuseStep 7885835 = 11828753) B11828753
theorem B1037327 : Blo 1036608 1037327 := bstep (se 1 (by rfl) ⟨777995, by rfl⟩ : syracuseStep 1037327 = 1555991) B1555991
theorem B1037371 : Blo 1036608 1037371 := bstep (se 1 (by rfl) ⟨778028, by rfl⟩ : syracuseStep 1037371 = 1556057) B1556057
theorem B1037447 : Blo 1036608 1037447 := bstep (se 1 (by rfl) ⟨778085, by rfl⟩ : syracuseStep 1037447 = 1556171) B1556171
theorem B1168519 : Blo 1036608 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B1037455 : Blo 1036608 1037455 := bstep (se 1 (by rfl) ⟨778091, by rfl⟩ : syracuseStep 1037455 = 1556183) B1556183
theorem B1037499 : Blo 1036608 1037499 := bstep (se 1 (by rfl) ⟨778124, by rfl⟩ : syracuseStep 1037499 = 1556249) B1556249
theorem B1037575 : Blo 1036608 1037575 := bstep (se 1 (by rfl) ⟨778181, by rfl⟩ : syracuseStep 1037575 = 1556363) B1556363
theorem B1037583 : Blo 1036608 1037583 := bstep (se 1 (by rfl) ⟨778187, by rfl⟩ : syracuseStep 1037583 = 1556375) B1556375
theorem B1266959 : Blo 1036608 1266959 := bstep (se 1 (by rfl) ⟨950219, by rfl⟩ : syracuseStep 1266959 = 1900439) B1900439
theorem B1037627 : Blo 1036608 1037627 := bstep (se 1 (by rfl) ⟨778220, by rfl⟩ : syracuseStep 1037627 = 1556441) B1556441
theorem B1168699 : Blo 1036608 1168699 := bstep (se 1 (by rfl) ⟨876524, by rfl⟩ : syracuseStep 1168699 = 1753049) B1753049
theorem B1037703 : Blo 1036608 1037703 := bstep (se 1 (by rfl) ⟨778277, by rfl⟩ : syracuseStep 1037703 = 1556555) B1556555
theorem B1037711 : Blo 1036608 1037711 := bstep (se 1 (by rfl) ⟨778283, by rfl⟩ : syracuseStep 1037711 = 1556567) B1556567
theorem B1037755 : Blo 1036608 1037755 := bstep (se 1 (by rfl) ⟨778316, by rfl⟩ : syracuseStep 1037755 = 1556633) B1556633
theorem B1037831 : Blo 1036608 1037831 := bstep (se 1 (by rfl) ⟨778373, by rfl⟩ : syracuseStep 1037831 = 1556747) B1556747
theorem B1037839 : Blo 1036608 1037839 := bstep (se 1 (by rfl) ⟨778379, by rfl⟩ : syracuseStep 1037839 = 1556759) B1556759
theorem B2283041 : Blo 1036608 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B1037883 : Blo 1036608 1037883 := bstep (se 1 (by rfl) ⟨778412, by rfl⟩ : syracuseStep 1037883 = 1556825) B1556825
theorem B1037959 : Blo 1036608 1037959 := bstep (se 1 (by rfl) ⟨778469, by rfl⟩ : syracuseStep 1037959 = 1556939) B1556939
theorem B1037967 : Blo 1036608 1037967 := bstep (se 1 (by rfl) ⟨778475, by rfl⟩ : syracuseStep 1037967 = 1556951) B1556951
theorem B1038011 : Blo 1036608 1038011 := bstep (se 1 (by rfl) ⟨778508, by rfl⟩ : syracuseStep 1038011 = 1557017) B1557017
theorem B1038087 : Blo 1036608 1038087 := bstep (se 1 (by rfl) ⟨778565, by rfl⟩ : syracuseStep 1038087 = 1557131) B1557131
theorem B1038095 : Blo 1036608 1038095 := bstep (se 1 (by rfl) ⟨778571, by rfl⟩ : syracuseStep 1038095 = 1557143) B1557143
theorem B1169167 : Blo 1036608 1169167 := bstep (se 1 (by rfl) ⟨876875, by rfl⟩ : syracuseStep 1169167 = 1753751) B1753751
theorem B1038139 : Blo 1036608 1038139 := bstep (se 1 (by rfl) ⟨778604, by rfl⟩ : syracuseStep 1038139 = 1557209) B1557209
theorem B1201979 : Blo 1036608 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B1038215 : Blo 1036608 1038215 := bstep (se 1 (by rfl) ⟨778661, by rfl⟩ : syracuseStep 1038215 = 1557323) B1557323
theorem B1038223 : Blo 1036608 1038223 := bstep (se 1 (by rfl) ⟨778667, by rfl⟩ : syracuseStep 1038223 = 1557335) B1557335
theorem B9983897 : Blo 1036608 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B1038267 : Blo 1036608 1038267 := bstep (se 1 (by rfl) ⟨778700, by rfl⟩ : syracuseStep 1038267 = 1557401) B1557401
theorem B1038343 : Blo 1036608 1038343 := bstep (se 1 (by rfl) ⟨778757, by rfl⟩ : syracuseStep 1038343 = 1557515) B1557515
theorem B1038351 : Blo 1036608 1038351 := bstep (se 1 (by rfl) ⟨778763, by rfl⟩ : syracuseStep 1038351 = 1557527) B1557527
theorem B1038395 : Blo 1036608 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B8411197 : Blo 1036608 8411197 := bstep (se 3 (by rfl) ⟨1577099, by rfl⟩ : syracuseStep 8411197 = 3154199) B3154199
theorem B2250871 : Blo 1036608 2250871 := bstep (se 1 (by rfl) ⟨1688153, by rfl⟩ : syracuseStep 2250871 = 3376307) B3376307
theorem B1038471 : Blo 1036608 1038471 := bstep (se 1 (by rfl) ⟨778853, by rfl⟩ : syracuseStep 1038471 = 1557707) B1557707
theorem B1038479 : Blo 1036608 1038479 := bstep (se 1 (by rfl) ⟨778859, by rfl⟩ : syracuseStep 1038479 = 1557719) B1557719
theorem B6641837 : Blo 1036608 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B1038523 : Blo 1036608 1038523 := bstep (se 1 (by rfl) ⟨778892, by rfl⟩ : syracuseStep 1038523 = 1557785) B1557785
theorem B1038599 : Blo 1036608 1038599 := bstep (se 1 (by rfl) ⟨778949, by rfl⟩ : syracuseStep 1038599 = 1557899) B1557899
theorem B1169671 : Blo 1036608 1169671 := bstep (se 1 (by rfl) ⟨877253, by rfl⟩ : syracuseStep 1169671 = 1754507) B1754507
theorem B1038607 : Blo 1036608 1038607 := bstep (se 1 (by rfl) ⟨778955, by rfl⟩ : syracuseStep 1038607 = 1557911) B1557911
theorem B4741409 : Blo 1036608 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B1038651 : Blo 1036608 1038651 := bstep (se 1 (by rfl) ⟨778988, by rfl⟩ : syracuseStep 1038651 = 1557977) B1557977
theorem B1038727 : Blo 1036608 1038727 := bstep (se 1 (by rfl) ⟨779045, by rfl⟩ : syracuseStep 1038727 = 1558091) B1558091
theorem B1038735 : Blo 1036608 1038735 := bstep (se 1 (by rfl) ⟨779051, by rfl⟩ : syracuseStep 1038735 = 1558103) B1558103
theorem B5265809 : Blo 1036608 5265809 := bstep (se 2 (by rfl) ⟨1974678, by rfl⟩ : syracuseStep 5265809 = 3949357) B3949357
theorem B1038779 : Blo 1036608 1038779 := bstep (se 1 (by rfl) ⟨779084, by rfl⟩ : syracuseStep 1038779 = 1558169) B1558169
theorem B1169851 : Blo 1036608 1169851 := bstep (se 1 (by rfl) ⟨877388, by rfl⟩ : syracuseStep 1169851 = 1754777) B1754777
theorem B1038855 : Blo 1036608 1038855 := bstep (se 1 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 1038855 = 1558283) B1558283
theorem B1038863 : Blo 1036608 1038863 := bstep (se 1 (by rfl) ⟨779147, by rfl⟩ : syracuseStep 1038863 = 1558295) B1558295
theorem B1038907 : Blo 1036608 1038907 := bstep (se 1 (by rfl) ⟨779180, by rfl⟩ : syracuseStep 1038907 = 1558361) B1558361
theorem B1038983 : Blo 1036608 1038983 := bstep (se 1 (by rfl) ⟨779237, by rfl⟩ : syracuseStep 1038983 = 1558475) B1558475
theorem B1038991 : Blo 1036608 1038991 := bstep (se 1 (by rfl) ⟨779243, by rfl⟩ : syracuseStep 1038991 = 1558487) B1558487
theorem B1039035 : Blo 1036608 1039035 := bstep (se 1 (by rfl) ⟨779276, by rfl⟩ : syracuseStep 1039035 = 1558553) B1558553
theorem B95836877 : Blo 1036608 95836877 := bstep (se 3 (by rfl) ⟨17969414, by rfl⟩ : syracuseStep 95836877 = 35938829) B35938829
theorem B1039111 : Blo 1036608 1039111 := bstep (se 1 (by rfl) ⟨779333, by rfl⟩ : syracuseStep 1039111 = 1558667) B1558667
theorem B1039119 : Blo 1036608 1039119 := bstep (se 1 (by rfl) ⟨779339, by rfl⟩ : syracuseStep 1039119 = 1558679) B1558679
theorem B1039163 : Blo 1036608 1039163 := bstep (se 1 (by rfl) ⟨779372, by rfl⟩ : syracuseStep 1039163 = 1558745) B1558745
theorem B1039239 : Blo 1036608 1039239 := bstep (se 1 (by rfl) ⟨779429, by rfl⟩ : syracuseStep 1039239 = 1558859) B1558859
theorem B1039247 : Blo 1036608 1039247 := bstep (se 1 (by rfl) ⟨779435, by rfl⟩ : syracuseStep 1039247 = 1558871) B1558871
theorem B1170319 : Blo 1036608 1170319 := bstep (se 1 (by rfl) ⟨877739, by rfl⟩ : syracuseStep 1170319 = 1755479) B1755479
theorem B26598293 : Blo 1036608 26598293 := bstep (se 6 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 26598293 = 1246795) B1246795
theorem B7887779 : Blo 1036608 7887779 := bstep (se 1 (by rfl) ⟨5915834, by rfl⟩ : syracuseStep 7887779 = 11831669) B11831669
theorem B1661881 : Blo 1036608 1661881 := bstep (se 2 (by rfl) ⟨623205, by rfl⟩ : syracuseStep 1661881 = 1246411) B1246411
theorem B1039291 : Blo 1036608 1039291 := bstep (se 1 (by rfl) ⟨779468, by rfl⟩ : syracuseStep 1039291 = 1558937) B1558937
theorem B12639179 : Blo 1036608 12639179 := bstep (se 1 (by rfl) ⟨9479384, by rfl⟩ : syracuseStep 12639179 = 18958769) B18958769
theorem B1039367 : Blo 1036608 1039367 := bstep (se 1 (by rfl) ⟨779525, by rfl⟩ : syracuseStep 1039367 = 1559051) B1559051
theorem B1039375 : Blo 1036608 1039375 := bstep (se 1 (by rfl) ⟨779531, by rfl⟩ : syracuseStep 1039375 = 1559063) B1559063
theorem B2841659 : Blo 1036608 2841659 := bstep (se 1 (by rfl) ⟨2131244, by rfl⟩ : syracuseStep 2841659 = 4262489) B4262489
theorem B1039419 : Blo 1036608 1039419 := bstep (se 1 (by rfl) ⟨779564, by rfl⟩ : syracuseStep 1039419 = 1559129) B1559129
theorem B1039495 : Blo 1036608 1039495 := bstep (se 1 (by rfl) ⟨779621, by rfl⟩ : syracuseStep 1039495 = 1559243) B1559243
theorem B1039503 : Blo 1036608 1039503 := bstep (se 1 (by rfl) ⟨779627, by rfl⟩ : syracuseStep 1039503 = 1559255) B1559255
theorem B1039547 : Blo 1036608 1039547 := bstep (se 1 (by rfl) ⟨779660, by rfl⟩ : syracuseStep 1039547 = 1559321) B1559321
theorem B1039623 : Blo 1036608 1039623 := bstep (se 1 (by rfl) ⟨779717, by rfl⟩ : syracuseStep 1039623 = 1559435) B1559435
theorem B1039631 : Blo 1036608 1039631 := bstep (se 1 (by rfl) ⟨779723, by rfl⟩ : syracuseStep 1039631 = 1559447) B1559447
theorem B1039675 : Blo 1036608 1039675 := bstep (se 1 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 1039675 = 1559513) B1559513
theorem B1039751 : Blo 1036608 1039751 := bstep (se 1 (by rfl) ⟨779813, by rfl⟩ : syracuseStep 1039751 = 1559627) B1559627
theorem B1039759 : Blo 1036608 1039759 := bstep (se 1 (by rfl) ⟨779819, by rfl⟩ : syracuseStep 1039759 = 1559639) B1559639
theorem B1039803 : Blo 1036608 1039803 := bstep (se 1 (by rfl) ⟨779852, by rfl⟩ : syracuseStep 1039803 = 1559705) B1559705
theorem B1039879 : Blo 1036608 1039879 := bstep (se 1 (by rfl) ⟨779909, by rfl⟩ : syracuseStep 1039879 = 1559819) B1559819
theorem B1039887 : Blo 1036608 1039887 := bstep (se 1 (by rfl) ⟨779915, by rfl⟩ : syracuseStep 1039887 = 1559831) B1559831
theorem B1039931 : Blo 1036608 1039931 := bstep (se 1 (by rfl) ⟨779948, by rfl⟩ : syracuseStep 1039931 = 1559897) B1559897
theorem B1040007 : Blo 1036608 1040007 := bstep (se 1 (by rfl) ⟨780005, by rfl⟩ : syracuseStep 1040007 = 1560011) B1560011
theorem B1040015 : Blo 1036608 1040015 := bstep (se 1 (by rfl) ⟨780011, by rfl⟩ : syracuseStep 1040015 = 1560023) B1560023
theorem B2809529 : Blo 1036608 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B1040059 : Blo 1036608 1040059 := bstep (se 1 (by rfl) ⟨780044, by rfl⟩ : syracuseStep 1040059 = 1560089) B1560089
theorem B1040135 : Blo 1036608 1040135 := bstep (se 1 (by rfl) ⟨780101, by rfl⟩ : syracuseStep 1040135 = 1560203) B1560203
theorem B1040143 : Blo 1036608 1040143 := bstep (se 1 (by rfl) ⟨780107, by rfl⟩ : syracuseStep 1040143 = 1560215) B1560215
theorem B1040187 : Blo 1036608 1040187 := bstep (se 1 (by rfl) ⟨780140, by rfl⟩ : syracuseStep 1040187 = 1560281) B1560281
theorem B1040263 : Blo 1036608 1040263 := bstep (se 1 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 1040263 = 1560395) B1560395
theorem B1040271 : Blo 1036608 1040271 := bstep (se 1 (by rfl) ⟨780203, by rfl⟩ : syracuseStep 1040271 = 1560407) B1560407
theorem B1040315 : Blo 1036608 1040315 := bstep (se 1 (by rfl) ⟨780236, by rfl⟩ : syracuseStep 1040315 = 1560473) B1560473
theorem B1040391 : Blo 1036608 1040391 := bstep (se 1 (by rfl) ⟨780293, by rfl⟩ : syracuseStep 1040391 = 1560587) B1560587
theorem B1040399 : Blo 1036608 1040399 := bstep (se 1 (by rfl) ⟨780299, by rfl⟩ : syracuseStep 1040399 = 1560599) B1560599
theorem B1040443 : Blo 1036608 1040443 := bstep (se 1 (by rfl) ⟨780332, by rfl⟩ : syracuseStep 1040443 = 1560665) B1560665
theorem B5988419 : Blo 1036608 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B1663111 : Blo 1036608 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B1040519 : Blo 1036608 1040519 := bstep (se 1 (by rfl) ⟨780389, by rfl⟩ : syracuseStep 1040519 = 1560779) B1560779
theorem B1040527 : Blo 1036608 1040527 := bstep (se 1 (by rfl) ⟨780395, by rfl⟩ : syracuseStep 1040527 = 1560791) B1560791
theorem B5922989 : Blo 1036608 5922989 := bstep (se 3 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 5922989 = 2221121) B2221121
theorem B1040571 : Blo 1036608 1040571 := bstep (se 1 (by rfl) ⟨780428, by rfl⟩ : syracuseStep 1040571 = 1560857) B1560857
theorem B1663291 : Blo 1036608 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B9986435 : Blo 1036608 9986435 := bstep (se 1 (by rfl) ⟨7489826, by rfl⟩ : syracuseStep 9986435 = 14979653) B14979653
theorem B5267915 : Blo 1036608 5267915 := bstep (se 1 (by rfl) ⟨3950936, by rfl⟩ : syracuseStep 5267915 = 7901873) B7901873
theorem B3498767 : Blo 1036608 3498767 := bstep (se 1 (by rfl) ⟨2624075, by rfl⟩ : syracuseStep 3498767 = 5248151) B5248151
theorem B4744145 : Blo 1036608 4744145 := bstep (se 2 (by rfl) ⟨1779054, by rfl⟩ : syracuseStep 4744145 = 3558109) B3558109
theorem B3499037 : Blo 1036608 3499037 := bstep (se 3 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 3499037 = 1312139) B1312139
theorem B1401991 : Blo 1036608 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B8414381 : Blo 1036608 8414381 := bstep (se 3 (by rfl) ⟨1577696, by rfl⟩ : syracuseStep 8414381 = 3155393) B3155393
theorem B1664201 : Blo 1036608 1664201 := bstep (se 2 (by rfl) ⟨624075, by rfl⟩ : syracuseStep 1664201 = 1248151) B1248151
theorem B1893665 : Blo 1036608 1893665 := bstep (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) B1420249
theorem B31974689 : Blo 1036608 31974689 := bstep (se 2 (by rfl) ⟨11990508, by rfl⟩ : syracuseStep 31974689 = 23981017) B23981017
theorem B7890209 : Blo 1036608 7890209 := bstep (se 2 (by rfl) ⟨2958828, by rfl⟩ : syracuseStep 7890209 = 5917657) B5917657
theorem B1402169 : Blo 1036608 1402169 := bstep (se 2 (by rfl) ⟨525813, by rfl⟩ : syracuseStep 1402169 = 1051627) B1051627
theorem B8873549 : Blo 1036608 8873549 := bstep (se 3 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 8873549 = 3327581) B3327581
theorem B2222095 : Blo 1036608 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B7891181 : Blo 1036608 7891181 := bstep (se 3 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 7891181 = 2959193) B2959193
theorem B8874299 : Blo 1036608 8874299 := bstep (se 1 (by rfl) ⟨6655724, by rfl⟩ : syracuseStep 8874299 = 13311449) B13311449
theorem B6318425 : Blo 1036608 6318425 := bstep (se 2 (by rfl) ⟨2369409, by rfl⟩ : syracuseStep 6318425 = 4738819) B4738819
theorem B2222471 : Blo 1036608 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B3500441 : Blo 1036608 3500441 := bstep (se 2 (by rfl) ⟨1312665, by rfl⟩ : syracuseStep 3500441 = 2625331) B2625331
theorem B7498763 : Blo 1036608 7498763 := bstep (se 1 (by rfl) ⟨5624072, by rfl⟩ : syracuseStep 7498763 = 11248145) B11248145
theorem B3501143 : Blo 1036608 3501143 := bstep (se 1 (by rfl) ⟨2625857, by rfl⟩ : syracuseStep 3501143 = 5251715) B5251715
theorem B6319397 : Blo 1036608 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B12610961 : Blo 1036608 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B1666489 : Blo 1036608 1666489 := bstep (se 2 (by rfl) ⟨624933, by rfl⟩ : syracuseStep 1666489 = 1249867) B1249867
theorem B3501629 : Blo 1036608 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B19951181 : Blo 1036608 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B1666745 : Blo 1036608 1666745 := bstep (se 2 (by rfl) ⟨625029, by rfl⟩ : syracuseStep 1666745 = 1250059) B1250059
theorem B5336833 : Blo 1036608 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B8875939 : Blo 1036608 8875939 := bstep (se 1 (by rfl) ⟨6656954, by rfl⟩ : syracuseStep 8875939 = 13313909) B13313909
theorem B7893125 : Blo 1036608 7893125 := bstep (se 4 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 7893125 = 1479961) B1479961
theorem B136376945 : Blo 1036608 136376945 := bstep (se 2 (by rfl) ⟨51141354, by rfl⟩ : syracuseStep 136376945 = 102282709) B102282709
theorem B1110791 : Blo 1036608 1110791 := bstep (se 1 (by rfl) ⟨833093, by rfl⟩ : syracuseStep 1110791 = 1666187) B1666187
theorem B3503033 : Blo 1036608 3503033 := bstep (se 2 (by rfl) ⟨1313637, by rfl⟩ : syracuseStep 3503033 = 2627275) B2627275
theorem B23950727 : Blo 1036608 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B3503627 : Blo 1036608 3503627 := bstep (se 1 (by rfl) ⟨2627720, by rfl⟩ : syracuseStep 3503627 = 5255441) B5255441
theorem B3503735 : Blo 1036608 3503735 := bstep (se 1 (by rfl) ⟨2627801, by rfl⟩ : syracuseStep 3503735 = 5255603) B5255603
theorem B5994499 : Blo 1036608 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B4388951 : Blo 1036608 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B3504329 : Blo 1036608 3504329 := bstep (se 2 (by rfl) ⟨1314123, by rfl⟩ : syracuseStep 3504329 = 2628247) B2628247
theorem B7895555 : Blo 1036608 7895555 := bstep (se 1 (by rfl) ⟨5921666, by rfl⟩ : syracuseStep 7895555 = 11843333) B11843333
theorem B3505031 : Blo 1036608 3505031 := bstep (se 1 (by rfl) ⟨2628773, by rfl⟩ : syracuseStep 3505031 = 5257547) B5257547
theorem B10648709 : Blo 1036608 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B7109869 : Blo 1036608 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B3505409 : Blo 1036608 3505409 := bstep (se 2 (by rfl) ⟨1314528, by rfl⟩ : syracuseStep 3505409 = 2629057) B2629057
theorem B42695981 : Blo 1036608 42695981 := bstep (se 3 (by rfl) ⟨8005496, by rfl⟩ : syracuseStep 42695981 = 16010993) B16010993
theorem B8420867 : Blo 1036608 8420867 := bstep (se 1 (by rfl) ⟨6315650, by rfl⟩ : syracuseStep 8420867 = 12631301) B12631301
theorem B1245623 : Blo 1036608 1245623 := bstep (se 1 (by rfl) ⟨934217, by rfl⟩ : syracuseStep 1245623 = 1868435) B1868435
theorem B16875985 : Blo 1036608 16875985 := bstep (se 2 (by rfl) ⟨6328494, by rfl⟩ : syracuseStep 16875985 = 12656989) B12656989
theorem B3506651 : Blo 1036608 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B14221925 : Blo 1036608 14221925 := bstep (se 4 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 14221925 = 2666611) B2666611
theorem B15205427 : Blo 1036608 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B8881271 : Blo 1036608 8881271 := bstep (se 1 (by rfl) ⟨6660953, by rfl⟩ : syracuseStep 8881271 = 13321907) B13321907
theorem B3507353 : Blo 1036608 3507353 := bstep (se 2 (by rfl) ⟨1315257, by rfl⟩ : syracuseStep 3507353 = 2630515) B2630515
theorem B3737303 : Blo 1036608 3737303 := bstep (se 1 (by rfl) ⟨2802977, by rfl⟩ : syracuseStep 3737303 = 5605955) B5605955
theorem B3737387 : Blo 1036608 3737387 := bstep (se 1 (by rfl) ⟨2803040, by rfl⟩ : syracuseStep 3737387 = 5606081) B5606081
theorem B7997251 : Blo 1036608 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B3377309 : Blo 1036608 3377309 := bstep (se 3 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 3377309 = 1266491) B1266491
theorem B7899443 : Blo 1036608 7899443 := bstep (se 1 (by rfl) ⟨5924582, by rfl⟩ : syracuseStep 7899443 = 11849165) B11849165
theorem B3508541 : Blo 1036608 3508541 := bstep (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) B1315703
theorem B14191051 : Blo 1036608 14191051 := bstep (se 1 (by rfl) ⟨10643288, by rfl⟩ : syracuseStep 14191051 = 21286577) B21286577
theorem B6654473 : Blo 1036608 6654473 := bstep (se 2 (by rfl) ⟨2495427, by rfl⟩ : syracuseStep 6654473 = 4990855) B4990855
theorem B3509405 : Blo 1036608 3509405 := bstep (se 3 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 3509405 = 1316027) B1316027
theorem B2624683 : Blo 1036608 2624683 := bstep (se 1 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 2624683 = 3937025) B3937025
theorem B5606603 : Blo 1036608 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B1969363 : Blo 1036608 1969363 := bstep (se 1 (by rfl) ⟨1477022, by rfl⟩ : syracuseStep 1969363 = 2954045) B2954045
theorem B1871059 : Blo 1036608 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B3378557 : Blo 1036608 3378557 := bstep (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) B1266959
theorem B5049773 : Blo 1036608 5049773 := bstep (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) B1893665
theorem B1969591 : Blo 1036608 1969591 := bstep (se 1 (by rfl) ⟨1477193, by rfl⟩ : syracuseStep 1969591 = 2954387) B2954387
theorem B2624987 : Blo 1036608 2624987 := bstep (se 1 (by rfl) ⟨1968740, by rfl⟩ : syracuseStep 2624987 = 3937481) B3937481
theorem B3739117 : Blo 1036608 3739117 := bstep (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) B1402169
theorem B2952713 : Blo 1036608 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B2494091 : Blo 1036608 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B3509945 : Blo 1036608 3509945 := bstep (se 2 (by rfl) ⟨1316229, by rfl⟩ : syracuseStep 3509945 = 2632459) B2632459
theorem B6655931 : Blo 1036608 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B1970183 : Blo 1036608 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B4427891 : Blo 1036608 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B3510539 : Blo 1036608 3510539 := bstep (se 1 (by rfl) ⟨2632904, by rfl⟩ : syracuseStep 3510539 = 5265809) B5265809
theorem B3510809 : Blo 1036608 3510809 := bstep (se 2 (by rfl) ⟨1316553, by rfl⟩ : syracuseStep 3510809 = 2633107) B2633107
theorem B1577551 : Blo 1036608 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B17732195 : Blo 1036608 17732195 := bstep (se 1 (by rfl) ⟨13299146, by rfl⟩ : syracuseStep 17732195 = 26598293) B26598293
theorem B8426119 : Blo 1036608 8426119 := bstep (se 1 (by rfl) ⟨6319589, by rfl⟩ : syracuseStep 8426119 = 12639179) B12639179
theorem B2495225 : Blo 1036608 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B3740489 : Blo 1036608 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B1971049 : Blo 1036608 1971049 := bstep (se 2 (by rfl) ⟨739143, by rfl⟩ : syracuseStep 1971049 = 1478287) B1478287
theorem B2626465 : Blo 1036608 2626465 := bstep (se 2 (by rfl) ⟨984924, by rfl⟩ : syracuseStep 2626465 = 1969849) B1969849
theorem B1315759 : Blo 1036608 1315759 := bstep (se 1 (by rfl) ⟨986819, by rfl⟩ : syracuseStep 1315759 = 1973639) B1973639
theorem B3937207 : Blo 1036608 3937207 := bstep (se 1 (by rfl) ⟨2952905, by rfl⟩ : syracuseStep 3937207 = 5905811) B5905811
theorem B2954171 : Blo 1036608 2954171 := bstep (se 1 (by rfl) ⟨2215628, by rfl⟩ : syracuseStep 2954171 = 4431257) B4431257
theorem B7115777 : Blo 1036608 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B1971209 : Blo 1036608 1971209 := bstep (se 2 (by rfl) ⟨739203, by rfl⟩ : syracuseStep 1971209 = 1478407) B1478407
theorem B1873019 : Blo 1036608 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B11834585 : Blo 1036608 11834585 := bstep (se 2 (by rfl) ⟨4437969, by rfl⟩ : syracuseStep 11834585 = 8875939) B8875939
theorem B3937679 : Blo 1036608 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B5248475 : Blo 1036608 5248475 := bstep (se 1 (by rfl) ⟨3936356, by rfl⟩ : syracuseStep 5248475 = 7872713) B7872713
theorem B3741223 : Blo 1036608 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B6657623 : Blo 1036608 6657623 := bstep (se 1 (by rfl) ⟨4993217, by rfl⟩ : syracuseStep 6657623 = 9986435) B9986435
theorem B3511943 : Blo 1036608 3511943 := bstep (se 1 (by rfl) ⟨2633957, by rfl⟩ : syracuseStep 3511943 = 5267915) B5267915
theorem B3511997 : Blo 1036608 3511997 := bstep (se 3 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 3511997 = 1316999) B1316999
theorem B2332511 : Blo 1036608 2332511 := bstep (se 1 (by rfl) ⟨1749383, by rfl⟩ : syracuseStep 2332511 = 3498767) B3498767
theorem B5248961 : Blo 1036608 5248961 := bstep (se 2 (by rfl) ⟨1968360, by rfl⟩ : syracuseStep 5248961 = 3936721) B3936721
theorem B19929037 : Blo 1036608 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B1316827 : Blo 1036608 1316827 := bstep (se 1 (by rfl) ⟨987620, by rfl⟩ : syracuseStep 1316827 = 1975241) B1975241
theorem B2332691 : Blo 1036608 2332691 := bstep (se 1 (by rfl) ⟨1749518, by rfl⟩ : syracuseStep 2332691 = 3499037) B3499037
theorem B7477285 : Blo 1036608 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B5609587 : Blo 1036608 5609587 := bstep (se 1 (by rfl) ⟨4207190, by rfl⟩ : syracuseStep 5609587 = 8414381) B8414381
theorem B2333033 : Blo 1036608 2333033 := bstep (se 2 (by rfl) ⟨874887, by rfl⟩ : syracuseStep 2333033 = 1749775) B1749775
theorem B3938665 : Blo 1036608 3938665 := bstep (se 2 (by rfl) ⟨1476999, by rfl⟩ : syracuseStep 3938665 = 2953999) B2953999
theorem B19995011 : Blo 1036608 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B1972667 : Blo 1036608 1972667 := bstep (se 1 (by rfl) ⟨1479500, by rfl⟩ : syracuseStep 1972667 = 2959001) B2959001
theorem B3938939 : Blo 1036608 3938939 := bstep (se 1 (by rfl) ⟨2954204, by rfl⟩ : syracuseStep 3938939 = 5908409) B5908409
theorem B1973099 : Blo 1036608 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B1973153 : Blo 1036608 1973153 := bstep (se 2 (by rfl) ⟨739932, by rfl⟩ : syracuseStep 1973153 = 1479865) B1479865
theorem B1481647 : Blo 1036608 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B2333627 : Blo 1036608 2333627 := bstep (se 1 (by rfl) ⟨1750220, by rfl⟩ : syracuseStep 2333627 = 3500441) B3500441
theorem B1776647 : Blo 1036608 1776647 := bstep (se 1 (by rfl) ⟨1332485, by rfl⟩ : syracuseStep 1776647 = 2664971) B2664971
theorem B2333753 : Blo 1036608 2333753 := bstep (se 2 (by rfl) ⟨875157, by rfl⟩ : syracuseStep 2333753 = 1750315) B1750315
theorem B2334095 : Blo 1036608 2334095 := bstep (se 1 (by rfl) ⟨1750571, by rfl⟩ : syracuseStep 2334095 = 3501143) B3501143
theorem B2629007 : Blo 1036608 2629007 := bstep (se 1 (by rfl) ⟨1971755, by rfl⟩ : syracuseStep 2629007 = 3943511) B3943511
theorem B2334419 : Blo 1036608 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B2629331 : Blo 1036608 2629331 := bstep (se 1 (by rfl) ⟨1971998, by rfl⟩ : syracuseStep 2629331 = 3943997) B3943997
theorem B11214929 : Blo 1036608 11214929 := bstep (se 2 (by rfl) ⟨4205598, by rfl⟩ : syracuseStep 11214929 = 8411197) B8411197
theorem B5251229 : Blo 1036608 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B59875685 : Blo 1036608 59875685 := bstep (se 4 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 59875685 = 11226691) B11226691
theorem B1974793 : Blo 1036608 1974793 := bstep (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) B1481095
theorem B2335355 : Blo 1036608 2335355 := bstep (se 1 (by rfl) ⟨1751516, by rfl⟩ : syracuseStep 2335355 = 3503033) B3503033
theorem B2335481 : Blo 1036608 2335481 := bstep (se 2 (by rfl) ⟨875805, by rfl⟩ : syracuseStep 2335481 = 1751611) B1751611
theorem B16851725 : Blo 1036608 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B3154783 : Blo 1036608 3154783 := bstep (se 1 (by rfl) ⟨2366087, by rfl⟩ : syracuseStep 3154783 = 4732175) B4732175
theorem B2630495 : Blo 1036608 2630495 := bstep (se 1 (by rfl) ⟨1972871, by rfl⟩ : syracuseStep 2630495 = 3945743) B3945743
theorem B15967151 : Blo 1036608 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B2499511 : Blo 1036608 2499511 := bstep (se 1 (by rfl) ⟨1874633, by rfl⟩ : syracuseStep 2499511 = 3749267) B3749267
theorem B2335751 : Blo 1036608 2335751 := bstep (se 1 (by rfl) ⟨1751813, by rfl⟩ : syracuseStep 2335751 = 3503627) B3503627
theorem B2335823 : Blo 1036608 2335823 := bstep (se 1 (by rfl) ⟨1751867, by rfl⟩ : syracuseStep 2335823 = 3503735) B3503735
theorem B53880025 : Blo 1036608 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B2925967 : Blo 1036608 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B5252525 : Blo 1036608 5252525 := bstep (se 3 (by rfl) ⟨984848, by rfl⟩ : syracuseStep 5252525 = 1969697) B1969697
theorem B2336219 : Blo 1036608 2336219 := bstep (se 1 (by rfl) ⟨1752164, by rfl⟩ : syracuseStep 2336219 = 3504329) B3504329
theorem B1779163 : Blo 1036608 1779163 := bstep (se 1 (by rfl) ⟨1334372, by rfl⟩ : syracuseStep 1779163 = 2668745) B2668745
theorem B7874171 : Blo 1036608 7874171 := bstep (se 1 (by rfl) ⟨5905628, by rfl⟩ : syracuseStep 7874171 = 11811257) B11811257
theorem B9479825 : Blo 1036608 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B13510489 : Blo 1036608 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B3155807 : Blo 1036608 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B2336687 : Blo 1036608 2336687 := bstep (se 1 (by rfl) ⟨1752515, by rfl⟩ : syracuseStep 2336687 = 3505031) B3505031
theorem B2631599 : Blo 1036608 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B6662081 : Blo 1036608 6662081 := bstep (se 2 (by rfl) ⟨2498280, by rfl⟩ : syracuseStep 6662081 = 4996561) B4996561
theorem B2107399 : Blo 1036608 2107399 := bstep (se 1 (by rfl) ⟨1580549, by rfl⟩ : syracuseStep 2107399 = 3161099) B3161099
theorem B2107471 : Blo 1036608 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B3942553 : Blo 1036608 3942553 := bstep (se 2 (by rfl) ⟨1478457, by rfl⟩ : syracuseStep 3942553 = 2956915) B2956915
theorem B2336939 : Blo 1036608 2336939 := bstep (se 1 (by rfl) ⟨1752704, by rfl⟩ : syracuseStep 2336939 = 3505409) B3505409
theorem B5613911 : Blo 1036608 5613911 := bstep (se 1 (by rfl) ⟨4210433, by rfl⟩ : syracuseStep 5613911 = 8420867) B8420867
theorem B3942857 : Blo 1036608 3942857 := bstep (se 2 (by rfl) ⟨1478571, by rfl⟩ : syracuseStep 3942857 = 2957143) B2957143
theorem B2337479 : Blo 1036608 2337479 := bstep (se 1 (by rfl) ⟨1753109, by rfl⟩ : syracuseStep 2337479 = 3506219) B3506219
theorem B3943343 : Blo 1036608 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B21605303 : Blo 1036608 21605303 := bstep (se 1 (by rfl) ⟨16203977, by rfl⟩ : syracuseStep 21605303 = 32407955) B32407955
theorem B5254145 : Blo 1036608 5254145 := bstep (se 2 (by rfl) ⟨1970304, by rfl⟩ : syracuseStep 5254145 = 3940609) B3940609
theorem B8432707 : Blo 1036608 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B2632783 : Blo 1036608 2632783 := bstep (se 1 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 2632783 = 3949175) B3949175
theorem B12004645 : Blo 1036608 12004645 := bstep (se 4 (by rfl) ⟨1125435, by rfl⟩ : syracuseStep 12004645 = 2250871) B2250871
theorem B13315549 : Blo 1036608 13315549 := bstep (se 3 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 13315549 = 4993331) B4993331
theorem B2338343 : Blo 1036608 2338343 := bstep (se 1 (by rfl) ⟨1753757, by rfl⟩ : syracuseStep 2338343 = 3507515) B3507515
theorem B27012727 : Blo 1036608 27012727 := bstep (se 1 (by rfl) ⟨20259545, by rfl⟩ : syracuseStep 27012727 = 40519091) B40519091
theorem B5320331 : Blo 1036608 5320331 := bstep (se 1 (by rfl) ⟨3990248, by rfl⟩ : syracuseStep 5320331 = 7980497) B7980497
theorem B2961107 : Blo 1036608 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B2633431 : Blo 1036608 2633431 := bstep (se 1 (by rfl) ⟨1975073, by rfl⟩ : syracuseStep 2633431 = 3950147) B3950147
theorem B5254955 : Blo 1036608 5254955 := bstep (se 1 (by rfl) ⟨3941216, by rfl⟩ : syracuseStep 5254955 = 7882433) B7882433
theorem B5910367 : Blo 1036608 5910367 := bstep (se 1 (by rfl) ⟨4432775, by rfl⟩ : syracuseStep 5910367 = 8865551) B8865551
theorem B6664031 : Blo 1036608 6664031 := bstep (se 1 (by rfl) ⟨4998023, by rfl⟩ : syracuseStep 6664031 = 9996047) B9996047
theorem B2338667 : Blo 1036608 2338667 := bstep (se 1 (by rfl) ⟨1754000, by rfl⟩ : syracuseStep 2338667 = 3508001) B3508001
theorem B2338721 : Blo 1036608 2338721 := bstep (se 2 (by rfl) ⟨877020, by rfl⟩ : syracuseStep 2338721 = 1754041) B1754041
theorem B2961335 : Blo 1036608 2961335 := bstep (se 1 (by rfl) ⟨2221001, by rfl⟩ : syracuseStep 2961335 = 4442003) B4442003
theorem B2633735 : Blo 1036608 2633735 := bstep (se 1 (by rfl) ⟨1975301, by rfl⟩ : syracuseStep 2633735 = 3950603) B3950603
theorem B2339063 : Blo 1036608 2339063 := bstep (se 1 (by rfl) ⟨1754297, by rfl⟩ : syracuseStep 2339063 = 3508595) B3508595
theorem B1749343 : Blo 1036608 1749343 := bstep (se 1 (by rfl) ⟨1312007, by rfl⟩ : syracuseStep 1749343 = 2624015) B2624015
theorem B1749431 : Blo 1036608 1749431 := bstep (se 1 (by rfl) ⟨1312073, by rfl⟩ : syracuseStep 1749431 = 2624147) B2624147
theorem B3944969 : Blo 1036608 3944969 := bstep (se 2 (by rfl) ⟨1479363, by rfl⟩ : syracuseStep 3944969 = 2958727) B2958727
theorem B2962109 : Blo 1036608 2962109 := bstep (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) B1110791
theorem B4207319 : Blo 1036608 4207319 := bstep (se 1 (by rfl) ⟨3155489, by rfl⟩ : syracuseStep 4207319 = 6310979) B6310979
theorem B5911325 : Blo 1036608 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B2339657 : Blo 1036608 2339657 := bstep (se 2 (by rfl) ⟨877371, by rfl⟩ : syracuseStep 2339657 = 1754743) B1754743
theorem B1750025 : Blo 1036608 1750025 := bstep (se 2 (by rfl) ⟨656259, by rfl⟩ : syracuseStep 1750025 = 1312519) B1312519
theorem B1750187 : Blo 1036608 1750187 := bstep (se 1 (by rfl) ⟨1312640, by rfl⟩ : syracuseStep 1750187 = 2625281) B2625281
theorem B2962793 : Blo 1036608 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1684919 : Blo 1036608 1684919 := bstep (se 1 (by rfl) ⟨1263689, by rfl⟩ : syracuseStep 1684919 = 2527379) B2527379
theorem B3159577 : Blo 1036608 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B1750585 : Blo 1036608 1750585 := bstep (se 2 (by rfl) ⟨656469, by rfl⟩ : syracuseStep 1750585 = 1312939) B1312939
theorem B2340449 : Blo 1036608 2340449 := bstep (se 2 (by rfl) ⟨877668, by rfl⟩ : syracuseStep 2340449 = 1755337) B1755337
theorem B1750727 : Blo 1036608 1750727 := bstep (se 1 (by rfl) ⟨1313045, by rfl⟩ : syracuseStep 1750727 = 2626091) B2626091
theorem B1750889 : Blo 1036608 1750889 := bstep (se 2 (by rfl) ⟨656583, by rfl⟩ : syracuseStep 1750889 = 1313167) B1313167
theorem B2340791 : Blo 1036608 2340791 := bstep (se 1 (by rfl) ⟨1755593, by rfl⟩ : syracuseStep 2340791 = 3511187) B3511187
theorem B3946427 : Blo 1036608 3946427 := bstep (se 1 (by rfl) ⟨2959820, by rfl⟩ : syracuseStep 3946427 = 5919641) B5919641
theorem B5257223 : Blo 1036608 5257223 := bstep (se 1 (by rfl) ⟨3942917, by rfl⟩ : syracuseStep 5257223 = 7885835) B7885835
theorem B1751287 : Blo 1036608 1751287 := bstep (se 1 (by rfl) ⟨1313465, by rfl⟩ : syracuseStep 1751287 = 2626931) B2626931
theorem B1522027 : Blo 1036608 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B1751483 : Blo 1036608 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B5257709 : Blo 1036608 5257709 := bstep (se 3 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 5257709 = 1971641) B1971641
theorem B1554953 : Blo 1036608 1554953 := bstep (se 2 (by rfl) ⟨583107, by rfl⟩ : syracuseStep 1554953 = 1166215) B1166215
theorem B1554983 : Blo 1036608 1554983 := bstep (se 1 (by rfl) ⟨1166237, by rfl⟩ : syracuseStep 1554983 = 2332475) B2332475
theorem B1751591 : Blo 1036608 1751591 := bstep (se 1 (by rfl) ⟨1313693, by rfl⟩ : syracuseStep 1751591 = 2627387) B2627387
theorem B1555067 : Blo 1036608 1555067 := bstep (se 1 (by rfl) ⟨1166300, by rfl⟩ : syracuseStep 1555067 = 2332601) B2332601
theorem B1555193 : Blo 1036608 1555193 := bstep (se 2 (by rfl) ⟨583197, by rfl⟩ : syracuseStep 1555193 = 1166395) B1166395
theorem B1751881 : Blo 1036608 1751881 := bstep (se 2 (by rfl) ⟨656955, by rfl⟩ : syracuseStep 1751881 = 1313911) B1313911
theorem B1555295 : Blo 1036608 1555295 := bstep (se 1 (by rfl) ⟨1166471, by rfl⟩ : syracuseStep 1555295 = 2332943) B2332943
theorem B3160939 : Blo 1036608 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B1555307 : Blo 1036608 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B1751915 : Blo 1036608 1751915 := bstep (se 1 (by rfl) ⟨1313936, by rfl⟩ : syracuseStep 1751915 = 2627873) B2627873
theorem B1850377 : Blo 1036608 1850377 := bstep (se 2 (by rfl) ⟨693891, by rfl⟩ : syracuseStep 1850377 = 1387783) B1387783
theorem B1555535 : Blo 1036608 1555535 := bstep (se 1 (by rfl) ⟨1166651, by rfl⟩ : syracuseStep 1555535 = 2333303) B2333303
theorem B1555655 : Blo 1036608 1555655 := bstep (se 1 (by rfl) ⟨1166741, by rfl⟩ : syracuseStep 1555655 = 2333483) B2333483
theorem B1752313 : Blo 1036608 1752313 := bstep (se 2 (by rfl) ⟨657117, by rfl⟩ : syracuseStep 1752313 = 1314235) B1314235
theorem B5258519 : Blo 1036608 5258519 := bstep (se 1 (by rfl) ⟨3943889, by rfl⟩ : syracuseStep 5258519 = 7887779) B7887779
theorem B1555817 : Blo 1036608 1555817 := bstep (se 2 (by rfl) ⟨583431, by rfl⟩ : syracuseStep 1555817 = 1166863) B1166863
theorem B1555895 : Blo 1036608 1555895 := bstep (se 1 (by rfl) ⟨1166921, by rfl⟩ : syracuseStep 1555895 = 2333843) B2333843
theorem B1555931 : Blo 1036608 1555931 := bstep (se 1 (by rfl) ⟨1166948, by rfl⟩ : syracuseStep 1555931 = 2333897) B2333897
theorem B1752583 : Blo 1036608 1752583 := bstep (se 1 (by rfl) ⟨1314437, by rfl⟩ : syracuseStep 1752583 = 2628875) B2628875
theorem B4210385 : Blo 1036608 4210385 := bstep (se 2 (by rfl) ⟨1578894, by rfl⟩ : syracuseStep 4210385 = 3157789) B3157789
theorem B14991065 : Blo 1036608 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B8437537 : Blo 1036608 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B1556399 : Blo 1036608 1556399 := bstep (se 1 (by rfl) ⟨1167299, by rfl⟩ : syracuseStep 1556399 = 2334599) B2334599
theorem B1753015 : Blo 1036608 1753015 := bstep (se 1 (by rfl) ⟨1314761, by rfl⟩ : syracuseStep 1753015 = 2629523) B2629523
theorem B1556489 : Blo 1036608 1556489 := bstep (se 2 (by rfl) ⟨583683, by rfl⟩ : syracuseStep 1556489 = 1167367) B1167367
theorem B3325967 : Blo 1036608 3325967 := bstep (se 1 (by rfl) ⟨2494475, by rfl⟩ : syracuseStep 3325967 = 4988951) B4988951
theorem B1556519 : Blo 1036608 1556519 := bstep (se 1 (by rfl) ⟨1167389, by rfl⟩ : syracuseStep 1556519 = 2334779) B2334779
theorem B4997177 : Blo 1036608 4997177 := bstep (se 2 (by rfl) ⟨1873941, by rfl⟩ : syracuseStep 4997177 = 3747883) B3747883
theorem B5619793 : Blo 1036608 5619793 := bstep (se 2 (by rfl) ⟨2107422, by rfl⟩ : syracuseStep 5619793 = 4214845) B4214845
theorem B3948659 : Blo 1036608 3948659 := bstep (se 1 (by rfl) ⟨2961494, by rfl⟩ : syracuseStep 3948659 = 5922989) B5922989
theorem B1556603 : Blo 1036608 1556603 := bstep (se 1 (by rfl) ⟨1167452, by rfl⟩ : syracuseStep 1556603 = 2334905) B2334905
theorem B1753211 : Blo 1036608 1753211 := bstep (se 1 (by rfl) ⟨1314908, by rfl⟩ : syracuseStep 1753211 = 2629817) B2629817
theorem B1556729 : Blo 1036608 1556729 := bstep (se 2 (by rfl) ⟨583773, by rfl⟩ : syracuseStep 1556729 = 1167547) B1167547
theorem B1556831 : Blo 1036608 1556831 := bstep (se 1 (by rfl) ⟨1167623, by rfl⟩ : syracuseStep 1556831 = 2335247) B2335247
theorem B1556843 : Blo 1036608 1556843 := bstep (se 1 (by rfl) ⟨1167632, by rfl⟩ : syracuseStep 1556843 = 2335265) B2335265
theorem B1753609 : Blo 1036608 1753609 := bstep (se 2 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 1753609 = 1315207) B1315207
theorem B26624537 : Blo 1036608 26624537 := bstep (se 2 (by rfl) ⟨9984201, by rfl⟩ : syracuseStep 26624537 = 19968403) B19968403
theorem B1557071 : Blo 1036608 1557071 := bstep (se 1 (by rfl) ⟨1167803, by rfl⟩ : syracuseStep 1557071 = 2335607) B2335607
theorem B3162763 : Blo 1036608 3162763 := bstep (se 1 (by rfl) ⟨2372072, by rfl⟩ : syracuseStep 3162763 = 4744145) B4744145
theorem B1753771 : Blo 1036608 1753771 := bstep (se 1 (by rfl) ⟨1315328, by rfl⟩ : syracuseStep 1753771 = 2630657) B2630657
theorem B1557191 : Blo 1036608 1557191 := bstep (se 1 (by rfl) ⟨1167893, by rfl⟩ : syracuseStep 1557191 = 2335787) B2335787
theorem B1557353 : Blo 1036608 1557353 := bstep (se 2 (by rfl) ⟨584007, by rfl⟩ : syracuseStep 1557353 = 1168015) B1168015
theorem B21316459 : Blo 1036608 21316459 := bstep (se 1 (by rfl) ⟨15987344, by rfl⟩ : syracuseStep 21316459 = 31974689) B31974689
theorem B5260139 : Blo 1036608 5260139 := bstep (se 1 (by rfl) ⟨3945104, by rfl⟩ : syracuseStep 5260139 = 7890209) B7890209
theorem B1557431 : Blo 1036608 1557431 := bstep (se 1 (by rfl) ⟨1168073, by rfl⟩ : syracuseStep 1557431 = 2336147) B2336147
theorem B1557467 : Blo 1036608 1557467 := bstep (se 1 (by rfl) ⟨1168100, by rfl⟩ : syracuseStep 1557467 = 2336201) B2336201
theorem B1754075 : Blo 1036608 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B5915699 : Blo 1036608 5915699 := bstep (se 1 (by rfl) ⟨4436774, by rfl⟩ : syracuseStep 5915699 = 8873549) B8873549
theorem B1754311 : Blo 1036608 1754311 := bstep (se 1 (by rfl) ⟨1315733, by rfl⟩ : syracuseStep 1754311 = 2631467) B2631467
theorem B1754473 : Blo 1036608 1754473 := bstep (se 2 (by rfl) ⟨657927, by rfl⟩ : syracuseStep 1754473 = 1315855) B1315855
theorem B17745317 : Blo 1036608 17745317 := bstep (se 4 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 17745317 = 3327247) B3327247
theorem B1557935 : Blo 1036608 1557935 := bstep (se 1 (by rfl) ⟨1168451, by rfl⟩ : syracuseStep 1557935 = 2336903) B2336903
theorem B5260787 : Blo 1036608 5260787 := bstep (se 1 (by rfl) ⟨3945590, by rfl⟩ : syracuseStep 5260787 = 7891181) B7891181
theorem B1558025 : Blo 1036608 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B1558055 : Blo 1036608 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B5916199 : Blo 1036608 5916199 := bstep (se 1 (by rfl) ⟨4437149, by rfl⟩ : syracuseStep 5916199 = 8874299) B8874299
theorem B4212283 : Blo 1036608 4212283 := bstep (se 1 (by rfl) ⟨3159212, by rfl⟩ : syracuseStep 4212283 = 6318425) B6318425
theorem B1558139 : Blo 1036608 1558139 := bstep (se 1 (by rfl) ⟨1168604, by rfl⟩ : syracuseStep 1558139 = 2337209) B2337209
theorem B1558265 : Blo 1036608 1558265 := bstep (se 2 (by rfl) ⟨584349, by rfl⟩ : syracuseStep 1558265 = 1168699) B1168699
theorem B3950329 : Blo 1036608 3950329 := bstep (se 2 (by rfl) ⟨1481373, by rfl⟩ : syracuseStep 3950329 = 2962747) B2962747
theorem B13289305 : Blo 1036608 13289305 := bstep (se 2 (by rfl) ⟨4983489, by rfl⟩ : syracuseStep 13289305 = 9966979) B9966979
theorem B1558367 : Blo 1036608 1558367 := bstep (se 1 (by rfl) ⟨1168775, by rfl⟩ : syracuseStep 1558367 = 2337551) B2337551
theorem B1558379 : Blo 1036608 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B1755067 : Blo 1036608 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B4999175 : Blo 1036608 4999175 := bstep (se 1 (by rfl) ⟨3749381, by rfl⟩ : syracuseStep 4999175 = 7498763) B7498763
theorem B7096349 : Blo 1036608 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B1755175 : Blo 1036608 1755175 := bstep (se 1 (by rfl) ⟨1316381, by rfl⟩ : syracuseStep 1755175 = 2632763) B2632763
theorem B1558607 : Blo 1036608 1558607 := bstep (se 1 (by rfl) ⟨1168955, by rfl⟩ : syracuseStep 1558607 = 2337911) B2337911
theorem B1558727 : Blo 1036608 1558727 := bstep (se 1 (by rfl) ⟨1169045, by rfl⟩ : syracuseStep 1558727 = 2338091) B2338091
theorem B8407307 : Blo 1036608 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B6080779 : Blo 1036608 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B1558889 : Blo 1036608 1558889 := bstep (se 2 (by rfl) ⟨584583, by rfl⟩ : syracuseStep 1558889 = 1169167) B1169167
theorem B1755499 : Blo 1036608 1755499 := bstep (se 1 (by rfl) ⟨1316624, by rfl⟩ : syracuseStep 1755499 = 2633249) B2633249
theorem B2214287 : Blo 1036608 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B1558967 : Blo 1036608 1558967 := bstep (se 1 (by rfl) ⟨1169225, by rfl⟩ : syracuseStep 1558967 = 2338451) B2338451
theorem B1559003 : Blo 1036608 1559003 := bstep (se 1 (by rfl) ⟨1169252, by rfl⟩ : syracuseStep 1559003 = 2338505) B2338505
theorem B34621937 : Blo 1036608 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B5262083 : Blo 1036608 5262083 := bstep (se 1 (by rfl) ⟨3946562, by rfl⟩ : syracuseStep 5262083 = 7893125) B7893125
theorem B1559471 : Blo 1036608 1559471 := bstep (se 1 (by rfl) ⟨1169603, by rfl⟩ : syracuseStep 1559471 = 2339207) B2339207
theorem B1559561 : Blo 1036608 1559561 := bstep (se 2 (by rfl) ⟨584835, by rfl⟩ : syracuseStep 1559561 = 1169671) B1169671
theorem B1559591 : Blo 1036608 1559591 := bstep (se 1 (by rfl) ⟨1169693, by rfl⟩ : syracuseStep 1559591 = 2339387) B2339387
theorem B90917963 : Blo 1036608 90917963 := bstep (se 1 (by rfl) ⟨68188472, by rfl⟩ : syracuseStep 90917963 = 136376945) B136376945
theorem B1559675 : Blo 1036608 1559675 := bstep (se 1 (by rfl) ⟨1169756, by rfl⟩ : syracuseStep 1559675 = 2339513) B2339513
theorem B1559801 : Blo 1036608 1559801 := bstep (se 2 (by rfl) ⟨584925, by rfl⟩ : syracuseStep 1559801 = 1169851) B1169851
theorem B1559903 : Blo 1036608 1559903 := bstep (se 1 (by rfl) ⟨1169927, by rfl⟩ : syracuseStep 1559903 = 2339855) B2339855
theorem B1559915 : Blo 1036608 1559915 := bstep (se 1 (by rfl) ⟨1169936, by rfl⟩ : syracuseStep 1559915 = 2339873) B2339873
theorem B1560143 : Blo 1036608 1560143 := bstep (se 1 (by rfl) ⟨1170107, by rfl⟩ : syracuseStep 1560143 = 2340215) B2340215
theorem B1166971 : Blo 1036608 1166971 := bstep (se 1 (by rfl) ⟨875228, by rfl⟩ : syracuseStep 1166971 = 1750457) B1750457
theorem B1560263 : Blo 1036608 1560263 := bstep (se 1 (by rfl) ⟨1170197, by rfl⟩ : syracuseStep 1560263 = 2340395) B2340395
theorem B14995165 : Blo 1036608 14995165 := bstep (se 3 (by rfl) ⟨2811593, by rfl⟩ : syracuseStep 14995165 = 5623187) B5623187
theorem B1560425 : Blo 1036608 1560425 := bstep (se 2 (by rfl) ⟨585159, by rfl⟩ : syracuseStep 1560425 = 1170319) B1170319
theorem B2215841 : Blo 1036608 2215841 := bstep (se 2 (by rfl) ⟨830940, by rfl⟩ : syracuseStep 2215841 = 1661881) B1661881
theorem B1560503 : Blo 1036608 1560503 := bstep (se 1 (by rfl) ⟨1170377, by rfl⟩ : syracuseStep 1560503 = 2340755) B2340755
theorem B1560539 : Blo 1036608 1560539 := bstep (se 1 (by rfl) ⟨1170404, by rfl⟩ : syracuseStep 1560539 = 2340809) B2340809
theorem B3330067 : Blo 1036608 3330067 := bstep (se 1 (by rfl) ⟨2497550, by rfl⟩ : syracuseStep 3330067 = 4995101) B4995101
theorem B1167439 : Blo 1036608 1167439 := bstep (se 1 (by rfl) ⟨875579, by rfl⟩ : syracuseStep 1167439 = 1751159) B1751159
theorem B1036623 : Blo 1036608 1036623 := bstep (se 1 (by rfl) ⟨777467, by rfl⟩ : syracuseStep 1036623 = 1554935) B1554935
theorem B5263703 : Blo 1036608 5263703 := bstep (se 1 (by rfl) ⟨3947777, by rfl⟩ : syracuseStep 5263703 = 7895555) B7895555
theorem B1036639 : Blo 1036608 1036639 := bstep (se 1 (by rfl) ⟨777479, by rfl⟩ : syracuseStep 1036639 = 1554959) B1554959
theorem B1036667 : Blo 1036608 1036667 := bstep (se 1 (by rfl) ⟨777500, by rfl⟩ : syracuseStep 1036667 = 1555001) B1555001
theorem B1036719 : Blo 1036608 1036719 := bstep (se 1 (by rfl) ⟨777539, by rfl⟩ : syracuseStep 1036719 = 1555079) B1555079
theorem B1036743 : Blo 1036608 1036743 := bstep (se 1 (by rfl) ⟨777557, by rfl⟩ : syracuseStep 1036743 = 1555115) B1555115
theorem B1036763 : Blo 1036608 1036763 := bstep (se 1 (by rfl) ⟨777572, by rfl⟩ : syracuseStep 1036763 = 1555145) B1555145
theorem B1167835 : Blo 1036608 1167835 := bstep (se 1 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 1167835 = 1751753) B1751753
theorem B1036839 : Blo 1036608 1036839 := bstep (se 1 (by rfl) ⟨777629, by rfl⟩ : syracuseStep 1036839 = 1555259) B1555259
theorem B1036879 : Blo 1036608 1036879 := bstep (se 1 (by rfl) ⟨777659, by rfl⟩ : syracuseStep 1036879 = 1555319) B1555319
theorem B1036895 : Blo 1036608 1036895 := bstep (se 1 (by rfl) ⟨777671, by rfl⟩ : syracuseStep 1036895 = 1555343) B1555343
theorem B1036923 : Blo 1036608 1036923 := bstep (se 1 (by rfl) ⟨777692, by rfl⟩ : syracuseStep 1036923 = 1555385) B1555385
theorem B3330683 : Blo 1036608 3330683 := bstep (se 1 (by rfl) ⟨2498012, by rfl⟩ : syracuseStep 3330683 = 4996025) B4996025
theorem B1036975 : Blo 1036608 1036975 := bstep (se 1 (by rfl) ⟨777731, by rfl⟩ : syracuseStep 1036975 = 1555463) B1555463
theorem B1036999 : Blo 1036608 1036999 := bstep (se 1 (by rfl) ⟨777749, by rfl⟩ : syracuseStep 1036999 = 1555499) B1555499
theorem B1037019 : Blo 1036608 1037019 := bstep (se 1 (by rfl) ⟨777764, by rfl⟩ : syracuseStep 1037019 = 1555529) B1555529
theorem B7099139 : Blo 1036608 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B1037095 : Blo 1036608 1037095 := bstep (se 1 (by rfl) ⟨777821, by rfl⟩ : syracuseStep 1037095 = 1555643) B1555643
theorem B1037135 : Blo 1036608 1037135 := bstep (se 1 (by rfl) ⟨777851, by rfl⟩ : syracuseStep 1037135 = 1555703) B1555703
theorem B1037151 : Blo 1036608 1037151 := bstep (se 1 (by rfl) ⟨777863, by rfl⟩ : syracuseStep 1037151 = 1555727) B1555727
theorem B28463987 : Blo 1036608 28463987 := bstep (se 1 (by rfl) ⟨21347990, by rfl⟩ : syracuseStep 28463987 = 42695981) B42695981
theorem B1037179 : Blo 1036608 1037179 := bstep (se 1 (by rfl) ⟨777884, by rfl⟩ : syracuseStep 1037179 = 1555769) B1555769
theorem B1037231 : Blo 1036608 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B1168303 : Blo 1036608 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B1037255 : Blo 1036608 1037255 := bstep (se 1 (by rfl) ⟨777941, by rfl⟩ : syracuseStep 1037255 = 1555883) B1555883
theorem B1037275 : Blo 1036608 1037275 := bstep (se 1 (by rfl) ⟨777956, by rfl⟩ : syracuseStep 1037275 = 1555913) B1555913
theorem B1037351 : Blo 1036608 1037351 := bstep (se 1 (by rfl) ⟨778013, by rfl⟩ : syracuseStep 1037351 = 1556027) B1556027
theorem B1037391 : Blo 1036608 1037391 := bstep (se 1 (by rfl) ⟨778043, by rfl⟩ : syracuseStep 1037391 = 1556087) B1556087
theorem B1037407 : Blo 1036608 1037407 := bstep (se 1 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 1037407 = 1556111) B1556111
theorem B1037435 : Blo 1036608 1037435 := bstep (se 1 (by rfl) ⟨778076, by rfl⟩ : syracuseStep 1037435 = 1556153) B1556153
theorem B1037487 : Blo 1036608 1037487 := bstep (se 1 (by rfl) ⟨778115, by rfl⟩ : syracuseStep 1037487 = 1556231) B1556231
theorem B1037511 : Blo 1036608 1037511 := bstep (se 1 (by rfl) ⟨778133, by rfl⟩ : syracuseStep 1037511 = 1556267) B1556267
theorem B1037531 : Blo 1036608 1037531 := bstep (se 1 (by rfl) ⟨778148, by rfl⟩ : syracuseStep 1037531 = 1556297) B1556297
theorem B1037607 : Blo 1036608 1037607 := bstep (se 1 (by rfl) ⟨778205, by rfl⟩ : syracuseStep 1037607 = 1556411) B1556411
theorem B1037647 : Blo 1036608 1037647 := bstep (se 1 (by rfl) ⟨778235, by rfl⟩ : syracuseStep 1037647 = 1556471) B1556471
theorem B1037663 : Blo 1036608 1037663 := bstep (se 1 (by rfl) ⟨778247, by rfl⟩ : syracuseStep 1037663 = 1556495) B1556495
theorem B1168735 : Blo 1036608 1168735 := bstep (se 1 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 1168735 = 1753103) B1753103
theorem B1037691 : Blo 1036608 1037691 := bstep (se 1 (by rfl) ⟨778268, by rfl⟩ : syracuseStep 1037691 = 1556537) B1556537
theorem B1037743 : Blo 1036608 1037743 := bstep (se 1 (by rfl) ⟨778307, by rfl⟩ : syracuseStep 1037743 = 1556615) B1556615
theorem B1037767 : Blo 1036608 1037767 := bstep (se 1 (by rfl) ⟨778325, by rfl⟩ : syracuseStep 1037767 = 1556651) B1556651
theorem B1037787 : Blo 1036608 1037787 := bstep (se 1 (by rfl) ⟨778340, by rfl⟩ : syracuseStep 1037787 = 1556681) B1556681
theorem B1037863 : Blo 1036608 1037863 := bstep (se 1 (by rfl) ⟨778397, by rfl⟩ : syracuseStep 1037863 = 1556795) B1556795
theorem B1037903 : Blo 1036608 1037903 := bstep (se 1 (by rfl) ⟨778427, by rfl⟩ : syracuseStep 1037903 = 1556855) B1556855
theorem B1037919 : Blo 1036608 1037919 := bstep (se 1 (by rfl) ⟨778439, by rfl⟩ : syracuseStep 1037919 = 1556879) B1556879
theorem B1037947 : Blo 1036608 1037947 := bstep (se 1 (by rfl) ⟨778460, by rfl⟩ : syracuseStep 1037947 = 1556921) B1556921
theorem B1037999 : Blo 1036608 1037999 := bstep (se 1 (by rfl) ⟨778499, by rfl⟩ : syracuseStep 1037999 = 1556999) B1556999
theorem B1038023 : Blo 1036608 1038023 := bstep (se 1 (by rfl) ⟨778517, by rfl⟩ : syracuseStep 1038023 = 1557035) B1557035
theorem B1169095 : Blo 1036608 1169095 := bstep (se 1 (by rfl) ⟨876821, by rfl⟩ : syracuseStep 1169095 = 1753643) B1753643
theorem B1038043 : Blo 1036608 1038043 := bstep (se 1 (by rfl) ⟨778532, by rfl⟩ : syracuseStep 1038043 = 1557065) B1557065
theorem B2217721 : Blo 1036608 2217721 := bstep (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) B1663291
theorem B1038119 : Blo 1036608 1038119 := bstep (se 1 (by rfl) ⟨778589, by rfl⟩ : syracuseStep 1038119 = 1557179) B1557179
theorem B1038159 : Blo 1036608 1038159 := bstep (se 1 (by rfl) ⟨778619, by rfl⟩ : syracuseStep 1038159 = 1557239) B1557239
theorem B1038175 : Blo 1036608 1038175 := bstep (se 1 (by rfl) ⟨778631, by rfl⟩ : syracuseStep 1038175 = 1557263) B1557263
theorem B1038203 : Blo 1036608 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1038255 : Blo 1036608 1038255 := bstep (se 1 (by rfl) ⟨778691, by rfl⟩ : syracuseStep 1038255 = 1557383) B1557383
theorem B1038279 : Blo 1036608 1038279 := bstep (se 1 (by rfl) ⟨778709, by rfl⟩ : syracuseStep 1038279 = 1557419) B1557419
theorem B1038299 : Blo 1036608 1038299 := bstep (se 1 (by rfl) ⟨778724, by rfl⟩ : syracuseStep 1038299 = 1557449) B1557449
theorem B16832519 : Blo 1036608 16832519 := bstep (se 1 (by rfl) ⟨12624389, by rfl⟩ : syracuseStep 16832519 = 25248779) B25248779
theorem B8869925 : Blo 1036608 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B1038375 : Blo 1036608 1038375 := bstep (se 1 (by rfl) ⟨778781, by rfl⟩ : syracuseStep 1038375 = 1557563) B1557563
theorem B1038415 : Blo 1036608 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B2218063 : Blo 1036608 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B1038431 : Blo 1036608 1038431 := bstep (se 1 (by rfl) ⟨778823, by rfl⟩ : syracuseStep 1038431 = 1557647) B1557647
theorem B1038459 : Blo 1036608 1038459 := bstep (se 1 (by rfl) ⟨778844, by rfl⟩ : syracuseStep 1038459 = 1557689) B1557689
theorem B1038511 : Blo 1036608 1038511 := bstep (se 1 (by rfl) ⟨778883, by rfl⟩ : syracuseStep 1038511 = 1557767) B1557767
theorem B1038535 : Blo 1036608 1038535 := bstep (se 1 (by rfl) ⟨778901, by rfl⟩ : syracuseStep 1038535 = 1557803) B1557803
theorem B1038555 : Blo 1036608 1038555 := bstep (se 1 (by rfl) ⟨778916, by rfl⟩ : syracuseStep 1038555 = 1557833) B1557833
theorem B1038631 : Blo 1036608 1038631 := bstep (se 1 (by rfl) ⟨778973, by rfl⟩ : syracuseStep 1038631 = 1557947) B1557947
theorem B11852081 : Blo 1036608 11852081 := bstep (se 2 (by rfl) ⟨4444530, by rfl⟩ : syracuseStep 11852081 = 8889061) B8889061
theorem B1038671 : Blo 1036608 1038671 := bstep (se 1 (by rfl) ⟨779003, by rfl⟩ : syracuseStep 1038671 = 1558007) B1558007
theorem B1038687 : Blo 1036608 1038687 := bstep (se 1 (by rfl) ⟨779015, by rfl⟩ : syracuseStep 1038687 = 1558031) B1558031
theorem B1038715 : Blo 1036608 1038715 := bstep (se 1 (by rfl) ⟨779036, by rfl⟩ : syracuseStep 1038715 = 1558073) B1558073
theorem B1038767 : Blo 1036608 1038767 := bstep (se 1 (by rfl) ⟨779075, by rfl⟩ : syracuseStep 1038767 = 1558151) B1558151
theorem B1038791 : Blo 1036608 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B1038811 : Blo 1036608 1038811 := bstep (se 1 (by rfl) ⟨779108, by rfl⟩ : syracuseStep 1038811 = 1558217) B1558217
theorem B1038887 : Blo 1036608 1038887 := bstep (se 1 (by rfl) ⟨779165, by rfl⟩ : syracuseStep 1038887 = 1558331) B1558331
theorem B1169959 : Blo 1036608 1169959 := bstep (se 1 (by rfl) ⟨877469, by rfl⟩ : syracuseStep 1169959 = 1754939) B1754939
theorem B34134605 : Blo 1036608 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B1038927 : Blo 1036608 1038927 := bstep (se 1 (by rfl) ⟨779195, by rfl⟩ : syracuseStep 1038927 = 1558391) B1558391
theorem B1038943 : Blo 1036608 1038943 := bstep (se 1 (by rfl) ⟨779207, by rfl⟩ : syracuseStep 1038943 = 1558415) B1558415
theorem B1038971 : Blo 1036608 1038971 := bstep (se 1 (by rfl) ⟨779228, by rfl⟩ : syracuseStep 1038971 = 1558457) B1558457
theorem B1039023 : Blo 1036608 1039023 := bstep (se 1 (by rfl) ⟨779267, by rfl⟩ : syracuseStep 1039023 = 1558535) B1558535
theorem B1039047 : Blo 1036608 1039047 := bstep (se 1 (by rfl) ⟨779285, by rfl⟩ : syracuseStep 1039047 = 1558571) B1558571
theorem B1039067 : Blo 1036608 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B91151119 : Blo 1036608 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B1039143 : Blo 1036608 1039143 := bstep (se 1 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 1039143 = 1558715) B1558715
theorem B1039183 : Blo 1036608 1039183 := bstep (se 1 (by rfl) ⟨779387, by rfl⟩ : syracuseStep 1039183 = 1558775) B1558775
theorem B1039199 : Blo 1036608 1039199 := bstep (se 1 (by rfl) ⟨779399, by rfl⟩ : syracuseStep 1039199 = 1558799) B1558799
theorem B1039227 : Blo 1036608 1039227 := bstep (se 1 (by rfl) ⟨779420, by rfl⟩ : syracuseStep 1039227 = 1558841) B1558841
theorem B1039279 : Blo 1036608 1039279 := bstep (se 1 (by rfl) ⟨779459, by rfl⟩ : syracuseStep 1039279 = 1558919) B1558919
theorem B1039303 : Blo 1036608 1039303 := bstep (se 1 (by rfl) ⟨779477, by rfl⟩ : syracuseStep 1039303 = 1558955) B1558955
theorem B1039323 : Blo 1036608 1039323 := bstep (se 1 (by rfl) ⟨779492, by rfl⟩ : syracuseStep 1039323 = 1558985) B1558985
theorem B11820005 : Blo 1036608 11820005 := bstep (se 4 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 11820005 = 2216251) B2216251
theorem B1039399 : Blo 1036608 1039399 := bstep (se 1 (by rfl) ⟨779549, by rfl⟩ : syracuseStep 1039399 = 1559099) B1559099
theorem B1039439 : Blo 1036608 1039439 := bstep (se 1 (by rfl) ⟨779579, by rfl⟩ : syracuseStep 1039439 = 1559159) B1559159
theorem B1039455 : Blo 1036608 1039455 := bstep (se 1 (by rfl) ⟨779591, by rfl⟩ : syracuseStep 1039455 = 1559183) B1559183
theorem B1039483 : Blo 1036608 1039483 := bstep (se 1 (by rfl) ⟨779612, by rfl⟩ : syracuseStep 1039483 = 1559225) B1559225
theorem B1039535 : Blo 1036608 1039535 := bstep (se 1 (by rfl) ⟨779651, by rfl⟩ : syracuseStep 1039535 = 1559303) B1559303
theorem B1039559 : Blo 1036608 1039559 := bstep (se 1 (by rfl) ⟨779669, by rfl⟩ : syracuseStep 1039559 = 1559339) B1559339
theorem B1039579 : Blo 1036608 1039579 := bstep (se 1 (by rfl) ⟨779684, by rfl⟩ : syracuseStep 1039579 = 1559369) B1559369
theorem B18963725 : Blo 1036608 18963725 := bstep (se 3 (by rfl) ⟨3555698, by rfl⟩ : syracuseStep 18963725 = 7111397) B7111397
theorem B1039655 : Blo 1036608 1039655 := bstep (se 1 (by rfl) ⟨779741, by rfl⟩ : syracuseStep 1039655 = 1559483) B1559483
theorem B1039695 : Blo 1036608 1039695 := bstep (se 1 (by rfl) ⟨779771, by rfl⟩ : syracuseStep 1039695 = 1559543) B1559543
theorem B1039711 : Blo 1036608 1039711 := bstep (se 1 (by rfl) ⟨779783, by rfl⟩ : syracuseStep 1039711 = 1559567) B1559567
theorem B1039739 : Blo 1036608 1039739 := bstep (se 1 (by rfl) ⟨779804, by rfl⟩ : syracuseStep 1039739 = 1559609) B1559609
theorem B1039791 : Blo 1036608 1039791 := bstep (se 1 (by rfl) ⟨779843, by rfl⟩ : syracuseStep 1039791 = 1559687) B1559687
theorem B1039815 : Blo 1036608 1039815 := bstep (se 1 (by rfl) ⟨779861, by rfl⟩ : syracuseStep 1039815 = 1559723) B1559723
theorem B1039835 : Blo 1036608 1039835 := bstep (se 1 (by rfl) ⟨779876, by rfl⟩ : syracuseStep 1039835 = 1559753) B1559753
theorem B1039911 : Blo 1036608 1039911 := bstep (se 1 (by rfl) ⟨779933, by rfl⟩ : syracuseStep 1039911 = 1559867) B1559867
theorem B1039951 : Blo 1036608 1039951 := bstep (se 1 (by rfl) ⟨779963, by rfl⟩ : syracuseStep 1039951 = 1559927) B1559927
theorem B1039967 : Blo 1036608 1039967 := bstep (se 1 (by rfl) ⟨779975, by rfl⟩ : syracuseStep 1039967 = 1559951) B1559951
theorem B1039995 : Blo 1036608 1039995 := bstep (se 1 (by rfl) ⟨779996, by rfl⟩ : syracuseStep 1039995 = 1559993) B1559993
theorem B1040047 : Blo 1036608 1040047 := bstep (se 1 (by rfl) ⟨780035, by rfl⟩ : syracuseStep 1040047 = 1560071) B1560071
theorem B1040071 : Blo 1036608 1040071 := bstep (se 1 (by rfl) ⟨780053, by rfl⟩ : syracuseStep 1040071 = 1560107) B1560107
theorem B1040091 : Blo 1036608 1040091 := bstep (se 1 (by rfl) ⟨780068, by rfl⟩ : syracuseStep 1040091 = 1560137) B1560137
theorem B1040167 : Blo 1036608 1040167 := bstep (se 1 (by rfl) ⟨780125, by rfl⟩ : syracuseStep 1040167 = 1560251) B1560251
theorem B5267267 : Blo 1036608 5267267 := bstep (se 1 (by rfl) ⟨3950450, by rfl⟩ : syracuseStep 5267267 = 7900901) B7900901
theorem B1040207 : Blo 1036608 1040207 := bstep (se 1 (by rfl) ⟨780155, by rfl⟩ : syracuseStep 1040207 = 1560311) B1560311
theorem B1040223 : Blo 1036608 1040223 := bstep (se 1 (by rfl) ⟨780167, by rfl⟩ : syracuseStep 1040223 = 1560335) B1560335
theorem B1040251 : Blo 1036608 1040251 := bstep (se 1 (by rfl) ⟨780188, by rfl⟩ : syracuseStep 1040251 = 1560377) B1560377
theorem B1040303 : Blo 1036608 1040303 := bstep (se 1 (by rfl) ⟨780227, by rfl⟩ : syracuseStep 1040303 = 1560455) B1560455
theorem B2809787 : Blo 1036608 2809787 := bstep (se 1 (by rfl) ⟨2107340, by rfl⟩ : syracuseStep 2809787 = 4214681) B4214681
theorem B1040327 : Blo 1036608 1040327 := bstep (se 1 (by rfl) ⟨780245, by rfl⟩ : syracuseStep 1040327 = 1560491) B1560491
theorem B1040347 : Blo 1036608 1040347 := bstep (se 1 (by rfl) ⟨780260, by rfl⟩ : syracuseStep 1040347 = 1560521) B1560521
theorem B1040423 : Blo 1036608 1040423 := bstep (se 1 (by rfl) ⟨780317, by rfl⟩ : syracuseStep 1040423 = 1560635) B1560635
theorem B1040463 : Blo 1036608 1040463 := bstep (se 1 (by rfl) ⟨780347, by rfl⟩ : syracuseStep 1040463 = 1560695) B1560695
theorem B1040479 : Blo 1036608 1040479 := bstep (se 1 (by rfl) ⟨780359, by rfl⟩ : syracuseStep 1040479 = 1560719) B1560719
theorem B1040507 : Blo 1036608 1040507 := bstep (se 1 (by rfl) ⟨780380, by rfl⟩ : syracuseStep 1040507 = 1560761) B1560761
theorem B1040559 : Blo 1036608 1040559 := bstep (se 1 (by rfl) ⟨780419, by rfl⟩ : syracuseStep 1040559 = 1560839) B1560839
theorem B1040583 : Blo 1036608 1040583 := bstep (se 1 (by rfl) ⟨780437, by rfl⟩ : syracuseStep 1040583 = 1560875) B1560875
theorem B1040603 : Blo 1036608 1040603 := bstep (se 1 (by rfl) ⟨780452, by rfl⟩ : syracuseStep 1040603 = 1560905) B1560905
theorem B1402105 : Blo 1036608 1402105 := bstep (se 2 (by rfl) ⟨525789, by rfl⟩ : syracuseStep 1402105 = 1051579) B1051579
theorem B63923755 : Blo 1036608 63923755 := bstep (se 1 (by rfl) ⟨47942816, by rfl⟩ : syracuseStep 63923755 = 95885633) B95885633
theorem B63891251 : Blo 1036608 63891251 := bstep (se 1 (by rfl) ⟨47918438, by rfl⟩ : syracuseStep 63891251 = 95836877) B95836877
theorem B2221985 : Blo 1036608 2221985 := bstep (se 2 (by rfl) ⟨833244, by rfl⟩ : syracuseStep 2221985 = 1666489) B1666489
theorem B1894439 : Blo 1036608 1894439 := bstep (se 1 (by rfl) ⟨1420829, by rfl⟩ : syracuseStep 1894439 = 2841659) B2841659
theorem B3205277 : Blo 1036608 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B3500279 : Blo 1036608 3500279 := bstep (se 1 (by rfl) ⟨2625209, by rfl⟩ : syracuseStep 3500279 = 5250419) B5250419
theorem B3500603 : Blo 1036608 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B7891667 : Blo 1036608 7891667 := bstep (se 1 (by rfl) ⟨5918750, by rfl⟩ : syracuseStep 7891667 = 11837501) B11837501
theorem B3992279 : Blo 1036608 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B3500873 : Blo 1036608 3500873 := bstep (se 2 (by rfl) ⟨1312827, by rfl⟩ : syracuseStep 3500873 = 2625655) B2625655
theorem B1109467 : Blo 1036608 1109467 := bstep (se 1 (by rfl) ⟨832100, by rfl⟩ : syracuseStep 1109467 = 1664201) B1664201
theorem B3502007 : Blo 1036608 3502007 := bstep (se 1 (by rfl) ⟨2626505, by rfl⟩ : syracuseStep 3502007 = 5253011) B5253011
theorem B1404937 : Blo 1036608 1404937 := bstep (se 2 (by rfl) ⟨526851, by rfl⟩ : syracuseStep 1404937 = 1053703) B1053703
theorem B12611699 : Blo 1036608 12611699 := bstep (se 1 (by rfl) ⟨9458774, by rfl⟩ : syracuseStep 12611699 = 18917549) B18917549
theorem B7499891 : Blo 1036608 7499891 := bstep (se 1 (by rfl) ⟨5624918, by rfl⟩ : syracuseStep 7499891 = 11249837) B11249837
theorem B6648115 : Blo 1036608 6648115 := bstep (se 1 (by rfl) ⟨4986086, by rfl⟩ : syracuseStep 6648115 = 9972173) B9972173
theorem B1405279 : Blo 1036608 1405279 := bstep (se 1 (by rfl) ⟨1053959, by rfl⟩ : syracuseStep 1405279 = 2107919) B2107919
theorem B3502601 : Blo 1036608 3502601 := bstep (se 2 (by rfl) ⟨1313475, by rfl⟩ : syracuseStep 3502601 = 2626951) B2626951
theorem B11825837 : Blo 1036608 11825837 := bstep (se 3 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 11825837 = 4434689) B4434689
theorem B13300787 : Blo 1036608 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B1111163 : Blo 1036608 1111163 := bstep (se 1 (by rfl) ⟨833372, by rfl⟩ : syracuseStep 1111163 = 1666745) B1666745
theorem B7992665 : Blo 1036608 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B3503465 : Blo 1036608 3503465 := bstep (se 2 (by rfl) ⟨1313799, by rfl⟩ : syracuseStep 3503465 = 2627599) B2627599
theorem B3995345 : Blo 1036608 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B3504059 : Blo 1036608 3504059 := bstep (se 1 (by rfl) ⟨2628044, by rfl⟩ : syracuseStep 3504059 = 5256089) B5256089
theorem B7895069 : Blo 1036608 7895069 := bstep (se 3 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 7895069 = 2960651) B2960651
theorem B4324205 : Blo 1036608 4324205 := bstep (se 3 (by rfl) ⟨810788, by rfl⟩ : syracuseStep 4324205 = 1621577) B1621577
theorem B3505787 : Blo 1036608 3505787 := bstep (se 1 (by rfl) ⟨2629340, by rfl⟩ : syracuseStep 3505787 = 5258681) B5258681
theorem B3505949 : Blo 1036608 3505949 := bstep (se 3 (by rfl) ⟨657365, by rfl⟩ : syracuseStep 3505949 = 1314731) B1314731
theorem B3506759 : Blo 1036608 3506759 := bstep (se 1 (by rfl) ⟨2630069, by rfl⟩ : syracuseStep 3506759 = 5260139) B5260139
theorem B11830211 : Blo 1036608 11830211 := bstep (se 1 (by rfl) ⟨8872658, by rfl⟩ : syracuseStep 11830211 = 17745317) B17745317
theorem B3507191 : Blo 1036608 3507191 := bstep (se 1 (by rfl) ⟨2630393, by rfl⟩ : syracuseStep 3507191 = 5260787) B5260787
theorem B2491535 : Blo 1036608 2491535 := bstep (se 1 (by rfl) ⟨1868651, by rfl⟩ : syracuseStep 2491535 = 3737303) B3737303
theorem B5604871 : Blo 1036608 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B1476191 : Blo 1036608 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B1869473 : Blo 1036608 1869473 := bstep (se 2 (by rfl) ⟨701052, by rfl⟩ : syracuseStep 1869473 = 1402105) B1402105
theorem B7898957 : Blo 1036608 7898957 := bstep (se 3 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 7898957 = 2962109) B2962109
theorem B3508055 : Blo 1036608 3508055 := bstep (se 1 (by rfl) ⟨2631041, by rfl⟩ : syracuseStep 3508055 = 5262083) B5262083
theorem B3901289 : Blo 1036608 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B6653933 : Blo 1036608 6653933 := bstep (se 3 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 6653933 = 2495225) B2495225
theorem B85231673 : Blo 1036608 85231673 := bstep (se 2 (by rfl) ⟨31961877, by rfl⟩ : syracuseStep 85231673 = 63923755) B63923755
theorem B3737735 : Blo 1036608 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B1968475 : Blo 1036608 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B2951927 : Blo 1036608 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B3509135 : Blo 1036608 3509135 := bstep (se 1 (by rfl) ⟨2631851, by rfl⟩ : syracuseStep 3509135 = 5263703) B5263703
theorem B2493659 : Blo 1036608 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B18975991 : Blo 1036608 18975991 := bstep (se 1 (by rfl) ⟨14231993, by rfl⟩ : syracuseStep 18975991 = 28463987) B28463987
theorem B1969447 : Blo 1036608 1969447 := bstep (se 1 (by rfl) ⟨1477085, by rfl⟩ : syracuseStep 1969447 = 2954171) B2954171
theorem B1314139 : Blo 1036608 1314139 := bstep (se 1 (by rfl) ⟨985604, by rfl⟩ : syracuseStep 1314139 = 1971209) B1971209
theorem B1248679 : Blo 1036608 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B2625119 : Blo 1036608 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B11243609 : Blo 1036608 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B3510377 : Blo 1036608 3510377 := bstep (se 2 (by rfl) ⟨1316391, by rfl⟩ : syracuseStep 3510377 = 2632783) B2632783
theorem B7901387 : Blo 1036608 7901387 := bstep (se 1 (by rfl) ⟨5926040, by rfl⟩ : syracuseStep 7901387 = 11852081) B11852081
theorem B2625817 : Blo 1036608 2625817 := bstep (se 2 (by rfl) ⟨984681, by rfl⟩ : syracuseStep 2625817 = 1969363) B1969363
theorem B2494745 : Blo 1036608 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B1315111 : Blo 1036608 1315111 := bstep (se 1 (by rfl) ⟨986333, by rfl⟩ : syracuseStep 1315111 = 1972667) B1972667
theorem B2625959 : Blo 1036608 2625959 := bstep (se 1 (by rfl) ⟨1969469, by rfl⟩ : syracuseStep 2625959 = 3938939) B3938939
theorem B10654253 : Blo 1036608 10654253 := bstep (se 3 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 10654253 = 3995345) B3995345
theorem B2626121 : Blo 1036608 2626121 := bstep (se 2 (by rfl) ⟨984795, by rfl⟩ : syracuseStep 2626121 = 1969591) B1969591
theorem B1315435 : Blo 1036608 1315435 := bstep (se 1 (by rfl) ⟨986576, by rfl⟩ : syracuseStep 1315435 = 1973153) B1973153
theorem B4985489 : Blo 1036608 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B1184431 : Blo 1036608 1184431 := bstep (se 1 (by rfl) ⟨888323, by rfl⟩ : syracuseStep 1184431 = 1776647) B1776647
theorem B9966365 : Blo 1036608 9966365 := bstep (se 3 (by rfl) ⟨1868693, by rfl⟩ : syracuseStep 9966365 = 3737387) B3737387
theorem B36016969 : Blo 1036608 36016969 := bstep (se 2 (by rfl) ⟨13506363, by rfl⟩ : syracuseStep 36016969 = 27012727) B27012727
theorem B3511241 : Blo 1036608 3511241 := bstep (se 2 (by rfl) ⟨1316715, by rfl⟩ : syracuseStep 3511241 = 2633431) B2633431
theorem B19993553 : Blo 1036608 19993553 := bstep (se 2 (by rfl) ⟨7497582, by rfl⟩ : syracuseStep 19993553 = 14995165) B14995165
theorem B3511511 : Blo 1036608 3511511 := bstep (se 1 (by rfl) ⟨2633633, by rfl⟩ : syracuseStep 3511511 = 5267267) B5267267
theorem B1873249 : Blo 1036608 1873249 := bstep (se 2 (by rfl) ⟨702468, by rfl⟩ : syracuseStep 1873249 = 1404937) B1404937
theorem B7476619 : Blo 1036608 7476619 := bstep (se 1 (by rfl) ⟨5607464, by rfl⟩ : syracuseStep 7476619 = 11214929) B11214929
theorem B5051837 : Blo 1036608 5051837 := bstep (se 3 (by rfl) ⟨947219, by rfl⟩ : syracuseStep 5051837 = 1894439) B1894439
theorem B39917123 : Blo 1036608 39917123 := bstep (se 1 (by rfl) ⟨29937842, by rfl⟩ : syracuseStep 39917123 = 59875685) B59875685
theorem B2332457 : Blo 1036608 2332457 := bstep (se 2 (by rfl) ⟨874671, by rfl⟩ : syracuseStep 2332457 = 1749343) B1749343
theorem B1873705 : Blo 1036608 1873705 := bstep (se 2 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 1873705 = 1405279) B1405279
theorem B2103401 : Blo 1036608 2103401 := bstep (se 2 (by rfl) ⟨788775, by rfl⟩ : syracuseStep 2103401 = 1577551) B1577551
theorem B5249447 : Blo 1036608 5249447 := bstep (se 1 (by rfl) ⟨3937085, by rfl⟩ : syracuseStep 5249447 = 7874171) B7874171
theorem B2628065 : Blo 1036608 2628065 := bstep (se 2 (by rfl) ⟨985524, by rfl⟩ : syracuseStep 2628065 = 1971049) B1971049
theorem B5249609 : Blo 1036608 5249609 := bstep (se 2 (by rfl) ⟨1968603, by rfl⟩ : syracuseStep 5249609 = 3937207) B3937207
theorem B1481323 : Blo 1036608 1481323 := bstep (se 1 (by rfl) ⟨1110992, by rfl⟩ : syracuseStep 1481323 = 2221985) B2221985
theorem B2136851 : Blo 1036608 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B2333519 : Blo 1036608 2333519 := bstep (se 1 (by rfl) ⟨1750139, by rfl⟩ : syracuseStep 2333519 = 3500279) B3500279
theorem B3742607 : Blo 1036608 3742607 := bstep (se 1 (by rfl) ⟨2806955, by rfl⟩ : syracuseStep 3742607 = 5613911) B5613911
theorem B2628571 : Blo 1036608 2628571 := bstep (se 1 (by rfl) ⟨1971428, by rfl⟩ : syracuseStep 2628571 = 3942857) B3942857
theorem B2333735 : Blo 1036608 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B2333915 : Blo 1036608 2333915 := bstep (se 1 (by rfl) ⟨1750436, by rfl⟩ : syracuseStep 2333915 = 3500873) B3500873
theorem B2628895 : Blo 1036608 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B4988297 : Blo 1036608 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B2334113 : Blo 1036608 2334113 := bstep (se 2 (by rfl) ⟨875292, by rfl⟩ : syracuseStep 2334113 = 1750585) B1750585
theorem B2956961 : Blo 1036608 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B3546887 : Blo 1036608 3546887 := bstep (se 1 (by rfl) ⟨2660165, by rfl⟩ : syracuseStep 3546887 = 5320331) B5320331
theorem B1974071 : Blo 1036608 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B57614141 : Blo 1036608 57614141 := bstep (se 3 (by rfl) ⟨10802651, by rfl⟩ : syracuseStep 57614141 = 21605303) B21605303
theorem B2334671 : Blo 1036608 2334671 := bstep (se 1 (by rfl) ⟨1751003, by rfl⟩ : syracuseStep 2334671 = 3502007) B3502007
theorem B1974223 : Blo 1036608 1974223 := bstep (se 1 (by rfl) ⟨1480667, by rfl⟩ : syracuseStep 1974223 = 2961335) B2961335
theorem B9969713 : Blo 1036608 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B2957417 : Blo 1036608 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B16851077 : Blo 1036608 16851077 := bstep (se 4 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 16851077 = 3159577) B3159577
theorem B7479449 : Blo 1036608 7479449 := bstep (se 2 (by rfl) ⟨2804793, by rfl⟩ : syracuseStep 7479449 = 5609587) B5609587
theorem B2335049 : Blo 1036608 2335049 := bstep (se 2 (by rfl) ⟨875643, by rfl⟩ : syracuseStep 2335049 = 1751287) B1751287
theorem B2335067 : Blo 1036608 2335067 := bstep (se 1 (by rfl) ⟨1751300, by rfl⟩ : syracuseStep 2335067 = 3502601) B3502601
theorem B2629979 : Blo 1036608 2629979 := bstep (se 1 (by rfl) ⟨1972484, by rfl⟩ : syracuseStep 2629979 = 3944969) B3944969
theorem B5251553 : Blo 1036608 5251553 := bstep (se 2 (by rfl) ⟨1969332, by rfl⟩ : syracuseStep 5251553 = 3938665) B3938665
theorem B3940883 : Blo 1036608 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B50569933 : Blo 1036608 50569933 := bstep (se 3 (by rfl) ⟨9481862, by rfl⟩ : syracuseStep 50569933 = 18963725) B18963725
theorem B2335643 : Blo 1036608 2335643 := bstep (se 1 (by rfl) ⟨1751732, by rfl⟩ : syracuseStep 2335643 = 3503465) B3503465
theorem B1975195 : Blo 1036608 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B1123279 : Blo 1036608 1123279 := bstep (se 1 (by rfl) ⟨842459, by rfl⟩ : syracuseStep 1123279 = 1684919) B1684919
theorem B2335841 : Blo 1036608 2335841 := bstep (se 2 (by rfl) ⟨875940, by rfl⟩ : syracuseStep 2335841 = 1751881) B1751881
theorem B1975529 : Blo 1036608 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B2336039 : Blo 1036608 2336039 := bstep (se 1 (by rfl) ⟨1752029, by rfl⟩ : syracuseStep 2336039 = 3504059) B3504059
theorem B2630951 : Blo 1036608 2630951 := bstep (se 1 (by rfl) ⟨1973213, by rfl⟩ : syracuseStep 2630951 = 3946427) B3946427
theorem B2467169 : Blo 1036608 2467169 := bstep (se 2 (by rfl) ⟨925188, by rfl⟩ : syracuseStep 2467169 = 1850377) B1850377
theorem B2336417 : Blo 1036608 2336417 := bstep (se 2 (by rfl) ⟨876156, by rfl⟩ : syracuseStep 2336417 = 1752313) B1752313
theorem B2336777 : Blo 1036608 2336777 := bstep (se 2 (by rfl) ⟨876291, by rfl⟩ : syracuseStep 2336777 = 1752583) B1752583
theorem B11250049 : Blo 1036608 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B2337191 : Blo 1036608 2337191 := bstep (se 1 (by rfl) ⟨1752893, by rfl⟩ : syracuseStep 2337191 = 3505787) B3505787
theorem B5908909 : Blo 1036608 5908909 := bstep (se 3 (by rfl) ⟨1107920, by rfl⟩ : syracuseStep 5908909 = 2215841) B2215841
theorem B2337299 : Blo 1036608 2337299 := bstep (se 1 (by rfl) ⟨1752974, by rfl⟩ : syracuseStep 2337299 = 3505949) B3505949
theorem B2337353 : Blo 1036608 2337353 := bstep (se 2 (by rfl) ⟨876507, by rfl⟩ : syracuseStep 2337353 = 1753015) B1753015
theorem B5253821 : Blo 1036608 5253821 := bstep (se 3 (by rfl) ⟨985091, by rfl⟩ : syracuseStep 5253821 = 1970183) B1970183
theorem B2632439 : Blo 1036608 2632439 := bstep (se 1 (by rfl) ⟨1974329, by rfl⟩ : syracuseStep 2632439 = 3948659) B3948659
theorem B2337767 : Blo 1036608 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B9481283 : Blo 1036608 9481283 := bstep (se 1 (by rfl) ⟨7110962, by rfl⟩ : syracuseStep 9481283 = 14221925) B14221925
theorem B2338145 : Blo 1036608 2338145 := bstep (se 2 (by rfl) ⟨876804, by rfl⟩ : syracuseStep 2338145 = 1753609) B1753609
theorem B2633057 : Blo 1036608 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B3943799 : Blo 1036608 3943799 := bstep (se 1 (by rfl) ⟨2957849, by rfl⟩ : syracuseStep 3943799 = 5915699) B5915699
theorem B10136951 : Blo 1036608 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B2338235 : Blo 1036608 2338235 := bstep (se 1 (by rfl) ⟨1753676, by rfl⟩ : syracuseStep 2338235 = 3507353) B3507353
theorem B2338361 : Blo 1036608 2338361 := bstep (se 2 (by rfl) ⟨876885, by rfl⟩ : syracuseStep 2338361 = 1753771) B1753771
theorem B4206377 : Blo 1036608 4206377 := bstep (se 2 (by rfl) ⟨1577391, by rfl⟩ : syracuseStep 4206377 = 3154783) B3154783
theorem B28421945 : Blo 1036608 28421945 := bstep (se 2 (by rfl) ⟨10658229, by rfl⟩ : syracuseStep 28421945 = 21316459) B21316459
theorem B3321661 : Blo 1036608 3321661 := bstep (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) B1245623
theorem B4730899 : Blo 1036608 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B2339027 : Blo 1036608 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B2339081 : Blo 1036608 2339081 := bstep (se 2 (by rfl) ⟨877155, by rfl⟩ : syracuseStep 2339081 = 1754311) B1754311
theorem B71840033 : Blo 1036608 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B23081291 : Blo 1036608 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B4436315 : Blo 1036608 4436315 := bstep (se 1 (by rfl) ⟨3327236, by rfl⟩ : syracuseStep 4436315 = 6654473) B6654473
theorem B2339297 : Blo 1036608 2339297 := bstep (se 2 (by rfl) ⟨877236, by rfl⟩ : syracuseStep 2339297 = 1754473) B1754473
theorem B5616377 : Blo 1036608 5616377 := bstep (se 2 (by rfl) ⟨2106141, by rfl⟩ : syracuseStep 5616377 = 4212283) B4212283
theorem B2339603 : Blo 1036608 2339603 := bstep (se 1 (by rfl) ⟨1754702, by rfl⟩ : syracuseStep 2339603 = 3509405) B3509405
theorem B1749991 : Blo 1036608 1749991 := bstep (se 1 (by rfl) ⟨1312493, by rfl⟩ : syracuseStep 1749991 = 2624987) B2624987
theorem B10663001 : Blo 1036608 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B2339963 : Blo 1036608 2339963 := bstep (se 1 (by rfl) ⟨1754972, by rfl⟩ : syracuseStep 2339963 = 3509945) B3509945
theorem B2340089 : Blo 1036608 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B4437287 : Blo 1036608 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B2340233 : Blo 1036608 2340233 := bstep (se 2 (by rfl) ⟨877587, by rfl⟩ : syracuseStep 2340233 = 1755175) B1755175
theorem B2340359 : Blo 1036608 2340359 := bstep (se 1 (by rfl) ⟨1755269, by rfl⟩ : syracuseStep 2340359 = 3510539) B3510539
theorem B5256737 : Blo 1036608 5256737 := bstep (se 2 (by rfl) ⟨1971276, by rfl⟩ : syracuseStep 5256737 = 3942553) B3942553
theorem B2963101 : Blo 1036608 2963101 := bstep (se 3 (by rfl) ⟨555581, by rfl⟩ : syracuseStep 2963101 = 1111163) B1111163
theorem B8107705 : Blo 1036608 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B2340539 : Blo 1036608 2340539 := bstep (se 1 (by rfl) ⟨1755404, by rfl⟩ : syracuseStep 2340539 = 3510809) B3510809
theorem B2340665 : Blo 1036608 2340665 := bstep (se 2 (by rfl) ⟨877749, by rfl⟩ : syracuseStep 2340665 = 1755499) B1755499
theorem B4732759 : Blo 1036608 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B18921401 : Blo 1036608 18921401 := bstep (se 2 (by rfl) ⟨7095525, by rfl⟩ : syracuseStep 18921401 = 14191051) B14191051
theorem B4438415 : Blo 1036608 4438415 := bstep (se 1 (by rfl) ⟨3328811, by rfl⟩ : syracuseStep 4438415 = 6657623) B6657623
theorem B2341295 : Blo 1036608 2341295 := bstep (se 1 (by rfl) ⟨1755971, by rfl⟩ : syracuseStep 2341295 = 3511943) B3511943
theorem B2341331 : Blo 1036608 2341331 := bstep (se 1 (by rfl) ⟨1755998, by rfl⟩ : syracuseStep 2341331 = 3511997) B3511997
theorem B1555007 : Blo 1036608 1555007 := bstep (se 1 (by rfl) ⟨1166255, by rfl⟩ : syracuseStep 1555007 = 2332511) B2332511
theorem B11221679 : Blo 1036608 11221679 := bstep (se 1 (by rfl) ⟨8416259, by rfl⟩ : syracuseStep 11221679 = 16832519) B16832519
theorem B1555127 : Blo 1036608 1555127 := bstep (se 1 (by rfl) ⟨1166345, by rfl⟩ : syracuseStep 1555127 = 2332691) B2332691
theorem B5913283 : Blo 1036608 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B1555355 : Blo 1036608 1555355 := bstep (se 1 (by rfl) ⟨1166516, by rfl⟩ : syracuseStep 1555355 = 2333033) B2333033
theorem B16006193 : Blo 1036608 16006193 := bstep (se 2 (by rfl) ⟨6002322, by rfl⟩ : syracuseStep 16006193 = 12004645) B12004645
theorem B22756403 : Blo 1036608 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B1555751 : Blo 1036608 1555751 := bstep (se 1 (by rfl) ⟨1166813, by rfl⟩ : syracuseStep 1555751 = 2333627) B2333627
theorem B7880003 : Blo 1036608 7880003 := bstep (se 1 (by rfl) ⟨5910002, by rfl⟩ : syracuseStep 7880003 = 11820005) B11820005
theorem B1555835 : Blo 1036608 1555835 := bstep (se 1 (by rfl) ⟨1166876, by rfl⟩ : syracuseStep 1555835 = 2333753) B2333753
theorem B1555961 : Blo 1036608 1555961 := bstep (se 2 (by rfl) ⟨583485, by rfl⟩ : syracuseStep 1555961 = 1166971) B1166971
theorem B1556063 : Blo 1036608 1556063 := bstep (se 1 (by rfl) ⟨1167047, by rfl⟩ : syracuseStep 1556063 = 2334095) B2334095
theorem B1752671 : Blo 1036608 1752671 := bstep (se 1 (by rfl) ⟨1314503, by rfl⟩ : syracuseStep 1752671 = 2629007) B2629007
theorem B7880489 : Blo 1036608 7880489 := bstep (se 2 (by rfl) ⟨2955183, by rfl⟩ : syracuseStep 7880489 = 5910367) B5910367
theorem B1556279 : Blo 1036608 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B1752887 : Blo 1036608 1752887 := bstep (se 1 (by rfl) ⟨1314665, by rfl⟩ : syracuseStep 1752887 = 2629331) B2629331
theorem B4440089 : Blo 1036608 4440089 := bstep (se 2 (by rfl) ⟨1665033, by rfl⟩ : syracuseStep 4440089 = 3330067) B3330067
theorem B1556585 : Blo 1036608 1556585 := bstep (se 2 (by rfl) ⟨583719, by rfl⟩ : syracuseStep 1556585 = 1167439) B1167439
theorem B8864153 : Blo 1036608 8864153 := bstep (se 2 (by rfl) ⟨3324057, by rfl⟩ : syracuseStep 8864153 = 6648115) B6648115
theorem B1556903 : Blo 1036608 1556903 := bstep (se 1 (by rfl) ⟨1167677, by rfl⟩ : syracuseStep 1556903 = 2335355) B2335355
theorem B1556987 : Blo 1036608 1556987 := bstep (se 1 (by rfl) ⟨1167740, by rfl⟩ : syracuseStep 1556987 = 2335481) B2335481
theorem B1753663 : Blo 1036608 1753663 := bstep (se 1 (by rfl) ⟨1315247, by rfl⟩ : syracuseStep 1753663 = 2630495) B2630495
theorem B1557113 : Blo 1036608 1557113 := bstep (se 2 (by rfl) ⟨583917, by rfl⟩ : syracuseStep 1557113 = 1167835) B1167835
theorem B1557167 : Blo 1036608 1557167 := bstep (se 1 (by rfl) ⟨1167875, by rfl⟩ : syracuseStep 1557167 = 2335751) B2335751
theorem B1557215 : Blo 1036608 1557215 := bstep (se 1 (by rfl) ⟨1167911, by rfl⟩ : syracuseStep 1557215 = 2335823) B2335823
theorem B1557479 : Blo 1036608 1557479 := bstep (se 1 (by rfl) ⟨1168109, by rfl⟩ : syracuseStep 1557479 = 2336219) B2336219
theorem B1557737 : Blo 1036608 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B1754345 : Blo 1036608 1754345 := bstep (se 2 (by rfl) ⟨657879, by rfl⟩ : syracuseStep 1754345 = 1315759) B1315759
theorem B1557791 : Blo 1036608 1557791 := bstep (se 1 (by rfl) ⟨1168343, by rfl⟩ : syracuseStep 1557791 = 2336687) B2336687
theorem B1754399 : Blo 1036608 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B4441387 : Blo 1036608 4441387 := bstep (se 1 (by rfl) ⟨3331040, by rfl⟩ : syracuseStep 4441387 = 6662081) B6662081
theorem B1557959 : Blo 1036608 1557959 := bstep (se 1 (by rfl) ⟨1168469, by rfl⟩ : syracuseStep 1557959 = 2336939) B2336939
theorem B1558313 : Blo 1036608 1558313 := bstep (se 2 (by rfl) ⟨584367, by rfl⟩ : syracuseStep 1558313 = 1168735) B1168735
theorem B1558319 : Blo 1036608 1558319 := bstep (se 1 (by rfl) ⟨1168739, by rfl⟩ : syracuseStep 1558319 = 2337479) B2337479
theorem B5261111 : Blo 1036608 5261111 := bstep (se 1 (by rfl) ⟨3945833, by rfl⟩ : syracuseStep 5261111 = 7891667) B7891667
theorem B1558793 : Blo 1036608 1558793 := bstep (se 2 (by rfl) ⟨584547, by rfl⟩ : syracuseStep 1558793 = 1169095) B1169095
theorem B5261597 : Blo 1036608 5261597 := bstep (se 3 (by rfl) ⟨986549, by rfl⟩ : syracuseStep 5261597 = 1973099) B1973099
theorem B1558895 : Blo 1036608 1558895 := bstep (se 1 (by rfl) ⟨1169171, by rfl⟩ : syracuseStep 1558895 = 2338343) B2338343
theorem B5917157 : Blo 1036608 5917157 := bstep (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) B1109467
theorem B9488869 : Blo 1036608 9488869 := bstep (se 4 (by rfl) ⟨889581, by rfl⟩ : syracuseStep 9488869 = 1779163) B1779163
theorem B4442687 : Blo 1036608 4442687 := bstep (se 1 (by rfl) ⟨3332015, by rfl⟩ : syracuseStep 4442687 = 6664031) B6664031
theorem B1559111 : Blo 1036608 1559111 := bstep (se 1 (by rfl) ⟨1169333, by rfl⟩ : syracuseStep 1559111 = 2338667) B2338667
theorem B1559147 : Blo 1036608 1559147 := bstep (se 1 (by rfl) ⟨1169360, by rfl⟩ : syracuseStep 1559147 = 2338721) B2338721
theorem B1755769 : Blo 1036608 1755769 := bstep (se 2 (by rfl) ⟨658413, by rfl⟩ : syracuseStep 1755769 = 1316827) B1316827
theorem B1755823 : Blo 1036608 1755823 := bstep (se 1 (by rfl) ⟨1316867, by rfl⟩ : syracuseStep 1755823 = 2633735) B2633735
theorem B8407799 : Blo 1036608 8407799 := bstep (se 1 (by rfl) ⟨6305849, by rfl⟩ : syracuseStep 8407799 = 12611699) B12611699
theorem B4999927 : Blo 1036608 4999927 := bstep (se 1 (by rfl) ⟨3749945, by rfl⟩ : syracuseStep 4999927 = 7499891) B7499891
theorem B1559375 : Blo 1036608 1559375 := bstep (se 1 (by rfl) ⟨1169531, by rfl⟩ : syracuseStep 1559375 = 2339063) B2339063
theorem B1166287 : Blo 1036608 1166287 := bstep (se 1 (by rfl) ⟨874715, by rfl⟩ : syracuseStep 1166287 = 1749431) B1749431
theorem B7883891 : Blo 1036608 7883891 := bstep (se 1 (by rfl) ⟨5912918, by rfl⟩ : syracuseStep 7883891 = 11825837) B11825837
theorem B2804879 : Blo 1036608 2804879 := bstep (se 1 (by rfl) ⟨2103659, by rfl⟩ : syracuseStep 2804879 = 4207319) B4207319
theorem B1559771 : Blo 1036608 1559771 := bstep (se 1 (by rfl) ⟨1169828, by rfl⟩ : syracuseStep 1559771 = 2339657) B2339657
theorem B1166683 : Blo 1036608 1166683 := bstep (se 1 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 1166683 = 1750025) B1750025
theorem B8867191 : Blo 1036608 8867191 := bstep (se 1 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 8867191 = 13300787) B13300787
theorem B1559945 : Blo 1036608 1559945 := bstep (se 2 (by rfl) ⟨584979, by rfl⟩ : syracuseStep 1559945 = 1169959) B1169959
theorem B1166791 : Blo 1036608 1166791 := bstep (se 1 (by rfl) ⟨875093, by rfl⟩ : syracuseStep 1166791 = 1750187) B1750187
theorem B5328443 : Blo 1036608 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B1560299 : Blo 1036608 1560299 := bstep (se 1 (by rfl) ⟨1170224, by rfl⟩ : syracuseStep 1560299 = 2340449) B2340449
theorem B1167151 : Blo 1036608 1167151 := bstep (se 1 (by rfl) ⟨875363, by rfl⟩ : syracuseStep 1167151 = 1750727) B1750727
theorem B4214585 : Blo 1036608 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B1167259 : Blo 1036608 1167259 := bstep (se 1 (by rfl) ⟨875444, by rfl⟩ : syracuseStep 1167259 = 1750889) B1750889
theorem B1560527 : Blo 1036608 1560527 := bstep (se 1 (by rfl) ⟨1170395, by rfl⟩ : syracuseStep 1560527 = 2340791) B2340791
theorem B5263379 : Blo 1036608 5263379 := bstep (se 1 (by rfl) ⟨3947534, by rfl⟩ : syracuseStep 5263379 = 7895069) B7895069
theorem B1167655 : Blo 1036608 1167655 := bstep (se 1 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 1167655 = 1751483) B1751483
theorem B1036635 : Blo 1036608 1036635 := bstep (se 1 (by rfl) ⟨777476, by rfl⟩ : syracuseStep 1036635 = 1554953) B1554953
theorem B1036655 : Blo 1036608 1036655 := bstep (se 1 (by rfl) ⟨777491, by rfl⟩ : syracuseStep 1036655 = 1554983) B1554983
theorem B1167727 : Blo 1036608 1167727 := bstep (se 1 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 1167727 = 1751591) B1751591
theorem B1036711 : Blo 1036608 1036711 := bstep (se 1 (by rfl) ⟨777533, by rfl⟩ : syracuseStep 1036711 = 1555067) B1555067
theorem B1036795 : Blo 1036608 1036795 := bstep (se 1 (by rfl) ⟨777596, by rfl⟩ : syracuseStep 1036795 = 1555193) B1555193
theorem B11227693 : Blo 1036608 11227693 := bstep (se 3 (by rfl) ⟨2105192, by rfl⟩ : syracuseStep 11227693 = 4210385) B4210385
theorem B1036863 : Blo 1036608 1036863 := bstep (se 1 (by rfl) ⟨777647, by rfl⟩ : syracuseStep 1036863 = 1555295) B1555295
theorem B1036871 : Blo 1036608 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B1167943 : Blo 1036608 1167943 := bstep (se 1 (by rfl) ⟨875957, by rfl⟩ : syracuseStep 1167943 = 1751915) B1751915
theorem B1037023 : Blo 1036608 1037023 := bstep (se 1 (by rfl) ⟨777767, by rfl⟩ : syracuseStep 1037023 = 1555535) B1555535
theorem B1037103 : Blo 1036608 1037103 := bstep (se 1 (by rfl) ⟨777827, by rfl⟩ : syracuseStep 1037103 = 1555655) B1555655
theorem B1037211 : Blo 1036608 1037211 := bstep (se 1 (by rfl) ⟨777908, by rfl⟩ : syracuseStep 1037211 = 1555817) B1555817
theorem B1037263 : Blo 1036608 1037263 := bstep (se 1 (by rfl) ⟨777947, by rfl⟩ : syracuseStep 1037263 = 1555895) B1555895
theorem B1037287 : Blo 1036608 1037287 := bstep (se 1 (by rfl) ⟨777965, by rfl⟩ : syracuseStep 1037287 = 1555931) B1555931
theorem B7492765 : Blo 1036608 7492765 := bstep (se 3 (by rfl) ⟨1404893, by rfl⟩ : syracuseStep 7492765 = 2809787) B2809787
theorem B1037599 : Blo 1036608 1037599 := bstep (se 1 (by rfl) ⟨778199, by rfl⟩ : syracuseStep 1037599 = 1556399) B1556399
theorem B1037659 : Blo 1036608 1037659 := bstep (se 1 (by rfl) ⟨778244, by rfl⟩ : syracuseStep 1037659 = 1556489) B1556489
theorem B2217311 : Blo 1036608 2217311 := bstep (se 1 (by rfl) ⟨1662983, by rfl⟩ : syracuseStep 2217311 = 3325967) B3325967
theorem B1037679 : Blo 1036608 1037679 := bstep (se 1 (by rfl) ⟨778259, by rfl⟩ : syracuseStep 1037679 = 1556519) B1556519
theorem B3331451 : Blo 1036608 3331451 := bstep (se 1 (by rfl) ⟨2498588, by rfl⟩ : syracuseStep 3331451 = 4997177) B4997177
theorem B1037735 : Blo 1036608 1037735 := bstep (se 1 (by rfl) ⟨778301, by rfl⟩ : syracuseStep 1037735 = 1556603) B1556603
theorem B1168807 : Blo 1036608 1168807 := bstep (se 1 (by rfl) ⟨876605, by rfl⟩ : syracuseStep 1168807 = 1753211) B1753211
theorem B7493057 : Blo 1036608 7493057 := bstep (se 2 (by rfl) ⟨2809896, by rfl⟩ : syracuseStep 7493057 = 5619793) B5619793
theorem B1037819 : Blo 1036608 1037819 := bstep (se 1 (by rfl) ⟨778364, by rfl⟩ : syracuseStep 1037819 = 1556729) B1556729
theorem B1037887 : Blo 1036608 1037887 := bstep (se 1 (by rfl) ⟨778415, by rfl⟩ : syracuseStep 1037887 = 1556831) B1556831
theorem B1037895 : Blo 1036608 1037895 := bstep (se 1 (by rfl) ⟨778421, by rfl⟩ : syracuseStep 1037895 = 1556843) B1556843
theorem B17749691 : Blo 1036608 17749691 := bstep (se 1 (by rfl) ⟨13312268, by rfl⟩ : syracuseStep 17749691 = 26624537) B26624537
theorem B1038047 : Blo 1036608 1038047 := bstep (se 1 (by rfl) ⟨778535, by rfl⟩ : syracuseStep 1038047 = 1557071) B1557071
theorem B1038127 : Blo 1036608 1038127 := bstep (se 1 (by rfl) ⟨778595, by rfl⟩ : syracuseStep 1038127 = 1557191) B1557191
theorem B1038235 : Blo 1036608 1038235 := bstep (se 1 (by rfl) ⟨778676, by rfl⟩ : syracuseStep 1038235 = 1557353) B1557353
theorem B22501313 : Blo 1036608 22501313 := bstep (se 2 (by rfl) ⟨8437992, by rfl⟩ : syracuseStep 22501313 = 16875985) B16875985
theorem B1038287 : Blo 1036608 1038287 := bstep (se 1 (by rfl) ⟨778715, by rfl⟩ : syracuseStep 1038287 = 1557431) B1557431
theorem B1038311 : Blo 1036608 1038311 := bstep (se 1 (by rfl) ⟨778733, by rfl⟩ : syracuseStep 1038311 = 1557467) B1557467
theorem B1169383 : Blo 1036608 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B5920847 : Blo 1036608 5920847 := bstep (se 1 (by rfl) ⟨4440635, by rfl⟩ : syracuseStep 5920847 = 8881271) B8881271
theorem B4217017 : Blo 1036608 4217017 := bstep (se 2 (by rfl) ⟨1581381, by rfl⟩ : syracuseStep 4217017 = 3162763) B3162763
theorem B1038623 : Blo 1036608 1038623 := bstep (se 1 (by rfl) ⟨778967, by rfl⟩ : syracuseStep 1038623 = 1557935) B1557935
theorem B1038683 : Blo 1036608 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B1038703 : Blo 1036608 1038703 := bstep (se 1 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 1038703 = 1558055) B1558055
theorem B1038759 : Blo 1036608 1038759 := bstep (se 1 (by rfl) ⟨779069, by rfl⟩ : syracuseStep 1038759 = 1558139) B1558139
theorem B1038843 : Blo 1036608 1038843 := bstep (se 1 (by rfl) ⟨779132, by rfl⟩ : syracuseStep 1038843 = 1558265) B1558265
theorem B1038911 : Blo 1036608 1038911 := bstep (se 1 (by rfl) ⟨779183, by rfl⟩ : syracuseStep 1038911 = 1558367) B1558367
theorem B1038919 : Blo 1036608 1038919 := bstep (se 1 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 1038919 = 1558379) B1558379
theorem B3332681 : Blo 1036608 3332681 := bstep (se 2 (by rfl) ⟨1249755, by rfl⟩ : syracuseStep 3332681 = 2499511) B2499511
theorem B3332783 : Blo 1036608 3332783 := bstep (se 1 (by rfl) ⟨2499587, by rfl⟩ : syracuseStep 3332783 = 4999175) B4999175
theorem B1039071 : Blo 1036608 1039071 := bstep (se 1 (by rfl) ⟨779303, by rfl⟩ : syracuseStep 1039071 = 1558607) B1558607
theorem B1039151 : Blo 1036608 1039151 := bstep (se 1 (by rfl) ⟨779363, by rfl⟩ : syracuseStep 1039151 = 1558727) B1558727
theorem B5266295 : Blo 1036608 5266295 := bstep (se 1 (by rfl) ⟨3949721, by rfl⟩ : syracuseStep 5266295 = 7899443) B7899443
theorem B1039259 : Blo 1036608 1039259 := bstep (se 1 (by rfl) ⟨779444, by rfl⟩ : syracuseStep 1039259 = 1558889) B1558889
theorem B1039311 : Blo 1036608 1039311 := bstep (se 1 (by rfl) ⟨779483, by rfl⟩ : syracuseStep 1039311 = 1558967) B1558967
theorem B1039335 : Blo 1036608 1039335 := bstep (se 1 (by rfl) ⟨779501, by rfl⟩ : syracuseStep 1039335 = 1559003) B1559003
theorem B1039647 : Blo 1036608 1039647 := bstep (se 1 (by rfl) ⟨779735, by rfl⟩ : syracuseStep 1039647 = 1559471) B1559471
theorem B1039707 : Blo 1036608 1039707 := bstep (se 1 (by rfl) ⟨779780, by rfl⟩ : syracuseStep 1039707 = 1559561) B1559561
theorem B1039727 : Blo 1036608 1039727 := bstep (se 1 (by rfl) ⟨779795, by rfl⟩ : syracuseStep 1039727 = 1559591) B1559591
theorem B60611975 : Blo 1036608 60611975 := bstep (se 1 (by rfl) ⟨45458981, by rfl⟩ : syracuseStep 60611975 = 90917963) B90917963
theorem B7888265 : Blo 1036608 7888265 := bstep (se 2 (by rfl) ⟨2958099, by rfl⟩ : syracuseStep 7888265 = 5916199) B5916199
theorem B1039783 : Blo 1036608 1039783 := bstep (se 1 (by rfl) ⟨779837, by rfl⟩ : syracuseStep 1039783 = 1559675) B1559675
theorem B1039867 : Blo 1036608 1039867 := bstep (se 1 (by rfl) ⟨779900, by rfl⟩ : syracuseStep 1039867 = 1559801) B1559801
theorem B1039935 : Blo 1036608 1039935 := bstep (se 1 (by rfl) ⟨779951, by rfl⟩ : syracuseStep 1039935 = 1559903) B1559903
theorem B1039943 : Blo 1036608 1039943 := bstep (se 1 (by rfl) ⟨779957, by rfl⟩ : syracuseStep 1039943 = 1559915) B1559915
theorem B2252371 : Blo 1036608 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B3366515 : Blo 1036608 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B5267105 : Blo 1036608 5267105 := bstep (se 2 (by rfl) ⟨1975164, by rfl⟩ : syracuseStep 5267105 = 3950329) B3950329
theorem B1040095 : Blo 1036608 1040095 := bstep (se 1 (by rfl) ⟨780071, by rfl⟩ : syracuseStep 1040095 = 1560143) B1560143
theorem B17719073 : Blo 1036608 17719073 := bstep (se 2 (by rfl) ⟨6644652, by rfl⟩ : syracuseStep 17719073 = 13289305) B13289305
theorem B18013985 : Blo 1036608 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1040175 : Blo 1036608 1040175 := bstep (se 1 (by rfl) ⟨780131, by rfl⟩ : syracuseStep 1040175 = 1560263) B1560263
theorem B1040283 : Blo 1036608 1040283 := bstep (se 1 (by rfl) ⟨780212, by rfl⟩ : syracuseStep 1040283 = 1560425) B1560425
theorem B1040335 : Blo 1036608 1040335 := bstep (se 1 (by rfl) ⟨780251, by rfl⟩ : syracuseStep 1040335 = 1560503) B1560503
theorem B1040359 : Blo 1036608 1040359 := bstep (se 1 (by rfl) ⟨780269, by rfl⟩ : syracuseStep 1040359 = 1560539) B1560539
theorem B2809865 : Blo 1036608 2809865 := bstep (se 2 (by rfl) ⟨1053699, by rfl⟩ : syracuseStep 2809865 = 2107399) B2107399
theorem B2809961 : Blo 1036608 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B11821463 : Blo 1036608 11821463 := bstep (se 1 (by rfl) ⟨8866097, by rfl⟩ : syracuseStep 11821463 = 17732195) B17732195
theorem B2220455 : Blo 1036608 2220455 := bstep (se 1 (by rfl) ⟨1665341, by rfl⟩ : syracuseStep 2220455 = 3330683) B3330683
theorem B4743851 : Blo 1036608 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B7889723 : Blo 1036608 7889723 := bstep (se 1 (by rfl) ⟨5917292, by rfl⟩ : syracuseStep 7889723 = 11834585) B11834585
theorem B3498983 : Blo 1036608 3498983 := bstep (se 1 (by rfl) ⟨2624237, by rfl⟩ : syracuseStep 3498983 = 5248475) B5248475
theorem B3499307 : Blo 1036608 3499307 := bstep (se 1 (by rfl) ⟨2624480, by rfl⟩ : syracuseStep 3499307 = 5248961) B5248961
theorem B3499577 : Blo 1036608 3499577 := bstep (se 2 (by rfl) ⟨1312341, by rfl⟩ : syracuseStep 3499577 = 2624683) B2624683
theorem B13330007 : Blo 1036608 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B17754065 : Blo 1036608 17754065 := bstep (se 2 (by rfl) ⟨6657774, by rfl⟩ : syracuseStep 17754065 = 13315549) B13315549
theorem B8415485 : Blo 1036608 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B3500819 : Blo 1036608 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B9006157 : Blo 1036608 9006157 := bstep (se 3 (by rfl) ⟨1688654, by rfl⟩ : syracuseStep 9006157 = 3377309) B3377309
theorem B11234483 : Blo 1036608 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B10644767 : Blo 1036608 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B11234825 : Blo 1036608 11234825 := bstep (se 2 (by rfl) ⟨4213059, by rfl⟩ : syracuseStep 11234825 = 8426119) B8426119
theorem B3501683 : Blo 1036608 3501683 := bstep (se 1 (by rfl) ⟨2626262, by rfl⟩ : syracuseStep 3501683 = 5252525) B5252525
theorem B6319883 : Blo 1036608 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B42594167 : Blo 1036608 42594167 := bstep (se 1 (by rfl) ⟨31945625, by rfl⟩ : syracuseStep 42594167 = 63891251) B63891251
theorem B3501953 : Blo 1036608 3501953 := bstep (se 2 (by rfl) ⟨1313232, by rfl⟩ : syracuseStep 3501953 = 2626465) B2626465
theorem B10646077 : Blo 1036608 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B3502763 : Blo 1036608 3502763 := bstep (se 1 (by rfl) ⟨2627072, by rfl⟩ : syracuseStep 3502763 = 5254145) B5254145
theorem B11531213 : Blo 1036608 11531213 := bstep (se 3 (by rfl) ⟨2162102, by rfl⟩ : syracuseStep 11531213 = 4324205) B4324205
theorem B3503303 : Blo 1036608 3503303 := bstep (se 1 (by rfl) ⟨2627477, by rfl⟩ : syracuseStep 3503303 = 5254955) B5254955
theorem B26572049 : Blo 1036608 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B2029369 : Blo 1036608 2029369 := bstep (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) B1522027
theorem B121534825 : Blo 1036608 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B3504815 : Blo 1036608 3504815 := bstep (se 1 (by rfl) ⟨2628611, by rfl⟩ : syracuseStep 3504815 = 5257223) B5257223
theorem B3505139 : Blo 1036608 3505139 := bstep (se 1 (by rfl) ⟨2628854, by rfl⟩ : syracuseStep 3505139 = 5257709) B5257709
theorem B6650909 : Blo 1036608 6650909 := bstep (se 3 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 6650909 = 2494091) B2494091
theorem B3505679 : Blo 1036608 3505679 := bstep (se 1 (by rfl) ⟨2629259, by rfl⟩ : syracuseStep 3505679 = 5258519) B5258519
theorem B9994043 : Blo 1036608 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B1246315 : Blo 1036608 1246315 := bstep (se 1 (by rfl) ⟨934736, by rfl⟩ : syracuseStep 1246315 = 1869473) B1869473
theorem B3507407 : Blo 1036608 3507407 := bstep (se 1 (by rfl) ⟨2630555, by rfl⟩ : syracuseStep 3507407 = 5261111) B5261111
theorem B56821115 : Blo 1036608 56821115 := bstep (se 1 (by rfl) ⟨42615836, by rfl⟩ : syracuseStep 56821115 = 85231673) B85231673
theorem B2491823 : Blo 1036608 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B3507731 : Blo 1036608 3507731 := bstep (se 1 (by rfl) ⟨2630798, by rfl⟩ : syracuseStep 3507731 = 5261597) B5261597
theorem B12650269 : Blo 1036608 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B1967951 : Blo 1036608 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B5605199 : Blo 1036608 5605199 := bstep (se 1 (by rfl) ⟨4203899, by rfl⟩ : syracuseStep 5605199 = 8407799) B8407799
theorem B7473161 : Blo 1036608 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B3508919 : Blo 1036608 3508919 := bstep (se 1 (by rfl) ⟨2631689, by rfl⟩ : syracuseStep 3508919 = 5263379) B5263379
theorem B2624633 : Blo 1036608 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B1478207 : Blo 1036608 1478207 := bstep (se 1 (by rfl) ⟨1108655, by rfl⟩ : syracuseStep 1478207 = 2217311) B2217311
theorem B26611415 : Blo 1036608 26611415 := bstep (se 1 (by rfl) ⟨19958561, by rfl⟩ : syracuseStep 26611415 = 39917123) B39917123
theorem B11833127 : Blo 1036608 11833127 := bstep (se 1 (by rfl) ⟨8874845, by rfl⟩ : syracuseStep 11833127 = 17749691) B17749691
theorem B3936509 : Blo 1036608 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B25301321 : Blo 1036608 25301321 := bstep (se 2 (by rfl) ⟨9487995, by rfl⟩ : syracuseStep 25301321 = 18975991) B18975991
theorem B2625929 : Blo 1036608 2625929 := bstep (se 2 (by rfl) ⟨984723, by rfl⟩ : syracuseStep 2625929 = 1969447) B1969447
theorem B3510863 : Blo 1036608 3510863 := bstep (se 1 (by rfl) ⟨2633147, by rfl⟩ : syracuseStep 3510863 = 5266295) B5266295
theorem B2495071 : Blo 1036608 2495071 := bstep (se 1 (by rfl) ⟨1871303, by rfl⟩ : syracuseStep 2495071 = 3742607) B3742607
theorem B40407983 : Blo 1036608 40407983 := bstep (se 1 (by rfl) ⟨30305987, by rfl⟩ : syracuseStep 40407983 = 60611975) B60611975
theorem B4428881 : Blo 1036608 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B1971307 : Blo 1036608 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B3511403 : Blo 1036608 3511403 := bstep (se 1 (by rfl) ⟨2633552, by rfl⟩ : syracuseStep 3511403 = 5267105) B5267105
theorem B38409427 : Blo 1036608 38409427 := bstep (se 1 (by rfl) ⟨28807070, by rfl⟩ : syracuseStep 38409427 = 57614141) B57614141
theorem B1873243 : Blo 1036608 1873243 := bstep (se 1 (by rfl) ⟨1404932, by rfl⟩ : syracuseStep 1873243 = 2809865) B2809865
theorem B1971611 : Blo 1036608 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1873307 : Blo 1036608 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B4986299 : Blo 1036608 4986299 := bstep (se 1 (by rfl) ⟨3739724, by rfl⟩ : syracuseStep 4986299 = 7479449) B7479449
theorem B1480303 : Blo 1036608 1480303 := bstep (se 1 (by rfl) ⟨1110227, by rfl⟩ : syracuseStep 1480303 = 2220455) B2220455
theorem B2627255 : Blo 1036608 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B2332655 : Blo 1036608 2332655 := bstep (se 1 (by rfl) ⟨1749491, by rfl⟩ : syracuseStep 2332655 = 3498983) B3498983
theorem B14194769 : Blo 1036608 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B2332871 : Blo 1036608 2332871 := bstep (se 1 (by rfl) ⟨1749653, by rfl⟩ : syracuseStep 2332871 = 3499307) B3499307
theorem B1579241 : Blo 1036608 1579241 := bstep (se 2 (by rfl) ⟨592215, by rfl⟩ : syracuseStep 1579241 = 1184431) B1184431
theorem B1644779 : Blo 1036608 1644779 := bstep (se 1 (by rfl) ⟨1233584, by rfl⟩ : syracuseStep 1644779 = 2467169) B2467169
theorem B2333051 : Blo 1036608 2333051 := bstep (se 1 (by rfl) ⟨1749788, by rfl⟩ : syracuseStep 2333051 = 3499577) B3499577
theorem B8886671 : Blo 1036608 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B2333321 : Blo 1036608 2333321 := bstep (se 2 (by rfl) ⟨874995, by rfl⟩ : syracuseStep 2333321 = 1749991) B1749991
theorem B11836043 : Blo 1036608 11836043 := bstep (se 1 (by rfl) ⟨8877032, by rfl⟩ : syracuseStep 11836043 = 17754065) B17754065
theorem B5610323 : Blo 1036608 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B8887421 : Blo 1036608 8887421 := bstep (se 3 (by rfl) ⟨1666391, by rfl⟩ : syracuseStep 8887421 = 3332783) B3332783
theorem B2333879 : Blo 1036608 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B9968825 : Blo 1036608 9968825 := bstep (se 2 (by rfl) ⟨3738309, by rfl⟩ : syracuseStep 9968825 = 7476619) B7476619
theorem B6659621 : Blo 1036608 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B2629199 : Blo 1036608 2629199 := bstep (se 1 (by rfl) ⟨1971899, by rfl⟩ : syracuseStep 2629199 = 3943799) B3943799
theorem B6757967 : Blo 1036608 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B2498273 : Blo 1036608 2498273 := bstep (se 2 (by rfl) ⟨936852, by rfl⟩ : syracuseStep 2498273 = 1873705) B1873705
theorem B2334455 : Blo 1036608 2334455 := bstep (se 1 (by rfl) ⟨1750841, by rfl⟩ : syracuseStep 2334455 = 3501683) B3501683
theorem B18947963 : Blo 1036608 18947963 := bstep (se 1 (by rfl) ⟨14210972, by rfl⟩ : syracuseStep 18947963 = 28421945) B28421945
theorem B2334635 : Blo 1036608 2334635 := bstep (se 1 (by rfl) ⟨1750976, by rfl⟩ : syracuseStep 2334635 = 3501953) B3501953
theorem B2957543 : Blo 1036608 2957543 := bstep (se 1 (by rfl) ⟨2218157, by rfl⟩ : syracuseStep 2957543 = 4436315) B4436315
theorem B7479677 : Blo 1036608 7479677 := bstep (se 3 (by rfl) ⟨1402439, by rfl⟩ : syracuseStep 7479677 = 2804879) B2804879
theorem B2335175 : Blo 1036608 2335175 := bstep (se 1 (by rfl) ⟨1751381, by rfl⟩ : syracuseStep 2335175 = 3502763) B3502763
theorem B162046433 : Blo 1036608 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B3744251 : Blo 1036608 3744251 := bstep (se 1 (by rfl) ⟨2808188, by rfl⟩ : syracuseStep 3744251 = 5616377) B5616377
theorem B2335535 : Blo 1036608 2335535 := bstep (se 1 (by rfl) ⟨1751651, by rfl⟩ : syracuseStep 2335535 = 3503303) B3503303
theorem B1975097 : Blo 1036608 1975097 := bstep (se 2 (by rfl) ⟨740661, by rfl⟩ : syracuseStep 1975097 = 1481323) B1481323
theorem B2958191 : Blo 1036608 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B2958943 : Blo 1036608 2958943 := bstep (se 1 (by rfl) ⟨2219207, by rfl⟩ : syracuseStep 2958943 = 4438415) B4438415
theorem B7481119 : Blo 1036608 7481119 := bstep (se 1 (by rfl) ⟨5610839, by rfl⟩ : syracuseStep 7481119 = 11221679) B11221679
theorem B2336543 : Blo 1036608 2336543 := bstep (se 1 (by rfl) ⟨1752407, by rfl⟩ : syracuseStep 2336543 = 3504815) B3504815
theorem B2336759 : Blo 1036608 2336759 := bstep (se 1 (by rfl) ⟨1752569, by rfl⟩ : syracuseStep 2336759 = 3505139) B3505139
theorem B4433939 : Blo 1036608 4433939 := bstep (se 1 (by rfl) ⟨3325454, by rfl⟩ : syracuseStep 4433939 = 6650909) B6650909
theorem B16853021 : Blo 1036608 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B11217005 : Blo 1036608 11217005 := bstep (se 3 (by rfl) ⟨2103188, by rfl⟩ : syracuseStep 11217005 = 4206377) B4206377
theorem B26650781 : Blo 1036608 26650781 := bstep (se 3 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 26650781 = 9994043) B9994043
theorem B5253335 : Blo 1036608 5253335 := bstep (se 1 (by rfl) ⟨3940001, by rfl⟩ : syracuseStep 5253335 = 7880003) B7880003
theorem B2337119 : Blo 1036608 2337119 := bstep (se 1 (by rfl) ⟨1752839, by rfl⟩ : syracuseStep 2337119 = 3505679) B3505679
theorem B5253659 : Blo 1036608 5253659 := bstep (se 1 (by rfl) ⟨3940244, by rfl⟩ : syracuseStep 5253659 = 7880489) B7880489
theorem B2632297 : Blo 1036608 2632297 := bstep (se 2 (by rfl) ⟨987111, by rfl⟩ : syracuseStep 2632297 = 1974223) B1974223
theorem B2960059 : Blo 1036608 2960059 := bstep (se 1 (by rfl) ⟨2220044, by rfl⟩ : syracuseStep 2960059 = 4440089) B4440089
theorem B5909435 : Blo 1036608 5909435 := bstep (se 1 (by rfl) ⟨4432076, by rfl⟩ : syracuseStep 5909435 = 8864153) B8864153
theorem B2337839 : Blo 1036608 2337839 := bstep (se 1 (by rfl) ⟨1753379, by rfl⟩ : syracuseStep 2337839 = 3506759) B3506759
theorem B2338127 : Blo 1036608 2338127 := bstep (se 1 (by rfl) ⟨1753595, by rfl⟩ : syracuseStep 2338127 = 3507191) B3507191
theorem B2338217 : Blo 1036608 2338217 := bstep (se 2 (by rfl) ⟨876831, by rfl⟩ : syracuseStep 2338217 = 1753663) B1753663
theorem B2633593 : Blo 1036608 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B2338703 : Blo 1036608 2338703 := bstep (se 1 (by rfl) ⟨1754027, by rfl⟩ : syracuseStep 2338703 = 3508055) B3508055
theorem B4435955 : Blo 1036608 4435955 := bstep (se 1 (by rfl) ⟨3326966, by rfl⟩ : syracuseStep 4435955 = 6653933) B6653933
theorem B3944771 : Blo 1036608 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B2961791 : Blo 1036608 2961791 := bstep (se 1 (by rfl) ⟨2221343, by rfl⟩ : syracuseStep 2961791 = 4442687) B4442687
theorem B2339423 : Blo 1036608 2339423 := bstep (se 1 (by rfl) ⟨1754567, by rfl⟩ : syracuseStep 2339423 = 3509135) B3509135
theorem B5255927 : Blo 1036608 5255927 := bstep (se 1 (by rfl) ⟨3941945, by rfl⟩ : syracuseStep 5255927 = 7883891) B7883891
theorem B1750079 : Blo 1036608 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B50607301 : Blo 1036608 50607301 := bstep (se 4 (by rfl) ⟨4744434, by rfl⟩ : syracuseStep 50607301 = 9488869) B9488869
theorem B2340251 : Blo 1036608 2340251 := bstep (se 1 (by rfl) ⟨1755188, by rfl⟩ : syracuseStep 2340251 = 3510377) B3510377
theorem B1750639 : Blo 1036608 1750639 := bstep (se 1 (by rfl) ⟨1312979, by rfl⟩ : syracuseStep 1750639 = 2625959) B2625959
theorem B1750747 : Blo 1036608 1750747 := bstep (se 1 (by rfl) ⟨1313060, by rfl⟩ : syracuseStep 1750747 = 2626121) B2626121
theorem B7878545 : Blo 1036608 7878545 := bstep (se 2 (by rfl) ⟨2954454, by rfl⟩ : syracuseStep 7878545 = 5908909) B5908909
theorem B2340827 : Blo 1036608 2340827 := bstep (se 1 (by rfl) ⟨1755620, by rfl⟩ : syracuseStep 2340827 = 3511241) B3511241
theorem B2341007 : Blo 1036608 2341007 := bstep (se 1 (by rfl) ⟨1755755, by rfl⟩ : syracuseStep 2341007 = 3511511) B3511511
theorem B2341025 : Blo 1036608 2341025 := bstep (se 2 (by rfl) ⟨877884, by rfl⟩ : syracuseStep 2341025 = 1755769) B1755769
theorem B2341097 : Blo 1036608 2341097 := bstep (se 2 (by rfl) ⟨877911, by rfl⟩ : syracuseStep 2341097 = 1755823) B1755823
theorem B4995371 : Blo 1036608 4995371 := bstep (se 1 (by rfl) ⟨3746528, by rfl⟩ : syracuseStep 4995371 = 7493057) B7493057
theorem B6666569 : Blo 1036608 6666569 := bstep (se 2 (by rfl) ⟨2499963, by rfl⟩ : syracuseStep 6666569 = 4999927) B4999927
theorem B1554971 : Blo 1036608 1554971 := bstep (se 1 (by rfl) ⟨1166228, by rfl⟩ : syracuseStep 1554971 = 2332457) B2332457
theorem B1555049 : Blo 1036608 1555049 := bstep (se 2 (by rfl) ⟨583143, by rfl⟩ : syracuseStep 1555049 = 1166287) B1166287
theorem B3947231 : Blo 1036608 3947231 := bstep (se 1 (by rfl) ⟨2960423, by rfl⟩ : syracuseStep 3947231 = 5920847) B5920847
theorem B12008209 : Blo 1036608 12008209 := bstep (se 2 (by rfl) ⟨4503078, by rfl⟩ : syracuseStep 12008209 = 9006157) B9006157
theorem B1752043 : Blo 1036608 1752043 := bstep (se 1 (by rfl) ⟨1314032, by rfl⟩ : syracuseStep 1752043 = 2628065) B2628065
theorem B1555577 : Blo 1036608 1555577 := bstep (se 2 (by rfl) ⟨583341, by rfl⟩ : syracuseStep 1555577 = 1166683) B1166683
theorem B1752185 : Blo 1036608 1752185 := bstep (se 2 (by rfl) ⟨657069, by rfl⟩ : syracuseStep 1752185 = 1314139) B1314139
theorem B1424567 : Blo 1036608 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B1555679 : Blo 1036608 1555679 := bstep (se 1 (by rfl) ⟨1166759, by rfl⟩ : syracuseStep 1555679 = 2333519) B2333519
theorem B1555721 : Blo 1036608 1555721 := bstep (se 2 (by rfl) ⟨583395, by rfl⟩ : syracuseStep 1555721 = 1166791) B1166791
theorem B1555823 : Blo 1036608 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B1555943 : Blo 1036608 1555943 := bstep (se 1 (by rfl) ⟨1166957, by rfl⟩ : syracuseStep 1555943 = 2333915) B2333915
theorem B3325531 : Blo 1036608 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B5258843 : Blo 1036608 5258843 := bstep (se 1 (by rfl) ⟨3944132, by rfl⟩ : syracuseStep 5258843 = 7888265) B7888265
theorem B1556075 : Blo 1036608 1556075 := bstep (se 1 (by rfl) ⟨1167056, by rfl⟩ : syracuseStep 1556075 = 2334113) B2334113
theorem B1556201 : Blo 1036608 1556201 := bstep (se 2 (by rfl) ⟨583575, by rfl⟩ : syracuseStep 1556201 = 1167151) B1167151
theorem B2244343 : Blo 1036608 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B11812715 : Blo 1036608 11812715 := bstep (se 1 (by rfl) ⟨8859536, by rfl⟩ : syracuseStep 11812715 = 17719073) B17719073
theorem B12009323 : Blo 1036608 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B1556345 : Blo 1036608 1556345 := bstep (se 2 (by rfl) ⟨583629, by rfl⟩ : syracuseStep 1556345 = 1167259) B1167259
theorem B1556447 : Blo 1036608 1556447 := bstep (se 1 (by rfl) ⟨1167335, by rfl⟩ : syracuseStep 1556447 = 2334671) B2334671
theorem B6307865 : Blo 1036608 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B1556699 : Blo 1036608 1556699 := bstep (se 1 (by rfl) ⟨1167524, by rfl⟩ : syracuseStep 1556699 = 2335049) B2335049
theorem B1556711 : Blo 1036608 1556711 := bstep (se 1 (by rfl) ⟨1167533, by rfl⟩ : syracuseStep 1556711 = 2335067) B2335067
theorem B1753319 : Blo 1036608 1753319 := bstep (se 1 (by rfl) ⟨1314989, by rfl⟩ : syracuseStep 1753319 = 2629979) B2629979
theorem B7880975 : Blo 1036608 7880975 := bstep (se 1 (by rfl) ⟨5910731, by rfl⟩ : syracuseStep 7880975 = 11821463) B11821463
theorem B1556873 : Blo 1036608 1556873 := bstep (se 2 (by rfl) ⟨583827, by rfl⟩ : syracuseStep 1556873 = 1167655) B1167655
theorem B1753481 : Blo 1036608 1753481 := bstep (se 2 (by rfl) ⟨657555, by rfl⟩ : syracuseStep 1753481 = 1315111) B1315111
theorem B1556969 : Blo 1036608 1556969 := bstep (se 2 (by rfl) ⟨583863, by rfl⟩ : syracuseStep 1556969 = 1167727) B1167727
theorem B5259815 : Blo 1036608 5259815 := bstep (se 1 (by rfl) ⟨3944861, by rfl⟩ : syracuseStep 5259815 = 7889723) B7889723
theorem B1557095 : Blo 1036608 1557095 := bstep (se 1 (by rfl) ⟨1167821, by rfl⟩ : syracuseStep 1557095 = 2335643) B2335643
theorem B1557227 : Blo 1036608 1557227 := bstep (se 1 (by rfl) ⟨1167920, by rfl⟩ : syracuseStep 1557227 = 2335841) B2335841
theorem B1557257 : Blo 1036608 1557257 := bstep (se 2 (by rfl) ⟨583971, by rfl⟩ : syracuseStep 1557257 = 1167943) B1167943
theorem B1753913 : Blo 1036608 1753913 := bstep (se 2 (by rfl) ⟨657717, by rfl⟩ : syracuseStep 1753913 = 1315435) B1315435
theorem B1557359 : Blo 1036608 1557359 := bstep (se 1 (by rfl) ⟨1168019, by rfl⟩ : syracuseStep 1557359 = 2336039) B2336039
theorem B1753967 : Blo 1036608 1753967 := bstep (se 1 (by rfl) ⟨1315475, by rfl⟩ : syracuseStep 1753967 = 2630951) B2630951
theorem B48022625 : Blo 1036608 48022625 := bstep (se 2 (by rfl) ⟨18008484, by rfl⟩ : syracuseStep 48022625 = 36016969) B36016969
theorem B1557611 : Blo 1036608 1557611 := bstep (se 1 (by rfl) ⟨1168208, by rfl⟩ : syracuseStep 1557611 = 2336417) B2336417
theorem B1557851 : Blo 1036608 1557851 := bstep (se 1 (by rfl) ⟨1168388, by rfl⟩ : syracuseStep 1557851 = 2336777) B2336777
theorem B1558127 : Blo 1036608 1558127 := bstep (se 1 (by rfl) ⟨1168595, by rfl⟩ : syracuseStep 1558127 = 2337191) B2337191
theorem B1558199 : Blo 1036608 1558199 := bstep (se 1 (by rfl) ⟨1168649, by rfl⟩ : syracuseStep 1558199 = 2337299) B2337299
theorem B1558235 : Blo 1036608 1558235 := bstep (se 1 (by rfl) ⟨1168676, by rfl⟩ : syracuseStep 1558235 = 2337353) B2337353
theorem B1754959 : Blo 1036608 1754959 := bstep (se 1 (by rfl) ⟨1316219, by rfl⟩ : syracuseStep 1754959 = 2632439) B2632439
theorem B1558409 : Blo 1036608 1558409 := bstep (se 2 (by rfl) ⟨584403, by rfl⟩ : syracuseStep 1558409 = 1168807) B1168807
theorem B1558511 : Blo 1036608 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B7489655 : Blo 1036608 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B7096511 : Blo 1036608 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B3950801 : Blo 1036608 3950801 := bstep (se 2 (by rfl) ⟨1481550, by rfl⟩ : syracuseStep 3950801 = 2963101) B2963101
theorem B1558763 : Blo 1036608 1558763 := bstep (se 1 (by rfl) ⟨1169072, by rfl⟩ : syracuseStep 1558763 = 2338145) B2338145
theorem B1755371 : Blo 1036608 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B1558823 : Blo 1036608 1558823 := bstep (se 1 (by rfl) ⟨1169117, by rfl⟩ : syracuseStep 1558823 = 2338235) B2338235
theorem B7489883 : Blo 1036608 7489883 := bstep (se 1 (by rfl) ⟨5617412, by rfl⟩ : syracuseStep 7489883 = 11234825) B11234825
theorem B1558907 : Blo 1036608 1558907 := bstep (se 1 (by rfl) ⟨1169180, by rfl⟩ : syracuseStep 1558907 = 2338361) B2338361
theorem B2705825 : Blo 1036608 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B6310345 : Blo 1036608 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B28396111 : Blo 1036608 28396111 := bstep (se 1 (by rfl) ⟨21297083, by rfl⟩ : syracuseStep 28396111 = 42594167) B42594167
theorem B1559177 : Blo 1036608 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B1559351 : Blo 1036608 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B1559387 : Blo 1036608 1559387 := bstep (se 1 (by rfl) ⟨1169540, by rfl⟩ : syracuseStep 1559387 = 2339081) B2339081
theorem B47893355 : Blo 1036608 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B15387527 : Blo 1036608 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B5622689 : Blo 1036608 5622689 := bstep (se 2 (by rfl) ⟨2108508, by rfl⟩ : syracuseStep 5622689 = 4217017) B4217017
theorem B1559531 : Blo 1036608 1559531 := bstep (se 1 (by rfl) ⟨1169648, by rfl⟩ : syracuseStep 1559531 = 2339297) B2339297
theorem B1559735 : Blo 1036608 1559735 := bstep (se 1 (by rfl) ⟨1169801, by rfl⟩ : syracuseStep 1559735 = 2339603) B2339603
theorem B7687475 : Blo 1036608 7687475 := bstep (se 1 (by rfl) ⟨5765606, by rfl⟩ : syracuseStep 7687475 = 11531213) B11531213
theorem B1559975 : Blo 1036608 1559975 := bstep (se 1 (by rfl) ⟨1169981, by rfl⟩ : syracuseStep 1559975 = 2339963) B2339963
theorem B1560059 : Blo 1036608 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B17714699 : Blo 1036608 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B7884377 : Blo 1036608 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B1560155 : Blo 1036608 1560155 := bstep (se 1 (by rfl) ⟨1170116, by rfl⟩ : syracuseStep 1560155 = 2340233) B2340233
theorem B1560239 : Blo 1036608 1560239 := bstep (se 1 (by rfl) ⟨1170179, by rfl⟩ : syracuseStep 1560239 = 2340359) B2340359
theorem B1560359 : Blo 1036608 1560359 := bstep (se 1 (by rfl) ⟨1170269, by rfl⟩ : syracuseStep 1560359 = 2340539) B2340539
theorem B1560443 : Blo 1036608 1560443 := bstep (se 1 (by rfl) ⟨1170332, by rfl⟩ : syracuseStep 1560443 = 2340665) B2340665
theorem B14209181 : Blo 1036608 14209181 := bstep (se 3 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 14209181 = 5328443) B5328443
theorem B1560863 : Blo 1036608 1560863 := bstep (se 1 (by rfl) ⟨1170647, by rfl⟩ : syracuseStep 1560863 = 2341295) B2341295
theorem B1560887 : Blo 1036608 1560887 := bstep (se 1 (by rfl) ⟨1170665, by rfl⟩ : syracuseStep 1560887 = 2341331) B2341331
theorem B1036671 : Blo 1036608 1036671 := bstep (se 1 (by rfl) ⟨777503, by rfl⟩ : syracuseStep 1036671 = 1555007) B1555007
theorem B1036751 : Blo 1036608 1036751 := bstep (se 1 (by rfl) ⟨777563, by rfl⟩ : syracuseStep 1036751 = 1555127) B1555127
theorem B1036903 : Blo 1036608 1036903 := bstep (se 1 (by rfl) ⟨777677, by rfl⟩ : syracuseStep 1036903 = 1555355) B1555355
theorem B9458365 : Blo 1036608 9458365 := bstep (se 3 (by rfl) ⟨1773443, by rfl⟩ : syracuseStep 9458365 = 3546887) B3546887
theorem B10670795 : Blo 1036608 10670795 := bstep (se 1 (by rfl) ⟨8003096, by rfl⟩ : syracuseStep 10670795 = 16006193) B16006193
theorem B3003161 : Blo 1036608 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B5264189 : Blo 1036608 5264189 := bstep (se 3 (by rfl) ⟨987035, by rfl⟩ : syracuseStep 5264189 = 1974071) B1974071
theorem B1037167 : Blo 1036608 1037167 := bstep (se 1 (by rfl) ⟨777875, by rfl⟩ : syracuseStep 1037167 = 1555751) B1555751
theorem B1037223 : Blo 1036608 1037223 := bstep (se 1 (by rfl) ⟨777917, by rfl⟩ : syracuseStep 1037223 = 1555835) B1555835
theorem B1037307 : Blo 1036608 1037307 := bstep (se 1 (by rfl) ⟨777980, by rfl⟩ : syracuseStep 1037307 = 1555961) B1555961
theorem B1037375 : Blo 1036608 1037375 := bstep (se 1 (by rfl) ⟨778031, by rfl⟩ : syracuseStep 1037375 = 1556063) B1556063
theorem B1168447 : Blo 1036608 1168447 := bstep (se 1 (by rfl) ⟨876335, by rfl⟩ : syracuseStep 1168447 = 1752671) B1752671
theorem B1037519 : Blo 1036608 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B1168591 : Blo 1036608 1168591 := bstep (se 1 (by rfl) ⟨876443, by rfl⟩ : syracuseStep 1168591 = 1752887) B1752887
theorem B1037723 : Blo 1036608 1037723 := bstep (se 1 (by rfl) ⟨778292, by rfl⟩ : syracuseStep 1037723 = 1556585) B1556585
theorem B1037935 : Blo 1036608 1037935 := bstep (se 1 (by rfl) ⟨778451, by rfl⟩ : syracuseStep 1037935 = 1556903) B1556903
theorem B1037991 : Blo 1036608 1037991 := bstep (se 1 (by rfl) ⟨778493, by rfl⟩ : syracuseStep 1037991 = 1556987) B1556987
theorem B1038075 : Blo 1036608 1038075 := bstep (se 1 (by rfl) ⟨778556, by rfl⟩ : syracuseStep 1038075 = 1557113) B1557113
theorem B1038111 : Blo 1036608 1038111 := bstep (se 1 (by rfl) ⟨778583, by rfl⟩ : syracuseStep 1038111 = 1557167) B1557167
theorem B1038143 : Blo 1036608 1038143 := bstep (se 1 (by rfl) ⟨778607, by rfl⟩ : syracuseStep 1038143 = 1557215) B1557215
theorem B7886807 : Blo 1036608 7886807 := bstep (se 1 (by rfl) ⟨5915105, by rfl⟩ : syracuseStep 7886807 = 11830211) B11830211
theorem B1038319 : Blo 1036608 1038319 := bstep (se 1 (by rfl) ⟨778739, by rfl⟩ : syracuseStep 1038319 = 1557479) B1557479
theorem B1661023 : Blo 1036608 1661023 := bstep (se 1 (by rfl) ⟨1245767, by rfl⟩ : syracuseStep 1661023 = 2491535) B2491535
theorem B1038491 : Blo 1036608 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B1169563 : Blo 1036608 1169563 := bstep (se 1 (by rfl) ⟨877172, by rfl⟩ : syracuseStep 1169563 = 1754345) B1754345
theorem B1038527 : Blo 1036608 1038527 := bstep (se 1 (by rfl) ⟨778895, by rfl⟩ : syracuseStep 1038527 = 1557791) B1557791
theorem B1169599 : Blo 1036608 1169599 := bstep (se 1 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 1169599 = 1754399) B1754399
theorem B67426577 : Blo 1036608 67426577 := bstep (se 2 (by rfl) ⟨25284966, by rfl⟩ : syracuseStep 67426577 = 50569933) B50569933
theorem B1038639 : Blo 1036608 1038639 := bstep (se 1 (by rfl) ⟨778979, by rfl⟩ : syracuseStep 1038639 = 1557959) B1557959
theorem B1038875 : Blo 1036608 1038875 := bstep (se 1 (by rfl) ⟨779156, by rfl⟩ : syracuseStep 1038875 = 1558313) B1558313
theorem B1038879 : Blo 1036608 1038879 := bstep (se 1 (by rfl) ⟨779159, by rfl⟩ : syracuseStep 1038879 = 1558319) B1558319
theorem B5265971 : Blo 1036608 5265971 := bstep (se 1 (by rfl) ⟨3949478, by rfl⟩ : syracuseStep 5265971 = 7898957) B7898957
theorem B1039195 : Blo 1036608 1039195 := bstep (se 1 (by rfl) ⟨779396, by rfl⟩ : syracuseStep 1039195 = 1558793) B1558793
theorem B1039263 : Blo 1036608 1039263 := bstep (se 1 (by rfl) ⟨779447, by rfl⟩ : syracuseStep 1039263 = 1558895) B1558895
theorem B13294637 : Blo 1036608 13294637 := bstep (se 3 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 13294637 = 4985489) B4985489
theorem B1039407 : Blo 1036608 1039407 := bstep (se 1 (by rfl) ⟨779555, by rfl⟩ : syracuseStep 1039407 = 1559111) B1559111
theorem B5921849 : Blo 1036608 5921849 := bstep (se 2 (by rfl) ⟨2220693, by rfl⟩ : syracuseStep 5921849 = 4441387) B4441387
theorem B1039431 : Blo 1036608 1039431 := bstep (se 1 (by rfl) ⟨779573, by rfl⟩ : syracuseStep 1039431 = 1559147) B1559147
theorem B1039583 : Blo 1036608 1039583 := bstep (se 1 (by rfl) ⟨779687, by rfl⟩ : syracuseStep 1039583 = 1559375) B1559375
theorem B1662439 : Blo 1036608 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B1039847 : Blo 1036608 1039847 := bstep (se 1 (by rfl) ⟨779885, by rfl⟩ : syracuseStep 1039847 = 1559771) B1559771
theorem B1039963 : Blo 1036608 1039963 := bstep (se 1 (by rfl) ⟨779972, by rfl⟩ : syracuseStep 1039963 = 1559945) B1559945
theorem B1040199 : Blo 1036608 1040199 := bstep (se 1 (by rfl) ⟨780149, by rfl⟩ : syracuseStep 1040199 = 1560299) B1560299
theorem B2809723 : Blo 1036608 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B1040351 : Blo 1036608 1040351 := bstep (se 1 (by rfl) ⟨780263, by rfl⟩ : syracuseStep 1040351 = 1560527) B1560527
theorem B7495739 : Blo 1036608 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B5267591 : Blo 1036608 5267591 := bstep (se 1 (by rfl) ⟨3950693, by rfl⟩ : syracuseStep 5267591 = 7901387) B7901387
theorem B1663163 : Blo 1036608 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B7102835 : Blo 1036608 7102835 := bstep (se 1 (by rfl) ⟨5327126, by rfl⟩ : syracuseStep 7102835 = 10654253) B10654253
theorem B15000065 : Blo 1036608 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B6644243 : Blo 1036608 6644243 := bstep (se 1 (by rfl) ⟨4983182, by rfl⟩ : syracuseStep 6644243 = 9966365) B9966365
theorem B5268077 : Blo 1036608 5268077 := bstep (se 3 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 5268077 = 1975529) B1975529
theorem B13329035 : Blo 1036608 13329035 := bstep (se 1 (by rfl) ⟨9996776, by rfl⟩ : syracuseStep 13329035 = 19993553) B19993553
theorem B2220967 : Blo 1036608 2220967 := bstep (se 1 (by rfl) ⟨1665725, by rfl⟩ : syracuseStep 2220967 = 3331451) B3331451
theorem B3367891 : Blo 1036608 3367891 := bstep (se 1 (by rfl) ⟨2525918, by rfl⟩ : syracuseStep 3367891 = 5051837) B5051837
theorem B15000875 : Blo 1036608 15000875 := bstep (se 1 (by rfl) ⟨11250656, by rfl⟩ : syracuseStep 15000875 = 22501313) B22501313
theorem B1402267 : Blo 1036608 1402267 := bstep (se 1 (by rfl) ⟨1051700, by rfl⟩ : syracuseStep 1402267 = 2103401) B2103401
theorem B3499631 : Blo 1036608 3499631 := bstep (se 1 (by rfl) ⟨2624723, by rfl⟩ : syracuseStep 3499631 = 5249447) B5249447
theorem B3499739 : Blo 1036608 3499739 := bstep (se 1 (by rfl) ⟨2624804, by rfl⟩ : syracuseStep 3499739 = 5249609) B5249609
theorem B2221787 : Blo 1036608 2221787 := bstep (se 1 (by rfl) ⟨1666340, by rfl⟩ : syracuseStep 2221787 = 3332681) B3332681
theorem B11822921 : Blo 1036608 11822921 := bstep (se 2 (by rfl) ⟨4433595, by rfl⟩ : syracuseStep 11822921 = 8867191) B8867191
theorem B5990821 : Blo 1036608 5990821 := bstep (se 4 (by rfl) ⟨561639, by rfl⟩ : syracuseStep 5990821 = 1123279) B1123279
theorem B6646475 : Blo 1036608 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B11234051 : Blo 1036608 11234051 := bstep (se 1 (by rfl) ⟨8425538, by rfl⟩ : syracuseStep 11234051 = 16851077) B16851077
theorem B3501035 : Blo 1036608 3501035 := bstep (se 1 (by rfl) ⟨2625776, by rfl⟩ : syracuseStep 3501035 = 5251553) B5251553
theorem B3501089 : Blo 1036608 3501089 := bstep (se 2 (by rfl) ⟨1312908, by rfl⟩ : syracuseStep 3501089 = 2625817) B2625817
theorem B14970257 : Blo 1036608 14970257 := bstep (se 2 (by rfl) ⟨5613846, by rfl⟩ : syracuseStep 14970257 = 11227693) B11227693
theorem B9990353 : Blo 1036608 9990353 := bstep (se 2 (by rfl) ⟨3746382, by rfl⟩ : syracuseStep 9990353 = 7492765) B7492765
theorem B3502547 : Blo 1036608 3502547 := bstep (se 1 (by rfl) ⟨2626910, by rfl⟩ : syracuseStep 3502547 = 5253821) B5253821
theorem B9990661 : Blo 1036608 9990661 := bstep (se 4 (by rfl) ⟨936624, by rfl⟩ : syracuseStep 9990661 = 1873249) B1873249
theorem B6320855 : Blo 1036608 6320855 := bstep (se 1 (by rfl) ⟨4740641, by rfl⟩ : syracuseStep 6320855 = 9481283) B9481283
theorem B10810273 : Blo 1036608 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B7108667 : Blo 1036608 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B3504491 : Blo 1036608 3504491 := bstep (se 1 (by rfl) ⟨2628368, by rfl⟩ : syracuseStep 3504491 = 5256737) B5256737
theorem B41613749 : Blo 1036608 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B3504761 : Blo 1036608 3504761 := bstep (se 2 (by rfl) ⟨1314285, by rfl⟩ : syracuseStep 3504761 = 2628571) B2628571
theorem B12614267 : Blo 1036608 12614267 := bstep (se 1 (by rfl) ⟨9460700, by rfl⟩ : syracuseStep 12614267 = 18921401) B18921401
theorem B3505193 : Blo 1036608 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B15170935 : Blo 1036608 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B3506543 : Blo 1036608 3506543 := bstep (se 1 (by rfl) ⟨2629907, by rfl⟩ : syracuseStep 3506543 = 5259815) B5259815
theorem B32015083 : Blo 1036608 32015083 := bstep (se 1 (by rfl) ⟨24011312, by rfl⟩ : syracuseStep 32015083 = 48022625) B48022625
theorem B37880743 : Blo 1036608 37880743 := bstep (se 1 (by rfl) ⟨28410557, by rfl⟩ : syracuseStep 37880743 = 56821115) B56821115
theorem B1311967 : Blo 1036608 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B3736799 : Blo 1036608 3736799 := bstep (se 1 (by rfl) ⟨2802599, by rfl⟩ : syracuseStep 3736799 = 5605199) B5605199
theorem B4490521 : Blo 1036608 4490521 := bstep (se 2 (by rfl) ⟨1683945, by rfl⟩ : syracuseStep 4490521 = 3367891) B3367891
theorem B4982107 : Blo 1036608 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B1803883 : Blo 1036608 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B1869689 : Blo 1036608 1869689 := bstep (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) B1402267
theorem B31951045 : Blo 1036608 31951045 := bstep (se 4 (by rfl) ⟨2995410, by rfl⟩ : syracuseStep 31951045 = 5990821) B5990821
theorem B9472787 : Blo 1036608 9472787 := bstep (se 1 (by rfl) ⟨7104590, by rfl⟩ : syracuseStep 9472787 = 14209181) B14209181
theorem B2624339 : Blo 1036608 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B7113863 : Blo 1036608 7113863 := bstep (se 1 (by rfl) ⟨5335397, by rfl⟩ : syracuseStep 7113863 = 10670795) B10670795
theorem B3509459 : Blo 1036608 3509459 := bstep (se 1 (by rfl) ⟨2632094, by rfl⟩ : syracuseStep 3509459 = 5264189) B5264189
theorem B26938655 : Blo 1036608 26938655 := bstep (se 1 (by rfl) ⟨20203991, by rfl⟩ : syracuseStep 26938655 = 40407983) B40407983
theorem B2952587 : Blo 1036608 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B3509729 : Blo 1036608 3509729 := bstep (se 2 (by rfl) ⟨1316148, by rfl⟩ : syracuseStep 3509729 = 2632297) B2632297
theorem B1314407 : Blo 1036608 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1052827 : Blo 1036608 1052827 := bstep (se 1 (by rfl) ⟨789620, by rfl⟩ : syracuseStep 1052827 = 1579241) B1579241
theorem B3510647 : Blo 1036608 3510647 := bstep (se 1 (by rfl) ⟨2632985, by rfl⟩ : syracuseStep 3510647 = 5265971) B5265971
theorem B3740215 : Blo 1036608 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B3511457 : Blo 1036608 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B3511727 : Blo 1036608 3511727 := bstep (se 1 (by rfl) ⟨2633795, by rfl⟩ : syracuseStep 3511727 = 5267591) B5267591
theorem B1971695 : Blo 1036608 1971695 := bstep (se 1 (by rfl) ⟨1478771, by rfl⟩ : syracuseStep 1971695 = 2957543) B2957543
theorem B37852717 : Blo 1036608 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B4986451 : Blo 1036608 4986451 := bstep (se 1 (by rfl) ⟨3739838, by rfl⟩ : syracuseStep 4986451 = 7479677) B7479677
theorem B2496167 : Blo 1036608 2496167 := bstep (se 1 (by rfl) ⟨1872125, by rfl⟩ : syracuseStep 2496167 = 3744251) B3744251
theorem B10000043 : Blo 1036608 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B4429495 : Blo 1036608 4429495 := bstep (se 1 (by rfl) ⟨3322121, by rfl⟩ : syracuseStep 4429495 = 6644243) B6644243
theorem B3512051 : Blo 1036608 3512051 := bstep (se 1 (by rfl) ⟨2634038, by rfl⟩ : syracuseStep 3512051 = 5268077) B5268077
theorem B8886023 : Blo 1036608 8886023 := bstep (se 1 (by rfl) ⟨6664517, by rfl⟩ : syracuseStep 8886023 = 13329035) B13329035
theorem B1316731 : Blo 1036608 1316731 := bstep (se 1 (by rfl) ⟨987548, by rfl⟩ : syracuseStep 1316731 = 1975097) B1975097
theorem B1972127 : Blo 1036608 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B10000583 : Blo 1036608 10000583 := bstep (se 1 (by rfl) ⟨7500437, by rfl⟩ : syracuseStep 10000583 = 15000875) B15000875
theorem B2333087 : Blo 1036608 2333087 := bstep (se 1 (by rfl) ⟨1749815, by rfl⟩ : syracuseStep 2333087 = 3499631) B3499631
theorem B2333159 : Blo 1036608 2333159 := bstep (se 1 (by rfl) ⟨1749869, by rfl⟩ : syracuseStep 2333159 = 3499739) B3499739
theorem B2955959 : Blo 1036608 2955959 := bstep (se 1 (by rfl) ⟨2216969, by rfl⟩ : syracuseStep 2955959 = 4433939) B4433939
theorem B7478003 : Blo 1036608 7478003 := bstep (se 1 (by rfl) ⟨5608502, by rfl⟩ : syracuseStep 7478003 = 11217005) B11217005
theorem B17767187 : Blo 1036608 17767187 := bstep (se 1 (by rfl) ⟨13325390, by rfl⟩ : syracuseStep 17767187 = 26650781) B26650781
theorem B2628409 : Blo 1036608 2628409 := bstep (se 2 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 2628409 = 1971307) B1971307
theorem B67476401 : Blo 1036608 67476401 := bstep (se 2 (by rfl) ⟨25303650, by rfl⟩ : syracuseStep 67476401 = 50607301) B50607301
theorem B2497657 : Blo 1036608 2497657 := bstep (se 2 (by rfl) ⟨936621, by rfl⟩ : syracuseStep 2497657 = 1873243) B1873243
theorem B4430983 : Blo 1036608 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B3939623 : Blo 1036608 3939623 := bstep (se 1 (by rfl) ⟨2954717, by rfl⟩ : syracuseStep 3939623 = 5909435) B5909435
theorem B2334023 : Blo 1036608 2334023 := bstep (se 1 (by rfl) ⟨1750517, by rfl⟩ : syracuseStep 2334023 = 3501035) B3501035
theorem B2334059 : Blo 1036608 2334059 := bstep (se 1 (by rfl) ⟨1750544, by rfl⟩ : syracuseStep 2334059 = 3501089) B3501089
theorem B2334185 : Blo 1036608 2334185 := bstep (se 2 (by rfl) ⟨875319, by rfl⟩ : syracuseStep 2334185 = 1750639) B1750639
theorem B1973737 : Blo 1036608 1973737 := bstep (se 2 (by rfl) ⟨740151, by rfl⟩ : syracuseStep 1973737 = 1480303) B1480303
theorem B2334329 : Blo 1036608 2334329 := bstep (se 2 (by rfl) ⟨875373, by rfl⟩ : syracuseStep 2334329 = 1750747) B1750747
theorem B41033405 : Blo 1036608 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B2957303 : Blo 1036608 2957303 := bstep (se 1 (by rfl) ⟨2217977, by rfl⟩ : syracuseStep 2957303 = 4435955) B4435955
theorem B6660235 : Blo 1036608 6660235 := bstep (se 1 (by rfl) ⟨4995176, by rfl⟩ : syracuseStep 6660235 = 9990353) B9990353
theorem B2629847 : Blo 1036608 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B1974527 : Blo 1036608 1974527 := bstep (se 1 (by rfl) ⟨1480895, by rfl⟩ : syracuseStep 1974527 = 2961791) B2961791
theorem B2335031 : Blo 1036608 2335031 := bstep (se 1 (by rfl) ⟨1751273, by rfl⟩ : syracuseStep 2335031 = 3502547) B3502547
theorem B5252363 : Blo 1036608 5252363 := bstep (se 1 (by rfl) ⟨3939272, by rfl⟩ : syracuseStep 5252363 = 7878545) B7878545
theorem B2336057 : Blo 1036608 2336057 := bstep (se 2 (by rfl) ⟨876021, by rfl⟩ : syracuseStep 2336057 = 1752043) B1752043
theorem B3941885 : Blo 1036608 3941885 := bstep (se 3 (by rfl) ⟨739103, by rfl⟩ : syracuseStep 3941885 = 1478207) B1478207
theorem B2336327 : Blo 1036608 2336327 := bstep (se 1 (by rfl) ⟨1752245, by rfl⟩ : syracuseStep 2336327 = 3504491) B3504491
theorem B2336507 : Blo 1036608 2336507 := bstep (se 1 (by rfl) ⟨1752380, by rfl⟩ : syracuseStep 2336507 = 3504761) B3504761
theorem B2631487 : Blo 1036608 2631487 := bstep (se 1 (by rfl) ⟨1973615, by rfl⟩ : syracuseStep 2631487 = 3947231) B3947231
theorem B20227913 : Blo 1036608 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B2336795 : Blo 1036608 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B4434041 : Blo 1036608 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B2992457 : Blo 1036608 2992457 := bstep (se 2 (by rfl) ⟨1122171, by rfl⟩ : syracuseStep 2992457 = 2244343) B2244343
theorem B3746297 : Blo 1036608 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B7875143 : Blo 1036608 7875143 := bstep (se 1 (by rfl) ⟨5906357, by rfl⟩ : syracuseStep 7875143 = 11812715) B11812715
theorem B8006215 : Blo 1036608 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B4205243 : Blo 1036608 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B5253983 : Blo 1036608 5253983 := bstep (se 1 (by rfl) ⟨3940487, by rfl⟩ : syracuseStep 5253983 = 7880975) B7880975
theorem B2338271 : Blo 1036608 2338271 := bstep (se 1 (by rfl) ⟨1753703, by rfl⟩ : syracuseStep 2338271 = 3507407) B3507407
theorem B2338487 : Blo 1036608 2338487 := bstep (se 1 (by rfl) ⟨1753865, by rfl⟩ : syracuseStep 2338487 = 3507731) B3507731
theorem B2961289 : Blo 1036608 2961289 := bstep (se 2 (by rfl) ⟨1110483, by rfl⟩ : syracuseStep 2961289 = 2220967) B2220967
theorem B4993103 : Blo 1036608 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B2633867 : Blo 1036608 2633867 := bstep (se 1 (by rfl) ⟨1975400, by rfl⟩ : syracuseStep 2633867 = 3950801) B3950801
theorem B4993255 : Blo 1036608 4993255 := bstep (se 1 (by rfl) ⟨3744941, by rfl⟩ : syracuseStep 4993255 = 7489883) B7489883
theorem B2339279 : Blo 1036608 2339279 := bstep (se 1 (by rfl) ⟨1754459, by rfl⟩ : syracuseStep 2339279 = 3508919) B3508919
theorem B31928903 : Blo 1036608 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B3748459 : Blo 1036608 3748459 := bstep (se 1 (by rfl) ⟨2811344, by rfl⟩ : syracuseStep 3748459 = 5622689) B5622689
theorem B8008429 : Blo 1036608 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B1749755 : Blo 1036608 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B3945257 : Blo 1036608 3945257 := bstep (se 2 (by rfl) ⟨1479471, by rfl⟩ : syracuseStep 3945257 = 2958943) B2958943
theorem B5124983 : Blo 1036608 5124983 := bstep (se 1 (by rfl) ⟨3843737, by rfl⟩ : syracuseStep 5124983 = 7687475) B7687475
theorem B11809799 : Blo 1036608 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B9974825 : Blo 1036608 9974825 := bstep (se 2 (by rfl) ⟨3740559, by rfl⟩ : syracuseStep 9974825 = 7481119) B7481119
theorem B5256251 : Blo 1036608 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B2339945 : Blo 1036608 2339945 := bstep (se 2 (by rfl) ⟨877479, by rfl⟩ : syracuseStep 2339945 = 1754959) B1754959
theorem B17740943 : Blo 1036608 17740943 := bstep (se 1 (by rfl) ⟨13305707, by rfl⟩ : syracuseStep 17740943 = 26611415) B26611415
theorem B1750619 : Blo 1036608 1750619 := bstep (se 1 (by rfl) ⟨1312964, by rfl⟩ : syracuseStep 1750619 = 2625929) B2625929
theorem B2340575 : Blo 1036608 2340575 := bstep (se 1 (by rfl) ⟨1755431, by rfl⟩ : syracuseStep 2340575 = 3510863) B3510863
theorem B2340935 : Blo 1036608 2340935 := bstep (se 1 (by rfl) ⟨1755701, by rfl⟩ : syracuseStep 2340935 = 3511403) B3511403
theorem B37861481 : Blo 1036608 37861481 := bstep (se 2 (by rfl) ⟨14198055, by rfl⟩ : syracuseStep 37861481 = 28396111) B28396111
theorem B3946745 : Blo 1036608 3946745 := bstep (se 2 (by rfl) ⟨1480029, by rfl⟩ : syracuseStep 3946745 = 2960059) B2960059
theorem B3324199 : Blo 1036608 3324199 := bstep (se 1 (by rfl) ⟨2493149, by rfl⟩ : syracuseStep 3324199 = 4986299) B4986299
theorem B4995485 : Blo 1036608 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B1751503 : Blo 1036608 1751503 := bstep (se 1 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 1751503 = 2627255) B2627255
theorem B5257871 : Blo 1036608 5257871 := bstep (se 1 (by rfl) ⟨3943403, by rfl⟩ : syracuseStep 5257871 = 7886807) B7886807
theorem B1555103 : Blo 1036608 1555103 := bstep (se 1 (by rfl) ⟨1166327, by rfl⟩ : syracuseStep 1555103 = 2332655) B2332655
theorem B1555247 : Blo 1036608 1555247 := bstep (se 1 (by rfl) ⟨1166435, by rfl⟩ : syracuseStep 1555247 = 2332871) B2332871
theorem B1096519 : Blo 1036608 1096519 := bstep (se 1 (by rfl) ⟨822389, by rfl⟩ : syracuseStep 1096519 = 1644779) B1644779
theorem B1555367 : Blo 1036608 1555367 := bstep (se 1 (by rfl) ⟨1166525, by rfl⟩ : syracuseStep 1555367 = 2333051) B2333051
theorem B1555547 : Blo 1036608 1555547 := bstep (se 1 (by rfl) ⟨1166660, by rfl⟩ : syracuseStep 1555547 = 2333321) B2333321
theorem B8863091 : Blo 1036608 8863091 := bstep (se 1 (by rfl) ⟨6647318, by rfl⟩ : syracuseStep 8863091 = 13294637) B13294637
theorem B3947899 : Blo 1036608 3947899 := bstep (se 1 (by rfl) ⟨2960924, by rfl⟩ : syracuseStep 3947899 = 5921849) B5921849
theorem B1555919 : Blo 1036608 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B4439747 : Blo 1036608 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B1752799 : Blo 1036608 1752799 := bstep (se 1 (by rfl) ⟨1314599, by rfl⟩ : syracuseStep 1752799 = 2629199) B2629199
theorem B4505311 : Blo 1036608 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1556303 : Blo 1036608 1556303 := bstep (se 1 (by rfl) ⟨1167227, by rfl⟩ : syracuseStep 1556303 = 2334455) B2334455
theorem B1556423 : Blo 1036608 1556423 := bstep (se 1 (by rfl) ⟨1167317, by rfl⟩ : syracuseStep 1556423 = 2334635) B2334635
theorem B4997159 : Blo 1036608 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B4735223 : Blo 1036608 4735223 := bstep (se 1 (by rfl) ⟨3551417, by rfl⟩ : syracuseStep 4735223 = 7102835) B7102835
theorem B1556783 : Blo 1036608 1556783 := bstep (se 1 (by rfl) ⟨1167587, by rfl⟩ : syracuseStep 1556783 = 2335175) B2335175
theorem B18924029 : Blo 1036608 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B1557023 : Blo 1036608 1557023 := bstep (se 1 (by rfl) ⟨1167767, by rfl⟩ : syracuseStep 1557023 = 2335535) B2335535
theorem B13320881 : Blo 1036608 13320881 := bstep (se 2 (by rfl) ⟨4995330, by rfl⟩ : syracuseStep 13320881 = 9990661) B9990661
theorem B3326761 : Blo 1036608 3326761 := bstep (se 2 (by rfl) ⟨1247535, by rfl⟩ : syracuseStep 3326761 = 2495071) B2495071
theorem B1557695 : Blo 1036608 1557695 := bstep (se 1 (by rfl) ⟨1168271, by rfl⟩ : syracuseStep 1557695 = 2336543) B2336543
theorem B7881947 : Blo 1036608 7881947 := bstep (se 1 (by rfl) ⟨5911460, by rfl⟩ : syracuseStep 7881947 = 11822921) B11822921
theorem B1557839 : Blo 1036608 1557839 := bstep (se 1 (by rfl) ⟨1168379, by rfl⟩ : syracuseStep 1557839 = 2336759) B2336759
theorem B1557929 : Blo 1036608 1557929 := bstep (se 2 (by rfl) ⟨584223, by rfl⟩ : syracuseStep 1557929 = 1168447) B1168447
theorem B1558079 : Blo 1036608 1558079 := bstep (se 1 (by rfl) ⟨1168559, by rfl⟩ : syracuseStep 1558079 = 2337119) B2337119
theorem B1558121 : Blo 1036608 1558121 := bstep (se 2 (by rfl) ⟨584295, by rfl⟩ : syracuseStep 1558121 = 1168591) B1168591
theorem B7489367 : Blo 1036608 7489367 := bstep (se 1 (by rfl) ⟨5617025, by rfl⟩ : syracuseStep 7489367 = 11234051) B11234051
theorem B1558559 : Blo 1036608 1558559 := bstep (se 1 (by rfl) ⟨1168919, by rfl⟩ : syracuseStep 1558559 = 2337839) B2337839
theorem B1558751 : Blo 1036608 1558751 := bstep (se 1 (by rfl) ⟨1169063, by rfl⟩ : syracuseStep 1558751 = 2338127) B2338127
theorem B9980171 : Blo 1036608 9980171 := bstep (se 1 (by rfl) ⟨7485128, by rfl⟩ : syracuseStep 9980171 = 14970257) B14970257
theorem B1558811 : Blo 1036608 1558811 := bstep (se 1 (by rfl) ⟨1169108, by rfl⟩ : syracuseStep 1558811 = 2338217) B2338217
theorem B1559135 : Blo 1036608 1559135 := bstep (se 1 (by rfl) ⟨1169351, by rfl⟩ : syracuseStep 1559135 = 2338703) B2338703
theorem B2214697 : Blo 1036608 2214697 := bstep (se 2 (by rfl) ⟨830511, by rfl⟩ : syracuseStep 2214697 = 1661023) B1661023
theorem B1559417 : Blo 1036608 1559417 := bstep (se 2 (by rfl) ⟨584781, by rfl⟩ : syracuseStep 1559417 = 1169563) B1169563
theorem B1559465 : Blo 1036608 1559465 := bstep (se 2 (by rfl) ⟨584799, by rfl⟩ : syracuseStep 1559465 = 1169599) B1169599
theorem B1559615 : Blo 1036608 1559615 := bstep (se 1 (by rfl) ⟨1169711, by rfl⟩ : syracuseStep 1559615 = 2339423) B2339423
theorem B4213903 : Blo 1036608 4213903 := bstep (se 1 (by rfl) ⟨3160427, by rfl⟩ : syracuseStep 4213903 = 6320855) B6320855
theorem B1166719 : Blo 1036608 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B1560167 : Blo 1036608 1560167 := bstep (se 1 (by rfl) ⟨1170125, by rfl⟩ : syracuseStep 1560167 = 2340251) B2340251
theorem B16010945 : Blo 1036608 16010945 := bstep (se 2 (by rfl) ⟨6004104, by rfl⟩ : syracuseStep 16010945 = 12008209) B12008209
theorem B1560551 : Blo 1036608 1560551 := bstep (se 1 (by rfl) ⟨1170413, by rfl⟩ : syracuseStep 1560551 = 2340827) B2340827
theorem B4739111 : Blo 1036608 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B1560671 : Blo 1036608 1560671 := bstep (se 1 (by rfl) ⟨1170503, by rfl⟩ : syracuseStep 1560671 = 2341007) B2341007
theorem B1560683 : Blo 1036608 1560683 := bstep (se 1 (by rfl) ⟨1170512, by rfl⟩ : syracuseStep 1560683 = 2341025) B2341025
theorem B1560731 : Blo 1036608 1560731 := bstep (se 1 (by rfl) ⟨1170548, by rfl⟩ : syracuseStep 1560731 = 2341097) B2341097
theorem B3330247 : Blo 1036608 3330247 := bstep (se 1 (by rfl) ⟨2497685, by rfl⟩ : syracuseStep 3330247 = 4995371) B4995371
theorem B4444379 : Blo 1036608 4444379 := bstep (se 1 (by rfl) ⟨3333284, by rfl⟩ : syracuseStep 4444379 = 6666569) B6666569
theorem B27742499 : Blo 1036608 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B1036647 : Blo 1036608 1036647 := bstep (se 1 (by rfl) ⟨777485, by rfl⟩ : syracuseStep 1036647 = 1554971) B1554971
theorem B1036699 : Blo 1036608 1036699 := bstep (se 1 (by rfl) ⟨777524, by rfl⟩ : syracuseStep 1036699 = 1555049) B1555049
theorem B8409511 : Blo 1036608 8409511 := bstep (se 1 (by rfl) ⟨6307133, by rfl⟩ : syracuseStep 8409511 = 12614267) B12614267
theorem B2216585 : Blo 1036608 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B1037051 : Blo 1036608 1037051 := bstep (se 1 (by rfl) ⟨777788, by rfl⟩ : syracuseStep 1037051 = 1555577) B1555577
theorem B1168123 : Blo 1036608 1168123 := bstep (se 1 (by rfl) ⟨876092, by rfl⟩ : syracuseStep 1168123 = 1752185) B1752185
theorem B1037119 : Blo 1036608 1037119 := bstep (se 1 (by rfl) ⟨777839, by rfl⟩ : syracuseStep 1037119 = 1555679) B1555679
theorem B1037147 : Blo 1036608 1037147 := bstep (se 1 (by rfl) ⟨777860, by rfl⟩ : syracuseStep 1037147 = 1555721) B1555721
theorem B1037215 : Blo 1036608 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B1037295 : Blo 1036608 1037295 := bstep (se 1 (by rfl) ⟨777971, by rfl⟩ : syracuseStep 1037295 = 1555943) B1555943
theorem B1037383 : Blo 1036608 1037383 := bstep (se 1 (by rfl) ⟨778037, by rfl⟩ : syracuseStep 1037383 = 1556075) B1556075
theorem B1037467 : Blo 1036608 1037467 := bstep (se 1 (by rfl) ⟨778100, by rfl⟩ : syracuseStep 1037467 = 1556201) B1556201
theorem B1037563 : Blo 1036608 1037563 := bstep (se 1 (by rfl) ⟨778172, by rfl⟩ : syracuseStep 1037563 = 1556345) B1556345
theorem B1037631 : Blo 1036608 1037631 := bstep (se 1 (by rfl) ⟨778223, by rfl⟩ : syracuseStep 1037631 = 1556447) B1556447
theorem B1037799 : Blo 1036608 1037799 := bstep (se 1 (by rfl) ⟨778349, by rfl⟩ : syracuseStep 1037799 = 1556699) B1556699
theorem B1037807 : Blo 1036608 1037807 := bstep (se 1 (by rfl) ⟨778355, by rfl⟩ : syracuseStep 1037807 = 1556711) B1556711
theorem B1168879 : Blo 1036608 1168879 := bstep (se 1 (by rfl) ⟨876659, by rfl⟩ : syracuseStep 1168879 = 1753319) B1753319
theorem B1037915 : Blo 1036608 1037915 := bstep (se 1 (by rfl) ⟨778436, by rfl⟩ : syracuseStep 1037915 = 1556873) B1556873
theorem B1168987 : Blo 1036608 1168987 := bstep (se 1 (by rfl) ⟨876740, by rfl⟩ : syracuseStep 1168987 = 1753481) B1753481
theorem B1037979 : Blo 1036608 1037979 := bstep (se 1 (by rfl) ⟨778484, by rfl⟩ : syracuseStep 1037979 = 1556969) B1556969
theorem B1038063 : Blo 1036608 1038063 := bstep (se 1 (by rfl) ⟨778547, by rfl⟩ : syracuseStep 1038063 = 1557095) B1557095
theorem B1038151 : Blo 1036608 1038151 := bstep (se 1 (by rfl) ⟨778613, by rfl⟩ : syracuseStep 1038151 = 1557227) B1557227
theorem B1038171 : Blo 1036608 1038171 := bstep (se 1 (by rfl) ⟨778628, by rfl⟩ : syracuseStep 1038171 = 1557257) B1557257
theorem B1169275 : Blo 1036608 1169275 := bstep (se 1 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 1169275 = 1753913) B1753913
theorem B1038239 : Blo 1036608 1038239 := bstep (se 1 (by rfl) ⟨778679, by rfl⟩ : syracuseStep 1038239 = 1557359) B1557359
theorem B1169311 : Blo 1036608 1169311 := bstep (se 1 (by rfl) ⟨876983, by rfl⟩ : syracuseStep 1169311 = 1753967) B1753967
theorem B1038407 : Blo 1036608 1038407 := bstep (se 1 (by rfl) ⟨778805, by rfl⟩ : syracuseStep 1038407 = 1557611) B1557611
theorem B1038567 : Blo 1036608 1038567 := bstep (se 1 (by rfl) ⟨778925, by rfl⟩ : syracuseStep 1038567 = 1557851) B1557851
theorem B1661215 : Blo 1036608 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B1038751 : Blo 1036608 1038751 := bstep (se 1 (by rfl) ⟨779063, by rfl⟩ : syracuseStep 1038751 = 1558127) B1558127
theorem B1038799 : Blo 1036608 1038799 := bstep (se 1 (by rfl) ⟨779099, by rfl⟩ : syracuseStep 1038799 = 1558199) B1558199
theorem B1038823 : Blo 1036608 1038823 := bstep (se 1 (by rfl) ⟨779117, by rfl⟩ : syracuseStep 1038823 = 1558235) B1558235
theorem B1038939 : Blo 1036608 1038939 := bstep (se 1 (by rfl) ⟨779204, by rfl⟩ : syracuseStep 1038939 = 1558409) B1558409
theorem B1039007 : Blo 1036608 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B1661753 : Blo 1036608 1661753 := bstep (se 2 (by rfl) ⟨623157, by rfl⟩ : syracuseStep 1661753 = 1246315) B1246315
theorem B1039175 : Blo 1036608 1039175 := bstep (se 1 (by rfl) ⟨779381, by rfl⟩ : syracuseStep 1039175 = 1558763) B1558763
theorem B1170247 : Blo 1036608 1170247 := bstep (se 1 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 1170247 = 1755371) B1755371
theorem B1039215 : Blo 1036608 1039215 := bstep (se 1 (by rfl) ⟨779411, by rfl⟩ : syracuseStep 1039215 = 1558823) B1558823
theorem B1039271 : Blo 1036608 1039271 := bstep (se 1 (by rfl) ⟨779453, by rfl⟩ : syracuseStep 1039271 = 1558907) B1558907
theorem B1039451 : Blo 1036608 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B1039567 : Blo 1036608 1039567 := bstep (se 1 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 1039567 = 1559351) B1559351
theorem B1039591 : Blo 1036608 1039591 := bstep (se 1 (by rfl) ⟨779693, by rfl⟩ : syracuseStep 1039591 = 1559387) B1559387
theorem B1039687 : Blo 1036608 1039687 := bstep (se 1 (by rfl) ⟨779765, by rfl⟩ : syracuseStep 1039687 = 1559531) B1559531
theorem B1039823 : Blo 1036608 1039823 := bstep (se 1 (by rfl) ⟨779867, by rfl⟩ : syracuseStep 1039823 = 1559735) B1559735
theorem B1039983 : Blo 1036608 1039983 := bstep (se 1 (by rfl) ⟨779987, by rfl⟩ : syracuseStep 1039983 = 1559975) B1559975
theorem B1040039 : Blo 1036608 1040039 := bstep (se 1 (by rfl) ⟨780029, by rfl⟩ : syracuseStep 1040039 = 1560059) B1560059
theorem B16867025 : Blo 1036608 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B1040103 : Blo 1036608 1040103 := bstep (se 1 (by rfl) ⟨780077, by rfl⟩ : syracuseStep 1040103 = 1560155) B1560155
theorem B1040159 : Blo 1036608 1040159 := bstep (se 1 (by rfl) ⟨780119, by rfl⟩ : syracuseStep 1040159 = 1560239) B1560239
theorem B7888751 : Blo 1036608 7888751 := bstep (se 1 (by rfl) ⟨5916563, by rfl⟩ : syracuseStep 7888751 = 11833127) B11833127
theorem B1040239 : Blo 1036608 1040239 := bstep (se 1 (by rfl) ⟨780179, by rfl⟩ : syracuseStep 1040239 = 1560359) B1560359
theorem B1040295 : Blo 1036608 1040295 := bstep (se 1 (by rfl) ⟨780221, by rfl⟩ : syracuseStep 1040295 = 1560443) B1560443
theorem B1040575 : Blo 1036608 1040575 := bstep (se 1 (by rfl) ⟨780431, by rfl⟩ : syracuseStep 1040575 = 1560863) B1560863
theorem B1040591 : Blo 1036608 1040591 := bstep (se 1 (by rfl) ⟨780443, by rfl⟩ : syracuseStep 1040591 = 1560887) B1560887
theorem B16867547 : Blo 1036608 16867547 := bstep (se 1 (by rfl) ⟨12650660, by rfl⟩ : syracuseStep 16867547 = 25301321) B25301321
theorem B8413793 : Blo 1036608 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B44951051 : Blo 1036608 44951051 := bstep (se 1 (by rfl) ⟨33713288, by rfl⟩ : syracuseStep 44951051 = 67426577) B67426577
theorem B5924447 : Blo 1036608 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B7890695 : Blo 1036608 7890695 := bstep (se 1 (by rfl) ⟨5918021, by rfl⟩ : syracuseStep 7890695 = 11836043) B11836043
theorem B5924765 : Blo 1036608 5924765 := bstep (se 3 (by rfl) ⟨1110893, by rfl⟩ : syracuseStep 5924765 = 2221787) B2221787
theorem B5924947 : Blo 1036608 5924947 := bstep (se 1 (by rfl) ⟨4443710, by rfl⟩ : syracuseStep 5924947 = 8887421) B8887421
theorem B6645883 : Blo 1036608 6645883 := bstep (se 1 (by rfl) ⟨4984412, by rfl⟩ : syracuseStep 6645883 = 9968825) B9968825
theorem B1665515 : Blo 1036608 1665515 := bstep (se 1 (by rfl) ⟨1249136, by rfl⟩ : syracuseStep 1665515 = 2498273) B2498273
theorem B1108775 : Blo 1036608 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B108030955 : Blo 1036608 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B12611153 : Blo 1036608 12611153 := bstep (se 2 (by rfl) ⟨4729182, by rfl⟩ : syracuseStep 12611153 = 9458365) B9458365
theorem B14413697 : Blo 1036608 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B11235347 : Blo 1036608 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B3502223 : Blo 1036608 3502223 := bstep (se 1 (by rfl) ⟨2626667, by rfl⟩ : syracuseStep 3502223 = 5253335) B5253335
theorem B51212569 : Blo 1036608 51212569 := bstep (se 2 (by rfl) ⟨19204713, by rfl⟩ : syracuseStep 51212569 = 38409427) B38409427
theorem B3502439 : Blo 1036608 3502439 := bstep (se 1 (by rfl) ⟨2626829, by rfl⟩ : syracuseStep 3502439 = 5253659) B5253659
theorem B3798845 : Blo 1036608 3798845 := bstep (se 3 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 3798845 = 1424567) B1424567
theorem B3503951 : Blo 1036608 3503951 := bstep (se 1 (by rfl) ⟨2627963, by rfl⟩ : syracuseStep 3503951 = 5255927) B5255927
theorem B50527901 : Blo 1036608 50527901 := bstep (se 3 (by rfl) ⟨9473981, by rfl⟩ : syracuseStep 50527901 = 18947963) B18947963
theorem B3505895 : Blo 1036608 3505895 := bstep (se 1 (by rfl) ⟨2629421, by rfl⟩ : syracuseStep 3505895 = 5258843) B5258843
theorem B8880313 : Blo 1036608 8880313 := bstep (se 2 (by rfl) ⟨3330117, by rfl⟩ : syracuseStep 8880313 = 6660235) B6660235
theorem B12616019 : Blo 1036608 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B8880587 : Blo 1036608 8880587 := bstep (se 1 (by rfl) ⟨6660440, by rfl⟩ : syracuseStep 8880587 = 13320881) B13320881
theorem B2491199 : Blo 1036608 2491199 := bstep (se 1 (by rfl) ⟨1868399, by rfl⟩ : syracuseStep 2491199 = 3736799) B3736799
theorem B6653447 : Blo 1036608 6653447 := bstep (se 1 (by rfl) ⟨4990085, by rfl⟩ : syracuseStep 6653447 = 9980171) B9980171
theorem B17959103 : Blo 1036608 17959103 := bstep (se 1 (by rfl) ⟨13469327, by rfl⟩ : syracuseStep 17959103 = 26938655) B26938655
theorem B1968391 : Blo 1036608 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B13666621 : Blo 1036608 13666621 := bstep (se 3 (by rfl) ⟨2562491, by rfl⟩ : syracuseStep 13666621 = 5124983) B5124983
theorem B3508649 : Blo 1036608 3508649 := bstep (se 2 (by rfl) ⟨1315743, by rfl⟩ : syracuseStep 3508649 = 2631487) B2631487
theorem B7899929 : Blo 1036608 7899929 := bstep (se 2 (by rfl) ⟨2962473, by rfl⟩ : syracuseStep 7899929 = 5924947) B5924947
theorem B42601393 : Blo 1036608 42601393 := bstep (se 2 (by rfl) ⟨15975522, by rfl⟩ : syracuseStep 42601393 = 31951045) B31951045
theorem B1314463 : Blo 1036608 1314463 := bstep (se 1 (by rfl) ⟨985847, by rfl⟩ : syracuseStep 1314463 = 1971695) B1971695
theorem B2952929 : Blo 1036608 2952929 := bstep (se 2 (by rfl) ⟨1107348, by rfl⟩ : syracuseStep 2952929 = 2214697) B2214697
theorem B1970639 : Blo 1036608 1970639 := bstep (se 1 (by rfl) ⟨1477979, by rfl⟩ : syracuseStep 1970639 = 2955959) B2955959
theorem B4985335 : Blo 1036608 4985335 := bstep (se 1 (by rfl) ⟨3739001, by rfl⟩ : syracuseStep 4985335 = 7478003) B7478003
theorem B2626415 : Blo 1036608 2626415 := bstep (se 1 (by rfl) ⟨1969811, by rfl⟩ : syracuseStep 2626415 = 3939623) B3939623
theorem B4985837 : Blo 1036608 4985837 := bstep (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) B1869689
theorem B11244683 : Blo 1036608 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B1971535 : Blo 1036608 1971535 := bstep (se 1 (by rfl) ⟨1478651, by rfl⟩ : syracuseStep 1971535 = 2957303) B2957303
theorem B11245031 : Blo 1036608 11245031 := bstep (se 1 (by rfl) ⟨8433773, by rfl⟩ : syracuseStep 11245031 = 16867547) B16867547
theorem B1316351 : Blo 1036608 1316351 := bstep (se 1 (by rfl) ⟨987263, by rfl⟩ : syracuseStep 1316351 = 1974527) B1974527
theorem B6657673 : Blo 1036608 6657673 := bstep (se 2 (by rfl) ⟨2496627, by rfl⟩ : syracuseStep 6657673 = 4993255) B4993255
theorem B5609195 : Blo 1036608 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B11212681 : Blo 1036608 11212681 := bstep (se 2 (by rfl) ⟨4204755, by rfl⟩ : syracuseStep 11212681 = 8409511) B8409511
theorem B4986953 : Blo 1036608 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B2627923 : Blo 1036608 2627923 := bstep (se 1 (by rfl) ⟨1970942, by rfl⟩ : syracuseStep 2627923 = 3941885) B3941885
theorem B2956027 : Blo 1036608 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B5250095 : Blo 1036608 5250095 := bstep (se 1 (by rfl) ⟨3937571, by rfl⟩ : syracuseStep 5250095 = 7875143) B7875143
theorem B50470289 : Blo 1036608 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B2956733 : Blo 1036608 2956733 := bstep (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) B1108775
theorem B4431341 : Blo 1036608 4431341 := bstep (se 3 (by rfl) ⟨830876, by rfl⟩ : syracuseStep 4431341 = 1661753) B1661753
theorem B5905993 : Blo 1036608 5905993 := bstep (se 2 (by rfl) ⟨2214747, by rfl⟩ : syracuseStep 5905993 = 4429495) B4429495
theorem B9609131 : Blo 1036608 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B2334815 : Blo 1036608 2334815 := bstep (se 1 (by rfl) ⟨1751111, by rfl⟩ : syracuseStep 2334815 = 3502223) B3502223
theorem B2334959 : Blo 1036608 2334959 := bstep (se 1 (by rfl) ⟨1751219, by rfl⟩ : syracuseStep 2334959 = 3502439) B3502439
theorem B4432265 : Blo 1036608 4432265 := bstep (se 2 (by rfl) ⟨1662099, by rfl⟩ : syracuseStep 4432265 = 3324199) B3324199
theorem B2630171 : Blo 1036608 2630171 := bstep (se 1 (by rfl) ⟨1972628, by rfl⟩ : syracuseStep 2630171 = 3945257) B3945257
theorem B2335337 : Blo 1036608 2335337 := bstep (se 2 (by rfl) ⟨875751, by rfl⟩ : syracuseStep 2335337 = 1751503) B1751503
theorem B7873199 : Blo 1036608 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B2532563 : Blo 1036608 2532563 := bstep (se 1 (by rfl) ⟨1899422, by rfl⟩ : syracuseStep 2532563 = 3798845) B3798845
theorem B2335967 : Blo 1036608 2335967 := bstep (se 1 (by rfl) ⟨1751975, by rfl⟩ : syracuseStep 2335967 = 3503951) B3503951
theorem B25240987 : Blo 1036608 25240987 := bstep (se 1 (by rfl) ⟨18930740, by rfl⟩ : syracuseStep 25240987 = 37861481) B37861481
theorem B2631163 : Blo 1036608 2631163 := bstep (se 1 (by rfl) ⟨1973372, by rfl⟩ : syracuseStep 2631163 = 3946745) B3946745
theorem B5907977 : Blo 1036608 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B33629741 : Blo 1036608 33629741 := bstep (se 3 (by rfl) ⟨6305576, by rfl⟩ : syracuseStep 33629741 = 12611153) B12611153
theorem B109422413 : Blo 1036608 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B2631649 : Blo 1036608 2631649 := bstep (se 2 (by rfl) ⟨986868, by rfl⟩ : syracuseStep 2631649 = 1973737) B1973737
theorem B5908727 : Blo 1036608 5908727 := bstep (se 1 (by rfl) ⟨4431545, by rfl⟩ : syracuseStep 5908727 = 8863091) B8863091
theorem B2337065 : Blo 1036608 2337065 := bstep (se 2 (by rfl) ⟨876399, by rfl⟩ : syracuseStep 2337065 = 1752799) B1752799
theorem B6007081 : Blo 1036608 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B2959831 : Blo 1036608 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B2337263 : Blo 1036608 2337263 := bstep (se 1 (by rfl) ⟨1752947, by rfl⟩ : syracuseStep 2337263 = 3505895) B3505895
theorem B3156815 : Blo 1036608 3156815 := bstep (se 1 (by rfl) ⟨2367611, by rfl⟩ : syracuseStep 3156815 = 4735223) B4735223
theorem B2337695 : Blo 1036608 2337695 := bstep (se 1 (by rfl) ⟨1753271, by rfl⟩ : syracuseStep 2337695 = 3506543) B3506543
theorem B5615077 : Blo 1036608 5615077 := bstep (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) B1052827
theorem B5254631 : Blo 1036608 5254631 := bstep (se 1 (by rfl) ⟨3940973, by rfl⟩ : syracuseStep 5254631 = 7881947) B7881947
theorem B4435681 : Blo 1036608 4435681 := bstep (se 2 (by rfl) ⟨1663380, by rfl⟩ : syracuseStep 4435681 = 3326761) B3326761
theorem B50507657 : Blo 1036608 50507657 := bstep (se 2 (by rfl) ⟨18940371, by rfl⟩ : syracuseStep 50507657 = 37880743) B37880743
theorem B4992911 : Blo 1036608 4992911 := bstep (se 1 (by rfl) ⟨3744683, by rfl⟩ : syracuseStep 4992911 = 7489367) B7489367
theorem B1749289 : Blo 1036608 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B5910893 : Blo 1036608 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B1749559 : Blo 1036608 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B2339639 : Blo 1036608 2339639 := bstep (se 1 (by rfl) ⟨1754729, by rfl⟩ : syracuseStep 2339639 = 3509459) B3509459
theorem B2405177 : Blo 1036608 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B2339819 : Blo 1036608 2339819 := bstep (se 1 (by rfl) ⟨1754864, by rfl⟩ : syracuseStep 2339819 = 3509729) B3509729
theorem B3159407 : Blo 1036608 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B2962919 : Blo 1036608 2962919 := bstep (se 1 (by rfl) ⟨2222189, by rfl⟩ : syracuseStep 2962919 = 4444379) B4444379
theorem B8861177 : Blo 1036608 8861177 := bstep (se 2 (by rfl) ⟨3322941, by rfl⟩ : syracuseStep 8861177 = 6645883) B6645883
theorem B18494999 : Blo 1036608 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B2340431 : Blo 1036608 2340431 := bstep (se 1 (by rfl) ⟨1755323, by rfl⟩ : syracuseStep 2340431 = 3510647) B3510647
theorem B2340971 : Blo 1036608 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B2341151 : Blo 1036608 2341151 := bstep (se 1 (by rfl) ⟨1755863, by rfl⟩ : syracuseStep 2341151 = 3511727) B3511727
theorem B6666695 : Blo 1036608 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B2341367 : Blo 1036608 2341367 := bstep (se 1 (by rfl) ⟨1756025, by rfl⟩ : syracuseStep 2341367 = 3512051) B3512051
theorem B6667055 : Blo 1036608 6667055 := bstep (se 1 (by rfl) ⟨5000291, by rfl⟩ : syracuseStep 6667055 = 10000583) B10000583
theorem B5618537 : Blo 1036608 5618537 := bstep (se 2 (by rfl) ⟨2106951, by rfl⟩ : syracuseStep 5618537 = 4213903) B4213903
theorem B1555391 : Blo 1036608 1555391 := bstep (se 1 (by rfl) ⟨1166543, by rfl⟩ : syracuseStep 1555391 = 2333087) B2333087
theorem B1555439 : Blo 1036608 1555439 := bstep (se 1 (by rfl) ⟨1166579, by rfl⟩ : syracuseStep 1555439 = 2333159) B2333159
theorem B1555625 : Blo 1036608 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B11844791 : Blo 1036608 11844791 := bstep (se 1 (by rfl) ⟨8883593, by rfl⟩ : syracuseStep 11844791 = 17767187) B17767187
theorem B1556015 : Blo 1036608 1556015 := bstep (se 1 (by rfl) ⟨1167011, by rfl⟩ : syracuseStep 1556015 = 2334023) B2334023
theorem B1556039 : Blo 1036608 1556039 := bstep (se 1 (by rfl) ⟨1167029, by rfl⟩ : syracuseStep 1556039 = 2334059) B2334059
theorem B1556123 : Blo 1036608 1556123 := bstep (se 1 (by rfl) ⟨1167092, by rfl⟩ : syracuseStep 1556123 = 2334185) B2334185
theorem B1556219 : Blo 1036608 1556219 := bstep (se 1 (by rfl) ⟨1167164, by rfl⟩ : syracuseStep 1556219 = 2334329) B2334329
theorem B5259005 : Blo 1036608 5259005 := bstep (se 3 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 5259005 = 1972127) B1972127
theorem B3948385 : Blo 1036608 3948385 := bstep (se 2 (by rfl) ⟨1480644, by rfl⟩ : syracuseStep 3948385 = 2961289) B2961289
theorem B5259167 : Blo 1036608 5259167 := bstep (se 1 (by rfl) ⟨3944375, by rfl⟩ : syracuseStep 5259167 = 7888751) B7888751
theorem B1753231 : Blo 1036608 1753231 := bstep (se 1 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 1753231 = 2629847) B2629847
theorem B1556687 : Blo 1036608 1556687 := bstep (se 1 (by rfl) ⟨1167515, by rfl⟩ : syracuseStep 1556687 = 2335031) B2335031
theorem B4440329 : Blo 1036608 4440329 := bstep (se 2 (by rfl) ⟨1665123, by rfl⟩ : syracuseStep 4440329 = 3330247) B3330247
theorem B4997945 : Blo 1036608 4997945 := bstep (se 2 (by rfl) ⟨1874229, by rfl⟩ : syracuseStep 4997945 = 3748459) B3748459
theorem B1557371 : Blo 1036608 1557371 := bstep (se 1 (by rfl) ⟨1168028, by rfl⟩ : syracuseStep 1557371 = 2336057) B2336057
theorem B1557497 : Blo 1036608 1557497 := bstep (se 2 (by rfl) ⟨584061, by rfl⟩ : syracuseStep 1557497 = 1168123) B1168123
theorem B29967367 : Blo 1036608 29967367 := bstep (se 1 (by rfl) ⟨22475525, by rfl⟩ : syracuseStep 29967367 = 44951051) B44951051
theorem B1557551 : Blo 1036608 1557551 := bstep (se 1 (by rfl) ⟨1168163, by rfl⟩ : syracuseStep 1557551 = 2336327) B2336327
theorem B3949631 : Blo 1036608 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B1557671 : Blo 1036608 1557671 := bstep (se 1 (by rfl) ⟨1168253, by rfl⟩ : syracuseStep 1557671 = 2336507) B2336507
theorem B5260463 : Blo 1036608 5260463 := bstep (se 1 (by rfl) ⟨3945347, by rfl⟩ : syracuseStep 5260463 = 7890695) B7890695
theorem B13485275 : Blo 1036608 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B3949843 : Blo 1036608 3949843 := bstep (se 1 (by rfl) ⟨2962382, by rfl⟩ : syracuseStep 3949843 = 5924765) B5924765
theorem B1557863 : Blo 1036608 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B2803495 : Blo 1036608 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B1558505 : Blo 1036608 1558505 := bstep (se 2 (by rfl) ⟨584439, by rfl⟩ : syracuseStep 1558505 = 1168879) B1168879
theorem B1558649 : Blo 1036608 1558649 := bstep (se 2 (by rfl) ⟨584493, by rfl⟩ : syracuseStep 1558649 = 1168987) B1168987
theorem B1558847 : Blo 1036608 1558847 := bstep (se 1 (by rfl) ⟨1169135, by rfl⟩ : syracuseStep 1558847 = 2338271) B2338271
theorem B1558991 : Blo 1036608 1558991 := bstep (se 1 (by rfl) ⟨1169243, by rfl⟩ : syracuseStep 1558991 = 2338487) B2338487
theorem B1559033 : Blo 1036608 1559033 := bstep (se 2 (by rfl) ⟨584637, by rfl⟩ : syracuseStep 1559033 = 1169275) B1169275
theorem B1755641 : Blo 1036608 1755641 := bstep (se 2 (by rfl) ⟨658365, by rfl⟩ : syracuseStep 1755641 = 1316731) B1316731
theorem B1559081 : Blo 1036608 1559081 := bstep (se 2 (by rfl) ⟨584655, by rfl⟩ : syracuseStep 1559081 = 1169311) B1169311
theorem B7490231 : Blo 1036608 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B3328735 : Blo 1036608 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B1755911 : Blo 1036608 1755911 := bstep (se 1 (by rfl) ⟨1316933, by rfl⟩ : syracuseStep 1755911 = 2633867) B2633867
theorem B1559519 : Blo 1036608 1559519 := bstep (se 1 (by rfl) ⟨1169639, by rfl⟩ : syracuseStep 1559519 = 2339279) B2339279
theorem B2214953 : Blo 1036608 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B21285935 : Blo 1036608 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B1166503 : Blo 1036608 1166503 := bstep (se 1 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 1166503 = 1749755) B1749755
theorem B1559963 : Blo 1036608 1559963 := bstep (se 1 (by rfl) ⟨1169972, by rfl⟩ : syracuseStep 1559963 = 2339945) B2339945
theorem B1167079 : Blo 1036608 1167079 := bstep (se 1 (by rfl) ⟨875309, by rfl⟩ : syracuseStep 1167079 = 1750619) B1750619
theorem B1462025 : Blo 1036608 1462025 := bstep (se 2 (by rfl) ⟨548259, by rfl⟩ : syracuseStep 1462025 = 1096519) B1096519
theorem B1560329 : Blo 1036608 1560329 := bstep (se 2 (by rfl) ⟨585123, by rfl⟩ : syracuseStep 1560329 = 1170247) B1170247
theorem B1560383 : Blo 1036608 1560383 := bstep (se 1 (by rfl) ⟨1170287, by rfl⟩ : syracuseStep 1560383 = 2340575) B2340575
theorem B1560623 : Blo 1036608 1560623 := bstep (se 1 (by rfl) ⟨1170467, by rfl⟩ : syracuseStep 1560623 = 2340935) B2340935
theorem B3330209 : Blo 1036608 3330209 := bstep (se 2 (by rfl) ⟨1248828, by rfl⟩ : syracuseStep 3330209 = 2497657) B2497657
theorem B3330323 : Blo 1036608 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B1036735 : Blo 1036608 1036735 := bstep (se 1 (by rfl) ⟨777551, by rfl⟩ : syracuseStep 1036735 = 1555103) B1555103
theorem B5263865 : Blo 1036608 5263865 := bstep (se 2 (by rfl) ⟨1973949, by rfl⟩ : syracuseStep 5263865 = 3947899) B3947899
theorem B1036831 : Blo 1036608 1036831 := bstep (se 1 (by rfl) ⟨777623, by rfl⟩ : syracuseStep 1036831 = 1555247) B1555247
theorem B1036911 : Blo 1036608 1036911 := bstep (se 1 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 1036911 = 1555367) B1555367
theorem B1037031 : Blo 1036608 1037031 := bstep (se 1 (by rfl) ⟨777773, by rfl⟩ : syracuseStep 1037031 = 1555547) B1555547
theorem B1037279 : Blo 1036608 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B1037535 : Blo 1036608 1037535 := bstep (se 1 (by rfl) ⟨778151, by rfl⟩ : syracuseStep 1037535 = 1556303) B1556303
theorem B1037615 : Blo 1036608 1037615 := bstep (se 1 (by rfl) ⟨778211, by rfl⟩ : syracuseStep 1037615 = 1556423) B1556423
theorem B3331439 : Blo 1036608 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B1037855 : Blo 1036608 1037855 := bstep (se 1 (by rfl) ⟨778391, by rfl⟩ : syracuseStep 1037855 = 1556783) B1556783
theorem B1038015 : Blo 1036608 1038015 := bstep (se 1 (by rfl) ⟨778511, by rfl⟩ : syracuseStep 1038015 = 1557023) B1557023
theorem B1038463 : Blo 1036608 1038463 := bstep (se 1 (by rfl) ⟨778847, by rfl⟩ : syracuseStep 1038463 = 1557695) B1557695
theorem B1038559 : Blo 1036608 1038559 := bstep (se 1 (by rfl) ⟨778919, by rfl⟩ : syracuseStep 1038559 = 1557839) B1557839
theorem B1038619 : Blo 1036608 1038619 := bstep (se 1 (by rfl) ⟨778964, by rfl⟩ : syracuseStep 1038619 = 1557929) B1557929
theorem B42686777 : Blo 1036608 42686777 := bstep (se 2 (by rfl) ⟨16007541, by rfl⟩ : syracuseStep 42686777 = 32015083) B32015083
theorem B1038719 : Blo 1036608 1038719 := bstep (se 1 (by rfl) ⟨779039, by rfl⟩ : syracuseStep 1038719 = 1558079) B1558079
theorem B1038747 : Blo 1036608 1038747 := bstep (se 1 (by rfl) ⟨779060, by rfl⟩ : syracuseStep 1038747 = 1558121) B1558121
theorem B1039039 : Blo 1036608 1039039 := bstep (se 1 (by rfl) ⟨779279, by rfl⟩ : syracuseStep 1039039 = 1558559) B1558559
theorem B1039167 : Blo 1036608 1039167 := bstep (se 1 (by rfl) ⟨779375, by rfl⟩ : syracuseStep 1039167 = 1558751) B1558751
theorem B1039207 : Blo 1036608 1039207 := bstep (se 1 (by rfl) ⟨779405, by rfl⟩ : syracuseStep 1039207 = 1558811) B1558811
theorem B1039423 : Blo 1036608 1039423 := bstep (se 1 (by rfl) ⟨779567, by rfl⟩ : syracuseStep 1039423 = 1559135) B1559135
theorem B6642809 : Blo 1036608 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B6315191 : Blo 1036608 6315191 := bstep (se 1 (by rfl) ⟨4736393, by rfl⟩ : syracuseStep 6315191 = 9472787) B9472787
theorem B1039611 : Blo 1036608 1039611 := bstep (se 1 (by rfl) ⟨779708, by rfl⟩ : syracuseStep 1039611 = 1559417) B1559417
theorem B1039643 : Blo 1036608 1039643 := bstep (se 1 (by rfl) ⟨779732, by rfl⟩ : syracuseStep 1039643 = 1559465) B1559465
theorem B1039743 : Blo 1036608 1039743 := bstep (se 1 (by rfl) ⟨779807, by rfl⟩ : syracuseStep 1039743 = 1559615) B1559615
theorem B1040111 : Blo 1036608 1040111 := bstep (se 1 (by rfl) ⟨780083, by rfl⟩ : syracuseStep 1040111 = 1560167) B1560167
theorem B10673963 : Blo 1036608 10673963 := bstep (se 1 (by rfl) ⟨8005472, by rfl⟩ : syracuseStep 10673963 = 16010945) B16010945
theorem B1040367 : Blo 1036608 1040367 := bstep (se 1 (by rfl) ⟨780275, by rfl⟩ : syracuseStep 1040367 = 1560551) B1560551
theorem B1040447 : Blo 1036608 1040447 := bstep (se 1 (by rfl) ⟨780335, by rfl⟩ : syracuseStep 1040447 = 1560671) B1560671
theorem B1040455 : Blo 1036608 1040455 := bstep (se 1 (by rfl) ⟨780341, by rfl⟩ : syracuseStep 1040455 = 1560683) B1560683
theorem B1040487 : Blo 1036608 1040487 := bstep (se 1 (by rfl) ⟨780365, by rfl⟩ : syracuseStep 1040487 = 1560731) B1560731
theorem B10674953 : Blo 1036608 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B1664111 : Blo 1036608 1664111 := bstep (se 1 (by rfl) ⟨1248083, by rfl⟩ : syracuseStep 1664111 = 2496167) B2496167
theorem B5924015 : Blo 1036608 5924015 := bstep (se 1 (by rfl) ⟨4443011, by rfl⟩ : syracuseStep 5924015 = 8886023) B8886023
theorem B144041273 : Blo 1036608 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B44984267 : Blo 1036608 44984267 := bstep (se 1 (by rfl) ⟨33738200, by rfl⟩ : syracuseStep 44984267 = 67476401) B67476401
theorem B68283425 : Blo 1036608 68283425 := bstep (se 2 (by rfl) ⟨25606284, by rfl⟩ : syracuseStep 68283425 = 51212569) B51212569
theorem B3501575 : Blo 1036608 3501575 := bstep (se 1 (by rfl) ⟨2626181, by rfl⟩ : syracuseStep 3501575 = 5252363) B5252363
theorem B10677905 : Blo 1036608 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B9990125 : Blo 1036608 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B23949445 : Blo 1036608 23949445 := bstep (se 4 (by rfl) ⟨2245260, by rfl⟩ : syracuseStep 23949445 = 4490521) B4490521
theorem B1994971 : Blo 1036608 1994971 := bstep (se 1 (by rfl) ⟨1496228, by rfl⟩ : syracuseStep 1994971 = 2992457) B2992457
theorem B1110343 : Blo 1036608 1110343 := bstep (se 1 (by rfl) ⟨832757, by rfl⟩ : syracuseStep 1110343 = 1665515) B1665515
theorem B3502655 : Blo 1036608 3502655 := bstep (se 1 (by rfl) ⟨2626991, by rfl⟩ : syracuseStep 3502655 = 5253983) B5253983
theorem B6648601 : Blo 1036608 6648601 := bstep (se 2 (by rfl) ⟨2493225, by rfl⟩ : syracuseStep 6648601 = 4986451) B4986451
theorem B18970301 : Blo 1036608 18970301 := bstep (se 3 (by rfl) ⟨3556931, by rfl⟩ : syracuseStep 18970301 = 7113863) B7113863
theorem B6649883 : Blo 1036608 6649883 := bstep (se 1 (by rfl) ⟨4987412, by rfl⟩ : syracuseStep 6649883 = 9974825) B9974825
theorem B3504167 : Blo 1036608 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B11827295 : Blo 1036608 11827295 := bstep (se 1 (by rfl) ⟨8870471, by rfl⟩ : syracuseStep 11827295 = 17740943) B17740943
theorem B3504545 : Blo 1036608 3504545 := bstep (se 2 (by rfl) ⟨1314204, by rfl⟩ : syracuseStep 3504545 = 2628409) B2628409
theorem B3505085 : Blo 1036608 3505085 := bstep (se 3 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 3505085 = 1314407) B1314407
theorem B3505247 : Blo 1036608 3505247 := bstep (se 1 (by rfl) ⟨2628935, by rfl⟩ : syracuseStep 3505247 = 5257871) B5257871
theorem B33685267 : Blo 1036608 33685267 := bstep (se 1 (by rfl) ⟨25263950, by rfl⟩ : syracuseStep 33685267 = 50527901) B50527901
theorem B3506975 : Blo 1036608 3506975 := bstep (se 1 (by rfl) ⟨2630231, by rfl⟩ : syracuseStep 3506975 = 5260463) B5260463
theorem B33654649 : Blo 1036608 33654649 := bstep (se 2 (by rfl) ⟨12620493, by rfl⟩ : syracuseStep 33654649 = 25240987) B25240987
theorem B3508217 : Blo 1036608 3508217 := bstep (se 2 (by rfl) ⟨1315581, by rfl⟩ : syracuseStep 3508217 = 2631163) B2631163
theorem B1476635 : Blo 1036608 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B14190623 : Blo 1036608 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B3737993 : Blo 1036608 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B1968619 : Blo 1036608 1968619 := bstep (se 1 (by rfl) ⟨1476464, by rfl⟩ : syracuseStep 1968619 = 2952929) B2952929
theorem B3508865 : Blo 1036608 3508865 := bstep (se 2 (by rfl) ⟨1315824, by rfl⟩ : syracuseStep 3508865 = 2631649) B2631649
theorem B1313759 : Blo 1036608 1313759 := bstep (se 1 (by rfl) ⟨985319, by rfl⟩ : syracuseStep 1313759 = 1970639) B1970639
theorem B3509243 : Blo 1036608 3509243 := bstep (se 1 (by rfl) ⟨2631932, by rfl⟩ : syracuseStep 3509243 = 5263865) B5263865
theorem B2624521 : Blo 1036608 2624521 := bstep (se 2 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 2624521 = 1968391) B1968391
theorem B29985821 : Blo 1036608 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B18222161 : Blo 1036608 18222161 := bstep (se 2 (by rfl) ⟨6833310, by rfl⟩ : syracuseStep 18222161 = 13666621) B13666621
theorem B3739463 : Blo 1036608 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B3510269 : Blo 1036608 3510269 := bstep (se 3 (by rfl) ⟨658175, by rfl⟩ : syracuseStep 3510269 = 1316351) B1316351
theorem B4428539 : Blo 1036608 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B1971155 : Blo 1036608 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B2954227 : Blo 1036608 2954227 := bstep (se 1 (by rfl) ⟨2215670, by rfl⟩ : syracuseStep 2954227 = 4431341) B4431341
theorem B7115975 : Blo 1036608 7115975 := bstep (se 1 (by rfl) ⟨5336981, by rfl⟩ : syracuseStep 7115975 = 10673963) B10673963
theorem B2954843 : Blo 1036608 2954843 := bstep (se 1 (by rfl) ⟨2216132, by rfl⟩ : syracuseStep 2954843 = 4432265) B4432265
theorem B2659961 : Blo 1036608 2659961 := bstep (se 2 (by rfl) ⟨997485, by rfl⟩ : syracuseStep 2659961 = 1994971) B1994971
theorem B2332385 : Blo 1036608 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B1480457 : Blo 1036608 1480457 := bstep (se 2 (by rfl) ⟨555171, by rfl⟩ : syracuseStep 1480457 = 1110343) B1110343
theorem B5248799 : Blo 1036608 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B7116635 : Blo 1036608 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B2332745 : Blo 1036608 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B3938651 : Blo 1036608 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B22419827 : Blo 1036608 22419827 := bstep (se 1 (by rfl) ⟨16814870, by rfl⟩ : syracuseStep 22419827 = 33629741) B33629741
theorem B72948275 : Blo 1036608 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B29989511 : Blo 1036608 29989511 := bstep (se 1 (by rfl) ⟨22492133, by rfl⟩ : syracuseStep 29989511 = 44984267) B44984267
theorem B3939151 : Blo 1036608 3939151 := bstep (se 1 (by rfl) ⟨2954363, by rfl⟩ : syracuseStep 3939151 = 5908727) B5908727
theorem B2628713 : Blo 1036608 2628713 := bstep (se 2 (by rfl) ⟨985767, by rfl⟩ : syracuseStep 2628713 = 1971535) B1971535
theorem B45522283 : Blo 1036608 45522283 := bstep (se 1 (by rfl) ⟨34141712, by rfl⟩ : syracuseStep 45522283 = 68283425) B68283425
theorem B2334383 : Blo 1036608 2334383 := bstep (se 1 (by rfl) ⟨1750787, by rfl⟩ : syracuseStep 2334383 = 3501575) B3501575
theorem B7118603 : Blo 1036608 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B14950241 : Blo 1036608 14950241 := bstep (se 2 (by rfl) ⟨5606340, by rfl⟩ : syracuseStep 14950241 = 11212681) B11212681
theorem B6660083 : Blo 1036608 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B3940595 : Blo 1036608 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B2335103 : Blo 1036608 2335103 := bstep (se 1 (by rfl) ⟨1751327, by rfl⟩ : syracuseStep 2335103 = 3502655) B3502655
theorem B2106271 : Blo 1036608 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B1975279 : Blo 1036608 1975279 := bstep (se 1 (by rfl) ⟨1481459, by rfl⟩ : syracuseStep 1975279 = 2962919) B2962919
theorem B3941369 : Blo 1036608 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B5907451 : Blo 1036608 5907451 := bstep (se 1 (by rfl) ⟨4430588, by rfl⟩ : syracuseStep 5907451 = 8861177) B8861177
theorem B12329999 : Blo 1036608 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B4433255 : Blo 1036608 4433255 := bstep (se 1 (by rfl) ⟨3324941, by rfl⟩ : syracuseStep 4433255 = 6649883) B6649883
theorem B2336111 : Blo 1036608 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B2336363 : Blo 1036608 2336363 := bstep (se 1 (by rfl) ⟨1752272, by rfl⟩ : syracuseStep 2336363 = 3504545) B3504545
theorem B3745691 : Blo 1036608 3745691 := bstep (se 1 (by rfl) ⟨2809268, by rfl⟩ : syracuseStep 3745691 = 5618537) B5618537
theorem B2336723 : Blo 1036608 2336723 := bstep (se 1 (by rfl) ⟨1752542, by rfl⟩ : syracuseStep 2336723 = 3505085) B3505085
theorem B2336831 : Blo 1036608 2336831 := bstep (se 1 (by rfl) ⟨1752623, by rfl⟩ : syracuseStep 2336831 = 3505247) B3505247
theorem B7874657 : Blo 1036608 7874657 := bstep (se 2 (by rfl) ⟨2952996, by rfl⟩ : syracuseStep 7874657 = 5905993) B5905993
theorem B2960219 : Blo 1036608 2960219 := bstep (se 1 (by rfl) ⟨2220164, by rfl⟩ : syracuseStep 2960219 = 4440329) B4440329
theorem B2337641 : Blo 1036608 2337641 := bstep (se 2 (by rfl) ⟨876615, by rfl⟩ : syracuseStep 2337641 = 1753231) B1753231
theorem B11840417 : Blo 1036608 11840417 := bstep (se 2 (by rfl) ⟨4440156, by rfl⟩ : syracuseStep 11840417 = 8880313) B8880313
theorem B2633087 : Blo 1036608 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B8990183 : Blo 1036608 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B4435631 : Blo 1036608 4435631 := bstep (se 1 (by rfl) ⟨3326723, by rfl⟩ : syracuseStep 4435631 = 6653447) B6653447
theorem B39956489 : Blo 1036608 39956489 := bstep (se 2 (by rfl) ⟨14983683, by rfl⟩ : syracuseStep 39956489 = 29967367) B29967367
theorem B11972735 : Blo 1036608 11972735 := bstep (se 1 (by rfl) ⟨8979551, by rfl⟩ : syracuseStep 11972735 = 17959103) B17959103
theorem B2339099 : Blo 1036608 2339099 := bstep (se 1 (by rfl) ⟨1754324, by rfl⟩ : syracuseStep 2339099 = 3508649) B3508649
theorem B4993487 : Blo 1036608 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B4437629 : Blo 1036608 4437629 := bstep (se 3 (by rfl) ⟨832055, by rfl⟩ : syracuseStep 4437629 = 1664111) B1664111
theorem B8009441 : Blo 1036608 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B1750943 : Blo 1036608 1750943 := bstep (se 1 (by rfl) ⟨1313207, by rfl⟩ : syracuseStep 1750943 = 2626415) B2626415
theorem B3946441 : Blo 1036608 3946441 := bstep (se 2 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 3946441 = 2959831) B2959831
theorem B3323891 : Blo 1036608 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B4438313 : Blo 1036608 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B56801857 : Blo 1036608 56801857 := bstep (se 2 (by rfl) ⟨21300696, by rfl⟩ : syracuseStep 56801857 = 42601393) B42601393
theorem B3324635 : Blo 1036608 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B1555337 : Blo 1036608 1555337 := bstep (se 2 (by rfl) ⟨583251, by rfl⟩ : syracuseStep 1555337 = 1166503) B1166503
theorem B7486769 : Blo 1036608 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B4210127 : Blo 1036608 4210127 := bstep (se 1 (by rfl) ⟨3157595, by rfl⟩ : syracuseStep 4210127 = 6315191) B6315191
theorem B1752617 : Blo 1036608 1752617 := bstep (se 2 (by rfl) ⟨657231, by rfl⟩ : syracuseStep 1752617 = 1314463) B1314463
theorem B5914241 : Blo 1036608 5914241 := bstep (se 2 (by rfl) ⟨2217840, by rfl⟩ : syracuseStep 5914241 = 4435681) B4435681
theorem B1556105 : Blo 1036608 1556105 := bstep (se 2 (by rfl) ⟨583539, by rfl⟩ : syracuseStep 1556105 = 1167079) B1167079
theorem B1556543 : Blo 1036608 1556543 := bstep (se 1 (by rfl) ⟨1167407, by rfl⟩ : syracuseStep 1556543 = 2334815) B2334815
theorem B1556639 : Blo 1036608 1556639 := bstep (se 1 (by rfl) ⟨1167479, by rfl⟩ : syracuseStep 1556639 = 2334959) B2334959
theorem B31932593 : Blo 1036608 31932593 := bstep (se 2 (by rfl) ⟨11974722, by rfl⟩ : syracuseStep 31932593 = 23949445) B23949445
theorem B1753447 : Blo 1036608 1753447 := bstep (se 1 (by rfl) ⟨1315085, by rfl⟩ : syracuseStep 1753447 = 2630171) B2630171
theorem B1556891 : Blo 1036608 1556891 := bstep (se 1 (by rfl) ⟨1167668, by rfl⟩ : syracuseStep 1556891 = 2335337) B2335337
theorem B3949343 : Blo 1036608 3949343 := bstep (se 1 (by rfl) ⟨2962007, by rfl⟩ : syracuseStep 3949343 = 5924015) B5924015
theorem B1688375 : Blo 1036608 1688375 := bstep (se 1 (by rfl) ⟨1266281, by rfl⟩ : syracuseStep 1688375 = 2532563) B2532563
theorem B1557311 : Blo 1036608 1557311 := bstep (se 1 (by rfl) ⟨1167983, by rfl⟩ : syracuseStep 1557311 = 2335967) B2335967
theorem B96027515 : Blo 1036608 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B8864801 : Blo 1036608 8864801 := bstep (se 2 (by rfl) ⟨3324300, by rfl⟩ : syracuseStep 8864801 = 6648601) B6648601
theorem B1558043 : Blo 1036608 1558043 := bstep (se 1 (by rfl) ⟨1168532, by rfl⟩ : syracuseStep 1558043 = 2337065) B2337065
theorem B1558175 : Blo 1036608 1558175 := bstep (se 1 (by rfl) ⟨1168631, by rfl⟩ : syracuseStep 1558175 = 2337263) B2337263
theorem B1558463 : Blo 1036608 1558463 := bstep (se 1 (by rfl) ⟨1168847, by rfl⟩ : syracuseStep 1558463 = 2337695) B2337695
theorem B33671771 : Blo 1036608 33671771 := bstep (se 1 (by rfl) ⟨25253828, by rfl⟩ : syracuseStep 33671771 = 50507657) B50507657
theorem B3328607 : Blo 1036608 3328607 := bstep (se 1 (by rfl) ⟨2496455, by rfl⟩ : syracuseStep 3328607 = 4992911) B4992911
theorem B1559759 : Blo 1036608 1559759 := bstep (se 1 (by rfl) ⟨1169819, by rfl⟩ : syracuseStep 1559759 = 2339639) B2339639
theorem B1559879 : Blo 1036608 1559879 := bstep (se 1 (by rfl) ⟨1169909, by rfl⟩ : syracuseStep 1559879 = 2339819) B2339819
theorem B1560287 : Blo 1036608 1560287 := bstep (se 1 (by rfl) ⟨1170215, by rfl⟩ : syracuseStep 1560287 = 2340431) B2340431
theorem B7884863 : Blo 1036608 7884863 := bstep (se 1 (by rfl) ⟨5913647, by rfl⟩ : syracuseStep 7884863 = 11827295) B11827295
theorem B1560647 : Blo 1036608 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B1560767 : Blo 1036608 1560767 := bstep (se 1 (by rfl) ⟨1170575, by rfl⟩ : syracuseStep 1560767 = 2341151) B2341151
theorem B4444463 : Blo 1036608 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B1560911 : Blo 1036608 1560911 := bstep (se 1 (by rfl) ⟨1170683, by rfl⟩ : syracuseStep 1560911 = 2341367) B2341367
theorem B4444703 : Blo 1036608 4444703 := bstep (se 1 (by rfl) ⟨3333527, by rfl⟩ : syracuseStep 4444703 = 6667055) B6667055
theorem B1036927 : Blo 1036608 1036927 := bstep (se 1 (by rfl) ⟨777695, by rfl⟩ : syracuseStep 1036927 = 1555391) B1555391
theorem B1036959 : Blo 1036608 1036959 := bstep (se 1 (by rfl) ⟨777719, by rfl⟩ : syracuseStep 1036959 = 1555439) B1555439
theorem B1037083 : Blo 1036608 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B44913689 : Blo 1036608 44913689 := bstep (se 2 (by rfl) ⟨16842633, by rfl⟩ : syracuseStep 44913689 = 33685267) B33685267
theorem B1037343 : Blo 1036608 1037343 := bstep (se 1 (by rfl) ⟨778007, by rfl⟩ : syracuseStep 1037343 = 1556015) B1556015
theorem B1037359 : Blo 1036608 1037359 := bstep (se 1 (by rfl) ⟨778019, by rfl⟩ : syracuseStep 1037359 = 1556039) B1556039
theorem B1037415 : Blo 1036608 1037415 := bstep (se 1 (by rfl) ⟨778061, by rfl⟩ : syracuseStep 1037415 = 1556123) B1556123
theorem B5264513 : Blo 1036608 5264513 := bstep (se 2 (by rfl) ⟨1974192, by rfl⟩ : syracuseStep 5264513 = 3948385) B3948385
theorem B1037479 : Blo 1036608 1037479 := bstep (se 1 (by rfl) ⟨778109, by rfl⟩ : syracuseStep 1037479 = 1556219) B1556219
theorem B1037791 : Blo 1036608 1037791 := bstep (se 1 (by rfl) ⟨778343, by rfl⟩ : syracuseStep 1037791 = 1556687) B1556687
theorem B8410679 : Blo 1036608 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B5920391 : Blo 1036608 5920391 := bstep (se 1 (by rfl) ⟨4440293, by rfl⟩ : syracuseStep 5920391 = 8880587) B8880587
theorem B3331963 : Blo 1036608 3331963 := bstep (se 1 (by rfl) ⟨2498972, by rfl⟩ : syracuseStep 3331963 = 4997945) B4997945
theorem B1660799 : Blo 1036608 1660799 := bstep (se 1 (by rfl) ⟨1245599, by rfl⟩ : syracuseStep 1660799 = 2491199) B2491199
theorem B1038247 : Blo 1036608 1038247 := bstep (se 1 (by rfl) ⟨778685, by rfl⟩ : syracuseStep 1038247 = 1557371) B1557371
theorem B1038331 : Blo 1036608 1038331 := bstep (se 1 (by rfl) ⟨778748, by rfl⟩ : syracuseStep 1038331 = 1557497) B1557497
theorem B1038367 : Blo 1036608 1038367 := bstep (se 1 (by rfl) ⟨778775, by rfl⟩ : syracuseStep 1038367 = 1557551) B1557551
theorem B1038447 : Blo 1036608 1038447 := bstep (se 1 (by rfl) ⟨778835, by rfl⟩ : syracuseStep 1038447 = 1557671) B1557671
theorem B1038575 : Blo 1036608 1038575 := bstep (se 1 (by rfl) ⟨778931, by rfl⟩ : syracuseStep 1038575 = 1557863) B1557863
theorem B1039003 : Blo 1036608 1039003 := bstep (se 1 (by rfl) ⟨779252, by rfl⟩ : syracuseStep 1039003 = 1558505) B1558505
theorem B1039099 : Blo 1036608 1039099 := bstep (se 1 (by rfl) ⟨779324, by rfl⟩ : syracuseStep 1039099 = 1558649) B1558649
theorem B1039231 : Blo 1036608 1039231 := bstep (se 1 (by rfl) ⟨779423, by rfl⟩ : syracuseStep 1039231 = 1558847) B1558847
theorem B1039327 : Blo 1036608 1039327 := bstep (se 1 (by rfl) ⟨779495, by rfl⟩ : syracuseStep 1039327 = 1558991) B1558991
theorem B1039355 : Blo 1036608 1039355 := bstep (se 1 (by rfl) ⟨779516, by rfl⟩ : syracuseStep 1039355 = 1559033) B1559033
theorem B1170427 : Blo 1036608 1170427 := bstep (se 1 (by rfl) ⟨877820, by rfl⟩ : syracuseStep 1170427 = 1755641) B1755641
theorem B5266457 : Blo 1036608 5266457 := bstep (se 2 (by rfl) ⟨1974921, by rfl⟩ : syracuseStep 5266457 = 3949843) B3949843
theorem B1039387 : Blo 1036608 1039387 := bstep (se 1 (by rfl) ⟨779540, by rfl⟩ : syracuseStep 1039387 = 1559081) B1559081
theorem B1170607 : Blo 1036608 1170607 := bstep (se 1 (by rfl) ⟨877955, by rfl⟩ : syracuseStep 1170607 = 1755911) B1755911
theorem B5266619 : Blo 1036608 5266619 := bstep (se 1 (by rfl) ⟨3949964, by rfl⟩ : syracuseStep 5266619 = 7899929) B7899929
theorem B1039679 : Blo 1036608 1039679 := bstep (se 1 (by rfl) ⟨779759, by rfl⟩ : syracuseStep 1039679 = 1559519) B1559519
theorem B1039975 : Blo 1036608 1039975 := bstep (se 1 (by rfl) ⟨779981, by rfl⟩ : syracuseStep 1039975 = 1559963) B1559963
theorem B1040219 : Blo 1036608 1040219 := bstep (se 1 (by rfl) ⟨780164, by rfl⟩ : syracuseStep 1040219 = 1560329) B1560329
theorem B1040255 : Blo 1036608 1040255 := bstep (se 1 (by rfl) ⟨780191, by rfl⟩ : syracuseStep 1040255 = 1560383) B1560383
theorem B1040415 : Blo 1036608 1040415 := bstep (se 1 (by rfl) ⟨780311, by rfl⟩ : syracuseStep 1040415 = 1560623) B1560623
theorem B2220139 : Blo 1036608 2220139 := bstep (se 1 (by rfl) ⟨1665104, by rfl⟩ : syracuseStep 2220139 = 3330209) B3330209
theorem B2220215 : Blo 1036608 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B2220959 : Blo 1036608 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B7496687 : Blo 1036608 7496687 := bstep (se 1 (by rfl) ⟨5622515, by rfl⟩ : syracuseStep 7496687 = 11245031) B11245031
theorem B3500063 : Blo 1036608 3500063 := bstep (se 1 (by rfl) ⟨2625047, by rfl⟩ : syracuseStep 3500063 = 5250095) B5250095
theorem B33646859 : Blo 1036608 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B6647113 : Blo 1036608 6647113 := bstep (se 2 (by rfl) ⟨2492667, by rfl⟩ : syracuseStep 6647113 = 4985335) B4985335
theorem B113831405 : Blo 1036608 113831405 := bstep (se 3 (by rfl) ⟨21343388, by rfl⟩ : syracuseStep 113831405 = 42686777) B42686777
theorem B8876897 : Blo 1036608 8876897 := bstep (se 2 (by rfl) ⟨3328836, by rfl⟩ : syracuseStep 8876897 = 6657673) B6657673
theorem B8418173 : Blo 1036608 8418173 := bstep (se 3 (by rfl) ⟨1578407, by rfl⟩ : syracuseStep 8418173 = 3156815) B3156815
theorem B3503087 : Blo 1036608 3503087 := bstep (se 1 (by rfl) ⟨2627315, by rfl⟩ : syracuseStep 3503087 = 5254631) B5254631
theorem B3503897 : Blo 1036608 3503897 := bstep (se 2 (by rfl) ⟨1313961, by rfl⟩ : syracuseStep 3503897 = 2627923) B2627923
theorem B1603451 : Blo 1036608 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B12646867 : Blo 1036608 12646867 := bstep (se 1 (by rfl) ⟨9485150, by rfl⟩ : syracuseStep 12646867 = 18970301) B18970301
theorem B3898733 : Blo 1036608 3898733 := bstep (se 3 (by rfl) ⟨731012, by rfl⟩ : syracuseStep 3898733 = 1462025) B1462025
theorem B7896527 : Blo 1036608 7896527 := bstep (se 1 (by rfl) ⟨5922395, by rfl⟩ : syracuseStep 7896527 = 11844791) B11844791
theorem B25624349 : Blo 1036608 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B3506003 : Blo 1036608 3506003 := bstep (se 1 (by rfl) ⟨2629502, by rfl⟩ : syracuseStep 3506003 = 5259005) B5259005
theorem B3506111 : Blo 1036608 3506111 := bstep (se 1 (by rfl) ⟨2629583, by rfl⟩ : syracuseStep 3506111 = 5259167) B5259167
theorem B22447847 : Blo 1036608 22447847 := bstep (se 1 (by rfl) ⟨16835885, by rfl⟩ : syracuseStep 22447847 = 33671771) B33671771
theorem B19990547 : Blo 1036608 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B22448461 : Blo 1036608 22448461 := bstep (se 3 (by rfl) ⟨4209086, by rfl⟩ : syracuseStep 22448461 = 8418173) B8418173
theorem B2492975 : Blo 1036608 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B2952359 : Blo 1036608 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B2624825 : Blo 1036608 2624825 := bstep (se 2 (by rfl) ⟨984309, by rfl⟩ : syracuseStep 2624825 = 1968619) B1968619
theorem B3509675 : Blo 1036608 3509675 := bstep (se 1 (by rfl) ⟨2632256, by rfl⟩ : syracuseStep 3509675 = 5264513) B5264513
theorem B5607119 : Blo 1036608 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1969895 : Blo 1036608 1969895 := bstep (se 1 (by rfl) ⟨1477421, by rfl⟩ : syracuseStep 1969895 = 2954843) B2954843
theorem B1773307 : Blo 1036608 1773307 := bstep (se 1 (by rfl) ⟨1329980, by rfl⟩ : syracuseStep 1773307 = 2659961) B2659961
theorem B2625767 : Blo 1036608 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B14946551 : Blo 1036608 14946551 := bstep (se 1 (by rfl) ⟨11209913, by rfl⟩ : syracuseStep 14946551 = 22419827) B22419827
theorem B48632183 : Blo 1036608 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B19993007 : Blo 1036608 19993007 := bstep (se 1 (by rfl) ⟨14994755, by rfl⟩ : syracuseStep 19993007 = 29989511) B29989511
theorem B3510971 : Blo 1036608 3510971 := bstep (se 1 (by rfl) ⟨2633228, by rfl⟩ : syracuseStep 3510971 = 5266457) B5266457
theorem B3511079 : Blo 1036608 3511079 := bstep (se 1 (by rfl) ⟨2633309, by rfl⟩ : syracuseStep 3511079 = 5266619) B5266619
theorem B9966827 : Blo 1036608 9966827 := bstep (se 1 (by rfl) ⟨7475120, by rfl⟩ : syracuseStep 9966827 = 14950241) B14950241
theorem B3937693 : Blo 1036608 3937693 := bstep (se 3 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 3937693 = 1476635) B1476635
theorem B2627063 : Blo 1036608 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B2627579 : Blo 1036608 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B2955503 : Blo 1036608 2955503 := bstep (se 1 (by rfl) ⟨2216627, by rfl⟩ : syracuseStep 2955503 = 4433255) B4433255
theorem B9967981 : Blo 1036608 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B2497127 : Blo 1036608 2497127 := bstep (se 1 (by rfl) ⟨1872845, by rfl⟩ : syracuseStep 2497127 = 3745691) B3745691
theorem B3938969 : Blo 1036608 3938969 := bstep (se 2 (by rfl) ⟨1477113, by rfl⟩ : syracuseStep 3938969 = 2954227) B2954227
theorem B2333375 : Blo 1036608 2333375 := bstep (se 1 (by rfl) ⟨1750031, by rfl⟩ : syracuseStep 2333375 = 3500063) B3500063
theorem B5249771 : Blo 1036608 5249771 := bstep (se 1 (by rfl) ⟨3937328, by rfl⟩ : syracuseStep 5249771 = 7874657) B7874657
theorem B1973479 : Blo 1036608 1973479 := bstep (se 1 (by rfl) ⟨1480109, by rfl⟩ : syracuseStep 1973479 = 2960219) B2960219
theorem B2957087 : Blo 1036608 2957087 := bstep (se 1 (by rfl) ⟨2217815, by rfl⟩ : syracuseStep 2957087 = 4435631) B4435631
theorem B2335391 : Blo 1036608 2335391 := bstep (se 1 (by rfl) ⟨1751543, by rfl⟩ : syracuseStep 2335391 = 3503087) B3503087
theorem B75735809 : Blo 1036608 75735809 := bstep (se 2 (by rfl) ⟨28400928, by rfl⟩ : syracuseStep 75735809 = 56801857) B56801857
theorem B10396621 : Blo 1036608 10396621 := bstep (se 3 (by rfl) ⟨1949366, by rfl⟩ : syracuseStep 10396621 = 3898733) B3898733
theorem B2958419 : Blo 1036608 2958419 := bstep (se 1 (by rfl) ⟨2218814, by rfl⟩ : syracuseStep 2958419 = 4437629) B4437629
theorem B5252201 : Blo 1036608 5252201 := bstep (se 2 (by rfl) ⟨1969575, by rfl⟩ : syracuseStep 5252201 = 3939151) B3939151
theorem B2335931 : Blo 1036608 2335931 := bstep (se 1 (by rfl) ⟨1751948, by rfl⟩ : syracuseStep 2335931 = 3503897) B3503897
theorem B2958875 : Blo 1036608 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B60696377 : Blo 1036608 60696377 := bstep (se 2 (by rfl) ⟨22761141, by rfl⟩ : syracuseStep 60696377 = 45522283) B45522283
theorem B4991179 : Blo 1036608 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B3942827 : Blo 1036608 3942827 := bstep (se 1 (by rfl) ⟨2957120, by rfl⟩ : syracuseStep 3942827 = 5914241) B5914241
theorem B17082899 : Blo 1036608 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B2337335 : Blo 1036608 2337335 := bstep (se 1 (by rfl) ⟨1753001, by rfl⟩ : syracuseStep 2337335 = 3506003) B3506003
theorem B2337407 : Blo 1036608 2337407 := bstep (se 1 (by rfl) ⟨1753055, by rfl⟩ : syracuseStep 2337407 = 3506111) B3506111
theorem B2960185 : Blo 1036608 2960185 := bstep (se 2 (by rfl) ⟨1110069, by rfl⟩ : syracuseStep 2960185 = 2220139) B2220139
theorem B2337929 : Blo 1036608 2337929 := bstep (se 2 (by rfl) ⟨876723, by rfl⟩ : syracuseStep 2337929 = 1753447) B1753447
theorem B2337983 : Blo 1036608 2337983 := bstep (se 1 (by rfl) ⟨1753487, by rfl⟩ : syracuseStep 2337983 = 3506975) B3506975
theorem B2632895 : Blo 1036608 2632895 := bstep (se 1 (by rfl) ⟨1974671, by rfl⟩ : syracuseStep 2632895 = 3949343) B3949343
theorem B5909867 : Blo 1036608 5909867 := bstep (se 1 (by rfl) ⟨4432400, by rfl⟩ : syracuseStep 5909867 = 8864801) B8864801
theorem B2633705 : Blo 1036608 2633705 := bstep (se 2 (by rfl) ⟨987639, by rfl⟩ : syracuseStep 2633705 = 1975279) B1975279
theorem B7876601 : Blo 1036608 7876601 := bstep (se 2 (by rfl) ⟨2953725, by rfl⟩ : syracuseStep 7876601 = 5907451) B5907451
theorem B2338811 : Blo 1036608 2338811 := bstep (se 1 (by rfl) ⟨1754108, by rfl⟩ : syracuseStep 2338811 = 3508217) B3508217
theorem B2339243 : Blo 1036608 2339243 := bstep (se 1 (by rfl) ⟨1754432, by rfl⟩ : syracuseStep 2339243 = 3508865) B3508865
theorem B2339495 : Blo 1036608 2339495 := bstep (se 1 (by rfl) ⟨1754621, by rfl⟩ : syracuseStep 2339495 = 3509243) B3509243
theorem B4502333 : Blo 1036608 4502333 := bstep (se 3 (by rfl) ⟨844187, by rfl⟩ : syracuseStep 4502333 = 1688375) B1688375
theorem B44872865 : Blo 1036608 44872865 := bstep (se 2 (by rfl) ⟨16827324, by rfl⟩ : syracuseStep 44872865 = 33654649) B33654649
theorem B5256413 : Blo 1036608 5256413 := bstep (se 3 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 5256413 = 1971155) B1971155
theorem B2340179 : Blo 1036608 2340179 := bstep (se 1 (by rfl) ⟨1755134, by rfl⟩ : syracuseStep 2340179 = 3510269) B3510269
theorem B5256575 : Blo 1036608 5256575 := bstep (se 1 (by rfl) ⟨3942431, by rfl⟩ : syracuseStep 5256575 = 7884863) B7884863
theorem B2962975 : Blo 1036608 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B2963135 : Blo 1036608 2963135 := bstep (se 1 (by rfl) ⟨2222351, by rfl⟩ : syracuseStep 2963135 = 4444703) B4444703
theorem B3946927 : Blo 1036608 3946927 := bstep (se 1 (by rfl) ⟨2960195, by rfl⟩ : syracuseStep 3946927 = 5920391) B5920391
theorem B1554923 : Blo 1036608 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B1555163 : Blo 1036608 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B8862817 : Blo 1036608 8862817 := bstep (se 2 (by rfl) ⟨3323556, by rfl⟩ : syracuseStep 8862817 = 6647113) B6647113
theorem B3947885 : Blo 1036608 3947885 := bstep (se 3 (by rfl) ⟨740228, by rfl⟩ : syracuseStep 3947885 = 1480457) B1480457
theorem B1752475 : Blo 1036608 1752475 := bstep (se 1 (by rfl) ⟨1314356, by rfl⟩ : syracuseStep 1752475 = 2628713) B2628713
theorem B1556255 : Blo 1036608 1556255 := bstep (se 1 (by rfl) ⟨1167191, by rfl⟩ : syracuseStep 1556255 = 2334383) B2334383
theorem B4440055 : Blo 1036608 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B1556735 : Blo 1036608 1556735 := bstep (se 1 (by rfl) ⟨1167551, by rfl⟩ : syracuseStep 1556735 = 2335103) B2335103
theorem B4997791 : Blo 1036608 4997791 := bstep (se 1 (by rfl) ⟨3748343, by rfl⟩ : syracuseStep 4997791 = 7496687) B7496687
theorem B1557407 : Blo 1036608 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B1557575 : Blo 1036608 1557575 := bstep (se 1 (by rfl) ⟨1168181, by rfl⟩ : syracuseStep 1557575 = 2336363) B2336363
theorem B1557815 : Blo 1036608 1557815 := bstep (se 1 (by rfl) ⟨1168361, by rfl⟩ : syracuseStep 1557815 = 2336723) B2336723
theorem B1557887 : Blo 1036608 1557887 := bstep (se 1 (by rfl) ⟨1168415, by rfl⟩ : syracuseStep 1557887 = 2336831) B2336831
theorem B22431239 : Blo 1036608 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B1558427 : Blo 1036608 1558427 := bstep (se 1 (by rfl) ⟨1168820, by rfl⟩ : syracuseStep 1558427 = 2337641) B2337641
theorem B1755391 : Blo 1036608 1755391 := bstep (se 1 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 1755391 = 2633087) B2633087
theorem B4442617 : Blo 1036608 4442617 := bstep (se 2 (by rfl) ⟨1665981, by rfl⟩ : syracuseStep 4442617 = 3331963) B3331963
theorem B5261921 : Blo 1036608 5261921 := bstep (se 2 (by rfl) ⟨1973220, by rfl⟩ : syracuseStep 5261921 = 3946441) B3946441
theorem B7981823 : Blo 1036608 7981823 := bstep (se 1 (by rfl) ⟨5986367, by rfl⟩ : syracuseStep 7981823 = 11972735) B11972735
theorem B1559399 : Blo 1036608 1559399 := bstep (se 1 (by rfl) ⟨1169549, by rfl⟩ : syracuseStep 1559399 = 2339099) B2339099
theorem B3328991 : Blo 1036608 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B5917931 : Blo 1036608 5917931 := bstep (se 1 (by rfl) ⟨4438448, by rfl⟩ : syracuseStep 5917931 = 8876897) B8876897
theorem B16862489 : Blo 1036608 16862489 := bstep (se 2 (by rfl) ⟨6323433, by rfl⟩ : syracuseStep 16862489 = 12646867) B12646867
theorem B1068967 : Blo 1036608 1068967 := bstep (se 1 (by rfl) ⟨801725, by rfl⟩ : syracuseStep 1068967 = 1603451) B1603451
theorem B1167295 : Blo 1036608 1167295 := bstep (se 1 (by rfl) ⟨875471, by rfl⟩ : syracuseStep 1167295 = 1750943) B1750943
theorem B2215927 : Blo 1036608 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B1560569 : Blo 1036608 1560569 := bstep (se 2 (by rfl) ⟨585213, by rfl⟩ : syracuseStep 1560569 = 1170427) B1170427
theorem B1560809 : Blo 1036608 1560809 := bstep (se 2 (by rfl) ⟨585303, by rfl⟩ : syracuseStep 1560809 = 1170607) B1170607
theorem B2216423 : Blo 1036608 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B1036891 : Blo 1036608 1036891 := bstep (se 1 (by rfl) ⟨777668, by rfl⟩ : syracuseStep 1036891 = 1555337) B1555337
theorem B2806751 : Blo 1036608 2806751 := bstep (se 1 (by rfl) ⟨2105063, by rfl⟩ : syracuseStep 2806751 = 4210127) B4210127
theorem B5264351 : Blo 1036608 5264351 := bstep (se 1 (by rfl) ⟨3948263, by rfl⟩ : syracuseStep 5264351 = 7896527) B7896527
theorem B1168411 : Blo 1036608 1168411 := bstep (se 1 (by rfl) ⟨876308, by rfl⟩ : syracuseStep 1168411 = 1752617) B1752617
theorem B1037403 : Blo 1036608 1037403 := bstep (se 1 (by rfl) ⟨778052, by rfl⟩ : syracuseStep 1037403 = 1556105) B1556105
theorem B1037695 : Blo 1036608 1037695 := bstep (se 1 (by rfl) ⟨778271, by rfl⟩ : syracuseStep 1037695 = 1556543) B1556543
theorem B1037759 : Blo 1036608 1037759 := bstep (se 1 (by rfl) ⟨778319, by rfl⟩ : syracuseStep 1037759 = 1556639) B1556639
theorem B21288395 : Blo 1036608 21288395 := bstep (se 1 (by rfl) ⟨15966296, by rfl⟩ : syracuseStep 21288395 = 31932593) B31932593
theorem B1037927 : Blo 1036608 1037927 := bstep (se 1 (by rfl) ⟨778445, by rfl⟩ : syracuseStep 1037927 = 1556891) B1556891
theorem B5920573 : Blo 1036608 5920573 := bstep (se 3 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 5920573 = 2220215) B2220215
theorem B1038207 : Blo 1036608 1038207 := bstep (se 1 (by rfl) ⟨778655, by rfl⟩ : syracuseStep 1038207 = 1557311) B1557311
theorem B64018343 : Blo 1036608 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B1038695 : Blo 1036608 1038695 := bstep (se 1 (by rfl) ⟨779021, by rfl⟩ : syracuseStep 1038695 = 1558043) B1558043
theorem B1038783 : Blo 1036608 1038783 := bstep (se 1 (by rfl) ⟨779087, by rfl⟩ : syracuseStep 1038783 = 1558175) B1558175
theorem B2808361 : Blo 1036608 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B1038975 : Blo 1036608 1038975 := bstep (se 1 (by rfl) ⟨779231, by rfl⟩ : syracuseStep 1038975 = 1558463) B1558463
theorem B9460415 : Blo 1036608 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B2219071 : Blo 1036608 2219071 := bstep (se 1 (by rfl) ⟨1664303, by rfl⟩ : syracuseStep 2219071 = 3328607) B3328607
theorem B1039839 : Blo 1036608 1039839 := bstep (se 1 (by rfl) ⟨779879, by rfl⟩ : syracuseStep 1039839 = 1559759) B1559759
theorem B1039919 : Blo 1036608 1039919 := bstep (se 1 (by rfl) ⟨779939, by rfl⟩ : syracuseStep 1039919 = 1559879) B1559879
theorem B5922557 : Blo 1036608 5922557 := bstep (se 3 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 5922557 = 2220959) B2220959
theorem B1040191 : Blo 1036608 1040191 := bstep (se 1 (by rfl) ⟨780143, by rfl⟩ : syracuseStep 1040191 = 1560287) B1560287
theorem B1040431 : Blo 1036608 1040431 := bstep (se 1 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 1040431 = 1560647) B1560647
theorem B1040511 : Blo 1036608 1040511 := bstep (se 1 (by rfl) ⟨780383, by rfl⟩ : syracuseStep 1040511 = 1560767) B1560767
theorem B1040607 : Blo 1036608 1040607 := bstep (se 1 (by rfl) ⟨780455, by rfl⟩ : syracuseStep 1040607 = 1560911) B1560911
theorem B29942459 : Blo 1036608 29942459 := bstep (se 1 (by rfl) ⟨22456844, by rfl⟩ : syracuseStep 29942459 = 44913689) B44913689
theorem B4743983 : Blo 1036608 4743983 := bstep (se 1 (by rfl) ⟨3557987, by rfl⟩ : syracuseStep 4743983 = 7115975) B7115975
theorem B3499199 : Blo 1036608 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B4744423 : Blo 1036608 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B1107199 : Blo 1036608 1107199 := bstep (se 1 (by rfl) ⟨830399, by rfl⟩ : syracuseStep 1107199 = 1660799) B1660799
theorem B3499361 : Blo 1036608 3499361 := bstep (se 2 (by rfl) ⟨1312260, by rfl⟩ : syracuseStep 3499361 = 2624521) B2624521
theorem B4745735 : Blo 1036608 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B8219999 : Blo 1036608 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B7893611 : Blo 1036608 7893611 := bstep (se 1 (by rfl) ⟨5920208, by rfl⟩ : syracuseStep 7893611 = 11840417) B11840417
theorem B5993455 : Blo 1036608 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B75887603 : Blo 1036608 75887603 := bstep (se 1 (by rfl) ⟨56915702, by rfl⟩ : syracuseStep 75887603 = 113831405) B113831405
theorem B3503357 : Blo 1036608 3503357 := bstep (se 3 (by rfl) ⟨656879, by rfl⟩ : syracuseStep 3503357 = 1313759) B1313759
theorem B26637659 : Blo 1036608 26637659 := bstep (se 1 (by rfl) ⟨19978244, by rfl⟩ : syracuseStep 26637659 = 39956489) B39956489
theorem B48592429 : Blo 1036608 48592429 := bstep (se 3 (by rfl) ⟨9111080, by rfl⟩ : syracuseStep 48592429 = 18222161) B18222161
theorem B5339627 : Blo 1036608 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B13862161 : Blo 1036608 13862161 := bstep (se 2 (by rfl) ⟨5198310, by rfl⟩ : syracuseStep 13862161 = 10396621) B10396621
theorem B6325897 : Blo 1036608 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B3507947 : Blo 1036608 3507947 := bstep (se 1 (by rfl) ⟨2630960, by rfl⟩ : syracuseStep 3507947 = 5261921) B5261921
theorem B1968239 : Blo 1036608 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B11241659 : Blo 1036608 11241659 := bstep (se 1 (by rfl) ⟨8431244, by rfl⟩ : syracuseStep 11241659 = 16862489) B16862489
theorem B3738079 : Blo 1036608 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B1313263 : Blo 1036608 1313263 := bstep (se 1 (by rfl) ⟨984947, by rfl⟩ : syracuseStep 1313263 = 1969895) B1969895
theorem B9964367 : Blo 1036608 9964367 := bstep (se 1 (by rfl) ⟨7473275, by rfl⟩ : syracuseStep 9964367 = 14946551) B14946551
theorem B6654905 : Blo 1036608 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B1477615 : Blo 1036608 1477615 := bstep (se 1 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 1477615 = 2216423) B2216423
theorem B1871167 : Blo 1036608 1871167 := bstep (se 1 (by rfl) ⟨1403375, by rfl⟩ : syracuseStep 1871167 = 2806751) B2806751
theorem B3509567 : Blo 1036608 3509567 := bstep (se 1 (by rfl) ⟨2632175, by rfl⟩ : syracuseStep 3509567 = 5264351) B5264351
theorem B14192263 : Blo 1036608 14192263 := bstep (se 1 (by rfl) ⟨10644197, by rfl⟩ : syracuseStep 14192263 = 21288395) B21288395
theorem B1970335 : Blo 1036608 1970335 := bstep (se 1 (by rfl) ⟨1477751, by rfl⟩ : syracuseStep 1970335 = 2955503) B2955503
theorem B2625979 : Blo 1036608 2625979 := bstep (se 1 (by rfl) ⟨1969484, by rfl⟩ : syracuseStep 2625979 = 3938969) B3938969
theorem B2364409 : Blo 1036608 2364409 := bstep (se 2 (by rfl) ⟨886653, by rfl⟩ : syracuseStep 2364409 = 1773307) B1773307
theorem B1971391 : Blo 1036608 1971391 := bstep (se 1 (by rfl) ⟨1478543, by rfl⟩ : syracuseStep 1971391 = 2957087) B2957087
theorem B2954569 : Blo 1036608 2954569 := bstep (se 2 (by rfl) ⟨1107963, by rfl⟩ : syracuseStep 2954569 = 2215927) B2215927
theorem B19961639 : Blo 1036608 19961639 := bstep (se 1 (by rfl) ⟨14971229, by rfl⟩ : syracuseStep 19961639 = 29942459) B29942459
theorem B1972279 : Blo 1036608 1972279 := bstep (se 1 (by rfl) ⟨1479209, by rfl⟩ : syracuseStep 1972279 = 2958419) B2958419
theorem B2332799 : Blo 1036608 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B2332907 : Blo 1036608 2332907 := bstep (se 1 (by rfl) ⟨1749680, by rfl⟩ : syracuseStep 2332907 = 3499361) B3499361
theorem B1972583 : Blo 1036608 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B5905061 : Blo 1036608 5905061 := bstep (se 4 (by rfl) ⟨553599, by rfl⟩ : syracuseStep 5905061 = 1107199) B1107199
theorem B6659005 : Blo 1036608 6659005 := bstep (se 3 (by rfl) ⟨1248563, by rfl⟩ : syracuseStep 6659005 = 2497127) B2497127
theorem B2628551 : Blo 1036608 2628551 := bstep (se 1 (by rfl) ⟨1971413, by rfl⟩ : syracuseStep 2628551 = 3942827) B3942827
theorem B5250257 : Blo 1036608 5250257 := bstep (se 2 (by rfl) ⟨1968846, by rfl⟩ : syracuseStep 5250257 = 3937693) B3937693
theorem B3939911 : Blo 1036608 3939911 := bstep (se 1 (by rfl) ⟨2954933, by rfl⟩ : syracuseStep 3939911 = 5909867) B5909867
theorem B5251067 : Blo 1036608 5251067 := bstep (se 1 (by rfl) ⟨3938300, by rfl⟩ : syracuseStep 5251067 = 7876601) B7876601
theorem B3744481 : Blo 1036608 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B2335571 : Blo 1036608 2335571 := bstep (se 1 (by rfl) ⟨1751678, by rfl⟩ : syracuseStep 2335571 = 3503357) B3503357
theorem B1975423 : Blo 1036608 1975423 := bstep (se 1 (by rfl) ⟨1481567, by rfl⟩ : syracuseStep 1975423 = 2963135) B2963135
theorem B2958761 : Blo 1036608 2958761 := bstep (se 2 (by rfl) ⟨1109535, by rfl⟩ : syracuseStep 2958761 = 2219071) B2219071
theorem B2631305 : Blo 1036608 2631305 := bstep (se 2 (by rfl) ⟨986739, by rfl⟩ : syracuseStep 2631305 = 1973479) B1973479
theorem B2336633 : Blo 1036608 2336633 := bstep (se 2 (by rfl) ⟨876237, by rfl⟩ : syracuseStep 2336633 = 1752475) B1752475
theorem B2631923 : Blo 1036608 2631923 := bstep (se 1 (by rfl) ⟨1973942, by rfl⟩ : syracuseStep 2631923 = 3947885) B3947885
theorem B6663721 : Blo 1036608 6663721 := bstep (se 2 (by rfl) ⟨2498895, by rfl⟩ : syracuseStep 6663721 = 4997791) B4997791
theorem B14954159 : Blo 1036608 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B5321215 : Blo 1036608 5321215 := bstep (se 1 (by rfl) ⟨3990911, by rfl⟩ : syracuseStep 5321215 = 7981823) B7981823
theorem B3945287 : Blo 1036608 3945287 := bstep (se 1 (by rfl) ⟨2958965, by rfl⟩ : syracuseStep 3945287 = 5917931) B5917931
theorem B1749883 : Blo 1036608 1749883 := bstep (se 1 (by rfl) ⟨1312412, by rfl⟩ : syracuseStep 1749883 = 2624825) B2624825
theorem B2339783 : Blo 1036608 2339783 := bstep (se 1 (by rfl) ⟨1754837, by rfl⟩ : syracuseStep 2339783 = 3509675) B3509675
theorem B1750511 : Blo 1036608 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B32421455 : Blo 1036608 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B2340521 : Blo 1036608 2340521 := bstep (se 2 (by rfl) ⟨877695, by rfl⟩ : syracuseStep 2340521 = 1755391) B1755391
theorem B29931281 : Blo 1036608 29931281 := bstep (se 2 (by rfl) ⟨11224230, by rfl⟩ : syracuseStep 29931281 = 22448461) B22448461
theorem B2340647 : Blo 1036608 2340647 := bstep (se 1 (by rfl) ⟨1755485, by rfl⟩ : syracuseStep 2340647 = 3510971) B3510971
theorem B2340719 : Blo 1036608 2340719 := bstep (se 1 (by rfl) ⟨1755539, by rfl⟩ : syracuseStep 2340719 = 3511079) B3511079
theorem B1751375 : Blo 1036608 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B3946913 : Blo 1036608 3946913 := bstep (se 2 (by rfl) ⟨1480092, by rfl⟩ : syracuseStep 3946913 = 2960185) B2960185
theorem B42678895 : Blo 1036608 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B1751719 : Blo 1036608 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B6306943 : Blo 1036608 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B1555583 : Blo 1036608 1555583 := bstep (se 1 (by rfl) ⟨1166687, by rfl⟩ : syracuseStep 1555583 = 2333375) B2333375
theorem B3948371 : Blo 1036608 3948371 := bstep (se 1 (by rfl) ⟨2961278, by rfl⟩ : syracuseStep 3948371 = 5922557) B5922557
theorem B1425289 : Blo 1036608 1425289 := bstep (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) B1068967
theorem B1556393 : Blo 1036608 1556393 := bstep (se 2 (by rfl) ⟨583647, by rfl⟩ : syracuseStep 1556393 = 1167295) B1167295
theorem B1556927 : Blo 1036608 1556927 := bstep (se 1 (by rfl) ⟨1167695, by rfl⟩ : syracuseStep 1556927 = 2335391) B2335391
theorem B3162655 : Blo 1036608 3162655 := bstep (se 1 (by rfl) ⟨2371991, by rfl⟩ : syracuseStep 3162655 = 4743983) B4743983
theorem B1557287 : Blo 1036608 1557287 := bstep (se 1 (by rfl) ⟨1167965, by rfl⟩ : syracuseStep 1557287 = 2335931) B2335931
theorem B1557881 : Blo 1036608 1557881 := bstep (se 2 (by rfl) ⟨584205, by rfl⟩ : syracuseStep 1557881 = 1168411) B1168411
theorem B3163823 : Blo 1036608 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B11388599 : Blo 1036608 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B1558223 : Blo 1036608 1558223 := bstep (se 1 (by rfl) ⟨1168667, by rfl⟩ : syracuseStep 1558223 = 2337335) B2337335
theorem B1558271 : Blo 1036608 1558271 := bstep (se 1 (by rfl) ⟨1168703, by rfl⟩ : syracuseStep 1558271 = 2337407) B2337407
theorem B3950633 : Blo 1036608 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B1558619 : Blo 1036608 1558619 := bstep (se 1 (by rfl) ⟨1168964, by rfl⟩ : syracuseStep 1558619 = 2337929) B2337929
theorem B1558655 : Blo 1036608 1558655 := bstep (se 1 (by rfl) ⟨1168991, by rfl⟩ : syracuseStep 1558655 = 2337983) B2337983
theorem B1755263 : Blo 1036608 1755263 := bstep (se 1 (by rfl) ⟨1316447, by rfl⟩ : syracuseStep 1755263 = 2632895) B2632895
theorem B1755803 : Blo 1036608 1755803 := bstep (se 1 (by rfl) ⟨1316852, by rfl⟩ : syracuseStep 1755803 = 2633705) B2633705
theorem B1559207 : Blo 1036608 1559207 := bstep (se 1 (by rfl) ⟨1169405, by rfl⟩ : syracuseStep 1559207 = 2338811) B2338811
theorem B1559495 : Blo 1036608 1559495 := bstep (se 1 (by rfl) ⟨1169621, by rfl⟩ : syracuseStep 1559495 = 2339243) B2339243
theorem B5262407 : Blo 1036608 5262407 := bstep (se 1 (by rfl) ⟨3946805, by rfl⟩ : syracuseStep 5262407 = 7893611) B7893611
theorem B1559663 : Blo 1036608 1559663 := bstep (se 1 (by rfl) ⟨1169747, by rfl⟩ : syracuseStep 1559663 = 2339495) B2339495
theorem B13290641 : Blo 1036608 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B3001555 : Blo 1036608 3001555 := bstep (se 1 (by rfl) ⟨2251166, by rfl⟩ : syracuseStep 3001555 = 4502333) B4502333
theorem B5262569 : Blo 1036608 5262569 := bstep (se 2 (by rfl) ⟨1973463, by rfl⟩ : syracuseStep 5262569 = 3946927) B3946927
theorem B1560119 : Blo 1036608 1560119 := bstep (se 1 (by rfl) ⟨1170089, by rfl⟩ : syracuseStep 1560119 = 2340179) B2340179
theorem B11817089 : Blo 1036608 11817089 := bstep (se 2 (by rfl) ⟨4431408, by rfl⟩ : syracuseStep 11817089 = 8862817) B8862817
theorem B1036615 : Blo 1036608 1036615 := bstep (se 1 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 1036615 = 1554923) B1554923
theorem B3559751 : Blo 1036608 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B1036775 : Blo 1036608 1036775 := bstep (se 1 (by rfl) ⟨777581, by rfl⟩ : syracuseStep 1036775 = 1555163) B1555163
theorem B1037503 : Blo 1036608 1037503 := bstep (se 1 (by rfl) ⟨778127, by rfl⟩ : syracuseStep 1037503 = 1556255) B1556255
theorem B5920073 : Blo 1036608 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B1037823 : Blo 1036608 1037823 := bstep (se 1 (by rfl) ⟨778367, by rfl⟩ : syracuseStep 1037823 = 1556735) B1556735
theorem B1038271 : Blo 1036608 1038271 := bstep (se 1 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 1038271 = 1557407) B1557407
theorem B1038383 : Blo 1036608 1038383 := bstep (se 1 (by rfl) ⟨778787, by rfl⟩ : syracuseStep 1038383 = 1557575) B1557575
theorem B1038543 : Blo 1036608 1038543 := bstep (se 1 (by rfl) ⟨778907, by rfl⟩ : syracuseStep 1038543 = 1557815) B1557815
theorem B1038591 : Blo 1036608 1038591 := bstep (se 1 (by rfl) ⟨778943, by rfl⟩ : syracuseStep 1038591 = 1557887) B1557887
theorem B14965231 : Blo 1036608 14965231 := bstep (se 1 (by rfl) ⟨11223923, by rfl⟩ : syracuseStep 14965231 = 22447847) B22447847
theorem B1038951 : Blo 1036608 1038951 := bstep (se 1 (by rfl) ⟨779213, by rfl⟩ : syracuseStep 1038951 = 1558427) B1558427
theorem B13327031 : Blo 1036608 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B1039599 : Blo 1036608 1039599 := bstep (se 1 (by rfl) ⟨779699, by rfl⟩ : syracuseStep 1039599 = 1559399) B1559399
theorem B2219327 : Blo 1036608 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B1040379 : Blo 1036608 1040379 := bstep (se 1 (by rfl) ⟨780284, by rfl⟩ : syracuseStep 1040379 = 1560569) B1560569
theorem B1040539 : Blo 1036608 1040539 := bstep (se 1 (by rfl) ⟨780404, by rfl⟩ : syracuseStep 1040539 = 1560809) B1560809
theorem B13328671 : Blo 1036608 13328671 := bstep (se 1 (by rfl) ⟨9996503, by rfl⟩ : syracuseStep 13328671 = 19993007) B19993007
theorem B5923489 : Blo 1036608 5923489 := bstep (se 2 (by rfl) ⟨2221308, by rfl⟩ : syracuseStep 5923489 = 4442617) B4442617
theorem B6644551 : Blo 1036608 6644551 := bstep (se 1 (by rfl) ⟨4983413, by rfl⟩ : syracuseStep 6644551 = 9966827) B9966827
theorem B3499847 : Blo 1036608 3499847 := bstep (se 1 (by rfl) ⟨2624885, by rfl⟩ : syracuseStep 3499847 = 5249771) B5249771
theorem B50490539 : Blo 1036608 50490539 := bstep (se 1 (by rfl) ⟨37867904, by rfl⟩ : syracuseStep 50490539 = 75735809) B75735809
theorem B3501467 : Blo 1036608 3501467 := bstep (se 1 (by rfl) ⟨2626100, by rfl⟩ : syracuseStep 3501467 = 5252201) B5252201
theorem B40464251 : Blo 1036608 40464251 := bstep (se 1 (by rfl) ⟨30348188, by rfl⟩ : syracuseStep 40464251 = 60696377) B60696377
theorem B7991273 : Blo 1036608 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B6647933 : Blo 1036608 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B7894097 : Blo 1036608 7894097 := bstep (se 2 (by rfl) ⟨2960286, by rfl⟩ : syracuseStep 7894097 = 5920573) B5920573
theorem B259159621 : Blo 1036608 259159621 := bstep (se 4 (by rfl) ⟨24296214, by rfl⟩ : syracuseStep 259159621 = 48592429) B48592429
theorem B50591735 : Blo 1036608 50591735 := bstep (se 1 (by rfl) ⟨37943801, by rfl⟩ : syracuseStep 50591735 = 75887603) B75887603
theorem B29915243 : Blo 1036608 29915243 := bstep (se 1 (by rfl) ⟨22436432, by rfl⟩ : syracuseStep 29915243 = 44872865) B44872865
theorem B3504275 : Blo 1036608 3504275 := bstep (se 1 (by rfl) ⟨2628206, by rfl⟩ : syracuseStep 3504275 = 5256413) B5256413
theorem B17758439 : Blo 1036608 17758439 := bstep (se 1 (by rfl) ⟨13318829, by rfl⟩ : syracuseStep 17758439 = 26637659) B26637659
theorem B21919997 : Blo 1036608 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B3504383 : Blo 1036608 3504383 := bstep (se 1 (by rfl) ⟨2628287, by rfl⟩ : syracuseStep 3504383 = 5256575) B5256575
theorem B17727821 : Blo 1036608 17727821 := bstep (se 3 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 17727821 = 6647933) B6647933
theorem B7897985 : Blo 1036608 7897985 := bstep (se 2 (by rfl) ⟨2961744, by rfl⟩ : syracuseStep 7897985 = 5923489) B5923489
theorem B3508271 : Blo 1036608 3508271 := bstep (se 1 (by rfl) ⟨2631203, by rfl⟩ : syracuseStep 3508271 = 5262407) B5262407
theorem B3508379 : Blo 1036608 3508379 := bstep (se 1 (by rfl) ⟨2631284, by rfl⟩ : syracuseStep 3508379 = 5262569) B5262569
theorem B4984105 : Blo 1036608 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B13307759 : Blo 1036608 13307759 := bstep (se 1 (by rfl) ⟨9980819, by rfl⟩ : syracuseStep 13307759 = 19961639) B19961639
theorem B1970153 : Blo 1036608 1970153 := bstep (se 2 (by rfl) ⟨738807, by rfl⟩ : syracuseStep 1970153 = 1477615) B1477615
theorem B1315055 : Blo 1036608 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B2494889 : Blo 1036608 2494889 := bstep (se 2 (by rfl) ⟨935583, by rfl⟩ : syracuseStep 2494889 = 1871167) B1871167
theorem B3936707 : Blo 1036608 3936707 := bstep (se 1 (by rfl) ⟨2952530, by rfl⟩ : syracuseStep 3936707 = 5905061) B5905061
theorem B8884687 : Blo 1036608 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B8884961 : Blo 1036608 8884961 := bstep (se 2 (by rfl) ⟨3331860, by rfl⟩ : syracuseStep 8884961 = 6663721) B6663721
theorem B1479551 : Blo 1036608 1479551 := bstep (se 1 (by rfl) ⟨1109663, by rfl⟩ : syracuseStep 1479551 = 2219327) B2219327
theorem B2626607 : Blo 1036608 2626607 := bstep (se 1 (by rfl) ⟨1969955, by rfl⟩ : syracuseStep 2626607 = 3939911) B3939911
theorem B2627113 : Blo 1036608 2627113 := bstep (se 2 (by rfl) ⟨985167, by rfl⟩ : syracuseStep 2627113 = 1970335) B1970335
theorem B5248637 : Blo 1036608 5248637 := bstep (se 3 (by rfl) ⟨984119, by rfl⟩ : syracuseStep 5248637 = 1968239) B1968239
theorem B1972507 : Blo 1036608 1972507 := bstep (se 1 (by rfl) ⟨1479380, by rfl⟩ : syracuseStep 1972507 = 2958761) B2958761
theorem B2333177 : Blo 1036608 2333177 := bstep (se 2 (by rfl) ⟨874941, by rfl⟩ : syracuseStep 2333177 = 1749883) B1749883
theorem B2333231 : Blo 1036608 2333231 := bstep (se 1 (by rfl) ⟨1749923, by rfl⟩ : syracuseStep 2333231 = 3499847) B3499847
theorem B73931525 : Blo 1036608 73931525 := bstep (se 4 (by rfl) ⟨6931080, by rfl⟩ : syracuseStep 73931525 = 13862161) B13862161
theorem B2628521 : Blo 1036608 2628521 := bstep (se 2 (by rfl) ⟨985695, by rfl⟩ : syracuseStep 2628521 = 1971391) B1971391
theorem B3939425 : Blo 1036608 3939425 := bstep (se 2 (by rfl) ⟨1477284, by rfl⟩ : syracuseStep 3939425 = 2954569) B2954569
theorem B345546161 : Blo 1036608 345546161 := bstep (se 2 (by rfl) ⟨129579810, by rfl⟩ : syracuseStep 345546161 = 259159621) B259159621
theorem B33660359 : Blo 1036608 33660359 := bstep (se 1 (by rfl) ⟨25245269, by rfl⟩ : syracuseStep 33660359 = 50490539) B50490539
theorem B2334311 : Blo 1036608 2334311 := bstep (se 1 (by rfl) ⟨1750733, by rfl⟩ : syracuseStep 2334311 = 3501467) B3501467
theorem B26976167 : Blo 1036608 26976167 := bstep (se 1 (by rfl) ⟨20232125, by rfl⟩ : syracuseStep 26976167 = 40464251) B40464251
theorem B2629705 : Blo 1036608 2629705 := bstep (se 2 (by rfl) ⟨986139, by rfl⟩ : syracuseStep 2629705 = 1972279) B1972279
theorem B2630191 : Blo 1036608 2630191 := bstep (se 1 (by rfl) ⟨1972643, by rfl⟩ : syracuseStep 2630191 = 3945287) B3945287
theorem B2335625 : Blo 1036608 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B33727823 : Blo 1036608 33727823 := bstep (se 1 (by rfl) ⟨25295867, by rfl⟩ : syracuseStep 33727823 = 50591735) B50591735
theorem B2336183 : Blo 1036608 2336183 := bstep (se 1 (by rfl) ⟨1752137, by rfl⟩ : syracuseStep 2336183 = 3504275) B3504275
theorem B11838959 : Blo 1036608 11838959 := bstep (se 1 (by rfl) ⟨8879219, by rfl⟩ : syracuseStep 11838959 = 17758439) B17758439
theorem B2336255 : Blo 1036608 2336255 := bstep (se 1 (by rfl) ⟨1752191, by rfl⟩ : syracuseStep 2336255 = 3504383) B3504383
theorem B2631275 : Blo 1036608 2631275 := bstep (se 1 (by rfl) ⟨1973456, by rfl⟩ : syracuseStep 2631275 = 3946913) B3946913
theorem B2632247 : Blo 1036608 2632247 := bstep (se 1 (by rfl) ⟨1974185, by rfl⟩ : syracuseStep 2632247 = 3948371) B3948371
theorem B17771561 : Blo 1036608 17771561 := bstep (se 2 (by rfl) ⟨6664335, by rfl⟩ : syracuseStep 17771561 = 13328671) B13328671
theorem B4992641 : Blo 1036608 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B8859401 : Blo 1036608 8859401 := bstep (se 2 (by rfl) ⟨3322275, by rfl⟩ : syracuseStep 8859401 = 6644551) B6644551
theorem B2109215 : Blo 1036608 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B2338631 : Blo 1036608 2338631 := bstep (se 1 (by rfl) ⟨1753973, by rfl⟩ : syracuseStep 2338631 = 3507947) B3507947
theorem B2633755 : Blo 1036608 2633755 := bstep (se 1 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 2633755 = 3950633) B3950633
theorem B2633897 : Blo 1036608 2633897 := bstep (se 2 (by rfl) ⟨987711, by rfl⟩ : syracuseStep 2633897 = 1975423) B1975423
theorem B4436603 : Blo 1036608 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B8860427 : Blo 1036608 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B8434529 : Blo 1036608 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B2339711 : Blo 1036608 2339711 := bstep (se 1 (by rfl) ⟨1754783, by rfl⟩ : syracuseStep 2339711 = 3509567) B3509567
theorem B7878059 : Blo 1036608 7878059 := bstep (se 1 (by rfl) ⟨5908544, by rfl⟩ : syracuseStep 7878059 = 11817089) B11817089
theorem B2373167 : Blo 1036608 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B1751017 : Blo 1036608 1751017 := bstep (se 2 (by rfl) ⟨656631, by rfl⟩ : syracuseStep 1751017 = 1313263) B1313263
theorem B3946715 : Blo 1036608 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B1555199 : Blo 1036608 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B1555271 : Blo 1036608 1555271 := bstep (se 1 (by rfl) ⟨1166453, by rfl⟩ : syracuseStep 1555271 = 2332907) B2332907
theorem B1752367 : Blo 1036608 1752367 := bstep (se 1 (by rfl) ⟨1314275, by rfl⟩ : syracuseStep 1752367 = 2628551) B2628551
theorem B18923017 : Blo 1036608 18923017 := bstep (se 2 (by rfl) ⟨7096131, by rfl⟩ : syracuseStep 18923017 = 14192263) B14192263
theorem B1557047 : Blo 1036608 1557047 := bstep (se 1 (by rfl) ⟨1167785, by rfl⟩ : syracuseStep 1557047 = 2335571) B2335571
theorem B7094953 : Blo 1036608 7094953 := bstep (se 2 (by rfl) ⟨2660607, by rfl⟩ : syracuseStep 7094953 = 5321215) B5321215
theorem B1754203 : Blo 1036608 1754203 := bstep (se 1 (by rfl) ⟨1315652, by rfl⟩ : syracuseStep 1754203 = 2631305) B2631305
theorem B16008293 : Blo 1036608 16008293 := bstep (se 4 (by rfl) ⟨1500777, by rfl⟩ : syracuseStep 16008293 = 3001555) B3001555
theorem B1557755 : Blo 1036608 1557755 := bstep (se 1 (by rfl) ⟨1168316, by rfl⟩ : syracuseStep 1557755 = 2336633) B2336633
theorem B1754615 : Blo 1036608 1754615 := bstep (se 1 (by rfl) ⟨1315961, by rfl⟩ : syracuseStep 1754615 = 2631923) B2631923
theorem B5327515 : Blo 1036608 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B1559855 : Blo 1036608 1559855 := bstep (se 1 (by rfl) ⟨1169891, by rfl⟩ : syracuseStep 1559855 = 2339783) B2339783
theorem B5262731 : Blo 1036608 5262731 := bstep (se 1 (by rfl) ⟨3947048, by rfl⟩ : syracuseStep 5262731 = 7894097) B7894097
theorem B56905193 : Blo 1036608 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B1167007 : Blo 1036608 1167007 := bstep (se 1 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 1167007 = 1750511) B1750511
theorem B21614303 : Blo 1036608 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B1560347 : Blo 1036608 1560347 := bstep (se 1 (by rfl) ⟨1170260, by rfl⟩ : syracuseStep 1560347 = 2340521) B2340521
theorem B1560431 : Blo 1036608 1560431 := bstep (se 1 (by rfl) ⟨1170323, by rfl⟩ : syracuseStep 1560431 = 2340647) B2340647
theorem B1560479 : Blo 1036608 1560479 := bstep (se 1 (by rfl) ⟨1170359, by rfl⟩ : syracuseStep 1560479 = 2340719) B2340719
theorem B19943495 : Blo 1036608 19943495 := bstep (se 1 (by rfl) ⟨14957621, by rfl⟩ : syracuseStep 19943495 = 29915243) B29915243
theorem B8409257 : Blo 1036608 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B1167583 : Blo 1036608 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B1037055 : Blo 1036608 1037055 := bstep (se 1 (by rfl) ⟨777791, by rfl⟩ : syracuseStep 1037055 = 1555583) B1555583
theorem B1037595 : Blo 1036608 1037595 := bstep (se 1 (by rfl) ⟨778196, by rfl⟩ : syracuseStep 1037595 = 1556393) B1556393
theorem B1037951 : Blo 1036608 1037951 := bstep (se 1 (by rfl) ⟨778463, by rfl⟩ : syracuseStep 1037951 = 1556927) B1556927
theorem B1038191 : Blo 1036608 1038191 := bstep (se 1 (by rfl) ⟨778643, by rfl⟩ : syracuseStep 1038191 = 1557287) B1557287
theorem B4216873 : Blo 1036608 4216873 := bstep (se 2 (by rfl) ⟨1581327, by rfl⟩ : syracuseStep 4216873 = 3162655) B3162655
theorem B1038587 : Blo 1036608 1038587 := bstep (se 1 (by rfl) ⟨778940, by rfl⟩ : syracuseStep 1038587 = 1557881) B1557881
theorem B7592399 : Blo 1036608 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B1038815 : Blo 1036608 1038815 := bstep (se 1 (by rfl) ⟨779111, by rfl⟩ : syracuseStep 1038815 = 1558223) B1558223
theorem B1038847 : Blo 1036608 1038847 := bstep (se 1 (by rfl) ⟨779135, by rfl⟩ : syracuseStep 1038847 = 1558271) B1558271
theorem B1039079 : Blo 1036608 1039079 := bstep (se 1 (by rfl) ⟨779309, by rfl⟩ : syracuseStep 1039079 = 1558619) B1558619
theorem B1039103 : Blo 1036608 1039103 := bstep (se 1 (by rfl) ⟨779327, by rfl⟩ : syracuseStep 1039103 = 1558655) B1558655
theorem B1170175 : Blo 1036608 1170175 := bstep (se 1 (by rfl) ⟨877631, by rfl⟩ : syracuseStep 1170175 = 1755263) B1755263
theorem B7494439 : Blo 1036608 7494439 := bstep (se 1 (by rfl) ⟨5620829, by rfl⟩ : syracuseStep 7494439 = 11241659) B11241659
theorem B1170535 : Blo 1036608 1170535 := bstep (se 1 (by rfl) ⟨877901, by rfl⟩ : syracuseStep 1170535 = 1755803) B1755803
theorem B1039471 : Blo 1036608 1039471 := bstep (se 1 (by rfl) ⟨779603, by rfl⟩ : syracuseStep 1039471 = 1559207) B1559207
theorem B6642911 : Blo 1036608 6642911 := bstep (se 1 (by rfl) ⟨4982183, by rfl⟩ : syracuseStep 6642911 = 9964367) B9964367
theorem B1039663 : Blo 1036608 1039663 := bstep (se 1 (by rfl) ⟨779747, by rfl⟩ : syracuseStep 1039663 = 1559495) B1559495
theorem B1039775 : Blo 1036608 1039775 := bstep (se 1 (by rfl) ⟨779831, by rfl⟩ : syracuseStep 1039775 = 1559663) B1559663
theorem B1040079 : Blo 1036608 1040079 := bstep (se 1 (by rfl) ⟨780059, by rfl⟩ : syracuseStep 1040079 = 1560119) B1560119
theorem B3500171 : Blo 1036608 3500171 := bstep (se 1 (by rfl) ⟨2625128, by rfl⟩ : syracuseStep 3500171 = 5250257) B5250257
theorem B12610181 : Blo 1036608 12610181 := bstep (se 4 (by rfl) ⟨1182204, by rfl⟩ : syracuseStep 12610181 = 2364409) B2364409
theorem B3500711 : Blo 1036608 3500711 := bstep (se 1 (by rfl) ⟨2625533, by rfl⟩ : syracuseStep 3500711 = 5251067) B5251067
theorem B3501305 : Blo 1036608 3501305 := bstep (se 2 (by rfl) ⟨1312989, by rfl⟩ : syracuseStep 3501305 = 2625979) B2625979
theorem B58453325 : Blo 1036608 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B19953641 : Blo 1036608 19953641 := bstep (se 2 (by rfl) ⟨7482615, by rfl⟩ : syracuseStep 19953641 = 14965231) B14965231
theorem B19954187 : Blo 1036608 19954187 := bstep (se 1 (by rfl) ⟨14965640, by rfl⟩ : syracuseStep 19954187 = 29931281) B29931281
theorem B8878673 : Blo 1036608 8878673 := bstep (se 2 (by rfl) ⟨3329502, by rfl⟩ : syracuseStep 8878673 = 6659005) B6659005
theorem B39877757 : Blo 1036608 39877757 := bstep (se 3 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 39877757 = 14954159) B14954159
theorem B1900385 : Blo 1036608 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B3506273 : Blo 1036608 3506273 := bstep (se 2 (by rfl) ⟨1314852, by rfl⟩ : syracuseStep 3506273 = 2629705) B2629705
theorem B3506813 : Blo 1036608 3506813 := bstep (se 3 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 3506813 = 1315055) B1315055
theorem B3506921 : Blo 1036608 3506921 := bstep (se 2 (by rfl) ⟨1315095, by rfl⟩ : syracuseStep 3506921 = 2630191) B2630191
theorem B3508487 : Blo 1036608 3508487 := bstep (se 1 (by rfl) ⟨2631365, by rfl⟩ : syracuseStep 3508487 = 5262731) B5262731
theorem B1313435 : Blo 1036608 1313435 := bstep (se 1 (by rfl) ⟨985076, by rfl⟩ : syracuseStep 1313435 = 1970153) B1970153
theorem B5606171 : Blo 1036608 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B2624471 : Blo 1036608 2624471 := bstep (se 1 (by rfl) ⟨1968353, by rfl⟩ : syracuseStep 2624471 = 3936707) B3936707
theorem B28413413 : Blo 1036608 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B49287683 : Blo 1036608 49287683 := bstep (se 1 (by rfl) ⟨36965762, by rfl⟩ : syracuseStep 49287683 = 73931525) B73931525
theorem B2626283 : Blo 1036608 2626283 := bstep (se 1 (by rfl) ⟨1969712, by rfl⟩ : syracuseStep 2626283 = 3939425) B3939425
theorem B4428607 : Blo 1036608 4428607 := bstep (se 1 (by rfl) ⟨3321455, by rfl⟩ : syracuseStep 4428607 = 6642911) B6642911
theorem B230364107 : Blo 1036608 230364107 := bstep (se 1 (by rfl) ⟨172773080, by rfl⟩ : syracuseStep 230364107 = 345546161) B345546161
theorem B3511673 : Blo 1036608 3511673 := bstep (se 2 (by rfl) ⟨1316877, by rfl⟩ : syracuseStep 3511673 = 2633755) B2633755
theorem B22485215 : Blo 1036608 22485215 := bstep (se 1 (by rfl) ⟨16863911, by rfl⟩ : syracuseStep 22485215 = 33727823) B33727823
theorem B2333447 : Blo 1036608 2333447 := bstep (se 1 (by rfl) ⟨1750085, by rfl⟩ : syracuseStep 2333447 = 3500171) B3500171
theorem B2333807 : Blo 1036608 2333807 := bstep (se 1 (by rfl) ⟨1750355, by rfl⟩ : syracuseStep 2333807 = 3500711) B3500711
theorem B2334203 : Blo 1036608 2334203 := bstep (se 1 (by rfl) ⟨1750652, by rfl⟩ : syracuseStep 2334203 = 3501305) B3501305
theorem B38968883 : Blo 1036608 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B5906267 : Blo 1036608 5906267 := bstep (se 1 (by rfl) ⟨4429700, by rfl⟩ : syracuseStep 5906267 = 8859401) B8859401
theorem B2334689 : Blo 1036608 2334689 := bstep (se 2 (by rfl) ⟨875508, by rfl⟩ : syracuseStep 2334689 = 1751017) B1751017
theorem B2630009 : Blo 1036608 2630009 := bstep (se 2 (by rfl) ⟨986253, by rfl⟩ : syracuseStep 2630009 = 1972507) B1972507
theorem B2957735 : Blo 1036608 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B5906951 : Blo 1036608 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B5252039 : Blo 1036608 5252039 := bstep (se 1 (by rfl) ⟨3939029, by rfl⟩ : syracuseStep 5252039 = 7878059) B7878059
theorem B1582111 : Blo 1036608 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B2631143 : Blo 1036608 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B2336489 : Blo 1036608 2336489 := bstep (se 2 (by rfl) ⟨876183, by rfl⟩ : syracuseStep 2336489 = 1752367) B1752367
theorem B26585171 : Blo 1036608 26585171 := bstep (se 1 (by rfl) ⟨19938878, by rfl⟩ : syracuseStep 26585171 = 39877757) B39877757
theorem B2338847 : Blo 1036608 2338847 := bstep (se 1 (by rfl) ⟨1754135, by rfl⟩ : syracuseStep 2338847 = 3508271) B3508271
theorem B2338919 : Blo 1036608 2338919 := bstep (se 1 (by rfl) ⟨1754189, by rfl⟩ : syracuseStep 2338919 = 3508379) B3508379
theorem B2338937 : Blo 1036608 2338937 := bstep (se 2 (by rfl) ⟨877101, by rfl⟩ : syracuseStep 2338937 = 1754203) B1754203
theorem B3945469 : Blo 1036608 3945469 := bstep (se 3 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 3945469 = 1479551) B1479551
theorem B1751071 : Blo 1036608 1751071 := bstep (se 1 (by rfl) ⟨1313303, by rfl⟩ : syracuseStep 1751071 = 2626607) B2626607
theorem B5061599 : Blo 1036608 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B1555451 : Blo 1036608 1555451 := bstep (se 1 (by rfl) ⟨1166588, by rfl⟩ : syracuseStep 1555451 = 2333177) B2333177
theorem B1555487 : Blo 1036608 1555487 := bstep (se 1 (by rfl) ⟨1166615, by rfl⟩ : syracuseStep 1555487 = 2333231) B2333231
theorem B1752347 : Blo 1036608 1752347 := bstep (se 1 (by rfl) ⟨1314260, by rfl⟩ : syracuseStep 1752347 = 2628521) B2628521
theorem B1556009 : Blo 1036608 1556009 := bstep (se 2 (by rfl) ⟨583503, by rfl⟩ : syracuseStep 1556009 = 1167007) B1167007
theorem B1556207 : Blo 1036608 1556207 := bstep (se 1 (by rfl) ⟨1167155, by rfl⟩ : syracuseStep 1556207 = 2334311) B2334311
theorem B1556777 : Blo 1036608 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B1557083 : Blo 1036608 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B11846249 : Blo 1036608 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B1557455 : Blo 1036608 1557455 := bstep (se 1 (by rfl) ⟨1168091, by rfl⟩ : syracuseStep 1557455 = 2336183) B2336183
theorem B1557503 : Blo 1036608 1557503 := bstep (se 1 (by rfl) ⟨1168127, by rfl⟩ : syracuseStep 1557503 = 2336255) B2336255
theorem B1754183 : Blo 1036608 1754183 := bstep (se 1 (by rfl) ⟨1315637, by rfl⟩ : syracuseStep 1754183 = 2631275) B2631275
theorem B1754831 : Blo 1036608 1754831 := bstep (se 1 (by rfl) ⟨1316123, by rfl⟩ : syracuseStep 1754831 = 2632247) B2632247
theorem B8406787 : Blo 1036608 8406787 := bstep (se 1 (by rfl) ⟨6305090, by rfl⟩ : syracuseStep 8406787 = 12610181) B12610181
theorem B11847707 : Blo 1036608 11847707 := bstep (se 1 (by rfl) ⟨8885780, by rfl⟩ : syracuseStep 11847707 = 17771561) B17771561
theorem B3328427 : Blo 1036608 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B1559087 : Blo 1036608 1559087 := bstep (se 1 (by rfl) ⟨1169315, by rfl⟩ : syracuseStep 1559087 = 2338631) B2338631
theorem B5622497 : Blo 1036608 5622497 := bstep (se 2 (by rfl) ⟨2108436, by rfl⟩ : syracuseStep 5622497 = 4216873) B4216873
theorem B1755931 : Blo 1036608 1755931 := bstep (se 1 (by rfl) ⟨1316948, by rfl⟩ : syracuseStep 1755931 = 2633897) B2633897
theorem B5623019 : Blo 1036608 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B1559807 : Blo 1036608 1559807 := bstep (se 1 (by rfl) ⟨1169855, by rfl⟩ : syracuseStep 1559807 = 2339711) B2339711
theorem B1560233 : Blo 1036608 1560233 := bstep (se 2 (by rfl) ⟨585087, by rfl⟩ : syracuseStep 1560233 = 1170175) B1170175
theorem B1560713 : Blo 1036608 1560713 := bstep (se 2 (by rfl) ⟨585267, by rfl⟩ : syracuseStep 1560713 = 1170535) B1170535
theorem B5919115 : Blo 1036608 5919115 := bstep (se 1 (by rfl) ⟨4439336, by rfl⟩ : syracuseStep 5919115 = 8878673) B8878673
theorem B1036799 : Blo 1036608 1036799 := bstep (se 1 (by rfl) ⟨777599, by rfl⟩ : syracuseStep 1036799 = 1555199) B1555199
theorem B1036847 : Blo 1036608 1036847 := bstep (se 1 (by rfl) ⟨777635, by rfl⟩ : syracuseStep 1036847 = 1555271) B1555271
theorem B1266923 : Blo 1036608 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B11818547 : Blo 1036608 11818547 := bstep (se 1 (by rfl) ⟨8863910, by rfl⟩ : syracuseStep 11818547 = 17727821) B17727821
theorem B1038031 : Blo 1036608 1038031 := bstep (se 1 (by rfl) ⟨778523, by rfl⟩ : syracuseStep 1038031 = 1557047) B1557047
theorem B5265323 : Blo 1036608 5265323 := bstep (se 1 (by rfl) ⟨3948992, by rfl⟩ : syracuseStep 5265323 = 7897985) B7897985
theorem B10672195 : Blo 1036608 10672195 := bstep (se 1 (by rfl) ⟨8004146, by rfl⟩ : syracuseStep 10672195 = 16008293) B16008293
theorem B1038503 : Blo 1036608 1038503 := bstep (se 1 (by rfl) ⟨778877, by rfl⟩ : syracuseStep 1038503 = 1557755) B1557755
theorem B9459937 : Blo 1036608 9459937 := bstep (se 2 (by rfl) ⟨3547476, by rfl⟩ : syracuseStep 9459937 = 7094953) B7094953
theorem B1169743 : Blo 1036608 1169743 := bstep (se 1 (by rfl) ⟨877307, by rfl⟩ : syracuseStep 1169743 = 1754615) B1754615
theorem B1039903 : Blo 1036608 1039903 := bstep (se 1 (by rfl) ⟨779927, by rfl⟩ : syracuseStep 1039903 = 1559855) B1559855
theorem B37936795 : Blo 1036608 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B14409535 : Blo 1036608 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B1040231 : Blo 1036608 1040231 := bstep (se 1 (by rfl) ⟨780173, by rfl⟩ : syracuseStep 1040231 = 1560347) B1560347
theorem B8871839 : Blo 1036608 8871839 := bstep (se 1 (by rfl) ⟨6653879, by rfl⟩ : syracuseStep 8871839 = 13307759) B13307759
theorem B1040287 : Blo 1036608 1040287 := bstep (se 1 (by rfl) ⟨780215, by rfl⟩ : syracuseStep 1040287 = 1560431) B1560431
theorem B1040319 : Blo 1036608 1040319 := bstep (se 1 (by rfl) ⟨780239, by rfl⟩ : syracuseStep 1040319 = 1560479) B1560479
theorem B13295663 : Blo 1036608 13295663 := bstep (se 1 (by rfl) ⟨9971747, by rfl⟩ : syracuseStep 13295663 = 19943495) B19943495
theorem B1663259 : Blo 1036608 1663259 := bstep (se 1 (by rfl) ⟨1247444, by rfl⟩ : syracuseStep 1663259 = 2494889) B2494889
theorem B5923307 : Blo 1036608 5923307 := bstep (se 1 (by rfl) ⟨4442480, by rfl⟩ : syracuseStep 5923307 = 8884961) B8884961
theorem B3499091 : Blo 1036608 3499091 := bstep (se 1 (by rfl) ⟨2624318, by rfl⟩ : syracuseStep 3499091 = 5248637) B5248637
theorem B6645473 : Blo 1036608 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B22440239 : Blo 1036608 22440239 := bstep (se 1 (by rfl) ⟨16830179, by rfl⟩ : syracuseStep 22440239 = 33660359) B33660359
theorem B17984111 : Blo 1036608 17984111 := bstep (se 1 (by rfl) ⟨13488083, by rfl⟩ : syracuseStep 17984111 = 26976167) B26976167
theorem B7892639 : Blo 1036608 7892639 := bstep (se 1 (by rfl) ⟨5919479, by rfl⟩ : syracuseStep 7892639 = 11838959) B11838959
theorem B3502817 : Blo 1036608 3502817 := bstep (se 2 (by rfl) ⟨1313556, by rfl⟩ : syracuseStep 3502817 = 2627113) B2627113
theorem B1406143 : Blo 1036608 1406143 := bstep (se 1 (by rfl) ⟨1054607, by rfl⟩ : syracuseStep 1406143 = 2109215) B2109215
theorem B9992585 : Blo 1036608 9992585 := bstep (se 2 (by rfl) ⟨3747219, by rfl⟩ : syracuseStep 9992585 = 7494439) B7494439
theorem B13302427 : Blo 1036608 13302427 := bstep (se 1 (by rfl) ⟨9976820, by rfl⟩ : syracuseStep 13302427 = 19953641) B19953641
theorem B13302791 : Blo 1036608 13302791 := bstep (se 1 (by rfl) ⟨9977093, by rfl⟩ : syracuseStep 13302791 = 19954187) B19954187
theorem B25230689 : Blo 1036608 25230689 := bstep (se 2 (by rfl) ⟨9461508, by rfl⟩ : syracuseStep 25230689 = 18923017) B18923017
theorem B7897499 : Blo 1036608 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B7898471 : Blo 1036608 7898471 := bstep (se 1 (by rfl) ⟨5923853, by rfl⟩ : syracuseStep 7898471 = 11847707) B11847707
theorem B3737447 : Blo 1036608 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B18942275 : Blo 1036608 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B11209049 : Blo 1036608 11209049 := bstep (se 2 (by rfl) ⟨4203393, by rfl⟩ : syracuseStep 11209049 = 8406787) B8406787
theorem B3378461 : Blo 1036608 3378461 := bstep (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) B1266923
theorem B3510215 : Blo 1036608 3510215 := bstep (se 1 (by rfl) ⟨2632661, by rfl⟩ : syracuseStep 3510215 = 5265323) B5265323
theorem B3937511 : Blo 1036608 3937511 := bstep (se 1 (by rfl) ⟨2953133, by rfl⟩ : syracuseStep 3937511 = 5906267) B5906267
theorem B3937967 : Blo 1036608 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B2332727 : Blo 1036608 2332727 := bstep (se 1 (by rfl) ⟨1749545, by rfl⟩ : syracuseStep 2332727 = 3499091) B3499091
theorem B5904809 : Blo 1036608 5904809 := bstep (se 2 (by rfl) ⟨2214303, by rfl⟩ : syracuseStep 5904809 = 4428607) B4428607
theorem B4430315 : Blo 1036608 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B2334761 : Blo 1036608 2334761 := bstep (se 2 (by rfl) ⟨875535, by rfl⟩ : syracuseStep 2334761 = 1751071) B1751071
theorem B14229593 : Blo 1036608 14229593 := bstep (se 2 (by rfl) ⟨5336097, by rfl⟩ : syracuseStep 14229593 = 10672195) B10672195
theorem B2335211 : Blo 1036608 2335211 := bstep (se 1 (by rfl) ⟨1751408, by rfl⟩ : syracuseStep 2335211 = 3502817) B3502817
theorem B17736569 : Blo 1036608 17736569 := bstep (se 2 (by rfl) ⟨6651213, by rfl⟩ : syracuseStep 17736569 = 13302427) B13302427
theorem B6661723 : Blo 1036608 6661723 := bstep (se 1 (by rfl) ⟨4996292, by rfl⟩ : syracuseStep 6661723 = 9992585) B9992585
theorem B16820459 : Blo 1036608 16820459 := bstep (se 1 (by rfl) ⟨12615344, by rfl⟩ : syracuseStep 16820459 = 25230689) B25230689
theorem B19212713 : Blo 1036608 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B2337515 : Blo 1036608 2337515 := bstep (se 1 (by rfl) ⟨1753136, by rfl⟩ : syracuseStep 2337515 = 3506273) B3506273
theorem B2337875 : Blo 1036608 2337875 := bstep (se 1 (by rfl) ⟨1753406, by rfl⟩ : syracuseStep 2337875 = 3506813) B3506813
theorem B2337947 : Blo 1036608 2337947 := bstep (se 1 (by rfl) ⟨1753460, by rfl⟩ : syracuseStep 2337947 = 3506921) B3506921
theorem B4435357 : Blo 1036608 4435357 := bstep (se 3 (by rfl) ⟨831629, by rfl⟩ : syracuseStep 4435357 = 1663259) B1663259
theorem B2338991 : Blo 1036608 2338991 := bstep (se 1 (by rfl) ⟨1754243, by rfl⟩ : syracuseStep 2338991 = 3508487) B3508487
theorem B3748331 : Blo 1036608 3748331 := bstep (se 1 (by rfl) ⟨2811248, by rfl⟩ : syracuseStep 3748331 = 5622497) B5622497
theorem B1749647 : Blo 1036608 1749647 := bstep (se 1 (by rfl) ⟨1312235, by rfl⟩ : syracuseStep 1749647 = 2624471) B2624471
theorem B3748679 : Blo 1036608 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B1750855 : Blo 1036608 1750855 := bstep (se 1 (by rfl) ⟨1313141, by rfl⟩ : syracuseStep 1750855 = 2626283) B2626283
theorem B2341115 : Blo 1036608 2341115 := bstep (se 1 (by rfl) ⟨1755836, by rfl⟩ : syracuseStep 2341115 = 3511673) B3511673
theorem B7879031 : Blo 1036608 7879031 := bstep (se 1 (by rfl) ⟨5909273, by rfl⟩ : syracuseStep 7879031 = 11818547) B11818547
theorem B2341241 : Blo 1036608 2341241 := bstep (se 2 (by rfl) ⟨877965, by rfl⟩ : syracuseStep 2341241 = 1755931) B1755931
theorem B14990143 : Blo 1036608 14990143 := bstep (se 1 (by rfl) ⟨11242607, by rfl⟩ : syracuseStep 14990143 = 22485215) B22485215
theorem B1555631 : Blo 1036608 1555631 := bstep (se 1 (by rfl) ⟨1166723, by rfl⟩ : syracuseStep 1555631 = 2333447) B2333447
theorem B1555871 : Blo 1036608 1555871 := bstep (se 1 (by rfl) ⟨1166903, by rfl⟩ : syracuseStep 1555871 = 2333807) B2333807
theorem B1556135 : Blo 1036608 1556135 := bstep (se 1 (by rfl) ⟨1167101, by rfl⟩ : syracuseStep 1556135 = 2334203) B2334203
theorem B5914559 : Blo 1036608 5914559 := bstep (se 1 (by rfl) ⟨4435919, by rfl⟩ : syracuseStep 5914559 = 8871839) B8871839
theorem B1556459 : Blo 1036608 1556459 := bstep (se 1 (by rfl) ⟨1167344, by rfl⟩ : syracuseStep 1556459 = 2334689) B2334689
theorem B8863775 : Blo 1036608 8863775 := bstep (se 1 (by rfl) ⟨6647831, by rfl⟩ : syracuseStep 8863775 = 13295663) B13295663
theorem B8437925 : Blo 1036608 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1753339 : Blo 1036608 1753339 := bstep (se 1 (by rfl) ⟨1315004, by rfl⟩ : syracuseStep 1753339 = 2630009) B2630009
theorem B3948871 : Blo 1036608 3948871 := bstep (se 1 (by rfl) ⟨2961653, by rfl⟩ : syracuseStep 3948871 = 5923307) B5923307
theorem B1754095 : Blo 1036608 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B1557659 : Blo 1036608 1557659 := bstep (se 1 (by rfl) ⟨1168244, by rfl⟩ : syracuseStep 1557659 = 2336489) B2336489
theorem B5260625 : Blo 1036608 5260625 := bstep (se 2 (by rfl) ⟨1972734, by rfl⟩ : syracuseStep 5260625 = 3945469) B3945469
theorem B14960159 : Blo 1036608 14960159 := bstep (se 1 (by rfl) ⟨11220119, by rfl⟩ : syracuseStep 14960159 = 22440239) B22440239
theorem B47957629 : Blo 1036608 47957629 := bstep (se 3 (by rfl) ⟨8992055, by rfl⟩ : syracuseStep 47957629 = 17984111) B17984111
theorem B5261759 : Blo 1036608 5261759 := bstep (se 1 (by rfl) ⟨3946319, by rfl⟩ : syracuseStep 5261759 = 7892639) B7892639
theorem B1559231 : Blo 1036608 1559231 := bstep (se 1 (by rfl) ⟨1169423, by rfl⟩ : syracuseStep 1559231 = 2338847) B2338847
theorem B1559279 : Blo 1036608 1559279 := bstep (se 1 (by rfl) ⟨1169459, by rfl⟩ : syracuseStep 1559279 = 2338919) B2338919
theorem B1559291 : Blo 1036608 1559291 := bstep (se 1 (by rfl) ⟨1169468, by rfl⟩ : syracuseStep 1559291 = 2338937) B2338937
theorem B1559657 : Blo 1036608 1559657 := bstep (se 2 (by rfl) ⟨584871, by rfl⟩ : syracuseStep 1559657 = 1169743) B1169743
theorem B1036967 : Blo 1036608 1036967 := bstep (se 1 (by rfl) ⟨777725, by rfl⟩ : syracuseStep 1036967 = 1555451) B1555451
theorem B8868527 : Blo 1036608 8868527 := bstep (se 1 (by rfl) ⟨6651395, by rfl⟩ : syracuseStep 8868527 = 13302791) B13302791
theorem B1036991 : Blo 1036608 1036991 := bstep (se 1 (by rfl) ⟨777743, by rfl⟩ : syracuseStep 1036991 = 1555487) B1555487
theorem B1168231 : Blo 1036608 1168231 := bstep (se 1 (by rfl) ⟨876173, by rfl⟩ : syracuseStep 1168231 = 1752347) B1752347
theorem B50582393 : Blo 1036608 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B1037339 : Blo 1036608 1037339 := bstep (se 1 (by rfl) ⟨778004, by rfl⟩ : syracuseStep 1037339 = 1556009) B1556009
theorem B1037471 : Blo 1036608 1037471 := bstep (se 1 (by rfl) ⟨778103, by rfl⟩ : syracuseStep 1037471 = 1556207) B1556207
theorem B1037851 : Blo 1036608 1037851 := bstep (se 1 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 1037851 = 1556777) B1556777
theorem B1038055 : Blo 1036608 1038055 := bstep (se 1 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 1038055 = 1557083) B1557083
theorem B1038303 : Blo 1036608 1038303 := bstep (se 1 (by rfl) ⟨778727, by rfl⟩ : syracuseStep 1038303 = 1557455) B1557455
theorem B1038335 : Blo 1036608 1038335 := bstep (se 1 (by rfl) ⟨778751, by rfl⟩ : syracuseStep 1038335 = 1557503) B1557503
theorem B1169455 : Blo 1036608 1169455 := bstep (se 1 (by rfl) ⟨877091, by rfl⟩ : syracuseStep 1169455 = 1754183) B1754183
theorem B7887293 : Blo 1036608 7887293 := bstep (se 3 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 7887293 = 2957735) B2957735
theorem B1169887 : Blo 1036608 1169887 := bstep (se 1 (by rfl) ⟨877415, by rfl⟩ : syracuseStep 1169887 = 1754831) B1754831
theorem B2218951 : Blo 1036608 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1039391 : Blo 1036608 1039391 := bstep (se 1 (by rfl) ⟨779543, by rfl⟩ : syracuseStep 1039391 = 1559087) B1559087
theorem B1039871 : Blo 1036608 1039871 := bstep (se 1 (by rfl) ⟨779903, by rfl⟩ : syracuseStep 1039871 = 1559807) B1559807
theorem B1040155 : Blo 1036608 1040155 := bstep (se 1 (by rfl) ⟨780116, by rfl⟩ : syracuseStep 1040155 = 1560233) B1560233
theorem B1040475 : Blo 1036608 1040475 := bstep (se 1 (by rfl) ⟨780356, by rfl⟩ : syracuseStep 1040475 = 1560713) B1560713
theorem B32858455 : Blo 1036608 32858455 := bstep (se 1 (by rfl) ⟨24643841, by rfl⟩ : syracuseStep 32858455 = 49287683) B49287683
theorem B153576071 : Blo 1036608 153576071 := bstep (se 1 (by rfl) ⟨115182053, by rfl⟩ : syracuseStep 153576071 = 230364107) B230364107
theorem B25979255 : Blo 1036608 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B7892153 : Blo 1036608 7892153 := bstep (se 2 (by rfl) ⟨2959557, by rfl⟩ : syracuseStep 7892153 = 5919115) B5919115
theorem B3501359 : Blo 1036608 3501359 := bstep (se 1 (by rfl) ⟨2626019, by rfl⟩ : syracuseStep 3501359 = 5252039) B5252039
theorem B7499429 : Blo 1036608 7499429 := bstep (se 4 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 7499429 = 1406143) B1406143
theorem B17723447 : Blo 1036608 17723447 := bstep (se 1 (by rfl) ⟨13292585, by rfl⟩ : syracuseStep 17723447 = 26585171) B26585171
theorem B3502493 : Blo 1036608 3502493 := bstep (se 3 (by rfl) ⟨656717, by rfl⟩ : syracuseStep 3502493 = 1313435) B1313435
theorem B12613249 : Blo 1036608 12613249 := bstep (se 2 (by rfl) ⟨4729968, by rfl⟩ : syracuseStep 12613249 = 9459937) B9459937
theorem B3374399 : Blo 1036608 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B43811273 : Blo 1036608 43811273 := bstep (se 2 (by rfl) ⟨16429227, by rfl⟩ : syracuseStep 43811273 = 32858455) B32858455
theorem B3507083 : Blo 1036608 3507083 := bstep (se 1 (by rfl) ⟨2630312, by rfl⟩ : syracuseStep 3507083 = 5260625) B5260625
theorem B2491631 : Blo 1036608 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B7472699 : Blo 1036608 7472699 := bstep (se 1 (by rfl) ⟨5604524, by rfl⟩ : syracuseStep 7472699 = 11209049) B11209049
theorem B3507839 : Blo 1036608 3507839 := bstep (se 1 (by rfl) ⟨2630879, by rfl⟩ : syracuseStep 3507839 = 5261759) B5261759
theorem B8882297 : Blo 1036608 8882297 := bstep (se 2 (by rfl) ⟨3330861, by rfl⟩ : syracuseStep 8882297 = 6661723) B6661723
theorem B33721595 : Blo 1036608 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B2625007 : Blo 1036608 2625007 := bstep (se 1 (by rfl) ⟨1968755, by rfl⟩ : syracuseStep 2625007 = 3937511) B3937511
theorem B2625311 : Blo 1036608 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B3936539 : Blo 1036608 3936539 := bstep (se 1 (by rfl) ⟨2952404, by rfl⟩ : syracuseStep 3936539 = 5904809) B5904809
theorem B11213639 : Blo 1036608 11213639 := bstep (se 1 (by rfl) ⟨8410229, by rfl⟩ : syracuseStep 11213639 = 16820459) B16820459
theorem B16817665 : Blo 1036608 16817665 := bstep (se 2 (by rfl) ⟨6306624, by rfl⟩ : syracuseStep 16817665 = 12613249) B12613249
theorem B2334239 : Blo 1036608 2334239 := bstep (se 1 (by rfl) ⟨1750679, by rfl⟩ : syracuseStep 2334239 = 3501359) B3501359
theorem B2334473 : Blo 1036608 2334473 := bstep (se 2 (by rfl) ⟨875427, by rfl⟩ : syracuseStep 2334473 = 1750855) B1750855
theorem B2334995 : Blo 1036608 2334995 := bstep (se 1 (by rfl) ⟨1751246, by rfl⟩ : syracuseStep 2334995 = 3502493) B3502493
theorem B2498887 : Blo 1036608 2498887 := bstep (se 1 (by rfl) ⟨1874165, by rfl⟩ : syracuseStep 2498887 = 3748331) B3748331
theorem B2499119 : Blo 1036608 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B2958601 : Blo 1036608 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B5252687 : Blo 1036608 5252687 := bstep (se 1 (by rfl) ⟨3939515, by rfl⟩ : syracuseStep 5252687 = 7879031) B7879031
theorem B3943039 : Blo 1036608 3943039 := bstep (se 1 (by rfl) ⟨2957279, by rfl⟩ : syracuseStep 3943039 = 5914559) B5914559
theorem B5909183 : Blo 1036608 5909183 := bstep (se 1 (by rfl) ⟨4431887, by rfl⟩ : syracuseStep 5909183 = 8863775) B8863775
theorem B2337785 : Blo 1036608 2337785 := bstep (se 2 (by rfl) ⟨876669, by rfl⟩ : syracuseStep 2337785 = 1753339) B1753339
theorem B9973439 : Blo 1036608 9973439 := bstep (se 1 (by rfl) ⟨7480079, by rfl⟩ : syracuseStep 9973439 = 14960159) B14960159
theorem B2338793 : Blo 1036608 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B12628183 : Blo 1036608 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B63943505 : Blo 1036608 63943505 := bstep (se 2 (by rfl) ⟨23978814, by rfl⟩ : syracuseStep 63943505 = 47957629) B47957629
theorem B2340143 : Blo 1036608 2340143 := bstep (se 1 (by rfl) ⟨1755107, by rfl⟩ : syracuseStep 2340143 = 3510215) B3510215
theorem B5912351 : Blo 1036608 5912351 := bstep (se 1 (by rfl) ⟨4434263, by rfl⟩ : syracuseStep 5912351 = 8868527) B8868527
theorem B1555151 : Blo 1036608 1555151 := bstep (se 1 (by rfl) ⟨1166363, by rfl⟩ : syracuseStep 1555151 = 2332727) B2332727
theorem B5258195 : Blo 1036608 5258195 := bstep (se 1 (by rfl) ⟨3943646, by rfl⟩ : syracuseStep 5258195 = 7887293) B7887293
theorem B5913809 : Blo 1036608 5913809 := bstep (se 2 (by rfl) ⟨2217678, by rfl⟩ : syracuseStep 5913809 = 4435357) B4435357
theorem B1556507 : Blo 1036608 1556507 := bstep (se 1 (by rfl) ⟨1167380, by rfl⟩ : syracuseStep 1556507 = 2334761) B2334761
theorem B9486395 : Blo 1036608 9486395 := bstep (se 1 (by rfl) ⟨7114796, by rfl⟩ : syracuseStep 9486395 = 14229593) B14229593
theorem B1556807 : Blo 1036608 1556807 := bstep (se 1 (by rfl) ⟨1167605, by rfl⟩ : syracuseStep 1556807 = 2335211) B2335211
theorem B102384047 : Blo 1036608 102384047 := bstep (se 1 (by rfl) ⟨76788035, by rfl⟩ : syracuseStep 102384047 = 153576071) B153576071
theorem B1557641 : Blo 1036608 1557641 := bstep (se 2 (by rfl) ⟨584115, by rfl⟩ : syracuseStep 1557641 = 1168231) B1168231
theorem B11814173 : Blo 1036608 11814173 := bstep (se 3 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 11814173 = 4430315) B4430315
theorem B17319503 : Blo 1036608 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B1558343 : Blo 1036608 1558343 := bstep (se 1 (by rfl) ⟨1168757, by rfl⟩ : syracuseStep 1558343 = 2337515) B2337515
theorem B1558583 : Blo 1036608 1558583 := bstep (se 1 (by rfl) ⟨1168937, by rfl⟩ : syracuseStep 1558583 = 2337875) B2337875
theorem B1558631 : Blo 1036608 1558631 := bstep (se 1 (by rfl) ⟨1168973, by rfl⟩ : syracuseStep 1558631 = 2337947) B2337947
theorem B5261435 : Blo 1036608 5261435 := bstep (se 1 (by rfl) ⟨3946076, by rfl⟩ : syracuseStep 5261435 = 7892153) B7892153
theorem B4999619 : Blo 1036608 4999619 := bstep (se 1 (by rfl) ⟨3749714, by rfl⟩ : syracuseStep 4999619 = 7499429) B7499429
theorem B11815631 : Blo 1036608 11815631 := bstep (se 1 (by rfl) ⟨8861723, by rfl⟩ : syracuseStep 11815631 = 17723447) B17723447
theorem B1559273 : Blo 1036608 1559273 := bstep (se 2 (by rfl) ⟨584727, by rfl⟩ : syracuseStep 1559273 = 1169455) B1169455
theorem B1559327 : Blo 1036608 1559327 := bstep (se 1 (by rfl) ⟨1169495, by rfl⟩ : syracuseStep 1559327 = 2338991) B2338991
theorem B1166431 : Blo 1036608 1166431 := bstep (se 1 (by rfl) ⟨874823, by rfl⟩ : syracuseStep 1166431 = 1749647) B1749647
theorem B1559849 : Blo 1036608 1559849 := bstep (se 2 (by rfl) ⟨584943, by rfl⟩ : syracuseStep 1559849 = 1169887) B1169887
theorem B8998397 : Blo 1036608 8998397 := bstep (se 3 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 8998397 = 3374399) B3374399
theorem B1560743 : Blo 1036608 1560743 := bstep (se 1 (by rfl) ⟨1170557, by rfl⟩ : syracuseStep 1560743 = 2341115) B2341115
theorem B1560827 : Blo 1036608 1560827 := bstep (se 1 (by rfl) ⟨1170620, by rfl⟩ : syracuseStep 1560827 = 2341241) B2341241
theorem B1037087 : Blo 1036608 1037087 := bstep (se 1 (by rfl) ⟨777815, by rfl⟩ : syracuseStep 1037087 = 1555631) B1555631
theorem B1037247 : Blo 1036608 1037247 := bstep (se 1 (by rfl) ⟨777935, by rfl⟩ : syracuseStep 1037247 = 1555871) B1555871
theorem B1037423 : Blo 1036608 1037423 := bstep (se 1 (by rfl) ⟨778067, by rfl⟩ : syracuseStep 1037423 = 1556135) B1556135
theorem B1037639 : Blo 1036608 1037639 := bstep (se 1 (by rfl) ⟨778229, by rfl⟩ : syracuseStep 1037639 = 1556459) B1556459
theorem B5625283 : Blo 1036608 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B5264999 : Blo 1036608 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B5265161 : Blo 1036608 5265161 := bstep (se 2 (by rfl) ⟨1974435, by rfl⟩ : syracuseStep 5265161 = 3948871) B3948871
theorem B1038439 : Blo 1036608 1038439 := bstep (se 1 (by rfl) ⟨778829, by rfl⟩ : syracuseStep 1038439 = 1557659) B1557659
theorem B5265647 : Blo 1036608 5265647 := bstep (se 1 (by rfl) ⟨3949235, by rfl⟩ : syracuseStep 5265647 = 7898471) B7898471
theorem B1039487 : Blo 1036608 1039487 := bstep (se 1 (by rfl) ⟨779615, by rfl⟩ : syracuseStep 1039487 = 1559231) B1559231
theorem B1039519 : Blo 1036608 1039519 := bstep (se 1 (by rfl) ⟨779639, by rfl⟩ : syracuseStep 1039519 = 1559279) B1559279
theorem B1039527 : Blo 1036608 1039527 := bstep (se 1 (by rfl) ⟨779645, by rfl⟩ : syracuseStep 1039527 = 1559291) B1559291
theorem B1039771 : Blo 1036608 1039771 := bstep (se 1 (by rfl) ⟨779828, by rfl⟩ : syracuseStep 1039771 = 1559657) B1559657
theorem B36036917 : Blo 1036608 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B11824379 : Blo 1036608 11824379 := bstep (se 1 (by rfl) ⟨8868284, by rfl⟩ : syracuseStep 11824379 = 17736569) B17736569
theorem B12808475 : Blo 1036608 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B19986857 : Blo 1036608 19986857 := bstep (se 2 (by rfl) ⟨7495071, by rfl⟩ : syracuseStep 19986857 = 14990143) B14990143
theorem B6324263 : Blo 1036608 6324263 := bstep (se 1 (by rfl) ⟨4743197, by rfl⟩ : syracuseStep 6324263 = 9486395) B9486395
theorem B68256031 : Blo 1036608 68256031 := bstep (se 1 (by rfl) ⟨51192023, by rfl⟩ : syracuseStep 68256031 = 102384047) B102384047
theorem B4981799 : Blo 1036608 4981799 := bstep (se 1 (by rfl) ⟨3736349, by rfl⟩ : syracuseStep 4981799 = 7472699) B7472699
theorem B3507623 : Blo 1036608 3507623 := bstep (se 1 (by rfl) ⟨2630717, by rfl⟩ : syracuseStep 3507623 = 5261435) B5261435
theorem B22481063 : Blo 1036608 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B5998931 : Blo 1036608 5998931 := bstep (se 1 (by rfl) ⟨4499198, by rfl⟩ : syracuseStep 5998931 = 8998397) B8998397
theorem B2624359 : Blo 1036608 2624359 := bstep (se 1 (by rfl) ⟨1968269, by rfl⟩ : syracuseStep 2624359 = 3936539) B3936539
theorem B3509999 : Blo 1036608 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B3510107 : Blo 1036608 3510107 := bstep (se 1 (by rfl) ⟨2632580, by rfl⟩ : syracuseStep 3510107 = 5265161) B5265161
theorem B3510431 : Blo 1036608 3510431 := bstep (se 1 (by rfl) ⟨2632823, by rfl⟩ : syracuseStep 3510431 = 5265647) B5265647
theorem B7475759 : Blo 1036608 7475759 := bstep (se 1 (by rfl) ⟨5606819, by rfl⟩ : syracuseStep 7475759 = 11213639) B11213639
theorem B24024611 : Blo 1036608 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B3939455 : Blo 1036608 3939455 := bstep (se 1 (by rfl) ⟨2954591, by rfl⟩ : syracuseStep 3939455 = 5909183) B5909183
theorem B3941567 : Blo 1036608 3941567 := bstep (se 1 (by rfl) ⟨2956175, by rfl⟩ : syracuseStep 3941567 = 5912351) B5912351
theorem B22423553 : Blo 1036608 22423553 := bstep (se 2 (by rfl) ⟨8408832, by rfl⟩ : syracuseStep 22423553 = 16817665) B16817665
theorem B3942539 : Blo 1036608 3942539 := bstep (se 1 (by rfl) ⟨2956904, by rfl⟩ : syracuseStep 3942539 = 5913809) B5913809
theorem B29207515 : Blo 1036608 29207515 := bstep (se 1 (by rfl) ⟨21905636, by rfl⟩ : syracuseStep 29207515 = 43811273) B43811273
theorem B2338055 : Blo 1036608 2338055 := bstep (se 1 (by rfl) ⟨1753541, by rfl⟩ : syracuseStep 2338055 = 3507083) B3507083
theorem B7876115 : Blo 1036608 7876115 := bstep (se 1 (by rfl) ⟨5907086, by rfl⟩ : syracuseStep 7876115 = 11814173) B11814173
theorem B11546335 : Blo 1036608 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B2338559 : Blo 1036608 2338559 := bstep (se 1 (by rfl) ⟨1753919, by rfl⟩ : syracuseStep 2338559 = 3507839) B3507839
theorem B3944801 : Blo 1036608 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B7877087 : Blo 1036608 7877087 := bstep (se 1 (by rfl) ⟨5907815, by rfl⟩ : syracuseStep 7877087 = 11815631) B11815631
theorem B1750207 : Blo 1036608 1750207 := bstep (se 1 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 1750207 = 2625311) B2625311
theorem B5257385 : Blo 1036608 5257385 := bstep (se 2 (by rfl) ⟨1971519, by rfl⟩ : syracuseStep 5257385 = 3943039) B3943039
theorem B1555241 : Blo 1036608 1555241 := bstep (se 2 (by rfl) ⟨583215, by rfl⟩ : syracuseStep 1555241 = 1166431) B1166431
theorem B1556159 : Blo 1036608 1556159 := bstep (se 1 (by rfl) ⟨1167119, by rfl⟩ : syracuseStep 1556159 = 2334239) B2334239
theorem B1556315 : Blo 1036608 1556315 := bstep (se 1 (by rfl) ⟨1167236, by rfl⟩ : syracuseStep 1556315 = 2334473) B2334473
theorem B1556663 : Blo 1036608 1556663 := bstep (se 1 (by rfl) ⟨1167497, by rfl⟩ : syracuseStep 1556663 = 2334995) B2334995
theorem B1558523 : Blo 1036608 1558523 := bstep (se 1 (by rfl) ⟨1168892, by rfl⟩ : syracuseStep 1558523 = 2337785) B2337785
theorem B7882919 : Blo 1036608 7882919 := bstep (se 1 (by rfl) ⟨5912189, by rfl⟩ : syracuseStep 7882919 = 11824379) B11824379
theorem B1559195 : Blo 1036608 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B8538983 : Blo 1036608 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B1560095 : Blo 1036608 1560095 := bstep (se 1 (by rfl) ⟨1170071, by rfl⟩ : syracuseStep 1560095 = 2340143) B2340143
theorem B13324571 : Blo 1036608 13324571 := bstep (se 1 (by rfl) ⟨9993428, by rfl⟩ : syracuseStep 13324571 = 19986857) B19986857
theorem B1036767 : Blo 1036608 1036767 := bstep (se 1 (by rfl) ⟨777575, by rfl⟩ : syracuseStep 1036767 = 1555151) B1555151
theorem B1037671 : Blo 1036608 1037671 := bstep (se 1 (by rfl) ⟨778253, by rfl⟩ : syracuseStep 1037671 = 1556507) B1556507
theorem B1037871 : Blo 1036608 1037871 := bstep (se 1 (by rfl) ⟨778403, by rfl⟩ : syracuseStep 1037871 = 1556807) B1556807
theorem B3331849 : Blo 1036608 3331849 := bstep (se 2 (by rfl) ⟨1249443, by rfl⟩ : syracuseStep 3331849 = 2498887) B2498887
theorem B1038427 : Blo 1036608 1038427 := bstep (se 1 (by rfl) ⟨778820, by rfl⟩ : syracuseStep 1038427 = 1557641) B1557641
theorem B1661087 : Blo 1036608 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B1038895 : Blo 1036608 1038895 := bstep (se 1 (by rfl) ⟨779171, by rfl⟩ : syracuseStep 1038895 = 1558343) B1558343
theorem B1039055 : Blo 1036608 1039055 := bstep (se 1 (by rfl) ⟨779291, by rfl⟩ : syracuseStep 1039055 = 1558583) B1558583
theorem B1039087 : Blo 1036608 1039087 := bstep (se 1 (by rfl) ⟨779315, by rfl⟩ : syracuseStep 1039087 = 1558631) B1558631
theorem B5921531 : Blo 1036608 5921531 := bstep (se 1 (by rfl) ⟨4441148, by rfl⟩ : syracuseStep 5921531 = 8882297) B8882297
theorem B3333079 : Blo 1036608 3333079 := bstep (se 1 (by rfl) ⟨2499809, by rfl⟩ : syracuseStep 3333079 = 4999619) B4999619
theorem B1039515 : Blo 1036608 1039515 := bstep (se 1 (by rfl) ⟨779636, by rfl⟩ : syracuseStep 1039515 = 1559273) B1559273
theorem B1039551 : Blo 1036608 1039551 := bstep (se 1 (by rfl) ⟨779663, by rfl⟩ : syracuseStep 1039551 = 1559327) B1559327
theorem B1039899 : Blo 1036608 1039899 := bstep (se 1 (by rfl) ⟨779924, by rfl⟩ : syracuseStep 1039899 = 1559849) B1559849
theorem B1040495 : Blo 1036608 1040495 := bstep (se 1 (by rfl) ⟨780371, by rfl⟩ : syracuseStep 1040495 = 1560743) B1560743
theorem B1040551 : Blo 1036608 1040551 := bstep (se 1 (by rfl) ⟨780413, by rfl⟩ : syracuseStep 1040551 = 1560827) B1560827
theorem B3500009 : Blo 1036608 3500009 := bstep (se 2 (by rfl) ⟨1312503, by rfl⟩ : syracuseStep 3500009 = 2625007) B2625007
theorem B16837577 : Blo 1036608 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B1666079 : Blo 1036608 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B3501791 : Blo 1036608 3501791 := bstep (se 1 (by rfl) ⟨2626343, by rfl⟩ : syracuseStep 3501791 = 5252687) B5252687
theorem B7500377 : Blo 1036608 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B6648959 : Blo 1036608 6648959 := bstep (se 1 (by rfl) ⟨4986719, by rfl⟩ : syracuseStep 6648959 = 9973439) B9973439
theorem B42629003 : Blo 1036608 42629003 := bstep (se 1 (by rfl) ⟨31971752, by rfl⟩ : syracuseStep 42629003 = 63943505) B63943505
theorem B3505463 : Blo 1036608 3505463 := bstep (se 1 (by rfl) ⟨2629097, by rfl⟩ : syracuseStep 3505463 = 5258195) B5258195
theorem B3999287 : Blo 1036608 3999287 := bstep (se 1 (by rfl) ⟨2999465, by rfl⟩ : syracuseStep 3999287 = 5998931) B5998931
theorem B8883047 : Blo 1036608 8883047 := bstep (se 1 (by rfl) ⟨6662285, by rfl⟩ : syracuseStep 8883047 = 13324571) B13324571
theorem B4983839 : Blo 1036608 4983839 := bstep (se 1 (by rfl) ⟨3737879, by rfl⟩ : syracuseStep 4983839 = 7475759) B7475759
theorem B64065629 : Blo 1036608 64065629 := bstep (se 3 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 64065629 = 24024611) B24024611
theorem B2626303 : Blo 1036608 2626303 := bstep (se 1 (by rfl) ⟨1969727, by rfl⟩ : syracuseStep 2626303 = 3939455) B3939455
theorem B4429565 : Blo 1036608 4429565 := bstep (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) B1661087
theorem B2627711 : Blo 1036608 2627711 := bstep (se 1 (by rfl) ⟨1970783, by rfl⟩ : syracuseStep 2627711 = 3941567) B3941567
theorem B2333339 : Blo 1036608 2333339 := bstep (se 1 (by rfl) ⟨1750004, by rfl⟩ : syracuseStep 2333339 = 3500009) B3500009
theorem B14949035 : Blo 1036608 14949035 := bstep (se 1 (by rfl) ⟨11211776, by rfl⟩ : syracuseStep 14949035 = 22423553) B22423553
theorem B2628359 : Blo 1036608 2628359 := bstep (se 1 (by rfl) ⟨1971269, by rfl⟩ : syracuseStep 2628359 = 3942539) B3942539
theorem B2333609 : Blo 1036608 2333609 := bstep (se 2 (by rfl) ⟨875103, by rfl⟩ : syracuseStep 2333609 = 1750207) B1750207
theorem B5250743 : Blo 1036608 5250743 := bstep (se 1 (by rfl) ⟨3938057, by rfl⟩ : syracuseStep 5250743 = 7876115) B7876115
theorem B2334527 : Blo 1036608 2334527 := bstep (se 1 (by rfl) ⟨1750895, by rfl⟩ : syracuseStep 2334527 = 3501791) B3501791
theorem B2629867 : Blo 1036608 2629867 := bstep (se 1 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 2629867 = 3944801) B3944801
theorem B5251391 : Blo 1036608 5251391 := bstep (se 1 (by rfl) ⟨3938543, by rfl⟩ : syracuseStep 5251391 = 7877087) B7877087
theorem B4432639 : Blo 1036608 4432639 := bstep (se 1 (by rfl) ⟨3324479, by rfl⟩ : syracuseStep 4432639 = 6648959) B6648959
theorem B28419335 : Blo 1036608 28419335 := bstep (se 1 (by rfl) ⟨21314501, by rfl⟩ : syracuseStep 28419335 = 42629003) B42629003
theorem B2336975 : Blo 1036608 2336975 := bstep (se 1 (by rfl) ⟨1752731, by rfl⟩ : syracuseStep 2336975 = 3505463) B3505463
theorem B91008041 : Blo 1036608 91008041 := bstep (se 2 (by rfl) ⟨34128015, by rfl⟩ : syracuseStep 91008041 = 68256031) B68256031
theorem B3321199 : Blo 1036608 3321199 := bstep (se 1 (by rfl) ⟨2490899, by rfl⟩ : syracuseStep 3321199 = 4981799) B4981799
theorem B2338415 : Blo 1036608 2338415 := bstep (se 1 (by rfl) ⟨1753811, by rfl⟩ : syracuseStep 2338415 = 3507623) B3507623
theorem B5255279 : Blo 1036608 5255279 := bstep (se 1 (by rfl) ⟨3941459, by rfl⟩ : syracuseStep 5255279 = 7882919) B7882919
theorem B14987375 : Blo 1036608 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B20001005 : Blo 1036608 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B2339999 : Blo 1036608 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B2340071 : Blo 1036608 2340071 := bstep (se 1 (by rfl) ⟨1755053, by rfl⟩ : syracuseStep 2340071 = 3510107) B3510107
theorem B2340287 : Blo 1036608 2340287 := bstep (se 1 (by rfl) ⟨1755215, by rfl⟩ : syracuseStep 2340287 = 3510431) B3510431
theorem B38943353 : Blo 1036608 38943353 := bstep (se 2 (by rfl) ⟨14603757, by rfl⟩ : syracuseStep 38943353 = 29207515) B29207515
theorem B3947687 : Blo 1036608 3947687 := bstep (se 1 (by rfl) ⟨2960765, by rfl⟩ : syracuseStep 3947687 = 5921531) B5921531
theorem B11225051 : Blo 1036608 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B1558703 : Blo 1036608 1558703 := bstep (se 1 (by rfl) ⟨1169027, by rfl⟩ : syracuseStep 1558703 = 2338055) B2338055
theorem B4442465 : Blo 1036608 4442465 := bstep (se 2 (by rfl) ⟨1665924, by rfl⟩ : syracuseStep 4442465 = 3331849) B3331849
theorem B1559039 : Blo 1036608 1559039 := bstep (se 1 (by rfl) ⟨1169279, by rfl⟩ : syracuseStep 1559039 = 2338559) B2338559
theorem B4444105 : Blo 1036608 4444105 := bstep (se 2 (by rfl) ⟨1666539, by rfl⟩ : syracuseStep 4444105 = 3333079) B3333079
theorem B1036827 : Blo 1036608 1036827 := bstep (se 1 (by rfl) ⟨777620, by rfl⟩ : syracuseStep 1036827 = 1555241) B1555241
theorem B1037439 : Blo 1036608 1037439 := bstep (se 1 (by rfl) ⟨778079, by rfl⟩ : syracuseStep 1037439 = 1556159) B1556159
theorem B1037543 : Blo 1036608 1037543 := bstep (se 1 (by rfl) ⟨778157, by rfl⟩ : syracuseStep 1037543 = 1556315) B1556315
theorem B4216175 : Blo 1036608 4216175 := bstep (se 1 (by rfl) ⟨3162131, by rfl⟩ : syracuseStep 4216175 = 6324263) B6324263
theorem B1037775 : Blo 1036608 1037775 := bstep (se 1 (by rfl) ⟨778331, by rfl⟩ : syracuseStep 1037775 = 1556663) B1556663
theorem B1039015 : Blo 1036608 1039015 := bstep (se 1 (by rfl) ⟨779261, by rfl⟩ : syracuseStep 1039015 = 1558523) B1558523
theorem B1039463 : Blo 1036608 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B5692655 : Blo 1036608 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B1040063 : Blo 1036608 1040063 := bstep (se 1 (by rfl) ⟨780047, by rfl⟩ : syracuseStep 1040063 = 1560095) B1560095
theorem B3499145 : Blo 1036608 3499145 := bstep (se 2 (by rfl) ⟨1312179, by rfl⟩ : syracuseStep 3499145 = 2624359) B2624359
theorem B15395113 : Blo 1036608 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B1110719 : Blo 1036608 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B3504923 : Blo 1036608 3504923 := bstep (se 1 (by rfl) ⟨2628692, by rfl⟩ : syracuseStep 3504923 = 5257385) B5257385
theorem B3506489 : Blo 1036608 3506489 := bstep (se 2 (by rfl) ⟨1314933, by rfl⟩ : syracuseStep 3506489 = 2629867) B2629867
theorem B2953043 : Blo 1036608 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B9966023 : Blo 1036608 9966023 := bstep (se 1 (by rfl) ⟨7474517, by rfl⟩ : syracuseStep 9966023 = 14949035) B14949035
theorem B4428265 : Blo 1036608 4428265 := bstep (se 2 (by rfl) ⟨1660599, by rfl⟩ : syracuseStep 4428265 = 3321199) B3321199
theorem B2332763 : Blo 1036608 2332763 := bstep (se 1 (by rfl) ⟨1749572, by rfl⟩ : syracuseStep 2332763 = 3499145) B3499145
theorem B18946223 : Blo 1036608 18946223 := bstep (se 1 (by rfl) ⟨14209667, by rfl⟩ : syracuseStep 18946223 = 28419335) B28419335
theorem B103848941 : Blo 1036608 103848941 := bstep (se 3 (by rfl) ⟨19471676, by rfl⟩ : syracuseStep 103848941 = 38943353) B38943353
theorem B242688109 : Blo 1036608 242688109 := bstep (se 3 (by rfl) ⟨45504020, by rfl⟩ : syracuseStep 242688109 = 91008041) B91008041
theorem B2336615 : Blo 1036608 2336615 := bstep (se 1 (by rfl) ⟨1752461, by rfl⟩ : syracuseStep 2336615 = 3504923) B3504923
theorem B2631791 : Blo 1036608 2631791 := bstep (se 1 (by rfl) ⟨1973843, by rfl⟩ : syracuseStep 2631791 = 3947687) B3947687
theorem B5910185 : Blo 1036608 5910185 := bstep (se 2 (by rfl) ⟨2216319, by rfl⟩ : syracuseStep 5910185 = 4432639) B4432639
theorem B2666191 : Blo 1036608 2666191 := bstep (se 1 (by rfl) ⟨1999643, by rfl⟩ : syracuseStep 2666191 = 3999287) B3999287
theorem B7483367 : Blo 1036608 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B2961643 : Blo 1036608 2961643 := bstep (se 1 (by rfl) ⟨2221232, by rfl⟩ : syracuseStep 2961643 = 4442465) B4442465
theorem B2961917 : Blo 1036608 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B3322559 : Blo 1036608 3322559 := bstep (se 1 (by rfl) ⟨2491919, by rfl⟩ : syracuseStep 3322559 = 4983839) B4983839
theorem B42710419 : Blo 1036608 42710419 := bstep (se 1 (by rfl) ⟨32032814, by rfl⟩ : syracuseStep 42710419 = 64065629) B64065629
theorem B20526817 : Blo 1036608 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B1751807 : Blo 1036608 1751807 := bstep (se 1 (by rfl) ⟨1313855, by rfl⟩ : syracuseStep 1751807 = 2627711) B2627711
theorem B1555559 : Blo 1036608 1555559 := bstep (se 1 (by rfl) ⟨1166669, by rfl⟩ : syracuseStep 1555559 = 2333339) B2333339
theorem B1752239 : Blo 1036608 1752239 := bstep (se 1 (by rfl) ⟨1314179, by rfl⟩ : syracuseStep 1752239 = 2628359) B2628359
theorem B1555739 : Blo 1036608 1555739 := bstep (se 1 (by rfl) ⟨1166804, by rfl⟩ : syracuseStep 1555739 = 2333609) B2333609
theorem B1556351 : Blo 1036608 1556351 := bstep (se 1 (by rfl) ⟨1167263, by rfl⟩ : syracuseStep 1556351 = 2334527) B2334527
theorem B1557983 : Blo 1036608 1557983 := bstep (se 1 (by rfl) ⟨1168487, by rfl⟩ : syracuseStep 1557983 = 2336975) B2336975
theorem B1558943 : Blo 1036608 1558943 := bstep (se 1 (by rfl) ⟨1169207, by rfl⟩ : syracuseStep 1558943 = 2338415) B2338415
theorem B1559999 : Blo 1036608 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B1560047 : Blo 1036608 1560047 := bstep (se 1 (by rfl) ⟨1170035, by rfl⟩ : syracuseStep 1560047 = 2340071) B2340071
theorem B1560191 : Blo 1036608 1560191 := bstep (se 1 (by rfl) ⟨1170143, by rfl⟩ : syracuseStep 1560191 = 2340287) B2340287
theorem B1039135 : Blo 1036608 1039135 := bstep (se 1 (by rfl) ⟨779351, by rfl⟩ : syracuseStep 1039135 = 1558703) B1558703
theorem B1039359 : Blo 1036608 1039359 := bstep (se 1 (by rfl) ⟨779519, by rfl⟩ : syracuseStep 1039359 = 1559039) B1559039
theorem B5922031 : Blo 1036608 5922031 := bstep (se 1 (by rfl) ⟨4441523, by rfl⟩ : syracuseStep 5922031 = 8883047) B8883047
theorem B2810783 : Blo 1036608 2810783 := bstep (se 1 (by rfl) ⟨2108087, by rfl⟩ : syracuseStep 2810783 = 4216175) B4216175
theorem B3795103 : Blo 1036608 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B3500495 : Blo 1036608 3500495 := bstep (se 1 (by rfl) ⟨2625371, by rfl⟩ : syracuseStep 3500495 = 5250743) B5250743
theorem B5925473 : Blo 1036608 5925473 := bstep (se 2 (by rfl) ⟨2222052, by rfl⟩ : syracuseStep 5925473 = 4444105) B4444105
theorem B3500927 : Blo 1036608 3500927 := bstep (se 1 (by rfl) ⟨2625695, by rfl⟩ : syracuseStep 3500927 = 5251391) B5251391
theorem B3501737 : Blo 1036608 3501737 := bstep (se 2 (by rfl) ⟨1313151, by rfl⟩ : syracuseStep 3501737 = 2626303) B2626303
theorem B3503519 : Blo 1036608 3503519 := bstep (se 1 (by rfl) ⟨2627639, by rfl⟩ : syracuseStep 3503519 = 5255279) B5255279
theorem B9991583 : Blo 1036608 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B13334003 : Blo 1036608 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B323584145 : Blo 1036608 323584145 := bstep (se 2 (by rfl) ⟨121344054, by rfl⟩ : syracuseStep 323584145 = 242688109) B242688109
theorem B1968695 : Blo 1036608 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B1873855 : Blo 1036608 1873855 := bstep (se 1 (by rfl) ⟨1405391, by rfl⟩ : syracuseStep 1873855 = 2810783) B2810783
theorem B5904353 : Blo 1036608 5904353 := bstep (se 2 (by rfl) ⟨2214132, by rfl⟩ : syracuseStep 5904353 = 4428265) B4428265
theorem B2333663 : Blo 1036608 2333663 := bstep (se 1 (by rfl) ⟨1750247, by rfl⟩ : syracuseStep 2333663 = 3500495) B3500495
theorem B2333951 : Blo 1036608 2333951 := bstep (se 1 (by rfl) ⟨1750463, by rfl⟩ : syracuseStep 2333951 = 3500927) B3500927
theorem B27369089 : Blo 1036608 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B2334491 : Blo 1036608 2334491 := bstep (se 1 (by rfl) ⟨1750868, by rfl⟩ : syracuseStep 2334491 = 3501737) B3501737
theorem B3940123 : Blo 1036608 3940123 := bstep (se 1 (by rfl) ⟨2955092, by rfl⟩ : syracuseStep 3940123 = 5910185) B5910185
theorem B1974611 : Blo 1036608 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B2335679 : Blo 1036608 2335679 := bstep (se 1 (by rfl) ⟨1751759, by rfl⟩ : syracuseStep 2335679 = 3503519) B3503519
theorem B6661055 : Blo 1036608 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B8889335 : Blo 1036608 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B2337659 : Blo 1036608 2337659 := bstep (se 1 (by rfl) ⟨1753244, by rfl⟩ : syracuseStep 2337659 = 3506489) B3506489
theorem B1555175 : Blo 1036608 1555175 := bstep (se 1 (by rfl) ⟨1166381, by rfl⟩ : syracuseStep 1555175 = 2332763) B2332763
theorem B12630815 : Blo 1036608 12630815 := bstep (se 1 (by rfl) ⟨9473111, by rfl⟩ : syracuseStep 12630815 = 18946223) B18946223
theorem B3554921 : Blo 1036608 3554921 := bstep (se 2 (by rfl) ⟨1333095, by rfl⟩ : syracuseStep 3554921 = 2666191) B2666191
theorem B3948857 : Blo 1036608 3948857 := bstep (se 2 (by rfl) ⟨1480821, by rfl⟩ : syracuseStep 3948857 = 2961643) B2961643
theorem B1557743 : Blo 1036608 1557743 := bstep (se 1 (by rfl) ⟨1168307, by rfl⟩ : syracuseStep 1557743 = 2336615) B2336615
theorem B1754527 : Blo 1036608 1754527 := bstep (se 1 (by rfl) ⟨1315895, by rfl⟩ : syracuseStep 1754527 = 2631791) B2631791
theorem B3950315 : Blo 1036608 3950315 := bstep (se 1 (by rfl) ⟨2962736, by rfl⟩ : syracuseStep 3950315 = 5925473) B5925473
theorem B2215039 : Blo 1036608 2215039 := bstep (se 1 (by rfl) ⟨1661279, by rfl⟩ : syracuseStep 2215039 = 3322559) B3322559
theorem B1167871 : Blo 1036608 1167871 := bstep (se 1 (by rfl) ⟨875903, by rfl⟩ : syracuseStep 1167871 = 1751807) B1751807
theorem B1037039 : Blo 1036608 1037039 := bstep (se 1 (by rfl) ⟨777779, by rfl⟩ : syracuseStep 1037039 = 1555559) B1555559
theorem B1168159 : Blo 1036608 1168159 := bstep (se 1 (by rfl) ⟨876119, by rfl⟩ : syracuseStep 1168159 = 1752239) B1752239
theorem B1037159 : Blo 1036608 1037159 := bstep (se 1 (by rfl) ⟨777869, by rfl⟩ : syracuseStep 1037159 = 1555739) B1555739
theorem B1037567 : Blo 1036608 1037567 := bstep (se 1 (by rfl) ⟨778175, by rfl⟩ : syracuseStep 1037567 = 1556351) B1556351
theorem B20240549 : Blo 1036608 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B1038655 : Blo 1036608 1038655 := bstep (se 1 (by rfl) ⟨778991, by rfl⟩ : syracuseStep 1038655 = 1557983) B1557983
theorem B1039295 : Blo 1036608 1039295 := bstep (se 1 (by rfl) ⟨779471, by rfl⟩ : syracuseStep 1039295 = 1558943) B1558943
theorem B1039999 : Blo 1036608 1039999 := bstep (se 1 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 1039999 = 1559999) B1559999
theorem B1040031 : Blo 1036608 1040031 := bstep (se 1 (by rfl) ⟨780023, by rfl⟩ : syracuseStep 1040031 = 1560047) B1560047
theorem B1040127 : Blo 1036608 1040127 := bstep (se 1 (by rfl) ⟨780095, by rfl⟩ : syracuseStep 1040127 = 1560191) B1560191
theorem B6644015 : Blo 1036608 6644015 := bstep (se 1 (by rfl) ⟨4983011, by rfl⟩ : syracuseStep 6644015 = 9966023) B9966023
theorem B69232627 : Blo 1036608 69232627 := bstep (se 1 (by rfl) ⟨51924470, by rfl⟩ : syracuseStep 69232627 = 103848941) B103848941
theorem B56947225 : Blo 1036608 56947225 := bstep (se 2 (by rfl) ⟨21355209, by rfl⟩ : syracuseStep 56947225 = 42710419) B42710419
theorem B7896041 : Blo 1036608 7896041 := bstep (se 2 (by rfl) ⟨2961015, by rfl⟩ : syracuseStep 7896041 = 5922031) B5922031
theorem B19955645 : Blo 1036608 19955645 := bstep (se 3 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 19955645 = 7483367) B7483367
theorem B1312463 : Blo 1036608 1312463 := bstep (se 1 (by rfl) ⟨984347, by rfl⟩ : syracuseStep 1312463 = 1968695) B1968695
theorem B17762813 : Blo 1036608 17762813 := bstep (se 3 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 17762813 = 6661055) B6661055
theorem B3936235 : Blo 1036608 3936235 := bstep (se 1 (by rfl) ⟨2952176, by rfl⟩ : syracuseStep 3936235 = 5904353) B5904353
theorem B2953385 : Blo 1036608 2953385 := bstep (se 2 (by rfl) ⟨1107519, by rfl⟩ : syracuseStep 2953385 = 2215039) B2215039
theorem B4429343 : Blo 1036608 4429343 := bstep (se 1 (by rfl) ⟨3322007, by rfl⟩ : syracuseStep 4429343 = 6644015) B6644015
theorem B1316407 : Blo 1036608 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B75929633 : Blo 1036608 75929633 := bstep (se 2 (by rfl) ⟨28473612, by rfl⟩ : syracuseStep 75929633 = 56947225) B56947225
theorem B2498473 : Blo 1036608 2498473 := bstep (se 2 (by rfl) ⟨936927, by rfl⟩ : syracuseStep 2498473 = 1873855) B1873855
theorem B5253497 : Blo 1036608 5253497 := bstep (se 2 (by rfl) ⟨1970061, by rfl⟩ : syracuseStep 5253497 = 3940123) B3940123
theorem B2369947 : Blo 1036608 2369947 := bstep (se 1 (by rfl) ⟨1777460, by rfl⟩ : syracuseStep 2369947 = 3554921) B3554921
theorem B369240677 : Blo 1036608 369240677 := bstep (se 4 (by rfl) ⟨34616313, by rfl⟩ : syracuseStep 369240677 = 69232627) B69232627
theorem B215722763 : Blo 1036608 215722763 := bstep (se 1 (by rfl) ⟨161792072, by rfl⟩ : syracuseStep 215722763 = 323584145) B323584145
theorem B2632571 : Blo 1036608 2632571 := bstep (se 1 (by rfl) ⟨1974428, by rfl⟩ : syracuseStep 2632571 = 3948857) B3948857
theorem B2633543 : Blo 1036608 2633543 := bstep (se 1 (by rfl) ⟨1975157, by rfl⟩ : syracuseStep 2633543 = 3950315) B3950315
theorem B2339369 : Blo 1036608 2339369 := bstep (se 2 (by rfl) ⟨877263, by rfl⟩ : syracuseStep 2339369 = 1754527) B1754527
theorem B1555775 : Blo 1036608 1555775 := bstep (se 1 (by rfl) ⟨1166831, by rfl⟩ : syracuseStep 1555775 = 2333663) B2333663
theorem B1555967 : Blo 1036608 1555967 := bstep (se 1 (by rfl) ⟨1166975, by rfl⟩ : syracuseStep 1555967 = 2333951) B2333951
theorem B1556327 : Blo 1036608 1556327 := bstep (se 1 (by rfl) ⟨1167245, by rfl⟩ : syracuseStep 1556327 = 2334491) B2334491
theorem B1557119 : Blo 1036608 1557119 := bstep (se 1 (by rfl) ⟨1167839, by rfl⟩ : syracuseStep 1557119 = 2335679) B2335679
theorem B1557161 : Blo 1036608 1557161 := bstep (se 2 (by rfl) ⟨583935, by rfl⟩ : syracuseStep 1557161 = 1167871) B1167871
theorem B1557545 : Blo 1036608 1557545 := bstep (se 2 (by rfl) ⟨584079, by rfl⟩ : syracuseStep 1557545 = 1168159) B1168159
theorem B1558439 : Blo 1036608 1558439 := bstep (se 1 (by rfl) ⟨1168829, by rfl⟩ : syracuseStep 1558439 = 2337659) B2337659
theorem B1036783 : Blo 1036608 1036783 := bstep (se 1 (by rfl) ⟨777587, by rfl⟩ : syracuseStep 1036783 = 1555175) B1555175
theorem B5264027 : Blo 1036608 5264027 := bstep (se 1 (by rfl) ⟨3948020, by rfl⟩ : syracuseStep 5264027 = 7896041) B7896041
theorem B1038495 : Blo 1036608 1038495 := bstep (se 1 (by rfl) ⟨778871, by rfl⟩ : syracuseStep 1038495 = 1557743) B1557743
theorem B13493699 : Blo 1036608 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B18246059 : Blo 1036608 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B5926223 : Blo 1036608 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B8420543 : Blo 1036608 8420543 := bstep (se 1 (by rfl) ⟨6315407, by rfl⟩ : syracuseStep 8420543 = 12630815) B12630815
theorem B13303763 : Blo 1036608 13303763 := bstep (se 1 (by rfl) ⟨9977822, by rfl⟩ : syracuseStep 13303763 = 19955645) B19955645
theorem B1968923 : Blo 1036608 1968923 := bstep (se 1 (by rfl) ⟨1476692, by rfl⟩ : syracuseStep 1968923 = 2953385) B2953385
theorem B3509351 : Blo 1036608 3509351 := bstep (se 1 (by rfl) ⟨2632013, by rfl⟩ : syracuseStep 3509351 = 5264027) B5264027
theorem B2952895 : Blo 1036608 2952895 := bstep (se 1 (by rfl) ⟨2214671, by rfl⟩ : syracuseStep 2952895 = 4429343) B4429343
theorem B5248313 : Blo 1036608 5248313 := bstep (se 2 (by rfl) ⟨1968117, by rfl⟩ : syracuseStep 5248313 = 3936235) B3936235
theorem B12164039 : Blo 1036608 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B246160451 : Blo 1036608 246160451 := bstep (se 1 (by rfl) ⟨184620338, by rfl⟩ : syracuseStep 246160451 = 369240677) B369240677
theorem B5613695 : Blo 1036608 5613695 := bstep (se 1 (by rfl) ⟨4210271, by rfl⟩ : syracuseStep 5613695 = 8420543) B8420543
theorem B11841875 : Blo 1036608 11841875 := bstep (se 1 (by rfl) ⟨8881406, by rfl⟩ : syracuseStep 11841875 = 17762813) B17762813
theorem B3159929 : Blo 1036608 3159929 := bstep (se 2 (by rfl) ⟨1184973, by rfl⟩ : syracuseStep 3159929 = 2369947) B2369947
theorem B8995799 : Blo 1036608 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B1755047 : Blo 1036608 1755047 := bstep (se 1 (by rfl) ⟨1316285, by rfl⟩ : syracuseStep 1755047 = 2632571) B2632571
theorem B1755209 : Blo 1036608 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B3950815 : Blo 1036608 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B1755695 : Blo 1036608 1755695 := bstep (se 1 (by rfl) ⟨1316771, by rfl⟩ : syracuseStep 1755695 = 2633543) B2633543
theorem B1559579 : Blo 1036608 1559579 := bstep (se 1 (by rfl) ⟨1169684, by rfl⟩ : syracuseStep 1559579 = 2339369) B2339369
theorem B1037183 : Blo 1036608 1037183 := bstep (se 1 (by rfl) ⟨777887, by rfl⟩ : syracuseStep 1037183 = 1555775) B1555775
theorem B1037311 : Blo 1036608 1037311 := bstep (se 1 (by rfl) ⟨777983, by rfl⟩ : syracuseStep 1037311 = 1555967) B1555967
theorem B3331297 : Blo 1036608 3331297 := bstep (se 2 (by rfl) ⟨1249236, by rfl⟩ : syracuseStep 3331297 = 2498473) B2498473
theorem B1037551 : Blo 1036608 1037551 := bstep (se 1 (by rfl) ⟨778163, by rfl⟩ : syracuseStep 1037551 = 1556327) B1556327
theorem B8869175 : Blo 1036608 8869175 := bstep (se 1 (by rfl) ⟨6651881, by rfl⟩ : syracuseStep 8869175 = 13303763) B13303763
theorem B1038079 : Blo 1036608 1038079 := bstep (se 1 (by rfl) ⟨778559, by rfl⟩ : syracuseStep 1038079 = 1557119) B1557119
theorem B1038107 : Blo 1036608 1038107 := bstep (se 1 (by rfl) ⟨778580, by rfl⟩ : syracuseStep 1038107 = 1557161) B1557161
theorem B1038363 : Blo 1036608 1038363 := bstep (se 1 (by rfl) ⟨778772, by rfl⟩ : syracuseStep 1038363 = 1557545) B1557545
theorem B1038959 : Blo 1036608 1038959 := bstep (se 1 (by rfl) ⟨779219, by rfl⟩ : syracuseStep 1038959 = 1558439) B1558439
theorem B50619755 : Blo 1036608 50619755 := bstep (se 1 (by rfl) ⟨37964816, by rfl⟩ : syracuseStep 50619755 = 75929633) B75929633
theorem B3499901 : Blo 1036608 3499901 := bstep (se 3 (by rfl) ⟨656231, by rfl⟩ : syracuseStep 3499901 = 1312463) B1312463
theorem B3502331 : Blo 1036608 3502331 := bstep (se 1 (by rfl) ⟨2626748, by rfl⟩ : syracuseStep 3502331 = 5253497) B5253497
theorem B143815175 : Blo 1036608 143815175 := bstep (se 1 (by rfl) ⟨107861381, by rfl⟩ : syracuseStep 143815175 = 215722763) B215722763
theorem B5997199 : Blo 1036608 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B1312615 : Blo 1036608 1312615 := bstep (se 1 (by rfl) ⟨984461, by rfl⟩ : syracuseStep 1312615 = 1968923) B1968923
theorem B164106967 : Blo 1036608 164106967 := bstep (se 1 (by rfl) ⟨123080225, by rfl⟩ : syracuseStep 164106967 = 246160451) B246160451
theorem B3937193 : Blo 1036608 3937193 := bstep (se 2 (by rfl) ⟨1476447, by rfl⟩ : syracuseStep 3937193 = 2952895) B2952895
theorem B8426477 : Blo 1036608 8426477 := bstep (se 3 (by rfl) ⟨1579964, by rfl⟩ : syracuseStep 8426477 = 3159929) B3159929
theorem B2333267 : Blo 1036608 2333267 := bstep (se 1 (by rfl) ⟨1749950, by rfl⟩ : syracuseStep 2333267 = 3499901) B3499901
theorem B3742463 : Blo 1036608 3742463 := bstep (se 1 (by rfl) ⟨2806847, by rfl⟩ : syracuseStep 3742463 = 5613695) B5613695
theorem B2334887 : Blo 1036608 2334887 := bstep (se 1 (by rfl) ⟨1751165, by rfl⟩ : syracuseStep 2334887 = 3502331) B3502331
theorem B2339567 : Blo 1036608 2339567 := bstep (se 1 (by rfl) ⟨1754675, by rfl⟩ : syracuseStep 2339567 = 3509351) B3509351
theorem B5912783 : Blo 1036608 5912783 := bstep (se 1 (by rfl) ⟨4434587, by rfl⟩ : syracuseStep 5912783 = 8869175) B8869175
theorem B134986013 : Blo 1036608 134986013 := bstep (se 3 (by rfl) ⟨25309877, by rfl⟩ : syracuseStep 134986013 = 50619755) B50619755
theorem B8109359 : Blo 1036608 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B4441729 : Blo 1036608 4441729 := bstep (se 2 (by rfl) ⟨1665648, by rfl⟩ : syracuseStep 4441729 = 3331297) B3331297
theorem B1170031 : Blo 1036608 1170031 := bstep (se 1 (by rfl) ⟨877523, by rfl⟩ : syracuseStep 1170031 = 1755047) B1755047
theorem B1170139 : Blo 1036608 1170139 := bstep (se 1 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 1170139 = 1755209) B1755209
theorem B1170463 : Blo 1036608 1170463 := bstep (se 1 (by rfl) ⟨877847, by rfl⟩ : syracuseStep 1170463 = 1755695) B1755695
theorem B1039719 : Blo 1036608 1039719 := bstep (se 1 (by rfl) ⟨779789, by rfl⟩ : syracuseStep 1039719 = 1559579) B1559579
theorem B5267753 : Blo 1036608 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B3498875 : Blo 1036608 3498875 := bstep (se 1 (by rfl) ⟨2624156, by rfl⟩ : syracuseStep 3498875 = 5248313) B5248313
theorem B7894583 : Blo 1036608 7894583 := bstep (se 1 (by rfl) ⟨5920937, by rfl⟩ : syracuseStep 7894583 = 11841875) B11841875
theorem B95876783 : Blo 1036608 95876783 := bstep (se 1 (by rfl) ⟨71907587, by rfl⟩ : syracuseStep 95876783 = 143815175) B143815175
theorem B7996265 : Blo 1036608 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B2624795 : Blo 1036608 2624795 := bstep (se 1 (by rfl) ⟨1968596, by rfl⟩ : syracuseStep 2624795 = 3937193) B3937193
theorem B2494975 : Blo 1036608 2494975 := bstep (se 1 (by rfl) ⟨1871231, by rfl⟩ : syracuseStep 2494975 = 3742463) B3742463
theorem B3511835 : Blo 1036608 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B2332583 : Blo 1036608 2332583 := bstep (se 1 (by rfl) ⟨1749437, by rfl⟩ : syracuseStep 2332583 = 3498875) B3498875
theorem B3941855 : Blo 1036608 3941855 := bstep (se 1 (by rfl) ⟨2956391, by rfl⟩ : syracuseStep 3941855 = 5912783) B5912783
theorem B89990675 : Blo 1036608 89990675 := bstep (se 1 (by rfl) ⟨67493006, by rfl⟩ : syracuseStep 89990675 = 134986013) B134986013
theorem B1750153 : Blo 1036608 1750153 := bstep (se 2 (by rfl) ⟨656307, by rfl⟩ : syracuseStep 1750153 = 1312615) B1312615
theorem B1555511 : Blo 1036608 1555511 := bstep (se 1 (by rfl) ⟨1166633, by rfl⟩ : syracuseStep 1555511 = 2333267) B2333267
theorem B1556591 : Blo 1036608 1556591 := bstep (se 1 (by rfl) ⟨1167443, by rfl⟩ : syracuseStep 1556591 = 2334887) B2334887
theorem B218809289 : Blo 1036608 218809289 := bstep (se 2 (by rfl) ⟨82053483, by rfl⟩ : syracuseStep 218809289 = 164106967) B164106967
theorem B1559711 : Blo 1036608 1559711 := bstep (se 1 (by rfl) ⟨1169783, by rfl⟩ : syracuseStep 1559711 = 2339567) B2339567
theorem B1560041 : Blo 1036608 1560041 := bstep (se 2 (by rfl) ⟨585015, by rfl⟩ : syracuseStep 1560041 = 1170031) B1170031
theorem B1560185 : Blo 1036608 1560185 := bstep (se 2 (by rfl) ⟨585069, by rfl⟩ : syracuseStep 1560185 = 1170139) B1170139
theorem B5263055 : Blo 1036608 5263055 := bstep (se 1 (by rfl) ⟨3947291, by rfl⟩ : syracuseStep 5263055 = 7894583) B7894583
theorem B63917855 : Blo 1036608 63917855 := bstep (se 1 (by rfl) ⟨47938391, by rfl⟩ : syracuseStep 63917855 = 95876783) B95876783
theorem B1560617 : Blo 1036608 1560617 := bstep (se 2 (by rfl) ⟨585231, by rfl⟩ : syracuseStep 1560617 = 1170463) B1170463
theorem B5922305 : Blo 1036608 5922305 := bstep (se 2 (by rfl) ⟨2220864, by rfl⟩ : syracuseStep 5922305 = 4441729) B4441729
theorem B22470605 : Blo 1036608 22470605 := bstep (se 3 (by rfl) ⟨4213238, by rfl⟩ : syracuseStep 22470605 = 8426477) B8426477
theorem B5406239 : Blo 1036608 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B3508703 : Blo 1036608 3508703 := bstep (se 1 (by rfl) ⟨2631527, by rfl⟩ : syracuseStep 3508703 = 5263055) B5263055
theorem B14980403 : Blo 1036608 14980403 := bstep (se 1 (by rfl) ⟨11235302, by rfl⟩ : syracuseStep 14980403 = 22470605) B22470605
theorem B2627903 : Blo 1036608 2627903 := bstep (se 1 (by rfl) ⟨1970927, by rfl⟩ : syracuseStep 2627903 = 3941855) B3941855
theorem B2333537 : Blo 1036608 2333537 := bstep (se 2 (by rfl) ⟨875076, by rfl⟩ : syracuseStep 2333537 = 1750153) B1750153
theorem B1749863 : Blo 1036608 1749863 := bstep (se 1 (by rfl) ⟨1312397, by rfl⟩ : syracuseStep 1749863 = 2624795) B2624795
theorem B42611903 : Blo 1036608 42611903 := bstep (se 1 (by rfl) ⟨31958927, by rfl⟩ : syracuseStep 42611903 = 63917855) B63917855
theorem B2341223 : Blo 1036608 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B1555055 : Blo 1036608 1555055 := bstep (se 1 (by rfl) ⟨1166291, by rfl⟩ : syracuseStep 1555055 = 2332583) B2332583
theorem B3948203 : Blo 1036608 3948203 := bstep (se 1 (by rfl) ⟨2961152, by rfl⟩ : syracuseStep 3948203 = 5922305) B5922305
theorem B3326633 : Blo 1036608 3326633 := bstep (se 2 (by rfl) ⟨1247487, by rfl⟩ : syracuseStep 3326633 = 2494975) B2494975
theorem B1037007 : Blo 1036608 1037007 := bstep (se 1 (by rfl) ⟨777755, by rfl⟩ : syracuseStep 1037007 = 1555511) B1555511
theorem B1037727 : Blo 1036608 1037727 := bstep (se 1 (by rfl) ⟨778295, by rfl⟩ : syracuseStep 1037727 = 1556591) B1556591
theorem B5330843 : Blo 1036608 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B145872859 : Blo 1036608 145872859 := bstep (se 1 (by rfl) ⟨109404644, by rfl⟩ : syracuseStep 145872859 = 218809289) B218809289
theorem B1039807 : Blo 1036608 1039807 := bstep (se 1 (by rfl) ⟨779855, by rfl⟩ : syracuseStep 1039807 = 1559711) B1559711
theorem B1040027 : Blo 1036608 1040027 := bstep (se 1 (by rfl) ⟨780020, by rfl⟩ : syracuseStep 1040027 = 1560041) B1560041
theorem B1040123 : Blo 1036608 1040123 := bstep (se 1 (by rfl) ⟨780092, by rfl⟩ : syracuseStep 1040123 = 1560185) B1560185
theorem B1040411 : Blo 1036608 1040411 := bstep (se 1 (by rfl) ⟨780308, by rfl⟩ : syracuseStep 1040411 = 1560617) B1560617
theorem B59993783 : Blo 1036608 59993783 := bstep (se 1 (by rfl) ⟨44995337, by rfl⟩ : syracuseStep 59993783 = 89990675) B89990675
theorem B3604159 : Blo 1036608 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B2632135 : Blo 1036608 2632135 := bstep (se 1 (by rfl) ⟨1974101, by rfl⟩ : syracuseStep 2632135 = 3948203) B3948203
theorem B2339135 : Blo 1036608 2339135 := bstep (se 1 (by rfl) ⟨1754351, by rfl⟩ : syracuseStep 2339135 = 3508703) B3508703
theorem B3553895 : Blo 1036608 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B1751935 : Blo 1036608 1751935 := bstep (se 1 (by rfl) ⟨1313951, by rfl⟩ : syracuseStep 1751935 = 2627903) B2627903
theorem B1555691 : Blo 1036608 1555691 := bstep (se 1 (by rfl) ⟨1166768, by rfl⟩ : syracuseStep 1555691 = 2333537) B2333537
theorem B39995855 : Blo 1036608 39995855 := bstep (se 1 (by rfl) ⟨29996891, by rfl⟩ : syracuseStep 39995855 = 59993783) B59993783
theorem B194497145 : Blo 1036608 194497145 := bstep (se 2 (by rfl) ⟨72936429, by rfl⟩ : syracuseStep 194497145 = 145872859) B145872859
theorem B1166575 : Blo 1036608 1166575 := bstep (se 1 (by rfl) ⟨874931, by rfl⟩ : syracuseStep 1166575 = 1749863) B1749863
theorem B19222181 : Blo 1036608 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B1560815 : Blo 1036608 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B1036703 : Blo 1036608 1036703 := bstep (se 1 (by rfl) ⟨777527, by rfl⟩ : syracuseStep 1036703 = 1555055) B1555055
theorem B2217755 : Blo 1036608 2217755 := bstep (se 1 (by rfl) ⟨1663316, by rfl⟩ : syracuseStep 2217755 = 3326633) B3326633
theorem B9986935 : Blo 1036608 9986935 := bstep (se 1 (by rfl) ⟨7490201, by rfl⟩ : syracuseStep 9986935 = 14980403) B14980403
theorem B28407935 : Blo 1036608 28407935 := bstep (se 1 (by rfl) ⟨21305951, by rfl⟩ : syracuseStep 28407935 = 42611903) B42611903
theorem B129664763 : Blo 1036608 129664763 := bstep (se 1 (by rfl) ⟨97248572, by rfl⟩ : syracuseStep 129664763 = 194497145) B194497145
theorem B12814787 : Blo 1036608 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B3509513 : Blo 1036608 3509513 := bstep (se 2 (by rfl) ⟨1316067, by rfl⟩ : syracuseStep 3509513 = 2632135) B2632135
theorem B1478503 : Blo 1036608 1478503 := bstep (se 1 (by rfl) ⟨1108877, by rfl⟩ : syracuseStep 1478503 = 2217755) B2217755
theorem B2335913 : Blo 1036608 2335913 := bstep (se 2 (by rfl) ⟨875967, by rfl⟩ : syracuseStep 2335913 = 1751935) B1751935
theorem B2369263 : Blo 1036608 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B13315913 : Blo 1036608 13315913 := bstep (se 2 (by rfl) ⟨4993467, by rfl⟩ : syracuseStep 13315913 = 9986935) B9986935
theorem B1555433 : Blo 1036608 1555433 := bstep (se 2 (by rfl) ⟨583287, by rfl⟩ : syracuseStep 1555433 = 1166575) B1166575
theorem B1559423 : Blo 1036608 1559423 := bstep (se 1 (by rfl) ⟨1169567, by rfl⟩ : syracuseStep 1559423 = 2339135) B2339135
theorem B1037127 : Blo 1036608 1037127 := bstep (se 1 (by rfl) ⟨777845, by rfl⟩ : syracuseStep 1037127 = 1555691) B1555691
theorem B26663903 : Blo 1036608 26663903 := bstep (se 1 (by rfl) ⟨19997927, by rfl⟩ : syracuseStep 26663903 = 39995855) B39995855
theorem B1040543 : Blo 1036608 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B18938623 : Blo 1036608 18938623 := bstep (se 1 (by rfl) ⟨14203967, by rfl⟩ : syracuseStep 18938623 = 28407935) B28407935
theorem B86443175 : Blo 1036608 86443175 := bstep (se 1 (by rfl) ⟨64832381, by rfl⟩ : syracuseStep 86443175 = 129664763) B129664763
theorem B2339675 : Blo 1036608 2339675 := bstep (se 1 (by rfl) ⟨1754756, by rfl⟩ : syracuseStep 2339675 = 3509513) B3509513
theorem B3159017 : Blo 1036608 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B17775935 : Blo 1036608 17775935 := bstep (se 1 (by rfl) ⟨13331951, by rfl⟩ : syracuseStep 17775935 = 26663903) B26663903
theorem B1557275 : Blo 1036608 1557275 := bstep (se 1 (by rfl) ⟨1167956, by rfl⟩ : syracuseStep 1557275 = 2335913) B2335913
theorem B25251497 : Blo 1036608 25251497 := bstep (se 2 (by rfl) ⟨9469311, by rfl⟩ : syracuseStep 25251497 = 18938623) B18938623
theorem B7885349 : Blo 1036608 7885349 := bstep (se 4 (by rfl) ⟨739251, by rfl⟩ : syracuseStep 7885349 = 1478503) B1478503
theorem B1036955 : Blo 1036608 1036955 := bstep (se 1 (by rfl) ⟨777716, by rfl⟩ : syracuseStep 1036955 = 1555433) B1555433
theorem B1039615 : Blo 1036608 1039615 := bstep (se 1 (by rfl) ⟨779711, by rfl⟩ : syracuseStep 1039615 = 1559423) B1559423
theorem B34172765 : Blo 1036608 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B8877275 : Blo 1036608 8877275 := bstep (se 1 (by rfl) ⟨6657956, by rfl⟩ : syracuseStep 8877275 = 13315913) B13315913
theorem B22781843 : Blo 1036608 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B2106011 : Blo 1036608 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B5256899 : Blo 1036608 5256899 := bstep (se 1 (by rfl) ⟨3942674, by rfl⟩ : syracuseStep 5256899 = 7885349) B7885349
theorem B1559783 : Blo 1036608 1559783 := bstep (se 1 (by rfl) ⟨1169837, by rfl⟩ : syracuseStep 1559783 = 2339675) B2339675
theorem B5918183 : Blo 1036608 5918183 := bstep (se 1 (by rfl) ⟨4438637, by rfl⟩ : syracuseStep 5918183 = 8877275) B8877275
theorem B11850623 : Blo 1036608 11850623 := bstep (se 1 (by rfl) ⟨8887967, by rfl⟩ : syracuseStep 11850623 = 17775935) B17775935
theorem B1038183 : Blo 1036608 1038183 := bstep (se 1 (by rfl) ⟨778637, by rfl⟩ : syracuseStep 1038183 = 1557275) B1557275
theorem B57628783 : Blo 1036608 57628783 := bstep (se 1 (by rfl) ⟨43221587, by rfl⟩ : syracuseStep 57628783 = 86443175) B86443175
theorem B16834331 : Blo 1036608 16834331 := bstep (se 1 (by rfl) ⟨12625748, by rfl⟩ : syracuseStep 16834331 = 25251497) B25251497
theorem B7900415 : Blo 1036608 7900415 := bstep (se 1 (by rfl) ⟨5925311, by rfl⟩ : syracuseStep 7900415 = 11850623) B11850623
theorem B5616029 : Blo 1036608 5616029 := bstep (se 3 (by rfl) ⟨1053005, by rfl⟩ : syracuseStep 5616029 = 2106011) B2106011
theorem B3945455 : Blo 1036608 3945455 := bstep (se 1 (by rfl) ⟨2959091, by rfl⟩ : syracuseStep 3945455 = 5918183) B5918183
theorem B11222887 : Blo 1036608 11222887 := bstep (se 1 (by rfl) ⟨8417165, by rfl⟩ : syracuseStep 11222887 = 16834331) B16834331
theorem B15187895 : Blo 1036608 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B1039855 : Blo 1036608 1039855 := bstep (se 1 (by rfl) ⟨779891, by rfl⟩ : syracuseStep 1039855 = 1559783) B1559783
theorem B76838377 : Blo 1036608 76838377 := bstep (se 2 (by rfl) ⟨28814391, by rfl⟩ : syracuseStep 76838377 = 57628783) B57628783
theorem B3504599 : Blo 1036608 3504599 := bstep (se 1 (by rfl) ⟨2628449, by rfl⟩ : syracuseStep 3504599 = 5256899) B5256899
theorem B3744019 : Blo 1036608 3744019 := bstep (se 1 (by rfl) ⟨2808014, by rfl⟩ : syracuseStep 3744019 = 5616029) B5616029
theorem B2630303 : Blo 1036608 2630303 := bstep (se 1 (by rfl) ⟨1972727, by rfl⟩ : syracuseStep 2630303 = 3945455) B3945455
theorem B2336399 : Blo 1036608 2336399 := bstep (se 1 (by rfl) ⟨1752299, by rfl⟩ : syracuseStep 2336399 = 3504599) B3504599
theorem B102451169 : Blo 1036608 102451169 := bstep (se 2 (by rfl) ⟨38419188, by rfl⟩ : syracuseStep 102451169 = 76838377) B76838377
theorem B14963849 : Blo 1036608 14963849 := bstep (se 2 (by rfl) ⟨5611443, by rfl⟩ : syracuseStep 14963849 = 11222887) B11222887
theorem B5266943 : Blo 1036608 5266943 := bstep (se 1 (by rfl) ⟨3950207, by rfl⟩ : syracuseStep 5266943 = 7900415) B7900415
theorem B10125263 : Blo 1036608 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B3511295 : Blo 1036608 3511295 := bstep (se 1 (by rfl) ⟨2633471, by rfl⟩ : syracuseStep 3511295 = 5266943) B5266943
theorem B4992025 : Blo 1036608 4992025 := bstep (se 2 (by rfl) ⟨1872009, by rfl⟩ : syracuseStep 4992025 = 3744019) B3744019
theorem B9975899 : Blo 1036608 9975899 := bstep (se 1 (by rfl) ⟨7481924, by rfl⟩ : syracuseStep 9975899 = 14963849) B14963849
theorem B273203117 : Blo 1036608 273203117 := bstep (se 3 (by rfl) ⟨51225584, by rfl⟩ : syracuseStep 273203117 = 102451169) B102451169
theorem B1753535 : Blo 1036608 1753535 := bstep (se 1 (by rfl) ⟨1315151, by rfl⟩ : syracuseStep 1753535 = 2630303) B2630303
theorem B1557599 : Blo 1036608 1557599 := bstep (se 1 (by rfl) ⟨1168199, by rfl⟩ : syracuseStep 1557599 = 2336399) B2336399
theorem B27000701 : Blo 1036608 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B6656033 : Blo 1036608 6656033 := bstep (se 2 (by rfl) ⟨2496012, by rfl⟩ : syracuseStep 6656033 = 4992025) B4992025
theorem B18000467 : Blo 1036608 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B182135411 : Blo 1036608 182135411 := bstep (se 1 (by rfl) ⟨136601558, by rfl⟩ : syracuseStep 182135411 = 273203117) B273203117
theorem B2340863 : Blo 1036608 2340863 := bstep (se 1 (by rfl) ⟨1755647, by rfl⟩ : syracuseStep 2340863 = 3511295) B3511295
theorem B1169023 : Blo 1036608 1169023 := bstep (se 1 (by rfl) ⟨876767, by rfl⟩ : syracuseStep 1169023 = 1753535) B1753535
theorem B1038399 : Blo 1036608 1038399 := bstep (se 1 (by rfl) ⟨778799, by rfl⟩ : syracuseStep 1038399 = 1557599) B1557599
theorem B6650599 : Blo 1036608 6650599 := bstep (se 1 (by rfl) ⟨4987949, by rfl⟩ : syracuseStep 6650599 = 9975899) B9975899
theorem B12000311 : Blo 1036608 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B4437355 : Blo 1036608 4437355 := bstep (se 1 (by rfl) ⟨3328016, by rfl⟩ : syracuseStep 4437355 = 6656033) B6656033
theorem B121423607 : Blo 1036608 121423607 := bstep (se 1 (by rfl) ⟨91067705, by rfl⟩ : syracuseStep 121423607 = 182135411) B182135411
theorem B1558697 : Blo 1036608 1558697 := bstep (se 2 (by rfl) ⟨584511, by rfl⟩ : syracuseStep 1558697 = 1169023) B1169023
theorem B8867465 : Blo 1036608 8867465 := bstep (se 2 (by rfl) ⟨3325299, by rfl⟩ : syracuseStep 8867465 = 6650599) B6650599
theorem B1560575 : Blo 1036608 1560575 := bstep (se 1 (by rfl) ⟨1170431, by rfl⟩ : syracuseStep 1560575 = 2340863) B2340863
theorem B8000207 : Blo 1036608 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B80949071 : Blo 1036608 80949071 := bstep (se 1 (by rfl) ⟨60711803, by rfl⟩ : syracuseStep 80949071 = 121423607) B121423607
theorem B5911643 : Blo 1036608 5911643 := bstep (se 1 (by rfl) ⟨4433732, by rfl⟩ : syracuseStep 5911643 = 8867465) B8867465
theorem B5916473 : Blo 1036608 5916473 := bstep (se 2 (by rfl) ⟨2218677, by rfl⟩ : syracuseStep 5916473 = 4437355) B4437355
theorem B1039131 : Blo 1036608 1039131 := bstep (se 1 (by rfl) ⟨779348, by rfl⟩ : syracuseStep 1039131 = 1558697) B1558697
theorem B1040383 : Blo 1036608 1040383 := bstep (se 1 (by rfl) ⟨780287, by rfl⟩ : syracuseStep 1040383 = 1560575) B1560575
theorem B3941095 : Blo 1036608 3941095 := bstep (se 1 (by rfl) ⟨2955821, by rfl⟩ : syracuseStep 3941095 = 5911643) B5911643
theorem B3944315 : Blo 1036608 3944315 := bstep (se 1 (by rfl) ⟨2958236, by rfl⟩ : syracuseStep 3944315 = 5916473) B5916473
theorem B5333471 : Blo 1036608 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B53966047 : Blo 1036608 53966047 := bstep (se 1 (by rfl) ⟨40474535, by rfl⟩ : syracuseStep 53966047 = 80949071) B80949071
theorem B2629543 : Blo 1036608 2629543 := bstep (se 1 (by rfl) ⟨1972157, by rfl⟩ : syracuseStep 2629543 = 3944315) B3944315
theorem B5254793 : Blo 1036608 5254793 := bstep (se 2 (by rfl) ⟨1970547, by rfl⟩ : syracuseStep 5254793 = 3941095) B3941095
theorem B3555647 : Blo 1036608 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B71954729 : Blo 1036608 71954729 := bstep (se 2 (by rfl) ⟨26983023, by rfl⟩ : syracuseStep 71954729 = 53966047) B53966047
theorem B2370431 : Blo 1036608 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B3503195 : Blo 1036608 3503195 := bstep (se 1 (by rfl) ⟨2627396, by rfl⟩ : syracuseStep 3503195 = 5254793) B5254793
theorem B47969819 : Blo 1036608 47969819 := bstep (se 1 (by rfl) ⟨35977364, by rfl⟩ : syracuseStep 47969819 = 71954729) B71954729
theorem B3506057 : Blo 1036608 3506057 := bstep (se 2 (by rfl) ⟨1314771, by rfl⟩ : syracuseStep 3506057 = 2629543) B2629543
theorem B2335463 : Blo 1036608 2335463 := bstep (se 1 (by rfl) ⟨1751597, by rfl⟩ : syracuseStep 2335463 = 3503195) B3503195
theorem B2337371 : Blo 1036608 2337371 := bstep (se 1 (by rfl) ⟨1753028, by rfl⟩ : syracuseStep 2337371 = 3506057) B3506057
theorem B6321149 : Blo 1036608 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B31979879 : Blo 1036608 31979879 := bstep (se 1 (by rfl) ⟨23984909, by rfl⟩ : syracuseStep 31979879 = 47969819) B47969819
theorem B1556975 : Blo 1036608 1556975 := bstep (se 1 (by rfl) ⟨1167731, by rfl⟩ : syracuseStep 1556975 = 2335463) B2335463
theorem B1558247 : Blo 1036608 1558247 := bstep (se 1 (by rfl) ⟨1168685, by rfl⟩ : syracuseStep 1558247 = 2337371) B2337371
theorem B4214099 : Blo 1036608 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B21319919 : Blo 1036608 21319919 := bstep (se 1 (by rfl) ⟨15989939, by rfl⟩ : syracuseStep 21319919 = 31979879) B31979879
theorem B1037983 : Blo 1036608 1037983 := bstep (se 1 (by rfl) ⟨778487, by rfl⟩ : syracuseStep 1037983 = 1556975) B1556975
theorem B1038831 : Blo 1036608 1038831 := bstep (se 1 (by rfl) ⟨779123, by rfl⟩ : syracuseStep 1038831 = 1558247) B1558247
theorem B2809399 : Blo 1036608 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B14213279 : Blo 1036608 14213279 := bstep (se 1 (by rfl) ⟨10659959, by rfl⟩ : syracuseStep 14213279 = 21319919) B21319919
theorem B3745865 : Blo 1036608 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B37902077 : Blo 1036608 37902077 := bstep (se 3 (by rfl) ⟨7106639, by rfl⟩ : syracuseStep 37902077 = 14213279) B14213279
theorem B25268051 : Blo 1036608 25268051 := bstep (se 1 (by rfl) ⟨18951038, by rfl⟩ : syracuseStep 25268051 = 37902077) B37902077
theorem B2497243 : Blo 1036608 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B16845367 : Blo 1036608 16845367 := bstep (se 1 (by rfl) ⟨12634025, by rfl⟩ : syracuseStep 16845367 = 25268051) B25268051
theorem B3329657 : Blo 1036608 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B22460489 : Blo 1036608 22460489 := bstep (se 2 (by rfl) ⟨8422683, by rfl⟩ : syracuseStep 22460489 = 16845367) B16845367
theorem B2219771 : Blo 1036608 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B5919389 : Blo 1036608 5919389 := bstep (se 3 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 5919389 = 2219771) B2219771
theorem B14973659 : Blo 1036608 14973659 := bstep (se 1 (by rfl) ⟨11230244, by rfl⟩ : syracuseStep 14973659 = 22460489) B22460489
theorem B3946259 : Blo 1036608 3946259 := bstep (se 1 (by rfl) ⟨2959694, by rfl⟩ : syracuseStep 3946259 = 5919389) B5919389
theorem B9982439 : Blo 1036608 9982439 := bstep (se 1 (by rfl) ⟨7486829, by rfl⟩ : syracuseStep 9982439 = 14973659) B14973659
theorem B6654959 : Blo 1036608 6654959 := bstep (se 1 (by rfl) ⟨4991219, by rfl⟩ : syracuseStep 6654959 = 9982439) B9982439
theorem B2630839 : Blo 1036608 2630839 := bstep (se 1 (by rfl) ⟨1973129, by rfl⟩ : syracuseStep 2630839 = 3946259) B3946259
theorem B3507785 : Blo 1036608 3507785 := bstep (se 2 (by rfl) ⟨1315419, by rfl⟩ : syracuseStep 3507785 = 2630839) B2630839
theorem B4436639 : Blo 1036608 4436639 := bstep (se 1 (by rfl) ⟨3327479, by rfl⟩ : syracuseStep 4436639 = 6654959) B6654959
theorem B2957759 : Blo 1036608 2957759 := bstep (se 1 (by rfl) ⟨2218319, by rfl⟩ : syracuseStep 2957759 = 4436639) B4436639
theorem B2338523 : Blo 1036608 2338523 := bstep (se 1 (by rfl) ⟨1753892, by rfl⟩ : syracuseStep 2338523 = 3507785) B3507785
theorem B1971839 : Blo 1036608 1971839 := bstep (se 1 (by rfl) ⟨1478879, by rfl⟩ : syracuseStep 1971839 = 2957759) B2957759
theorem B1559015 : Blo 1036608 1559015 := bstep (se 1 (by rfl) ⟨1169261, by rfl⟩ : syracuseStep 1559015 = 2338523) B2338523
theorem B1314559 : Blo 1036608 1314559 := bstep (se 1 (by rfl) ⟨985919, by rfl⟩ : syracuseStep 1314559 = 1971839) B1971839
theorem B1039343 : Blo 1036608 1039343 := bstep (se 1 (by rfl) ⟨779507, by rfl⟩ : syracuseStep 1039343 = 1559015) B1559015
theorem B1752745 : Blo 1036608 1752745 := bstep (se 2 (by rfl) ⟨657279, by rfl⟩ : syracuseStep 1752745 = 1314559) B1314559
theorem B2336993 : Blo 1036608 2336993 := bstep (se 2 (by rfl) ⟨876372, by rfl⟩ : syracuseStep 2336993 = 1752745) B1752745
theorem B1557995 : Blo 1036608 1557995 := bstep (se 1 (by rfl) ⟨1168496, by rfl⟩ : syracuseStep 1557995 = 2336993) B2336993
theorem B1038663 : Blo 1036608 1038663 := bstep (se 1 (by rfl) ⟨778997, by rfl⟩ : syracuseStep 1038663 = 1557995) B1557995

theorem C0 (j : ℕ) (h1 : 259152 ≤ j) (h2 : j ≤ 259851) : Blo 1036608 (4 * j + 3) := by
  interval_cases j
  · exact B1036611
  · exact B1036615
  · exact B1036619
  · exact B1036623
  · exact B1036627
  · exact B1036631
  · exact B1036635
  · exact B1036639
  · exact B1036643
  · exact B1036647
  · exact B1036651
  · exact B1036655
  · exact B1036659
  · exact B1036663
  · exact B1036667
  · exact B1036671
  · exact B1036675
  · exact B1036679
  · exact B1036683
  · exact B1036687
  · exact B1036691
  · exact B1036695
  · exact B1036699
  · exact B1036703
  · exact B1036707
  · exact B1036711
  · exact B1036715
  · exact B1036719
  · exact B1036723
  · exact B1036727
  · exact B1036731
  · exact B1036735
  · exact B1036739
  · exact B1036743
  · exact B1036747
  · exact B1036751
  · exact B1036755
  · exact B1036759
  · exact B1036763
  · exact B1036767
  · exact B1036771
  · exact B1036775
  · exact B1036779
  · exact B1036783
  · exact B1036787
  · exact B1036791
  · exact B1036795
  · exact B1036799
  · exact B1036803
  · exact B1036807
  · exact B1036811
  · exact B1036815
  · exact B1036819
  · exact B1036823
  · exact B1036827
  · exact B1036831
  · exact B1036835
  · exact B1036839
  · exact B1036843
  · exact B1036847
  · exact B1036851
  · exact B1036855
  · exact B1036859
  · exact B1036863
  · exact B1036867
  · exact B1036871
  · exact B1036875
  · exact B1036879
  · exact B1036883
  · exact B1036887
  · exact B1036891
  · exact B1036895
  · exact B1036899
  · exact B1036903
  · exact B1036907
  · exact B1036911
  · exact B1036915
  · exact B1036919
  · exact B1036923
  · exact B1036927
  · exact B1036931
  · exact B1036935
  · exact B1036939
  · exact B1036943
  · exact B1036947
  · exact B1036951
  · exact B1036955
  · exact B1036959
  · exact B1036963
  · exact B1036967
  · exact B1036971
  · exact B1036975
  · exact B1036979
  · exact B1036983
  · exact B1036987
  · exact B1036991
  · exact B1036995
  · exact B1036999
  · exact B1037003
  · exact B1037007
  · exact B1037011
  · exact B1037015
  · exact B1037019
  · exact B1037023
  · exact B1037027
  · exact B1037031
  · exact B1037035
  · exact B1037039
  · exact B1037043
  · exact B1037047
  · exact B1037051
  · exact B1037055
  · exact B1037059
  · exact B1037063
  · exact B1037067
  · exact B1037071
  · exact B1037075
  · exact B1037079
  · exact B1037083
  · exact B1037087
  · exact B1037091
  · exact B1037095
  · exact B1037099
  · exact B1037103
  · exact B1037107
  · exact B1037111
  · exact B1037115
  · exact B1037119
  · exact B1037123
  · exact B1037127
  · exact B1037131
  · exact B1037135
  · exact B1037139
  · exact B1037143
  · exact B1037147
  · exact B1037151
  · exact B1037155
  · exact B1037159
  · exact B1037163
  · exact B1037167
  · exact B1037171
  · exact B1037175
  · exact B1037179
  · exact B1037183
  · exact B1037187
  · exact B1037191
  · exact B1037195
  · exact B1037199
  · exact B1037203
  · exact B1037207
  · exact B1037211
  · exact B1037215
  · exact B1037219
  · exact B1037223
  · exact B1037227
  · exact B1037231
  · exact B1037235
  · exact B1037239
  · exact B1037243
  · exact B1037247
  · exact B1037251
  · exact B1037255
  · exact B1037259
  · exact B1037263
  · exact B1037267
  · exact B1037271
  · exact B1037275
  · exact B1037279
  · exact B1037283
  · exact B1037287
  · exact B1037291
  · exact B1037295
  · exact B1037299
  · exact B1037303
  · exact B1037307
  · exact B1037311
  · exact B1037315
  · exact B1037319
  · exact B1037323
  · exact B1037327
  · exact B1037331
  · exact B1037335
  · exact B1037339
  · exact B1037343
  · exact B1037347
  · exact B1037351
  · exact B1037355
  · exact B1037359
  · exact B1037363
  · exact B1037367
  · exact B1037371
  · exact B1037375
  · exact B1037379
  · exact B1037383
  · exact B1037387
  · exact B1037391
  · exact B1037395
  · exact B1037399
  · exact B1037403
  · exact B1037407
  · exact B1037411
  · exact B1037415
  · exact B1037419
  · exact B1037423
  · exact B1037427
  · exact B1037431
  · exact B1037435
  · exact B1037439
  · exact B1037443
  · exact B1037447
  · exact B1037451
  · exact B1037455
  · exact B1037459
  · exact B1037463
  · exact B1037467
  · exact B1037471
  · exact B1037475
  · exact B1037479
  · exact B1037483
  · exact B1037487
  · exact B1037491
  · exact B1037495
  · exact B1037499
  · exact B1037503
  · exact B1037507
  · exact B1037511
  · exact B1037515
  · exact B1037519
  · exact B1037523
  · exact B1037527
  · exact B1037531
  · exact B1037535
  · exact B1037539
  · exact B1037543
  · exact B1037547
  · exact B1037551
  · exact B1037555
  · exact B1037559
  · exact B1037563
  · exact B1037567
  · exact B1037571
  · exact B1037575
  · exact B1037579
  · exact B1037583
  · exact B1037587
  · exact B1037591
  · exact B1037595
  · exact B1037599
  · exact B1037603
  · exact B1037607
  · exact B1037611
  · exact B1037615
  · exact B1037619
  · exact B1037623
  · exact B1037627
  · exact B1037631
  · exact B1037635
  · exact B1037639
  · exact B1037643
  · exact B1037647
  · exact B1037651
  · exact B1037655
  · exact B1037659
  · exact B1037663
  · exact B1037667
  · exact B1037671
  · exact B1037675
  · exact B1037679
  · exact B1037683
  · exact B1037687
  · exact B1037691
  · exact B1037695
  · exact B1037699
  · exact B1037703
  · exact B1037707
  · exact B1037711
  · exact B1037715
  · exact B1037719
  · exact B1037723
  · exact B1037727
  · exact B1037731
  · exact B1037735
  · exact B1037739
  · exact B1037743
  · exact B1037747
  · exact B1037751
  · exact B1037755
  · exact B1037759
  · exact B1037763
  · exact B1037767
  · exact B1037771
  · exact B1037775
  · exact B1037779
  · exact B1037783
  · exact B1037787
  · exact B1037791
  · exact B1037795
  · exact B1037799
  · exact B1037803
  · exact B1037807
  · exact B1037811
  · exact B1037815
  · exact B1037819
  · exact B1037823
  · exact B1037827
  · exact B1037831
  · exact B1037835
  · exact B1037839
  · exact B1037843
  · exact B1037847
  · exact B1037851
  · exact B1037855
  · exact B1037859
  · exact B1037863
  · exact B1037867
  · exact B1037871
  · exact B1037875
  · exact B1037879
  · exact B1037883
  · exact B1037887
  · exact B1037891
  · exact B1037895
  · exact B1037899
  · exact B1037903
  · exact B1037907
  · exact B1037911
  · exact B1037915
  · exact B1037919
  · exact B1037923
  · exact B1037927
  · exact B1037931
  · exact B1037935
  · exact B1037939
  · exact B1037943
  · exact B1037947
  · exact B1037951
  · exact B1037955
  · exact B1037959
  · exact B1037963
  · exact B1037967
  · exact B1037971
  · exact B1037975
  · exact B1037979
  · exact B1037983
  · exact B1037987
  · exact B1037991
  · exact B1037995
  · exact B1037999
  · exact B1038003
  · exact B1038007
  · exact B1038011
  · exact B1038015
  · exact B1038019
  · exact B1038023
  · exact B1038027
  · exact B1038031
  · exact B1038035
  · exact B1038039
  · exact B1038043
  · exact B1038047
  · exact B1038051
  · exact B1038055
  · exact B1038059
  · exact B1038063
  · exact B1038067
  · exact B1038071
  · exact B1038075
  · exact B1038079
  · exact B1038083
  · exact B1038087
  · exact B1038091
  · exact B1038095
  · exact B1038099
  · exact B1038103
  · exact B1038107
  · exact B1038111
  · exact B1038115
  · exact B1038119
  · exact B1038123
  · exact B1038127
  · exact B1038131
  · exact B1038135
  · exact B1038139
  · exact B1038143
  · exact B1038147
  · exact B1038151
  · exact B1038155
  · exact B1038159
  · exact B1038163
  · exact B1038167
  · exact B1038171
  · exact B1038175
  · exact B1038179
  · exact B1038183
  · exact B1038187
  · exact B1038191
  · exact B1038195
  · exact B1038199
  · exact B1038203
  · exact B1038207
  · exact B1038211
  · exact B1038215
  · exact B1038219
  · exact B1038223
  · exact B1038227
  · exact B1038231
  · exact B1038235
  · exact B1038239
  · exact B1038243
  · exact B1038247
  · exact B1038251
  · exact B1038255
  · exact B1038259
  · exact B1038263
  · exact B1038267
  · exact B1038271
  · exact B1038275
  · exact B1038279
  · exact B1038283
  · exact B1038287
  · exact B1038291
  · exact B1038295
  · exact B1038299
  · exact B1038303
  · exact B1038307
  · exact B1038311
  · exact B1038315
  · exact B1038319
  · exact B1038323
  · exact B1038327
  · exact B1038331
  · exact B1038335
  · exact B1038339
  · exact B1038343
  · exact B1038347
  · exact B1038351
  · exact B1038355
  · exact B1038359
  · exact B1038363
  · exact B1038367
  · exact B1038371
  · exact B1038375
  · exact B1038379
  · exact B1038383
  · exact B1038387
  · exact B1038391
  · exact B1038395
  · exact B1038399
  · exact B1038403
  · exact B1038407
  · exact B1038411
  · exact B1038415
  · exact B1038419
  · exact B1038423
  · exact B1038427
  · exact B1038431
  · exact B1038435
  · exact B1038439
  · exact B1038443
  · exact B1038447
  · exact B1038451
  · exact B1038455
  · exact B1038459
  · exact B1038463
  · exact B1038467
  · exact B1038471
  · exact B1038475
  · exact B1038479
  · exact B1038483
  · exact B1038487
  · exact B1038491
  · exact B1038495
  · exact B1038499
  · exact B1038503
  · exact B1038507
  · exact B1038511
  · exact B1038515
  · exact B1038519
  · exact B1038523
  · exact B1038527
  · exact B1038531
  · exact B1038535
  · exact B1038539
  · exact B1038543
  · exact B1038547
  · exact B1038551
  · exact B1038555
  · exact B1038559
  · exact B1038563
  · exact B1038567
  · exact B1038571
  · exact B1038575
  · exact B1038579
  · exact B1038583
  · exact B1038587
  · exact B1038591
  · exact B1038595
  · exact B1038599
  · exact B1038603
  · exact B1038607
  · exact B1038611
  · exact B1038615
  · exact B1038619
  · exact B1038623
  · exact B1038627
  · exact B1038631
  · exact B1038635
  · exact B1038639
  · exact B1038643
  · exact B1038647
  · exact B1038651
  · exact B1038655
  · exact B1038659
  · exact B1038663
  · exact B1038667
  · exact B1038671
  · exact B1038675
  · exact B1038679
  · exact B1038683
  · exact B1038687
  · exact B1038691
  · exact B1038695
  · exact B1038699
  · exact B1038703
  · exact B1038707
  · exact B1038711
  · exact B1038715
  · exact B1038719
  · exact B1038723
  · exact B1038727
  · exact B1038731
  · exact B1038735
  · exact B1038739
  · exact B1038743
  · exact B1038747
  · exact B1038751
  · exact B1038755
  · exact B1038759
  · exact B1038763
  · exact B1038767
  · exact B1038771
  · exact B1038775
  · exact B1038779
  · exact B1038783
  · exact B1038787
  · exact B1038791
  · exact B1038795
  · exact B1038799
  · exact B1038803
  · exact B1038807
  · exact B1038811
  · exact B1038815
  · exact B1038819
  · exact B1038823
  · exact B1038827
  · exact B1038831
  · exact B1038835
  · exact B1038839
  · exact B1038843
  · exact B1038847
  · exact B1038851
  · exact B1038855
  · exact B1038859
  · exact B1038863
  · exact B1038867
  · exact B1038871
  · exact B1038875
  · exact B1038879
  · exact B1038883
  · exact B1038887
  · exact B1038891
  · exact B1038895
  · exact B1038899
  · exact B1038903
  · exact B1038907
  · exact B1038911
  · exact B1038915
  · exact B1038919
  · exact B1038923
  · exact B1038927
  · exact B1038931
  · exact B1038935
  · exact B1038939
  · exact B1038943
  · exact B1038947
  · exact B1038951
  · exact B1038955
  · exact B1038959
  · exact B1038963
  · exact B1038967
  · exact B1038971
  · exact B1038975
  · exact B1038979
  · exact B1038983
  · exact B1038987
  · exact B1038991
  · exact B1038995
  · exact B1038999
  · exact B1039003
  · exact B1039007
  · exact B1039011
  · exact B1039015
  · exact B1039019
  · exact B1039023
  · exact B1039027
  · exact B1039031
  · exact B1039035
  · exact B1039039
  · exact B1039043
  · exact B1039047
  · exact B1039051
  · exact B1039055
  · exact B1039059
  · exact B1039063
  · exact B1039067
  · exact B1039071
  · exact B1039075
  · exact B1039079
  · exact B1039083
  · exact B1039087
  · exact B1039091
  · exact B1039095
  · exact B1039099
  · exact B1039103
  · exact B1039107
  · exact B1039111
  · exact B1039115
  · exact B1039119
  · exact B1039123
  · exact B1039127
  · exact B1039131
  · exact B1039135
  · exact B1039139
  · exact B1039143
  · exact B1039147
  · exact B1039151
  · exact B1039155
  · exact B1039159
  · exact B1039163
  · exact B1039167
  · exact B1039171
  · exact B1039175
  · exact B1039179
  · exact B1039183
  · exact B1039187
  · exact B1039191
  · exact B1039195
  · exact B1039199
  · exact B1039203
  · exact B1039207
  · exact B1039211
  · exact B1039215
  · exact B1039219
  · exact B1039223
  · exact B1039227
  · exact B1039231
  · exact B1039235
  · exact B1039239
  · exact B1039243
  · exact B1039247
  · exact B1039251
  · exact B1039255
  · exact B1039259
  · exact B1039263
  · exact B1039267
  · exact B1039271
  · exact B1039275
  · exact B1039279
  · exact B1039283
  · exact B1039287
  · exact B1039291
  · exact B1039295
  · exact B1039299
  · exact B1039303
  · exact B1039307
  · exact B1039311
  · exact B1039315
  · exact B1039319
  · exact B1039323
  · exact B1039327
  · exact B1039331
  · exact B1039335
  · exact B1039339
  · exact B1039343
  · exact B1039347
  · exact B1039351
  · exact B1039355
  · exact B1039359
  · exact B1039363
  · exact B1039367
  · exact B1039371
  · exact B1039375
  · exact B1039379
  · exact B1039383
  · exact B1039387
  · exact B1039391
  · exact B1039395
  · exact B1039399
  · exact B1039403
  · exact B1039407

theorem C1 (j : ℕ) (h1 : 259852 ≤ j) (h2 : j ≤ 260151) : Blo 1036608 (4 * j + 3) := by
  interval_cases j
  · exact B1039411
  · exact B1039415
  · exact B1039419
  · exact B1039423
  · exact B1039427
  · exact B1039431
  · exact B1039435
  · exact B1039439
  · exact B1039443
  · exact B1039447
  · exact B1039451
  · exact B1039455
  · exact B1039459
  · exact B1039463
  · exact B1039467
  · exact B1039471
  · exact B1039475
  · exact B1039479
  · exact B1039483
  · exact B1039487
  · exact B1039491
  · exact B1039495
  · exact B1039499
  · exact B1039503
  · exact B1039507
  · exact B1039511
  · exact B1039515
  · exact B1039519
  · exact B1039523
  · exact B1039527
  · exact B1039531
  · exact B1039535
  · exact B1039539
  · exact B1039543
  · exact B1039547
  · exact B1039551
  · exact B1039555
  · exact B1039559
  · exact B1039563
  · exact B1039567
  · exact B1039571
  · exact B1039575
  · exact B1039579
  · exact B1039583
  · exact B1039587
  · exact B1039591
  · exact B1039595
  · exact B1039599
  · exact B1039603
  · exact B1039607
  · exact B1039611
  · exact B1039615
  · exact B1039619
  · exact B1039623
  · exact B1039627
  · exact B1039631
  · exact B1039635
  · exact B1039639
  · exact B1039643
  · exact B1039647
  · exact B1039651
  · exact B1039655
  · exact B1039659
  · exact B1039663
  · exact B1039667
  · exact B1039671
  · exact B1039675
  · exact B1039679
  · exact B1039683
  · exact B1039687
  · exact B1039691
  · exact B1039695
  · exact B1039699
  · exact B1039703
  · exact B1039707
  · exact B1039711
  · exact B1039715
  · exact B1039719
  · exact B1039723
  · exact B1039727
  · exact B1039731
  · exact B1039735
  · exact B1039739
  · exact B1039743
  · exact B1039747
  · exact B1039751
  · exact B1039755
  · exact B1039759
  · exact B1039763
  · exact B1039767
  · exact B1039771
  · exact B1039775
  · exact B1039779
  · exact B1039783
  · exact B1039787
  · exact B1039791
  · exact B1039795
  · exact B1039799
  · exact B1039803
  · exact B1039807
  · exact B1039811
  · exact B1039815
  · exact B1039819
  · exact B1039823
  · exact B1039827
  · exact B1039831
  · exact B1039835
  · exact B1039839
  · exact B1039843
  · exact B1039847
  · exact B1039851
  · exact B1039855
  · exact B1039859
  · exact B1039863
  · exact B1039867
  · exact B1039871
  · exact B1039875
  · exact B1039879
  · exact B1039883
  · exact B1039887
  · exact B1039891
  · exact B1039895
  · exact B1039899
  · exact B1039903
  · exact B1039907
  · exact B1039911
  · exact B1039915
  · exact B1039919
  · exact B1039923
  · exact B1039927
  · exact B1039931
  · exact B1039935
  · exact B1039939
  · exact B1039943
  · exact B1039947
  · exact B1039951
  · exact B1039955
  · exact B1039959
  · exact B1039963
  · exact B1039967
  · exact B1039971
  · exact B1039975
  · exact B1039979
  · exact B1039983
  · exact B1039987
  · exact B1039991
  · exact B1039995
  · exact B1039999
  · exact B1040003
  · exact B1040007
  · exact B1040011
  · exact B1040015
  · exact B1040019
  · exact B1040023
  · exact B1040027
  · exact B1040031
  · exact B1040035
  · exact B1040039
  · exact B1040043
  · exact B1040047
  · exact B1040051
  · exact B1040055
  · exact B1040059
  · exact B1040063
  · exact B1040067
  · exact B1040071
  · exact B1040075
  · exact B1040079
  · exact B1040083
  · exact B1040087
  · exact B1040091
  · exact B1040095
  · exact B1040099
  · exact B1040103
  · exact B1040107
  · exact B1040111
  · exact B1040115
  · exact B1040119
  · exact B1040123
  · exact B1040127
  · exact B1040131
  · exact B1040135
  · exact B1040139
  · exact B1040143
  · exact B1040147
  · exact B1040151
  · exact B1040155
  · exact B1040159
  · exact B1040163
  · exact B1040167
  · exact B1040171
  · exact B1040175
  · exact B1040179
  · exact B1040183
  · exact B1040187
  · exact B1040191
  · exact B1040195
  · exact B1040199
  · exact B1040203
  · exact B1040207
  · exact B1040211
  · exact B1040215
  · exact B1040219
  · exact B1040223
  · exact B1040227
  · exact B1040231
  · exact B1040235
  · exact B1040239
  · exact B1040243
  · exact B1040247
  · exact B1040251
  · exact B1040255
  · exact B1040259
  · exact B1040263
  · exact B1040267
  · exact B1040271
  · exact B1040275
  · exact B1040279
  · exact B1040283
  · exact B1040287
  · exact B1040291
  · exact B1040295
  · exact B1040299
  · exact B1040303
  · exact B1040307
  · exact B1040311
  · exact B1040315
  · exact B1040319
  · exact B1040323
  · exact B1040327
  · exact B1040331
  · exact B1040335
  · exact B1040339
  · exact B1040343
  · exact B1040347
  · exact B1040351
  · exact B1040355
  · exact B1040359
  · exact B1040363
  · exact B1040367
  · exact B1040371
  · exact B1040375
  · exact B1040379
  · exact B1040383
  · exact B1040387
  · exact B1040391
  · exact B1040395
  · exact B1040399
  · exact B1040403
  · exact B1040407
  · exact B1040411
  · exact B1040415
  · exact B1040419
  · exact B1040423
  · exact B1040427
  · exact B1040431
  · exact B1040435
  · exact B1040439
  · exact B1040443
  · exact B1040447
  · exact B1040451
  · exact B1040455
  · exact B1040459
  · exact B1040463
  · exact B1040467
  · exact B1040471
  · exact B1040475
  · exact B1040479
  · exact B1040483
  · exact B1040487
  · exact B1040491
  · exact B1040495
  · exact B1040499
  · exact B1040503
  · exact B1040507
  · exact B1040511
  · exact B1040515
  · exact B1040519
  · exact B1040523
  · exact B1040527
  · exact B1040531
  · exact B1040535
  · exact B1040539
  · exact B1040543
  · exact B1040547
  · exact B1040551
  · exact B1040555
  · exact B1040559
  · exact B1040563
  · exact B1040567
  · exact B1040571
  · exact B1040575
  · exact B1040579
  · exact B1040583
  · exact B1040587
  · exact B1040591
  · exact B1040595
  · exact B1040599
  · exact B1040603
  · exact B1040607

theorem solution (m : ℕ) (hlo : 1036608 ≤ m) (hhi : m ≤ 1040608) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 259152 ≤ j := by omega
    have hj2 : j ≤ 260151 := by omega
    have hb : Blo 1036608 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 259852 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
