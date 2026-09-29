-- Prove2me | solution 1 for syracuse_descends_range_1012602_1016602
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:17.726015+00:00
-- url     : https://prove2.me/submissions/ba4d28cf-55b6-4463-98bd-030c09da9a51

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


theorem B1081369 : Blo 1012602 1081369 := bbase (se 2 (by rfl) ⟨405513, by rfl⟩ : syracuseStep 1081369 = 811027) (by norm_num)
theorem B1441837 : Blo 1012602 1441837 := bbase (se 3 (by rfl) ⟨270344, by rfl⟩ : syracuseStep 1441837 = 540689) (by norm_num)
theorem B1114273 : Blo 1012602 1114273 := bbase (se 2 (by rfl) ⟨417852, by rfl⟩ : syracuseStep 1114273 = 835705) (by norm_num)
theorem B1441957 : Blo 1012602 1441957 := bbase (se 4 (by rfl) ⟨135183, by rfl⟩ : syracuseStep 1441957 = 270367) (by norm_num)
theorem B1081549 : Blo 1012602 1081549 := bbase (se 3 (by rfl) ⟨202790, by rfl⟩ : syracuseStep 1081549 = 405581) (by norm_num)
theorem B2162909 : Blo 1012602 2162909 := bbase (se 3 (by rfl) ⟨405545, by rfl⟩ : syracuseStep 2162909 = 811091) (by norm_num)
theorem B1736957 : Blo 1012602 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1442053 : Blo 1012602 1442053 := bbase (se 4 (by rfl) ⟨135192, by rfl⟩ : syracuseStep 1442053 = 270385) (by norm_num)
theorem B3473813 : Blo 1012602 3473813 := bbase (se 6 (by rfl) ⟨81417, by rfl⟩ : syracuseStep 3473813 = 162835) (by norm_num)
theorem B9732629 : Blo 1012602 9732629 := bbase (se 6 (by rfl) ⟨228108, by rfl⟩ : syracuseStep 9732629 = 456217) (by norm_num)
theorem B2163277 : Blo 1012602 2163277 := bbase (se 3 (by rfl) ⟨405614, by rfl⟩ : syracuseStep 2163277 = 811229) (by norm_num)
theorem B21955157 : Blo 1012602 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B1081993 : Blo 1012602 1081993 := bbase (se 2 (by rfl) ⟨405747, by rfl⟩ : syracuseStep 1081993 = 811495) (by norm_num)
theorem B1442549 : Blo 1012602 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B1082117 : Blo 1012602 1082117 := bbase (se 4 (by rfl) ⟨101448, by rfl⟩ : syracuseStep 1082117 = 202897) (by norm_num)
theorem B1540901 : Blo 1012602 1540901 := bbase (se 4 (by rfl) ⟨144459, by rfl⟩ : syracuseStep 1540901 = 288919) (by norm_num)
theorem B2884517 : Blo 1012602 2884517 := bbase (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) (by norm_num)
theorem B9765845 : Blo 1012602 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B1082369 : Blo 1012602 1082369 := bbase (se 2 (by rfl) ⟨405888, by rfl⟩ : syracuseStep 1082369 = 811777) (by norm_num)
theorem B5145605 : Blo 1012602 5145605 := bbase (se 4 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 5145605 = 964801) (by norm_num)
theorem B3081365 : Blo 1012602 3081365 := bbase (se 6 (by rfl) ⟨72219, by rfl⟩ : syracuseStep 3081365 = 144439) (by norm_num)
theorem B1443101 : Blo 1012602 1443101 := bbase (se 3 (by rfl) ⟨270581, by rfl⟩ : syracuseStep 1443101 = 541163) (by norm_num)
theorem B1082813 : Blo 1012602 1082813 := bbase (se 3 (by rfl) ⟨203027, by rfl⟩ : syracuseStep 1082813 = 406055) (by norm_num)
theorem B4326965 : Blo 1012602 4326965 := bbase (se 5 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 4326965 = 405653) (by norm_num)
theorem B1083061 : Blo 1012602 1083061 := bbase (se 5 (by rfl) ⟨50768, by rfl⟩ : syracuseStep 1083061 = 101537) (by norm_num)
theorem B7309045 : Blo 1012602 7309045 := bbase (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) (by norm_num)
theorem B4327253 : Blo 1012602 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B3901301 : Blo 1012602 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B3475349 : Blo 1012602 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1443853 : Blo 1012602 1443853 := bbase (se 3 (by rfl) ⟨270722, by rfl⟩ : syracuseStep 1443853 = 541445) (by norm_num)
theorem B2164781 : Blo 1012602 2164781 := bbase (se 3 (by rfl) ⟨405896, by rfl⟩ : syracuseStep 2164781 = 811793) (by norm_num)
theorem B2885701 : Blo 1012602 2885701 := bbase (se 4 (by rfl) ⟨270534, by rfl⟩ : syracuseStep 2885701 = 541069) (by norm_num)
theorem B7702613 : Blo 1012602 7702613 := bbase (se 8 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 7702613 = 90265) (by norm_num)
theorem B1738837 : Blo 1012602 1738837 := bbase (se 8 (by rfl) ⟨10188, by rfl⟩ : syracuseStep 1738837 = 20377) (by norm_num)
theorem B1083505 : Blo 1012602 1083505 := bbase (se 2 (by rfl) ⟨406314, by rfl⟩ : syracuseStep 1083505 = 812629) (by norm_num)
theorem B1083565 : Blo 1012602 1083565 := bbase (se 3 (by rfl) ⟨203168, by rfl⟩ : syracuseStep 1083565 = 406337) (by norm_num)
theorem B2164925 : Blo 1012602 2164925 := bbase (se 3 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 2164925 = 811847) (by norm_num)
theorem B2885861 : Blo 1012602 2885861 := bbase (se 4 (by rfl) ⟨270549, by rfl⟩ : syracuseStep 2885861 = 541099) (by norm_num)
theorem B3246389 : Blo 1012602 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B5212613 : Blo 1012602 5212613 := bbase (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) (by norm_num)
theorem B2886101 : Blo 1012602 2886101 := bbase (se 7 (by rfl) ⟨33821, by rfl⟩ : syracuseStep 2886101 = 67643) (by norm_num)
theorem B1083881 : Blo 1012602 1083881 := bbase (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) (by norm_num)
theorem B1542653 : Blo 1012602 1542653 := bbase (se 3 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 1542653 = 578495) (by norm_num)
theorem B2165285 : Blo 1012602 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B4328005 : Blo 1012602 4328005 := bbase (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) (by norm_num)
theorem B2886293 : Blo 1012602 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B1444645 : Blo 1012602 1444645 := bbase (se 4 (by rfl) ⟨135435, by rfl⟩ : syracuseStep 1444645 = 270871) (by norm_num)
theorem B3083093 : Blo 1012602 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B1084325 : Blo 1012602 1084325 := bbase (se 4 (by rfl) ⟨101655, by rfl⟩ : syracuseStep 1084325 = 203311) (by norm_num)
theorem B1084385 : Blo 1012602 1084385 := bbase (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) (by norm_num)
theorem B1084513 : Blo 1012602 1084513 := bbase (se 2 (by rfl) ⟨406692, by rfl⟩ : syracuseStep 1084513 = 813385) (by norm_num)
theorem B1444981 : Blo 1012602 1444981 := bbase (se 5 (by rfl) ⟨67733, by rfl⟩ : syracuseStep 1444981 = 135467) (by norm_num)
theorem B3247285 : Blo 1012602 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B4328741 : Blo 1012602 4328741 := bbase (se 4 (by rfl) ⟨405819, by rfl⟩ : syracuseStep 4328741 = 811639) (by norm_num)
theorem B1445197 : Blo 1012602 1445197 := bbase (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) (by norm_num)
theorem B2166173 : Blo 1012602 2166173 := bbase (se 3 (by rfl) ⟨406157, by rfl⟩ : syracuseStep 2166173 = 812315) (by norm_num)
theorem B1084957 : Blo 1012602 1084957 := bbase (se 3 (by rfl) ⟨203429, by rfl⟩ : syracuseStep 1084957 = 406859) (by norm_num)
theorem B1281577 : Blo 1012602 1281577 := bbase (se 2 (by rfl) ⟨480591, by rfl⟩ : syracuseStep 1281577 = 961183) (by norm_num)
theorem B3247685 : Blo 1012602 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B2887285 : Blo 1012602 2887285 := bbase (se 5 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 2887285 = 270683) (by norm_num)
theorem B1281673 : Blo 1012602 1281673 := bbase (se 2 (by rfl) ⟨480627, by rfl⟩ : syracuseStep 1281673 = 961255) (by norm_num)
theorem B2166421 : Blo 1012602 2166421 := bbase (se 6 (by rfl) ⟨50775, by rfl⟩ : syracuseStep 2166421 = 101551) (by norm_num)
theorem B1085077 : Blo 1012602 1085077 := bbase (se 6 (by rfl) ⟨25431, by rfl⟩ : syracuseStep 1085077 = 50863) (by norm_num)
theorem B1445573 : Blo 1012602 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B1281845 : Blo 1012602 1281845 := bbase (se 5 (by rfl) ⟨60086, by rfl⟩ : syracuseStep 1281845 = 120173) (by norm_num)
theorem B1281901 : Blo 1012602 1281901 := bbase (se 3 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 1281901 = 480713) (by norm_num)
theorem B1085329 : Blo 1012602 1085329 := bbase (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) (by norm_num)
theorem B1085333 : Blo 1012602 1085333 := bbase (se 6 (by rfl) ⟨25437, by rfl⟩ : syracuseStep 1085333 = 50875) (by norm_num)
theorem B1281997 : Blo 1012602 1281997 := bbase (se 3 (by rfl) ⟨240374, by rfl⟩ : syracuseStep 1281997 = 480749) (by norm_num)
theorem B2199653 : Blo 1012602 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B1282169 : Blo 1012602 1282169 := bbase (se 2 (by rfl) ⟨480813, by rfl⟩ : syracuseStep 1282169 = 961627) (by norm_num)
theorem B2166925 : Blo 1012602 2166925 := bbase (se 3 (by rfl) ⟨406298, by rfl⟩ : syracuseStep 2166925 = 812597) (by norm_num)
theorem B1282225 : Blo 1012602 1282225 := bbase (se 2 (by rfl) ⟨480834, by rfl⟩ : syracuseStep 1282225 = 961669) (by norm_num)
theorem B1282321 : Blo 1012602 1282321 := bbase (se 2 (by rfl) ⟨480870, by rfl⟩ : syracuseStep 1282321 = 961741) (by norm_num)
theorem B19796309 : Blo 1012602 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B6951349 : Blo 1012602 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B1282493 : Blo 1012602 1282493 := bbase (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) (by norm_num)
theorem B1282549 : Blo 1012602 1282549 := bbase (se 5 (by rfl) ⟨60119, by rfl⟩ : syracuseStep 1282549 = 120239) (by norm_num)
theorem B1282645 : Blo 1012602 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B1217117 : Blo 1012602 1217117 := bbase (se 3 (by rfl) ⟨228209, by rfl⟩ : syracuseStep 1217117 = 456419) (by norm_num)
theorem B2888389 : Blo 1012602 2888389 := bbase (se 4 (by rfl) ⟨270786, by rfl⟩ : syracuseStep 2888389 = 541573) (by norm_num)
theorem B1708789 : Blo 1012602 1708789 := bbase (se 5 (by rfl) ⟨80099, by rfl⟩ : syracuseStep 1708789 = 160199) (by norm_num)
theorem B1282817 : Blo 1012602 1282817 := bbase (se 2 (by rfl) ⟨481056, by rfl⟩ : syracuseStep 1282817 = 962113) (by norm_num)
theorem B1217305 : Blo 1012602 1217305 := bbase (se 2 (by rfl) ⟨456489, by rfl⟩ : syracuseStep 1217305 = 912979) (by norm_num)
theorem B1282873 : Blo 1012602 1282873 := bbase (se 2 (by rfl) ⟨481077, by rfl⟩ : syracuseStep 1282873 = 962155) (by norm_num)
theorem B1708877 : Blo 1012602 1708877 := bbase (se 3 (by rfl) ⟨320414, by rfl⟩ : syracuseStep 1708877 = 640829) (by norm_num)
theorem B1282969 : Blo 1012602 1282969 := bbase (se 2 (by rfl) ⟨481113, by rfl⟩ : syracuseStep 1282969 = 962227) (by norm_num)
theorem B1709005 : Blo 1012602 1709005 := bbase (se 3 (by rfl) ⟨320438, by rfl⟩ : syracuseStep 1709005 = 640877) (by norm_num)
theorem B1217521 : Blo 1012602 1217521 := bbase (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) (by norm_num)
theorem B2167813 : Blo 1012602 2167813 := bbase (se 4 (by rfl) ⟨203232, by rfl⟩ : syracuseStep 2167813 = 406465) (by norm_num)
theorem B1709093 : Blo 1012602 1709093 := bbase (se 4 (by rfl) ⟨160227, by rfl⟩ : syracuseStep 1709093 = 320455) (by norm_num)
theorem B1283141 : Blo 1012602 1283141 := bbase (se 4 (by rfl) ⟨120294, by rfl⟩ : syracuseStep 1283141 = 240589) (by norm_num)
theorem B1446997 : Blo 1012602 1446997 := bbase (se 8 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 1446997 = 16957) (by norm_num)
theorem B1283197 : Blo 1012602 1283197 := bbase (se 3 (by rfl) ⟨240599, by rfl⟩ : syracuseStep 1283197 = 481199) (by norm_num)
theorem B1709221 : Blo 1012602 1709221 := bbase (se 4 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 1709221 = 320479) (by norm_num)
theorem B1545421 : Blo 1012602 1545421 := bbase (se 3 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 1545421 = 579533) (by norm_num)
theorem B1283293 : Blo 1012602 1283293 := bbase (se 3 (by rfl) ⟨240617, by rfl⟩ : syracuseStep 1283293 = 481235) (by norm_num)
theorem B1709309 : Blo 1012602 1709309 := bbase (se 3 (by rfl) ⟨320495, by rfl⟩ : syracuseStep 1709309 = 640991) (by norm_num)
theorem B1217809 : Blo 1012602 1217809 := bbase (se 2 (by rfl) ⟨456678, by rfl⟩ : syracuseStep 1217809 = 913357) (by norm_num)
theorem B1709437 : Blo 1012602 1709437 := bbase (se 3 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 1709437 = 641039) (by norm_num)
theorem B1283465 : Blo 1012602 1283465 := bbase (se 2 (by rfl) ⟨481299, by rfl⟩ : syracuseStep 1283465 = 962599) (by norm_num)
theorem B1283521 : Blo 1012602 1283521 := bbase (se 2 (by rfl) ⟨481320, by rfl⟩ : syracuseStep 1283521 = 962641) (by norm_num)
theorem B1709525 : Blo 1012602 1709525 := bbase (se 7 (by rfl) ⟨20033, by rfl⟩ : syracuseStep 1709525 = 40067) (by norm_num)
theorem B2168309 : Blo 1012602 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B1283617 : Blo 1012602 1283617 := bbase (se 2 (by rfl) ⟨481356, by rfl⟩ : syracuseStep 1283617 = 962713) (by norm_num)
theorem B1709653 : Blo 1012602 1709653 := bbase (se 8 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 1709653 = 20035) (by norm_num)
theorem B1709741 : Blo 1012602 1709741 := bbase (se 3 (by rfl) ⟨320576, by rfl⟩ : syracuseStep 1709741 = 641153) (by norm_num)
theorem B1283789 : Blo 1012602 1283789 := bbase (se 3 (by rfl) ⟨240710, by rfl⟩ : syracuseStep 1283789 = 481421) (by norm_num)
theorem B1283845 : Blo 1012602 1283845 := bbase (se 4 (by rfl) ⟨120360, by rfl⟩ : syracuseStep 1283845 = 240721) (by norm_num)
theorem B1709869 : Blo 1012602 1709869 := bbase (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) (by norm_num)
theorem B1283941 : Blo 1012602 1283941 := bbase (se 4 (by rfl) ⟨120369, by rfl⟩ : syracuseStep 1283941 = 240739) (by norm_num)
theorem B1709957 : Blo 1012602 1709957 := bbase (se 4 (by rfl) ⟨160308, by rfl⟩ : syracuseStep 1709957 = 320617) (by norm_num)
theorem B1710085 : Blo 1012602 1710085 := bbase (se 4 (by rfl) ⟨160320, by rfl⟩ : syracuseStep 1710085 = 320641) (by norm_num)
theorem B1284113 : Blo 1012602 1284113 := bbase (se 2 (by rfl) ⟨481542, by rfl⟩ : syracuseStep 1284113 = 963085) (by norm_num)
theorem B1284169 : Blo 1012602 1284169 := bbase (se 2 (by rfl) ⟨481563, by rfl⟩ : syracuseStep 1284169 = 963127) (by norm_num)
theorem B1710173 : Blo 1012602 1710173 := bbase (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) (by norm_num)
theorem B2889893 : Blo 1012602 2889893 := bbase (se 4 (by rfl) ⟨270927, by rfl⟩ : syracuseStep 2889893 = 541855) (by norm_num)
theorem B1284265 : Blo 1012602 1284265 := bbase (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) (by norm_num)
theorem B1710301 : Blo 1012602 1710301 := bbase (se 3 (by rfl) ⟨320681, by rfl⟩ : syracuseStep 1710301 = 641363) (by norm_num)
theorem B5773589 : Blo 1012602 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B1710389 : Blo 1012602 1710389 := bbase (se 5 (by rfl) ⟨80174, by rfl⟩ : syracuseStep 1710389 = 160349) (by norm_num)
theorem B1284437 : Blo 1012602 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B2169197 : Blo 1012602 2169197 := bbase (se 3 (by rfl) ⟨406724, by rfl⟩ : syracuseStep 2169197 = 813449) (by norm_num)
theorem B1284493 : Blo 1012602 1284493 := bbase (se 3 (by rfl) ⟨240842, by rfl⟩ : syracuseStep 1284493 = 481685) (by norm_num)
theorem B1710517 : Blo 1012602 1710517 := bbase (se 5 (by rfl) ⟨80180, by rfl⟩ : syracuseStep 1710517 = 160361) (by norm_num)
theorem B2169317 : Blo 1012602 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B1284589 : Blo 1012602 1284589 := bbase (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) (by norm_num)
theorem B4332037 : Blo 1012602 4332037 := bbase (se 4 (by rfl) ⟨406128, by rfl⟩ : syracuseStep 4332037 = 812257) (by norm_num)
theorem B1710605 : Blo 1012602 1710605 := bbase (se 3 (by rfl) ⟨320738, by rfl⟩ : syracuseStep 1710605 = 641477) (by norm_num)
theorem B1219097 : Blo 1012602 1219097 := bbase (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) (by norm_num)
theorem B1710733 : Blo 1012602 1710733 := bbase (se 3 (by rfl) ⟨320762, by rfl⟩ : syracuseStep 1710733 = 641525) (by norm_num)
theorem B1284761 : Blo 1012602 1284761 := bbase (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) (by norm_num)
theorem B1317541 : Blo 1012602 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B1284817 : Blo 1012602 1284817 := bbase (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) (by norm_num)
theorem B1710821 : Blo 1012602 1710821 := bbase (se 4 (by rfl) ⟨160389, by rfl⟩ : syracuseStep 1710821 = 320779) (by norm_num)
theorem B1284913 : Blo 1012602 1284913 := bbase (se 2 (by rfl) ⟨481842, by rfl⟩ : syracuseStep 1284913 = 963685) (by norm_num)
theorem B1710949 : Blo 1012602 1710949 := bbase (se 4 (by rfl) ⟨160401, by rfl⟩ : syracuseStep 1710949 = 320803) (by norm_num)
theorem B1711037 : Blo 1012602 1711037 := bbase (se 3 (by rfl) ⟨320819, by rfl⟩ : syracuseStep 1711037 = 641639) (by norm_num)
theorem B1285085 : Blo 1012602 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B1285141 : Blo 1012602 1285141 := bbase (se 6 (by rfl) ⟨30120, by rfl⟩ : syracuseStep 1285141 = 60241) (by norm_num)
theorem B1711165 : Blo 1012602 1711165 := bbase (se 3 (by rfl) ⟨320843, by rfl⟩ : syracuseStep 1711165 = 641687) (by norm_num)
theorem B2169949 : Blo 1012602 2169949 := bbase (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) (by norm_num)
theorem B1219693 : Blo 1012602 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B1285237 : Blo 1012602 1285237 := bbase (se 5 (by rfl) ⟨60245, by rfl⟩ : syracuseStep 1285237 = 120491) (by norm_num)
theorem B1711253 : Blo 1012602 1711253 := bbase (se 6 (by rfl) ⟨40107, by rfl⟩ : syracuseStep 1711253 = 80215) (by norm_num)
theorem B1219789 : Blo 1012602 1219789 := bbase (se 3 (by rfl) ⟨228710, by rfl⟩ : syracuseStep 1219789 = 457421) (by norm_num)
theorem B2563285 : Blo 1012602 2563285 := bbase (se 7 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 2563285 = 60077) (by norm_num)
theorem B2923733 : Blo 1012602 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B8658197 : Blo 1012602 8658197 := bbase (se 6 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 8658197 = 405853) (by norm_num)
theorem B1711381 : Blo 1012602 1711381 := bbase (se 6 (by rfl) ⟨40110, by rfl⟩ : syracuseStep 1711381 = 80221) (by norm_num)
theorem B3251477 : Blo 1012602 3251477 := bbase (se 6 (by rfl) ⟨76206, by rfl⟩ : syracuseStep 3251477 = 152413) (by norm_num)
theorem B1285409 : Blo 1012602 1285409 := bbase (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) (by norm_num)
theorem B2563397 : Blo 1012602 2563397 := bbase (se 4 (by rfl) ⟨240318, by rfl⟩ : syracuseStep 2563397 = 480637) (by norm_num)
theorem B1285465 : Blo 1012602 1285465 := bbase (se 2 (by rfl) ⟨482049, by rfl⟩ : syracuseStep 1285465 = 964099) (by norm_num)
theorem B4627813 : Blo 1012602 4627813 := bbase (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) (by norm_num)
theorem B1711469 : Blo 1012602 1711469 := bbase (se 3 (by rfl) ⟨320900, by rfl⟩ : syracuseStep 1711469 = 641801) (by norm_num)
theorem B5774773 : Blo 1012602 5774773 := bbase (se 5 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 5774773 = 541385) (by norm_num)
theorem B1285561 : Blo 1012602 1285561 := bbase (se 2 (by rfl) ⟨482085, by rfl⟩ : syracuseStep 1285561 = 964171) (by norm_num)
theorem B1711597 : Blo 1012602 1711597 := bbase (se 3 (by rfl) ⟨320924, by rfl⟩ : syracuseStep 1711597 = 641849) (by norm_num)
theorem B3907061 : Blo 1012602 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B2563589 : Blo 1012602 2563589 := bbase (se 4 (by rfl) ⟨240336, by rfl⟩ : syracuseStep 2563589 = 480673) (by norm_num)
theorem B1711685 : Blo 1012602 1711685 := bbase (se 4 (by rfl) ⟨160470, by rfl⟩ : syracuseStep 1711685 = 320941) (by norm_num)
theorem B4398661 : Blo 1012602 4398661 := bbase (se 4 (by rfl) ⟨412374, by rfl⟩ : syracuseStep 4398661 = 824749) (by norm_num)
theorem B1285733 : Blo 1012602 1285733 := bbase (se 4 (by rfl) ⟨120537, by rfl⟩ : syracuseStep 1285733 = 241075) (by norm_num)
theorem B1285789 : Blo 1012602 1285789 := bbase (se 3 (by rfl) ⟨241085, by rfl⟩ : syracuseStep 1285789 = 482171) (by norm_num)
theorem B1711813 : Blo 1012602 1711813 := bbase (se 4 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 1711813 = 320965) (by norm_num)
theorem B2891477 : Blo 1012602 2891477 := bbase (se 7 (by rfl) ⟨33884, by rfl⟩ : syracuseStep 2891477 = 67769) (by norm_num)
theorem B1285885 : Blo 1012602 1285885 := bbase (se 3 (by rfl) ⟨241103, by rfl⟩ : syracuseStep 1285885 = 482207) (by norm_num)
theorem B1154837 : Blo 1012602 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B11575061 : Blo 1012602 11575061 := bbase (se 6 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 11575061 = 542581) (by norm_num)
theorem B1711901 : Blo 1012602 1711901 := bbase (se 3 (by rfl) ⟨320981, by rfl⟩ : syracuseStep 1711901 = 641963) (by norm_num)
theorem B2563933 : Blo 1012602 2563933 := bbase (se 3 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 2563933 = 961475) (by norm_num)
theorem B1712029 : Blo 1012602 1712029 := bbase (se 3 (by rfl) ⟨321005, by rfl⟩ : syracuseStep 1712029 = 642011) (by norm_num)
theorem B1286057 : Blo 1012602 1286057 := bbase (se 2 (by rfl) ⟨482271, by rfl⟩ : syracuseStep 1286057 = 964543) (by norm_num)
theorem B2564045 : Blo 1012602 2564045 := bbase (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) (by norm_num)
theorem B2170837 : Blo 1012602 2170837 := bbase (se 7 (by rfl) ⟨25439, by rfl⟩ : syracuseStep 2170837 = 50879) (by norm_num)
theorem B1286113 : Blo 1012602 1286113 := bbase (se 2 (by rfl) ⟨482292, by rfl⟩ : syracuseStep 1286113 = 964585) (by norm_num)
theorem B6168565 : Blo 1012602 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B1712117 : Blo 1012602 1712117 := bbase (se 5 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 1712117 = 160511) (by norm_num)
theorem B11706389 : Blo 1012602 11706389 := bbase (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) (by norm_num)
theorem B1286209 : Blo 1012602 1286209 := bbase (se 2 (by rfl) ⟨482328, by rfl⟩ : syracuseStep 1286209 = 964657) (by norm_num)
theorem B2170957 : Blo 1012602 2170957 := bbase (se 3 (by rfl) ⟨407054, by rfl⟩ : syracuseStep 2170957 = 814109) (by norm_num)
theorem B1712245 : Blo 1012602 1712245 := bbase (se 5 (by rfl) ⟨80261, by rfl⟩ : syracuseStep 1712245 = 160523) (by norm_num)
theorem B2564237 : Blo 1012602 2564237 := bbase (se 3 (by rfl) ⟨480794, by rfl⟩ : syracuseStep 2564237 = 961589) (by norm_num)
theorem B1712333 : Blo 1012602 1712333 := bbase (se 3 (by rfl) ⟨321062, by rfl⟩ : syracuseStep 1712333 = 642125) (by norm_num)
theorem B6496469 : Blo 1012602 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B1286381 : Blo 1012602 1286381 := bbase (se 3 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 1286381 = 482393) (by norm_num)
theorem B1286437 : Blo 1012602 1286437 := bbase (se 4 (by rfl) ⟨120603, by rfl⟩ : syracuseStep 1286437 = 241207) (by norm_num)
theorem B1220933 : Blo 1012602 1220933 := bbase (se 4 (by rfl) ⟨114462, by rfl⟩ : syracuseStep 1220933 = 228925) (by norm_num)
theorem B1712461 : Blo 1012602 1712461 := bbase (se 3 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 1712461 = 642173) (by norm_num)
theorem B3252565 : Blo 1012602 3252565 := bbase (se 10 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 3252565 = 9529) (by norm_num)
theorem B1155421 : Blo 1012602 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B2892149 : Blo 1012602 2892149 := bbase (se 5 (by rfl) ⟨135569, by rfl⟩ : syracuseStep 2892149 = 271139) (by norm_num)
theorem B1286533 : Blo 1012602 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B1712549 : Blo 1012602 1712549 := bbase (se 4 (by rfl) ⟨160551, by rfl⟩ : syracuseStep 1712549 = 321103) (by norm_num)
theorem B2564581 : Blo 1012602 2564581 := bbase (se 4 (by rfl) ⟨240429, by rfl⟩ : syracuseStep 2564581 = 480859) (by norm_num)
theorem B1712677 : Blo 1012602 1712677 := bbase (se 4 (by rfl) ⟨160563, by rfl⟩ : syracuseStep 1712677 = 321127) (by norm_num)
theorem B2433581 : Blo 1012602 2433581 := bbase (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) (by norm_num)
theorem B2564693 : Blo 1012602 2564693 := bbase (se 8 (by rfl) ⟨15027, by rfl⟩ : syracuseStep 2564693 = 30055) (by norm_num)
theorem B1712765 : Blo 1012602 1712765 := bbase (se 3 (by rfl) ⟨321143, by rfl⟩ : syracuseStep 1712765 = 642287) (by norm_num)
theorem B1221265 : Blo 1012602 1221265 := bbase (se 2 (by rfl) ⟨457974, by rfl⟩ : syracuseStep 1221265 = 915949) (by norm_num)
theorem B2433773 : Blo 1012602 2433773 := bbase (se 3 (by rfl) ⟨456332, by rfl⟩ : syracuseStep 2433773 = 912665) (by norm_num)
theorem B1712893 : Blo 1012602 1712893 := bbase (se 3 (by rfl) ⟨321167, by rfl⟩ : syracuseStep 1712893 = 642335) (by norm_num)
theorem B2564885 : Blo 1012602 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B2892581 : Blo 1012602 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B1712981 : Blo 1012602 1712981 := bbase (se 9 (by rfl) ⟨5018, by rfl⟩ : syracuseStep 1712981 = 10037) (by norm_num)
theorem B1713109 : Blo 1012602 1713109 := bbase (se 7 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 1713109 = 40151) (by norm_num)
theorem B1713197 : Blo 1012602 1713197 := bbase (se 3 (by rfl) ⟨321224, by rfl⟩ : syracuseStep 1713197 = 642449) (by norm_num)
theorem B2565229 : Blo 1012602 2565229 := bbase (se 3 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 2565229 = 961961) (by norm_num)
theorem B3515557 : Blo 1012602 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B1713325 : Blo 1012602 1713325 := bbase (se 3 (by rfl) ⟨321248, by rfl⟩ : syracuseStep 1713325 = 642497) (by norm_num)
theorem B1156297 : Blo 1012602 1156297 := bbase (se 2 (by rfl) ⟨433611, by rfl⟩ : syracuseStep 1156297 = 867223) (by norm_num)
theorem B2565341 : Blo 1012602 2565341 := bbase (se 3 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 2565341 = 962003) (by norm_num)
theorem B1713413 : Blo 1012602 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B4695317 : Blo 1012602 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B5776757 : Blo 1012602 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B2467205 : Blo 1012602 2467205 := bbase (se 4 (by rfl) ⟨231300, by rfl⟩ : syracuseStep 2467205 = 462601) (by norm_num)
theorem B1713541 : Blo 1012602 1713541 := bbase (se 4 (by rfl) ⟨160644, by rfl⟩ : syracuseStep 1713541 = 321289) (by norm_num)
theorem B2565533 : Blo 1012602 2565533 := bbase (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) (by norm_num)
theorem B4335029 : Blo 1012602 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B1713629 : Blo 1012602 1713629 := bbase (se 3 (by rfl) ⟨321305, by rfl⟩ : syracuseStep 1713629 = 642611) (by norm_num)
theorem B3253733 : Blo 1012602 3253733 := bbase (se 4 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 3253733 = 610075) (by norm_num)
theorem B2434541 : Blo 1012602 2434541 := bbase (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) (by norm_num)
theorem B3417605 : Blo 1012602 3417605 := bbase (se 4 (by rfl) ⟨320400, by rfl⟩ : syracuseStep 3417605 = 640801) (by norm_num)
theorem B2893333 : Blo 1012602 2893333 := bbase (se 6 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 2893333 = 135625) (by norm_num)
theorem B1713757 : Blo 1012602 1713757 := bbase (se 3 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 1713757 = 642659) (by norm_num)
theorem B7710389 : Blo 1012602 7710389 := bbase (se 5 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 7710389 = 722849) (by norm_num)
theorem B1713845 : Blo 1012602 1713845 := bbase (se 5 (by rfl) ⟨80336, by rfl⟩ : syracuseStep 1713845 = 160673) (by norm_num)
theorem B2565877 : Blo 1012602 2565877 := bbase (se 5 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 2565877 = 240551) (by norm_num)
theorem B1484573 : Blo 1012602 1484573 := bbase (se 3 (by rfl) ⟨278357, by rfl⟩ : syracuseStep 1484573 = 556715) (by norm_num)
theorem B2598701 : Blo 1012602 2598701 := bbase (se 3 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 2598701 = 974513) (by norm_num)
theorem B1713973 : Blo 1012602 1713973 := bbase (se 5 (by rfl) ⟨80342, by rfl⟩ : syracuseStep 1713973 = 160685) (by norm_num)
theorem B54077269 : Blo 1012602 54077269 := bbase (se 9 (by rfl) ⟨158429, by rfl⟩ : syracuseStep 54077269 = 316859) (by norm_num)
theorem B2565989 : Blo 1012602 2565989 := bbase (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) (by norm_num)
theorem B1058689 : Blo 1012602 1058689 := bbase (se 2 (by rfl) ⟨397008, by rfl⟩ : syracuseStep 1058689 = 794017) (by norm_num)
theorem B1714061 : Blo 1012602 1714061 := bbase (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) (by norm_num)
theorem B3418037 : Blo 1012602 3418037 := bbase (se 5 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 3418037 = 320441) (by norm_num)
theorem B1714189 : Blo 1012602 1714189 := bbase (se 3 (by rfl) ⟨321410, by rfl⟩ : syracuseStep 1714189 = 642821) (by norm_num)
theorem B2566181 : Blo 1012602 2566181 := bbase (se 4 (by rfl) ⟨240579, by rfl⟩ : syracuseStep 2566181 = 481159) (by norm_num)
theorem B1714277 : Blo 1012602 1714277 := bbase (se 4 (by rfl) ⟨160713, by rfl⟩ : syracuseStep 1714277 = 321427) (by norm_num)
theorem B1714405 : Blo 1012602 1714405 := bbase (se 4 (by rfl) ⟨160725, by rfl⟩ : syracuseStep 1714405 = 321451) (by norm_num)
theorem B1714493 : Blo 1012602 1714493 := bbase (se 3 (by rfl) ⟨321467, by rfl⟩ : syracuseStep 1714493 = 642935) (by norm_num)
theorem B3418469 : Blo 1012602 3418469 := bbase (se 4 (by rfl) ⟨320481, by rfl⟩ : syracuseStep 3418469 = 640963) (by norm_num)
theorem B2566525 : Blo 1012602 2566525 := bbase (se 3 (by rfl) ⟨481223, by rfl⟩ : syracuseStep 2566525 = 962447) (by norm_num)
theorem B4336037 : Blo 1012602 4336037 := bbase (se 4 (by rfl) ⟨406503, by rfl⟩ : syracuseStep 4336037 = 813007) (by norm_num)
theorem B1714621 : Blo 1012602 1714621 := bbase (se 3 (by rfl) ⟨321491, by rfl⟩ : syracuseStep 1714621 = 642983) (by norm_num)
theorem B2566637 : Blo 1012602 2566637 := bbase (se 3 (by rfl) ⟨481244, by rfl⟩ : syracuseStep 2566637 = 962489) (by norm_num)
theorem B1714709 : Blo 1012602 1714709 := bbase (se 6 (by rfl) ⟨40188, by rfl⟩ : syracuseStep 1714709 = 80377) (by norm_num)
theorem B10693205 : Blo 1012602 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B1714837 : Blo 1012602 1714837 := bbase (se 6 (by rfl) ⟨40191, by rfl⟩ : syracuseStep 1714837 = 80383) (by norm_num)
theorem B2566829 : Blo 1012602 2566829 := bbase (se 3 (by rfl) ⟨481280, by rfl⟩ : syracuseStep 2566829 = 962561) (by norm_num)
theorem B1714925 : Blo 1012602 1714925 := bbase (se 3 (by rfl) ⟨321548, by rfl⟩ : syracuseStep 1714925 = 643097) (by norm_num)
theorem B3844853 : Blo 1012602 3844853 := bbase (se 5 (by rfl) ⟨180227, by rfl⟩ : syracuseStep 3844853 = 360455) (by norm_num)
theorem B3418901 : Blo 1012602 3418901 := bbase (se 6 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 3418901 = 160261) (by norm_num)
theorem B1715053 : Blo 1012602 1715053 := bbase (se 3 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 1715053 = 643145) (by norm_num)
theorem B4107125 : Blo 1012602 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B1715141 : Blo 1012602 1715141 := bbase (se 4 (by rfl) ⟨160794, by rfl⟩ : syracuseStep 1715141 = 321589) (by norm_num)
theorem B21933013 : Blo 1012602 21933013 := bbase (se 7 (by rfl) ⟨257027, by rfl⟩ : syracuseStep 21933013 = 514055) (by norm_num)
theorem B2567173 : Blo 1012602 2567173 := bbase (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) (by norm_num)
theorem B3845141 : Blo 1012602 3845141 := bbase (se 6 (by rfl) ⟨90120, by rfl⟩ : syracuseStep 3845141 = 180241) (by norm_num)
theorem B1715269 : Blo 1012602 1715269 := bbase (se 4 (by rfl) ⟨160806, by rfl⟩ : syracuseStep 1715269 = 321613) (by norm_num)
theorem B2174045 : Blo 1012602 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B2567285 : Blo 1012602 2567285 := bbase (se 5 (by rfl) ⟨120341, by rfl⟩ : syracuseStep 2567285 = 240683) (by norm_num)
theorem B1715357 : Blo 1012602 1715357 := bbase (se 3 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 1715357 = 643259) (by norm_num)
theorem B3419333 : Blo 1012602 3419333 := bbase (se 4 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 3419333 = 641125) (by norm_num)
theorem B1715485 : Blo 1012602 1715485 := bbase (se 3 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 1715485 = 643307) (by norm_num)
theorem B3255589 : Blo 1012602 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B2567477 : Blo 1012602 2567477 := bbase (se 5 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 2567477 = 240701) (by norm_num)
theorem B1518917 : Blo 1012602 1518917 := bbase (se 4 (by rfl) ⟨142398, by rfl⟩ : syracuseStep 1518917 = 284797) (by norm_num)
theorem B1518941 : Blo 1012602 1518941 := bbase (se 3 (by rfl) ⟨284801, by rfl⟩ : syracuseStep 1518941 = 569603) (by norm_num)
theorem B1518965 : Blo 1012602 1518965 := bbase (se 5 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 1518965 = 142403) (by norm_num)
theorem B1518989 : Blo 1012602 1518989 := bbase (se 3 (by rfl) ⟨284810, by rfl⟩ : syracuseStep 1518989 = 569621) (by norm_num)
theorem B1486237 : Blo 1012602 1486237 := bbase (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) (by norm_num)
theorem B1519013 : Blo 1012602 1519013 := bbase (se 4 (by rfl) ⟨142407, by rfl⟩ : syracuseStep 1519013 = 284815) (by norm_num)
theorem B1519037 : Blo 1012602 1519037 := bbase (se 3 (by rfl) ⟨284819, by rfl⟩ : syracuseStep 1519037 = 569639) (by norm_num)
theorem B1519061 : Blo 1012602 1519061 := bbase (se 7 (by rfl) ⟨17801, by rfl⟩ : syracuseStep 1519061 = 35603) (by norm_num)
theorem B1519085 : Blo 1012602 1519085 := bbase (se 3 (by rfl) ⟨284828, by rfl⟩ : syracuseStep 1519085 = 569657) (by norm_num)
theorem B1519109 : Blo 1012602 1519109 := bbase (se 4 (by rfl) ⟨142416, by rfl⟩ : syracuseStep 1519109 = 284833) (by norm_num)
theorem B5778965 : Blo 1012602 5778965 := bbase (se 6 (by rfl) ⟨135444, by rfl⟩ : syracuseStep 5778965 = 270889) (by norm_num)
theorem B1519133 : Blo 1012602 1519133 := bbase (se 3 (by rfl) ⟨284837, by rfl⟩ : syracuseStep 1519133 = 569675) (by norm_num)
theorem B2436637 : Blo 1012602 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B1519157 : Blo 1012602 1519157 := bbase (se 5 (by rfl) ⟨71210, by rfl⟩ : syracuseStep 1519157 = 142421) (by norm_num)
theorem B1027657 : Blo 1012602 1027657 := bbase (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) (by norm_num)
theorem B1519181 : Blo 1012602 1519181 := bbase (se 3 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 1519181 = 569693) (by norm_num)
theorem B1519205 : Blo 1012602 1519205 := bbase (se 4 (by rfl) ⟨142425, by rfl⟩ : syracuseStep 1519205 = 284851) (by norm_num)
theorem B3419765 : Blo 1012602 3419765 := bbase (se 5 (by rfl) ⟨160301, by rfl⟩ : syracuseStep 3419765 = 320603) (by norm_num)
theorem B1519229 : Blo 1012602 1519229 := bbase (se 3 (by rfl) ⟨284855, by rfl⟩ : syracuseStep 1519229 = 569711) (by norm_num)
theorem B2567821 : Blo 1012602 2567821 := bbase (se 3 (by rfl) ⟨481466, by rfl⟩ : syracuseStep 2567821 = 962933) (by norm_num)
theorem B1519253 : Blo 1012602 1519253 := bbase (se 6 (by rfl) ⟨35607, by rfl⟩ : syracuseStep 1519253 = 71215) (by norm_num)
theorem B1519277 : Blo 1012602 1519277 := bbase (se 3 (by rfl) ⟨284864, by rfl⟩ : syracuseStep 1519277 = 569729) (by norm_num)
theorem B1519301 : Blo 1012602 1519301 := bbase (se 4 (by rfl) ⟨142434, by rfl⟩ : syracuseStep 1519301 = 284869) (by norm_num)
theorem B1519325 : Blo 1012602 1519325 := bbase (se 3 (by rfl) ⟨284873, by rfl⟩ : syracuseStep 1519325 = 569747) (by norm_num)
theorem B1519349 : Blo 1012602 1519349 := bbase (se 5 (by rfl) ⟨71219, by rfl⟩ : syracuseStep 1519349 = 142439) (by norm_num)
theorem B2567933 : Blo 1012602 2567933 := bbase (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) (by norm_num)
theorem B1519373 : Blo 1012602 1519373 := bbase (se 3 (by rfl) ⟨284882, by rfl⟩ : syracuseStep 1519373 = 569765) (by norm_num)
theorem B1519397 : Blo 1012602 1519397 := bbase (se 4 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 1519397 = 284887) (by norm_num)
theorem B2928437 : Blo 1012602 2928437 := bbase (se 5 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 2928437 = 274541) (by norm_num)
theorem B1519421 : Blo 1012602 1519421 := bbase (se 3 (by rfl) ⟨284891, by rfl⟩ : syracuseStep 1519421 = 569783) (by norm_num)
theorem B1519445 : Blo 1012602 1519445 := bbase (se 9 (by rfl) ⟨4451, by rfl⟩ : syracuseStep 1519445 = 8903) (by norm_num)
theorem B1519469 : Blo 1012602 1519469 := bbase (se 3 (by rfl) ⟨284900, by rfl⟩ : syracuseStep 1519469 = 569801) (by norm_num)
theorem B1519493 : Blo 1012602 1519493 := bbase (se 4 (by rfl) ⟨142452, by rfl⟩ : syracuseStep 1519493 = 284905) (by norm_num)
theorem B1027981 : Blo 1012602 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B1519517 : Blo 1012602 1519517 := bbase (se 3 (by rfl) ⟨284909, by rfl⟩ : syracuseStep 1519517 = 569819) (by norm_num)
theorem B1519541 : Blo 1012602 1519541 := bbase (se 5 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 1519541 = 142457) (by norm_num)
theorem B2568125 : Blo 1012602 2568125 := bbase (se 3 (by rfl) ⟨481523, by rfl⟩ : syracuseStep 2568125 = 963047) (by norm_num)
theorem B1519565 : Blo 1012602 1519565 := bbase (se 3 (by rfl) ⟨284918, by rfl⟩ : syracuseStep 1519565 = 569837) (by norm_num)
theorem B1519589 : Blo 1012602 1519589 := bbase (se 4 (by rfl) ⟨142461, by rfl⟩ : syracuseStep 1519589 = 284923) (by norm_num)
theorem B1519613 : Blo 1012602 1519613 := bbase (se 3 (by rfl) ⟨284927, by rfl⟩ : syracuseStep 1519613 = 569855) (by norm_num)
theorem B1519637 : Blo 1012602 1519637 := bbase (se 6 (by rfl) ⟨35616, by rfl⟩ : syracuseStep 1519637 = 71233) (by norm_num)
theorem B3420197 : Blo 1012602 3420197 := bbase (se 4 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 3420197 = 641287) (by norm_num)
theorem B1519661 : Blo 1012602 1519661 := bbase (se 3 (by rfl) ⟨284936, by rfl⟩ : syracuseStep 1519661 = 569873) (by norm_num)
theorem B1519685 : Blo 1012602 1519685 := bbase (se 4 (by rfl) ⟨142470, by rfl⟩ : syracuseStep 1519685 = 284941) (by norm_num)
theorem B3518549 : Blo 1012602 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B1519709 : Blo 1012602 1519709 := bbase (se 3 (by rfl) ⟨284945, by rfl⟩ : syracuseStep 1519709 = 569891) (by norm_num)
theorem B1519733 : Blo 1012602 1519733 := bbase (se 5 (by rfl) ⟨71237, by rfl⟩ : syracuseStep 1519733 = 142475) (by norm_num)
theorem B4108421 : Blo 1012602 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B2437253 : Blo 1012602 2437253 := bbase (se 4 (by rfl) ⟨228492, by rfl⟩ : syracuseStep 2437253 = 456985) (by norm_num)
theorem B1519757 : Blo 1012602 1519757 := bbase (se 3 (by rfl) ⟨284954, by rfl⟩ : syracuseStep 1519757 = 569909) (by norm_num)
theorem B4337813 : Blo 1012602 4337813 := bbase (se 6 (by rfl) ⟨101667, by rfl⟩ : syracuseStep 4337813 = 203335) (by norm_num)
theorem B1519781 : Blo 1012602 1519781 := bbase (se 4 (by rfl) ⟨142479, by rfl⟩ : syracuseStep 1519781 = 284959) (by norm_num)
theorem B1028269 : Blo 1012602 1028269 := bbase (se 3 (by rfl) ⟨192800, by rfl⟩ : syracuseStep 1028269 = 385601) (by norm_num)
theorem B3846325 : Blo 1012602 3846325 := bbase (se 5 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 3846325 = 360593) (by norm_num)
theorem B1519805 : Blo 1012602 1519805 := bbase (se 3 (by rfl) ⟨284963, by rfl⟩ : syracuseStep 1519805 = 569927) (by norm_num)
theorem B2437309 : Blo 1012602 2437309 := bbase (se 3 (by rfl) ⟨456995, by rfl⟩ : syracuseStep 2437309 = 913991) (by norm_num)
theorem B1028305 : Blo 1012602 1028305 := bbase (se 2 (by rfl) ⟨385614, by rfl⟩ : syracuseStep 1028305 = 771229) (by norm_num)
theorem B1519829 : Blo 1012602 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B1519853 : Blo 1012602 1519853 := bbase (se 3 (by rfl) ⟨284972, by rfl⟩ : syracuseStep 1519853 = 569945) (by norm_num)
theorem B1519877 : Blo 1012602 1519877 := bbase (se 4 (by rfl) ⟨142488, by rfl⟩ : syracuseStep 1519877 = 284977) (by norm_num)
theorem B2568469 : Blo 1012602 2568469 := bbase (se 6 (by rfl) ⟨60198, by rfl⟩ : syracuseStep 2568469 = 120397) (by norm_num)
theorem B1519901 : Blo 1012602 1519901 := bbase (se 3 (by rfl) ⟨284981, by rfl⟩ : syracuseStep 1519901 = 569963) (by norm_num)
theorem B1519925 : Blo 1012602 1519925 := bbase (se 5 (by rfl) ⟨71246, by rfl⟩ : syracuseStep 1519925 = 142493) (by norm_num)
theorem B1519949 : Blo 1012602 1519949 := bbase (se 3 (by rfl) ⟨284990, by rfl⟩ : syracuseStep 1519949 = 569981) (by norm_num)
theorem B1519973 : Blo 1012602 1519973 := bbase (se 4 (by rfl) ⟨142497, by rfl⟩ : syracuseStep 1519973 = 284995) (by norm_num)
theorem B1519997 : Blo 1012602 1519997 := bbase (se 3 (by rfl) ⟨284999, by rfl⟩ : syracuseStep 1519997 = 569999) (by norm_num)
theorem B2568581 : Blo 1012602 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B1520021 : Blo 1012602 1520021 := bbase (se 6 (by rfl) ⟨35625, by rfl⟩ : syracuseStep 1520021 = 71251) (by norm_num)
theorem B1520045 : Blo 1012602 1520045 := bbase (se 3 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 1520045 = 570017) (by norm_num)
theorem B1520069 : Blo 1012602 1520069 := bbase (se 4 (by rfl) ⟨142506, by rfl⟩ : syracuseStep 1520069 = 285013) (by norm_num)
theorem B3420629 : Blo 1012602 3420629 := bbase (se 7 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 3420629 = 80171) (by norm_num)
theorem B1520093 : Blo 1012602 1520093 := bbase (se 3 (by rfl) ⟨285017, by rfl⟩ : syracuseStep 1520093 = 570035) (by norm_num)
theorem B3846629 : Blo 1012602 3846629 := bbase (se 4 (by rfl) ⟨360621, by rfl⟩ : syracuseStep 3846629 = 721243) (by norm_num)
theorem B1520117 : Blo 1012602 1520117 := bbase (se 5 (by rfl) ⟨71255, by rfl⟩ : syracuseStep 1520117 = 142511) (by norm_num)
theorem B1520141 : Blo 1012602 1520141 := bbase (se 3 (by rfl) ⟨285026, by rfl⟩ : syracuseStep 1520141 = 570053) (by norm_num)
theorem B3650069 : Blo 1012602 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B1520165 : Blo 1012602 1520165 := bbase (se 4 (by rfl) ⟨142515, by rfl⟩ : syracuseStep 1520165 = 285031) (by norm_num)
theorem B1520189 : Blo 1012602 1520189 := bbase (se 3 (by rfl) ⟨285035, by rfl⟩ : syracuseStep 1520189 = 570071) (by norm_num)
theorem B2568773 : Blo 1012602 2568773 := bbase (se 4 (by rfl) ⟨240822, by rfl⟩ : syracuseStep 2568773 = 481645) (by norm_num)
theorem B1520213 : Blo 1012602 1520213 := bbase (se 8 (by rfl) ⟨8907, by rfl⟩ : syracuseStep 1520213 = 17815) (by norm_num)
theorem B1520237 : Blo 1012602 1520237 := bbase (se 3 (by rfl) ⟨285044, by rfl⟩ : syracuseStep 1520237 = 570089) (by norm_num)
theorem B1520261 : Blo 1012602 1520261 := bbase (se 4 (by rfl) ⟨142524, by rfl⟩ : syracuseStep 1520261 = 285049) (by norm_num)
theorem B1520285 : Blo 1012602 1520285 := bbase (se 3 (by rfl) ⟨285053, by rfl⟩ : syracuseStep 1520285 = 570107) (by norm_num)
theorem B1520309 : Blo 1012602 1520309 := bbase (se 5 (by rfl) ⟨71264, by rfl⟩ : syracuseStep 1520309 = 142529) (by norm_num)
theorem B1520333 : Blo 1012602 1520333 := bbase (se 3 (by rfl) ⟨285062, by rfl⟩ : syracuseStep 1520333 = 570125) (by norm_num)
theorem B1520357 : Blo 1012602 1520357 := bbase (se 4 (by rfl) ⟨142533, by rfl⟩ : syracuseStep 1520357 = 285067) (by norm_num)
theorem B1520381 : Blo 1012602 1520381 := bbase (se 3 (by rfl) ⟨285071, by rfl⟩ : syracuseStep 1520381 = 570143) (by norm_num)
theorem B1520405 : Blo 1012602 1520405 := bbase (se 6 (by rfl) ⟨35634, by rfl⟩ : syracuseStep 1520405 = 71269) (by norm_num)
theorem B1520429 : Blo 1012602 1520429 := bbase (se 3 (by rfl) ⟨285080, by rfl⟩ : syracuseStep 1520429 = 570161) (by norm_num)
theorem B1520453 : Blo 1012602 1520453 := bbase (se 4 (by rfl) ⟨142542, by rfl⟩ : syracuseStep 1520453 = 285085) (by norm_num)
theorem B1520477 : Blo 1012602 1520477 := bbase (se 3 (by rfl) ⟨285089, by rfl⟩ : syracuseStep 1520477 = 570179) (by norm_num)
theorem B1520501 : Blo 1012602 1520501 := bbase (se 5 (by rfl) ⟨71273, by rfl⟩ : syracuseStep 1520501 = 142547) (by norm_num)
theorem B7811957 : Blo 1012602 7811957 := bbase (se 5 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 7811957 = 732371) (by norm_num)
theorem B3421061 : Blo 1012602 3421061 := bbase (se 4 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 3421061 = 641449) (by norm_num)
theorem B1520525 : Blo 1012602 1520525 := bbase (se 3 (by rfl) ⟨285098, by rfl⟩ : syracuseStep 1520525 = 570197) (by norm_num)
theorem B2569117 : Blo 1012602 2569117 := bbase (se 3 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 2569117 = 963419) (by norm_num)
theorem B1520549 : Blo 1012602 1520549 := bbase (se 4 (by rfl) ⟨142551, by rfl⟩ : syracuseStep 1520549 = 285103) (by norm_num)
theorem B1520573 : Blo 1012602 1520573 := bbase (se 3 (by rfl) ⟨285107, by rfl⟩ : syracuseStep 1520573 = 570215) (by norm_num)
theorem B1520597 : Blo 1012602 1520597 := bbase (se 7 (by rfl) ⟨17819, by rfl⟩ : syracuseStep 1520597 = 35639) (by norm_num)
theorem B1520621 : Blo 1012602 1520621 := bbase (se 3 (by rfl) ⟨285116, by rfl⟩ : syracuseStep 1520621 = 570233) (by norm_num)
theorem B1520645 : Blo 1012602 1520645 := bbase (se 4 (by rfl) ⟨142560, by rfl⟩ : syracuseStep 1520645 = 285121) (by norm_num)
theorem B2569229 : Blo 1012602 2569229 := bbase (se 3 (by rfl) ⟨481730, by rfl⟩ : syracuseStep 2569229 = 963461) (by norm_num)
theorem B1520669 : Blo 1012602 1520669 := bbase (se 3 (by rfl) ⟨285125, by rfl⟩ : syracuseStep 1520669 = 570251) (by norm_num)
theorem B1520693 : Blo 1012602 1520693 := bbase (se 5 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 1520693 = 142565) (by norm_num)
theorem B1520717 : Blo 1012602 1520717 := bbase (se 3 (by rfl) ⟨285134, by rfl⟩ : syracuseStep 1520717 = 570269) (by norm_num)
theorem B1520741 : Blo 1012602 1520741 := bbase (se 4 (by rfl) ⟨142569, by rfl⟩ : syracuseStep 1520741 = 285139) (by norm_num)
theorem B1520765 : Blo 1012602 1520765 := bbase (se 3 (by rfl) ⟨285143, by rfl⟩ : syracuseStep 1520765 = 570287) (by norm_num)
theorem B1520789 : Blo 1012602 1520789 := bbase (se 6 (by rfl) ⟨35643, by rfl⟩ : syracuseStep 1520789 = 71287) (by norm_num)
theorem B2438309 : Blo 1012602 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B1520813 : Blo 1012602 1520813 := bbase (se 3 (by rfl) ⟨285152, by rfl⟩ : syracuseStep 1520813 = 570305) (by norm_num)
theorem B1520837 : Blo 1012602 1520837 := bbase (se 4 (by rfl) ⟨142578, by rfl⟩ : syracuseStep 1520837 = 285157) (by norm_num)
theorem B2569421 : Blo 1012602 2569421 := bbase (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) (by norm_num)
theorem B1520861 : Blo 1012602 1520861 := bbase (se 3 (by rfl) ⟨285161, by rfl⟩ : syracuseStep 1520861 = 570323) (by norm_num)
theorem B1520885 : Blo 1012602 1520885 := bbase (se 5 (by rfl) ⟨71291, by rfl⟩ : syracuseStep 1520885 = 142583) (by norm_num)
theorem B1520909 : Blo 1012602 1520909 := bbase (se 3 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 1520909 = 570341) (by norm_num)
theorem B1520933 : Blo 1012602 1520933 := bbase (se 4 (by rfl) ⟨142587, by rfl⟩ : syracuseStep 1520933 = 285175) (by norm_num)
theorem B3421493 : Blo 1012602 3421493 := bbase (se 5 (by rfl) ⟨160382, by rfl⟩ : syracuseStep 3421493 = 320765) (by norm_num)
theorem B1520957 : Blo 1012602 1520957 := bbase (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) (by norm_num)
theorem B1520981 : Blo 1012602 1520981 := bbase (se 13 (by rfl) ⟨278, by rfl⟩ : syracuseStep 1520981 = 557) (by norm_num)
theorem B1521005 : Blo 1012602 1521005 := bbase (se 3 (by rfl) ⟨285188, by rfl⟩ : syracuseStep 1521005 = 570377) (by norm_num)
theorem B1521029 : Blo 1012602 1521029 := bbase (se 4 (by rfl) ⟨142596, by rfl⟩ : syracuseStep 1521029 = 285193) (by norm_num)
theorem B1521053 : Blo 1012602 1521053 := bbase (se 3 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 1521053 = 570395) (by norm_num)
theorem B9876917 : Blo 1012602 9876917 := bbase (se 5 (by rfl) ⟨462980, by rfl⟩ : syracuseStep 9876917 = 925961) (by norm_num)
theorem B1521077 : Blo 1012602 1521077 := bbase (se 5 (by rfl) ⟨71300, by rfl⟩ : syracuseStep 1521077 = 142601) (by norm_num)
theorem B1521101 : Blo 1012602 1521101 := bbase (se 3 (by rfl) ⟨285206, by rfl⟩ : syracuseStep 1521101 = 570413) (by norm_num)
theorem B1521125 : Blo 1012602 1521125 := bbase (se 4 (by rfl) ⟨142605, by rfl⟩ : syracuseStep 1521125 = 285211) (by norm_num)
theorem B1521149 : Blo 1012602 1521149 := bbase (se 3 (by rfl) ⟨285215, by rfl⟩ : syracuseStep 1521149 = 570431) (by norm_num)
theorem B1521173 : Blo 1012602 1521173 := bbase (se 6 (by rfl) ⟨35652, by rfl⟩ : syracuseStep 1521173 = 71305) (by norm_num)
theorem B2569765 : Blo 1012602 2569765 := bbase (se 4 (by rfl) ⟨240915, by rfl⟩ : syracuseStep 2569765 = 481831) (by norm_num)
theorem B1521197 : Blo 1012602 1521197 := bbase (se 3 (by rfl) ⟨285224, by rfl⟩ : syracuseStep 1521197 = 570449) (by norm_num)
theorem B1521221 : Blo 1012602 1521221 := bbase (se 4 (by rfl) ⟨142614, by rfl⟩ : syracuseStep 1521221 = 285229) (by norm_num)
theorem B1521245 : Blo 1012602 1521245 := bbase (se 3 (by rfl) ⟨285233, by rfl⟩ : syracuseStep 1521245 = 570467) (by norm_num)
theorem B1521269 : Blo 1012602 1521269 := bbase (se 5 (by rfl) ⟨71309, by rfl⟩ : syracuseStep 1521269 = 142619) (by norm_num)
theorem B1521293 : Blo 1012602 1521293 := bbase (se 3 (by rfl) ⟨285242, by rfl⟩ : syracuseStep 1521293 = 570485) (by norm_num)
theorem B2569877 : Blo 1012602 2569877 := bbase (se 6 (by rfl) ⟨60231, by rfl⟩ : syracuseStep 2569877 = 120463) (by norm_num)
theorem B1521317 : Blo 1012602 1521317 := bbase (se 4 (by rfl) ⟨142623, by rfl⟩ : syracuseStep 1521317 = 285247) (by norm_num)
theorem B1521341 : Blo 1012602 1521341 := bbase (se 3 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 1521341 = 570503) (by norm_num)
theorem B10401493 : Blo 1012602 10401493 := bbase (se 7 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 10401493 = 243785) (by norm_num)
theorem B1521365 : Blo 1012602 1521365 := bbase (se 7 (by rfl) ⟨17828, by rfl⟩ : syracuseStep 1521365 = 35657) (by norm_num)
theorem B3421925 : Blo 1012602 3421925 := bbase (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) (by norm_num)
theorem B1521389 : Blo 1012602 1521389 := bbase (se 3 (by rfl) ⟨285260, by rfl⟩ : syracuseStep 1521389 = 570521) (by norm_num)
theorem B6502133 : Blo 1012602 6502133 := bbase (se 5 (by rfl) ⟨304787, by rfl⟩ : syracuseStep 6502133 = 609575) (by norm_num)
theorem B1521413 : Blo 1012602 1521413 := bbase (se 4 (by rfl) ⟨142632, by rfl⟩ : syracuseStep 1521413 = 285265) (by norm_num)
theorem B1521437 : Blo 1012602 1521437 := bbase (se 3 (by rfl) ⟨285269, by rfl⟩ : syracuseStep 1521437 = 570539) (by norm_num)
theorem B1521461 : Blo 1012602 1521461 := bbase (se 5 (by rfl) ⟨71318, by rfl⟩ : syracuseStep 1521461 = 142637) (by norm_num)
theorem B1521485 : Blo 1012602 1521485 := bbase (se 3 (by rfl) ⟨285278, by rfl⟩ : syracuseStep 1521485 = 570557) (by norm_num)
theorem B2570069 : Blo 1012602 2570069 := bbase (se 9 (by rfl) ⟨7529, by rfl⟩ : syracuseStep 2570069 = 15059) (by norm_num)
theorem B1521509 : Blo 1012602 1521509 := bbase (se 4 (by rfl) ⟨142641, by rfl⟩ : syracuseStep 1521509 = 285283) (by norm_num)
theorem B1521533 : Blo 1012602 1521533 := bbase (se 3 (by rfl) ⟨285287, by rfl⟩ : syracuseStep 1521533 = 570575) (by norm_num)
theorem B1030033 : Blo 1012602 1030033 := bbase (se 2 (by rfl) ⟨386262, by rfl⟩ : syracuseStep 1030033 = 772525) (by norm_num)
theorem B1521557 : Blo 1012602 1521557 := bbase (se 6 (by rfl) ⟨35661, by rfl⟩ : syracuseStep 1521557 = 71323) (by norm_num)
theorem B1521581 : Blo 1012602 1521581 := bbase (se 3 (by rfl) ⟨285296, by rfl⟩ : syracuseStep 1521581 = 570593) (by norm_num)
theorem B1521605 : Blo 1012602 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B1521629 : Blo 1012602 1521629 := bbase (se 3 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 1521629 = 570611) (by norm_num)
theorem B1521653 : Blo 1012602 1521653 := bbase (se 5 (by rfl) ⟨71327, by rfl⟩ : syracuseStep 1521653 = 142655) (by norm_num)
theorem B1521677 : Blo 1012602 1521677 := bbase (se 3 (by rfl) ⟨285314, by rfl⟩ : syracuseStep 1521677 = 570629) (by norm_num)
theorem B1521701 : Blo 1012602 1521701 := bbase (se 4 (by rfl) ⟨142659, by rfl⟩ : syracuseStep 1521701 = 285319) (by norm_num)
theorem B1521725 : Blo 1012602 1521725 := bbase (se 3 (by rfl) ⟨285323, by rfl⟩ : syracuseStep 1521725 = 570647) (by norm_num)
theorem B1980493 : Blo 1012602 1980493 := bbase (se 3 (by rfl) ⟨371342, by rfl⟩ : syracuseStep 1980493 = 742685) (by norm_num)
theorem B1521749 : Blo 1012602 1521749 := bbase (se 8 (by rfl) ⟨8916, by rfl⟩ : syracuseStep 1521749 = 17833) (by norm_num)
theorem B1521773 : Blo 1012602 1521773 := bbase (se 3 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 1521773 = 570665) (by norm_num)
theorem B1521797 : Blo 1012602 1521797 := bbase (se 4 (by rfl) ⟨142668, by rfl⟩ : syracuseStep 1521797 = 285337) (by norm_num)
theorem B3422357 : Blo 1012602 3422357 := bbase (se 6 (by rfl) ⟨80211, by rfl⟩ : syracuseStep 3422357 = 160423) (by norm_num)
theorem B1521821 : Blo 1012602 1521821 := bbase (se 3 (by rfl) ⟨285341, by rfl⟩ : syracuseStep 1521821 = 570683) (by norm_num)
theorem B2570413 : Blo 1012602 2570413 := bbase (se 3 (by rfl) ⟨481952, by rfl⟩ : syracuseStep 2570413 = 963905) (by norm_num)
theorem B1521845 : Blo 1012602 1521845 := bbase (se 5 (by rfl) ⟨71336, by rfl⟩ : syracuseStep 1521845 = 142673) (by norm_num)
theorem B1521869 : Blo 1012602 1521869 := bbase (se 3 (by rfl) ⟨285350, by rfl⟩ : syracuseStep 1521869 = 570701) (by norm_num)
theorem B1521893 : Blo 1012602 1521893 := bbase (se 4 (by rfl) ⟨142677, by rfl⟩ : syracuseStep 1521893 = 285355) (by norm_num)
theorem B1521917 : Blo 1012602 1521917 := bbase (se 3 (by rfl) ⟨285359, by rfl⟩ : syracuseStep 1521917 = 570719) (by norm_num)
theorem B1521941 : Blo 1012602 1521941 := bbase (se 6 (by rfl) ⟨35670, by rfl⟩ : syracuseStep 1521941 = 71341) (by norm_num)
theorem B2570525 : Blo 1012602 2570525 := bbase (se 3 (by rfl) ⟨481973, by rfl⟩ : syracuseStep 2570525 = 963947) (by norm_num)
theorem B1521965 : Blo 1012602 1521965 := bbase (se 3 (by rfl) ⟨285368, by rfl⟩ : syracuseStep 1521965 = 570737) (by norm_num)
theorem B1521989 : Blo 1012602 1521989 := bbase (se 4 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 1521989 = 285373) (by norm_num)
theorem B5486933 : Blo 1012602 5486933 := bbase (se 10 (by rfl) ⟨8037, by rfl⟩ : syracuseStep 5486933 = 16075) (by norm_num)
theorem B1522013 : Blo 1012602 1522013 := bbase (se 3 (by rfl) ⟨285377, by rfl⟩ : syracuseStep 1522013 = 570755) (by norm_num)
theorem B1522037 : Blo 1012602 1522037 := bbase (se 5 (by rfl) ⟨71345, by rfl⟩ : syracuseStep 1522037 = 142691) (by norm_num)
theorem B1980805 : Blo 1012602 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B1522061 : Blo 1012602 1522061 := bbase (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) (by norm_num)
theorem B1522085 : Blo 1012602 1522085 := bbase (se 4 (by rfl) ⟨142695, by rfl⟩ : syracuseStep 1522085 = 285391) (by norm_num)
theorem B1522109 : Blo 1012602 1522109 := bbase (se 3 (by rfl) ⟨285395, by rfl⟩ : syracuseStep 1522109 = 570791) (by norm_num)
theorem B1522133 : Blo 1012602 1522133 := bbase (se 7 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 1522133 = 35675) (by norm_num)
theorem B5487061 : Blo 1012602 5487061 := bbase (se 7 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 5487061 = 128603) (by norm_num)
theorem B2570717 : Blo 1012602 2570717 := bbase (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) (by norm_num)
theorem B4110821 : Blo 1012602 4110821 := bbase (se 4 (by rfl) ⟨385389, by rfl⟩ : syracuseStep 4110821 = 770779) (by norm_num)
theorem B1522157 : Blo 1012602 1522157 := bbase (se 3 (by rfl) ⟨285404, by rfl⟩ : syracuseStep 1522157 = 570809) (by norm_num)
theorem B1522181 : Blo 1012602 1522181 := bbase (se 4 (by rfl) ⟨142704, by rfl⟩ : syracuseStep 1522181 = 285409) (by norm_num)
theorem B1522205 : Blo 1012602 1522205 := bbase (se 3 (by rfl) ⟨285413, by rfl⟩ : syracuseStep 1522205 = 570827) (by norm_num)
theorem B3848741 : Blo 1012602 3848741 := bbase (se 4 (by rfl) ⟨360819, by rfl⟩ : syracuseStep 3848741 = 721639) (by norm_num)
theorem B1522229 : Blo 1012602 1522229 := bbase (se 5 (by rfl) ⟨71354, by rfl⟩ : syracuseStep 1522229 = 142709) (by norm_num)
theorem B3422789 : Blo 1012602 3422789 := bbase (se 4 (by rfl) ⟨320886, by rfl⟩ : syracuseStep 3422789 = 641773) (by norm_num)
theorem B1522253 : Blo 1012602 1522253 := bbase (se 3 (by rfl) ⟨285422, by rfl⟩ : syracuseStep 1522253 = 570845) (by norm_num)
theorem B2964053 : Blo 1012602 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B1522277 : Blo 1012602 1522277 := bbase (se 4 (by rfl) ⟨142713, by rfl⟩ : syracuseStep 1522277 = 285427) (by norm_num)
theorem B1522301 : Blo 1012602 1522301 := bbase (se 3 (by rfl) ⟨285431, by rfl⟩ : syracuseStep 1522301 = 570863) (by norm_num)
theorem B1522325 : Blo 1012602 1522325 := bbase (se 6 (by rfl) ⟨35679, by rfl⟩ : syracuseStep 1522325 = 71359) (by norm_num)
theorem B1522349 : Blo 1012602 1522349 := bbase (se 3 (by rfl) ⟨285440, by rfl⟩ : syracuseStep 1522349 = 570881) (by norm_num)
theorem B1522373 : Blo 1012602 1522373 := bbase (se 4 (by rfl) ⟨142722, by rfl⟩ : syracuseStep 1522373 = 285445) (by norm_num)
theorem B1522397 : Blo 1012602 1522397 := bbase (se 3 (by rfl) ⟨285449, by rfl⟩ : syracuseStep 1522397 = 570899) (by norm_num)
theorem B1522421 : Blo 1012602 1522421 := bbase (se 5 (by rfl) ⟨71363, by rfl⟩ : syracuseStep 1522421 = 142727) (by norm_num)
theorem B1522445 : Blo 1012602 1522445 := bbase (se 3 (by rfl) ⟨285458, by rfl⟩ : syracuseStep 1522445 = 570917) (by norm_num)
theorem B1522469 : Blo 1012602 1522469 := bbase (se 4 (by rfl) ⟨142731, by rfl⟩ : syracuseStep 1522469 = 285463) (by norm_num)
theorem B1391413 : Blo 1012602 1391413 := bbase (se 5 (by rfl) ⟨65222, by rfl⟩ : syracuseStep 1391413 = 130445) (by norm_num)
theorem B2571061 : Blo 1012602 2571061 := bbase (se 5 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 2571061 = 241037) (by norm_num)
theorem B1522493 : Blo 1012602 1522493 := bbase (se 3 (by rfl) ⟨285467, by rfl⟩ : syracuseStep 1522493 = 570935) (by norm_num)
theorem B3849029 : Blo 1012602 3849029 := bbase (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) (by norm_num)
theorem B1522517 : Blo 1012602 1522517 := bbase (se 9 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 1522517 = 8921) (by norm_num)
theorem B1522541 : Blo 1012602 1522541 := bbase (se 3 (by rfl) ⟨285476, by rfl⟩ : syracuseStep 1522541 = 570953) (by norm_num)
theorem B1522565 : Blo 1012602 1522565 := bbase (se 4 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 1522565 = 285481) (by norm_num)
theorem B1522589 : Blo 1012602 1522589 := bbase (se 3 (by rfl) ⟨285485, by rfl⟩ : syracuseStep 1522589 = 570971) (by norm_num)
theorem B2571173 : Blo 1012602 2571173 := bbase (se 4 (by rfl) ⟨241047, by rfl⟩ : syracuseStep 2571173 = 482095) (by norm_num)
theorem B1522613 : Blo 1012602 1522613 := bbase (se 5 (by rfl) ⟨71372, by rfl⟩ : syracuseStep 1522613 = 142745) (by norm_num)
theorem B1522637 : Blo 1012602 1522637 := bbase (se 3 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 1522637 = 570989) (by norm_num)
theorem B1522661 : Blo 1012602 1522661 := bbase (se 4 (by rfl) ⟨142749, by rfl⟩ : syracuseStep 1522661 = 285499) (by norm_num)
theorem B3423221 : Blo 1012602 3423221 := bbase (se 5 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 3423221 = 320927) (by norm_num)
theorem B1522685 : Blo 1012602 1522685 := bbase (se 3 (by rfl) ⟨285503, by rfl⟩ : syracuseStep 1522685 = 571007) (by norm_num)
theorem B1522709 : Blo 1012602 1522709 := bbase (se 6 (by rfl) ⟨35688, by rfl⟩ : syracuseStep 1522709 = 71377) (by norm_num)
theorem B1522733 : Blo 1012602 1522733 := bbase (se 3 (by rfl) ⟨285512, by rfl⟩ : syracuseStep 1522733 = 571025) (by norm_num)
theorem B1522757 : Blo 1012602 1522757 := bbase (se 4 (by rfl) ⟨142758, by rfl⟩ : syracuseStep 1522757 = 285517) (by norm_num)
theorem B1522781 : Blo 1012602 1522781 := bbase (se 3 (by rfl) ⟨285521, by rfl⟩ : syracuseStep 1522781 = 571043) (by norm_num)
theorem B2571365 : Blo 1012602 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B1850485 : Blo 1012602 1850485 := bbase (se 5 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 1850485 = 173483) (by norm_num)
theorem B1522805 : Blo 1012602 1522805 := bbase (se 5 (by rfl) ⟨71381, by rfl⟩ : syracuseStep 1522805 = 142763) (by norm_num)
theorem B1522829 : Blo 1012602 1522829 := bbase (se 3 (by rfl) ⟨285530, by rfl⟩ : syracuseStep 1522829 = 571061) (by norm_num)
theorem B8666261 : Blo 1012602 8666261 := bbase (se 6 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 8666261 = 406231) (by norm_num)
theorem B1522853 : Blo 1012602 1522853 := bbase (se 4 (by rfl) ⟨142767, by rfl⟩ : syracuseStep 1522853 = 285535) (by norm_num)
theorem B1522877 : Blo 1012602 1522877 := bbase (se 3 (by rfl) ⟨285539, by rfl⟩ : syracuseStep 1522877 = 571079) (by norm_num)
theorem B1522901 : Blo 1012602 1522901 := bbase (se 7 (by rfl) ⟨17846, by rfl⟩ : syracuseStep 1522901 = 35693) (by norm_num)
theorem B1522925 : Blo 1012602 1522925 := bbase (se 3 (by rfl) ⟨285548, by rfl⟩ : syracuseStep 1522925 = 571097) (by norm_num)
theorem B9747701 : Blo 1012602 9747701 := bbase (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) (by norm_num)
theorem B1522949 : Blo 1012602 1522949 := bbase (se 4 (by rfl) ⟨142776, by rfl⟩ : syracuseStep 1522949 = 285553) (by norm_num)
theorem B1522973 : Blo 1012602 1522973 := bbase (se 3 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 1522973 = 571115) (by norm_num)
theorem B5127461 : Blo 1012602 5127461 := bbase (se 4 (by rfl) ⟨480699, by rfl⟩ : syracuseStep 5127461 = 961399) (by norm_num)
theorem B1522997 : Blo 1012602 1522997 := bbase (se 5 (by rfl) ⟨71390, by rfl⟩ : syracuseStep 1522997 = 142781) (by norm_num)
theorem B1523021 : Blo 1012602 1523021 := bbase (se 3 (by rfl) ⟨285566, by rfl⟩ : syracuseStep 1523021 = 571133) (by norm_num)
theorem B1523045 : Blo 1012602 1523045 := bbase (se 4 (by rfl) ⟨142785, by rfl⟩ : syracuseStep 1523045 = 285571) (by norm_num)
theorem B1523069 : Blo 1012602 1523069 := bbase (se 3 (by rfl) ⟨285575, by rfl⟩ : syracuseStep 1523069 = 571151) (by norm_num)
theorem B1523093 : Blo 1012602 1523093 := bbase (se 6 (by rfl) ⟨35697, by rfl⟩ : syracuseStep 1523093 = 71395) (by norm_num)
theorem B3423653 : Blo 1012602 3423653 := bbase (se 4 (by rfl) ⟨320967, by rfl⟩ : syracuseStep 3423653 = 641935) (by norm_num)
theorem B1523117 : Blo 1012602 1523117 := bbase (se 3 (by rfl) ⟨285584, by rfl⟩ : syracuseStep 1523117 = 571169) (by norm_num)
theorem B2571709 : Blo 1012602 2571709 := bbase (se 3 (by rfl) ⟨482195, by rfl⟩ : syracuseStep 2571709 = 964391) (by norm_num)
theorem B1523141 : Blo 1012602 1523141 := bbase (se 4 (by rfl) ⟨142794, by rfl⟩ : syracuseStep 1523141 = 285589) (by norm_num)
theorem B1523165 : Blo 1012602 1523165 := bbase (se 3 (by rfl) ⟨285593, by rfl⟩ : syracuseStep 1523165 = 571187) (by norm_num)
theorem B2440685 : Blo 1012602 2440685 := bbase (se 3 (by rfl) ⟨457628, by rfl⟩ : syracuseStep 2440685 = 915257) (by norm_num)
theorem B1523189 : Blo 1012602 1523189 := bbase (se 5 (by rfl) ⟨71399, by rfl⟩ : syracuseStep 1523189 = 142799) (by norm_num)
theorem B1523213 : Blo 1012602 1523213 := bbase (se 3 (by rfl) ⟨285602, by rfl⟩ : syracuseStep 1523213 = 571205) (by norm_num)
theorem B1523237 : Blo 1012602 1523237 := bbase (se 4 (by rfl) ⟨142803, by rfl⟩ : syracuseStep 1523237 = 285607) (by norm_num)
theorem B2571821 : Blo 1012602 2571821 := bbase (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) (by norm_num)
theorem B1523261 : Blo 1012602 1523261 := bbase (se 3 (by rfl) ⟨285611, by rfl⟩ : syracuseStep 1523261 = 571223) (by norm_num)
theorem B1523285 : Blo 1012602 1523285 := bbase (se 8 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 1523285 = 17851) (by norm_num)
theorem B2637413 : Blo 1012602 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B1523309 : Blo 1012602 1523309 := bbase (se 3 (by rfl) ⟨285620, by rfl⟩ : syracuseStep 1523309 = 571241) (by norm_num)
theorem B1523333 : Blo 1012602 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B1523357 : Blo 1012602 1523357 := bbase (se 3 (by rfl) ⟨285629, by rfl⟩ : syracuseStep 1523357 = 571259) (by norm_num)
theorem B1523381 : Blo 1012602 1523381 := bbase (se 5 (by rfl) ⟨71408, by rfl⟩ : syracuseStep 1523381 = 142817) (by norm_num)
theorem B1523405 : Blo 1012602 1523405 := bbase (se 3 (by rfl) ⟨285638, by rfl⟩ : syracuseStep 1523405 = 571277) (by norm_num)
theorem B1523429 : Blo 1012602 1523429 := bbase (se 4 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 1523429 = 285643) (by norm_num)
theorem B2572013 : Blo 1012602 2572013 := bbase (se 3 (by rfl) ⟨482252, by rfl⟩ : syracuseStep 2572013 = 964505) (by norm_num)
theorem B1523453 : Blo 1012602 1523453 := bbase (se 3 (by rfl) ⟨285647, by rfl⟩ : syracuseStep 1523453 = 571295) (by norm_num)
theorem B1523477 : Blo 1012602 1523477 := bbase (se 6 (by rfl) ⟨35706, by rfl⟩ : syracuseStep 1523477 = 71413) (by norm_num)
theorem B1523501 : Blo 1012602 1523501 := bbase (se 3 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 1523501 = 571313) (by norm_num)
theorem B1523525 : Blo 1012602 1523525 := bbase (se 4 (by rfl) ⟨142830, by rfl⟩ : syracuseStep 1523525 = 285661) (by norm_num)
theorem B3424085 : Blo 1012602 3424085 := bbase (se 9 (by rfl) ⟨10031, by rfl⟩ : syracuseStep 3424085 = 20063) (by norm_num)
theorem B1523549 : Blo 1012602 1523549 := bbase (se 3 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 1523549 = 571331) (by norm_num)
theorem B2441069 : Blo 1012602 2441069 := bbase (se 3 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 2441069 = 915401) (by norm_num)
theorem B1523573 : Blo 1012602 1523573 := bbase (se 5 (by rfl) ⟨71417, by rfl⟩ : syracuseStep 1523573 = 142835) (by norm_num)
theorem B1523597 : Blo 1012602 1523597 := bbase (se 3 (by rfl) ⟨285674, by rfl⟩ : syracuseStep 1523597 = 571349) (by norm_num)
theorem B1523621 : Blo 1012602 1523621 := bbase (se 4 (by rfl) ⟨142839, by rfl⟩ : syracuseStep 1523621 = 285679) (by norm_num)
theorem B1523645 : Blo 1012602 1523645 := bbase (se 3 (by rfl) ⟨285683, by rfl⟩ : syracuseStep 1523645 = 571367) (by norm_num)
theorem B1523669 : Blo 1012602 1523669 := bbase (se 7 (by rfl) ⟨17855, by rfl⟩ : syracuseStep 1523669 = 35711) (by norm_num)
theorem B3850213 : Blo 1012602 3850213 := bbase (se 4 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 3850213 = 721915) (by norm_num)
theorem B1523693 : Blo 1012602 1523693 := bbase (se 3 (by rfl) ⟨285692, by rfl⟩ : syracuseStep 1523693 = 571385) (by norm_num)
theorem B1523717 : Blo 1012602 1523717 := bbase (se 4 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 1523717 = 285697) (by norm_num)
theorem B1523741 : Blo 1012602 1523741 := bbase (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) (by norm_num)
theorem B1523765 : Blo 1012602 1523765 := bbase (se 5 (by rfl) ⟨71426, by rfl⟩ : syracuseStep 1523765 = 142853) (by norm_num)
theorem B2441269 : Blo 1012602 2441269 := bbase (se 5 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 2441269 = 228869) (by norm_num)
theorem B2572357 : Blo 1012602 2572357 := bbase (se 4 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 2572357 = 482317) (by norm_num)
theorem B1523789 : Blo 1012602 1523789 := bbase (se 3 (by rfl) ⟨285710, by rfl⟩ : syracuseStep 1523789 = 571421) (by norm_num)
theorem B1523813 : Blo 1012602 1523813 := bbase (se 4 (by rfl) ⟨142857, by rfl⟩ : syracuseStep 1523813 = 285715) (by norm_num)
theorem B1523837 : Blo 1012602 1523837 := bbase (se 3 (by rfl) ⟨285719, by rfl⟩ : syracuseStep 1523837 = 571439) (by norm_num)
theorem B1523861 : Blo 1012602 1523861 := bbase (se 6 (by rfl) ⟨35715, by rfl⟩ : syracuseStep 1523861 = 71431) (by norm_num)
theorem B1523885 : Blo 1012602 1523885 := bbase (se 3 (by rfl) ⟨285728, by rfl⟩ : syracuseStep 1523885 = 571457) (by norm_num)
theorem B2572469 : Blo 1012602 2572469 := bbase (se 5 (by rfl) ⟨120584, by rfl⟩ : syracuseStep 2572469 = 241169) (by norm_num)
theorem B1523909 : Blo 1012602 1523909 := bbase (se 4 (by rfl) ⟨142866, by rfl⟩ : syracuseStep 1523909 = 285733) (by norm_num)
theorem B1523933 : Blo 1012602 1523933 := bbase (se 3 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 1523933 = 571475) (by norm_num)
theorem B1523957 : Blo 1012602 1523957 := bbase (se 5 (by rfl) ⟨71435, by rfl⟩ : syracuseStep 1523957 = 142871) (by norm_num)
theorem B3424517 : Blo 1012602 3424517 := bbase (se 4 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 3424517 = 642097) (by norm_num)
theorem B1622285 : Blo 1012602 1622285 := bbase (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) (by norm_num)
theorem B1523981 : Blo 1012602 1523981 := bbase (se 3 (by rfl) ⟨285746, by rfl⟩ : syracuseStep 1523981 = 571493) (by norm_num)
theorem B3850517 : Blo 1012602 3850517 := bbase (se 6 (by rfl) ⟨90246, by rfl⟩ : syracuseStep 3850517 = 180493) (by norm_num)
theorem B1524005 : Blo 1012602 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B1524029 : Blo 1012602 1524029 := bbase (se 3 (by rfl) ⟨285755, by rfl⟩ : syracuseStep 1524029 = 571511) (by norm_num)
theorem B4342085 : Blo 1012602 4342085 := bbase (se 4 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 4342085 = 814141) (by norm_num)
theorem B1524053 : Blo 1012602 1524053 := bbase (se 10 (by rfl) ⟨2232, by rfl⟩ : syracuseStep 1524053 = 4465) (by norm_num)
theorem B2343277 : Blo 1012602 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B1524077 : Blo 1012602 1524077 := bbase (se 3 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 1524077 = 571529) (by norm_num)
theorem B2572661 : Blo 1012602 2572661 := bbase (se 5 (by rfl) ⟨120593, by rfl⟩ : syracuseStep 2572661 = 241187) (by norm_num)
theorem B1524101 : Blo 1012602 1524101 := bbase (se 4 (by rfl) ⟨142884, by rfl⟩ : syracuseStep 1524101 = 285769) (by norm_num)
theorem B1524125 : Blo 1012602 1524125 := bbase (se 3 (by rfl) ⟨285773, by rfl⟩ : syracuseStep 1524125 = 571547) (by norm_num)
theorem B1524149 : Blo 1012602 1524149 := bbase (se 5 (by rfl) ⟨71444, by rfl⟩ : syracuseStep 1524149 = 142889) (by norm_num)
theorem B1622477 : Blo 1012602 1622477 := bbase (se 3 (by rfl) ⟨304214, by rfl⟩ : syracuseStep 1622477 = 608429) (by norm_num)
theorem B1524173 : Blo 1012602 1524173 := bbase (se 3 (by rfl) ⟨285782, by rfl⟩ : syracuseStep 1524173 = 571565) (by norm_num)
theorem B1524197 : Blo 1012602 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B1524221 : Blo 1012602 1524221 := bbase (se 3 (by rfl) ⟨285791, by rfl⟩ : syracuseStep 1524221 = 571583) (by norm_num)
theorem B1524245 : Blo 1012602 1524245 := bbase (se 6 (by rfl) ⟨35724, by rfl⟩ : syracuseStep 1524245 = 71449) (by norm_num)
theorem B1524269 : Blo 1012602 1524269 := bbase (se 3 (by rfl) ⟨285800, by rfl⟩ : syracuseStep 1524269 = 571601) (by norm_num)
theorem B5128757 : Blo 1012602 5128757 := bbase (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) (by norm_num)
theorem B1524293 : Blo 1012602 1524293 := bbase (se 4 (by rfl) ⟨142902, by rfl⟩ : syracuseStep 1524293 = 285805) (by norm_num)
theorem B1524317 : Blo 1012602 1524317 := bbase (se 3 (by rfl) ⟨285809, by rfl⟩ : syracuseStep 1524317 = 571619) (by norm_num)
theorem B1950325 : Blo 1012602 1950325 := bbase (se 5 (by rfl) ⟨91421, by rfl⟩ : syracuseStep 1950325 = 182843) (by norm_num)
theorem B1524341 : Blo 1012602 1524341 := bbase (se 5 (by rfl) ⟨71453, by rfl⟩ : syracuseStep 1524341 = 142907) (by norm_num)
theorem B1852045 : Blo 1012602 1852045 := bbase (se 3 (by rfl) ⟨347258, by rfl⟩ : syracuseStep 1852045 = 694517) (by norm_num)
theorem B1524365 : Blo 1012602 1524365 := bbase (se 3 (by rfl) ⟨285818, by rfl⟩ : syracuseStep 1524365 = 571637) (by norm_num)
theorem B2310805 : Blo 1012602 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B1524389 : Blo 1012602 1524389 := bbase (se 4 (by rfl) ⟨142911, by rfl⟩ : syracuseStep 1524389 = 285823) (by norm_num)
theorem B3424949 : Blo 1012602 3424949 := bbase (se 5 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 3424949 = 321089) (by norm_num)
theorem B1524413 : Blo 1012602 1524413 := bbase (se 3 (by rfl) ⟨285827, by rfl⟩ : syracuseStep 1524413 = 571655) (by norm_num)
theorem B2573005 : Blo 1012602 2573005 := bbase (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) (by norm_num)
theorem B1524437 : Blo 1012602 1524437 := bbase (se 7 (by rfl) ⟨17864, by rfl⟩ : syracuseStep 1524437 = 35729) (by norm_num)
theorem B4113125 : Blo 1012602 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B1524461 : Blo 1012602 1524461 := bbase (se 3 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 1524461 = 571673) (by norm_num)
theorem B10535669 : Blo 1012602 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B1524485 : Blo 1012602 1524485 := bbase (se 4 (by rfl) ⟨142920, by rfl⟩ : syracuseStep 1524485 = 285841) (by norm_num)
theorem B1524509 : Blo 1012602 1524509 := bbase (se 3 (by rfl) ⟨285845, by rfl⟩ : syracuseStep 1524509 = 571691) (by norm_num)
theorem B1524533 : Blo 1012602 1524533 := bbase (se 5 (by rfl) ⟨71462, by rfl⟩ : syracuseStep 1524533 = 142925) (by norm_num)
theorem B2573117 : Blo 1012602 2573117 := bbase (se 3 (by rfl) ⟨482459, by rfl⟩ : syracuseStep 2573117 = 964919) (by norm_num)
theorem B1524557 : Blo 1012602 1524557 := bbase (se 3 (by rfl) ⟨285854, by rfl⟩ : syracuseStep 1524557 = 571709) (by norm_num)
theorem B1524581 : Blo 1012602 1524581 := bbase (se 4 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 1524581 = 285859) (by norm_num)
theorem B1098617 : Blo 1012602 1098617 := bbase (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) (by norm_num)
theorem B1524605 : Blo 1012602 1524605 := bbase (se 3 (by rfl) ⟨285863, by rfl⟩ : syracuseStep 1524605 = 571727) (by norm_num)
theorem B1524629 : Blo 1012602 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B1524653 : Blo 1012602 1524653 := bbase (se 3 (by rfl) ⟨285872, by rfl⟩ : syracuseStep 1524653 = 571745) (by norm_num)
theorem B1524677 : Blo 1012602 1524677 := bbase (se 4 (by rfl) ⟨142938, by rfl⟩ : syracuseStep 1524677 = 285877) (by norm_num)
theorem B1524701 : Blo 1012602 1524701 := bbase (se 3 (by rfl) ⟨285881, by rfl⟩ : syracuseStep 1524701 = 571763) (by norm_num)
theorem B1524725 : Blo 1012602 1524725 := bbase (se 5 (by rfl) ⟨71471, by rfl⟩ : syracuseStep 1524725 = 142943) (by norm_num)
theorem B1524749 : Blo 1012602 1524749 := bbase (se 3 (by rfl) ⟨285890, by rfl⟩ : syracuseStep 1524749 = 571781) (by norm_num)
theorem B2278421 : Blo 1012602 2278421 := bbase (se 6 (by rfl) ⟨53400, by rfl⟩ : syracuseStep 2278421 = 106801) (by norm_num)
theorem B1524773 : Blo 1012602 1524773 := bbase (se 4 (by rfl) ⟨142947, by rfl⟩ : syracuseStep 1524773 = 285895) (by norm_num)
theorem B1524797 : Blo 1012602 1524797 := bbase (se 3 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 1524797 = 571799) (by norm_num)
theorem B1524821 : Blo 1012602 1524821 := bbase (se 8 (by rfl) ⟨8934, by rfl⟩ : syracuseStep 1524821 = 17869) (by norm_num)
theorem B2278493 : Blo 1012602 2278493 := bbase (se 3 (by rfl) ⟨427217, by rfl⟩ : syracuseStep 2278493 = 854435) (by norm_num)
theorem B3425381 : Blo 1012602 3425381 := bbase (se 4 (by rfl) ⟨321129, by rfl⟩ : syracuseStep 3425381 = 642259) (by norm_num)
theorem B1524845 : Blo 1012602 1524845 := bbase (se 3 (by rfl) ⟨285908, by rfl⟩ : syracuseStep 1524845 = 571817) (by norm_num)
theorem B1524869 : Blo 1012602 1524869 := bbase (se 4 (by rfl) ⟨142956, by rfl⟩ : syracuseStep 1524869 = 285913) (by norm_num)
theorem B1524893 : Blo 1012602 1524893 := bbase (se 3 (by rfl) ⟨285917, by rfl⟩ : syracuseStep 1524893 = 571835) (by norm_num)
theorem B2278565 : Blo 1012602 2278565 := bbase (se 4 (by rfl) ⟨213615, by rfl⟩ : syracuseStep 2278565 = 427231) (by norm_num)
theorem B4867237 : Blo 1012602 4867237 := bbase (se 4 (by rfl) ⟨456303, by rfl⟩ : syracuseStep 4867237 = 912607) (by norm_num)
theorem B2278637 : Blo 1012602 2278637 := bbase (se 3 (by rfl) ⟨427244, by rfl⟩ : syracuseStep 2278637 = 854489) (by norm_num)
theorem B7718165 : Blo 1012602 7718165 := bbase (se 6 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 7718165 = 361789) (by norm_num)
theorem B2278709 : Blo 1012602 2278709 := bbase (se 5 (by rfl) ⟨106814, by rfl⟩ : syracuseStep 2278709 = 213629) (by norm_num)
theorem B2278781 : Blo 1012602 2278781 := bbase (se 3 (by rfl) ⟨427271, by rfl⟩ : syracuseStep 2278781 = 854543) (by norm_num)
theorem B2278853 : Blo 1012602 2278853 := bbase (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) (by norm_num)
theorem B2278925 : Blo 1012602 2278925 := bbase (se 3 (by rfl) ⟨427298, by rfl⟩ : syracuseStep 2278925 = 854597) (by norm_num)
theorem B3425813 : Blo 1012602 3425813 := bbase (se 6 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 3425813 = 160585) (by norm_num)
theorem B2278997 : Blo 1012602 2278997 := bbase (se 8 (by rfl) ⟨13353, by rfl⟩ : syracuseStep 2278997 = 26707) (by norm_num)
theorem B2279069 : Blo 1012602 2279069 := bbase (se 3 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 2279069 = 854651) (by norm_num)
theorem B2344661 : Blo 1012602 2344661 := bbase (se 7 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 2344661 = 54953) (by norm_num)
theorem B2279141 : Blo 1012602 2279141 := bbase (se 4 (by rfl) ⟨213669, by rfl⟩ : syracuseStep 2279141 = 427339) (by norm_num)
theorem B1623797 : Blo 1012602 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B2279213 : Blo 1012602 2279213 := bbase (se 3 (by rfl) ⟨427352, by rfl⟩ : syracuseStep 2279213 = 854705) (by norm_num)
theorem B5130053 : Blo 1012602 5130053 := bbase (se 4 (by rfl) ⟨480942, by rfl⟩ : syracuseStep 5130053 = 961885) (by norm_num)
theorem B1623893 : Blo 1012602 1623893 := bbase (se 9 (by rfl) ⟨4757, by rfl⟩ : syracuseStep 1623893 = 9515) (by norm_num)
theorem B2279285 : Blo 1012602 2279285 := bbase (se 5 (by rfl) ⟨106841, by rfl⟩ : syracuseStep 2279285 = 213683) (by norm_num)
theorem B1623925 : Blo 1012602 1623925 := bbase (se 5 (by rfl) ⟨76121, by rfl⟩ : syracuseStep 1623925 = 152243) (by norm_num)
theorem B2279357 : Blo 1012602 2279357 := bbase (se 3 (by rfl) ⟨427379, by rfl⟩ : syracuseStep 2279357 = 854759) (by norm_num)
theorem B3426245 : Blo 1012602 3426245 := bbase (se 4 (by rfl) ⟨321210, by rfl⟩ : syracuseStep 3426245 = 642421) (by norm_num)
theorem B7325653 : Blo 1012602 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B2279429 : Blo 1012602 2279429 := bbase (se 4 (by rfl) ⟨213696, by rfl⟩ : syracuseStep 2279429 = 427393) (by norm_num)
theorem B2279501 : Blo 1012602 2279501 := bbase (se 3 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 2279501 = 854813) (by norm_num)
theorem B2279573 : Blo 1012602 2279573 := bbase (se 6 (by rfl) ⟨53427, by rfl⟩ : syracuseStep 2279573 = 106855) (by norm_num)
theorem B2279645 : Blo 1012602 2279645 := bbase (se 3 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 2279645 = 854867) (by norm_num)
theorem B2279717 : Blo 1012602 2279717 := bbase (se 4 (by rfl) ⟨213723, by rfl⟩ : syracuseStep 2279717 = 427447) (by norm_num)
theorem B3852629 : Blo 1012602 3852629 := bbase (se 10 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 3852629 = 11287) (by norm_num)
theorem B2279789 : Blo 1012602 2279789 := bbase (se 3 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 2279789 = 854921) (by norm_num)
theorem B3426677 : Blo 1012602 3426677 := bbase (se 5 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 3426677 = 321251) (by norm_num)
theorem B6244789 : Blo 1012602 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B2279861 : Blo 1012602 2279861 := bbase (se 5 (by rfl) ⟨106868, by rfl⟩ : syracuseStep 2279861 = 213737) (by norm_num)
theorem B1100245 : Blo 1012602 1100245 := bbase (se 7 (by rfl) ⟨12893, by rfl⟩ : syracuseStep 1100245 = 25787) (by norm_num)
theorem B9882101 : Blo 1012602 9882101 := bbase (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) (by norm_num)
theorem B2279933 : Blo 1012602 2279933 := bbase (se 3 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 2279933 = 854975) (by norm_num)
theorem B2280005 : Blo 1012602 2280005 := bbase (se 4 (by rfl) ⟨213750, by rfl⟩ : syracuseStep 2280005 = 427501) (by norm_num)
theorem B3525205 : Blo 1012602 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B3852917 : Blo 1012602 3852917 := bbase (se 5 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 3852917 = 361211) (by norm_num)
theorem B2280077 : Blo 1012602 2280077 := bbase (se 3 (by rfl) ⟨427514, by rfl⟩ : syracuseStep 2280077 = 855029) (by norm_num)
theorem B2280149 : Blo 1012602 2280149 := bbase (se 7 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 2280149 = 53441) (by norm_num)
theorem B1854181 : Blo 1012602 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B2280221 : Blo 1012602 2280221 := bbase (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) (by norm_num)
theorem B3427109 : Blo 1012602 3427109 := bbase (se 4 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 3427109 = 642583) (by norm_num)
theorem B2280293 : Blo 1012602 2280293 := bbase (se 4 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 2280293 = 427555) (by norm_num)
theorem B2280365 : Blo 1012602 2280365 := bbase (se 3 (by rfl) ⟨427568, by rfl⟩ : syracuseStep 2280365 = 855137) (by norm_num)
theorem B5721013 : Blo 1012602 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B2280437 : Blo 1012602 2280437 := bbase (se 5 (by rfl) ⟨106895, by rfl⟩ : syracuseStep 2280437 = 213791) (by norm_num)
theorem B2739205 : Blo 1012602 2739205 := bbase (se 4 (by rfl) ⟨256800, by rfl⟩ : syracuseStep 2739205 = 513601) (by norm_num)
theorem B2280509 : Blo 1012602 2280509 := bbase (se 3 (by rfl) ⟨427595, by rfl⟩ : syracuseStep 2280509 = 855191) (by norm_num)
theorem B5131349 : Blo 1012602 5131349 := bbase (se 8 (by rfl) ⟨30066, by rfl⟩ : syracuseStep 5131349 = 60133) (by norm_num)
theorem B3132533 : Blo 1012602 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B2280581 : Blo 1012602 2280581 := bbase (se 4 (by rfl) ⟨213804, by rfl⟩ : syracuseStep 2280581 = 427609) (by norm_num)
theorem B2280653 : Blo 1012602 2280653 := bbase (se 3 (by rfl) ⟨427622, by rfl⟩ : syracuseStep 2280653 = 855245) (by norm_num)
theorem B3427541 : Blo 1012602 3427541 := bbase (se 7 (by rfl) ⟨40166, by rfl⟩ : syracuseStep 3427541 = 80333) (by norm_num)
theorem B2280725 : Blo 1012602 2280725 := bbase (se 6 (by rfl) ⟨53454, by rfl⟩ : syracuseStep 2280725 = 106909) (by norm_num)
theorem B2280797 : Blo 1012602 2280797 := bbase (se 3 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 2280797 = 855299) (by norm_num)
theorem B1625437 : Blo 1012602 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B2280869 : Blo 1012602 2280869 := bbase (se 4 (by rfl) ⟨213831, by rfl⟩ : syracuseStep 2280869 = 427663) (by norm_num)
theorem B2280941 : Blo 1012602 2280941 := bbase (se 3 (by rfl) ⟨427676, by rfl⟩ : syracuseStep 2280941 = 855353) (by norm_num)
theorem B2281013 : Blo 1012602 2281013 := bbase (se 5 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 2281013 = 213845) (by norm_num)
theorem B2281085 : Blo 1012602 2281085 := bbase (se 3 (by rfl) ⟨427703, by rfl⟩ : syracuseStep 2281085 = 855407) (by norm_num)
theorem B3427973 : Blo 1012602 3427973 := bbase (se 4 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 3427973 = 642745) (by norm_num)
theorem B2281157 : Blo 1012602 2281157 := bbase (se 4 (by rfl) ⟨213858, by rfl⟩ : syracuseStep 2281157 = 427717) (by norm_num)
theorem B2281229 : Blo 1012602 2281229 := bbase (se 3 (by rfl) ⟨427730, by rfl⟩ : syracuseStep 2281229 = 855461) (by norm_num)
theorem B3854101 : Blo 1012602 3854101 := bbase (se 6 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 3854101 = 180661) (by norm_num)
theorem B1953589 : Blo 1012602 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B2281301 : Blo 1012602 2281301 := bbase (se 9 (by rfl) ⟨6683, by rfl⟩ : syracuseStep 2281301 = 13367) (by norm_num)
theorem B2281373 : Blo 1012602 2281373 := bbase (se 3 (by rfl) ⟨427757, by rfl⟩ : syracuseStep 2281373 = 855515) (by norm_num)
theorem B2281445 : Blo 1012602 2281445 := bbase (se 4 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 2281445 = 427771) (by norm_num)
theorem B2084861 : Blo 1012602 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B1626149 : Blo 1012602 1626149 := bbase (se 4 (by rfl) ⟨152451, by rfl⟩ : syracuseStep 1626149 = 304903) (by norm_num)
theorem B2281517 : Blo 1012602 2281517 := bbase (se 3 (by rfl) ⟨427784, by rfl⟩ : syracuseStep 2281517 = 855569) (by norm_num)
theorem B3428405 : Blo 1012602 3428405 := bbase (se 5 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 3428405 = 321413) (by norm_num)
theorem B3854405 : Blo 1012602 3854405 := bbase (se 4 (by rfl) ⟨361350, by rfl⟩ : syracuseStep 3854405 = 722701) (by norm_num)
theorem B2281589 : Blo 1012602 2281589 := bbase (se 5 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 2281589 = 213899) (by norm_num)
theorem B2281661 : Blo 1012602 2281661 := bbase (se 3 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 2281661 = 855623) (by norm_num)
theorem B2281733 : Blo 1012602 2281733 := bbase (se 4 (by rfl) ⟨213912, by rfl⟩ : syracuseStep 2281733 = 427825) (by norm_num)
theorem B2314565 : Blo 1012602 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B2281805 : Blo 1012602 2281805 := bbase (se 3 (by rfl) ⟨427838, by rfl⟩ : syracuseStep 2281805 = 855677) (by norm_num)
theorem B2085197 : Blo 1012602 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B5132645 : Blo 1012602 5132645 := bbase (se 4 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 5132645 = 962371) (by norm_num)
theorem B2281877 : Blo 1012602 2281877 := bbase (se 6 (by rfl) ⟨53481, by rfl⟩ : syracuseStep 2281877 = 106963) (by norm_num)
theorem B2314709 : Blo 1012602 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B2281949 : Blo 1012602 2281949 := bbase (se 3 (by rfl) ⟨427865, by rfl⟩ : syracuseStep 2281949 = 855731) (by norm_num)
theorem B3658213 : Blo 1012602 3658213 := bbase (se 4 (by rfl) ⟨342957, by rfl⟩ : syracuseStep 3658213 = 685915) (by norm_num)
theorem B3428837 : Blo 1012602 3428837 := bbase (se 4 (by rfl) ⟨321453, by rfl⟩ : syracuseStep 3428837 = 642907) (by norm_num)
theorem B2282021 : Blo 1012602 2282021 := bbase (se 4 (by rfl) ⟨213939, by rfl⟩ : syracuseStep 2282021 = 427879) (by norm_num)
theorem B2282093 : Blo 1012602 2282093 := bbase (se 3 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 2282093 = 855785) (by norm_num)
theorem B3658373 : Blo 1012602 3658373 := bbase (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) (by norm_num)
theorem B2282165 : Blo 1012602 2282165 := bbase (se 5 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 2282165 = 213953) (by norm_num)
theorem B9261749 : Blo 1012602 9261749 := bbase (se 5 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 9261749 = 868289) (by norm_num)
theorem B4870853 : Blo 1012602 4870853 := bbase (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) (by norm_num)
theorem B1626821 : Blo 1012602 1626821 := bbase (se 4 (by rfl) ⟨152514, by rfl⟩ : syracuseStep 1626821 = 305029) (by norm_num)
theorem B2282237 : Blo 1012602 2282237 := bbase (se 3 (by rfl) ⟨427919, by rfl⟩ : syracuseStep 2282237 = 855839) (by norm_num)
theorem B2282309 : Blo 1012602 2282309 := bbase (se 4 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 2282309 = 427933) (by norm_num)
theorem B2282381 : Blo 1012602 2282381 := bbase (se 3 (by rfl) ⟨427946, by rfl⟩ : syracuseStep 2282381 = 855893) (by norm_num)
theorem B3429269 : Blo 1012602 3429269 := bbase (se 6 (by rfl) ⟨80373, by rfl⟩ : syracuseStep 3429269 = 160747) (by norm_num)
theorem B10539989 : Blo 1012602 10539989 := bbase (se 7 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 10539989 = 247031) (by norm_num)
theorem B2282453 : Blo 1012602 2282453 := bbase (se 7 (by rfl) ⟨26747, by rfl⟩ : syracuseStep 2282453 = 53495) (by norm_num)
theorem B2282525 : Blo 1012602 2282525 := bbase (se 3 (by rfl) ⟨427973, by rfl⟩ : syracuseStep 2282525 = 855947) (by norm_num)
theorem B2282597 : Blo 1012602 2282597 := bbase (se 4 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 2282597 = 427987) (by norm_num)
theorem B2282669 : Blo 1012602 2282669 := bbase (se 3 (by rfl) ⟨428000, by rfl⟩ : syracuseStep 2282669 = 856001) (by norm_num)
theorem B5788853 : Blo 1012602 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B1627333 : Blo 1012602 1627333 := bbase (se 4 (by rfl) ⟨152562, by rfl⟩ : syracuseStep 1627333 = 305125) (by norm_num)
theorem B2282741 : Blo 1012602 2282741 := bbase (se 5 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 2282741 = 214007) (by norm_num)
theorem B2282813 : Blo 1012602 2282813 := bbase (se 3 (by rfl) ⟨428027, by rfl⟩ : syracuseStep 2282813 = 856055) (by norm_num)
theorem B3429701 : Blo 1012602 3429701 := bbase (se 4 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 3429701 = 643069) (by norm_num)
theorem B2282885 : Blo 1012602 2282885 := bbase (se 4 (by rfl) ⟨214020, by rfl⟩ : syracuseStep 2282885 = 428041) (by norm_num)
theorem B2282957 : Blo 1012602 2282957 := bbase (se 3 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 2282957 = 856109) (by norm_num)
theorem B1922525 : Blo 1012602 1922525 := bbase (se 3 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 1922525 = 720947) (by norm_num)
theorem B2283029 : Blo 1012602 2283029 := bbase (se 6 (by rfl) ⟨53508, by rfl⟩ : syracuseStep 2283029 = 107017) (by norm_num)
theorem B5494325 : Blo 1012602 5494325 := bbase (se 5 (by rfl) ⟨257546, by rfl⟩ : syracuseStep 5494325 = 515093) (by norm_num)
theorem B2283101 : Blo 1012602 2283101 := bbase (se 3 (by rfl) ⟨428081, by rfl⟩ : syracuseStep 2283101 = 856163) (by norm_num)
theorem B5133941 : Blo 1012602 5133941 := bbase (se 5 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 5133941 = 481307) (by norm_num)
theorem B1627789 : Blo 1012602 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B2283173 : Blo 1012602 2283173 := bbase (se 4 (by rfl) ⟨214047, by rfl⟩ : syracuseStep 2283173 = 428095) (by norm_num)
theorem B2053837 : Blo 1012602 2053837 := bbase (se 3 (by rfl) ⟨385094, by rfl⟩ : syracuseStep 2053837 = 770189) (by norm_num)
theorem B2283245 : Blo 1012602 2283245 := bbase (se 3 (by rfl) ⟨428108, by rfl⟩ : syracuseStep 2283245 = 856217) (by norm_num)
theorem B3430133 : Blo 1012602 3430133 := bbase (se 5 (by rfl) ⟨160787, by rfl⟩ : syracuseStep 3430133 = 321575) (by norm_num)
theorem B2283317 : Blo 1012602 2283317 := bbase (se 5 (by rfl) ⟨107030, by rfl⟩ : syracuseStep 2283317 = 214061) (by norm_num)
theorem B2283389 : Blo 1012602 2283389 := bbase (se 3 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 2283389 = 856271) (by norm_num)
theorem B2381717 : Blo 1012602 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B2283461 : Blo 1012602 2283461 := bbase (se 4 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 2283461 = 428149) (by norm_num)
theorem B2283533 : Blo 1012602 2283533 := bbase (se 3 (by rfl) ⟨428162, by rfl⟩ : syracuseStep 2283533 = 856325) (by norm_num)
theorem B2283605 : Blo 1012602 2283605 := bbase (se 8 (by rfl) ⟨13380, by rfl⟩ : syracuseStep 2283605 = 26761) (by norm_num)
theorem B3856517 : Blo 1012602 3856517 := bbase (se 4 (by rfl) ⟨361548, by rfl⟩ : syracuseStep 3856517 = 723097) (by norm_num)
theorem B2283677 : Blo 1012602 2283677 := bbase (se 3 (by rfl) ⟨428189, by rfl⟩ : syracuseStep 2283677 = 856379) (by norm_num)
theorem B3430565 : Blo 1012602 3430565 := bbase (se 4 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 3430565 = 643231) (by norm_num)
theorem B1923277 : Blo 1012602 1923277 := bbase (se 3 (by rfl) ⟨360614, by rfl⟩ : syracuseStep 1923277 = 721229) (by norm_num)
theorem B2283749 : Blo 1012602 2283749 := bbase (se 4 (by rfl) ⟨214101, by rfl⟩ : syracuseStep 2283749 = 428203) (by norm_num)
theorem B2283821 : Blo 1012602 2283821 := bbase (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) (by norm_num)
theorem B1923421 : Blo 1012602 1923421 := bbase (se 3 (by rfl) ⟨360641, by rfl⟩ : syracuseStep 1923421 = 721283) (by norm_num)
theorem B2283893 : Blo 1012602 2283893 := bbase (se 5 (by rfl) ⟨107057, by rfl⟩ : syracuseStep 2283893 = 214115) (by norm_num)
theorem B3856805 : Blo 1012602 3856805 := bbase (se 4 (by rfl) ⟨361575, by rfl⟩ : syracuseStep 3856805 = 723151) (by norm_num)
theorem B2283965 : Blo 1012602 2283965 := bbase (se 3 (by rfl) ⟨428243, by rfl⟩ : syracuseStep 2283965 = 856487) (by norm_num)
theorem B1923581 : Blo 1012602 1923581 := bbase (se 3 (by rfl) ⟨360671, by rfl⟩ : syracuseStep 1923581 = 721343) (by norm_num)
theorem B2284037 : Blo 1012602 2284037 := bbase (se 4 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 2284037 = 428257) (by norm_num)
theorem B4872757 : Blo 1012602 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B4872773 : Blo 1012602 4872773 := bbase (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) (by norm_num)
theorem B2284109 : Blo 1012602 2284109 := bbase (se 3 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 2284109 = 856541) (by norm_num)
theorem B3430997 : Blo 1012602 3430997 := bbase (se 8 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 3430997 = 40207) (by norm_num)
theorem B1923725 : Blo 1012602 1923725 := bbase (se 3 (by rfl) ⟨360698, by rfl⟩ : syracuseStep 1923725 = 721397) (by norm_num)
theorem B2284181 : Blo 1012602 2284181 := bbase (se 6 (by rfl) ⟨53535, by rfl⟩ : syracuseStep 2284181 = 107071) (by norm_num)
theorem B1825445 : Blo 1012602 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B2284253 : Blo 1012602 2284253 := bbase (se 3 (by rfl) ⟨428297, by rfl⟩ : syracuseStep 2284253 = 856595) (by norm_num)
theorem B2284325 : Blo 1012602 2284325 := bbase (se 4 (by rfl) ⟨214155, by rfl⟩ : syracuseStep 2284325 = 428311) (by norm_num)
theorem B2284397 : Blo 1012602 2284397 := bbase (se 3 (by rfl) ⟨428324, by rfl⟩ : syracuseStep 2284397 = 856649) (by norm_num)
theorem B5135237 : Blo 1012602 5135237 := bbase (se 4 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 5135237 = 962857) (by norm_num)
theorem B1924013 : Blo 1012602 1924013 := bbase (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) (by norm_num)
theorem B2284469 : Blo 1012602 2284469 := bbase (se 5 (by rfl) ⟨107084, by rfl⟩ : syracuseStep 2284469 = 214169) (by norm_num)
theorem B2284541 : Blo 1012602 2284541 := bbase (se 3 (by rfl) ⟨428351, by rfl⟩ : syracuseStep 2284541 = 856703) (by norm_num)
theorem B1924165 : Blo 1012602 1924165 := bbase (se 4 (by rfl) ⟨180390, by rfl⟩ : syracuseStep 1924165 = 360781) (by norm_num)
theorem B2284613 : Blo 1012602 2284613 := bbase (se 4 (by rfl) ⟨214182, by rfl⟩ : syracuseStep 2284613 = 428365) (by norm_num)
theorem B1236061 : Blo 1012602 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B2284685 : Blo 1012602 2284685 := bbase (se 3 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 2284685 = 856757) (by norm_num)
theorem B1301665 : Blo 1012602 1301665 := bbase (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) (by norm_num)
theorem B2317501 : Blo 1012602 2317501 := bbase (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) (by norm_num)
theorem B2284757 : Blo 1012602 2284757 := bbase (se 7 (by rfl) ⟨26774, by rfl⟩ : syracuseStep 2284757 = 53549) (by norm_num)
theorem B2284829 : Blo 1012602 2284829 := bbase (se 3 (by rfl) ⟨428405, by rfl⟩ : syracuseStep 2284829 = 856811) (by norm_num)
theorem B3661141 : Blo 1012602 3661141 := bbase (se 11 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3661141 = 5363) (by norm_num)
theorem B2284901 : Blo 1012602 2284901 := bbase (se 4 (by rfl) ⟨214209, by rfl⟩ : syracuseStep 2284901 = 428419) (by norm_num)
theorem B1924469 : Blo 1012602 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B2284973 : Blo 1012602 2284973 := bbase (se 3 (by rfl) ⟨428432, by rfl⟩ : syracuseStep 2284973 = 856865) (by norm_num)
theorem B2285045 : Blo 1012602 2285045 := bbase (se 5 (by rfl) ⟨107111, by rfl⟩ : syracuseStep 2285045 = 214223) (by norm_num)
theorem B3661301 : Blo 1012602 3661301 := bbase (se 5 (by rfl) ⟨171623, by rfl⟩ : syracuseStep 3661301 = 343247) (by norm_num)
theorem B2285117 : Blo 1012602 2285117 := bbase (se 3 (by rfl) ⟨428459, by rfl⟩ : syracuseStep 2285117 = 856919) (by norm_num)
theorem B2743877 : Blo 1012602 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B3857989 : Blo 1012602 3857989 := bbase (se 4 (by rfl) ⟨361686, by rfl⟩ : syracuseStep 3857989 = 723373) (by norm_num)
theorem B2252405 : Blo 1012602 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B2285189 : Blo 1012602 2285189 := bbase (se 4 (by rfl) ⟨214236, by rfl⟩ : syracuseStep 2285189 = 428473) (by norm_num)
theorem B2285261 : Blo 1012602 2285261 := bbase (se 3 (by rfl) ⟨428486, by rfl⟩ : syracuseStep 2285261 = 856973) (by norm_num)
theorem B2285333 : Blo 1012602 2285333 := bbase (se 6 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 2285333 = 107125) (by norm_num)
theorem B2285405 : Blo 1012602 2285405 := bbase (se 3 (by rfl) ⟨428513, by rfl⟩ : syracuseStep 2285405 = 857027) (by norm_num)
theorem B3858293 : Blo 1012602 3858293 := bbase (se 5 (by rfl) ⟨180857, by rfl⟩ : syracuseStep 3858293 = 361715) (by norm_num)
theorem B2285477 : Blo 1012602 2285477 := bbase (se 4 (by rfl) ⟨214263, by rfl⟩ : syracuseStep 2285477 = 428527) (by norm_num)
theorem B2285549 : Blo 1012602 2285549 := bbase (se 3 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 2285549 = 857081) (by norm_num)
theorem B2285621 : Blo 1012602 2285621 := bbase (se 5 (by rfl) ⟨107138, by rfl⟩ : syracuseStep 2285621 = 214277) (by norm_num)
theorem B1925221 : Blo 1012602 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B2285693 : Blo 1012602 2285693 := bbase (se 3 (by rfl) ⟨428567, by rfl⟩ : syracuseStep 2285693 = 857135) (by norm_num)
theorem B5136533 : Blo 1012602 5136533 := bbase (se 6 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 5136533 = 240775) (by norm_num)
theorem B2285765 : Blo 1012602 2285765 := bbase (se 4 (by rfl) ⟨214290, by rfl⟩ : syracuseStep 2285765 = 428581) (by norm_num)
theorem B4940021 : Blo 1012602 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B1925365 : Blo 1012602 1925365 := bbase (se 5 (by rfl) ⟨90251, by rfl⟩ : syracuseStep 1925365 = 180503) (by norm_num)
theorem B2285837 : Blo 1012602 2285837 := bbase (se 3 (by rfl) ⟨428594, by rfl⟩ : syracuseStep 2285837 = 857189) (by norm_num)
theorem B2285909 : Blo 1012602 2285909 := bbase (se 10 (by rfl) ⟨3348, by rfl⟩ : syracuseStep 2285909 = 6697) (by norm_num)
theorem B1925525 : Blo 1012602 1925525 := bbase (se 6 (by rfl) ⟨45129, by rfl⟩ : syracuseStep 1925525 = 90259) (by norm_num)
theorem B2285981 : Blo 1012602 2285981 := bbase (se 3 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 2285981 = 857243) (by norm_num)
theorem B2286053 : Blo 1012602 2286053 := bbase (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) (by norm_num)
theorem B1139197 : Blo 1012602 1139197 := bbase (se 3 (by rfl) ⟨213599, by rfl⟩ : syracuseStep 1139197 = 427199) (by norm_num)
theorem B1139233 : Blo 1012602 1139233 := bbase (se 2 (by rfl) ⟨427212, by rfl⟩ : syracuseStep 1139233 = 854425) (by norm_num)
theorem B1925669 : Blo 1012602 1925669 := bbase (se 4 (by rfl) ⟨180531, by rfl⟩ : syracuseStep 1925669 = 361063) (by norm_num)
theorem B2286125 : Blo 1012602 2286125 := bbase (se 3 (by rfl) ⟨428648, by rfl⟩ : syracuseStep 2286125 = 857297) (by norm_num)
theorem B1139269 : Blo 1012602 1139269 := bbase (se 4 (by rfl) ⟨106806, by rfl⟩ : syracuseStep 1139269 = 213613) (by norm_num)
theorem B1139305 : Blo 1012602 1139305 := bbase (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) (by norm_num)
theorem B2286197 : Blo 1012602 2286197 := bbase (se 5 (by rfl) ⟨107165, by rfl⟩ : syracuseStep 2286197 = 214331) (by norm_num)
theorem B1139341 : Blo 1012602 1139341 := bbase (se 3 (by rfl) ⟨213626, by rfl⟩ : syracuseStep 1139341 = 427253) (by norm_num)
theorem B17588885 : Blo 1012602 17588885 := bbase (se 6 (by rfl) ⟨412239, by rfl⟩ : syracuseStep 17588885 = 824479) (by norm_num)
theorem B1139377 : Blo 1012602 1139377 := bbase (se 2 (by rfl) ⟨427266, by rfl⟩ : syracuseStep 1139377 = 854533) (by norm_num)
theorem B2286269 : Blo 1012602 2286269 := bbase (se 3 (by rfl) ⟨428675, by rfl⟩ : syracuseStep 2286269 = 857351) (by norm_num)
theorem B1368781 : Blo 1012602 1368781 := bbase (se 3 (by rfl) ⟨256646, by rfl⟩ : syracuseStep 1368781 = 513293) (by norm_num)
theorem B1139413 : Blo 1012602 1139413 := bbase (se 7 (by rfl) ⟨13352, by rfl⟩ : syracuseStep 1139413 = 26705) (by norm_num)
theorem B1139449 : Blo 1012602 1139449 := bbase (se 2 (by rfl) ⟨427293, by rfl⟩ : syracuseStep 1139449 = 854587) (by norm_num)
theorem B2286341 : Blo 1012602 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1139485 : Blo 1012602 1139485 := bbase (se 3 (by rfl) ⟨213653, by rfl⟩ : syracuseStep 1139485 = 427307) (by norm_num)
theorem B7824181 : Blo 1012602 7824181 := bbase (se 5 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 7824181 = 733517) (by norm_num)
theorem B1139521 : Blo 1012602 1139521 := bbase (se 2 (by rfl) ⟨427320, by rfl⟩ : syracuseStep 1139521 = 854641) (by norm_num)
theorem B1925957 : Blo 1012602 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B2286413 : Blo 1012602 2286413 := bbase (se 3 (by rfl) ⟨428702, by rfl⟩ : syracuseStep 2286413 = 857405) (by norm_num)
theorem B1139557 : Blo 1012602 1139557 := bbase (se 4 (by rfl) ⟨106833, by rfl⟩ : syracuseStep 1139557 = 213667) (by norm_num)
theorem B1139593 : Blo 1012602 1139593 := bbase (se 2 (by rfl) ⟨427347, by rfl⟩ : syracuseStep 1139593 = 854695) (by norm_num)
theorem B4875157 : Blo 1012602 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B2286485 : Blo 1012602 2286485 := bbase (se 6 (by rfl) ⟨53589, by rfl⟩ : syracuseStep 2286485 = 107179) (by norm_num)
theorem B1139629 : Blo 1012602 1139629 := bbase (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) (by norm_num)
theorem B4940741 : Blo 1012602 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B1139665 : Blo 1012602 1139665 := bbase (se 2 (by rfl) ⟨427374, by rfl⟩ : syracuseStep 1139665 = 854749) (by norm_num)
theorem B1926109 : Blo 1012602 1926109 := bbase (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) (by norm_num)
theorem B2286557 : Blo 1012602 2286557 := bbase (se 3 (by rfl) ⟨428729, by rfl⟩ : syracuseStep 2286557 = 857459) (by norm_num)
theorem B1139701 : Blo 1012602 1139701 := bbase (se 5 (by rfl) ⟨53423, by rfl⟩ : syracuseStep 1139701 = 106847) (by norm_num)
theorem B1139737 : Blo 1012602 1139737 := bbase (se 2 (by rfl) ⟨427401, by rfl⟩ : syracuseStep 1139737 = 854803) (by norm_num)
theorem B2286629 : Blo 1012602 2286629 := bbase (se 4 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 2286629 = 428743) (by norm_num)
theorem B1139773 : Blo 1012602 1139773 := bbase (se 3 (by rfl) ⟨213707, by rfl⟩ : syracuseStep 1139773 = 427415) (by norm_num)
theorem B1139809 : Blo 1012602 1139809 := bbase (se 2 (by rfl) ⟨427428, by rfl⟩ : syracuseStep 1139809 = 854857) (by norm_num)
theorem B2286701 : Blo 1012602 2286701 := bbase (se 3 (by rfl) ⟨428756, by rfl⟩ : syracuseStep 2286701 = 857513) (by norm_num)
theorem B1139845 : Blo 1012602 1139845 := bbase (se 4 (by rfl) ⟨106860, by rfl⟩ : syracuseStep 1139845 = 213721) (by norm_num)
theorem B1139881 : Blo 1012602 1139881 := bbase (se 2 (by rfl) ⟨427455, by rfl⟩ : syracuseStep 1139881 = 854911) (by norm_num)
theorem B2286773 : Blo 1012602 2286773 := bbase (se 5 (by rfl) ⟨107192, by rfl⟩ : syracuseStep 2286773 = 214385) (by norm_num)
theorem B1139917 : Blo 1012602 1139917 := bbase (se 3 (by rfl) ⟨213734, by rfl⟩ : syracuseStep 1139917 = 427469) (by norm_num)
theorem B1172701 : Blo 1012602 1172701 := bbase (se 3 (by rfl) ⟨219881, by rfl⟩ : syracuseStep 1172701 = 439763) (by norm_num)
theorem B1139953 : Blo 1012602 1139953 := bbase (se 2 (by rfl) ⟨427482, by rfl⟩ : syracuseStep 1139953 = 854965) (by norm_num)
theorem B2286845 : Blo 1012602 2286845 := bbase (se 3 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 2286845 = 857567) (by norm_num)
theorem B1926413 : Blo 1012602 1926413 := bbase (se 3 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 1926413 = 722405) (by norm_num)
theorem B1139989 : Blo 1012602 1139989 := bbase (se 6 (by rfl) ⟨26718, by rfl⟩ : syracuseStep 1139989 = 53437) (by norm_num)
theorem B5203253 : Blo 1012602 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B1140025 : Blo 1012602 1140025 := bbase (se 2 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 1140025 = 855019) (by norm_num)
theorem B2286917 : Blo 1012602 2286917 := bbase (se 4 (by rfl) ⟨214398, by rfl⟩ : syracuseStep 2286917 = 428797) (by norm_num)
theorem B1140061 : Blo 1012602 1140061 := bbase (se 3 (by rfl) ⟨213761, by rfl⟩ : syracuseStep 1140061 = 427523) (by norm_num)
theorem B1140097 : Blo 1012602 1140097 := bbase (se 2 (by rfl) ⟨427536, by rfl⟩ : syracuseStep 1140097 = 855073) (by norm_num)
theorem B2286989 : Blo 1012602 2286989 := bbase (se 3 (by rfl) ⟨428810, by rfl⟩ : syracuseStep 2286989 = 857621) (by norm_num)
theorem B1140133 : Blo 1012602 1140133 := bbase (se 4 (by rfl) ⟨106887, by rfl⟩ : syracuseStep 1140133 = 213775) (by norm_num)
theorem B2778533 : Blo 1012602 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B5137829 : Blo 1012602 5137829 := bbase (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) (by norm_num)
theorem B1140169 : Blo 1012602 1140169 := bbase (se 2 (by rfl) ⟨427563, by rfl⟩ : syracuseStep 1140169 = 855127) (by norm_num)
theorem B2287061 : Blo 1012602 2287061 := bbase (se 7 (by rfl) ⟨26801, by rfl⟩ : syracuseStep 2287061 = 53603) (by norm_num)
theorem B1140205 : Blo 1012602 1140205 := bbase (se 3 (by rfl) ⟨213788, by rfl⟩ : syracuseStep 1140205 = 427577) (by norm_num)
theorem B1140241 : Blo 1012602 1140241 := bbase (se 2 (by rfl) ⟨427590, by rfl⟩ : syracuseStep 1140241 = 855181) (by norm_num)
theorem B17360405 : Blo 1012602 17360405 := bbase (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) (by norm_num)
theorem B2287133 : Blo 1012602 2287133 := bbase (se 3 (by rfl) ⟨428837, by rfl⟩ : syracuseStep 2287133 = 857675) (by norm_num)
theorem B1140277 : Blo 1012602 1140277 := bbase (se 5 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 1140277 = 106901) (by norm_num)
theorem B1140313 : Blo 1012602 1140313 := bbase (se 2 (by rfl) ⟨427617, by rfl⟩ : syracuseStep 1140313 = 855235) (by norm_num)
theorem B3663461 : Blo 1012602 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B2287205 : Blo 1012602 2287205 := bbase (se 4 (by rfl) ⟨214425, by rfl⟩ : syracuseStep 2287205 = 428851) (by norm_num)
theorem B1140349 : Blo 1012602 1140349 := bbase (se 3 (by rfl) ⟨213815, by rfl⟩ : syracuseStep 1140349 = 427631) (by norm_num)
theorem B1140385 : Blo 1012602 1140385 := bbase (se 2 (by rfl) ⟨427644, by rfl⟩ : syracuseStep 1140385 = 855289) (by norm_num)
theorem B2287277 : Blo 1012602 2287277 := bbase (se 3 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 2287277 = 857729) (by norm_num)
theorem B1140421 : Blo 1012602 1140421 := bbase (se 4 (by rfl) ⟨106914, by rfl⟩ : syracuseStep 1140421 = 213829) (by norm_num)
theorem B1140457 : Blo 1012602 1140457 := bbase (se 2 (by rfl) ⟨427671, by rfl⟩ : syracuseStep 1140457 = 855343) (by norm_num)
theorem B2287349 : Blo 1012602 2287349 := bbase (se 5 (by rfl) ⟨107219, by rfl⟩ : syracuseStep 2287349 = 214439) (by norm_num)
theorem B2057989 : Blo 1012602 2057989 := bbase (se 4 (by rfl) ⟨192936, by rfl⟩ : syracuseStep 2057989 = 385873) (by norm_num)
theorem B1140493 : Blo 1012602 1140493 := bbase (se 3 (by rfl) ⟨213842, by rfl⟩ : syracuseStep 1140493 = 427685) (by norm_num)
theorem B1140529 : Blo 1012602 1140529 := bbase (se 2 (by rfl) ⟨427698, by rfl⟩ : syracuseStep 1140529 = 855397) (by norm_num)
theorem B1828669 : Blo 1012602 1828669 := bbase (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) (by norm_num)
theorem B1140565 : Blo 1012602 1140565 := bbase (se 9 (by rfl) ⟨3341, by rfl⟩ : syracuseStep 1140565 = 6683) (by norm_num)
theorem B1140601 : Blo 1012602 1140601 := bbase (se 2 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 1140601 = 855451) (by norm_num)
theorem B3663749 : Blo 1012602 3663749 := bbase (se 4 (by rfl) ⟨343476, by rfl⟩ : syracuseStep 3663749 = 686953) (by norm_num)
theorem B1140637 : Blo 1012602 1140637 := bbase (se 3 (by rfl) ⟨213869, by rfl⟩ : syracuseStep 1140637 = 427739) (by norm_num)
theorem B1140673 : Blo 1012602 1140673 := bbase (se 2 (by rfl) ⟨427752, by rfl⟩ : syracuseStep 1140673 = 855505) (by norm_num)
theorem B1140709 : Blo 1012602 1140709 := bbase (se 4 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 1140709 = 213883) (by norm_num)
theorem B1927165 : Blo 1012602 1927165 := bbase (se 3 (by rfl) ⟨361343, by rfl⟩ : syracuseStep 1927165 = 722687) (by norm_num)
theorem B1140745 : Blo 1012602 1140745 := bbase (se 2 (by rfl) ⟨427779, by rfl⟩ : syracuseStep 1140745 = 855559) (by norm_num)
theorem B1140781 : Blo 1012602 1140781 := bbase (se 3 (by rfl) ⟨213896, by rfl⟩ : syracuseStep 1140781 = 427793) (by norm_num)
theorem B1140817 : Blo 1012602 1140817 := bbase (se 2 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 1140817 = 855613) (by norm_num)
theorem B1140853 : Blo 1012602 1140853 := bbase (se 5 (by rfl) ⟨53477, by rfl⟩ : syracuseStep 1140853 = 106955) (by norm_num)
theorem B1927309 : Blo 1012602 1927309 := bbase (se 3 (by rfl) ⟨361370, by rfl⟩ : syracuseStep 1927309 = 722741) (by norm_num)
theorem B1140889 : Blo 1012602 1140889 := bbase (se 2 (by rfl) ⟨427833, by rfl⟩ : syracuseStep 1140889 = 855667) (by norm_num)
theorem B1140925 : Blo 1012602 1140925 := bbase (se 3 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 1140925 = 427847) (by norm_num)
theorem B1140961 : Blo 1012602 1140961 := bbase (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) (by norm_num)
theorem B1140997 : Blo 1012602 1140997 := bbase (se 4 (by rfl) ⟨106968, by rfl⟩ : syracuseStep 1140997 = 213937) (by norm_num)
theorem B2058509 : Blo 1012602 2058509 := bbase (se 3 (by rfl) ⟨385970, by rfl⟩ : syracuseStep 2058509 = 771941) (by norm_num)
theorem B1141033 : Blo 1012602 1141033 := bbase (se 2 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 1141033 = 855775) (by norm_num)
theorem B1927469 : Blo 1012602 1927469 := bbase (se 3 (by rfl) ⟨361400, by rfl⟩ : syracuseStep 1927469 = 722801) (by norm_num)
theorem B1141069 : Blo 1012602 1141069 := bbase (se 3 (by rfl) ⟨213950, by rfl⟩ : syracuseStep 1141069 = 427901) (by norm_num)
theorem B1141105 : Blo 1012602 1141105 := bbase (se 2 (by rfl) ⟨427914, by rfl⟩ : syracuseStep 1141105 = 855829) (by norm_num)
theorem B1141141 : Blo 1012602 1141141 := bbase (se 6 (by rfl) ⟨26745, by rfl⟩ : syracuseStep 1141141 = 53491) (by norm_num)
theorem B1141177 : Blo 1012602 1141177 := bbase (se 2 (by rfl) ⟨427941, by rfl⟩ : syracuseStep 1141177 = 855883) (by norm_num)
theorem B1927613 : Blo 1012602 1927613 := bbase (se 3 (by rfl) ⟨361427, by rfl⟩ : syracuseStep 1927613 = 722855) (by norm_num)
theorem B1141213 : Blo 1012602 1141213 := bbase (se 3 (by rfl) ⟨213977, by rfl⟩ : syracuseStep 1141213 = 427955) (by norm_num)
theorem B7694837 : Blo 1012602 7694837 := bbase (se 5 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 7694837 = 721391) (by norm_num)
theorem B6941173 : Blo 1012602 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B1141249 : Blo 1012602 1141249 := bbase (se 2 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 1141249 = 855937) (by norm_num)
theorem B1141285 : Blo 1012602 1141285 := bbase (se 4 (by rfl) ⟨106995, by rfl⟩ : syracuseStep 1141285 = 213991) (by norm_num)
theorem B1141321 : Blo 1012602 1141321 := bbase (se 2 (by rfl) ⟨427995, by rfl⟩ : syracuseStep 1141321 = 855991) (by norm_num)
theorem B1141357 : Blo 1012602 1141357 := bbase (se 3 (by rfl) ⟨214004, by rfl⟩ : syracuseStep 1141357 = 428009) (by norm_num)
theorem B1141393 : Blo 1012602 1141393 := bbase (se 2 (by rfl) ⟨428022, by rfl⟩ : syracuseStep 1141393 = 856045) (by norm_num)
theorem B6941333 : Blo 1012602 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B1141429 : Blo 1012602 1141429 := bbase (se 5 (by rfl) ⟨53504, by rfl⟩ : syracuseStep 1141429 = 107009) (by norm_num)
theorem B5139125 : Blo 1012602 5139125 := bbase (se 5 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 5139125 = 481793) (by norm_num)
theorem B1141465 : Blo 1012602 1141465 := bbase (se 2 (by rfl) ⟨428049, by rfl⟩ : syracuseStep 1141465 = 856099) (by norm_num)
theorem B1927901 : Blo 1012602 1927901 := bbase (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) (by norm_num)
theorem B1141501 : Blo 1012602 1141501 := bbase (se 3 (by rfl) ⟨214031, by rfl⟩ : syracuseStep 1141501 = 428063) (by norm_num)
theorem B1141537 : Blo 1012602 1141537 := bbase (se 2 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 1141537 = 856153) (by norm_num)
theorem B1141573 : Blo 1012602 1141573 := bbase (se 4 (by rfl) ⟨107022, by rfl⟩ : syracuseStep 1141573 = 214045) (by norm_num)
theorem B1141609 : Blo 1012602 1141609 := bbase (se 2 (by rfl) ⟨428103, by rfl⟩ : syracuseStep 1141609 = 856207) (by norm_num)
theorem B1928053 : Blo 1012602 1928053 := bbase (se 5 (by rfl) ⟨90377, by rfl⟩ : syracuseStep 1928053 = 180755) (by norm_num)
theorem B2059141 : Blo 1012602 2059141 := bbase (se 4 (by rfl) ⟨193044, by rfl⟩ : syracuseStep 2059141 = 386089) (by norm_num)
theorem B1141645 : Blo 1012602 1141645 := bbase (se 3 (by rfl) ⟨214058, by rfl⟩ : syracuseStep 1141645 = 428117) (by norm_num)
theorem B1141681 : Blo 1012602 1141681 := bbase (se 2 (by rfl) ⟨428130, by rfl⟩ : syracuseStep 1141681 = 856261) (by norm_num)
theorem B1141717 : Blo 1012602 1141717 := bbase (se 7 (by rfl) ⟨13379, by rfl⟩ : syracuseStep 1141717 = 26759) (by norm_num)
theorem B1141753 : Blo 1012602 1141753 := bbase (se 2 (by rfl) ⟨428157, by rfl⟩ : syracuseStep 1141753 = 856315) (by norm_num)
theorem B1829885 : Blo 1012602 1829885 := bbase (se 3 (by rfl) ⟨343103, by rfl⟩ : syracuseStep 1829885 = 686207) (by norm_num)
theorem B1141789 : Blo 1012602 1141789 := bbase (se 3 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 1141789 = 428171) (by norm_num)
theorem B1141825 : Blo 1012602 1141825 := bbase (se 2 (by rfl) ⟨428184, by rfl⟩ : syracuseStep 1141825 = 856369) (by norm_num)
theorem B1141861 : Blo 1012602 1141861 := bbase (se 4 (by rfl) ⟨107049, by rfl⟩ : syracuseStep 1141861 = 214099) (by norm_num)
theorem B1141897 : Blo 1012602 1141897 := bbase (se 2 (by rfl) ⟨428211, by rfl⟩ : syracuseStep 1141897 = 856423) (by norm_num)
theorem B1830053 : Blo 1012602 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B1928357 : Blo 1012602 1928357 := bbase (se 4 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 1928357 = 361567) (by norm_num)
theorem B1141933 : Blo 1012602 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B1141969 : Blo 1012602 1141969 := bbase (se 2 (by rfl) ⟨428238, by rfl⟩ : syracuseStep 1141969 = 856477) (by norm_num)
theorem B1142005 : Blo 1012602 1142005 := bbase (se 5 (by rfl) ⟨53531, by rfl⟩ : syracuseStep 1142005 = 107063) (by norm_num)
theorem B1142041 : Blo 1012602 1142041 := bbase (se 2 (by rfl) ⟨428265, by rfl⟩ : syracuseStep 1142041 = 856531) (by norm_num)
theorem B1142077 : Blo 1012602 1142077 := bbase (se 3 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 1142077 = 428279) (by norm_num)
theorem B1142113 : Blo 1012602 1142113 := bbase (se 2 (by rfl) ⟨428292, by rfl⟩ : syracuseStep 1142113 = 856585) (by norm_num)
theorem B1142149 : Blo 1012602 1142149 := bbase (se 4 (by rfl) ⟨107076, by rfl⟩ : syracuseStep 1142149 = 214153) (by norm_num)
theorem B1142185 : Blo 1012602 1142185 := bbase (se 2 (by rfl) ⟨428319, by rfl⟩ : syracuseStep 1142185 = 856639) (by norm_num)
theorem B1142221 : Blo 1012602 1142221 := bbase (se 3 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 1142221 = 428333) (by norm_num)
theorem B1142257 : Blo 1012602 1142257 := bbase (se 2 (by rfl) ⟨428346, by rfl⟩ : syracuseStep 1142257 = 856693) (by norm_num)
theorem B1142293 : Blo 1012602 1142293 := bbase (se 6 (by rfl) ⟨26772, by rfl⟩ : syracuseStep 1142293 = 53545) (by norm_num)
theorem B1142329 : Blo 1012602 1142329 := bbase (se 2 (by rfl) ⟨428373, by rfl⟩ : syracuseStep 1142329 = 856747) (by norm_num)
theorem B1142365 : Blo 1012602 1142365 := bbase (se 3 (by rfl) ⟨214193, by rfl⟩ : syracuseStep 1142365 = 428387) (by norm_num)
theorem B1142401 : Blo 1012602 1142401 := bbase (se 2 (by rfl) ⟨428400, by rfl⟩ : syracuseStep 1142401 = 856801) (by norm_num)
theorem B1142437 : Blo 1012602 1142437 := bbase (se 4 (by rfl) ⟨107103, by rfl⟩ : syracuseStep 1142437 = 214207) (by norm_num)
theorem B1142473 : Blo 1012602 1142473 := bbase (se 2 (by rfl) ⟨428427, by rfl⟩ : syracuseStep 1142473 = 856855) (by norm_num)
theorem B1142509 : Blo 1012602 1142509 := bbase (se 3 (by rfl) ⟨214220, by rfl⟩ : syracuseStep 1142509 = 428441) (by norm_num)
theorem B1142545 : Blo 1012602 1142545 := bbase (se 2 (by rfl) ⟨428454, by rfl⟩ : syracuseStep 1142545 = 856909) (by norm_num)
theorem B1142581 : Blo 1012602 1142581 := bbase (se 5 (by rfl) ⟨53558, by rfl⟩ : syracuseStep 1142581 = 107117) (by norm_num)
theorem B1142617 : Blo 1012602 1142617 := bbase (se 2 (by rfl) ⟨428481, by rfl⟩ : syracuseStep 1142617 = 856963) (by norm_num)
theorem B1142653 : Blo 1012602 1142653 := bbase (se 3 (by rfl) ⟨214247, by rfl⟩ : syracuseStep 1142653 = 428495) (by norm_num)
theorem B1929109 : Blo 1012602 1929109 := bbase (se 6 (by rfl) ⟨45213, by rfl⟩ : syracuseStep 1929109 = 90427) (by norm_num)
theorem B1142689 : Blo 1012602 1142689 := bbase (se 2 (by rfl) ⟨428508, by rfl⟩ : syracuseStep 1142689 = 857017) (by norm_num)
theorem B5140421 : Blo 1012602 5140421 := bbase (se 4 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 5140421 = 963829) (by norm_num)
theorem B1142725 : Blo 1012602 1142725 := bbase (se 4 (by rfl) ⟨107130, by rfl⟩ : syracuseStep 1142725 = 214261) (by norm_num)
theorem B1142761 : Blo 1012602 1142761 := bbase (se 2 (by rfl) ⟨428535, by rfl⟩ : syracuseStep 1142761 = 857071) (by norm_num)
theorem B1142797 : Blo 1012602 1142797 := bbase (se 3 (by rfl) ⟨214274, by rfl⟩ : syracuseStep 1142797 = 428549) (by norm_num)
theorem B2060309 : Blo 1012602 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1929253 : Blo 1012602 1929253 := bbase (se 4 (by rfl) ⟨180867, by rfl⟩ : syracuseStep 1929253 = 361735) (by norm_num)
theorem B1142833 : Blo 1012602 1142833 := bbase (se 2 (by rfl) ⟨428562, by rfl⟩ : syracuseStep 1142833 = 857125) (by norm_num)
theorem B1142869 : Blo 1012602 1142869 := bbase (se 8 (by rfl) ⟨6696, by rfl⟩ : syracuseStep 1142869 = 13393) (by norm_num)
theorem B1142905 : Blo 1012602 1142905 := bbase (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) (by norm_num)
theorem B1142941 : Blo 1012602 1142941 := bbase (se 3 (by rfl) ⟨214301, by rfl⟩ : syracuseStep 1142941 = 428603) (by norm_num)
theorem B1142977 : Blo 1012602 1142977 := bbase (se 2 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 1142977 = 857233) (by norm_num)
theorem B1929413 : Blo 1012602 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B1143013 : Blo 1012602 1143013 := bbase (se 4 (by rfl) ⟨107157, by rfl⟩ : syracuseStep 1143013 = 214315) (by norm_num)
theorem B1143049 : Blo 1012602 1143049 := bbase (se 2 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 1143049 = 857287) (by norm_num)
theorem B1143085 : Blo 1012602 1143085 := bbase (se 3 (by rfl) ⟨214328, by rfl⟩ : syracuseStep 1143085 = 428657) (by norm_num)
theorem B1143121 : Blo 1012602 1143121 := bbase (se 2 (by rfl) ⟨428670, by rfl⟩ : syracuseStep 1143121 = 857341) (by norm_num)
theorem B1929557 : Blo 1012602 1929557 := bbase (se 10 (by rfl) ⟨2826, by rfl⟩ : syracuseStep 1929557 = 5653) (by norm_num)
theorem B1143157 : Blo 1012602 1143157 := bbase (se 5 (by rfl) ⟨53585, by rfl⟩ : syracuseStep 1143157 = 107171) (by norm_num)
theorem B1143193 : Blo 1012602 1143193 := bbase (se 2 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 1143193 = 857395) (by norm_num)
theorem B1143229 : Blo 1012602 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B1143265 : Blo 1012602 1143265 := bbase (se 2 (by rfl) ⟨428724, by rfl⟩ : syracuseStep 1143265 = 857449) (by norm_num)
theorem B1143301 : Blo 1012602 1143301 := bbase (se 4 (by rfl) ⟨107184, by rfl⟩ : syracuseStep 1143301 = 214369) (by norm_num)
theorem B1143337 : Blo 1012602 1143337 := bbase (se 2 (by rfl) ⟨428751, by rfl⟩ : syracuseStep 1143337 = 857503) (by norm_num)
theorem B1372717 : Blo 1012602 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1143373 : Blo 1012602 1143373 := bbase (se 3 (by rfl) ⟨214382, by rfl⟩ : syracuseStep 1143373 = 428765) (by norm_num)
theorem B1143409 : Blo 1012602 1143409 := bbase (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) (by norm_num)
theorem B1929845 : Blo 1012602 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B1143445 : Blo 1012602 1143445 := bbase (se 6 (by rfl) ⟨26799, by rfl⟩ : syracuseStep 1143445 = 53599) (by norm_num)
theorem B1143481 : Blo 1012602 1143481 := bbase (se 2 (by rfl) ⟨428805, by rfl⟩ : syracuseStep 1143481 = 857611) (by norm_num)
theorem B4879061 : Blo 1012602 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B1143517 : Blo 1012602 1143517 := bbase (se 3 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 1143517 = 428819) (by norm_num)
theorem B1143553 : Blo 1012602 1143553 := bbase (se 2 (by rfl) ⟨428832, by rfl⟩ : syracuseStep 1143553 = 857665) (by norm_num)
theorem B1372933 : Blo 1012602 1372933 := bbase (se 4 (by rfl) ⟨128712, by rfl⟩ : syracuseStep 1372933 = 257425) (by norm_num)
theorem B1143589 : Blo 1012602 1143589 := bbase (se 4 (by rfl) ⟨107211, by rfl⟩ : syracuseStep 1143589 = 214423) (by norm_num)
theorem B1143625 : Blo 1012602 1143625 := bbase (se 2 (by rfl) ⟨428859, by rfl⟩ : syracuseStep 1143625 = 857719) (by norm_num)
theorem B1143661 : Blo 1012602 1143661 := bbase (se 3 (by rfl) ⟨214436, by rfl⟩ : syracuseStep 1143661 = 428873) (by norm_num)
theorem B1373117 : Blo 1012602 1373117 := bbase (se 3 (by rfl) ⟨257459, by rfl⟩ : syracuseStep 1373117 = 514919) (by norm_num)
theorem B5141717 : Blo 1012602 5141717 := bbase (se 7 (by rfl) ⟨60254, by rfl⟩ : syracuseStep 5141717 = 120509) (by norm_num)
theorem B5862709 : Blo 1012602 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B17593685 : Blo 1012602 17593685 := bbase (se 13 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 17593685 = 6443) (by norm_num)
theorem B1734061 : Blo 1012602 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B4388357 : Blo 1012602 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B5143013 : Blo 1012602 5143013 := bbase (se 4 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 5143013 = 964315) (by norm_num)
theorem B4881077 : Blo 1012602 4881077 := bbase (se 5 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 4881077 = 457601) (by norm_num)
theorem B28113749 : Blo 1012602 28113749 := bbase (se 9 (by rfl) ⟨82364, by rfl⟩ : syracuseStep 28113749 = 164729) (by norm_num)
theorem B1736005 : Blo 1012602 1736005 := bbase (se 4 (by rfl) ⟨162750, by rfl⟩ : syracuseStep 1736005 = 325501) (by norm_num)
theorem B4881829 : Blo 1012602 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B1736245 : Blo 1012602 1736245 := bbase (se 5 (by rfl) ⟨81386, by rfl⟩ : syracuseStep 1736245 = 162773) (by norm_num)
theorem B5144309 : Blo 1012602 5144309 := bbase (se 5 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 5144309 = 482279) (by norm_num)
theorem B1539989 : Blo 1012602 1539989 := bbase (se 6 (by rfl) ⟨36093, by rfl⟩ : syracuseStep 1539989 = 72187) (by norm_num)
theorem B1015811 : Blo 1012602 1015811 := bstep (se 1 (by rfl) ⟨761858, by rfl⟩ : syracuseStep 1015811 = 1523717) B1523717
theorem B1015827 : Blo 1012602 1015827 := bstep (se 1 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 1015827 = 1523741) B1523741
theorem B1015843 : Blo 1012602 1015843 := bstep (se 1 (by rfl) ⟨761882, by rfl⟩ : syracuseStep 1015843 = 1523765) B1523765
theorem B1015859 : Blo 1012602 1015859 := bstep (se 1 (by rfl) ⟨761894, by rfl⟩ : syracuseStep 1015859 = 1523789) B1523789
theorem B1015875 : Blo 1012602 1015875 := bstep (se 1 (by rfl) ⟨761906, by rfl⟩ : syracuseStep 1015875 = 1523813) B1523813
theorem B1015891 : Blo 1012602 1015891 := bstep (se 1 (by rfl) ⟨761918, by rfl⟩ : syracuseStep 1015891 = 1523837) B1523837
theorem B1015907 : Blo 1012602 1015907 := bstep (se 1 (by rfl) ⟨761930, by rfl⟩ : syracuseStep 1015907 = 1523861) B1523861
theorem B1015923 : Blo 1012602 1015923 := bstep (se 1 (by rfl) ⟨761942, by rfl⟩ : syracuseStep 1015923 = 1523885) B1523885
theorem B1015939 : Blo 1012602 1015939 := bstep (se 1 (by rfl) ⟨761954, by rfl⟩ : syracuseStep 1015939 = 1523909) B1523909
theorem B5767301 : Blo 1012602 5767301 := bstep (se 4 (by rfl) ⟨540684, by rfl⟩ : syracuseStep 5767301 = 1081369) B1081369
theorem B1015955 : Blo 1012602 1015955 := bstep (se 1 (by rfl) ⟨761966, by rfl⟩ : syracuseStep 1015955 = 1523933) B1523933
theorem B1015971 : Blo 1012602 1015971 := bstep (se 1 (by rfl) ⟨761978, by rfl⟩ : syracuseStep 1015971 = 1523957) B1523957
theorem B1081523 : Blo 1012602 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B1015987 : Blo 1012602 1015987 := bstep (se 1 (by rfl) ⟨761990, by rfl⟩ : syracuseStep 1015987 = 1523981) B1523981
theorem B1016003 : Blo 1012602 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B1016019 : Blo 1012602 1016019 := bstep (se 1 (by rfl) ⟨762014, by rfl⟩ : syracuseStep 1016019 = 1524029) B1524029
theorem B1016035 : Blo 1012602 1016035 := bstep (se 1 (by rfl) ⟨762026, by rfl⟩ : syracuseStep 1016035 = 1524053) B1524053
theorem B1016051 : Blo 1012602 1016051 := bstep (se 1 (by rfl) ⟨762038, by rfl⟩ : syracuseStep 1016051 = 1524077) B1524077
theorem B1016067 : Blo 1012602 1016067 := bstep (se 1 (by rfl) ⟨762050, by rfl⟩ : syracuseStep 1016067 = 1524101) B1524101
theorem B1442065 : Blo 1012602 1442065 := bstep (se 2 (by rfl) ⟨540774, by rfl⟩ : syracuseStep 1442065 = 1081549) B1081549
theorem B1016083 : Blo 1012602 1016083 := bstep (se 1 (by rfl) ⟨762062, by rfl⟩ : syracuseStep 1016083 = 1524125) B1524125
theorem B1016099 : Blo 1012602 1016099 := bstep (se 1 (by rfl) ⟨762074, by rfl⟩ : syracuseStep 1016099 = 1524149) B1524149
theorem B1016115 : Blo 1012602 1016115 := bstep (se 1 (by rfl) ⟨762086, by rfl⟩ : syracuseStep 1016115 = 1524173) B1524173
theorem B1016131 : Blo 1012602 1016131 := bstep (se 1 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 1016131 = 1524197) B1524197
theorem B1016147 : Blo 1012602 1016147 := bstep (se 1 (by rfl) ⟨762110, by rfl⟩ : syracuseStep 1016147 = 1524221) B1524221
theorem B6488419 : Blo 1012602 6488419 := bstep (se 1 (by rfl) ⟨4866314, by rfl⟩ : syracuseStep 6488419 = 9732629) B9732629
theorem B1016163 : Blo 1012602 1016163 := bstep (se 1 (by rfl) ⟨762122, by rfl⟩ : syracuseStep 1016163 = 1524245) B1524245
theorem B1016179 : Blo 1012602 1016179 := bstep (se 1 (by rfl) ⟨762134, by rfl⟩ : syracuseStep 1016179 = 1524269) B1524269
theorem B1016195 : Blo 1012602 1016195 := bstep (se 1 (by rfl) ⟨762146, by rfl⟩ : syracuseStep 1016195 = 1524293) B1524293
theorem B1016211 : Blo 1012602 1016211 := bstep (se 1 (by rfl) ⟨762158, by rfl⟩ : syracuseStep 1016211 = 1524317) B1524317
theorem B1016227 : Blo 1012602 1016227 := bstep (se 1 (by rfl) ⟨762170, by rfl⟩ : syracuseStep 1016227 = 1524341) B1524341
theorem B1016243 : Blo 1012602 1016243 := bstep (se 1 (by rfl) ⟨762182, by rfl⟩ : syracuseStep 1016243 = 1524365) B1524365
theorem B1016259 : Blo 1012602 1016259 := bstep (se 1 (by rfl) ⟨762194, by rfl⟩ : syracuseStep 1016259 = 1524389) B1524389
theorem B9273797 : Blo 1012602 9273797 := bstep (se 4 (by rfl) ⟨869418, by rfl⟩ : syracuseStep 9273797 = 1738837) B1738837
theorem B1540561 : Blo 1012602 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B1016275 : Blo 1012602 1016275 := bstep (se 1 (by rfl) ⟨762206, by rfl⟩ : syracuseStep 1016275 = 1524413) B1524413
theorem B1016291 : Blo 1012602 1016291 := bstep (se 1 (by rfl) ⟨762218, by rfl⟩ : syracuseStep 1016291 = 1524437) B1524437
theorem B1016307 : Blo 1012602 1016307 := bstep (se 1 (by rfl) ⟨762230, by rfl⟩ : syracuseStep 1016307 = 1524461) B1524461
theorem B1016323 : Blo 1012602 1016323 := bstep (se 1 (by rfl) ⟨762242, by rfl⟩ : syracuseStep 1016323 = 1524485) B1524485
theorem B1016339 : Blo 1012602 1016339 := bstep (se 1 (by rfl) ⟨762254, by rfl⟩ : syracuseStep 1016339 = 1524509) B1524509
theorem B1016355 : Blo 1012602 1016355 := bstep (se 1 (by rfl) ⟨762266, by rfl⟩ : syracuseStep 1016355 = 1524533) B1524533
theorem B1016371 : Blo 1012602 1016371 := bstep (se 1 (by rfl) ⟨762278, by rfl⟩ : syracuseStep 1016371 = 1524557) B1524557
theorem B1016387 : Blo 1012602 1016387 := bstep (se 1 (by rfl) ⟨762290, by rfl⟩ : syracuseStep 1016387 = 1524581) B1524581
theorem B5767757 : Blo 1012602 5767757 := bstep (se 3 (by rfl) ⟨1081454, by rfl⟩ : syracuseStep 5767757 = 2162909) B2162909
theorem B1016403 : Blo 1012602 1016403 := bstep (se 1 (by rfl) ⟨762302, by rfl⟩ : syracuseStep 1016403 = 1524605) B1524605
theorem B1016419 : Blo 1012602 1016419 := bstep (se 1 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 1016419 = 1524629) B1524629
theorem B1016435 : Blo 1012602 1016435 := bstep (se 1 (by rfl) ⟨762326, by rfl⟩ : syracuseStep 1016435 = 1524653) B1524653
theorem B1016451 : Blo 1012602 1016451 := bstep (se 1 (by rfl) ⟨762338, by rfl⟩ : syracuseStep 1016451 = 1524677) B1524677
theorem B1016467 : Blo 1012602 1016467 := bstep (se 1 (by rfl) ⟨762350, by rfl⟩ : syracuseStep 1016467 = 1524701) B1524701
theorem B1016483 : Blo 1012602 1016483 := bstep (se 1 (by rfl) ⟨762362, by rfl⟩ : syracuseStep 1016483 = 1524725) B1524725
theorem B1016499 : Blo 1012602 1016499 := bstep (se 1 (by rfl) ⟨762374, by rfl⟩ : syracuseStep 1016499 = 1524749) B1524749
theorem B1016515 : Blo 1012602 1016515 := bstep (se 1 (by rfl) ⟨762386, by rfl⟩ : syracuseStep 1016515 = 1524773) B1524773
theorem B1016531 : Blo 1012602 1016531 := bstep (se 1 (by rfl) ⟨762398, by rfl⟩ : syracuseStep 1016531 = 1524797) B1524797
theorem B1016547 : Blo 1012602 1016547 := bstep (se 1 (by rfl) ⟨762410, by rfl⟩ : syracuseStep 1016547 = 1524821) B1524821
theorem B1016563 : Blo 1012602 1016563 := bstep (se 1 (by rfl) ⟨762422, by rfl⟩ : syracuseStep 1016563 = 1524845) B1524845
theorem B1016579 : Blo 1012602 1016579 := bstep (se 1 (by rfl) ⟨762434, by rfl⟩ : syracuseStep 1016579 = 1524869) B1524869
theorem B2884369 : Blo 1012602 2884369 := bstep (se 2 (by rfl) ⟨1081638, by rfl⟩ : syracuseStep 2884369 = 2163277) B2163277
theorem B1016595 : Blo 1012602 1016595 := bstep (se 1 (by rfl) ⟨762446, by rfl⟩ : syracuseStep 1016595 = 1524893) B1524893
theorem B1442657 : Blo 1012602 1442657 := bstep (se 2 (by rfl) ⟨540996, by rfl⟩ : syracuseStep 1442657 = 1081993) B1081993
theorem B5145443 : Blo 1012602 5145443 := bstep (se 1 (by rfl) ⟨3859082, by rfl⟩ : syracuseStep 5145443 = 7718165) B7718165
theorem B3081073 : Blo 1012602 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B2884643 : Blo 1012602 2884643 := bstep (se 1 (by rfl) ⟨2163482, by rfl⟩ : syracuseStep 2884643 = 4326965) B4326965
theorem B1082531 : Blo 1012602 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B4326605 : Blo 1012602 4326605 := bstep (se 3 (by rfl) ⟨811238, by rfl⟩ : syracuseStep 4326605 = 1622477) B1622477
theorem B2884835 : Blo 1012602 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B1443187 : Blo 1012602 1443187 := bstep (se 1 (by rfl) ⟨1082390, by rfl⟩ : syracuseStep 1443187 = 2164781) B2164781
theorem B9733517 : Blo 1012602 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B2164259 : Blo 1012602 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B6489649 : Blo 1012602 6489649 := bstep (se 2 (by rfl) ⟨2433618, by rfl⟩ : syracuseStep 6489649 = 4867237) B4867237
theorem B4687409 : Blo 1012602 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B3245645 : Blo 1012602 3245645 := bstep (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) B1217117
theorem B1541729 : Blo 1012602 1541729 := bstep (se 2 (by rfl) ⟨578148, by rfl⟩ : syracuseStep 1541729 = 1156297) B1156297
theorem B3475075 : Blo 1012602 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B5146253 : Blo 1012602 5146253 := bstep (se 3 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 5146253 = 1929845) B1929845
theorem B6588067 : Blo 1012602 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B1443523 : Blo 1012602 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B2885645 : Blo 1012602 2885645 := bstep (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) B1082117
theorem B2885827 : Blo 1012602 2885827 := bstep (se 1 (by rfl) ⟨2164370, by rfl⟩ : syracuseStep 2885827 = 4328741) B4328741
theorem B1444081 : Blo 1012602 1444081 := bstep (se 2 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 1444081 = 1083061) B1083061
theorem B1444115 : Blo 1012602 1444115 := bstep (se 1 (by rfl) ⟨1083086, by rfl⟩ : syracuseStep 1444115 = 2166173) B2166173
theorem B2165123 : Blo 1012602 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B2165233 : Blo 1012602 2165233 := bstep (se 2 (by rfl) ⟨811962, by rfl⟩ : syracuseStep 2165233 = 1623925) B1623925
theorem B9767537 : Blo 1012602 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B2886317 : Blo 1012602 2886317 := bstep (se 3 (by rfl) ⟨541184, by rfl⟩ : syracuseStep 2886317 = 1082369) B1082369
theorem B1084099 : Blo 1012602 1084099 := bstep (se 1 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 1084099 = 1626149) B1626149
theorem B1444673 : Blo 1012602 1444673 := bstep (se 2 (by rfl) ⟨541752, by rfl⟩ : syracuseStep 1444673 = 1083505) B1083505
theorem B1543043 : Blo 1012602 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B1444753 : Blo 1012602 1444753 := bstep (se 2 (by rfl) ⟨541782, by rfl⟩ : syracuseStep 1444753 = 1083565) B1083565
theorem B1543139 : Blo 1012602 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B3247235 : Blo 1012602 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B1084547 : Blo 1012602 1084547 := bstep (se 1 (by rfl) ⟨813410, by rfl⟩ : syracuseStep 1084547 = 1626821) B1626821
theorem B8326385 : Blo 1012602 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B5770673 : Blo 1012602 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B1281683 : Blo 1012602 1281683 := bstep (se 1 (by rfl) ⟨961262, by rfl⟩ : syracuseStep 1281683 = 1922525) B1922525
theorem B1445539 : Blo 1012602 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B2887501 : Blo 1012602 2887501 := bstep (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) B1082813
theorem B1446017 : Blo 1012602 1446017 := bstep (se 2 (by rfl) ⟨542256, by rfl⟩ : syracuseStep 1446017 = 1084513) B1084513
theorem B14651533 : Blo 1012602 14651533 := bstep (se 3 (by rfl) ⟨2747162, by rfl⟩ : syracuseStep 14651533 = 5494325) B5494325
theorem B4329713 : Blo 1012602 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B1446131 : Blo 1012602 1446131 := bstep (se 1 (by rfl) ⟨1084598, by rfl⟩ : syracuseStep 1446131 = 2169197) B2169197
theorem B1446211 : Blo 1012602 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B1282387 : Blo 1012602 1282387 := bstep (se 1 (by rfl) ⟨961790, by rfl⟩ : syracuseStep 1282387 = 1923581) B1923581
theorem B3248515 : Blo 1012602 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B1282483 : Blo 1012602 1282483 := bstep (se 1 (by rfl) ⟨961862, by rfl⟩ : syracuseStep 1282483 = 1923725) B1923725
theorem B1216963 : Blo 1012602 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B2167249 : Blo 1012602 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B3248849 : Blo 1012602 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B1708769 : Blo 1012602 1708769 := bstep (se 2 (by rfl) ⟨640788, by rfl⟩ : syracuseStep 1708769 = 1281577) B1281577
theorem B1708897 : Blo 1012602 1708897 := bstep (se 2 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 1708897 = 1281673) B1281673
theorem B5772131 : Blo 1012602 5772131 := bstep (se 1 (by rfl) ⟨4329098, by rfl⟩ : syracuseStep 5772131 = 8658197) B8658197
theorem B2167651 : Blo 1012602 2167651 := bstep (se 1 (by rfl) ⟨1625738, by rfl⟩ : syracuseStep 2167651 = 3251477) B3251477
theorem B2888561 : Blo 1012602 2888561 := bstep (se 2 (by rfl) ⟨1083210, by rfl⟩ : syracuseStep 2888561 = 2166421) B2166421
theorem B1446769 : Blo 1012602 1446769 := bstep (se 2 (by rfl) ⟨542538, by rfl⟩ : syracuseStep 1446769 = 1085077) B1085077
theorem B1708931 : Blo 1012602 1708931 := bstep (se 1 (by rfl) ⟨1281698, by rfl⟩ : syracuseStep 1708931 = 2563397) B2563397
theorem B4330381 : Blo 1012602 4330381 := bstep (se 3 (by rfl) ⟨811946, by rfl⟩ : syracuseStep 4330381 = 1623893) B1623893
theorem B1282979 : Blo 1012602 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B1709059 : Blo 1012602 1709059 := bstep (se 1 (by rfl) ⟨1281794, by rfl⟩ : syracuseStep 1709059 = 2563589) B2563589
theorem B9769997 : Blo 1012602 9769997 := bstep (se 3 (by rfl) ⟨1831874, by rfl⟩ : syracuseStep 9769997 = 3663749) B3663749
theorem B1709201 : Blo 1012602 1709201 := bstep (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) B1281901
theorem B6493445 : Blo 1012602 6493445 := bstep (se 4 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 6493445 = 1217521) B1217521
theorem B1709329 : Blo 1012602 1709329 := bstep (se 2 (by rfl) ⟨640998, by rfl⟩ : syracuseStep 1709329 = 1281997) B1281997
theorem B1709363 : Blo 1012602 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B7804259 : Blo 1012602 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B1709491 : Blo 1012602 1709491 := bstep (se 1 (by rfl) ⟨1282118, by rfl⟩ : syracuseStep 1709491 = 2564237) B2564237
theorem B4330979 : Blo 1012602 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B2889233 : Blo 1012602 2889233 := bstep (se 2 (by rfl) ⟨1083462, by rfl⟩ : syracuseStep 2889233 = 2166925) B2166925
theorem B1709633 : Blo 1012602 1709633 := bstep (se 2 (by rfl) ⟨641112, by rfl⟩ : syracuseStep 1709633 = 1282225) B1282225
theorem B1283683 : Blo 1012602 1283683 := bstep (se 1 (by rfl) ⟨962762, by rfl⟩ : syracuseStep 1283683 = 1925525) B1925525
theorem B1709761 : Blo 1012602 1709761 := bstep (se 2 (by rfl) ⟨641160, by rfl⟩ : syracuseStep 1709761 = 1282321) B1282321
theorem B1283779 : Blo 1012602 1283779 := bstep (se 1 (by rfl) ⟨962834, by rfl⟩ : syracuseStep 1283779 = 1925669) B1925669
theorem B1709795 : Blo 1012602 1709795 := bstep (se 1 (by rfl) ⟨1282346, by rfl⟩ : syracuseStep 1709795 = 2564693) B2564693
theorem B5773133 : Blo 1012602 5773133 := bstep (se 3 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 5773133 = 2164925) B2164925
theorem B1709923 : Blo 1012602 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B1710065 : Blo 1012602 1710065 := bstep (se 2 (by rfl) ⟨641274, by rfl⟩ : syracuseStep 1710065 = 1282549) B1282549
theorem B1710193 : Blo 1012602 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B1710227 : Blo 1012602 1710227 := bstep (se 1 (by rfl) ⟨1282670, by rfl⟩ : syracuseStep 1710227 = 2565341) B2565341
theorem B1284275 : Blo 1012602 1284275 := bstep (se 1 (by rfl) ⟨963206, by rfl⟩ : syracuseStep 1284275 = 1926413) B1926413
theorem B1644803 : Blo 1012602 1644803 := bstep (se 1 (by rfl) ⟨1233602, by rfl⟩ : syracuseStep 1644803 = 2467205) B2467205
theorem B1710355 : Blo 1012602 1710355 := bstep (se 1 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 1710355 = 2565533) B2565533
theorem B2890019 : Blo 1012602 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B2169155 : Blo 1012602 2169155 := bstep (se 1 (by rfl) ⟨1626866, by rfl⟩ : syracuseStep 2169155 = 3253733) B3253733
theorem B11573603 : Blo 1012602 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B1710497 : Blo 1012602 1710497 := bstep (se 2 (by rfl) ⟨641436, by rfl⟩ : syracuseStep 1710497 = 1282873) B1282873
theorem B1710625 : Blo 1012602 1710625 := bstep (se 2 (by rfl) ⟨641484, by rfl⟩ : syracuseStep 1710625 = 1282969) B1282969
theorem B1710659 : Blo 1012602 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B2890349 : Blo 1012602 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B2890417 : Blo 1012602 2890417 := bstep (se 2 (by rfl) ⟨1083906, by rfl⟩ : syracuseStep 2890417 = 2167813) B2167813
theorem B1710787 : Blo 1012602 1710787 := bstep (se 1 (by rfl) ⟨1283090, by rfl⟩ : syracuseStep 1710787 = 2566181) B2566181
theorem B3250925 : Blo 1012602 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B1710929 : Blo 1012602 1710929 := bstep (se 2 (by rfl) ⟨641598, by rfl⟩ : syracuseStep 1710929 = 1283197) B1283197
theorem B1284979 : Blo 1012602 1284979 := bstep (se 1 (by rfl) ⟨963734, by rfl⟩ : syracuseStep 1284979 = 1927469) B1927469
theorem B2890691 : Blo 1012602 2890691 := bstep (se 1 (by rfl) ⟨2168018, by rfl⟩ : syracuseStep 2890691 = 4336037) B4336037
theorem B31267781 : Blo 1012602 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B1711057 : Blo 1012602 1711057 := bstep (se 2 (by rfl) ⟨641646, by rfl⟩ : syracuseStep 1711057 = 1283293) B1283293
theorem B1285075 : Blo 1012602 1285075 := bstep (se 1 (by rfl) ⟨963806, by rfl⟩ : syracuseStep 1285075 = 1927613) B1927613
theorem B1711091 : Blo 1012602 1711091 := bstep (se 1 (by rfl) ⟨1283318, by rfl⟩ : syracuseStep 1711091 = 2566637) B2566637
theorem B1711219 : Blo 1012602 1711219 := bstep (se 1 (by rfl) ⟨1283414, by rfl⟩ : syracuseStep 1711219 = 2566829) B2566829
theorem B2563235 : Blo 1012602 2563235 := bstep (se 1 (by rfl) ⟨1922426, by rfl⟩ : syracuseStep 2563235 = 3844853) B3844853
theorem B1711361 : Blo 1012602 1711361 := bstep (se 2 (by rfl) ⟨641760, by rfl⟩ : syracuseStep 1711361 = 1283521) B1283521
theorem B2563427 : Blo 1012602 2563427 := bstep (se 1 (by rfl) ⟨1922570, by rfl⟩ : syracuseStep 2563427 = 3845141) B3845141
theorem B1711489 : Blo 1012602 1711489 := bstep (se 2 (by rfl) ⟨641808, by rfl⟩ : syracuseStep 1711489 = 1283617) B1283617
theorem B1711523 : Blo 1012602 1711523 := bstep (se 1 (by rfl) ⟨1283642, by rfl⟩ : syracuseStep 1711523 = 2567285) B2567285
theorem B1220035 : Blo 1012602 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B1285571 : Blo 1012602 1285571 := bstep (se 1 (by rfl) ⟨964178, by rfl⟩ : syracuseStep 1285571 = 1928357) B1928357
theorem B2170385 : Blo 1012602 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B1711651 : Blo 1012602 1711651 := bstep (se 1 (by rfl) ⟨1283738, by rfl⟩ : syracuseStep 1711651 = 2567477) B2567477
theorem B13868657 : Blo 1012602 13868657 := bstep (se 2 (by rfl) ⟨5200746, by rfl⟩ : syracuseStep 13868657 = 10401493) B10401493
theorem B1711793 : Blo 1012602 1711793 := bstep (se 2 (by rfl) ⟨641922, by rfl⟩ : syracuseStep 1711793 = 1283845) B1283845
theorem B2891533 : Blo 1012602 2891533 := bstep (se 3 (by rfl) ⟨542162, by rfl⟩ : syracuseStep 2891533 = 1084325) B1084325
theorem B1711921 : Blo 1012602 1711921 := bstep (se 2 (by rfl) ⟨641970, by rfl⟩ : syracuseStep 1711921 = 1283941) B1283941
theorem B1711955 : Blo 1012602 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B2891693 : Blo 1012602 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B1712083 : Blo 1012602 1712083 := bstep (se 1 (by rfl) ⟨1284062, by rfl⟩ : syracuseStep 1712083 = 2568125) B2568125
theorem B1712225 : Blo 1012602 1712225 := bstep (se 2 (by rfl) ⟨642084, by rfl⟩ : syracuseStep 1712225 = 1284169) B1284169
theorem B2891875 : Blo 1012602 2891875 := bstep (se 1 (by rfl) ⟨2168906, by rfl⟩ : syracuseStep 2891875 = 4337813) B4337813
theorem B1286275 : Blo 1012602 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B1712353 : Blo 1012602 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B1286371 : Blo 1012602 1286371 := bstep (se 1 (by rfl) ⟨964778, by rfl⟩ : syracuseStep 1286371 = 1929557) B1929557
theorem B1712387 : Blo 1012602 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B2564369 : Blo 1012602 2564369 := bstep (se 2 (by rfl) ⟨961638, by rfl⟩ : syracuseStep 2564369 = 1923277) B1923277
theorem B15835445 : Blo 1012602 15835445 := bstep (se 5 (by rfl) ⟨742286, by rfl⟩ : syracuseStep 15835445 = 1484573) B1484573
theorem B2564419 : Blo 1012602 2564419 := bstep (se 1 (by rfl) ⟨1923314, by rfl⟩ : syracuseStep 2564419 = 3846629) B3846629
theorem B1712515 : Blo 1012602 1712515 := bstep (se 1 (by rfl) ⟨1284386, by rfl⟩ : syracuseStep 1712515 = 2568773) B2568773
theorem B2564561 : Blo 1012602 2564561 := bstep (se 2 (by rfl) ⟨961710, by rfl⟩ : syracuseStep 2564561 = 1923421) B1923421
theorem B3252707 : Blo 1012602 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B1712657 : Blo 1012602 1712657 := bstep (se 2 (by rfl) ⟨642246, by rfl⟩ : syracuseStep 1712657 = 1284493) B1284493
theorem B7316081 : Blo 1012602 7316081 := bstep (se 2 (by rfl) ⟨2743530, by rfl⟩ : syracuseStep 7316081 = 5487061) B5487061
theorem B1712785 : Blo 1012602 1712785 := bstep (se 2 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 1712785 = 1284589) B1284589
theorem B5776049 : Blo 1012602 5776049 := bstep (se 2 (by rfl) ⟨2166018, by rfl⟩ : syracuseStep 5776049 = 4332037) B4332037
theorem B1712819 : Blo 1012602 1712819 := bstep (se 1 (by rfl) ⟨1284614, by rfl⟩ : syracuseStep 1712819 = 2569229) B2569229
theorem B6497009 : Blo 1012602 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B1712947 : Blo 1012602 1712947 := bstep (se 1 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 1712947 = 2569421) B2569421
theorem B1713089 : Blo 1012602 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B2925571 : Blo 1012602 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B1713217 : Blo 1012602 1713217 := bstep (se 2 (by rfl) ⟨642456, by rfl⟩ : syracuseStep 1713217 = 1284913) B1284913
theorem B1713251 : Blo 1012602 1713251 := bstep (se 1 (by rfl) ⟨1284938, by rfl⟩ : syracuseStep 1713251 = 2569877) B2569877
theorem B4334755 : Blo 1012602 4334755 := bstep (se 1 (by rfl) ⟨3251066, by rfl⟩ : syracuseStep 4334755 = 6502133) B6502133
theorem B1713379 : Blo 1012602 1713379 := bstep (se 1 (by rfl) ⟨1285034, by rfl⟩ : syracuseStep 1713379 = 2570069) B2570069
theorem B1713521 : Blo 1012602 1713521 := bstep (se 2 (by rfl) ⟨642570, by rfl⟩ : syracuseStep 1713521 = 1285141) B1285141
theorem B2565553 : Blo 1012602 2565553 := bstep (se 2 (by rfl) ⟨962082, by rfl⟩ : syracuseStep 2565553 = 1924165) B1924165
theorem B1648081 : Blo 1012602 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B2893265 : Blo 1012602 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B2467313 : Blo 1012602 2467313 := bstep (se 2 (by rfl) ⟨925242, by rfl⟩ : syracuseStep 2467313 = 1850485) B1850485
theorem B1713649 : Blo 1012602 1713649 := bstep (se 2 (by rfl) ⟨642618, by rfl⟩ : syracuseStep 1713649 = 1285237) B1285237
theorem B1713683 : Blo 1012602 1713683 := bstep (se 1 (by rfl) ⟨1285262, by rfl⟩ : syracuseStep 1713683 = 2570525) B2570525
theorem B3090001 : Blo 1012602 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B3417713 : Blo 1012602 3417713 := bstep (se 2 (by rfl) ⟨1281642, by rfl⟩ : syracuseStep 3417713 = 2563285) B2563285
theorem B6006413 : Blo 1012602 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1713811 : Blo 1012602 1713811 := bstep (se 1 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 1713811 = 2570717) B2570717
theorem B2565827 : Blo 1012602 2565827 := bstep (se 1 (by rfl) ⟨1924370, by rfl⟩ : syracuseStep 2565827 = 3848741) B3848741
theorem B1976035 : Blo 1012602 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B1713953 : Blo 1012602 1713953 := bstep (se 2 (by rfl) ⟨642732, by rfl⟩ : syracuseStep 1713953 = 1285465) B1285465
theorem B3254051 : Blo 1012602 3254051 := bstep (se 1 (by rfl) ⟨2440538, by rfl⟩ : syracuseStep 3254051 = 4881077) B4881077
theorem B6170417 : Blo 1012602 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B2566019 : Blo 1012602 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B1714081 : Blo 1012602 1714081 := bstep (se 2 (by rfl) ⟨642780, by rfl⟩ : syracuseStep 1714081 = 1285561) B1285561
theorem B1714115 : Blo 1012602 1714115 := bstep (se 1 (by rfl) ⟨1285586, by rfl⟩ : syracuseStep 1714115 = 2571173) B2571173
theorem B5646341 : Blo 1012602 5646341 := bstep (se 4 (by rfl) ⟨529344, by rfl⟩ : syracuseStep 5646341 = 1058689) B1058689
theorem B1714243 : Blo 1012602 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B5482565 : Blo 1012602 5482565 := bstep (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) B1027981
theorem B5777507 : Blo 1012602 5777507 := bstep (se 1 (by rfl) ⟨4333130, by rfl⟩ : syracuseStep 5777507 = 8666261) B8666261
theorem B3418253 : Blo 1012602 3418253 := bstep (se 3 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 3418253 = 1281845) B1281845
theorem B6498467 : Blo 1012602 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B3418307 : Blo 1012602 3418307 := bstep (se 1 (by rfl) ⟨2563730, by rfl⟩ : syracuseStep 3418307 = 5127461) B5127461
theorem B1714385 : Blo 1012602 1714385 := bstep (se 2 (by rfl) ⟨642894, by rfl⟩ : syracuseStep 1714385 = 1285789) B1285789
theorem B1714513 : Blo 1012602 1714513 := bstep (se 2 (by rfl) ⟨642942, by rfl⟩ : syracuseStep 1714513 = 1285885) B1285885
theorem B1714547 : Blo 1012602 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B2894221 : Blo 1012602 2894221 := bstep (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) B1085333
theorem B3418577 : Blo 1012602 3418577 := bstep (se 2 (by rfl) ⟨1281966, by rfl⟩ : syracuseStep 3418577 = 2563933) B2563933
theorem B1714675 : Blo 1012602 1714675 := bstep (se 1 (by rfl) ⟨1286006, by rfl⟩ : syracuseStep 1714675 = 2572013) B2572013
theorem B1026659 : Blo 1012602 1026659 := bstep (se 1 (by rfl) ⟨769994, by rfl⟩ : syracuseStep 1026659 = 1539989) B1539989
theorem B2894449 : Blo 1012602 2894449 := bstep (se 2 (by rfl) ⟨1085418, by rfl⟩ : syracuseStep 2894449 = 2170837) B2170837
theorem B1714817 : Blo 1012602 1714817 := bstep (se 2 (by rfl) ⟨643056, by rfl⟩ : syracuseStep 1714817 = 1286113) B1286113
theorem B1714945 : Blo 1012602 1714945 := bstep (se 2 (by rfl) ⟨643104, by rfl⟩ : syracuseStep 1714945 = 1286209) B1286209
theorem B2894609 : Blo 1012602 2894609 := bstep (se 2 (by rfl) ⟨1085478, by rfl⟩ : syracuseStep 2894609 = 2170957) B2170957
theorem B1714979 : Blo 1012602 1714979 := bstep (se 1 (by rfl) ⟨1286234, by rfl⟩ : syracuseStep 1714979 = 2572469) B2572469
theorem B2566961 : Blo 1012602 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B1157971 : Blo 1012602 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B2567011 : Blo 1012602 2567011 := bstep (se 1 (by rfl) ⟨1925258, by rfl⟩ : syracuseStep 2567011 = 3850517) B3850517
theorem B1485697 : Blo 1012602 1485697 := bstep (se 2 (by rfl) ⟨557136, by rfl⟩ : syracuseStep 1485697 = 1114273) B1114273
theorem B2894723 : Blo 1012602 2894723 := bstep (se 1 (by rfl) ⟨2171042, by rfl⟩ : syracuseStep 2894723 = 4342085) B4342085
theorem B1715107 : Blo 1012602 1715107 := bstep (se 1 (by rfl) ⟨1286330, by rfl⟩ : syracuseStep 1715107 = 2572661) B2572661
theorem B13020101 : Blo 1012602 13020101 := bstep (se 4 (by rfl) ⟨1220634, by rfl⟩ : syracuseStep 13020101 = 2441269) B2441269
theorem B3419117 : Blo 1012602 3419117 := bstep (se 3 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 3419117 = 1282169) B1282169
theorem B2567153 : Blo 1012602 2567153 := bstep (se 2 (by rfl) ⟨962682, by rfl⟩ : syracuseStep 2567153 = 1925365) B1925365
theorem B3419171 : Blo 1012602 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B1715249 : Blo 1012602 1715249 := bstep (se 2 (by rfl) ⟨643218, by rfl⟩ : syracuseStep 1715249 = 1286437) B1286437
theorem B4336753 : Blo 1012602 4336753 := bstep (se 2 (by rfl) ⟨1626282, by rfl⟩ : syracuseStep 4336753 = 3252565) B3252565
theorem B3124369 : Blo 1012602 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B7023779 : Blo 1012602 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B1715377 : Blo 1012602 1715377 := bstep (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) B1286533
theorem B1715411 : Blo 1012602 1715411 := bstep (se 1 (by rfl) ⟨1286558, by rfl⟩ : syracuseStep 1715411 = 2573117) B2573117
theorem B3419441 : Blo 1012602 3419441 := bstep (se 2 (by rfl) ⟨1282290, by rfl⟩ : syracuseStep 3419441 = 2564581) B2564581
theorem B1518929 : Blo 1012602 1518929 := bstep (se 2 (by rfl) ⟨569598, by rfl⟩ : syracuseStep 1518929 = 1139197) B1139197
theorem B1518947 : Blo 1012602 1518947 := bstep (se 1 (by rfl) ⟨1139210, by rfl⟩ : syracuseStep 1518947 = 2278421) B2278421
theorem B1518977 : Blo 1012602 1518977 := bstep (se 2 (by rfl) ⟨569616, by rfl⟩ : syracuseStep 1518977 = 1139233) B1139233
theorem B1518995 : Blo 1012602 1518995 := bstep (se 1 (by rfl) ⟨1139246, by rfl⟩ : syracuseStep 1518995 = 2278493) B2278493
theorem B1519025 : Blo 1012602 1519025 := bstep (se 2 (by rfl) ⟨569634, by rfl⟩ : syracuseStep 1519025 = 1139269) B1139269
theorem B1519043 : Blo 1012602 1519043 := bstep (se 1 (by rfl) ⟨1139282, by rfl⟩ : syracuseStep 1519043 = 2278565) B2278565
theorem B1519073 : Blo 1012602 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B1519091 : Blo 1012602 1519091 := bstep (se 1 (by rfl) ⟨1139318, by rfl⟩ : syracuseStep 1519091 = 2278637) B2278637
theorem B3255821 : Blo 1012602 3255821 := bstep (se 3 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 3255821 = 1220933) B1220933
theorem B1519121 : Blo 1012602 1519121 := bstep (se 2 (by rfl) ⟨569670, by rfl⟩ : syracuseStep 1519121 = 1139341) B1139341
theorem B1519139 : Blo 1012602 1519139 := bstep (se 1 (by rfl) ⟨1139354, by rfl⟩ : syracuseStep 1519139 = 2278709) B2278709
theorem B1519169 : Blo 1012602 1519169 := bstep (se 2 (by rfl) ⟨569688, by rfl⟩ : syracuseStep 1519169 = 1139377) B1139377
theorem B1519187 : Blo 1012602 1519187 := bstep (se 1 (by rfl) ⟨1139390, by rfl⟩ : syracuseStep 1519187 = 2278781) B2278781
theorem B1519217 : Blo 1012602 1519217 := bstep (se 2 (by rfl) ⟨569706, by rfl⟩ : syracuseStep 1519217 = 1139413) B1139413
theorem B1519235 : Blo 1012602 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B1519265 : Blo 1012602 1519265 := bstep (se 2 (by rfl) ⟨569724, by rfl⟩ : syracuseStep 1519265 = 1139449) B1139449
theorem B1519283 : Blo 1012602 1519283 := bstep (se 1 (by rfl) ⟨1139462, by rfl⟩ : syracuseStep 1519283 = 2278925) B2278925
theorem B1519313 : Blo 1012602 1519313 := bstep (se 2 (by rfl) ⟨569742, by rfl⟩ : syracuseStep 1519313 = 1139485) B1139485
theorem B1519331 : Blo 1012602 1519331 := bstep (se 1 (by rfl) ⟨1139498, by rfl⟩ : syracuseStep 1519331 = 2278997) B2278997
theorem B10432241 : Blo 1012602 10432241 := bstep (se 2 (by rfl) ⟨3912090, by rfl⟩ : syracuseStep 10432241 = 7824181) B7824181
theorem B1519361 : Blo 1012602 1519361 := bstep (se 2 (by rfl) ⟨569760, by rfl⟩ : syracuseStep 1519361 = 1139521) B1139521
theorem B5484293 : Blo 1012602 5484293 := bstep (se 4 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 5484293 = 1028305) B1028305
theorem B1519379 : Blo 1012602 1519379 := bstep (se 1 (by rfl) ⟨1139534, by rfl⟩ : syracuseStep 1519379 = 2279069) B2279069
theorem B1519409 : Blo 1012602 1519409 := bstep (se 2 (by rfl) ⟨569778, by rfl⟩ : syracuseStep 1519409 = 1139557) B1139557
theorem B1519427 : Blo 1012602 1519427 := bstep (se 1 (by rfl) ⟨1139570, by rfl⟩ : syracuseStep 1519427 = 2279141) B2279141
theorem B3419981 : Blo 1012602 3419981 := bstep (se 3 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 3419981 = 1282493) B1282493
theorem B1519457 : Blo 1012602 1519457 := bstep (se 2 (by rfl) ⟨569796, by rfl⟩ : syracuseStep 1519457 = 1139593) B1139593
theorem B6500209 : Blo 1012602 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B1519475 : Blo 1012602 1519475 := bstep (se 1 (by rfl) ⟨1139606, by rfl⟩ : syracuseStep 1519475 = 2279213) B2279213
theorem B3420035 : Blo 1012602 3420035 := bstep (se 1 (by rfl) ⟨2565026, by rfl⟩ : syracuseStep 3420035 = 5130053) B5130053
theorem B1519505 : Blo 1012602 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B1519523 : Blo 1012602 1519523 := bstep (se 1 (by rfl) ⟨1139642, by rfl⟩ : syracuseStep 1519523 = 2279285) B2279285
theorem B2600867 : Blo 1012602 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B1519553 : Blo 1012602 1519553 := bstep (se 2 (by rfl) ⟨569832, by rfl⟩ : syracuseStep 1519553 = 1139665) B1139665
theorem B2568145 : Blo 1012602 2568145 := bstep (se 2 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 2568145 = 1926109) B1926109
theorem B1519571 : Blo 1012602 1519571 := bstep (se 1 (by rfl) ⟨1139678, by rfl⟩ : syracuseStep 1519571 = 2279357) B2279357
theorem B1519601 : Blo 1012602 1519601 := bstep (se 2 (by rfl) ⟨569850, by rfl⟩ : syracuseStep 1519601 = 1139701) B1139701
theorem B1519619 : Blo 1012602 1519619 := bstep (se 1 (by rfl) ⟨1139714, by rfl⟩ : syracuseStep 1519619 = 2279429) B2279429
theorem B1519649 : Blo 1012602 1519649 := bstep (se 2 (by rfl) ⟨569868, by rfl⟩ : syracuseStep 1519649 = 1139737) B1139737
theorem B1519667 : Blo 1012602 1519667 := bstep (se 1 (by rfl) ⟨1139750, by rfl⟩ : syracuseStep 1519667 = 2279501) B2279501
theorem B1519697 : Blo 1012602 1519697 := bstep (se 2 (by rfl) ⟨569886, by rfl⟩ : syracuseStep 1519697 = 1139773) B1139773
theorem B1519715 : Blo 1012602 1519715 := bstep (se 1 (by rfl) ⟨1139786, by rfl⟩ : syracuseStep 1519715 = 2279573) B2279573
theorem B1519745 : Blo 1012602 1519745 := bstep (se 2 (by rfl) ⟨569904, by rfl⟩ : syracuseStep 1519745 = 1139809) B1139809
theorem B3420305 : Blo 1012602 3420305 := bstep (se 2 (by rfl) ⟨1282614, by rfl⟩ : syracuseStep 3420305 = 2565229) B2565229
theorem B1519763 : Blo 1012602 1519763 := bstep (se 1 (by rfl) ⟨1139822, by rfl⟩ : syracuseStep 1519763 = 2279645) B2279645
theorem B1519793 : Blo 1012602 1519793 := bstep (se 2 (by rfl) ⟨569922, by rfl⟩ : syracuseStep 1519793 = 1139845) B1139845
theorem B1519811 : Blo 1012602 1519811 := bstep (se 1 (by rfl) ⟨1139858, by rfl⟩ : syracuseStep 1519811 = 2279717) B2279717
theorem B1519841 : Blo 1012602 1519841 := bstep (se 2 (by rfl) ⟨569940, by rfl⟩ : syracuseStep 1519841 = 1139881) B1139881
theorem B2568419 : Blo 1012602 2568419 := bstep (se 1 (by rfl) ⟨1926314, by rfl⟩ : syracuseStep 2568419 = 3852629) B3852629
theorem B1519859 : Blo 1012602 1519859 := bstep (se 1 (by rfl) ⟨1139894, by rfl⟩ : syracuseStep 1519859 = 2279789) B2279789
theorem B1519889 : Blo 1012602 1519889 := bstep (se 2 (by rfl) ⟨569958, by rfl⟩ : syracuseStep 1519889 = 1139917) B1139917
theorem B42250517 : Blo 1012602 42250517 := bstep (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) B1980493
theorem B1519907 : Blo 1012602 1519907 := bstep (se 1 (by rfl) ⟨1139930, by rfl⟩ : syracuseStep 1519907 = 2279861) B2279861
theorem B1519937 : Blo 1012602 1519937 := bstep (se 2 (by rfl) ⟨569976, by rfl⟩ : syracuseStep 1519937 = 1139953) B1139953
theorem B1519955 : Blo 1012602 1519955 := bstep (se 1 (by rfl) ⟨1139966, by rfl⟩ : syracuseStep 1519955 = 2279933) B2279933
theorem B1028435 : Blo 1012602 1028435 := bstep (se 1 (by rfl) ⟨771326, by rfl⟩ : syracuseStep 1028435 = 1542653) B1542653
theorem B1519985 : Blo 1012602 1519985 := bstep (se 2 (by rfl) ⟨569994, by rfl⟩ : syracuseStep 1519985 = 1139989) B1139989
theorem B1520003 : Blo 1012602 1520003 := bstep (se 1 (by rfl) ⟨1140002, by rfl⟩ : syracuseStep 1520003 = 2280005) B2280005
theorem B46903693 : Blo 1012602 46903693 := bstep (se 3 (by rfl) ⟨8794442, by rfl⟩ : syracuseStep 46903693 = 17588885) B17588885
theorem B1520033 : Blo 1012602 1520033 := bstep (se 2 (by rfl) ⟨570012, by rfl⟩ : syracuseStep 1520033 = 1140025) B1140025
theorem B2568611 : Blo 1012602 2568611 := bstep (se 1 (by rfl) ⟨1926458, by rfl⟩ : syracuseStep 2568611 = 3852917) B3852917
theorem B1520051 : Blo 1012602 1520051 := bstep (se 1 (by rfl) ⟨1140038, by rfl⟩ : syracuseStep 1520051 = 2280077) B2280077
theorem B1520081 : Blo 1012602 1520081 := bstep (se 2 (by rfl) ⟨570030, by rfl⟩ : syracuseStep 1520081 = 1140061) B1140061
theorem B1520099 : Blo 1012602 1520099 := bstep (se 1 (by rfl) ⟨1140074, by rfl⟩ : syracuseStep 1520099 = 2280149) B2280149
theorem B1520129 : Blo 1012602 1520129 := bstep (se 2 (by rfl) ⟨570048, by rfl⟩ : syracuseStep 1520129 = 1140097) B1140097
theorem B1520147 : Blo 1012602 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B1520177 : Blo 1012602 1520177 := bstep (se 2 (by rfl) ⟨570066, by rfl⟩ : syracuseStep 1520177 = 1140133) B1140133
theorem B1520195 : Blo 1012602 1520195 := bstep (se 1 (by rfl) ⟨1140146, by rfl⟩ : syracuseStep 1520195 = 2280293) B2280293
theorem B1520225 : Blo 1012602 1520225 := bstep (se 2 (by rfl) ⟨570084, by rfl⟩ : syracuseStep 1520225 = 1140169) B1140169
theorem B1520243 : Blo 1012602 1520243 := bstep (se 1 (by rfl) ⟨1140182, by rfl⟩ : syracuseStep 1520243 = 2280365) B2280365
theorem B3846797 : Blo 1012602 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B1520273 : Blo 1012602 1520273 := bstep (se 2 (by rfl) ⟨570102, by rfl⟩ : syracuseStep 1520273 = 1140205) B1140205
theorem B1520291 : Blo 1012602 1520291 := bstep (se 1 (by rfl) ⟨1140218, by rfl⟩ : syracuseStep 1520291 = 2280437) B2280437
theorem B3420845 : Blo 1012602 3420845 := bstep (se 3 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 3420845 = 1282817) B1282817
theorem B1520321 : Blo 1012602 1520321 := bstep (se 2 (by rfl) ⟨570120, by rfl⟩ : syracuseStep 1520321 = 1140241) B1140241
theorem B1520339 : Blo 1012602 1520339 := bstep (se 1 (by rfl) ⟨1140254, by rfl⟩ : syracuseStep 1520339 = 2280509) B2280509
theorem B3420899 : Blo 1012602 3420899 := bstep (se 1 (by rfl) ⟨2565674, by rfl⟩ : syracuseStep 3420899 = 5131349) B5131349
theorem B1520369 : Blo 1012602 1520369 := bstep (se 2 (by rfl) ⟨570138, by rfl⟩ : syracuseStep 1520369 = 1140277) B1140277
theorem B1520387 : Blo 1012602 1520387 := bstep (se 1 (by rfl) ⟨1140290, by rfl⟩ : syracuseStep 1520387 = 2280581) B2280581
theorem B4109069 : Blo 1012602 4109069 := bstep (se 3 (by rfl) ⟨770450, by rfl⟩ : syracuseStep 4109069 = 1540901) B1540901
theorem B1520417 : Blo 1012602 1520417 := bstep (se 2 (by rfl) ⟨570156, by rfl⟩ : syracuseStep 1520417 = 1140313) B1140313
theorem B1520435 : Blo 1012602 1520435 := bstep (se 1 (by rfl) ⟨1140326, by rfl⟩ : syracuseStep 1520435 = 2280653) B2280653
theorem B1520465 : Blo 1012602 1520465 := bstep (se 2 (by rfl) ⟨570174, by rfl⟩ : syracuseStep 1520465 = 1140349) B1140349
theorem B1520483 : Blo 1012602 1520483 := bstep (se 1 (by rfl) ⟨1140362, by rfl⟩ : syracuseStep 1520483 = 2280725) B2280725
theorem B1520513 : Blo 1012602 1520513 := bstep (se 2 (by rfl) ⟨570192, by rfl⟩ : syracuseStep 1520513 = 1140385) B1140385
theorem B1520531 : Blo 1012602 1520531 := bstep (se 1 (by rfl) ⟨1140398, by rfl⟩ : syracuseStep 1520531 = 2280797) B2280797
theorem B1520561 : Blo 1012602 1520561 := bstep (se 2 (by rfl) ⟨570210, by rfl⟩ : syracuseStep 1520561 = 1140421) B1140421
theorem B1520579 : Blo 1012602 1520579 := bstep (se 1 (by rfl) ⟨1140434, by rfl⟩ : syracuseStep 1520579 = 2280869) B2280869
theorem B1520609 : Blo 1012602 1520609 := bstep (se 2 (by rfl) ⟨570228, by rfl⟩ : syracuseStep 1520609 = 1140457) B1140457
theorem B2929645 : Blo 1012602 2929645 := bstep (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) B1098617
theorem B3421169 : Blo 1012602 3421169 := bstep (se 2 (by rfl) ⟨1282938, by rfl⟩ : syracuseStep 3421169 = 2565877) B2565877
theorem B9745393 : Blo 1012602 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B1520627 : Blo 1012602 1520627 := bstep (se 1 (by rfl) ⟨1140470, by rfl⟩ : syracuseStep 1520627 = 2280941) B2280941
theorem B1520657 : Blo 1012602 1520657 := bstep (se 2 (by rfl) ⟨570246, by rfl⟩ : syracuseStep 1520657 = 1140493) B1140493
theorem B1520675 : Blo 1012602 1520675 := bstep (se 1 (by rfl) ⟨1140506, by rfl⟩ : syracuseStep 1520675 = 2281013) B2281013
theorem B1520705 : Blo 1012602 1520705 := bstep (se 2 (by rfl) ⟨570264, by rfl⟩ : syracuseStep 1520705 = 1140529) B1140529
theorem B2438225 : Blo 1012602 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B1520723 : Blo 1012602 1520723 := bstep (se 1 (by rfl) ⟨1140542, by rfl⟩ : syracuseStep 1520723 = 2281085) B2281085
theorem B72103025 : Blo 1012602 72103025 := bstep (se 2 (by rfl) ⟨27038634, by rfl⟩ : syracuseStep 72103025 = 54077269) B54077269
theorem B1520753 : Blo 1012602 1520753 := bstep (se 2 (by rfl) ⟨570282, by rfl⟩ : syracuseStep 1520753 = 1140565) B1140565
theorem B1520771 : Blo 1012602 1520771 := bstep (se 1 (by rfl) ⟨1140578, by rfl⟩ : syracuseStep 1520771 = 2281157) B2281157
theorem B1520801 : Blo 1012602 1520801 := bstep (se 2 (by rfl) ⟨570300, by rfl⟩ : syracuseStep 1520801 = 1140601) B1140601
theorem B1520819 : Blo 1012602 1520819 := bstep (se 1 (by rfl) ⟨1140614, by rfl⟩ : syracuseStep 1520819 = 2281229) B2281229
theorem B19510469 : Blo 1012602 19510469 := bstep (se 4 (by rfl) ⟨1829106, by rfl⟩ : syracuseStep 19510469 = 3658213) B3658213
theorem B1520849 : Blo 1012602 1520849 := bstep (se 2 (by rfl) ⟨570318, by rfl⟩ : syracuseStep 1520849 = 1140637) B1140637
theorem B1520867 : Blo 1012602 1520867 := bstep (se 1 (by rfl) ⟨1140650, by rfl⟩ : syracuseStep 1520867 = 2281301) B2281301
theorem B1520897 : Blo 1012602 1520897 := bstep (se 2 (by rfl) ⟨570336, by rfl⟩ : syracuseStep 1520897 = 1140673) B1140673
theorem B1520915 : Blo 1012602 1520915 := bstep (se 1 (by rfl) ⟨1140686, by rfl⟩ : syracuseStep 1520915 = 2281373) B2281373
theorem B1520945 : Blo 1012602 1520945 := bstep (se 2 (by rfl) ⟨570354, by rfl⟩ : syracuseStep 1520945 = 1140709) B1140709
theorem B1520963 : Blo 1012602 1520963 := bstep (se 1 (by rfl) ⟨1140722, by rfl⟩ : syracuseStep 1520963 = 2281445) B2281445
theorem B2569553 : Blo 1012602 2569553 := bstep (se 2 (by rfl) ⟨963582, by rfl⟩ : syracuseStep 2569553 = 1927165) B1927165
theorem B1389907 : Blo 1012602 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B1520993 : Blo 1012602 1520993 := bstep (se 2 (by rfl) ⟨570372, by rfl⟩ : syracuseStep 1520993 = 1140745) B1140745
theorem B1521011 : Blo 1012602 1521011 := bstep (se 1 (by rfl) ⟨1140758, by rfl⟩ : syracuseStep 1521011 = 2281517) B2281517
theorem B2569603 : Blo 1012602 2569603 := bstep (se 1 (by rfl) ⟨1927202, by rfl⟩ : syracuseStep 2569603 = 3854405) B3854405
theorem B1521041 : Blo 1012602 1521041 := bstep (se 2 (by rfl) ⟨570390, by rfl⟩ : syracuseStep 1521041 = 1140781) B1140781
theorem B1521059 : Blo 1012602 1521059 := bstep (se 1 (by rfl) ⟨1140794, by rfl⟩ : syracuseStep 1521059 = 2281589) B2281589
theorem B3847601 : Blo 1012602 3847601 := bstep (se 2 (by rfl) ⟨1442850, by rfl⟩ : syracuseStep 3847601 = 2885701) B2885701
theorem B1521089 : Blo 1012602 1521089 := bstep (se 2 (by rfl) ⟨570408, by rfl⟩ : syracuseStep 1521089 = 1140817) B1140817
theorem B1521107 : Blo 1012602 1521107 := bstep (se 1 (by rfl) ⟨1140830, by rfl⟩ : syracuseStep 1521107 = 2281661) B2281661
theorem B1521137 : Blo 1012602 1521137 := bstep (se 2 (by rfl) ⟨570426, by rfl⟩ : syracuseStep 1521137 = 1140853) B1140853
theorem B1521155 : Blo 1012602 1521155 := bstep (se 1 (by rfl) ⟨1140866, by rfl⟩ : syracuseStep 1521155 = 2281733) B2281733
theorem B3421709 : Blo 1012602 3421709 := bstep (se 3 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 3421709 = 1283141) B1283141
theorem B2569745 : Blo 1012602 2569745 := bstep (se 2 (by rfl) ⟨963654, by rfl⟩ : syracuseStep 2569745 = 1927309) B1927309
theorem B1521185 : Blo 1012602 1521185 := bstep (se 2 (by rfl) ⟨570444, by rfl⟩ : syracuseStep 1521185 = 1140889) B1140889
theorem B1521203 : Blo 1012602 1521203 := bstep (se 1 (by rfl) ⟨1140902, by rfl⟩ : syracuseStep 1521203 = 2281805) B2281805
theorem B3421763 : Blo 1012602 3421763 := bstep (se 1 (by rfl) ⟨2566322, by rfl⟩ : syracuseStep 3421763 = 5132645) B5132645
theorem B1521233 : Blo 1012602 1521233 := bstep (se 2 (by rfl) ⟨570462, by rfl⟩ : syracuseStep 1521233 = 1140925) B1140925
theorem B1521251 : Blo 1012602 1521251 := bstep (se 1 (by rfl) ⟨1140938, by rfl⟩ : syracuseStep 1521251 = 2281877) B2281877
theorem B1521281 : Blo 1012602 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B1521299 : Blo 1012602 1521299 := bstep (se 1 (by rfl) ⟨1140974, by rfl⟩ : syracuseStep 1521299 = 2281949) B2281949
theorem B1521329 : Blo 1012602 1521329 := bstep (se 2 (by rfl) ⟨570498, by rfl⟩ : syracuseStep 1521329 = 1140997) B1140997
theorem B1521347 : Blo 1012602 1521347 := bstep (se 1 (by rfl) ⟨1141010, by rfl⟩ : syracuseStep 1521347 = 2282021) B2282021
theorem B1521377 : Blo 1012602 1521377 := bstep (se 2 (by rfl) ⟨570516, by rfl⟩ : syracuseStep 1521377 = 1141033) B1141033
theorem B1521395 : Blo 1012602 1521395 := bstep (se 1 (by rfl) ⟨1141046, by rfl⟩ : syracuseStep 1521395 = 2282093) B2282093
theorem B2438915 : Blo 1012602 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B6502157 : Blo 1012602 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B1521425 : Blo 1012602 1521425 := bstep (se 2 (by rfl) ⟨570534, by rfl⟩ : syracuseStep 1521425 = 1141069) B1141069
theorem B1521443 : Blo 1012602 1521443 := bstep (se 1 (by rfl) ⟨1141082, by rfl⟩ : syracuseStep 1521443 = 2282165) B2282165
theorem B1521473 : Blo 1012602 1521473 := bstep (se 2 (by rfl) ⟨570552, by rfl⟩ : syracuseStep 1521473 = 1141105) B1141105
theorem B3422033 : Blo 1012602 3422033 := bstep (se 2 (by rfl) ⟨1283262, by rfl⟩ : syracuseStep 3422033 = 2566525) B2566525
theorem B1521491 : Blo 1012602 1521491 := bstep (se 1 (by rfl) ⟨1141118, by rfl⟩ : syracuseStep 1521491 = 2282237) B2282237
theorem B1521521 : Blo 1012602 1521521 := bstep (se 2 (by rfl) ⟨570570, by rfl⟩ : syracuseStep 1521521 = 1141141) B1141141
theorem B1521539 : Blo 1012602 1521539 := bstep (se 1 (by rfl) ⟨1141154, by rfl⟩ : syracuseStep 1521539 = 2282309) B2282309
theorem B1521569 : Blo 1012602 1521569 := bstep (se 2 (by rfl) ⟨570588, by rfl⟩ : syracuseStep 1521569 = 1141177) B1141177
theorem B1521587 : Blo 1012602 1521587 := bstep (se 1 (by rfl) ⟨1141190, by rfl⟩ : syracuseStep 1521587 = 2282381) B2282381
theorem B10401733 : Blo 1012602 10401733 := bstep (se 4 (by rfl) ⟨975162, by rfl⟩ : syracuseStep 10401733 = 1950325) B1950325
theorem B1521617 : Blo 1012602 1521617 := bstep (se 2 (by rfl) ⟨570606, by rfl⟩ : syracuseStep 1521617 = 1141213) B1141213
theorem B7026659 : Blo 1012602 7026659 := bstep (se 1 (by rfl) ⟨5269994, by rfl⟩ : syracuseStep 7026659 = 10539989) B10539989
theorem B1521635 : Blo 1012602 1521635 := bstep (se 1 (by rfl) ⟨1141226, by rfl⟩ : syracuseStep 1521635 = 2282453) B2282453
theorem B9254897 : Blo 1012602 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B1521665 : Blo 1012602 1521665 := bstep (se 2 (by rfl) ⟨570624, by rfl⟩ : syracuseStep 1521665 = 1141249) B1141249
theorem B1521683 : Blo 1012602 1521683 := bstep (se 1 (by rfl) ⟨1141262, by rfl⟩ : syracuseStep 1521683 = 2282525) B2282525
theorem B1521713 : Blo 1012602 1521713 := bstep (se 2 (by rfl) ⟨570642, by rfl⟩ : syracuseStep 1521713 = 1141285) B1141285
theorem B1521731 : Blo 1012602 1521731 := bstep (se 1 (by rfl) ⟨1141298, by rfl⟩ : syracuseStep 1521731 = 2282597) B2282597
theorem B9877573 : Blo 1012602 9877573 := bstep (se 4 (by rfl) ⟨926022, by rfl⟩ : syracuseStep 9877573 = 1852045) B1852045
theorem B3848269 : Blo 1012602 3848269 := bstep (se 3 (by rfl) ⟨721550, by rfl⟩ : syracuseStep 3848269 = 1443101) B1443101
theorem B1521761 : Blo 1012602 1521761 := bstep (se 2 (by rfl) ⟨570660, by rfl⟩ : syracuseStep 1521761 = 1141321) B1141321
theorem B4700273 : Blo 1012602 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B1521779 : Blo 1012602 1521779 := bstep (se 1 (by rfl) ⟨1141334, by rfl⟩ : syracuseStep 1521779 = 2282669) B2282669
theorem B1521809 : Blo 1012602 1521809 := bstep (se 2 (by rfl) ⟨570678, by rfl⟩ : syracuseStep 1521809 = 1141357) B1141357
theorem B1521827 : Blo 1012602 1521827 := bstep (se 1 (by rfl) ⟨1141370, by rfl⟩ : syracuseStep 1521827 = 2282741) B2282741
theorem B1521857 : Blo 1012602 1521857 := bstep (se 2 (by rfl) ⟨570696, by rfl⟩ : syracuseStep 1521857 = 1141393) B1141393
theorem B1521875 : Blo 1012602 1521875 := bstep (se 1 (by rfl) ⟨1141406, by rfl⟩ : syracuseStep 1521875 = 2282813) B2282813
theorem B1521905 : Blo 1012602 1521905 := bstep (se 2 (by rfl) ⟨570714, by rfl⟩ : syracuseStep 1521905 = 1141429) B1141429
theorem B1521923 : Blo 1012602 1521923 := bstep (se 1 (by rfl) ⟨1141442, by rfl⟩ : syracuseStep 1521923 = 2282885) B2282885
theorem B1521953 : Blo 1012602 1521953 := bstep (se 2 (by rfl) ⟨570732, by rfl⟩ : syracuseStep 1521953 = 1141465) B1141465
theorem B2472241 : Blo 1012602 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B1521971 : Blo 1012602 1521971 := bstep (se 1 (by rfl) ⟨1141478, by rfl⟩ : syracuseStep 1521971 = 2282957) B2282957
theorem B1522001 : Blo 1012602 1522001 := bstep (se 2 (by rfl) ⟨570750, by rfl⟩ : syracuseStep 1522001 = 1141501) B1141501
theorem B1522019 : Blo 1012602 1522019 := bstep (se 1 (by rfl) ⟨1141514, by rfl⟩ : syracuseStep 1522019 = 2283029) B2283029
theorem B3422573 : Blo 1012602 3422573 := bstep (se 3 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 3422573 = 1283465) B1283465
theorem B1522049 : Blo 1012602 1522049 := bstep (se 2 (by rfl) ⟨570768, by rfl⟩ : syracuseStep 1522049 = 1141537) B1141537
theorem B1522067 : Blo 1012602 1522067 := bstep (se 1 (by rfl) ⟨1141550, by rfl⟩ : syracuseStep 1522067 = 2283101) B2283101
theorem B3422627 : Blo 1012602 3422627 := bstep (se 1 (by rfl) ⟨2566970, by rfl⟩ : syracuseStep 3422627 = 5133941) B5133941
theorem B1522097 : Blo 1012602 1522097 := bstep (se 2 (by rfl) ⟨570786, by rfl⟩ : syracuseStep 1522097 = 1141573) B1141573
theorem B1522115 : Blo 1012602 1522115 := bstep (se 1 (by rfl) ⟨1141586, by rfl⟩ : syracuseStep 1522115 = 2283173) B2283173
theorem B1522145 : Blo 1012602 1522145 := bstep (se 2 (by rfl) ⟨570804, by rfl⟩ : syracuseStep 1522145 = 1141609) B1141609
theorem B2570737 : Blo 1012602 2570737 := bstep (se 2 (by rfl) ⟨964026, by rfl⟩ : syracuseStep 2570737 = 1928053) B1928053
theorem B1522163 : Blo 1012602 1522163 := bstep (se 1 (by rfl) ⟨1141622, by rfl⟩ : syracuseStep 1522163 = 2283245) B2283245
theorem B1522193 : Blo 1012602 1522193 := bstep (se 2 (by rfl) ⟨570822, by rfl⟩ : syracuseStep 1522193 = 1141645) B1141645
theorem B1522211 : Blo 1012602 1522211 := bstep (se 1 (by rfl) ⟨1141658, by rfl⟩ : syracuseStep 1522211 = 2283317) B2283317
theorem B1522241 : Blo 1012602 1522241 := bstep (se 2 (by rfl) ⟨570840, by rfl⟩ : syracuseStep 1522241 = 1141681) B1141681
theorem B1522259 : Blo 1012602 1522259 := bstep (se 1 (by rfl) ⟨1141694, by rfl⟩ : syracuseStep 1522259 = 2283389) B2283389
theorem B1587811 : Blo 1012602 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B29244017 : Blo 1012602 29244017 := bstep (se 2 (by rfl) ⟨10966506, by rfl⟩ : syracuseStep 29244017 = 21933013) B21933013
theorem B1522289 : Blo 1012602 1522289 := bstep (se 2 (by rfl) ⟨570858, by rfl⟩ : syracuseStep 1522289 = 1141717) B1141717
theorem B1522307 : Blo 1012602 1522307 := bstep (se 1 (by rfl) ⟨1141730, by rfl⟩ : syracuseStep 1522307 = 2283461) B2283461
theorem B1522337 : Blo 1012602 1522337 := bstep (se 2 (by rfl) ⟨570876, by rfl⟩ : syracuseStep 1522337 = 1141753) B1141753
theorem B3652273 : Blo 1012602 3652273 := bstep (se 2 (by rfl) ⟨1369602, by rfl⟩ : syracuseStep 3652273 = 2739205) B2739205
theorem B3422897 : Blo 1012602 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B1522355 : Blo 1012602 1522355 := bstep (se 1 (by rfl) ⟨1141766, by rfl⟩ : syracuseStep 1522355 = 2283533) B2283533
theorem B7322309 : Blo 1012602 7322309 := bstep (se 4 (by rfl) ⟨686466, by rfl⟩ : syracuseStep 7322309 = 1372933) B1372933
theorem B1522385 : Blo 1012602 1522385 := bstep (se 2 (by rfl) ⟨570894, by rfl⟩ : syracuseStep 1522385 = 1141789) B1141789
theorem B1522403 : Blo 1012602 1522403 := bstep (se 1 (by rfl) ⟨1141802, by rfl⟩ : syracuseStep 1522403 = 2283605) B2283605
theorem B1522433 : Blo 1012602 1522433 := bstep (se 2 (by rfl) ⟨570912, by rfl⟩ : syracuseStep 1522433 = 1141825) B1141825
theorem B2571011 : Blo 1012602 2571011 := bstep (se 1 (by rfl) ⟨1928258, by rfl⟩ : syracuseStep 2571011 = 3856517) B3856517
theorem B1522451 : Blo 1012602 1522451 := bstep (se 1 (by rfl) ⟨1141838, by rfl⟩ : syracuseStep 1522451 = 2283677) B2283677
theorem B1522481 : Blo 1012602 1522481 := bstep (se 2 (by rfl) ⟨570930, by rfl⟩ : syracuseStep 1522481 = 1141861) B1141861
theorem B1522499 : Blo 1012602 1522499 := bstep (se 1 (by rfl) ⟨1141874, by rfl⟩ : syracuseStep 1522499 = 2283749) B2283749
theorem B1522529 : Blo 1012602 1522529 := bstep (se 2 (by rfl) ⟨570948, by rfl⟩ : syracuseStep 1522529 = 1141897) B1141897
theorem B3849059 : Blo 1012602 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B1522547 : Blo 1012602 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B1522577 : Blo 1012602 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B1522595 : Blo 1012602 1522595 := bstep (se 1 (by rfl) ⟨1141946, by rfl⟩ : syracuseStep 1522595 = 2283893) B2283893
theorem B1522625 : Blo 1012602 1522625 := bstep (se 2 (by rfl) ⟨570984, by rfl⟩ : syracuseStep 1522625 = 1141969) B1141969
theorem B2571203 : Blo 1012602 2571203 := bstep (se 1 (by rfl) ⟨1928402, by rfl⟩ : syracuseStep 2571203 = 3856805) B3856805
theorem B1522643 : Blo 1012602 1522643 := bstep (se 1 (by rfl) ⟨1141982, by rfl⟩ : syracuseStep 1522643 = 2283965) B2283965
theorem B1522673 : Blo 1012602 1522673 := bstep (se 2 (by rfl) ⟨571002, by rfl⟩ : syracuseStep 1522673 = 1142005) B1142005
theorem B1522691 : Blo 1012602 1522691 := bstep (se 1 (by rfl) ⟨1142018, by rfl⟩ : syracuseStep 1522691 = 2284037) B2284037
theorem B1522721 : Blo 1012602 1522721 := bstep (se 2 (by rfl) ⟨571020, by rfl⟩ : syracuseStep 1522721 = 1142041) B1142041
theorem B4340785 : Blo 1012602 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B1522739 : Blo 1012602 1522739 := bstep (se 1 (by rfl) ⟨1142054, by rfl⟩ : syracuseStep 1522739 = 2284109) B2284109
theorem B1522769 : Blo 1012602 1522769 := bstep (se 2 (by rfl) ⟨571038, by rfl⟩ : syracuseStep 1522769 = 1142077) B1142077
theorem B1522787 : Blo 1012602 1522787 := bstep (se 1 (by rfl) ⟨1142090, by rfl⟩ : syracuseStep 1522787 = 2284181) B2284181
theorem B1522817 : Blo 1012602 1522817 := bstep (se 2 (by rfl) ⟨571056, by rfl⟩ : syracuseStep 1522817 = 1142113) B1142113
theorem B1522835 : Blo 1012602 1522835 := bstep (se 1 (by rfl) ⟨1142126, by rfl⟩ : syracuseStep 1522835 = 2284253) B2284253
theorem B1522865 : Blo 1012602 1522865 := bstep (se 2 (by rfl) ⟨571074, by rfl⟩ : syracuseStep 1522865 = 1142149) B1142149
theorem B1522883 : Blo 1012602 1522883 := bstep (se 1 (by rfl) ⟨1142162, by rfl⟩ : syracuseStep 1522883 = 2284325) B2284325
theorem B3423437 : Blo 1012602 3423437 := bstep (se 3 (by rfl) ⟨641894, by rfl⟩ : syracuseStep 3423437 = 1283789) B1283789
theorem B1981649 : Blo 1012602 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B1522913 : Blo 1012602 1522913 := bstep (se 2 (by rfl) ⟨571092, by rfl⟩ : syracuseStep 1522913 = 1142185) B1142185
theorem B1522931 : Blo 1012602 1522931 := bstep (se 1 (by rfl) ⟨1142198, by rfl⟩ : syracuseStep 1522931 = 2284397) B2284397
theorem B3423491 : Blo 1012602 3423491 := bstep (se 1 (by rfl) ⟨2567618, by rfl⟩ : syracuseStep 3423491 = 5135237) B5135237
theorem B1522961 : Blo 1012602 1522961 := bstep (se 2 (by rfl) ⟨571110, by rfl⟩ : syracuseStep 1522961 = 1142221) B1142221
theorem B1522979 : Blo 1012602 1522979 := bstep (se 1 (by rfl) ⟨1142234, by rfl⟩ : syracuseStep 1522979 = 2284469) B2284469
theorem B1523009 : Blo 1012602 1523009 := bstep (se 2 (by rfl) ⟨571128, by rfl⟩ : syracuseStep 1523009 = 1142257) B1142257
theorem B1523027 : Blo 1012602 1523027 := bstep (se 1 (by rfl) ⟨1142270, by rfl⟩ : syracuseStep 1523027 = 2284541) B2284541
theorem B1523057 : Blo 1012602 1523057 := bstep (se 2 (by rfl) ⟨571146, by rfl⟩ : syracuseStep 1523057 = 1142293) B1142293
theorem B1523075 : Blo 1012602 1523075 := bstep (se 1 (by rfl) ⟨1142306, by rfl⟩ : syracuseStep 1523075 = 2284613) B2284613
theorem B1523105 : Blo 1012602 1523105 := bstep (se 2 (by rfl) ⟨571164, by rfl⟩ : syracuseStep 1523105 = 1142329) B1142329
theorem B1523123 : Blo 1012602 1523123 := bstep (se 1 (by rfl) ⟨1142342, by rfl⟩ : syracuseStep 1523123 = 2284685) B2284685
theorem B6929869 : Blo 1012602 6929869 := bstep (se 3 (by rfl) ⟨1299350, by rfl⟩ : syracuseStep 6929869 = 2598701) B2598701
theorem B1523153 : Blo 1012602 1523153 := bstep (se 2 (by rfl) ⟨571182, by rfl⟩ : syracuseStep 1523153 = 1142365) B1142365
theorem B1523171 : Blo 1012602 1523171 := bstep (se 1 (by rfl) ⟨1142378, by rfl⟩ : syracuseStep 1523171 = 2284757) B2284757
theorem B3849713 : Blo 1012602 3849713 := bstep (se 2 (by rfl) ⟨1443642, by rfl⟩ : syracuseStep 3849713 = 2887285) B2887285
theorem B1523201 : Blo 1012602 1523201 := bstep (se 2 (by rfl) ⟨571200, by rfl⟩ : syracuseStep 1523201 = 1142401) B1142401
theorem B3423761 : Blo 1012602 3423761 := bstep (se 2 (by rfl) ⟨1283910, by rfl⟩ : syracuseStep 3423761 = 2567821) B2567821
theorem B1523219 : Blo 1012602 1523219 := bstep (se 1 (by rfl) ⟨1142414, by rfl⟩ : syracuseStep 1523219 = 2284829) B2284829
theorem B1523249 : Blo 1012602 1523249 := bstep (se 2 (by rfl) ⟨571218, by rfl⟩ : syracuseStep 1523249 = 1142437) B1142437
theorem B1523267 : Blo 1012602 1523267 := bstep (se 1 (by rfl) ⟨1142450, by rfl⟩ : syracuseStep 1523267 = 2284901) B2284901
theorem B1523297 : Blo 1012602 1523297 := bstep (se 2 (by rfl) ⟨571236, by rfl⟩ : syracuseStep 1523297 = 1142473) B1142473
theorem B1523315 : Blo 1012602 1523315 := bstep (se 1 (by rfl) ⟨1142486, by rfl⟩ : syracuseStep 1523315 = 2284973) B2284973
theorem B1523345 : Blo 1012602 1523345 := bstep (se 2 (by rfl) ⟨571254, by rfl⟩ : syracuseStep 1523345 = 1142509) B1142509
theorem B2604707 : Blo 1012602 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B1523363 : Blo 1012602 1523363 := bstep (se 1 (by rfl) ⟨1142522, by rfl⟩ : syracuseStep 1523363 = 2285045) B2285045
theorem B2440867 : Blo 1012602 2440867 := bstep (se 1 (by rfl) ⟨1830650, by rfl⟩ : syracuseStep 2440867 = 3661301) B3661301
theorem B1523393 : Blo 1012602 1523393 := bstep (se 2 (by rfl) ⟨571272, by rfl⟩ : syracuseStep 1523393 = 1142545) B1142545
theorem B1523411 : Blo 1012602 1523411 := bstep (se 1 (by rfl) ⟨1142558, by rfl⟩ : syracuseStep 1523411 = 2285117) B2285117
theorem B1523441 : Blo 1012602 1523441 := bstep (se 2 (by rfl) ⟨571290, by rfl⟩ : syracuseStep 1523441 = 1142581) B1142581
theorem B1523459 : Blo 1012602 1523459 := bstep (se 1 (by rfl) ⟨1142594, by rfl⟩ : syracuseStep 1523459 = 2285189) B2285189
theorem B1523489 : Blo 1012602 1523489 := bstep (se 2 (by rfl) ⟨571308, by rfl⟩ : syracuseStep 1523489 = 1142617) B1142617
theorem B1523507 : Blo 1012602 1523507 := bstep (se 1 (by rfl) ⟨1142630, by rfl⟩ : syracuseStep 1523507 = 2285261) B2285261
theorem B25968437 : Blo 1012602 25968437 := bstep (se 5 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 25968437 = 2434541) B2434541
theorem B1523537 : Blo 1012602 1523537 := bstep (se 2 (by rfl) ⟨571326, by rfl⟩ : syracuseStep 1523537 = 1142653) B1142653
theorem B1523555 : Blo 1012602 1523555 := bstep (se 1 (by rfl) ⟨1142666, by rfl⟩ : syracuseStep 1523555 = 2285333) B2285333
theorem B7716707 : Blo 1012602 7716707 := bstep (se 1 (by rfl) ⟨5787530, by rfl⟩ : syracuseStep 7716707 = 11575061) B11575061
theorem B2572145 : Blo 1012602 2572145 := bstep (se 2 (by rfl) ⟨964554, by rfl⟩ : syracuseStep 2572145 = 1929109) B1929109
theorem B1523585 : Blo 1012602 1523585 := bstep (se 2 (by rfl) ⟨571344, by rfl⟩ : syracuseStep 1523585 = 1142689) B1142689
theorem B1523603 : Blo 1012602 1523603 := bstep (se 1 (by rfl) ⟨1142702, by rfl⟩ : syracuseStep 1523603 = 2285405) B2285405
theorem B2572195 : Blo 1012602 2572195 := bstep (se 1 (by rfl) ⟨1929146, by rfl⟩ : syracuseStep 2572195 = 3858293) B3858293
theorem B1523633 : Blo 1012602 1523633 := bstep (se 2 (by rfl) ⟨571362, by rfl⟩ : syracuseStep 1523633 = 1142725) B1142725
theorem B1523651 : Blo 1012602 1523651 := bstep (se 1 (by rfl) ⟨1142738, by rfl⟩ : syracuseStep 1523651 = 2285477) B2285477
theorem B1523681 : Blo 1012602 1523681 := bstep (se 2 (by rfl) ⟨571380, by rfl⟩ : syracuseStep 1523681 = 1142761) B1142761
theorem B1523699 : Blo 1012602 1523699 := bstep (se 1 (by rfl) ⟨1142774, by rfl⟩ : syracuseStep 1523699 = 2285549) B2285549
theorem B1523729 : Blo 1012602 1523729 := bstep (se 2 (by rfl) ⟨571398, by rfl⟩ : syracuseStep 1523729 = 1142797) B1142797
theorem B1523747 : Blo 1012602 1523747 := bstep (se 1 (by rfl) ⟨1142810, by rfl⟩ : syracuseStep 1523747 = 2285621) B2285621
theorem B3424301 : Blo 1012602 3424301 := bstep (se 3 (by rfl) ⟨642056, by rfl⟩ : syracuseStep 3424301 = 1284113) B1284113
theorem B2572337 : Blo 1012602 2572337 := bstep (se 2 (by rfl) ⟨964626, by rfl⟩ : syracuseStep 2572337 = 1929253) B1929253
theorem B1523777 : Blo 1012602 1523777 := bstep (se 2 (by rfl) ⟨571416, by rfl⟩ : syracuseStep 1523777 = 1142833) B1142833
theorem B1523795 : Blo 1012602 1523795 := bstep (se 1 (by rfl) ⟨1142846, by rfl⟩ : syracuseStep 1523795 = 2285693) B2285693
theorem B3424355 : Blo 1012602 3424355 := bstep (se 1 (by rfl) ⟨2568266, by rfl⟩ : syracuseStep 3424355 = 5136533) B5136533
theorem B1523825 : Blo 1012602 1523825 := bstep (se 2 (by rfl) ⟨571434, by rfl⟩ : syracuseStep 1523825 = 1142869) B1142869
theorem B1523843 : Blo 1012602 1523843 := bstep (se 1 (by rfl) ⟨1142882, by rfl⟩ : syracuseStep 1523843 = 2285765) B2285765
theorem B1523873 : Blo 1012602 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B3293347 : Blo 1012602 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B1523891 : Blo 1012602 1523891 := bstep (se 1 (by rfl) ⟨1142918, by rfl⟩ : syracuseStep 1523891 = 2285837) B2285837
theorem B1523921 : Blo 1012602 1523921 := bstep (se 2 (by rfl) ⟨571470, by rfl⟩ : syracuseStep 1523921 = 1142941) B1142941
theorem B1523939 : Blo 1012602 1523939 := bstep (se 1 (by rfl) ⟨1142954, by rfl⟩ : syracuseStep 1523939 = 2285909) B2285909
theorem B5128433 : Blo 1012602 5128433 := bstep (se 2 (by rfl) ⟨1923162, by rfl⟩ : syracuseStep 5128433 = 3846325) B3846325
theorem B1523969 : Blo 1012602 1523969 := bstep (se 2 (by rfl) ⟨571488, by rfl⟩ : syracuseStep 1523969 = 1142977) B1142977
theorem B1523987 : Blo 1012602 1523987 := bstep (se 1 (by rfl) ⟨1142990, by rfl⟩ : syracuseStep 1523987 = 2285981) B2285981
theorem B1524017 : Blo 1012602 1524017 := bstep (se 2 (by rfl) ⟨571506, by rfl⟩ : syracuseStep 1524017 = 1143013) B1143013
theorem B1524035 : Blo 1012602 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B1524065 : Blo 1012602 1524065 := bstep (se 2 (by rfl) ⟨571524, by rfl⟩ : syracuseStep 1524065 = 1143049) B1143049
theorem B3424625 : Blo 1012602 3424625 := bstep (se 2 (by rfl) ⟨1284234, by rfl⟩ : syracuseStep 3424625 = 2568469) B2568469
theorem B1622387 : Blo 1012602 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B1524083 : Blo 1012602 1524083 := bstep (se 1 (by rfl) ⟨1143062, by rfl⟩ : syracuseStep 1524083 = 2286125) B2286125
theorem B1524113 : Blo 1012602 1524113 := bstep (se 2 (by rfl) ⟨571542, by rfl⟩ : syracuseStep 1524113 = 1143085) B1143085
theorem B1524131 : Blo 1012602 1524131 := bstep (se 1 (by rfl) ⟨1143098, by rfl⟩ : syracuseStep 1524131 = 2286197) B2286197
theorem B1524161 : Blo 1012602 1524161 := bstep (se 2 (by rfl) ⟨571560, by rfl⟩ : syracuseStep 1524161 = 1143121) B1143121
theorem B1524179 : Blo 1012602 1524179 := bstep (se 1 (by rfl) ⟨1143134, by rfl⟩ : syracuseStep 1524179 = 2286269) B2286269
theorem B1524209 : Blo 1012602 1524209 := bstep (se 2 (by rfl) ⟨571578, by rfl⟩ : syracuseStep 1524209 = 1143157) B1143157
theorem B1622515 : Blo 1012602 1622515 := bstep (se 1 (by rfl) ⟨1216886, by rfl⟩ : syracuseStep 1622515 = 2433773) B2433773
theorem B1524227 : Blo 1012602 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B1524257 : Blo 1012602 1524257 := bstep (se 2 (by rfl) ⟨571596, by rfl⟩ : syracuseStep 1524257 = 1143193) B1143193
theorem B1524275 : Blo 1012602 1524275 := bstep (se 1 (by rfl) ⟨1143206, by rfl⟩ : syracuseStep 1524275 = 2286413) B2286413
theorem B1524305 : Blo 1012602 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B1524323 : Blo 1012602 1524323 := bstep (se 1 (by rfl) ⟨1143242, by rfl⟩ : syracuseStep 1524323 = 2286485) B2286485
theorem B1524353 : Blo 1012602 1524353 := bstep (se 2 (by rfl) ⟨571632, by rfl⟩ : syracuseStep 1524353 = 1143265) B1143265
theorem B3293827 : Blo 1012602 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B1524371 : Blo 1012602 1524371 := bstep (se 1 (by rfl) ⟨1143278, by rfl⟩ : syracuseStep 1524371 = 2286557) B2286557
theorem B1524401 : Blo 1012602 1524401 := bstep (se 2 (by rfl) ⟨571650, by rfl⟩ : syracuseStep 1524401 = 1143301) B1143301
theorem B1524419 : Blo 1012602 1524419 := bstep (se 1 (by rfl) ⟨1143314, by rfl⟩ : syracuseStep 1524419 = 2286629) B2286629
theorem B1524449 : Blo 1012602 1524449 := bstep (se 2 (by rfl) ⟨571668, by rfl⟩ : syracuseStep 1524449 = 1143337) B1143337
theorem B1524467 : Blo 1012602 1524467 := bstep (se 1 (by rfl) ⟨1143350, by rfl⟩ : syracuseStep 1524467 = 2286701) B2286701
theorem B1524497 : Blo 1012602 1524497 := bstep (se 2 (by rfl) ⟨571686, by rfl⟩ : syracuseStep 1524497 = 1143373) B1143373
theorem B1524515 : Blo 1012602 1524515 := bstep (se 1 (by rfl) ⟨1143386, by rfl⟩ : syracuseStep 1524515 = 2286773) B2286773
theorem B1524545 : Blo 1012602 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B1524563 : Blo 1012602 1524563 := bstep (se 1 (by rfl) ⟨1143422, by rfl⟩ : syracuseStep 1524563 = 2286845) B2286845
theorem B3130211 : Blo 1012602 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B1524593 : Blo 1012602 1524593 := bstep (se 2 (by rfl) ⟨571722, by rfl⟩ : syracuseStep 1524593 = 1143445) B1143445
theorem B1524611 : Blo 1012602 1524611 := bstep (se 1 (by rfl) ⟨1143458, by rfl⟩ : syracuseStep 1524611 = 2286917) B2286917
theorem B3425165 : Blo 1012602 3425165 := bstep (se 3 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 3425165 = 1284437) B1284437
theorem B1524641 : Blo 1012602 1524641 := bstep (se 2 (by rfl) ⟨571740, by rfl⟩ : syracuseStep 1524641 = 1143481) B1143481
theorem B3851171 : Blo 1012602 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B3851185 : Blo 1012602 3851185 := bstep (se 2 (by rfl) ⟨1444194, by rfl⟩ : syracuseStep 3851185 = 2888389) B2888389
theorem B1524659 : Blo 1012602 1524659 := bstep (se 1 (by rfl) ⟨1143494, by rfl⟩ : syracuseStep 1524659 = 2286989) B2286989
theorem B1852355 : Blo 1012602 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B3425219 : Blo 1012602 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B1524689 : Blo 1012602 1524689 := bstep (se 2 (by rfl) ⟨571758, by rfl⟩ : syracuseStep 1524689 = 1143517) B1143517
theorem B1524707 : Blo 1012602 1524707 := bstep (se 1 (by rfl) ⟨1143530, by rfl⟩ : syracuseStep 1524707 = 2287061) B2287061
theorem B2278385 : Blo 1012602 2278385 := bstep (se 2 (by rfl) ⟨854394, by rfl⟩ : syracuseStep 2278385 = 1708789) B1708789
theorem B1524737 : Blo 1012602 1524737 := bstep (se 2 (by rfl) ⟨571776, by rfl⟩ : syracuseStep 1524737 = 1143553) B1143553
theorem B2278403 : Blo 1012602 2278403 := bstep (se 1 (by rfl) ⟨1708802, by rfl⟩ : syracuseStep 2278403 = 3417605) B3417605
theorem B1524755 : Blo 1012602 1524755 := bstep (se 1 (by rfl) ⟨1143566, by rfl⟩ : syracuseStep 1524755 = 2287133) B2287133
theorem B1623073 : Blo 1012602 1623073 := bstep (se 2 (by rfl) ⟨608652, by rfl⟩ : syracuseStep 1623073 = 1217305) B1217305
theorem B1524785 : Blo 1012602 1524785 := bstep (se 2 (by rfl) ⟨571794, by rfl⟩ : syracuseStep 1524785 = 1143589) B1143589
theorem B2442307 : Blo 1012602 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B1524803 : Blo 1012602 1524803 := bstep (se 1 (by rfl) ⟨1143602, by rfl⟩ : syracuseStep 1524803 = 2287205) B2287205
theorem B6505541 : Blo 1012602 6505541 := bstep (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) B1219789
theorem B1524833 : Blo 1012602 1524833 := bstep (se 2 (by rfl) ⟨571812, by rfl⟩ : syracuseStep 1524833 = 1143625) B1143625
theorem B1524851 : Blo 1012602 1524851 := bstep (se 1 (by rfl) ⟨1143638, by rfl⟩ : syracuseStep 1524851 = 2287277) B2287277
theorem B1524881 : Blo 1012602 1524881 := bstep (se 2 (by rfl) ⟨571830, by rfl⟩ : syracuseStep 1524881 = 1143661) B1143661
theorem B1524899 : Blo 1012602 1524899 := bstep (se 1 (by rfl) ⟨1143674, by rfl⟩ : syracuseStep 1524899 = 2287349) B2287349
theorem B3425489 : Blo 1012602 3425489 := bstep (se 2 (by rfl) ⟨1284558, by rfl⟩ : syracuseStep 3425489 = 2569117) B2569117
theorem B2278673 : Blo 1012602 2278673 := bstep (se 2 (by rfl) ⟨854502, by rfl⟩ : syracuseStep 2278673 = 1709005) B1709005
theorem B2278691 : Blo 1012602 2278691 := bstep (se 1 (by rfl) ⟨1709018, by rfl⟩ : syracuseStep 2278691 = 3418037) B3418037
theorem B2278961 : Blo 1012602 2278961 := bstep (se 2 (by rfl) ⟨854610, by rfl⟩ : syracuseStep 2278961 = 1709221) B1709221
theorem B2278979 : Blo 1012602 2278979 := bstep (se 1 (by rfl) ⟨1709234, by rfl⟩ : syracuseStep 2278979 = 3418469) B3418469
theorem B5129891 : Blo 1012602 5129891 := bstep (se 1 (by rfl) ⟨3847418, by rfl⟩ : syracuseStep 5129891 = 7694837) B7694837
theorem B1623745 : Blo 1012602 1623745 := bstep (se 2 (by rfl) ⟨608904, by rfl⟩ : syracuseStep 1623745 = 1217809) B1217809
theorem B7128803 : Blo 1012602 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B3426029 : Blo 1012602 3426029 := bstep (se 3 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 3426029 = 1284761) B1284761
theorem B3426083 : Blo 1012602 3426083 := bstep (se 1 (by rfl) ⟨2569562, by rfl⟩ : syracuseStep 3426083 = 5139125) B5139125
theorem B2279249 : Blo 1012602 2279249 := bstep (se 2 (by rfl) ⟨854718, by rfl⟩ : syracuseStep 2279249 = 1709437) B1709437
theorem B2279267 : Blo 1012602 2279267 := bstep (se 1 (by rfl) ⟨1709450, by rfl⟩ : syracuseStep 2279267 = 3418901) B3418901
theorem B2312081 : Blo 1012602 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2738083 : Blo 1012602 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B3426353 : Blo 1012602 3426353 := bstep (se 2 (by rfl) ⟨1284882, by rfl⟩ : syracuseStep 3426353 = 2569765) B2569765
theorem B2279537 : Blo 1012602 2279537 := bstep (se 2 (by rfl) ⟨854826, by rfl⟩ : syracuseStep 2279537 = 1709653) B1709653
theorem B2279555 : Blo 1012602 2279555 := bstep (se 1 (by rfl) ⟨1709666, by rfl⟩ : syracuseStep 2279555 = 3419333) B3419333
theorem B2738449 : Blo 1012602 2738449 := bstep (se 2 (by rfl) ⟨1026918, by rfl⟩ : syracuseStep 2738449 = 2053837) B2053837
theorem B3852643 : Blo 1012602 3852643 := bstep (se 1 (by rfl) ⟨2889482, by rfl⟩ : syracuseStep 3852643 = 5778965) B5778965
theorem B2279825 : Blo 1012602 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B2279843 : Blo 1012602 2279843 := bstep (se 1 (by rfl) ⟨1709882, by rfl⟩ : syracuseStep 2279843 = 3419765) B3419765
theorem B5130701 : Blo 1012602 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B1952291 : Blo 1012602 1952291 := bstep (se 1 (by rfl) ⟨1464218, by rfl⟩ : syracuseStep 1952291 = 2928437) B2928437
theorem B3426893 : Blo 1012602 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B3426947 : Blo 1012602 3426947 := bstep (se 1 (by rfl) ⟨2570210, by rfl⟩ : syracuseStep 3426947 = 5140421) B5140421
theorem B2280113 : Blo 1012602 2280113 := bstep (se 2 (by rfl) ⟨855042, by rfl⟩ : syracuseStep 2280113 = 1710085) B1710085
theorem B2280131 : Blo 1012602 2280131 := bstep (se 1 (by rfl) ⟨1710098, by rfl⟩ : syracuseStep 2280131 = 3420197) B3420197
theorem B2345699 : Blo 1012602 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B2738947 : Blo 1012602 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B1624835 : Blo 1012602 1624835 := bstep (se 1 (by rfl) ⟨1218626, by rfl⟩ : syracuseStep 1624835 = 2437253) B2437253
theorem B42257173 : Blo 1012602 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B5786437 : Blo 1012602 5786437 := bstep (se 4 (by rfl) ⟨542478, by rfl⟩ : syracuseStep 5786437 = 1084957) B1084957
theorem B3427217 : Blo 1012602 3427217 := bstep (se 2 (by rfl) ⟨1285206, by rfl⟩ : syracuseStep 3427217 = 2570413) B2570413
theorem B2280401 : Blo 1012602 2280401 := bstep (se 2 (by rfl) ⟨855150, by rfl⟩ : syracuseStep 2280401 = 1710301) B1710301
theorem B2280419 : Blo 1012602 2280419 := bstep (se 1 (by rfl) ⟨1710314, by rfl⟩ : syracuseStep 2280419 = 3420629) B3420629
theorem B2280689 : Blo 1012602 2280689 := bstep (se 2 (by rfl) ⟨855258, by rfl⟩ : syracuseStep 2280689 = 1710517) B1710517
theorem B2280707 : Blo 1012602 2280707 := bstep (se 1 (by rfl) ⟨1710530, by rfl⟩ : syracuseStep 2280707 = 3421061) B3421061
theorem B3427757 : Blo 1012602 3427757 := bstep (se 3 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 3427757 = 1285409) B1285409
theorem B3427811 : Blo 1012602 3427811 := bstep (se 1 (by rfl) ⟨2570858, by rfl⟩ : syracuseStep 3427811 = 5141717) B5141717
theorem B2280977 : Blo 1012602 2280977 := bstep (se 2 (by rfl) ⟨855366, by rfl⟩ : syracuseStep 2280977 = 1710733) B1710733
theorem B2280995 : Blo 1012602 2280995 := bstep (se 1 (by rfl) ⟨1710746, by rfl⟩ : syracuseStep 2280995 = 3421493) B3421493
theorem B1756721 : Blo 1012602 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B1855217 : Blo 1012602 1855217 := bstep (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) B1391413
theorem B3428081 : Blo 1012602 3428081 := bstep (se 2 (by rfl) ⟨1285530, by rfl⟩ : syracuseStep 3428081 = 2571061) B2571061
theorem B2281265 : Blo 1012602 2281265 := bstep (se 2 (by rfl) ⟨855474, by rfl⟩ : syracuseStep 2281265 = 1710949) B1710949
theorem B2281283 : Blo 1012602 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B2281553 : Blo 1012602 2281553 := bstep (se 2 (by rfl) ⟨855582, by rfl⟩ : syracuseStep 2281553 = 1711165) B1711165
theorem B2281571 : Blo 1012602 2281571 := bstep (se 1 (by rfl) ⟨1711178, by rfl⟩ : syracuseStep 2281571 = 3422357) B3422357
theorem B1626257 : Blo 1012602 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B3657955 : Blo 1012602 3657955 := bstep (se 1 (by rfl) ⟨2743466, by rfl⟩ : syracuseStep 3657955 = 5486933) B5486933
theorem B3428621 : Blo 1012602 3428621 := bstep (se 3 (by rfl) ⟨642866, by rfl⟩ : syracuseStep 3428621 = 1285733) B1285733
theorem B2740547 : Blo 1012602 2740547 := bstep (se 1 (by rfl) ⟨2055410, by rfl⟩ : syracuseStep 2740547 = 4110821) B4110821
theorem B3428675 : Blo 1012602 3428675 := bstep (se 1 (by rfl) ⟨2571506, by rfl⟩ : syracuseStep 3428675 = 5143013) B5143013
theorem B2281841 : Blo 1012602 2281841 := bstep (se 2 (by rfl) ⟨855690, by rfl⟩ : syracuseStep 2281841 = 1711381) B1711381
theorem B2281859 : Blo 1012602 2281859 := bstep (se 1 (by rfl) ⟨1711394, by rfl⟩ : syracuseStep 2281859 = 3422789) B3422789
theorem B2314673 : Blo 1012602 2314673 := bstep (se 2 (by rfl) ⟨868002, by rfl⟩ : syracuseStep 2314673 = 1736005) B1736005
theorem B3854861 : Blo 1012602 3854861 := bstep (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) B1445573
theorem B6509105 : Blo 1012602 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B3428945 : Blo 1012602 3428945 := bstep (se 2 (by rfl) ⟨1285854, by rfl⟩ : syracuseStep 3428945 = 2571709) B2571709
theorem B2282129 : Blo 1012602 2282129 := bstep (se 2 (by rfl) ⟨855798, by rfl⟩ : syracuseStep 2282129 = 1711597) B1711597
theorem B2282147 : Blo 1012602 2282147 := bstep (se 1 (by rfl) ⟨1711610, by rfl⟩ : syracuseStep 2282147 = 3423221) B3423221
theorem B2314993 : Blo 1012602 2314993 := bstep (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) B1736245
theorem B5788421 : Blo 1012602 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B2282417 : Blo 1012602 2282417 := bstep (se 2 (by rfl) ⟨855906, by rfl⟩ : syracuseStep 2282417 = 1711813) B1711813
theorem B2282435 : Blo 1012602 2282435 := bstep (se 1 (by rfl) ⟨1711826, by rfl⟩ : syracuseStep 2282435 = 3423653) B3423653
theorem B1627123 : Blo 1012602 1627123 := bstep (se 1 (by rfl) ⟨1220342, by rfl⟩ : syracuseStep 1627123 = 2440685) B2440685
theorem B1758275 : Blo 1012602 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B3429485 : Blo 1012602 3429485 := bstep (se 3 (by rfl) ⟨643028, by rfl⟩ : syracuseStep 3429485 = 1286057) B1286057
theorem B3429539 : Blo 1012602 3429539 := bstep (se 1 (by rfl) ⟨2572154, by rfl⟩ : syracuseStep 3429539 = 5144309) B5144309
theorem B2282705 : Blo 1012602 2282705 := bstep (se 2 (by rfl) ⟨856014, by rfl⟩ : syracuseStep 2282705 = 1712029) B1712029
theorem B2282723 : Blo 1012602 2282723 := bstep (se 1 (by rfl) ⟨1712042, by rfl⟩ : syracuseStep 2282723 = 3424085) B3424085
theorem B1627379 : Blo 1012602 1627379 := bstep (se 1 (by rfl) ⟨1220534, by rfl⟩ : syracuseStep 1627379 = 2441069) B2441069
theorem B5133617 : Blo 1012602 5133617 := bstep (se 2 (by rfl) ⟨1925106, by rfl⟩ : syracuseStep 5133617 = 3850213) B3850213
theorem B1922449 : Blo 1012602 1922449 := bstep (se 2 (by rfl) ⟨720918, by rfl⟩ : syracuseStep 1922449 = 1441837) B1441837
theorem B3429809 : Blo 1012602 3429809 := bstep (se 2 (by rfl) ⟨1286178, by rfl⟩ : syracuseStep 3429809 = 2572357) B2572357
theorem B2282993 : Blo 1012602 2282993 := bstep (se 2 (by rfl) ⟨856122, by rfl⟩ : syracuseStep 2282993 = 1712245) B1712245
theorem B2283011 : Blo 1012602 2283011 := bstep (se 1 (by rfl) ⟨1712258, by rfl⟩ : syracuseStep 2283011 = 3424517) B3424517
theorem B1922609 : Blo 1012602 1922609 := bstep (se 2 (by rfl) ⟨720978, by rfl⟩ : syracuseStep 1922609 = 1441957) B1441957
theorem B14636771 : Blo 1012602 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B2283281 : Blo 1012602 2283281 := bstep (se 2 (by rfl) ⟨856230, by rfl⟩ : syracuseStep 2283281 = 1712461) B1712461
theorem B2283299 : Blo 1012602 2283299 := bstep (se 1 (by rfl) ⟨1712474, by rfl⟩ : syracuseStep 2283299 = 3424949) B3424949
theorem B2742083 : Blo 1012602 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B1923011 : Blo 1012602 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B3430349 : Blo 1012602 3430349 := bstep (se 3 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 3430349 = 1286381) B1286381
theorem B6510563 : Blo 1012602 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B3430403 : Blo 1012602 3430403 := bstep (se 1 (by rfl) ⟨2572802, by rfl⟩ : syracuseStep 3430403 = 5145605) B5145605
theorem B2283569 : Blo 1012602 2283569 := bstep (se 2 (by rfl) ⟨856338, by rfl⟩ : syracuseStep 2283569 = 1712677) B1712677
theorem B2283587 : Blo 1012602 2283587 := bstep (se 1 (by rfl) ⟨1712690, by rfl⟩ : syracuseStep 2283587 = 3425381) B3425381
theorem B2054243 : Blo 1012602 2054243 := bstep (se 1 (by rfl) ⟨1540682, by rfl⟩ : syracuseStep 2054243 = 3081365) B3081365
theorem B1628353 : Blo 1012602 1628353 := bstep (se 2 (by rfl) ⟨610632, by rfl⟩ : syracuseStep 1628353 = 1221265) B1221265
theorem B5560525 : Blo 1012602 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B3430673 : Blo 1012602 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B12998981 : Blo 1012602 12998981 := bstep (se 4 (by rfl) ⟨1218654, by rfl⟩ : syracuseStep 12998981 = 2437309) B2437309
theorem B2283857 : Blo 1012602 2283857 := bstep (se 2 (by rfl) ⟨856446, by rfl⟩ : syracuseStep 2283857 = 1712893) B1712893
theorem B2283875 : Blo 1012602 2283875 := bstep (se 1 (by rfl) ⟨1712906, by rfl⟩ : syracuseStep 2283875 = 3425813) B3425813
theorem B9263501 : Blo 1012602 9263501 := bstep (se 3 (by rfl) ⟨1736906, by rfl⟩ : syracuseStep 9263501 = 3473813) B3473813
theorem B1563107 : Blo 1012602 1563107 := bstep (se 1 (by rfl) ⟨1172330, by rfl⟩ : syracuseStep 1563107 = 2344661) B2344661
theorem B2316899 : Blo 1012602 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B2284145 : Blo 1012602 2284145 := bstep (se 2 (by rfl) ⟨856554, by rfl⟩ : syracuseStep 2284145 = 1713109) B1713109
theorem B2284163 : Blo 1012602 2284163 := bstep (se 1 (by rfl) ⟨1713122, by rfl⟩ : syracuseStep 2284163 = 3426245) B3426245
theorem B7690949 : Blo 1012602 7690949 := bstep (se 4 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 7690949 = 1442053) B1442053
theorem B5135075 : Blo 1012602 5135075 := bstep (se 1 (by rfl) ⟨3851306, by rfl⟩ : syracuseStep 5135075 = 7702613) B7702613
theorem B1923907 : Blo 1012602 1923907 := bstep (se 1 (by rfl) ⟨1442930, by rfl⟩ : syracuseStep 1923907 = 2885861) B2885861
theorem B2284433 : Blo 1012602 2284433 := bstep (se 2 (by rfl) ⟨856662, by rfl⟩ : syracuseStep 2284433 = 1713325) B1713325
theorem B2284451 : Blo 1012602 2284451 := bstep (se 1 (by rfl) ⟨1713338, by rfl⟩ : syracuseStep 2284451 = 3426677) B3426677
theorem B1924067 : Blo 1012602 1924067 := bstep (se 1 (by rfl) ⟨1443050, by rfl⟩ : syracuseStep 1924067 = 2886101) B2886101
theorem B24697997 : Blo 1012602 24697997 := bstep (se 3 (by rfl) ⟨4630874, by rfl⟩ : syracuseStep 24697997 = 9261749) B9261749
theorem B2284721 : Blo 1012602 2284721 := bstep (se 2 (by rfl) ⟨856770, by rfl⟩ : syracuseStep 2284721 = 1713541) B1713541
theorem B2284739 : Blo 1012602 2284739 := bstep (se 1 (by rfl) ⟨1713554, by rfl⟩ : syracuseStep 2284739 = 3427109) B3427109
theorem B2055395 : Blo 1012602 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B3857777 : Blo 1012602 3857777 := bstep (se 2 (by rfl) ⟨1446666, by rfl⟩ : syracuseStep 3857777 = 2893333) B2893333
theorem B2088355 : Blo 1012602 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B2285009 : Blo 1012602 2285009 := bstep (se 2 (by rfl) ⟨856878, by rfl⟩ : syracuseStep 2285009 = 1713757) B1713757
theorem B2285027 : Blo 1012602 2285027 := bstep (se 1 (by rfl) ⟨1713770, by rfl⟩ : syracuseStep 2285027 = 3427541) B3427541
theorem B5135885 : Blo 1012602 5135885 := bstep (se 3 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 5135885 = 1925957) B1925957
theorem B2743985 : Blo 1012602 2743985 := bstep (se 2 (by rfl) ⟨1028994, by rfl⟩ : syracuseStep 2743985 = 2057989) B2057989
theorem B2285297 : Blo 1012602 2285297 := bstep (se 2 (by rfl) ⟨856986, by rfl⟩ : syracuseStep 2285297 = 1713973) B1713973
theorem B2285315 : Blo 1012602 2285315 := bstep (se 1 (by rfl) ⟨1713986, by rfl⟩ : syracuseStep 2285315 = 3427973) B3427973
theorem B1925137 : Blo 1012602 1925137 := bstep (se 2 (by rfl) ⟨721926, by rfl⟩ : syracuseStep 1925137 = 1443853) B1443853
theorem B2285585 : Blo 1012602 2285585 := bstep (se 2 (by rfl) ⟨857094, by rfl⟩ : syracuseStep 2285585 = 1714189) B1714189
theorem B2285603 : Blo 1012602 2285603 := bstep (se 1 (by rfl) ⟨1714202, by rfl⟩ : syracuseStep 2285603 = 3428405) B3428405
theorem B1466435 : Blo 1012602 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B13197539 : Blo 1012602 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B2285873 : Blo 1012602 2285873 := bstep (se 2 (by rfl) ⟨857202, by rfl⟩ : syracuseStep 2285873 = 1714405) B1714405
theorem B2285891 : Blo 1012602 2285891 := bstep (se 1 (by rfl) ⟨1714418, by rfl⟩ : syracuseStep 2285891 = 3428837) B3428837
theorem B1139251 : Blo 1012602 1139251 := bstep (se 1 (by rfl) ⟨854438, by rfl⟩ : syracuseStep 1139251 = 1708877) B1708877
theorem B2286161 : Blo 1012602 2286161 := bstep (se 2 (by rfl) ⟨857310, by rfl⟩ : syracuseStep 2286161 = 1714621) B1714621
theorem B2286179 : Blo 1012602 2286179 := bstep (se 1 (by rfl) ⟨1714634, by rfl⟩ : syracuseStep 2286179 = 3429269) B3429269
theorem B1466993 : Blo 1012602 1466993 := bstep (se 2 (by rfl) ⟨550122, by rfl⟩ : syracuseStep 1466993 = 1100245) B1100245
theorem B1139395 : Blo 1012602 1139395 := bstep (se 1 (by rfl) ⟨854546, by rfl⟩ : syracuseStep 1139395 = 1709093) B1709093
theorem B3859235 : Blo 1012602 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B1139539 : Blo 1012602 1139539 := bstep (se 1 (by rfl) ⟨854654, by rfl⟩ : syracuseStep 1139539 = 1709309) B1709309
theorem B2286449 : Blo 1012602 2286449 := bstep (se 2 (by rfl) ⟨857418, by rfl⟩ : syracuseStep 2286449 = 1714837) B1714837
theorem B2286467 : Blo 1012602 2286467 := bstep (se 1 (by rfl) ⟨1714850, by rfl⟩ : syracuseStep 2286467 = 3429701) B3429701
theorem B1139683 : Blo 1012602 1139683 := bstep (se 1 (by rfl) ⟨854762, by rfl⟩ : syracuseStep 1139683 = 1709525) B1709525
theorem B1926193 : Blo 1012602 1926193 := bstep (se 2 (by rfl) ⟨722322, by rfl⟩ : syracuseStep 1926193 = 1444645) B1444645
theorem B7300165 : Blo 1012602 7300165 := bstep (se 4 (by rfl) ⟨684390, by rfl⟩ : syracuseStep 7300165 = 1368781) B1368781
theorem B1139827 : Blo 1012602 1139827 := bstep (se 1 (by rfl) ⟨854870, by rfl⟩ : syracuseStep 1139827 = 1709741) B1709741
theorem B26338445 : Blo 1012602 26338445 := bstep (se 3 (by rfl) ⟨4938458, by rfl⟩ : syracuseStep 26338445 = 9876917) B9876917
theorem B2286737 : Blo 1012602 2286737 := bstep (se 2 (by rfl) ⟨857526, by rfl⟩ : syracuseStep 2286737 = 1715053) B1715053
theorem B2286755 : Blo 1012602 2286755 := bstep (se 1 (by rfl) ⟨1715066, by rfl⟩ : syracuseStep 2286755 = 3430133) B3430133
theorem B2745521 : Blo 1012602 2745521 := bstep (se 2 (by rfl) ⟨1029570, by rfl⟩ : syracuseStep 2745521 = 2059141) B2059141
theorem B7628017 : Blo 1012602 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B1139971 : Blo 1012602 1139971 := bstep (se 1 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 1139971 = 1709957) B1709957
theorem B1140115 : Blo 1012602 1140115 := bstep (se 1 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 1140115 = 1710173) B1710173
theorem B2287025 : Blo 1012602 2287025 := bstep (se 2 (by rfl) ⟨857634, by rfl⟩ : syracuseStep 2287025 = 1715269) B1715269
theorem B1926595 : Blo 1012602 1926595 := bstep (se 1 (by rfl) ⟨1444946, by rfl⟩ : syracuseStep 1926595 = 2889893) B2889893
theorem B2287043 : Blo 1012602 2287043 := bstep (se 1 (by rfl) ⟨1715282, by rfl⟩ : syracuseStep 2287043 = 3430565) B3430565
theorem B1926641 : Blo 1012602 1926641 := bstep (se 2 (by rfl) ⟨722490, by rfl⟩ : syracuseStep 1926641 = 1444981) B1444981
theorem B1140259 : Blo 1012602 1140259 := bstep (se 1 (by rfl) ⟨855194, by rfl⟩ : syracuseStep 1140259 = 1710389) B1710389
theorem B1140403 : Blo 1012602 1140403 := bstep (se 1 (by rfl) ⟨855302, by rfl⟩ : syracuseStep 1140403 = 1710605) B1710605
theorem B2287313 : Blo 1012602 2287313 := bstep (se 2 (by rfl) ⟨857742, by rfl⟩ : syracuseStep 2287313 = 1715485) B1715485
theorem B2287331 : Blo 1012602 2287331 := bstep (se 1 (by rfl) ⟨1715498, by rfl⟩ : syracuseStep 2287331 = 3430997) B3430997
theorem B1926929 : Blo 1012602 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B1140547 : Blo 1012602 1140547 := bstep (se 1 (by rfl) ⟨855410, by rfl⟩ : syracuseStep 1140547 = 1710821) B1710821
theorem B1140691 : Blo 1012602 1140691 := bstep (se 1 (by rfl) ⟨855518, by rfl⟩ : syracuseStep 1140691 = 1711037) B1711037
theorem B1370209 : Blo 1012602 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B1140835 : Blo 1012602 1140835 := bstep (se 1 (by rfl) ⟨855626, by rfl⟩ : syracuseStep 1140835 = 1711253) B1711253
theorem B1140979 : Blo 1012602 1140979 := bstep (se 1 (by rfl) ⟨855734, by rfl⟩ : syracuseStep 1140979 = 1711469) B1711469
theorem B5138801 : Blo 1012602 5138801 := bstep (se 2 (by rfl) ⟨1927050, by rfl⟩ : syracuseStep 5138801 = 3854101) B3854101
theorem B1141123 : Blo 1012602 1141123 := bstep (se 1 (by rfl) ⟨855842, by rfl⟩ : syracuseStep 1141123 = 1711685) B1711685
theorem B1829251 : Blo 1012602 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1927651 : Blo 1012602 1927651 := bstep (se 1 (by rfl) ⟨1445738, by rfl⟩ : syracuseStep 1927651 = 2891477) B2891477
theorem B1141267 : Blo 1012602 1141267 := bstep (se 1 (by rfl) ⟨855950, by rfl⟩ : syracuseStep 1141267 = 1711901) B1711901
theorem B1141411 : Blo 1012602 1141411 := bstep (se 1 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 1141411 = 1712117) B1712117
theorem B1141555 : Blo 1012602 1141555 := bstep (se 1 (by rfl) ⟨856166, by rfl⟩ : syracuseStep 1141555 = 1712333) B1712333
theorem B1371025 : Blo 1012602 1371025 := bstep (se 2 (by rfl) ⟨514134, by rfl⟩ : syracuseStep 1371025 = 1028269) B1028269
theorem B1928099 : Blo 1012602 1928099 := bstep (se 1 (by rfl) ⟨1446074, by rfl⟩ : syracuseStep 1928099 = 2892149) B2892149
theorem B1141699 : Blo 1012602 1141699 := bstep (se 1 (by rfl) ⟨856274, by rfl⟩ : syracuseStep 1141699 = 1712549) B1712549
theorem B1141843 : Blo 1012602 1141843 := bstep (se 1 (by rfl) ⟨856382, by rfl⟩ : syracuseStep 1141843 = 1712765) B1712765
theorem B1928387 : Blo 1012602 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B1141987 : Blo 1012602 1141987 := bstep (se 1 (by rfl) ⟨856490, by rfl⟩ : syracuseStep 1141987 = 1712981) B1712981
theorem B9268465 : Blo 1012602 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B1142131 : Blo 1012602 1142131 := bstep (se 1 (by rfl) ⟨856598, by rfl⟩ : syracuseStep 1142131 = 1713197) B1713197
theorem B1830289 : Blo 1012602 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1142275 : Blo 1012602 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B3468835 : Blo 1012602 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B1142419 : Blo 1012602 1142419 := bstep (se 1 (by rfl) ⟨856814, by rfl⟩ : syracuseStep 1142419 = 1713629) B1713629
theorem B8679109 : Blo 1012602 8679109 := bstep (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) B1627333
theorem B41676565 : Blo 1012602 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B5140259 : Blo 1012602 5140259 := bstep (se 1 (by rfl) ⟨3855194, by rfl⟩ : syracuseStep 5140259 = 7710389) B7710389
theorem B1142563 : Blo 1012602 1142563 := bstep (se 1 (by rfl) ⟨856922, by rfl⟩ : syracuseStep 1142563 = 1713845) B1713845
theorem B6254405 : Blo 1012602 6254405 := bstep (se 4 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 6254405 = 1172701) B1172701
theorem B1142707 : Blo 1012602 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B1142851 : Blo 1012602 1142851 := bstep (se 1 (by rfl) ⟨857138, by rfl⟩ : syracuseStep 1142851 = 1714277) B1714277
theorem B1929329 : Blo 1012602 1929329 := bstep (se 2 (by rfl) ⟨723498, by rfl⟩ : syracuseStep 1929329 = 1446997) B1446997
theorem B1372339 : Blo 1012602 1372339 := bstep (se 1 (by rfl) ⟨1029254, by rfl⟩ : syracuseStep 1372339 = 2058509) B2058509
theorem B1142995 : Blo 1012602 1142995 := bstep (se 1 (by rfl) ⟨857246, by rfl⟩ : syracuseStep 1142995 = 1714493) B1714493
theorem B2060561 : Blo 1012602 2060561 := bstep (se 2 (by rfl) ⟨772710, by rfl⟩ : syracuseStep 2060561 = 1545421) B1545421
theorem B1143139 : Blo 1012602 1143139 := bstep (se 1 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 1143139 = 1714709) B1714709
theorem B7696781 : Blo 1012602 7696781 := bstep (se 3 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 7696781 = 2886293) B2886293
theorem B18510221 : Blo 1012602 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B1143283 : Blo 1012602 1143283 := bstep (se 1 (by rfl) ⟨857462, by rfl⟩ : syracuseStep 1143283 = 1714925) B1714925
theorem B5141069 : Blo 1012602 5141069 := bstep (se 3 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 5141069 = 1927901) B1927901
theorem B1143427 : Blo 1012602 1143427 := bstep (se 1 (by rfl) ⟨857570, by rfl⟩ : syracuseStep 1143427 = 1715141) B1715141
theorem B1143571 : Blo 1012602 1143571 := bstep (se 1 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 1143571 = 1715357) B1715357
theorem B1012611 : Blo 1012602 1012611 := bstep (se 1 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 1012611 = 1518917) B1518917
theorem B1012627 : Blo 1012602 1012627 := bstep (se 1 (by rfl) ⟨759470, by rfl⟩ : syracuseStep 1012627 = 1518941) B1518941
theorem B1012643 : Blo 1012602 1012643 := bstep (se 1 (by rfl) ⟨759482, by rfl⟩ : syracuseStep 1012643 = 1518965) B1518965
theorem B1012659 : Blo 1012602 1012659 := bstep (se 1 (by rfl) ⟨759494, by rfl⟩ : syracuseStep 1012659 = 1518989) B1518989
theorem B1012675 : Blo 1012602 1012675 := bstep (se 1 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 1012675 = 1519013) B1519013
theorem B1012691 : Blo 1012602 1012691 := bstep (se 1 (by rfl) ⟨759518, by rfl⟩ : syracuseStep 1012691 = 1519037) B1519037
theorem B1012707 : Blo 1012602 1012707 := bstep (se 1 (by rfl) ⟨759530, by rfl⟩ : syracuseStep 1012707 = 1519061) B1519061
theorem B1012723 : Blo 1012602 1012723 := bstep (se 1 (by rfl) ⟨759542, by rfl⟩ : syracuseStep 1012723 = 1519085) B1519085
theorem B1012739 : Blo 1012602 1012739 := bstep (se 1 (by rfl) ⟨759554, by rfl⟩ : syracuseStep 1012739 = 1519109) B1519109
theorem B1012755 : Blo 1012602 1012755 := bstep (se 1 (by rfl) ⟨759566, by rfl⟩ : syracuseStep 1012755 = 1519133) B1519133
theorem B1012771 : Blo 1012602 1012771 := bstep (se 1 (by rfl) ⟨759578, by rfl⟩ : syracuseStep 1012771 = 1519157) B1519157
theorem B1012787 : Blo 1012602 1012787 := bstep (se 1 (by rfl) ⟨759590, by rfl⟩ : syracuseStep 1012787 = 1519181) B1519181
theorem B1012803 : Blo 1012602 1012803 := bstep (se 1 (by rfl) ⟨759602, by rfl⟩ : syracuseStep 1012803 = 1519205) B1519205
theorem B1012819 : Blo 1012602 1012819 := bstep (se 1 (by rfl) ⟨759614, by rfl⟩ : syracuseStep 1012819 = 1519229) B1519229
theorem B1012835 : Blo 1012602 1012835 := bstep (se 1 (by rfl) ⟨759626, by rfl⟩ : syracuseStep 1012835 = 1519253) B1519253
theorem B1012851 : Blo 1012602 1012851 := bstep (se 1 (by rfl) ⟨759638, by rfl⟩ : syracuseStep 1012851 = 1519277) B1519277
theorem B1012867 : Blo 1012602 1012867 := bstep (se 1 (by rfl) ⟨759650, by rfl⟩ : syracuseStep 1012867 = 1519301) B1519301
theorem B1012883 : Blo 1012602 1012883 := bstep (se 1 (by rfl) ⟨759662, by rfl⟩ : syracuseStep 1012883 = 1519325) B1519325
theorem B1012899 : Blo 1012602 1012899 := bstep (se 1 (by rfl) ⟨759674, by rfl⟩ : syracuseStep 1012899 = 1519349) B1519349
theorem B1012915 : Blo 1012602 1012915 := bstep (se 1 (by rfl) ⟨759686, by rfl⟩ : syracuseStep 1012915 = 1519373) B1519373
theorem B1373377 : Blo 1012602 1373377 := bstep (se 2 (by rfl) ⟨515016, by rfl⟩ : syracuseStep 1373377 = 1030033) B1030033
theorem B1012931 : Blo 1012602 1012931 := bstep (se 1 (by rfl) ⟨759698, by rfl⟩ : syracuseStep 1012931 = 1519397) B1519397
theorem B1012947 : Blo 1012602 1012947 := bstep (se 1 (by rfl) ⟨759710, by rfl⟩ : syracuseStep 1012947 = 1519421) B1519421
theorem B1012963 : Blo 1012602 1012963 := bstep (se 1 (by rfl) ⟨759722, by rfl⟩ : syracuseStep 1012963 = 1519445) B1519445
theorem B1012979 : Blo 1012602 1012979 := bstep (se 1 (by rfl) ⟨759734, by rfl⟩ : syracuseStep 1012979 = 1519469) B1519469
theorem B1012995 : Blo 1012602 1012995 := bstep (se 1 (by rfl) ⟨759746, by rfl⟩ : syracuseStep 1012995 = 1519493) B1519493
theorem B1013011 : Blo 1012602 1013011 := bstep (se 1 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 1013011 = 1519517) B1519517
theorem B1013027 : Blo 1012602 1013027 := bstep (se 1 (by rfl) ⟨759770, by rfl⟩ : syracuseStep 1013027 = 1519541) B1519541
theorem B1013043 : Blo 1012602 1013043 := bstep (se 1 (by rfl) ⟨759782, by rfl⟩ : syracuseStep 1013043 = 1519565) B1519565
theorem B1013059 : Blo 1012602 1013059 := bstep (se 1 (by rfl) ⟨759794, by rfl⟩ : syracuseStep 1013059 = 1519589) B1519589
theorem B4879693 : Blo 1012602 4879693 := bstep (se 3 (by rfl) ⟨914942, by rfl⟩ : syracuseStep 4879693 = 1829885) B1829885
theorem B1013075 : Blo 1012602 1013075 := bstep (se 1 (by rfl) ⟨759806, by rfl⟩ : syracuseStep 1013075 = 1519613) B1519613
theorem B1013091 : Blo 1012602 1013091 := bstep (se 1 (by rfl) ⟨759818, by rfl⟩ : syracuseStep 1013091 = 1519637) B1519637
theorem B1373539 : Blo 1012602 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B1013107 : Blo 1012602 1013107 := bstep (se 1 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 1013107 = 1519661) B1519661
theorem B1013123 : Blo 1012602 1013123 := bstep (se 1 (by rfl) ⟨759842, by rfl⟩ : syracuseStep 1013123 = 1519685) B1519685
theorem B1013139 : Blo 1012602 1013139 := bstep (se 1 (by rfl) ⟨759854, by rfl⟩ : syracuseStep 1013139 = 1519709) B1519709
theorem B1013155 : Blo 1012602 1013155 := bstep (se 1 (by rfl) ⟨759866, by rfl⟩ : syracuseStep 1013155 = 1519733) B1519733
theorem B1013171 : Blo 1012602 1013171 := bstep (se 1 (by rfl) ⟨759878, by rfl⟩ : syracuseStep 1013171 = 1519757) B1519757
theorem B1013187 : Blo 1012602 1013187 := bstep (se 1 (by rfl) ⟨759890, by rfl⟩ : syracuseStep 1013187 = 1519781) B1519781
theorem B1013203 : Blo 1012602 1013203 := bstep (se 1 (by rfl) ⟨759902, by rfl⟩ : syracuseStep 1013203 = 1519805) B1519805
theorem B1013219 : Blo 1012602 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B1013235 : Blo 1012602 1013235 := bstep (se 1 (by rfl) ⟨759926, by rfl⟩ : syracuseStep 1013235 = 1519853) B1519853
theorem B1013251 : Blo 1012602 1013251 := bstep (se 1 (by rfl) ⟨759938, by rfl⟩ : syracuseStep 1013251 = 1519877) B1519877
theorem B1013267 : Blo 1012602 1013267 := bstep (se 1 (by rfl) ⟨759950, by rfl⟩ : syracuseStep 1013267 = 1519901) B1519901
theorem B1013283 : Blo 1012602 1013283 := bstep (se 1 (by rfl) ⟨759962, by rfl⟩ : syracuseStep 1013283 = 1519925) B1519925
theorem B1013299 : Blo 1012602 1013299 := bstep (se 1 (by rfl) ⟨759974, by rfl⟩ : syracuseStep 1013299 = 1519949) B1519949
theorem B1013315 : Blo 1012602 1013315 := bstep (se 1 (by rfl) ⟨759986, by rfl⟩ : syracuseStep 1013315 = 1519973) B1519973
theorem B5797453 : Blo 1012602 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B1013331 : Blo 1012602 1013331 := bstep (se 1 (by rfl) ⟨759998, by rfl⟩ : syracuseStep 1013331 = 1519997) B1519997
theorem B1013347 : Blo 1012602 1013347 := bstep (se 1 (by rfl) ⟨760010, by rfl⟩ : syracuseStep 1013347 = 1520021) B1520021
theorem B1013363 : Blo 1012602 1013363 := bstep (se 1 (by rfl) ⟨760022, by rfl⟩ : syracuseStep 1013363 = 1520045) B1520045
theorem B1013379 : Blo 1012602 1013379 := bstep (se 1 (by rfl) ⟨760034, by rfl⟩ : syracuseStep 1013379 = 1520069) B1520069
theorem B1013395 : Blo 1012602 1013395 := bstep (se 1 (by rfl) ⟨760046, by rfl⟩ : syracuseStep 1013395 = 1520093) B1520093
theorem B1013411 : Blo 1012602 1013411 := bstep (se 1 (by rfl) ⟨760058, by rfl⟩ : syracuseStep 1013411 = 1520117) B1520117
theorem B1013427 : Blo 1012602 1013427 := bstep (se 1 (by rfl) ⟨760070, by rfl⟩ : syracuseStep 1013427 = 1520141) B1520141
theorem B1013443 : Blo 1012602 1013443 := bstep (se 1 (by rfl) ⟨760082, by rfl⟩ : syracuseStep 1013443 = 1520165) B1520165
theorem B1013459 : Blo 1012602 1013459 := bstep (se 1 (by rfl) ⟨760094, by rfl⟩ : syracuseStep 1013459 = 1520189) B1520189
theorem B1013475 : Blo 1012602 1013475 := bstep (se 1 (by rfl) ⟨760106, by rfl⟩ : syracuseStep 1013475 = 1520213) B1520213
theorem B1013491 : Blo 1012602 1013491 := bstep (se 1 (by rfl) ⟨760118, by rfl⟩ : syracuseStep 1013491 = 1520237) B1520237
theorem B1013507 : Blo 1012602 1013507 := bstep (se 1 (by rfl) ⟨760130, by rfl⟩ : syracuseStep 1013507 = 1520261) B1520261
theorem B1013523 : Blo 1012602 1013523 := bstep (se 1 (by rfl) ⟨760142, by rfl⟩ : syracuseStep 1013523 = 1520285) B1520285
theorem B1013539 : Blo 1012602 1013539 := bstep (se 1 (by rfl) ⟨760154, by rfl⟩ : syracuseStep 1013539 = 1520309) B1520309
theorem B1013555 : Blo 1012602 1013555 := bstep (se 1 (by rfl) ⟨760166, by rfl⟩ : syracuseStep 1013555 = 1520333) B1520333
theorem B1013571 : Blo 1012602 1013571 := bstep (se 1 (by rfl) ⟨760178, by rfl⟩ : syracuseStep 1013571 = 1520357) B1520357
theorem B1013587 : Blo 1012602 1013587 := bstep (se 1 (by rfl) ⟨760190, by rfl⟩ : syracuseStep 1013587 = 1520381) B1520381
theorem B1013603 : Blo 1012602 1013603 := bstep (se 1 (by rfl) ⟨760202, by rfl⟩ : syracuseStep 1013603 = 1520405) B1520405
theorem B1013619 : Blo 1012602 1013619 := bstep (se 1 (by rfl) ⟨760214, by rfl⟩ : syracuseStep 1013619 = 1520429) B1520429
theorem B1013635 : Blo 1012602 1013635 := bstep (se 1 (by rfl) ⟨760226, by rfl⟩ : syracuseStep 1013635 = 1520453) B1520453
theorem B7796621 : Blo 1012602 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B1013651 : Blo 1012602 1013651 := bstep (se 1 (by rfl) ⟨760238, by rfl⟩ : syracuseStep 1013651 = 1520477) B1520477
theorem B1013667 : Blo 1012602 1013667 := bstep (se 1 (by rfl) ⟨760250, by rfl⟩ : syracuseStep 1013667 = 1520501) B1520501
theorem B5207971 : Blo 1012602 5207971 := bstep (se 1 (by rfl) ⟨3905978, by rfl⟩ : syracuseStep 5207971 = 7811957) B7811957
theorem B1013683 : Blo 1012602 1013683 := bstep (se 1 (by rfl) ⟨760262, by rfl⟩ : syracuseStep 1013683 = 1520525) B1520525
theorem B1013699 : Blo 1012602 1013699 := bstep (se 1 (by rfl) ⟨760274, by rfl⟩ : syracuseStep 1013699 = 1520549) B1520549
theorem B1013715 : Blo 1012602 1013715 := bstep (se 1 (by rfl) ⟨760286, by rfl⟩ : syracuseStep 1013715 = 1520573) B1520573
theorem B1013731 : Blo 1012602 1013731 := bstep (se 1 (by rfl) ⟨760298, by rfl⟩ : syracuseStep 1013731 = 1520597) B1520597
theorem B1013747 : Blo 1012602 1013747 := bstep (se 1 (by rfl) ⟨760310, by rfl⟩ : syracuseStep 1013747 = 1520621) B1520621
theorem B1013763 : Blo 1012602 1013763 := bstep (se 1 (by rfl) ⟨760322, by rfl⟩ : syracuseStep 1013763 = 1520645) B1520645
theorem B1013779 : Blo 1012602 1013779 := bstep (se 1 (by rfl) ⟨760334, by rfl⟩ : syracuseStep 1013779 = 1520669) B1520669
theorem B1013795 : Blo 1012602 1013795 := bstep (se 1 (by rfl) ⟨760346, by rfl⟩ : syracuseStep 1013795 = 1520693) B1520693
theorem B1013811 : Blo 1012602 1013811 := bstep (se 1 (by rfl) ⟨760358, by rfl⟩ : syracuseStep 1013811 = 1520717) B1520717
theorem B1013827 : Blo 1012602 1013827 := bstep (se 1 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 1013827 = 1520741) B1520741
theorem B1013843 : Blo 1012602 1013843 := bstep (se 1 (by rfl) ⟨760382, by rfl⟩ : syracuseStep 1013843 = 1520765) B1520765
theorem B1013859 : Blo 1012602 1013859 := bstep (se 1 (by rfl) ⟨760394, by rfl⟩ : syracuseStep 1013859 = 1520789) B1520789
theorem B1013875 : Blo 1012602 1013875 := bstep (se 1 (by rfl) ⟨760406, by rfl⟩ : syracuseStep 1013875 = 1520813) B1520813
theorem B1013891 : Blo 1012602 1013891 := bstep (se 1 (by rfl) ⟨760418, by rfl⟩ : syracuseStep 1013891 = 1520837) B1520837
theorem B1013907 : Blo 1012602 1013907 := bstep (se 1 (by rfl) ⟨760430, by rfl⟩ : syracuseStep 1013907 = 1520861) B1520861
theorem B1013923 : Blo 1012602 1013923 := bstep (se 1 (by rfl) ⟨760442, by rfl⟩ : syracuseStep 1013923 = 1520885) B1520885
theorem B1013939 : Blo 1012602 1013939 := bstep (se 1 (by rfl) ⟨760454, by rfl⟩ : syracuseStep 1013939 = 1520909) B1520909
theorem B1013955 : Blo 1012602 1013955 := bstep (se 1 (by rfl) ⟨760466, by rfl⟩ : syracuseStep 1013955 = 1520933) B1520933
theorem B1013971 : Blo 1012602 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B1013987 : Blo 1012602 1013987 := bstep (se 1 (by rfl) ⟨760490, by rfl⟩ : syracuseStep 1013987 = 1520981) B1520981
theorem B11729123 : Blo 1012602 11729123 := bstep (se 1 (by rfl) ⟨8796842, by rfl⟩ : syracuseStep 11729123 = 17593685) B17593685
theorem B1014003 : Blo 1012602 1014003 := bstep (se 1 (by rfl) ⟨760502, by rfl⟩ : syracuseStep 1014003 = 1521005) B1521005
theorem B1014019 : Blo 1012602 1014019 := bstep (se 1 (by rfl) ⟨760514, by rfl⟩ : syracuseStep 1014019 = 1521029) B1521029
theorem B1014035 : Blo 1012602 1014035 := bstep (se 1 (by rfl) ⟨760526, by rfl⟩ : syracuseStep 1014035 = 1521053) B1521053
theorem B1014051 : Blo 1012602 1014051 := bstep (se 1 (by rfl) ⟨760538, by rfl⟩ : syracuseStep 1014051 = 1521077) B1521077
theorem B1014067 : Blo 1012602 1014067 := bstep (se 1 (by rfl) ⟨760550, by rfl⟩ : syracuseStep 1014067 = 1521101) B1521101
theorem B1014083 : Blo 1012602 1014083 := bstep (se 1 (by rfl) ⟨760562, by rfl⟩ : syracuseStep 1014083 = 1521125) B1521125
theorem B1014099 : Blo 1012602 1014099 := bstep (se 1 (by rfl) ⟨760574, by rfl⟩ : syracuseStep 1014099 = 1521149) B1521149
theorem B1014115 : Blo 1012602 1014115 := bstep (se 1 (by rfl) ⟨760586, by rfl⟩ : syracuseStep 1014115 = 1521173) B1521173
theorem B1014131 : Blo 1012602 1014131 := bstep (se 1 (by rfl) ⟨760598, by rfl⟩ : syracuseStep 1014131 = 1521197) B1521197
theorem B1014147 : Blo 1012602 1014147 := bstep (se 1 (by rfl) ⟨760610, by rfl⟩ : syracuseStep 1014147 = 1521221) B1521221
theorem B1014163 : Blo 1012602 1014163 := bstep (se 1 (by rfl) ⟨760622, by rfl⟩ : syracuseStep 1014163 = 1521245) B1521245
theorem B1014179 : Blo 1012602 1014179 := bstep (se 1 (by rfl) ⟨760634, by rfl⟩ : syracuseStep 1014179 = 1521269) B1521269
theorem B1014195 : Blo 1012602 1014195 := bstep (se 1 (by rfl) ⟨760646, by rfl⟩ : syracuseStep 1014195 = 1521293) B1521293
theorem B1014211 : Blo 1012602 1014211 := bstep (se 1 (by rfl) ⟨760658, by rfl⟩ : syracuseStep 1014211 = 1521317) B1521317
theorem B1014227 : Blo 1012602 1014227 := bstep (se 1 (by rfl) ⟨760670, by rfl⟩ : syracuseStep 1014227 = 1521341) B1521341
theorem B1014243 : Blo 1012602 1014243 := bstep (se 1 (by rfl) ⟨760682, by rfl⟩ : syracuseStep 1014243 = 1521365) B1521365
theorem B1014259 : Blo 1012602 1014259 := bstep (se 1 (by rfl) ⟨760694, by rfl⟩ : syracuseStep 1014259 = 1521389) B1521389
theorem B1014275 : Blo 1012602 1014275 := bstep (se 1 (by rfl) ⟨760706, by rfl⟩ : syracuseStep 1014275 = 1521413) B1521413
theorem B1014291 : Blo 1012602 1014291 := bstep (se 1 (by rfl) ⟨760718, by rfl⟩ : syracuseStep 1014291 = 1521437) B1521437
theorem B1014307 : Blo 1012602 1014307 := bstep (se 1 (by rfl) ⟨760730, by rfl⟩ : syracuseStep 1014307 = 1521461) B1521461
theorem B1014323 : Blo 1012602 1014323 := bstep (se 1 (by rfl) ⟨760742, by rfl⟩ : syracuseStep 1014323 = 1521485) B1521485
theorem B1014339 : Blo 1012602 1014339 := bstep (se 1 (by rfl) ⟨760754, by rfl⟩ : syracuseStep 1014339 = 1521509) B1521509
theorem B1014355 : Blo 1012602 1014355 := bstep (se 1 (by rfl) ⟨760766, by rfl⟩ : syracuseStep 1014355 = 1521533) B1521533
theorem B1014371 : Blo 1012602 1014371 := bstep (se 1 (by rfl) ⟨760778, by rfl⟩ : syracuseStep 1014371 = 1521557) B1521557
theorem B1014387 : Blo 1012602 1014387 := bstep (se 1 (by rfl) ⟨760790, by rfl⟩ : syracuseStep 1014387 = 1521581) B1521581
theorem B1014403 : Blo 1012602 1014403 := bstep (se 1 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 1014403 = 1521605) B1521605
theorem B1014419 : Blo 1012602 1014419 := bstep (se 1 (by rfl) ⟨760814, by rfl⟩ : syracuseStep 1014419 = 1521629) B1521629
theorem B1014435 : Blo 1012602 1014435 := bstep (se 1 (by rfl) ⟨760826, by rfl⟩ : syracuseStep 1014435 = 1521653) B1521653
theorem B1014451 : Blo 1012602 1014451 := bstep (se 1 (by rfl) ⟨760838, by rfl⟩ : syracuseStep 1014451 = 1521677) B1521677
theorem B1014467 : Blo 1012602 1014467 := bstep (se 1 (by rfl) ⟨760850, by rfl⟩ : syracuseStep 1014467 = 1521701) B1521701
theorem B1014483 : Blo 1012602 1014483 := bstep (se 1 (by rfl) ⟨760862, by rfl⟩ : syracuseStep 1014483 = 1521725) B1521725
theorem B1014499 : Blo 1012602 1014499 := bstep (se 1 (by rfl) ⟨760874, by rfl⟩ : syracuseStep 1014499 = 1521749) B1521749
theorem B1014515 : Blo 1012602 1014515 := bstep (se 1 (by rfl) ⟨760886, by rfl⟩ : syracuseStep 1014515 = 1521773) B1521773
theorem B1014531 : Blo 1012602 1014531 := bstep (se 1 (by rfl) ⟨760898, by rfl⟩ : syracuseStep 1014531 = 1521797) B1521797
theorem B1014547 : Blo 1012602 1014547 := bstep (se 1 (by rfl) ⟨760910, by rfl⟩ : syracuseStep 1014547 = 1521821) B1521821
theorem B1014563 : Blo 1012602 1014563 := bstep (se 1 (by rfl) ⟨760922, by rfl⟩ : syracuseStep 1014563 = 1521845) B1521845
theorem B1014579 : Blo 1012602 1014579 := bstep (se 1 (by rfl) ⟨760934, by rfl⟩ : syracuseStep 1014579 = 1521869) B1521869
theorem B1014595 : Blo 1012602 1014595 := bstep (se 1 (by rfl) ⟨760946, by rfl⟩ : syracuseStep 1014595 = 1521893) B1521893
theorem B1014611 : Blo 1012602 1014611 := bstep (se 1 (by rfl) ⟨760958, by rfl⟩ : syracuseStep 1014611 = 1521917) B1521917
theorem B1014627 : Blo 1012602 1014627 := bstep (se 1 (by rfl) ⟨760970, by rfl⟩ : syracuseStep 1014627 = 1521941) B1521941
theorem B1014643 : Blo 1012602 1014643 := bstep (se 1 (by rfl) ⟨760982, by rfl⟩ : syracuseStep 1014643 = 1521965) B1521965
theorem B1735553 : Blo 1012602 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1014659 : Blo 1012602 1014659 := bstep (se 1 (by rfl) ⟨760994, by rfl⟩ : syracuseStep 1014659 = 1521989) B1521989
theorem B1014675 : Blo 1012602 1014675 := bstep (se 1 (by rfl) ⟨761006, by rfl⟩ : syracuseStep 1014675 = 1522013) B1522013
theorem B1014691 : Blo 1012602 1014691 := bstep (se 1 (by rfl) ⟨761018, by rfl⟩ : syracuseStep 1014691 = 1522037) B1522037
theorem B1014707 : Blo 1012602 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B1014723 : Blo 1012602 1014723 := bstep (se 1 (by rfl) ⟨761042, by rfl⟩ : syracuseStep 1014723 = 1522085) B1522085
theorem B1014739 : Blo 1012602 1014739 := bstep (se 1 (by rfl) ⟨761054, by rfl⟩ : syracuseStep 1014739 = 1522109) B1522109
theorem B1014755 : Blo 1012602 1014755 := bstep (se 1 (by rfl) ⟨761066, by rfl⟩ : syracuseStep 1014755 = 1522133) B1522133
theorem B1014771 : Blo 1012602 1014771 := bstep (se 1 (by rfl) ⟨761078, by rfl⟩ : syracuseStep 1014771 = 1522157) B1522157
theorem B1014787 : Blo 1012602 1014787 := bstep (se 1 (by rfl) ⟨761090, by rfl⟩ : syracuseStep 1014787 = 1522181) B1522181
theorem B1014803 : Blo 1012602 1014803 := bstep (se 1 (by rfl) ⟨761102, by rfl⟩ : syracuseStep 1014803 = 1522205) B1522205
theorem B1014819 : Blo 1012602 1014819 := bstep (se 1 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 1014819 = 1522229) B1522229
theorem B1014835 : Blo 1012602 1014835 := bstep (se 1 (by rfl) ⟨761126, by rfl⟩ : syracuseStep 1014835 = 1522253) B1522253
theorem B1014851 : Blo 1012602 1014851 := bstep (se 1 (by rfl) ⟨761138, by rfl⟩ : syracuseStep 1014851 = 1522277) B1522277
theorem B1014867 : Blo 1012602 1014867 := bstep (se 1 (by rfl) ⟨761150, by rfl⟩ : syracuseStep 1014867 = 1522301) B1522301
theorem B1014883 : Blo 1012602 1014883 := bstep (se 1 (by rfl) ⟨761162, by rfl⟩ : syracuseStep 1014883 = 1522325) B1522325
theorem B4881521 : Blo 1012602 4881521 := bstep (se 2 (by rfl) ⟨1830570, by rfl⟩ : syracuseStep 4881521 = 3661141) B3661141
theorem B1014899 : Blo 1012602 1014899 := bstep (se 1 (by rfl) ⟨761174, by rfl⟩ : syracuseStep 1014899 = 1522349) B1522349
theorem B1014915 : Blo 1012602 1014915 := bstep (se 1 (by rfl) ⟨761186, by rfl⟩ : syracuseStep 1014915 = 1522373) B1522373
theorem B1014931 : Blo 1012602 1014931 := bstep (se 1 (by rfl) ⟨761198, by rfl⟩ : syracuseStep 1014931 = 1522397) B1522397
theorem B1014947 : Blo 1012602 1014947 := bstep (se 1 (by rfl) ⟨761210, by rfl⟩ : syracuseStep 1014947 = 1522421) B1522421
theorem B1014963 : Blo 1012602 1014963 := bstep (se 1 (by rfl) ⟨761222, by rfl⟩ : syracuseStep 1014963 = 1522445) B1522445
theorem B1014979 : Blo 1012602 1014979 := bstep (se 1 (by rfl) ⟨761234, by rfl⟩ : syracuseStep 1014979 = 1522469) B1522469
theorem B1014995 : Blo 1012602 1014995 := bstep (se 1 (by rfl) ⟨761246, by rfl⟩ : syracuseStep 1014995 = 1522493) B1522493
theorem B18742499 : Blo 1012602 18742499 := bstep (se 1 (by rfl) ⟨14056874, by rfl⟩ : syracuseStep 18742499 = 28113749) B28113749
theorem B1015011 : Blo 1012602 1015011 := bstep (se 1 (by rfl) ⟨761258, by rfl⟩ : syracuseStep 1015011 = 1522517) B1522517
theorem B7699697 : Blo 1012602 7699697 := bstep (se 2 (by rfl) ⟨2887386, by rfl⟩ : syracuseStep 7699697 = 5774773) B5774773
theorem B1015027 : Blo 1012602 1015027 := bstep (se 1 (by rfl) ⟨761270, by rfl⟩ : syracuseStep 1015027 = 1522541) B1522541
theorem B1015043 : Blo 1012602 1015043 := bstep (se 1 (by rfl) ⟨761282, by rfl⟩ : syracuseStep 1015043 = 1522565) B1522565
theorem B1015059 : Blo 1012602 1015059 := bstep (se 1 (by rfl) ⟨761294, by rfl⟩ : syracuseStep 1015059 = 1522589) B1522589
theorem B1015075 : Blo 1012602 1015075 := bstep (se 1 (by rfl) ⟨761306, by rfl⟩ : syracuseStep 1015075 = 1522613) B1522613
theorem B1015091 : Blo 1012602 1015091 := bstep (se 1 (by rfl) ⟨761318, by rfl⟩ : syracuseStep 1015091 = 1522637) B1522637
theorem B14646581 : Blo 1012602 14646581 := bstep (se 5 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 14646581 = 1373117) B1373117
theorem B1015107 : Blo 1012602 1015107 := bstep (se 1 (by rfl) ⟨761330, by rfl⟩ : syracuseStep 1015107 = 1522661) B1522661
theorem B1015123 : Blo 1012602 1015123 := bstep (se 1 (by rfl) ⟨761342, by rfl⟩ : syracuseStep 1015123 = 1522685) B1522685
theorem B1015139 : Blo 1012602 1015139 := bstep (se 1 (by rfl) ⟨761354, by rfl⟩ : syracuseStep 1015139 = 1522709) B1522709
theorem B1015155 : Blo 1012602 1015155 := bstep (se 1 (by rfl) ⟨761366, by rfl⟩ : syracuseStep 1015155 = 1522733) B1522733
theorem B1015171 : Blo 1012602 1015171 := bstep (se 1 (by rfl) ⟨761378, by rfl⟩ : syracuseStep 1015171 = 1522757) B1522757
theorem B3079565 : Blo 1012602 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1015187 : Blo 1012602 1015187 := bstep (se 1 (by rfl) ⟨761390, by rfl⟩ : syracuseStep 1015187 = 1522781) B1522781
theorem B1015203 : Blo 1012602 1015203 := bstep (se 1 (by rfl) ⟨761402, by rfl⟩ : syracuseStep 1015203 = 1522805) B1522805
theorem B5864881 : Blo 1012602 5864881 := bstep (se 2 (by rfl) ⟨2199330, by rfl⟩ : syracuseStep 5864881 = 4398661) B4398661
theorem B5143985 : Blo 1012602 5143985 := bstep (se 2 (by rfl) ⟨1928994, by rfl⟩ : syracuseStep 5143985 = 3857989) B3857989
theorem B1015219 : Blo 1012602 1015219 := bstep (se 1 (by rfl) ⟨761414, by rfl⟩ : syracuseStep 1015219 = 1522829) B1522829
theorem B1015235 : Blo 1012602 1015235 := bstep (se 1 (by rfl) ⟨761426, by rfl⟩ : syracuseStep 1015235 = 1522853) B1522853
theorem B1015251 : Blo 1012602 1015251 := bstep (se 1 (by rfl) ⟨761438, by rfl⟩ : syracuseStep 1015251 = 1522877) B1522877
theorem B1015267 : Blo 1012602 1015267 := bstep (se 1 (by rfl) ⟨761450, by rfl⟩ : syracuseStep 1015267 = 1522901) B1522901
theorem B1015283 : Blo 1012602 1015283 := bstep (se 1 (by rfl) ⟨761462, by rfl⟩ : syracuseStep 1015283 = 1522925) B1522925
theorem B1015299 : Blo 1012602 1015299 := bstep (se 1 (by rfl) ⟨761474, by rfl⟩ : syracuseStep 1015299 = 1522949) B1522949
theorem B1015315 : Blo 1012602 1015315 := bstep (se 1 (by rfl) ⟨761486, by rfl⟩ : syracuseStep 1015315 = 1522973) B1522973
theorem B1015331 : Blo 1012602 1015331 := bstep (se 1 (by rfl) ⟨761498, by rfl⟩ : syracuseStep 1015331 = 1522997) B1522997
theorem B1015347 : Blo 1012602 1015347 := bstep (se 1 (by rfl) ⟨761510, by rfl⟩ : syracuseStep 1015347 = 1523021) B1523021
theorem B1015363 : Blo 1012602 1015363 := bstep (se 1 (by rfl) ⟨761522, by rfl⟩ : syracuseStep 1015363 = 1523045) B1523045
theorem B1015379 : Blo 1012602 1015379 := bstep (se 1 (by rfl) ⟨761534, by rfl⟩ : syracuseStep 1015379 = 1523069) B1523069
theorem B1015395 : Blo 1012602 1015395 := bstep (se 1 (by rfl) ⟨761546, by rfl⟩ : syracuseStep 1015395 = 1523093) B1523093
theorem B1015411 : Blo 1012602 1015411 := bstep (se 1 (by rfl) ⟨761558, by rfl⟩ : syracuseStep 1015411 = 1523117) B1523117
theorem B1015427 : Blo 1012602 1015427 := bstep (se 1 (by rfl) ⟨761570, by rfl⟩ : syracuseStep 1015427 = 1523141) B1523141
theorem B1015443 : Blo 1012602 1015443 := bstep (se 1 (by rfl) ⟨761582, by rfl⟩ : syracuseStep 1015443 = 1523165) B1523165
theorem B1015459 : Blo 1012602 1015459 := bstep (se 1 (by rfl) ⟨761594, by rfl⟩ : syracuseStep 1015459 = 1523189) B1523189
theorem B1015475 : Blo 1012602 1015475 := bstep (se 1 (by rfl) ⟨761606, by rfl⟩ : syracuseStep 1015475 = 1523213) B1523213
theorem B1015491 : Blo 1012602 1015491 := bstep (se 1 (by rfl) ⟨761618, by rfl⟩ : syracuseStep 1015491 = 1523237) B1523237
theorem B1015507 : Blo 1012602 1015507 := bstep (se 1 (by rfl) ⟨761630, by rfl⟩ : syracuseStep 1015507 = 1523261) B1523261
theorem B1015523 : Blo 1012602 1015523 := bstep (se 1 (by rfl) ⟨761642, by rfl⟩ : syracuseStep 1015523 = 1523285) B1523285
theorem B1015539 : Blo 1012602 1015539 := bstep (se 1 (by rfl) ⟨761654, by rfl⟩ : syracuseStep 1015539 = 1523309) B1523309
theorem B1015555 : Blo 1012602 1015555 := bstep (se 1 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 1015555 = 1523333) B1523333
theorem B1015571 : Blo 1012602 1015571 := bstep (se 1 (by rfl) ⟨761678, by rfl⟩ : syracuseStep 1015571 = 1523357) B1523357
theorem B1015587 : Blo 1012602 1015587 := bstep (se 1 (by rfl) ⟨761690, by rfl⟩ : syracuseStep 1015587 = 1523381) B1523381
theorem B1015603 : Blo 1012602 1015603 := bstep (se 1 (by rfl) ⟨761702, by rfl⟩ : syracuseStep 1015603 = 1523405) B1523405
theorem B1015619 : Blo 1012602 1015619 := bstep (se 1 (by rfl) ⟨761714, by rfl⟩ : syracuseStep 1015619 = 1523429) B1523429
theorem B1015635 : Blo 1012602 1015635 := bstep (se 1 (by rfl) ⟨761726, by rfl⟩ : syracuseStep 1015635 = 1523453) B1523453
theorem B1015651 : Blo 1012602 1015651 := bstep (se 1 (by rfl) ⟨761738, by rfl⟩ : syracuseStep 1015651 = 1523477) B1523477
theorem B1015667 : Blo 1012602 1015667 := bstep (se 1 (by rfl) ⟨761750, by rfl⟩ : syracuseStep 1015667 = 1523501) B1523501
theorem B1015683 : Blo 1012602 1015683 := bstep (se 1 (by rfl) ⟨761762, by rfl⟩ : syracuseStep 1015683 = 1523525) B1523525
theorem B1015699 : Blo 1012602 1015699 := bstep (se 1 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 1015699 = 1523549) B1523549
theorem B1015715 : Blo 1012602 1015715 := bstep (se 1 (by rfl) ⟨761786, by rfl⟩ : syracuseStep 1015715 = 1523573) B1523573
theorem B1015731 : Blo 1012602 1015731 := bstep (se 1 (by rfl) ⟨761798, by rfl⟩ : syracuseStep 1015731 = 1523597) B1523597
theorem B1015747 : Blo 1012602 1015747 := bstep (se 1 (by rfl) ⟨761810, by rfl⟩ : syracuseStep 1015747 = 1523621) B1523621
theorem B1015763 : Blo 1012602 1015763 := bstep (se 1 (by rfl) ⟨761822, by rfl⟩ : syracuseStep 1015763 = 1523645) B1523645
theorem B1015779 : Blo 1012602 1015779 := bstep (se 1 (by rfl) ⟨761834, by rfl⟩ : syracuseStep 1015779 = 1523669) B1523669
theorem B8224753 : Blo 1012602 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B1015795 : Blo 1012602 1015795 := bstep (se 1 (by rfl) ⟨761846, by rfl⟩ : syracuseStep 1015795 = 1523693) B1523693
theorem B1015819 : Blo 1012602 1015819 := bstep (se 1 (by rfl) ⟨761864, by rfl⟩ : syracuseStep 1015819 = 1523729) B1523729
theorem B1015831 : Blo 1012602 1015831 := bstep (se 1 (by rfl) ⟨761873, by rfl⟩ : syracuseStep 1015831 = 1523747) B1523747
theorem B1015851 : Blo 1012602 1015851 := bstep (se 1 (by rfl) ⟨761888, by rfl⟩ : syracuseStep 1015851 = 1523777) B1523777
theorem B1015863 : Blo 1012602 1015863 := bstep (se 1 (by rfl) ⟨761897, by rfl⟩ : syracuseStep 1015863 = 1523795) B1523795
theorem B1015883 : Blo 1012602 1015883 := bstep (se 1 (by rfl) ⟨761912, by rfl⟩ : syracuseStep 1015883 = 1523825) B1523825
theorem B1015895 : Blo 1012602 1015895 := bstep (se 1 (by rfl) ⟨761921, by rfl⟩ : syracuseStep 1015895 = 1523843) B1523843
theorem B1015915 : Blo 1012602 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B1015927 : Blo 1012602 1015927 := bstep (se 1 (by rfl) ⟨761945, by rfl⟩ : syracuseStep 1015927 = 1523891) B1523891
theorem B1015947 : Blo 1012602 1015947 := bstep (se 1 (by rfl) ⟨761960, by rfl⟩ : syracuseStep 1015947 = 1523921) B1523921
theorem B1015959 : Blo 1012602 1015959 := bstep (se 1 (by rfl) ⟨761969, by rfl⟩ : syracuseStep 1015959 = 1523939) B1523939
theorem B1015979 : Blo 1012602 1015979 := bstep (se 1 (by rfl) ⟨761984, by rfl⟩ : syracuseStep 1015979 = 1523969) B1523969
theorem B1015991 : Blo 1012602 1015991 := bstep (se 1 (by rfl) ⟨761993, by rfl⟩ : syracuseStep 1015991 = 1523987) B1523987
theorem B1016011 : Blo 1012602 1016011 := bstep (se 1 (by rfl) ⟨762008, by rfl⟩ : syracuseStep 1016011 = 1524017) B1524017
theorem B1016023 : Blo 1012602 1016023 := bstep (se 1 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 1016023 = 1524035) B1524035
theorem B4391129 : Blo 1012602 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B1016043 : Blo 1012602 1016043 := bstep (se 1 (by rfl) ⟨762032, by rfl⟩ : syracuseStep 1016043 = 1524065) B1524065
theorem B1016055 : Blo 1012602 1016055 := bstep (se 1 (by rfl) ⟨762041, by rfl⟩ : syracuseStep 1016055 = 1524083) B1524083
theorem B1016075 : Blo 1012602 1016075 := bstep (se 1 (by rfl) ⟨762056, by rfl⟩ : syracuseStep 1016075 = 1524113) B1524113
theorem B1016087 : Blo 1012602 1016087 := bstep (se 1 (by rfl) ⟨762065, by rfl⟩ : syracuseStep 1016087 = 1524131) B1524131
theorem B1016107 : Blo 1012602 1016107 := bstep (se 1 (by rfl) ⟨762080, by rfl⟩ : syracuseStep 1016107 = 1524161) B1524161
theorem B1016119 : Blo 1012602 1016119 := bstep (se 1 (by rfl) ⟨762089, by rfl⟩ : syracuseStep 1016119 = 1524179) B1524179
theorem B1016139 : Blo 1012602 1016139 := bstep (se 1 (by rfl) ⟨762104, by rfl⟩ : syracuseStep 1016139 = 1524209) B1524209
theorem B1016151 : Blo 1012602 1016151 := bstep (se 1 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 1016151 = 1524227) B1524227
theorem B1016171 : Blo 1012602 1016171 := bstep (se 1 (by rfl) ⟨762128, by rfl⟩ : syracuseStep 1016171 = 1524257) B1524257
theorem B1016183 : Blo 1012602 1016183 := bstep (se 1 (by rfl) ⟨762137, by rfl⟩ : syracuseStep 1016183 = 1524275) B1524275
theorem B1016203 : Blo 1012602 1016203 := bstep (se 1 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 1016203 = 1524305) B1524305
theorem B1016215 : Blo 1012602 1016215 := bstep (se 1 (by rfl) ⟨762161, by rfl⟩ : syracuseStep 1016215 = 1524323) B1524323
theorem B1016235 : Blo 1012602 1016235 := bstep (se 1 (by rfl) ⟨762176, by rfl⟩ : syracuseStep 1016235 = 1524353) B1524353
theorem B1016247 : Blo 1012602 1016247 := bstep (se 1 (by rfl) ⟨762185, by rfl⟩ : syracuseStep 1016247 = 1524371) B1524371
theorem B1016267 : Blo 1012602 1016267 := bstep (se 1 (by rfl) ⟨762200, by rfl⟩ : syracuseStep 1016267 = 1524401) B1524401
theorem B1016279 : Blo 1012602 1016279 := bstep (se 1 (by rfl) ⟨762209, by rfl⟩ : syracuseStep 1016279 = 1524419) B1524419
theorem B8651225 : Blo 1012602 8651225 := bstep (se 2 (by rfl) ⟨3244209, by rfl⟩ : syracuseStep 8651225 = 6488419) B6488419
theorem B2884061 : Blo 1012602 2884061 := bstep (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) B1081523
theorem B1016299 : Blo 1012602 1016299 := bstep (se 1 (by rfl) ⟨762224, by rfl⟩ : syracuseStep 1016299 = 1524449) B1524449
theorem B1016311 : Blo 1012602 1016311 := bstep (se 1 (by rfl) ⟨762233, by rfl⟩ : syracuseStep 1016311 = 1524467) B1524467
theorem B1016331 : Blo 1012602 1016331 := bstep (se 1 (by rfl) ⟨762248, by rfl⟩ : syracuseStep 1016331 = 1524497) B1524497
theorem B1016343 : Blo 1012602 1016343 := bstep (se 1 (by rfl) ⟨762257, by rfl⟩ : syracuseStep 1016343 = 1524515) B1524515
theorem B1016363 : Blo 1012602 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B1016375 : Blo 1012602 1016375 := bstep (se 1 (by rfl) ⟨762281, by rfl⟩ : syracuseStep 1016375 = 1524563) B1524563
theorem B1016395 : Blo 1012602 1016395 := bstep (se 1 (by rfl) ⟨762296, by rfl⟩ : syracuseStep 1016395 = 1524593) B1524593
theorem B1016407 : Blo 1012602 1016407 := bstep (se 1 (by rfl) ⟨762305, by rfl⟩ : syracuseStep 1016407 = 1524611) B1524611
theorem B35193437 : Blo 1012602 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B1016427 : Blo 1012602 1016427 := bstep (se 1 (by rfl) ⟨762320, by rfl⟩ : syracuseStep 1016427 = 1524641) B1524641
theorem B1016439 : Blo 1012602 1016439 := bstep (se 1 (by rfl) ⟨762329, by rfl⟩ : syracuseStep 1016439 = 1524659) B1524659
theorem B1016459 : Blo 1012602 1016459 := bstep (se 1 (by rfl) ⟨762344, by rfl⟩ : syracuseStep 1016459 = 1524689) B1524689
theorem B1016471 : Blo 1012602 1016471 := bstep (se 1 (by rfl) ⟨762353, by rfl⟩ : syracuseStep 1016471 = 1524707) B1524707
theorem B2163353 : Blo 1012602 2163353 := bstep (se 2 (by rfl) ⟨811257, by rfl⟩ : syracuseStep 2163353 = 1622515) B1622515
theorem B1016491 : Blo 1012602 1016491 := bstep (se 1 (by rfl) ⟨762368, by rfl⟩ : syracuseStep 1016491 = 1524737) B1524737
theorem B1016503 : Blo 1012602 1016503 := bstep (se 1 (by rfl) ⟨762377, by rfl⟩ : syracuseStep 1016503 = 1524755) B1524755
theorem B1016523 : Blo 1012602 1016523 := bstep (se 1 (by rfl) ⟨762392, by rfl⟩ : syracuseStep 1016523 = 1524785) B1524785
theorem B1016535 : Blo 1012602 1016535 := bstep (se 1 (by rfl) ⟨762401, by rfl⟩ : syracuseStep 1016535 = 1524803) B1524803
theorem B1016555 : Blo 1012602 1016555 := bstep (se 1 (by rfl) ⟨762416, by rfl⟩ : syracuseStep 1016555 = 1524833) B1524833
theorem B1016567 : Blo 1012602 1016567 := bstep (se 1 (by rfl) ⟨762425, by rfl⟩ : syracuseStep 1016567 = 1524851) B1524851
theorem B1016587 : Blo 1012602 1016587 := bstep (se 1 (by rfl) ⟨762440, by rfl⟩ : syracuseStep 1016587 = 1524881) B1524881
theorem B1016599 : Blo 1012602 1016599 := bstep (se 1 (by rfl) ⟨762449, by rfl⟩ : syracuseStep 1016599 = 1524899) B1524899
theorem B2884403 : Blo 1012602 2884403 := bstep (se 1 (by rfl) ⟨2163302, by rfl⟩ : syracuseStep 2884403 = 4326605) B4326605
theorem B6489011 : Blo 1012602 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B4326365 : Blo 1012602 4326365 := bstep (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) B1622387
theorem B2163763 : Blo 1012602 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B4752535 : Blo 1012602 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B50136245 : Blo 1012602 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B1541387 : Blo 1012602 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B3900761 : Blo 1012602 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B2164097 : Blo 1012602 2164097 := bstep (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) B1623073
theorem B9733553 : Blo 1012602 9733553 := bstep (se 2 (by rfl) ⟨3650082, by rfl⟩ : syracuseStep 9733553 = 7300165) B7300165
theorem B1443415 : Blo 1012602 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B1083223 : Blo 1012602 1083223 := bstep (se 1 (by rfl) ⟨812417, by rfl⟩ : syracuseStep 1083223 = 1624835) B1624835
theorem B2197441 : Blo 1012602 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B8652865 : Blo 1012602 8652865 := bstep (se 2 (by rfl) ⟨3244824, by rfl⟩ : syracuseStep 8652865 = 6489649) B6489649
theorem B2164823 : Blo 1012602 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B8784089 : Blo 1012602 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B6490469 : Blo 1012602 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B1543115 : Blo 1012602 1543115 := bstep (se 1 (by rfl) ⟨1157336, by rfl⟩ : syracuseStep 1543115 = 2314673) B2314673
theorem B2886749 : Blo 1012602 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B2886977 : Blo 1012602 2886977 := bstep (se 2 (by rfl) ⟨1082616, by rfl⟩ : syracuseStep 2886977 = 2165233) B2165233
theorem B1084919 : Blo 1012602 1084919 := bstep (se 1 (by rfl) ⟨813689, by rfl⟩ : syracuseStep 1084919 = 1627379) B1627379
theorem B4328963 : Blo 1012602 4328963 := bstep (se 1 (by rfl) ⟨3246722, by rfl⟩ : syracuseStep 4328963 = 6493445) B6493445
theorem B1445465 : Blo 1012602 1445465 := bstep (se 2 (by rfl) ⟨542049, by rfl⟩ : syracuseStep 1445465 = 1084099) B1084099
theorem B2887319 : Blo 1012602 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B1281739 : Blo 1012602 1281739 := bstep (se 1 (by rfl) ⟨961304, by rfl⟩ : syracuseStep 1281739 = 1922609) B1922609
theorem B1543961 : Blo 1012602 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B1282007 : Blo 1012602 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B5771357 : Blo 1012602 5771357 := bstep (se 3 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 5771357 = 2164259) B2164259
theorem B4165825 : Blo 1012602 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B1446103 : Blo 1012602 1446103 := bstep (se 1 (by rfl) ⟨1084577, by rfl⟩ : syracuseStep 1446103 = 2169155) B2169155
theorem B12357953 : Blo 1012602 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B1544599 : Blo 1012602 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B2167283 : Blo 1012602 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B20845187 : Blo 1012602 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B1282711 : Blo 1012602 1282711 := bstep (se 1 (by rfl) ⟨962033, by rfl⟩ : syracuseStep 1282711 = 1924067) B1924067
theorem B4625113 : Blo 1012602 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B7312133 : Blo 1012602 7312133 := bstep (se 4 (by rfl) ⟨685512, by rfl⟩ : syracuseStep 7312133 = 1371025) B1371025
theorem B1708823 : Blo 1012602 1708823 := bstep (se 1 (by rfl) ⟨1281617, by rfl⟩ : syracuseStep 1708823 = 2563235) B2563235
theorem B1708951 : Blo 1012602 1708951 := bstep (se 1 (by rfl) ⟨1281713, by rfl⟩ : syracuseStep 1708951 = 2563427) B2563427
theorem B11572145 : Blo 1012602 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B1446923 : Blo 1012602 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B9245771 : Blo 1012602 9245771 := bstep (se 1 (by rfl) ⟨6934328, by rfl⟩ : syracuseStep 9245771 = 13868657) B13868657
theorem B1709579 : Blo 1012602 1709579 := bstep (se 1 (by rfl) ⟨1282184, by rfl⟩ : syracuseStep 1709579 = 2564369) B2564369
theorem B19535377 : Blo 1012602 19535377 := bstep (se 2 (by rfl) ⟨7325766, by rfl⟩ : syracuseStep 19535377 = 14651533) B14651533
theorem B10556963 : Blo 1012602 10556963 := bstep (se 1 (by rfl) ⟨7917722, by rfl⟩ : syracuseStep 10556963 = 15835445) B15835445
theorem B1709707 : Blo 1012602 1709707 := bstep (se 1 (by rfl) ⟨1282280, by rfl⟩ : syracuseStep 1709707 = 2564561) B2564561
theorem B2168471 : Blo 1012602 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B1709849 : Blo 1012602 1709849 := bstep (se 2 (by rfl) ⟨641193, by rfl⟩ : syracuseStep 1709849 = 1282387) B1282387
theorem B4331339 : Blo 1012602 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B1709977 : Blo 1012602 1709977 := bstep (se 2 (by rfl) ⟨641241, by rfl⟩ : syracuseStep 1709977 = 1282483) B1282483
theorem B2889665 : Blo 1012602 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B3086657 : Blo 1012602 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B1644875 : Blo 1012602 1644875 := bstep (se 1 (by rfl) ⟨1233656, by rfl⟩ : syracuseStep 1644875 = 2467313) B2467313
theorem B1284427 : Blo 1012602 1284427 := bstep (se 1 (by rfl) ⟨963320, by rfl⟩ : syracuseStep 1284427 = 1926641) B1926641
theorem B4004275 : Blo 1012602 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1710551 : Blo 1012602 1710551 := bstep (se 1 (by rfl) ⟨1282913, by rfl⟩ : syracuseStep 1710551 = 2565827) B2565827
theorem B2890201 : Blo 1012602 2890201 := bstep (se 2 (by rfl) ⟨1083825, by rfl⟩ : syracuseStep 2890201 = 2167651) B2167651
theorem B5773841 : Blo 1012602 5773841 := bstep (se 2 (by rfl) ⟨2165190, by rfl⟩ : syracuseStep 5773841 = 4330381) B4330381
theorem B1710679 : Blo 1012602 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B3906193 : Blo 1012602 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B2169497 : Blo 1012602 2169497 := bstep (se 2 (by rfl) ⟨813561, by rfl⟩ : syracuseStep 2169497 = 1627123) B1627123
theorem B4332311 : Blo 1012602 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B2563265 : Blo 1012602 2563265 := bstep (se 2 (by rfl) ⟨961224, by rfl⟩ : syracuseStep 2563265 = 1922449) B1922449
theorem B1711307 : Blo 1012602 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B1285399 : Blo 1012602 1285399 := bstep (se 1 (by rfl) ⟨964049, by rfl⟩ : syracuseStep 1285399 = 1928099) B1928099
theorem B1711435 : Blo 1012602 1711435 := bstep (se 1 (by rfl) ⟨1283576, by rfl⟩ : syracuseStep 1711435 = 2567153) B2567153
theorem B1711577 : Blo 1012602 1711577 := bstep (se 2 (by rfl) ⟨641841, by rfl⟩ : syracuseStep 1711577 = 1283683) B1283683
theorem B1711705 : Blo 1012602 1711705 := bstep (se 2 (by rfl) ⟨641889, by rfl⟩ : syracuseStep 1711705 = 1283779) B1283779
theorem B4628141 : Blo 1012602 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B2170547 : Blo 1012602 2170547 := bstep (se 1 (by rfl) ⟨1627910, by rfl⟩ : syracuseStep 2170547 = 3255821) B3255821
theorem B6954827 : Blo 1012602 6954827 := bstep (se 1 (by rfl) ⟨5216120, by rfl⟩ : syracuseStep 6954827 = 10432241) B10432241
theorem B4169603 : Blo 1012602 4169603 := bstep (se 1 (by rfl) ⟨3127202, by rfl⟩ : syracuseStep 4169603 = 6254405) B6254405
theorem B13868977 : Blo 1012602 13868977 := bstep (se 2 (by rfl) ⟨5200866, by rfl⟩ : syracuseStep 13868977 = 10401733) B10401733
theorem B1286219 : Blo 1012602 1286219 := bstep (se 1 (by rfl) ⟨964664, by rfl⟩ : syracuseStep 1286219 = 1929329) B1929329
theorem B1712279 : Blo 1012602 1712279 := bstep (se 1 (by rfl) ⟨1284209, by rfl⟩ : syracuseStep 1712279 = 2568419) B2568419
theorem B2171137 : Blo 1012602 2171137 := bstep (se 2 (by rfl) ⟨814176, by rfl⟩ : syracuseStep 2171137 = 1628353) B1628353
theorem B7414033 : Blo 1012602 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B1712407 : Blo 1012602 1712407 := bstep (se 1 (by rfl) ⟨1284305, by rfl⟩ : syracuseStep 1712407 = 2568611) B2568611
theorem B2892125 : Blo 1012602 2892125 := bstep (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) B1084547
theorem B2564531 : Blo 1012602 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B1713035 : Blo 1012602 1713035 := bstep (se 1 (by rfl) ⟨1284776, by rfl⟩ : syracuseStep 1713035 = 2569553) B2569553
theorem B2565067 : Blo 1012602 2565067 := bstep (se 1 (by rfl) ⟨1923800, by rfl⟩ : syracuseStep 2565067 = 3847601) B3847601
theorem B8659973 : Blo 1012602 8659973 := bstep (se 4 (by rfl) ⟨811872, by rfl⟩ : syracuseStep 8659973 = 1623745) B1623745
theorem B1713163 : Blo 1012602 1713163 := bstep (se 1 (by rfl) ⟨1284872, by rfl⟩ : syracuseStep 1713163 = 2569745) B2569745
theorem B2565209 : Blo 1012602 2565209 := bstep (se 2 (by rfl) ⟨961953, by rfl⟩ : syracuseStep 2565209 = 1923907) B1923907
theorem B1713305 : Blo 1012602 1713305 := bstep (se 2 (by rfl) ⟨642489, by rfl⟩ : syracuseStep 1713305 = 1284979) B1284979
theorem B4334771 : Blo 1012602 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B1713433 : Blo 1012602 1713433 := bstep (se 2 (by rfl) ⟨642537, by rfl⟩ : syracuseStep 1713433 = 1285075) B1285075
theorem B6169931 : Blo 1012602 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B3417821 : Blo 1012602 3417821 := bstep (se 3 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 3417821 = 1281683) B1281683
theorem B1714007 : Blo 1012602 1714007 := bstep (se 1 (by rfl) ⟨1285505, by rfl⟩ : syracuseStep 1714007 = 2571011) B2571011
theorem B2566039 : Blo 1012602 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B1714135 : Blo 1012602 1714135 := bstep (se 1 (by rfl) ⟨1285601, by rfl⟩ : syracuseStep 1714135 = 2571203) B2571203
theorem B3254347 : Blo 1012602 3254347 := bstep (se 1 (by rfl) ⟨2440760, by rfl⟩ : syracuseStep 3254347 = 4881521) B4881521
theorem B1321099 : Blo 1012602 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B12494999 : Blo 1012602 12494999 := bstep (se 1 (by rfl) ⟨9371249, by rfl⟩ : syracuseStep 12494999 = 18742499) B18742499
theorem B3254489 : Blo 1012602 3254489 := bstep (se 2 (by rfl) ⟨1220433, by rfl⟩ : syracuseStep 3254489 = 2440867) B2440867
theorem B2566475 : Blo 1012602 2566475 := bstep (se 1 (by rfl) ⟨1924856, by rfl⟩ : syracuseStep 2566475 = 3849713) B3849713
theorem B17312291 : Blo 1012602 17312291 := bstep (se 1 (by rfl) ⟨12984218, by rfl⟩ : syracuseStep 17312291 = 25968437) B25968437
theorem B1714763 : Blo 1012602 1714763 := bstep (se 1 (by rfl) ⟨1286072, by rfl⟩ : syracuseStep 1714763 = 2572145) B2572145
theorem B2566849 : Blo 1012602 2566849 := bstep (se 2 (by rfl) ⟨962568, by rfl⟩ : syracuseStep 2566849 = 1925137) B1925137
theorem B1714891 : Blo 1012602 1714891 := bstep (se 1 (by rfl) ⟨1286168, by rfl⟩ : syracuseStep 1714891 = 2572337) B2572337
theorem B3844867 : Blo 1012602 3844867 := bstep (se 1 (by rfl) ⟨2883650, by rfl⟩ : syracuseStep 3844867 = 5767301) B5767301
theorem B3418955 : Blo 1012602 3418955 := bstep (se 1 (by rfl) ⟨2564216, by rfl⟩ : syracuseStep 3418955 = 5128433) B5128433
theorem B1715033 : Blo 1012602 1715033 := bstep (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) B1286275
theorem B3910493 : Blo 1012602 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B1715161 : Blo 1012602 1715161 := bstep (se 2 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 1715161 = 1286371) B1286371
theorem B4336685 : Blo 1012602 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B3845171 : Blo 1012602 3845171 := bstep (se 1 (by rfl) ⟨2883878, by rfl⟩ : syracuseStep 3845171 = 5767757) B5767757
theorem B3419225 : Blo 1012602 3419225 := bstep (se 2 (by rfl) ⟨1282209, by rfl⟩ : syracuseStep 3419225 = 2564419) B2564419
theorem B2567447 : Blo 1012602 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B11545901 : Blo 1012602 11545901 := bstep (se 3 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 11545901 = 4329713) B4329713
theorem B1518923 : Blo 1012602 1518923 := bstep (se 1 (by rfl) ⟨1139192, by rfl⟩ : syracuseStep 1518923 = 2278385) B2278385
theorem B1518935 : Blo 1012602 1518935 := bstep (se 1 (by rfl) ⟨1139201, by rfl⟩ : syracuseStep 1518935 = 2278403) B2278403
theorem B4337027 : Blo 1012602 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B1519001 : Blo 1012602 1519001 := bstep (se 2 (by rfl) ⟨569625, by rfl⟩ : syracuseStep 1519001 = 1139251) B1139251
theorem B1519115 : Blo 1012602 1519115 := bstep (se 1 (by rfl) ⟨1139336, by rfl⟩ : syracuseStep 1519115 = 2278673) B2278673
theorem B1519127 : Blo 1012602 1519127 := bstep (se 1 (by rfl) ⟨1139345, by rfl⟩ : syracuseStep 1519127 = 2278691) B2278691
theorem B1519193 : Blo 1012602 1519193 := bstep (se 2 (by rfl) ⟨569697, by rfl⟩ : syracuseStep 1519193 = 1139395) B1139395
theorem B3845825 : Blo 1012602 3845825 := bstep (se 2 (by rfl) ⟨1442184, by rfl⟩ : syracuseStep 3845825 = 2884369) B2884369
theorem B1519307 : Blo 1012602 1519307 := bstep (se 1 (by rfl) ⟨1139480, by rfl⟩ : syracuseStep 1519307 = 2278961) B2278961
theorem B3124939 : Blo 1012602 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B49360589 : Blo 1012602 49360589 := bstep (se 3 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 49360589 = 18510221) B18510221
theorem B1519319 : Blo 1012602 1519319 := bstep (se 1 (by rfl) ⟨1139489, by rfl⟩ : syracuseStep 1519319 = 2278979) B2278979
theorem B1027819 : Blo 1012602 1027819 := bstep (se 1 (by rfl) ⟨770864, by rfl⟩ : syracuseStep 1027819 = 1541729) B1541729
theorem B3419927 : Blo 1012602 3419927 := bstep (se 1 (by rfl) ⟨2564945, by rfl⟩ : syracuseStep 3419927 = 5129891) B5129891
theorem B1519385 : Blo 1012602 1519385 := bstep (se 2 (by rfl) ⟨569769, by rfl⟩ : syracuseStep 1519385 = 1139539) B1139539
theorem B4108097 : Blo 1012602 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B1519499 : Blo 1012602 1519499 := bstep (se 1 (by rfl) ⟨1139624, by rfl⟩ : syracuseStep 1519499 = 2279249) B2279249
theorem B1519511 : Blo 1012602 1519511 := bstep (se 1 (by rfl) ⟨1139633, by rfl⟩ : syracuseStep 1519511 = 2279267) B2279267
theorem B1519577 : Blo 1012602 1519577 := bstep (se 2 (by rfl) ⟨569841, by rfl⟩ : syracuseStep 1519577 = 1139683) B1139683
theorem B2568257 : Blo 1012602 2568257 := bstep (se 2 (by rfl) ⟨963096, by rfl⟩ : syracuseStep 2568257 = 1926193) B1926193
theorem B1519691 : Blo 1012602 1519691 := bstep (se 1 (by rfl) ⟨1139768, by rfl⟩ : syracuseStep 1519691 = 2279537) B2279537
theorem B1519703 : Blo 1012602 1519703 := bstep (se 1 (by rfl) ⟨1139777, by rfl⟩ : syracuseStep 1519703 = 2279555) B2279555
theorem B3256409 : Blo 1012602 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B1519769 : Blo 1012602 1519769 := bstep (se 2 (by rfl) ⟨569913, by rfl⟩ : syracuseStep 1519769 = 1139827) B1139827
theorem B5779673 : Blo 1012602 5779673 := bstep (se 2 (by rfl) ⟨2167377, by rfl⟩ : syracuseStep 5779673 = 4334755) B4334755
theorem B1519883 : Blo 1012602 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B1519895 : Blo 1012602 1519895 := bstep (se 1 (by rfl) ⟨1139921, by rfl⟩ : syracuseStep 1519895 = 2279843) B2279843
theorem B3911981 : Blo 1012602 3911981 := bstep (se 3 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 3911981 = 1466993) B1466993
theorem B3420467 : Blo 1012602 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B10170689 : Blo 1012602 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B1519961 : Blo 1012602 1519961 := bstep (se 2 (by rfl) ⟨569985, by rfl⟩ : syracuseStep 1519961 = 1139971) B1139971
theorem B1520075 : Blo 1012602 1520075 := bstep (se 1 (by rfl) ⟨1140056, by rfl⟩ : syracuseStep 1520075 = 2280113) B2280113
theorem B1520087 : Blo 1012602 1520087 := bstep (se 1 (by rfl) ⟨1140065, by rfl⟩ : syracuseStep 1520087 = 2280131) B2280131
theorem B1520153 : Blo 1012602 1520153 := bstep (se 2 (by rfl) ⟨570057, by rfl⟩ : syracuseStep 1520153 = 1140115) B1140115
theorem B8663597 : Blo 1012602 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B3420737 : Blo 1012602 3420737 := bstep (se 2 (by rfl) ⟨1282776, by rfl⟩ : syracuseStep 3420737 = 2565553) B2565553
theorem B1028695 : Blo 1012602 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B2568793 : Blo 1012602 2568793 := bstep (se 2 (by rfl) ⟨963297, by rfl⟩ : syracuseStep 2568793 = 1926595) B1926595
theorem B1520267 : Blo 1012602 1520267 := bstep (se 1 (by rfl) ⟨1140200, by rfl⟩ : syracuseStep 1520267 = 2280401) B2280401
theorem B1520279 : Blo 1012602 1520279 := bstep (se 1 (by rfl) ⟨1140209, by rfl⟩ : syracuseStep 1520279 = 2280419) B2280419
theorem B1028759 : Blo 1012602 1028759 := bstep (se 1 (by rfl) ⟨771569, by rfl⟩ : syracuseStep 1028759 = 1543139) B1543139
theorem B1520345 : Blo 1012602 1520345 := bstep (se 2 (by rfl) ⟨570129, by rfl⟩ : syracuseStep 1520345 = 1140259) B1140259
theorem B5550923 : Blo 1012602 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B1520459 : Blo 1012602 1520459 := bstep (se 1 (by rfl) ⟨1140344, by rfl⟩ : syracuseStep 1520459 = 2280689) B2280689
theorem B1520471 : Blo 1012602 1520471 := bstep (se 1 (by rfl) ⟨1140353, by rfl⟩ : syracuseStep 1520471 = 2280707) B2280707
theorem B4633433 : Blo 1012602 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B1520537 : Blo 1012602 1520537 := bstep (se 2 (by rfl) ⟨570201, by rfl⟩ : syracuseStep 1520537 = 1140403) B1140403
theorem B3847085 : Blo 1012602 3847085 := bstep (se 3 (by rfl) ⟨721328, by rfl⟩ : syracuseStep 3847085 = 1442657) B1442657
theorem B3847115 : Blo 1012602 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B2634713 : Blo 1012602 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B1520651 : Blo 1012602 1520651 := bstep (se 1 (by rfl) ⟨1140488, by rfl⟩ : syracuseStep 1520651 = 2280977) B2280977
theorem B1520663 : Blo 1012602 1520663 := bstep (se 1 (by rfl) ⟨1140497, by rfl⟩ : syracuseStep 1520663 = 2280995) B2280995
theorem B1520729 : Blo 1012602 1520729 := bstep (se 2 (by rfl) ⟨570273, by rfl⟩ : syracuseStep 1520729 = 1140547) B1140547
theorem B3421277 : Blo 1012602 3421277 := bstep (se 3 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 3421277 = 1282979) B1282979
theorem B1520843 : Blo 1012602 1520843 := bstep (se 1 (by rfl) ⟨1140632, by rfl⟩ : syracuseStep 1520843 = 2281265) B2281265
theorem B1520855 : Blo 1012602 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B3650777 : Blo 1012602 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B1520921 : Blo 1012602 1520921 := bstep (se 2 (by rfl) ⟨570345, by rfl⟩ : syracuseStep 1520921 = 1140691) B1140691
theorem B1521035 : Blo 1012602 1521035 := bstep (se 1 (by rfl) ⟨1140776, by rfl⟩ : syracuseStep 1521035 = 2281553) B2281553
theorem B70268309 : Blo 1012602 70268309 := bstep (se 6 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 70268309 = 3293827) B3293827
theorem B1521047 : Blo 1012602 1521047 := bstep (se 1 (by rfl) ⟨1140785, by rfl⟩ : syracuseStep 1521047 = 2281571) B2281571
theorem B1521113 : Blo 1012602 1521113 := bstep (se 2 (by rfl) ⟨570417, by rfl⟩ : syracuseStep 1521113 = 1140835) B1140835
theorem B1521227 : Blo 1012602 1521227 := bstep (se 1 (by rfl) ⟨1140920, by rfl⟩ : syracuseStep 1521227 = 2281841) B2281841
theorem B1521239 : Blo 1012602 1521239 := bstep (se 1 (by rfl) ⟨1140929, by rfl⟩ : syracuseStep 1521239 = 2281859) B2281859
theorem B3847769 : Blo 1012602 3847769 := bstep (se 2 (by rfl) ⟨1442913, by rfl⟩ : syracuseStep 3847769 = 2885827) B2885827
theorem B1521305 : Blo 1012602 1521305 := bstep (se 2 (by rfl) ⟨570489, by rfl⟩ : syracuseStep 1521305 = 1140979) B1140979
theorem B2569907 : Blo 1012602 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B3651265 : Blo 1012602 3651265 := bstep (se 2 (by rfl) ⟨1369224, by rfl⟩ : syracuseStep 3651265 = 2738449) B2738449
theorem B4339403 : Blo 1012602 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B1521419 : Blo 1012602 1521419 := bstep (se 1 (by rfl) ⟨1141064, by rfl⟩ : syracuseStep 1521419 = 2282129) B2282129
theorem B1521431 : Blo 1012602 1521431 := bstep (se 1 (by rfl) ⟨1141073, by rfl⟩ : syracuseStep 1521431 = 2282147) B2282147
theorem B1521497 : Blo 1012602 1521497 := bstep (se 2 (by rfl) ⟨570561, by rfl⟩ : syracuseStep 1521497 = 1141123) B1141123
theorem B2439001 : Blo 1012602 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B3848087 : Blo 1012602 3848087 := bstep (se 1 (by rfl) ⟨2886065, by rfl⟩ : syracuseStep 3848087 = 5772131) B5772131
theorem B1521611 : Blo 1012602 1521611 := bstep (se 1 (by rfl) ⟨1141208, by rfl⟩ : syracuseStep 1521611 = 2282417) B2282417
theorem B1521623 : Blo 1012602 1521623 := bstep (se 1 (by rfl) ⟨1141217, by rfl⟩ : syracuseStep 1521623 = 2282435) B2282435
theorem B2570201 : Blo 1012602 2570201 := bstep (se 2 (by rfl) ⟨963825, by rfl⟩ : syracuseStep 2570201 = 1927651) B1927651
theorem B1521689 : Blo 1012602 1521689 := bstep (se 2 (by rfl) ⟨570633, by rfl⟩ : syracuseStep 1521689 = 1141267) B1141267
theorem B1521803 : Blo 1012602 1521803 := bstep (se 1 (by rfl) ⟨1141352, by rfl⟩ : syracuseStep 1521803 = 2282705) B2282705
theorem B1521815 : Blo 1012602 1521815 := bstep (se 1 (by rfl) ⟨1141361, by rfl⟩ : syracuseStep 1521815 = 2282723) B2282723
theorem B3422411 : Blo 1012602 3422411 := bstep (se 1 (by rfl) ⟨2566808, by rfl⟩ : syracuseStep 3422411 = 5133617) B5133617
theorem B1521881 : Blo 1012602 1521881 := bstep (se 2 (by rfl) ⟨570705, by rfl⟩ : syracuseStep 1521881 = 1141411) B1141411
theorem B19478789 : Blo 1012602 19478789 := bstep (se 4 (by rfl) ⟨1826136, by rfl⟩ : syracuseStep 19478789 = 3652273) B3652273
theorem B1521995 : Blo 1012602 1521995 := bstep (se 1 (by rfl) ⟨1141496, by rfl⟩ : syracuseStep 1521995 = 2282993) B2282993
theorem B1522007 : Blo 1012602 1522007 := bstep (se 1 (by rfl) ⟨1141505, by rfl⟩ : syracuseStep 1522007 = 2283011) B2283011
theorem B3651929 : Blo 1012602 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B56342897 : Blo 1012602 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B1522073 : Blo 1012602 1522073 := bstep (se 2 (by rfl) ⟨570777, by rfl⟩ : syracuseStep 1522073 = 1141555) B1141555
theorem B7715249 : Blo 1012602 7715249 := bstep (se 2 (by rfl) ⟨2893218, by rfl⟩ : syracuseStep 7715249 = 5786437) B5786437
theorem B3422681 : Blo 1012602 3422681 := bstep (se 2 (by rfl) ⟨1283505, by rfl⟩ : syracuseStep 3422681 = 2567011) B2567011
theorem B1980929 : Blo 1012602 1980929 := bstep (se 2 (by rfl) ⟨742848, by rfl⟩ : syracuseStep 1980929 = 1485697) B1485697
theorem B1522187 : Blo 1012602 1522187 := bstep (se 1 (by rfl) ⟨1141640, by rfl⟩ : syracuseStep 1522187 = 2283281) B2283281
theorem B1522199 : Blo 1012602 1522199 := bstep (se 1 (by rfl) ⟨1141649, by rfl⟩ : syracuseStep 1522199 = 2283299) B2283299
theorem B3848755 : Blo 1012602 3848755 := bstep (se 1 (by rfl) ⟨2886566, by rfl⟩ : syracuseStep 3848755 = 5773133) B5773133
theorem B1522265 : Blo 1012602 1522265 := bstep (se 2 (by rfl) ⟨570849, by rfl⟩ : syracuseStep 1522265 = 1141699) B1141699
theorem B4340375 : Blo 1012602 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B1522379 : Blo 1012602 1522379 := bstep (se 1 (by rfl) ⟨1141784, by rfl⟩ : syracuseStep 1522379 = 2283569) B2283569
theorem B1522391 : Blo 1012602 1522391 := bstep (se 1 (by rfl) ⟨1141793, by rfl⟩ : syracuseStep 1522391 = 2283587) B2283587
theorem B1522457 : Blo 1012602 1522457 := bstep (se 2 (by rfl) ⟨570921, by rfl⟩ : syracuseStep 1522457 = 1141843) B1141843
theorem B5782337 : Blo 1012602 5782337 := bstep (se 2 (by rfl) ⟨2168376, by rfl⟩ : syracuseStep 5782337 = 4336753) B4336753
theorem B1096535 : Blo 1012602 1096535 := bstep (se 1 (by rfl) ⟨822401, by rfl⟩ : syracuseStep 1096535 = 1644803) B1644803
theorem B8665987 : Blo 1012602 8665987 := bstep (se 1 (by rfl) ⟨6499490, by rfl⟩ : syracuseStep 8665987 = 12998981) B12998981
theorem B1522571 : Blo 1012602 1522571 := bstep (se 1 (by rfl) ⟨1141928, by rfl⟩ : syracuseStep 1522571 = 2283857) B2283857
theorem B1522583 : Blo 1012602 1522583 := bstep (se 1 (by rfl) ⟨1141937, by rfl⟩ : syracuseStep 1522583 = 2283875) B2283875
theorem B7715735 : Blo 1012602 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B6175667 : Blo 1012602 6175667 := bstep (se 1 (by rfl) ⟨4631750, by rfl⟩ : syracuseStep 6175667 = 9263501) B9263501
theorem B1522649 : Blo 1012602 1522649 := bstep (se 2 (by rfl) ⟨570993, by rfl⟩ : syracuseStep 1522649 = 1141987) B1141987
theorem B1522763 : Blo 1012602 1522763 := bstep (se 1 (by rfl) ⟨1142072, by rfl⟩ : syracuseStep 1522763 = 2284145) B2284145
theorem B1522775 : Blo 1012602 1522775 := bstep (se 1 (by rfl) ⟨1142081, by rfl⟩ : syracuseStep 1522775 = 2284163) B2284163
theorem B5127299 : Blo 1012602 5127299 := bstep (se 1 (by rfl) ⟨3845474, by rfl⟩ : syracuseStep 5127299 = 7690949) B7690949
theorem B3423383 : Blo 1012602 3423383 := bstep (se 1 (by rfl) ⟨2567537, by rfl⟩ : syracuseStep 3423383 = 5135075) B5135075
theorem B1522841 : Blo 1012602 1522841 := bstep (se 2 (by rfl) ⟨571065, by rfl⟩ : syracuseStep 1522841 = 1142131) B1142131
theorem B2440385 : Blo 1012602 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B1522955 : Blo 1012602 1522955 := bstep (se 1 (by rfl) ⟨1142216, by rfl⟩ : syracuseStep 1522955 = 2284433) B2284433
theorem B1522967 : Blo 1012602 1522967 := bstep (se 1 (by rfl) ⟨1142225, by rfl⟩ : syracuseStep 1522967 = 2284451) B2284451
theorem B1523033 : Blo 1012602 1523033 := bstep (se 2 (by rfl) ⟨571137, by rfl⟩ : syracuseStep 1523033 = 1142275) B1142275
theorem B6503773 : Blo 1012602 6503773 := bstep (se 3 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 6503773 = 2438915) B2438915
theorem B16465331 : Blo 1012602 16465331 := bstep (se 1 (by rfl) ⟨12348998, by rfl⟩ : syracuseStep 16465331 = 24697997) B24697997
theorem B1523147 : Blo 1012602 1523147 := bstep (se 1 (by rfl) ⟨1142360, by rfl⟩ : syracuseStep 1523147 = 2284721) B2284721
theorem B1523159 : Blo 1012602 1523159 := bstep (se 1 (by rfl) ⟨1142369, by rfl⟩ : syracuseStep 1523159 = 2284739) B2284739
theorem B1523225 : Blo 1012602 1523225 := bstep (se 2 (by rfl) ⟨571209, by rfl⟩ : syracuseStep 1523225 = 1142419) B1142419
theorem B2571851 : Blo 1012602 2571851 := bstep (se 1 (by rfl) ⟨1928888, by rfl⟩ : syracuseStep 2571851 = 3857777) B3857777
theorem B1523339 : Blo 1012602 1523339 := bstep (se 1 (by rfl) ⟨1142504, by rfl⟩ : syracuseStep 1523339 = 2285009) B2285009
theorem B1523351 : Blo 1012602 1523351 := bstep (se 1 (by rfl) ⟨1142513, by rfl⟩ : syracuseStep 1523351 = 2285027) B2285027
theorem B3423923 : Blo 1012602 3423923 := bstep (se 1 (by rfl) ⟨2567942, by rfl⟩ : syracuseStep 3423923 = 5135885) B5135885
theorem B20790989 : Blo 1012602 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B1523417 : Blo 1012602 1523417 := bstep (se 2 (by rfl) ⟨571281, by rfl⟩ : syracuseStep 1523417 = 1142563) B1142563
theorem B3850001 : Blo 1012602 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B8666945 : Blo 1012602 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B1523531 : Blo 1012602 1523531 := bstep (se 1 (by rfl) ⟨1142648, by rfl⟩ : syracuseStep 1523531 = 2285297) B2285297
theorem B1523543 : Blo 1012602 1523543 := bstep (se 1 (by rfl) ⟨1142657, by rfl⟩ : syracuseStep 1523543 = 2285315) B2285315
theorem B1523609 : Blo 1012602 1523609 := bstep (se 2 (by rfl) ⟨571353, by rfl⟩ : syracuseStep 1523609 = 1142707) B1142707
theorem B3424193 : Blo 1012602 3424193 := bstep (se 2 (by rfl) ⟨1284072, by rfl⟩ : syracuseStep 3424193 = 2568145) B2568145
theorem B1523723 : Blo 1012602 1523723 := bstep (se 1 (by rfl) ⟨1142792, by rfl⟩ : syracuseStep 1523723 = 2285585) B2285585
theorem B1523735 : Blo 1012602 1523735 := bstep (se 1 (by rfl) ⟨1142801, by rfl⟩ : syracuseStep 1523735 = 2285603) B2285603
theorem B1523801 : Blo 1012602 1523801 := bstep (se 2 (by rfl) ⟨571425, by rfl⟩ : syracuseStep 1523801 = 1142851) B1142851
theorem B1523915 : Blo 1012602 1523915 := bstep (se 1 (by rfl) ⟨1142936, by rfl⟩ : syracuseStep 1523915 = 2285873) B2285873
theorem B1523927 : Blo 1012602 1523927 := bstep (se 1 (by rfl) ⟨1142945, by rfl⟩ : syracuseStep 1523927 = 2285891) B2285891
theorem B1523993 : Blo 1012602 1523993 := bstep (se 2 (by rfl) ⟨571497, by rfl⟩ : syracuseStep 1523993 = 1142995) B1142995
theorem B1524107 : Blo 1012602 1524107 := bstep (se 1 (by rfl) ⟨1143080, by rfl⟩ : syracuseStep 1524107 = 2286161) B2286161
theorem B1524119 : Blo 1012602 1524119 := bstep (se 1 (by rfl) ⟨1143089, by rfl⟩ : syracuseStep 1524119 = 2286179) B2286179
theorem B3850699 : Blo 1012602 3850699 := bstep (se 1 (by rfl) ⟨2888024, by rfl⟩ : syracuseStep 3850699 = 5776049) B5776049
theorem B1524185 : Blo 1012602 1524185 := bstep (se 2 (by rfl) ⟨571569, by rfl⟩ : syracuseStep 1524185 = 1143139) B1143139
theorem B3424733 : Blo 1012602 3424733 := bstep (se 3 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 3424733 = 1284275) B1284275
theorem B62538257 : Blo 1012602 62538257 := bstep (se 2 (by rfl) ⟨23451846, by rfl⟩ : syracuseStep 62538257 = 46903693) B46903693
theorem B2572823 : Blo 1012602 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B1524299 : Blo 1012602 1524299 := bstep (se 1 (by rfl) ⟨1143224, by rfl⟩ : syracuseStep 1524299 = 2286449) B2286449
theorem B1524311 : Blo 1012602 1524311 := bstep (se 1 (by rfl) ⟨1143233, by rfl⟩ : syracuseStep 1524311 = 2286467) B2286467
theorem B1524377 : Blo 1012602 1524377 := bstep (se 2 (by rfl) ⟨571641, by rfl⟩ : syracuseStep 1524377 = 1143283) B1143283
theorem B3850973 : Blo 1012602 3850973 := bstep (se 3 (by rfl) ⟨722057, by rfl⟩ : syracuseStep 3850973 = 1444115) B1444115
theorem B1524491 : Blo 1012602 1524491 := bstep (se 1 (by rfl) ⟨1143368, by rfl⟩ : syracuseStep 1524491 = 2286737) B2286737
theorem B1524503 : Blo 1012602 1524503 := bstep (se 1 (by rfl) ⟨1143377, by rfl⟩ : syracuseStep 1524503 = 2286755) B2286755
theorem B1524569 : Blo 1012602 1524569 := bstep (se 2 (by rfl) ⟨571713, by rfl⟩ : syracuseStep 1524569 = 1143427) B1143427
theorem B1524683 : Blo 1012602 1524683 := bstep (se 1 (by rfl) ⟨1143512, by rfl⟩ : syracuseStep 1524683 = 2287025) B2287025
theorem B1524695 : Blo 1012602 1524695 := bstep (se 1 (by rfl) ⟨1143521, by rfl⟩ : syracuseStep 1524695 = 2287043) B2287043
theorem B1524761 : Blo 1012602 1524761 := bstep (se 2 (by rfl) ⟨571785, by rfl⟩ : syracuseStep 1524761 = 1143571) B1143571
theorem B2278475 : Blo 1012602 2278475 := bstep (se 1 (by rfl) ⟨1708856, by rfl⟩ : syracuseStep 2278475 = 3417713) B3417713
theorem B2278529 : Blo 1012602 2278529 := bstep (se 2 (by rfl) ⟨854448, by rfl⟩ : syracuseStep 2278529 = 1708897) B1708897
theorem B1524875 : Blo 1012602 1524875 := bstep (se 1 (by rfl) ⟨1143656, by rfl⟩ : syracuseStep 1524875 = 2287313) B2287313
theorem B1524887 : Blo 1012602 1524887 := bstep (se 1 (by rfl) ⟨1143665, by rfl⟩ : syracuseStep 1524887 = 2287331) B2287331
theorem B4113611 : Blo 1012602 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B12993857 : Blo 1012602 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B2278745 : Blo 1012602 2278745 := bstep (se 2 (by rfl) ⟨854529, by rfl⟩ : syracuseStep 2278745 = 1709059) B1709059
theorem B3655043 : Blo 1012602 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B3851671 : Blo 1012602 3851671 := bstep (se 1 (by rfl) ⟨2888753, by rfl⟩ : syracuseStep 3851671 = 5777507) B5777507
theorem B2278835 : Blo 1012602 2278835 := bstep (se 1 (by rfl) ⟨1709126, by rfl⟩ : syracuseStep 2278835 = 3418253) B3418253
theorem B2278871 : Blo 1012602 2278871 := bstep (se 1 (by rfl) ⟨1709153, by rfl⟩ : syracuseStep 2278871 = 3418307) B3418307
theorem B3425867 : Blo 1012602 3425867 := bstep (se 1 (by rfl) ⟨2569400, by rfl⟩ : syracuseStep 3425867 = 5138801) B5138801
theorem B2737757 : Blo 1012602 2737757 := bstep (se 3 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 2737757 = 1026659) B1026659
theorem B2279051 : Blo 1012602 2279051 := bstep (se 1 (by rfl) ⟨1709288, by rfl⟩ : syracuseStep 2279051 = 3418577) B3418577
theorem B2279105 : Blo 1012602 2279105 := bstep (se 2 (by rfl) ⟨854664, by rfl⟩ : syracuseStep 2279105 = 1709329) B1709329
theorem B6506257 : Blo 1012602 6506257 := bstep (se 2 (by rfl) ⟨2439846, by rfl⟩ : syracuseStep 6506257 = 4879693) B4879693
theorem B1853209 : Blo 1012602 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B3426137 : Blo 1012602 3426137 := bstep (se 2 (by rfl) ⟨1284801, by rfl⟩ : syracuseStep 3426137 = 2569603) B2569603
theorem B2279321 : Blo 1012602 2279321 := bstep (se 2 (by rfl) ⟨854745, by rfl⟩ : syracuseStep 2279321 = 1709491) B1709491
theorem B2279411 : Blo 1012602 2279411 := bstep (se 1 (by rfl) ⟨1709558, by rfl⟩ : syracuseStep 2279411 = 3419117) B3419117
theorem B2279447 : Blo 1012602 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B3852461 : Blo 1012602 3852461 := bstep (se 3 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 3852461 = 1444673) B1444673
theorem B2279627 : Blo 1012602 2279627 := bstep (se 1 (by rfl) ⟨1709720, by rfl⟩ : syracuseStep 2279627 = 3419441) B3419441
theorem B2279681 : Blo 1012602 2279681 := bstep (se 2 (by rfl) ⟨854880, by rfl⟩ : syracuseStep 2279681 = 1709761) B1709761
theorem B2279897 : Blo 1012602 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B3656195 : Blo 1012602 3656195 := bstep (se 1 (by rfl) ⟨2742146, by rfl⟩ : syracuseStep 3656195 = 5484293) B5484293
theorem B3426839 : Blo 1012602 3426839 := bstep (se 1 (by rfl) ⟨2570129, by rfl⟩ : syracuseStep 3426839 = 5140259) B5140259
theorem B2279987 : Blo 1012602 2279987 := bstep (se 1 (by rfl) ⟨1709990, by rfl⟩ : syracuseStep 2279987 = 3419981) B3419981
theorem B2280023 : Blo 1012602 2280023 := bstep (se 1 (by rfl) ⟨1710017, by rfl⟩ : syracuseStep 2280023 = 3420035) B3420035
theorem B2280203 : Blo 1012602 2280203 := bstep (se 1 (by rfl) ⟨1710152, by rfl⟩ : syracuseStep 2280203 = 3420305) B3420305
theorem B5131025 : Blo 1012602 5131025 := bstep (se 2 (by rfl) ⟨1924134, by rfl⟩ : syracuseStep 5131025 = 3848269) B3848269
theorem B2280257 : Blo 1012602 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B28167011 : Blo 1012602 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B5131187 : Blo 1012602 5131187 := bstep (se 1 (by rfl) ⟨3848390, by rfl⟩ : syracuseStep 5131187 = 7696781) B7696781
theorem B2280473 : Blo 1012602 2280473 := bstep (se 2 (by rfl) ⟨855177, by rfl⟩ : syracuseStep 2280473 = 1710355) B1710355
theorem B3427379 : Blo 1012602 3427379 := bstep (se 1 (by rfl) ⟨2570534, by rfl⟩ : syracuseStep 3427379 = 5141069) B5141069
theorem B3296321 : Blo 1012602 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B2280563 : Blo 1012602 2280563 := bstep (se 1 (by rfl) ⟨1710422, by rfl⟩ : syracuseStep 2280563 = 3420845) B3420845
theorem B2280599 : Blo 1012602 2280599 := bstep (se 1 (by rfl) ⟨1710449, by rfl⟩ : syracuseStep 2280599 = 3420899) B3420899
theorem B2739379 : Blo 1012602 2739379 := bstep (se 1 (by rfl) ⟨2054534, by rfl⟩ : syracuseStep 2739379 = 4109069) B4109069
theorem B3427649 : Blo 1012602 3427649 := bstep (se 2 (by rfl) ⟨1285368, by rfl⟩ : syracuseStep 3427649 = 2570737) B2570737
theorem B2280779 : Blo 1012602 2280779 := bstep (se 1 (by rfl) ⟨1710584, by rfl⟩ : syracuseStep 2280779 = 3421169) B3421169
theorem B2280833 : Blo 1012602 2280833 := bstep (se 2 (by rfl) ⟨855312, by rfl⟩ : syracuseStep 2280833 = 1710625) B1710625
theorem B1625483 : Blo 1012602 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B2117081 : Blo 1012602 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B3853889 : Blo 1012602 3853889 := bstep (se 2 (by rfl) ⟨1445208, by rfl⟩ : syracuseStep 3853889 = 2890417) B2890417
theorem B2281049 : Blo 1012602 2281049 := bstep (se 2 (by rfl) ⟨855393, by rfl⟩ : syracuseStep 2281049 = 1710787) B1710787
theorem B2281139 : Blo 1012602 2281139 := bstep (se 1 (by rfl) ⟨1710854, by rfl⟩ : syracuseStep 2281139 = 3421709) B3421709
theorem B2281175 : Blo 1012602 2281175 := bstep (se 1 (by rfl) ⟨1710881, by rfl⟩ : syracuseStep 2281175 = 3421763) B3421763
theorem B3428189 : Blo 1012602 3428189 := bstep (se 3 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 3428189 = 1285571) B1285571
theorem B2281355 : Blo 1012602 2281355 := bstep (se 1 (by rfl) ⟨1711016, by rfl⟩ : syracuseStep 2281355 = 3422033) B3422033
theorem B2281409 : Blo 1012602 2281409 := bstep (se 2 (by rfl) ⟨855528, by rfl⟩ : syracuseStep 2281409 = 1711057) B1711057
theorem B5787713 : Blo 1012602 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B7819415 : Blo 1012602 7819415 := bstep (se 1 (by rfl) ⟨5864561, by rfl⟩ : syracuseStep 7819415 = 11729123) B11729123
theorem B2281625 : Blo 1012602 2281625 := bstep (se 2 (by rfl) ⟨855609, by rfl⟩ : syracuseStep 2281625 = 1711219) B1711219
theorem B2281715 : Blo 1012602 2281715 := bstep (se 1 (by rfl) ⟨1711286, by rfl⟩ : syracuseStep 2281715 = 3422573) B3422573
theorem B2281751 : Blo 1012602 2281751 := bstep (se 1 (by rfl) ⟨1711313, by rfl⟩ : syracuseStep 2281751 = 3422627) B3422627
theorem B2281931 : Blo 1012602 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B2281985 : Blo 1012602 2281985 := bstep (se 2 (by rfl) ⟨855744, by rfl⟩ : syracuseStep 2281985 = 1711489) B1711489
theorem B7819841 : Blo 1012602 7819841 := bstep (se 2 (by rfl) ⟨2932440, by rfl⟩ : syracuseStep 7819841 = 5864881) B5864881
theorem B1626713 : Blo 1012602 1626713 := bstep (se 2 (by rfl) ⟨610017, by rfl⟩ : syracuseStep 1626713 = 1220035) B1220035
theorem B2282201 : Blo 1012602 2282201 := bstep (se 2 (by rfl) ⟨855825, by rfl⟩ : syracuseStep 2282201 = 1711651) B1711651
theorem B2282291 : Blo 1012602 2282291 := bstep (se 1 (by rfl) ⟨1711718, by rfl⟩ : syracuseStep 2282291 = 3423437) B3423437
theorem B5133131 : Blo 1012602 5133131 := bstep (se 1 (by rfl) ⟨3849848, by rfl⟩ : syracuseStep 5133131 = 7699697) B7699697
theorem B2282327 : Blo 1012602 2282327 := bstep (se 1 (by rfl) ⟨1711745, by rfl⟩ : syracuseStep 2282327 = 3423491) B3423491
theorem B2053043 : Blo 1012602 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B3429323 : Blo 1012602 3429323 := bstep (se 1 (by rfl) ⟨2571992, by rfl⟩ : syracuseStep 3429323 = 5143985) B5143985
theorem B2282507 : Blo 1012602 2282507 := bstep (se 1 (by rfl) ⟨1711880, by rfl⟩ : syracuseStep 2282507 = 3423761) B3423761
theorem B3855377 : Blo 1012602 3855377 := bstep (se 2 (by rfl) ⟨1445766, by rfl⟩ : syracuseStep 3855377 = 2891533) B2891533
theorem B2282561 : Blo 1012602 2282561 := bstep (se 2 (by rfl) ⟨855960, by rfl⟩ : syracuseStep 2282561 = 1711921) B1711921
theorem B6935645 : Blo 1012602 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B3429593 : Blo 1012602 3429593 := bstep (se 2 (by rfl) ⟨1286097, by rfl⟩ : syracuseStep 3429593 = 2572195) B2572195
theorem B2282777 : Blo 1012602 2282777 := bstep (se 2 (by rfl) ⟨856041, by rfl⟩ : syracuseStep 2282777 = 1712083) B1712083
theorem B10966337 : Blo 1012602 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B2282867 : Blo 1012602 2282867 := bstep (se 1 (by rfl) ⟨1712150, by rfl⟩ : syracuseStep 2282867 = 3424301) B3424301
theorem B2282903 : Blo 1012602 2282903 := bstep (se 1 (by rfl) ⟨1712177, by rfl⟩ : syracuseStep 2282903 = 3424355) B3424355
theorem B3855833 : Blo 1012602 3855833 := bstep (se 2 (by rfl) ⟨1445937, by rfl⟩ : syracuseStep 3855833 = 2891875) B2891875
theorem B2283083 : Blo 1012602 2283083 := bstep (se 1 (by rfl) ⟨1712312, by rfl⟩ : syracuseStep 2283083 = 3424625) B3424625
theorem B2283137 : Blo 1012602 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B6182531 : Blo 1012602 6182531 := bstep (se 1 (by rfl) ⟨4636898, by rfl⟩ : syracuseStep 6182531 = 9273797) B9273797
theorem B3856045 : Blo 1012602 3856045 := bstep (se 3 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 3856045 = 1446017) B1446017
theorem B1922753 : Blo 1012602 1922753 := bstep (se 2 (by rfl) ⟨721032, by rfl⟩ : syracuseStep 1922753 = 1442065) B1442065
theorem B2283353 : Blo 1012602 2283353 := bstep (se 2 (by rfl) ⟨856257, by rfl⟩ : syracuseStep 2283353 = 1712515) B1712515
theorem B3430295 : Blo 1012602 3430295 := bstep (se 1 (by rfl) ⟨2572721, by rfl⟩ : syracuseStep 3430295 = 5145443) B5145443
theorem B2283443 : Blo 1012602 2283443 := bstep (se 1 (by rfl) ⟨1712582, by rfl⟩ : syracuseStep 2283443 = 3425165) B3425165
theorem B2054081 : Blo 1012602 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B2283479 : Blo 1012602 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B3856349 : Blo 1012602 3856349 := bstep (se 3 (by rfl) ⟨723065, by rfl⟩ : syracuseStep 3856349 = 1446131) B1446131
theorem B1923095 : Blo 1012602 1923095 := bstep (se 1 (by rfl) ⟨1442321, by rfl⟩ : syracuseStep 1923095 = 2884643) B2884643
theorem B2283659 : Blo 1012602 2283659 := bstep (se 1 (by rfl) ⟨1712744, by rfl⟩ : syracuseStep 2283659 = 3425489) B3425489
theorem B2283713 : Blo 1012602 2283713 := bstep (se 2 (by rfl) ⟨856392, by rfl⟩ : syracuseStep 2283713 = 1712785) B1712785
theorem B2742493 : Blo 1012602 2742493 := bstep (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) B1028435
theorem B2283929 : Blo 1012602 2283929 := bstep (se 2 (by rfl) ⟨856473, by rfl⟩ : syracuseStep 2283929 = 1712947) B1712947
theorem B3430835 : Blo 1012602 3430835 := bstep (se 1 (by rfl) ⟨2573126, by rfl⟩ : syracuseStep 3430835 = 5146253) B5146253
theorem B2284019 : Blo 1012602 2284019 := bstep (se 1 (by rfl) ⟨1713014, by rfl⟩ : syracuseStep 2284019 = 3426029) B3426029
theorem B2284055 : Blo 1012602 2284055 := bstep (se 1 (by rfl) ⟨1713041, by rfl⟩ : syracuseStep 2284055 = 3426083) B3426083
theorem B5134913 : Blo 1012602 5134913 := bstep (se 2 (by rfl) ⟨1925592, by rfl⟩ : syracuseStep 5134913 = 3851185) B3851185
theorem B1923763 : Blo 1012602 1923763 := bstep (se 1 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 1923763 = 2885645) B2885645
theorem B2284235 : Blo 1012602 2284235 := bstep (se 1 (by rfl) ⟨1713176, by rfl⟩ : syracuseStep 2284235 = 3426353) B3426353
theorem B2284289 : Blo 1012602 2284289 := bstep (se 2 (by rfl) ⟨856608, by rfl⟩ : syracuseStep 2284289 = 1713217) B1713217
theorem B2284505 : Blo 1012602 2284505 := bstep (se 2 (by rfl) ⟨856689, by rfl⟩ : syracuseStep 2284505 = 1713379) B1713379
theorem B1301527 : Blo 1012602 1301527 := bstep (se 1 (by rfl) ⟨976145, by rfl⟩ : syracuseStep 1301527 = 1952291) B1952291
theorem B2284595 : Blo 1012602 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B6511691 : Blo 1012602 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B2284631 : Blo 1012602 2284631 := bstep (se 1 (by rfl) ⟨1713473, by rfl⟩ : syracuseStep 2284631 = 3426947) B3426947
theorem B1924211 : Blo 1012602 1924211 := bstep (se 1 (by rfl) ⟨1443158, by rfl⟩ : syracuseStep 1924211 = 2886317) B2886317
theorem B1924249 : Blo 1012602 1924249 := bstep (se 2 (by rfl) ⟨721593, by rfl⟩ : syracuseStep 1924249 = 1443187) B1443187
theorem B2284811 : Blo 1012602 2284811 := bstep (se 1 (by rfl) ⟨1713608, by rfl⟩ : syracuseStep 2284811 = 3427217) B3427217
theorem B2284865 : Blo 1012602 2284865 := bstep (se 2 (by rfl) ⟨856824, by rfl⟩ : syracuseStep 2284865 = 1713649) B1713649
theorem B17325413 : Blo 1012602 17325413 := bstep (se 4 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 17325413 = 3248515) B3248515
theorem B4120001 : Blo 1012602 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B2285081 : Blo 1012602 2285081 := bstep (se 2 (by rfl) ⟨856905, by rfl⟩ : syracuseStep 2285081 = 1713811) B1713811
theorem B1924697 : Blo 1012602 1924697 := bstep (se 2 (by rfl) ⟨721761, by rfl⟩ : syracuseStep 1924697 = 1443523) B1443523
theorem B8347229 : Blo 1012602 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B2285171 : Blo 1012602 2285171 := bstep (se 1 (by rfl) ⟨1713878, by rfl⟩ : syracuseStep 2285171 = 3427757) B3427757
theorem B2285207 : Blo 1012602 2285207 := bstep (se 1 (by rfl) ⟨1713905, by rfl⟩ : syracuseStep 2285207 = 3427811) B3427811
theorem B1171147 : Blo 1012602 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B2285387 : Blo 1012602 2285387 := bstep (se 1 (by rfl) ⟨1714040, by rfl⟩ : syracuseStep 2285387 = 3428081) B3428081
theorem B4939613 : Blo 1012602 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B2285441 : Blo 1012602 2285441 := bstep (se 2 (by rfl) ⟨857040, by rfl⟩ : syracuseStep 2285441 = 1714081) B1714081
theorem B2285657 : Blo 1012602 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B1826945 : Blo 1012602 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B2285747 : Blo 1012602 2285747 := bstep (se 1 (by rfl) ⟨1714310, by rfl⟩ : syracuseStep 2285747 = 3428621) B3428621
theorem B1827031 : Blo 1012602 1827031 := bstep (se 1 (by rfl) ⟨1370273, by rfl⟩ : syracuseStep 1827031 = 2740547) B2740547
theorem B2285783 : Blo 1012602 2285783 := bstep (se 1 (by rfl) ⟨1714337, by rfl⟩ : syracuseStep 2285783 = 3428675) B3428675
theorem B1925441 : Blo 1012602 1925441 := bstep (se 2 (by rfl) ⟨722040, by rfl⟩ : syracuseStep 1925441 = 1444081) B1444081
theorem B2285963 : Blo 1012602 2285963 := bstep (se 1 (by rfl) ⟨1714472, by rfl⟩ : syracuseStep 2285963 = 3428945) B3428945
theorem B2286017 : Blo 1012602 2286017 := bstep (se 2 (by rfl) ⟨857256, by rfl⟩ : syracuseStep 2286017 = 1714513) B1714513
theorem B5136857 : Blo 1012602 5136857 := bstep (se 2 (by rfl) ⟨1926321, by rfl⟩ : syracuseStep 5136857 = 3852643) B3852643
theorem B1139179 : Blo 1012602 1139179 := bstep (se 1 (by rfl) ⟨854384, by rfl⟩ : syracuseStep 1139179 = 1708769) B1708769
theorem B3858947 : Blo 1012602 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B3858961 : Blo 1012602 3858961 := bstep (se 2 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 3858961 = 2894221) B2894221
theorem B1925707 : Blo 1012602 1925707 := bstep (se 1 (by rfl) ⟨1444280, by rfl⟩ : syracuseStep 1925707 = 2888561) B2888561
theorem B1139287 : Blo 1012602 1139287 := bstep (se 1 (by rfl) ⟨854465, by rfl⟩ : syracuseStep 1139287 = 1708931) B1708931
theorem B7692893 : Blo 1012602 7692893 := bstep (se 3 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 7692893 = 2884835) B2884835
theorem B2286233 : Blo 1012602 2286233 := bstep (se 2 (by rfl) ⟨857337, by rfl⟩ : syracuseStep 2286233 = 1714675) B1714675
theorem B6513331 : Blo 1012602 6513331 := bstep (se 1 (by rfl) ⟨4884998, by rfl⟩ : syracuseStep 6513331 = 9769997) B9769997
theorem B1172183 : Blo 1012602 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B2286323 : Blo 1012602 2286323 := bstep (se 1 (by rfl) ⟨1714742, by rfl⟩ : syracuseStep 2286323 = 3429485) B3429485
theorem B1139467 : Blo 1012602 1139467 := bstep (se 1 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 1139467 = 1709201) B1709201
theorem B2286359 : Blo 1012602 2286359 := bstep (se 1 (by rfl) ⟨1714769, by rfl⟩ : syracuseStep 2286359 = 3429539) B3429539
theorem B3859265 : Blo 1012602 3859265 := bstep (se 2 (by rfl) ⟨1447224, by rfl⟩ : syracuseStep 3859265 = 2894449) B2894449
theorem B1139575 : Blo 1012602 1139575 := bstep (se 1 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 1139575 = 1709363) B1709363
theorem B5202839 : Blo 1012602 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B2286539 : Blo 1012602 2286539 := bstep (se 1 (by rfl) ⟨1714904, by rfl⟩ : syracuseStep 2286539 = 3429809) B3429809
theorem B2286593 : Blo 1012602 2286593 := bstep (se 2 (by rfl) ⟨857472, by rfl⟩ : syracuseStep 2286593 = 1714945) B1714945
theorem B1926155 : Blo 1012602 1926155 := bstep (se 1 (by rfl) ⟨1444616, by rfl⟩ : syracuseStep 1926155 = 2889233) B2889233
theorem B1139755 : Blo 1012602 1139755 := bstep (se 1 (by rfl) ⟨854816, by rfl⟩ : syracuseStep 1139755 = 1709633) B1709633
theorem B1139863 : Blo 1012602 1139863 := bstep (se 1 (by rfl) ⟨854897, by rfl⟩ : syracuseStep 1139863 = 1709795) B1709795
theorem B9757847 : Blo 1012602 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B1926337 : Blo 1012602 1926337 := bstep (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) B1444753
theorem B1828055 : Blo 1012602 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B2286809 : Blo 1012602 2286809 := bstep (se 2 (by rfl) ⟨857553, by rfl⟩ : syracuseStep 2286809 = 1715107) B1715107
theorem B2286899 : Blo 1012602 2286899 := bstep (se 1 (by rfl) ⟨1715174, by rfl⟩ : syracuseStep 2286899 = 3430349) B3430349
theorem B1140043 : Blo 1012602 1140043 := bstep (se 1 (by rfl) ⟨855032, by rfl⟩ : syracuseStep 1140043 = 1710065) B1710065
theorem B2286935 : Blo 1012602 2286935 := bstep (se 1 (by rfl) ⟨1715201, by rfl⟩ : syracuseStep 2286935 = 3430403) B3430403
theorem B1369495 : Blo 1012602 1369495 := bstep (se 1 (by rfl) ⟨1027121, by rfl⟩ : syracuseStep 1369495 = 2054243) B2054243
theorem B1140151 : Blo 1012602 1140151 := bstep (se 1 (by rfl) ⟨855113, by rfl⟩ : syracuseStep 1140151 = 1710227) B1710227
theorem B2287115 : Blo 1012602 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B1926679 : Blo 1012602 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B2287169 : Blo 1012602 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B1140331 : Blo 1012602 1140331 := bstep (se 1 (by rfl) ⟨855248, by rfl⟩ : syracuseStep 1140331 = 1710497) B1710497
theorem B1140439 : Blo 1012602 1140439 := bstep (se 1 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 1140439 = 1710659) B1710659
theorem B1926899 : Blo 1012602 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B1140619 : Blo 1012602 1140619 := bstep (se 1 (by rfl) ⟨855464, by rfl⟩ : syracuseStep 1140619 = 1710929) B1710929
theorem B1927127 : Blo 1012602 1927127 := bstep (se 1 (by rfl) ⟨1445345, by rfl⟩ : syracuseStep 1927127 = 2890691) B2890691
theorem B1140727 : Blo 1012602 1140727 := bstep (se 1 (by rfl) ⟨855545, by rfl⟩ : syracuseStep 1140727 = 1711091) B1711091
theorem B5138477 : Blo 1012602 5138477 := bstep (se 3 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 5138477 = 1926929) B1926929
theorem B8677469 : Blo 1012602 8677469 := bstep (se 3 (by rfl) ⟨1627025, by rfl⟩ : syracuseStep 8677469 = 3254051) B3254051
theorem B1370263 : Blo 1012602 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B1140907 : Blo 1012602 1140907 := bstep (se 1 (by rfl) ⟨855680, by rfl⟩ : syracuseStep 1140907 = 1711361) B1711361
theorem B1927385 : Blo 1012602 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1141015 : Blo 1012602 1141015 := bstep (se 1 (by rfl) ⟨855761, by rfl⟩ : syracuseStep 1141015 = 1711523) B1711523
theorem B55568753 : Blo 1012602 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B16673141 : Blo 1012602 16673141 := bstep (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) B1563107
theorem B1141195 : Blo 1012602 1141195 := bstep (se 1 (by rfl) ⟨855896, by rfl⟩ : syracuseStep 1141195 = 1711793) B1711793
theorem B1829323 : Blo 1012602 1829323 := bstep (se 1 (by rfl) ⟨1371992, by rfl⟩ : syracuseStep 1829323 = 2743985) B2743985
theorem B1141303 : Blo 1012602 1141303 := bstep (se 1 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 1141303 = 1711955) B1711955
theorem B1927795 : Blo 1012602 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B1141483 : Blo 1012602 1141483 := bstep (se 1 (by rfl) ⟨856112, by rfl⟩ : syracuseStep 1141483 = 1712225) B1712225
theorem B1141591 : Blo 1012602 1141591 := bstep (se 1 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 1141591 = 1712387) B1712387
theorem B1829785 : Blo 1012602 1829785 := bstep (se 2 (by rfl) ⟨686169, by rfl⟩ : syracuseStep 1829785 = 1372339) B1372339
theorem B4877273 : Blo 1012602 4877273 := bstep (se 2 (by rfl) ⟨1828977, by rfl⟩ : syracuseStep 4877273 = 3657955) B3657955
theorem B1141771 : Blo 1012602 1141771 := bstep (se 1 (by rfl) ⟨856328, by rfl⟩ : syracuseStep 1141771 = 1712657) B1712657
theorem B4877387 : Blo 1012602 4877387 := bstep (se 1 (by rfl) ⟨3658040, by rfl⟩ : syracuseStep 4877387 = 7316081) B7316081
theorem B1928281 : Blo 1012602 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B1141879 : Blo 1012602 1141879 := bstep (se 1 (by rfl) ⟨856409, by rfl⟩ : syracuseStep 1141879 = 1712819) B1712819
theorem B1142059 : Blo 1012602 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B1142167 : Blo 1012602 1142167 := bstep (se 1 (by rfl) ⟨856625, by rfl⟩ : syracuseStep 1142167 = 1713251) B1713251
theorem B17558963 : Blo 1012602 17558963 := bstep (se 1 (by rfl) ⟨13169222, by rfl⟩ : syracuseStep 17558963 = 26338445) B26338445
theorem B1830347 : Blo 1012602 1830347 := bstep (se 1 (by rfl) ⟨1372760, by rfl⟩ : syracuseStep 1830347 = 2745521) B2745521
theorem B1142347 : Blo 1012602 1142347 := bstep (se 1 (by rfl) ⟨856760, by rfl⟩ : syracuseStep 1142347 = 1713521) B1713521
theorem B1928843 : Blo 1012602 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B1142455 : Blo 1012602 1142455 := bstep (se 1 (by rfl) ⟨856841, by rfl⟩ : syracuseStep 1142455 = 1713683) B1713683
theorem B1929025 : Blo 1012602 1929025 := bstep (se 2 (by rfl) ⟨723384, by rfl⟩ : syracuseStep 1929025 = 1446769) B1446769
theorem B1142635 : Blo 1012602 1142635 := bstep (se 1 (by rfl) ⟨856976, by rfl⟩ : syracuseStep 1142635 = 1713953) B1713953
theorem B1142743 : Blo 1012602 1142743 := bstep (se 1 (by rfl) ⟨857057, by rfl⟩ : syracuseStep 1142743 = 1714115) B1714115
theorem B3764227 : Blo 1012602 3764227 := bstep (se 1 (by rfl) ⟨2823170, by rfl⟩ : syracuseStep 3764227 = 5646341) B5646341
theorem B1142923 : Blo 1012602 1142923 := bstep (se 1 (by rfl) ⟨857192, by rfl⟩ : syracuseStep 1142923 = 1714385) B1714385
theorem B1143031 : Blo 1012602 1143031 := bstep (se 1 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 1143031 = 1714547) B1714547
theorem B1831169 : Blo 1012602 1831169 := bstep (se 2 (by rfl) ⟨686688, by rfl⟩ : syracuseStep 1831169 = 1373377) B1373377
theorem B1143211 : Blo 1012602 1143211 := bstep (se 1 (by rfl) ⟨857408, by rfl⟩ : syracuseStep 1143211 = 1714817) B1714817
theorem B1831385 : Blo 1012602 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B1929739 : Blo 1012602 1929739 := bstep (se 1 (by rfl) ⟨1447304, by rfl⟩ : syracuseStep 1929739 = 2894609) B2894609
theorem B1143319 : Blo 1012602 1143319 := bstep (se 1 (by rfl) ⟨857489, by rfl⟩ : syracuseStep 1143319 = 1714979) B1714979
theorem B1929815 : Blo 1012602 1929815 := bstep (se 1 (by rfl) ⟨1447361, by rfl⟩ : syracuseStep 1929815 = 2894723) B2894723
theorem B6255197 : Blo 1012602 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B8680067 : Blo 1012602 8680067 := bstep (se 1 (by rfl) ⟨6510050, by rfl⟩ : syracuseStep 8680067 = 13020101) B13020101
theorem B1143499 : Blo 1012602 1143499 := bstep (se 1 (by rfl) ⟨857624, by rfl⟩ : syracuseStep 1143499 = 1715249) B1715249
theorem B7729937 : Blo 1012602 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B4682519 : Blo 1012602 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B1143607 : Blo 1012602 1143607 := bstep (se 1 (by rfl) ⟨857705, by rfl⟩ : syracuseStep 1143607 = 1715411) B1715411
theorem B1012619 : Blo 1012602 1012619 := bstep (se 1 (by rfl) ⟨759464, by rfl⟩ : syracuseStep 1012619 = 1518929) B1518929
theorem B1012631 : Blo 1012602 1012631 := bstep (se 1 (by rfl) ⟨759473, by rfl⟩ : syracuseStep 1012631 = 1518947) B1518947
theorem B1012651 : Blo 1012602 1012651 := bstep (se 1 (by rfl) ⟨759488, by rfl⟩ : syracuseStep 1012651 = 1518977) B1518977
theorem B1012663 : Blo 1012602 1012663 := bstep (se 1 (by rfl) ⟨759497, by rfl⟩ : syracuseStep 1012663 = 1518995) B1518995
theorem B1012683 : Blo 1012602 1012683 := bstep (se 1 (by rfl) ⟨759512, by rfl⟩ : syracuseStep 1012683 = 1519025) B1519025
theorem B1012695 : Blo 1012602 1012695 := bstep (se 1 (by rfl) ⟨759521, by rfl⟩ : syracuseStep 1012695 = 1519043) B1519043
theorem B1012715 : Blo 1012602 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B1012727 : Blo 1012602 1012727 := bstep (se 1 (by rfl) ⟨759545, by rfl⟩ : syracuseStep 1012727 = 1519091) B1519091
theorem B1012747 : Blo 1012602 1012747 := bstep (se 1 (by rfl) ⟨759560, by rfl⟩ : syracuseStep 1012747 = 1519121) B1519121
theorem B1012759 : Blo 1012602 1012759 := bstep (se 1 (by rfl) ⟨759569, by rfl⟩ : syracuseStep 1012759 = 1519139) B1519139
theorem B1012779 : Blo 1012602 1012779 := bstep (se 1 (by rfl) ⟨759584, by rfl⟩ : syracuseStep 1012779 = 1519169) B1519169
theorem B1012791 : Blo 1012602 1012791 := bstep (se 1 (by rfl) ⟨759593, by rfl⟩ : syracuseStep 1012791 = 1519187) B1519187
theorem B1012811 : Blo 1012602 1012811 := bstep (se 1 (by rfl) ⟨759608, by rfl⟩ : syracuseStep 1012811 = 1519217) B1519217
theorem B1012823 : Blo 1012602 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B1012843 : Blo 1012602 1012843 := bstep (se 1 (by rfl) ⟨759632, by rfl⟩ : syracuseStep 1012843 = 1519265) B1519265
theorem B1012855 : Blo 1012602 1012855 := bstep (se 1 (by rfl) ⟨759641, by rfl⟩ : syracuseStep 1012855 = 1519283) B1519283
theorem B1012875 : Blo 1012602 1012875 := bstep (se 1 (by rfl) ⟨759656, by rfl⟩ : syracuseStep 1012875 = 1519313) B1519313
theorem B1012887 : Blo 1012602 1012887 := bstep (se 1 (by rfl) ⟨759665, by rfl⟩ : syracuseStep 1012887 = 1519331) B1519331
theorem B1012907 : Blo 1012602 1012907 := bstep (se 1 (by rfl) ⟨759680, by rfl⟩ : syracuseStep 1012907 = 1519361) B1519361
theorem B1012919 : Blo 1012602 1012919 := bstep (se 1 (by rfl) ⟨759689, by rfl⟩ : syracuseStep 1012919 = 1519379) B1519379
theorem B1012939 : Blo 1012602 1012939 := bstep (se 1 (by rfl) ⟨759704, by rfl⟩ : syracuseStep 1012939 = 1519409) B1519409
theorem B1012951 : Blo 1012602 1012951 := bstep (se 1 (by rfl) ⟨759713, by rfl⟩ : syracuseStep 1012951 = 1519427) B1519427
theorem B6943961 : Blo 1012602 6943961 := bstep (se 2 (by rfl) ⟨2603985, by rfl⟩ : syracuseStep 6943961 = 5207971) B5207971
theorem B1012971 : Blo 1012602 1012971 := bstep (se 1 (by rfl) ⟨759728, by rfl⟩ : syracuseStep 1012971 = 1519457) B1519457
theorem B1012983 : Blo 1012602 1012983 := bstep (se 1 (by rfl) ⟨759737, by rfl⟩ : syracuseStep 1012983 = 1519475) B1519475
theorem B1013003 : Blo 1012602 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B1013015 : Blo 1012602 1013015 := bstep (se 1 (by rfl) ⟨759761, by rfl⟩ : syracuseStep 1013015 = 1519523) B1519523
theorem B1013035 : Blo 1012602 1013035 := bstep (se 1 (by rfl) ⟨759776, by rfl⟩ : syracuseStep 1013035 = 1519553) B1519553
theorem B1013047 : Blo 1012602 1013047 := bstep (se 1 (by rfl) ⟨759785, by rfl⟩ : syracuseStep 1013047 = 1519571) B1519571
theorem B1013067 : Blo 1012602 1013067 := bstep (se 1 (by rfl) ⟨759800, by rfl⟩ : syracuseStep 1013067 = 1519601) B1519601
theorem B1013079 : Blo 1012602 1013079 := bstep (se 1 (by rfl) ⟨759809, by rfl⟩ : syracuseStep 1013079 = 1519619) B1519619
theorem B1013099 : Blo 1012602 1013099 := bstep (se 1 (by rfl) ⟨759824, by rfl⟩ : syracuseStep 1013099 = 1519649) B1519649
theorem B1013111 : Blo 1012602 1013111 := bstep (se 1 (by rfl) ⟨759833, by rfl⟩ : syracuseStep 1013111 = 1519667) B1519667
theorem B1013131 : Blo 1012602 1013131 := bstep (se 1 (by rfl) ⟨759848, by rfl⟩ : syracuseStep 1013131 = 1519697) B1519697
theorem B1013143 : Blo 1012602 1013143 := bstep (se 1 (by rfl) ⟨759857, by rfl⟩ : syracuseStep 1013143 = 1519715) B1519715
theorem B1013163 : Blo 1012602 1013163 := bstep (se 1 (by rfl) ⟨759872, by rfl⟩ : syracuseStep 1013163 = 1519745) B1519745
theorem B13170097 : Blo 1012602 13170097 := bstep (se 2 (by rfl) ⟨4938786, by rfl⟩ : syracuseStep 13170097 = 9877573) B9877573
theorem B1013175 : Blo 1012602 1013175 := bstep (se 1 (by rfl) ⟨759881, by rfl⟩ : syracuseStep 1013175 = 1519763) B1519763
theorem B1013195 : Blo 1012602 1013195 := bstep (se 1 (by rfl) ⟨759896, by rfl⟩ : syracuseStep 1013195 = 1519793) B1519793
theorem B1013207 : Blo 1012602 1013207 := bstep (se 1 (by rfl) ⟨759905, by rfl⟩ : syracuseStep 1013207 = 1519811) B1519811
theorem B1013227 : Blo 1012602 1013227 := bstep (se 1 (by rfl) ⟨759920, by rfl⟩ : syracuseStep 1013227 = 1519841) B1519841
theorem B1013239 : Blo 1012602 1013239 := bstep (se 1 (by rfl) ⟨759929, by rfl⟩ : syracuseStep 1013239 = 1519859) B1519859
theorem B1013259 : Blo 1012602 1013259 := bstep (se 1 (by rfl) ⟨759944, by rfl⟩ : syracuseStep 1013259 = 1519889) B1519889
theorem B1373707 : Blo 1012602 1373707 := bstep (se 1 (by rfl) ⟨1030280, by rfl⟩ : syracuseStep 1373707 = 2060561) B2060561
theorem B1013271 : Blo 1012602 1013271 := bstep (se 1 (by rfl) ⟨759953, by rfl⟩ : syracuseStep 1013271 = 1519907) B1519907
theorem B1013291 : Blo 1012602 1013291 := bstep (se 1 (by rfl) ⟨759968, by rfl⟩ : syracuseStep 1013291 = 1519937) B1519937
theorem B1013303 : Blo 1012602 1013303 := bstep (se 1 (by rfl) ⟨759977, by rfl⟩ : syracuseStep 1013303 = 1519955) B1519955
theorem B1013323 : Blo 1012602 1013323 := bstep (se 1 (by rfl) ⟨759992, by rfl⟩ : syracuseStep 1013323 = 1519985) B1519985
theorem B1013335 : Blo 1012602 1013335 := bstep (se 1 (by rfl) ⟨760001, by rfl⟩ : syracuseStep 1013335 = 1520003) B1520003
theorem B1013355 : Blo 1012602 1013355 := bstep (se 1 (by rfl) ⟨760016, by rfl⟩ : syracuseStep 1013355 = 1520033) B1520033
theorem B1013367 : Blo 1012602 1013367 := bstep (se 1 (by rfl) ⟨760025, by rfl⟩ : syracuseStep 1013367 = 1520051) B1520051
theorem B1013387 : Blo 1012602 1013387 := bstep (se 1 (by rfl) ⟨760040, by rfl⟩ : syracuseStep 1013387 = 1520081) B1520081
theorem B1013399 : Blo 1012602 1013399 := bstep (se 1 (by rfl) ⟨760049, by rfl⟩ : syracuseStep 1013399 = 1520099) B1520099
theorem B1013419 : Blo 1012602 1013419 := bstep (se 1 (by rfl) ⟨760064, by rfl⟩ : syracuseStep 1013419 = 1520129) B1520129
theorem B1013431 : Blo 1012602 1013431 := bstep (se 1 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 1013431 = 1520147) B1520147
theorem B1013451 : Blo 1012602 1013451 := bstep (se 1 (by rfl) ⟨760088, by rfl⟩ : syracuseStep 1013451 = 1520177) B1520177
theorem B1013463 : Blo 1012602 1013463 := bstep (se 1 (by rfl) ⟨760097, by rfl⟩ : syracuseStep 1013463 = 1520195) B1520195
theorem B1013483 : Blo 1012602 1013483 := bstep (se 1 (by rfl) ⟨760112, by rfl⟩ : syracuseStep 1013483 = 1520225) B1520225
theorem B1013495 : Blo 1012602 1013495 := bstep (se 1 (by rfl) ⟨760121, by rfl⟩ : syracuseStep 1013495 = 1520243) B1520243
theorem B1013515 : Blo 1012602 1013515 := bstep (se 1 (by rfl) ⟨760136, by rfl⟩ : syracuseStep 1013515 = 1520273) B1520273
theorem B1013527 : Blo 1012602 1013527 := bstep (se 1 (by rfl) ⟨760145, by rfl⟩ : syracuseStep 1013527 = 1520291) B1520291
theorem B1013547 : Blo 1012602 1013547 := bstep (se 1 (by rfl) ⟨760160, by rfl⟩ : syracuseStep 1013547 = 1520321) B1520321
theorem B1013559 : Blo 1012602 1013559 := bstep (se 1 (by rfl) ⟨760169, by rfl⟩ : syracuseStep 1013559 = 1520339) B1520339
theorem B1013579 : Blo 1012602 1013579 := bstep (se 1 (by rfl) ⟨760184, by rfl⟩ : syracuseStep 1013579 = 1520369) B1520369
theorem B1013591 : Blo 1012602 1013591 := bstep (se 1 (by rfl) ⟨760193, by rfl⟩ : syracuseStep 1013591 = 1520387) B1520387
theorem B5142365 : Blo 1012602 5142365 := bstep (se 3 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 5142365 = 1928387) B1928387
theorem B1013611 : Blo 1012602 1013611 := bstep (se 1 (by rfl) ⟨760208, by rfl⟩ : syracuseStep 1013611 = 1520417) B1520417
theorem B1013623 : Blo 1012602 1013623 := bstep (se 1 (by rfl) ⟨760217, by rfl⟩ : syracuseStep 1013623 = 1520435) B1520435
theorem B1013643 : Blo 1012602 1013643 := bstep (se 1 (by rfl) ⟨760232, by rfl⟩ : syracuseStep 1013643 = 1520465) B1520465
theorem B1013655 : Blo 1012602 1013655 := bstep (se 1 (by rfl) ⟨760241, by rfl⟩ : syracuseStep 1013655 = 1520483) B1520483
theorem B1013675 : Blo 1012602 1013675 := bstep (se 1 (by rfl) ⟨760256, by rfl⟩ : syracuseStep 1013675 = 1520513) B1520513
theorem B1013687 : Blo 1012602 1013687 := bstep (se 1 (by rfl) ⟨760265, by rfl⟩ : syracuseStep 1013687 = 1520531) B1520531
theorem B1013707 : Blo 1012602 1013707 := bstep (se 1 (by rfl) ⟨760280, by rfl⟩ : syracuseStep 1013707 = 1520561) B1520561
theorem B1013719 : Blo 1012602 1013719 := bstep (se 1 (by rfl) ⟨760289, by rfl⟩ : syracuseStep 1013719 = 1520579) B1520579
theorem B1013739 : Blo 1012602 1013739 := bstep (se 1 (by rfl) ⟨760304, by rfl⟩ : syracuseStep 1013739 = 1520609) B1520609
theorem B1013751 : Blo 1012602 1013751 := bstep (se 1 (by rfl) ⟨760313, by rfl⟩ : syracuseStep 1013751 = 1520627) B1520627
theorem B1013771 : Blo 1012602 1013771 := bstep (se 1 (by rfl) ⟨760328, by rfl⟩ : syracuseStep 1013771 = 1520657) B1520657
theorem B1013783 : Blo 1012602 1013783 := bstep (se 1 (by rfl) ⟨760337, by rfl⟩ : syracuseStep 1013783 = 1520675) B1520675
theorem B1013803 : Blo 1012602 1013803 := bstep (se 1 (by rfl) ⟨760352, by rfl⟩ : syracuseStep 1013803 = 1520705) B1520705
theorem B1013815 : Blo 1012602 1013815 := bstep (se 1 (by rfl) ⟨760361, by rfl⟩ : syracuseStep 1013815 = 1520723) B1520723
theorem B48068683 : Blo 1012602 48068683 := bstep (se 1 (by rfl) ⟨36051512, by rfl⟩ : syracuseStep 48068683 = 72103025) B72103025
theorem B1013835 : Blo 1012602 1013835 := bstep (se 1 (by rfl) ⟨760376, by rfl⟩ : syracuseStep 1013835 = 1520753) B1520753
theorem B1013847 : Blo 1012602 1013847 := bstep (se 1 (by rfl) ⟨760385, by rfl⟩ : syracuseStep 1013847 = 1520771) B1520771
theorem B1013867 : Blo 1012602 1013867 := bstep (se 1 (by rfl) ⟨760400, by rfl⟩ : syracuseStep 1013867 = 1520801) B1520801
theorem B1013879 : Blo 1012602 1013879 := bstep (se 1 (by rfl) ⟨760409, by rfl⟩ : syracuseStep 1013879 = 1520819) B1520819
theorem B13006979 : Blo 1012602 13006979 := bstep (se 1 (by rfl) ⟨9755234, by rfl⟩ : syracuseStep 13006979 = 19510469) B19510469
theorem B1013899 : Blo 1012602 1013899 := bstep (se 1 (by rfl) ⟨760424, by rfl⟩ : syracuseStep 1013899 = 1520849) B1520849
theorem B1013911 : Blo 1012602 1013911 := bstep (se 1 (by rfl) ⟨760433, by rfl⟩ : syracuseStep 1013911 = 1520867) B1520867
theorem B1013931 : Blo 1012602 1013931 := bstep (se 1 (by rfl) ⟨760448, by rfl⟩ : syracuseStep 1013931 = 1520897) B1520897
theorem B1013943 : Blo 1012602 1013943 := bstep (se 1 (by rfl) ⟨760457, by rfl⟩ : syracuseStep 1013943 = 1520915) B1520915
theorem B1013963 : Blo 1012602 1013963 := bstep (se 1 (by rfl) ⟨760472, by rfl⟩ : syracuseStep 1013963 = 1520945) B1520945
theorem B1013975 : Blo 1012602 1013975 := bstep (se 1 (by rfl) ⟨760481, by rfl⟩ : syracuseStep 1013975 = 1520963) B1520963
theorem B1013995 : Blo 1012602 1013995 := bstep (se 1 (by rfl) ⟨760496, by rfl⟩ : syracuseStep 1013995 = 1520993) B1520993
theorem B1014007 : Blo 1012602 1014007 := bstep (se 1 (by rfl) ⟨760505, by rfl⟩ : syracuseStep 1014007 = 1521011) B1521011
theorem B1014027 : Blo 1012602 1014027 := bstep (se 1 (by rfl) ⟨760520, by rfl⟩ : syracuseStep 1014027 = 1521041) B1521041
theorem B1014039 : Blo 1012602 1014039 := bstep (se 1 (by rfl) ⟨760529, by rfl⟩ : syracuseStep 1014039 = 1521059) B1521059
theorem B1014059 : Blo 1012602 1014059 := bstep (se 1 (by rfl) ⟨760544, by rfl⟩ : syracuseStep 1014059 = 1521089) B1521089
theorem B1014071 : Blo 1012602 1014071 := bstep (se 1 (by rfl) ⟨760553, by rfl⟩ : syracuseStep 1014071 = 1521107) B1521107
theorem B1014091 : Blo 1012602 1014091 := bstep (se 1 (by rfl) ⟨760568, by rfl⟩ : syracuseStep 1014091 = 1521137) B1521137
theorem B1014103 : Blo 1012602 1014103 := bstep (se 1 (by rfl) ⟨760577, by rfl⟩ : syracuseStep 1014103 = 1521155) B1521155
theorem B1014123 : Blo 1012602 1014123 := bstep (se 1 (by rfl) ⟨760592, by rfl⟩ : syracuseStep 1014123 = 1521185) B1521185
theorem B1014135 : Blo 1012602 1014135 := bstep (se 1 (by rfl) ⟨760601, by rfl⟩ : syracuseStep 1014135 = 1521203) B1521203
theorem B1014155 : Blo 1012602 1014155 := bstep (se 1 (by rfl) ⟨760616, by rfl⟩ : syracuseStep 1014155 = 1521233) B1521233
theorem B1014167 : Blo 1012602 1014167 := bstep (se 1 (by rfl) ⟨760625, by rfl⟩ : syracuseStep 1014167 = 1521251) B1521251
theorem B1014187 : Blo 1012602 1014187 := bstep (se 1 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 1014187 = 1521281) B1521281
theorem B1014199 : Blo 1012602 1014199 := bstep (se 1 (by rfl) ⟨760649, by rfl⟩ : syracuseStep 1014199 = 1521299) B1521299
theorem B1014219 : Blo 1012602 1014219 := bstep (se 1 (by rfl) ⟨760664, by rfl⟩ : syracuseStep 1014219 = 1521329) B1521329
theorem B1014231 : Blo 1012602 1014231 := bstep (se 1 (by rfl) ⟨760673, by rfl⟩ : syracuseStep 1014231 = 1521347) B1521347
theorem B1014251 : Blo 1012602 1014251 := bstep (se 1 (by rfl) ⟨760688, by rfl⟩ : syracuseStep 1014251 = 1521377) B1521377
theorem B1014263 : Blo 1012602 1014263 := bstep (se 1 (by rfl) ⟨760697, by rfl⟩ : syracuseStep 1014263 = 1521395) B1521395
theorem B1014283 : Blo 1012602 1014283 := bstep (se 1 (by rfl) ⟨760712, by rfl⟩ : syracuseStep 1014283 = 1521425) B1521425
theorem B1014295 : Blo 1012602 1014295 := bstep (se 1 (by rfl) ⟨760721, by rfl⟩ : syracuseStep 1014295 = 1521443) B1521443
theorem B1014315 : Blo 1012602 1014315 := bstep (se 1 (by rfl) ⟨760736, by rfl⟩ : syracuseStep 1014315 = 1521473) B1521473
theorem B1014327 : Blo 1012602 1014327 := bstep (se 1 (by rfl) ⟨760745, by rfl⟩ : syracuseStep 1014327 = 1521491) B1521491
theorem B1014347 : Blo 1012602 1014347 := bstep (se 1 (by rfl) ⟨760760, by rfl⟩ : syracuseStep 1014347 = 1521521) B1521521
theorem B1014359 : Blo 1012602 1014359 := bstep (se 1 (by rfl) ⟨760769, by rfl⟩ : syracuseStep 1014359 = 1521539) B1521539
theorem B1014379 : Blo 1012602 1014379 := bstep (se 1 (by rfl) ⟨760784, by rfl⟩ : syracuseStep 1014379 = 1521569) B1521569
theorem B1014391 : Blo 1012602 1014391 := bstep (se 1 (by rfl) ⟨760793, by rfl⟩ : syracuseStep 1014391 = 1521587) B1521587
theorem B1014411 : Blo 1012602 1014411 := bstep (se 1 (by rfl) ⟨760808, by rfl⟩ : syracuseStep 1014411 = 1521617) B1521617
theorem B4684439 : Blo 1012602 4684439 := bstep (se 1 (by rfl) ⟨3513329, by rfl⟩ : syracuseStep 4684439 = 7026659) B7026659
theorem B1014423 : Blo 1012602 1014423 := bstep (se 1 (by rfl) ⟨760817, by rfl⟩ : syracuseStep 1014423 = 1521635) B1521635
theorem B1014443 : Blo 1012602 1014443 := bstep (se 1 (by rfl) ⟨760832, by rfl⟩ : syracuseStep 1014443 = 1521665) B1521665
theorem B1014455 : Blo 1012602 1014455 := bstep (se 1 (by rfl) ⟨760841, by rfl⟩ : syracuseStep 1014455 = 1521683) B1521683
theorem B1014475 : Blo 1012602 1014475 := bstep (se 1 (by rfl) ⟨760856, by rfl⟩ : syracuseStep 1014475 = 1521713) B1521713
theorem B1014487 : Blo 1012602 1014487 := bstep (se 1 (by rfl) ⟨760865, by rfl⟩ : syracuseStep 1014487 = 1521731) B1521731
theorem B1014507 : Blo 1012602 1014507 := bstep (se 1 (by rfl) ⟨760880, by rfl⟩ : syracuseStep 1014507 = 1521761) B1521761
theorem B1014519 : Blo 1012602 1014519 := bstep (se 1 (by rfl) ⟨760889, by rfl⟩ : syracuseStep 1014519 = 1521779) B1521779
theorem B1014539 : Blo 1012602 1014539 := bstep (se 1 (by rfl) ⟨760904, by rfl⟩ : syracuseStep 1014539 = 1521809) B1521809
theorem B1014551 : Blo 1012602 1014551 := bstep (se 1 (by rfl) ⟨760913, by rfl⟩ : syracuseStep 1014551 = 1521827) B1521827
theorem B1014571 : Blo 1012602 1014571 := bstep (se 1 (by rfl) ⟨760928, by rfl⟩ : syracuseStep 1014571 = 1521857) B1521857
theorem B1014583 : Blo 1012602 1014583 := bstep (se 1 (by rfl) ⟨760937, by rfl⟩ : syracuseStep 1014583 = 1521875) B1521875
theorem B1014603 : Blo 1012602 1014603 := bstep (se 1 (by rfl) ⟨760952, by rfl⟩ : syracuseStep 1014603 = 1521905) B1521905
theorem B1014615 : Blo 1012602 1014615 := bstep (se 1 (by rfl) ⟨760961, by rfl⟩ : syracuseStep 1014615 = 1521923) B1521923
theorem B1014635 : Blo 1012602 1014635 := bstep (se 1 (by rfl) ⟨760976, by rfl⟩ : syracuseStep 1014635 = 1521953) B1521953
theorem B1014647 : Blo 1012602 1014647 := bstep (se 1 (by rfl) ⟨760985, by rfl⟩ : syracuseStep 1014647 = 1521971) B1521971
theorem B1014667 : Blo 1012602 1014667 := bstep (se 1 (by rfl) ⟨761000, by rfl⟩ : syracuseStep 1014667 = 1522001) B1522001
theorem B1014679 : Blo 1012602 1014679 := bstep (se 1 (by rfl) ⟨761009, by rfl⟩ : syracuseStep 1014679 = 1522019) B1522019
theorem B1014699 : Blo 1012602 1014699 := bstep (se 1 (by rfl) ⟨761024, by rfl⟩ : syracuseStep 1014699 = 1522049) B1522049
theorem B1014711 : Blo 1012602 1014711 := bstep (se 1 (by rfl) ⟨761033, by rfl⟩ : syracuseStep 1014711 = 1522067) B1522067
theorem B1014731 : Blo 1012602 1014731 := bstep (se 1 (by rfl) ⟨761048, by rfl⟩ : syracuseStep 1014731 = 1522097) B1522097
theorem B1014743 : Blo 1012602 1014743 := bstep (se 1 (by rfl) ⟨761057, by rfl⟩ : syracuseStep 1014743 = 1522115) B1522115
theorem B1014763 : Blo 1012602 1014763 := bstep (se 1 (by rfl) ⟨761072, by rfl⟩ : syracuseStep 1014763 = 1522145) B1522145
theorem B1014775 : Blo 1012602 1014775 := bstep (se 1 (by rfl) ⟨761081, by rfl⟩ : syracuseStep 1014775 = 1522163) B1522163
theorem B1014795 : Blo 1012602 1014795 := bstep (se 1 (by rfl) ⟨761096, by rfl⟩ : syracuseStep 1014795 = 1522193) B1522193
theorem B1014807 : Blo 1012602 1014807 := bstep (se 1 (by rfl) ⟨761105, by rfl⟩ : syracuseStep 1014807 = 1522211) B1522211
theorem B1014827 : Blo 1012602 1014827 := bstep (se 1 (by rfl) ⟨761120, by rfl⟩ : syracuseStep 1014827 = 1522241) B1522241
theorem B1014839 : Blo 1012602 1014839 := bstep (se 1 (by rfl) ⟨761129, by rfl⟩ : syracuseStep 1014839 = 1522259) B1522259
theorem B19496011 : Blo 1012602 19496011 := bstep (se 1 (by rfl) ⟨14622008, by rfl⟩ : syracuseStep 19496011 = 29244017) B29244017
theorem B1014859 : Blo 1012602 1014859 := bstep (se 1 (by rfl) ⟨761144, by rfl⟩ : syracuseStep 1014859 = 1522289) B1522289
theorem B1014871 : Blo 1012602 1014871 := bstep (se 1 (by rfl) ⟨761153, by rfl⟩ : syracuseStep 1014871 = 1522307) B1522307
theorem B1014891 : Blo 1012602 1014891 := bstep (se 1 (by rfl) ⟨761168, by rfl⟩ : syracuseStep 1014891 = 1522337) B1522337
theorem B1014903 : Blo 1012602 1014903 := bstep (se 1 (by rfl) ⟨761177, by rfl⟩ : syracuseStep 1014903 = 1522355) B1522355
theorem B4881539 : Blo 1012602 4881539 := bstep (se 1 (by rfl) ⟨3661154, by rfl⟩ : syracuseStep 4881539 = 7322309) B7322309
theorem B1014923 : Blo 1012602 1014923 := bstep (se 1 (by rfl) ⟨761192, by rfl⟩ : syracuseStep 1014923 = 1522385) B1522385
theorem B1014935 : Blo 1012602 1014935 := bstep (se 1 (by rfl) ⟨761201, by rfl⟩ : syracuseStep 1014935 = 1522403) B1522403
theorem B1014955 : Blo 1012602 1014955 := bstep (se 1 (by rfl) ⟨761216, by rfl⟩ : syracuseStep 1014955 = 1522433) B1522433
theorem B1014967 : Blo 1012602 1014967 := bstep (se 1 (by rfl) ⟨761225, by rfl⟩ : syracuseStep 1014967 = 1522451) B1522451
theorem B1014987 : Blo 1012602 1014987 := bstep (se 1 (by rfl) ⟨761240, by rfl⟩ : syracuseStep 1014987 = 1522481) B1522481
theorem B1014999 : Blo 1012602 1014999 := bstep (se 1 (by rfl) ⟨761249, by rfl⟩ : syracuseStep 1014999 = 1522499) B1522499
theorem B2784473 : Blo 1012602 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B1015019 : Blo 1012602 1015019 := bstep (se 1 (by rfl) ⟨761264, by rfl⟩ : syracuseStep 1015019 = 1522529) B1522529
theorem B1015031 : Blo 1012602 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B1015051 : Blo 1012602 1015051 := bstep (se 1 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 1015051 = 1522577) B1522577
theorem B9239825 : Blo 1012602 9239825 := bstep (se 2 (by rfl) ⟨3464934, by rfl⟩ : syracuseStep 9239825 = 6929869) B6929869
theorem B1015063 : Blo 1012602 1015063 := bstep (se 1 (by rfl) ⟨761297, by rfl⟩ : syracuseStep 1015063 = 1522595) B1522595
theorem B1015083 : Blo 1012602 1015083 := bstep (se 1 (by rfl) ⟨761312, by rfl⟩ : syracuseStep 1015083 = 1522625) B1522625
theorem B4947245 : Blo 1012602 4947245 := bstep (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) B1855217
theorem B1015095 : Blo 1012602 1015095 := bstep (se 1 (by rfl) ⟨761321, by rfl⟩ : syracuseStep 1015095 = 1522643) B1522643
theorem B1015115 : Blo 1012602 1015115 := bstep (se 1 (by rfl) ⟨761336, by rfl⟩ : syracuseStep 1015115 = 1522673) B1522673
theorem B1015127 : Blo 1012602 1015127 := bstep (se 1 (by rfl) ⟨761345, by rfl⟩ : syracuseStep 1015127 = 1522691) B1522691
theorem B1015147 : Blo 1012602 1015147 := bstep (se 1 (by rfl) ⟨761360, by rfl⟩ : syracuseStep 1015147 = 1522721) B1522721
theorem B1015159 : Blo 1012602 1015159 := bstep (se 1 (by rfl) ⟨761369, by rfl⟩ : syracuseStep 1015159 = 1522739) B1522739
theorem B1015179 : Blo 1012602 1015179 := bstep (se 1 (by rfl) ⟨761384, by rfl⟩ : syracuseStep 1015179 = 1522769) B1522769
theorem B1015191 : Blo 1012602 1015191 := bstep (se 1 (by rfl) ⟨761393, by rfl⟩ : syracuseStep 1015191 = 1522787) B1522787
theorem B1015211 : Blo 1012602 1015211 := bstep (se 1 (by rfl) ⟨761408, by rfl⟩ : syracuseStep 1015211 = 1522817) B1522817
theorem B1015223 : Blo 1012602 1015223 := bstep (se 1 (by rfl) ⟨761417, by rfl⟩ : syracuseStep 1015223 = 1522835) B1522835
theorem B1015243 : Blo 1012602 1015243 := bstep (se 1 (by rfl) ⟨761432, by rfl⟩ : syracuseStep 1015243 = 1522865) B1522865
theorem B1015255 : Blo 1012602 1015255 := bstep (se 1 (by rfl) ⟨761441, by rfl⟩ : syracuseStep 1015255 = 1522883) B1522883
theorem B1015275 : Blo 1012602 1015275 := bstep (se 1 (by rfl) ⟨761456, by rfl⟩ : syracuseStep 1015275 = 1522913) B1522913
theorem B1015287 : Blo 1012602 1015287 := bstep (se 1 (by rfl) ⟨761465, by rfl⟩ : syracuseStep 1015287 = 1522931) B1522931
theorem B1015307 : Blo 1012602 1015307 := bstep (se 1 (by rfl) ⟨761480, by rfl⟩ : syracuseStep 1015307 = 1522961) B1522961
theorem B1015319 : Blo 1012602 1015319 := bstep (se 1 (by rfl) ⟨761489, by rfl⟩ : syracuseStep 1015319 = 1522979) B1522979
theorem B9764387 : Blo 1012602 9764387 := bstep (se 1 (by rfl) ⟨7323290, by rfl⟩ : syracuseStep 9764387 = 14646581) B14646581
theorem B1015339 : Blo 1012602 1015339 := bstep (se 1 (by rfl) ⟨761504, by rfl⟩ : syracuseStep 1015339 = 1523009) B1523009
theorem B1015351 : Blo 1012602 1015351 := bstep (se 1 (by rfl) ⟨761513, by rfl⟩ : syracuseStep 1015351 = 1523027) B1523027
theorem B1015371 : Blo 1012602 1015371 := bstep (se 1 (by rfl) ⟨761528, by rfl⟩ : syracuseStep 1015371 = 1523057) B1523057
theorem B1015383 : Blo 1012602 1015383 := bstep (se 1 (by rfl) ⟨761537, by rfl⟩ : syracuseStep 1015383 = 1523075) B1523075
theorem B1015403 : Blo 1012602 1015403 := bstep (se 1 (by rfl) ⟨761552, by rfl⟩ : syracuseStep 1015403 = 1523105) B1523105
theorem B1015415 : Blo 1012602 1015415 := bstep (se 1 (by rfl) ⟨761561, by rfl⟩ : syracuseStep 1015415 = 1523123) B1523123
theorem B1015435 : Blo 1012602 1015435 := bstep (se 1 (by rfl) ⟨761576, by rfl⟩ : syracuseStep 1015435 = 1523153) B1523153
theorem B1015447 : Blo 1012602 1015447 := bstep (se 1 (by rfl) ⟨761585, by rfl⟩ : syracuseStep 1015447 = 1523171) B1523171
theorem B1015467 : Blo 1012602 1015467 := bstep (se 1 (by rfl) ⟨761600, by rfl⟩ : syracuseStep 1015467 = 1523201) B1523201
theorem B1015479 : Blo 1012602 1015479 := bstep (se 1 (by rfl) ⟨761609, by rfl⟩ : syracuseStep 1015479 = 1523219) B1523219
theorem B1015499 : Blo 1012602 1015499 := bstep (se 1 (by rfl) ⟨761624, by rfl⟩ : syracuseStep 1015499 = 1523249) B1523249
theorem B1015511 : Blo 1012602 1015511 := bstep (se 1 (by rfl) ⟨761633, by rfl⟩ : syracuseStep 1015511 = 1523267) B1523267
theorem B1015531 : Blo 1012602 1015531 := bstep (se 1 (by rfl) ⟨761648, by rfl⟩ : syracuseStep 1015531 = 1523297) B1523297
theorem B1015543 : Blo 1012602 1015543 := bstep (se 1 (by rfl) ⟨761657, by rfl⟩ : syracuseStep 1015543 = 1523315) B1523315
theorem B1015563 : Blo 1012602 1015563 := bstep (se 1 (by rfl) ⟨761672, by rfl⟩ : syracuseStep 1015563 = 1523345) B1523345
theorem B1736471 : Blo 1012602 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B1015575 : Blo 1012602 1015575 := bstep (se 1 (by rfl) ⟨761681, by rfl⟩ : syracuseStep 1015575 = 1523363) B1523363
theorem B1015595 : Blo 1012602 1015595 := bstep (se 1 (by rfl) ⟨761696, by rfl⟩ : syracuseStep 1015595 = 1523393) B1523393
theorem B1015607 : Blo 1012602 1015607 := bstep (se 1 (by rfl) ⟨761705, by rfl⟩ : syracuseStep 1015607 = 1523411) B1523411
theorem B1015627 : Blo 1012602 1015627 := bstep (se 1 (by rfl) ⟨761720, by rfl⟩ : syracuseStep 1015627 = 1523441) B1523441
theorem B1015639 : Blo 1012602 1015639 := bstep (se 1 (by rfl) ⟨761729, by rfl⟩ : syracuseStep 1015639 = 1523459) B1523459
theorem B1015659 : Blo 1012602 1015659 := bstep (se 1 (by rfl) ⟨761744, by rfl⟩ : syracuseStep 1015659 = 1523489) B1523489
theorem B1015671 : Blo 1012602 1015671 := bstep (se 1 (by rfl) ⟨761753, by rfl⟩ : syracuseStep 1015671 = 1523507) B1523507
theorem B1015691 : Blo 1012602 1015691 := bstep (se 1 (by rfl) ⟨761768, by rfl⟩ : syracuseStep 1015691 = 1523537) B1523537
theorem B1015703 : Blo 1012602 1015703 := bstep (se 1 (by rfl) ⟨761777, by rfl⟩ : syracuseStep 1015703 = 1523555) B1523555
theorem B5144471 : Blo 1012602 5144471 := bstep (se 1 (by rfl) ⟨3858353, by rfl⟩ : syracuseStep 5144471 = 7716707) B7716707
theorem B1015723 : Blo 1012602 1015723 := bstep (se 1 (by rfl) ⟨761792, by rfl⟩ : syracuseStep 1015723 = 1523585) B1523585
theorem B1015735 : Blo 1012602 1015735 := bstep (se 1 (by rfl) ⟨761801, by rfl⟩ : syracuseStep 1015735 = 1523603) B1523603
theorem B1015755 : Blo 1012602 1015755 := bstep (se 1 (by rfl) ⟨761816, by rfl⟩ : syracuseStep 1015755 = 1523633) B1523633
theorem B1015767 : Blo 1012602 1015767 := bstep (se 1 (by rfl) ⟨761825, by rfl⟩ : syracuseStep 1015767 = 1523651) B1523651
theorem B1015787 : Blo 1012602 1015787 := bstep (se 1 (by rfl) ⟨761840, by rfl⟩ : syracuseStep 1015787 = 1523681) B1523681
theorem B1015799 : Blo 1012602 1015799 := bstep (se 1 (by rfl) ⟨761849, by rfl⟩ : syracuseStep 1015799 = 1523699) B1523699
theorem B1015815 : Blo 1012602 1015815 := bstep (se 1 (by rfl) ⟨761861, by rfl⟩ : syracuseStep 1015815 = 1523723) B1523723
theorem B1015823 : Blo 1012602 1015823 := bstep (se 1 (by rfl) ⟨761867, by rfl⟩ : syracuseStep 1015823 = 1523735) B1523735
theorem B1015867 : Blo 1012602 1015867 := bstep (se 1 (by rfl) ⟨761900, by rfl⟩ : syracuseStep 1015867 = 1523801) B1523801
theorem B1015943 : Blo 1012602 1015943 := bstep (se 1 (by rfl) ⟨761957, by rfl⟩ : syracuseStep 1015943 = 1523915) B1523915
theorem B1015951 : Blo 1012602 1015951 := bstep (se 1 (by rfl) ⟨761963, by rfl⟩ : syracuseStep 1015951 = 1523927) B1523927
theorem B1015995 : Blo 1012602 1015995 := bstep (se 1 (by rfl) ⟨761996, by rfl⟩ : syracuseStep 1015995 = 1523993) B1523993
theorem B8683757 : Blo 1012602 8683757 := bstep (se 3 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 8683757 = 3256409) B3256409
theorem B1016071 : Blo 1012602 1016071 := bstep (se 1 (by rfl) ⟨762053, by rfl⟩ : syracuseStep 1016071 = 1524107) B1524107
theorem B1016079 : Blo 1012602 1016079 := bstep (se 1 (by rfl) ⟨762059, by rfl⟩ : syracuseStep 1016079 = 1524119) B1524119
theorem B5767483 : Blo 1012602 5767483 := bstep (se 1 (by rfl) ⟨4325612, by rfl⟩ : syracuseStep 5767483 = 8651225) B8651225
theorem B1016123 : Blo 1012602 1016123 := bstep (se 1 (by rfl) ⟨762092, by rfl⟩ : syracuseStep 1016123 = 1524185) B1524185
theorem B1016199 : Blo 1012602 1016199 := bstep (se 1 (by rfl) ⟨762149, by rfl⟩ : syracuseStep 1016199 = 1524299) B1524299
theorem B1016207 : Blo 1012602 1016207 := bstep (se 1 (by rfl) ⟨762155, by rfl⟩ : syracuseStep 1016207 = 1524311) B1524311
theorem B23462291 : Blo 1012602 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B1016251 : Blo 1012602 1016251 := bstep (se 1 (by rfl) ⟨762188, by rfl⟩ : syracuseStep 1016251 = 1524377) B1524377
theorem B1016327 : Blo 1012602 1016327 := bstep (se 1 (by rfl) ⟨762245, by rfl⟩ : syracuseStep 1016327 = 1524491) B1524491
theorem B1016335 : Blo 1012602 1016335 := bstep (se 1 (by rfl) ⟨762251, by rfl⟩ : syracuseStep 1016335 = 1524503) B1524503
theorem B1016379 : Blo 1012602 1016379 := bstep (se 1 (by rfl) ⟨762284, by rfl⟩ : syracuseStep 1016379 = 1524569) B1524569
theorem B4326007 : Blo 1012602 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B1016455 : Blo 1012602 1016455 := bstep (se 1 (by rfl) ⟨762341, by rfl⟩ : syracuseStep 1016455 = 1524683) B1524683
theorem B1016463 : Blo 1012602 1016463 := bstep (se 1 (by rfl) ⟨762347, by rfl⟩ : syracuseStep 1016463 = 1524695) B1524695
theorem B2884243 : Blo 1012602 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B1016507 : Blo 1012602 1016507 := bstep (se 1 (by rfl) ⟨762380, by rfl⟩ : syracuseStep 1016507 = 1524761) B1524761
theorem B5145281 : Blo 1012602 5145281 := bstep (se 2 (by rfl) ⟨1929480, by rfl⟩ : syracuseStep 5145281 = 3858961) B3858961
theorem B7045861 : Blo 1012602 7045861 := bstep (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) B1321099
theorem B1016583 : Blo 1012602 1016583 := bstep (se 1 (by rfl) ⟨762437, by rfl⟩ : syracuseStep 1016583 = 1524875) B1524875
theorem B1016591 : Blo 1012602 1016591 := bstep (se 1 (by rfl) ⟨762443, by rfl⟩ : syracuseStep 1016591 = 1524887) B1524887
theorem B33424163 : Blo 1012602 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B8684441 : Blo 1012602 8684441 := bstep (se 2 (by rfl) ⟨3256665, by rfl⟩ : syracuseStep 8684441 = 6513331) B6513331
theorem B6489035 : Blo 1012602 6489035 := bstep (se 1 (by rfl) ⟨4866776, by rfl⟩ : syracuseStep 6489035 = 9733553) B9733553
theorem B1443215 : Blo 1012602 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B5768941 : Blo 1012602 5768941 := bstep (se 3 (by rfl) ⟨1081676, by rfl⟩ : syracuseStep 5768941 = 2163353) B2163353
theorem B18778007 : Blo 1012602 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B2197547 : Blo 1012602 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B1083655 : Blo 1012602 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B1411387 : Blo 1012602 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B2885975 : Blo 1012602 2885975 := bstep (se 1 (by rfl) ⟨2164481, by rfl⟩ : syracuseStep 2885975 = 4328963) B4328963
theorem B11537153 : Blo 1012602 11537153 := bstep (se 2 (by rfl) ⟨4326432, by rfl⟩ : syracuseStep 11537153 = 8652865) B8652865
theorem B5212943 : Blo 1012602 5212943 := bstep (se 1 (by rfl) ⟨3909707, by rfl⟩ : syracuseStep 5212943 = 7819415) B7819415
theorem B1084475 : Blo 1012602 1084475 := bstep (se 1 (by rfl) ⟨813356, by rfl⟩ : syracuseStep 1084475 = 1626713) B1626713
theorem B26020925 : Blo 1012602 26020925 := bstep (se 3 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 26020925 = 9757847) B9757847
theorem B13896791 : Blo 1012602 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B6163847 : Blo 1012602 6163847 := bstep (se 1 (by rfl) ⟨4622885, by rfl⟩ : syracuseStep 6163847 = 9245771) B9245771
theorem B4623763 : Blo 1012602 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B7310891 : Blo 1012602 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B5770925 : Blo 1012602 5770925 := bstep (se 3 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 5770925 = 2164097) B2164097
theorem B1281835 : Blo 1012602 1281835 := bstep (se 1 (by rfl) ⟨961376, by rfl⟩ : syracuseStep 1281835 = 1922753) B1922753
theorem B2887559 : Blo 1012602 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B1282063 : Blo 1012602 1282063 := bstep (se 1 (by rfl) ⟨961547, by rfl⟩ : syracuseStep 1282063 = 1923095) B1923095
theorem B1446331 : Blo 1012602 1446331 := bstep (se 1 (by rfl) ⟨1084748, by rfl⟩ : syracuseStep 1446331 = 2169497) B2169497
theorem B2888207 : Blo 1012602 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B1282807 : Blo 1012602 1282807 := bstep (se 1 (by rfl) ⟨962105, by rfl⟩ : syracuseStep 1282807 = 1924211) B1924211
theorem B1708843 : Blo 1012602 1708843 := bstep (se 1 (by rfl) ⟨1281632, by rfl⟩ : syracuseStep 1708843 = 2563265) B2563265
theorem B1708985 : Blo 1012602 1708985 := bstep (se 2 (by rfl) ⟨640869, by rfl⟩ : syracuseStep 1708985 = 1281739) B1281739
theorem B4166585 : Blo 1012602 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B1283131 : Blo 1012602 1283131 := bstep (se 1 (by rfl) ⟨962348, by rfl⟩ : syracuseStep 1283131 = 1924697) B1924697
theorem B3085427 : Blo 1012602 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1447031 : Blo 1012602 1447031 := bstep (se 1 (by rfl) ⟨1085273, by rfl⟩ : syracuseStep 1447031 = 2170547) B2170547
theorem B5018969 : Blo 1012602 5018969 := bstep (se 2 (by rfl) ⟨1882113, by rfl⟩ : syracuseStep 5018969 = 3764227) B3764227
theorem B1217963 : Blo 1012602 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B1283627 : Blo 1012602 1283627 := bstep (se 1 (by rfl) ⟨962720, by rfl⟩ : syracuseStep 1283627 = 1925441) B1925441
theorem B11540069 : Blo 1012602 11540069 := bstep (se 4 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 11540069 = 2163763) B2163763
theorem B1709687 : Blo 1012602 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B5773315 : Blo 1012602 5773315 := bstep (se 1 (by rfl) ⟨4329986, by rfl⟩ : syracuseStep 5773315 = 8659973) B8659973
theorem B1284103 : Blo 1012602 1284103 := bstep (se 1 (by rfl) ⟨963077, by rfl⟩ : syracuseStep 1284103 = 1926155) B1926155
theorem B1710139 : Blo 1012602 1710139 := bstep (se 1 (by rfl) ⟨1282604, by rfl⟩ : syracuseStep 1710139 = 2565209) B2565209
theorem B2889847 : Blo 1012602 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B1710281 : Blo 1012602 1710281 := bstep (se 2 (by rfl) ⟨641355, by rfl⟩ : syracuseStep 1710281 = 1282711) B1282711
theorem B17307917 : Blo 1012602 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B6166817 : Blo 1012602 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B1284599 : Blo 1012602 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B1284751 : Blo 1012602 1284751 := bstep (se 1 (by rfl) ⟨963563, by rfl⟩ : syracuseStep 1284751 = 1927127) B1927127
theorem B8329999 : Blo 1012602 8329999 := bstep (se 1 (by rfl) ⟨6247499, by rfl⟩ : syracuseStep 8329999 = 12494999) B12494999
theorem B2169659 : Blo 1012602 2169659 := bstep (se 1 (by rfl) ⟨1627244, by rfl⟩ : syracuseStep 2169659 = 3254489) B3254489
theorem B1284923 : Blo 1012602 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B1710983 : Blo 1012602 1710983 := bstep (se 1 (by rfl) ⟨1283237, by rfl⟩ : syracuseStep 1710983 = 2566475) B2566475
theorem B11541527 : Blo 1012602 11541527 := bstep (se 1 (by rfl) ⟨8656145, by rfl⟩ : syracuseStep 11541527 = 17312291) B17312291
theorem B12491837 : Blo 1012602 12491837 := bstep (se 3 (by rfl) ⟨2342219, by rfl⟩ : syracuseStep 12491837 = 4684439) B4684439
theorem B3251515 : Blo 1012602 3251515 := bstep (se 1 (by rfl) ⟨2438636, by rfl⟩ : syracuseStep 3251515 = 4877273) B4877273
theorem B2891123 : Blo 1012602 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B2563447 : Blo 1012602 2563447 := bstep (se 1 (by rfl) ⟨1922585, by rfl⟩ : syracuseStep 2563447 = 3845171) B3845171
theorem B3251591 : Blo 1012602 3251591 := bstep (se 1 (by rfl) ⟨2438693, by rfl⟩ : syracuseStep 3251591 = 4877387) B4877387
theorem B1711631 : Blo 1012602 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B2924093 : Blo 1012602 2924093 := bstep (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) B1096535
theorem B2891351 : Blo 1012602 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B11705975 : Blo 1012602 11705975 := bstep (se 1 (by rfl) ⟨8779481, by rfl⟩ : syracuseStep 11705975 = 17558963) B17558963
theorem B1220231 : Blo 1012602 1220231 := bstep (se 1 (by rfl) ⟨915173, by rfl⟩ : syracuseStep 1220231 = 1830347) B1830347
theorem B1285895 : Blo 1012602 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B3252001 : Blo 1012602 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B2563883 : Blo 1012602 2563883 := bstep (se 1 (by rfl) ⟨1922912, by rfl⟩ : syracuseStep 2563883 = 3845825) B3845825
theorem B32907059 : Blo 1012602 32907059 := bstep (se 1 (by rfl) ⟨24680294, by rfl⟩ : syracuseStep 32907059 = 49360589) B49360589
theorem B1712171 : Blo 1012602 1712171 := bstep (se 1 (by rfl) ⟨1284128, by rfl⟩ : syracuseStep 1712171 = 2568257) B2568257
theorem B1220779 : Blo 1012602 1220779 := bstep (se 1 (by rfl) ⟨915584, by rfl⟩ : syracuseStep 1220779 = 1831169) B1831169
theorem B1220923 : Blo 1012602 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B5775731 : Blo 1012602 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B1286543 : Blo 1012602 1286543 := bstep (se 1 (by rfl) ⟨964907, by rfl⟩ : syracuseStep 1286543 = 1929815) B1929815
theorem B4170131 : Blo 1012602 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B1712569 : Blo 1012602 1712569 := bstep (se 2 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 1712569 = 1284427) B1284427
theorem B5153291 : Blo 1012602 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B3121679 : Blo 1012602 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B3088955 : Blo 1012602 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B2564723 : Blo 1012602 2564723 := bstep (se 1 (by rfl) ⟨1923542, by rfl⟩ : syracuseStep 2564723 = 3847085) B3847085
theorem B2564743 : Blo 1012602 2564743 := bstep (se 1 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 2564743 = 3847115) B3847115
theorem B2433851 : Blo 1012602 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B4629307 : Blo 1012602 4629307 := bstep (se 1 (by rfl) ⟨3471980, by rfl⟩ : syracuseStep 4629307 = 6943961) B6943961
theorem B2565017 : Blo 1012602 2565017 := bstep (se 2 (by rfl) ⟨961881, by rfl⟩ : syracuseStep 2565017 = 1923763) B1923763
theorem B2565179 : Blo 1012602 2565179 := bstep (se 1 (by rfl) ⟨1923884, by rfl⟩ : syracuseStep 2565179 = 3847769) B3847769
theorem B1713271 : Blo 1012602 1713271 := bstep (se 1 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 1713271 = 2569907) B2569907
theorem B2892935 : Blo 1012602 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B5481701 : Blo 1012602 5481701 := bstep (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) B1027819
theorem B2565391 : Blo 1012602 2565391 := bstep (se 1 (by rfl) ⟨1924043, by rfl⟩ : syracuseStep 2565391 = 3848087) B3848087
theorem B1713467 : Blo 1012602 1713467 := bstep (se 1 (by rfl) ⟨1285100, by rfl⟩ : syracuseStep 1713467 = 2570201) B2570201
theorem B2893117 : Blo 1012602 2893117 := bstep (se 3 (by rfl) ⟨542459, by rfl⟩ : syracuseStep 2893117 = 1084919) B1084919
theorem B25994681 : Blo 1012602 25994681 := bstep (se 2 (by rfl) ⟨9748005, by rfl⟩ : syracuseStep 25994681 = 19496011) B19496011
theorem B12985859 : Blo 1012602 12985859 := bstep (se 1 (by rfl) ⟨9739394, by rfl⟩ : syracuseStep 12985859 = 19478789) B19478789
theorem B2565665 : Blo 1012602 2565665 := bstep (se 2 (by rfl) ⟨962124, by rfl⟩ : syracuseStep 2565665 = 1924249) B1924249
theorem B2434619 : Blo 1012602 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B37561931 : Blo 1012602 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B1320619 : Blo 1012602 1320619 := bstep (se 1 (by rfl) ⟨990464, by rfl⟩ : syracuseStep 1320619 = 1980929) B1980929
theorem B1713865 : Blo 1012602 1713865 := bstep (se 2 (by rfl) ⟨642699, by rfl⟩ : syracuseStep 1713865 = 1285399) B1285399
theorem B2893583 : Blo 1012602 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B5777189 : Blo 1012602 5777189 := bstep (se 4 (by rfl) ⟨541611, by rfl⟩ : syracuseStep 5777189 = 1083223) B1083223
theorem B3418199 : Blo 1012602 3418199 := bstep (se 1 (by rfl) ⟨2563649, by rfl⟩ : syracuseStep 3418199 = 5127299) B5127299
theorem B3254359 : Blo 1012602 3254359 := bstep (se 1 (by rfl) ⟨2440769, by rfl⟩ : syracuseStep 3254359 = 4881539) B4881539
theorem B10954925 : Blo 1012602 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B11118941 : Blo 1012602 11118941 := bstep (se 3 (by rfl) ⟨2084801, by rfl⟩ : syracuseStep 11118941 = 4169603) B4169603
theorem B1714567 : Blo 1012602 1714567 := bstep (se 1 (by rfl) ⟨1285925, by rfl⟩ : syracuseStep 1714567 = 2571851) B2571851
theorem B2566667 : Blo 1012602 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B1157647 : Blo 1012602 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B5777963 : Blo 1012602 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B3418685 : Blo 1012602 3418685 := bstep (se 3 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 3418685 = 1282007) B1282007
theorem B18491969 : Blo 1012602 18491969 := bstep (se 2 (by rfl) ⟨6934488, by rfl⟩ : syracuseStep 18491969 = 13868977) B13868977
theorem B2436041 : Blo 1012602 2436041 := bstep (se 2 (by rfl) ⟨913515, by rfl⟩ : syracuseStep 2436041 = 1827031) B1827031
theorem B2894849 : Blo 1012602 2894849 := bstep (se 2 (by rfl) ⟨1085568, by rfl⟩ : syracuseStep 2894849 = 2171137) B2171137
theorem B41692171 : Blo 1012602 41692171 := bstep (se 1 (by rfl) ⟨31269128, by rfl⟩ : syracuseStep 41692171 = 62538257) B62538257
theorem B1715215 : Blo 1012602 1715215 := bstep (se 1 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 1715215 = 2572823) B2572823
theorem B2567315 : Blo 1012602 2567315 := bstep (se 1 (by rfl) ⟨1925486, by rfl⟩ : syracuseStep 2567315 = 3850973) B3850973
theorem B11709677 : Blo 1012602 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B1518905 : Blo 1012602 1518905 := bstep (se 2 (by rfl) ⟨569589, by rfl⟩ : syracuseStep 1518905 = 1139179) B1139179
theorem B1518983 : Blo 1012602 1518983 := bstep (se 1 (by rfl) ⟨1139237, by rfl⟩ : syracuseStep 1518983 = 2278475) B2278475
theorem B1519019 : Blo 1012602 1519019 := bstep (se 1 (by rfl) ⟨1139264, by rfl⟩ : syracuseStep 1519019 = 2278529) B2278529
theorem B2567609 : Blo 1012602 2567609 := bstep (se 2 (by rfl) ⟨962853, by rfl⟩ : syracuseStep 2567609 = 1925707) B1925707
theorem B1519049 : Blo 1012602 1519049 := bstep (se 2 (by rfl) ⟨569643, by rfl⟩ : syracuseStep 1519049 = 1139287) B1139287
theorem B10431949 : Blo 1012602 10431949 := bstep (se 3 (by rfl) ⟨1955990, by rfl⟩ : syracuseStep 10431949 = 3911981) B3911981
theorem B1027591 : Blo 1012602 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B8662571 : Blo 1012602 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B1519163 : Blo 1012602 1519163 := bstep (se 1 (by rfl) ⟨1139372, by rfl⟩ : syracuseStep 1519163 = 2278745) B2278745
theorem B2600507 : Blo 1012602 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B7712333 : Blo 1012602 7712333 := bstep (se 3 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 7712333 = 2892125) B2892125
theorem B2436695 : Blo 1012602 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B1519223 : Blo 1012602 1519223 := bstep (se 1 (by rfl) ⟨1139417, by rfl⟩ : syracuseStep 1519223 = 2278835) B2278835
theorem B1519247 : Blo 1012602 1519247 := bstep (se 1 (by rfl) ⟨1139435, by rfl⟩ : syracuseStep 1519247 = 2278871) B2278871
theorem B1519289 : Blo 1012602 1519289 := bstep (se 2 (by rfl) ⟨569733, by rfl⟩ : syracuseStep 1519289 = 1139467) B1139467
theorem B1519367 : Blo 1012602 1519367 := bstep (se 1 (by rfl) ⟨1139525, by rfl⟩ : syracuseStep 1519367 = 2279051) B2279051
theorem B1519403 : Blo 1012602 1519403 := bstep (se 1 (by rfl) ⟨1139552, by rfl⟩ : syracuseStep 1519403 = 2279105) B2279105
theorem B1519433 : Blo 1012602 1519433 := bstep (se 2 (by rfl) ⟨569787, by rfl⟩ : syracuseStep 1519433 = 1139575) B1139575
theorem B3420089 : Blo 1012602 3420089 := bstep (se 2 (by rfl) ⟨1282533, by rfl⟩ : syracuseStep 3420089 = 2565067) B2565067
theorem B1519547 : Blo 1012602 1519547 := bstep (se 1 (by rfl) ⟨1139660, by rfl⟩ : syracuseStep 1519547 = 2279321) B2279321
theorem B5779421 : Blo 1012602 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B1519607 : Blo 1012602 1519607 := bstep (se 1 (by rfl) ⟨1139705, by rfl⟩ : syracuseStep 1519607 = 2279411) B2279411
theorem B1519631 : Blo 1012602 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B1519673 : Blo 1012602 1519673 := bstep (se 2 (by rfl) ⟨569877, by rfl⟩ : syracuseStep 1519673 = 1139755) B1139755
theorem B2568307 : Blo 1012602 2568307 := bstep (se 1 (by rfl) ⟨1926230, by rfl⟩ : syracuseStep 2568307 = 3852461) B3852461
theorem B1519751 : Blo 1012602 1519751 := bstep (se 1 (by rfl) ⟨1139813, by rfl⟩ : syracuseStep 1519751 = 2279627) B2279627
theorem B1519787 : Blo 1012602 1519787 := bstep (se 1 (by rfl) ⟨1139840, by rfl⟩ : syracuseStep 1519787 = 2279681) B2279681
theorem B20852909 : Blo 1012602 20852909 := bstep (se 3 (by rfl) ⟨3909920, by rfl⟩ : syracuseStep 20852909 = 7819841) B7819841
theorem B1519817 : Blo 1012602 1519817 := bstep (se 2 (by rfl) ⟨569931, by rfl⟩ : syracuseStep 1519817 = 1139863) B1139863
theorem B6336713 : Blo 1012602 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B2568449 : Blo 1012602 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B1519931 : Blo 1012602 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B2437463 : Blo 1012602 2437463 := bstep (se 1 (by rfl) ⟨1828097, by rfl⟩ : syracuseStep 2437463 = 3656195) B3656195
theorem B1519991 : Blo 1012602 1519991 := bstep (se 1 (by rfl) ⟨1139993, by rfl⟩ : syracuseStep 1519991 = 2279987) B2279987
theorem B1520015 : Blo 1012602 1520015 := bstep (se 1 (by rfl) ⟨1140011, by rfl⟩ : syracuseStep 1520015 = 2280023) B2280023
theorem B1520057 : Blo 1012602 1520057 := bstep (se 2 (by rfl) ⟨570021, by rfl⟩ : syracuseStep 1520057 = 1140043) B1140043
theorem B1520135 : Blo 1012602 1520135 := bstep (se 1 (by rfl) ⟨1140101, by rfl⟩ : syracuseStep 1520135 = 2280203) B2280203
theorem B3420683 : Blo 1012602 3420683 := bstep (se 1 (by rfl) ⟨2565512, by rfl⟩ : syracuseStep 3420683 = 5131025) B5131025
theorem B1520171 : Blo 1012602 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B1520201 : Blo 1012602 1520201 := bstep (se 2 (by rfl) ⟨570075, by rfl⟩ : syracuseStep 1520201 = 1140151) B1140151
theorem B3420791 : Blo 1012602 3420791 := bstep (se 1 (by rfl) ⟨2565593, by rfl⟩ : syracuseStep 3420791 = 5131187) B5131187
theorem B1028743 : Blo 1012602 1028743 := bstep (se 1 (by rfl) ⟨771557, by rfl⟩ : syracuseStep 1028743 = 1543115) B1543115
theorem B1520315 : Blo 1012602 1520315 := bstep (se 1 (by rfl) ⟨1140236, by rfl⟩ : syracuseStep 1520315 = 2280473) B2280473
theorem B2568905 : Blo 1012602 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B1520375 : Blo 1012602 1520375 := bstep (se 1 (by rfl) ⟨1140281, by rfl⟩ : syracuseStep 1520375 = 2280563) B2280563
theorem B1520399 : Blo 1012602 1520399 := bstep (se 1 (by rfl) ⟨1140299, by rfl⟩ : syracuseStep 1520399 = 2280599) B2280599
theorem B8237861 : Blo 1012602 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B1520441 : Blo 1012602 1520441 := bstep (se 2 (by rfl) ⟨570165, by rfl⟩ : syracuseStep 1520441 = 1140331) B1140331
theorem B1520519 : Blo 1012602 1520519 := bstep (se 1 (by rfl) ⟨1140389, by rfl⟩ : syracuseStep 1520519 = 2280779) B2280779
theorem B1520555 : Blo 1012602 1520555 := bstep (se 1 (by rfl) ⟨1140416, by rfl⟩ : syracuseStep 1520555 = 2280833) B2280833
theorem B1520585 : Blo 1012602 1520585 := bstep (se 2 (by rfl) ⟨570219, by rfl⟩ : syracuseStep 1520585 = 1140439) B1140439
theorem B2569259 : Blo 1012602 2569259 := bstep (se 1 (by rfl) ⟨1926944, by rfl⟩ : syracuseStep 2569259 = 3853889) B3853889
theorem B1520699 : Blo 1012602 1520699 := bstep (se 1 (by rfl) ⟨1140524, by rfl⟩ : syracuseStep 1520699 = 2281049) B2281049
theorem B13874237 : Blo 1012602 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B1520759 : Blo 1012602 1520759 := bstep (se 1 (by rfl) ⟨1140569, by rfl⟩ : syracuseStep 1520759 = 2281139) B2281139
theorem B1520783 : Blo 1012602 1520783 := bstep (se 1 (by rfl) ⟨1140587, by rfl⟩ : syracuseStep 1520783 = 2281175) B2281175
theorem B1520825 : Blo 1012602 1520825 := bstep (se 2 (by rfl) ⟨570309, by rfl⟩ : syracuseStep 1520825 = 1140619) B1140619
theorem B3421385 : Blo 1012602 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B1520903 : Blo 1012602 1520903 := bstep (se 1 (by rfl) ⟨1140677, by rfl⟩ : syracuseStep 1520903 = 2281355) B2281355
theorem B1520939 : Blo 1012602 1520939 := bstep (se 1 (by rfl) ⟨1140704, by rfl⟩ : syracuseStep 1520939 = 2281409) B2281409
theorem B1520969 : Blo 1012602 1520969 := bstep (se 2 (by rfl) ⟨570363, by rfl⟩ : syracuseStep 1520969 = 1140727) B1140727
theorem B3847571 : Blo 1012602 3847571 := bstep (se 1 (by rfl) ⟨2885678, by rfl⟩ : syracuseStep 3847571 = 5771357) B5771357
theorem B4339129 : Blo 1012602 4339129 := bstep (se 2 (by rfl) ⟨1627173, by rfl⟩ : syracuseStep 4339129 = 3254347) B3254347
theorem B1521083 : Blo 1012602 1521083 := bstep (se 1 (by rfl) ⟨1140812, by rfl⟩ : syracuseStep 1521083 = 2281625) B2281625
theorem B1521143 : Blo 1012602 1521143 := bstep (se 1 (by rfl) ⟨1140857, by rfl⟩ : syracuseStep 1521143 = 2281715) B2281715
theorem B1521167 : Blo 1012602 1521167 := bstep (se 1 (by rfl) ⟨1140875, by rfl⟩ : syracuseStep 1521167 = 2281751) B2281751
theorem B8238635 : Blo 1012602 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B1521209 : Blo 1012602 1521209 := bstep (se 2 (by rfl) ⟨570453, by rfl⟩ : syracuseStep 1521209 = 1140907) B1140907
theorem B1521287 : Blo 1012602 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B1521323 : Blo 1012602 1521323 := bstep (se 1 (by rfl) ⟨1140992, by rfl⟩ : syracuseStep 1521323 = 2281985) B2281985
theorem B1521353 : Blo 1012602 1521353 := bstep (se 2 (by rfl) ⟨570507, by rfl⟩ : syracuseStep 1521353 = 1141015) B1141015
theorem B1521467 : Blo 1012602 1521467 := bstep (se 1 (by rfl) ⟨1141100, by rfl⟩ : syracuseStep 1521467 = 2282201) B2282201
theorem B1521527 : Blo 1012602 1521527 := bstep (se 1 (by rfl) ⟨1141145, by rfl⟩ : syracuseStep 1521527 = 2282291) B2282291
theorem B3422087 : Blo 1012602 3422087 := bstep (se 1 (by rfl) ⟨2566565, by rfl⟩ : syracuseStep 3422087 = 5133131) B5133131
theorem B1521551 : Blo 1012602 1521551 := bstep (se 1 (by rfl) ⟨1141163, by rfl⟩ : syracuseStep 1521551 = 2282327) B2282327
theorem B1521593 : Blo 1012602 1521593 := bstep (se 2 (by rfl) ⟨570597, by rfl⟩ : syracuseStep 1521593 = 1141195) B1141195
theorem B7714763 : Blo 1012602 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B1521671 : Blo 1012602 1521671 := bstep (se 1 (by rfl) ⟨1141253, by rfl⟩ : syracuseStep 1521671 = 2282507) B2282507
theorem B2570251 : Blo 1012602 2570251 := bstep (se 1 (by rfl) ⟨1927688, by rfl⟩ : syracuseStep 2570251 = 3855377) B3855377
theorem B1521707 : Blo 1012602 1521707 := bstep (se 1 (by rfl) ⟨1141280, by rfl⟩ : syracuseStep 1521707 = 2282561) B2282561
theorem B1521737 : Blo 1012602 1521737 := bstep (se 2 (by rfl) ⟨570651, by rfl⟩ : syracuseStep 1521737 = 1141303) B1141303
theorem B2570393 : Blo 1012602 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B1521851 : Blo 1012602 1521851 := bstep (se 1 (by rfl) ⟨1141388, by rfl⟩ : syracuseStep 1521851 = 2282777) B2282777
theorem B1521911 : Blo 1012602 1521911 := bstep (se 1 (by rfl) ⟨1141433, by rfl⟩ : syracuseStep 1521911 = 2282867) B2282867
theorem B3422465 : Blo 1012602 3422465 := bstep (se 2 (by rfl) ⟨1283424, by rfl⟩ : syracuseStep 3422465 = 2566849) B2566849
theorem B1521935 : Blo 1012602 1521935 := bstep (se 1 (by rfl) ⟨1141451, by rfl⟩ : syracuseStep 1521935 = 2282903) B2282903
theorem B1521977 : Blo 1012602 1521977 := bstep (se 2 (by rfl) ⟨570741, by rfl⟩ : syracuseStep 1521977 = 1141483) B1141483
theorem B2570555 : Blo 1012602 2570555 := bstep (se 1 (by rfl) ⟨1927916, by rfl⟩ : syracuseStep 2570555 = 3855833) B3855833
theorem B5126489 : Blo 1012602 5126489 := bstep (se 2 (by rfl) ⟨1922433, by rfl⟩ : syracuseStep 5126489 = 3844867) B3844867
theorem B1522055 : Blo 1012602 1522055 := bstep (se 1 (by rfl) ⟨1141541, by rfl⟩ : syracuseStep 1522055 = 2283083) B2283083
theorem B1522091 : Blo 1012602 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B1522121 : Blo 1012602 1522121 := bstep (se 2 (by rfl) ⟨570795, by rfl⟩ : syracuseStep 1522121 = 1141591) B1141591
theorem B2439713 : Blo 1012602 2439713 := bstep (se 2 (by rfl) ⟨914892, by rfl⟩ : syracuseStep 2439713 = 1829785) B1829785
theorem B1522235 : Blo 1012602 1522235 := bstep (se 1 (by rfl) ⟨1141676, by rfl⟩ : syracuseStep 1522235 = 2283353) B2283353
theorem B1522295 : Blo 1012602 1522295 := bstep (se 1 (by rfl) ⟨1141721, by rfl⟩ : syracuseStep 1522295 = 2283443) B2283443
theorem B1522319 : Blo 1012602 1522319 := bstep (se 1 (by rfl) ⟨1141739, by rfl⟩ : syracuseStep 1522319 = 2283479) B2283479
theorem B2570899 : Blo 1012602 2570899 := bstep (se 1 (by rfl) ⟨1928174, by rfl⟩ : syracuseStep 2570899 = 3856349) B3856349
theorem B1522361 : Blo 1012602 1522361 := bstep (se 2 (by rfl) ⟨570885, by rfl⟩ : syracuseStep 1522361 = 1141771) B1141771
theorem B1522439 : Blo 1012602 1522439 := bstep (se 1 (by rfl) ⟨1141829, by rfl⟩ : syracuseStep 1522439 = 2283659) B2283659
theorem B2571041 : Blo 1012602 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B1522475 : Blo 1012602 1522475 := bstep (se 1 (by rfl) ⟨1141856, by rfl⟩ : syracuseStep 1522475 = 2283713) B2283713
theorem B1522505 : Blo 1012602 1522505 := bstep (se 2 (by rfl) ⟨570939, by rfl⟩ : syracuseStep 1522505 = 1141879) B1141879
theorem B1096583 : Blo 1012602 1096583 := bstep (se 1 (by rfl) ⟨822437, by rfl⟩ : syracuseStep 1096583 = 1644875) B1644875
theorem B3652505 : Blo 1012602 3652505 := bstep (se 2 (by rfl) ⟨1369689, by rfl⟩ : syracuseStep 3652505 = 2739379) B2739379
theorem B1522619 : Blo 1012602 1522619 := bstep (se 1 (by rfl) ⟨1141964, by rfl⟩ : syracuseStep 1522619 = 2283929) B2283929
theorem B1522679 : Blo 1012602 1522679 := bstep (se 1 (by rfl) ⟨1142009, by rfl⟩ : syracuseStep 1522679 = 2284019) B2284019
theorem B3849227 : Blo 1012602 3849227 := bstep (se 1 (by rfl) ⟨2886920, by rfl⟩ : syracuseStep 3849227 = 5773841) B5773841
theorem B1522703 : Blo 1012602 1522703 := bstep (se 1 (by rfl) ⟨1142027, by rfl⟩ : syracuseStep 1522703 = 2284055) B2284055
theorem B3423275 : Blo 1012602 3423275 := bstep (se 1 (by rfl) ⟨2567456, by rfl⟩ : syracuseStep 3423275 = 5134913) B5134913
theorem B1522745 : Blo 1012602 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B5782589 : Blo 1012602 5782589 := bstep (se 3 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 5782589 = 2168471) B2168471
theorem B1522823 : Blo 1012602 1522823 := bstep (se 1 (by rfl) ⟨1142117, by rfl⟩ : syracuseStep 1522823 = 2284235) B2284235
theorem B1522859 : Blo 1012602 1522859 := bstep (se 1 (by rfl) ⟨1142144, by rfl⟩ : syracuseStep 1522859 = 2284289) B2284289
theorem B1522889 : Blo 1012602 1522889 := bstep (se 2 (by rfl) ⟨571083, by rfl⟩ : syracuseStep 1522889 = 1142167) B1142167
theorem B1523003 : Blo 1012602 1523003 := bstep (se 1 (by rfl) ⟨1142252, by rfl⟩ : syracuseStep 1523003 = 2284505) B2284505
theorem B1523063 : Blo 1012602 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B4341127 : Blo 1012602 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B1523087 : Blo 1012602 1523087 := bstep (se 1 (by rfl) ⟨1142315, by rfl⟩ : syracuseStep 1523087 = 2284631) B2284631
theorem B1523129 : Blo 1012602 1523129 := bstep (se 2 (by rfl) ⟨571173, by rfl⟩ : syracuseStep 1523129 = 1142347) B1142347
theorem B1523207 : Blo 1012602 1523207 := bstep (se 1 (by rfl) ⟨1142405, by rfl⟩ : syracuseStep 1523207 = 2284811) B2284811
theorem B1523243 : Blo 1012602 1523243 := bstep (se 1 (by rfl) ⟨1142432, by rfl⟩ : syracuseStep 1523243 = 2284865) B2284865
theorem B11550275 : Blo 1012602 11550275 := bstep (se 1 (by rfl) ⟨8662706, by rfl⟩ : syracuseStep 11550275 = 17325413) B17325413
theorem B1523273 : Blo 1012602 1523273 := bstep (se 2 (by rfl) ⟨571227, by rfl⟩ : syracuseStep 1523273 = 1142455) B1142455
theorem B1523387 : Blo 1012602 1523387 := bstep (se 1 (by rfl) ⟨1142540, by rfl⟩ : syracuseStep 1523387 = 2285081) B2285081
theorem B1523447 : Blo 1012602 1523447 := bstep (se 1 (by rfl) ⟨1142585, by rfl⟩ : syracuseStep 1523447 = 2285171) B2285171
theorem B2572033 : Blo 1012602 2572033 := bstep (se 2 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 2572033 = 1929025) B1929025
theorem B1523471 : Blo 1012602 1523471 := bstep (se 1 (by rfl) ⟨1142603, by rfl⟩ : syracuseStep 1523471 = 2285207) B2285207
theorem B1523513 : Blo 1012602 1523513 := bstep (se 2 (by rfl) ⟨571317, by rfl⟩ : syracuseStep 1523513 = 1142635) B1142635
theorem B1523591 : Blo 1012602 1523591 := bstep (se 1 (by rfl) ⟨1142693, by rfl⟩ : syracuseStep 1523591 = 2285387) B2285387
theorem B3293075 : Blo 1012602 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B1523627 : Blo 1012602 1523627 := bstep (se 1 (by rfl) ⟨1142720, by rfl⟩ : syracuseStep 1523627 = 2285441) B2285441
theorem B1523657 : Blo 1012602 1523657 := bstep (se 2 (by rfl) ⟨571371, by rfl⟩ : syracuseStep 1523657 = 1142743) B1142743
theorem B1523771 : Blo 1012602 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B1523831 : Blo 1012602 1523831 := bstep (se 1 (by rfl) ⟨1142873, by rfl⟩ : syracuseStep 1523831 = 2285747) B2285747
theorem B1523855 : Blo 1012602 1523855 := bstep (se 1 (by rfl) ⟨1142891, by rfl⟩ : syracuseStep 1523855 = 2285783) B2285783
theorem B1523897 : Blo 1012602 1523897 := bstep (se 2 (by rfl) ⟨571461, by rfl⟩ : syracuseStep 1523897 = 1142923) B1142923
theorem B5554433 : Blo 1012602 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1523975 : Blo 1012602 1523975 := bstep (se 1 (by rfl) ⟨1142981, by rfl⟩ : syracuseStep 1523975 = 2285963) B2285963
theorem B1524011 : Blo 1012602 1524011 := bstep (se 1 (by rfl) ⟨1143008, by rfl⟩ : syracuseStep 1524011 = 2286017) B2286017
theorem B3424571 : Blo 1012602 3424571 := bstep (se 1 (by rfl) ⟨2568428, by rfl⟩ : syracuseStep 3424571 = 5136857) B5136857
theorem B1524041 : Blo 1012602 1524041 := bstep (se 2 (by rfl) ⟨571515, by rfl⟩ : syracuseStep 1524041 = 1143031) B1143031
theorem B2572631 : Blo 1012602 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B5128595 : Blo 1012602 5128595 := bstep (se 1 (by rfl) ⟨3846446, by rfl⟩ : syracuseStep 5128595 = 7692893) B7692893
theorem B1524155 : Blo 1012602 1524155 := bstep (se 1 (by rfl) ⟨1143116, by rfl⟩ : syracuseStep 1524155 = 2286233) B2286233
theorem B1524215 : Blo 1012602 1524215 := bstep (se 1 (by rfl) ⟨1143161, by rfl⟩ : syracuseStep 1524215 = 2286323) B2286323
theorem B1524239 : Blo 1012602 1524239 := bstep (se 1 (by rfl) ⟨1143179, by rfl⟩ : syracuseStep 1524239 = 2286359) B2286359
theorem B2572843 : Blo 1012602 2572843 := bstep (se 1 (by rfl) ⟨1929632, by rfl⟩ : syracuseStep 2572843 = 3859265) B3859265
theorem B1524281 : Blo 1012602 1524281 := bstep (se 2 (by rfl) ⟨571605, by rfl⟩ : syracuseStep 1524281 = 1143211) B1143211
theorem B1524359 : Blo 1012602 1524359 := bstep (se 1 (by rfl) ⟨1143269, by rfl⟩ : syracuseStep 1524359 = 2286539) B2286539
theorem B1524395 : Blo 1012602 1524395 := bstep (se 1 (by rfl) ⟨1143296, by rfl⟩ : syracuseStep 1524395 = 2286593) B2286593
theorem B2572985 : Blo 1012602 2572985 := bstep (se 2 (by rfl) ⟨964869, by rfl⟩ : syracuseStep 2572985 = 1929739) B1929739
theorem B1524425 : Blo 1012602 1524425 := bstep (se 2 (by rfl) ⟨571659, by rfl⟩ : syracuseStep 1524425 = 1143319) B1143319
theorem B3425057 : Blo 1012602 3425057 := bstep (se 2 (by rfl) ⟨1284396, by rfl⟩ : syracuseStep 3425057 = 2568793) B2568793
theorem B1524539 : Blo 1012602 1524539 := bstep (se 1 (by rfl) ⟨1143404, by rfl⟩ : syracuseStep 1524539 = 2286809) B2286809
theorem B1524599 : Blo 1012602 1524599 := bstep (se 1 (by rfl) ⟨1143449, by rfl⟩ : syracuseStep 1524599 = 2286899) B2286899
theorem B4113287 : Blo 1012602 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B1524623 : Blo 1012602 1524623 := bstep (se 1 (by rfl) ⟨1143467, by rfl⟩ : syracuseStep 1524623 = 2286935) B2286935
theorem B1524665 : Blo 1012602 1524665 := bstep (se 2 (by rfl) ⟨571749, by rfl⟩ : syracuseStep 1524665 = 1143499) B1143499
theorem B1524743 : Blo 1012602 1524743 := bstep (se 1 (by rfl) ⟨1143557, by rfl⟩ : syracuseStep 1524743 = 2287115) B2287115
theorem B1524779 : Blo 1012602 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B1524809 : Blo 1012602 1524809 := bstep (se 2 (by rfl) ⟨571803, by rfl⟩ : syracuseStep 1524809 = 1143607) B1143607
theorem B2278547 : Blo 1012602 2278547 := bstep (se 1 (by rfl) ⟨1708910, by rfl⟩ : syracuseStep 2278547 = 3417821) B3417821
theorem B2278601 : Blo 1012602 2278601 := bstep (se 2 (by rfl) ⟨854475, by rfl⟩ : syracuseStep 2278601 = 1708951) B1708951
theorem B3425651 : Blo 1012602 3425651 := bstep (se 1 (by rfl) ⟨2569238, by rfl⟩ : syracuseStep 3425651 = 5138477) B5138477
theorem B5784979 : Blo 1012602 5784979 := bstep (se 1 (by rfl) ⟨4338734, by rfl⟩ : syracuseStep 5784979 = 8677469) B8677469
theorem B37045835 : Blo 1012602 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B2279303 : Blo 1012602 2279303 := bstep (se 1 (by rfl) ⟨1709477, by rfl⟩ : syracuseStep 2279303 = 3418955) B3418955
theorem B2606995 : Blo 1012602 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B2279483 : Blo 1012602 2279483 := bstep (se 1 (by rfl) ⟨1709612, by rfl⟩ : syracuseStep 2279483 = 3419225) B3419225
theorem B2279609 : Blo 1012602 2279609 := bstep (se 2 (by rfl) ⟨854853, by rfl⟩ : syracuseStep 2279609 = 1709707) B1709707
theorem B12503285 : Blo 1012602 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B4868353 : Blo 1012602 4868353 := bstep (se 2 (by rfl) ⟨1825632, by rfl⟩ : syracuseStep 4868353 = 3651265) B3651265
theorem B70240517 : Blo 1012602 70240517 := bstep (se 4 (by rfl) ⟨6585048, by rfl⟩ : syracuseStep 70240517 = 13170097) B13170097
theorem B2279951 : Blo 1012602 2279951 := bstep (se 1 (by rfl) ⟨1709963, by rfl⟩ : syracuseStep 2279951 = 3419927) B3419927
theorem B2279969 : Blo 1012602 2279969 := bstep (se 2 (by rfl) ⟨854988, by rfl⟩ : syracuseStep 2279969 = 1709977) B1709977
theorem B3853115 : Blo 1012602 3853115 := bstep (se 1 (by rfl) ⟨2889836, by rfl⟩ : syracuseStep 3853115 = 5779673) B5779673
theorem B2280311 : Blo 1012602 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B3656657 : Blo 1012602 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B2280491 : Blo 1012602 2280491 := bstep (se 1 (by rfl) ⟨1710368, by rfl⟩ : syracuseStep 2280491 = 3420737) B3420737
theorem B5786711 : Blo 1012602 5786711 := bstep (se 1 (by rfl) ⟨4340033, by rfl⟩ : syracuseStep 5786711 = 8680067) B8680067
theorem B3853601 : Blo 1012602 3853601 := bstep (se 2 (by rfl) ⟨1445100, by rfl⟩ : syracuseStep 3853601 = 2890201) B2890201
theorem B1756475 : Blo 1012602 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B2280851 : Blo 1012602 2280851 := bstep (se 1 (by rfl) ⟨1710638, by rfl⟩ : syracuseStep 2280851 = 3421277) B3421277
theorem B5131673 : Blo 1012602 5131673 := bstep (se 2 (by rfl) ⟨1924377, by rfl⟩ : syracuseStep 5131673 = 3848755) B3848755
theorem B2280905 : Blo 1012602 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B46845539 : Blo 1012602 46845539 := bstep (se 1 (by rfl) ⟨35134154, by rfl⟩ : syracuseStep 46845539 = 70268309) B70268309
theorem B11554649 : Blo 1012602 11554649 := bstep (se 2 (by rfl) ⟨4332993, by rfl⟩ : syracuseStep 11554649 = 8665987) B8665987
theorem B3428243 : Blo 1012602 3428243 := bstep (se 1 (by rfl) ⟨2571182, by rfl⟩ : syracuseStep 3428243 = 5142365) B5142365
theorem B8671319 : Blo 1012602 8671319 := bstep (se 1 (by rfl) ⟨6503489, by rfl⟩ : syracuseStep 8671319 = 13006979) B13006979
theorem B9883781 : Blo 1012602 9883781 := bstep (se 4 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 9883781 = 1853209) B1853209
theorem B2281607 : Blo 1012602 2281607 := bstep (se 1 (by rfl) ⟨1711205, by rfl⟩ : syracuseStep 2281607 = 3422411) B3422411
theorem B3854573 : Blo 1012602 3854573 := bstep (se 3 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 3854573 = 1445465) B1445465
theorem B2281787 : Blo 1012602 2281787 := bstep (se 1 (by rfl) ⟨1711340, by rfl⟩ : syracuseStep 2281787 = 3422681) B3422681
theorem B2281913 : Blo 1012602 2281913 := bstep (se 2 (by rfl) ⟨855717, by rfl⟩ : syracuseStep 2281913 = 1711435) B1711435
theorem B8671697 : Blo 1012602 8671697 := bstep (se 2 (by rfl) ⟨3251886, by rfl⟩ : syracuseStep 8671697 = 6503773) B6503773
theorem B3854891 : Blo 1012602 3854891 := bstep (se 1 (by rfl) ⟨2891168, by rfl⟩ : syracuseStep 3854891 = 5782337) B5782337
theorem B4117111 : Blo 1012602 4117111 := bstep (se 1 (by rfl) ⟨3087833, by rfl⟩ : syracuseStep 4117111 = 6175667) B6175667
theorem B4117229 : Blo 1012602 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B2282255 : Blo 1012602 2282255 := bstep (se 1 (by rfl) ⟨1711691, by rfl⟩ : syracuseStep 2282255 = 3423383) B3423383
theorem B2282273 : Blo 1012602 2282273 := bstep (se 2 (by rfl) ⟨855852, by rfl⟩ : syracuseStep 2282273 = 1711705) B1711705
theorem B1626923 : Blo 1012602 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B1856315 : Blo 1012602 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B3298163 : Blo 1012602 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B1561529 : Blo 1012602 1561529 := bstep (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) B1171147
theorem B11719685 : Blo 1012602 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B6509591 : Blo 1012602 6509591 := bstep (se 1 (by rfl) ⟨4882193, by rfl⟩ : syracuseStep 6509591 = 9764387) B9764387
theorem B2282615 : Blo 1012602 2282615 := bstep (se 1 (by rfl) ⟨1711961, by rfl⟩ : syracuseStep 2282615 = 3423923) B3423923
theorem B3429647 : Blo 1012602 3429647 := bstep (se 1 (by rfl) ⟨2572235, by rfl⟩ : syracuseStep 3429647 = 5144471) B5144471
theorem B2282795 : Blo 1012602 2282795 := bstep (se 1 (by rfl) ⟨1712096, by rfl⟩ : syracuseStep 2282795 = 3424193) B3424193
theorem B3429917 : Blo 1012602 3429917 := bstep (se 3 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 3429917 = 1286219) B1286219
theorem B1922707 : Blo 1012602 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B2283155 : Blo 1012602 2283155 := bstep (se 1 (by rfl) ⟨1712366, by rfl⟩ : syracuseStep 2283155 = 3424733) B3424733
theorem B9885377 : Blo 1012602 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B2283209 : Blo 1012602 2283209 := bstep (se 2 (by rfl) ⟨856203, by rfl⟩ : syracuseStep 2283209 = 1712407) B1712407
theorem B256366309 : Blo 1012602 256366309 := bstep (se 4 (by rfl) ⟨24034341, by rfl⟩ : syracuseStep 256366309 = 48068683) B48068683
theorem B1922935 : Blo 1012602 1922935 := bstep (se 1 (by rfl) ⟨1442201, by rfl⟩ : syracuseStep 1922935 = 2884403) B2884403
theorem B5134265 : Blo 1012602 5134265 := bstep (se 2 (by rfl) ⟨1925349, by rfl⟩ : syracuseStep 5134265 = 3850699) B3850699
theorem B2742407 : Blo 1012602 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B27121837 : Blo 1012602 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B2283911 : Blo 1012602 2283911 := bstep (se 1 (by rfl) ⟨1712933, by rfl⟩ : syracuseStep 2283911 = 3425867) B3425867
theorem B2284091 : Blo 1012602 2284091 := bstep (se 1 (by rfl) ⟨1713068, by rfl⟩ : syracuseStep 2284091 = 3426137) B3426137
theorem B2284217 : Blo 1012602 2284217 := bstep (se 2 (by rfl) ⟨856581, by rfl⟩ : syracuseStep 2284217 = 1713163) B1713163
theorem B5856059 : Blo 1012602 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B2284559 : Blo 1012602 2284559 := bstep (se 1 (by rfl) ⟨1713419, by rfl⟩ : syracuseStep 2284559 = 3426839) B3426839
theorem B2284577 : Blo 1012602 2284577 := bstep (se 2 (by rfl) ⟨856716, by rfl⟩ : syracuseStep 2284577 = 1713433) B1713433
theorem B2743357 : Blo 1012602 2743357 := bstep (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) B1028759
theorem B1825993 : Blo 1012602 1825993 := bstep (se 2 (by rfl) ⟨684747, by rfl⟩ : syracuseStep 1825993 = 1369495) B1369495
theorem B5135561 : Blo 1012602 5135561 := bstep (se 2 (by rfl) ⟨1925835, by rfl⟩ : syracuseStep 5135561 = 3851671) B3851671
theorem B2284919 : Blo 1012602 2284919 := bstep (se 1 (by rfl) ⟨1713689, by rfl⟩ : syracuseStep 2284919 = 3427379) B3427379
theorem B1924499 : Blo 1012602 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1924553 : Blo 1012602 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B1924651 : Blo 1012602 1924651 := bstep (se 1 (by rfl) ⟨1443488, by rfl⟩ : syracuseStep 1924651 = 2886977) B2886977
theorem B2285099 : Blo 1012602 2285099 := bstep (se 1 (by rfl) ⟨1713824, by rfl⟩ : syracuseStep 2285099 = 3427649) B3427649
theorem B8675009 : Blo 1012602 8675009 := bstep (se 2 (by rfl) ⟨3253128, by rfl⟩ : syracuseStep 8675009 = 6506257) B6506257
theorem B9756389 : Blo 1012602 9756389 := bstep (se 4 (by rfl) ⟨914661, by rfl⟩ : syracuseStep 9756389 = 1829323) B1829323
theorem B1924879 : Blo 1012602 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B2285459 : Blo 1012602 2285459 := bstep (se 1 (by rfl) ⟨1714094, by rfl⟩ : syracuseStep 2285459 = 3428189) B3428189
theorem B2285513 : Blo 1012602 2285513 := bstep (se 2 (by rfl) ⟨857067, by rfl⟩ : syracuseStep 2285513 = 1714135) B1714135
theorem B3858461 : Blo 1012602 3858461 := bstep (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) B1446923
theorem B3858475 : Blo 1012602 3858475 := bstep (se 1 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 3858475 = 5787713) B5787713
theorem B1827017 : Blo 1012602 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B4874755 : Blo 1012602 4874755 := bstep (se 1 (by rfl) ⟨3656066, by rfl⟩ : syracuseStep 4874755 = 7312133) B7312133
theorem B1139215 : Blo 1012602 1139215 := bstep (se 1 (by rfl) ⟨854411, by rfl⟩ : syracuseStep 1139215 = 1708823) B1708823
theorem B4874813 : Blo 1012602 4874813 := bstep (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) B1828055
theorem B1368695 : Blo 1012602 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B2286215 : Blo 1012602 2286215 := bstep (se 1 (by rfl) ⟨1714661, by rfl⟩ : syracuseStep 2286215 = 3429323) B3429323
theorem B2286395 : Blo 1012602 2286395 := bstep (se 1 (by rfl) ⟨1714796, by rfl⟩ : syracuseStep 2286395 = 3429593) B3429593
theorem B2286521 : Blo 1012602 2286521 := bstep (se 2 (by rfl) ⟨857445, by rfl⟩ : syracuseStep 2286521 = 1714891) B1714891
theorem B1139719 : Blo 1012602 1139719 := bstep (se 1 (by rfl) ⟨854789, by rfl⟩ : syracuseStep 1139719 = 1709579) B1709579
theorem B7037975 : Blo 1012602 7037975 := bstep (se 1 (by rfl) ⟨5278481, by rfl⟩ : syracuseStep 7037975 = 10556963) B10556963
theorem B4121687 : Blo 1012602 4121687 := bstep (se 1 (by rfl) ⟨3091265, by rfl⟩ : syracuseStep 4121687 = 6182531) B6182531
theorem B1139899 : Blo 1012602 1139899 := bstep (se 1 (by rfl) ⟨854924, by rfl⟩ : syracuseStep 1139899 = 1709849) B1709849
theorem B2286863 : Blo 1012602 2286863 := bstep (se 1 (by rfl) ⟨1715147, by rfl⟩ : syracuseStep 2286863 = 3430295) B3430295
theorem B2286881 : Blo 1012602 2286881 := bstep (se 2 (by rfl) ⟨857580, by rfl⟩ : syracuseStep 2286881 = 1715161) B1715161
theorem B1369387 : Blo 1012602 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B1926443 : Blo 1012602 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B2057771 : Blo 1012602 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B7300685 : Blo 1012602 7300685 := bstep (se 3 (by rfl) ⟨1368878, by rfl⟩ : syracuseStep 7300685 = 2737757) B2737757
theorem B2287223 : Blo 1012602 2287223 := bstep (se 1 (by rfl) ⟨1715417, by rfl⟩ : syracuseStep 2287223 = 3430835) B3430835
theorem B1140367 : Blo 1012602 1140367 := bstep (se 1 (by rfl) ⟨855275, by rfl⟩ : syracuseStep 1140367 = 1710551) B1710551
theorem B1140871 : Blo 1012602 1140871 := bstep (se 1 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 1140871 = 1711307) B1711307
theorem B2746667 : Blo 1012602 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B1141051 : Blo 1012602 1141051 := bstep (se 1 (by rfl) ⟨855788, by rfl⟩ : syracuseStep 1141051 = 1711577) B1711577
theorem B5564819 : Blo 1012602 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B1141519 : Blo 1012602 1141519 := bstep (se 1 (by rfl) ⟨856139, by rfl⟩ : syracuseStep 1141519 = 1712279) B1712279
theorem B6941477 : Blo 1012602 6941477 := bstep (se 4 (by rfl) ⟨650763, by rfl⟩ : syracuseStep 6941477 = 1301527) B1301527
theorem B1928137 : Blo 1012602 1928137 := bstep (se 2 (by rfl) ⟨723051, by rfl⟩ : syracuseStep 1928137 = 1446103) B1446103
theorem B1142023 : Blo 1012602 1142023 := bstep (se 1 (by rfl) ⟨856517, by rfl⟩ : syracuseStep 1142023 = 1713035) B1713035
theorem B1142203 : Blo 1012602 1142203 := bstep (se 1 (by rfl) ⟨856652, by rfl⟩ : syracuseStep 1142203 = 1713305) B1713305
theorem B1371593 : Blo 1012602 1371593 := bstep (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) B1028695
theorem B44461709 : Blo 1012602 44461709 := bstep (se 3 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 44461709 = 16673141) B16673141
theorem B1142671 : Blo 1012602 1142671 := bstep (se 1 (by rfl) ⟨857003, by rfl⟩ : syracuseStep 1142671 = 1714007) B1714007
theorem B1143175 : Blo 1012602 1143175 := bstep (se 1 (by rfl) ⟨857381, by rfl⟩ : syracuseStep 1143175 = 1714763) B1714763
theorem B1143355 : Blo 1012602 1143355 := bstep (se 1 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 1143355 = 1715033) B1715033
theorem B1831609 : Blo 1012602 1831609 := bstep (se 2 (by rfl) ⟨686853, by rfl⟩ : syracuseStep 1831609 = 1373707) B1373707
theorem B26047169 : Blo 1012602 26047169 := bstep (se 2 (by rfl) ⟨9767688, by rfl⟩ : syracuseStep 26047169 = 19535377) B19535377
theorem B7697267 : Blo 1012602 7697267 := bstep (se 1 (by rfl) ⟨5772950, by rfl⟩ : syracuseStep 7697267 = 11545901) B11545901
theorem B1012615 : Blo 1012602 1012615 := bstep (se 1 (by rfl) ⟨759461, by rfl⟩ : syracuseStep 1012615 = 1518923) B1518923
theorem B1012623 : Blo 1012602 1012623 := bstep (se 1 (by rfl) ⟨759467, by rfl⟩ : syracuseStep 1012623 = 1518935) B1518935
theorem B5141393 : Blo 1012602 5141393 := bstep (se 2 (by rfl) ⟨1928022, by rfl⟩ : syracuseStep 5141393 = 3856045) B3856045
theorem B1012667 : Blo 1012602 1012667 := bstep (se 1 (by rfl) ⟨759500, by rfl⟩ : syracuseStep 1012667 = 1519001) B1519001
theorem B1012743 : Blo 1012602 1012743 := bstep (se 1 (by rfl) ⟨759557, by rfl⟩ : syracuseStep 1012743 = 1519115) B1519115
theorem B1012751 : Blo 1012602 1012751 := bstep (se 1 (by rfl) ⟨759563, by rfl⟩ : syracuseStep 1012751 = 1519127) B1519127
theorem B1012795 : Blo 1012602 1012795 := bstep (se 1 (by rfl) ⟨759596, by rfl⟩ : syracuseStep 1012795 = 1519193) B1519193
theorem B1012871 : Blo 1012602 1012871 := bstep (se 1 (by rfl) ⟨759653, by rfl⟩ : syracuseStep 1012871 = 1519307) B1519307
theorem B1012879 : Blo 1012602 1012879 := bstep (se 1 (by rfl) ⟨759659, by rfl⟩ : syracuseStep 1012879 = 1519319) B1519319
theorem B1012923 : Blo 1012602 1012923 := bstep (se 1 (by rfl) ⟨759692, by rfl⟩ : syracuseStep 1012923 = 1519385) B1519385
theorem B1012999 : Blo 1012602 1012999 := bstep (se 1 (by rfl) ⟨759749, by rfl⟩ : syracuseStep 1012999 = 1519499) B1519499
theorem B1013007 : Blo 1012602 1013007 := bstep (se 1 (by rfl) ⟨759755, by rfl⟩ : syracuseStep 1013007 = 1519511) B1519511
theorem B1013051 : Blo 1012602 1013051 := bstep (se 1 (by rfl) ⟨759788, by rfl⟩ : syracuseStep 1013051 = 1519577) B1519577
theorem B1013127 : Blo 1012602 1013127 := bstep (se 1 (by rfl) ⟨759845, by rfl⟩ : syracuseStep 1013127 = 1519691) B1519691
theorem B1013135 : Blo 1012602 1013135 := bstep (se 1 (by rfl) ⟨759851, by rfl⟩ : syracuseStep 1013135 = 1519703) B1519703
theorem B1013179 : Blo 1012602 1013179 := bstep (se 1 (by rfl) ⟨759884, by rfl⟩ : syracuseStep 1013179 = 1519769) B1519769
theorem B1013255 : Blo 1012602 1013255 := bstep (se 1 (by rfl) ⟨759941, by rfl⟩ : syracuseStep 1013255 = 1519883) B1519883
theorem B1013263 : Blo 1012602 1013263 := bstep (se 1 (by rfl) ⟨759947, by rfl⟩ : syracuseStep 1013263 = 1519895) B1519895
theorem B1013307 : Blo 1012602 1013307 := bstep (se 1 (by rfl) ⟨759980, by rfl⟩ : syracuseStep 1013307 = 1519961) B1519961
theorem B1013383 : Blo 1012602 1013383 := bstep (se 1 (by rfl) ⟨760037, by rfl⟩ : syracuseStep 1013383 = 1520075) B1520075
theorem B1013391 : Blo 1012602 1013391 := bstep (se 1 (by rfl) ⟨760043, by rfl⟩ : syracuseStep 1013391 = 1520087) B1520087
theorem B1013435 : Blo 1012602 1013435 := bstep (se 1 (by rfl) ⟨760076, by rfl⟩ : syracuseStep 1013435 = 1520153) B1520153
theorem B1013511 : Blo 1012602 1013511 := bstep (se 1 (by rfl) ⟨760133, by rfl⟩ : syracuseStep 1013511 = 1520267) B1520267
theorem B1013519 : Blo 1012602 1013519 := bstep (se 1 (by rfl) ⟨760139, by rfl⟩ : syracuseStep 1013519 = 1520279) B1520279
theorem B1013563 : Blo 1012602 1013563 := bstep (se 1 (by rfl) ⟨760172, by rfl⟩ : syracuseStep 1013563 = 1520345) B1520345
theorem B3700615 : Blo 1012602 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B1013639 : Blo 1012602 1013639 := bstep (se 1 (by rfl) ⟨760229, by rfl⟩ : syracuseStep 1013639 = 1520459) B1520459
theorem B1013647 : Blo 1012602 1013647 := bstep (se 1 (by rfl) ⟨760235, by rfl⟩ : syracuseStep 1013647 = 1520471) B1520471
theorem B5339033 : Blo 1012602 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1013691 : Blo 1012602 1013691 := bstep (se 1 (by rfl) ⟨760268, by rfl⟩ : syracuseStep 1013691 = 1520537) B1520537
theorem B1013767 : Blo 1012602 1013767 := bstep (se 1 (by rfl) ⟨760325, by rfl⟩ : syracuseStep 1013767 = 1520651) B1520651
theorem B1013775 : Blo 1012602 1013775 := bstep (se 1 (by rfl) ⟨760331, by rfl⟩ : syracuseStep 1013775 = 1520663) B1520663
theorem B1013819 : Blo 1012602 1013819 := bstep (se 1 (by rfl) ⟨760364, by rfl⟩ : syracuseStep 1013819 = 1520729) B1520729
theorem B1013895 : Blo 1012602 1013895 := bstep (se 1 (by rfl) ⟨760421, by rfl⟩ : syracuseStep 1013895 = 1520843) B1520843
theorem B1013903 : Blo 1012602 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B1013947 : Blo 1012602 1013947 := bstep (se 1 (by rfl) ⟨760460, by rfl⟩ : syracuseStep 1013947 = 1520921) B1520921
theorem B5208257 : Blo 1012602 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B1014023 : Blo 1012602 1014023 := bstep (se 1 (by rfl) ⟨760517, by rfl⟩ : syracuseStep 1014023 = 1521035) B1521035
theorem B1014031 : Blo 1012602 1014031 := bstep (se 1 (by rfl) ⟨760523, by rfl⟩ : syracuseStep 1014031 = 1521047) B1521047
theorem B1014075 : Blo 1012602 1014075 := bstep (se 1 (by rfl) ⟨760556, by rfl⟩ : syracuseStep 1014075 = 1521113) B1521113
theorem B1014151 : Blo 1012602 1014151 := bstep (se 1 (by rfl) ⟨760613, by rfl⟩ : syracuseStep 1014151 = 1521227) B1521227
theorem B1014159 : Blo 1012602 1014159 := bstep (se 1 (by rfl) ⟨760619, by rfl⟩ : syracuseStep 1014159 = 1521239) B1521239
theorem B1014203 : Blo 1012602 1014203 := bstep (se 1 (by rfl) ⟨760652, by rfl⟩ : syracuseStep 1014203 = 1521305) B1521305
theorem B1014279 : Blo 1012602 1014279 := bstep (se 1 (by rfl) ⟨760709, by rfl⟩ : syracuseStep 1014279 = 1521419) B1521419
theorem B1014287 : Blo 1012602 1014287 := bstep (se 1 (by rfl) ⟨760715, by rfl⟩ : syracuseStep 1014287 = 1521431) B1521431
theorem B1014331 : Blo 1012602 1014331 := bstep (se 1 (by rfl) ⟨760748, by rfl⟩ : syracuseStep 1014331 = 1521497) B1521497
theorem B1014407 : Blo 1012602 1014407 := bstep (se 1 (by rfl) ⟨760805, by rfl⟩ : syracuseStep 1014407 = 1521611) B1521611
theorem B1014415 : Blo 1012602 1014415 := bstep (se 1 (by rfl) ⟨760811, by rfl⟩ : syracuseStep 1014415 = 1521623) B1521623
theorem B1014459 : Blo 1012602 1014459 := bstep (se 1 (by rfl) ⟨760844, by rfl⟩ : syracuseStep 1014459 = 1521689) B1521689
theorem B1014535 : Blo 1012602 1014535 := bstep (se 1 (by rfl) ⟨760901, by rfl⟩ : syracuseStep 1014535 = 1521803) B1521803
theorem B1014543 : Blo 1012602 1014543 := bstep (se 1 (by rfl) ⟨760907, by rfl⟩ : syracuseStep 1014543 = 1521815) B1521815
theorem B1014587 : Blo 1012602 1014587 := bstep (se 1 (by rfl) ⟨760940, by rfl⟩ : syracuseStep 1014587 = 1521881) B1521881
theorem B1014663 : Blo 1012602 1014663 := bstep (se 1 (by rfl) ⟨760997, by rfl⟩ : syracuseStep 1014663 = 1521995) B1521995
theorem B1014671 : Blo 1012602 1014671 := bstep (se 1 (by rfl) ⟨761003, by rfl⟩ : syracuseStep 1014671 = 1522007) B1522007
theorem B1014715 : Blo 1012602 1014715 := bstep (se 1 (by rfl) ⟨761036, by rfl⟩ : syracuseStep 1014715 = 1522073) B1522073
theorem B5143499 : Blo 1012602 5143499 := bstep (se 1 (by rfl) ⟨3857624, by rfl⟩ : syracuseStep 5143499 = 7715249) B7715249
theorem B1014791 : Blo 1012602 1014791 := bstep (se 1 (by rfl) ⟨761093, by rfl⟩ : syracuseStep 1014791 = 1522187) B1522187
theorem B1014799 : Blo 1012602 1014799 := bstep (se 1 (by rfl) ⟨761099, by rfl⟩ : syracuseStep 1014799 = 1522199) B1522199
theorem B1014843 : Blo 1012602 1014843 := bstep (se 1 (by rfl) ⟨761132, by rfl⟩ : syracuseStep 1014843 = 1522265) B1522265
theorem B1014919 : Blo 1012602 1014919 := bstep (se 1 (by rfl) ⟨761189, by rfl⟩ : syracuseStep 1014919 = 1522379) B1522379
theorem B1014927 : Blo 1012602 1014927 := bstep (se 1 (by rfl) ⟨761195, by rfl⟩ : syracuseStep 1014927 = 1522391) B1522391
theorem B1014971 : Blo 1012602 1014971 := bstep (se 1 (by rfl) ⟨761228, by rfl⟩ : syracuseStep 1014971 = 1522457) B1522457
theorem B1015047 : Blo 1012602 1015047 := bstep (se 1 (by rfl) ⟨761285, by rfl⟩ : syracuseStep 1015047 = 1522571) B1522571
theorem B1015055 : Blo 1012602 1015055 := bstep (se 1 (by rfl) ⟨761291, by rfl⟩ : syracuseStep 1015055 = 1522583) B1522583
theorem B5143823 : Blo 1012602 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B1015099 : Blo 1012602 1015099 := bstep (se 1 (by rfl) ⟨761324, by rfl⟩ : syracuseStep 1015099 = 1522649) B1522649
theorem B1015175 : Blo 1012602 1015175 := bstep (se 1 (by rfl) ⟨761381, by rfl⟩ : syracuseStep 1015175 = 1522763) B1522763
theorem B1015183 : Blo 1012602 1015183 := bstep (se 1 (by rfl) ⟨761387, by rfl⟩ : syracuseStep 1015183 = 1522775) B1522775
theorem B1015227 : Blo 1012602 1015227 := bstep (se 1 (by rfl) ⟨761420, by rfl⟩ : syracuseStep 1015227 = 1522841) B1522841
theorem B1015303 : Blo 1012602 1015303 := bstep (se 1 (by rfl) ⟨761477, by rfl⟩ : syracuseStep 1015303 = 1522955) B1522955
theorem B6159883 : Blo 1012602 6159883 := bstep (se 1 (by rfl) ⟨4619912, by rfl⟩ : syracuseStep 6159883 = 9239825) B9239825
theorem B1015311 : Blo 1012602 1015311 := bstep (se 1 (by rfl) ⟨761483, by rfl⟩ : syracuseStep 1015311 = 1522967) B1522967
theorem B18546205 : Blo 1012602 18546205 := bstep (se 3 (by rfl) ⟨3477413, by rfl⟩ : syracuseStep 18546205 = 6954827) B6954827
theorem B1015355 : Blo 1012602 1015355 := bstep (se 1 (by rfl) ⟨761516, by rfl⟩ : syracuseStep 1015355 = 1523033) B1523033
theorem B10976887 : Blo 1012602 10976887 := bstep (se 1 (by rfl) ⟨8232665, by rfl⟩ : syracuseStep 10976887 = 16465331) B16465331
theorem B1015431 : Blo 1012602 1015431 := bstep (se 1 (by rfl) ⟨761573, by rfl⟩ : syracuseStep 1015431 = 1523147) B1523147
theorem B1015439 : Blo 1012602 1015439 := bstep (se 1 (by rfl) ⟨761579, by rfl⟩ : syracuseStep 1015439 = 1523159) B1523159
theorem B1015483 : Blo 1012602 1015483 := bstep (se 1 (by rfl) ⟨761612, by rfl⟩ : syracuseStep 1015483 = 1523225) B1523225
theorem B1015559 : Blo 1012602 1015559 := bstep (se 1 (by rfl) ⟨761669, by rfl⟩ : syracuseStep 1015559 = 1523339) B1523339
theorem B1015567 : Blo 1012602 1015567 := bstep (se 1 (by rfl) ⟨761675, by rfl⟩ : syracuseStep 1015567 = 1523351) B1523351
theorem B13860659 : Blo 1012602 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B1015611 : Blo 1012602 1015611 := bstep (se 1 (by rfl) ⟨761708, by rfl⟩ : syracuseStep 1015611 = 1523417) B1523417
theorem B1015687 : Blo 1012602 1015687 := bstep (se 1 (by rfl) ⟨761765, by rfl⟩ : syracuseStep 1015687 = 1523531) B1523531
theorem B1015695 : Blo 1012602 1015695 := bstep (se 1 (by rfl) ⟨761771, by rfl⟩ : syracuseStep 1015695 = 1523543) B1523543
theorem B1015739 : Blo 1012602 1015739 := bstep (se 1 (by rfl) ⟨761804, by rfl⟩ : syracuseStep 1015739 = 1523609) B1523609
theorem B1015847 : Blo 1012602 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B5144633 : Blo 1012602 5144633 := bstep (se 2 (by rfl) ⟨1929237, by rfl⟩ : syracuseStep 5144633 = 3858475) B3858475
theorem B1015887 : Blo 1012602 1015887 := bstep (se 1 (by rfl) ⟨761915, by rfl⟩ : syracuseStep 1015887 = 1523831) B1523831
theorem B1015903 : Blo 1012602 1015903 := bstep (se 1 (by rfl) ⟨761927, by rfl⟩ : syracuseStep 1015903 = 1523855) B1523855
theorem B1015931 : Blo 1012602 1015931 := bstep (se 1 (by rfl) ⟨761948, by rfl⟩ : syracuseStep 1015931 = 1523897) B1523897
theorem B21921941 : Blo 1012602 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B1015983 : Blo 1012602 1015983 := bstep (se 1 (by rfl) ⟨761987, by rfl⟩ : syracuseStep 1015983 = 1523975) B1523975
theorem B1016007 : Blo 1012602 1016007 := bstep (se 1 (by rfl) ⟨762005, by rfl⟩ : syracuseStep 1016007 = 1524011) B1524011
theorem B1016027 : Blo 1012602 1016027 := bstep (se 1 (by rfl) ⟨762020, by rfl⟩ : syracuseStep 1016027 = 1524041) B1524041
theorem B1016103 : Blo 1012602 1016103 := bstep (se 1 (by rfl) ⟨762077, by rfl⟩ : syracuseStep 1016103 = 1524155) B1524155
theorem B1016143 : Blo 1012602 1016143 := bstep (se 1 (by rfl) ⟨762107, by rfl⟩ : syracuseStep 1016143 = 1524215) B1524215
theorem B1016159 : Blo 1012602 1016159 := bstep (se 1 (by rfl) ⟨762119, by rfl⟩ : syracuseStep 1016159 = 1524239) B1524239
theorem B1016187 : Blo 1012602 1016187 := bstep (se 1 (by rfl) ⟨762140, by rfl⟩ : syracuseStep 1016187 = 1524281) B1524281
theorem B1016239 : Blo 1012602 1016239 := bstep (se 1 (by rfl) ⟨762179, by rfl⟩ : syracuseStep 1016239 = 1524359) B1524359
theorem B1016263 : Blo 1012602 1016263 := bstep (se 1 (by rfl) ⟨762197, by rfl⟩ : syracuseStep 1016263 = 1524395) B1524395
theorem B1016283 : Blo 1012602 1016283 := bstep (se 1 (by rfl) ⟨762212, by rfl⟩ : syracuseStep 1016283 = 1524425) B1524425
theorem B22282775 : Blo 1012602 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B1016359 : Blo 1012602 1016359 := bstep (se 1 (by rfl) ⟨762269, by rfl⟩ : syracuseStep 1016359 = 1524539) B1524539
theorem B1016399 : Blo 1012602 1016399 := bstep (se 1 (by rfl) ⟨762299, by rfl⟩ : syracuseStep 1016399 = 1524599) B1524599
theorem B1016415 : Blo 1012602 1016415 := bstep (se 1 (by rfl) ⟨762311, by rfl⟩ : syracuseStep 1016415 = 1524623) B1524623
theorem B1016443 : Blo 1012602 1016443 := bstep (se 1 (by rfl) ⟨762332, by rfl⟩ : syracuseStep 1016443 = 1524665) B1524665
theorem B4326023 : Blo 1012602 4326023 := bstep (se 1 (by rfl) ⟨3244517, by rfl⟩ : syracuseStep 4326023 = 6489035) B6489035
theorem B14811821 : Blo 1012602 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B1016495 : Blo 1012602 1016495 := bstep (se 1 (by rfl) ⟨762371, by rfl⟩ : syracuseStep 1016495 = 1524743) B1524743
theorem B1016519 : Blo 1012602 1016519 := bstep (se 1 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 1016519 = 1524779) B1524779
theorem B1016539 : Blo 1012602 1016539 := bstep (se 1 (by rfl) ⟨762404, by rfl⟩ : syracuseStep 1016539 = 1524809) B1524809
theorem B5768009 : Blo 1012602 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B12518671 : Blo 1012602 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B46827011 : Blo 1012602 46827011 := bstep (se 1 (by rfl) ⟨35120258, by rfl⟩ : syracuseStep 46827011 = 70240517) B70240517
theorem B3475295 : Blo 1012602 3475295 := bstep (se 1 (by rfl) ⟨2606471, by rfl⟩ : syracuseStep 3475295 = 5212943) B5212943
theorem B4950173 : Blo 1012602 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B31230359 : Blo 1012602 31230359 := bstep (se 1 (by rfl) ⟨23422769, by rfl⟩ : syracuseStep 31230359 = 46845539) B46845539
theorem B4164077 : Blo 1012602 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B3475993 : Blo 1012602 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B7703099 : Blo 1012602 7703099 := bstep (se 1 (by rfl) ⟨5777324, by rfl⟩ : syracuseStep 7703099 = 11554649) B11554649
theorem B6589187 : Blo 1012602 6589187 := bstep (se 1 (by rfl) ⟨4941890, by rfl⟩ : syracuseStep 6589187 = 9883781) B9883781
theorem B6491137 : Blo 1012602 6491137 := bstep (se 2 (by rfl) ⟨2434176, by rfl⟩ : syracuseStep 6491137 = 4868353) B4868353
theorem B1444873 : Blo 1012602 1444873 := bstep (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) B1083655
theorem B21957925 : Blo 1012602 21957925 := bstep (se 4 (by rfl) ⟨2058555, by rfl⟩ : syracuseStep 21957925 = 4117111) B4117111
theorem B1543529 : Blo 1012602 1543529 := bstep (se 2 (by rfl) ⟨578823, by rfl⟩ : syracuseStep 1543529 = 1157647) B1157647
theorem B3247901 : Blo 1012602 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B6590251 : Blo 1012602 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B11538611 : Blo 1012602 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B6165017 : Blo 1012602 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B3904039 : Blo 1012602 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B1446439 : Blo 1012602 1446439 := bstep (se 1 (by rfl) ⟨1084829, by rfl⟩ : syracuseStep 1446439 = 2169659) B2169659
theorem B8327891 : Blo 1012602 8327891 := bstep (se 1 (by rfl) ⟨6245918, by rfl⟩ : syracuseStep 8327891 = 12491837) B12491837
theorem B2167727 : Blo 1012602 2167727 := bstep (se 1 (by rfl) ⟨1625795, by rfl⟩ : syracuseStep 2167727 = 3251591) B3251591
theorem B1283035 : Blo 1012602 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B1709113 : Blo 1012602 1709113 := bstep (se 2 (by rfl) ⟨640917, by rfl⟩ : syracuseStep 1709113 = 1281835) B1281835
theorem B7803983 : Blo 1012602 7803983 := bstep (se 1 (by rfl) ⟨5852987, by rfl⟩ : syracuseStep 7803983 = 11705975) B11705975
theorem B1709255 : Blo 1012602 1709255 := bstep (se 1 (by rfl) ⟨1281941, by rfl⟩ : syracuseStep 1709255 = 2563883) B2563883
theorem B1709417 : Blo 1012602 1709417 := bstep (se 2 (by rfl) ⟨641031, by rfl⟩ : syracuseStep 1709417 = 1282063) B1282063
theorem B1218011 : Blo 1012602 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B3249875 : Blo 1012602 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B1709815 : Blo 1012602 1709815 := bstep (se 1 (by rfl) ⟨1282361, by rfl⟩ : syracuseStep 1709815 = 2564723) B2564723
theorem B1710011 : Blo 1012602 1710011 := bstep (se 1 (by rfl) ⟨1282508, by rfl⟩ : syracuseStep 1710011 = 2565017) B2565017
theorem B1710119 : Blo 1012602 1710119 := bstep (se 1 (by rfl) ⟨1282589, by rfl⟩ : syracuseStep 1710119 = 2565179) B2565179
theorem B1710409 : Blo 1012602 1710409 := bstep (se 2 (by rfl) ⟨641403, by rfl⟩ : syracuseStep 1710409 = 1282807) B1282807
theorem B8657239 : Blo 1012602 8657239 := bstep (se 1 (by rfl) ⟨6492929, by rfl⟩ : syracuseStep 8657239 = 12985859) B12985859
theorem B1710443 : Blo 1012602 1710443 := bstep (se 1 (by rfl) ⟨1282832, by rfl⟩ : syracuseStep 1710443 = 2565665) B2565665
theorem B9738629 : Blo 1012602 9738629 := bstep (se 4 (by rfl) ⟨912996, by rfl⟩ : syracuseStep 9738629 = 1825993) B1825993
theorem B25041287 : Blo 1012602 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B1710841 : Blo 1012602 1710841 := bstep (se 2 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 1710841 = 1283131) B1283131
theorem B7412627 : Blo 1012602 7412627 := bstep (se 1 (by rfl) ⟨5559470, by rfl⟩ : syracuseStep 7412627 = 11118941) B11118941
theorem B1711111 : Blo 1012602 1711111 := bstep (se 1 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 1711111 = 2566667) B2566667
theorem B12327979 : Blo 1012602 12327979 := bstep (se 1 (by rfl) ⟨9245984, by rfl⟩ : syracuseStep 12327979 = 18491969) B18491969
theorem B4627651 : Blo 1012602 4627651 := bstep (se 1 (by rfl) ⟨3470738, by rfl⟩ : syracuseStep 4627651 = 6941477) B6941477
theorem B1711543 : Blo 1012602 1711543 := bstep (se 1 (by rfl) ⟨1283657, by rfl⟩ : syracuseStep 1711543 = 2567315) B2567315
theorem B7806451 : Blo 1012602 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B2563609 : Blo 1012602 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B1711739 : Blo 1012602 1711739 := bstep (se 1 (by rfl) ⟨1283804, by rfl⟩ : syracuseStep 1711739 = 2567609) B2567609
theorem B2924221 : Blo 1012602 2924221 := bstep (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) B1096583
theorem B5775047 : Blo 1012602 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B2563913 : Blo 1012602 2563913 := bstep (se 2 (by rfl) ⟨961467, by rfl⟩ : syracuseStep 2563913 = 1922935) B1922935
theorem B6496109 : Blo 1012602 6496109 := bstep (se 3 (by rfl) ⟨1218020, by rfl⟩ : syracuseStep 6496109 = 2436041) B2436041
theorem B1712137 : Blo 1012602 1712137 := bstep (se 2 (by rfl) ⟨642051, by rfl⟩ : syracuseStep 1712137 = 1284103) B1284103
theorem B13901939 : Blo 1012602 13901939 := bstep (se 1 (by rfl) ⟨10426454, by rfl⟩ : syracuseStep 13901939 = 20852909) B20852909
theorem B2891933 : Blo 1012602 2891933 := bstep (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) B1084475
theorem B1712299 : Blo 1012602 1712299 := bstep (se 1 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 1712299 = 2568449) B2568449
theorem B1712603 : Blo 1012602 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B1712839 : Blo 1012602 1712839 := bstep (se 1 (by rfl) ⟨1284629, by rfl⟩ : syracuseStep 1712839 = 2569259) B2569259
theorem B9249491 : Blo 1012602 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B1713001 : Blo 1012602 1713001 := bstep (se 2 (by rfl) ⟨642375, by rfl⟩ : syracuseStep 1713001 = 1284751) B1284751
theorem B2565047 : Blo 1012602 2565047 := bstep (se 1 (by rfl) ⟨1923785, by rfl⟩ : syracuseStep 2565047 = 3847571) B3847571
theorem B1713595 : Blo 1012602 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B1713703 : Blo 1012602 1713703 := bstep (se 1 (by rfl) ⟨1285277, by rfl⟩ : syracuseStep 1713703 = 2570555) B2570555
theorem B3417659 : Blo 1012602 3417659 := bstep (se 1 (by rfl) ⟨2563244, by rfl⟩ : syracuseStep 3417659 = 5126489) B5126489
theorem B3253949 : Blo 1012602 3253949 := bstep (se 3 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 3253949 = 1220231) B1220231
theorem B4335353 : Blo 1012602 4335353 := bstep (se 2 (by rfl) ⟨1625757, by rfl⟩ : syracuseStep 4335353 = 3251515) B3251515
theorem B3417929 : Blo 1012602 3417929 := bstep (se 2 (by rfl) ⟨1281723, by rfl⟩ : syracuseStep 3417929 = 2563447) B2563447
theorem B1714027 : Blo 1012602 1714027 := bstep (se 1 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 1714027 = 2571041) B2571041
theorem B2435003 : Blo 1012602 2435003 := bstep (se 1 (by rfl) ⟨1826252, by rfl⟩ : syracuseStep 2435003 = 3652505) B3652505
theorem B2566151 : Blo 1012602 2566151 := bstep (se 1 (by rfl) ⟨1924613, by rfl⟩ : syracuseStep 2566151 = 3849227) B3849227
theorem B2566201 : Blo 1012602 2566201 := bstep (se 2 (by rfl) ⟨962325, by rfl⟩ : syracuseStep 2566201 = 1924651) B1924651
theorem B2566505 : Blo 1012602 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B4336001 : Blo 1012602 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B1715087 : Blo 1012602 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B3419063 : Blo 1012602 3419063 := bstep (se 1 (by rfl) ⟨2564297, by rfl⟩ : syracuseStep 3419063 = 5128595) B5128595
theorem B15641527 : Blo 1012602 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B1715323 : Blo 1012602 1715323 := bstep (se 1 (by rfl) ⟨1286492, by rfl⟩ : syracuseStep 1715323 = 2572985) B2572985
theorem B6499673 : Blo 1012602 6499673 := bstep (se 2 (by rfl) ⟨2437377, by rfl⟩ : syracuseStep 6499673 = 4874755) B4874755
theorem B1518953 : Blo 1012602 1518953 := bstep (se 2 (by rfl) ⟨569607, by rfl⟩ : syracuseStep 1518953 = 1139215) B1139215
theorem B1519031 : Blo 1012602 1519031 := bstep (se 1 (by rfl) ⟨1139273, by rfl⟩ : syracuseStep 1519031 = 2278547) B2278547
theorem B1519067 : Blo 1012602 1519067 := bstep (se 1 (by rfl) ⟨1139300, by rfl⟩ : syracuseStep 1519067 = 2278601) B2278601
theorem B3419657 : Blo 1012602 3419657 := bstep (se 2 (by rfl) ⟨1282371, by rfl⟩ : syracuseStep 3419657 = 2564743) B2564743
theorem B3845657 : Blo 1012602 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B6499901 : Blo 1012602 6499901 := bstep (se 3 (by rfl) ⟨1218731, by rfl⟩ : syracuseStep 6499901 = 2437463) B2437463
theorem B6172409 : Blo 1012602 6172409 := bstep (se 2 (by rfl) ⟨2314653, by rfl⟩ : syracuseStep 6172409 = 4629307) B4629307
theorem B1519535 : Blo 1012602 1519535 := bstep (se 1 (by rfl) ⟨1139651, by rfl⟩ : syracuseStep 1519535 = 2279303) B2279303
theorem B1519625 : Blo 1012602 1519625 := bstep (se 2 (by rfl) ⟨569859, by rfl⟩ : syracuseStep 1519625 = 1139719) B1139719
theorem B1519655 : Blo 1012602 1519655 := bstep (se 1 (by rfl) ⟨1139741, by rfl⟩ : syracuseStep 1519655 = 2279483) B2279483
theorem B1519739 : Blo 1012602 1519739 := bstep (se 1 (by rfl) ⟨1139804, by rfl⟩ : syracuseStep 1519739 = 2279609) B2279609
theorem B8237213 : Blo 1012602 8237213 := bstep (se 3 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 8237213 = 3088955) B3088955
theorem B8335523 : Blo 1012602 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B1519865 : Blo 1012602 1519865 := bstep (se 2 (by rfl) ⟨569949, by rfl⟩ : syracuseStep 1519865 = 1139899) B1139899
theorem B3649853 : Blo 1012602 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B1519967 : Blo 1012602 1519967 := bstep (se 1 (by rfl) ⟨1139975, by rfl⟩ : syracuseStep 1519967 = 2279951) B2279951
theorem B3420521 : Blo 1012602 3420521 := bstep (se 2 (by rfl) ⟨1282695, by rfl⟩ : syracuseStep 3420521 = 2565391) B2565391
theorem B1519979 : Blo 1012602 1519979 := bstep (se 1 (by rfl) ⟨1139984, by rfl⟩ : syracuseStep 1519979 = 2279969) B2279969
theorem B7713305 : Blo 1012602 7713305 := bstep (se 2 (by rfl) ⟨2892489, by rfl⟩ : syracuseStep 7713305 = 5784979) B5784979
theorem B2568743 : Blo 1012602 2568743 := bstep (se 1 (by rfl) ⟨1926557, by rfl⟩ : syracuseStep 2568743 = 3853115) B3853115
theorem B1520207 : Blo 1012602 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B2437771 : Blo 1012602 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B1520327 : Blo 1012602 1520327 := bstep (se 1 (by rfl) ⟨1140245, by rfl⟩ : syracuseStep 1520327 = 2280491) B2280491
theorem B17347283 : Blo 1012602 17347283 := bstep (se 1 (by rfl) ⟨13010462, by rfl⟩ : syracuseStep 17347283 = 26020925) B26020925
theorem B4338461 : Blo 1012602 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B1520489 : Blo 1012602 1520489 := bstep (se 2 (by rfl) ⟨570183, by rfl⟩ : syracuseStep 1520489 = 1140367) B1140367
theorem B2569067 : Blo 1012602 2569067 := bstep (se 1 (by rfl) ⟨1926800, by rfl⟩ : syracuseStep 2569067 = 3853601) B3853601
theorem B4109231 : Blo 1012602 4109231 := bstep (se 1 (by rfl) ⟨3081923, by rfl⟩ : syracuseStep 4109231 = 6163847) B6163847
theorem B1520567 : Blo 1012602 1520567 := bstep (se 1 (by rfl) ⟨1140425, by rfl⟩ : syracuseStep 1520567 = 2280851) B2280851
theorem B3421115 : Blo 1012602 3421115 := bstep (se 1 (by rfl) ⟨2565836, by rfl⟩ : syracuseStep 3421115 = 5131673) B5131673
theorem B1520603 : Blo 1012602 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B8795101 : Blo 1012602 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B3847283 : Blo 1012602 3847283 := bstep (se 1 (by rfl) ⟨2885462, by rfl⟩ : syracuseStep 3847283 = 5770925) B5770925
theorem B5780879 : Blo 1012602 5780879 := bstep (se 1 (by rfl) ⟨4335659, by rfl⟩ : syracuseStep 5780879 = 8671319) B8671319
theorem B1521071 : Blo 1012602 1521071 := bstep (se 1 (by rfl) ⟨1140803, by rfl⟩ : syracuseStep 1521071 = 2281607) B2281607
theorem B4339145 : Blo 1012602 4339145 := bstep (se 2 (by rfl) ⟨1627179, by rfl⟩ : syracuseStep 4339145 = 3254359) B3254359
theorem B2569715 : Blo 1012602 2569715 := bstep (se 1 (by rfl) ⟨1927286, by rfl⟩ : syracuseStep 2569715 = 3854573) B3854573
theorem B1521161 : Blo 1012602 1521161 := bstep (se 2 (by rfl) ⟨570435, by rfl⟩ : syracuseStep 1521161 = 1140871) B1140871
theorem B1521191 : Blo 1012602 1521191 := bstep (se 1 (by rfl) ⟨1140893, by rfl⟩ : syracuseStep 1521191 = 2281787) B2281787
theorem B1521275 : Blo 1012602 1521275 := bstep (se 1 (by rfl) ⟨1140956, by rfl⟩ : syracuseStep 1521275 = 2281913) B2281913
theorem B5781131 : Blo 1012602 5781131 := bstep (se 1 (by rfl) ⟨4335848, by rfl⟩ : syracuseStep 5781131 = 8671697) B8671697
theorem B2569927 : Blo 1012602 2569927 := bstep (se 1 (by rfl) ⟨1927445, by rfl⟩ : syracuseStep 2569927 = 3854891) B3854891
theorem B1521401 : Blo 1012602 1521401 := bstep (se 2 (by rfl) ⟨570525, by rfl⟩ : syracuseStep 1521401 = 1141051) B1141051
theorem B1521503 : Blo 1012602 1521503 := bstep (se 1 (by rfl) ⟨1141127, by rfl⟩ : syracuseStep 1521503 = 2282255) B2282255
theorem B1521515 : Blo 1012602 1521515 := bstep (se 1 (by rfl) ⟨1141136, by rfl⟩ : syracuseStep 1521515 = 2282273) B2282273
theorem B4339727 : Blo 1012602 4339727 := bstep (se 1 (by rfl) ⟨3254795, by rfl⟩ : syracuseStep 4339727 = 6509591) B6509591
theorem B5486629 : Blo 1012602 5486629 := bstep (se 4 (by rfl) ⟨514371, by rfl⟩ : syracuseStep 5486629 = 1028743) B1028743
theorem B1521743 : Blo 1012602 1521743 := bstep (se 1 (by rfl) ⟨1141307, by rfl⟩ : syracuseStep 1521743 = 2282615) B2282615
theorem B1521863 : Blo 1012602 1521863 := bstep (se 1 (by rfl) ⟨1141397, by rfl⟩ : syracuseStep 1521863 = 2282795) B2282795
theorem B13383917 : Blo 1012602 13383917 := bstep (se 3 (by rfl) ⟨2509484, by rfl⟩ : syracuseStep 13383917 = 5018969) B5018969
theorem B1522025 : Blo 1012602 1522025 := bstep (se 2 (by rfl) ⟨570759, by rfl⟩ : syracuseStep 1522025 = 1141519) B1141519
theorem B3848573 : Blo 1012602 3848573 := bstep (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) B1443215
theorem B1522103 : Blo 1012602 1522103 := bstep (se 1 (by rfl) ⟨1141577, by rfl⟩ : syracuseStep 1522103 = 2283155) B2283155
theorem B1522139 : Blo 1012602 1522139 := bstep (se 1 (by rfl) ⟨1141604, by rfl⟩ : syracuseStep 1522139 = 2283209) B2283209
theorem B2570849 : Blo 1012602 2570849 := bstep (se 2 (by rfl) ⟨964068, by rfl⟩ : syracuseStep 2570849 = 1928137) B1928137
theorem B3422843 : Blo 1012602 3422843 := bstep (se 1 (by rfl) ⟨2567132, by rfl⟩ : syracuseStep 3422843 = 5134265) B5134265
theorem B55589561 : Blo 1012602 55589561 := bstep (se 2 (by rfl) ⟨20846085, by rfl⟩ : syracuseStep 55589561 = 41692171) B41692171
theorem B3423005 : Blo 1012602 3423005 := bstep (se 3 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 3423005 = 1283627) B1283627
theorem B5487389 : Blo 1012602 5487389 := bstep (se 3 (by rfl) ⟨1028885, by rfl⟩ : syracuseStep 5487389 = 2057771) B2057771
theorem B4111211 : Blo 1012602 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B1522607 : Blo 1012602 1522607 := bstep (se 1 (by rfl) ⟨1141955, by rfl⟩ : syracuseStep 1522607 = 2283911) B2283911
theorem B1522697 : Blo 1012602 1522697 := bstep (se 2 (by rfl) ⟨571011, by rfl⟩ : syracuseStep 1522697 = 1142023) B1142023
theorem B1522727 : Blo 1012602 1522727 := bstep (se 1 (by rfl) ⟨1142045, by rfl⟩ : syracuseStep 1522727 = 2284091) B2284091
theorem B1522811 : Blo 1012602 1522811 := bstep (se 1 (by rfl) ⟨1142108, by rfl⟩ : syracuseStep 1522811 = 2284217) B2284217
theorem B1522937 : Blo 1012602 1522937 := bstep (se 2 (by rfl) ⟨571101, by rfl⟩ : syracuseStep 1522937 = 1142203) B1142203
theorem B13909265 : Blo 1012602 13909265 := bstep (se 2 (by rfl) ⟨5215974, by rfl⟩ : syracuseStep 13909265 = 10431949) B10431949
theorem B1523039 : Blo 1012602 1523039 := bstep (se 1 (by rfl) ⟨1142279, by rfl⟩ : syracuseStep 1523039 = 2284559) B2284559
theorem B1523051 : Blo 1012602 1523051 := bstep (se 1 (by rfl) ⟨1142288, by rfl⟩ : syracuseStep 1523051 = 2284577) B2284577
theorem B7716221 : Blo 1012602 7716221 := bstep (se 3 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 7716221 = 2893583) B2893583
theorem B3423707 : Blo 1012602 3423707 := bstep (se 1 (by rfl) ⟨2567780, by rfl⟩ : syracuseStep 3423707 = 5135561) B5135561
theorem B1523279 : Blo 1012602 1523279 := bstep (se 1 (by rfl) ⟨1142459, by rfl⟩ : syracuseStep 1523279 = 2284919) B2284919
theorem B1523399 : Blo 1012602 1523399 := bstep (se 1 (by rfl) ⟨1142549, by rfl⟩ : syracuseStep 1523399 = 2285099) B2285099
theorem B1949395 : Blo 1012602 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B5783339 : Blo 1012602 5783339 := bstep (se 1 (by rfl) ⟨4337504, by rfl⟩ : syracuseStep 5783339 = 8675009) B8675009
theorem B6504259 : Blo 1012602 6504259 := bstep (se 1 (by rfl) ⟨4878194, by rfl⟩ : syracuseStep 6504259 = 9756389) B9756389
theorem B1523561 : Blo 1012602 1523561 := bstep (se 2 (by rfl) ⟨571335, by rfl⟩ : syracuseStep 1523561 = 1142671) B1142671
theorem B21938039 : Blo 1012602 21938039 := bstep (se 1 (by rfl) ⟨16453529, by rfl⟩ : syracuseStep 21938039 = 32907059) B32907059
theorem B1523639 : Blo 1012602 1523639 := bstep (se 1 (by rfl) ⟨1142729, by rfl⟩ : syracuseStep 1523639 = 2285459) B2285459
theorem B1523675 : Blo 1012602 1523675 := bstep (se 1 (by rfl) ⟨1142756, by rfl⟩ : syracuseStep 1523675 = 2285513) B2285513
theorem B2572307 : Blo 1012602 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B3424409 : Blo 1012602 3424409 := bstep (se 2 (by rfl) ⟨1284153, by rfl⟩ : syracuseStep 3424409 = 2568307) B2568307
theorem B3850487 : Blo 1012602 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B2081119 : Blo 1012602 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B1524143 : Blo 1012602 1524143 := bstep (se 1 (by rfl) ⟨1143107, by rfl⟩ : syracuseStep 1524143 = 2286215) B2286215
theorem B1524233 : Blo 1012602 1524233 := bstep (se 2 (by rfl) ⟨571587, by rfl⟩ : syracuseStep 1524233 = 1143175) B1143175
theorem B1622567 : Blo 1012602 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B1524263 : Blo 1012602 1524263 := bstep (se 1 (by rfl) ⟨1143197, by rfl⟩ : syracuseStep 1524263 = 2286395) B2286395
theorem B1524347 : Blo 1012602 1524347 := bstep (se 1 (by rfl) ⟨1143260, by rfl⟩ : syracuseStep 1524347 = 2286521) B2286521
theorem B1524473 : Blo 1012602 1524473 := bstep (se 2 (by rfl) ⟨571677, by rfl⟩ : syracuseStep 1524473 = 1143355) B1143355
theorem B7324445 : Blo 1012602 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B3654467 : Blo 1012602 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B1524575 : Blo 1012602 1524575 := bstep (se 1 (by rfl) ⟨1143431, by rfl⟩ : syracuseStep 1524575 = 2286863) B2286863
theorem B1524587 : Blo 1012602 1524587 := bstep (se 1 (by rfl) ⟨1143440, by rfl⟩ : syracuseStep 1524587 = 2286881) B2286881
theorem B2442145 : Blo 1012602 2442145 := bstep (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) B1831609
theorem B1623079 : Blo 1012602 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B4867123 : Blo 1012602 4867123 := bstep (se 1 (by rfl) ⟨3650342, by rfl⟩ : syracuseStep 4867123 = 7300685) B7300685
theorem B2278457 : Blo 1012602 2278457 := bstep (se 2 (by rfl) ⟨854421, by rfl⟩ : syracuseStep 2278457 = 1708843) B1708843
theorem B1524815 : Blo 1012602 1524815 := bstep (se 1 (by rfl) ⟨1143611, by rfl⟩ : syracuseStep 1524815 = 2287223) B2287223
theorem B3851459 : Blo 1012602 3851459 := bstep (se 1 (by rfl) ⟨2888594, by rfl⟩ : syracuseStep 3851459 = 5777189) B5777189
theorem B3425597 : Blo 1012602 3425597 := bstep (se 3 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 3425597 = 1284599) B1284599
theorem B2278799 : Blo 1012602 2278799 := bstep (se 1 (by rfl) ⟨1709099, by rfl⟩ : syracuseStep 2278799 = 3418199) B3418199
theorem B3851975 : Blo 1012602 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B2279123 : Blo 1012602 2279123 := bstep (se 1 (by rfl) ⟨1709342, by rfl⟩ : syracuseStep 2279123 = 3418685) B3418685
theorem B5785505 : Blo 1012602 5785505 := bstep (se 2 (by rfl) ⟨2169564, by rfl⟩ : syracuseStep 5785505 = 4339129) B4339129
theorem B3426461 : Blo 1012602 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B341821745 : Blo 1012602 341821745 := bstep (se 2 (by rfl) ⟨128183154, by rfl⟩ : syracuseStep 341821745 = 256366309) B256366309
theorem B1624463 : Blo 1012602 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B29641139 : Blo 1012602 29641139 := bstep (se 1 (by rfl) ⟨22230854, by rfl⟩ : syracuseStep 29641139 = 44461709) B44461709
theorem B4934153 : Blo 1012602 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B2280059 : Blo 1012602 2280059 := bstep (se 1 (by rfl) ⟨1710044, by rfl⟩ : syracuseStep 2280059 = 3420089) B3420089
theorem B3852947 : Blo 1012602 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B3427001 : Blo 1012602 3427001 := bstep (se 2 (by rfl) ⟨1285125, by rfl⟩ : syracuseStep 3427001 = 2570251) B2570251
theorem B2280185 : Blo 1012602 2280185 := bstep (se 2 (by rfl) ⟨855069, by rfl⟩ : syracuseStep 2280185 = 1710139) B1710139
theorem B3853129 : Blo 1012602 3853129 := bstep (se 2 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 3853129 = 2889847) B2889847
theorem B36162449 : Blo 1012602 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B2280455 : Blo 1012602 2280455 := bstep (se 1 (by rfl) ⟨1710341, by rfl⟩ : syracuseStep 2280455 = 3420683) B3420683
theorem B2280527 : Blo 1012602 2280527 := bstep (se 1 (by rfl) ⟨1710395, by rfl⟩ : syracuseStep 2280527 = 3420791) B3420791
theorem B5491907 : Blo 1012602 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B5131511 : Blo 1012602 5131511 := bstep (se 1 (by rfl) ⟨3848633, by rfl⟩ : syracuseStep 5131511 = 7697267) B7697267
theorem B3427595 : Blo 1012602 3427595 := bstep (se 1 (by rfl) ⟨2570696, by rfl⟩ : syracuseStep 3427595 = 5141393) B5141393
theorem B2280923 : Blo 1012602 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B3427865 : Blo 1012602 3427865 := bstep (se 2 (by rfl) ⟨1285449, by rfl⟩ : syracuseStep 3427865 = 2570899) B2570899
theorem B5492423 : Blo 1012602 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B5131997 : Blo 1012602 5131997 := bstep (se 3 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 5131997 = 1924499) B1924499
theorem B3657581 : Blo 1012602 3657581 := bstep (se 3 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 3657581 = 1371593) B1371593
theorem B2281391 : Blo 1012602 2281391 := bstep (se 1 (by rfl) ⟨1711043, by rfl⟩ : syracuseStep 2281391 = 3422087) B3422087
theorem B3559355 : Blo 1012602 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B3657809 : Blo 1012602 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B2281643 : Blo 1012602 2281643 := bstep (se 1 (by rfl) ⟨1711232, by rfl⟩ : syracuseStep 2281643 = 3422465) B3422465
theorem B1626475 : Blo 1012602 1626475 := bstep (se 1 (by rfl) ⟨1219856, by rfl⟩ : syracuseStep 1626475 = 2439713) B2439713
theorem B5788169 : Blo 1012602 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B3428999 : Blo 1012602 3428999 := bstep (se 1 (by rfl) ⟨2571749, by rfl⟩ : syracuseStep 3428999 = 5143499) B5143499
theorem B8213177 : Blo 1012602 8213177 := bstep (se 2 (by rfl) ⟨3079941, by rfl⟩ : syracuseStep 8213177 = 6159883) B6159883
theorem B3429053 : Blo 1012602 3429053 := bstep (se 3 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 3429053 = 1285895) B1285895
theorem B2282183 : Blo 1012602 2282183 := bstep (se 1 (by rfl) ⟨1711637, by rfl⟩ : syracuseStep 2282183 = 3423275) B3423275
theorem B24728273 : Blo 1012602 24728273 := bstep (se 2 (by rfl) ⟨9273102, by rfl⟩ : syracuseStep 24728273 = 18546205) B18546205
theorem B3855059 : Blo 1012602 3855059 := bstep (se 1 (by rfl) ⟨2891294, by rfl⟩ : syracuseStep 3855059 = 5782589) B5782589
theorem B14635849 : Blo 1012602 14635849 := bstep (se 2 (by rfl) ⟨5488443, by rfl⟩ : syracuseStep 14635849 = 10976887) B10976887
theorem B3429215 : Blo 1012602 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B3429377 : Blo 1012602 3429377 := bstep (se 2 (by rfl) ⟨1286016, by rfl⟩ : syracuseStep 3429377 = 2572033) B2572033
theorem B5789171 : Blo 1012602 5789171 := bstep (se 1 (by rfl) ⟨4341878, by rfl⟩ : syracuseStep 5789171 = 8683757) B8683757
theorem B2283047 : Blo 1012602 2283047 := bstep (se 1 (by rfl) ⟨1712285, by rfl⟩ : syracuseStep 2283047 = 3424571) B3424571
theorem B1627705 : Blo 1012602 1627705 := bstep (se 2 (by rfl) ⟨610389, by rfl⟩ : syracuseStep 1627705 = 1220779) B1220779
theorem B7689977 : Blo 1012602 7689977 := bstep (se 2 (by rfl) ⟨2883741, by rfl⟩ : syracuseStep 7689977 = 5767483) B5767483
theorem B3430187 : Blo 1012602 3430187 := bstep (se 1 (by rfl) ⟨2572640, by rfl⟩ : syracuseStep 3430187 = 5145281) B5145281
theorem B2283371 : Blo 1012602 2283371 := bstep (se 1 (by rfl) ⟨1712528, by rfl⟩ : syracuseStep 2283371 = 3425057) B3425057
theorem B16897901 : Blo 1012602 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B2283425 : Blo 1012602 2283425 := bstep (se 2 (by rfl) ⟨856284, by rfl⟩ : syracuseStep 2283425 = 1712569) B1712569
theorem B2742191 : Blo 1012602 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B5789627 : Blo 1012602 5789627 := bstep (se 1 (by rfl) ⟨4342220, by rfl⟩ : syracuseStep 5789627 = 8684441) B8684441
theorem B3430457 : Blo 1012602 3430457 := bstep (se 2 (by rfl) ⟨1286421, by rfl⟩ : syracuseStep 3430457 = 2572843) B2572843
theorem B2283767 : Blo 1012602 2283767 := bstep (se 1 (by rfl) ⟨1712825, by rfl⟩ : syracuseStep 2283767 = 3425651) B3425651
theorem B9394481 : Blo 1012602 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B3430781 : Blo 1012602 3430781 := bstep (se 3 (by rfl) ⟨643271, by rfl⟩ : syracuseStep 3430781 = 1286543) B1286543
theorem B24697223 : Blo 1012602 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B1465031 : Blo 1012602 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B2284361 : Blo 1012602 2284361 := bstep (se 2 (by rfl) ⟨856635, by rfl⟩ : syracuseStep 2284361 = 1713271) B1713271
theorem B1923983 : Blo 1012602 1923983 := bstep (se 1 (by rfl) ⟨1442987, by rfl⟩ : syracuseStep 1923983 = 2885975) B2885975
theorem B6511589 : Blo 1012602 6511589 := bstep (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) B1220923
theorem B7527397 : Blo 1012602 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B1825849 : Blo 1012602 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B3857489 : Blo 1012602 3857489 := bstep (se 2 (by rfl) ⟨1446558, by rfl⟩ : syracuseStep 3857489 = 2893117) B2893117
theorem B7691435 : Blo 1012602 7691435 := bstep (se 1 (by rfl) ⟨5768576, by rfl⟩ : syracuseStep 7691435 = 11537153) B11537153
theorem B9264527 : Blo 1012602 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B3857807 : Blo 1012602 3857807 := bstep (se 1 (by rfl) ⟨2893355, by rfl⟩ : syracuseStep 3857807 = 5786711) B5786711
theorem B1170983 : Blo 1012602 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B2285153 : Blo 1012602 2285153 := bstep (se 2 (by rfl) ⟨856932, by rfl⟩ : syracuseStep 2285153 = 1713865) B1713865
theorem B7691921 : Blo 1012602 7691921 := bstep (se 2 (by rfl) ⟨2884470, by rfl⟩ : syracuseStep 7691921 = 5768941) B5768941
theorem B4873927 : Blo 1012602 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B1925039 : Blo 1012602 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B2285495 : Blo 1012602 2285495 := bstep (se 1 (by rfl) ⟨1714121, by rfl⟩ : syracuseStep 2285495 = 3428243) B3428243
theorem B31252493 : Blo 1012602 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B18767933 : Blo 1012602 18767933 := bstep (se 3 (by rfl) ⟨3518987, by rfl⟩ : syracuseStep 18767933 = 7037975) B7037975
theorem B3858749 : Blo 1012602 3858749 := bstep (se 3 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 3858749 = 1447031) B1447031
theorem B1925471 : Blo 1012602 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B2744819 : Blo 1012602 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2286089 : Blo 1012602 2286089 := bstep (se 2 (by rfl) ⟨857283, by rfl⟩ : syracuseStep 2286089 = 1714567) B1714567
theorem B1139323 : Blo 1012602 1139323 := bstep (se 1 (by rfl) ⟨854492, by rfl⟩ : syracuseStep 1139323 = 1708985) B1708985
theorem B2777723 : Blo 1012602 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B2056951 : Blo 1012602 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B5137181 : Blo 1012602 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B2286431 : Blo 1012602 2286431 := bstep (se 1 (by rfl) ⟨1714823, by rfl⟩ : syracuseStep 2286431 = 3429647) B3429647
theorem B28173205 : Blo 1012602 28173205 := bstep (se 6 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 28173205 = 1320619) B1320619
theorem B2286611 : Blo 1012602 2286611 := bstep (se 1 (by rfl) ⟨1714958, by rfl⟩ : syracuseStep 2286611 = 3429917) B3429917
theorem B7693379 : Blo 1012602 7693379 := bstep (se 1 (by rfl) ⟨5770034, by rfl⟩ : syracuseStep 7693379 = 11540069) B11540069
theorem B1139791 : Blo 1012602 1139791 := bstep (se 1 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 1139791 = 1709687) B1709687
theorem B2286953 : Blo 1012602 2286953 := bstep (se 2 (by rfl) ⟨857607, by rfl⟩ : syracuseStep 2286953 = 1715215) B1715215
theorem B1828271 : Blo 1012602 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B1140187 : Blo 1012602 1140187 := bstep (se 1 (by rfl) ⟨855140, by rfl⟩ : syracuseStep 1140187 = 1710281) B1710281
theorem B1140655 : Blo 1012602 1140655 := bstep (se 1 (by rfl) ⟨855491, by rfl⟩ : syracuseStep 1140655 = 1710983) B1710983
theorem B7694351 : Blo 1012602 7694351 := bstep (se 1 (by rfl) ⟨5770763, by rfl⟩ : syracuseStep 7694351 = 11541527) B11541527
theorem B1927415 : Blo 1012602 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B1141087 : Blo 1012602 1141087 := bstep (se 1 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 1141087 = 1711631) B1711631
theorem B1927567 : Blo 1012602 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B1141447 : Blo 1012602 1141447 := bstep (se 1 (by rfl) ⟨856085, by rfl⟩ : syracuseStep 1141447 = 1712171) B1712171
theorem B2780087 : Blo 1012602 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B3435527 : Blo 1012602 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B13888685 : Blo 1012602 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B1928441 : Blo 1012602 1928441 := bstep (se 2 (by rfl) ⟨723165, by rfl⟩ : syracuseStep 1928441 = 1446331) B1446331
theorem B2747791 : Blo 1012602 2747791 := bstep (se 1 (by rfl) ⟨2060843, by rfl⟩ : syracuseStep 2747791 = 4121687) B4121687
theorem B1928623 : Blo 1012602 1928623 := bstep (se 1 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 1928623 = 2892935) B2892935
theorem B1142311 : Blo 1012602 1142311 := bstep (se 1 (by rfl) ⟨856733, by rfl⟩ : syracuseStep 1142311 = 1713467) B1713467
theorem B17329787 : Blo 1012602 17329787 := bstep (se 1 (by rfl) ⟨12997340, by rfl⟩ : syracuseStep 17329787 = 25994681) B25994681
theorem B14839517 : Blo 1012602 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B7303283 : Blo 1012602 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B1929899 : Blo 1012602 1929899 := bstep (se 1 (by rfl) ⟨1447424, by rfl⟩ : syracuseStep 1929899 = 2894849) B2894849
theorem B1012603 : Blo 1012602 1012603 := bstep (se 1 (by rfl) ⟨759452, by rfl⟩ : syracuseStep 1012603 = 1518905) B1518905
theorem B1012655 : Blo 1012602 1012655 := bstep (se 1 (by rfl) ⟨759491, by rfl⟩ : syracuseStep 1012655 = 1518983) B1518983
theorem B1012679 : Blo 1012602 1012679 := bstep (se 1 (by rfl) ⟨759509, by rfl⟩ : syracuseStep 1012679 = 1519019) B1519019
theorem B1012699 : Blo 1012602 1012699 := bstep (se 1 (by rfl) ⟨759524, by rfl⟩ : syracuseStep 1012699 = 1519049) B1519049
theorem B1012775 : Blo 1012602 1012775 := bstep (se 1 (by rfl) ⟨759581, by rfl⟩ : syracuseStep 1012775 = 1519163) B1519163
theorem B1733671 : Blo 1012602 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B5141555 : Blo 1012602 5141555 := bstep (se 1 (by rfl) ⟨3856166, by rfl⟩ : syracuseStep 5141555 = 7712333) B7712333
theorem B1012815 : Blo 1012602 1012815 := bstep (se 1 (by rfl) ⟨759611, by rfl⟩ : syracuseStep 1012815 = 1519223) B1519223
theorem B1012831 : Blo 1012602 1012831 := bstep (se 1 (by rfl) ⟨759623, by rfl⟩ : syracuseStep 1012831 = 1519247) B1519247
theorem B1012859 : Blo 1012602 1012859 := bstep (se 1 (by rfl) ⟨759644, by rfl⟩ : syracuseStep 1012859 = 1519289) B1519289
theorem B1012911 : Blo 1012602 1012911 := bstep (se 1 (by rfl) ⟨759683, by rfl⟩ : syracuseStep 1012911 = 1519367) B1519367
theorem B1012935 : Blo 1012602 1012935 := bstep (se 1 (by rfl) ⟨759701, by rfl⟩ : syracuseStep 1012935 = 1519403) B1519403
theorem B1012955 : Blo 1012602 1012955 := bstep (se 1 (by rfl) ⟨759716, by rfl⟩ : syracuseStep 1012955 = 1519433) B1519433
theorem B1013031 : Blo 1012602 1013031 := bstep (se 1 (by rfl) ⟨759773, by rfl⟩ : syracuseStep 1013031 = 1519547) B1519547
theorem B1013071 : Blo 1012602 1013071 := bstep (se 1 (by rfl) ⟨759803, by rfl⟩ : syracuseStep 1013071 = 1519607) B1519607
theorem B7697753 : Blo 1012602 7697753 := bstep (se 2 (by rfl) ⟨2886657, by rfl⟩ : syracuseStep 7697753 = 5773315) B5773315
theorem B1013087 : Blo 1012602 1013087 := bstep (se 1 (by rfl) ⟨759815, by rfl⟩ : syracuseStep 1013087 = 1519631) B1519631
theorem B1013115 : Blo 1012602 1013115 := bstep (se 1 (by rfl) ⟨759836, by rfl⟩ : syracuseStep 1013115 = 1519673) B1519673
theorem B1013167 : Blo 1012602 1013167 := bstep (se 1 (by rfl) ⟨759875, by rfl⟩ : syracuseStep 1013167 = 1519751) B1519751
theorem B1013191 : Blo 1012602 1013191 := bstep (se 1 (by rfl) ⟨759893, by rfl⟩ : syracuseStep 1013191 = 1519787) B1519787
theorem B1013211 : Blo 1012602 1013211 := bstep (se 1 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 1013211 = 1519817) B1519817
theorem B1013287 : Blo 1012602 1013287 := bstep (se 1 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 1013287 = 1519931) B1519931
theorem B1013327 : Blo 1012602 1013327 := bstep (se 1 (by rfl) ⟨759995, by rfl⟩ : syracuseStep 1013327 = 1519991) B1519991
theorem B1013343 : Blo 1012602 1013343 := bstep (se 1 (by rfl) ⟨760007, by rfl⟩ : syracuseStep 1013343 = 1520015) B1520015
theorem B1013371 : Blo 1012602 1013371 := bstep (se 1 (by rfl) ⟨760028, by rfl⟩ : syracuseStep 1013371 = 1520057) B1520057
theorem B1013423 : Blo 1012602 1013423 := bstep (se 1 (by rfl) ⟨760067, by rfl⟩ : syracuseStep 1013423 = 1520135) B1520135
theorem B1013447 : Blo 1012602 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B1013467 : Blo 1012602 1013467 := bstep (se 1 (by rfl) ⟨760100, by rfl⟩ : syracuseStep 1013467 = 1520201) B1520201
theorem B1013543 : Blo 1012602 1013543 := bstep (se 1 (by rfl) ⟨760157, by rfl⟩ : syracuseStep 1013543 = 1520315) B1520315
theorem B17364779 : Blo 1012602 17364779 := bstep (se 1 (by rfl) ⟨13023584, by rfl⟩ : syracuseStep 17364779 = 26047169) B26047169
theorem B1013583 : Blo 1012602 1013583 := bstep (se 1 (by rfl) ⟨760187, by rfl⟩ : syracuseStep 1013583 = 1520375) B1520375
theorem B1013599 : Blo 1012602 1013599 := bstep (se 1 (by rfl) ⟨760199, by rfl⟩ : syracuseStep 1013599 = 1520399) B1520399
theorem B1013627 : Blo 1012602 1013627 := bstep (se 1 (by rfl) ⟨760220, by rfl⟩ : syracuseStep 1013627 = 1520441) B1520441
theorem B1013679 : Blo 1012602 1013679 := bstep (se 1 (by rfl) ⟨760259, by rfl⟩ : syracuseStep 1013679 = 1520519) B1520519
theorem B1013703 : Blo 1012602 1013703 := bstep (se 1 (by rfl) ⟨760277, by rfl⟩ : syracuseStep 1013703 = 1520555) B1520555
theorem B1013723 : Blo 1012602 1013723 := bstep (se 1 (by rfl) ⟨760292, by rfl⟩ : syracuseStep 1013723 = 1520585) B1520585
theorem B1013799 : Blo 1012602 1013799 := bstep (se 1 (by rfl) ⟨760349, by rfl⟩ : syracuseStep 1013799 = 1520699) B1520699
theorem B1013839 : Blo 1012602 1013839 := bstep (se 1 (by rfl) ⟨760379, by rfl⟩ : syracuseStep 1013839 = 1520759) B1520759
theorem B1013855 : Blo 1012602 1013855 := bstep (se 1 (by rfl) ⟨760391, by rfl⟩ : syracuseStep 1013855 = 1520783) B1520783
theorem B1013883 : Blo 1012602 1013883 := bstep (se 1 (by rfl) ⟨760412, by rfl⟩ : syracuseStep 1013883 = 1520825) B1520825
theorem B1013935 : Blo 1012602 1013935 := bstep (se 1 (by rfl) ⟨760451, by rfl⟩ : syracuseStep 1013935 = 1520903) B1520903
theorem B1013959 : Blo 1012602 1013959 := bstep (se 1 (by rfl) ⟨760469, by rfl⟩ : syracuseStep 1013959 = 1520939) B1520939
theorem B1013979 : Blo 1012602 1013979 := bstep (se 1 (by rfl) ⟨760484, by rfl⟩ : syracuseStep 1013979 = 1520969) B1520969
theorem B1014055 : Blo 1012602 1014055 := bstep (se 1 (by rfl) ⟨760541, by rfl⟩ : syracuseStep 1014055 = 1521083) B1521083
theorem B1014095 : Blo 1012602 1014095 := bstep (se 1 (by rfl) ⟨760571, by rfl⟩ : syracuseStep 1014095 = 1521143) B1521143
theorem B1014111 : Blo 1012602 1014111 := bstep (se 1 (by rfl) ⟨760583, by rfl⟩ : syracuseStep 1014111 = 1521167) B1521167
theorem B11106665 : Blo 1012602 11106665 := bstep (se 2 (by rfl) ⟨4164999, by rfl⟩ : syracuseStep 11106665 = 8329999) B8329999
theorem B1014139 : Blo 1012602 1014139 := bstep (se 1 (by rfl) ⟨760604, by rfl⟩ : syracuseStep 1014139 = 1521209) B1521209
theorem B1014191 : Blo 1012602 1014191 := bstep (se 1 (by rfl) ⟨760643, by rfl⟩ : syracuseStep 1014191 = 1521287) B1521287
theorem B1014215 : Blo 1012602 1014215 := bstep (se 1 (by rfl) ⟨760661, by rfl⟩ : syracuseStep 1014215 = 1521323) B1521323
theorem B1014235 : Blo 1012602 1014235 := bstep (se 1 (by rfl) ⟨760676, by rfl⟩ : syracuseStep 1014235 = 1521353) B1521353
theorem B1014311 : Blo 1012602 1014311 := bstep (se 1 (by rfl) ⟨760733, by rfl⟩ : syracuseStep 1014311 = 1521467) B1521467
theorem B1014351 : Blo 1012602 1014351 := bstep (se 1 (by rfl) ⟨760763, by rfl⟩ : syracuseStep 1014351 = 1521527) B1521527
theorem B1014367 : Blo 1012602 1014367 := bstep (se 1 (by rfl) ⟨760775, by rfl⟩ : syracuseStep 1014367 = 1521551) B1521551
theorem B1014395 : Blo 1012602 1014395 := bstep (se 1 (by rfl) ⟨760796, by rfl⟩ : syracuseStep 1014395 = 1521593) B1521593
theorem B5143175 : Blo 1012602 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B1014447 : Blo 1012602 1014447 := bstep (se 1 (by rfl) ⟨760835, by rfl⟩ : syracuseStep 1014447 = 1521671) B1521671
theorem B1014471 : Blo 1012602 1014471 := bstep (se 1 (by rfl) ⟨760853, by rfl⟩ : syracuseStep 1014471 = 1521707) B1521707
theorem B1014491 : Blo 1012602 1014491 := bstep (se 1 (by rfl) ⟨760868, by rfl⟩ : syracuseStep 1014491 = 1521737) B1521737
theorem B1014567 : Blo 1012602 1014567 := bstep (se 1 (by rfl) ⟨760925, by rfl⟩ : syracuseStep 1014567 = 1521851) B1521851
theorem B1014607 : Blo 1012602 1014607 := bstep (se 1 (by rfl) ⟨760955, by rfl⟩ : syracuseStep 1014607 = 1521911) B1521911
theorem B1014623 : Blo 1012602 1014623 := bstep (se 1 (by rfl) ⟨760967, by rfl⟩ : syracuseStep 1014623 = 1521935) B1521935
theorem B1014651 : Blo 1012602 1014651 := bstep (se 1 (by rfl) ⟨760988, by rfl⟩ : syracuseStep 1014651 = 1521977) B1521977
theorem B1014703 : Blo 1012602 1014703 := bstep (se 1 (by rfl) ⟨761027, by rfl⟩ : syracuseStep 1014703 = 1522055) B1522055
theorem B1014727 : Blo 1012602 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B1014747 : Blo 1012602 1014747 := bstep (se 1 (by rfl) ⟨761060, by rfl⟩ : syracuseStep 1014747 = 1522121) B1522121
theorem B1014823 : Blo 1012602 1014823 := bstep (se 1 (by rfl) ⟨761117, by rfl⟩ : syracuseStep 1014823 = 1522235) B1522235
theorem B1014863 : Blo 1012602 1014863 := bstep (se 1 (by rfl) ⟨761147, by rfl⟩ : syracuseStep 1014863 = 1522295) B1522295
theorem B1014879 : Blo 1012602 1014879 := bstep (se 1 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 1014879 = 1522319) B1522319
theorem B1014907 : Blo 1012602 1014907 := bstep (se 1 (by rfl) ⟨761180, by rfl⟩ : syracuseStep 1014907 = 1522361) B1522361
theorem B1014959 : Blo 1012602 1014959 := bstep (se 1 (by rfl) ⟨761219, by rfl⟩ : syracuseStep 1014959 = 1522439) B1522439
theorem B1014983 : Blo 1012602 1014983 := bstep (se 1 (by rfl) ⟨761237, by rfl⟩ : syracuseStep 1014983 = 1522475) B1522475
theorem B1015003 : Blo 1012602 1015003 := bstep (se 1 (by rfl) ⟨761252, by rfl⟩ : syracuseStep 1015003 = 1522505) B1522505
theorem B1015079 : Blo 1012602 1015079 := bstep (se 1 (by rfl) ⟨761309, by rfl⟩ : syracuseStep 1015079 = 1522619) B1522619
theorem B1015119 : Blo 1012602 1015119 := bstep (se 1 (by rfl) ⟨761339, by rfl⟩ : syracuseStep 1015119 = 1522679) B1522679
theorem B1015135 : Blo 1012602 1015135 := bstep (se 1 (by rfl) ⟨761351, by rfl⟩ : syracuseStep 1015135 = 1522703) B1522703
theorem B1015163 : Blo 1012602 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B1015215 : Blo 1012602 1015215 := bstep (se 1 (by rfl) ⟨761411, by rfl⟩ : syracuseStep 1015215 = 1522823) B1522823
theorem B1015239 : Blo 1012602 1015239 := bstep (se 1 (by rfl) ⟨761429, by rfl⟩ : syracuseStep 1015239 = 1522859) B1522859
theorem B1015259 : Blo 1012602 1015259 := bstep (se 1 (by rfl) ⟨761444, by rfl⟩ : syracuseStep 1015259 = 1522889) B1522889
theorem B36961757 : Blo 1012602 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B1015335 : Blo 1012602 1015335 := bstep (se 1 (by rfl) ⟨761501, by rfl⟩ : syracuseStep 1015335 = 1523003) B1523003
theorem B1015375 : Blo 1012602 1015375 := bstep (se 1 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 1015375 = 1523063) B1523063
theorem B1015391 : Blo 1012602 1015391 := bstep (se 1 (by rfl) ⟨761543, by rfl⟩ : syracuseStep 1015391 = 1523087) B1523087
theorem B1015419 : Blo 1012602 1015419 := bstep (se 1 (by rfl) ⟨761564, by rfl⟩ : syracuseStep 1015419 = 1523129) B1523129
theorem B1015471 : Blo 1012602 1015471 := bstep (se 1 (by rfl) ⟨761603, by rfl⟩ : syracuseStep 1015471 = 1523207) B1523207
theorem B1015495 : Blo 1012602 1015495 := bstep (se 1 (by rfl) ⟨761621, by rfl⟩ : syracuseStep 1015495 = 1523243) B1523243
theorem B7700183 : Blo 1012602 7700183 := bstep (se 1 (by rfl) ⟨5775137, by rfl⟩ : syracuseStep 7700183 = 11550275) B11550275
theorem B1015515 : Blo 1012602 1015515 := bstep (se 1 (by rfl) ⟨761636, by rfl⟩ : syracuseStep 1015515 = 1523273) B1523273
theorem B8781533 : Blo 1012602 8781533 := bstep (se 3 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 8781533 = 3293075) B3293075
theorem B1015591 : Blo 1012602 1015591 := bstep (se 1 (by rfl) ⟨761693, by rfl⟩ : syracuseStep 1015591 = 1523387) B1523387
theorem B1015631 : Blo 1012602 1015631 := bstep (se 1 (by rfl) ⟨761723, by rfl⟩ : syracuseStep 1015631 = 1523447) B1523447
theorem B1015647 : Blo 1012602 1015647 := bstep (se 1 (by rfl) ⟨761735, by rfl⟩ : syracuseStep 1015647 = 1523471) B1523471
theorem B1015675 : Blo 1012602 1015675 := bstep (se 1 (by rfl) ⟨761756, by rfl⟩ : syracuseStep 1015675 = 1523513) B1523513
theorem B1015727 : Blo 1012602 1015727 := bstep (se 1 (by rfl) ⟨761795, by rfl⟩ : syracuseStep 1015727 = 1523591) B1523591
theorem B1015751 : Blo 1012602 1015751 := bstep (se 1 (by rfl) ⟨761813, by rfl⟩ : syracuseStep 1015751 = 1523627) B1523627
theorem B1015771 : Blo 1012602 1015771 := bstep (se 1 (by rfl) ⟨761828, by rfl⟩ : syracuseStep 1015771 = 1523657) B1523657
theorem B1016095 : Blo 1012602 1016095 := bstep (se 1 (by rfl) ⟨762071, by rfl⟩ : syracuseStep 1016095 = 1524143) B1524143
theorem B1016155 : Blo 1012602 1016155 := bstep (se 1 (by rfl) ⟨762116, by rfl⟩ : syracuseStep 1016155 = 1524233) B1524233
theorem B1081711 : Blo 1012602 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B1016175 : Blo 1012602 1016175 := bstep (se 1 (by rfl) ⟨762131, by rfl⟩ : syracuseStep 1016175 = 1524263) B1524263
theorem B58458509 : Blo 1012602 58458509 := bstep (se 3 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 58458509 = 21921941) B21921941
theorem B1016231 : Blo 1012602 1016231 := bstep (se 1 (by rfl) ⟨762173, by rfl⟩ : syracuseStep 1016231 = 1524347) B1524347
theorem B2884015 : Blo 1012602 2884015 := bstep (se 1 (by rfl) ⟨2163011, by rfl⟩ : syracuseStep 2884015 = 4326023) B4326023
theorem B1016315 : Blo 1012602 1016315 := bstep (se 1 (by rfl) ⟨762236, by rfl⟩ : syracuseStep 1016315 = 1524473) B1524473
theorem B4882963 : Blo 1012602 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B1016383 : Blo 1012602 1016383 := bstep (se 1 (by rfl) ⟨762287, by rfl⟩ : syracuseStep 1016383 = 1524575) B1524575
theorem B1016391 : Blo 1012602 1016391 := bstep (se 1 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 1016391 = 1524587) B1524587
theorem B1016543 : Blo 1012602 1016543 := bstep (se 1 (by rfl) ⟨762407, by rfl⟩ : syracuseStep 1016543 = 1524815) B1524815
theorem B2164105 : Blo 1012602 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B6489497 : Blo 1012602 6489497 := bstep (se 2 (by rfl) ⟨2433561, by rfl⟩ : syracuseStep 6489497 = 4867123) B4867123
theorem B1082975 : Blo 1012602 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B19760759 : Blo 1012602 19760759 := bstep (se 1 (by rfl) ⟨14820569, by rfl⟩ : syracuseStep 19760759 = 29641139) B29641139
theorem B4392791 : Blo 1012602 4392791 := bstep (se 1 (by rfl) ⟨3294593, by rfl⟩ : syracuseStep 4392791 = 6589187) B6589187
theorem B11569229 : Blo 1012602 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B2165267 : Blo 1012602 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B20810621 : Blo 1012602 20810621 := bstep (se 3 (by rfl) ⟨3901991, by rfl⟩ : syracuseStep 20810621 = 7803983) B7803983
theorem B5475451 : Blo 1012602 5475451 := bstep (se 1 (by rfl) ⟨4106588, by rfl⟩ : syracuseStep 5475451 = 8213177) B8213177
theorem B16485515 : Blo 1012602 16485515 := bstep (se 1 (by rfl) ⟨12364136, by rfl⟩ : syracuseStep 16485515 = 24728273) B24728273
theorem B2166583 : Blo 1012602 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B3248029 : Blo 1012602 3248029 := bstep (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) B1218011
theorem B8654849 : Blo 1012602 8654849 := bstep (se 2 (by rfl) ⟨3245568, by rfl⟩ : syracuseStep 8654849 = 6491137) B6491137
theorem B6492419 : Blo 1012602 6492419 := bstep (se 1 (by rfl) ⟨4869314, by rfl⟩ : syracuseStep 6492419 = 9738629) B9738629
theorem B1282655 : Blo 1012602 1282655 := bstep (se 1 (by rfl) ⟨961991, by rfl⟩ : syracuseStep 1282655 = 1923983) B1923983
theorem B45061069 : Blo 1012602 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B8787001 : Blo 1012602 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B1709275 : Blo 1012602 1709275 := bstep (se 1 (by rfl) ⟨1281956, by rfl⟩ : syracuseStep 1709275 = 2563913) B2563913
theorem B4330739 : Blo 1012602 4330739 := bstep (se 1 (by rfl) ⟨3248054, by rfl⟩ : syracuseStep 4330739 = 6496109) B6496109
theorem B1283359 : Blo 1012602 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B6166327 : Blo 1012602 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B2168633 : Blo 1012602 2168633 := bstep (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) B1626475
theorem B1710031 : Blo 1012602 1710031 := bstep (se 1 (by rfl) ⟨1282523, by rfl⟩ : syracuseStep 1710031 = 2565047) B2565047
theorem B3250361 : Blo 1012602 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B2169299 : Blo 1012602 2169299 := bstep (se 1 (by rfl) ⟨1626974, by rfl⟩ : syracuseStep 2169299 = 3253949) B3253949
theorem B2890235 : Blo 1012602 2890235 := bstep (se 1 (by rfl) ⟨2167676, by rfl⟩ : syracuseStep 2890235 = 4335353) B4335353
theorem B1710713 : Blo 1012602 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B1710767 : Blo 1012602 1710767 := bstep (se 1 (by rfl) ⟨1283075, by rfl⟩ : syracuseStep 1710767 = 2566151) B2566151
theorem B1711003 : Blo 1012602 1711003 := bstep (se 1 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 1711003 = 2566505) B2566505
theorem B2890667 : Blo 1012602 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B3906749 : Blo 1012602 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B1285627 : Blo 1012602 1285627 := bstep (se 1 (by rfl) ⟨964220, by rfl⟩ : syracuseStep 1285627 = 1928441) B1928441
theorem B4333115 : Blo 1012602 4333115 := bstep (se 1 (by rfl) ⟨3249836, by rfl⟩ : syracuseStep 4333115 = 6499673) B6499673
theorem B2563771 : Blo 1012602 2563771 := bstep (se 1 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 2563771 = 3845657) B3845657
theorem B4333267 : Blo 1012602 4333267 := bstep (se 1 (by rfl) ⟨3249950, by rfl⟩ : syracuseStep 4333267 = 6499901) B6499901
theorem B7413565 : Blo 1012602 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B7315505 : Blo 1012602 7315505 := bstep (se 2 (by rfl) ⟨2743314, by rfl⟩ : syracuseStep 7315505 = 5486629) B5486629
theorem B2433235 : Blo 1012602 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B1712495 : Blo 1012602 1712495 := bstep (se 1 (by rfl) ⟨1284371, by rfl⟩ : syracuseStep 1712495 = 2568743) B2568743
theorem B1286599 : Blo 1012602 1286599 := bstep (se 1 (by rfl) ⟨964949, by rfl⟩ : syracuseStep 1286599 = 1929899) B1929899
theorem B11542985 : Blo 1012602 11542985 := bstep (se 2 (by rfl) ⟨4328619, by rfl⟩ : syracuseStep 11542985 = 8657239) B8657239
theorem B1712711 : Blo 1012602 1712711 := bstep (se 1 (by rfl) ⟨1284533, by rfl⟩ : syracuseStep 1712711 = 2569067) B2569067
theorem B2564855 : Blo 1012602 2564855 := bstep (se 1 (by rfl) ⟨1923641, by rfl⟩ : syracuseStep 2564855 = 3847283) B3847283
theorem B2892763 : Blo 1012602 2892763 := bstep (se 1 (by rfl) ⟨2169572, by rfl⟩ : syracuseStep 2892763 = 4339145) B4339145
theorem B1713143 : Blo 1012602 1713143 := bstep (se 1 (by rfl) ⟨1284857, by rfl⟩ : syracuseStep 1713143 = 2569715) B2569715
theorem B11576519 : Blo 1012602 11576519 := bstep (se 1 (by rfl) ⟨8682389, by rfl⟩ : syracuseStep 11576519 = 17364779) B17364779
theorem B10036529 : Blo 1012602 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B2893151 : Blo 1012602 2893151 := bstep (se 1 (by rfl) ⟨2169863, by rfl⟩ : syracuseStep 2893151 = 4339727) B4339727
theorem B2434465 : Blo 1012602 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B3122621 : Blo 1012602 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B8922611 : Blo 1012602 8922611 := bstep (se 1 (by rfl) ⟨6691958, by rfl⟩ : syracuseStep 8922611 = 13383917) B13383917
theorem B2565715 : Blo 1012602 2565715 := bstep (se 1 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 2565715 = 3848573) B3848573
theorem B6170201 : Blo 1012602 6170201 := bstep (se 2 (by rfl) ⟨2313825, by rfl⟩ : syracuseStep 6170201 = 4627651) B4627651
theorem B1713899 : Blo 1012602 1713899 := bstep (se 1 (by rfl) ⟨1285424, by rfl⟩ : syracuseStep 1713899 = 2570849) B2570849
theorem B16459757 : Blo 1012602 16459757 := bstep (se 3 (by rfl) ⟨3086204, by rfl⟩ : syracuseStep 16459757 = 6172409) B6172409
theorem B3418145 : Blo 1012602 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B6498569 : Blo 1012602 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B2599193 : Blo 1012602 2599193 := bstep (se 2 (by rfl) ⟨974697, by rfl⟩ : syracuseStep 2599193 = 1949395) B1949395
theorem B14625359 : Blo 1012602 14625359 := bstep (se 1 (by rfl) ⟨10969019, by rfl⟩ : syracuseStep 14625359 = 21938039) B21938039
theorem B1714871 : Blo 1012602 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B2566991 : Blo 1012602 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B14855183 : Blo 1012602 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B9874547 : Blo 1012602 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B2436311 : Blo 1012602 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B3845339 : Blo 1012602 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B1518971 : Blo 1012602 1518971 := bstep (se 1 (by rfl) ⟨1139228, by rfl⟩ : syracuseStep 1518971 = 2278457) B2278457
theorem B2567639 : Blo 1012602 2567639 := bstep (se 1 (by rfl) ⟨1925729, by rfl⟩ : syracuseStep 2567639 = 3851459) B3851459
theorem B1519097 : Blo 1012602 1519097 := bstep (se 2 (by rfl) ⟨569661, by rfl⟩ : syracuseStep 1519097 = 1139323) B1139323
theorem B1519199 : Blo 1012602 1519199 := bstep (se 1 (by rfl) ⟨1139399, by rfl⟩ : syracuseStep 1519199 = 2278799) B2278799
theorem B2567983 : Blo 1012602 2567983 := bstep (se 1 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 2567983 = 3851975) B3851975
theorem B1519415 : Blo 1012602 1519415 := bstep (se 1 (by rfl) ⟨1139561, by rfl⟩ : syracuseStep 1519415 = 2279123) B2279123
theorem B37564273 : Blo 1012602 37564273 := bstep (se 2 (by rfl) ⟨14086602, by rfl⟩ : syracuseStep 37564273 = 28173205) B28173205
theorem B3256193 : Blo 1012602 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B1519721 : Blo 1012602 1519721 := bstep (se 2 (by rfl) ⟨569895, by rfl⟩ : syracuseStep 1519721 = 1139791) B1139791
theorem B227881163 : Blo 1012602 227881163 := bstep (se 1 (by rfl) ⟨170910872, by rfl⟩ : syracuseStep 227881163 = 341821745) B341821745
theorem B20820239 : Blo 1012602 20820239 := bstep (se 1 (by rfl) ⟨15615179, by rfl⟩ : syracuseStep 20820239 = 31230359) B31230359
theorem B16691561 : Blo 1012602 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B1520039 : Blo 1012602 1520039 := bstep (se 1 (by rfl) ⟨1140029, by rfl⟩ : syracuseStep 1520039 = 2280059) B2280059
theorem B2568631 : Blo 1012602 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B1520123 : Blo 1012602 1520123 := bstep (se 1 (by rfl) ⟨1140092, by rfl⟩ : syracuseStep 1520123 = 2280185) B2280185
theorem B1520249 : Blo 1012602 1520249 := bstep (se 2 (by rfl) ⟨570093, by rfl⟩ : syracuseStep 1520249 = 1140187) B1140187
theorem B1520303 : Blo 1012602 1520303 := bstep (se 1 (by rfl) ⟨1140227, by rfl⟩ : syracuseStep 1520303 = 2280455) B2280455
theorem B1520351 : Blo 1012602 1520351 := bstep (se 1 (by rfl) ⟨1140263, by rfl⟩ : syracuseStep 1520351 = 2280527) B2280527
theorem B3421007 : Blo 1012602 3421007 := bstep (se 1 (by rfl) ⟨2565755, by rfl⟩ : syracuseStep 3421007 = 5131511) B5131511
theorem B1029019 : Blo 1012602 1029019 := bstep (se 1 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 1029019 = 1543529) B1543529
theorem B1520615 : Blo 1012602 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B10957949 : Blo 1012602 10957949 := bstep (se 3 (by rfl) ⟨2054615, by rfl⟩ : syracuseStep 10957949 = 4109231) B4109231
theorem B5780605 : Blo 1012602 5780605 := bstep (se 3 (by rfl) ⟨1083863, by rfl⟩ : syracuseStep 5780605 = 2167727) B2167727
theorem B3421331 : Blo 1012602 3421331 := bstep (se 1 (by rfl) ⟨2565998, by rfl⟩ : syracuseStep 3421331 = 5131997) B5131997
theorem B1520873 : Blo 1012602 1520873 := bstep (se 2 (by rfl) ⟨570327, by rfl⟩ : syracuseStep 1520873 = 1140655) B1140655
theorem B2438387 : Blo 1012602 2438387 := bstep (se 1 (by rfl) ⟨1828790, by rfl⟩ : syracuseStep 2438387 = 3657581) B3657581
theorem B1520927 : Blo 1012602 1520927 := bstep (se 1 (by rfl) ⟨1140695, by rfl⟩ : syracuseStep 1520927 = 2281391) B2281391
theorem B2372903 : Blo 1012602 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B3421601 : Blo 1012602 3421601 := bstep (se 2 (by rfl) ⟨1283100, by rfl⟩ : syracuseStep 3421601 = 2566201) B2566201
theorem B1521095 : Blo 1012602 1521095 := bstep (se 1 (by rfl) ⟨1140821, by rfl⟩ : syracuseStep 1521095 = 2281643) B2281643
theorem B4110011 : Blo 1012602 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B1521449 : Blo 1012602 1521449 := bstep (se 2 (by rfl) ⟨570543, by rfl⟩ : syracuseStep 1521449 = 1141087) B1141087
theorem B1521455 : Blo 1012602 1521455 := bstep (se 1 (by rfl) ⟨1141091, by rfl⟩ : syracuseStep 1521455 = 2282183) B2282183
theorem B5551927 : Blo 1012602 5551927 := bstep (se 1 (by rfl) ⟨4163945, by rfl⟩ : syracuseStep 5551927 = 8327891) B8327891
theorem B2570039 : Blo 1012602 2570039 := bstep (se 1 (by rfl) ⟨1927529, by rfl⟩ : syracuseStep 2570039 = 3855059) B3855059
theorem B2570089 : Blo 1012602 2570089 := bstep (se 2 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 2570089 = 1927567) B1927567
theorem B4634657 : Blo 1012602 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B1521929 : Blo 1012602 1521929 := bstep (se 2 (by rfl) ⟨570723, by rfl⟩ : syracuseStep 1521929 = 1141447) B1141447
theorem B1522031 : Blo 1012602 1522031 := bstep (se 1 (by rfl) ⟨1141523, by rfl⟩ : syracuseStep 1522031 = 2283047) B2283047
theorem B5126651 : Blo 1012602 5126651 := bstep (se 1 (by rfl) ⟨3844988, by rfl⟩ : syracuseStep 5126651 = 7689977) B7689977
theorem B1522247 : Blo 1012602 1522247 := bstep (se 1 (by rfl) ⟨1141685, by rfl⟩ : syracuseStep 1522247 = 2283371) B2283371
theorem B20855369 : Blo 1012602 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B1522283 : Blo 1012602 1522283 := bstep (se 1 (by rfl) ⟨1141712, by rfl⟩ : syracuseStep 1522283 = 2283425) B2283425
theorem B1522511 : Blo 1012602 1522511 := bstep (se 1 (by rfl) ⟨1141883, by rfl⟩ : syracuseStep 1522511 = 2283767) B2283767
theorem B16464815 : Blo 1012602 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B16694191 : Blo 1012602 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B29277233 : Blo 1012602 29277233 := bstep (se 2 (by rfl) ⟨10978962, by rfl⟩ : syracuseStep 29277233 = 21957925) B21957925
theorem B1522907 : Blo 1012602 1522907 := bstep (se 1 (by rfl) ⟨1142180, by rfl⟩ : syracuseStep 1522907 = 2284361) B2284361
theorem B2571497 : Blo 1012602 2571497 := bstep (se 2 (by rfl) ⟨964311, by rfl⟩ : syracuseStep 2571497 = 1928623) B1928623
theorem B4341059 : Blo 1012602 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B1523081 : Blo 1012602 1523081 := bstep (se 2 (by rfl) ⟨571155, by rfl⟩ : syracuseStep 1523081 = 1142311) B1142311
theorem B2571659 : Blo 1012602 2571659 := bstep (se 1 (by rfl) ⟨1928744, by rfl⟩ : syracuseStep 2571659 = 3857489) B3857489
theorem B5127623 : Blo 1012602 5127623 := bstep (se 1 (by rfl) ⟨3845717, by rfl⟩ : syracuseStep 5127623 = 7691435) B7691435
theorem B6176351 : Blo 1012602 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B2571871 : Blo 1012602 2571871 := bstep (se 1 (by rfl) ⟨1928903, by rfl⟩ : syracuseStep 2571871 = 3857807) B3857807
theorem B1523435 : Blo 1012602 1523435 := bstep (se 1 (by rfl) ⟨1142576, by rfl⟩ : syracuseStep 1523435 = 2285153) B2285153
theorem B5127947 : Blo 1012602 5127947 := bstep (se 1 (by rfl) ⟨3845960, by rfl⟩ : syracuseStep 5127947 = 7691921) B7691921
theorem B3850031 : Blo 1012602 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B1523663 : Blo 1012602 1523663 := bstep (se 1 (by rfl) ⟨1142747, by rfl⟩ : syracuseStep 1523663 = 2285495) B2285495
theorem B2572499 : Blo 1012602 2572499 := bstep (se 1 (by rfl) ⟨1929374, by rfl⟩ : syracuseStep 2572499 = 3858749) B3858749
theorem B1524059 : Blo 1012602 1524059 := bstep (se 1 (by rfl) ⟨1143044, by rfl⟩ : syracuseStep 1524059 = 2286089) B2286089
theorem B1851815 : Blo 1012602 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B3424787 : Blo 1012602 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B1524287 : Blo 1012602 1524287 := bstep (se 1 (by rfl) ⟨1143215, by rfl⟩ : syracuseStep 1524287 = 2286431) B2286431
theorem B1524407 : Blo 1012602 1524407 := bstep (se 1 (by rfl) ⟨1143305, by rfl⟩ : syracuseStep 1524407 = 2286611) B2286611
theorem B5128919 : Blo 1012602 5128919 := bstep (se 1 (by rfl) ⟨3846689, by rfl⟩ : syracuseStep 5128919 = 7693379) B7693379
theorem B25051949 : Blo 1012602 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B1524635 : Blo 1012602 1524635 := bstep (se 1 (by rfl) ⟨1143476, by rfl⟩ : syracuseStep 1524635 = 2286953) B2286953
theorem B2278439 : Blo 1012602 2278439 := bstep (se 1 (by rfl) ⟨1708829, by rfl⟩ : syracuseStep 2278439 = 3417659) B3417659
theorem B19514465 : Blo 1012602 19514465 := bstep (se 2 (by rfl) ⟨7317924, by rfl⟩ : syracuseStep 19514465 = 14635849) B14635849
theorem B2278619 : Blo 1012602 2278619 := bstep (se 1 (by rfl) ⟨1708964, by rfl⟩ : syracuseStep 2278619 = 3417929) B3417929
theorem B1623335 : Blo 1012602 1623335 := bstep (se 1 (by rfl) ⟨1217501, by rfl⟩ : syracuseStep 1623335 = 2435003) B2435003
theorem B5129567 : Blo 1012602 5129567 := bstep (se 1 (by rfl) ⟨3847175, by rfl⟩ : syracuseStep 5129567 = 7694351) B7694351
theorem B13157741 : Blo 1012602 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B2311561 : Blo 1012602 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B2278817 : Blo 1012602 2278817 := bstep (se 2 (by rfl) ⟨854556, by rfl⟩ : syracuseStep 2278817 = 1709113) B1709113
theorem B2279375 : Blo 1012602 2279375 := bstep (se 1 (by rfl) ⟨1709531, by rfl⟩ : syracuseStep 2279375 = 3419063) B3419063
theorem B9259123 : Blo 1012602 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B3426569 : Blo 1012602 3426569 := bstep (se 2 (by rfl) ⟨1284963, by rfl⟩ : syracuseStep 3426569 = 2569927) B2569927
theorem B2279753 : Blo 1012602 2279753 := bstep (se 2 (by rfl) ⟨854907, by rfl⟩ : syracuseStep 2279753 = 1709815) B1709815
theorem B2279771 : Blo 1012602 2279771 := bstep (se 1 (by rfl) ⟨1709828, by rfl⟩ : syracuseStep 2279771 = 3419657) B3419657
theorem B11553191 : Blo 1012602 11553191 := bstep (se 1 (by rfl) ⟨8664893, by rfl⟩ : syracuseStep 11553191 = 17329787) B17329787
theorem B4868855 : Blo 1012602 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B5491475 : Blo 1012602 5491475 := bstep (se 1 (by rfl) ⟨4118606, by rfl⟩ : syracuseStep 5491475 = 8237213) B8237213
theorem B5557015 : Blo 1012602 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B2280347 : Blo 1012602 2280347 := bstep (se 1 (by rfl) ⟨1710260, by rfl⟩ : syracuseStep 2280347 = 3420521) B3420521
theorem B2280545 : Blo 1012602 2280545 := bstep (se 2 (by rfl) ⟨855204, by rfl⟩ : syracuseStep 2280545 = 1710409) B1710409
theorem B2280743 : Blo 1012602 2280743 := bstep (se 1 (by rfl) ⟨1710557, by rfl⟩ : syracuseStep 2280743 = 3421115) B3421115
theorem B3427703 : Blo 1012602 3427703 := bstep (se 1 (by rfl) ⟨2570777, by rfl⟩ : syracuseStep 3427703 = 5141555) B5141555
theorem B5131835 : Blo 1012602 5131835 := bstep (se 1 (by rfl) ⟨3848876, by rfl⟩ : syracuseStep 5131835 = 7697753) B7697753
theorem B3853919 : Blo 1012602 3853919 := bstep (se 1 (by rfl) ⟨2890439, by rfl⟩ : syracuseStep 3853919 = 5780879) B5780879
theorem B2281121 : Blo 1012602 2281121 := bstep (se 2 (by rfl) ⟨855420, by rfl⟩ : syracuseStep 2281121 = 1710841) B1710841
theorem B3854087 : Blo 1012602 3854087 := bstep (se 1 (by rfl) ⟨2890565, by rfl⟩ : syracuseStep 3854087 = 5781131) B5781131
theorem B2281481 : Blo 1012602 2281481 := bstep (se 2 (by rfl) ⟨855555, by rfl⟩ : syracuseStep 2281481 = 1711111) B1711111
theorem B16437305 : Blo 1012602 16437305 := bstep (se 2 (by rfl) ⟨6163989, by rfl⟩ : syracuseStep 16437305 = 12327979) B12327979
theorem B2281895 : Blo 1012602 2281895 := bstep (se 1 (by rfl) ⟨1711421, by rfl⟩ : syracuseStep 2281895 = 3422843) B3422843
theorem B3428783 : Blo 1012602 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B2282003 : Blo 1012602 2282003 := bstep (se 1 (by rfl) ⟨1711502, by rfl⟩ : syracuseStep 2282003 = 3423005) B3423005
theorem B3658259 : Blo 1012602 3658259 := bstep (se 1 (by rfl) ⟨2743694, by rfl⟩ : syracuseStep 3658259 = 5487389) B5487389
theorem B2740807 : Blo 1012602 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B2282057 : Blo 1012602 2282057 := bstep (se 2 (by rfl) ⟨855771, by rfl⟩ : syracuseStep 2282057 = 1711543) B1711543
theorem B10408601 : Blo 1012602 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B2282471 : Blo 1012602 2282471 := bstep (se 1 (by rfl) ⟨1711853, by rfl⟩ : syracuseStep 2282471 = 3423707) B3423707
theorem B8672345 : Blo 1012602 8672345 := bstep (se 2 (by rfl) ⟨3252129, by rfl⟩ : syracuseStep 8672345 = 6504259) B6504259
theorem B5133455 : Blo 1012602 5133455 := bstep (se 1 (by rfl) ⟨3850091, by rfl⟩ : syracuseStep 5133455 = 7700183) B7700183
theorem B5854355 : Blo 1012602 5854355 := bstep (se 1 (by rfl) ⟨4390766, by rfl⟩ : syracuseStep 5854355 = 8781533) B8781533
theorem B3855559 : Blo 1012602 3855559 := bstep (se 1 (by rfl) ⟨2891669, by rfl⟩ : syracuseStep 3855559 = 5783339) B5783339
theorem B2282849 : Blo 1012602 2282849 := bstep (se 2 (by rfl) ⟨856068, by rfl⟩ : syracuseStep 2282849 = 1712137) B1712137
theorem B3429755 : Blo 1012602 3429755 := bstep (se 1 (by rfl) ⟨2572316, by rfl⟩ : syracuseStep 3429755 = 5144633) B5144633
theorem B2282939 : Blo 1012602 2282939 := bstep (se 1 (by rfl) ⟨1712204, by rfl⟩ : syracuseStep 2282939 = 3424409) B3424409
theorem B9754157 : Blo 1012602 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B2283065 : Blo 1012602 2283065 := bstep (se 2 (by rfl) ⟨856149, by rfl⟩ : syracuseStep 2283065 = 1712299) B1712299
theorem B2774825 : Blo 1012602 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B2283731 : Blo 1012602 2283731 := bstep (se 1 (by rfl) ⟨1712798, by rfl⟩ : syracuseStep 2283731 = 3425597) B3425597
theorem B5134589 : Blo 1012602 5134589 := bstep (se 3 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 5134589 = 1925471) B1925471
theorem B2283785 : Blo 1012602 2283785 := bstep (se 2 (by rfl) ⟨856419, by rfl⟩ : syracuseStep 2283785 = 1712839) B1712839
theorem B2742601 : Blo 1012602 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B2284001 : Blo 1012602 2284001 := bstep (se 2 (by rfl) ⟨856500, by rfl⟩ : syracuseStep 2284001 = 1713001) B1713001
theorem B2316863 : Blo 1012602 2316863 := bstep (se 1 (by rfl) ⟨1737647, by rfl⟩ : syracuseStep 2316863 = 3475295) B3475295
theorem B3857003 : Blo 1012602 3857003 := bstep (se 1 (by rfl) ⟨2892752, by rfl⟩ : syracuseStep 3857003 = 5785505) B5785505
theorem B2284307 : Blo 1012602 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B3300115 : Blo 1012602 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B2776051 : Blo 1012602 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B5135399 : Blo 1012602 5135399 := bstep (se 1 (by rfl) ⟨3851549, by rfl⟩ : syracuseStep 5135399 = 7703099) B7703099
theorem B2284667 : Blo 1012602 2284667 := bstep (se 1 (by rfl) ⟨1713500, by rfl⟩ : syracuseStep 2284667 = 3427001) B3427001
theorem B2284793 : Blo 1012602 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B24108299 : Blo 1012602 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B2284937 : Blo 1012602 2284937 := bstep (se 2 (by rfl) ⟨856851, by rfl⟩ : syracuseStep 2284937 = 1713703) B1713703
theorem B3661271 : Blo 1012602 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B2285063 : Blo 1012602 2285063 := bstep (se 1 (by rfl) ⟨1713797, by rfl⟩ : syracuseStep 2285063 = 3427595) B3427595
theorem B2285243 : Blo 1012602 2285243 := bstep (se 1 (by rfl) ⟨1713932, by rfl⟩ : syracuseStep 2285243 = 3427865) B3427865
theorem B3661615 : Blo 1012602 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2285369 : Blo 1012602 2285369 := bstep (se 2 (by rfl) ⟨857013, by rfl⟩ : syracuseStep 2285369 = 1714027) B1714027
theorem B7692407 : Blo 1012602 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B3858779 : Blo 1012602 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B2285999 : Blo 1012602 2285999 := bstep (se 1 (by rfl) ⟨1714499, by rfl⟩ : syracuseStep 2285999 = 3428999) B3428999
theorem B2286035 : Blo 1012602 2286035 := bstep (se 1 (by rfl) ⟨1714526, by rfl⟩ : syracuseStep 2286035 = 3429053) B3429053
theorem B2286143 : Blo 1012602 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B2286251 : Blo 1012602 2286251 := bstep (se 1 (by rfl) ⟨1714688, by rfl⟩ : syracuseStep 2286251 = 3429377) B3429377
theorem B1139503 : Blo 1012602 1139503 := bstep (se 1 (by rfl) ⟨854627, by rfl⟩ : syracuseStep 1139503 = 1709255) B1709255
theorem B1139611 : Blo 1012602 1139611 := bstep (se 1 (by rfl) ⟨854708, by rfl⟩ : syracuseStep 1139611 = 1709417) B1709417
theorem B3859447 : Blo 1012602 3859447 := bstep (se 1 (by rfl) ⟨2894585, by rfl⟩ : syracuseStep 3859447 = 5789171) B5789171
theorem B5137505 : Blo 1012602 5137505 := bstep (se 2 (by rfl) ⟨1926564, by rfl⟩ : syracuseStep 5137505 = 3853129) B3853129
theorem B4875389 : Blo 1012602 4875389 := bstep (se 3 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 4875389 = 1828271) B1828271
theorem B2286791 : Blo 1012602 2286791 := bstep (se 1 (by rfl) ⟨1715093, by rfl⟩ : syracuseStep 2286791 = 3430187) B3430187
theorem B1828127 : Blo 1012602 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B1140007 : Blo 1012602 1140007 := bstep (se 1 (by rfl) ⟨855005, by rfl⟩ : syracuseStep 1140007 = 1710011) B1710011
theorem B3859751 : Blo 1012602 3859751 := bstep (se 1 (by rfl) ⟨2894813, by rfl⟩ : syracuseStep 3859751 = 5789627) B5789627
theorem B124872029 : Blo 1012602 124872029 := bstep (se 3 (by rfl) ⟨23413505, by rfl⟩ : syracuseStep 124872029 = 46827011) B46827011
theorem B1926497 : Blo 1012602 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B1140079 : Blo 1012602 1140079 := bstep (se 1 (by rfl) ⟨855059, by rfl⟩ : syracuseStep 1140079 = 1710119) B1710119
theorem B2286971 : Blo 1012602 2286971 := bstep (se 1 (by rfl) ⟨1715228, by rfl⟩ : syracuseStep 2286971 = 3430457) B3430457
theorem B2287097 : Blo 1012602 2287097 := bstep (se 2 (by rfl) ⟨857661, by rfl⟩ : syracuseStep 2287097 = 1715323) B1715323
theorem B1140295 : Blo 1012602 1140295 := bstep (se 1 (by rfl) ⟨855221, by rfl⟩ : syracuseStep 1140295 = 1710443) B1710443
theorem B2287187 : Blo 1012602 2287187 := bstep (se 1 (by rfl) ⟨1715390, by rfl⟩ : syracuseStep 2287187 = 3430781) B3430781
theorem B3663721 : Blo 1012602 3663721 := bstep (se 2 (by rfl) ⟨1373895, by rfl⟩ : syracuseStep 3663721 = 2747791) B2747791
theorem B4941751 : Blo 1012602 4941751 := bstep (se 1 (by rfl) ⟨3706313, by rfl⟩ : syracuseStep 4941751 = 7412627) B7412627
theorem B1141159 : Blo 1012602 1141159 := bstep (se 1 (by rfl) ⟨855869, by rfl⟩ : syracuseStep 1141159 = 1711739) B1711739
theorem B20834995 : Blo 1012602 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B12511955 : Blo 1012602 12511955 := bstep (se 1 (by rfl) ⟨9383966, by rfl⟩ : syracuseStep 12511955 = 18767933) B18767933
theorem B9267959 : Blo 1012602 9267959 := bstep (se 1 (by rfl) ⟨6950969, by rfl⟩ : syracuseStep 9267959 = 13901939) B13901939
theorem B1927955 : Blo 1012602 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B1141735 : Blo 1012602 1141735 := bstep (se 1 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 1141735 = 1712603) B1712603
theorem B1829879 : Blo 1012602 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B5139773 : Blo 1012602 5139773 := bstep (se 3 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 5139773 = 1927415) B1927415
theorem B5205385 : Blo 1012602 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B1928585 : Blo 1012602 1928585 := bstep (se 2 (by rfl) ⟨723219, by rfl⟩ : syracuseStep 1928585 = 1446439) B1446439
theorem B11726801 : Blo 1012602 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B1143391 : Blo 1012602 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B2290351 : Blo 1012602 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B1012635 : Blo 1012602 1012635 := bstep (se 1 (by rfl) ⟨759476, by rfl⟩ : syracuseStep 1012635 = 1518953) B1518953
theorem B1012687 : Blo 1012602 1012687 := bstep (se 1 (by rfl) ⟨759515, by rfl⟩ : syracuseStep 1012687 = 1519031) B1519031
theorem B1012711 : Blo 1012602 1012711 := bstep (se 1 (by rfl) ⟨759533, by rfl⟩ : syracuseStep 1012711 = 1519067) B1519067
theorem B9893011 : Blo 1012602 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B1013023 : Blo 1012602 1013023 := bstep (se 1 (by rfl) ⟨759767, by rfl⟩ : syracuseStep 1013023 = 1519535) B1519535
theorem B1013083 : Blo 1012602 1013083 := bstep (se 1 (by rfl) ⟨759812, by rfl⟩ : syracuseStep 1013083 = 1519625) B1519625
theorem B1013103 : Blo 1012602 1013103 := bstep (se 1 (by rfl) ⟨759827, by rfl⟩ : syracuseStep 1013103 = 1519655) B1519655
theorem B1013159 : Blo 1012602 1013159 := bstep (se 1 (by rfl) ⟨759869, by rfl⟩ : syracuseStep 1013159 = 1519739) B1519739
theorem B1013243 : Blo 1012602 1013243 := bstep (se 1 (by rfl) ⟨759932, by rfl⟩ : syracuseStep 1013243 = 1519865) B1519865
theorem B1013311 : Blo 1012602 1013311 := bstep (se 1 (by rfl) ⟨759983, by rfl⟩ : syracuseStep 1013311 = 1519967) B1519967
theorem B1013319 : Blo 1012602 1013319 := bstep (se 1 (by rfl) ⟨759989, by rfl⟩ : syracuseStep 1013319 = 1519979) B1519979
theorem B8681093 : Blo 1012602 8681093 := bstep (se 4 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 8681093 = 1627705) B1627705
theorem B5142203 : Blo 1012602 5142203 := bstep (se 1 (by rfl) ⟨3856652, by rfl⟩ : syracuseStep 5142203 = 7713305) B7713305
theorem B1013471 : Blo 1012602 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B1013551 : Blo 1012602 1013551 := bstep (se 1 (by rfl) ⟨760163, by rfl⟩ : syracuseStep 1013551 = 1520327) B1520327
theorem B11564855 : Blo 1012602 11564855 := bstep (se 1 (by rfl) ⟨8673641, by rfl⟩ : syracuseStep 11564855 = 17347283) B17347283
theorem B1013659 : Blo 1012602 1013659 := bstep (se 1 (by rfl) ⟨760244, by rfl⟩ : syracuseStep 1013659 = 1520489) B1520489
theorem B1013711 : Blo 1012602 1013711 := bstep (se 1 (by rfl) ⟨760283, by rfl⟩ : syracuseStep 1013711 = 1520567) B1520567
theorem B1013735 : Blo 1012602 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B1014047 : Blo 1012602 1014047 := bstep (se 1 (by rfl) ⟨760535, by rfl⟩ : syracuseStep 1014047 = 1521071) B1521071
theorem B1014107 : Blo 1012602 1014107 := bstep (se 1 (by rfl) ⟨760580, by rfl⟩ : syracuseStep 1014107 = 1521161) B1521161
theorem B1014127 : Blo 1012602 1014127 := bstep (se 1 (by rfl) ⟨760595, by rfl⟩ : syracuseStep 1014127 = 1521191) B1521191
theorem B1014183 : Blo 1012602 1014183 := bstep (se 1 (by rfl) ⟨760637, by rfl⟩ : syracuseStep 1014183 = 1521275) B1521275
theorem B1014267 : Blo 1012602 1014267 := bstep (se 1 (by rfl) ⟨760700, by rfl⟩ : syracuseStep 1014267 = 1521401) B1521401
theorem B1014335 : Blo 1012602 1014335 := bstep (se 1 (by rfl) ⟨760751, by rfl⟩ : syracuseStep 1014335 = 1521503) B1521503
theorem B1014343 : Blo 1012602 1014343 := bstep (se 1 (by rfl) ⟨760757, by rfl⟩ : syracuseStep 1014343 = 1521515) B1521515
theorem B1014495 : Blo 1012602 1014495 := bstep (se 1 (by rfl) ⟨760871, by rfl⟩ : syracuseStep 1014495 = 1521743) B1521743
theorem B1014575 : Blo 1012602 1014575 := bstep (se 1 (by rfl) ⟨760931, by rfl⟩ : syracuseStep 1014575 = 1521863) B1521863
theorem B7404443 : Blo 1012602 7404443 := bstep (se 1 (by rfl) ⟨5553332, by rfl⟩ : syracuseStep 7404443 = 11106665) B11106665
theorem B1014683 : Blo 1012602 1014683 := bstep (se 1 (by rfl) ⟨761012, by rfl⟩ : syracuseStep 1014683 = 1522025) B1522025
theorem B1014735 : Blo 1012602 1014735 := bstep (se 1 (by rfl) ⟨761051, by rfl⟩ : syracuseStep 1014735 = 1522103) B1522103
theorem B1014759 : Blo 1012602 1014759 := bstep (se 1 (by rfl) ⟨761069, by rfl⟩ : syracuseStep 1014759 = 1522139) B1522139
theorem B37059707 : Blo 1012602 37059707 := bstep (se 1 (by rfl) ⟨27794780, by rfl⟩ : syracuseStep 37059707 = 55589561) B55589561
theorem B1015071 : Blo 1012602 1015071 := bstep (se 1 (by rfl) ⟨761303, by rfl⟩ : syracuseStep 1015071 = 1522607) B1522607
theorem B1015131 : Blo 1012602 1015131 := bstep (se 1 (by rfl) ⟨761348, by rfl⟩ : syracuseStep 1015131 = 1522697) B1522697
theorem B1015151 : Blo 1012602 1015151 := bstep (se 1 (by rfl) ⟨761363, by rfl⟩ : syracuseStep 1015151 = 1522727) B1522727
theorem B1015207 : Blo 1012602 1015207 := bstep (se 1 (by rfl) ⟨761405, by rfl⟩ : syracuseStep 1015207 = 1522811) B1522811
theorem B1015291 : Blo 1012602 1015291 := bstep (se 1 (by rfl) ⟨761468, by rfl⟩ : syracuseStep 1015291 = 1522937) B1522937
theorem B9272843 : Blo 1012602 9272843 := bstep (se 1 (by rfl) ⟨6954632, by rfl⟩ : syracuseStep 9272843 = 13909265) B13909265
theorem B1015359 : Blo 1012602 1015359 := bstep (se 1 (by rfl) ⟨761519, by rfl⟩ : syracuseStep 1015359 = 1523039) B1523039
theorem B1015367 : Blo 1012602 1015367 := bstep (se 1 (by rfl) ⟨761525, by rfl⟩ : syracuseStep 1015367 = 1523051) B1523051
theorem B3898961 : Blo 1012602 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B5144147 : Blo 1012602 5144147 := bstep (se 1 (by rfl) ⟨3858110, by rfl⟩ : syracuseStep 5144147 = 7716221) B7716221
theorem B24641171 : Blo 1012602 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B1015519 : Blo 1012602 1015519 := bstep (se 1 (by rfl) ⟨761639, by rfl⟩ : syracuseStep 1015519 = 1523279) B1523279
theorem B1015599 : Blo 1012602 1015599 := bstep (se 1 (by rfl) ⟨761699, by rfl⟩ : syracuseStep 1015599 = 1523399) B1523399
theorem B1015707 : Blo 1012602 1015707 := bstep (se 1 (by rfl) ⟨761780, by rfl⟩ : syracuseStep 1015707 = 1523561) B1523561
theorem B1015759 : Blo 1012602 1015759 := bstep (se 1 (by rfl) ⟨761819, by rfl⟩ : syracuseStep 1015759 = 1523639) B1523639
theorem B1015783 : Blo 1012602 1015783 := bstep (se 1 (by rfl) ⟨761837, by rfl⟩ : syracuseStep 1015783 = 1523675) B1523675
theorem B1016039 : Blo 1012602 1016039 := bstep (se 1 (by rfl) ⟨762029, by rfl⟩ : syracuseStep 1016039 = 1524059) B1524059
theorem B3244313 : Blo 1012602 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1016191 : Blo 1012602 1016191 := bstep (se 1 (by rfl) ⟨762143, by rfl⟩ : syracuseStep 1016191 = 1524287) B1524287
theorem B1016271 : Blo 1012602 1016271 := bstep (se 1 (by rfl) ⟨762203, by rfl⟩ : syracuseStep 1016271 = 1524407) B1524407
theorem B1442281 : Blo 1012602 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B1016423 : Blo 1012602 1016423 := bstep (se 1 (by rfl) ⟨762317, by rfl⟩ : syracuseStep 1016423 = 1524635) B1524635
theorem B13009643 : Blo 1012602 13009643 := bstep (se 1 (by rfl) ⟨9757232, by rfl⟩ : syracuseStep 13009643 = 19514465) B19514465
theorem B4326331 : Blo 1012602 4326331 := bstep (se 1 (by rfl) ⟨3244748, by rfl⟩ : syracuseStep 4326331 = 6489497) B6489497
theorem B13173839 : Blo 1012602 13173839 := bstep (se 1 (by rfl) ⟨9880379, by rfl⟩ : syracuseStep 13173839 = 19760759) B19760759
theorem B5145929 : Blo 1012602 5145929 := bstep (se 2 (by rfl) ⟨1929723, by rfl⟩ : syracuseStep 5145929 = 3859447) B3859447
theorem B7702127 : Blo 1012602 7702127 := bstep (se 1 (by rfl) ⟨5776595, by rfl⟩ : syracuseStep 7702127 = 11553191) B11553191
theorem B1443511 : Blo 1012602 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B3245903 : Blo 1012602 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B2885473 : Blo 1012602 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B3245953 : Blo 1012602 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B4884961 : Blo 1012602 4884961 := bstep (se 2 (by rfl) ⟨1831860, by rfl⟩ : syracuseStep 4884961 = 3663721) B3663721
theorem B6589001 : Blo 1012602 6589001 := bstep (se 2 (by rfl) ⟨2470875, by rfl⟩ : syracuseStep 6589001 = 4941751) B4941751
theorem B5769899 : Blo 1012602 5769899 := bstep (se 1 (by rfl) ⟨4327424, by rfl⟩ : syracuseStep 5769899 = 8654849) B8654849
theorem B4328279 : Blo 1012602 4328279 := bstep (se 1 (by rfl) ⟨3246209, by rfl⟩ : syracuseStep 4328279 = 6492419) B6492419
theorem B3902903 : Blo 1012602 3902903 := bstep (se 1 (by rfl) ⟨2927177, by rfl⟩ : syracuseStep 3902903 = 5854355) B5854355
theorem B4328893 : Blo 1012602 4328893 := bstep (se 3 (by rfl) ⟨811667, by rfl⟩ : syracuseStep 4328893 = 1623335) B1623335
theorem B2887159 : Blo 1012602 2887159 := bstep (se 1 (by rfl) ⟨2165369, by rfl⟩ : syracuseStep 2887159 = 4330739) B4330739
theorem B2166907 : Blo 1012602 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B1544575 : Blo 1012602 1544575 := bstep (se 1 (by rfl) ⟨1158431, by rfl⟩ : syracuseStep 1544575 = 2316863) B2316863
theorem B2888743 : Blo 1012602 2888743 := bstep (se 1 (by rfl) ⟨2166557, by rfl⟩ : syracuseStep 2888743 = 4333115) B4333115
theorem B2888777 : Blo 1012602 2888777 := bstep (se 2 (by rfl) ⟨1083291, by rfl⟩ : syracuseStep 2888777 = 2166583) B2166583
theorem B4330705 : Blo 1012602 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B1709903 : Blo 1012602 1709903 := bstep (se 1 (by rfl) ⟨1282427, by rfl⟩ : syracuseStep 1709903 = 2564855) B2564855
theorem B3250259 : Blo 1012602 3250259 := bstep (se 1 (by rfl) ⟨2437694, by rfl⟩ : syracuseStep 3250259 = 4875389) B4875389
theorem B6691019 : Blo 1012602 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B3053801 : Blo 1012602 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B1284331 : Blo 1012602 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B7707473 : Blo 1012602 7707473 := bstep (se 2 (by rfl) ⟨2890302, by rfl⟩ : syracuseStep 7707473 = 5780605) B5780605
theorem B4332379 : Blo 1012602 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B1711145 : Blo 1012602 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B1285303 : Blo 1012602 1285303 := bstep (se 1 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 1285303 = 1927955) B1927955
theorem B33365213 : Blo 1012602 33365213 := bstep (se 3 (by rfl) ⟨6255977, by rfl⟩ : syracuseStep 33365213 = 12511955) B12511955
theorem B1711327 : Blo 1012602 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B1219919 : Blo 1012602 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B9903455 : Blo 1012602 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B12328325 : Blo 1012602 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B2563559 : Blo 1012602 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B1285723 : Blo 1012602 1285723 := bstep (se 1 (by rfl) ⟨964292, by rfl⟩ : syracuseStep 1285723 = 1928585) B1928585
theorem B1711759 : Blo 1012602 1711759 := bstep (se 1 (by rfl) ⟨1283819, by rfl⟩ : syracuseStep 1711759 = 2567639) B2567639
theorem B7708445 : Blo 1012602 7708445 := bstep (se 3 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 7708445 = 2890667) B2890667
theorem B2170795 : Blo 1012602 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B151920775 : Blo 1012602 151920775 := bstep (se 1 (by rfl) ⟨113940581, by rfl⟩ : syracuseStep 151920775 = 227881163) B227881163
theorem B1581935 : Blo 1012602 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B4400153 : Blo 1012602 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B7709903 : Blo 1012602 7709903 := bstep (se 1 (by rfl) ⟨5782427, by rfl⟩ : syracuseStep 7709903 = 11564855) B11564855
theorem B1713359 : Blo 1012602 1713359 := bstep (se 1 (by rfl) ⟨1285019, by rfl⟩ : syracuseStep 1713359 = 2570039) B2570039
theorem B22258921 : Blo 1012602 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B3089771 : Blo 1012602 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B3417767 : Blo 1012602 3417767 := bstep (se 1 (by rfl) ⟨2563325, by rfl⟩ : syracuseStep 3417767 = 5126651) B5126651
theorem B13903579 : Blo 1012602 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B1714169 : Blo 1012602 1714169 := bstep (se 2 (by rfl) ⟨642813, by rfl⟩ : syracuseStep 1714169 = 1285627) B1285627
theorem B1714331 : Blo 1012602 1714331 := bstep (se 1 (by rfl) ⟨1285748, by rfl⟩ : syracuseStep 1714331 = 2571497) B2571497
theorem B2894039 : Blo 1012602 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B3418361 : Blo 1012602 3418361 := bstep (se 2 (by rfl) ⟨1281885, by rfl⟩ : syracuseStep 3418361 = 2563771) B2563771
theorem B1714439 : Blo 1012602 1714439 := bstep (se 1 (by rfl) ⟨1285829, by rfl⟩ : syracuseStep 1714439 = 2571659) B2571659
theorem B5777689 : Blo 1012602 5777689 := bstep (se 2 (by rfl) ⟨2166633, by rfl⟩ : syracuseStep 5777689 = 4333267) B4333267
theorem B3418415 : Blo 1012602 3418415 := bstep (se 1 (by rfl) ⟨2563811, by rfl⟩ : syracuseStep 3418415 = 5127623) B5127623
theorem B2599307 : Blo 1012602 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B16427447 : Blo 1012602 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B3418631 : Blo 1012602 3418631 := bstep (se 1 (by rfl) ⟨2563973, by rfl⟩ : syracuseStep 3418631 = 5127947) B5127947
theorem B2566687 : Blo 1012602 2566687 := bstep (se 1 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 2566687 = 3850031) B3850031
theorem B1714999 : Blo 1012602 1714999 := bstep (se 1 (by rfl) ⟨1286249, by rfl⟩ : syracuseStep 1714999 = 2572499) B2572499
theorem B38972339 : Blo 1012602 38972339 := bstep (se 1 (by rfl) ⟨29229254, by rfl⟩ : syracuseStep 38972339 = 58458509) B58458509
theorem B3419279 : Blo 1012602 3419279 := bstep (se 1 (by rfl) ⟨2564459, by rfl⟩ : syracuseStep 3419279 = 5128919) B5128919
theorem B3845353 : Blo 1012602 3845353 := bstep (se 2 (by rfl) ⟨1442007, by rfl⟩ : syracuseStep 3845353 = 2884015) B2884015
theorem B1715465 : Blo 1012602 1715465 := bstep (se 2 (by rfl) ⟨643299, by rfl⟩ : syracuseStep 1715465 = 1286599) B1286599
theorem B1518959 : Blo 1012602 1518959 := bstep (se 1 (by rfl) ⟨1139219, by rfl⟩ : syracuseStep 1518959 = 2278439) B2278439
theorem B1519079 : Blo 1012602 1519079 := bstep (se 1 (by rfl) ⟨1139309, by rfl⟩ : syracuseStep 1519079 = 2278619) B2278619
theorem B3419711 : Blo 1012602 3419711 := bstep (se 1 (by rfl) ⟨2564783, by rfl⟩ : syracuseStep 3419711 = 5129567) B5129567
theorem B1519211 : Blo 1012602 1519211 := bstep (se 1 (by rfl) ⟨1139408, by rfl⟩ : syracuseStep 1519211 = 2278817) B2278817
theorem B1519337 : Blo 1012602 1519337 := bstep (se 2 (by rfl) ⟨569751, by rfl⟩ : syracuseStep 1519337 = 1139503) B1139503
theorem B1519481 : Blo 1012602 1519481 := bstep (se 2 (by rfl) ⟨569805, by rfl⟩ : syracuseStep 1519481 = 1139611) B1139611
theorem B2928527 : Blo 1012602 2928527 := bstep (se 1 (by rfl) ⟨2196395, by rfl⟩ : syracuseStep 2928527 = 4392791) B4392791
theorem B1519583 : Blo 1012602 1519583 := bstep (se 1 (by rfl) ⟨1139687, by rfl⟩ : syracuseStep 1519583 = 2279375) B2279375
theorem B7712819 : Blo 1012602 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B1519835 : Blo 1012602 1519835 := bstep (se 1 (by rfl) ⟨1139876, by rfl⟩ : syracuseStep 1519835 = 2279753) B2279753
theorem B1519847 : Blo 1012602 1519847 := bstep (se 1 (by rfl) ⟨1139885, by rfl⟩ : syracuseStep 1519847 = 2279771) B2279771
theorem B3420413 : Blo 1012602 3420413 := bstep (se 3 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 3420413 = 1282655) B1282655
theorem B1520009 : Blo 1012602 1520009 := bstep (se 2 (by rfl) ⟨570003, by rfl⟩ : syracuseStep 1520009 = 1140007) B1140007
theorem B1520105 : Blo 1012602 1520105 := bstep (se 2 (by rfl) ⟨570039, by rfl⟩ : syracuseStep 1520105 = 1140079) B1140079
theorem B1520231 : Blo 1012602 1520231 := bstep (se 1 (by rfl) ⟨1140173, by rfl⟩ : syracuseStep 1520231 = 2280347) B2280347
theorem B1520363 : Blo 1012602 1520363 := bstep (se 1 (by rfl) ⟨1140272, by rfl⟩ : syracuseStep 1520363 = 2280545) B2280545
theorem B10990343 : Blo 1012602 10990343 := bstep (se 1 (by rfl) ⟨8242757, by rfl⟩ : syracuseStep 10990343 = 16485515) B16485515
theorem B1520393 : Blo 1012602 1520393 := bstep (se 2 (by rfl) ⟨570147, by rfl⟩ : syracuseStep 1520393 = 1140295) B1140295
theorem B3420953 : Blo 1012602 3420953 := bstep (se 2 (by rfl) ⟨1282857, by rfl⟩ : syracuseStep 3420953 = 2565715) B2565715
theorem B1520495 : Blo 1012602 1520495 := bstep (se 1 (by rfl) ⟨1140371, by rfl⟩ : syracuseStep 1520495 = 2280743) B2280743
theorem B3421223 : Blo 1012602 3421223 := bstep (se 1 (by rfl) ⟨2565917, by rfl⟩ : syracuseStep 3421223 = 5131835) B5131835
theorem B2569279 : Blo 1012602 2569279 := bstep (se 1 (by rfl) ⟨1926959, by rfl⟩ : syracuseStep 2569279 = 3853919) B3853919
theorem B1520747 : Blo 1012602 1520747 := bstep (se 1 (by rfl) ⟨1140560, by rfl⟩ : syracuseStep 1520747 = 2281121) B2281121
theorem B2569391 : Blo 1012602 2569391 := bstep (se 1 (by rfl) ⟨1927043, by rfl⟩ : syracuseStep 2569391 = 3854087) B3854087
theorem B1520987 : Blo 1012602 1520987 := bstep (se 1 (by rfl) ⟨1140740, by rfl⟩ : syracuseStep 1520987 = 2281481) B2281481
theorem B10958203 : Blo 1012602 10958203 := bstep (se 1 (by rfl) ⟨8218652, by rfl⟩ : syracuseStep 10958203 = 16437305) B16437305
theorem B1521263 : Blo 1012602 1521263 := bstep (se 1 (by rfl) ⟨1140947, by rfl⟩ : syracuseStep 1521263 = 2281895) B2281895
theorem B1521335 : Blo 1012602 1521335 := bstep (se 1 (by rfl) ⟨1141001, by rfl⟩ : syracuseStep 1521335 = 2282003) B2282003
theorem B2438839 : Blo 1012602 2438839 := bstep (se 1 (by rfl) ⟨1829129, by rfl⟩ : syracuseStep 2438839 = 3658259) B3658259
theorem B1521371 : Blo 1012602 1521371 := bstep (se 1 (by rfl) ⟨1141028, by rfl⟩ : syracuseStep 1521371 = 2282057) B2282057
theorem B1521545 : Blo 1012602 1521545 := bstep (se 2 (by rfl) ⟨570579, by rfl⟩ : syracuseStep 1521545 = 1141159) B1141159
theorem B1521647 : Blo 1012602 1521647 := bstep (se 1 (by rfl) ⟨1141235, by rfl⟩ : syracuseStep 1521647 = 2282471) B2282471
theorem B5781563 : Blo 1012602 5781563 := bstep (se 1 (by rfl) ⟨4336172, by rfl⟩ : syracuseStep 5781563 = 8672345) B8672345
theorem B3422303 : Blo 1012602 3422303 := bstep (se 1 (by rfl) ⟨2566727, by rfl⟩ : syracuseStep 3422303 = 5133455) B5133455
theorem B1521899 : Blo 1012602 1521899 := bstep (se 1 (by rfl) ⟨1141424, by rfl⟩ : syracuseStep 1521899 = 2282849) B2282849
theorem B1521959 : Blo 1012602 1521959 := bstep (se 1 (by rfl) ⟨1141469, by rfl⟩ : syracuseStep 1521959 = 2282939) B2282939
theorem B6502771 : Blo 1012602 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B1522043 : Blo 1012602 1522043 := bstep (se 1 (by rfl) ⟨1141532, by rfl⟩ : syracuseStep 1522043 = 2283065) B2283065
theorem B1849883 : Blo 1012602 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B1522313 : Blo 1012602 1522313 := bstep (se 2 (by rfl) ⟨570867, by rfl⟩ : syracuseStep 1522313 = 1141735) B1141735
theorem B29637413 : Blo 1012602 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B1522487 : Blo 1012602 1522487 := bstep (se 1 (by rfl) ⟨1141865, by rfl⟩ : syracuseStep 1522487 = 2283731) B2283731
theorem B3423059 : Blo 1012602 3423059 := bstep (se 1 (by rfl) ⟨2567294, by rfl⟩ : syracuseStep 3423059 = 5134589) B5134589
theorem B1522523 : Blo 1012602 1522523 := bstep (se 1 (by rfl) ⟨1141892, by rfl⟩ : syracuseStep 1522523 = 2283785) B2283785
theorem B1522667 : Blo 1012602 1522667 := bstep (se 1 (by rfl) ⟨1142000, by rfl⟩ : syracuseStep 1522667 = 2284001) B2284001
theorem B2571335 : Blo 1012602 2571335 := bstep (se 1 (by rfl) ⟨1928501, by rfl⟩ : syracuseStep 2571335 = 3857003) B3857003
theorem B1522871 : Blo 1012602 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B3423599 : Blo 1012602 3423599 := bstep (se 1 (by rfl) ⟨2567699, by rfl⟩ : syracuseStep 3423599 = 5135399) B5135399
theorem B1523111 : Blo 1012602 1523111 := bstep (se 1 (by rfl) ⟨1142333, by rfl⟩ : syracuseStep 1523111 = 2284667) B2284667
theorem B5783021 : Blo 1012602 5783021 := bstep (se 3 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 5783021 = 2168633) B2168633
theorem B1523195 : Blo 1012602 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B16072199 : Blo 1012602 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B1523291 : Blo 1012602 1523291 := bstep (se 1 (by rfl) ⟨1142468, by rfl⟩ : syracuseStep 1523291 = 2284937) B2284937
theorem B2440847 : Blo 1012602 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B1523375 : Blo 1012602 1523375 := bstep (se 1 (by rfl) ⟨1142531, by rfl⟩ : syracuseStep 1523375 = 2285063) B2285063
theorem B3423977 : Blo 1012602 3423977 := bstep (se 2 (by rfl) ⟨1283991, by rfl⟩ : syracuseStep 3423977 = 2567983) B2567983
theorem B1523495 : Blo 1012602 1523495 := bstep (se 1 (by rfl) ⟨1142621, by rfl⟩ : syracuseStep 1523495 = 2285243) B2285243
theorem B50085697 : Blo 1012602 50085697 := bstep (se 2 (by rfl) ⟨18782136, by rfl⟩ : syracuseStep 50085697 = 37564273) B37564273
theorem B1523579 : Blo 1012602 1523579 := bstep (se 1 (by rfl) ⟨1142684, by rfl⟩ : syracuseStep 1523579 = 2285369) B2285369
theorem B5128271 : Blo 1012602 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B2572519 : Blo 1012602 2572519 := bstep (se 1 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 2572519 = 3858779) B3858779
theorem B1523999 : Blo 1012602 1523999 := bstep (se 1 (by rfl) ⟨1142999, by rfl⟩ : syracuseStep 1523999 = 2285999) B2285999
theorem B1524023 : Blo 1012602 1524023 := bstep (se 1 (by rfl) ⟨1143017, by rfl⟩ : syracuseStep 1524023 = 2286035) B2286035
theorem B1524095 : Blo 1012602 1524095 := bstep (se 1 (by rfl) ⟨1143071, by rfl⟩ : syracuseStep 1524095 = 2286143) B2286143
theorem B1524167 : Blo 1012602 1524167 := bstep (se 1 (by rfl) ⟨1143125, by rfl⟩ : syracuseStep 1524167 = 2286251) B2286251
theorem B3424841 : Blo 1012602 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B3425003 : Blo 1012602 3425003 := bstep (se 1 (by rfl) ⟨2568752, by rfl⟩ : syracuseStep 3425003 = 5137505) B5137505
theorem B3654409 : Blo 1012602 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B1524521 : Blo 1012602 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B7717679 : Blo 1012602 7717679 := bstep (se 1 (by rfl) ⟨5788259, by rfl⟩ : syracuseStep 7717679 = 11576519) B11576519
theorem B1524527 : Blo 1012602 1524527 := bstep (se 1 (by rfl) ⟨1143395, by rfl⟩ : syracuseStep 1524527 = 2286791) B2286791
theorem B2573167 : Blo 1012602 2573167 := bstep (se 1 (by rfl) ⟨1929875, by rfl⟩ : syracuseStep 2573167 = 3859751) B3859751
theorem B83248019 : Blo 1012602 83248019 := bstep (se 1 (by rfl) ⟨62436014, by rfl⟩ : syracuseStep 83248019 = 124872029) B124872029
theorem B1524647 : Blo 1012602 1524647 := bstep (se 1 (by rfl) ⟨1143485, by rfl⟩ : syracuseStep 1524647 = 2286971) B2286971
theorem B2081747 : Blo 1012602 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B11551733 : Blo 1012602 11551733 := bstep (se 5 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 11551733 = 1082975) B1082975
theorem B5948407 : Blo 1012602 5948407 := bstep (se 1 (by rfl) ⟨4461305, by rfl⟩ : syracuseStep 5948407 = 8922611) B8922611
theorem B1524731 : Blo 1012602 1524731 := bstep (se 1 (by rfl) ⟨1143548, by rfl⟩ : syracuseStep 1524731 = 2287097) B2287097
theorem B1524791 : Blo 1012602 1524791 := bstep (se 1 (by rfl) ⟨1143593, by rfl⟩ : syracuseStep 1524791 = 2287187) B2287187
theorem B4113467 : Blo 1012602 4113467 := bstep (se 1 (by rfl) ⟨3085100, by rfl⟩ : syracuseStep 4113467 = 6170201) B6170201
theorem B118441109 : Blo 1012602 118441109 := bstep (se 6 (by rfl) ⟨2775963, by rfl⟩ : syracuseStep 118441109 = 5551927) B5551927
theorem B5784797 : Blo 1012602 5784797 := bstep (se 3 (by rfl) ⟨1084649, by rfl⟩ : syracuseStep 5784797 = 2169299) B2169299
theorem B60081425 : Blo 1012602 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B2278763 : Blo 1012602 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B11716001 : Blo 1012602 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B13190681 : Blo 1012602 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B2279033 : Blo 1012602 2279033 := bstep (se 2 (by rfl) ⟨854637, by rfl⟩ : syracuseStep 2279033 = 1709275) B1709275
theorem B9750239 : Blo 1012602 9750239 := bstep (se 1 (by rfl) ⟨7312679, by rfl⟩ : syracuseStep 9750239 = 14625359) B14625359
theorem B6178639 : Blo 1012602 6178639 := bstep (se 1 (by rfl) ⟨4633979, by rfl⟩ : syracuseStep 6178639 = 9267959) B9267959
theorem B1624207 : Blo 1012602 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B3426515 : Blo 1012602 3426515 := bstep (se 1 (by rfl) ⟨2569886, by rfl⟩ : syracuseStep 3426515 = 5139773) B5139773
theorem B55494989 : Blo 1012602 55494989 := bstep (se 3 (by rfl) ⟨10405310, by rfl⟩ : syracuseStep 55494989 = 20810621) B20810621
theorem B3426785 : Blo 1012602 3426785 := bstep (se 2 (by rfl) ⟨1285044, by rfl⟩ : syracuseStep 3426785 = 2570089) B2570089
theorem B2280041 : Blo 1012602 2280041 := bstep (se 2 (by rfl) ⟨855015, by rfl⟩ : syracuseStep 2280041 = 1710031) B1710031
theorem B7817867 : Blo 1012602 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B13880159 : Blo 1012602 13880159 := bstep (se 1 (by rfl) ⟨10410119, by rfl⟩ : syracuseStep 13880159 = 20820239) B20820239
theorem B11127707 : Blo 1012602 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B3656801 : Blo 1012602 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B2280671 : Blo 1012602 2280671 := bstep (se 1 (by rfl) ⟨1710503, by rfl⟩ : syracuseStep 2280671 = 3421007) B3421007
theorem B2280887 : Blo 1012602 2280887 := bstep (se 1 (by rfl) ⟨1710665, by rfl⟩ : syracuseStep 2280887 = 3421331) B3421331
theorem B1625591 : Blo 1012602 1625591 := bstep (se 1 (by rfl) ⟨1219193, by rfl⟩ : syracuseStep 1625591 = 2438387) B2438387
theorem B2281067 : Blo 1012602 2281067 := bstep (se 1 (by rfl) ⟨1710800, by rfl⟩ : syracuseStep 2281067 = 3421601) B3421601
theorem B5787395 : Blo 1012602 5787395 := bstep (se 1 (by rfl) ⟨4340546, by rfl⟩ : syracuseStep 5787395 = 8681093) B8681093
theorem B2740007 : Blo 1012602 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B3428135 : Blo 1012602 3428135 := bstep (se 1 (by rfl) ⟨2571101, by rfl⟩ : syracuseStep 3428135 = 5142203) B5142203
theorem B2281337 : Blo 1012602 2281337 := bstep (se 2 (by rfl) ⟨855501, by rfl⟩ : syracuseStep 2281337 = 1711003) B1711003
theorem B4936295 : Blo 1012602 4936295 := bstep (se 1 (by rfl) ⟨3702221, by rfl⟩ : syracuseStep 4936295 = 7404443) B7404443
theorem B19518155 : Blo 1012602 19518155 := bstep (se 1 (by rfl) ⟨14638616, by rfl⟩ : syracuseStep 19518155 = 29277233) B29277233
theorem B3429161 : Blo 1012602 3429161 := bstep (se 2 (by rfl) ⟨1285935, by rfl⟩ : syracuseStep 3429161 = 2571871) B2571871
theorem B6181895 : Blo 1012602 6181895 := bstep (se 1 (by rfl) ⟨4636421, by rfl⟩ : syracuseStep 6181895 = 9272843) B9272843
theorem B3429431 : Blo 1012602 3429431 := bstep (se 1 (by rfl) ⟨2572073, by rfl⟩ : syracuseStep 3429431 = 5144147) B5144147
theorem B4117567 : Blo 1012602 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B9884753 : Blo 1012602 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B1234543 : Blo 1012602 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B2283191 : Blo 1012602 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B16701299 : Blo 1012602 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B6510617 : Blo 1012602 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B8771827 : Blo 1012602 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B3857017 : Blo 1012602 3857017 := bstep (se 2 (by rfl) ⟨1446381, by rfl⟩ : syracuseStep 3857017 = 2892763) B2892763
theorem B2284379 : Blo 1012602 2284379 := bstep (se 1 (by rfl) ⟨1713284, by rfl⟩ : syracuseStep 2284379 = 3426569) B3426569
theorem B3660983 : Blo 1012602 3660983 := bstep (se 1 (by rfl) ⟨2745737, by rfl⟩ : syracuseStep 3660983 = 5491475) B5491475
theorem B2285135 : Blo 1012602 2285135 := bstep (se 1 (by rfl) ⟨1713851, by rfl⟩ : syracuseStep 2285135 = 3427703) B3427703
theorem B12345497 : Blo 1012602 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B2285855 : Blo 1012602 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B6939067 : Blo 1012602 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B4875005 : Blo 1012602 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B27779993 : Blo 1012602 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B2286503 : Blo 1012602 2286503 := bstep (se 1 (by rfl) ⟨1714877, by rfl⟩ : syracuseStep 2286503 = 3429755) B3429755
theorem B7300601 : Blo 1012602 7300601 := bstep (se 2 (by rfl) ⟨2737725, by rfl⟩ : syracuseStep 7300601 = 5475451) B5475451
theorem B1926823 : Blo 1012602 1926823 := bstep (se 1 (by rfl) ⟨1445117, by rfl⟩ : syracuseStep 1926823 = 2890235) B2890235
theorem B1140475 : Blo 1012602 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B1140511 : Blo 1012602 1140511 := bstep (se 1 (by rfl) ⟨855383, by rfl⟩ : syracuseStep 1140511 = 1710767) B1710767
theorem B6940513 : Blo 1012602 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B14805605 : Blo 1012602 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B4877003 : Blo 1012602 4877003 := bstep (se 1 (by rfl) ⟨3657752, by rfl⟩ : syracuseStep 4877003 = 7315505) B7315505
theorem B1141663 : Blo 1012602 1141663 := bstep (se 1 (by rfl) ⟨856247, by rfl⟩ : syracuseStep 1141663 = 1712495) B1712495
theorem B7695323 : Blo 1012602 7695323 := bstep (se 1 (by rfl) ⟨5771492, by rfl⟩ : syracuseStep 7695323 = 11542985) B11542985
theorem B1141807 : Blo 1012602 1141807 := bstep (se 1 (by rfl) ⟨856355, by rfl⟩ : syracuseStep 1141807 = 1712711) B1712711
theorem B1142095 : Blo 1012602 1142095 := bstep (se 1 (by rfl) ⟨856571, by rfl⟩ : syracuseStep 1142095 = 1713143) B1713143
theorem B1928767 : Blo 1012602 1928767 := bstep (se 1 (by rfl) ⟨1446575, by rfl⟩ : syracuseStep 1928767 = 2893151) B2893151
theorem B1142599 : Blo 1012602 1142599 := bstep (se 1 (by rfl) ⟨856949, by rfl⟩ : syracuseStep 1142599 = 1713899) B1713899
theorem B1372025 : Blo 1012602 1372025 := bstep (se 2 (by rfl) ⟨514509, by rfl⟩ : syracuseStep 1372025 = 1029019) B1029019
theorem B10973171 : Blo 1012602 10973171 := bstep (se 1 (by rfl) ⟨8229878, by rfl⟩ : syracuseStep 10973171 = 16459757) B16459757
theorem B1732795 : Blo 1012602 1732795 := bstep (se 1 (by rfl) ⟨1299596, by rfl⟩ : syracuseStep 1732795 = 2599193) B2599193
theorem B5140745 : Blo 1012602 5140745 := bstep (se 2 (by rfl) ⟨1927779, by rfl⟩ : syracuseStep 5140745 = 3855559) B3855559
theorem B1143247 : Blo 1012602 1143247 := bstep (se 1 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 1143247 = 1714871) B1714871
theorem B6583031 : Blo 1012602 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B1012647 : Blo 1012602 1012647 := bstep (se 1 (by rfl) ⟨759485, by rfl⟩ : syracuseStep 1012647 = 1518971) B1518971
theorem B1012731 : Blo 1012602 1012731 := bstep (se 1 (by rfl) ⟨759548, by rfl⟩ : syracuseStep 1012731 = 1519097) B1519097
theorem B1012799 : Blo 1012602 1012799 := bstep (se 1 (by rfl) ⟨759599, by rfl⟩ : syracuseStep 1012799 = 1519199) B1519199
theorem B8221769 : Blo 1012602 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B1012943 : Blo 1012602 1012943 := bstep (se 1 (by rfl) ⟨759707, by rfl⟩ : syracuseStep 1012943 = 1519415) B1519415
theorem B1013147 : Blo 1012602 1013147 := bstep (se 1 (by rfl) ⟨759860, by rfl⟩ : syracuseStep 1013147 = 1519721) B1519721
theorem B1013359 : Blo 1012602 1013359 := bstep (se 1 (by rfl) ⟨760019, by rfl⟩ : syracuseStep 1013359 = 1520039) B1520039
theorem B1013415 : Blo 1012602 1013415 := bstep (se 1 (by rfl) ⟨760061, by rfl⟩ : syracuseStep 1013415 = 1520123) B1520123
theorem B1013499 : Blo 1012602 1013499 := bstep (se 1 (by rfl) ⟨760124, by rfl⟩ : syracuseStep 1013499 = 1520249) B1520249
theorem B1013535 : Blo 1012602 1013535 := bstep (se 1 (by rfl) ⟨760151, by rfl⟩ : syracuseStep 1013535 = 1520303) B1520303
theorem B1013567 : Blo 1012602 1013567 := bstep (se 1 (by rfl) ⟨760175, by rfl⟩ : syracuseStep 1013567 = 1520351) B1520351
theorem B10417997 : Blo 1012602 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B1013743 : Blo 1012602 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B7305299 : Blo 1012602 7305299 := bstep (se 1 (by rfl) ⟨5478974, by rfl⟩ : syracuseStep 7305299 = 10957949) B10957949
theorem B1013915 : Blo 1012602 1013915 := bstep (se 1 (by rfl) ⟨760436, by rfl⟩ : syracuseStep 1013915 = 1520873) B1520873
theorem B1013951 : Blo 1012602 1013951 := bstep (se 1 (by rfl) ⟨760463, by rfl⟩ : syracuseStep 1013951 = 1520927) B1520927
theorem B1014063 : Blo 1012602 1014063 := bstep (se 1 (by rfl) ⟨760547, by rfl⟩ : syracuseStep 1014063 = 1521095) B1521095
theorem B1014299 : Blo 1012602 1014299 := bstep (se 1 (by rfl) ⟨760724, by rfl⟩ : syracuseStep 1014299 = 1521449) B1521449
theorem B1014303 : Blo 1012602 1014303 := bstep (se 1 (by rfl) ⟨760727, by rfl⟩ : syracuseStep 1014303 = 1521455) B1521455
theorem B1014619 : Blo 1012602 1014619 := bstep (se 1 (by rfl) ⟨760964, by rfl⟩ : syracuseStep 1014619 = 1521929) B1521929
theorem B1014687 : Blo 1012602 1014687 := bstep (se 1 (by rfl) ⟨761015, by rfl⟩ : syracuseStep 1014687 = 1522031) B1522031
theorem B19528613 : Blo 1012602 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B1014831 : Blo 1012602 1014831 := bstep (se 1 (by rfl) ⟨761123, by rfl⟩ : syracuseStep 1014831 = 1522247) B1522247
theorem B1014855 : Blo 1012602 1014855 := bstep (se 1 (by rfl) ⟨761141, by rfl⟩ : syracuseStep 1014855 = 1522283) B1522283
theorem B1015007 : Blo 1012602 1015007 := bstep (se 1 (by rfl) ⟨761255, by rfl⟩ : syracuseStep 1015007 = 1522511) B1522511
theorem B10976543 : Blo 1012602 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B24706471 : Blo 1012602 24706471 := bstep (se 1 (by rfl) ⟨18529853, by rfl⟩ : syracuseStep 24706471 = 37059707) B37059707
theorem B1015271 : Blo 1012602 1015271 := bstep (se 1 (by rfl) ⟨761453, by rfl⟩ : syracuseStep 1015271 = 1522907) B1522907
theorem B1015387 : Blo 1012602 1015387 := bstep (se 1 (by rfl) ⟨761540, by rfl⟩ : syracuseStep 1015387 = 1523081) B1523081
theorem B1015623 : Blo 1012602 1015623 := bstep (se 1 (by rfl) ⟨761717, by rfl⟩ : syracuseStep 1015623 = 1523435) B1523435
theorem B1015775 : Blo 1012602 1015775 := bstep (se 1 (by rfl) ⟨761831, by rfl⟩ : syracuseStep 1015775 = 1523663) B1523663
theorem B2162875 : Blo 1012602 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B1015999 : Blo 1012602 1015999 := bstep (se 1 (by rfl) ⟨761999, by rfl⟩ : syracuseStep 1015999 = 1523999) B1523999
theorem B1016015 : Blo 1012602 1016015 := bstep (se 1 (by rfl) ⟨762011, by rfl⟩ : syracuseStep 1016015 = 1524023) B1524023
theorem B1016063 : Blo 1012602 1016063 := bstep (se 1 (by rfl) ⟨762047, by rfl⟩ : syracuseStep 1016063 = 1524095) B1524095
theorem B1016111 : Blo 1012602 1016111 := bstep (se 1 (by rfl) ⟨762083, by rfl⟩ : syracuseStep 1016111 = 1524167) B1524167
theorem B1016347 : Blo 1012602 1016347 := bstep (se 1 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 1016347 = 1524521) B1524521
theorem B5145119 : Blo 1012602 5145119 := bstep (se 1 (by rfl) ⟨3858839, by rfl⟩ : syracuseStep 5145119 = 7717679) B7717679
theorem B1016351 : Blo 1012602 1016351 := bstep (se 1 (by rfl) ⟨762263, by rfl⟩ : syracuseStep 1016351 = 1524527) B1524527
theorem B1016431 : Blo 1012602 1016431 := bstep (se 1 (by rfl) ⟨762323, by rfl⟩ : syracuseStep 1016431 = 1524647) B1524647
theorem B7701155 : Blo 1012602 7701155 := bstep (se 1 (by rfl) ⟨5775866, by rfl⟩ : syracuseStep 7701155 = 11551733) B11551733
theorem B1016487 : Blo 1012602 1016487 := bstep (se 1 (by rfl) ⟨762365, by rfl⟩ : syracuseStep 1016487 = 1524731) B1524731
theorem B1016527 : Blo 1012602 1016527 := bstep (se 1 (by rfl) ⟨762395, by rfl⟩ : syracuseStep 1016527 = 1524791) B1524791
theorem B8782559 : Blo 1012602 8782559 := bstep (se 1 (by rfl) ⟨6586919, by rfl⟩ : syracuseStep 8782559 = 13173839) B13173839
theorem B2163935 : Blo 1012602 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B5768441 : Blo 1012602 5768441 := bstep (se 2 (by rfl) ⟨2163165, by rfl⟩ : syracuseStep 5768441 = 4326331) B4326331
theorem B7931209 : Blo 1012602 7931209 := bstep (se 2 (by rfl) ⟨2974203, by rfl⟩ : syracuseStep 7931209 = 5948407) B5948407
theorem B36996659 : Blo 1012602 36996659 := bstep (se 1 (by rfl) ⟨27747494, by rfl⟩ : syracuseStep 36996659 = 55494989) B55494989
theorem B4392667 : Blo 1012602 4392667 := bstep (se 1 (by rfl) ⟨3294500, by rfl⟩ : syracuseStep 4392667 = 6589001) B6589001
theorem B5211911 : Blo 1012602 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B2885519 : Blo 1012602 2885519 := bstep (se 1 (by rfl) ⟨2164139, by rfl⟩ : syracuseStep 2885519 = 4328279) B4328279
theorem B1083727 : Blo 1012602 1083727 := bstep (se 1 (by rfl) ⟨812795, by rfl⟩ : syracuseStep 1083727 = 1625591) B1625591
theorem B4327937 : Blo 1012602 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B2165609 : Blo 1012602 2165609 := bstep (se 2 (by rfl) ⟨812103, by rfl⟩ : syracuseStep 2165609 = 1624207) B1624207
theorem B7703585 : Blo 1012602 7703585 := bstep (se 2 (by rfl) ⟨2888844, by rfl⟩ : syracuseStep 7703585 = 5777689) B5777689
theorem B13012103 : Blo 1012602 13012103 := bstep (se 1 (by rfl) ⟨9759077, by rfl⟩ : syracuseStep 13012103 = 19518155) B19518155
theorem B6589835 : Blo 1012602 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B36966293 : Blo 1012602 36966293 := bstep (se 6 (by rfl) ⟨866397, by rfl⟩ : syracuseStep 36966293 = 1732795) B1732795
theorem B2166839 : Blo 1012602 2166839 := bstep (se 1 (by rfl) ⟨1625129, by rfl⟩ : syracuseStep 2166839 = 3250259) B3250259
theorem B2035867 : Blo 1012602 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B5771857 : Blo 1012602 5771857 := bstep (se 2 (by rfl) ⟨2164446, by rfl⟩ : syracuseStep 5771857 = 4328893) B4328893
theorem B1709039 : Blo 1012602 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B8230331 : Blo 1012602 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B2889209 : Blo 1012602 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B19732085 : Blo 1012602 19732085 := bstep (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) B1849883
theorem B3250003 : Blo 1012602 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B18519995 : Blo 1012602 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B5774273 : Blo 1012602 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B10951631 : Blo 1012602 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B9870403 : Blo 1012602 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B3251335 : Blo 1012602 3251335 := bstep (se 1 (by rfl) ⟨2438501, by rfl⟩ : syracuseStep 3251335 = 4877003) B4877003
theorem B1646057 : Blo 1012602 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B3251785 : Blo 1012602 3251785 := bstep (se 2 (by rfl) ⟨1219419, by rfl⟩ : syracuseStep 3251785 = 2438839) B2438839
theorem B7315447 : Blo 1012602 7315447 := bstep (se 1 (by rfl) ⟨5486585, by rfl⟩ : syracuseStep 7315447 = 10973171) B10973171
theorem B1712441 : Blo 1012602 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B5481179 : Blo 1012602 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B1712927 : Blo 1012602 1712927 := bstep (se 1 (by rfl) ⟨1284695, by rfl⟩ : syracuseStep 1712927 = 2569391) B2569391
theorem B3253117 : Blo 1012602 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B5776505 : Blo 1012602 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B1713737 : Blo 1012602 1713737 := bstep (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) B1285303
theorem B32941961 : Blo 1012602 32941961 := bstep (se 2 (by rfl) ⟨12353235, by rfl⟩ : syracuseStep 32941961 = 24706471) B24706471
theorem B13019075 : Blo 1012602 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B1714223 : Blo 1012602 1714223 := bstep (se 1 (by rfl) ⟨1285667, by rfl⟩ : syracuseStep 1714223 = 2571335) B2571335
theorem B1714297 : Blo 1012602 1714297 := bstep (se 2 (by rfl) ⟨642861, by rfl⟩ : syracuseStep 1714297 = 1285723) B1285723
theorem B7317695 : Blo 1012602 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B2894393 : Blo 1012602 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B3418847 : Blo 1012602 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B9252089 : Blo 1012602 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B40054283 : Blo 1012602 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B1519175 : Blo 1012602 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B7810667 : Blo 1012602 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B8793787 : Blo 1012602 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B1519355 : Blo 1012602 1519355 := bstep (se 1 (by rfl) ⟨1139516, by rfl⟩ : syracuseStep 1519355 = 2279033) B2279033
theorem B6500159 : Blo 1012602 6500159 := bstep (se 1 (by rfl) ⟨4875119, by rfl⟩ : syracuseStep 6500159 = 9750239) B9750239
theorem B1520027 : Blo 1012602 1520027 := bstep (se 1 (by rfl) ⟨1140020, by rfl⟩ : syracuseStep 1520027 = 2280041) B2280041
theorem B3846599 : Blo 1012602 3846599 := bstep (se 1 (by rfl) ⟨2884949, by rfl⟩ : syracuseStep 3846599 = 5769899) B5769899
theorem B9253439 : Blo 1012602 9253439 := bstep (se 1 (by rfl) ⟨6940079, by rfl⟩ : syracuseStep 9253439 = 13880159) B13880159
theorem B7418471 : Blo 1012602 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B2437867 : Blo 1012602 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B1520447 : Blo 1012602 1520447 := bstep (se 1 (by rfl) ⟨1140335, by rfl⟩ : syracuseStep 1520447 = 2280671) B2280671
theorem B2569097 : Blo 1012602 2569097 := bstep (se 2 (by rfl) ⟨963411, by rfl⟩ : syracuseStep 2569097 = 1926823) B1926823
theorem B1520591 : Blo 1012602 1520591 := bstep (se 1 (by rfl) ⟨1140443, by rfl⟩ : syracuseStep 1520591 = 2280887) B2280887
theorem B2601935 : Blo 1012602 2601935 := bstep (se 1 (by rfl) ⟨1951451, by rfl⟩ : syracuseStep 2601935 = 3902903) B3902903
theorem B1520633 : Blo 1012602 1520633 := bstep (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) B1140475
theorem B1520681 : Blo 1012602 1520681 := bstep (se 2 (by rfl) ⟨570255, by rfl⟩ : syracuseStep 1520681 = 1140511) B1140511
theorem B1520711 : Blo 1012602 1520711 := bstep (se 1 (by rfl) ⟨1140533, by rfl⟩ : syracuseStep 1520711 = 2281067) B2281067
theorem B8238185 : Blo 1012602 8238185 := bstep (se 2 (by rfl) ⟨3089319, by rfl⟩ : syracuseStep 8238185 = 6178639) B6178639
theorem B3847297 : Blo 1012602 3847297 := bstep (se 2 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 3847297 = 2885473) B2885473
theorem B9254017 : Blo 1012602 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B5551325 : Blo 1012602 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B1520891 : Blo 1012602 1520891 := bstep (se 1 (by rfl) ⟨1140668, by rfl⟩ : syracuseStep 1520891 = 2281337) B2281337
theorem B3290863 : Blo 1012602 3290863 := bstep (se 1 (by rfl) ⟨2468147, by rfl⟩ : syracuseStep 3290863 = 4936295) B4936295
theorem B3422249 : Blo 1012602 3422249 := bstep (se 2 (by rfl) ⟨1283343, by rfl⟩ : syracuseStep 3422249 = 2566687) B2566687
theorem B1522127 : Blo 1012602 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B1522217 : Blo 1012602 1522217 := bstep (se 2 (by rfl) ⟨570831, by rfl⟩ : syracuseStep 1522217 = 1141663) B1141663
theorem B4340411 : Blo 1012602 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B1522409 : Blo 1012602 1522409 := bstep (se 2 (by rfl) ⟨570903, by rfl⟩ : syracuseStep 1522409 = 1141807) B1141807
theorem B5127137 : Blo 1012602 5127137 := bstep (se 2 (by rfl) ⟨1922676, by rfl⟩ : syracuseStep 5127137 = 3845353) B3845353
theorem B1522793 : Blo 1012602 1522793 := bstep (se 2 (by rfl) ⟨571047, by rfl⟩ : syracuseStep 1522793 = 1142095) B1142095
theorem B1522919 : Blo 1012602 1522919 := bstep (se 1 (by rfl) ⟨1142189, by rfl⟩ : syracuseStep 1522919 = 2284379) B2284379
theorem B3849545 : Blo 1012602 3849545 := bstep (se 2 (by rfl) ⟨1443579, by rfl⟩ : syracuseStep 3849545 = 2887159) B2887159
theorem B2571689 : Blo 1012602 2571689 := bstep (se 2 (by rfl) ⟨964383, by rfl⟩ : syracuseStep 2571689 = 1928767) B1928767
theorem B2440655 : Blo 1012602 2440655 := bstep (se 1 (by rfl) ⟨1830491, by rfl⟩ : syracuseStep 2440655 = 3660983) B3660983
theorem B6602303 : Blo 1012602 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B1523423 : Blo 1012602 1523423 := bstep (se 1 (by rfl) ⟨1142567, by rfl⟩ : syracuseStep 1523423 = 2285135) B2285135
theorem B1523465 : Blo 1012602 1523465 := bstep (se 2 (by rfl) ⟨571299, by rfl⟩ : syracuseStep 1523465 = 1142599) B1142599
theorem B1523903 : Blo 1012602 1523903 := bstep (se 1 (by rfl) ⟨1142927, by rfl⟩ : syracuseStep 1523903 = 2285855) B2285855
theorem B17842717 : Blo 1012602 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B1524329 : Blo 1012602 1524329 := bstep (se 2 (by rfl) ⟨571623, by rfl⟩ : syracuseStep 1524329 = 1143247) B1143247
theorem B1524335 : Blo 1012602 1524335 := bstep (se 1 (by rfl) ⟨1143251, by rfl⟩ : syracuseStep 1524335 = 2286503) B2286503
theorem B2933435 : Blo 1012602 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B4867067 : Blo 1012602 4867067 := bstep (se 1 (by rfl) ⟨3650300, by rfl⟩ : syracuseStep 4867067 = 7300601) B7300601
theorem B2278511 : Blo 1012602 2278511 := bstep (se 1 (by rfl) ⟨1708883, by rfl⟩ : syracuseStep 2278511 = 3417767) B3417767
theorem B3851657 : Blo 1012602 3851657 := bstep (se 2 (by rfl) ⟨1444371, by rfl⟩ : syracuseStep 3851657 = 2888743) B2888743
theorem B3425705 : Blo 1012602 3425705 := bstep (se 2 (by rfl) ⟨1284639, by rfl⟩ : syracuseStep 3425705 = 2569279) B2569279
theorem B5490089 : Blo 1012602 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B2278907 : Blo 1012602 2278907 := bstep (se 1 (by rfl) ⟨1709180, by rfl⟩ : syracuseStep 2278907 = 3418361) B3418361
theorem B2278943 : Blo 1012602 2278943 := bstep (se 1 (by rfl) ⟨1709207, by rfl⟩ : syracuseStep 2278943 = 3418415) B3418415
theorem B2279087 : Blo 1012602 2279087 := bstep (se 1 (by rfl) ⟨1709315, by rfl⟩ : syracuseStep 2279087 = 3418631) B3418631
theorem B5130215 : Blo 1012602 5130215 := bstep (se 1 (by rfl) ⟨3847661, by rfl⟩ : syracuseStep 5130215 = 7695323) B7695323
theorem B2279519 : Blo 1012602 2279519 := bstep (se 1 (by rfl) ⟨1709639, by rfl⟩ : syracuseStep 2279519 = 3419279) B3419279
theorem B2279807 : Blo 1012602 2279807 := bstep (se 1 (by rfl) ⟨1709855, by rfl⟩ : syracuseStep 2279807 = 3419711) B3419711
theorem B1952351 : Blo 1012602 1952351 := bstep (se 1 (by rfl) ⟨1464263, by rfl⟩ : syracuseStep 1952351 = 2928527) B2928527
theorem B2280275 : Blo 1012602 2280275 := bstep (se 1 (by rfl) ⟨1710206, by rfl⟩ : syracuseStep 2280275 = 3420413) B3420413
theorem B3427163 : Blo 1012602 3427163 := bstep (se 1 (by rfl) ⟨2570372, by rfl⟩ : syracuseStep 3427163 = 5140745) B5140745
theorem B8670361 : Blo 1012602 8670361 := bstep (se 2 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 8670361 = 6502771) B6502771
theorem B7326895 : Blo 1012602 7326895 := bstep (se 1 (by rfl) ⟨5495171, by rfl⟩ : syracuseStep 7326895 = 10990343) B10990343
theorem B2280635 : Blo 1012602 2280635 := bstep (se 1 (by rfl) ⟨1710476, by rfl⟩ : syracuseStep 2280635 = 3420953) B3420953
theorem B2280815 : Blo 1012602 2280815 := bstep (se 1 (by rfl) ⟨1710611, by rfl⟩ : syracuseStep 2280815 = 3421223) B3421223
theorem B3854375 : Blo 1012602 3854375 := bstep (se 1 (by rfl) ⟨2890781, by rfl⟩ : syracuseStep 3854375 = 5781563) B5781563
theorem B4870199 : Blo 1012602 4870199 := bstep (se 1 (by rfl) ⟨3652649, by rfl⟩ : syracuseStep 4870199 = 7305299) B7305299
theorem B2281535 : Blo 1012602 2281535 := bstep (se 1 (by rfl) ⟨1711151, by rfl⟩ : syracuseStep 2281535 = 3422303) B3422303
theorem B2281769 : Blo 1012602 2281769 := bstep (se 2 (by rfl) ⟨855663, by rfl⟩ : syracuseStep 2281769 = 1711327) B1711327
theorem B2282039 : Blo 1012602 2282039 := bstep (se 1 (by rfl) ⟨1711529, by rfl⟩ : syracuseStep 2282039 = 3423059) B3423059
theorem B2282345 : Blo 1012602 2282345 := bstep (se 2 (by rfl) ⟨855879, by rfl⟩ : syracuseStep 2282345 = 1711759) B1711759
theorem B2282399 : Blo 1012602 2282399 := bstep (se 1 (by rfl) ⟨1711799, by rfl⟩ : syracuseStep 2282399 = 3423599) B3423599
theorem B3658733 : Blo 1012602 3658733 := bstep (se 3 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 3658733 = 1372025) B1372025
theorem B3855347 : Blo 1012602 3855347 := bstep (se 1 (by rfl) ⟨2891510, by rfl⟩ : syracuseStep 3855347 = 5783021) B5783021
theorem B1627231 : Blo 1012602 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B2282651 : Blo 1012602 2282651 := bstep (se 1 (by rfl) ⟨1711988, by rfl⟩ : syracuseStep 2282651 = 3423977) B3423977
theorem B3430025 : Blo 1012602 3430025 := bstep (se 2 (by rfl) ⟨1286259, by rfl⟩ : syracuseStep 3430025 = 2572519) B2572519
theorem B2283227 : Blo 1012602 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B2283335 : Blo 1012602 2283335 := bstep (se 1 (by rfl) ⟨1712501, by rfl⟩ : syracuseStep 2283335 = 3425003) B3425003
theorem B8673095 : Blo 1012602 8673095 := bstep (se 1 (by rfl) ⟨6504821, by rfl⟩ : syracuseStep 8673095 = 13009643) B13009643
theorem B55498679 : Blo 1012602 55498679 := bstep (se 1 (by rfl) ⟨41624009, by rfl⟩ : syracuseStep 55498679 = 83248019) B83248019
theorem B1923041 : Blo 1012602 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B810244133 : Blo 1012602 810244133 := bstep (se 4 (by rfl) ⟨75960387, by rfl⟩ : syracuseStep 810244133 = 151920775) B151920775
theorem B2742311 : Blo 1012602 2742311 := bstep (se 1 (by rfl) ⟨2056733, by rfl⟩ : syracuseStep 2742311 = 4113467) B4113467
theorem B78960739 : Blo 1012602 78960739 := bstep (se 1 (by rfl) ⟨59220554, by rfl⟩ : syracuseStep 78960739 = 118441109) B118441109
theorem B3856531 : Blo 1012602 3856531 := bstep (se 1 (by rfl) ⟨2892398, by rfl⟩ : syracuseStep 3856531 = 5784797) B5784797
theorem B3430619 : Blo 1012602 3430619 := bstep (se 1 (by rfl) ⟨2572964, by rfl⟩ : syracuseStep 3430619 = 5145929) B5145929
theorem B4872545 : Blo 1012602 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B5134751 : Blo 1012602 5134751 := bstep (se 1 (by rfl) ⟨3851063, by rfl⟩ : syracuseStep 5134751 = 7702127) B7702127
theorem B3430889 : Blo 1012602 3430889 := bstep (se 2 (by rfl) ⟨1286583, by rfl⟩ : syracuseStep 3430889 = 2573167) B2573167
theorem B2284343 : Blo 1012602 2284343 := bstep (se 1 (by rfl) ⟨1713257, by rfl⟩ : syracuseStep 2284343 = 3426515) B3426515
theorem B29678561 : Blo 1012602 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B2284523 : Blo 1012602 2284523 := bstep (se 1 (by rfl) ⟨1713392, by rfl⟩ : syracuseStep 2284523 = 3426785) B3426785
theorem B18538105 : Blo 1012602 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B4218493 : Blo 1012602 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B3858263 : Blo 1012602 3858263 := bstep (se 1 (by rfl) ⟨2893697, by rfl⟩ : syracuseStep 3858263 = 5787395) B5787395
theorem B2285423 : Blo 1012602 2285423 := bstep (se 1 (by rfl) ⟨1714067, by rfl⟩ : syracuseStep 2285423 = 3428135) B3428135
theorem B2286107 : Blo 1012602 2286107 := bstep (se 1 (by rfl) ⟨1714580, by rfl⟩ : syracuseStep 2286107 = 3429161) B3429161
theorem B6513281 : Blo 1012602 6513281 := bstep (se 2 (by rfl) ⟨2442480, by rfl⟩ : syracuseStep 6513281 = 4884961) B4884961
theorem B4121263 : Blo 1012602 4121263 := bstep (se 1 (by rfl) ⟨3090947, by rfl⟩ : syracuseStep 4121263 = 6181895) B6181895
theorem B2286287 : Blo 1012602 2286287 := bstep (se 1 (by rfl) ⟨1714715, by rfl⟩ : syracuseStep 2286287 = 3429431) B3429431
theorem B1925851 : Blo 1012602 1925851 := bstep (se 1 (by rfl) ⟨1444388, by rfl⟩ : syracuseStep 1925851 = 2888777) B2888777
theorem B2286665 : Blo 1012602 2286665 := bstep (se 2 (by rfl) ⟨857499, by rfl⟩ : syracuseStep 2286665 = 1714999) B1714999
theorem B1139935 : Blo 1012602 1139935 := bstep (se 1 (by rfl) ⟨854951, by rfl⟩ : syracuseStep 1139935 = 1709903) B1709903
theorem B11134199 : Blo 1012602 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B5138315 : Blo 1012602 5138315 := bstep (se 1 (by rfl) ⟨3853736, by rfl⟩ : syracuseStep 5138315 = 7707473) B7707473
theorem B1140763 : Blo 1012602 1140763 := bstep (se 1 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 1140763 = 1711145) B1711145
theorem B22243475 : Blo 1012602 22243475 := bstep (se 1 (by rfl) ⟨16682606, by rfl⟩ : syracuseStep 22243475 = 33365213) B33365213
theorem B27781325 : Blo 1012602 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B8218883 : Blo 1012602 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B5138963 : Blo 1012602 5138963 := bstep (se 1 (by rfl) ⟨3854222, by rfl⟩ : syracuseStep 5138963 = 7708445) B7708445
theorem B2059433 : Blo 1012602 2059433 := bstep (se 2 (by rfl) ⟨772287, by rfl⟩ : syracuseStep 2059433 = 1544575) B1544575
theorem B5139935 : Blo 1012602 5139935 := bstep (se 1 (by rfl) ⟨3854951, by rfl⟩ : syracuseStep 5139935 = 7709903) B7709903
theorem B1142239 : Blo 1012602 1142239 := bstep (se 1 (by rfl) ⟨856679, by rfl⟩ : syracuseStep 1142239 = 1713359) B1713359
theorem B2059847 : Blo 1012602 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1142779 : Blo 1012602 1142779 := bstep (se 1 (by rfl) ⟨857084, by rfl⟩ : syracuseStep 1142779 = 1714169) B1714169
theorem B1142887 : Blo 1012602 1142887 := bstep (se 1 (by rfl) ⟨857165, by rfl⟩ : syracuseStep 1142887 = 1714331) B1714331
theorem B1929359 : Blo 1012602 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B1142959 : Blo 1012602 1142959 := bstep (se 1 (by rfl) ⟨857219, by rfl⟩ : syracuseStep 1142959 = 1714439) B1714439
theorem B1732871 : Blo 1012602 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B14610937 : Blo 1012602 14610937 := bstep (se 2 (by rfl) ⟨5479101, by rfl⟩ : syracuseStep 14610937 = 10958203) B10958203
theorem B25981559 : Blo 1012602 25981559 := bstep (se 1 (by rfl) ⟨19486169, by rfl⟩ : syracuseStep 25981559 = 38972339) B38972339
theorem B1143643 : Blo 1012602 1143643 := bstep (se 1 (by rfl) ⟨857732, by rfl⟩ : syracuseStep 1143643 = 1715465) B1715465
theorem B1012639 : Blo 1012602 1012639 := bstep (se 1 (by rfl) ⟨759479, by rfl⟩ : syracuseStep 1012639 = 1518959) B1518959
theorem B1012719 : Blo 1012602 1012719 := bstep (se 1 (by rfl) ⟨759539, by rfl⟩ : syracuseStep 1012719 = 1519079) B1519079
theorem B1012807 : Blo 1012602 1012807 := bstep (se 1 (by rfl) ⟨759605, by rfl⟩ : syracuseStep 1012807 = 1519211) B1519211
theorem B1012891 : Blo 1012602 1012891 := bstep (se 1 (by rfl) ⟨759668, by rfl⟩ : syracuseStep 1012891 = 1519337) B1519337
theorem B1012987 : Blo 1012602 1012987 := bstep (se 1 (by rfl) ⟨759740, by rfl⟩ : syracuseStep 1012987 = 1519481) B1519481
theorem B1013055 : Blo 1012602 1013055 := bstep (se 1 (by rfl) ⟨759791, by rfl⟩ : syracuseStep 1013055 = 1519583) B1519583
theorem B5141879 : Blo 1012602 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B1013223 : Blo 1012602 1013223 := bstep (se 1 (by rfl) ⟨759917, by rfl⟩ : syracuseStep 1013223 = 1519835) B1519835
theorem B1013231 : Blo 1012602 1013231 := bstep (se 1 (by rfl) ⟨759923, by rfl⟩ : syracuseStep 1013231 = 1519847) B1519847
theorem B1013339 : Blo 1012602 1013339 := bstep (se 1 (by rfl) ⟨760004, by rfl⟩ : syracuseStep 1013339 = 1520009) B1520009
theorem B11695769 : Blo 1012602 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B1013403 : Blo 1012602 1013403 := bstep (se 1 (by rfl) ⟨760052, by rfl⟩ : syracuseStep 1013403 = 1520105) B1520105
theorem B1013487 : Blo 1012602 1013487 := bstep (se 1 (by rfl) ⟨760115, by rfl⟩ : syracuseStep 1013487 = 1520231) B1520231
theorem B1013575 : Blo 1012602 1013575 := bstep (se 1 (by rfl) ⟨760181, by rfl⟩ : syracuseStep 1013575 = 1520363) B1520363
theorem B4388687 : Blo 1012602 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B1013595 : Blo 1012602 1013595 := bstep (se 1 (by rfl) ⟨760196, by rfl⟩ : syracuseStep 1013595 = 1520393) B1520393
theorem B1013663 : Blo 1012602 1013663 := bstep (se 1 (by rfl) ⟨760247, by rfl⟩ : syracuseStep 1013663 = 1520495) B1520495
theorem B1013831 : Blo 1012602 1013831 := bstep (se 1 (by rfl) ⟨760373, by rfl⟩ : syracuseStep 1013831 = 1520747) B1520747
theorem B5142689 : Blo 1012602 5142689 := bstep (se 2 (by rfl) ⟨1928508, by rfl⟩ : syracuseStep 5142689 = 3857017) B3857017
theorem B1013991 : Blo 1012602 1013991 := bstep (se 1 (by rfl) ⟨760493, by rfl⟩ : syracuseStep 1013991 = 1520987) B1520987
theorem B7698725 : Blo 1012602 7698725 := bstep (se 4 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 7698725 = 1443511) B1443511
theorem B1014175 : Blo 1012602 1014175 := bstep (se 1 (by rfl) ⟨760631, by rfl⟩ : syracuseStep 1014175 = 1521263) B1521263
theorem B1014223 : Blo 1012602 1014223 := bstep (se 1 (by rfl) ⟨760667, by rfl⟩ : syracuseStep 1014223 = 1521335) B1521335
theorem B1014247 : Blo 1012602 1014247 := bstep (se 1 (by rfl) ⟨760685, by rfl⟩ : syracuseStep 1014247 = 1521371) B1521371
theorem B1014363 : Blo 1012602 1014363 := bstep (se 1 (by rfl) ⟨760772, by rfl⟩ : syracuseStep 1014363 = 1521545) B1521545
theorem B1014431 : Blo 1012602 1014431 := bstep (se 1 (by rfl) ⟨760823, by rfl⟩ : syracuseStep 1014431 = 1521647) B1521647
theorem B1014599 : Blo 1012602 1014599 := bstep (se 1 (by rfl) ⟨760949, by rfl⟩ : syracuseStep 1014599 = 1521899) B1521899
theorem B1014639 : Blo 1012602 1014639 := bstep (se 1 (by rfl) ⟨760979, by rfl⟩ : syracuseStep 1014639 = 1521959) B1521959
theorem B1014695 : Blo 1012602 1014695 := bstep (se 1 (by rfl) ⟨761021, by rfl⟩ : syracuseStep 1014695 = 1522043) B1522043
theorem B1014875 : Blo 1012602 1014875 := bstep (se 1 (by rfl) ⟨761156, by rfl⟩ : syracuseStep 1014875 = 1522313) B1522313
theorem B19758275 : Blo 1012602 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1014991 : Blo 1012602 1014991 := bstep (se 1 (by rfl) ⟨761243, by rfl⟩ : syracuseStep 1014991 = 1522487) B1522487
theorem B1015015 : Blo 1012602 1015015 := bstep (se 1 (by rfl) ⟨761261, by rfl⟩ : syracuseStep 1015015 = 1522523) B1522523
theorem B1015111 : Blo 1012602 1015111 := bstep (se 1 (by rfl) ⟨761333, by rfl⟩ : syracuseStep 1015111 = 1522667) B1522667
theorem B7306685 : Blo 1012602 7306685 := bstep (se 3 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 7306685 = 2740007) B2740007
theorem B1015247 : Blo 1012602 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B1015407 : Blo 1012602 1015407 := bstep (se 1 (by rfl) ⟨761555, by rfl⟩ : syracuseStep 1015407 = 1523111) B1523111
theorem B1015463 : Blo 1012602 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B10714799 : Blo 1012602 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B1015527 : Blo 1012602 1015527 := bstep (se 1 (by rfl) ⟨761645, by rfl⟩ : syracuseStep 1015527 = 1523291) B1523291
theorem B66780929 : Blo 1012602 66780929 := bstep (se 2 (by rfl) ⟨25042848, by rfl⟩ : syracuseStep 66780929 = 50085697) B50085697
theorem B1015583 : Blo 1012602 1015583 := bstep (se 1 (by rfl) ⟨761687, by rfl⟩ : syracuseStep 1015583 = 1523375) B1523375
theorem B1015663 : Blo 1012602 1015663 := bstep (se 1 (by rfl) ⟨761747, by rfl⟩ : syracuseStep 1015663 = 1523495) B1523495
theorem B1015719 : Blo 1012602 1015719 := bstep (se 1 (by rfl) ⟨761789, by rfl⟩ : syracuseStep 1015719 = 1523579) B1523579
theorem B1015935 : Blo 1012602 1015935 := bstep (se 1 (by rfl) ⟨761951, by rfl⟩ : syracuseStep 1015935 = 1523903) B1523903
theorem B2883833 : Blo 1012602 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B5144957 : Blo 1012602 5144957 := bstep (se 3 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 5144957 = 1929359) B1929359
theorem B1016219 : Blo 1012602 1016219 := bstep (se 1 (by rfl) ⟨762164, by rfl⟩ : syracuseStep 1016219 = 1524329) B1524329
theorem B1016223 : Blo 1012602 1016223 := bstep (se 1 (by rfl) ⟨762167, by rfl⟩ : syracuseStep 1016223 = 1524335) B1524335
theorem B3244711 : Blo 1012602 3244711 := bstep (se 1 (by rfl) ⟨2433533, by rfl⟩ : syracuseStep 3244711 = 4867067) B4867067
theorem B4620989 : Blo 1012602 4620989 := bstep (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) B1732871
theorem B23790289 : Blo 1012602 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B1442623 : Blo 1012602 1442623 := bstep (se 1 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 1442623 = 2163935) B2163935
theorem B2885291 : Blo 1012602 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B1443739 : Blo 1012602 1443739 := bstep (se 1 (by rfl) ⟨1082804, by rfl⟩ : syracuseStep 1443739 = 2165609) B2165609
theorem B4393223 : Blo 1012602 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B24644195 : Blo 1012602 24644195 := bstep (se 1 (by rfl) ⟨18483146, by rfl⟩ : syracuseStep 24644195 = 36966293) B36966293
theorem B3246799 : Blo 1012602 3246799 := bstep (se 1 (by rfl) ⟨2435099, by rfl⟩ : syracuseStep 3246799 = 4870199) B4870199
theorem B1444559 : Blo 1012602 1444559 := bstep (se 1 (by rfl) ⟨1083419, by rfl⟩ : syracuseStep 1444559 = 2166839) B2166839
theorem B1444969 : Blo 1012602 1444969 := bstep (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) B1083727
theorem B36999119 : Blo 1012602 36999119 := bstep (se 1 (by rfl) ⟨27749339, by rfl⟩ : syracuseStep 36999119 = 55498679) B55498679
theorem B7704557 : Blo 1012602 7704557 := bstep (se 3 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 7704557 = 2889209) B2889209
theorem B9769193 : Blo 1012602 9769193 := bstep (se 2 (by rfl) ⟨3663447, by rfl⟩ : syracuseStep 9769193 = 7326895) B7326895
theorem B3248363 : Blo 1012602 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B13898429 : Blo 1012602 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B21961307 : Blo 1012602 21961307 := bstep (se 1 (by rfl) ⟨16470980, by rfl⟩ : syracuseStep 21961307 = 32941961) B32941961
theorem B2169641 : Blo 1012602 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B18520883 : Blo 1012602 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B5479255 : Blo 1012602 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B6168059 : Blo 1012602 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B4333337 : Blo 1012602 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B4333439 : Blo 1012602 4333439 := bstep (se 1 (by rfl) ⟨3250079, by rfl⟩ : syracuseStep 4333439 = 6500159) B6500159
theorem B2564399 : Blo 1012602 2564399 := bstep (se 1 (by rfl) ⟨1923299, by rfl⟩ : syracuseStep 2564399 = 3846599) B3846599
theorem B6168959 : Blo 1012602 6168959 := bstep (se 1 (by rfl) ⟨4626719, by rfl⟩ : syracuseStep 6168959 = 9253439) B9253439
theorem B1712731 : Blo 1012602 1712731 := bstep (se 1 (by rfl) ⟨1284548, by rfl⟩ : syracuseStep 1712731 = 2569097) B2569097
theorem B2925791 : Blo 1012602 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B4335113 : Blo 1012602 4335113 := bstep (se 2 (by rfl) ⟨1625667, by rfl⟩ : syracuseStep 4335113 = 3251335) B3251335
theorem B2893607 : Blo 1012602 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B3418091 : Blo 1012602 3418091 := bstep (se 1 (by rfl) ⟨2563568, by rfl⟩ : syracuseStep 3418091 = 5127137) B5127137
theorem B4335713 : Blo 1012602 4335713 := bstep (se 2 (by rfl) ⟨1625892, by rfl⟩ : syracuseStep 4335713 = 3251785) B3251785
theorem B24717473 : Blo 1012602 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B2566363 : Blo 1012602 2566363 := bstep (se 1 (by rfl) ⟨1924772, by rfl⟩ : syracuseStep 2566363 = 3849545) B3849545
theorem B1714459 : Blo 1012602 1714459 := bstep (se 1 (by rfl) ⟨1285844, by rfl⟩ : syracuseStep 1714459 = 2571689) B2571689
theorem B4401535 : Blo 1012602 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B1519007 : Blo 1012602 1519007 := bstep (se 1 (by rfl) ⟨1139255, by rfl⟩ : syracuseStep 1519007 = 2278511) B2278511
theorem B3845627 : Blo 1012602 3845627 := bstep (se 1 (by rfl) ⟨2884220, by rfl⟩ : syracuseStep 3845627 = 5768441) B5768441
theorem B2567771 : Blo 1012602 2567771 := bstep (se 1 (by rfl) ⟨1925828, by rfl⟩ : syracuseStep 2567771 = 3851657) B3851657
theorem B2567801 : Blo 1012602 2567801 := bstep (se 2 (by rfl) ⟨962925, by rfl⟩ : syracuseStep 2567801 = 1925851) B1925851
theorem B1519271 : Blo 1012602 1519271 := bstep (se 1 (by rfl) ⟨1139453, by rfl⟩ : syracuseStep 1519271 = 2278907) B2278907
theorem B1519295 : Blo 1012602 1519295 := bstep (se 1 (by rfl) ⟨1139471, by rfl⟩ : syracuseStep 1519295 = 2278943) B2278943
theorem B1519391 : Blo 1012602 1519391 := bstep (se 1 (by rfl) ⟨1139543, by rfl⟩ : syracuseStep 1519391 = 2279087) B2279087
theorem B4337489 : Blo 1012602 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B3420143 : Blo 1012602 3420143 := bstep (se 1 (by rfl) ⟨2565107, by rfl⟩ : syracuseStep 3420143 = 5130215) B5130215
theorem B1519679 : Blo 1012602 1519679 := bstep (se 1 (by rfl) ⟨1139759, by rfl⟩ : syracuseStep 1519679 = 2279519) B2279519
theorem B1519871 : Blo 1012602 1519871 := bstep (se 1 (by rfl) ⟨1139903, by rfl⟩ : syracuseStep 1519871 = 2279807) B2279807
theorem B1519913 : Blo 1012602 1519913 := bstep (se 2 (by rfl) ⟨569967, by rfl⟩ : syracuseStep 1519913 = 1139935) B1139935
theorem B1520183 : Blo 1012602 1520183 := bstep (se 1 (by rfl) ⟨1140137, by rfl⟩ : syracuseStep 1520183 = 2280275) B2280275
theorem B1520423 : Blo 1012602 1520423 := bstep (se 1 (by rfl) ⟨1140317, by rfl⟩ : syracuseStep 1520423 = 2280635) B2280635
theorem B1520543 : Blo 1012602 1520543 := bstep (se 1 (by rfl) ⟨1140407, by rfl⟩ : syracuseStep 1520543 = 2280815) B2280815
theorem B2569583 : Blo 1012602 2569583 := bstep (se 1 (by rfl) ⟨1927187, by rfl⟩ : syracuseStep 2569583 = 3854375) B3854375
theorem B1521017 : Blo 1012602 1521017 := bstep (se 2 (by rfl) ⟨570381, by rfl⟩ : syracuseStep 1521017 = 1140763) B1140763
theorem B1521023 : Blo 1012602 1521023 := bstep (se 1 (by rfl) ⟨1140767, by rfl⟩ : syracuseStep 1521023 = 2281535) B2281535
theorem B1521179 : Blo 1012602 1521179 := bstep (se 1 (by rfl) ⟨1140884, by rfl⟩ : syracuseStep 1521179 = 2281769) B2281769
theorem B1521359 : Blo 1012602 1521359 := bstep (se 1 (by rfl) ⟨1141019, by rfl⟩ : syracuseStep 1521359 = 2282039) B2282039
theorem B1521563 : Blo 1012602 1521563 := bstep (se 1 (by rfl) ⟨1141172, by rfl⟩ : syracuseStep 1521563 = 2282345) B2282345
theorem B1521599 : Blo 1012602 1521599 := bstep (se 1 (by rfl) ⟨1141199, by rfl⟩ : syracuseStep 1521599 = 2282399) B2282399
theorem B2439155 : Blo 1012602 2439155 := bstep (se 1 (by rfl) ⟨1829366, by rfl⟩ : syracuseStep 2439155 = 3658733) B3658733
theorem B2570231 : Blo 1012602 2570231 := bstep (se 1 (by rfl) ⟨1927673, by rfl⟩ : syracuseStep 2570231 = 3855347) B3855347
theorem B1521767 : Blo 1012602 1521767 := bstep (se 1 (by rfl) ⟨1141325, by rfl⟩ : syracuseStep 1521767 = 2282651) B2282651
theorem B5486887 : Blo 1012602 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B13154723 : Blo 1012602 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B1522151 : Blo 1012602 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B1522223 : Blo 1012602 1522223 := bstep (se 1 (by rfl) ⟨1141667, by rfl⟩ : syracuseStep 1522223 = 2283335) B2283335
theorem B5782063 : Blo 1012602 5782063 := bstep (se 1 (by rfl) ⟨4336547, by rfl⟩ : syracuseStep 5782063 = 8673095) B8673095
theorem B540162755 : Blo 1012602 540162755 := bstep (se 1 (by rfl) ⟨405122066, by rfl⟩ : syracuseStep 540162755 = 810244133) B810244133
theorem B3423167 : Blo 1012602 3423167 := bstep (se 1 (by rfl) ⟨2567375, by rfl⟩ : syracuseStep 3423167 = 5134751) B5134751
theorem B1522895 : Blo 1012602 1522895 := bstep (se 1 (by rfl) ⟨1142171, by rfl⟩ : syracuseStep 1522895 = 2284343) B2284343
theorem B1522985 : Blo 1012602 1522985 := bstep (se 2 (by rfl) ⟨571119, by rfl⟩ : syracuseStep 1522985 = 1142239) B1142239
theorem B3849515 : Blo 1012602 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B1523015 : Blo 1012602 1523015 := bstep (se 1 (by rfl) ⟨1142261, by rfl⟩ : syracuseStep 1523015 = 2284523) B2284523
theorem B1097371 : Blo 1012602 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B2572175 : Blo 1012602 2572175 := bstep (se 1 (by rfl) ⟨1929131, by rfl⟩ : syracuseStep 2572175 = 3858263) B3858263
theorem B1523615 : Blo 1012602 1523615 := bstep (se 1 (by rfl) ⟨1142711, by rfl⟩ : syracuseStep 1523615 = 2285423) B2285423
theorem B5128109 : Blo 1012602 5128109 := bstep (se 3 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 5128109 = 1923041) B1923041
theorem B1523705 : Blo 1012602 1523705 := bstep (se 2 (by rfl) ⟨571389, by rfl⟩ : syracuseStep 1523705 = 1142779) B1142779
theorem B1523849 : Blo 1012602 1523849 := bstep (se 2 (by rfl) ⟨571443, by rfl⟩ : syracuseStep 1523849 = 1142887) B1142887
theorem B1523945 : Blo 1012602 1523945 := bstep (se 2 (by rfl) ⟨571479, by rfl⟩ : syracuseStep 1523945 = 1142959) B1142959
theorem B1524071 : Blo 1012602 1524071 := bstep (se 1 (by rfl) ⟨1143053, by rfl⟩ : syracuseStep 1524071 = 2286107) B2286107
theorem B4342187 : Blo 1012602 4342187 := bstep (se 1 (by rfl) ⟨3256640, by rfl⟩ : syracuseStep 4342187 = 6513281) B6513281
theorem B1524191 : Blo 1012602 1524191 := bstep (se 1 (by rfl) ⟨1143143, by rfl⟩ : syracuseStep 1524191 = 2286287) B2286287
theorem B3654119 : Blo 1012602 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B19481249 : Blo 1012602 19481249 := bstep (se 2 (by rfl) ⟨7305468, by rfl⟩ : syracuseStep 19481249 = 14610937) B14610937
theorem B1524443 : Blo 1012602 1524443 := bstep (se 1 (by rfl) ⟨1143332, by rfl⟩ : syracuseStep 1524443 = 2286665) B2286665
theorem B3851003 : Blo 1012602 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B7422799 : Blo 1012602 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B1524857 : Blo 1012602 1524857 := bstep (se 2 (by rfl) ⟨571821, by rfl⟩ : syracuseStep 1524857 = 1143643) B1143643
theorem B3425543 : Blo 1012602 3425543 := bstep (se 1 (by rfl) ⟨2569157, by rfl⟩ : syracuseStep 3425543 = 5138315) B5138315
theorem B14828983 : Blo 1012602 14828983 := bstep (se 1 (by rfl) ⟨11121737, by rfl⟩ : syracuseStep 14828983 = 22243475) B22243475
theorem B5129729 : Blo 1012602 5129729 := bstep (se 2 (by rfl) ⟨1923648, by rfl⟩ : syracuseStep 5129729 = 3847297) B3847297
theorem B12338689 : Blo 1012602 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B3425975 : Blo 1012602 3425975 := bstep (se 1 (by rfl) ⟨2569481, by rfl⟩ : syracuseStep 3425975 = 5138963) B5138963
theorem B2279231 : Blo 1012602 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B3426623 : Blo 1012602 3426623 := bstep (se 1 (by rfl) ⟨2569967, by rfl⟩ : syracuseStep 3426623 = 5139935) B5139935
theorem B17321039 : Blo 1012602 17321039 := bstep (se 1 (by rfl) ⟨12990779, by rfl⟩ : syracuseStep 17321039 = 25981559) B25981559
theorem B5492123 : Blo 1012602 5492123 := bstep (se 1 (by rfl) ⟨4119092, by rfl⟩ : syracuseStep 5492123 = 8238185) B8238185
theorem B3427919 : Blo 1012602 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B2281499 : Blo 1012602 2281499 := bstep (se 1 (by rfl) ⟨1711124, by rfl⟩ : syracuseStep 2281499 = 3422249) B3422249
theorem B13160537 : Blo 1012602 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B3428459 : Blo 1012602 3428459 := bstep (se 1 (by rfl) ⟨2571344, by rfl⟩ : syracuseStep 3428459 = 5142689) B5142689
theorem B5132483 : Blo 1012602 5132483 := bstep (se 1 (by rfl) ⟨3849362, by rfl⟩ : syracuseStep 5132483 = 7698725) B7698725
theorem B5624657 : Blo 1012602 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B4871123 : Blo 1012602 4871123 := bstep (se 1 (by rfl) ⟨3653342, by rfl⟩ : syracuseStep 4871123 = 7306685) B7306685
theorem B1627103 : Blo 1012602 1627103 := bstep (se 1 (by rfl) ⟨1220327, by rfl⟩ : syracuseStep 1627103 = 2440655) B2440655
theorem B44520619 : Blo 1012602 44520619 := bstep (se 1 (by rfl) ⟨33390464, by rfl⟩ : syracuseStep 44520619 = 66780929) B66780929
theorem B9753929 : Blo 1012602 9753929 := bstep (se 2 (by rfl) ⟨3657723, by rfl⟩ : syracuseStep 9753929 = 7315447) B7315447
theorem B3430079 : Blo 1012602 3430079 := bstep (se 1 (by rfl) ⟨2572559, by rfl⟩ : syracuseStep 3430079 = 5145119) B5145119
theorem B5134103 : Blo 1012602 5134103 := bstep (se 1 (by rfl) ⟨3850577, by rfl⟩ : syracuseStep 5134103 = 7701155) B7701155
theorem B1955623 : Blo 1012602 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B5855039 : Blo 1012602 5855039 := bstep (se 1 (by rfl) ⟨4391279, by rfl⟩ : syracuseStep 5855039 = 8782559) B8782559
theorem B2283803 : Blo 1012602 2283803 := bstep (se 1 (by rfl) ⟨1712852, by rfl⟩ : syracuseStep 2283803 = 3425705) B3425705
theorem B3660059 : Blo 1012602 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B24664439 : Blo 1012602 24664439 := bstep (se 1 (by rfl) ⟨18498329, by rfl⟩ : syracuseStep 24664439 = 36996659) B36996659
theorem B1923679 : Blo 1012602 1923679 := bstep (se 1 (by rfl) ⟨1442759, by rfl⟩ : syracuseStep 1923679 = 2885519) B2885519
theorem B19782589 : Blo 1012602 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B1301567 : Blo 1012602 1301567 := bstep (se 1 (by rfl) ⟨976175, by rfl⟩ : syracuseStep 1301567 = 1952351) B1952351
theorem B10574945 : Blo 1012602 10574945 := bstep (se 2 (by rfl) ⟨3965604, by rfl⟩ : syracuseStep 10574945 = 7931209) B7931209
theorem B2284775 : Blo 1012602 2284775 := bstep (se 1 (by rfl) ⟨1713581, by rfl⟩ : syracuseStep 2284775 = 3427163) B3427163
theorem B5135723 : Blo 1012602 5135723 := bstep (se 1 (by rfl) ⟨3851792, by rfl⟩ : syracuseStep 5135723 = 7703585) B7703585
theorem B8674735 : Blo 1012602 8674735 := bstep (se 1 (by rfl) ⟨6506051, by rfl⟩ : syracuseStep 8674735 = 13012103) B13012103
theorem B5856889 : Blo 1012602 5856889 := bstep (se 2 (by rfl) ⟨2196333, by rfl⟩ : syracuseStep 5856889 = 4392667) B4392667
theorem B2285729 : Blo 1012602 2285729 := bstep (se 2 (by rfl) ⟨857148, by rfl⟩ : syracuseStep 2285729 = 1714297) B1714297
theorem B1139359 : Blo 1012602 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B21980069 : Blo 1012602 21980069 := bstep (se 4 (by rfl) ⟨2060631, by rfl⟩ : syracuseStep 21980069 = 4121263) B4121263
theorem B2286683 : Blo 1012602 2286683 := bstep (se 1 (by rfl) ⟨1715012, by rfl⟩ : syracuseStep 2286683 = 3430025) B3430025
theorem B13001957 : Blo 1012602 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B12346663 : Blo 1012602 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1828207 : Blo 1012602 1828207 := bstep (se 1 (by rfl) ⟨1371155, by rfl⟩ : syracuseStep 1828207 = 2742311) B2742311
theorem B2287079 : Blo 1012602 2287079 := bstep (se 1 (by rfl) ⟨1715309, by rfl⟩ : syracuseStep 2287079 = 3430619) B3430619
theorem B11560481 : Blo 1012602 11560481 := bstep (se 2 (by rfl) ⟨4335180, by rfl⟩ : syracuseStep 11560481 = 8670361) B8670361
theorem B2287259 : Blo 1012602 2287259 := bstep (se 1 (by rfl) ⟨1715444, by rfl⟩ : syracuseStep 2287259 = 3430889) B3430889
theorem B7301087 : Blo 1012602 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B19785707 : Blo 1012602 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B11725049 : Blo 1012602 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B2714489 : Blo 1012602 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B1141627 : Blo 1012602 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B1141951 : Blo 1012602 1141951 := bstep (se 1 (by rfl) ⟨856463, by rfl⟩ : syracuseStep 1141951 = 1712927) B1712927
theorem B7695809 : Blo 1012602 7695809 := bstep (se 2 (by rfl) ⟨2885928, by rfl⟩ : syracuseStep 7695809 = 5771857) B5771857
theorem B1142491 : Blo 1012602 1142491 := bstep (se 1 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 1142491 = 1713737) B1713737
theorem B8679383 : Blo 1012602 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B1142815 : Blo 1012602 1142815 := bstep (se 1 (by rfl) ⟨857111, by rfl⟩ : syracuseStep 1142815 = 1714223) B1714223
theorem B4878463 : Blo 1012602 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B1929595 : Blo 1012602 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B1372955 : Blo 1012602 1372955 := bstep (se 1 (by rfl) ⟨1029716, by rfl⟩ : syracuseStep 1372955 = 2059433) B2059433
theorem B4387817 : Blo 1012602 4387817 := bstep (se 2 (by rfl) ⟨1645431, by rfl⟩ : syracuseStep 4387817 = 3290863) B3290863
theorem B26702855 : Blo 1012602 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B1012783 : Blo 1012602 1012783 := bstep (se 1 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 1012783 = 1519175) B1519175
theorem B1373231 : Blo 1012602 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B5207111 : Blo 1012602 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B1012903 : Blo 1012602 1012903 := bstep (se 1 (by rfl) ⟨759677, by rfl⟩ : syracuseStep 1012903 = 1519355) B1519355
theorem B105280985 : Blo 1012602 105280985 := bstep (se 2 (by rfl) ⟨39480369, by rfl⟩ : syracuseStep 105280985 = 78960739) B78960739
theorem B5142041 : Blo 1012602 5142041 := bstep (se 2 (by rfl) ⟨1928265, by rfl⟩ : syracuseStep 5142041 = 3856531) B3856531
theorem B1013351 : Blo 1012602 1013351 := bstep (se 1 (by rfl) ⟨760013, by rfl⟩ : syracuseStep 1013351 = 1520027) B1520027
theorem B1013631 : Blo 1012602 1013631 := bstep (se 1 (by rfl) ⟨760223, by rfl⟩ : syracuseStep 1013631 = 1520447) B1520447
theorem B1013727 : Blo 1012602 1013727 := bstep (se 1 (by rfl) ⟨760295, by rfl⟩ : syracuseStep 1013727 = 1520591) B1520591
theorem B1734623 : Blo 1012602 1734623 := bstep (se 1 (by rfl) ⟨1300967, by rfl⟩ : syracuseStep 1734623 = 2601935) B2601935
theorem B1013755 : Blo 1012602 1013755 := bstep (se 1 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 1013755 = 1520633) B1520633
theorem B1013787 : Blo 1012602 1013787 := bstep (se 1 (by rfl) ⟨760340, by rfl⟩ : syracuseStep 1013787 = 1520681) B1520681
theorem B1013807 : Blo 1012602 1013807 := bstep (se 1 (by rfl) ⟨760355, by rfl⟩ : syracuseStep 1013807 = 1520711) B1520711
theorem B3700883 : Blo 1012602 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B1013927 : Blo 1012602 1013927 := bstep (se 1 (by rfl) ⟨760445, by rfl⟩ : syracuseStep 1013927 = 1520891) B1520891
theorem B7797179 : Blo 1012602 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B1014751 : Blo 1012602 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B1014811 : Blo 1012602 1014811 := bstep (se 1 (by rfl) ⟨761108, by rfl⟩ : syracuseStep 1014811 = 1522217) B1522217
theorem B28572797 : Blo 1012602 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B1014939 : Blo 1012602 1014939 := bstep (se 1 (by rfl) ⟨761204, by rfl⟩ : syracuseStep 1014939 = 1522409) B1522409
theorem B1015195 : Blo 1012602 1015195 := bstep (se 1 (by rfl) ⟨761396, by rfl⟩ : syracuseStep 1015195 = 1522793) B1522793
theorem B13172183 : Blo 1012602 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1015279 : Blo 1012602 1015279 := bstep (se 1 (by rfl) ⟨761459, by rfl⟩ : syracuseStep 1015279 = 1522919) B1522919
theorem B1015615 : Blo 1012602 1015615 := bstep (se 1 (by rfl) ⟨761711, by rfl⟩ : syracuseStep 1015615 = 1523423) B1523423
theorem B1015643 : Blo 1012602 1015643 := bstep (se 1 (by rfl) ⟨761732, by rfl⟩ : syracuseStep 1015643 = 1523465) B1523465
theorem B1015899 : Blo 1012602 1015899 := bstep (se 1 (by rfl) ⟨761924, by rfl⟩ : syracuseStep 1015899 = 1523849) B1523849
theorem B1015963 : Blo 1012602 1015963 := bstep (se 1 (by rfl) ⟨761972, by rfl⟩ : syracuseStep 1015963 = 1523945) B1523945
theorem B1016047 : Blo 1012602 1016047 := bstep (se 1 (by rfl) ⟨762035, by rfl⟩ : syracuseStep 1016047 = 1524071) B1524071
theorem B1016127 : Blo 1012602 1016127 := bstep (se 1 (by rfl) ⟨762095, by rfl⟩ : syracuseStep 1016127 = 1524191) B1524191
theorem B1016295 : Blo 1012602 1016295 := bstep (se 1 (by rfl) ⟨762221, by rfl⟩ : syracuseStep 1016295 = 1524443) B1524443
theorem B1016571 : Blo 1012602 1016571 := bstep (se 1 (by rfl) ⟨762428, by rfl⟩ : syracuseStep 1016571 = 1524857) B1524857
theorem B4326281 : Blo 1012602 4326281 := bstep (se 2 (by rfl) ⟨1622355, by rfl⟩ : syracuseStep 4326281 = 3244711) B3244711
theorem B31720385 : Blo 1012602 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B9897065 : Blo 1012602 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B12322637 : Blo 1012602 12322637 := bstep (se 3 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 12322637 = 4620989) B4620989
theorem B16451585 : Blo 1012602 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B11700845 : Blo 1012602 11700845 := bstep (se 3 (by rfl) ⟨2193908, by rfl⟩ : syracuseStep 11700845 = 4387817) B4387817
theorem B2165575 : Blo 1012602 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B5868713 : Blo 1012602 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B3247415 : Blo 1012602 3247415 := bstep (se 1 (by rfl) ⟨2435561, by rfl⟩ : syracuseStep 3247415 = 4871123) B4871123
theorem B1084735 : Blo 1012602 1084735 := bstep (se 1 (by rfl) ⟨813551, by rfl⟩ : syracuseStep 1084735 = 1627103) B1627103
theorem B4329065 : Blo 1012602 4329065 := bstep (se 2 (by rfl) ⟨1623399, by rfl⟩ : syracuseStep 4329065 = 3246799) B3246799
theorem B1446427 : Blo 1012602 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B7049963 : Blo 1012602 7049963 := bstep (se 1 (by rfl) ⟨5287472, by rfl⟩ : syracuseStep 7049963 = 10574945) B10574945
theorem B2888891 : Blo 1012602 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B2888959 : Blo 1012602 2888959 := bstep (se 1 (by rfl) ⟨2166719, by rfl⟩ : syracuseStep 2888959 = 4333439) B4333439
theorem B1709599 : Blo 1012602 1709599 := bstep (se 1 (by rfl) ⟨1282199, by rfl⟩ : syracuseStep 1709599 = 2564399) B2564399
theorem B7706501 : Blo 1012602 7706501 := bstep (se 4 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 7706501 = 1444969) B1444969
theorem B14653379 : Blo 1012602 14653379 := bstep (se 1 (by rfl) ⟨10990034, by rfl⟩ : syracuseStep 14653379 = 21980069) B21980069
theorem B2890075 : Blo 1012602 2890075 := bstep (se 1 (by rfl) ⟨2167556, by rfl⟩ : syracuseStep 2890075 = 4335113) B4335113
theorem B7706987 : Blo 1012602 7706987 := bstep (se 1 (by rfl) ⟨5780240, by rfl⟩ : syracuseStep 7706987 = 11560481) B11560481
theorem B2890475 : Blo 1012602 2890475 := bstep (se 1 (by rfl) ⟨2167856, by rfl⟩ : syracuseStep 2890475 = 4335713) B4335713
theorem B1809659 : Blo 1012602 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B2563751 : Blo 1012602 2563751 := bstep (se 1 (by rfl) ⟨1922813, by rfl⟩ : syracuseStep 2563751 = 3845627) B3845627
theorem B1711847 : Blo 1012602 1711847 := bstep (se 1 (by rfl) ⟨1283885, by rfl⟩ : syracuseStep 1711847 = 2567771) B2567771
theorem B1711867 : Blo 1012602 1711867 := bstep (se 1 (by rfl) ⟨1283900, by rfl⟩ : syracuseStep 1711867 = 2567801) B2567801
theorem B2891659 : Blo 1012602 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B7315849 : Blo 1012602 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B17801903 : Blo 1012602 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B7709417 : Blo 1012602 7709417 := bstep (se 2 (by rfl) ⟨2891031, by rfl⟩ : syracuseStep 7709417 = 5782063) B5782063
theorem B2564905 : Blo 1012602 2564905 := bstep (se 2 (by rfl) ⟨961839, by rfl⟩ : syracuseStep 2564905 = 1923679) B1923679
theorem B1713055 : Blo 1012602 1713055 := bstep (se 1 (by rfl) ⟨1284791, by rfl⟩ : syracuseStep 1713055 = 2569583) B2569583
theorem B1156415 : Blo 1012602 1156415 := bstep (se 1 (by rfl) ⟨867311, by rfl⟩ : syracuseStep 1156415 = 1734623) B1734623
theorem B1713487 : Blo 1012602 1713487 := bstep (se 1 (by rfl) ⟨1285115, by rfl⟩ : syracuseStep 1713487 = 2570231) B2570231
theorem B2467255 : Blo 1012602 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B19048531 : Blo 1012602 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B7809185 : Blo 1012602 7809185 := bstep (se 2 (by rfl) ⟨2928444, by rfl⟩ : syracuseStep 7809185 = 5856889) B5856889
theorem B2566343 : Blo 1012602 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B1714783 : Blo 1012602 1714783 := bstep (se 1 (by rfl) ⟨1286087, by rfl⟩ : syracuseStep 1714783 = 2572175) B2572175
theorem B3418739 : Blo 1012602 3418739 := bstep (se 1 (by rfl) ⟨2564054, by rfl⟩ : syracuseStep 3418739 = 5128109) B5128109
theorem B2894791 : Blo 1012602 2894791 := bstep (se 1 (by rfl) ⟨2171093, by rfl⟩ : syracuseStep 2894791 = 4342187) B4342187
theorem B2436079 : Blo 1012602 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B12987499 : Blo 1012602 12987499 := bstep (se 1 (by rfl) ⟨9740624, by rfl⟩ : syracuseStep 12987499 = 19481249) B19481249
theorem B2567335 : Blo 1012602 2567335 := bstep (se 1 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 2567335 = 3851003) B3851003
theorem B1519145 : Blo 1012602 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B3419819 : Blo 1012602 3419819 := bstep (se 1 (by rfl) ⟨2564864, by rfl⟩ : syracuseStep 3419819 = 5129729) B5129729
theorem B1519487 : Blo 1012602 1519487 := bstep (se 1 (by rfl) ⟨1139615, by rfl⟩ : syracuseStep 1519487 = 2279231) B2279231
theorem B2928815 : Blo 1012602 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B16462217 : Blo 1012602 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B16429463 : Blo 1012602 16429463 := bstep (se 1 (by rfl) ⟨12322097, by rfl⟩ : syracuseStep 16429463 = 24644195) B24644195
theorem B2437609 : Blo 1012602 2437609 := bstep (se 2 (by rfl) ⟨914103, by rfl⟩ : syracuseStep 2437609 = 1828207) B1828207
theorem B11547359 : Blo 1012602 11547359 := bstep (se 1 (by rfl) ⟨8660519, by rfl⟩ : syracuseStep 11547359 = 17321039) B17321039
theorem B1520999 : Blo 1012602 1520999 := bstep (se 1 (by rfl) ⟨1140749, by rfl⟩ : syracuseStep 1520999 = 2281499) B2281499
theorem B3421655 : Blo 1012602 3421655 := bstep (se 1 (by rfl) ⟨2566241, by rfl⟩ : syracuseStep 3421655 = 5132483) B5132483
theorem B3421817 : Blo 1012602 3421817 := bstep (se 2 (by rfl) ⟨1283181, by rfl⟩ : syracuseStep 3421817 = 2566363) B2566363
theorem B3749771 : Blo 1012602 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B6502619 : Blo 1012602 6502619 := bstep (se 1 (by rfl) ⟨4876964, by rfl⟩ : syracuseStep 6502619 = 9753929) B9753929
theorem B1522169 : Blo 1012602 1522169 := bstep (se 2 (by rfl) ⟨570813, by rfl⟩ : syracuseStep 1522169 = 1141627) B1141627
theorem B3422735 : Blo 1012602 3422735 := bstep (se 1 (by rfl) ⟨2567051, by rfl⟩ : syracuseStep 3422735 = 5134103) B5134103
theorem B1522535 : Blo 1012602 1522535 := bstep (se 1 (by rfl) ⟨1141901, by rfl⟩ : syracuseStep 1522535 = 2283803) B2283803
theorem B2440039 : Blo 1012602 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B1522601 : Blo 1012602 1522601 := bstep (se 2 (by rfl) ⟨570975, by rfl⟩ : syracuseStep 1522601 = 1141951) B1141951
theorem B1523183 : Blo 1012602 1523183 := bstep (se 1 (by rfl) ⟨1142387, by rfl⟩ : syracuseStep 1523183 = 2284775) B2284775
theorem B3423815 : Blo 1012602 3423815 := bstep (se 1 (by rfl) ⟨2567861, by rfl⟩ : syracuseStep 3423815 = 5135723) B5135723
theorem B1523321 : Blo 1012602 1523321 := bstep (se 2 (by rfl) ⟨571245, by rfl⟩ : syracuseStep 1523321 = 1142491) B1142491
theorem B4112039 : Blo 1012602 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B1523753 : Blo 1012602 1523753 := bstep (se 2 (by rfl) ⟨571407, by rfl⟩ : syracuseStep 1523753 = 1142815) B1142815
theorem B1523819 : Blo 1012602 1523819 := bstep (se 1 (by rfl) ⟨1142864, by rfl⟩ : syracuseStep 1523819 = 2285729) B2285729
theorem B6504617 : Blo 1012602 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B4112639 : Blo 1012602 4112639 := bstep (se 1 (by rfl) ⟨3084479, by rfl⟩ : syracuseStep 4112639 = 6168959) B6168959
theorem B2572793 : Blo 1012602 2572793 := bstep (se 2 (by rfl) ⟨964797, by rfl⟩ : syracuseStep 2572793 = 1929595) B1929595
theorem B1524455 : Blo 1012602 1524455 := bstep (se 1 (by rfl) ⟨1143341, by rfl⟩ : syracuseStep 1524455 = 2286683) B2286683
theorem B1950527 : Blo 1012602 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B8667971 : Blo 1012602 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B1524719 : Blo 1012602 1524719 := bstep (se 1 (by rfl) ⟨1143539, by rfl⟩ : syracuseStep 1524719 = 2287079) B2287079
theorem B1524839 : Blo 1012602 1524839 := bstep (se 1 (by rfl) ⟨1143629, by rfl⟩ : syracuseStep 1524839 = 2287259) B2287259
theorem B20792477 : Blo 1012602 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B4867391 : Blo 1012602 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B2278727 : Blo 1012602 2278727 := bstep (se 1 (by rfl) ⟨1709045, by rfl⟩ : syracuseStep 2278727 = 3418091) B3418091
theorem B13190471 : Blo 1012602 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B7816699 : Blo 1012602 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B59360825 : Blo 1012602 59360825 := bstep (se 2 (by rfl) ⟨22260309, by rfl⟩ : syracuseStep 59360825 = 44520619) B44520619
theorem B3852157 : Blo 1012602 3852157 := bstep (se 3 (by rfl) ⟨722279, by rfl⟩ : syracuseStep 3852157 = 1444559) B1444559
theorem B79087909 : Blo 1012602 79087909 := bstep (se 4 (by rfl) ⟨7414491, by rfl⟩ : syracuseStep 79087909 = 14828983) B14828983
theorem B5130539 : Blo 1012602 5130539 := bstep (se 1 (by rfl) ⟨3847904, by rfl⟩ : syracuseStep 5130539 = 7695809) B7695809
theorem B2607497 : Blo 1012602 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B5786255 : Blo 1012602 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B2280095 : Blo 1012602 2280095 := bstep (se 1 (by rfl) ⟨1710071, by rfl⟩ : syracuseStep 2280095 = 3420143) B3420143
theorem B5852645 : Blo 1012602 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B3428027 : Blo 1012602 3428027 := bstep (se 1 (by rfl) ⟨2571020, by rfl⟩ : syracuseStep 3428027 = 5142041) B5142041
theorem B1626103 : Blo 1012602 1626103 := bstep (se 1 (by rfl) ⟨1219577, by rfl⟩ : syracuseStep 1626103 = 2439155) B2439155
theorem B8769815 : Blo 1012602 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B360108503 : Blo 1012602 360108503 := bstep (se 1 (by rfl) ⟨270081377, by rfl⟩ : syracuseStep 360108503 = 540162755) B540162755
theorem B2282111 : Blo 1012602 2282111 := bstep (se 1 (by rfl) ⟨1711583, by rfl⟩ : syracuseStep 2282111 = 3423167) B3423167
theorem B1922555 : Blo 1012602 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B3429971 : Blo 1012602 3429971 := bstep (se 1 (by rfl) ⟨2572478, by rfl⟩ : syracuseStep 3429971 = 5144957) B5144957
theorem B2283641 : Blo 1012602 2283641 := bstep (se 2 (by rfl) ⟨856365, by rfl⟩ : syracuseStep 2283641 = 1712731) B1712731
theorem B2283695 : Blo 1012602 2283695 := bstep (se 1 (by rfl) ⟨1712771, by rfl⟩ : syracuseStep 2283695 = 3425543) B3425543
theorem B1923497 : Blo 1012602 1923497 := bstep (se 2 (by rfl) ⟨721311, by rfl⟩ : syracuseStep 1923497 = 1442623) B1442623
theorem B1923527 : Blo 1012602 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B2283983 : Blo 1012602 2283983 := bstep (se 1 (by rfl) ⟨1712987, by rfl⟩ : syracuseStep 2283983 = 3425975) B3425975
theorem B2284415 : Blo 1012602 2284415 := bstep (se 1 (by rfl) ⟨1713311, by rfl⟩ : syracuseStep 2284415 = 3426623) B3426623
theorem B3661213 : Blo 1012602 3661213 := bstep (se 3 (by rfl) ⟨686477, by rfl⟩ : syracuseStep 3661213 = 1372955) B1372955
theorem B3661415 : Blo 1012602 3661415 := bstep (se 1 (by rfl) ⟨2746061, by rfl⟩ : syracuseStep 3661415 = 5492123) B5492123
theorem B2285279 : Blo 1012602 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B1924985 : Blo 1012602 1924985 := bstep (se 2 (by rfl) ⟨721869, by rfl⟩ : syracuseStep 1924985 = 1443739) B1443739
theorem B5136371 : Blo 1012602 5136371 := bstep (se 1 (by rfl) ⟨3852278, by rfl⟩ : syracuseStep 5136371 = 7704557) B7704557
theorem B8773691 : Blo 1012602 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B2285639 : Blo 1012602 2285639 := bstep (se 1 (by rfl) ⟨1714229, by rfl⟩ : syracuseStep 2285639 = 3428459) B3428459
theorem B3661949 : Blo 1012602 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B6512795 : Blo 1012602 6512795 := bstep (se 1 (by rfl) ⟨4884596, by rfl⟩ : syracuseStep 6512795 = 9769193) B9769193
theorem B2285945 : Blo 1012602 2285945 := bstep (se 2 (by rfl) ⟨857229, by rfl⟩ : syracuseStep 2285945 = 1714459) B1714459
theorem B9265619 : Blo 1012602 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B2286719 : Blo 1012602 2286719 := bstep (se 1 (by rfl) ⟨1715039, by rfl⟩ : syracuseStep 2286719 = 3430079) B3430079
theorem B16442959 : Blo 1012602 16442959 := bstep (se 1 (by rfl) ⟨12332219, by rfl⟩ : syracuseStep 16442959 = 24664439) B24664439
theorem B14640871 : Blo 1012602 14640871 := bstep (se 1 (by rfl) ⟨10980653, by rfl⟩ : syracuseStep 14640871 = 21961307) B21961307
theorem B29222693 : Blo 1012602 29222693 := bstep (se 4 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 29222693 = 5479255) B5479255
theorem B12347255 : Blo 1012602 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B1929071 : Blo 1012602 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B16478315 : Blo 1012602 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B1012671 : Blo 1012602 1012671 := bstep (se 1 (by rfl) ⟨759503, by rfl⟩ : syracuseStep 1012671 = 1519007) B1519007
theorem B1012847 : Blo 1012602 1012847 := bstep (se 1 (by rfl) ⟨759635, by rfl⟩ : syracuseStep 1012847 = 1519271) B1519271
theorem B1012863 : Blo 1012602 1012863 := bstep (se 1 (by rfl) ⟨759647, by rfl⟩ : syracuseStep 1012863 = 1519295) B1519295
theorem B1012927 : Blo 1012602 1012927 := bstep (se 1 (by rfl) ⟨759695, by rfl⟩ : syracuseStep 1012927 = 1519391) B1519391
theorem B1013119 : Blo 1012602 1013119 := bstep (se 1 (by rfl) ⟨759839, by rfl⟩ : syracuseStep 1013119 = 1519679) B1519679
theorem B3470845 : Blo 1012602 3470845 := bstep (se 3 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 3470845 = 1301567) B1301567
theorem B1013247 : Blo 1012602 1013247 := bstep (se 1 (by rfl) ⟨759935, by rfl⟩ : syracuseStep 1013247 = 1519871) B1519871
theorem B1013275 : Blo 1012602 1013275 := bstep (se 1 (by rfl) ⟨759956, by rfl⟩ : syracuseStep 1013275 = 1519913) B1519913
theorem B1013455 : Blo 1012602 1013455 := bstep (se 1 (by rfl) ⟨760091, by rfl⟩ : syracuseStep 1013455 = 1520183) B1520183
theorem B1013615 : Blo 1012602 1013615 := bstep (se 1 (by rfl) ⟨760211, by rfl⟩ : syracuseStep 1013615 = 1520423) B1520423
theorem B1013695 : Blo 1012602 1013695 := bstep (se 1 (by rfl) ⟨760271, by rfl⟩ : syracuseStep 1013695 = 1520543) B1520543
theorem B62453749 : Blo 1012602 62453749 := bstep (se 5 (by rfl) ⟨2927519, by rfl⟩ : syracuseStep 62453749 = 5855039) B5855039
theorem B3471407 : Blo 1012602 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B1014011 : Blo 1012602 1014011 := bstep (se 1 (by rfl) ⟨760508, by rfl⟩ : syracuseStep 1014011 = 1521017) B1521017
theorem B1014015 : Blo 1012602 1014015 := bstep (se 1 (by rfl) ⟨760511, by rfl⟩ : syracuseStep 1014015 = 1521023) B1521023
theorem B70187323 : Blo 1012602 70187323 := bstep (se 1 (by rfl) ⟨52640492, by rfl⟩ : syracuseStep 70187323 = 105280985) B105280985
theorem B1014119 : Blo 1012602 1014119 := bstep (se 1 (by rfl) ⟨760589, by rfl⟩ : syracuseStep 1014119 = 1521179) B1521179
theorem B1014239 : Blo 1012602 1014239 := bstep (se 1 (by rfl) ⟨760679, by rfl⟩ : syracuseStep 1014239 = 1521359) B1521359
theorem B26376785 : Blo 1012602 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B1014375 : Blo 1012602 1014375 := bstep (se 1 (by rfl) ⟨760781, by rfl⟩ : syracuseStep 1014375 = 1521563) B1521563
theorem B1014399 : Blo 1012602 1014399 := bstep (se 1 (by rfl) ⟨760799, by rfl⟩ : syracuseStep 1014399 = 1521599) B1521599
theorem B1014511 : Blo 1012602 1014511 := bstep (se 1 (by rfl) ⟨760883, by rfl⟩ : syracuseStep 1014511 = 1521767) B1521767
theorem B1014767 : Blo 1012602 1014767 := bstep (se 1 (by rfl) ⟨761075, by rfl⟩ : syracuseStep 1014767 = 1522151) B1522151
theorem B1014815 : Blo 1012602 1014815 := bstep (se 1 (by rfl) ⟨761111, by rfl⟩ : syracuseStep 1014815 = 1522223) B1522223
theorem B11566313 : Blo 1012602 11566313 := bstep (se 2 (by rfl) ⟨4337367, by rfl⟩ : syracuseStep 11566313 = 8674735) B8674735
theorem B1015263 : Blo 1012602 1015263 := bstep (se 1 (by rfl) ⟨761447, by rfl⟩ : syracuseStep 1015263 = 1522895) B1522895
theorem B1015323 : Blo 1012602 1015323 := bstep (se 1 (by rfl) ⟨761492, by rfl⟩ : syracuseStep 1015323 = 1522985) B1522985
theorem B1015343 : Blo 1012602 1015343 := bstep (se 1 (by rfl) ⟨761507, by rfl⟩ : syracuseStep 1015343 = 1523015) B1523015
theorem B8781455 : Blo 1012602 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B98664317 : Blo 1012602 98664317 := bstep (se 3 (by rfl) ⟨18499559, by rfl⟩ : syracuseStep 98664317 = 36999119) B36999119
theorem B1015743 : Blo 1012602 1015743 := bstep (se 1 (by rfl) ⟨761807, by rfl⟩ : syracuseStep 1015743 = 1523615) B1523615
theorem B1015803 : Blo 1012602 1015803 := bstep (se 1 (by rfl) ⟨761852, by rfl⟩ : syracuseStep 1015803 = 1523705) B1523705
theorem B1015835 : Blo 1012602 1015835 := bstep (se 1 (by rfl) ⟨761876, by rfl⟩ : syracuseStep 1015835 = 1523753) B1523753
theorem B1015879 : Blo 1012602 1015879 := bstep (se 1 (by rfl) ⟨761909, by rfl⟩ : syracuseStep 1015879 = 1523819) B1523819
theorem B23396509 : Blo 1012602 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B9765197 : Blo 1012602 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B1016303 : Blo 1012602 1016303 := bstep (se 1 (by rfl) ⟨762227, by rfl⟩ : syracuseStep 1016303 = 1524455) B1524455
theorem B2884187 : Blo 1012602 2884187 := bstep (se 1 (by rfl) ⟨2163140, by rfl⟩ : syracuseStep 2884187 = 4326281) B4326281
theorem B1016479 : Blo 1012602 1016479 := bstep (se 1 (by rfl) ⟨762359, by rfl⟩ : syracuseStep 1016479 = 1524719) B1524719
theorem B1016559 : Blo 1012602 1016559 := bstep (se 1 (by rfl) ⟨762419, by rfl⟩ : syracuseStep 1016559 = 1524839) B1524839
theorem B13861651 : Blo 1012602 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B1738331 : Blo 1012602 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B7800563 : Blo 1012602 7800563 := bstep (se 1 (by rfl) ⟨5850422, by rfl⟩ : syracuseStep 7800563 = 11700845) B11700845
theorem B10422265 : Blo 1012602 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B21923945 : Blo 1012602 21923945 := bstep (se 2 (by rfl) ⟨8221479, by rfl⟩ : syracuseStep 21923945 = 16442959) B16442959
theorem B2164943 : Blo 1012602 2164943 := bstep (se 1 (by rfl) ⟨1623707, by rfl⟩ : syracuseStep 2164943 = 3247415) B3247415
theorem B3901763 : Blo 1012602 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2886043 : Blo 1012602 2886043 := bstep (se 1 (by rfl) ⟨2164532, by rfl⟩ : syracuseStep 2886043 = 4329065) B4329065
theorem B25398041 : Blo 1012602 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B105450545 : Blo 1012602 105450545 := bstep (se 2 (by rfl) ⟨39543954, by rfl⟩ : syracuseStep 105450545 = 79087909) B79087909
theorem B12979709 : Blo 1012602 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B3083773 : Blo 1012602 3083773 := bstep (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) B1156415
theorem B2887433 : Blo 1012602 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B9768919 : Blo 1012602 9768919 := bstep (se 1 (by rfl) ⟨7326689, by rfl⟩ : syracuseStep 9768919 = 14653379) B14653379
theorem B3248105 : Blo 1012602 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B1282331 : Blo 1012602 1282331 := bstep (se 1 (by rfl) ⟨961748, by rfl⟩ : syracuseStep 1282331 = 1923497) B1923497
theorem B9999389 : Blo 1012602 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1709167 : Blo 1012602 1709167 := bstep (se 1 (by rfl) ⟨1281875, by rfl⟩ : syracuseStep 1709167 = 2563751) B2563751
theorem B2168137 : Blo 1012602 2168137 := bstep (se 2 (by rfl) ⟨813051, by rfl⟩ : syracuseStep 2168137 = 1626103) B1626103
theorem B3250145 : Blo 1012602 3250145 := bstep (se 2 (by rfl) ⟨1218804, by rfl⟩ : syracuseStep 3250145 = 2437609) B2437609
theorem B8231503 : Blo 1012602 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B1710895 : Blo 1012602 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B4627793 : Blo 1012602 4627793 := bstep (se 2 (by rfl) ⟨1735422, by rfl⟩ : syracuseStep 4627793 = 3470845) B3470845
theorem B1286047 : Blo 1012602 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B83271665 : Blo 1012602 83271665 := bstep (se 2 (by rfl) ⟨31226874, by rfl⟩ : syracuseStep 83271665 = 62453749) B62453749
theorem B10985543 : Blo 1012602 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B10952975 : Blo 1012602 10952975 := bstep (se 1 (by rfl) ⟨8214731, by rfl⟩ : syracuseStep 10952975 = 16429463) B16429463
theorem B4825757 : Blo 1012602 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B3253385 : Blo 1012602 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B4335079 : Blo 1012602 4335079 := bstep (se 1 (by rfl) ⟨3251309, by rfl⟩ : syracuseStep 4335079 = 6502619) B6502619
theorem B7710875 : Blo 1012602 7710875 := bstep (se 1 (by rfl) ⟨5783156, by rfl⟩ : syracuseStep 7710875 = 11566313) B11566313
theorem B65776211 : Blo 1012602 65776211 := bstep (se 1 (by rfl) ⟨49332158, by rfl⟩ : syracuseStep 65776211 = 98664317) B98664317
theorem B4336411 : Blo 1012602 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B1715195 : Blo 1012602 1715195 := bstep (se 1 (by rfl) ⟨1286396, by rfl⟩ : syracuseStep 1715195 = 2572793) B2572793
theorem B5778647 : Blo 1012602 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B21146923 : Blo 1012602 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B6598043 : Blo 1012602 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B1519151 : Blo 1012602 1519151 := bstep (se 1 (by rfl) ⟨1139363, by rfl⟩ : syracuseStep 1519151 = 2278727) B2278727
theorem B8793647 : Blo 1012602 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B3419873 : Blo 1012602 3419873 := bstep (se 2 (by rfl) ⟨1282452, by rfl⟩ : syracuseStep 3419873 = 2564905) B2564905
theorem B3420359 : Blo 1012602 3420359 := bstep (se 1 (by rfl) ⟨2565269, by rfl⟩ : syracuseStep 3420359 = 5130539) B5130539
theorem B1520063 : Blo 1012602 1520063 := bstep (se 1 (by rfl) ⟨1140047, by rfl⟩ : syracuseStep 1520063 = 2280095) B2280095
theorem B3289673 : Blo 1012602 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B3912475 : Blo 1012602 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B7714277 : Blo 1012602 7714277 := bstep (se 4 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 7714277 = 1446427) B1446427
theorem B5846543 : Blo 1012602 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B240072335 : Blo 1012602 240072335 := bstep (se 1 (by rfl) ⟨180054251, by rfl⟩ : syracuseStep 240072335 = 360108503) B360108503
theorem B1521407 : Blo 1012602 1521407 := bstep (se 1 (by rfl) ⟨1141055, by rfl⟩ : syracuseStep 1521407 = 2282111) B2282111
theorem B5126813 : Blo 1012602 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B1522427 : Blo 1012602 1522427 := bstep (se 1 (by rfl) ⟨1141820, by rfl⟩ : syracuseStep 1522427 = 2283641) B2283641
theorem B1522463 : Blo 1012602 1522463 := bstep (se 1 (by rfl) ⟨1141847, by rfl⟩ : syracuseStep 1522463 = 2283695) B2283695
theorem B17316665 : Blo 1012602 17316665 := bstep (se 2 (by rfl) ⟨6493749, by rfl⟩ : syracuseStep 17316665 = 12987499) B12987499
theorem B3423113 : Blo 1012602 3423113 := bstep (se 2 (by rfl) ⟨1283667, by rfl⟩ : syracuseStep 3423113 = 2567335) B2567335
theorem B1522655 : Blo 1012602 1522655 := bstep (se 1 (by rfl) ⟨1141991, by rfl⟩ : syracuseStep 1522655 = 2283983) B2283983
theorem B1522943 : Blo 1012602 1522943 := bstep (se 1 (by rfl) ⟨1142207, by rfl⟩ : syracuseStep 1522943 = 2284415) B2284415
theorem B2440943 : Blo 1012602 2440943 := bstep (se 1 (by rfl) ⟨1830707, by rfl⟩ : syracuseStep 2440943 = 3661415) B3661415
theorem B1523519 : Blo 1012602 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B3424247 : Blo 1012602 3424247 := bstep (se 1 (by rfl) ⟨2568185, by rfl⟩ : syracuseStep 3424247 = 5136371) B5136371
theorem B1523759 : Blo 1012602 1523759 := bstep (se 1 (by rfl) ⟨1142819, by rfl⟩ : syracuseStep 1523759 = 2285639) B2285639
theorem B4341863 : Blo 1012602 4341863 := bstep (se 1 (by rfl) ⟨3256397, by rfl⟩ : syracuseStep 4341863 = 6512795) B6512795
theorem B1523963 : Blo 1012602 1523963 := bstep (se 1 (by rfl) ⟨1142972, by rfl⟩ : syracuseStep 1523963 = 2285945) B2285945
theorem B6177079 : Blo 1012602 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B1524479 : Blo 1012602 1524479 := bstep (se 1 (by rfl) ⟨1143359, by rfl⟩ : syracuseStep 1524479 = 2286719) B2286719
theorem B5129405 : Blo 1012602 5129405 := bstep (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) B1923527
theorem B19481795 : Blo 1012602 19481795 := bstep (se 1 (by rfl) ⟨14611346, by rfl⟩ : syracuseStep 19481795 = 29222693) B29222693
theorem B5785253 : Blo 1012602 5785253 := bstep (se 4 (by rfl) ⟨542367, by rfl⟩ : syracuseStep 5785253 = 1084735) B1084735
theorem B3851945 : Blo 1012602 3851945 := bstep (se 2 (by rfl) ⟨1444479, by rfl⟩ : syracuseStep 3851945 = 2888959) B2888959
theorem B2279159 : Blo 1012602 2279159 := bstep (se 1 (by rfl) ⟨1709369, by rfl⟩ : syracuseStep 2279159 = 3418739) B3418739
theorem B2279465 : Blo 1012602 2279465 := bstep (se 2 (by rfl) ⟨854799, by rfl⟩ : syracuseStep 2279465 = 1709599) B1709599
theorem B2279879 : Blo 1012602 2279879 := bstep (se 1 (by rfl) ⟨1709909, by rfl⟩ : syracuseStep 2279879 = 3419819) B3419819
theorem B1952543 : Blo 1012602 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B3853433 : Blo 1012602 3853433 := bstep (se 2 (by rfl) ⟨1445037, by rfl⟩ : syracuseStep 3853433 = 2890075) B2890075
theorem B2281103 : Blo 1012602 2281103 := bstep (se 1 (by rfl) ⟨1710827, by rfl⟩ : syracuseStep 2281103 = 3421655) B3421655
theorem B2281211 : Blo 1012602 2281211 := bstep (se 1 (by rfl) ⟨1710908, by rfl⟩ : syracuseStep 2281211 = 3421817) B3421817
theorem B2314271 : Blo 1012602 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B2281823 : Blo 1012602 2281823 := bstep (se 1 (by rfl) ⟨1711367, by rfl⟩ : syracuseStep 2281823 = 3422735) B3422735
theorem B17584523 : Blo 1012602 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B5133293 : Blo 1012602 5133293 := bstep (se 3 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 5133293 = 1924985) B1924985
theorem B2282489 : Blo 1012602 2282489 := bstep (se 2 (by rfl) ⟨855933, by rfl⟩ : syracuseStep 2282489 = 1711867) B1711867
theorem B2282543 : Blo 1012602 2282543 := bstep (se 1 (by rfl) ⟨1711907, by rfl⟩ : syracuseStep 2282543 = 3423815) B3423815
theorem B5854303 : Blo 1012602 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B2741359 : Blo 1012602 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B3855545 : Blo 1012602 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B2741759 : Blo 1012602 2741759 := bstep (se 1 (by rfl) ⟨2056319, by rfl⟩ : syracuseStep 2741759 = 4112639) B4112639
theorem B9754465 : Blo 1012602 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B39573883 : Blo 1012602 39573883 := bstep (se 1 (by rfl) ⟨29680412, by rfl⟩ : syracuseStep 39573883 = 59360825) B59360825
theorem B2284073 : Blo 1012602 2284073 := bstep (se 2 (by rfl) ⟨856527, by rfl⟩ : syracuseStep 2284073 = 1713055) B1713055
theorem B8215091 : Blo 1012602 8215091 := bstep (se 1 (by rfl) ⟨6161318, by rfl⟩ : syracuseStep 8215091 = 12322637) B12322637
theorem B10967723 : Blo 1012602 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B3857503 : Blo 1012602 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B2284649 : Blo 1012602 2284649 := bstep (se 2 (by rfl) ⟨856743, by rfl⟩ : syracuseStep 2284649 = 1713487) B1713487
theorem B47471741 : Blo 1012602 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B18799901 : Blo 1012602 18799901 := bstep (se 3 (by rfl) ⟨3524981, by rfl⟩ : syracuseStep 18799901 = 7049963) B7049963
theorem B5201405 : Blo 1012602 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B19521161 : Blo 1012602 19521161 := bstep (se 2 (by rfl) ⟨7320435, by rfl⟩ : syracuseStep 19521161 = 14640871) B14640871
theorem B2285351 : Blo 1012602 2285351 := bstep (se 1 (by rfl) ⟨1714013, by rfl⟩ : syracuseStep 2285351 = 3428027) B3428027
theorem B5136209 : Blo 1012602 5136209 := bstep (se 2 (by rfl) ⟨1926078, by rfl⟩ : syracuseStep 5136209 = 3852157) B3852157
theorem B1925927 : Blo 1012602 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B2286377 : Blo 1012602 2286377 := bstep (se 2 (by rfl) ⟨857391, by rfl⟩ : syracuseStep 2286377 = 1714783) B1714783
theorem B2286647 : Blo 1012602 2286647 := bstep (se 1 (by rfl) ⟨1714985, by rfl⟩ : syracuseStep 2286647 = 3429971) B3429971
theorem B5137667 : Blo 1012602 5137667 := bstep (se 1 (by rfl) ⟨3853250, by rfl⟩ : syracuseStep 5137667 = 7706501) B7706501
theorem B3859721 : Blo 1012602 3859721 := bstep (se 2 (by rfl) ⟨1447395, by rfl⟩ : syracuseStep 3859721 = 2894791) B2894791
theorem B5137991 : Blo 1012602 5137991 := bstep (se 1 (by rfl) ⟨3853493, by rfl⟩ : syracuseStep 5137991 = 7706987) B7706987
theorem B1926983 : Blo 1012602 1926983 := bstep (se 1 (by rfl) ⟨1445237, by rfl⟩ : syracuseStep 1926983 = 2890475) B2890475
theorem B1141231 : Blo 1012602 1141231 := bstep (se 1 (by rfl) ⟨855923, by rfl⟩ : syracuseStep 1141231 = 1711847) B1711847
theorem B5139611 : Blo 1012602 5139611 := bstep (se 1 (by rfl) ⟨3854708, by rfl⟩ : syracuseStep 5139611 = 7709417) B7709417
theorem B5206123 : Blo 1012602 5206123 := bstep (se 1 (by rfl) ⟨3904592, by rfl⟩ : syracuseStep 5206123 = 7809185) B7809185
theorem B1012763 : Blo 1012602 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B1012991 : Blo 1012602 1012991 := bstep (se 1 (by rfl) ⟨759743, by rfl⟩ : syracuseStep 1012991 = 1519487) B1519487
theorem B10974811 : Blo 1012602 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B93583097 : Blo 1012602 93583097 := bstep (se 2 (by rfl) ⟨35093661, by rfl⟩ : syracuseStep 93583097 = 70187323) B70187323
theorem B7698239 : Blo 1012602 7698239 := bstep (se 1 (by rfl) ⟨5773679, by rfl⟩ : syracuseStep 7698239 = 11547359) B11547359
theorem B1013999 : Blo 1012602 1013999 := bstep (se 1 (by rfl) ⟨760499, by rfl⟩ : syracuseStep 1013999 = 1520999) B1520999
theorem B1014779 : Blo 1012602 1014779 := bstep (se 1 (by rfl) ⟨761084, by rfl⟩ : syracuseStep 1014779 = 1522169) B1522169
theorem B4881617 : Blo 1012602 4881617 := bstep (se 2 (by rfl) ⟨1830606, by rfl⟩ : syracuseStep 4881617 = 3661213) B3661213
theorem B1015023 : Blo 1012602 1015023 := bstep (se 1 (by rfl) ⟨761267, by rfl⟩ : syracuseStep 1015023 = 1522535) B1522535
theorem B1015067 : Blo 1012602 1015067 := bstep (se 1 (by rfl) ⟨761300, by rfl⟩ : syracuseStep 1015067 = 1522601) B1522601
theorem B1015455 : Blo 1012602 1015455 := bstep (se 1 (by rfl) ⟨761591, by rfl⟩ : syracuseStep 1015455 = 1523183) B1523183
theorem B1015547 : Blo 1012602 1015547 := bstep (se 1 (by rfl) ⟨761660, by rfl⟩ : syracuseStep 1015547 = 1523321) B1523321
theorem B1015839 : Blo 1012602 1015839 := bstep (se 1 (by rfl) ⟨761879, by rfl⟩ : syracuseStep 1015839 = 1523759) B1523759
theorem B1015975 : Blo 1012602 1015975 := bstep (se 1 (by rfl) ⟨761981, by rfl⟩ : syracuseStep 1015975 = 1523963) B1523963
theorem B1016319 : Blo 1012602 1016319 := bstep (se 1 (by rfl) ⟨762239, by rfl⟩ : syracuseStep 1016319 = 1524479) B1524479
theorem B124781381 : Blo 1012602 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B18482201 : Blo 1012602 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B14615963 : Blo 1012602 14615963 := bstep (se 1 (by rfl) ⟨10961972, by rfl⟩ : syracuseStep 14615963 = 21923945) B21923945
theorem B1443295 : Blo 1012602 1443295 := bstep (se 1 (by rfl) ⟨1082471, by rfl⟩ : syracuseStep 1443295 = 2164943) B2164943
theorem B8653139 : Blo 1012602 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B13896353 : Blo 1012602 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B2166763 : Blo 1012602 2166763 := bstep (se 1 (by rfl) ⟨1625072, by rfl⟩ : syracuseStep 2166763 = 3250145) B3250145
theorem B5476727 : Blo 1012602 5476727 := bstep (se 1 (by rfl) ⟨4107545, by rfl⟩ : syracuseStep 5476727 = 8215091) B8215091
theorem B7311815 : Blo 1012602 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B13014107 : Blo 1012602 13014107 := bstep (se 1 (by rfl) ⟨9760580, by rfl⟩ : syracuseStep 13014107 = 19521161) B19521161
theorem B55514443 : Blo 1012602 55514443 := bstep (se 1 (by rfl) ⟨41635832, by rfl⟩ : syracuseStep 55514443 = 83271665) B83271665
theorem B3217171 : Blo 1012602 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B1283951 : Blo 1012602 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B5216633 : Blo 1012602 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B1284655 : Blo 1012602 1284655 := bstep (se 1 (by rfl) ⟨963491, by rfl⟩ : syracuseStep 1284655 = 1926983) B1926983
theorem B7805737 : Blo 1012602 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B43850807 : Blo 1012602 43850807 := bstep (se 1 (by rfl) ⟨32888105, by rfl⟩ : syracuseStep 43850807 = 65776211) B65776211
theorem B4398695 : Blo 1012602 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B52765177 : Blo 1012602 52765177 := bstep (se 2 (by rfl) ⟨19786941, by rfl⟩ : syracuseStep 52765177 = 39573883) B39573883
theorem B160048223 : Blo 1012602 160048223 := bstep (se 1 (by rfl) ⟨120036167, by rfl⟩ : syracuseStep 160048223 = 240072335) B240072335
theorem B3417875 : Blo 1012602 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B11544443 : Blo 1012602 11544443 := bstep (se 1 (by rfl) ⟨8658332, by rfl⟩ : syracuseStep 11544443 = 17316665) B17316665
theorem B3254411 : Blo 1012602 3254411 := bstep (se 1 (by rfl) ⟨2440808, by rfl⟩ : syracuseStep 3254411 = 4881617) B4881617
theorem B1714729 : Blo 1012602 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B8661613 : Blo 1012602 8661613 := bstep (se 3 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 8661613 = 3248105) B3248105
theorem B2894575 : Blo 1012602 2894575 := bstep (se 1 (by rfl) ⟨2170931, by rfl⟩ : syracuseStep 2894575 = 4341863) B4341863
theorem B6171389 : Blo 1012602 6171389 := bstep (se 3 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 6171389 = 2314271) B2314271
theorem B3419549 : Blo 1012602 3419549 := bstep (se 3 (by rfl) ⟨641165, by rfl⟩ : syracuseStep 3419549 = 1282331) B1282331
theorem B3419603 : Blo 1012602 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B12987863 : Blo 1012602 12987863 := bstep (se 1 (by rfl) ⟨9740897, by rfl⟩ : syracuseStep 12987863 = 19481795) B19481795
theorem B1158887 : Blo 1012602 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B2567963 : Blo 1012602 2567963 := bstep (se 1 (by rfl) ⟨1925972, by rfl⟩ : syracuseStep 2567963 = 3851945) B3851945
theorem B1519439 : Blo 1012602 1519439 := bstep (se 1 (by rfl) ⟨1139579, by rfl⟩ : syracuseStep 1519439 = 2279159) B2279159
theorem B1519643 : Blo 1012602 1519643 := bstep (se 1 (by rfl) ⟨1139732, by rfl⟩ : syracuseStep 1519643 = 2279465) B2279465
theorem B2601175 : Blo 1012602 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B32944421 : Blo 1012602 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B1519919 : Blo 1012602 1519919 := bstep (se 1 (by rfl) ⟨1139939, by rfl⟩ : syracuseStep 1519919 = 2279879) B2279879
theorem B5780105 : Blo 1012602 5780105 := bstep (se 2 (by rfl) ⟨2167539, by rfl⟩ : syracuseStep 5780105 = 4335079) B4335079
theorem B2568955 : Blo 1012602 2568955 := bstep (se 1 (by rfl) ⟨1926716, by rfl⟩ : syracuseStep 2568955 = 3853433) B3853433
theorem B1520735 : Blo 1012602 1520735 := bstep (se 1 (by rfl) ⟨1140551, by rfl⟩ : syracuseStep 1520735 = 2281103) B2281103
theorem B1520807 : Blo 1012602 1520807 := bstep (se 1 (by rfl) ⟨1140605, by rfl⟩ : syracuseStep 1520807 = 2281211) B2281211
theorem B1521215 : Blo 1012602 1521215 := bstep (se 1 (by rfl) ⟨1140911, by rfl⟩ : syracuseStep 1521215 = 2281823) B2281823
theorem B3848057 : Blo 1012602 3848057 := bstep (se 2 (by rfl) ⟨1443021, by rfl⟩ : syracuseStep 3848057 = 2886043) B2886043
theorem B1521641 : Blo 1012602 1521641 := bstep (se 2 (by rfl) ⟨570615, by rfl⟩ : syracuseStep 1521641 = 1141231) B1141231
theorem B3422195 : Blo 1012602 3422195 := bstep (se 1 (by rfl) ⟨2566646, by rfl⟩ : syracuseStep 3422195 = 5133293) B5133293
theorem B1521659 : Blo 1012602 1521659 := bstep (se 1 (by rfl) ⟨1141244, by rfl⟩ : syracuseStep 1521659 = 2282489) B2282489
theorem B6666259 : Blo 1012602 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B1521695 : Blo 1012602 1521695 := bstep (se 1 (by rfl) ⟨1141271, by rfl⟩ : syracuseStep 1521695 = 2282543) B2282543
theorem B2570363 : Blo 1012602 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B5781881 : Blo 1012602 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B1522715 : Blo 1012602 1522715 := bstep (se 1 (by rfl) ⟨1142036, by rfl⟩ : syracuseStep 1522715 = 2284073) B2284073
theorem B4111697 : Blo 1012602 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B1523099 : Blo 1012602 1523099 := bstep (se 1 (by rfl) ⟨1142324, by rfl⟩ : syracuseStep 1523099 = 2284649) B2284649
theorem B12533267 : Blo 1012602 12533267 := bstep (se 1 (by rfl) ⟨9399950, by rfl⟩ : syracuseStep 12533267 = 18799901) B18799901
theorem B1523567 : Blo 1012602 1523567 := bstep (se 1 (by rfl) ⟨1142675, by rfl⟩ : syracuseStep 1523567 = 2285351) B2285351
theorem B3424139 : Blo 1012602 3424139 := bstep (se 1 (by rfl) ⟨2568104, by rfl⟩ : syracuseStep 3424139 = 5136209) B5136209
theorem B13025225 : Blo 1012602 13025225 := bstep (se 2 (by rfl) ⟨4884459, by rfl⟩ : syracuseStep 13025225 = 9768919) B9768919
theorem B7323695 : Blo 1012602 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B1524251 : Blo 1012602 1524251 := bstep (se 1 (by rfl) ⟨1143188, by rfl⟩ : syracuseStep 1524251 = 2286377) B2286377
theorem B1524431 : Blo 1012602 1524431 := bstep (se 1 (by rfl) ⟨1143323, by rfl⟩ : syracuseStep 1524431 = 2286647) B2286647
theorem B3425111 : Blo 1012602 3425111 := bstep (se 1 (by rfl) ⟨2568833, by rfl⟩ : syracuseStep 3425111 = 5137667) B5137667
theorem B2573147 : Blo 1012602 2573147 := bstep (se 1 (by rfl) ⟨1929860, by rfl⟩ : syracuseStep 2573147 = 3859721) B3859721
theorem B3425327 : Blo 1012602 3425327 := bstep (se 1 (by rfl) ⟨2568995, by rfl⟩ : syracuseStep 3425327 = 5137991) B5137991
theorem B2278889 : Blo 1012602 2278889 := bstep (se 2 (by rfl) ⟨854583, by rfl⟩ : syracuseStep 2278889 = 1709167) B1709167
theorem B3655145 : Blo 1012602 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B3426407 : Blo 1012602 3426407 := bstep (se 1 (by rfl) ⟨2569805, by rfl⟩ : syracuseStep 3426407 = 5139611) B5139611
theorem B14633081 : Blo 1012602 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B3852431 : Blo 1012602 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B2279915 : Blo 1012602 2279915 := bstep (se 1 (by rfl) ⟨1709936, by rfl⟩ : syracuseStep 2279915 = 3419873) B3419873
theorem B281201453 : Blo 1012602 281201453 := bstep (se 3 (by rfl) ⟨52725272, by rfl⟩ : syracuseStep 281201453 = 105450545) B105450545
theorem B2280239 : Blo 1012602 2280239 := bstep (se 1 (by rfl) ⟨1710179, by rfl⟩ : syracuseStep 2280239 = 3420359) B3420359
theorem B270912437 : Blo 1012602 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B12340781 : Blo 1012602 12340781 := bstep (se 3 (by rfl) ⟨2313896, by rfl⟩ : syracuseStep 12340781 = 4627793) B4627793
theorem B2281193 : Blo 1012602 2281193 := bstep (se 2 (by rfl) ⟨855447, by rfl⟩ : syracuseStep 2281193 = 1710895) B1710895
theorem B5132159 : Blo 1012602 5132159 := bstep (se 1 (by rfl) ⟨3849119, by rfl⟩ : syracuseStep 5132159 = 7698239) B7698239
theorem B2282075 : Blo 1012602 2282075 := bstep (se 1 (by rfl) ⟨1711556, by rfl⟩ : syracuseStep 2282075 = 3423113) B3423113
theorem B1627295 : Blo 1012602 1627295 := bstep (se 1 (by rfl) ⟨1220471, by rfl⟩ : syracuseStep 1627295 = 2440943) B2440943
theorem B2282831 : Blo 1012602 2282831 := bstep (se 1 (by rfl) ⟨1712123, by rfl⟩ : syracuseStep 2282831 = 3424247) B3424247
theorem B6510131 : Blo 1012602 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B1922791 : Blo 1012602 1922791 := bstep (se 1 (by rfl) ⟨1442093, by rfl⟩ : syracuseStep 1922791 = 2884187) B2884187
theorem B3856835 : Blo 1012602 3856835 := bstep (se 1 (by rfl) ⟨2892626, by rfl⟩ : syracuseStep 3856835 = 5785253) B5785253
theorem B5200375 : Blo 1012602 5200375 := bstep (se 1 (by rfl) ⟨3900281, by rfl⟩ : syracuseStep 5200375 = 7800563) B7800563
theorem B1924955 : Blo 1012602 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B11723015 : Blo 1012602 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B8675693 : Blo 1012602 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B1827839 : Blo 1012602 1827839 := bstep (se 1 (by rfl) ⟨1370879, by rfl⟩ : syracuseStep 1827839 = 2741759) B2741759
theorem B31647827 : Blo 1012602 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B3467603 : Blo 1012602 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B6941497 : Blo 1012602 6941497 := bstep (se 2 (by rfl) ⟨2603061, by rfl⟩ : syracuseStep 6941497 = 5206123) B5206123
theorem B7301983 : Blo 1012602 7301983 := bstep (se 1 (by rfl) ⟨5476487, by rfl⟩ : syracuseStep 7301983 = 10952975) B10952975
theorem B5140583 : Blo 1012602 5140583 := bstep (se 1 (by rfl) ⟨3855437, by rfl⟩ : syracuseStep 5140583 = 7710875) B7710875
theorem B112783589 : Blo 1012602 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B11563397 : Blo 1012602 11563397 := bstep (se 4 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 11563397 = 2168137) B2168137
theorem B1143463 : Blo 1012602 1143463 := bstep (se 1 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 1143463 = 1715195) B1715195
theorem B5206781 : Blo 1012602 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B1012767 : Blo 1012602 1012767 := bstep (se 1 (by rfl) ⟨759575, by rfl⟩ : syracuseStep 1012767 = 1519151) B1519151
theorem B5862431 : Blo 1012602 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B13005953 : Blo 1012602 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B1013375 : Blo 1012602 1013375 := bstep (se 1 (by rfl) ⟨760031, by rfl⟩ : syracuseStep 1013375 = 1520063) B1520063
theorem B2193115 : Blo 1012602 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B10975337 : Blo 1012602 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B5142851 : Blo 1012602 5142851 := bstep (se 1 (by rfl) ⟨3857138, by rfl⟩ : syracuseStep 5142851 = 7714277) B7714277
theorem B3897695 : Blo 1012602 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B62388731 : Blo 1012602 62388731 := bstep (se 1 (by rfl) ⟨46791548, by rfl⟩ : syracuseStep 62388731 = 93583097) B93583097
theorem B1014271 : Blo 1012602 1014271 := bstep (se 1 (by rfl) ⟨760703, by rfl⟩ : syracuseStep 1014271 = 1521407) B1521407
theorem B5143337 : Blo 1012602 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1014951 : Blo 1012602 1014951 := bstep (se 1 (by rfl) ⟨761213, by rfl⟩ : syracuseStep 1014951 = 1522427) B1522427
theorem B1014975 : Blo 1012602 1014975 := bstep (se 1 (by rfl) ⟨761231, by rfl⟩ : syracuseStep 1014975 = 1522463) B1522463
theorem B1015103 : Blo 1012602 1015103 := bstep (se 1 (by rfl) ⟨761327, by rfl⟩ : syracuseStep 1015103 = 1522655) B1522655
theorem B1015295 : Blo 1012602 1015295 := bstep (se 1 (by rfl) ⟨761471, by rfl⟩ : syracuseStep 1015295 = 1522943) B1522943
theorem B1015679 : Blo 1012602 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B4882463 : Blo 1012602 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B1016167 : Blo 1012602 1016167 := bstep (se 1 (by rfl) ⟨762125, by rfl⟩ : syracuseStep 1016167 = 1524251) B1524251
theorem B1016287 : Blo 1012602 1016287 := bstep (se 1 (by rfl) ⟨762215, by rfl⟩ : syracuseStep 1016287 = 1524431) B1524431
theorem B70353569 : Blo 1012602 70353569 := bstep (se 2 (by rfl) ⟨26382588, by rfl⟩ : syracuseStep 70353569 = 52765177) B52765177
theorem B12321467 : Blo 1012602 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B31261373 : Blo 1012602 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B5768759 : Blo 1012602 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B187467635 : Blo 1012602 187467635 := bstep (se 1 (by rfl) ⟨140600726, by rfl⟩ : syracuseStep 187467635 = 281201453) B281201453
theorem B8227187 : Blo 1012602 8227187 := bstep (se 1 (by rfl) ⟨6170390, by rfl⟩ : syracuseStep 8227187 = 12340781) B12340781
theorem B9735977 : Blo 1012602 9735977 := bstep (se 2 (by rfl) ⟨3650991, by rfl⟩ : syracuseStep 9735977 = 7301983) B7301983
theorem B3477755 : Blo 1012602 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B29233871 : Blo 1012602 29233871 := bstep (se 1 (by rfl) ⟨21925403, by rfl⟩ : syracuseStep 29233871 = 43850807) B43850807
theorem B1283303 : Blo 1012602 1283303 := bstep (se 1 (by rfl) ⟨962477, by rfl⟩ : syracuseStep 1283303 = 1924955) B1924955
theorem B2889017 : Blo 1012602 2889017 := bstep (se 2 (by rfl) ⟨1083381, by rfl⟩ : syracuseStep 2889017 = 2166763) B2166763
theorem B1218559 : Blo 1012602 1218559 := bstep (se 1 (by rfl) ⟨913919, by rfl⟩ : syracuseStep 1218559 = 1827839) B1827839
theorem B106698815 : Blo 1012602 106698815 := bstep (se 1 (by rfl) ⟨80024111, by rfl⟩ : syracuseStep 106698815 = 160048223) B160048223
theorem B2169607 : Blo 1012602 2169607 := bstep (se 1 (by rfl) ⟨1627205, by rfl⟩ : syracuseStep 2169607 = 3254411) B3254411
theorem B2924153 : Blo 1012602 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B2563721 : Blo 1012602 2563721 := bstep (se 2 (by rfl) ⟨961395, by rfl⟩ : syracuseStep 2563721 = 1922791) B1922791
theorem B8658575 : Blo 1012602 8658575 := bstep (se 1 (by rfl) ⟨6493931, by rfl⟩ : syracuseStep 8658575 = 12987863) B12987863
theorem B1711975 : Blo 1012602 1711975 := bstep (se 1 (by rfl) ⟨1283981, by rfl⟩ : syracuseStep 1711975 = 2567963) B2567963
theorem B8888345 : Blo 1012602 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B21962947 : Blo 1012602 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B7708931 : Blo 1012602 7708931 := bstep (se 1 (by rfl) ⟨5781698, by rfl⟩ : syracuseStep 7708931 = 11563397) B11563397
theorem B3908287 : Blo 1012602 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B1712873 : Blo 1012602 1712873 := bstep (se 2 (by rfl) ⟨642327, by rfl⟩ : syracuseStep 1712873 = 1284655) B1284655
theorem B2565371 : Blo 1012602 2565371 := bstep (se 1 (by rfl) ⟨1924028, by rfl⟩ : syracuseStep 2565371 = 3848057) B3848057
theorem B7316891 : Blo 1012602 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B1713575 : Blo 1012602 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B2598463 : Blo 1012602 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B41592487 : Blo 1012602 41592487 := bstep (se 1 (by rfl) ⟨31194365, by rfl⟩ : syracuseStep 41592487 = 62388731) B62388731
theorem B3090365 : Blo 1012602 3090365 := bstep (se 3 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 3090365 = 1158887) B1158887
theorem B1715431 : Blo 1012602 1715431 := bstep (se 1 (by rfl) ⟨1286573, by rfl⟩ : syracuseStep 1715431 = 2573147) B2573147
theorem B9743975 : Blo 1012602 9743975 := bstep (se 1 (by rfl) ⟨7307981, by rfl⟩ : syracuseStep 9743975 = 14615963) B14615963
theorem B1519259 : Blo 1012602 1519259 := bstep (se 1 (by rfl) ⟨1139444, by rfl⟩ : syracuseStep 1519259 = 2278889) B2278889
theorem B2436763 : Blo 1012602 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B2568287 : Blo 1012602 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B1519943 : Blo 1012602 1519943 := bstep (se 1 (by rfl) ⟨1139957, by rfl⟩ : syracuseStep 1519943 = 2279915) B2279915
theorem B1520159 : Blo 1012602 1520159 := bstep (se 1 (by rfl) ⟨1140119, by rfl⟩ : syracuseStep 1520159 = 2280239) B2280239
theorem B1520795 : Blo 1012602 1520795 := bstep (se 1 (by rfl) ⟨1140596, by rfl⟩ : syracuseStep 1520795 = 2281193) B2281193
theorem B3421439 : Blo 1012602 3421439 := bstep (se 1 (by rfl) ⟨2566079, by rfl⟩ : syracuseStep 3421439 = 5132159) B5132159
theorem B3651151 : Blo 1012602 3651151 := bstep (se 1 (by rfl) ⟨2738363, by rfl⟩ : syracuseStep 3651151 = 5476727) B5476727
theorem B1521383 : Blo 1012602 1521383 := bstep (se 1 (by rfl) ⟨1141037, by rfl⟩ : syracuseStep 1521383 = 2282075) B2282075
theorem B4339453 : Blo 1012602 4339453 := bstep (se 3 (by rfl) ⟨813647, by rfl⟩ : syracuseStep 4339453 = 1627295) B1627295
theorem B11548817 : Blo 1012602 11548817 := bstep (se 2 (by rfl) ⟨4330806, by rfl⟩ : syracuseStep 11548817 = 8661613) B8661613
theorem B1521887 : Blo 1012602 1521887 := bstep (se 1 (by rfl) ⟨1141415, by rfl⟩ : syracuseStep 1521887 = 2282831) B2282831
theorem B4340087 : Blo 1012602 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B9255329 : Blo 1012602 9255329 := bstep (se 2 (by rfl) ⟨3470748, by rfl⟩ : syracuseStep 9255329 = 6941497) B6941497
theorem B2571223 : Blo 1012602 2571223 := bstep (se 1 (by rfl) ⟨1928417, by rfl⟩ : syracuseStep 2571223 = 3856835) B3856835
theorem B3423869 : Blo 1012602 3423869 := bstep (se 3 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 3423869 = 1283951) B1283951
theorem B2932463 : Blo 1012602 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B5783795 : Blo 1012602 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B1524617 : Blo 1012602 1524617 := bstep (se 2 (by rfl) ⟨571731, by rfl⟩ : syracuseStep 1524617 = 1143463) B1143463
theorem B3425273 : Blo 1012602 3425273 := bstep (se 2 (by rfl) ⟨1284477, by rfl⟩ : syracuseStep 3425273 = 2568955) B2568955
theorem B2278583 : Blo 1012602 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B2311735 : Blo 1012602 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B4114259 : Blo 1012602 4114259 := bstep (se 1 (by rfl) ⟨3085694, by rfl⟩ : syracuseStep 4114259 = 6171389) B6171389
theorem B2279699 : Blo 1012602 2279699 := bstep (se 1 (by rfl) ⟨1709774, by rfl⟩ : syracuseStep 2279699 = 3419549) B3419549
theorem B2279735 : Blo 1012602 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B3427055 : Blo 1012602 3427055 := bstep (se 1 (by rfl) ⟨2570291, by rfl⟩ : syracuseStep 3427055 = 5140583) B5140583
theorem B75189059 : Blo 1012602 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B3853403 : Blo 1012602 3853403 := bstep (se 1 (by rfl) ⟨2890052, by rfl⟩ : syracuseStep 3853403 = 5780105) B5780105
theorem B6933833 : Blo 1012602 6933833 := bstep (se 2 (by rfl) ⟨2600187, by rfl⟩ : syracuseStep 6933833 = 5200375) B5200375
theorem B8670635 : Blo 1012602 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B10407649 : Blo 1012602 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B2281463 : Blo 1012602 2281463 := bstep (se 1 (by rfl) ⟨1711097, by rfl⟩ : syracuseStep 2281463 = 3422195) B3422195
theorem B3428567 : Blo 1012602 3428567 := bstep (se 1 (by rfl) ⟨2571425, by rfl⟩ : syracuseStep 3428567 = 5142851) B5142851
theorem B3854587 : Blo 1012602 3854587 := bstep (se 1 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 3854587 = 5781881) B5781881
theorem B3428891 : Blo 1012602 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B2741131 : Blo 1012602 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B2282759 : Blo 1012602 2282759 := bstep (se 1 (by rfl) ⟨1712069, by rfl⟩ : syracuseStep 2282759 = 3424139) B3424139
theorem B83187587 : Blo 1012602 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B2283407 : Blo 1012602 2283407 := bstep (se 1 (by rfl) ⟨1712555, by rfl⟩ : syracuseStep 2283407 = 3425111) B3425111
theorem B2283551 : Blo 1012602 2283551 := bstep (se 1 (by rfl) ⟨1712663, by rfl⟩ : syracuseStep 2283551 = 3425327) B3425327
theorem B2284271 : Blo 1012602 2284271 := bstep (se 1 (by rfl) ⟨1713203, by rfl⟩ : syracuseStep 2284271 = 3426407) B3426407
theorem B9755387 : Blo 1012602 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B9264235 : Blo 1012602 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B180608291 : Blo 1012602 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B1924393 : Blo 1012602 1924393 := bstep (se 2 (by rfl) ⟨721647, by rfl⟩ : syracuseStep 1924393 = 1443295) B1443295
theorem B4874543 : Blo 1012602 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B2286305 : Blo 1012602 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B8676071 : Blo 1012602 8676071 := bstep (se 1 (by rfl) ⟨6507053, by rfl⟩ : syracuseStep 8676071 = 13014107) B13014107
theorem B3859433 : Blo 1012602 3859433 := bstep (se 2 (by rfl) ⟨1447287, by rfl⟩ : syracuseStep 3859433 = 2894575) B2894575
theorem B3468233 : Blo 1012602 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B7696295 : Blo 1012602 7696295 := bstep (se 1 (by rfl) ⟨5772221, by rfl⟩ : syracuseStep 7696295 = 11544443) B11544443
theorem B21098551 : Blo 1012602 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B74019257 : Blo 1012602 74019257 := bstep (se 2 (by rfl) ⟨27757221, by rfl⟩ : syracuseStep 74019257 = 55514443) B55514443
theorem B4289561 : Blo 1012602 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B1012959 : Blo 1012602 1012959 := bstep (se 1 (by rfl) ⟨759719, by rfl⟩ : syracuseStep 1012959 = 1519439) B1519439
theorem B1013095 : Blo 1012602 1013095 := bstep (se 1 (by rfl) ⟨759821, by rfl⟩ : syracuseStep 1013095 = 1519643) B1519643
theorem B1013279 : Blo 1012602 1013279 := bstep (se 1 (by rfl) ⟨759959, by rfl⟩ : syracuseStep 1013279 = 1519919) B1519919
theorem B3471187 : Blo 1012602 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B1013823 : Blo 1012602 1013823 := bstep (se 1 (by rfl) ⟨760367, by rfl⟩ : syracuseStep 1013823 = 1520735) B1520735
theorem B1013871 : Blo 1012602 1013871 := bstep (se 1 (by rfl) ⟨760403, by rfl⟩ : syracuseStep 1013871 = 1520807) B1520807
theorem B1014143 : Blo 1012602 1014143 := bstep (se 1 (by rfl) ⟨760607, by rfl⟩ : syracuseStep 1014143 = 1521215) B1521215
theorem B1014427 : Blo 1012602 1014427 := bstep (se 1 (by rfl) ⟨760820, by rfl⟩ : syracuseStep 1014427 = 1521641) B1521641
theorem B1014439 : Blo 1012602 1014439 := bstep (se 1 (by rfl) ⟨760829, by rfl⟩ : syracuseStep 1014439 = 1521659) B1521659
theorem B1014463 : Blo 1012602 1014463 := bstep (se 1 (by rfl) ⟨760847, by rfl⟩ : syracuseStep 1014463 = 1521695) B1521695
theorem B1015143 : Blo 1012602 1015143 := bstep (se 1 (by rfl) ⟨761357, by rfl⟩ : syracuseStep 1015143 = 1522715) B1522715
theorem B1015399 : Blo 1012602 1015399 := bstep (se 1 (by rfl) ⟨761549, by rfl⟩ : syracuseStep 1015399 = 1523099) B1523099
theorem B8355511 : Blo 1012602 8355511 := bstep (se 1 (by rfl) ⟨6266633, by rfl⟩ : syracuseStep 8355511 = 12533267) B12533267
theorem B1015711 : Blo 1012602 1015711 := bstep (se 1 (by rfl) ⟨761783, by rfl⟩ : syracuseStep 1015711 = 1523567) B1523567
theorem B8683483 : Blo 1012602 8683483 := bstep (se 1 (by rfl) ⟨6512612, by rfl⟩ : syracuseStep 8683483 = 13025225) B13025225
theorem B20840915 : Blo 1012602 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B1016411 : Blo 1012602 1016411 := bstep (se 1 (by rfl) ⟨762308, by rfl⟩ : syracuseStep 1016411 = 1524617) B1524617
theorem B9274013 : Blo 1012602 9274013 := bstep (se 3 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 9274013 = 3477755) B3477755
theorem B5211049 : Blo 1012602 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B124978423 : Blo 1012602 124978423 := bstep (se 1 (by rfl) ⟨93733817, by rfl⟩ : syracuseStep 124978423 = 187467635) B187467635
theorem B3082313 : Blo 1012602 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B4622555 : Blo 1012602 4622555 := bstep (se 1 (by rfl) ⟨3466916, by rfl⟩ : syracuseStep 4622555 = 6933833) B6933833
theorem B6490651 : Blo 1012602 6490651 := bstep (se 1 (by rfl) ⟨4867988, by rfl⟩ : syracuseStep 6490651 = 9735977) B9735977
theorem B14619365 : Blo 1012602 14619365 := bstep (se 4 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 14619365 = 2741131) B2741131
theorem B3249017 : Blo 1012602 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B1709147 : Blo 1012602 1709147 := bstep (se 1 (by rfl) ⟨1281860, by rfl⟩ : syracuseStep 1709147 = 2563721) B2563721
theorem B5772383 : Blo 1012602 5772383 := bstep (se 1 (by rfl) ⟨4329287, by rfl⟩ : syracuseStep 5772383 = 8658575) B8658575
theorem B3249695 : Blo 1012602 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B1710247 : Blo 1012602 1710247 := bstep (se 1 (by rfl) ⟨1282685, by rfl⟩ : syracuseStep 1710247 = 2565371) B2565371
theorem B6495983 : Blo 1012602 6495983 := bstep (se 1 (by rfl) ⟨4871987, by rfl⟩ : syracuseStep 6495983 = 9743975) B9743975
theorem B4628249 : Blo 1012602 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B1712191 : Blo 1012602 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B2859707 : Blo 1012602 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B2892809 : Blo 1012602 2892809 := bstep (se 2 (by rfl) ⟨1084803, by rfl⟩ : syracuseStep 2892809 = 2169607) B2169607
theorem B2893391 : Blo 1012602 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B6170219 : Blo 1012602 6170219 := bstep (se 1 (by rfl) ⟨4627664, by rfl⟩ : syracuseStep 6170219 = 9255329) B9255329
theorem B2565857 : Blo 1012602 2565857 := bstep (se 2 (by rfl) ⟨962196, by rfl⟩ : syracuseStep 2565857 = 1924393) B1924393
theorem B11577977 : Blo 1012602 11577977 := bstep (se 2 (by rfl) ⟨4341741, by rfl⟩ : syracuseStep 11577977 = 8683483) B8683483
theorem B3254975 : Blo 1012602 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B1519055 : Blo 1012602 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B3845839 : Blo 1012602 3845839 := bstep (se 1 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 3845839 = 5768759) B5768759
theorem B1519799 : Blo 1012602 1519799 := bstep (se 1 (by rfl) ⟨1139849, by rfl⟩ : syracuseStep 1519799 = 2279699) B2279699
theorem B1519823 : Blo 1012602 1519823 := bstep (se 1 (by rfl) ⟨1139867, by rfl⟩ : syracuseStep 1519823 = 2279735) B2279735
theorem B5484791 : Blo 1012602 5484791 := bstep (se 1 (by rfl) ⟨4113593, by rfl⟩ : syracuseStep 5484791 = 8227187) B8227187
theorem B187609517 : Blo 1012602 187609517 := bstep (se 3 (by rfl) ⟨35176784, by rfl⟩ : syracuseStep 187609517 = 70353569) B70353569
theorem B2568935 : Blo 1012602 2568935 := bstep (se 1 (by rfl) ⟨1926701, by rfl⟩ : syracuseStep 2568935 = 3853403) B3853403
theorem B55456649 : Blo 1012602 55456649 := bstep (se 2 (by rfl) ⟨20796243, by rfl⟩ : syracuseStep 55456649 = 41592487) B41592487
theorem B5780423 : Blo 1012602 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B1520975 : Blo 1012602 1520975 := bstep (se 1 (by rfl) ⟨1140731, by rfl⟩ : syracuseStep 1520975 = 2281463) B2281463
theorem B3422141 : Blo 1012602 3422141 := bstep (se 3 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 3422141 = 1283303) B1283303
theorem B1521839 : Blo 1012602 1521839 := bstep (se 1 (by rfl) ⟨1141379, by rfl⟩ : syracuseStep 1521839 = 2282759) B2282759
theorem B55458391 : Blo 1012602 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B1522271 : Blo 1012602 1522271 := bstep (se 1 (by rfl) ⟨1141703, by rfl⟩ : syracuseStep 1522271 = 2283407) B2283407
theorem B1522367 : Blo 1012602 1522367 := bstep (se 1 (by rfl) ⟨1141775, by rfl⟩ : syracuseStep 1522367 = 2283551) B2283551
theorem B1522847 : Blo 1012602 1522847 := bstep (se 1 (by rfl) ⟨1142135, by rfl⟩ : syracuseStep 1522847 = 2284271) B2284271
theorem B6503591 : Blo 1012602 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B120405527 : Blo 1012602 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B13876865 : Blo 1012602 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B1949435 : Blo 1012602 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B28131401 : Blo 1012602 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B1524203 : Blo 1012602 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B5784047 : Blo 1012602 5784047 := bstep (se 1 (by rfl) ⟨4338035, by rfl⟩ : syracuseStep 5784047 = 8676071) B8676071
theorem B2572955 : Blo 1012602 2572955 := bstep (se 1 (by rfl) ⟨1929716, by rfl⟩ : syracuseStep 2572955 = 3859433) B3859433
theorem B2312155 : Blo 1012602 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B4868201 : Blo 1012602 4868201 := bstep (se 2 (by rfl) ⟨1825575, by rfl⟩ : syracuseStep 4868201 = 3651151) B3651151
theorem B5785937 : Blo 1012602 5785937 := bstep (se 2 (by rfl) ⟨2169726, by rfl⟩ : syracuseStep 5785937 = 4339453) B4339453
theorem B5130863 : Blo 1012602 5130863 := bstep (se 1 (by rfl) ⟨3848147, by rfl⟩ : syracuseStep 5130863 = 7696295) B7696295
theorem B1624745 : Blo 1012602 1624745 := bstep (se 2 (by rfl) ⟨609279, by rfl⟩ : syracuseStep 1624745 = 1218559) B1218559
theorem B2280959 : Blo 1012602 2280959 := bstep (se 1 (by rfl) ⟨1710719, by rfl⟩ : syracuseStep 2280959 = 3421439) B3421439
theorem B3428297 : Blo 1012602 3428297 := bstep (se 2 (by rfl) ⟨1285611, by rfl⟩ : syracuseStep 3428297 = 2571223) B2571223
theorem B7819901 : Blo 1012602 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B2282579 : Blo 1012602 2282579 := bstep (se 1 (by rfl) ⟨1711934, by rfl⟩ : syracuseStep 2282579 = 3423869) B3423869
theorem B2282633 : Blo 1012602 2282633 := bstep (se 2 (by rfl) ⟨855987, by rfl⟩ : syracuseStep 2282633 = 1711975) B1711975
theorem B3855863 : Blo 1012602 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B29283929 : Blo 1012602 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B8214311 : Blo 1012602 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B2283515 : Blo 1012602 2283515 := bstep (se 1 (by rfl) ⟨1712636, by rfl⟩ : syracuseStep 2283515 = 3425273) B3425273
theorem B2742839 : Blo 1012602 2742839 := bstep (se 1 (by rfl) ⟨2057129, by rfl⟩ : syracuseStep 2742839 = 4114259) B4114259
theorem B2284703 : Blo 1012602 2284703 := bstep (se 1 (by rfl) ⟨1713527, by rfl⟩ : syracuseStep 2284703 = 3427055) B3427055
theorem B50126039 : Blo 1012602 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B3464617 : Blo 1012602 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B2285711 : Blo 1012602 2285711 := bstep (se 1 (by rfl) ⟨1714283, by rfl⟩ : syracuseStep 2285711 = 3428567) B3428567
theorem B2285927 : Blo 1012602 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B19489247 : Blo 1012602 19489247 := bstep (se 1 (by rfl) ⟨14616935, by rfl⟩ : syracuseStep 19489247 = 29233871) B29233871
theorem B1926011 : Blo 1012602 1926011 := bstep (se 1 (by rfl) ⟨1444508, by rfl⟩ : syracuseStep 1926011 = 2889017) B2889017
theorem B71132543 : Blo 1012602 71132543 := bstep (se 1 (by rfl) ⟨53349407, by rfl⟩ : syracuseStep 71132543 = 106698815) B106698815
theorem B2287241 : Blo 1012602 2287241 := bstep (se 2 (by rfl) ⟨857715, by rfl⟩ : syracuseStep 2287241 = 1715431) B1715431
theorem B5925563 : Blo 1012602 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B5139287 : Blo 1012602 5139287 := bstep (se 1 (by rfl) ⟨3854465, by rfl⟩ : syracuseStep 5139287 = 7708931) B7708931
theorem B5139449 : Blo 1012602 5139449 := bstep (se 2 (by rfl) ⟨1927293, by rfl⟩ : syracuseStep 5139449 = 3854587) B3854587
theorem B1141915 : Blo 1012602 1141915 := bstep (se 1 (by rfl) ⟨856436, by rfl⟩ : syracuseStep 1141915 = 1712873) B1712873
theorem B4877927 : Blo 1012602 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B1142383 : Blo 1012602 1142383 := bstep (se 1 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 1142383 = 1713575) B1713575
theorem B2060243 : Blo 1012602 2060243 := bstep (se 1 (by rfl) ⟨1545182, by rfl⟩ : syracuseStep 2060243 = 3090365) B3090365
theorem B1012839 : Blo 1012602 1012839 := bstep (se 1 (by rfl) ⟨759629, by rfl⟩ : syracuseStep 1012839 = 1519259) B1519259
theorem B1013295 : Blo 1012602 1013295 := bstep (se 1 (by rfl) ⟨759971, by rfl⟩ : syracuseStep 1013295 = 1519943) B1519943
theorem B49346171 : Blo 1012602 49346171 := bstep (se 1 (by rfl) ⟨37009628, by rfl⟩ : syracuseStep 49346171 = 74019257) B74019257
theorem B1013439 : Blo 1012602 1013439 := bstep (se 1 (by rfl) ⟨760079, by rfl⟩ : syracuseStep 1013439 = 1520159) B1520159
theorem B1013863 : Blo 1012602 1013863 := bstep (se 1 (by rfl) ⟨760397, by rfl⟩ : syracuseStep 1013863 = 1520795) B1520795
theorem B1014255 : Blo 1012602 1014255 := bstep (se 1 (by rfl) ⟨760691, by rfl⟩ : syracuseStep 1014255 = 1521383) B1521383
theorem B7699211 : Blo 1012602 7699211 := bstep (se 1 (by rfl) ⟨5774408, by rfl⟩ : syracuseStep 7699211 = 11548817) B11548817
theorem B12352313 : Blo 1012602 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B1014591 : Blo 1012602 1014591 := bstep (se 1 (by rfl) ⟨760943, by rfl⟩ : syracuseStep 1014591 = 1521887) B1521887
theorem B11140681 : Blo 1012602 11140681 := bstep (se 2 (by rfl) ⟨4177755, by rfl⟩ : syracuseStep 11140681 = 8355511) B8355511
theorem B13893943 : Blo 1012602 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B1016135 : Blo 1012602 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B6948065 : Blo 1012602 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B3245467 : Blo 1012602 3245467 := bstep (se 1 (by rfl) ⟨2434100, by rfl⟩ : syracuseStep 3245467 = 4868201) B4868201
theorem B3082873 : Blo 1012602 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B5213267 : Blo 1012602 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B2166011 : Blo 1012602 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B8654201 : Blo 1012602 8654201 := bstep (se 2 (by rfl) ⟨3245325, by rfl⟩ : syracuseStep 8654201 = 6490651) B6490651
theorem B2166463 : Blo 1012602 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B5476207 : Blo 1012602 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B4330655 : Blo 1012602 4330655 := bstep (se 1 (by rfl) ⟨3247991, by rfl⟩ : syracuseStep 4330655 = 6495983) B6495983
theorem B3085499 : Blo 1012602 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B1906471 : Blo 1012602 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B12326813 : Blo 1012602 12326813 := bstep (se 3 (by rfl) ⟨2311277, by rfl⟩ : syracuseStep 12326813 = 4622555) B4622555
theorem B1284007 : Blo 1012602 1284007 := bstep (se 1 (by rfl) ⟨963005, by rfl⟩ : syracuseStep 1284007 = 1926011) B1926011
theorem B47421695 : Blo 1012602 47421695 := bstep (se 1 (by rfl) ⟨35566271, by rfl⟩ : syracuseStep 47421695 = 71132543) B71132543
theorem B1710571 : Blo 1012602 1710571 := bstep (se 1 (by rfl) ⟨1282928, by rfl⟩ : syracuseStep 1710571 = 2565857) B2565857
theorem B4332653 : Blo 1012602 4332653 := bstep (se 3 (by rfl) ⟨812372, by rfl⟩ : syracuseStep 4332653 = 1624745) B1624745
theorem B2169983 : Blo 1012602 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B3251951 : Blo 1012602 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B17342909 : Blo 1012602 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B1712623 : Blo 1012602 1712623 := bstep (se 1 (by rfl) ⟨1284467, by rfl⟩ : syracuseStep 1712623 = 2568935) B2568935
theorem B36971099 : Blo 1012602 36971099 := bstep (se 1 (by rfl) ⟨27728324, by rfl⟩ : syracuseStep 36971099 = 55456649) B55456649
theorem B8234875 : Blo 1012602 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B14854241 : Blo 1012602 14854241 := bstep (se 2 (by rfl) ⟨5570340, by rfl⟩ : syracuseStep 14854241 = 11140681) B11140681
theorem B9251243 : Blo 1012602 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B18754267 : Blo 1012602 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B1715303 : Blo 1012602 1715303 := bstep (se 1 (by rfl) ⟨1286477, by rfl⟩ : syracuseStep 1715303 = 2572955) B2572955
theorem B14626109 : Blo 1012602 14626109 := bstep (se 3 (by rfl) ⟨2742395, by rfl⟩ : syracuseStep 14626109 = 5484791) B5484791
theorem B166637897 : Blo 1012602 166637897 := bstep (se 2 (by rfl) ⟨62489211, by rfl⟩ : syracuseStep 166637897 = 124978423) B124978423
theorem B3420575 : Blo 1012602 3420575 := bstep (se 1 (by rfl) ⟨2565431, by rfl⟩ : syracuseStep 3420575 = 5130863) B5130863
theorem B1520639 : Blo 1012602 1520639 := bstep (se 1 (by rfl) ⟨1140479, by rfl⟩ : syracuseStep 1520639 = 2280959) B2280959
theorem B9746243 : Blo 1012602 9746243 := bstep (se 1 (by rfl) ⟨7309682, by rfl⟩ : syracuseStep 9746243 = 14619365) B14619365
theorem B1521719 : Blo 1012602 1521719 := bstep (se 1 (by rfl) ⟨1141289, by rfl⟩ : syracuseStep 1521719 = 2282579) B2282579
theorem B3848255 : Blo 1012602 3848255 := bstep (se 1 (by rfl) ⟨2886191, by rfl⟩ : syracuseStep 3848255 = 5772383) B5772383
theorem B1521755 : Blo 1012602 1521755 := bstep (se 1 (by rfl) ⟨1141316, by rfl⟩ : syracuseStep 1521755 = 2282633) B2282633
theorem B2570575 : Blo 1012602 2570575 := bstep (se 1 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 2570575 = 3855863) B3855863
theorem B1522343 : Blo 1012602 1522343 := bstep (se 1 (by rfl) ⟨1141757, by rfl⟩ : syracuseStep 1522343 = 2283515) B2283515
theorem B1522553 : Blo 1012602 1522553 := bstep (se 2 (by rfl) ⟨570957, by rfl⟩ : syracuseStep 1522553 = 1141915) B1141915
theorem B1523135 : Blo 1012602 1523135 := bstep (se 1 (by rfl) ⟨1142351, by rfl⟩ : syracuseStep 1523135 = 2284703) B2284703
theorem B1523177 : Blo 1012602 1523177 := bstep (se 2 (by rfl) ⟨571191, by rfl⟩ : syracuseStep 1523177 = 1142383) B1142383
theorem B5127785 : Blo 1012602 5127785 := bstep (se 2 (by rfl) ⟨1922919, by rfl⟩ : syracuseStep 5127785 = 3845839) B3845839
theorem B1523807 : Blo 1012602 1523807 := bstep (se 1 (by rfl) ⟨1142855, by rfl⟩ : syracuseStep 1523807 = 2285711) B2285711
theorem B1523951 : Blo 1012602 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B12992831 : Blo 1012602 12992831 := bstep (se 1 (by rfl) ⟨9744623, by rfl⟩ : syracuseStep 12992831 = 19489247) B19489247
theorem B4113479 : Blo 1012602 4113479 := bstep (se 1 (by rfl) ⟨3085109, by rfl⟩ : syracuseStep 4113479 = 6170219) B6170219
theorem B1524827 : Blo 1012602 1524827 := bstep (se 1 (by rfl) ⟨1143620, by rfl⟩ : syracuseStep 1524827 = 2287241) B2287241
theorem B7718651 : Blo 1012602 7718651 := bstep (se 1 (by rfl) ⟨5788988, by rfl⟩ : syracuseStep 7718651 = 11577977) B11577977
theorem B3950375 : Blo 1012602 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B3426191 : Blo 1012602 3426191 := bstep (se 1 (by rfl) ⟨2569643, by rfl⟩ : syracuseStep 3426191 = 5139287) B5139287
theorem B3426299 : Blo 1012602 3426299 := bstep (se 1 (by rfl) ⟨2569724, by rfl⟩ : syracuseStep 3426299 = 5139449) B5139449
theorem B2280329 : Blo 1012602 2280329 := bstep (se 2 (by rfl) ⟨855123, by rfl⟩ : syracuseStep 2280329 = 1710247) B1710247
theorem B3853615 : Blo 1012602 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B73944521 : Blo 1012602 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B2281427 : Blo 1012602 2281427 := bstep (se 1 (by rfl) ⟨1711070, by rfl⟩ : syracuseStep 2281427 = 3422141) B3422141
theorem B5132807 : Blo 1012602 5132807 := bstep (se 1 (by rfl) ⟨3849605, by rfl⟩ : syracuseStep 5132807 = 7699211) B7699211
theorem B80270351 : Blo 1012602 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B1299623 : Blo 1012602 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B2282921 : Blo 1012602 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B3856031 : Blo 1012602 3856031 := bstep (se 1 (by rfl) ⟨2892023, by rfl⟩ : syracuseStep 3856031 = 5784047) B5784047
theorem B6182675 : Blo 1012602 6182675 := bstep (se 1 (by rfl) ⟨4637006, by rfl⟩ : syracuseStep 6182675 = 9274013) B9274013
theorem B2054875 : Blo 1012602 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B3857291 : Blo 1012602 3857291 := bstep (se 1 (by rfl) ⟨2892968, by rfl⟩ : syracuseStep 3857291 = 5785937) B5785937
theorem B2285531 : Blo 1012602 2285531 := bstep (se 1 (by rfl) ⟨1714148, by rfl⟩ : syracuseStep 2285531 = 3428297) B3428297
theorem B1139431 : Blo 1012602 1139431 := bstep (se 1 (by rfl) ⟨854573, by rfl⟩ : syracuseStep 1139431 = 1709147) B1709147
theorem B19522619 : Blo 1012602 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B1828559 : Blo 1012602 1828559 := bstep (se 1 (by rfl) ⟨1371419, by rfl⟩ : syracuseStep 1828559 = 2742839) B2742839
theorem B33417359 : Blo 1012602 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B1928539 : Blo 1012602 1928539 := bstep (se 1 (by rfl) ⟨1446404, by rfl⟩ : syracuseStep 1928539 = 2892809) B2892809
theorem B1928927 : Blo 1012602 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B1012703 : Blo 1012602 1012703 := bstep (se 1 (by rfl) ⟨759527, by rfl⟩ : syracuseStep 1012703 = 1519055) B1519055
theorem B1373495 : Blo 1012602 1373495 := bstep (se 1 (by rfl) ⟨1030121, by rfl⟩ : syracuseStep 1373495 = 2060243) B2060243
theorem B1013199 : Blo 1012602 1013199 := bstep (se 1 (by rfl) ⟨759899, by rfl⟩ : syracuseStep 1013199 = 1519799) B1519799
theorem B1013215 : Blo 1012602 1013215 := bstep (se 1 (by rfl) ⟨759911, by rfl⟩ : syracuseStep 1013215 = 1519823) B1519823
theorem B125073011 : Blo 1012602 125073011 := bstep (se 1 (by rfl) ⟨93804758, by rfl⟩ : syracuseStep 125073011 = 187609517) B187609517
theorem B1013983 : Blo 1012602 1013983 := bstep (se 1 (by rfl) ⟨760487, by rfl⟩ : syracuseStep 1013983 = 1520975) B1520975
theorem B32897447 : Blo 1012602 32897447 := bstep (se 1 (by rfl) ⟨24673085, by rfl⟩ : syracuseStep 32897447 = 49346171) B49346171
theorem B1014559 : Blo 1012602 1014559 := bstep (se 1 (by rfl) ⟨760919, by rfl⟩ : syracuseStep 1014559 = 1521839) B1521839
theorem B1014847 : Blo 1012602 1014847 := bstep (se 1 (by rfl) ⟨761135, by rfl⟩ : syracuseStep 1014847 = 1522271) B1522271
theorem B1014911 : Blo 1012602 1014911 := bstep (se 1 (by rfl) ⟨761183, by rfl⟩ : syracuseStep 1014911 = 1522367) B1522367
theorem B4619489 : Blo 1012602 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B1015231 : Blo 1012602 1015231 := bstep (se 1 (by rfl) ⟨761423, by rfl⟩ : syracuseStep 1015231 = 1522847) B1522847
theorem B1015871 : Blo 1012602 1015871 := bstep (se 1 (by rfl) ⟨761903, by rfl⟩ : syracuseStep 1015871 = 1523807) B1523807
theorem B1015967 : Blo 1012602 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B1016551 : Blo 1012602 1016551 := bstep (se 1 (by rfl) ⟨762413, by rfl⟩ : syracuseStep 1016551 = 1524827) B1524827
theorem B5145767 : Blo 1012602 5145767 := bstep (se 1 (by rfl) ⟨3859325, by rfl⟩ : syracuseStep 5145767 = 7718651) B7718651
theorem B4327289 : Blo 1012602 4327289 := bstep (se 2 (by rfl) ⟨1622733, by rfl⟩ : syracuseStep 4327289 = 3245467) B3245467
theorem B3475511 : Blo 1012602 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B1444007 : Blo 1012602 1444007 := bstep (se 1 (by rfl) ⟨1083005, by rfl⟩ : syracuseStep 1444007 = 2166011) B2166011
theorem B5769467 : Blo 1012602 5769467 := bstep (se 1 (by rfl) ⟨4327100, by rfl⟩ : syracuseStep 5769467 = 8654201) B8654201
theorem B10979833 : Blo 1012602 10979833 := bstep (se 2 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 10979833 = 8234875) B8234875
theorem B53513567 : Blo 1012602 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B2887103 : Blo 1012602 2887103 := bstep (se 1 (by rfl) ⟨2165327, by rfl⟩ : syracuseStep 2887103 = 4330655) B4330655
theorem B25005689 : Blo 1012602 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B2888435 : Blo 1012602 2888435 := bstep (se 1 (by rfl) ⟨2166326, by rfl⟩ : syracuseStep 2888435 = 4332653) B4332653
theorem B1446655 : Blo 1012602 1446655 := bstep (se 1 (by rfl) ⟨1084991, by rfl⟩ : syracuseStep 1446655 = 2169983) B2169983
theorem B2888617 : Blo 1012602 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B2167967 : Blo 1012602 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B24647399 : Blo 1012602 24647399 := bstep (se 1 (by rfl) ⟨18485549, by rfl⟩ : syracuseStep 24647399 = 36971099) B36971099
theorem B126457853 : Blo 1012602 126457853 := bstep (se 3 (by rfl) ⟨23710847, by rfl⟩ : syracuseStep 126457853 = 47421695) B47421695
theorem B13015079 : Blo 1012602 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B1219039 : Blo 1012602 1219039 := bstep (se 1 (by rfl) ⟨914279, by rfl⟩ : syracuseStep 1219039 = 1828559) B1828559
theorem B9902827 : Blo 1012602 9902827 := bstep (se 1 (by rfl) ⟨7427120, by rfl⟩ : syracuseStep 9902827 = 14854241) B14854241
theorem B6167495 : Blo 1012602 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1285951 : Blo 1012602 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B1712009 : Blo 1012602 1712009 := bstep (se 2 (by rfl) ⟨642003, by rfl⟩ : syracuseStep 1712009 = 1284007) B1284007
theorem B111091931 : Blo 1012602 111091931 := bstep (se 1 (by rfl) ⟨83318948, by rfl⟩ : syracuseStep 111091931 = 166637897) B166637897
theorem B6497495 : Blo 1012602 6497495 := bstep (se 1 (by rfl) ⟨4873121, by rfl⟩ : syracuseStep 6497495 = 9746243) B9746243
theorem B2565503 : Blo 1012602 2565503 := bstep (se 1 (by rfl) ⟨1924127, by rfl⟩ : syracuseStep 2565503 = 3848255) B3848255
theorem B21931631 : Blo 1012602 21931631 := bstep (se 1 (by rfl) ⟨16448723, by rfl⟩ : syracuseStep 21931631 = 32897447) B32897447
theorem B3418523 : Blo 1012602 3418523 := bstep (se 1 (by rfl) ⟨2563892, by rfl⟩ : syracuseStep 3418523 = 5127785) B5127785
theorem B8661887 : Blo 1012602 8661887 := bstep (se 1 (by rfl) ⟨6496415, by rfl⟩ : syracuseStep 8661887 = 12992831) B12992831
theorem B18525257 : Blo 1012602 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B1519241 : Blo 1012602 1519241 := bstep (se 2 (by rfl) ⟨569715, by rfl⟩ : syracuseStep 1519241 = 1139431) B1139431
theorem B1520219 : Blo 1012602 1520219 := bstep (se 1 (by rfl) ⟨1140164, by rfl⟩ : syracuseStep 1520219 = 2280329) B2280329
theorem B49296347 : Blo 1012602 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B1520951 : Blo 1012602 1520951 := bstep (se 1 (by rfl) ⟨1140713, by rfl⟩ : syracuseStep 1520951 = 2281427) B2281427
theorem B3421871 : Blo 1012602 3421871 := bstep (se 1 (by rfl) ⟨2566403, by rfl⟩ : syracuseStep 3421871 = 5132807) B5132807
theorem B18528173 : Blo 1012602 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B4110497 : Blo 1012602 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B1521947 : Blo 1012602 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B2570687 : Blo 1012602 2570687 := bstep (se 1 (by rfl) ⟨1928015, by rfl⟩ : syracuseStep 2570687 = 3856031) B3856031
theorem B2571385 : Blo 1012602 2571385 := bstep (se 2 (by rfl) ⟨964269, by rfl⟩ : syracuseStep 2571385 = 1928539) B1928539
theorem B2571527 : Blo 1012602 2571527 := bstep (se 1 (by rfl) ⟨1928645, by rfl⟩ : syracuseStep 2571527 = 3857291) B3857291
theorem B1523687 : Blo 1012602 1523687 := bstep (se 1 (by rfl) ⟨1142765, by rfl⟩ : syracuseStep 1523687 = 2285531) B2285531
theorem B9750739 : Blo 1012602 9750739 := bstep (se 1 (by rfl) ⟨7313054, by rfl⟩ : syracuseStep 9750739 = 14626109) B14626109
theorem B2541961 : Blo 1012602 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B2280383 : Blo 1012602 2280383 := bstep (se 1 (by rfl) ⟨1710287, by rfl⟩ : syracuseStep 2280383 = 3420575) B3420575
theorem B3427433 : Blo 1012602 3427433 := bstep (se 2 (by rfl) ⟨1285287, by rfl⟩ : syracuseStep 3427433 = 2570575) B2570575
theorem B2280761 : Blo 1012602 2280761 := bstep (se 2 (by rfl) ⟨855285, by rfl⟩ : syracuseStep 2280761 = 1710571) B1710571
theorem B2739833 : Blo 1012602 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B83382007 : Blo 1012602 83382007 := bstep (se 1 (by rfl) ⟨62536505, by rfl⟩ : syracuseStep 83382007 = 125073011) B125073011
theorem B2283497 : Blo 1012602 2283497 := bstep (se 2 (by rfl) ⟨856311, by rfl⟩ : syracuseStep 2283497 = 1712623) B1712623
theorem B2742319 : Blo 1012602 2742319 := bstep (se 1 (by rfl) ⟨2056739, by rfl⟩ : syracuseStep 2742319 = 4113479) B4113479
theorem B2284127 : Blo 1012602 2284127 := bstep (se 1 (by rfl) ⟨1713095, by rfl⟩ : syracuseStep 2284127 = 3426191) B3426191
theorem B2284199 : Blo 1012602 2284199 := bstep (se 1 (by rfl) ⟨1713149, by rfl⟩ : syracuseStep 2284199 = 3426299) B3426299
theorem B3465661 : Blo 1012602 3465661 := bstep (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) B1299623
theorem B2056999 : Blo 1012602 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B3662653 : Blo 1012602 3662653 := bstep (se 3 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 3662653 = 1373495) B1373495
theorem B4121783 : Blo 1012602 4121783 := bstep (se 1 (by rfl) ⟨3091337, by rfl⟩ : syracuseStep 4121783 = 6182675) B6182675
theorem B8217875 : Blo 1012602 8217875 := bstep (se 1 (by rfl) ⟨6163406, by rfl⟩ : syracuseStep 8217875 = 12326813) B12326813
theorem B5138153 : Blo 1012602 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B7301609 : Blo 1012602 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B11561939 : Blo 1012602 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B22278239 : Blo 1012602 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B1143535 : Blo 1012602 1143535 := bstep (se 1 (by rfl) ⟨857651, by rfl⟩ : syracuseStep 1143535 = 1715303) B1715303
theorem B42137333 : Blo 1012602 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B12318637 : Blo 1012602 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B1013759 : Blo 1012602 1013759 := bstep (se 1 (by rfl) ⟨760319, by rfl⟩ : syracuseStep 1013759 = 1520639) B1520639
theorem B1014479 : Blo 1012602 1014479 := bstep (se 1 (by rfl) ⟨760859, by rfl⟩ : syracuseStep 1014479 = 1521719) B1521719
theorem B1014503 : Blo 1012602 1014503 := bstep (se 1 (by rfl) ⟨760877, by rfl⟩ : syracuseStep 1014503 = 1521755) B1521755
theorem B1014895 : Blo 1012602 1014895 := bstep (se 1 (by rfl) ⟨761171, by rfl⟩ : syracuseStep 1014895 = 1522343) B1522343
theorem B1015035 : Blo 1012602 1015035 := bstep (se 1 (by rfl) ⟨761276, by rfl⟩ : syracuseStep 1015035 = 1522553) B1522553
theorem B1015423 : Blo 1012602 1015423 := bstep (se 1 (by rfl) ⟨761567, by rfl⟩ : syracuseStep 1015423 = 1523135) B1523135
theorem B1015451 : Blo 1012602 1015451 := bstep (se 1 (by rfl) ⟨761588, by rfl⟩ : syracuseStep 1015451 = 1523177) B1523177
theorem B4620881 : Blo 1012602 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B4883537 : Blo 1012602 4883537 := bstep (se 2 (by rfl) ⟨1831326, by rfl⟩ : syracuseStep 4883537 = 3662653) B3662653
theorem B2884859 : Blo 1012602 2884859 := bstep (se 1 (by rfl) ⟨2163644, by rfl⟩ : syracuseStep 2884859 = 4327289) B4327289
theorem B1445311 : Blo 1012602 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B337220941 : Blo 1012602 337220941 := bstep (se 3 (by rfl) ⟨63228926, by rfl⟩ : syracuseStep 337220941 = 126457853) B126457853
theorem B74061287 : Blo 1012602 74061287 := bstep (se 1 (by rfl) ⟨55545965, by rfl⟩ : syracuseStep 74061287 = 111091931) B111091931
theorem B4331663 : Blo 1012602 4331663 := bstep (se 1 (by rfl) ⟨3248747, by rfl⟩ : syracuseStep 4331663 = 6497495) B6497495
theorem B1710335 : Blo 1012602 1710335 := bstep (se 1 (by rfl) ⟨1282751, by rfl⟩ : syracuseStep 1710335 = 2565503) B2565503
theorem B14621087 : Blo 1012602 14621087 := bstep (se 1 (by rfl) ⟨10965815, by rfl⟩ : syracuseStep 14621087 = 21931631) B21931631
theorem B5774591 : Blo 1012602 5774591 := bstep (se 1 (by rfl) ⟨4330943, by rfl⟩ : syracuseStep 5774591 = 8661887) B8661887
theorem B7707959 : Blo 1012602 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B16424849 : Blo 1012602 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B14852159 : Blo 1012602 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B28091555 : Blo 1012602 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B1713791 : Blo 1012602 1713791 := bstep (se 1 (by rfl) ⟨1285343, by rfl⟩ : syracuseStep 1713791 = 2570687) B2570687
theorem B1714351 : Blo 1012602 1714351 := bstep (se 1 (by rfl) ⟨1285763, by rfl⟩ : syracuseStep 1714351 = 2571527) B2571527
theorem B1714601 : Blo 1012602 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B3846311 : Blo 1012602 3846311 := bstep (se 1 (by rfl) ⟨2884733, by rfl⟩ : syracuseStep 3846311 = 5769467) B5769467
theorem B1520255 : Blo 1012602 1520255 := bstep (se 1 (by rfl) ⟨1140191, by rfl⟩ : syracuseStep 1520255 = 2280383) B2280383
theorem B1520507 : Blo 1012602 1520507 := bstep (se 1 (by rfl) ⟨1140380, by rfl⟩ : syracuseStep 1520507 = 2280761) B2280761
theorem B6501541 : Blo 1012602 6501541 := bstep (se 4 (by rfl) ⟨609519, by rfl⟩ : syracuseStep 6501541 = 1219039) B1219039
theorem B16431599 : Blo 1012602 16431599 := bstep (se 1 (by rfl) ⟨12323699, by rfl⟩ : syracuseStep 16431599 = 24647399) B24647399
theorem B1522331 : Blo 1012602 1522331 := bstep (se 1 (by rfl) ⟨1141748, by rfl⟩ : syracuseStep 1522331 = 2283497) B2283497
theorem B1522751 : Blo 1012602 1522751 := bstep (se 1 (by rfl) ⟨1142063, by rfl⟩ : syracuseStep 1522751 = 2284127) B2284127
theorem B1522799 : Blo 1012602 1522799 := bstep (se 1 (by rfl) ⟨1142099, by rfl⟩ : syracuseStep 1522799 = 2284199) B2284199
theorem B4111663 : Blo 1012602 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B3850685 : Blo 1012602 3850685 := bstep (se 3 (by rfl) ⟨722003, by rfl⟩ : syracuseStep 3850685 = 1444007) B1444007
theorem B1524713 : Blo 1012602 1524713 := bstep (se 2 (by rfl) ⟨571767, by rfl⟩ : syracuseStep 1524713 = 1143535) B1143535
theorem B3425435 : Blo 1012602 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B3851489 : Blo 1012602 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B2279015 : Blo 1012602 2279015 := bstep (se 1 (by rfl) ⟨1709261, by rfl⟩ : syracuseStep 2279015 = 3418523) B3418523
theorem B4867739 : Blo 1012602 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B3656425 : Blo 1012602 3656425 := bstep (se 2 (by rfl) ⟨1371159, by rfl⟩ : syracuseStep 3656425 = 2742319) B2742319
theorem B2281247 : Blo 1012602 2281247 := bstep (se 1 (by rfl) ⟨1710935, by rfl⟩ : syracuseStep 2281247 = 3421871) B3421871
theorem B2740331 : Blo 1012602 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B3428513 : Blo 1012602 3428513 := bstep (se 2 (by rfl) ⟨1285692, by rfl⟩ : syracuseStep 3428513 = 2571385) B2571385
theorem B3430511 : Blo 1012602 3430511 := bstep (se 1 (by rfl) ⟨2572883, by rfl⟩ : syracuseStep 3430511 = 5145767) B5145767
theorem B2742665 : Blo 1012602 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B2317007 : Blo 1012602 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B13557125 : Blo 1012602 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B2284955 : Blo 1012602 2284955 := bstep (se 1 (by rfl) ⟨1713716, by rfl⟩ : syracuseStep 2284955 = 3427433) B3427433
theorem B35675711 : Blo 1012602 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B1924735 : Blo 1012602 1924735 := bstep (se 1 (by rfl) ⟨1443551, by rfl⟩ : syracuseStep 1924735 = 2887103) B2887103
theorem B1826555 : Blo 1012602 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B16670459 : Blo 1012602 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B13000985 : Blo 1012602 13000985 := bstep (se 2 (by rfl) ⟨4875369, by rfl⟩ : syracuseStep 13000985 = 9750739) B9750739
theorem B1925623 : Blo 1012602 1925623 := bstep (se 1 (by rfl) ⟨1444217, by rfl⟩ : syracuseStep 1925623 = 2888435) B2888435
theorem B14639777 : Blo 1012602 14639777 := bstep (se 2 (by rfl) ⟨5489916, by rfl⟩ : syracuseStep 14639777 = 10979833) B10979833
theorem B21914333 : Blo 1012602 21914333 := bstep (se 3 (by rfl) ⟨4108937, by rfl⟩ : syracuseStep 21914333 = 8217875) B8217875
theorem B8676719 : Blo 1012602 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B111176009 : Blo 1012602 111176009 := bstep (se 2 (by rfl) ⟨41691003, by rfl⟩ : syracuseStep 111176009 = 83382007) B83382007
theorem B1141339 : Blo 1012602 1141339 := bstep (se 1 (by rfl) ⟨856004, by rfl⟩ : syracuseStep 1141339 = 1712009) B1712009
theorem B2747855 : Blo 1012602 2747855 := bstep (se 1 (by rfl) ⟨2060891, by rfl⟩ : syracuseStep 2747855 = 4121783) B4121783
theorem B1928873 : Blo 1012602 1928873 := bstep (se 2 (by rfl) ⟨723327, by rfl⟩ : syracuseStep 1928873 = 1446655) B1446655
theorem B12350171 : Blo 1012602 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B1012827 : Blo 1012602 1012827 := bstep (se 1 (by rfl) ⟨759620, by rfl⟩ : syracuseStep 1012827 = 1519241) B1519241
theorem B1013479 : Blo 1012602 1013479 := bstep (se 1 (by rfl) ⟨760109, by rfl⟩ : syracuseStep 1013479 = 1520219) B1520219
theorem B32864231 : Blo 1012602 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B1013967 : Blo 1012602 1013967 := bstep (se 1 (by rfl) ⟨760475, by rfl⟩ : syracuseStep 1013967 = 1520951) B1520951
theorem B13203769 : Blo 1012602 13203769 := bstep (se 2 (by rfl) ⟨4951413, by rfl⟩ : syracuseStep 13203769 = 9902827) B9902827
theorem B12352115 : Blo 1012602 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B1014631 : Blo 1012602 1014631 := bstep (se 1 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 1014631 = 1521947) B1521947
theorem B1015791 : Blo 1012602 1015791 := bstep (se 1 (by rfl) ⟨761843, by rfl⟩ : syracuseStep 1015791 = 1523687) B1523687
theorem B3080587 : Blo 1012602 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B1016475 : Blo 1012602 1016475 := bstep (se 1 (by rfl) ⟨762356, by rfl⟩ : syracuseStep 1016475 = 1524713) B1524713
theorem B3245159 : Blo 1012602 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B2887775 : Blo 1012602 2887775 := bstep (se 1 (by rfl) ⟨2165831, by rfl⟩ : syracuseStep 2887775 = 4331663) B4331663
theorem B10949899 : Blo 1012602 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B9901439 : Blo 1012602 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B7313773 : Blo 1012602 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B2564207 : Blo 1012602 2564207 := bstep (se 1 (by rfl) ⟨1923155, by rfl⟩ : syracuseStep 2564207 = 3846311) B3846311
theorem B17605025 : Blo 1012602 17605025 := bstep (se 2 (by rfl) ⟨6601884, by rfl⟩ : syracuseStep 17605025 = 13203769) B13203769
theorem B8233447 : Blo 1012602 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B10954399 : Blo 1012602 10954399 := bstep (se 1 (by rfl) ⟨8215799, by rfl⟩ : syracuseStep 10954399 = 16431599) B16431599
theorem B5482217 : Blo 1012602 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B8234743 : Blo 1012602 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B2566313 : Blo 1012602 2566313 := bstep (se 2 (by rfl) ⟨962367, by rfl⟩ : syracuseStep 2566313 = 1924735) B1924735
theorem B2567123 : Blo 1012602 2567123 := bstep (se 1 (by rfl) ⟨1925342, by rfl⟩ : syracuseStep 2567123 = 3850685) B3850685
theorem B2567497 : Blo 1012602 2567497 := bstep (se 2 (by rfl) ⟨962811, by rfl⟩ : syracuseStep 2567497 = 1925623) B1925623
theorem B2567659 : Blo 1012602 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B1519343 : Blo 1012602 1519343 := bstep (se 1 (by rfl) ⟨1139507, by rfl⟩ : syracuseStep 1519343 = 2279015) B2279015
theorem B1520831 : Blo 1012602 1520831 := bstep (se 1 (by rfl) ⟨1140623, by rfl⟩ : syracuseStep 1520831 = 2281247) B2281247
theorem B13022765 : Blo 1012602 13022765 := bstep (se 3 (by rfl) ⟨2441768, by rfl⟩ : syracuseStep 13022765 = 4883537) B4883537
theorem B1521785 : Blo 1012602 1521785 := bstep (se 2 (by rfl) ⟨570669, by rfl⟩ : syracuseStep 1521785 = 1141339) B1141339
theorem B9747391 : Blo 1012602 9747391 := bstep (se 1 (by rfl) ⟨7310543, by rfl⟩ : syracuseStep 9747391 = 14621087) B14621087
theorem B3849727 : Blo 1012602 3849727 := bstep (se 1 (by rfl) ⟨2887295, by rfl⟩ : syracuseStep 3849727 = 5774591) B5774591
theorem B1523303 : Blo 1012602 1523303 := bstep (se 1 (by rfl) ⟨1142477, by rfl⟩ : syracuseStep 1523303 = 2284955) B2284955
theorem B8667323 : Blo 1012602 8667323 := bstep (se 1 (by rfl) ⟨6500492, by rfl⟩ : syracuseStep 8667323 = 13000985) B13000985
theorem B18727703 : Blo 1012602 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B5784479 : Blo 1012602 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B8668721 : Blo 1012602 8668721 := bstep (se 2 (by rfl) ⟨3250770, by rfl⟩ : syracuseStep 8668721 = 6501541) B6501541
theorem B449627921 : Blo 1012602 449627921 := bstep (se 2 (by rfl) ⟨168610470, by rfl⟩ : syracuseStep 449627921 = 337220941) B337220941
theorem B6178685 : Blo 1012602 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B19483253 : Blo 1012602 19483253 := bstep (se 5 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 19483253 = 1826555) B1826555
theorem B21909487 : Blo 1012602 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B44454557 : Blo 1012602 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B2283623 : Blo 1012602 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B1923239 : Blo 1012602 1923239 := bstep (se 1 (by rfl) ⟨1442429, by rfl⟩ : syracuseStep 1923239 = 2884859) B2884859
theorem B1826887 : Blo 1012602 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B2285675 : Blo 1012602 2285675 := bstep (se 1 (by rfl) ⟨1714256, by rfl⟩ : syracuseStep 2285675 = 3428513) B3428513
theorem B2285801 : Blo 1012602 2285801 := bstep (se 2 (by rfl) ⟨857175, by rfl⟩ : syracuseStep 2285801 = 1714351) B1714351
theorem B4875233 : Blo 1012602 4875233 := bstep (se 2 (by rfl) ⟨1828212, by rfl⟩ : syracuseStep 4875233 = 3656425) B3656425
theorem B49374191 : Blo 1012602 49374191 := bstep (se 1 (by rfl) ⟨37030643, by rfl⟩ : syracuseStep 49374191 = 74061287) B74061287
theorem B2287007 : Blo 1012602 2287007 := bstep (se 1 (by rfl) ⟨1715255, by rfl⟩ : syracuseStep 2287007 = 3430511) B3430511
theorem B1140223 : Blo 1012602 1140223 := bstep (se 1 (by rfl) ⟨855167, by rfl⟩ : syracuseStep 1140223 = 1710335) B1710335
theorem B1927081 : Blo 1012602 1927081 := bstep (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) B1445311
theorem B5138639 : Blo 1012602 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B9038083 : Blo 1012602 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B23783807 : Blo 1012602 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B9759851 : Blo 1012602 9759851 := bstep (se 1 (by rfl) ⟨7319888, by rfl⟩ : syracuseStep 9759851 = 14639777) B14639777
theorem B14609555 : Blo 1012602 14609555 := bstep (se 1 (by rfl) ⟨10957166, by rfl⟩ : syracuseStep 14609555 = 21914333) B21914333
theorem B1142527 : Blo 1012602 1142527 := bstep (se 1 (by rfl) ⟨856895, by rfl⟩ : syracuseStep 1142527 = 1713791) B1713791
theorem B74117339 : Blo 1012602 74117339 := bstep (se 1 (by rfl) ⟨55588004, by rfl⟩ : syracuseStep 74117339 = 111176009) B111176009
theorem B1143067 : Blo 1012602 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B1831903 : Blo 1012602 1831903 := bstep (se 1 (by rfl) ⟨1373927, by rfl⟩ : syracuseStep 1831903 = 2747855) B2747855
theorem B1013503 : Blo 1012602 1013503 := bstep (se 1 (by rfl) ⟨760127, by rfl⟩ : syracuseStep 1013503 = 1520255) B1520255
theorem B1013671 : Blo 1012602 1013671 := bstep (se 1 (by rfl) ⟨760253, by rfl⟩ : syracuseStep 1013671 = 1520507) B1520507
theorem B1014887 : Blo 1012602 1014887 := bstep (se 1 (by rfl) ⟨761165, by rfl⟩ : syracuseStep 1014887 = 1522331) B1522331
theorem B5143661 : Blo 1012602 5143661 := bstep (se 3 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 5143661 = 1928873) B1928873
theorem B1015167 : Blo 1012602 1015167 := bstep (se 1 (by rfl) ⟨761375, by rfl⟩ : syracuseStep 1015167 = 1522751) B1522751
theorem B1015199 : Blo 1012602 1015199 := bstep (se 1 (by rfl) ⟨761399, by rfl⟩ : syracuseStep 1015199 = 1522799) B1522799
theorem B12485135 : Blo 1012602 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B10977929 : Blo 1012602 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B2163439 : Blo 1012602 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B10979657 : Blo 1012602 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B1282159 : Blo 1012602 1282159 := bstep (se 1 (by rfl) ⟨961619, by rfl⟩ : syracuseStep 1282159 = 1923239) B1923239
theorem B9770149 : Blo 1012602 9770149 := bstep (se 4 (by rfl) ⟨915951, by rfl⟩ : syracuseStep 9770149 = 1831903) B1831903
theorem B1709471 : Blo 1012602 1709471 := bstep (se 1 (by rfl) ⟨1282103, by rfl⟩ : syracuseStep 1709471 = 2564207) B2564207
theorem B11736683 : Blo 1012602 11736683 := bstep (se 1 (by rfl) ⟨8802512, by rfl⟩ : syracuseStep 11736683 = 17605025) B17605025
theorem B1710875 : Blo 1012602 1710875 := bstep (se 1 (by rfl) ⟨1283156, by rfl⟩ : syracuseStep 1710875 = 2566313) B2566313
theorem B1711415 : Blo 1012602 1711415 := bstep (se 1 (by rfl) ⟨1283561, by rfl⟩ : syracuseStep 1711415 = 2567123) B2567123
theorem B9739703 : Blo 1012602 9739703 := bstep (se 1 (by rfl) ⟨7304777, by rfl⟩ : syracuseStep 9739703 = 14609555) B14609555
theorem B2435849 : Blo 1012602 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B5778215 : Blo 1012602 5778215 := bstep (se 1 (by rfl) ⟨4333661, by rfl⟩ : syracuseStep 5778215 = 8667323) B8667323
theorem B4107449 : Blo 1012602 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B5779147 : Blo 1012602 5779147 := bstep (se 1 (by rfl) ⟨4334360, by rfl⟩ : syracuseStep 5779147 = 8668721) B8668721
theorem B12988835 : Blo 1012602 12988835 := bstep (se 1 (by rfl) ⟨9741626, by rfl⟩ : syracuseStep 12988835 = 19483253) B19483253
theorem B1520297 : Blo 1012602 1520297 := bstep (se 2 (by rfl) ⟨570111, by rfl⟩ : syracuseStep 1520297 = 1140223) B1140223
theorem B2569441 : Blo 1012602 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B29636371 : Blo 1012602 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B6600959 : Blo 1012602 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B1522415 : Blo 1012602 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B3423329 : Blo 1012602 3423329 := bstep (se 2 (by rfl) ⟨1283748, by rfl⟩ : syracuseStep 3423329 = 2567497) B2567497
theorem B3423545 : Blo 1012602 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B1523369 : Blo 1012602 1523369 := bstep (se 2 (by rfl) ⟨571263, by rfl⟩ : syracuseStep 1523369 = 1142527) B1142527
theorem B29212649 : Blo 1012602 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B1523783 : Blo 1012602 1523783 := bstep (se 1 (by rfl) ⟨1142837, by rfl⟩ : syracuseStep 1523783 = 2285675) B2285675
theorem B1523867 : Blo 1012602 1523867 := bstep (se 1 (by rfl) ⟨1142900, by rfl⟩ : syracuseStep 1523867 = 2285801) B2285801
theorem B1524089 : Blo 1012602 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B32916127 : Blo 1012602 32916127 := bstep (se 1 (by rfl) ⟨24687095, by rfl⟩ : syracuseStep 32916127 = 49374191) B49374191
theorem B1524671 : Blo 1012602 1524671 := bstep (se 1 (by rfl) ⟨1143503, by rfl⟩ : syracuseStep 1524671 = 2287007) B2287007
theorem B3654811 : Blo 1012602 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B3425759 : Blo 1012602 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B14599865 : Blo 1012602 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B6506567 : Blo 1012602 6506567 := bstep (se 1 (by rfl) ⟨4879925, by rfl⟩ : syracuseStep 6506567 = 9759851) B9759851
theorem B9751697 : Blo 1012602 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B12996521 : Blo 1012602 12996521 := bstep (se 2 (by rfl) ⟨4873695, by rfl⟩ : syracuseStep 12996521 = 9747391) B9747391
theorem B5132969 : Blo 1012602 5132969 := bstep (se 2 (by rfl) ⟨1924863, by rfl⟩ : syracuseStep 5132969 = 3849727) B3849727
theorem B3429107 : Blo 1012602 3429107 := bstep (se 1 (by rfl) ⟨2571830, by rfl⟩ : syracuseStep 3429107 = 5143661) B5143661
theorem B3856319 : Blo 1012602 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B299751947 : Blo 1012602 299751947 := bstep (se 1 (by rfl) ⟨224813960, by rfl⟩ : syracuseStep 299751947 = 449627921) B449627921
theorem B14605865 : Blo 1012602 14605865 := bstep (se 2 (by rfl) ⟨5477199, by rfl⟩ : syracuseStep 14605865 = 10954399) B10954399
theorem B13000621 : Blo 1012602 13000621 := bstep (se 3 (by rfl) ⟨2437616, by rfl⟩ : syracuseStep 13000621 = 4875233) B4875233
theorem B1925183 : Blo 1012602 1925183 := bstep (se 1 (by rfl) ⟨1443887, by rfl⟩ : syracuseStep 1925183 = 2887775) B2887775
theorem B12050777 : Blo 1012602 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B16476493 : Blo 1012602 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B15855871 : Blo 1012602 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B1012895 : Blo 1012602 1012895 := bstep (se 1 (by rfl) ⟨759671, by rfl⟩ : syracuseStep 1012895 = 1519343) B1519343
theorem B49411559 : Blo 1012602 49411559 := bstep (se 1 (by rfl) ⟨37058669, by rfl⟩ : syracuseStep 49411559 = 74117339) B74117339
theorem B1013887 : Blo 1012602 1013887 := bstep (se 1 (by rfl) ⟨760415, by rfl⟩ : syracuseStep 1013887 = 1520831) B1520831
theorem B8681843 : Blo 1012602 8681843 := bstep (se 1 (by rfl) ⟨6511382, by rfl⟩ : syracuseStep 8681843 = 13022765) B13022765
theorem B1014523 : Blo 1012602 1014523 := bstep (se 1 (by rfl) ⟨760892, by rfl⟩ : syracuseStep 1014523 = 1521785) B1521785
theorem B1015535 : Blo 1012602 1015535 := bstep (se 1 (by rfl) ⟨761651, by rfl⟩ : syracuseStep 1015535 = 1523303) B1523303
theorem B1015855 : Blo 1012602 1015855 := bstep (se 1 (by rfl) ⟨761891, by rfl⟩ : syracuseStep 1015855 = 1523783) B1523783
theorem B1015911 : Blo 1012602 1015911 := bstep (se 1 (by rfl) ⟨761933, by rfl⟩ : syracuseStep 1015911 = 1523867) B1523867
theorem B1016059 : Blo 1012602 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B1016447 : Blo 1012602 1016447 := bstep (se 1 (by rfl) ⟨762335, by rfl⟩ : syracuseStep 1016447 = 1524671) B1524671
theorem B2884585 : Blo 1012602 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B33293693 : Blo 1012602 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B38932973 : Blo 1012602 38932973 := bstep (se 3 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 38932973 = 14599865) B14599865
theorem B7705529 : Blo 1012602 7705529 := bstep (se 2 (by rfl) ⟨2889573, by rfl⟩ : syracuseStep 7705529 = 5779147) B5779147
theorem B6493135 : Blo 1012602 6493135 := bstep (se 1 (by rfl) ⟨4869851, by rfl⟩ : syracuseStep 6493135 = 9739703) B9739703
theorem B9737243 : Blo 1012602 9737243 := bstep (se 1 (by rfl) ⟨7302932, by rfl⟩ : syracuseStep 9737243 = 14605865) B14605865
theorem B1283455 : Blo 1012602 1283455 := bstep (se 1 (by rfl) ⟨962591, by rfl⟩ : syracuseStep 1283455 = 1925183) B1925183
theorem B1709545 : Blo 1012602 1709545 := bstep (se 2 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 1709545 = 1282159) B1282159
theorem B8033851 : Blo 1012602 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B21141161 : Blo 1012602 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B8659223 : Blo 1012602 8659223 := bstep (se 1 (by rfl) ⟨6494417, by rfl⟩ : syracuseStep 8659223 = 12988835) B12988835
theorem B32941039 : Blo 1012602 32941039 := bstep (se 1 (by rfl) ⟨24705779, by rfl⟩ : syracuseStep 32941039 = 49411559) B49411559
theorem B4400639 : Blo 1012602 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B19475099 : Blo 1012602 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B7318619 : Blo 1012602 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B43888169 : Blo 1012602 43888169 := bstep (se 2 (by rfl) ⟨16458063, by rfl⟩ : syracuseStep 43888169 = 32916127) B32916127
theorem B4337711 : Blo 1012602 4337711 := bstep (se 1 (by rfl) ⟨3253283, by rfl⟩ : syracuseStep 4337711 = 6506567) B6506567
theorem B7319771 : Blo 1012602 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B6501131 : Blo 1012602 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B8664347 : Blo 1012602 8664347 := bstep (se 1 (by rfl) ⟨6498260, by rfl⟩ : syracuseStep 8664347 = 12996521) B12996521
theorem B21968657 : Blo 1012602 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B3421979 : Blo 1012602 3421979 := bstep (se 1 (by rfl) ⟨2566484, by rfl⟩ : syracuseStep 3421979 = 5132969) B5132969
theorem B2570879 : Blo 1012602 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B199834631 : Blo 1012602 199834631 := bstep (se 1 (by rfl) ⟨149875973, by rfl⟩ : syracuseStep 199834631 = 299751947) B299751947
theorem B13026865 : Blo 1012602 13026865 := bstep (se 2 (by rfl) ⟨4885074, by rfl⟩ : syracuseStep 13026865 = 9770149) B9770149
theorem B3425921 : Blo 1012602 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B1623899 : Blo 1012602 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B3852143 : Blo 1012602 3852143 := bstep (se 1 (by rfl) ⟨2889107, by rfl⟩ : syracuseStep 3852143 = 5778215) B5778215
theorem B2738299 : Blo 1012602 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B5787895 : Blo 1012602 5787895 := bstep (se 1 (by rfl) ⟨4340921, by rfl⟩ : syracuseStep 5787895 = 8681843) B8681843
theorem B2282219 : Blo 1012602 2282219 := bstep (se 1 (by rfl) ⟨1711664, by rfl⟩ : syracuseStep 2282219 = 3423329) B3423329
theorem B2282363 : Blo 1012602 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B2283839 : Blo 1012602 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B4873081 : Blo 1012602 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B2286071 : Blo 1012602 2286071 := bstep (se 1 (by rfl) ⟨1714553, by rfl⟩ : syracuseStep 2286071 = 3429107) B3429107
theorem B1139647 : Blo 1012602 1139647 := bstep (se 1 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 1139647 = 1709471) B1709471
theorem B7824455 : Blo 1012602 7824455 := bstep (se 1 (by rfl) ⟨5868341, by rfl⟩ : syracuseStep 7824455 = 11736683) B11736683
theorem B1140583 : Blo 1012602 1140583 := bstep (se 1 (by rfl) ⟨855437, by rfl⟩ : syracuseStep 1140583 = 1710875) B1710875
theorem B1140943 : Blo 1012602 1140943 := bstep (se 1 (by rfl) ⟨855707, by rfl⟩ : syracuseStep 1140943 = 1711415) B1711415
theorem B39515161 : Blo 1012602 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B1013531 : Blo 1012602 1013531 := bstep (se 1 (by rfl) ⟨760148, by rfl⟩ : syracuseStep 1013531 = 1520297) B1520297
theorem B1014943 : Blo 1012602 1014943 := bstep (se 1 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 1014943 = 1522415) B1522415
theorem B1015579 : Blo 1012602 1015579 := bstep (se 1 (by rfl) ⟨761684, by rfl⟩ : syracuseStep 1015579 = 1523369) B1523369
theorem B17334161 : Blo 1012602 17334161 := bstep (se 2 (by rfl) ⟨6500310, by rfl⟩ : syracuseStep 17334161 = 13000621) B13000621
theorem B17369153 : Blo 1012602 17369153 := bstep (se 2 (by rfl) ⟨6513432, by rfl⟩ : syracuseStep 17369153 = 13026865) B13026865
theorem B25955315 : Blo 1012602 25955315 := bstep (se 1 (by rfl) ⟨19466486, by rfl⟩ : syracuseStep 25955315 = 38932973) B38932973
theorem B6491495 : Blo 1012602 6491495 := bstep (se 1 (by rfl) ⟨4868621, by rfl⟩ : syracuseStep 6491495 = 9737243) B9737243
theorem B14094107 : Blo 1012602 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B4330397 : Blo 1012602 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B5772815 : Blo 1012602 5772815 := bstep (se 1 (by rfl) ⟨4329611, by rfl⟩ : syracuseStep 5772815 = 8659223) B8659223
theorem B5216303 : Blo 1012602 5216303 := bstep (se 1 (by rfl) ⟨3912227, by rfl⟩ : syracuseStep 5216303 = 7824455) B7824455
theorem B8657513 : Blo 1012602 8657513 := bstep (se 2 (by rfl) ⟨3246567, by rfl⟩ : syracuseStep 8657513 = 6493135) B6493135
theorem B12983399 : Blo 1012602 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B1711273 : Blo 1012602 1711273 := bstep (se 2 (by rfl) ⟨641727, by rfl⟩ : syracuseStep 1711273 = 1283455) B1283455
theorem B2891807 : Blo 1012602 2891807 := bstep (se 1 (by rfl) ⟨2168855, by rfl⟩ : syracuseStep 2891807 = 4337711) B4337711
theorem B4334087 : Blo 1012602 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B5776231 : Blo 1012602 5776231 := bstep (se 1 (by rfl) ⟨4332173, by rfl⟩ : syracuseStep 5776231 = 8664347) B8664347
theorem B6497441 : Blo 1012602 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B1713919 : Blo 1012602 1713919 := bstep (se 1 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 1713919 = 2570879) B2570879
theorem B22195795 : Blo 1012602 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B2568095 : Blo 1012602 2568095 := bstep (se 1 (by rfl) ⟨1926071, by rfl⟩ : syracuseStep 2568095 = 3852143) B3852143
theorem B1519529 : Blo 1012602 1519529 := bstep (se 2 (by rfl) ⟨569823, by rfl⟩ : syracuseStep 1519529 = 1139647) B1139647
theorem B3846113 : Blo 1012602 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B43921385 : Blo 1012602 43921385 := bstep (se 2 (by rfl) ⟨16470519, by rfl⟩ : syracuseStep 43921385 = 32941039) B32941039
theorem B1520777 : Blo 1012602 1520777 := bstep (se 2 (by rfl) ⟨570291, by rfl⟩ : syracuseStep 1520777 = 1140583) B1140583
theorem B3651065 : Blo 1012602 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B1521257 : Blo 1012602 1521257 := bstep (se 2 (by rfl) ⟨570471, by rfl⟩ : syracuseStep 1521257 = 1140943) B1140943
theorem B1521479 : Blo 1012602 1521479 := bstep (se 1 (by rfl) ⟨1141109, by rfl⟩ : syracuseStep 1521479 = 2282219) B2282219
theorem B1521575 : Blo 1012602 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B1522559 : Blo 1012602 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B7717193 : Blo 1012602 7717193 := bstep (se 2 (by rfl) ⟨2893947, by rfl⟩ : syracuseStep 7717193 = 5787895) B5787895
theorem B1524047 : Blo 1012602 1524047 := bstep (se 1 (by rfl) ⟨1143035, by rfl⟩ : syracuseStep 1524047 = 2286071) B2286071
theorem B2933759 : Blo 1012602 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B2279393 : Blo 1012602 2279393 := bstep (se 2 (by rfl) ⟨854772, by rfl⟩ : syracuseStep 2279393 = 1709545) B1709545
theorem B2281319 : Blo 1012602 2281319 := bstep (se 1 (by rfl) ⟨1710989, by rfl⟩ : syracuseStep 2281319 = 3421979) B3421979
theorem B133223087 : Blo 1012602 133223087 := bstep (se 1 (by rfl) ⟨99917315, by rfl⟩ : syracuseStep 133223087 = 199834631) B199834631
theorem B11556107 : Blo 1012602 11556107 := bstep (se 1 (by rfl) ⟨8667080, by rfl⟩ : syracuseStep 11556107 = 17334161) B17334161
theorem B2283947 : Blo 1012602 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B5137019 : Blo 1012602 5137019 := bstep (se 1 (by rfl) ⟨3852764, by rfl⟩ : syracuseStep 5137019 = 7705529) B7705529
theorem B52686881 : Blo 1012602 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B4879079 : Blo 1012602 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B10711801 : Blo 1012602 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B29258779 : Blo 1012602 29258779 := bstep (se 1 (by rfl) ⟨21944084, by rfl⟩ : syracuseStep 29258779 = 43888169) B43888169
theorem B4879847 : Blo 1012602 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B14645771 : Blo 1012602 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B5144795 : Blo 1012602 5144795 := bstep (se 1 (by rfl) ⟨3858596, by rfl⟩ : syracuseStep 5144795 = 7717193) B7717193
theorem B1016031 : Blo 1012602 1016031 := bstep (se 1 (by rfl) ⟨762023, by rfl⟩ : syracuseStep 1016031 = 1524047) B1524047
theorem B7701641 : Blo 1012602 7701641 := bstep (se 2 (by rfl) ⟨2888115, by rfl⟩ : syracuseStep 7701641 = 5776231) B5776231
theorem B17303543 : Blo 1012602 17303543 := bstep (se 1 (by rfl) ⟨12977657, by rfl⟩ : syracuseStep 17303543 = 25955315) B25955315
theorem B4327663 : Blo 1012602 4327663 := bstep (se 1 (by rfl) ⟨3245747, by rfl⟩ : syracuseStep 4327663 = 6491495) B6491495
theorem B2886931 : Blo 1012602 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B7704071 : Blo 1012602 7704071 := bstep (se 1 (by rfl) ⟨5778053, by rfl⟩ : syracuseStep 7704071 = 11556107) B11556107
theorem B3477535 : Blo 1012602 3477535 := bstep (se 1 (by rfl) ⟨2608151, by rfl⟩ : syracuseStep 3477535 = 5216303) B5216303
theorem B5771675 : Blo 1012602 5771675 := bstep (se 1 (by rfl) ⟨4328756, by rfl⟩ : syracuseStep 5771675 = 8657513) B8657513
theorem B8655599 : Blo 1012602 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B29594393 : Blo 1012602 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B4331627 : Blo 1012602 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B1712063 : Blo 1012602 1712063 := bstep (se 1 (by rfl) ⟨1284047, by rfl⟩ : syracuseStep 1712063 = 2568095) B2568095
theorem B2564075 : Blo 1012602 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B3252719 : Blo 1012602 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B3253231 : Blo 1012602 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B2434043 : Blo 1012602 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B1519595 : Blo 1012602 1519595 := bstep (se 1 (by rfl) ⟨1139696, by rfl⟩ : syracuseStep 1519595 = 2279393) B2279393
theorem B11579435 : Blo 1012602 11579435 := bstep (se 1 (by rfl) ⟨8684576, by rfl⟩ : syracuseStep 11579435 = 17369153) B17369153
theorem B1520879 : Blo 1012602 1520879 := bstep (se 1 (by rfl) ⟨1140659, by rfl⟩ : syracuseStep 1520879 = 2281319) B2281319
theorem B3848543 : Blo 1012602 3848543 := bstep (se 1 (by rfl) ⟨2886407, by rfl⟩ : syracuseStep 3848543 = 5772815) B5772815
theorem B1522631 : Blo 1012602 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B3424679 : Blo 1012602 3424679 := bstep (se 1 (by rfl) ⟨2568509, by rfl⟩ : syracuseStep 3424679 = 5137019) B5137019
theorem B39011705 : Blo 1012602 39011705 := bstep (se 2 (by rfl) ⟨14629389, by rfl⟩ : syracuseStep 39011705 = 29258779) B29258779
theorem B29280923 : Blo 1012602 29280923 := bstep (se 1 (by rfl) ⟨21960692, by rfl⟩ : syracuseStep 29280923 = 43921385) B43921385
theorem B2281697 : Blo 1012602 2281697 := bstep (se 2 (by rfl) ⟨855636, by rfl⟩ : syracuseStep 2281697 = 1711273) B1711273
theorem B1955839 : Blo 1012602 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B11557565 : Blo 1012602 11557565 := bstep (se 3 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 11557565 = 4334087) B4334087
theorem B355261565 : Blo 1012602 355261565 := bstep (se 3 (by rfl) ⟨66611543, by rfl⟩ : syracuseStep 355261565 = 133223087) B133223087
theorem B2285225 : Blo 1012602 2285225 := bstep (se 2 (by rfl) ⟨856959, by rfl⟩ : syracuseStep 2285225 = 1713919) B1713919
theorem B9396071 : Blo 1012602 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B1927871 : Blo 1012602 1927871 := bstep (se 1 (by rfl) ⟨1445903, by rfl⟩ : syracuseStep 1927871 = 2891807) B2891807
theorem B14282401 : Blo 1012602 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B1013019 : Blo 1012602 1013019 := bstep (se 1 (by rfl) ⟨759764, by rfl⟩ : syracuseStep 1013019 = 1519529) B1519529
theorem B35124587 : Blo 1012602 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B1013851 : Blo 1012602 1013851 := bstep (se 1 (by rfl) ⟨760388, by rfl⟩ : syracuseStep 1013851 = 1520777) B1520777
theorem B1014171 : Blo 1012602 1014171 := bstep (se 1 (by rfl) ⟨760628, by rfl⟩ : syracuseStep 1014171 = 1521257) B1521257
theorem B1014319 : Blo 1012602 1014319 := bstep (se 1 (by rfl) ⟨760739, by rfl⟩ : syracuseStep 1014319 = 1521479) B1521479
theorem B1014383 : Blo 1012602 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B9763847 : Blo 1012602 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B1015039 : Blo 1012602 1015039 := bstep (se 1 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 1015039 = 1522559) B1522559
theorem B74187413 : Blo 1012602 74187413 := bstep (se 6 (by rfl) ⟨1738767, by rfl⟩ : syracuseStep 74187413 = 3477535) B3477535
theorem B11535695 : Blo 1012602 11535695 := bstep (se 1 (by rfl) ⟨8651771, by rfl⟩ : syracuseStep 11535695 = 17303543) B17303543
theorem B5770217 : Blo 1012602 5770217 := bstep (se 2 (by rfl) ⟨2163831, by rfl⟩ : syracuseStep 5770217 = 4327663) B4327663
theorem B5770399 : Blo 1012602 5770399 := bstep (se 1 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 5770399 = 8655599) B8655599
theorem B19729595 : Blo 1012602 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B2887751 : Blo 1012602 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B7705043 : Blo 1012602 7705043 := bstep (se 1 (by rfl) ⟨5778782, by rfl⟩ : syracuseStep 7705043 = 11557565) B11557565
theorem B19043201 : Blo 1012602 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B6264047 : Blo 1012602 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B1709383 : Blo 1012602 1709383 := bstep (se 1 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 1709383 = 2564075) B2564075
theorem B2168479 : Blo 1012602 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B1285247 : Blo 1012602 1285247 := bstep (se 1 (by rfl) ⟨963935, by rfl⟩ : syracuseStep 1285247 = 1927871) B1927871
theorem B2565695 : Blo 1012602 2565695 := bstep (se 1 (by rfl) ⟨1924271, by rfl⟩ : syracuseStep 2565695 = 3848543) B3848543
theorem B4337641 : Blo 1012602 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B1521131 : Blo 1012602 1521131 := bstep (se 1 (by rfl) ⟨1140848, by rfl⟩ : syracuseStep 1521131 = 2281697) B2281697
theorem B3847783 : Blo 1012602 3847783 := bstep (se 1 (by rfl) ⟨2885837, by rfl⟩ : syracuseStep 3847783 = 5771675) B5771675
theorem B3849241 : Blo 1012602 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B1523483 : Blo 1012602 1523483 := bstep (se 1 (by rfl) ⟨1142612, by rfl⟩ : syracuseStep 1523483 = 2285225) B2285225
theorem B1622695 : Blo 1012602 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B2607785 : Blo 1012602 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B7719623 : Blo 1012602 7719623 := bstep (se 1 (by rfl) ⟨5789717, by rfl⟩ : syracuseStep 7719623 = 11579435) B11579435
theorem B23416391 : Blo 1012602 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B6509231 : Blo 1012602 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B3429863 : Blo 1012602 3429863 := bstep (se 1 (by rfl) ⟨2572397, by rfl⟩ : syracuseStep 3429863 = 5144795) B5144795
theorem B2283119 : Blo 1012602 2283119 := bstep (se 1 (by rfl) ⟨1712339, by rfl⟩ : syracuseStep 2283119 = 3424679) B3424679
theorem B5134427 : Blo 1012602 5134427 := bstep (se 1 (by rfl) ⟨3850820, by rfl⟩ : syracuseStep 5134427 = 7701641) B7701641
theorem B26007803 : Blo 1012602 26007803 := bstep (se 1 (by rfl) ⟨19505852, by rfl⟩ : syracuseStep 26007803 = 39011705) B39011705
theorem B19520615 : Blo 1012602 19520615 := bstep (se 1 (by rfl) ⟨14640461, by rfl⟩ : syracuseStep 19520615 = 29280923) B29280923
theorem B5136047 : Blo 1012602 5136047 := bstep (se 1 (by rfl) ⟨3852035, by rfl⟩ : syracuseStep 5136047 = 7704071) B7704071
theorem B236841043 : Blo 1012602 236841043 := bstep (se 1 (by rfl) ⟨177630782, by rfl⟩ : syracuseStep 236841043 = 355261565) B355261565
theorem B1141375 : Blo 1012602 1141375 := bstep (se 1 (by rfl) ⟨856031, by rfl⟩ : syracuseStep 1141375 = 1712063) B1712063
theorem B1013063 : Blo 1012602 1013063 := bstep (se 1 (by rfl) ⟨759797, by rfl⟩ : syracuseStep 1013063 = 1519595) B1519595
theorem B1013919 : Blo 1012602 1013919 := bstep (se 1 (by rfl) ⟨760439, by rfl⟩ : syracuseStep 1013919 = 1520879) B1520879
theorem B1015087 : Blo 1012602 1015087 := bstep (se 1 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 1015087 = 1522631) B1522631
theorem B7700669 : Blo 1012602 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B2163593 : Blo 1012602 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B1738523 : Blo 1012602 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B5146415 : Blo 1012602 5146415 := bstep (se 1 (by rfl) ⟨3859811, by rfl⟩ : syracuseStep 5146415 = 7719623) B7719623
theorem B315788057 : Blo 1012602 315788057 := bstep (se 2 (by rfl) ⟨118420521, by rfl⟩ : syracuseStep 315788057 = 236841043) B236841043
theorem B17338535 : Blo 1012602 17338535 := bstep (se 1 (by rfl) ⟨13003901, by rfl⟩ : syracuseStep 17338535 = 26007803) B26007803
theorem B13013743 : Blo 1012602 13013743 := bstep (se 1 (by rfl) ⟨9760307, by rfl⟩ : syracuseStep 13013743 = 19520615) B19520615
theorem B1710463 : Blo 1012602 1710463 := bstep (se 1 (by rfl) ⟨1282847, by rfl⟩ : syracuseStep 1710463 = 2565695) B2565695
theorem B2891305 : Blo 1012602 2891305 := bstep (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) B2168479
theorem B49458275 : Blo 1012602 49458275 := bstep (se 1 (by rfl) ⟨37093706, by rfl⟩ : syracuseStep 49458275 = 74187413) B74187413
theorem B3846811 : Blo 1012602 3846811 := bstep (se 1 (by rfl) ⟨2885108, by rfl⟩ : syracuseStep 3846811 = 5770217) B5770217
theorem B13153063 : Blo 1012602 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B15610927 : Blo 1012602 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B4339487 : Blo 1012602 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B12695467 : Blo 1012602 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B4176031 : Blo 1012602 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B1521833 : Blo 1012602 1521833 := bstep (se 2 (by rfl) ⟨570687, by rfl⟩ : syracuseStep 1521833 = 1141375) B1141375
theorem B1522079 : Blo 1012602 1522079 := bstep (se 1 (by rfl) ⟨1141559, by rfl⟩ : syracuseStep 1522079 = 2283119) B2283119
theorem B3422951 : Blo 1012602 3422951 := bstep (se 1 (by rfl) ⟨2567213, by rfl⟩ : syracuseStep 3422951 = 5134427) B5134427
theorem B3424031 : Blo 1012602 3424031 := bstep (se 1 (by rfl) ⟨2568023, by rfl⟩ : syracuseStep 3424031 = 5136047) B5136047
theorem B5783521 : Blo 1012602 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B2279177 : Blo 1012602 2279177 := bstep (se 2 (by rfl) ⟨854691, by rfl⟩ : syracuseStep 2279177 = 1709383) B1709383
theorem B5130377 : Blo 1012602 5130377 := bstep (se 2 (by rfl) ⟨1923891, by rfl⟩ : syracuseStep 5130377 = 3847783) B3847783
theorem B3427325 : Blo 1012602 3427325 := bstep (se 3 (by rfl) ⟨642623, by rfl⟩ : syracuseStep 3427325 = 1285247) B1285247
theorem B5132321 : Blo 1012602 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B7690463 : Blo 1012602 7690463 := bstep (se 1 (by rfl) ⟨5767847, by rfl⟩ : syracuseStep 7690463 = 11535695) B11535695
theorem B5136695 : Blo 1012602 5136695 := bstep (se 1 (by rfl) ⟨3852521, by rfl⟩ : syracuseStep 5136695 = 7705043) B7705043
theorem B2286575 : Blo 1012602 2286575 := bstep (se 1 (by rfl) ⟨1714931, by rfl⟩ : syracuseStep 2286575 = 3429863) B3429863
theorem B7693865 : Blo 1012602 7693865 := bstep (se 2 (by rfl) ⟨2885199, by rfl⟩ : syracuseStep 7693865 = 5770399) B5770399
theorem B1014087 : Blo 1012602 1014087 := bstep (se 1 (by rfl) ⟨760565, by rfl⟩ : syracuseStep 1014087 = 1521131) B1521131
theorem B1015655 : Blo 1012602 1015655 := bstep (se 1 (by rfl) ⟨761741, by rfl⟩ : syracuseStep 1015655 = 1523483) B1523483
theorem B1442395 : Blo 1012602 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B17537417 : Blo 1012602 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B20814569 : Blo 1012602 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B32972183 : Blo 1012602 32972183 := bstep (se 1 (by rfl) ⟨24729137, by rfl⟩ : syracuseStep 32972183 = 49458275) B49458275
theorem B2892991 : Blo 1012602 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B7711361 : Blo 1012602 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B1519451 : Blo 1012602 1519451 := bstep (se 1 (by rfl) ⟨1139588, by rfl⟩ : syracuseStep 1519451 = 2279177) B2279177
theorem B3420251 : Blo 1012602 3420251 := bstep (se 1 (by rfl) ⟨2565188, by rfl⟩ : syracuseStep 3420251 = 5130377) B5130377
theorem B3421547 : Blo 1012602 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B5126975 : Blo 1012602 5126975 := bstep (se 1 (by rfl) ⟨3845231, by rfl⟩ : syracuseStep 5126975 = 7690463) B7690463
theorem B4636061 : Blo 1012602 4636061 := bstep (se 3 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 4636061 = 1738523) B1738523
theorem B3424463 : Blo 1012602 3424463 := bstep (se 1 (by rfl) ⟨2568347, by rfl⟩ : syracuseStep 3424463 = 5136695) B5136695
theorem B1524383 : Blo 1012602 1524383 := bstep (se 1 (by rfl) ⟨1143287, by rfl⟩ : syracuseStep 1524383 = 2286575) B2286575
theorem B5129081 : Blo 1012602 5129081 := bstep (se 2 (by rfl) ⟨1923405, by rfl⟩ : syracuseStep 5129081 = 3846811) B3846811
theorem B17351657 : Blo 1012602 17351657 := bstep (se 2 (by rfl) ⟨6506871, by rfl⟩ : syracuseStep 17351657 = 13013743) B13013743
theorem B5129243 : Blo 1012602 5129243 := bstep (se 1 (by rfl) ⟨3846932, by rfl⟩ : syracuseStep 5129243 = 7693865) B7693865
theorem B16927289 : Blo 1012602 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B2280617 : Blo 1012602 2280617 := bstep (se 2 (by rfl) ⟨855231, by rfl⟩ : syracuseStep 2280617 = 1710463) B1710463
theorem B2281967 : Blo 1012602 2281967 := bstep (se 1 (by rfl) ⟨1711475, by rfl⟩ : syracuseStep 2281967 = 3422951) B3422951
theorem B3855073 : Blo 1012602 3855073 := bstep (se 2 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 3855073 = 2891305) B2891305
theorem B2282687 : Blo 1012602 2282687 := bstep (se 1 (by rfl) ⟨1712015, by rfl⟩ : syracuseStep 2282687 = 3424031) B3424031
theorem B5133779 : Blo 1012602 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B3430943 : Blo 1012602 3430943 := bstep (se 1 (by rfl) ⟨2573207, by rfl⟩ : syracuseStep 3430943 = 5146415) B5146415
theorem B210525371 : Blo 1012602 210525371 := bstep (se 1 (by rfl) ⟨157894028, by rfl⟩ : syracuseStep 210525371 = 315788057) B315788057
theorem B2284883 : Blo 1012602 2284883 := bstep (se 1 (by rfl) ⟨1713662, by rfl⟩ : syracuseStep 2284883 = 3427325) B3427325
theorem B11559023 : Blo 1012602 11559023 := bstep (se 1 (by rfl) ⟨8669267, by rfl⟩ : syracuseStep 11559023 = 17338535) B17338535
theorem B5568041 : Blo 1012602 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B1014555 : Blo 1012602 1014555 := bstep (se 1 (by rfl) ⟨760916, by rfl⟩ : syracuseStep 1014555 = 1521833) B1521833
theorem B1014719 : Blo 1012602 1014719 := bstep (se 1 (by rfl) ⟨761039, by rfl⟩ : syracuseStep 1014719 = 1522079) B1522079
theorem B1016255 : Blo 1012602 1016255 := bstep (se 1 (by rfl) ⟨762191, by rfl⟩ : syracuseStep 1016255 = 1524383) B1524383
theorem B11567771 : Blo 1012602 11567771 := bstep (se 1 (by rfl) ⟨8675828, by rfl⟩ : syracuseStep 11567771 = 17351657) B17351657
theorem B14848109 : Blo 1012602 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B140350247 : Blo 1012602 140350247 := bstep (se 1 (by rfl) ⟨105262685, by rfl⟩ : syracuseStep 140350247 = 210525371) B210525371
theorem B7706015 : Blo 1012602 7706015 := bstep (se 1 (by rfl) ⟨5779511, by rfl⟩ : syracuseStep 7706015 = 11559023) B11559023
theorem B3417983 : Blo 1012602 3417983 := bstep (se 1 (by rfl) ⟨2563487, by rfl⟩ : syracuseStep 3417983 = 5126975) B5126975
theorem B3090707 : Blo 1012602 3090707 := bstep (se 1 (by rfl) ⟨2318030, by rfl⟩ : syracuseStep 3090707 = 4636061) B4636061
theorem B3419387 : Blo 1012602 3419387 := bstep (se 1 (by rfl) ⟨2564540, by rfl⟩ : syracuseStep 3419387 = 5129081) B5129081
theorem B3419495 : Blo 1012602 3419495 := bstep (se 1 (by rfl) ⟨2564621, by rfl⟩ : syracuseStep 3419495 = 5129243) B5129243
theorem B11284859 : Blo 1012602 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B1520411 : Blo 1012602 1520411 := bstep (se 1 (by rfl) ⟨1140308, by rfl⟩ : syracuseStep 1520411 = 2280617) B2280617
theorem B1521311 : Blo 1012602 1521311 := bstep (se 1 (by rfl) ⟨1140983, by rfl⟩ : syracuseStep 1521311 = 2281967) B2281967
theorem B1521791 : Blo 1012602 1521791 := bstep (se 1 (by rfl) ⟨1141343, by rfl⟩ : syracuseStep 1521791 = 2282687) B2282687
theorem B3422519 : Blo 1012602 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B13876379 : Blo 1012602 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B1523255 : Blo 1012602 1523255 := bstep (se 1 (by rfl) ⟨1142441, by rfl⟩ : syracuseStep 1523255 = 2284883) B2284883
theorem B2280167 : Blo 1012602 2280167 := bstep (se 1 (by rfl) ⟨1710125, by rfl⟩ : syracuseStep 2280167 = 3420251) B3420251
theorem B2281031 : Blo 1012602 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B2282975 : Blo 1012602 2282975 := bstep (se 1 (by rfl) ⟨1712231, by rfl⟩ : syracuseStep 2282975 = 3424463) B3424463
theorem B1923193 : Blo 1012602 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B3857321 : Blo 1012602 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B11691611 : Blo 1012602 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B2287295 : Blo 1012602 2287295 := bstep (se 1 (by rfl) ⟨1715471, by rfl⟩ : syracuseStep 2287295 = 3430943) B3430943
theorem B21981455 : Blo 1012602 21981455 := bstep (se 1 (by rfl) ⟨16486091, by rfl⟩ : syracuseStep 21981455 = 32972183) B32972183
theorem B5140097 : Blo 1012602 5140097 := bstep (se 2 (by rfl) ⟨1927536, by rfl⟩ : syracuseStep 5140097 = 3855073) B3855073
theorem B5140907 : Blo 1012602 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B1012967 : Blo 1012602 1012967 := bstep (se 1 (by rfl) ⟨759725, by rfl⟩ : syracuseStep 1012967 = 1519451) B1519451
theorem B9898739 : Blo 1012602 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B14654303 : Blo 1012602 14654303 := bstep (se 1 (by rfl) ⟨10990727, by rfl⟩ : syracuseStep 14654303 = 21981455) B21981455
theorem B2564257 : Blo 1012602 2564257 := bstep (se 2 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 2564257 = 1923193) B1923193
theorem B9250919 : Blo 1012602 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B7711847 : Blo 1012602 7711847 := bstep (se 1 (by rfl) ⟨5783885, by rfl⟩ : syracuseStep 7711847 = 11567771) B11567771
theorem B1520111 : Blo 1012602 1520111 := bstep (se 1 (by rfl) ⟨1140083, by rfl⟩ : syracuseStep 1520111 = 2280167) B2280167
theorem B1520687 : Blo 1012602 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B93566831 : Blo 1012602 93566831 := bstep (se 1 (by rfl) ⟨70175123, by rfl⟩ : syracuseStep 93566831 = 140350247) B140350247
theorem B1521983 : Blo 1012602 1521983 := bstep (se 1 (by rfl) ⟨1141487, by rfl⟩ : syracuseStep 1521983 = 2282975) B2282975
theorem B2571547 : Blo 1012602 2571547 := bstep (se 1 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 2571547 = 3857321) B3857321
theorem B1524863 : Blo 1012602 1524863 := bstep (se 1 (by rfl) ⟨1143647, by rfl⟩ : syracuseStep 1524863 = 2287295) B2287295
theorem B2278655 : Blo 1012602 2278655 := bstep (se 1 (by rfl) ⟨1708991, by rfl⟩ : syracuseStep 2278655 = 3417983) B3417983
theorem B2279591 : Blo 1012602 2279591 := bstep (se 1 (by rfl) ⟨1709693, by rfl⟩ : syracuseStep 2279591 = 3419387) B3419387
theorem B2279663 : Blo 1012602 2279663 := bstep (se 1 (by rfl) ⟨1709747, by rfl⟩ : syracuseStep 2279663 = 3419495) B3419495
theorem B3426731 : Blo 1012602 3426731 := bstep (se 1 (by rfl) ⟨2570048, by rfl⟩ : syracuseStep 3426731 = 5140097) B5140097
theorem B7523239 : Blo 1012602 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B3427271 : Blo 1012602 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B2281679 : Blo 1012602 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B5137343 : Blo 1012602 5137343 := bstep (se 1 (by rfl) ⟨3853007, by rfl⟩ : syracuseStep 5137343 = 7706015) B7706015
theorem B7794407 : Blo 1012602 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B2060471 : Blo 1012602 2060471 := bstep (se 1 (by rfl) ⟨1545353, by rfl⟩ : syracuseStep 2060471 = 3090707) B3090707
theorem B1013607 : Blo 1012602 1013607 := bstep (se 1 (by rfl) ⟨760205, by rfl⟩ : syracuseStep 1013607 = 1520411) B1520411
theorem B1014207 : Blo 1012602 1014207 := bstep (se 1 (by rfl) ⟨760655, by rfl⟩ : syracuseStep 1014207 = 1521311) B1521311
theorem B1014527 : Blo 1012602 1014527 := bstep (se 1 (by rfl) ⟨760895, by rfl⟩ : syracuseStep 1014527 = 1521791) B1521791
theorem B1015503 : Blo 1012602 1015503 := bstep (se 1 (by rfl) ⟨761627, by rfl⟩ : syracuseStep 1015503 = 1523255) B1523255
theorem B1016575 : Blo 1012602 1016575 := bstep (se 1 (by rfl) ⟨762431, by rfl⟩ : syracuseStep 1016575 = 1524863) B1524863
theorem B10030985 : Blo 1012602 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B9769535 : Blo 1012602 9769535 := bstep (se 1 (by rfl) ⟨7327151, by rfl⟩ : syracuseStep 9769535 = 14654303) B14654303
theorem B6167279 : Blo 1012602 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B3419009 : Blo 1012602 3419009 := bstep (se 2 (by rfl) ⟨1282128, by rfl⟩ : syracuseStep 3419009 = 2564257) B2564257
theorem B1519103 : Blo 1012602 1519103 := bstep (se 1 (by rfl) ⟨1139327, by rfl⟩ : syracuseStep 1519103 = 2278655) B2278655
theorem B1519727 : Blo 1012602 1519727 := bstep (se 1 (by rfl) ⟨1139795, by rfl⟩ : syracuseStep 1519727 = 2279591) B2279591
theorem B1519775 : Blo 1012602 1519775 := bstep (se 1 (by rfl) ⟨1139831, by rfl⟩ : syracuseStep 1519775 = 2279663) B2279663
theorem B6599159 : Blo 1012602 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B1521119 : Blo 1012602 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B249511549 : Blo 1012602 249511549 := bstep (se 3 (by rfl) ⟨46783415, by rfl⟩ : syracuseStep 249511549 = 93566831) B93566831
theorem B3424895 : Blo 1012602 3424895 := bstep (se 1 (by rfl) ⟨2568671, by rfl⟩ : syracuseStep 3424895 = 5137343) B5137343
theorem B5196271 : Blo 1012602 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B3428729 : Blo 1012602 3428729 := bstep (se 2 (by rfl) ⟨1285773, by rfl⟩ : syracuseStep 3428729 = 2571547) B2571547
theorem B2284487 : Blo 1012602 2284487 := bstep (se 1 (by rfl) ⟨1713365, by rfl⟩ : syracuseStep 2284487 = 3426731) B3426731
theorem B2284847 : Blo 1012602 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B5141231 : Blo 1012602 5141231 := bstep (se 1 (by rfl) ⟨3855923, by rfl⟩ : syracuseStep 5141231 = 7711847) B7711847
theorem B1373647 : Blo 1012602 1373647 := bstep (se 1 (by rfl) ⟨1030235, by rfl⟩ : syracuseStep 1373647 = 2060471) B2060471
theorem B1013407 : Blo 1012602 1013407 := bstep (se 1 (by rfl) ⟨760055, by rfl⟩ : syracuseStep 1013407 = 1520111) B1520111
theorem B1013791 : Blo 1012602 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B1014655 : Blo 1012602 1014655 := bstep (se 1 (by rfl) ⟨760991, by rfl⟩ : syracuseStep 1014655 = 1521983) B1521983
theorem B6687323 : Blo 1012602 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B4399439 : Blo 1012602 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B6928361 : Blo 1012602 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B4111519 : Blo 1012602 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B1522991 : Blo 1012602 1522991 := bstep (se 1 (by rfl) ⟨1142243, by rfl⟩ : syracuseStep 1522991 = 2284487) B2284487
theorem B1523231 : Blo 1012602 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B2279339 : Blo 1012602 2279339 := bstep (se 1 (by rfl) ⟨1709504, by rfl⟩ : syracuseStep 2279339 = 3419009) B3419009
theorem B3427487 : Blo 1012602 3427487 := bstep (se 1 (by rfl) ⟨2570615, by rfl⟩ : syracuseStep 3427487 = 5141231) B5141231
theorem B332682065 : Blo 1012602 332682065 := bstep (se 2 (by rfl) ⟨124755774, by rfl⟩ : syracuseStep 332682065 = 249511549) B249511549
theorem B2283263 : Blo 1012602 2283263 := bstep (se 1 (by rfl) ⟨1712447, by rfl⟩ : syracuseStep 2283263 = 3424895) B3424895
theorem B2285819 : Blo 1012602 2285819 := bstep (se 1 (by rfl) ⟨1714364, by rfl⟩ : syracuseStep 2285819 = 3428729) B3428729
theorem B6513023 : Blo 1012602 6513023 := bstep (se 1 (by rfl) ⟨4884767, by rfl⟩ : syracuseStep 6513023 = 9769535) B9769535
theorem B1831529 : Blo 1012602 1831529 := bstep (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) B1373647
theorem B1012735 : Blo 1012602 1012735 := bstep (se 1 (by rfl) ⟨759551, by rfl⟩ : syracuseStep 1012735 = 1519103) B1519103
theorem B1013151 : Blo 1012602 1013151 := bstep (se 1 (by rfl) ⟨759863, by rfl⟩ : syracuseStep 1013151 = 1519727) B1519727
theorem B1013183 : Blo 1012602 1013183 := bstep (se 1 (by rfl) ⟨759887, by rfl⟩ : syracuseStep 1013183 = 1519775) B1519775
theorem B1014079 : Blo 1012602 1014079 := bstep (se 1 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 1014079 = 1521119) B1521119
theorem B4884077 : Blo 1012602 4884077 := bstep (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) B1831529
theorem B4458215 : Blo 1012602 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B46927349 : Blo 1012602 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B5482025 : Blo 1012602 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B1519559 : Blo 1012602 1519559 := bstep (se 1 (by rfl) ⟨1139669, by rfl⟩ : syracuseStep 1519559 = 2279339) B2279339
theorem B221788043 : Blo 1012602 221788043 := bstep (se 1 (by rfl) ⟨166341032, by rfl⟩ : syracuseStep 221788043 = 332682065) B332682065
theorem B1522175 : Blo 1012602 1522175 := bstep (se 1 (by rfl) ⟨1141631, by rfl⟩ : syracuseStep 1522175 = 2283263) B2283263
theorem B1523879 : Blo 1012602 1523879 := bstep (se 1 (by rfl) ⟨1142909, by rfl⟩ : syracuseStep 1523879 = 2285819) B2285819
theorem B4342015 : Blo 1012602 4342015 := bstep (se 1 (by rfl) ⟨3256511, by rfl⟩ : syracuseStep 4342015 = 6513023) B6513023
theorem B2284991 : Blo 1012602 2284991 := bstep (se 1 (by rfl) ⟨1713743, by rfl⟩ : syracuseStep 2284991 = 3427487) B3427487
theorem B4618907 : Blo 1012602 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B1015327 : Blo 1012602 1015327 := bstep (se 1 (by rfl) ⟨761495, by rfl⟩ : syracuseStep 1015327 = 1522991) B1522991
theorem B1015487 : Blo 1012602 1015487 := bstep (se 1 (by rfl) ⟨761615, by rfl⟩ : syracuseStep 1015487 = 1523231) B1523231
theorem B1015919 : Blo 1012602 1015919 := bstep (se 1 (by rfl) ⟨761939, by rfl⟩ : syracuseStep 1015919 = 1523879) B1523879
theorem B147858695 : Blo 1012602 147858695 := bstep (se 1 (by rfl) ⟨110894021, by rfl⟩ : syracuseStep 147858695 = 221788043) B221788043
theorem B3256051 : Blo 1012602 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B1523327 : Blo 1012602 1523327 := bstep (se 1 (by rfl) ⟨1142495, by rfl⟩ : syracuseStep 1523327 = 2284991) B2284991
theorem B3654683 : Blo 1012602 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B5789353 : Blo 1012602 5789353 := bstep (se 2 (by rfl) ⟨2171007, by rfl⟩ : syracuseStep 5789353 = 4342015) B4342015
theorem B2972143 : Blo 1012602 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B31284899 : Blo 1012602 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B1013039 : Blo 1012602 1013039 := bstep (se 1 (by rfl) ⟨759779, by rfl⟩ : syracuseStep 1013039 = 1519559) B1519559
theorem B1014783 : Blo 1012602 1014783 := bstep (se 1 (by rfl) ⟨761087, by rfl⟩ : syracuseStep 1014783 = 1522175) B1522175
theorem B3079271 : Blo 1012602 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B98572463 : Blo 1012602 98572463 := bstep (se 1 (by rfl) ⟨73929347, by rfl⟩ : syracuseStep 98572463 = 147858695) B147858695
theorem B2436455 : Blo 1012602 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B4341401 : Blo 1012602 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B20856599 : Blo 1012602 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B7719137 : Blo 1012602 7719137 := bstep (se 2 (by rfl) ⟨2894676, by rfl⟩ : syracuseStep 7719137 = 5789353) B5789353
theorem B2052847 : Blo 1012602 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B3962857 : Blo 1012602 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B1015551 : Blo 1012602 1015551 := bstep (se 1 (by rfl) ⟨761663, by rfl⟩ : syracuseStep 1015551 = 1523327) B1523327
theorem B5146091 : Blo 1012602 5146091 := bstep (se 1 (by rfl) ⟨3859568, by rfl⟩ : syracuseStep 5146091 = 7719137) B7719137
theorem B10948517 : Blo 1012602 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B5283809 : Blo 1012602 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B2894267 : Blo 1012602 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B13904399 : Blo 1012602 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B65714975 : Blo 1012602 65714975 := bstep (se 1 (by rfl) ⟨49286231, by rfl⟩ : syracuseStep 65714975 = 98572463) B98572463
theorem B1624303 : Blo 1012602 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B8662949 : Blo 1012602 8662949 := bstep (se 4 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 8662949 = 1624303) B1624303
theorem B3522539 : Blo 1012602 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B37078397 : Blo 1012602 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B3430727 : Blo 1012602 3430727 := bstep (se 1 (by rfl) ⟨2573045, by rfl⟩ : syracuseStep 3430727 = 5146091) B5146091
theorem B7299011 : Blo 1012602 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B1929511 : Blo 1012602 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B43809983 : Blo 1012602 43809983 := bstep (se 1 (by rfl) ⟨32857487, by rfl⟩ : syracuseStep 43809983 = 65714975) B65714975
theorem B5775299 : Blo 1012602 5775299 := bstep (se 1 (by rfl) ⟨4331474, by rfl⟩ : syracuseStep 5775299 = 8662949) B8662949
theorem B29206655 : Blo 1012602 29206655 := bstep (se 1 (by rfl) ⟨21904991, by rfl⟩ : syracuseStep 29206655 = 43809983) B43809983
theorem B24718931 : Blo 1012602 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B4866007 : Blo 1012602 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B2572681 : Blo 1012602 2572681 := bstep (se 2 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 2572681 = 1929511) B1929511
theorem B2348359 : Blo 1012602 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B2287151 : Blo 1012602 2287151 := bstep (se 1 (by rfl) ⟨1715363, by rfl⟩ : syracuseStep 2287151 = 3430727) B3430727
theorem B19471103 : Blo 1012602 19471103 := bstep (se 1 (by rfl) ⟨14603327, by rfl⟩ : syracuseStep 19471103 = 29206655) B29206655
theorem B12524581 : Blo 1012602 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B3850199 : Blo 1012602 3850199 := bstep (se 1 (by rfl) ⟨2887649, by rfl⟩ : syracuseStep 3850199 = 5775299) B5775299
theorem B1524767 : Blo 1012602 1524767 := bstep (se 1 (by rfl) ⟨1143575, by rfl⟩ : syracuseStep 1524767 = 2287151) B2287151
theorem B3430241 : Blo 1012602 3430241 := bstep (se 2 (by rfl) ⟨1286340, by rfl⟩ : syracuseStep 3430241 = 2572681) B2572681
theorem B16479287 : Blo 1012602 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B6488009 : Blo 1012602 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B1016511 : Blo 1012602 1016511 := bstep (se 1 (by rfl) ⟨762383, by rfl⟩ : syracuseStep 1016511 = 1524767) B1524767
theorem B12980735 : Blo 1012602 12980735 := bstep (se 1 (by rfl) ⟨9735551, by rfl⟩ : syracuseStep 12980735 = 19471103) B19471103
theorem B10986191 : Blo 1012602 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B2566799 : Blo 1012602 2566799 := bstep (se 1 (by rfl) ⟨1925099, by rfl⟩ : syracuseStep 2566799 = 3850199) B3850199
theorem B16699441 : Blo 1012602 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B2286827 : Blo 1012602 2286827 := bstep (se 1 (by rfl) ⟨1715120, by rfl⟩ : syracuseStep 2286827 = 3430241) B3430241
theorem B4325339 : Blo 1012602 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B8653823 : Blo 1012602 8653823 := bstep (se 1 (by rfl) ⟨6490367, by rfl⟩ : syracuseStep 8653823 = 12980735) B12980735
theorem B1711199 : Blo 1012602 1711199 := bstep (se 1 (by rfl) ⟨1283399, by rfl⟩ : syracuseStep 1711199 = 2566799) B2566799
theorem B22265921 : Blo 1012602 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B7324127 : Blo 1012602 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B1524551 : Blo 1012602 1524551 := bstep (se 1 (by rfl) ⟨1143413, by rfl⟩ : syracuseStep 1524551 = 2286827) B2286827
theorem B11534237 : Blo 1012602 11534237 := bstep (se 3 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 11534237 = 4325339) B4325339
theorem B14843947 : Blo 1012602 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B4882751 : Blo 1012602 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B1016367 : Blo 1012602 1016367 := bstep (se 1 (by rfl) ⟨762275, by rfl⟩ : syracuseStep 1016367 = 1524551) B1524551
theorem B5769215 : Blo 1012602 5769215 := bstep (se 1 (by rfl) ⟨4326911, by rfl⟩ : syracuseStep 5769215 = 8653823) B8653823
theorem B7689491 : Blo 1012602 7689491 := bstep (se 1 (by rfl) ⟨5767118, by rfl⟩ : syracuseStep 7689491 = 11534237) B11534237
theorem B1140799 : Blo 1012602 1140799 := bstep (se 1 (by rfl) ⟨855599, by rfl⟩ : syracuseStep 1140799 = 1711199) B1711199
theorem B19791929 : Blo 1012602 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B3255167 : Blo 1012602 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B3846143 : Blo 1012602 3846143 := bstep (se 1 (by rfl) ⟨2884607, by rfl⟩ : syracuseStep 3846143 = 5769215) B5769215
theorem B1521065 : Blo 1012602 1521065 := bstep (se 2 (by rfl) ⟨570399, by rfl⟩ : syracuseStep 1521065 = 1140799) B1140799
theorem B5126327 : Blo 1012602 5126327 := bstep (se 1 (by rfl) ⟨3844745, by rfl⟩ : syracuseStep 5126327 = 7689491) B7689491
theorem B2564095 : Blo 1012602 2564095 := bstep (se 1 (by rfl) ⟨1923071, by rfl⟩ : syracuseStep 2564095 = 3846143) B3846143
theorem B3417551 : Blo 1012602 3417551 := bstep (se 1 (by rfl) ⟨2563163, by rfl⟩ : syracuseStep 3417551 = 5126327) B5126327
theorem B13194619 : Blo 1012602 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B8680445 : Blo 1012602 8680445 := bstep (se 3 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 8680445 = 3255167) B3255167
theorem B1014043 : Blo 1012602 1014043 := bstep (se 1 (by rfl) ⟨760532, by rfl⟩ : syracuseStep 1014043 = 1521065) B1521065
theorem B3418793 : Blo 1012602 3418793 := bstep (se 2 (by rfl) ⟨1282047, by rfl⟩ : syracuseStep 3418793 = 2564095) B2564095
theorem B2278367 : Blo 1012602 2278367 := bstep (se 1 (by rfl) ⟨1708775, by rfl⟩ : syracuseStep 2278367 = 3417551) B3417551
theorem B70371301 : Blo 1012602 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B5786963 : Blo 1012602 5786963 := bstep (se 1 (by rfl) ⟨4340222, by rfl⟩ : syracuseStep 5786963 = 8680445) B8680445
theorem B1518911 : Blo 1012602 1518911 := bstep (se 1 (by rfl) ⟨1139183, by rfl⟩ : syracuseStep 1518911 = 2278367) B2278367
theorem B93828401 : Blo 1012602 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B2279195 : Blo 1012602 2279195 := bstep (se 1 (by rfl) ⟨1709396, by rfl⟩ : syracuseStep 2279195 = 3418793) B3418793
theorem B3857975 : Blo 1012602 3857975 := bstep (se 1 (by rfl) ⟨2893481, by rfl⟩ : syracuseStep 3857975 = 5786963) B5786963
theorem B1519463 : Blo 1012602 1519463 := bstep (se 1 (by rfl) ⟨1139597, by rfl⟩ : syracuseStep 1519463 = 2279195) B2279195
theorem B2571983 : Blo 1012602 2571983 := bstep (se 1 (by rfl) ⟨1928987, by rfl⟩ : syracuseStep 2571983 = 3857975) B3857975
theorem B1012607 : Blo 1012602 1012607 := bstep (se 1 (by rfl) ⟨759455, by rfl⟩ : syracuseStep 1012607 = 1518911) B1518911
theorem B62552267 : Blo 1012602 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B1714655 : Blo 1012602 1714655 := bstep (se 1 (by rfl) ⟨1285991, by rfl⟩ : syracuseStep 1714655 = 2571983) B2571983
theorem B41701511 : Blo 1012602 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B1012975 : Blo 1012602 1012975 := bstep (se 1 (by rfl) ⟨759731, by rfl⟩ : syracuseStep 1012975 = 1519463) B1519463
theorem B111204029 : Blo 1012602 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B1143103 : Blo 1012602 1143103 := bstep (se 1 (by rfl) ⟨857327, by rfl⟩ : syracuseStep 1143103 = 1714655) B1714655
theorem B1524137 : Blo 1012602 1524137 := bstep (se 2 (by rfl) ⟨571551, by rfl⟩ : syracuseStep 1524137 = 1143103) B1143103
theorem B296544077 : Blo 1012602 296544077 := bstep (se 3 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 296544077 = 111204029) B111204029
theorem B1016091 : Blo 1012602 1016091 := bstep (se 1 (by rfl) ⟨762068, by rfl⟩ : syracuseStep 1016091 = 1524137) B1524137
theorem B197696051 : Blo 1012602 197696051 := bstep (se 1 (by rfl) ⟨148272038, by rfl⟩ : syracuseStep 197696051 = 296544077) B296544077
theorem B131797367 : Blo 1012602 131797367 := bstep (se 1 (by rfl) ⟨98848025, by rfl⟩ : syracuseStep 131797367 = 197696051) B197696051
theorem B87864911 : Blo 1012602 87864911 := bstep (se 1 (by rfl) ⟨65898683, by rfl⟩ : syracuseStep 87864911 = 131797367) B131797367
theorem B58576607 : Blo 1012602 58576607 := bstep (se 1 (by rfl) ⟨43932455, by rfl⟩ : syracuseStep 58576607 = 87864911) B87864911
theorem B39051071 : Blo 1012602 39051071 := bstep (se 1 (by rfl) ⟨29288303, by rfl⟩ : syracuseStep 39051071 = 58576607) B58576607
theorem B26034047 : Blo 1012602 26034047 := bstep (se 1 (by rfl) ⟨19525535, by rfl⟩ : syracuseStep 26034047 = 39051071) B39051071
theorem B17356031 : Blo 1012602 17356031 := bstep (se 1 (by rfl) ⟨13017023, by rfl⟩ : syracuseStep 17356031 = 26034047) B26034047
theorem B11570687 : Blo 1012602 11570687 := bstep (se 1 (by rfl) ⟨8678015, by rfl⟩ : syracuseStep 11570687 = 17356031) B17356031
theorem B7713791 : Blo 1012602 7713791 := bstep (se 1 (by rfl) ⟨5785343, by rfl⟩ : syracuseStep 7713791 = 11570687) B11570687
theorem B5142527 : Blo 1012602 5142527 := bstep (se 1 (by rfl) ⟨3856895, by rfl⟩ : syracuseStep 5142527 = 7713791) B7713791
theorem B3428351 : Blo 1012602 3428351 := bstep (se 1 (by rfl) ⟨2571263, by rfl⟩ : syracuseStep 3428351 = 5142527) B5142527
theorem B2285567 : Blo 1012602 2285567 := bstep (se 1 (by rfl) ⟨1714175, by rfl⟩ : syracuseStep 2285567 = 3428351) B3428351
theorem B1523711 : Blo 1012602 1523711 := bstep (se 1 (by rfl) ⟨1142783, by rfl⟩ : syracuseStep 1523711 = 2285567) B2285567
theorem B1015807 : Blo 1012602 1015807 := bstep (se 1 (by rfl) ⟨761855, by rfl⟩ : syracuseStep 1015807 = 1523711) B1523711

theorem C0 (j : ℕ) (h1 : 253150 ≤ j) (h2 : j ≤ 253849) : Blo 1012602 (4 * j + 3) := by
  interval_cases j
  · exact B1012603
  · exact B1012607
  · exact B1012611
  · exact B1012615
  · exact B1012619
  · exact B1012623
  · exact B1012627
  · exact B1012631
  · exact B1012635
  · exact B1012639
  · exact B1012643
  · exact B1012647
  · exact B1012651
  · exact B1012655
  · exact B1012659
  · exact B1012663
  · exact B1012667
  · exact B1012671
  · exact B1012675
  · exact B1012679
  · exact B1012683
  · exact B1012687
  · exact B1012691
  · exact B1012695
  · exact B1012699
  · exact B1012703
  · exact B1012707
  · exact B1012711
  · exact B1012715
  · exact B1012719
  · exact B1012723
  · exact B1012727
  · exact B1012731
  · exact B1012735
  · exact B1012739
  · exact B1012743
  · exact B1012747
  · exact B1012751
  · exact B1012755
  · exact B1012759
  · exact B1012763
  · exact B1012767
  · exact B1012771
  · exact B1012775
  · exact B1012779
  · exact B1012783
  · exact B1012787
  · exact B1012791
  · exact B1012795
  · exact B1012799
  · exact B1012803
  · exact B1012807
  · exact B1012811
  · exact B1012815
  · exact B1012819
  · exact B1012823
  · exact B1012827
  · exact B1012831
  · exact B1012835
  · exact B1012839
  · exact B1012843
  · exact B1012847
  · exact B1012851
  · exact B1012855
  · exact B1012859
  · exact B1012863
  · exact B1012867
  · exact B1012871
  · exact B1012875
  · exact B1012879
  · exact B1012883
  · exact B1012887
  · exact B1012891
  · exact B1012895
  · exact B1012899
  · exact B1012903
  · exact B1012907
  · exact B1012911
  · exact B1012915
  · exact B1012919
  · exact B1012923
  · exact B1012927
  · exact B1012931
  · exact B1012935
  · exact B1012939
  · exact B1012943
  · exact B1012947
  · exact B1012951
  · exact B1012955
  · exact B1012959
  · exact B1012963
  · exact B1012967
  · exact B1012971
  · exact B1012975
  · exact B1012979
  · exact B1012983
  · exact B1012987
  · exact B1012991
  · exact B1012995
  · exact B1012999
  · exact B1013003
  · exact B1013007
  · exact B1013011
  · exact B1013015
  · exact B1013019
  · exact B1013023
  · exact B1013027
  · exact B1013031
  · exact B1013035
  · exact B1013039
  · exact B1013043
  · exact B1013047
  · exact B1013051
  · exact B1013055
  · exact B1013059
  · exact B1013063
  · exact B1013067
  · exact B1013071
  · exact B1013075
  · exact B1013079
  · exact B1013083
  · exact B1013087
  · exact B1013091
  · exact B1013095
  · exact B1013099
  · exact B1013103
  · exact B1013107
  · exact B1013111
  · exact B1013115
  · exact B1013119
  · exact B1013123
  · exact B1013127
  · exact B1013131
  · exact B1013135
  · exact B1013139
  · exact B1013143
  · exact B1013147
  · exact B1013151
  · exact B1013155
  · exact B1013159
  · exact B1013163
  · exact B1013167
  · exact B1013171
  · exact B1013175
  · exact B1013179
  · exact B1013183
  · exact B1013187
  · exact B1013191
  · exact B1013195
  · exact B1013199
  · exact B1013203
  · exact B1013207
  · exact B1013211
  · exact B1013215
  · exact B1013219
  · exact B1013223
  · exact B1013227
  · exact B1013231
  · exact B1013235
  · exact B1013239
  · exact B1013243
  · exact B1013247
  · exact B1013251
  · exact B1013255
  · exact B1013259
  · exact B1013263
  · exact B1013267
  · exact B1013271
  · exact B1013275
  · exact B1013279
  · exact B1013283
  · exact B1013287
  · exact B1013291
  · exact B1013295
  · exact B1013299
  · exact B1013303
  · exact B1013307
  · exact B1013311
  · exact B1013315
  · exact B1013319
  · exact B1013323
  · exact B1013327
  · exact B1013331
  · exact B1013335
  · exact B1013339
  · exact B1013343
  · exact B1013347
  · exact B1013351
  · exact B1013355
  · exact B1013359
  · exact B1013363
  · exact B1013367
  · exact B1013371
  · exact B1013375
  · exact B1013379
  · exact B1013383
  · exact B1013387
  · exact B1013391
  · exact B1013395
  · exact B1013399
  · exact B1013403
  · exact B1013407
  · exact B1013411
  · exact B1013415
  · exact B1013419
  · exact B1013423
  · exact B1013427
  · exact B1013431
  · exact B1013435
  · exact B1013439
  · exact B1013443
  · exact B1013447
  · exact B1013451
  · exact B1013455
  · exact B1013459
  · exact B1013463
  · exact B1013467
  · exact B1013471
  · exact B1013475
  · exact B1013479
  · exact B1013483
  · exact B1013487
  · exact B1013491
  · exact B1013495
  · exact B1013499
  · exact B1013503
  · exact B1013507
  · exact B1013511
  · exact B1013515
  · exact B1013519
  · exact B1013523
  · exact B1013527
  · exact B1013531
  · exact B1013535
  · exact B1013539
  · exact B1013543
  · exact B1013547
  · exact B1013551
  · exact B1013555
  · exact B1013559
  · exact B1013563
  · exact B1013567
  · exact B1013571
  · exact B1013575
  · exact B1013579
  · exact B1013583
  · exact B1013587
  · exact B1013591
  · exact B1013595
  · exact B1013599
  · exact B1013603
  · exact B1013607
  · exact B1013611
  · exact B1013615
  · exact B1013619
  · exact B1013623
  · exact B1013627
  · exact B1013631
  · exact B1013635
  · exact B1013639
  · exact B1013643
  · exact B1013647
  · exact B1013651
  · exact B1013655
  · exact B1013659
  · exact B1013663
  · exact B1013667
  · exact B1013671
  · exact B1013675
  · exact B1013679
  · exact B1013683
  · exact B1013687
  · exact B1013691
  · exact B1013695
  · exact B1013699
  · exact B1013703
  · exact B1013707
  · exact B1013711
  · exact B1013715
  · exact B1013719
  · exact B1013723
  · exact B1013727
  · exact B1013731
  · exact B1013735
  · exact B1013739
  · exact B1013743
  · exact B1013747
  · exact B1013751
  · exact B1013755
  · exact B1013759
  · exact B1013763
  · exact B1013767
  · exact B1013771
  · exact B1013775
  · exact B1013779
  · exact B1013783
  · exact B1013787
  · exact B1013791
  · exact B1013795
  · exact B1013799
  · exact B1013803
  · exact B1013807
  · exact B1013811
  · exact B1013815
  · exact B1013819
  · exact B1013823
  · exact B1013827
  · exact B1013831
  · exact B1013835
  · exact B1013839
  · exact B1013843
  · exact B1013847
  · exact B1013851
  · exact B1013855
  · exact B1013859
  · exact B1013863
  · exact B1013867
  · exact B1013871
  · exact B1013875
  · exact B1013879
  · exact B1013883
  · exact B1013887
  · exact B1013891
  · exact B1013895
  · exact B1013899
  · exact B1013903
  · exact B1013907
  · exact B1013911
  · exact B1013915
  · exact B1013919
  · exact B1013923
  · exact B1013927
  · exact B1013931
  · exact B1013935
  · exact B1013939
  · exact B1013943
  · exact B1013947
  · exact B1013951
  · exact B1013955
  · exact B1013959
  · exact B1013963
  · exact B1013967
  · exact B1013971
  · exact B1013975
  · exact B1013979
  · exact B1013983
  · exact B1013987
  · exact B1013991
  · exact B1013995
  · exact B1013999
  · exact B1014003
  · exact B1014007
  · exact B1014011
  · exact B1014015
  · exact B1014019
  · exact B1014023
  · exact B1014027
  · exact B1014031
  · exact B1014035
  · exact B1014039
  · exact B1014043
  · exact B1014047
  · exact B1014051
  · exact B1014055
  · exact B1014059
  · exact B1014063
  · exact B1014067
  · exact B1014071
  · exact B1014075
  · exact B1014079
  · exact B1014083
  · exact B1014087
  · exact B1014091
  · exact B1014095
  · exact B1014099
  · exact B1014103
  · exact B1014107
  · exact B1014111
  · exact B1014115
  · exact B1014119
  · exact B1014123
  · exact B1014127
  · exact B1014131
  · exact B1014135
  · exact B1014139
  · exact B1014143
  · exact B1014147
  · exact B1014151
  · exact B1014155
  · exact B1014159
  · exact B1014163
  · exact B1014167
  · exact B1014171
  · exact B1014175
  · exact B1014179
  · exact B1014183
  · exact B1014187
  · exact B1014191
  · exact B1014195
  · exact B1014199
  · exact B1014203
  · exact B1014207
  · exact B1014211
  · exact B1014215
  · exact B1014219
  · exact B1014223
  · exact B1014227
  · exact B1014231
  · exact B1014235
  · exact B1014239
  · exact B1014243
  · exact B1014247
  · exact B1014251
  · exact B1014255
  · exact B1014259
  · exact B1014263
  · exact B1014267
  · exact B1014271
  · exact B1014275
  · exact B1014279
  · exact B1014283
  · exact B1014287
  · exact B1014291
  · exact B1014295
  · exact B1014299
  · exact B1014303
  · exact B1014307
  · exact B1014311
  · exact B1014315
  · exact B1014319
  · exact B1014323
  · exact B1014327
  · exact B1014331
  · exact B1014335
  · exact B1014339
  · exact B1014343
  · exact B1014347
  · exact B1014351
  · exact B1014355
  · exact B1014359
  · exact B1014363
  · exact B1014367
  · exact B1014371
  · exact B1014375
  · exact B1014379
  · exact B1014383
  · exact B1014387
  · exact B1014391
  · exact B1014395
  · exact B1014399
  · exact B1014403
  · exact B1014407
  · exact B1014411
  · exact B1014415
  · exact B1014419
  · exact B1014423
  · exact B1014427
  · exact B1014431
  · exact B1014435
  · exact B1014439
  · exact B1014443
  · exact B1014447
  · exact B1014451
  · exact B1014455
  · exact B1014459
  · exact B1014463
  · exact B1014467
  · exact B1014471
  · exact B1014475
  · exact B1014479
  · exact B1014483
  · exact B1014487
  · exact B1014491
  · exact B1014495
  · exact B1014499
  · exact B1014503
  · exact B1014507
  · exact B1014511
  · exact B1014515
  · exact B1014519
  · exact B1014523
  · exact B1014527
  · exact B1014531
  · exact B1014535
  · exact B1014539
  · exact B1014543
  · exact B1014547
  · exact B1014551
  · exact B1014555
  · exact B1014559
  · exact B1014563
  · exact B1014567
  · exact B1014571
  · exact B1014575
  · exact B1014579
  · exact B1014583
  · exact B1014587
  · exact B1014591
  · exact B1014595
  · exact B1014599
  · exact B1014603
  · exact B1014607
  · exact B1014611
  · exact B1014615
  · exact B1014619
  · exact B1014623
  · exact B1014627
  · exact B1014631
  · exact B1014635
  · exact B1014639
  · exact B1014643
  · exact B1014647
  · exact B1014651
  · exact B1014655
  · exact B1014659
  · exact B1014663
  · exact B1014667
  · exact B1014671
  · exact B1014675
  · exact B1014679
  · exact B1014683
  · exact B1014687
  · exact B1014691
  · exact B1014695
  · exact B1014699
  · exact B1014703
  · exact B1014707
  · exact B1014711
  · exact B1014715
  · exact B1014719
  · exact B1014723
  · exact B1014727
  · exact B1014731
  · exact B1014735
  · exact B1014739
  · exact B1014743
  · exact B1014747
  · exact B1014751
  · exact B1014755
  · exact B1014759
  · exact B1014763
  · exact B1014767
  · exact B1014771
  · exact B1014775
  · exact B1014779
  · exact B1014783
  · exact B1014787
  · exact B1014791
  · exact B1014795
  · exact B1014799
  · exact B1014803
  · exact B1014807
  · exact B1014811
  · exact B1014815
  · exact B1014819
  · exact B1014823
  · exact B1014827
  · exact B1014831
  · exact B1014835
  · exact B1014839
  · exact B1014843
  · exact B1014847
  · exact B1014851
  · exact B1014855
  · exact B1014859
  · exact B1014863
  · exact B1014867
  · exact B1014871
  · exact B1014875
  · exact B1014879
  · exact B1014883
  · exact B1014887
  · exact B1014891
  · exact B1014895
  · exact B1014899
  · exact B1014903
  · exact B1014907
  · exact B1014911
  · exact B1014915
  · exact B1014919
  · exact B1014923
  · exact B1014927
  · exact B1014931
  · exact B1014935
  · exact B1014939
  · exact B1014943
  · exact B1014947
  · exact B1014951
  · exact B1014955
  · exact B1014959
  · exact B1014963
  · exact B1014967
  · exact B1014971
  · exact B1014975
  · exact B1014979
  · exact B1014983
  · exact B1014987
  · exact B1014991
  · exact B1014995
  · exact B1014999
  · exact B1015003
  · exact B1015007
  · exact B1015011
  · exact B1015015
  · exact B1015019
  · exact B1015023
  · exact B1015027
  · exact B1015031
  · exact B1015035
  · exact B1015039
  · exact B1015043
  · exact B1015047
  · exact B1015051
  · exact B1015055
  · exact B1015059
  · exact B1015063
  · exact B1015067
  · exact B1015071
  · exact B1015075
  · exact B1015079
  · exact B1015083
  · exact B1015087
  · exact B1015091
  · exact B1015095
  · exact B1015099
  · exact B1015103
  · exact B1015107
  · exact B1015111
  · exact B1015115
  · exact B1015119
  · exact B1015123
  · exact B1015127
  · exact B1015131
  · exact B1015135
  · exact B1015139
  · exact B1015143
  · exact B1015147
  · exact B1015151
  · exact B1015155
  · exact B1015159
  · exact B1015163
  · exact B1015167
  · exact B1015171
  · exact B1015175
  · exact B1015179
  · exact B1015183
  · exact B1015187
  · exact B1015191
  · exact B1015195
  · exact B1015199
  · exact B1015203
  · exact B1015207
  · exact B1015211
  · exact B1015215
  · exact B1015219
  · exact B1015223
  · exact B1015227
  · exact B1015231
  · exact B1015235
  · exact B1015239
  · exact B1015243
  · exact B1015247
  · exact B1015251
  · exact B1015255
  · exact B1015259
  · exact B1015263
  · exact B1015267
  · exact B1015271
  · exact B1015275
  · exact B1015279
  · exact B1015283
  · exact B1015287
  · exact B1015291
  · exact B1015295
  · exact B1015299
  · exact B1015303
  · exact B1015307
  · exact B1015311
  · exact B1015315
  · exact B1015319
  · exact B1015323
  · exact B1015327
  · exact B1015331
  · exact B1015335
  · exact B1015339
  · exact B1015343
  · exact B1015347
  · exact B1015351
  · exact B1015355
  · exact B1015359
  · exact B1015363
  · exact B1015367
  · exact B1015371
  · exact B1015375
  · exact B1015379
  · exact B1015383
  · exact B1015387
  · exact B1015391
  · exact B1015395
  · exact B1015399

theorem C1 (j : ℕ) (h1 : 253850 ≤ j) (h2 : j ≤ 254149) : Blo 1012602 (4 * j + 3) := by
  interval_cases j
  · exact B1015403
  · exact B1015407
  · exact B1015411
  · exact B1015415
  · exact B1015419
  · exact B1015423
  · exact B1015427
  · exact B1015431
  · exact B1015435
  · exact B1015439
  · exact B1015443
  · exact B1015447
  · exact B1015451
  · exact B1015455
  · exact B1015459
  · exact B1015463
  · exact B1015467
  · exact B1015471
  · exact B1015475
  · exact B1015479
  · exact B1015483
  · exact B1015487
  · exact B1015491
  · exact B1015495
  · exact B1015499
  · exact B1015503
  · exact B1015507
  · exact B1015511
  · exact B1015515
  · exact B1015519
  · exact B1015523
  · exact B1015527
  · exact B1015531
  · exact B1015535
  · exact B1015539
  · exact B1015543
  · exact B1015547
  · exact B1015551
  · exact B1015555
  · exact B1015559
  · exact B1015563
  · exact B1015567
  · exact B1015571
  · exact B1015575
  · exact B1015579
  · exact B1015583
  · exact B1015587
  · exact B1015591
  · exact B1015595
  · exact B1015599
  · exact B1015603
  · exact B1015607
  · exact B1015611
  · exact B1015615
  · exact B1015619
  · exact B1015623
  · exact B1015627
  · exact B1015631
  · exact B1015635
  · exact B1015639
  · exact B1015643
  · exact B1015647
  · exact B1015651
  · exact B1015655
  · exact B1015659
  · exact B1015663
  · exact B1015667
  · exact B1015671
  · exact B1015675
  · exact B1015679
  · exact B1015683
  · exact B1015687
  · exact B1015691
  · exact B1015695
  · exact B1015699
  · exact B1015703
  · exact B1015707
  · exact B1015711
  · exact B1015715
  · exact B1015719
  · exact B1015723
  · exact B1015727
  · exact B1015731
  · exact B1015735
  · exact B1015739
  · exact B1015743
  · exact B1015747
  · exact B1015751
  · exact B1015755
  · exact B1015759
  · exact B1015763
  · exact B1015767
  · exact B1015771
  · exact B1015775
  · exact B1015779
  · exact B1015783
  · exact B1015787
  · exact B1015791
  · exact B1015795
  · exact B1015799
  · exact B1015803
  · exact B1015807
  · exact B1015811
  · exact B1015815
  · exact B1015819
  · exact B1015823
  · exact B1015827
  · exact B1015831
  · exact B1015835
  · exact B1015839
  · exact B1015843
  · exact B1015847
  · exact B1015851
  · exact B1015855
  · exact B1015859
  · exact B1015863
  · exact B1015867
  · exact B1015871
  · exact B1015875
  · exact B1015879
  · exact B1015883
  · exact B1015887
  · exact B1015891
  · exact B1015895
  · exact B1015899
  · exact B1015903
  · exact B1015907
  · exact B1015911
  · exact B1015915
  · exact B1015919
  · exact B1015923
  · exact B1015927
  · exact B1015931
  · exact B1015935
  · exact B1015939
  · exact B1015943
  · exact B1015947
  · exact B1015951
  · exact B1015955
  · exact B1015959
  · exact B1015963
  · exact B1015967
  · exact B1015971
  · exact B1015975
  · exact B1015979
  · exact B1015983
  · exact B1015987
  · exact B1015991
  · exact B1015995
  · exact B1015999
  · exact B1016003
  · exact B1016007
  · exact B1016011
  · exact B1016015
  · exact B1016019
  · exact B1016023
  · exact B1016027
  · exact B1016031
  · exact B1016035
  · exact B1016039
  · exact B1016043
  · exact B1016047
  · exact B1016051
  · exact B1016055
  · exact B1016059
  · exact B1016063
  · exact B1016067
  · exact B1016071
  · exact B1016075
  · exact B1016079
  · exact B1016083
  · exact B1016087
  · exact B1016091
  · exact B1016095
  · exact B1016099
  · exact B1016103
  · exact B1016107
  · exact B1016111
  · exact B1016115
  · exact B1016119
  · exact B1016123
  · exact B1016127
  · exact B1016131
  · exact B1016135
  · exact B1016139
  · exact B1016143
  · exact B1016147
  · exact B1016151
  · exact B1016155
  · exact B1016159
  · exact B1016163
  · exact B1016167
  · exact B1016171
  · exact B1016175
  · exact B1016179
  · exact B1016183
  · exact B1016187
  · exact B1016191
  · exact B1016195
  · exact B1016199
  · exact B1016203
  · exact B1016207
  · exact B1016211
  · exact B1016215
  · exact B1016219
  · exact B1016223
  · exact B1016227
  · exact B1016231
  · exact B1016235
  · exact B1016239
  · exact B1016243
  · exact B1016247
  · exact B1016251
  · exact B1016255
  · exact B1016259
  · exact B1016263
  · exact B1016267
  · exact B1016271
  · exact B1016275
  · exact B1016279
  · exact B1016283
  · exact B1016287
  · exact B1016291
  · exact B1016295
  · exact B1016299
  · exact B1016303
  · exact B1016307
  · exact B1016311
  · exact B1016315
  · exact B1016319
  · exact B1016323
  · exact B1016327
  · exact B1016331
  · exact B1016335
  · exact B1016339
  · exact B1016343
  · exact B1016347
  · exact B1016351
  · exact B1016355
  · exact B1016359
  · exact B1016363
  · exact B1016367
  · exact B1016371
  · exact B1016375
  · exact B1016379
  · exact B1016383
  · exact B1016387
  · exact B1016391
  · exact B1016395
  · exact B1016399
  · exact B1016403
  · exact B1016407
  · exact B1016411
  · exact B1016415
  · exact B1016419
  · exact B1016423
  · exact B1016427
  · exact B1016431
  · exact B1016435
  · exact B1016439
  · exact B1016443
  · exact B1016447
  · exact B1016451
  · exact B1016455
  · exact B1016459
  · exact B1016463
  · exact B1016467
  · exact B1016471
  · exact B1016475
  · exact B1016479
  · exact B1016483
  · exact B1016487
  · exact B1016491
  · exact B1016495
  · exact B1016499
  · exact B1016503
  · exact B1016507
  · exact B1016511
  · exact B1016515
  · exact B1016519
  · exact B1016523
  · exact B1016527
  · exact B1016531
  · exact B1016535
  · exact B1016539
  · exact B1016543
  · exact B1016547
  · exact B1016551
  · exact B1016555
  · exact B1016559
  · exact B1016563
  · exact B1016567
  · exact B1016571
  · exact B1016575
  · exact B1016579
  · exact B1016583
  · exact B1016587
  · exact B1016591
  · exact B1016595
  · exact B1016599

theorem solution (m : ℕ) (hlo : 1012602 ≤ m) (hhi : m ≤ 1016602) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 253150 ≤ j := by omega
    have hj2 : j ≤ 254149 := by omega
    have hb : Blo 1012602 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 253850 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
