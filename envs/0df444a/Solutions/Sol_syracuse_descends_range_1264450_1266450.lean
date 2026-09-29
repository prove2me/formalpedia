-- Prove2me | solution 1 for syracuse_descends_range_1264450_1266450
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:25.553053+00:00
-- url     : https://prove2.me/submissions/a393b75c-63d3-4981-a75b-0f2d1c3ba9be

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


theorem B1925141 : Blo 1264450 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B12165173 : Blo 1264450 12165173 := bbase (se 5 (by rfl) ⟨570242, by rfl⟩ : syracuseStep 12165173 = 1140485) (by norm_num)
theorem B1351733 : Blo 1264450 1351733 := bbase (se 5 (by rfl) ⟨63362, by rfl⟩ : syracuseStep 1351733 = 126725) (by norm_num)
theorem B3203165 : Blo 1264450 3203165 := bbase (se 3 (by rfl) ⟨600593, by rfl⟩ : syracuseStep 3203165 = 1201187) (by norm_num)
theorem B1925221 : Blo 1264450 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B16425109 : Blo 1264450 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B6160549 : Blo 1264450 6160549 := bbase (se 4 (by rfl) ⟨577551, by rfl⟩ : syracuseStep 6160549 = 1155103) (by norm_num)
theorem B4268213 : Blo 1264450 4268213 := bbase (se 5 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 4268213 = 400145) (by norm_num)
theorem B10813621 : Blo 1264450 10813621 := bbase (se 5 (by rfl) ⟨506888, by rfl⟩ : syracuseStep 10813621 = 1013777) (by norm_num)
theorem B13156597 : Blo 1264450 13156597 := bbase (se 5 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 13156597 = 1233431) (by norm_num)
theorem B2883845 : Blo 1264450 2883845 := bbase (se 4 (by rfl) ⟨270360, by rfl⟩ : syracuseStep 2883845 = 540721) (by norm_num)
theorem B2564365 : Blo 1264450 2564365 := bbase (se 3 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 2564365 = 961637) (by norm_num)
theorem B1442113 : Blo 1264450 1442113 := bbase (se 2 (by rfl) ⟨540792, by rfl⟩ : syracuseStep 1442113 = 1081585) (by norm_num)
theorem B2883917 : Blo 1264450 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B3604837 : Blo 1264450 3604837 := bbase (se 4 (by rfl) ⟨337953, by rfl⟩ : syracuseStep 3604837 = 675907) (by norm_num)
theorem B3203509 : Blo 1264450 3203509 := bbase (se 5 (by rfl) ⟨150164, by rfl⟩ : syracuseStep 3203509 = 300329) (by norm_num)
theorem B6406613 : Blo 1264450 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B2400749 : Blo 1264450 2400749 := bbase (se 3 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 2400749 = 900281) (by norm_num)
theorem B1802749 : Blo 1264450 1802749 := bbase (se 3 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 1802749 = 676031) (by norm_num)
theorem B25960981 : Blo 1264450 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B3203621 : Blo 1264450 3203621 := bbase (se 4 (by rfl) ⟨300339, by rfl⟩ : syracuseStep 3203621 = 600679) (by norm_num)
theorem B2163245 : Blo 1264450 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B4268645 : Blo 1264450 4268645 := bbase (se 4 (by rfl) ⟨400185, by rfl⟩ : syracuseStep 4268645 = 800371) (by norm_num)
theorem B2704013 : Blo 1264450 2704013 := bbase (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) (by norm_num)
theorem B3203813 : Blo 1264450 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B4801301 : Blo 1264450 4801301 := bbase (se 6 (by rfl) ⟨112530, by rfl⟩ : syracuseStep 4801301 = 225061) (by norm_num)
theorem B2564885 : Blo 1264450 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B4883237 : Blo 1264450 4883237 := bbase (se 4 (by rfl) ⟨457803, by rfl⟩ : syracuseStep 4883237 = 915607) (by norm_num)
theorem B4269077 : Blo 1264450 4269077 := bbase (se 6 (by rfl) ⟨100056, by rfl⟩ : syracuseStep 4269077 = 200113) (by norm_num)
theorem B4563989 : Blo 1264450 4563989 := bbase (se 6 (by rfl) ⟨106968, by rfl⟩ : syracuseStep 4563989 = 213937) (by norm_num)
theorem B4801589 : Blo 1264450 4801589 := bbase (se 5 (by rfl) ⟨225074, by rfl⟩ : syracuseStep 4801589 = 450149) (by norm_num)
theorem B3204157 : Blo 1264450 3204157 := bbase (se 3 (by rfl) ⟨600779, by rfl⟩ : syracuseStep 3204157 = 1201559) (by norm_num)
theorem B2311237 : Blo 1264450 2311237 := bbase (se 4 (by rfl) ⟨216678, by rfl⟩ : syracuseStep 2311237 = 433357) (by norm_num)
theorem B54731861 : Blo 1264450 54731861 := bbase (se 8 (by rfl) ⟨320694, by rfl⟩ : syracuseStep 54731861 = 641389) (by norm_num)
theorem B3245197 : Blo 1264450 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B4564133 : Blo 1264450 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B3204269 : Blo 1264450 3204269 := bbase (se 3 (by rfl) ⟨600800, by rfl⟩ : syracuseStep 3204269 = 1201601) (by norm_num)
theorem B7201973 : Blo 1264450 7201973 := bbase (se 5 (by rfl) ⟨337592, by rfl⟩ : syracuseStep 7201973 = 675185) (by norm_num)
theorem B2401501 : Blo 1264450 2401501 := bbase (se 3 (by rfl) ⟨450281, by rfl⟩ : syracuseStep 2401501 = 900563) (by norm_num)
theorem B10257749 : Blo 1264450 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B2401645 : Blo 1264450 2401645 := bbase (se 3 (by rfl) ⟨450308, by rfl⟩ : syracuseStep 2401645 = 900617) (by norm_num)
theorem B3204461 : Blo 1264450 3204461 := bbase (se 3 (by rfl) ⟨600836, by rfl⟩ : syracuseStep 3204461 = 1201673) (by norm_num)
theorem B2704765 : Blo 1264450 2704765 := bbase (se 3 (by rfl) ⟨507143, by rfl⟩ : syracuseStep 2704765 = 1014287) (by norm_num)
theorem B20514197 : Blo 1264450 20514197 := bbase (se 6 (by rfl) ⟨480801, by rfl⟩ : syracuseStep 20514197 = 961603) (by norm_num)
theorem B4269509 : Blo 1264450 4269509 := bbase (se 4 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 4269509 = 800533) (by norm_num)
theorem B3900869 : Blo 1264450 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B1541605 : Blo 1264450 1541605 := bbase (se 4 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 1541605 = 289051) (by norm_num)
theorem B2401805 : Blo 1264450 2401805 := bbase (se 3 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 2401805 = 900677) (by norm_num)
theorem B1443481 : Blo 1264450 1443481 := bbase (se 2 (by rfl) ⟨541305, by rfl⟩ : syracuseStep 1443481 = 1082611) (by norm_num)
theorem B2401949 : Blo 1264450 2401949 := bbase (se 3 (by rfl) ⟨450365, by rfl⟩ : syracuseStep 2401949 = 900731) (by norm_num)
theorem B1369765 : Blo 1264450 1369765 := bbase (se 4 (by rfl) ⟨128415, by rfl⟩ : syracuseStep 1369765 = 256831) (by norm_num)
theorem B3204805 : Blo 1264450 3204805 := bbase (se 4 (by rfl) ⟨300450, by rfl⟩ : syracuseStep 3204805 = 600901) (by norm_num)
theorem B2164429 : Blo 1264450 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B2279125 : Blo 1264450 2279125 := bbase (se 7 (by rfl) ⟨26708, by rfl⟩ : syracuseStep 2279125 = 53417) (by norm_num)
theorem B6407909 : Blo 1264450 6407909 := bbase (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) (by norm_num)
theorem B3204917 : Blo 1264450 3204917 := bbase (se 5 (by rfl) ⟨150230, by rfl⟩ : syracuseStep 3204917 = 300461) (by norm_num)
theorem B3041101 : Blo 1264450 3041101 := bbase (se 3 (by rfl) ⟨570206, by rfl⟩ : syracuseStep 3041101 = 1140413) (by norm_num)
theorem B2279269 : Blo 1264450 2279269 := bbase (se 4 (by rfl) ⟨213681, by rfl⟩ : syracuseStep 2279269 = 427363) (by norm_num)
theorem B4269941 : Blo 1264450 4269941 := bbase (se 5 (by rfl) ⟨200153, by rfl⟩ : syracuseStep 4269941 = 400307) (by norm_num)
theorem B3082117 : Blo 1264450 3082117 := bbase (se 4 (by rfl) ⟨288948, by rfl⟩ : syracuseStep 3082117 = 577897) (by norm_num)
theorem B2402237 : Blo 1264450 2402237 := bbase (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) (by norm_num)
theorem B2779085 : Blo 1264450 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B2926573 : Blo 1264450 2926573 := bbase (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) (by norm_num)
theorem B3205109 : Blo 1264450 3205109 := bbase (se 5 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 3205109 = 300479) (by norm_num)
theorem B5769253 : Blo 1264450 5769253 := bbase (se 4 (by rfl) ⟨540867, by rfl⟩ : syracuseStep 5769253 = 1081735) (by norm_num)
theorem B1370189 : Blo 1264450 1370189 := bbase (se 3 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 1370189 = 513821) (by norm_num)
theorem B2402389 : Blo 1264450 2402389 := bbase (se 8 (by rfl) ⟨14076, by rfl⟩ : syracuseStep 2402389 = 28153) (by norm_num)
theorem B10815605 : Blo 1264450 10815605 := bbase (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) (by norm_num)
theorem B4802773 : Blo 1264450 4802773 := bbase (se 7 (by rfl) ⟨56282, by rfl⟩ : syracuseStep 4802773 = 112565) (by norm_num)
theorem B1444061 : Blo 1264450 1444061 := bbase (se 3 (by rfl) ⟨270761, by rfl⟩ : syracuseStep 1444061 = 541523) (by norm_num)
theorem B6080741 : Blo 1264450 6080741 := bbase (se 4 (by rfl) ⟨570069, by rfl⟩ : syracuseStep 6080741 = 1140139) (by norm_num)
theorem B3041525 : Blo 1264450 3041525 := bbase (se 5 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 3041525 = 285143) (by norm_num)
theorem B4270373 : Blo 1264450 4270373 := bbase (se 4 (by rfl) ⟨400347, by rfl⟩ : syracuseStep 4270373 = 800695) (by norm_num)
theorem B3205453 : Blo 1264450 3205453 := bbase (se 3 (by rfl) ⟨601022, by rfl⟩ : syracuseStep 3205453 = 1202045) (by norm_num)
theorem B116877653 : Blo 1264450 116877653 := bbase (se 10 (by rfl) ⟨171207, by rfl⟩ : syracuseStep 116877653 = 342415) (by norm_num)
theorem B2886013 : Blo 1264450 2886013 := bbase (se 3 (by rfl) ⟨541127, by rfl⟩ : syracuseStep 2886013 = 1082255) (by norm_num)
theorem B2845061 : Blo 1264450 2845061 := bbase (se 4 (by rfl) ⟨266724, by rfl⟩ : syracuseStep 2845061 = 533449) (by norm_num)
theorem B2402693 : Blo 1264450 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B22219157 : Blo 1264450 22219157 := bbase (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) (by norm_num)
theorem B2279845 : Blo 1264450 2279845 := bbase (se 4 (by rfl) ⟨213735, by rfl⟩ : syracuseStep 2279845 = 427471) (by norm_num)
theorem B3205565 : Blo 1264450 3205565 := bbase (se 3 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 3205565 = 1202087) (by norm_num)
theorem B4106693 : Blo 1264450 4106693 := bbase (se 4 (by rfl) ⟨385002, by rfl⟩ : syracuseStep 4106693 = 770005) (by norm_num)
theorem B2845133 : Blo 1264450 2845133 := bbase (se 3 (by rfl) ⟨533462, by rfl⟩ : syracuseStep 2845133 = 1066925) (by norm_num)
theorem B4327925 : Blo 1264450 4327925 := bbase (se 5 (by rfl) ⟨202871, by rfl⟩ : syracuseStep 4327925 = 405743) (by norm_num)
theorem B4803077 : Blo 1264450 4803077 := bbase (se 4 (by rfl) ⟨450288, by rfl⟩ : syracuseStep 4803077 = 900577) (by norm_num)
theorem B2845205 : Blo 1264450 2845205 := bbase (se 6 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 2845205 = 133369) (by norm_num)
theorem B2599445 : Blo 1264450 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B3041813 : Blo 1264450 3041813 := bbase (se 6 (by rfl) ⟨71292, by rfl⟩ : syracuseStep 3041813 = 142585) (by norm_num)
theorem B5130805 : Blo 1264450 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B2845277 : Blo 1264450 2845277 := bbase (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) (by norm_num)
theorem B2845349 : Blo 1264450 2845349 := bbase (se 4 (by rfl) ⟨266751, by rfl⟩ : syracuseStep 2845349 = 533503) (by norm_num)
theorem B6163157 : Blo 1264450 6163157 := bbase (se 7 (by rfl) ⟨72224, by rfl⟩ : syracuseStep 6163157 = 144449) (by norm_num)
theorem B4270805 : Blo 1264450 4270805 := bbase (se 7 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 4270805 = 100097) (by norm_num)
theorem B2845421 : Blo 1264450 2845421 := bbase (se 3 (by rfl) ⟨533516, by rfl⟩ : syracuseStep 2845421 = 1067033) (by norm_num)
theorem B2845493 : Blo 1264450 2845493 := bbase (se 5 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 2845493 = 266765) (by norm_num)
theorem B3418949 : Blo 1264450 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B1600337 : Blo 1264450 1600337 := bbase (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) (by norm_num)
theorem B7211861 : Blo 1264450 7211861 := bbase (se 9 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 7211861 = 42257) (by norm_num)
theorem B2845565 : Blo 1264450 2845565 := bbase (se 3 (by rfl) ⟨533543, by rfl⟩ : syracuseStep 2845565 = 1067087) (by norm_num)
theorem B1600393 : Blo 1264450 1600393 := bbase (se 2 (by rfl) ⟨600147, by rfl⟩ : syracuseStep 1600393 = 1200295) (by norm_num)
theorem B2083733 : Blo 1264450 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B2845637 : Blo 1264450 2845637 := bbase (se 4 (by rfl) ⟨266778, by rfl⟩ : syracuseStep 2845637 = 533557) (by norm_num)
theorem B2026453 : Blo 1264450 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B1600489 : Blo 1264450 1600489 := bbase (se 2 (by rfl) ⟨600183, by rfl⟩ : syracuseStep 1600489 = 1200367) (by norm_num)
theorem B6409205 : Blo 1264450 6409205 := bbase (se 5 (by rfl) ⟨300431, by rfl⟩ : syracuseStep 6409205 = 600863) (by norm_num)
theorem B2845709 : Blo 1264450 2845709 := bbase (se 3 (by rfl) ⟨533570, by rfl⟩ : syracuseStep 2845709 = 1067141) (by norm_num)
theorem B2845781 : Blo 1264450 2845781 := bbase (se 8 (by rfl) ⟨16674, by rfl⟩ : syracuseStep 2845781 = 33349) (by norm_num)
theorem B14421077 : Blo 1264450 14421077 := bbase (se 8 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 14421077 = 168997) (by norm_num)
theorem B2403445 : Blo 1264450 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B4271237 : Blo 1264450 4271237 := bbase (se 4 (by rfl) ⟨400428, by rfl⟩ : syracuseStep 4271237 = 800857) (by norm_num)
theorem B1600661 : Blo 1264450 1600661 := bbase (se 6 (by rfl) ⟨37515, by rfl⟩ : syracuseStep 1600661 = 75031) (by norm_num)
theorem B2845853 : Blo 1264450 2845853 := bbase (se 3 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 2845853 = 1067195) (by norm_num)
theorem B1600717 : Blo 1264450 1600717 := bbase (se 3 (by rfl) ⟨300134, by rfl⟩ : syracuseStep 1600717 = 600269) (by norm_num)
theorem B2280653 : Blo 1264450 2280653 := bbase (se 3 (by rfl) ⟨427622, by rfl⟩ : syracuseStep 2280653 = 855245) (by norm_num)
theorem B2026709 : Blo 1264450 2026709 := bbase (se 7 (by rfl) ⟨23750, by rfl⟩ : syracuseStep 2026709 = 47501) (by norm_num)
theorem B2845925 : Blo 1264450 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B2403589 : Blo 1264450 2403589 := bbase (se 4 (by rfl) ⟨225336, by rfl⟩ : syracuseStep 2403589 = 450673) (by norm_num)
theorem B1600813 : Blo 1264450 1600813 := bbase (se 3 (by rfl) ⟨300152, by rfl⟩ : syracuseStep 1600813 = 600305) (by norm_num)
theorem B2845997 : Blo 1264450 2845997 := bbase (se 3 (by rfl) ⟨533624, by rfl⟩ : syracuseStep 2845997 = 1067249) (by norm_num)
theorem B2846069 : Blo 1264450 2846069 := bbase (se 5 (by rfl) ⟨133409, by rfl⟩ : syracuseStep 2846069 = 266819) (by norm_num)
theorem B3419509 : Blo 1264450 3419509 := bbase (se 5 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 3419509 = 320579) (by norm_num)
theorem B2436493 : Blo 1264450 2436493 := bbase (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) (by norm_num)
theorem B6401429 : Blo 1264450 6401429 := bbase (se 6 (by rfl) ⟨150033, by rfl⟩ : syracuseStep 6401429 = 300067) (by norm_num)
theorem B9498005 : Blo 1264450 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B2026901 : Blo 1264450 2026901 := bbase (se 6 (by rfl) ⟨47505, by rfl⟩ : syracuseStep 2026901 = 95011) (by norm_num)
theorem B2403749 : Blo 1264450 2403749 := bbase (se 4 (by rfl) ⟨225351, by rfl⟩ : syracuseStep 2403749 = 450703) (by norm_num)
theorem B2846141 : Blo 1264450 2846141 := bbase (se 3 (by rfl) ⟨533651, by rfl⟩ : syracuseStep 2846141 = 1067303) (by norm_num)
theorem B1600985 : Blo 1264450 1600985 := bbase (se 2 (by rfl) ⟨600369, by rfl⟩ : syracuseStep 1600985 = 1200739) (by norm_num)
theorem B2846213 : Blo 1264450 2846213 := bbase (se 4 (by rfl) ⟨266832, by rfl⟩ : syracuseStep 2846213 = 533665) (by norm_num)
theorem B1601041 : Blo 1264450 1601041 := bbase (se 2 (by rfl) ⟨600390, by rfl⟩ : syracuseStep 1601041 = 1200781) (by norm_num)
theorem B3247661 : Blo 1264450 3247661 := bbase (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) (by norm_num)
theorem B4271669 : Blo 1264450 4271669 := bbase (se 5 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 4271669 = 400469) (by norm_num)
theorem B2403893 : Blo 1264450 2403893 := bbase (se 5 (by rfl) ⟨112682, by rfl⟩ : syracuseStep 2403893 = 225365) (by norm_num)
theorem B1519177 : Blo 1264450 1519177 := bbase (se 2 (by rfl) ⟨569691, by rfl⟩ : syracuseStep 1519177 = 1139383) (by norm_num)
theorem B2846285 : Blo 1264450 2846285 := bbase (se 3 (by rfl) ⟨533678, by rfl⟩ : syracuseStep 2846285 = 1067357) (by norm_num)
theorem B1601137 : Blo 1264450 1601137 := bbase (se 2 (by rfl) ⟨600426, by rfl⟩ : syracuseStep 1601137 = 1200853) (by norm_num)
theorem B2846357 : Blo 1264450 2846357 := bbase (se 6 (by rfl) ⟨66711, by rfl⟩ : syracuseStep 2846357 = 133423) (by norm_num)
theorem B1281749 : Blo 1264450 1281749 := bbase (se 7 (by rfl) ⟨15020, by rfl⟩ : syracuseStep 1281749 = 30041) (by norm_num)
theorem B46157525 : Blo 1264450 46157525 := bbase (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) (by norm_num)
theorem B7302869 : Blo 1264450 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B2846429 : Blo 1264450 2846429 := bbase (se 3 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 2846429 = 1067411) (by norm_num)
theorem B1601309 : Blo 1264450 1601309 := bbase (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) (by norm_num)
theorem B1519393 : Blo 1264450 1519393 := bbase (se 2 (by rfl) ⟨569772, by rfl⟩ : syracuseStep 1519393 = 1139545) (by norm_num)
theorem B2846501 : Blo 1264450 2846501 := bbase (se 4 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 2846501 = 533719) (by norm_num)
theorem B1601365 : Blo 1264450 1601365 := bbase (se 9 (by rfl) ⟨4691, by rfl⟩ : syracuseStep 1601365 = 9383) (by norm_num)
theorem B2404181 : Blo 1264450 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B2846573 : Blo 1264450 2846573 := bbase (se 3 (by rfl) ⟨533732, by rfl⟩ : syracuseStep 2846573 = 1067465) (by norm_num)
theorem B2133877 : Blo 1264450 2133877 := bbase (se 5 (by rfl) ⟨100025, by rfl⟩ : syracuseStep 2133877 = 200051) (by norm_num)
theorem B2846645 : Blo 1264450 2846645 := bbase (se 5 (by rfl) ⟨133436, by rfl⟩ : syracuseStep 2846645 = 266873) (by norm_num)
theorem B1601461 : Blo 1264450 1601461 := bbase (se 5 (by rfl) ⟨75068, by rfl⟩ : syracuseStep 1601461 = 150137) (by norm_num)
theorem B1519561 : Blo 1264450 1519561 := bbase (se 2 (by rfl) ⟨569835, by rfl⟩ : syracuseStep 1519561 = 1139671) (by norm_num)
theorem B2133965 : Blo 1264450 2133965 := bbase (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) (by norm_num)
theorem B4272101 : Blo 1264450 4272101 := bbase (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) (by norm_num)
theorem B8114165 : Blo 1264450 8114165 := bbase (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) (by norm_num)
theorem B2846717 : Blo 1264450 2846717 := bbase (se 3 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 2846717 = 1067519) (by norm_num)
theorem B2846789 : Blo 1264450 2846789 := bbase (se 4 (by rfl) ⟨266886, by rfl⟩ : syracuseStep 2846789 = 533773) (by norm_num)
theorem B2134093 : Blo 1264450 2134093 := bbase (se 3 (by rfl) ⟨400142, by rfl⟩ : syracuseStep 2134093 = 800285) (by norm_num)
theorem B1601633 : Blo 1264450 1601633 := bbase (se 2 (by rfl) ⟨600612, by rfl⟩ : syracuseStep 1601633 = 1201225) (by norm_num)
theorem B2846861 : Blo 1264450 2846861 := bbase (se 3 (by rfl) ⟨533786, by rfl⟩ : syracuseStep 2846861 = 1067573) (by norm_num)
theorem B1601689 : Blo 1264450 1601689 := bbase (se 2 (by rfl) ⟨600633, by rfl⟩ : syracuseStep 1601689 = 1201267) (by norm_num)
theorem B2134181 : Blo 1264450 2134181 := bbase (se 4 (by rfl) ⟨200079, by rfl⟩ : syracuseStep 2134181 = 400159) (by norm_num)
theorem B2846933 : Blo 1264450 2846933 := bbase (se 7 (by rfl) ⟨33362, by rfl⟩ : syracuseStep 2846933 = 66725) (by norm_num)
theorem B1896677 : Blo 1264450 1896677 := bbase (se 4 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 1896677 = 355627) (by norm_num)
theorem B1601785 : Blo 1264450 1601785 := bbase (se 2 (by rfl) ⟨600669, by rfl⟩ : syracuseStep 1601785 = 1201339) (by norm_num)
theorem B1896701 : Blo 1264450 1896701 := bbase (se 3 (by rfl) ⟨355631, by rfl⟩ : syracuseStep 1896701 = 711263) (by norm_num)
theorem B6410501 : Blo 1264450 6410501 := bbase (se 4 (by rfl) ⟨600984, by rfl⟩ : syracuseStep 6410501 = 1201969) (by norm_num)
theorem B1896725 : Blo 1264450 1896725 := bbase (se 6 (by rfl) ⟨44454, by rfl⟩ : syracuseStep 1896725 = 88909) (by norm_num)
theorem B16224533 : Blo 1264450 16224533 := bbase (se 6 (by rfl) ⟨380262, by rfl⟩ : syracuseStep 16224533 = 760525) (by norm_num)
theorem B2847005 : Blo 1264450 2847005 := bbase (se 3 (by rfl) ⟨533813, by rfl⟩ : syracuseStep 2847005 = 1067627) (by norm_num)
theorem B2134309 : Blo 1264450 2134309 := bbase (se 4 (by rfl) ⟨200091, by rfl⟩ : syracuseStep 2134309 = 400183) (by norm_num)
theorem B1896749 : Blo 1264450 1896749 := bbase (se 3 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 1896749 = 711281) (by norm_num)
theorem B2601269 : Blo 1264450 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B2027837 : Blo 1264450 2027837 := bbase (se 3 (by rfl) ⟨380219, by rfl⟩ : syracuseStep 2027837 = 760439) (by norm_num)
theorem B1896773 : Blo 1264450 1896773 := bbase (se 4 (by rfl) ⟨177822, by rfl⟩ : syracuseStep 1896773 = 355645) (by norm_num)
theorem B1896797 : Blo 1264450 1896797 := bbase (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) (by norm_num)
theorem B1282397 : Blo 1264450 1282397 := bbase (se 3 (by rfl) ⟨240449, by rfl⟩ : syracuseStep 1282397 = 480899) (by norm_num)
theorem B2847077 : Blo 1264450 2847077 := bbase (se 4 (by rfl) ⟨266913, by rfl⟩ : syracuseStep 2847077 = 533827) (by norm_num)
theorem B1896821 : Blo 1264450 1896821 := bbase (se 5 (by rfl) ⟨88913, by rfl⟩ : syracuseStep 1896821 = 177827) (by norm_num)
theorem B2134397 : Blo 1264450 2134397 := bbase (se 3 (by rfl) ⟨400199, by rfl⟩ : syracuseStep 2134397 = 800399) (by norm_num)
theorem B1896845 : Blo 1264450 1896845 := bbase (se 3 (by rfl) ⟨355658, by rfl⟩ : syracuseStep 1896845 = 711317) (by norm_num)
theorem B4272533 : Blo 1264450 4272533 := bbase (se 6 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 4272533 = 200275) (by norm_num)
theorem B1896869 : Blo 1264450 1896869 := bbase (se 4 (by rfl) ⟨177831, by rfl⟩ : syracuseStep 1896869 = 355663) (by norm_num)
theorem B1601957 : Blo 1264450 1601957 := bbase (se 4 (by rfl) ⟨150183, by rfl⟩ : syracuseStep 1601957 = 300367) (by norm_num)
theorem B2847149 : Blo 1264450 2847149 := bbase (se 3 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 2847149 = 1067681) (by norm_num)
theorem B1896893 : Blo 1264450 1896893 := bbase (se 3 (by rfl) ⟨355667, by rfl⟩ : syracuseStep 1896893 = 711335) (by norm_num)
theorem B1896917 : Blo 1264450 1896917 := bbase (se 7 (by rfl) ⟨22229, by rfl⟩ : syracuseStep 1896917 = 44459) (by norm_num)
theorem B1520089 : Blo 1264450 1520089 := bbase (se 2 (by rfl) ⟨570033, by rfl⟩ : syracuseStep 1520089 = 1140067) (by norm_num)
theorem B1602013 : Blo 1264450 1602013 := bbase (se 3 (by rfl) ⟨300377, by rfl⟩ : syracuseStep 1602013 = 600755) (by norm_num)
theorem B1896941 : Blo 1264450 1896941 := bbase (se 3 (by rfl) ⟨355676, by rfl⟩ : syracuseStep 1896941 = 711353) (by norm_num)
theorem B2847221 : Blo 1264450 2847221 := bbase (se 5 (by rfl) ⟨133463, by rfl⟩ : syracuseStep 2847221 = 266927) (by norm_num)
theorem B2134525 : Blo 1264450 2134525 := bbase (se 3 (by rfl) ⟨400223, by rfl⟩ : syracuseStep 2134525 = 800447) (by norm_num)
theorem B1896965 : Blo 1264450 1896965 := bbase (se 4 (by rfl) ⟨177840, by rfl⟩ : syracuseStep 1896965 = 355681) (by norm_num)
theorem B1896989 : Blo 1264450 1896989 := bbase (se 3 (by rfl) ⟨355685, by rfl⟩ : syracuseStep 1896989 = 711371) (by norm_num)
theorem B1897013 : Blo 1264450 1897013 := bbase (se 5 (by rfl) ⟨88922, by rfl⟩ : syracuseStep 1897013 = 177845) (by norm_num)
theorem B2847293 : Blo 1264450 2847293 := bbase (se 3 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 2847293 = 1067735) (by norm_num)
theorem B1602109 : Blo 1264450 1602109 := bbase (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) (by norm_num)
theorem B4805189 : Blo 1264450 4805189 := bbase (se 4 (by rfl) ⟨450486, by rfl⟩ : syracuseStep 4805189 = 900973) (by norm_num)
theorem B1897037 : Blo 1264450 1897037 := bbase (se 3 (by rfl) ⟨355694, by rfl⟩ : syracuseStep 1897037 = 711389) (by norm_num)
theorem B2134613 : Blo 1264450 2134613 := bbase (se 8 (by rfl) ⟨12507, by rfl⟩ : syracuseStep 2134613 = 25015) (by norm_num)
theorem B1897061 : Blo 1264450 1897061 := bbase (se 4 (by rfl) ⟨177849, by rfl⟩ : syracuseStep 1897061 = 355699) (by norm_num)
theorem B1897085 : Blo 1264450 1897085 := bbase (se 3 (by rfl) ⟨355703, by rfl⟩ : syracuseStep 1897085 = 711407) (by norm_num)
theorem B2847365 : Blo 1264450 2847365 := bbase (se 4 (by rfl) ⟨266940, by rfl⟩ : syracuseStep 2847365 = 533881) (by norm_num)
theorem B1897109 : Blo 1264450 1897109 := bbase (se 6 (by rfl) ⟨44463, by rfl⟩ : syracuseStep 1897109 = 88927) (by norm_num)
theorem B6402725 : Blo 1264450 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B1897133 : Blo 1264450 1897133 := bbase (se 3 (by rfl) ⟨355712, by rfl⟩ : syracuseStep 1897133 = 711425) (by norm_num)
theorem B2028221 : Blo 1264450 2028221 := bbase (se 3 (by rfl) ⟨380291, by rfl⟩ : syracuseStep 2028221 = 760583) (by norm_num)
theorem B1897157 : Blo 1264450 1897157 := bbase (se 4 (by rfl) ⟨177858, by rfl⟩ : syracuseStep 1897157 = 355717) (by norm_num)
theorem B2847437 : Blo 1264450 2847437 := bbase (se 3 (by rfl) ⟨533894, by rfl⟩ : syracuseStep 2847437 = 1067789) (by norm_num)
theorem B2134741 : Blo 1264450 2134741 := bbase (se 7 (by rfl) ⟨25016, by rfl⟩ : syracuseStep 2134741 = 50033) (by norm_num)
theorem B1897181 : Blo 1264450 1897181 := bbase (se 3 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 1897181 = 711443) (by norm_num)
theorem B1602281 : Blo 1264450 1602281 := bbase (se 2 (by rfl) ⟨600855, by rfl⟩ : syracuseStep 1602281 = 1201711) (by norm_num)
theorem B1897205 : Blo 1264450 1897205 := bbase (se 5 (by rfl) ⟨88931, by rfl⟩ : syracuseStep 1897205 = 177863) (by norm_num)
theorem B3420917 : Blo 1264450 3420917 := bbase (se 5 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 3420917 = 320711) (by norm_num)
theorem B1897229 : Blo 1264450 1897229 := bbase (se 3 (by rfl) ⟨355730, by rfl⟩ : syracuseStep 1897229 = 711461) (by norm_num)
theorem B2847509 : Blo 1264450 2847509 := bbase (se 6 (by rfl) ⟨66738, by rfl⟩ : syracuseStep 2847509 = 133477) (by norm_num)
theorem B1602337 : Blo 1264450 1602337 := bbase (se 2 (by rfl) ⟨600876, by rfl⟩ : syracuseStep 1602337 = 1201753) (by norm_num)
theorem B1897253 : Blo 1264450 1897253 := bbase (se 4 (by rfl) ⟨177867, by rfl⟩ : syracuseStep 1897253 = 355735) (by norm_num)
theorem B2134829 : Blo 1264450 2134829 := bbase (se 3 (by rfl) ⟨400280, by rfl⟩ : syracuseStep 2134829 = 800561) (by norm_num)
theorem B1897277 : Blo 1264450 1897277 := bbase (se 3 (by rfl) ⟨355739, by rfl⟩ : syracuseStep 1897277 = 711479) (by norm_num)
theorem B2028349 : Blo 1264450 2028349 := bbase (se 3 (by rfl) ⟨380315, by rfl⟩ : syracuseStep 2028349 = 760631) (by norm_num)
theorem B4272965 : Blo 1264450 4272965 := bbase (se 4 (by rfl) ⟨400590, by rfl⟩ : syracuseStep 4272965 = 801181) (by norm_num)
theorem B1897301 : Blo 1264450 1897301 := bbase (se 9 (by rfl) ⟨5558, by rfl⟩ : syracuseStep 1897301 = 11117) (by norm_num)
theorem B2847581 : Blo 1264450 2847581 := bbase (se 3 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 2847581 = 1067843) (by norm_num)
theorem B4805477 : Blo 1264450 4805477 := bbase (se 4 (by rfl) ⟨450513, by rfl⟩ : syracuseStep 4805477 = 901027) (by norm_num)
theorem B1897325 : Blo 1264450 1897325 := bbase (se 3 (by rfl) ⟨355748, by rfl⟩ : syracuseStep 1897325 = 711497) (by norm_num)
theorem B1602433 : Blo 1264450 1602433 := bbase (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) (by norm_num)
theorem B1897349 : Blo 1264450 1897349 := bbase (se 4 (by rfl) ⟨177876, by rfl⟩ : syracuseStep 1897349 = 355753) (by norm_num)
theorem B1897373 : Blo 1264450 1897373 := bbase (se 3 (by rfl) ⟨355757, by rfl⟩ : syracuseStep 1897373 = 711515) (by norm_num)
theorem B2847653 : Blo 1264450 2847653 := bbase (se 4 (by rfl) ⟨266967, by rfl⟩ : syracuseStep 2847653 = 533935) (by norm_num)
theorem B2134957 : Blo 1264450 2134957 := bbase (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) (by norm_num)
theorem B1897397 : Blo 1264450 1897397 := bbase (se 5 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 1897397 = 177881) (by norm_num)
theorem B1897421 : Blo 1264450 1897421 := bbase (se 3 (by rfl) ⟨355766, by rfl⟩ : syracuseStep 1897421 = 711533) (by norm_num)
theorem B1897445 : Blo 1264450 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B1463269 : Blo 1264450 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B2847725 : Blo 1264450 2847725 := bbase (se 3 (by rfl) ⟨533948, by rfl⟩ : syracuseStep 2847725 = 1067897) (by norm_num)
theorem B3601397 : Blo 1264450 3601397 := bbase (se 5 (by rfl) ⟨168815, by rfl⟩ : syracuseStep 3601397 = 337631) (by norm_num)
theorem B4051957 : Blo 1264450 4051957 := bbase (se 5 (by rfl) ⟨189935, by rfl⟩ : syracuseStep 4051957 = 379871) (by norm_num)
theorem B1897469 : Blo 1264450 1897469 := bbase (se 3 (by rfl) ⟨355775, by rfl⟩ : syracuseStep 1897469 = 711551) (by norm_num)
theorem B2135045 : Blo 1264450 2135045 := bbase (se 4 (by rfl) ⟨200160, by rfl⟩ : syracuseStep 2135045 = 400321) (by norm_num)
theorem B1897493 : Blo 1264450 1897493 := bbase (se 6 (by rfl) ⟨44472, by rfl⟩ : syracuseStep 1897493 = 88945) (by norm_num)
theorem B1897517 : Blo 1264450 1897517 := bbase (se 3 (by rfl) ⟨355784, by rfl⟩ : syracuseStep 1897517 = 711569) (by norm_num)
theorem B1602605 : Blo 1264450 1602605 := bbase (se 3 (by rfl) ⟨300488, by rfl⟩ : syracuseStep 1602605 = 600977) (by norm_num)
theorem B2847797 : Blo 1264450 2847797 := bbase (se 5 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 2847797 = 266981) (by norm_num)
theorem B1897541 : Blo 1264450 1897541 := bbase (se 4 (by rfl) ⟨177894, by rfl⟩ : syracuseStep 1897541 = 355789) (by norm_num)
theorem B3249229 : Blo 1264450 3249229 := bbase (se 3 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 3249229 = 1218461) (by norm_num)
theorem B1897565 : Blo 1264450 1897565 := bbase (se 3 (by rfl) ⟨355793, by rfl⟩ : syracuseStep 1897565 = 711587) (by norm_num)
theorem B1602661 : Blo 1264450 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B1897589 : Blo 1264450 1897589 := bbase (se 5 (by rfl) ⟨88949, by rfl⟩ : syracuseStep 1897589 = 177899) (by norm_num)
theorem B2847869 : Blo 1264450 2847869 := bbase (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) (by norm_num)
theorem B2135173 : Blo 1264450 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B1897613 : Blo 1264450 1897613 := bbase (se 3 (by rfl) ⟨355802, by rfl⟩ : syracuseStep 1897613 = 711605) (by norm_num)
theorem B1897637 : Blo 1264450 1897637 := bbase (se 4 (by rfl) ⟨177903, by rfl⟩ : syracuseStep 1897637 = 355807) (by norm_num)
theorem B3421349 : Blo 1264450 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B1422517 : Blo 1264450 1422517 := bbase (se 5 (by rfl) ⟨66680, by rfl⟩ : syracuseStep 1422517 = 133361) (by norm_num)
theorem B1897661 : Blo 1264450 1897661 := bbase (se 3 (by rfl) ⟨355811, by rfl⟩ : syracuseStep 1897661 = 711623) (by norm_num)
theorem B2847941 : Blo 1264450 2847941 := bbase (se 4 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 2847941 = 533989) (by norm_num)
theorem B1602757 : Blo 1264450 1602757 := bbase (se 4 (by rfl) ⟨150258, by rfl⟩ : syracuseStep 1602757 = 300517) (by norm_num)
theorem B1897685 : Blo 1264450 1897685 := bbase (se 7 (by rfl) ⟨22238, by rfl⟩ : syracuseStep 1897685 = 44477) (by norm_num)
theorem B1422553 : Blo 1264450 1422553 := bbase (se 2 (by rfl) ⟨533457, by rfl⟩ : syracuseStep 1422553 = 1066915) (by norm_num)
theorem B2135261 : Blo 1264450 2135261 := bbase (se 3 (by rfl) ⟨400361, by rfl⟩ : syracuseStep 2135261 = 800723) (by norm_num)
theorem B1897709 : Blo 1264450 1897709 := bbase (se 3 (by rfl) ⟨355820, by rfl⟩ : syracuseStep 1897709 = 711641) (by norm_num)
theorem B4273397 : Blo 1264450 4273397 := bbase (se 5 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 4273397 = 400631) (by norm_num)
theorem B1422589 : Blo 1264450 1422589 := bbase (se 3 (by rfl) ⟨266735, by rfl⟩ : syracuseStep 1422589 = 533471) (by norm_num)
theorem B1897733 : Blo 1264450 1897733 := bbase (se 4 (by rfl) ⟨177912, by rfl⟩ : syracuseStep 1897733 = 355825) (by norm_num)
theorem B2848013 : Blo 1264450 2848013 := bbase (se 3 (by rfl) ⟨534002, by rfl⟩ : syracuseStep 2848013 = 1068005) (by norm_num)
theorem B1897757 : Blo 1264450 1897757 := bbase (se 3 (by rfl) ⟨355829, by rfl⟩ : syracuseStep 1897757 = 711659) (by norm_num)
theorem B1422625 : Blo 1264450 1422625 := bbase (se 2 (by rfl) ⟨533484, by rfl⟩ : syracuseStep 1422625 = 1066969) (by norm_num)
theorem B5403941 : Blo 1264450 5403941 := bbase (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) (by norm_num)
theorem B1897781 : Blo 1264450 1897781 := bbase (se 5 (by rfl) ⟨88958, by rfl⟩ : syracuseStep 1897781 = 177917) (by norm_num)
theorem B1422661 : Blo 1264450 1422661 := bbase (se 4 (by rfl) ⟨133374, by rfl⟩ : syracuseStep 1422661 = 266749) (by norm_num)
theorem B1897805 : Blo 1264450 1897805 := bbase (se 3 (by rfl) ⟨355838, by rfl⟩ : syracuseStep 1897805 = 711677) (by norm_num)
theorem B2848085 : Blo 1264450 2848085 := bbase (se 13 (by rfl) ⟨521, by rfl⟩ : syracuseStep 2848085 = 1043) (by norm_num)
theorem B2135389 : Blo 1264450 2135389 := bbase (se 3 (by rfl) ⟨400385, by rfl⟩ : syracuseStep 2135389 = 800771) (by norm_num)
theorem B1897829 : Blo 1264450 1897829 := bbase (se 4 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 1897829 = 355843) (by norm_num)
theorem B1422697 : Blo 1264450 1422697 := bbase (se 2 (by rfl) ⟨533511, by rfl⟩ : syracuseStep 1422697 = 1067023) (by norm_num)
theorem B1897853 : Blo 1264450 1897853 := bbase (se 3 (by rfl) ⟨355847, by rfl⟩ : syracuseStep 1897853 = 711695) (by norm_num)
theorem B1422733 : Blo 1264450 1422733 := bbase (se 3 (by rfl) ⟨266762, by rfl⟩ : syracuseStep 1422733 = 533525) (by norm_num)
theorem B1897877 : Blo 1264450 1897877 := bbase (se 6 (by rfl) ⟨44481, by rfl⟩ : syracuseStep 1897877 = 88963) (by norm_num)
theorem B2848157 : Blo 1264450 2848157 := bbase (se 3 (by rfl) ⟨534029, by rfl⟩ : syracuseStep 2848157 = 1068059) (by norm_num)
theorem B1897901 : Blo 1264450 1897901 := bbase (se 3 (by rfl) ⟨355856, by rfl⟩ : syracuseStep 1897901 = 711713) (by norm_num)
theorem B1422769 : Blo 1264450 1422769 := bbase (se 2 (by rfl) ⟨533538, by rfl⟩ : syracuseStep 1422769 = 1067077) (by norm_num)
theorem B2135477 : Blo 1264450 2135477 := bbase (se 5 (by rfl) ⟨100100, by rfl⟩ : syracuseStep 2135477 = 200201) (by norm_num)
theorem B1897925 : Blo 1264450 1897925 := bbase (se 4 (by rfl) ⟨177930, by rfl⟩ : syracuseStep 1897925 = 355861) (by norm_num)
theorem B1422805 : Blo 1264450 1422805 := bbase (se 7 (by rfl) ⟨16673, by rfl⟩ : syracuseStep 1422805 = 33347) (by norm_num)
theorem B1283545 : Blo 1264450 1283545 := bbase (se 2 (by rfl) ⟨481329, by rfl⟩ : syracuseStep 1283545 = 962659) (by norm_num)
theorem B1897949 : Blo 1264450 1897949 := bbase (se 3 (by rfl) ⟨355865, by rfl⟩ : syracuseStep 1897949 = 711731) (by norm_num)
theorem B2848229 : Blo 1264450 2848229 := bbase (se 4 (by rfl) ⟨267021, by rfl⟩ : syracuseStep 2848229 = 534043) (by norm_num)
theorem B1897973 : Blo 1264450 1897973 := bbase (se 5 (by rfl) ⟨88967, by rfl⟩ : syracuseStep 1897973 = 177935) (by norm_num)
theorem B1422841 : Blo 1264450 1422841 := bbase (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) (by norm_num)
theorem B1283581 : Blo 1264450 1283581 := bbase (se 3 (by rfl) ⟨240671, by rfl⟩ : syracuseStep 1283581 = 481343) (by norm_num)
theorem B1897997 : Blo 1264450 1897997 := bbase (se 3 (by rfl) ⟨355874, by rfl⟩ : syracuseStep 1897997 = 711749) (by norm_num)
theorem B1422877 : Blo 1264450 1422877 := bbase (se 3 (by rfl) ⟨266789, by rfl⟩ : syracuseStep 1422877 = 533579) (by norm_num)
theorem B1521185 : Blo 1264450 1521185 := bbase (se 2 (by rfl) ⟨570444, by rfl⟩ : syracuseStep 1521185 = 1140889) (by norm_num)
theorem B1898021 : Blo 1264450 1898021 := bbase (se 4 (by rfl) ⟨177939, by rfl⟩ : syracuseStep 1898021 = 355879) (by norm_num)
theorem B2848301 : Blo 1264450 2848301 := bbase (se 3 (by rfl) ⟨534056, by rfl⟩ : syracuseStep 2848301 = 1068113) (by norm_num)
theorem B2135605 : Blo 1264450 2135605 := bbase (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) (by norm_num)
theorem B1898045 : Blo 1264450 1898045 := bbase (se 3 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 1898045 = 711767) (by norm_num)
theorem B1422913 : Blo 1264450 1422913 := bbase (se 2 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 1422913 = 1067185) (by norm_num)
theorem B2700877 : Blo 1264450 2700877 := bbase (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) (by norm_num)
theorem B1898069 : Blo 1264450 1898069 := bbase (se 8 (by rfl) ⟨11121, by rfl⟩ : syracuseStep 1898069 = 22243) (by norm_num)
theorem B1422949 : Blo 1264450 1422949 := bbase (se 4 (by rfl) ⟨133401, by rfl⟩ : syracuseStep 1422949 = 266803) (by norm_num)
theorem B1898093 : Blo 1264450 1898093 := bbase (se 3 (by rfl) ⟨355892, by rfl⟩ : syracuseStep 1898093 = 711785) (by norm_num)
theorem B2848373 : Blo 1264450 2848373 := bbase (se 5 (by rfl) ⟨133517, by rfl⟩ : syracuseStep 2848373 = 267035) (by norm_num)
theorem B1898117 : Blo 1264450 1898117 := bbase (se 4 (by rfl) ⟨177948, by rfl⟩ : syracuseStep 1898117 = 355897) (by norm_num)
theorem B1422985 : Blo 1264450 1422985 := bbase (se 2 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 1422985 = 1067239) (by norm_num)
theorem B2135693 : Blo 1264450 2135693 := bbase (se 3 (by rfl) ⟨400442, by rfl⟩ : syracuseStep 2135693 = 800885) (by norm_num)
theorem B1898141 : Blo 1264450 1898141 := bbase (se 3 (by rfl) ⟨355901, by rfl⟩ : syracuseStep 1898141 = 711803) (by norm_num)
theorem B4273829 : Blo 1264450 4273829 := bbase (se 4 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 4273829 = 801343) (by norm_num)
theorem B1423021 : Blo 1264450 1423021 := bbase (se 3 (by rfl) ⟨266816, by rfl⟩ : syracuseStep 1423021 = 533633) (by norm_num)
theorem B1898165 : Blo 1264450 1898165 := bbase (se 5 (by rfl) ⟨88976, by rfl⟩ : syracuseStep 1898165 = 177953) (by norm_num)
theorem B2848445 : Blo 1264450 2848445 := bbase (se 3 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 2848445 = 1068167) (by norm_num)
theorem B1898189 : Blo 1264450 1898189 := bbase (se 3 (by rfl) ⟨355910, by rfl⟩ : syracuseStep 1898189 = 711821) (by norm_num)
theorem B1423057 : Blo 1264450 1423057 := bbase (se 2 (by rfl) ⟨533646, by rfl⟩ : syracuseStep 1423057 = 1067293) (by norm_num)
theorem B1898213 : Blo 1264450 1898213 := bbase (se 4 (by rfl) ⟨177957, by rfl⟩ : syracuseStep 1898213 = 355915) (by norm_num)
theorem B1423093 : Blo 1264450 1423093 := bbase (se 5 (by rfl) ⟨66707, by rfl⟩ : syracuseStep 1423093 = 133415) (by norm_num)
theorem B1898237 : Blo 1264450 1898237 := bbase (se 3 (by rfl) ⟨355919, by rfl⟩ : syracuseStep 1898237 = 711839) (by norm_num)
theorem B2848517 : Blo 1264450 2848517 := bbase (se 4 (by rfl) ⟨267048, by rfl⟩ : syracuseStep 2848517 = 534097) (by norm_num)
theorem B2135821 : Blo 1264450 2135821 := bbase (se 3 (by rfl) ⟨400466, by rfl⟩ : syracuseStep 2135821 = 800933) (by norm_num)
theorem B1898261 : Blo 1264450 1898261 := bbase (se 6 (by rfl) ⟨44490, by rfl⟩ : syracuseStep 1898261 = 88981) (by norm_num)
theorem B1423129 : Blo 1264450 1423129 := bbase (se 2 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 1423129 = 1067347) (by norm_num)
theorem B1898285 : Blo 1264450 1898285 := bbase (se 3 (by rfl) ⟨355928, by rfl⟩ : syracuseStep 1898285 = 711857) (by norm_num)
theorem B1423165 : Blo 1264450 1423165 := bbase (se 3 (by rfl) ⟨266843, by rfl⟩ : syracuseStep 1423165 = 533687) (by norm_num)
theorem B1898309 : Blo 1264450 1898309 := bbase (se 4 (by rfl) ⟨177966, by rfl⟩ : syracuseStep 1898309 = 355933) (by norm_num)
theorem B2848589 : Blo 1264450 2848589 := bbase (se 3 (by rfl) ⟨534110, by rfl⟩ : syracuseStep 2848589 = 1068221) (by norm_num)
theorem B1898333 : Blo 1264450 1898333 := bbase (se 3 (by rfl) ⟨355937, by rfl⟩ : syracuseStep 1898333 = 711875) (by norm_num)
theorem B1423201 : Blo 1264450 1423201 := bbase (se 2 (by rfl) ⟨533700, by rfl⟩ : syracuseStep 1423201 = 1067401) (by norm_num)
theorem B2135909 : Blo 1264450 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B1898357 : Blo 1264450 1898357 := bbase (se 5 (by rfl) ⟨88985, by rfl⟩ : syracuseStep 1898357 = 177971) (by norm_num)
theorem B1423237 : Blo 1264450 1423237 := bbase (se 4 (by rfl) ⟨133428, by rfl⟩ : syracuseStep 1423237 = 266857) (by norm_num)
theorem B1898381 : Blo 1264450 1898381 := bbase (se 3 (by rfl) ⟨355946, by rfl⟩ : syracuseStep 1898381 = 711893) (by norm_num)
theorem B3200917 : Blo 1264450 3200917 := bbase (se 6 (by rfl) ⟨75021, by rfl⟩ : syracuseStep 3200917 = 150043) (by norm_num)
theorem B2848661 : Blo 1264450 2848661 := bbase (se 6 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 2848661 = 133531) (by norm_num)
theorem B1898405 : Blo 1264450 1898405 := bbase (se 4 (by rfl) ⟨177975, by rfl⟩ : syracuseStep 1898405 = 355951) (by norm_num)
theorem B1423273 : Blo 1264450 1423273 := bbase (se 2 (by rfl) ⟨533727, by rfl⟩ : syracuseStep 1423273 = 1067455) (by norm_num)
theorem B6404021 : Blo 1264450 6404021 := bbase (se 5 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 6404021 = 600377) (by norm_num)
theorem B1898429 : Blo 1264450 1898429 := bbase (se 3 (by rfl) ⟨355955, by rfl⟩ : syracuseStep 1898429 = 711911) (by norm_num)
theorem B1423309 : Blo 1264450 1423309 := bbase (se 3 (by rfl) ⟨266870, by rfl⟩ : syracuseStep 1423309 = 533741) (by norm_num)
theorem B1898453 : Blo 1264450 1898453 := bbase (se 7 (by rfl) ⟨22247, by rfl⟩ : syracuseStep 1898453 = 44495) (by norm_num)
theorem B2848733 : Blo 1264450 2848733 := bbase (se 3 (by rfl) ⟨534137, by rfl⟩ : syracuseStep 2848733 = 1068275) (by norm_num)
theorem B2136037 : Blo 1264450 2136037 := bbase (se 4 (by rfl) ⟨200253, by rfl⟩ : syracuseStep 2136037 = 400507) (by norm_num)
theorem B1898477 : Blo 1264450 1898477 := bbase (se 3 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 1898477 = 711929) (by norm_num)
theorem B1423345 : Blo 1264450 1423345 := bbase (se 2 (by rfl) ⟨533754, by rfl⟩ : syracuseStep 1423345 = 1067509) (by norm_num)
theorem B3201029 : Blo 1264450 3201029 := bbase (se 4 (by rfl) ⟨300096, by rfl⟩ : syracuseStep 3201029 = 600193) (by norm_num)
theorem B1898501 : Blo 1264450 1898501 := bbase (se 4 (by rfl) ⟨177984, by rfl⟩ : syracuseStep 1898501 = 355969) (by norm_num)
theorem B4806661 : Blo 1264450 4806661 := bbase (se 4 (by rfl) ⟨450624, by rfl⟩ : syracuseStep 4806661 = 901249) (by norm_num)
theorem B1423381 : Blo 1264450 1423381 := bbase (se 6 (by rfl) ⟨33360, by rfl⟩ : syracuseStep 1423381 = 66721) (by norm_num)
theorem B11548693 : Blo 1264450 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B1898525 : Blo 1264450 1898525 := bbase (se 3 (by rfl) ⟨355973, by rfl⟩ : syracuseStep 1898525 = 711947) (by norm_num)
theorem B2848805 : Blo 1264450 2848805 := bbase (se 4 (by rfl) ⟨267075, by rfl⟩ : syracuseStep 2848805 = 534151) (by norm_num)
theorem B1898549 : Blo 1264450 1898549 := bbase (se 5 (by rfl) ⟨88994, by rfl⟩ : syracuseStep 1898549 = 177989) (by norm_num)
theorem B1423417 : Blo 1264450 1423417 := bbase (se 2 (by rfl) ⟨533781, by rfl⟩ : syracuseStep 1423417 = 1067563) (by norm_num)
theorem B2136125 : Blo 1264450 2136125 := bbase (se 3 (by rfl) ⟨400523, by rfl⟩ : syracuseStep 2136125 = 801047) (by norm_num)
theorem B1898573 : Blo 1264450 1898573 := bbase (se 3 (by rfl) ⟨355982, by rfl⟩ : syracuseStep 1898573 = 711965) (by norm_num)
theorem B4274261 : Blo 1264450 4274261 := bbase (se 8 (by rfl) ⟨25044, by rfl⟩ : syracuseStep 4274261 = 50089) (by norm_num)
theorem B1423453 : Blo 1264450 1423453 := bbase (se 3 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 1423453 = 533795) (by norm_num)
theorem B1898597 : Blo 1264450 1898597 := bbase (se 4 (by rfl) ⟨177993, by rfl⟩ : syracuseStep 1898597 = 355987) (by norm_num)
theorem B2848877 : Blo 1264450 2848877 := bbase (se 3 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 2848877 = 1068329) (by norm_num)
theorem B1898621 : Blo 1264450 1898621 := bbase (se 3 (by rfl) ⟨355991, by rfl⟩ : syracuseStep 1898621 = 711983) (by norm_num)
theorem B1423489 : Blo 1264450 1423489 := bbase (se 2 (by rfl) ⟨533808, by rfl⟩ : syracuseStep 1423489 = 1067617) (by norm_num)
theorem B1898645 : Blo 1264450 1898645 := bbase (se 6 (by rfl) ⟨44499, by rfl⟩ : syracuseStep 1898645 = 88999) (by norm_num)
theorem B9615509 : Blo 1264450 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B1423525 : Blo 1264450 1423525 := bbase (se 4 (by rfl) ⟨133455, by rfl⟩ : syracuseStep 1423525 = 266911) (by norm_num)
theorem B1898669 : Blo 1264450 1898669 := bbase (se 3 (by rfl) ⟨356000, by rfl⟩ : syracuseStep 1898669 = 712001) (by norm_num)
theorem B2848949 : Blo 1264450 2848949 := bbase (se 5 (by rfl) ⟨133544, by rfl⟩ : syracuseStep 2848949 = 267089) (by norm_num)
theorem B2136253 : Blo 1264450 2136253 := bbase (se 3 (by rfl) ⟨400547, by rfl⟩ : syracuseStep 2136253 = 801095) (by norm_num)
theorem B3201221 : Blo 1264450 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B1898693 : Blo 1264450 1898693 := bbase (se 4 (by rfl) ⟨178002, by rfl⟩ : syracuseStep 1898693 = 356005) (by norm_num)
theorem B1423561 : Blo 1264450 1423561 := bbase (se 2 (by rfl) ⟨533835, by rfl⟩ : syracuseStep 1423561 = 1067671) (by norm_num)
theorem B1800397 : Blo 1264450 1800397 := bbase (se 3 (by rfl) ⟨337574, by rfl⟩ : syracuseStep 1800397 = 675149) (by norm_num)
theorem B1898717 : Blo 1264450 1898717 := bbase (se 3 (by rfl) ⟨356009, by rfl⟩ : syracuseStep 1898717 = 712019) (by norm_num)
theorem B1423597 : Blo 1264450 1423597 := bbase (se 3 (by rfl) ⟨266924, by rfl⟩ : syracuseStep 1423597 = 533849) (by norm_num)
theorem B1898741 : Blo 1264450 1898741 := bbase (se 5 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 1898741 = 178007) (by norm_num)
theorem B2849021 : Blo 1264450 2849021 := bbase (se 3 (by rfl) ⟨534191, by rfl⟩ : syracuseStep 2849021 = 1068383) (by norm_num)
theorem B1898765 : Blo 1264450 1898765 := bbase (se 3 (by rfl) ⟨356018, by rfl⟩ : syracuseStep 1898765 = 712037) (by norm_num)
theorem B1423633 : Blo 1264450 1423633 := bbase (se 2 (by rfl) ⟨533862, by rfl⟩ : syracuseStep 1423633 = 1067725) (by norm_num)
theorem B2136341 : Blo 1264450 2136341 := bbase (se 6 (by rfl) ⟨50070, by rfl⟩ : syracuseStep 2136341 = 100141) (by norm_num)
theorem B1898789 : Blo 1264450 1898789 := bbase (se 4 (by rfl) ⟨178011, by rfl⟩ : syracuseStep 1898789 = 356023) (by norm_num)
theorem B1423669 : Blo 1264450 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B4806965 : Blo 1264450 4806965 := bbase (se 5 (by rfl) ⟨225326, by rfl⟩ : syracuseStep 4806965 = 450653) (by norm_num)
theorem B1898813 : Blo 1264450 1898813 := bbase (se 3 (by rfl) ⟨356027, by rfl⟩ : syracuseStep 1898813 = 712055) (by norm_num)
theorem B2849093 : Blo 1264450 2849093 := bbase (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) (by norm_num)
theorem B1898837 : Blo 1264450 1898837 := bbase (se 10 (by rfl) ⟨2781, by rfl⟩ : syracuseStep 1898837 = 5563) (by norm_num)
theorem B1423705 : Blo 1264450 1423705 := bbase (se 2 (by rfl) ⟨533889, by rfl⟩ : syracuseStep 1423705 = 1067779) (by norm_num)
theorem B1898861 : Blo 1264450 1898861 := bbase (se 3 (by rfl) ⟨356036, by rfl⟩ : syracuseStep 1898861 = 712073) (by norm_num)
theorem B1423741 : Blo 1264450 1423741 := bbase (se 3 (by rfl) ⟨266951, by rfl⟩ : syracuseStep 1423741 = 533903) (by norm_num)
theorem B1898885 : Blo 1264450 1898885 := bbase (se 4 (by rfl) ⟨178020, by rfl⟩ : syracuseStep 1898885 = 356041) (by norm_num)
theorem B2849165 : Blo 1264450 2849165 := bbase (se 3 (by rfl) ⟨534218, by rfl⟩ : syracuseStep 2849165 = 1068437) (by norm_num)
theorem B2136469 : Blo 1264450 2136469 := bbase (se 6 (by rfl) ⟨50073, by rfl⟩ : syracuseStep 2136469 = 100147) (by norm_num)
theorem B1898909 : Blo 1264450 1898909 := bbase (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) (by norm_num)
theorem B1423777 : Blo 1264450 1423777 := bbase (se 2 (by rfl) ⟨533916, by rfl⟩ : syracuseStep 1423777 = 1067833) (by norm_num)
theorem B1898933 : Blo 1264450 1898933 := bbase (se 5 (by rfl) ⟨89012, by rfl⟩ : syracuseStep 1898933 = 178025) (by norm_num)
theorem B2701765 : Blo 1264450 2701765 := bbase (se 4 (by rfl) ⟨253290, by rfl⟩ : syracuseStep 2701765 = 506581) (by norm_num)
theorem B1423813 : Blo 1264450 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B1898957 : Blo 1264450 1898957 := bbase (se 3 (by rfl) ⟨356054, by rfl⟩ : syracuseStep 1898957 = 712109) (by norm_num)
theorem B2849237 : Blo 1264450 2849237 := bbase (se 7 (by rfl) ⟨33389, by rfl⟩ : syracuseStep 2849237 = 66779) (by norm_num)
theorem B2193893 : Blo 1264450 2193893 := bbase (se 4 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 2193893 = 411355) (by norm_num)
theorem B1898981 : Blo 1264450 1898981 := bbase (se 4 (by rfl) ⟨178029, by rfl⟩ : syracuseStep 1898981 = 356059) (by norm_num)
theorem B1423849 : Blo 1264450 1423849 := bbase (se 2 (by rfl) ⟨533943, by rfl⟩ : syracuseStep 1423849 = 1067887) (by norm_num)
theorem B2136557 : Blo 1264450 2136557 := bbase (se 3 (by rfl) ⟨400604, by rfl⟩ : syracuseStep 2136557 = 801209) (by norm_num)
theorem B1899005 : Blo 1264450 1899005 := bbase (se 3 (by rfl) ⟨356063, by rfl⟩ : syracuseStep 1899005 = 712127) (by norm_num)
theorem B1423885 : Blo 1264450 1423885 := bbase (se 3 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 1423885 = 533957) (by norm_num)
theorem B1899029 : Blo 1264450 1899029 := bbase (se 6 (by rfl) ⟨44508, by rfl⟩ : syracuseStep 1899029 = 89017) (by norm_num)
theorem B1800733 : Blo 1264450 1800733 := bbase (se 3 (by rfl) ⟨337637, by rfl⟩ : syracuseStep 1800733 = 675275) (by norm_num)
theorem B3201565 : Blo 1264450 3201565 := bbase (se 3 (by rfl) ⟨600293, by rfl⟩ : syracuseStep 3201565 = 1200587) (by norm_num)
theorem B2849309 : Blo 1264450 2849309 := bbase (se 3 (by rfl) ⟨534245, by rfl⟩ : syracuseStep 2849309 = 1068491) (by norm_num)
theorem B3602981 : Blo 1264450 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B1899053 : Blo 1264450 1899053 := bbase (se 3 (by rfl) ⟨356072, by rfl⟩ : syracuseStep 1899053 = 712145) (by norm_num)
theorem B1423921 : Blo 1264450 1423921 := bbase (se 2 (by rfl) ⟨533970, by rfl⟩ : syracuseStep 1423921 = 1067941) (by norm_num)
theorem B9607733 : Blo 1264450 9607733 := bbase (se 5 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 9607733 = 900725) (by norm_num)
theorem B1899077 : Blo 1264450 1899077 := bbase (se 4 (by rfl) ⟨178038, by rfl⟩ : syracuseStep 1899077 = 356077) (by norm_num)
theorem B1423957 : Blo 1264450 1423957 := bbase (se 8 (by rfl) ⟨8343, by rfl⟩ : syracuseStep 1423957 = 16687) (by norm_num)
theorem B1899101 : Blo 1264450 1899101 := bbase (se 3 (by rfl) ⟨356081, by rfl⟩ : syracuseStep 1899101 = 712163) (by norm_num)
theorem B2849381 : Blo 1264450 2849381 := bbase (se 4 (by rfl) ⟨267129, by rfl⟩ : syracuseStep 2849381 = 534259) (by norm_num)
theorem B2136685 : Blo 1264450 2136685 := bbase (se 3 (by rfl) ⟨400628, by rfl⟩ : syracuseStep 2136685 = 801257) (by norm_num)
theorem B1899125 : Blo 1264450 1899125 := bbase (se 5 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 1899125 = 178043) (by norm_num)
theorem B1423993 : Blo 1264450 1423993 := bbase (se 2 (by rfl) ⟨533997, by rfl⟩ : syracuseStep 1423993 = 1067995) (by norm_num)
theorem B3201677 : Blo 1264450 3201677 := bbase (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) (by norm_num)
theorem B1899149 : Blo 1264450 1899149 := bbase (se 3 (by rfl) ⟨356090, by rfl⟩ : syracuseStep 1899149 = 712181) (by norm_num)
theorem B1424029 : Blo 1264450 1424029 := bbase (se 3 (by rfl) ⟨267005, by rfl⟩ : syracuseStep 1424029 = 534011) (by norm_num)
theorem B1899173 : Blo 1264450 1899173 := bbase (se 4 (by rfl) ⟨178047, by rfl⟩ : syracuseStep 1899173 = 356095) (by norm_num)
theorem B4332197 : Blo 1264450 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B2849453 : Blo 1264450 2849453 := bbase (se 3 (by rfl) ⟨534272, by rfl⟩ : syracuseStep 2849453 = 1068545) (by norm_num)
theorem B1899197 : Blo 1264450 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B1424065 : Blo 1264450 1424065 := bbase (se 2 (by rfl) ⟨534024, by rfl⟩ : syracuseStep 1424065 = 1068049) (by norm_num)
theorem B2136773 : Blo 1264450 2136773 := bbase (se 4 (by rfl) ⟨200322, by rfl⟩ : syracuseStep 2136773 = 400645) (by norm_num)
theorem B1899221 : Blo 1264450 1899221 := bbase (se 7 (by rfl) ⟨22256, by rfl⟩ : syracuseStep 1899221 = 44513) (by norm_num)
theorem B1424101 : Blo 1264450 1424101 := bbase (se 4 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 1424101 = 267019) (by norm_num)
theorem B1899245 : Blo 1264450 1899245 := bbase (se 3 (by rfl) ⟨356108, by rfl⟩ : syracuseStep 1899245 = 712217) (by norm_num)
theorem B1800949 : Blo 1264450 1800949 := bbase (se 5 (by rfl) ⟨84419, by rfl⟩ : syracuseStep 1800949 = 168839) (by norm_num)
theorem B1899269 : Blo 1264450 1899269 := bbase (se 4 (by rfl) ⟨178056, by rfl⟩ : syracuseStep 1899269 = 356113) (by norm_num)
theorem B1424137 : Blo 1264450 1424137 := bbase (se 2 (by rfl) ⟨534051, by rfl⟩ : syracuseStep 1424137 = 1068103) (by norm_num)
theorem B1899293 : Blo 1264450 1899293 := bbase (se 3 (by rfl) ⟨356117, by rfl⟩ : syracuseStep 1899293 = 712235) (by norm_num)
theorem B1424173 : Blo 1264450 1424173 := bbase (se 3 (by rfl) ⟨267032, by rfl⟩ : syracuseStep 1424173 = 534065) (by norm_num)
theorem B1899317 : Blo 1264450 1899317 := bbase (se 5 (by rfl) ⟨89030, by rfl⟩ : syracuseStep 1899317 = 178061) (by norm_num)
theorem B1350469 : Blo 1264450 1350469 := bbase (se 4 (by rfl) ⟨126606, by rfl⟩ : syracuseStep 1350469 = 253213) (by norm_num)
theorem B2136901 : Blo 1264450 2136901 := bbase (se 4 (by rfl) ⟨200334, by rfl⟩ : syracuseStep 2136901 = 400669) (by norm_num)
theorem B3201869 : Blo 1264450 3201869 := bbase (se 3 (by rfl) ⟨600350, by rfl⟩ : syracuseStep 3201869 = 1200701) (by norm_num)
theorem B1899341 : Blo 1264450 1899341 := bbase (se 3 (by rfl) ⟨356126, by rfl⟩ : syracuseStep 1899341 = 712253) (by norm_num)
theorem B1424209 : Blo 1264450 1424209 := bbase (se 2 (by rfl) ⟨534078, by rfl⟩ : syracuseStep 1424209 = 1068157) (by norm_num)
theorem B1825637 : Blo 1264450 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B1899365 : Blo 1264450 1899365 := bbase (se 4 (by rfl) ⟨178065, by rfl⟩ : syracuseStep 1899365 = 356131) (by norm_num)
theorem B1424245 : Blo 1264450 1424245 := bbase (se 5 (by rfl) ⟨66761, by rfl⟩ : syracuseStep 1424245 = 133523) (by norm_num)
theorem B1899389 : Blo 1264450 1899389 := bbase (se 3 (by rfl) ⟨356135, by rfl⟩ : syracuseStep 1899389 = 712271) (by norm_num)
theorem B1350541 : Blo 1264450 1350541 := bbase (se 3 (by rfl) ⟨253226, by rfl⟩ : syracuseStep 1350541 = 506453) (by norm_num)
theorem B1899413 : Blo 1264450 1899413 := bbase (se 6 (by rfl) ⟨44517, by rfl⟩ : syracuseStep 1899413 = 89035) (by norm_num)
theorem B1424281 : Blo 1264450 1424281 := bbase (se 2 (by rfl) ⟨534105, by rfl⟩ : syracuseStep 1424281 = 1068211) (by norm_num)
theorem B2136989 : Blo 1264450 2136989 := bbase (se 3 (by rfl) ⟨400685, by rfl⟩ : syracuseStep 2136989 = 801371) (by norm_num)
theorem B1899437 : Blo 1264450 1899437 := bbase (se 3 (by rfl) ⟨356144, by rfl⟩ : syracuseStep 1899437 = 712289) (by norm_num)
theorem B2702261 : Blo 1264450 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B4332469 : Blo 1264450 4332469 := bbase (se 5 (by rfl) ⟨203084, by rfl⟩ : syracuseStep 4332469 = 406169) (by norm_num)
theorem B1424317 : Blo 1264450 1424317 := bbase (se 3 (by rfl) ⟨267059, by rfl⟩ : syracuseStep 1424317 = 534119) (by norm_num)
theorem B1899461 : Blo 1264450 1899461 := bbase (se 4 (by rfl) ⟨178074, by rfl⟩ : syracuseStep 1899461 = 356149) (by norm_num)
theorem B1899485 : Blo 1264450 1899485 := bbase (se 3 (by rfl) ⟨356153, by rfl⟩ : syracuseStep 1899485 = 712307) (by norm_num)
theorem B1424353 : Blo 1264450 1424353 := bbase (se 2 (by rfl) ⟨534132, by rfl⟩ : syracuseStep 1424353 = 1068265) (by norm_num)
theorem B1899509 : Blo 1264450 1899509 := bbase (se 5 (by rfl) ⟨89039, by rfl⟩ : syracuseStep 1899509 = 178079) (by norm_num)
theorem B1424389 : Blo 1264450 1424389 := bbase (se 4 (by rfl) ⟨133536, by rfl⟩ : syracuseStep 1424389 = 267073) (by norm_num)
theorem B1899533 : Blo 1264450 1899533 := bbase (se 3 (by rfl) ⟨356162, by rfl⟩ : syracuseStep 1899533 = 712325) (by norm_num)
theorem B5405717 : Blo 1264450 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B2137117 : Blo 1264450 2137117 := bbase (se 3 (by rfl) ⟨400709, by rfl⟩ : syracuseStep 2137117 = 801419) (by norm_num)
theorem B1899557 : Blo 1264450 1899557 := bbase (se 4 (by rfl) ⟨178083, by rfl⟩ : syracuseStep 1899557 = 356167) (by norm_num)
theorem B1424425 : Blo 1264450 1424425 := bbase (se 2 (by rfl) ⟨534159, by rfl⟩ : syracuseStep 1424425 = 1068319) (by norm_num)
theorem B1899581 : Blo 1264450 1899581 := bbase (se 3 (by rfl) ⟨356171, by rfl⟩ : syracuseStep 1899581 = 712343) (by norm_num)
theorem B1424461 : Blo 1264450 1424461 := bbase (se 3 (by rfl) ⟨267086, by rfl⟩ : syracuseStep 1424461 = 534173) (by norm_num)
theorem B1899605 : Blo 1264450 1899605 := bbase (se 8 (by rfl) ⟨11130, by rfl⟩ : syracuseStep 1899605 = 22261) (by norm_num)
theorem B1801325 : Blo 1264450 1801325 := bbase (se 3 (by rfl) ⟨337748, by rfl⟩ : syracuseStep 1801325 = 675497) (by norm_num)
theorem B1899629 : Blo 1264450 1899629 := bbase (se 3 (by rfl) ⟨356180, by rfl⟩ : syracuseStep 1899629 = 712361) (by norm_num)
theorem B1424497 : Blo 1264450 1424497 := bbase (se 2 (by rfl) ⟨534186, by rfl⟩ : syracuseStep 1424497 = 1068373) (by norm_num)
theorem B1899653 : Blo 1264450 1899653 := bbase (se 4 (by rfl) ⟨178092, by rfl⟩ : syracuseStep 1899653 = 356185) (by norm_num)
theorem B5127317 : Blo 1264450 5127317 := bbase (se 6 (by rfl) ⟨120171, by rfl⟩ : syracuseStep 5127317 = 240343) (by norm_num)
theorem B1424533 : Blo 1264450 1424533 := bbase (se 6 (by rfl) ⟨33387, by rfl⟩ : syracuseStep 1424533 = 66775) (by norm_num)
theorem B1924253 : Blo 1264450 1924253 := bbase (se 3 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 1924253 = 721595) (by norm_num)
theorem B3202213 : Blo 1264450 3202213 := bbase (se 4 (by rfl) ⟨300207, by rfl⟩ : syracuseStep 3202213 = 600415) (by norm_num)
theorem B1424569 : Blo 1264450 1424569 := bbase (se 2 (by rfl) ⟨534213, by rfl⟩ : syracuseStep 1424569 = 1068427) (by norm_num)
theorem B6405317 : Blo 1264450 6405317 := bbase (se 4 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 6405317 = 1200997) (by norm_num)
theorem B3603653 : Blo 1264450 3603653 := bbase (se 4 (by rfl) ⟨337842, by rfl⟩ : syracuseStep 3603653 = 675685) (by norm_num)
theorem B1424605 : Blo 1264450 1424605 := bbase (se 3 (by rfl) ⟨267113, by rfl⟩ : syracuseStep 1424605 = 534227) (by norm_num)
theorem B1350913 : Blo 1264450 1350913 := bbase (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) (by norm_num)
theorem B1424641 : Blo 1264450 1424641 := bbase (se 2 (by rfl) ⟨534240, by rfl⟩ : syracuseStep 1424641 = 1068481) (by norm_num)
theorem B3202325 : Blo 1264450 3202325 := bbase (se 6 (by rfl) ⟨75054, by rfl⟩ : syracuseStep 3202325 = 150109) (by norm_num)
theorem B1424677 : Blo 1264450 1424677 := bbase (se 4 (by rfl) ⟨133563, by rfl⟩ : syracuseStep 1424677 = 267127) (by norm_num)
theorem B1424713 : Blo 1264450 1424713 := bbase (se 2 (by rfl) ⟨534267, by rfl⟩ : syracuseStep 1424713 = 1068535) (by norm_num)
theorem B1424749 : Blo 1264450 1424749 := bbase (se 3 (by rfl) ⟨267140, by rfl⟩ : syracuseStep 1424749 = 534281) (by norm_num)
theorem B2194877 : Blo 1264450 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B3202517 : Blo 1264450 3202517 := bbase (se 7 (by rfl) ⟨37529, by rfl⟩ : syracuseStep 3202517 = 75059) (by norm_num)
theorem B6839797 : Blo 1264450 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B3604085 : Blo 1264450 3604085 := bbase (se 5 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 3604085 = 337883) (by norm_num)
theorem B1351289 : Blo 1264450 1351289 := bbase (se 2 (by rfl) ⟨506733, by rfl⟩ : syracuseStep 1351289 = 1013467) (by norm_num)
theorem B8781493 : Blo 1264450 8781493 := bbase (se 5 (by rfl) ⟨411632, by rfl⟩ : syracuseStep 8781493 = 823265) (by norm_num)
theorem B1351361 : Blo 1264450 1351361 := bbase (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) (by norm_num)
theorem B4267781 : Blo 1264450 4267781 := bbase (se 4 (by rfl) ⟨400104, by rfl⟩ : syracuseStep 4267781 = 800209) (by norm_num)
theorem B4054789 : Blo 1264450 4054789 := bbase (se 4 (by rfl) ⟨380136, by rfl⟩ : syracuseStep 4054789 = 760273) (by norm_num)
theorem B2703125 : Blo 1264450 2703125 := bbase (se 6 (by rfl) ⟨63354, by rfl⟩ : syracuseStep 2703125 = 126709) (by norm_num)
theorem B1924885 : Blo 1264450 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B3202861 : Blo 1264450 3202861 := bbase (se 3 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 3202861 = 1201073) (by norm_num)
theorem B4054853 : Blo 1264450 4054853 := bbase (se 4 (by rfl) ⟨380142, by rfl⟩ : syracuseStep 4054853 = 760285) (by norm_num)
theorem B1351549 : Blo 1264450 1351549 := bbase (se 3 (by rfl) ⟨253415, by rfl⟩ : syracuseStep 1351549 = 506831) (by norm_num)
theorem B6078341 : Blo 1264450 6078341 := bbase (se 4 (by rfl) ⟨569844, by rfl⟩ : syracuseStep 6078341 = 1139689) (by norm_num)
theorem B3202973 : Blo 1264450 3202973 := bbase (se 3 (by rfl) ⟨600557, by rfl⟩ : syracuseStep 3202973 = 1201115) (by norm_num)
theorem B2703269 : Blo 1264450 2703269 := bbase (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) (by norm_num)
theorem B5406709 : Blo 1264450 5406709 := bbase (se 5 (by rfl) ⟨253439, by rfl⟩ : syracuseStep 5406709 = 506879) (by norm_num)
theorem B8110115 : Blo 1264450 8110115 := bstep (se 1 (by rfl) ⟨6082586, by rfl⟩ : syracuseStep 8110115 = 12165173) B12165173
theorem B7692337 : Blo 1264450 7692337 := bstep (se 2 (by rfl) ⟨2884626, by rfl⟩ : syracuseStep 7692337 = 5769253) B5769253
theorem B3203185 : Blo 1264450 3203185 := bstep (se 2 (by rfl) ⟨1201194, by rfl⟩ : syracuseStep 3203185 = 2402389) B2402389
theorem B3604621 : Blo 1264450 3604621 := bstep (se 3 (by rfl) ⟨675866, by rfl⟩ : syracuseStep 3604621 = 1351733) B1351733
theorem B3653837 : Blo 1264450 3653837 := bstep (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) B1370189
theorem B1351891 : Blo 1264450 1351891 := bstep (se 1 (by rfl) ⟨1013918, by rfl⟩ : syracuseStep 1351891 = 2027837) B2027837
theorem B14418161 : Blo 1264450 14418161 := bstep (se 2 (by rfl) ⟨5406810, by rfl⟩ : syracuseStep 14418161 = 10813621) B10813621
theorem B2400529 : Blo 1264450 2400529 := bstep (se 2 (by rfl) ⟨900198, by rfl⟩ : syracuseStep 2400529 = 1800397) B1800397
theorem B3203459 : Blo 1264450 3203459 := bstep (se 1 (by rfl) ⟨2402594, by rfl⟩ : syracuseStep 3203459 = 4805189) B4805189
theorem B4268429 : Blo 1264450 4268429 := bstep (se 3 (by rfl) ⟨800330, by rfl⟩ : syracuseStep 4268429 = 1600661) B1600661
theorem B1802675 : Blo 1264450 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B4268483 : Blo 1264450 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B1352147 : Blo 1264450 1352147 := bstep (se 1 (by rfl) ⟨1014110, by rfl⟩ : syracuseStep 1352147 = 2028221) B2028221
theorem B3203651 : Blo 1264450 3203651 := bstep (se 1 (by rfl) ⟨2402738, by rfl⟩ : syracuseStep 3203651 = 4805477) B4805477
theorem B3850829 : Blo 1264450 3850829 := bstep (se 3 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 3850829 = 1444061) B1444061
theorem B2400931 : Blo 1264450 2400931 := bstep (se 1 (by rfl) ⟨1800698, by rfl⟩ : syracuseStep 2400931 = 3601397) B3601397
theorem B2400977 : Blo 1264450 2400977 := bstep (se 2 (by rfl) ⟨900366, by rfl⟩ : syracuseStep 2400977 = 1800733) B1800733
theorem B4268753 : Blo 1264450 4268753 := bstep (se 2 (by rfl) ⟨1600782, by rfl⟩ : syracuseStep 4268753 = 3201565) B3201565
theorem B36487907 : Blo 1264450 36487907 := bstep (se 1 (by rfl) ⟨27365930, by rfl⟩ : syracuseStep 36487907 = 54731861) B54731861
theorem B6841073 : Blo 1264450 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B4801315 : Blo 1264450 4801315 := bstep (se 1 (by rfl) ⟨3600986, by rfl⟩ : syracuseStep 4801315 = 7201973) B7201973
theorem B2401265 : Blo 1264450 2401265 := bstep (se 2 (by rfl) ⟨900474, by rfl⟩ : syracuseStep 2401265 = 1800949) B1800949
theorem B2704465 : Blo 1264450 2704465 := bstep (se 2 (by rfl) ⟨1014174, by rfl⟩ : syracuseStep 2704465 = 2028349) B2028349
theorem B4269293 : Blo 1264450 4269293 := bstep (se 3 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 4269293 = 1600985) B1600985
theorem B5776625 : Blo 1264450 5776625 := bstep (se 2 (by rfl) ⟨2166234, by rfl⟩ : syracuseStep 5776625 = 4332469) B4332469
theorem B4269347 : Blo 1264450 4269347 := bstep (se 1 (by rfl) ⟨3202010, by rfl⟩ : syracuseStep 4269347 = 6404021) B6404021
theorem B1951025 : Blo 1264450 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B1852723 : Blo 1264450 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B8111501 : Blo 1264450 8111501 := bstep (se 3 (by rfl) ⟨1520906, by rfl⟩ : syracuseStep 8111501 = 3041813) B3041813
theorem B7210403 : Blo 1264450 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B4056493 : Blo 1264450 4056493 := bstep (se 3 (by rfl) ⟨760592, by rfl⟩ : syracuseStep 4056493 = 1521185) B1521185
theorem B3081649 : Blo 1264450 3081649 := bstep (se 2 (by rfl) ⟨1155618, by rfl⟩ : syracuseStep 3081649 = 2311237) B2311237
theorem B5768653 : Blo 1264450 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B8660429 : Blo 1264450 8660429 := bstep (se 3 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 8660429 = 3247661) B3247661
theorem B3204593 : Blo 1264450 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B4326929 : Blo 1264450 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B3204643 : Blo 1264450 3204643 := bstep (se 1 (by rfl) ⟨2403482, by rfl⟩ : syracuseStep 3204643 = 4806965) B4806965
theorem B4269617 : Blo 1264450 4269617 := bstep (se 2 (by rfl) ⟨1601106, by rfl⟩ : syracuseStep 4269617 = 3202213) B3202213
theorem B3204785 : Blo 1264450 3204785 := bstep (se 2 (by rfl) ⟨1201794, by rfl⟩ : syracuseStep 3204785 = 2403589) B2403589
theorem B2401987 : Blo 1264450 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B3606353 : Blo 1264450 3606353 := bstep (se 2 (by rfl) ⟨1352382, by rfl⟩ : syracuseStep 3606353 = 2704765) B2704765
theorem B2279299 : Blo 1264450 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B3417997 : Blo 1264450 3417997 := bstep (se 3 (by rfl) ⟨640874, by rfl⟩ : syracuseStep 3417997 = 1281749) B1281749
theorem B9119729 : Blo 1264450 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B4270157 : Blo 1264450 4270157 := bstep (se 3 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 4270157 = 1601309) B1601309
theorem B2025569 : Blo 1264450 2025569 := bstep (se 2 (by rfl) ⟨759588, by rfl⟩ : syracuseStep 2025569 = 1519177) B1519177
theorem B3418211 : Blo 1264450 3418211 := bstep (se 1 (by rfl) ⟨2563658, by rfl⟩ : syracuseStep 3418211 = 5127317) B5127317
theorem B4270211 : Blo 1264450 4270211 := bstep (se 1 (by rfl) ⟨3202658, by rfl⟩ : syracuseStep 4270211 = 6405317) B6405317
theorem B2402435 : Blo 1264450 2402435 := bstep (se 1 (by rfl) ⟨1801826, by rfl⟩ : syracuseStep 2402435 = 3603653) B3603653
theorem B12159173 : Blo 1264450 12159173 := bstep (se 4 (by rfl) ⟨1139922, by rfl⟩ : syracuseStep 12159173 = 2279845) B2279845
theorem B11708657 : Blo 1264450 11708657 := bstep (se 2 (by rfl) ⟨4390746, by rfl⟩ : syracuseStep 11708657 = 8781493) B8781493
theorem B4868365 : Blo 1264450 4868365 := bstep (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) B1825637
theorem B2885905 : Blo 1264450 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B2566513 : Blo 1264450 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B2025857 : Blo 1264450 2025857 := bstep (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) B1519393
theorem B4270481 : Blo 1264450 4270481 := bstep (se 2 (by rfl) ⟨1601430, by rfl⟩ : syracuseStep 4270481 = 3202861) B3202861
theorem B2402723 : Blo 1264450 2402723 := bstep (se 1 (by rfl) ⟨1802042, by rfl⟩ : syracuseStep 2402723 = 3604085) B3604085
theorem B30771683 : Blo 1264450 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B4868579 : Blo 1264450 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B2845169 : Blo 1264450 2845169 := bstep (se 2 (by rfl) ⟨1066938, by rfl⟩ : syracuseStep 2845169 = 2133877) B2133877
theorem B2845187 : Blo 1264450 2845187 := bstep (se 1 (by rfl) ⟨2133890, by rfl⟩ : syracuseStep 2845187 = 4267781) B4267781
theorem B15608389 : Blo 1264450 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B2026081 : Blo 1264450 2026081 := bstep (se 2 (by rfl) ⟨759780, by rfl⟩ : syracuseStep 2026081 = 1519561) B1519561
theorem B5409443 : Blo 1264450 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B6408881 : Blo 1264450 6408881 := bstep (se 2 (by rfl) ⟨2403330, by rfl⟩ : syracuseStep 6408881 = 4806661) B4806661
theorem B2845457 : Blo 1264450 2845457 := bstep (se 2 (by rfl) ⟨1067046, by rfl⟩ : syracuseStep 2845457 = 2134093) B2134093
theorem B2845475 : Blo 1264450 2845475 := bstep (se 1 (by rfl) ⟨2134106, by rfl⟩ : syracuseStep 2845475 = 4268213) B4268213
theorem B2566961 : Blo 1264450 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B1264451 : Blo 1264450 1264451 := bstep (se 1 (by rfl) ⟨948338, by rfl⟩ : syracuseStep 1264451 = 1896677) B1896677
theorem B1264467 : Blo 1264450 1264467 := bstep (se 1 (by rfl) ⟨948350, by rfl⟩ : syracuseStep 1264467 = 1896701) B1896701
theorem B1264483 : Blo 1264450 1264483 := bstep (se 1 (by rfl) ⟨948362, by rfl⟩ : syracuseStep 1264483 = 1896725) B1896725
theorem B10816355 : Blo 1264450 10816355 := bstep (se 1 (by rfl) ⟨8112266, by rfl⟩ : syracuseStep 10816355 = 16224533) B16224533
theorem B21900145 : Blo 1264450 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B1264499 : Blo 1264450 1264499 := bstep (se 1 (by rfl) ⟨948374, by rfl⟩ : syracuseStep 1264499 = 1896749) B1896749
theorem B1264515 : Blo 1264450 1264515 := bstep (se 1 (by rfl) ⟨948386, by rfl⟩ : syracuseStep 1264515 = 1896773) B1896773
theorem B1264531 : Blo 1264450 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B1264547 : Blo 1264450 1264547 := bstep (se 1 (by rfl) ⟨948410, by rfl⟩ : syracuseStep 1264547 = 1896821) B1896821
theorem B4271021 : Blo 1264450 4271021 := bstep (se 3 (by rfl) ⟨800816, by rfl⟩ : syracuseStep 4271021 = 1601633) B1601633
theorem B1264563 : Blo 1264450 1264563 := bstep (se 1 (by rfl) ⟨948422, by rfl⟩ : syracuseStep 1264563 = 1896845) B1896845
theorem B1264579 : Blo 1264450 1264579 := bstep (se 1 (by rfl) ⟨948434, by rfl⟩ : syracuseStep 1264579 = 1896869) B1896869
theorem B4803533 : Blo 1264450 4803533 := bstep (se 3 (by rfl) ⟨900662, by rfl⟩ : syracuseStep 4803533 = 1801325) B1801325
theorem B1264595 : Blo 1264450 1264595 := bstep (se 1 (by rfl) ⟨948446, by rfl⟩ : syracuseStep 1264595 = 1896893) B1896893
theorem B1264611 : Blo 1264450 1264611 := bstep (se 1 (by rfl) ⟨948458, by rfl⟩ : syracuseStep 1264611 = 1896917) B1896917
theorem B4271075 : Blo 1264450 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B17542129 : Blo 1264450 17542129 := bstep (se 2 (by rfl) ⟨6578298, by rfl⟩ : syracuseStep 17542129 = 13156597) B13156597
theorem B1600499 : Blo 1264450 1600499 := bstep (se 1 (by rfl) ⟨1200374, by rfl⟩ : syracuseStep 1600499 = 2400749) B2400749
theorem B1264627 : Blo 1264450 1264627 := bstep (se 1 (by rfl) ⟨948470, by rfl⟩ : syracuseStep 1264627 = 1896941) B1896941
theorem B1264643 : Blo 1264450 1264643 := bstep (se 1 (by rfl) ⟨948482, by rfl⟩ : syracuseStep 1264643 = 1896965) B1896965
theorem B3419153 : Blo 1264450 3419153 := bstep (se 2 (by rfl) ⟨1282182, by rfl⟩ : syracuseStep 3419153 = 2564365) B2564365
theorem B1264659 : Blo 1264450 1264659 := bstep (se 1 (by rfl) ⟨948494, by rfl⟩ : syracuseStep 1264659 = 1896989) B1896989
theorem B1264675 : Blo 1264450 1264675 := bstep (se 1 (by rfl) ⟨948506, by rfl⟩ : syracuseStep 1264675 = 1897013) B1897013
theorem B2845745 : Blo 1264450 2845745 := bstep (se 2 (by rfl) ⟨1067154, by rfl⟩ : syracuseStep 2845745 = 2134309) B2134309
theorem B1264691 : Blo 1264450 1264691 := bstep (se 1 (by rfl) ⟨948518, by rfl⟩ : syracuseStep 1264691 = 1897037) B1897037
theorem B1264707 : Blo 1264450 1264707 := bstep (se 1 (by rfl) ⟨948530, by rfl⟩ : syracuseStep 1264707 = 1897061) B1897061
theorem B2845763 : Blo 1264450 2845763 := bstep (se 1 (by rfl) ⟨2134322, by rfl⟩ : syracuseStep 2845763 = 4268645) B4268645
theorem B1264723 : Blo 1264450 1264723 := bstep (se 1 (by rfl) ⟨948542, by rfl⟩ : syracuseStep 1264723 = 1897085) B1897085
theorem B1264739 : Blo 1264450 1264739 := bstep (se 1 (by rfl) ⟨948554, by rfl⟩ : syracuseStep 1264739 = 1897109) B1897109
theorem B1264755 : Blo 1264450 1264755 := bstep (se 1 (by rfl) ⟨948566, by rfl⟩ : syracuseStep 1264755 = 1897133) B1897133
theorem B1264771 : Blo 1264450 1264771 := bstep (se 1 (by rfl) ⟨948578, by rfl⟩ : syracuseStep 1264771 = 1897157) B1897157
theorem B1264787 : Blo 1264450 1264787 := bstep (se 1 (by rfl) ⟨948590, by rfl⟩ : syracuseStep 1264787 = 1897181) B1897181
theorem B1264803 : Blo 1264450 1264803 := bstep (se 1 (by rfl) ⟨948602, by rfl⟩ : syracuseStep 1264803 = 1897205) B1897205
theorem B2280611 : Blo 1264450 2280611 := bstep (se 1 (by rfl) ⟨1710458, by rfl⟩ : syracuseStep 2280611 = 3420917) B3420917
theorem B1264819 : Blo 1264450 1264819 := bstep (se 1 (by rfl) ⟨948614, by rfl⟩ : syracuseStep 1264819 = 1897229) B1897229
theorem B1264835 : Blo 1264450 1264835 := bstep (se 1 (by rfl) ⟨948626, by rfl⟩ : syracuseStep 1264835 = 1897253) B1897253
theorem B3255491 : Blo 1264450 3255491 := bstep (se 1 (by rfl) ⟨2441618, by rfl⟩ : syracuseStep 3255491 = 4883237) B4883237
theorem B1264851 : Blo 1264450 1264851 := bstep (se 1 (by rfl) ⟨948638, by rfl⟩ : syracuseStep 1264851 = 1897277) B1897277
theorem B1264867 : Blo 1264450 1264867 := bstep (se 1 (by rfl) ⟨948650, by rfl⟩ : syracuseStep 1264867 = 1897301) B1897301
theorem B4271345 : Blo 1264450 4271345 := bstep (se 2 (by rfl) ⟨1601754, by rfl⟩ : syracuseStep 4271345 = 3203509) B3203509
theorem B1264883 : Blo 1264450 1264883 := bstep (se 1 (by rfl) ⟨948662, by rfl⟩ : syracuseStep 1264883 = 1897325) B1897325
theorem B1264899 : Blo 1264450 1264899 := bstep (se 1 (by rfl) ⟨948674, by rfl⟩ : syracuseStep 1264899 = 1897349) B1897349
theorem B1264915 : Blo 1264450 1264915 := bstep (se 1 (by rfl) ⟨948686, by rfl⟩ : syracuseStep 1264915 = 1897373) B1897373
theorem B1264931 : Blo 1264450 1264931 := bstep (se 1 (by rfl) ⟨948698, by rfl⟩ : syracuseStep 1264931 = 1897397) B1897397
theorem B1264947 : Blo 1264450 1264947 := bstep (se 1 (by rfl) ⟨948710, by rfl⟩ : syracuseStep 1264947 = 1897421) B1897421
theorem B1264963 : Blo 1264450 1264963 := bstep (se 1 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 1264963 = 1897445) B1897445
theorem B2846033 : Blo 1264450 2846033 := bstep (se 2 (by rfl) ⟨1067262, by rfl⟩ : syracuseStep 2846033 = 2134525) B2134525
theorem B2403665 : Blo 1264450 2403665 := bstep (se 2 (by rfl) ⟨901374, by rfl⟩ : syracuseStep 2403665 = 1802749) B1802749
theorem B1264979 : Blo 1264450 1264979 := bstep (se 1 (by rfl) ⟨948734, by rfl⟩ : syracuseStep 1264979 = 1897469) B1897469
theorem B2846051 : Blo 1264450 2846051 := bstep (se 1 (by rfl) ⟨2134538, by rfl⟩ : syracuseStep 2846051 = 4269077) B4269077
theorem B1264995 : Blo 1264450 1264995 := bstep (se 1 (by rfl) ⟨948746, by rfl⟩ : syracuseStep 1264995 = 1897493) B1897493
theorem B3042659 : Blo 1264450 3042659 := bstep (se 1 (by rfl) ⟨2281994, by rfl⟩ : syracuseStep 3042659 = 4563989) B4563989
theorem B34614641 : Blo 1264450 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B1265011 : Blo 1264450 1265011 := bstep (se 1 (by rfl) ⟨948758, by rfl⟩ : syracuseStep 1265011 = 1897517) B1897517
theorem B1265027 : Blo 1264450 1265027 := bstep (se 1 (by rfl) ⟨948770, by rfl⟩ : syracuseStep 1265027 = 1897541) B1897541
theorem B1265043 : Blo 1264450 1265043 := bstep (se 1 (by rfl) ⟨948782, by rfl⟩ : syracuseStep 1265043 = 1897565) B1897565
theorem B1265059 : Blo 1264450 1265059 := bstep (se 1 (by rfl) ⟨948794, by rfl⟩ : syracuseStep 1265059 = 1897589) B1897589
theorem B1265075 : Blo 1264450 1265075 := bstep (se 1 (by rfl) ⟨948806, by rfl⟩ : syracuseStep 1265075 = 1897613) B1897613
theorem B1265091 : Blo 1264450 1265091 := bstep (se 1 (by rfl) ⟨948818, by rfl⟩ : syracuseStep 1265091 = 1897637) B1897637
theorem B2280899 : Blo 1264450 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B3042755 : Blo 1264450 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B1265107 : Blo 1264450 1265107 := bstep (se 1 (by rfl) ⟨948830, by rfl⟩ : syracuseStep 1265107 = 1897661) B1897661
theorem B1265123 : Blo 1264450 1265123 := bstep (se 1 (by rfl) ⟨948842, by rfl⟩ : syracuseStep 1265123 = 1897685) B1897685
theorem B1265139 : Blo 1264450 1265139 := bstep (se 1 (by rfl) ⟨948854, by rfl⟩ : syracuseStep 1265139 = 1897709) B1897709
theorem B1265155 : Blo 1264450 1265155 := bstep (se 1 (by rfl) ⟨948866, by rfl⟩ : syracuseStep 1265155 = 1897733) B1897733
theorem B1265171 : Blo 1264450 1265171 := bstep (se 1 (by rfl) ⟨948878, by rfl⟩ : syracuseStep 1265171 = 1897757) B1897757
theorem B1265187 : Blo 1264450 1265187 := bstep (se 1 (by rfl) ⟨948890, by rfl⟩ : syracuseStep 1265187 = 1897781) B1897781
theorem B1265203 : Blo 1264450 1265203 := bstep (se 1 (by rfl) ⟨948902, by rfl⟩ : syracuseStep 1265203 = 1897805) B1897805
theorem B1265219 : Blo 1264450 1265219 := bstep (se 1 (by rfl) ⟨948914, by rfl⟩ : syracuseStep 1265219 = 1897829) B1897829
theorem B1265235 : Blo 1264450 1265235 := bstep (se 1 (by rfl) ⟨948926, by rfl⟩ : syracuseStep 1265235 = 1897853) B1897853
theorem B13676131 : Blo 1264450 13676131 := bstep (se 1 (by rfl) ⟨10257098, by rfl⟩ : syracuseStep 13676131 = 20514197) B20514197
theorem B1265251 : Blo 1264450 1265251 := bstep (se 1 (by rfl) ⟨948938, by rfl⟩ : syracuseStep 1265251 = 1897877) B1897877
theorem B2846321 : Blo 1264450 2846321 := bstep (se 2 (by rfl) ⟨1067370, by rfl⟩ : syracuseStep 2846321 = 2134741) B2134741
theorem B1265267 : Blo 1264450 1265267 := bstep (se 1 (by rfl) ⟨948950, by rfl⟩ : syracuseStep 1265267 = 1897901) B1897901
theorem B2846339 : Blo 1264450 2846339 := bstep (se 1 (by rfl) ⟨2134754, by rfl⟩ : syracuseStep 2846339 = 4269509) B4269509
theorem B1265283 : Blo 1264450 1265283 := bstep (se 1 (by rfl) ⟨948962, by rfl⟩ : syracuseStep 1265283 = 1897925) B1897925
theorem B2600579 : Blo 1264450 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B1265299 : Blo 1264450 1265299 := bstep (se 1 (by rfl) ⟨948974, by rfl⟩ : syracuseStep 1265299 = 1897949) B1897949
theorem B1265315 : Blo 1264450 1265315 := bstep (se 1 (by rfl) ⟨948986, by rfl⟩ : syracuseStep 1265315 = 1897973) B1897973
theorem B1601203 : Blo 1264450 1601203 := bstep (se 1 (by rfl) ⟨1200902, by rfl⟩ : syracuseStep 1601203 = 2401805) B2401805
theorem B1265331 : Blo 1264450 1265331 := bstep (se 1 (by rfl) ⟨948998, by rfl⟩ : syracuseStep 1265331 = 1897997) B1897997
theorem B1265347 : Blo 1264450 1265347 := bstep (se 1 (by rfl) ⟨949010, by rfl⟩ : syracuseStep 1265347 = 1898021) B1898021
theorem B1265363 : Blo 1264450 1265363 := bstep (se 1 (by rfl) ⟨949022, by rfl⟩ : syracuseStep 1265363 = 1898045) B1898045
theorem B1265379 : Blo 1264450 1265379 := bstep (se 1 (by rfl) ⟨949034, by rfl⟩ : syracuseStep 1265379 = 1898069) B1898069
theorem B1265395 : Blo 1264450 1265395 := bstep (se 1 (by rfl) ⟨949046, by rfl⟩ : syracuseStep 1265395 = 1898093) B1898093
theorem B1265411 : Blo 1264450 1265411 := bstep (se 1 (by rfl) ⟨949058, by rfl⟩ : syracuseStep 1265411 = 1898117) B1898117
theorem B4271885 : Blo 1264450 4271885 := bstep (se 3 (by rfl) ⟨800978, by rfl⟩ : syracuseStep 4271885 = 1601957) B1601957
theorem B1601299 : Blo 1264450 1601299 := bstep (se 1 (by rfl) ⟨1200974, by rfl⟩ : syracuseStep 1601299 = 2401949) B2401949
theorem B1265427 : Blo 1264450 1265427 := bstep (se 1 (by rfl) ⟨949070, by rfl⟩ : syracuseStep 1265427 = 1898141) B1898141
theorem B1265443 : Blo 1264450 1265443 := bstep (se 1 (by rfl) ⟨949082, by rfl⟩ : syracuseStep 1265443 = 1898165) B1898165
theorem B1265459 : Blo 1264450 1265459 := bstep (se 1 (by rfl) ⟨949094, by rfl⟩ : syracuseStep 1265459 = 1898189) B1898189
theorem B1265475 : Blo 1264450 1265475 := bstep (se 1 (by rfl) ⟨949106, by rfl⟩ : syracuseStep 1265475 = 1898213) B1898213
theorem B4271939 : Blo 1264450 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B1265491 : Blo 1264450 1265491 := bstep (se 1 (by rfl) ⟨949118, by rfl⟩ : syracuseStep 1265491 = 1898237) B1898237
theorem B2133857 : Blo 1264450 2133857 := bstep (se 2 (by rfl) ⟨800196, by rfl⟩ : syracuseStep 2133857 = 1600393) B1600393
theorem B1265507 : Blo 1264450 1265507 := bstep (se 1 (by rfl) ⟨949130, by rfl⟩ : syracuseStep 1265507 = 1898261) B1898261
theorem B1265523 : Blo 1264450 1265523 := bstep (se 1 (by rfl) ⟨949142, by rfl⟩ : syracuseStep 1265523 = 1898285) B1898285
theorem B1265539 : Blo 1264450 1265539 := bstep (se 1 (by rfl) ⟨949154, by rfl⟩ : syracuseStep 1265539 = 1898309) B1898309
theorem B2846609 : Blo 1264450 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B1265555 : Blo 1264450 1265555 := bstep (se 1 (by rfl) ⟨949166, by rfl⟩ : syracuseStep 1265555 = 1898333) B1898333
theorem B2846627 : Blo 1264450 2846627 := bstep (se 1 (by rfl) ⟨2134970, by rfl⟩ : syracuseStep 2846627 = 4269941) B4269941
theorem B1265571 : Blo 1264450 1265571 := bstep (se 1 (by rfl) ⟨949178, by rfl⟩ : syracuseStep 1265571 = 1898357) B1898357
theorem B1265587 : Blo 1264450 1265587 := bstep (se 1 (by rfl) ⟨949190, by rfl⟩ : syracuseStep 1265587 = 1898381) B1898381
theorem B1265603 : Blo 1264450 1265603 := bstep (se 1 (by rfl) ⟨949202, by rfl⟩ : syracuseStep 1265603 = 1898405) B1898405
theorem B1265619 : Blo 1264450 1265619 := bstep (se 1 (by rfl) ⟨949214, by rfl⟩ : syracuseStep 1265619 = 1898429) B1898429
theorem B2133985 : Blo 1264450 2133985 := bstep (se 2 (by rfl) ⟨800244, by rfl⟩ : syracuseStep 2133985 = 1600489) B1600489
theorem B1265635 : Blo 1264450 1265635 := bstep (se 1 (by rfl) ⟨949226, by rfl⟩ : syracuseStep 1265635 = 1898453) B1898453
theorem B5402609 : Blo 1264450 5402609 := bstep (se 2 (by rfl) ⟨2025978, by rfl⟩ : syracuseStep 5402609 = 4051957) B4051957
theorem B1265651 : Blo 1264450 1265651 := bstep (se 1 (by rfl) ⟨949238, by rfl⟩ : syracuseStep 1265651 = 1898477) B1898477
theorem B2134019 : Blo 1264450 2134019 := bstep (se 1 (by rfl) ⟨1600514, by rfl⟩ : syracuseStep 2134019 = 3201029) B3201029
theorem B1265667 : Blo 1264450 1265667 := bstep (se 1 (by rfl) ⟨949250, by rfl⟩ : syracuseStep 1265667 = 1898501) B1898501
theorem B1265683 : Blo 1264450 1265683 := bstep (se 1 (by rfl) ⟨949262, by rfl⟩ : syracuseStep 1265683 = 1898525) B1898525
theorem B1265699 : Blo 1264450 1265699 := bstep (se 1 (by rfl) ⟨949274, by rfl⟩ : syracuseStep 1265699 = 1898549) B1898549
theorem B1265715 : Blo 1264450 1265715 := bstep (se 1 (by rfl) ⟨949286, by rfl⟩ : syracuseStep 1265715 = 1898573) B1898573
theorem B1265731 : Blo 1264450 1265731 := bstep (se 1 (by rfl) ⟨949298, by rfl⟩ : syracuseStep 1265731 = 1898597) B1898597
theorem B4272209 : Blo 1264450 4272209 := bstep (se 2 (by rfl) ⟨1602078, by rfl⟩ : syracuseStep 4272209 = 3204157) B3204157
theorem B1265747 : Blo 1264450 1265747 := bstep (se 1 (by rfl) ⟨949310, by rfl⟩ : syracuseStep 1265747 = 1898621) B1898621
theorem B1265763 : Blo 1264450 1265763 := bstep (se 1 (by rfl) ⟨949322, by rfl⟩ : syracuseStep 1265763 = 1898645) B1898645
theorem B6410339 : Blo 1264450 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B1265779 : Blo 1264450 1265779 := bstep (se 1 (by rfl) ⟨949334, by rfl⟩ : syracuseStep 1265779 = 1898669) B1898669
theorem B2134147 : Blo 1264450 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B1265795 : Blo 1264450 1265795 := bstep (se 1 (by rfl) ⟨949346, by rfl⟩ : syracuseStep 1265795 = 1898693) B1898693
theorem B1265811 : Blo 1264450 1265811 := bstep (se 1 (by rfl) ⟨949358, by rfl⟩ : syracuseStep 1265811 = 1898717) B1898717
theorem B1265827 : Blo 1264450 1265827 := bstep (se 1 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 1265827 = 1898741) B1898741
theorem B2027683 : Blo 1264450 2027683 := bstep (se 1 (by rfl) ⟨1520762, by rfl⟩ : syracuseStep 2027683 = 3041525) B3041525
theorem B2846897 : Blo 1264450 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B1265843 : Blo 1264450 1265843 := bstep (se 1 (by rfl) ⟨949382, by rfl⟩ : syracuseStep 1265843 = 1898765) B1898765
theorem B2846915 : Blo 1264450 2846915 := bstep (se 1 (by rfl) ⟨2135186, by rfl⟩ : syracuseStep 2846915 = 4270373) B4270373
theorem B1265859 : Blo 1264450 1265859 := bstep (se 1 (by rfl) ⟨949394, by rfl⟩ : syracuseStep 1265859 = 1898789) B1898789
theorem B1265875 : Blo 1264450 1265875 := bstep (se 1 (by rfl) ⟨949406, by rfl⟩ : syracuseStep 1265875 = 1898813) B1898813
theorem B77918435 : Blo 1264450 77918435 := bstep (se 1 (by rfl) ⟨58438826, by rfl⟩ : syracuseStep 77918435 = 116877653) B116877653
theorem B1265891 : Blo 1264450 1265891 := bstep (se 1 (by rfl) ⟨949418, by rfl⟩ : syracuseStep 1265891 = 1898837) B1898837
theorem B1896689 : Blo 1264450 1896689 := bstep (se 2 (by rfl) ⟨711258, by rfl⟩ : syracuseStep 1896689 = 1422517) B1422517
theorem B1265907 : Blo 1264450 1265907 := bstep (se 1 (by rfl) ⟨949430, by rfl⟩ : syracuseStep 1265907 = 1898861) B1898861
theorem B1896707 : Blo 1264450 1896707 := bstep (se 1 (by rfl) ⟨1422530, by rfl⟩ : syracuseStep 1896707 = 2845061) B2845061
theorem B1601795 : Blo 1264450 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B1265923 : Blo 1264450 1265923 := bstep (se 1 (by rfl) ⟨949442, by rfl⟩ : syracuseStep 1265923 = 1898885) B1898885
theorem B2134289 : Blo 1264450 2134289 := bstep (se 2 (by rfl) ⟨800358, by rfl⟩ : syracuseStep 2134289 = 1600717) B1600717
theorem B1265939 : Blo 1264450 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B1896737 : Blo 1264450 1896737 := bstep (se 2 (by rfl) ⟨711276, by rfl⟩ : syracuseStep 1896737 = 1422553) B1422553
theorem B1265955 : Blo 1264450 1265955 := bstep (se 1 (by rfl) ⟨949466, by rfl⟩ : syracuseStep 1265955 = 1898933) B1898933
theorem B1896755 : Blo 1264450 1896755 := bstep (se 1 (by rfl) ⟨1422566, by rfl⟩ : syracuseStep 1896755 = 2845133) B2845133
theorem B1265971 : Blo 1264450 1265971 := bstep (se 1 (by rfl) ⟨949478, by rfl⟩ : syracuseStep 1265971 = 1898957) B1898957
theorem B1462595 : Blo 1264450 1462595 := bstep (se 1 (by rfl) ⟨1096946, by rfl⟩ : syracuseStep 1462595 = 2193893) B2193893
theorem B1265987 : Blo 1264450 1265987 := bstep (se 1 (by rfl) ⟨949490, by rfl⟩ : syracuseStep 1265987 = 1898981) B1898981
theorem B1896785 : Blo 1264450 1896785 := bstep (se 2 (by rfl) ⟨711294, by rfl⟩ : syracuseStep 1896785 = 1422589) B1422589
theorem B1266003 : Blo 1264450 1266003 := bstep (se 1 (by rfl) ⟨949502, by rfl⟩ : syracuseStep 1266003 = 1899005) B1899005
theorem B1896803 : Blo 1264450 1896803 := bstep (se 1 (by rfl) ⟨1422602, by rfl⟩ : syracuseStep 1896803 = 2845205) B2845205
theorem B1732963 : Blo 1264450 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B1266019 : Blo 1264450 1266019 := bstep (se 1 (by rfl) ⟨949514, by rfl⟩ : syracuseStep 1266019 = 1899029) B1899029
theorem B1266035 : Blo 1264450 1266035 := bstep (se 1 (by rfl) ⟨949526, by rfl⟩ : syracuseStep 1266035 = 1899053) B1899053
theorem B1896833 : Blo 1264450 1896833 := bstep (se 2 (by rfl) ⟨711312, by rfl⟩ : syracuseStep 1896833 = 1422625) B1422625
theorem B1266051 : Blo 1264450 1266051 := bstep (se 1 (by rfl) ⟨949538, by rfl⟩ : syracuseStep 1266051 = 1899077) B1899077
theorem B2134417 : Blo 1264450 2134417 := bstep (se 2 (by rfl) ⟨800406, by rfl⟩ : syracuseStep 2134417 = 1600813) B1600813
theorem B1896851 : Blo 1264450 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B1266067 : Blo 1264450 1266067 := bstep (se 1 (by rfl) ⟨949550, by rfl⟩ : syracuseStep 1266067 = 1899101) B1899101
theorem B1266083 : Blo 1264450 1266083 := bstep (se 1 (by rfl) ⟨949562, by rfl⟩ : syracuseStep 1266083 = 1899125) B1899125
theorem B1896881 : Blo 1264450 1896881 := bstep (se 2 (by rfl) ⟨711330, by rfl⟩ : syracuseStep 1896881 = 1422661) B1422661
theorem B2134451 : Blo 1264450 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B1266099 : Blo 1264450 1266099 := bstep (se 1 (by rfl) ⟨949574, by rfl⟩ : syracuseStep 1266099 = 1899149) B1899149
theorem B1896899 : Blo 1264450 1896899 := bstep (se 1 (by rfl) ⟨1422674, by rfl⟩ : syracuseStep 1896899 = 2845349) B2845349
theorem B1266115 : Blo 1264450 1266115 := bstep (se 1 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 1266115 = 1899173) B1899173
theorem B2888131 : Blo 1264450 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B2847185 : Blo 1264450 2847185 := bstep (se 2 (by rfl) ⟨1067694, by rfl⟩ : syracuseStep 2847185 = 2135389) B2135389
theorem B1266131 : Blo 1264450 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B1896929 : Blo 1264450 1896929 := bstep (se 2 (by rfl) ⟨711348, by rfl⟩ : syracuseStep 1896929 = 1422697) B1422697
theorem B4108771 : Blo 1264450 4108771 := bstep (se 1 (by rfl) ⟨3081578, by rfl⟩ : syracuseStep 4108771 = 6163157) B6163157
theorem B2847203 : Blo 1264450 2847203 := bstep (se 1 (by rfl) ⟨2135402, by rfl⟩ : syracuseStep 2847203 = 4270805) B4270805
theorem B1266147 : Blo 1264450 1266147 := bstep (se 1 (by rfl) ⟨949610, by rfl⟩ : syracuseStep 1266147 = 1899221) B1899221
theorem B4559345 : Blo 1264450 4559345 := bstep (se 2 (by rfl) ⟨1709754, by rfl⟩ : syracuseStep 4559345 = 3419509) B3419509
theorem B1896947 : Blo 1264450 1896947 := bstep (se 1 (by rfl) ⟨1422710, by rfl⟩ : syracuseStep 1896947 = 2845421) B2845421
theorem B1266163 : Blo 1264450 1266163 := bstep (se 1 (by rfl) ⟨949622, by rfl⟩ : syracuseStep 1266163 = 1899245) B1899245
theorem B1266179 : Blo 1264450 1266179 := bstep (se 1 (by rfl) ⟨949634, by rfl⟩ : syracuseStep 1266179 = 1899269) B1899269
theorem B1896977 : Blo 1264450 1896977 := bstep (se 2 (by rfl) ⟨711366, by rfl⟩ : syracuseStep 1896977 = 1422733) B1422733
theorem B3248657 : Blo 1264450 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B1266195 : Blo 1264450 1266195 := bstep (se 1 (by rfl) ⟨949646, by rfl⟩ : syracuseStep 1266195 = 1899293) B1899293
theorem B1896995 : Blo 1264450 1896995 := bstep (se 1 (by rfl) ⟨1422746, by rfl⟩ : syracuseStep 1896995 = 2845493) B2845493
theorem B1266211 : Blo 1264450 1266211 := bstep (se 1 (by rfl) ⟨949658, by rfl⟩ : syracuseStep 1266211 = 1899317) B1899317
theorem B2134579 : Blo 1264450 2134579 := bstep (se 1 (by rfl) ⟨1600934, by rfl⟩ : syracuseStep 2134579 = 3201869) B3201869
theorem B1266227 : Blo 1264450 1266227 := bstep (se 1 (by rfl) ⟨949670, by rfl⟩ : syracuseStep 1266227 = 1899341) B1899341
theorem B1897025 : Blo 1264450 1897025 := bstep (se 2 (by rfl) ⟨711384, by rfl⟩ : syracuseStep 1897025 = 1422769) B1422769
theorem B1266243 : Blo 1264450 1266243 := bstep (se 1 (by rfl) ⟨949682, by rfl⟩ : syracuseStep 1266243 = 1899365) B1899365
theorem B1897043 : Blo 1264450 1897043 := bstep (se 1 (by rfl) ⟨1422782, by rfl⟩ : syracuseStep 1897043 = 2845565) B2845565
theorem B1266259 : Blo 1264450 1266259 := bstep (se 1 (by rfl) ⟨949694, by rfl⟩ : syracuseStep 1266259 = 1899389) B1899389
theorem B1389155 : Blo 1264450 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B1266275 : Blo 1264450 1266275 := bstep (se 1 (by rfl) ⟨949706, by rfl⟩ : syracuseStep 1266275 = 1899413) B1899413
theorem B4272749 : Blo 1264450 4272749 := bstep (se 3 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 4272749 = 1602281) B1602281
theorem B1897073 : Blo 1264450 1897073 := bstep (se 2 (by rfl) ⟨711402, by rfl⟩ : syracuseStep 1897073 = 1422805) B1422805
theorem B1266291 : Blo 1264450 1266291 := bstep (se 1 (by rfl) ⟨949718, by rfl⟩ : syracuseStep 1266291 = 1899437) B1899437
theorem B1897091 : Blo 1264450 1897091 := bstep (se 1 (by rfl) ⟨1422818, by rfl⟩ : syracuseStep 1897091 = 2845637) B2845637
theorem B1266307 : Blo 1264450 1266307 := bstep (se 1 (by rfl) ⟨949730, by rfl⟩ : syracuseStep 1266307 = 1899461) B1899461
theorem B1266323 : Blo 1264450 1266323 := bstep (se 1 (by rfl) ⟨949742, by rfl⟩ : syracuseStep 1266323 = 1899485) B1899485
theorem B1897121 : Blo 1264450 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B4272803 : Blo 1264450 4272803 := bstep (se 1 (by rfl) ⟨3204602, by rfl⟩ : syracuseStep 4272803 = 6409205) B6409205
theorem B1266339 : Blo 1264450 1266339 := bstep (se 1 (by rfl) ⟨949754, by rfl⟩ : syracuseStep 1266339 = 1899509) B1899509
theorem B1897139 : Blo 1264450 1897139 := bstep (se 1 (by rfl) ⟨1422854, by rfl⟩ : syracuseStep 1897139 = 2845709) B2845709
theorem B1266355 : Blo 1264450 1266355 := bstep (se 1 (by rfl) ⟨949766, by rfl⟩ : syracuseStep 1266355 = 1899533) B1899533
theorem B2134721 : Blo 1264450 2134721 := bstep (se 2 (by rfl) ⟨800520, by rfl⟩ : syracuseStep 2134721 = 1601041) B1601041
theorem B1266371 : Blo 1264450 1266371 := bstep (se 1 (by rfl) ⟨949778, by rfl⟩ : syracuseStep 1266371 = 1899557) B1899557
theorem B1897169 : Blo 1264450 1897169 := bstep (se 2 (by rfl) ⟨711438, by rfl⟩ : syracuseStep 1897169 = 1422877) B1422877
theorem B1266387 : Blo 1264450 1266387 := bstep (se 1 (by rfl) ⟨949790, by rfl⟩ : syracuseStep 1266387 = 1899581) B1899581
theorem B1897187 : Blo 1264450 1897187 := bstep (se 1 (by rfl) ⟨1422890, by rfl⟩ : syracuseStep 1897187 = 2845781) B2845781
theorem B9614051 : Blo 1264450 9614051 := bstep (se 1 (by rfl) ⟨7210538, by rfl⟩ : syracuseStep 9614051 = 14421077) B14421077
theorem B1266403 : Blo 1264450 1266403 := bstep (se 1 (by rfl) ⟨949802, by rfl⟩ : syracuseStep 1266403 = 1899605) B1899605
theorem B2847473 : Blo 1264450 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1266419 : Blo 1264450 1266419 := bstep (se 1 (by rfl) ⟨949814, by rfl⟩ : syracuseStep 1266419 = 1899629) B1899629
theorem B1897217 : Blo 1264450 1897217 := bstep (se 2 (by rfl) ⟨711456, by rfl⟩ : syracuseStep 1897217 = 1422913) B1422913
theorem B2847491 : Blo 1264450 2847491 := bstep (se 1 (by rfl) ⟨2135618, by rfl⟩ : syracuseStep 2847491 = 4271237) B4271237
theorem B1266435 : Blo 1264450 1266435 := bstep (se 1 (by rfl) ⟨949826, by rfl⟩ : syracuseStep 1266435 = 1899653) B1899653
theorem B3601169 : Blo 1264450 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B1897235 : Blo 1264450 1897235 := bstep (se 1 (by rfl) ⟨1422926, by rfl⟩ : syracuseStep 1897235 = 2845853) B2845853
theorem B1282835 : Blo 1264450 1282835 := bstep (se 1 (by rfl) ⟨962126, by rfl⟩ : syracuseStep 1282835 = 1924253) B1924253
theorem B1897265 : Blo 1264450 1897265 := bstep (se 2 (by rfl) ⟨711474, by rfl⟩ : syracuseStep 1897265 = 1422949) B1422949
theorem B1520435 : Blo 1264450 1520435 := bstep (se 1 (by rfl) ⟨1140326, by rfl⟩ : syracuseStep 1520435 = 2280653) B2280653
theorem B2134849 : Blo 1264450 2134849 := bstep (se 2 (by rfl) ⟨800568, by rfl⟩ : syracuseStep 2134849 = 1601137) B1601137
theorem B1897283 : Blo 1264450 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B1897313 : Blo 1264450 1897313 := bstep (se 2 (by rfl) ⟨711492, by rfl⟩ : syracuseStep 1897313 = 1422985) B1422985
theorem B2134883 : Blo 1264450 2134883 := bstep (se 1 (by rfl) ⟨1601162, by rfl⟩ : syracuseStep 2134883 = 3202325) B3202325
theorem B1897331 : Blo 1264450 1897331 := bstep (se 1 (by rfl) ⟨1422998, by rfl⟩ : syracuseStep 1897331 = 2845997) B2845997
theorem B6411149 : Blo 1264450 6411149 := bstep (se 3 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 6411149 = 2404181) B2404181
theorem B1897361 : Blo 1264450 1897361 := bstep (se 2 (by rfl) ⟨711510, by rfl⟩ : syracuseStep 1897361 = 1423021) B1423021
theorem B1897379 : Blo 1264450 1897379 := bstep (se 1 (by rfl) ⟨1423034, by rfl⟩ : syracuseStep 1897379 = 2846069) B2846069
theorem B4273073 : Blo 1264450 4273073 := bstep (se 2 (by rfl) ⟨1602402, by rfl⟩ : syracuseStep 4273073 = 3204805) B3204805
theorem B1897409 : Blo 1264450 1897409 := bstep (se 2 (by rfl) ⟨711528, by rfl⟩ : syracuseStep 1897409 = 1423057) B1423057
theorem B1602499 : Blo 1264450 1602499 := bstep (se 1 (by rfl) ⟨1201874, by rfl⟩ : syracuseStep 1602499 = 2403749) B2403749
theorem B1897427 : Blo 1264450 1897427 := bstep (se 1 (by rfl) ⟨1423070, by rfl⟩ : syracuseStep 1897427 = 2846141) B2846141
theorem B1463251 : Blo 1264450 1463251 := bstep (se 1 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 1463251 = 2194877) B2194877
theorem B2135011 : Blo 1264450 2135011 := bstep (se 1 (by rfl) ⟨1601258, by rfl⟩ : syracuseStep 2135011 = 3202517) B3202517
theorem B1897457 : Blo 1264450 1897457 := bstep (se 2 (by rfl) ⟨711546, by rfl⟩ : syracuseStep 1897457 = 1423093) B1423093
theorem B1897475 : Blo 1264450 1897475 := bstep (se 1 (by rfl) ⟨1423106, by rfl⟩ : syracuseStep 1897475 = 2846213) B2846213
theorem B2847761 : Blo 1264450 2847761 := bstep (se 2 (by rfl) ⟨1067910, by rfl⟩ : syracuseStep 2847761 = 2135821) B2135821
theorem B1897505 : Blo 1264450 1897505 := bstep (se 2 (by rfl) ⟨711564, by rfl⟩ : syracuseStep 1897505 = 1423129) B1423129
theorem B2847779 : Blo 1264450 2847779 := bstep (se 1 (by rfl) ⟨2135834, by rfl⟩ : syracuseStep 2847779 = 4271669) B4271669
theorem B1602595 : Blo 1264450 1602595 := bstep (se 1 (by rfl) ⟨1201946, by rfl⟩ : syracuseStep 1602595 = 2403893) B2403893
theorem B1897523 : Blo 1264450 1897523 := bstep (se 1 (by rfl) ⟨1423142, by rfl⟩ : syracuseStep 1897523 = 2846285) B2846285
theorem B1897553 : Blo 1264450 1897553 := bstep (se 2 (by rfl) ⟨711582, by rfl⟩ : syracuseStep 1897553 = 1423165) B1423165
theorem B1897571 : Blo 1264450 1897571 := bstep (se 1 (by rfl) ⟨1423178, by rfl⟩ : syracuseStep 1897571 = 2846357) B2846357
theorem B2135153 : Blo 1264450 2135153 := bstep (se 2 (by rfl) ⟨800682, by rfl⟩ : syracuseStep 2135153 = 1601365) B1601365
theorem B1897601 : Blo 1264450 1897601 := bstep (se 2 (by rfl) ⟨711600, by rfl⟩ : syracuseStep 1897601 = 1423201) B1423201
theorem B8107141 : Blo 1264450 8107141 := bstep (se 4 (by rfl) ⟨760044, by rfl⟩ : syracuseStep 8107141 = 1520089) B1520089
theorem B6845573 : Blo 1264450 6845573 := bstep (se 4 (by rfl) ⟨641772, by rfl⟩ : syracuseStep 6845573 = 1283545) B1283545
theorem B7206029 : Blo 1264450 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1897619 : Blo 1264450 1897619 := bstep (se 1 (by rfl) ⟨1423214, by rfl⟩ : syracuseStep 1897619 = 2846429) B2846429
theorem B1897649 : Blo 1264450 1897649 := bstep (se 2 (by rfl) ⟨711618, by rfl⟩ : syracuseStep 1897649 = 1423237) B1423237
theorem B4109489 : Blo 1264450 4109489 := bstep (se 2 (by rfl) ⟨1541058, by rfl⟩ : syracuseStep 4109489 = 3082117) B3082117
theorem B1897667 : Blo 1264450 1897667 := bstep (se 1 (by rfl) ⟨1423250, by rfl⟩ : syracuseStep 1897667 = 2846501) B2846501
theorem B1897697 : Blo 1264450 1897697 := bstep (se 2 (by rfl) ⟨711636, by rfl⟩ : syracuseStep 1897697 = 1423273) B1423273
theorem B2135281 : Blo 1264450 2135281 := bstep (se 2 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 2135281 = 1601461) B1601461
theorem B1897715 : Blo 1264450 1897715 := bstep (se 1 (by rfl) ⟨1423286, by rfl⟩ : syracuseStep 1897715 = 2846573) B2846573
theorem B4052227 : Blo 1264450 4052227 := bstep (se 1 (by rfl) ⟨3039170, by rfl⟩ : syracuseStep 4052227 = 6078341) B6078341
theorem B1897745 : Blo 1264450 1897745 := bstep (se 2 (by rfl) ⟨711654, by rfl⟩ : syracuseStep 1897745 = 1423309) B1423309
theorem B2135315 : Blo 1264450 2135315 := bstep (se 1 (by rfl) ⟨1601486, by rfl⟩ : syracuseStep 2135315 = 3202973) B3202973
theorem B1897763 : Blo 1264450 1897763 := bstep (se 1 (by rfl) ⟨1423322, by rfl⟩ : syracuseStep 1897763 = 2846645) B2846645
theorem B2848049 : Blo 1264450 2848049 := bstep (se 2 (by rfl) ⟨1068018, by rfl⟩ : syracuseStep 2848049 = 2136037) B2136037
theorem B1422643 : Blo 1264450 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B1897793 : Blo 1264450 1897793 := bstep (se 2 (by rfl) ⟨711672, by rfl⟩ : syracuseStep 1897793 = 1423345) B1423345
theorem B2848067 : Blo 1264450 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B1897811 : Blo 1264450 1897811 := bstep (se 1 (by rfl) ⟨1423358, by rfl⟩ : syracuseStep 1897811 = 2846717) B2846717
theorem B1897841 : Blo 1264450 1897841 := bstep (se 2 (by rfl) ⟨711690, by rfl⟩ : syracuseStep 1897841 = 1423381) B1423381
theorem B15398257 : Blo 1264450 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B1897859 : Blo 1264450 1897859 := bstep (se 1 (by rfl) ⟨1423394, by rfl⟩ : syracuseStep 1897859 = 2846789) B2846789
theorem B14415245 : Blo 1264450 14415245 := bstep (se 3 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 14415245 = 5405717) B5405717
theorem B5133709 : Blo 1264450 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B2135443 : Blo 1264450 2135443 := bstep (se 1 (by rfl) ⟨1601582, by rfl⟩ : syracuseStep 2135443 = 3203165) B3203165
theorem B1897889 : Blo 1264450 1897889 := bstep (se 2 (by rfl) ⟨711708, by rfl⟩ : syracuseStep 1897889 = 1423417) B1423417
theorem B1897907 : Blo 1264450 1897907 := bstep (se 1 (by rfl) ⟨1423430, by rfl⟩ : syracuseStep 1897907 = 2846861) B2846861
theorem B1422787 : Blo 1264450 1422787 := bstep (se 1 (by rfl) ⟨1067090, by rfl⟩ : syracuseStep 1422787 = 2134181) B2134181
theorem B4273613 : Blo 1264450 4273613 := bstep (se 3 (by rfl) ⟨801302, by rfl⟩ : syracuseStep 4273613 = 1602605) B1602605
theorem B1897937 : Blo 1264450 1897937 := bstep (se 2 (by rfl) ⟨711726, by rfl⟩ : syracuseStep 1897937 = 1423453) B1423453
theorem B1897955 : Blo 1264450 1897955 := bstep (se 1 (by rfl) ⟨1423466, by rfl⟩ : syracuseStep 1897955 = 2846933) B2846933
theorem B1897985 : Blo 1264450 1897985 := bstep (se 2 (by rfl) ⟨711744, by rfl⟩ : syracuseStep 1897985 = 1423489) B1423489
theorem B1922563 : Blo 1264450 1922563 := bstep (se 1 (by rfl) ⟨1441922, by rfl⟩ : syracuseStep 1922563 = 2883845) B2883845
theorem B4273667 : Blo 1264450 4273667 := bstep (se 1 (by rfl) ⟨3205250, by rfl⟩ : syracuseStep 4273667 = 6410501) B6410501
theorem B1898003 : Blo 1264450 1898003 := bstep (se 1 (by rfl) ⟨1423502, by rfl⟩ : syracuseStep 1898003 = 2847005) B2847005
theorem B2135585 : Blo 1264450 2135585 := bstep (se 2 (by rfl) ⟨800844, by rfl⟩ : syracuseStep 2135585 = 1601689) B1601689
theorem B1734179 : Blo 1264450 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B8214065 : Blo 1264450 8214065 := bstep (se 2 (by rfl) ⟨3080274, by rfl⟩ : syracuseStep 8214065 = 6160549) B6160549
theorem B1922611 : Blo 1264450 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B1898033 : Blo 1264450 1898033 := bstep (se 2 (by rfl) ⟨711762, by rfl⟩ : syracuseStep 1898033 = 1423525) B1423525
theorem B1898051 : Blo 1264450 1898051 := bstep (se 1 (by rfl) ⟨1423538, by rfl⟩ : syracuseStep 1898051 = 2847077) B2847077
theorem B2848337 : Blo 1264450 2848337 := bstep (se 2 (by rfl) ⟨1068126, by rfl⟩ : syracuseStep 2848337 = 2136253) B2136253
theorem B1422931 : Blo 1264450 1422931 := bstep (se 1 (by rfl) ⟨1067198, by rfl⟩ : syracuseStep 1422931 = 2134397) B2134397
theorem B1898081 : Blo 1264450 1898081 := bstep (se 2 (by rfl) ⟨711780, by rfl⟩ : syracuseStep 1898081 = 1423561) B1423561
theorem B2848355 : Blo 1264450 2848355 := bstep (se 1 (by rfl) ⟨2136266, by rfl⟩ : syracuseStep 2848355 = 4272533) B4272533
theorem B6403697 : Blo 1264450 6403697 := bstep (se 2 (by rfl) ⟨2401386, by rfl⟩ : syracuseStep 6403697 = 4802773) B4802773
theorem B1898099 : Blo 1264450 1898099 := bstep (se 1 (by rfl) ⟨1423574, by rfl⟩ : syracuseStep 1898099 = 2847149) B2847149
theorem B1898129 : Blo 1264450 1898129 := bstep (se 2 (by rfl) ⟨711798, by rfl⟩ : syracuseStep 1898129 = 1423597) B1423597
theorem B2135713 : Blo 1264450 2135713 := bstep (se 2 (by rfl) ⟨800892, by rfl⟩ : syracuseStep 2135713 = 1601785) B1601785
theorem B1898147 : Blo 1264450 1898147 := bstep (se 1 (by rfl) ⟨1423610, by rfl⟩ : syracuseStep 1898147 = 2847221) B2847221
theorem B1898177 : Blo 1264450 1898177 := bstep (se 2 (by rfl) ⟨711816, by rfl⟩ : syracuseStep 1898177 = 1423633) B1423633
theorem B2135747 : Blo 1264450 2135747 := bstep (se 1 (by rfl) ⟨1601810, by rfl⟩ : syracuseStep 2135747 = 3203621) B3203621
theorem B1898195 : Blo 1264450 1898195 := bstep (se 1 (by rfl) ⟨1423646, by rfl⟩ : syracuseStep 1898195 = 2847293) B2847293
theorem B1423075 : Blo 1264450 1423075 := bstep (se 1 (by rfl) ⟨1067306, by rfl⟩ : syracuseStep 1423075 = 2134613) B2134613
theorem B1898225 : Blo 1264450 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B1898243 : Blo 1264450 1898243 := bstep (se 1 (by rfl) ⟨1423682, by rfl⟩ : syracuseStep 1898243 = 2847365) B2847365
theorem B4273937 : Blo 1264450 4273937 := bstep (se 2 (by rfl) ⟨1602726, by rfl⟩ : syracuseStep 4273937 = 3205453) B3205453
theorem B1898273 : Blo 1264450 1898273 := bstep (se 2 (by rfl) ⟨711852, by rfl⟩ : syracuseStep 1898273 = 1423705) B1423705
theorem B4806449 : Blo 1264450 4806449 := bstep (se 2 (by rfl) ⟨1802418, by rfl⟩ : syracuseStep 4806449 = 3604837) B3604837
theorem B1898291 : Blo 1264450 1898291 := bstep (se 1 (by rfl) ⟨1423718, by rfl⟩ : syracuseStep 1898291 = 2847437) B2847437
theorem B2135875 : Blo 1264450 2135875 := bstep (se 1 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 2135875 = 3203813) B3203813
theorem B1898321 : Blo 1264450 1898321 := bstep (se 2 (by rfl) ⟨711870, by rfl⟩ : syracuseStep 1898321 = 1423741) B1423741
theorem B3200867 : Blo 1264450 3200867 := bstep (se 1 (by rfl) ⟨2400650, by rfl⟩ : syracuseStep 3200867 = 4801301) B4801301
theorem B1709923 : Blo 1264450 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B1898339 : Blo 1264450 1898339 := bstep (se 1 (by rfl) ⟨1423754, by rfl⟩ : syracuseStep 1898339 = 2847509) B2847509
theorem B2848625 : Blo 1264450 2848625 := bstep (se 2 (by rfl) ⟨1068234, by rfl⟩ : syracuseStep 2848625 = 2136469) B2136469
theorem B1423219 : Blo 1264450 1423219 := bstep (se 1 (by rfl) ⟨1067414, by rfl⟩ : syracuseStep 1423219 = 2134829) B2134829
theorem B1898369 : Blo 1264450 1898369 := bstep (se 2 (by rfl) ⟨711888, by rfl⟩ : syracuseStep 1898369 = 1423777) B1423777
theorem B2848643 : Blo 1264450 2848643 := bstep (se 1 (by rfl) ⟨2136482, by rfl⟩ : syracuseStep 2848643 = 4272965) B4272965
theorem B1898387 : Blo 1264450 1898387 := bstep (se 1 (by rfl) ⟨1423790, by rfl⟩ : syracuseStep 1898387 = 2847581) B2847581
theorem B1898417 : Blo 1264450 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1898435 : Blo 1264450 1898435 := bstep (se 1 (by rfl) ⟨1423826, by rfl⟩ : syracuseStep 1898435 = 2847653) B2847653
theorem B2136017 : Blo 1264450 2136017 := bstep (se 2 (by rfl) ⟨801006, by rfl⟩ : syracuseStep 2136017 = 1602013) B1602013
theorem B1898465 : Blo 1264450 1898465 := bstep (se 2 (by rfl) ⟨711924, by rfl⟩ : syracuseStep 1898465 = 1423849) B1423849
theorem B1898483 : Blo 1264450 1898483 := bstep (se 1 (by rfl) ⟨1423862, by rfl⟩ : syracuseStep 1898483 = 2847725) B2847725
theorem B1423363 : Blo 1264450 1423363 := bstep (se 1 (by rfl) ⟨1067522, by rfl⟩ : syracuseStep 1423363 = 2135045) B2135045
theorem B1898513 : Blo 1264450 1898513 := bstep (se 2 (by rfl) ⟨711942, by rfl⟩ : syracuseStep 1898513 = 1423885) B1423885
theorem B3201059 : Blo 1264450 3201059 := bstep (se 1 (by rfl) ⟨2400794, by rfl⟩ : syracuseStep 3201059 = 4801589) B4801589
theorem B1898531 : Blo 1264450 1898531 := bstep (se 1 (by rfl) ⟨1423898, by rfl⟩ : syracuseStep 1898531 = 2847797) B2847797
theorem B1898561 : Blo 1264450 1898561 := bstep (se 2 (by rfl) ⟨711960, by rfl⟩ : syracuseStep 1898561 = 1423921) B1423921
theorem B2136145 : Blo 1264450 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B1898579 : Blo 1264450 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B1898609 : Blo 1264450 1898609 := bstep (se 2 (by rfl) ⟨711978, by rfl⟩ : syracuseStep 1898609 = 1423957) B1423957
theorem B2136179 : Blo 1264450 2136179 := bstep (se 1 (by rfl) ⟨1602134, by rfl⟩ : syracuseStep 2136179 = 3204269) B3204269
theorem B1898627 : Blo 1264450 1898627 := bstep (se 1 (by rfl) ⟨1423970, by rfl⟩ : syracuseStep 1898627 = 2847941) B2847941
theorem B7698565 : Blo 1264450 7698565 := bstep (se 4 (by rfl) ⟨721740, by rfl⟩ : syracuseStep 7698565 = 1443481) B1443481
theorem B2848913 : Blo 1264450 2848913 := bstep (se 2 (by rfl) ⟨1068342, by rfl⟩ : syracuseStep 2848913 = 2136685) B2136685
theorem B1423507 : Blo 1264450 1423507 := bstep (se 1 (by rfl) ⟨1067630, by rfl⟩ : syracuseStep 1423507 = 2135261) B2135261
theorem B1898657 : Blo 1264450 1898657 := bstep (se 2 (by rfl) ⟨711996, by rfl⟩ : syracuseStep 1898657 = 1423993) B1423993
theorem B2848931 : Blo 1264450 2848931 := bstep (se 1 (by rfl) ⟨2136698, by rfl⟩ : syracuseStep 2848931 = 4273397) B4273397
theorem B1898675 : Blo 1264450 1898675 := bstep (se 1 (by rfl) ⟨1424006, by rfl⟩ : syracuseStep 1898675 = 2848013) B2848013
theorem B3602627 : Blo 1264450 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B1898705 : Blo 1264450 1898705 := bstep (se 2 (by rfl) ⟨712014, by rfl⟩ : syracuseStep 1898705 = 1424029) B1424029
theorem B6838499 : Blo 1264450 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B1898723 : Blo 1264450 1898723 := bstep (se 1 (by rfl) ⟨1424042, by rfl⟩ : syracuseStep 1898723 = 2848085) B2848085
theorem B2136307 : Blo 1264450 2136307 := bstep (se 1 (by rfl) ⟨1602230, by rfl⟩ : syracuseStep 2136307 = 3204461) B3204461
theorem B1898753 : Blo 1264450 1898753 := bstep (se 2 (by rfl) ⟨712032, by rfl⟩ : syracuseStep 1898753 = 1424065) B1424065
theorem B1898771 : Blo 1264450 1898771 := bstep (se 1 (by rfl) ⟨1424078, by rfl⟩ : syracuseStep 1898771 = 2848157) B2848157
theorem B1423651 : Blo 1264450 1423651 := bstep (se 1 (by rfl) ⟨1067738, by rfl⟩ : syracuseStep 1423651 = 2135477) B2135477
theorem B1898801 : Blo 1264450 1898801 := bstep (se 2 (by rfl) ⟨712050, by rfl⟩ : syracuseStep 1898801 = 1424101) B1424101
theorem B13678901 : Blo 1264450 13678901 := bstep (se 5 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 13678901 = 1282397) B1282397
theorem B1898819 : Blo 1264450 1898819 := bstep (se 1 (by rfl) ⟨1424114, by rfl⟩ : syracuseStep 1898819 = 2848229) B2848229
theorem B1898849 : Blo 1264450 1898849 := bstep (se 2 (by rfl) ⟨712068, by rfl⟩ : syracuseStep 1898849 = 1424137) B1424137
theorem B1898867 : Blo 1264450 1898867 := bstep (se 1 (by rfl) ⟨1424150, by rfl⟩ : syracuseStep 1898867 = 2848301) B2848301
theorem B2136449 : Blo 1264450 2136449 := bstep (se 2 (by rfl) ⟨801168, by rfl⟩ : syracuseStep 2136449 = 1602337) B1602337
theorem B5405069 : Blo 1264450 5405069 := bstep (se 3 (by rfl) ⟨1013450, by rfl⟩ : syracuseStep 5405069 = 2026901) B2026901
theorem B59251085 : Blo 1264450 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B1898897 : Blo 1264450 1898897 := bstep (se 2 (by rfl) ⟨712086, by rfl⟩ : syracuseStep 1898897 = 1424173) B1424173
theorem B1898915 : Blo 1264450 1898915 := bstep (se 1 (by rfl) ⟨1424186, by rfl⟩ : syracuseStep 1898915 = 2848373) B2848373
theorem B1800625 : Blo 1264450 1800625 := bstep (se 2 (by rfl) ⟨675234, by rfl⟩ : syracuseStep 1800625 = 1350469) B1350469
theorem B1423795 : Blo 1264450 1423795 := bstep (se 1 (by rfl) ⟨1067846, by rfl⟩ : syracuseStep 1423795 = 2135693) B2135693
theorem B2849201 : Blo 1264450 2849201 := bstep (se 2 (by rfl) ⟨1068450, by rfl⟩ : syracuseStep 2849201 = 2136901) B2136901
theorem B1898945 : Blo 1264450 1898945 := bstep (se 2 (by rfl) ⟨712104, by rfl⟩ : syracuseStep 1898945 = 1424209) B1424209
theorem B2849219 : Blo 1264450 2849219 := bstep (se 1 (by rfl) ⟨2136914, by rfl⟩ : syracuseStep 2849219 = 4273829) B4273829
theorem B1898963 : Blo 1264450 1898963 := bstep (se 1 (by rfl) ⟨1424222, by rfl⟩ : syracuseStep 1898963 = 2848445) B2848445
theorem B1898993 : Blo 1264450 1898993 := bstep (se 2 (by rfl) ⟨712122, by rfl⟩ : syracuseStep 1898993 = 1424245) B1424245
theorem B2136577 : Blo 1264450 2136577 := bstep (se 2 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 2136577 = 1602433) B1602433
theorem B1899011 : Blo 1264450 1899011 := bstep (se 1 (by rfl) ⟨1424258, by rfl⟩ : syracuseStep 1899011 = 2848517) B2848517
theorem B10951181 : Blo 1264450 10951181 := bstep (se 3 (by rfl) ⟨2053346, by rfl⟩ : syracuseStep 10951181 = 4106693) B4106693
theorem B1800721 : Blo 1264450 1800721 := bstep (se 2 (by rfl) ⟨675270, by rfl⟩ : syracuseStep 1800721 = 1350541) B1350541
theorem B1899041 : Blo 1264450 1899041 := bstep (se 2 (by rfl) ⟨712140, by rfl⟩ : syracuseStep 1899041 = 1424281) B1424281
theorem B2136611 : Blo 1264450 2136611 := bstep (se 1 (by rfl) ⟨1602458, by rfl⟩ : syracuseStep 2136611 = 3204917) B3204917
theorem B1899059 : Blo 1264450 1899059 := bstep (se 1 (by rfl) ⟨1424294, by rfl⟩ : syracuseStep 1899059 = 2848589) B2848589
theorem B1423939 : Blo 1264450 1423939 := bstep (se 1 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 1423939 = 2135909) B2135909
theorem B1899089 : Blo 1264450 1899089 := bstep (se 2 (by rfl) ⟨712158, by rfl⟩ : syracuseStep 1899089 = 1424317) B1424317
theorem B1899107 : Blo 1264450 1899107 := bstep (se 1 (by rfl) ⟨1424330, by rfl⟩ : syracuseStep 1899107 = 2848661) B2848661
theorem B2701937 : Blo 1264450 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B1899137 : Blo 1264450 1899137 := bstep (se 2 (by rfl) ⟨712176, by rfl⟩ : syracuseStep 1899137 = 1424353) B1424353
theorem B11541133 : Blo 1264450 11541133 := bstep (se 3 (by rfl) ⟨2163962, by rfl⟩ : syracuseStep 11541133 = 4327925) B4327925
theorem B1899155 : Blo 1264450 1899155 := bstep (se 1 (by rfl) ⟨1424366, by rfl⟩ : syracuseStep 1899155 = 2848733) B2848733
theorem B2136739 : Blo 1264450 2136739 := bstep (se 1 (by rfl) ⟨1602554, by rfl⟩ : syracuseStep 2136739 = 3205109) B3205109
theorem B1899185 : Blo 1264450 1899185 := bstep (se 2 (by rfl) ⟨712194, by rfl⟩ : syracuseStep 1899185 = 1424389) B1424389
theorem B1899203 : Blo 1264450 1899203 := bstep (se 1 (by rfl) ⟨1424402, by rfl⟩ : syracuseStep 1899203 = 2848805) B2848805
theorem B2849489 : Blo 1264450 2849489 := bstep (se 2 (by rfl) ⟨1068558, by rfl⟩ : syracuseStep 2849489 = 2137117) B2137117
theorem B1424083 : Blo 1264450 1424083 := bstep (se 1 (by rfl) ⟨1068062, by rfl⟩ : syracuseStep 1424083 = 2136125) B2136125
theorem B1899233 : Blo 1264450 1899233 := bstep (se 2 (by rfl) ⟨712212, by rfl⟩ : syracuseStep 1899233 = 1424425) B1424425
theorem B2849507 : Blo 1264450 2849507 := bstep (se 1 (by rfl) ⟨2137130, by rfl⟩ : syracuseStep 2849507 = 4274261) B4274261
theorem B1899251 : Blo 1264450 1899251 := bstep (se 1 (by rfl) ⟨1424438, by rfl⟩ : syracuseStep 1899251 = 2848877) B2848877
theorem B1899281 : Blo 1264450 1899281 := bstep (se 2 (by rfl) ⟨712230, by rfl⟩ : syracuseStep 1899281 = 1424461) B1424461
theorem B4332305 : Blo 1264450 4332305 := bstep (se 2 (by rfl) ⟨1624614, by rfl⟩ : syracuseStep 4332305 = 3249229) B3249229
theorem B1899299 : Blo 1264450 1899299 := bstep (se 1 (by rfl) ⟨1424474, by rfl⟩ : syracuseStep 1899299 = 2848949) B2848949
theorem B2136881 : Blo 1264450 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B1899329 : Blo 1264450 1899329 := bstep (se 2 (by rfl) ⟨712248, by rfl⟩ : syracuseStep 1899329 = 1424497) B1424497
theorem B4053827 : Blo 1264450 4053827 := bstep (se 1 (by rfl) ⟨3040370, by rfl⟩ : syracuseStep 4053827 = 6080741) B6080741
theorem B1899347 : Blo 1264450 1899347 := bstep (se 1 (by rfl) ⟨1424510, by rfl⟩ : syracuseStep 1899347 = 2849021) B2849021
theorem B1424227 : Blo 1264450 1424227 := bstep (se 1 (by rfl) ⟨1068170, by rfl⟩ : syracuseStep 1424227 = 2136341) B2136341
theorem B1899377 : Blo 1264450 1899377 := bstep (se 2 (by rfl) ⟨712266, by rfl⟩ : syracuseStep 1899377 = 1424533) B1424533
theorem B1899395 : Blo 1264450 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B1899425 : Blo 1264450 1899425 := bstep (se 2 (by rfl) ⟨712284, by rfl⟩ : syracuseStep 1899425 = 1424569) B1424569
theorem B2137009 : Blo 1264450 2137009 := bstep (se 2 (by rfl) ⟨801378, by rfl⟩ : syracuseStep 2137009 = 1602757) B1602757
theorem B1899443 : Blo 1264450 1899443 := bstep (se 1 (by rfl) ⟨1424582, by rfl⟩ : syracuseStep 1899443 = 2849165) B2849165
theorem B3202001 : Blo 1264450 3202001 := bstep (se 2 (by rfl) ⟨1200750, by rfl⟩ : syracuseStep 3202001 = 2401501) B2401501
theorem B1899473 : Blo 1264450 1899473 := bstep (se 2 (by rfl) ⟨712302, by rfl⟩ : syracuseStep 1899473 = 1424605) B1424605
theorem B2137043 : Blo 1264450 2137043 := bstep (se 1 (by rfl) ⟨1602782, by rfl⟩ : syracuseStep 2137043 = 3205565) B3205565
theorem B1899491 : Blo 1264450 1899491 := bstep (se 1 (by rfl) ⟨1424618, by rfl⟩ : syracuseStep 1899491 = 2849237) B2849237
theorem B3603437 : Blo 1264450 3603437 := bstep (se 3 (by rfl) ⟨675644, by rfl⟩ : syracuseStep 3603437 = 1351289) B1351289
theorem B1424371 : Blo 1264450 1424371 := bstep (se 1 (by rfl) ⟨1068278, by rfl⟩ : syracuseStep 1424371 = 2136557) B2136557
theorem B1801217 : Blo 1264450 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B1899521 : Blo 1264450 1899521 := bstep (se 2 (by rfl) ⟨712320, by rfl⟩ : syracuseStep 1899521 = 1424641) B1424641
theorem B3202051 : Blo 1264450 3202051 := bstep (se 1 (by rfl) ⟨2401538, by rfl⟩ : syracuseStep 3202051 = 4803077) B4803077
theorem B7691269 : Blo 1264450 7691269 := bstep (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) B1442113
theorem B1899539 : Blo 1264450 1899539 := bstep (se 1 (by rfl) ⟨1424654, by rfl⟩ : syracuseStep 1899539 = 2849309) B2849309
theorem B6405155 : Blo 1264450 6405155 := bstep (se 1 (by rfl) ⟨4803866, by rfl⟩ : syracuseStep 6405155 = 9607733) B9607733
theorem B1899569 : Blo 1264450 1899569 := bstep (se 2 (by rfl) ⟨712338, by rfl⟩ : syracuseStep 1899569 = 1424677) B1424677
theorem B1899587 : Blo 1264450 1899587 := bstep (se 1 (by rfl) ⟨1424690, by rfl⟩ : syracuseStep 1899587 = 2849381) B2849381
theorem B1899617 : Blo 1264450 1899617 := bstep (se 2 (by rfl) ⟨712356, by rfl⟩ : syracuseStep 1899617 = 1424713) B1424713
theorem B1899635 : Blo 1264450 1899635 := bstep (se 1 (by rfl) ⟨1424726, by rfl⟩ : syracuseStep 1899635 = 2849453) B2849453
theorem B1424515 : Blo 1264450 1424515 := bstep (se 1 (by rfl) ⟨1068386, by rfl⟩ : syracuseStep 1424515 = 2136773) B2136773
theorem B3202193 : Blo 1264450 3202193 := bstep (se 2 (by rfl) ⟨1200822, by rfl⟩ : syracuseStep 3202193 = 2401645) B2401645
theorem B1899665 : Blo 1264450 1899665 := bstep (se 2 (by rfl) ⟨712374, by rfl⟩ : syracuseStep 1899665 = 1424749) B1424749
theorem B3603629 : Blo 1264450 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B4807907 : Blo 1264450 4807907 := bstep (se 1 (by rfl) ⟨3605930, by rfl⟩ : syracuseStep 4807907 = 7211861) B7211861
theorem B1424659 : Blo 1264450 1424659 := bstep (se 1 (by rfl) ⟨1068494, by rfl⟩ : syracuseStep 1424659 = 2136989) B2136989
theorem B2055473 : Blo 1264450 2055473 := bstep (se 2 (by rfl) ⟨770802, by rfl⟩ : syracuseStep 2055473 = 1541605) B1541605
theorem B15392069 : Blo 1264450 15392069 := bstep (se 4 (by rfl) ⟨1443006, by rfl⟩ : syracuseStep 15392069 = 2886013) B2886013
theorem B7208261 : Blo 1264450 7208261 := bstep (se 4 (by rfl) ⟨675774, by rfl⟩ : syracuseStep 7208261 = 1351549) B1351549
theorem B1711441 : Blo 1264450 1711441 := bstep (se 2 (by rfl) ⟨641790, by rfl⟩ : syracuseStep 1711441 = 1283581) B1283581
theorem B1351139 : Blo 1264450 1351139 := bstep (se 1 (by rfl) ⟨1013354, by rfl⟩ : syracuseStep 1351139 = 2026709) B2026709
theorem B4267565 : Blo 1264450 4267565 := bstep (se 3 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 4267565 = 1600337) B1600337
theorem B1826353 : Blo 1264450 1826353 := bstep (se 2 (by rfl) ⟨684882, by rfl⟩ : syracuseStep 1826353 = 1369765) B1369765
theorem B4267619 : Blo 1264450 4267619 := bstep (se 1 (by rfl) ⟨3200714, by rfl⟩ : syracuseStep 4267619 = 6401429) B6401429
theorem B6332003 : Blo 1264450 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B3038833 : Blo 1264450 3038833 := bstep (se 2 (by rfl) ⟨1139562, by rfl⟩ : syracuseStep 3038833 = 2279125) B2279125
theorem B5406385 : Blo 1264450 5406385 := bstep (se 2 (by rfl) ⟨2027394, by rfl⟩ : syracuseStep 5406385 = 4054789) B4054789
theorem B14409413 : Blo 1264450 14409413 := bstep (se 4 (by rfl) ⟨1350882, by rfl⟩ : syracuseStep 14409413 = 2701765) B2701765
theorem B4054801 : Blo 1264450 4054801 := bstep (se 2 (by rfl) ⟨1520550, by rfl⟩ : syracuseStep 4054801 = 3041101) B3041101
theorem B3039025 : Blo 1264450 3039025 := bstep (se 2 (by rfl) ⟨1139634, by rfl⟩ : syracuseStep 3039025 = 2279269) B2279269
theorem B6405965 : Blo 1264450 6405965 := bstep (se 3 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 6405965 = 2402237) B2402237
theorem B1802083 : Blo 1264450 1802083 := bstep (se 1 (by rfl) ⟨1351562, by rfl⟩ : syracuseStep 1802083 = 2703125) B2703125
theorem B4267889 : Blo 1264450 4267889 := bstep (se 2 (by rfl) ⟨1600458, by rfl⟩ : syracuseStep 4267889 = 3200917) B3200917
theorem B2703235 : Blo 1264450 2703235 := bstep (se 1 (by rfl) ⟨2027426, by rfl⟩ : syracuseStep 2703235 = 4054853) B4054853
theorem B1802179 : Blo 1264450 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B7208945 : Blo 1264450 7208945 := bstep (se 2 (by rfl) ⟨2703354, by rfl⟩ : syracuseStep 7208945 = 5406709) B5406709
theorem B5406743 : Blo 1264450 5406743 := bstep (se 1 (by rfl) ⟨4055057, by rfl⟩ : syracuseStep 5406743 = 8110115) B8110115
theorem B51945623 : Blo 1264450 51945623 := bstep (se 1 (by rfl) ⟨38959217, by rfl⟩ : syracuseStep 51945623 = 77918435) B77918435
theorem B10264753 : Blo 1264450 10264753 := bstep (se 2 (by rfl) ⟨3849282, by rfl⟩ : syracuseStep 10264753 = 7698565) B7698565
theorem B2703577 : Blo 1264450 2703577 := bstep (se 2 (by rfl) ⟨1013841, by rfl⟩ : syracuseStep 2703577 = 2027683) B2027683
theorem B41025797 : Blo 1264450 41025797 := bstep (se 4 (by rfl) ⟨3846168, by rfl⟩ : syracuseStep 41025797 = 7692337) B7692337
theorem B9740549 : Blo 1264450 9740549 := bstep (se 4 (by rfl) ⟨913176, by rfl⟩ : syracuseStep 9740549 = 1826353) B1826353
theorem B1802521 : Blo 1264450 1802521 := bstep (se 2 (by rfl) ⟨675945, by rfl⟩ : syracuseStep 1802521 = 1351891) B1351891
theorem B3039563 : Blo 1264450 3039563 := bstep (se 1 (by rfl) ⟨2279672, by rfl⟩ : syracuseStep 3039563 = 4559345) B4559345
theorem B18497909 : Blo 1264450 18497909 := bstep (se 5 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 18497909 = 1734179) B1734179
theorem B9609677 : Blo 1264450 9609677 := bstep (se 3 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 9609677 = 3603629) B3603629
theorem B2310617 : Blo 1264450 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B2400779 : Blo 1264450 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B32424461 : Blo 1264450 32424461 := bstep (se 3 (by rfl) ⟨6079586, by rfl⟩ : syracuseStep 32424461 = 12159173) B12159173
theorem B2400833 : Blo 1264450 2400833 := bstep (se 2 (by rfl) ⟨900312, by rfl⟩ : syracuseStep 2400833 = 1800625) B1800625
theorem B3850841 : Blo 1264450 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B4563715 : Blo 1264450 4563715 := bstep (se 1 (by rfl) ⟨3422786, by rfl⟩ : syracuseStep 4563715 = 6845573) B6845573
theorem B5202733 : Blo 1264450 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B3851083 : Blo 1264450 3851083 := bstep (se 1 (by rfl) ⟨2888312, by rfl⟩ : syracuseStep 3851083 = 5776625) B5776625
theorem B3900253 : Blo 1264450 3900253 := bstep (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) B1462595
theorem B9610163 : Blo 1264450 9610163 := bstep (se 1 (by rfl) ⟨7207622, by rfl⟩ : syracuseStep 9610163 = 14415245) B14415245
theorem B5407667 : Blo 1264450 5407667 := bstep (se 1 (by rfl) ⟨4055750, by rfl⟩ : syracuseStep 5407667 = 8111501) B8111501
theorem B2884619 : Blo 1264450 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B4269131 : Blo 1264450 4269131 := bstep (se 1 (by rfl) ⟨3201848, by rfl⟩ : syracuseStep 4269131 = 6403697) B6403697
theorem B6407261 : Blo 1264450 6407261 := bstep (se 3 (by rfl) ⟨1201361, by rfl⟩ : syracuseStep 6407261 = 2402723) B2402723
theorem B3204299 : Blo 1264450 3204299 := bstep (se 1 (by rfl) ⟨2403224, by rfl⟩ : syracuseStep 3204299 = 4806449) B4806449
theorem B3605725 : Blo 1264450 3605725 := bstep (se 3 (by rfl) ⟨676073, by rfl⟩ : syracuseStep 3605725 = 1352147) B1352147
theorem B1951001 : Blo 1264450 1951001 := bstep (se 2 (by rfl) ⟨731625, by rfl⟩ : syracuseStep 1951001 = 1463251) B1463251
theorem B23389505 : Blo 1264450 23389505 := bstep (se 2 (by rfl) ⟨8771064, by rfl⟩ : syracuseStep 23389505 = 17542129) B17542129
theorem B6079819 : Blo 1264450 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B4269401 : Blo 1264450 4269401 := bstep (se 2 (by rfl) ⟨1601025, by rfl⟩ : syracuseStep 4269401 = 3202051) B3202051
theorem B3605953 : Blo 1264450 3605953 := bstep (se 2 (by rfl) ⟨1352232, by rfl⟩ : syracuseStep 3605953 = 2704465) B2704465
theorem B2401751 : Blo 1264450 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B9119267 : Blo 1264450 9119267 := bstep (se 1 (by rfl) ⟨6839450, by rfl⟩ : syracuseStep 9119267 = 13678901) B13678901
theorem B20514455 : Blo 1264450 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B3245719 : Blo 1264450 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B7300787 : Blo 1264450 7300787 := bstep (se 1 (by rfl) ⟨5475590, by rfl⟩ : syracuseStep 7300787 = 10951181) B10951181
theorem B3606295 : Blo 1264450 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B20531009 : Blo 1264450 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B5408657 : Blo 1264450 5408657 := bstep (se 2 (by rfl) ⟨2028246, by rfl⟩ : syracuseStep 5408657 = 4056493) B4056493
theorem B7210903 : Blo 1264450 7210903 := bstep (se 1 (by rfl) ⟨5408177, by rfl⟩ : syracuseStep 7210903 = 10816355) B10816355
theorem B2402291 : Blo 1264450 2402291 := bstep (se 1 (by rfl) ⟨1801718, by rfl⟩ : syracuseStep 2402291 = 3603437) B3603437
theorem B2279435 : Blo 1264450 2279435 := bstep (se 1 (by rfl) ⟨1709576, by rfl⟩ : syracuseStep 2279435 = 3419153) B3419153
theorem B4270103 : Blo 1264450 4270103 := bstep (se 1 (by rfl) ⟨3202577, by rfl⟩ : syracuseStep 4270103 = 6405155) B6405155
theorem B11552813 : Blo 1264450 11552813 := bstep (se 3 (by rfl) ⟨2166152, by rfl⟩ : syracuseStep 11552813 = 4332305) B4332305
theorem B3205271 : Blo 1264450 3205271 := bstep (se 1 (by rfl) ⟨2403953, by rfl⟩ : syracuseStep 3205271 = 4807907) B4807907
theorem B1370315 : Blo 1264450 1370315 := bstep (se 1 (by rfl) ⟨1027736, by rfl⟩ : syracuseStep 1370315 = 2055473) B2055473
theorem B9611621 : Blo 1264450 9611621 := bstep (se 4 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 9611621 = 1802179) B1802179
theorem B2845043 : Blo 1264450 2845043 := bstep (se 1 (by rfl) ⟨2133782, by rfl⟩ : syracuseStep 2845043 = 4267565) B4267565
theorem B2845079 : Blo 1264450 2845079 := bstep (se 1 (by rfl) ⟨2133809, by rfl⟩ : syracuseStep 2845079 = 4267619) B4267619
theorem B4221335 : Blo 1264450 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B2279897 : Blo 1264450 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B2402777 : Blo 1264450 2402777 := bstep (se 2 (by rfl) ⟨901041, by rfl⟩ : syracuseStep 2402777 = 1802083) B1802083
theorem B4557329 : Blo 1264450 4557329 := bstep (se 2 (by rfl) ⟨1708998, by rfl⟩ : syracuseStep 4557329 = 3417997) B3417997
theorem B4270643 : Blo 1264450 4270643 := bstep (se 1 (by rfl) ⟨3202982, by rfl⟩ : syracuseStep 4270643 = 6405965) B6405965
theorem B2845259 : Blo 1264450 2845259 := bstep (se 1 (by rfl) ⟨2133944, by rfl⟩ : syracuseStep 2845259 = 4267889) B4267889
theorem B2845313 : Blo 1264450 2845313 := bstep (se 2 (by rfl) ⟨1066992, by rfl⟩ : syracuseStep 2845313 = 2133985) B2133985
theorem B4803245 : Blo 1264450 4803245 := bstep (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) B1801217
theorem B9603845 : Blo 1264450 9603845 := bstep (se 4 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 9603845 = 1800721) B1800721
theorem B2435891 : Blo 1264450 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B4270913 : Blo 1264450 4270913 := bstep (se 2 (by rfl) ⟨1601592, by rfl⟩ : syracuseStep 4270913 = 3203185) B3203185
theorem B1264459 : Blo 1264450 1264459 := bstep (se 1 (by rfl) ⟨948344, by rfl⟩ : syracuseStep 1264459 = 1896689) B1896689
theorem B9612107 : Blo 1264450 9612107 := bstep (se 1 (by rfl) ⟨7209080, by rfl⟩ : syracuseStep 9612107 = 14418161) B14418161
theorem B1264471 : Blo 1264450 1264471 := bstep (se 1 (by rfl) ⟨948353, by rfl⟩ : syracuseStep 1264471 = 1896707) B1896707
theorem B2845529 : Blo 1264450 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B1264491 : Blo 1264450 1264491 := bstep (se 1 (by rfl) ⟨948368, by rfl⟩ : syracuseStep 1264491 = 1896737) B1896737
theorem B1264503 : Blo 1264450 1264503 := bstep (se 1 (by rfl) ⟨948377, by rfl⟩ : syracuseStep 1264503 = 1896755) B1896755
theorem B1264523 : Blo 1264450 1264523 := bstep (se 1 (by rfl) ⟨948392, by rfl⟩ : syracuseStep 1264523 = 1896785) B1896785
theorem B1264535 : Blo 1264450 1264535 := bstep (se 1 (by rfl) ⟨948401, by rfl⟩ : syracuseStep 1264535 = 1896803) B1896803
theorem B1264555 : Blo 1264450 1264555 := bstep (se 1 (by rfl) ⟨948416, by rfl⟩ : syracuseStep 1264555 = 1896833) B1896833
theorem B2845619 : Blo 1264450 2845619 := bstep (se 1 (by rfl) ⟨2134214, by rfl⟩ : syracuseStep 2845619 = 4268429) B4268429
theorem B1264567 : Blo 1264450 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B1264587 : Blo 1264450 1264587 := bstep (se 1 (by rfl) ⟨948440, by rfl⟩ : syracuseStep 1264587 = 1896881) B1896881
theorem B1264599 : Blo 1264450 1264599 := bstep (se 1 (by rfl) ⟨948449, by rfl⟩ : syracuseStep 1264599 = 1896899) B1896899
theorem B2845655 : Blo 1264450 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1264619 : Blo 1264450 1264619 := bstep (se 1 (by rfl) ⟨948464, by rfl⟩ : syracuseStep 1264619 = 1896929) B1896929
theorem B1264631 : Blo 1264450 1264631 := bstep (se 1 (by rfl) ⟨948473, by rfl⟩ : syracuseStep 1264631 = 1896947) B1896947
theorem B1264651 : Blo 1264450 1264651 := bstep (se 1 (by rfl) ⟨948488, by rfl⟩ : syracuseStep 1264651 = 1896977) B1896977
theorem B2165771 : Blo 1264450 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B6491153 : Blo 1264450 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B1264663 : Blo 1264450 1264663 := bstep (se 1 (by rfl) ⟨948497, by rfl⟩ : syracuseStep 1264663 = 1896995) B1896995
theorem B1264683 : Blo 1264450 1264683 := bstep (se 1 (by rfl) ⟨948512, by rfl⟩ : syracuseStep 1264683 = 1897025) B1897025
theorem B2567219 : Blo 1264450 2567219 := bstep (se 1 (by rfl) ⟨1925414, by rfl⟩ : syracuseStep 2567219 = 3850829) B3850829
theorem B1264695 : Blo 1264450 1264695 := bstep (se 1 (by rfl) ⟨948521, by rfl⟩ : syracuseStep 1264695 = 1897043) B1897043
theorem B1264715 : Blo 1264450 1264715 := bstep (se 1 (by rfl) ⟨948536, by rfl⟩ : syracuseStep 1264715 = 1897073) B1897073
theorem B1264727 : Blo 1264450 1264727 := bstep (se 1 (by rfl) ⟨948545, by rfl⟩ : syracuseStep 1264727 = 1897091) B1897091
theorem B1264747 : Blo 1264450 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B1264759 : Blo 1264450 1264759 := bstep (se 1 (by rfl) ⟨948569, by rfl⟩ : syracuseStep 1264759 = 1897139) B1897139
theorem B1600651 : Blo 1264450 1600651 := bstep (se 1 (by rfl) ⟨1200488, by rfl⟩ : syracuseStep 1600651 = 2400977) B2400977
theorem B1264779 : Blo 1264450 1264779 := bstep (se 1 (by rfl) ⟨948584, by rfl⟩ : syracuseStep 1264779 = 1897169) B1897169
theorem B2845835 : Blo 1264450 2845835 := bstep (se 1 (by rfl) ⟨2134376, by rfl⟩ : syracuseStep 2845835 = 4268753) B4268753
theorem B1264791 : Blo 1264450 1264791 := bstep (se 1 (by rfl) ⟨948593, by rfl⟩ : syracuseStep 1264791 = 1897187) B1897187
theorem B24325271 : Blo 1264450 24325271 := bstep (se 1 (by rfl) ⟨18243953, by rfl⟩ : syracuseStep 24325271 = 36487907) B36487907
theorem B6409367 : Blo 1264450 6409367 := bstep (se 1 (by rfl) ⟨4807025, by rfl⟩ : syracuseStep 6409367 = 9614051) B9614051
theorem B1264811 : Blo 1264450 1264811 := bstep (se 1 (by rfl) ⟨948608, by rfl⟩ : syracuseStep 1264811 = 1897217) B1897217
theorem B1264823 : Blo 1264450 1264823 := bstep (se 1 (by rfl) ⟨948617, by rfl⟩ : syracuseStep 1264823 = 1897235) B1897235
theorem B2845889 : Blo 1264450 2845889 := bstep (se 2 (by rfl) ⟨1067208, by rfl⟩ : syracuseStep 2845889 = 2134417) B2134417
theorem B1264843 : Blo 1264450 1264843 := bstep (se 1 (by rfl) ⟨948632, by rfl⟩ : syracuseStep 1264843 = 1897265) B1897265
theorem B1264855 : Blo 1264450 1264855 := bstep (se 1 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 1264855 = 1897283) B1897283
theorem B1264875 : Blo 1264450 1264875 := bstep (se 1 (by rfl) ⟨948656, by rfl⟩ : syracuseStep 1264875 = 1897313) B1897313
theorem B1264887 : Blo 1264450 1264887 := bstep (se 1 (by rfl) ⟨948665, by rfl⟩ : syracuseStep 1264887 = 1897331) B1897331
theorem B1264907 : Blo 1264450 1264907 := bstep (se 1 (by rfl) ⟨948680, by rfl⟩ : syracuseStep 1264907 = 1897361) B1897361
theorem B1264919 : Blo 1264450 1264919 := bstep (se 1 (by rfl) ⟨948689, by rfl⟩ : syracuseStep 1264919 = 1897379) B1897379
theorem B1264939 : Blo 1264450 1264939 := bstep (se 1 (by rfl) ⟨948704, by rfl⟩ : syracuseStep 1264939 = 1897409) B1897409
theorem B1264951 : Blo 1264450 1264951 := bstep (se 1 (by rfl) ⟨948713, by rfl⟩ : syracuseStep 1264951 = 1897427) B1897427
theorem B1264971 : Blo 1264450 1264971 := bstep (se 1 (by rfl) ⟨948728, by rfl⟩ : syracuseStep 1264971 = 1897457) B1897457
theorem B1264983 : Blo 1264450 1264983 := bstep (se 1 (by rfl) ⟨948737, by rfl⟩ : syracuseStep 1264983 = 1897475) B1897475
theorem B4271453 : Blo 1264450 4271453 := bstep (se 3 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 4271453 = 1601795) B1601795
theorem B1265003 : Blo 1264450 1265003 := bstep (se 1 (by rfl) ⟨948752, by rfl⟩ : syracuseStep 1265003 = 1897505) B1897505
theorem B1265015 : Blo 1264450 1265015 := bstep (se 1 (by rfl) ⟨948761, by rfl⟩ : syracuseStep 1265015 = 1897523) B1897523
theorem B1265035 : Blo 1264450 1265035 := bstep (se 1 (by rfl) ⟨948776, by rfl⟩ : syracuseStep 1265035 = 1897553) B1897553
theorem B1265047 : Blo 1264450 1265047 := bstep (se 1 (by rfl) ⟨948785, by rfl⟩ : syracuseStep 1265047 = 1897571) B1897571
theorem B2846105 : Blo 1264450 2846105 := bstep (se 2 (by rfl) ⟨1067289, by rfl⟩ : syracuseStep 2846105 = 2134579) B2134579
theorem B1265067 : Blo 1264450 1265067 := bstep (se 1 (by rfl) ⟨948800, by rfl⟩ : syracuseStep 1265067 = 1897601) B1897601
theorem B20811185 : Blo 1264450 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B4804019 : Blo 1264450 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B1265079 : Blo 1264450 1265079 := bstep (se 1 (by rfl) ⟨948809, by rfl⟩ : syracuseStep 1265079 = 1897619) B1897619
theorem B1265099 : Blo 1264450 1265099 := bstep (se 1 (by rfl) ⟨948824, by rfl⟩ : syracuseStep 1265099 = 1897649) B1897649
theorem B2739659 : Blo 1264450 2739659 := bstep (se 1 (by rfl) ⟨2054744, by rfl⟩ : syracuseStep 2739659 = 4109489) B4109489
theorem B1265111 : Blo 1264450 1265111 := bstep (se 1 (by rfl) ⟨948833, by rfl⟩ : syracuseStep 1265111 = 1897667) B1897667
theorem B1265131 : Blo 1264450 1265131 := bstep (se 1 (by rfl) ⟨948848, by rfl⟩ : syracuseStep 1265131 = 1897697) B1897697
theorem B2846195 : Blo 1264450 2846195 := bstep (se 1 (by rfl) ⟨2134646, by rfl⟩ : syracuseStep 2846195 = 4269293) B4269293
theorem B1265143 : Blo 1264450 1265143 := bstep (se 1 (by rfl) ⟨948857, by rfl⟩ : syracuseStep 1265143 = 1897715) B1897715
theorem B1265163 : Blo 1264450 1265163 := bstep (se 1 (by rfl) ⟨948872, by rfl⟩ : syracuseStep 1265163 = 1897745) B1897745
theorem B15388177 : Blo 1264450 15388177 := bstep (se 2 (by rfl) ⟨5770566, by rfl⟩ : syracuseStep 15388177 = 11541133) B11541133
theorem B2846231 : Blo 1264450 2846231 := bstep (se 1 (by rfl) ⟨2134673, by rfl⟩ : syracuseStep 2846231 = 4269347) B4269347
theorem B1265175 : Blo 1264450 1265175 := bstep (se 1 (by rfl) ⟨948881, by rfl⟩ : syracuseStep 1265175 = 1897763) B1897763
theorem B1265195 : Blo 1264450 1265195 := bstep (se 1 (by rfl) ⟨948896, by rfl⟩ : syracuseStep 1265195 = 1897793) B1897793
theorem B1265207 : Blo 1264450 1265207 := bstep (se 1 (by rfl) ⟨948905, by rfl⟩ : syracuseStep 1265207 = 1897811) B1897811
theorem B1265227 : Blo 1264450 1265227 := bstep (se 1 (by rfl) ⟨948920, by rfl⟩ : syracuseStep 1265227 = 1897841) B1897841
theorem B1265239 : Blo 1264450 1265239 := bstep (se 1 (by rfl) ⟨948929, by rfl⟩ : syracuseStep 1265239 = 1897859) B1897859
theorem B1265259 : Blo 1264450 1265259 := bstep (se 1 (by rfl) ⟨948944, by rfl⟩ : syracuseStep 1265259 = 1897889) B1897889
theorem B1265271 : Blo 1264450 1265271 := bstep (se 1 (by rfl) ⟨948953, by rfl⟩ : syracuseStep 1265271 = 1897907) B1897907
theorem B1265291 : Blo 1264450 1265291 := bstep (se 1 (by rfl) ⟨948968, by rfl⟩ : syracuseStep 1265291 = 1897937) B1897937
theorem B1265303 : Blo 1264450 1265303 := bstep (se 1 (by rfl) ⟨948977, by rfl⟩ : syracuseStep 1265303 = 1897955) B1897955
theorem B1265323 : Blo 1264450 1265323 := bstep (se 1 (by rfl) ⟨948992, by rfl⟩ : syracuseStep 1265323 = 1897985) B1897985
theorem B5402285 : Blo 1264450 5402285 := bstep (se 3 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 5402285 = 2025857) B2025857
theorem B1265335 : Blo 1264450 1265335 := bstep (se 1 (by rfl) ⟨949001, by rfl⟩ : syracuseStep 1265335 = 1898003) B1898003
theorem B5476043 : Blo 1264450 5476043 := bstep (se 1 (by rfl) ⟨4107032, by rfl⟩ : syracuseStep 5476043 = 8214065) B8214065
theorem B2846411 : Blo 1264450 2846411 := bstep (se 1 (by rfl) ⟨2134808, by rfl⟩ : syracuseStep 2846411 = 4269617) B4269617
theorem B1265355 : Blo 1264450 1265355 := bstep (se 1 (by rfl) ⟨949016, by rfl⟩ : syracuseStep 1265355 = 1898033) B1898033
theorem B1265367 : Blo 1264450 1265367 := bstep (se 1 (by rfl) ⟨949025, by rfl⟩ : syracuseStep 1265367 = 1898051) B1898051
theorem B6401753 : Blo 1264450 6401753 := bstep (se 2 (by rfl) ⟨2400657, by rfl⟩ : syracuseStep 6401753 = 4801315) B4801315
theorem B1265387 : Blo 1264450 1265387 := bstep (se 1 (by rfl) ⟨949040, by rfl⟩ : syracuseStep 1265387 = 1898081) B1898081
theorem B1265399 : Blo 1264450 1265399 := bstep (se 1 (by rfl) ⟨949049, by rfl⟩ : syracuseStep 1265399 = 1898099) B1898099
theorem B2846465 : Blo 1264450 2846465 := bstep (se 2 (by rfl) ⟨1067424, by rfl⟩ : syracuseStep 2846465 = 2134849) B2134849
theorem B1265419 : Blo 1264450 1265419 := bstep (se 1 (by rfl) ⟨949064, by rfl⟩ : syracuseStep 1265419 = 1898129) B1898129
theorem B1265431 : Blo 1264450 1265431 := bstep (se 1 (by rfl) ⟨949073, by rfl⟩ : syracuseStep 1265431 = 1898147) B1898147
theorem B1265451 : Blo 1264450 1265451 := bstep (se 1 (by rfl) ⟨949088, by rfl⟩ : syracuseStep 1265451 = 1898177) B1898177
theorem B1265463 : Blo 1264450 1265463 := bstep (se 1 (by rfl) ⟨949097, by rfl⟩ : syracuseStep 1265463 = 1898195) B1898195
theorem B29200193 : Blo 1264450 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B1265483 : Blo 1264450 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B1265495 : Blo 1264450 1265495 := bstep (se 1 (by rfl) ⟨949121, by rfl⟩ : syracuseStep 1265495 = 1898243) B1898243
theorem B6082397 : Blo 1264450 6082397 := bstep (se 3 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 6082397 = 2280899) B2280899
theorem B1265515 : Blo 1264450 1265515 := bstep (se 1 (by rfl) ⟨949136, by rfl⟩ : syracuseStep 1265515 = 1898273) B1898273
theorem B1265527 : Blo 1264450 1265527 := bstep (se 1 (by rfl) ⟨949145, by rfl⟩ : syracuseStep 1265527 = 1898291) B1898291
theorem B1265547 : Blo 1264450 1265547 := bstep (se 1 (by rfl) ⟨949160, by rfl⟩ : syracuseStep 1265547 = 1898321) B1898321
theorem B2404235 : Blo 1264450 2404235 := bstep (se 1 (by rfl) ⟨1803176, by rfl⟩ : syracuseStep 2404235 = 3606353) B3606353
theorem B2133911 : Blo 1264450 2133911 := bstep (se 1 (by rfl) ⟨1600433, by rfl⟩ : syracuseStep 2133911 = 3200867) B3200867
theorem B1265559 : Blo 1264450 1265559 := bstep (se 1 (by rfl) ⟨949169, by rfl⟩ : syracuseStep 1265559 = 1898339) B1898339
theorem B1265579 : Blo 1264450 1265579 := bstep (se 1 (by rfl) ⟨949184, by rfl⟩ : syracuseStep 1265579 = 1898369) B1898369
theorem B1265591 : Blo 1264450 1265591 := bstep (se 1 (by rfl) ⟨949193, by rfl⟩ : syracuseStep 1265591 = 1898387) B1898387
theorem B1265611 : Blo 1264450 1265611 := bstep (se 1 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 1265611 = 1898417) B1898417
theorem B1265623 : Blo 1264450 1265623 := bstep (se 1 (by rfl) ⟨949217, by rfl⟩ : syracuseStep 1265623 = 1898435) B1898435
theorem B2846681 : Blo 1264450 2846681 := bstep (se 2 (by rfl) ⟨1067505, by rfl⟩ : syracuseStep 2846681 = 2135011) B2135011
theorem B1265643 : Blo 1264450 1265643 := bstep (se 1 (by rfl) ⟨949232, by rfl⟩ : syracuseStep 1265643 = 1898465) B1898465
theorem B1265655 : Blo 1264450 1265655 := bstep (se 1 (by rfl) ⟨949241, by rfl⟩ : syracuseStep 1265655 = 1898483) B1898483
theorem B1265675 : Blo 1264450 1265675 := bstep (se 1 (by rfl) ⟨949256, by rfl⟩ : syracuseStep 1265675 = 1898513) B1898513
theorem B2134039 : Blo 1264450 2134039 := bstep (se 1 (by rfl) ⟨1600529, by rfl⟩ : syracuseStep 2134039 = 3201059) B3201059
theorem B1265687 : Blo 1264450 1265687 := bstep (se 1 (by rfl) ⟨949265, by rfl⟩ : syracuseStep 1265687 = 1898531) B1898531
theorem B1265707 : Blo 1264450 1265707 := bstep (se 1 (by rfl) ⟨949280, by rfl⟩ : syracuseStep 1265707 = 1898561) B1898561
theorem B2846771 : Blo 1264450 2846771 := bstep (se 1 (by rfl) ⟨2135078, by rfl⟩ : syracuseStep 2846771 = 4270157) B4270157
theorem B1265719 : Blo 1264450 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B1265739 : Blo 1264450 1265739 := bstep (se 1 (by rfl) ⟨949304, by rfl⟩ : syracuseStep 1265739 = 1898609) B1898609
theorem B2846807 : Blo 1264450 2846807 := bstep (se 1 (by rfl) ⟨2135105, by rfl⟩ : syracuseStep 2846807 = 4270211) B4270211
theorem B1601623 : Blo 1264450 1601623 := bstep (se 1 (by rfl) ⟨1201217, by rfl⟩ : syracuseStep 1601623 = 2402435) B2402435
theorem B1265751 : Blo 1264450 1265751 := bstep (se 1 (by rfl) ⟨949313, by rfl⟩ : syracuseStep 1265751 = 1898627) B1898627
theorem B1265771 : Blo 1264450 1265771 := bstep (se 1 (by rfl) ⟨949328, by rfl⟩ : syracuseStep 1265771 = 1898657) B1898657
theorem B1265783 : Blo 1264450 1265783 := bstep (se 1 (by rfl) ⟨949337, by rfl⟩ : syracuseStep 1265783 = 1898675) B1898675
theorem B1265803 : Blo 1264450 1265803 := bstep (se 1 (by rfl) ⟨949352, by rfl⟩ : syracuseStep 1265803 = 1898705) B1898705
theorem B4558999 : Blo 1264450 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B1265815 : Blo 1264450 1265815 := bstep (se 1 (by rfl) ⟨949361, by rfl⟩ : syracuseStep 1265815 = 1898723) B1898723
theorem B1265835 : Blo 1264450 1265835 := bstep (se 1 (by rfl) ⟨949376, by rfl⟩ : syracuseStep 1265835 = 1898753) B1898753
theorem B10809521 : Blo 1264450 10809521 := bstep (se 2 (by rfl) ⟨4053570, by rfl⟩ : syracuseStep 10809521 = 8107141) B8107141
theorem B1265847 : Blo 1264450 1265847 := bstep (se 1 (by rfl) ⟨949385, by rfl⟩ : syracuseStep 1265847 = 1898771) B1898771
theorem B1265867 : Blo 1264450 1265867 := bstep (se 1 (by rfl) ⟨949400, by rfl⟩ : syracuseStep 1265867 = 1898801) B1898801
theorem B1265879 : Blo 1264450 1265879 := bstep (se 1 (by rfl) ⟨949409, by rfl⟩ : syracuseStep 1265879 = 1898819) B1898819
theorem B1265899 : Blo 1264450 1265899 := bstep (se 1 (by rfl) ⟨949424, by rfl⟩ : syracuseStep 1265899 = 1898849) B1898849
theorem B1265911 : Blo 1264450 1265911 := bstep (se 1 (by rfl) ⟨949433, by rfl⟩ : syracuseStep 1265911 = 1898867) B1898867
theorem B2846987 : Blo 1264450 2846987 := bstep (se 1 (by rfl) ⟨2135240, by rfl⟩ : syracuseStep 2846987 = 4270481) B4270481
theorem B1265931 : Blo 1264450 1265931 := bstep (se 1 (by rfl) ⟨949448, by rfl⟩ : syracuseStep 1265931 = 1898897) B1898897
theorem B1265943 : Blo 1264450 1265943 := bstep (se 1 (by rfl) ⟨949457, by rfl⟩ : syracuseStep 1265943 = 1898915) B1898915
theorem B1265963 : Blo 1264450 1265963 := bstep (se 1 (by rfl) ⟨949472, by rfl⟩ : syracuseStep 1265963 = 1898945) B1898945
theorem B1265975 : Blo 1264450 1265975 := bstep (se 1 (by rfl) ⟨949481, by rfl⟩ : syracuseStep 1265975 = 1898963) B1898963
theorem B2847041 : Blo 1264450 2847041 := bstep (se 2 (by rfl) ⟨1067640, by rfl⟩ : syracuseStep 2847041 = 2135281) B2135281
theorem B1896779 : Blo 1264450 1896779 := bstep (se 1 (by rfl) ⟨1422584, by rfl⟩ : syracuseStep 1896779 = 2845169) B2845169
theorem B1265995 : Blo 1264450 1265995 := bstep (se 1 (by rfl) ⟨949496, by rfl⟩ : syracuseStep 1265995 = 1898993) B1898993
theorem B1896791 : Blo 1264450 1896791 := bstep (se 1 (by rfl) ⟨1422593, by rfl⟩ : syracuseStep 1896791 = 2845187) B2845187
theorem B1266007 : Blo 1264450 1266007 := bstep (se 1 (by rfl) ⟨949505, by rfl⟩ : syracuseStep 1266007 = 1899011) B1899011
theorem B5402969 : Blo 1264450 5402969 := bstep (se 2 (by rfl) ⟨2026113, by rfl⟩ : syracuseStep 5402969 = 4052227) B4052227
theorem B1266027 : Blo 1264450 1266027 := bstep (se 1 (by rfl) ⟨949520, by rfl⟩ : syracuseStep 1266027 = 1899041) B1899041
theorem B1266039 : Blo 1264450 1266039 := bstep (se 1 (by rfl) ⟨949529, by rfl⟩ : syracuseStep 1266039 = 1899059) B1899059
theorem B1266059 : Blo 1264450 1266059 := bstep (se 1 (by rfl) ⟨949544, by rfl⟩ : syracuseStep 1266059 = 1899089) B1899089
theorem B1266071 : Blo 1264450 1266071 := bstep (se 1 (by rfl) ⟨949553, by rfl⟩ : syracuseStep 1266071 = 1899107) B1899107
theorem B1896857 : Blo 1264450 1896857 := bstep (se 2 (by rfl) ⟨711321, by rfl⟩ : syracuseStep 1896857 = 1422643) B1422643
theorem B2470297 : Blo 1264450 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B1266091 : Blo 1264450 1266091 := bstep (se 1 (by rfl) ⟨949568, by rfl⟩ : syracuseStep 1266091 = 1899137) B1899137
theorem B1266103 : Blo 1264450 1266103 := bstep (se 1 (by rfl) ⟨949577, by rfl⟩ : syracuseStep 1266103 = 1899155) B1899155
theorem B2281921 : Blo 1264450 2281921 := bstep (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) B1711441
theorem B4272587 : Blo 1264450 4272587 := bstep (se 1 (by rfl) ⟨3204440, by rfl⟩ : syracuseStep 4272587 = 6408881) B6408881
theorem B1266123 : Blo 1264450 1266123 := bstep (se 1 (by rfl) ⟨949592, by rfl⟩ : syracuseStep 1266123 = 1899185) B1899185
theorem B1266135 : Blo 1264450 1266135 := bstep (se 1 (by rfl) ⟨949601, by rfl⟩ : syracuseStep 1266135 = 1899203) B1899203
theorem B1266155 : Blo 1264450 1266155 := bstep (se 1 (by rfl) ⟨949616, by rfl⟩ : syracuseStep 1266155 = 1899233) B1899233
theorem B1266167 : Blo 1264450 1266167 := bstep (se 1 (by rfl) ⟨949625, by rfl⟩ : syracuseStep 1266167 = 1899251) B1899251
theorem B1896971 : Blo 1264450 1896971 := bstep (se 1 (by rfl) ⟨1422728, by rfl⟩ : syracuseStep 1896971 = 2845457) B2845457
theorem B1266187 : Blo 1264450 1266187 := bstep (se 1 (by rfl) ⟨949640, by rfl⟩ : syracuseStep 1266187 = 1899281) B1899281
theorem B6844945 : Blo 1264450 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B1896983 : Blo 1264450 1896983 := bstep (se 1 (by rfl) ⟨1422737, by rfl⟩ : syracuseStep 1896983 = 2845475) B2845475
theorem B1266199 : Blo 1264450 1266199 := bstep (se 1 (by rfl) ⟨949649, by rfl⟩ : syracuseStep 1266199 = 1899299) B1899299
theorem B2847257 : Blo 1264450 2847257 := bstep (se 2 (by rfl) ⟨1067721, by rfl⟩ : syracuseStep 2847257 = 2135443) B2135443
theorem B1266219 : Blo 1264450 1266219 := bstep (se 1 (by rfl) ⟨949664, by rfl⟩ : syracuseStep 1266219 = 1899329) B1899329
theorem B1266231 : Blo 1264450 1266231 := bstep (se 1 (by rfl) ⟨949673, by rfl⟩ : syracuseStep 1266231 = 1899347) B1899347
theorem B4108865 : Blo 1264450 4108865 := bstep (se 2 (by rfl) ⟨1540824, by rfl⟩ : syracuseStep 4108865 = 3081649) B3081649
theorem B1266251 : Blo 1264450 1266251 := bstep (se 1 (by rfl) ⟨949688, by rfl⟩ : syracuseStep 1266251 = 1899377) B1899377
theorem B1266263 : Blo 1264450 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B1897049 : Blo 1264450 1897049 := bstep (se 2 (by rfl) ⟨711393, by rfl⟩ : syracuseStep 1897049 = 1422787) B1422787
theorem B1266283 : Blo 1264450 1266283 := bstep (se 1 (by rfl) ⟨949712, by rfl⟩ : syracuseStep 1266283 = 1899425) B1899425
theorem B2847347 : Blo 1264450 2847347 := bstep (se 1 (by rfl) ⟨2135510, by rfl⟩ : syracuseStep 2847347 = 4271021) B4271021
theorem B1266295 : Blo 1264450 1266295 := bstep (se 1 (by rfl) ⟨949721, by rfl⟩ : syracuseStep 1266295 = 1899443) B1899443
theorem B2134667 : Blo 1264450 2134667 := bstep (se 1 (by rfl) ⟨1601000, by rfl⟩ : syracuseStep 2134667 = 3202001) B3202001
theorem B1266315 : Blo 1264450 1266315 := bstep (se 1 (by rfl) ⟨949736, by rfl⟩ : syracuseStep 1266315 = 1899473) B1899473
theorem B2847383 : Blo 1264450 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B1266327 : Blo 1264450 1266327 := bstep (se 1 (by rfl) ⟨949745, by rfl⟩ : syracuseStep 1266327 = 1899491) B1899491
theorem B1266347 : Blo 1264450 1266347 := bstep (se 1 (by rfl) ⟨949760, by rfl⟩ : syracuseStep 1266347 = 1899521) B1899521
theorem B1266359 : Blo 1264450 1266359 := bstep (se 1 (by rfl) ⟨949769, by rfl⟩ : syracuseStep 1266359 = 1899539) B1899539
theorem B1897163 : Blo 1264450 1897163 := bstep (se 1 (by rfl) ⟨1422872, by rfl⟩ : syracuseStep 1897163 = 2845745) B2845745
theorem B1266379 : Blo 1264450 1266379 := bstep (se 1 (by rfl) ⟨949784, by rfl⟩ : syracuseStep 1266379 = 1899569) B1899569
theorem B1897175 : Blo 1264450 1897175 := bstep (se 1 (by rfl) ⟨1422881, by rfl⟩ : syracuseStep 1897175 = 2845763) B2845763
theorem B4272857 : Blo 1264450 4272857 := bstep (se 2 (by rfl) ⟨1602321, by rfl⟩ : syracuseStep 4272857 = 3204643) B3204643
theorem B1266391 : Blo 1264450 1266391 := bstep (se 1 (by rfl) ⟨949793, by rfl⟩ : syracuseStep 1266391 = 1899587) B1899587
theorem B3420893 : Blo 1264450 3420893 := bstep (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) B1282835
theorem B1266411 : Blo 1264450 1266411 := bstep (se 1 (by rfl) ⟨949808, by rfl⟩ : syracuseStep 1266411 = 1899617) B1899617
theorem B1266423 : Blo 1264450 1266423 := bstep (se 1 (by rfl) ⟨949817, by rfl⟩ : syracuseStep 1266423 = 1899635) B1899635
theorem B2134795 : Blo 1264450 2134795 := bstep (se 1 (by rfl) ⟨1601096, by rfl⟩ : syracuseStep 2134795 = 3202193) B3202193
theorem B1266443 : Blo 1264450 1266443 := bstep (se 1 (by rfl) ⟨949832, by rfl⟩ : syracuseStep 1266443 = 1899665) B1899665
theorem B1520407 : Blo 1264450 1520407 := bstep (se 1 (by rfl) ⟨1140305, by rfl⟩ : syracuseStep 1520407 = 2280611) B2280611
theorem B1897241 : Blo 1264450 1897241 := bstep (se 2 (by rfl) ⟨711465, by rfl⟩ : syracuseStep 1897241 = 1422931) B1422931
theorem B4051777 : Blo 1264450 4051777 := bstep (se 2 (by rfl) ⟨1519416, by rfl⟩ : syracuseStep 4051777 = 3038833) B3038833
theorem B2847563 : Blo 1264450 2847563 := bstep (se 1 (by rfl) ⟨2135672, by rfl⟩ : syracuseStep 2847563 = 4271345) B4271345
theorem B10810205 : Blo 1264450 10810205 := bstep (se 3 (by rfl) ⟨2026913, by rfl⟩ : syracuseStep 10810205 = 4053827) B4053827
theorem B2847617 : Blo 1264450 2847617 := bstep (se 2 (by rfl) ⟨1067856, by rfl⟩ : syracuseStep 2847617 = 2135713) B2135713
theorem B10261379 : Blo 1264450 10261379 := bstep (se 1 (by rfl) ⟨7696034, by rfl⟩ : syracuseStep 10261379 = 15392069) B15392069
theorem B4805507 : Blo 1264450 4805507 := bstep (se 1 (by rfl) ⟨3604130, by rfl⟩ : syracuseStep 4805507 = 7208261) B7208261
theorem B1897355 : Blo 1264450 1897355 := bstep (se 1 (by rfl) ⟨1423016, by rfl⟩ : syracuseStep 1897355 = 2846033) B2846033
theorem B1602443 : Blo 1264450 1602443 := bstep (se 1 (by rfl) ⟨1201832, by rfl⟩ : syracuseStep 1602443 = 2403665) B2403665
theorem B1897367 : Blo 1264450 1897367 := bstep (se 1 (by rfl) ⟨1423025, by rfl⟩ : syracuseStep 1897367 = 2846051) B2846051
theorem B2028439 : Blo 1264450 2028439 := bstep (se 1 (by rfl) ⟨1521329, by rfl⟩ : syracuseStep 2028439 = 3042659) B3042659
theorem B2134937 : Blo 1264450 2134937 := bstep (se 2 (by rfl) ⟨800601, by rfl⟩ : syracuseStep 2134937 = 1601203) B1601203
theorem B2028503 : Blo 1264450 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B1897433 : Blo 1264450 1897433 := bstep (se 2 (by rfl) ⟨711537, by rfl⟩ : syracuseStep 1897433 = 1423075) B1423075
theorem B2135065 : Blo 1264450 2135065 := bstep (se 2 (by rfl) ⟨800649, by rfl⟩ : syracuseStep 2135065 = 1601299) B1601299
theorem B4052033 : Blo 1264450 4052033 := bstep (se 2 (by rfl) ⟨1519512, by rfl⟩ : syracuseStep 4052033 = 3039025) B3039025
theorem B1897547 : Blo 1264450 1897547 := bstep (se 1 (by rfl) ⟨1423160, by rfl⟩ : syracuseStep 1897547 = 2846321) B2846321
theorem B1897559 : Blo 1264450 1897559 := bstep (se 1 (by rfl) ⟨1423169, by rfl⟩ : syracuseStep 1897559 = 2846339) B2846339
theorem B1733719 : Blo 1264450 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B2847833 : Blo 1264450 2847833 := bstep (se 2 (by rfl) ⟨1067937, by rfl⟩ : syracuseStep 2847833 = 2135875) B2135875
theorem B9606275 : Blo 1264450 9606275 := bstep (se 1 (by rfl) ⟨7204706, by rfl⟩ : syracuseStep 9606275 = 14409413) B14409413
theorem B1897625 : Blo 1264450 1897625 := bstep (se 2 (by rfl) ⟨711609, by rfl⟩ : syracuseStep 1897625 = 1423219) B1423219
theorem B2847923 : Blo 1264450 2847923 := bstep (se 1 (by rfl) ⟨2135942, by rfl⟩ : syracuseStep 2847923 = 4271885) B4271885
theorem B2847959 : Blo 1264450 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B1422571 : Blo 1264450 1422571 := bstep (se 1 (by rfl) ⟨1066928, by rfl⟩ : syracuseStep 1422571 = 2133857) B2133857
theorem B1897739 : Blo 1264450 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B1897751 : Blo 1264450 1897751 := bstep (se 1 (by rfl) ⟨1423313, by rfl⟩ : syracuseStep 1897751 = 2846627) B2846627
theorem B6403373 : Blo 1264450 6403373 := bstep (se 3 (by rfl) ⟨1200632, by rfl⟩ : syracuseStep 6403373 = 2401265) B2401265
theorem B3601739 : Blo 1264450 3601739 := bstep (se 1 (by rfl) ⟨2701304, by rfl⟩ : syracuseStep 3601739 = 5402609) B5402609
theorem B4805963 : Blo 1264450 4805963 := bstep (se 1 (by rfl) ⟨3604472, by rfl⟩ : syracuseStep 4805963 = 7208945) B7208945
theorem B1422679 : Blo 1264450 1422679 := bstep (se 1 (by rfl) ⟨1067009, by rfl⟩ : syracuseStep 1422679 = 2134019) B2134019
theorem B1897817 : Blo 1264450 1897817 := bstep (se 2 (by rfl) ⟨711681, by rfl⟩ : syracuseStep 1897817 = 1423363) B1423363
theorem B2848139 : Blo 1264450 2848139 := bstep (se 1 (by rfl) ⟨2136104, by rfl⟩ : syracuseStep 2848139 = 4272209) B4272209
theorem B4273559 : Blo 1264450 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B2848193 : Blo 1264450 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B1897931 : Blo 1264450 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B1897943 : Blo 1264450 1897943 := bstep (se 1 (by rfl) ⟨1423457, by rfl⟩ : syracuseStep 1897943 = 2846915) B2846915
theorem B1422859 : Blo 1264450 1422859 := bstep (se 1 (by rfl) ⟨1067144, by rfl⟩ : syracuseStep 1422859 = 2134289) B2134289
theorem B4806161 : Blo 1264450 4806161 := bstep (se 2 (by rfl) ⟨1802310, by rfl⟩ : syracuseStep 4806161 = 3604621) B3604621
theorem B1898009 : Blo 1264450 1898009 := bstep (se 2 (by rfl) ⟨711753, by rfl⟩ : syracuseStep 1898009 = 1423507) B1423507
theorem B2135639 : Blo 1264450 2135639 := bstep (se 1 (by rfl) ⟨1601729, by rfl⟩ : syracuseStep 2135639 = 3203459) B3203459
theorem B9115229 : Blo 1264450 9115229 := bstep (se 3 (by rfl) ⟨1709105, by rfl⟩ : syracuseStep 9115229 = 3418211) B3418211
theorem B1422967 : Blo 1264450 1422967 := bstep (se 1 (by rfl) ⟨1067225, by rfl⟩ : syracuseStep 1422967 = 2134451) B2134451
theorem B1898123 : Blo 1264450 1898123 := bstep (se 1 (by rfl) ⟨1423592, by rfl⟩ : syracuseStep 1898123 = 2847185) B2847185
theorem B1898135 : Blo 1264450 1898135 := bstep (se 1 (by rfl) ⟨1423601, by rfl⟩ : syracuseStep 1898135 = 2847203) B2847203
theorem B2848409 : Blo 1264450 2848409 := bstep (se 2 (by rfl) ⟨1068153, by rfl⟩ : syracuseStep 2848409 = 2136307) B2136307
theorem B3200705 : Blo 1264450 3200705 := bstep (se 2 (by rfl) ⟨1200264, by rfl⟩ : syracuseStep 3200705 = 2400529) B2400529
theorem B3847873 : Blo 1264450 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B2135767 : Blo 1264450 2135767 := bstep (se 1 (by rfl) ⟨1601825, by rfl⟩ : syracuseStep 2135767 = 3203651) B3203651
theorem B1898201 : Blo 1264450 1898201 := bstep (se 2 (by rfl) ⟨711825, by rfl⟩ : syracuseStep 1898201 = 1423651) B1423651
theorem B2848499 : Blo 1264450 2848499 := bstep (se 1 (by rfl) ⟨2136374, by rfl⟩ : syracuseStep 2848499 = 4272749) B4272749
theorem B2848535 : Blo 1264450 2848535 := bstep (se 1 (by rfl) ⟨2136401, by rfl⟩ : syracuseStep 2848535 = 4272803) B4272803
theorem B1423147 : Blo 1264450 1423147 := bstep (se 1 (by rfl) ⟨1067360, by rfl⟩ : syracuseStep 1423147 = 2134721) B2134721
theorem B3422017 : Blo 1264450 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B4560715 : Blo 1264450 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B1898315 : Blo 1264450 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B1898327 : Blo 1264450 1898327 := bstep (se 1 (by rfl) ⟨1423745, by rfl⟩ : syracuseStep 1898327 = 2847491) B2847491
theorem B1423255 : Blo 1264450 1423255 := bstep (se 1 (by rfl) ⟨1067441, by rfl⟩ : syracuseStep 1423255 = 2134883) B2134883
theorem B1898393 : Blo 1264450 1898393 := bstep (se 2 (by rfl) ⟨711897, by rfl⟩ : syracuseStep 1898393 = 1423795) B1423795
theorem B4274099 : Blo 1264450 4274099 := bstep (se 1 (by rfl) ⟨3205574, by rfl⟩ : syracuseStep 4274099 = 6411149) B6411149
theorem B2848715 : Blo 1264450 2848715 := bstep (se 1 (by rfl) ⟨2136536, by rfl⟩ : syracuseStep 2848715 = 4273073) B4273073
theorem B5478361 : Blo 1264450 5478361 := bstep (se 2 (by rfl) ⟨2054385, by rfl⟩ : syracuseStep 5478361 = 4108771) B4108771
theorem B2848769 : Blo 1264450 2848769 := bstep (se 2 (by rfl) ⟨1068288, by rfl⟩ : syracuseStep 2848769 = 2136577) B2136577
theorem B1898507 : Blo 1264450 1898507 := bstep (se 1 (by rfl) ⟨1423880, by rfl⟩ : syracuseStep 1898507 = 2847761) B2847761
theorem B1898519 : Blo 1264450 1898519 := bstep (se 1 (by rfl) ⟨1423889, by rfl⟩ : syracuseStep 1898519 = 2847779) B2847779
theorem B1423435 : Blo 1264450 1423435 := bstep (se 1 (by rfl) ⟨1067576, by rfl⟩ : syracuseStep 1423435 = 2135153) B2135153
theorem B1898585 : Blo 1264450 1898585 := bstep (se 2 (by rfl) ⟨711969, by rfl⟩ : syracuseStep 1898585 = 1423939) B1423939
theorem B2701441 : Blo 1264450 2701441 := bstep (se 2 (by rfl) ⟨1013040, by rfl⟩ : syracuseStep 2701441 = 2026081) B2026081
theorem B1423543 : Blo 1264450 1423543 := bstep (se 1 (by rfl) ⟨1067657, by rfl⟩ : syracuseStep 1423543 = 2135315) B2135315
theorem B1898699 : Blo 1264450 1898699 := bstep (se 1 (by rfl) ⟨1424024, by rfl⟩ : syracuseStep 1898699 = 2848049) B2848049
theorem B1898711 : Blo 1264450 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B3201241 : Blo 1264450 3201241 := bstep (se 2 (by rfl) ⟨1200465, by rfl⟩ : syracuseStep 3201241 = 2400931) B2400931
theorem B2848985 : Blo 1264450 2848985 := bstep (se 2 (by rfl) ⟨1068369, by rfl⟩ : syracuseStep 2848985 = 2136739) B2136739
theorem B4806935 : Blo 1264450 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B1898777 : Blo 1264450 1898777 := bstep (se 2 (by rfl) ⟨712041, by rfl⟩ : syracuseStep 1898777 = 1424083) B1424083
theorem B5773619 : Blo 1264450 5773619 := bstep (se 1 (by rfl) ⟨4330214, by rfl⟩ : syracuseStep 5773619 = 8660429) B8660429
theorem B2849075 : Blo 1264450 2849075 := bstep (se 1 (by rfl) ⟨2136806, by rfl⟩ : syracuseStep 2849075 = 4273613) B4273613
theorem B2136395 : Blo 1264450 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B2849111 : Blo 1264450 2849111 := bstep (se 1 (by rfl) ⟨2136833, by rfl⟩ : syracuseStep 2849111 = 4273667) B4273667
theorem B1423723 : Blo 1264450 1423723 := bstep (se 1 (by rfl) ⟨1067792, by rfl⟩ : syracuseStep 1423723 = 2135585) B2135585
theorem B14817653 : Blo 1264450 14817653 := bstep (se 5 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 14817653 = 1389155) B1389155
theorem B1898891 : Blo 1264450 1898891 := bstep (se 1 (by rfl) ⟨1424168, by rfl⟩ : syracuseStep 1898891 = 2848337) B2848337
theorem B1898903 : Blo 1264450 1898903 := bstep (se 1 (by rfl) ⟨1424177, by rfl⟩ : syracuseStep 1898903 = 2848355) B2848355
theorem B2136523 : Blo 1264450 2136523 := bstep (se 1 (by rfl) ⟨1602392, by rfl⟩ : syracuseStep 2136523 = 3204785) B3204785
theorem B1423831 : Blo 1264450 1423831 := bstep (se 1 (by rfl) ⟨1067873, by rfl⟩ : syracuseStep 1423831 = 2135747) B2135747
theorem B1898969 : Blo 1264450 1898969 := bstep (se 2 (by rfl) ⟨712113, by rfl⟩ : syracuseStep 1898969 = 1424227) B1424227
theorem B4807133 : Blo 1264450 4807133 := bstep (se 3 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 4807133 = 1802675) B1802675
theorem B2849291 : Blo 1264450 2849291 := bstep (se 1 (by rfl) ⟨2136968, by rfl⟩ : syracuseStep 2849291 = 4273937) B4273937
theorem B2849345 : Blo 1264450 2849345 := bstep (se 2 (by rfl) ⟨1068504, by rfl⟩ : syracuseStep 2849345 = 2137009) B2137009
theorem B1899083 : Blo 1264450 1899083 := bstep (se 1 (by rfl) ⟨1424312, by rfl⟩ : syracuseStep 1899083 = 2848625) B2848625
theorem B1899095 : Blo 1264450 1899095 := bstep (se 1 (by rfl) ⟨1424321, by rfl⟩ : syracuseStep 1899095 = 2848643) B2848643
theorem B2136665 : Blo 1264450 2136665 := bstep (se 2 (by rfl) ⟨801249, by rfl⟩ : syracuseStep 2136665 = 1602499) B1602499
theorem B3603037 : Blo 1264450 3603037 := bstep (se 3 (by rfl) ⟨675569, by rfl⟩ : syracuseStep 3603037 = 1351139) B1351139
theorem B1424011 : Blo 1264450 1424011 := bstep (se 1 (by rfl) ⟨1068008, by rfl⟩ : syracuseStep 1424011 = 2136017) B2136017
theorem B1899161 : Blo 1264450 1899161 := bstep (se 2 (by rfl) ⟨712185, by rfl⟩ : syracuseStep 1899161 = 1424371) B1424371
theorem B10255025 : Blo 1264450 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B2136793 : Blo 1264450 2136793 := bstep (se 2 (by rfl) ⟨801297, by rfl⟩ : syracuseStep 2136793 = 1602595) B1602595
theorem B1350379 : Blo 1264450 1350379 := bstep (se 1 (by rfl) ⟨1012784, by rfl⟩ : syracuseStep 1350379 = 2025569) B2025569
theorem B1424119 : Blo 1264450 1424119 := bstep (se 1 (by rfl) ⟨1068089, by rfl⟩ : syracuseStep 1424119 = 2136179) B2136179
theorem B1899275 : Blo 1264450 1899275 := bstep (se 1 (by rfl) ⟨1424456, by rfl⟩ : syracuseStep 1899275 = 2848913) B2848913
theorem B1899287 : Blo 1264450 1899287 := bstep (se 1 (by rfl) ⟨1424465, by rfl⟩ : syracuseStep 1899287 = 2848931) B2848931
theorem B7805771 : Blo 1264450 7805771 := bstep (se 1 (by rfl) ⟨5854328, by rfl⟩ : syracuseStep 7805771 = 11708657) B11708657
theorem B1899353 : Blo 1264450 1899353 := bstep (se 2 (by rfl) ⟨712257, by rfl⟩ : syracuseStep 1899353 = 1424515) B1424515
theorem B1424299 : Blo 1264450 1424299 := bstep (se 1 (by rfl) ⟨1068224, by rfl⟩ : syracuseStep 1424299 = 2136449) B2136449
theorem B3603379 : Blo 1264450 3603379 := bstep (se 1 (by rfl) ⟨2702534, by rfl⟩ : syracuseStep 3603379 = 5405069) B5405069
theorem B39500723 : Blo 1264450 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B1899467 : Blo 1264450 1899467 := bstep (se 1 (by rfl) ⟨1424600, by rfl⟩ : syracuseStep 1899467 = 2849201) B2849201
theorem B1899479 : Blo 1264450 1899479 := bstep (se 1 (by rfl) ⟨1424609, by rfl⟩ : syracuseStep 1899479 = 2849219) B2849219
theorem B1424407 : Blo 1264450 1424407 := bstep (se 1 (by rfl) ⟨1068305, by rfl⟩ : syracuseStep 1424407 = 2136611) B2136611
theorem B1899545 : Blo 1264450 1899545 := bstep (se 2 (by rfl) ⟨712329, by rfl⟩ : syracuseStep 1899545 = 1424659) B1424659
theorem B1801291 : Blo 1264450 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B1899659 : Blo 1264450 1899659 := bstep (se 1 (by rfl) ⟨1424744, by rfl⟩ : syracuseStep 1899659 = 2849489) B2849489
theorem B1899671 : Blo 1264450 1899671 := bstep (se 1 (by rfl) ⟨1424753, by rfl⟩ : syracuseStep 1899671 = 2849507) B2849507
theorem B1711307 : Blo 1264450 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B1424587 : Blo 1264450 1424587 := bstep (se 1 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 1424587 = 2136881) B2136881
theorem B7691537 : Blo 1264450 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B3202355 : Blo 1264450 3202355 := bstep (se 1 (by rfl) ⟨2401766, by rfl⟩ : syracuseStep 3202355 = 4803533) B4803533
theorem B1424695 : Blo 1264450 1424695 := bstep (se 1 (by rfl) ⟨1068521, by rfl⟩ : syracuseStep 1424695 = 2137043) B2137043
theorem B2563417 : Blo 1264450 2563417 := bstep (se 2 (by rfl) ⟨961281, by rfl⟩ : syracuseStep 2563417 = 1922563) B1922563
theorem B2563481 : Blo 1264450 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B2170327 : Blo 1264450 2170327 := bstep (se 1 (by rfl) ⟨1627745, by rfl⟩ : syracuseStep 2170327 = 3255491) B3255491
theorem B18234841 : Blo 1264450 18234841 := bstep (se 2 (by rfl) ⟨6838065, by rfl⟩ : syracuseStep 18234841 = 13676131) B13676131
theorem B4054493 : Blo 1264450 4054493 := bstep (se 3 (by rfl) ⟨760217, by rfl⟩ : syracuseStep 4054493 = 1520435) B1520435
theorem B7208513 : Blo 1264450 7208513 := bstep (se 2 (by rfl) ⟨2703192, by rfl⟩ : syracuseStep 7208513 = 5406385) B5406385
theorem B23076427 : Blo 1264450 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B3202649 : Blo 1264450 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B5406401 : Blo 1264450 5406401 := bstep (se 2 (by rfl) ⟨2027400, by rfl⟩ : syracuseStep 5406401 = 4054801) B4054801
theorem B3039065 : Blo 1264450 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B3604313 : Blo 1264450 3604313 := bstep (se 2 (by rfl) ⟨1351617, by rfl⟩ : syracuseStep 3604313 = 2703235) B2703235
theorem B4267997 : Blo 1264450 4267997 := bstep (se 3 (by rfl) ⟨800249, by rfl⟩ : syracuseStep 4267997 = 1600499) B1600499
theorem B3604495 : Blo 1264450 3604495 := bstep (se 1 (by rfl) ⟨2703371, by rfl⟩ : syracuseStep 3604495 = 5406743) B5406743
theorem B7692317 : Blo 1264450 7692317 := bstep (se 3 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 7692317 = 2884619) B2884619
theorem B6078493 : Blo 1264450 6078493 := bstep (se 3 (by rfl) ⟨1139717, by rfl⟩ : syracuseStep 6078493 = 2279435) B2279435
theorem B6078665 : Blo 1264450 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B4268321 : Blo 1264450 4268321 := bstep (se 2 (by rfl) ⟨1600620, by rfl⟩ : syracuseStep 4268321 = 3201241) B3201241
theorem B3604769 : Blo 1264450 3604769 := bstep (se 2 (by rfl) ⟨1351788, by rfl⟩ : syracuseStep 3604769 = 2703577) B2703577
theorem B6406451 : Blo 1264450 6406451 := bstep (se 1 (by rfl) ⟨4804838, by rfl⟩ : syracuseStep 6406451 = 9609677) B9609677
theorem B3654173 : Blo 1264450 3654173 := bstep (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) B1370315
theorem B4563485 : Blo 1264450 4563485 := bstep (se 3 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 4563485 = 1711307) B1711307
theorem B3293729 : Blo 1264450 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B6840919 : Blo 1264450 6840919 := bstep (se 1 (by rfl) ⟨5130689, by rfl⟩ : syracuseStep 6840919 = 10261379) B10261379
theorem B3203671 : Blo 1264450 3203671 := bstep (se 1 (by rfl) ⟨2402753, by rfl⟩ : syracuseStep 3203671 = 4805507) B4805507
theorem B6406775 : Blo 1264450 6406775 := bstep (se 1 (by rfl) ⟨4805081, by rfl⟩ : syracuseStep 6406775 = 9610163) B9610163
theorem B3605111 : Blo 1264450 3605111 := bstep (se 1 (by rfl) ⟨2703833, by rfl⟩ : syracuseStep 3605111 = 5407667) B5407667
theorem B9126593 : Blo 1264450 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B4268915 : Blo 1264450 4268915 := bstep (se 1 (by rfl) ⟨3201686, by rfl⟩ : syracuseStep 4268915 = 6403373) B6403373
theorem B2401159 : Blo 1264450 2401159 := bstep (se 1 (by rfl) ⟨1800869, by rfl⟩ : syracuseStep 2401159 = 3601739) B3601739
theorem B3203975 : Blo 1264450 3203975 := bstep (se 1 (by rfl) ⟨2402981, by rfl⟩ : syracuseStep 3203975 = 4805963) B4805963
theorem B3204107 : Blo 1264450 3204107 := bstep (se 1 (by rfl) ⟨2403080, by rfl⟩ : syracuseStep 3204107 = 4806161) B4806161
theorem B6079511 : Blo 1264450 6079511 := bstep (se 1 (by rfl) ⟨4559633, by rfl⟩ : syracuseStep 6079511 = 9119267) B9119267
theorem B11256893 : Blo 1264450 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B2704585 : Blo 1264450 2704585 := bstep (se 2 (by rfl) ⟨1014219, by rfl⟩ : syracuseStep 2704585 = 2028439) B2028439
theorem B6161645 : Blo 1264450 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B3605771 : Blo 1264450 3605771 := bstep (se 1 (by rfl) ⟨2704328, by rfl⟩ : syracuseStep 3605771 = 5408657) B5408657
theorem B7701875 : Blo 1264450 7701875 := bstep (se 1 (by rfl) ⟨5776406, by rfl⟩ : syracuseStep 7701875 = 11552813) B11552813
theorem B2401721 : Blo 1264450 2401721 := bstep (se 2 (by rfl) ⟨900645, by rfl⟩ : syracuseStep 2401721 = 1801291) B1801291
theorem B2311625 : Blo 1264450 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B3204623 : Blo 1264450 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B6407747 : Blo 1264450 6407747 := bstep (se 1 (by rfl) ⟨4805810, by rfl⟩ : syracuseStep 6407747 = 9611621) B9611621
theorem B3204755 : Blo 1264450 3204755 := bstep (se 1 (by rfl) ⟨2403566, by rfl⟩ : syracuseStep 3204755 = 4807133) B4807133
theorem B24323813 : Blo 1264450 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B20539109 : Blo 1264450 20539109 := bstep (se 4 (by rfl) ⟨1925541, by rfl⟩ : syracuseStep 20539109 = 3851083) B3851083
theorem B3417889 : Blo 1264450 3417889 := bstep (se 2 (by rfl) ⟨1281708, by rfl⟩ : syracuseStep 3417889 = 2563417) B2563417
theorem B6408071 : Blo 1264450 6408071 := bstep (se 1 (by rfl) ⟨4806053, by rfl⟩ : syracuseStep 6408071 = 9612107) B9612107
theorem B5203847 : Blo 1264450 5203847 := bstep (se 1 (by rfl) ⟨3902885, by rfl⟩ : syracuseStep 5203847 = 7805771) B7805771
theorem B2893769 : Blo 1264450 2893769 := bstep (se 2 (by rfl) ⟨1085163, by rfl⟩ : syracuseStep 2893769 = 2170327) B2170327
theorem B1443847 : Blo 1264450 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B4327435 : Blo 1264450 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B4327625 : Blo 1264450 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B5130497 : Blo 1264450 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B105335261 : Blo 1264450 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B19466795 : Blo 1264450 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B2026043 : Blo 1264450 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B2402875 : Blo 1264450 2402875 := bstep (se 1 (by rfl) ⟨1802156, by rfl⟩ : syracuseStep 2402875 = 3604313) B3604313
theorem B5409341 : Blo 1264450 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B2845331 : Blo 1264450 2845331 := bstep (se 1 (by rfl) ⟨2133998, by rfl⟩ : syracuseStep 2845331 = 4267997) B4267997
theorem B2845385 : Blo 1264450 2845385 := bstep (se 2 (by rfl) ⟨1067019, by rfl⟩ : syracuseStep 2845385 = 2134039) B2134039
theorem B34630415 : Blo 1264450 34630415 := bstep (se 1 (by rfl) ⟨25972811, by rfl⟩ : syracuseStep 34630415 = 51945623) B51945623
theorem B1264519 : Blo 1264450 1264519 := bstep (se 1 (by rfl) ⟨948389, by rfl⟩ : syracuseStep 1264519 = 1896779) B1896779
theorem B1264527 : Blo 1264450 1264527 := bstep (se 1 (by rfl) ⟨948395, by rfl⟩ : syracuseStep 1264527 = 1896791) B1896791
theorem B12331939 : Blo 1264450 12331939 := bstep (se 1 (by rfl) ⟨9248954, by rfl⟩ : syracuseStep 12331939 = 18497909) B18497909
theorem B1264571 : Blo 1264450 1264571 := bstep (se 1 (by rfl) ⟨948428, by rfl⟩ : syracuseStep 1264571 = 1896857) B1896857
theorem B1264647 : Blo 1264450 1264647 := bstep (se 1 (by rfl) ⟨948485, by rfl⟩ : syracuseStep 1264647 = 1896971) B1896971
theorem B1264655 : Blo 1264450 1264655 := bstep (se 1 (by rfl) ⟨948491, by rfl⟩ : syracuseStep 1264655 = 1896983) B1896983
theorem B2403361 : Blo 1264450 2403361 := bstep (se 2 (by rfl) ⟨901260, by rfl⟩ : syracuseStep 2403361 = 1802521) B1802521
theorem B1600555 : Blo 1264450 1600555 := bstep (se 1 (by rfl) ⟨1200416, by rfl⟩ : syracuseStep 1600555 = 2400833) B2400833
theorem B1264699 : Blo 1264450 1264699 := bstep (se 1 (by rfl) ⟨948524, by rfl⟩ : syracuseStep 1264699 = 1897049) B1897049
theorem B2567227 : Blo 1264450 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B1264775 : Blo 1264450 1264775 := bstep (se 1 (by rfl) ⟨948581, by rfl⟩ : syracuseStep 1264775 = 1897163) B1897163
theorem B1264783 : Blo 1264450 1264783 := bstep (se 1 (by rfl) ⟨948587, by rfl⟩ : syracuseStep 1264783 = 1897175) B1897175
theorem B1264827 : Blo 1264450 1264827 := bstep (se 1 (by rfl) ⟨948620, by rfl⟩ : syracuseStep 1264827 = 1897241) B1897241
theorem B1264903 : Blo 1264450 1264903 := bstep (se 1 (by rfl) ⟨948677, by rfl⟩ : syracuseStep 1264903 = 1897355) B1897355
theorem B1264911 : Blo 1264450 1264911 := bstep (se 1 (by rfl) ⟨948683, by rfl⟩ : syracuseStep 1264911 = 1897367) B1897367
theorem B1264955 : Blo 1264450 1264955 := bstep (se 1 (by rfl) ⟨948716, by rfl⟩ : syracuseStep 1264955 = 1897433) B1897433
theorem B2846087 : Blo 1264450 2846087 := bstep (se 1 (by rfl) ⟨2134565, by rfl⟩ : syracuseStep 2846087 = 4269131) B4269131
theorem B1265031 : Blo 1264450 1265031 := bstep (se 1 (by rfl) ⟨948773, by rfl⟩ : syracuseStep 1265031 = 1897547) B1897547
theorem B1265039 : Blo 1264450 1265039 := bstep (se 1 (by rfl) ⟨948779, by rfl⟩ : syracuseStep 1265039 = 1897559) B1897559
theorem B4271507 : Blo 1264450 4271507 := bstep (se 1 (by rfl) ⟨3203630, by rfl⟩ : syracuseStep 4271507 = 6407261) B6407261
theorem B1265083 : Blo 1264450 1265083 := bstep (se 1 (by rfl) ⟨948812, by rfl⟩ : syracuseStep 1265083 = 1897625) B1897625
theorem B4804049 : Blo 1264450 4804049 := bstep (se 2 (by rfl) ⟨1801518, by rfl⟩ : syracuseStep 4804049 = 3603037) B3603037
theorem B1265159 : Blo 1264450 1265159 := bstep (se 1 (by rfl) ⟨948869, by rfl⟩ : syracuseStep 1265159 = 1897739) B1897739
theorem B1265167 : Blo 1264450 1265167 := bstep (se 1 (by rfl) ⟨948875, by rfl⟩ : syracuseStep 1265167 = 1897751) B1897751
theorem B8105501 : Blo 1264450 8105501 := bstep (se 3 (by rfl) ⟨1519781, by rfl⟩ : syracuseStep 8105501 = 3039563) B3039563
theorem B15593003 : Blo 1264450 15593003 := bstep (se 1 (by rfl) ⟨11694752, by rfl⟩ : syracuseStep 15593003 = 23389505) B23389505
theorem B2846267 : Blo 1264450 2846267 := bstep (se 1 (by rfl) ⟨2134700, by rfl⟩ : syracuseStep 2846267 = 4269401) B4269401
theorem B1265211 : Blo 1264450 1265211 := bstep (se 1 (by rfl) ⟨948908, by rfl⟩ : syracuseStep 1265211 = 1897817) B1897817
theorem B1265287 : Blo 1264450 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B1265295 : Blo 1264450 1265295 := bstep (se 1 (by rfl) ⟨948971, by rfl⟩ : syracuseStep 1265295 = 1897943) B1897943
theorem B2846393 : Blo 1264450 2846393 := bstep (se 2 (by rfl) ⟨1067397, by rfl⟩ : syracuseStep 2846393 = 2134795) B2134795
theorem B1265339 : Blo 1264450 1265339 := bstep (se 1 (by rfl) ⟨949004, by rfl⟩ : syracuseStep 1265339 = 1898009) B1898009
theorem B2027209 : Blo 1264450 2027209 := bstep (se 2 (by rfl) ⟨760203, by rfl⟩ : syracuseStep 2027209 = 1520407) B1520407
theorem B5402369 : Blo 1264450 5402369 := bstep (se 2 (by rfl) ⟨2025888, by rfl⟩ : syracuseStep 5402369 = 4051777) B4051777
theorem B1265415 : Blo 1264450 1265415 := bstep (se 1 (by rfl) ⟨949061, by rfl⟩ : syracuseStep 1265415 = 1898123) B1898123
theorem B13676303 : Blo 1264450 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B1265423 : Blo 1264450 1265423 := bstep (se 1 (by rfl) ⟨949067, by rfl⟩ : syracuseStep 1265423 = 1898135) B1898135
theorem B2133803 : Blo 1264450 2133803 := bstep (se 1 (by rfl) ⟨1600352, by rfl⟩ : syracuseStep 2133803 = 3200705) B3200705
theorem B1265467 : Blo 1264450 1265467 := bstep (se 1 (by rfl) ⟨949100, by rfl⟩ : syracuseStep 1265467 = 1898201) B1898201
theorem B1265543 : Blo 1264450 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B1265551 : Blo 1264450 1265551 := bstep (se 1 (by rfl) ⟨949163, by rfl⟩ : syracuseStep 1265551 = 1898327) B1898327
theorem B4804505 : Blo 1264450 4804505 := bstep (se 2 (by rfl) ⟨1801689, by rfl⟩ : syracuseStep 4804505 = 3603379) B3603379
theorem B1265595 : Blo 1264450 1265595 := bstep (se 1 (by rfl) ⟨949196, by rfl⟩ : syracuseStep 1265595 = 1898393) B1898393
theorem B1601527 : Blo 1264450 1601527 := bstep (se 1 (by rfl) ⟨1201145, by rfl⟩ : syracuseStep 1601527 = 2402291) B2402291
theorem B1265671 : Blo 1264450 1265671 := bstep (se 1 (by rfl) ⟨949253, by rfl⟩ : syracuseStep 1265671 = 1898507) B1898507
theorem B2846735 : Blo 1264450 2846735 := bstep (se 1 (by rfl) ⟨2135051, by rfl⟩ : syracuseStep 2846735 = 4270103) B4270103
theorem B1265679 : Blo 1264450 1265679 := bstep (se 1 (by rfl) ⟨949259, by rfl⟩ : syracuseStep 1265679 = 1898519) B1898519
theorem B6402077 : Blo 1264450 6402077 := bstep (se 3 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 6402077 = 2400779) B2400779
theorem B2846753 : Blo 1264450 2846753 := bstep (se 2 (by rfl) ⟨1067532, by rfl⟩ : syracuseStep 2846753 = 2135065) B2135065
theorem B1265723 : Blo 1264450 1265723 := bstep (se 1 (by rfl) ⟨949292, by rfl⟩ : syracuseStep 1265723 = 1898585) B1898585
theorem B1265799 : Blo 1264450 1265799 := bstep (se 1 (by rfl) ⟨949349, by rfl⟩ : syracuseStep 1265799 = 1898699) B1898699
theorem B1265807 : Blo 1264450 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B10956973 : Blo 1264450 10956973 := bstep (se 3 (by rfl) ⟨2054432, by rfl⟩ : syracuseStep 10956973 = 4108865) B4108865
theorem B2134201 : Blo 1264450 2134201 := bstep (se 2 (by rfl) ⟨800325, by rfl⟩ : syracuseStep 2134201 = 1600651) B1600651
theorem B1265851 : Blo 1264450 1265851 := bstep (se 1 (by rfl) ⟨949388, by rfl⟩ : syracuseStep 1265851 = 1898777) B1898777
theorem B1896695 : Blo 1264450 1896695 := bstep (se 1 (by rfl) ⟨1422521, by rfl⟩ : syracuseStep 1896695 = 2845043) B2845043
theorem B1265927 : Blo 1264450 1265927 := bstep (se 1 (by rfl) ⟨949445, by rfl⟩ : syracuseStep 1265927 = 1898891) B1898891
theorem B1896719 : Blo 1264450 1896719 := bstep (se 1 (by rfl) ⟨1422539, by rfl⟩ : syracuseStep 1896719 = 2845079) B2845079
theorem B1265935 : Blo 1264450 1265935 := bstep (se 1 (by rfl) ⟨949451, by rfl⟩ : syracuseStep 1265935 = 1898903) B1898903
theorem B1896761 : Blo 1264450 1896761 := bstep (se 2 (by rfl) ⟨711285, by rfl⟩ : syracuseStep 1896761 = 1422571) B1422571
theorem B1519931 : Blo 1264450 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B1601851 : Blo 1264450 1601851 := bstep (se 1 (by rfl) ⟨1201388, by rfl⟩ : syracuseStep 1601851 = 2402777) B2402777
theorem B1265979 : Blo 1264450 1265979 := bstep (se 1 (by rfl) ⟨949484, by rfl⟩ : syracuseStep 1265979 = 1898969) B1898969
theorem B2847095 : Blo 1264450 2847095 := bstep (se 1 (by rfl) ⟨2135321, by rfl⟩ : syracuseStep 2847095 = 4270643) B4270643
theorem B1896839 : Blo 1264450 1896839 := bstep (se 1 (by rfl) ⟨1422629, by rfl⟩ : syracuseStep 1896839 = 2845259) B2845259
theorem B1266055 : Blo 1264450 1266055 := bstep (se 1 (by rfl) ⟨949541, by rfl⟩ : syracuseStep 1266055 = 1899083) B1899083
theorem B1266063 : Blo 1264450 1266063 := bstep (se 1 (by rfl) ⟨949547, by rfl⟩ : syracuseStep 1266063 = 1899095) B1899095
theorem B1896875 : Blo 1264450 1896875 := bstep (se 1 (by rfl) ⟨1422656, by rfl⟩ : syracuseStep 1896875 = 2845313) B2845313
theorem B8106425 : Blo 1264450 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B1266107 : Blo 1264450 1266107 := bstep (se 1 (by rfl) ⟨949580, by rfl⟩ : syracuseStep 1266107 = 1899161) B1899161
theorem B1896905 : Blo 1264450 1896905 := bstep (se 2 (by rfl) ⟨711339, by rfl⟩ : syracuseStep 1896905 = 1422679) B1422679
theorem B6836683 : Blo 1264450 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B19468765 : Blo 1264450 19468765 := bstep (se 3 (by rfl) ⟨3650393, by rfl⟩ : syracuseStep 19468765 = 7300787) B7300787
theorem B6402563 : Blo 1264450 6402563 := bstep (se 1 (by rfl) ⟨4801922, by rfl⟩ : syracuseStep 6402563 = 9603845) B9603845
theorem B1266183 : Blo 1264450 1266183 := bstep (se 1 (by rfl) ⟨949637, by rfl⟩ : syracuseStep 1266183 = 1899275) B1899275
theorem B1266191 : Blo 1264450 1266191 := bstep (se 1 (by rfl) ⟨949643, by rfl⟩ : syracuseStep 1266191 = 1899287) B1899287
theorem B14602781 : Blo 1264450 14602781 := bstep (se 3 (by rfl) ⟨2738021, by rfl⟩ : syracuseStep 14602781 = 5476043) B5476043
theorem B2847275 : Blo 1264450 2847275 := bstep (se 1 (by rfl) ⟨2135456, by rfl⟩ : syracuseStep 2847275 = 4270913) B4270913
theorem B1897019 : Blo 1264450 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B1266235 : Blo 1264450 1266235 := bstep (se 1 (by rfl) ⟨949676, by rfl⟩ : syracuseStep 1266235 = 1899353) B1899353
theorem B9122381 : Blo 1264450 9122381 := bstep (se 3 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 9122381 = 3420893) B3420893
theorem B1897079 : Blo 1264450 1897079 := bstep (se 1 (by rfl) ⟨1422809, by rfl⟩ : syracuseStep 1897079 = 2845619) B2845619
theorem B1266311 : Blo 1264450 1266311 := bstep (se 1 (by rfl) ⟨949733, by rfl⟩ : syracuseStep 1266311 = 1899467) B1899467
theorem B1897103 : Blo 1264450 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B1266319 : Blo 1264450 1266319 := bstep (se 1 (by rfl) ⟨949739, by rfl⟩ : syracuseStep 1266319 = 1899479) B1899479
theorem B1897145 : Blo 1264450 1897145 := bstep (se 2 (by rfl) ⟨711429, by rfl⟩ : syracuseStep 1897145 = 1422859) B1422859
theorem B1266363 : Blo 1264450 1266363 := bstep (se 1 (by rfl) ⟨949772, by rfl⟩ : syracuseStep 1266363 = 1899545) B1899545
theorem B20517569 : Blo 1264450 20517569 := bstep (se 2 (by rfl) ⟨7694088, by rfl⟩ : syracuseStep 20517569 = 15388177) B15388177
theorem B1897223 : Blo 1264450 1897223 := bstep (se 1 (by rfl) ⟨1422917, by rfl⟩ : syracuseStep 1897223 = 2845835) B2845835
theorem B1266439 : Blo 1264450 1266439 := bstep (se 1 (by rfl) ⟨949829, by rfl⟩ : syracuseStep 1266439 = 1899659) B1899659
theorem B16216847 : Blo 1264450 16216847 := bstep (se 1 (by rfl) ⟨12162635, by rfl⟩ : syracuseStep 16216847 = 24325271) B24325271
theorem B4272911 : Blo 1264450 4272911 := bstep (se 1 (by rfl) ⟨3204683, by rfl⟩ : syracuseStep 4272911 = 6409367) B6409367
theorem B1266447 : Blo 1264450 1266447 := bstep (se 1 (by rfl) ⟨949835, by rfl⟩ : syracuseStep 1266447 = 1899671) B1899671
theorem B1897259 : Blo 1264450 1897259 := bstep (se 1 (by rfl) ⟨1422944, by rfl⟩ : syracuseStep 1897259 = 2845889) B2845889
theorem B1897289 : Blo 1264450 1897289 := bstep (se 2 (by rfl) ⟨711483, by rfl⟩ : syracuseStep 1897289 = 1422967) B1422967
theorem B2134903 : Blo 1264450 2134903 := bstep (se 1 (by rfl) ⟨1601177, by rfl⟩ : syracuseStep 2134903 = 3202355) B3202355
theorem B2847635 : Blo 1264450 2847635 := bstep (se 1 (by rfl) ⟨2135726, by rfl⟩ : syracuseStep 2847635 = 4271453) B4271453
theorem B1708987 : Blo 1264450 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B1897403 : Blo 1264450 1897403 := bstep (se 1 (by rfl) ⟨1423052, by rfl⟩ : syracuseStep 1897403 = 2846105) B2846105
theorem B2847689 : Blo 1264450 2847689 := bstep (se 2 (by rfl) ⟨1067883, by rfl⟩ : syracuseStep 2847689 = 2135767) B2135767
theorem B13874123 : Blo 1264450 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B1897463 : Blo 1264450 1897463 := bstep (se 1 (by rfl) ⟨1423097, by rfl⟩ : syracuseStep 1897463 = 2846195) B2846195
theorem B12170245 : Blo 1264450 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B1897487 : Blo 1264450 1897487 := bstep (se 1 (by rfl) ⟨1423115, by rfl⟩ : syracuseStep 1897487 = 2846231) B2846231
theorem B4273181 : Blo 1264450 4273181 := bstep (se 3 (by rfl) ⟨801221, by rfl⟩ : syracuseStep 4273181 = 1602443) B1602443
theorem B4805675 : Blo 1264450 4805675 := bstep (se 1 (by rfl) ⟨3604256, by rfl⟩ : syracuseStep 4805675 = 7208513) B7208513
theorem B1897529 : Blo 1264450 1897529 := bstep (se 2 (by rfl) ⟨711573, by rfl⟩ : syracuseStep 1897529 = 1423147) B1423147
theorem B2135099 : Blo 1264450 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B3601523 : Blo 1264450 3601523 := bstep (se 1 (by rfl) ⟨2701142, by rfl⟩ : syracuseStep 3601523 = 5402285) B5402285
theorem B29217925 : Blo 1264450 29217925 := bstep (se 4 (by rfl) ⟨2739180, by rfl⟩ : syracuseStep 29217925 = 5478361) B5478361
theorem B1897607 : Blo 1264450 1897607 := bstep (se 1 (by rfl) ⟨1423205, by rfl⟩ : syracuseStep 1897607 = 2846411) B2846411
theorem B1897643 : Blo 1264450 1897643 := bstep (se 1 (by rfl) ⟨1423232, by rfl⟩ : syracuseStep 1897643 = 2846465) B2846465
theorem B1897673 : Blo 1264450 1897673 := bstep (se 2 (by rfl) ⟨711627, by rfl⟩ : syracuseStep 1897673 = 1423255) B1423255
theorem B9614537 : Blo 1264450 9614537 := bstep (se 2 (by rfl) ⟨3605451, by rfl⟩ : syracuseStep 9614537 = 7210903) B7210903
theorem B1602823 : Blo 1264450 1602823 := bstep (se 1 (by rfl) ⟨1202117, by rfl⟩ : syracuseStep 1602823 = 2404235) B2404235
theorem B1422607 : Blo 1264450 1422607 := bstep (se 1 (by rfl) ⟨1066955, by rfl⟩ : syracuseStep 1422607 = 2133911) B2133911
theorem B1897787 : Blo 1264450 1897787 := bstep (se 1 (by rfl) ⟨1423340, by rfl⟩ : syracuseStep 1897787 = 2846681) B2846681
theorem B1897847 : Blo 1264450 1897847 := bstep (se 1 (by rfl) ⟨1423385, by rfl⟩ : syracuseStep 1897847 = 2846771) B2846771
theorem B1897871 : Blo 1264450 1897871 := bstep (se 1 (by rfl) ⟨1423403, by rfl⟩ : syracuseStep 1897871 = 2846807) B2846807
theorem B1897913 : Blo 1264450 1897913 := bstep (se 2 (by rfl) ⟨711717, by rfl⟩ : syracuseStep 1897913 = 1423435) B1423435
theorem B2135497 : Blo 1264450 2135497 := bstep (se 2 (by rfl) ⟨800811, by rfl⟩ : syracuseStep 2135497 = 1601623) B1601623
theorem B7206347 : Blo 1264450 7206347 := bstep (se 1 (by rfl) ⟨5404760, by rfl⟩ : syracuseStep 7206347 = 10809521) B10809521
theorem B3601921 : Blo 1264450 3601921 := bstep (se 2 (by rfl) ⟨1350720, by rfl⟩ : syracuseStep 3601921 = 2701441) B2701441
theorem B27350531 : Blo 1264450 27350531 := bstep (se 1 (by rfl) ⟨20512898, by rfl⟩ : syracuseStep 27350531 = 41025797) B41025797
theorem B6493699 : Blo 1264450 6493699 := bstep (se 1 (by rfl) ⟨4870274, by rfl⟩ : syracuseStep 6493699 = 9740549) B9740549
theorem B1897991 : Blo 1264450 1897991 := bstep (se 1 (by rfl) ⟨1423493, by rfl⟩ : syracuseStep 1897991 = 2846987) B2846987
theorem B1898027 : Blo 1264450 1898027 := bstep (se 1 (by rfl) ⟨1423520, by rfl⟩ : syracuseStep 1898027 = 2847041) B2847041
theorem B3601979 : Blo 1264450 3601979 := bstep (se 1 (by rfl) ⟨2701484, by rfl⟩ : syracuseStep 3601979 = 5402969) B5402969
theorem B13686337 : Blo 1264450 13686337 := bstep (se 2 (by rfl) ⟨5132376, by rfl⟩ : syracuseStep 13686337 = 10264753) B10264753
theorem B1898057 : Blo 1264450 1898057 := bstep (se 2 (by rfl) ⟨711771, by rfl⟩ : syracuseStep 1898057 = 1423543) B1423543
theorem B2848391 : Blo 1264450 2848391 := bstep (se 1 (by rfl) ⟨2136293, by rfl⟩ : syracuseStep 2848391 = 4272587) B4272587
theorem B21616307 : Blo 1264450 21616307 := bstep (se 1 (by rfl) ⟨16212230, by rfl⟩ : syracuseStep 21616307 = 32424461) B32424461
theorem B1898171 : Blo 1264450 1898171 := bstep (se 1 (by rfl) ⟨1423628, by rfl⟩ : syracuseStep 1898171 = 2847257) B2847257
theorem B1898231 : Blo 1264450 1898231 := bstep (se 1 (by rfl) ⟨1423673, by rfl⟩ : syracuseStep 1898231 = 2847347) B2847347
theorem B1423111 : Blo 1264450 1423111 := bstep (se 1 (by rfl) ⟨1067333, by rfl⟩ : syracuseStep 1423111 = 2134667) B2134667
theorem B1898255 : Blo 1264450 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B1898297 : Blo 1264450 1898297 := bstep (se 2 (by rfl) ⟨711861, by rfl⟩ : syracuseStep 1898297 = 1423723) B1423723
theorem B2848571 : Blo 1264450 2848571 := bstep (se 1 (by rfl) ⟨2136428, by rfl⟩ : syracuseStep 2848571 = 4272857) B4272857
theorem B27383669 : Blo 1264450 27383669 := bstep (se 5 (by rfl) ⟨1283609, by rfl⟩ : syracuseStep 27383669 = 2567219) B2567219
theorem B1898375 : Blo 1264450 1898375 := bstep (se 1 (by rfl) ⟨1423781, by rfl⟩ : syracuseStep 1898375 = 2847563) B2847563
theorem B7206803 : Blo 1264450 7206803 := bstep (se 1 (by rfl) ⟨5405102, by rfl⟩ : syracuseStep 7206803 = 10810205) B10810205
theorem B1898411 : Blo 1264450 1898411 := bstep (se 1 (by rfl) ⟨1423808, by rfl⟩ : syracuseStep 1898411 = 2847617) B2847617
theorem B2848697 : Blo 1264450 2848697 := bstep (se 2 (by rfl) ⟨1068261, by rfl⟩ : syracuseStep 2848697 = 2136523) B2136523
theorem B1423291 : Blo 1264450 1423291 := bstep (se 1 (by rfl) ⟨1067468, by rfl⟩ : syracuseStep 1423291 = 2134937) B2134937
theorem B1898441 : Blo 1264450 1898441 := bstep (se 2 (by rfl) ⟨711915, by rfl⟩ : syracuseStep 1898441 = 1423831) B1423831
theorem B2701355 : Blo 1264450 2701355 := bstep (se 1 (by rfl) ⟨2026016, by rfl⟩ : syracuseStep 2701355 = 4052033) B4052033
theorem B20510765 : Blo 1264450 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B1898555 : Blo 1264450 1898555 := bstep (se 1 (by rfl) ⟨1423916, by rfl⟩ : syracuseStep 1898555 = 2847833) B2847833
theorem B6404183 : Blo 1264450 6404183 := bstep (se 1 (by rfl) ⟨4803137, by rfl⟩ : syracuseStep 6404183 = 9606275) B9606275
theorem B1898615 : Blo 1264450 1898615 := bstep (se 1 (by rfl) ⟨1423961, by rfl⟩ : syracuseStep 1898615 = 2847923) B2847923
theorem B2136199 : Blo 1264450 2136199 := bstep (se 1 (by rfl) ⟨1602149, by rfl⟩ : syracuseStep 2136199 = 3204299) B3204299
theorem B1898639 : Blo 1264450 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B1898681 : Blo 1264450 1898681 := bstep (se 2 (by rfl) ⟨712005, by rfl⟩ : syracuseStep 1898681 = 1424011) B1424011
theorem B1300667 : Blo 1264450 1300667 := bstep (se 1 (by rfl) ⟨975500, by rfl⟩ : syracuseStep 1300667 = 1951001) B1951001
theorem B1898759 : Blo 1264450 1898759 := bstep (se 1 (by rfl) ⟨1424069, by rfl⟩ : syracuseStep 1898759 = 2848139) B2848139
theorem B2849039 : Blo 1264450 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B2849057 : Blo 1264450 2849057 := bstep (se 2 (by rfl) ⟨1068396, by rfl⟩ : syracuseStep 2849057 = 2136793) B2136793
theorem B1898795 : Blo 1264450 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B1800505 : Blo 1264450 1800505 := bstep (se 2 (by rfl) ⟨675189, by rfl⟩ : syracuseStep 1800505 = 1350379) B1350379
theorem B1898825 : Blo 1264450 1898825 := bstep (se 2 (by rfl) ⟨712059, by rfl⟩ : syracuseStep 1898825 = 1424119) B1424119
theorem B6084953 : Blo 1264450 6084953 := bstep (se 2 (by rfl) ⟨2281857, by rfl⟩ : syracuseStep 6084953 = 4563715) B4563715
theorem B1423759 : Blo 1264450 1423759 := bstep (se 1 (by rfl) ⟨1067819, by rfl⟩ : syracuseStep 1423759 = 2135639) B2135639
theorem B6936977 : Blo 1264450 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B6076819 : Blo 1264450 6076819 := bstep (se 1 (by rfl) ⟨4557614, by rfl⟩ : syracuseStep 6076819 = 9115229) B9115229
theorem B1898939 : Blo 1264450 1898939 := bstep (se 1 (by rfl) ⟨1424204, by rfl⟩ : syracuseStep 1898939 = 2848409) B2848409
theorem B5200337 : Blo 1264450 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B1898999 : Blo 1264450 1898999 := bstep (se 1 (by rfl) ⟨1424249, by rfl⟩ : syracuseStep 1898999 = 2848499) B2848499
theorem B1899023 : Blo 1264450 1899023 := bstep (se 1 (by rfl) ⟨1424267, by rfl⟩ : syracuseStep 1899023 = 2848535) B2848535
theorem B7305757 : Blo 1264450 7305757 := bstep (se 3 (by rfl) ⟨1369829, by rfl⟩ : syracuseStep 7305757 = 2739659) B2739659
theorem B13687339 : Blo 1264450 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B1899065 : Blo 1264450 1899065 := bstep (se 2 (by rfl) ⟨712149, by rfl⟩ : syracuseStep 1899065 = 1424299) B1424299
theorem B6404669 : Blo 1264450 6404669 := bstep (se 3 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 6404669 = 2401751) B2401751
theorem B10811981 : Blo 1264450 10811981 := bstep (se 3 (by rfl) ⟨2027246, by rfl⟩ : syracuseStep 10811981 = 4054493) B4054493
theorem B2849399 : Blo 1264450 2849399 := bstep (se 1 (by rfl) ⟨2137049, by rfl⟩ : syracuseStep 2849399 = 4274099) B4274099
theorem B1899143 : Blo 1264450 1899143 := bstep (se 1 (by rfl) ⟨1424357, by rfl⟩ : syracuseStep 1899143 = 2848715) B2848715
theorem B1899179 : Blo 1264450 1899179 := bstep (se 1 (by rfl) ⟨1424384, by rfl⟩ : syracuseStep 1899179 = 2848769) B2848769
theorem B1899209 : Blo 1264450 1899209 := bstep (se 2 (by rfl) ⟨712203, by rfl⟩ : syracuseStep 1899209 = 1424407) B1424407
theorem B2136847 : Blo 1264450 2136847 := bstep (se 1 (by rfl) ⟨1602635, by rfl⟩ : syracuseStep 2136847 = 3205271) B3205271
theorem B1899323 : Blo 1264450 1899323 := bstep (se 1 (by rfl) ⟨1424492, by rfl⟩ : syracuseStep 1899323 = 2848985) B2848985
theorem B3849079 : Blo 1264450 3849079 := bstep (se 1 (by rfl) ⟨2886809, by rfl⟩ : syracuseStep 3849079 = 5773619) B5773619
theorem B1899383 : Blo 1264450 1899383 := bstep (se 1 (by rfl) ⟨1424537, by rfl⟩ : syracuseStep 1899383 = 2849075) B2849075
theorem B1424263 : Blo 1264450 1424263 := bstep (se 1 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 1424263 = 2136395) B2136395
theorem B1899407 : Blo 1264450 1899407 := bstep (se 1 (by rfl) ⟨1424555, by rfl⟩ : syracuseStep 1899407 = 2849111) B2849111
theorem B9878435 : Blo 1264450 9878435 := bstep (se 1 (by rfl) ⟨7408826, by rfl⟩ : syracuseStep 9878435 = 14817653) B14817653
theorem B1899449 : Blo 1264450 1899449 := bstep (se 2 (by rfl) ⟨712293, by rfl⟩ : syracuseStep 1899449 = 1424587) B1424587
theorem B4807633 : Blo 1264450 4807633 := bstep (se 2 (by rfl) ⟨1802862, by rfl⟩ : syracuseStep 4807633 = 3605725) B3605725
theorem B18250757 : Blo 1264450 18250757 := bstep (se 4 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 18250757 = 3422017) B3422017
theorem B1899527 : Blo 1264450 1899527 := bstep (se 1 (by rfl) ⟨1424645, by rfl⟩ : syracuseStep 1899527 = 2849291) B2849291
theorem B3038219 : Blo 1264450 3038219 := bstep (se 1 (by rfl) ⟨2278664, by rfl⟩ : syracuseStep 3038219 = 4557329) B4557329
theorem B1899563 : Blo 1264450 1899563 := bstep (se 1 (by rfl) ⟨1424672, by rfl⟩ : syracuseStep 1899563 = 2849345) B2849345
theorem B1424443 : Blo 1264450 1424443 := bstep (se 1 (by rfl) ⟨1068332, by rfl⟩ : syracuseStep 1424443 = 2136665) B2136665
theorem B1899593 : Blo 1264450 1899593 := bstep (se 2 (by rfl) ⟨712347, by rfl⟩ : syracuseStep 1899593 = 1424695) B1424695
theorem B3202163 : Blo 1264450 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B4807937 : Blo 1264450 4807937 := bstep (se 2 (by rfl) ⟨1802976, by rfl⟩ : syracuseStep 4807937 = 3605953) B3605953
theorem B24313121 : Blo 1264450 24313121 := bstep (se 2 (by rfl) ⟨9117420, by rfl⟩ : syracuseStep 24313121 = 18234841) B18234841
theorem B30768569 : Blo 1264450 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B6495709 : Blo 1264450 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B3202679 : Blo 1264450 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B4808393 : Blo 1264450 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B3604267 : Blo 1264450 3604267 := bstep (se 1 (by rfl) ⟨2703200, by rfl⟩ : syracuseStep 3604267 = 5406401) B5406401
theorem B4267835 : Blo 1264450 4267835 := bstep (se 1 (by rfl) ⟨3200876, by rfl⟩ : syracuseStep 4267835 = 6401753) B6401753
theorem B4054931 : Blo 1264450 4054931 := bstep (se 1 (by rfl) ⟨3041198, by rfl⟩ : syracuseStep 4054931 = 6082397) B6082397
theorem B1925129 : Blo 1264450 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B4268051 : Blo 1264450 4268051 := bstep (se 1 (by rfl) ⟨3201038, by rfl⟩ : syracuseStep 4268051 = 6402077) B6402077
theorem B5128211 : Blo 1264450 5128211 := bstep (se 1 (by rfl) ⟨3846158, by rfl⟩ : syracuseStep 5128211 = 7692317) B7692317
theorem B4268375 : Blo 1264450 4268375 := bstep (se 1 (by rfl) ⟨3201281, by rfl⟩ : syracuseStep 4268375 = 6402563) B6402563
theorem B2195819 : Blo 1264450 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B2400673 : Blo 1264450 2400673 := bstep (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) B1800505
theorem B8102425 : Blo 1264450 8102425 := bstep (se 2 (by rfl) ⟨3038409, by rfl⟩ : syracuseStep 8102425 = 6076819) B6076819
theorem B13681325 : Blo 1264450 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B3203783 : Blo 1264450 3203783 := bstep (se 1 (by rfl) ⟨2402837, by rfl⟩ : syracuseStep 3203783 = 4805675) B4805675
theorem B7504595 : Blo 1264450 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B2401015 : Blo 1264450 2401015 := bstep (se 1 (by rfl) ⟨1800761, by rfl⟩ : syracuseStep 2401015 = 3601523) B3601523
theorem B3203833 : Blo 1264450 3203833 := bstep (se 2 (by rfl) ⟨1201437, by rfl⟩ : syracuseStep 3203833 = 2402875) B2402875
theorem B2401319 : Blo 1264450 2401319 := bstep (se 1 (by rfl) ⟨1800989, by rfl⟩ : syracuseStep 2401319 = 3601979) B3601979
theorem B14410871 : Blo 1264450 14410871 := bstep (se 1 (by rfl) ⟨10808153, by rfl⟩ : syracuseStep 14410871 = 21616307) B21616307
theorem B16442585 : Blo 1264450 16442585 := bstep (se 2 (by rfl) ⟨6165969, by rfl⟩ : syracuseStep 16442585 = 12331939) B12331939
theorem B2278649 : Blo 1264450 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B13673843 : Blo 1264450 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B3204481 : Blo 1264450 3204481 := bstep (se 2 (by rfl) ⟨1201680, by rfl⟩ : syracuseStep 3204481 = 2403361) B2403361
theorem B4269455 : Blo 1264450 4269455 := bstep (se 1 (by rfl) ⟨3202091, by rfl⟩ : syracuseStep 4269455 = 6404183) B6404183
theorem B4056635 : Blo 1264450 4056635 := bstep (se 1 (by rfl) ⟨3042476, by rfl⟩ : syracuseStep 4056635 = 6084953) B6084953
theorem B3606113 : Blo 1264450 3606113 := bstep (se 2 (by rfl) ⟨1352292, by rfl⟩ : syracuseStep 3606113 = 2704585) B2704585
theorem B3466891 : Blo 1264450 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B70223507 : Blo 1264450 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B12977863 : Blo 1264450 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B4269779 : Blo 1264450 4269779 := bstep (se 1 (by rfl) ⟨3202334, by rfl⟩ : syracuseStep 4269779 = 6404669) B6404669
theorem B3606227 : Blo 1264450 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B23086943 : Blo 1264450 23086943 := bstep (se 1 (by rfl) ⟨17315207, by rfl⟩ : syracuseStep 23086943 = 34630415) B34630415
theorem B8660945 : Blo 1264450 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B4802561 : Blo 1264450 4802561 := bstep (se 2 (by rfl) ⟨1800960, by rfl⟩ : syracuseStep 4802561 = 3601921) B3601921
theorem B12167171 : Blo 1264450 12167171 := bstep (se 1 (by rfl) ⟨9125378, by rfl⟩ : syracuseStep 12167171 = 18250757) B18250757
theorem B2025479 : Blo 1264450 2025479 := bstep (se 1 (by rfl) ⟨1519109, by rfl⟩ : syracuseStep 2025479 = 3038219) B3038219
theorem B3205291 : Blo 1264450 3205291 := bstep (se 1 (by rfl) ⟨2403968, by rfl⟩ : syracuseStep 3205291 = 4807937) B4807937
theorem B4557185 : Blo 1264450 4557185 := bstep (se 2 (by rfl) ⟨1708944, by rfl⟩ : syracuseStep 4557185 = 3417889) B3417889
theorem B3205595 : Blo 1264450 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B36997661 : Blo 1264450 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B2845223 : Blo 1264450 2845223 := bstep (se 1 (by rfl) ⟨2133917, by rfl⟩ : syracuseStep 2845223 = 4267835) B4267835
theorem B8104657 : Blo 1264450 8104657 := bstep (se 2 (by rfl) ⟨3039246, by rfl⟩ : syracuseStep 8104657 = 6078493) B6078493
theorem B23079653 : Blo 1264450 23079653 := bstep (se 4 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 23079653 = 4327435) B4327435
theorem B7203613 : Blo 1264450 7203613 := bstep (se 3 (by rfl) ⟨1350677, by rfl⟩ : syracuseStep 7203613 = 2701355) B2701355
theorem B38964037 : Blo 1264450 38964037 := bstep (se 4 (by rfl) ⟨3652878, by rfl⟩ : syracuseStep 38964037 = 7305757) B7305757
theorem B1264463 : Blo 1264450 1264463 := bstep (se 1 (by rfl) ⟨948347, by rfl⟩ : syracuseStep 1264463 = 1896695) B1896695
theorem B1264479 : Blo 1264450 1264479 := bstep (se 1 (by rfl) ⟨948359, by rfl⟩ : syracuseStep 1264479 = 1896719) B1896719
theorem B2845547 : Blo 1264450 2845547 := bstep (se 1 (by rfl) ⟨2134160, by rfl⟩ : syracuseStep 2845547 = 4268321) B4268321
theorem B2403179 : Blo 1264450 2403179 := bstep (se 1 (by rfl) ⟨1802384, by rfl⟩ : syracuseStep 2403179 = 3604769) B3604769
theorem B4270967 : Blo 1264450 4270967 := bstep (se 1 (by rfl) ⟨3203225, by rfl⟩ : syracuseStep 4270967 = 6406451) B6406451
theorem B1264507 : Blo 1264450 1264507 := bstep (se 1 (by rfl) ⟨948380, by rfl⟩ : syracuseStep 1264507 = 1896761) B1896761
theorem B14609297 : Blo 1264450 14609297 := bstep (se 2 (by rfl) ⟨5478486, by rfl⟩ : syracuseStep 14609297 = 10956973) B10956973
theorem B2845601 : Blo 1264450 2845601 := bstep (se 2 (by rfl) ⟨1067100, by rfl⟩ : syracuseStep 2845601 = 2134201) B2134201
theorem B1264559 : Blo 1264450 1264559 := bstep (se 1 (by rfl) ⟨948419, by rfl⟩ : syracuseStep 1264559 = 1896839) B1896839
theorem B1264583 : Blo 1264450 1264583 := bstep (se 1 (by rfl) ⟨948437, by rfl⟩ : syracuseStep 1264583 = 1896875) B1896875
theorem B1264603 : Blo 1264450 1264603 := bstep (se 1 (by rfl) ⟨948452, by rfl⟩ : syracuseStep 1264603 = 1896905) B1896905
theorem B9735187 : Blo 1264450 9735187 := bstep (se 1 (by rfl) ⟨7301390, by rfl⟩ : syracuseStep 9735187 = 14602781) B14602781
theorem B3042323 : Blo 1264450 3042323 := bstep (se 1 (by rfl) ⟨2281742, by rfl⟩ : syracuseStep 3042323 = 4563485) B4563485
theorem B1264679 : Blo 1264450 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B6081587 : Blo 1264450 6081587 := bstep (se 1 (by rfl) ⟨4561190, by rfl⟩ : syracuseStep 6081587 = 9122381) B9122381
theorem B1264719 : Blo 1264450 1264719 := bstep (se 1 (by rfl) ⟨948539, by rfl⟩ : syracuseStep 1264719 = 1897079) B1897079
theorem B4271183 : Blo 1264450 4271183 := bstep (se 1 (by rfl) ⟨3203387, by rfl⟩ : syracuseStep 4271183 = 6406775) B6406775
theorem B2403407 : Blo 1264450 2403407 := bstep (se 1 (by rfl) ⟨1802555, by rfl⟩ : syracuseStep 2403407 = 3605111) B3605111
theorem B1264735 : Blo 1264450 1264735 := bstep (se 1 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 1264735 = 1897103) B1897103
theorem B1264763 : Blo 1264450 1264763 := bstep (se 1 (by rfl) ⟨948572, by rfl⟩ : syracuseStep 1264763 = 1897145) B1897145
theorem B1264815 : Blo 1264450 1264815 := bstep (se 1 (by rfl) ⟨948611, by rfl⟩ : syracuseStep 1264815 = 1897223) B1897223
theorem B1264839 : Blo 1264450 1264839 := bstep (se 1 (by rfl) ⟨948629, by rfl⟩ : syracuseStep 1264839 = 1897259) B1897259
theorem B1264859 : Blo 1264450 1264859 := bstep (se 1 (by rfl) ⟨948644, by rfl⟩ : syracuseStep 1264859 = 1897289) B1897289
theorem B2845943 : Blo 1264450 2845943 := bstep (se 1 (by rfl) ⟨2134457, by rfl⟩ : syracuseStep 2845943 = 4268915) B4268915
theorem B1264935 : Blo 1264450 1264935 := bstep (se 1 (by rfl) ⟨948701, by rfl⟩ : syracuseStep 1264935 = 1897403) B1897403
theorem B1264975 : Blo 1264450 1264975 := bstep (se 1 (by rfl) ⟨948731, by rfl⟩ : syracuseStep 1264975 = 1897463) B1897463
theorem B1264991 : Blo 1264450 1264991 := bstep (se 1 (by rfl) ⟨948743, by rfl⟩ : syracuseStep 1264991 = 1897487) B1897487
theorem B1265019 : Blo 1264450 1265019 := bstep (se 1 (by rfl) ⟨948764, by rfl⟩ : syracuseStep 1265019 = 1897529) B1897529
theorem B1265071 : Blo 1264450 1265071 := bstep (se 1 (by rfl) ⟨948803, by rfl⟩ : syracuseStep 1265071 = 1897607) B1897607
theorem B1265095 : Blo 1264450 1265095 := bstep (se 1 (by rfl) ⟨948821, by rfl⟩ : syracuseStep 1265095 = 1897643) B1897643
theorem B4271561 : Blo 1264450 4271561 := bstep (se 2 (by rfl) ⟨1601835, by rfl⟩ : syracuseStep 4271561 = 3203671) B3203671
theorem B1265115 : Blo 1264450 1265115 := bstep (se 1 (by rfl) ⟨948836, by rfl⟩ : syracuseStep 1265115 = 1897673) B1897673
theorem B6409691 : Blo 1264450 6409691 := bstep (se 1 (by rfl) ⟨4807268, by rfl⟩ : syracuseStep 6409691 = 9614537) B9614537
theorem B4107763 : Blo 1264450 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B2403847 : Blo 1264450 2403847 := bstep (se 1 (by rfl) ⟨1802885, by rfl⟩ : syracuseStep 2403847 = 3605771) B3605771
theorem B1265191 : Blo 1264450 1265191 := bstep (se 1 (by rfl) ⟨948893, by rfl⟩ : syracuseStep 1265191 = 1897787) B1897787
theorem B1265231 : Blo 1264450 1265231 := bstep (se 1 (by rfl) ⟨948923, by rfl⟩ : syracuseStep 1265231 = 1897847) B1897847
theorem B1265247 : Blo 1264450 1265247 := bstep (se 1 (by rfl) ⟨948935, by rfl⟩ : syracuseStep 1265247 = 1897871) B1897871
theorem B1601147 : Blo 1264450 1601147 := bstep (se 1 (by rfl) ⟨1200860, by rfl⟩ : syracuseStep 1601147 = 2401721) B2401721
theorem B1265275 : Blo 1264450 1265275 := bstep (se 1 (by rfl) ⟨948956, by rfl⟩ : syracuseStep 1265275 = 1897913) B1897913
theorem B4804231 : Blo 1264450 4804231 := bstep (se 1 (by rfl) ⟨3603173, by rfl⟩ : syracuseStep 4804231 = 7206347) B7206347
theorem B1265327 : Blo 1264450 1265327 := bstep (se 1 (by rfl) ⟨948995, by rfl⟩ : syracuseStep 1265327 = 1897991) B1897991
theorem B1265351 : Blo 1264450 1265351 := bstep (se 1 (by rfl) ⟨949013, by rfl⟩ : syracuseStep 1265351 = 1898027) B1898027
theorem B4271831 : Blo 1264450 4271831 := bstep (se 1 (by rfl) ⟨3203873, by rfl⟩ : syracuseStep 4271831 = 6407747) B6407747
theorem B1265371 : Blo 1264450 1265371 := bstep (se 1 (by rfl) ⟨949028, by rfl⟩ : syracuseStep 1265371 = 1898057) B1898057
theorem B1265447 : Blo 1264450 1265447 := bstep (se 1 (by rfl) ⟨949085, by rfl⟩ : syracuseStep 1265447 = 1898171) B1898171
theorem B16215875 : Blo 1264450 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B13692739 : Blo 1264450 13692739 := bstep (se 1 (by rfl) ⟨10269554, by rfl⟩ : syracuseStep 13692739 = 20539109) B20539109
theorem B2846537 : Blo 1264450 2846537 := bstep (se 2 (by rfl) ⟨1067451, by rfl⟩ : syracuseStep 2846537 = 2134903) B2134903
theorem B5132105 : Blo 1264450 5132105 := bstep (se 2 (by rfl) ⟨1924539, by rfl⟩ : syracuseStep 5132105 = 3849079) B3849079
theorem B1265487 : Blo 1264450 1265487 := bstep (se 1 (by rfl) ⟨949115, by rfl⟩ : syracuseStep 1265487 = 1898231) B1898231
theorem B1265503 : Blo 1264450 1265503 := bstep (se 1 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 1265503 = 1898255) B1898255
theorem B6164333 : Blo 1264450 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B1265531 : Blo 1264450 1265531 := bstep (se 1 (by rfl) ⟨949148, by rfl⟩ : syracuseStep 1265531 = 1898297) B1898297
theorem B18255779 : Blo 1264450 18255779 := bstep (se 1 (by rfl) ⟨13691834, by rfl⟩ : syracuseStep 18255779 = 27383669) B27383669
theorem B1265583 : Blo 1264450 1265583 := bstep (se 1 (by rfl) ⟨949187, by rfl⟩ : syracuseStep 1265583 = 1898375) B1898375
theorem B4272047 : Blo 1264450 4272047 := bstep (se 1 (by rfl) ⟨3204035, by rfl⟩ : syracuseStep 4272047 = 6408071) B6408071
theorem B4804535 : Blo 1264450 4804535 := bstep (se 1 (by rfl) ⟨3603401, by rfl⟩ : syracuseStep 4804535 = 7206803) B7206803
theorem B6410177 : Blo 1264450 6410177 := bstep (se 2 (by rfl) ⟨2403816, by rfl⟩ : syracuseStep 6410177 = 4807633) B4807633
theorem B1265607 : Blo 1264450 1265607 := bstep (se 1 (by rfl) ⟨949205, by rfl⟩ : syracuseStep 1265607 = 1898411) B1898411
theorem B1265627 : Blo 1264450 1265627 := bstep (se 1 (by rfl) ⟨949220, by rfl⟩ : syracuseStep 1265627 = 1898441) B1898441
theorem B1929179 : Blo 1264450 1929179 := bstep (se 1 (by rfl) ⟨1446884, by rfl⟩ : syracuseStep 1929179 = 2893769) B2893769
theorem B1265703 : Blo 1264450 1265703 := bstep (se 1 (by rfl) ⟨949277, by rfl⟩ : syracuseStep 1265703 = 1898555) B1898555
theorem B2134073 : Blo 1264450 2134073 := bstep (se 2 (by rfl) ⟨800277, by rfl⟩ : syracuseStep 2134073 = 1600555) B1600555
theorem B9744461 : Blo 1264450 9744461 := bstep (se 3 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 9744461 = 3654173) B3654173
theorem B1265743 : Blo 1264450 1265743 := bstep (se 1 (by rfl) ⟨949307, by rfl⟩ : syracuseStep 1265743 = 1898615) B1898615
theorem B1265759 : Blo 1264450 1265759 := bstep (se 1 (by rfl) ⟨949319, by rfl⟩ : syracuseStep 1265759 = 1898639) B1898639
theorem B1265787 : Blo 1264450 1265787 := bstep (se 1 (by rfl) ⟨949340, by rfl⟩ : syracuseStep 1265787 = 1898681) B1898681
theorem B1265839 : Blo 1264450 1265839 := bstep (se 1 (by rfl) ⟨949379, by rfl⟩ : syracuseStep 1265839 = 1898759) B1898759
theorem B38957233 : Blo 1264450 38957233 := bstep (se 2 (by rfl) ⟨14608962, by rfl⟩ : syracuseStep 38957233 = 29217925) B29217925
theorem B1265863 : Blo 1264450 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1265883 : Blo 1264450 1265883 := bstep (se 1 (by rfl) ⟨949412, by rfl⟩ : syracuseStep 1265883 = 1898825) B1898825
theorem B4624651 : Blo 1264450 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B1265959 : Blo 1264450 1265959 := bstep (se 1 (by rfl) ⟨949469, by rfl⟩ : syracuseStep 1265959 = 1898939) B1898939
theorem B1265999 : Blo 1264450 1265999 := bstep (se 1 (by rfl) ⟨949499, by rfl⟩ : syracuseStep 1265999 = 1898999) B1898999
theorem B1266015 : Blo 1264450 1266015 := bstep (se 1 (by rfl) ⟨949511, by rfl⟩ : syracuseStep 1266015 = 1899023) B1899023
theorem B1896809 : Blo 1264450 1896809 := bstep (se 2 (by rfl) ⟨711303, by rfl⟩ : syracuseStep 1896809 = 1422607) B1422607
theorem B1266043 : Blo 1264450 1266043 := bstep (se 1 (by rfl) ⟨949532, by rfl⟩ : syracuseStep 1266043 = 1899065) B1899065
theorem B1266095 : Blo 1264450 1266095 := bstep (se 1 (by rfl) ⟨949571, by rfl⟩ : syracuseStep 1266095 = 1899143) B1899143
theorem B1896887 : Blo 1264450 1896887 := bstep (se 1 (by rfl) ⟨1422665, by rfl⟩ : syracuseStep 1896887 = 2845331) B2845331
theorem B1266119 : Blo 1264450 1266119 := bstep (se 1 (by rfl) ⟨949589, by rfl⟩ : syracuseStep 1266119 = 1899179) B1899179
theorem B1896923 : Blo 1264450 1896923 := bstep (se 1 (by rfl) ⟨1422692, by rfl⟩ : syracuseStep 1896923 = 2845385) B2845385
theorem B1266139 : Blo 1264450 1266139 := bstep (se 1 (by rfl) ⟨949604, by rfl⟩ : syracuseStep 1266139 = 1899209) B1899209
theorem B1266215 : Blo 1264450 1266215 := bstep (se 1 (by rfl) ⟨949661, by rfl⟩ : syracuseStep 1266215 = 1899323) B1899323
theorem B1266255 : Blo 1264450 1266255 := bstep (se 1 (by rfl) ⟨949691, by rfl⟩ : syracuseStep 1266255 = 1899383) B1899383
theorem B2847329 : Blo 1264450 2847329 := bstep (se 2 (by rfl) ⟨1067748, by rfl⟩ : syracuseStep 2847329 = 2135497) B2135497
theorem B1266271 : Blo 1264450 1266271 := bstep (se 1 (by rfl) ⟨949703, by rfl⟩ : syracuseStep 1266271 = 1899407) B1899407
theorem B13873781 : Blo 1264450 13873781 := bstep (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) B1300667
theorem B1266299 : Blo 1264450 1266299 := bstep (se 1 (by rfl) ⟨949724, by rfl⟩ : syracuseStep 1266299 = 1899449) B1899449
theorem B1266351 : Blo 1264450 1266351 := bstep (se 1 (by rfl) ⟨949763, by rfl⟩ : syracuseStep 1266351 = 1899527) B1899527
theorem B1266375 : Blo 1264450 1266375 := bstep (se 1 (by rfl) ⟨949781, by rfl⟩ : syracuseStep 1266375 = 1899563) B1899563
theorem B1266395 : Blo 1264450 1266395 := bstep (se 1 (by rfl) ⟨949796, by rfl⟩ : syracuseStep 1266395 = 1899593) B1899593
theorem B2134775 : Blo 1264450 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B18248449 : Blo 1264450 18248449 := bstep (se 2 (by rfl) ⟨6843168, by rfl⟩ : syracuseStep 18248449 = 13686337) B13686337
theorem B16208747 : Blo 1264450 16208747 := bstep (se 1 (by rfl) ⟨12156560, by rfl⟩ : syracuseStep 16208747 = 24313121) B24313121
theorem B1897391 : Blo 1264450 1897391 := bstep (se 1 (by rfl) ⟨1423043, by rfl⟩ : syracuseStep 1897391 = 2846087) B2846087
theorem B2847671 : Blo 1264450 2847671 := bstep (se 1 (by rfl) ⟨2135753, by rfl⟩ : syracuseStep 2847671 = 4271507) B4271507
theorem B1897481 : Blo 1264450 1897481 := bstep (se 2 (by rfl) ⟨711555, by rfl⟩ : syracuseStep 1897481 = 1423111) B1423111
theorem B5403667 : Blo 1264450 5403667 := bstep (se 1 (by rfl) ⟨4052750, by rfl⟩ : syracuseStep 5403667 = 8105501) B8105501
theorem B1897511 : Blo 1264450 1897511 := bstep (se 1 (by rfl) ⟨1423133, by rfl⟩ : syracuseStep 1897511 = 2846267) B2846267
theorem B4805689 : Blo 1264450 4805689 := bstep (se 2 (by rfl) ⟨1802133, by rfl⟩ : syracuseStep 4805689 = 3604267) B3604267
theorem B2135119 : Blo 1264450 2135119 := bstep (se 1 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 2135119 = 3202679) B3202679
theorem B1897595 : Blo 1264450 1897595 := bstep (se 1 (by rfl) ⟨1423196, by rfl⟩ : syracuseStep 1897595 = 2846393) B2846393
theorem B3601579 : Blo 1264450 3601579 := bstep (se 1 (by rfl) ⟨2701184, by rfl⟩ : syracuseStep 3601579 = 5402369) B5402369
theorem B1422535 : Blo 1264450 1422535 := bstep (se 1 (by rfl) ⟨1066901, by rfl⟩ : syracuseStep 1422535 = 2133803) B2133803
theorem B1897721 : Blo 1264450 1897721 := bstep (se 2 (by rfl) ⟨711645, by rfl⟩ : syracuseStep 1897721 = 1423291) B1423291
theorem B2135369 : Blo 1264450 2135369 := bstep (se 2 (by rfl) ⟨800763, by rfl⟩ : syracuseStep 2135369 = 1601527) B1601527
theorem B1897823 : Blo 1264450 1897823 := bstep (se 1 (by rfl) ⟨1423367, by rfl⟩ : syracuseStep 1897823 = 2846735) B2846735
theorem B1897835 : Blo 1264450 1897835 := bstep (se 1 (by rfl) ⟨1423376, by rfl⟩ : syracuseStep 1897835 = 2846753) B2846753
theorem B4805993 : Blo 1264450 4805993 := bstep (se 2 (by rfl) ⟨1802247, by rfl⟩ : syracuseStep 4805993 = 3604495) B3604495
theorem B4052443 : Blo 1264450 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B2848265 : Blo 1264450 2848265 := bstep (se 2 (by rfl) ⟨1068099, by rfl⟩ : syracuseStep 2848265 = 2136199) B2136199
theorem B1898063 : Blo 1264450 1898063 := bstep (se 1 (by rfl) ⟨1423547, by rfl⟩ : syracuseStep 1898063 = 2847095) B2847095
theorem B5404283 : Blo 1264450 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B1898183 : Blo 1264450 1898183 := bstep (se 1 (by rfl) ⟨1423637, by rfl⟩ : syracuseStep 1898183 = 2847275) B2847275
theorem B2135801 : Blo 1264450 2135801 := bstep (se 2 (by rfl) ⟨800925, by rfl⟩ : syracuseStep 2135801 = 1601851) B1601851
theorem B36484901 : Blo 1264450 36484901 := bstep (se 4 (by rfl) ⟨3420459, by rfl⟩ : syracuseStep 36484901 = 6840919) B6840919
theorem B13678379 : Blo 1264450 13678379 := bstep (se 1 (by rfl) ⟨10258784, by rfl⟩ : syracuseStep 13678379 = 20517569) B20517569
theorem B6084395 : Blo 1264450 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B10811231 : Blo 1264450 10811231 := bstep (se 1 (by rfl) ⟨8108423, by rfl⟩ : syracuseStep 10811231 = 16216847) B16216847
theorem B2848607 : Blo 1264450 2848607 := bstep (se 1 (by rfl) ⟨2136455, by rfl⟩ : syracuseStep 2848607 = 4272911) B4272911
theorem B1898345 : Blo 1264450 1898345 := bstep (se 2 (by rfl) ⟨711879, by rfl⟩ : syracuseStep 1898345 = 1423759) B1423759
theorem B11540333 : Blo 1264450 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B2135983 : Blo 1264450 2135983 := bstep (se 1 (by rfl) ⟨1601987, by rfl⟩ : syracuseStep 2135983 = 3203975) B3203975
theorem B1898423 : Blo 1264450 1898423 := bstep (se 1 (by rfl) ⟨1423817, by rfl⟩ : syracuseStep 1898423 = 2847635) B2847635
theorem B9115577 : Blo 1264450 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B25958353 : Blo 1264450 25958353 := bstep (se 2 (by rfl) ⟨9734382, by rfl⟩ : syracuseStep 25958353 = 19468765) B19468765
theorem B1898459 : Blo 1264450 1898459 := bstep (se 1 (by rfl) ⟨1423844, by rfl⟩ : syracuseStep 1898459 = 2847689) B2847689
theorem B2136071 : Blo 1264450 2136071 := bstep (se 1 (by rfl) ⟨1602053, by rfl⟩ : syracuseStep 2136071 = 3204107) B3204107
theorem B4053007 : Blo 1264450 4053007 := bstep (se 1 (by rfl) ⟨3039755, by rfl⟩ : syracuseStep 4053007 = 6079511) B6079511
theorem B2848787 : Blo 1264450 2848787 := bstep (se 1 (by rfl) ⟨2136590, by rfl⟩ : syracuseStep 2848787 = 4273181) B4273181
theorem B1423399 : Blo 1264450 1423399 := bstep (se 1 (by rfl) ⟨1067549, by rfl⟩ : syracuseStep 1423399 = 2135099) B2135099
theorem B18249785 : Blo 1264450 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B4053149 : Blo 1264450 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B5134583 : Blo 1264450 5134583 := bstep (se 1 (by rfl) ⟨3850937, by rfl⟩ : syracuseStep 5134583 = 7701875) B7701875
theorem B18233687 : Blo 1264450 18233687 := bstep (se 1 (by rfl) ⟨13675265, by rfl⟩ : syracuseStep 18233687 = 27350531) B27350531
theorem B2136415 : Blo 1264450 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B2849129 : Blo 1264450 2849129 := bstep (se 2 (by rfl) ⟨1068423, by rfl⟩ : syracuseStep 2849129 = 2136847) B2136847
theorem B1898927 : Blo 1264450 1898927 := bstep (se 1 (by rfl) ⟨1424195, by rfl⟩ : syracuseStep 1898927 = 2848391) B2848391
theorem B2136503 : Blo 1264450 2136503 := bstep (se 1 (by rfl) ⟨1602377, by rfl⟩ : syracuseStep 2136503 = 3204755) B3204755
theorem B3201545 : Blo 1264450 3201545 := bstep (se 2 (by rfl) ⟨1200579, by rfl⟩ : syracuseStep 3201545 = 2401159) B2401159
theorem B1899017 : Blo 1264450 1899017 := bstep (se 2 (by rfl) ⟨712131, by rfl⟩ : syracuseStep 1899017 = 1424263) B1424263
theorem B1899047 : Blo 1264450 1899047 := bstep (se 1 (by rfl) ⟨1424285, by rfl⟩ : syracuseStep 1899047 = 2848571) B2848571
theorem B1899131 : Blo 1264450 1899131 := bstep (se 1 (by rfl) ⟨1424348, by rfl⟩ : syracuseStep 1899131 = 2848697) B2848697
theorem B16226993 : Blo 1264450 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B1899257 : Blo 1264450 1899257 := bstep (se 2 (by rfl) ⟨712221, by rfl⟩ : syracuseStep 1899257 = 1424443) B1424443
theorem B3422969 : Blo 1264450 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B1899359 : Blo 1264450 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B1899371 : Blo 1264450 1899371 := bstep (se 1 (by rfl) ⟨1424528, by rfl⟩ : syracuseStep 1899371 = 2849057) B2849057
theorem B2137097 : Blo 1264450 2137097 := bstep (se 2 (by rfl) ⟨801411, by rfl⟩ : syracuseStep 2137097 = 1602823) B1602823
theorem B1350695 : Blo 1264450 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B7207987 : Blo 1264450 7207987 := bstep (se 1 (by rfl) ⟨5405990, by rfl⟩ : syracuseStep 7207987 = 10811981) B10811981
theorem B1899599 : Blo 1264450 1899599 := bstep (se 1 (by rfl) ⟨1424699, by rfl⟩ : syracuseStep 1899599 = 2849399) B2849399
theorem B6585623 : Blo 1264450 6585623 := bstep (se 1 (by rfl) ⟨4939217, by rfl⟩ : syracuseStep 6585623 = 9878435) B9878435
theorem B8658265 : Blo 1264450 8658265 := bstep (se 2 (by rfl) ⟨3246849, by rfl⟩ : syracuseStep 8658265 = 6493699) B6493699
theorem B2702945 : Blo 1264450 2702945 := bstep (se 2 (by rfl) ⟨1013604, by rfl⟩ : syracuseStep 2702945 = 2027209) B2027209
theorem B20512379 : Blo 1264450 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B3202699 : Blo 1264450 3202699 := bstep (se 1 (by rfl) ⟨2402024, by rfl⟩ : syracuseStep 3202699 = 4804049) B4804049
theorem B13876925 : Blo 1264450 13876925 := bstep (se 3 (by rfl) ⟨2601923, by rfl⟩ : syracuseStep 13876925 = 5203847) B5203847
theorem B10395335 : Blo 1264450 10395335 := bstep (se 1 (by rfl) ⟨7796501, by rfl⟩ : syracuseStep 10395335 = 15593003) B15593003
theorem B9117535 : Blo 1264450 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B2703287 : Blo 1264450 2703287 := bstep (se 1 (by rfl) ⟨2027465, by rfl⟩ : syracuseStep 2703287 = 4054931) B4054931
theorem B3203003 : Blo 1264450 3203003 := bstep (se 1 (by rfl) ⟨2402252, by rfl⟩ : syracuseStep 3203003 = 4804505) B4804505
theorem B6496307 : Blo 1264450 6496307 := bstep (se 1 (by rfl) ⟨4872230, by rfl⟩ : syracuseStep 6496307 = 9744461) B9744461
theorem B9249187 : Blo 1264450 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B10805831 : Blo 1264450 10805831 := bstep (se 1 (by rfl) ⟨8104373, by rfl⟩ : syracuseStep 10805831 = 16208747) B16208747
theorem B10961723 : Blo 1264450 10961723 := bstep (se 1 (by rfl) ⟨8221292, by rfl⟩ : syracuseStep 10961723 = 16442585) B16442585
theorem B3203995 : Blo 1264450 3203995 := bstep (se 1 (by rfl) ⟨2402996, by rfl⟩ : syracuseStep 3203995 = 4805993) B4805993
theorem B10806209 : Blo 1264450 10806209 := bstep (se 2 (by rfl) ⟨4052328, by rfl⟩ : syracuseStep 10806209 = 8104657) B8104657
theorem B24331265 : Blo 1264450 24331265 := bstep (se 2 (by rfl) ⟨9124224, by rfl⟩ : syracuseStep 24331265 = 18248449) B18248449
theorem B69215269 : Blo 1264450 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B2704423 : Blo 1264450 2704423 := bstep (se 1 (by rfl) ⟨2028317, by rfl⟩ : syracuseStep 2704423 = 4056635) B4056635
theorem B24323267 : Blo 1264450 24323267 := bstep (se 1 (by rfl) ⟨18242450, by rfl⟩ : syracuseStep 24323267 = 36484901) B36484901
theorem B9118919 : Blo 1264450 9118919 := bstep (se 1 (by rfl) ⟨6839189, by rfl⟩ : syracuseStep 9118919 = 13678379) B13678379
theorem B4056263 : Blo 1264450 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B7693555 : Blo 1264450 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B8111447 : Blo 1264450 8111447 := bstep (se 1 (by rfl) ⟨6083585, by rfl⟩ : syracuseStep 8111447 = 12167171) B12167171
theorem B12166523 : Blo 1264450 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B9610649 : Blo 1264450 9610649 := bstep (se 2 (by rfl) ⟨3603993, by rfl⟩ : syracuseStep 9610649 = 7207987) B7207987
theorem B6407585 : Blo 1264450 6407585 := bstep (se 2 (by rfl) ⟨2402844, by rfl⟩ : syracuseStep 6407585 = 4805689) B4805689
theorem B4802105 : Blo 1264450 4802105 := bstep (se 2 (by rfl) ⟨1800789, by rfl⟩ : syracuseStep 4802105 = 3601579) B3601579
theorem B4269725 : Blo 1264450 4269725 := bstep (se 3 (by rfl) ⟨800573, by rfl⟩ : syracuseStep 4269725 = 1601147) B1601147
theorem B11544353 : Blo 1264450 11544353 := bstep (se 2 (by rfl) ⟨4329132, by rfl⟩ : syracuseStep 11544353 = 8658265) B8658265
theorem B15386435 : Blo 1264450 15386435 := bstep (se 1 (by rfl) ⟨11539826, by rfl⟩ : syracuseStep 15386435 = 23079653) B23079653
theorem B37005133 : Blo 1264450 37005133 := bstep (se 3 (by rfl) ⟨6938462, by rfl⟩ : syracuseStep 37005133 = 13876925) B13876925
theorem B3205129 : Blo 1264450 3205129 := bstep (se 2 (by rfl) ⟨1201923, by rfl⟩ : syracuseStep 3205129 = 2403847) B2403847
theorem B4270265 : Blo 1264450 4270265 := bstep (se 2 (by rfl) ⟨1601349, by rfl⟩ : syracuseStep 4270265 = 3202699) B3202699
theorem B4622521 : Blo 1264450 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B13674919 : Blo 1264450 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B21908069 : Blo 1264450 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B2845367 : Blo 1264450 2845367 := bstep (se 1 (by rfl) ⟨2134025, by rfl⟩ : syracuseStep 2845367 = 4268051) B4268051
theorem B13675229 : Blo 1264450 13675229 := bstep (se 3 (by rfl) ⟨2564105, by rfl⟩ : syracuseStep 13675229 = 5128211) B5128211
theorem B2845583 : Blo 1264450 2845583 := bstep (se 1 (by rfl) ⟨2134187, by rfl⟩ : syracuseStep 2845583 = 4268375) B4268375
theorem B1264539 : Blo 1264450 1264539 := bstep (se 1 (by rfl) ⟨948404, by rfl⟩ : syracuseStep 1264539 = 1896809) B1896809
theorem B1264591 : Blo 1264450 1264591 := bstep (se 1 (by rfl) ⟨948443, by rfl⟩ : syracuseStep 1264591 = 1896887) B1896887
theorem B1264615 : Blo 1264450 1264615 := bstep (se 1 (by rfl) ⟨948461, by rfl⟩ : syracuseStep 1264615 = 1896923) B1896923
theorem B9120883 : Blo 1264450 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B1264927 : Blo 1264450 1264927 := bstep (se 1 (by rfl) ⟨948695, by rfl⟩ : syracuseStep 1264927 = 1897391) B1897391
theorem B1264987 : Blo 1264450 1264987 := bstep (se 1 (by rfl) ⟨948740, by rfl⟩ : syracuseStep 1264987 = 1897481) B1897481
theorem B1600879 : Blo 1264450 1600879 := bstep (se 1 (by rfl) ⟨1200659, by rfl⟩ : syracuseStep 1600879 = 2401319) B2401319
theorem B1265007 : Blo 1264450 1265007 := bstep (se 1 (by rfl) ⟨948755, by rfl⟩ : syracuseStep 1265007 = 1897511) B1897511
theorem B1265063 : Blo 1264450 1265063 := bstep (se 1 (by rfl) ⟨948797, by rfl⟩ : syracuseStep 1265063 = 1897595) B1897595
theorem B1265147 : Blo 1264450 1265147 := bstep (se 1 (by rfl) ⟨948860, by rfl⟩ : syracuseStep 1265147 = 1897721) B1897721
theorem B1265215 : Blo 1264450 1265215 := bstep (se 1 (by rfl) ⟨948911, by rfl⟩ : syracuseStep 1265215 = 1897823) B1897823
theorem B1265223 : Blo 1264450 1265223 := bstep (se 1 (by rfl) ⟨948917, by rfl⟩ : syracuseStep 1265223 = 1897835) B1897835
theorem B2846303 : Blo 1264450 2846303 := bstep (se 1 (by rfl) ⟨2134727, by rfl⟩ : syracuseStep 2846303 = 4269455) B4269455
theorem B4271777 : Blo 1264450 4271777 := bstep (se 2 (by rfl) ⟨1601916, by rfl⟩ : syracuseStep 4271777 = 3203833) B3203833
theorem B9604817 : Blo 1264450 9604817 := bstep (se 2 (by rfl) ⟨3601806, by rfl⟩ : syracuseStep 9604817 = 7203613) B7203613
theorem B1265375 : Blo 1264450 1265375 := bstep (se 1 (by rfl) ⟨949031, by rfl⟩ : syracuseStep 1265375 = 1898063) B1898063
theorem B2404075 : Blo 1264450 2404075 := bstep (se 1 (by rfl) ⟨1803056, by rfl⟩ : syracuseStep 2404075 = 3606113) B3606113
theorem B1265455 : Blo 1264450 1265455 := bstep (se 1 (by rfl) ⟨949091, by rfl⟩ : syracuseStep 1265455 = 1898183) B1898183
theorem B2846519 : Blo 1264450 2846519 := bstep (se 1 (by rfl) ⟨2134889, by rfl⟩ : syracuseStep 2846519 = 4269779) B4269779
theorem B2404151 : Blo 1264450 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B1265563 : Blo 1264450 1265563 := bstep (se 1 (by rfl) ⟨949172, by rfl⟩ : syracuseStep 1265563 = 1898345) B1898345
theorem B1265615 : Blo 1264450 1265615 := bstep (se 1 (by rfl) ⟨949211, by rfl⟩ : syracuseStep 1265615 = 1898423) B1898423
theorem B1265639 : Blo 1264450 1265639 := bstep (se 1 (by rfl) ⟨949229, by rfl⟩ : syracuseStep 1265639 = 1898459) B1898459
theorem B12980249 : Blo 1264450 12980249 := bstep (se 2 (by rfl) ⟨4867593, by rfl⟩ : syracuseStep 12980249 = 9735187) B9735187
theorem B7204889 : Blo 1264450 7204889 := bstep (se 2 (by rfl) ⟨2701833, by rfl⟩ : syracuseStep 7204889 = 5403667) B5403667
theorem B2846825 : Blo 1264450 2846825 := bstep (se 2 (by rfl) ⟨1067559, by rfl⟩ : syracuseStep 2846825 = 2135119) B2135119
theorem B1896713 : Blo 1264450 1896713 := bstep (se 2 (by rfl) ⟨711267, by rfl⟩ : syracuseStep 1896713 = 1422535) B1422535
theorem B1265951 : Blo 1264450 1265951 := bstep (se 1 (by rfl) ⟨949463, by rfl⟩ : syracuseStep 1265951 = 1898927) B1898927
theorem B2134363 : Blo 1264450 2134363 := bstep (se 1 (by rfl) ⟨1600772, by rfl⟩ : syracuseStep 2134363 = 3201545) B3201545
theorem B1266011 : Blo 1264450 1266011 := bstep (se 1 (by rfl) ⟨949508, by rfl⟩ : syracuseStep 1266011 = 1899017) B1899017
theorem B1896815 : Blo 1264450 1896815 := bstep (se 1 (by rfl) ⟨1422611, by rfl⟩ : syracuseStep 1896815 = 2845223) B2845223
theorem B1266031 : Blo 1264450 1266031 := bstep (se 1 (by rfl) ⟨949523, by rfl⟩ : syracuseStep 1266031 = 1899047) B1899047
theorem B1266087 : Blo 1264450 1266087 := bstep (se 1 (by rfl) ⟨949565, by rfl⟩ : syracuseStep 1266087 = 1899131) B1899131
theorem B10817995 : Blo 1264450 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B1266171 : Blo 1264450 1266171 := bstep (se 1 (by rfl) ⟨949628, by rfl⟩ : syracuseStep 1266171 = 1899257) B1899257
theorem B2281979 : Blo 1264450 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B4272641 : Blo 1264450 4272641 := bstep (se 2 (by rfl) ⟨1602240, by rfl⟩ : syracuseStep 4272641 = 3204481) B3204481
theorem B1266239 : Blo 1264450 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B1897031 : Blo 1264450 1897031 := bstep (se 1 (by rfl) ⟨1422773, by rfl⟩ : syracuseStep 1897031 = 2845547) B2845547
theorem B1602119 : Blo 1264450 1602119 := bstep (se 1 (by rfl) ⟨1201589, by rfl⟩ : syracuseStep 1602119 = 2403179) B2403179
theorem B1266247 : Blo 1264450 1266247 := bstep (se 1 (by rfl) ⟨949685, by rfl⟩ : syracuseStep 1266247 = 1899371) B1899371
theorem B2847311 : Blo 1264450 2847311 := bstep (se 1 (by rfl) ⟨2135483, by rfl⟩ : syracuseStep 2847311 = 4270967) B4270967
theorem B1897067 : Blo 1264450 1897067 := bstep (se 1 (by rfl) ⟨1422800, by rfl⟩ : syracuseStep 1897067 = 2845601) B2845601
theorem B5403257 : Blo 1264450 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B2028215 : Blo 1264450 2028215 := bstep (se 1 (by rfl) ⟨1521161, by rfl⟩ : syracuseStep 2028215 = 3042323) B3042323
theorem B2847455 : Blo 1264450 2847455 := bstep (se 1 (by rfl) ⟨2135591, by rfl⟩ : syracuseStep 2847455 = 4271183) B4271183
theorem B1602271 : Blo 1264450 1602271 := bstep (se 1 (by rfl) ⟨1201703, by rfl⟩ : syracuseStep 1602271 = 2403407) B2403407
theorem B1266399 : Blo 1264450 1266399 := bstep (se 1 (by rfl) ⟨949799, by rfl⟩ : syracuseStep 1266399 = 1899599) B1899599
theorem B1897295 : Blo 1264450 1897295 := bstep (se 1 (by rfl) ⟨1422971, by rfl⟩ : syracuseStep 1897295 = 2845943) B2845943
theorem B2847707 : Blo 1264450 2847707 := bstep (se 1 (by rfl) ⟨2135780, by rfl⟩ : syracuseStep 2847707 = 4271561) B4271561
theorem B4273127 : Blo 1264450 4273127 := bstep (se 1 (by rfl) ⟨3204845, by rfl⟩ : syracuseStep 4273127 = 6409691) B6409691
theorem B18256985 : Blo 1264450 18256985 := bstep (se 2 (by rfl) ⟨6846369, by rfl⟩ : syracuseStep 18256985 = 13692739) B13692739
theorem B2847887 : Blo 1264450 2847887 := bstep (se 1 (by rfl) ⟨2135915, by rfl⟩ : syracuseStep 2847887 = 4271831) B4271831
theorem B10810583 : Blo 1264450 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B1897691 : Blo 1264450 1897691 := bstep (se 1 (by rfl) ⟨1423268, by rfl⟩ : syracuseStep 1897691 = 2846537) B2846537
theorem B3421403 : Blo 1264450 3421403 := bstep (se 1 (by rfl) ⟨2566052, by rfl⟩ : syracuseStep 3421403 = 5132105) B5132105
theorem B2847977 : Blo 1264450 2847977 := bstep (se 2 (by rfl) ⟨1067991, by rfl⟩ : syracuseStep 2847977 = 2135983) B2135983
theorem B4109555 : Blo 1264450 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B12170519 : Blo 1264450 12170519 := bstep (se 1 (by rfl) ⟨9127889, by rfl⟩ : syracuseStep 12170519 = 18255779) B18255779
theorem B2848031 : Blo 1264450 2848031 := bstep (se 1 (by rfl) ⟨2136023, by rfl⟩ : syracuseStep 2848031 = 4272047) B4272047
theorem B2135335 : Blo 1264450 2135335 := bstep (se 1 (by rfl) ⟨1601501, by rfl⟩ : syracuseStep 2135335 = 3203003) B3203003
theorem B4273451 : Blo 1264450 4273451 := bstep (se 1 (by rfl) ⟨3205088, by rfl⟩ : syracuseStep 4273451 = 6410177) B6410177
theorem B1283419 : Blo 1264450 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B5404009 : Blo 1264450 5404009 := bstep (se 2 (by rfl) ⟨2026503, by rfl⟩ : syracuseStep 5404009 = 4053007) B4053007
theorem B1422715 : Blo 1264450 1422715 := bstep (se 1 (by rfl) ⟨1067036, by rfl⟩ : syracuseStep 1422715 = 2134073) B2134073
theorem B1897865 : Blo 1264450 1897865 := bstep (se 2 (by rfl) ⟨711699, by rfl⟩ : syracuseStep 1897865 = 1423399) B1423399
theorem B3601853 : Blo 1264450 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B4273721 : Blo 1264450 4273721 := bstep (se 2 (by rfl) ⟨1602645, by rfl⟩ : syracuseStep 4273721 = 3205291) B3205291
theorem B51942977 : Blo 1264450 51942977 := bstep (se 2 (by rfl) ⟨19478616, by rfl⟩ : syracuseStep 51942977 = 38957233) B38957233
theorem B1463879 : Blo 1264450 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B6166201 : Blo 1264450 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B1898219 : Blo 1264450 1898219 := bstep (se 1 (by rfl) ⟨1423664, by rfl⟩ : syracuseStep 1898219 = 2847329) B2847329
theorem B2848553 : Blo 1264450 2848553 := bstep (se 2 (by rfl) ⟨1068207, by rfl⟩ : syracuseStep 2848553 = 2136415) B2136415
theorem B2135855 : Blo 1264450 2135855 := bstep (se 1 (by rfl) ⟨1601891, by rfl⟩ : syracuseStep 2135855 = 3203783) B3203783
theorem B5003063 : Blo 1264450 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B1423183 : Blo 1264450 1423183 := bstep (se 1 (by rfl) ⟨1067387, by rfl⟩ : syracuseStep 1423183 = 2134775) B2134775
theorem B3200897 : Blo 1264450 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B1898447 : Blo 1264450 1898447 := bstep (se 1 (by rfl) ⟨1423835, by rfl⟩ : syracuseStep 1898447 = 2847671) B2847671
theorem B6076397 : Blo 1264450 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B10803233 : Blo 1264450 10803233 := bstep (se 2 (by rfl) ⟨4051212, by rfl⟩ : syracuseStep 10803233 = 8102425) B8102425
theorem B9607247 : Blo 1264450 9607247 := bstep (se 1 (by rfl) ⟨7205435, by rfl⟩ : syracuseStep 9607247 = 14410871) B14410871
theorem B1423579 : Blo 1264450 1423579 := bstep (se 1 (by rfl) ⟨1067684, by rfl⟩ : syracuseStep 1423579 = 2135369) B2135369
theorem B9115895 : Blo 1264450 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B3201353 : Blo 1264450 3201353 := bstep (se 2 (by rfl) ⟨1200507, by rfl⟩ : syracuseStep 3201353 = 2401015) B2401015
theorem B1898843 : Blo 1264450 1898843 := bstep (se 1 (by rfl) ⟨1424132, by rfl⟩ : syracuseStep 1898843 = 2848265) B2848265
theorem B3602855 : Blo 1264450 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B51952049 : Blo 1264450 51952049 := bstep (se 2 (by rfl) ⟨19482018, by rfl⟩ : syracuseStep 51952049 = 38964037) B38964037
theorem B46815671 : Blo 1264450 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B1423867 : Blo 1264450 1423867 := bstep (se 1 (by rfl) ⟨1067900, by rfl⟩ : syracuseStep 1423867 = 2135801) B2135801
theorem B15391295 : Blo 1264450 15391295 := bstep (se 1 (by rfl) ⟨11543471, by rfl⟩ : syracuseStep 15391295 = 23086943) B23086943
theorem B7207487 : Blo 1264450 7207487 := bstep (se 1 (by rfl) ⟨5405615, by rfl⟩ : syracuseStep 7207487 = 10811231) B10811231
theorem B1899071 : Blo 1264450 1899071 := bstep (se 1 (by rfl) ⟨1424303, by rfl⟩ : syracuseStep 1899071 = 2848607) B2848607
theorem B6077051 : Blo 1264450 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B5773963 : Blo 1264450 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B3201707 : Blo 1264450 3201707 := bstep (se 1 (by rfl) ⟨2401280, by rfl⟩ : syracuseStep 3201707 = 4802561) B4802561
theorem B1350319 : Blo 1264450 1350319 := bstep (se 1 (by rfl) ⟨1012739, by rfl⟩ : syracuseStep 1350319 = 2025479) B2025479
theorem B1424047 : Blo 1264450 1424047 := bstep (se 1 (by rfl) ⟨1068035, by rfl⟩ : syracuseStep 1424047 = 2136071) B2136071
theorem B1899191 : Blo 1264450 1899191 := bstep (se 1 (by rfl) ⟨1424393, by rfl⟩ : syracuseStep 1899191 = 2848787) B2848787
theorem B2702099 : Blo 1264450 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B3423055 : Blo 1264450 3423055 := bstep (se 1 (by rfl) ⟨2567291, by rfl⟩ : syracuseStep 3423055 = 5134583) B5134583
theorem B12155791 : Blo 1264450 12155791 := bstep (se 1 (by rfl) ⟨9116843, by rfl⟩ : syracuseStep 12155791 = 18233687) B18233687
theorem B1899419 : Blo 1264450 1899419 := bstep (se 1 (by rfl) ⟨1424564, by rfl⟩ : syracuseStep 1899419 = 2849129) B2849129
theorem B3038123 : Blo 1264450 3038123 := bstep (se 1 (by rfl) ⟨2278592, by rfl⟩ : syracuseStep 3038123 = 4557185) B4557185
theorem B1424335 : Blo 1264450 1424335 := bstep (se 1 (by rfl) ⟨1068251, by rfl⟩ : syracuseStep 1424335 = 2136503) B2136503
theorem B2137063 : Blo 1264450 2137063 := bstep (se 1 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 2137063 = 3205595) B3205595
theorem B24665107 : Blo 1264450 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B27720893 : Blo 1264450 27720893 := bstep (se 3 (by rfl) ⟨5197667, by rfl⟩ : syracuseStep 27720893 = 10395335) B10395335
theorem B9739531 : Blo 1264450 9739531 := bstep (se 1 (by rfl) ⟨7304648, by rfl⟩ : syracuseStep 9739531 = 14609297) B14609297
theorem B1424731 : Blo 1264450 1424731 := bstep (se 1 (by rfl) ⟨1068548, by rfl⟩ : syracuseStep 1424731 = 2137097) B2137097
theorem B4054391 : Blo 1264450 4054391 := bstep (se 1 (by rfl) ⟨3040793, by rfl⟩ : syracuseStep 4054391 = 6081587) B6081587
theorem B6405641 : Blo 1264450 6405641 := bstep (se 2 (by rfl) ⟨2402115, by rfl⟩ : syracuseStep 6405641 = 4804231) B4804231
theorem B4390415 : Blo 1264450 4390415 := bstep (se 1 (by rfl) ⟨3292811, by rfl⟩ : syracuseStep 4390415 = 6585623) B6585623
theorem B1801963 : Blo 1264450 1801963 := bstep (se 1 (by rfl) ⟨1351472, by rfl⟩ : syracuseStep 1801963 = 2702945) B2702945
theorem B12156713 : Blo 1264450 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B34611137 : Blo 1264450 34611137 := bstep (se 2 (by rfl) ⟨12979176, by rfl⟩ : syracuseStep 34611137 = 25958353) B25958353
theorem B3203023 : Blo 1264450 3203023 := bstep (se 1 (by rfl) ⟨2402267, by rfl⟩ : syracuseStep 3203023 = 4804535) B4804535
theorem B1802191 : Blo 1264450 1802191 := bstep (se 1 (by rfl) ⟨1351643, by rfl⟩ : syracuseStep 1802191 = 2703287) B2703287
theorem B1286119 : Blo 1264450 1286119 := bstep (se 1 (by rfl) ⟨964589, by rfl⟩ : syracuseStep 1286119 = 1929179) B1929179
theorem B1352143 : Blo 1264450 1352143 := bstep (se 1 (by rfl) ⟨1014107, by rfl⟩ : syracuseStep 1352143 = 2028215) B2028215
theorem B7307815 : Blo 1264450 7307815 := bstep (se 1 (by rfl) ⟨5480861, by rfl⟩ : syracuseStep 7307815 = 10961723) B10961723
theorem B16220843 : Blo 1264450 16220843 := bstep (se 1 (by rfl) ⟨12165632, by rfl⟩ : syracuseStep 16220843 = 24331265) B24331265
theorem B2704175 : Blo 1264450 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B5407631 : Blo 1264450 5407631 := bstep (se 1 (by rfl) ⟨4055723, by rfl⟩ : syracuseStep 5407631 = 8111447) B8111447
theorem B8111015 : Blo 1264450 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B6407099 : Blo 1264450 6407099 := bstep (se 1 (by rfl) ⟨4805324, by rfl⟩ : syracuseStep 6407099 = 9610649) B9610649
theorem B2401235 : Blo 1264450 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B34628651 : Blo 1264450 34628651 := bstep (se 1 (by rfl) ⟨25971488, by rfl⟩ : syracuseStep 34628651 = 51942977) B51942977
theorem B4564073 : Blo 1264450 4564073 := bstep (se 2 (by rfl) ⟨1711527, by rfl⟩ : syracuseStep 4564073 = 3423055) B3423055
theorem B3335375 : Blo 1264450 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B10257623 : Blo 1264450 10257623 := bstep (se 1 (by rfl) ⟨7693217, by rfl⟩ : syracuseStep 10257623 = 15386435) B15386435
theorem B7202155 : Blo 1264450 7202155 := bstep (se 1 (by rfl) ⟨5401616, by rfl⟩ : syracuseStep 7202155 = 10803233) B10803233
theorem B3605897 : Blo 1264450 3605897 := bstep (se 2 (by rfl) ⟨1352211, by rfl⟩ : syracuseStep 3605897 = 2704423) B2704423
theorem B2401903 : Blo 1264450 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B10258073 : Blo 1264450 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B12986041 : Blo 1264450 12986041 := bstep (se 2 (by rfl) ⟨4869765, by rfl⟩ : syracuseStep 12986041 = 9739531) B9739531
theorem B2025415 : Blo 1264450 2025415 := bstep (se 1 (by rfl) ⟨1519061, by rfl⟩ : syracuseStep 2025415 = 3038123) B3038123
theorem B2402617 : Blo 1264450 2402617 := bstep (se 2 (by rfl) ⟨900981, by rfl⟩ : syracuseStep 2402617 = 1801963) B1801963
theorem B3205433 : Blo 1264450 3205433 := bstep (se 2 (by rfl) ⟨1202037, by rfl⟩ : syracuseStep 3205433 = 2404075) B2404075
theorem B4270427 : Blo 1264450 4270427 := bstep (se 1 (by rfl) ⟨3202820, by rfl⟩ : syracuseStep 4270427 = 6405641) B6405641
theorem B2926943 : Blo 1264450 2926943 := bstep (se 1 (by rfl) ⟨2195207, by rfl⟩ : syracuseStep 2926943 = 4390415) B4390415
theorem B8104475 : Blo 1264450 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B4270697 : Blo 1264450 4270697 := bstep (se 2 (by rfl) ⟨1601511, by rfl⟩ : syracuseStep 4270697 = 3203023) B3203023
theorem B2402921 : Blo 1264450 2402921 := bstep (se 2 (by rfl) ⟨901095, by rfl⟩ : syracuseStep 2402921 = 1802191) B1802191
theorem B1714825 : Blo 1264450 1714825 := bstep (se 2 (by rfl) ⟨643059, by rfl⟩ : syracuseStep 1714825 = 1286119) B1286119
theorem B8653499 : Blo 1264450 8653499 := bstep (se 1 (by rfl) ⟨6490124, by rfl⟩ : syracuseStep 8653499 = 12980249) B12980249
theorem B4803259 : Blo 1264450 4803259 := bstep (se 1 (by rfl) ⟨3602444, by rfl⟩ : syracuseStep 4803259 = 7204889) B7204889
theorem B1264475 : Blo 1264450 1264475 := bstep (se 1 (by rfl) ⟨948356, by rfl⟩ : syracuseStep 1264475 = 1896713) B1896713
theorem B1264543 : Blo 1264450 1264543 := bstep (se 1 (by rfl) ⟨948407, by rfl⟩ : syracuseStep 1264543 = 1896815) B1896815
theorem B6163361 : Blo 1264450 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B1264687 : Blo 1264450 1264687 := bstep (se 1 (by rfl) ⟨948515, by rfl⟩ : syracuseStep 1264687 = 1897031) B1897031
theorem B7203887 : Blo 1264450 7203887 := bstep (se 1 (by rfl) ⟨5402915, by rfl⟩ : syracuseStep 7203887 = 10805831) B10805831
theorem B1264711 : Blo 1264450 1264711 := bstep (se 1 (by rfl) ⟨948533, by rfl⟩ : syracuseStep 1264711 = 1897067) B1897067
theorem B2845817 : Blo 1264450 2845817 := bstep (se 2 (by rfl) ⟨1067181, by rfl⟩ : syracuseStep 2845817 = 2134363) B2134363
theorem B24317117 : Blo 1264450 24317117 := bstep (se 3 (by rfl) ⟨4559459, by rfl⟩ : syracuseStep 24317117 = 9118919) B9118919
theorem B12332249 : Blo 1264450 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B1264863 : Blo 1264450 1264863 := bstep (se 1 (by rfl) ⟨948647, by rfl⟩ : syracuseStep 1264863 = 1897295) B1897295
theorem B7204139 : Blo 1264450 7204139 := bstep (se 1 (by rfl) ⟨5403104, by rfl⟩ : syracuseStep 7204139 = 10806209) B10806209
theorem B16215511 : Blo 1264450 16215511 := bstep (se 1 (by rfl) ⟨12161633, by rfl⟩ : syracuseStep 16215511 = 24323267) B24323267
theorem B1265127 : Blo 1264450 1265127 := bstep (se 1 (by rfl) ⟨948845, by rfl⟩ : syracuseStep 1265127 = 1897691) B1897691
theorem B2280935 : Blo 1264450 2280935 := bstep (se 1 (by rfl) ⟨1710701, by rfl⟩ : syracuseStep 2280935 = 3421403) B3421403
theorem B8113679 : Blo 1264450 8113679 := bstep (se 1 (by rfl) ⟨6085259, by rfl⟩ : syracuseStep 8113679 = 12170519) B12170519
theorem B1265243 : Blo 1264450 1265243 := bstep (se 1 (by rfl) ⟨948932, by rfl⟩ : syracuseStep 1265243 = 1897865) B1897865
theorem B4271723 : Blo 1264450 4271723 := bstep (se 1 (by rfl) ⟨3203792, by rfl⟩ : syracuseStep 4271723 = 6407585) B6407585
theorem B2846483 : Blo 1264450 2846483 := bstep (se 1 (by rfl) ⟨2134862, by rfl⟩ : syracuseStep 2846483 = 4269725) B4269725
theorem B1265479 : Blo 1264450 1265479 := bstep (se 1 (by rfl) ⟨949109, by rfl⟩ : syracuseStep 1265479 = 1898219) B1898219
theorem B16207721 : Blo 1264450 16207721 := bstep (se 2 (by rfl) ⟨6077895, by rfl⟩ : syracuseStep 16207721 = 12155791) B12155791
theorem B7696235 : Blo 1264450 7696235 := bstep (se 1 (by rfl) ⟨5772176, by rfl⟩ : syracuseStep 7696235 = 11544353) B11544353
theorem B4271993 : Blo 1264450 4271993 := bstep (se 2 (by rfl) ⟨1601997, by rfl⟩ : syracuseStep 4271993 = 3203995) B3203995
theorem B2133931 : Blo 1264450 2133931 := bstep (se 1 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 2133931 = 3200897) B3200897
theorem B1265631 : Blo 1264450 1265631 := bstep (se 1 (by rfl) ⟨949223, by rfl⟩ : syracuseStep 1265631 = 1898447) B1898447
theorem B32886809 : Blo 1264450 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B92287025 : Blo 1264450 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B2846843 : Blo 1264450 2846843 := bstep (se 1 (by rfl) ⟨2135132, by rfl⟩ : syracuseStep 2846843 = 4270265) B4270265
theorem B12161177 : Blo 1264450 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B4272317 : Blo 1264450 4272317 := bstep (se 3 (by rfl) ⟨801059, by rfl⟩ : syracuseStep 4272317 = 1602119) B1602119
theorem B3903677 : Blo 1264450 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B2134235 : Blo 1264450 2134235 := bstep (se 1 (by rfl) ⟨1600676, by rfl⟩ : syracuseStep 2134235 = 3201353) B3201353
theorem B1265895 : Blo 1264450 1265895 := bstep (se 1 (by rfl) ⟨949421, by rfl⟩ : syracuseStep 1265895 = 1898843) B1898843
theorem B10260863 : Blo 1264450 10260863 := bstep (se 1 (by rfl) ⟨7695647, by rfl⟩ : syracuseStep 10260863 = 15391295) B15391295
theorem B4804991 : Blo 1264450 4804991 := bstep (se 1 (by rfl) ⟨3603743, by rfl⟩ : syracuseStep 4804991 = 7207487) B7207487
theorem B1266047 : Blo 1264450 1266047 := bstep (se 1 (by rfl) ⟨949535, by rfl⟩ : syracuseStep 1266047 = 1899071) B1899071
theorem B2847113 : Blo 1264450 2847113 := bstep (se 2 (by rfl) ⟨1067667, by rfl⟩ : syracuseStep 2847113 = 2135335) B2135335
theorem B4051367 : Blo 1264450 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B2134471 : Blo 1264450 2134471 := bstep (se 1 (by rfl) ⟨1600853, by rfl⟩ : syracuseStep 2134471 = 3201707) B3201707
theorem B1896911 : Blo 1264450 1896911 := bstep (se 1 (by rfl) ⟨1422683, by rfl⟩ : syracuseStep 1896911 = 2845367) B2845367
theorem B1266127 : Blo 1264450 1266127 := bstep (se 1 (by rfl) ⟨949595, by rfl⟩ : syracuseStep 1266127 = 1899191) B1899191
theorem B7205345 : Blo 1264450 7205345 := bstep (se 2 (by rfl) ⟨2702004, by rfl⟩ : syracuseStep 7205345 = 5404009) B5404009
theorem B2134505 : Blo 1264450 2134505 := bstep (se 2 (by rfl) ⟨800439, by rfl⟩ : syracuseStep 2134505 = 1600879) B1600879
theorem B1896953 : Blo 1264450 1896953 := bstep (se 2 (by rfl) ⟨711357, by rfl⟩ : syracuseStep 1896953 = 1422715) B1422715
theorem B1897055 : Blo 1264450 1897055 := bstep (se 1 (by rfl) ⟨1422791, by rfl⟩ : syracuseStep 1897055 = 2845583) B2845583
theorem B1266279 : Blo 1264450 1266279 := bstep (se 1 (by rfl) ⟨949709, by rfl⟩ : syracuseStep 1266279 = 1899419) B1899419
theorem B7205597 : Blo 1264450 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B8221601 : Blo 1264450 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B1897535 : Blo 1264450 1897535 := bstep (se 1 (by rfl) ⟨1423151, by rfl⟩ : syracuseStep 1897535 = 2846303) B2846303
theorem B1897577 : Blo 1264450 1897577 := bstep (se 2 (by rfl) ⟨711591, by rfl⟩ : syracuseStep 1897577 = 1423183) B1423183
theorem B2847851 : Blo 1264450 2847851 := bstep (se 1 (by rfl) ⟨2135888, by rfl⟩ : syracuseStep 2847851 = 4271777) B4271777
theorem B6403211 : Blo 1264450 6403211 := bstep (se 1 (by rfl) ⟨4802408, by rfl⟩ : syracuseStep 6403211 = 9604817) B9604817
theorem B1897679 : Blo 1264450 1897679 := bstep (se 1 (by rfl) ⟨1423259, by rfl⟩ : syracuseStep 1897679 = 2846519) B2846519
theorem B1602767 : Blo 1264450 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B23074091 : Blo 1264450 23074091 := bstep (se 1 (by rfl) ⟨17305568, by rfl⟩ : syracuseStep 23074091 = 34611137) B34611137
theorem B4273505 : Blo 1264450 4273505 := bstep (se 2 (by rfl) ⟨1602564, by rfl⟩ : syracuseStep 4273505 = 3205129) B3205129
theorem B4330871 : Blo 1264450 4330871 := bstep (se 1 (by rfl) ⟨3248153, by rfl⟩ : syracuseStep 4330871 = 6496307) B6496307
theorem B1897883 : Blo 1264450 1897883 := bstep (se 1 (by rfl) ⟨1423412, by rfl⟩ : syracuseStep 1897883 = 2846825) B2846825
theorem B1898105 : Blo 1264450 1898105 := bstep (se 2 (by rfl) ⟨711789, by rfl⟩ : syracuseStep 1898105 = 1423579) B1423579
theorem B2848427 : Blo 1264450 2848427 := bstep (se 1 (by rfl) ⟨2136320, by rfl⟩ : syracuseStep 2848427 = 4272641) B4272641
theorem B1898207 : Blo 1264450 1898207 := bstep (se 1 (by rfl) ⟨1423655, by rfl⟩ : syracuseStep 1898207 = 2847311) B2847311
theorem B3602171 : Blo 1264450 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B1898303 : Blo 1264450 1898303 := bstep (se 1 (by rfl) ⟨1423727, by rfl⟩ : syracuseStep 1898303 = 2847455) B2847455
theorem B18233225 : Blo 1264450 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B14423993 : Blo 1264450 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B10958813 : Blo 1264450 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B1898471 : Blo 1264450 1898471 := bstep (se 1 (by rfl) ⟨1423853, by rfl⟩ : syracuseStep 1898471 = 2847707) B2847707
theorem B2848751 : Blo 1264450 2848751 := bstep (se 1 (by rfl) ⟨2136563, by rfl⟩ : syracuseStep 2848751 = 4273127) B4273127
theorem B1898489 : Blo 1264450 1898489 := bstep (se 2 (by rfl) ⟨711933, by rfl⟩ : syracuseStep 1898489 = 1423867) B1423867
theorem B12171323 : Blo 1264450 12171323 := bstep (se 1 (by rfl) ⟨9128492, by rfl⟩ : syracuseStep 12171323 = 18256985) B18256985
theorem B1898591 : Blo 1264450 1898591 := bstep (se 1 (by rfl) ⟨1423943, by rfl⟩ : syracuseStep 1898591 = 2847887) B2847887
theorem B7207055 : Blo 1264450 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B1898651 : Blo 1264450 1898651 := bstep (se 1 (by rfl) ⟨1423988, by rfl⟩ : syracuseStep 1898651 = 2847977) B2847977
theorem B7698617 : Blo 1264450 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B1898687 : Blo 1264450 1898687 := bstep (se 1 (by rfl) ⟨1424015, by rfl⟩ : syracuseStep 1898687 = 2848031) B2848031
theorem B2848967 : Blo 1264450 2848967 := bstep (se 1 (by rfl) ⟨2136725, by rfl⟩ : syracuseStep 2848967 = 4273451) B4273451
theorem B1800425 : Blo 1264450 1800425 := bstep (se 2 (by rfl) ⟨675159, by rfl⟩ : syracuseStep 1800425 = 1350319) B1350319
theorem B1898729 : Blo 1264450 1898729 := bstep (se 2 (by rfl) ⟨712023, by rfl⟩ : syracuseStep 1898729 = 1424047) B1424047
theorem B2136361 : Blo 1264450 2136361 := bstep (se 2 (by rfl) ⟨801135, by rfl⟩ : syracuseStep 2136361 = 1602271) B1602271
theorem B3201403 : Blo 1264450 3201403 := bstep (se 1 (by rfl) ⟨2401052, by rfl⟩ : syracuseStep 3201403 = 4802105) B4802105
theorem B2849147 : Blo 1264450 2849147 := bstep (se 1 (by rfl) ⟨2136860, by rfl⟩ : syracuseStep 2849147 = 4273721) B4273721
theorem B1899035 : Blo 1264450 1899035 := bstep (se 1 (by rfl) ⟨1424276, by rfl⟩ : syracuseStep 1899035 = 2848553) B2848553
theorem B1423903 : Blo 1264450 1423903 := bstep (se 1 (by rfl) ⟨1067927, by rfl⟩ : syracuseStep 1423903 = 2135855) B2135855
theorem B1899113 : Blo 1264450 1899113 := bstep (se 2 (by rfl) ⟨712167, by rfl⟩ : syracuseStep 1899113 = 1424335) B1424335
theorem B2849417 : Blo 1264450 2849417 := bstep (se 2 (by rfl) ⟨1068531, by rfl⟩ : syracuseStep 2849417 = 2137063) B2137063
theorem B6085277 : Blo 1264450 6085277 := bstep (se 3 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 6085277 = 2281979) B2281979
theorem B6404831 : Blo 1264450 6404831 := bstep (se 1 (by rfl) ⟨4803623, by rfl⟩ : syracuseStep 6404831 = 9607247) B9607247
theorem B6077263 : Blo 1264450 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B34634699 : Blo 1264450 34634699 := bstep (se 1 (by rfl) ⟨25976024, by rfl⟩ : syracuseStep 34634699 = 51952049) B51952049
theorem B31210447 : Blo 1264450 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B14605379 : Blo 1264450 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B1711225 : Blo 1264450 1711225 := bstep (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) B1283419
theorem B1899641 : Blo 1264450 1899641 := bstep (se 2 (by rfl) ⟨712365, by rfl⟩ : syracuseStep 1899641 = 1424731) B1424731
theorem B9116819 : Blo 1264450 9116819 := bstep (se 1 (by rfl) ⟨6837614, by rfl⟩ : syracuseStep 9116819 = 13675229) B13675229
theorem B18480595 : Blo 1264450 18480595 := bstep (se 1 (by rfl) ⟨13860446, by rfl⟩ : syracuseStep 18480595 = 27720893) B27720893
theorem B2702927 : Blo 1264450 2702927 := bstep (se 1 (by rfl) ⟨2027195, by rfl⟩ : syracuseStep 2702927 = 4054391) B4054391
theorem B49340177 : Blo 1264450 49340177 := bstep (se 2 (by rfl) ⟨18502566, by rfl⟩ : syracuseStep 49340177 = 37005133) B37005133
theorem B16203725 : Blo 1264450 16203725 := bstep (se 3 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 16203725 = 6076397) B6076397
theorem B6840575 : Blo 1264450 6840575 := bstep (se 1 (by rfl) ⟨5130431, by rfl⟩ : syracuseStep 6840575 = 10260863) B10260863
theorem B3203327 : Blo 1264450 3203327 := bstep (se 1 (by rfl) ⟨2402495, by rfl⟩ : syracuseStep 3203327 = 4804991) B4804991
theorem B3203489 : Blo 1264450 3203489 := bstep (se 2 (by rfl) ⟨1201308, by rfl⟩ : syracuseStep 3203489 = 2402617) B2402617
theorem B10813895 : Blo 1264450 10813895 := bstep (se 1 (by rfl) ⟨8110421, by rfl⟩ : syracuseStep 10813895 = 16220843) B16220843
theorem B4268537 : Blo 1264450 4268537 := bstep (se 2 (by rfl) ⟨1600701, by rfl⟩ : syracuseStep 4268537 = 3201403) B3201403
theorem B1802783 : Blo 1264450 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B3605087 : Blo 1264450 3605087 := bstep (se 1 (by rfl) ⟨2703815, by rfl⟩ : syracuseStep 3605087 = 5407631) B5407631
theorem B5481067 : Blo 1264450 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B4801133 : Blo 1264450 4801133 := bstep (se 3 (by rfl) ⟨900212, by rfl⟩ : syracuseStep 4801133 = 1800425) B1800425
theorem B5407343 : Blo 1264450 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B9126533 : Blo 1264450 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B23085767 : Blo 1264450 23085767 := bstep (se 1 (by rfl) ⟨17314325, by rfl⟩ : syracuseStep 23085767 = 34628651) B34628651
theorem B4268807 : Blo 1264450 4268807 := bstep (se 1 (by rfl) ⟨3201605, by rfl⟩ : syracuseStep 4268807 = 6403211) B6403211
theorem B2286433 : Blo 1264450 2286433 := bstep (se 2 (by rfl) ⟨857412, by rfl⟩ : syracuseStep 2286433 = 1714825) B1714825
theorem B8103017 : Blo 1264450 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B21611933 : Blo 1264450 21611933 := bstep (se 3 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 21611933 = 8104475) B8104475
theorem B1951295 : Blo 1264450 1951295 := bstep (se 1 (by rfl) ⟨1463471, by rfl⟩ : syracuseStep 1951295 = 2926943) B2926943
theorem B4056851 : Blo 1264450 4056851 := bstep (se 1 (by rfl) ⟨3042638, by rfl⟩ : syracuseStep 4056851 = 6085277) B6085277
theorem B5768999 : Blo 1264450 5768999 := bstep (se 1 (by rfl) ⟨4326749, by rfl⟩ : syracuseStep 5768999 = 8653499) B8653499
theorem B9602873 : Blo 1264450 9602873 := bstep (se 2 (by rfl) ⟨3601077, by rfl⟩ : syracuseStep 9602873 = 7202155) B7202155
theorem B4269887 : Blo 1264450 4269887 := bstep (se 1 (by rfl) ⟨3202415, by rfl⟩ : syracuseStep 4269887 = 6404831) B6404831
theorem B21620681 : Blo 1264450 21620681 := bstep (se 2 (by rfl) ⟨8107755, by rfl⟩ : syracuseStep 21620681 = 16215511) B16215511
theorem B4802591 : Blo 1264450 4802591 := bstep (se 1 (by rfl) ⟨3601943, by rfl⟩ : syracuseStep 4802591 = 7203887) B7203887
theorem B4802759 : Blo 1264450 4802759 := bstep (se 1 (by rfl) ⟨3602069, by rfl⟩ : syracuseStep 4802759 = 7204139) B7204139
theorem B5409119 : Blo 1264450 5409119 := bstep (se 1 (by rfl) ⟨4056839, by rfl⟩ : syracuseStep 5409119 = 8113679) B8113679
theorem B7211429 : Blo 1264450 7211429 := bstep (se 4 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 7211429 = 1352143) B1352143
theorem B32893451 : Blo 1264450 32893451 := bstep (se 1 (by rfl) ⟨24670088, by rfl⟩ : syracuseStep 32893451 = 49340177) B49340177
theorem B2845241 : Blo 1264450 2845241 := bstep (se 2 (by rfl) ⟨1066965, by rfl⟩ : syracuseStep 2845241 = 2133931) B2133931
theorem B5130823 : Blo 1264450 5130823 := bstep (se 1 (by rfl) ⟨3848117, by rfl⟩ : syracuseStep 5130823 = 7696235) B7696235
theorem B21924539 : Blo 1264450 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B61524683 : Blo 1264450 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B1264607 : Blo 1264450 1264607 := bstep (se 1 (by rfl) ⟨948455, by rfl⟩ : syracuseStep 1264607 = 1896911) B1896911
theorem B4803563 : Blo 1264450 4803563 := bstep (se 1 (by rfl) ⟨3602672, by rfl⟩ : syracuseStep 4803563 = 7205345) B7205345
theorem B1264635 : Blo 1264450 1264635 := bstep (se 1 (by rfl) ⟨948476, by rfl⟩ : syracuseStep 1264635 = 1896953) B1896953
theorem B1264703 : Blo 1264450 1264703 := bstep (se 1 (by rfl) ⟨948527, by rfl⟩ : syracuseStep 1264703 = 1897055) B1897055
theorem B4803731 : Blo 1264450 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B2845961 : Blo 1264450 2845961 := bstep (se 2 (by rfl) ⟨1067235, by rfl⟩ : syracuseStep 2845961 = 2134471) B2134471
theorem B4271399 : Blo 1264450 4271399 := bstep (se 1 (by rfl) ⟨3203549, by rfl⟩ : syracuseStep 4271399 = 6407099) B6407099
theorem B1600823 : Blo 1264450 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B1265023 : Blo 1264450 1265023 := bstep (se 1 (by rfl) ⟨948767, by rfl⟩ : syracuseStep 1265023 = 1897535) B1897535
theorem B9743753 : Blo 1264450 9743753 := bstep (se 2 (by rfl) ⟨3653907, by rfl⟩ : syracuseStep 9743753 = 7307815) B7307815
theorem B1265051 : Blo 1264450 1265051 := bstep (se 1 (by rfl) ⟨948788, by rfl⟩ : syracuseStep 1265051 = 1897577) B1897577
theorem B1265119 : Blo 1264450 1265119 := bstep (se 1 (by rfl) ⟨948839, by rfl⟩ : syracuseStep 1265119 = 1897679) B1897679
theorem B2887247 : Blo 1264450 2887247 := bstep (se 1 (by rfl) ⟨2165435, by rfl⟩ : syracuseStep 2887247 = 4330871) B4330871
theorem B2403931 : Blo 1264450 2403931 := bstep (se 1 (by rfl) ⟨1802948, by rfl⟩ : syracuseStep 2403931 = 3605897) B3605897
theorem B1265255 : Blo 1264450 1265255 := bstep (se 1 (by rfl) ⟨948941, by rfl⟩ : syracuseStep 1265255 = 1897883) B1897883
theorem B1265403 : Blo 1264450 1265403 := bstep (se 1 (by rfl) ⟨949052, by rfl⟩ : syracuseStep 1265403 = 1898105) B1898105
theorem B1265471 : Blo 1264450 1265471 := bstep (se 1 (by rfl) ⟨949103, by rfl⟩ : syracuseStep 1265471 = 1898207) B1898207
theorem B1265535 : Blo 1264450 1265535 := bstep (se 1 (by rfl) ⟨949151, by rfl⟩ : syracuseStep 1265535 = 1898303) B1898303
theorem B1265647 : Blo 1264450 1265647 := bstep (se 1 (by rfl) ⟨949235, by rfl⟩ : syracuseStep 1265647 = 1898471) B1898471
theorem B1265659 : Blo 1264450 1265659 := bstep (se 1 (by rfl) ⟨949244, by rfl⟩ : syracuseStep 1265659 = 1898489) B1898489
theorem B8114215 : Blo 1264450 8114215 := bstep (se 1 (by rfl) ⟨6085661, by rfl⟩ : syracuseStep 8114215 = 12171323) B12171323
theorem B1265727 : Blo 1264450 1265727 := bstep (se 1 (by rfl) ⟨949295, by rfl⟩ : syracuseStep 1265727 = 1898591) B1898591
theorem B4804703 : Blo 1264450 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B1265767 : Blo 1264450 1265767 := bstep (se 1 (by rfl) ⟨949325, by rfl⟩ : syracuseStep 1265767 = 1898651) B1898651
theorem B5132411 : Blo 1264450 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B1265791 : Blo 1264450 1265791 := bstep (se 1 (by rfl) ⟨949343, by rfl⟩ : syracuseStep 1265791 = 1898687) B1898687
theorem B1265819 : Blo 1264450 1265819 := bstep (se 1 (by rfl) ⟨949364, by rfl⟩ : syracuseStep 1265819 = 1898729) B1898729
theorem B2846951 : Blo 1264450 2846951 := bstep (se 1 (by rfl) ⟨2135213, by rfl⟩ : syracuseStep 2846951 = 4270427) B4270427
theorem B1266023 : Blo 1264450 1266023 := bstep (se 1 (by rfl) ⟨949517, by rfl⟩ : syracuseStep 1266023 = 1899035) B1899035
theorem B2847131 : Blo 1264450 2847131 := bstep (se 1 (by rfl) ⟨2135348, by rfl⟩ : syracuseStep 2847131 = 4270697) B4270697
theorem B1601947 : Blo 1264450 1601947 := bstep (se 1 (by rfl) ⟨1201460, by rfl⟩ : syracuseStep 1601947 = 2402921) B2402921
theorem B1266075 : Blo 1264450 1266075 := bstep (se 1 (by rfl) ⟨949556, by rfl⟩ : syracuseStep 1266075 = 1899113) B1899113
theorem B4108907 : Blo 1264450 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B23089799 : Blo 1264450 23089799 := bstep (se 1 (by rfl) ⟨17317349, by rfl⟩ : syracuseStep 23089799 = 34634699) B34634699
theorem B9605789 : Blo 1264450 9605789 := bstep (se 3 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 9605789 = 3602171) B3602171
theorem B9736919 : Blo 1264450 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B1897211 : Blo 1264450 1897211 := bstep (se 1 (by rfl) ⟨1422908, by rfl⟩ : syracuseStep 1897211 = 2845817) B2845817
theorem B1266427 : Blo 1264450 1266427 := bstep (se 1 (by rfl) ⟨949820, by rfl⟩ : syracuseStep 1266427 = 1899641) B1899641
theorem B8221499 : Blo 1264450 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B17314721 : Blo 1264450 17314721 := bstep (se 2 (by rfl) ⟨6493020, by rfl⟩ : syracuseStep 17314721 = 12986041) B12986041
theorem B1520623 : Blo 1264450 1520623 := bstep (se 1 (by rfl) ⟨1140467, by rfl⟩ : syracuseStep 1520623 = 2280935) B2280935
theorem B2847815 : Blo 1264450 2847815 := bstep (se 1 (by rfl) ⟨2135861, by rfl⟩ : syracuseStep 2847815 = 4271723) B4271723
theorem B1897655 : Blo 1264450 1897655 := bstep (se 1 (by rfl) ⟨1423241, by rfl⟩ : syracuseStep 1897655 = 2846483) B2846483
theorem B2847995 : Blo 1264450 2847995 := bstep (se 1 (by rfl) ⟨2135996, by rfl⟩ : syracuseStep 2847995 = 4271993) B4271993
theorem B2700553 : Blo 1264450 2700553 := bstep (se 2 (by rfl) ⟨1012707, by rfl⟩ : syracuseStep 2700553 = 2025415) B2025415
theorem B10802483 : Blo 1264450 10802483 := bstep (se 1 (by rfl) ⟨8101862, by rfl⟩ : syracuseStep 10802483 = 16203725) B16203725
theorem B1897895 : Blo 1264450 1897895 := bstep (se 1 (by rfl) ⟨1423421, by rfl⟩ : syracuseStep 1897895 = 2846843) B2846843
theorem B8107451 : Blo 1264450 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B2848211 : Blo 1264450 2848211 := bstep (se 1 (by rfl) ⟨2136158, by rfl⟩ : syracuseStep 2848211 = 4272317) B4272317
theorem B2602451 : Blo 1264450 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B1422823 : Blo 1264450 1422823 := bstep (se 1 (by rfl) ⟨1067117, by rfl⟩ : syracuseStep 1422823 = 2134235) B2134235
theorem B1898075 : Blo 1264450 1898075 := bstep (se 1 (by rfl) ⟨1423556, by rfl⟩ : syracuseStep 1898075 = 2847113) B2847113
theorem B12170861 : Blo 1264450 12170861 := bstep (se 3 (by rfl) ⟨2282036, by rfl⟩ : syracuseStep 12170861 = 4564073) B4564073
theorem B2700911 : Blo 1264450 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B1423003 : Blo 1264450 1423003 := bstep (se 1 (by rfl) ⟨1067252, by rfl⟩ : syracuseStep 1423003 = 2134505) B2134505
theorem B2848481 : Blo 1264450 2848481 := bstep (se 2 (by rfl) ⟨1068180, by rfl⟩ : syracuseStep 2848481 = 2136361) B2136361
theorem B8894333 : Blo 1264450 8894333 := bstep (se 3 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 8894333 = 3335375) B3335375
theorem B4274045 : Blo 1264450 4274045 := bstep (se 3 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 4274045 = 1602767) B1602767
theorem B1898537 : Blo 1264450 1898537 := bstep (se 2 (by rfl) ⟨711951, by rfl⟩ : syracuseStep 1898537 = 1423903) B1423903
theorem B1898567 : Blo 1264450 1898567 := bstep (se 1 (by rfl) ⟨1423925, by rfl⟩ : syracuseStep 1898567 = 2847851) B2847851
theorem B6838415 : Blo 1264450 6838415 := bstep (se 1 (by rfl) ⟨5128811, by rfl⟩ : syracuseStep 6838415 = 10257623) B10257623
theorem B15382727 : Blo 1264450 15382727 := bstep (se 1 (by rfl) ⟨11537045, by rfl⟩ : syracuseStep 15382727 = 23074091) B23074091
theorem B2849003 : Blo 1264450 2849003 := bstep (se 1 (by rfl) ⟨2136752, by rfl⟩ : syracuseStep 2849003 = 4273505) B4273505
theorem B6404345 : Blo 1264450 6404345 := bstep (se 2 (by rfl) ⟨2401629, by rfl⟩ : syracuseStep 6404345 = 4803259) B4803259
theorem B6838715 : Blo 1264450 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B1898951 : Blo 1264450 1898951 := bstep (se 1 (by rfl) ⟨1424213, by rfl⟩ : syracuseStep 1898951 = 2848427) B2848427
theorem B12155483 : Blo 1264450 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B41613929 : Blo 1264450 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B9615995 : Blo 1264450 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B7305875 : Blo 1264450 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B1899167 : Blo 1264450 1899167 := bstep (se 1 (by rfl) ⟨1424375, by rfl⟩ : syracuseStep 1899167 = 2848751) B2848751
theorem B1899311 : Blo 1264450 1899311 := bstep (se 1 (by rfl) ⟨1424483, by rfl⟩ : syracuseStep 1899311 = 2848967) B2848967
theorem B2136955 : Blo 1264450 2136955 := bstep (se 1 (by rfl) ⟨1602716, by rfl⟩ : syracuseStep 2136955 = 3205433) B3205433
theorem B7207805 : Blo 1264450 7207805 := bstep (se 3 (by rfl) ⟨1351463, by rfl⟩ : syracuseStep 7207805 = 2702927) B2702927
theorem B1899431 : Blo 1264450 1899431 := bstep (se 1 (by rfl) ⟨1424573, by rfl⟩ : syracuseStep 1899431 = 2849147) B2849147
theorem B1899611 : Blo 1264450 1899611 := bstep (se 1 (by rfl) ⟨1424708, by rfl⟩ : syracuseStep 1899611 = 2849417) B2849417
theorem B24640793 : Blo 1264450 24640793 := bstep (se 2 (by rfl) ⟨9240297, by rfl⟩ : syracuseStep 24640793 = 18480595) B18480595
theorem B6077879 : Blo 1264450 6077879 := bstep (se 1 (by rfl) ⟨4558409, by rfl⟩ : syracuseStep 6077879 = 9116819) B9116819
theorem B16211411 : Blo 1264450 16211411 := bstep (se 1 (by rfl) ⟨12158558, by rfl⟩ : syracuseStep 16211411 = 24317117) B24317117
theorem B3202537 : Blo 1264450 3202537 := bstep (se 2 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 3202537 = 2401903) B2401903
theorem B10805147 : Blo 1264450 10805147 := bstep (se 1 (by rfl) ⟨8103860, by rfl⟩ : syracuseStep 10805147 = 16207721) B16207721
theorem B3203135 : Blo 1264450 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B7209263 : Blo 1264450 7209263 := bstep (se 1 (by rfl) ⟨5406947, by rfl⟩ : syracuseStep 7209263 = 10813895) B10813895
theorem B3604895 : Blo 1264450 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B15393199 : Blo 1264450 15393199 := bstep (se 1 (by rfl) ⟨11544899, by rfl⟩ : syracuseStep 15393199 = 23089799) B23089799
theorem B5480999 : Blo 1264450 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B11543147 : Blo 1264450 11543147 := bstep (se 1 (by rfl) ⟨8657360, by rfl⟩ : syracuseStep 11543147 = 17314721) B17314721
theorem B6841097 : Blo 1264450 6841097 := bstep (se 2 (by rfl) ⟨2565411, by rfl⟩ : syracuseStep 6841097 = 5130823) B5130823
theorem B7308089 : Blo 1264450 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B4268861 : Blo 1264450 4268861 := bstep (se 3 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 4268861 = 1600823) B1600823
theorem B7201655 : Blo 1264450 7201655 := bstep (se 1 (by rfl) ⟨5401241, by rfl⟩ : syracuseStep 7201655 = 10802483) B10802483
theorem B3048577 : Blo 1264450 3048577 := bstep (se 2 (by rfl) ⟨1143216, by rfl⟩ : syracuseStep 3048577 = 2286433) B2286433
theorem B18236573 : Blo 1264450 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B4269563 : Blo 1264450 4269563 := bstep (se 1 (by rfl) ⟨3202172, by rfl⟩ : syracuseStep 4269563 = 6404345) B6404345
theorem B3606079 : Blo 1264450 3606079 := bstep (se 1 (by rfl) ⟨2704559, by rfl⟩ : syracuseStep 3606079 = 5409119) B5409119
theorem B7202429 : Blo 1264450 7202429 := bstep (se 3 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 7202429 = 2700911) B2700911
theorem B8103655 : Blo 1264450 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B14616359 : Blo 1264450 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B4270049 : Blo 1264450 4270049 := bstep (se 2 (by rfl) ⟨1601268, by rfl⟩ : syracuseStep 4270049 = 3202537) B3202537
theorem B3205241 : Blo 1264450 3205241 := bstep (se 2 (by rfl) ⟨1201965, by rfl⟩ : syracuseStep 3205241 = 2403931) B2403931
theorem B16427195 : Blo 1264450 16427195 := bstep (se 1 (by rfl) ⟨12320396, by rfl⟩ : syracuseStep 16427195 = 24640793) B24640793
theorem B10807607 : Blo 1264450 10807607 := bstep (se 1 (by rfl) ⟨8105705, by rfl⟩ : syracuseStep 10807607 = 16211411) B16211411
theorem B23718221 : Blo 1264450 23718221 := bstep (se 3 (by rfl) ⟨4447166, by rfl⟩ : syracuseStep 23718221 = 8894333) B8894333
theorem B7203431 : Blo 1264450 7203431 := bstep (se 1 (by rfl) ⟨5402573, by rfl⟩ : syracuseStep 7203431 = 10805147) B10805147
theorem B2845691 : Blo 1264450 2845691 := bstep (se 1 (by rfl) ⟨2134268, by rfl⟩ : syracuseStep 2845691 = 4268537) B4268537
theorem B2739271 : Blo 1264450 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B6491279 : Blo 1264450 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B1264807 : Blo 1264450 1264807 := bstep (se 1 (by rfl) ⟨948605, by rfl⟩ : syracuseStep 1264807 = 1897211) B1897211
theorem B2845871 : Blo 1264450 2845871 := bstep (se 1 (by rfl) ⟨2134403, by rfl⟩ : syracuseStep 2845871 = 4268807) B4268807
theorem B5402011 : Blo 1264450 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B1265103 : Blo 1264450 1265103 := bstep (se 1 (by rfl) ⟨948827, by rfl⟩ : syracuseStep 1265103 = 1897655) B1897655
theorem B1265263 : Blo 1264450 1265263 := bstep (se 1 (by rfl) ⟨948947, by rfl⟩ : syracuseStep 1265263 = 1897895) B1897895
theorem B1265383 : Blo 1264450 1265383 := bstep (se 1 (by rfl) ⟨949037, by rfl⟩ : syracuseStep 1265383 = 1898075) B1898075
theorem B8113907 : Blo 1264450 8113907 := bstep (se 1 (by rfl) ⟨6085430, by rfl⟩ : syracuseStep 8113907 = 12170861) B12170861
theorem B3845999 : Blo 1264450 3845999 := bstep (se 1 (by rfl) ⟨2884499, by rfl⟩ : syracuseStep 3845999 = 5768999) B5768999
theorem B6401915 : Blo 1264450 6401915 := bstep (se 1 (by rfl) ⟨4801436, by rfl⟩ : syracuseStep 6401915 = 9602873) B9602873
theorem B2846591 : Blo 1264450 2846591 := bstep (se 1 (by rfl) ⟨2134943, by rfl⟩ : syracuseStep 2846591 = 4269887) B4269887
theorem B14413787 : Blo 1264450 14413787 := bstep (se 1 (by rfl) ⟨10810340, by rfl⟩ : syracuseStep 14413787 = 21620681) B21620681
theorem B1265691 : Blo 1264450 1265691 := bstep (se 1 (by rfl) ⟨949268, by rfl⟩ : syracuseStep 1265691 = 1898537) B1898537
theorem B1265711 : Blo 1264450 1265711 := bstep (se 1 (by rfl) ⟨949283, by rfl⟩ : syracuseStep 1265711 = 1898567) B1898567
theorem B4558943 : Blo 1264450 4558943 := bstep (se 1 (by rfl) ⟨3419207, by rfl⟩ : syracuseStep 4558943 = 6838415) B6838415
theorem B9613565 : Blo 1264450 9613565 := bstep (se 3 (by rfl) ⟨1802543, by rfl⟩ : syracuseStep 9613565 = 3605087) B3605087
theorem B1265967 : Blo 1264450 1265967 := bstep (se 1 (by rfl) ⟨949475, by rfl⟩ : syracuseStep 1265967 = 1898951) B1898951
theorem B3600737 : Blo 1264450 3600737 := bstep (se 2 (by rfl) ⟨1350276, by rfl⟩ : syracuseStep 3600737 = 2700553) B2700553
theorem B1896827 : Blo 1264450 1896827 := bstep (se 1 (by rfl) ⟨1422620, by rfl⟩ : syracuseStep 1896827 = 2845241) B2845241
theorem B27742619 : Blo 1264450 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B6410663 : Blo 1264450 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B4870583 : Blo 1264450 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B1266111 : Blo 1264450 1266111 := bstep (se 1 (by rfl) ⟨949583, by rfl⟩ : syracuseStep 1266111 = 1899167) B1899167
theorem B1266207 : Blo 1264450 1266207 := bstep (se 1 (by rfl) ⟨949655, by rfl⟩ : syracuseStep 1266207 = 1899311) B1899311
theorem B4805203 : Blo 1264450 4805203 := bstep (se 1 (by rfl) ⟨3603902, by rfl⟩ : syracuseStep 4805203 = 7207805) B7207805
theorem B1266287 : Blo 1264450 1266287 := bstep (se 1 (by rfl) ⟨949715, by rfl⟩ : syracuseStep 1266287 = 1899431) B1899431
theorem B1897097 : Blo 1264450 1897097 := bstep (se 2 (by rfl) ⟨711411, by rfl⟩ : syracuseStep 1897097 = 1422823) B1422823
theorem B10818269 : Blo 1264450 10818269 := bstep (se 3 (by rfl) ⟨2028425, by rfl⟩ : syracuseStep 10818269 = 4056851) B4056851
theorem B1266407 : Blo 1264450 1266407 := bstep (se 1 (by rfl) ⟨949805, by rfl⟩ : syracuseStep 1266407 = 1899611) B1899611
theorem B1897307 : Blo 1264450 1897307 := bstep (se 1 (by rfl) ⟨1422980, by rfl⟩ : syracuseStep 1897307 = 2845961) B2845961
theorem B2847599 : Blo 1264450 2847599 := bstep (se 1 (by rfl) ⟨2135699, by rfl⟩ : syracuseStep 2847599 = 4271399) B4271399
theorem B1897337 : Blo 1264450 1897337 := bstep (se 2 (by rfl) ⟨711501, by rfl⟩ : syracuseStep 1897337 = 1423003) B1423003
theorem B4051919 : Blo 1264450 4051919 := bstep (se 1 (by rfl) ⟨3038939, by rfl⟩ : syracuseStep 4051919 = 6077879) B6077879
theorem B10818953 : Blo 1264450 10818953 := bstep (se 2 (by rfl) ⟨4057107, by rfl⟩ : syracuseStep 10818953 = 8114215) B8114215
theorem B3421607 : Blo 1264450 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B1897967 : Blo 1264450 1897967 := bstep (se 1 (by rfl) ⟨1423475, by rfl⟩ : syracuseStep 1897967 = 2846951) B2846951
theorem B4560383 : Blo 1264450 4560383 := bstep (se 1 (by rfl) ⟨3420287, by rfl⟩ : syracuseStep 4560383 = 6840575) B6840575
theorem B2135551 : Blo 1264450 2135551 := bstep (se 1 (by rfl) ⟨1601663, by rfl⟩ : syracuseStep 2135551 = 3203327) B3203327
theorem B1898087 : Blo 1264450 1898087 := bstep (se 1 (by rfl) ⟨1423565, by rfl⟩ : syracuseStep 1898087 = 2847131) B2847131
theorem B2135659 : Blo 1264450 2135659 := bstep (se 1 (by rfl) ⟨1601744, by rfl⟩ : syracuseStep 2135659 = 3203489) B3203489
theorem B3200755 : Blo 1264450 3200755 := bstep (se 1 (by rfl) ⟨2400566, by rfl⟩ : syracuseStep 3200755 = 4801133) B4801133
theorem B6084355 : Blo 1264450 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B6403859 : Blo 1264450 6403859 := bstep (se 1 (by rfl) ⟨4802894, by rfl⟩ : syracuseStep 6403859 = 9605789) B9605789
theorem B2135929 : Blo 1264450 2135929 := bstep (se 2 (by rfl) ⟨800973, by rfl⟩ : syracuseStep 2135929 = 1601947) B1601947
theorem B20813813 : Blo 1264450 20813813 := bstep (se 5 (by rfl) ⟨975647, by rfl⟩ : syracuseStep 20813813 = 1951295) B1951295
theorem B1898543 : Blo 1264450 1898543 := bstep (se 1 (by rfl) ⟨1423907, by rfl⟩ : syracuseStep 1898543 = 2847815) B2847815
theorem B1898663 : Blo 1264450 1898663 := bstep (se 1 (by rfl) ⟨1423997, by rfl⟩ : syracuseStep 1898663 = 2847995) B2847995
theorem B14407955 : Blo 1264450 14407955 := bstep (se 1 (by rfl) ⟨10805966, by rfl⟩ : syracuseStep 14407955 = 21611933) B21611933
theorem B5404967 : Blo 1264450 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B1898807 : Blo 1264450 1898807 := bstep (se 1 (by rfl) ⟨1424105, by rfl⟩ : syracuseStep 1898807 = 2848211) B2848211
theorem B1734967 : Blo 1264450 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B1898987 : Blo 1264450 1898987 := bstep (se 1 (by rfl) ⟨1424240, by rfl⟩ : syracuseStep 1898987 = 2848481) B2848481
theorem B2849273 : Blo 1264450 2849273 := bstep (se 2 (by rfl) ⟨1068477, by rfl⟩ : syracuseStep 2849273 = 2136955) B2136955
theorem B2849363 : Blo 1264450 2849363 := bstep (se 1 (by rfl) ⟨2137022, by rfl⟩ : syracuseStep 2849363 = 4274045) B4274045
theorem B3201727 : Blo 1264450 3201727 := bstep (se 1 (by rfl) ⟨2401295, by rfl⟩ : syracuseStep 3201727 = 4802591) B4802591
theorem B4807421 : Blo 1264450 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B10255151 : Blo 1264450 10255151 := bstep (se 1 (by rfl) ⟨7691363, by rfl⟩ : syracuseStep 10255151 = 15382727) B15382727
theorem B3201839 : Blo 1264450 3201839 := bstep (se 1 (by rfl) ⟨2401379, by rfl⟩ : syracuseStep 3201839 = 4802759) B4802759
theorem B1899335 : Blo 1264450 1899335 := bstep (se 1 (by rfl) ⟨1424501, by rfl⟩ : syracuseStep 1899335 = 2849003) B2849003
theorem B4807619 : Blo 1264450 4807619 := bstep (se 1 (by rfl) ⟨3605714, by rfl⟩ : syracuseStep 4807619 = 7211429) B7211429
theorem B21928967 : Blo 1264450 21928967 := bstep (se 1 (by rfl) ⟨16446725, by rfl⟩ : syracuseStep 21928967 = 32893451) B32893451
theorem B41016455 : Blo 1264450 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B61562045 : Blo 1264450 61562045 := bstep (se 3 (by rfl) ⟨11542883, by rfl⟩ : syracuseStep 61562045 = 23085767) B23085767
theorem B3202375 : Blo 1264450 3202375 := bstep (se 1 (by rfl) ⟨2401781, by rfl⟩ : syracuseStep 3202375 = 4803563) B4803563
theorem B3202487 : Blo 1264450 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B6495835 : Blo 1264450 6495835 := bstep (se 1 (by rfl) ⟨4871876, by rfl⟩ : syracuseStep 6495835 = 9743753) B9743753
theorem B1924831 : Blo 1264450 1924831 := bstep (se 1 (by rfl) ⟨1443623, by rfl⟩ : syracuseStep 1924831 = 2887247) B2887247
theorem B8109989 : Blo 1264450 8109989 := bstep (se 4 (by rfl) ⟨760311, by rfl⟩ : syracuseStep 8109989 = 1520623) B1520623
theorem B3039295 : Blo 1264450 3039295 := bstep (se 1 (by rfl) ⟨2279471, by rfl⟩ : syracuseStep 3039295 = 4558943) B4558943
theorem B2400491 : Blo 1264450 2400491 := bstep (se 1 (by rfl) ⟨1800368, by rfl⟩ : syracuseStep 2400491 = 3600737) B3600737
theorem B3653999 : Blo 1264450 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B4801103 : Blo 1264450 4801103 := bstep (se 1 (by rfl) ⟨3600827, by rfl⟩ : syracuseStep 4801103 = 7201655) B7201655
theorem B12157715 : Blo 1264450 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B6406937 : Blo 1264450 6406937 := bstep (se 2 (by rfl) ⟨2402601, by rfl⟩ : syracuseStep 6406937 = 4805203) B4805203
theorem B4268969 : Blo 1264450 4268969 := bstep (se 2 (by rfl) ⟨1600863, by rfl⟩ : syracuseStep 4268969 = 3201727) B3201727
theorem B3040255 : Blo 1264450 3040255 := bstep (se 1 (by rfl) ⟨2280191, by rfl⟩ : syracuseStep 3040255 = 4560383) B4560383
theorem B4801619 : Blo 1264450 4801619 := bstep (se 1 (by rfl) ⟨3601214, by rfl⟩ : syracuseStep 4801619 = 7202429) B7202429
theorem B4269239 : Blo 1264450 4269239 := bstep (se 1 (by rfl) ⟨3201929, by rfl⟩ : syracuseStep 4269239 = 6403859) B6403859
theorem B15812147 : Blo 1264450 15812147 := bstep (se 1 (by rfl) ⟨11859110, by rfl⟩ : syracuseStep 15812147 = 23718221) B23718221
theorem B4802287 : Blo 1264450 4802287 := bstep (se 1 (by rfl) ⟨3601715, by rfl⟩ : syracuseStep 4802287 = 7203431) B7203431
theorem B4269833 : Blo 1264450 4269833 := bstep (se 2 (by rfl) ⟨1601187, by rfl⟩ : syracuseStep 4269833 = 3202375) B3202375
theorem B3204947 : Blo 1264450 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B7202681 : Blo 1264450 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B3205079 : Blo 1264450 3205079 := bstep (se 1 (by rfl) ⟨2403809, by rfl⟩ : syracuseStep 3205079 = 4807619) B4807619
theorem B4327519 : Blo 1264450 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B8661113 : Blo 1264450 8661113 := bstep (se 2 (by rfl) ⟨3247917, by rfl⟩ : syracuseStep 8661113 = 6495835) B6495835
theorem B2566441 : Blo 1264450 2566441 := bstep (se 2 (by rfl) ⟨962415, by rfl⟩ : syracuseStep 2566441 = 1924831) B1924831
theorem B8112473 : Blo 1264450 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B5409271 : Blo 1264450 5409271 := bstep (se 1 (by rfl) ⟨4056953, by rfl⟩ : syracuseStep 5409271 = 8113907) B8113907
theorem B6409043 : Blo 1264450 6409043 := bstep (se 1 (by rfl) ⟨4806782, by rfl⟩ : syracuseStep 6409043 = 9613565) B9613565
theorem B1264551 : Blo 1264450 1264551 := bstep (se 1 (by rfl) ⟨948413, by rfl⟩ : syracuseStep 1264551 = 1896827) B1896827
theorem B2403263 : Blo 1264450 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B3247055 : Blo 1264450 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B7695431 : Blo 1264450 7695431 := bstep (se 1 (by rfl) ⟨5771573, by rfl⟩ : syracuseStep 7695431 = 11543147) B11543147
theorem B2313289 : Blo 1264450 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B1264731 : Blo 1264450 1264731 := bstep (se 1 (by rfl) ⟨948548, by rfl⟩ : syracuseStep 1264731 = 1897097) B1897097
theorem B7212179 : Blo 1264450 7212179 := bstep (se 1 (by rfl) ⟨5409134, by rfl⟩ : syracuseStep 7212179 = 10818269) B10818269
theorem B2845907 : Blo 1264450 2845907 := bstep (se 1 (by rfl) ⟨2134430, by rfl⟩ : syracuseStep 2845907 = 4268861) B4268861
theorem B1264871 : Blo 1264450 1264871 := bstep (se 1 (by rfl) ⟨948653, by rfl⟩ : syracuseStep 1264871 = 1897307) B1897307
theorem B20524265 : Blo 1264450 20524265 := bstep (se 2 (by rfl) ⟨7696599, by rfl⟩ : syracuseStep 20524265 = 15393199) B15393199
theorem B1264891 : Blo 1264450 1264891 := bstep (se 1 (by rfl) ⟨948668, by rfl⟩ : syracuseStep 1264891 = 1897337) B1897337
theorem B7212635 : Blo 1264450 7212635 := bstep (se 1 (by rfl) ⟨5409476, by rfl⟩ : syracuseStep 7212635 = 10818953) B10818953
theorem B1265311 : Blo 1264450 1265311 := bstep (se 1 (by rfl) ⟨948983, by rfl⟩ : syracuseStep 1265311 = 1897967) B1897967
theorem B2846375 : Blo 1264450 2846375 := bstep (se 1 (by rfl) ⟨2134781, by rfl⟩ : syracuseStep 2846375 = 4269563) B4269563
theorem B1265391 : Blo 1264450 1265391 := bstep (se 1 (by rfl) ⟨949043, by rfl⟩ : syracuseStep 1265391 = 1898087) B1898087
theorem B9744239 : Blo 1264450 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B2846699 : Blo 1264450 2846699 := bstep (se 1 (by rfl) ⟨2135024, by rfl⟩ : syracuseStep 2846699 = 4270049) B4270049
theorem B1265695 : Blo 1264450 1265695 := bstep (se 1 (by rfl) ⟨949271, by rfl⟩ : syracuseStep 1265695 = 1898543) B1898543
theorem B1265775 : Blo 1264450 1265775 := bstep (se 1 (by rfl) ⟨949331, by rfl⟩ : syracuseStep 1265775 = 1898663) B1898663
theorem B9605303 : Blo 1264450 9605303 := bstep (se 1 (by rfl) ⟨7203977, by rfl⟩ : syracuseStep 9605303 = 14407955) B14407955
theorem B7205071 : Blo 1264450 7205071 := bstep (se 1 (by rfl) ⟨5403803, by rfl⟩ : syracuseStep 7205071 = 10807607) B10807607
theorem B1265871 : Blo 1264450 1265871 := bstep (se 1 (by rfl) ⟨949403, by rfl⟩ : syracuseStep 1265871 = 1898807) B1898807
theorem B1265991 : Blo 1264450 1265991 := bstep (se 1 (by rfl) ⟨949493, by rfl⟩ : syracuseStep 1265991 = 1898987) B1898987
theorem B6836767 : Blo 1264450 6836767 := bstep (se 1 (by rfl) ⟨5127575, by rfl⟩ : syracuseStep 6836767 = 10255151) B10255151
theorem B2134559 : Blo 1264450 2134559 := bstep (se 1 (by rfl) ⟨1600919, by rfl⟩ : syracuseStep 2134559 = 3201839) B3201839
theorem B1266223 : Blo 1264450 1266223 := bstep (se 1 (by rfl) ⟨949667, by rfl⟩ : syracuseStep 1266223 = 1899335) B1899335
theorem B1897127 : Blo 1264450 1897127 := bstep (se 1 (by rfl) ⟨1422845, by rfl⟩ : syracuseStep 1897127 = 2845691) B2845691
theorem B2847401 : Blo 1264450 2847401 := bstep (se 2 (by rfl) ⟨1067775, by rfl⟩ : syracuseStep 2847401 = 2135551) B2135551
theorem B14619311 : Blo 1264450 14619311 := bstep (se 1 (by rfl) ⟨10964483, by rfl⟩ : syracuseStep 14619311 = 21928967) B21928967
theorem B1897247 : Blo 1264450 1897247 := bstep (se 1 (by rfl) ⟨1422935, by rfl⟩ : syracuseStep 1897247 = 2845871) B2845871
theorem B2847545 : Blo 1264450 2847545 := bstep (se 2 (by rfl) ⟨1067829, by rfl⟩ : syracuseStep 2847545 = 2135659) B2135659
theorem B2134991 : Blo 1264450 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B2847905 : Blo 1264450 2847905 := bstep (se 2 (by rfl) ⟨1067964, by rfl⟩ : syracuseStep 2847905 = 2135929) B2135929
theorem B1897727 : Blo 1264450 1897727 := bstep (se 1 (by rfl) ⟨1423295, by rfl⟩ : syracuseStep 1897727 = 2846591) B2846591
theorem B2135423 : Blo 1264450 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B4806175 : Blo 1264450 4806175 := bstep (se 1 (by rfl) ⟨3604631, by rfl⟩ : syracuseStep 4806175 = 7209263) B7209263
theorem B4273775 : Blo 1264450 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B4560731 : Blo 1264450 4560731 := bstep (se 1 (by rfl) ⟨3420548, by rfl⟩ : syracuseStep 4560731 = 6841097) B6841097
theorem B4872059 : Blo 1264450 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B1898399 : Blo 1264450 1898399 := bstep (se 1 (by rfl) ⟨1423799, by rfl⟩ : syracuseStep 1898399 = 2847599) B2847599
theorem B2701279 : Blo 1264450 2701279 := bstep (se 1 (by rfl) ⟨2025959, by rfl⟩ : syracuseStep 2701279 = 4051919) B4051919
theorem B16259077 : Blo 1264450 16259077 := bstep (se 4 (by rfl) ⟨1524288, by rfl⟩ : syracuseStep 16259077 = 3048577) B3048577
theorem B73980317 : Blo 1264450 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B9124285 : Blo 1264450 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B13875875 : Blo 1264450 13875875 := bstep (se 1 (by rfl) ⟨10406906, by rfl⟩ : syracuseStep 13875875 = 20813813) B20813813
theorem B2136827 : Blo 1264450 2136827 := bstep (se 1 (by rfl) ⟨1602620, by rfl⟩ : syracuseStep 2136827 = 3205241) B3205241
theorem B3652361 : Blo 1264450 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B10951463 : Blo 1264450 10951463 := bstep (se 1 (by rfl) ⟨8213597, by rfl⟩ : syracuseStep 10951463 = 16427195) B16427195
theorem B3603311 : Blo 1264450 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B1899515 : Blo 1264450 1899515 := bstep (se 1 (by rfl) ⟨1424636, by rfl⟩ : syracuseStep 1899515 = 2849273) B2849273
theorem B1899575 : Blo 1264450 1899575 := bstep (se 1 (by rfl) ⟨1424681, by rfl⟩ : syracuseStep 1899575 = 2849363) B2849363
theorem B4808105 : Blo 1264450 4808105 := bstep (se 2 (by rfl) ⟨1803039, by rfl⟩ : syracuseStep 4808105 = 3606079) B3606079
theorem B27344303 : Blo 1264450 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B41041363 : Blo 1264450 41041363 := bstep (se 1 (by rfl) ⟨30781022, by rfl⟩ : syracuseStep 41041363 = 61562045) B61562045
theorem B10255997 : Blo 1264450 10255997 := bstep (se 3 (by rfl) ⟨1922999, by rfl⟩ : syracuseStep 10255997 = 3845999) B3845999
theorem B10804873 : Blo 1264450 10804873 := bstep (se 2 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 10804873 = 8103655) B8103655
theorem B4267673 : Blo 1264450 4267673 := bstep (se 2 (by rfl) ⟨1600377, by rfl⟩ : syracuseStep 4267673 = 3200755) B3200755
theorem B4267943 : Blo 1264450 4267943 := bstep (se 1 (by rfl) ⟨3200957, by rfl⟩ : syracuseStep 4267943 = 6401915) B6401915
theorem B5406659 : Blo 1264450 5406659 := bstep (se 1 (by rfl) ⟨4054994, by rfl⟩ : syracuseStep 5406659 = 8109989) B8109989
theorem B9609191 : Blo 1264450 9609191 := bstep (se 1 (by rfl) ⟨7206893, by rfl⟩ : syracuseStep 9609191 = 14413787) B14413787
theorem B36462757 : Blo 1264450 36462757 := bstep (se 4 (by rfl) ⟨3418383, by rfl⟩ : syracuseStep 36462757 = 6836767) B6836767
theorem B12337541 : Blo 1264450 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B12165713 : Blo 1264450 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B3040487 : Blo 1264450 3040487 := bstep (se 1 (by rfl) ⟨2280365, by rfl⟩ : syracuseStep 3040487 = 4560731) B4560731
theorem B4801787 : Blo 1264450 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B5408315 : Blo 1264450 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B9250583 : Blo 1264450 9250583 := bstep (se 1 (by rfl) ⟨6937937, by rfl⟩ : syracuseStep 9250583 = 13875875) B13875875
theorem B2434907 : Blo 1264450 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B2402207 : Blo 1264450 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B2164703 : Blo 1264450 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B6408233 : Blo 1264450 6408233 := bstep (se 2 (by rfl) ⟨2403087, by rfl⟩ : syracuseStep 6408233 = 4806175) B4806175
theorem B5130287 : Blo 1264450 5130287 := bstep (se 1 (by rfl) ⟨3847715, by rfl⟩ : syracuseStep 5130287 = 7695431) B7695431
theorem B13682843 : Blo 1264450 13682843 := bstep (se 1 (by rfl) ⟨10262132, by rfl⟩ : syracuseStep 13682843 = 20524265) B20524265
theorem B3205403 : Blo 1264450 3205403 := bstep (se 1 (by rfl) ⟨2404052, by rfl⟩ : syracuseStep 3205403 = 4808105) B4808105
theorem B18229535 : Blo 1264450 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B2845115 : Blo 1264450 2845115 := bstep (se 1 (by rfl) ⟨2133836, by rfl⟩ : syracuseStep 2845115 = 4267673) B4267673
theorem B2845295 : Blo 1264450 2845295 := bstep (se 1 (by rfl) ⟨2133971, by rfl⟩ : syracuseStep 2845295 = 4267943) B4267943
theorem B21678769 : Blo 1264450 21678769 := bstep (se 2 (by rfl) ⟨8129538, by rfl⟩ : syracuseStep 21678769 = 16259077) B16259077
theorem B5770025 : Blo 1264450 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B1600327 : Blo 1264450 1600327 := bstep (se 1 (by rfl) ⟨1200245, by rfl⟩ : syracuseStep 1600327 = 2400491) B2400491
theorem B2435999 : Blo 1264450 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B1264751 : Blo 1264450 1264751 := bstep (se 1 (by rfl) ⟨948563, by rfl⟩ : syracuseStep 1264751 = 1897127) B1897127
theorem B8105143 : Blo 1264450 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B4271291 : Blo 1264450 4271291 := bstep (se 1 (by rfl) ⟨3203468, by rfl⟩ : syracuseStep 4271291 = 6406937) B6406937
theorem B1264831 : Blo 1264450 1264831 := bstep (se 1 (by rfl) ⟨948623, by rfl⟩ : syracuseStep 1264831 = 1897247) B1897247
theorem B2845979 : Blo 1264450 2845979 := bstep (se 1 (by rfl) ⟨2134484, by rfl⟩ : syracuseStep 2845979 = 4268969) B4268969
theorem B7212361 : Blo 1264450 7212361 := bstep (se 2 (by rfl) ⟨2704635, by rfl⟩ : syracuseStep 7212361 = 5409271) B5409271
theorem B2846159 : Blo 1264450 2846159 := bstep (se 1 (by rfl) ⟨2134619, by rfl⟩ : syracuseStep 2846159 = 4269239) B4269239
theorem B1265151 : Blo 1264450 1265151 := bstep (se 1 (by rfl) ⟨948863, by rfl⟩ : syracuseStep 1265151 = 1897727) B1897727
theorem B2846555 : Blo 1264450 2846555 := bstep (se 1 (by rfl) ⟨2134916, by rfl⟩ : syracuseStep 2846555 = 4269833) B4269833
theorem B3248039 : Blo 1264450 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B1265599 : Blo 1264450 1265599 := bstep (se 1 (by rfl) ⟨949199, by rfl⟩ : syracuseStep 1265599 = 1898399) B1898399
theorem B49320211 : Blo 1264450 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B27349325 : Blo 1264450 27349325 := bstep (se 3 (by rfl) ⟨5127998, by rfl⟩ : syracuseStep 27349325 = 10255997) B10255997
theorem B4272695 : Blo 1264450 4272695 := bstep (se 1 (by rfl) ⟨3204521, by rfl⟩ : syracuseStep 4272695 = 6409043) B6409043
theorem B1602175 : Blo 1264450 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B1266343 : Blo 1264450 1266343 := bstep (se 1 (by rfl) ⟨949757, by rfl⟩ : syracuseStep 1266343 = 1899515) B1899515
theorem B1266383 : Blo 1264450 1266383 := bstep (se 1 (by rfl) ⟨949787, by rfl⟩ : syracuseStep 1266383 = 1899575) B1899575
theorem B1897271 : Blo 1264450 1897271 := bstep (se 1 (by rfl) ⟨1422953, by rfl⟩ : syracuseStep 1897271 = 2845907) B2845907
theorem B14406497 : Blo 1264450 14406497 := bstep (se 2 (by rfl) ⟨5402436, by rfl⟩ : syracuseStep 14406497 = 10804873) B10804873
theorem B6403049 : Blo 1264450 6403049 := bstep (se 2 (by rfl) ⟨2401143, by rfl⟩ : syracuseStep 6403049 = 4802287) B4802287
theorem B1897583 : Blo 1264450 1897583 := bstep (se 1 (by rfl) ⟨1423187, by rfl⟩ : syracuseStep 1897583 = 2846375) B2846375
theorem B3601705 : Blo 1264450 3601705 := bstep (se 2 (by rfl) ⟨1350639, by rfl⟩ : syracuseStep 3601705 = 2701279) B2701279
theorem B1897799 : Blo 1264450 1897799 := bstep (se 1 (by rfl) ⟨1423349, by rfl⟩ : syracuseStep 1897799 = 2846699) B2846699
theorem B4052393 : Blo 1264450 4052393 := bstep (se 2 (by rfl) ⟨1519647, by rfl⟩ : syracuseStep 4052393 = 3039295) B3039295
theorem B6403535 : Blo 1264450 6403535 := bstep (se 1 (by rfl) ⟨4802651, by rfl⟩ : syracuseStep 6403535 = 9605303) B9605303
theorem B9606761 : Blo 1264450 9606761 := bstep (se 2 (by rfl) ⟨3602535, by rfl⟩ : syracuseStep 9606761 = 7205071) B7205071
theorem B1423039 : Blo 1264450 1423039 := bstep (se 1 (by rfl) ⟨1067279, by rfl⟩ : syracuseStep 1423039 = 2134559) B2134559
theorem B3200735 : Blo 1264450 3200735 := bstep (se 1 (by rfl) ⟨2400551, by rfl⟩ : syracuseStep 3200735 = 4801103) B4801103
theorem B3421921 : Blo 1264450 3421921 := bstep (se 2 (by rfl) ⟨1283220, by rfl⟩ : syracuseStep 3421921 = 2566441) B2566441
theorem B1898267 : Blo 1264450 1898267 := bstep (se 1 (by rfl) ⟨1423700, by rfl⟩ : syracuseStep 1898267 = 2847401) B2847401
theorem B9746207 : Blo 1264450 9746207 := bstep (se 1 (by rfl) ⟨7309655, by rfl⟩ : syracuseStep 9746207 = 14619311) B14619311
theorem B1898363 : Blo 1264450 1898363 := bstep (se 1 (by rfl) ⟨1423772, by rfl⟩ : syracuseStep 1898363 = 2847545) B2847545
theorem B1423327 : Blo 1264450 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B3201079 : Blo 1264450 3201079 := bstep (se 1 (by rfl) ⟨2400809, by rfl⟩ : syracuseStep 3201079 = 4801619) B4801619
theorem B1898603 : Blo 1264450 1898603 := bstep (se 1 (by rfl) ⟨1423952, by rfl⟩ : syracuseStep 1898603 = 2847905) B2847905
theorem B1423615 : Blo 1264450 1423615 := bstep (se 1 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 1423615 = 2135423) B2135423
theorem B10541431 : Blo 1264450 10541431 := bstep (se 1 (by rfl) ⟨7906073, by rfl⟩ : syracuseStep 10541431 = 15812147) B15812147
theorem B2849183 : Blo 1264450 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B2136631 : Blo 1264450 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B2136719 : Blo 1264450 2136719 := bstep (se 1 (by rfl) ⟨1602539, by rfl⟩ : syracuseStep 2136719 = 3205079) B3205079
theorem B4053673 : Blo 1264450 4053673 := bstep (se 2 (by rfl) ⟨1520127, by rfl⟩ : syracuseStep 4053673 = 3040255) B3040255
theorem B5774075 : Blo 1264450 5774075 := bstep (se 1 (by rfl) ⟨4330556, by rfl⟩ : syracuseStep 5774075 = 8661113) B8661113
theorem B1424551 : Blo 1264450 1424551 := bstep (se 1 (by rfl) ⟨1068413, by rfl⟩ : syracuseStep 1424551 = 2136827) B2136827
theorem B54721817 : Blo 1264450 54721817 := bstep (se 2 (by rfl) ⟨20520681, by rfl⟩ : syracuseStep 54721817 = 41041363) B41041363
theorem B4808119 : Blo 1264450 4808119 := bstep (se 1 (by rfl) ⟨3606089, by rfl⟩ : syracuseStep 4808119 = 7212179) B7212179
theorem B29203901 : Blo 1264450 29203901 := bstep (se 3 (by rfl) ⟨5475731, by rfl⟩ : syracuseStep 29203901 = 10951463) B10951463
theorem B25984637 : Blo 1264450 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B4808423 : Blo 1264450 4808423 := bstep (se 1 (by rfl) ⟨3606317, by rfl⟩ : syracuseStep 4808423 = 7212635) B7212635
theorem B3604439 : Blo 1264450 3604439 := bstep (se 1 (by rfl) ⟨2703329, by rfl⟩ : syracuseStep 3604439 = 5406659) B5406659
theorem B6406127 : Blo 1264450 6406127 := bstep (se 1 (by rfl) ⟨4804595, by rfl⟩ : syracuseStep 6406127 = 9609191) B9609191
theorem B4268105 : Blo 1264450 4268105 := bstep (se 2 (by rfl) ⟨1600539, by rfl⟩ : syracuseStep 4268105 = 3201079) B3201079
theorem B8225027 : Blo 1264450 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B8110475 : Blo 1264450 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B4268699 : Blo 1264450 4268699 := bstep (se 1 (by rfl) ⟨3201524, by rfl⟩ : syracuseStep 4268699 = 6403049) B6403049
theorem B4269023 : Blo 1264450 4269023 := bstep (se 1 (by rfl) ⟨3201767, by rfl⟩ : syracuseStep 4269023 = 6403535) B6403535
theorem B3605543 : Blo 1264450 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B6497471 : Blo 1264450 6497471 := bstep (se 1 (by rfl) ⟨4873103, by rfl⟩ : syracuseStep 6497471 = 9746207) B9746207
theorem B10806857 : Blo 1264450 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B4802273 : Blo 1264450 4802273 := bstep (se 2 (by rfl) ⟨1800852, by rfl⟩ : syracuseStep 4802273 = 3601705) B3601705
theorem B24668221 : Blo 1264450 24668221 := bstep (se 3 (by rfl) ⟨4625291, by rfl⟩ : syracuseStep 24668221 = 9250583) B9250583
theorem B36481211 : Blo 1264450 36481211 := bstep (se 1 (by rfl) ⟨27360908, by rfl⟩ : syracuseStep 36481211 = 54721817) B54721817
theorem B8661437 : Blo 1264450 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B3205615 : Blo 1264450 3205615 := bstep (se 1 (by rfl) ⟨2404211, by rfl⟩ : syracuseStep 3205615 = 4808423) B4808423
theorem B2402959 : Blo 1264450 2402959 := bstep (se 1 (by rfl) ⟨1802219, by rfl⟩ : syracuseStep 2402959 = 3604439) B3604439
theorem B4270751 : Blo 1264450 4270751 := bstep (se 1 (by rfl) ⟨3203063, by rfl⟩ : syracuseStep 4270751 = 6406127) B6406127
theorem B65760281 : Blo 1264450 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B1264847 : Blo 1264450 1264847 := bstep (se 1 (by rfl) ⟨948635, by rfl⟩ : syracuseStep 1264847 = 1897271) B1897271
theorem B9604331 : Blo 1264450 9604331 := bstep (se 1 (by rfl) ⟨7203248, by rfl⟩ : syracuseStep 9604331 = 14406497) B14406497
theorem B1265055 : Blo 1264450 1265055 := bstep (se 1 (by rfl) ⟨948791, by rfl⟩ : syracuseStep 1265055 = 1897583) B1897583
theorem B2026991 : Blo 1264450 2026991 := bstep (se 1 (by rfl) ⟨1520243, by rfl⟩ : syracuseStep 2026991 = 3040487) B3040487
theorem B1265199 : Blo 1264450 1265199 := bstep (se 1 (by rfl) ⟨948899, by rfl⟩ : syracuseStep 1265199 = 1897799) B1897799
theorem B28905025 : Blo 1264450 28905025 := bstep (se 2 (by rfl) ⟨10839384, by rfl⟩ : syracuseStep 28905025 = 21678769) B21678769
theorem B2133769 : Blo 1264450 2133769 := bstep (se 2 (by rfl) ⟨800163, by rfl⟩ : syracuseStep 2133769 = 1600327) B1600327
theorem B2133823 : Blo 1264450 2133823 := bstep (se 1 (by rfl) ⟨1600367, by rfl⟩ : syracuseStep 2133823 = 3200735) B3200735
theorem B1265511 : Blo 1264450 1265511 := bstep (se 1 (by rfl) ⟨949133, by rfl⟩ : syracuseStep 1265511 = 1898267) B1898267
theorem B1265575 : Blo 1264450 1265575 := bstep (se 1 (by rfl) ⟨949181, by rfl⟩ : syracuseStep 1265575 = 1898363) B1898363
theorem B1601471 : Blo 1264450 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B4272155 : Blo 1264450 4272155 := bstep (se 1 (by rfl) ⟨3204116, by rfl⟩ : syracuseStep 4272155 = 6408233) B6408233
theorem B3420191 : Blo 1264450 3420191 := bstep (se 1 (by rfl) ⟨2565143, by rfl⟩ : syracuseStep 3420191 = 5130287) B5130287
theorem B1265735 : Blo 1264450 1265735 := bstep (se 1 (by rfl) ⟨949301, by rfl⟩ : syracuseStep 1265735 = 1898603) B1898603
theorem B9121895 : Blo 1264450 9121895 := bstep (se 1 (by rfl) ⟨6841421, by rfl⟩ : syracuseStep 9121895 = 13682843) B13682843
theorem B12153023 : Blo 1264450 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B1896743 : Blo 1264450 1896743 := bstep (se 1 (by rfl) ⟨1422557, by rfl⟩ : syracuseStep 1896743 = 2845115) B2845115
theorem B1896863 : Blo 1264450 1896863 := bstep (se 1 (by rfl) ⟨1422647, by rfl⟩ : syracuseStep 1896863 = 2845295) B2845295
theorem B3846683 : Blo 1264450 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B6410825 : Blo 1264450 6410825 := bstep (se 2 (by rfl) ⟨2404059, by rfl⟩ : syracuseStep 6410825 = 4808119) B4808119
theorem B2847527 : Blo 1264450 2847527 := bstep (se 1 (by rfl) ⟨2135645, by rfl⟩ : syracuseStep 2847527 = 4271291) B4271291
theorem B1897319 : Blo 1264450 1897319 := bstep (se 1 (by rfl) ⟨1422989, by rfl⟩ : syracuseStep 1897319 = 2845979) B2845979
theorem B6493085 : Blo 1264450 6493085 := bstep (se 3 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 6493085 = 2434907) B2434907
theorem B1897385 : Blo 1264450 1897385 := bstep (se 2 (by rfl) ⟨711519, by rfl⟩ : syracuseStep 1897385 = 1423039) B1423039
theorem B19469267 : Blo 1264450 19469267 := bstep (se 1 (by rfl) ⟨14601950, by rfl⟩ : syracuseStep 19469267 = 29203901) B29203901
theorem B1897439 : Blo 1264450 1897439 := bstep (se 1 (by rfl) ⟨1423079, by rfl⟩ : syracuseStep 1897439 = 2846159) B2846159
theorem B17323091 : Blo 1264450 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B1897703 : Blo 1264450 1897703 := bstep (se 1 (by rfl) ⟨1423277, by rfl⟩ : syracuseStep 1897703 = 2846555) B2846555
theorem B5772541 : Blo 1264450 5772541 := bstep (se 3 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 5772541 = 2164703) B2164703
theorem B1897769 : Blo 1264450 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B48617009 : Blo 1264450 48617009 := bstep (se 2 (by rfl) ⟨18231378, by rfl⟩ : syracuseStep 48617009 = 36462757) B36462757
theorem B18232883 : Blo 1264450 18232883 := bstep (se 1 (by rfl) ⟨13674662, by rfl⟩ : syracuseStep 18232883 = 27349325) B27349325
theorem B1898153 : Blo 1264450 1898153 := bstep (se 2 (by rfl) ⟨711807, by rfl⟩ : syracuseStep 1898153 = 1423615) B1423615
theorem B2848463 : Blo 1264450 2848463 := bstep (se 1 (by rfl) ⟨2136347, by rfl⟩ : syracuseStep 2848463 = 4272695) B4272695
theorem B14055241 : Blo 1264450 14055241 := bstep (se 2 (by rfl) ⟨5270715, by rfl⟩ : syracuseStep 14055241 = 10541431) B10541431
theorem B2848841 : Blo 1264450 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B3201191 : Blo 1264450 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B2136233 : Blo 1264450 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B5404897 : Blo 1264450 5404897 := bstep (se 2 (by rfl) ⟨2026836, by rfl⟩ : syracuseStep 5404897 = 4053673) B4053673
theorem B2701595 : Blo 1264450 2701595 := bstep (se 1 (by rfl) ⟨2026196, by rfl⟩ : syracuseStep 2701595 = 4052393) B4052393
theorem B6404507 : Blo 1264450 6404507 := bstep (se 1 (by rfl) ⟨4803380, by rfl⟩ : syracuseStep 6404507 = 9606761) B9606761
theorem B2136935 : Blo 1264450 2136935 := bstep (se 1 (by rfl) ⟨1602701, by rfl⟩ : syracuseStep 2136935 = 3205403) B3205403
theorem B1899401 : Blo 1264450 1899401 := bstep (se 2 (by rfl) ⟨712275, by rfl⟩ : syracuseStep 1899401 = 1424551) B1424551
theorem B1899455 : Blo 1264450 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B25983989 : Blo 1264450 25983989 := bstep (se 5 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 25983989 = 2435999) B2435999
theorem B1424479 : Blo 1264450 1424479 := bstep (se 1 (by rfl) ⟨1068359, by rfl⟩ : syracuseStep 1424479 = 2136719) B2136719
theorem B9616481 : Blo 1264450 9616481 := bstep (se 2 (by rfl) ⟨3606180, by rfl⟩ : syracuseStep 9616481 = 7212361) B7212361
theorem B3849383 : Blo 1264450 3849383 := bstep (se 1 (by rfl) ⟨2887037, by rfl⟩ : syracuseStep 3849383 = 5774075) B5774075
theorem B4562561 : Blo 1264450 4562561 := bstep (se 2 (by rfl) ⟨1710960, by rfl⟩ : syracuseStep 4562561 = 3421921) B3421921
theorem B32890961 : Blo 1264450 32890961 := bstep (se 2 (by rfl) ⟨12334110, by rfl⟩ : syracuseStep 32890961 = 24668221) B24668221
theorem B8102015 : Blo 1264450 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B5406983 : Blo 1264450 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B2564455 : Blo 1264450 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B3203945 : Blo 1264450 3203945 := bstep (se 2 (by rfl) ⟨1201479, by rfl⟩ : syracuseStep 3203945 = 2402959) B2402959
theorem B4269671 : Blo 1264450 4269671 := bstep (se 1 (by rfl) ⟨3202253, by rfl⟩ : syracuseStep 4269671 = 6404507) B6404507
theorem B2566255 : Blo 1264450 2566255 := bstep (se 1 (by rfl) ⟨1924691, by rfl⟩ : syracuseStep 2566255 = 3849383) B3849383
theorem B2845025 : Blo 1264450 2845025 := bstep (se 2 (by rfl) ⟨1066884, by rfl⟩ : syracuseStep 2845025 = 2133769) B2133769
theorem B2845097 : Blo 1264450 2845097 := bstep (se 2 (by rfl) ⟨1066911, by rfl⟩ : syracuseStep 2845097 = 2133823) B2133823
theorem B3041707 : Blo 1264450 3041707 := bstep (se 1 (by rfl) ⟨2281280, by rfl⟩ : syracuseStep 3041707 = 4562561) B4562561
theorem B4270589 : Blo 1264450 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B2845403 : Blo 1264450 2845403 := bstep (se 1 (by rfl) ⟨2134052, by rfl⟩ : syracuseStep 2845403 = 4268105) B4268105
theorem B6081263 : Blo 1264450 6081263 := bstep (se 1 (by rfl) ⟨4560947, by rfl⟩ : syracuseStep 6081263 = 9121895) B9121895
theorem B9120509 : Blo 1264450 9120509 := bstep (se 3 (by rfl) ⟨1710095, by rfl⟩ : syracuseStep 9120509 = 3420191) B3420191
theorem B5483351 : Blo 1264450 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B1264495 : Blo 1264450 1264495 := bstep (se 1 (by rfl) ⟨948371, by rfl⟩ : syracuseStep 1264495 = 1896743) B1896743
theorem B1264575 : Blo 1264450 1264575 := bstep (se 1 (by rfl) ⟨948431, by rfl⟩ : syracuseStep 1264575 = 1896863) B1896863
theorem B2845799 : Blo 1264450 2845799 := bstep (se 1 (by rfl) ⟨2134349, by rfl⟩ : syracuseStep 2845799 = 4268699) B4268699
theorem B1264879 : Blo 1264450 1264879 := bstep (se 1 (by rfl) ⟨948659, by rfl⟩ : syracuseStep 1264879 = 1897319) B1897319
theorem B4328723 : Blo 1264450 4328723 := bstep (se 1 (by rfl) ⟨3246542, by rfl⟩ : syracuseStep 4328723 = 6493085) B6493085
theorem B1264923 : Blo 1264450 1264923 := bstep (se 1 (by rfl) ⟨948692, by rfl⟩ : syracuseStep 1264923 = 1897385) B1897385
theorem B12979511 : Blo 1264450 12979511 := bstep (se 1 (by rfl) ⟨9734633, by rfl⟩ : syracuseStep 12979511 = 19469267) B19469267
theorem B2846015 : Blo 1264450 2846015 := bstep (se 1 (by rfl) ⟨2134511, by rfl⟩ : syracuseStep 2846015 = 4269023) B4269023
theorem B1264959 : Blo 1264450 1264959 := bstep (se 1 (by rfl) ⟨948719, by rfl⟩ : syracuseStep 1264959 = 1897439) B1897439
theorem B2403695 : Blo 1264450 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B1265135 : Blo 1264450 1265135 := bstep (se 1 (by rfl) ⟨948851, by rfl⟩ : syracuseStep 1265135 = 1897703) B1897703
theorem B1265179 : Blo 1264450 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B32411339 : Blo 1264450 32411339 := bstep (se 1 (by rfl) ⟨24308504, by rfl⟩ : syracuseStep 32411339 = 48617009) B48617009
theorem B7204571 : Blo 1264450 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B1265435 : Blo 1264450 1265435 := bstep (se 1 (by rfl) ⟨949076, by rfl⟩ : syracuseStep 1265435 = 1898153) B1898153
theorem B2134127 : Blo 1264450 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B7696721 : Blo 1264450 7696721 := bstep (se 2 (by rfl) ⟨2886270, by rfl⟩ : syracuseStep 7696721 = 5772541) B5772541
theorem B2847167 : Blo 1264450 2847167 := bstep (se 1 (by rfl) ⟨2135375, by rfl⟩ : syracuseStep 2847167 = 4270751) B4270751
theorem B1266267 : Blo 1264450 1266267 := bstep (se 1 (by rfl) ⟨949700, by rfl⟩ : syracuseStep 1266267 = 1899401) B1899401
theorem B1266303 : Blo 1264450 1266303 := bstep (se 1 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 1266303 = 1899455) B1899455
theorem B17322659 : Blo 1264450 17322659 := bstep (se 1 (by rfl) ⟨12991994, by rfl⟩ : syracuseStep 17322659 = 25983989) B25983989
theorem B43840187 : Blo 1264450 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B6410987 : Blo 1264450 6410987 := bstep (se 1 (by rfl) ⟨4808240, by rfl⟩ : syracuseStep 6410987 = 9616481) B9616481
theorem B38540033 : Blo 1264450 38540033 := bstep (se 2 (by rfl) ⟨14452512, by rfl⟩ : syracuseStep 38540033 = 28905025) B28905025
theorem B6402887 : Blo 1264450 6402887 := bstep (se 1 (by rfl) ⟨4802165, by rfl⟩ : syracuseStep 6402887 = 9604331) B9604331
theorem B18740321 : Blo 1264450 18740321 := bstep (se 2 (by rfl) ⟨7027620, by rfl⟩ : syracuseStep 18740321 = 14055241) B14055241
theorem B2848103 : Blo 1264450 2848103 := bstep (se 1 (by rfl) ⟨2136077, by rfl⟩ : syracuseStep 2848103 = 4272155) B4272155
theorem B7206529 : Blo 1264450 7206529 := bstep (se 2 (by rfl) ⟨2702448, by rfl⟩ : syracuseStep 7206529 = 5404897) B5404897
theorem B4273883 : Blo 1264450 4273883 := bstep (se 1 (by rfl) ⟨3205412, by rfl⟩ : syracuseStep 4273883 = 6410825) B6410825
theorem B1898351 : Blo 1264450 1898351 := bstep (se 1 (by rfl) ⟨1423763, by rfl⟩ : syracuseStep 1898351 = 2847527) B2847527
theorem B4274153 : Blo 1264450 4274153 := bstep (se 2 (by rfl) ⟨1602807, by rfl⟩ : syracuseStep 4274153 = 3205615) B3205615
theorem B11548727 : Blo 1264450 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B4331647 : Blo 1264450 4331647 := bstep (se 1 (by rfl) ⟨3248735, by rfl⟩ : syracuseStep 4331647 = 6497471) B6497471
theorem B12155255 : Blo 1264450 12155255 := bstep (se 1 (by rfl) ⟨9116441, by rfl⟩ : syracuseStep 12155255 = 18232883) B18232883
theorem B1898975 : Blo 1264450 1898975 := bstep (se 1 (by rfl) ⟨1424231, by rfl⟩ : syracuseStep 1898975 = 2848463) B2848463
theorem B3201515 : Blo 1264450 3201515 := bstep (se 1 (by rfl) ⟨2401136, by rfl⟩ : syracuseStep 3201515 = 4802273) B4802273
theorem B1899227 : Blo 1264450 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B1424155 : Blo 1264450 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B24320807 : Blo 1264450 24320807 := bstep (se 1 (by rfl) ⟨18240605, by rfl⟩ : syracuseStep 24320807 = 36481211) B36481211
theorem B1899305 : Blo 1264450 1899305 := bstep (se 2 (by rfl) ⟨712239, by rfl⟩ : syracuseStep 1899305 = 1424479) B1424479
theorem B1801063 : Blo 1264450 1801063 := bstep (se 1 (by rfl) ⟨1350797, by rfl⟩ : syracuseStep 1801063 = 2701595) B2701595
theorem B5774291 : Blo 1264450 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B1424623 : Blo 1264450 1424623 := bstep (se 1 (by rfl) ⟨1068467, by rfl⟩ : syracuseStep 1424623 = 2136935) B2136935
theorem B1351327 : Blo 1264450 1351327 := bstep (se 1 (by rfl) ⟨1013495, by rfl⟩ : syracuseStep 1351327 = 2026991) B2026991
theorem B3604655 : Blo 1264450 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B4268591 : Blo 1264450 4268591 := bstep (se 1 (by rfl) ⟨3201443, by rfl⟩ : syracuseStep 4268591 = 6402887) B6402887
theorem B4055609 : Blo 1264450 4055609 := bstep (se 2 (by rfl) ⟨1520853, by rfl⟩ : syracuseStep 4055609 = 3041707) B3041707
theorem B23102117 : Blo 1264450 23102117 := bstep (se 4 (by rfl) ⟨2165823, by rfl⟩ : syracuseStep 23102117 = 4331647) B4331647
theorem B12493547 : Blo 1264450 12493547 := bstep (se 1 (by rfl) ⟨9370160, by rfl⟩ : syracuseStep 12493547 = 18740321) B18740321
theorem B2401417 : Blo 1264450 2401417 := bstep (se 2 (by rfl) ⟨900531, by rfl⟩ : syracuseStep 2401417 = 1801063) B1801063
theorem B8103503 : Blo 1264450 8103503 := bstep (se 1 (by rfl) ⟨6077627, by rfl⟩ : syracuseStep 8103503 = 12155255) B12155255
theorem B6080339 : Blo 1264450 6080339 := bstep (se 1 (by rfl) ⟨4560254, by rfl⟩ : syracuseStep 6080339 = 9120509) B9120509
theorem B16213871 : Blo 1264450 16213871 := bstep (se 1 (by rfl) ⟨12160403, by rfl⟩ : syracuseStep 16213871 = 24320807) B24320807
theorem B3655567 : Blo 1264450 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B2885815 : Blo 1264450 2885815 := bstep (se 1 (by rfl) ⟨2164361, by rfl⟩ : syracuseStep 2885815 = 4328723) B4328723
theorem B8653007 : Blo 1264450 8653007 := bstep (se 1 (by rfl) ⟨6489755, by rfl⟩ : syracuseStep 8653007 = 12979511) B12979511
theorem B4803047 : Blo 1264450 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B5401343 : Blo 1264450 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B5131147 : Blo 1264450 5131147 := bstep (se 1 (by rfl) ⟨3848360, by rfl⟩ : syracuseStep 5131147 = 7696721) B7696721
theorem B3419273 : Blo 1264450 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B25693355 : Blo 1264450 25693355 := bstep (se 1 (by rfl) ⟨19270016, by rfl⟩ : syracuseStep 25693355 = 38540033) B38540033
theorem B6409853 : Blo 1264450 6409853 := bstep (se 3 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 6409853 = 2403695) B2403695
theorem B2846447 : Blo 1264450 2846447 := bstep (se 1 (by rfl) ⟨2134835, by rfl⟩ : syracuseStep 2846447 = 4269671) B4269671
theorem B1265567 : Blo 1264450 1265567 := bstep (se 1 (by rfl) ⟨949175, by rfl⟩ : syracuseStep 1265567 = 1898351) B1898351
theorem B1896683 : Blo 1264450 1896683 := bstep (se 1 (by rfl) ⟨1422512, by rfl⟩ : syracuseStep 1896683 = 2845025) B2845025
theorem B1896731 : Blo 1264450 1896731 := bstep (se 1 (by rfl) ⟨1422548, by rfl⟩ : syracuseStep 1896731 = 2845097) B2845097
theorem B1265983 : Blo 1264450 1265983 := bstep (se 1 (by rfl) ⟨949487, by rfl⟩ : syracuseStep 1265983 = 1898975) B1898975
theorem B2134343 : Blo 1264450 2134343 := bstep (se 1 (by rfl) ⟨1600757, by rfl⟩ : syracuseStep 2134343 = 3201515) B3201515
theorem B2847059 : Blo 1264450 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B1896935 : Blo 1264450 1896935 := bstep (se 1 (by rfl) ⟨1422701, by rfl⟩ : syracuseStep 1896935 = 2845403) B2845403
theorem B1266151 : Blo 1264450 1266151 := bstep (se 1 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 1266151 = 1899227) B1899227
theorem B1266203 : Blo 1264450 1266203 := bstep (se 1 (by rfl) ⟨949652, by rfl⟩ : syracuseStep 1266203 = 1899305) B1899305
theorem B1897199 : Blo 1264450 1897199 := bstep (se 1 (by rfl) ⟨1422899, by rfl⟩ : syracuseStep 1897199 = 2845799) B2845799
theorem B1897343 : Blo 1264450 1897343 := bstep (se 1 (by rfl) ⟨1423007, by rfl⟩ : syracuseStep 1897343 = 2846015) B2846015
theorem B21607559 : Blo 1264450 21607559 := bstep (se 1 (by rfl) ⟨16205669, by rfl⟩ : syracuseStep 21607559 = 32411339) B32411339
theorem B21927307 : Blo 1264450 21927307 := bstep (se 1 (by rfl) ⟨16445480, by rfl⟩ : syracuseStep 21927307 = 32890961) B32890961
theorem B1422751 : Blo 1264450 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B3421673 : Blo 1264450 3421673 := bstep (se 2 (by rfl) ⟨1283127, by rfl⟩ : syracuseStep 3421673 = 2566255) B2566255
theorem B1898111 : Blo 1264450 1898111 := bstep (se 1 (by rfl) ⟨1423583, by rfl⟩ : syracuseStep 1898111 = 2847167) B2847167
theorem B11548439 : Blo 1264450 11548439 := bstep (se 1 (by rfl) ⟨8661329, by rfl⟩ : syracuseStep 11548439 = 17322659) B17322659
theorem B29226791 : Blo 1264450 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B4273991 : Blo 1264450 4273991 := bstep (se 1 (by rfl) ⟨3205493, by rfl⟩ : syracuseStep 4273991 = 6410987) B6410987
theorem B2135963 : Blo 1264450 2135963 := bstep (se 1 (by rfl) ⟨1601972, by rfl⟩ : syracuseStep 2135963 = 3203945) B3203945
theorem B1898735 : Blo 1264450 1898735 := bstep (se 1 (by rfl) ⟨1424051, by rfl⟩ : syracuseStep 1898735 = 2848103) B2848103
theorem B1898873 : Blo 1264450 1898873 := bstep (se 2 (by rfl) ⟨712077, by rfl⟩ : syracuseStep 1898873 = 1424155) B1424155
theorem B2849255 : Blo 1264450 2849255 := bstep (se 1 (by rfl) ⟨2136941, by rfl⟩ : syracuseStep 2849255 = 4273883) B4273883
theorem B2849435 : Blo 1264450 2849435 := bstep (se 1 (by rfl) ⟨2137076, by rfl⟩ : syracuseStep 2849435 = 4274153) B4274153
theorem B7699151 : Blo 1264450 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B1899497 : Blo 1264450 1899497 := bstep (se 2 (by rfl) ⟨712311, by rfl⟩ : syracuseStep 1899497 = 1424623) B1424623
theorem B4054175 : Blo 1264450 4054175 := bstep (se 1 (by rfl) ⟨3040631, by rfl⟩ : syracuseStep 4054175 = 6081263) B6081263
theorem B3849527 : Blo 1264450 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B9608705 : Blo 1264450 9608705 := bstep (se 2 (by rfl) ⟨3603264, by rfl⟩ : syracuseStep 9608705 = 7206529) B7206529
theorem B1801769 : Blo 1264450 1801769 := bstep (se 2 (by rfl) ⟨675663, by rfl⟩ : syracuseStep 1801769 = 1351327) B1351327
theorem B15401411 : Blo 1264450 15401411 := bstep (se 1 (by rfl) ⟨11551058, by rfl⟩ : syracuseStep 15401411 = 23102117) B23102117
theorem B6841529 : Blo 1264450 6841529 := bstep (se 2 (by rfl) ⟨2565573, by rfl⟩ : syracuseStep 6841529 = 5131147) B5131147
theorem B5768671 : Blo 1264450 5768671 := bstep (se 1 (by rfl) ⟨4326503, by rfl⟩ : syracuseStep 5768671 = 8653007) B8653007
theorem B10814957 : Blo 1264450 10814957 := bstep (se 3 (by rfl) ⟨2027804, by rfl⟩ : syracuseStep 10814957 = 4055609) B4055609
theorem B14403581 : Blo 1264450 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B2279515 : Blo 1264450 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B2566351 : Blo 1264450 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B2403103 : Blo 1264450 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B1264455 : Blo 1264450 1264455 := bstep (se 1 (by rfl) ⟨948341, by rfl⟩ : syracuseStep 1264455 = 1896683) B1896683
theorem B1264487 : Blo 1264450 1264487 := bstep (se 1 (by rfl) ⟨948365, by rfl⟩ : syracuseStep 1264487 = 1896731) B1896731
theorem B1264623 : Blo 1264450 1264623 := bstep (se 1 (by rfl) ⟨948467, by rfl⟩ : syracuseStep 1264623 = 1896935) B1896935
theorem B2845727 : Blo 1264450 2845727 := bstep (se 1 (by rfl) ⟨2134295, by rfl⟩ : syracuseStep 2845727 = 4268591) B4268591
theorem B1264799 : Blo 1264450 1264799 := bstep (se 1 (by rfl) ⟨948599, by rfl⟩ : syracuseStep 1264799 = 1897199) B1897199
theorem B1264895 : Blo 1264450 1264895 := bstep (se 1 (by rfl) ⟨948671, by rfl⟩ : syracuseStep 1264895 = 1897343) B1897343
theorem B14405039 : Blo 1264450 14405039 := bstep (se 1 (by rfl) ⟨10803779, by rfl⟩ : syracuseStep 14405039 = 21607559) B21607559
theorem B2281115 : Blo 1264450 2281115 := bstep (se 1 (by rfl) ⟨1710836, by rfl⟩ : syracuseStep 2281115 = 3421673) B3421673
theorem B5402335 : Blo 1264450 5402335 := bstep (se 1 (by rfl) ⟨4051751, by rfl⟩ : syracuseStep 5402335 = 8103503) B8103503
theorem B1265407 : Blo 1264450 1265407 := bstep (se 1 (by rfl) ⟨949055, by rfl⟩ : syracuseStep 1265407 = 1898111) B1898111
theorem B10809247 : Blo 1264450 10809247 := bstep (se 1 (by rfl) ⟨8106935, by rfl⟩ : syracuseStep 10809247 = 16213871) B16213871
theorem B4804717 : Blo 1264450 4804717 := bstep (se 3 (by rfl) ⟨900884, by rfl⟩ : syracuseStep 4804717 = 1801769) B1801769
theorem B1265823 : Blo 1264450 1265823 := bstep (se 1 (by rfl) ⟨949367, by rfl⟩ : syracuseStep 1265823 = 1898735) B1898735
theorem B1265915 : Blo 1264450 1265915 := bstep (se 1 (by rfl) ⟨949436, by rfl⟩ : syracuseStep 1265915 = 1898873) B1898873
theorem B5132767 : Blo 1264450 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B1897001 : Blo 1264450 1897001 := bstep (se 2 (by rfl) ⟨711375, by rfl⟩ : syracuseStep 1897001 = 1422751) B1422751
theorem B1266331 : Blo 1264450 1266331 := bstep (se 1 (by rfl) ⟨949748, by rfl⟩ : syracuseStep 1266331 = 1899497) B1899497
theorem B4273235 : Blo 1264450 4273235 := bstep (se 1 (by rfl) ⟨3204926, by rfl⟩ : syracuseStep 4273235 = 6409853) B6409853
theorem B1897631 : Blo 1264450 1897631 := bstep (se 1 (by rfl) ⟨1423223, by rfl⟩ : syracuseStep 1897631 = 2846447) B2846447
theorem B1422895 : Blo 1264450 1422895 := bstep (se 1 (by rfl) ⟨1067171, by rfl⟩ : syracuseStep 1422895 = 2134343) B2134343
theorem B1898039 : Blo 1264450 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B3847753 : Blo 1264450 3847753 := bstep (se 2 (by rfl) ⟨1442907, by rfl⟩ : syracuseStep 3847753 = 2885815) B2885815
theorem B8329031 : Blo 1264450 8329031 := bstep (se 1 (by rfl) ⟨6246773, by rfl⟩ : syracuseStep 8329031 = 12493547) B12493547
theorem B7698959 : Blo 1264450 7698959 := bstep (se 1 (by rfl) ⟨5774219, by rfl⟩ : syracuseStep 7698959 = 11548439) B11548439
theorem B2849327 : Blo 1264450 2849327 := bstep (se 1 (by rfl) ⟨2136995, by rfl⟩ : syracuseStep 2849327 = 4273991) B4273991
theorem B4053559 : Blo 1264450 4053559 := bstep (se 1 (by rfl) ⟨3040169, by rfl⟩ : syracuseStep 4053559 = 6080339) B6080339
theorem B1423975 : Blo 1264450 1423975 := bstep (se 1 (by rfl) ⟨1067981, by rfl⟩ : syracuseStep 1423975 = 2135963) B2135963
theorem B3201889 : Blo 1264450 3201889 := bstep (se 2 (by rfl) ⟨1200708, by rfl⟩ : syracuseStep 3201889 = 2401417) B2401417
theorem B3202031 : Blo 1264450 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B1899503 : Blo 1264450 1899503 := bstep (se 1 (by rfl) ⟨1424627, by rfl⟩ : syracuseStep 1899503 = 2849255) B2849255
theorem B1899623 : Blo 1264450 1899623 := bstep (se 1 (by rfl) ⟨1424717, by rfl⟩ : syracuseStep 1899623 = 2849435) B2849435
theorem B29236409 : Blo 1264450 29236409 := bstep (se 2 (by rfl) ⟨10963653, by rfl⟩ : syracuseStep 29236409 = 21927307) B21927307
theorem B77938109 : Blo 1264450 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B2702783 : Blo 1264450 2702783 := bstep (se 1 (by rfl) ⟨2027087, by rfl⟩ : syracuseStep 2702783 = 4054175) B4054175
theorem B17128903 : Blo 1264450 17128903 := bstep (se 1 (by rfl) ⟨12846677, by rfl⟩ : syracuseStep 17128903 = 25693355) B25693355
theorem B6405803 : Blo 1264450 6405803 := bstep (se 1 (by rfl) ⟨4804352, by rfl⟩ : syracuseStep 6405803 = 9608705) B9608705
theorem B4874089 : Blo 1264450 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B3039353 : Blo 1264450 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B6406289 : Blo 1264450 6406289 := bstep (se 2 (by rfl) ⟨2402358, by rfl⟩ : syracuseStep 6406289 = 4804717) B4804717
theorem B7209971 : Blo 1264450 7209971 := bstep (se 1 (by rfl) ⟨5407478, by rfl⟩ : syracuseStep 7209971 = 10814957) B10814957
theorem B3204137 : Blo 1264450 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B4269185 : Blo 1264450 4269185 := bstep (se 2 (by rfl) ⟨1600944, by rfl⟩ : syracuseStep 4269185 = 3201889) B3201889
theorem B9602387 : Blo 1264450 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B5130337 : Blo 1264450 5130337 := bstep (se 2 (by rfl) ⟨1923876, by rfl⟩ : syracuseStep 5130337 = 3847753) B3847753
theorem B19490939 : Blo 1264450 19490939 := bstep (se 1 (by rfl) ⟨14618204, by rfl⟩ : syracuseStep 19490939 = 29236409) B29236409
theorem B9603359 : Blo 1264450 9603359 := bstep (se 1 (by rfl) ⟨7202519, by rfl⟩ : syracuseStep 9603359 = 14405039) B14405039
theorem B7203113 : Blo 1264450 7203113 := bstep (se 2 (by rfl) ⟨2701167, by rfl⟩ : syracuseStep 7203113 = 5402335) B5402335
theorem B4270535 : Blo 1264450 4270535 := bstep (se 1 (by rfl) ⟨3202901, by rfl⟩ : syracuseStep 4270535 = 6405803) B6405803
theorem B6498785 : Blo 1264450 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B14412329 : Blo 1264450 14412329 := bstep (se 2 (by rfl) ⟨5404623, by rfl⟩ : syracuseStep 14412329 = 10809247) B10809247
theorem B10267607 : Blo 1264450 10267607 := bstep (se 1 (by rfl) ⟨7700705, by rfl⟩ : syracuseStep 10267607 = 15401411) B15401411
theorem B1264667 : Blo 1264450 1264667 := bstep (se 1 (by rfl) ⟨948500, by rfl⟩ : syracuseStep 1264667 = 1897001) B1897001
theorem B6843689 : Blo 1264450 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B1265087 : Blo 1264450 1265087 := bstep (se 1 (by rfl) ⟨948815, by rfl⟩ : syracuseStep 1265087 = 1897631) B1897631
theorem B1265359 : Blo 1264450 1265359 := bstep (se 1 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 1265359 = 1898039) B1898039
theorem B5132639 : Blo 1264450 5132639 := bstep (se 1 (by rfl) ⟨3849479, by rfl⟩ : syracuseStep 5132639 = 7698959) B7698959
theorem B2134687 : Blo 1264450 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B1266335 : Blo 1264450 1266335 := bstep (se 1 (by rfl) ⟨949751, by rfl⟩ : syracuseStep 1266335 = 1899503) B1899503
theorem B1897151 : Blo 1264450 1897151 := bstep (se 1 (by rfl) ⟨1422863, by rfl⟩ : syracuseStep 1897151 = 2845727) B2845727
theorem B1897193 : Blo 1264450 1897193 := bstep (se 2 (by rfl) ⟨711447, by rfl⟩ : syracuseStep 1897193 = 1422895) B1422895
theorem B1266415 : Blo 1264450 1266415 := bstep (se 1 (by rfl) ⟨949811, by rfl⟩ : syracuseStep 1266415 = 1899623) B1899623
theorem B51958739 : Blo 1264450 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B1520743 : Blo 1264450 1520743 := bstep (se 1 (by rfl) ⟨1140557, by rfl⟩ : syracuseStep 1520743 = 2281115) B2281115
theorem B3421801 : Blo 1264450 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B2848823 : Blo 1264450 2848823 := bstep (se 1 (by rfl) ⟨2136617, by rfl⟩ : syracuseStep 2848823 = 4273235) B4273235
theorem B5404745 : Blo 1264450 5404745 := bstep (se 2 (by rfl) ⟨2026779, by rfl⟩ : syracuseStep 5404745 = 4053559) B4053559
theorem B4561019 : Blo 1264450 4561019 := bstep (se 1 (by rfl) ⟨3420764, by rfl⟩ : syracuseStep 4561019 = 6841529) B6841529
theorem B1898633 : Blo 1264450 1898633 := bstep (se 2 (by rfl) ⟨711987, by rfl⟩ : syracuseStep 1898633 = 1423975) B1423975
theorem B5552687 : Blo 1264450 5552687 := bstep (se 1 (by rfl) ⟨4164515, by rfl⟩ : syracuseStep 5552687 = 8329031) B8329031
theorem B1899551 : Blo 1264450 1899551 := bstep (se 1 (by rfl) ⟨1424663, by rfl⟩ : syracuseStep 1899551 = 2849327) B2849327
theorem B22838537 : Blo 1264450 22838537 := bstep (se 2 (by rfl) ⟨8564451, by rfl⟩ : syracuseStep 22838537 = 17128903) B17128903
theorem B7691561 : Blo 1264450 7691561 := bstep (se 2 (by rfl) ⟨2884335, by rfl⟩ : syracuseStep 7691561 = 5768671) B5768671
theorem B1801855 : Blo 1264450 1801855 := bstep (se 1 (by rfl) ⟨1351391, by rfl⟩ : syracuseStep 1801855 = 2702783) B2702783
theorem B6840449 : Blo 1264450 6840449 := bstep (se 2 (by rfl) ⟨2565168, by rfl⟩ : syracuseStep 6840449 = 5130337) B5130337
theorem B3040679 : Blo 1264450 3040679 := bstep (se 1 (by rfl) ⟨2280509, by rfl⟩ : syracuseStep 3040679 = 4561019) B4561019
theorem B12993959 : Blo 1264450 12993959 := bstep (se 1 (by rfl) ⟨9745469, by rfl⟩ : syracuseStep 12993959 = 19490939) B19490939
theorem B4802075 : Blo 1264450 4802075 := bstep (se 1 (by rfl) ⟨3601556, by rfl⟩ : syracuseStep 4802075 = 7203113) B7203113
theorem B2402473 : Blo 1264450 2402473 := bstep (se 2 (by rfl) ⟨900927, by rfl⟩ : syracuseStep 2402473 = 1801855) B1801855
theorem B2026235 : Blo 1264450 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B4270859 : Blo 1264450 4270859 := bstep (se 1 (by rfl) ⟨3203144, by rfl⟩ : syracuseStep 4270859 = 6406289) B6406289
theorem B1264767 : Blo 1264450 1264767 := bstep (se 1 (by rfl) ⟨948575, by rfl⟩ : syracuseStep 1264767 = 1897151) B1897151
theorem B1264795 : Blo 1264450 1264795 := bstep (se 1 (by rfl) ⟨948596, by rfl⟩ : syracuseStep 1264795 = 1897193) B1897193
theorem B34639159 : Blo 1264450 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B2846123 : Blo 1264450 2846123 := bstep (se 1 (by rfl) ⟨2134592, by rfl⟩ : syracuseStep 2846123 = 4269185) B4269185
theorem B2846249 : Blo 1264450 2846249 := bstep (se 2 (by rfl) ⟨1067343, by rfl⟩ : syracuseStep 2846249 = 2134687) B2134687
theorem B6401591 : Blo 1264450 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B1265755 : Blo 1264450 1265755 := bstep (se 1 (by rfl) ⟨949316, by rfl⟩ : syracuseStep 1265755 = 1898633) B1898633
theorem B2027657 : Blo 1264450 2027657 := bstep (se 2 (by rfl) ⟨760371, by rfl⟩ : syracuseStep 2027657 = 1520743) B1520743
theorem B6402239 : Blo 1264450 6402239 := bstep (se 1 (by rfl) ⟨4801679, by rfl⟩ : syracuseStep 6402239 = 9603359) B9603359
theorem B2847023 : Blo 1264450 2847023 := bstep (se 1 (by rfl) ⟨2135267, by rfl⟩ : syracuseStep 2847023 = 4270535) B4270535
theorem B6845071 : Blo 1264450 6845071 := bstep (se 1 (by rfl) ⟨5133803, by rfl⟩ : syracuseStep 6845071 = 10267607) B10267607
theorem B1266367 : Blo 1264450 1266367 := bstep (se 1 (by rfl) ⟨949775, by rfl⟩ : syracuseStep 1266367 = 1899551) B1899551
theorem B15225691 : Blo 1264450 15225691 := bstep (se 1 (by rfl) ⟨11419268, by rfl⟩ : syracuseStep 15225691 = 22838537) B22838537
theorem B3421759 : Blo 1264450 3421759 := bstep (se 1 (by rfl) ⟨2566319, by rfl⟩ : syracuseStep 3421759 = 5132639) B5132639
theorem B4806647 : Blo 1264450 4806647 := bstep (se 1 (by rfl) ⟨3604985, by rfl⟩ : syracuseStep 4806647 = 7209971) B7209971
theorem B2136091 : Blo 1264450 2136091 := bstep (se 1 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 2136091 = 3204137) B3204137
theorem B1899215 : Blo 1264450 1899215 := bstep (se 1 (by rfl) ⟨1424411, by rfl⟩ : syracuseStep 1899215 = 2848823) B2848823
theorem B3603163 : Blo 1264450 3603163 := bstep (se 1 (by rfl) ⟨2702372, by rfl⟩ : syracuseStep 3603163 = 5404745) B5404745
theorem B4332523 : Blo 1264450 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B9608219 : Blo 1264450 9608219 := bstep (se 1 (by rfl) ⟨7206164, by rfl⟩ : syracuseStep 9608219 = 14412329) B14412329
theorem B3701791 : Blo 1264450 3701791 := bstep (se 1 (by rfl) ⟨2776343, by rfl⟩ : syracuseStep 3701791 = 5552687) B5552687
theorem B4562401 : Blo 1264450 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B5127707 : Blo 1264450 5127707 := bstep (se 1 (by rfl) ⟨3845780, by rfl⟩ : syracuseStep 5127707 = 7691561) B7691561
theorem B4562459 : Blo 1264450 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B1351771 : Blo 1264450 1351771 := bstep (se 1 (by rfl) ⟨1013828, by rfl⟩ : syracuseStep 1351771 = 2027657) B2027657
theorem B4268159 : Blo 1264450 4268159 := bstep (se 1 (by rfl) ⟨3201119, by rfl⟩ : syracuseStep 4268159 = 6402239) B6402239
theorem B19742885 : Blo 1264450 19742885 := bstep (se 4 (by rfl) ⟨1850895, by rfl⟩ : syracuseStep 19742885 = 3701791) B3701791
theorem B3203297 : Blo 1264450 3203297 := bstep (se 2 (by rfl) ⟨1201236, by rfl⟩ : syracuseStep 3203297 = 2402473) B2402473
theorem B9126761 : Blo 1264450 9126761 := bstep (se 2 (by rfl) ⟨3422535, by rfl⟩ : syracuseStep 9126761 = 6845071) B6845071
theorem B20300921 : Blo 1264450 20300921 := bstep (se 2 (by rfl) ⟨7612845, by rfl⟩ : syracuseStep 20300921 = 15225691) B15225691
theorem B5776697 : Blo 1264450 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B3204431 : Blo 1264450 3204431 := bstep (se 1 (by rfl) ⟨2403323, by rfl⟩ : syracuseStep 3204431 = 4806647) B4806647
theorem B3418471 : Blo 1264450 3418471 := bstep (se 1 (by rfl) ⟨2563853, by rfl⟩ : syracuseStep 3418471 = 5127707) B5127707
theorem B3041639 : Blo 1264450 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B2027119 : Blo 1264450 2027119 := bstep (se 1 (by rfl) ⟨1520339, by rfl⟩ : syracuseStep 2027119 = 3040679) B3040679
theorem B8662639 : Blo 1264450 8662639 := bstep (se 1 (by rfl) ⟨6496979, by rfl⟩ : syracuseStep 8662639 = 12993959) B12993959
theorem B4804217 : Blo 1264450 4804217 := bstep (se 2 (by rfl) ⟨1801581, by rfl⟩ : syracuseStep 4804217 = 3603163) B3603163
theorem B1266143 : Blo 1264450 1266143 := bstep (se 1 (by rfl) ⟨949607, by rfl⟩ : syracuseStep 1266143 = 1899215) B1899215
theorem B2847239 : Blo 1264450 2847239 := bstep (se 1 (by rfl) ⟨2135429, by rfl⟩ : syracuseStep 2847239 = 4270859) B4270859
theorem B6083201 : Blo 1264450 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B5403293 : Blo 1264450 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B1897415 : Blo 1264450 1897415 := bstep (se 1 (by rfl) ⟨1423061, by rfl⟩ : syracuseStep 1897415 = 2846123) B2846123
theorem B1897499 : Blo 1264450 1897499 := bstep (se 1 (by rfl) ⟨1423124, by rfl⟩ : syracuseStep 1897499 = 2846249) B2846249
theorem B2848121 : Blo 1264450 2848121 := bstep (se 2 (by rfl) ⟨1068045, by rfl⟩ : syracuseStep 2848121 = 2136091) B2136091
theorem B4560299 : Blo 1264450 4560299 := bstep (se 1 (by rfl) ⟨3420224, by rfl⟩ : syracuseStep 4560299 = 6840449) B6840449
theorem B1898015 : Blo 1264450 1898015 := bstep (se 1 (by rfl) ⟨1423511, by rfl⟩ : syracuseStep 1898015 = 2847023) B2847023
theorem B3201383 : Blo 1264450 3201383 := bstep (se 1 (by rfl) ⟨2401037, by rfl⟩ : syracuseStep 3201383 = 4802075) B4802075
theorem B46185545 : Blo 1264450 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B6405479 : Blo 1264450 6405479 := bstep (se 1 (by rfl) ⟨4804109, by rfl⟩ : syracuseStep 6405479 = 9608219) B9608219
theorem B4562345 : Blo 1264450 4562345 := bstep (se 2 (by rfl) ⟨1710879, by rfl⟩ : syracuseStep 4562345 = 3421759) B3421759
theorem B4267727 : Blo 1264450 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B7209445 : Blo 1264450 7209445 := bstep (se 4 (by rfl) ⟨675885, by rfl⟩ : syracuseStep 7209445 = 1351771) B1351771
theorem B13533947 : Blo 1264450 13533947 := bstep (se 1 (by rfl) ⟨10150460, by rfl⟩ : syracuseStep 13533947 = 20300921) B20300921
theorem B3040199 : Blo 1264450 3040199 := bstep (se 1 (by rfl) ⟨2280149, by rfl⟩ : syracuseStep 3040199 = 4560299) B4560299
theorem B16221869 : Blo 1264450 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B4270319 : Blo 1264450 4270319 := bstep (se 1 (by rfl) ⟨3202739, by rfl⟩ : syracuseStep 4270319 = 6405479) B6405479
theorem B3041563 : Blo 1264450 3041563 := bstep (se 1 (by rfl) ⟨2281172, by rfl⟩ : syracuseStep 3041563 = 4562345) B4562345
theorem B2845151 : Blo 1264450 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B2845439 : Blo 1264450 2845439 := bstep (se 1 (by rfl) ⟨2134079, by rfl⟩ : syracuseStep 2845439 = 4268159) B4268159
theorem B4557961 : Blo 1264450 4557961 := bstep (se 2 (by rfl) ⟨1709235, by rfl⟩ : syracuseStep 4557961 = 3418471) B3418471
theorem B1264943 : Blo 1264450 1264943 := bstep (se 1 (by rfl) ⟨948707, by rfl⟩ : syracuseStep 1264943 = 1897415) B1897415
theorem B1264999 : Blo 1264450 1264999 := bstep (se 1 (by rfl) ⟨948749, by rfl⟩ : syracuseStep 1264999 = 1897499) B1897499
theorem B15404525 : Blo 1264450 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B1265343 : Blo 1264450 1265343 := bstep (se 1 (by rfl) ⟨949007, by rfl⟩ : syracuseStep 1265343 = 1898015) B1898015
theorem B2134255 : Blo 1264450 2134255 := bstep (se 1 (by rfl) ⟨1600691, by rfl⟩ : syracuseStep 2134255 = 3201383) B3201383
theorem B2027759 : Blo 1264450 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B30790363 : Blo 1264450 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B13161923 : Blo 1264450 13161923 := bstep (se 1 (by rfl) ⟨9871442, by rfl⟩ : syracuseStep 13161923 = 19742885) B19742885
theorem B2135531 : Blo 1264450 2135531 := bstep (se 1 (by rfl) ⟨1601648, by rfl⟩ : syracuseStep 2135531 = 3203297) B3203297
theorem B1898159 : Blo 1264450 1898159 := bstep (se 1 (by rfl) ⟨1423619, by rfl⟩ : syracuseStep 1898159 = 2847239) B2847239
theorem B3602195 : Blo 1264450 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B2136287 : Blo 1264450 2136287 := bstep (se 1 (by rfl) ⟨1602215, by rfl⟩ : syracuseStep 2136287 = 3204431) B3204431
theorem B1898747 : Blo 1264450 1898747 := bstep (se 1 (by rfl) ⟨1424060, by rfl⟩ : syracuseStep 1898747 = 2848121) B2848121
theorem B2702825 : Blo 1264450 2702825 := bstep (se 2 (by rfl) ⟨1013559, by rfl⟩ : syracuseStep 2702825 = 2027119) B2027119
theorem B11550185 : Blo 1264450 11550185 := bstep (se 2 (by rfl) ⟨4331319, by rfl⟩ : syracuseStep 11550185 = 8662639) B8662639
theorem B24338029 : Blo 1264450 24338029 := bstep (se 3 (by rfl) ⟨4563380, by rfl⟩ : syracuseStep 24338029 = 9126761) B9126761
theorem B3202811 : Blo 1264450 3202811 := bstep (se 1 (by rfl) ⟨2402108, by rfl⟩ : syracuseStep 3202811 = 4804217) B4804217
theorem B4055417 : Blo 1264450 4055417 := bstep (se 2 (by rfl) ⟨1520781, by rfl⟩ : syracuseStep 4055417 = 3041563) B3041563
theorem B8774615 : Blo 1264450 8774615 := bstep (se 1 (by rfl) ⟨6580961, by rfl⟩ : syracuseStep 8774615 = 13161923) B13161923
theorem B10814579 : Blo 1264450 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B2401463 : Blo 1264450 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B32450705 : Blo 1264450 32450705 := bstep (se 2 (by rfl) ⟨12169014, by rfl⟩ : syracuseStep 32450705 = 24338029) B24338029
theorem B21629429 : Blo 1264450 21629429 := bstep (se 5 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 21629429 = 2027759) B2027759
theorem B2845673 : Blo 1264450 2845673 := bstep (se 2 (by rfl) ⟨1067127, by rfl⟩ : syracuseStep 2845673 = 2134255) B2134255
theorem B9022631 : Blo 1264450 9022631 := bstep (se 1 (by rfl) ⟨6766973, by rfl⟩ : syracuseStep 9022631 = 13533947) B13533947
theorem B2026799 : Blo 1264450 2026799 := bstep (se 1 (by rfl) ⟨1520099, by rfl⟩ : syracuseStep 2026799 = 3040199) B3040199
theorem B9612593 : Blo 1264450 9612593 := bstep (se 2 (by rfl) ⟨3604722, by rfl⟩ : syracuseStep 9612593 = 7209445) B7209445
theorem B41053817 : Blo 1264450 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B1265439 : Blo 1264450 1265439 := bstep (se 1 (by rfl) ⟨949079, by rfl⟩ : syracuseStep 1265439 = 1898159) B1898159
theorem B2846879 : Blo 1264450 2846879 := bstep (se 1 (by rfl) ⟨2135159, by rfl⟩ : syracuseStep 2846879 = 4270319) B4270319
theorem B1265831 : Blo 1264450 1265831 := bstep (se 1 (by rfl) ⟨949373, by rfl⟩ : syracuseStep 1265831 = 1898747) B1898747
theorem B1896767 : Blo 1264450 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B1896959 : Blo 1264450 1896959 := bstep (se 1 (by rfl) ⟨1422719, by rfl⟩ : syracuseStep 1896959 = 2845439) B2845439
theorem B10269683 : Blo 1264450 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B2135207 : Blo 1264450 2135207 := bstep (se 1 (by rfl) ⟨1601405, by rfl⟩ : syracuseStep 2135207 = 3202811) B3202811
theorem B1423687 : Blo 1264450 1423687 := bstep (se 1 (by rfl) ⟨1067765, by rfl⟩ : syracuseStep 1423687 = 2135531) B2135531
theorem B1424191 : Blo 1264450 1424191 := bstep (se 1 (by rfl) ⟨1068143, by rfl⟩ : syracuseStep 1424191 = 2136287) B2136287
theorem B6077281 : Blo 1264450 6077281 := bstep (se 2 (by rfl) ⟨2278980, by rfl⟩ : syracuseStep 6077281 = 4557961) B4557961
theorem B1801883 : Blo 1264450 1801883 := bstep (se 1 (by rfl) ⟨1351412, by rfl⟩ : syracuseStep 1801883 = 2702825) B2702825
theorem B7700123 : Blo 1264450 7700123 := bstep (se 1 (by rfl) ⟨5775092, by rfl⟩ : syracuseStep 7700123 = 11550185) B11550185
theorem B2703611 : Blo 1264450 2703611 := bstep (se 1 (by rfl) ⟨2027708, by rfl⟩ : syracuseStep 2703611 = 4055417) B4055417
theorem B24060349 : Blo 1264450 24060349 := bstep (se 3 (by rfl) ⟨4511315, by rfl⟩ : syracuseStep 24060349 = 9022631) B9022631
theorem B5849743 : Blo 1264450 5849743 := bstep (se 1 (by rfl) ⟨4387307, by rfl⟩ : syracuseStep 5849743 = 8774615) B8774615
theorem B7209719 : Blo 1264450 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B8103041 : Blo 1264450 8103041 := bstep (se 2 (by rfl) ⟨3038640, by rfl⟩ : syracuseStep 8103041 = 6077281) B6077281
theorem B14419619 : Blo 1264450 14419619 := bstep (se 1 (by rfl) ⟨10814714, by rfl⟩ : syracuseStep 14419619 = 21629429) B21629429
theorem B6408395 : Blo 1264450 6408395 := bstep (se 1 (by rfl) ⟨4806296, by rfl⟩ : syracuseStep 6408395 = 9612593) B9612593
theorem B1264511 : Blo 1264450 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B1264639 : Blo 1264450 1264639 := bstep (se 1 (by rfl) ⟨948479, by rfl⟩ : syracuseStep 1264639 = 1896959) B1896959
theorem B1600975 : Blo 1264450 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B4805021 : Blo 1264450 4805021 := bstep (se 3 (by rfl) ⟨900941, by rfl⟩ : syracuseStep 4805021 = 1801883) B1801883
theorem B20533661 : Blo 1264450 20533661 := bstep (se 3 (by rfl) ⟨3850061, by rfl⟩ : syracuseStep 20533661 = 7700123) B7700123
theorem B1897115 : Blo 1264450 1897115 := bstep (se 1 (by rfl) ⟨1422836, by rfl⟩ : syracuseStep 1897115 = 2845673) B2845673
theorem B1897919 : Blo 1264450 1897919 := bstep (se 1 (by rfl) ⟨1423439, by rfl⟩ : syracuseStep 1897919 = 2846879) B2846879
theorem B1898249 : Blo 1264450 1898249 := bstep (se 2 (by rfl) ⟨711843, by rfl⟩ : syracuseStep 1898249 = 1423687) B1423687
theorem B6846455 : Blo 1264450 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B1423471 : Blo 1264450 1423471 := bstep (se 1 (by rfl) ⟨1067603, by rfl⟩ : syracuseStep 1423471 = 2135207) B2135207
theorem B1898921 : Blo 1264450 1898921 := bstep (se 2 (by rfl) ⟨712095, by rfl⟩ : syracuseStep 1898921 = 1424191) B1424191
theorem B21633803 : Blo 1264450 21633803 := bstep (se 1 (by rfl) ⟨16225352, by rfl⟩ : syracuseStep 21633803 = 32450705) B32450705
theorem B109476845 : Blo 1264450 109476845 := bstep (se 3 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 109476845 = 41053817) B41053817
theorem B1351199 : Blo 1264450 1351199 := bstep (se 1 (by rfl) ⟨1013399, by rfl⟩ : syracuseStep 1351199 = 2026799) B2026799
theorem B1802407 : Blo 1264450 1802407 := bstep (se 1 (by rfl) ⟨1351805, by rfl⟩ : syracuseStep 1802407 = 2703611) B2703611
theorem B3203347 : Blo 1264450 3203347 := bstep (se 1 (by rfl) ⟨2402510, by rfl⟩ : syracuseStep 3203347 = 4805021) B4805021
theorem B13689107 : Blo 1264450 13689107 := bstep (se 1 (by rfl) ⟨10266830, by rfl⟩ : syracuseStep 13689107 = 20533661) B20533661
theorem B32080465 : Blo 1264450 32080465 := bstep (se 2 (by rfl) ⟨12030174, by rfl⟩ : syracuseStep 32080465 = 24060349) B24060349
theorem B7799657 : Blo 1264450 7799657 := bstep (se 2 (by rfl) ⟨2924871, by rfl⟩ : syracuseStep 7799657 = 5849743) B5849743
theorem B72984563 : Blo 1264450 72984563 := bstep (se 1 (by rfl) ⟨54738422, by rfl⟩ : syracuseStep 72984563 = 109476845) B109476845
theorem B1264743 : Blo 1264450 1264743 := bstep (se 1 (by rfl) ⟨948557, by rfl⟩ : syracuseStep 1264743 = 1897115) B1897115
theorem B5402027 : Blo 1264450 5402027 := bstep (se 1 (by rfl) ⟨4051520, by rfl⟩ : syracuseStep 5402027 = 8103041) B8103041
theorem B1265279 : Blo 1264450 1265279 := bstep (se 1 (by rfl) ⟨948959, by rfl⟩ : syracuseStep 1265279 = 1897919) B1897919
theorem B9613079 : Blo 1264450 9613079 := bstep (se 1 (by rfl) ⟨7209809, by rfl⟩ : syracuseStep 9613079 = 14419619) B14419619
theorem B1265499 : Blo 1264450 1265499 := bstep (se 1 (by rfl) ⟨949124, by rfl⟩ : syracuseStep 1265499 = 1898249) B1898249
theorem B4272263 : Blo 1264450 4272263 := bstep (se 1 (by rfl) ⟨3204197, by rfl⟩ : syracuseStep 4272263 = 6408395) B6408395
theorem B1265947 : Blo 1264450 1265947 := bstep (se 1 (by rfl) ⟨949460, by rfl⟩ : syracuseStep 1265947 = 1898921) B1898921
theorem B14422535 : Blo 1264450 14422535 := bstep (se 1 (by rfl) ⟨10816901, by rfl⟩ : syracuseStep 14422535 = 21633803) B21633803
theorem B2134633 : Blo 1264450 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B18257213 : Blo 1264450 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B1897961 : Blo 1264450 1897961 := bstep (se 2 (by rfl) ⟨711735, by rfl⟩ : syracuseStep 1897961 = 1423471) B1423471
theorem B4806479 : Blo 1264450 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B3603197 : Blo 1264450 3603197 := bstep (se 3 (by rfl) ⟨675599, by rfl⟩ : syracuseStep 3603197 = 1351199) B1351199
theorem B9126071 : Blo 1264450 9126071 := bstep (se 1 (by rfl) ⟨6844553, by rfl⟩ : syracuseStep 9126071 = 13689107) B13689107
theorem B3204319 : Blo 1264450 3204319 := bstep (se 1 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 3204319 = 4806479) B4806479
theorem B2402131 : Blo 1264450 2402131 := bstep (se 1 (by rfl) ⟨1801598, by rfl⟩ : syracuseStep 2402131 = 3603197) B3603197
theorem B6408719 : Blo 1264450 6408719 := bstep (se 1 (by rfl) ⟨4806539, by rfl⟩ : syracuseStep 6408719 = 9613079) B9613079
theorem B2403209 : Blo 1264450 2403209 := bstep (se 2 (by rfl) ⟨901203, by rfl⟩ : syracuseStep 2403209 = 1802407) B1802407
theorem B4271129 : Blo 1264450 4271129 := bstep (se 2 (by rfl) ⟨1601673, by rfl⟩ : syracuseStep 4271129 = 3203347) B3203347
theorem B2846177 : Blo 1264450 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B1265307 : Blo 1264450 1265307 := bstep (se 1 (by rfl) ⟨948980, by rfl⟩ : syracuseStep 1265307 = 1897961) B1897961
theorem B48656375 : Blo 1264450 48656375 := bstep (se 1 (by rfl) ⟨36492281, by rfl⟩ : syracuseStep 48656375 = 72984563) B72984563
theorem B3601351 : Blo 1264450 3601351 := bstep (se 1 (by rfl) ⟨2701013, by rfl⟩ : syracuseStep 3601351 = 5402027) B5402027
theorem B2848175 : Blo 1264450 2848175 := bstep (se 1 (by rfl) ⟨2136131, by rfl⟩ : syracuseStep 2848175 = 4272263) B4272263
theorem B9615023 : Blo 1264450 9615023 := bstep (se 1 (by rfl) ⟨7211267, by rfl⟩ : syracuseStep 9615023 = 14422535) B14422535
theorem B171095813 : Blo 1264450 171095813 := bstep (se 4 (by rfl) ⟨16040232, by rfl⟩ : syracuseStep 171095813 = 32080465) B32080465
theorem B12171475 : Blo 1264450 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B83196341 : Blo 1264450 83196341 := bstep (se 5 (by rfl) ⟨3899828, by rfl⟩ : syracuseStep 83196341 = 7799657) B7799657
theorem B16228633 : Blo 1264450 16228633 := bstep (se 2 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 16228633 = 12171475) B12171475
theorem B4801801 : Blo 1264450 4801801 := bstep (se 2 (by rfl) ⟨1800675, by rfl⟩ : syracuseStep 4801801 = 3601351) B3601351
theorem B6408557 : Blo 1264450 6408557 := bstep (se 3 (by rfl) ⟨1201604, by rfl⟩ : syracuseStep 6408557 = 2403209) B2403209
theorem B6410015 : Blo 1264450 6410015 := bstep (se 1 (by rfl) ⟨4807511, by rfl⟩ : syracuseStep 6410015 = 9615023) B9615023
theorem B55464227 : Blo 1264450 55464227 := bstep (se 1 (by rfl) ⟨41598170, by rfl⟩ : syracuseStep 55464227 = 83196341) B83196341
theorem B4272425 : Blo 1264450 4272425 := bstep (se 2 (by rfl) ⟨1602159, by rfl⟩ : syracuseStep 4272425 = 3204319) B3204319
theorem B4272479 : Blo 1264450 4272479 := bstep (se 1 (by rfl) ⟨3204359, by rfl⟩ : syracuseStep 4272479 = 6408719) B6408719
theorem B2847419 : Blo 1264450 2847419 := bstep (se 1 (by rfl) ⟨2135564, by rfl⟩ : syracuseStep 2847419 = 4271129) B4271129
theorem B1897451 : Blo 1264450 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B32437583 : Blo 1264450 32437583 := bstep (se 1 (by rfl) ⟨24328187, by rfl⟩ : syracuseStep 32437583 = 48656375) B48656375
theorem B6084047 : Blo 1264450 6084047 := bstep (se 1 (by rfl) ⟨4563035, by rfl⟩ : syracuseStep 6084047 = 9126071) B9126071
theorem B1898783 : Blo 1264450 1898783 := bstep (se 1 (by rfl) ⟨1424087, by rfl⟩ : syracuseStep 1898783 = 2848175) B2848175
theorem B114063875 : Blo 1264450 114063875 := bstep (se 1 (by rfl) ⟨85547906, by rfl⟩ : syracuseStep 114063875 = 171095813) B171095813
theorem B3202841 : Blo 1264450 3202841 := bstep (se 2 (by rfl) ⟨1201065, by rfl⟩ : syracuseStep 3202841 = 2402131) B2402131
theorem B4056031 : Blo 1264450 4056031 := bstep (se 1 (by rfl) ⟨3042023, by rfl⟩ : syracuseStep 4056031 = 6084047) B6084047
theorem B21638177 : Blo 1264450 21638177 := bstep (se 2 (by rfl) ⟨8114316, by rfl⟩ : syracuseStep 21638177 = 16228633) B16228633
theorem B1264967 : Blo 1264450 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B1265855 : Blo 1264450 1265855 := bstep (se 1 (by rfl) ⟨949391, by rfl⟩ : syracuseStep 1265855 = 1898783) B1898783
theorem B4272371 : Blo 1264450 4272371 := bstep (se 1 (by rfl) ⟨3204278, by rfl⟩ : syracuseStep 4272371 = 6408557) B6408557
theorem B76042583 : Blo 1264450 76042583 := bstep (se 1 (by rfl) ⟨57031937, by rfl⟩ : syracuseStep 76042583 = 114063875) B114063875
theorem B6402401 : Blo 1264450 6402401 := bstep (se 2 (by rfl) ⟨2400900, by rfl⟩ : syracuseStep 6402401 = 4801801) B4801801
theorem B2135227 : Blo 1264450 2135227 := bstep (se 1 (by rfl) ⟨1601420, by rfl⟩ : syracuseStep 2135227 = 3202841) B3202841
theorem B4273343 : Blo 1264450 4273343 := bstep (se 1 (by rfl) ⟨3205007, by rfl⟩ : syracuseStep 4273343 = 6410015) B6410015
theorem B36976151 : Blo 1264450 36976151 := bstep (se 1 (by rfl) ⟨27732113, by rfl⟩ : syracuseStep 36976151 = 55464227) B55464227
theorem B2848283 : Blo 1264450 2848283 := bstep (se 1 (by rfl) ⟨2136212, by rfl⟩ : syracuseStep 2848283 = 4272425) B4272425
theorem B2848319 : Blo 1264450 2848319 := bstep (se 1 (by rfl) ⟨2136239, by rfl⟩ : syracuseStep 2848319 = 4272479) B4272479
theorem B1898279 : Blo 1264450 1898279 := bstep (se 1 (by rfl) ⟨1423709, by rfl⟩ : syracuseStep 1898279 = 2847419) B2847419
theorem B21625055 : Blo 1264450 21625055 := bstep (se 1 (by rfl) ⟨16218791, by rfl⟩ : syracuseStep 21625055 = 32437583) B32437583
theorem B4268267 : Blo 1264450 4268267 := bstep (se 1 (by rfl) ⟨3201200, by rfl⟩ : syracuseStep 4268267 = 6402401) B6402401
theorem B24650767 : Blo 1264450 24650767 := bstep (se 1 (by rfl) ⟨18488075, by rfl⟩ : syracuseStep 24650767 = 36976151) B36976151
theorem B5408041 : Blo 1264450 5408041 := bstep (se 2 (by rfl) ⟨2028015, by rfl⟩ : syracuseStep 5408041 = 4056031) B4056031
theorem B50695055 : Blo 1264450 50695055 := bstep (se 1 (by rfl) ⟨38021291, by rfl⟩ : syracuseStep 50695055 = 76042583) B76042583
theorem B1265519 : Blo 1264450 1265519 := bstep (se 1 (by rfl) ⟨949139, by rfl⟩ : syracuseStep 1265519 = 1898279) B1898279
theorem B2846969 : Blo 1264450 2846969 := bstep (se 2 (by rfl) ⟨1067613, by rfl⟩ : syracuseStep 2846969 = 2135227) B2135227
theorem B2848247 : Blo 1264450 2848247 := bstep (se 1 (by rfl) ⟨2136185, by rfl⟩ : syracuseStep 2848247 = 4272371) B4272371
theorem B2848895 : Blo 1264450 2848895 := bstep (se 1 (by rfl) ⟨2136671, by rfl⟩ : syracuseStep 2848895 = 4273343) B4273343
theorem B1898855 : Blo 1264450 1898855 := bstep (se 1 (by rfl) ⟨1424141, by rfl⟩ : syracuseStep 1898855 = 2848283) B2848283
theorem B1898879 : Blo 1264450 1898879 := bstep (se 1 (by rfl) ⟨1424159, by rfl⟩ : syracuseStep 1898879 = 2848319) B2848319
theorem B14416703 : Blo 1264450 14416703 := bstep (se 1 (by rfl) ⟨10812527, by rfl⟩ : syracuseStep 14416703 = 21625055) B21625055
theorem B14425451 : Blo 1264450 14425451 := bstep (se 1 (by rfl) ⟨10819088, by rfl⟩ : syracuseStep 14425451 = 21638177) B21638177
theorem B32867689 : Blo 1264450 32867689 := bstep (se 2 (by rfl) ⟨12325383, by rfl⟩ : syracuseStep 32867689 = 24650767) B24650767
theorem B7210721 : Blo 1264450 7210721 := bstep (se 2 (by rfl) ⟨2704020, by rfl⟩ : syracuseStep 7210721 = 5408041) B5408041
theorem B9611135 : Blo 1264450 9611135 := bstep (se 1 (by rfl) ⟨7208351, by rfl⟩ : syracuseStep 9611135 = 14416703) B14416703
theorem B2845511 : Blo 1264450 2845511 := bstep (se 1 (by rfl) ⟨2134133, by rfl⟩ : syracuseStep 2845511 = 4268267) B4268267
theorem B1265903 : Blo 1264450 1265903 := bstep (se 1 (by rfl) ⟨949427, by rfl⟩ : syracuseStep 1265903 = 1898855) B1898855
theorem B1265919 : Blo 1264450 1265919 := bstep (se 1 (by rfl) ⟨949439, by rfl⟩ : syracuseStep 1265919 = 1898879) B1898879
theorem B33796703 : Blo 1264450 33796703 := bstep (se 1 (by rfl) ⟨25347527, by rfl⟩ : syracuseStep 33796703 = 50695055) B50695055
theorem B1897979 : Blo 1264450 1897979 := bstep (se 1 (by rfl) ⟨1423484, by rfl⟩ : syracuseStep 1897979 = 2846969) B2846969
theorem B1898831 : Blo 1264450 1898831 := bstep (se 1 (by rfl) ⟨1424123, by rfl⟩ : syracuseStep 1898831 = 2848247) B2848247
theorem B1899263 : Blo 1264450 1899263 := bstep (se 1 (by rfl) ⟨1424447, by rfl⟩ : syracuseStep 1899263 = 2848895) B2848895
theorem B9616967 : Blo 1264450 9616967 := bstep (se 1 (by rfl) ⟨7212725, by rfl⟩ : syracuseStep 9616967 = 14425451) B14425451
theorem B6407423 : Blo 1264450 6407423 := bstep (se 1 (by rfl) ⟨4805567, by rfl⟩ : syracuseStep 6407423 = 9611135) B9611135
theorem B22531135 : Blo 1264450 22531135 := bstep (se 1 (by rfl) ⟨16898351, by rfl⟩ : syracuseStep 22531135 = 33796703) B33796703
theorem B1265319 : Blo 1264450 1265319 := bstep (se 1 (by rfl) ⟨948989, by rfl⟩ : syracuseStep 1265319 = 1897979) B1897979
theorem B1265887 : Blo 1264450 1265887 := bstep (se 1 (by rfl) ⟨949415, by rfl⟩ : syracuseStep 1265887 = 1898831) B1898831
theorem B43823585 : Blo 1264450 43823585 := bstep (se 2 (by rfl) ⟨16433844, by rfl⟩ : syracuseStep 43823585 = 32867689) B32867689
theorem B1266175 : Blo 1264450 1266175 := bstep (se 1 (by rfl) ⟨949631, by rfl⟩ : syracuseStep 1266175 = 1899263) B1899263
theorem B1897007 : Blo 1264450 1897007 := bstep (se 1 (by rfl) ⟨1422755, by rfl⟩ : syracuseStep 1897007 = 2845511) B2845511
theorem B6411311 : Blo 1264450 6411311 := bstep (se 1 (by rfl) ⟨4808483, by rfl⟩ : syracuseStep 6411311 = 9616967) B9616967
theorem B4807147 : Blo 1264450 4807147 := bstep (se 1 (by rfl) ⟨3605360, by rfl⟩ : syracuseStep 4807147 = 7210721) B7210721
theorem B30041513 : Blo 1264450 30041513 := bstep (se 2 (by rfl) ⟨11265567, by rfl⟩ : syracuseStep 30041513 = 22531135) B22531135
theorem B29215723 : Blo 1264450 29215723 := bstep (se 1 (by rfl) ⟨21911792, by rfl⟩ : syracuseStep 29215723 = 43823585) B43823585
theorem B1264671 : Blo 1264450 1264671 := bstep (se 1 (by rfl) ⟨948503, by rfl⟩ : syracuseStep 1264671 = 1897007) B1897007
theorem B6409529 : Blo 1264450 6409529 := bstep (se 2 (by rfl) ⟨2403573, by rfl⟩ : syracuseStep 6409529 = 4807147) B4807147
theorem B4271615 : Blo 1264450 4271615 := bstep (se 1 (by rfl) ⟨3203711, by rfl⟩ : syracuseStep 4271615 = 6407423) B6407423
theorem B4274207 : Blo 1264450 4274207 := bstep (se 1 (by rfl) ⟨3205655, by rfl⟩ : syracuseStep 4274207 = 6411311) B6411311
theorem B38954297 : Blo 1264450 38954297 := bstep (se 2 (by rfl) ⟨14607861, by rfl⟩ : syracuseStep 38954297 = 29215723) B29215723
theorem B4273019 : Blo 1264450 4273019 := bstep (se 1 (by rfl) ⟨3204764, by rfl⟩ : syracuseStep 4273019 = 6409529) B6409529
theorem B2847743 : Blo 1264450 2847743 := bstep (se 1 (by rfl) ⟨2135807, by rfl⟩ : syracuseStep 2847743 = 4271615) B4271615
theorem B20027675 : Blo 1264450 20027675 := bstep (se 1 (by rfl) ⟨15020756, by rfl⟩ : syracuseStep 20027675 = 30041513) B30041513
theorem B2849471 : Blo 1264450 2849471 := bstep (se 1 (by rfl) ⟨2137103, by rfl⟩ : syracuseStep 2849471 = 4274207) B4274207
theorem B25969531 : Blo 1264450 25969531 := bstep (se 1 (by rfl) ⟨19477148, by rfl⟩ : syracuseStep 25969531 = 38954297) B38954297
theorem B2848679 : Blo 1264450 2848679 := bstep (se 1 (by rfl) ⟨2136509, by rfl⟩ : syracuseStep 2848679 = 4273019) B4273019
theorem B1898495 : Blo 1264450 1898495 := bstep (se 1 (by rfl) ⟨1423871, by rfl⟩ : syracuseStep 1898495 = 2847743) B2847743
theorem B13351783 : Blo 1264450 13351783 := bstep (se 1 (by rfl) ⟨10013837, by rfl⟩ : syracuseStep 13351783 = 20027675) B20027675
theorem B1899647 : Blo 1264450 1899647 := bstep (se 1 (by rfl) ⟨1424735, by rfl⟩ : syracuseStep 1899647 = 2849471) B2849471
theorem B17802377 : Blo 1264450 17802377 := bstep (se 2 (by rfl) ⟨6675891, by rfl⟩ : syracuseStep 17802377 = 13351783) B13351783
theorem B1265663 : Blo 1264450 1265663 := bstep (se 1 (by rfl) ⟨949247, by rfl⟩ : syracuseStep 1265663 = 1898495) B1898495
theorem B1266431 : Blo 1264450 1266431 := bstep (se 1 (by rfl) ⟨949823, by rfl⟩ : syracuseStep 1266431 = 1899647) B1899647
theorem B34626041 : Blo 1264450 34626041 := bstep (se 2 (by rfl) ⟨12984765, by rfl⟩ : syracuseStep 34626041 = 25969531) B25969531
theorem B1899119 : Blo 1264450 1899119 := bstep (se 1 (by rfl) ⟨1424339, by rfl⟩ : syracuseStep 1899119 = 2848679) B2848679
theorem B1266079 : Blo 1264450 1266079 := bstep (se 1 (by rfl) ⟨949559, by rfl⟩ : syracuseStep 1266079 = 1899119) B1899119
theorem B11868251 : Blo 1264450 11868251 := bstep (se 1 (by rfl) ⟨8901188, by rfl⟩ : syracuseStep 11868251 = 17802377) B17802377
theorem B23084027 : Blo 1264450 23084027 := bstep (se 1 (by rfl) ⟨17313020, by rfl⟩ : syracuseStep 23084027 = 34626041) B34626041
theorem B126594677 : Blo 1264450 126594677 := bstep (se 5 (by rfl) ⟨5934125, by rfl⟩ : syracuseStep 126594677 = 11868251) B11868251
theorem B15389351 : Blo 1264450 15389351 := bstep (se 1 (by rfl) ⟨11542013, by rfl⟩ : syracuseStep 15389351 = 23084027) B23084027
theorem B84396451 : Blo 1264450 84396451 := bstep (se 1 (by rfl) ⟨63297338, by rfl⟩ : syracuseStep 84396451 = 126594677) B126594677
theorem B10259567 : Blo 1264450 10259567 := bstep (se 1 (by rfl) ⟨7694675, by rfl⟩ : syracuseStep 10259567 = 15389351) B15389351
theorem B112528601 : Blo 1264450 112528601 := bstep (se 2 (by rfl) ⟨42198225, by rfl⟩ : syracuseStep 112528601 = 84396451) B84396451
theorem B6839711 : Blo 1264450 6839711 := bstep (se 1 (by rfl) ⟨5129783, by rfl⟩ : syracuseStep 6839711 = 10259567) B10259567
theorem B75019067 : Blo 1264450 75019067 := bstep (se 1 (by rfl) ⟨56264300, by rfl⟩ : syracuseStep 75019067 = 112528601) B112528601
theorem B4559807 : Blo 1264450 4559807 := bstep (se 1 (by rfl) ⟨3419855, by rfl⟩ : syracuseStep 4559807 = 6839711) B6839711
theorem B50012711 : Blo 1264450 50012711 := bstep (se 1 (by rfl) ⟨37509533, by rfl⟩ : syracuseStep 50012711 = 75019067) B75019067
theorem B3039871 : Blo 1264450 3039871 := bstep (se 1 (by rfl) ⟨2279903, by rfl⟩ : syracuseStep 3039871 = 4559807) B4559807
theorem B33341807 : Blo 1264450 33341807 := bstep (se 1 (by rfl) ⟨25006355, by rfl⟩ : syracuseStep 33341807 = 50012711) B50012711
theorem B4053161 : Blo 1264450 4053161 := bstep (se 2 (by rfl) ⟨1519935, by rfl⟩ : syracuseStep 4053161 = 3039871) B3039871
theorem B22227871 : Blo 1264450 22227871 := bstep (se 1 (by rfl) ⟨16670903, by rfl⟩ : syracuseStep 22227871 = 33341807) B33341807
theorem B2702107 : Blo 1264450 2702107 := bstep (se 1 (by rfl) ⟨2026580, by rfl⟩ : syracuseStep 2702107 = 4053161) B4053161
theorem B3602809 : Blo 1264450 3602809 := bstep (se 2 (by rfl) ⟨1351053, by rfl⟩ : syracuseStep 3602809 = 2702107) B2702107
theorem B29637161 : Blo 1264450 29637161 := bstep (se 2 (by rfl) ⟨11113935, by rfl⟩ : syracuseStep 29637161 = 22227871) B22227871
theorem B4803745 : Blo 1264450 4803745 := bstep (se 2 (by rfl) ⟨1801404, by rfl⟩ : syracuseStep 4803745 = 3602809) B3602809
theorem B19758107 : Blo 1264450 19758107 := bstep (se 1 (by rfl) ⟨14818580, by rfl⟩ : syracuseStep 19758107 = 29637161) B29637161
theorem B6404993 : Blo 1264450 6404993 := bstep (se 2 (by rfl) ⟨2401872, by rfl⟩ : syracuseStep 6404993 = 4803745) B4803745
theorem B13172071 : Blo 1264450 13172071 := bstep (se 1 (by rfl) ⟨9879053, by rfl⟩ : syracuseStep 13172071 = 19758107) B19758107
theorem B4269995 : Blo 1264450 4269995 := bstep (se 1 (by rfl) ⟨3202496, by rfl⟩ : syracuseStep 4269995 = 6404993) B6404993
theorem B17562761 : Blo 1264450 17562761 := bstep (se 2 (by rfl) ⟨6586035, by rfl⟩ : syracuseStep 17562761 = 13172071) B13172071
theorem B11708507 : Blo 1264450 11708507 := bstep (se 1 (by rfl) ⟨8781380, by rfl⟩ : syracuseStep 11708507 = 17562761) B17562761
theorem B2846663 : Blo 1264450 2846663 := bstep (se 1 (by rfl) ⟨2134997, by rfl⟩ : syracuseStep 2846663 = 4269995) B4269995
theorem B31222685 : Blo 1264450 31222685 := bstep (se 3 (by rfl) ⟨5854253, by rfl⟩ : syracuseStep 31222685 = 11708507) B11708507
theorem B1897775 : Blo 1264450 1897775 := bstep (se 1 (by rfl) ⟨1423331, by rfl⟩ : syracuseStep 1897775 = 2846663) B2846663
theorem B1265183 : Blo 1264450 1265183 := bstep (se 1 (by rfl) ⟨948887, by rfl⟩ : syracuseStep 1265183 = 1897775) B1897775
theorem B83260493 : Blo 1264450 83260493 := bstep (se 3 (by rfl) ⟨15611342, by rfl⟩ : syracuseStep 83260493 = 31222685) B31222685
theorem B55506995 : Blo 1264450 55506995 := bstep (se 1 (by rfl) ⟨41630246, by rfl⟩ : syracuseStep 55506995 = 83260493) B83260493
theorem B37004663 : Blo 1264450 37004663 := bstep (se 1 (by rfl) ⟨27753497, by rfl⟩ : syracuseStep 37004663 = 55506995) B55506995
theorem B24669775 : Blo 1264450 24669775 := bstep (se 1 (by rfl) ⟨18502331, by rfl⟩ : syracuseStep 24669775 = 37004663) B37004663
theorem B32893033 : Blo 1264450 32893033 := bstep (se 2 (by rfl) ⟨12334887, by rfl⟩ : syracuseStep 32893033 = 24669775) B24669775
theorem B43857377 : Blo 1264450 43857377 := bstep (se 2 (by rfl) ⟨16446516, by rfl⟩ : syracuseStep 43857377 = 32893033) B32893033
theorem B29238251 : Blo 1264450 29238251 := bstep (se 1 (by rfl) ⟨21928688, by rfl⟩ : syracuseStep 29238251 = 43857377) B43857377
theorem B77968669 : Blo 1264450 77968669 := bstep (se 3 (by rfl) ⟨14619125, by rfl⟩ : syracuseStep 77968669 = 29238251) B29238251
theorem B103958225 : Blo 1264450 103958225 := bstep (se 2 (by rfl) ⟨38984334, by rfl⟩ : syracuseStep 103958225 = 77968669) B77968669
theorem B69305483 : Blo 1264450 69305483 := bstep (se 1 (by rfl) ⟨51979112, by rfl⟩ : syracuseStep 69305483 = 103958225) B103958225
theorem B46203655 : Blo 1264450 46203655 := bstep (se 1 (by rfl) ⟨34652741, by rfl⟩ : syracuseStep 46203655 = 69305483) B69305483
theorem B61604873 : Blo 1264450 61604873 := bstep (se 2 (by rfl) ⟨23101827, by rfl⟩ : syracuseStep 61604873 = 46203655) B46203655
theorem B41069915 : Blo 1264450 41069915 := bstep (se 1 (by rfl) ⟨30802436, by rfl⟩ : syracuseStep 41069915 = 61604873) B61604873
theorem B27379943 : Blo 1264450 27379943 := bstep (se 1 (by rfl) ⟨20534957, by rfl⟩ : syracuseStep 27379943 = 41069915) B41069915
theorem B18253295 : Blo 1264450 18253295 := bstep (se 1 (by rfl) ⟨13689971, by rfl⟩ : syracuseStep 18253295 = 27379943) B27379943
theorem B12168863 : Blo 1264450 12168863 := bstep (se 1 (by rfl) ⟨9126647, by rfl⟩ : syracuseStep 12168863 = 18253295) B18253295
theorem B8112575 : Blo 1264450 8112575 := bstep (se 1 (by rfl) ⟨6084431, by rfl⟩ : syracuseStep 8112575 = 12168863) B12168863
theorem B5408383 : Blo 1264450 5408383 := bstep (se 1 (by rfl) ⟨4056287, by rfl⟩ : syracuseStep 5408383 = 8112575) B8112575
theorem B7211177 : Blo 1264450 7211177 := bstep (se 2 (by rfl) ⟨2704191, by rfl⟩ : syracuseStep 7211177 = 5408383) B5408383
theorem B4807451 : Blo 1264450 4807451 := bstep (se 1 (by rfl) ⟨3605588, by rfl⟩ : syracuseStep 4807451 = 7211177) B7211177
theorem B3204967 : Blo 1264450 3204967 := bstep (se 1 (by rfl) ⟨2403725, by rfl⟩ : syracuseStep 3204967 = 4807451) B4807451
theorem B4273289 : Blo 1264450 4273289 := bstep (se 2 (by rfl) ⟨1602483, by rfl⟩ : syracuseStep 4273289 = 3204967) B3204967
theorem B2848859 : Blo 1264450 2848859 := bstep (se 1 (by rfl) ⟨2136644, by rfl⟩ : syracuseStep 2848859 = 4273289) B4273289
theorem B1899239 : Blo 1264450 1899239 := bstep (se 1 (by rfl) ⟨1424429, by rfl⟩ : syracuseStep 1899239 = 2848859) B2848859
theorem B1266159 : Blo 1264450 1266159 := bstep (se 1 (by rfl) ⟨949619, by rfl⟩ : syracuseStep 1266159 = 1899239) B1899239

theorem C0 (j : ℕ) (h1 : 316112 ≤ j) (h2 : j ≤ 316611) : Blo 1264450 (4 * j + 3) := by
  interval_cases j
  · exact B1264451
  · exact B1264455
  · exact B1264459
  · exact B1264463
  · exact B1264467
  · exact B1264471
  · exact B1264475
  · exact B1264479
  · exact B1264483
  · exact B1264487
  · exact B1264491
  · exact B1264495
  · exact B1264499
  · exact B1264503
  · exact B1264507
  · exact B1264511
  · exact B1264515
  · exact B1264519
  · exact B1264523
  · exact B1264527
  · exact B1264531
  · exact B1264535
  · exact B1264539
  · exact B1264543
  · exact B1264547
  · exact B1264551
  · exact B1264555
  · exact B1264559
  · exact B1264563
  · exact B1264567
  · exact B1264571
  · exact B1264575
  · exact B1264579
  · exact B1264583
  · exact B1264587
  · exact B1264591
  · exact B1264595
  · exact B1264599
  · exact B1264603
  · exact B1264607
  · exact B1264611
  · exact B1264615
  · exact B1264619
  · exact B1264623
  · exact B1264627
  · exact B1264631
  · exact B1264635
  · exact B1264639
  · exact B1264643
  · exact B1264647
  · exact B1264651
  · exact B1264655
  · exact B1264659
  · exact B1264663
  · exact B1264667
  · exact B1264671
  · exact B1264675
  · exact B1264679
  · exact B1264683
  · exact B1264687
  · exact B1264691
  · exact B1264695
  · exact B1264699
  · exact B1264703
  · exact B1264707
  · exact B1264711
  · exact B1264715
  · exact B1264719
  · exact B1264723
  · exact B1264727
  · exact B1264731
  · exact B1264735
  · exact B1264739
  · exact B1264743
  · exact B1264747
  · exact B1264751
  · exact B1264755
  · exact B1264759
  · exact B1264763
  · exact B1264767
  · exact B1264771
  · exact B1264775
  · exact B1264779
  · exact B1264783
  · exact B1264787
  · exact B1264791
  · exact B1264795
  · exact B1264799
  · exact B1264803
  · exact B1264807
  · exact B1264811
  · exact B1264815
  · exact B1264819
  · exact B1264823
  · exact B1264827
  · exact B1264831
  · exact B1264835
  · exact B1264839
  · exact B1264843
  · exact B1264847
  · exact B1264851
  · exact B1264855
  · exact B1264859
  · exact B1264863
  · exact B1264867
  · exact B1264871
  · exact B1264875
  · exact B1264879
  · exact B1264883
  · exact B1264887
  · exact B1264891
  · exact B1264895
  · exact B1264899
  · exact B1264903
  · exact B1264907
  · exact B1264911
  · exact B1264915
  · exact B1264919
  · exact B1264923
  · exact B1264927
  · exact B1264931
  · exact B1264935
  · exact B1264939
  · exact B1264943
  · exact B1264947
  · exact B1264951
  · exact B1264955
  · exact B1264959
  · exact B1264963
  · exact B1264967
  · exact B1264971
  · exact B1264975
  · exact B1264979
  · exact B1264983
  · exact B1264987
  · exact B1264991
  · exact B1264995
  · exact B1264999
  · exact B1265003
  · exact B1265007
  · exact B1265011
  · exact B1265015
  · exact B1265019
  · exact B1265023
  · exact B1265027
  · exact B1265031
  · exact B1265035
  · exact B1265039
  · exact B1265043
  · exact B1265047
  · exact B1265051
  · exact B1265055
  · exact B1265059
  · exact B1265063
  · exact B1265067
  · exact B1265071
  · exact B1265075
  · exact B1265079
  · exact B1265083
  · exact B1265087
  · exact B1265091
  · exact B1265095
  · exact B1265099
  · exact B1265103
  · exact B1265107
  · exact B1265111
  · exact B1265115
  · exact B1265119
  · exact B1265123
  · exact B1265127
  · exact B1265131
  · exact B1265135
  · exact B1265139
  · exact B1265143
  · exact B1265147
  · exact B1265151
  · exact B1265155
  · exact B1265159
  · exact B1265163
  · exact B1265167
  · exact B1265171
  · exact B1265175
  · exact B1265179
  · exact B1265183
  · exact B1265187
  · exact B1265191
  · exact B1265195
  · exact B1265199
  · exact B1265203
  · exact B1265207
  · exact B1265211
  · exact B1265215
  · exact B1265219
  · exact B1265223
  · exact B1265227
  · exact B1265231
  · exact B1265235
  · exact B1265239
  · exact B1265243
  · exact B1265247
  · exact B1265251
  · exact B1265255
  · exact B1265259
  · exact B1265263
  · exact B1265267
  · exact B1265271
  · exact B1265275
  · exact B1265279
  · exact B1265283
  · exact B1265287
  · exact B1265291
  · exact B1265295
  · exact B1265299
  · exact B1265303
  · exact B1265307
  · exact B1265311
  · exact B1265315
  · exact B1265319
  · exact B1265323
  · exact B1265327
  · exact B1265331
  · exact B1265335
  · exact B1265339
  · exact B1265343
  · exact B1265347
  · exact B1265351
  · exact B1265355
  · exact B1265359
  · exact B1265363
  · exact B1265367
  · exact B1265371
  · exact B1265375
  · exact B1265379
  · exact B1265383
  · exact B1265387
  · exact B1265391
  · exact B1265395
  · exact B1265399
  · exact B1265403
  · exact B1265407
  · exact B1265411
  · exact B1265415
  · exact B1265419
  · exact B1265423
  · exact B1265427
  · exact B1265431
  · exact B1265435
  · exact B1265439
  · exact B1265443
  · exact B1265447
  · exact B1265451
  · exact B1265455
  · exact B1265459
  · exact B1265463
  · exact B1265467
  · exact B1265471
  · exact B1265475
  · exact B1265479
  · exact B1265483
  · exact B1265487
  · exact B1265491
  · exact B1265495
  · exact B1265499
  · exact B1265503
  · exact B1265507
  · exact B1265511
  · exact B1265515
  · exact B1265519
  · exact B1265523
  · exact B1265527
  · exact B1265531
  · exact B1265535
  · exact B1265539
  · exact B1265543
  · exact B1265547
  · exact B1265551
  · exact B1265555
  · exact B1265559
  · exact B1265563
  · exact B1265567
  · exact B1265571
  · exact B1265575
  · exact B1265579
  · exact B1265583
  · exact B1265587
  · exact B1265591
  · exact B1265595
  · exact B1265599
  · exact B1265603
  · exact B1265607
  · exact B1265611
  · exact B1265615
  · exact B1265619
  · exact B1265623
  · exact B1265627
  · exact B1265631
  · exact B1265635
  · exact B1265639
  · exact B1265643
  · exact B1265647
  · exact B1265651
  · exact B1265655
  · exact B1265659
  · exact B1265663
  · exact B1265667
  · exact B1265671
  · exact B1265675
  · exact B1265679
  · exact B1265683
  · exact B1265687
  · exact B1265691
  · exact B1265695
  · exact B1265699
  · exact B1265703
  · exact B1265707
  · exact B1265711
  · exact B1265715
  · exact B1265719
  · exact B1265723
  · exact B1265727
  · exact B1265731
  · exact B1265735
  · exact B1265739
  · exact B1265743
  · exact B1265747
  · exact B1265751
  · exact B1265755
  · exact B1265759
  · exact B1265763
  · exact B1265767
  · exact B1265771
  · exact B1265775
  · exact B1265779
  · exact B1265783
  · exact B1265787
  · exact B1265791
  · exact B1265795
  · exact B1265799
  · exact B1265803
  · exact B1265807
  · exact B1265811
  · exact B1265815
  · exact B1265819
  · exact B1265823
  · exact B1265827
  · exact B1265831
  · exact B1265835
  · exact B1265839
  · exact B1265843
  · exact B1265847
  · exact B1265851
  · exact B1265855
  · exact B1265859
  · exact B1265863
  · exact B1265867
  · exact B1265871
  · exact B1265875
  · exact B1265879
  · exact B1265883
  · exact B1265887
  · exact B1265891
  · exact B1265895
  · exact B1265899
  · exact B1265903
  · exact B1265907
  · exact B1265911
  · exact B1265915
  · exact B1265919
  · exact B1265923
  · exact B1265927
  · exact B1265931
  · exact B1265935
  · exact B1265939
  · exact B1265943
  · exact B1265947
  · exact B1265951
  · exact B1265955
  · exact B1265959
  · exact B1265963
  · exact B1265967
  · exact B1265971
  · exact B1265975
  · exact B1265979
  · exact B1265983
  · exact B1265987
  · exact B1265991
  · exact B1265995
  · exact B1265999
  · exact B1266003
  · exact B1266007
  · exact B1266011
  · exact B1266015
  · exact B1266019
  · exact B1266023
  · exact B1266027
  · exact B1266031
  · exact B1266035
  · exact B1266039
  · exact B1266043
  · exact B1266047
  · exact B1266051
  · exact B1266055
  · exact B1266059
  · exact B1266063
  · exact B1266067
  · exact B1266071
  · exact B1266075
  · exact B1266079
  · exact B1266083
  · exact B1266087
  · exact B1266091
  · exact B1266095
  · exact B1266099
  · exact B1266103
  · exact B1266107
  · exact B1266111
  · exact B1266115
  · exact B1266119
  · exact B1266123
  · exact B1266127
  · exact B1266131
  · exact B1266135
  · exact B1266139
  · exact B1266143
  · exact B1266147
  · exact B1266151
  · exact B1266155
  · exact B1266159
  · exact B1266163
  · exact B1266167
  · exact B1266171
  · exact B1266175
  · exact B1266179
  · exact B1266183
  · exact B1266187
  · exact B1266191
  · exact B1266195
  · exact B1266199
  · exact B1266203
  · exact B1266207
  · exact B1266211
  · exact B1266215
  · exact B1266219
  · exact B1266223
  · exact B1266227
  · exact B1266231
  · exact B1266235
  · exact B1266239
  · exact B1266243
  · exact B1266247
  · exact B1266251
  · exact B1266255
  · exact B1266259
  · exact B1266263
  · exact B1266267
  · exact B1266271
  · exact B1266275
  · exact B1266279
  · exact B1266283
  · exact B1266287
  · exact B1266291
  · exact B1266295
  · exact B1266299
  · exact B1266303
  · exact B1266307
  · exact B1266311
  · exact B1266315
  · exact B1266319
  · exact B1266323
  · exact B1266327
  · exact B1266331
  · exact B1266335
  · exact B1266339
  · exact B1266343
  · exact B1266347
  · exact B1266351
  · exact B1266355
  · exact B1266359
  · exact B1266363
  · exact B1266367
  · exact B1266371
  · exact B1266375
  · exact B1266379
  · exact B1266383
  · exact B1266387
  · exact B1266391
  · exact B1266395
  · exact B1266399
  · exact B1266403
  · exact B1266407
  · exact B1266411
  · exact B1266415
  · exact B1266419
  · exact B1266423
  · exact B1266427
  · exact B1266431
  · exact B1266435
  · exact B1266439
  · exact B1266443
  · exact B1266447

theorem solution (m : ℕ) (hlo : 1264450 ≤ m) (hhi : m ≤ 1266450) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 316112 ≤ j := by omega
    have hj2 : j ≤ 316611 := by omega
    have hb : Blo 1264450 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
