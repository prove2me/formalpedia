-- Prove2me | solution 1 for syracuse_descends_range_330750_334750
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:30.948567+00:00
-- url     : https://prove2.me/submissions/6351c5bc-2590-4349-b102-451806cd4000

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


theorem B2162933 : Blo 330750 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1212677 : Blo 330750 1212677 := bbase (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) (by norm_num)
theorem B4882837 : Blo 330750 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B1901141 : Blo 330750 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B5374613 : Blo 330750 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B2523797 : Blo 330750 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B951061 : Blo 330750 951061 := bbase (se 6 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 951061 = 44581) (by norm_num)
theorem B1016597 : Blo 330750 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B1016693 : Blo 330750 1016693 := bbase (se 5 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 1016693 = 95315) (by norm_num)
theorem B1606549 : Blo 330750 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B426989 : Blo 330750 426989 := bbase (se 3 (by rfl) ⟨80060, by rfl⟩ : syracuseStep 426989 = 160121) (by norm_num)
theorem B558157 : Blo 330750 558157 := bbase (se 3 (by rfl) ⟨104654, by rfl⟩ : syracuseStep 558157 = 209309) (by norm_num)
theorem B5407829 : Blo 330750 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B361589 : Blo 330750 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B558245 : Blo 330750 558245 := bbase (se 4 (by rfl) ⟨52335, by rfl⟩ : syracuseStep 558245 = 104671) (by norm_num)
theorem B853237 : Blo 330750 853237 := bbase (se 5 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 853237 = 79991) (by norm_num)
theorem B558373 : Blo 330750 558373 := bbase (se 4 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 558373 = 104695) (by norm_num)
theorem B558461 : Blo 330750 558461 := bbase (se 3 (by rfl) ⟨104711, by rfl⟩ : syracuseStep 558461 = 209423) (by norm_num)
theorem B755077 : Blo 330750 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B558589 : Blo 330750 558589 := bbase (se 3 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 558589 = 209471) (by norm_num)
theorem B558677 : Blo 330750 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B558805 : Blo 330750 558805 := bbase (se 7 (by rfl) ⟨6548, by rfl⟩ : syracuseStep 558805 = 13097) (by norm_num)
theorem B1902325 : Blo 330750 1902325 := bbase (se 5 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 1902325 = 178343) (by norm_num)
theorem B558893 : Blo 330750 558893 := bbase (se 3 (by rfl) ⟨104792, by rfl⟩ : syracuseStep 558893 = 209585) (by norm_num)
theorem B1509205 : Blo 330750 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B952165 : Blo 330750 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B427933 : Blo 330750 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B559021 : Blo 330750 559021 := bbase (se 3 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 559021 = 209633) (by norm_num)
theorem B559109 : Blo 330750 559109 := bbase (se 4 (by rfl) ⟨52416, by rfl⟩ : syracuseStep 559109 = 104833) (by norm_num)
theorem B428149 : Blo 330750 428149 := bbase (se 5 (by rfl) ⟨20069, by rfl⟩ : syracuseStep 428149 = 40139) (by norm_num)
theorem B559237 : Blo 330750 559237 := bbase (se 4 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 559237 = 104857) (by norm_num)
theorem B1116341 : Blo 330750 1116341 := bbase (se 5 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 1116341 = 104657) (by norm_num)
theorem B559325 : Blo 330750 559325 := bbase (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) (by norm_num)
theorem B559453 : Blo 330750 559453 := bbase (se 3 (by rfl) ⟨104897, by rfl⟩ : syracuseStep 559453 = 209795) (by norm_num)
theorem B2394485 : Blo 330750 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B559541 : Blo 330750 559541 := bbase (se 5 (by rfl) ⟨26228, by rfl⟩ : syracuseStep 559541 = 52457) (by norm_num)
theorem B559669 : Blo 330750 559669 := bbase (se 5 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 559669 = 52469) (by norm_num)
theorem B1116773 : Blo 330750 1116773 := bbase (se 4 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 1116773 = 209395) (by norm_num)
theorem B559757 : Blo 330750 559757 := bbase (se 3 (by rfl) ⟨104954, by rfl⟩ : syracuseStep 559757 = 209909) (by norm_num)
theorem B1804949 : Blo 330750 1804949 := bbase (se 6 (by rfl) ⟨42303, by rfl⟩ : syracuseStep 1804949 = 84607) (by norm_num)
theorem B559885 : Blo 330750 559885 := bbase (se 3 (by rfl) ⟨104978, by rfl⟩ : syracuseStep 559885 = 209957) (by norm_num)
theorem B559973 : Blo 330750 559973 := bbase (se 4 (by rfl) ⟨52497, by rfl⟩ : syracuseStep 559973 = 104995) (by norm_num)
theorem B560101 : Blo 330750 560101 := bbase (se 4 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 560101 = 105019) (by norm_num)
theorem B1117205 : Blo 330750 1117205 := bbase (se 6 (by rfl) ⟨26184, by rfl⟩ : syracuseStep 1117205 = 52369) (by norm_num)
theorem B560189 : Blo 330750 560189 := bbase (se 3 (by rfl) ⟨105035, by rfl⟩ : syracuseStep 560189 = 210071) (by norm_num)
theorem B396397 : Blo 330750 396397 := bbase (se 3 (by rfl) ⟨74324, by rfl⟩ : syracuseStep 396397 = 148649) (by norm_num)
theorem B560317 : Blo 330750 560317 := bbase (se 3 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 560317 = 210119) (by norm_num)
theorem B560405 : Blo 330750 560405 := bbase (se 6 (by rfl) ⟨13134, by rfl⟩ : syracuseStep 560405 = 26269) (by norm_num)
theorem B560533 : Blo 330750 560533 := bbase (se 6 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 560533 = 26275) (by norm_num)
theorem B1117637 : Blo 330750 1117637 := bbase (se 4 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 1117637 = 209557) (by norm_num)
theorem B1347029 : Blo 330750 1347029 := bbase (se 7 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 1347029 = 31571) (by norm_num)
theorem B560621 : Blo 330750 560621 := bbase (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) (by norm_num)
theorem B560749 : Blo 330750 560749 := bbase (se 3 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 560749 = 210281) (by norm_num)
theorem B1674917 : Blo 330750 1674917 := bbase (se 4 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 1674917 = 314047) (by norm_num)
theorem B1904309 : Blo 330750 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B560837 : Blo 330750 560837 := bbase (se 4 (by rfl) ⟨52578, by rfl⟩ : syracuseStep 560837 = 105157) (by norm_num)
theorem B560965 : Blo 330750 560965 := bbase (se 4 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 560965 = 105181) (by norm_num)
theorem B1118069 : Blo 330750 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B561053 : Blo 330750 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B3411925 : Blo 330750 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B561181 : Blo 330750 561181 := bbase (se 3 (by rfl) ⟨105221, by rfl⟩ : syracuseStep 561181 = 210443) (by norm_num)
theorem B856133 : Blo 330750 856133 := bbase (se 4 (by rfl) ⟨80262, by rfl⟩ : syracuseStep 856133 = 160525) (by norm_num)
theorem B13176917 : Blo 330750 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B561269 : Blo 330750 561269 := bbase (se 5 (by rfl) ⟨26309, by rfl⟩ : syracuseStep 561269 = 52619) (by norm_num)
theorem B397553 : Blo 330750 397553 := bbase (se 2 (by rfl) ⟨149082, by rfl⟩ : syracuseStep 397553 = 298165) (by norm_num)
theorem B561397 : Blo 330750 561397 := bbase (se 5 (by rfl) ⟨26315, by rfl⟩ : syracuseStep 561397 = 52631) (by norm_num)
theorem B1118501 : Blo 330750 1118501 := bbase (se 4 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 1118501 = 209719) (by norm_num)
theorem B561485 : Blo 330750 561485 := bbase (se 3 (by rfl) ⟨105278, by rfl⟩ : syracuseStep 561485 = 210557) (by norm_num)
theorem B561613 : Blo 330750 561613 := bbase (se 3 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 561613 = 210605) (by norm_num)
theorem B496133 : Blo 330750 496133 := bbase (se 4 (by rfl) ⟨46512, by rfl⟩ : syracuseStep 496133 = 93025) (by norm_num)
theorem B1282565 : Blo 330750 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B496157 : Blo 330750 496157 := bbase (se 3 (by rfl) ⟨93029, by rfl⟩ : syracuseStep 496157 = 186059) (by norm_num)
theorem B561701 : Blo 330750 561701 := bbase (se 4 (by rfl) ⟨52659, by rfl⟩ : syracuseStep 561701 = 105319) (by norm_num)
theorem B496181 : Blo 330750 496181 := bbase (se 5 (by rfl) ⟨23258, by rfl⟩ : syracuseStep 496181 = 46517) (by norm_num)
theorem B496205 : Blo 330750 496205 := bbase (se 3 (by rfl) ⟨93038, by rfl⟩ : syracuseStep 496205 = 186077) (by norm_num)
theorem B397909 : Blo 330750 397909 := bbase (se 8 (by rfl) ⟨2331, by rfl⟩ : syracuseStep 397909 = 4663) (by norm_num)
theorem B496229 : Blo 330750 496229 := bbase (se 4 (by rfl) ⟨46521, by rfl⟩ : syracuseStep 496229 = 93043) (by norm_num)
theorem B496253 : Blo 330750 496253 := bbase (se 3 (by rfl) ⟨93047, by rfl⟩ : syracuseStep 496253 = 186095) (by norm_num)
theorem B496277 : Blo 330750 496277 := bbase (se 6 (by rfl) ⟨11631, by rfl⟩ : syracuseStep 496277 = 23263) (by norm_num)
theorem B561829 : Blo 330750 561829 := bbase (se 4 (by rfl) ⟨52671, by rfl⟩ : syracuseStep 561829 = 105343) (by norm_num)
theorem B496301 : Blo 330750 496301 := bbase (se 3 (by rfl) ⟨93056, by rfl⟩ : syracuseStep 496301 = 186113) (by norm_num)
theorem B496325 : Blo 330750 496325 := bbase (se 4 (by rfl) ⟨46530, by rfl⟩ : syracuseStep 496325 = 93061) (by norm_num)
theorem B1020629 : Blo 330750 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B1118933 : Blo 330750 1118933 := bbase (se 7 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 1118933 = 26225) (by norm_num)
theorem B496349 : Blo 330750 496349 := bbase (se 3 (by rfl) ⟨93065, by rfl⟩ : syracuseStep 496349 = 186131) (by norm_num)
theorem B496373 : Blo 330750 496373 := bbase (se 5 (by rfl) ⟨23267, by rfl⟩ : syracuseStep 496373 = 46535) (by norm_num)
theorem B561917 : Blo 330750 561917 := bbase (se 3 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 561917 = 210719) (by norm_num)
theorem B496397 : Blo 330750 496397 := bbase (se 3 (by rfl) ⟨93074, by rfl⟩ : syracuseStep 496397 = 186149) (by norm_num)
theorem B398101 : Blo 330750 398101 := bbase (se 6 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 398101 = 18661) (by norm_num)
theorem B496421 : Blo 330750 496421 := bbase (se 4 (by rfl) ⟨46539, by rfl⟩ : syracuseStep 496421 = 93079) (by norm_num)
theorem B496445 : Blo 330750 496445 := bbase (se 3 (by rfl) ⟨93083, by rfl⟩ : syracuseStep 496445 = 186167) (by norm_num)
theorem B496469 : Blo 330750 496469 := bbase (se 9 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 496469 = 2909) (by norm_num)
theorem B496493 : Blo 330750 496493 := bbase (se 3 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 496493 = 186185) (by norm_num)
theorem B562045 : Blo 330750 562045 := bbase (se 3 (by rfl) ⟨105383, by rfl⟩ : syracuseStep 562045 = 210767) (by norm_num)
theorem B496517 : Blo 330750 496517 := bbase (se 4 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 496517 = 93097) (by norm_num)
theorem B496541 : Blo 330750 496541 := bbase (se 3 (by rfl) ⟨93101, by rfl⟩ : syracuseStep 496541 = 186203) (by norm_num)
theorem B398245 : Blo 330750 398245 := bbase (se 4 (by rfl) ⟨37335, by rfl⟩ : syracuseStep 398245 = 74671) (by norm_num)
theorem B496565 : Blo 330750 496565 := bbase (se 5 (by rfl) ⟨23276, by rfl⟩ : syracuseStep 496565 = 46553) (by norm_num)
theorem B1676213 : Blo 330750 1676213 := bbase (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) (by norm_num)
theorem B496589 : Blo 330750 496589 := bbase (se 3 (by rfl) ⟨93110, by rfl⟩ : syracuseStep 496589 = 186221) (by norm_num)
theorem B562133 : Blo 330750 562133 := bbase (se 7 (by rfl) ⟨6587, by rfl⟩ : syracuseStep 562133 = 13175) (by norm_num)
theorem B496613 : Blo 330750 496613 := bbase (se 4 (by rfl) ⟨46557, by rfl⟩ : syracuseStep 496613 = 93115) (by norm_num)
theorem B496637 : Blo 330750 496637 := bbase (se 3 (by rfl) ⟨93119, by rfl⟩ : syracuseStep 496637 = 186239) (by norm_num)
theorem B496661 : Blo 330750 496661 := bbase (se 6 (by rfl) ⟨11640, by rfl⟩ : syracuseStep 496661 = 23281) (by norm_num)
theorem B496685 : Blo 330750 496685 := bbase (se 3 (by rfl) ⟨93128, by rfl⟩ : syracuseStep 496685 = 186257) (by norm_num)
theorem B496709 : Blo 330750 496709 := bbase (se 4 (by rfl) ⟨46566, by rfl⟩ : syracuseStep 496709 = 93133) (by norm_num)
theorem B562261 : Blo 330750 562261 := bbase (se 8 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 562261 = 6589) (by norm_num)
theorem B496733 : Blo 330750 496733 := bbase (se 3 (by rfl) ⟨93137, by rfl⟩ : syracuseStep 496733 = 186275) (by norm_num)
theorem B496757 : Blo 330750 496757 := bbase (se 5 (by rfl) ⟨23285, by rfl⟩ : syracuseStep 496757 = 46571) (by norm_num)
theorem B1119365 : Blo 330750 1119365 := bbase (se 4 (by rfl) ⟨104940, by rfl⟩ : syracuseStep 1119365 = 209881) (by norm_num)
theorem B496781 : Blo 330750 496781 := bbase (se 3 (by rfl) ⟨93146, by rfl⟩ : syracuseStep 496781 = 186293) (by norm_num)
theorem B496805 : Blo 330750 496805 := bbase (se 4 (by rfl) ⟨46575, by rfl⟩ : syracuseStep 496805 = 93151) (by norm_num)
theorem B562349 : Blo 330750 562349 := bbase (se 3 (by rfl) ⟨105440, by rfl⟩ : syracuseStep 562349 = 210881) (by norm_num)
theorem B496829 : Blo 330750 496829 := bbase (se 3 (by rfl) ⟨93155, by rfl⟩ : syracuseStep 496829 = 186311) (by norm_num)
theorem B496853 : Blo 330750 496853 := bbase (se 7 (by rfl) ⟨5822, by rfl⟩ : syracuseStep 496853 = 11645) (by norm_num)
theorem B496877 : Blo 330750 496877 := bbase (se 3 (by rfl) ⟨93164, by rfl⟩ : syracuseStep 496877 = 186329) (by norm_num)
theorem B496901 : Blo 330750 496901 := bbase (se 4 (by rfl) ⟨46584, by rfl⟩ : syracuseStep 496901 = 93169) (by norm_num)
theorem B496925 : Blo 330750 496925 := bbase (se 3 (by rfl) ⟨93173, by rfl⟩ : syracuseStep 496925 = 186347) (by norm_num)
theorem B562477 : Blo 330750 562477 := bbase (se 3 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 562477 = 210929) (by norm_num)
theorem B496949 : Blo 330750 496949 := bbase (se 5 (by rfl) ⟨23294, by rfl⟩ : syracuseStep 496949 = 46589) (by norm_num)
theorem B496973 : Blo 330750 496973 := bbase (se 3 (by rfl) ⟨93182, by rfl⟩ : syracuseStep 496973 = 186365) (by norm_num)
theorem B496997 : Blo 330750 496997 := bbase (se 4 (by rfl) ⟨46593, by rfl⟩ : syracuseStep 496997 = 93187) (by norm_num)
theorem B497021 : Blo 330750 497021 := bbase (se 3 (by rfl) ⟨93191, by rfl⟩ : syracuseStep 497021 = 186383) (by norm_num)
theorem B562565 : Blo 330750 562565 := bbase (se 4 (by rfl) ⟨52740, by rfl⟩ : syracuseStep 562565 = 105481) (by norm_num)
theorem B497045 : Blo 330750 497045 := bbase (se 6 (by rfl) ⟨11649, by rfl⟩ : syracuseStep 497045 = 23299) (by norm_num)
theorem B497069 : Blo 330750 497069 := bbase (se 3 (by rfl) ⟨93200, by rfl⟩ : syracuseStep 497069 = 186401) (by norm_num)
theorem B497093 : Blo 330750 497093 := bbase (se 4 (by rfl) ⟨46602, by rfl⟩ : syracuseStep 497093 = 93205) (by norm_num)
theorem B497117 : Blo 330750 497117 := bbase (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) (by norm_num)
theorem B497141 : Blo 330750 497141 := bbase (se 5 (by rfl) ⟨23303, by rfl⟩ : syracuseStep 497141 = 46607) (by norm_num)
theorem B1218053 : Blo 330750 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B562693 : Blo 330750 562693 := bbase (se 4 (by rfl) ⟨52752, by rfl⟩ : syracuseStep 562693 = 105505) (by norm_num)
theorem B497165 : Blo 330750 497165 := bbase (se 3 (by rfl) ⟨93218, by rfl⟩ : syracuseStep 497165 = 186437) (by norm_num)
theorem B529949 : Blo 330750 529949 := bbase (se 3 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 529949 = 198731) (by norm_num)
theorem B497189 : Blo 330750 497189 := bbase (se 4 (by rfl) ⟨46611, by rfl⟩ : syracuseStep 497189 = 93223) (by norm_num)
theorem B1119797 : Blo 330750 1119797 := bbase (se 5 (by rfl) ⟨52490, by rfl⟩ : syracuseStep 1119797 = 104981) (by norm_num)
theorem B497213 : Blo 330750 497213 := bbase (se 3 (by rfl) ⟨93227, by rfl⟩ : syracuseStep 497213 = 186455) (by norm_num)
theorem B497237 : Blo 330750 497237 := bbase (se 8 (by rfl) ⟨2913, by rfl⟩ : syracuseStep 497237 = 5827) (by norm_num)
theorem B562781 : Blo 330750 562781 := bbase (se 3 (by rfl) ⟨105521, by rfl⟩ : syracuseStep 562781 = 211043) (by norm_num)
theorem B497261 : Blo 330750 497261 := bbase (se 3 (by rfl) ⟨93236, by rfl⟩ : syracuseStep 497261 = 186473) (by norm_num)
theorem B497285 : Blo 330750 497285 := bbase (se 4 (by rfl) ⟨46620, by rfl⟩ : syracuseStep 497285 = 93241) (by norm_num)
theorem B497309 : Blo 330750 497309 := bbase (se 3 (by rfl) ⟨93245, by rfl⟩ : syracuseStep 497309 = 186491) (by norm_num)
theorem B497333 : Blo 330750 497333 := bbase (se 5 (by rfl) ⟨23312, by rfl⟩ : syracuseStep 497333 = 46625) (by norm_num)
theorem B1414853 : Blo 330750 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B497357 : Blo 330750 497357 := bbase (se 3 (by rfl) ⟨93254, by rfl⟩ : syracuseStep 497357 = 186509) (by norm_num)
theorem B562909 : Blo 330750 562909 := bbase (se 3 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 562909 = 211091) (by norm_num)
theorem B497381 : Blo 330750 497381 := bbase (se 4 (by rfl) ⟨46629, by rfl⟩ : syracuseStep 497381 = 93259) (by norm_num)
theorem B530173 : Blo 330750 530173 := bbase (se 3 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 530173 = 198815) (by norm_num)
theorem B497405 : Blo 330750 497405 := bbase (se 3 (by rfl) ⟨93263, by rfl⟩ : syracuseStep 497405 = 186527) (by norm_num)
theorem B497429 : Blo 330750 497429 := bbase (se 6 (by rfl) ⟨11658, by rfl⟩ : syracuseStep 497429 = 23317) (by norm_num)
theorem B497453 : Blo 330750 497453 := bbase (se 3 (by rfl) ⟨93272, by rfl⟩ : syracuseStep 497453 = 186545) (by norm_num)
theorem B562997 : Blo 330750 562997 := bbase (se 5 (by rfl) ⟨26390, by rfl⟩ : syracuseStep 562997 = 52781) (by norm_num)
theorem B497477 : Blo 330750 497477 := bbase (se 4 (by rfl) ⟨46638, by rfl⟩ : syracuseStep 497477 = 93277) (by norm_num)
theorem B628573 : Blo 330750 628573 := bbase (se 3 (by rfl) ⟨117857, by rfl⟩ : syracuseStep 628573 = 235715) (by norm_num)
theorem B497501 : Blo 330750 497501 := bbase (se 3 (by rfl) ⟨93281, by rfl⟩ : syracuseStep 497501 = 186563) (by norm_num)
theorem B497525 : Blo 330750 497525 := bbase (se 5 (by rfl) ⟨23321, by rfl⟩ : syracuseStep 497525 = 46643) (by norm_num)
theorem B497549 : Blo 330750 497549 := bbase (se 3 (by rfl) ⟨93290, by rfl⟩ : syracuseStep 497549 = 186581) (by norm_num)
theorem B497573 : Blo 330750 497573 := bbase (se 4 (by rfl) ⟨46647, by rfl⟩ : syracuseStep 497573 = 93295) (by norm_num)
theorem B563125 : Blo 330750 563125 := bbase (se 5 (by rfl) ⟨26396, by rfl⟩ : syracuseStep 563125 = 52793) (by norm_num)
theorem B497597 : Blo 330750 497597 := bbase (se 3 (by rfl) ⟨93299, by rfl⟩ : syracuseStep 497597 = 186599) (by norm_num)
theorem B497621 : Blo 330750 497621 := bbase (se 7 (by rfl) ⟨5831, by rfl⟩ : syracuseStep 497621 = 11663) (by norm_num)
theorem B366557 : Blo 330750 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B1120229 : Blo 330750 1120229 := bbase (se 4 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 1120229 = 210043) (by norm_num)
theorem B628717 : Blo 330750 628717 := bbase (se 3 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 628717 = 235769) (by norm_num)
theorem B497645 : Blo 330750 497645 := bbase (se 3 (by rfl) ⟨93308, by rfl⟩ : syracuseStep 497645 = 186617) (by norm_num)
theorem B497669 : Blo 330750 497669 := bbase (se 4 (by rfl) ⟨46656, by rfl⟩ : syracuseStep 497669 = 93313) (by norm_num)
theorem B563213 : Blo 330750 563213 := bbase (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) (by norm_num)
theorem B497693 : Blo 330750 497693 := bbase (se 3 (by rfl) ⟨93317, by rfl⟩ : syracuseStep 497693 = 186635) (by norm_num)
theorem B497717 : Blo 330750 497717 := bbase (se 5 (by rfl) ⟨23330, by rfl⟩ : syracuseStep 497717 = 46661) (by norm_num)
theorem B497741 : Blo 330750 497741 := bbase (se 3 (by rfl) ⟨93326, by rfl⟩ : syracuseStep 497741 = 186653) (by norm_num)
theorem B497765 : Blo 330750 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B497789 : Blo 330750 497789 := bbase (se 3 (by rfl) ⟨93335, by rfl⟩ : syracuseStep 497789 = 186671) (by norm_num)
theorem B628877 : Blo 330750 628877 := bbase (se 3 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 628877 = 235829) (by norm_num)
theorem B563341 : Blo 330750 563341 := bbase (se 3 (by rfl) ⟨105626, by rfl⟩ : syracuseStep 563341 = 211253) (by norm_num)
theorem B497813 : Blo 330750 497813 := bbase (se 6 (by rfl) ⟨11667, by rfl⟩ : syracuseStep 497813 = 23335) (by norm_num)
theorem B858269 : Blo 330750 858269 := bbase (se 3 (by rfl) ⟨160925, by rfl⟩ : syracuseStep 858269 = 321851) (by norm_num)
theorem B497837 : Blo 330750 497837 := bbase (se 3 (by rfl) ⟨93344, by rfl⟩ : syracuseStep 497837 = 186689) (by norm_num)
theorem B1677509 : Blo 330750 1677509 := bbase (se 4 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 1677509 = 314533) (by norm_num)
theorem B497861 : Blo 330750 497861 := bbase (se 4 (by rfl) ⟨46674, by rfl⟩ : syracuseStep 497861 = 93349) (by norm_num)
theorem B5445845 : Blo 330750 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B497885 : Blo 330750 497885 := bbase (se 3 (by rfl) ⟨93353, by rfl⟩ : syracuseStep 497885 = 186707) (by norm_num)
theorem B563429 : Blo 330750 563429 := bbase (se 4 (by rfl) ⟨52821, by rfl⟩ : syracuseStep 563429 = 105643) (by norm_num)
theorem B497909 : Blo 330750 497909 := bbase (se 5 (by rfl) ⟨23339, by rfl⟩ : syracuseStep 497909 = 46679) (by norm_num)
theorem B497933 : Blo 330750 497933 := bbase (se 3 (by rfl) ⟨93362, by rfl⟩ : syracuseStep 497933 = 186725) (by norm_num)
theorem B629021 : Blo 330750 629021 := bbase (se 3 (by rfl) ⟨117941, by rfl⟩ : syracuseStep 629021 = 235883) (by norm_num)
theorem B497957 : Blo 330750 497957 := bbase (se 4 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 497957 = 93367) (by norm_num)
theorem B497981 : Blo 330750 497981 := bbase (se 3 (by rfl) ⟨93371, by rfl⟩ : syracuseStep 497981 = 186743) (by norm_num)
theorem B498005 : Blo 330750 498005 := bbase (se 10 (by rfl) ⟨729, by rfl⟩ : syracuseStep 498005 = 1459) (by norm_num)
theorem B563557 : Blo 330750 563557 := bbase (se 4 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 563557 = 105667) (by norm_num)
theorem B498029 : Blo 330750 498029 := bbase (se 3 (by rfl) ⟨93380, by rfl⟩ : syracuseStep 498029 = 186761) (by norm_num)
theorem B498053 : Blo 330750 498053 := bbase (se 4 (by rfl) ⟨46692, by rfl⟩ : syracuseStep 498053 = 93385) (by norm_num)
theorem B1120661 : Blo 330750 1120661 := bbase (se 6 (by rfl) ⟨26265, by rfl⟩ : syracuseStep 1120661 = 52531) (by norm_num)
theorem B498077 : Blo 330750 498077 := bbase (se 3 (by rfl) ⟨93389, by rfl⟩ : syracuseStep 498077 = 186779) (by norm_num)
theorem B399773 : Blo 330750 399773 := bbase (se 3 (by rfl) ⟨74957, by rfl⟩ : syracuseStep 399773 = 149915) (by norm_num)
theorem B498101 : Blo 330750 498101 := bbase (se 5 (by rfl) ⟨23348, by rfl⟩ : syracuseStep 498101 = 46697) (by norm_num)
theorem B563645 : Blo 330750 563645 := bbase (se 3 (by rfl) ⟨105683, by rfl⟩ : syracuseStep 563645 = 211367) (by norm_num)
theorem B498125 : Blo 330750 498125 := bbase (se 3 (by rfl) ⟨93398, by rfl⟩ : syracuseStep 498125 = 186797) (by norm_num)
theorem B498149 : Blo 330750 498149 := bbase (se 4 (by rfl) ⟨46701, by rfl⟩ : syracuseStep 498149 = 93403) (by norm_num)
theorem B498173 : Blo 330750 498173 := bbase (se 3 (by rfl) ⟨93407, by rfl⟩ : syracuseStep 498173 = 186815) (by norm_num)
theorem B498197 : Blo 330750 498197 := bbase (se 6 (by rfl) ⟨11676, by rfl⟩ : syracuseStep 498197 = 23353) (by norm_num)
theorem B498221 : Blo 330750 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B629309 : Blo 330750 629309 := bbase (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) (by norm_num)
theorem B563773 : Blo 330750 563773 := bbase (se 3 (by rfl) ⟨105707, by rfl⟩ : syracuseStep 563773 = 211415) (by norm_num)
theorem B498245 : Blo 330750 498245 := bbase (se 4 (by rfl) ⟨46710, by rfl⟩ : syracuseStep 498245 = 93421) (by norm_num)
theorem B498269 : Blo 330750 498269 := bbase (se 3 (by rfl) ⟨93425, by rfl⟩ : syracuseStep 498269 = 186851) (by norm_num)
theorem B498293 : Blo 330750 498293 := bbase (se 5 (by rfl) ⟨23357, by rfl⟩ : syracuseStep 498293 = 46715) (by norm_num)
theorem B2857589 : Blo 330750 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B1809013 : Blo 330750 1809013 := bbase (se 5 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 1809013 = 169595) (by norm_num)
theorem B498317 : Blo 330750 498317 := bbase (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) (by norm_num)
theorem B563861 : Blo 330750 563861 := bbase (se 6 (by rfl) ⟨13215, by rfl⟩ : syracuseStep 563861 = 26431) (by norm_num)
theorem B498341 : Blo 330750 498341 := bbase (se 4 (by rfl) ⟨46719, by rfl⟩ : syracuseStep 498341 = 93439) (by norm_num)
theorem B498365 : Blo 330750 498365 := bbase (se 3 (by rfl) ⟨93443, by rfl⟩ : syracuseStep 498365 = 186887) (by norm_num)
theorem B400081 : Blo 330750 400081 := bbase (se 2 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 400081 = 300061) (by norm_num)
theorem B629461 : Blo 330750 629461 := bbase (se 7 (by rfl) ⟨7376, by rfl⟩ : syracuseStep 629461 = 14753) (by norm_num)
theorem B498389 : Blo 330750 498389 := bbase (se 7 (by rfl) ⟨5840, by rfl⟩ : syracuseStep 498389 = 11681) (by norm_num)
theorem B498413 : Blo 330750 498413 := bbase (se 3 (by rfl) ⟨93452, by rfl⟩ : syracuseStep 498413 = 186905) (by norm_num)
theorem B498437 : Blo 330750 498437 := bbase (se 4 (by rfl) ⟨46728, by rfl⟩ : syracuseStep 498437 = 93457) (by norm_num)
theorem B563989 : Blo 330750 563989 := bbase (se 6 (by rfl) ⟨13218, by rfl⟩ : syracuseStep 563989 = 26437) (by norm_num)
theorem B498461 : Blo 330750 498461 := bbase (se 3 (by rfl) ⟨93461, by rfl⟩ : syracuseStep 498461 = 186923) (by norm_num)
theorem B400177 : Blo 330750 400177 := bbase (se 2 (by rfl) ⟨150066, by rfl⟩ : syracuseStep 400177 = 300133) (by norm_num)
theorem B498485 : Blo 330750 498485 := bbase (se 5 (by rfl) ⟨23366, by rfl⟩ : syracuseStep 498485 = 46733) (by norm_num)
theorem B1121093 : Blo 330750 1121093 := bbase (se 4 (by rfl) ⟨105102, by rfl⟩ : syracuseStep 1121093 = 210205) (by norm_num)
theorem B498509 : Blo 330750 498509 := bbase (se 3 (by rfl) ⟨93470, by rfl⟩ : syracuseStep 498509 = 186941) (by norm_num)
theorem B760661 : Blo 330750 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B531301 : Blo 330750 531301 := bbase (se 4 (by rfl) ⟨49809, by rfl⟩ : syracuseStep 531301 = 99619) (by norm_num)
theorem B498533 : Blo 330750 498533 := bbase (se 4 (by rfl) ⟨46737, by rfl⟩ : syracuseStep 498533 = 93475) (by norm_num)
theorem B564077 : Blo 330750 564077 := bbase (se 3 (by rfl) ⟨105764, by rfl⟩ : syracuseStep 564077 = 211529) (by norm_num)
theorem B498557 : Blo 330750 498557 := bbase (se 3 (by rfl) ⟨93479, by rfl⟩ : syracuseStep 498557 = 186959) (by norm_num)
theorem B498581 : Blo 330750 498581 := bbase (se 6 (by rfl) ⟨11685, by rfl⟩ : syracuseStep 498581 = 23371) (by norm_num)
theorem B498605 : Blo 330750 498605 := bbase (se 3 (by rfl) ⟨93488, by rfl⟩ : syracuseStep 498605 = 186977) (by norm_num)
theorem B498629 : Blo 330750 498629 := bbase (se 4 (by rfl) ⟨46746, by rfl⟩ : syracuseStep 498629 = 93493) (by norm_num)
theorem B498653 : Blo 330750 498653 := bbase (se 3 (by rfl) ⟨93497, by rfl⟩ : syracuseStep 498653 = 186995) (by norm_num)
theorem B564205 : Blo 330750 564205 := bbase (se 3 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 564205 = 211577) (by norm_num)
theorem B498677 : Blo 330750 498677 := bbase (se 5 (by rfl) ⟨23375, by rfl⟩ : syracuseStep 498677 = 46751) (by norm_num)
theorem B629765 : Blo 330750 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B498701 : Blo 330750 498701 := bbase (se 3 (by rfl) ⟨93506, by rfl⟩ : syracuseStep 498701 = 187013) (by norm_num)
theorem B498725 : Blo 330750 498725 := bbase (se 4 (by rfl) ⟨46755, by rfl⟩ : syracuseStep 498725 = 93511) (by norm_num)
theorem B498749 : Blo 330750 498749 := bbase (se 3 (by rfl) ⟨93515, by rfl⟩ : syracuseStep 498749 = 187031) (by norm_num)
theorem B564293 : Blo 330750 564293 := bbase (se 4 (by rfl) ⟨52902, by rfl⟩ : syracuseStep 564293 = 105805) (by norm_num)
theorem B400465 : Blo 330750 400465 := bbase (se 2 (by rfl) ⟨150174, by rfl⟩ : syracuseStep 400465 = 300349) (by norm_num)
theorem B498773 : Blo 330750 498773 := bbase (se 8 (by rfl) ⟨2922, by rfl⟩ : syracuseStep 498773 = 5845) (by norm_num)
theorem B498797 : Blo 330750 498797 := bbase (se 3 (by rfl) ⟨93524, by rfl⟩ : syracuseStep 498797 = 187049) (by norm_num)
theorem B498821 : Blo 330750 498821 := bbase (se 4 (by rfl) ⟨46764, by rfl⟩ : syracuseStep 498821 = 93529) (by norm_num)
theorem B498845 : Blo 330750 498845 := bbase (se 3 (by rfl) ⟨93533, by rfl⟩ : syracuseStep 498845 = 187067) (by norm_num)
theorem B498869 : Blo 330750 498869 := bbase (se 5 (by rfl) ⟨23384, by rfl⟩ : syracuseStep 498869 = 46769) (by norm_num)
theorem B564421 : Blo 330750 564421 := bbase (se 4 (by rfl) ⟨52914, by rfl⟩ : syracuseStep 564421 = 105829) (by norm_num)
theorem B498893 : Blo 330750 498893 := bbase (se 3 (by rfl) ⟨93542, by rfl⟩ : syracuseStep 498893 = 187085) (by norm_num)
theorem B498917 : Blo 330750 498917 := bbase (se 4 (by rfl) ⟨46773, by rfl⟩ : syracuseStep 498917 = 93547) (by norm_num)
theorem B1121525 : Blo 330750 1121525 := bbase (se 5 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 1121525 = 105143) (by norm_num)
theorem B498941 : Blo 330750 498941 := bbase (se 3 (by rfl) ⟨93551, by rfl⟩ : syracuseStep 498941 = 187103) (by norm_num)
theorem B597253 : Blo 330750 597253 := bbase (se 4 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 597253 = 111985) (by norm_num)
theorem B400657 : Blo 330750 400657 := bbase (se 2 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 400657 = 300493) (by norm_num)
theorem B498965 : Blo 330750 498965 := bbase (se 6 (by rfl) ⟨11694, by rfl⟩ : syracuseStep 498965 = 23389) (by norm_num)
theorem B564509 : Blo 330750 564509 := bbase (se 3 (by rfl) ⟨105845, by rfl⟩ : syracuseStep 564509 = 211691) (by norm_num)
theorem B531749 : Blo 330750 531749 := bbase (se 4 (by rfl) ⟨49851, by rfl⟩ : syracuseStep 531749 = 99703) (by norm_num)
theorem B498989 : Blo 330750 498989 := bbase (se 3 (by rfl) ⟨93560, by rfl⟩ : syracuseStep 498989 = 187121) (by norm_num)
theorem B499013 : Blo 330750 499013 := bbase (se 4 (by rfl) ⟨46782, by rfl⟩ : syracuseStep 499013 = 93565) (by norm_num)
theorem B499037 : Blo 330750 499037 := bbase (se 3 (by rfl) ⟨93569, by rfl⟩ : syracuseStep 499037 = 187139) (by norm_num)
theorem B499061 : Blo 330750 499061 := bbase (se 5 (by rfl) ⟨23393, by rfl⟩ : syracuseStep 499061 = 46787) (by norm_num)
theorem B499085 : Blo 330750 499085 := bbase (se 3 (by rfl) ⟨93578, by rfl⟩ : syracuseStep 499085 = 187157) (by norm_num)
theorem B564637 : Blo 330750 564637 := bbase (se 3 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 564637 = 211739) (by norm_num)
theorem B499109 : Blo 330750 499109 := bbase (se 4 (by rfl) ⟨46791, by rfl⟩ : syracuseStep 499109 = 93583) (by norm_num)
theorem B1416629 : Blo 330750 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B499133 : Blo 330750 499133 := bbase (se 3 (by rfl) ⟨93587, by rfl⟩ : syracuseStep 499133 = 187175) (by norm_num)
theorem B597461 : Blo 330750 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B1678805 : Blo 330750 1678805 := bbase (se 7 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 1678805 = 39347) (by norm_num)
theorem B499157 : Blo 330750 499157 := bbase (se 7 (by rfl) ⟨5849, by rfl⟩ : syracuseStep 499157 = 11699) (by norm_num)
theorem B597469 : Blo 330750 597469 := bbase (se 3 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 597469 = 224051) (by norm_num)
theorem B499181 : Blo 330750 499181 := bbase (se 3 (by rfl) ⟨93596, by rfl⟩ : syracuseStep 499181 = 187193) (by norm_num)
theorem B564725 : Blo 330750 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B499205 : Blo 330750 499205 := bbase (se 4 (by rfl) ⟨46800, by rfl⟩ : syracuseStep 499205 = 93601) (by norm_num)
theorem B499229 : Blo 330750 499229 := bbase (se 3 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 499229 = 187211) (by norm_num)
theorem B499253 : Blo 330750 499253 := bbase (se 5 (by rfl) ⟨23402, by rfl⟩ : syracuseStep 499253 = 46805) (by norm_num)
theorem B499277 : Blo 330750 499277 := bbase (se 3 (by rfl) ⟨93614, by rfl⟩ : syracuseStep 499277 = 187229) (by norm_num)
theorem B499301 : Blo 330750 499301 := bbase (se 4 (by rfl) ⟨46809, by rfl⟩ : syracuseStep 499301 = 93619) (by norm_num)
theorem B597613 : Blo 330750 597613 := bbase (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) (by norm_num)
theorem B564853 : Blo 330750 564853 := bbase (se 5 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 564853 = 52955) (by norm_num)
theorem B499325 : Blo 330750 499325 := bbase (se 3 (by rfl) ⟨93623, by rfl⟩ : syracuseStep 499325 = 187247) (by norm_num)
theorem B499349 : Blo 330750 499349 := bbase (se 6 (by rfl) ⟨11703, by rfl⟩ : syracuseStep 499349 = 23407) (by norm_num)
theorem B335521 : Blo 330750 335521 := bbase (se 2 (by rfl) ⟨125820, by rfl⟩ : syracuseStep 335521 = 251641) (by norm_num)
theorem B1121957 : Blo 330750 1121957 := bbase (se 4 (by rfl) ⟨105183, by rfl⟩ : syracuseStep 1121957 = 210367) (by norm_num)
theorem B499373 : Blo 330750 499373 := bbase (se 3 (by rfl) ⟨93632, by rfl⟩ : syracuseStep 499373 = 187265) (by norm_num)
theorem B499397 : Blo 330750 499397 := bbase (se 4 (by rfl) ⟨46818, by rfl⟩ : syracuseStep 499397 = 93637) (by norm_num)
theorem B499421 : Blo 330750 499421 := bbase (se 3 (by rfl) ⟨93641, by rfl⟩ : syracuseStep 499421 = 187283) (by norm_num)
theorem B630517 : Blo 330750 630517 := bbase (se 5 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 630517 = 59111) (by norm_num)
theorem B499445 : Blo 330750 499445 := bbase (se 5 (by rfl) ⟨23411, by rfl⟩ : syracuseStep 499445 = 46823) (by norm_num)
theorem B499469 : Blo 330750 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B499493 : Blo 330750 499493 := bbase (se 4 (by rfl) ⟨46827, by rfl⟩ : syracuseStep 499493 = 93655) (by norm_num)
theorem B499517 : Blo 330750 499517 := bbase (se 3 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 499517 = 187319) (by norm_num)
theorem B499541 : Blo 330750 499541 := bbase (se 9 (by rfl) ⟨1463, by rfl⟩ : syracuseStep 499541 = 2927) (by norm_num)
theorem B499565 : Blo 330750 499565 := bbase (se 3 (by rfl) ⟨93668, by rfl⟩ : syracuseStep 499565 = 187337) (by norm_num)
theorem B761717 : Blo 330750 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B630661 : Blo 330750 630661 := bbase (se 4 (by rfl) ⟨59124, by rfl⟩ : syracuseStep 630661 = 118249) (by norm_num)
theorem B499589 : Blo 330750 499589 := bbase (se 4 (by rfl) ⟨46836, by rfl⟩ : syracuseStep 499589 = 93673) (by norm_num)
theorem B499613 : Blo 330750 499613 := bbase (se 3 (by rfl) ⟨93677, by rfl⟩ : syracuseStep 499613 = 187355) (by norm_num)
theorem B499637 : Blo 330750 499637 := bbase (se 5 (by rfl) ⟨23420, by rfl⟩ : syracuseStep 499637 = 46841) (by norm_num)
theorem B499661 : Blo 330750 499661 := bbase (se 3 (by rfl) ⟨93686, by rfl⟩ : syracuseStep 499661 = 187373) (by norm_num)
theorem B499685 : Blo 330750 499685 := bbase (se 4 (by rfl) ⟨46845, by rfl⟩ : syracuseStep 499685 = 93691) (by norm_num)
theorem B499709 : Blo 330750 499709 := bbase (se 3 (by rfl) ⟨93695, by rfl⟩ : syracuseStep 499709 = 187391) (by norm_num)
theorem B499733 : Blo 330750 499733 := bbase (se 6 (by rfl) ⟨11712, by rfl⟩ : syracuseStep 499733 = 23425) (by norm_num)
theorem B630821 : Blo 330750 630821 := bbase (se 4 (by rfl) ⟨59139, by rfl⟩ : syracuseStep 630821 = 118279) (by norm_num)
theorem B499757 : Blo 330750 499757 := bbase (se 3 (by rfl) ⟨93704, by rfl⟩ : syracuseStep 499757 = 187409) (by norm_num)
theorem B499781 : Blo 330750 499781 := bbase (se 4 (by rfl) ⟨46854, by rfl⟩ : syracuseStep 499781 = 93709) (by norm_num)
theorem B1122389 : Blo 330750 1122389 := bbase (se 8 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 1122389 = 13153) (by norm_num)
theorem B499805 : Blo 330750 499805 := bbase (se 3 (by rfl) ⟨93713, by rfl⟩ : syracuseStep 499805 = 187427) (by norm_num)
theorem B499829 : Blo 330750 499829 := bbase (se 5 (by rfl) ⟨23429, by rfl⟩ : syracuseStep 499829 = 46859) (by norm_num)
theorem B401537 : Blo 330750 401537 := bbase (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) (by norm_num)
theorem B499853 : Blo 330750 499853 := bbase (se 3 (by rfl) ⟨93722, by rfl⟩ : syracuseStep 499853 = 187445) (by norm_num)
theorem B499877 : Blo 330750 499877 := bbase (se 4 (by rfl) ⟨46863, by rfl⟩ : syracuseStep 499877 = 93727) (by norm_num)
theorem B630965 : Blo 330750 630965 := bbase (se 5 (by rfl) ⟨29576, by rfl⟩ : syracuseStep 630965 = 59153) (by norm_num)
theorem B499901 : Blo 330750 499901 := bbase (se 3 (by rfl) ⟨93731, by rfl⟩ : syracuseStep 499901 = 187463) (by norm_num)
theorem B499925 : Blo 330750 499925 := bbase (se 7 (by rfl) ⟨5858, by rfl⟩ : syracuseStep 499925 = 11717) (by norm_num)
theorem B499949 : Blo 330750 499949 := bbase (se 3 (by rfl) ⟨93740, by rfl⟩ : syracuseStep 499949 = 187481) (by norm_num)
theorem B2531573 : Blo 330750 2531573 := bbase (se 5 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 2531573 = 237335) (by norm_num)
theorem B499973 : Blo 330750 499973 := bbase (se 4 (by rfl) ⟨46872, by rfl⟩ : syracuseStep 499973 = 93745) (by norm_num)
theorem B499997 : Blo 330750 499997 := bbase (se 3 (by rfl) ⟨93749, by rfl⟩ : syracuseStep 499997 = 187499) (by norm_num)
theorem B500021 : Blo 330750 500021 := bbase (se 5 (by rfl) ⟨23438, by rfl⟩ : syracuseStep 500021 = 46877) (by norm_num)
theorem B598333 : Blo 330750 598333 := bbase (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) (by norm_num)
theorem B500045 : Blo 330750 500045 := bbase (se 3 (by rfl) ⟨93758, by rfl⟩ : syracuseStep 500045 = 187517) (by norm_num)
theorem B500069 : Blo 330750 500069 := bbase (se 4 (by rfl) ⟨46881, by rfl⟩ : syracuseStep 500069 = 93763) (by norm_num)
theorem B500093 : Blo 330750 500093 := bbase (se 3 (by rfl) ⟨93767, by rfl⟩ : syracuseStep 500093 = 187535) (by norm_num)
theorem B1417621 : Blo 330750 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B598421 : Blo 330750 598421 := bbase (se 6 (by rfl) ⟨14025, by rfl⟩ : syracuseStep 598421 = 28051) (by norm_num)
theorem B500117 : Blo 330750 500117 := bbase (se 6 (by rfl) ⟨11721, by rfl⟩ : syracuseStep 500117 = 23443) (by norm_num)
theorem B500141 : Blo 330750 500141 := bbase (se 3 (by rfl) ⟨93776, by rfl⟩ : syracuseStep 500141 = 187553) (by norm_num)
theorem B500165 : Blo 330750 500165 := bbase (se 4 (by rfl) ⟨46890, by rfl⟩ : syracuseStep 500165 = 93781) (by norm_num)
theorem B631253 : Blo 330750 631253 := bbase (se 7 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 631253 = 14795) (by norm_num)
theorem B500189 : Blo 330750 500189 := bbase (se 3 (by rfl) ⟨93785, by rfl⟩ : syracuseStep 500189 = 187571) (by norm_num)
theorem B500213 : Blo 330750 500213 := bbase (se 5 (by rfl) ⟨23447, by rfl⟩ : syracuseStep 500213 = 46895) (by norm_num)
theorem B1122821 : Blo 330750 1122821 := bbase (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) (by norm_num)
theorem B500237 : Blo 330750 500237 := bbase (se 3 (by rfl) ⟨93794, by rfl⟩ : syracuseStep 500237 = 187589) (by norm_num)
theorem B500261 : Blo 330750 500261 := bbase (se 4 (by rfl) ⟨46899, by rfl⟩ : syracuseStep 500261 = 93799) (by norm_num)
theorem B500285 : Blo 330750 500285 := bbase (se 3 (by rfl) ⟨93803, by rfl⟩ : syracuseStep 500285 = 187607) (by norm_num)
theorem B500309 : Blo 330750 500309 := bbase (se 8 (by rfl) ⟨2931, by rfl⟩ : syracuseStep 500309 = 5863) (by norm_num)
theorem B631405 : Blo 330750 631405 := bbase (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) (by norm_num)
theorem B500333 : Blo 330750 500333 := bbase (se 3 (by rfl) ⟨93812, by rfl⟩ : syracuseStep 500333 = 187625) (by norm_num)
theorem B402041 : Blo 330750 402041 := bbase (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) (by norm_num)
theorem B500357 : Blo 330750 500357 := bbase (se 4 (by rfl) ⟨46908, by rfl⟩ : syracuseStep 500357 = 93817) (by norm_num)
theorem B500381 : Blo 330750 500381 := bbase (se 3 (by rfl) ⟨93821, by rfl⟩ : syracuseStep 500381 = 187643) (by norm_num)
theorem B402089 : Blo 330750 402089 := bbase (se 2 (by rfl) ⟨150783, by rfl⟩ : syracuseStep 402089 = 301567) (by norm_num)
theorem B500405 : Blo 330750 500405 := bbase (se 5 (by rfl) ⟨23456, by rfl⟩ : syracuseStep 500405 = 46913) (by norm_num)
theorem B500429 : Blo 330750 500429 := bbase (se 3 (by rfl) ⟨93830, by rfl⟩ : syracuseStep 500429 = 187661) (by norm_num)
theorem B1680101 : Blo 330750 1680101 := bbase (se 4 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 1680101 = 315019) (by norm_num)
theorem B500453 : Blo 330750 500453 := bbase (se 4 (by rfl) ⟨46917, by rfl⟩ : syracuseStep 500453 = 93835) (by norm_num)
theorem B500477 : Blo 330750 500477 := bbase (se 3 (by rfl) ⟨93839, by rfl⟩ : syracuseStep 500477 = 187679) (by norm_num)
theorem B533261 : Blo 330750 533261 := bbase (se 3 (by rfl) ⟨99986, by rfl⟩ : syracuseStep 533261 = 199973) (by norm_num)
theorem B2564885 : Blo 330750 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B500501 : Blo 330750 500501 := bbase (se 6 (by rfl) ⟨11730, by rfl⟩ : syracuseStep 500501 = 23461) (by norm_num)
theorem B500525 : Blo 330750 500525 := bbase (se 3 (by rfl) ⟨93848, by rfl⟩ : syracuseStep 500525 = 187697) (by norm_num)
theorem B598853 : Blo 330750 598853 := bbase (se 4 (by rfl) ⟨56142, by rfl⟩ : syracuseStep 598853 = 112285) (by norm_num)
theorem B500549 : Blo 330750 500549 := bbase (se 4 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 500549 = 93853) (by norm_num)
theorem B500573 : Blo 330750 500573 := bbase (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) (by norm_num)
theorem B500597 : Blo 330750 500597 := bbase (se 5 (by rfl) ⟨23465, by rfl⟩ : syracuseStep 500597 = 46931) (by norm_num)
theorem B533389 : Blo 330750 533389 := bbase (se 3 (by rfl) ⟨100010, by rfl⟩ : syracuseStep 533389 = 200021) (by norm_num)
theorem B500621 : Blo 330750 500621 := bbase (se 3 (by rfl) ⟨93866, by rfl⟩ : syracuseStep 500621 = 187733) (by norm_num)
theorem B631709 : Blo 330750 631709 := bbase (se 3 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 631709 = 236891) (by norm_num)
theorem B500645 : Blo 330750 500645 := bbase (se 4 (by rfl) ⟨46935, by rfl⟩ : syracuseStep 500645 = 93871) (by norm_num)
theorem B1123253 : Blo 330750 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B500669 : Blo 330750 500669 := bbase (se 3 (by rfl) ⟨93875, by rfl⟩ : syracuseStep 500669 = 187751) (by norm_num)
theorem B598997 : Blo 330750 598997 := bbase (se 7 (by rfl) ⟨7019, by rfl⟩ : syracuseStep 598997 = 14039) (by norm_num)
theorem B500693 : Blo 330750 500693 := bbase (se 7 (by rfl) ⟨5867, by rfl⟩ : syracuseStep 500693 = 11735) (by norm_num)
theorem B500717 : Blo 330750 500717 := bbase (se 3 (by rfl) ⟨93884, by rfl⟩ : syracuseStep 500717 = 187769) (by norm_num)
theorem B500741 : Blo 330750 500741 := bbase (se 4 (by rfl) ⟨46944, by rfl⟩ : syracuseStep 500741 = 93889) (by norm_num)
theorem B500765 : Blo 330750 500765 := bbase (se 3 (by rfl) ⟨93893, by rfl⟩ : syracuseStep 500765 = 187787) (by norm_num)
theorem B795701 : Blo 330750 795701 := bbase (se 5 (by rfl) ⟨37298, by rfl⟩ : syracuseStep 795701 = 74597) (by norm_num)
theorem B500789 : Blo 330750 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B500813 : Blo 330750 500813 := bbase (se 3 (by rfl) ⟨93902, by rfl⟩ : syracuseStep 500813 = 187805) (by norm_num)
theorem B500837 : Blo 330750 500837 := bbase (se 4 (by rfl) ⟨46953, by rfl⟩ : syracuseStep 500837 = 93907) (by norm_num)
theorem B500861 : Blo 330750 500861 := bbase (se 3 (by rfl) ⟨93911, by rfl⟩ : syracuseStep 500861 = 187823) (by norm_num)
theorem B500885 : Blo 330750 500885 := bbase (se 6 (by rfl) ⟨11739, by rfl⟩ : syracuseStep 500885 = 23479) (by norm_num)
theorem B599213 : Blo 330750 599213 := bbase (se 3 (by rfl) ⟨112352, by rfl⟩ : syracuseStep 599213 = 224705) (by norm_num)
theorem B500909 : Blo 330750 500909 := bbase (se 3 (by rfl) ⟨93920, by rfl⟩ : syracuseStep 500909 = 187841) (by norm_num)
theorem B500933 : Blo 330750 500933 := bbase (se 4 (by rfl) ⟨46962, by rfl⟩ : syracuseStep 500933 = 93925) (by norm_num)
theorem B500957 : Blo 330750 500957 := bbase (se 3 (by rfl) ⟨93929, by rfl⟩ : syracuseStep 500957 = 187859) (by norm_num)
theorem B1352933 : Blo 330750 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B500981 : Blo 330750 500981 := bbase (se 5 (by rfl) ⟨23483, by rfl⟩ : syracuseStep 500981 = 46967) (by norm_num)
theorem B501005 : Blo 330750 501005 := bbase (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) (by norm_num)
theorem B501029 : Blo 330750 501029 := bbase (se 4 (by rfl) ⟨46971, by rfl⟩ : syracuseStep 501029 = 93943) (by norm_num)
theorem B501053 : Blo 330750 501053 := bbase (se 3 (by rfl) ⟨93947, by rfl⟩ : syracuseStep 501053 = 187895) (by norm_num)
theorem B501077 : Blo 330750 501077 := bbase (se 12 (by rfl) ⟨183, by rfl⟩ : syracuseStep 501077 = 367) (by norm_num)
theorem B1123685 : Blo 330750 1123685 := bbase (se 4 (by rfl) ⟨105345, by rfl⟩ : syracuseStep 1123685 = 210691) (by norm_num)
theorem B501101 : Blo 330750 501101 := bbase (se 3 (by rfl) ⟨93956, by rfl⟩ : syracuseStep 501101 = 187913) (by norm_num)
theorem B501125 : Blo 330750 501125 := bbase (se 4 (by rfl) ⟨46980, by rfl⟩ : syracuseStep 501125 = 93961) (by norm_num)
theorem B501149 : Blo 330750 501149 := bbase (se 3 (by rfl) ⟨93965, by rfl⟩ : syracuseStep 501149 = 187931) (by norm_num)
theorem B501173 : Blo 330750 501173 := bbase (se 5 (by rfl) ⟨23492, by rfl⟩ : syracuseStep 501173 = 46985) (by norm_num)
theorem B501197 : Blo 330750 501197 := bbase (se 3 (by rfl) ⟨93974, by rfl⟩ : syracuseStep 501197 = 187949) (by norm_num)
theorem B4793813 : Blo 330750 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B2139605 : Blo 330750 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B501221 : Blo 330750 501221 := bbase (se 4 (by rfl) ⟨46989, by rfl⟩ : syracuseStep 501221 = 93979) (by norm_num)
theorem B501245 : Blo 330750 501245 := bbase (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) (by norm_num)
theorem B763397 : Blo 330750 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B501269 : Blo 330750 501269 := bbase (se 6 (by rfl) ⟨11748, by rfl⟩ : syracuseStep 501269 = 23497) (by norm_num)
theorem B501293 : Blo 330750 501293 := bbase (se 3 (by rfl) ⟨93992, by rfl⟩ : syracuseStep 501293 = 187985) (by norm_num)
theorem B501317 : Blo 330750 501317 := bbase (se 4 (by rfl) ⟨46998, by rfl⟩ : syracuseStep 501317 = 93997) (by norm_num)
theorem B501341 : Blo 330750 501341 := bbase (se 3 (by rfl) ⟨94001, by rfl⟩ : syracuseStep 501341 = 188003) (by norm_num)
theorem B501365 : Blo 330750 501365 := bbase (se 5 (by rfl) ⟨23501, by rfl⟩ : syracuseStep 501365 = 47003) (by norm_num)
theorem B632461 : Blo 330750 632461 := bbase (se 3 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 632461 = 237173) (by norm_num)
theorem B501389 : Blo 330750 501389 := bbase (se 3 (by rfl) ⟨94010, by rfl⟩ : syracuseStep 501389 = 188021) (by norm_num)
theorem B501413 : Blo 330750 501413 := bbase (se 4 (by rfl) ⟨47007, by rfl⟩ : syracuseStep 501413 = 94015) (by norm_num)
theorem B501437 : Blo 330750 501437 := bbase (se 3 (by rfl) ⟨94019, by rfl⟩ : syracuseStep 501437 = 188039) (by norm_num)
theorem B501461 : Blo 330750 501461 := bbase (se 7 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 501461 = 11753) (by norm_num)
theorem B501485 : Blo 330750 501485 := bbase (se 3 (by rfl) ⟨94028, by rfl⟩ : syracuseStep 501485 = 188057) (by norm_num)
theorem B501509 : Blo 330750 501509 := bbase (se 4 (by rfl) ⟨47016, by rfl⟩ : syracuseStep 501509 = 94033) (by norm_num)
theorem B1124117 : Blo 330750 1124117 := bbase (se 6 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 1124117 = 52693) (by norm_num)
theorem B632605 : Blo 330750 632605 := bbase (se 3 (by rfl) ⟨118613, by rfl⟩ : syracuseStep 632605 = 237227) (by norm_num)
theorem B501533 : Blo 330750 501533 := bbase (se 3 (by rfl) ⟨94037, by rfl⟩ : syracuseStep 501533 = 188075) (by norm_num)
theorem B501557 : Blo 330750 501557 := bbase (se 5 (by rfl) ⟨23510, by rfl⟩ : syracuseStep 501557 = 47021) (by norm_num)
theorem B501581 : Blo 330750 501581 := bbase (se 3 (by rfl) ⟨94046, by rfl⟩ : syracuseStep 501581 = 188093) (by norm_num)
theorem B501605 : Blo 330750 501605 := bbase (se 4 (by rfl) ⟨47025, by rfl⟩ : syracuseStep 501605 = 94051) (by norm_num)
theorem B501629 : Blo 330750 501629 := bbase (se 3 (by rfl) ⟨94055, by rfl⟩ : syracuseStep 501629 = 188111) (by norm_num)
theorem B501653 : Blo 330750 501653 := bbase (se 6 (by rfl) ⟨11757, by rfl⟩ : syracuseStep 501653 = 23515) (by norm_num)
theorem B501677 : Blo 330750 501677 := bbase (se 3 (by rfl) ⟨94064, by rfl⟩ : syracuseStep 501677 = 188129) (by norm_num)
theorem B632765 : Blo 330750 632765 := bbase (se 3 (by rfl) ⟨118643, by rfl⟩ : syracuseStep 632765 = 237287) (by norm_num)
theorem B600005 : Blo 330750 600005 := bbase (se 4 (by rfl) ⟨56250, by rfl⟩ : syracuseStep 600005 = 112501) (by norm_num)
theorem B501701 : Blo 330750 501701 := bbase (se 4 (by rfl) ⟨47034, by rfl⟩ : syracuseStep 501701 = 94069) (by norm_num)
theorem B501725 : Blo 330750 501725 := bbase (se 3 (by rfl) ⟨94073, by rfl⟩ : syracuseStep 501725 = 188147) (by norm_num)
theorem B337889 : Blo 330750 337889 := bbase (se 2 (by rfl) ⟨126708, by rfl⟩ : syracuseStep 337889 = 253417) (by norm_num)
theorem B1681397 : Blo 330750 1681397 := bbase (se 5 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 1681397 = 157631) (by norm_num)
theorem B501749 : Blo 330750 501749 := bbase (se 5 (by rfl) ⟨23519, by rfl⟩ : syracuseStep 501749 = 47039) (by norm_num)
theorem B501773 : Blo 330750 501773 := bbase (se 3 (by rfl) ⟨94082, by rfl⟩ : syracuseStep 501773 = 188165) (by norm_num)
theorem B501797 : Blo 330750 501797 := bbase (se 4 (by rfl) ⟨47043, by rfl⟩ : syracuseStep 501797 = 94087) (by norm_num)
theorem B501821 : Blo 330750 501821 := bbase (se 3 (by rfl) ⟨94091, by rfl⟩ : syracuseStep 501821 = 188183) (by norm_num)
theorem B632909 : Blo 330750 632909 := bbase (se 3 (by rfl) ⟨118670, by rfl⟩ : syracuseStep 632909 = 237341) (by norm_num)
theorem B501845 : Blo 330750 501845 := bbase (se 8 (by rfl) ⟨2940, by rfl⟩ : syracuseStep 501845 = 5881) (by norm_num)
theorem B501869 : Blo 330750 501869 := bbase (se 3 (by rfl) ⟨94100, by rfl⟩ : syracuseStep 501869 = 188201) (by norm_num)
theorem B501893 : Blo 330750 501893 := bbase (se 4 (by rfl) ⟨47052, by rfl⟩ : syracuseStep 501893 = 94105) (by norm_num)
theorem B501917 : Blo 330750 501917 := bbase (se 3 (by rfl) ⟨94109, by rfl⟩ : syracuseStep 501917 = 188219) (by norm_num)
theorem B600229 : Blo 330750 600229 := bbase (se 4 (by rfl) ⟨56271, by rfl⟩ : syracuseStep 600229 = 112543) (by norm_num)
theorem B501941 : Blo 330750 501941 := bbase (se 5 (by rfl) ⟨23528, by rfl⟩ : syracuseStep 501941 = 47057) (by norm_num)
theorem B1124549 : Blo 330750 1124549 := bbase (se 4 (by rfl) ⟨105426, by rfl⟩ : syracuseStep 1124549 = 210853) (by norm_num)
theorem B501965 : Blo 330750 501965 := bbase (se 3 (by rfl) ⟨94118, by rfl⟩ : syracuseStep 501965 = 188237) (by norm_num)
theorem B501989 : Blo 330750 501989 := bbase (se 4 (by rfl) ⟨47061, by rfl⟩ : syracuseStep 501989 = 94123) (by norm_num)
theorem B534773 : Blo 330750 534773 := bbase (se 5 (by rfl) ⟨25067, by rfl⟩ : syracuseStep 534773 = 50135) (by norm_num)
theorem B502013 : Blo 330750 502013 := bbase (se 3 (by rfl) ⟨94127, by rfl⟩ : syracuseStep 502013 = 188255) (by norm_num)
theorem B502037 : Blo 330750 502037 := bbase (se 6 (by rfl) ⟨11766, by rfl⟩ : syracuseStep 502037 = 23533) (by norm_num)
theorem B502061 : Blo 330750 502061 := bbase (se 3 (by rfl) ⟨94136, by rfl⟩ : syracuseStep 502061 = 188273) (by norm_num)
theorem B502085 : Blo 330750 502085 := bbase (se 4 (by rfl) ⟨47070, by rfl⟩ : syracuseStep 502085 = 94141) (by norm_num)
theorem B502109 : Blo 330750 502109 := bbase (se 3 (by rfl) ⟨94145, by rfl⟩ : syracuseStep 502109 = 188291) (by norm_num)
theorem B633197 : Blo 330750 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B633349 : Blo 330750 633349 := bbase (se 4 (by rfl) ⟨59376, by rfl⟩ : syracuseStep 633349 = 118753) (by norm_num)
theorem B2599445 : Blo 330750 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B338509 : Blo 330750 338509 := bbase (se 3 (by rfl) ⟨63470, by rfl⟩ : syracuseStep 338509 = 126941) (by norm_num)
theorem B1092197 : Blo 330750 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B1124981 : Blo 330750 1124981 := bbase (se 5 (by rfl) ⟨52733, by rfl⟩ : syracuseStep 1124981 = 105467) (by norm_num)
theorem B633653 : Blo 330750 633653 := bbase (se 5 (by rfl) ⟨29702, by rfl⟩ : syracuseStep 633653 = 59405) (by norm_num)
theorem B797701 : Blo 330750 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B568333 : Blo 330750 568333 := bbase (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) (by norm_num)
theorem B1125413 : Blo 330750 1125413 := bbase (se 4 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 1125413 = 211015) (by norm_num)
theorem B797845 : Blo 330750 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B535709 : Blo 330750 535709 := bbase (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) (by norm_num)
theorem B339109 : Blo 330750 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B928997 : Blo 330750 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B1682693 : Blo 330750 1682693 := bbase (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) (by norm_num)
theorem B372109 : Blo 330750 372109 := bbase (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) (by norm_num)
theorem B372145 : Blo 330750 372145 := bbase (se 2 (by rfl) ⟨139554, by rfl⟩ : syracuseStep 372145 = 279109) (by norm_num)
theorem B372181 : Blo 330750 372181 := bbase (se 7 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 372181 = 8723) (by norm_num)
theorem B1256917 : Blo 330750 1256917 := bbase (se 7 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 1256917 = 29459) (by norm_num)
theorem B1125845 : Blo 330750 1125845 := bbase (se 7 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 1125845 = 26387) (by norm_num)
theorem B372217 : Blo 330750 372217 := bbase (se 2 (by rfl) ⟨139581, by rfl⟩ : syracuseStep 372217 = 279163) (by norm_num)
theorem B372253 : Blo 330750 372253 := bbase (se 3 (by rfl) ⟨69797, by rfl⟩ : syracuseStep 372253 = 139595) (by norm_num)
theorem B634405 : Blo 330750 634405 := bbase (se 4 (by rfl) ⟨59475, by rfl⟩ : syracuseStep 634405 = 118951) (by norm_num)
theorem B372289 : Blo 330750 372289 := bbase (se 2 (by rfl) ⟨139608, by rfl⟩ : syracuseStep 372289 = 279217) (by norm_num)
theorem B831061 : Blo 330750 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B372325 : Blo 330750 372325 := bbase (se 4 (by rfl) ⟨34905, by rfl⟩ : syracuseStep 372325 = 69811) (by norm_num)
theorem B568949 : Blo 330750 568949 := bbase (se 5 (by rfl) ⟨26669, by rfl⟩ : syracuseStep 568949 = 53339) (by norm_num)
theorem B372361 : Blo 330750 372361 := bbase (se 2 (by rfl) ⟨139635, by rfl⟩ : syracuseStep 372361 = 279271) (by norm_num)
theorem B372397 : Blo 330750 372397 := bbase (se 3 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 372397 = 139649) (by norm_num)
theorem B634549 : Blo 330750 634549 := bbase (se 5 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 634549 = 59489) (by norm_num)
theorem B372433 : Blo 330750 372433 := bbase (se 2 (by rfl) ⟨139662, by rfl⟩ : syracuseStep 372433 = 279325) (by norm_num)
theorem B765677 : Blo 330750 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B372469 : Blo 330750 372469 := bbase (se 5 (by rfl) ⟨17459, by rfl⟩ : syracuseStep 372469 = 34919) (by norm_num)
theorem B798461 : Blo 330750 798461 := bbase (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) (by norm_num)
theorem B1257221 : Blo 330750 1257221 := bbase (se 4 (by rfl) ⟨117864, by rfl⟩ : syracuseStep 1257221 = 235729) (by norm_num)
theorem B372505 : Blo 330750 372505 := bbase (se 2 (by rfl) ⟨139689, by rfl⟩ : syracuseStep 372505 = 279379) (by norm_num)
theorem B372541 : Blo 330750 372541 := bbase (se 3 (by rfl) ⟨69851, by rfl⟩ : syracuseStep 372541 = 139703) (by norm_num)
theorem B634709 : Blo 330750 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B372577 : Blo 330750 372577 := bbase (se 2 (by rfl) ⟨139716, by rfl⟩ : syracuseStep 372577 = 279433) (by norm_num)
theorem B896885 : Blo 330750 896885 := bbase (se 5 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 896885 = 84083) (by norm_num)
theorem B372613 : Blo 330750 372613 := bbase (se 4 (by rfl) ⟨34932, by rfl⟩ : syracuseStep 372613 = 69865) (by norm_num)
theorem B1126277 : Blo 330750 1126277 := bbase (se 4 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 1126277 = 211177) (by norm_num)
theorem B372649 : Blo 330750 372649 := bbase (se 2 (by rfl) ⟨139743, by rfl⟩ : syracuseStep 372649 = 279487) (by norm_num)
theorem B372685 : Blo 330750 372685 := bbase (se 3 (by rfl) ⟨69878, by rfl⟩ : syracuseStep 372685 = 139757) (by norm_num)
theorem B634853 : Blo 330750 634853 := bbase (se 4 (by rfl) ⟨59517, by rfl⟩ : syracuseStep 634853 = 119035) (by norm_num)
theorem B372721 : Blo 330750 372721 := bbase (se 2 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 372721 = 279541) (by norm_num)
theorem B471037 : Blo 330750 471037 := bbase (se 3 (by rfl) ⟨88319, by rfl⟩ : syracuseStep 471037 = 176639) (by norm_num)
theorem B372757 : Blo 330750 372757 := bbase (se 6 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 372757 = 17473) (by norm_num)
theorem B372793 : Blo 330750 372793 := bbase (se 2 (by rfl) ⟨139797, by rfl⟩ : syracuseStep 372793 = 279595) (by norm_num)
theorem B798797 : Blo 330750 798797 := bbase (se 3 (by rfl) ⟨149774, by rfl⟩ : syracuseStep 798797 = 299549) (by norm_num)
theorem B372829 : Blo 330750 372829 := bbase (se 3 (by rfl) ⟨69905, by rfl⟩ : syracuseStep 372829 = 139811) (by norm_num)
theorem B372865 : Blo 330750 372865 := bbase (se 2 (by rfl) ⟨139824, by rfl⟩ : syracuseStep 372865 = 279649) (by norm_num)
theorem B372901 : Blo 330750 372901 := bbase (se 4 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 372901 = 69919) (by norm_num)
theorem B798893 : Blo 330750 798893 := bbase (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) (by norm_num)
theorem B372937 : Blo 330750 372937 := bbase (se 2 (by rfl) ⟨139851, by rfl⟩ : syracuseStep 372937 = 279703) (by norm_num)
theorem B471253 : Blo 330750 471253 := bbase (se 7 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 471253 = 11045) (by norm_num)
theorem B2699477 : Blo 330750 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B372973 : Blo 330750 372973 := bbase (se 3 (by rfl) ⟨69932, by rfl⟩ : syracuseStep 372973 = 139865) (by norm_num)
theorem B635141 : Blo 330750 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B373009 : Blo 330750 373009 := bbase (se 2 (by rfl) ⟨139878, by rfl⟩ : syracuseStep 373009 = 279757) (by norm_num)
theorem B373045 : Blo 330750 373045 := bbase (se 5 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 373045 = 34973) (by norm_num)
theorem B1126709 : Blo 330750 1126709 := bbase (se 5 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 1126709 = 105629) (by norm_num)
theorem B373081 : Blo 330750 373081 := bbase (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) (by norm_num)
theorem B799085 : Blo 330750 799085 := bbase (se 3 (by rfl) ⟨149828, by rfl⟩ : syracuseStep 799085 = 299657) (by norm_num)
theorem B373117 : Blo 330750 373117 := bbase (se 3 (by rfl) ⟨69959, by rfl⟩ : syracuseStep 373117 = 139919) (by norm_num)
theorem B635293 : Blo 330750 635293 := bbase (se 3 (by rfl) ⟨119117, by rfl⟩ : syracuseStep 635293 = 238235) (by norm_num)
theorem B373153 : Blo 330750 373153 := bbase (se 2 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 373153 = 279865) (by norm_num)
theorem B373189 : Blo 330750 373189 := bbase (se 4 (by rfl) ⟨34986, by rfl⟩ : syracuseStep 373189 = 69973) (by norm_num)
theorem B1061333 : Blo 330750 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B373225 : Blo 330750 373225 := bbase (se 2 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 373225 = 279919) (by norm_num)
theorem B373261 : Blo 330750 373261 := bbase (se 3 (by rfl) ⟨69986, by rfl⟩ : syracuseStep 373261 = 139973) (by norm_num)
theorem B1683989 : Blo 330750 1683989 := bbase (se 6 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 1683989 = 78937) (by norm_num)
theorem B373297 : Blo 330750 373297 := bbase (se 2 (by rfl) ⟨139986, by rfl⟩ : syracuseStep 373297 = 279973) (by norm_num)
theorem B471629 : Blo 330750 471629 := bbase (se 3 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 471629 = 176861) (by norm_num)
theorem B373333 : Blo 330750 373333 := bbase (se 8 (by rfl) ⟨2187, by rfl⟩ : syracuseStep 373333 = 4375) (by norm_num)
theorem B373369 : Blo 330750 373369 := bbase (se 2 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 373369 = 280027) (by norm_num)
theorem B373405 : Blo 330750 373405 := bbase (se 3 (by rfl) ⟨70013, by rfl⟩ : syracuseStep 373405 = 140027) (by norm_num)
theorem B373441 : Blo 330750 373441 := bbase (se 2 (by rfl) ⟨140040, by rfl⟩ : syracuseStep 373441 = 280081) (by norm_num)
theorem B373477 : Blo 330750 373477 := bbase (se 4 (by rfl) ⟨35013, by rfl⟩ : syracuseStep 373477 = 70027) (by norm_num)
theorem B1127141 : Blo 330750 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B373513 : Blo 330750 373513 := bbase (se 2 (by rfl) ⟨140067, by rfl⟩ : syracuseStep 373513 = 280135) (by norm_num)
theorem B373549 : Blo 330750 373549 := bbase (se 3 (by rfl) ⟨70040, by rfl⟩ : syracuseStep 373549 = 140081) (by norm_num)
theorem B373585 : Blo 330750 373585 := bbase (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) (by norm_num)
theorem B1192805 : Blo 330750 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B373621 : Blo 330750 373621 := bbase (se 5 (by rfl) ⟨17513, by rfl⟩ : syracuseStep 373621 = 35027) (by norm_num)
theorem B373657 : Blo 330750 373657 := bbase (se 2 (by rfl) ⟨140121, by rfl⟩ : syracuseStep 373657 = 280243) (by norm_num)
theorem B373693 : Blo 330750 373693 := bbase (se 3 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 373693 = 140135) (by norm_num)
theorem B1029077 : Blo 330750 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B373729 : Blo 330750 373729 := bbase (se 2 (by rfl) ⟨140148, by rfl⟩ : syracuseStep 373729 = 280297) (by norm_num)
theorem B373765 : Blo 330750 373765 := bbase (se 4 (by rfl) ⟨35040, by rfl⟩ : syracuseStep 373765 = 70081) (by norm_num)
theorem B373801 : Blo 330750 373801 := bbase (se 2 (by rfl) ⟨140175, by rfl⟩ : syracuseStep 373801 = 280351) (by norm_num)
theorem B373837 : Blo 330750 373837 := bbase (se 3 (by rfl) ⟨70094, by rfl⟩ : syracuseStep 373837 = 140189) (by norm_num)
theorem B373873 : Blo 330750 373873 := bbase (se 2 (by rfl) ⟨140202, by rfl⟩ : syracuseStep 373873 = 280405) (by norm_num)
theorem B1193077 : Blo 330750 1193077 := bbase (se 5 (by rfl) ⟨55925, by rfl⟩ : syracuseStep 1193077 = 111851) (by norm_num)
theorem B373909 : Blo 330750 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B1127573 : Blo 330750 1127573 := bbase (se 6 (by rfl) ⟨26427, by rfl⟩ : syracuseStep 1127573 = 52855) (by norm_num)
theorem B373945 : Blo 330750 373945 := bbase (se 2 (by rfl) ⟨140229, by rfl⟩ : syracuseStep 373945 = 280459) (by norm_num)
theorem B373981 : Blo 330750 373981 := bbase (se 3 (by rfl) ⟨70121, by rfl⟩ : syracuseStep 373981 = 140243) (by norm_num)
theorem B374017 : Blo 330750 374017 := bbase (se 2 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 374017 = 280513) (by norm_num)
theorem B1193237 : Blo 330750 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B374053 : Blo 330750 374053 := bbase (se 4 (by rfl) ⟨35067, by rfl⟩ : syracuseStep 374053 = 70135) (by norm_num)
theorem B1422629 : Blo 330750 1422629 := bbase (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) (by norm_num)
theorem B374089 : Blo 330750 374089 := bbase (se 2 (by rfl) ⟨140283, by rfl⟩ : syracuseStep 374089 = 280567) (by norm_num)
theorem B374125 : Blo 330750 374125 := bbase (se 3 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 374125 = 140297) (by norm_num)
theorem B374161 : Blo 330750 374161 := bbase (se 2 (by rfl) ⟨140310, by rfl⟩ : syracuseStep 374161 = 280621) (by norm_num)
theorem B374197 : Blo 330750 374197 := bbase (se 5 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 374197 = 35081) (by norm_num)
theorem B374233 : Blo 330750 374233 := bbase (se 2 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 374233 = 280675) (by norm_num)
theorem B800237 : Blo 330750 800237 := bbase (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) (by norm_num)
theorem B374269 : Blo 330750 374269 := bbase (se 3 (by rfl) ⟨70175, by rfl⟩ : syracuseStep 374269 = 140351) (by norm_num)
theorem B374305 : Blo 330750 374305 := bbase (se 2 (by rfl) ⟨140364, by rfl⟩ : syracuseStep 374305 = 280729) (by norm_num)
theorem B374341 : Blo 330750 374341 := bbase (se 4 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 374341 = 70189) (by norm_num)
theorem B1422917 : Blo 330750 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B1128005 : Blo 330750 1128005 := bbase (se 4 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 1128005 = 211501) (by norm_num)
theorem B374377 : Blo 330750 374377 := bbase (se 2 (by rfl) ⟨140391, by rfl⟩ : syracuseStep 374377 = 280783) (by norm_num)
theorem B538253 : Blo 330750 538253 := bbase (se 3 (by rfl) ⟨100922, by rfl⟩ : syracuseStep 538253 = 201845) (by norm_num)
theorem B374413 : Blo 330750 374413 := bbase (se 3 (by rfl) ⟨70202, by rfl⟩ : syracuseStep 374413 = 140405) (by norm_num)
theorem B374449 : Blo 330750 374449 := bbase (se 2 (by rfl) ⟨140418, by rfl⟩ : syracuseStep 374449 = 280837) (by norm_num)
theorem B374485 : Blo 330750 374485 := bbase (se 7 (by rfl) ⟨4388, by rfl⟩ : syracuseStep 374485 = 8777) (by norm_num)
theorem B374521 : Blo 330750 374521 := bbase (se 2 (by rfl) ⟨140445, by rfl⟩ : syracuseStep 374521 = 280891) (by norm_num)
theorem B1062677 : Blo 330750 1062677 := bbase (se 6 (by rfl) ⟨24906, by rfl⟩ : syracuseStep 1062677 = 49813) (by norm_num)
theorem B374557 : Blo 330750 374557 := bbase (se 3 (by rfl) ⟨70229, by rfl⟩ : syracuseStep 374557 = 140459) (by norm_num)
theorem B1685285 : Blo 330750 1685285 := bbase (se 4 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 1685285 = 315991) (by norm_num)
theorem B3094325 : Blo 330750 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B374593 : Blo 330750 374593 := bbase (se 2 (by rfl) ⟨140472, by rfl⟩ : syracuseStep 374593 = 280945) (by norm_num)
theorem B1259333 : Blo 330750 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B374629 : Blo 330750 374629 := bbase (se 4 (by rfl) ⟨35121, by rfl⟩ : syracuseStep 374629 = 70243) (by norm_num)
theorem B374665 : Blo 330750 374665 := bbase (se 2 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 374665 = 280999) (by norm_num)
theorem B374701 : Blo 330750 374701 := bbase (se 3 (by rfl) ⟨70256, by rfl⟩ : syracuseStep 374701 = 140513) (by norm_num)
theorem B505781 : Blo 330750 505781 := bbase (se 5 (by rfl) ⟨23708, by rfl⟩ : syracuseStep 505781 = 47417) (by norm_num)
theorem B374737 : Blo 330750 374737 := bbase (se 2 (by rfl) ⟨140526, by rfl⟩ : syracuseStep 374737 = 281053) (by norm_num)
theorem B473053 : Blo 330750 473053 := bbase (se 3 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 473053 = 177395) (by norm_num)
theorem B374773 : Blo 330750 374773 := bbase (se 5 (by rfl) ⟨17567, by rfl⟩ : syracuseStep 374773 = 35135) (by norm_num)
theorem B1128437 : Blo 330750 1128437 := bbase (se 5 (by rfl) ⟨52895, by rfl⟩ : syracuseStep 1128437 = 105791) (by norm_num)
theorem B374809 : Blo 330750 374809 := bbase (se 2 (by rfl) ⟨140553, by rfl⟩ : syracuseStep 374809 = 281107) (by norm_num)
theorem B374845 : Blo 330750 374845 := bbase (se 3 (by rfl) ⟨70283, by rfl⟩ : syracuseStep 374845 = 140567) (by norm_num)
theorem B374881 : Blo 330750 374881 := bbase (se 2 (by rfl) ⟨140580, by rfl⟩ : syracuseStep 374881 = 281161) (by norm_num)
theorem B1259621 : Blo 330750 1259621 := bbase (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) (by norm_num)
theorem B374917 : Blo 330750 374917 := bbase (se 4 (by rfl) ⟨35148, by rfl⟩ : syracuseStep 374917 = 70297) (by norm_num)
theorem B374953 : Blo 330750 374953 := bbase (se 2 (by rfl) ⟨140607, by rfl⟩ : syracuseStep 374953 = 281215) (by norm_num)
theorem B374989 : Blo 330750 374989 := bbase (se 3 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 374989 = 140621) (by norm_num)
theorem B375025 : Blo 330750 375025 := bbase (se 2 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 375025 = 281269) (by norm_num)
theorem B375061 : Blo 330750 375061 := bbase (se 6 (by rfl) ⟨8790, by rfl⟩ : syracuseStep 375061 = 17581) (by norm_num)
theorem B604445 : Blo 330750 604445 := bbase (se 3 (by rfl) ⟨113333, by rfl⟩ : syracuseStep 604445 = 226667) (by norm_num)
theorem B1423669 : Blo 330750 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B375097 : Blo 330750 375097 := bbase (se 2 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 375097 = 281323) (by norm_num)
theorem B375133 : Blo 330750 375133 := bbase (se 3 (by rfl) ⟨70337, by rfl⟩ : syracuseStep 375133 = 140675) (by norm_num)
theorem B375169 : Blo 330750 375169 := bbase (se 2 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 375169 = 281377) (by norm_num)
theorem B375205 : Blo 330750 375205 := bbase (se 4 (by rfl) ⟨35175, by rfl⟩ : syracuseStep 375205 = 70351) (by norm_num)
theorem B1128869 : Blo 330750 1128869 := bbase (se 4 (by rfl) ⟨105831, by rfl⟩ : syracuseStep 1128869 = 211663) (by norm_num)
theorem B375241 : Blo 330750 375241 := bbase (se 2 (by rfl) ⟨140715, by rfl⟩ : syracuseStep 375241 = 281431) (by norm_num)
theorem B375277 : Blo 330750 375277 := bbase (se 3 (by rfl) ⟨70364, by rfl⟩ : syracuseStep 375277 = 140729) (by norm_num)
theorem B375313 : Blo 330750 375313 := bbase (se 2 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 375313 = 281485) (by norm_num)
theorem B473645 : Blo 330750 473645 := bbase (se 3 (by rfl) ⟨88808, by rfl⟩ : syracuseStep 473645 = 177617) (by norm_num)
theorem B375349 : Blo 330750 375349 := bbase (se 5 (by rfl) ⟨17594, by rfl⟩ : syracuseStep 375349 = 35189) (by norm_num)
theorem B375385 : Blo 330750 375385 := bbase (se 2 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 375385 = 281539) (by norm_num)
theorem B473725 : Blo 330750 473725 := bbase (se 3 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 473725 = 177647) (by norm_num)
theorem B375421 : Blo 330750 375421 := bbase (se 3 (by rfl) ⟨70391, by rfl⟩ : syracuseStep 375421 = 140783) (by norm_num)
theorem B375457 : Blo 330750 375457 := bbase (se 2 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 375457 = 281593) (by norm_num)
theorem B375493 : Blo 330750 375493 := bbase (se 4 (by rfl) ⟨35202, by rfl⟩ : syracuseStep 375493 = 70405) (by norm_num)
theorem B375529 : Blo 330750 375529 := bbase (se 2 (by rfl) ⟨140823, by rfl⟩ : syracuseStep 375529 = 281647) (by norm_num)
theorem B473845 : Blo 330750 473845 := bbase (se 5 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 473845 = 44423) (by norm_num)
theorem B375565 : Blo 330750 375565 := bbase (se 3 (by rfl) ⟨70418, by rfl⟩ : syracuseStep 375565 = 140837) (by norm_num)
theorem B375601 : Blo 330750 375601 := bbase (se 2 (by rfl) ⟨140850, by rfl⟩ : syracuseStep 375601 = 281701) (by norm_num)
theorem B3783509 : Blo 330750 3783509 := bbase (se 9 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 3783509 = 22169) (by norm_num)
theorem B473941 : Blo 330750 473941 := bbase (se 9 (by rfl) ⟨1388, by rfl⟩ : syracuseStep 473941 = 2777) (by norm_num)
theorem B375637 : Blo 330750 375637 := bbase (se 9 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 375637 = 2201) (by norm_num)
theorem B1129301 : Blo 330750 1129301 := bbase (se 9 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 1129301 = 6617) (by norm_num)
theorem B375673 : Blo 330750 375673 := bbase (se 2 (by rfl) ⟨140877, by rfl⟩ : syracuseStep 375673 = 281755) (by norm_num)
theorem B375709 : Blo 330750 375709 := bbase (se 3 (by rfl) ⟨70445, by rfl⟩ : syracuseStep 375709 = 140891) (by norm_num)
theorem B375745 : Blo 330750 375745 := bbase (se 2 (by rfl) ⟨140904, by rfl⟩ : syracuseStep 375745 = 281809) (by norm_num)
theorem B1391573 : Blo 330750 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B375781 : Blo 330750 375781 := bbase (se 4 (by rfl) ⟨35229, by rfl⟩ : syracuseStep 375781 = 70459) (by norm_num)
theorem B965621 : Blo 330750 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B375817 : Blo 330750 375817 := bbase (se 2 (by rfl) ⟨140931, by rfl⟩ : syracuseStep 375817 = 281863) (by norm_num)
theorem B1424405 : Blo 330750 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B375853 : Blo 330750 375853 := bbase (se 3 (by rfl) ⟨70472, by rfl⟩ : syracuseStep 375853 = 140945) (by norm_num)
theorem B1686581 : Blo 330750 1686581 := bbase (se 5 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 1686581 = 158117) (by norm_num)
theorem B670789 : Blo 330750 670789 := bbase (se 4 (by rfl) ⟨62886, by rfl⟩ : syracuseStep 670789 = 125773) (by norm_num)
theorem B375889 : Blo 330750 375889 := bbase (se 2 (by rfl) ⟨140958, by rfl⟩ : syracuseStep 375889 = 281917) (by norm_num)
theorem B375925 : Blo 330750 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B375961 : Blo 330750 375961 := bbase (se 2 (by rfl) ⟨140985, by rfl⟩ : syracuseStep 375961 = 281971) (by norm_num)
theorem B375997 : Blo 330750 375997 := bbase (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) (by norm_num)
theorem B1621205 : Blo 330750 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B376033 : Blo 330750 376033 := bbase (se 2 (by rfl) ⟨141012, by rfl⟩ : syracuseStep 376033 = 282025) (by norm_num)
theorem B1260805 : Blo 330750 1260805 := bbase (se 4 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 1260805 = 236401) (by norm_num)
theorem B376069 : Blo 330750 376069 := bbase (se 4 (by rfl) ⟨35256, by rfl⟩ : syracuseStep 376069 = 70513) (by norm_num)
theorem B1129733 : Blo 330750 1129733 := bbase (se 4 (by rfl) ⟨105912, by rfl⟩ : syracuseStep 1129733 = 211825) (by norm_num)
theorem B376105 : Blo 330750 376105 := bbase (se 2 (by rfl) ⟨141039, by rfl⟩ : syracuseStep 376105 = 282079) (by norm_num)
theorem B474437 : Blo 330750 474437 := bbase (se 4 (by rfl) ⟨44478, by rfl⟩ : syracuseStep 474437 = 88957) (by norm_num)
theorem B376141 : Blo 330750 376141 := bbase (se 3 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 376141 = 141053) (by norm_num)
theorem B376177 : Blo 330750 376177 := bbase (se 2 (by rfl) ⟨141066, by rfl⟩ : syracuseStep 376177 = 282133) (by norm_num)
theorem B376213 : Blo 330750 376213 := bbase (se 6 (by rfl) ⟨8817, by rfl⟩ : syracuseStep 376213 = 17635) (by norm_num)
theorem B376249 : Blo 330750 376249 := bbase (se 2 (by rfl) ⟨141093, by rfl⟩ : syracuseStep 376249 = 282187) (by norm_num)
theorem B802237 : Blo 330750 802237 := bbase (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) (by norm_num)
theorem B376285 : Blo 330750 376285 := bbase (se 3 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 376285 = 141107) (by norm_num)
theorem B376321 : Blo 330750 376321 := bbase (se 2 (by rfl) ⟨141120, by rfl⟩ : syracuseStep 376321 = 282241) (by norm_num)
theorem B802333 : Blo 330750 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B376357 : Blo 330750 376357 := bbase (se 4 (by rfl) ⟨35283, by rfl⟩ : syracuseStep 376357 = 70567) (by norm_num)
theorem B1261109 : Blo 330750 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B376393 : Blo 330750 376393 := bbase (se 2 (by rfl) ⟨141147, by rfl⟩ : syracuseStep 376393 = 282295) (by norm_num)
theorem B376429 : Blo 330750 376429 := bbase (se 3 (by rfl) ⟨70580, by rfl⟩ : syracuseStep 376429 = 141161) (by norm_num)
theorem B376465 : Blo 330750 376465 := bbase (se 2 (by rfl) ⟨141174, by rfl⟩ : syracuseStep 376465 = 282349) (by norm_num)
theorem B2014901 : Blo 330750 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B376501 : Blo 330750 376501 := bbase (se 5 (by rfl) ⟨17648, by rfl⟩ : syracuseStep 376501 = 35297) (by norm_num)
theorem B376537 : Blo 330750 376537 := bbase (se 2 (by rfl) ⟨141201, by rfl⟩ : syracuseStep 376537 = 282403) (by norm_num)
theorem B1064677 : Blo 330750 1064677 := bbase (se 4 (by rfl) ⟨99813, by rfl⟩ : syracuseStep 1064677 = 199627) (by norm_num)
theorem B376573 : Blo 330750 376573 := bbase (se 3 (by rfl) ⟨70607, by rfl⟩ : syracuseStep 376573 = 141215) (by norm_num)
theorem B507709 : Blo 330750 507709 := bbase (se 3 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 507709 = 190391) (by norm_num)
theorem B2539349 : Blo 330750 2539349 := bbase (se 9 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 2539349 = 14879) (by norm_num)
theorem B474989 : Blo 330750 474989 := bbase (se 3 (by rfl) ⟨89060, by rfl⟩ : syracuseStep 474989 = 178121) (by norm_num)
theorem B540629 : Blo 330750 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B1196005 : Blo 330750 1196005 := bbase (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) (by norm_num)
theorem B1524005 : Blo 330750 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B1589557 : Blo 330750 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1687877 : Blo 330750 1687877 := bbase (se 4 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 1687877 = 316477) (by norm_num)
theorem B3195413 : Blo 330750 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B475741 : Blo 330750 475741 := bbase (se 3 (by rfl) ⟨89201, by rfl⟩ : syracuseStep 475741 = 178403) (by norm_num)
theorem B803429 : Blo 330750 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B377465 : Blo 330750 377465 := bbase (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) (by norm_num)
theorem B672605 : Blo 330750 672605 := bbase (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) (by norm_num)
theorem B2835445 : Blo 330750 2835445 := bbase (se 5 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 2835445 = 265823) (by norm_num)
theorem B476533 : Blo 330750 476533 := bbase (se 5 (by rfl) ⟨22337, by rfl⟩ : syracuseStep 476533 = 44675) (by norm_num)
theorem B1689173 : Blo 330750 1689173 := bbase (se 8 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 1689173 = 19795) (by norm_num)
theorem B378469 : Blo 330750 378469 := bbase (se 4 (by rfl) ⟨35481, by rfl⟩ : syracuseStep 378469 = 70963) (by norm_num)
theorem B1263221 : Blo 330750 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B837317 : Blo 330750 837317 := bbase (se 4 (by rfl) ⟨78498, by rfl⟩ : syracuseStep 837317 = 156997) (by norm_num)
theorem B1623797 : Blo 330750 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B1263509 : Blo 330750 1263509 := bbase (se 6 (by rfl) ⟨29613, by rfl⟩ : syracuseStep 1263509 = 59227) (by norm_num)
theorem B837661 : Blo 330750 837661 := bbase (se 3 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 837661 = 314123) (by norm_num)
theorem B641053 : Blo 330750 641053 := bbase (se 3 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 641053 = 240395) (by norm_num)
theorem B1198165 : Blo 330750 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B837773 : Blo 330750 837773 := bbase (se 3 (by rfl) ⟨157082, by rfl⟩ : syracuseStep 837773 = 314165) (by norm_num)
theorem B1427701 : Blo 330750 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B837965 : Blo 330750 837965 := bbase (se 3 (by rfl) ⟨157118, by rfl⟩ : syracuseStep 837965 = 314237) (by norm_num)
theorem B1296821 : Blo 330750 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B1198613 : Blo 330750 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B707221 : Blo 330750 707221 := bbase (se 6 (by rfl) ⟨16575, by rfl⟩ : syracuseStep 707221 = 33151) (by norm_num)
theorem B838309 : Blo 330750 838309 := bbase (se 4 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 838309 = 157183) (by norm_num)
theorem B1067701 : Blo 330750 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B838421 : Blo 330750 838421 := bbase (se 6 (by rfl) ⟨19650, by rfl⟩ : syracuseStep 838421 = 39301) (by norm_num)
theorem B1690469 : Blo 330750 1690469 := bbase (se 4 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 1690469 = 316963) (by norm_num)
theorem B2837429 : Blo 330750 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B838613 : Blo 330750 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B2870261 : Blo 330750 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B1264693 : Blo 330750 1264693 := bbase (se 5 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 1264693 = 118565) (by norm_num)
theorem B674893 : Blo 330750 674893 := bbase (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) (by norm_num)
theorem B478325 : Blo 330750 478325 := bbase (se 5 (by rfl) ⟨22421, by rfl⟩ : syracuseStep 478325 = 44843) (by norm_num)
theorem B674941 : Blo 330750 674941 := bbase (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) (by norm_num)
theorem B707717 : Blo 330750 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B2411669 : Blo 330750 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B838957 : Blo 330750 838957 := bbase (se 3 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 838957 = 314609) (by norm_num)
theorem B1264997 : Blo 330750 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B839069 : Blo 330750 839069 := bbase (se 3 (by rfl) ⟨157325, by rfl⟩ : syracuseStep 839069 = 314651) (by norm_num)
theorem B839261 : Blo 330750 839261 := bbase (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) (by norm_num)
theorem B675461 : Blo 330750 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B478909 : Blo 330750 478909 := bbase (se 3 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 478909 = 179591) (by norm_num)
theorem B380641 : Blo 330750 380641 := bbase (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) (by norm_num)
theorem B4771669 : Blo 330750 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B839605 : Blo 330750 839605 := bbase (se 5 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 839605 = 78713) (by norm_num)
theorem B708581 : Blo 330750 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B839717 : Blo 330750 839717 := bbase (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) (by norm_num)
theorem B380965 : Blo 330750 380965 := bbase (se 4 (by rfl) ⟨35715, by rfl⟩ : syracuseStep 380965 = 71431) (by norm_num)
theorem B643133 : Blo 330750 643133 := bbase (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) (by norm_num)
theorem B708725 : Blo 330750 708725 := bbase (se 5 (by rfl) ⟨33221, by rfl⟩ : syracuseStep 708725 = 66443) (by norm_num)
theorem B1691765 : Blo 330750 1691765 := bbase (se 5 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 1691765 = 158603) (by norm_num)
theorem B643253 : Blo 330750 643253 := bbase (se 5 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 643253 = 60305) (by norm_num)
theorem B839909 : Blo 330750 839909 := bbase (se 4 (by rfl) ⟨78741, by rfl⟩ : syracuseStep 839909 = 157483) (by norm_num)
theorem B840253 : Blo 330750 840253 := bbase (se 3 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 840253 = 315095) (by norm_num)
theorem B840365 : Blo 330750 840365 := bbase (se 3 (by rfl) ⟨157568, by rfl⟩ : syracuseStep 840365 = 315137) (by norm_num)
theorem B1299253 : Blo 330750 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B709469 : Blo 330750 709469 := bbase (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) (by norm_num)
theorem B840557 : Blo 330750 840557 := bbase (se 3 (by rfl) ⟨157604, by rfl⟩ : syracuseStep 840557 = 315209) (by norm_num)
theorem B676757 : Blo 330750 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B349177 : Blo 330750 349177 := bbase (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) (by norm_num)
theorem B840901 : Blo 330750 840901 := bbase (se 4 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 840901 = 157669) (by norm_num)
theorem B841013 : Blo 330750 841013 := bbase (se 5 (by rfl) ⟨39422, by rfl⟩ : syracuseStep 841013 = 78845) (by norm_num)
theorem B1693061 : Blo 330750 1693061 := bbase (se 4 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 1693061 = 317449) (by norm_num)
theorem B4576661 : Blo 330750 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B1267109 : Blo 330750 1267109 := bbase (se 4 (by rfl) ⟨118791, by rfl⟩ : syracuseStep 1267109 = 237583) (by norm_num)
theorem B1136117 : Blo 330750 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B841205 : Blo 330750 841205 := bbase (se 5 (by rfl) ⟨39431, by rfl⟩ : syracuseStep 841205 = 78863) (by norm_num)
theorem B1070597 : Blo 330750 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B710221 : Blo 330750 710221 := bbase (se 3 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 710221 = 266333) (by norm_num)
theorem B1267397 : Blo 330750 1267397 := bbase (se 4 (by rfl) ⟨118818, by rfl⟩ : syracuseStep 1267397 = 237637) (by norm_num)
theorem B710365 : Blo 330750 710365 := bbase (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) (by norm_num)
theorem B841549 : Blo 330750 841549 := bbase (se 3 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 841549 = 315581) (by norm_num)
theorem B841661 : Blo 330750 841661 := bbase (se 3 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 841661 = 315623) (by norm_num)
theorem B1595477 : Blo 330750 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B710741 : Blo 330750 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B841853 : Blo 330750 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1136773 : Blo 330750 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B8542421 : Blo 330750 8542421 := bbase (se 7 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 8542421 = 200213) (by norm_num)
theorem B383393 : Blo 330750 383393 := bbase (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) (by norm_num)
theorem B711109 : Blo 330750 711109 := bbase (se 4 (by rfl) ⟨66666, by rfl⟩ : syracuseStep 711109 = 133333) (by norm_num)
theorem B842197 : Blo 330750 842197 := bbase (se 7 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 842197 = 19739) (by norm_num)
theorem B842309 : Blo 330750 842309 := bbase (se 4 (by rfl) ⟨78966, by rfl⟩ : syracuseStep 842309 = 157933) (by norm_num)
theorem B1694357 : Blo 330750 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B940709 : Blo 330750 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B449221 : Blo 330750 449221 := bbase (se 4 (by rfl) ⟨42114, by rfl⟩ : syracuseStep 449221 = 84229) (by norm_num)
theorem B842501 : Blo 330750 842501 := bbase (se 4 (by rfl) ⟨78984, by rfl⟩ : syracuseStep 842501 = 157969) (by norm_num)
theorem B1071893 : Blo 330750 1071893 := bbase (se 6 (by rfl) ⟨25122, by rfl⟩ : syracuseStep 1071893 = 50245) (by norm_num)
theorem B744245 : Blo 330750 744245 := bbase (se 5 (by rfl) ⟨34886, by rfl⟩ : syracuseStep 744245 = 69773) (by norm_num)
theorem B1268581 : Blo 330750 1268581 := bbase (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) (by norm_num)
theorem B744317 : Blo 330750 744317 := bbase (se 3 (by rfl) ⟨139559, by rfl⟩ : syracuseStep 744317 = 279119) (by norm_num)
theorem B744389 : Blo 330750 744389 := bbase (se 4 (by rfl) ⟨69786, by rfl⟩ : syracuseStep 744389 = 139573) (by norm_num)
theorem B744461 : Blo 330750 744461 := bbase (se 3 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 744461 = 279173) (by norm_num)
theorem B744533 : Blo 330750 744533 := bbase (se 8 (by rfl) ⟨4362, by rfl⟩ : syracuseStep 744533 = 8725) (by norm_num)
theorem B842845 : Blo 330750 842845 := bbase (se 3 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 842845 = 316067) (by norm_num)
theorem B1268885 : Blo 330750 1268885 := bbase (se 6 (by rfl) ⟨29739, by rfl⟩ : syracuseStep 1268885 = 59479) (by norm_num)
theorem B744605 : Blo 330750 744605 := bbase (se 3 (by rfl) ⟨139613, by rfl⟩ : syracuseStep 744605 = 279227) (by norm_num)
theorem B449701 : Blo 330750 449701 := bbase (se 4 (by rfl) ⟨42159, by rfl⟩ : syracuseStep 449701 = 84319) (by norm_num)
theorem B842957 : Blo 330750 842957 := bbase (se 3 (by rfl) ⟨158054, by rfl⟩ : syracuseStep 842957 = 316109) (by norm_num)
theorem B744677 : Blo 330750 744677 := bbase (se 4 (by rfl) ⟨69813, by rfl⟩ : syracuseStep 744677 = 139627) (by norm_num)
theorem B744749 : Blo 330750 744749 := bbase (se 3 (by rfl) ⟨139640, by rfl⟩ : syracuseStep 744749 = 279281) (by norm_num)
theorem B744821 : Blo 330750 744821 := bbase (se 5 (by rfl) ⟨34913, by rfl⟩ : syracuseStep 744821 = 69827) (by norm_num)
theorem B843149 : Blo 330750 843149 := bbase (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) (by norm_num)
theorem B744893 : Blo 330750 744893 := bbase (se 3 (by rfl) ⟨139667, by rfl⟩ : syracuseStep 744893 = 279335) (by norm_num)
theorem B744965 : Blo 330750 744965 := bbase (se 4 (by rfl) ⟨69840, by rfl⟩ : syracuseStep 744965 = 139681) (by norm_num)
theorem B745037 : Blo 330750 745037 := bbase (se 3 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 745037 = 279389) (by norm_num)
theorem B745109 : Blo 330750 745109 := bbase (se 6 (by rfl) ⟨17463, by rfl⟩ : syracuseStep 745109 = 34927) (by norm_num)
theorem B745181 : Blo 330750 745181 := bbase (se 3 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 745181 = 279443) (by norm_num)
theorem B843493 : Blo 330750 843493 := bbase (se 4 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 843493 = 158155) (by norm_num)
theorem B1203989 : Blo 330750 1203989 := bbase (se 6 (by rfl) ⟨28218, by rfl⟩ : syracuseStep 1203989 = 56437) (by norm_num)
theorem B745253 : Blo 330750 745253 := bbase (se 4 (by rfl) ⟨69867, by rfl⟩ : syracuseStep 745253 = 139735) (by norm_num)
theorem B843605 : Blo 330750 843605 := bbase (se 9 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 843605 = 4943) (by norm_num)
theorem B745325 : Blo 330750 745325 := bbase (se 3 (by rfl) ⟨139748, by rfl⟩ : syracuseStep 745325 = 279497) (by norm_num)
theorem B712613 : Blo 330750 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B942005 : Blo 330750 942005 := bbase (se 5 (by rfl) ⟨44156, by rfl⟩ : syracuseStep 942005 = 88313) (by norm_num)
theorem B745397 : Blo 330750 745397 := bbase (se 5 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 745397 = 69881) (by norm_num)
theorem B745469 : Blo 330750 745469 := bbase (se 3 (by rfl) ⟨139775, by rfl⟩ : syracuseStep 745469 = 279551) (by norm_num)
theorem B1138693 : Blo 330750 1138693 := bbase (se 4 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 1138693 = 213505) (by norm_num)
theorem B843797 : Blo 330750 843797 := bbase (se 6 (by rfl) ⟨19776, by rfl⟩ : syracuseStep 843797 = 39553) (by norm_num)
theorem B1925141 : Blo 330750 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B712757 : Blo 330750 712757 := bbase (se 5 (by rfl) ⟨33410, by rfl⟩ : syracuseStep 712757 = 66821) (by norm_num)
theorem B745541 : Blo 330750 745541 := bbase (se 4 (by rfl) ⟨69894, by rfl⟩ : syracuseStep 745541 = 139789) (by norm_num)
theorem B745613 : Blo 330750 745613 := bbase (se 3 (by rfl) ⟨139802, by rfl⟩ : syracuseStep 745613 = 279605) (by norm_num)
theorem B745685 : Blo 330750 745685 := bbase (se 7 (by rfl) ⟨8738, by rfl⟩ : syracuseStep 745685 = 17477) (by norm_num)
theorem B745757 : Blo 330750 745757 := bbase (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) (by norm_num)
theorem B745829 : Blo 330750 745829 := bbase (se 4 (by rfl) ⟨69921, by rfl⟩ : syracuseStep 745829 = 139843) (by norm_num)
theorem B844141 : Blo 330750 844141 := bbase (se 3 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 844141 = 316553) (by norm_num)
theorem B713117 : Blo 330750 713117 := bbase (se 3 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 713117 = 267419) (by norm_num)
theorem B745901 : Blo 330750 745901 := bbase (se 3 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 745901 = 279713) (by norm_num)
theorem B2384309 : Blo 330750 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B844253 : Blo 330750 844253 := bbase (se 3 (by rfl) ⟨158297, by rfl⟩ : syracuseStep 844253 = 316595) (by norm_num)
theorem B745973 : Blo 330750 745973 := bbase (se 5 (by rfl) ⟨34967, by rfl⟩ : syracuseStep 745973 = 69935) (by norm_num)
theorem B746045 : Blo 330750 746045 := bbase (se 3 (by rfl) ⟨139883, by rfl⟩ : syracuseStep 746045 = 279767) (by norm_num)
theorem B746117 : Blo 330750 746117 := bbase (se 4 (by rfl) ⟨69948, by rfl⟩ : syracuseStep 746117 = 139897) (by norm_num)
theorem B844445 : Blo 330750 844445 := bbase (se 3 (by rfl) ⟨158333, by rfl⟩ : syracuseStep 844445 = 316667) (by norm_num)
theorem B746189 : Blo 330750 746189 := bbase (se 3 (by rfl) ⟨139910, by rfl⟩ : syracuseStep 746189 = 279821) (by norm_num)
theorem B1893077 : Blo 330750 1893077 := bbase (se 7 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 1893077 = 44369) (by norm_num)
theorem B746261 : Blo 330750 746261 := bbase (se 6 (by rfl) ⟨17490, by rfl⟩ : syracuseStep 746261 = 34981) (by norm_num)
theorem B746333 : Blo 330750 746333 := bbase (se 3 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 746333 = 279875) (by norm_num)
theorem B418709 : Blo 330750 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B746405 : Blo 330750 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B418765 : Blo 330750 418765 := bbase (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) (by norm_num)
theorem B746477 : Blo 330750 746477 := bbase (se 3 (by rfl) ⟨139964, by rfl⟩ : syracuseStep 746477 = 279929) (by norm_num)
theorem B353269 : Blo 330750 353269 := bbase (se 5 (by rfl) ⟨16559, by rfl⟩ : syracuseStep 353269 = 33119) (by norm_num)
theorem B844789 : Blo 330750 844789 := bbase (se 5 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 844789 = 79199) (by norm_num)
theorem B418861 : Blo 330750 418861 := bbase (se 3 (by rfl) ⟨78536, by rfl⟩ : syracuseStep 418861 = 157073) (by norm_num)
theorem B2516021 : Blo 330750 2516021 := bbase (se 5 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 2516021 = 235877) (by norm_num)
theorem B746549 : Blo 330750 746549 := bbase (se 5 (by rfl) ⟨34994, by rfl⟩ : syracuseStep 746549 = 69989) (by norm_num)
theorem B844901 : Blo 330750 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B746621 : Blo 330750 746621 := bbase (se 3 (by rfl) ⟨139991, by rfl⟩ : syracuseStep 746621 = 279983) (by norm_num)
theorem B1598629 : Blo 330750 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B746693 : Blo 330750 746693 := bbase (se 4 (by rfl) ⟨70002, by rfl⟩ : syracuseStep 746693 = 140005) (by norm_num)
theorem B1270997 : Blo 330750 1270997 := bbase (se 7 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 1270997 = 29789) (by norm_num)
theorem B419033 : Blo 330750 419033 := bbase (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) (by norm_num)
theorem B746765 : Blo 330750 746765 := bbase (se 3 (by rfl) ⟨140018, by rfl⟩ : syracuseStep 746765 = 280037) (by norm_num)
theorem B419089 : Blo 330750 419089 := bbase (se 2 (by rfl) ⟨157158, by rfl⟩ : syracuseStep 419089 = 314317) (by norm_num)
theorem B714005 : Blo 330750 714005 := bbase (se 6 (by rfl) ⟨16734, by rfl⟩ : syracuseStep 714005 = 33469) (by norm_num)
theorem B845093 : Blo 330750 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B484693 : Blo 330750 484693 := bbase (se 12 (by rfl) ⟨177, by rfl⟩ : syracuseStep 484693 = 355) (by norm_num)
theorem B746837 : Blo 330750 746837 := bbase (se 12 (by rfl) ⟨273, by rfl⟩ : syracuseStep 746837 = 547) (by norm_num)
theorem B353641 : Blo 330750 353641 := bbase (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) (by norm_num)
theorem B419185 : Blo 330750 419185 := bbase (se 2 (by rfl) ⟨157194, by rfl⟩ : syracuseStep 419185 = 314389) (by norm_num)
theorem B746909 : Blo 330750 746909 := bbase (se 3 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 746909 = 280091) (by norm_num)
theorem B943589 : Blo 330750 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B746981 : Blo 330750 746981 := bbase (se 4 (by rfl) ⟨70029, by rfl⟩ : syracuseStep 746981 = 140059) (by norm_num)
theorem B714253 : Blo 330750 714253 := bbase (se 3 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 714253 = 267845) (by norm_num)
theorem B4285973 : Blo 330750 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B419357 : Blo 330750 419357 := bbase (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) (by norm_num)
theorem B747053 : Blo 330750 747053 := bbase (se 3 (by rfl) ⟨140072, by rfl⟩ : syracuseStep 747053 = 280145) (by norm_num)
theorem B419413 : Blo 330750 419413 := bbase (se 8 (by rfl) ⟨2457, by rfl⟩ : syracuseStep 419413 = 4915) (by norm_num)
theorem B747125 : Blo 330750 747125 := bbase (se 5 (by rfl) ⟨35021, by rfl⟩ : syracuseStep 747125 = 70043) (by norm_num)
theorem B845437 : Blo 330750 845437 := bbase (se 3 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 845437 = 317039) (by norm_num)
theorem B812717 : Blo 330750 812717 := bbase (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) (by norm_num)
theorem B419509 : Blo 330750 419509 := bbase (se 5 (by rfl) ⟨19664, by rfl⟩ : syracuseStep 419509 = 39329) (by norm_num)
theorem B747197 : Blo 330750 747197 := bbase (se 3 (by rfl) ⟨140099, by rfl⟩ : syracuseStep 747197 = 280199) (by norm_num)
theorem B354017 : Blo 330750 354017 := bbase (se 2 (by rfl) ⟨132756, by rfl⟩ : syracuseStep 354017 = 265513) (by norm_num)
theorem B845549 : Blo 330750 845549 := bbase (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) (by norm_num)
theorem B2123509 : Blo 330750 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B747269 : Blo 330750 747269 := bbase (se 4 (by rfl) ⟨70056, by rfl⟩ : syracuseStep 747269 = 140113) (by norm_num)
theorem B354089 : Blo 330750 354089 := bbase (se 2 (by rfl) ⟨132783, by rfl⟩ : syracuseStep 354089 = 265567) (by norm_num)
theorem B747341 : Blo 330750 747341 := bbase (se 3 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 747341 = 280253) (by norm_num)
theorem B419681 : Blo 330750 419681 := bbase (se 2 (by rfl) ⟨157380, by rfl⟩ : syracuseStep 419681 = 314761) (by norm_num)
theorem B747413 : Blo 330750 747413 := bbase (se 6 (by rfl) ⟨17517, by rfl⟩ : syracuseStep 747413 = 35035) (by norm_num)
theorem B419737 : Blo 330750 419737 := bbase (se 2 (by rfl) ⟨157401, by rfl⟩ : syracuseStep 419737 = 314803) (by norm_num)
theorem B845741 : Blo 330750 845741 := bbase (se 3 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 845741 = 317153) (by norm_num)
theorem B747485 : Blo 330750 747485 := bbase (se 3 (by rfl) ⟨140153, by rfl⟩ : syracuseStep 747485 = 280307) (by norm_num)
theorem B354277 : Blo 330750 354277 := bbase (se 4 (by rfl) ⟨33213, by rfl⟩ : syracuseStep 354277 = 66427) (by norm_num)
theorem B1927157 : Blo 330750 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B419833 : Blo 330750 419833 := bbase (se 2 (by rfl) ⟨157437, by rfl⟩ : syracuseStep 419833 = 314875) (by norm_num)
theorem B714757 : Blo 330750 714757 := bbase (se 4 (by rfl) ⟨67008, by rfl⟩ : syracuseStep 714757 = 134017) (by norm_num)
theorem B1697813 : Blo 330750 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B747557 : Blo 330750 747557 := bbase (se 4 (by rfl) ⟨70083, by rfl⟩ : syracuseStep 747557 = 140167) (by norm_num)
theorem B747629 : Blo 330750 747629 := bbase (se 3 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 747629 = 280361) (by norm_num)
theorem B944261 : Blo 330750 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B354461 : Blo 330750 354461 := bbase (se 3 (by rfl) ⟨66461, by rfl⟩ : syracuseStep 354461 = 132923) (by norm_num)
theorem B420005 : Blo 330750 420005 := bbase (se 4 (by rfl) ⟨39375, by rfl⟩ : syracuseStep 420005 = 78751) (by norm_num)
theorem B747701 : Blo 330750 747701 := bbase (se 5 (by rfl) ⟨35048, by rfl⟩ : syracuseStep 747701 = 70097) (by norm_num)
theorem B420061 : Blo 330750 420061 := bbase (se 3 (by rfl) ⟨78761, by rfl⟩ : syracuseStep 420061 = 157523) (by norm_num)
theorem B747773 : Blo 330750 747773 := bbase (se 3 (by rfl) ⟨140207, by rfl⟩ : syracuseStep 747773 = 280415) (by norm_num)
theorem B846085 : Blo 330750 846085 := bbase (se 4 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 846085 = 158641) (by norm_num)
theorem B420157 : Blo 330750 420157 := bbase (se 3 (by rfl) ⟨78779, by rfl⟩ : syracuseStep 420157 = 157559) (by norm_num)
theorem B747845 : Blo 330750 747845 := bbase (se 4 (by rfl) ⟨70110, by rfl⟩ : syracuseStep 747845 = 140221) (by norm_num)
theorem B846197 : Blo 330750 846197 := bbase (se 5 (by rfl) ⟨39665, by rfl⟩ : syracuseStep 846197 = 79331) (by norm_num)
theorem B747917 : Blo 330750 747917 := bbase (se 3 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 747917 = 280469) (by norm_num)
theorem B747989 : Blo 330750 747989 := bbase (se 7 (by rfl) ⟨8765, by rfl⟩ : syracuseStep 747989 = 17531) (by norm_num)
theorem B420329 : Blo 330750 420329 := bbase (se 2 (by rfl) ⟨157623, by rfl⟩ : syracuseStep 420329 = 315247) (by norm_num)
theorem B748061 : Blo 330750 748061 := bbase (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) (by norm_num)
theorem B420385 : Blo 330750 420385 := bbase (se 2 (by rfl) ⟨157644, by rfl⟩ : syracuseStep 420385 = 315289) (by norm_num)
theorem B944693 : Blo 330750 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B846389 : Blo 330750 846389 := bbase (se 5 (by rfl) ⟨39674, by rfl⟩ : syracuseStep 846389 = 79349) (by norm_num)
theorem B748133 : Blo 330750 748133 := bbase (se 4 (by rfl) ⟨70137, by rfl⟩ : syracuseStep 748133 = 140275) (by norm_num)
theorem B420481 : Blo 330750 420481 := bbase (se 2 (by rfl) ⟨157680, by rfl⟩ : syracuseStep 420481 = 315361) (by norm_num)
theorem B748205 : Blo 330750 748205 := bbase (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) (by norm_num)
theorem B748277 : Blo 330750 748277 := bbase (se 5 (by rfl) ⟨35075, by rfl⟩ : syracuseStep 748277 = 70151) (by norm_num)
theorem B420653 : Blo 330750 420653 := bbase (se 3 (by rfl) ⟨78872, by rfl⟩ : syracuseStep 420653 = 157745) (by norm_num)
theorem B748349 : Blo 330750 748349 := bbase (se 3 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 748349 = 280631) (by norm_num)
theorem B420709 : Blo 330750 420709 := bbase (se 4 (by rfl) ⟨39441, by rfl⟩ : syracuseStep 420709 = 78883) (by norm_num)
theorem B748421 : Blo 330750 748421 := bbase (se 4 (by rfl) ⟨70164, by rfl⟩ : syracuseStep 748421 = 140329) (by norm_num)
theorem B355213 : Blo 330750 355213 := bbase (se 3 (by rfl) ⟨66602, by rfl⟩ : syracuseStep 355213 = 133205) (by norm_num)
theorem B846733 : Blo 330750 846733 := bbase (se 3 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 846733 = 317525) (by norm_num)
theorem B519077 : Blo 330750 519077 := bbase (se 4 (by rfl) ⟨48663, by rfl⟩ : syracuseStep 519077 = 97327) (by norm_num)
theorem B420805 : Blo 330750 420805 := bbase (se 4 (by rfl) ⟨39450, by rfl⟩ : syracuseStep 420805 = 78901) (by norm_num)
theorem B748493 : Blo 330750 748493 := bbase (se 3 (by rfl) ⟨140342, by rfl⟩ : syracuseStep 748493 = 280685) (by norm_num)
theorem B355285 : Blo 330750 355285 := bbase (se 7 (by rfl) ⟨4163, by rfl⟩ : syracuseStep 355285 = 8327) (by norm_num)
theorem B846845 : Blo 330750 846845 := bbase (se 3 (by rfl) ⟨158783, by rfl⟩ : syracuseStep 846845 = 317567) (by norm_num)
theorem B748565 : Blo 330750 748565 := bbase (se 6 (by rfl) ⟨17544, by rfl⟩ : syracuseStep 748565 = 35089) (by norm_num)
theorem B748637 : Blo 330750 748637 := bbase (se 3 (by rfl) ⟨140369, by rfl⟩ : syracuseStep 748637 = 280739) (by norm_num)
theorem B420977 : Blo 330750 420977 := bbase (se 2 (by rfl) ⟨157866, by rfl⟩ : syracuseStep 420977 = 315733) (by norm_num)
theorem B355465 : Blo 330750 355465 := bbase (se 2 (by rfl) ⟨133299, by rfl⟩ : syracuseStep 355465 = 266599) (by norm_num)
theorem B748709 : Blo 330750 748709 := bbase (se 4 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 748709 = 140383) (by norm_num)
theorem B421033 : Blo 330750 421033 := bbase (se 2 (by rfl) ⟨157887, by rfl⟩ : syracuseStep 421033 = 315775) (by norm_num)
theorem B847037 : Blo 330750 847037 := bbase (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) (by norm_num)
theorem B748781 : Blo 330750 748781 := bbase (se 3 (by rfl) ⟨140396, by rfl⟩ : syracuseStep 748781 = 280793) (by norm_num)
theorem B421129 : Blo 330750 421129 := bbase (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) (by norm_num)
theorem B945445 : Blo 330750 945445 := bbase (se 4 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 945445 = 177271) (by norm_num)
theorem B748853 : Blo 330750 748853 := bbase (se 5 (by rfl) ⟨35102, by rfl⟩ : syracuseStep 748853 = 70205) (by norm_num)
theorem B748925 : Blo 330750 748925 := bbase (se 3 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 748925 = 280847) (by norm_num)
theorem B421301 : Blo 330750 421301 := bbase (se 5 (by rfl) ⟨19748, by rfl⟩ : syracuseStep 421301 = 39497) (by norm_num)
theorem B748997 : Blo 330750 748997 := bbase (se 4 (by rfl) ⟨70218, by rfl⟩ : syracuseStep 748997 = 140437) (by norm_num)
theorem B421357 : Blo 330750 421357 := bbase (se 3 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 421357 = 158009) (by norm_num)
theorem B749069 : Blo 330750 749069 := bbase (se 3 (by rfl) ⟨140450, by rfl⟩ : syracuseStep 749069 = 280901) (by norm_num)
theorem B355909 : Blo 330750 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B421453 : Blo 330750 421453 := bbase (se 3 (by rfl) ⟨79022, by rfl⟩ : syracuseStep 421453 = 158045) (by norm_num)
theorem B749141 : Blo 330750 749141 := bbase (se 8 (by rfl) ⟨4389, by rfl⟩ : syracuseStep 749141 = 8779) (by norm_num)
theorem B749213 : Blo 330750 749213 := bbase (se 3 (by rfl) ⟨140477, by rfl⟩ : syracuseStep 749213 = 280955) (by norm_num)
theorem B356033 : Blo 330750 356033 := bbase (se 2 (by rfl) ⟨133512, by rfl⟩ : syracuseStep 356033 = 267025) (by norm_num)
theorem B749285 : Blo 330750 749285 := bbase (se 4 (by rfl) ⟨70245, by rfl⟩ : syracuseStep 749285 = 140491) (by norm_num)
theorem B421625 : Blo 330750 421625 := bbase (se 2 (by rfl) ⟨158109, by rfl⟩ : syracuseStep 421625 = 316219) (by norm_num)
theorem B749357 : Blo 330750 749357 := bbase (se 3 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 749357 = 281009) (by norm_num)
theorem B421681 : Blo 330750 421681 := bbase (se 2 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 421681 = 316261) (by norm_num)
theorem B749429 : Blo 330750 749429 := bbase (se 5 (by rfl) ⟨35129, by rfl⟩ : syracuseStep 749429 = 70259) (by norm_num)
theorem B421777 : Blo 330750 421777 := bbase (se 2 (by rfl) ⟨158166, by rfl⟩ : syracuseStep 421777 = 316333) (by norm_num)
theorem B716701 : Blo 330750 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B749501 : Blo 330750 749501 := bbase (se 3 (by rfl) ⟨140531, by rfl⟩ : syracuseStep 749501 = 281063) (by norm_num)
theorem B356285 : Blo 330750 356285 := bbase (se 3 (by rfl) ⟨66803, by rfl⟩ : syracuseStep 356285 = 133607) (by norm_num)
theorem B1601477 : Blo 330750 1601477 := bbase (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) (by norm_num)
theorem B749573 : Blo 330750 749573 := bbase (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) (by norm_num)
theorem B421949 : Blo 330750 421949 := bbase (se 3 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 421949 = 158231) (by norm_num)
theorem B749645 : Blo 330750 749645 := bbase (se 3 (by rfl) ⟨140558, by rfl⟩ : syracuseStep 749645 = 281117) (by norm_num)
theorem B422005 : Blo 330750 422005 := bbase (se 5 (by rfl) ⟨19781, by rfl⟩ : syracuseStep 422005 = 39563) (by norm_num)
theorem B749717 : Blo 330750 749717 := bbase (se 6 (by rfl) ⟨17571, by rfl⟩ : syracuseStep 749717 = 35143) (by norm_num)
theorem B422101 : Blo 330750 422101 := bbase (se 7 (by rfl) ⟨4946, by rfl⟩ : syracuseStep 422101 = 9893) (by norm_num)
theorem B749789 : Blo 330750 749789 := bbase (se 3 (by rfl) ⟨140585, by rfl⟩ : syracuseStep 749789 = 281171) (by norm_num)
theorem B749861 : Blo 330750 749861 := bbase (se 4 (by rfl) ⟨70299, by rfl⟩ : syracuseStep 749861 = 140599) (by norm_num)
theorem B782669 : Blo 330750 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B749933 : Blo 330750 749933 := bbase (se 3 (by rfl) ⟨140612, by rfl⟩ : syracuseStep 749933 = 281225) (by norm_num)
theorem B356729 : Blo 330750 356729 := bbase (se 2 (by rfl) ⟨133773, by rfl⟩ : syracuseStep 356729 = 267547) (by norm_num)
theorem B422273 : Blo 330750 422273 := bbase (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) (by norm_num)
theorem B750005 : Blo 330750 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B422329 : Blo 330750 422329 := bbase (se 2 (by rfl) ⟨158373, by rfl⟩ : syracuseStep 422329 = 316747) (by norm_num)
theorem B750077 : Blo 330750 750077 := bbase (se 3 (by rfl) ⟨140639, by rfl⟩ : syracuseStep 750077 = 281279) (by norm_num)
theorem B2126357 : Blo 330750 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B422425 : Blo 330750 422425 := bbase (se 2 (by rfl) ⟨158409, by rfl⟩ : syracuseStep 422425 = 316819) (by norm_num)
theorem B750149 : Blo 330750 750149 := bbase (se 4 (by rfl) ⟨70326, by rfl⟩ : syracuseStep 750149 = 140653) (by norm_num)
theorem B356977 : Blo 330750 356977 := bbase (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) (by norm_num)
theorem B750221 : Blo 330750 750221 := bbase (se 3 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 750221 = 281333) (by norm_num)
theorem B422597 : Blo 330750 422597 := bbase (se 4 (by rfl) ⟨39618, by rfl⟩ : syracuseStep 422597 = 79237) (by norm_num)
theorem B750293 : Blo 330750 750293 := bbase (se 7 (by rfl) ⟨8792, by rfl⟩ : syracuseStep 750293 = 17585) (by norm_num)
theorem B422653 : Blo 330750 422653 := bbase (se 3 (by rfl) ⟨79247, by rfl⟩ : syracuseStep 422653 = 158495) (by norm_num)
theorem B750365 : Blo 330750 750365 := bbase (se 3 (by rfl) ⟨140693, by rfl⟩ : syracuseStep 750365 = 281387) (by norm_num)
theorem B422749 : Blo 330750 422749 := bbase (se 3 (by rfl) ⟨79265, by rfl⟩ : syracuseStep 422749 = 158531) (by norm_num)
theorem B750437 : Blo 330750 750437 := bbase (se 4 (by rfl) ⟨70353, by rfl⟩ : syracuseStep 750437 = 140707) (by norm_num)
theorem B750509 : Blo 330750 750509 := bbase (se 3 (by rfl) ⟨140720, by rfl⟩ : syracuseStep 750509 = 281441) (by norm_num)
theorem B1438661 : Blo 330750 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B1274869 : Blo 330750 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B750581 : Blo 330750 750581 := bbase (se 5 (by rfl) ⟨35183, by rfl⟩ : syracuseStep 750581 = 70367) (by norm_num)
theorem B422921 : Blo 330750 422921 := bbase (se 2 (by rfl) ⟨158595, by rfl⟩ : syracuseStep 422921 = 317191) (by norm_num)
theorem B357421 : Blo 330750 357421 := bbase (se 3 (by rfl) ⟨67016, by rfl⟩ : syracuseStep 357421 = 134033) (by norm_num)
theorem B750653 : Blo 330750 750653 := bbase (se 3 (by rfl) ⟨140747, by rfl⟩ : syracuseStep 750653 = 281495) (by norm_num)
theorem B422977 : Blo 330750 422977 := bbase (se 2 (by rfl) ⟨158616, by rfl⟩ : syracuseStep 422977 = 317233) (by norm_num)
theorem B750725 : Blo 330750 750725 := bbase (se 4 (by rfl) ⟨70380, by rfl⟩ : syracuseStep 750725 = 140761) (by norm_num)
theorem B423073 : Blo 330750 423073 := bbase (se 2 (by rfl) ⟨158652, by rfl⟩ : syracuseStep 423073 = 317305) (by norm_num)
theorem B750797 : Blo 330750 750797 := bbase (se 3 (by rfl) ⟨140774, by rfl⟩ : syracuseStep 750797 = 281549) (by norm_num)
theorem B849133 : Blo 330750 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B1602821 : Blo 330750 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B750869 : Blo 330750 750869 := bbase (se 6 (by rfl) ⟨17598, by rfl⟩ : syracuseStep 750869 = 35197) (by norm_num)
theorem B423245 : Blo 330750 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B750941 : Blo 330750 750941 := bbase (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) (by norm_num)
theorem B423301 : Blo 330750 423301 := bbase (se 4 (by rfl) ⟨39684, by rfl⟩ : syracuseStep 423301 = 79369) (by norm_num)
theorem B751013 : Blo 330750 751013 := bbase (se 4 (by rfl) ⟨70407, by rfl⟩ : syracuseStep 751013 = 140815) (by norm_num)
theorem B423397 : Blo 330750 423397 := bbase (se 4 (by rfl) ⟨39693, by rfl⟩ : syracuseStep 423397 = 79387) (by norm_num)
theorem B751085 : Blo 330750 751085 := bbase (se 3 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 751085 = 281657) (by norm_num)
theorem B751157 : Blo 330750 751157 := bbase (se 5 (by rfl) ⟨35210, by rfl⟩ : syracuseStep 751157 = 70421) (by norm_num)
theorem B751229 : Blo 330750 751229 := bbase (se 3 (by rfl) ⟨140855, by rfl⟩ : syracuseStep 751229 = 281711) (by norm_num)
theorem B423569 : Blo 330750 423569 := bbase (se 2 (by rfl) ⟨158838, by rfl⟩ : syracuseStep 423569 = 317677) (by norm_num)
theorem B751301 : Blo 330750 751301 := bbase (se 4 (by rfl) ⟨70434, by rfl⟩ : syracuseStep 751301 = 140869) (by norm_num)
theorem B784069 : Blo 330750 784069 := bbase (se 4 (by rfl) ⟨73506, by rfl⟩ : syracuseStep 784069 = 147013) (by norm_num)
theorem B423625 : Blo 330750 423625 := bbase (se 2 (by rfl) ⟨158859, by rfl⟩ : syracuseStep 423625 = 317719) (by norm_num)
theorem B751373 : Blo 330750 751373 := bbase (se 3 (by rfl) ⟨140882, by rfl⟩ : syracuseStep 751373 = 281765) (by norm_num)
theorem B751445 : Blo 330750 751445 := bbase (se 9 (by rfl) ⟨2201, by rfl⟩ : syracuseStep 751445 = 4403) (by norm_num)
theorem B751517 : Blo 330750 751517 := bbase (se 3 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 751517 = 281819) (by norm_num)
theorem B751589 : Blo 330750 751589 := bbase (se 4 (by rfl) ⟨70461, by rfl⟩ : syracuseStep 751589 = 140923) (by norm_num)
theorem B751661 : Blo 330750 751661 := bbase (se 3 (by rfl) ⟨140936, by rfl⟩ : syracuseStep 751661 = 281873) (by norm_num)
theorem B948293 : Blo 330750 948293 := bbase (se 4 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 948293 = 177805) (by norm_num)
theorem B751733 : Blo 330750 751733 := bbase (se 5 (by rfl) ⟨35237, by rfl⟩ : syracuseStep 751733 = 70475) (by norm_num)
theorem B751805 : Blo 330750 751805 := bbase (se 3 (by rfl) ⟨140963, by rfl⟩ : syracuseStep 751805 = 281927) (by norm_num)
theorem B751877 : Blo 330750 751877 := bbase (se 4 (by rfl) ⟨70488, by rfl⟩ : syracuseStep 751877 = 140977) (by norm_num)
theorem B751949 : Blo 330750 751949 := bbase (se 3 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 751949 = 281981) (by norm_num)
theorem B752021 : Blo 330750 752021 := bbase (se 6 (by rfl) ⟨17625, by rfl⟩ : syracuseStep 752021 = 35251) (by norm_num)
theorem B522677 : Blo 330750 522677 := bbase (se 5 (by rfl) ⟨24500, by rfl⟩ : syracuseStep 522677 = 49001) (by norm_num)
theorem B752093 : Blo 330750 752093 := bbase (se 3 (by rfl) ⟨141017, by rfl⟩ : syracuseStep 752093 = 282035) (by norm_num)
theorem B752165 : Blo 330750 752165 := bbase (se 4 (by rfl) ⟨70515, by rfl⟩ : syracuseStep 752165 = 141031) (by norm_num)
theorem B424525 : Blo 330750 424525 := bbase (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) (by norm_num)
theorem B752237 : Blo 330750 752237 := bbase (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) (by norm_num)
theorem B752309 : Blo 330750 752309 := bbase (se 5 (by rfl) ⟨35264, by rfl⟩ : syracuseStep 752309 = 70529) (by norm_num)
theorem B2849525 : Blo 330750 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B752381 : Blo 330750 752381 := bbase (se 3 (by rfl) ⟨141071, by rfl⟩ : syracuseStep 752381 = 282143) (by norm_num)
theorem B752453 : Blo 330750 752453 := bbase (se 4 (by rfl) ⟨70542, by rfl⟩ : syracuseStep 752453 = 141085) (by norm_num)
theorem B752525 : Blo 330750 752525 := bbase (se 3 (by rfl) ⟨141098, by rfl⟩ : syracuseStep 752525 = 282197) (by norm_num)
theorem B850877 : Blo 330750 850877 := bbase (se 3 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 850877 = 319079) (by norm_num)
theorem B752597 : Blo 330750 752597 := bbase (se 7 (by rfl) ⟨8819, by rfl⟩ : syracuseStep 752597 = 17639) (by norm_num)
theorem B752669 : Blo 330750 752669 := bbase (se 3 (by rfl) ⟨141125, by rfl⟩ : syracuseStep 752669 = 282251) (by norm_num)
theorem B752741 : Blo 330750 752741 := bbase (se 4 (by rfl) ⟨70569, by rfl⟩ : syracuseStep 752741 = 141139) (by norm_num)
theorem B752813 : Blo 330750 752813 := bbase (se 3 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 752813 = 282305) (by norm_num)
theorem B1440949 : Blo 330750 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B949477 : Blo 330750 949477 := bbase (se 4 (by rfl) ⟨89013, by rfl⟩ : syracuseStep 949477 = 178027) (by norm_num)
theorem B752885 : Blo 330750 752885 := bbase (se 5 (by rfl) ⟨35291, by rfl⟩ : syracuseStep 752885 = 70583) (by norm_num)
theorem B425245 : Blo 330750 425245 := bbase (se 3 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 425245 = 159467) (by norm_num)
theorem B752957 : Blo 330750 752957 := bbase (se 3 (by rfl) ⟨141179, by rfl⟩ : syracuseStep 752957 = 282359) (by norm_num)
theorem B425305 : Blo 330750 425305 := bbase (se 2 (by rfl) ⟨159489, by rfl⟩ : syracuseStep 425305 = 318979) (by norm_num)
theorem B949637 : Blo 330750 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B753029 : Blo 330750 753029 := bbase (se 4 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 753029 = 141193) (by norm_num)
theorem B753101 : Blo 330750 753101 := bbase (se 3 (by rfl) ⟨141206, by rfl⟩ : syracuseStep 753101 = 282413) (by norm_num)
theorem B425425 : Blo 330750 425425 := bbase (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) (by norm_num)
theorem B753173 : Blo 330750 753173 := bbase (se 6 (by rfl) ⟨17652, by rfl⟩ : syracuseStep 753173 = 35305) (by norm_num)
theorem B949877 : Blo 330750 949877 := bbase (se 5 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 949877 = 89051) (by norm_num)
theorem B1703605 : Blo 330750 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B851677 : Blo 330750 851677 := bbase (se 3 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 851677 = 319379) (by norm_num)
theorem B950069 : Blo 330750 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B851917 : Blo 330750 851917 := bbase (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) (by norm_num)
theorem B1900685 : Blo 330750 1900685 := bstep (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) B712757
theorem B1441955 : Blo 330750 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B1016003 : Blo 330750 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B2130275 : Blo 330750 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B6062789 : Blo 330750 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B3605219 : Blo 330750 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B951277 : Blo 330750 951277 := bstep (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) B356729
theorem B558211 : Blo 330750 558211 := bstep (se 1 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 558211 = 837317) B837317
theorem B1082531 : Blo 330750 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B558353 : Blo 330750 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B558481 : Blo 330750 558481 := bstep (se 2 (by rfl) ⟨209430, by rfl⟩ : syracuseStep 558481 = 418861) B418861
theorem B558515 : Blo 330750 558515 := bstep (se 1 (by rfl) ⟨418886, by rfl⟩ : syracuseStep 558515 = 837773) B837773
theorem B2131505 : Blo 330750 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B558643 : Blo 330750 558643 := bstep (se 1 (by rfl) ⟨418982, by rfl⟩ : syracuseStep 558643 = 837965) B837965
theorem B558785 : Blo 330750 558785 := bstep (se 2 (by rfl) ⟨209544, by rfl⟩ : syracuseStep 558785 = 419089) B419089
theorem B558913 : Blo 330750 558913 := bstep (se 2 (by rfl) ⟨209592, by rfl⟩ : syracuseStep 558913 = 419185) B419185
theorem B558947 : Blo 330750 558947 := bstep (se 1 (by rfl) ⟨419210, by rfl⟩ : syracuseStep 558947 = 838421) B838421
theorem B559075 : Blo 330750 559075 := bstep (se 1 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 559075 = 838613) B838613
theorem B952337 : Blo 330750 952337 := bstep (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) B714253
theorem B1607779 : Blo 330750 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B559217 : Blo 330750 559217 := bstep (se 2 (by rfl) ⟨209706, by rfl⟩ : syracuseStep 559217 = 419413) B419413
theorem B559345 : Blo 330750 559345 := bstep (se 2 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 559345 = 419509) B419509
theorem B559379 : Blo 330750 559379 := bstep (se 1 (by rfl) ⟨419534, by rfl⟩ : syracuseStep 559379 = 839069) B839069
theorem B1116557 : Blo 330750 1116557 := bstep (se 3 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 1116557 = 418709) B418709
theorem B1804685 : Blo 330750 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B559507 : Blo 330750 559507 := bstep (se 1 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 559507 = 839261) B839261
theorem B1116611 : Blo 330750 1116611 := bstep (se 1 (by rfl) ⟨837458, by rfl⟩ : syracuseStep 1116611 = 1674917) B1674917
theorem B3836429 : Blo 330750 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B559649 : Blo 330750 559649 := bstep (se 2 (by rfl) ⟨209868, by rfl⟩ : syracuseStep 559649 = 419737) B419737
theorem B559777 : Blo 330750 559777 := bstep (se 2 (by rfl) ⟨209916, by rfl⟩ : syracuseStep 559777 = 419833) B419833
theorem B953009 : Blo 330750 953009 := bstep (se 2 (by rfl) ⟨357378, by rfl⟩ : syracuseStep 953009 = 714757) B714757
theorem B559811 : Blo 330750 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B1116881 : Blo 330750 1116881 := bstep (se 2 (by rfl) ⟨418830, by rfl⟩ : syracuseStep 1116881 = 837661) B837661
theorem B428755 : Blo 330750 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B8784611 : Blo 330750 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B559939 : Blo 330750 559939 := bstep (se 1 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 559939 = 839909) B839909
theorem B560081 : Blo 330750 560081 := bstep (se 2 (by rfl) ⟨210030, by rfl⟩ : syracuseStep 560081 = 420061) B420061
theorem B1903601 : Blo 330750 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B330755 : Blo 330750 330755 := bstep (se 1 (by rfl) ⟨248066, by rfl⟩ : syracuseStep 330755 = 496133) B496133
theorem B855043 : Blo 330750 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B330771 : Blo 330750 330771 := bstep (se 1 (by rfl) ⟨248078, by rfl⟩ : syracuseStep 330771 = 496157) B496157
theorem B330787 : Blo 330750 330787 := bstep (se 1 (by rfl) ⟨248090, by rfl⟩ : syracuseStep 330787 = 496181) B496181
theorem B330803 : Blo 330750 330803 := bstep (se 1 (by rfl) ⟨248102, by rfl⟩ : syracuseStep 330803 = 496205) B496205
theorem B330819 : Blo 330750 330819 := bstep (se 1 (by rfl) ⟨248114, by rfl⟩ : syracuseStep 330819 = 496229) B496229
theorem B560209 : Blo 330750 560209 := bstep (se 2 (by rfl) ⟨210078, by rfl⟩ : syracuseStep 560209 = 420157) B420157
theorem B330835 : Blo 330750 330835 := bstep (se 1 (by rfl) ⟨248126, by rfl⟩ : syracuseStep 330835 = 496253) B496253
theorem B330851 : Blo 330750 330851 := bstep (se 1 (by rfl) ⟨248138, by rfl⟩ : syracuseStep 330851 = 496277) B496277
theorem B330867 : Blo 330750 330867 := bstep (se 1 (by rfl) ⟨248150, by rfl⟩ : syracuseStep 330867 = 496301) B496301
theorem B560243 : Blo 330750 560243 := bstep (se 1 (by rfl) ⟨420182, by rfl⟩ : syracuseStep 560243 = 840365) B840365
theorem B330883 : Blo 330750 330883 := bstep (se 1 (by rfl) ⟨248162, by rfl⟩ : syracuseStep 330883 = 496325) B496325
theorem B330899 : Blo 330750 330899 := bstep (se 1 (by rfl) ⟨248174, by rfl⟩ : syracuseStep 330899 = 496349) B496349
theorem B330915 : Blo 330750 330915 := bstep (se 1 (by rfl) ⟨248186, by rfl⟩ : syracuseStep 330915 = 496373) B496373
theorem B330931 : Blo 330750 330931 := bstep (se 1 (by rfl) ⟨248198, by rfl⟩ : syracuseStep 330931 = 496397) B496397
theorem B330947 : Blo 330750 330947 := bstep (se 1 (by rfl) ⟨248210, by rfl⟩ : syracuseStep 330947 = 496421) B496421
theorem B330963 : Blo 330750 330963 := bstep (se 1 (by rfl) ⟨248222, by rfl⟩ : syracuseStep 330963 = 496445) B496445
theorem B330979 : Blo 330750 330979 := bstep (se 1 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 330979 = 496469) B496469
theorem B1117421 : Blo 330750 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B330995 : Blo 330750 330995 := bstep (se 1 (by rfl) ⟨248246, by rfl⟩ : syracuseStep 330995 = 496493) B496493
theorem B560371 : Blo 330750 560371 := bstep (se 1 (by rfl) ⟨420278, by rfl⟩ : syracuseStep 560371 = 840557) B840557
theorem B331011 : Blo 330750 331011 := bstep (se 1 (by rfl) ⟨248258, by rfl⟩ : syracuseStep 331011 = 496517) B496517
theorem B331027 : Blo 330750 331027 := bstep (se 1 (by rfl) ⟨248270, by rfl⟩ : syracuseStep 331027 = 496541) B496541
theorem B331043 : Blo 330750 331043 := bstep (se 1 (by rfl) ⟨248282, by rfl⟩ : syracuseStep 331043 = 496565) B496565
theorem B1117475 : Blo 330750 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B331059 : Blo 330750 331059 := bstep (se 1 (by rfl) ⟨248294, by rfl⟩ : syracuseStep 331059 = 496589) B496589
theorem B331075 : Blo 330750 331075 := bstep (se 1 (by rfl) ⟨248306, by rfl⟩ : syracuseStep 331075 = 496613) B496613
theorem B331091 : Blo 330750 331091 := bstep (se 1 (by rfl) ⟨248318, by rfl⟩ : syracuseStep 331091 = 496637) B496637
theorem B331107 : Blo 330750 331107 := bstep (se 1 (by rfl) ⟨248330, by rfl⟩ : syracuseStep 331107 = 496661) B496661
theorem B331123 : Blo 330750 331123 := bstep (se 1 (by rfl) ⟨248342, by rfl⟩ : syracuseStep 331123 = 496685) B496685
theorem B560513 : Blo 330750 560513 := bstep (se 2 (by rfl) ⟨210192, by rfl⟩ : syracuseStep 560513 = 420385) B420385
theorem B331139 : Blo 330750 331139 := bstep (se 1 (by rfl) ⟨248354, by rfl⟩ : syracuseStep 331139 = 496709) B496709
theorem B331155 : Blo 330750 331155 := bstep (se 1 (by rfl) ⟨248366, by rfl⟩ : syracuseStep 331155 = 496733) B496733
theorem B331171 : Blo 330750 331171 := bstep (se 1 (by rfl) ⟨248378, by rfl⟩ : syracuseStep 331171 = 496757) B496757
theorem B331187 : Blo 330750 331187 := bstep (se 1 (by rfl) ⟨248390, by rfl⟩ : syracuseStep 331187 = 496781) B496781
theorem B331203 : Blo 330750 331203 := bstep (se 1 (by rfl) ⟨248402, by rfl⟩ : syracuseStep 331203 = 496805) B496805
theorem B3771845 : Blo 330750 3771845 := bstep (se 4 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 3771845 = 707221) B707221
theorem B331219 : Blo 330750 331219 := bstep (se 1 (by rfl) ⟨248414, by rfl⟩ : syracuseStep 331219 = 496829) B496829
theorem B331235 : Blo 330750 331235 := bstep (se 1 (by rfl) ⟨248426, by rfl⟩ : syracuseStep 331235 = 496853) B496853
theorem B331251 : Blo 330750 331251 := bstep (se 1 (by rfl) ⟨248438, by rfl⟩ : syracuseStep 331251 = 496877) B496877
theorem B560641 : Blo 330750 560641 := bstep (se 2 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 560641 = 420481) B420481
theorem B331267 : Blo 330750 331267 := bstep (se 1 (by rfl) ⟨248450, by rfl⟩ : syracuseStep 331267 = 496901) B496901
theorem B331283 : Blo 330750 331283 := bstep (se 1 (by rfl) ⟨248462, by rfl⟩ : syracuseStep 331283 = 496925) B496925
theorem B331299 : Blo 330750 331299 := bstep (se 1 (by rfl) ⟨248474, by rfl⟩ : syracuseStep 331299 = 496949) B496949
theorem B560675 : Blo 330750 560675 := bstep (se 1 (by rfl) ⟨420506, by rfl⟩ : syracuseStep 560675 = 841013) B841013
theorem B1117745 : Blo 330750 1117745 := bstep (se 2 (by rfl) ⟨419154, by rfl⟩ : syracuseStep 1117745 = 838309) B838309
theorem B331315 : Blo 330750 331315 := bstep (se 1 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 331315 = 496973) B496973
theorem B331331 : Blo 330750 331331 := bstep (se 1 (by rfl) ⟨248498, by rfl⟩ : syracuseStep 331331 = 496997) B496997
theorem B331347 : Blo 330750 331347 := bstep (se 1 (by rfl) ⟨248510, by rfl⟩ : syracuseStep 331347 = 497021) B497021
theorem B331363 : Blo 330750 331363 := bstep (se 1 (by rfl) ⟨248522, by rfl⟩ : syracuseStep 331363 = 497045) B497045
theorem B3051107 : Blo 330750 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B331379 : Blo 330750 331379 := bstep (se 1 (by rfl) ⟨248534, by rfl⟩ : syracuseStep 331379 = 497069) B497069
theorem B331395 : Blo 330750 331395 := bstep (se 1 (by rfl) ⟨248546, by rfl⟩ : syracuseStep 331395 = 497093) B497093
theorem B331411 : Blo 330750 331411 := bstep (se 1 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 331411 = 497117) B497117
theorem B331427 : Blo 330750 331427 := bstep (se 1 (by rfl) ⟨248570, by rfl⟩ : syracuseStep 331427 = 497141) B497141
theorem B560803 : Blo 330750 560803 := bstep (se 1 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 560803 = 841205) B841205
theorem B331443 : Blo 330750 331443 := bstep (se 1 (by rfl) ⟨248582, by rfl⟩ : syracuseStep 331443 = 497165) B497165
theorem B331459 : Blo 330750 331459 := bstep (se 1 (by rfl) ⟨248594, by rfl⟩ : syracuseStep 331459 = 497189) B497189
theorem B331475 : Blo 330750 331475 := bstep (se 1 (by rfl) ⟨248606, by rfl⟩ : syracuseStep 331475 = 497213) B497213
theorem B331491 : Blo 330750 331491 := bstep (se 1 (by rfl) ⟨248618, by rfl⟩ : syracuseStep 331491 = 497237) B497237
theorem B331507 : Blo 330750 331507 := bstep (se 1 (by rfl) ⟨248630, by rfl⟩ : syracuseStep 331507 = 497261) B497261
theorem B331523 : Blo 330750 331523 := bstep (se 1 (by rfl) ⟨248642, by rfl⟩ : syracuseStep 331523 = 497285) B497285
theorem B331539 : Blo 330750 331539 := bstep (se 1 (by rfl) ⟨248654, by rfl⟩ : syracuseStep 331539 = 497309) B497309
theorem B331555 : Blo 330750 331555 := bstep (se 1 (by rfl) ⟨248666, by rfl⟩ : syracuseStep 331555 = 497333) B497333
theorem B560945 : Blo 330750 560945 := bstep (se 2 (by rfl) ⟨210354, by rfl⟩ : syracuseStep 560945 = 420709) B420709
theorem B331571 : Blo 330750 331571 := bstep (se 1 (by rfl) ⟨248678, by rfl⟩ : syracuseStep 331571 = 497357) B497357
theorem B331587 : Blo 330750 331587 := bstep (se 1 (by rfl) ⟨248690, by rfl⟩ : syracuseStep 331587 = 497381) B497381
theorem B331603 : Blo 330750 331603 := bstep (se 1 (by rfl) ⟨248702, by rfl⟩ : syracuseStep 331603 = 497405) B497405
theorem B331619 : Blo 330750 331619 := bstep (se 1 (by rfl) ⟨248714, by rfl⟩ : syracuseStep 331619 = 497429) B497429
theorem B331635 : Blo 330750 331635 := bstep (se 1 (by rfl) ⟨248726, by rfl⟩ : syracuseStep 331635 = 497453) B497453
theorem B331651 : Blo 330750 331651 := bstep (se 1 (by rfl) ⟨248738, by rfl⟩ : syracuseStep 331651 = 497477) B497477
theorem B331667 : Blo 330750 331667 := bstep (se 1 (by rfl) ⟨248750, by rfl⟩ : syracuseStep 331667 = 497501) B497501
theorem B331683 : Blo 330750 331683 := bstep (se 1 (by rfl) ⟨248762, by rfl⟩ : syracuseStep 331683 = 497525) B497525
theorem B561073 : Blo 330750 561073 := bstep (se 2 (by rfl) ⟨210402, by rfl⟩ : syracuseStep 561073 = 420805) B420805
theorem B331699 : Blo 330750 331699 := bstep (se 1 (by rfl) ⟨248774, by rfl⟩ : syracuseStep 331699 = 497549) B497549
theorem B331715 : Blo 330750 331715 := bstep (se 1 (by rfl) ⟨248786, by rfl⟩ : syracuseStep 331715 = 497573) B497573
theorem B2133965 : Blo 330750 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B331731 : Blo 330750 331731 := bstep (se 1 (by rfl) ⟨248798, by rfl⟩ : syracuseStep 331731 = 497597) B497597
theorem B561107 : Blo 330750 561107 := bstep (se 1 (by rfl) ⟨420830, by rfl⟩ : syracuseStep 561107 = 841661) B841661
theorem B331747 : Blo 330750 331747 := bstep (se 1 (by rfl) ⟨248810, by rfl⟩ : syracuseStep 331747 = 497621) B497621
theorem B331763 : Blo 330750 331763 := bstep (se 1 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 331763 = 497645) B497645
theorem B331779 : Blo 330750 331779 := bstep (se 1 (by rfl) ⟨248834, by rfl⟩ : syracuseStep 331779 = 497669) B497669
theorem B2854925 : Blo 330750 2854925 := bstep (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) B1070597
theorem B757777 : Blo 330750 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B331795 : Blo 330750 331795 := bstep (se 1 (by rfl) ⟨248846, by rfl⟩ : syracuseStep 331795 = 497693) B497693
theorem B331811 : Blo 330750 331811 := bstep (se 1 (by rfl) ⟨248858, by rfl⟩ : syracuseStep 331811 = 497717) B497717
theorem B331827 : Blo 330750 331827 := bstep (se 1 (by rfl) ⟨248870, by rfl⟩ : syracuseStep 331827 = 497741) B497741
theorem B331843 : Blo 330750 331843 := bstep (se 1 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 331843 = 497765) B497765
theorem B1413197 : Blo 330750 1413197 := bstep (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) B529949
theorem B1118285 : Blo 330750 1118285 := bstep (se 3 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 1118285 = 419357) B419357
theorem B331859 : Blo 330750 331859 := bstep (se 1 (by rfl) ⟨248894, by rfl⟩ : syracuseStep 331859 = 497789) B497789
theorem B561235 : Blo 330750 561235 := bstep (se 1 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 561235 = 841853) B841853
theorem B331875 : Blo 330750 331875 := bstep (se 1 (by rfl) ⟨248906, by rfl⟩ : syracuseStep 331875 = 497813) B497813
theorem B331891 : Blo 330750 331891 := bstep (se 1 (by rfl) ⟨248918, by rfl⟩ : syracuseStep 331891 = 497837) B497837
theorem B1118339 : Blo 330750 1118339 := bstep (se 1 (by rfl) ⟨838754, by rfl⟩ : syracuseStep 1118339 = 1677509) B1677509
theorem B331907 : Blo 330750 331907 := bstep (se 1 (by rfl) ⟨248930, by rfl⟩ : syracuseStep 331907 = 497861) B497861
theorem B331923 : Blo 330750 331923 := bstep (se 1 (by rfl) ⟨248942, by rfl⟩ : syracuseStep 331923 = 497885) B497885
theorem B331939 : Blo 330750 331939 := bstep (se 1 (by rfl) ⟨248954, by rfl⟩ : syracuseStep 331939 = 497909) B497909
theorem B331955 : Blo 330750 331955 := bstep (se 1 (by rfl) ⟨248966, by rfl⟩ : syracuseStep 331955 = 497933) B497933
theorem B331971 : Blo 330750 331971 := bstep (se 1 (by rfl) ⟨248978, by rfl⟩ : syracuseStep 331971 = 497957) B497957
theorem B331987 : Blo 330750 331987 := bstep (se 1 (by rfl) ⟨248990, by rfl⟩ : syracuseStep 331987 = 497981) B497981
theorem B561377 : Blo 330750 561377 := bstep (se 2 (by rfl) ⟨210516, by rfl⟩ : syracuseStep 561377 = 421033) B421033
theorem B332003 : Blo 330750 332003 := bstep (se 1 (by rfl) ⟨249002, by rfl⟩ : syracuseStep 332003 = 498005) B498005
theorem B332019 : Blo 330750 332019 := bstep (se 1 (by rfl) ⟨249014, by rfl⟩ : syracuseStep 332019 = 498029) B498029
theorem B332035 : Blo 330750 332035 := bstep (se 1 (by rfl) ⟨249026, by rfl⟩ : syracuseStep 332035 = 498053) B498053
theorem B332051 : Blo 330750 332051 := bstep (se 1 (by rfl) ⟨249038, by rfl⟩ : syracuseStep 332051 = 498077) B498077
theorem B332067 : Blo 330750 332067 := bstep (se 1 (by rfl) ⟨249050, by rfl⟩ : syracuseStep 332067 = 498101) B498101
theorem B332083 : Blo 330750 332083 := bstep (se 1 (by rfl) ⟨249062, by rfl⟩ : syracuseStep 332083 = 498125) B498125
theorem B332099 : Blo 330750 332099 := bstep (se 1 (by rfl) ⟨249074, by rfl⟩ : syracuseStep 332099 = 498149) B498149
theorem B332115 : Blo 330750 332115 := bstep (se 1 (by rfl) ⟨249086, by rfl⟩ : syracuseStep 332115 = 498173) B498173
theorem B561505 : Blo 330750 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B332131 : Blo 330750 332131 := bstep (se 1 (by rfl) ⟨249098, by rfl⟩ : syracuseStep 332131 = 498197) B498197
theorem B332147 : Blo 330750 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B332163 : Blo 330750 332163 := bstep (se 1 (by rfl) ⟨249122, by rfl⟩ : syracuseStep 332163 = 498245) B498245
theorem B561539 : Blo 330750 561539 := bstep (se 1 (by rfl) ⟨421154, by rfl⟩ : syracuseStep 561539 = 842309) B842309
theorem B1118609 : Blo 330750 1118609 := bstep (se 2 (by rfl) ⟨419478, by rfl⟩ : syracuseStep 1118609 = 838957) B838957
theorem B332179 : Blo 330750 332179 := bstep (se 1 (by rfl) ⟨249134, by rfl⟩ : syracuseStep 332179 = 498269) B498269
theorem B332195 : Blo 330750 332195 := bstep (se 1 (by rfl) ⟨249146, by rfl⟩ : syracuseStep 332195 = 498293) B498293
theorem B1905059 : Blo 330750 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B332211 : Blo 330750 332211 := bstep (se 1 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 332211 = 498317) B498317
theorem B332227 : Blo 330750 332227 := bstep (se 1 (by rfl) ⟨249170, by rfl⟩ : syracuseStep 332227 = 498341) B498341
theorem B627139 : Blo 330750 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B2527685 : Blo 330750 2527685 := bstep (se 4 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 2527685 = 473941) B473941
theorem B332243 : Blo 330750 332243 := bstep (se 1 (by rfl) ⟨249182, by rfl⟩ : syracuseStep 332243 = 498365) B498365
theorem B332259 : Blo 330750 332259 := bstep (se 1 (by rfl) ⟨249194, by rfl⟩ : syracuseStep 332259 = 498389) B498389
theorem B332275 : Blo 330750 332275 := bstep (se 1 (by rfl) ⟨249206, by rfl⟩ : syracuseStep 332275 = 498413) B498413
theorem B332291 : Blo 330750 332291 := bstep (se 1 (by rfl) ⟨249218, by rfl⟩ : syracuseStep 332291 = 498437) B498437
theorem B561667 : Blo 330750 561667 := bstep (se 1 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 561667 = 842501) B842501
theorem B496145 : Blo 330750 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B332307 : Blo 330750 332307 := bstep (se 1 (by rfl) ⟨249230, by rfl⟩ : syracuseStep 332307 = 498461) B498461
theorem B496163 : Blo 330750 496163 := bstep (se 1 (by rfl) ⟨372122, by rfl⟩ : syracuseStep 496163 = 744245) B744245
theorem B332323 : Blo 330750 332323 := bstep (se 1 (by rfl) ⟨249242, by rfl⟩ : syracuseStep 332323 = 498485) B498485
theorem B332339 : Blo 330750 332339 := bstep (se 1 (by rfl) ⟨249254, by rfl⟩ : syracuseStep 332339 = 498509) B498509
theorem B496193 : Blo 330750 496193 := bstep (se 2 (by rfl) ⟨186072, by rfl⟩ : syracuseStep 496193 = 372145) B372145
theorem B332355 : Blo 330750 332355 := bstep (se 1 (by rfl) ⟨249266, by rfl⟩ : syracuseStep 332355 = 498533) B498533
theorem B496211 : Blo 330750 496211 := bstep (se 1 (by rfl) ⟨372158, by rfl⟩ : syracuseStep 496211 = 744317) B744317
theorem B332371 : Blo 330750 332371 := bstep (se 1 (by rfl) ⟨249278, by rfl⟩ : syracuseStep 332371 = 498557) B498557
theorem B332387 : Blo 330750 332387 := bstep (se 1 (by rfl) ⟨249290, by rfl⟩ : syracuseStep 332387 = 498581) B498581
theorem B496241 : Blo 330750 496241 := bstep (se 2 (by rfl) ⟨186090, by rfl⟩ : syracuseStep 496241 = 372181) B372181
theorem B1675889 : Blo 330750 1675889 := bstep (se 2 (by rfl) ⟨628458, by rfl⟩ : syracuseStep 1675889 = 1256917) B1256917
theorem B332403 : Blo 330750 332403 := bstep (se 1 (by rfl) ⟨249302, by rfl⟩ : syracuseStep 332403 = 498605) B498605
theorem B496259 : Blo 330750 496259 := bstep (se 1 (by rfl) ⟨372194, by rfl⟩ : syracuseStep 496259 = 744389) B744389
theorem B332419 : Blo 330750 332419 := bstep (se 1 (by rfl) ⟨249314, by rfl⟩ : syracuseStep 332419 = 498629) B498629
theorem B561809 : Blo 330750 561809 := bstep (se 2 (by rfl) ⟨210678, by rfl⟩ : syracuseStep 561809 = 421357) B421357
theorem B332435 : Blo 330750 332435 := bstep (se 1 (by rfl) ⟨249326, by rfl⟩ : syracuseStep 332435 = 498653) B498653
theorem B496289 : Blo 330750 496289 := bstep (se 2 (by rfl) ⟨186108, by rfl⟩ : syracuseStep 496289 = 372217) B372217
theorem B332451 : Blo 330750 332451 := bstep (se 1 (by rfl) ⟨249338, by rfl⟩ : syracuseStep 332451 = 498677) B498677
theorem B496307 : Blo 330750 496307 := bstep (se 1 (by rfl) ⟨372230, by rfl⟩ : syracuseStep 496307 = 744461) B744461
theorem B332467 : Blo 330750 332467 := bstep (se 1 (by rfl) ⟨249350, by rfl⟩ : syracuseStep 332467 = 498701) B498701
theorem B332483 : Blo 330750 332483 := bstep (se 1 (by rfl) ⟨249362, by rfl⟩ : syracuseStep 332483 = 498725) B498725
theorem B496337 : Blo 330750 496337 := bstep (se 2 (by rfl) ⟨186126, by rfl⟩ : syracuseStep 496337 = 372253) B372253
theorem B332499 : Blo 330750 332499 := bstep (se 1 (by rfl) ⟨249374, by rfl⟩ : syracuseStep 332499 = 498749) B498749
theorem B496355 : Blo 330750 496355 := bstep (se 1 (by rfl) ⟨372266, by rfl⟩ : syracuseStep 496355 = 744533) B744533
theorem B332515 : Blo 330750 332515 := bstep (se 1 (by rfl) ⟨249386, by rfl⟩ : syracuseStep 332515 = 498773) B498773
theorem B332531 : Blo 330750 332531 := bstep (se 1 (by rfl) ⟨249398, by rfl⟩ : syracuseStep 332531 = 498797) B498797
theorem B496385 : Blo 330750 496385 := bstep (se 2 (by rfl) ⟨186144, by rfl⟩ : syracuseStep 496385 = 372289) B372289
theorem B332547 : Blo 330750 332547 := bstep (se 1 (by rfl) ⟨249410, by rfl⟩ : syracuseStep 332547 = 498821) B498821
theorem B561937 : Blo 330750 561937 := bstep (se 2 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 561937 = 421453) B421453
theorem B496403 : Blo 330750 496403 := bstep (se 1 (by rfl) ⟨372302, by rfl⟩ : syracuseStep 496403 = 744605) B744605
theorem B332563 : Blo 330750 332563 := bstep (se 1 (by rfl) ⟨249422, by rfl⟩ : syracuseStep 332563 = 498845) B498845
theorem B332579 : Blo 330750 332579 := bstep (se 1 (by rfl) ⟨249434, by rfl⟩ : syracuseStep 332579 = 498869) B498869
theorem B496433 : Blo 330750 496433 := bstep (se 2 (by rfl) ⟨186162, by rfl⟩ : syracuseStep 496433 = 372325) B372325
theorem B332595 : Blo 330750 332595 := bstep (se 1 (by rfl) ⟨249446, by rfl⟩ : syracuseStep 332595 = 498893) B498893
theorem B561971 : Blo 330750 561971 := bstep (se 1 (by rfl) ⟨421478, by rfl⟩ : syracuseStep 561971 = 842957) B842957
theorem B496451 : Blo 330750 496451 := bstep (se 1 (by rfl) ⟨372338, by rfl⟩ : syracuseStep 496451 = 744677) B744677
theorem B332611 : Blo 330750 332611 := bstep (se 1 (by rfl) ⟨249458, by rfl⟩ : syracuseStep 332611 = 498917) B498917
theorem B332627 : Blo 330750 332627 := bstep (se 1 (by rfl) ⟨249470, by rfl⟩ : syracuseStep 332627 = 498941) B498941
theorem B496481 : Blo 330750 496481 := bstep (se 2 (by rfl) ⟨186180, by rfl⟩ : syracuseStep 496481 = 372361) B372361
theorem B332643 : Blo 330750 332643 := bstep (se 1 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 332643 = 498965) B498965
theorem B496499 : Blo 330750 496499 := bstep (se 1 (by rfl) ⟨372374, by rfl⟩ : syracuseStep 496499 = 744749) B744749
theorem B332659 : Blo 330750 332659 := bstep (se 1 (by rfl) ⟨249494, by rfl⟩ : syracuseStep 332659 = 498989) B498989
theorem B332675 : Blo 330750 332675 := bstep (se 1 (by rfl) ⟨249506, by rfl⟩ : syracuseStep 332675 = 499013) B499013
theorem B496529 : Blo 330750 496529 := bstep (se 2 (by rfl) ⟨186198, by rfl⟩ : syracuseStep 496529 = 372397) B372397
theorem B332691 : Blo 330750 332691 := bstep (se 1 (by rfl) ⟨249518, by rfl⟩ : syracuseStep 332691 = 499037) B499037
theorem B496547 : Blo 330750 496547 := bstep (se 1 (by rfl) ⟨372410, by rfl⟩ : syracuseStep 496547 = 744821) B744821
theorem B332707 : Blo 330750 332707 := bstep (se 1 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 332707 = 499061) B499061
theorem B1119149 : Blo 330750 1119149 := bstep (se 3 (by rfl) ⟨209840, by rfl⟩ : syracuseStep 1119149 = 419681) B419681
theorem B332723 : Blo 330750 332723 := bstep (se 1 (by rfl) ⟨249542, by rfl⟩ : syracuseStep 332723 = 499085) B499085
theorem B562099 : Blo 330750 562099 := bstep (se 1 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 562099 = 843149) B843149
theorem B496577 : Blo 330750 496577 := bstep (se 2 (by rfl) ⟨186216, by rfl⟩ : syracuseStep 496577 = 372433) B372433
theorem B332739 : Blo 330750 332739 := bstep (se 1 (by rfl) ⟨249554, by rfl⟩ : syracuseStep 332739 = 499109) B499109
theorem B496595 : Blo 330750 496595 := bstep (se 1 (by rfl) ⟨372446, by rfl⟩ : syracuseStep 496595 = 744893) B744893
theorem B332755 : Blo 330750 332755 := bstep (se 1 (by rfl) ⟨249566, by rfl⟩ : syracuseStep 332755 = 499133) B499133
theorem B1119203 : Blo 330750 1119203 := bstep (se 1 (by rfl) ⟨839402, by rfl⟩ : syracuseStep 1119203 = 1678805) B1678805
theorem B332771 : Blo 330750 332771 := bstep (se 1 (by rfl) ⟨249578, by rfl⟩ : syracuseStep 332771 = 499157) B499157
theorem B496625 : Blo 330750 496625 := bstep (se 2 (by rfl) ⟨186234, by rfl⟩ : syracuseStep 496625 = 372469) B372469
theorem B332787 : Blo 330750 332787 := bstep (se 1 (by rfl) ⟨249590, by rfl⟩ : syracuseStep 332787 = 499181) B499181
theorem B496643 : Blo 330750 496643 := bstep (se 1 (by rfl) ⟨372482, by rfl⟩ : syracuseStep 496643 = 744965) B744965
theorem B332803 : Blo 330750 332803 := bstep (se 1 (by rfl) ⟨249602, by rfl⟩ : syracuseStep 332803 = 499205) B499205
theorem B332819 : Blo 330750 332819 := bstep (se 1 (by rfl) ⟨249614, by rfl⟩ : syracuseStep 332819 = 499229) B499229
theorem B496673 : Blo 330750 496673 := bstep (se 2 (by rfl) ⟨186252, by rfl⟩ : syracuseStep 496673 = 372505) B372505
theorem B332835 : Blo 330750 332835 := bstep (se 1 (by rfl) ⟨249626, by rfl⟩ : syracuseStep 332835 = 499253) B499253
theorem B496691 : Blo 330750 496691 := bstep (se 1 (by rfl) ⟨372518, by rfl⟩ : syracuseStep 496691 = 745037) B745037
theorem B332851 : Blo 330750 332851 := bstep (se 1 (by rfl) ⟨249638, by rfl⟩ : syracuseStep 332851 = 499277) B499277
theorem B562241 : Blo 330750 562241 := bstep (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) B421681
theorem B332867 : Blo 330750 332867 := bstep (se 1 (by rfl) ⟨249650, by rfl⟩ : syracuseStep 332867 = 499301) B499301
theorem B496721 : Blo 330750 496721 := bstep (se 2 (by rfl) ⟨186270, by rfl⟩ : syracuseStep 496721 = 372541) B372541
theorem B332883 : Blo 330750 332883 := bstep (se 1 (by rfl) ⟨249662, by rfl⟩ : syracuseStep 332883 = 499325) B499325
theorem B496739 : Blo 330750 496739 := bstep (se 1 (by rfl) ⟨372554, by rfl⟩ : syracuseStep 496739 = 745109) B745109
theorem B332899 : Blo 330750 332899 := bstep (se 1 (by rfl) ⟨249674, by rfl⟩ : syracuseStep 332899 = 499349) B499349
theorem B6362225 : Blo 330750 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B332915 : Blo 330750 332915 := bstep (se 1 (by rfl) ⟨249686, by rfl⟩ : syracuseStep 332915 = 499373) B499373
theorem B496769 : Blo 330750 496769 := bstep (se 2 (by rfl) ⟨186288, by rfl⟩ : syracuseStep 496769 = 372577) B372577
theorem B332931 : Blo 330750 332931 := bstep (se 1 (by rfl) ⟨249698, by rfl⟩ : syracuseStep 332931 = 499397) B499397
theorem B496787 : Blo 330750 496787 := bstep (se 1 (by rfl) ⟨372590, by rfl⟩ : syracuseStep 496787 = 745181) B745181
theorem B332947 : Blo 330750 332947 := bstep (se 1 (by rfl) ⟨249710, by rfl⟩ : syracuseStep 332947 = 499421) B499421
theorem B332963 : Blo 330750 332963 := bstep (se 1 (by rfl) ⟨249722, by rfl⟩ : syracuseStep 332963 = 499445) B499445
theorem B496817 : Blo 330750 496817 := bstep (se 2 (by rfl) ⟨186306, by rfl⟩ : syracuseStep 496817 = 372613) B372613
theorem B332979 : Blo 330750 332979 := bstep (se 1 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 332979 = 499469) B499469
theorem B562369 : Blo 330750 562369 := bstep (se 2 (by rfl) ⟨210888, by rfl⟩ : syracuseStep 562369 = 421777) B421777
theorem B496835 : Blo 330750 496835 := bstep (se 1 (by rfl) ⟨372626, by rfl⟩ : syracuseStep 496835 = 745253) B745253
theorem B332995 : Blo 330750 332995 := bstep (se 1 (by rfl) ⟨249746, by rfl⟩ : syracuseStep 332995 = 499493) B499493
theorem B955601 : Blo 330750 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B333011 : Blo 330750 333011 := bstep (se 1 (by rfl) ⟨249758, by rfl⟩ : syracuseStep 333011 = 499517) B499517
theorem B496865 : Blo 330750 496865 := bstep (se 2 (by rfl) ⟨186324, by rfl⟩ : syracuseStep 496865 = 372649) B372649
theorem B333027 : Blo 330750 333027 := bstep (se 1 (by rfl) ⟨249770, by rfl⟩ : syracuseStep 333027 = 499541) B499541
theorem B562403 : Blo 330750 562403 := bstep (se 1 (by rfl) ⟨421802, by rfl⟩ : syracuseStep 562403 = 843605) B843605
theorem B1119473 : Blo 330750 1119473 := bstep (se 2 (by rfl) ⟨419802, by rfl⟩ : syracuseStep 1119473 = 839605) B839605
theorem B496883 : Blo 330750 496883 := bstep (se 1 (by rfl) ⟨372662, by rfl⟩ : syracuseStep 496883 = 745325) B745325
theorem B333043 : Blo 330750 333043 := bstep (se 1 (by rfl) ⟨249782, by rfl⟩ : syracuseStep 333043 = 499565) B499565
theorem B333059 : Blo 330750 333059 := bstep (se 1 (by rfl) ⟨249794, by rfl⟩ : syracuseStep 333059 = 499589) B499589
theorem B496913 : Blo 330750 496913 := bstep (se 2 (by rfl) ⟨186342, by rfl⟩ : syracuseStep 496913 = 372685) B372685
theorem B333075 : Blo 330750 333075 := bstep (se 1 (by rfl) ⟨249806, by rfl⟩ : syracuseStep 333075 = 499613) B499613
theorem B628003 : Blo 330750 628003 := bstep (se 1 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 628003 = 942005) B942005
theorem B496931 : Blo 330750 496931 := bstep (se 1 (by rfl) ⟨372698, by rfl⟩ : syracuseStep 496931 = 745397) B745397
theorem B333091 : Blo 330750 333091 := bstep (se 1 (by rfl) ⟨249818, by rfl⟩ : syracuseStep 333091 = 499637) B499637
theorem B333107 : Blo 330750 333107 := bstep (se 1 (by rfl) ⟨249830, by rfl⟩ : syracuseStep 333107 = 499661) B499661
theorem B496961 : Blo 330750 496961 := bstep (se 2 (by rfl) ⟨186360, by rfl⟩ : syracuseStep 496961 = 372721) B372721
theorem B333123 : Blo 330750 333123 := bstep (se 1 (by rfl) ⟨249842, by rfl⟩ : syracuseStep 333123 = 499685) B499685
theorem B628049 : Blo 330750 628049 := bstep (se 2 (by rfl) ⟨235518, by rfl⟩ : syracuseStep 628049 = 471037) B471037
theorem B496979 : Blo 330750 496979 := bstep (se 1 (by rfl) ⟨372734, by rfl⟩ : syracuseStep 496979 = 745469) B745469
theorem B333139 : Blo 330750 333139 := bstep (se 1 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 333139 = 499709) B499709
theorem B333155 : Blo 330750 333155 := bstep (se 1 (by rfl) ⟨249866, by rfl⟩ : syracuseStep 333155 = 499733) B499733
theorem B562531 : Blo 330750 562531 := bstep (se 1 (by rfl) ⟨421898, by rfl⟩ : syracuseStep 562531 = 843797) B843797
theorem B497009 : Blo 330750 497009 := bstep (se 2 (by rfl) ⟨186378, by rfl⟩ : syracuseStep 497009 = 372757) B372757
theorem B333171 : Blo 330750 333171 := bstep (se 1 (by rfl) ⟨249878, by rfl⟩ : syracuseStep 333171 = 499757) B499757
theorem B497027 : Blo 330750 497027 := bstep (se 1 (by rfl) ⟨372770, by rfl⟩ : syracuseStep 497027 = 745541) B745541
theorem B333187 : Blo 330750 333187 := bstep (se 1 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 333187 = 499781) B499781
theorem B333203 : Blo 330750 333203 := bstep (se 1 (by rfl) ⟨249902, by rfl⟩ : syracuseStep 333203 = 499805) B499805
theorem B497057 : Blo 330750 497057 := bstep (se 2 (by rfl) ⟨186396, by rfl⟩ : syracuseStep 497057 = 372793) B372793
theorem B333219 : Blo 330750 333219 := bstep (se 1 (by rfl) ⟨249914, by rfl⟩ : syracuseStep 333219 = 499829) B499829
theorem B497075 : Blo 330750 497075 := bstep (se 1 (by rfl) ⟨372806, by rfl⟩ : syracuseStep 497075 = 745613) B745613
theorem B333235 : Blo 330750 333235 := bstep (se 1 (by rfl) ⟨249926, by rfl⟩ : syracuseStep 333235 = 499853) B499853
theorem B333251 : Blo 330750 333251 := bstep (se 1 (by rfl) ⟨249938, by rfl⟩ : syracuseStep 333251 = 499877) B499877
theorem B497105 : Blo 330750 497105 := bstep (se 2 (by rfl) ⟨186414, by rfl⟩ : syracuseStep 497105 = 372829) B372829
theorem B333267 : Blo 330750 333267 := bstep (se 1 (by rfl) ⟨249950, by rfl⟩ : syracuseStep 333267 = 499901) B499901
theorem B497123 : Blo 330750 497123 := bstep (se 1 (by rfl) ⟨372842, by rfl⟩ : syracuseStep 497123 = 745685) B745685
theorem B333283 : Blo 330750 333283 := bstep (se 1 (by rfl) ⟨249962, by rfl⟩ : syracuseStep 333283 = 499925) B499925
theorem B562673 : Blo 330750 562673 := bstep (se 2 (by rfl) ⟨211002, by rfl⟩ : syracuseStep 562673 = 422005) B422005
theorem B333299 : Blo 330750 333299 := bstep (se 1 (by rfl) ⟨249974, by rfl⟩ : syracuseStep 333299 = 499949) B499949
theorem B497153 : Blo 330750 497153 := bstep (se 2 (by rfl) ⟨186432, by rfl⟩ : syracuseStep 497153 = 372865) B372865
theorem B333315 : Blo 330750 333315 := bstep (se 1 (by rfl) ⟨249986, by rfl⟩ : syracuseStep 333315 = 499973) B499973
theorem B497171 : Blo 330750 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B333331 : Blo 330750 333331 := bstep (se 1 (by rfl) ⟨249998, by rfl⟩ : syracuseStep 333331 = 499997) B499997
theorem B333347 : Blo 330750 333347 := bstep (se 1 (by rfl) ⟨250010, by rfl⟩ : syracuseStep 333347 = 500021) B500021
theorem B497201 : Blo 330750 497201 := bstep (se 2 (by rfl) ⟨186450, by rfl⟩ : syracuseStep 497201 = 372901) B372901
theorem B333363 : Blo 330750 333363 := bstep (se 1 (by rfl) ⟨250022, by rfl⟩ : syracuseStep 333363 = 500045) B500045
theorem B497219 : Blo 330750 497219 := bstep (se 1 (by rfl) ⟨372914, by rfl⟩ : syracuseStep 497219 = 745829) B745829
theorem B333379 : Blo 330750 333379 := bstep (se 1 (by rfl) ⟨250034, by rfl⟩ : syracuseStep 333379 = 500069) B500069
theorem B333395 : Blo 330750 333395 := bstep (se 1 (by rfl) ⟨250046, by rfl⟩ : syracuseStep 333395 = 500093) B500093
theorem B497249 : Blo 330750 497249 := bstep (se 2 (by rfl) ⟨186468, by rfl⟩ : syracuseStep 497249 = 372937) B372937
theorem B398947 : Blo 330750 398947 := bstep (se 1 (by rfl) ⟨299210, by rfl⟩ : syracuseStep 398947 = 598421) B598421
theorem B333411 : Blo 330750 333411 := bstep (se 1 (by rfl) ⟨250058, by rfl⟩ : syracuseStep 333411 = 500117) B500117
theorem B628337 : Blo 330750 628337 := bstep (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) B471253
theorem B562801 : Blo 330750 562801 := bstep (se 2 (by rfl) ⟨211050, by rfl⟩ : syracuseStep 562801 = 422101) B422101
theorem B497267 : Blo 330750 497267 := bstep (se 1 (by rfl) ⟨372950, by rfl⟩ : syracuseStep 497267 = 745901) B745901
theorem B333427 : Blo 330750 333427 := bstep (se 1 (by rfl) ⟨250070, by rfl⟩ : syracuseStep 333427 = 500141) B500141
theorem B333443 : Blo 330750 333443 := bstep (se 1 (by rfl) ⟨250082, by rfl⟩ : syracuseStep 333443 = 500165) B500165
theorem B497297 : Blo 330750 497297 := bstep (se 2 (by rfl) ⟨186486, by rfl⟩ : syracuseStep 497297 = 372973) B372973
theorem B333459 : Blo 330750 333459 := bstep (se 1 (by rfl) ⟨250094, by rfl⟩ : syracuseStep 333459 = 500189) B500189
theorem B562835 : Blo 330750 562835 := bstep (se 1 (by rfl) ⟨422126, by rfl⟩ : syracuseStep 562835 = 844253) B844253
theorem B497315 : Blo 330750 497315 := bstep (se 1 (by rfl) ⟨372986, by rfl⟩ : syracuseStep 497315 = 745973) B745973
theorem B333475 : Blo 330750 333475 := bstep (se 1 (by rfl) ⟨250106, by rfl⟩ : syracuseStep 333475 = 500213) B500213
theorem B333491 : Blo 330750 333491 := bstep (se 1 (by rfl) ⟨250118, by rfl⟩ : syracuseStep 333491 = 500237) B500237
theorem B497345 : Blo 330750 497345 := bstep (se 2 (by rfl) ⟨186504, by rfl⟩ : syracuseStep 497345 = 373009) B373009
theorem B333507 : Blo 330750 333507 := bstep (se 1 (by rfl) ⟨250130, by rfl⟩ : syracuseStep 333507 = 500261) B500261
theorem B497363 : Blo 330750 497363 := bstep (se 1 (by rfl) ⟨373022, by rfl⟩ : syracuseStep 497363 = 746045) B746045
theorem B333523 : Blo 330750 333523 := bstep (se 1 (by rfl) ⟨250142, by rfl⟩ : syracuseStep 333523 = 500285) B500285
theorem B333539 : Blo 330750 333539 := bstep (se 1 (by rfl) ⟨250154, by rfl⟩ : syracuseStep 333539 = 500309) B500309
theorem B497393 : Blo 330750 497393 := bstep (se 2 (by rfl) ⟨186522, by rfl⟩ : syracuseStep 497393 = 373045) B373045
theorem B333555 : Blo 330750 333555 := bstep (se 1 (by rfl) ⟨250166, by rfl⟩ : syracuseStep 333555 = 500333) B500333
theorem B497411 : Blo 330750 497411 := bstep (se 1 (by rfl) ⟨373058, by rfl⟩ : syracuseStep 497411 = 746117) B746117
theorem B333571 : Blo 330750 333571 := bstep (se 1 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 333571 = 500357) B500357
theorem B1120013 : Blo 330750 1120013 := bstep (se 3 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 1120013 = 420005) B420005
theorem B333587 : Blo 330750 333587 := bstep (se 1 (by rfl) ⟨250190, by rfl⟩ : syracuseStep 333587 = 500381) B500381
theorem B562963 : Blo 330750 562963 := bstep (se 1 (by rfl) ⟨422222, by rfl⟩ : syracuseStep 562963 = 844445) B844445
theorem B497441 : Blo 330750 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B333603 : Blo 330750 333603 := bstep (se 1 (by rfl) ⟨250202, by rfl⟩ : syracuseStep 333603 = 500405) B500405
theorem B497459 : Blo 330750 497459 := bstep (se 1 (by rfl) ⟨373094, by rfl⟩ : syracuseStep 497459 = 746189) B746189
theorem B333619 : Blo 330750 333619 := bstep (se 1 (by rfl) ⟨250214, by rfl⟩ : syracuseStep 333619 = 500429) B500429
theorem B1120067 : Blo 330750 1120067 := bstep (se 1 (by rfl) ⟨840050, by rfl⟩ : syracuseStep 1120067 = 1680101) B1680101
theorem B333635 : Blo 330750 333635 := bstep (se 1 (by rfl) ⟨250226, by rfl⟩ : syracuseStep 333635 = 500453) B500453
theorem B497489 : Blo 330750 497489 := bstep (se 2 (by rfl) ⟨186558, by rfl⟩ : syracuseStep 497489 = 373117) B373117
theorem B333651 : Blo 330750 333651 := bstep (se 1 (by rfl) ⟨250238, by rfl⟩ : syracuseStep 333651 = 500477) B500477
theorem B497507 : Blo 330750 497507 := bstep (se 1 (by rfl) ⟨373130, by rfl⟩ : syracuseStep 497507 = 746261) B746261
theorem B1709923 : Blo 330750 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B333667 : Blo 330750 333667 := bstep (se 1 (by rfl) ⟨250250, by rfl⟩ : syracuseStep 333667 = 500501) B500501
theorem B333683 : Blo 330750 333683 := bstep (se 1 (by rfl) ⟨250262, by rfl⟩ : syracuseStep 333683 = 500525) B500525
theorem B497537 : Blo 330750 497537 := bstep (se 2 (by rfl) ⟨186576, by rfl⟩ : syracuseStep 497537 = 373153) B373153
theorem B399235 : Blo 330750 399235 := bstep (se 1 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 399235 = 598853) B598853
theorem B333699 : Blo 330750 333699 := bstep (se 1 (by rfl) ⟨250274, by rfl⟩ : syracuseStep 333699 = 500549) B500549
theorem B497555 : Blo 330750 497555 := bstep (se 1 (by rfl) ⟨373166, by rfl⟩ : syracuseStep 497555 = 746333) B746333
theorem B333715 : Blo 330750 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B563105 : Blo 330750 563105 := bstep (se 2 (by rfl) ⟨211164, by rfl⟩ : syracuseStep 563105 = 422329) B422329
theorem B333731 : Blo 330750 333731 := bstep (se 1 (by rfl) ⟨250298, by rfl⟩ : syracuseStep 333731 = 500597) B500597
theorem B497585 : Blo 330750 497585 := bstep (se 2 (by rfl) ⟨186594, by rfl⟩ : syracuseStep 497585 = 373189) B373189
theorem B333747 : Blo 330750 333747 := bstep (se 1 (by rfl) ⟨250310, by rfl⟩ : syracuseStep 333747 = 500621) B500621
theorem B497603 : Blo 330750 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B333763 : Blo 330750 333763 := bstep (se 1 (by rfl) ⟨250322, by rfl⟩ : syracuseStep 333763 = 500645) B500645
theorem B333779 : Blo 330750 333779 := bstep (se 1 (by rfl) ⟨250334, by rfl⟩ : syracuseStep 333779 = 500669) B500669
theorem B497633 : Blo 330750 497633 := bstep (se 2 (by rfl) ⟨186612, by rfl⟩ : syracuseStep 497633 = 373225) B373225
theorem B399331 : Blo 330750 399331 := bstep (se 1 (by rfl) ⟨299498, by rfl⟩ : syracuseStep 399331 = 598997) B598997
theorem B333795 : Blo 330750 333795 := bstep (se 1 (by rfl) ⟨250346, by rfl⟩ : syracuseStep 333795 = 500693) B500693
theorem B497651 : Blo 330750 497651 := bstep (se 1 (by rfl) ⟨373238, by rfl⟩ : syracuseStep 497651 = 746477) B746477
theorem B333811 : Blo 330750 333811 := bstep (se 1 (by rfl) ⟨250358, by rfl⟩ : syracuseStep 333811 = 500717) B500717
theorem B333827 : Blo 330750 333827 := bstep (se 1 (by rfl) ⟨250370, by rfl⟩ : syracuseStep 333827 = 500741) B500741
theorem B497681 : Blo 330750 497681 := bstep (se 2 (by rfl) ⟨186630, by rfl⟩ : syracuseStep 497681 = 373261) B373261
theorem B333843 : Blo 330750 333843 := bstep (se 1 (by rfl) ⟨250382, by rfl⟩ : syracuseStep 333843 = 500765) B500765
theorem B563233 : Blo 330750 563233 := bstep (se 2 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 563233 = 422425) B422425
theorem B1677347 : Blo 330750 1677347 := bstep (se 1 (by rfl) ⟨1258010, by rfl⟩ : syracuseStep 1677347 = 2516021) B2516021
theorem B497699 : Blo 330750 497699 := bstep (se 1 (by rfl) ⟨373274, by rfl⟩ : syracuseStep 497699 = 746549) B746549
theorem B333859 : Blo 330750 333859 := bstep (se 1 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 333859 = 500789) B500789
theorem B333875 : Blo 330750 333875 := bstep (se 1 (by rfl) ⟨250406, by rfl⟩ : syracuseStep 333875 = 500813) B500813
theorem B497729 : Blo 330750 497729 := bstep (se 2 (by rfl) ⟨186648, by rfl⟩ : syracuseStep 497729 = 373297) B373297
theorem B563267 : Blo 330750 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B333891 : Blo 330750 333891 := bstep (se 1 (by rfl) ⟨250418, by rfl⟩ : syracuseStep 333891 = 500837) B500837
theorem B1120337 : Blo 330750 1120337 := bstep (se 2 (by rfl) ⟨420126, by rfl⟩ : syracuseStep 1120337 = 840253) B840253
theorem B497747 : Blo 330750 497747 := bstep (se 1 (by rfl) ⟨373310, by rfl⟩ : syracuseStep 497747 = 746621) B746621
theorem B333907 : Blo 330750 333907 := bstep (se 1 (by rfl) ⟨250430, by rfl⟩ : syracuseStep 333907 = 500861) B500861
theorem B333923 : Blo 330750 333923 := bstep (se 1 (by rfl) ⟨250442, by rfl⟩ : syracuseStep 333923 = 500885) B500885
theorem B530545 : Blo 330750 530545 := bstep (se 2 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 530545 = 397909) B397909
theorem B497777 : Blo 330750 497777 := bstep (se 2 (by rfl) ⟨186666, by rfl⟩ : syracuseStep 497777 = 373333) B373333
theorem B399475 : Blo 330750 399475 := bstep (se 1 (by rfl) ⟨299606, by rfl⟩ : syracuseStep 399475 = 599213) B599213
theorem B333939 : Blo 330750 333939 := bstep (se 1 (by rfl) ⟨250454, by rfl⟩ : syracuseStep 333939 = 500909) B500909
theorem B497795 : Blo 330750 497795 := bstep (se 1 (by rfl) ⟨373346, by rfl⟩ : syracuseStep 497795 = 746693) B746693
theorem B333955 : Blo 330750 333955 := bstep (se 1 (by rfl) ⟨250466, by rfl⟩ : syracuseStep 333955 = 500933) B500933
theorem B333971 : Blo 330750 333971 := bstep (se 1 (by rfl) ⟨250478, by rfl⟩ : syracuseStep 333971 = 500957) B500957
theorem B497825 : Blo 330750 497825 := bstep (se 2 (by rfl) ⟨186684, by rfl⟩ : syracuseStep 497825 = 373369) B373369
theorem B333987 : Blo 330750 333987 := bstep (se 1 (by rfl) ⟨250490, by rfl⟩ : syracuseStep 333987 = 500981) B500981
theorem B497843 : Blo 330750 497843 := bstep (se 1 (by rfl) ⟨373382, by rfl⟩ : syracuseStep 497843 = 746765) B746765
theorem B334003 : Blo 330750 334003 := bstep (se 1 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 334003 = 501005) B501005
theorem B563395 : Blo 330750 563395 := bstep (se 1 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 563395 = 845093) B845093
theorem B334019 : Blo 330750 334019 := bstep (se 1 (by rfl) ⟨250514, by rfl⟩ : syracuseStep 334019 = 501029) B501029
theorem B2398405 : Blo 330750 2398405 := bstep (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) B449701
theorem B1808581 : Blo 330750 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B497873 : Blo 330750 497873 := bstep (se 2 (by rfl) ⟨186702, by rfl⟩ : syracuseStep 497873 = 373405) B373405
theorem B334035 : Blo 330750 334035 := bstep (se 1 (by rfl) ⟨250526, by rfl⟩ : syracuseStep 334035 = 501053) B501053
theorem B497891 : Blo 330750 497891 := bstep (se 1 (by rfl) ⟨373418, by rfl⟩ : syracuseStep 497891 = 746837) B746837
theorem B334051 : Blo 330750 334051 := bstep (se 1 (by rfl) ⟨250538, by rfl⟩ : syracuseStep 334051 = 501077) B501077
theorem B334067 : Blo 330750 334067 := bstep (se 1 (by rfl) ⟨250550, by rfl⟩ : syracuseStep 334067 = 501101) B501101
theorem B497921 : Blo 330750 497921 := bstep (se 2 (by rfl) ⟨186720, by rfl⟩ : syracuseStep 497921 = 373441) B373441
theorem B334083 : Blo 330750 334083 := bstep (se 1 (by rfl) ⟨250562, by rfl⟩ : syracuseStep 334083 = 501125) B501125
theorem B497939 : Blo 330750 497939 := bstep (se 1 (by rfl) ⟨373454, by rfl⟩ : syracuseStep 497939 = 746909) B746909
theorem B334099 : Blo 330750 334099 := bstep (se 1 (by rfl) ⟨250574, by rfl⟩ : syracuseStep 334099 = 501149) B501149
theorem B334115 : Blo 330750 334115 := bstep (se 1 (by rfl) ⟨250586, by rfl⟩ : syracuseStep 334115 = 501173) B501173
theorem B497969 : Blo 330750 497969 := bstep (se 2 (by rfl) ⟨186738, by rfl⟩ : syracuseStep 497969 = 373477) B373477
theorem B334131 : Blo 330750 334131 := bstep (se 1 (by rfl) ⟨250598, by rfl⟩ : syracuseStep 334131 = 501197) B501197
theorem B629059 : Blo 330750 629059 := bstep (se 1 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 629059 = 943589) B943589
theorem B497987 : Blo 330750 497987 := bstep (se 1 (by rfl) ⟨373490, by rfl⟩ : syracuseStep 497987 = 746981) B746981
theorem B334147 : Blo 330750 334147 := bstep (se 1 (by rfl) ⟨250610, by rfl⟩ : syracuseStep 334147 = 501221) B501221
theorem B563537 : Blo 330750 563537 := bstep (se 2 (by rfl) ⟨211326, by rfl⟩ : syracuseStep 563537 = 422653) B422653
theorem B334163 : Blo 330750 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B498017 : Blo 330750 498017 := bstep (se 2 (by rfl) ⟨186756, by rfl⟩ : syracuseStep 498017 = 373513) B373513
theorem B334179 : Blo 330750 334179 := bstep (se 1 (by rfl) ⟨250634, by rfl⟩ : syracuseStep 334179 = 501269) B501269
theorem B2857315 : Blo 330750 2857315 := bstep (se 1 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 2857315 = 4285973) B4285973
theorem B530801 : Blo 330750 530801 := bstep (se 2 (by rfl) ⟨199050, by rfl⟩ : syracuseStep 530801 = 398101) B398101
theorem B498035 : Blo 330750 498035 := bstep (se 1 (by rfl) ⟨373526, by rfl⟩ : syracuseStep 498035 = 747053) B747053
theorem B334195 : Blo 330750 334195 := bstep (se 1 (by rfl) ⟨250646, by rfl⟩ : syracuseStep 334195 = 501293) B501293
theorem B334211 : Blo 330750 334211 := bstep (se 1 (by rfl) ⟨250658, by rfl⟩ : syracuseStep 334211 = 501317) B501317
theorem B498065 : Blo 330750 498065 := bstep (se 2 (by rfl) ⟨186774, by rfl⟩ : syracuseStep 498065 = 373549) B373549
theorem B334227 : Blo 330750 334227 := bstep (se 1 (by rfl) ⟨250670, by rfl⟩ : syracuseStep 334227 = 501341) B501341
theorem B498083 : Blo 330750 498083 := bstep (se 1 (by rfl) ⟨373562, by rfl⟩ : syracuseStep 498083 = 747125) B747125
theorem B334243 : Blo 330750 334243 := bstep (se 1 (by rfl) ⟨250682, by rfl⟩ : syracuseStep 334243 = 501365) B501365
theorem B1022381 : Blo 330750 1022381 := bstep (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) B383393
theorem B334259 : Blo 330750 334259 := bstep (se 1 (by rfl) ⟨250694, by rfl⟩ : syracuseStep 334259 = 501389) B501389
theorem B498113 : Blo 330750 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B334275 : Blo 330750 334275 := bstep (se 1 (by rfl) ⟨250706, by rfl⟩ : syracuseStep 334275 = 501413) B501413
theorem B563665 : Blo 330750 563665 := bstep (se 2 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 563665 = 422749) B422749
theorem B498131 : Blo 330750 498131 := bstep (se 1 (by rfl) ⟨373598, by rfl⟩ : syracuseStep 498131 = 747197) B747197
theorem B334291 : Blo 330750 334291 := bstep (se 1 (by rfl) ⟨250718, by rfl⟩ : syracuseStep 334291 = 501437) B501437
theorem B334307 : Blo 330750 334307 := bstep (se 1 (by rfl) ⟨250730, by rfl⟩ : syracuseStep 334307 = 501461) B501461
theorem B498161 : Blo 330750 498161 := bstep (se 2 (by rfl) ⟨186810, by rfl⟩ : syracuseStep 498161 = 373621) B373621
theorem B563699 : Blo 330750 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B334323 : Blo 330750 334323 := bstep (se 1 (by rfl) ⟨250742, by rfl⟩ : syracuseStep 334323 = 501485) B501485
theorem B498179 : Blo 330750 498179 := bstep (se 1 (by rfl) ⟨373634, by rfl⟩ : syracuseStep 498179 = 747269) B747269
theorem B334339 : Blo 330750 334339 := bstep (se 1 (by rfl) ⟨250754, by rfl⟩ : syracuseStep 334339 = 501509) B501509
theorem B334355 : Blo 330750 334355 := bstep (se 1 (by rfl) ⟨250766, by rfl⟩ : syracuseStep 334355 = 501533) B501533
theorem B498209 : Blo 330750 498209 := bstep (se 2 (by rfl) ⟨186828, by rfl⟩ : syracuseStep 498209 = 373657) B373657
theorem B334371 : Blo 330750 334371 := bstep (se 1 (by rfl) ⟨250778, by rfl⟩ : syracuseStep 334371 = 501557) B501557
theorem B530993 : Blo 330750 530993 := bstep (se 2 (by rfl) ⟨199122, by rfl⟩ : syracuseStep 530993 = 398245) B398245
theorem B498227 : Blo 330750 498227 := bstep (se 1 (by rfl) ⟨373670, by rfl⟩ : syracuseStep 498227 = 747341) B747341
theorem B334387 : Blo 330750 334387 := bstep (se 1 (by rfl) ⟨250790, by rfl⟩ : syracuseStep 334387 = 501581) B501581
theorem B6068789 : Blo 330750 6068789 := bstep (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) B568949
theorem B334403 : Blo 330750 334403 := bstep (se 1 (by rfl) ⟨250802, by rfl⟩ : syracuseStep 334403 = 501605) B501605
theorem B4528709 : Blo 330750 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B498257 : Blo 330750 498257 := bstep (se 2 (by rfl) ⟨186846, by rfl⟩ : syracuseStep 498257 = 373693) B373693
theorem B334419 : Blo 330750 334419 := bstep (se 1 (by rfl) ⟨250814, by rfl⟩ : syracuseStep 334419 = 501629) B501629
theorem B498275 : Blo 330750 498275 := bstep (se 1 (by rfl) ⟨373706, by rfl⟩ : syracuseStep 498275 = 747413) B747413
theorem B334435 : Blo 330750 334435 := bstep (se 1 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 334435 = 501653) B501653
theorem B1120877 : Blo 330750 1120877 := bstep (se 3 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 1120877 = 420329) B420329
theorem B563827 : Blo 330750 563827 := bstep (se 1 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 563827 = 845741) B845741
theorem B334451 : Blo 330750 334451 := bstep (se 1 (by rfl) ⟨250838, by rfl⟩ : syracuseStep 334451 = 501677) B501677
theorem B498305 : Blo 330750 498305 := bstep (se 2 (by rfl) ⟨186864, by rfl⟩ : syracuseStep 498305 = 373729) B373729
theorem B334467 : Blo 330750 334467 := bstep (se 1 (by rfl) ⟨250850, by rfl⟩ : syracuseStep 334467 = 501701) B501701
theorem B498323 : Blo 330750 498323 := bstep (se 1 (by rfl) ⟨373742, by rfl⟩ : syracuseStep 498323 = 747485) B747485
theorem B334483 : Blo 330750 334483 := bstep (se 1 (by rfl) ⟨250862, by rfl⟩ : syracuseStep 334483 = 501725) B501725
theorem B465569 : Blo 330750 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B1120931 : Blo 330750 1120931 := bstep (se 1 (by rfl) ⟨840698, by rfl⟩ : syracuseStep 1120931 = 1681397) B1681397
theorem B334499 : Blo 330750 334499 := bstep (se 1 (by rfl) ⟨250874, by rfl⟩ : syracuseStep 334499 = 501749) B501749
theorem B498353 : Blo 330750 498353 := bstep (se 2 (by rfl) ⟨186882, by rfl⟩ : syracuseStep 498353 = 373765) B373765
theorem B334515 : Blo 330750 334515 := bstep (se 1 (by rfl) ⟨250886, by rfl⟩ : syracuseStep 334515 = 501773) B501773
theorem B498371 : Blo 330750 498371 := bstep (se 1 (by rfl) ⟨373778, by rfl⟩ : syracuseStep 498371 = 747557) B747557
theorem B334531 : Blo 330750 334531 := bstep (se 1 (by rfl) ⟨250898, by rfl⟩ : syracuseStep 334531 = 501797) B501797
theorem B334547 : Blo 330750 334547 := bstep (se 1 (by rfl) ⟨250910, by rfl⟩ : syracuseStep 334547 = 501821) B501821
theorem B498401 : Blo 330750 498401 := bstep (se 2 (by rfl) ⟨186900, by rfl⟩ : syracuseStep 498401 = 373801) B373801
theorem B334563 : Blo 330750 334563 := bstep (se 1 (by rfl) ⟨250922, by rfl⟩ : syracuseStep 334563 = 501845) B501845
theorem B498419 : Blo 330750 498419 := bstep (se 1 (by rfl) ⟨373814, by rfl⟩ : syracuseStep 498419 = 747629) B747629
theorem B334579 : Blo 330750 334579 := bstep (se 1 (by rfl) ⟨250934, by rfl⟩ : syracuseStep 334579 = 501869) B501869
theorem B563969 : Blo 330750 563969 := bstep (se 2 (by rfl) ⟨211488, by rfl⟩ : syracuseStep 563969 = 422977) B422977
theorem B629507 : Blo 330750 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B334595 : Blo 330750 334595 := bstep (se 1 (by rfl) ⟨250946, by rfl⟩ : syracuseStep 334595 = 501893) B501893
theorem B498449 : Blo 330750 498449 := bstep (se 2 (by rfl) ⟨186918, by rfl⟩ : syracuseStep 498449 = 373837) B373837
theorem B334611 : Blo 330750 334611 := bstep (se 1 (by rfl) ⟨250958, by rfl⟩ : syracuseStep 334611 = 501917) B501917
theorem B498467 : Blo 330750 498467 := bstep (se 1 (by rfl) ⟨373850, by rfl⟩ : syracuseStep 498467 = 747701) B747701
theorem B334627 : Blo 330750 334627 := bstep (se 1 (by rfl) ⟨250970, by rfl⟩ : syracuseStep 334627 = 501941) B501941
theorem B334643 : Blo 330750 334643 := bstep (se 1 (by rfl) ⟨250982, by rfl⟩ : syracuseStep 334643 = 501965) B501965
theorem B498497 : Blo 330750 498497 := bstep (se 2 (by rfl) ⟨186936, by rfl⟩ : syracuseStep 498497 = 373873) B373873
theorem B334659 : Blo 330750 334659 := bstep (se 1 (by rfl) ⟨250994, by rfl⟩ : syracuseStep 334659 = 501989) B501989
theorem B1678157 : Blo 330750 1678157 := bstep (se 3 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 1678157 = 629309) B629309
theorem B498515 : Blo 330750 498515 := bstep (se 1 (by rfl) ⟨373886, by rfl⟩ : syracuseStep 498515 = 747773) B747773
theorem B334675 : Blo 330750 334675 := bstep (se 1 (by rfl) ⟨251006, by rfl⟩ : syracuseStep 334675 = 502013) B502013
theorem B334691 : Blo 330750 334691 := bstep (se 1 (by rfl) ⟨251018, by rfl⟩ : syracuseStep 334691 = 502037) B502037
theorem B498545 : Blo 330750 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B334707 : Blo 330750 334707 := bstep (se 1 (by rfl) ⟨251030, by rfl⟩ : syracuseStep 334707 = 502061) B502061
theorem B564097 : Blo 330750 564097 := bstep (se 2 (by rfl) ⟨211536, by rfl⟩ : syracuseStep 564097 = 423073) B423073
theorem B498563 : Blo 330750 498563 := bstep (se 1 (by rfl) ⟨373922, by rfl⟩ : syracuseStep 498563 = 747845) B747845
theorem B334723 : Blo 330750 334723 := bstep (se 1 (by rfl) ⟨251042, by rfl⟩ : syracuseStep 334723 = 502085) B502085
theorem B334739 : Blo 330750 334739 := bstep (se 1 (by rfl) ⟨251054, by rfl⟩ : syracuseStep 334739 = 502109) B502109
theorem B498593 : Blo 330750 498593 := bstep (se 2 (by rfl) ⟨186972, by rfl⟩ : syracuseStep 498593 = 373945) B373945
theorem B564131 : Blo 330750 564131 := bstep (se 1 (by rfl) ⟨423098, by rfl⟩ : syracuseStep 564131 = 846197) B846197
theorem B1121201 : Blo 330750 1121201 := bstep (se 2 (by rfl) ⟨420450, by rfl⟩ : syracuseStep 1121201 = 840901) B840901
theorem B498611 : Blo 330750 498611 := bstep (se 1 (by rfl) ⟨373958, by rfl⟩ : syracuseStep 498611 = 747917) B747917
theorem B498641 : Blo 330750 498641 := bstep (se 2 (by rfl) ⟨186990, by rfl⟩ : syracuseStep 498641 = 373981) B373981
theorem B498659 : Blo 330750 498659 := bstep (se 1 (by rfl) ⟨373994, by rfl⟩ : syracuseStep 498659 = 747989) B747989
theorem B498689 : Blo 330750 498689 := bstep (se 2 (by rfl) ⟨187008, by rfl⟩ : syracuseStep 498689 = 374017) B374017
theorem B498707 : Blo 330750 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B629795 : Blo 330750 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B564259 : Blo 330750 564259 := bstep (se 1 (by rfl) ⟨423194, by rfl⟩ : syracuseStep 564259 = 846389) B846389
theorem B498737 : Blo 330750 498737 := bstep (se 2 (by rfl) ⟨187026, by rfl⟩ : syracuseStep 498737 = 374053) B374053
theorem B728131 : Blo 330750 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B498755 : Blo 330750 498755 := bstep (se 1 (by rfl) ⟨374066, by rfl⟩ : syracuseStep 498755 = 748133) B748133
theorem B498785 : Blo 330750 498785 := bstep (se 2 (by rfl) ⟨187044, by rfl⟩ : syracuseStep 498785 = 374089) B374089
theorem B498803 : Blo 330750 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B498833 : Blo 330750 498833 := bstep (se 2 (by rfl) ⟨187062, by rfl⟩ : syracuseStep 498833 = 374125) B374125
theorem B498851 : Blo 330750 498851 := bstep (se 1 (by rfl) ⟨374138, by rfl⟩ : syracuseStep 498851 = 748277) B748277
theorem B564401 : Blo 330750 564401 := bstep (se 2 (by rfl) ⟨211650, by rfl⟩ : syracuseStep 564401 = 423301) B423301
theorem B498881 : Blo 330750 498881 := bstep (se 2 (by rfl) ⟨187080, by rfl⟩ : syracuseStep 498881 = 374161) B374161
theorem B498899 : Blo 330750 498899 := bstep (se 1 (by rfl) ⟨374174, by rfl⟩ : syracuseStep 498899 = 748349) B748349
theorem B498929 : Blo 330750 498929 := bstep (se 2 (by rfl) ⟨187098, by rfl⟩ : syracuseStep 498929 = 374197) B374197
theorem B498947 : Blo 330750 498947 := bstep (se 1 (by rfl) ⟨374210, by rfl⟩ : syracuseStep 498947 = 748421) B748421
theorem B498977 : Blo 330750 498977 := bstep (se 2 (by rfl) ⟨187116, by rfl⟩ : syracuseStep 498977 = 374233) B374233
theorem B564529 : Blo 330750 564529 := bstep (se 2 (by rfl) ⟨211698, by rfl⟩ : syracuseStep 564529 = 423397) B423397
theorem B498995 : Blo 330750 498995 := bstep (se 1 (by rfl) ⟨374246, by rfl⟩ : syracuseStep 498995 = 748493) B748493
theorem B499025 : Blo 330750 499025 := bstep (se 2 (by rfl) ⟨187134, by rfl⟩ : syracuseStep 499025 = 374269) B374269
theorem B564563 : Blo 330750 564563 := bstep (se 1 (by rfl) ⟨423422, by rfl⟩ : syracuseStep 564563 = 846845) B846845
theorem B499043 : Blo 330750 499043 := bstep (se 1 (by rfl) ⟨374282, by rfl⟩ : syracuseStep 499043 = 748565) B748565
theorem B499073 : Blo 330750 499073 := bstep (se 2 (by rfl) ⟨187152, by rfl⟩ : syracuseStep 499073 = 374305) B374305
theorem B499091 : Blo 330750 499091 := bstep (se 1 (by rfl) ⟨374318, by rfl⟩ : syracuseStep 499091 = 748637) B748637
theorem B499121 : Blo 330750 499121 := bstep (se 2 (by rfl) ⟨187170, by rfl⟩ : syracuseStep 499121 = 374341) B374341
theorem B499139 : Blo 330750 499139 := bstep (se 1 (by rfl) ⟨374354, by rfl⟩ : syracuseStep 499139 = 748709) B748709
theorem B1121741 : Blo 330750 1121741 := bstep (se 3 (by rfl) ⟨210326, by rfl⟩ : syracuseStep 1121741 = 420653) B420653
theorem B564691 : Blo 330750 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B499169 : Blo 330750 499169 := bstep (se 2 (by rfl) ⟨187188, by rfl⟩ : syracuseStep 499169 = 374377) B374377
theorem B499187 : Blo 330750 499187 := bstep (se 1 (by rfl) ⟨374390, by rfl⟩ : syracuseStep 499187 = 748781) B748781
theorem B1121795 : Blo 330750 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B499217 : Blo 330750 499217 := bstep (se 2 (by rfl) ⟨187206, by rfl⟩ : syracuseStep 499217 = 374413) B374413
theorem B499235 : Blo 330750 499235 := bstep (se 1 (by rfl) ⟨374426, by rfl⟩ : syracuseStep 499235 = 748853) B748853
theorem B499265 : Blo 330750 499265 := bstep (se 2 (by rfl) ⟨187224, by rfl⟩ : syracuseStep 499265 = 374449) B374449
theorem B499283 : Blo 330750 499283 := bstep (se 1 (by rfl) ⟨374462, by rfl⟩ : syracuseStep 499283 = 748925) B748925
theorem B564833 : Blo 330750 564833 := bstep (se 2 (by rfl) ⟨211812, by rfl⟩ : syracuseStep 564833 = 423625) B423625
theorem B499313 : Blo 330750 499313 := bstep (se 2 (by rfl) ⟨187242, by rfl⟩ : syracuseStep 499313 = 374485) B374485
theorem B499331 : Blo 330750 499331 := bstep (se 1 (by rfl) ⟨374498, by rfl⟩ : syracuseStep 499331 = 748997) B748997
theorem B499361 : Blo 330750 499361 := bstep (se 2 (by rfl) ⟨187260, by rfl⟩ : syracuseStep 499361 = 374521) B374521
theorem B499379 : Blo 330750 499379 := bstep (se 1 (by rfl) ⟨374534, by rfl⟩ : syracuseStep 499379 = 749069) B749069
theorem B499409 : Blo 330750 499409 := bstep (se 2 (by rfl) ⟨187278, by rfl⟩ : syracuseStep 499409 = 374557) B374557
theorem B499427 : Blo 330750 499427 := bstep (se 1 (by rfl) ⟨374570, by rfl⟩ : syracuseStep 499427 = 749141) B749141
theorem B499457 : Blo 330750 499457 := bstep (se 2 (by rfl) ⟨187296, by rfl⟩ : syracuseStep 499457 = 374593) B374593
theorem B1122065 : Blo 330750 1122065 := bstep (se 2 (by rfl) ⟨420774, by rfl⟩ : syracuseStep 1122065 = 841549) B841549
theorem B499475 : Blo 330750 499475 := bstep (se 1 (by rfl) ⟨374606, by rfl⟩ : syracuseStep 499475 = 749213) B749213
theorem B499505 : Blo 330750 499505 := bstep (se 2 (by rfl) ⟨187314, by rfl⟩ : syracuseStep 499505 = 374629) B374629
theorem B499523 : Blo 330750 499523 := bstep (se 1 (by rfl) ⟨374642, by rfl⟩ : syracuseStep 499523 = 749285) B749285
theorem B532307 : Blo 330750 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B499553 : Blo 330750 499553 := bstep (se 2 (by rfl) ⟨187332, by rfl⟩ : syracuseStep 499553 = 374665) B374665
theorem B499571 : Blo 330750 499571 := bstep (se 1 (by rfl) ⟨374678, by rfl⟩ : syracuseStep 499571 = 749357) B749357
theorem B3710861 : Blo 330750 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B499601 : Blo 330750 499601 := bstep (se 2 (by rfl) ⟨187350, by rfl⟩ : syracuseStep 499601 = 374701) B374701
theorem B597923 : Blo 330750 597923 := bstep (se 1 (by rfl) ⟨448442, by rfl⟩ : syracuseStep 597923 = 896885) B896885
theorem B499619 : Blo 330750 499619 := bstep (se 1 (by rfl) ⟨374714, by rfl⟩ : syracuseStep 499619 = 749429) B749429
theorem B499649 : Blo 330750 499649 := bstep (se 2 (by rfl) ⟨187368, by rfl⟩ : syracuseStep 499649 = 374737) B374737
theorem B630737 : Blo 330750 630737 := bstep (se 2 (by rfl) ⟨236526, by rfl⟩ : syracuseStep 630737 = 473053) B473053
theorem B499667 : Blo 330750 499667 := bstep (se 1 (by rfl) ⟨374750, by rfl⟩ : syracuseStep 499667 = 749501) B749501
theorem B499697 : Blo 330750 499697 := bstep (se 2 (by rfl) ⟨187386, by rfl⟩ : syracuseStep 499697 = 374773) B374773
theorem B499715 : Blo 330750 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B499745 : Blo 330750 499745 := bstep (se 2 (by rfl) ⟨187404, by rfl⟩ : syracuseStep 499745 = 374809) B374809
theorem B532531 : Blo 330750 532531 := bstep (se 1 (by rfl) ⟨399398, by rfl⟩ : syracuseStep 532531 = 798797) B798797
theorem B499763 : Blo 330750 499763 := bstep (se 1 (by rfl) ⟨374822, by rfl⟩ : syracuseStep 499763 = 749645) B749645
theorem B499793 : Blo 330750 499793 := bstep (se 2 (by rfl) ⟨187422, by rfl⟩ : syracuseStep 499793 = 374845) B374845
theorem B499811 : Blo 330750 499811 := bstep (se 1 (by rfl) ⟨374858, by rfl⟩ : syracuseStep 499811 = 749717) B749717
theorem B532595 : Blo 330750 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B499841 : Blo 330750 499841 := bstep (se 2 (by rfl) ⟨187440, by rfl⟩ : syracuseStep 499841 = 374881) B374881
theorem B499859 : Blo 330750 499859 := bstep (se 1 (by rfl) ⟨374894, by rfl⟩ : syracuseStep 499859 = 749789) B749789
theorem B499889 : Blo 330750 499889 := bstep (se 2 (by rfl) ⟨187458, by rfl⟩ : syracuseStep 499889 = 374917) B374917
theorem B499907 : Blo 330750 499907 := bstep (se 1 (by rfl) ⟨374930, by rfl⟩ : syracuseStep 499907 = 749861) B749861
theorem B499937 : Blo 330750 499937 := bstep (se 2 (by rfl) ⟨187476, by rfl⟩ : syracuseStep 499937 = 374953) B374953
theorem B532723 : Blo 330750 532723 := bstep (se 1 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 532723 = 799085) B799085
theorem B499955 : Blo 330750 499955 := bstep (se 1 (by rfl) ⟨374966, by rfl⟩ : syracuseStep 499955 = 749933) B749933
theorem B499985 : Blo 330750 499985 := bstep (se 2 (by rfl) ⟨187494, by rfl⟩ : syracuseStep 499985 = 374989) B374989
theorem B500003 : Blo 330750 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B1122605 : Blo 330750 1122605 := bstep (se 3 (by rfl) ⟨210488, by rfl⟩ : syracuseStep 1122605 = 420977) B420977
theorem B500033 : Blo 330750 500033 := bstep (se 2 (by rfl) ⟨187512, by rfl⟩ : syracuseStep 500033 = 375025) B375025
theorem B500051 : Blo 330750 500051 := bstep (se 1 (by rfl) ⟨375038, by rfl⟩ : syracuseStep 500051 = 750077) B750077
theorem B1417571 : Blo 330750 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B1122659 : Blo 330750 1122659 := bstep (se 1 (by rfl) ⟨841994, by rfl⟩ : syracuseStep 1122659 = 1683989) B1683989
theorem B500081 : Blo 330750 500081 := bstep (se 2 (by rfl) ⟨187530, by rfl⟩ : syracuseStep 500081 = 375061) B375061
theorem B500099 : Blo 330750 500099 := bstep (se 1 (by rfl) ⟨375074, by rfl⟩ : syracuseStep 500099 = 750149) B750149
theorem B500129 : Blo 330750 500129 := bstep (se 2 (by rfl) ⟨187548, by rfl⟩ : syracuseStep 500129 = 375097) B375097
theorem B500147 : Blo 330750 500147 := bstep (se 1 (by rfl) ⟨375110, by rfl⟩ : syracuseStep 500147 = 750221) B750221
theorem B500177 : Blo 330750 500177 := bstep (se 2 (by rfl) ⟨187566, by rfl⟩ : syracuseStep 500177 = 375133) B375133
theorem B500195 : Blo 330750 500195 := bstep (se 1 (by rfl) ⟨375146, by rfl⟩ : syracuseStep 500195 = 750293) B750293
theorem B500225 : Blo 330750 500225 := bstep (se 2 (by rfl) ⟨187584, by rfl⟩ : syracuseStep 500225 = 375169) B375169
theorem B500243 : Blo 330750 500243 := bstep (se 1 (by rfl) ⟨375182, by rfl⟩ : syracuseStep 500243 = 750365) B750365
theorem B500273 : Blo 330750 500273 := bstep (se 2 (by rfl) ⟨187602, by rfl⟩ : syracuseStep 500273 = 375205) B375205
theorem B795203 : Blo 330750 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B500291 : Blo 330750 500291 := bstep (se 1 (by rfl) ⟨375218, by rfl⟩ : syracuseStep 500291 = 750437) B750437
theorem B500321 : Blo 330750 500321 := bstep (se 2 (by rfl) ⟨187620, by rfl⟩ : syracuseStep 500321 = 375241) B375241
theorem B1122929 : Blo 330750 1122929 := bstep (se 2 (by rfl) ⟨421098, by rfl⟩ : syracuseStep 1122929 = 842197) B842197
theorem B500339 : Blo 330750 500339 := bstep (se 1 (by rfl) ⟨375254, by rfl⟩ : syracuseStep 500339 = 750509) B750509
theorem B500369 : Blo 330750 500369 := bstep (se 2 (by rfl) ⟨187638, by rfl⟩ : syracuseStep 500369 = 375277) B375277
theorem B500387 : Blo 330750 500387 := bstep (se 1 (by rfl) ⟨375290, by rfl⟩ : syracuseStep 500387 = 750581) B750581
theorem B500417 : Blo 330750 500417 := bstep (se 2 (by rfl) ⟨187656, by rfl⟩ : syracuseStep 500417 = 375313) B375313
theorem B500435 : Blo 330750 500435 := bstep (se 1 (by rfl) ⟨375326, by rfl⟩ : syracuseStep 500435 = 750653) B750653
theorem B500465 : Blo 330750 500465 := bstep (se 2 (by rfl) ⟨187674, by rfl⟩ : syracuseStep 500465 = 375349) B375349
theorem B500483 : Blo 330750 500483 := bstep (se 1 (by rfl) ⟨375362, by rfl⟩ : syracuseStep 500483 = 750725) B750725
theorem B566033 : Blo 330750 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B500513 : Blo 330750 500513 := bstep (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) B375385
theorem B500531 : Blo 330750 500531 := bstep (se 1 (by rfl) ⟨375398, by rfl⟩ : syracuseStep 500531 = 750797) B750797
theorem B631633 : Blo 330750 631633 := bstep (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) B473725
theorem B500561 : Blo 330750 500561 := bstep (se 2 (by rfl) ⟨187710, by rfl⟩ : syracuseStep 500561 = 375421) B375421
theorem B795491 : Blo 330750 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B500579 : Blo 330750 500579 := bstep (se 1 (by rfl) ⟨375434, by rfl⟩ : syracuseStep 500579 = 750869) B750869
theorem B500609 : Blo 330750 500609 := bstep (se 2 (by rfl) ⟨187728, by rfl⟩ : syracuseStep 500609 = 375457) B375457
theorem B500627 : Blo 330750 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B598961 : Blo 330750 598961 := bstep (se 2 (by rfl) ⟨224610, by rfl⟩ : syracuseStep 598961 = 449221) B449221
theorem B500657 : Blo 330750 500657 := bstep (se 2 (by rfl) ⟨187746, by rfl⟩ : syracuseStep 500657 = 375493) B375493
theorem B533441 : Blo 330750 533441 := bstep (se 2 (by rfl) ⟨200040, by rfl⟩ : syracuseStep 533441 = 400081) B400081
theorem B500675 : Blo 330750 500675 := bstep (se 1 (by rfl) ⟨375506, by rfl⟩ : syracuseStep 500675 = 751013) B751013
theorem B500705 : Blo 330750 500705 := bstep (se 2 (by rfl) ⟨187764, by rfl⟩ : syracuseStep 500705 = 375529) B375529
theorem B631793 : Blo 330750 631793 := bstep (se 2 (by rfl) ⟨236922, by rfl⟩ : syracuseStep 631793 = 473845) B473845
theorem B500723 : Blo 330750 500723 := bstep (se 1 (by rfl) ⟨375542, by rfl⟩ : syracuseStep 500723 = 751085) B751085
theorem B500753 : Blo 330750 500753 := bstep (se 2 (by rfl) ⟨187782, by rfl⟩ : syracuseStep 500753 = 375565) B375565
theorem B500771 : Blo 330750 500771 := bstep (se 1 (by rfl) ⟨375578, by rfl⟩ : syracuseStep 500771 = 751157) B751157
theorem B533569 : Blo 330750 533569 := bstep (se 2 (by rfl) ⟨200088, by rfl⟩ : syracuseStep 533569 = 400177) B400177
theorem B500801 : Blo 330750 500801 := bstep (se 2 (by rfl) ⟨187800, by rfl⟩ : syracuseStep 500801 = 375601) B375601
theorem B500819 : Blo 330750 500819 := bstep (se 1 (by rfl) ⟨375614, by rfl⟩ : syracuseStep 500819 = 751229) B751229
theorem B500849 : Blo 330750 500849 := bstep (se 2 (by rfl) ⟨187818, by rfl⟩ : syracuseStep 500849 = 375637) B375637
theorem B500867 : Blo 330750 500867 := bstep (se 1 (by rfl) ⟨375650, by rfl⟩ : syracuseStep 500867 = 751301) B751301
theorem B3777677 : Blo 330750 3777677 := bstep (se 3 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 3777677 = 1416629) B1416629
theorem B1123469 : Blo 330750 1123469 := bstep (se 3 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 1123469 = 421301) B421301
theorem B500897 : Blo 330750 500897 := bstep (se 2 (by rfl) ⟨187836, by rfl⟩ : syracuseStep 500897 = 375673) B375673
theorem B500915 : Blo 330750 500915 := bstep (se 1 (by rfl) ⟨375686, by rfl⟩ : syracuseStep 500915 = 751373) B751373
theorem B1123523 : Blo 330750 1123523 := bstep (se 1 (by rfl) ⟨842642, by rfl⟩ : syracuseStep 1123523 = 1685285) B1685285
theorem B500945 : Blo 330750 500945 := bstep (se 2 (by rfl) ⟨187854, by rfl⟩ : syracuseStep 500945 = 375709) B375709
theorem B500963 : Blo 330750 500963 := bstep (se 1 (by rfl) ⟨375722, by rfl⟩ : syracuseStep 500963 = 751445) B751445
theorem B500993 : Blo 330750 500993 := bstep (se 2 (by rfl) ⟨187872, by rfl⟩ : syracuseStep 500993 = 375745) B375745
theorem B501011 : Blo 330750 501011 := bstep (se 1 (by rfl) ⟨375758, by rfl⟩ : syracuseStep 501011 = 751517) B751517
theorem B337187 : Blo 330750 337187 := bstep (se 1 (by rfl) ⟨252890, by rfl⟩ : syracuseStep 337187 = 505781) B505781
theorem B501041 : Blo 330750 501041 := bstep (se 2 (by rfl) ⟨187890, by rfl⟩ : syracuseStep 501041 = 375781) B375781
theorem B501059 : Blo 330750 501059 := bstep (se 1 (by rfl) ⟨375794, by rfl⟩ : syracuseStep 501059 = 751589) B751589
theorem B501089 : Blo 330750 501089 := bstep (se 2 (by rfl) ⟨187908, by rfl⟩ : syracuseStep 501089 = 375817) B375817
theorem B501107 : Blo 330750 501107 := bstep (se 1 (by rfl) ⟨375830, by rfl⟩ : syracuseStep 501107 = 751661) B751661
theorem B632195 : Blo 330750 632195 := bstep (se 1 (by rfl) ⟨474146, by rfl⟩ : syracuseStep 632195 = 948293) B948293
theorem B501137 : Blo 330750 501137 := bstep (se 2 (by rfl) ⟨187926, by rfl⟩ : syracuseStep 501137 = 375853) B375853
theorem B501155 : Blo 330750 501155 := bstep (se 1 (by rfl) ⟨375866, by rfl⟩ : syracuseStep 501155 = 751733) B751733
theorem B894385 : Blo 330750 894385 := bstep (se 2 (by rfl) ⟨335394, by rfl⟩ : syracuseStep 894385 = 670789) B670789
theorem B533953 : Blo 330750 533953 := bstep (se 2 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 533953 = 400465) B400465
theorem B501185 : Blo 330750 501185 := bstep (se 2 (by rfl) ⟨187944, by rfl⟩ : syracuseStep 501185 = 375889) B375889
theorem B1123793 : Blo 330750 1123793 := bstep (se 2 (by rfl) ⟨421422, by rfl⟩ : syracuseStep 1123793 = 842845) B842845
theorem B501203 : Blo 330750 501203 := bstep (se 1 (by rfl) ⟨375902, by rfl⟩ : syracuseStep 501203 = 751805) B751805
theorem B501233 : Blo 330750 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B501251 : Blo 330750 501251 := bstep (se 1 (by rfl) ⟨375938, by rfl⟩ : syracuseStep 501251 = 751877) B751877
theorem B501281 : Blo 330750 501281 := bstep (se 2 (by rfl) ⟨187980, by rfl⟩ : syracuseStep 501281 = 375961) B375961
theorem B501299 : Blo 330750 501299 := bstep (se 1 (by rfl) ⟨375974, by rfl⟩ : syracuseStep 501299 = 751949) B751949
theorem B501329 : Blo 330750 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B501347 : Blo 330750 501347 := bstep (se 1 (by rfl) ⟨376010, by rfl⟩ : syracuseStep 501347 = 752021) B752021
theorem B501377 : Blo 330750 501377 := bstep (se 2 (by rfl) ⟨188016, by rfl⟩ : syracuseStep 501377 = 376033) B376033
theorem B501395 : Blo 330750 501395 := bstep (se 1 (by rfl) ⟨376046, by rfl⟩ : syracuseStep 501395 = 752093) B752093
theorem B796337 : Blo 330750 796337 := bstep (se 2 (by rfl) ⟨298626, by rfl⟩ : syracuseStep 796337 = 597253) B597253
theorem B1681073 : Blo 330750 1681073 := bstep (se 2 (by rfl) ⟨630402, by rfl⟩ : syracuseStep 1681073 = 1260805) B1260805
theorem B501425 : Blo 330750 501425 := bstep (se 2 (by rfl) ⟨188034, by rfl⟩ : syracuseStep 501425 = 376069) B376069
theorem B534209 : Blo 330750 534209 := bstep (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) B400657
theorem B501443 : Blo 330750 501443 := bstep (se 1 (by rfl) ⟨376082, by rfl⟩ : syracuseStep 501443 = 752165) B752165
theorem B566993 : Blo 330750 566993 := bstep (se 2 (by rfl) ⟨212622, by rfl⟩ : syracuseStep 566993 = 425245) B425245
theorem B501473 : Blo 330750 501473 := bstep (se 2 (by rfl) ⟨188052, by rfl⟩ : syracuseStep 501473 = 376105) B376105
theorem B501491 : Blo 330750 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B501521 : Blo 330750 501521 := bstep (se 2 (by rfl) ⟨188070, by rfl⟩ : syracuseStep 501521 = 376141) B376141
theorem B567073 : Blo 330750 567073 := bstep (se 2 (by rfl) ⟨212652, by rfl⟩ : syracuseStep 567073 = 425305) B425305
theorem B501539 : Blo 330750 501539 := bstep (se 1 (by rfl) ⟨376154, by rfl⟩ : syracuseStep 501539 = 752309) B752309
theorem B501569 : Blo 330750 501569 := bstep (se 2 (by rfl) ⟨188088, by rfl⟩ : syracuseStep 501569 = 376177) B376177
theorem B501587 : Blo 330750 501587 := bstep (se 1 (by rfl) ⟨376190, by rfl⟩ : syracuseStep 501587 = 752381) B752381
theorem B501617 : Blo 330750 501617 := bstep (se 2 (by rfl) ⟨188106, by rfl⟩ : syracuseStep 501617 = 376213) B376213
theorem B501635 : Blo 330750 501635 := bstep (se 1 (by rfl) ⟨376226, by rfl⟩ : syracuseStep 501635 = 752453) B752453
theorem B501665 : Blo 330750 501665 := bstep (se 2 (by rfl) ⟨188124, by rfl⟩ : syracuseStep 501665 = 376249) B376249
theorem B501683 : Blo 330750 501683 := bstep (se 1 (by rfl) ⟨376262, by rfl⟩ : syracuseStep 501683 = 752525) B752525
theorem B567233 : Blo 330750 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B796625 : Blo 330750 796625 := bstep (se 2 (by rfl) ⟨298734, by rfl⟩ : syracuseStep 796625 = 597469) B597469
theorem B501713 : Blo 330750 501713 := bstep (se 2 (by rfl) ⟨188142, by rfl⟩ : syracuseStep 501713 = 376285) B376285
theorem B567251 : Blo 330750 567251 := bstep (se 1 (by rfl) ⟨425438, by rfl⟩ : syracuseStep 567251 = 850877) B850877
theorem B501731 : Blo 330750 501731 := bstep (se 1 (by rfl) ⟨376298, by rfl⟩ : syracuseStep 501731 = 752597) B752597
theorem B1124333 : Blo 330750 1124333 := bstep (se 3 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 1124333 = 421625) B421625
theorem B501761 : Blo 330750 501761 := bstep (se 2 (by rfl) ⟨188160, by rfl⟩ : syracuseStep 501761 = 376321) B376321
theorem B501779 : Blo 330750 501779 := bstep (se 1 (by rfl) ⟨376334, by rfl⟩ : syracuseStep 501779 = 752669) B752669
theorem B1124387 : Blo 330750 1124387 := bstep (se 1 (by rfl) ⟨843290, by rfl⟩ : syracuseStep 1124387 = 1686581) B1686581
theorem B501809 : Blo 330750 501809 := bstep (se 2 (by rfl) ⟨188178, by rfl⟩ : syracuseStep 501809 = 376357) B376357
theorem B501827 : Blo 330750 501827 := bstep (se 1 (by rfl) ⟨376370, by rfl⟩ : syracuseStep 501827 = 752741) B752741
theorem B501857 : Blo 330750 501857 := bstep (se 2 (by rfl) ⟨188196, by rfl⟩ : syracuseStep 501857 = 376393) B376393
theorem B501875 : Blo 330750 501875 := bstep (se 1 (by rfl) ⟨376406, by rfl⟩ : syracuseStep 501875 = 752813) B752813
theorem B2533517 : Blo 330750 2533517 := bstep (se 3 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 2533517 = 950069) B950069
theorem B796817 : Blo 330750 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B501905 : Blo 330750 501905 := bstep (se 2 (by rfl) ⟨188214, by rfl⟩ : syracuseStep 501905 = 376429) B376429
theorem B501923 : Blo 330750 501923 := bstep (se 1 (by rfl) ⟨376442, by rfl⟩ : syracuseStep 501923 = 752885) B752885
theorem B501953 : Blo 330750 501953 := bstep (se 2 (by rfl) ⟨188232, by rfl⟩ : syracuseStep 501953 = 376465) B376465
theorem B501971 : Blo 330750 501971 := bstep (se 1 (by rfl) ⟨376478, by rfl⟩ : syracuseStep 501971 = 752957) B752957
theorem B2271473 : Blo 330750 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B502001 : Blo 330750 502001 := bstep (se 2 (by rfl) ⟨188250, by rfl⟩ : syracuseStep 502001 = 376501) B376501
theorem B633091 : Blo 330750 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B502019 : Blo 330750 502019 := bstep (se 1 (by rfl) ⟨376514, by rfl⟩ : syracuseStep 502019 = 753029) B753029
theorem B502049 : Blo 330750 502049 := bstep (se 2 (by rfl) ⟨188268, by rfl⟩ : syracuseStep 502049 = 376537) B376537
theorem B1419569 : Blo 330750 1419569 := bstep (se 2 (by rfl) ⟨532338, by rfl⟩ : syracuseStep 1419569 = 1064677) B1064677
theorem B1124657 : Blo 330750 1124657 := bstep (se 2 (by rfl) ⟨421746, by rfl⟩ : syracuseStep 1124657 = 843493) B843493
theorem B502067 : Blo 330750 502067 := bstep (se 1 (by rfl) ⟨376550, by rfl⟩ : syracuseStep 502067 = 753101) B753101
theorem B3909941 : Blo 330750 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B502097 : Blo 330750 502097 := bstep (se 2 (by rfl) ⟨188286, by rfl⟩ : syracuseStep 502097 = 376573) B376573
theorem B502115 : Blo 330750 502115 := bstep (se 1 (by rfl) ⟨376586, by rfl⟩ : syracuseStep 502115 = 753173) B753173
theorem B633251 : Blo 330750 633251 := bstep (se 1 (by rfl) ⟨474938, by rfl⟩ : syracuseStep 633251 = 949877) B949877
theorem B18196933 : Blo 330750 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B1518257 : Blo 330750 1518257 := bstep (se 2 (by rfl) ⟨569346, by rfl⟩ : syracuseStep 1518257 = 1138693) B1138693
theorem B3418949 : Blo 330750 3418949 := bstep (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) B641053
theorem B1125197 : Blo 330750 1125197 := bstep (se 3 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 1125197 = 421949) B421949
theorem B1125251 : Blo 330750 1125251 := bstep (se 1 (by rfl) ⟨843938, by rfl⟩ : syracuseStep 1125251 = 1687877) B1687877
theorem B535619 : Blo 330750 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B797777 : Blo 330750 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B1682531 : Blo 330750 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B1715341 : Blo 330750 1715341 := bstep (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) B643253
theorem B1125521 : Blo 330750 1125521 := bstep (se 2 (by rfl) ⟨422070, by rfl⟩ : syracuseStep 1125521 = 844141) B844141
theorem B1060141 : Blo 330750 1060141 := bstep (se 3 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 1060141 = 397553) B397553
theorem B372163 : Blo 330750 372163 := bstep (se 1 (by rfl) ⟨279122, by rfl⟩ : syracuseStep 372163 = 558245) B558245
theorem B634321 : Blo 330750 634321 := bstep (se 2 (by rfl) ⟨237870, by rfl⟩ : syracuseStep 634321 = 475741) B475741
theorem B372307 : Blo 330750 372307 := bstep (se 1 (by rfl) ⟨279230, by rfl⟩ : syracuseStep 372307 = 558461) B558461
theorem B1126061 : Blo 330750 1126061 := bstep (se 3 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 1126061 = 422273) B422273
theorem B372451 : Blo 330750 372451 := bstep (se 1 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 372451 = 558677) B558677
theorem B1126115 : Blo 330750 1126115 := bstep (se 1 (by rfl) ⟨844586, by rfl⟩ : syracuseStep 1126115 = 1689173) B1689173
theorem B2142065 : Blo 330750 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B372595 : Blo 330750 372595 := bstep (se 1 (by rfl) ⟨279446, by rfl⟩ : syracuseStep 372595 = 558893) B558893
theorem B1683341 : Blo 330750 1683341 := bstep (se 3 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 1683341 = 631253) B631253
theorem B471025 : Blo 330750 471025 := bstep (se 2 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 471025 = 353269) B353269
theorem B3780593 : Blo 330750 3780593 := bstep (se 2 (by rfl) ⟨1417722, by rfl⟩ : syracuseStep 3780593 = 2835445) B2835445
theorem B1126385 : Blo 330750 1126385 := bstep (se 2 (by rfl) ⟨422394, by rfl⟩ : syracuseStep 1126385 = 844789) B844789
theorem B372739 : Blo 330750 372739 := bstep (se 1 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 372739 = 559109) B559109
theorem B372883 : Blo 330750 372883 := bstep (se 1 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 372883 = 559325) B559325
theorem B1257677 : Blo 330750 1257677 := bstep (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) B471629
theorem B373027 : Blo 330750 373027 := bstep (se 1 (by rfl) ⟨279770, by rfl⟩ : syracuseStep 373027 = 559541) B559541
theorem B799075 : Blo 330750 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B14332301 : Blo 330750 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B373171 : Blo 330750 373171 := bstep (se 1 (by rfl) ⟨279878, by rfl⟩ : syracuseStep 373171 = 559757) B559757
theorem B471521 : Blo 330750 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B635377 : Blo 330750 635377 := bstep (se 2 (by rfl) ⟨238266, by rfl⟩ : syracuseStep 635377 = 476533) B476533
theorem B1126925 : Blo 330750 1126925 := bstep (se 3 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 1126925 = 422597) B422597
theorem B373315 : Blo 330750 373315 := bstep (se 1 (by rfl) ⟨279986, by rfl⟩ : syracuseStep 373315 = 559973) B559973
theorem B1126979 : Blo 330750 1126979 := bstep (se 1 (by rfl) ⟨845234, by rfl⟩ : syracuseStep 1126979 = 1690469) B1690469
theorem B1913507 : Blo 330750 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B1422029 : Blo 330750 1422029 := bstep (se 3 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 1422029 = 533261) B533261
theorem B373459 : Blo 330750 373459 := bstep (se 1 (by rfl) ⟨280094, by rfl⟩ : syracuseStep 373459 = 560189) B560189
theorem B504625 : Blo 330750 504625 := bstep (se 2 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 504625 = 378469) B378469
theorem B1127249 : Blo 330750 1127249 := bstep (se 2 (by rfl) ⟨422718, by rfl⟩ : syracuseStep 1127249 = 845437) B845437
theorem B373603 : Blo 330750 373603 := bstep (se 1 (by rfl) ⟨280202, by rfl⟩ : syracuseStep 373603 = 560405) B560405
theorem B898019 : Blo 330750 898019 := bstep (se 1 (by rfl) ⟨673514, by rfl⟩ : syracuseStep 898019 = 1347029) B1347029
theorem B2831345 : Blo 330750 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B2536433 : Blo 330750 2536433 := bstep (se 2 (by rfl) ⟨951162, by rfl⟩ : syracuseStep 2536433 = 1902325) B1902325
theorem B373747 : Blo 330750 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B2012273 : Blo 330750 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B373891 : Blo 330750 373891 := bstep (se 1 (by rfl) ⟨280418, by rfl⟩ : syracuseStep 373891 = 560837) B560837
theorem B570577 : Blo 330750 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B374035 : Blo 330750 374035 := bstep (se 1 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 374035 = 561053) B561053
theorem B472387 : Blo 330750 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B1127789 : Blo 330750 1127789 := bstep (se 3 (by rfl) ⟨211460, by rfl⟩ : syracuseStep 1127789 = 422921) B422921
theorem B570755 : Blo 330750 570755 := bstep (se 1 (by rfl) ⟨428066, by rfl⟩ : syracuseStep 570755 = 856133) B856133
theorem B472483 : Blo 330750 472483 := bstep (se 1 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 472483 = 708725) B708725
theorem B374179 : Blo 330750 374179 := bstep (se 1 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 374179 = 561269) B561269
theorem B1127843 : Blo 330750 1127843 := bstep (se 1 (by rfl) ⟨845882, by rfl⟩ : syracuseStep 1127843 = 1691765) B1691765
theorem B374323 : Blo 330750 374323 := bstep (se 1 (by rfl) ⟨280742, by rfl⟩ : syracuseStep 374323 = 561485) B561485
theorem B964237 : Blo 330750 964237 := bstep (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) B361589
theorem B1128113 : Blo 330750 1128113 := bstep (se 2 (by rfl) ⟨423042, by rfl⟩ : syracuseStep 1128113 = 846085) B846085
theorem B374467 : Blo 330750 374467 := bstep (se 1 (by rfl) ⟨280850, by rfl⟩ : syracuseStep 374467 = 561701) B561701
theorem B374611 : Blo 330750 374611 := bstep (se 1 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 374611 = 561917) B561917
theorem B472979 : Blo 330750 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B374755 : Blo 330750 374755 := bstep (se 1 (by rfl) ⟨281066, by rfl⟩ : syracuseStep 374755 = 562133) B562133
theorem B374899 : Blo 330750 374899 := bstep (se 1 (by rfl) ⟨281174, by rfl⟩ : syracuseStep 374899 = 562349) B562349
theorem B1128653 : Blo 330750 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B1423601 : Blo 330750 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B375043 : Blo 330750 375043 := bstep (se 1 (by rfl) ⟨281282, by rfl⟩ : syracuseStep 375043 = 562565) B562565
theorem B1128707 : Blo 330750 1128707 := bstep (se 1 (by rfl) ⟨846530, by rfl⟩ : syracuseStep 1128707 = 1693061) B1693061
theorem B375187 : Blo 330750 375187 := bstep (se 1 (by rfl) ⟨281390, by rfl⟩ : syracuseStep 375187 = 562781) B562781
theorem B473617 : Blo 330750 473617 := bstep (se 2 (by rfl) ⟨177606, by rfl⟩ : syracuseStep 473617 = 355213) B355213
theorem B1128977 : Blo 330750 1128977 := bstep (se 2 (by rfl) ⟨423366, by rfl⟩ : syracuseStep 1128977 = 846733) B846733
theorem B375331 : Blo 330750 375331 := bstep (se 1 (by rfl) ⟨281498, by rfl⟩ : syracuseStep 375331 = 562997) B562997
theorem B3029645 : Blo 330750 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B1063601 : Blo 330750 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B375475 : Blo 330750 375475 := bstep (se 1 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 375475 = 563213) B563213
theorem B1686257 : Blo 330750 1686257 := bstep (se 2 (by rfl) ⟨632346, by rfl⟩ : syracuseStep 1686257 = 1264693) B1264693
theorem B899857 : Blo 330750 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B572179 : Blo 330750 572179 := bstep (se 1 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 572179 = 858269) B858269
theorem B375619 : Blo 330750 375619 := bstep (se 1 (by rfl) ⟨281714, by rfl⟩ : syracuseStep 375619 = 563429) B563429
theorem B899921 : Blo 330750 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B473953 : Blo 330750 473953 := bstep (se 2 (by rfl) ⟨177732, by rfl⟩ : syracuseStep 473953 = 355465) B355465
theorem B1063793 : Blo 330750 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B375763 : Blo 330750 375763 := bstep (se 1 (by rfl) ⟨281822, by rfl⟩ : syracuseStep 375763 = 563645) B563645
theorem B1129517 : Blo 330750 1129517 := bstep (se 3 (by rfl) ⟨211784, by rfl⟩ : syracuseStep 1129517 = 423569) B423569
theorem B1260593 : Blo 330750 1260593 := bstep (se 2 (by rfl) ⟨472722, by rfl⟩ : syracuseStep 1260593 = 945445) B945445
theorem B375907 : Blo 330750 375907 := bstep (se 1 (by rfl) ⟨281930, by rfl⟩ : syracuseStep 375907 = 563861) B563861
theorem B1129571 : Blo 330750 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B507107 : Blo 330750 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B376051 : Blo 330750 376051 := bstep (se 1 (by rfl) ⟨282038, by rfl⟩ : syracuseStep 376051 = 564077) B564077
theorem B376195 : Blo 330750 376195 := bstep (se 1 (by rfl) ⟨282146, by rfl⟩ : syracuseStep 376195 = 564293) B564293
theorem B2833805 : Blo 330750 2833805 := bstep (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) B1062677
theorem B474545 : Blo 330750 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B376339 : Blo 330750 376339 := bstep (se 1 (by rfl) ⟨282254, by rfl⟩ : syracuseStep 376339 = 564509) B564509
theorem B6372917 : Blo 330750 6372917 := bstep (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) B597461
theorem B638545 : Blo 330750 638545 := bstep (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) B478909
theorem B507521 : Blo 330750 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B376483 : Blo 330750 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B901037 : Blo 330750 901037 := bstep (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) B337889
theorem B475075 : Blo 330750 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B6799301 : Blo 330750 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B507953 : Blo 330750 507953 := bstep (se 2 (by rfl) ⟨190482, by rfl⟩ : syracuseStep 507953 = 380965) B380965
theorem B1687715 : Blo 330750 1687715 := bstep (se 1 (by rfl) ⟨1265786, by rfl⟩ : syracuseStep 1687715 = 2531573) B2531573
theorem B475411 : Blo 330750 475411 := bstep (se 1 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 475411 = 713117) B713117
theorem B1589539 : Blo 330750 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B1262051 : Blo 330750 1262051 := bstep (se 1 (by rfl) ⟨946538, by rfl⟩ : syracuseStep 1262051 = 1893077) B1893077
theorem B2114117 : Blo 330750 2114117 := bstep (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) B396397
theorem B1426061 : Blo 330750 1426061 := bstep (se 3 (by rfl) ⟨267386, by rfl⟩ : syracuseStep 1426061 = 534773) B534773
theorem B475969 : Blo 330750 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B901955 : Blo 330750 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B476003 : Blo 330750 476003 := bstep (se 1 (by rfl) ⟨357002, by rfl⟩ : syracuseStep 476003 = 714005) B714005
theorem B1688525 : Blo 330750 1688525 := bstep (se 3 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 1688525 = 633197) B633197
theorem B3195875 : Blo 330750 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B1426403 : Blo 330750 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B508931 : Blo 330750 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B1066061 : Blo 330750 1066061 := bstep (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) B399773
theorem B541811 : Blo 330750 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B3458189 : Blo 330750 3458189 := bstep (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) B1296821
theorem B1131875 : Blo 330750 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B476561 : Blo 330750 476561 := bstep (se 2 (by rfl) ⟨178710, by rfl⟩ : syracuseStep 476561 = 357421) B357421
theorem B1263053 : Blo 330750 1263053 := bstep (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) B473645
theorem B1590769 : Blo 330750 1590769 := bstep (se 2 (by rfl) ⟨596538, by rfl⟩ : syracuseStep 1590769 = 1193077) B1193077
theorem B346051 : Blo 330750 346051 := bstep (se 1 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 346051 = 519077) B519077
theorem B706897 : Blo 330750 706897 := bstep (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) B530173
theorem B838097 : Blo 330750 838097 := bstep (se 2 (by rfl) ⟨314286, by rfl⟩ : syracuseStep 838097 = 628573) B628573
theorem B510451 : Blo 330750 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B838147 : Blo 330750 838147 := bstep (se 1 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 838147 = 1257221) B1257221
theorem B1067651 : Blo 330750 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B2574989 : Blo 330750 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B838289 : Blo 330750 838289 := bstep (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) B628717
theorem B707555 : Blo 330750 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B1887245 : Blo 330750 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B2412017 : Blo 330750 2412017 := bstep (se 2 (by rfl) ⟨904506, by rfl⟩ : syracuseStep 2412017 = 1809013) B1809013
theorem B1068547 : Blo 330750 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B1789445 : Blo 330750 1789445 := bstep (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) B335521
theorem B1265165 : Blo 330750 1265165 := bstep (se 3 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 1265165 = 474437) B474437
theorem B839281 : Blo 330750 839281 := bstep (se 2 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 839281 = 629461) B629461
theorem B4181701 : Blo 330750 4181701 := bstep (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) B784069
theorem B708401 : Blo 330750 708401 := bstep (se 2 (by rfl) ⟨265650, by rfl⟩ : syracuseStep 708401 = 531301) B531301
theorem B1691441 : Blo 330750 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B4542277 : Blo 330750 4542277 := bstep (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) B851677
theorem B839555 : Blo 330750 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B839747 : Blo 330750 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B1921265 : Blo 330750 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B348451 : Blo 330750 348451 := bstep (se 1 (by rfl) ⟨261338, by rfl⟩ : syracuseStep 348451 = 522677) B522677
theorem B1265969 : Blo 330750 1265969 := bstep (se 2 (by rfl) ⟨474738, by rfl⟩ : syracuseStep 1265969 = 949477) B949477
theorem B1069649 : Blo 330750 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B1069777 : Blo 330750 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B1266637 : Blo 330750 1266637 := bstep (se 3 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 1266637 = 474989) B474989
theorem B840689 : Blo 330750 840689 := bstep (se 2 (by rfl) ⟨315258, by rfl⟩ : syracuseStep 840689 = 630517) B630517
theorem B840739 : Blo 330750 840739 := bstep (se 1 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 840739 = 1261109) B1261109
theorem B676945 : Blo 330750 676945 := bstep (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) B507709
theorem B840881 : Blo 330750 840881 := bstep (se 2 (by rfl) ⟨315330, by rfl⟩ : syracuseStep 840881 = 630661) B630661
theorem B1889477 : Blo 330750 1889477 := bstep (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) B354277
theorem B1692899 : Blo 330750 1692899 := bstep (se 1 (by rfl) ⟨1269674, by rfl⟩ : syracuseStep 1692899 = 2539349) B2539349
theorem B1135889 : Blo 330750 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B1594673 : Blo 330750 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B5133709 : Blo 330750 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B808451 : Blo 330750 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B1070765 : Blo 330750 1070765 := bstep (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) B401537
theorem B1267427 : Blo 330750 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B2119409 : Blo 330750 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B677731 : Blo 330750 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B1890161 : Blo 330750 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B6510449 : Blo 330750 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B677795 : Blo 330750 677795 := bstep (se 1 (by rfl) ⟨508346, by rfl⟩ : syracuseStep 677795 = 1016693) B1016693
theorem B2283461 : Blo 330750 2283461 := bstep (se 4 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 2283461 = 428149) B428149
theorem B1693709 : Blo 330750 1693709 := bstep (se 3 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 1693709 = 635141) B635141
theorem B841873 : Blo 330750 841873 := bstep (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) B631405
theorem B3201221 : Blo 330750 3201221 := bstep (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) B600229
theorem B2087117 : Blo 330750 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1268081 : Blo 330750 1268081 := bstep (se 2 (by rfl) ⟨475530, by rfl⟩ : syracuseStep 1268081 = 951061) B951061
theorem B842147 : Blo 330750 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B711185 : Blo 330750 711185 := bstep (se 2 (by rfl) ⟨266694, by rfl⟩ : syracuseStep 711185 = 533389) B533389
theorem B842339 : Blo 330750 842339 := bstep (se 1 (by rfl) ⟨631754, by rfl⟩ : syracuseStep 842339 = 1263509) B1263509
theorem B744209 : Blo 330750 744209 := bstep (se 2 (by rfl) ⟨279078, by rfl⟩ : syracuseStep 744209 = 558157) B558157
theorem B744227 : Blo 330750 744227 := bstep (se 1 (by rfl) ⟨558170, by rfl⟩ : syracuseStep 744227 = 1116341) B1116341
theorem B1596323 : Blo 330750 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1006573 : Blo 330750 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B1072109 : Blo 330750 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B1137649 : Blo 330750 1137649 := bstep (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) B853237
theorem B744497 : Blo 330750 744497 := bstep (se 2 (by rfl) ⟨279186, by rfl⟩ : syracuseStep 744497 = 558373) B558373
theorem B744515 : Blo 330750 744515 := bstep (se 1 (by rfl) ⟨558386, by rfl⟩ : syracuseStep 744515 = 1116773) B1116773
theorem B1203299 : Blo 330750 1203299 := bstep (se 1 (by rfl) ⟨902474, by rfl⟩ : syracuseStep 1203299 = 1804949) B1804949
theorem B1006769 : Blo 330750 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B1891619 : Blo 330750 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B744785 : Blo 330750 744785 := bstep (se 2 (by rfl) ⟨279294, by rfl⟩ : syracuseStep 744785 = 558589) B558589
theorem B744803 : Blo 330750 744803 := bstep (se 1 (by rfl) ⟨558602, by rfl⟩ : syracuseStep 744803 = 1117205) B1117205
theorem B843281 : Blo 330750 843281 := bstep (se 2 (by rfl) ⟨316230, by rfl⟩ : syracuseStep 843281 = 632461) B632461
theorem B843331 : Blo 330750 843331 := bstep (se 1 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 843331 = 1264997) B1264997
theorem B745073 : Blo 330750 745073 := bstep (se 2 (by rfl) ⟨279402, by rfl⟩ : syracuseStep 745073 = 558805) B558805
theorem B745091 : Blo 330750 745091 := bstep (se 1 (by rfl) ⟨558818, by rfl⟩ : syracuseStep 745091 = 1117637) B1117637
theorem B843473 : Blo 330750 843473 := bstep (se 2 (by rfl) ⟨316302, by rfl⟩ : syracuseStep 843473 = 632605) B632605
theorem B450307 : Blo 330750 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B1269539 : Blo 330750 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B1269553 : Blo 330750 1269553 := bstep (se 2 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 1269553 = 952165) B952165
theorem B745361 : Blo 330750 745361 := bstep (se 2 (by rfl) ⟨279510, by rfl⟩ : syracuseStep 745361 = 559021) B559021
theorem B745379 : Blo 330750 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B1138637 : Blo 330750 1138637 := bstep (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) B426989
theorem B1597553 : Blo 330750 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B2121869 : Blo 330750 2121869 := bstep (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) B795701
theorem B745649 : Blo 330750 745649 := bstep (se 2 (by rfl) ⟨279618, by rfl⟩ : syracuseStep 745649 = 559237) B559237
theorem B745667 : Blo 330750 745667 := bstep (se 1 (by rfl) ⟨559250, by rfl⟩ : syracuseStep 745667 = 1118501) B1118501
theorem B6447413 : Blo 330750 6447413 := bstep (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) B604445
theorem B745937 : Blo 330750 745937 := bstep (se 2 (by rfl) ⟨279726, by rfl⟩ : syracuseStep 745937 = 559453) B559453
theorem B680419 : Blo 330750 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B745955 : Blo 330750 745955 := bstep (se 1 (by rfl) ⟨559466, by rfl⟩ : syracuseStep 745955 = 1118933) B1118933
theorem B844465 : Blo 330750 844465 := bstep (se 2 (by rfl) ⟨316674, by rfl⟩ : syracuseStep 844465 = 633349) B633349
theorem B746225 : Blo 330750 746225 := bstep (se 2 (by rfl) ⟨279834, by rfl⟩ : syracuseStep 746225 = 559669) B559669
theorem B746243 : Blo 330750 746243 := bstep (se 1 (by rfl) ⟨559682, by rfl⟩ : syracuseStep 746243 = 1119365) B1119365
theorem B451345 : Blo 330750 451345 := bstep (se 2 (by rfl) ⟨169254, by rfl⟩ : syracuseStep 451345 = 338509) B338509
theorem B844739 : Blo 330750 844739 := bstep (se 1 (by rfl) ⟨633554, by rfl⟩ : syracuseStep 844739 = 1267109) B1267109
theorem B812035 : Blo 330750 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B746513 : Blo 330750 746513 := bstep (se 2 (by rfl) ⟨279942, by rfl⟩ : syracuseStep 746513 = 559885) B559885
theorem B746531 : Blo 330750 746531 := bstep (se 1 (by rfl) ⟨559898, by rfl⟩ : syracuseStep 746531 = 1119797) B1119797
theorem B943235 : Blo 330750 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B844931 : Blo 330750 844931 := bstep (se 1 (by rfl) ⟨633698, by rfl⟩ : syracuseStep 844931 = 1267397) B1267397
theorem B28697813 : Blo 330750 28697813 := bstep (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) B672605
theorem B746801 : Blo 330750 746801 := bstep (se 2 (by rfl) ⟨280050, by rfl⟩ : syracuseStep 746801 = 560101) B560101
theorem B746819 : Blo 330750 746819 := bstep (se 1 (by rfl) ⟨560114, by rfl⟩ : syracuseStep 746819 = 1120229) B1120229
theorem B419251 : Blo 330750 419251 := bstep (se 1 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 419251 = 628877) B628877
theorem B3630563 : Blo 330750 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B5694947 : Blo 330750 5694947 := bstep (se 1 (by rfl) ⟨4271210, by rfl⟩ : syracuseStep 5694947 = 8542421) B8542421
theorem B419347 : Blo 330750 419347 := bstep (se 1 (by rfl) ⟨314510, by rfl⟩ : syracuseStep 419347 = 629021) B629021
theorem B747089 : Blo 330750 747089 := bstep (se 2 (by rfl) ⟨280158, by rfl⟩ : syracuseStep 747089 = 560317) B560317
theorem B747107 : Blo 330750 747107 := bstep (se 1 (by rfl) ⟨560330, by rfl⟩ : syracuseStep 747107 = 1120661) B1120661
theorem B714595 : Blo 330750 714595 := bstep (se 1 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 714595 = 1071893) B1071893
theorem B747377 : Blo 330750 747377 := bstep (se 2 (by rfl) ⟨280266, by rfl⟩ : syracuseStep 747377 = 560533) B560533
theorem B747395 : Blo 330750 747395 := bstep (se 1 (by rfl) ⟨560546, by rfl⟩ : syracuseStep 747395 = 1121093) B1121093
theorem B944045 : Blo 330750 944045 := bstep (se 3 (by rfl) ⟨177008, by rfl⟩ : syracuseStep 944045 = 354017) B354017
theorem B419843 : Blo 330750 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B845873 : Blo 330750 845873 := bstep (se 2 (by rfl) ⟨317202, by rfl⟩ : syracuseStep 845873 = 634405) B634405
theorem B845923 : Blo 330750 845923 := bstep (se 1 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 845923 = 1268885) B1268885
theorem B944237 : Blo 330750 944237 := bstep (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) B354089
theorem B1108081 : Blo 330750 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B747665 : Blo 330750 747665 := bstep (se 2 (by rfl) ⟨280374, by rfl⟩ : syracuseStep 747665 = 560749) B560749
theorem B747683 : Blo 330750 747683 := bstep (se 1 (by rfl) ⟨560762, by rfl⟩ : syracuseStep 747683 = 1121525) B1121525
theorem B354499 : Blo 330750 354499 := bstep (se 1 (by rfl) ⟨265874, by rfl⟩ : syracuseStep 354499 = 531749) B531749
theorem B846065 : Blo 330750 846065 := bstep (se 2 (by rfl) ⟨317274, by rfl⟩ : syracuseStep 846065 = 634549) B634549
theorem B747953 : Blo 330750 747953 := bstep (se 2 (by rfl) ⟨280482, by rfl⟩ : syracuseStep 747953 = 560965) B560965
theorem B747971 : Blo 330750 747971 := bstep (se 1 (by rfl) ⟨560978, by rfl⟩ : syracuseStep 747971 = 1121957) B1121957
theorem B1894853 : Blo 330750 1894853 := bstep (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) B355285
theorem B1600013 : Blo 330750 1600013 := bstep (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) B600005
theorem B5139085 : Blo 330750 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B420547 : Blo 330750 420547 := bstep (se 1 (by rfl) ⟨315410, by rfl⟩ : syracuseStep 420547 = 630821) B630821
theorem B748241 : Blo 330750 748241 := bstep (se 2 (by rfl) ⟨280590, by rfl⟩ : syracuseStep 748241 = 561181) B561181
theorem B748259 : Blo 330750 748259 := bstep (se 1 (by rfl) ⟨561194, by rfl⟩ : syracuseStep 748259 = 1122389) B1122389
theorem B420643 : Blo 330750 420643 := bstep (se 1 (by rfl) ⟨315482, by rfl⟩ : syracuseStep 420643 = 630965) B630965
theorem B4254605 : Blo 330750 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B1895309 : Blo 330750 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B748529 : Blo 330750 748529 := bstep (se 2 (by rfl) ⟨280698, by rfl⟩ : syracuseStep 748529 = 561397) B561397
theorem B748547 : Blo 330750 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B945229 : Blo 330750 945229 := bstep (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) B354461
theorem B847057 : Blo 330750 847057 := bstep (se 2 (by rfl) ⟨317646, by rfl⟩ : syracuseStep 847057 = 635293) B635293
theorem B748817 : Blo 330750 748817 := bstep (se 2 (by rfl) ⟨280806, by rfl⟩ : syracuseStep 748817 = 561613) B561613
theorem B421139 : Blo 330750 421139 := bstep (se 1 (by rfl) ⟨315854, by rfl⟩ : syracuseStep 421139 = 631709) B631709
theorem B748835 : Blo 330750 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B847331 : Blo 330750 847331 := bstep (se 1 (by rfl) ⟨635498, by rfl⟩ : syracuseStep 847331 = 1270997) B1270997
theorem B749105 : Blo 330750 749105 := bstep (se 2 (by rfl) ⟨280914, by rfl⟩ : syracuseStep 749105 = 561829) B561829
theorem B749123 : Blo 330750 749123 := bstep (se 1 (by rfl) ⟨561842, by rfl⟩ : syracuseStep 749123 = 1123685) B1123685
theorem B1732337 : Blo 330750 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B749393 : Blo 330750 749393 := bstep (se 2 (by rfl) ⟨281022, by rfl⟩ : syracuseStep 749393 = 562045) B562045
theorem B749411 : Blo 330750 749411 := bstep (se 1 (by rfl) ⟨562058, by rfl⟩ : syracuseStep 749411 = 1124117) B1124117
theorem B421843 : Blo 330750 421843 := bstep (se 1 (by rfl) ⟨316382, by rfl⟩ : syracuseStep 421843 = 632765) B632765
theorem B421939 : Blo 330750 421939 := bstep (se 1 (by rfl) ⟨316454, by rfl⟩ : syracuseStep 421939 = 632909) B632909
theorem B749681 : Blo 330750 749681 := bstep (se 2 (by rfl) ⟨281130, by rfl⟩ : syracuseStep 749681 = 562261) B562261
theorem B749699 : Blo 330750 749699 := bstep (se 1 (by rfl) ⟨562274, by rfl⟩ : syracuseStep 749699 = 1124549) B1124549
theorem B1732963 : Blo 330750 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B749969 : Blo 330750 749969 := bstep (se 2 (by rfl) ⟨281238, by rfl⟩ : syracuseStep 749969 = 562477) B562477
theorem B749987 : Blo 330750 749987 := bstep (se 1 (by rfl) ⟨562490, by rfl⟩ : syracuseStep 749987 = 1124981) B1124981
theorem B4288949 : Blo 330750 4288949 := bstep (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) B402089
theorem B2585029 : Blo 330750 2585029 := bstep (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) B484693
theorem B422435 : Blo 330750 422435 := bstep (se 1 (by rfl) ⟨316826, by rfl⟩ : syracuseStep 422435 = 633653) B633653
theorem B750257 : Blo 330750 750257 := bstep (se 2 (by rfl) ⟨281346, by rfl⟩ : syracuseStep 750257 = 562693) B562693
theorem B750275 : Blo 330750 750275 := bstep (se 1 (by rfl) ⟨562706, by rfl⟩ : syracuseStep 750275 = 1125413) B1125413
theorem B946961 : Blo 330750 946961 := bstep (se 2 (by rfl) ⟨355110, by rfl⟩ : syracuseStep 946961 = 710221) B710221
theorem B357139 : Blo 330750 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B619331 : Blo 330750 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B947153 : Blo 330750 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B750545 : Blo 330750 750545 := bstep (se 2 (by rfl) ⟨281454, by rfl⟩ : syracuseStep 750545 = 562909) B562909
theorem B750563 : Blo 330750 750563 := bstep (se 1 (by rfl) ⟨562922, by rfl⟩ : syracuseStep 750563 = 1125845) B1125845
theorem B423139 : Blo 330750 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B750833 : Blo 330750 750833 := bstep (se 2 (by rfl) ⟨281562, by rfl⟩ : syracuseStep 750833 = 563125) B563125
theorem B750851 : Blo 330750 750851 := bstep (se 1 (by rfl) ⟨563138, by rfl⟩ : syracuseStep 750851 = 1126277) B1126277
theorem B423235 : Blo 330750 423235 := bstep (se 1 (by rfl) ⟨317426, by rfl⟩ : syracuseStep 423235 = 634853) B634853
theorem B1799651 : Blo 330750 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B751121 : Blo 330750 751121 := bstep (se 2 (by rfl) ⟨281670, by rfl⟩ : syracuseStep 751121 = 563341) B563341
theorem B751139 : Blo 330750 751139 := bstep (se 1 (by rfl) ⟨563354, by rfl⟩ : syracuseStep 751139 = 1126709) B1126709
theorem B1275533 : Blo 330750 1275533 := bstep (se 3 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 1275533 = 478325) B478325
theorem B1898225 : Blo 330750 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B751409 : Blo 330750 751409 := bstep (se 2 (by rfl) ⟨281778, by rfl⟩ : syracuseStep 751409 = 563557) B563557
theorem B751427 : Blo 330750 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B948145 : Blo 330750 948145 := bstep (se 2 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 948145 = 711109) B711109
theorem B686051 : Blo 330750 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B751697 : Blo 330750 751697 := bstep (se 2 (by rfl) ⟨281886, by rfl⟩ : syracuseStep 751697 = 563773) B563773
theorem B751715 : Blo 330750 751715 := bstep (se 1 (by rfl) ⟨563786, by rfl⟩ : syracuseStep 751715 = 1127573) B1127573
theorem B948419 : Blo 330750 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B751985 : Blo 330750 751985 := bstep (se 2 (by rfl) ⟨281994, by rfl⟩ : syracuseStep 751985 = 563989) B563989
theorem B948611 : Blo 330750 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B752003 : Blo 330750 752003 := bstep (se 1 (by rfl) ⟨564002, by rfl⟩ : syracuseStep 752003 = 1128005) B1128005
theorem B358835 : Blo 330750 358835 := bstep (se 1 (by rfl) ⟨269126, by rfl⟩ : syracuseStep 358835 = 538253) B538253
theorem B2062883 : Blo 330750 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B752273 : Blo 330750 752273 := bstep (se 2 (by rfl) ⟨282102, by rfl⟩ : syracuseStep 752273 = 564205) B564205
theorem B752291 : Blo 330750 752291 := bstep (se 1 (by rfl) ⟨564218, by rfl⟩ : syracuseStep 752291 = 1128437) B1128437
theorem B752561 : Blo 330750 752561 := bstep (se 2 (by rfl) ⟨282210, by rfl⟩ : syracuseStep 752561 = 564421) B564421
theorem B752579 : Blo 330750 752579 := bstep (se 1 (by rfl) ⟨564434, by rfl⟩ : syracuseStep 752579 = 1128869) B1128869
theorem B1899683 : Blo 330750 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B949421 : Blo 330750 949421 := bstep (se 3 (by rfl) ⟨178016, by rfl⟩ : syracuseStep 949421 = 356033) B356033
theorem B752849 : Blo 330750 752849 := bstep (se 2 (by rfl) ⟨282318, by rfl⟩ : syracuseStep 752849 = 564637) B564637
theorem B2522339 : Blo 330750 2522339 := bstep (se 1 (by rfl) ⟨1891754, by rfl⟩ : syracuseStep 2522339 = 3783509) B3783509
theorem B752867 : Blo 330750 752867 := bstep (se 1 (by rfl) ⟨564650, by rfl⟩ : syracuseStep 752867 = 1129301) B1129301
theorem B949603 : Blo 330750 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B3210637 : Blo 330750 3210637 := bstep (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) B1203989
theorem B1080803 : Blo 330750 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B753137 : Blo 330750 753137 := bstep (se 2 (by rfl) ⟨282426, by rfl⟩ : syracuseStep 753137 = 564853) B564853
theorem B753155 : Blo 330750 753155 := bstep (se 1 (by rfl) ⟨564866, by rfl⟩ : syracuseStep 753155 = 1129733) B1129733
theorem B5766709 : Blo 330750 5766709 := bstep (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) B540629
theorem B2031245 : Blo 330750 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B1343267 : Blo 330750 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B950093 : Blo 330750 950093 := bstep (se 3 (by rfl) ⟨178142, by rfl⟩ : syracuseStep 950093 = 356285) B356285
theorem B1409411 : Blo 330750 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B950707 : Blo 330750 950707 := bstep (se 1 (by rfl) ⟨713030, by rfl⟩ : syracuseStep 950707 = 1426061) B1426061
theorem B2130533 : Blo 330750 2130533 := bstep (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) B399475
theorem B2130583 : Blo 330750 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B950935 : Blo 330750 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B361207 : Blo 330750 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B558731 : Blo 330750 558731 := bstep (se 1 (by rfl) ⟨419048, by rfl⟩ : syracuseStep 558731 = 838097) B838097
theorem B2557619 : Blo 330750 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B558859 : Blo 330750 558859 := bstep (se 1 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 558859 = 838289) B838289
theorem B4261733 : Blo 330750 4261733 := bstep (se 4 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 4261733 = 799075) B799075
theorem B559001 : Blo 330750 559001 := bstep (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) B419251
theorem B559129 : Blo 330750 559129 := bstep (se 2 (by rfl) ⟨209673, by rfl⟩ : syracuseStep 559129 = 419347) B419347
theorem B1608011 : Blo 330750 1608011 := bstep (se 1 (by rfl) ⟨1206008, by rfl⟩ : syracuseStep 1608011 = 2412017) B2412017
theorem B756097 : Blo 330750 756097 := bstep (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) B567073
theorem B2034071 : Blo 330750 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B952793 : Blo 330750 952793 := bstep (se 2 (by rfl) ⟨357297, by rfl⟩ : syracuseStep 952793 = 714595) B714595
theorem B2525741 : Blo 330750 2525741 := bstep (se 3 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 2525741 = 947153) B947153
theorem B559703 : Blo 330750 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B2722405 : Blo 330750 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B1903283 : Blo 330750 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B559831 : Blo 330750 559831 := bstep (se 1 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 559831 = 839747) B839747
theorem B1477441 : Blo 330750 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B1280843 : Blo 330750 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B330763 : Blo 330750 330763 := bstep (se 1 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 330763 = 496145) B496145
theorem B330775 : Blo 330750 330775 := bstep (se 1 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 330775 = 496163) B496163
theorem B330795 : Blo 330750 330795 := bstep (se 1 (by rfl) ⟨248096, by rfl⟩ : syracuseStep 330795 = 496193) B496193
theorem B330807 : Blo 330750 330807 := bstep (se 1 (by rfl) ⟨248105, by rfl⟩ : syracuseStep 330807 = 496211) B496211
theorem B330827 : Blo 330750 330827 := bstep (se 1 (by rfl) ⟨248120, by rfl⟩ : syracuseStep 330827 = 496241) B496241
theorem B1117259 : Blo 330750 1117259 := bstep (se 1 (by rfl) ⟨837944, by rfl⟩ : syracuseStep 1117259 = 1675889) B1675889
theorem B330839 : Blo 330750 330839 := bstep (se 1 (by rfl) ⟨248129, by rfl⟩ : syracuseStep 330839 = 496259) B496259
theorem B2886749 : Blo 330750 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B330859 : Blo 330750 330859 := bstep (se 1 (by rfl) ⟨248144, by rfl⟩ : syracuseStep 330859 = 496289) B496289
theorem B330871 : Blo 330750 330871 := bstep (se 1 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 330871 = 496307) B496307
theorem B330891 : Blo 330750 330891 := bstep (se 1 (by rfl) ⟨248168, by rfl⟩ : syracuseStep 330891 = 496337) B496337
theorem B330903 : Blo 330750 330903 := bstep (se 1 (by rfl) ⟨248177, by rfl⟩ : syracuseStep 330903 = 496355) B496355
theorem B330923 : Blo 330750 330923 := bstep (se 1 (by rfl) ⟨248192, by rfl⟩ : syracuseStep 330923 = 496385) B496385
theorem B330935 : Blo 330750 330935 := bstep (se 1 (by rfl) ⟨248201, by rfl⟩ : syracuseStep 330935 = 496403) B496403
theorem B330955 : Blo 330750 330955 := bstep (se 1 (by rfl) ⟨248216, by rfl⟩ : syracuseStep 330955 = 496433) B496433
theorem B330967 : Blo 330750 330967 := bstep (se 1 (by rfl) ⟨248225, by rfl⟩ : syracuseStep 330967 = 496451) B496451
theorem B330987 : Blo 330750 330987 := bstep (se 1 (by rfl) ⟨248240, by rfl⟩ : syracuseStep 330987 = 496481) B496481
theorem B330999 : Blo 330750 330999 := bstep (se 1 (by rfl) ⟨248249, by rfl⟩ : syracuseStep 330999 = 496499) B496499
theorem B331019 : Blo 330750 331019 := bstep (se 1 (by rfl) ⟨248264, by rfl⟩ : syracuseStep 331019 = 496529) B496529
theorem B331031 : Blo 330750 331031 := bstep (se 1 (by rfl) ⟨248273, by rfl⟩ : syracuseStep 331031 = 496547) B496547
theorem B331051 : Blo 330750 331051 := bstep (se 1 (by rfl) ⟨248288, by rfl⟩ : syracuseStep 331051 = 496577) B496577
theorem B331063 : Blo 330750 331063 := bstep (se 1 (by rfl) ⟨248297, by rfl⟩ : syracuseStep 331063 = 496595) B496595
theorem B331083 : Blo 330750 331083 := bstep (se 1 (by rfl) ⟨248312, by rfl⟩ : syracuseStep 331083 = 496625) B496625
theorem B560459 : Blo 330750 560459 := bstep (se 1 (by rfl) ⟨420344, by rfl⟩ : syracuseStep 560459 = 840689) B840689
theorem B331095 : Blo 330750 331095 := bstep (se 1 (by rfl) ⟨248321, by rfl⟩ : syracuseStep 331095 = 496643) B496643
theorem B1117529 : Blo 330750 1117529 := bstep (se 2 (by rfl) ⟨419073, by rfl⟩ : syracuseStep 1117529 = 838147) B838147
theorem B331115 : Blo 330750 331115 := bstep (se 1 (by rfl) ⟨248336, by rfl⟩ : syracuseStep 331115 = 496673) B496673
theorem B331127 : Blo 330750 331127 := bstep (se 1 (by rfl) ⟨248345, by rfl⟩ : syracuseStep 331127 = 496691) B496691
theorem B331147 : Blo 330750 331147 := bstep (se 1 (by rfl) ⟨248360, by rfl⟩ : syracuseStep 331147 = 496721) B496721
theorem B331159 : Blo 330750 331159 := bstep (se 1 (by rfl) ⟨248369, by rfl⟩ : syracuseStep 331159 = 496739) B496739
theorem B331179 : Blo 330750 331179 := bstep (se 1 (by rfl) ⟨248384, by rfl⟩ : syracuseStep 331179 = 496769) B496769
theorem B331191 : Blo 330750 331191 := bstep (se 1 (by rfl) ⟨248393, by rfl⟩ : syracuseStep 331191 = 496787) B496787
theorem B331211 : Blo 330750 331211 := bstep (se 1 (by rfl) ⟨248408, by rfl⟩ : syracuseStep 331211 = 496817) B496817
theorem B560587 : Blo 330750 560587 := bstep (se 1 (by rfl) ⟨420440, by rfl⟩ : syracuseStep 560587 = 840881) B840881
theorem B331223 : Blo 330750 331223 := bstep (se 1 (by rfl) ⟨248417, by rfl⟩ : syracuseStep 331223 = 496835) B496835
theorem B331243 : Blo 330750 331243 := bstep (se 1 (by rfl) ⟨248432, by rfl⟩ : syracuseStep 331243 = 496865) B496865
theorem B331255 : Blo 330750 331255 := bstep (se 1 (by rfl) ⟨248441, by rfl⟩ : syracuseStep 331255 = 496883) B496883
theorem B331275 : Blo 330750 331275 := bstep (se 1 (by rfl) ⟨248456, by rfl⟩ : syracuseStep 331275 = 496913) B496913
theorem B757259 : Blo 330750 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B6852113 : Blo 330750 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B331287 : Blo 330750 331287 := bstep (se 1 (by rfl) ⟨248465, by rfl⟩ : syracuseStep 331287 = 496931) B496931
theorem B331307 : Blo 330750 331307 := bstep (se 1 (by rfl) ⟨248480, by rfl⟩ : syracuseStep 331307 = 496961) B496961
theorem B331319 : Blo 330750 331319 := bstep (se 1 (by rfl) ⟨248489, by rfl⟩ : syracuseStep 331319 = 496979) B496979
theorem B331339 : Blo 330750 331339 := bstep (se 1 (by rfl) ⟨248504, by rfl⟩ : syracuseStep 331339 = 497009) B497009
theorem B331351 : Blo 330750 331351 := bstep (se 1 (by rfl) ⟨248513, by rfl⟩ : syracuseStep 331351 = 497027) B497027
theorem B560729 : Blo 330750 560729 := bstep (se 2 (by rfl) ⟨210273, by rfl⟩ : syracuseStep 560729 = 420547) B420547
theorem B331371 : Blo 330750 331371 := bstep (se 1 (by rfl) ⟨248528, by rfl⟩ : syracuseStep 331371 = 497057) B497057
theorem B331383 : Blo 330750 331383 := bstep (se 1 (by rfl) ⟨248537, by rfl⟩ : syracuseStep 331383 = 497075) B497075
theorem B331403 : Blo 330750 331403 := bstep (se 1 (by rfl) ⟨248552, by rfl⟩ : syracuseStep 331403 = 497105) B497105
theorem B331415 : Blo 330750 331415 := bstep (se 1 (by rfl) ⟨248561, by rfl⟩ : syracuseStep 331415 = 497123) B497123
theorem B331435 : Blo 330750 331435 := bstep (se 1 (by rfl) ⟨248576, by rfl⟩ : syracuseStep 331435 = 497153) B497153
theorem B331447 : Blo 330750 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B331467 : Blo 330750 331467 := bstep (se 1 (by rfl) ⟨248600, by rfl⟩ : syracuseStep 331467 = 497201) B497201
theorem B331479 : Blo 330750 331479 := bstep (se 1 (by rfl) ⟨248609, by rfl⟩ : syracuseStep 331479 = 497219) B497219
theorem B560857 : Blo 330750 560857 := bstep (se 2 (by rfl) ⟨210321, by rfl⟩ : syracuseStep 560857 = 420643) B420643
theorem B331499 : Blo 330750 331499 := bstep (se 1 (by rfl) ⟨248624, by rfl⟩ : syracuseStep 331499 = 497249) B497249
theorem B331511 : Blo 330750 331511 := bstep (se 1 (by rfl) ⟨248633, by rfl⟩ : syracuseStep 331511 = 497267) B497267
theorem B331531 : Blo 330750 331531 := bstep (se 1 (by rfl) ⟨248648, by rfl⟩ : syracuseStep 331531 = 497297) B497297
theorem B331543 : Blo 330750 331543 := bstep (se 1 (by rfl) ⟨248657, by rfl⟩ : syracuseStep 331543 = 497315) B497315
theorem B331563 : Blo 330750 331563 := bstep (se 1 (by rfl) ⟨248672, by rfl⟩ : syracuseStep 331563 = 497345) B497345
theorem B331575 : Blo 330750 331575 := bstep (se 1 (by rfl) ⟨248681, by rfl⟩ : syracuseStep 331575 = 497363) B497363
theorem B1412939 : Blo 330750 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B331595 : Blo 330750 331595 := bstep (se 1 (by rfl) ⟨248696, by rfl⟩ : syracuseStep 331595 = 497393) B497393
theorem B331607 : Blo 330750 331607 := bstep (se 1 (by rfl) ⟨248705, by rfl⟩ : syracuseStep 331607 = 497411) B497411
theorem B331627 : Blo 330750 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B331639 : Blo 330750 331639 := bstep (se 1 (by rfl) ⟨248729, by rfl⟩ : syracuseStep 331639 = 497459) B497459
theorem B331659 : Blo 330750 331659 := bstep (se 1 (by rfl) ⟨248744, by rfl⟩ : syracuseStep 331659 = 497489) B497489
theorem B331671 : Blo 330750 331671 := bstep (se 1 (by rfl) ⟨248753, by rfl⟩ : syracuseStep 331671 = 497507) B497507
theorem B331691 : Blo 330750 331691 := bstep (se 1 (by rfl) ⟨248768, by rfl⟩ : syracuseStep 331691 = 497537) B497537
theorem B331703 : Blo 330750 331703 := bstep (se 1 (by rfl) ⟨248777, by rfl⟩ : syracuseStep 331703 = 497555) B497555
theorem B331723 : Blo 330750 331723 := bstep (se 1 (by rfl) ⟨248792, by rfl⟩ : syracuseStep 331723 = 497585) B497585
theorem B331735 : Blo 330750 331735 := bstep (se 1 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 331735 = 497603) B497603
theorem B331755 : Blo 330750 331755 := bstep (se 1 (by rfl) ⟨248816, by rfl⟩ : syracuseStep 331755 = 497633) B497633
theorem B331767 : Blo 330750 331767 := bstep (se 1 (by rfl) ⟨248825, by rfl⟩ : syracuseStep 331767 = 497651) B497651
theorem B331787 : Blo 330750 331787 := bstep (se 1 (by rfl) ⟨248840, by rfl⟩ : syracuseStep 331787 = 497681) B497681
theorem B1118231 : Blo 330750 1118231 := bstep (se 1 (by rfl) ⟨838673, by rfl⟩ : syracuseStep 1118231 = 1677347) B1677347
theorem B331799 : Blo 330750 331799 := bstep (se 1 (by rfl) ⟨248849, by rfl⟩ : syracuseStep 331799 = 497699) B497699
theorem B331819 : Blo 330750 331819 := bstep (se 1 (by rfl) ⟨248864, by rfl⟩ : syracuseStep 331819 = 497729) B497729
theorem B331831 : Blo 330750 331831 := bstep (se 1 (by rfl) ⟨248873, by rfl⟩ : syracuseStep 331831 = 497747) B497747
theorem B331851 : Blo 330750 331851 := bstep (se 1 (by rfl) ⟨248888, by rfl⟩ : syracuseStep 331851 = 497777) B497777
theorem B331863 : Blo 330750 331863 := bstep (se 1 (by rfl) ⟨248897, by rfl⟩ : syracuseStep 331863 = 497795) B497795
theorem B1904741 : Blo 330750 1904741 := bstep (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) B357139
theorem B331883 : Blo 330750 331883 := bstep (se 1 (by rfl) ⟨248912, by rfl⟩ : syracuseStep 331883 = 497825) B497825
theorem B331895 : Blo 330750 331895 := bstep (se 1 (by rfl) ⟨248921, by rfl⟩ : syracuseStep 331895 = 497843) B497843
theorem B2134147 : Blo 330750 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B331915 : Blo 330750 331915 := bstep (se 1 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 331915 = 497873) B497873
theorem B331927 : Blo 330750 331927 := bstep (se 1 (by rfl) ⟨248945, by rfl⟩ : syracuseStep 331927 = 497891) B497891
theorem B331947 : Blo 330750 331947 := bstep (se 1 (by rfl) ⟨248960, by rfl⟩ : syracuseStep 331947 = 497921) B497921
theorem B331959 : Blo 330750 331959 := bstep (se 1 (by rfl) ⟨248969, by rfl⟩ : syracuseStep 331959 = 497939) B497939
theorem B331979 : Blo 330750 331979 := bstep (se 1 (by rfl) ⟨248984, by rfl⟩ : syracuseStep 331979 = 497969) B497969
theorem B331991 : Blo 330750 331991 := bstep (se 1 (by rfl) ⟨248993, by rfl⟩ : syracuseStep 331991 = 497987) B497987
theorem B332011 : Blo 330750 332011 := bstep (se 1 (by rfl) ⟨249008, by rfl⟩ : syracuseStep 332011 = 498017) B498017
theorem B332023 : Blo 330750 332023 := bstep (se 1 (by rfl) ⟨249017, by rfl⟩ : syracuseStep 332023 = 498035) B498035
theorem B332043 : Blo 330750 332043 := bstep (se 1 (by rfl) ⟨249032, by rfl⟩ : syracuseStep 332043 = 498065) B498065
theorem B332055 : Blo 330750 332055 := bstep (se 1 (by rfl) ⟨249041, by rfl⟩ : syracuseStep 332055 = 498083) B498083
theorem B561431 : Blo 330750 561431 := bstep (se 1 (by rfl) ⟨421073, by rfl⟩ : syracuseStep 561431 = 842147) B842147
theorem B332075 : Blo 330750 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B1675565 : Blo 330750 1675565 := bstep (se 3 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 1675565 = 628337) B628337
theorem B332087 : Blo 330750 332087 := bstep (se 1 (by rfl) ⟨249065, by rfl⟩ : syracuseStep 332087 = 498131) B498131
theorem B332107 : Blo 330750 332107 := bstep (se 1 (by rfl) ⟨249080, by rfl⟩ : syracuseStep 332107 = 498161) B498161
theorem B332119 : Blo 330750 332119 := bstep (se 1 (by rfl) ⟨249089, by rfl⟩ : syracuseStep 332119 = 498179) B498179
theorem B332139 : Blo 330750 332139 := bstep (se 1 (by rfl) ⟨249104, by rfl⟩ : syracuseStep 332139 = 498209) B498209
theorem B332151 : Blo 330750 332151 := bstep (se 1 (by rfl) ⟨249113, by rfl⟩ : syracuseStep 332151 = 498227) B498227
theorem B3019139 : Blo 330750 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B332171 : Blo 330750 332171 := bstep (se 1 (by rfl) ⟨249128, by rfl⟩ : syracuseStep 332171 = 498257) B498257
theorem B1413521 : Blo 330750 1413521 := bstep (se 2 (by rfl) ⟨530070, by rfl⟩ : syracuseStep 1413521 = 1060141) B1060141
theorem B332183 : Blo 330750 332183 := bstep (se 1 (by rfl) ⟨249137, by rfl⟩ : syracuseStep 332183 = 498275) B498275
theorem B561559 : Blo 330750 561559 := bstep (se 1 (by rfl) ⟨421169, by rfl⟩ : syracuseStep 561559 = 842339) B842339
theorem B332203 : Blo 330750 332203 := bstep (se 1 (by rfl) ⟨249152, by rfl⟩ : syracuseStep 332203 = 498305) B498305
theorem B332215 : Blo 330750 332215 := bstep (se 1 (by rfl) ⟨249161, by rfl⟩ : syracuseStep 332215 = 498323) B498323
theorem B332235 : Blo 330750 332235 := bstep (se 1 (by rfl) ⟨249176, by rfl⟩ : syracuseStep 332235 = 498353) B498353
theorem B332247 : Blo 330750 332247 := bstep (se 1 (by rfl) ⟨249185, by rfl⟩ : syracuseStep 332247 = 498371) B498371
theorem B332267 : Blo 330750 332267 := bstep (se 1 (by rfl) ⟨249200, by rfl⟩ : syracuseStep 332267 = 498401) B498401
theorem B332279 : Blo 330750 332279 := bstep (se 1 (by rfl) ⟨249209, by rfl⟩ : syracuseStep 332279 = 498419) B498419
theorem B496139 : Blo 330750 496139 := bstep (se 1 (by rfl) ⟨372104, by rfl⟩ : syracuseStep 496139 = 744209) B744209
theorem B332299 : Blo 330750 332299 := bstep (se 1 (by rfl) ⟨249224, by rfl⟩ : syracuseStep 332299 = 498449) B498449
theorem B496151 : Blo 330750 496151 := bstep (se 1 (by rfl) ⟨372113, by rfl⟩ : syracuseStep 496151 = 744227) B744227
theorem B332311 : Blo 330750 332311 := bstep (se 1 (by rfl) ⟨249233, by rfl⟩ : syracuseStep 332311 = 498467) B498467
theorem B332331 : Blo 330750 332331 := bstep (se 1 (by rfl) ⟨249248, by rfl⟩ : syracuseStep 332331 = 498497) B498497
theorem B1118771 : Blo 330750 1118771 := bstep (se 1 (by rfl) ⟨839078, by rfl⟩ : syracuseStep 1118771 = 1678157) B1678157
theorem B332343 : Blo 330750 332343 := bstep (se 1 (by rfl) ⟨249257, by rfl⟩ : syracuseStep 332343 = 498515) B498515
theorem B332363 : Blo 330750 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B332375 : Blo 330750 332375 := bstep (se 1 (by rfl) ⟨249281, by rfl⟩ : syracuseStep 332375 = 498563) B498563
theorem B496217 : Blo 330750 496217 := bstep (se 2 (by rfl) ⟨186081, by rfl⟩ : syracuseStep 496217 = 372163) B372163
theorem B332395 : Blo 330750 332395 := bstep (se 1 (by rfl) ⟨249296, by rfl⟩ : syracuseStep 332395 = 498593) B498593
theorem B332407 : Blo 330750 332407 := bstep (se 1 (by rfl) ⟨249305, by rfl⟩ : syracuseStep 332407 = 498611) B498611
theorem B332427 : Blo 330750 332427 := bstep (se 1 (by rfl) ⟨249320, by rfl⟩ : syracuseStep 332427 = 498641) B498641
theorem B332439 : Blo 330750 332439 := bstep (se 1 (by rfl) ⟨249329, by rfl⟩ : syracuseStep 332439 = 498659) B498659
theorem B332459 : Blo 330750 332459 := bstep (se 1 (by rfl) ⟨249344, by rfl⟩ : syracuseStep 332459 = 498689) B498689
theorem B332471 : Blo 330750 332471 := bstep (se 1 (by rfl) ⟨249353, by rfl⟩ : syracuseStep 332471 = 498707) B498707
theorem B496331 : Blo 330750 496331 := bstep (se 1 (by rfl) ⟨372248, by rfl⟩ : syracuseStep 496331 = 744497) B744497
theorem B332491 : Blo 330750 332491 := bstep (se 1 (by rfl) ⟨249368, by rfl⟩ : syracuseStep 332491 = 498737) B498737
theorem B496343 : Blo 330750 496343 := bstep (se 1 (by rfl) ⟨372257, by rfl⟩ : syracuseStep 496343 = 744515) B744515
theorem B332503 : Blo 330750 332503 := bstep (se 1 (by rfl) ⟨249377, by rfl⟩ : syracuseStep 332503 = 498755) B498755
theorem B332523 : Blo 330750 332523 := bstep (se 1 (by rfl) ⟨249392, by rfl⟩ : syracuseStep 332523 = 498785) B498785
theorem B332535 : Blo 330750 332535 := bstep (se 1 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 332535 = 498803) B498803
theorem B332555 : Blo 330750 332555 := bstep (se 1 (by rfl) ⟨249416, by rfl⟩ : syracuseStep 332555 = 498833) B498833
theorem B332567 : Blo 330750 332567 := bstep (se 1 (by rfl) ⟨249425, by rfl⟩ : syracuseStep 332567 = 498851) B498851
theorem B496409 : Blo 330750 496409 := bstep (se 2 (by rfl) ⟨186153, by rfl⟩ : syracuseStep 496409 = 372307) B372307
theorem B332587 : Blo 330750 332587 := bstep (se 1 (by rfl) ⟨249440, by rfl⟩ : syracuseStep 332587 = 498881) B498881
theorem B332599 : Blo 330750 332599 := bstep (se 1 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 332599 = 498899) B498899
theorem B1119041 : Blo 330750 1119041 := bstep (se 2 (by rfl) ⟨419640, by rfl⟩ : syracuseStep 1119041 = 839281) B839281
theorem B332619 : Blo 330750 332619 := bstep (se 1 (by rfl) ⟨249464, by rfl⟩ : syracuseStep 332619 = 498929) B498929
theorem B332631 : Blo 330750 332631 := bstep (se 1 (by rfl) ⟨249473, by rfl⟩ : syracuseStep 332631 = 498947) B498947
theorem B332651 : Blo 330750 332651 := bstep (se 1 (by rfl) ⟨249488, by rfl⟩ : syracuseStep 332651 = 498977) B498977
theorem B332663 : Blo 330750 332663 := bstep (se 1 (by rfl) ⟨249497, by rfl⟩ : syracuseStep 332663 = 498995) B498995
theorem B496523 : Blo 330750 496523 := bstep (se 1 (by rfl) ⟨372392, by rfl⟩ : syracuseStep 496523 = 744785) B744785
theorem B332683 : Blo 330750 332683 := bstep (se 1 (by rfl) ⟨249512, by rfl⟩ : syracuseStep 332683 = 499025) B499025
theorem B496535 : Blo 330750 496535 := bstep (se 1 (by rfl) ⟨372401, by rfl⟩ : syracuseStep 496535 = 744803) B744803
theorem B332695 : Blo 330750 332695 := bstep (se 1 (by rfl) ⟨249521, by rfl⟩ : syracuseStep 332695 = 499043) B499043
theorem B332715 : Blo 330750 332715 := bstep (se 1 (by rfl) ⟨249536, by rfl⟩ : syracuseStep 332715 = 499073) B499073
theorem B5575601 : Blo 330750 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B332727 : Blo 330750 332727 := bstep (se 1 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 332727 = 499091) B499091
theorem B332747 : Blo 330750 332747 := bstep (se 1 (by rfl) ⟨249560, by rfl⟩ : syracuseStep 332747 = 499121) B499121
theorem B332759 : Blo 330750 332759 := bstep (se 1 (by rfl) ⟨249569, by rfl⟩ : syracuseStep 332759 = 499139) B499139
theorem B496601 : Blo 330750 496601 := bstep (se 2 (by rfl) ⟨186225, by rfl⟩ : syracuseStep 496601 = 372451) B372451
theorem B332779 : Blo 330750 332779 := bstep (se 1 (by rfl) ⟨249584, by rfl⟩ : syracuseStep 332779 = 499169) B499169
theorem B332791 : Blo 330750 332791 := bstep (se 1 (by rfl) ⟨249593, by rfl⟩ : syracuseStep 332791 = 499187) B499187
theorem B332811 : Blo 330750 332811 := bstep (se 1 (by rfl) ⟨249608, by rfl⟩ : syracuseStep 332811 = 499217) B499217
theorem B562187 : Blo 330750 562187 := bstep (se 1 (by rfl) ⟨421640, by rfl⟩ : syracuseStep 562187 = 843281) B843281
theorem B332823 : Blo 330750 332823 := bstep (se 1 (by rfl) ⟨249617, by rfl⟩ : syracuseStep 332823 = 499235) B499235
theorem B332843 : Blo 330750 332843 := bstep (se 1 (by rfl) ⟨249632, by rfl⟩ : syracuseStep 332843 = 499265) B499265
theorem B332855 : Blo 330750 332855 := bstep (se 1 (by rfl) ⟨249641, by rfl⟩ : syracuseStep 332855 = 499283) B499283
theorem B496715 : Blo 330750 496715 := bstep (se 1 (by rfl) ⟨372536, by rfl⟩ : syracuseStep 496715 = 745073) B745073
theorem B332875 : Blo 330750 332875 := bstep (se 1 (by rfl) ⟨249656, by rfl⟩ : syracuseStep 332875 = 499313) B499313
theorem B496727 : Blo 330750 496727 := bstep (se 1 (by rfl) ⟨372545, by rfl⟩ : syracuseStep 496727 = 745091) B745091
theorem B332887 : Blo 330750 332887 := bstep (se 1 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 332887 = 499331) B499331
theorem B1807453 : Blo 330750 1807453 := bstep (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) B677795
theorem B332907 : Blo 330750 332907 := bstep (se 1 (by rfl) ⟨249680, by rfl⟩ : syracuseStep 332907 = 499361) B499361
theorem B332919 : Blo 330750 332919 := bstep (se 1 (by rfl) ⟨249689, by rfl⟩ : syracuseStep 332919 = 499379) B499379
theorem B332939 : Blo 330750 332939 := bstep (se 1 (by rfl) ⟨249704, by rfl⟩ : syracuseStep 332939 = 499409) B499409
theorem B562315 : Blo 330750 562315 := bstep (se 1 (by rfl) ⟨421736, by rfl⟩ : syracuseStep 562315 = 843473) B843473
theorem B332951 : Blo 330750 332951 := bstep (se 1 (by rfl) ⟨249713, by rfl⟩ : syracuseStep 332951 = 499427) B499427
theorem B496793 : Blo 330750 496793 := bstep (se 2 (by rfl) ⟨186297, by rfl⟩ : syracuseStep 496793 = 372595) B372595
theorem B332971 : Blo 330750 332971 := bstep (se 1 (by rfl) ⟨249728, by rfl⟩ : syracuseStep 332971 = 499457) B499457
theorem B332983 : Blo 330750 332983 := bstep (se 1 (by rfl) ⟨249737, by rfl⟩ : syracuseStep 332983 = 499475) B499475
theorem B333003 : Blo 330750 333003 := bstep (se 1 (by rfl) ⟨249752, by rfl⟩ : syracuseStep 333003 = 499505) B499505
theorem B333015 : Blo 330750 333015 := bstep (se 1 (by rfl) ⟨249761, by rfl⟩ : syracuseStep 333015 = 499523) B499523
theorem B333035 : Blo 330750 333035 := bstep (se 1 (by rfl) ⟨249776, by rfl⟩ : syracuseStep 333035 = 499553) B499553
theorem B333047 : Blo 330750 333047 := bstep (se 1 (by rfl) ⟨249785, by rfl⟩ : syracuseStep 333047 = 499571) B499571
theorem B496907 : Blo 330750 496907 := bstep (se 1 (by rfl) ⟨372680, by rfl⟩ : syracuseStep 496907 = 745361) B745361
theorem B333067 : Blo 330750 333067 := bstep (se 1 (by rfl) ⟨249800, by rfl⟩ : syracuseStep 333067 = 499601) B499601
theorem B496919 : Blo 330750 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B398615 : Blo 330750 398615 := bstep (se 1 (by rfl) ⟨298961, by rfl⟩ : syracuseStep 398615 = 597923) B597923
theorem B333079 : Blo 330750 333079 := bstep (se 1 (by rfl) ⟨249809, by rfl⟩ : syracuseStep 333079 = 499619) B499619
theorem B562457 : Blo 330750 562457 := bstep (se 2 (by rfl) ⟨210921, by rfl⟩ : syracuseStep 562457 = 421843) B421843
theorem B333099 : Blo 330750 333099 := bstep (se 1 (by rfl) ⟨249824, by rfl⟩ : syracuseStep 333099 = 499649) B499649
theorem B759091 : Blo 330750 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B333111 : Blo 330750 333111 := bstep (se 1 (by rfl) ⟨249833, by rfl⟩ : syracuseStep 333111 = 499667) B499667
theorem B333131 : Blo 330750 333131 := bstep (se 1 (by rfl) ⟨249848, by rfl⟩ : syracuseStep 333131 = 499697) B499697
theorem B333143 : Blo 330750 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B496985 : Blo 330750 496985 := bstep (se 2 (by rfl) ⟨186369, by rfl⟩ : syracuseStep 496985 = 372739) B372739
theorem B1119581 : Blo 330750 1119581 := bstep (se 3 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 1119581 = 419843) B419843
theorem B4560229 : Blo 330750 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B4330853 : Blo 330750 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B333163 : Blo 330750 333163 := bstep (se 1 (by rfl) ⟨249872, by rfl⟩ : syracuseStep 333163 = 499745) B499745
theorem B333175 : Blo 330750 333175 := bstep (se 1 (by rfl) ⟨249881, by rfl⟩ : syracuseStep 333175 = 499763) B499763
theorem B333195 : Blo 330750 333195 := bstep (se 1 (by rfl) ⟨249896, by rfl⟩ : syracuseStep 333195 = 499793) B499793
theorem B333207 : Blo 330750 333207 := bstep (se 1 (by rfl) ⟨249905, by rfl⟩ : syracuseStep 333207 = 499811) B499811
theorem B562585 : Blo 330750 562585 := bstep (se 2 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 562585 = 421939) B421939
theorem B333227 : Blo 330750 333227 := bstep (se 1 (by rfl) ⟨249920, by rfl⟩ : syracuseStep 333227 = 499841) B499841
theorem B1414579 : Blo 330750 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B333239 : Blo 330750 333239 := bstep (se 1 (by rfl) ⟨249929, by rfl⟩ : syracuseStep 333239 = 499859) B499859
theorem B497099 : Blo 330750 497099 := bstep (se 1 (by rfl) ⟨372824, by rfl⟩ : syracuseStep 497099 = 745649) B745649
theorem B333259 : Blo 330750 333259 := bstep (se 1 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 333259 = 499889) B499889
theorem B497111 : Blo 330750 497111 := bstep (se 1 (by rfl) ⟨372833, by rfl⟩ : syracuseStep 497111 = 745667) B745667
theorem B333271 : Blo 330750 333271 := bstep (se 1 (by rfl) ⟨249953, by rfl⟩ : syracuseStep 333271 = 499907) B499907
theorem B333291 : Blo 330750 333291 := bstep (se 1 (by rfl) ⟨249968, by rfl⟩ : syracuseStep 333291 = 499937) B499937
theorem B333303 : Blo 330750 333303 := bstep (se 1 (by rfl) ⟨249977, by rfl⟩ : syracuseStep 333303 = 499955) B499955
theorem B333323 : Blo 330750 333323 := bstep (se 1 (by rfl) ⟨249992, by rfl⟩ : syracuseStep 333323 = 499985) B499985
theorem B333335 : Blo 330750 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B497177 : Blo 330750 497177 := bstep (se 2 (by rfl) ⟨186441, by rfl⟩ : syracuseStep 497177 = 372883) B372883
theorem B4298275 : Blo 330750 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B333355 : Blo 330750 333355 := bstep (se 1 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 333355 = 500033) B500033
theorem B333367 : Blo 330750 333367 := bstep (se 1 (by rfl) ⟨250025, by rfl⟩ : syracuseStep 333367 = 500051) B500051
theorem B333387 : Blo 330750 333387 := bstep (se 1 (by rfl) ⟨250040, by rfl⟩ : syracuseStep 333387 = 500081) B500081
theorem B333399 : Blo 330750 333399 := bstep (se 1 (by rfl) ⟨250049, by rfl⟩ : syracuseStep 333399 = 500099) B500099
theorem B333419 : Blo 330750 333419 := bstep (se 1 (by rfl) ⟨250064, by rfl⟩ : syracuseStep 333419 = 500129) B500129
theorem B333431 : Blo 330750 333431 := bstep (se 1 (by rfl) ⟨250073, by rfl⟩ : syracuseStep 333431 = 500147) B500147
theorem B497291 : Blo 330750 497291 := bstep (se 1 (by rfl) ⟨372968, by rfl⟩ : syracuseStep 497291 = 745937) B745937
theorem B333451 : Blo 330750 333451 := bstep (se 1 (by rfl) ⟨250088, by rfl⟩ : syracuseStep 333451 = 500177) B500177
theorem B497303 : Blo 330750 497303 := bstep (se 1 (by rfl) ⟨372977, by rfl⟩ : syracuseStep 497303 = 745955) B745955
theorem B333463 : Blo 330750 333463 := bstep (se 1 (by rfl) ⟨250097, by rfl⟩ : syracuseStep 333463 = 500195) B500195
theorem B333483 : Blo 330750 333483 := bstep (se 1 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 333483 = 500225) B500225
theorem B333495 : Blo 330750 333495 := bstep (se 1 (by rfl) ⟨250121, by rfl⟩ : syracuseStep 333495 = 500243) B500243
theorem B333515 : Blo 330750 333515 := bstep (se 1 (by rfl) ⟨250136, by rfl⟩ : syracuseStep 333515 = 500273) B500273
theorem B530135 : Blo 330750 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B497369 : Blo 330750 497369 := bstep (se 2 (by rfl) ⟨186513, by rfl⟩ : syracuseStep 497369 = 373027) B373027
theorem B333527 : Blo 330750 333527 := bstep (se 1 (by rfl) ⟨250145, by rfl⟩ : syracuseStep 333527 = 500291) B500291
theorem B333547 : Blo 330750 333547 := bstep (se 1 (by rfl) ⟨250160, by rfl⟩ : syracuseStep 333547 = 500321) B500321
theorem B333559 : Blo 330750 333559 := bstep (se 1 (by rfl) ⟨250169, by rfl⟩ : syracuseStep 333559 = 500339) B500339
theorem B333579 : Blo 330750 333579 := bstep (se 1 (by rfl) ⟨250184, by rfl⟩ : syracuseStep 333579 = 500369) B500369
theorem B333591 : Blo 330750 333591 := bstep (se 1 (by rfl) ⟨250193, by rfl⟩ : syracuseStep 333591 = 500387) B500387
theorem B333611 : Blo 330750 333611 := bstep (se 1 (by rfl) ⟨250208, by rfl⟩ : syracuseStep 333611 = 500417) B500417
theorem B333623 : Blo 330750 333623 := bstep (se 1 (by rfl) ⟨250217, by rfl⟩ : syracuseStep 333623 = 500435) B500435
theorem B497483 : Blo 330750 497483 := bstep (se 1 (by rfl) ⟨373112, by rfl⟩ : syracuseStep 497483 = 746225) B746225
theorem B333643 : Blo 330750 333643 := bstep (se 1 (by rfl) ⟨250232, by rfl⟩ : syracuseStep 333643 = 500465) B500465
theorem B497495 : Blo 330750 497495 := bstep (se 1 (by rfl) ⟨373121, by rfl⟩ : syracuseStep 497495 = 746243) B746243
theorem B333655 : Blo 330750 333655 := bstep (se 1 (by rfl) ⟨250241, by rfl⟩ : syracuseStep 333655 = 500483) B500483
theorem B333675 : Blo 330750 333675 := bstep (se 1 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 333675 = 500513) B500513
theorem B333687 : Blo 330750 333687 := bstep (se 1 (by rfl) ⟨250265, by rfl⟩ : syracuseStep 333687 = 500531) B500531
theorem B333707 : Blo 330750 333707 := bstep (se 1 (by rfl) ⟨250280, by rfl⟩ : syracuseStep 333707 = 500561) B500561
theorem B530327 : Blo 330750 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B333719 : Blo 330750 333719 := bstep (se 1 (by rfl) ⟨250289, by rfl⟩ : syracuseStep 333719 = 500579) B500579
theorem B497561 : Blo 330750 497561 := bstep (se 2 (by rfl) ⟨186585, by rfl⟩ : syracuseStep 497561 = 373171) B373171
theorem B333739 : Blo 330750 333739 := bstep (se 1 (by rfl) ⟨250304, by rfl⟩ : syracuseStep 333739 = 500609) B500609
theorem B3446705 : Blo 330750 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B333751 : Blo 330750 333751 := bstep (se 1 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 333751 = 500627) B500627
theorem B333771 : Blo 330750 333771 := bstep (se 1 (by rfl) ⟨250328, by rfl⟩ : syracuseStep 333771 = 500657) B500657
theorem B563159 : Blo 330750 563159 := bstep (se 1 (by rfl) ⟨422369, by rfl⟩ : syracuseStep 563159 = 844739) B844739
theorem B333783 : Blo 330750 333783 := bstep (se 1 (by rfl) ⟨250337, by rfl⟩ : syracuseStep 333783 = 500675) B500675
theorem B333803 : Blo 330750 333803 := bstep (se 1 (by rfl) ⟨250352, by rfl⟩ : syracuseStep 333803 = 500705) B500705
theorem B333815 : Blo 330750 333815 := bstep (se 1 (by rfl) ⟨250361, by rfl⟩ : syracuseStep 333815 = 500723) B500723
theorem B497675 : Blo 330750 497675 := bstep (se 1 (by rfl) ⟨373256, by rfl⟩ : syracuseStep 497675 = 746513) B746513
theorem B333835 : Blo 330750 333835 := bstep (se 1 (by rfl) ⟨250376, by rfl⟩ : syracuseStep 333835 = 500753) B500753
theorem B497687 : Blo 330750 497687 := bstep (se 1 (by rfl) ⟨373265, by rfl⟩ : syracuseStep 497687 = 746531) B746531
theorem B333847 : Blo 330750 333847 := bstep (se 1 (by rfl) ⟨250385, by rfl⟩ : syracuseStep 333847 = 500771) B500771
theorem B333867 : Blo 330750 333867 := bstep (se 1 (by rfl) ⟨250400, by rfl⟩ : syracuseStep 333867 = 500801) B500801
theorem B333879 : Blo 330750 333879 := bstep (se 1 (by rfl) ⟨250409, by rfl⟩ : syracuseStep 333879 = 500819) B500819
theorem B333899 : Blo 330750 333899 := bstep (se 1 (by rfl) ⟨250424, by rfl⟩ : syracuseStep 333899 = 500849) B500849
theorem B628823 : Blo 330750 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B563287 : Blo 330750 563287 := bstep (se 1 (by rfl) ⟨422465, by rfl⟩ : syracuseStep 563287 = 844931) B844931
theorem B497753 : Blo 330750 497753 := bstep (se 2 (by rfl) ⟨186657, by rfl⟩ : syracuseStep 497753 = 373315) B373315
theorem B333911 : Blo 330750 333911 := bstep (se 1 (by rfl) ⟨250433, by rfl⟩ : syracuseStep 333911 = 500867) B500867
theorem B333931 : Blo 330750 333931 := bstep (se 1 (by rfl) ⟨250448, by rfl⟩ : syracuseStep 333931 = 500897) B500897
theorem B333943 : Blo 330750 333943 := bstep (se 1 (by rfl) ⟨250457, by rfl⟩ : syracuseStep 333943 = 500915) B500915
theorem B333963 : Blo 330750 333963 := bstep (se 1 (by rfl) ⟨250472, by rfl⟩ : syracuseStep 333963 = 500945) B500945
theorem B333975 : Blo 330750 333975 := bstep (se 1 (by rfl) ⟨250481, by rfl⟩ : syracuseStep 333975 = 500963) B500963
theorem B333995 : Blo 330750 333995 := bstep (se 1 (by rfl) ⟨250496, by rfl⟩ : syracuseStep 333995 = 500993) B500993
theorem B334007 : Blo 330750 334007 := bstep (se 1 (by rfl) ⟨250505, by rfl⟩ : syracuseStep 334007 = 501011) B501011
theorem B497867 : Blo 330750 497867 := bstep (se 1 (by rfl) ⟨373400, by rfl⟩ : syracuseStep 497867 = 746801) B746801
theorem B334027 : Blo 330750 334027 := bstep (se 1 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 334027 = 501041) B501041
theorem B497879 : Blo 330750 497879 := bstep (se 1 (by rfl) ⟨373409, by rfl⟩ : syracuseStep 497879 = 746819) B746819
theorem B334039 : Blo 330750 334039 := bstep (se 1 (by rfl) ⟨250529, by rfl⟩ : syracuseStep 334039 = 501059) B501059
theorem B334059 : Blo 330750 334059 := bstep (se 1 (by rfl) ⟨250544, by rfl⟩ : syracuseStep 334059 = 501089) B501089
theorem B334071 : Blo 330750 334071 := bstep (se 1 (by rfl) ⟨250553, by rfl⟩ : syracuseStep 334071 = 501107) B501107
theorem B334091 : Blo 330750 334091 := bstep (se 1 (by rfl) ⟨250568, by rfl⟩ : syracuseStep 334091 = 501137) B501137
theorem B334103 : Blo 330750 334103 := bstep (se 1 (by rfl) ⟨250577, by rfl⟩ : syracuseStep 334103 = 501155) B501155
theorem B497945 : Blo 330750 497945 := bstep (se 2 (by rfl) ⟨186729, by rfl⟩ : syracuseStep 497945 = 373459) B373459
theorem B334123 : Blo 330750 334123 := bstep (se 1 (by rfl) ⟨250592, by rfl⟩ : syracuseStep 334123 = 501185) B501185
theorem B334135 : Blo 330750 334135 := bstep (se 1 (by rfl) ⟨250601, by rfl⟩ : syracuseStep 334135 = 501203) B501203
theorem B334155 : Blo 330750 334155 := bstep (se 1 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 334155 = 501233) B501233
theorem B334167 : Blo 330750 334167 := bstep (se 1 (by rfl) ⟨250625, by rfl⟩ : syracuseStep 334167 = 501251) B501251
theorem B2529629 : Blo 330750 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B334187 : Blo 330750 334187 := bstep (se 1 (by rfl) ⟨250640, by rfl⟩ : syracuseStep 334187 = 501281) B501281
theorem B334199 : Blo 330750 334199 := bstep (se 1 (by rfl) ⟨250649, by rfl⟩ : syracuseStep 334199 = 501299) B501299
theorem B498059 : Blo 330750 498059 := bstep (se 1 (by rfl) ⟨373544, by rfl⟩ : syracuseStep 498059 = 747089) B747089
theorem B334219 : Blo 330750 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B498071 : Blo 330750 498071 := bstep (se 1 (by rfl) ⟨373553, by rfl⟩ : syracuseStep 498071 = 747107) B747107
theorem B334231 : Blo 330750 334231 := bstep (se 1 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 334231 = 501347) B501347
theorem B334251 : Blo 330750 334251 := bstep (se 1 (by rfl) ⟨250688, by rfl⟩ : syracuseStep 334251 = 501377) B501377
theorem B334263 : Blo 330750 334263 := bstep (se 1 (by rfl) ⟨250697, by rfl⟩ : syracuseStep 334263 = 501395) B501395
theorem B530891 : Blo 330750 530891 := bstep (se 1 (by rfl) ⟨398168, by rfl⟩ : syracuseStep 530891 = 796337) B796337
theorem B1120715 : Blo 330750 1120715 := bstep (se 1 (by rfl) ⟨840536, by rfl⟩ : syracuseStep 1120715 = 1681073) B1681073
theorem B334283 : Blo 330750 334283 := bstep (se 1 (by rfl) ⟨250712, by rfl⟩ : syracuseStep 334283 = 501425) B501425
theorem B334295 : Blo 330750 334295 := bstep (se 1 (by rfl) ⟨250721, by rfl⟩ : syracuseStep 334295 = 501443) B501443
theorem B498137 : Blo 330750 498137 := bstep (se 2 (by rfl) ⟨186801, by rfl⟩ : syracuseStep 498137 = 373603) B373603
theorem B956893 : Blo 330750 956893 := bstep (se 3 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 956893 = 358835) B358835
theorem B334315 : Blo 330750 334315 := bstep (se 1 (by rfl) ⟨250736, by rfl⟩ : syracuseStep 334315 = 501473) B501473
theorem B334327 : Blo 330750 334327 := bstep (se 1 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 334327 = 501491) B501491
theorem B334347 : Blo 330750 334347 := bstep (se 1 (by rfl) ⟨250760, by rfl⟩ : syracuseStep 334347 = 501521) B501521
theorem B334359 : Blo 330750 334359 := bstep (se 1 (by rfl) ⟨250769, by rfl⟩ : syracuseStep 334359 = 501539) B501539
theorem B334379 : Blo 330750 334379 := bstep (se 1 (by rfl) ⟨250784, by rfl⟩ : syracuseStep 334379 = 501569) B501569
theorem B334391 : Blo 330750 334391 := bstep (se 1 (by rfl) ⟨250793, by rfl⟩ : syracuseStep 334391 = 501587) B501587
theorem B498251 : Blo 330750 498251 := bstep (se 1 (by rfl) ⟨373688, by rfl⟩ : syracuseStep 498251 = 747377) B747377
theorem B334411 : Blo 330750 334411 := bstep (se 1 (by rfl) ⟨250808, by rfl⟩ : syracuseStep 334411 = 501617) B501617
theorem B498263 : Blo 330750 498263 := bstep (se 1 (by rfl) ⟨373697, by rfl⟩ : syracuseStep 498263 = 747395) B747395
theorem B334423 : Blo 330750 334423 := bstep (se 1 (by rfl) ⟨250817, by rfl⟩ : syracuseStep 334423 = 501635) B501635
theorem B334443 : Blo 330750 334443 := bstep (se 1 (by rfl) ⟨250832, by rfl⟩ : syracuseStep 334443 = 501665) B501665
theorem B629363 : Blo 330750 629363 := bstep (se 1 (by rfl) ⟨472022, by rfl⟩ : syracuseStep 629363 = 944045) B944045
theorem B334455 : Blo 330750 334455 := bstep (se 1 (by rfl) ⟨250841, by rfl⟩ : syracuseStep 334455 = 501683) B501683
theorem B531083 : Blo 330750 531083 := bstep (se 1 (by rfl) ⟨398312, by rfl⟩ : syracuseStep 531083 = 796625) B796625
theorem B334475 : Blo 330750 334475 := bstep (se 1 (by rfl) ⟨250856, by rfl⟩ : syracuseStep 334475 = 501713) B501713
theorem B334487 : Blo 330750 334487 := bstep (se 1 (by rfl) ⟨250865, by rfl⟩ : syracuseStep 334487 = 501731) B501731
theorem B498329 : Blo 330750 498329 := bstep (se 2 (by rfl) ⟨186873, by rfl⟩ : syracuseStep 498329 = 373747) B373747
theorem B334507 : Blo 330750 334507 := bstep (se 1 (by rfl) ⟨250880, by rfl⟩ : syracuseStep 334507 = 501761) B501761
theorem B334519 : Blo 330750 334519 := bstep (se 1 (by rfl) ⟨250889, by rfl⟩ : syracuseStep 334519 = 501779) B501779
theorem B563915 : Blo 330750 563915 := bstep (se 1 (by rfl) ⟨422936, by rfl⟩ : syracuseStep 563915 = 845873) B845873
theorem B334539 : Blo 330750 334539 := bstep (se 1 (by rfl) ⟨250904, by rfl⟩ : syracuseStep 334539 = 501809) B501809
theorem B4266701 : Blo 330750 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B334551 : Blo 330750 334551 := bstep (se 1 (by rfl) ⟨250913, by rfl⟩ : syracuseStep 334551 = 501827) B501827
theorem B1120985 : Blo 330750 1120985 := bstep (se 2 (by rfl) ⟨420369, by rfl⟩ : syracuseStep 1120985 = 840739) B840739
theorem B334571 : Blo 330750 334571 := bstep (se 1 (by rfl) ⟨250928, by rfl⟩ : syracuseStep 334571 = 501857) B501857
theorem B334583 : Blo 330750 334583 := bstep (se 1 (by rfl) ⟨250937, by rfl⟩ : syracuseStep 334583 = 501875) B501875
theorem B531211 : Blo 330750 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B498443 : Blo 330750 498443 := bstep (se 1 (by rfl) ⟨373832, by rfl⟩ : syracuseStep 498443 = 747665) B747665
theorem B334603 : Blo 330750 334603 := bstep (se 1 (by rfl) ⟨250952, by rfl⟩ : syracuseStep 334603 = 501905) B501905
theorem B498455 : Blo 330750 498455 := bstep (se 1 (by rfl) ⟨373841, by rfl⟩ : syracuseStep 498455 = 747683) B747683
theorem B334615 : Blo 330750 334615 := bstep (se 1 (by rfl) ⟨250961, by rfl⟩ : syracuseStep 334615 = 501923) B501923
theorem B334635 : Blo 330750 334635 := bstep (se 1 (by rfl) ⟨250976, by rfl⟩ : syracuseStep 334635 = 501953) B501953
theorem B1415981 : Blo 330750 1415981 := bstep (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) B530993
theorem B334647 : Blo 330750 334647 := bstep (se 1 (by rfl) ⟨250985, by rfl⟩ : syracuseStep 334647 = 501971) B501971
theorem B1514315 : Blo 330750 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B564043 : Blo 330750 564043 := bstep (se 1 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 564043 = 846065) B846065
theorem B334667 : Blo 330750 334667 := bstep (se 1 (by rfl) ⟨251000, by rfl⟩ : syracuseStep 334667 = 502001) B502001
theorem B334679 : Blo 330750 334679 := bstep (se 1 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 334679 = 502019) B502019
theorem B498521 : Blo 330750 498521 := bstep (se 2 (by rfl) ⟨186945, by rfl⟩ : syracuseStep 498521 = 373891) B373891
theorem B334699 : Blo 330750 334699 := bstep (se 1 (by rfl) ⟨251024, by rfl⟩ : syracuseStep 334699 = 502049) B502049
theorem B334711 : Blo 330750 334711 := bstep (se 1 (by rfl) ⟨251033, by rfl⟩ : syracuseStep 334711 = 502067) B502067
theorem B334731 : Blo 330750 334731 := bstep (se 1 (by rfl) ⟨251048, by rfl⟩ : syracuseStep 334731 = 502097) B502097
theorem B334743 : Blo 330750 334743 := bstep (se 1 (by rfl) ⟨251057, by rfl⟩ : syracuseStep 334743 = 502115) B502115
theorem B760769 : Blo 330750 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B498635 : Blo 330750 498635 := bstep (se 1 (by rfl) ⟨373976, by rfl⟩ : syracuseStep 498635 = 747953) B747953
theorem B498647 : Blo 330750 498647 := bstep (se 1 (by rfl) ⟨373985, by rfl⟩ : syracuseStep 498647 = 747971) B747971
theorem B564185 : Blo 330750 564185 := bstep (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) B423139
theorem B498713 : Blo 330750 498713 := bstep (se 2 (by rfl) ⟨187017, by rfl⟩ : syracuseStep 498713 = 374035) B374035
theorem B629849 : Blo 330750 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B564313 : Blo 330750 564313 := bstep (se 2 (by rfl) ⟨211617, by rfl⟩ : syracuseStep 564313 = 423235) B423235
theorem B498827 : Blo 330750 498827 := bstep (se 1 (by rfl) ⟨374120, by rfl⟩ : syracuseStep 498827 = 748241) B748241
theorem B498839 : Blo 330750 498839 := bstep (se 1 (by rfl) ⟨374129, by rfl⟩ : syracuseStep 498839 = 748259) B748259
theorem B498905 : Blo 330750 498905 := bstep (se 2 (by rfl) ⟨187089, by rfl⟩ : syracuseStep 498905 = 374179) B374179
theorem B499019 : Blo 330750 499019 := bstep (se 1 (by rfl) ⟨374264, by rfl⟩ : syracuseStep 499019 = 748529) B748529
theorem B499031 : Blo 330750 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B531851 : Blo 330750 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B1121687 : Blo 330750 1121687 := bstep (se 1 (by rfl) ⟨841265, by rfl⟩ : syracuseStep 1121687 = 1682531) B1682531
theorem B499097 : Blo 330750 499097 := bstep (se 2 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 499097 = 374323) B374323
theorem B531929 : Blo 330750 531929 := bstep (se 2 (by rfl) ⟨199473, by rfl⟩ : syracuseStep 531929 = 398947) B398947
theorem B499211 : Blo 330750 499211 := bstep (se 1 (by rfl) ⟨374408, by rfl⟩ : syracuseStep 499211 = 748817) B748817
theorem B1285649 : Blo 330750 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B499223 : Blo 330750 499223 := bstep (se 1 (by rfl) ⟨374417, by rfl⟩ : syracuseStep 499223 = 748835) B748835
theorem B2399789 : Blo 330750 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B499289 : Blo 330750 499289 := bstep (se 2 (by rfl) ⟨187233, by rfl⟩ : syracuseStep 499289 = 374467) B374467
theorem B564887 : Blo 330750 564887 := bstep (se 1 (by rfl) ⟨423665, by rfl⟩ : syracuseStep 564887 = 847331) B847331
theorem B499403 : Blo 330750 499403 := bstep (se 1 (by rfl) ⟨374552, by rfl⟩ : syracuseStep 499403 = 749105) B749105
theorem B499415 : Blo 330750 499415 := bstep (se 1 (by rfl) ⟨374561, by rfl⟩ : syracuseStep 499415 = 749123) B749123
theorem B499481 : Blo 330750 499481 := bstep (se 2 (by rfl) ⟨187305, by rfl⟩ : syracuseStep 499481 = 374611) B374611
theorem B1154891 : Blo 330750 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B532313 : Blo 330750 532313 := bstep (se 2 (by rfl) ⟨199617, by rfl⟩ : syracuseStep 532313 = 399235) B399235
theorem B499595 : Blo 330750 499595 := bstep (se 1 (by rfl) ⟨374696, by rfl⟩ : syracuseStep 499595 = 749393) B749393
theorem B499607 : Blo 330750 499607 := bstep (se 1 (by rfl) ⟨374705, by rfl⟩ : syracuseStep 499607 = 749411) B749411
theorem B1122227 : Blo 330750 1122227 := bstep (se 1 (by rfl) ⟨841670, by rfl⟩ : syracuseStep 1122227 = 1683341) B1683341
theorem B532441 : Blo 330750 532441 := bstep (se 2 (by rfl) ⟨199665, by rfl⟩ : syracuseStep 532441 = 399331) B399331
theorem B499673 : Blo 330750 499673 := bstep (se 2 (by rfl) ⟨187377, by rfl⟩ : syracuseStep 499673 = 374755) B374755
theorem B499787 : Blo 330750 499787 := bstep (se 1 (by rfl) ⟨374840, by rfl⟩ : syracuseStep 499787 = 749681) B749681
theorem B499799 : Blo 330750 499799 := bstep (se 1 (by rfl) ⟨374849, by rfl⟩ : syracuseStep 499799 = 749699) B749699
theorem B1679453 : Blo 330750 1679453 := bstep (se 3 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 1679453 = 629795) B629795
theorem B499865 : Blo 330750 499865 := bstep (se 2 (by rfl) ⟨187449, by rfl⟩ : syracuseStep 499865 = 374899) B374899
theorem B6037685 : Blo 330750 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B1122497 : Blo 330750 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B499979 : Blo 330750 499979 := bstep (se 1 (by rfl) ⟨374984, by rfl⟩ : syracuseStep 499979 = 749969) B749969
theorem B499991 : Blo 330750 499991 := bstep (se 1 (by rfl) ⟨374993, by rfl⟩ : syracuseStep 499991 = 749987) B749987
theorem B2859299 : Blo 330750 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B500057 : Blo 330750 500057 := bstep (se 2 (by rfl) ⟨187521, by rfl⟩ : syracuseStep 500057 = 375043) B375043
theorem B500171 : Blo 330750 500171 := bstep (se 1 (by rfl) ⟨375128, by rfl⟩ : syracuseStep 500171 = 750257) B750257
theorem B500183 : Blo 330750 500183 := bstep (se 1 (by rfl) ⟨375137, by rfl⟩ : syracuseStep 500183 = 750275) B750275
theorem B3809753 : Blo 330750 3809753 := bstep (se 2 (by rfl) ⟨1428657, by rfl⟩ : syracuseStep 3809753 = 2857315) B2857315
theorem B631307 : Blo 330750 631307 := bstep (se 1 (by rfl) ⟨473480, by rfl⟩ : syracuseStep 631307 = 946961) B946961
theorem B500249 : Blo 330750 500249 := bstep (se 2 (by rfl) ⟨187593, by rfl⟩ : syracuseStep 500249 = 375187) B375187
theorem B1352285 : Blo 330750 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B500363 : Blo 330750 500363 := bstep (se 1 (by rfl) ⟨375272, by rfl⟩ : syracuseStep 500363 = 750545) B750545
theorem B598679 : Blo 330750 598679 := bstep (se 1 (by rfl) ⟨449009, by rfl⟩ : syracuseStep 598679 = 898019) B898019
theorem B500375 : Blo 330750 500375 := bstep (se 1 (by rfl) ⟨375281, by rfl⟩ : syracuseStep 500375 = 750563) B750563
theorem B631489 : Blo 330750 631489 := bstep (se 2 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 631489 = 473617) B473617
theorem B500441 : Blo 330750 500441 := bstep (se 2 (by rfl) ⟨187665, by rfl⟩ : syracuseStep 500441 = 375331) B375331
theorem B1123037 : Blo 330750 1123037 := bstep (se 3 (by rfl) ⟨210569, by rfl⟩ : syracuseStep 1123037 = 421139) B421139
theorem B500555 : Blo 330750 500555 := bstep (se 1 (by rfl) ⟨375416, by rfl⟩ : syracuseStep 500555 = 750833) B750833
theorem B500567 : Blo 330750 500567 := bstep (se 1 (by rfl) ⟨375425, by rfl⟩ : syracuseStep 500567 = 750851) B750851
theorem B500633 : Blo 330750 500633 := bstep (se 2 (by rfl) ⟨187737, by rfl⟩ : syracuseStep 500633 = 375475) B375475
theorem B500747 : Blo 330750 500747 := bstep (se 1 (by rfl) ⟨375560, by rfl⟩ : syracuseStep 500747 = 751121) B751121
theorem B500759 : Blo 330750 500759 := bstep (se 1 (by rfl) ⟨375569, by rfl⟩ : syracuseStep 500759 = 751139) B751139
theorem B762905 : Blo 330750 762905 := bstep (se 2 (by rfl) ⟨286089, by rfl⟩ : syracuseStep 762905 = 572179) B572179
theorem B500825 : Blo 330750 500825 := bstep (se 2 (by rfl) ⟨187809, by rfl⟩ : syracuseStep 500825 = 375619) B375619
theorem B631937 : Blo 330750 631937 := bstep (se 2 (by rfl) ⟨236976, by rfl⟩ : syracuseStep 631937 = 473953) B473953
theorem B500939 : Blo 330750 500939 := bstep (se 1 (by rfl) ⟨375704, by rfl⟩ : syracuseStep 500939 = 751409) B751409
theorem B500951 : Blo 330750 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B501017 : Blo 330750 501017 := bstep (se 2 (by rfl) ⟨187881, by rfl⟩ : syracuseStep 501017 = 375763) B375763
theorem B1516865 : Blo 330750 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B501131 : Blo 330750 501131 := bstep (se 1 (by rfl) ⟨375848, by rfl⟩ : syracuseStep 501131 = 751697) B751697
theorem B501143 : Blo 330750 501143 := bstep (se 1 (by rfl) ⟨375857, by rfl⟩ : syracuseStep 501143 = 751715) B751715
theorem B632279 : Blo 330750 632279 := bstep (se 1 (by rfl) ⟨474209, by rfl⟩ : syracuseStep 632279 = 948419) B948419
theorem B501209 : Blo 330750 501209 := bstep (se 2 (by rfl) ⟨187953, by rfl⟩ : syracuseStep 501209 = 375907) B375907
theorem B501323 : Blo 330750 501323 := bstep (se 1 (by rfl) ⟨375992, by rfl⟩ : syracuseStep 501323 = 751985) B751985
theorem B501335 : Blo 330750 501335 := bstep (se 1 (by rfl) ⟨376001, by rfl⟩ : syracuseStep 501335 = 752003) B752003
theorem B501401 : Blo 330750 501401 := bstep (se 2 (by rfl) ⟨188025, by rfl⟩ : syracuseStep 501401 = 376051) B376051
theorem B501515 : Blo 330750 501515 := bstep (se 1 (by rfl) ⟨376136, by rfl⟩ : syracuseStep 501515 = 752273) B752273
theorem B501527 : Blo 330750 501527 := bstep (se 1 (by rfl) ⟨376145, by rfl⟩ : syracuseStep 501527 = 752291) B752291
theorem B1124171 : Blo 330750 1124171 := bstep (se 1 (by rfl) ⟨843128, by rfl⟩ : syracuseStep 1124171 = 1686257) B1686257
theorem B501593 : Blo 330750 501593 := bstep (se 2 (by rfl) ⟨188097, by rfl⟩ : syracuseStep 501593 = 376195) B376195
theorem B501707 : Blo 330750 501707 := bstep (se 1 (by rfl) ⟨376280, by rfl⟩ : syracuseStep 501707 = 752561) B752561
theorem B501719 : Blo 330750 501719 := bstep (se 1 (by rfl) ⟨376289, by rfl⟩ : syracuseStep 501719 = 752579) B752579
theorem B501785 : Blo 330750 501785 := bstep (se 2 (by rfl) ⟨188169, by rfl⟩ : syracuseStep 501785 = 376339) B376339
theorem B1124441 : Blo 330750 1124441 := bstep (se 2 (by rfl) ⟨421665, by rfl⟩ : syracuseStep 1124441 = 843331) B843331
theorem B632947 : Blo 330750 632947 := bstep (se 1 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 632947 = 949421) B949421
theorem B501899 : Blo 330750 501899 := bstep (se 1 (by rfl) ⟨376424, by rfl⟩ : syracuseStep 501899 = 752849) B752849
theorem B1681559 : Blo 330750 1681559 := bstep (se 1 (by rfl) ⟨1261169, by rfl⟩ : syracuseStep 1681559 = 2522339) B2522339
theorem B501911 : Blo 330750 501911 := bstep (se 1 (by rfl) ⟨376433, by rfl⟩ : syracuseStep 501911 = 752867) B752867
theorem B501977 : Blo 330750 501977 := bstep (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) B376483
theorem B502091 : Blo 330750 502091 := bstep (se 1 (by rfl) ⟨376568, by rfl⟩ : syracuseStep 502091 = 753137) B753137
theorem B502103 : Blo 330750 502103 := bstep (se 1 (by rfl) ⟨376577, by rfl⟩ : syracuseStep 502103 = 753155) B753155
theorem B600409 : Blo 330750 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B1845605 : Blo 330750 1845605 := bstep (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) B346051
theorem B338347 : Blo 330750 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B1354163 : Blo 330750 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B895511 : Blo 330750 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B633395 : Blo 330750 633395 := bstep (se 1 (by rfl) ⟨475046, by rfl⟩ : syracuseStep 633395 = 950093) B950093
theorem B633433 : Blo 330750 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B600691 : Blo 330750 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B4532867 : Blo 330750 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B338635 : Blo 330750 338635 := bstep (se 1 (by rfl) ⟨253976, by rfl⟩ : syracuseStep 338635 = 507953) B507953
theorem B961303 : Blo 330750 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B1125143 : Blo 330750 1125143 := bstep (se 1 (by rfl) ⟨843857, by rfl⟩ : syracuseStep 1125143 = 1687715) B1687715
theorem B1420183 : Blo 330750 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1420253 : Blo 330750 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B633881 : Blo 330750 633881 := bstep (se 2 (by rfl) ⟨237705, by rfl⟩ : syracuseStep 633881 = 475411) B475411
theorem B4041859 : Blo 330750 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B2403479 : Blo 330750 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B1125683 : Blo 330750 1125683 := bstep (se 1 (by rfl) ⟨844262, by rfl⟩ : syracuseStep 1125683 = 1688525) B1688525
theorem B339287 : Blo 330750 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B2305459 : Blo 330750 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B372235 : Blo 330750 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B1125953 : Blo 330750 1125953 := bstep (se 2 (by rfl) ⟨422232, by rfl⟩ : syracuseStep 1125953 = 844465) B844465
theorem B372343 : Blo 330750 372343 := bstep (se 1 (by rfl) ⟨279257, by rfl⟩ : syracuseStep 372343 = 558515) B558515
theorem B601793 : Blo 330750 601793 := bstep (se 2 (by rfl) ⟨225672, by rfl⟩ : syracuseStep 601793 = 451345) B451345
theorem B1421003 : Blo 330750 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B634625 : Blo 330750 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B372523 : Blo 330750 372523 := bstep (se 1 (by rfl) ⟨279392, by rfl⟩ : syracuseStep 372523 = 558785) B558785
theorem B372631 : Blo 330750 372631 := bstep (se 1 (by rfl) ⟨279473, by rfl⟩ : syracuseStep 372631 = 558947) B558947
theorem B1257389 : Blo 330750 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B634891 : Blo 330750 634891 := bstep (se 1 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 634891 = 952337) B952337
theorem B372811 : Blo 330750 372811 := bstep (se 1 (by rfl) ⟨279608, by rfl⟩ : syracuseStep 372811 = 559217) B559217
theorem B1126493 : Blo 330750 1126493 := bstep (se 3 (by rfl) ⟨211217, by rfl⟩ : syracuseStep 1126493 = 422435) B422435
theorem B372919 : Blo 330750 372919 := bstep (se 1 (by rfl) ⟨279689, by rfl⟩ : syracuseStep 372919 = 559379) B559379
theorem B373099 : Blo 330750 373099 := bstep (se 1 (by rfl) ⟨279824, by rfl⟩ : syracuseStep 373099 = 559649) B559649
theorem B1716659 : Blo 330750 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B635339 : Blo 330750 635339 := bstep (se 1 (by rfl) ⟨476504, by rfl⟩ : syracuseStep 635339 = 953009) B953009
theorem B373207 : Blo 330750 373207 := bstep (se 1 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 373207 = 559811) B559811
theorem B373387 : Blo 330750 373387 := bstep (se 1 (by rfl) ⟨280040, by rfl⟩ : syracuseStep 373387 = 560081) B560081
theorem B1258163 : Blo 330750 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B373495 : Blo 330750 373495 := bstep (se 1 (by rfl) ⟨280121, by rfl⟩ : syracuseStep 373495 = 560243) B560243
theorem B2405213 : Blo 330750 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B1651549 : Blo 330750 1651549 := bstep (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) B619331
theorem B373675 : Blo 330750 373675 := bstep (se 1 (by rfl) ⟨280256, by rfl⟩ : syracuseStep 373675 = 560513) B560513
theorem B1192963 : Blo 330750 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B373783 : Blo 330750 373783 := bstep (se 1 (by rfl) ⟨280337, by rfl⟩ : syracuseStep 373783 = 560675) B560675
theorem B472267 : Blo 330750 472267 := bstep (se 1 (by rfl) ⟨354200, by rfl⟩ : syracuseStep 472267 = 708401) B708401
theorem B373963 : Blo 330750 373963 := bstep (se 1 (by rfl) ⟨280472, by rfl⟩ : syracuseStep 373963 = 560945) B560945
theorem B1127627 : Blo 330750 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B374071 : Blo 330750 374071 := bstep (se 1 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 374071 = 561107) B561107
theorem B1127897 : Blo 330750 1127897 := bstep (se 2 (by rfl) ⟨422961, by rfl⟩ : syracuseStep 1127897 = 845923) B845923
theorem B2143705 : Blo 330750 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B374251 : Blo 330750 374251 := bstep (se 1 (by rfl) ⟨280688, by rfl⟩ : syracuseStep 374251 = 561377) B561377
theorem B374359 : Blo 330750 374359 := bstep (se 1 (by rfl) ⟨280769, by rfl⟩ : syracuseStep 374359 = 561539) B561539
theorem B1685123 : Blo 330750 1685123 := bstep (se 1 (by rfl) ⟨1263842, by rfl⟩ : syracuseStep 1685123 = 2527685) B2527685
theorem B374539 : Blo 330750 374539 := bstep (se 1 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 374539 = 561809) B561809
theorem B374647 : Blo 330750 374647 := bstep (se 1 (by rfl) ⟨280985, by rfl⟩ : syracuseStep 374647 = 561971) B561971
theorem B24262577 : Blo 330750 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B374827 : Blo 330750 374827 := bstep (se 1 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 374827 = 562241) B562241
theorem B4241483 : Blo 330750 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B899165 : Blo 330750 899165 := bstep (se 3 (by rfl) ⟨168593, by rfl⟩ : syracuseStep 899165 = 337187) B337187
theorem B1259651 : Blo 330750 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B637067 : Blo 330750 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B374935 : Blo 330750 374935 := bstep (se 1 (by rfl) ⟨281201, by rfl⟩ : syracuseStep 374935 = 562403) B562403
theorem B1128599 : Blo 330750 1128599 := bstep (se 1 (by rfl) ⟨846449, by rfl⟩ : syracuseStep 1128599 = 1692899) B1692899
theorem B1063115 : Blo 330750 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B571673 : Blo 330750 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B375115 : Blo 330750 375115 := bstep (se 1 (by rfl) ⟨281336, by rfl⟩ : syracuseStep 375115 = 562673) B562673
theorem B538967 : Blo 330750 538967 := bstep (se 1 (by rfl) ⟨404225, by rfl⟩ : syracuseStep 538967 = 808451) B808451
theorem B12073333 : Blo 330750 12073333 := bstep (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) B1131875
theorem B375223 : Blo 330750 375223 := bstep (se 1 (by rfl) ⟨281417, by rfl⟩ : syracuseStep 375223 = 562835) B562835
theorem B1260107 : Blo 330750 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B4340299 : Blo 330750 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B375403 : Blo 330750 375403 := bstep (se 1 (by rfl) ⟨281552, by rfl⟩ : syracuseStep 375403 = 563105) B563105
theorem B1522307 : Blo 330750 1522307 := bstep (se 1 (by rfl) ⟨1141730, by rfl⟩ : syracuseStep 1522307 = 2283461) B2283461
theorem B1129139 : Blo 330750 1129139 := bstep (se 1 (by rfl) ⟨846854, by rfl⟩ : syracuseStep 1129139 = 1693709) B1693709
theorem B375511 : Blo 330750 375511 := bstep (se 1 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 375511 = 563267) B563267
theorem B1260305 : Blo 330750 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B1391411 : Blo 330750 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B19249973 : Blo 330750 19249973 := bstep (se 5 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 19249973 = 1804685) B1804685
theorem B375691 : Blo 330750 375691 := bstep (se 1 (by rfl) ⟨281768, by rfl⟩ : syracuseStep 375691 = 563537) B563537
theorem B1129409 : Blo 330750 1129409 := bstep (se 2 (by rfl) ⟨423528, by rfl⟩ : syracuseStep 1129409 = 847057) B847057
theorem B375799 : Blo 330750 375799 := bstep (se 1 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 375799 = 563699) B563699
theorem B4045859 : Blo 330750 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B375979 : Blo 330750 375979 := bstep (se 1 (by rfl) ⟨281984, by rfl⟩ : syracuseStep 375979 = 563969) B563969
theorem B1424557 : Blo 330750 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B1064215 : Blo 330750 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B376087 : Blo 330750 376087 := bstep (se 1 (by rfl) ⟨282065, by rfl⟩ : syracuseStep 376087 = 564131) B564131
theorem B1424729 : Blo 330750 1424729 := bstep (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) B1068547
theorem B802199 : Blo 330750 802199 := bstep (se 1 (by rfl) ⟨601649, by rfl⟩ : syracuseStep 802199 = 1203299) B1203299
theorem B671179 : Blo 330750 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B376267 : Blo 330750 376267 := bstep (se 1 (by rfl) ⟨282200, by rfl⟩ : syracuseStep 376267 = 564401) B564401
theorem B1261079 : Blo 330750 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B376375 : Blo 330750 376375 := bstep (se 1 (by rfl) ⟨282281, by rfl⟩ : syracuseStep 376375 = 564563) B564563
theorem B1261277 : Blo 330750 1261277 := bstep (se 3 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 1261277 = 472979) B472979
theorem B376555 : Blo 330750 376555 := bstep (se 1 (by rfl) ⟨282416, by rfl⟩ : syracuseStep 376555 = 564833) B564833
theorem B2473907 : Blo 330750 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1065035 : Blo 330750 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B2310617 : Blo 330750 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B836185 : Blo 330750 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B1426369 : Blo 330750 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B672833 : Blo 330750 672833 := bstep (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) B504625
theorem B377995 : Blo 330750 377995 := bstep (se 1 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 377995 = 566993) B566993
theorem B1688849 : Blo 330750 1688849 := bstep (se 2 (by rfl) ⟨633318, by rfl⟩ : syracuseStep 1688849 = 1266637) B1266637
theorem B378155 : Blo 330750 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B1689011 : Blo 330750 1689011 := bstep (se 1 (by rfl) ⟨1266758, by rfl⟩ : syracuseStep 1689011 = 2533517) B2533517
theorem B902593 : Blo 330750 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B2606627 : Blo 330750 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1263235 : Blo 330750 1263235 := bstep (se 1 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 1263235 = 1894853) B1894853
theorem B4966069 : Blo 330750 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B837337 : Blo 330750 837337 := bstep (se 2 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 837337 = 628003) B628003
theorem B2279299 : Blo 330750 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B2836403 : Blo 330750 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1263539 : Blo 330750 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B4770053 : Blo 330750 4770053 := bstep (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) B894385
theorem B2836781 : Blo 330750 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B2279897 : Blo 330750 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B903641 : Blo 330750 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B1264193 : Blo 330750 1264193 := bstep (se 2 (by rfl) ⟨474072, by rfl⟩ : syracuseStep 1264193 = 948145) B948145
theorem B1428043 : Blo 330750 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1886813 : Blo 330750 1886813 := bstep (se 3 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 1886813 = 707555) B707555
theorem B838451 : Blo 330750 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B707393 : Blo 330750 707393 := bstep (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) B530545
theorem B1428317 : Blo 330750 1428317 := bstep (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) B535619
theorem B3197873 : Blo 330750 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B2411441 : Blo 330750 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B9554867 : Blo 330750 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B838745 : Blo 330750 838745 := bstep (se 2 (by rfl) ⟨314529, by rfl⟩ : syracuseStep 838745 = 629059) B629059
theorem B1887563 : Blo 330750 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B1690955 : Blo 330750 1690955 := bstep (se 1 (by rfl) ⟨1268216, by rfl⟩ : syracuseStep 1690955 = 2536433) B2536433
theorem B24202709 : Blo 330750 24202709 := bstep (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) B567251
theorem B380503 : Blo 330750 380503 := bstep (se 1 (by rfl) ⟨285377, by rfl⟩ : syracuseStep 380503 = 570755) B570755
theorem B1199767 : Blo 330750 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B1199809 : Blo 330750 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B1265453 : Blo 330750 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B1265483 : Blo 330750 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B970841 : Blo 330750 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B2019763 : Blo 330750 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B709067 : Blo 330750 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B1266137 : Blo 330750 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B4280849 : Blo 330750 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B840395 : Blo 330750 840395 := bstep (se 1 (by rfl) ⟨630296, by rfl⟩ : syracuseStep 840395 = 1260593) B1260593
theorem B7688945 : Blo 330750 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B1266455 : Blo 330750 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B1889203 : Blo 330750 1889203 := bstep (se 1 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 1889203 = 2833805) B2833805
theorem B4248611 : Blo 330750 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B1692737 : Blo 330750 1692737 := bstep (se 2 (by rfl) ⟨634776, by rfl⟩ : syracuseStep 1692737 = 1269553) B1269553
theorem B5690573 : Blo 330750 5690573 := bstep (se 3 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 5690573 = 2133965) B2133965
theorem B2512133 : Blo 330750 2512133 := bstep (se 4 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 2512133 = 471025) B471025
theorem B710041 : Blo 330750 710041 := bstep (se 2 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 710041 = 532531) B532531
theorem B1267123 : Blo 330750 1267123 := bstep (se 1 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 1267123 = 1900685) B1900685
theorem B677335 : Blo 330750 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B841367 : Blo 330750 841367 := bstep (se 1 (by rfl) ⟨631025, by rfl⟩ : syracuseStep 841367 = 1262051) B1262051
theorem B710297 : Blo 330750 710297 := bstep (se 2 (by rfl) ⟨266361, by rfl⟩ : syracuseStep 710297 = 532723) B532723
theorem B2119385 : Blo 330750 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B710707 : Blo 330750 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B842035 : Blo 330750 842035 := bstep (se 1 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 842035 = 1263053) B1263053
theorem B1890661 : Blo 330750 1890661 := bstep (se 4 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 1890661 = 354499) B354499
theorem B842177 : Blo 330750 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B1268369 : Blo 330750 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B711425 : Blo 330750 711425 := bstep (se 2 (by rfl) ⟨266784, by rfl⟩ : syracuseStep 711425 = 533569) B533569
theorem B744281 : Blo 330750 744281 := bstep (se 2 (by rfl) ⟨279105, by rfl⟩ : syracuseStep 744281 = 558211) B558211
theorem B1858405 : Blo 330750 1858405 := bstep (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) B348451
theorem B744371 : Blo 330750 744371 := bstep (se 1 (by rfl) ⟨558278, by rfl⟩ : syracuseStep 744371 = 1116557) B1116557
theorem B744407 : Blo 330750 744407 := bstep (se 1 (by rfl) ⟨558305, by rfl⟩ : syracuseStep 744407 = 1116611) B1116611
theorem B711767 : Blo 330750 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B744587 : Blo 330750 744587 := bstep (se 1 (by rfl) ⟨558440, by rfl⟩ : syracuseStep 744587 = 1116881) B1116881
theorem B5856407 : Blo 330750 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B744641 : Blo 330750 744641 := bstep (se 2 (by rfl) ⟨279240, by rfl⟩ : syracuseStep 744641 = 558481) B558481
theorem B711937 : Blo 330750 711937 := bstep (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) B533953
theorem B2121025 : Blo 330750 2121025 := bstep (se 2 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 2121025 = 1590769) B1590769
theorem B1269067 : Blo 330750 1269067 := bstep (se 1 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 1269067 = 1903601) B1903601
theorem B744857 : Blo 330750 744857 := bstep (se 2 (by rfl) ⟨279321, by rfl⟩ : syracuseStep 744857 = 558643) B558643
theorem B744947 : Blo 330750 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B744983 : Blo 330750 744983 := bstep (se 1 (by rfl) ⟨558737, by rfl⟩ : syracuseStep 744983 = 1117475) B1117475
theorem B1269341 : Blo 330750 1269341 := bstep (se 3 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 1269341 = 476003) B476003
theorem B2514563 : Blo 330750 2514563 := bstep (se 1 (by rfl) ⟨1885922, by rfl⟩ : syracuseStep 2514563 = 3771845) B3771845
theorem B843443 : Blo 330750 843443 := bstep (se 1 (by rfl) ⟨632582, by rfl⟩ : syracuseStep 843443 = 1265165) B1265165
theorem B745163 : Blo 330750 745163 := bstep (se 1 (by rfl) ⟨558872, by rfl⟩ : syracuseStep 745163 = 1117745) B1117745
theorem B745217 : Blo 330750 745217 := bstep (se 2 (by rfl) ⟨279456, by rfl⟩ : syracuseStep 745217 = 558913) B558913
theorem B1597229 : Blo 330750 1597229 := bstep (se 3 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 1597229 = 598961) B598961
theorem B3628901 : Blo 330750 3628901 := bstep (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) B680419
theorem B745433 : Blo 330750 745433 := bstep (se 2 (by rfl) ⟨279537, by rfl⟩ : syracuseStep 745433 = 559075) B559075
theorem B942131 : Blo 330750 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B745523 : Blo 330750 745523 := bstep (se 1 (by rfl) ⟨559142, by rfl⟩ : syracuseStep 745523 = 1118285) B1118285
theorem B745559 : Blo 330750 745559 := bstep (se 1 (by rfl) ⟨559169, by rfl⟩ : syracuseStep 745559 = 1118339) B1118339
theorem B843979 : Blo 330750 843979 := bstep (se 1 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 843979 = 1265969) B1265969
theorem B745739 : Blo 330750 745739 := bstep (se 1 (by rfl) ⟨559304, by rfl⟩ : syracuseStep 745739 = 1118609) B1118609
theorem B1270039 : Blo 330750 1270039 := bstep (se 1 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 1270039 = 1905059) B1905059
theorem B745793 : Blo 330750 745793 := bstep (se 2 (by rfl) ⟨279672, by rfl⟩ : syracuseStep 745793 = 559345) B559345
theorem B844121 : Blo 330750 844121 := bstep (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) B633091
theorem B713099 : Blo 330750 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B942529 : Blo 330750 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B746009 : Blo 330750 746009 := bstep (se 2 (by rfl) ⟨279753, by rfl⟩ : syracuseStep 746009 = 559507) B559507
theorem B746099 : Blo 330750 746099 := bstep (se 1 (by rfl) ⟨559574, by rfl⟩ : syracuseStep 746099 = 1119149) B1119149
theorem B746135 : Blo 330750 746135 := bstep (se 1 (by rfl) ⟨559601, by rfl⟩ : syracuseStep 746135 = 1119203) B1119203
theorem B746315 : Blo 330750 746315 := bstep (se 1 (by rfl) ⟨559736, by rfl⟩ : syracuseStep 746315 = 1119473) B1119473
theorem B746369 : Blo 330750 746369 := bstep (se 2 (by rfl) ⟨279888, by rfl⟩ : syracuseStep 746369 = 559777) B559777
theorem B418699 : Blo 330750 418699 := bstep (se 1 (by rfl) ⟨314024, by rfl⟩ : syracuseStep 418699 = 628049) B628049
theorem B1270829 : Blo 330750 1270829 := bstep (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) B476561
theorem B746585 : Blo 330750 746585 := bstep (se 2 (by rfl) ⟨279969, by rfl⟩ : syracuseStep 746585 = 559939) B559939
theorem B713843 : Blo 330750 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B844951 : Blo 330750 844951 := bstep (se 1 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 844951 = 1267427) B1267427
theorem B746675 : Blo 330750 746675 := bstep (se 1 (by rfl) ⟨560006, by rfl⟩ : syracuseStep 746675 = 1120013) B1120013
theorem B746711 : Blo 330750 746711 := bstep (se 1 (by rfl) ⟨560033, by rfl⟩ : syracuseStep 746711 = 1120067) B1120067
theorem B746891 : Blo 330750 746891 := bstep (se 1 (by rfl) ⟨560168, by rfl⟩ : syracuseStep 746891 = 1120337) B1120337
theorem B746945 : Blo 330750 746945 := bstep (se 2 (by rfl) ⟨280104, by rfl⟩ : syracuseStep 746945 = 560209) B560209
theorem B2287121 : Blo 330750 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B353867 : Blo 330750 353867 := bstep (se 1 (by rfl) ⟨265400, by rfl⟩ : syracuseStep 353867 = 530801) B530801
theorem B845387 : Blo 330750 845387 := bstep (se 1 (by rfl) ⟨634040, by rfl⟩ : syracuseStep 845387 = 1268081) B1268081
theorem B681587 : Blo 330750 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B747161 : Blo 330750 747161 := bstep (se 2 (by rfl) ⟨280185, by rfl⟩ : syracuseStep 747161 = 560371) B560371
theorem B747251 : Blo 330750 747251 := bstep (se 1 (by rfl) ⟨560438, by rfl⟩ : syracuseStep 747251 = 1120877) B1120877
theorem B747287 : Blo 330750 747287 := bstep (se 1 (by rfl) ⟨560465, by rfl⟩ : syracuseStep 747287 = 1120931) B1120931
theorem B419671 : Blo 330750 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B845761 : Blo 330750 845761 := bstep (se 2 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 845761 = 634321) B634321
theorem B747467 : Blo 330750 747467 := bstep (se 1 (by rfl) ⟨560600, by rfl⟩ : syracuseStep 747467 = 1121201) B1121201
theorem B714739 : Blo 330750 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B747521 : Blo 330750 747521 := bstep (se 2 (by rfl) ⟨280320, by rfl⟩ : syracuseStep 747521 = 560641) B560641
theorem B747737 : Blo 330750 747737 := bstep (se 2 (by rfl) ⟨280401, by rfl⟩ : syracuseStep 747737 = 560803) B560803
theorem B747827 : Blo 330750 747827 := bstep (se 1 (by rfl) ⟨560870, by rfl⟩ : syracuseStep 747827 = 1121741) B1121741
theorem B747863 : Blo 330750 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B6056369 : Blo 330750 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B748043 : Blo 330750 748043 := bstep (se 1 (by rfl) ⟨561032, by rfl⟩ : syracuseStep 748043 = 1122065) B1122065
theorem B846359 : Blo 330750 846359 := bstep (se 1 (by rfl) ⟨634769, by rfl⟩ : syracuseStep 846359 = 1269539) B1269539
theorem B354871 : Blo 330750 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B748097 : Blo 330750 748097 := bstep (se 2 (by rfl) ⟨280536, by rfl⟩ : syracuseStep 748097 = 561073) B561073
theorem B420491 : Blo 330750 420491 := bstep (se 1 (by rfl) ⟨315368, by rfl⟩ : syracuseStep 420491 = 630737) B630737
theorem B1010369 : Blo 330750 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B748313 : Blo 330750 748313 := bstep (se 2 (by rfl) ⟨280617, by rfl⟩ : syracuseStep 748313 = 561235) B561235
theorem B748403 : Blo 330750 748403 := bstep (se 1 (by rfl) ⟨561302, by rfl⟩ : syracuseStep 748403 = 1122605) B1122605
theorem B945047 : Blo 330750 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B748439 : Blo 330750 748439 := bstep (se 1 (by rfl) ⟨561329, by rfl⟩ : syracuseStep 748439 = 1122659) B1122659
theorem B2517965 : Blo 330750 2517965 := bstep (se 3 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 2517965 = 944237) B944237
theorem B748619 : Blo 330750 748619 := bstep (se 1 (by rfl) ⟨561464, by rfl⟩ : syracuseStep 748619 = 1122929) B1122929
theorem B748673 : Blo 330750 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B355627 : Blo 330750 355627 := bstep (se 1 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 355627 = 533441) B533441
theorem B847169 : Blo 330750 847169 := bstep (se 2 (by rfl) ⟨317688, by rfl⟩ : syracuseStep 847169 = 635377) B635377
theorem B421195 : Blo 330750 421195 := bstep (se 1 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 421195 = 631793) B631793
theorem B748889 : Blo 330750 748889 := bstep (se 2 (by rfl) ⟨280833, by rfl⟩ : syracuseStep 748889 = 561667) B561667
theorem B2518451 : Blo 330750 2518451 := bstep (se 1 (by rfl) ⟨1888838, by rfl⟩ : syracuseStep 2518451 = 3777677) B3777677
theorem B748979 : Blo 330750 748979 := bstep (se 1 (by rfl) ⟨561734, by rfl⟩ : syracuseStep 748979 = 1123469) B1123469
theorem B749015 : Blo 330750 749015 := bstep (se 1 (by rfl) ⟨561761, by rfl⟩ : syracuseStep 749015 = 1123523) B1123523
theorem B19131875 : Blo 330750 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B421463 : Blo 330750 421463 := bstep (se 1 (by rfl) ⟨316097, by rfl⟩ : syracuseStep 421463 = 632195) B632195
theorem B749195 : Blo 330750 749195 := bstep (se 1 (by rfl) ⟨561896, by rfl⟩ : syracuseStep 749195 = 1123793) B1123793
theorem B2420375 : Blo 330750 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B3796631 : Blo 330750 3796631 := bstep (se 1 (by rfl) ⟨2847473, by rfl⟩ : syracuseStep 3796631 = 5694947) B5694947
theorem B749249 : Blo 330750 749249 := bstep (se 2 (by rfl) ⟨280968, by rfl⟩ : syracuseStep 749249 = 561937) B561937
theorem B749465 : Blo 330750 749465 := bstep (se 2 (by rfl) ⟨281049, by rfl⟩ : syracuseStep 749465 = 562099) B562099
theorem B749555 : Blo 330750 749555 := bstep (se 1 (by rfl) ⟨562166, by rfl⟩ : syracuseStep 749555 = 1124333) B1124333
theorem B749591 : Blo 330750 749591 := bstep (se 1 (by rfl) ⟨562193, by rfl⟩ : syracuseStep 749591 = 1124387) B1124387
theorem B1896493 : Blo 330750 1896493 := bstep (se 3 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 1896493 = 711185) B711185
theorem B946379 : Blo 330750 946379 := bstep (se 1 (by rfl) ⟨709784, by rfl⟩ : syracuseStep 946379 = 1419569) B1419569
theorem B749771 : Blo 330750 749771 := bstep (se 1 (by rfl) ⟨562328, by rfl⟩ : syracuseStep 749771 = 1124657) B1124657
theorem B749825 : Blo 330750 749825 := bstep (se 2 (by rfl) ⟨281184, by rfl⟩ : syracuseStep 749825 = 562369) B562369
theorem B422167 : Blo 330750 422167 := bstep (se 1 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 422167 = 633251) B633251
theorem B1012171 : Blo 330750 1012171 := bstep (se 1 (by rfl) ⟨759128, by rfl⟩ : syracuseStep 1012171 = 1518257) B1518257
theorem B750041 : Blo 330750 750041 := bstep (se 2 (by rfl) ⟨281265, by rfl⟩ : syracuseStep 750041 = 562531) B562531
theorem B6844945 : Blo 330750 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B750131 : Blo 330750 750131 := bstep (se 1 (by rfl) ⟨562598, by rfl⟩ : syracuseStep 750131 = 1125197) B1125197
theorem B750167 : Blo 330750 750167 := bstep (se 1 (by rfl) ⟨562625, by rfl⟩ : syracuseStep 750167 = 1125251) B1125251
theorem B750347 : Blo 330750 750347 := bstep (se 1 (by rfl) ⟨562760, by rfl⟩ : syracuseStep 750347 = 1125521) B1125521
theorem B750401 : Blo 330750 750401 := bstep (se 2 (by rfl) ⟨281400, by rfl⟩ : syracuseStep 750401 = 562801) B562801
theorem B2519909 : Blo 330750 2519909 := bstep (se 4 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 2519909 = 472483) B472483
theorem B750617 : Blo 330750 750617 := bstep (se 2 (by rfl) ⟨281481, by rfl⟩ : syracuseStep 750617 = 562963) B562963
theorem B750707 : Blo 330750 750707 := bstep (se 1 (by rfl) ⟨563030, by rfl⟩ : syracuseStep 750707 = 1126061) B1126061
theorem B750743 : Blo 330750 750743 := bstep (se 1 (by rfl) ⟨563057, by rfl⟩ : syracuseStep 750743 = 1126115) B1126115
theorem B2520395 : Blo 330750 2520395 := bstep (se 1 (by rfl) ⟨1890296, by rfl⟩ : syracuseStep 2520395 = 3780593) B3780593
theorem B750923 : Blo 330750 750923 := bstep (se 1 (by rfl) ⟨563192, by rfl⟩ : syracuseStep 750923 = 1126385) B1126385
theorem B750977 : Blo 330750 750977 := bstep (se 2 (by rfl) ⟨281616, by rfl⟩ : syracuseStep 750977 = 563233) B563233
theorem B751193 : Blo 330750 751193 := bstep (se 2 (by rfl) ⟨281697, by rfl⟩ : syracuseStep 751193 = 563395) B563395
theorem B751283 : Blo 330750 751283 := bstep (se 1 (by rfl) ⟨563462, by rfl⟩ : syracuseStep 751283 = 1126925) B1126925
theorem B751319 : Blo 330750 751319 := bstep (se 1 (by rfl) ⟨563489, by rfl⟩ : syracuseStep 751319 = 1126979) B1126979
theorem B1275671 : Blo 330750 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B948019 : Blo 330750 948019 := bstep (se 1 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 948019 = 1422029) B1422029
theorem B751499 : Blo 330750 751499 := bstep (se 1 (by rfl) ⟨563624, by rfl⟩ : syracuseStep 751499 = 1127249) B1127249
theorem B751553 : Blo 330750 751553 := bstep (se 2 (by rfl) ⟨281832, by rfl⟩ : syracuseStep 751553 = 563665) B563665
theorem B1341515 : Blo 330750 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B751769 : Blo 330750 751769 := bstep (se 2 (by rfl) ⟨281913, by rfl⟩ : syracuseStep 751769 = 563827) B563827
theorem B751859 : Blo 330750 751859 := bstep (se 1 (by rfl) ⟨563894, by rfl⟩ : syracuseStep 751859 = 1127789) B1127789
theorem B751895 : Blo 330750 751895 := bstep (se 1 (by rfl) ⟨563921, by rfl⟩ : syracuseStep 751895 = 1127843) B1127843
theorem B850355 : Blo 330750 850355 := bstep (se 1 (by rfl) ⟨637766, by rfl⟩ : syracuseStep 850355 = 1275533) B1275533
theorem B752075 : Blo 330750 752075 := bstep (se 1 (by rfl) ⟨564056, by rfl⟩ : syracuseStep 752075 = 1128113) B1128113
theorem B752129 : Blo 330750 752129 := bstep (se 2 (by rfl) ⟨282048, by rfl⟩ : syracuseStep 752129 = 564097) B564097
theorem B2882141 : Blo 330750 2882141 := bstep (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) B1080803
theorem B1342097 : Blo 330750 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B457367 : Blo 330750 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B752345 : Blo 330750 752345 := bstep (se 2 (by rfl) ⟨282129, by rfl⟩ : syracuseStep 752345 = 564259) B564259
theorem B752435 : Blo 330750 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B949067 : Blo 330750 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B752471 : Blo 330750 752471 := bstep (se 1 (by rfl) ⟨564353, by rfl⟩ : syracuseStep 752471 = 1128707) B1128707
theorem B752651 : Blo 330750 752651 := bstep (se 1 (by rfl) ⟨564488, by rfl⟩ : syracuseStep 752651 = 1128977) B1128977
theorem B1375255 : Blo 330750 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B752705 : Blo 330750 752705 := bstep (se 2 (by rfl) ⟨282264, by rfl⟩ : syracuseStep 752705 = 564529) B564529
theorem B752921 : Blo 330750 752921 := bstep (se 2 (by rfl) ⟨282345, by rfl⟩ : syracuseStep 752921 = 564691) B564691
theorem B753011 : Blo 330750 753011 := bstep (se 1 (by rfl) ⟨564758, by rfl⟩ : syracuseStep 753011 = 1129517) B1129517
theorem B753047 : Blo 330750 753047 := bstep (se 1 (by rfl) ⟨564785, by rfl⟩ : syracuseStep 753047 = 1129571) B1129571
theorem B851393 : Blo 330750 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B1114913 : Blo 330750 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B1705079 : Blo 330750 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B558265 : Blo 330750 558265 := bstep (se 2 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 558265 = 418699) B418699
theorem B6161645 : Blo 330750 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B1901825 : Blo 330750 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B3180035 : Blo 330750 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B558967 : Blo 330750 558967 := bstep (se 1 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 558967 = 838451) B838451
theorem B853895 : Blo 330750 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B952211 : Blo 330750 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B2131915 : Blo 330750 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B1607627 : Blo 330750 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B4032517 : Blo 330750 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B559163 : Blo 330750 559163 := bstep (se 1 (by rfl) ⟨419372, by rfl⟩ : syracuseStep 559163 = 838745) B838745
theorem B1804517 : Blo 330750 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B6621425 : Blo 330750 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1116449 : Blo 330750 1116449 := bstep (se 2 (by rfl) ⟨418668, by rfl⟩ : syracuseStep 1116449 = 837337) B837337
theorem B559561 : Blo 330750 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B952985 : Blo 330750 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B1117043 : Blo 330750 1117043 := bstep (se 1 (by rfl) ⟨837782, by rfl⟩ : syracuseStep 1117043 = 1675565) B1675565
theorem B330759 : Blo 330750 330759 := bstep (se 1 (by rfl) ⟨248069, by rfl⟩ : syracuseStep 330759 = 496139) B496139
theorem B2853899 : Blo 330750 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B330767 : Blo 330750 330767 := bstep (se 1 (by rfl) ⟨248075, by rfl⟩ : syracuseStep 330767 = 496151) B496151
theorem B330811 : Blo 330750 330811 := bstep (se 1 (by rfl) ⟨248108, by rfl⟩ : syracuseStep 330811 = 496217) B496217
theorem B330887 : Blo 330750 330887 := bstep (se 1 (by rfl) ⟨248165, by rfl⟩ : syracuseStep 330887 = 496331) B496331
theorem B560263 : Blo 330750 560263 := bstep (se 1 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 560263 = 840395) B840395
theorem B330895 : Blo 330750 330895 := bstep (se 1 (by rfl) ⟨248171, by rfl⟩ : syracuseStep 330895 = 496343) B496343
theorem B330939 : Blo 330750 330939 := bstep (se 1 (by rfl) ⟨248204, by rfl⟩ : syracuseStep 330939 = 496409) B496409
theorem B331015 : Blo 330750 331015 := bstep (se 1 (by rfl) ⟨248261, by rfl⟩ : syracuseStep 331015 = 496523) B496523
theorem B331023 : Blo 330750 331023 := bstep (se 1 (by rfl) ⟨248267, by rfl⟩ : syracuseStep 331023 = 496535) B496535
theorem B331067 : Blo 330750 331067 := bstep (se 1 (by rfl) ⟨248300, by rfl⟩ : syracuseStep 331067 = 496601) B496601
theorem B331143 : Blo 330750 331143 := bstep (se 1 (by rfl) ⟨248357, by rfl⟩ : syracuseStep 331143 = 496715) B496715
theorem B331151 : Blo 330750 331151 := bstep (se 1 (by rfl) ⟨248363, by rfl⟩ : syracuseStep 331151 = 496727) B496727
theorem B1904057 : Blo 330750 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B331195 : Blo 330750 331195 := bstep (se 1 (by rfl) ⟨248396, by rfl⟩ : syracuseStep 331195 = 496793) B496793
theorem B1674755 : Blo 330750 1674755 := bstep (se 1 (by rfl) ⟨1256066, by rfl⟩ : syracuseStep 1674755 = 2512133) B2512133
theorem B331271 : Blo 330750 331271 := bstep (se 1 (by rfl) ⟨248453, by rfl⟩ : syracuseStep 331271 = 496907) B496907
theorem B331279 : Blo 330750 331279 := bstep (se 1 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 331279 = 496919) B496919
theorem B331323 : Blo 330750 331323 := bstep (se 1 (by rfl) ⟨248492, by rfl⟩ : syracuseStep 331323 = 496985) B496985
theorem B2887235 : Blo 330750 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B331399 : Blo 330750 331399 := bstep (se 1 (by rfl) ⟨248549, by rfl⟩ : syracuseStep 331399 = 497099) B497099
theorem B331407 : Blo 330750 331407 := bstep (se 1 (by rfl) ⟨248555, by rfl⟩ : syracuseStep 331407 = 497111) B497111
theorem B331451 : Blo 330750 331451 := bstep (se 1 (by rfl) ⟨248588, by rfl⟩ : syracuseStep 331451 = 497177) B497177
theorem B1281737 : Blo 330750 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B1969921 : Blo 330750 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B331527 : Blo 330750 331527 := bstep (se 1 (by rfl) ⟨248645, by rfl⟩ : syracuseStep 331527 = 497291) B497291
theorem B331535 : Blo 330750 331535 := bstep (se 1 (by rfl) ⟨248651, by rfl⟩ : syracuseStep 331535 = 497303) B497303
theorem B560911 : Blo 330750 560911 := bstep (se 1 (by rfl) ⟨420683, by rfl⟩ : syracuseStep 560911 = 841367) B841367
theorem B1412923 : Blo 330750 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B331579 : Blo 330750 331579 := bstep (se 1 (by rfl) ⟨248684, by rfl⟩ : syracuseStep 331579 = 497369) B497369
theorem B331655 : Blo 330750 331655 := bstep (se 1 (by rfl) ⟨248741, by rfl⟩ : syracuseStep 331655 = 497483) B497483
theorem B331663 : Blo 330750 331663 := bstep (se 1 (by rfl) ⟨248747, by rfl⟩ : syracuseStep 331663 = 497495) B497495
theorem B331707 : Blo 330750 331707 := bstep (se 1 (by rfl) ⟨248780, by rfl⟩ : syracuseStep 331707 = 497561) B497561
theorem B2297803 : Blo 330750 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B331783 : Blo 330750 331783 := bstep (se 1 (by rfl) ⟨248837, by rfl⟩ : syracuseStep 331783 = 497675) B497675
theorem B331791 : Blo 330750 331791 := bstep (se 1 (by rfl) ⟨248843, by rfl⟩ : syracuseStep 331791 = 497687) B497687
theorem B6098989 : Blo 330750 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B331835 : Blo 330750 331835 := bstep (se 1 (by rfl) ⟨248876, by rfl⟩ : syracuseStep 331835 = 497753) B497753
theorem B6951005 : Blo 330750 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B5673077 : Blo 330750 5673077 := bstep (se 5 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 5673077 = 531851) B531851
theorem B331911 : Blo 330750 331911 := bstep (se 1 (by rfl) ⟨248933, by rfl⟩ : syracuseStep 331911 = 497867) B497867
theorem B331919 : Blo 330750 331919 := bstep (se 1 (by rfl) ⟨248939, by rfl⟩ : syracuseStep 331919 = 497879) B497879
theorem B331963 : Blo 330750 331963 := bstep (se 1 (by rfl) ⟨248972, by rfl⟩ : syracuseStep 331963 = 497945) B497945
theorem B332039 : Blo 330750 332039 := bstep (se 1 (by rfl) ⟨249029, by rfl⟩ : syracuseStep 332039 = 498059) B498059
theorem B332047 : Blo 330750 332047 := bstep (se 1 (by rfl) ⟨249035, by rfl⟩ : syracuseStep 332047 = 498071) B498071
theorem B561451 : Blo 330750 561451 := bstep (se 1 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 561451 = 842177) B842177
theorem B332091 : Blo 330750 332091 := bstep (se 1 (by rfl) ⟨249068, by rfl⟩ : syracuseStep 332091 = 498137) B498137
theorem B332167 : Blo 330750 332167 := bstep (se 1 (by rfl) ⟨249125, by rfl⟩ : syracuseStep 332167 = 498251) B498251
theorem B332175 : Blo 330750 332175 := bstep (se 1 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 332175 = 498263) B498263
theorem B561593 : Blo 330750 561593 := bstep (se 2 (by rfl) ⟨210597, by rfl⟩ : syracuseStep 561593 = 421195) B421195
theorem B332219 : Blo 330750 332219 := bstep (se 1 (by rfl) ⟨249164, by rfl⟩ : syracuseStep 332219 = 498329) B498329
theorem B332295 : Blo 330750 332295 := bstep (se 1 (by rfl) ⟨249221, by rfl⟩ : syracuseStep 332295 = 498443) B498443
theorem B332303 : Blo 330750 332303 := bstep (se 1 (by rfl) ⟨249227, by rfl⟩ : syracuseStep 332303 = 498455) B498455
theorem B496187 : Blo 330750 496187 := bstep (se 1 (by rfl) ⟨372140, by rfl⟩ : syracuseStep 496187 = 744281) B744281
theorem B332347 : Blo 330750 332347 := bstep (se 1 (by rfl) ⟨249260, by rfl⟩ : syracuseStep 332347 = 498521) B498521
theorem B496247 : Blo 330750 496247 := bstep (se 1 (by rfl) ⟨372185, by rfl⟩ : syracuseStep 496247 = 744371) B744371
theorem B332423 : Blo 330750 332423 := bstep (se 1 (by rfl) ⟨249317, by rfl⟩ : syracuseStep 332423 = 498635) B498635
theorem B496271 : Blo 330750 496271 := bstep (se 1 (by rfl) ⟨372203, by rfl⟩ : syracuseStep 496271 = 744407) B744407
theorem B332431 : Blo 330750 332431 := bstep (se 1 (by rfl) ⟨249323, by rfl⟩ : syracuseStep 332431 = 498647) B498647
theorem B496313 : Blo 330750 496313 := bstep (se 2 (by rfl) ⟨186117, by rfl⟩ : syracuseStep 496313 = 372235) B372235
theorem B332475 : Blo 330750 332475 := bstep (se 1 (by rfl) ⟨249356, by rfl⟩ : syracuseStep 332475 = 498713) B498713
theorem B496391 : Blo 330750 496391 := bstep (se 1 (by rfl) ⟨372293, by rfl⟩ : syracuseStep 496391 = 744587) B744587
theorem B332551 : Blo 330750 332551 := bstep (se 1 (by rfl) ⟨249413, by rfl⟩ : syracuseStep 332551 = 498827) B498827
theorem B332559 : Blo 330750 332559 := bstep (se 1 (by rfl) ⟨249419, by rfl⟩ : syracuseStep 332559 = 498839) B498839
theorem B3904271 : Blo 330750 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B496427 : Blo 330750 496427 := bstep (se 1 (by rfl) ⟨372320, by rfl⟩ : syracuseStep 496427 = 744641) B744641
theorem B332603 : Blo 330750 332603 := bstep (se 1 (by rfl) ⟨249452, by rfl⟩ : syracuseStep 332603 = 498905) B498905
theorem B496457 : Blo 330750 496457 := bstep (se 2 (by rfl) ⟨186171, by rfl⟩ : syracuseStep 496457 = 372343) B372343
theorem B332679 : Blo 330750 332679 := bstep (se 1 (by rfl) ⟨249509, by rfl⟩ : syracuseStep 332679 = 499019) B499019
theorem B332687 : Blo 330750 332687 := bstep (se 1 (by rfl) ⟨249515, by rfl⟩ : syracuseStep 332687 = 499031) B499031
theorem B496571 : Blo 330750 496571 := bstep (se 1 (by rfl) ⟨372428, by rfl⟩ : syracuseStep 496571 = 744857) B744857
theorem B332731 : Blo 330750 332731 := bstep (se 1 (by rfl) ⟨249548, by rfl⟩ : syracuseStep 332731 = 499097) B499097
theorem B496631 : Blo 330750 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B332807 : Blo 330750 332807 := bstep (se 1 (by rfl) ⟨249605, by rfl⟩ : syracuseStep 332807 = 499211) B499211
theorem B857099 : Blo 330750 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B496655 : Blo 330750 496655 := bstep (se 1 (by rfl) ⟨372491, by rfl⟩ : syracuseStep 496655 = 744983) B744983
theorem B332815 : Blo 330750 332815 := bstep (se 1 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 332815 = 499223) B499223
theorem B496697 : Blo 330750 496697 := bstep (se 2 (by rfl) ⟨186261, by rfl⟩ : syracuseStep 496697 = 372523) B372523
theorem B332859 : Blo 330750 332859 := bstep (se 1 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 332859 = 499289) B499289
theorem B1414205 : Blo 330750 1414205 := bstep (se 3 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 1414205 = 530327) B530327
theorem B1676375 : Blo 330750 1676375 := bstep (se 1 (by rfl) ⟨1257281, by rfl⟩ : syracuseStep 1676375 = 2514563) B2514563
theorem B562295 : Blo 330750 562295 := bstep (se 1 (by rfl) ⟨421721, by rfl⟩ : syracuseStep 562295 = 843443) B843443
theorem B496775 : Blo 330750 496775 := bstep (se 1 (by rfl) ⟨372581, by rfl⟩ : syracuseStep 496775 = 745163) B745163
theorem B332935 : Blo 330750 332935 := bstep (se 1 (by rfl) ⟨249701, by rfl⟩ : syracuseStep 332935 = 499403) B499403
theorem B332943 : Blo 330750 332943 := bstep (se 1 (by rfl) ⟨249707, by rfl⟩ : syracuseStep 332943 = 499415) B499415
theorem B496811 : Blo 330750 496811 := bstep (se 1 (by rfl) ⟨372608, by rfl⟩ : syracuseStep 496811 = 745217) B745217
theorem B332987 : Blo 330750 332987 := bstep (se 1 (by rfl) ⟨249740, by rfl⟩ : syracuseStep 332987 = 499481) B499481
theorem B496841 : Blo 330750 496841 := bstep (se 2 (by rfl) ⟨186315, by rfl⟩ : syracuseStep 496841 = 372631) B372631
theorem B333063 : Blo 330750 333063 := bstep (se 1 (by rfl) ⟨249797, by rfl⟩ : syracuseStep 333063 = 499595) B499595
theorem B333071 : Blo 330750 333071 := bstep (se 1 (by rfl) ⟨249803, by rfl⟩ : syracuseStep 333071 = 499607) B499607
theorem B496955 : Blo 330750 496955 := bstep (se 1 (by rfl) ⟨372716, by rfl⟩ : syracuseStep 496955 = 745433) B745433
theorem B333115 : Blo 330750 333115 := bstep (se 1 (by rfl) ⟨249836, by rfl⟩ : syracuseStep 333115 = 499673) B499673
theorem B628087 : Blo 330750 628087 := bstep (se 1 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 628087 = 942131) B942131
theorem B497015 : Blo 330750 497015 := bstep (se 1 (by rfl) ⟨372761, by rfl⟩ : syracuseStep 497015 = 745523) B745523
theorem B333191 : Blo 330750 333191 := bstep (se 1 (by rfl) ⟨249893, by rfl⟩ : syracuseStep 333191 = 499787) B499787
theorem B497039 : Blo 330750 497039 := bstep (se 1 (by rfl) ⟨372779, by rfl⟩ : syracuseStep 497039 = 745559) B745559
theorem B333199 : Blo 330750 333199 := bstep (se 1 (by rfl) ⟨249899, by rfl⟩ : syracuseStep 333199 = 499799) B499799
theorem B2528657 : Blo 330750 2528657 := bstep (se 2 (by rfl) ⟨948246, by rfl⟩ : syracuseStep 2528657 = 1896493) B1896493
theorem B1119635 : Blo 330750 1119635 := bstep (se 1 (by rfl) ⟨839726, by rfl⟩ : syracuseStep 1119635 = 1679453) B1679453
theorem B497081 : Blo 330750 497081 := bstep (se 2 (by rfl) ⟨186405, by rfl⟩ : syracuseStep 497081 = 372811) B372811
theorem B333243 : Blo 330750 333243 := bstep (se 1 (by rfl) ⟨249932, by rfl⟩ : syracuseStep 333243 = 499865) B499865
theorem B497159 : Blo 330750 497159 := bstep (se 1 (by rfl) ⟨372869, by rfl⟩ : syracuseStep 497159 = 745739) B745739
theorem B333319 : Blo 330750 333319 := bstep (se 1 (by rfl) ⟨249989, by rfl⟩ : syracuseStep 333319 = 499979) B499979
theorem B333327 : Blo 330750 333327 := bstep (se 1 (by rfl) ⟨249995, by rfl⟩ : syracuseStep 333327 = 499991) B499991
theorem B1906199 : Blo 330750 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B497195 : Blo 330750 497195 := bstep (se 1 (by rfl) ⟨372896, by rfl⟩ : syracuseStep 497195 = 745793) B745793
theorem B333371 : Blo 330750 333371 := bstep (se 1 (by rfl) ⟨250028, by rfl⟩ : syracuseStep 333371 = 500057) B500057
theorem B562747 : Blo 330750 562747 := bstep (se 1 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 562747 = 844121) B844121
theorem B1676861 : Blo 330750 1676861 := bstep (se 3 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 1676861 = 628823) B628823
theorem B497225 : Blo 330750 497225 := bstep (se 2 (by rfl) ⟨186459, by rfl⟩ : syracuseStep 497225 = 372919) B372919
theorem B333447 : Blo 330750 333447 := bstep (se 1 (by rfl) ⟨250085, by rfl⟩ : syracuseStep 333447 = 500171) B500171
theorem B333455 : Blo 330750 333455 := bstep (se 1 (by rfl) ⟨250091, by rfl⟩ : syracuseStep 333455 = 500183) B500183
theorem B497339 : Blo 330750 497339 := bstep (se 1 (by rfl) ⟨373004, by rfl⟩ : syracuseStep 497339 = 746009) B746009
theorem B333499 : Blo 330750 333499 := bstep (se 1 (by rfl) ⟨250124, by rfl⟩ : syracuseStep 333499 = 500249) B500249
theorem B562889 : Blo 330750 562889 := bstep (se 2 (by rfl) ⟨211083, by rfl⟩ : syracuseStep 562889 = 422167) B422167
theorem B497399 : Blo 330750 497399 := bstep (se 1 (by rfl) ⟨373049, by rfl⟩ : syracuseStep 497399 = 746099) B746099
theorem B333575 : Blo 330750 333575 := bstep (se 1 (by rfl) ⟨250181, by rfl⟩ : syracuseStep 333575 = 500363) B500363
theorem B497423 : Blo 330750 497423 := bstep (se 1 (by rfl) ⟨373067, by rfl⟩ : syracuseStep 497423 = 746135) B746135
theorem B399119 : Blo 330750 399119 := bstep (se 1 (by rfl) ⟨299339, by rfl⟩ : syracuseStep 399119 = 598679) B598679
theorem B333583 : Blo 330750 333583 := bstep (se 1 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 333583 = 500375) B500375
theorem B497465 : Blo 330750 497465 := bstep (se 2 (by rfl) ⟨186549, by rfl⟩ : syracuseStep 497465 = 373099) B373099
theorem B333627 : Blo 330750 333627 := bstep (se 1 (by rfl) ⟨250220, by rfl⟩ : syracuseStep 333627 = 500441) B500441
theorem B9639749 : Blo 330750 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B497543 : Blo 330750 497543 := bstep (se 1 (by rfl) ⟨373157, by rfl⟩ : syracuseStep 497543 = 746315) B746315
theorem B333703 : Blo 330750 333703 := bstep (se 1 (by rfl) ⟨250277, by rfl⟩ : syracuseStep 333703 = 500555) B500555
theorem B333711 : Blo 330750 333711 := bstep (se 1 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 333711 = 500567) B500567
theorem B2693017 : Blo 330750 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B497579 : Blo 330750 497579 := bstep (se 1 (by rfl) ⟨373184, by rfl⟩ : syracuseStep 497579 = 746369) B746369
theorem B1349561 : Blo 330750 1349561 := bstep (se 2 (by rfl) ⟨506085, by rfl⟩ : syracuseStep 1349561 = 1012171) B1012171
theorem B333755 : Blo 330750 333755 := bstep (se 1 (by rfl) ⟨250316, by rfl⟩ : syracuseStep 333755 = 500633) B500633
theorem B497609 : Blo 330750 497609 := bstep (se 2 (by rfl) ⟨186603, by rfl⟩ : syracuseStep 497609 = 373207) B373207
theorem B333831 : Blo 330750 333831 := bstep (se 1 (by rfl) ⟨250373, by rfl⟩ : syracuseStep 333831 = 500747) B500747
theorem B333839 : Blo 330750 333839 := bstep (se 1 (by rfl) ⟨250379, by rfl⟩ : syracuseStep 333839 = 500759) B500759
theorem B497723 : Blo 330750 497723 := bstep (se 1 (by rfl) ⟨373292, by rfl⟩ : syracuseStep 497723 = 746585) B746585
theorem B333883 : Blo 330750 333883 := bstep (se 1 (by rfl) ⟨250412, by rfl⟩ : syracuseStep 333883 = 500825) B500825
theorem B497783 : Blo 330750 497783 := bstep (se 1 (by rfl) ⟨373337, by rfl⟩ : syracuseStep 497783 = 746675) B746675
theorem B333959 : Blo 330750 333959 := bstep (se 1 (by rfl) ⟨250469, by rfl⟩ : syracuseStep 333959 = 500939) B500939
theorem B497807 : Blo 330750 497807 := bstep (se 1 (by rfl) ⟨373355, by rfl⟩ : syracuseStep 497807 = 746711) B746711
theorem B333967 : Blo 330750 333967 := bstep (se 1 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 333967 = 500951) B500951
theorem B497849 : Blo 330750 497849 := bstep (se 2 (by rfl) ⟨186693, by rfl⟩ : syracuseStep 497849 = 373387) B373387
theorem B334011 : Blo 330750 334011 := bstep (se 1 (by rfl) ⟨250508, by rfl⟩ : syracuseStep 334011 = 501017) B501017
theorem B497927 : Blo 330750 497927 := bstep (se 1 (by rfl) ⟨373445, by rfl⟩ : syracuseStep 497927 = 746891) B746891
theorem B334087 : Blo 330750 334087 := bstep (se 1 (by rfl) ⟨250565, by rfl⟩ : syracuseStep 334087 = 501131) B501131
theorem B4921613 : Blo 330750 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B334095 : Blo 330750 334095 := bstep (se 1 (by rfl) ⟨250571, by rfl⟩ : syracuseStep 334095 = 501143) B501143
theorem B497963 : Blo 330750 497963 := bstep (se 1 (by rfl) ⟨373472, by rfl⟩ : syracuseStep 497963 = 746945) B746945
theorem B334139 : Blo 330750 334139 := bstep (se 1 (by rfl) ⟨250604, by rfl⟩ : syracuseStep 334139 = 501209) B501209
theorem B497993 : Blo 330750 497993 := bstep (se 2 (by rfl) ⟨186747, by rfl⟩ : syracuseStep 497993 = 373495) B373495
theorem B563591 : Blo 330750 563591 := bstep (se 1 (by rfl) ⟨422693, by rfl⟩ : syracuseStep 563591 = 845387) B845387
theorem B334215 : Blo 330750 334215 := bstep (se 1 (by rfl) ⟨250661, by rfl⟩ : syracuseStep 334215 = 501323) B501323
theorem B334223 : Blo 330750 334223 := bstep (se 1 (by rfl) ⟨250667, by rfl⟩ : syracuseStep 334223 = 501335) B501335
theorem B498107 : Blo 330750 498107 := bstep (se 1 (by rfl) ⟨373580, by rfl⟩ : syracuseStep 498107 = 747161) B747161
theorem B334267 : Blo 330750 334267 := bstep (se 1 (by rfl) ⟨250700, by rfl⟩ : syracuseStep 334267 = 501401) B501401
theorem B2202065 : Blo 330750 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B498167 : Blo 330750 498167 := bstep (se 1 (by rfl) ⟨373625, by rfl⟩ : syracuseStep 498167 = 747251) B747251
theorem B334343 : Blo 330750 334343 := bstep (se 1 (by rfl) ⟨250757, by rfl⟩ : syracuseStep 334343 = 501515) B501515
theorem B498191 : Blo 330750 498191 := bstep (se 1 (by rfl) ⟨373643, by rfl⟩ : syracuseStep 498191 = 747287) B747287
theorem B334351 : Blo 330750 334351 := bstep (se 1 (by rfl) ⟨250763, by rfl⟩ : syracuseStep 334351 = 501527) B501527
theorem B498233 : Blo 330750 498233 := bstep (se 2 (by rfl) ⟨186837, by rfl⟩ : syracuseStep 498233 = 373675) B373675
theorem B334395 : Blo 330750 334395 := bstep (se 1 (by rfl) ⟨250796, by rfl⟩ : syracuseStep 334395 = 501593) B501593
theorem B498311 : Blo 330750 498311 := bstep (se 1 (by rfl) ⟨373733, by rfl⟩ : syracuseStep 498311 = 747467) B747467
theorem B334471 : Blo 330750 334471 := bstep (se 1 (by rfl) ⟨250853, by rfl⟩ : syracuseStep 334471 = 501707) B501707
theorem B334479 : Blo 330750 334479 := bstep (se 1 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 334479 = 501719) B501719
theorem B498347 : Blo 330750 498347 := bstep (se 1 (by rfl) ⟨373760, by rfl⟩ : syracuseStep 498347 = 747521) B747521
theorem B334523 : Blo 330750 334523 := bstep (se 1 (by rfl) ⟨250892, by rfl⟩ : syracuseStep 334523 = 501785) B501785
theorem B498377 : Blo 330750 498377 := bstep (se 2 (by rfl) ⟨186891, by rfl⟩ : syracuseStep 498377 = 373783) B373783
theorem B334599 : Blo 330750 334599 := bstep (se 1 (by rfl) ⟨250949, by rfl⟩ : syracuseStep 334599 = 501899) B501899
theorem B1121039 : Blo 330750 1121039 := bstep (se 1 (by rfl) ⟨840779, by rfl⟩ : syracuseStep 1121039 = 1681559) B1681559
theorem B334607 : Blo 330750 334607 := bstep (se 1 (by rfl) ⟨250955, by rfl⟩ : syracuseStep 334607 = 501911) B501911
theorem B498491 : Blo 330750 498491 := bstep (se 1 (by rfl) ⟨373868, by rfl⟩ : syracuseStep 498491 = 747737) B747737
theorem B334651 : Blo 330750 334651 := bstep (se 1 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 334651 = 501977) B501977
theorem B498551 : Blo 330750 498551 := bstep (se 1 (by rfl) ⟨373913, by rfl⟩ : syracuseStep 498551 = 747827) B747827
theorem B334727 : Blo 330750 334727 := bstep (se 1 (by rfl) ⟨251045, by rfl⟩ : syracuseStep 334727 = 502091) B502091
theorem B498575 : Blo 330750 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B334735 : Blo 330750 334735 := bstep (se 1 (by rfl) ⟨251051, by rfl⟩ : syracuseStep 334735 = 502103) B502103
theorem B629689 : Blo 330750 629689 := bstep (se 2 (by rfl) ⟨236133, by rfl⟩ : syracuseStep 629689 = 472267) B472267
theorem B498617 : Blo 330750 498617 := bstep (se 2 (by rfl) ⟨186981, by rfl⟩ : syracuseStep 498617 = 373963) B373963
theorem B4037579 : Blo 330750 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B498695 : Blo 330750 498695 := bstep (se 1 (by rfl) ⟨374021, by rfl⟩ : syracuseStep 498695 = 748043) B748043
theorem B597007 : Blo 330750 597007 := bstep (se 1 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 597007 = 895511) B895511
theorem B564239 : Blo 330750 564239 := bstep (se 1 (by rfl) ⟨423179, by rfl⟩ : syracuseStep 564239 = 846359) B846359
theorem B1121309 : Blo 330750 1121309 := bstep (se 3 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 1121309 = 420491) B420491
theorem B498731 : Blo 330750 498731 := bstep (se 1 (by rfl) ⟨374048, by rfl⟩ : syracuseStep 498731 = 748097) B748097
theorem B1219645 : Blo 330750 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B498761 : Blo 330750 498761 := bstep (se 2 (by rfl) ⟨187035, by rfl⟩ : syracuseStep 498761 = 374071) B374071
theorem B3021911 : Blo 330750 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B498875 : Blo 330750 498875 := bstep (se 1 (by rfl) ⟨374156, by rfl⟩ : syracuseStep 498875 = 748313) B748313
theorem B498935 : Blo 330750 498935 := bstep (se 1 (by rfl) ⟨374201, by rfl⟩ : syracuseStep 498935 = 748403) B748403
theorem B630031 : Blo 330750 630031 := bstep (se 1 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 630031 = 945047) B945047
theorem B498959 : Blo 330750 498959 := bstep (se 1 (by rfl) ⟨374219, by rfl⟩ : syracuseStep 498959 = 748439) B748439
theorem B2858273 : Blo 330750 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B1678643 : Blo 330750 1678643 := bstep (se 1 (by rfl) ⟨1258982, by rfl⟩ : syracuseStep 1678643 = 2517965) B2517965
theorem B499001 : Blo 330750 499001 := bstep (se 2 (by rfl) ⟨187125, by rfl⟩ : syracuseStep 499001 = 374251) B374251
theorem B499079 : Blo 330750 499079 := bstep (se 1 (by rfl) ⟨374309, by rfl⟩ : syracuseStep 499079 = 748619) B748619
theorem B499115 : Blo 330750 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B499145 : Blo 330750 499145 := bstep (se 2 (by rfl) ⟨187179, by rfl⟩ : syracuseStep 499145 = 374359) B374359
theorem B4038173 : Blo 330750 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B564779 : Blo 330750 564779 := bstep (se 1 (by rfl) ⟨423584, by rfl⟩ : syracuseStep 564779 = 847169) B847169
theorem B499259 : Blo 330750 499259 := bstep (se 1 (by rfl) ⟨374444, by rfl⟩ : syracuseStep 499259 = 748889) B748889
theorem B1678967 : Blo 330750 1678967 := bstep (se 1 (by rfl) ⟨1259225, by rfl⟩ : syracuseStep 1678967 = 2518451) B2518451
theorem B499319 : Blo 330750 499319 := bstep (se 1 (by rfl) ⟨374489, by rfl⟩ : syracuseStep 499319 = 748979) B748979
theorem B499343 : Blo 330750 499343 := bstep (se 1 (by rfl) ⟨374507, by rfl⟩ : syracuseStep 499343 = 749015) B749015
theorem B12754583 : Blo 330750 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B499385 : Blo 330750 499385 := bstep (se 2 (by rfl) ⟨187269, by rfl⟩ : syracuseStep 499385 = 374539) B374539
theorem B499463 : Blo 330750 499463 := bstep (se 1 (by rfl) ⟨374597, by rfl⟩ : syracuseStep 499463 = 749195) B749195
theorem B2531087 : Blo 330750 2531087 := bstep (se 1 (by rfl) ⟨1898315, by rfl⟩ : syracuseStep 2531087 = 3796631) B3796631
theorem B499499 : Blo 330750 499499 := bstep (se 1 (by rfl) ⟨374624, by rfl⟩ : syracuseStep 499499 = 749249) B749249
theorem B401195 : Blo 330750 401195 := bstep (se 1 (by rfl) ⟨300896, by rfl⟩ : syracuseStep 401195 = 601793) B601793
theorem B499529 : Blo 330750 499529 := bstep (se 2 (by rfl) ⟨187323, by rfl⟩ : syracuseStep 499529 = 374647) B374647
theorem B499643 : Blo 330750 499643 := bstep (se 1 (by rfl) ⟨374732, by rfl⟩ : syracuseStep 499643 = 749465) B749465
theorem B499703 : Blo 330750 499703 := bstep (se 1 (by rfl) ⟨374777, by rfl⟩ : syracuseStep 499703 = 749555) B749555
theorem B499727 : Blo 330750 499727 := bstep (se 1 (by rfl) ⟨374795, by rfl⟩ : syracuseStep 499727 = 749591) B749591
theorem B499769 : Blo 330750 499769 := bstep (se 2 (by rfl) ⟨187413, by rfl⟩ : syracuseStep 499769 = 374827) B374827
theorem B630919 : Blo 330750 630919 := bstep (se 1 (by rfl) ⟨473189, by rfl⟩ : syracuseStep 630919 = 946379) B946379
theorem B499847 : Blo 330750 499847 := bstep (se 1 (by rfl) ⟨374885, by rfl⟩ : syracuseStep 499847 = 749771) B749771
theorem B499883 : Blo 330750 499883 := bstep (se 1 (by rfl) ⟨374912, by rfl⟩ : syracuseStep 499883 = 749825) B749825
theorem B499913 : Blo 330750 499913 := bstep (se 2 (by rfl) ⟨187467, by rfl⟩ : syracuseStep 499913 = 374935) B374935
theorem B500027 : Blo 330750 500027 := bstep (se 1 (by rfl) ⟨375020, by rfl⟩ : syracuseStep 500027 = 750041) B750041
theorem B500087 : Blo 330750 500087 := bstep (se 1 (by rfl) ⟨375065, by rfl⟩ : syracuseStep 500087 = 750131) B750131
theorem B500111 : Blo 330750 500111 := bstep (se 1 (by rfl) ⟨375083, by rfl⟩ : syracuseStep 500111 = 750167) B750167
theorem B1122713 : Blo 330750 1122713 := bstep (se 2 (by rfl) ⟨421017, by rfl⟩ : syracuseStep 1122713 = 842035) B842035
theorem B500153 : Blo 330750 500153 := bstep (se 2 (by rfl) ⟨187557, by rfl⟩ : syracuseStep 500153 = 375115) B375115
theorem B16097777 : Blo 330750 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B500231 : Blo 330750 500231 := bstep (se 1 (by rfl) ⟨375173, by rfl⟩ : syracuseStep 500231 = 750347) B750347
theorem B500267 : Blo 330750 500267 := bstep (se 1 (by rfl) ⟨375200, by rfl⟩ : syracuseStep 500267 = 750401) B750401
theorem B1679939 : Blo 330750 1679939 := bstep (se 1 (by rfl) ⟨1259954, by rfl⟩ : syracuseStep 1679939 = 2519909) B2519909
theorem B500297 : Blo 330750 500297 := bstep (se 2 (by rfl) ⟨187611, by rfl⟩ : syracuseStep 500297 = 375223) B375223
theorem B500411 : Blo 330750 500411 := bstep (se 1 (by rfl) ⟨375308, by rfl⟩ : syracuseStep 500411 = 750617) B750617
theorem B500471 : Blo 330750 500471 := bstep (se 1 (by rfl) ⟨375353, by rfl⟩ : syracuseStep 500471 = 750707) B750707
theorem B500495 : Blo 330750 500495 := bstep (se 1 (by rfl) ⟨375371, by rfl⟩ : syracuseStep 500495 = 750743) B750743
theorem B500537 : Blo 330750 500537 := bstep (se 2 (by rfl) ⟨187701, by rfl⟩ : syracuseStep 500537 = 375403) B375403
theorem B1680263 : Blo 330750 1680263 := bstep (se 1 (by rfl) ⟨1260197, by rfl⟩ : syracuseStep 1680263 = 2520395) B2520395
theorem B500615 : Blo 330750 500615 := bstep (se 1 (by rfl) ⟨375461, by rfl⟩ : syracuseStep 500615 = 750923) B750923
theorem B500651 : Blo 330750 500651 := bstep (se 1 (by rfl) ⟨375488, by rfl⟩ : syracuseStep 500651 = 750977) B750977
theorem B500681 : Blo 330750 500681 := bstep (se 2 (by rfl) ⟨187755, by rfl⟩ : syracuseStep 500681 = 375511) B375511
theorem B500795 : Blo 330750 500795 := bstep (se 1 (by rfl) ⟨375596, by rfl⟩ : syracuseStep 500795 = 751193) B751193
theorem B1123415 : Blo 330750 1123415 := bstep (se 1 (by rfl) ⟨842561, by rfl⟩ : syracuseStep 1123415 = 1685123) B1685123
theorem B500855 : Blo 330750 500855 := bstep (se 1 (by rfl) ⟨375641, by rfl⟩ : syracuseStep 500855 = 751283) B751283
theorem B500879 : Blo 330750 500879 := bstep (se 1 (by rfl) ⟨375659, by rfl⟩ : syracuseStep 500879 = 751319) B751319
theorem B500921 : Blo 330750 500921 := bstep (se 2 (by rfl) ⟨187845, by rfl⟩ : syracuseStep 500921 = 375691) B375691
theorem B500999 : Blo 330750 500999 := bstep (se 1 (by rfl) ⟨375749, by rfl⟩ : syracuseStep 500999 = 751499) B751499
theorem B501035 : Blo 330750 501035 := bstep (se 1 (by rfl) ⟨375776, by rfl⟩ : syracuseStep 501035 = 751553) B751553
theorem B501065 : Blo 330750 501065 := bstep (se 2 (by rfl) ⟨187899, by rfl⟩ : syracuseStep 501065 = 375799) B375799
theorem B894343 : Blo 330750 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B2827655 : Blo 330750 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B599443 : Blo 330750 599443 := bstep (se 1 (by rfl) ⟨449582, by rfl⟩ : syracuseStep 599443 = 899165) B899165
theorem B501179 : Blo 330750 501179 := bstep (se 1 (by rfl) ⟨375884, by rfl⟩ : syracuseStep 501179 = 751769) B751769
theorem B501239 : Blo 330750 501239 := bstep (se 1 (by rfl) ⟨375929, by rfl⟩ : syracuseStep 501239 = 751859) B751859
theorem B501263 : Blo 330750 501263 := bstep (se 1 (by rfl) ⟨375947, by rfl⟩ : syracuseStep 501263 = 751895) B751895
theorem B501305 : Blo 330750 501305 := bstep (se 2 (by rfl) ⟨187989, by rfl⟩ : syracuseStep 501305 = 375979) B375979
theorem B1123901 : Blo 330750 1123901 := bstep (se 3 (by rfl) ⟨210731, by rfl⟩ : syracuseStep 1123901 = 421463) B421463
theorem B566903 : Blo 330750 566903 := bstep (se 1 (by rfl) ⟨425177, by rfl⟩ : syracuseStep 566903 = 850355) B850355
theorem B501383 : Blo 330750 501383 := bstep (se 1 (by rfl) ⟨376037, by rfl⟩ : syracuseStep 501383 = 752075) B752075
theorem B501419 : Blo 330750 501419 := bstep (se 1 (by rfl) ⟨376064, by rfl⟩ : syracuseStep 501419 = 752129) B752129
theorem B1418953 : Blo 330750 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B501449 : Blo 330750 501449 := bstep (se 2 (by rfl) ⟨188043, by rfl⟩ : syracuseStep 501449 = 376087) B376087
theorem B2828033 : Blo 330750 2828033 := bstep (se 2 (by rfl) ⟨1060512, by rfl⟩ : syracuseStep 2828033 = 2121025) B2121025
theorem B894731 : Blo 330750 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B501563 : Blo 330750 501563 := bstep (se 1 (by rfl) ⟨376172, by rfl⟩ : syracuseStep 501563 = 752345) B752345
theorem B26388341 : Blo 330750 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B927607 : Blo 330750 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B501623 : Blo 330750 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B632711 : Blo 330750 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B501647 : Blo 330750 501647 := bstep (se 1 (by rfl) ⟨376235, by rfl⟩ : syracuseStep 501647 = 752471) B752471
theorem B894905 : Blo 330750 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B501689 : Blo 330750 501689 := bstep (se 2 (by rfl) ⟨188133, by rfl⟩ : syracuseStep 501689 = 376267) B376267
theorem B501767 : Blo 330750 501767 := bstep (se 1 (by rfl) ⟨376325, by rfl⟩ : syracuseStep 501767 = 752651) B752651
theorem B2697239 : Blo 330750 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B501803 : Blo 330750 501803 := bstep (se 1 (by rfl) ⟨376352, by rfl⟩ : syracuseStep 501803 = 752705) B752705
theorem B501833 : Blo 330750 501833 := bstep (se 2 (by rfl) ⟨188187, by rfl⟩ : syracuseStep 501833 = 376375) B376375
theorem B501947 : Blo 330750 501947 := bstep (se 1 (by rfl) ⟨376460, by rfl⟩ : syracuseStep 501947 = 752921) B752921
theorem B502007 : Blo 330750 502007 := bstep (se 1 (by rfl) ⟨376505, by rfl⟩ : syracuseStep 502007 = 753011) B753011
theorem B534799 : Blo 330750 534799 := bstep (se 1 (by rfl) ⟨401099, by rfl⟩ : syracuseStep 534799 = 802199) B802199
theorem B502031 : Blo 330750 502031 := bstep (se 1 (by rfl) ⟨376523, by rfl⟩ : syracuseStep 502031 = 753047) B753047
theorem B567595 : Blo 330750 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B502073 : Blo 330750 502073 := bstep (se 2 (by rfl) ⟨188277, by rfl⟩ : syracuseStep 502073 = 376555) B376555
theorem B1125305 : Blo 330750 1125305 := bstep (se 2 (by rfl) ⟨421989, by rfl⟩ : syracuseStep 1125305 = 843979) B843979
theorem B1420355 : Blo 330750 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B1256705 : Blo 330750 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B1125899 : Blo 330750 1125899 := bstep (se 1 (by rfl) ⟨844424, by rfl⟩ : syracuseStep 1125899 = 1688849) B1688849
theorem B1126007 : Blo 330750 1126007 := bstep (se 1 (by rfl) ⟨844505, by rfl⟩ : syracuseStep 1126007 = 1689011) B1689011
theorem B372487 : Blo 330750 372487 := bstep (se 1 (by rfl) ⟨279365, by rfl⟩ : syracuseStep 372487 = 558731) B558731
theorem B372667 : Blo 330750 372667 := bstep (se 1 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 372667 = 559001) B559001
theorem B503993 : Blo 330750 503993 := bstep (se 2 (by rfl) ⟨188997, by rfl⟩ : syracuseStep 503993 = 377995) B377995
theorem B1126601 : Blo 330750 1126601 := bstep (se 2 (by rfl) ⟨422475, by rfl⟩ : syracuseStep 1126601 = 844951) B844951
theorem B1356047 : Blo 330750 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B1519931 : Blo 330750 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B635195 : Blo 330750 635195 := bstep (se 1 (by rfl) ⟨476396, by rfl⟩ : syracuseStep 635195 = 952793) B952793
theorem B1683827 : Blo 330750 1683827 := bstep (se 1 (by rfl) ⟨1262870, by rfl⟩ : syracuseStep 1683827 = 2525741) B2525741
theorem B373135 : Blo 330750 373135 := bstep (se 1 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 373135 = 559703) B559703
theorem B1257875 : Blo 330750 1257875 := bstep (se 1 (by rfl) ⟨943406, by rfl⟩ : syracuseStep 1257875 = 1886813) B1886813
theorem B471595 : Blo 330750 471595 := bstep (se 1 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 471595 = 707393) B707393
theorem B6369911 : Blo 330750 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B1684313 : Blo 330750 1684313 := bstep (se 2 (by rfl) ⟨631617, by rfl⟩ : syracuseStep 1684313 = 1263235) B1263235
theorem B1258375 : Blo 330750 1258375 := bstep (se 1 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 1258375 = 1887563) B1887563
theorem B373639 : Blo 330750 373639 := bstep (se 1 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 373639 = 560459) B560459
theorem B1127303 : Blo 330750 1127303 := bstep (se 1 (by rfl) ⟨845477, by rfl⟩ : syracuseStep 1127303 = 1690955) B1690955
theorem B16135139 : Blo 330750 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B504839 : Blo 330750 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B4568075 : Blo 330750 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B373819 : Blo 330750 373819 := bstep (se 1 (by rfl) ⟨280364, by rfl⟩ : syracuseStep 373819 = 560729) B560729
theorem B1127681 : Blo 330750 1127681 := bstep (se 2 (by rfl) ⟨422880, by rfl⟩ : syracuseStep 1127681 = 845761) B845761
theorem B374287 : Blo 330750 374287 := bstep (se 1 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 374287 = 561431) B561431
theorem B2012759 : Blo 330750 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B472711 : Blo 330750 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B800545 : Blo 330750 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B5125963 : Blo 330750 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B374791 : Blo 330750 374791 := bstep (se 1 (by rfl) ⟨281093, by rfl⟩ : syracuseStep 374791 = 562187) B562187
theorem B2832407 : Blo 330750 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B1128491 : Blo 330750 1128491 := bstep (se 1 (by rfl) ⟨846368, by rfl⟩ : syracuseStep 1128491 = 1692737) B1692737
theorem B1062973 : Blo 330750 1062973 := bstep (se 3 (by rfl) ⟨199307, by rfl⟩ : syracuseStep 1062973 = 398615) B398615
theorem B800921 : Blo 330750 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B4044973 : Blo 330750 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B374971 : Blo 330750 374971 := bstep (se 1 (by rfl) ⟨281228, by rfl⟩ : syracuseStep 374971 = 562457) B562457
theorem B473531 : Blo 330750 473531 := bstep (se 1 (by rfl) ⟨355148, by rfl⟩ : syracuseStep 473531 = 710297) B710297
theorem B375439 : Blo 330750 375439 := bstep (se 1 (by rfl) ⟨281579, by rfl⟩ : syracuseStep 375439 = 563159) B563159
theorem B5389145 : Blo 330750 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B1686419 : Blo 330750 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B474169 : Blo 330750 474169 := bstep (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) B355627
theorem B375943 : Blo 330750 375943 := bstep (se 1 (by rfl) ⟨281957, by rfl⟩ : syracuseStep 375943 = 563915) B563915
theorem B474283 : Blo 330750 474283 := bstep (se 1 (by rfl) ⟨355712, by rfl⟩ : syracuseStep 474283 = 711425) B711425
theorem B507179 : Blo 330750 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B376123 : Blo 330750 376123 := bstep (se 1 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 376123 = 564185) B564185
theorem B474511 : Blo 330750 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B376591 : Blo 330750 376591 := bstep (se 1 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 376591 = 564887) B564887
theorem B1064819 : Blo 330750 1064819 := bstep (se 1 (by rfl) ⟨798614, by rfl⟩ : syracuseStep 1064819 = 1597229) B1597229
theorem B769927 : Blo 330750 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B475399 : Blo 330750 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B2539835 : Blo 330750 2539835 := bstep (se 1 (by rfl) ⟨1904876, by rfl⟩ : syracuseStep 2539835 = 3809753) B3809753
theorem B901523 : Blo 330750 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B508603 : Blo 330750 508603 := bstep (se 1 (by rfl) ⟨381452, by rfl⟩ : syracuseStep 508603 = 762905) B762905
theorem B9126593 : Blo 330750 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B475895 : Blo 330750 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B2409709 : Blo 330750 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B1590617 : Blo 330750 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B673579 : Blo 330750 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B6080305 : Blo 330750 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B1886105 : Blo 330750 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B1689497 : Blo 330750 1689497 := bstep (se 2 (by rfl) ⟨633561, by rfl⟩ : syracuseStep 1689497 = 1267123) B1267123
theorem B903113 : Blo 330750 903113 := bstep (se 2 (by rfl) ⟨338667, by rfl⟩ : syracuseStep 903113 = 677335) B677335
theorem B1264025 : Blo 330750 1264025 := bstep (se 2 (by rfl) ⟨474009, by rfl⟩ : syracuseStep 1264025 = 948019) B948019
theorem B838259 : Blo 330750 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B6409277 : Blo 330750 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B838775 : Blo 330750 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B5787065 : Blo 330750 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B904765 : Blo 330750 904765 := bstep (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) B339287
theorem B708281 : Blo 330750 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B2477873 : Blo 330750 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B16175051 : Blo 330750 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B839767 : Blo 330750 839767 := bstep (se 1 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 839767 = 1259651) B1259651
theorem B708743 : Blo 330750 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B381115 : Blo 330750 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B840071 : Blo 330750 840071 := bstep (se 1 (by rfl) ⟨630053, by rfl⟩ : syracuseStep 840071 = 1260107) B1260107
theorem B1921427 : Blo 330750 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B1692089 : Blo 330750 1692089 := bstep (se 2 (by rfl) ⟨634533, by rfl⟩ : syracuseStep 1692089 = 1269067) B1269067
theorem B840203 : Blo 330750 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B3789341 : Blo 330750 3789341 := bstep (se 3 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 3789341 = 1421003) B1421003
theorem B12833315 : Blo 330750 12833315 := bstep (se 1 (by rfl) ⟨9624986, by rfl⟩ : syracuseStep 12833315 = 19249973) B19249973
theorem B840719 : Blo 330750 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B840851 : Blo 330750 840851 := bstep (se 1 (by rfl) ⟨630638, by rfl⟩ : syracuseStep 840851 = 1261277) B1261277
theorem B709921 : Blo 330750 709921 := bstep (se 2 (by rfl) ⟨266220, by rfl⟩ : syracuseStep 709921 = 532441) B532441
theorem B2840093 : Blo 330750 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B939607 : Blo 330750 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B1693385 : Blo 330750 1693385 := bstep (se 2 (by rfl) ⟨635019, by rfl⟩ : syracuseStep 1693385 = 1270039) B1270039
theorem B1267609 : Blo 330750 1267609 := bstep (se 2 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 1267609 = 950707) B950707
theorem B2840777 : Blo 330750 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B1267913 : Blo 330750 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B841985 : Blo 330750 841985 := bstep (se 2 (by rfl) ⟨315744, by rfl⟩ : syracuseStep 841985 = 631489) B631489
theorem B481609 : Blo 330750 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B2841155 : Blo 330750 2841155 := bstep (se 1 (by rfl) ⟨2130866, by rfl⟩ : syracuseStep 2841155 = 4261733) B4261733
theorem B1890935 : Blo 330750 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B842359 : Blo 330750 842359 := bstep (se 1 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 842359 = 1263539) B1263539
theorem B1891187 : Blo 330750 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B1072007 : Blo 330750 1072007 := bstep (se 1 (by rfl) ⟨804005, by rfl⟩ : syracuseStep 1072007 = 1608011) B1608011
theorem B842795 : Blo 330750 842795 := bstep (se 1 (by rfl) ⟨632096, by rfl⟩ : syracuseStep 842795 = 1264193) B1264193
theorem B1268855 : Blo 330750 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B744839 : Blo 330750 744839 := bstep (se 1 (by rfl) ⟨558629, by rfl⟩ : syracuseStep 744839 = 1117259) B1117259
theorem B1924499 : Blo 330750 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B745019 : Blo 330750 745019 := bstep (se 1 (by rfl) ⟨558764, by rfl⟩ : syracuseStep 745019 = 1117529) B1117529
theorem B745145 : Blo 330750 745145 := bstep (se 2 (by rfl) ⟨279429, by rfl⟩ : syracuseStep 745145 = 558859) B558859
theorem B14868269 : Blo 330750 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B3039065 : Blo 330750 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B843635 : Blo 330750 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B941959 : Blo 330750 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B843655 : Blo 330750 843655 := bstep (se 1 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 843655 = 1265483) B1265483
theorem B745487 : Blo 330750 745487 := bstep (se 1 (by rfl) ⟨559115, by rfl⟩ : syracuseStep 745487 = 1118231) B1118231
theorem B745505 : Blo 330750 745505 := bstep (se 2 (by rfl) ⟨279564, by rfl⟩ : syracuseStep 745505 = 559129) B559129
theorem B647227 : Blo 330750 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B1269827 : Blo 330750 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B843929 : Blo 330750 843929 := bstep (se 2 (by rfl) ⟨316473, by rfl⟩ : syracuseStep 843929 = 632947) B632947
theorem B1794221 : Blo 330750 1794221 := bstep (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) B672833
theorem B942347 : Blo 330750 942347 := bstep (se 1 (by rfl) ⟨706760, by rfl⟩ : syracuseStep 942347 = 1413521) B1413521
theorem B1892645 : Blo 330750 1892645 := bstep (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) B354871
theorem B844091 : Blo 330750 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B745847 : Blo 330750 745847 := bstep (se 1 (by rfl) ⟨559385, by rfl⟩ : syracuseStep 745847 = 1118771) B1118771
theorem B844303 : Blo 330750 844303 := bstep (se 1 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 844303 = 1266455) B1266455
theorem B746027 : Blo 330750 746027 := bstep (se 1 (by rfl) ⟨559520, by rfl⟩ : syracuseStep 746027 = 1119041) B1119041
theorem B1008413 : Blo 330750 1008413 := bstep (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) B378155
theorem B844577 : Blo 330750 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B3629873 : Blo 330750 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B3793715 : Blo 330750 3793715 := bstep (se 1 (by rfl) ⟨2845286, by rfl⟩ : syracuseStep 3793715 = 5690573) B5690573
theorem B746387 : Blo 330750 746387 := bstep (se 1 (by rfl) ⟨559790, by rfl⟩ : syracuseStep 746387 = 1119581) B1119581
theorem B451513 : Blo 330750 451513 := bstep (se 2 (by rfl) ⟨169317, by rfl⟩ : syracuseStep 451513 = 338635) B338635
theorem B746441 : Blo 330750 746441 := bstep (se 2 (by rfl) ⟨279915, by rfl⟩ : syracuseStep 746441 = 559831) B559831
theorem B353423 : Blo 330750 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B1893577 : Blo 330750 1893577 := bstep (se 2 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 1893577 = 1420183) B1420183
theorem B943645 : Blo 330750 943645 := bstep (se 3 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 943645 = 353867) B353867
theorem B353927 : Blo 330750 353927 := bstep (se 1 (by rfl) ⟨265445, by rfl⟩ : syracuseStep 353927 = 530891) B530891
theorem B747143 : Blo 330750 747143 := bstep (se 1 (by rfl) ⟨560357, by rfl⟩ : syracuseStep 747143 = 1120715) B1120715
theorem B419575 : Blo 330750 419575 := bstep (se 1 (by rfl) ⟨314681, by rfl⟩ : syracuseStep 419575 = 629363) B629363
theorem B354055 : Blo 330750 354055 := bstep (se 1 (by rfl) ⟨265541, by rfl⟩ : syracuseStep 354055 = 531083) B531083
theorem B845579 : Blo 330750 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B2844467 : Blo 330750 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B747323 : Blo 330750 747323 := bstep (se 1 (by rfl) ⟨560492, by rfl⟩ : syracuseStep 747323 = 1120985) B1120985
theorem B943987 : Blo 330750 943987 := bstep (se 1 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 943987 = 1415981) B1415981
theorem B14444405 : Blo 330750 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B3073945 : Blo 330750 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B747449 : Blo 330750 747449 := bstep (se 2 (by rfl) ⟨280293, by rfl⟩ : syracuseStep 747449 = 560587) B560587
theorem B419899 : Blo 330750 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B1599689 : Blo 330750 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B1599745 : Blo 330750 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B747791 : Blo 330750 747791 := bstep (se 1 (by rfl) ⟨560843, by rfl⟩ : syracuseStep 747791 = 1121687) B1121687
theorem B747809 : Blo 330750 747809 := bstep (se 2 (by rfl) ⟨280428, by rfl⟩ : syracuseStep 747809 = 560857) B560857
theorem B354619 : Blo 330750 354619 := bstep (se 1 (by rfl) ⟨265964, by rfl⟩ : syracuseStep 354619 = 531929) B531929
theorem B1599859 : Blo 330750 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B846227 : Blo 330750 846227 := bstep (se 1 (by rfl) ⟨634670, by rfl⟩ : syracuseStep 846227 = 1269341) B1269341
theorem B354875 : Blo 330750 354875 := bstep (se 1 (by rfl) ⟨266156, by rfl⟩ : syracuseStep 354875 = 532313) B532313
theorem B2419267 : Blo 330750 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B748151 : Blo 330750 748151 := bstep (se 1 (by rfl) ⟨561113, by rfl⟩ : syracuseStep 748151 = 1122227) B1122227
theorem B846521 : Blo 330750 846521 := bstep (se 2 (by rfl) ⟨317445, by rfl⟩ : syracuseStep 846521 = 634891) B634891
theorem B4025123 : Blo 330750 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B748331 : Blo 330750 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B2845529 : Blo 330750 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B420871 : Blo 330750 420871 := bstep (se 1 (by rfl) ⟨315653, by rfl⟩ : syracuseStep 420871 = 631307) B631307
theorem B748691 : Blo 330750 748691 := bstep (se 1 (by rfl) ⟨561518, by rfl⟩ : syracuseStep 748691 = 1123037) B1123037
theorem B748745 : Blo 330750 748745 := bstep (se 2 (by rfl) ⟨280779, by rfl⟩ : syracuseStep 748745 = 561559) B561559
theorem B847219 : Blo 330750 847219 := bstep (se 1 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 847219 = 1270829) B1270829
theorem B421291 : Blo 330750 421291 := bstep (se 1 (by rfl) ⟨315968, by rfl⟩ : syracuseStep 421291 = 631937) B631937
theorem B421519 : Blo 330750 421519 := bstep (se 1 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 421519 = 632279) B632279
theorem B454391 : Blo 330750 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B749447 : Blo 330750 749447 := bstep (se 1 (by rfl) ⟨562085, by rfl⟩ : syracuseStep 749447 = 1124171) B1124171
theorem B2518937 : Blo 330750 2518937 := bstep (se 2 (by rfl) ⟨944601, by rfl⟩ : syracuseStep 2518937 = 1889203) B1889203
theorem B749627 : Blo 330750 749627 := bstep (se 1 (by rfl) ⟨562220, by rfl⟩ : syracuseStep 749627 = 1124441) B1124441
theorem B749753 : Blo 330750 749753 := bstep (se 2 (by rfl) ⟨281157, by rfl⟩ : syracuseStep 749753 = 562315) B562315
theorem B422263 : Blo 330750 422263 := bstep (se 1 (by rfl) ⟨316697, by rfl⟩ : syracuseStep 422263 = 633395) B633395
theorem B1012121 : Blo 330750 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B750095 : Blo 330750 750095 := bstep (se 1 (by rfl) ⟨562571, by rfl⟩ : syracuseStep 750095 = 1125143) B1125143
theorem B946721 : Blo 330750 946721 := bstep (se 2 (by rfl) ⟨355020, by rfl⟩ : syracuseStep 946721 = 710041) B710041
theorem B750113 : Blo 330750 750113 := bstep (se 2 (by rfl) ⟨281292, by rfl⟩ : syracuseStep 750113 = 562585) B562585
theorem B946835 : Blo 330750 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B422587 : Blo 330750 422587 := bstep (se 1 (by rfl) ⟨316940, by rfl⟩ : syracuseStep 422587 = 633881) B633881
theorem B5731033 : Blo 330750 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B750455 : Blo 330750 750455 := bstep (se 1 (by rfl) ⟨562841, by rfl⟩ : syracuseStep 750455 = 1125683) B1125683
theorem B4813829 : Blo 330750 4813829 := bstep (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) B902593
theorem B750635 : Blo 330750 750635 := bstep (se 1 (by rfl) ⟨562976, by rfl⟩ : syracuseStep 750635 = 1125953) B1125953
theorem B423083 : Blo 330750 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B750995 : Blo 330750 750995 := bstep (se 1 (by rfl) ⟨563246, by rfl⟩ : syracuseStep 750995 = 1126493) B1126493
theorem B947609 : Blo 330750 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B751049 : Blo 330750 751049 := bstep (se 2 (by rfl) ⟨281643, by rfl⟩ : syracuseStep 751049 = 563287) B563287
theorem B1144439 : Blo 330750 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B423559 : Blo 330750 423559 := bstep (se 1 (by rfl) ⟨317669, by rfl⟩ : syracuseStep 423559 = 635339) B635339
theorem B2029349 : Blo 330750 2029349 := bstep (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) B380503
theorem B2520881 : Blo 330750 2520881 := bstep (se 2 (by rfl) ⟨945330, by rfl⟩ : syracuseStep 2520881 = 1890661) B1890661
theorem B1603475 : Blo 330750 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B1275857 : Blo 330750 1275857 := bstep (se 2 (by rfl) ⟨478446, by rfl⟩ : syracuseStep 1275857 = 956893) B956893
theorem B751751 : Blo 330750 751751 := bstep (se 1 (by rfl) ⟨563813, by rfl⟩ : syracuseStep 751751 = 1127627) B1127627
theorem B751931 : Blo 330750 751931 := bstep (se 1 (by rfl) ⟨563948, by rfl⟩ : syracuseStep 751931 = 1127897) B1127897
theorem B752057 : Blo 330750 752057 := bstep (se 2 (by rfl) ⟨282021, by rfl⟩ : syracuseStep 752057 = 564043) B564043
theorem B850447 : Blo 330750 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B1833673 : Blo 330750 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B424711 : Blo 330750 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B752399 : Blo 330750 752399 := bstep (se 1 (by rfl) ⟨564299, by rfl⟩ : syracuseStep 752399 = 1128599) B1128599
theorem B752417 : Blo 330750 752417 := bstep (se 2 (by rfl) ⟨282156, by rfl⟩ : syracuseStep 752417 = 564313) B564313
theorem B359311 : Blo 330750 359311 := bstep (se 1 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 359311 = 538967) B538967
theorem B1899409 : Blo 330750 1899409 := bstep (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) B1424557
theorem B949249 : Blo 330750 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B6454333 : Blo 330750 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B1014871 : Blo 330750 1014871 := bstep (se 1 (by rfl) ⟨761153, by rfl⟩ : syracuseStep 1014871 = 1522307) B1522307
theorem B752759 : Blo 330750 752759 := bstep (se 1 (by rfl) ⟨564569, by rfl⟩ : syracuseStep 752759 = 1129139) B1129139
theorem B752939 : Blo 330750 752939 := bstep (se 1 (by rfl) ⟨564704, by rfl⟩ : syracuseStep 752939 = 1129409) B1129409
theorem B949819 : Blo 330750 949819 := bstep (se 1 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 949819 = 1424729) B1424729
theorem B2032613 : Blo 330750 2032613 := bstep (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) B381115
theorem B2524769 : Blo 330750 2524769 := bstep (se 2 (by rfl) ⟨946788, by rfl⟩ : syracuseStep 2524769 = 1893577) B1893577
theorem B3212945 : Blo 330750 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B558839 : Blo 330750 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B1902599 : Blo 330750 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B559183 : Blo 330750 559183 := bstep (se 1 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 559183 = 838775) B838775
theorem B559433 : Blo 330750 559433 := bstep (se 2 (by rfl) ⟨209787, by rfl⟩ : syracuseStep 559433 = 419575) B419575
theorem B1116503 : Blo 330750 1116503 := bstep (se 1 (by rfl) ⟨837377, by rfl⟩ : syracuseStep 1116503 = 1674755) B1674755
theorem B854491 : Blo 330750 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B4098593 : Blo 330750 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B10783367 : Blo 330750 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B5376689 : Blo 330750 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B559865 : Blo 330750 559865 := bstep (se 2 (by rfl) ⟨209949, by rfl⟩ : syracuseStep 559865 = 419899) B419899
theorem B560047 : Blo 330750 560047 := bstep (se 1 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 560047 = 840071) B840071
theorem B1280951 : Blo 330750 1280951 := bstep (se 1 (by rfl) ⟨960713, by rfl⟩ : syracuseStep 1280951 = 1921427) B1921427
theorem B2132993 : Blo 330750 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B560135 : Blo 330750 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B2526227 : Blo 330750 2526227 := bstep (se 1 (by rfl) ⟨1894670, by rfl⟩ : syracuseStep 2526227 = 3789341) B3789341
theorem B8555543 : Blo 330750 8555543 := bstep (se 1 (by rfl) ⟨6416657, by rfl⟩ : syracuseStep 8555543 = 12833315) B12833315
theorem B330791 : Blo 330750 330791 := bstep (se 1 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 330791 = 496187) B496187
theorem B756793 : Blo 330750 756793 := bstep (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) B567595
theorem B330831 : Blo 330750 330831 := bstep (se 1 (by rfl) ⟨248123, by rfl⟩ : syracuseStep 330831 = 496247) B496247
theorem B330847 : Blo 330750 330847 := bstep (se 1 (by rfl) ⟨248135, by rfl⟩ : syracuseStep 330847 = 496271) B496271
theorem B330875 : Blo 330750 330875 := bstep (se 1 (by rfl) ⟨248156, by rfl⟩ : syracuseStep 330875 = 496313) B496313
theorem B2133145 : Blo 330750 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B330927 : Blo 330750 330927 := bstep (se 1 (by rfl) ⟨248195, by rfl⟩ : syracuseStep 330927 = 496391) B496391
theorem B330951 : Blo 330750 330951 := bstep (se 1 (by rfl) ⟨248213, by rfl⟩ : syracuseStep 330951 = 496427) B496427
theorem B330971 : Blo 330750 330971 := bstep (se 1 (by rfl) ⟨248228, by rfl⟩ : syracuseStep 330971 = 496457) B496457
theorem B331047 : Blo 330750 331047 := bstep (se 1 (by rfl) ⟨248285, by rfl⟩ : syracuseStep 331047 = 496571) B496571
theorem B331087 : Blo 330750 331087 := bstep (se 1 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 331087 = 496631) B496631
theorem B331103 : Blo 330750 331103 := bstep (se 1 (by rfl) ⟨248327, by rfl⟩ : syracuseStep 331103 = 496655) B496655
theorem B560479 : Blo 330750 560479 := bstep (se 1 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 560479 = 840719) B840719
theorem B331131 : Blo 330750 331131 := bstep (se 1 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 331131 = 496697) B496697
theorem B1117583 : Blo 330750 1117583 := bstep (se 1 (by rfl) ⟨838187, by rfl⟩ : syracuseStep 1117583 = 1676375) B1676375
theorem B331183 : Blo 330750 331183 := bstep (se 1 (by rfl) ⟨248387, by rfl⟩ : syracuseStep 331183 = 496775) B496775
theorem B560567 : Blo 330750 560567 := bstep (se 1 (by rfl) ⟨420425, by rfl⟩ : syracuseStep 560567 = 840851) B840851
theorem B331207 : Blo 330750 331207 := bstep (se 1 (by rfl) ⟨248405, by rfl⟩ : syracuseStep 331207 = 496811) B496811
theorem B331227 : Blo 330750 331227 := bstep (se 1 (by rfl) ⟨248420, by rfl⟩ : syracuseStep 331227 = 496841) B496841
theorem B331303 : Blo 330750 331303 := bstep (se 1 (by rfl) ⟨248477, by rfl⟩ : syracuseStep 331303 = 496955) B496955
theorem B331343 : Blo 330750 331343 := bstep (se 1 (by rfl) ⟨248507, by rfl⟩ : syracuseStep 331343 = 497015) B497015
theorem B331359 : Blo 330750 331359 := bstep (se 1 (by rfl) ⟨248519, by rfl⟩ : syracuseStep 331359 = 497039) B497039
theorem B331387 : Blo 330750 331387 := bstep (se 1 (by rfl) ⟨248540, by rfl⟩ : syracuseStep 331387 = 497081) B497081
theorem B331439 : Blo 330750 331439 := bstep (se 1 (by rfl) ⟨248579, by rfl⟩ : syracuseStep 331439 = 497159) B497159
theorem B331463 : Blo 330750 331463 := bstep (se 1 (by rfl) ⟨248597, by rfl⟩ : syracuseStep 331463 = 497195) B497195
theorem B1117907 : Blo 330750 1117907 := bstep (se 1 (by rfl) ⟨838430, by rfl⟩ : syracuseStep 1117907 = 1676861) B1676861
theorem B331483 : Blo 330750 331483 := bstep (se 1 (by rfl) ⟨248612, by rfl⟩ : syracuseStep 331483 = 497225) B497225
theorem B331559 : Blo 330750 331559 := bstep (se 1 (by rfl) ⟨248669, by rfl⟩ : syracuseStep 331559 = 497339) B497339
theorem B331599 : Blo 330750 331599 := bstep (se 1 (by rfl) ⟨248699, by rfl⟩ : syracuseStep 331599 = 497399) B497399
theorem B331615 : Blo 330750 331615 := bstep (se 1 (by rfl) ⟨248711, by rfl⟩ : syracuseStep 331615 = 497423) B497423
theorem B331643 : Blo 330750 331643 := bstep (se 1 (by rfl) ⟨248732, by rfl⟩ : syracuseStep 331643 = 497465) B497465
theorem B6426499 : Blo 330750 6426499 := bstep (se 1 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 6426499 = 9639749) B9639749
theorem B331695 : Blo 330750 331695 := bstep (se 1 (by rfl) ⟨248771, by rfl⟩ : syracuseStep 331695 = 497543) B497543
theorem B331719 : Blo 330750 331719 := bstep (se 1 (by rfl) ⟨248789, by rfl⟩ : syracuseStep 331719 = 497579) B497579
theorem B331739 : Blo 330750 331739 := bstep (se 1 (by rfl) ⟨248804, by rfl⟩ : syracuseStep 331739 = 497609) B497609
theorem B561161 : Blo 330750 561161 := bstep (se 2 (by rfl) ⟨210435, by rfl⟩ : syracuseStep 561161 = 420871) B420871
theorem B331815 : Blo 330750 331815 := bstep (se 1 (by rfl) ⟨248861, by rfl⟩ : syracuseStep 331815 = 497723) B497723
theorem B331855 : Blo 330750 331855 := bstep (se 1 (by rfl) ⟨248891, by rfl⟩ : syracuseStep 331855 = 497783) B497783
theorem B331871 : Blo 330750 331871 := bstep (se 1 (by rfl) ⟨248903, by rfl⟩ : syracuseStep 331871 = 497807) B497807
theorem B331899 : Blo 330750 331899 := bstep (se 1 (by rfl) ⟨248924, by rfl⟩ : syracuseStep 331899 = 497849) B497849
theorem B561323 : Blo 330750 561323 := bstep (se 1 (by rfl) ⟨420992, by rfl⟩ : syracuseStep 561323 = 841985) B841985
theorem B331951 : Blo 330750 331951 := bstep (se 1 (by rfl) ⟨248963, by rfl⟩ : syracuseStep 331951 = 497927) B497927
theorem B3281075 : Blo 330750 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B331975 : Blo 330750 331975 := bstep (se 1 (by rfl) ⟨248981, by rfl⟩ : syracuseStep 331975 = 497963) B497963
theorem B331995 : Blo 330750 331995 := bstep (se 1 (by rfl) ⟨248996, by rfl⟩ : syracuseStep 331995 = 497993) B497993
theorem B332071 : Blo 330750 332071 := bstep (se 1 (by rfl) ⟨249053, by rfl⟩ : syracuseStep 332071 = 498107) B498107
theorem B1511741 : Blo 330750 1511741 := bstep (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) B566903
theorem B332111 : Blo 330750 332111 := bstep (se 1 (by rfl) ⟨249083, by rfl⟩ : syracuseStep 332111 = 498167) B498167
theorem B332127 : Blo 330750 332127 := bstep (se 1 (by rfl) ⟨249095, by rfl⟩ : syracuseStep 332127 = 498191) B498191
theorem B332155 : Blo 330750 332155 := bstep (se 1 (by rfl) ⟨249116, by rfl⟩ : syracuseStep 332155 = 498233) B498233
theorem B332207 : Blo 330750 332207 := bstep (se 1 (by rfl) ⟨249155, by rfl⟩ : syracuseStep 332207 = 498311) B498311
theorem B332231 : Blo 330750 332231 := bstep (se 1 (by rfl) ⟨249173, by rfl⟩ : syracuseStep 332231 = 498347) B498347
theorem B332251 : Blo 330750 332251 := bstep (se 1 (by rfl) ⟨249188, by rfl⟩ : syracuseStep 332251 = 498377) B498377
theorem B332327 : Blo 330750 332327 := bstep (se 1 (by rfl) ⟨249245, by rfl⟩ : syracuseStep 332327 = 498491) B498491
theorem B561721 : Blo 330750 561721 := bstep (se 2 (by rfl) ⟨210645, by rfl⟩ : syracuseStep 561721 = 421291) B421291
theorem B332367 : Blo 330750 332367 := bstep (se 1 (by rfl) ⟨249275, by rfl⟩ : syracuseStep 332367 = 498551) B498551
theorem B332383 : Blo 330750 332383 := bstep (se 1 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 332383 = 498575) B498575
theorem B332411 : Blo 330750 332411 := bstep (se 1 (by rfl) ⟨249308, by rfl⟩ : syracuseStep 332411 = 498617) B498617
theorem B2691719 : Blo 330750 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B332463 : Blo 330750 332463 := bstep (se 1 (by rfl) ⟨249347, by rfl⟩ : syracuseStep 332463 = 498695) B498695
theorem B332487 : Blo 330750 332487 := bstep (se 1 (by rfl) ⟨249365, by rfl⟩ : syracuseStep 332487 = 498731) B498731
theorem B561863 : Blo 330750 561863 := bstep (se 1 (by rfl) ⟨421397, by rfl⟩ : syracuseStep 561863 = 842795) B842795
theorem B332507 : Blo 330750 332507 := bstep (se 1 (by rfl) ⟨249380, by rfl⟩ : syracuseStep 332507 = 498761) B498761
theorem B332583 : Blo 330750 332583 := bstep (se 1 (by rfl) ⟨249437, by rfl⟩ : syracuseStep 332583 = 498875) B498875
theorem B332623 : Blo 330750 332623 := bstep (se 1 (by rfl) ⟨249467, by rfl⟩ : syracuseStep 332623 = 498935) B498935
theorem B332639 : Blo 330750 332639 := bstep (se 1 (by rfl) ⟨249479, by rfl⟩ : syracuseStep 332639 = 498959) B498959
theorem B562025 : Blo 330750 562025 := bstep (se 2 (by rfl) ⟨210759, by rfl⟩ : syracuseStep 562025 = 421519) B421519
theorem B1905515 : Blo 330750 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B1119095 : Blo 330750 1119095 := bstep (se 1 (by rfl) ⟨839321, by rfl⟩ : syracuseStep 1119095 = 1678643) B1678643
theorem B332667 : Blo 330750 332667 := bstep (se 1 (by rfl) ⟨249500, by rfl⟩ : syracuseStep 332667 = 499001) B499001
theorem B496559 : Blo 330750 496559 := bstep (se 1 (by rfl) ⟨372419, by rfl⟩ : syracuseStep 496559 = 744839) B744839
theorem B332719 : Blo 330750 332719 := bstep (se 1 (by rfl) ⟨249539, by rfl⟩ : syracuseStep 332719 = 499079) B499079
theorem B1282999 : Blo 330750 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B332743 : Blo 330750 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B332763 : Blo 330750 332763 := bstep (se 1 (by rfl) ⟨249572, by rfl⟩ : syracuseStep 332763 = 499145) B499145
theorem B2626561 : Blo 330750 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B496649 : Blo 330750 496649 := bstep (se 2 (by rfl) ⟨186243, by rfl⟩ : syracuseStep 496649 = 372487) B372487
theorem B2692115 : Blo 330750 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B496679 : Blo 330750 496679 := bstep (se 1 (by rfl) ⟨372509, by rfl⟩ : syracuseStep 496679 = 745019) B745019
theorem B332839 : Blo 330750 332839 := bstep (se 1 (by rfl) ⟨249629, by rfl⟩ : syracuseStep 332839 = 499259) B499259
theorem B1119311 : Blo 330750 1119311 := bstep (se 1 (by rfl) ⟨839483, by rfl⟩ : syracuseStep 1119311 = 1678967) B1678967
theorem B332879 : Blo 330750 332879 := bstep (se 1 (by rfl) ⟨249659, by rfl⟩ : syracuseStep 332879 = 499319) B499319
theorem B332895 : Blo 330750 332895 := bstep (se 1 (by rfl) ⟨249671, by rfl⟩ : syracuseStep 332895 = 499343) B499343
theorem B496763 : Blo 330750 496763 := bstep (se 1 (by rfl) ⟨372572, by rfl⟩ : syracuseStep 496763 = 745145) B745145
theorem B332923 : Blo 330750 332923 := bstep (se 1 (by rfl) ⟨249692, by rfl⟩ : syracuseStep 332923 = 499385) B499385
theorem B332975 : Blo 330750 332975 := bstep (se 1 (by rfl) ⟨249731, by rfl⟩ : syracuseStep 332975 = 499463) B499463
theorem B332999 : Blo 330750 332999 := bstep (se 1 (by rfl) ⟨249749, by rfl⟩ : syracuseStep 332999 = 499499) B499499
theorem B333019 : Blo 330750 333019 := bstep (se 1 (by rfl) ⟨249764, by rfl⟩ : syracuseStep 333019 = 499529) B499529
theorem B562423 : Blo 330750 562423 := bstep (se 1 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 562423 = 843635) B843635
theorem B496889 : Blo 330750 496889 := bstep (se 2 (by rfl) ⟨186333, by rfl⟩ : syracuseStep 496889 = 372667) B372667
theorem B333095 : Blo 330750 333095 := bstep (se 1 (by rfl) ⟨249821, by rfl⟩ : syracuseStep 333095 = 499643) B499643
theorem B333135 : Blo 330750 333135 := bstep (se 1 (by rfl) ⟨249851, by rfl⟩ : syracuseStep 333135 = 499703) B499703
theorem B496991 : Blo 330750 496991 := bstep (se 1 (by rfl) ⟨372743, by rfl⟩ : syracuseStep 496991 = 745487) B745487
theorem B333151 : Blo 330750 333151 := bstep (se 1 (by rfl) ⟨249863, by rfl⟩ : syracuseStep 333151 = 499727) B499727
theorem B497003 : Blo 330750 497003 := bstep (se 1 (by rfl) ⟨372752, by rfl⟩ : syracuseStep 497003 = 745505) B745505
theorem B333179 : Blo 330750 333179 := bstep (se 1 (by rfl) ⟨249884, by rfl⟩ : syracuseStep 333179 = 499769) B499769
theorem B8131985 : Blo 330750 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B333231 : Blo 330750 333231 := bstep (se 1 (by rfl) ⟨249923, by rfl⟩ : syracuseStep 333231 = 499847) B499847
theorem B562619 : Blo 330750 562619 := bstep (se 1 (by rfl) ⟨421964, by rfl⟩ : syracuseStep 562619 = 843929) B843929
theorem B333255 : Blo 330750 333255 := bstep (se 1 (by rfl) ⟨249941, by rfl⟩ : syracuseStep 333255 = 499883) B499883
theorem B1119689 : Blo 330750 1119689 := bstep (se 2 (by rfl) ⟨419883, by rfl⟩ : syracuseStep 1119689 = 839767) B839767
theorem B333275 : Blo 330750 333275 := bstep (se 1 (by rfl) ⟨249956, by rfl⟩ : syracuseStep 333275 = 499913) B499913
theorem B628231 : Blo 330750 628231 := bstep (se 1 (by rfl) ⟨471173, by rfl⟩ : syracuseStep 628231 = 942347) B942347
theorem B333351 : Blo 330750 333351 := bstep (se 1 (by rfl) ⟨250013, by rfl⟩ : syracuseStep 333351 = 500027) B500027
theorem B562727 : Blo 330750 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B497231 : Blo 330750 497231 := bstep (se 1 (by rfl) ⟨372923, by rfl⟩ : syracuseStep 497231 = 745847) B745847
theorem B333391 : Blo 330750 333391 := bstep (se 1 (by rfl) ⟨250043, by rfl⟩ : syracuseStep 333391 = 500087) B500087
theorem B333407 : Blo 330750 333407 := bstep (se 1 (by rfl) ⟨250055, by rfl⟩ : syracuseStep 333407 = 500111) B500111
theorem B333435 : Blo 330750 333435 := bstep (se 1 (by rfl) ⟨250076, by rfl⟩ : syracuseStep 333435 = 500153) B500153
theorem B333487 : Blo 330750 333487 := bstep (se 1 (by rfl) ⟨250115, by rfl⟩ : syracuseStep 333487 = 500231) B500231
theorem B497351 : Blo 330750 497351 := bstep (se 1 (by rfl) ⟨373013, by rfl⟩ : syracuseStep 497351 = 746027) B746027
theorem B333511 : Blo 330750 333511 := bstep (se 1 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 333511 = 500267) B500267
theorem B1119959 : Blo 330750 1119959 := bstep (se 1 (by rfl) ⟨839969, by rfl⟩ : syracuseStep 1119959 = 1679939) B1679939
theorem B333531 : Blo 330750 333531 := bstep (se 1 (by rfl) ⟨250148, by rfl⟩ : syracuseStep 333531 = 500297) B500297
theorem B333607 : Blo 330750 333607 := bstep (se 1 (by rfl) ⟨250205, by rfl⟩ : syracuseStep 333607 = 500411) B500411
theorem B563017 : Blo 330750 563017 := bstep (se 2 (by rfl) ⟨211131, by rfl⟩ : syracuseStep 563017 = 422263) B422263
theorem B333647 : Blo 330750 333647 := bstep (se 1 (by rfl) ⟨250235, by rfl⟩ : syracuseStep 333647 = 500471) B500471
theorem B333663 : Blo 330750 333663 := bstep (se 1 (by rfl) ⟨250247, by rfl⟩ : syracuseStep 333663 = 500495) B500495
theorem B497513 : Blo 330750 497513 := bstep (se 2 (by rfl) ⟨186567, by rfl⟩ : syracuseStep 497513 = 373135) B373135
theorem B563051 : Blo 330750 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B2529143 : Blo 330750 2529143 := bstep (se 1 (by rfl) ⟨1896857, by rfl⟩ : syracuseStep 2529143 = 3793715) B3793715
theorem B333691 : Blo 330750 333691 := bstep (se 1 (by rfl) ⟨250268, by rfl⟩ : syracuseStep 333691 = 500537) B500537
theorem B1120175 : Blo 330750 1120175 := bstep (se 1 (by rfl) ⟨840131, by rfl⟩ : syracuseStep 1120175 = 1680263) B1680263
theorem B333743 : Blo 330750 333743 := bstep (se 1 (by rfl) ⟨250307, by rfl⟩ : syracuseStep 333743 = 500615) B500615
theorem B497591 : Blo 330750 497591 := bstep (se 1 (by rfl) ⟨373193, by rfl⟩ : syracuseStep 497591 = 746387) B746387
theorem B333767 : Blo 330750 333767 := bstep (se 1 (by rfl) ⟨250325, by rfl⟩ : syracuseStep 333767 = 500651) B500651
theorem B497627 : Blo 330750 497627 := bstep (se 1 (by rfl) ⟨373220, by rfl⟩ : syracuseStep 497627 = 746441) B746441
theorem B333787 : Blo 330750 333787 := bstep (se 1 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 333787 = 500681) B500681
theorem B333863 : Blo 330750 333863 := bstep (se 1 (by rfl) ⟨250397, by rfl⟩ : syracuseStep 333863 = 500795) B500795
theorem B628793 : Blo 330750 628793 := bstep (se 2 (by rfl) ⟨235797, by rfl⟩ : syracuseStep 628793 = 471595) B471595
theorem B333903 : Blo 330750 333903 := bstep (se 1 (by rfl) ⟨250427, by rfl⟩ : syracuseStep 333903 = 500855) B500855
theorem B333919 : Blo 330750 333919 := bstep (se 1 (by rfl) ⟨250439, by rfl⟩ : syracuseStep 333919 = 500879) B500879
theorem B333947 : Blo 330750 333947 := bstep (se 1 (by rfl) ⟨250460, by rfl⟩ : syracuseStep 333947 = 500921) B500921
theorem B333999 : Blo 330750 333999 := bstep (se 1 (by rfl) ⟨250499, by rfl⟩ : syracuseStep 333999 = 500999) B500999
theorem B334023 : Blo 330750 334023 := bstep (se 1 (by rfl) ⟨250517, by rfl⟩ : syracuseStep 334023 = 501035) B501035
theorem B334043 : Blo 330750 334043 := bstep (se 1 (by rfl) ⟨250532, by rfl⟩ : syracuseStep 334043 = 501065) B501065
theorem B563449 : Blo 330750 563449 := bstep (se 2 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 563449 = 422587) B422587
theorem B7641377 : Blo 330750 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B334119 : Blo 330750 334119 := bstep (se 1 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 334119 = 501179) B501179
theorem B334159 : Blo 330750 334159 := bstep (se 1 (by rfl) ⟨250619, by rfl⟩ : syracuseStep 334159 = 501239) B501239
theorem B334175 : Blo 330750 334175 := bstep (se 1 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 334175 = 501263) B501263
theorem B334203 : Blo 330750 334203 := bstep (se 1 (by rfl) ⟨250652, by rfl⟩ : syracuseStep 334203 = 501305) B501305
theorem B498095 : Blo 330750 498095 := bstep (se 1 (by rfl) ⟨373571, by rfl⟩ : syracuseStep 498095 = 747143) B747143
theorem B334255 : Blo 330750 334255 := bstep (se 1 (by rfl) ⟨250691, by rfl⟩ : syracuseStep 334255 = 501383) B501383
theorem B334279 : Blo 330750 334279 := bstep (se 1 (by rfl) ⟨250709, by rfl⟩ : syracuseStep 334279 = 501419) B501419
theorem B334299 : Blo 330750 334299 := bstep (se 1 (by rfl) ⟨250724, by rfl⟩ : syracuseStep 334299 = 501449) B501449
theorem B563719 : Blo 330750 563719 := bstep (se 1 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 563719 = 845579) B845579
theorem B1677833 : Blo 330750 1677833 := bstep (se 2 (by rfl) ⟨629187, by rfl⟩ : syracuseStep 1677833 = 1258375) B1258375
theorem B498185 : Blo 330750 498185 := bstep (se 2 (by rfl) ⟨186819, by rfl⟩ : syracuseStep 498185 = 373639) B373639
theorem B498215 : Blo 330750 498215 := bstep (se 1 (by rfl) ⟨373661, by rfl⟩ : syracuseStep 498215 = 747323) B747323
theorem B334375 : Blo 330750 334375 := bstep (se 1 (by rfl) ⟨250781, by rfl⟩ : syracuseStep 334375 = 501563) B501563
theorem B334415 : Blo 330750 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B334431 : Blo 330750 334431 := bstep (se 1 (by rfl) ⟨250823, by rfl⟩ : syracuseStep 334431 = 501647) B501647
theorem B596603 : Blo 330750 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B498299 : Blo 330750 498299 := bstep (se 1 (by rfl) ⟨373724, by rfl⟩ : syracuseStep 498299 = 747449) B747449
theorem B334459 : Blo 330750 334459 := bstep (se 1 (by rfl) ⟨250844, by rfl⟩ : syracuseStep 334459 = 501689) B501689
theorem B334511 : Blo 330750 334511 := bstep (se 1 (by rfl) ⟨250883, by rfl⟩ : syracuseStep 334511 = 501767) B501767
theorem B334535 : Blo 330750 334535 := bstep (se 1 (by rfl) ⟨250901, by rfl⟩ : syracuseStep 334535 = 501803) B501803
theorem B334555 : Blo 330750 334555 := bstep (se 1 (by rfl) ⟨250916, by rfl⟩ : syracuseStep 334555 = 501833) B501833
theorem B498425 : Blo 330750 498425 := bstep (se 2 (by rfl) ⟨186909, by rfl⟩ : syracuseStep 498425 = 373819) B373819
theorem B334631 : Blo 330750 334631 := bstep (se 1 (by rfl) ⟨250973, by rfl⟩ : syracuseStep 334631 = 501947) B501947
theorem B334671 : Blo 330750 334671 := bstep (se 1 (by rfl) ⟨251003, by rfl⟩ : syracuseStep 334671 = 502007) B502007
theorem B498527 : Blo 330750 498527 := bstep (se 1 (by rfl) ⟨373895, by rfl⟩ : syracuseStep 498527 = 747791) B747791
theorem B334687 : Blo 330750 334687 := bstep (se 1 (by rfl) ⟨251015, by rfl⟩ : syracuseStep 334687 = 502031) B502031
theorem B498539 : Blo 330750 498539 := bstep (se 1 (by rfl) ⟨373904, by rfl⟩ : syracuseStep 498539 = 747809) B747809
theorem B334715 : Blo 330750 334715 := bstep (se 1 (by rfl) ⟨251036, by rfl⟩ : syracuseStep 334715 = 502073) B502073
theorem B564151 : Blo 330750 564151 := bstep (se 1 (by rfl) ⟨423113, by rfl⟩ : syracuseStep 564151 = 846227) B846227
theorem B498767 : Blo 330750 498767 := bstep (se 1 (by rfl) ⟨374075, by rfl⟩ : syracuseStep 498767 = 748151) B748151
theorem B564347 : Blo 330750 564347 := bstep (se 1 (by rfl) ⟨423260, by rfl⟩ : syracuseStep 564347 = 846521) B846521
theorem B498887 : Blo 330750 498887 := bstep (se 1 (by rfl) ⟨374165, by rfl⟩ : syracuseStep 498887 = 748331) B748331
theorem B499049 : Blo 330750 499049 := bstep (se 2 (by rfl) ⟨187143, by rfl⟩ : syracuseStep 499049 = 374287) B374287
theorem B499127 : Blo 330750 499127 := bstep (se 1 (by rfl) ⟨374345, by rfl⟩ : syracuseStep 499127 = 748691) B748691
theorem B499163 : Blo 330750 499163 := bstep (se 1 (by rfl) ⟨374372, by rfl⟩ : syracuseStep 499163 = 748745) B748745
theorem B630281 : Blo 330750 630281 := bstep (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) B472711
theorem B564745 : Blo 330750 564745 := bstep (se 2 (by rfl) ⟨211779, by rfl⟩ : syracuseStep 564745 = 423559) B423559
theorem B499631 : Blo 330750 499631 := bstep (se 1 (by rfl) ⟨374723, by rfl⟩ : syracuseStep 499631 = 749447) B749447
theorem B1679291 : Blo 330750 1679291 := bstep (se 1 (by rfl) ⟨1259468, by rfl⟩ : syracuseStep 1679291 = 2518937) B2518937
theorem B499721 : Blo 330750 499721 := bstep (se 2 (by rfl) ⟨187395, by rfl⟩ : syracuseStep 499721 = 374791) B374791
theorem B499751 : Blo 330750 499751 := bstep (se 1 (by rfl) ⟨374813, by rfl⟩ : syracuseStep 499751 = 749627) B749627
theorem B1417297 : Blo 330750 1417297 := bstep (se 2 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 1417297 = 1062973) B1062973
theorem B335995 : Blo 330750 335995 := bstep (se 1 (by rfl) ⟨251996, by rfl⟩ : syracuseStep 335995 = 503993) B503993
theorem B499835 : Blo 330750 499835 := bstep (se 1 (by rfl) ⟨374876, by rfl⟩ : syracuseStep 499835 = 749753) B749753
theorem B16425109 : Blo 330750 16425109 := bstep (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) B769927
theorem B1122551 : Blo 330750 1122551 := bstep (se 1 (by rfl) ⟨841913, by rfl⟩ : syracuseStep 1122551 = 1683827) B1683827
theorem B499961 : Blo 330750 499961 := bstep (se 2 (by rfl) ⟨187485, by rfl⟩ : syracuseStep 499961 = 374971) B374971
theorem B500063 : Blo 330750 500063 := bstep (se 1 (by rfl) ⟨375047, by rfl⟩ : syracuseStep 500063 = 750095) B750095
theorem B631147 : Blo 330750 631147 := bstep (se 1 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 631147 = 946721) B946721
theorem B500075 : Blo 330750 500075 := bstep (se 1 (by rfl) ⟨375056, by rfl⟩ : syracuseStep 500075 = 750113) B750113
theorem B631223 : Blo 330750 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B1122875 : Blo 330750 1122875 := bstep (se 1 (by rfl) ⟨842156, by rfl⟩ : syracuseStep 1122875 = 1684313) B1684313
theorem B500303 : Blo 330750 500303 := bstep (se 1 (by rfl) ⟨375227, by rfl⟩ : syracuseStep 500303 = 750455) B750455
theorem B10756759 : Blo 330750 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B336559 : Blo 330750 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B500423 : Blo 330750 500423 := bstep (se 1 (by rfl) ⟨375317, by rfl⟩ : syracuseStep 500423 = 750635) B750635
theorem B1123145 : Blo 330750 1123145 := bstep (se 2 (by rfl) ⟨421179, by rfl⟩ : syracuseStep 1123145 = 842359) B842359
theorem B500585 : Blo 330750 500585 := bstep (se 2 (by rfl) ⟨187719, by rfl⟩ : syracuseStep 500585 = 375439) B375439
theorem B500663 : Blo 330750 500663 := bstep (se 1 (by rfl) ⟨375497, by rfl⟩ : syracuseStep 500663 = 750995) B750995
theorem B631739 : Blo 330750 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B500699 : Blo 330750 500699 := bstep (se 1 (by rfl) ⟨375524, by rfl⟩ : syracuseStep 500699 = 751049) B751049
theorem B566281 : Blo 330750 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B762959 : Blo 330750 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B2532545 : Blo 330750 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B1352899 : Blo 330750 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B1680587 : Blo 330750 1680587 := bstep (se 1 (by rfl) ⟨1260440, by rfl⟩ : syracuseStep 1680587 = 2520881) B2520881
theorem B796009 : Blo 330750 796009 := bstep (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) B597007
theorem B632225 : Blo 330750 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B501167 : Blo 330750 501167 := bstep (se 1 (by rfl) ⟨375875, by rfl⟩ : syracuseStep 501167 = 751751) B751751
theorem B533947 : Blo 330750 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B1353161 : Blo 330750 1353161 := bstep (se 2 (by rfl) ⟨507435, by rfl⟩ : syracuseStep 1353161 = 1014871) B1014871
theorem B501257 : Blo 330750 501257 := bstep (se 2 (by rfl) ⟨187971, by rfl⟩ : syracuseStep 501257 = 375943) B375943
theorem B501287 : Blo 330750 501287 := bstep (se 1 (by rfl) ⟨375965, by rfl⟩ : syracuseStep 501287 = 751931) B751931
theorem B632377 : Blo 330750 632377 := bstep (se 2 (by rfl) ⟨237141, by rfl⟩ : syracuseStep 632377 = 474283) B474283
theorem B501371 : Blo 330750 501371 := bstep (se 1 (by rfl) ⟨376028, by rfl⟩ : syracuseStep 501371 = 752057) B752057
theorem B501497 : Blo 330750 501497 := bstep (se 2 (by rfl) ⟨188061, by rfl⟩ : syracuseStep 501497 = 376123) B376123
theorem B501599 : Blo 330750 501599 := bstep (se 1 (by rfl) ⟨376199, by rfl⟩ : syracuseStep 501599 = 752399) B752399
theorem B632681 : Blo 330750 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B501611 : Blo 330750 501611 := bstep (se 1 (by rfl) ⟨376208, by rfl⟩ : syracuseStep 501611 = 752417) B752417
theorem B1124279 : Blo 330750 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B501839 : Blo 330750 501839 := bstep (se 1 (by rfl) ⟨376379, by rfl⟩ : syracuseStep 501839 = 752759) B752759
theorem B338119 : Blo 330750 338119 := bstep (se 1 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 338119 = 507179) B507179
theorem B501959 : Blo 330750 501959 := bstep (se 1 (by rfl) ⟨376469, by rfl⟩ : syracuseStep 501959 = 752939) B752939
theorem B502121 : Blo 330750 502121 := bstep (se 2 (by rfl) ⟨188295, by rfl⟩ : syracuseStep 502121 = 376591) B376591
theorem B1255945 : Blo 330750 1255945 := bstep (se 2 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 1255945 = 941959) B941959
theorem B1124873 : Blo 330750 1124873 := bstep (se 2 (by rfl) ⟨421827, by rfl⟩ : syracuseStep 1124873 = 843655) B843655
theorem B862969 : Blo 330750 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B601015 : Blo 330750 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B1125737 : Blo 330750 1125737 := bstep (se 2 (by rfl) ⟨422151, by rfl⟩ : syracuseStep 1125737 = 844303) B844303
theorem B4107763 : Blo 330750 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B1060411 : Blo 330750 1060411 := bstep (se 1 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 1060411 = 1590617) B1590617
theorem B569263 : Blo 330750 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B634807 : Blo 330750 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B1257403 : Blo 330750 1257403 := bstep (se 1 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 1257403 = 1886105) B1886105
theorem B1126331 : Blo 330750 1126331 := bstep (se 1 (by rfl) ⟨844748, by rfl⟩ : syracuseStep 1126331 = 1689497) B1689497
theorem B602075 : Blo 330750 602075 := bstep (se 1 (by rfl) ⟨451556, by rfl⟩ : syracuseStep 602075 = 903113) B903113
theorem B2535461 : Blo 330750 2535461 := bstep (se 4 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 2535461 = 475399) B475399
theorem B372775 : Blo 330750 372775 := bstep (se 1 (by rfl) ⟨279581, by rfl⟩ : syracuseStep 372775 = 559163) B559163
theorem B2568581 : Blo 330750 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B1192457 : Blo 330750 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B1258193 : Blo 330750 1258193 := bstep (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) B943645
theorem B4272851 : Blo 330750 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B9679661 : Blo 330750 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B472073 : Blo 330750 472073 := bstep (se 2 (by rfl) ⟨177027, by rfl⟩ : syracuseStep 472073 = 354055) B354055
theorem B8107073 : Blo 330750 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B472187 : Blo 330750 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B1258649 : Blo 330750 1258649 := bstep (se 2 (by rfl) ⟨471993, by rfl⟩ : syracuseStep 1258649 = 943987) B943987
theorem B1651915 : Blo 330750 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B4634003 : Blo 330750 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B3782051 : Blo 330750 3782051 := bstep (se 1 (by rfl) ⟨2836538, by rfl⟩ : syracuseStep 3782051 = 5673077) B5673077
theorem B472495 : Blo 330750 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B374395 : Blo 330750 374395 := bstep (se 1 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 374395 = 561593) B561593
theorem B1128059 : Blo 330750 1128059 := bstep (se 1 (by rfl) ⟨846044, by rfl⟩ : syracuseStep 1128059 = 1692089) B1692089
theorem B472825 : Blo 330750 472825 := bstep (se 2 (by rfl) ⟨177309, by rfl⟩ : syracuseStep 472825 = 354619) B354619
theorem B1128221 : Blo 330750 1128221 := bstep (se 3 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 1128221 = 423083) B423083
theorem B2602847 : Blo 330750 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B374863 : Blo 330750 374863 := bstep (se 1 (by rfl) ⟨281147, by rfl⟩ : syracuseStep 374863 = 562295) B562295
theorem B3225689 : Blo 330750 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B1685771 : Blo 330750 1685771 := bstep (se 1 (by rfl) ⟨1264328, by rfl⟩ : syracuseStep 1685771 = 2528657) B2528657
theorem B375259 : Blo 330750 375259 := bstep (se 1 (by rfl) ⟨281444, by rfl⟩ : syracuseStep 375259 = 562889) B562889
theorem B1128923 : Blo 330750 1128923 := bstep (se 1 (by rfl) ⟨846692, by rfl⟩ : syracuseStep 1128923 = 1693385) B1693385
theorem B899707 : Blo 330750 899707 := bstep (se 1 (by rfl) ⟨674780, by rfl⟩ : syracuseStep 899707 = 1349561) B1349561
theorem B375727 : Blo 330750 375727 := bstep (se 1 (by rfl) ⟨281795, by rfl⟩ : syracuseStep 375727 = 563591) B563591
theorem B1260623 : Blo 330750 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B1129625 : Blo 330750 1129625 := bstep (se 2 (by rfl) ⟨423609, by rfl⟩ : syracuseStep 1129625 = 847219) B847219
theorem B1260791 : Blo 330750 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B376159 : Blo 330750 376159 := bstep (se 1 (by rfl) ⟨282119, by rfl⟩ : syracuseStep 376159 = 564239) B564239
theorem B2014607 : Blo 330750 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B2408069 : Blo 330750 2408069 := bstep (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) B451513
theorem B1687229 : Blo 330750 1687229 := bstep (se 3 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 1687229 = 632711) B632711
theorem B376519 : Blo 330750 376519 := bstep (se 1 (by rfl) ⟨282389, by rfl⟩ : syracuseStep 376519 = 564779) B564779
theorem B1883897 : Blo 330750 1883897 := bstep (se 2 (by rfl) ⟨706461, by rfl⟩ : syracuseStep 1883897 = 1412923) B1412923
theorem B8503055 : Blo 330750 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B1687391 : Blo 330750 1687391 := bstep (se 1 (by rfl) ⟨1265543, by rfl⟩ : syracuseStep 1687391 = 2531087) B2531087
theorem B9912179 : Blo 330750 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B3063737 : Blo 330750 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B1196147 : Blo 330750 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1261763 : Blo 330750 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B10731851 : Blo 330750 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B672275 : Blo 330750 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B1885103 : Blo 330750 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B1262749 : Blo 330750 1262749 := bstep (se 3 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 1262749 = 473531) B473531
theorem B1885355 : Blo 330750 1885355 := bstep (se 1 (by rfl) ⟨1414016, by rfl⟩ : syracuseStep 1885355 = 2828033) B2828033
theorem B1066459 : Blo 330750 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B2541293 : Blo 330750 2541293 := bstep (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) B952985
theorem B837449 : Blo 330750 837449 := bstep (se 2 (by rfl) ⟨314043, by rfl⟩ : syracuseStep 837449 = 628087) B628087
theorem B3197029 : Blo 330750 3197029 := bstep (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) B599443
theorem B837803 : Blo 330750 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B1067393 : Blo 330750 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B6834617 : Blo 330750 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B3590689 : Blo 330750 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B1690145 : Blo 330750 1690145 := bstep (se 2 (by rfl) ⟨633804, by rfl⟩ : syracuseStep 1690145 = 1267609) B1267609
theorem B904031 : Blo 330750 904031 := bstep (se 1 (by rfl) ⟨678023, by rfl⟩ : syracuseStep 904031 = 1356047) B1356047
theorem B5393297 : Blo 330750 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B838583 : Blo 330750 838583 := bstep (se 1 (by rfl) ⟨628937, by rfl⟩ : syracuseStep 838583 = 1257875) B1257875
theorem B674747 : Blo 330750 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B4246607 : Blo 330750 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B1133929 : Blo 330750 1133929 := bstep (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) B850447
theorem B2444897 : Blo 330750 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B479081 : Blo 330750 479081 := bstep (se 2 (by rfl) ⟨179655, by rfl⟩ : syracuseStep 479081 = 359311) B359311
theorem B839585 : Blo 330750 839585 := bstep (se 2 (by rfl) ⟨314844, by rfl⟩ : syracuseStep 839585 = 629689) B629689
theorem B1068983 : Blo 330750 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B1265665 : Blo 330750 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B1888271 : Blo 330750 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B8605777 : Blo 330750 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B1626193 : Blo 330750 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B3592421 : Blo 330750 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B840041 : Blo 330750 840041 := bstep (se 2 (by rfl) ⟨315015, by rfl⟩ : syracuseStep 840041 = 630031) B630031
theorem B3592763 : Blo 330750 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B1266425 : Blo 330750 1266425 := bstep (se 2 (by rfl) ⟨474909, by rfl⟩ : syracuseStep 1266425 = 949819) B949819
theorem B1069853 : Blo 330750 1069853 := bstep (se 3 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 1069853 = 401195) B401195
theorem B709879 : Blo 330750 709879 := bstep (se 1 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 709879 = 1064819) B1064819
theorem B841225 : Blo 330750 841225 := bstep (se 2 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 841225 = 630919) B630919
theorem B1693223 : Blo 330750 1693223 := bstep (se 1 (by rfl) ⟨1269917, by rfl⟩ : syracuseStep 1693223 = 2539835) B2539835
theorem B6084395 : Blo 330750 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B743275 : Blo 330750 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B1136719 : Blo 330750 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B4053149 : Blo 330750 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B1267883 : Blo 330750 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B678137 : Blo 330750 678137 := bstep (se 2 (by rfl) ⟨254301, by rfl⟩ : syracuseStep 678137 = 508603) B508603
theorem B2120023 : Blo 330750 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B1071751 : Blo 330750 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1203011 : Blo 330750 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B4414283 : Blo 330750 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B744299 : Blo 330750 744299 := bstep (se 1 (by rfl) ⟨558224, by rfl⟩ : syracuseStep 744299 = 1116449) B1116449
theorem B744353 : Blo 330750 744353 := bstep (se 2 (by rfl) ⟨279132, by rfl⟩ : syracuseStep 744353 = 558265) B558265
theorem B842683 : Blo 330750 842683 := bstep (se 1 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 842683 = 1264025) B1264025
theorem B744695 : Blo 330750 744695 := bstep (se 1 (by rfl) ⟨558521, by rfl⟩ : syracuseStep 744695 = 1117043) B1117043
theorem B1269053 : Blo 330750 1269053 := bstep (se 3 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 1269053 = 475895) B475895
theorem B1891937 : Blo 330750 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B3858043 : Blo 330750 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1269371 : Blo 330750 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B1924823 : Blo 330750 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B745289 : Blo 330750 745289 := bstep (se 2 (by rfl) ⟨279483, by rfl⟩ : syracuseStep 745289 = 558967) B558967
theorem B1236809 : Blo 330750 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B2842553 : Blo 330750 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B2285597 : Blo 330750 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B713065 : Blo 330750 713065 := bstep (se 2 (by rfl) ⟨267399, by rfl⟩ : syracuseStep 713065 = 534799) B534799
theorem B942461 : Blo 330750 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B746081 : Blo 330750 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B942803 : Blo 330750 942803 := bstep (se 1 (by rfl) ⟨707102, by rfl⟩ : syracuseStep 942803 = 1414205) B1414205
theorem B746423 : Blo 330750 746423 := bstep (se 1 (by rfl) ⟨559817, by rfl⟩ : syracuseStep 746423 = 1119635) B1119635
theorem B1270799 : Blo 330750 1270799 := bstep (se 1 (by rfl) ⟨953099, by rfl⟩ : syracuseStep 1270799 = 1906199) B1906199
theorem B1893395 : Blo 330750 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B1893851 : Blo 330750 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B845275 : Blo 330750 845275 := bstep (se 1 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 845275 = 1267913) B1267913
theorem B747017 : Blo 330750 747017 := bstep (se 2 (by rfl) ⟨280131, by rfl⟩ : syracuseStep 747017 = 560263) B560263
theorem B1468043 : Blo 330750 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B943805 : Blo 330750 943805 := bstep (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) B353927
theorem B1894103 : Blo 330750 1894103 := bstep (se 1 (by rfl) ⟨1420577, by rfl⟩ : syracuseStep 1894103 = 2841155) B2841155
theorem B747359 : Blo 330750 747359 := bstep (se 1 (by rfl) ⟨560519, by rfl⟩ : syracuseStep 747359 = 1121039) B1121039
theorem B714671 : Blo 330750 714671 := bstep (se 1 (by rfl) ⟨536003, by rfl⟩ : syracuseStep 714671 = 1072007) B1072007
theorem B747539 : Blo 330750 747539 := bstep (se 1 (by rfl) ⟨560654, by rfl⟩ : syracuseStep 747539 = 1121309) B1121309
theorem B2385949 : Blo 330750 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B845903 : Blo 330750 845903 := bstep (se 1 (by rfl) ⟨634427, by rfl⟩ : syracuseStep 845903 = 1268855) B1268855
theorem B1206353 : Blo 330750 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B747881 : Blo 330750 747881 := bstep (se 2 (by rfl) ⟨280455, by rfl⟩ : syracuseStep 747881 = 560911) B560911
theorem B2026043 : Blo 330750 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B846551 : Blo 330750 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B748475 : Blo 330750 748475 := bstep (se 1 (by rfl) ⟨561356, by rfl⟩ : syracuseStep 748475 = 1122713) B1122713
theorem B748601 : Blo 330750 748601 := bstep (se 2 (by rfl) ⟨280725, by rfl⟩ : syracuseStep 748601 = 561451) B561451
theorem B748943 : Blo 330750 748943 := bstep (se 1 (by rfl) ⟨561707, by rfl⟩ : syracuseStep 748943 = 1123415) B1123415
theorem B749267 : Blo 330750 749267 := bstep (se 1 (by rfl) ⟨561950, by rfl⟩ : syracuseStep 749267 = 1123901) B1123901
theorem B1896311 : Blo 330750 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B9629603 : Blo 330750 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B17592227 : Blo 330750 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B1798159 : Blo 330750 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B946333 : Blo 330750 946333 := bstep (se 3 (by rfl) ⟨177437, by rfl⟩ : syracuseStep 946333 = 354875) B354875
theorem B946561 : Blo 330750 946561 := bstep (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) B709921
theorem B2683415 : Blo 330750 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B1897019 : Blo 330750 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B750203 : Blo 330750 750203 := bstep (se 1 (by rfl) ⟨562652, by rfl⟩ : syracuseStep 750203 = 1125305) B1125305
theorem B946903 : Blo 330750 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B750329 : Blo 330750 750329 := bstep (se 2 (by rfl) ⟨281373, by rfl⟩ : syracuseStep 750329 = 562747) B562747
theorem B750599 : Blo 330750 750599 := bstep (se 1 (by rfl) ⟨562949, by rfl⟩ : syracuseStep 750599 = 1125899) B1125899
theorem B750671 : Blo 330750 750671 := bstep (se 1 (by rfl) ⟨563003, by rfl⟩ : syracuseStep 750671 = 1126007) B1126007
theorem B4846837 : Blo 330750 4846837 := bstep (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) B454391
theorem B751067 : Blo 330750 751067 := bstep (se 1 (by rfl) ⟨563300, by rfl⟩ : syracuseStep 751067 = 1126601) B1126601
theorem B4257269 : Blo 330750 4257269 := bstep (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) B399119
theorem B423463 : Blo 330750 423463 := bstep (se 1 (by rfl) ⟨317597, by rfl⟩ : syracuseStep 423463 = 635195) B635195
theorem B5011237 : Blo 330750 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B751535 : Blo 330750 751535 := bstep (se 1 (by rfl) ⟨563651, by rfl⟩ : syracuseStep 751535 = 1127303) B1127303
theorem B3209219 : Blo 330750 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B3045383 : Blo 330750 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B751787 : Blo 330750 751787 := bstep (se 1 (by rfl) ⟨563840, by rfl⟩ : syracuseStep 751787 = 1127681) B1127681
theorem B1341839 : Blo 330750 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B850571 : Blo 330750 850571 := bstep (se 1 (by rfl) ⟨637928, by rfl⟩ : syracuseStep 850571 = 1275857) B1275857
theorem B752327 : Blo 330750 752327 := bstep (se 1 (by rfl) ⟨564245, by rfl⟩ : syracuseStep 752327 = 1128491) B1128491
theorem B6062501 : Blo 330750 6062501 := bstep (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) B1136719
theorem B950753 : Blo 330750 950753 := bstep (se 2 (by rfl) ⟨356532, by rfl⟩ : syracuseStep 950753 = 713065) B713065
theorem B4031309 : Blo 330750 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B558299 : Blo 330750 558299 := bstep (se 1 (by rfl) ⟨418724, by rfl⟩ : syracuseStep 558299 = 837449) B837449
theorem B558535 : Blo 330750 558535 := bstep (se 1 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 558535 = 837803) B837803
theorem B1803865 : Blo 330750 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B4556411 : Blo 330750 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B559055 : Blo 330750 559055 := bstep (se 1 (by rfl) ⟨419291, by rfl⟩ : syracuseStep 559055 = 838583) B838583
theorem B853967 : Blo 330750 853967 := bstep (se 1 (by rfl) ⟨640475, by rfl⟩ : syracuseStep 853967 = 1280951) B1280951
theorem B5703695 : Blo 330750 5703695 := bstep (se 1 (by rfl) ⟨4277771, by rfl⟩ : syracuseStep 5703695 = 8555543) B8555543
theorem B2852941 : Blo 330750 2852941 := bstep (se 3 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 2852941 = 1069853) B1069853
theorem B559723 : Blo 330750 559723 := bstep (se 1 (by rfl) ⟨419792, by rfl⟩ : syracuseStep 559723 = 839585) B839585
theorem B3181265 : Blo 330750 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B4262705 : Blo 330750 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B2394947 : Blo 330750 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B2034557 : Blo 330750 2034557 := bstep (se 3 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 2034557 = 762959) B762959
theorem B560027 : Blo 330750 560027 := bstep (se 1 (by rfl) ⟨420020, by rfl⟩ : syracuseStep 560027 = 840041) B840041
theorem B2395175 : Blo 330750 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B331039 : Blo 330750 331039 := bstep (se 1 (by rfl) ⟨248279, by rfl⟩ : syracuseStep 331039 = 496559) B496559
theorem B331099 : Blo 330750 331099 := bstep (se 1 (by rfl) ⟨248324, by rfl⟩ : syracuseStep 331099 = 496649) B496649
theorem B1674593 : Blo 330750 1674593 := bstep (se 2 (by rfl) ⟨627972, by rfl⟩ : syracuseStep 1674593 = 1255945) B1255945
theorem B331119 : Blo 330750 331119 := bstep (se 1 (by rfl) ⟨248339, by rfl⟩ : syracuseStep 331119 = 496679) B496679
theorem B4787585 : Blo 330750 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B331175 : Blo 330750 331175 := bstep (se 1 (by rfl) ⟨248381, by rfl⟩ : syracuseStep 331175 = 496763) B496763
theorem B331259 : Blo 330750 331259 := bstep (se 1 (by rfl) ⟨248444, by rfl⟩ : syracuseStep 331259 = 496889) B496889
theorem B331327 : Blo 330750 331327 := bstep (se 1 (by rfl) ⟨248495, by rfl⟩ : syracuseStep 331327 = 496991) B496991
theorem B331335 : Blo 330750 331335 := bstep (se 1 (by rfl) ⟨248501, by rfl⟩ : syracuseStep 331335 = 497003) B497003
theorem B1150625 : Blo 330750 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B331487 : Blo 330750 331487 := bstep (se 1 (by rfl) ⟨248615, by rfl⟩ : syracuseStep 331487 = 497231) B497231
theorem B331567 : Blo 330750 331567 := bstep (se 1 (by rfl) ⟨248675, by rfl⟩ : syracuseStep 331567 = 497351) B497351
theorem B331675 : Blo 330750 331675 := bstep (se 1 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 331675 = 497513) B497513
theorem B331727 : Blo 330750 331727 := bstep (se 1 (by rfl) ⟨248795, by rfl⟩ : syracuseStep 331727 = 497591) B497591
theorem B331751 : Blo 330750 331751 := bstep (se 1 (by rfl) ⟨248813, by rfl⟩ : syracuseStep 331751 = 497627) B497627
theorem B7213205 : Blo 330750 7213205 := bstep (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) B338119
theorem B332063 : Blo 330750 332063 := bstep (se 1 (by rfl) ⟨249047, by rfl⟩ : syracuseStep 332063 = 498095) B498095
theorem B1118555 : Blo 330750 1118555 := bstep (se 1 (by rfl) ⟨838916, by rfl⟩ : syracuseStep 1118555 = 1677833) B1677833
theorem B332123 : Blo 330750 332123 := bstep (se 1 (by rfl) ⟨249092, by rfl⟩ : syracuseStep 332123 = 498185) B498185
theorem B332143 : Blo 330750 332143 := bstep (se 1 (by rfl) ⟨249107, by rfl⟩ : syracuseStep 332143 = 498215) B498215
theorem B332199 : Blo 330750 332199 := bstep (se 1 (by rfl) ⟨249149, by rfl⟩ : syracuseStep 332199 = 498299) B498299
theorem B1511905 : Blo 330750 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B332283 : Blo 330750 332283 := bstep (se 1 (by rfl) ⟨249212, by rfl⟩ : syracuseStep 332283 = 498425) B498425
theorem B332351 : Blo 330750 332351 := bstep (se 1 (by rfl) ⟨249263, by rfl⟩ : syracuseStep 332351 = 498527) B498527
theorem B496199 : Blo 330750 496199 := bstep (se 1 (by rfl) ⟨372149, by rfl⟩ : syracuseStep 496199 = 744299) B744299
theorem B332359 : Blo 330750 332359 := bstep (se 1 (by rfl) ⟨249269, by rfl⟩ : syracuseStep 332359 = 498539) B498539
theorem B496235 : Blo 330750 496235 := bstep (se 1 (by rfl) ⟨372176, by rfl⟩ : syracuseStep 496235 = 744353) B744353
theorem B332511 : Blo 330750 332511 := bstep (se 1 (by rfl) ⟨249383, by rfl⟩ : syracuseStep 332511 = 498767) B498767
theorem B1413881 : Blo 330750 1413881 := bstep (se 2 (by rfl) ⟨530205, by rfl⟩ : syracuseStep 1413881 = 1060411) B1060411
theorem B332591 : Blo 330750 332591 := bstep (se 1 (by rfl) ⟨249443, by rfl⟩ : syracuseStep 332591 = 498887) B498887
theorem B496463 : Blo 330750 496463 := bstep (se 1 (by rfl) ⟨372347, by rfl⟩ : syracuseStep 496463 = 744695) B744695
theorem B332699 : Blo 330750 332699 := bstep (se 1 (by rfl) ⟨249524, by rfl⟩ : syracuseStep 332699 = 499049) B499049
theorem B332751 : Blo 330750 332751 := bstep (se 1 (by rfl) ⟨249563, by rfl⟩ : syracuseStep 332751 = 499127) B499127
theorem B332775 : Blo 330750 332775 := bstep (se 1 (by rfl) ⟨249581, by rfl⟩ : syracuseStep 332775 = 499163) B499163
theorem B1283215 : Blo 330750 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B496859 : Blo 330750 496859 := bstep (se 1 (by rfl) ⟨372644, by rfl⟩ : syracuseStep 496859 = 745289) B745289
theorem B759017 : Blo 330750 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B1676537 : Blo 330750 1676537 := bstep (se 2 (by rfl) ⟨628701, by rfl⟩ : syracuseStep 1676537 = 1257403) B1257403
theorem B333087 : Blo 330750 333087 := bstep (se 1 (by rfl) ⟨249815, by rfl⟩ : syracuseStep 333087 = 499631) B499631
theorem B1119527 : Blo 330750 1119527 := bstep (se 1 (by rfl) ⟨839645, by rfl⟩ : syracuseStep 1119527 = 1679291) B1679291
theorem B333147 : Blo 330750 333147 := bstep (se 1 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 333147 = 499721) B499721
theorem B2397545 : Blo 330750 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B333167 : Blo 330750 333167 := bstep (se 1 (by rfl) ⟨249875, by rfl⟩ : syracuseStep 333167 = 499751) B499751
theorem B3020165 : Blo 330750 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B497033 : Blo 330750 497033 := bstep (se 2 (by rfl) ⟨186387, by rfl⟩ : syracuseStep 497033 = 372775) B372775
theorem B333223 : Blo 330750 333223 := bstep (se 1 (by rfl) ⟨249917, by rfl⟩ : syracuseStep 333223 = 499835) B499835
theorem B2168257 : Blo 330750 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B11474369 : Blo 330750 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B333307 : Blo 330750 333307 := bstep (se 1 (by rfl) ⟨249980, by rfl⟩ : syracuseStep 333307 = 499961) B499961
theorem B3216941 : Blo 330750 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B333375 : Blo 330750 333375 := bstep (se 1 (by rfl) ⟨250031, by rfl⟩ : syracuseStep 333375 = 500063) B500063
theorem B333383 : Blo 330750 333383 := bstep (se 1 (by rfl) ⟨250037, by rfl⟩ : syracuseStep 333383 = 500075) B500075
theorem B628307 : Blo 330750 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B333535 : Blo 330750 333535 := bstep (se 1 (by rfl) ⟨250151, by rfl⟩ : syracuseStep 333535 = 500303) B500303
theorem B497387 : Blo 330750 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B333615 : Blo 330750 333615 := bstep (se 1 (by rfl) ⟨250211, by rfl⟩ : syracuseStep 333615 = 500423) B500423
theorem B628535 : Blo 330750 628535 := bstep (se 1 (by rfl) ⟨471401, by rfl⟩ : syracuseStep 628535 = 942803) B942803
theorem B333723 : Blo 330750 333723 := bstep (se 1 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 333723 = 500585) B500585
theorem B497615 : Blo 330750 497615 := bstep (se 1 (by rfl) ⟨373211, by rfl⟩ : syracuseStep 497615 = 746423) B746423
theorem B333775 : Blo 330750 333775 := bstep (se 1 (by rfl) ⟨250331, by rfl⟩ : syracuseStep 333775 = 500663) B500663
theorem B333799 : Blo 330750 333799 := bstep (se 1 (by rfl) ⟨250349, by rfl⟩ : syracuseStep 333799 = 500699) B500699
theorem B1808365 : Blo 330750 1808365 := bstep (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) B678137
theorem B1120391 : Blo 330750 1120391 := bstep (se 1 (by rfl) ⟨840293, by rfl⟩ : syracuseStep 1120391 = 1680587) B1680587
theorem B334111 : Blo 330750 334111 := bstep (se 1 (by rfl) ⟨250583, by rfl⟩ : syracuseStep 334111 = 501167) B501167
theorem B498011 : Blo 330750 498011 := bstep (se 1 (by rfl) ⟨373508, by rfl⟩ : syracuseStep 498011 = 747017) B747017
theorem B334171 : Blo 330750 334171 := bstep (se 1 (by rfl) ⟨250628, by rfl⟩ : syracuseStep 334171 = 501257) B501257
theorem B334191 : Blo 330750 334191 := bstep (se 1 (by rfl) ⟨250643, by rfl⟩ : syracuseStep 334191 = 501287) B501287
theorem B334247 : Blo 330750 334247 := bstep (se 1 (by rfl) ⟨250685, by rfl⟩ : syracuseStep 334247 = 501371) B501371
theorem B629203 : Blo 330750 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B334331 : Blo 330750 334331 := bstep (se 1 (by rfl) ⟨250748, by rfl⟩ : syracuseStep 334331 = 501497) B501497
theorem B498239 : Blo 330750 498239 := bstep (se 1 (by rfl) ⟨373679, by rfl⟩ : syracuseStep 498239 = 747359) B747359
theorem B334399 : Blo 330750 334399 := bstep (se 1 (by rfl) ⟨250799, by rfl⟩ : syracuseStep 334399 = 501599) B501599
theorem B334407 : Blo 330750 334407 := bstep (se 1 (by rfl) ⟨250805, by rfl⟩ : syracuseStep 334407 = 501611) B501611
theorem B1710665 : Blo 330750 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B498359 : Blo 330750 498359 := bstep (se 1 (by rfl) ⟨373769, by rfl⟩ : syracuseStep 498359 = 747539) B747539
theorem B563935 : Blo 330750 563935 := bstep (se 1 (by rfl) ⟨422951, by rfl⟩ : syracuseStep 563935 = 845903) B845903
theorem B334559 : Blo 330750 334559 := bstep (se 1 (by rfl) ⟨250919, by rfl⟩ : syracuseStep 334559 = 501839) B501839
theorem B334639 : Blo 330750 334639 := bstep (se 1 (by rfl) ⟨250979, by rfl⟩ : syracuseStep 334639 = 501959) B501959
theorem B498587 : Blo 330750 498587 := bstep (se 1 (by rfl) ⟨373940, by rfl⟩ : syracuseStep 498587 = 747881) B747881
theorem B334747 : Blo 330750 334747 := bstep (se 1 (by rfl) ⟨251060, by rfl⟩ : syracuseStep 334747 = 502121) B502121
theorem B2202553 : Blo 330750 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B6462449 : Blo 330750 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B1350695 : Blo 330750 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B564367 : Blo 330750 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B629993 : Blo 330750 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B498983 : Blo 330750 498983 := bstep (se 1 (by rfl) ⟨374237, by rfl⟩ : syracuseStep 498983 = 748475) B748475
theorem B1121633 : Blo 330750 1121633 := bstep (se 2 (by rfl) ⟨420612, by rfl⟩ : syracuseStep 1121633 = 841225) B841225
theorem B499067 : Blo 330750 499067 := bstep (se 1 (by rfl) ⟨374300, by rfl⟩ : syracuseStep 499067 = 748601) B748601
theorem B564617 : Blo 330750 564617 := bstep (se 2 (by rfl) ⟨211731, by rfl⟩ : syracuseStep 564617 = 423463) B423463
theorem B499193 : Blo 330750 499193 := bstep (se 2 (by rfl) ⟨187197, by rfl⟩ : syracuseStep 499193 = 374395) B374395
theorem B499295 : Blo 330750 499295 := bstep (se 1 (by rfl) ⟨374471, by rfl⟩ : syracuseStep 499295 = 748943) B748943
theorem B630433 : Blo 330750 630433 := bstep (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) B472825
theorem B499511 : Blo 330750 499511 := bstep (se 1 (by rfl) ⟨374633, by rfl⟩ : syracuseStep 499511 = 749267) B749267
theorem B991033 : Blo 330750 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B401383 : Blo 330750 401383 := bstep (se 1 (by rfl) ⟨301037, by rfl⟩ : syracuseStep 401383 = 602075) B602075
theorem B499817 : Blo 330750 499817 := bstep (se 2 (by rfl) ⟨187431, by rfl⟩ : syracuseStep 499817 = 374863) B374863
theorem B1712387 : Blo 330750 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B794971 : Blo 330750 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B500135 : Blo 330750 500135 := bstep (se 1 (by rfl) ⟨375101, by rfl⟩ : syracuseStep 500135 = 750203) B750203
theorem B2826697 : Blo 330750 2826697 := bstep (se 2 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 2826697 = 2120023) B2120023
theorem B500219 : Blo 330750 500219 := bstep (se 1 (by rfl) ⟨375164, by rfl⟩ : syracuseStep 500219 = 750329) B750329
theorem B500345 : Blo 330750 500345 := bstep (se 2 (by rfl) ⟨187629, by rfl⟩ : syracuseStep 500345 = 375259) B375259
theorem B500399 : Blo 330750 500399 := bstep (se 1 (by rfl) ⟨375299, by rfl⟩ : syracuseStep 500399 = 750599) B750599
theorem B500447 : Blo 330750 500447 := bstep (se 1 (by rfl) ⟨375335, by rfl⟩ : syracuseStep 500447 = 750671) B750671
theorem B3089335 : Blo 330750 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B500711 : Blo 330750 500711 := bstep (se 1 (by rfl) ⟨375533, by rfl⟩ : syracuseStep 500711 = 751067) B751067
theorem B500969 : Blo 330750 500969 := bstep (se 2 (by rfl) ⟨187863, by rfl⟩ : syracuseStep 500969 = 375727) B375727
theorem B1123577 : Blo 330750 1123577 := bstep (se 2 (by rfl) ⟨421341, by rfl⟩ : syracuseStep 1123577 = 842683) B842683
theorem B501023 : Blo 330750 501023 := bstep (se 1 (by rfl) ⟨375767, by rfl⟩ : syracuseStep 501023 = 751535) B751535
theorem B2139479 : Blo 330750 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B1680749 : Blo 330750 1680749 := bstep (se 3 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 1680749 = 630281) B630281
theorem B501191 : Blo 330750 501191 := bstep (se 1 (by rfl) ⟨375893, by rfl⟩ : syracuseStep 501191 = 751787) B751787
theorem B1123847 : Blo 330750 1123847 := bstep (se 1 (by rfl) ⟨842885, by rfl⟩ : syracuseStep 1123847 = 1685771) B1685771
theorem B894559 : Blo 330750 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B567047 : Blo 330750 567047 := bstep (se 1 (by rfl) ⟨425285, by rfl⟩ : syracuseStep 567047 = 850571) B850571
theorem B501545 : Blo 330750 501545 := bstep (se 2 (by rfl) ⟨188079, by rfl⟩ : syracuseStep 501545 = 376159) B376159
theorem B501551 : Blo 330750 501551 := bstep (se 1 (by rfl) ⟨376163, by rfl⟩ : syracuseStep 501551 = 752327) B752327
theorem B502025 : Blo 330750 502025 := bstep (se 2 (by rfl) ⟨188259, by rfl⟩ : syracuseStep 502025 = 376519) B376519
theorem B1124819 : Blo 330750 1124819 := bstep (se 1 (by rfl) ⟨843614, by rfl⟩ : syracuseStep 1124819 = 1687229) B1687229
theorem B1255931 : Blo 330750 1255931 := bstep (se 1 (by rfl) ⟨941948, by rfl⟩ : syracuseStep 1255931 = 1883897) B1883897
theorem B1124927 : Blo 330750 1124927 := bstep (se 1 (by rfl) ⟨843695, by rfl⟩ : syracuseStep 1124927 = 1687391) B1687391
theorem B2042491 : Blo 330750 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B21900145 : Blo 330750 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B7154567 : Blo 330750 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B3189725 : Blo 330750 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B1256735 : Blo 330750 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B1355075 : Blo 330750 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B1256903 : Blo 330750 1256903 := bstep (se 1 (by rfl) ⟨942677, by rfl⟩ : syracuseStep 1256903 = 1885355) B1885355
theorem B1683179 : Blo 330750 1683179 := bstep (se 1 (by rfl) ⟨1262384, by rfl⟩ : syracuseStep 1683179 = 2524769) B2524769
theorem B2141963 : Blo 330750 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B372559 : Blo 330750 372559 := bstep (se 1 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 372559 = 558839) B558839
theorem B7155773 : Blo 330750 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B1683665 : Blo 330750 1683665 := bstep (se 2 (by rfl) ⟨631374, by rfl⟩ : syracuseStep 1683665 = 1262749) B1262749
theorem B372955 : Blo 330750 372955 := bstep (se 1 (by rfl) ⟨279716, by rfl⟩ : syracuseStep 372955 = 559433) B559433
theorem B2732395 : Blo 330750 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B1126763 : Blo 330750 1126763 := bstep (se 1 (by rfl) ⟨845072, by rfl⟩ : syracuseStep 1126763 = 1690145) B1690145
theorem B7188911 : Blo 330750 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B3584459 : Blo 330750 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B1061345 : Blo 330750 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B373243 : Blo 330750 373243 := bstep (se 1 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 373243 = 559865) B559865
theorem B602687 : Blo 330750 602687 := bstep (se 1 (by rfl) ⟨452015, by rfl⟩ : syracuseStep 602687 = 904031) B904031
theorem B1421945 : Blo 330750 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1127033 : Blo 330750 1127033 := bstep (se 2 (by rfl) ⟨422637, by rfl⟩ : syracuseStep 1127033 = 845275) B845275
theorem B1421995 : Blo 330750 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B373423 : Blo 330750 373423 := bstep (se 1 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 373423 = 560135) B560135
theorem B1684151 : Blo 330750 1684151 := bstep (se 1 (by rfl) ⟨1263113, by rfl⟩ : syracuseStep 1684151 = 2526227) B2526227
theorem B2831071 : Blo 330750 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B373711 : Blo 330750 373711 := bstep (se 1 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 373711 = 560567) B560567
theorem B1684637 : Blo 330750 1684637 := bstep (se 3 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 1684637 = 631739) B631739
theorem B374107 : Blo 330750 374107 := bstep (se 1 (by rfl) ⟨280580, by rfl⟩ : syracuseStep 374107 = 561161) B561161
theorem B1258847 : Blo 330750 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B1258861 : Blo 330750 1258861 := bstep (se 3 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 1258861 = 472073) B472073
theorem B374215 : Blo 330750 374215 := bstep (se 1 (by rfl) ⟨280661, by rfl⟩ : syracuseStep 374215 = 561323) B561323
theorem B1259165 : Blo 330750 1259165 := bstep (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) B472187
theorem B374575 : Blo 330750 374575 := bstep (se 1 (by rfl) ⟨280931, by rfl⟩ : syracuseStep 374575 = 561863) B561863
theorem B374683 : Blo 330750 374683 := bstep (se 1 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 374683 = 562025) B562025
theorem B5421323 : Blo 330750 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B375079 : Blo 330750 375079 := bstep (se 1 (by rfl) ⟨281309, by rfl⟩ : syracuseStep 375079 = 562619) B562619
theorem B375151 : Blo 330750 375151 := bstep (se 1 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 375151 = 562727) B562727
theorem B1128815 : Blo 330750 1128815 := bstep (se 1 (by rfl) ⟨846611, by rfl⟩ : syracuseStep 1128815 = 1693223) B1693223
theorem B1685933 : Blo 330750 1685933 := bstep (se 3 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 1685933 = 632225) B632225
theorem B801353 : Blo 330750 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B375367 : Blo 330750 375367 := bstep (se 1 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 375367 = 563051) B563051
theorem B1686095 : Blo 330750 1686095 := bstep (se 1 (by rfl) ⟨1264571, by rfl⟩ : syracuseStep 1686095 = 2529143) B2529143
theorem B2702099 : Blo 330750 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B5094251 : Blo 330750 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B802007 : Blo 330750 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B376231 : Blo 330750 376231 := bstep (se 1 (by rfl) ⟨282173, by rfl⟩ : syracuseStep 376231 = 564347) B564347
theorem B1261291 : Blo 330750 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B8568665 : Blo 330750 8568665 := bstep (se 2 (by rfl) ⟨3213249, by rfl⟩ : syracuseStep 8568665 = 6426499) B6426499
theorem B1687553 : Blo 330750 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B1523731 : Blo 330750 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B1261777 : Blo 330750 1261777 := bstep (se 2 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 1261777 = 946333) B946333
theorem B1262081 : Blo 330750 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B1262263 : Blo 330750 1262263 := bstep (se 1 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 1262263 = 1893395) B1893395
theorem B1688363 : Blo 330750 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B1262537 : Blo 330750 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B902107 : Blo 330750 902107 := bstep (se 1 (by rfl) ⟨676580, by rfl⟩ : syracuseStep 902107 = 1353161) B1353161
theorem B1262567 : Blo 330750 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B1262735 : Blo 330750 1262735 := bstep (se 1 (by rfl) ⟨947051, by rfl⟩ : syracuseStep 1262735 = 1894103) B1894103
theorem B476447 : Blo 330750 476447 := bstep (se 1 (by rfl) ⟨357335, by rfl⟩ : syracuseStep 476447 = 714671) B714671
theorem B1590941 : Blo 330750 1590941 := bstep (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) B596603
theorem B837641 : Blo 330750 837641 := bstep (se 2 (by rfl) ⟨314115, by rfl⟩ : syracuseStep 837641 = 628231) B628231
theorem B1264207 : Blo 330750 1264207 := bstep (se 1 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 1264207 = 1896311) B1896311
theorem B21908069 : Blo 330750 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1690307 : Blo 330750 1690307 := bstep (se 1 (by rfl) ⟨1267730, by rfl⟩ : syracuseStep 1690307 = 2535461) B2535461
theorem B1264679 : Blo 330750 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B838795 : Blo 330750 838795 := bstep (se 1 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 838795 = 1258193) B1258193
theorem B839099 : Blo 330750 839099 := bstep (se 1 (by rfl) ⟨629324, by rfl⟩ : syracuseStep 839099 = 1258649) B1258649
theorem B1199609 : Blo 330750 1199609 := bstep (se 2 (by rfl) ⟨449853, by rfl⟩ : syracuseStep 1199609 = 899707) B899707
theorem B1429001 : Blo 330750 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B2838179 : Blo 330750 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B2150459 : Blo 330750 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B26726597 : Blo 330750 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B840415 : Blo 330750 840415 := bstep (se 1 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 840415 = 1260623) B1260623
theorem B840527 : Blo 330750 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B3298157 : Blo 330750 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B26432477 : Blo 330750 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B1889729 : Blo 330750 1889729 := bstep (se 2 (by rfl) ⟨708648, by rfl⟩ : syracuseStep 1889729 = 1417297) B1417297
theorem B841175 : Blo 330750 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B448183 : Blo 330750 448183 := bstep (se 1 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 448183 = 672275) B672275
theorem B841529 : Blo 330750 841529 := bstep (se 2 (by rfl) ⟨315573, by rfl⟩ : syracuseStep 841529 = 631147) B631147
theorem B1791973 : Blo 330750 1791973 := bstep (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) B335995
theorem B14342345 : Blo 330750 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B448745 : Blo 330750 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B1694195 : Blo 330750 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B1268399 : Blo 330750 1268399 := bstep (se 1 (by rfl) ⟨951299, by rfl⟩ : syracuseStep 1268399 = 1902599) B1902599
theorem B744335 : Blo 330750 744335 := bstep (se 1 (by rfl) ⟨558251, by rfl⟩ : syracuseStep 744335 = 1116503) B1116503
theorem B711595 : Blo 330750 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B711929 : Blo 330750 711929 := bstep (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) B533947
theorem B3595531 : Blo 330750 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B449831 : Blo 330750 449831 := bstep (se 1 (by rfl) ⟨337373, by rfl⟩ : syracuseStep 449831 = 674747) B674747
theorem B843169 : Blo 330750 843169 := bstep (se 2 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 843169 = 632377) B632377
theorem B745055 : Blo 330750 745055 := bstep (se 1 (by rfl) ⟨558791, by rfl⟩ : syracuseStep 745055 = 1117583) B1117583
theorem B1629931 : Blo 330750 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B745271 : Blo 330750 745271 := bstep (se 1 (by rfl) ⟨558953, by rfl⟩ : syracuseStep 745271 = 1117907) B1117907
theorem B712655 : Blo 330750 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B745577 : Blo 330750 745577 := bstep (se 2 (by rfl) ⟨279591, by rfl⟩ : syracuseStep 745577 = 559183) B559183
theorem B2187383 : Blo 330750 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B1794479 : Blo 330750 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B844283 : Blo 330750 844283 := bstep (se 1 (by rfl) ⟨633212, by rfl⟩ : syracuseStep 844283 = 1266425) B1266425
theorem B1270343 : Blo 330750 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B746063 : Blo 330750 746063 := bstep (se 1 (by rfl) ⟨559547, by rfl⟩ : syracuseStep 746063 = 1119095) B1119095
theorem B1139321 : Blo 330750 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B1794743 : Blo 330750 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B746207 : Blo 330750 746207 := bstep (se 1 (by rfl) ⟨559655, by rfl⟩ : syracuseStep 746207 = 1119311) B1119311
theorem B746459 : Blo 330750 746459 := bstep (se 1 (by rfl) ⟨559844, by rfl⟩ : syracuseStep 746459 = 1119689) B1119689
theorem B746639 : Blo 330750 746639 := bstep (se 1 (by rfl) ⟨559979, by rfl⟩ : syracuseStep 746639 = 1119959) B1119959
theorem B4056263 : Blo 330750 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B746729 : Blo 330750 746729 := bstep (se 2 (by rfl) ⟨280023, by rfl⟩ : syracuseStep 746729 = 560047) B560047
theorem B746783 : Blo 330750 746783 := bstep (se 1 (by rfl) ⟨560087, by rfl⟩ : syracuseStep 746783 = 1120175) B1120175
theorem B419195 : Blo 330750 419195 := bstep (se 1 (by rfl) ⟨314396, by rfl⟩ : syracuseStep 419195 = 628793) B628793
theorem B1009057 : Blo 330750 1009057 := bstep (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) B756793
theorem B845255 : Blo 330750 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B2844193 : Blo 330750 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B747305 : Blo 330750 747305 := bstep (se 2 (by rfl) ⟨280239, by rfl⟩ : syracuseStep 747305 = 560479) B560479
theorem B2942855 : Blo 330750 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B846035 : Blo 330750 846035 := bstep (se 1 (by rfl) ⟨634526, by rfl⟩ : syracuseStep 846035 = 1269053) B1269053
theorem B846247 : Blo 330750 846247 := bstep (se 1 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 846247 = 1269371) B1269371
theorem B846409 : Blo 330750 846409 := bstep (se 2 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 846409 = 634807) B634807
theorem B1895035 : Blo 330750 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B748367 : Blo 330750 748367 := bstep (se 1 (by rfl) ⟨561275, by rfl⟩ : syracuseStep 748367 = 1122551) B1122551
theorem B420815 : Blo 330750 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B748583 : Blo 330750 748583 := bstep (se 1 (by rfl) ⟨561437, by rfl⟩ : syracuseStep 748583 = 1122875) B1122875
theorem B748763 : Blo 330750 748763 := bstep (se 1 (by rfl) ⟨561572, by rfl⟩ : syracuseStep 748763 = 1123145) B1123145
theorem B847199 : Blo 330750 847199 := bstep (se 1 (by rfl) ⟨635399, by rfl⟩ : syracuseStep 847199 = 1270799) B1270799
theorem B748961 : Blo 330750 748961 := bstep (se 2 (by rfl) ⟨280860, by rfl⟩ : syracuseStep 748961 = 561721) B561721
theorem B978695 : Blo 330750 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B421787 : Blo 330750 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B749519 : Blo 330750 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B3502081 : Blo 330750 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B946505 : Blo 330750 946505 := bstep (se 2 (by rfl) ⟨354939, by rfl⟩ : syracuseStep 946505 = 709879) B709879
theorem B749897 : Blo 330750 749897 := bstep (se 2 (by rfl) ⟨281211, by rfl⟩ : syracuseStep 749897 = 562423) B562423
theorem B749915 : Blo 330750 749915 := bstep (se 1 (by rfl) ⟨562436, by rfl⟩ : syracuseStep 749915 = 1124873) B1124873
theorem B750491 : Blo 330750 750491 := bstep (se 1 (by rfl) ⟨562868, by rfl⟩ : syracuseStep 750491 = 1125737) B1125737
theorem B750689 : Blo 330750 750689 := bstep (se 2 (by rfl) ⟨281508, by rfl⟩ : syracuseStep 750689 = 563017) B563017
theorem B11728151 : Blo 330750 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B6419735 : Blo 330750 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B750887 : Blo 330750 750887 := bstep (se 1 (by rfl) ⟨563165, by rfl⟩ : syracuseStep 750887 = 1126331) B1126331
theorem B751265 : Blo 330750 751265 := bstep (se 2 (by rfl) ⟨281724, by rfl⟩ : syracuseStep 751265 = 563449) B563449
theorem B2848567 : Blo 330750 2848567 := bstep (se 1 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 2848567 = 4272851) B4272851
theorem B6453107 : Blo 330750 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B751625 : Blo 330750 751625 := bstep (se 2 (by rfl) ⟨281859, by rfl⟩ : syracuseStep 751625 = 563719) B563719
theorem B5404715 : Blo 330750 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B2521367 : Blo 330750 2521367 := bstep (se 1 (by rfl) ⟨1891025, by rfl⟩ : syracuseStep 2521367 = 3782051) B3782051
theorem B752039 : Blo 330750 752039 := bstep (se 1 (by rfl) ⟨564029, by rfl⟩ : syracuseStep 752039 = 1128059) B1128059
theorem B752147 : Blo 330750 752147 := bstep (se 1 (by rfl) ⟨564110, by rfl⟩ : syracuseStep 752147 = 1128221) B1128221
theorem B1735231 : Blo 330750 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B752201 : Blo 330750 752201 := bstep (se 2 (by rfl) ⟨282075, by rfl⟩ : syracuseStep 752201 = 564151) B564151
theorem B2030255 : Blo 330750 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B752615 : Blo 330750 752615 := bstep (se 1 (by rfl) ⟨564461, by rfl⟩ : syracuseStep 752615 = 1128923) B1128923
theorem B752993 : Blo 330750 752993 := bstep (se 2 (by rfl) ⟨282372, by rfl⟩ : syracuseStep 752993 = 564745) B564745
theorem B753083 : Blo 330750 753083 := bstep (se 1 (by rfl) ⟨564812, by rfl⟩ : syracuseStep 753083 = 1129625) B1129625
theorem B5144057 : Blo 330750 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B1343071 : Blo 330750 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B1277549 : Blo 330750 1277549 := bstep (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) B479081
theorem B1605379 : Blo 330750 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B5668703 : Blo 330750 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B18677765 : Blo 330750 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B2031641 : Blo 330750 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B5833021 : Blo 330750 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B2687539 : Blo 330750 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B3768929 : Blo 330750 3768929 := bstep (se 2 (by rfl) ⟨1413348, by rfl⟩ : syracuseStep 3768929 = 2826697) B2826697
theorem B4785277 : Blo 330750 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B558427 : Blo 330750 558427 := bstep (se 1 (by rfl) ⟨418820, by rfl⟩ : syracuseStep 558427 = 837641) B837641
theorem B3802463 : Blo 330750 3802463 := bstep (se 1 (by rfl) ⟨2851847, by rfl⟩ : syracuseStep 3802463 = 5703695) B5703695
theorem B1607165 : Blo 330750 1607165 := bstep (se 3 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 1607165 = 602687) B602687
theorem B1345409 : Blo 330750 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B1116395 : Blo 330750 1116395 := bstep (se 1 (by rfl) ⟨837296, by rfl⟩ : syracuseStep 1116395 = 1674593) B1674593
theorem B559399 : Blo 330750 559399 := bstep (se 1 (by rfl) ⟨419549, by rfl⟩ : syracuseStep 559399 = 839099) B839099
theorem B952667 : Blo 330750 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B4786613 : Blo 330750 4786613 := bstep (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) B448745
theorem B3803921 : Blo 330750 3803921 := bstep (se 2 (by rfl) ⟨1426470, by rfl⟩ : syracuseStep 3803921 = 2852941) B2852941
theorem B330799 : Blo 330750 330799 := bstep (se 1 (by rfl) ⟨248099, by rfl⟩ : syracuseStep 330799 = 496199) B496199
theorem B330823 : Blo 330750 330823 := bstep (se 1 (by rfl) ⟨248117, by rfl⟩ : syracuseStep 330823 = 496235) B496235
theorem B330975 : Blo 330750 330975 := bstep (se 1 (by rfl) ⟨248231, by rfl⟩ : syracuseStep 330975 = 496463) B496463
theorem B560351 : Blo 330750 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B2198771 : Blo 330750 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B331239 : Blo 330750 331239 := bstep (se 1 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 331239 = 496859) B496859
theorem B2723321 : Blo 330750 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B2526713 : Blo 330750 2526713 := bstep (se 2 (by rfl) ⟨947517, by rfl⟩ : syracuseStep 2526713 = 1895035) B1895035
theorem B1117691 : Blo 330750 1117691 := bstep (se 1 (by rfl) ⟨838268, by rfl⟩ : syracuseStep 1117691 = 1676537) B1676537
theorem B331355 : Blo 330750 331355 := bstep (se 1 (by rfl) ⟨248516, by rfl⟩ : syracuseStep 331355 = 497033) B497033
theorem B560783 : Blo 330750 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B1117853 : Blo 330750 1117853 := bstep (se 3 (by rfl) ⟨209597, by rfl⟩ : syracuseStep 1117853 = 419195) B419195
theorem B29200193 : Blo 330750 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B331591 : Blo 330750 331591 := bstep (se 1 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 331591 = 497387) B497387
theorem B561019 : Blo 330750 561019 := bstep (se 1 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 561019 = 841529) B841529
theorem B331743 : Blo 330750 331743 := bstep (se 1 (by rfl) ⟨248807, by rfl⟩ : syracuseStep 331743 = 497615) B497615
theorem B1118393 : Blo 330750 1118393 := bstep (se 2 (by rfl) ⟨419397, by rfl⟩ : syracuseStep 1118393 = 838795) B838795
theorem B332007 : Blo 330750 332007 := bstep (se 1 (by rfl) ⟨249005, by rfl⟩ : syracuseStep 332007 = 498011) B498011
theorem B332159 : Blo 330750 332159 := bstep (se 1 (by rfl) ⟨249119, by rfl⟩ : syracuseStep 332159 = 498239) B498239
theorem B332239 : Blo 330750 332239 := bstep (se 1 (by rfl) ⟨249179, by rfl⟩ : syracuseStep 332239 = 498359) B498359
theorem B496223 : Blo 330750 496223 := bstep (se 1 (by rfl) ⟨372167, by rfl⟩ : syracuseStep 496223 = 744335) B744335
theorem B332391 : Blo 330750 332391 := bstep (se 1 (by rfl) ⟨249293, by rfl⟩ : syracuseStep 332391 = 498587) B498587
theorem B332655 : Blo 330750 332655 := bstep (se 1 (by rfl) ⟨249491, by rfl⟩ : syracuseStep 332655 = 498983) B498983
theorem B332711 : Blo 330750 332711 := bstep (se 1 (by rfl) ⟨249533, by rfl⟩ : syracuseStep 332711 = 499067) B499067
theorem B332795 : Blo 330750 332795 := bstep (se 1 (by rfl) ⟨249596, by rfl⟩ : syracuseStep 332795 = 499193) B499193
theorem B496703 : Blo 330750 496703 := bstep (se 1 (by rfl) ⟨372527, by rfl⟩ : syracuseStep 496703 = 745055) B745055
theorem B332863 : Blo 330750 332863 := bstep (se 1 (by rfl) ⟨249647, by rfl⟩ : syracuseStep 332863 = 499295) B499295
theorem B496745 : Blo 330750 496745 := bstep (se 2 (by rfl) ⟨186279, by rfl⟩ : syracuseStep 496745 = 372559) B372559
theorem B496847 : Blo 330750 496847 := bstep (se 1 (by rfl) ⟨372635, by rfl⟩ : syracuseStep 496847 = 745271) B745271
theorem B333007 : Blo 330750 333007 := bstep (se 1 (by rfl) ⟨249755, by rfl⟩ : syracuseStep 333007 = 499511) B499511
theorem B497051 : Blo 330750 497051 := bstep (se 1 (by rfl) ⟨372788, by rfl⟩ : syracuseStep 497051 = 745577) B745577
theorem B333211 : Blo 330750 333211 := bstep (se 1 (by rfl) ⟨249908, by rfl⟩ : syracuseStep 333211 = 499817) B499817
theorem B333423 : Blo 330750 333423 := bstep (se 1 (by rfl) ⟨250067, by rfl⟩ : syracuseStep 333423 = 500135) B500135
theorem B497273 : Blo 330750 497273 := bstep (se 2 (by rfl) ⟨186477, by rfl⟩ : syracuseStep 497273 = 372955) B372955
theorem B333479 : Blo 330750 333479 := bstep (se 1 (by rfl) ⟨250109, by rfl⟩ : syracuseStep 333479 = 500219) B500219
theorem B562855 : Blo 330750 562855 := bstep (se 1 (by rfl) ⟨422141, by rfl⟩ : syracuseStep 562855 = 844283) B844283
theorem B497375 : Blo 330750 497375 := bstep (se 1 (by rfl) ⟨373031, by rfl⟩ : syracuseStep 497375 = 746063) B746063
theorem B759547 : Blo 330750 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B333563 : Blo 330750 333563 := bstep (se 1 (by rfl) ⟨250172, by rfl⟩ : syracuseStep 333563 = 500345) B500345
theorem B333599 : Blo 330750 333599 := bstep (se 1 (by rfl) ⟨250199, by rfl⟩ : syracuseStep 333599 = 500399) B500399
theorem B3643193 : Blo 330750 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B497471 : Blo 330750 497471 := bstep (se 1 (by rfl) ⟨373103, by rfl⟩ : syracuseStep 497471 = 746207) B746207
theorem B333631 : Blo 330750 333631 := bstep (se 1 (by rfl) ⟨250223, by rfl⟩ : syracuseStep 333631 = 500447) B500447
theorem B497639 : Blo 330750 497639 := bstep (se 1 (by rfl) ⟨373229, by rfl⟩ : syracuseStep 497639 = 746459) B746459
theorem B333807 : Blo 330750 333807 := bstep (se 1 (by rfl) ⟨250355, by rfl⟩ : syracuseStep 333807 = 500711) B500711
theorem B497657 : Blo 330750 497657 := bstep (se 2 (by rfl) ⟨186621, by rfl⟩ : syracuseStep 497657 = 373243) B373243
theorem B497759 : Blo 330750 497759 := bstep (se 1 (by rfl) ⟨373319, by rfl⟩ : syracuseStep 497759 = 746639) B746639
theorem B497819 : Blo 330750 497819 := bstep (se 1 (by rfl) ⟨373364, by rfl⟩ : syracuseStep 497819 = 746729) B746729
theorem B333979 : Blo 330750 333979 := bstep (se 1 (by rfl) ⟨250484, by rfl⟩ : syracuseStep 333979 = 500969) B500969
theorem B497855 : Blo 330750 497855 := bstep (se 1 (by rfl) ⟨373391, by rfl⟩ : syracuseStep 497855 = 746783) B746783
theorem B334015 : Blo 330750 334015 := bstep (se 1 (by rfl) ⟨250511, by rfl⟩ : syracuseStep 334015 = 501023) B501023
theorem B497897 : Blo 330750 497897 := bstep (se 2 (by rfl) ⟨186711, by rfl⟩ : syracuseStep 497897 = 373423) B373423
theorem B1120499 : Blo 330750 1120499 := bstep (se 1 (by rfl) ⟨840374, by rfl⟩ : syracuseStep 1120499 = 1680749) B1680749
theorem B3774761 : Blo 330750 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B1120553 : Blo 330750 1120553 := bstep (se 2 (by rfl) ⟨420207, by rfl⟩ : syracuseStep 1120553 = 840415) B840415
theorem B563503 : Blo 330750 563503 := bstep (se 1 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 563503 = 845255) B845255
theorem B334127 : Blo 330750 334127 := bstep (se 1 (by rfl) ⟨250595, by rfl⟩ : syracuseStep 334127 = 501191) B501191
theorem B21142037 : Blo 330750 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B498203 : Blo 330750 498203 := bstep (se 1 (by rfl) ⟨373652, by rfl⟩ : syracuseStep 498203 = 747305) B747305
theorem B334363 : Blo 330750 334363 := bstep (se 1 (by rfl) ⟨250772, by rfl⟩ : syracuseStep 334363 = 501545) B501545
theorem B334367 : Blo 330750 334367 := bstep (se 1 (by rfl) ⟨250775, by rfl⟩ : syracuseStep 334367 = 501551) B501551
theorem B498281 : Blo 330750 498281 := bstep (se 2 (by rfl) ⟨186855, by rfl⟩ : syracuseStep 498281 = 373711) B373711
theorem B564023 : Blo 330750 564023 := bstep (se 1 (by rfl) ⟨423017, by rfl⟩ : syracuseStep 564023 = 846035) B846035
theorem B334683 : Blo 330750 334683 := bstep (se 1 (by rfl) ⟨251012, by rfl⟩ : syracuseStep 334683 = 502025) B502025
theorem B1710953 : Blo 330750 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B2136941 : Blo 330750 2136941 := bstep (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) B801353
theorem B498809 : Blo 330750 498809 := bstep (se 2 (by rfl) ⟨187053, by rfl⟩ : syracuseStep 498809 = 374107) B374107
theorem B1678481 : Blo 330750 1678481 := bstep (se 2 (by rfl) ⟨629430, by rfl⟩ : syracuseStep 1678481 = 1258861) B1258861
theorem B498911 : Blo 330750 498911 := bstep (se 1 (by rfl) ⟨374183, by rfl⟩ : syracuseStep 498911 = 748367) B748367
theorem B2891009 : Blo 330750 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B498953 : Blo 330750 498953 := bstep (se 2 (by rfl) ⟨187107, by rfl⟩ : syracuseStep 498953 = 374215) B374215
theorem B499055 : Blo 330750 499055 := bstep (se 1 (by rfl) ⟨374291, by rfl⟩ : syracuseStep 499055 = 748583) B748583
theorem B499175 : Blo 330750 499175 := bstep (se 1 (by rfl) ⟨374381, by rfl⟩ : syracuseStep 499175 = 748763) B748763
theorem B564799 : Blo 330750 564799 := bstep (se 1 (by rfl) ⟨423599, by rfl⟩ : syracuseStep 564799 = 847199) B847199
theorem B499307 : Blo 330750 499307 := bstep (se 1 (by rfl) ⟨374480, by rfl⟩ : syracuseStep 499307 = 748961) B748961
theorem B499433 : Blo 330750 499433 := bstep (se 2 (by rfl) ⟨187287, by rfl⟩ : syracuseStep 499433 = 374575) B374575
theorem B1122119 : Blo 330750 1122119 := bstep (se 1 (by rfl) ⟨841589, by rfl⟩ : syracuseStep 1122119 = 1683179) B1683179
theorem B499577 : Blo 330750 499577 := bstep (se 2 (by rfl) ⟨187341, by rfl⟩ : syracuseStep 499577 = 374683) B374683
theorem B1122173 : Blo 330750 1122173 := bstep (se 3 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 1122173 = 420815) B420815
theorem B499679 : Blo 330750 499679 := bstep (se 1 (by rfl) ⟨374759, by rfl⟩ : syracuseStep 499679 = 749519) B749519
theorem B1122443 : Blo 330750 1122443 := bstep (se 1 (by rfl) ⟨841832, by rfl⟩ : syracuseStep 1122443 = 1683665) B1683665
theorem B631003 : Blo 330750 631003 := bstep (se 1 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 631003 = 946505) B946505
theorem B499931 : Blo 330750 499931 := bstep (se 1 (by rfl) ⟨374948, by rfl⟩ : syracuseStep 499931 = 749897) B749897
theorem B499943 : Blo 330750 499943 := bstep (se 1 (by rfl) ⟨374957, by rfl⟩ : syracuseStep 499943 = 749915) B749915
theorem B4792607 : Blo 330750 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B500105 : Blo 330750 500105 := bstep (se 2 (by rfl) ⟨187539, by rfl⟩ : syracuseStep 500105 = 375079) B375079
theorem B1122767 : Blo 330750 1122767 := bstep (se 1 (by rfl) ⟨842075, by rfl⟩ : syracuseStep 1122767 = 1684151) B1684151
theorem B500201 : Blo 330750 500201 := bstep (se 2 (by rfl) ⟨187575, by rfl⟩ : syracuseStep 500201 = 375151) B375151
theorem B500327 : Blo 330750 500327 := bstep (se 1 (by rfl) ⟨375245, by rfl⟩ : syracuseStep 500327 = 750491) B750491
theorem B500459 : Blo 330750 500459 := bstep (se 1 (by rfl) ⟨375344, by rfl⟩ : syracuseStep 500459 = 750689) B750689
theorem B500489 : Blo 330750 500489 := bstep (se 2 (by rfl) ⟨187683, by rfl⟩ : syracuseStep 500489 = 375367) B375367
theorem B1123091 : Blo 330750 1123091 := bstep (se 1 (by rfl) ⟨842318, by rfl⟩ : syracuseStep 1123091 = 1684637) B1684637
theorem B500591 : Blo 330750 500591 := bstep (se 1 (by rfl) ⟨375443, by rfl⟩ : syracuseStep 500591 = 750887) B750887
theorem B500843 : Blo 330750 500843 := bstep (se 1 (by rfl) ⟨375632, by rfl⟩ : syracuseStep 500843 = 751265) B751265
theorem B4302071 : Blo 330750 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B501083 : Blo 330750 501083 := bstep (se 1 (by rfl) ⟨375812, by rfl⟩ : syracuseStep 501083 = 751625) B751625
theorem B3614215 : Blo 330750 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B1680911 : Blo 330750 1680911 := bstep (se 1 (by rfl) ⟨1260683, by rfl⟩ : syracuseStep 1680911 = 2521367) B2521367
theorem B501359 : Blo 330750 501359 := bstep (se 1 (by rfl) ⟨376019, by rfl⟩ : syracuseStep 501359 = 752039) B752039
theorem B1123955 : Blo 330750 1123955 := bstep (se 1 (by rfl) ⟨842966, by rfl⟩ : syracuseStep 1123955 = 1685933) B1685933
theorem B501431 : Blo 330750 501431 := bstep (se 1 (by rfl) ⟨376073, by rfl⟩ : syracuseStep 501431 = 752147) B752147
theorem B4794041 : Blo 330750 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B501467 : Blo 330750 501467 := bstep (se 1 (by rfl) ⟨376100, by rfl⟩ : syracuseStep 501467 = 752201) B752201
theorem B1124063 : Blo 330750 1124063 := bstep (se 1 (by rfl) ⟨843047, by rfl⟩ : syracuseStep 1124063 = 1686095) B1686095
theorem B1353503 : Blo 330750 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B1124225 : Blo 330750 1124225 := bstep (se 2 (by rfl) ⟨421584, by rfl⟩ : syracuseStep 1124225 = 843169) B843169
theorem B501641 : Blo 330750 501641 := bstep (se 2 (by rfl) ⟨188115, by rfl⟩ : syracuseStep 501641 = 376231) B376231
theorem B501743 : Blo 330750 501743 := bstep (se 1 (by rfl) ⟨376307, by rfl⟩ : syracuseStep 501743 = 752615) B752615
theorem B534671 : Blo 330750 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B501995 : Blo 330750 501995 := bstep (se 1 (by rfl) ⟨376496, by rfl⟩ : syracuseStep 501995 = 752993) B752993
theorem B502055 : Blo 330750 502055 := bstep (se 1 (by rfl) ⟨376541, by rfl⟩ : syracuseStep 502055 = 753083) B753083
theorem B1681721 : Blo 330750 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B2173241 : Blo 330750 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B2140505 : Blo 330750 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B1124765 : Blo 330750 1124765 := bstep (se 3 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 1124765 = 421787) B421787
theorem B5712443 : Blo 330750 5712443 := bstep (se 1 (by rfl) ⟨4284332, by rfl⟩ : syracuseStep 5712443 = 8568665) B8568665
theorem B3779135 : Blo 330750 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B535177 : Blo 330750 535177 := bstep (se 2 (by rfl) ⟨200691, by rfl⟩ : syracuseStep 535177 = 401383) B401383
theorem B1125035 : Blo 330750 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B1682369 : Blo 330750 1682369 := bstep (se 2 (by rfl) ⟨630888, by rfl⟩ : syracuseStep 1682369 = 1261777) B1261777
theorem B4041667 : Blo 330750 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B633835 : Blo 330750 633835 := bstep (se 1 (by rfl) ⟨475376, by rfl⟩ : syracuseStep 633835 = 950753) B950753
theorem B1059961 : Blo 330750 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B1125575 : Blo 330750 1125575 := bstep (se 1 (by rfl) ⟨844181, by rfl⟩ : syracuseStep 1125575 = 1688363) B1688363
theorem B4566365 : Blo 330750 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B372199 : Blo 330750 372199 := bstep (se 1 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 372199 = 558299) B558299
theorem B1683017 : Blo 330750 1683017 := bstep (se 2 (by rfl) ⟨631131, by rfl⟩ : syracuseStep 1683017 = 1262263) B1262263
theorem B1060627 : Blo 330750 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B372703 : Blo 330750 372703 := bstep (se 1 (by rfl) ⟨279527, by rfl⟩ : syracuseStep 372703 = 559055) B559055
theorem B569311 : Blo 330750 569311 := bstep (se 1 (by rfl) ⟨426983, by rfl⟩ : syracuseStep 569311 = 853967) B853967
theorem B1126871 : Blo 330750 1126871 := bstep (se 1 (by rfl) ⟨845153, by rfl⟩ : syracuseStep 1126871 = 1690307) B1690307
theorem B1356371 : Blo 330750 1356371 := bstep (se 1 (by rfl) ⟨1017278, by rfl⟩ : syracuseStep 1356371 = 2034557) B2034557
theorem B373351 : Blo 330750 373351 := bstep (se 1 (by rfl) ⟨280013, by rfl⟩ : syracuseStep 373351 = 560027) B560027
theorem B2405153 : Blo 330750 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B1192745 : Blo 330750 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B3191723 : Blo 330750 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B799739 : Blo 330750 799739 := bstep (se 1 (by rfl) ⟨599804, by rfl⟩ : syracuseStep 799739 = 1199609) B1199609
theorem B767083 : Blo 330750 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B1128329 : Blo 330750 1128329 := bstep (se 2 (by rfl) ⟨423123, by rfl⟩ : syracuseStep 1128329 = 846247) B846247
theorem B1128545 : Blo 330750 1128545 := bstep (se 2 (by rfl) ⟨423204, by rfl⟩ : syracuseStep 1128545 = 846409) B846409
theorem B1685609 : Blo 330750 1685609 := bstep (se 2 (by rfl) ⟨632103, by rfl⟩ : syracuseStep 1685609 = 1264207) B1264207
theorem B506011 : Blo 330750 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B2013443 : Blo 330750 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B7649579 : Blo 330750 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1259819 : Blo 330750 1259819 := bstep (se 1 (by rfl) ⟨944864, by rfl⟩ : syracuseStep 1259819 = 1889729) B1889729
theorem B2144627 : Blo 330750 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B1129463 : Blo 330750 1129463 := bstep (se 1 (by rfl) ⟨847097, by rfl⟩ : syracuseStep 1129463 = 1694195) B1694195
theorem B4308299 : Blo 330750 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B376411 : Blo 330750 376411 := bstep (se 1 (by rfl) ⟨282308, by rfl⟩ : syracuseStep 376411 = 564617) B564617
theorem B475103 : Blo 330750 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B1196495 : Blo 330750 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B2015873 : Blo 330750 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B2704175 : Blo 330750 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1426319 : Blo 330750 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B378031 : Blo 330750 378031 := bstep (se 1 (by rfl) ⟨283523, by rfl⟩ : syracuseStep 378031 = 567047) B567047
theorem B837287 : Blo 330750 837287 := bstep (se 1 (by rfl) ⟨627965, by rfl⟩ : syracuseStep 837287 = 1255931) B1255931
theorem B4769711 : Blo 330750 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B837823 : Blo 330750 837823 := bstep (se 1 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 837823 = 1256735) B1256735
theorem B903383 : Blo 330750 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B837935 : Blo 330750 837935 := bstep (se 1 (by rfl) ⟨628451, by rfl⟩ : syracuseStep 837935 = 1256903) B1256903
theorem B1427975 : Blo 330750 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B2411153 : Blo 330750 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B4770515 : Blo 330750 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B707563 : Blo 330750 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B838937 : Blo 330750 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B2313641 : Blo 330750 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B1199549 : Blo 330750 1199549 := bstep (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) B449831
theorem B4279823 : Blo 330750 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B7818767 : Blo 330750 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B839231 : Blo 330750 839231 := bstep (se 1 (by rfl) ⟨629423, by rfl⟩ : syracuseStep 839231 = 1258847) B1258847
theorem B839443 : Blo 330750 839443 := bstep (se 1 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 839443 = 1259165) B1259165
theorem B2936737 : Blo 330750 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B3396167 : Blo 330750 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B1790761 : Blo 330750 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B840577 : Blo 330750 840577 := bstep (se 2 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 840577 = 630433) B630433
theorem B3429371 : Blo 330750 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B841387 : Blo 330750 841387 := bstep (se 1 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 841387 = 1262081) B1262081
theorem B841691 : Blo 330750 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B841711 : Blo 330750 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B841823 : Blo 330750 841823 := bstep (se 1 (by rfl) ⟨631367, by rfl⟩ : syracuseStep 841823 = 1262735) B1262735
theorem B3037607 : Blo 330750 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B9558557 : Blo 330750 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B4119113 : Blo 330750 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1202809 : Blo 330750 1202809 := bstep (se 2 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 1202809 = 902107) B902107
theorem B14605379 : Blo 330750 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B2120843 : Blo 330750 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B2841803 : Blo 330750 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B1596631 : Blo 330750 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B744713 : Blo 330750 744713 := bstep (se 2 (by rfl) ⟨279267, by rfl⟩ : syracuseStep 744713 = 558535) B558535
theorem B843119 : Blo 330750 843119 := bstep (se 1 (by rfl) ⟨632339, by rfl⟩ : syracuseStep 843119 = 1264679) B1264679
theorem B3792257 : Blo 330750 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B1892119 : Blo 330750 1892119 := bstep (se 1 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 1892119 = 2838179) B2838179
theorem B1433639 : Blo 330750 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B4808803 : Blo 330750 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B17817731 : Blo 330750 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B745703 : Blo 330750 745703 := bstep (se 1 (by rfl) ⟨559277, by rfl⟩ : syracuseStep 745703 = 1118555) B1118555
theorem B942587 : Blo 330750 942587 := bstep (se 1 (by rfl) ⟨706940, by rfl⟩ : syracuseStep 942587 = 1413881) B1413881
theorem B17621651 : Blo 330750 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B1270525 : Blo 330750 1270525 := bstep (se 3 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 1270525 = 476447) B476447
theorem B746297 : Blo 330750 746297 := bstep (se 2 (by rfl) ⟨279861, by rfl⟩ : syracuseStep 746297 = 559723) B559723
theorem B746351 : Blo 330750 746351 := bstep (se 1 (by rfl) ⟨559763, by rfl⟩ : syracuseStep 746351 = 1119527) B1119527
theorem B1598363 : Blo 330750 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B418871 : Blo 330750 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B419023 : Blo 330750 419023 := bstep (se 1 (by rfl) ⟨314267, by rfl⟩ : syracuseStep 419023 = 628535) B628535
theorem B746927 : Blo 330750 746927 := bstep (se 1 (by rfl) ⟨560195, by rfl⟩ : syracuseStep 746927 = 1120391) B1120391
theorem B9561563 : Blo 330750 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B1140443 : Blo 330750 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B845599 : Blo 330750 845599 := bstep (se 1 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 845599 = 1268399) B1268399
theorem B419995 : Blo 330750 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B3795173 : Blo 330750 3795173 := bstep (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) B711595
theorem B747755 : Blo 330750 747755 := bstep (se 1 (by rfl) ⟨560816, by rfl⟩ : syracuseStep 747755 = 1121633) B1121633
theorem B846895 : Blo 330750 846895 := bstep (se 1 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 846895 = 1270343) B1270343
theorem B749051 : Blo 330750 749051 := bstep (se 1 (by rfl) ⟨561788, by rfl⟩ : syracuseStep 749051 = 1123577) B1123577
theorem B1895993 : Blo 330750 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B749231 : Blo 330750 749231 := bstep (se 1 (by rfl) ⟨561923, by rfl⟩ : syracuseStep 749231 = 1123847) B1123847
theorem B1961903 : Blo 330750 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B749879 : Blo 330750 749879 := bstep (se 1 (by rfl) ⟨562409, by rfl⟩ : syracuseStep 749879 = 1124819) B1124819
theorem B749951 : Blo 330750 749951 := bstep (se 1 (by rfl) ⟨562463, by rfl⟩ : syracuseStep 749951 = 1124927) B1124927
theorem B2126483 : Blo 330750 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B7205597 : Blo 330750 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B3798089 : Blo 330750 3798089 := bstep (se 2 (by rfl) ⟨1424283, by rfl⟩ : syracuseStep 3798089 = 2848567) B2848567
theorem B652463 : Blo 330750 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B2389297 : Blo 330750 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B6387133 : Blo 330750 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B3601853 : Blo 330750 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B751175 : Blo 330750 751175 := bstep (se 1 (by rfl) ⟨563381, by rfl⟩ : syracuseStep 751175 = 1126763) B1126763
theorem B751355 : Blo 330750 751355 := bstep (se 1 (by rfl) ⟨563516, by rfl⟩ : syracuseStep 751355 = 1127033) B1127033
theorem B947963 : Blo 330750 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B1898477 : Blo 330750 1898477 := bstep (se 3 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 1898477 = 711929) B711929
theorem B2390309 : Blo 330750 2390309 := bstep (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) B448183
theorem B751913 : Blo 330750 751913 := bstep (se 2 (by rfl) ⟨281967, by rfl⟩ : syracuseStep 751913 = 563935) B563935
theorem B3603143 : Blo 330750 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B752489 : Blo 330750 752489 := bstep (se 2 (by rfl) ⟨282183, by rfl⟩ : syracuseStep 752489 = 564367) B564367
theorem B752543 : Blo 330750 752543 := bstep (se 1 (by rfl) ⟨564407, by rfl⟩ : syracuseStep 752543 = 1128815) B1128815
theorem B851699 : Blo 330750 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B12451843 : Blo 330750 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B1343915 : Blo 330750 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B1802783 : Blo 330750 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B950879 : Blo 330750 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B558191 : Blo 330750 558191 := bstep (se 1 (by rfl) ⟨418643, by rfl⟩ : syracuseStep 558191 = 837287) B837287
theorem B3179807 : Blo 330750 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B558623 : Blo 330750 558623 := bstep (se 1 (by rfl) ⟨418967, by rfl⟩ : syracuseStep 558623 = 837935) B837935
theorem B558697 : Blo 330750 558697 := bstep (se 2 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 558697 = 419023) B419023
theorem B951983 : Blo 330750 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B1607435 : Blo 330750 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B3180343 : Blo 330750 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B4818953 : Blo 330750 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B559291 : Blo 330750 559291 := bstep (se 1 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 559291 = 838937) B838937
theorem B2853215 : Blo 330750 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B5212511 : Blo 330750 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B559487 : Blo 330750 559487 := bstep (se 1 (by rfl) ⟨419615, by rfl⟩ : syracuseStep 559487 = 839231) B839231
theorem B19466795 : Blo 330750 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B1116989 : Blo 330750 1116989 := bstep (se 3 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 1116989 = 418871) B418871
theorem B559993 : Blo 330750 559993 := bstep (se 2 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 559993 = 419995) B419995
theorem B1117097 : Blo 330750 1117097 := bstep (se 2 (by rfl) ⟨418911, by rfl⟩ : syracuseStep 1117097 = 837823) B837823
theorem B2264111 : Blo 330750 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B330815 : Blo 330750 330815 := bstep (se 1 (by rfl) ⟨248111, by rfl⟩ : syracuseStep 330815 = 496223) B496223
theorem B331135 : Blo 330750 331135 := bstep (se 1 (by rfl) ⟨248351, by rfl⟩ : syracuseStep 331135 = 496703) B496703
theorem B2854277 : Blo 330750 2854277 := bstep (se 4 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 2854277 = 535177) B535177
theorem B331163 : Blo 330750 331163 := bstep (se 1 (by rfl) ⟨248372, by rfl⟩ : syracuseStep 331163 = 496745) B496745
theorem B331231 : Blo 330750 331231 := bstep (se 1 (by rfl) ⟨248423, by rfl⟩ : syracuseStep 331231 = 496847) B496847
theorem B331367 : Blo 330750 331367 := bstep (se 1 (by rfl) ⟨248525, by rfl⟩ : syracuseStep 331367 = 497051) B497051
theorem B331515 : Blo 330750 331515 := bstep (se 1 (by rfl) ⟨248636, by rfl⟩ : syracuseStep 331515 = 497273) B497273
theorem B331583 : Blo 330750 331583 := bstep (se 1 (by rfl) ⟨248687, by rfl⟩ : syracuseStep 331583 = 497375) B497375
theorem B2428795 : Blo 330750 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B331647 : Blo 330750 331647 := bstep (se 1 (by rfl) ⟨248735, by rfl⟩ : syracuseStep 331647 = 497471) B497471
theorem B561127 : Blo 330750 561127 := bstep (se 1 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 561127 = 841691) B841691
theorem B331759 : Blo 330750 331759 := bstep (se 1 (by rfl) ⟨248819, by rfl⟩ : syracuseStep 331759 = 497639) B497639
theorem B331771 : Blo 330750 331771 := bstep (se 1 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 331771 = 497657) B497657
theorem B331839 : Blo 330750 331839 := bstep (se 1 (by rfl) ⟨248879, by rfl⟩ : syracuseStep 331839 = 497759) B497759
theorem B561215 : Blo 330750 561215 := bstep (se 1 (by rfl) ⟨420911, by rfl⟩ : syracuseStep 561215 = 841823) B841823
theorem B331879 : Blo 330750 331879 := bstep (se 1 (by rfl) ⟨248909, by rfl⟩ : syracuseStep 331879 = 497819) B497819
theorem B331903 : Blo 330750 331903 := bstep (se 1 (by rfl) ⟨248927, by rfl⟩ : syracuseStep 331903 = 497855) B497855
theorem B331931 : Blo 330750 331931 := bstep (se 1 (by rfl) ⟨248948, by rfl⟩ : syracuseStep 331931 = 497897) B497897
theorem B1413281 : Blo 330750 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B14094691 : Blo 330750 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B332135 : Blo 330750 332135 := bstep (se 1 (by rfl) ⟨249101, by rfl⟩ : syracuseStep 332135 = 498203) B498203
theorem B332187 : Blo 330750 332187 := bstep (se 1 (by rfl) ⟨249140, by rfl⟩ : syracuseStep 332187 = 498281) B498281
theorem B496265 : Blo 330750 496265 := bstep (se 2 (by rfl) ⟨186099, by rfl⟩ : syracuseStep 496265 = 372199) B372199
theorem B9736919 : Blo 330750 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B332539 : Blo 330750 332539 := bstep (se 1 (by rfl) ⟨249404, by rfl⟩ : syracuseStep 332539 = 498809) B498809
theorem B1118987 : Blo 330750 1118987 := bstep (se 1 (by rfl) ⟨839240, by rfl⟩ : syracuseStep 1118987 = 1678481) B1678481
theorem B332607 : Blo 330750 332607 := bstep (se 1 (by rfl) ⟨249455, by rfl⟩ : syracuseStep 332607 = 498911) B498911
theorem B496475 : Blo 330750 496475 := bstep (se 1 (by rfl) ⟨372356, by rfl⟩ : syracuseStep 496475 = 744713) B744713
theorem B332635 : Blo 330750 332635 := bstep (se 1 (by rfl) ⟨249476, by rfl⟩ : syracuseStep 332635 = 498953) B498953
theorem B332703 : Blo 330750 332703 := bstep (se 1 (by rfl) ⟨249527, by rfl⟩ : syracuseStep 332703 = 499055) B499055
theorem B562079 : Blo 330750 562079 := bstep (se 1 (by rfl) ⟨421559, by rfl⟩ : syracuseStep 562079 = 843119) B843119
theorem B2528171 : Blo 330750 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B332783 : Blo 330750 332783 := bstep (se 1 (by rfl) ⟨249587, by rfl⟩ : syracuseStep 332783 = 499175) B499175
theorem B1414169 : Blo 330750 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B1119257 : Blo 330750 1119257 := bstep (se 2 (by rfl) ⟨419721, by rfl⟩ : syracuseStep 1119257 = 839443) B839443
theorem B332871 : Blo 330750 332871 := bstep (se 1 (by rfl) ⟨249653, by rfl⟩ : syracuseStep 332871 = 499307) B499307
theorem B332955 : Blo 330750 332955 := bstep (se 1 (by rfl) ⟨249716, by rfl⟩ : syracuseStep 332955 = 499433) B499433
theorem B333051 : Blo 330750 333051 := bstep (se 1 (by rfl) ⟨249788, by rfl⟩ : syracuseStep 333051 = 499577) B499577
theorem B496937 : Blo 330750 496937 := bstep (se 2 (by rfl) ⟨186351, by rfl⟩ : syracuseStep 496937 = 372703) B372703
theorem B333119 : Blo 330750 333119 := bstep (se 1 (by rfl) ⟨249839, by rfl⟩ : syracuseStep 333119 = 499679) B499679
theorem B333287 : Blo 330750 333287 := bstep (se 1 (by rfl) ⟨249965, by rfl⟩ : syracuseStep 333287 = 499931) B499931
theorem B497135 : Blo 330750 497135 := bstep (se 1 (by rfl) ⟨372851, by rfl⟩ : syracuseStep 497135 = 745703) B745703
theorem B333295 : Blo 330750 333295 := bstep (se 1 (by rfl) ⟨249971, by rfl⟩ : syracuseStep 333295 = 499943) B499943
theorem B333403 : Blo 330750 333403 := bstep (se 1 (by rfl) ⟨250052, by rfl⟩ : syracuseStep 333403 = 500105) B500105
theorem B333467 : Blo 330750 333467 := bstep (se 1 (by rfl) ⟨250100, by rfl⟩ : syracuseStep 333467 = 500201) B500201
theorem B628391 : Blo 330750 628391 := bstep (se 1 (by rfl) ⟨471293, by rfl⟩ : syracuseStep 628391 = 942587) B942587
theorem B333551 : Blo 330750 333551 := bstep (se 1 (by rfl) ⟨250163, by rfl⟩ : syracuseStep 333551 = 500327) B500327
theorem B333639 : Blo 330750 333639 := bstep (se 1 (by rfl) ⟨250229, by rfl⟩ : syracuseStep 333639 = 500459) B500459
theorem B333659 : Blo 330750 333659 := bstep (se 1 (by rfl) ⟨250244, by rfl⟩ : syracuseStep 333659 = 500489) B500489
theorem B497531 : Blo 330750 497531 := bstep (se 1 (by rfl) ⟨373148, by rfl⟩ : syracuseStep 497531 = 746297) B746297
theorem B497567 : Blo 330750 497567 := bstep (se 1 (by rfl) ⟨373175, by rfl⟩ : syracuseStep 497567 = 746351) B746351
theorem B333727 : Blo 330750 333727 := bstep (se 1 (by rfl) ⟨250295, by rfl⟩ : syracuseStep 333727 = 500591) B500591
theorem B333895 : Blo 330750 333895 := bstep (se 1 (by rfl) ⟨250421, by rfl⟩ : syracuseStep 333895 = 500843) B500843
theorem B497801 : Blo 330750 497801 := bstep (se 2 (by rfl) ⟨186675, by rfl⟩ : syracuseStep 497801 = 373351) B373351
theorem B334055 : Blo 330750 334055 := bstep (se 1 (by rfl) ⟨250541, by rfl⟩ : syracuseStep 334055 = 501083) B501083
theorem B497951 : Blo 330750 497951 := bstep (se 1 (by rfl) ⟨373463, by rfl⟩ : syracuseStep 497951 = 746927) B746927
theorem B1120607 : Blo 330750 1120607 := bstep (se 1 (by rfl) ⟨840455, by rfl⟩ : syracuseStep 1120607 = 1680911) B1680911
theorem B334239 : Blo 330750 334239 := bstep (se 1 (by rfl) ⟨250679, by rfl⟩ : syracuseStep 334239 = 501359) B501359
theorem B334287 : Blo 330750 334287 := bstep (se 1 (by rfl) ⟨250715, by rfl⟩ : syracuseStep 334287 = 501431) B501431
theorem B760295 : Blo 330750 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B334311 : Blo 330750 334311 := bstep (se 1 (by rfl) ⟨250733, by rfl⟩ : syracuseStep 334311 = 501467) B501467
theorem B1120769 : Blo 330750 1120769 := bstep (se 2 (by rfl) ⟨420288, by rfl⟩ : syracuseStep 1120769 = 840577) B840577
theorem B334427 : Blo 330750 334427 := bstep (se 1 (by rfl) ⟨250820, by rfl⟩ : syracuseStep 334427 = 501641) B501641
theorem B334495 : Blo 330750 334495 := bstep (se 1 (by rfl) ⟨250871, by rfl⟩ : syracuseStep 334495 = 501743) B501743
theorem B1022777 : Blo 330750 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B2530115 : Blo 330750 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B498503 : Blo 330750 498503 := bstep (se 1 (by rfl) ⟨373877, by rfl⟩ : syracuseStep 498503 = 747755) B747755
theorem B334663 : Blo 330750 334663 := bstep (se 1 (by rfl) ⟨250997, by rfl⟩ : syracuseStep 334663 = 501995) B501995
theorem B334703 : Blo 330750 334703 := bstep (se 1 (by rfl) ⟨251027, by rfl⟩ : syracuseStep 334703 = 502055) B502055
theorem B1121147 : Blo 330750 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B3808295 : Blo 330750 3808295 := bstep (se 1 (by rfl) ⟨2856221, by rfl⟩ : syracuseStep 3808295 = 5712443) B5712443
theorem B3185729 : Blo 330750 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B9608381 : Blo 330750 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B1121579 : Blo 330750 1121579 := bstep (se 1 (by rfl) ⟨841184, by rfl⟩ : syracuseStep 1121579 = 1682369) B1682369
theorem B1121849 : Blo 330750 1121849 := bstep (se 2 (by rfl) ⟨420693, by rfl⟩ : syracuseStep 1121849 = 841387) B841387
theorem B499367 : Blo 330750 499367 := bstep (se 1 (by rfl) ⟨374525, by rfl⟩ : syracuseStep 499367 = 749051) B749051
theorem B1122011 : Blo 330750 1122011 := bstep (se 1 (by rfl) ⟨841508, by rfl⟩ : syracuseStep 1122011 = 1683017) B1683017
theorem B499487 : Blo 330750 499487 := bstep (se 1 (by rfl) ⟨374615, by rfl⟩ : syracuseStep 499487 = 749231) B749231
theorem B1122281 : Blo 330750 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B499919 : Blo 330750 499919 := bstep (se 1 (by rfl) ⟨374939, by rfl⟩ : syracuseStep 499919 = 749879) B749879
theorem B499967 : Blo 330750 499967 := bstep (se 1 (by rfl) ⟨374975, by rfl⟩ : syracuseStep 499967 = 749951) B749951
theorem B1417655 : Blo 330750 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B795163 : Blo 330750 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B533159 : Blo 330750 533159 := bstep (se 1 (by rfl) ⟨399869, by rfl⟩ : syracuseStep 533159 = 799739) B799739
theorem B7709357 : Blo 330750 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B2532059 : Blo 330750 2532059 := bstep (se 1 (by rfl) ⟨1899044, by rfl⟩ : syracuseStep 2532059 = 3798089) B3798089
theorem B434975 : Blo 330750 434975 := bstep (se 1 (by rfl) ⟨326231, by rfl⟩ : syracuseStep 434975 = 652463) B652463
theorem B2401235 : Blo 330750 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B500783 : Blo 330750 500783 := bstep (se 1 (by rfl) ⟨375587, by rfl⟩ : syracuseStep 500783 = 751175) B751175
theorem B6169709 : Blo 330750 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B631975 : Blo 330750 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B500903 : Blo 330750 500903 := bstep (se 1 (by rfl) ⟨375677, by rfl⟩ : syracuseStep 500903 = 751355) B751355
theorem B1123739 : Blo 330750 1123739 := bstep (se 1 (by rfl) ⟨842804, by rfl⟩ : syracuseStep 1123739 = 1685609) B1685609
theorem B501275 : Blo 330750 501275 := bstep (se 1 (by rfl) ⟨375956, by rfl⟩ : syracuseStep 501275 = 751913) B751913
theorem B501659 : Blo 330750 501659 := bstep (se 1 (by rfl) ⟨376244, by rfl⟩ : syracuseStep 501659 = 752489) B752489
theorem B501695 : Blo 330750 501695 := bstep (se 1 (by rfl) ⟨376271, by rfl⟩ : syracuseStep 501695 = 752543) B752543
theorem B501881 : Blo 330750 501881 := bstep (se 2 (by rfl) ⟨188205, by rfl⟩ : syracuseStep 501881 = 376411) B376411
theorem B567799 : Blo 330750 567799 := bstep (se 1 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 567799 = 851699) B851699
theorem B1354427 : Blo 330750 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B797663 : Blo 330750 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B7777361 : Blo 330750 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B3583385 : Blo 330750 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B2534975 : Blo 330750 2534975 := bstep (se 1 (by rfl) ⟨1901231, by rfl⟩ : syracuseStep 2534975 = 3802463) B3802463
theorem B896939 : Blo 330750 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B602255 : Blo 330750 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B635111 : Blo 330750 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B504041 : Blo 330750 504041 := bstep (se 2 (by rfl) ⟨189015, by rfl⟩ : syracuseStep 504041 = 378031) B378031
theorem B3191075 : Blo 330750 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B2535947 : Blo 330750 2535947 := bstep (se 1 (by rfl) ⟨1901960, by rfl⟩ : syracuseStep 2535947 = 3803921) B3803921
theorem B373567 : Blo 330750 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B1815547 : Blo 330750 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B1684475 : Blo 330750 1684475 := bstep (se 1 (by rfl) ⟨1263356, by rfl⟩ : syracuseStep 1684475 = 2526713) B2526713
theorem B1127465 : Blo 330750 1127465 := bstep (se 2 (by rfl) ⟨422799, by rfl⟩ : syracuseStep 1127465 = 845599) B845599
theorem B373855 : Blo 330750 373855 := bstep (se 1 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 373855 = 560783) B560783
theorem B5388889 : Blo 330750 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B1129193 : Blo 330750 1129193 := bstep (se 2 (by rfl) ⟨423447, by rfl⟩ : syracuseStep 1129193 = 846895) B846895
theorem B6372371 : Blo 330750 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B376015 : Blo 330750 376015 := bstep (se 1 (by rfl) ⟨282011, by rfl⟩ : syracuseStep 376015 = 564023) B564023
theorem B1424627 : Blo 330750 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B3915649 : Blo 330750 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B11878487 : Blo 330750 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B3195071 : Blo 330750 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B11747767 : Blo 330750 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B1065575 : Blo 330750 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B2868047 : Blo 330750 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B6374375 : Blo 330750 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B3196027 : Blo 330750 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B902335 : Blo 330750 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B1427003 : Blo 330750 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B1263995 : Blo 330750 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B674681 : Blo 330750 674681 := bstep (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) B506011
theorem B5655581 : Blo 330750 5655581 := bstep (se 3 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 5655581 = 2120843) B2120843
theorem B904247 : Blo 330750 904247 := bstep (se 1 (by rfl) ⟨678185, by rfl⟩ : syracuseStep 904247 = 1356371) B1356371
theorem B4803731 : Blo 330750 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B3198797 : Blo 330750 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B4050917 : Blo 330750 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B1265651 : Blo 330750 1265651 := bstep (se 1 (by rfl) ⟨949238, by rfl⟩ : syracuseStep 1265651 = 1898477) B1898477
theorem B1593539 : Blo 330750 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B5099719 : Blo 330750 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B839879 : Blo 330750 839879 := bstep (se 1 (by rfl) ⟨629909, by rfl⟩ : syracuseStep 839879 = 1259819) B1259819
theorem B1429751 : Blo 330750 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B12145301 : Blo 330750 12145301 := bstep (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) B569311
theorem B2872199 : Blo 330750 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1266941 : Blo 330750 1266941 := bstep (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) B475103
theorem B3823037 : Blo 330750 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B6411737 : Blo 330750 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B841337 : Blo 330750 841337 := bstep (se 2 (by rfl) ⟨315501, by rfl⟩ : syracuseStep 841337 = 631003) B631003
theorem B2512619 : Blo 330750 2512619 := bstep (se 1 (by rfl) ⟨1884464, by rfl⟩ : syracuseStep 2512619 = 3768929) B3768929
theorem B1694033 : Blo 330750 1694033 := bstep (se 2 (by rfl) ⟨635262, by rfl⟩ : syracuseStep 1694033 = 1270525) B1270525
theorem B1071443 : Blo 330750 1071443 := bstep (se 1 (by rfl) ⟨803582, by rfl⟩ : syracuseStep 1071443 = 1607165) B1607165
theorem B744263 : Blo 330750 744263 := bstep (se 1 (by rfl) ⟨558197, by rfl⟩ : syracuseStep 744263 = 1116395) B1116395
theorem B6380369 : Blo 330750 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B744569 : Blo 330750 744569 := bstep (se 2 (by rfl) ⟨279213, by rfl⟩ : syracuseStep 744569 = 558427) B558427
theorem B6413741 : Blo 330750 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B1465847 : Blo 330750 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B745127 : Blo 330750 745127 := bstep (se 1 (by rfl) ⟨558845, by rfl⟩ : syracuseStep 745127 = 1117691) B1117691
theorem B745235 : Blo 330750 745235 := bstep (se 1 (by rfl) ⟨558926, by rfl⟩ : syracuseStep 745235 = 1117853) B1117853
theorem B745595 : Blo 330750 745595 := bstep (se 1 (by rfl) ⟨559196, by rfl⟩ : syracuseStep 745595 = 1118393) B1118393
theorem B745865 : Blo 330750 745865 := bstep (se 2 (by rfl) ⟨279699, by rfl⟩ : syracuseStep 745865 = 559399) B559399
theorem B2286247 : Blo 330750 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B943417 : Blo 330750 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B845113 : Blo 330750 845113 := bstep (se 2 (by rfl) ⟨316917, by rfl⟩ : syracuseStep 845113 = 633835) B633835
theorem B746999 : Blo 330750 746999 := bstep (se 1 (by rfl) ⟨560249, by rfl⟩ : syracuseStep 746999 = 1120499) B1120499
theorem B2516507 : Blo 330750 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B747035 : Blo 330750 747035 := bstep (se 1 (by rfl) ⟨560276, by rfl⟩ : syracuseStep 747035 = 1120553) B1120553
theorem B2025071 : Blo 330750 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B2746075 : Blo 330750 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1140635 : Blo 330750 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1894535 : Blo 330750 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B748025 : Blo 330750 748025 := bstep (se 2 (by rfl) ⟨280509, by rfl⟩ : syracuseStep 748025 = 561019) B561019
theorem B748079 : Blo 330750 748079 := bstep (se 1 (by rfl) ⟨561059, by rfl⟩ : syracuseStep 748079 = 1122119) B1122119
theorem B748115 : Blo 330750 748115 := bstep (se 1 (by rfl) ⟨561086, by rfl⟩ : syracuseStep 748115 = 1122173) B1122173
theorem B748295 : Blo 330750 748295 := bstep (se 1 (by rfl) ⟨561221, by rfl⟩ : syracuseStep 748295 = 1122443) B1122443
theorem B748511 : Blo 330750 748511 := bstep (se 1 (by rfl) ⟨561383, by rfl⟩ : syracuseStep 748511 = 1122767) B1122767
theorem B748727 : Blo 330750 748727 := bstep (se 1 (by rfl) ⟨561545, by rfl⟩ : syracuseStep 748727 = 1123091) B1123091
theorem B5795309 : Blo 330750 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B2387681 : Blo 330750 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B749303 : Blo 330750 749303 := bstep (se 1 (by rfl) ⟨561977, by rfl⟩ : syracuseStep 749303 = 1123955) B1123955
theorem B749375 : Blo 330750 749375 := bstep (se 1 (by rfl) ⟨562031, by rfl⟩ : syracuseStep 749375 = 1124063) B1124063
theorem B749483 : Blo 330750 749483 := bstep (se 1 (by rfl) ⟨562112, by rfl⟩ : syracuseStep 749483 = 1124225) B1124225
theorem B356447 : Blo 330750 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B749843 : Blo 330750 749843 := bstep (se 1 (by rfl) ⟨562382, by rfl⟩ : syracuseStep 749843 = 1124765) B1124765
theorem B2519423 : Blo 330750 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B750023 : Blo 330750 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B8516177 : Blo 330750 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B750383 : Blo 330750 750383 := bstep (se 1 (by rfl) ⟨562787, by rfl⟩ : syracuseStep 750383 = 1125575) B1125575
theorem B750473 : Blo 330750 750473 := bstep (se 2 (by rfl) ⟨281427, by rfl⟩ : syracuseStep 750473 = 562855) B562855
theorem B3044243 : Blo 330750 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B1307935 : Blo 330750 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B751247 : Blo 330750 751247 := bstep (se 1 (by rfl) ⟨563435, by rfl⟩ : syracuseStep 751247 = 1126871) B1126871
theorem B751337 : Blo 330750 751337 := bstep (se 2 (by rfl) ⟨281751, by rfl⟩ : syracuseStep 751337 = 563503) B563503
theorem B2127815 : Blo 330750 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B1603745 : Blo 330750 1603745 := bstep (se 2 (by rfl) ⟨601404, by rfl⟩ : syracuseStep 1603745 = 1202809) B1202809
theorem B752219 : Blo 330750 752219 := bstep (se 1 (by rfl) ⟨564164, by rfl⟩ : syracuseStep 752219 = 1128329) B1128329
theorem B752363 : Blo 330750 752363 := bstep (se 1 (by rfl) ⟨564272, by rfl⟩ : syracuseStep 752363 = 1128545) B1128545
theorem B1342295 : Blo 330750 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B2128841 : Blo 330750 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B752975 : Blo 330750 752975 := bstep (se 1 (by rfl) ⟨564731, by rfl⟩ : syracuseStep 752975 = 1129463) B1129463
theorem B753065 : Blo 330750 753065 := bstep (se 2 (by rfl) ⟨282399, by rfl⟩ : syracuseStep 753065 = 564799) B564799
theorem B2522825 : Blo 330750 2522825 := bstep (se 2 (by rfl) ⟨946059, by rfl⟩ : syracuseStep 2522825 = 1892119) B1892119
theorem B2130047 : Blo 330750 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B950525 : Blo 330750 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B15663689 : Blo 330750 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B1344109 : Blo 330750 1344109 := bstep (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) B504041
theorem B3048329 : Blo 330750 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B951335 : Blo 330750 951335 := bstep (se 1 (by rfl) ⟨713501, by rfl⟩ : syracuseStep 951335 = 1427003) B1427003
theorem B3212635 : Blo 330750 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B4261369 : Blo 330750 4261369 := bstep (se 2 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 4261369 = 3196027) B3196027
theorem B1902143 : Blo 330750 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B3475007 : Blo 330750 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B12977863 : Blo 330750 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B75171685 : Blo 330750 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B3770387 : Blo 330750 3770387 := bstep (se 1 (by rfl) ⟨2827790, by rfl⟩ : syracuseStep 3770387 = 5655581) B5655581
theorem B1509407 : Blo 330750 1509407 := bstep (se 1 (by rfl) ⟨1132055, by rfl⟩ : syracuseStep 1509407 = 2264111) B2264111
theorem B1902851 : Blo 330750 1902851 := bstep (se 1 (by rfl) ⟨1427138, by rfl⟩ : syracuseStep 1902851 = 2854277) B2854277
theorem B2132531 : Blo 330750 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B559919 : Blo 330750 559919 := bstep (se 1 (by rfl) ⟨419939, by rfl⟩ : syracuseStep 559919 = 839879) B839879
theorem B330843 : Blo 330750 330843 := bstep (se 1 (by rfl) ⟨248132, by rfl⟩ : syracuseStep 330843 = 496265) B496265
theorem B8096867 : Blo 330750 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B6491279 : Blo 330750 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B330983 : Blo 330750 330983 := bstep (se 1 (by rfl) ⟨248237, by rfl⟩ : syracuseStep 330983 = 496475) B496475
theorem B331291 : Blo 330750 331291 := bstep (se 1 (by rfl) ⟨248468, by rfl⟩ : syracuseStep 331291 = 496937) B496937
theorem B331423 : Blo 330750 331423 := bstep (se 1 (by rfl) ⟨248567, by rfl⟩ : syracuseStep 331423 = 497135) B497135
theorem B560891 : Blo 330750 560891 := bstep (se 1 (by rfl) ⟨420668, by rfl⟩ : syracuseStep 560891 = 841337) B841337
theorem B1675079 : Blo 330750 1675079 := bstep (se 1 (by rfl) ⟨1256309, by rfl⟩ : syracuseStep 1675079 = 2512619) B2512619
theorem B331687 : Blo 330750 331687 := bstep (se 1 (by rfl) ⟨248765, by rfl⟩ : syracuseStep 331687 = 497531) B497531
theorem B331711 : Blo 330750 331711 := bstep (se 1 (by rfl) ⟨248783, by rfl⟩ : syracuseStep 331711 = 497567) B497567
theorem B331867 : Blo 330750 331867 := bstep (se 1 (by rfl) ⟨248900, by rfl⟩ : syracuseStep 331867 = 497801) B497801
theorem B331967 : Blo 330750 331967 := bstep (se 1 (by rfl) ⟨248975, by rfl⟩ : syracuseStep 331967 = 497951) B497951
theorem B496175 : Blo 330750 496175 := bstep (se 1 (by rfl) ⟨372131, by rfl⟩ : syracuseStep 496175 = 744263) B744263
theorem B332335 : Blo 330750 332335 := bstep (se 1 (by rfl) ⟨249251, by rfl⟩ : syracuseStep 332335 = 498503) B498503
theorem B496379 : Blo 330750 496379 := bstep (se 1 (by rfl) ⟨372284, by rfl⟩ : syracuseStep 496379 = 744569) B744569
theorem B496751 : Blo 330750 496751 := bstep (se 1 (by rfl) ⟨372563, by rfl⟩ : syracuseStep 496751 = 745127) B745127
theorem B332911 : Blo 330750 332911 := bstep (se 1 (by rfl) ⟨249683, by rfl⟩ : syracuseStep 332911 = 499367) B499367
theorem B496823 : Blo 330750 496823 := bstep (se 1 (by rfl) ⟨372617, by rfl⟩ : syracuseStep 496823 = 745235) B745235
theorem B332991 : Blo 330750 332991 := bstep (se 1 (by rfl) ⟨249743, by rfl⟩ : syracuseStep 332991 = 499487) B499487
theorem B497063 : Blo 330750 497063 := bstep (se 1 (by rfl) ⟨372797, by rfl⟩ : syracuseStep 497063 = 745595) B745595
theorem B333279 : Blo 330750 333279 := bstep (se 1 (by rfl) ⟨249959, by rfl⟩ : syracuseStep 333279 = 499919) B499919
theorem B333311 : Blo 330750 333311 := bstep (se 1 (by rfl) ⟨249983, by rfl⟩ : syracuseStep 333311 = 499967) B499967
theorem B497243 : Blo 330750 497243 := bstep (se 1 (by rfl) ⟨372932, by rfl⟩ : syracuseStep 497243 = 745865) B745865
theorem B333855 : Blo 330750 333855 := bstep (se 1 (by rfl) ⟨250391, by rfl⟩ : syracuseStep 333855 = 500783) B500783
theorem B333935 : Blo 330750 333935 := bstep (se 1 (by rfl) ⟨250451, by rfl⟩ : syracuseStep 333935 = 500903) B500903
theorem B497999 : Blo 330750 497999 := bstep (se 1 (by rfl) ⟨373499, by rfl⟩ : syracuseStep 497999 = 746999) B746999
theorem B1677671 : Blo 330750 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B498023 : Blo 330750 498023 := bstep (se 1 (by rfl) ⟨373517, by rfl⟩ : syracuseStep 498023 = 747035) B747035
theorem B334183 : Blo 330750 334183 := bstep (se 1 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 334183 = 501275) B501275
theorem B1350047 : Blo 330750 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B498089 : Blo 330750 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B760423 : Blo 330750 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B334439 : Blo 330750 334439 := bstep (se 1 (by rfl) ⟨250829, by rfl⟩ : syracuseStep 334439 = 501659) B501659
theorem B334463 : Blo 330750 334463 := bstep (se 1 (by rfl) ⟨250847, by rfl⟩ : syracuseStep 334463 = 501695) B501695
theorem B334587 : Blo 330750 334587 := bstep (se 1 (by rfl) ⟨250940, by rfl⟩ : syracuseStep 334587 = 501881) B501881
theorem B498473 : Blo 330750 498473 := bstep (se 2 (by rfl) ⟨186927, by rfl⟩ : syracuseStep 498473 = 373855) B373855
theorem B498683 : Blo 330750 498683 := bstep (se 1 (by rfl) ⟨374012, by rfl⟩ : syracuseStep 498683 = 748025) B748025
theorem B498719 : Blo 330750 498719 := bstep (se 1 (by rfl) ⟨374039, by rfl⟩ : syracuseStep 498719 = 748079) B748079
theorem B1743913 : Blo 330750 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B498743 : Blo 330750 498743 := bstep (se 1 (by rfl) ⟨374057, by rfl⟩ : syracuseStep 498743 = 748115) B748115
theorem B498863 : Blo 330750 498863 := bstep (se 1 (by rfl) ⟨374147, by rfl⟩ : syracuseStep 498863 = 748295) B748295
theorem B531775 : Blo 330750 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B499007 : Blo 330750 499007 := bstep (se 1 (by rfl) ⟨374255, by rfl⟩ : syracuseStep 499007 = 748511) B748511
theorem B499151 : Blo 330750 499151 := bstep (se 1 (by rfl) ⟨374363, by rfl⟩ : syracuseStep 499151 = 748727) B748727
theorem B499535 : Blo 330750 499535 := bstep (se 1 (by rfl) ⟨374651, by rfl⟩ : syracuseStep 499535 = 749303) B749303
theorem B499583 : Blo 330750 499583 := bstep (se 1 (by rfl) ⟨374687, by rfl⟩ : syracuseStep 499583 = 749375) B749375
theorem B597959 : Blo 330750 597959 := bstep (se 1 (by rfl) ⟨448469, by rfl⟩ : syracuseStep 597959 = 896939) B896939
theorem B499655 : Blo 330750 499655 := bstep (se 1 (by rfl) ⟨374741, by rfl⟩ : syracuseStep 499655 = 749483) B749483
theorem B401503 : Blo 330750 401503 := bstep (se 1 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 401503 = 602255) B602255
theorem B499895 : Blo 330750 499895 := bstep (se 1 (by rfl) ⟨374921, by rfl⟩ : syracuseStep 499895 = 749843) B749843
theorem B1679615 : Blo 330750 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B500015 : Blo 330750 500015 := bstep (se 1 (by rfl) ⟨375011, by rfl⟩ : syracuseStep 500015 = 750023) B750023
theorem B5677451 : Blo 330750 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B500255 : Blo 330750 500255 := bstep (se 1 (by rfl) ⟨375191, by rfl⟩ : syracuseStep 500255 = 750383) B750383
theorem B500315 : Blo 330750 500315 := bstep (se 1 (by rfl) ⟨375236, by rfl⟩ : syracuseStep 500315 = 750473) B750473
theorem B1122983 : Blo 330750 1122983 := bstep (se 1 (by rfl) ⟨842237, by rfl⟩ : syracuseStep 1122983 = 1684475) B1684475
theorem B7185185 : Blo 330750 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B500831 : Blo 330750 500831 := bstep (se 1 (by rfl) ⟨375623, by rfl⟩ : syracuseStep 500831 = 751247) B751247
theorem B500891 : Blo 330750 500891 := bstep (se 1 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 500891 = 751337) B751337
theorem B1418543 : Blo 330750 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B501353 : Blo 330750 501353 := bstep (se 2 (by rfl) ⟨188007, by rfl⟩ : syracuseStep 501353 = 376015) B376015
theorem B501479 : Blo 330750 501479 := bstep (se 1 (by rfl) ⟨376109, by rfl⟩ : syracuseStep 501479 = 752219) B752219
theorem B501575 : Blo 330750 501575 := bstep (se 1 (by rfl) ⟨376181, by rfl⟩ : syracuseStep 501575 = 752363) B752363
theorem B894863 : Blo 330750 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B1419227 : Blo 330750 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B501983 : Blo 330750 501983 := bstep (se 1 (by rfl) ⟨376487, by rfl⟩ : syracuseStep 501983 = 752975) B752975
theorem B502043 : Blo 330750 502043 := bstep (se 1 (by rfl) ⟨376532, by rfl⟩ : syracuseStep 502043 = 753065) B753065
theorem B1681883 : Blo 330750 1681883 := bstep (se 1 (by rfl) ⟨1261412, by rfl⟩ : syracuseStep 1681883 = 2522825) B2522825
theorem B5220865 : Blo 330750 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B895943 : Blo 330750 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B633919 : Blo 330750 633919 := bstep (se 1 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 633919 = 950879) B950879
theorem B1912031 : Blo 330750 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B3812669 : Blo 330750 3812669 := bstep (se 3 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 3812669 = 1429751) B1429751
theorem B1060217 : Blo 330750 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B372127 : Blo 330750 372127 := bstep (se 1 (by rfl) ⟨279095, by rfl⟩ : syracuseStep 372127 = 558191) B558191
theorem B372415 : Blo 330750 372415 := bstep (se 1 (by rfl) ⟨279311, by rfl⟩ : syracuseStep 372415 = 558623) B558623
theorem B634655 : Blo 330750 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B372991 : Blo 330750 372991 := bstep (se 1 (by rfl) ⟨279743, by rfl⟩ : syracuseStep 372991 = 559487) B559487
theorem B1257889 : Blo 330750 1257889 := bstep (se 2 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 1257889 = 943417) B943417
theorem B1126817 : Blo 330750 1126817 := bstep (se 2 (by rfl) ⟨422556, by rfl⟩ : syracuseStep 1126817 = 845113) B845113
theorem B602831 : Blo 330750 602831 := bstep (se 1 (by rfl) ⟨452123, by rfl⟩ : syracuseStep 602831 = 904247) B904247
theorem B1159933 : Blo 330750 1159933 := bstep (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) B434975
theorem B4240457 : Blo 330750 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B3028261 : Blo 330750 3028261 := bstep (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) B567799
theorem B2700611 : Blo 330750 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B374143 : Blo 330750 374143 := bstep (se 1 (by rfl) ⟨280607, by rfl⟩ : syracuseStep 374143 = 561215) B561215
theorem B1062359 : Blo 330750 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B1914799 : Blo 330750 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B374719 : Blo 330750 374719 := bstep (se 1 (by rfl) ⟨281039, by rfl⟩ : syracuseStep 374719 = 562079) B562079
theorem B1685447 : Blo 330750 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B4274491 : Blo 330750 4274491 := bstep (se 1 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 4274491 = 6411737) B6411737
theorem B1129355 : Blo 330750 1129355 := bstep (se 1 (by rfl) ⟨847016, by rfl⟩ : syracuseStep 1129355 = 1694033) B1694033
theorem B506863 : Blo 330750 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B1686743 : Blo 330750 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B2538863 : Blo 330750 2538863 := bstep (se 1 (by rfl) ⟨1904147, by rfl⟩ : syracuseStep 2538863 = 3808295) B3808295
theorem B6405587 : Blo 330750 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B4275827 : Blo 330750 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B6799625 : Blo 330750 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B1688039 : Blo 330750 1688039 := bstep (se 1 (by rfl) ⟨1266029, by rfl⟩ : syracuseStep 1688039 = 2532059) B2532059
theorem B4113139 : Blo 330750 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B1263023 : Blo 330750 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B902951 : Blo 330750 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B1689983 : Blo 330750 1689983 := bstep (se 1 (by rfl) ⟨1267487, by rfl⟩ : syracuseStep 1689983 = 2534975) B2534975
theorem B1591787 : Blo 330750 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B1690631 : Blo 330750 1690631 := bstep (se 1 (by rfl) ⟨1267973, by rfl⟩ : syracuseStep 1690631 = 2535947) B2535947
theorem B7196597 : Blo 330750 7196597 := bstep (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) B674681
theorem B1069163 : Blo 330750 1069163 := bstep (se 1 (by rfl) ⟨801872, by rfl⟩ : syracuseStep 1069163 = 1603745) B1603745
theorem B4248247 : Blo 330750 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B16602457 : Blo 330750 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B7918991 : Blo 330750 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B710383 : Blo 330750 710383 := bstep (se 1 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 710383 = 1065575) B1065575
theorem B4249583 : Blo 330750 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B2119871 : Blo 330750 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B1071623 : Blo 330750 1071623 := bstep (se 1 (by rfl) ⟨803717, by rfl⟩ : syracuseStep 1071623 = 1607435) B1607435
theorem B4807421 : Blo 330750 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B842633 : Blo 330750 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B842663 : Blo 330750 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B1203113 : Blo 330750 1203113 := bstep (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) B902335
theorem B744659 : Blo 330750 744659 := bstep (se 1 (by rfl) ⟨558494, by rfl⟩ : syracuseStep 744659 = 1116989) B1116989
theorem B744731 : Blo 330750 744731 := bstep (se 1 (by rfl) ⟨558548, by rfl⟩ : syracuseStep 744731 = 1117097) B1117097
theorem B3202487 : Blo 330750 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B744929 : Blo 330750 744929 := bstep (se 2 (by rfl) ⟨279348, by rfl⟩ : syracuseStep 744929 = 558697) B558697
theorem B3661433 : Blo 330750 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B843767 : Blo 330750 843767 := bstep (se 1 (by rfl) ⟨632825, by rfl⟩ : syracuseStep 843767 = 1265651) B1265651
theorem B942187 : Blo 330750 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B745721 : Blo 330750 745721 := bstep (se 2 (by rfl) ⟨279645, by rfl⟩ : syracuseStep 745721 = 559291) B559291
theorem B745991 : Blo 330750 745991 := bstep (se 1 (by rfl) ⟨559493, by rfl⟩ : syracuseStep 745991 = 1118987) B1118987
theorem B942779 : Blo 330750 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B746171 : Blo 330750 746171 := bstep (se 1 (by rfl) ⟨559628, by rfl⟩ : syracuseStep 746171 = 1119257) B1119257
theorem B844627 : Blo 330750 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B2548691 : Blo 330750 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B418927 : Blo 330750 418927 := bstep (se 1 (by rfl) ⟨314195, by rfl⟩ : syracuseStep 418927 = 628391) B628391
theorem B746657 : Blo 330750 746657 := bstep (se 2 (by rfl) ⟨279996, by rfl⟩ : syracuseStep 746657 = 559993) B559993
theorem B714295 : Blo 330750 714295 := bstep (se 1 (by rfl) ⟨535721, by rfl⟩ : syracuseStep 714295 = 1071443) B1071443
theorem B747071 : Blo 330750 747071 := bstep (se 1 (by rfl) ⟨560303, by rfl⟩ : syracuseStep 747071 = 1120607) B1120607
theorem B747179 : Blo 330750 747179 := bstep (se 1 (by rfl) ⟨560384, by rfl⟩ : syracuseStep 747179 = 1120769) B1120769
theorem B681851 : Blo 330750 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B4253579 : Blo 330750 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B747431 : Blo 330750 747431 := bstep (se 1 (by rfl) ⟨560573, by rfl⟩ : syracuseStep 747431 = 1121147) B1121147
theorem B2123819 : Blo 330750 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B747719 : Blo 330750 747719 := bstep (se 1 (by rfl) ⟨560789, by rfl⟩ : syracuseStep 747719 = 1121579) B1121579
theorem B977231 : Blo 330750 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B747899 : Blo 330750 747899 := bstep (se 1 (by rfl) ⟨560924, by rfl⟩ : syracuseStep 747899 = 1121849) B1121849
theorem B748007 : Blo 330750 748007 := bstep (se 1 (by rfl) ⟨561005, by rfl⟩ : syracuseStep 748007 = 1122011) B1122011
theorem B3238393 : Blo 330750 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B748169 : Blo 330750 748169 := bstep (se 2 (by rfl) ⟨280563, by rfl⟩ : syracuseStep 748169 = 561127) B561127
theorem B748187 : Blo 330750 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B945103 : Blo 330750 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B355439 : Blo 330750 355439 := bstep (se 1 (by rfl) ⟨266579, by rfl⟩ : syracuseStep 355439 = 533159) B533159
theorem B5139571 : Blo 330750 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B1600823 : Blo 330750 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B749159 : Blo 330750 749159 := bstep (se 1 (by rfl) ⟨561869, by rfl⟩ : syracuseStep 749159 = 1123739) B1123739
theorem B2420729 : Blo 330750 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B2388923 : Blo 330750 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B3863539 : Blo 330750 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B423407 : Blo 330750 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B2127383 : Blo 330750 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B20739629 : Blo 330750 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B2029495 : Blo 330750 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B751643 : Blo 330750 751643 := bstep (se 1 (by rfl) ⟨563732, by rfl⟩ : syracuseStep 751643 = 1127465) B1127465
theorem B752795 : Blo 330750 752795 := bstep (se 1 (by rfl) ⟨564596, by rfl⟩ : syracuseStep 752795 = 1129193) B1129193
theorem B949751 : Blo 330750 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B2032219 : Blo 330750 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B558569 : Blo 330750 558569 := bstep (se 2 (by rfl) ⟨209463, by rfl⟩ : syracuseStep 558569 = 418927) B418927
theorem B952393 : Blo 330750 952393 := bstep (se 2 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 952393 = 714295) B714295
theorem B4327519 : Blo 330750 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B1116719 : Blo 330750 1116719 := bstep (se 1 (by rfl) ⟨837539, by rfl⟩ : syracuseStep 1116719 = 1675079) B1675079
theorem B330783 : Blo 330750 330783 := bstep (se 1 (by rfl) ⟨248087, by rfl⟩ : syracuseStep 330783 = 496175) B496175
theorem B330919 : Blo 330750 330919 := bstep (se 1 (by rfl) ⟨248189, by rfl⟩ : syracuseStep 330919 = 496379) B496379
theorem B331167 : Blo 330750 331167 := bstep (se 1 (by rfl) ⟨248375, by rfl⟩ : syracuseStep 331167 = 496751) B496751
theorem B331215 : Blo 330750 331215 := bstep (se 1 (by rfl) ⟨248411, by rfl⟩ : syracuseStep 331215 = 496823) B496823
theorem B5279327 : Blo 330750 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B331375 : Blo 330750 331375 := bstep (se 1 (by rfl) ⟨248531, by rfl⟩ : syracuseStep 331375 = 497063) B497063
theorem B331495 : Blo 330750 331495 := bstep (se 1 (by rfl) ⟨248621, by rfl⟩ : syracuseStep 331495 = 497243) B497243
theorem B1413247 : Blo 330750 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B6852761 : Blo 330750 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B331999 : Blo 330750 331999 := bstep (se 1 (by rfl) ⟨248999, by rfl⟩ : syracuseStep 331999 = 497999) B497999
theorem B1118447 : Blo 330750 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B332015 : Blo 330750 332015 := bstep (se 1 (by rfl) ⟨249011, by rfl⟩ : syracuseStep 332015 = 498023) B498023
theorem B332059 : Blo 330750 332059 := bstep (se 1 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 332059 = 498089) B498089
theorem B332315 : Blo 330750 332315 := bstep (se 1 (by rfl) ⟨249236, by rfl⟩ : syracuseStep 332315 = 498473) B498473
theorem B496169 : Blo 330750 496169 := bstep (se 2 (by rfl) ⟨186063, by rfl⟩ : syracuseStep 496169 = 372127) B372127
theorem B561755 : Blo 330750 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B561775 : Blo 330750 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B332455 : Blo 330750 332455 := bstep (se 1 (by rfl) ⟨249341, by rfl⟩ : syracuseStep 332455 = 498683) B498683
theorem B332479 : Blo 330750 332479 := bstep (se 1 (by rfl) ⟨249359, by rfl⟩ : syracuseStep 332479 = 498719) B498719
theorem B332495 : Blo 330750 332495 := bstep (se 1 (by rfl) ⟨249371, by rfl⟩ : syracuseStep 332495 = 498743) B498743
theorem B332575 : Blo 330750 332575 := bstep (se 1 (by rfl) ⟨249431, by rfl⟩ : syracuseStep 332575 = 498863) B498863
theorem B496439 : Blo 330750 496439 := bstep (se 1 (by rfl) ⟨372329, by rfl⟩ : syracuseStep 496439 = 744659) B744659
theorem B496487 : Blo 330750 496487 := bstep (se 1 (by rfl) ⟨372365, by rfl⟩ : syracuseStep 496487 = 744731) B744731
theorem B332671 : Blo 330750 332671 := bstep (se 1 (by rfl) ⟨249503, by rfl⟩ : syracuseStep 332671 = 499007) B499007
theorem B496553 : Blo 330750 496553 := bstep (se 2 (by rfl) ⟨186207, by rfl⟩ : syracuseStep 496553 = 372415) B372415
theorem B2134991 : Blo 330750 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B332767 : Blo 330750 332767 := bstep (se 1 (by rfl) ⟨249575, by rfl⟩ : syracuseStep 332767 = 499151) B499151
theorem B496619 : Blo 330750 496619 := bstep (se 1 (by rfl) ⟨372464, by rfl⟩ : syracuseStep 496619 = 744929) B744929
theorem B333023 : Blo 330750 333023 := bstep (se 1 (by rfl) ⟨249767, by rfl⟩ : syracuseStep 333023 = 499535) B499535
theorem B333055 : Blo 330750 333055 := bstep (se 1 (by rfl) ⟨249791, by rfl⟩ : syracuseStep 333055 = 499583) B499583
theorem B398639 : Blo 330750 398639 := bstep (se 1 (by rfl) ⟨298979, by rfl⟩ : syracuseStep 398639 = 597959) B597959
theorem B333103 : Blo 330750 333103 := bstep (se 1 (by rfl) ⟨249827, by rfl⟩ : syracuseStep 333103 = 499655) B499655
theorem B562511 : Blo 330750 562511 := bstep (se 1 (by rfl) ⟨421883, by rfl⟩ : syracuseStep 562511 = 843767) B843767
theorem B333263 : Blo 330750 333263 := bstep (se 1 (by rfl) ⟨249947, by rfl⟩ : syracuseStep 333263 = 499895) B499895
theorem B497147 : Blo 330750 497147 := bstep (se 1 (by rfl) ⟨372860, by rfl⟩ : syracuseStep 497147 = 745721) B745721
theorem B1119743 : Blo 330750 1119743 := bstep (se 1 (by rfl) ⟨839807, by rfl⟩ : syracuseStep 1119743 = 1679615) B1679615
theorem B333343 : Blo 330750 333343 := bstep (se 1 (by rfl) ⟨250007, by rfl⟩ : syracuseStep 333343 = 500015) B500015
theorem B497321 : Blo 330750 497321 := bstep (se 2 (by rfl) ⟨186495, by rfl⟩ : syracuseStep 497321 = 372991) B372991
theorem B497327 : Blo 330750 497327 := bstep (se 1 (by rfl) ⟨372995, by rfl⟩ : syracuseStep 497327 = 745991) B745991
theorem B333503 : Blo 330750 333503 := bstep (se 1 (by rfl) ⟨250127, by rfl⟩ : syracuseStep 333503 = 500255) B500255
theorem B333543 : Blo 330750 333543 := bstep (se 1 (by rfl) ⟨250157, by rfl⟩ : syracuseStep 333543 = 500315) B500315
theorem B497447 : Blo 330750 497447 := bstep (se 1 (by rfl) ⟨373085, by rfl⟩ : syracuseStep 497447 = 746171) B746171
theorem B4790123 : Blo 330750 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B1677185 : Blo 330750 1677185 := bstep (se 2 (by rfl) ⟨628944, by rfl⟩ : syracuseStep 1677185 = 1257889) B1257889
theorem B333887 : Blo 330750 333887 := bstep (se 1 (by rfl) ⟨250415, by rfl⟩ : syracuseStep 333887 = 500831) B500831
theorem B333927 : Blo 330750 333927 := bstep (se 1 (by rfl) ⟨250445, by rfl⟩ : syracuseStep 333927 = 500891) B500891
theorem B497771 : Blo 330750 497771 := bstep (se 1 (by rfl) ⟨373328, by rfl⟩ : syracuseStep 497771 = 746657) B746657
theorem B1546577 : Blo 330750 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B498047 : Blo 330750 498047 := bstep (se 1 (by rfl) ⟨373535, by rfl⟩ : syracuseStep 498047 = 747071) B747071
theorem B334235 : Blo 330750 334235 := bstep (se 1 (by rfl) ⟨250676, by rfl⟩ : syracuseStep 334235 = 501353) B501353
theorem B498119 : Blo 330750 498119 := bstep (se 1 (by rfl) ⟨373589, by rfl⟩ : syracuseStep 498119 = 747179) B747179
theorem B334319 : Blo 330750 334319 := bstep (se 1 (by rfl) ⟨250739, by rfl⟩ : syracuseStep 334319 = 501479) B501479
theorem B334383 : Blo 330750 334383 := bstep (se 1 (by rfl) ⟨250787, by rfl⟩ : syracuseStep 334383 = 501575) B501575
theorem B596575 : Blo 330750 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B498287 : Blo 330750 498287 := bstep (se 1 (by rfl) ⟨373715, by rfl⟩ : syracuseStep 498287 = 747431) B747431
theorem B5151385 : Blo 330750 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B1415879 : Blo 330750 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B498479 : Blo 330750 498479 := bstep (se 1 (by rfl) ⟨373859, by rfl⟩ : syracuseStep 498479 = 747719) B747719
theorem B334655 : Blo 330750 334655 := bstep (se 1 (by rfl) ⟨250991, by rfl⟩ : syracuseStep 334655 = 501983) B501983
theorem B334695 : Blo 330750 334695 := bstep (se 1 (by rfl) ⟨251021, by rfl⟩ : syracuseStep 334695 = 502043) B502043
theorem B498599 : Blo 330750 498599 := bstep (se 1 (by rfl) ⟨373949, by rfl⟩ : syracuseStep 498599 = 747899) B747899
theorem B1121255 : Blo 330750 1121255 := bstep (se 1 (by rfl) ⟨840941, by rfl⟩ : syracuseStep 1121255 = 1681883) B1681883
theorem B498671 : Blo 330750 498671 := bstep (se 1 (by rfl) ⟨374003, by rfl⟩ : syracuseStep 498671 = 748007) B748007
theorem B4037681 : Blo 330750 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B498779 : Blo 330750 498779 := bstep (se 1 (by rfl) ⟨374084, by rfl⟩ : syracuseStep 498779 = 748169) B748169
theorem B498791 : Blo 330750 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B498857 : Blo 330750 498857 := bstep (se 2 (by rfl) ⟨187071, by rfl⟩ : syracuseStep 498857 = 374143) B374143
theorem B597295 : Blo 330750 597295 := bstep (se 1 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 597295 = 895943) B895943
theorem B499439 : Blo 330750 499439 := bstep (se 1 (by rfl) ⟨374579, by rfl⟩ : syracuseStep 499439 = 749159) B749159
theorem B499625 : Blo 330750 499625 := bstep (se 2 (by rfl) ⟨187359, by rfl⟩ : syracuseStep 499625 = 374719) B374719
theorem B1613819 : Blo 330750 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B401887 : Blo 330750 401887 := bstep (se 1 (by rfl) ⟨301415, by rfl⟩ : syracuseStep 401887 = 602831) B602831
theorem B2826971 : Blo 330750 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1418255 : Blo 330750 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B69215269 : Blo 330750 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B1123631 : Blo 330750 1123631 := bstep (se 1 (by rfl) ⟨842723, by rfl⟩ : syracuseStep 1123631 = 1685447) B1685447
theorem B501095 : Blo 330750 501095 := bstep (se 1 (by rfl) ⟨375821, by rfl⟩ : syracuseStep 501095 = 751643) B751643
theorem B501863 : Blo 330750 501863 := bstep (se 1 (by rfl) ⟨376397, by rfl⟩ : syracuseStep 501863 = 752795) B752795
theorem B1124495 : Blo 330750 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B4270391 : Blo 330750 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B633167 : Blo 330750 633167 := bstep (se 1 (by rfl) ⟨474875, by rfl⟩ : syracuseStep 633167 = 949751) B949751
theorem B1420031 : Blo 330750 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B535337 : Blo 330750 535337 := bstep (se 2 (by rfl) ⟨200751, by rfl⟩ : syracuseStep 535337 = 401503) B401503
theorem B1256249 : Blo 330750 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B633683 : Blo 330750 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B4533083 : Blo 330750 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B1125359 : Blo 330750 1125359 := bstep (se 1 (by rfl) ⟨844019, by rfl⟩ : syracuseStep 1125359 = 1688039) B1688039
theorem B634223 : Blo 330750 634223 := bstep (se 1 (by rfl) ⟨475667, by rfl⟩ : syracuseStep 634223 = 951335) B951335
theorem B5484185 : Blo 330750 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B1126169 : Blo 330750 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B601967 : Blo 330750 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B1126655 : Blo 330750 1126655 := bstep (se 1 (by rfl) ⟨844991, by rfl⟩ : syracuseStep 1126655 = 1689983) B1689983
theorem B1061191 : Blo 330750 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B1421687 : Blo 330750 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B373279 : Blo 330750 373279 := bstep (se 1 (by rfl) ⟨279959, by rfl⟩ : syracuseStep 373279 = 559919) B559919
theorem B5681825 : Blo 330750 5681825 := bstep (se 2 (by rfl) ⟨2130684, by rfl⟩ : syracuseStep 5681825 = 4261369) B4261369
theorem B1127087 : Blo 330750 1127087 := bstep (se 1 (by rfl) ⟨845315, by rfl⟩ : syracuseStep 1127087 = 1690631) B1690631
theorem B373927 : Blo 330750 373927 := bstep (se 1 (by rfl) ⟨280445, by rfl⟩ : syracuseStep 373927 = 560891) B560891
theorem B4797731 : Blo 330750 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B6961153 : Blo 330750 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B1260137 : Blo 330750 1260137 := bstep (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) B945103
theorem B1129085 : Blo 330750 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B2833055 : Blo 330750 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B900031 : Blo 330750 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B802075 : Blo 330750 802075 := bstep (se 1 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 802075 = 1203113) B1203113
theorem B2440955 : Blo 330750 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B2703269 : Blo 330750 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B3784967 : Blo 330750 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B2835719 : Blo 330750 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B22136609 : Blo 330750 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B1067215 : Blo 330750 1067215 := bstep (se 1 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 1067215 = 1600823) B1600823
theorem B2541779 : Blo 330750 2541779 := bstep (se 1 (by rfl) ⟨1906334, by rfl⟩ : syracuseStep 2541779 = 3812669) B3812669
theorem B706811 : Blo 330750 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B2705993 : Blo 330750 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B1592615 : Blo 330750 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B708239 : Blo 330750 708239 := bstep (se 1 (by rfl) ⟨531179, by rfl⟩ : syracuseStep 708239 = 1062359) B1062359
theorem B709033 : Blo 330750 709033 := bstep (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) B531775
theorem B1692413 : Blo 330750 1692413 := bstep (se 3 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 1692413 = 634655) B634655
theorem B1692575 : Blo 330750 1692575 := bstep (se 1 (by rfl) ⟨1269431, by rfl⟩ : syracuseStep 1692575 = 2538863) B2538863
theorem B10442459 : Blo 330750 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B1792145 : Blo 330750 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B842015 : Blo 330750 842015 := bstep (se 1 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 842015 = 1263023) B1263023
theorem B1268095 : Blo 330750 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B2316671 : Blo 330750 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B2513591 : Blo 330750 2513591 := bstep (se 1 (by rfl) ⟨1885193, by rfl⟩ : syracuseStep 2513591 = 3770387) B3770387
theorem B1006271 : Blo 330750 1006271 := bstep (se 1 (by rfl) ⟨754703, by rfl⟩ : syracuseStep 1006271 = 1509407) B1509407
theorem B1268567 : Blo 330750 1268567 := bstep (se 1 (by rfl) ⟨951425, by rfl⟩ : syracuseStep 1268567 = 1902851) B1902851
theorem B4283513 : Blo 330750 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B2514077 : Blo 330750 2514077 := bstep (se 3 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 2514077 = 942779) B942779
theorem B5397911 : Blo 330750 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B100228913 : Blo 330750 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B712775 : Blo 330750 712775 := bstep (se 1 (by rfl) ⟨534581, by rfl⟩ : syracuseStep 712775 = 1069163) B1069163
theorem B4317857 : Blo 330750 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B845225 : Blo 330750 845225 := bstep (se 2 (by rfl) ⟨316959, by rfl⟩ : syracuseStep 845225 = 633919) B633919
theorem B714415 : Blo 330750 714415 := bstep (se 1 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 714415 = 1071623) B1071623
theorem B3204947 : Blo 330750 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B748655 : Blo 330750 748655 := bstep (se 1 (by rfl) ⟨561491, by rfl⟩ : syracuseStep 748655 = 1122983) B1122983
theorem B1699127 : Blo 330750 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B945695 : Blo 330750 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B5664329 : Blo 330750 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B454567 : Blo 330750 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B946151 : Blo 330750 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B651487 : Blo 330750 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1274687 : Blo 330750 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B947177 : Blo 330750 947177 := bstep (se 2 (by rfl) ⟨355191, by rfl⟩ : syracuseStep 947177 = 710383) B710383
theorem B2553065 : Blo 330750 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B751211 : Blo 330750 751211 := bstep (se 1 (by rfl) ⟨563408, by rfl⟩ : syracuseStep 751211 = 1126817) B1126817
theorem B947837 : Blo 330750 947837 := bstep (se 3 (by rfl) ⟨177719, by rfl⟩ : syracuseStep 947837 = 355439) B355439
theorem B5699321 : Blo 330750 5699321 := bstep (se 2 (by rfl) ⟨2137245, by rfl⟩ : syracuseStep 5699321 = 4274491) B4274491
theorem B1013897 : Blo 330750 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1800407 : Blo 330750 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B13826419 : Blo 330750 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B2325217 : Blo 330750 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B752903 : Blo 330750 752903 := bstep (se 1 (by rfl) ⟨564677, by rfl⟩ : syracuseStep 752903 = 1129355) B1129355
theorem B2850551 : Blo 330750 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B2523311 : Blo 330750 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B1803995 : Blo 330750 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B952553 : Blo 330750 952553 := bstep (se 2 (by rfl) ⟨357207, by rfl⟩ : syracuseStep 952553 = 714415) B714415
theorem B5770025 : Blo 330750 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B330779 : Blo 330750 330779 := bstep (se 1 (by rfl) ⟨248084, by rfl⟩ : syracuseStep 330779 = 496169) B496169
theorem B330959 : Blo 330750 330959 := bstep (se 1 (by rfl) ⟨248219, by rfl⟩ : syracuseStep 330959 = 496439) B496439
theorem B330991 : Blo 330750 330991 := bstep (se 1 (by rfl) ⟨248243, by rfl⟩ : syracuseStep 330991 = 496487) B496487
theorem B331035 : Blo 330750 331035 := bstep (se 1 (by rfl) ⟨248276, by rfl⟩ : syracuseStep 331035 = 496553) B496553
theorem B331079 : Blo 330750 331079 := bstep (se 1 (by rfl) ⟨248309, by rfl⟩ : syracuseStep 331079 = 496619) B496619
theorem B331431 : Blo 330750 331431 := bstep (se 1 (by rfl) ⟨248573, by rfl⟩ : syracuseStep 331431 = 497147) B497147
theorem B331547 : Blo 330750 331547 := bstep (se 1 (by rfl) ⟨248660, by rfl⟩ : syracuseStep 331547 = 497321) B497321
theorem B331551 : Blo 330750 331551 := bstep (se 1 (by rfl) ⟨248663, by rfl⟩ : syracuseStep 331551 = 497327) B497327
theorem B331631 : Blo 330750 331631 := bstep (se 1 (by rfl) ⟨248723, by rfl⟩ : syracuseStep 331631 = 497447) B497447
theorem B1118123 : Blo 330750 1118123 := bstep (se 1 (by rfl) ⟨838592, by rfl⟩ : syracuseStep 1118123 = 1677185) B1677185
theorem B331847 : Blo 330750 331847 := bstep (se 1 (by rfl) ⟨248885, by rfl⟩ : syracuseStep 331847 = 497771) B497771
theorem B561343 : Blo 330750 561343 := bstep (se 1 (by rfl) ⟨421007, by rfl⟩ : syracuseStep 561343 = 842015) B842015
theorem B332031 : Blo 330750 332031 := bstep (se 1 (by rfl) ⟨249023, by rfl⟩ : syracuseStep 332031 = 498047) B498047
theorem B1544447 : Blo 330750 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B332079 : Blo 330750 332079 := bstep (se 1 (by rfl) ⟨249059, by rfl⟩ : syracuseStep 332079 = 498119) B498119
theorem B332191 : Blo 330750 332191 := bstep (se 1 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 332191 = 498287) B498287
theorem B1675727 : Blo 330750 1675727 := bstep (se 1 (by rfl) ⟨1256795, by rfl⟩ : syracuseStep 1675727 = 2513591) B2513591
theorem B332319 : Blo 330750 332319 := bstep (se 1 (by rfl) ⟨249239, by rfl⟩ : syracuseStep 332319 = 498479) B498479
theorem B332399 : Blo 330750 332399 := bstep (se 1 (by rfl) ⟨249299, by rfl⟩ : syracuseStep 332399 = 498599) B498599
theorem B332447 : Blo 330750 332447 := bstep (se 1 (by rfl) ⟨249335, by rfl⟩ : syracuseStep 332447 = 498671) B498671
theorem B2691787 : Blo 330750 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B332519 : Blo 330750 332519 := bstep (se 1 (by rfl) ⟨249389, by rfl⟩ : syracuseStep 332519 = 498779) B498779
theorem B332527 : Blo 330750 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B2855675 : Blo 330750 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B1676051 : Blo 330750 1676051 := bstep (se 1 (by rfl) ⟨1257038, by rfl⟩ : syracuseStep 1676051 = 2514077) B2514077
theorem B332571 : Blo 330750 332571 := bstep (se 1 (by rfl) ⟨249428, by rfl⟩ : syracuseStep 332571 = 498857) B498857
theorem B332959 : Blo 330750 332959 := bstep (se 1 (by rfl) ⟨249719, by rfl⟩ : syracuseStep 332959 = 499439) B499439
theorem B66819275 : Blo 330750 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B333083 : Blo 330750 333083 := bstep (se 1 (by rfl) ⟨249812, by rfl⟩ : syracuseStep 333083 = 499625) B499625
theorem B1414921 : Blo 330750 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B497705 : Blo 330750 497705 := bstep (se 2 (by rfl) ⟨186639, by rfl⟩ : syracuseStep 497705 = 373279) B373279
theorem B334063 : Blo 330750 334063 := bstep (se 1 (by rfl) ⟨250547, by rfl⟩ : syracuseStep 334063 = 501095) B501095
theorem B563483 : Blo 330750 563483 := bstep (se 1 (by rfl) ⟨422612, by rfl⟩ : syracuseStep 563483 = 845225) B845225
theorem B2136631 : Blo 330750 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B334575 : Blo 330750 334575 := bstep (se 1 (by rfl) ⟨250931, by rfl⟩ : syracuseStep 334575 = 501863) B501863
theorem B498569 : Blo 330750 498569 := bstep (se 2 (by rfl) ⟨186963, by rfl⟩ : syracuseStep 498569 = 373927) B373927
theorem B3022055 : Blo 330750 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B499103 : Blo 330750 499103 := bstep (se 1 (by rfl) ⟨374327, by rfl⟩ : syracuseStep 499103 = 748655) B748655
theorem B3776219 : Blo 330750 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B401311 : Blo 330750 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B630767 : Blo 330750 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B9281537 : Blo 330750 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B631451 : Blo 330750 631451 := bstep (se 1 (by rfl) ⟨473588, by rfl⟩ : syracuseStep 631451 = 947177) B947177
theorem B795433 : Blo 330750 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B500807 : Blo 330750 500807 := bstep (se 1 (by rfl) ⟨375605, by rfl⟩ : syracuseStep 500807 = 751211) B751211
theorem B631891 : Blo 330750 631891 := bstep (se 1 (by rfl) ⟨473918, by rfl⟩ : syracuseStep 631891 = 947837) B947837
theorem B796393 : Blo 330750 796393 := bstep (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) B597295
theorem B501935 : Blo 330750 501935 := bstep (se 1 (by rfl) ⟨376451, by rfl⟩ : syracuseStep 501935 = 752903) B752903
theorem B372379 : Blo 330750 372379 := bstep (se 1 (by rfl) ⟨279284, by rfl⟩ : syracuseStep 372379 = 558569) B558569
theorem B92287025 : Blo 330750 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B73740901 : Blo 330750 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B1061743 : Blo 330750 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B3519551 : Blo 330750 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B472159 : Blo 330750 472159 := bstep (se 1 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 472159 = 708239) B708239
theorem B2143397 : Blo 330750 2143397 := bstep (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) B401887
theorem B4568507 : Blo 330750 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B1422953 : Blo 330750 1422953 := bstep (se 2 (by rfl) ⟨533607, by rfl⟩ : syracuseStep 1422953 = 1067215) B1067215
theorem B374503 : Blo 330750 374503 := bstep (se 1 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 374503 = 561755) B561755
theorem B1128275 : Blo 330750 1128275 := bstep (se 1 (by rfl) ⟨846206, by rfl⟩ : syracuseStep 1128275 = 1692413) B1692413
theorem B1128383 : Blo 330750 1128383 := bstep (se 1 (by rfl) ⟨846287, by rfl⟩ : syracuseStep 1128383 = 1692575) B1692575
theorem B1423327 : Blo 330750 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B12793949 : Blo 330750 12793949 := bstep (se 3 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 12793949 = 4797731) B4797731
theorem B1063037 : Blo 330750 1063037 := bstep (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) B398639
theorem B375007 : Blo 330750 375007 := bstep (se 1 (by rfl) ⟨281255, by rfl⟩ : syracuseStep 375007 = 562511) B562511
theorem B6961639 : Blo 330750 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B3193415 : Blo 330750 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B1194763 : Blo 330750 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1031051 : Blo 330750 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B670847 : Blo 330750 670847 := bstep (se 1 (by rfl) ⟨503135, by rfl⟩ : syracuseStep 670847 = 1006271) B1006271
theorem B59030957 : Blo 330750 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B606089 : Blo 330750 606089 := bstep (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) B454567
theorem B475183 : Blo 330750 475183 := bstep (se 1 (by rfl) ⟨356387, by rfl⟩ : syracuseStep 475183 = 712775) B712775
theorem B1884329 : Blo 330750 1884329 := bstep (se 2 (by rfl) ⟨706623, by rfl⟩ : syracuseStep 1884329 = 1413247) B1413247
theorem B868649 : Blo 330750 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B2703725 : Blo 330750 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B1884647 : Blo 330750 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B1884829 : Blo 330750 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B837499 : Blo 330750 837499 := bstep (se 1 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 837499 = 1256249) B1256249
theorem B1132751 : Blo 330750 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B1689821 : Blo 330750 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B3656123 : Blo 330750 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B3787883 : Blo 330750 3787883 := bstep (se 1 (by rfl) ⟨2840912, by rfl⟩ : syracuseStep 3787883 = 5681825) B5681825
theorem B1690793 : Blo 330750 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B6868513 : Blo 330750 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B3100289 : Blo 330750 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B1200041 : Blo 330750 1200041 := bstep (se 2 (by rfl) ⟨450015, by rfl⟩ : syracuseStep 1200041 = 900031) B900031
theorem B1200271 : Blo 330750 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1069433 : Blo 330750 1069433 := bstep (se 2 (by rfl) ⟨401037, by rfl⟩ : syracuseStep 1069433 = 802075) B802075
theorem B840091 : Blo 330750 840091 := bstep (se 1 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 840091 = 1260137) B1260137
theorem B1888703 : Blo 330750 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B1627303 : Blo 330750 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B2709625 : Blo 330750 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B1890479 : Blo 330750 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B1694519 : Blo 330750 1694519 := bstep (se 1 (by rfl) ⟨1270889, by rfl⟩ : syracuseStep 1694519 = 2541779) B2541779
theorem B744479 : Blo 330750 744479 := bstep (se 1 (by rfl) ⟨558359, by rfl⟩ : syracuseStep 744479 = 1116719) B1116719
theorem B1269857 : Blo 330750 1269857 := bstep (se 2 (by rfl) ⟨476196, by rfl⟩ : syracuseStep 1269857 = 952393) B952393
theorem B745631 : Blo 330750 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B746495 : Blo 330750 746495 := bstep (se 1 (by rfl) ⟨559871, by rfl⟩ : syracuseStep 746495 = 1119743) B1119743
theorem B943919 : Blo 330750 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B845711 : Blo 330750 845711 := bstep (se 1 (by rfl) ⟨634283, by rfl⟩ : syracuseStep 845711 = 1268567) B1268567
theorem B747503 : Blo 330750 747503 := bstep (se 1 (by rfl) ⟨560627, by rfl⟩ : syracuseStep 747503 = 1121255) B1121255
theorem B3598607 : Blo 330750 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B1075879 : Blo 330750 1075879 := bstep (se 1 (by rfl) ⟨806909, by rfl⟩ : syracuseStep 1075879 = 1613819) B1613819
theorem B2878571 : Blo 330750 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B945377 : Blo 330750 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B945503 : Blo 330750 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B749033 : Blo 330750 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B749087 : Blo 330750 749087 := bstep (se 1 (by rfl) ⟨561815, by rfl⟩ : syracuseStep 749087 = 1123631) B1123631
theorem B749663 : Blo 330750 749663 := bstep (se 1 (by rfl) ⟨562247, by rfl⟩ : syracuseStep 749663 = 1124495) B1124495
theorem B2846927 : Blo 330750 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B422111 : Blo 330750 422111 := bstep (se 1 (by rfl) ⟨316583, by rfl⟩ : syracuseStep 422111 = 633167) B633167
theorem B946687 : Blo 330750 946687 := bstep (se 1 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 946687 = 1420031) B1420031
theorem B356891 : Blo 330750 356891 := bstep (se 1 (by rfl) ⟨267668, by rfl⟩ : syracuseStep 356891 = 535337) B535337
theorem B750239 : Blo 330750 750239 := bstep (se 1 (by rfl) ⟨562679, by rfl⟩ : syracuseStep 750239 = 1125359) B1125359
theorem B422815 : Blo 330750 422815 := bstep (se 1 (by rfl) ⟨317111, by rfl⟩ : syracuseStep 422815 = 634223) B634223
theorem B750779 : Blo 330750 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B751103 : Blo 330750 751103 := bstep (se 1 (by rfl) ⟨563327, by rfl⟩ : syracuseStep 751103 = 1126655) B1126655
theorem B947791 : Blo 330750 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B751391 : Blo 330750 751391 := bstep (se 1 (by rfl) ⟨563543, by rfl⟩ : syracuseStep 751391 = 1127087) B1127087
theorem B849791 : Blo 330750 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B1702043 : Blo 330750 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B3799547 : Blo 330750 3799547 := bstep (se 1 (by rfl) ⟨2849660, by rfl⟩ : syracuseStep 3799547 = 5699321) B5699321
theorem B2521853 : Blo 330750 2521853 := bstep (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) B945695
theorem B752723 : Blo 330750 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B1900367 : Blo 330750 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B1802179 : Blo 330750 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B1802483 : Blo 330750 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B2525255 : Blo 330750 2525255 := bstep (se 1 (by rfl) ⟨1893941, by rfl⟩ : syracuseStep 2525255 = 3787883) B3787883
theorem B1116665 : Blo 330750 1116665 := bstep (se 2 (by rfl) ⟨418749, by rfl⟩ : syracuseStep 1116665 = 837499) B837499
theorem B1117151 : Blo 330750 1117151 := bstep (se 1 (by rfl) ⟨837863, by rfl⟩ : syracuseStep 1117151 = 1675727) B1675727
theorem B1903783 : Blo 330750 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B1117367 : Blo 330750 1117367 := bstep (se 1 (by rfl) ⟨838025, by rfl⟩ : syracuseStep 1117367 = 1676051) B1676051
theorem B331803 : Blo 330750 331803 := bstep (se 1 (by rfl) ⟨248852, by rfl⟩ : syracuseStep 331803 = 497705) B497705
theorem B332379 : Blo 330750 332379 := bstep (se 1 (by rfl) ⟨249284, by rfl⟩ : syracuseStep 332379 = 498569) B498569
theorem B496319 : Blo 330750 496319 := bstep (se 1 (by rfl) ⟨372239, by rfl⟩ : syracuseStep 496319 = 744479) B744479
theorem B496505 : Blo 330750 496505 := bstep (se 2 (by rfl) ⟨186189, by rfl⟩ : syracuseStep 496505 = 372379) B372379
theorem B332735 : Blo 330750 332735 := bstep (se 1 (by rfl) ⟨249551, by rfl⟩ : syracuseStep 332735 = 499103) B499103
theorem B497087 : Blo 330750 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B3806837 : Blo 330750 3806837 := bstep (se 5 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 3806837 = 356891) B356891
theorem B1120121 : Blo 330750 1120121 := bstep (se 2 (by rfl) ⟨420045, by rfl⟩ : syracuseStep 1120121 = 840091) B840091
theorem B3020669 : Blo 330750 3020669 := bstep (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) B1132751
theorem B497663 : Blo 330750 497663 := bstep (se 1 (by rfl) ⟨373247, by rfl⟩ : syracuseStep 497663 = 746495) B746495
theorem B333871 : Blo 330750 333871 := bstep (se 1 (by rfl) ⟨250403, by rfl⟩ : syracuseStep 333871 = 500807) B500807
theorem B1415657 : Blo 330750 1415657 := bstep (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) B1061743
theorem B629279 : Blo 330750 629279 := bstep (se 1 (by rfl) ⟨471959, by rfl⟩ : syracuseStep 629279 = 943919) B943919
theorem B563753 : Blo 330750 563753 := bstep (se 2 (by rfl) ⟨211407, by rfl⟩ : syracuseStep 563753 = 422815) B422815
theorem B563807 : Blo 330750 563807 := bstep (se 1 (by rfl) ⟨422855, by rfl⟩ : syracuseStep 563807 = 845711) B845711
theorem B498335 : Blo 330750 498335 := bstep (se 1 (by rfl) ⟨373751, by rfl⟩ : syracuseStep 498335 = 747503) B747503
theorem B334623 : Blo 330750 334623 := bstep (se 1 (by rfl) ⟨250967, by rfl⟩ : syracuseStep 334623 = 501935) B501935
theorem B629545 : Blo 330750 629545 := bstep (se 2 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 629545 = 472159) B472159
theorem B2399071 : Blo 330750 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B2169737 : Blo 330750 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B630251 : Blo 330750 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B630335 : Blo 330750 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B499337 : Blo 330750 499337 := bstep (se 2 (by rfl) ⟨187251, by rfl⟩ : syracuseStep 499337 = 374503) B374503
theorem B499355 : Blo 330750 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B499391 : Blo 330750 499391 := bstep (se 1 (by rfl) ⟨374543, by rfl⟩ : syracuseStep 499391 = 749087) B749087
theorem B499775 : Blo 330750 499775 := bstep (se 1 (by rfl) ⟨374831, by rfl⟩ : syracuseStep 499775 = 749663) B749663
theorem B3612833 : Blo 330750 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B500009 : Blo 330750 500009 := bstep (se 2 (by rfl) ⟨187503, by rfl⟩ : syracuseStep 500009 = 375007) B375007
theorem B500159 : Blo 330750 500159 := bstep (se 1 (by rfl) ⟨375119, by rfl⟩ : syracuseStep 500159 = 750239) B750239
theorem B9282185 : Blo 330750 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B500519 : Blo 330750 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B500735 : Blo 330750 500735 := bstep (se 1 (by rfl) ⟨375551, by rfl⟩ : syracuseStep 500735 = 751103) B751103
theorem B500927 : Blo 330750 500927 := bstep (se 1 (by rfl) ⟨375695, by rfl⟩ : syracuseStep 500927 = 751391) B751391
theorem B566527 : Blo 330750 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B8529299 : Blo 330750 8529299 := bstep (se 1 (by rfl) ⟨6396974, by rfl⟩ : syracuseStep 8529299 = 12793949) B12793949
theorem B2533031 : Blo 330750 2533031 := bstep (se 1 (by rfl) ⟨1899773, by rfl⟩ : syracuseStep 2533031 = 3799547) B3799547
theorem B8267437 : Blo 330750 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B1681235 : Blo 330750 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B501815 : Blo 330750 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B1616237 : Blo 330750 1616237 := bstep (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) B606089
theorem B535081 : Blo 330750 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B2402905 : Blo 330750 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B1682045 : Blo 330750 1682045 := bstep (se 3 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 1682045 = 630767) B630767
theorem B633577 : Blo 330750 633577 := bstep (se 2 (by rfl) ⟨237591, by rfl⟩ : syracuseStep 633577 = 475183) B475183
theorem B1256219 : Blo 330750 1256219 := bstep (se 1 (by rfl) ⟨942164, by rfl⟩ : syracuseStep 1256219 = 1884329) B1884329
theorem B1682207 : Blo 330750 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B1256431 : Blo 330750 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B1125629 : Blo 330750 1125629 := bstep (se 3 (by rfl) ⟨211055, by rfl⟩ : syracuseStep 1125629 = 422111) B422111
theorem B1060577 : Blo 330750 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B1126547 : Blo 330750 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B635035 : Blo 330750 635035 := bstep (se 1 (by rfl) ⟨476276, by rfl⟩ : syracuseStep 635035 = 952553) B952553
theorem B2437415 : Blo 330750 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B3846683 : Blo 330750 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B1127195 : Blo 330750 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B1061857 : Blo 330750 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B800027 : Blo 330750 800027 := bstep (se 1 (by rfl) ⟨600020, by rfl⟩ : syracuseStep 800027 = 1200041) B1200041
theorem B1029631 : Blo 330750 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B1259135 : Blo 330750 1259135 := bstep (se 1 (by rfl) ⟨944351, by rfl⟩ : syracuseStep 1259135 = 1888703) B1888703
theorem B44546183 : Blo 330750 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B1260319 : Blo 330750 1260319 := bstep (se 1 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 1260319 = 1890479) B1890479
theorem B375655 : Blo 330750 375655 := bstep (se 1 (by rfl) ⟨281741, by rfl⟩ : syracuseStep 375655 = 563483) B563483
theorem B1129679 : Blo 330750 1129679 := bstep (se 1 (by rfl) ⟨847259, by rfl⟩ : syracuseStep 1129679 = 1694519) B1694519
theorem B9158017 : Blo 330750 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B2014703 : Blo 330750 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1262249 : Blo 330750 1262249 := bstep (se 2 (by rfl) ⟨473343, by rfl⟩ : syracuseStep 1262249 = 946687) B946687
theorem B98321201 : Blo 330750 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B3589049 : Blo 330750 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1919047 : Blo 330750 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B1263721 : Blo 330750 1263721 := bstep (se 2 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 1263721 = 947791) B947791
theorem B1886561 : Blo 330750 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B61524683 : Blo 330750 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B1788925 : Blo 330750 1788925 := bstep (se 3 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 1788925 = 670847) B670847
theorem B2346367 : Blo 330750 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B1428931 : Blo 330750 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B1593017 : Blo 330750 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B708691 : Blo 330750 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B1134695 : Blo 330750 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B1266911 : Blo 330750 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B2513105 : Blo 330750 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B1202663 : Blo 330750 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B842521 : Blo 330750 842521 := bstep (se 2 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 842521 = 631891) B631891
theorem B745415 : Blo 330750 745415 := bstep (se 1 (by rfl) ⟨559061, by rfl⟩ : syracuseStep 745415 = 1118123) B1118123
theorem B712955 : Blo 330750 712955 := bstep (se 1 (by rfl) ⟨534716, by rfl⟩ : syracuseStep 712955 = 1069433) B1069433
theorem B9265589 : Blo 330750 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B1434505 : Blo 330750 1434505 := bstep (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) B1075879
theorem B2517479 : Blo 330750 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B6187691 : Blo 330750 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B846571 : Blo 330750 846571 := bstep (se 1 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 846571 = 1269857) B1269857
theorem B1600361 : Blo 330750 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B748457 : Blo 330750 748457 := bstep (se 2 (by rfl) ⟨280671, by rfl⟩ : syracuseStep 748457 = 561343) B561343
theorem B420967 : Blo 330750 420967 := bstep (se 1 (by rfl) ⟨315725, by rfl⟩ : syracuseStep 420967 = 631451) B631451
theorem B2749469 : Blo 330750 2749469 := bstep (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) B1031051
theorem B1897769 : Blo 330750 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B1897951 : Blo 330750 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B2848841 : Blo 330750 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B3045671 : Blo 330750 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B948635 : Blo 330750 948635 := bstep (se 1 (by rfl) ⟨711476, by rfl⟩ : syracuseStep 948635 = 1422953) B1422953
theorem B752183 : Blo 330750 752183 := bstep (se 1 (by rfl) ⟨564137, by rfl⟩ : syracuseStep 752183 = 1128275) B1128275
theorem B752255 : Blo 330750 752255 := bstep (se 1 (by rfl) ⟨564191, by rfl⟩ : syracuseStep 752255 = 1128383) B1128383
theorem B2128943 : Blo 330750 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B39353971 : Blo 330750 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B2392699 : Blo 330750 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B755369 : Blo 330750 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B756463 : Blo 330750 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B2558729 : Blo 330750 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B330879 : Blo 330750 330879 := bstep (se 1 (by rfl) ⟨248159, by rfl⟩ : syracuseStep 330879 = 496319) B496319
theorem B331003 : Blo 330750 331003 := bstep (se 1 (by rfl) ⟨248252, by rfl⟩ : syracuseStep 331003 = 496505) B496505
theorem B331391 : Blo 330750 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B1675241 : Blo 330750 1675241 := bstep (se 2 (by rfl) ⟨628215, by rfl⟩ : syracuseStep 1675241 = 1256431) B1256431
theorem B331775 : Blo 330750 331775 := bstep (se 1 (by rfl) ⟨248831, by rfl⟩ : syracuseStep 331775 = 497663) B497663
theorem B561289 : Blo 330750 561289 := bstep (se 2 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 561289 = 420967) B420967
theorem B1675403 : Blo 330750 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B332223 : Blo 330750 332223 := bstep (se 1 (by rfl) ⟨249167, by rfl⟩ : syracuseStep 332223 = 498335) B498335
theorem B1905241 : Blo 330750 1905241 := bstep (se 2 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 1905241 = 1428931) B1428931
theorem B1446491 : Blo 330750 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B332891 : Blo 330750 332891 := bstep (se 1 (by rfl) ⟨249668, by rfl⟩ : syracuseStep 332891 = 499337) B499337
theorem B332903 : Blo 330750 332903 := bstep (se 1 (by rfl) ⟨249677, by rfl⟩ : syracuseStep 332903 = 499355) B499355
theorem B332927 : Blo 330750 332927 := bstep (se 1 (by rfl) ⟨249695, by rfl⟩ : syracuseStep 332927 = 499391) B499391
theorem B496943 : Blo 330750 496943 := bstep (se 1 (by rfl) ⟨372707, by rfl⟩ : syracuseStep 496943 = 745415) B745415
theorem B333183 : Blo 330750 333183 := bstep (se 1 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 333183 = 499775) B499775
theorem B333339 : Blo 330750 333339 := bstep (se 1 (by rfl) ⟨250004, by rfl⟩ : syracuseStep 333339 = 500009) B500009
theorem B333439 : Blo 330750 333439 := bstep (se 1 (by rfl) ⟨250079, by rfl⟩ : syracuseStep 333439 = 500159) B500159
theorem B333679 : Blo 330750 333679 := bstep (se 1 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 333679 = 500519) B500519
theorem B333823 : Blo 330750 333823 := bstep (se 1 (by rfl) ⟨250367, by rfl⟩ : syracuseStep 333823 = 500735) B500735
theorem B333951 : Blo 330750 333951 := bstep (se 1 (by rfl) ⟨250463, by rfl⟩ : syracuseStep 333951 = 500927) B500927
theorem B1120823 : Blo 330750 1120823 := bstep (se 1 (by rfl) ⟨840617, by rfl⟩ : syracuseStep 1120823 = 1681235) B1681235
theorem B1415809 : Blo 330750 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B334543 : Blo 330750 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B1678319 : Blo 330750 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B1121363 : Blo 330750 1121363 := bstep (se 1 (by rfl) ⟨841022, by rfl⟩ : syracuseStep 1121363 = 1682045) B1682045
theorem B1121471 : Blo 330750 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B498971 : Blo 330750 498971 := bstep (se 1 (by rfl) ⟨374228, by rfl⟩ : syracuseStep 498971 = 748457) B748457
theorem B2530601 : Blo 330750 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B2564455 : Blo 330750 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B533351 : Blo 330750 533351 := bstep (se 1 (by rfl) ⟨400013, by rfl⟩ : syracuseStep 533351 = 800027) B800027
theorem B1123361 : Blo 330750 1123361 := bstep (se 2 (by rfl) ⟨421260, by rfl⟩ : syracuseStep 1123361 = 842521) B842521
theorem B1680425 : Blo 330750 1680425 := bstep (se 2 (by rfl) ⟨630159, by rfl⟩ : syracuseStep 1680425 = 1260319) B1260319
theorem B500873 : Blo 330750 500873 := bstep (se 2 (by rfl) ⟨187827, by rfl⟩ : syracuseStep 500873 = 375655) B375655
theorem B29697455 : Blo 330750 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B632423 : Blo 330750 632423 := bstep (se 1 (by rfl) ⟨474317, by rfl⟩ : syracuseStep 632423 = 948635) B948635
theorem B501455 : Blo 330750 501455 := bstep (se 1 (by rfl) ⟨376091, by rfl⟩ : syracuseStep 501455 = 752183) B752183
theorem B501503 : Blo 330750 501503 := bstep (se 1 (by rfl) ⟨376127, by rfl⟩ : syracuseStep 501503 = 752255) B752255
theorem B1419295 : Blo 330750 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B52471961 : Blo 330750 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B65547467 : Blo 330750 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B1912673 : Blo 330750 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B1683503 : Blo 330750 1683503 := bstep (se 1 (by rfl) ⟨1262627, by rfl⟩ : syracuseStep 1683503 = 2525255) B2525255
theorem B1257707 : Blo 330750 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B1062011 : Blo 330750 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B1684961 : Blo 330750 1684961 := bstep (se 2 (by rfl) ⟨631860, by rfl⟩ : syracuseStep 1684961 = 1263721) B1263721
theorem B1128761 : Blo 330750 1128761 := bstep (se 2 (by rfl) ⟨423285, by rfl⟩ : syracuseStep 1128761 = 846571) B846571
theorem B2537891 : Blo 330750 2537891 := bstep (se 1 (by rfl) ⟨1903418, by rfl⟩ : syracuseStep 2537891 = 3806837) B3806837
theorem B2013779 : Blo 330750 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B2538377 : Blo 330750 2538377 := bstep (se 2 (by rfl) ⟨951891, by rfl⟩ : syracuseStep 2538377 = 1903783) B1903783
theorem B801775 : Blo 330750 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B375835 : Blo 330750 375835 := bstep (se 1 (by rfl) ⟨281876, by rfl⟩ : syracuseStep 375835 = 563753) B563753
theorem B375871 : Blo 330750 375871 := bstep (se 1 (by rfl) ⟨281903, by rfl⟩ : syracuseStep 375871 = 563807) B563807
theorem B3128489 : Blo 330750 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B2408555 : Blo 330750 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B475303 : Blo 330750 475303 := bstep (se 1 (by rfl) ⟨356477, by rfl⟩ : syracuseStep 475303 = 712955) B712955
theorem B6177059 : Blo 330750 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B5686199 : Blo 330750 5686199 := bstep (se 1 (by rfl) ⟨4264649, by rfl⟩ : syracuseStep 5686199 = 8529299) B8529299
theorem B1688687 : Blo 330750 1688687 := bstep (se 1 (by rfl) ⟨1266515, by rfl⟩ : syracuseStep 1688687 = 2533031) B2533031
theorem B837479 : Blo 330750 837479 := bstep (se 1 (by rfl) ⟨628109, by rfl⟩ : syracuseStep 837479 = 1256219) B1256219
theorem B1066907 : Blo 330750 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B707051 : Blo 330750 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B1624943 : Blo 330750 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B1265179 : Blo 330750 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B44092997 : Blo 330750 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B839393 : Blo 330750 839393 := bstep (se 2 (by rfl) ⟨314772, by rfl⟩ : syracuseStep 839393 = 629545) B629545
theorem B839423 : Blo 330750 839423 := bstep (se 1 (by rfl) ⟨629567, by rfl⟩ : syracuseStep 839423 = 1259135) B1259135
theorem B3198761 : Blo 330750 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B12210689 : Blo 330750 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B1201655 : Blo 330750 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B841499 : Blo 330750 841499 := bstep (se 1 (by rfl) ⟨631124, by rfl⟩ : syracuseStep 841499 = 1262249) B1262249
theorem B744443 : Blo 330750 744443 := bstep (se 1 (by rfl) ⟨558332, by rfl⟩ : syracuseStep 744443 = 1116665) B1116665
theorem B41016455 : Blo 330750 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B744767 : Blo 330750 744767 := bstep (se 1 (by rfl) ⟨558575, by rfl⟩ : syracuseStep 744767 = 1117151) B1117151
theorem B744911 : Blo 330750 744911 := bstep (se 1 (by rfl) ⟨558683, by rfl⟩ : syracuseStep 744911 = 1117367) B1117367
theorem B7331917 : Blo 330750 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B713441 : Blo 330750 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B3203873 : Blo 330750 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B844607 : Blo 330750 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B844769 : Blo 330750 844769 := bstep (se 2 (by rfl) ⟨316788, by rfl⟩ : syracuseStep 844769 = 633577) B633577
theorem B746747 : Blo 330750 746747 := bstep (se 1 (by rfl) ⟨560060, by rfl⟩ : syracuseStep 746747 = 1120121) B1120121
theorem B2385233 : Blo 330750 2385233 := bstep (se 2 (by rfl) ⟨894462, by rfl⟩ : syracuseStep 2385233 = 1788925) B1788925
theorem B943771 : Blo 330750 943771 := bstep (se 1 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 943771 = 1415657) B1415657
theorem B419519 : Blo 330750 419519 := bstep (se 1 (by rfl) ⟨314639, by rfl⟩ : syracuseStep 419519 = 629279) B629279
theorem B420167 : Blo 330750 420167 := bstep (se 1 (by rfl) ⟨315125, by rfl⟩ : syracuseStep 420167 = 630251) B630251
theorem B420223 : Blo 330750 420223 := bstep (se 1 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 420223 = 630335) B630335
theorem B944921 : Blo 330750 944921 := bstep (se 2 (by rfl) ⟨354345, by rfl⟩ : syracuseStep 944921 = 708691) B708691
theorem B846713 : Blo 330750 846713 := bstep (se 2 (by rfl) ⟨317517, by rfl⟩ : syracuseStep 846713 = 635035) B635035
theorem B6188123 : Blo 330750 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B1077491 : Blo 330750 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B4125127 : Blo 330750 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B1372841 : Blo 330750 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B750419 : Blo 330750 750419 := bstep (se 1 (by rfl) ⟨562814, by rfl⟩ : syracuseStep 750419 = 1125629) B1125629
theorem B751031 : Blo 330750 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B751463 : Blo 330750 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B1899227 : Blo 330750 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B2030447 : Blo 330750 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B753119 : Blo 330750 753119 := bstep (se 1 (by rfl) ⟨564839, by rfl⟩ : syracuseStep 753119 = 1129679) B1129679
theorem B1343135 : Blo 330750 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B1605703 : Blo 330750 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B558319 : Blo 330750 558319 := bstep (se 1 (by rfl) ⟨418739, by rfl⟩ : syracuseStep 558319 = 837479) B837479
theorem B1705819 : Blo 330750 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B1083295 : Blo 330750 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B29395331 : Blo 330750 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B559595 : Blo 330750 559595 := bstep (se 1 (by rfl) ⟨419696, by rfl⟩ : syracuseStep 559595 = 839393) B839393
theorem B559615 : Blo 330750 559615 := bstep (se 1 (by rfl) ⟨419711, by rfl⟩ : syracuseStep 559615 = 839423) B839423
theorem B2132507 : Blo 330750 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B1116827 : Blo 330750 1116827 := bstep (se 1 (by rfl) ⟨837620, by rfl⟩ : syracuseStep 1116827 = 1675241) B1675241
theorem B1116935 : Blo 330750 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B560297 : Blo 330750 560297 := bstep (se 2 (by rfl) ⟨210111, by rfl⟩ : syracuseStep 560297 = 420223) B420223
theorem B331295 : Blo 330750 331295 := bstep (se 1 (by rfl) ⟨248471, by rfl⟩ : syracuseStep 331295 = 496943) B496943
theorem B560999 : Blo 330750 560999 := bstep (se 1 (by rfl) ⟨420749, by rfl⟩ : syracuseStep 560999 = 841499) B841499
theorem B1118717 : Blo 330750 1118717 := bstep (se 3 (by rfl) ⟨209759, by rfl⟩ : syracuseStep 1118717 = 419519) B419519
theorem B1118879 : Blo 330750 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B496295 : Blo 330750 496295 := bstep (se 1 (by rfl) ⟨372221, by rfl⟩ : syracuseStep 496295 = 744443) B744443
theorem B332647 : Blo 330750 332647 := bstep (se 1 (by rfl) ⟨249485, by rfl⟩ : syracuseStep 332647 = 498971) B498971
theorem B496511 : Blo 330750 496511 := bstep (se 1 (by rfl) ⟨372383, by rfl⟩ : syracuseStep 496511 = 744767) B744767
theorem B496607 : Blo 330750 496607 := bstep (se 1 (by rfl) ⟨372455, by rfl⟩ : syracuseStep 496607 = 744911) B744911
theorem B2135915 : Blo 330750 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B563071 : Blo 330750 563071 := bstep (se 1 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 563071 = 844607) B844607
theorem B563179 : Blo 330750 563179 := bstep (se 1 (by rfl) ⟨422384, by rfl⟩ : syracuseStep 563179 = 844769) B844769
theorem B1120283 : Blo 330750 1120283 := bstep (se 1 (by rfl) ⟨840212, by rfl⟩ : syracuseStep 1120283 = 1680425) B1680425
theorem B333915 : Blo 330750 333915 := bstep (se 1 (by rfl) ⟨250436, by rfl⟩ : syracuseStep 333915 = 500873) B500873
theorem B497831 : Blo 330750 497831 := bstep (se 1 (by rfl) ⟨373373, by rfl⟩ : syracuseStep 497831 = 746747) B746747
theorem B1120445 : Blo 330750 1120445 := bstep (se 3 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 1120445 = 420167) B420167
theorem B334303 : Blo 330750 334303 := bstep (se 1 (by rfl) ⟨250727, by rfl⟩ : syracuseStep 334303 = 501455) B501455
theorem B334335 : Blo 330750 334335 := bstep (se 1 (by rfl) ⟨250751, by rfl⟩ : syracuseStep 334335 = 501503) B501503
theorem B629947 : Blo 330750 629947 := bstep (se 1 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 629947 = 944921) B944921
theorem B564475 : Blo 330750 564475 := bstep (se 1 (by rfl) ⟨423356, by rfl⟩ : syracuseStep 564475 = 846713) B846713
theorem B1122335 : Blo 330750 1122335 := bstep (se 1 (by rfl) ⟨841751, by rfl⟩ : syracuseStep 1122335 = 1683503) B1683503
theorem B500279 : Blo 330750 500279 := bstep (se 1 (by rfl) ⟨375209, by rfl⟩ : syracuseStep 500279 = 750419) B750419
theorem B500687 : Blo 330750 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B1123307 : Blo 330750 1123307 := bstep (se 1 (by rfl) ⟨842480, by rfl⟩ : syracuseStep 1123307 = 1684961) B1684961
theorem B500975 : Blo 330750 500975 := bstep (se 1 (by rfl) ⟨375731, by rfl⟩ : syracuseStep 500975 = 751463) B751463
theorem B501113 : Blo 330750 501113 := bstep (se 2 (by rfl) ⟨187917, by rfl⟩ : syracuseStep 501113 = 375835) B375835
theorem B501161 : Blo 330750 501161 := bstep (se 2 (by rfl) ⟨187935, by rfl⟩ : syracuseStep 501161 = 375871) B375871
theorem B1353631 : Blo 330750 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B502079 : Blo 330750 502079 := bstep (se 1 (by rfl) ⟨376559, by rfl⟩ : syracuseStep 502079 = 753119) B753119
theorem B895423 : Blo 330750 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B9775889 : Blo 330750 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B633737 : Blo 330750 633737 := bstep (se 2 (by rfl) ⟨237651, by rfl⟩ : syracuseStep 633737 = 475303) B475303
theorem B3419273 : Blo 330750 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B1125791 : Blo 330750 1125791 := bstep (se 1 (by rfl) ⟨844343, by rfl⟩ : syracuseStep 1125791 = 1688687) B1688687
theorem B3190265 : Blo 330750 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B503579 : Blo 330750 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B471367 : Blo 330750 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B1258361 : Blo 330750 1258361 := bstep (se 2 (by rfl) ⟨471885, by rfl⟩ : syracuseStep 1258361 = 943771) B943771
theorem B1422269 : Blo 330750 1422269 := bstep (se 3 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 1422269 = 533351) B533351
theorem B2832029 : Blo 330750 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B8140459 : Blo 330750 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B964327 : Blo 330750 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B801103 : Blo 330750 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B1686905 : Blo 330750 1686905 := bstep (se 2 (by rfl) ⟨632589, by rfl⟩ : syracuseStep 1686905 = 1265179) B1265179
theorem B27344303 : Blo 330750 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B1687067 : Blo 330750 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B475627 : Blo 330750 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B2540321 : Blo 330750 2540321 := bstep (se 2 (by rfl) ⟨952620, by rfl⟩ : syracuseStep 2540321 = 1905241) B1905241
theorem B1590155 : Blo 330750 1590155 := bstep (se 1 (by rfl) ⟨1192616, by rfl⟩ : syracuseStep 1590155 = 2385233) B2385233
theorem B34981307 : Blo 330750 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B43698311 : Blo 330750 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B838471 : Blo 330750 838471 := bstep (se 1 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 838471 = 1257707) B1257707
theorem B1887745 : Blo 330750 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B1069033 : Blo 330750 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B1691927 : Blo 330750 1691927 := bstep (se 1 (by rfl) ⟨1268945, by rfl⟩ : syracuseStep 1691927 = 2537891) B2537891
theorem B1266151 : Blo 330750 1266151 := bstep (se 1 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 1266151 = 1899227) B1899227
theorem B1692251 : Blo 330750 1692251 := bstep (se 1 (by rfl) ⟨1269188, by rfl⟩ : syracuseStep 1692251 = 2538377) B2538377
theorem B2085659 : Blo 330750 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B5100461 : Blo 330750 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B4118039 : Blo 330750 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B3790799 : Blo 330750 3790799 := bstep (se 1 (by rfl) ⟨2843099, by rfl⟩ : syracuseStep 3790799 = 5686199) B5686199
theorem B711271 : Blo 330750 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1892393 : Blo 330750 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B1008617 : Blo 330750 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B79193213 : Blo 330750 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B747215 : Blo 330750 747215 := bstep (se 1 (by rfl) ⟨560411, by rfl⟩ : syracuseStep 747215 = 1120823) B1120823
theorem B747575 : Blo 330750 747575 := bstep (se 1 (by rfl) ⟨560681, by rfl⟩ : syracuseStep 747575 = 1121363) B1121363
theorem B747647 : Blo 330750 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B748385 : Blo 330750 748385 := bstep (se 2 (by rfl) ⟨280644, by rfl⟩ : syracuseStep 748385 = 561289) B561289
theorem B5500169 : Blo 330750 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B748907 : Blo 330750 748907 := bstep (se 1 (by rfl) ⟨561680, by rfl⟩ : syracuseStep 748907 = 1123361) B1123361
theorem B421615 : Blo 330750 421615 := bstep (se 1 (by rfl) ⟨316211, by rfl⟩ : syracuseStep 421615 = 632423) B632423
theorem B5370077 : Blo 330750 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B4125415 : Blo 330750 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B718327 : Blo 330750 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B915227 : Blo 330750 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B752507 : Blo 330750 752507 := bstep (se 1 (by rfl) ⟨564380, by rfl⟩ : syracuseStep 752507 = 1128761) B1128761
theorem B29132207 : Blo 330750 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B19596887 : Blo 330750 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B1804841 : Blo 330750 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B2689645 : Blo 330750 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B330863 : Blo 330750 330863 := bstep (se 1 (by rfl) ⟨248147, by rfl⟩ : syracuseStep 330863 = 496295) B496295
theorem B331007 : Blo 330750 331007 := bstep (se 1 (by rfl) ⟨248255, by rfl⟩ : syracuseStep 331007 = 496511) B496511
theorem B331071 : Blo 330750 331071 := bstep (se 1 (by rfl) ⟨248303, by rfl⟩ : syracuseStep 331071 = 496607) B496607
theorem B1117961 : Blo 330750 1117961 := bstep (se 2 (by rfl) ⟨419235, by rfl⟩ : syracuseStep 1117961 = 838471) B838471
theorem B2527199 : Blo 330750 2527199 := bstep (se 1 (by rfl) ⟨1895399, by rfl⟩ : syracuseStep 2527199 = 3790799) B3790799
theorem B331887 : Blo 330750 331887 := bstep (se 1 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 331887 = 497831) B497831
theorem B562153 : Blo 330750 562153 := bstep (se 2 (by rfl) ⟨210807, by rfl⟩ : syracuseStep 562153 = 421615) B421615
theorem B333519 : Blo 330750 333519 := bstep (se 1 (by rfl) ⟨250139, by rfl⟩ : syracuseStep 333519 = 500279) B500279
theorem B628489 : Blo 330750 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B333791 : Blo 330750 333791 := bstep (se 1 (by rfl) ⟨250343, by rfl⟩ : syracuseStep 333791 = 500687) B500687
theorem B52795475 : Blo 330750 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B333983 : Blo 330750 333983 := bstep (se 1 (by rfl) ⟨250487, by rfl⟩ : syracuseStep 333983 = 500975) B500975
theorem B334075 : Blo 330750 334075 := bstep (se 1 (by rfl) ⟨250556, by rfl⟩ : syracuseStep 334075 = 501113) B501113
theorem B334107 : Blo 330750 334107 := bstep (se 1 (by rfl) ⟨250580, by rfl⟩ : syracuseStep 334107 = 501161) B501161
theorem B498143 : Blo 330750 498143 := bstep (se 1 (by rfl) ⟨373607, by rfl⟩ : syracuseStep 498143 = 747215) B747215
theorem B498383 : Blo 330750 498383 := bstep (se 1 (by rfl) ⟨373787, by rfl⟩ : syracuseStep 498383 = 747575) B747575
theorem B498431 : Blo 330750 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B334719 : Blo 330750 334719 := bstep (se 1 (by rfl) ⟨251039, by rfl⟩ : syracuseStep 334719 = 502079) B502079
theorem B498923 : Blo 330750 498923 := bstep (se 1 (by rfl) ⟨374192, by rfl⟩ : syracuseStep 498923 = 748385) B748385
theorem B10853945 : Blo 330750 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B499271 : Blo 330750 499271 := bstep (se 1 (by rfl) ⟨374453, by rfl⟩ : syracuseStep 499271 = 748907) B748907
theorem B1285769 : Blo 330750 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B335719 : Blo 330750 335719 := bstep (se 1 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 335719 = 503579) B503579
theorem B3580051 : Blo 330750 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B501671 : Blo 330750 501671 := bstep (se 1 (by rfl) ⟨376253, by rfl⟩ : syracuseStep 501671 = 752507) B752507
theorem B5777573 : Blo 330750 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B1124603 : Blo 330750 1124603 := bstep (se 1 (by rfl) ⟨843452, by rfl⟩ : syracuseStep 1124603 = 1686905) B1686905
theorem B18229535 : Blo 330750 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B1124711 : Blo 330750 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B2140937 : Blo 330750 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B1060103 : Blo 330750 1060103 := bstep (se 1 (by rfl) ⟨795077, by rfl⟩ : syracuseStep 1060103 = 1590155) B1590155
theorem B634169 : Blo 330750 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B373063 : Blo 330750 373063 := bstep (se 1 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 373063 = 559595) B559595
theorem B1421671 : Blo 330750 1421671 := bstep (se 1 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 1421671 = 2132507) B2132507
theorem B373531 : Blo 330750 373531 := bstep (se 1 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 373531 = 560297) B560297
theorem B2274425 : Blo 330750 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B373999 : Blo 330750 373999 := bstep (se 1 (by rfl) ⟨280499, by rfl⟩ : syracuseStep 373999 = 560999) B560999
theorem B1127951 : Blo 330750 1127951 := bstep (se 1 (by rfl) ⟨845963, by rfl⟩ : syracuseStep 1127951 = 1691927) B1691927
theorem B1128167 : Blo 330750 1128167 := bstep (se 1 (by rfl) ⟨846125, by rfl⟩ : syracuseStep 1128167 = 1692251) B1692251
theorem B1390439 : Blo 330750 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B1193897 : Blo 330750 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1423943 : Blo 330750 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B1425377 : Blo 330750 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B1261595 : Blo 330750 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B1688201 : Blo 330750 1688201 := bstep (se 2 (by rfl) ⟨633075, by rfl⟩ : syracuseStep 1688201 = 1266151) B1266151
theorem B2279515 : Blo 330750 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B1068137 : Blo 330750 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B838907 : Blo 330750 838907 := bstep (se 1 (by rfl) ⟨629180, by rfl⟩ : syracuseStep 838907 = 1258361) B1258361
theorem B1888019 : Blo 330750 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B610151 : Blo 330750 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B839929 : Blo 330750 839929 := bstep (se 2 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 839929 = 629947) B629947
theorem B1693547 : Blo 330750 1693547 := bstep (se 1 (by rfl) ⟨1270160, by rfl⟩ : syracuseStep 1693547 = 2540321) B2540321
theorem B23320871 : Blo 330750 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B744425 : Blo 330750 744425 := bstep (se 2 (by rfl) ⟨279159, by rfl⟩ : syracuseStep 744425 = 558319) B558319
theorem B744551 : Blo 330750 744551 := bstep (se 1 (by rfl) ⟨558413, by rfl⟩ : syracuseStep 744551 = 1116827) B1116827
theorem B744623 : Blo 330750 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B745811 : Blo 330750 745811 := bstep (se 1 (by rfl) ⟨559358, by rfl⟩ : syracuseStep 745811 = 1118717) B1118717
theorem B745919 : Blo 330750 745919 := bstep (se 1 (by rfl) ⟨559439, by rfl⟩ : syracuseStep 745919 = 1118879) B1118879
theorem B3400307 : Blo 330750 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B746153 : Blo 330750 746153 := bstep (se 2 (by rfl) ⟨279807, by rfl⟩ : syracuseStep 746153 = 559615) B559615
theorem B2745359 : Blo 330750 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B746855 : Blo 330750 746855 := bstep (se 1 (by rfl) ⟨560141, by rfl⟩ : syracuseStep 746855 = 1120283) B1120283
theorem B746963 : Blo 330750 746963 := bstep (se 1 (by rfl) ⟨560222, by rfl⟩ : syracuseStep 746963 = 1120445) B1120445
theorem B2516993 : Blo 330750 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B748223 : Blo 330750 748223 := bstep (se 1 (by rfl) ⟨561167, by rfl⟩ : syracuseStep 748223 = 1122335) B1122335
theorem B748871 : Blo 330750 748871 := bstep (se 1 (by rfl) ⟨561653, by rfl⟩ : syracuseStep 748871 = 1123307) B1123307
theorem B5500553 : Blo 330750 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B6517259 : Blo 330750 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B422491 : Blo 330750 422491 := bstep (se 1 (by rfl) ⟨316868, by rfl⟩ : syracuseStep 422491 = 633737) B633737
theorem B3666779 : Blo 330750 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B750527 : Blo 330750 750527 := bstep (se 1 (by rfl) ⟨562895, by rfl⟩ : syracuseStep 750527 = 1125791) B1125791
theorem B2126843 : Blo 330750 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B750761 : Blo 330750 750761 := bstep (se 2 (by rfl) ⟨281535, by rfl⟩ : syracuseStep 750761 = 563071) B563071
theorem B3831077 : Blo 330750 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B750905 : Blo 330750 750905 := bstep (se 2 (by rfl) ⟨281589, by rfl⟩ : syracuseStep 750905 = 563179) B563179
theorem B948179 : Blo 330750 948179 := bstep (se 1 (by rfl) ⟨711134, by rfl⟩ : syracuseStep 948179 = 1422269) B1422269
theorem B948361 : Blo 330750 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B752633 : Blo 330750 752633 := bstep (se 2 (by rfl) ⟨282237, by rfl⟩ : syracuseStep 752633 = 564475) B564475
theorem B559271 : Blo 330750 559271 := bstep (se 1 (by rfl) ⟨419453, by rfl⟩ : syracuseStep 559271 = 838907) B838907
theorem B35196983 : Blo 330750 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B332095 : Blo 330750 332095 := bstep (se 1 (by rfl) ⟨249071, by rfl⟩ : syracuseStep 332095 = 498143) B498143
theorem B332255 : Blo 330750 332255 := bstep (se 1 (by rfl) ⟨249191, by rfl⟩ : syracuseStep 332255 = 498383) B498383
theorem B332287 : Blo 330750 332287 := bstep (se 1 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 332287 = 498431) B498431
theorem B496283 : Blo 330750 496283 := bstep (se 1 (by rfl) ⟨372212, by rfl⟩ : syracuseStep 496283 = 744425) B744425
theorem B496367 : Blo 330750 496367 := bstep (se 1 (by rfl) ⟨372275, by rfl⟩ : syracuseStep 496367 = 744551) B744551
theorem B496415 : Blo 330750 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B332615 : Blo 330750 332615 := bstep (se 1 (by rfl) ⟨249461, by rfl⟩ : syracuseStep 332615 = 498923) B498923
theorem B332847 : Blo 330750 332847 := bstep (se 1 (by rfl) ⟨249635, by rfl⟩ : syracuseStep 332847 = 499271) B499271
theorem B857179 : Blo 330750 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B3183725 : Blo 330750 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B497207 : Blo 330750 497207 := bstep (se 1 (by rfl) ⟨372905, by rfl⟩ : syracuseStep 497207 = 745811) B745811
theorem B497279 : Blo 330750 497279 := bstep (se 1 (by rfl) ⟨372959, by rfl⟩ : syracuseStep 497279 = 745919) B745919
theorem B1119905 : Blo 330750 1119905 := bstep (se 2 (by rfl) ⟨419964, by rfl⟩ : syracuseStep 1119905 = 839929) B839929
theorem B2266871 : Blo 330750 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B497417 : Blo 330750 497417 := bstep (se 2 (by rfl) ⟨186531, by rfl⟩ : syracuseStep 497417 = 373063) B373063
theorem B15406861 : Blo 330750 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B497435 : Blo 330750 497435 := bstep (se 1 (by rfl) ⟨373076, by rfl⟩ : syracuseStep 497435 = 746153) B746153
theorem B563321 : Blo 330750 563321 := bstep (se 2 (by rfl) ⟨211245, by rfl⟩ : syracuseStep 563321 = 422491) B422491
theorem B497903 : Blo 330750 497903 := bstep (se 1 (by rfl) ⟨373427, by rfl⟩ : syracuseStep 497903 = 746855) B746855
theorem B497975 : Blo 330750 497975 := bstep (se 1 (by rfl) ⟨373481, by rfl⟩ : syracuseStep 497975 = 746963) B746963
theorem B498041 : Blo 330750 498041 := bstep (se 2 (by rfl) ⟨186765, by rfl⟩ : syracuseStep 498041 = 373531) B373531
theorem B334447 : Blo 330750 334447 := bstep (se 1 (by rfl) ⟨250835, by rfl⟩ : syracuseStep 334447 = 501671) B501671
theorem B1677995 : Blo 330750 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B498665 : Blo 330750 498665 := bstep (se 2 (by rfl) ⟨186999, by rfl⟩ : syracuseStep 498665 = 373999) B373999
theorem B498815 : Blo 330750 498815 := bstep (se 1 (by rfl) ⟨374111, by rfl⟩ : syracuseStep 498815 = 748223) B748223
theorem B499247 : Blo 330750 499247 := bstep (se 1 (by rfl) ⟨374435, by rfl⟩ : syracuseStep 499247 = 748871) B748871
theorem B500351 : Blo 330750 500351 := bstep (se 1 (by rfl) ⟨375263, by rfl⟩ : syracuseStep 500351 = 750527) B750527
theorem B1417895 : Blo 330750 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B1516283 : Blo 330750 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B500507 : Blo 330750 500507 := bstep (se 1 (by rfl) ⟨375380, by rfl⟩ : syracuseStep 500507 = 750761) B750761
theorem B500603 : Blo 330750 500603 := bstep (se 1 (by rfl) ⟨375452, by rfl⟩ : syracuseStep 500603 = 750905) B750905
theorem B926959 : Blo 330750 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B632119 : Blo 330750 632119 := bstep (se 1 (by rfl) ⟨474089, by rfl⟩ : syracuseStep 632119 = 948179) B948179
theorem B501755 : Blo 330750 501755 := bstep (se 1 (by rfl) ⟨376316, by rfl⟩ : syracuseStep 501755 = 752633) B752633
theorem B1125467 : Blo 330750 1125467 := bstep (se 1 (by rfl) ⟨844100, by rfl⟩ : syracuseStep 1125467 = 1688201) B1688201
theorem B1258679 : Blo 330750 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B1684799 : Blo 330750 1684799 := bstep (se 1 (by rfl) ⟨1263599, by rfl⟩ : syracuseStep 1684799 = 2527199) B2527199
theorem B3586193 : Blo 330750 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1129031 : Blo 330750 1129031 := bstep (se 1 (by rfl) ⟨846773, by rfl⟩ : syracuseStep 1129031 = 1693547) B1693547
theorem B15547247 : Blo 330750 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B1427291 : Blo 330750 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B706735 : Blo 330750 706735 := bstep (se 1 (by rfl) ⟨530051, by rfl⟩ : syracuseStep 706735 = 1060103) B1060103
theorem B837985 : Blo 330750 837985 := bstep (se 2 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 837985 = 628489) B628489
theorem B1264481 : Blo 330750 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B4344839 : Blo 330750 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B2444519 : Blo 330750 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B1691117 : Blo 330750 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B14668141 : Blo 330750 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B1627069 : Blo 330750 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B447625 : Blo 330750 447625 := bstep (se 2 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 447625 = 335719) B335719
theorem B841063 : Blo 330750 841063 := bstep (se 1 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 841063 = 1261595) B1261595
theorem B4773401 : Blo 330750 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B19421471 : Blo 330750 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B13064591 : Blo 330750 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B1203227 : Blo 330750 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B712091 : Blo 330750 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B745307 : Blo 330750 745307 := bstep (se 1 (by rfl) ⟨558980, by rfl⟩ : syracuseStep 745307 = 1117961) B1117961
theorem B3039353 : Blo 330750 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B7235963 : Blo 330750 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B1895561 : Blo 330750 1895561 := bstep (se 2 (by rfl) ⟨710835, by rfl⟩ : syracuseStep 1895561 = 1421671) B1421671
theorem B1830239 : Blo 330750 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B749537 : Blo 330750 749537 := bstep (se 2 (by rfl) ⟨281076, by rfl⟩ : syracuseStep 749537 = 562153) B562153
theorem B749735 : Blo 330750 749735 := bstep (se 1 (by rfl) ⟨562301, by rfl⟩ : syracuseStep 749735 = 1124603) B1124603
theorem B12153023 : Blo 330750 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B749807 : Blo 330750 749807 := bstep (se 1 (by rfl) ⟨562355, by rfl⟩ : syracuseStep 749807 = 1124711) B1124711
theorem B2554051 : Blo 330750 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B751967 : Blo 330750 751967 := bstep (se 1 (by rfl) ⟨563975, by rfl⟩ : syracuseStep 751967 = 1127951) B1127951
theorem B752111 : Blo 330750 752111 := bstep (se 1 (by rfl) ⟨564083, by rfl⟩ : syracuseStep 752111 = 1128167) B1128167
theorem B949295 : Blo 330750 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B3801005 : Blo 330750 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B951527 : Blo 330750 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B23464655 : Blo 330750 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B8489933 : Blo 330750 8489933 := bstep (se 3 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 8489933 = 3183725) B3183725
theorem B330855 : Blo 330750 330855 := bstep (se 1 (by rfl) ⟨248141, by rfl⟩ : syracuseStep 330855 = 496283) B496283
theorem B1117313 : Blo 330750 1117313 := bstep (se 2 (by rfl) ⟨418992, by rfl⟩ : syracuseStep 1117313 = 837985) B837985
theorem B330911 : Blo 330750 330911 := bstep (se 1 (by rfl) ⟨248183, by rfl⟩ : syracuseStep 330911 = 496367) B496367
theorem B330943 : Blo 330750 330943 := bstep (se 1 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 330943 = 496415) B496415
theorem B3182267 : Blo 330750 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B331471 : Blo 330750 331471 := bstep (se 1 (by rfl) ⟨248603, by rfl⟩ : syracuseStep 331471 = 497207) B497207
theorem B331519 : Blo 330750 331519 := bstep (se 1 (by rfl) ⟨248639, by rfl⟩ : syracuseStep 331519 = 497279) B497279
theorem B331611 : Blo 330750 331611 := bstep (se 1 (by rfl) ⟨248708, by rfl⟩ : syracuseStep 331611 = 497417) B497417
theorem B331623 : Blo 330750 331623 := bstep (se 1 (by rfl) ⟨248717, by rfl⟩ : syracuseStep 331623 = 497435) B497435
theorem B331935 : Blo 330750 331935 := bstep (se 1 (by rfl) ⟨248951, by rfl⟩ : syracuseStep 331935 = 497903) B497903
theorem B331983 : Blo 330750 331983 := bstep (se 1 (by rfl) ⟨248987, by rfl⟩ : syracuseStep 331983 = 497975) B497975
theorem B332027 : Blo 330750 332027 := bstep (se 1 (by rfl) ⟨249020, by rfl⟩ : syracuseStep 332027 = 498041) B498041
theorem B1118663 : Blo 330750 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B332443 : Blo 330750 332443 := bstep (se 1 (by rfl) ⟨249332, by rfl⟩ : syracuseStep 332443 = 498665) B498665
theorem B332543 : Blo 330750 332543 := bstep (se 1 (by rfl) ⟨249407, by rfl⟩ : syracuseStep 332543 = 498815) B498815
theorem B332831 : Blo 330750 332831 := bstep (se 1 (by rfl) ⟨249623, by rfl⟩ : syracuseStep 332831 = 499247) B499247
theorem B496871 : Blo 330750 496871 := bstep (se 1 (by rfl) ⟨372653, by rfl⟩ : syracuseStep 496871 = 745307) B745307
theorem B333567 : Blo 330750 333567 := bstep (se 1 (by rfl) ⟨250175, by rfl⟩ : syracuseStep 333567 = 500351) B500351
theorem B333671 : Blo 330750 333671 := bstep (se 1 (by rfl) ⟨250253, by rfl⟩ : syracuseStep 333671 = 500507) B500507
theorem B333735 : Blo 330750 333735 := bstep (se 1 (by rfl) ⟨250301, by rfl⟩ : syracuseStep 333735 = 500603) B500603
theorem B2169425 : Blo 330750 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B334503 : Blo 330750 334503 := bstep (se 1 (by rfl) ⟨250877, by rfl⟩ : syracuseStep 334503 = 501755) B501755
theorem B4823975 : Blo 330750 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B1121417 : Blo 330750 1121417 := bstep (se 2 (by rfl) ⟨420531, by rfl⟩ : syracuseStep 1121417 = 841063) B841063
theorem B1220159 : Blo 330750 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B499691 : Blo 330750 499691 := bstep (se 1 (by rfl) ⟨374768, by rfl⟩ : syracuseStep 499691 = 749537) B749537
theorem B499823 : Blo 330750 499823 := bstep (se 1 (by rfl) ⟨374867, by rfl⟩ : syracuseStep 499823 = 749735) B749735
theorem B8102015 : Blo 330750 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B499871 : Blo 330750 499871 := bstep (se 1 (by rfl) ⟨374903, by rfl⟩ : syracuseStep 499871 = 749807) B749807
theorem B1123199 : Blo 330750 1123199 := bstep (se 1 (by rfl) ⟨842399, by rfl⟩ : syracuseStep 1123199 = 1684799) B1684799
theorem B501311 : Blo 330750 501311 := bstep (se 1 (by rfl) ⟨375983, by rfl⟩ : syracuseStep 501311 = 751967) B751967
theorem B501407 : Blo 330750 501407 := bstep (se 1 (by rfl) ⟨376055, by rfl⟩ : syracuseStep 501407 = 752111) B752111
theorem B10364831 : Blo 330750 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B632863 : Blo 330750 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B2534003 : Blo 330750 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B372847 : Blo 330750 372847 := bstep (se 1 (by rfl) ⟨279635, by rfl⟩ : syracuseStep 372847 = 559271) B559271
theorem B2896559 : Blo 330750 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B1127411 : Blo 330750 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B375547 : Blo 330750 375547 := bstep (se 1 (by rfl) ⟨281660, by rfl⟩ : syracuseStep 375547 = 563321) B563321
theorem B6044989 : Blo 330750 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B802151 : Blo 330750 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B51790589 : Blo 330750 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B1263707 : Blo 330750 1263707 := bstep (se 1 (by rfl) ⟨947780, by rfl⟩ : syracuseStep 1263707 = 1895561) B1895561
theorem B839119 : Blo 330750 839119 := bstep (se 1 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 839119 = 1258679) B1258679
theorem B1235945 : Blo 330750 1235945 := bstep (se 2 (by rfl) ⟨463479, by rfl⟩ : syracuseStep 1235945 = 926959) B926959
theorem B842825 : Blo 330750 842825 := bstep (se 2 (by rfl) ⟨316059, by rfl⟩ : syracuseStep 842825 = 632119) B632119
theorem B842987 : Blo 330750 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B942313 : Blo 330750 942313 := bstep (se 2 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 942313 = 706735) B706735
theorem B746603 : Blo 330750 746603 := bstep (se 1 (by rfl) ⟨559952, by rfl⟩ : syracuseStep 746603 = 1119905) B1119905
theorem B8709727 : Blo 330750 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B2026235 : Blo 330750 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B945263 : Blo 330750 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B19557521 : Blo 330750 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B1010855 : Blo 330750 1010855 := bstep (se 1 (by rfl) ⟨758141, by rfl⟩ : syracuseStep 1010855 = 1516283) B1516283
theorem B2387333 : Blo 330750 2387333 := bstep (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) B447625
theorem B1142905 : Blo 330750 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B750311 : Blo 330750 750311 := bstep (se 1 (by rfl) ⟨562733, by rfl⟩ : syracuseStep 750311 = 1125467) B1125467
theorem B20542481 : Blo 330750 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B3405401 : Blo 330750 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B6518717 : Blo 330750 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B1898909 : Blo 330750 1898909 := bstep (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) B712091
theorem B2390795 : Blo 330750 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B752687 : Blo 330750 752687 := bstep (se 1 (by rfl) ⟨564515, by rfl⟩ : syracuseStep 752687 = 1129031) B1129031
theorem B331247 : Blo 330750 331247 := bstep (se 1 (by rfl) ⟨248435, by rfl⟩ : syracuseStep 331247 = 496871) B496871
theorem B1446283 : Blo 330750 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B1118825 : Blo 330750 1118825 := bstep (se 2 (by rfl) ⟨419559, by rfl⟩ : syracuseStep 1118825 = 839119) B839119
theorem B3215983 : Blo 330750 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B823963 : Blo 330750 823963 := bstep (se 1 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 823963 = 1235945) B1235945
theorem B561883 : Blo 330750 561883 := bstep (se 1 (by rfl) ⟨421412, by rfl⟩ : syracuseStep 561883 = 842825) B842825
theorem B561991 : Blo 330750 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B333127 : Blo 330750 333127 := bstep (se 1 (by rfl) ⟨249845, by rfl⟩ : syracuseStep 333127 = 499691) B499691
theorem B333215 : Blo 330750 333215 := bstep (se 1 (by rfl) ⟨249911, by rfl⟩ : syracuseStep 333215 = 499823) B499823
theorem B333247 : Blo 330750 333247 := bstep (se 1 (by rfl) ⟨249935, by rfl⟩ : syracuseStep 333247 = 499871) B499871
theorem B497129 : Blo 330750 497129 := bstep (se 2 (by rfl) ⟨186423, by rfl⟩ : syracuseStep 497129 = 372847) B372847
theorem B497735 : Blo 330750 497735 := bstep (se 1 (by rfl) ⟨373301, by rfl⟩ : syracuseStep 497735 = 746603) B746603
theorem B334207 : Blo 330750 334207 := bstep (se 1 (by rfl) ⟨250655, by rfl⟩ : syracuseStep 334207 = 501311) B501311
theorem B334271 : Blo 330750 334271 := bstep (se 1 (by rfl) ⟨250703, by rfl⟩ : syracuseStep 334271 = 501407) B501407
theorem B630175 : Blo 330750 630175 := bstep (se 1 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 630175 = 945263) B945263
theorem B500207 : Blo 330750 500207 := bstep (se 1 (by rfl) ⟨375155, by rfl⟩ : syracuseStep 500207 = 750311) B750311
theorem B500729 : Blo 330750 500729 := bstep (se 2 (by rfl) ⟨187773, by rfl⟩ : syracuseStep 500729 = 375547) B375547
theorem B6366221 : Blo 330750 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B2270267 : Blo 330750 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B501791 : Blo 330750 501791 := bstep (se 1 (by rfl) ⟨376343, by rfl⟩ : syracuseStep 501791 = 752687) B752687
theorem B534767 : Blo 330750 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B1256417 : Blo 330750 1256417 := bstep (se 2 (by rfl) ⟨471156, by rfl⟩ : syracuseStep 1256417 = 942313) B942313
theorem B15643103 : Blo 330750 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B11612969 : Blo 330750 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B2537405 : Blo 330750 2537405 := bstep (se 3 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 2537405 = 951527) B951527
theorem B1523873 : Blo 330750 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B1689335 : Blo 330750 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B673903 : Blo 330750 673903 := bstep (se 1 (by rfl) ⟨505427, by rfl⟩ : syracuseStep 673903 = 1010855) B1010855
theorem B4345811 : Blo 330750 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B1265939 : Blo 330750 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B1593863 : Blo 330750 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B34527059 : Blo 330750 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B842471 : Blo 330750 842471 := bstep (se 1 (by rfl) ⟨631853, by rfl⟩ : syracuseStep 842471 = 1263707) B1263707
theorem B5659955 : Blo 330750 5659955 := bstep (se 1 (by rfl) ⟨4244966, by rfl⟩ : syracuseStep 5659955 = 8489933) B8489933
theorem B744875 : Blo 330750 744875 := bstep (se 1 (by rfl) ⟨558656, by rfl⟩ : syracuseStep 744875 = 1117313) B1117313
theorem B2121511 : Blo 330750 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B843817 : Blo 330750 843817 := bstep (se 2 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 843817 = 632863) B632863
theorem B745775 : Blo 330750 745775 := bstep (se 1 (by rfl) ⟨559331, by rfl⟩ : syracuseStep 745775 = 1118663) B1118663
theorem B747611 : Blo 330750 747611 := bstep (se 1 (by rfl) ⟨560708, by rfl⟩ : syracuseStep 747611 = 1121417) B1121417
theorem B813439 : Blo 330750 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B5401343 : Blo 330750 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B748799 : Blo 330750 748799 := bstep (se 1 (by rfl) ⟨561599, by rfl⟩ : syracuseStep 748799 = 1123199) B1123199
theorem B6909887 : Blo 330750 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B5403293 : Blo 330750 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B13038347 : Blo 330750 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B1931039 : Blo 330750 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B751607 : Blo 330750 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B13694987 : Blo 330750 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B8059985 : Blo 330750 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B1015915 : Blo 330750 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B41714941 : Blo 330750 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B1084585 : Blo 330750 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B331419 : Blo 330750 331419 := bstep (se 1 (by rfl) ⟨248564, by rfl⟩ : syracuseStep 331419 = 497129) B497129
theorem B331823 : Blo 330750 331823 := bstep (se 1 (by rfl) ⟨248867, by rfl⟩ : syracuseStep 331823 = 497735) B497735
theorem B561647 : Blo 330750 561647 := bstep (se 1 (by rfl) ⟨421235, by rfl⟩ : syracuseStep 561647 = 842471) B842471
theorem B3773303 : Blo 330750 3773303 := bstep (se 1 (by rfl) ⟨2829977, by rfl⟩ : syracuseStep 3773303 = 5659955) B5659955
theorem B496583 : Blo 330750 496583 := bstep (se 1 (by rfl) ⟨372437, by rfl⟩ : syracuseStep 496583 = 744875) B744875
theorem B497183 : Blo 330750 497183 := bstep (se 1 (by rfl) ⟨372887, by rfl⟩ : syracuseStep 497183 = 745775) B745775
theorem B333471 : Blo 330750 333471 := bstep (se 1 (by rfl) ⟨250103, by rfl⟩ : syracuseStep 333471 = 500207) B500207
theorem B333819 : Blo 330750 333819 := bstep (se 1 (by rfl) ⟨250364, by rfl⟩ : syracuseStep 333819 = 500729) B500729
theorem B1513511 : Blo 330750 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B334527 : Blo 330750 334527 := bstep (se 1 (by rfl) ⟨250895, by rfl⟩ : syracuseStep 334527 = 501791) B501791
theorem B498407 : Blo 330750 498407 := bstep (se 1 (by rfl) ⟨373805, by rfl⟩ : syracuseStep 498407 = 747611) B747611
theorem B499199 : Blo 330750 499199 := bstep (se 1 (by rfl) ⟨374399, by rfl⟩ : syracuseStep 499199 = 748799) B748799
theorem B8692231 : Blo 330750 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B7741979 : Blo 330750 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B1287359 : Blo 330750 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B501071 : Blo 330750 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B2828681 : Blo 330750 2828681 := bstep (se 2 (by rfl) ⟨1060755, by rfl⟩ : syracuseStep 2828681 = 2121511) B2121511
theorem B18426365 : Blo 330750 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B1125089 : Blo 330750 1125089 := bstep (se 2 (by rfl) ⟨421908, by rfl⟩ : syracuseStep 1125089 = 843817) B843817
theorem B1126223 : Blo 330750 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B2897207 : Blo 330750 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B898537 : Blo 330750 898537 := bstep (se 2 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 898537 = 673903) B673903
theorem B1062575 : Blo 330750 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B23018039 : Blo 330750 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B1426045 : Blo 330750 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B4244147 : Blo 330750 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B1098617 : Blo 330750 1098617 := bstep (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) B823963
theorem B837611 : Blo 330750 837611 := bstep (se 1 (by rfl) ⟨628208, by rfl⟩ : syracuseStep 837611 = 1256417) B1256417
theorem B14403581 : Blo 330750 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B1691603 : Blo 330750 1691603 := bstep (se 1 (by rfl) ⟨1268702, by rfl⟩ : syracuseStep 1691603 = 2537405) B2537405
theorem B9129991 : Blo 330750 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B840233 : Blo 330750 840233 := bstep (se 2 (by rfl) ⟨315087, by rfl⟩ : syracuseStep 840233 = 630175) B630175
theorem B843959 : Blo 330750 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B745883 : Blo 330750 745883 := bstep (se 1 (by rfl) ⟨559412, by rfl⟩ : syracuseStep 745883 = 1118825) B1118825
theorem B1928377 : Blo 330750 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B4287977 : Blo 330750 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B749177 : Blo 330750 749177 := bstep (se 2 (by rfl) ⟨280941, by rfl⟩ : syracuseStep 749177 = 561883) B561883
theorem B749321 : Blo 330750 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B3602195 : Blo 330750 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B5373323 : Blo 330750 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B1901393 : Blo 330750 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B558407 : Blo 330750 558407 := bstep (se 1 (by rfl) ⟨418805, by rfl⟩ : syracuseStep 558407 = 837611) B837611
theorem B9602387 : Blo 330750 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B560155 : Blo 330750 560155 := bstep (se 1 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 560155 = 840233) B840233
theorem B331055 : Blo 330750 331055 := bstep (se 1 (by rfl) ⟨248291, by rfl⟩ : syracuseStep 331055 = 496583) B496583
theorem B331455 : Blo 330750 331455 := bstep (se 1 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 331455 = 497183) B497183
theorem B1446113 : Blo 330750 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B332271 : Blo 330750 332271 := bstep (se 1 (by rfl) ⟨249203, by rfl⟩ : syracuseStep 332271 = 498407) B498407
theorem B332799 : Blo 330750 332799 := bstep (se 1 (by rfl) ⟨249599, by rfl⟩ : syracuseStep 332799 = 499199) B499199
theorem B562639 : Blo 330750 562639 := bstep (se 1 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 562639 = 843959) B843959
theorem B497255 : Blo 330750 497255 := bstep (se 1 (by rfl) ⟨372941, by rfl⟩ : syracuseStep 497255 = 745883) B745883
theorem B858239 : Blo 330750 858239 := bstep (se 1 (by rfl) ⟨643679, by rfl⟩ : syracuseStep 858239 = 1287359) B1287359
theorem B334047 : Blo 330750 334047 := bstep (se 1 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 334047 = 501071) B501071
theorem B2858651 : Blo 330750 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B499451 : Blo 330750 499451 := bstep (se 1 (by rfl) ⟨374588, by rfl⟩ : syracuseStep 499451 = 749177) B749177
theorem B499547 : Blo 330750 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B2401463 : Blo 330750 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B15345359 : Blo 330750 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B3582215 : Blo 330750 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B1354553 : Blo 330750 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B2829431 : Blo 330750 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B55619921 : Blo 330750 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B2929645 : Blo 330750 2929645 := bstep (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) B1098617
theorem B1127735 : Blo 330750 1127735 := bstep (se 1 (by rfl) ⟨845801, by rfl⟩ : syracuseStep 1127735 = 1691603) B1691603
theorem B374431 : Blo 330750 374431 := bstep (se 1 (by rfl) ⟨280823, by rfl⟩ : syracuseStep 374431 = 561647) B561647
theorem B12173321 : Blo 330750 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B5161319 : Blo 330750 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B1885787 : Blo 330750 1885787 := bstep (se 1 (by rfl) ⟨1414340, by rfl⟩ : syracuseStep 1885787 = 2828681) B2828681
theorem B1198049 : Blo 330750 1198049 := bstep (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) B898537
theorem B708383 : Blo 330750 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B11589641 : Blo 330750 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B2515535 : Blo 330750 2515535 := bstep (se 1 (by rfl) ⟨1886651, by rfl⟩ : syracuseStep 2515535 = 3773303) B3773303
theorem B1009007 : Blo 330750 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B10284677 : Blo 330750 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B12284243 : Blo 330750 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B750059 : Blo 330750 750059 := bstep (se 1 (by rfl) ⟨562544, by rfl⟩ : syracuseStep 750059 = 1125089) B1125089
theorem B750815 : Blo 330750 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B1931471 : Blo 330750 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B3440879 : Blo 330750 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B331503 : Blo 330750 331503 := bstep (se 1 (by rfl) ⟨248627, by rfl⟩ : syracuseStep 331503 = 497255) B497255
theorem B1905767 : Blo 330750 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B332967 : Blo 330750 332967 := bstep (se 1 (by rfl) ⟨249725, by rfl⟩ : syracuseStep 332967 = 499451) B499451
theorem B333031 : Blo 330750 333031 := bstep (se 1 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 333031 = 499547) B499547
theorem B1677023 : Blo 330750 1677023 := bstep (se 1 (by rfl) ⟨1257767, by rfl⟩ : syracuseStep 1677023 = 2515535) B2515535
theorem B10230239 : Blo 330750 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B3906193 : Blo 330750 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B499241 : Blo 330750 499241 := bstep (se 2 (by rfl) ⟨187215, by rfl⟩ : syracuseStep 499241 = 374431) B374431
theorem B6856451 : Blo 330750 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B500039 : Blo 330750 500039 := bstep (se 1 (by rfl) ⟨375029, by rfl⟩ : syracuseStep 500039 = 750059) B750059
theorem B500543 : Blo 330750 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B1287647 : Blo 330750 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B372271 : Blo 330750 372271 := bstep (se 1 (by rfl) ⟨279203, by rfl⟩ : syracuseStep 372271 = 558407) B558407
theorem B6401591 : Blo 330750 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B1257191 : Blo 330750 1257191 := bstep (se 1 (by rfl) ⟨942893, by rfl⟩ : syracuseStep 1257191 = 1885787) B1885787
theorem B964075 : Blo 330750 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B572159 : Blo 330750 572159 := bstep (se 1 (by rfl) ⟨429119, by rfl⟩ : syracuseStep 572159 = 858239) B858239
theorem B3194797 : Blo 330750 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B672671 : Blo 330750 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B903035 : Blo 330750 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1886287 : Blo 330750 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B37079947 : Blo 330750 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B1889021 : Blo 330750 1889021 := bstep (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) B708383
theorem B8115547 : Blo 330750 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B1267595 : Blo 330750 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B7726427 : Blo 330750 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B746873 : Blo 330750 746873 := bstep (se 2 (by rfl) ⟨280077, by rfl⟩ : syracuseStep 746873 = 560155) B560155
theorem B1600975 : Blo 330750 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B2388143 : Blo 330750 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B750185 : Blo 330750 750185 := bstep (se 2 (by rfl) ⟨281319, by rfl⟩ : syracuseStep 750185 = 562639) B562639
theorem B8189495 : Blo 330750 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B751823 : Blo 330750 751823 := bstep (se 1 (by rfl) ⟨563867, by rfl⟩ : syracuseStep 751823 = 1127735) B1127735
theorem B2293919 : Blo 330750 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B1118015 : Blo 330750 1118015 := bstep (se 1 (by rfl) ⟨838511, by rfl⟩ : syracuseStep 1118015 = 1677023) B1677023
theorem B2134633 : Blo 330750 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B197759717 : Blo 330750 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B496361 : Blo 330750 496361 := bstep (se 2 (by rfl) ⟨186135, by rfl⟩ : syracuseStep 496361 = 372271) B372271
theorem B332827 : Blo 330750 332827 := bstep (se 1 (by rfl) ⟨249620, by rfl⟩ : syracuseStep 332827 = 499241) B499241
theorem B333359 : Blo 330750 333359 := bstep (se 1 (by rfl) ⟨250019, by rfl⟩ : syracuseStep 333359 = 500039) B500039
theorem B333695 : Blo 330750 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B5150951 : Blo 330750 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B497915 : Blo 330750 497915 := bstep (se 1 (by rfl) ⟨373436, by rfl⟩ : syracuseStep 497915 = 746873) B746873
theorem B858431 : Blo 330750 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B10820729 : Blo 330750 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B1285433 : Blo 330750 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B4267727 : Blo 330750 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B500123 : Blo 330750 500123 := bstep (se 1 (by rfl) ⟨375092, by rfl⟩ : syracuseStep 500123 = 750185) B750185
theorem B501215 : Blo 330750 501215 := bstep (se 1 (by rfl) ⟨375911, by rfl⟩ : syracuseStep 501215 = 751823) B751823
theorem B1259347 : Blo 330750 1259347 := bstep (se 1 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 1259347 = 1889021) B1889021
theorem B2408093 : Blo 330750 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B4570967 : Blo 330750 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B27280637 : Blo 330750 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B838127 : Blo 330750 838127 := bstep (se 1 (by rfl) ⟨628595, by rfl⟩ : syracuseStep 838127 = 1257191) B1257191
theorem B1592095 : Blo 330750 1592095 := bstep (se 1 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 1592095 = 2388143) B2388143
theorem B5459663 : Blo 330750 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B381439 : Blo 330750 381439 := bstep (se 1 (by rfl) ⟨286079, by rfl⟩ : syracuseStep 381439 = 572159) B572159
theorem B1793789 : Blo 330750 1793789 := bstep (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) B672671
theorem B2515049 : Blo 330750 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B1270511 : Blo 330750 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B845063 : Blo 330750 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B5208257 : Blo 330750 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B4259729 : Blo 330750 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B18187091 : Blo 330750 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B558751 : Blo 330750 558751 := bstep (se 1 (by rfl) ⟨419063, by rfl⟩ : syracuseStep 558751 = 838127) B838127
theorem B330907 : Blo 330750 330907 := bstep (se 1 (by rfl) ⟨248180, by rfl⟩ : syracuseStep 330907 = 496361) B496361
theorem B331943 : Blo 330750 331943 := bstep (se 1 (by rfl) ⟨248957, by rfl⟩ : syracuseStep 331943 = 497915) B497915
theorem B7213819 : Blo 330750 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B856955 : Blo 330750 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B1676699 : Blo 330750 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B333415 : Blo 330750 333415 := bstep (se 1 (by rfl) ⟨250061, by rfl⟩ : syracuseStep 333415 = 500123) B500123
theorem B563375 : Blo 330750 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B334143 : Blo 330750 334143 := bstep (se 1 (by rfl) ⟨250607, by rfl⟩ : syracuseStep 334143 = 501215) B501215
theorem B1679129 : Blo 330750 1679129 := bstep (se 2 (by rfl) ⟨629673, by rfl⟩ : syracuseStep 1679129 = 1259347) B1259347
theorem B14559101 : Blo 330750 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B131839811 : Blo 330750 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B1195859 : Blo 330750 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B508585 : Blo 330750 508585 := bstep (se 2 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 508585 = 381439) B381439
theorem B2839819 : Blo 330750 2839819 := bstep (se 1 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 2839819 = 4259729) B4259729
theorem B1529279 : Blo 330750 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B745343 : Blo 330750 745343 := bstep (se 1 (by rfl) ⟨559007, by rfl⟩ : syracuseStep 745343 = 1118015) B1118015
theorem B2122793 : Blo 330750 2122793 := bstep (se 2 (by rfl) ⟨796047, by rfl⟩ : syracuseStep 2122793 = 1592095) B1592095
theorem B3433967 : Blo 330750 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B2845151 : Blo 330750 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B847007 : Blo 330750 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B13888685 : Blo 330750 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B2846177 : Blo 330750 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B2289149 : Blo 330750 2289149 := bstep (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) B858431
theorem B1605395 : Blo 330750 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B3047311 : Blo 330750 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B12124727 : Blo 330750 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B1117799 : Blo 330750 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B1019519 : Blo 330750 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B1119419 : Blo 330750 1119419 := bstep (se 1 (by rfl) ⟨839564, by rfl⟩ : syracuseStep 1119419 = 1679129) B1679129
theorem B496895 : Blo 330750 496895 := bstep (se 1 (by rfl) ⟨372671, by rfl⟩ : syracuseStep 496895 = 745343) B745343
theorem B1415195 : Blo 330750 1415195 := bstep (se 1 (by rfl) ⟨1061396, by rfl⟩ : syracuseStep 1415195 = 2122793) B2122793
theorem B9706067 : Blo 330750 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B564671 : Blo 330750 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B87893207 : Blo 330750 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B797239 : Blo 330750 797239 := bstep (se 1 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 797239 = 1195859) B1195859
theorem B571303 : Blo 330750 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B375583 : Blo 330750 375583 := bstep (se 1 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 375583 = 563375) B563375
theorem B9618425 : Blo 330750 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B3786425 : Blo 330750 3786425 := bstep (se 2 (by rfl) ⟨1419909, by rfl⟩ : syracuseStep 3786425 = 2839819) B2839819
theorem B9259123 : Blo 330750 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B1526099 : Blo 330750 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B1070263 : Blo 330750 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B678113 : Blo 330750 678113 := bstep (se 2 (by rfl) ⟨254292, by rfl⟩ : syracuseStep 678113 = 508585) B508585
theorem B745001 : Blo 330750 745001 := bstep (se 2 (by rfl) ⟨279375, by rfl⟩ : syracuseStep 745001 = 558751) B558751
theorem B2289311 : Blo 330750 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B1896767 : Blo 330750 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B1897451 : Blo 330750 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B4063081 : Blo 330750 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B2524283 : Blo 330750 2524283 := bstep (se 1 (by rfl) ⟨1893212, by rfl⟩ : syracuseStep 2524283 = 3786425) B3786425
theorem B331263 : Blo 330750 331263 := bstep (se 1 (by rfl) ⟨248447, by rfl⟩ : syracuseStep 331263 = 496895) B496895
theorem B496667 : Blo 330750 496667 := bstep (se 1 (by rfl) ⟨372500, by rfl⟩ : syracuseStep 496667 = 745001) B745001
theorem B58595471 : Blo 330750 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B4069597 : Blo 330750 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B5708069 : Blo 330750 5708069 := bstep (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) B1070263
theorem B761737 : Blo 330750 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B500777 : Blo 330750 500777 := bstep (se 2 (by rfl) ⟨187791, by rfl⟩ : syracuseStep 500777 = 375583) B375583
theorem B5417441 : Blo 330750 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B1062985 : Blo 330750 1062985 := bstep (se 2 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 1062985 = 797239) B797239
theorem B6470711 : Blo 330750 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B376447 : Blo 330750 376447 := bstep (se 1 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 376447 = 564671) B564671
theorem B1526207 : Blo 330750 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B1264511 : Blo 330750 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B1264967 : Blo 330750 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B8083151 : Blo 330750 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B6412283 : Blo 330750 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B745199 : Blo 330750 745199 := bstep (se 1 (by rfl) ⟨558899, by rfl⟩ : syracuseStep 745199 = 1117799) B1117799
theorem B679679 : Blo 330750 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B12345497 : Blo 330750 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B746279 : Blo 330750 746279 := bstep (se 1 (by rfl) ⟨559709, by rfl⟩ : syracuseStep 746279 = 1119419) B1119419
theorem B943463 : Blo 330750 943463 := bstep (se 1 (by rfl) ⟨707597, by rfl⟩ : syracuseStep 943463 = 1415195) B1415195
theorem B452075 : Blo 330750 452075 := bstep (se 1 (by rfl) ⟨339056, by rfl⟩ : syracuseStep 452075 = 678113) B678113
theorem B331111 : Blo 330750 331111 := bstep (se 1 (by rfl) ⟨248333, by rfl⟩ : syracuseStep 331111 = 496667) B496667
theorem B39063647 : Blo 330750 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B3805379 : Blo 330750 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B496799 : Blo 330750 496799 := bstep (se 1 (by rfl) ⟨372599, by rfl⟩ : syracuseStep 496799 = 745199) B745199
theorem B8230331 : Blo 330750 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B497519 : Blo 330750 497519 := bstep (se 1 (by rfl) ⟨373139, by rfl⟩ : syracuseStep 497519 = 746279) B746279
theorem B333851 : Blo 330750 333851 := bstep (se 1 (by rfl) ⟨250388, by rfl⟩ : syracuseStep 333851 = 500777) B500777
theorem B628975 : Blo 330750 628975 := bstep (se 1 (by rfl) ⟨471731, by rfl⟩ : syracuseStep 628975 = 943463) B943463
theorem B4069885 : Blo 330750 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B3611627 : Blo 330750 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B1417313 : Blo 330750 1417313 := bstep (se 2 (by rfl) ⟨531492, by rfl⟩ : syracuseStep 1417313 = 1062985) B1062985
theorem B501929 : Blo 330750 501929 := bstep (se 2 (by rfl) ⟨188223, by rfl⟩ : syracuseStep 501929 = 376447) B376447
theorem B1682855 : Blo 330750 1682855 := bstep (se 1 (by rfl) ⟨1262141, by rfl⟩ : syracuseStep 1682855 = 2524283) B2524283
theorem B5388767 : Blo 330750 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B4274855 : Blo 330750 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B5426129 : Blo 330750 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B4313807 : Blo 330750 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B843007 : Blo 330750 843007 := bstep (se 1 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 843007 = 1264511) B1264511
theorem B843311 : Blo 330750 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B1205533 : Blo 330750 1205533 := bstep (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) B452075
theorem B453119 : Blo 330750 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B1015649 : Blo 330750 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B1607377 : Blo 330750 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B331199 : Blo 330750 331199 := bstep (se 1 (by rfl) ⟨248399, by rfl⟩ : syracuseStep 331199 = 496799) B496799
theorem B331679 : Blo 330750 331679 := bstep (se 1 (by rfl) ⟨248759, by rfl⟩ : syracuseStep 331679 = 497519) B497519
theorem B562207 : Blo 330750 562207 := bstep (se 1 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 562207 = 843311) B843311
theorem B334619 : Blo 330750 334619 := bstep (se 1 (by rfl) ⟨250964, by rfl⟩ : syracuseStep 334619 = 501929) B501929
theorem B1121903 : Blo 330750 1121903 := bstep (se 1 (by rfl) ⟨841427, by rfl⟩ : syracuseStep 1121903 = 1682855) B1682855
theorem B1124009 : Blo 330750 1124009 := bstep (se 2 (by rfl) ⟨421503, by rfl⟩ : syracuseStep 1124009 = 843007) B843007
theorem B3617419 : Blo 330750 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B2536919 : Blo 330750 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B5486887 : Blo 330750 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B2407751 : Blo 330750 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B4833269 : Blo 330750 4833269 := bstep (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) B453119
theorem B838633 : Blo 330750 838633 := bstep (se 2 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 838633 = 628975) B628975
theorem B5426513 : Blo 330750 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B3592511 : Blo 330750 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B677099 : Blo 330750 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B26042431 : Blo 330750 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B2875871 : Blo 330750 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B944875 : Blo 330750 944875 := bstep (se 1 (by rfl) ⟨708656, by rfl⟩ : syracuseStep 944875 = 1417313) B1417313
theorem B2849903 : Blo 330750 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B7668989 : Blo 330750 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B2395007 : Blo 330750 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B1805597 : Blo 330750 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B1118177 : Blo 330750 1118177 := bstep (se 2 (by rfl) ⟨419316, by rfl⟩ : syracuseStep 1118177 = 838633) B838633
theorem B4823225 : Blo 330750 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B7315849 : Blo 330750 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B3222179 : Blo 330750 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B3617675 : Blo 330750 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B2143169 : Blo 330750 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B1259833 : Blo 330750 1259833 := bstep (se 2 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 1259833 = 944875) B944875
theorem B1691279 : Blo 330750 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B34723241 : Blo 330750 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B747935 : Blo 330750 747935 := bstep (se 1 (by rfl) ⟨560951, by rfl⟩ : syracuseStep 747935 = 1121903) B1121903
theorem B749339 : Blo 330750 749339 := bstep (se 1 (by rfl) ⟨562004, by rfl⟩ : syracuseStep 749339 = 1124009) B1124009
theorem B749609 : Blo 330750 749609 := bstep (se 2 (by rfl) ⟨281103, by rfl⟩ : syracuseStep 749609 = 562207) B562207
theorem B1899935 : Blo 330750 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B1605167 : Blo 330750 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B5112659 : Blo 330750 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B3215483 : Blo 330750 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B498623 : Blo 330750 498623 := bstep (se 1 (by rfl) ⟨373967, by rfl⟩ : syracuseStep 498623 = 747935) B747935
theorem B499559 : Blo 330750 499559 := bstep (se 1 (by rfl) ⟨374669, by rfl⟩ : syracuseStep 499559 = 749339) B749339
theorem B499739 : Blo 330750 499739 := bstep (se 1 (by rfl) ⟨374804, by rfl⟩ : syracuseStep 499739 = 749609) B749609
theorem B1679777 : Blo 330750 1679777 := bstep (se 2 (by rfl) ⟨629916, by rfl⟩ : syracuseStep 1679777 = 1259833) B1259833
theorem B1127519 : Blo 330750 1127519 := bstep (se 1 (by rfl) ⟨845639, by rfl⟩ : syracuseStep 1127519 = 1691279) B1691279
theorem B23148827 : Blo 330750 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B2148119 : Blo 330750 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B2411783 : Blo 330750 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B1428779 : Blo 330750 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B1266623 : Blo 330750 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B1070111 : Blo 330750 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B9754465 : Blo 330750 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B1596671 : Blo 330750 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B1203731 : Blo 330750 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B745451 : Blo 330750 745451 := bstep (se 1 (by rfl) ⟨559088, by rfl⟩ : syracuseStep 745451 = 1118177) B1118177
theorem B1607855 : Blo 330750 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B952519 : Blo 330750 952519 := bstep (se 1 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 952519 = 1428779) B1428779
theorem B13633757 : Blo 330750 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B332415 : Blo 330750 332415 := bstep (se 1 (by rfl) ⟨249311, by rfl⟩ : syracuseStep 332415 = 498623) B498623
theorem B333039 : Blo 330750 333039 := bstep (se 1 (by rfl) ⟨249779, by rfl⟩ : syracuseStep 333039 = 499559) B499559
theorem B496967 : Blo 330750 496967 := bstep (se 1 (by rfl) ⟨372725, by rfl⟩ : syracuseStep 496967 = 745451) B745451
theorem B333159 : Blo 330750 333159 := bstep (se 1 (by rfl) ⟨249869, by rfl⟩ : syracuseStep 333159 = 499739) B499739
theorem B1119851 : Blo 330750 1119851 := bstep (se 1 (by rfl) ⟨839888, by rfl⟩ : syracuseStep 1119851 = 1679777) B1679777
theorem B2143655 : Blo 330750 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B1064447 : Blo 330750 1064447 := bstep (se 1 (by rfl) ⟨798335, by rfl⟩ : syracuseStep 1064447 = 1596671) B1596671
theorem B802487 : Blo 330750 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B1432079 : Blo 330750 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B844415 : Blo 330750 844415 := bstep (se 1 (by rfl) ⟨633311, by rfl⟩ : syracuseStep 844415 = 1266623) B1266623
theorem B713407 : Blo 330750 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B13005953 : Blo 330750 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B751679 : Blo 330750 751679 := bstep (se 1 (by rfl) ⟨563759, by rfl⟩ : syracuseStep 751679 = 1127519) B1127519
theorem B15432551 : Blo 330750 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B951209 : Blo 330750 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B331311 : Blo 330750 331311 := bstep (se 1 (by rfl) ⟨248483, by rfl⟩ : syracuseStep 331311 = 496967) B496967
theorem B954719 : Blo 330750 954719 := bstep (se 1 (by rfl) ⟨716039, by rfl⟩ : syracuseStep 954719 = 1432079) B1432079
theorem B562943 : Blo 330750 562943 := bstep (se 1 (by rfl) ⟨422207, by rfl⟩ : syracuseStep 562943 = 844415) B844415
theorem B501119 : Blo 330750 501119 := bstep (se 1 (by rfl) ⟨375839, by rfl⟩ : syracuseStep 501119 = 751679) B751679
theorem B2139965 : Blo 330750 2139965 := bstep (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) B802487
theorem B9089171 : Blo 330750 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B8670635 : Blo 330750 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B1429103 : Blo 330750 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B709631 : Blo 330750 709631 := bstep (se 1 (by rfl) ⟨532223, by rfl⟩ : syracuseStep 709631 = 1064447) B1064447
theorem B1270025 : Blo 330750 1270025 := bstep (se 2 (by rfl) ⟨476259, by rfl⟩ : syracuseStep 1270025 = 952519) B952519
theorem B746567 : Blo 330750 746567 := bstep (se 1 (by rfl) ⟨559925, by rfl⟩ : syracuseStep 746567 = 1119851) B1119851
theorem B4287613 : Blo 330750 4287613 := bstep (se 3 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 4287613 = 1607855) B1607855
theorem B10288367 : Blo 330750 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B952735 : Blo 330750 952735 := bstep (se 1 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 952735 = 1429103) B1429103
theorem B497711 : Blo 330750 497711 := bstep (se 1 (by rfl) ⟨373283, by rfl⟩ : syracuseStep 497711 = 746567) B746567
theorem B334079 : Blo 330750 334079 := bstep (se 1 (by rfl) ⟨250559, by rfl⟩ : syracuseStep 334079 = 501119) B501119
theorem B6858911 : Blo 330750 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B634139 : Blo 330750 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B5780423 : Blo 330750 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B636479 : Blo 330750 636479 := bstep (se 1 (by rfl) ⟨477359, by rfl⟩ : syracuseStep 636479 = 954719) B954719
theorem B473087 : Blo 330750 473087 := bstep (se 1 (by rfl) ⟨354815, by rfl⟩ : syracuseStep 473087 = 709631) B709631
theorem B375295 : Blo 330750 375295 := bstep (se 1 (by rfl) ⟨281471, by rfl⟩ : syracuseStep 375295 = 562943) B562943
theorem B5716817 : Blo 330750 5716817 := bstep (se 2 (by rfl) ⟨2143806, by rfl⟩ : syracuseStep 5716817 = 4287613) B4287613
theorem B1426643 : Blo 330750 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B846683 : Blo 330750 846683 := bstep (se 1 (by rfl) ⟨635012, by rfl⟩ : syracuseStep 846683 = 1270025) B1270025
theorem B6059447 : Blo 330750 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B951095 : Blo 330750 951095 := bstep (se 1 (by rfl) ⟨713321, by rfl⟩ : syracuseStep 951095 = 1426643) B1426643
theorem B331807 : Blo 330750 331807 := bstep (se 1 (by rfl) ⟨248855, by rfl⟩ : syracuseStep 331807 = 497711) B497711
theorem B6789109 : Blo 330750 6789109 := bstep (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) B636479
theorem B564455 : Blo 330750 564455 := bstep (se 1 (by rfl) ⟨423341, by rfl⟩ : syracuseStep 564455 = 846683) B846683
theorem B500393 : Blo 330750 500393 := bstep (se 2 (by rfl) ⟨187647, by rfl⟩ : syracuseStep 500393 = 375295) B375295
theorem B4039631 : Blo 330750 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B3811211 : Blo 330750 3811211 := bstep (se 1 (by rfl) ⟨2858408, by rfl⟩ : syracuseStep 3811211 = 5716817) B5716817
theorem B1261565 : Blo 330750 1261565 := bstep (se 3 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 1261565 = 473087) B473087
theorem B4572607 : Blo 330750 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B3853615 : Blo 330750 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B1270313 : Blo 330750 1270313 := bstep (se 2 (by rfl) ⟨476367, by rfl⟩ : syracuseStep 1270313 = 952735) B952735
theorem B422759 : Blo 330750 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B6096809 : Blo 330750 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B333595 : Blo 330750 333595 := bstep (se 1 (by rfl) ⟨250196, by rfl⟩ : syracuseStep 333595 = 500393) B500393
theorem B2693087 : Blo 330750 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B9052145 : Blo 330750 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B634063 : Blo 330750 634063 := bstep (se 1 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 634063 = 951095) B951095
theorem B1127357 : Blo 330750 1127357 := bstep (se 3 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 1127357 = 422759) B422759
theorem B376303 : Blo 330750 376303 := bstep (se 1 (by rfl) ⟨282227, by rfl⟩ : syracuseStep 376303 = 564455) B564455
theorem B2540807 : Blo 330750 2540807 := bstep (se 1 (by rfl) ⟨1905605, by rfl⟩ : syracuseStep 2540807 = 3811211) B3811211
theorem B841043 : Blo 330750 841043 := bstep (se 1 (by rfl) ⟨630782, by rfl⟩ : syracuseStep 841043 = 1261565) B1261565
theorem B5138153 : Blo 330750 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B846875 : Blo 330750 846875 := bstep (se 1 (by rfl) ⟨635156, by rfl⟩ : syracuseStep 846875 = 1270313) B1270313
theorem B560695 : Blo 330750 560695 := bstep (se 1 (by rfl) ⟨420521, by rfl⟩ : syracuseStep 560695 = 841043) B841043
theorem B16258157 : Blo 330750 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B6034763 : Blo 330750 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B564583 : Blo 330750 564583 := bstep (se 1 (by rfl) ⟨423437, by rfl⟩ : syracuseStep 564583 = 846875) B846875
theorem B501737 : Blo 330750 501737 := bstep (se 2 (by rfl) ⟨188151, by rfl⟩ : syracuseStep 501737 = 376303) B376303
theorem B3425435 : Blo 330750 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B1693871 : Blo 330750 1693871 := bstep (se 1 (by rfl) ⟨1270403, by rfl⟩ : syracuseStep 1693871 = 2540807) B2540807
theorem B1795391 : Blo 330750 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B845417 : Blo 330750 845417 := bstep (se 2 (by rfl) ⟨317031, by rfl⟩ : syracuseStep 845417 = 634063) B634063
theorem B751571 : Blo 330750 751571 := bstep (se 1 (by rfl) ⟨563678, by rfl⟩ : syracuseStep 751571 = 1127357) B1127357
theorem B563611 : Blo 330750 563611 := bstep (se 1 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 563611 = 845417) B845417
theorem B334491 : Blo 330750 334491 := bstep (se 1 (by rfl) ⟨250868, by rfl⟩ : syracuseStep 334491 = 501737) B501737
theorem B501047 : Blo 330750 501047 := bstep (se 1 (by rfl) ⟨375785, by rfl⟩ : syracuseStep 501047 = 751571) B751571
theorem B1129247 : Blo 330750 1129247 := bstep (se 1 (by rfl) ⟨846935, by rfl⟩ : syracuseStep 1129247 = 1693871) B1693871
theorem B1196927 : Blo 330750 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B2283623 : Blo 330750 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B10838771 : Blo 330750 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B4023175 : Blo 330750 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B747593 : Blo 330750 747593 := bstep (se 2 (by rfl) ⟨280347, by rfl⟩ : syracuseStep 747593 = 560695) B560695
theorem B752777 : Blo 330750 752777 := bstep (se 2 (by rfl) ⟨282291, by rfl⟩ : syracuseStep 752777 = 564583) B564583
theorem B334031 : Blo 330750 334031 := bstep (se 1 (by rfl) ⟨250523, by rfl⟩ : syracuseStep 334031 = 501047) B501047
theorem B498395 : Blo 330750 498395 := bstep (se 1 (by rfl) ⟨373796, by rfl⟩ : syracuseStep 498395 = 747593) B747593
theorem B501851 : Blo 330750 501851 := bstep (se 1 (by rfl) ⟨376388, by rfl⟩ : syracuseStep 501851 = 752777) B752777
theorem B797951 : Blo 330750 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B1522415 : Blo 330750 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B7225847 : Blo 330750 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B5364233 : Blo 330750 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B751481 : Blo 330750 751481 := bstep (se 2 (by rfl) ⟨281805, by rfl⟩ : syracuseStep 751481 = 563611) B563611
theorem B752831 : Blo 330750 752831 := bstep (se 1 (by rfl) ⟨564623, by rfl⟩ : syracuseStep 752831 = 1129247) B1129247
theorem B4817231 : Blo 330750 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B3576155 : Blo 330750 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B332263 : Blo 330750 332263 := bstep (se 1 (by rfl) ⟨249197, by rfl⟩ : syracuseStep 332263 = 498395) B498395
theorem B334567 : Blo 330750 334567 := bstep (se 1 (by rfl) ⟨250925, by rfl⟩ : syracuseStep 334567 = 501851) B501851
theorem B500987 : Blo 330750 500987 := bstep (se 1 (by rfl) ⟨375740, by rfl⟩ : syracuseStep 500987 = 751481) B751481
theorem B501887 : Blo 330750 501887 := bstep (se 1 (by rfl) ⟨376415, by rfl⟩ : syracuseStep 501887 = 752831) B752831
theorem B2127869 : Blo 330750 2127869 := bstep (se 3 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 2127869 = 797951) B797951
theorem B1014943 : Blo 330750 1014943 := bstep (se 1 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 1014943 = 1522415) B1522415
theorem B3211487 : Blo 330750 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B9536413 : Blo 330750 9536413 := bstep (se 3 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 9536413 = 3576155) B3576155
theorem B333991 : Blo 330750 333991 := bstep (se 1 (by rfl) ⟨250493, by rfl⟩ : syracuseStep 333991 = 500987) B500987
theorem B334591 : Blo 330750 334591 := bstep (se 1 (by rfl) ⟨250943, by rfl⟩ : syracuseStep 334591 = 501887) B501887
theorem B1418579 : Blo 330750 1418579 := bstep (se 1 (by rfl) ⟨1063934, by rfl⟩ : syracuseStep 1418579 = 2127869) B2127869
theorem B1353257 : Blo 330750 1353257 := bstep (se 2 (by rfl) ⟨507471, by rfl⟩ : syracuseStep 1353257 = 1014943) B1014943
theorem B12715217 : Blo 330750 12715217 := bstep (se 2 (by rfl) ⟨4768206, by rfl⟩ : syracuseStep 12715217 = 9536413) B9536413
theorem B2140991 : Blo 330750 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B902171 : Blo 330750 902171 := bstep (se 1 (by rfl) ⟨676628, by rfl⟩ : syracuseStep 902171 = 1353257) B1353257
theorem B945719 : Blo 330750 945719 := bstep (se 1 (by rfl) ⟨709289, by rfl⟩ : syracuseStep 945719 = 1418579) B1418579
theorem B630479 : Blo 330750 630479 := bstep (se 1 (by rfl) ⟨472859, by rfl⟩ : syracuseStep 630479 = 945719) B945719
theorem B601447 : Blo 330750 601447 := bstep (se 1 (by rfl) ⟨451085, by rfl⟩ : syracuseStep 601447 = 902171) B902171
theorem B1427327 : Blo 330750 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B8476811 : Blo 330750 8476811 := bstep (se 1 (by rfl) ⟨6357608, by rfl⟩ : syracuseStep 8476811 = 12715217) B12715217
theorem B951551 : Blo 330750 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B5651207 : Blo 330750 5651207 := bstep (se 1 (by rfl) ⟨4238405, by rfl⟩ : syracuseStep 5651207 = 8476811) B8476811
theorem B801929 : Blo 330750 801929 := bstep (se 2 (by rfl) ⟨300723, by rfl⟩ : syracuseStep 801929 = 601447) B601447
theorem B420319 : Blo 330750 420319 := bstep (se 1 (by rfl) ⟨315239, by rfl⟩ : syracuseStep 420319 = 630479) B630479
theorem B560425 : Blo 330750 560425 := bstep (se 2 (by rfl) ⟨210159, by rfl⟩ : syracuseStep 560425 = 420319) B420319
theorem B534619 : Blo 330750 534619 := bstep (se 1 (by rfl) ⟨400964, by rfl⟩ : syracuseStep 534619 = 801929) B801929
theorem B634367 : Blo 330750 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B3767471 : Blo 330750 3767471 := bstep (se 1 (by rfl) ⟨2825603, by rfl⟩ : syracuseStep 3767471 = 5651207) B5651207
theorem B2851301 : Blo 330750 2851301 := bstep (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) B534619
theorem B2511647 : Blo 330750 2511647 := bstep (se 1 (by rfl) ⟨1883735, by rfl⟩ : syracuseStep 2511647 = 3767471) B3767471
theorem B747233 : Blo 330750 747233 := bstep (se 2 (by rfl) ⟨280212, by rfl⟩ : syracuseStep 747233 = 560425) B560425
theorem B422911 : Blo 330750 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B1900867 : Blo 330750 1900867 := bstep (se 1 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 1900867 = 2851301) B2851301
theorem B1674431 : Blo 330750 1674431 := bstep (se 1 (by rfl) ⟨1255823, by rfl⟩ : syracuseStep 1674431 = 2511647) B2511647
theorem B498155 : Blo 330750 498155 := bstep (se 1 (by rfl) ⟨373616, by rfl⟩ : syracuseStep 498155 = 747233) B747233
theorem B563881 : Blo 330750 563881 := bstep (se 2 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 563881 = 422911) B422911
theorem B1116287 : Blo 330750 1116287 := bstep (se 1 (by rfl) ⟨837215, by rfl⟩ : syracuseStep 1116287 = 1674431) B1674431
theorem B332103 : Blo 330750 332103 := bstep (se 1 (by rfl) ⟨249077, by rfl⟩ : syracuseStep 332103 = 498155) B498155
theorem B2534489 : Blo 330750 2534489 := bstep (se 2 (by rfl) ⟨950433, by rfl⟩ : syracuseStep 2534489 = 1900867) B1900867
theorem B751841 : Blo 330750 751841 := bstep (se 2 (by rfl) ⟨281940, by rfl⟩ : syracuseStep 751841 = 563881) B563881
theorem B501227 : Blo 330750 501227 := bstep (se 1 (by rfl) ⟨375920, by rfl⟩ : syracuseStep 501227 = 751841) B751841
theorem B1689659 : Blo 330750 1689659 := bstep (se 1 (by rfl) ⟨1267244, by rfl⟩ : syracuseStep 1689659 = 2534489) B2534489
theorem B744191 : Blo 330750 744191 := bstep (se 1 (by rfl) ⟨558143, by rfl⟩ : syracuseStep 744191 = 1116287) B1116287
theorem B496127 : Blo 330750 496127 := bstep (se 1 (by rfl) ⟨372095, by rfl⟩ : syracuseStep 496127 = 744191) B744191
theorem B334151 : Blo 330750 334151 := bstep (se 1 (by rfl) ⟨250613, by rfl⟩ : syracuseStep 334151 = 501227) B501227
theorem B1126439 : Blo 330750 1126439 := bstep (se 1 (by rfl) ⟨844829, by rfl⟩ : syracuseStep 1126439 = 1689659) B1689659
theorem B330751 : Blo 330750 330751 := bstep (se 1 (by rfl) ⟨248063, by rfl⟩ : syracuseStep 330751 = 496127) B496127
theorem B750959 : Blo 330750 750959 := bstep (se 1 (by rfl) ⟨563219, by rfl⟩ : syracuseStep 750959 = 1126439) B1126439
theorem B500639 : Blo 330750 500639 := bstep (se 1 (by rfl) ⟨375479, by rfl⟩ : syracuseStep 500639 = 750959) B750959
theorem B333759 : Blo 330750 333759 := bstep (se 1 (by rfl) ⟨250319, by rfl⟩ : syracuseStep 333759 = 500639) B500639

theorem C0 (j : ℕ) (h1 : 82687 ≤ j) (h2 : j ≤ 83386) : Blo 330750 (4 * j + 3) := by
  interval_cases j
  · exact B330751
  · exact B330755
  · exact B330759
  · exact B330763
  · exact B330767
  · exact B330771
  · exact B330775
  · exact B330779
  · exact B330783
  · exact B330787
  · exact B330791
  · exact B330795
  · exact B330799
  · exact B330803
  · exact B330807
  · exact B330811
  · exact B330815
  · exact B330819
  · exact B330823
  · exact B330827
  · exact B330831
  · exact B330835
  · exact B330839
  · exact B330843
  · exact B330847
  · exact B330851
  · exact B330855
  · exact B330859
  · exact B330863
  · exact B330867
  · exact B330871
  · exact B330875
  · exact B330879
  · exact B330883
  · exact B330887
  · exact B330891
  · exact B330895
  · exact B330899
  · exact B330903
  · exact B330907
  · exact B330911
  · exact B330915
  · exact B330919
  · exact B330923
  · exact B330927
  · exact B330931
  · exact B330935
  · exact B330939
  · exact B330943
  · exact B330947
  · exact B330951
  · exact B330955
  · exact B330959
  · exact B330963
  · exact B330967
  · exact B330971
  · exact B330975
  · exact B330979
  · exact B330983
  · exact B330987
  · exact B330991
  · exact B330995
  · exact B330999
  · exact B331003
  · exact B331007
  · exact B331011
  · exact B331015
  · exact B331019
  · exact B331023
  · exact B331027
  · exact B331031
  · exact B331035
  · exact B331039
  · exact B331043
  · exact B331047
  · exact B331051
  · exact B331055
  · exact B331059
  · exact B331063
  · exact B331067
  · exact B331071
  · exact B331075
  · exact B331079
  · exact B331083
  · exact B331087
  · exact B331091
  · exact B331095
  · exact B331099
  · exact B331103
  · exact B331107
  · exact B331111
  · exact B331115
  · exact B331119
  · exact B331123
  · exact B331127
  · exact B331131
  · exact B331135
  · exact B331139
  · exact B331143
  · exact B331147
  · exact B331151
  · exact B331155
  · exact B331159
  · exact B331163
  · exact B331167
  · exact B331171
  · exact B331175
  · exact B331179
  · exact B331183
  · exact B331187
  · exact B331191
  · exact B331195
  · exact B331199
  · exact B331203
  · exact B331207
  · exact B331211
  · exact B331215
  · exact B331219
  · exact B331223
  · exact B331227
  · exact B331231
  · exact B331235
  · exact B331239
  · exact B331243
  · exact B331247
  · exact B331251
  · exact B331255
  · exact B331259
  · exact B331263
  · exact B331267
  · exact B331271
  · exact B331275
  · exact B331279
  · exact B331283
  · exact B331287
  · exact B331291
  · exact B331295
  · exact B331299
  · exact B331303
  · exact B331307
  · exact B331311
  · exact B331315
  · exact B331319
  · exact B331323
  · exact B331327
  · exact B331331
  · exact B331335
  · exact B331339
  · exact B331343
  · exact B331347
  · exact B331351
  · exact B331355
  · exact B331359
  · exact B331363
  · exact B331367
  · exact B331371
  · exact B331375
  · exact B331379
  · exact B331383
  · exact B331387
  · exact B331391
  · exact B331395
  · exact B331399
  · exact B331403
  · exact B331407
  · exact B331411
  · exact B331415
  · exact B331419
  · exact B331423
  · exact B331427
  · exact B331431
  · exact B331435
  · exact B331439
  · exact B331443
  · exact B331447
  · exact B331451
  · exact B331455
  · exact B331459
  · exact B331463
  · exact B331467
  · exact B331471
  · exact B331475
  · exact B331479
  · exact B331483
  · exact B331487
  · exact B331491
  · exact B331495
  · exact B331499
  · exact B331503
  · exact B331507
  · exact B331511
  · exact B331515
  · exact B331519
  · exact B331523
  · exact B331527
  · exact B331531
  · exact B331535
  · exact B331539
  · exact B331543
  · exact B331547
  · exact B331551
  · exact B331555
  · exact B331559
  · exact B331563
  · exact B331567
  · exact B331571
  · exact B331575
  · exact B331579
  · exact B331583
  · exact B331587
  · exact B331591
  · exact B331595
  · exact B331599
  · exact B331603
  · exact B331607
  · exact B331611
  · exact B331615
  · exact B331619
  · exact B331623
  · exact B331627
  · exact B331631
  · exact B331635
  · exact B331639
  · exact B331643
  · exact B331647
  · exact B331651
  · exact B331655
  · exact B331659
  · exact B331663
  · exact B331667
  · exact B331671
  · exact B331675
  · exact B331679
  · exact B331683
  · exact B331687
  · exact B331691
  · exact B331695
  · exact B331699
  · exact B331703
  · exact B331707
  · exact B331711
  · exact B331715
  · exact B331719
  · exact B331723
  · exact B331727
  · exact B331731
  · exact B331735
  · exact B331739
  · exact B331743
  · exact B331747
  · exact B331751
  · exact B331755
  · exact B331759
  · exact B331763
  · exact B331767
  · exact B331771
  · exact B331775
  · exact B331779
  · exact B331783
  · exact B331787
  · exact B331791
  · exact B331795
  · exact B331799
  · exact B331803
  · exact B331807
  · exact B331811
  · exact B331815
  · exact B331819
  · exact B331823
  · exact B331827
  · exact B331831
  · exact B331835
  · exact B331839
  · exact B331843
  · exact B331847
  · exact B331851
  · exact B331855
  · exact B331859
  · exact B331863
  · exact B331867
  · exact B331871
  · exact B331875
  · exact B331879
  · exact B331883
  · exact B331887
  · exact B331891
  · exact B331895
  · exact B331899
  · exact B331903
  · exact B331907
  · exact B331911
  · exact B331915
  · exact B331919
  · exact B331923
  · exact B331927
  · exact B331931
  · exact B331935
  · exact B331939
  · exact B331943
  · exact B331947
  · exact B331951
  · exact B331955
  · exact B331959
  · exact B331963
  · exact B331967
  · exact B331971
  · exact B331975
  · exact B331979
  · exact B331983
  · exact B331987
  · exact B331991
  · exact B331995
  · exact B331999
  · exact B332003
  · exact B332007
  · exact B332011
  · exact B332015
  · exact B332019
  · exact B332023
  · exact B332027
  · exact B332031
  · exact B332035
  · exact B332039
  · exact B332043
  · exact B332047
  · exact B332051
  · exact B332055
  · exact B332059
  · exact B332063
  · exact B332067
  · exact B332071
  · exact B332075
  · exact B332079
  · exact B332083
  · exact B332087
  · exact B332091
  · exact B332095
  · exact B332099
  · exact B332103
  · exact B332107
  · exact B332111
  · exact B332115
  · exact B332119
  · exact B332123
  · exact B332127
  · exact B332131
  · exact B332135
  · exact B332139
  · exact B332143
  · exact B332147
  · exact B332151
  · exact B332155
  · exact B332159
  · exact B332163
  · exact B332167
  · exact B332171
  · exact B332175
  · exact B332179
  · exact B332183
  · exact B332187
  · exact B332191
  · exact B332195
  · exact B332199
  · exact B332203
  · exact B332207
  · exact B332211
  · exact B332215
  · exact B332219
  · exact B332223
  · exact B332227
  · exact B332231
  · exact B332235
  · exact B332239
  · exact B332243
  · exact B332247
  · exact B332251
  · exact B332255
  · exact B332259
  · exact B332263
  · exact B332267
  · exact B332271
  · exact B332275
  · exact B332279
  · exact B332283
  · exact B332287
  · exact B332291
  · exact B332295
  · exact B332299
  · exact B332303
  · exact B332307
  · exact B332311
  · exact B332315
  · exact B332319
  · exact B332323
  · exact B332327
  · exact B332331
  · exact B332335
  · exact B332339
  · exact B332343
  · exact B332347
  · exact B332351
  · exact B332355
  · exact B332359
  · exact B332363
  · exact B332367
  · exact B332371
  · exact B332375
  · exact B332379
  · exact B332383
  · exact B332387
  · exact B332391
  · exact B332395
  · exact B332399
  · exact B332403
  · exact B332407
  · exact B332411
  · exact B332415
  · exact B332419
  · exact B332423
  · exact B332427
  · exact B332431
  · exact B332435
  · exact B332439
  · exact B332443
  · exact B332447
  · exact B332451
  · exact B332455
  · exact B332459
  · exact B332463
  · exact B332467
  · exact B332471
  · exact B332475
  · exact B332479
  · exact B332483
  · exact B332487
  · exact B332491
  · exact B332495
  · exact B332499
  · exact B332503
  · exact B332507
  · exact B332511
  · exact B332515
  · exact B332519
  · exact B332523
  · exact B332527
  · exact B332531
  · exact B332535
  · exact B332539
  · exact B332543
  · exact B332547
  · exact B332551
  · exact B332555
  · exact B332559
  · exact B332563
  · exact B332567
  · exact B332571
  · exact B332575
  · exact B332579
  · exact B332583
  · exact B332587
  · exact B332591
  · exact B332595
  · exact B332599
  · exact B332603
  · exact B332607
  · exact B332611
  · exact B332615
  · exact B332619
  · exact B332623
  · exact B332627
  · exact B332631
  · exact B332635
  · exact B332639
  · exact B332643
  · exact B332647
  · exact B332651
  · exact B332655
  · exact B332659
  · exact B332663
  · exact B332667
  · exact B332671
  · exact B332675
  · exact B332679
  · exact B332683
  · exact B332687
  · exact B332691
  · exact B332695
  · exact B332699
  · exact B332703
  · exact B332707
  · exact B332711
  · exact B332715
  · exact B332719
  · exact B332723
  · exact B332727
  · exact B332731
  · exact B332735
  · exact B332739
  · exact B332743
  · exact B332747
  · exact B332751
  · exact B332755
  · exact B332759
  · exact B332763
  · exact B332767
  · exact B332771
  · exact B332775
  · exact B332779
  · exact B332783
  · exact B332787
  · exact B332791
  · exact B332795
  · exact B332799
  · exact B332803
  · exact B332807
  · exact B332811
  · exact B332815
  · exact B332819
  · exact B332823
  · exact B332827
  · exact B332831
  · exact B332835
  · exact B332839
  · exact B332843
  · exact B332847
  · exact B332851
  · exact B332855
  · exact B332859
  · exact B332863
  · exact B332867
  · exact B332871
  · exact B332875
  · exact B332879
  · exact B332883
  · exact B332887
  · exact B332891
  · exact B332895
  · exact B332899
  · exact B332903
  · exact B332907
  · exact B332911
  · exact B332915
  · exact B332919
  · exact B332923
  · exact B332927
  · exact B332931
  · exact B332935
  · exact B332939
  · exact B332943
  · exact B332947
  · exact B332951
  · exact B332955
  · exact B332959
  · exact B332963
  · exact B332967
  · exact B332971
  · exact B332975
  · exact B332979
  · exact B332983
  · exact B332987
  · exact B332991
  · exact B332995
  · exact B332999
  · exact B333003
  · exact B333007
  · exact B333011
  · exact B333015
  · exact B333019
  · exact B333023
  · exact B333027
  · exact B333031
  · exact B333035
  · exact B333039
  · exact B333043
  · exact B333047
  · exact B333051
  · exact B333055
  · exact B333059
  · exact B333063
  · exact B333067
  · exact B333071
  · exact B333075
  · exact B333079
  · exact B333083
  · exact B333087
  · exact B333091
  · exact B333095
  · exact B333099
  · exact B333103
  · exact B333107
  · exact B333111
  · exact B333115
  · exact B333119
  · exact B333123
  · exact B333127
  · exact B333131
  · exact B333135
  · exact B333139
  · exact B333143
  · exact B333147
  · exact B333151
  · exact B333155
  · exact B333159
  · exact B333163
  · exact B333167
  · exact B333171
  · exact B333175
  · exact B333179
  · exact B333183
  · exact B333187
  · exact B333191
  · exact B333195
  · exact B333199
  · exact B333203
  · exact B333207
  · exact B333211
  · exact B333215
  · exact B333219
  · exact B333223
  · exact B333227
  · exact B333231
  · exact B333235
  · exact B333239
  · exact B333243
  · exact B333247
  · exact B333251
  · exact B333255
  · exact B333259
  · exact B333263
  · exact B333267
  · exact B333271
  · exact B333275
  · exact B333279
  · exact B333283
  · exact B333287
  · exact B333291
  · exact B333295
  · exact B333299
  · exact B333303
  · exact B333307
  · exact B333311
  · exact B333315
  · exact B333319
  · exact B333323
  · exact B333327
  · exact B333331
  · exact B333335
  · exact B333339
  · exact B333343
  · exact B333347
  · exact B333351
  · exact B333355
  · exact B333359
  · exact B333363
  · exact B333367
  · exact B333371
  · exact B333375
  · exact B333379
  · exact B333383
  · exact B333387
  · exact B333391
  · exact B333395
  · exact B333399
  · exact B333403
  · exact B333407
  · exact B333411
  · exact B333415
  · exact B333419
  · exact B333423
  · exact B333427
  · exact B333431
  · exact B333435
  · exact B333439
  · exact B333443
  · exact B333447
  · exact B333451
  · exact B333455
  · exact B333459
  · exact B333463
  · exact B333467
  · exact B333471
  · exact B333475
  · exact B333479
  · exact B333483
  · exact B333487
  · exact B333491
  · exact B333495
  · exact B333499
  · exact B333503
  · exact B333507
  · exact B333511
  · exact B333515
  · exact B333519
  · exact B333523
  · exact B333527
  · exact B333531
  · exact B333535
  · exact B333539
  · exact B333543
  · exact B333547

theorem C1 (j : ℕ) (h1 : 83387 ≤ j) (h2 : j ≤ 83686) : Blo 330750 (4 * j + 3) := by
  interval_cases j
  · exact B333551
  · exact B333555
  · exact B333559
  · exact B333563
  · exact B333567
  · exact B333571
  · exact B333575
  · exact B333579
  · exact B333583
  · exact B333587
  · exact B333591
  · exact B333595
  · exact B333599
  · exact B333603
  · exact B333607
  · exact B333611
  · exact B333615
  · exact B333619
  · exact B333623
  · exact B333627
  · exact B333631
  · exact B333635
  · exact B333639
  · exact B333643
  · exact B333647
  · exact B333651
  · exact B333655
  · exact B333659
  · exact B333663
  · exact B333667
  · exact B333671
  · exact B333675
  · exact B333679
  · exact B333683
  · exact B333687
  · exact B333691
  · exact B333695
  · exact B333699
  · exact B333703
  · exact B333707
  · exact B333711
  · exact B333715
  · exact B333719
  · exact B333723
  · exact B333727
  · exact B333731
  · exact B333735
  · exact B333739
  · exact B333743
  · exact B333747
  · exact B333751
  · exact B333755
  · exact B333759
  · exact B333763
  · exact B333767
  · exact B333771
  · exact B333775
  · exact B333779
  · exact B333783
  · exact B333787
  · exact B333791
  · exact B333795
  · exact B333799
  · exact B333803
  · exact B333807
  · exact B333811
  · exact B333815
  · exact B333819
  · exact B333823
  · exact B333827
  · exact B333831
  · exact B333835
  · exact B333839
  · exact B333843
  · exact B333847
  · exact B333851
  · exact B333855
  · exact B333859
  · exact B333863
  · exact B333867
  · exact B333871
  · exact B333875
  · exact B333879
  · exact B333883
  · exact B333887
  · exact B333891
  · exact B333895
  · exact B333899
  · exact B333903
  · exact B333907
  · exact B333911
  · exact B333915
  · exact B333919
  · exact B333923
  · exact B333927
  · exact B333931
  · exact B333935
  · exact B333939
  · exact B333943
  · exact B333947
  · exact B333951
  · exact B333955
  · exact B333959
  · exact B333963
  · exact B333967
  · exact B333971
  · exact B333975
  · exact B333979
  · exact B333983
  · exact B333987
  · exact B333991
  · exact B333995
  · exact B333999
  · exact B334003
  · exact B334007
  · exact B334011
  · exact B334015
  · exact B334019
  · exact B334023
  · exact B334027
  · exact B334031
  · exact B334035
  · exact B334039
  · exact B334043
  · exact B334047
  · exact B334051
  · exact B334055
  · exact B334059
  · exact B334063
  · exact B334067
  · exact B334071
  · exact B334075
  · exact B334079
  · exact B334083
  · exact B334087
  · exact B334091
  · exact B334095
  · exact B334099
  · exact B334103
  · exact B334107
  · exact B334111
  · exact B334115
  · exact B334119
  · exact B334123
  · exact B334127
  · exact B334131
  · exact B334135
  · exact B334139
  · exact B334143
  · exact B334147
  · exact B334151
  · exact B334155
  · exact B334159
  · exact B334163
  · exact B334167
  · exact B334171
  · exact B334175
  · exact B334179
  · exact B334183
  · exact B334187
  · exact B334191
  · exact B334195
  · exact B334199
  · exact B334203
  · exact B334207
  · exact B334211
  · exact B334215
  · exact B334219
  · exact B334223
  · exact B334227
  · exact B334231
  · exact B334235
  · exact B334239
  · exact B334243
  · exact B334247
  · exact B334251
  · exact B334255
  · exact B334259
  · exact B334263
  · exact B334267
  · exact B334271
  · exact B334275
  · exact B334279
  · exact B334283
  · exact B334287
  · exact B334291
  · exact B334295
  · exact B334299
  · exact B334303
  · exact B334307
  · exact B334311
  · exact B334315
  · exact B334319
  · exact B334323
  · exact B334327
  · exact B334331
  · exact B334335
  · exact B334339
  · exact B334343
  · exact B334347
  · exact B334351
  · exact B334355
  · exact B334359
  · exact B334363
  · exact B334367
  · exact B334371
  · exact B334375
  · exact B334379
  · exact B334383
  · exact B334387
  · exact B334391
  · exact B334395
  · exact B334399
  · exact B334403
  · exact B334407
  · exact B334411
  · exact B334415
  · exact B334419
  · exact B334423
  · exact B334427
  · exact B334431
  · exact B334435
  · exact B334439
  · exact B334443
  · exact B334447
  · exact B334451
  · exact B334455
  · exact B334459
  · exact B334463
  · exact B334467
  · exact B334471
  · exact B334475
  · exact B334479
  · exact B334483
  · exact B334487
  · exact B334491
  · exact B334495
  · exact B334499
  · exact B334503
  · exact B334507
  · exact B334511
  · exact B334515
  · exact B334519
  · exact B334523
  · exact B334527
  · exact B334531
  · exact B334535
  · exact B334539
  · exact B334543
  · exact B334547
  · exact B334551
  · exact B334555
  · exact B334559
  · exact B334563
  · exact B334567
  · exact B334571
  · exact B334575
  · exact B334579
  · exact B334583
  · exact B334587
  · exact B334591
  · exact B334595
  · exact B334599
  · exact B334603
  · exact B334607
  · exact B334611
  · exact B334615
  · exact B334619
  · exact B334623
  · exact B334627
  · exact B334631
  · exact B334635
  · exact B334639
  · exact B334643
  · exact B334647
  · exact B334651
  · exact B334655
  · exact B334659
  · exact B334663
  · exact B334667
  · exact B334671
  · exact B334675
  · exact B334679
  · exact B334683
  · exact B334687
  · exact B334691
  · exact B334695
  · exact B334699
  · exact B334703
  · exact B334707
  · exact B334711
  · exact B334715
  · exact B334719
  · exact B334723
  · exact B334727
  · exact B334731
  · exact B334735
  · exact B334739
  · exact B334743
  · exact B334747

theorem solution (m : ℕ) (hlo : 330750 ≤ m) (hhi : m ≤ 334750) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 82687 ≤ j := by omega
    have hj2 : j ≤ 83686 := by omega
    have hb : Blo 330750 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 83387 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
