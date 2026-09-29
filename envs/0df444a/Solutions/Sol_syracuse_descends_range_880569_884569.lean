-- Prove2me | solution 1 for syracuse_descends_range_880569_884569
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:44.819508+00:00
-- url     : https://prove2.me/submissions/d66eb3e8-0c55-4f5c-943c-36e0c85971ba

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


theorem B1343557 : Blo 880569 1343557 := bbase (se 4 (by rfl) ⟨125958, by rfl⟩ : syracuseStep 1343557 = 251917) (by norm_num)
theorem B2982149 : Blo 880569 2982149 := bbase (se 4 (by rfl) ⟨279576, by rfl⟩ : syracuseStep 2982149 = 559153) (by norm_num)
theorem B1114489 : Blo 880569 1114489 := bbase (se 2 (by rfl) ⟨417933, by rfl⟩ : syracuseStep 1114489 = 835867) (by norm_num)
theorem B1114661 : Blo 880569 1114661 := bbase (se 4 (by rfl) ⟨104499, by rfl⟩ : syracuseStep 1114661 = 208999) (by norm_num)
theorem B3768869 : Blo 880569 3768869 := bbase (se 4 (by rfl) ⟨353331, by rfl⟩ : syracuseStep 3768869 = 706663) (by norm_num)
theorem B1671749 : Blo 880569 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B1114717 : Blo 880569 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B2982581 : Blo 880569 2982581 := bbase (se 5 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 2982581 = 279617) (by norm_num)
theorem B1114813 : Blo 880569 1114813 := bbase (se 3 (by rfl) ⟨209027, by rfl⟩ : syracuseStep 1114813 = 418055) (by norm_num)
theorem B3572437 : Blo 880569 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B2229029 : Blo 880569 2229029 := bbase (se 4 (by rfl) ⟨208971, by rfl⟩ : syracuseStep 2229029 = 417943) (by norm_num)
theorem B1114985 : Blo 880569 1114985 := bbase (se 2 (by rfl) ⟨418119, by rfl⟩ : syracuseStep 1114985 = 836239) (by norm_num)
theorem B1115041 : Blo 880569 1115041 := bbase (se 2 (by rfl) ⟨418140, by rfl⟩ : syracuseStep 1115041 = 836281) (by norm_num)
theorem B3015589 : Blo 880569 3015589 := bbase (se 4 (by rfl) ⟨282711, by rfl⟩ : syracuseStep 3015589 = 565423) (by norm_num)
theorem B2229221 : Blo 880569 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B1115137 : Blo 880569 1115137 := bbase (se 2 (by rfl) ⟨418176, by rfl⟩ : syracuseStep 1115137 = 836353) (by norm_num)
theorem B8487989 : Blo 880569 8487989 := bbase (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) (by norm_num)
theorem B2688085 : Blo 880569 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B2983013 : Blo 880569 2983013 := bbase (se 4 (by rfl) ⟨279657, by rfl⟩ : syracuseStep 2983013 = 559315) (by norm_num)
theorem B1115309 : Blo 880569 1115309 := bbase (se 3 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 1115309 = 418241) (by norm_num)
theorem B3343589 : Blo 880569 3343589 := bbase (se 4 (by rfl) ⟨313461, by rfl⟩ : syracuseStep 3343589 = 626923) (by norm_num)
theorem B1115365 : Blo 880569 1115365 := bbase (se 4 (by rfl) ⟨104565, by rfl⟩ : syracuseStep 1115365 = 209131) (by norm_num)
theorem B1672501 : Blo 880569 1672501 := bbase (se 5 (by rfl) ⟨78398, by rfl⟩ : syracuseStep 1672501 = 156797) (by norm_num)
theorem B2229565 : Blo 880569 2229565 := bbase (se 3 (by rfl) ⟨418043, by rfl⟩ : syracuseStep 2229565 = 836087) (by norm_num)
theorem B1115461 : Blo 880569 1115461 := bbase (se 4 (by rfl) ⟨104574, by rfl⟩ : syracuseStep 1115461 = 209149) (by norm_num)
theorem B2229677 : Blo 880569 2229677 := bbase (se 3 (by rfl) ⟨418064, by rfl⟩ : syracuseStep 2229677 = 836129) (by norm_num)
theorem B1672645 : Blo 880569 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B1050085 : Blo 880569 1050085 := bbase (se 4 (by rfl) ⟨98445, by rfl⟩ : syracuseStep 1050085 = 196891) (by norm_num)
theorem B1115633 : Blo 880569 1115633 := bbase (se 2 (by rfl) ⟨418362, by rfl⟩ : syracuseStep 1115633 = 836725) (by norm_num)
theorem B2983445 : Blo 880569 2983445 := bbase (se 6 (by rfl) ⟨69924, by rfl⟩ : syracuseStep 2983445 = 139849) (by norm_num)
theorem B1115689 : Blo 880569 1115689 := bbase (se 2 (by rfl) ⟨418383, by rfl⟩ : syracuseStep 1115689 = 836767) (by norm_num)
theorem B1672805 : Blo 880569 1672805 := bbase (se 4 (by rfl) ⟨156825, by rfl⟩ : syracuseStep 1672805 = 313651) (by norm_num)
theorem B2229869 : Blo 880569 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B1115785 : Blo 880569 1115785 := bbase (se 2 (by rfl) ⟨418419, by rfl⟩ : syracuseStep 1115785 = 836839) (by norm_num)
theorem B2623205 : Blo 880569 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B1672949 : Blo 880569 1672949 := bbase (se 5 (by rfl) ⟨78419, by rfl⟩ : syracuseStep 1672949 = 156839) (by norm_num)
theorem B7538453 : Blo 880569 7538453 := bbase (se 6 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 7538453 = 353365) (by norm_num)
theorem B1115957 : Blo 880569 1115957 := bbase (se 5 (by rfl) ⟨52310, by rfl⟩ : syracuseStep 1115957 = 104621) (by norm_num)
theorem B1116013 : Blo 880569 1116013 := bbase (se 3 (by rfl) ⟨209252, by rfl⟩ : syracuseStep 1116013 = 418505) (by norm_num)
theorem B1410949 : Blo 880569 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B2230213 : Blo 880569 2230213 := bbase (se 4 (by rfl) ⟨209082, by rfl⟩ : syracuseStep 2230213 = 418165) (by norm_num)
theorem B2983877 : Blo 880569 2983877 := bbase (se 4 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 2983877 = 559477) (by norm_num)
theorem B1116109 : Blo 880569 1116109 := bbase (se 3 (by rfl) ⟨209270, by rfl⟩ : syracuseStep 1116109 = 418541) (by norm_num)
theorem B1673237 : Blo 880569 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B1509421 : Blo 880569 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B2230325 : Blo 880569 2230325 := bbase (se 5 (by rfl) ⟨104546, by rfl⟩ : syracuseStep 2230325 = 209093) (by norm_num)
theorem B1116281 : Blo 880569 1116281 := bbase (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) (by norm_num)
theorem B1673389 : Blo 880569 1673389 := bbase (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) (by norm_num)
theorem B1116337 : Blo 880569 1116337 := bbase (se 2 (by rfl) ⟨418626, by rfl⟩ : syracuseStep 1116337 = 837253) (by norm_num)
theorem B9537749 : Blo 880569 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B4458725 : Blo 880569 4458725 := bbase (se 4 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 4458725 = 836011) (by norm_num)
theorem B2689253 : Blo 880569 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B2230517 : Blo 880569 2230517 := bbase (se 5 (by rfl) ⟨104555, by rfl⟩ : syracuseStep 2230517 = 209111) (by norm_num)
theorem B1116433 : Blo 880569 1116433 := bbase (se 2 (by rfl) ⟨418662, by rfl⟩ : syracuseStep 1116433 = 837325) (by norm_num)
theorem B1018217 : Blo 880569 1018217 := bbase (se 2 (by rfl) ⟨381831, by rfl⟩ : syracuseStep 1018217 = 763663) (by norm_num)
theorem B2984309 : Blo 880569 2984309 := bbase (se 5 (by rfl) ⟨139889, by rfl⟩ : syracuseStep 2984309 = 279779) (by norm_num)
theorem B3344773 : Blo 880569 3344773 := bbase (se 4 (by rfl) ⟨313572, by rfl⟩ : syracuseStep 3344773 = 627145) (by norm_num)
theorem B8063381 : Blo 880569 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B1116605 : Blo 880569 1116605 := bbase (se 3 (by rfl) ⟨209363, by rfl⟩ : syracuseStep 1116605 = 418727) (by norm_num)
theorem B1673693 : Blo 880569 1673693 := bbase (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) (by norm_num)
theorem B1116661 : Blo 880569 1116661 := bbase (se 5 (by rfl) ⟨52343, by rfl⟩ : syracuseStep 1116661 = 104687) (by norm_num)
theorem B920089 : Blo 880569 920089 := bbase (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) (by norm_num)
theorem B2230861 : Blo 880569 2230861 := bbase (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) (by norm_num)
theorem B1116757 : Blo 880569 1116757 := bbase (se 8 (by rfl) ⟨6543, by rfl⟩ : syracuseStep 1116757 = 13087) (by norm_num)
theorem B3345077 : Blo 880569 3345077 := bbase (se 5 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 3345077 = 313601) (by norm_num)
theorem B2230973 : Blo 880569 2230973 := bbase (se 3 (by rfl) ⟨418307, by rfl⟩ : syracuseStep 2230973 = 836615) (by norm_num)
theorem B1116929 : Blo 880569 1116929 := bbase (se 2 (by rfl) ⟨418848, by rfl⟩ : syracuseStep 1116929 = 837697) (by norm_num)
theorem B2984741 : Blo 880569 2984741 := bbase (se 4 (by rfl) ⟨279819, by rfl⟩ : syracuseStep 2984741 = 559639) (by norm_num)
theorem B1116985 : Blo 880569 1116985 := bbase (se 2 (by rfl) ⟨418869, by rfl⟩ : syracuseStep 1116985 = 837739) (by norm_num)
theorem B2231165 : Blo 880569 2231165 := bbase (se 3 (by rfl) ⟨418343, by rfl⟩ : syracuseStep 2231165 = 836687) (by norm_num)
theorem B1117081 : Blo 880569 1117081 := bbase (se 2 (by rfl) ⟨418905, by rfl⟩ : syracuseStep 1117081 = 837811) (by norm_num)
theorem B1117253 : Blo 880569 1117253 := bbase (se 4 (by rfl) ⟨104742, by rfl⟩ : syracuseStep 1117253 = 209485) (by norm_num)
theorem B1510517 : Blo 880569 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B1117309 : Blo 880569 1117309 := bbase (se 3 (by rfl) ⟨209495, by rfl⟩ : syracuseStep 1117309 = 418991) (by norm_num)
theorem B1674445 : Blo 880569 1674445 := bbase (se 3 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 1674445 = 627917) (by norm_num)
theorem B2821333 : Blo 880569 2821333 := bbase (se 7 (by rfl) ⟨33062, by rfl⟩ : syracuseStep 2821333 = 66125) (by norm_num)
theorem B2231509 : Blo 880569 2231509 := bbase (se 7 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 2231509 = 52301) (by norm_num)
theorem B2985173 : Blo 880569 2985173 := bbase (se 7 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 2985173 = 69965) (by norm_num)
theorem B1117405 : Blo 880569 1117405 := bbase (se 3 (by rfl) ⟨209513, by rfl⟩ : syracuseStep 1117405 = 419027) (by norm_num)
theorem B1412333 : Blo 880569 1412333 := bbase (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) (by norm_num)
theorem B2231621 : Blo 880569 2231621 := bbase (se 4 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 2231621 = 418429) (by norm_num)
theorem B1674589 : Blo 880569 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B1117577 : Blo 880569 1117577 := bbase (se 2 (by rfl) ⟨419091, by rfl⟩ : syracuseStep 1117577 = 838183) (by norm_num)
theorem B1412525 : Blo 880569 1412525 := bbase (se 3 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 1412525 = 529697) (by norm_num)
theorem B1117633 : Blo 880569 1117633 := bbase (se 2 (by rfl) ⟨419112, by rfl⟩ : syracuseStep 1117633 = 838225) (by norm_num)
theorem B4460021 : Blo 880569 4460021 := bbase (se 5 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 4460021 = 418127) (by norm_num)
theorem B1674749 : Blo 880569 1674749 := bbase (se 3 (by rfl) ⟨314015, by rfl⟩ : syracuseStep 1674749 = 628031) (by norm_num)
theorem B2231813 : Blo 880569 2231813 := bbase (se 4 (by rfl) ⟨209232, by rfl⟩ : syracuseStep 2231813 = 418465) (by norm_num)
theorem B1117729 : Blo 880569 1117729 := bbase (se 2 (by rfl) ⟨419148, by rfl⟩ : syracuseStep 1117729 = 838297) (by norm_num)
theorem B1674893 : Blo 880569 1674893 := bbase (se 3 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 1674893 = 628085) (by norm_num)
theorem B1117901 : Blo 880569 1117901 := bbase (se 3 (by rfl) ⟨209606, by rfl⟩ : syracuseStep 1117901 = 419213) (by norm_num)
theorem B12095189 : Blo 880569 12095189 := bbase (se 7 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 12095189 = 283481) (by norm_num)
theorem B954109 : Blo 880569 954109 := bbase (se 3 (by rfl) ⟨178895, by rfl⟩ : syracuseStep 954109 = 357791) (by norm_num)
theorem B3772165 : Blo 880569 3772165 := bbase (se 4 (by rfl) ⟨353640, by rfl⟩ : syracuseStep 3772165 = 707281) (by norm_num)
theorem B1117957 : Blo 880569 1117957 := bbase (se 4 (by rfl) ⟨104808, by rfl⟩ : syracuseStep 1117957 = 209617) (by norm_num)
theorem B1511173 : Blo 880569 1511173 := bbase (se 4 (by rfl) ⟨141672, by rfl⟩ : syracuseStep 1511173 = 283345) (by norm_num)
theorem B1511221 : Blo 880569 1511221 := bbase (se 5 (by rfl) ⟨70838, by rfl⟩ : syracuseStep 1511221 = 141677) (by norm_num)
theorem B954185 : Blo 880569 954185 := bbase (se 2 (by rfl) ⟨357819, by rfl⟩ : syracuseStep 954185 = 715639) (by norm_num)
theorem B2232157 : Blo 880569 2232157 := bbase (se 3 (by rfl) ⟨418529, by rfl⟩ : syracuseStep 2232157 = 837059) (by norm_num)
theorem B1118053 : Blo 880569 1118053 := bbase (se 4 (by rfl) ⟨104817, by rfl⟩ : syracuseStep 1118053 = 209635) (by norm_num)
theorem B1675181 : Blo 880569 1675181 := bbase (se 3 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 1675181 = 628193) (by norm_num)
theorem B2232269 : Blo 880569 2232269 := bbase (se 3 (by rfl) ⟨418550, by rfl⟩ : syracuseStep 2232269 = 837101) (by norm_num)
theorem B1118225 : Blo 880569 1118225 := bbase (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) (by norm_num)
theorem B1675333 : Blo 880569 1675333 := bbase (se 4 (by rfl) ⟨157062, by rfl⟩ : syracuseStep 1675333 = 314125) (by norm_num)
theorem B1118281 : Blo 880569 1118281 := bbase (se 2 (by rfl) ⟨419355, by rfl⟩ : syracuseStep 1118281 = 838711) (by norm_num)
theorem B2232461 : Blo 880569 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B1118377 : Blo 880569 1118377 := bbase (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) (by norm_num)
theorem B2265365 : Blo 880569 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B1118549 : Blo 880569 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B1675637 : Blo 880569 1675637 := bbase (se 5 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 1675637 = 157091) (by norm_num)
theorem B1118605 : Blo 880569 1118605 := bbase (se 3 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 1118605 = 419477) (by norm_num)
theorem B2232805 : Blo 880569 2232805 := bbase (se 4 (by rfl) ⟨209325, by rfl⟩ : syracuseStep 2232805 = 418651) (by norm_num)
theorem B1118701 : Blo 880569 1118701 := bbase (se 3 (by rfl) ⟨209756, by rfl⟩ : syracuseStep 1118701 = 419513) (by norm_num)
theorem B2232917 : Blo 880569 2232917 := bbase (se 8 (by rfl) ⟨13083, by rfl⟩ : syracuseStep 2232917 = 26167) (by norm_num)
theorem B1118873 : Blo 880569 1118873 := bbase (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) (by norm_num)
theorem B1118929 : Blo 880569 1118929 := bbase (se 2 (by rfl) ⟨419598, by rfl⟩ : syracuseStep 1118929 = 839197) (by norm_num)
theorem B1413845 : Blo 880569 1413845 := bbase (se 7 (by rfl) ⟨16568, by rfl⟩ : syracuseStep 1413845 = 33137) (by norm_num)
theorem B3347189 : Blo 880569 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B4461317 : Blo 880569 4461317 := bbase (se 4 (by rfl) ⟨418248, by rfl⟩ : syracuseStep 4461317 = 836497) (by norm_num)
theorem B2233109 : Blo 880569 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B1119025 : Blo 880569 1119025 := bbase (se 2 (by rfl) ⟨419634, by rfl⟩ : syracuseStep 1119025 = 839269) (by norm_num)
theorem B1413941 : Blo 880569 1413941 := bbase (se 5 (by rfl) ⟨66278, by rfl⟩ : syracuseStep 1413941 = 132557) (by norm_num)
theorem B1413973 : Blo 880569 1413973 := bbase (se 9 (by rfl) ⟨4142, by rfl⟩ : syracuseStep 1413973 = 8285) (by norm_num)
theorem B3019717 : Blo 880569 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B2266061 : Blo 880569 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B1119197 : Blo 880569 1119197 := bbase (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) (by norm_num)
theorem B3347477 : Blo 880569 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B1119253 : Blo 880569 1119253 := bbase (se 6 (by rfl) ⟨26232, by rfl⟩ : syracuseStep 1119253 = 52465) (by norm_num)
theorem B1676389 : Blo 880569 1676389 := bbase (se 4 (by rfl) ⟨157161, by rfl⟩ : syracuseStep 1676389 = 314323) (by norm_num)
theorem B2233453 : Blo 880569 2233453 := bbase (se 3 (by rfl) ⟨418772, by rfl⟩ : syracuseStep 2233453 = 837545) (by norm_num)
theorem B1119349 : Blo 880569 1119349 := bbase (se 5 (by rfl) ⟨52469, by rfl⟩ : syracuseStep 1119349 = 104939) (by norm_num)
theorem B2233565 : Blo 880569 2233565 := bbase (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) (by norm_num)
theorem B1676533 : Blo 880569 1676533 := bbase (se 5 (by rfl) ⟨78587, by rfl⟩ : syracuseStep 1676533 = 157175) (by norm_num)
theorem B1119521 : Blo 880569 1119521 := bbase (se 2 (by rfl) ⟨419820, by rfl⟩ : syracuseStep 1119521 = 839641) (by norm_num)
theorem B5019029 : Blo 880569 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B1676693 : Blo 880569 1676693 := bbase (se 6 (by rfl) ⟨39297, by rfl⟩ : syracuseStep 1676693 = 78595) (by norm_num)
theorem B2233757 : Blo 880569 2233757 := bbase (se 3 (by rfl) ⟨418829, by rfl⟩ : syracuseStep 2233757 = 837659) (by norm_num)
theorem B1676837 : Blo 880569 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B1021489 : Blo 880569 1021489 := bbase (se 2 (by rfl) ⟨383058, by rfl⟩ : syracuseStep 1021489 = 766117) (by norm_num)
theorem B2234101 : Blo 880569 2234101 := bbase (se 5 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 2234101 = 209447) (by norm_num)
theorem B1677125 : Blo 880569 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B2234213 : Blo 880569 2234213 := bbase (se 4 (by rfl) ⟨209457, by rfl⟩ : syracuseStep 2234213 = 418915) (by norm_num)
theorem B1677277 : Blo 880569 1677277 := bbase (se 3 (by rfl) ⟨314489, by rfl⟩ : syracuseStep 1677277 = 628979) (by norm_num)
theorem B4462613 : Blo 880569 4462613 := bbase (se 6 (by rfl) ⟨104592, by rfl⟩ : syracuseStep 4462613 = 209185) (by norm_num)
theorem B2234405 : Blo 880569 2234405 := bbase (se 4 (by rfl) ⟨209475, by rfl⟩ : syracuseStep 2234405 = 418951) (by norm_num)
theorem B1022081 : Blo 880569 1022081 := bbase (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) (by norm_num)
theorem B3348661 : Blo 880569 3348661 := bbase (se 5 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 3348661 = 313937) (by norm_num)
theorem B1677581 : Blo 880569 1677581 := bbase (se 3 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 1677581 = 629093) (by norm_num)
theorem B956705 : Blo 880569 956705 := bbase (se 2 (by rfl) ⟨358764, by rfl⟩ : syracuseStep 956705 = 717529) (by norm_num)
theorem B1415485 : Blo 880569 1415485 := bbase (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) (by norm_num)
theorem B2234749 : Blo 880569 2234749 := bbase (se 3 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 2234749 = 838031) (by norm_num)
theorem B3578309 : Blo 880569 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B3348965 : Blo 880569 3348965 := bbase (se 4 (by rfl) ⟨313965, by rfl⟩ : syracuseStep 3348965 = 627931) (by norm_num)
theorem B2234861 : Blo 880569 2234861 := bbase (se 3 (by rfl) ⟨419036, by rfl⟩ : syracuseStep 2234861 = 838073) (by norm_num)
theorem B3185189 : Blo 880569 3185189 := bbase (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) (by norm_num)
theorem B4233845 : Blo 880569 4233845 := bbase (se 5 (by rfl) ⟨198461, by rfl⟩ : syracuseStep 4233845 = 396923) (by norm_num)
theorem B2235053 : Blo 880569 2235053 := bbase (se 3 (by rfl) ⟨419072, by rfl⟩ : syracuseStep 2235053 = 838145) (by norm_num)
theorem B3775157 : Blo 880569 3775157 := bbase (se 5 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 3775157 = 353921) (by norm_num)
theorem B3021637 : Blo 880569 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B6691733 : Blo 880569 6691733 := bbase (se 6 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 6691733 = 313675) (by norm_num)
theorem B3218357 : Blo 880569 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1678333 : Blo 880569 1678333 := bbase (se 3 (by rfl) ⟨314687, by rfl⟩ : syracuseStep 1678333 = 629375) (by norm_num)
theorem B2235397 : Blo 880569 2235397 := bbase (se 4 (by rfl) ⟨209568, by rfl⟩ : syracuseStep 2235397 = 419137) (by norm_num)
theorem B1416197 : Blo 880569 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B2235509 : Blo 880569 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B1678477 : Blo 880569 1678477 := bbase (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) (by norm_num)
theorem B2268341 : Blo 880569 2268341 := bbase (se 5 (by rfl) ⟨106328, by rfl⟩ : syracuseStep 2268341 = 212657) (by norm_num)
theorem B4463909 : Blo 880569 4463909 := bbase (se 4 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 4463909 = 836983) (by norm_num)
theorem B1678637 : Blo 880569 1678637 := bbase (se 3 (by rfl) ⟨314744, by rfl⟩ : syracuseStep 1678637 = 629489) (by norm_num)
theorem B2235701 : Blo 880569 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B1678781 : Blo 880569 1678781 := bbase (se 3 (by rfl) ⟨314771, by rfl⟩ : syracuseStep 1678781 = 629543) (by norm_num)
theorem B990661 : Blo 880569 990661 := bbase (se 4 (by rfl) ⟨92874, by rfl⟩ : syracuseStep 990661 = 185749) (by norm_num)
theorem B990697 : Blo 880569 990697 := bbase (se 2 (by rfl) ⟨371511, by rfl⟩ : syracuseStep 990697 = 743023) (by norm_num)
theorem B990733 : Blo 880569 990733 := bbase (se 3 (by rfl) ⟨185762, by rfl⟩ : syracuseStep 990733 = 371525) (by norm_num)
theorem B990769 : Blo 880569 990769 := bbase (se 2 (by rfl) ⟨371538, by rfl⟩ : syracuseStep 990769 = 743077) (by norm_num)
theorem B990805 : Blo 880569 990805 := bbase (se 8 (by rfl) ⟨5805, by rfl⟩ : syracuseStep 990805 = 11611) (by norm_num)
theorem B990841 : Blo 880569 990841 := bbase (se 2 (by rfl) ⟨371565, by rfl⟩ : syracuseStep 990841 = 743131) (by norm_num)
theorem B2236045 : Blo 880569 2236045 := bbase (se 3 (by rfl) ⟨419258, by rfl⟩ : syracuseStep 2236045 = 838517) (by norm_num)
theorem B14294677 : Blo 880569 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B990877 : Blo 880569 990877 := bbase (se 3 (by rfl) ⟨185789, by rfl⟩ : syracuseStep 990877 = 371579) (by norm_num)
theorem B3776165 : Blo 880569 3776165 := bbase (se 4 (by rfl) ⟨354015, by rfl⟩ : syracuseStep 3776165 = 708031) (by norm_num)
theorem B3186341 : Blo 880569 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B1416869 : Blo 880569 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B990913 : Blo 880569 990913 := bbase (se 2 (by rfl) ⟨371592, by rfl⟩ : syracuseStep 990913 = 743185) (by norm_num)
theorem B1679069 : Blo 880569 1679069 := bbase (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) (by norm_num)
theorem B990949 : Blo 880569 990949 := bbase (se 4 (by rfl) ⟨92901, by rfl⟩ : syracuseStep 990949 = 185803) (by norm_num)
theorem B2236157 : Blo 880569 2236157 := bbase (se 3 (by rfl) ⟨419279, by rfl⟩ : syracuseStep 2236157 = 838559) (by norm_num)
theorem B990985 : Blo 880569 990985 := bbase (se 2 (by rfl) ⟨371619, by rfl⟩ : syracuseStep 990985 = 743239) (by norm_num)
theorem B991021 : Blo 880569 991021 := bbase (se 3 (by rfl) ⟨185816, by rfl⟩ : syracuseStep 991021 = 371633) (by norm_num)
theorem B892729 : Blo 880569 892729 := bbase (se 2 (by rfl) ⟨334773, by rfl⟩ : syracuseStep 892729 = 669547) (by norm_num)
theorem B991057 : Blo 880569 991057 := bbase (se 2 (by rfl) ⟨371646, by rfl⟩ : syracuseStep 991057 = 743293) (by norm_num)
theorem B991093 : Blo 880569 991093 := bbase (se 5 (by rfl) ⟨46457, by rfl⟩ : syracuseStep 991093 = 92915) (by norm_num)
theorem B1679221 : Blo 880569 1679221 := bbase (se 5 (by rfl) ⟨78713, by rfl⟩ : syracuseStep 1679221 = 157427) (by norm_num)
theorem B991129 : Blo 880569 991129 := bbase (se 2 (by rfl) ⟨371673, by rfl⟩ : syracuseStep 991129 = 743347) (by norm_num)
theorem B991165 : Blo 880569 991165 := bbase (se 3 (by rfl) ⟨185843, by rfl⟩ : syracuseStep 991165 = 371687) (by norm_num)
theorem B2236349 : Blo 880569 2236349 := bbase (se 3 (by rfl) ⟨419315, by rfl⟩ : syracuseStep 2236349 = 838631) (by norm_num)
theorem B991201 : Blo 880569 991201 := bbase (se 2 (by rfl) ⟨371700, by rfl⟩ : syracuseStep 991201 = 743401) (by norm_num)
theorem B991237 : Blo 880569 991237 := bbase (se 4 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 991237 = 185857) (by norm_num)
theorem B991273 : Blo 880569 991273 := bbase (se 2 (by rfl) ⟨371727, by rfl⟩ : syracuseStep 991273 = 743455) (by norm_num)
theorem B991309 : Blo 880569 991309 := bbase (se 3 (by rfl) ⟨185870, by rfl⟩ : syracuseStep 991309 = 371741) (by norm_num)
theorem B991345 : Blo 880569 991345 := bbase (se 2 (by rfl) ⟨371754, by rfl⟩ : syracuseStep 991345 = 743509) (by norm_num)
theorem B991381 : Blo 880569 991381 := bbase (se 6 (by rfl) ⟨23235, by rfl⟩ : syracuseStep 991381 = 46471) (by norm_num)
theorem B991417 : Blo 880569 991417 := bbase (se 2 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 991417 = 743563) (by norm_num)
theorem B10035413 : Blo 880569 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B30613717 : Blo 880569 30613717 := bbase (se 7 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 30613717 = 717509) (by norm_num)
theorem B991453 : Blo 880569 991453 := bbase (se 3 (by rfl) ⟨185897, by rfl⟩ : syracuseStep 991453 = 371795) (by norm_num)
theorem B2826485 : Blo 880569 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B991489 : Blo 880569 991489 := bbase (se 2 (by rfl) ⟨371808, by rfl⟩ : syracuseStep 991489 = 743617) (by norm_num)
theorem B5644565 : Blo 880569 5644565 := bbase (se 6 (by rfl) ⟨132294, by rfl⟩ : syracuseStep 5644565 = 264589) (by norm_num)
theorem B2236693 : Blo 880569 2236693 := bbase (se 6 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 2236693 = 104845) (by norm_num)
theorem B991525 : Blo 880569 991525 := bbase (se 4 (by rfl) ⟨92955, by rfl⟩ : syracuseStep 991525 = 185911) (by norm_num)
theorem B1909045 : Blo 880569 1909045 := bbase (se 5 (by rfl) ⟨89486, by rfl⟩ : syracuseStep 1909045 = 178973) (by norm_num)
theorem B991561 : Blo 880569 991561 := bbase (se 2 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 991561 = 743671) (by norm_num)
theorem B991597 : Blo 880569 991597 := bbase (se 3 (by rfl) ⟨185924, by rfl⟩ : syracuseStep 991597 = 371849) (by norm_num)
theorem B6037877 : Blo 880569 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B2236805 : Blo 880569 2236805 := bbase (se 4 (by rfl) ⟨209700, by rfl⟩ : syracuseStep 2236805 = 419401) (by norm_num)
theorem B991633 : Blo 880569 991633 := bbase (se 2 (by rfl) ⟨371862, by rfl⟩ : syracuseStep 991633 = 743725) (by norm_num)
theorem B991669 : Blo 880569 991669 := bbase (se 5 (by rfl) ⟨46484, by rfl⟩ : syracuseStep 991669 = 92969) (by norm_num)
theorem B991705 : Blo 880569 991705 := bbase (se 2 (by rfl) ⟨371889, by rfl⟩ : syracuseStep 991705 = 743779) (by norm_num)
theorem B991741 : Blo 880569 991741 := bbase (se 3 (by rfl) ⟨185951, by rfl⟩ : syracuseStep 991741 = 371903) (by norm_num)
theorem B991777 : Blo 880569 991777 := bbase (se 2 (by rfl) ⟨371916, by rfl⟩ : syracuseStep 991777 = 743833) (by norm_num)
theorem B3351077 : Blo 880569 3351077 := bbase (se 4 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 3351077 = 628327) (by norm_num)
theorem B4465205 : Blo 880569 4465205 := bbase (se 5 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 4465205 = 418613) (by norm_num)
theorem B3875381 : Blo 880569 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B991813 : Blo 880569 991813 := bbase (se 4 (by rfl) ⟨92982, by rfl⟩ : syracuseStep 991813 = 185965) (by norm_num)
theorem B2236997 : Blo 880569 2236997 := bbase (se 4 (by rfl) ⟨209718, by rfl⟩ : syracuseStep 2236997 = 419437) (by norm_num)
theorem B991849 : Blo 880569 991849 := bbase (se 2 (by rfl) ⟨371943, by rfl⟩ : syracuseStep 991849 = 743887) (by norm_num)
theorem B991885 : Blo 880569 991885 := bbase (se 3 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 991885 = 371957) (by norm_num)
theorem B991921 : Blo 880569 991921 := bbase (se 2 (by rfl) ⟨371970, by rfl⟩ : syracuseStep 991921 = 743941) (by norm_num)
theorem B991957 : Blo 880569 991957 := bbase (se 7 (by rfl) ⟨11624, by rfl⟩ : syracuseStep 991957 = 23249) (by norm_num)
theorem B1614557 : Blo 880569 1614557 := bbase (se 3 (by rfl) ⟨302729, by rfl⟩ : syracuseStep 1614557 = 605459) (by norm_num)
theorem B3023605 : Blo 880569 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B991993 : Blo 880569 991993 := bbase (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) (by norm_num)
theorem B992029 : Blo 880569 992029 := bbase (se 3 (by rfl) ⟨186005, by rfl⟩ : syracuseStep 992029 = 372011) (by norm_num)
theorem B992065 : Blo 880569 992065 := bbase (se 2 (by rfl) ⟨372024, by rfl⟩ : syracuseStep 992065 = 744049) (by norm_num)
theorem B3351365 : Blo 880569 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B992101 : Blo 880569 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B992137 : Blo 880569 992137 := bbase (se 2 (by rfl) ⟨372051, by rfl⟩ : syracuseStep 992137 = 744103) (by norm_num)
theorem B2237341 : Blo 880569 2237341 := bbase (se 3 (by rfl) ⟨419501, by rfl⟩ : syracuseStep 2237341 = 839003) (by norm_num)
theorem B992173 : Blo 880569 992173 := bbase (se 3 (by rfl) ⟨186032, by rfl⟩ : syracuseStep 992173 = 372065) (by norm_num)
theorem B992209 : Blo 880569 992209 := bbase (se 2 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 992209 = 744157) (by norm_num)
theorem B893921 : Blo 880569 893921 := bbase (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) (by norm_num)
theorem B992245 : Blo 880569 992245 := bbase (se 5 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 992245 = 93023) (by norm_num)
theorem B893953 : Blo 880569 893953 := bbase (se 2 (by rfl) ⟨335232, by rfl⟩ : syracuseStep 893953 = 670465) (by norm_num)
theorem B2237453 : Blo 880569 2237453 := bbase (se 3 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 2237453 = 839045) (by norm_num)
theorem B992281 : Blo 880569 992281 := bbase (se 2 (by rfl) ⟨372105, by rfl⟩ : syracuseStep 992281 = 744211) (by norm_num)
theorem B992317 : Blo 880569 992317 := bbase (se 3 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 992317 = 372119) (by norm_num)
theorem B992353 : Blo 880569 992353 := bbase (se 2 (by rfl) ⟨372132, by rfl⟩ : syracuseStep 992353 = 744265) (by norm_num)
theorem B2827381 : Blo 880569 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B992389 : Blo 880569 992389 := bbase (se 4 (by rfl) ⟨93036, by rfl⟩ : syracuseStep 992389 = 186073) (by norm_num)
theorem B1254541 : Blo 880569 1254541 := bbase (se 3 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 1254541 = 470453) (by norm_num)
theorem B992425 : Blo 880569 992425 := bbase (se 2 (by rfl) ⟨372159, by rfl⟩ : syracuseStep 992425 = 744319) (by norm_num)
theorem B992461 : Blo 880569 992461 := bbase (se 3 (by rfl) ⟨186086, by rfl⟩ : syracuseStep 992461 = 372173) (by norm_num)
theorem B2237645 : Blo 880569 2237645 := bbase (se 3 (by rfl) ⟨419558, by rfl⟩ : syracuseStep 2237645 = 839117) (by norm_num)
theorem B992497 : Blo 880569 992497 := bbase (se 2 (by rfl) ⟨372186, by rfl⟩ : syracuseStep 992497 = 744373) (by norm_num)
theorem B992533 : Blo 880569 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B894245 : Blo 880569 894245 := bbase (se 4 (by rfl) ⟨83835, by rfl⟩ : syracuseStep 894245 = 167671) (by norm_num)
theorem B992569 : Blo 880569 992569 := bbase (se 2 (by rfl) ⟨372213, by rfl⟩ : syracuseStep 992569 = 744427) (by norm_num)
theorem B992605 : Blo 880569 992605 := bbase (se 3 (by rfl) ⟨186113, by rfl⟩ : syracuseStep 992605 = 372227) (by norm_num)
theorem B992641 : Blo 880569 992641 := bbase (se 2 (by rfl) ⟨372240, by rfl⟩ : syracuseStep 992641 = 744481) (by norm_num)
theorem B4760981 : Blo 880569 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B3777941 : Blo 880569 3777941 := bbase (se 6 (by rfl) ⟨88545, by rfl⟩ : syracuseStep 3777941 = 177091) (by norm_num)
theorem B992677 : Blo 880569 992677 := bbase (se 4 (by rfl) ⟨93063, by rfl⟩ : syracuseStep 992677 = 186127) (by norm_num)
theorem B992713 : Blo 880569 992713 := bbase (se 2 (by rfl) ⟨372267, by rfl⟩ : syracuseStep 992713 = 744535) (by norm_num)
theorem B1058269 : Blo 880569 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B992749 : Blo 880569 992749 := bbase (se 3 (by rfl) ⟨186140, by rfl⟩ : syracuseStep 992749 = 372281) (by norm_num)
theorem B2827781 : Blo 880569 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B992785 : Blo 880569 992785 := bbase (se 2 (by rfl) ⟨372294, by rfl⟩ : syracuseStep 992785 = 744589) (by norm_num)
theorem B2237989 : Blo 880569 2237989 := bbase (se 4 (by rfl) ⟨209811, by rfl⟩ : syracuseStep 2237989 = 419623) (by norm_num)
theorem B992821 : Blo 880569 992821 := bbase (se 5 (by rfl) ⟨46538, by rfl⟩ : syracuseStep 992821 = 93077) (by norm_num)
theorem B992857 : Blo 880569 992857 := bbase (se 2 (by rfl) ⟨372321, by rfl⟩ : syracuseStep 992857 = 744643) (by norm_num)
theorem B992893 : Blo 880569 992893 := bbase (se 3 (by rfl) ⟨186167, by rfl⟩ : syracuseStep 992893 = 372335) (by norm_num)
theorem B7546517 : Blo 880569 7546517 := bbase (se 6 (by rfl) ⟨176871, by rfl⟩ : syracuseStep 7546517 = 353743) (by norm_num)
theorem B2238101 : Blo 880569 2238101 := bbase (se 6 (by rfl) ⟨52455, by rfl⟩ : syracuseStep 2238101 = 104911) (by norm_num)
theorem B992929 : Blo 880569 992929 := bbase (se 2 (by rfl) ⟨372348, by rfl⟩ : syracuseStep 992929 = 744697) (by norm_num)
theorem B992965 : Blo 880569 992965 := bbase (se 4 (by rfl) ⟨93090, by rfl⟩ : syracuseStep 992965 = 186181) (by norm_num)
theorem B1255133 : Blo 880569 1255133 := bbase (se 3 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 1255133 = 470675) (by norm_num)
theorem B993001 : Blo 880569 993001 := bbase (se 2 (by rfl) ⟨372375, by rfl⟩ : syracuseStep 993001 = 744751) (by norm_num)
theorem B993037 : Blo 880569 993037 := bbase (se 3 (by rfl) ⟨186194, by rfl⟩ : syracuseStep 993037 = 372389) (by norm_num)
theorem B1255213 : Blo 880569 1255213 := bbase (se 3 (by rfl) ⟨235352, by rfl⟩ : syracuseStep 1255213 = 470705) (by norm_num)
theorem B993073 : Blo 880569 993073 := bbase (se 2 (by rfl) ⟨372402, by rfl⟩ : syracuseStep 993073 = 744805) (by norm_num)
theorem B4466501 : Blo 880569 4466501 := bbase (se 4 (by rfl) ⟨418734, by rfl⟩ : syracuseStep 4466501 = 837469) (by norm_num)
theorem B993109 : Blo 880569 993109 := bbase (se 9 (by rfl) ⟨2909, by rfl⟩ : syracuseStep 993109 = 5819) (by norm_num)
theorem B2238293 : Blo 880569 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B993145 : Blo 880569 993145 := bbase (se 2 (by rfl) ⟨372429, by rfl⟩ : syracuseStep 993145 = 744859) (by norm_num)
theorem B894845 : Blo 880569 894845 := bbase (se 3 (by rfl) ⟨167783, by rfl⟩ : syracuseStep 894845 = 335567) (by norm_num)
theorem B993181 : Blo 880569 993181 := bbase (se 3 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 993181 = 372443) (by norm_num)
theorem B1320869 : Blo 880569 1320869 := bbase (se 4 (by rfl) ⟨123831, by rfl⟩ : syracuseStep 1320869 = 247663) (by norm_num)
theorem B1255333 : Blo 880569 1255333 := bbase (se 4 (by rfl) ⟨117687, by rfl⟩ : syracuseStep 1255333 = 235375) (by norm_num)
theorem B1320893 : Blo 880569 1320893 := bbase (se 3 (by rfl) ⟨247667, by rfl⟩ : syracuseStep 1320893 = 495335) (by norm_num)
theorem B993217 : Blo 880569 993217 := bbase (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) (by norm_num)
theorem B1320917 : Blo 880569 1320917 := bbase (se 7 (by rfl) ⟨15479, by rfl⟩ : syracuseStep 1320917 = 30959) (by norm_num)
theorem B993253 : Blo 880569 993253 := bbase (se 4 (by rfl) ⟨93117, by rfl⟩ : syracuseStep 993253 = 186235) (by norm_num)
theorem B3352549 : Blo 880569 3352549 := bbase (se 4 (by rfl) ⟨314301, by rfl⟩ : syracuseStep 3352549 = 628603) (by norm_num)
theorem B1320941 : Blo 880569 1320941 := bbase (se 3 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 1320941 = 495353) (by norm_num)
theorem B1320965 : Blo 880569 1320965 := bbase (se 4 (by rfl) ⟨123840, by rfl⟩ : syracuseStep 1320965 = 247681) (by norm_num)
theorem B1255429 : Blo 880569 1255429 := bbase (se 4 (by rfl) ⟨117696, by rfl⟩ : syracuseStep 1255429 = 235393) (by norm_num)
theorem B993289 : Blo 880569 993289 := bbase (se 2 (by rfl) ⟨372483, by rfl⟩ : syracuseStep 993289 = 744967) (by norm_num)
theorem B1320989 : Blo 880569 1320989 := bbase (se 3 (by rfl) ⟨247685, by rfl⟩ : syracuseStep 1320989 = 495371) (by norm_num)
theorem B993325 : Blo 880569 993325 := bbase (se 3 (by rfl) ⟨186248, by rfl⟩ : syracuseStep 993325 = 372497) (by norm_num)
theorem B1321013 : Blo 880569 1321013 := bbase (se 5 (by rfl) ⟨61922, by rfl⟩ : syracuseStep 1321013 = 123845) (by norm_num)
theorem B4237381 : Blo 880569 4237381 := bbase (se 4 (by rfl) ⟨397254, by rfl⟩ : syracuseStep 4237381 = 794509) (by norm_num)
theorem B1321037 : Blo 880569 1321037 := bbase (se 3 (by rfl) ⟨247694, by rfl⟩ : syracuseStep 1321037 = 495389) (by norm_num)
theorem B993361 : Blo 880569 993361 := bbase (se 2 (by rfl) ⟨372510, by rfl⟩ : syracuseStep 993361 = 745021) (by norm_num)
theorem B1321061 : Blo 880569 1321061 := bbase (se 4 (by rfl) ⟨123849, by rfl⟩ : syracuseStep 1321061 = 247699) (by norm_num)
theorem B993397 : Blo 880569 993397 := bbase (se 5 (by rfl) ⟨46565, by rfl⟩ : syracuseStep 993397 = 93131) (by norm_num)
theorem B6367349 : Blo 880569 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B1321085 : Blo 880569 1321085 := bbase (se 3 (by rfl) ⟨247703, by rfl⟩ : syracuseStep 1321085 = 495407) (by norm_num)
theorem B1321109 : Blo 880569 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B993433 : Blo 880569 993433 := bbase (se 2 (by rfl) ⟨372537, by rfl⟩ : syracuseStep 993433 = 745075) (by norm_num)
theorem B1321133 : Blo 880569 1321133 := bbase (se 3 (by rfl) ⟨247712, by rfl⟩ : syracuseStep 1321133 = 495425) (by norm_num)
theorem B2238637 : Blo 880569 2238637 := bbase (se 3 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 2238637 = 839489) (by norm_num)
theorem B993469 : Blo 880569 993469 := bbase (se 3 (by rfl) ⟨186275, by rfl⟩ : syracuseStep 993469 = 372551) (by norm_num)
theorem B1321157 : Blo 880569 1321157 := bbase (se 4 (by rfl) ⟨123858, by rfl⟩ : syracuseStep 1321157 = 247717) (by norm_num)
theorem B1321181 : Blo 880569 1321181 := bbase (se 3 (by rfl) ⟨247721, by rfl⟩ : syracuseStep 1321181 = 495443) (by norm_num)
theorem B993505 : Blo 880569 993505 := bbase (se 2 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 993505 = 745129) (by norm_num)
theorem B1321205 : Blo 880569 1321205 := bbase (se 5 (by rfl) ⟨61931, by rfl⟩ : syracuseStep 1321205 = 123863) (by norm_num)
theorem B993541 : Blo 880569 993541 := bbase (se 4 (by rfl) ⟨93144, by rfl⟩ : syracuseStep 993541 = 186289) (by norm_num)
theorem B1321229 : Blo 880569 1321229 := bbase (se 3 (by rfl) ⟨247730, by rfl⟩ : syracuseStep 1321229 = 495461) (by norm_num)
theorem B3352853 : Blo 880569 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B2238749 : Blo 880569 2238749 := bbase (se 3 (by rfl) ⟨419765, by rfl⟩ : syracuseStep 2238749 = 839531) (by norm_num)
theorem B1321253 : Blo 880569 1321253 := bbase (se 4 (by rfl) ⟨123867, by rfl⟩ : syracuseStep 1321253 = 247735) (by norm_num)
theorem B993577 : Blo 880569 993577 := bbase (se 2 (by rfl) ⟨372591, by rfl⟩ : syracuseStep 993577 = 745183) (by norm_num)
theorem B1321277 : Blo 880569 1321277 := bbase (se 3 (by rfl) ⟨247739, by rfl⟩ : syracuseStep 1321277 = 495479) (by norm_num)
theorem B993613 : Blo 880569 993613 := bbase (se 3 (by rfl) ⟨186302, by rfl⟩ : syracuseStep 993613 = 372605) (by norm_num)
theorem B1321301 : Blo 880569 1321301 := bbase (se 10 (by rfl) ⟨1935, by rfl⟩ : syracuseStep 1321301 = 3871) (by norm_num)
theorem B1321325 : Blo 880569 1321325 := bbase (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) (by norm_num)
theorem B993649 : Blo 880569 993649 := bbase (se 2 (by rfl) ⟨372618, by rfl⟩ : syracuseStep 993649 = 745237) (by norm_num)
theorem B1321349 : Blo 880569 1321349 := bbase (se 4 (by rfl) ⟨123876, by rfl⟩ : syracuseStep 1321349 = 247753) (by norm_num)
theorem B993685 : Blo 880569 993685 := bbase (se 6 (by rfl) ⟨23289, by rfl⟩ : syracuseStep 993685 = 46579) (by norm_num)
theorem B1321373 : Blo 880569 1321373 := bbase (se 3 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 1321373 = 495515) (by norm_num)
theorem B1321397 : Blo 880569 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B993721 : Blo 880569 993721 := bbase (se 2 (by rfl) ⟨372645, by rfl⟩ : syracuseStep 993721 = 745291) (by norm_num)
theorem B895421 : Blo 880569 895421 := bbase (se 3 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 895421 = 335783) (by norm_num)
theorem B1321421 : Blo 880569 1321421 := bbase (se 3 (by rfl) ⟨247766, by rfl⟩ : syracuseStep 1321421 = 495533) (by norm_num)
theorem B11446741 : Blo 880569 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B993757 : Blo 880569 993757 := bbase (se 3 (by rfl) ⟨186329, by rfl⟩ : syracuseStep 993757 = 372659) (by norm_num)
theorem B2238941 : Blo 880569 2238941 := bbase (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) (by norm_num)
theorem B1321445 : Blo 880569 1321445 := bbase (se 4 (by rfl) ⟨123885, by rfl⟩ : syracuseStep 1321445 = 247771) (by norm_num)
theorem B1255925 : Blo 880569 1255925 := bbase (se 5 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 1255925 = 117743) (by norm_num)
theorem B1321469 : Blo 880569 1321469 := bbase (se 3 (by rfl) ⟨247775, by rfl⟩ : syracuseStep 1321469 = 495551) (by norm_num)
theorem B993793 : Blo 880569 993793 := bbase (se 2 (by rfl) ⟨372672, by rfl⟩ : syracuseStep 993793 = 745345) (by norm_num)
theorem B1321493 : Blo 880569 1321493 := bbase (se 6 (by rfl) ⟨30972, by rfl⟩ : syracuseStep 1321493 = 61945) (by norm_num)
theorem B993829 : Blo 880569 993829 := bbase (se 4 (by rfl) ⟨93171, by rfl⟩ : syracuseStep 993829 = 186343) (by norm_num)
theorem B1321517 : Blo 880569 1321517 := bbase (se 3 (by rfl) ⟨247784, by rfl⟩ : syracuseStep 1321517 = 495569) (by norm_num)
theorem B1321541 : Blo 880569 1321541 := bbase (se 4 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 1321541 = 247789) (by norm_num)
theorem B993865 : Blo 880569 993865 := bbase (se 2 (by rfl) ⟨372699, by rfl⟩ : syracuseStep 993865 = 745399) (by norm_num)
theorem B1321565 : Blo 880569 1321565 := bbase (se 3 (by rfl) ⟨247793, by rfl⟩ : syracuseStep 1321565 = 495587) (by norm_num)
theorem B993901 : Blo 880569 993901 := bbase (se 3 (by rfl) ⟨186356, by rfl⟩ : syracuseStep 993901 = 372713) (by norm_num)
theorem B1321589 : Blo 880569 1321589 := bbase (se 5 (by rfl) ⟨61949, by rfl⟩ : syracuseStep 1321589 = 123899) (by norm_num)
theorem B1321613 : Blo 880569 1321613 := bbase (se 3 (by rfl) ⟨247802, by rfl⟩ : syracuseStep 1321613 = 495605) (by norm_num)
theorem B993937 : Blo 880569 993937 := bbase (se 2 (by rfl) ⟨372726, by rfl⟩ : syracuseStep 993937 = 745453) (by norm_num)
theorem B1321637 : Blo 880569 1321637 := bbase (se 4 (by rfl) ⟨123903, by rfl⟩ : syracuseStep 1321637 = 247807) (by norm_num)
theorem B993973 : Blo 880569 993973 := bbase (se 5 (by rfl) ⟨46592, by rfl⟩ : syracuseStep 993973 = 93185) (by norm_num)
theorem B1321661 : Blo 880569 1321661 := bbase (se 3 (by rfl) ⟨247811, by rfl⟩ : syracuseStep 1321661 = 495623) (by norm_num)
theorem B1321685 : Blo 880569 1321685 := bbase (se 7 (by rfl) ⟨15488, by rfl⟩ : syracuseStep 1321685 = 30977) (by norm_num)
theorem B994009 : Blo 880569 994009 := bbase (se 2 (by rfl) ⟨372753, by rfl⟩ : syracuseStep 994009 = 745507) (by norm_num)
theorem B1321709 : Blo 880569 1321709 := bbase (se 3 (by rfl) ⟨247820, by rfl⟩ : syracuseStep 1321709 = 495641) (by norm_num)
theorem B994045 : Blo 880569 994045 := bbase (se 3 (by rfl) ⟨186383, by rfl⟩ : syracuseStep 994045 = 372767) (by norm_num)
theorem B1321733 : Blo 880569 1321733 := bbase (se 4 (by rfl) ⟨123912, by rfl⟩ : syracuseStep 1321733 = 247825) (by norm_num)
theorem B3025685 : Blo 880569 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B1321757 : Blo 880569 1321757 := bbase (se 3 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 1321757 = 495659) (by norm_num)
theorem B994081 : Blo 880569 994081 := bbase (se 2 (by rfl) ⟨372780, by rfl⟩ : syracuseStep 994081 = 745561) (by norm_num)
theorem B1321781 : Blo 880569 1321781 := bbase (se 5 (by rfl) ⟨61958, by rfl⟩ : syracuseStep 1321781 = 123917) (by norm_num)
theorem B1059653 : Blo 880569 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B994117 : Blo 880569 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B1321805 : Blo 880569 1321805 := bbase (se 3 (by rfl) ⟨247838, by rfl⟩ : syracuseStep 1321805 = 495677) (by norm_num)
theorem B1321829 : Blo 880569 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B994153 : Blo 880569 994153 := bbase (se 2 (by rfl) ⟨372807, by rfl⟩ : syracuseStep 994153 = 745615) (by norm_num)
theorem B1321853 : Blo 880569 1321853 := bbase (se 3 (by rfl) ⟨247847, by rfl⟩ : syracuseStep 1321853 = 495695) (by norm_num)
theorem B994189 : Blo 880569 994189 := bbase (se 3 (by rfl) ⟨186410, by rfl⟩ : syracuseStep 994189 = 372821) (by norm_num)
theorem B1321877 : Blo 880569 1321877 := bbase (se 6 (by rfl) ⟨30981, by rfl⟩ : syracuseStep 1321877 = 61963) (by norm_num)
theorem B1321901 : Blo 880569 1321901 := bbase (se 3 (by rfl) ⟨247856, by rfl⟩ : syracuseStep 1321901 = 495713) (by norm_num)
theorem B994225 : Blo 880569 994225 := bbase (se 2 (by rfl) ⟨372834, by rfl⟩ : syracuseStep 994225 = 745669) (by norm_num)
theorem B1321925 : Blo 880569 1321925 := bbase (se 4 (by rfl) ⟨123930, by rfl⟩ : syracuseStep 1321925 = 247861) (by norm_num)
theorem B994261 : Blo 880569 994261 := bbase (se 7 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 994261 = 23303) (by norm_num)
theorem B1321949 : Blo 880569 1321949 := bbase (se 3 (by rfl) ⟨247865, by rfl⟩ : syracuseStep 1321949 = 495731) (by norm_num)
theorem B1321973 : Blo 880569 1321973 := bbase (se 5 (by rfl) ⟨61967, by rfl⟩ : syracuseStep 1321973 = 123935) (by norm_num)
theorem B994297 : Blo 880569 994297 := bbase (se 2 (by rfl) ⟨372861, by rfl⟩ : syracuseStep 994297 = 745723) (by norm_num)
theorem B1059841 : Blo 880569 1059841 := bbase (se 2 (by rfl) ⟨397440, by rfl⟩ : syracuseStep 1059841 = 794881) (by norm_num)
theorem B1321997 : Blo 880569 1321997 := bbase (se 3 (by rfl) ⟨247874, by rfl⟩ : syracuseStep 1321997 = 495749) (by norm_num)
theorem B1256477 : Blo 880569 1256477 := bbase (se 3 (by rfl) ⟨235589, by rfl⟩ : syracuseStep 1256477 = 471179) (by norm_num)
theorem B994333 : Blo 880569 994333 := bbase (se 3 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 994333 = 372875) (by norm_num)
theorem B1322021 : Blo 880569 1322021 := bbase (se 4 (by rfl) ⟨123939, by rfl⟩ : syracuseStep 1322021 = 247879) (by norm_num)
theorem B1322045 : Blo 880569 1322045 := bbase (se 3 (by rfl) ⟨247883, by rfl⟩ : syracuseStep 1322045 = 495767) (by norm_num)
theorem B994369 : Blo 880569 994369 := bbase (se 2 (by rfl) ⟨372888, by rfl⟩ : syracuseStep 994369 = 745777) (by norm_num)
theorem B1322069 : Blo 880569 1322069 := bbase (se 8 (by rfl) ⟨7746, by rfl⟩ : syracuseStep 1322069 = 15493) (by norm_num)
theorem B4467797 : Blo 880569 4467797 := bbase (se 8 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 4467797 = 52357) (by norm_num)
theorem B4598869 : Blo 880569 4598869 := bbase (se 8 (by rfl) ⟨26946, by rfl⟩ : syracuseStep 4598869 = 53893) (by norm_num)
theorem B994405 : Blo 880569 994405 := bbase (se 4 (by rfl) ⟨93225, by rfl⟩ : syracuseStep 994405 = 186451) (by norm_num)
theorem B1322093 : Blo 880569 1322093 := bbase (se 3 (by rfl) ⟨247892, by rfl⟩ : syracuseStep 1322093 = 495785) (by norm_num)
theorem B1322117 : Blo 880569 1322117 := bbase (se 4 (by rfl) ⟨123948, by rfl⟩ : syracuseStep 1322117 = 247897) (by norm_num)
theorem B994441 : Blo 880569 994441 := bbase (se 2 (by rfl) ⟨372915, by rfl⟩ : syracuseStep 994441 = 745831) (by norm_num)
theorem B1485965 : Blo 880569 1485965 := bbase (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) (by norm_num)
theorem B1322141 : Blo 880569 1322141 := bbase (se 3 (by rfl) ⟨247901, by rfl⟩ : syracuseStep 1322141 = 495803) (by norm_num)
theorem B994477 : Blo 880569 994477 := bbase (se 3 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 994477 = 372929) (by norm_num)
theorem B1322165 : Blo 880569 1322165 := bbase (se 5 (by rfl) ⟨61976, by rfl⟩ : syracuseStep 1322165 = 123953) (by norm_num)
theorem B1322189 : Blo 880569 1322189 := bbase (se 3 (by rfl) ⟨247910, by rfl⟩ : syracuseStep 1322189 = 495821) (by norm_num)
theorem B994513 : Blo 880569 994513 := bbase (se 2 (by rfl) ⟨372942, by rfl⟩ : syracuseStep 994513 = 745885) (by norm_num)
theorem B1060057 : Blo 880569 1060057 := bbase (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) (by norm_num)
theorem B1322213 : Blo 880569 1322213 := bbase (se 4 (by rfl) ⟨123957, by rfl⟩ : syracuseStep 1322213 = 247915) (by norm_num)
theorem B994549 : Blo 880569 994549 := bbase (se 5 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 994549 = 93239) (by norm_num)
theorem B1322237 : Blo 880569 1322237 := bbase (se 3 (by rfl) ⟨247919, by rfl⟩ : syracuseStep 1322237 = 495839) (by norm_num)
theorem B1486093 : Blo 880569 1486093 := bbase (se 3 (by rfl) ⟨278642, by rfl⟩ : syracuseStep 1486093 = 557285) (by norm_num)
theorem B1191181 : Blo 880569 1191181 := bbase (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) (by norm_num)
theorem B1322261 : Blo 880569 1322261 := bbase (se 6 (by rfl) ⟨30990, by rfl⟩ : syracuseStep 1322261 = 61981) (by norm_num)
theorem B994585 : Blo 880569 994585 := bbase (se 2 (by rfl) ⟨372969, by rfl⟩ : syracuseStep 994585 = 745939) (by norm_num)
theorem B1322285 : Blo 880569 1322285 := bbase (se 3 (by rfl) ⟨247928, by rfl⟩ : syracuseStep 1322285 = 495857) (by norm_num)
theorem B994621 : Blo 880569 994621 := bbase (se 3 (by rfl) ⟨186491, by rfl⟩ : syracuseStep 994621 = 372983) (by norm_num)
theorem B1322309 : Blo 880569 1322309 := bbase (se 4 (by rfl) ⟨123966, by rfl⟩ : syracuseStep 1322309 = 247933) (by norm_num)
theorem B4828501 : Blo 880569 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B1322333 : Blo 880569 1322333 := bbase (se 3 (by rfl) ⟨247937, by rfl⟩ : syracuseStep 1322333 = 495875) (by norm_num)
theorem B994657 : Blo 880569 994657 := bbase (se 2 (by rfl) ⟨372996, by rfl⟩ : syracuseStep 994657 = 745993) (by norm_num)
theorem B1486181 : Blo 880569 1486181 := bbase (se 4 (by rfl) ⟨139329, by rfl⟩ : syracuseStep 1486181 = 278659) (by norm_num)
theorem B1322357 : Blo 880569 1322357 := bbase (se 5 (by rfl) ⟨61985, by rfl⟩ : syracuseStep 1322357 = 123971) (by norm_num)
theorem B994693 : Blo 880569 994693 := bbase (se 4 (by rfl) ⟨93252, by rfl⟩ : syracuseStep 994693 = 186505) (by norm_num)
theorem B1322381 : Blo 880569 1322381 := bbase (se 3 (by rfl) ⟨247946, by rfl⟩ : syracuseStep 1322381 = 495893) (by norm_num)
theorem B1322405 : Blo 880569 1322405 := bbase (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) (by norm_num)
theorem B994729 : Blo 880569 994729 := bbase (se 2 (by rfl) ⟨373023, by rfl⟩ : syracuseStep 994729 = 746047) (by norm_num)
theorem B1322429 : Blo 880569 1322429 := bbase (se 3 (by rfl) ⟨247955, by rfl⟩ : syracuseStep 1322429 = 495911) (by norm_num)
theorem B994765 : Blo 880569 994765 := bbase (se 3 (by rfl) ⟨186518, by rfl⟩ : syracuseStep 994765 = 373037) (by norm_num)
theorem B1322453 : Blo 880569 1322453 := bbase (se 7 (by rfl) ⟨15497, by rfl⟩ : syracuseStep 1322453 = 30995) (by norm_num)
theorem B1486309 : Blo 880569 1486309 := bbase (se 4 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 1486309 = 278683) (by norm_num)
theorem B1322477 : Blo 880569 1322477 := bbase (se 3 (by rfl) ⟨247964, by rfl⟩ : syracuseStep 1322477 = 495929) (by norm_num)
theorem B994801 : Blo 880569 994801 := bbase (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) (by norm_num)
theorem B1060345 : Blo 880569 1060345 := bbase (se 2 (by rfl) ⟨397629, by rfl⟩ : syracuseStep 1060345 = 795259) (by norm_num)
theorem B1322501 : Blo 880569 1322501 := bbase (se 4 (by rfl) ⟨123984, by rfl⟩ : syracuseStep 1322501 = 247969) (by norm_num)
theorem B994837 : Blo 880569 994837 := bbase (se 6 (by rfl) ⟨23316, by rfl⟩ : syracuseStep 994837 = 46633) (by norm_num)
theorem B1322525 : Blo 880569 1322525 := bbase (se 3 (by rfl) ⟨247973, by rfl⟩ : syracuseStep 1322525 = 495947) (by norm_num)
theorem B896545 : Blo 880569 896545 := bbase (se 2 (by rfl) ⟨336204, by rfl⟩ : syracuseStep 896545 = 672409) (by norm_num)
theorem B1322549 : Blo 880569 1322549 := bbase (se 5 (by rfl) ⟨61994, by rfl⟩ : syracuseStep 1322549 = 123989) (by norm_num)
theorem B994873 : Blo 880569 994873 := bbase (se 2 (by rfl) ⟨373077, by rfl⟩ : syracuseStep 994873 = 746155) (by norm_num)
theorem B1486397 : Blo 880569 1486397 := bbase (se 3 (by rfl) ⟨278699, by rfl⟩ : syracuseStep 1486397 = 557399) (by norm_num)
theorem B1322573 : Blo 880569 1322573 := bbase (se 3 (by rfl) ⟨247982, by rfl⟩ : syracuseStep 1322573 = 495965) (by norm_num)
theorem B994909 : Blo 880569 994909 := bbase (se 3 (by rfl) ⟨186545, by rfl⟩ : syracuseStep 994909 = 373091) (by norm_num)
theorem B1322597 : Blo 880569 1322597 := bbase (se 4 (by rfl) ⟨123993, by rfl⟩ : syracuseStep 1322597 = 247987) (by norm_num)
theorem B1322621 : Blo 880569 1322621 := bbase (se 3 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 1322621 = 495983) (by norm_num)
theorem B994945 : Blo 880569 994945 := bbase (se 2 (by rfl) ⟨373104, by rfl⟩ : syracuseStep 994945 = 746209) (by norm_num)
theorem B1322645 : Blo 880569 1322645 := bbase (se 6 (by rfl) ⟨30999, by rfl⟩ : syracuseStep 1322645 = 61999) (by norm_num)
theorem B12070549 : Blo 880569 12070549 := bbase (se 6 (by rfl) ⟨282903, by rfl⟩ : syracuseStep 12070549 = 565807) (by norm_num)
theorem B994981 : Blo 880569 994981 := bbase (se 4 (by rfl) ⟨93279, by rfl⟩ : syracuseStep 994981 = 186559) (by norm_num)
theorem B1322669 : Blo 880569 1322669 := bbase (se 3 (by rfl) ⟨248000, by rfl⟩ : syracuseStep 1322669 = 496001) (by norm_num)
theorem B1486525 : Blo 880569 1486525 := bbase (se 3 (by rfl) ⟨278723, by rfl⟩ : syracuseStep 1486525 = 557447) (by norm_num)
theorem B1322693 : Blo 880569 1322693 := bbase (se 4 (by rfl) ⟨124002, by rfl⟩ : syracuseStep 1322693 = 248005) (by norm_num)
theorem B995017 : Blo 880569 995017 := bbase (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) (by norm_num)
theorem B1191629 : Blo 880569 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B1322717 : Blo 880569 1322717 := bbase (se 3 (by rfl) ⟨248009, by rfl⟩ : syracuseStep 1322717 = 496019) (by norm_num)
theorem B995053 : Blo 880569 995053 := bbase (se 3 (by rfl) ⟨186572, by rfl⟩ : syracuseStep 995053 = 373145) (by norm_num)
theorem B1322741 : Blo 880569 1322741 := bbase (se 5 (by rfl) ⟨62003, by rfl⟩ : syracuseStep 1322741 = 124007) (by norm_num)
theorem B1322765 : Blo 880569 1322765 := bbase (se 3 (by rfl) ⟨248018, by rfl⟩ : syracuseStep 1322765 = 496037) (by norm_num)
theorem B1257229 : Blo 880569 1257229 := bbase (se 3 (by rfl) ⟨235730, by rfl⟩ : syracuseStep 1257229 = 471461) (by norm_num)
theorem B995089 : Blo 880569 995089 := bbase (se 2 (by rfl) ⟨373158, by rfl⟩ : syracuseStep 995089 = 746317) (by norm_num)
theorem B1486613 : Blo 880569 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B1322789 : Blo 880569 1322789 := bbase (se 4 (by rfl) ⟨124011, by rfl⟩ : syracuseStep 1322789 = 248023) (by norm_num)
theorem B995125 : Blo 880569 995125 := bbase (se 5 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 995125 = 93293) (by norm_num)
theorem B1322813 : Blo 880569 1322813 := bbase (se 3 (by rfl) ⟨248027, by rfl⟩ : syracuseStep 1322813 = 496055) (by norm_num)
theorem B1322837 : Blo 880569 1322837 := bbase (se 9 (by rfl) ⟨3875, by rfl⟩ : syracuseStep 1322837 = 7751) (by norm_num)
theorem B1322861 : Blo 880569 1322861 := bbase (se 3 (by rfl) ⟨248036, by rfl⟩ : syracuseStep 1322861 = 496073) (by norm_num)
theorem B1322885 : Blo 880569 1322885 := bbase (se 4 (by rfl) ⟨124020, by rfl⟩ : syracuseStep 1322885 = 248041) (by norm_num)
theorem B1486741 : Blo 880569 1486741 := bbase (se 6 (by rfl) ⟨34845, by rfl⟩ : syracuseStep 1486741 = 69691) (by norm_num)
theorem B1322909 : Blo 880569 1322909 := bbase (se 3 (by rfl) ⟨248045, by rfl⟩ : syracuseStep 1322909 = 496091) (by norm_num)
theorem B1322933 : Blo 880569 1322933 := bbase (se 5 (by rfl) ⟨62012, by rfl⟩ : syracuseStep 1322933 = 124025) (by norm_num)
theorem B1322957 : Blo 880569 1322957 := bbase (se 3 (by rfl) ⟨248054, by rfl⟩ : syracuseStep 1322957 = 496109) (by norm_num)
theorem B1322981 : Blo 880569 1322981 := bbase (se 4 (by rfl) ⟨124029, by rfl⟩ : syracuseStep 1322981 = 248059) (by norm_num)
theorem B1486829 : Blo 880569 1486829 := bbase (se 3 (by rfl) ⟨278780, by rfl⟩ : syracuseStep 1486829 = 557561) (by norm_num)
theorem B1323005 : Blo 880569 1323005 := bbase (se 3 (by rfl) ⟨248063, by rfl⟩ : syracuseStep 1323005 = 496127) (by norm_num)
theorem B1323029 : Blo 880569 1323029 := bbase (se 6 (by rfl) ⟨31008, by rfl⟩ : syracuseStep 1323029 = 62017) (by norm_num)
theorem B1323053 : Blo 880569 1323053 := bbase (se 3 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 1323053 = 496145) (by norm_num)
theorem B1323077 : Blo 880569 1323077 := bbase (se 4 (by rfl) ⟨124038, by rfl⟩ : syracuseStep 1323077 = 248077) (by norm_num)
theorem B1323101 : Blo 880569 1323101 := bbase (se 3 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 1323101 = 496163) (by norm_num)
theorem B3584101 : Blo 880569 3584101 := bbase (se 4 (by rfl) ⟨336009, by rfl⟩ : syracuseStep 3584101 = 672019) (by norm_num)
theorem B1486957 : Blo 880569 1486957 := bbase (se 3 (by rfl) ⟨278804, by rfl⟩ : syracuseStep 1486957 = 557609) (by norm_num)
theorem B1323125 : Blo 880569 1323125 := bbase (se 5 (by rfl) ⟨62021, by rfl⟩ : syracuseStep 1323125 = 124043) (by norm_num)
theorem B1323149 : Blo 880569 1323149 := bbase (se 3 (by rfl) ⟨248090, by rfl⟩ : syracuseStep 1323149 = 496181) (by norm_num)
theorem B1323173 : Blo 880569 1323173 := bbase (se 4 (by rfl) ⟨124047, by rfl⟩ : syracuseStep 1323173 = 248095) (by norm_num)
theorem B1323197 : Blo 880569 1323197 := bbase (se 3 (by rfl) ⟨248099, by rfl⟩ : syracuseStep 1323197 = 496199) (by norm_num)
theorem B1487045 : Blo 880569 1487045 := bbase (se 4 (by rfl) ⟨139410, by rfl⟩ : syracuseStep 1487045 = 278821) (by norm_num)
theorem B1323221 : Blo 880569 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B1323245 : Blo 880569 1323245 := bbase (se 3 (by rfl) ⟨248108, by rfl⟩ : syracuseStep 1323245 = 496217) (by norm_num)
theorem B1323269 : Blo 880569 1323269 := bbase (se 4 (by rfl) ⟨124056, by rfl⟩ : syracuseStep 1323269 = 248113) (by norm_num)
theorem B1323293 : Blo 880569 1323293 := bbase (se 3 (by rfl) ⟨248117, by rfl⟩ : syracuseStep 1323293 = 496235) (by norm_num)
theorem B1323317 : Blo 880569 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1487173 : Blo 880569 1487173 := bbase (se 4 (by rfl) ⟨139422, by rfl⟩ : syracuseStep 1487173 = 278845) (by norm_num)
theorem B1323341 : Blo 880569 1323341 := bbase (se 3 (by rfl) ⟨248126, by rfl⟩ : syracuseStep 1323341 = 496253) (by norm_num)
theorem B3354965 : Blo 880569 3354965 := bbase (se 10 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 3354965 = 9829) (by norm_num)
theorem B1323365 : Blo 880569 1323365 := bbase (se 4 (by rfl) ⟨124065, by rfl⟩ : syracuseStep 1323365 = 248131) (by norm_num)
theorem B4469093 : Blo 880569 4469093 := bbase (se 4 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 4469093 = 837955) (by norm_num)
theorem B1323389 : Blo 880569 1323389 := bbase (se 3 (by rfl) ⟨248135, by rfl⟩ : syracuseStep 1323389 = 496271) (by norm_num)
theorem B1323413 : Blo 880569 1323413 := bbase (se 6 (by rfl) ⟨31017, by rfl⟩ : syracuseStep 1323413 = 62035) (by norm_num)
theorem B1487261 : Blo 880569 1487261 := bbase (se 3 (by rfl) ⟨278861, by rfl⟩ : syracuseStep 1487261 = 557723) (by norm_num)
theorem B1323437 : Blo 880569 1323437 := bbase (se 3 (by rfl) ⟨248144, by rfl⟩ : syracuseStep 1323437 = 496289) (by norm_num)
theorem B1323461 : Blo 880569 1323461 := bbase (se 4 (by rfl) ⟨124074, by rfl⟩ : syracuseStep 1323461 = 248149) (by norm_num)
theorem B1323485 : Blo 880569 1323485 := bbase (se 3 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 1323485 = 496307) (by norm_num)
theorem B1323509 : Blo 880569 1323509 := bbase (se 5 (by rfl) ⟨62039, by rfl⟩ : syracuseStep 1323509 = 124079) (by norm_num)
theorem B1323533 : Blo 880569 1323533 := bbase (se 3 (by rfl) ⟨248162, by rfl⟩ : syracuseStep 1323533 = 496325) (by norm_num)
theorem B1487389 : Blo 880569 1487389 := bbase (se 3 (by rfl) ⟨278885, by rfl⟩ : syracuseStep 1487389 = 557771) (by norm_num)
theorem B1323557 : Blo 880569 1323557 := bbase (se 4 (by rfl) ⟨124083, by rfl⟩ : syracuseStep 1323557 = 248167) (by norm_num)
theorem B1258021 : Blo 880569 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B1323581 : Blo 880569 1323581 := bbase (se 3 (by rfl) ⟨248171, by rfl⟩ : syracuseStep 1323581 = 496343) (by norm_num)
theorem B1323605 : Blo 880569 1323605 := bbase (se 8 (by rfl) ⟨7755, by rfl⟩ : syracuseStep 1323605 = 15511) (by norm_num)
theorem B1323629 : Blo 880569 1323629 := bbase (se 3 (by rfl) ⟨248180, by rfl⟩ : syracuseStep 1323629 = 496361) (by norm_num)
theorem B1487477 : Blo 880569 1487477 := bbase (se 5 (by rfl) ⟨69725, by rfl⟩ : syracuseStep 1487477 = 139451) (by norm_num)
theorem B3355253 : Blo 880569 3355253 := bbase (se 5 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 3355253 = 314555) (by norm_num)
theorem B1323653 : Blo 880569 1323653 := bbase (se 4 (by rfl) ⟨124092, by rfl⟩ : syracuseStep 1323653 = 248185) (by norm_num)
theorem B1323677 : Blo 880569 1323677 := bbase (se 3 (by rfl) ⟨248189, by rfl⟩ : syracuseStep 1323677 = 496379) (by norm_num)
theorem B1323701 : Blo 880569 1323701 := bbase (se 5 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 1323701 = 124097) (by norm_num)
theorem B1323725 : Blo 880569 1323725 := bbase (se 3 (by rfl) ⟨248198, by rfl⟩ : syracuseStep 1323725 = 496397) (by norm_num)
theorem B1323749 : Blo 880569 1323749 := bbase (se 4 (by rfl) ⟨124101, by rfl⟩ : syracuseStep 1323749 = 248203) (by norm_num)
theorem B1880813 : Blo 880569 1880813 := bbase (se 3 (by rfl) ⟨352652, by rfl⟩ : syracuseStep 1880813 = 705305) (by norm_num)
theorem B1487605 : Blo 880569 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B1323773 : Blo 880569 1323773 := bbase (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) (by norm_num)
theorem B1061633 : Blo 880569 1061633 := bbase (se 2 (by rfl) ⟨398112, by rfl⟩ : syracuseStep 1061633 = 796225) (by norm_num)
theorem B1323797 : Blo 880569 1323797 := bbase (se 6 (by rfl) ⟨31026, by rfl⟩ : syracuseStep 1323797 = 62053) (by norm_num)
theorem B1323821 : Blo 880569 1323821 := bbase (se 3 (by rfl) ⟨248216, by rfl⟩ : syracuseStep 1323821 = 496433) (by norm_num)
theorem B1323845 : Blo 880569 1323845 := bbase (se 4 (by rfl) ⟨124110, by rfl⟩ : syracuseStep 1323845 = 248221) (by norm_num)
theorem B1487693 : Blo 880569 1487693 := bbase (se 3 (by rfl) ⟨278942, by rfl⟩ : syracuseStep 1487693 = 557885) (by norm_num)
theorem B1323869 : Blo 880569 1323869 := bbase (se 3 (by rfl) ⟨248225, by rfl⟩ : syracuseStep 1323869 = 496451) (by norm_num)
theorem B1323893 : Blo 880569 1323893 := bbase (se 5 (by rfl) ⟨62057, by rfl⟩ : syracuseStep 1323893 = 124115) (by norm_num)
theorem B1258357 : Blo 880569 1258357 := bbase (se 5 (by rfl) ⟨58985, by rfl⟩ : syracuseStep 1258357 = 117971) (by norm_num)
theorem B1880957 : Blo 880569 1880957 := bbase (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) (by norm_num)
theorem B1323917 : Blo 880569 1323917 := bbase (se 3 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 1323917 = 496469) (by norm_num)
theorem B1323941 : Blo 880569 1323941 := bbase (se 4 (by rfl) ⟨124119, by rfl⟩ : syracuseStep 1323941 = 248239) (by norm_num)
theorem B1323965 : Blo 880569 1323965 := bbase (se 3 (by rfl) ⟨248243, by rfl⟩ : syracuseStep 1323965 = 496487) (by norm_num)
theorem B1487821 : Blo 880569 1487821 := bbase (se 3 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 1487821 = 557933) (by norm_num)
theorem B1323989 : Blo 880569 1323989 := bbase (se 7 (by rfl) ⟨15515, by rfl⟩ : syracuseStep 1323989 = 31031) (by norm_num)
theorem B1324013 : Blo 880569 1324013 := bbase (se 3 (by rfl) ⟨248252, by rfl⟩ : syracuseStep 1324013 = 496505) (by norm_num)
theorem B1324037 : Blo 880569 1324037 := bbase (se 4 (by rfl) ⟨124128, by rfl⟩ : syracuseStep 1324037 = 248257) (by norm_num)
theorem B1324061 : Blo 880569 1324061 := bbase (se 3 (by rfl) ⟨248261, by rfl⟩ : syracuseStep 1324061 = 496523) (by norm_num)
theorem B1487909 : Blo 880569 1487909 := bbase (se 4 (by rfl) ⟨139491, by rfl⟩ : syracuseStep 1487909 = 278983) (by norm_num)
theorem B1324085 : Blo 880569 1324085 := bbase (se 5 (by rfl) ⟨62066, by rfl⟩ : syracuseStep 1324085 = 124133) (by norm_num)
theorem B1324109 : Blo 880569 1324109 := bbase (se 3 (by rfl) ⟨248270, by rfl⟩ : syracuseStep 1324109 = 496541) (by norm_num)
theorem B1258573 : Blo 880569 1258573 := bbase (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) (by norm_num)
theorem B1324133 : Blo 880569 1324133 := bbase (se 4 (by rfl) ⟨124137, by rfl⟩ : syracuseStep 1324133 = 248275) (by norm_num)
theorem B1324157 : Blo 880569 1324157 := bbase (se 3 (by rfl) ⟨248279, by rfl⟩ : syracuseStep 1324157 = 496559) (by norm_num)
theorem B1324181 : Blo 880569 1324181 := bbase (se 6 (by rfl) ⟨31035, by rfl⟩ : syracuseStep 1324181 = 62071) (by norm_num)
theorem B1488037 : Blo 880569 1488037 := bbase (se 4 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 1488037 = 279007) (by norm_num)
theorem B1324205 : Blo 880569 1324205 := bbase (se 3 (by rfl) ⟨248288, by rfl⟩ : syracuseStep 1324205 = 496577) (by norm_num)
theorem B1324229 : Blo 880569 1324229 := bbase (se 4 (by rfl) ⟨124146, by rfl⟩ : syracuseStep 1324229 = 248293) (by norm_num)
theorem B2831573 : Blo 880569 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B1324253 : Blo 880569 1324253 := bbase (se 3 (by rfl) ⟨248297, by rfl⟩ : syracuseStep 1324253 = 496595) (by norm_num)
theorem B1324277 : Blo 880569 1324277 := bbase (se 5 (by rfl) ⟨62075, by rfl⟩ : syracuseStep 1324277 = 124151) (by norm_num)
theorem B1488125 : Blo 880569 1488125 := bbase (se 3 (by rfl) ⟨279023, by rfl⟩ : syracuseStep 1488125 = 558047) (by norm_num)
theorem B1324301 : Blo 880569 1324301 := bbase (se 3 (by rfl) ⟨248306, by rfl⟩ : syracuseStep 1324301 = 496613) (by norm_num)
theorem B5027093 : Blo 880569 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B1324325 : Blo 880569 1324325 := bbase (se 4 (by rfl) ⟨124155, by rfl⟩ : syracuseStep 1324325 = 248311) (by norm_num)
theorem B1324349 : Blo 880569 1324349 := bbase (se 3 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 1324349 = 496631) (by norm_num)
theorem B1324373 : Blo 880569 1324373 := bbase (se 13 (by rfl) ⟨242, by rfl⟩ : syracuseStep 1324373 = 485) (by norm_num)
theorem B1062229 : Blo 880569 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B1324397 : Blo 880569 1324397 := bbase (se 3 (by rfl) ⟨248324, by rfl⟩ : syracuseStep 1324397 = 496649) (by norm_num)
theorem B1488253 : Blo 880569 1488253 := bbase (se 3 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 1488253 = 558095) (by norm_num)
theorem B1324421 : Blo 880569 1324421 := bbase (se 4 (by rfl) ⟨124164, by rfl⟩ : syracuseStep 1324421 = 248329) (by norm_num)
theorem B1324445 : Blo 880569 1324445 := bbase (se 3 (by rfl) ⟨248333, by rfl⟩ : syracuseStep 1324445 = 496667) (by norm_num)
theorem B1324469 : Blo 880569 1324469 := bbase (se 5 (by rfl) ⟨62084, by rfl⟩ : syracuseStep 1324469 = 124169) (by norm_num)
theorem B1062325 : Blo 880569 1062325 := bbase (se 5 (by rfl) ⟨49796, by rfl⟩ : syracuseStep 1062325 = 99593) (by norm_num)
theorem B1258949 : Blo 880569 1258949 := bbase (se 4 (by rfl) ⟨118026, by rfl⟩ : syracuseStep 1258949 = 236053) (by norm_num)
theorem B1324493 : Blo 880569 1324493 := bbase (se 3 (by rfl) ⟨248342, by rfl⟩ : syracuseStep 1324493 = 496685) (by norm_num)
theorem B1488341 : Blo 880569 1488341 := bbase (se 7 (by rfl) ⟨17441, by rfl⟩ : syracuseStep 1488341 = 34883) (by norm_num)
theorem B1324517 : Blo 880569 1324517 := bbase (se 4 (by rfl) ⟨124173, by rfl⟩ : syracuseStep 1324517 = 248347) (by norm_num)
theorem B1324541 : Blo 880569 1324541 := bbase (se 3 (by rfl) ⟨248351, by rfl⟩ : syracuseStep 1324541 = 496703) (by norm_num)
theorem B1324565 : Blo 880569 1324565 := bbase (se 6 (by rfl) ⟨31044, by rfl⟩ : syracuseStep 1324565 = 62089) (by norm_num)
theorem B1324589 : Blo 880569 1324589 := bbase (se 3 (by rfl) ⟨248360, by rfl⟩ : syracuseStep 1324589 = 496721) (by norm_num)
theorem B1324613 : Blo 880569 1324613 := bbase (se 4 (by rfl) ⟨124182, by rfl⟩ : syracuseStep 1324613 = 248365) (by norm_num)
theorem B1488469 : Blo 880569 1488469 := bbase (se 8 (by rfl) ⟨8721, by rfl⟩ : syracuseStep 1488469 = 17443) (by norm_num)
theorem B1324637 : Blo 880569 1324637 := bbase (se 3 (by rfl) ⟨248369, by rfl⟩ : syracuseStep 1324637 = 496739) (by norm_num)
theorem B1881701 : Blo 880569 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B4240997 : Blo 880569 4240997 := bbase (se 4 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 4240997 = 795187) (by norm_num)
theorem B4470389 : Blo 880569 4470389 := bbase (se 5 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 4470389 = 419099) (by norm_num)
theorem B1324661 : Blo 880569 1324661 := bbase (se 5 (by rfl) ⟨62093, by rfl⟩ : syracuseStep 1324661 = 124187) (by norm_num)
theorem B1324685 : Blo 880569 1324685 := bbase (se 3 (by rfl) ⟨248378, by rfl⟩ : syracuseStep 1324685 = 496757) (by norm_num)
theorem B1324709 : Blo 880569 1324709 := bbase (se 4 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 1324709 = 248383) (by norm_num)
theorem B1488557 : Blo 880569 1488557 := bbase (se 3 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 1488557 = 558209) (by norm_num)
theorem B1324733 : Blo 880569 1324733 := bbase (se 3 (by rfl) ⟨248387, by rfl⟩ : syracuseStep 1324733 = 496775) (by norm_num)
theorem B1324757 : Blo 880569 1324757 := bbase (se 7 (by rfl) ⟨15524, by rfl⟩ : syracuseStep 1324757 = 31049) (by norm_num)
theorem B1324781 : Blo 880569 1324781 := bbase (se 3 (by rfl) ⟨248396, by rfl⟩ : syracuseStep 1324781 = 496793) (by norm_num)
theorem B1324805 : Blo 880569 1324805 := bbase (se 4 (by rfl) ⟨124200, by rfl⟩ : syracuseStep 1324805 = 248401) (by norm_num)
theorem B3356437 : Blo 880569 3356437 := bbase (se 6 (by rfl) ⟨78666, by rfl⟩ : syracuseStep 3356437 = 157333) (by norm_num)
theorem B1324829 : Blo 880569 1324829 := bbase (se 3 (by rfl) ⟨248405, by rfl⟩ : syracuseStep 1324829 = 496811) (by norm_num)
theorem B1488685 : Blo 880569 1488685 := bbase (se 3 (by rfl) ⟨279128, by rfl⟩ : syracuseStep 1488685 = 558257) (by norm_num)
theorem B1324853 : Blo 880569 1324853 := bbase (se 5 (by rfl) ⟨62102, by rfl⟩ : syracuseStep 1324853 = 124205) (by norm_num)
theorem B1324877 : Blo 880569 1324877 := bbase (se 3 (by rfl) ⟨248414, by rfl⟩ : syracuseStep 1324877 = 496829) (by norm_num)
theorem B1718101 : Blo 880569 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B1324901 : Blo 880569 1324901 := bbase (se 4 (by rfl) ⟨124209, by rfl⟩ : syracuseStep 1324901 = 248419) (by norm_num)
theorem B1324925 : Blo 880569 1324925 := bbase (se 3 (by rfl) ⟨248423, by rfl⟩ : syracuseStep 1324925 = 496847) (by norm_num)
theorem B1488773 : Blo 880569 1488773 := bbase (se 4 (by rfl) ⟨139572, by rfl⟩ : syracuseStep 1488773 = 279145) (by norm_num)
theorem B1324949 : Blo 880569 1324949 := bbase (se 6 (by rfl) ⟨31053, by rfl⟩ : syracuseStep 1324949 = 62107) (by norm_num)
theorem B1587109 : Blo 880569 1587109 := bbase (se 4 (by rfl) ⟨148791, by rfl⟩ : syracuseStep 1587109 = 297583) (by norm_num)
theorem B1324973 : Blo 880569 1324973 := bbase (se 3 (by rfl) ⟨248432, by rfl⟩ : syracuseStep 1324973 = 496865) (by norm_num)
theorem B1324997 : Blo 880569 1324997 := bbase (se 4 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 1324997 = 248437) (by norm_num)
theorem B1325021 : Blo 880569 1325021 := bbase (se 3 (by rfl) ⟨248441, by rfl⟩ : syracuseStep 1325021 = 496883) (by norm_num)
theorem B1325045 : Blo 880569 1325045 := bbase (se 5 (by rfl) ⟨62111, by rfl⟩ : syracuseStep 1325045 = 124223) (by norm_num)
theorem B1488901 : Blo 880569 1488901 := bbase (se 4 (by rfl) ⟨139584, by rfl⟩ : syracuseStep 1488901 = 279169) (by norm_num)
theorem B1325069 : Blo 880569 1325069 := bbase (se 3 (by rfl) ⟨248450, by rfl⟩ : syracuseStep 1325069 = 496901) (by norm_num)
theorem B1325093 : Blo 880569 1325093 := bbase (se 4 (by rfl) ⟨124227, by rfl⟩ : syracuseStep 1325093 = 248455) (by norm_num)
theorem B1325117 : Blo 880569 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B3356741 : Blo 880569 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B1325141 : Blo 880569 1325141 := bbase (se 8 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 1325141 = 15529) (by norm_num)
theorem B1488989 : Blo 880569 1488989 := bbase (se 3 (by rfl) ⟨279185, by rfl⟩ : syracuseStep 1488989 = 558371) (by norm_num)
theorem B1325165 : Blo 880569 1325165 := bbase (se 3 (by rfl) ⟨248468, by rfl⟩ : syracuseStep 1325165 = 496937) (by norm_num)
theorem B1325189 : Blo 880569 1325189 := bbase (se 4 (by rfl) ⟨124236, by rfl⟩ : syracuseStep 1325189 = 248473) (by norm_num)
theorem B1325213 : Blo 880569 1325213 := bbase (se 3 (by rfl) ⟨248477, by rfl⟩ : syracuseStep 1325213 = 496955) (by norm_num)
theorem B1325237 : Blo 880569 1325237 := bbase (se 5 (by rfl) ⟨62120, by rfl⟩ : syracuseStep 1325237 = 124241) (by norm_num)
theorem B1325261 : Blo 880569 1325261 := bbase (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) (by norm_num)
theorem B1489117 : Blo 880569 1489117 := bbase (se 3 (by rfl) ⟨279209, by rfl⟩ : syracuseStep 1489117 = 558419) (by norm_num)
theorem B1325285 : Blo 880569 1325285 := bbase (se 4 (by rfl) ⟨124245, by rfl⟩ : syracuseStep 1325285 = 248491) (by norm_num)
theorem B1325309 : Blo 880569 1325309 := bbase (se 3 (by rfl) ⟨248495, by rfl⟩ : syracuseStep 1325309 = 496991) (by norm_num)
theorem B2177285 : Blo 880569 2177285 := bbase (se 4 (by rfl) ⟨204120, by rfl⟩ : syracuseStep 2177285 = 408241) (by norm_num)
theorem B1325333 : Blo 880569 1325333 := bbase (se 6 (by rfl) ⟨31062, by rfl⟩ : syracuseStep 1325333 = 62125) (by norm_num)
theorem B2832661 : Blo 880569 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B1325357 : Blo 880569 1325357 := bbase (se 3 (by rfl) ⟨248504, by rfl⟩ : syracuseStep 1325357 = 497009) (by norm_num)
theorem B1489205 : Blo 880569 1489205 := bbase (se 5 (by rfl) ⟨69806, by rfl⟩ : syracuseStep 1489205 = 139613) (by norm_num)
theorem B1325381 : Blo 880569 1325381 := bbase (se 4 (by rfl) ⟨124254, by rfl⟩ : syracuseStep 1325381 = 248509) (by norm_num)
theorem B1882453 : Blo 880569 1882453 := bbase (se 10 (by rfl) ⟨2757, by rfl⟩ : syracuseStep 1882453 = 5515) (by norm_num)
theorem B1325405 : Blo 880569 1325405 := bbase (se 3 (by rfl) ⟨248513, by rfl⟩ : syracuseStep 1325405 = 497027) (by norm_num)
theorem B1325429 : Blo 880569 1325429 := bbase (se 5 (by rfl) ⟨62129, by rfl⟩ : syracuseStep 1325429 = 124259) (by norm_num)
theorem B1325453 : Blo 880569 1325453 := bbase (se 3 (by rfl) ⟨248522, by rfl⟩ : syracuseStep 1325453 = 497045) (by norm_num)
theorem B1325477 : Blo 880569 1325477 := bbase (se 4 (by rfl) ⟨124263, by rfl⟩ : syracuseStep 1325477 = 248527) (by norm_num)
theorem B1489333 : Blo 880569 1489333 := bbase (se 5 (by rfl) ⟨69812, by rfl⟩ : syracuseStep 1489333 = 139625) (by norm_num)
theorem B5028277 : Blo 880569 5028277 := bbase (se 5 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 5028277 = 471401) (by norm_num)
theorem B1325501 : Blo 880569 1325501 := bbase (se 3 (by rfl) ⟨248531, by rfl⟩ : syracuseStep 1325501 = 497063) (by norm_num)
theorem B1325525 : Blo 880569 1325525 := bbase (se 7 (by rfl) ⟨15533, by rfl⟩ : syracuseStep 1325525 = 31067) (by norm_num)
theorem B1882597 : Blo 880569 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B1325549 : Blo 880569 1325549 := bbase (se 3 (by rfl) ⟨248540, by rfl⟩ : syracuseStep 1325549 = 497081) (by norm_num)
theorem B6699509 : Blo 880569 6699509 := bbase (se 5 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 6699509 = 628079) (by norm_num)
theorem B1325573 : Blo 880569 1325573 := bbase (se 4 (by rfl) ⟨124272, by rfl⟩ : syracuseStep 1325573 = 248545) (by norm_num)
theorem B1489421 : Blo 880569 1489421 := bbase (se 3 (by rfl) ⟨279266, by rfl⟩ : syracuseStep 1489421 = 558533) (by norm_num)
theorem B1325597 : Blo 880569 1325597 := bbase (se 3 (by rfl) ⟨248549, by rfl⟩ : syracuseStep 1325597 = 497099) (by norm_num)
theorem B1325621 : Blo 880569 1325621 := bbase (se 5 (by rfl) ⟨62138, by rfl⟩ : syracuseStep 1325621 = 124277) (by norm_num)
theorem B1325645 : Blo 880569 1325645 := bbase (se 3 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 1325645 = 497117) (by norm_num)
theorem B1325669 : Blo 880569 1325669 := bbase (se 4 (by rfl) ⟨124281, by rfl⟩ : syracuseStep 1325669 = 248563) (by norm_num)
theorem B1325693 : Blo 880569 1325693 := bbase (se 3 (by rfl) ⟨248567, by rfl⟩ : syracuseStep 1325693 = 497135) (by norm_num)
theorem B1489549 : Blo 880569 1489549 := bbase (se 3 (by rfl) ⟨279290, by rfl⟩ : syracuseStep 1489549 = 558581) (by norm_num)
theorem B1325717 : Blo 880569 1325717 := bbase (se 6 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 1325717 = 62143) (by norm_num)
theorem B1325741 : Blo 880569 1325741 := bbase (se 3 (by rfl) ⟨248576, by rfl⟩ : syracuseStep 1325741 = 497153) (by norm_num)
theorem B1325765 : Blo 880569 1325765 := bbase (se 4 (by rfl) ⟨124290, by rfl⟩ : syracuseStep 1325765 = 248581) (by norm_num)
theorem B1587917 : Blo 880569 1587917 := bbase (se 3 (by rfl) ⟨297734, by rfl⟩ : syracuseStep 1587917 = 595469) (by norm_num)
theorem B1325789 : Blo 880569 1325789 := bbase (se 3 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 1325789 = 497171) (by norm_num)
theorem B1489637 : Blo 880569 1489637 := bbase (se 4 (by rfl) ⟨139653, by rfl⟩ : syracuseStep 1489637 = 279307) (by norm_num)
theorem B1325813 : Blo 880569 1325813 := bbase (se 5 (by rfl) ⟨62147, by rfl⟩ : syracuseStep 1325813 = 124295) (by norm_num)
theorem B1325837 : Blo 880569 1325837 := bbase (se 3 (by rfl) ⟨248594, by rfl⟩ : syracuseStep 1325837 = 497189) (by norm_num)
theorem B1325861 : Blo 880569 1325861 := bbase (se 4 (by rfl) ⟨124299, by rfl⟩ : syracuseStep 1325861 = 248599) (by norm_num)
theorem B1325885 : Blo 880569 1325885 := bbase (se 3 (by rfl) ⟨248603, by rfl⟩ : syracuseStep 1325885 = 497207) (by norm_num)
theorem B1325909 : Blo 880569 1325909 := bbase (se 9 (by rfl) ⟨3884, by rfl⟩ : syracuseStep 1325909 = 7769) (by norm_num)
theorem B1882973 : Blo 880569 1882973 := bbase (se 3 (by rfl) ⟨353057, by rfl⟩ : syracuseStep 1882973 = 706115) (by norm_num)
theorem B1489765 : Blo 880569 1489765 := bbase (se 4 (by rfl) ⟨139665, by rfl⟩ : syracuseStep 1489765 = 279331) (by norm_num)
theorem B1325933 : Blo 880569 1325933 := bbase (se 3 (by rfl) ⟨248612, by rfl⟩ : syracuseStep 1325933 = 497225) (by norm_num)
theorem B4471685 : Blo 880569 4471685 := bbase (se 4 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 4471685 = 838441) (by norm_num)
theorem B1325957 : Blo 880569 1325957 := bbase (se 4 (by rfl) ⟨124308, by rfl⟩ : syracuseStep 1325957 = 248617) (by norm_num)
theorem B1325981 : Blo 880569 1325981 := bbase (se 3 (by rfl) ⟨248621, by rfl⟩ : syracuseStep 1325981 = 497243) (by norm_num)
theorem B1981349 : Blo 880569 1981349 := bbase (se 4 (by rfl) ⟨185751, by rfl⟩ : syracuseStep 1981349 = 371503) (by norm_num)
theorem B1326005 : Blo 880569 1326005 := bbase (se 5 (by rfl) ⟨62156, by rfl⟩ : syracuseStep 1326005 = 124313) (by norm_num)
theorem B1489853 : Blo 880569 1489853 := bbase (se 3 (by rfl) ⟨279347, by rfl⟩ : syracuseStep 1489853 = 558695) (by norm_num)
theorem B1326029 : Blo 880569 1326029 := bbase (se 3 (by rfl) ⟨248630, by rfl⟩ : syracuseStep 1326029 = 497261) (by norm_num)
theorem B1326053 : Blo 880569 1326053 := bbase (se 4 (by rfl) ⟨124317, by rfl⟩ : syracuseStep 1326053 = 248635) (by norm_num)
theorem B1981421 : Blo 880569 1981421 := bbase (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) (by norm_num)
theorem B1326077 : Blo 880569 1326077 := bbase (se 3 (by rfl) ⟨248639, by rfl⟩ : syracuseStep 1326077 = 497279) (by norm_num)
theorem B1326101 : Blo 880569 1326101 := bbase (se 6 (by rfl) ⟨31080, by rfl⟩ : syracuseStep 1326101 = 62161) (by norm_num)
theorem B1326125 : Blo 880569 1326125 := bbase (se 3 (by rfl) ⟨248648, by rfl⟩ : syracuseStep 1326125 = 497297) (by norm_num)
theorem B1981493 : Blo 880569 1981493 := bbase (se 5 (by rfl) ⟨92882, by rfl⟩ : syracuseStep 1981493 = 185765) (by norm_num)
theorem B1489981 : Blo 880569 1489981 := bbase (se 3 (by rfl) ⟨279371, by rfl⟩ : syracuseStep 1489981 = 558743) (by norm_num)
theorem B1326149 : Blo 880569 1326149 := bbase (se 4 (by rfl) ⟨124326, by rfl⟩ : syracuseStep 1326149 = 248653) (by norm_num)
theorem B1326173 : Blo 880569 1326173 := bbase (se 3 (by rfl) ⟨248657, by rfl⟩ : syracuseStep 1326173 = 497315) (by norm_num)
theorem B1326197 : Blo 880569 1326197 := bbase (se 5 (by rfl) ⟨62165, by rfl⟩ : syracuseStep 1326197 = 124331) (by norm_num)
theorem B1981565 : Blo 880569 1981565 := bbase (se 3 (by rfl) ⟨371543, by rfl⟩ : syracuseStep 1981565 = 743087) (by norm_num)
theorem B1326221 : Blo 880569 1326221 := bbase (se 3 (by rfl) ⟨248666, by rfl⟩ : syracuseStep 1326221 = 497333) (by norm_num)
theorem B1490069 : Blo 880569 1490069 := bbase (se 6 (by rfl) ⟨34923, by rfl⟩ : syracuseStep 1490069 = 69847) (by norm_num)
theorem B1326245 : Blo 880569 1326245 := bbase (se 4 (by rfl) ⟨124335, by rfl⟩ : syracuseStep 1326245 = 248671) (by norm_num)
theorem B1326269 : Blo 880569 1326269 := bbase (se 3 (by rfl) ⟨248675, by rfl⟩ : syracuseStep 1326269 = 497351) (by norm_num)
theorem B1981637 : Blo 880569 1981637 := bbase (se 4 (by rfl) ⟨185778, by rfl⟩ : syracuseStep 1981637 = 371557) (by norm_num)
theorem B1883341 : Blo 880569 1883341 := bbase (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) (by norm_num)
theorem B1326293 : Blo 880569 1326293 := bbase (se 7 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 1326293 = 31085) (by norm_num)
theorem B1326317 : Blo 880569 1326317 := bbase (se 3 (by rfl) ⟨248684, by rfl⟩ : syracuseStep 1326317 = 497369) (by norm_num)
theorem B1326341 : Blo 880569 1326341 := bbase (se 4 (by rfl) ⟨124344, by rfl⟩ : syracuseStep 1326341 = 248689) (by norm_num)
theorem B1981709 : Blo 880569 1981709 := bbase (se 3 (by rfl) ⟨371570, by rfl⟩ : syracuseStep 1981709 = 743141) (by norm_num)
theorem B1490197 : Blo 880569 1490197 := bbase (se 6 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 1490197 = 69853) (by norm_num)
theorem B1326365 : Blo 880569 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B1326389 : Blo 880569 1326389 := bbase (se 5 (by rfl) ⟨62174, by rfl⟩ : syracuseStep 1326389 = 124349) (by norm_num)
theorem B1326413 : Blo 880569 1326413 := bbase (se 3 (by rfl) ⟨248702, by rfl⟩ : syracuseStep 1326413 = 497405) (by norm_num)
theorem B1981781 : Blo 880569 1981781 := bbase (se 11 (by rfl) ⟨1451, by rfl⟩ : syracuseStep 1981781 = 2903) (by norm_num)
theorem B1785181 : Blo 880569 1785181 := bbase (se 3 (by rfl) ⟨334721, by rfl⟩ : syracuseStep 1785181 = 669443) (by norm_num)
theorem B1326437 : Blo 880569 1326437 := bbase (se 4 (by rfl) ⟨124353, by rfl⟩ : syracuseStep 1326437 = 248707) (by norm_num)
theorem B1490285 : Blo 880569 1490285 := bbase (se 3 (by rfl) ⟨279428, by rfl⟩ : syracuseStep 1490285 = 558857) (by norm_num)
theorem B1326461 : Blo 880569 1326461 := bbase (se 3 (by rfl) ⟨248711, by rfl⟩ : syracuseStep 1326461 = 497423) (by norm_num)
theorem B1326485 : Blo 880569 1326485 := bbase (se 6 (by rfl) ⟨31089, by rfl⟩ : syracuseStep 1326485 = 62179) (by norm_num)
theorem B1981853 : Blo 880569 1981853 := bbase (se 3 (by rfl) ⟨371597, by rfl⟩ : syracuseStep 1981853 = 743195) (by norm_num)
theorem B1326509 : Blo 880569 1326509 := bbase (se 3 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 1326509 = 497441) (by norm_num)
theorem B1326533 : Blo 880569 1326533 := bbase (se 4 (by rfl) ⟨124362, by rfl⟩ : syracuseStep 1326533 = 248725) (by norm_num)
theorem B4242901 : Blo 880569 4242901 := bbase (se 7 (by rfl) ⟨49721, by rfl⟩ : syracuseStep 4242901 = 99443) (by norm_num)
theorem B1326557 : Blo 880569 1326557 := bbase (se 3 (by rfl) ⟨248729, by rfl⟩ : syracuseStep 1326557 = 497459) (by norm_num)
theorem B1981925 : Blo 880569 1981925 := bbase (se 4 (by rfl) ⟨185805, by rfl⟩ : syracuseStep 1981925 = 371611) (by norm_num)
theorem B4242917 : Blo 880569 4242917 := bbase (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) (by norm_num)
theorem B1490413 : Blo 880569 1490413 := bbase (se 3 (by rfl) ⟨279452, by rfl⟩ : syracuseStep 1490413 = 558905) (by norm_num)
theorem B1326581 : Blo 880569 1326581 := bbase (se 5 (by rfl) ⟨62183, by rfl⟩ : syracuseStep 1326581 = 124367) (by norm_num)
theorem B1326605 : Blo 880569 1326605 := bbase (se 3 (by rfl) ⟨248738, by rfl⟩ : syracuseStep 1326605 = 497477) (by norm_num)
theorem B1326629 : Blo 880569 1326629 := bbase (se 4 (by rfl) ⟨124371, by rfl⟩ : syracuseStep 1326629 = 248743) (by norm_num)
theorem B1981997 : Blo 880569 1981997 := bbase (se 3 (by rfl) ⟨371624, by rfl⟩ : syracuseStep 1981997 = 743249) (by norm_num)
theorem B1326653 : Blo 880569 1326653 := bbase (se 3 (by rfl) ⟨248747, by rfl⟩ : syracuseStep 1326653 = 497495) (by norm_num)
theorem B1490501 : Blo 880569 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B2014789 : Blo 880569 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B1326677 : Blo 880569 1326677 := bbase (se 8 (by rfl) ⟨7773, by rfl⟩ : syracuseStep 1326677 = 15547) (by norm_num)
theorem B1326701 : Blo 880569 1326701 := bbase (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) (by norm_num)
theorem B1982069 : Blo 880569 1982069 := bbase (se 5 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 1982069 = 185819) (by norm_num)
theorem B1326725 : Blo 880569 1326725 := bbase (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) (by norm_num)
theorem B1326749 : Blo 880569 1326749 := bbase (se 3 (by rfl) ⟨248765, by rfl⟩ : syracuseStep 1326749 = 497531) (by norm_num)
theorem B1719973 : Blo 880569 1719973 := bbase (se 4 (by rfl) ⟨161247, by rfl⟩ : syracuseStep 1719973 = 322495) (by norm_num)
theorem B1326773 : Blo 880569 1326773 := bbase (se 5 (by rfl) ⟨62192, by rfl⟩ : syracuseStep 1326773 = 124385) (by norm_num)
theorem B1982141 : Blo 880569 1982141 := bbase (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) (by norm_num)
theorem B1490629 : Blo 880569 1490629 := bbase (se 4 (by rfl) ⟨139746, by rfl⟩ : syracuseStep 1490629 = 279493) (by norm_num)
theorem B1326797 : Blo 880569 1326797 := bbase (se 3 (by rfl) ⟨248774, by rfl⟩ : syracuseStep 1326797 = 497549) (by norm_num)
theorem B1326821 : Blo 880569 1326821 := bbase (se 4 (by rfl) ⟨124389, by rfl⟩ : syracuseStep 1326821 = 248779) (by norm_num)
theorem B1326845 : Blo 880569 1326845 := bbase (se 3 (by rfl) ⟨248783, by rfl⟩ : syracuseStep 1326845 = 497567) (by norm_num)
theorem B1982213 : Blo 880569 1982213 := bbase (se 4 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 1982213 = 371665) (by norm_num)
theorem B1490717 : Blo 880569 1490717 := bbase (se 3 (by rfl) ⟨279509, by rfl⟩ : syracuseStep 1490717 = 559019) (by norm_num)
theorem B1982285 : Blo 880569 1982285 := bbase (se 3 (by rfl) ⟨371678, by rfl⟩ : syracuseStep 1982285 = 743357) (by norm_num)
theorem B1785701 : Blo 880569 1785701 := bbase (se 4 (by rfl) ⟨167409, by rfl⟩ : syracuseStep 1785701 = 334819) (by norm_num)
theorem B1982357 : Blo 880569 1982357 := bbase (se 6 (by rfl) ⟨46461, by rfl⟩ : syracuseStep 1982357 = 92923) (by norm_num)
theorem B1490845 : Blo 880569 1490845 := bbase (se 3 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 1490845 = 559067) (by norm_num)
theorem B3391397 : Blo 880569 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B2015189 : Blo 880569 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B1982429 : Blo 880569 1982429 := bbase (se 3 (by rfl) ⟨371705, by rfl⟩ : syracuseStep 1982429 = 743411) (by norm_num)
theorem B1490933 : Blo 880569 1490933 := bbase (se 5 (by rfl) ⟨69887, by rfl⟩ : syracuseStep 1490933 = 139775) (by norm_num)
theorem B1982501 : Blo 880569 1982501 := bbase (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) (by norm_num)
theorem B1982573 : Blo 880569 1982573 := bbase (se 3 (by rfl) ⟨371732, by rfl⟩ : syracuseStep 1982573 = 743465) (by norm_num)
theorem B1491061 : Blo 880569 1491061 := bbase (se 5 (by rfl) ⟨69893, by rfl⟩ : syracuseStep 1491061 = 139787) (by norm_num)
theorem B4472981 : Blo 880569 4472981 := bbase (se 6 (by rfl) ⟨104835, by rfl⟩ : syracuseStep 4472981 = 209671) (by norm_num)
theorem B1982645 : Blo 880569 1982645 := bbase (se 5 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 1982645 = 185873) (by norm_num)
theorem B1491149 : Blo 880569 1491149 := bbase (se 3 (by rfl) ⟨279590, by rfl⟩ : syracuseStep 1491149 = 559181) (by norm_num)
theorem B1982717 : Blo 880569 1982717 := bbase (se 3 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 1982717 = 743519) (by norm_num)
theorem B1982789 : Blo 880569 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B4538693 : Blo 880569 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B1491277 : Blo 880569 1491277 := bbase (se 3 (by rfl) ⟨279614, by rfl⟩ : syracuseStep 1491277 = 559229) (by norm_num)
theorem B5030261 : Blo 880569 5030261 := bbase (se 5 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 5030261 = 471587) (by norm_num)
theorem B1982861 : Blo 880569 1982861 := bbase (se 3 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 1982861 = 743573) (by norm_num)
theorem B1589653 : Blo 880569 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B1130917 : Blo 880569 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B1491365 : Blo 880569 1491365 := bbase (se 4 (by rfl) ⟨139815, by rfl⟩ : syracuseStep 1491365 = 279631) (by norm_num)
theorem B1786301 : Blo 880569 1786301 := bbase (se 3 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 1786301 = 669863) (by norm_num)
theorem B1982933 : Blo 880569 1982933 := bbase (se 7 (by rfl) ⟨23237, by rfl⟩ : syracuseStep 1982933 = 46475) (by norm_num)
theorem B1983005 : Blo 880569 1983005 := bbase (se 3 (by rfl) ⟨371813, by rfl⟩ : syracuseStep 1983005 = 743627) (by norm_num)
theorem B1589797 : Blo 880569 1589797 := bbase (se 4 (by rfl) ⟨149043, by rfl⟩ : syracuseStep 1589797 = 298087) (by norm_num)
theorem B1491493 : Blo 880569 1491493 := bbase (se 4 (by rfl) ⟨139827, by rfl⟩ : syracuseStep 1491493 = 279655) (by norm_num)
theorem B1983077 : Blo 880569 1983077 := bbase (se 4 (by rfl) ⟨185913, by rfl⟩ : syracuseStep 1983077 = 371827) (by norm_num)
theorem B1491581 : Blo 880569 1491581 := bbase (se 3 (by rfl) ⟨279671, by rfl⟩ : syracuseStep 1491581 = 559343) (by norm_num)
theorem B1983149 : Blo 880569 1983149 := bbase (se 3 (by rfl) ⟨371840, by rfl⟩ : syracuseStep 1983149 = 743681) (by norm_num)
theorem B1884845 : Blo 880569 1884845 := bbase (se 3 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 1884845 = 706817) (by norm_num)
theorem B1983221 : Blo 880569 1983221 := bbase (se 5 (by rfl) ⟨92963, by rfl⟩ : syracuseStep 1983221 = 185927) (by norm_num)
theorem B1491709 : Blo 880569 1491709 := bbase (se 3 (by rfl) ⟨279695, by rfl⟩ : syracuseStep 1491709 = 559391) (by norm_num)
theorem B2016029 : Blo 880569 2016029 := bbase (se 3 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 2016029 = 756011) (by norm_num)
theorem B1983293 : Blo 880569 1983293 := bbase (se 3 (by rfl) ⟨371867, by rfl⟩ : syracuseStep 1983293 = 743735) (by norm_num)
theorem B1884989 : Blo 880569 1884989 := bbase (se 3 (by rfl) ⟨353435, by rfl⟩ : syracuseStep 1884989 = 706871) (by norm_num)
theorem B1491797 : Blo 880569 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B1983365 : Blo 880569 1983365 := bbase (se 4 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 1983365 = 371881) (by norm_num)
theorem B2507669 : Blo 880569 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B1983437 : Blo 880569 1983437 := bbase (se 3 (by rfl) ⟨371894, by rfl⟩ : syracuseStep 1983437 = 743789) (by norm_num)
theorem B1491925 : Blo 880569 1491925 := bbase (se 7 (by rfl) ⟨17483, by rfl⟩ : syracuseStep 1491925 = 34967) (by norm_num)
theorem B1983509 : Blo 880569 1983509 := bbase (se 6 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 1983509 = 92977) (by norm_num)
theorem B1492013 : Blo 880569 1492013 := bbase (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) (by norm_num)
theorem B1983581 : Blo 880569 1983581 := bbase (se 3 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 1983581 = 743843) (by norm_num)
theorem B1983653 : Blo 880569 1983653 := bbase (se 4 (by rfl) ⟨185967, by rfl⟩ : syracuseStep 1983653 = 371935) (by norm_num)
theorem B1885349 : Blo 880569 1885349 := bbase (se 4 (by rfl) ⟨176751, by rfl⟩ : syracuseStep 1885349 = 353503) (by norm_num)
theorem B1492141 : Blo 880569 1492141 := bbase (se 3 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 1492141 = 559553) (by norm_num)
theorem B1983725 : Blo 880569 1983725 := bbase (se 3 (by rfl) ⟨371948, by rfl⟩ : syracuseStep 1983725 = 743897) (by norm_num)
theorem B1492229 : Blo 880569 1492229 := bbase (se 4 (by rfl) ⟨139896, by rfl⟩ : syracuseStep 1492229 = 279793) (by norm_num)
theorem B1361197 : Blo 880569 1361197 := bbase (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) (by norm_num)
theorem B1983797 : Blo 880569 1983797 := bbase (se 5 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 1983797 = 185981) (by norm_num)
theorem B3818821 : Blo 880569 3818821 := bbase (se 4 (by rfl) ⟨358014, by rfl⟩ : syracuseStep 3818821 = 716029) (by norm_num)
theorem B1983869 : Blo 880569 1983869 := bbase (se 3 (by rfl) ⟨371975, by rfl⟩ : syracuseStep 1983869 = 743951) (by norm_num)
theorem B1492357 : Blo 880569 1492357 := bbase (se 4 (by rfl) ⟨139908, by rfl⟩ : syracuseStep 1492357 = 279817) (by norm_num)
theorem B4474277 : Blo 880569 4474277 := bbase (se 4 (by rfl) ⟨419463, by rfl⟩ : syracuseStep 4474277 = 838927) (by norm_num)
theorem B1983941 : Blo 880569 1983941 := bbase (se 4 (by rfl) ⟨185994, by rfl⟩ : syracuseStep 1983941 = 371989) (by norm_num)
theorem B1131985 : Blo 880569 1131985 := bbase (se 2 (by rfl) ⟨424494, by rfl⟩ : syracuseStep 1131985 = 848989) (by norm_num)
theorem B1590749 : Blo 880569 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1492445 : Blo 880569 1492445 := bbase (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) (by norm_num)
theorem B1984013 : Blo 880569 1984013 := bbase (se 3 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 1984013 = 744005) (by norm_num)
theorem B1590821 : Blo 880569 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B1984085 : Blo 880569 1984085 := bbase (se 8 (by rfl) ⟨11625, by rfl⟩ : syracuseStep 1984085 = 23251) (by norm_num)
theorem B1492573 : Blo 880569 1492573 := bbase (se 3 (by rfl) ⟨279857, by rfl⟩ : syracuseStep 1492573 = 559715) (by norm_num)
theorem B2508421 : Blo 880569 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B1984157 : Blo 880569 1984157 := bbase (se 3 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 1984157 = 744059) (by norm_num)
theorem B1492661 : Blo 880569 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B1984229 : Blo 880569 1984229 := bbase (se 4 (by rfl) ⟨186021, by rfl⟩ : syracuseStep 1984229 = 372043) (by norm_num)
theorem B1361693 : Blo 880569 1361693 := bbase (se 3 (by rfl) ⟨255317, by rfl⟩ : syracuseStep 1361693 = 510635) (by norm_num)
theorem B1984301 : Blo 880569 1984301 := bbase (se 3 (by rfl) ⟨372056, by rfl⟩ : syracuseStep 1984301 = 744113) (by norm_num)
theorem B4245301 : Blo 880569 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B1984373 : Blo 880569 1984373 := bbase (se 5 (by rfl) ⟨93017, by rfl⟩ : syracuseStep 1984373 = 186035) (by norm_num)
theorem B1984445 : Blo 880569 1984445 := bbase (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) (by norm_num)
theorem B1984517 : Blo 880569 1984517 := bbase (se 4 (by rfl) ⟨186048, by rfl⟩ : syracuseStep 1984517 = 372097) (by norm_num)
theorem B1886237 : Blo 880569 1886237 := bbase (se 3 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 1886237 = 707339) (by norm_num)
theorem B1984589 : Blo 880569 1984589 := bbase (se 3 (by rfl) ⟨372110, by rfl⟩ : syracuseStep 1984589 = 744221) (by norm_num)
theorem B1984661 : Blo 880569 1984661 := bbase (se 6 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 1984661 = 93031) (by norm_num)
theorem B1984733 : Blo 880569 1984733 := bbase (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) (by norm_num)
theorem B1886485 : Blo 880569 1886485 := bbase (se 6 (by rfl) ⟨44214, by rfl⟩ : syracuseStep 1886485 = 88429) (by norm_num)
theorem B1984805 : Blo 880569 1984805 := bbase (se 4 (by rfl) ⟨186075, by rfl⟩ : syracuseStep 1984805 = 372151) (by norm_num)
theorem B8472917 : Blo 880569 8472917 := bbase (se 10 (by rfl) ⟨12411, by rfl⟩ : syracuseStep 8472917 = 24823) (by norm_num)
theorem B1984877 : Blo 880569 1984877 := bbase (se 3 (by rfl) ⟨372164, by rfl⟩ : syracuseStep 1984877 = 744329) (by norm_num)
theorem B1984949 : Blo 880569 1984949 := bbase (se 5 (by rfl) ⟨93044, by rfl⟩ : syracuseStep 1984949 = 186089) (by norm_num)
theorem B1985021 : Blo 880569 1985021 := bbase (se 3 (by rfl) ⟨372191, by rfl⟩ : syracuseStep 1985021 = 744383) (by norm_num)
theorem B5032469 : Blo 880569 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B2542117 : Blo 880569 2542117 := bbase (se 4 (by rfl) ⟨238323, by rfl⟩ : syracuseStep 2542117 = 476647) (by norm_num)
theorem B2148925 : Blo 880569 2148925 := bbase (se 3 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 2148925 = 805847) (by norm_num)
theorem B1985093 : Blo 880569 1985093 := bbase (se 4 (by rfl) ⟨186102, by rfl⟩ : syracuseStep 1985093 = 372205) (by norm_num)
theorem B1985165 : Blo 880569 1985165 := bbase (se 3 (by rfl) ⟨372218, by rfl⟩ : syracuseStep 1985165 = 744437) (by norm_num)
theorem B4475573 : Blo 880569 4475573 := bbase (se 5 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 4475573 = 419585) (by norm_num)
theorem B1985237 : Blo 880569 1985237 := bbase (se 7 (by rfl) ⟨23264, by rfl⟩ : syracuseStep 1985237 = 46529) (by norm_num)
theorem B1723141 : Blo 880569 1723141 := bbase (se 4 (by rfl) ⟨161544, by rfl⟩ : syracuseStep 1723141 = 323089) (by norm_num)
theorem B1886989 : Blo 880569 1886989 := bbase (se 3 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 1886989 = 707621) (by norm_num)
theorem B1985309 : Blo 880569 1985309 := bbase (se 3 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 1985309 = 744491) (by norm_num)
theorem B1985381 : Blo 880569 1985381 := bbase (se 4 (by rfl) ⟨186129, by rfl⟩ : syracuseStep 1985381 = 372259) (by norm_num)
theorem B1985453 : Blo 880569 1985453 := bbase (se 3 (by rfl) ⟨372272, by rfl⟩ : syracuseStep 1985453 = 744545) (by norm_num)
theorem B1985525 : Blo 880569 1985525 := bbase (se 5 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 1985525 = 186143) (by norm_num)
theorem B1985597 : Blo 880569 1985597 := bbase (se 3 (by rfl) ⟨372299, by rfl⟩ : syracuseStep 1985597 = 744599) (by norm_num)
theorem B1985669 : Blo 880569 1985669 := bbase (se 4 (by rfl) ⟨186156, by rfl⟩ : syracuseStep 1985669 = 372313) (by norm_num)
theorem B1985741 : Blo 880569 1985741 := bbase (se 3 (by rfl) ⟨372326, by rfl⟩ : syracuseStep 1985741 = 744653) (by norm_num)
theorem B1363213 : Blo 880569 1363213 := bbase (se 3 (by rfl) ⟨255602, by rfl⟩ : syracuseStep 1363213 = 511205) (by norm_num)
theorem B1985813 : Blo 880569 1985813 := bbase (se 6 (by rfl) ⟨46542, by rfl⟩ : syracuseStep 1985813 = 93085) (by norm_num)
theorem B1985885 : Blo 880569 1985885 := bbase (se 3 (by rfl) ⟨372353, by rfl⟩ : syracuseStep 1985885 = 744707) (by norm_num)
theorem B1789285 : Blo 880569 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B1985957 : Blo 880569 1985957 := bbase (se 4 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 1985957 = 372367) (by norm_num)
theorem B2870741 : Blo 880569 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B1986029 : Blo 880569 1986029 := bbase (se 3 (by rfl) ⟨372380, by rfl⟩ : syracuseStep 1986029 = 744761) (by norm_num)
theorem B1986101 : Blo 880569 1986101 := bbase (se 5 (by rfl) ⟨93098, by rfl⟩ : syracuseStep 1986101 = 186197) (by norm_num)
theorem B3624533 : Blo 880569 3624533 := bbase (se 8 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 3624533 = 42475) (by norm_num)
theorem B1986173 : Blo 880569 1986173 := bbase (se 3 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 1986173 = 744815) (by norm_num)
theorem B1887877 : Blo 880569 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B2117269 : Blo 880569 2117269 := bbase (se 6 (by rfl) ⟨49623, by rfl⟩ : syracuseStep 2117269 = 99247) (by norm_num)
theorem B1986245 : Blo 880569 1986245 := bbase (se 4 (by rfl) ⟨186210, by rfl⟩ : syracuseStep 1986245 = 372421) (by norm_num)
theorem B1986317 : Blo 880569 1986317 := bbase (se 3 (by rfl) ⟨372434, by rfl⟩ : syracuseStep 1986317 = 744869) (by norm_num)
theorem B1986389 : Blo 880569 1986389 := bbase (se 9 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 1986389 = 11639) (by norm_num)
theorem B1986461 : Blo 880569 1986461 := bbase (se 3 (by rfl) ⟨372461, by rfl⟩ : syracuseStep 1986461 = 744923) (by norm_num)
theorem B1789885 : Blo 880569 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B4476869 : Blo 880569 4476869 := bbase (se 4 (by rfl) ⟨419706, by rfl⟩ : syracuseStep 4476869 = 839413) (by norm_num)
theorem B1986533 : Blo 880569 1986533 := bbase (se 4 (by rfl) ⟨186237, by rfl⟩ : syracuseStep 1986533 = 372475) (by norm_num)
theorem B1789949 : Blo 880569 1789949 := bbase (se 3 (by rfl) ⟨335615, by rfl⟩ : syracuseStep 1789949 = 671231) (by norm_num)
theorem B7524373 : Blo 880569 7524373 := bbase (se 6 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 7524373 = 352705) (by norm_num)
theorem B1986605 : Blo 880569 1986605 := bbase (se 3 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 1986605 = 744977) (by norm_num)
theorem B5656661 : Blo 880569 5656661 := bbase (se 8 (by rfl) ⟨33144, by rfl⟩ : syracuseStep 5656661 = 66289) (by norm_num)
theorem B1986677 : Blo 880569 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B1888373 : Blo 880569 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B1986749 : Blo 880569 1986749 := bbase (se 3 (by rfl) ⟨372515, by rfl⟩ : syracuseStep 1986749 = 745031) (by norm_num)
theorem B1593589 : Blo 880569 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1986821 : Blo 880569 1986821 := bbase (se 4 (by rfl) ⟨186264, by rfl⟩ : syracuseStep 1986821 = 372529) (by norm_num)
theorem B1986893 : Blo 880569 1986893 := bbase (se 3 (by rfl) ⟨372542, by rfl⟩ : syracuseStep 1986893 = 745085) (by norm_num)
theorem B1986965 : Blo 880569 1986965 := bbase (se 6 (by rfl) ⟨46569, by rfl⟩ : syracuseStep 1986965 = 93139) (by norm_num)
theorem B2511269 : Blo 880569 2511269 := bbase (se 4 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 2511269 = 470863) (by norm_num)
theorem B8049077 : Blo 880569 8049077 := bbase (se 5 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 8049077 = 754601) (by norm_num)
theorem B1987037 : Blo 880569 1987037 := bbase (se 3 (by rfl) ⟨372569, by rfl⟩ : syracuseStep 1987037 = 745139) (by norm_num)
theorem B1987109 : Blo 880569 1987109 := bbase (se 4 (by rfl) ⟨186291, by rfl⟩ : syracuseStep 1987109 = 372583) (by norm_num)
theorem B1987181 : Blo 880569 1987181 := bbase (se 3 (by rfl) ⟨372596, by rfl⟩ : syracuseStep 1987181 = 745193) (by norm_num)
theorem B1987253 : Blo 880569 1987253 := bbase (se 5 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 1987253 = 186305) (by norm_num)
theorem B2577125 : Blo 880569 2577125 := bbase (se 4 (by rfl) ⟨241605, by rfl⟩ : syracuseStep 2577125 = 483211) (by norm_num)
theorem B1987325 : Blo 880569 1987325 := bbase (se 3 (by rfl) ⟨372623, by rfl⟩ : syracuseStep 1987325 = 745247) (by norm_num)
theorem B1987397 : Blo 880569 1987397 := bbase (se 4 (by rfl) ⟨186318, by rfl⟩ : syracuseStep 1987397 = 372637) (by norm_num)
theorem B1004365 : Blo 880569 1004365 := bbase (se 3 (by rfl) ⟨188318, by rfl⟩ : syracuseStep 1004365 = 376637) (by norm_num)
theorem B1987469 : Blo 880569 1987469 := bbase (se 3 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 1987469 = 745301) (by norm_num)
theorem B1987541 : Blo 880569 1987541 := bbase (se 7 (by rfl) ⟨23291, by rfl⟩ : syracuseStep 1987541 = 46583) (by norm_num)
theorem B1004525 : Blo 880569 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B2118653 : Blo 880569 2118653 := bbase (se 3 (by rfl) ⟨397247, by rfl⟩ : syracuseStep 2118653 = 794495) (by norm_num)
theorem B1987613 : Blo 880569 1987613 := bbase (se 3 (by rfl) ⟨372677, by rfl⟩ : syracuseStep 1987613 = 745355) (by norm_num)
theorem B1791013 : Blo 880569 1791013 := bbase (se 4 (by rfl) ⟨167907, by rfl⟩ : syracuseStep 1791013 = 335815) (by norm_num)
theorem B1987685 : Blo 880569 1987685 := bbase (se 4 (by rfl) ⟨186345, by rfl⟩ : syracuseStep 1987685 = 372691) (by norm_num)
theorem B1791085 : Blo 880569 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B1987757 : Blo 880569 1987757 := bbase (se 3 (by rfl) ⟨372704, by rfl⟩ : syracuseStep 1987757 = 745409) (by norm_num)
theorem B2118845 : Blo 880569 2118845 := bbase (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) (by norm_num)
theorem B1987829 : Blo 880569 1987829 := bbase (se 5 (by rfl) ⟨93179, by rfl⟩ : syracuseStep 1987829 = 186359) (by norm_num)
theorem B1987901 : Blo 880569 1987901 := bbase (se 3 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 1987901 = 745463) (by norm_num)
theorem B1987973 : Blo 880569 1987973 := bbase (se 4 (by rfl) ⟨186372, by rfl⟩ : syracuseStep 1987973 = 372745) (by norm_num)
theorem B1988045 : Blo 880569 1988045 := bbase (se 3 (by rfl) ⟨372758, by rfl⟩ : syracuseStep 1988045 = 745517) (by norm_num)
theorem B1529309 : Blo 880569 1529309 := bbase (se 3 (by rfl) ⟨286745, by rfl⟩ : syracuseStep 1529309 = 573491) (by norm_num)
theorem B1988117 : Blo 880569 1988117 := bbase (se 6 (by rfl) ⟨46596, by rfl⟩ : syracuseStep 1988117 = 93193) (by norm_num)
theorem B1791533 : Blo 880569 1791533 := bbase (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) (by norm_num)
theorem B2512453 : Blo 880569 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B4019797 : Blo 880569 4019797 := bbase (se 8 (by rfl) ⟨23553, by rfl⟩ : syracuseStep 4019797 = 47107) (by norm_num)
theorem B1988189 : Blo 880569 1988189 := bbase (se 3 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 1988189 = 745571) (by norm_num)
theorem B4249205 : Blo 880569 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B1988261 : Blo 880569 1988261 := bbase (se 4 (by rfl) ⟨186399, by rfl⟩ : syracuseStep 1988261 = 372799) (by norm_num)
theorem B2512613 : Blo 880569 2512613 := bbase (se 4 (by rfl) ⟨235557, by rfl⟩ : syracuseStep 2512613 = 471115) (by norm_num)
theorem B1988333 : Blo 880569 1988333 := bbase (se 3 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 1988333 = 745625) (by norm_num)
theorem B1988405 : Blo 880569 1988405 := bbase (se 5 (by rfl) ⟨93206, by rfl⟩ : syracuseStep 1988405 = 186413) (by norm_num)
theorem B1988477 : Blo 880569 1988477 := bbase (se 3 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 1988477 = 745679) (by norm_num)
theorem B2119613 : Blo 880569 2119613 := bbase (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) (by norm_num)
theorem B1988549 : Blo 880569 1988549 := bbase (se 4 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 1988549 = 372853) (by norm_num)
theorem B7526357 : Blo 880569 7526357 := bbase (se 7 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 7526357 = 176399) (by norm_num)
theorem B2512853 : Blo 880569 2512853 := bbase (se 7 (by rfl) ⟨29447, by rfl⟩ : syracuseStep 2512853 = 58895) (by norm_num)
theorem B2381797 : Blo 880569 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B1988621 : Blo 880569 1988621 := bbase (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) (by norm_num)
theorem B2414645 : Blo 880569 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B6707285 : Blo 880569 6707285 := bbase (se 8 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 6707285 = 78601) (by norm_num)
theorem B1988693 : Blo 880569 1988693 := bbase (se 8 (by rfl) ⟨11652, by rfl⟩ : syracuseStep 1988693 = 23305) (by norm_num)
theorem B2513045 : Blo 880569 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B1988765 : Blo 880569 1988765 := bbase (se 3 (by rfl) ⟨372893, by rfl⟩ : syracuseStep 1988765 = 745787) (by norm_num)
theorem B1988837 : Blo 880569 1988837 := bbase (se 4 (by rfl) ⟨186453, by rfl⟩ : syracuseStep 1988837 = 372907) (by norm_num)
theorem B1988909 : Blo 880569 1988909 := bbase (se 3 (by rfl) ⟨372920, by rfl⟩ : syracuseStep 1988909 = 745841) (by norm_num)
theorem B1136941 : Blo 880569 1136941 := bbase (se 3 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 1136941 = 426353) (by norm_num)
theorem B940393 : Blo 880569 940393 := bbase (se 2 (by rfl) ⟨352647, by rfl⟩ : syracuseStep 940393 = 705295) (by norm_num)
theorem B1988981 : Blo 880569 1988981 := bbase (se 5 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 1988981 = 186467) (by norm_num)
theorem B11295125 : Blo 880569 11295125 := bbase (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) (by norm_num)
theorem B1989053 : Blo 880569 1989053 := bbase (se 3 (by rfl) ⟨372947, by rfl⟩ : syracuseStep 1989053 = 745895) (by norm_num)
theorem B1989125 : Blo 880569 1989125 := bbase (se 4 (by rfl) ⟨186480, by rfl⟩ : syracuseStep 1989125 = 372961) (by norm_num)
theorem B940577 : Blo 880569 940577 := bbase (se 2 (by rfl) ⟨352716, by rfl⟩ : syracuseStep 940577 = 705433) (by norm_num)
theorem B2972213 : Blo 880569 2972213 := bbase (se 5 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 2972213 = 278645) (by norm_num)
theorem B1989197 : Blo 880569 1989197 := bbase (se 3 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 1989197 = 745949) (by norm_num)
theorem B1989269 : Blo 880569 1989269 := bbase (se 6 (by rfl) ⟨46623, by rfl⟩ : syracuseStep 1989269 = 93247) (by norm_num)
theorem B1989341 : Blo 880569 1989341 := bbase (se 3 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 1989341 = 746003) (by norm_num)
theorem B1989413 : Blo 880569 1989413 := bbase (se 4 (by rfl) ⟨186507, by rfl⟩ : syracuseStep 1989413 = 373015) (by norm_num)
theorem B1989485 : Blo 880569 1989485 := bbase (se 3 (by rfl) ⟨373028, by rfl⟩ : syracuseStep 1989485 = 746057) (by norm_num)
theorem B1792901 : Blo 880569 1792901 := bbase (se 4 (by rfl) ⟨168084, by rfl⟩ : syracuseStep 1792901 = 336169) (by norm_num)
theorem B1989557 : Blo 880569 1989557 := bbase (se 5 (by rfl) ⟨93260, by rfl⟩ : syracuseStep 1989557 = 186521) (by norm_num)
theorem B2972645 : Blo 880569 2972645 := bbase (se 4 (by rfl) ⟨278685, by rfl⟩ : syracuseStep 2972645 = 557371) (by norm_num)
theorem B1989629 : Blo 880569 1989629 := bbase (se 3 (by rfl) ⟨373055, by rfl⟩ : syracuseStep 1989629 = 746111) (by norm_num)
theorem B1989701 : Blo 880569 1989701 := bbase (se 4 (by rfl) ⟨186534, by rfl⟩ : syracuseStep 1989701 = 373069) (by norm_num)
theorem B2514037 : Blo 880569 2514037 := bbase (se 5 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 2514037 = 235691) (by norm_num)
theorem B3398773 : Blo 880569 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B1989773 : Blo 880569 1989773 := bbase (se 3 (by rfl) ⟨373082, by rfl⟩ : syracuseStep 1989773 = 746165) (by norm_num)
theorem B1432733 : Blo 880569 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B1989845 : Blo 880569 1989845 := bbase (se 7 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 1989845 = 46637) (by norm_num)
theorem B941329 : Blo 880569 941329 := bbase (se 2 (by rfl) ⟨352998, by rfl⟩ : syracuseStep 941329 = 705997) (by norm_num)
theorem B1989917 : Blo 880569 1989917 := bbase (se 3 (by rfl) ⟨373109, by rfl⟩ : syracuseStep 1989917 = 746219) (by norm_num)
theorem B41278805 : Blo 880569 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B941401 : Blo 880569 941401 := bbase (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) (by norm_num)
theorem B1531237 : Blo 880569 1531237 := bbase (se 4 (by rfl) ⟨143553, by rfl⟩ : syracuseStep 1531237 = 287107) (by norm_num)
theorem B1989989 : Blo 880569 1989989 := bbase (se 4 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 1989989 = 373123) (by norm_num)
theorem B2973077 : Blo 880569 2973077 := bbase (se 6 (by rfl) ⟨69681, by rfl⟩ : syracuseStep 2973077 = 139363) (by norm_num)
theorem B12705173 : Blo 880569 12705173 := bbase (se 6 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 12705173 = 595555) (by norm_num)
theorem B1990061 : Blo 880569 1990061 := bbase (se 3 (by rfl) ⟨373136, by rfl⟩ : syracuseStep 1990061 = 746273) (by norm_num)
theorem B1990133 : Blo 880569 1990133 := bbase (se 5 (by rfl) ⟨93287, by rfl⟩ : syracuseStep 1990133 = 186575) (by norm_num)
theorem B941581 : Blo 880569 941581 := bbase (se 3 (by rfl) ⟨176546, by rfl⟩ : syracuseStep 941581 = 353093) (by norm_num)
theorem B1990205 : Blo 880569 1990205 := bbase (se 3 (by rfl) ⟨373163, by rfl⟩ : syracuseStep 1990205 = 746327) (by norm_num)
theorem B1990277 : Blo 880569 1990277 := bbase (se 4 (by rfl) ⟨186588, by rfl⟩ : syracuseStep 1990277 = 373177) (by norm_num)
theorem B2973509 : Blo 880569 2973509 := bbase (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) (by norm_num)
theorem B1072981 : Blo 880569 1072981 := bbase (se 9 (by rfl) ⟨3143, by rfl⟩ : syracuseStep 1072981 = 6287) (by norm_num)
theorem B5103445 : Blo 880569 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B9428885 : Blo 880569 9428885 := bbase (se 6 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 9428885 = 441979) (by norm_num)
theorem B942025 : Blo 880569 942025 := bbase (se 2 (by rfl) ⟨353259, by rfl⟩ : syracuseStep 942025 = 706519) (by norm_num)
theorem B2121709 : Blo 880569 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B942149 : Blo 880569 942149 := bbase (se 4 (by rfl) ⟨88326, by rfl⟩ : syracuseStep 942149 = 176653) (by norm_num)
theorem B1531973 : Blo 880569 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B2384005 : Blo 880569 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B2515141 : Blo 880569 2515141 := bbase (se 4 (by rfl) ⟨235794, by rfl⟩ : syracuseStep 2515141 = 471589) (by norm_num)
theorem B2973941 : Blo 880569 2973941 := bbase (se 5 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 2973941 = 278807) (by norm_num)
theorem B942401 : Blo 880569 942401 := bbase (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) (by norm_num)
theorem B1008065 : Blo 880569 1008065 := bbase (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) (by norm_num)
theorem B2122325 : Blo 880569 2122325 := bbase (se 8 (by rfl) ⟨12435, by rfl⟩ : syracuseStep 2122325 = 24871) (by norm_num)
theorem B2122381 : Blo 880569 2122381 := bbase (se 3 (by rfl) ⟨397946, by rfl⟩ : syracuseStep 2122381 = 795893) (by norm_num)
theorem B13591189 : Blo 880569 13591189 := bbase (se 6 (by rfl) ⟨318543, by rfl⟩ : syracuseStep 13591189 = 637087) (by norm_num)
theorem B2974373 : Blo 880569 2974373 := bbase (se 4 (by rfl) ⟨278847, by rfl⟩ : syracuseStep 2974373 = 557695) (by norm_num)
theorem B1008361 : Blo 880569 1008361 := bbase (se 2 (by rfl) ⟨378135, by rfl⟩ : syracuseStep 1008361 = 756271) (by norm_num)
theorem B942845 : Blo 880569 942845 := bbase (se 3 (by rfl) ⟨176783, by rfl⟩ : syracuseStep 942845 = 353567) (by norm_num)
theorem B1631069 : Blo 880569 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B1696621 : Blo 880569 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B943093 : Blo 880569 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B2974805 : Blo 880569 2974805 := bbase (se 8 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 2974805 = 34861) (by norm_num)
theorem B2680037 : Blo 880569 2680037 := bbase (se 4 (by rfl) ⟨251253, by rfl⟩ : syracuseStep 2680037 = 502507) (by norm_num)
theorem B2680229 : Blo 880569 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B943537 : Blo 880569 943537 := bbase (se 2 (by rfl) ⟨353826, by rfl⟩ : syracuseStep 943537 = 707653) (by norm_num)
theorem B943597 : Blo 880569 943597 := bbase (se 3 (by rfl) ⟨176924, by rfl⟩ : syracuseStep 943597 = 353849) (by norm_num)
theorem B2975237 : Blo 880569 2975237 := bbase (se 4 (by rfl) ⟨278928, by rfl⟩ : syracuseStep 2975237 = 557857) (by norm_num)
theorem B5662325 : Blo 880569 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B2123381 : Blo 880569 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B2516645 : Blo 880569 2516645 := bbase (se 4 (by rfl) ⟨235935, by rfl⟩ : syracuseStep 2516645 = 471871) (by norm_num)
theorem B943913 : Blo 880569 943913 := bbase (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) (by norm_num)
theorem B3762085 : Blo 880569 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B2975669 : Blo 880569 2975669 := bbase (se 5 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 2975669 = 278969) (by norm_num)
theorem B2386037 : Blo 880569 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B2418853 : Blo 880569 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B944357 : Blo 880569 944357 := bbase (se 4 (by rfl) ⟨88533, by rfl⟩ : syracuseStep 944357 = 177067) (by norm_num)
theorem B944417 : Blo 880569 944417 := bbase (se 2 (by rfl) ⟨354156, by rfl⟩ : syracuseStep 944417 = 708313) (by norm_num)
theorem B2976101 : Blo 880569 2976101 := bbase (se 4 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 2976101 = 558019) (by norm_num)
theorem B944545 : Blo 880569 944545 := bbase (se 2 (by rfl) ⟨354204, by rfl⟩ : syracuseStep 944545 = 708409) (by norm_num)
theorem B2976533 : Blo 880569 2976533 := bbase (se 6 (by rfl) ⟨69762, by rfl⟩ : syracuseStep 2976533 = 139525) (by norm_num)
theorem B2386837 : Blo 880569 2386837 := bbase (se 6 (by rfl) ⟨55941, by rfl⟩ : syracuseStep 2386837 = 111883) (by norm_num)
theorem B2976965 : Blo 880569 2976965 := bbase (se 4 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 2976965 = 558181) (by norm_num)
theorem B2518229 : Blo 880569 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B2977397 : Blo 880569 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B7171861 : Blo 880569 7171861 := bbase (se 6 (by rfl) ⟨168090, by rfl⟩ : syracuseStep 7171861 = 336181) (by norm_num)
theorem B2518901 : Blo 880569 2518901 := bbase (se 5 (by rfl) ⟨118073, by rfl⟩ : syracuseStep 2518901 = 236147) (by norm_num)
theorem B1339325 : Blo 880569 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B2977829 : Blo 880569 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B1274077 : Blo 880569 1274077 := bbase (se 3 (by rfl) ⟨238889, by rfl⟩ : syracuseStep 1274077 = 477779) (by norm_num)
theorem B2978261 : Blo 880569 2978261 := bbase (se 7 (by rfl) ⟨34901, by rfl⟩ : syracuseStep 2978261 = 69803) (by norm_num)
theorem B1340005 : Blo 880569 1340005 := bbase (se 4 (by rfl) ⟨125625, by rfl⟩ : syracuseStep 1340005 = 251251) (by norm_num)
theorem B1340053 : Blo 880569 1340053 := bbase (se 6 (by rfl) ⟨31407, by rfl⟩ : syracuseStep 1340053 = 62815) (by norm_num)
theorem B2978693 : Blo 880569 2978693 := bbase (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) (by norm_num)
theorem B1274845 : Blo 880569 1274845 := bbase (se 3 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 1274845 = 478067) (by norm_num)
theorem B2323637 : Blo 880569 2323637 := bbase (se 5 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 2323637 = 217841) (by norm_num)
theorem B4027589 : Blo 880569 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B2979125 : Blo 880569 2979125 := bbase (se 5 (by rfl) ⟨139646, by rfl⟩ : syracuseStep 2979125 = 279293) (by norm_num)
theorem B1340893 : Blo 880569 1340893 := bbase (se 3 (by rfl) ⟨251417, by rfl⟩ : syracuseStep 1340893 = 502835) (by norm_num)
theorem B6715061 : Blo 880569 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B2979557 : Blo 880569 2979557 := bbase (se 4 (by rfl) ⟨279333, by rfl⟩ : syracuseStep 2979557 = 558667) (by norm_num)
theorem B2979989 : Blo 880569 2979989 := bbase (se 6 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 2979989 = 139687) (by norm_num)
theorem B6027509 : Blo 880569 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B6355381 : Blo 880569 6355381 := bbase (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) (by norm_num)
theorem B2980421 : Blo 880569 2980421 := bbase (se 4 (by rfl) ⟨279414, by rfl⟩ : syracuseStep 2980421 = 558829) (by norm_num)
theorem B2259533 : Blo 880569 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B3767093 : Blo 880569 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B3177461 : Blo 880569 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B2980853 : Blo 880569 2980853 := bbase (se 5 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 2980853 = 279455) (by norm_num)
theorem B3767381 : Blo 880569 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B2981285 : Blo 880569 2981285 := bbase (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) (by norm_num)
theorem B3768133 : Blo 880569 3768133 := bbase (se 4 (by rfl) ⟨353262, by rfl⟩ : syracuseStep 3768133 = 706525) (by norm_num)
theorem B2981717 : Blo 880569 2981717 := bbase (se 9 (by rfl) ⟨8735, by rfl⟩ : syracuseStep 2981717 = 17471) (by norm_num)
theorem B2981933 : Blo 880569 2981933 := bstep (se 3 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 2981933 = 1118225) B1118225
theorem B2981987 : Blo 880569 2981987 := bstep (se 1 (by rfl) ⟨2236490, by rfl⟩ : syracuseStep 2981987 = 4472981) B4472981
theorem B3178673 : Blo 880569 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B2982257 : Blo 880569 2982257 := bstep (se 2 (by rfl) ⟨1118346, by rfl⟩ : syracuseStep 2982257 = 2236693) B2236693
theorem B1114499 : Blo 880569 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1344019 : Blo 880569 1344019 := bstep (se 1 (by rfl) ⟨1008014, by rfl⟩ : syracuseStep 1344019 = 2016029) B2016029
theorem B1507889 : Blo 880569 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B1671779 : Blo 880569 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B2229059 : Blo 880569 2229059 := bstep (se 1 (by rfl) ⟨1671794, by rfl⟩ : syracuseStep 2229059 = 3343589) B3343589
theorem B18121585 : Blo 880569 18121585 := bstep (se 2 (by rfl) ⟨6795594, by rfl⟩ : syracuseStep 18121585 = 13591189) B13591189
theorem B2982797 : Blo 880569 2982797 := bstep (se 3 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 2982797 = 1118549) B1118549
theorem B2982851 : Blo 880569 2982851 := bstep (se 1 (by rfl) ⟨2237138, by rfl⟩ : syracuseStep 2982851 = 4474277) B4474277
theorem B1344481 : Blo 880569 1344481 := bstep (se 2 (by rfl) ⟨504180, by rfl⟩ : syracuseStep 1344481 = 1008361) B1008361
theorem B4031473 : Blo 880569 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B1115203 : Blo 880569 1115203 := bstep (se 1 (by rfl) ⟨836402, by rfl⟩ : syracuseStep 1115203 = 1672805) B1672805
theorem B2262161 : Blo 880569 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B1115299 : Blo 880569 1115299 := bstep (se 1 (by rfl) ⟨836474, by rfl⟩ : syracuseStep 1115299 = 1672949) B1672949
theorem B2688173 : Blo 880569 2688173 := bstep (se 3 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 2688173 = 1008065) B1008065
theorem B2983121 : Blo 880569 2983121 := bstep (se 2 (by rfl) ⟨1118670, by rfl⟩ : syracuseStep 2983121 = 2237341) B2237341
theorem B6358499 : Blo 880569 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B3769841 : Blo 880569 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B1672721 : Blo 880569 1672721 := bstep (se 2 (by rfl) ⟨627270, by rfl⟩ : syracuseStep 1672721 = 1254541) B1254541
theorem B5375587 : Blo 880569 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B1115795 : Blo 880569 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B2983661 : Blo 880569 2983661 := bstep (se 3 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 2983661 = 1118873) B1118873
theorem B2230001 : Blo 880569 2230001 := bstep (se 2 (by rfl) ⟨836250, by rfl⟩ : syracuseStep 2230001 = 1672501) B1672501
theorem B2230051 : Blo 880569 2230051 := bstep (se 1 (by rfl) ⟨1672538, by rfl⟩ : syracuseStep 2230051 = 3345077) B3345077
theorem B2983715 : Blo 880569 2983715 := bstep (se 1 (by rfl) ⟨2237786, by rfl⟩ : syracuseStep 2983715 = 4475573) B4475573
theorem B5015429 : Blo 880569 5015429 := bstep (se 4 (by rfl) ⟨470196, by rfl⟩ : syracuseStep 5015429 = 940393) B940393
theorem B2230193 : Blo 880569 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B1509313 : Blo 880569 1509313 := bstep (se 2 (by rfl) ⟨565992, by rfl⟩ : syracuseStep 1509313 = 1131985) B1131985
theorem B1411025 : Blo 880569 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B2983985 : Blo 880569 2983985 := bstep (se 2 (by rfl) ⟨1118994, by rfl⟩ : syracuseStep 2983985 = 2237989) B2237989
theorem B3770509 : Blo 880569 3770509 := bstep (se 3 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 3770509 = 1413941) B1413941
theorem B3344561 : Blo 880569 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B1116499 : Blo 880569 1116499 := bstep (se 1 (by rfl) ⟨837374, by rfl⟩ : syracuseStep 1116499 = 1674749) B1674749
theorem B1673617 : Blo 880569 1673617 := bstep (se 2 (by rfl) ⟨627606, by rfl⟩ : syracuseStep 1673617 = 1255213) B1255213
theorem B1116595 : Blo 880569 1116595 := bstep (se 1 (by rfl) ⟨837446, by rfl⟩ : syracuseStep 1116595 = 1674893) B1674893
theorem B61049285 : Blo 880569 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B8063459 : Blo 880569 8063459 := bstep (se 1 (by rfl) ⟨6047594, by rfl⟩ : syracuseStep 8063459 = 12095189) B12095189
theorem B5016113 : Blo 880569 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B1673777 : Blo 880569 1673777 := bstep (se 2 (by rfl) ⟨627666, by rfl⟩ : syracuseStep 1673777 = 1255333) B1255333
theorem B2984525 : Blo 880569 2984525 := bstep (se 3 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 2984525 = 1119197) B1119197
theorem B2984579 : Blo 880569 2984579 := bstep (se 1 (by rfl) ⟨2238434, by rfl⟩ : syracuseStep 2984579 = 4476869) B4476869
theorem B3771107 : Blo 880569 3771107 := bstep (se 1 (by rfl) ⟨2828330, by rfl⟩ : syracuseStep 3771107 = 5656661) B5656661
theorem B2231185 : Blo 880569 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B2984849 : Blo 880569 2984849 := bstep (se 2 (by rfl) ⟨1119318, by rfl⟩ : syracuseStep 2984849 = 2238637) B2238637
theorem B1117091 : Blo 880569 1117091 := bstep (se 1 (by rfl) ⟨837818, by rfl⟩ : syracuseStep 1117091 = 1675637) B1675637
theorem B1674179 : Blo 880569 1674179 := bstep (se 1 (by rfl) ⟨1255634, by rfl⟩ : syracuseStep 1674179 = 2511269) B2511269
theorem B2231459 : Blo 880569 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B4459697 : Blo 880569 4459697 := bstep (se 2 (by rfl) ⟨1672386, by rfl⟩ : syracuseStep 4459697 = 3344773) B3344773
theorem B1412435 : Blo 880569 1412435 := bstep (se 1 (by rfl) ⟨1059326, by rfl⟩ : syracuseStep 1412435 = 2118653) B2118653
theorem B2231651 : Blo 880569 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B2985389 : Blo 880569 2985389 := bstep (se 3 (by rfl) ⟨559760, by rfl⟩ : syracuseStep 2985389 = 1119521) B1119521
theorem B7146949 : Blo 880569 7146949 := bstep (se 4 (by rfl) ⟨670026, by rfl⟩ : syracuseStep 7146949 = 1340053) B1340053
theorem B1412563 : Blo 880569 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B3346019 : Blo 880569 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B1117795 : Blo 880569 1117795 := bstep (se 1 (by rfl) ⟨838346, by rfl⟩ : syracuseStep 1117795 = 1676693) B1676693
theorem B1019539 : Blo 880569 1019539 := bstep (se 1 (by rfl) ⟨764654, by rfl⟩ : syracuseStep 1019539 = 1529309) B1529309
theorem B2297521 : Blo 880569 2297521 := bstep (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) B1723141
theorem B1117891 : Blo 880569 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B7147277 : Blo 880569 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B1675075 : Blo 880569 1675075 := bstep (se 1 (by rfl) ⟨1256306, by rfl⟩ : syracuseStep 1675075 = 2512613) B2512613
theorem B5017571 : Blo 880569 5017571 := bstep (se 1 (by rfl) ⟨3763178, by rfl⟩ : syracuseStep 5017571 = 7526357) B7526357
theorem B1675235 : Blo 880569 1675235 := bstep (se 1 (by rfl) ⟨1256426, by rfl⟩ : syracuseStep 1675235 = 2512853) B2512853
theorem B1413121 : Blo 880569 1413121 := bstep (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) B1059841
theorem B1609763 : Blo 880569 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B6131825 : Blo 880569 6131825 := bstep (se 2 (by rfl) ⟨2299434, by rfl⟩ : syracuseStep 6131825 = 4598869) B4598869
theorem B1118387 : Blo 880569 1118387 := bstep (se 1 (by rfl) ⟨838790, by rfl⟩ : syracuseStep 1118387 = 1677581) B1677581
theorem B2232593 : Blo 880569 2232593 := bstep (se 2 (by rfl) ⟨837222, by rfl⟩ : syracuseStep 2232593 = 1674445) B1674445
theorem B2232643 : Blo 880569 2232643 := bstep (se 1 (by rfl) ⟨1674482, by rfl⟩ : syracuseStep 2232643 = 3348965) B3348965
theorem B2822563 : Blo 880569 2822563 := bstep (se 1 (by rfl) ⟨2116922, by rfl⟩ : syracuseStep 2822563 = 4233845) B4233845
theorem B2232785 : Blo 880569 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B3347021 : Blo 880569 3347021 := bstep (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) B1255133
theorem B4461155 : Blo 880569 4461155 := bstep (se 1 (by rfl) ⟨3345866, by rfl⟩ : syracuseStep 4461155 = 6691733) B6691733
theorem B1413793 : Blo 880569 1413793 := bstep (se 2 (by rfl) ⟨530172, by rfl⟩ : syracuseStep 1413793 = 1060345) B1060345
theorem B1512227 : Blo 880569 1512227 := bstep (se 1 (by rfl) ⟨1134170, by rfl⟩ : syracuseStep 1512227 = 2268341) B2268341
theorem B2823025 : Blo 880569 2823025 := bstep (se 2 (by rfl) ⟨1058634, by rfl⟩ : syracuseStep 2823025 = 2117269) B2117269
theorem B16094065 : Blo 880569 16094065 := bstep (se 2 (by rfl) ⟨6035274, by rfl⟩ : syracuseStep 16094065 = 12070549) B12070549
theorem B1119091 : Blo 880569 1119091 := bstep (se 1 (by rfl) ⟨839318, by rfl⟩ : syracuseStep 1119091 = 1678637) B1678637
theorem B1119187 : Blo 880569 1119187 := bstep (se 1 (by rfl) ⟨839390, by rfl⟩ : syracuseStep 1119187 = 1678781) B1678781
theorem B1676305 : Blo 880569 1676305 := bstep (se 2 (by rfl) ⟨628614, by rfl⟩ : syracuseStep 1676305 = 1257229) B1257229
theorem B10032497 : Blo 880569 10032497 := bstep (se 2 (by rfl) ⟨3762186, by rfl⟩ : syracuseStep 10032497 = 7524373) B7524373
theorem B4461965 : Blo 880569 4461965 := bstep (se 3 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 4461965 = 1673237) B1673237
theorem B2233777 : Blo 880569 2233777 := bstep (se 2 (by rfl) ⟨837666, by rfl⟩ : syracuseStep 2233777 = 1675333) B1675333
theorem B6690275 : Blo 880569 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B2234051 : Blo 880569 2234051 := bstep (se 1 (by rfl) ⟨1675538, by rfl⟩ : syracuseStep 2234051 = 3351077) B3351077
theorem B1414883 : Blo 880569 1414883 := bstep (se 1 (by rfl) ⟨1061162, by rfl⟩ : syracuseStep 1414883 = 2122325) B2122325
theorem B2234243 : Blo 880569 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B1087379 : Blo 880569 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B5806093 : Blo 880569 5806093 := bstep (se 3 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 5806093 = 2177285) B2177285
theorem B1677361 : Blo 880569 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B24254741 : Blo 880569 24254741 := bstep (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) B1136941
theorem B3774883 : Blo 880569 3774883 := bstep (se 1 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 3774883 = 5662325) B5662325
theorem B1677763 : Blo 880569 1677763 := bstep (se 1 (by rfl) ⟨1258322, by rfl⟩ : syracuseStep 1677763 = 2516645) B2516645
theorem B1677809 : Blo 880569 1677809 := bstep (se 2 (by rfl) ⟨629178, by rfl⟩ : syracuseStep 1677809 = 1258357) B1258357
theorem B3349133 : Blo 880569 3349133 := bstep (se 3 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 3349133 = 1255925) B1255925
theorem B1678097 : Blo 880569 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B2235185 : Blo 880569 2235185 := bstep (se 2 (by rfl) ⟨838194, by rfl⟩ : syracuseStep 2235185 = 1676389) B1676389
theorem B2235235 : Blo 880569 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B2235377 : Blo 880569 2235377 := bstep (se 2 (by rfl) ⟨838266, by rfl⟩ : syracuseStep 2235377 = 1676533) B1676533
theorem B1416305 : Blo 880569 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B5020805 : Blo 880569 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B8068493 : Blo 880569 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B3349937 : Blo 880569 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B990643 : Blo 880569 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B1678819 : Blo 880569 1678819 := bstep (se 1 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 1678819 = 2518229) B2518229
theorem B2825741 : Blo 880569 2825741 := bstep (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) B1059653
theorem B990787 : Blo 880569 990787 := bstep (se 1 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 990787 = 1486181) B1486181
theorem B5021261 : Blo 880569 5021261 := bstep (se 3 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 5021261 = 1882973) B1882973
theorem B990931 : Blo 880569 990931 := bstep (se 1 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 990931 = 1486397) B1486397
theorem B7151429 : Blo 880569 7151429 := bstep (se 4 (by rfl) ⟨670446, by rfl⟩ : syracuseStep 7151429 = 1340893) B1340893
theorem B991075 : Blo 880569 991075 := bstep (se 1 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 991075 = 1486613) B1486613
theorem B1679267 : Blo 880569 1679267 := bstep (se 1 (by rfl) ⟨1259450, by rfl⟩ : syracuseStep 1679267 = 2518901) B2518901
theorem B2236369 : Blo 880569 2236369 := bstep (se 2 (by rfl) ⟨838638, by rfl⟩ : syracuseStep 2236369 = 1677277) B1677277
theorem B892883 : Blo 880569 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B991219 : Blo 880569 991219 := bstep (se 1 (by rfl) ⟨743414, by rfl⟩ : syracuseStep 991219 = 1486829) B1486829
theorem B3350605 : Blo 880569 3350605 := bstep (se 3 (by rfl) ⟨628238, by rfl⟩ : syracuseStep 3350605 = 1256477) B1256477
theorem B991363 : Blo 880569 991363 := bstep (se 1 (by rfl) ⟨743522, by rfl⟩ : syracuseStep 991363 = 1487045) B1487045
theorem B2236643 : Blo 880569 2236643 := bstep (se 1 (by rfl) ⟨1677482, by rfl⟩ : syracuseStep 2236643 = 3354965) B3354965
theorem B4464881 : Blo 880569 4464881 := bstep (se 2 (by rfl) ⟨1674330, by rfl⟩ : syracuseStep 4464881 = 3348661) B3348661
theorem B5447941 : Blo 880569 5447941 := bstep (se 4 (by rfl) ⟨510744, by rfl⟩ : syracuseStep 5447941 = 1021489) B1021489
theorem B991507 : Blo 880569 991507 := bstep (se 1 (by rfl) ⟨743630, by rfl⟩ : syracuseStep 991507 = 1487261) B1487261
theorem B3776881 : Blo 880569 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B991651 : Blo 880569 991651 := bstep (se 1 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 991651 = 1487477) B1487477
theorem B2236835 : Blo 880569 2236835 := bstep (se 1 (by rfl) ⟨1677626, by rfl⟩ : syracuseStep 2236835 = 3355253) B3355253
theorem B1253875 : Blo 880569 1253875 := bstep (se 1 (by rfl) ⟨940406, by rfl⟩ : syracuseStep 1253875 = 1880813) B1880813
theorem B991795 : Blo 880569 991795 := bstep (se 1 (by rfl) ⟨743846, by rfl⟩ : syracuseStep 991795 = 1487693) B1487693
theorem B1253971 : Blo 880569 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B991939 : Blo 880569 991939 := bstep (se 1 (by rfl) ⟨743954, by rfl⟩ : syracuseStep 991939 = 1487909) B1487909
theorem B1549091 : Blo 880569 1549091 := bstep (se 1 (by rfl) ⟨1161818, by rfl⟩ : syracuseStep 1549091 = 2323637) B2323637
theorem B992083 : Blo 880569 992083 := bstep (se 1 (by rfl) ⟨744062, by rfl⟩ : syracuseStep 992083 = 1488125) B1488125
theorem B3351395 : Blo 880569 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B992227 : Blo 880569 992227 := bstep (se 1 (by rfl) ⟨744170, by rfl⟩ : syracuseStep 992227 = 1488341) B1488341
theorem B1254467 : Blo 880569 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B2827331 : Blo 880569 2827331 := bstep (se 1 (by rfl) ⟨2120498, by rfl⟩ : syracuseStep 2827331 = 4240997) B4240997
theorem B992371 : Blo 880569 992371 := bstep (se 1 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 992371 = 1488557) B1488557
theorem B992515 : Blo 880569 992515 := bstep (se 1 (by rfl) ⟨744386, by rfl⟩ : syracuseStep 992515 = 1488773) B1488773
theorem B5088581 : Blo 880569 5088581 := bstep (se 4 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 5088581 = 954109) B954109
theorem B2237777 : Blo 880569 2237777 := bstep (se 2 (by rfl) ⟨839166, by rfl⟩ : syracuseStep 2237777 = 1678333) B1678333
theorem B2237827 : Blo 880569 2237827 := bstep (se 1 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 2237827 = 3356741) B3356741
theorem B992659 : Blo 880569 992659 := bstep (se 1 (by rfl) ⟨744494, by rfl⟩ : syracuseStep 992659 = 1488989) B1488989
theorem B3352049 : Blo 880569 3352049 := bstep (se 2 (by rfl) ⟨1257018, by rfl⟩ : syracuseStep 3352049 = 2514037) B2514037
theorem B4531697 : Blo 880569 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B2237969 : Blo 880569 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B992803 : Blo 880569 992803 := bstep (se 1 (by rfl) ⟨744602, by rfl⟩ : syracuseStep 992803 = 1489205) B1489205
theorem B4466339 : Blo 880569 4466339 := bstep (se 1 (by rfl) ⟨3349754, by rfl⟩ : syracuseStep 4466339 = 6699509) B6699509
theorem B992947 : Blo 880569 992947 := bstep (se 1 (by rfl) ⟨744710, by rfl⟩ : syracuseStep 992947 = 1489421) B1489421
theorem B1255105 : Blo 880569 1255105 := bstep (se 2 (by rfl) ⟨470664, by rfl⟩ : syracuseStep 1255105 = 941329) B941329
theorem B2041649 : Blo 880569 2041649 := bstep (se 2 (by rfl) ⟨765618, by rfl⟩ : syracuseStep 2041649 = 1531237) B1531237
theorem B1058611 : Blo 880569 1058611 := bstep (se 1 (by rfl) ⟨793958, by rfl⟩ : syracuseStep 1058611 = 1587917) B1587917
theorem B993091 : Blo 880569 993091 := bstep (se 1 (by rfl) ⟨744818, by rfl⟩ : syracuseStep 993091 = 1489637) B1489637
theorem B1320881 : Blo 880569 1320881 := bstep (se 2 (by rfl) ⟨495330, by rfl⟩ : syracuseStep 1320881 = 990661) B990661
theorem B1320899 : Blo 880569 1320899 := bstep (se 1 (by rfl) ⟨990674, by rfl⟩ : syracuseStep 1320899 = 1981349) B1981349
theorem B993235 : Blo 880569 993235 := bstep (se 1 (by rfl) ⟨744926, by rfl⟩ : syracuseStep 993235 = 1489853) B1489853
theorem B1320929 : Blo 880569 1320929 := bstep (se 2 (by rfl) ⟨495348, by rfl⟩ : syracuseStep 1320929 = 990697) B990697
theorem B1320947 : Blo 880569 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B1320977 : Blo 880569 1320977 := bstep (se 2 (by rfl) ⟨495366, by rfl⟩ : syracuseStep 1320977 = 990733) B990733
theorem B1255441 : Blo 880569 1255441 := bstep (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) B941581
theorem B1320995 : Blo 880569 1320995 := bstep (se 1 (by rfl) ⟨990746, by rfl⟩ : syracuseStep 1320995 = 1981493) B1981493
theorem B1321025 : Blo 880569 1321025 := bstep (se 2 (by rfl) ⟨495384, by rfl⟩ : syracuseStep 1321025 = 990769) B990769
theorem B1321043 : Blo 880569 1321043 := bstep (se 1 (by rfl) ⟨990782, by rfl⟩ : syracuseStep 1321043 = 1981565) B1981565
theorem B993379 : Blo 880569 993379 := bstep (se 1 (by rfl) ⟨745034, by rfl⟩ : syracuseStep 993379 = 1490069) B1490069
theorem B1321073 : Blo 880569 1321073 := bstep (se 2 (by rfl) ⟨495402, by rfl⟩ : syracuseStep 1321073 = 990805) B990805
theorem B1321091 : Blo 880569 1321091 := bstep (se 1 (by rfl) ⟨990818, by rfl⟩ : syracuseStep 1321091 = 1981637) B1981637
theorem B1321121 : Blo 880569 1321121 := bstep (se 2 (by rfl) ⟨495420, by rfl⟩ : syracuseStep 1321121 = 990841) B990841
theorem B1321139 : Blo 880569 1321139 := bstep (se 1 (by rfl) ⟨990854, by rfl⟩ : syracuseStep 1321139 = 1981709) B1981709
theorem B1321169 : Blo 880569 1321169 := bstep (se 2 (by rfl) ⟨495438, by rfl⟩ : syracuseStep 1321169 = 990877) B990877
theorem B1321187 : Blo 880569 1321187 := bstep (se 1 (by rfl) ⟨990890, by rfl⟩ : syracuseStep 1321187 = 1981781) B1981781
theorem B993523 : Blo 880569 993523 := bstep (se 1 (by rfl) ⟨745142, by rfl⟩ : syracuseStep 993523 = 1490285) B1490285
theorem B1321217 : Blo 880569 1321217 := bstep (se 2 (by rfl) ⟨495456, by rfl⟩ : syracuseStep 1321217 = 990913) B990913
theorem B1321235 : Blo 880569 1321235 := bstep (se 1 (by rfl) ⟨990926, by rfl⟩ : syracuseStep 1321235 = 1981853) B1981853
theorem B1321265 : Blo 880569 1321265 := bstep (se 2 (by rfl) ⟨495474, by rfl⟩ : syracuseStep 1321265 = 990949) B990949
theorem B1321283 : Blo 880569 1321283 := bstep (se 1 (by rfl) ⟨990962, by rfl⟩ : syracuseStep 1321283 = 1981925) B1981925
theorem B2828611 : Blo 880569 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B1321313 : Blo 880569 1321313 := bstep (se 2 (by rfl) ⟨495492, by rfl⟩ : syracuseStep 1321313 = 990985) B990985
theorem B1321331 : Blo 880569 1321331 := bstep (se 1 (by rfl) ⟨990998, by rfl⟩ : syracuseStep 1321331 = 1981997) B1981997
theorem B993667 : Blo 880569 993667 := bstep (se 1 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 993667 = 1490501) B1490501
theorem B1321361 : Blo 880569 1321361 := bstep (se 2 (by rfl) ⟨495510, by rfl⟩ : syracuseStep 1321361 = 991021) B991021
theorem B1190305 : Blo 880569 1190305 := bstep (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) B892729
theorem B1321379 : Blo 880569 1321379 := bstep (se 1 (by rfl) ⟨991034, by rfl⟩ : syracuseStep 1321379 = 1982069) B1982069
theorem B5024177 : Blo 880569 5024177 := bstep (se 2 (by rfl) ⟨1884066, by rfl⟩ : syracuseStep 5024177 = 3768133) B3768133
theorem B1321409 : Blo 880569 1321409 := bstep (se 2 (by rfl) ⟨495528, by rfl⟩ : syracuseStep 1321409 = 991057) B991057
theorem B4467149 : Blo 880569 4467149 := bstep (se 3 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 4467149 = 1675181) B1675181
theorem B1321427 : Blo 880569 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B1321457 : Blo 880569 1321457 := bstep (se 2 (by rfl) ⟨495546, by rfl⟩ : syracuseStep 1321457 = 991093) B991093
theorem B2238961 : Blo 880569 2238961 := bstep (se 2 (by rfl) ⟨839610, by rfl⟩ : syracuseStep 2238961 = 1679221) B1679221
theorem B1321475 : Blo 880569 1321475 := bstep (se 1 (by rfl) ⟨991106, by rfl⟩ : syracuseStep 1321475 = 1982213) B1982213
theorem B993811 : Blo 880569 993811 := bstep (se 1 (by rfl) ⟨745358, by rfl⟩ : syracuseStep 993811 = 1490717) B1490717
theorem B1321505 : Blo 880569 1321505 := bstep (se 2 (by rfl) ⟨495564, by rfl⟩ : syracuseStep 1321505 = 991129) B991129
theorem B1321523 : Blo 880569 1321523 := bstep (se 1 (by rfl) ⟨991142, by rfl⟩ : syracuseStep 1321523 = 1982285) B1982285
theorem B1190467 : Blo 880569 1190467 := bstep (se 1 (by rfl) ⟨892850, by rfl⟩ : syracuseStep 1190467 = 1785701) B1785701
theorem B1321553 : Blo 880569 1321553 := bstep (se 2 (by rfl) ⟨495582, by rfl⟩ : syracuseStep 1321553 = 991165) B991165
theorem B1256033 : Blo 880569 1256033 := bstep (se 2 (by rfl) ⟨471012, by rfl⟩ : syracuseStep 1256033 = 942025) B942025
theorem B1321571 : Blo 880569 1321571 := bstep (se 1 (by rfl) ⟨991178, by rfl⟩ : syracuseStep 1321571 = 1982357) B1982357
theorem B1321601 : Blo 880569 1321601 := bstep (se 2 (by rfl) ⟨495600, by rfl⟩ : syracuseStep 1321601 = 991201) B991201
theorem B2828945 : Blo 880569 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B1321619 : Blo 880569 1321619 := bstep (se 1 (by rfl) ⟨991214, by rfl⟩ : syracuseStep 1321619 = 1982429) B1982429
theorem B993955 : Blo 880569 993955 := bstep (se 1 (by rfl) ⟨745466, by rfl⟩ : syracuseStep 993955 = 1490933) B1490933
theorem B1321649 : Blo 880569 1321649 := bstep (se 2 (by rfl) ⟨495618, by rfl⟩ : syracuseStep 1321649 = 991237) B991237
theorem B1321667 : Blo 880569 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B6695621 : Blo 880569 6695621 := bstep (se 4 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 6695621 = 1255429) B1255429
theorem B1321697 : Blo 880569 1321697 := bstep (se 2 (by rfl) ⟨495636, by rfl⟩ : syracuseStep 1321697 = 991273) B991273
theorem B1321715 : Blo 880569 1321715 := bstep (se 1 (by rfl) ⟨991286, by rfl⟩ : syracuseStep 1321715 = 1982573) B1982573
theorem B1321745 : Blo 880569 1321745 := bstep (se 2 (by rfl) ⟨495654, by rfl⟩ : syracuseStep 1321745 = 991309) B991309
theorem B1321763 : Blo 880569 1321763 := bstep (se 1 (by rfl) ⟨991322, by rfl⟩ : syracuseStep 1321763 = 1982645) B1982645
theorem B994099 : Blo 880569 994099 := bstep (se 1 (by rfl) ⟨745574, by rfl⟩ : syracuseStep 994099 = 1491149) B1491149
theorem B1321793 : Blo 880569 1321793 := bstep (se 2 (by rfl) ⟨495672, by rfl⟩ : syracuseStep 1321793 = 991345) B991345
theorem B1321811 : Blo 880569 1321811 := bstep (se 1 (by rfl) ⟨991358, by rfl⟩ : syracuseStep 1321811 = 1982717) B1982717
theorem B1321841 : Blo 880569 1321841 := bstep (se 2 (by rfl) ⟨495690, by rfl⟩ : syracuseStep 1321841 = 991381) B991381
theorem B1321859 : Blo 880569 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B3025795 : Blo 880569 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B1321889 : Blo 880569 1321889 := bstep (se 2 (by rfl) ⟨495708, by rfl⟩ : syracuseStep 1321889 = 991417) B991417
theorem B3353507 : Blo 880569 3353507 := bstep (se 1 (by rfl) ⟨2515130, by rfl⟩ : syracuseStep 3353507 = 5030261) B5030261
theorem B3353521 : Blo 880569 3353521 := bstep (se 2 (by rfl) ⟨1257570, by rfl⟩ : syracuseStep 3353521 = 2515141) B2515141
theorem B1321907 : Blo 880569 1321907 := bstep (se 1 (by rfl) ⟨991430, by rfl⟩ : syracuseStep 1321907 = 1982861) B1982861
theorem B994243 : Blo 880569 994243 := bstep (se 1 (by rfl) ⟨745682, by rfl⟩ : syracuseStep 994243 = 1491365) B1491365
theorem B1321937 : Blo 880569 1321937 := bstep (se 2 (by rfl) ⟨495726, by rfl⟩ : syracuseStep 1321937 = 991453) B991453
theorem B1190867 : Blo 880569 1190867 := bstep (se 1 (by rfl) ⟨893150, by rfl⟩ : syracuseStep 1190867 = 1786301) B1786301
theorem B1321955 : Blo 880569 1321955 := bstep (se 1 (by rfl) ⟨991466, by rfl⟩ : syracuseStep 1321955 = 1982933) B1982933
theorem B1321985 : Blo 880569 1321985 := bstep (se 2 (by rfl) ⟨495744, by rfl⟩ : syracuseStep 1321985 = 991489) B991489
theorem B1322003 : Blo 880569 1322003 := bstep (se 1 (by rfl) ⟨991502, by rfl⟩ : syracuseStep 1322003 = 1983005) B1983005
theorem B1322033 : Blo 880569 1322033 := bstep (se 2 (by rfl) ⟨495762, by rfl⟩ : syracuseStep 1322033 = 991525) B991525
theorem B1322051 : Blo 880569 1322051 := bstep (se 1 (by rfl) ⟨991538, by rfl⟩ : syracuseStep 1322051 = 1983077) B1983077
theorem B994387 : Blo 880569 994387 := bstep (se 1 (by rfl) ⟨745790, by rfl⟩ : syracuseStep 994387 = 1491581) B1491581
theorem B1322081 : Blo 880569 1322081 := bstep (se 2 (by rfl) ⟨495780, by rfl⟩ : syracuseStep 1322081 = 991561) B991561
theorem B1322099 : Blo 880569 1322099 := bstep (se 1 (by rfl) ⟨991574, by rfl⟩ : syracuseStep 1322099 = 1983149) B1983149
theorem B1256563 : Blo 880569 1256563 := bstep (se 1 (by rfl) ⟨942422, by rfl⟩ : syracuseStep 1256563 = 1884845) B1884845
theorem B1322129 : Blo 880569 1322129 := bstep (se 2 (by rfl) ⟨495798, by rfl⟩ : syracuseStep 1322129 = 991597) B991597
theorem B1485985 : Blo 880569 1485985 := bstep (se 2 (by rfl) ⟨557244, by rfl⟩ : syracuseStep 1485985 = 1114489) B1114489
theorem B1322147 : Blo 880569 1322147 := bstep (se 1 (by rfl) ⟨991610, by rfl⟩ : syracuseStep 1322147 = 1983221) B1983221
theorem B1322177 : Blo 880569 1322177 := bstep (se 2 (by rfl) ⟨495816, by rfl⟩ : syracuseStep 1322177 = 991633) B991633
theorem B1486019 : Blo 880569 1486019 := bstep (se 1 (by rfl) ⟨1114514, by rfl⟩ : syracuseStep 1486019 = 2229029) B2229029
theorem B1322195 : Blo 880569 1322195 := bstep (se 1 (by rfl) ⟨991646, by rfl⟩ : syracuseStep 1322195 = 1983293) B1983293
theorem B994531 : Blo 880569 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B1322225 : Blo 880569 1322225 := bstep (se 2 (by rfl) ⟨495834, by rfl⟩ : syracuseStep 1322225 = 991669) B991669
theorem B1322243 : Blo 880569 1322243 := bstep (se 1 (by rfl) ⟨991682, by rfl⟩ : syracuseStep 1322243 = 1983365) B1983365
theorem B1322273 : Blo 880569 1322273 := bstep (se 2 (by rfl) ⟨495852, by rfl⟩ : syracuseStep 1322273 = 991705) B991705
theorem B1322291 : Blo 880569 1322291 := bstep (se 1 (by rfl) ⟨991718, by rfl⟩ : syracuseStep 1322291 = 1983437) B1983437
theorem B1486147 : Blo 880569 1486147 := bstep (se 1 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 1486147 = 2229221) B2229221
theorem B1322321 : Blo 880569 1322321 := bstep (se 2 (by rfl) ⟨495870, by rfl⟩ : syracuseStep 1322321 = 991741) B991741
theorem B1322339 : Blo 880569 1322339 := bstep (se 1 (by rfl) ⟨991754, by rfl⟩ : syracuseStep 1322339 = 1983509) B1983509
theorem B994675 : Blo 880569 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B1322369 : Blo 880569 1322369 := bstep (se 2 (by rfl) ⟨495888, by rfl⟩ : syracuseStep 1322369 = 991777) B991777
theorem B6040973 : Blo 880569 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B1322387 : Blo 880569 1322387 := bstep (se 1 (by rfl) ⟨991790, by rfl⟩ : syracuseStep 1322387 = 1983581) B1983581
theorem B1322417 : Blo 880569 1322417 := bstep (se 2 (by rfl) ⟨495906, by rfl⟩ : syracuseStep 1322417 = 991813) B991813
theorem B1322435 : Blo 880569 1322435 := bstep (se 1 (by rfl) ⟨991826, by rfl⟩ : syracuseStep 1322435 = 1983653) B1983653
theorem B1256899 : Blo 880569 1256899 := bstep (se 1 (by rfl) ⟨942674, by rfl⟩ : syracuseStep 1256899 = 1885349) B1885349
theorem B1486289 : Blo 880569 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B1322465 : Blo 880569 1322465 := bstep (se 2 (by rfl) ⟨495924, by rfl⟩ : syracuseStep 1322465 = 991849) B991849
theorem B1322483 : Blo 880569 1322483 := bstep (se 1 (by rfl) ⟨991862, by rfl⟩ : syracuseStep 1322483 = 1983725) B1983725
theorem B994819 : Blo 880569 994819 := bstep (se 1 (by rfl) ⟨746114, by rfl⟩ : syracuseStep 994819 = 1492229) B1492229
theorem B1322513 : Blo 880569 1322513 := bstep (se 2 (by rfl) ⟨495942, by rfl⟩ : syracuseStep 1322513 = 991885) B991885
theorem B1322531 : Blo 880569 1322531 := bstep (se 1 (by rfl) ⟨991898, by rfl⟩ : syracuseStep 1322531 = 1983797) B1983797
theorem B1322561 : Blo 880569 1322561 := bstep (se 2 (by rfl) ⟨495960, by rfl⟩ : syracuseStep 1322561 = 991921) B991921
theorem B1486417 : Blo 880569 1486417 := bstep (se 2 (by rfl) ⟨557406, by rfl⟩ : syracuseStep 1486417 = 1114813) B1114813
theorem B1322579 : Blo 880569 1322579 := bstep (se 1 (by rfl) ⟨991934, by rfl⟩ : syracuseStep 1322579 = 1983869) B1983869
theorem B4763249 : Blo 880569 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B1322609 : Blo 880569 1322609 := bstep (se 2 (by rfl) ⟨495978, by rfl⟩ : syracuseStep 1322609 = 991957) B991957
theorem B1486451 : Blo 880569 1486451 := bstep (se 1 (by rfl) ⟨1114838, by rfl⟩ : syracuseStep 1486451 = 2229677) B2229677
theorem B1322627 : Blo 880569 1322627 := bstep (se 1 (by rfl) ⟨991970, by rfl⟩ : syracuseStep 1322627 = 1983941) B1983941
theorem B1060499 : Blo 880569 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B994963 : Blo 880569 994963 := bstep (se 1 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 994963 = 1492445) B1492445
theorem B1322657 : Blo 880569 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B1322675 : Blo 880569 1322675 := bstep (se 1 (by rfl) ⟨992006, by rfl⟩ : syracuseStep 1322675 = 1984013) B1984013
theorem B1060547 : Blo 880569 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B1322705 : Blo 880569 1322705 := bstep (se 2 (by rfl) ⟨496014, by rfl⟩ : syracuseStep 1322705 = 992029) B992029
theorem B1322723 : Blo 880569 1322723 := bstep (se 1 (by rfl) ⟨992042, by rfl⟩ : syracuseStep 1322723 = 1984085) B1984085
theorem B1486579 : Blo 880569 1486579 := bstep (se 1 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 1486579 = 2229869) B2229869
theorem B1322753 : Blo 880569 1322753 := bstep (se 2 (by rfl) ⟨496032, by rfl⟩ : syracuseStep 1322753 = 992065) B992065
theorem B1322771 : Blo 880569 1322771 := bstep (se 1 (by rfl) ⟨992078, by rfl⟩ : syracuseStep 1322771 = 1984157) B1984157
theorem B995107 : Blo 880569 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B1322801 : Blo 880569 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B1322819 : Blo 880569 1322819 := bstep (se 1 (by rfl) ⟨992114, by rfl⟩ : syracuseStep 1322819 = 1984229) B1984229
theorem B1748803 : Blo 880569 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B1322849 : Blo 880569 1322849 := bstep (se 2 (by rfl) ⟨496068, by rfl⟩ : syracuseStep 1322849 = 992137) B992137
theorem B5025635 : Blo 880569 5025635 := bstep (se 1 (by rfl) ⟨3769226, by rfl⟩ : syracuseStep 5025635 = 7538453) B7538453
theorem B1322867 : Blo 880569 1322867 := bstep (se 1 (by rfl) ⟨992150, by rfl⟩ : syracuseStep 1322867 = 1984301) B1984301
theorem B1486721 : Blo 880569 1486721 := bstep (se 2 (by rfl) ⟨557520, by rfl⟩ : syracuseStep 1486721 = 1115041) B1115041
theorem B1322897 : Blo 880569 1322897 := bstep (se 2 (by rfl) ⟨496086, by rfl⟩ : syracuseStep 1322897 = 992173) B992173
theorem B1322915 : Blo 880569 1322915 := bstep (se 1 (by rfl) ⟨992186, by rfl⟩ : syracuseStep 1322915 = 1984373) B1984373
theorem B1322945 : Blo 880569 1322945 := bstep (se 2 (by rfl) ⟨496104, by rfl⟩ : syracuseStep 1322945 = 992209) B992209
theorem B1322963 : Blo 880569 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B1322993 : Blo 880569 1322993 := bstep (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) B992245
theorem B1257457 : Blo 880569 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B1486849 : Blo 880569 1486849 := bstep (se 2 (by rfl) ⟨557568, by rfl⟩ : syracuseStep 1486849 = 1115137) B1115137
theorem B1191937 : Blo 880569 1191937 := bstep (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) B893953
theorem B1323011 : Blo 880569 1323011 := bstep (se 1 (by rfl) ⟨992258, by rfl⟩ : syracuseStep 1323011 = 1984517) B1984517
theorem B1257491 : Blo 880569 1257491 := bstep (se 1 (by rfl) ⟨943118, by rfl⟩ : syracuseStep 1257491 = 1886237) B1886237
theorem B1323041 : Blo 880569 1323041 := bstep (se 2 (by rfl) ⟨496140, by rfl⟩ : syracuseStep 1323041 = 992281) B992281
theorem B1486883 : Blo 880569 1486883 := bstep (se 1 (by rfl) ⟨1115162, by rfl⟩ : syracuseStep 1486883 = 2230325) B2230325
theorem B1323059 : Blo 880569 1323059 := bstep (se 1 (by rfl) ⟨992294, by rfl⟩ : syracuseStep 1323059 = 1984589) B1984589
theorem B1323089 : Blo 880569 1323089 := bstep (se 2 (by rfl) ⟨496158, by rfl⟩ : syracuseStep 1323089 = 992317) B992317
theorem B1323107 : Blo 880569 1323107 := bstep (se 1 (by rfl) ⟨992330, by rfl⟩ : syracuseStep 1323107 = 1984661) B1984661
theorem B1323137 : Blo 880569 1323137 := bstep (se 2 (by rfl) ⟨496176, by rfl⟩ : syracuseStep 1323137 = 992353) B992353
theorem B1323155 : Blo 880569 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B1487011 : Blo 880569 1487011 := bstep (se 1 (by rfl) ⟨1115258, by rfl⟩ : syracuseStep 1487011 = 2230517) B2230517
theorem B1323185 : Blo 880569 1323185 := bstep (se 2 (by rfl) ⟨496194, by rfl⟩ : syracuseStep 1323185 = 992389) B992389
theorem B1323203 : Blo 880569 1323203 := bstep (se 1 (by rfl) ⟨992402, by rfl⟩ : syracuseStep 1323203 = 1984805) B1984805
theorem B1323233 : Blo 880569 1323233 := bstep (se 2 (by rfl) ⟨496212, by rfl⟩ : syracuseStep 1323233 = 992425) B992425
theorem B5648611 : Blo 880569 5648611 := bstep (se 1 (by rfl) ⟨4236458, by rfl⟩ : syracuseStep 5648611 = 8472917) B8472917
theorem B1323251 : Blo 880569 1323251 := bstep (se 1 (by rfl) ⟨992438, by rfl⟩ : syracuseStep 1323251 = 1984877) B1984877
theorem B1323281 : Blo 880569 1323281 := bstep (se 2 (by rfl) ⟨496230, by rfl⟩ : syracuseStep 1323281 = 992461) B992461
theorem B1323299 : Blo 880569 1323299 := bstep (se 1 (by rfl) ⟨992474, by rfl⟩ : syracuseStep 1323299 = 1984949) B1984949
theorem B1487153 : Blo 880569 1487153 := bstep (se 2 (by rfl) ⟨557682, by rfl⟩ : syracuseStep 1487153 = 1115365) B1115365
theorem B1323329 : Blo 880569 1323329 := bstep (se 2 (by rfl) ⟨496248, by rfl⟩ : syracuseStep 1323329 = 992497) B992497
theorem B1323347 : Blo 880569 1323347 := bstep (se 1 (by rfl) ⟨992510, by rfl⟩ : syracuseStep 1323347 = 1985021) B1985021
theorem B3354979 : Blo 880569 3354979 := bstep (se 1 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 3354979 = 5032469) B5032469
theorem B1323377 : Blo 880569 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B1323395 : Blo 880569 1323395 := bstep (se 1 (by rfl) ⟨992546, by rfl⟩ : syracuseStep 1323395 = 1985093) B1985093
theorem B1814929 : Blo 880569 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B1323425 : Blo 880569 1323425 := bstep (se 2 (by rfl) ⟨496284, by rfl⟩ : syracuseStep 1323425 = 992569) B992569
theorem B1487281 : Blo 880569 1487281 := bstep (se 2 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 1487281 = 1115461) B1115461
theorem B5091761 : Blo 880569 5091761 := bstep (se 2 (by rfl) ⟨1909410, by rfl⟩ : syracuseStep 5091761 = 3818821) B3818821
theorem B1323443 : Blo 880569 1323443 := bstep (se 1 (by rfl) ⟨992582, by rfl⟩ : syracuseStep 1323443 = 1985165) B1985165
theorem B1323473 : Blo 880569 1323473 := bstep (se 2 (by rfl) ⟨496302, by rfl⟩ : syracuseStep 1323473 = 992605) B992605
theorem B1487315 : Blo 880569 1487315 := bstep (se 1 (by rfl) ⟨1115486, by rfl⟩ : syracuseStep 1487315 = 2230973) B2230973
theorem B1323491 : Blo 880569 1323491 := bstep (se 1 (by rfl) ⟨992618, by rfl⟩ : syracuseStep 1323491 = 1985237) B1985237
theorem B1323521 : Blo 880569 1323521 := bstep (se 2 (by rfl) ⟨496320, by rfl⟩ : syracuseStep 1323521 = 992641) B992641
theorem B1323539 : Blo 880569 1323539 := bstep (se 1 (by rfl) ⟨992654, by rfl⟩ : syracuseStep 1323539 = 1985309) B1985309
theorem B1323569 : Blo 880569 1323569 := bstep (se 2 (by rfl) ⟨496338, by rfl⟩ : syracuseStep 1323569 = 992677) B992677
theorem B1258049 : Blo 880569 1258049 := bstep (se 2 (by rfl) ⟨471768, by rfl⟩ : syracuseStep 1258049 = 943537) B943537
theorem B1323587 : Blo 880569 1323587 := bstep (se 1 (by rfl) ⟨992690, by rfl⟩ : syracuseStep 1323587 = 1985381) B1985381
theorem B1487443 : Blo 880569 1487443 := bstep (se 1 (by rfl) ⟨1115582, by rfl⟩ : syracuseStep 1487443 = 2231165) B2231165
theorem B1323617 : Blo 880569 1323617 := bstep (se 2 (by rfl) ⟨496356, by rfl⟩ : syracuseStep 1323617 = 992713) B992713
theorem B1323635 : Blo 880569 1323635 := bstep (se 1 (by rfl) ⟨992726, by rfl⟩ : syracuseStep 1323635 = 1985453) B1985453
theorem B1323665 : Blo 880569 1323665 := bstep (se 2 (by rfl) ⟨496374, by rfl⟩ : syracuseStep 1323665 = 992749) B992749
theorem B1258129 : Blo 880569 1258129 := bstep (se 2 (by rfl) ⟨471798, by rfl⟩ : syracuseStep 1258129 = 943597) B943597
theorem B1323683 : Blo 880569 1323683 := bstep (se 1 (by rfl) ⟨992762, by rfl⟩ : syracuseStep 1323683 = 1985525) B1985525
theorem B2831021 : Blo 880569 2831021 := bstep (se 3 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 2831021 = 1061633) B1061633
theorem B1323713 : Blo 880569 1323713 := bstep (se 2 (by rfl) ⟨496392, by rfl⟩ : syracuseStep 1323713 = 992785) B992785
theorem B1323731 : Blo 880569 1323731 := bstep (se 1 (by rfl) ⟨992798, by rfl⟩ : syracuseStep 1323731 = 1985597) B1985597
theorem B1487585 : Blo 880569 1487585 := bstep (se 2 (by rfl) ⟨557844, by rfl⟩ : syracuseStep 1487585 = 1115689) B1115689
theorem B1323761 : Blo 880569 1323761 := bstep (se 2 (by rfl) ⟨496410, by rfl⟩ : syracuseStep 1323761 = 992821) B992821
theorem B1323779 : Blo 880569 1323779 := bstep (se 1 (by rfl) ⟨992834, by rfl⟩ : syracuseStep 1323779 = 1985669) B1985669
theorem B1323809 : Blo 880569 1323809 := bstep (se 2 (by rfl) ⟨496428, by rfl⟩ : syracuseStep 1323809 = 992857) B992857
theorem B1323827 : Blo 880569 1323827 := bstep (se 1 (by rfl) ⟨992870, by rfl⟩ : syracuseStep 1323827 = 1985741) B1985741
theorem B5026637 : Blo 880569 5026637 := bstep (se 3 (by rfl) ⟨942494, by rfl⟩ : syracuseStep 5026637 = 1884989) B1884989
theorem B1323857 : Blo 880569 1323857 := bstep (se 2 (by rfl) ⟨496446, by rfl⟩ : syracuseStep 1323857 = 992893) B992893
theorem B1487713 : Blo 880569 1487713 := bstep (se 2 (by rfl) ⟨557892, by rfl⟩ : syracuseStep 1487713 = 1115785) B1115785
theorem B1323875 : Blo 880569 1323875 := bstep (se 1 (by rfl) ⟨992906, by rfl⟩ : syracuseStep 1323875 = 1985813) B1985813
theorem B1323905 : Blo 880569 1323905 := bstep (se 2 (by rfl) ⟨496464, by rfl⟩ : syracuseStep 1323905 = 992929) B992929
theorem B1487747 : Blo 880569 1487747 := bstep (se 1 (by rfl) ⟨1115810, by rfl⟩ : syracuseStep 1487747 = 2231621) B2231621
theorem B1323923 : Blo 880569 1323923 := bstep (se 1 (by rfl) ⟨992942, by rfl⟩ : syracuseStep 1323923 = 1985885) B1985885
theorem B1323953 : Blo 880569 1323953 := bstep (se 2 (by rfl) ⟨496482, by rfl⟩ : syracuseStep 1323953 = 992965) B992965
theorem B1323971 : Blo 880569 1323971 := bstep (se 1 (by rfl) ⟨992978, by rfl⟩ : syracuseStep 1323971 = 1985957) B1985957
theorem B1324001 : Blo 880569 1324001 := bstep (se 2 (by rfl) ⟨496500, by rfl⟩ : syracuseStep 1324001 = 993001) B993001
theorem B1913827 : Blo 880569 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B1324019 : Blo 880569 1324019 := bstep (se 1 (by rfl) ⟨993014, by rfl⟩ : syracuseStep 1324019 = 1986029) B1986029
theorem B1487875 : Blo 880569 1487875 := bstep (se 1 (by rfl) ⟨1115906, by rfl⟩ : syracuseStep 1487875 = 2231813) B2231813
theorem B1324049 : Blo 880569 1324049 := bstep (se 2 (by rfl) ⟨496518, by rfl⟩ : syracuseStep 1324049 = 993037) B993037
theorem B1324067 : Blo 880569 1324067 := bstep (se 1 (by rfl) ⟨993050, by rfl⟩ : syracuseStep 1324067 = 1986101) B1986101
theorem B1324097 : Blo 880569 1324097 := bstep (se 2 (by rfl) ⟨496536, by rfl⟩ : syracuseStep 1324097 = 993073) B993073
theorem B1324115 : Blo 880569 1324115 := bstep (se 1 (by rfl) ⟨993086, by rfl⟩ : syracuseStep 1324115 = 1986173) B1986173
theorem B1324145 : Blo 880569 1324145 := bstep (se 2 (by rfl) ⟨496554, by rfl⟩ : syracuseStep 1324145 = 993109) B993109
theorem B1324163 : Blo 880569 1324163 := bstep (se 1 (by rfl) ⟨993122, by rfl⟩ : syracuseStep 1324163 = 1986245) B1986245
theorem B1488017 : Blo 880569 1488017 := bstep (se 2 (by rfl) ⟨558006, by rfl⟩ : syracuseStep 1488017 = 1116013) B1116013
theorem B1324193 : Blo 880569 1324193 := bstep (se 2 (by rfl) ⟨496572, by rfl⟩ : syracuseStep 1324193 = 993145) B993145
theorem B1881265 : Blo 880569 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B1324211 : Blo 880569 1324211 := bstep (se 1 (by rfl) ⟨993158, by rfl⟩ : syracuseStep 1324211 = 1986317) B1986317
theorem B1324241 : Blo 880569 1324241 := bstep (se 2 (by rfl) ⟨496590, by rfl⟩ : syracuseStep 1324241 = 993181) B993181
theorem B1324259 : Blo 880569 1324259 := bstep (se 1 (by rfl) ⟨993194, by rfl⟩ : syracuseStep 1324259 = 1986389) B1986389
theorem B1324289 : Blo 880569 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B1488145 : Blo 880569 1488145 := bstep (se 2 (by rfl) ⟨558054, by rfl⟩ : syracuseStep 1488145 = 1116109) B1116109
theorem B1324307 : Blo 880569 1324307 := bstep (se 1 (by rfl) ⟨993230, by rfl⟩ : syracuseStep 1324307 = 1986461) B1986461
theorem B1324337 : Blo 880569 1324337 := bstep (se 2 (by rfl) ⟨496626, by rfl⟩ : syracuseStep 1324337 = 993253) B993253
theorem B4470065 : Blo 880569 4470065 := bstep (se 2 (by rfl) ⟨1676274, by rfl⟩ : syracuseStep 4470065 = 3352549) B3352549
theorem B1488179 : Blo 880569 1488179 := bstep (se 1 (by rfl) ⟨1116134, by rfl⟩ : syracuseStep 1488179 = 2232269) B2232269
theorem B1324355 : Blo 880569 1324355 := bstep (se 1 (by rfl) ⟨993266, by rfl⟩ : syracuseStep 1324355 = 1986533) B1986533
theorem B1193299 : Blo 880569 1193299 := bstep (se 1 (by rfl) ⟨894974, by rfl⟩ : syracuseStep 1193299 = 1789949) B1789949
theorem B1324385 : Blo 880569 1324385 := bstep (se 2 (by rfl) ⟨496644, by rfl⟩ : syracuseStep 1324385 = 993289) B993289
theorem B1324403 : Blo 880569 1324403 := bstep (se 1 (by rfl) ⟨993302, by rfl⟩ : syracuseStep 1324403 = 1986605) B1986605
theorem B2012561 : Blo 880569 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B1324433 : Blo 880569 1324433 := bstep (se 2 (by rfl) ⟨496662, by rfl⟩ : syracuseStep 1324433 = 993325) B993325
theorem B1324451 : Blo 880569 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B1258915 : Blo 880569 1258915 := bstep (se 1 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 1258915 = 1888373) B1888373
theorem B5649841 : Blo 880569 5649841 := bstep (se 2 (by rfl) ⟨2118690, by rfl⟩ : syracuseStep 5649841 = 4237381) B4237381
theorem B1488307 : Blo 880569 1488307 := bstep (se 1 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 1488307 = 2232461) B2232461
theorem B1324481 : Blo 880569 1324481 := bstep (se 2 (by rfl) ⟨496680, by rfl⟩ : syracuseStep 1324481 = 993361) B993361
theorem B1324499 : Blo 880569 1324499 := bstep (se 1 (by rfl) ⟨993374, by rfl⟩ : syracuseStep 1324499 = 1986749) B1986749
theorem B1324529 : Blo 880569 1324529 := bstep (se 2 (by rfl) ⟨496698, by rfl⟩ : syracuseStep 1324529 = 993397) B993397
theorem B1324547 : Blo 880569 1324547 := bstep (se 1 (by rfl) ⟨993410, by rfl⟩ : syracuseStep 1324547 = 1986821) B1986821
theorem B1324577 : Blo 880569 1324577 := bstep (se 2 (by rfl) ⟨496716, by rfl⟩ : syracuseStep 1324577 = 993433) B993433
theorem B1324595 : Blo 880569 1324595 := bstep (se 1 (by rfl) ⟨993446, by rfl⟩ : syracuseStep 1324595 = 1986893) B1986893
theorem B1488449 : Blo 880569 1488449 := bstep (se 2 (by rfl) ⟨558168, by rfl⟩ : syracuseStep 1488449 = 1116337) B1116337
theorem B1324625 : Blo 880569 1324625 := bstep (se 2 (by rfl) ⟨496734, by rfl⟩ : syracuseStep 1324625 = 993469) B993469
theorem B1324643 : Blo 880569 1324643 := bstep (se 1 (by rfl) ⟨993482, by rfl⟩ : syracuseStep 1324643 = 1986965) B1986965
theorem B1324673 : Blo 880569 1324673 := bstep (se 2 (by rfl) ⟨496752, by rfl⟩ : syracuseStep 1324673 = 993505) B993505
theorem B1324691 : Blo 880569 1324691 := bstep (se 1 (by rfl) ⟨993518, by rfl⟩ : syracuseStep 1324691 = 1987037) B1987037
theorem B1324721 : Blo 880569 1324721 := bstep (se 2 (by rfl) ⟨496770, by rfl⟩ : syracuseStep 1324721 = 993541) B993541
theorem B1488577 : Blo 880569 1488577 := bstep (se 2 (by rfl) ⟨558216, by rfl⟩ : syracuseStep 1488577 = 1116433) B1116433
theorem B1324739 : Blo 880569 1324739 := bstep (se 1 (by rfl) ⟨993554, by rfl⟩ : syracuseStep 1324739 = 1987109) B1987109
theorem B1324769 : Blo 880569 1324769 := bstep (se 2 (by rfl) ⟨496788, by rfl⟩ : syracuseStep 1324769 = 993577) B993577
theorem B1488611 : Blo 880569 1488611 := bstep (se 1 (by rfl) ⟨1116458, by rfl⟩ : syracuseStep 1488611 = 2232917) B2232917
theorem B1324787 : Blo 880569 1324787 := bstep (se 1 (by rfl) ⟨993590, by rfl⟩ : syracuseStep 1324787 = 1987181) B1987181
theorem B1324817 : Blo 880569 1324817 := bstep (se 2 (by rfl) ⟨496806, by rfl⟩ : syracuseStep 1324817 = 993613) B993613
theorem B1324835 : Blo 880569 1324835 := bstep (se 1 (by rfl) ⟨993626, by rfl⟩ : syracuseStep 1324835 = 1987253) B1987253
theorem B1324865 : Blo 880569 1324865 := bstep (se 2 (by rfl) ⟨496824, by rfl⟩ : syracuseStep 1324865 = 993649) B993649
theorem B1718083 : Blo 880569 1718083 := bstep (se 1 (by rfl) ⟨1288562, by rfl⟩ : syracuseStep 1718083 = 2577125) B2577125
theorem B1324883 : Blo 880569 1324883 := bstep (se 1 (by rfl) ⟨993662, by rfl⟩ : syracuseStep 1324883 = 1987325) B1987325
theorem B1488739 : Blo 880569 1488739 := bstep (se 1 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 1488739 = 2233109) B2233109
theorem B1324913 : Blo 880569 1324913 := bstep (se 2 (by rfl) ⟨496842, by rfl⟩ : syracuseStep 1324913 = 993685) B993685
theorem B1259393 : Blo 880569 1259393 := bstep (se 2 (by rfl) ⟨472272, by rfl⟩ : syracuseStep 1259393 = 944545) B944545
theorem B1324931 : Blo 880569 1324931 := bstep (se 1 (by rfl) ⟨993698, by rfl⟩ : syracuseStep 1324931 = 1987397) B1987397
theorem B1324961 : Blo 880569 1324961 := bstep (se 2 (by rfl) ⟨496860, by rfl⟩ : syracuseStep 1324961 = 993721) B993721
theorem B1324979 : Blo 880569 1324979 := bstep (se 1 (by rfl) ⟨993734, by rfl⟩ : syracuseStep 1324979 = 1987469) B1987469
theorem B1325009 : Blo 880569 1325009 := bstep (se 2 (by rfl) ⟨496878, by rfl⟩ : syracuseStep 1325009 = 993757) B993757
theorem B1325027 : Blo 880569 1325027 := bstep (se 1 (by rfl) ⟨993770, by rfl⟩ : syracuseStep 1325027 = 1987541) B1987541
theorem B1488881 : Blo 880569 1488881 := bstep (se 2 (by rfl) ⟨558330, by rfl⟩ : syracuseStep 1488881 = 1116661) B1116661
theorem B1325057 : Blo 880569 1325057 := bstep (se 2 (by rfl) ⟨496896, by rfl⟩ : syracuseStep 1325057 = 993793) B993793
theorem B1325075 : Blo 880569 1325075 := bstep (se 1 (by rfl) ⟨993806, by rfl⟩ : syracuseStep 1325075 = 1987613) B1987613
theorem B3389489 : Blo 880569 3389489 := bstep (se 2 (by rfl) ⟨1271058, by rfl⟩ : syracuseStep 3389489 = 2542117) B2542117
theorem B1325105 : Blo 880569 1325105 := bstep (se 2 (by rfl) ⟨496914, by rfl⟩ : syracuseStep 1325105 = 993829) B993829
theorem B1325123 : Blo 880569 1325123 := bstep (se 1 (by rfl) ⟨993842, by rfl⟩ : syracuseStep 1325123 = 1987685) B1987685
theorem B11319365 : Blo 880569 11319365 := bstep (se 4 (by rfl) ⟨1061190, by rfl⟩ : syracuseStep 11319365 = 2122381) B2122381
theorem B2865233 : Blo 880569 2865233 := bstep (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) B2148925
theorem B1325153 : Blo 880569 1325153 := bstep (se 2 (by rfl) ⟨496932, by rfl⟩ : syracuseStep 1325153 = 993865) B993865
theorem B1489009 : Blo 880569 1489009 := bstep (se 2 (by rfl) ⟨558378, by rfl⟩ : syracuseStep 1489009 = 1116757) B1116757
theorem B1325171 : Blo 880569 1325171 := bstep (se 1 (by rfl) ⟨993878, by rfl⟩ : syracuseStep 1325171 = 1987757) B1987757
theorem B1325201 : Blo 880569 1325201 := bstep (se 2 (by rfl) ⟨496950, by rfl⟩ : syracuseStep 1325201 = 993901) B993901
theorem B1489043 : Blo 880569 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B1325219 : Blo 880569 1325219 := bstep (se 1 (by rfl) ⟨993914, by rfl⟩ : syracuseStep 1325219 = 1987829) B1987829
theorem B1325249 : Blo 880569 1325249 := bstep (se 2 (by rfl) ⟨496968, by rfl⟩ : syracuseStep 1325249 = 993937) B993937
theorem B1325267 : Blo 880569 1325267 := bstep (se 1 (by rfl) ⟨993950, by rfl⟩ : syracuseStep 1325267 = 1987901) B1987901
theorem B1325297 : Blo 880569 1325297 := bstep (se 2 (by rfl) ⟨496986, by rfl⟩ : syracuseStep 1325297 = 993973) B993973
theorem B1325315 : Blo 880569 1325315 := bstep (se 1 (by rfl) ⟨993986, by rfl⟩ : syracuseStep 1325315 = 1987973) B1987973
theorem B1489171 : Blo 880569 1489171 := bstep (se 1 (by rfl) ⟨1116878, by rfl⟩ : syracuseStep 1489171 = 2233757) B2233757
theorem B1325345 : Blo 880569 1325345 := bstep (se 2 (by rfl) ⟨497004, by rfl⟩ : syracuseStep 1325345 = 994009) B994009
theorem B1325363 : Blo 880569 1325363 := bstep (se 1 (by rfl) ⟨994022, by rfl⟩ : syracuseStep 1325363 = 1988045) B1988045
theorem B1325393 : Blo 880569 1325393 := bstep (se 2 (by rfl) ⟨497022, by rfl⟩ : syracuseStep 1325393 = 994045) B994045
theorem B1325411 : Blo 880569 1325411 := bstep (se 1 (by rfl) ⟨994058, by rfl⟩ : syracuseStep 1325411 = 1988117) B1988117
theorem B1194355 : Blo 880569 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B1325441 : Blo 880569 1325441 := bstep (se 2 (by rfl) ⟨497040, by rfl⟩ : syracuseStep 1325441 = 994081) B994081
theorem B1325459 : Blo 880569 1325459 := bstep (se 1 (by rfl) ⟨994094, by rfl⟩ : syracuseStep 1325459 = 1988189) B1988189
theorem B1489313 : Blo 880569 1489313 := bstep (se 2 (by rfl) ⟨558492, by rfl⟩ : syracuseStep 1489313 = 1116985) B1116985
theorem B2832803 : Blo 880569 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B1325489 : Blo 880569 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B1325507 : Blo 880569 1325507 := bstep (se 1 (by rfl) ⟨994130, by rfl⟩ : syracuseStep 1325507 = 1988261) B1988261
theorem B1325537 : Blo 880569 1325537 := bstep (se 2 (by rfl) ⟨497076, by rfl⟩ : syracuseStep 1325537 = 994153) B994153
theorem B1325555 : Blo 880569 1325555 := bstep (se 1 (by rfl) ⟨994166, by rfl⟩ : syracuseStep 1325555 = 1988333) B1988333
theorem B3357197 : Blo 880569 3357197 := bstep (se 3 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 3357197 = 1258949) B1258949
theorem B1325585 : Blo 880569 1325585 := bstep (se 2 (by rfl) ⟨497094, by rfl⟩ : syracuseStep 1325585 = 994189) B994189
theorem B1489441 : Blo 880569 1489441 := bstep (se 2 (by rfl) ⟨558540, by rfl⟩ : syracuseStep 1489441 = 1117081) B1117081
theorem B1325603 : Blo 880569 1325603 := bstep (se 1 (by rfl) ⟨994202, by rfl⟩ : syracuseStep 1325603 = 1988405) B1988405
theorem B1325633 : Blo 880569 1325633 := bstep (se 2 (by rfl) ⟨497112, by rfl⟩ : syracuseStep 1325633 = 994225) B994225
theorem B1489475 : Blo 880569 1489475 := bstep (se 1 (by rfl) ⟨1117106, by rfl⟩ : syracuseStep 1489475 = 2234213) B2234213
theorem B1325651 : Blo 880569 1325651 := bstep (se 1 (by rfl) ⟨994238, by rfl⟩ : syracuseStep 1325651 = 1988477) B1988477
theorem B1325681 : Blo 880569 1325681 := bstep (se 2 (by rfl) ⟨497130, by rfl⟩ : syracuseStep 1325681 = 994261) B994261
theorem B1325699 : Blo 880569 1325699 := bstep (se 1 (by rfl) ⟨994274, by rfl⟩ : syracuseStep 1325699 = 1988549) B1988549
theorem B1325729 : Blo 880569 1325729 := bstep (se 2 (by rfl) ⟨497148, by rfl⟩ : syracuseStep 1325729 = 994297) B994297
theorem B1325747 : Blo 880569 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B1489603 : Blo 880569 1489603 := bstep (se 1 (by rfl) ⟨1117202, by rfl⟩ : syracuseStep 1489603 = 2234405) B2234405
theorem B1325777 : Blo 880569 1325777 := bstep (se 2 (by rfl) ⟨497166, by rfl⟩ : syracuseStep 1325777 = 994333) B994333
theorem B4471523 : Blo 880569 4471523 := bstep (se 1 (by rfl) ⟨3353642, by rfl⟩ : syracuseStep 4471523 = 6707285) B6707285
theorem B1325795 : Blo 880569 1325795 := bstep (se 1 (by rfl) ⟨994346, by rfl⟩ : syracuseStep 1325795 = 1988693) B1988693
theorem B1325825 : Blo 880569 1325825 := bstep (se 2 (by rfl) ⟨497184, by rfl⟩ : syracuseStep 1325825 = 994369) B994369
theorem B1325843 : Blo 880569 1325843 := bstep (se 1 (by rfl) ⟨994382, by rfl⟩ : syracuseStep 1325843 = 1988765) B1988765
theorem B1325873 : Blo 880569 1325873 := bstep (se 2 (by rfl) ⟨497202, by rfl⟩ : syracuseStep 1325873 = 994405) B994405
theorem B1325891 : Blo 880569 1325891 := bstep (se 1 (by rfl) ⟨994418, by rfl⟩ : syracuseStep 1325891 = 1988837) B1988837
theorem B1489745 : Blo 880569 1489745 := bstep (se 2 (by rfl) ⟨558654, by rfl⟩ : syracuseStep 1489745 = 1117309) B1117309
theorem B1325921 : Blo 880569 1325921 := bstep (se 2 (by rfl) ⟨497220, by rfl⟩ : syracuseStep 1325921 = 994441) B994441
theorem B1325939 : Blo 880569 1325939 := bstep (se 1 (by rfl) ⟨994454, by rfl⟩ : syracuseStep 1325939 = 1988909) B1988909
theorem B1325969 : Blo 880569 1325969 := bstep (se 2 (by rfl) ⟨497238, by rfl⟩ : syracuseStep 1325969 = 994477) B994477
theorem B1325987 : Blo 880569 1325987 := bstep (se 1 (by rfl) ⟨994490, by rfl⟩ : syracuseStep 1325987 = 1988981) B1988981
theorem B1326017 : Blo 880569 1326017 := bstep (se 2 (by rfl) ⟨497256, by rfl⟩ : syracuseStep 1326017 = 994513) B994513
theorem B1489873 : Blo 880569 1489873 := bstep (se 2 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 1489873 = 1117405) B1117405
theorem B1326035 : Blo 880569 1326035 := bstep (se 1 (by rfl) ⟨994526, by rfl⟩ : syracuseStep 1326035 = 1989053) B1989053
theorem B1326065 : Blo 880569 1326065 := bstep (se 2 (by rfl) ⟨497274, by rfl⟩ : syracuseStep 1326065 = 994549) B994549
theorem B1489907 : Blo 880569 1489907 := bstep (se 1 (by rfl) ⟨1117430, by rfl⟩ : syracuseStep 1489907 = 2234861) B2234861
theorem B1326083 : Blo 880569 1326083 := bstep (se 1 (by rfl) ⟨994562, by rfl⟩ : syracuseStep 1326083 = 1989125) B1989125
theorem B1981457 : Blo 880569 1981457 := bstep (se 2 (by rfl) ⟨743046, by rfl⟩ : syracuseStep 1981457 = 1486093) B1486093
theorem B1588241 : Blo 880569 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B1326113 : Blo 880569 1326113 := bstep (se 2 (by rfl) ⟨497292, by rfl⟩ : syracuseStep 1326113 = 994585) B994585
theorem B1981475 : Blo 880569 1981475 := bstep (se 1 (by rfl) ⟨1486106, by rfl⟩ : syracuseStep 1981475 = 2972213) B2972213
theorem B1326131 : Blo 880569 1326131 := bstep (se 1 (by rfl) ⟨994598, by rfl⟩ : syracuseStep 1326131 = 1989197) B1989197
theorem B5356613 : Blo 880569 5356613 := bstep (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) B1004365
theorem B1326161 : Blo 880569 1326161 := bstep (se 2 (by rfl) ⟨497310, by rfl⟩ : syracuseStep 1326161 = 994621) B994621
theorem B1326179 : Blo 880569 1326179 := bstep (se 1 (by rfl) ⟨994634, by rfl⟩ : syracuseStep 1326179 = 1989269) B1989269
theorem B6438001 : Blo 880569 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B1490035 : Blo 880569 1490035 := bstep (se 1 (by rfl) ⟨1117526, by rfl⟩ : syracuseStep 1490035 = 2235053) B2235053
theorem B1326209 : Blo 880569 1326209 := bstep (se 2 (by rfl) ⟨497328, by rfl⟩ : syracuseStep 1326209 = 994657) B994657
theorem B1326227 : Blo 880569 1326227 := bstep (se 1 (by rfl) ⟨994670, by rfl⟩ : syracuseStep 1326227 = 1989341) B1989341
theorem B1326257 : Blo 880569 1326257 := bstep (se 2 (by rfl) ⟨497346, by rfl⟩ : syracuseStep 1326257 = 994693) B994693
theorem B1326275 : Blo 880569 1326275 := bstep (se 1 (by rfl) ⟨994706, by rfl⟩ : syracuseStep 1326275 = 1989413) B1989413
theorem B1326305 : Blo 880569 1326305 := bstep (se 2 (by rfl) ⟨497364, by rfl⟩ : syracuseStep 1326305 = 994729) B994729
theorem B1326323 : Blo 880569 1326323 := bstep (se 1 (by rfl) ⟨994742, by rfl⟩ : syracuseStep 1326323 = 1989485) B1989485
theorem B1490177 : Blo 880569 1490177 := bstep (se 2 (by rfl) ⟨558816, by rfl⟩ : syracuseStep 1490177 = 1117633) B1117633
theorem B1195267 : Blo 880569 1195267 := bstep (se 1 (by rfl) ⟨896450, by rfl⟩ : syracuseStep 1195267 = 1792901) B1792901
theorem B1326353 : Blo 880569 1326353 := bstep (se 2 (by rfl) ⟨497382, by rfl⟩ : syracuseStep 1326353 = 994765) B994765
theorem B2145571 : Blo 880569 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B1326371 : Blo 880569 1326371 := bstep (se 1 (by rfl) ⟨994778, by rfl⟩ : syracuseStep 1326371 = 1989557) B1989557
theorem B1981745 : Blo 880569 1981745 := bstep (se 2 (by rfl) ⟨743154, by rfl⟩ : syracuseStep 1981745 = 1486309) B1486309
theorem B1326401 : Blo 880569 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B1981763 : Blo 880569 1981763 := bstep (se 1 (by rfl) ⟨1486322, by rfl⟩ : syracuseStep 1981763 = 2972645) B2972645
theorem B1326419 : Blo 880569 1326419 := bstep (se 1 (by rfl) ⟨994814, by rfl⟩ : syracuseStep 1326419 = 1989629) B1989629
theorem B1326449 : Blo 880569 1326449 := bstep (se 2 (by rfl) ⟨497418, by rfl⟩ : syracuseStep 1326449 = 994837) B994837
theorem B1490305 : Blo 880569 1490305 := bstep (se 2 (by rfl) ⟨558864, by rfl⟩ : syracuseStep 1490305 = 1117729) B1117729
theorem B1195393 : Blo 880569 1195393 := bstep (se 2 (by rfl) ⟨448272, by rfl⟩ : syracuseStep 1195393 = 896545) B896545
theorem B1326467 : Blo 880569 1326467 := bstep (se 1 (by rfl) ⟨994850, by rfl⟩ : syracuseStep 1326467 = 1989701) B1989701
theorem B1326497 : Blo 880569 1326497 := bstep (se 2 (by rfl) ⟨497436, by rfl⟩ : syracuseStep 1326497 = 994873) B994873
theorem B1490339 : Blo 880569 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B1326515 : Blo 880569 1326515 := bstep (se 1 (by rfl) ⟨994886, by rfl⟩ : syracuseStep 1326515 = 1989773) B1989773
theorem B12729797 : Blo 880569 12729797 := bstep (se 4 (by rfl) ⟨1193418, by rfl⟩ : syracuseStep 12729797 = 2386837) B2386837
theorem B1326545 : Blo 880569 1326545 := bstep (se 2 (by rfl) ⟨497454, by rfl⟩ : syracuseStep 1326545 = 994909) B994909
theorem B1326563 : Blo 880569 1326563 := bstep (se 1 (by rfl) ⟨994922, by rfl⟩ : syracuseStep 1326563 = 1989845) B1989845
theorem B1326593 : Blo 880569 1326593 := bstep (se 2 (by rfl) ⟨497472, by rfl⟩ : syracuseStep 1326593 = 994945) B994945
theorem B4472333 : Blo 880569 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B1326611 : Blo 880569 1326611 := bstep (se 1 (by rfl) ⟨994958, by rfl⟩ : syracuseStep 1326611 = 1989917) B1989917
theorem B1490467 : Blo 880569 1490467 := bstep (se 1 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 1490467 = 2235701) B2235701
theorem B1326641 : Blo 880569 1326641 := bstep (se 2 (by rfl) ⟨497490, by rfl⟩ : syracuseStep 1326641 = 994981) B994981
theorem B1326659 : Blo 880569 1326659 := bstep (se 1 (by rfl) ⟨994994, by rfl⟩ : syracuseStep 1326659 = 1989989) B1989989
theorem B1982033 : Blo 880569 1982033 := bstep (se 2 (by rfl) ⟨743262, by rfl⟩ : syracuseStep 1982033 = 1486525) B1486525
theorem B1326689 : Blo 880569 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B1982051 : Blo 880569 1982051 := bstep (se 1 (by rfl) ⟨1486538, by rfl⟩ : syracuseStep 1982051 = 2973077) B2973077
theorem B8470115 : Blo 880569 8470115 := bstep (se 1 (by rfl) ⟨6352586, by rfl⟩ : syracuseStep 8470115 = 12705173) B12705173
theorem B1326707 : Blo 880569 1326707 := bstep (se 1 (by rfl) ⟨995030, by rfl⟩ : syracuseStep 1326707 = 1990061) B1990061
theorem B1326737 : Blo 880569 1326737 := bstep (se 2 (by rfl) ⟨497526, by rfl⟩ : syracuseStep 1326737 = 995053) B995053
theorem B1326755 : Blo 880569 1326755 := bstep (se 1 (by rfl) ⟨995066, by rfl⟩ : syracuseStep 1326755 = 1990133) B1990133
theorem B5029553 : Blo 880569 5029553 := bstep (se 2 (by rfl) ⟨1886082, by rfl⟩ : syracuseStep 5029553 = 3772165) B3772165
theorem B1490609 : Blo 880569 1490609 := bstep (se 2 (by rfl) ⟨558978, by rfl⟩ : syracuseStep 1490609 = 1117957) B1117957
theorem B2014897 : Blo 880569 2014897 := bstep (se 2 (by rfl) ⟨755586, by rfl⟩ : syracuseStep 2014897 = 1511173) B1511173
theorem B1326785 : Blo 880569 1326785 := bstep (se 2 (by rfl) ⟨497544, by rfl⟩ : syracuseStep 1326785 = 995089) B995089
theorem B1326803 : Blo 880569 1326803 := bstep (se 1 (by rfl) ⟨995102, by rfl⟩ : syracuseStep 1326803 = 1990205) B1990205
theorem B2014961 : Blo 880569 2014961 := bstep (se 2 (by rfl) ⟨755610, by rfl⟩ : syracuseStep 2014961 = 1511221) B1511221
theorem B1326833 : Blo 880569 1326833 := bstep (se 2 (by rfl) ⟨497562, by rfl⟩ : syracuseStep 1326833 = 995125) B995125
theorem B1326851 : Blo 880569 1326851 := bstep (se 1 (by rfl) ⟨995138, by rfl⟩ : syracuseStep 1326851 = 1990277) B1990277
theorem B1490737 : Blo 880569 1490737 := bstep (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) B1118053
theorem B1490771 : Blo 880569 1490771 := bstep (se 1 (by rfl) ⟨1118078, by rfl⟩ : syracuseStep 1490771 = 2236157) B2236157
theorem B1982321 : Blo 880569 1982321 := bstep (se 2 (by rfl) ⟨743370, by rfl⟩ : syracuseStep 1982321 = 1486741) B1486741
theorem B1982339 : Blo 880569 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B1490899 : Blo 880569 1490899 := bstep (se 1 (by rfl) ⟨1118174, by rfl⟩ : syracuseStep 1490899 = 2236349) B2236349
theorem B1491041 : Blo 880569 1491041 := bstep (se 2 (by rfl) ⟨559140, by rfl⟩ : syracuseStep 1491041 = 1118281) B1118281
theorem B1982609 : Blo 880569 1982609 := bstep (se 2 (by rfl) ⟨743478, by rfl⟩ : syracuseStep 1982609 = 1486957) B1486957
theorem B1982627 : Blo 880569 1982627 := bstep (se 1 (by rfl) ⟨1486970, by rfl⟩ : syracuseStep 1982627 = 2973941) B2973941
theorem B1884323 : Blo 880569 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B1491169 : Blo 880569 1491169 := bstep (se 2 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 1491169 = 1118377) B1118377
theorem B1491203 : Blo 880569 1491203 := bstep (se 1 (by rfl) ⟨1118402, by rfl⟩ : syracuseStep 1491203 = 2236805) B2236805
theorem B1491331 : Blo 880569 1491331 := bstep (se 1 (by rfl) ⟨1118498, by rfl⟩ : syracuseStep 1491331 = 2236997) B2236997
theorem B6701453 : Blo 880569 6701453 := bstep (se 3 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 6701453 = 2513045) B2513045
theorem B1982897 : Blo 880569 1982897 := bstep (se 2 (by rfl) ⟨743586, by rfl⟩ : syracuseStep 1982897 = 1487173) B1487173
theorem B1982915 : Blo 880569 1982915 := bstep (se 1 (by rfl) ⟨1487186, by rfl⟩ : syracuseStep 1982915 = 2974373) B2974373
theorem B14336453 : Blo 880569 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B1491473 : Blo 880569 1491473 := bstep (se 2 (by rfl) ⟨559302, by rfl⟩ : syracuseStep 1491473 = 1118605) B1118605
theorem B1491601 : Blo 880569 1491601 := bstep (se 2 (by rfl) ⟨559350, by rfl⟩ : syracuseStep 1491601 = 1118701) B1118701
theorem B1491635 : Blo 880569 1491635 := bstep (se 1 (by rfl) ⟨1118726, by rfl⟩ : syracuseStep 1491635 = 2237453) B2237453
theorem B1983185 : Blo 880569 1983185 := bstep (se 2 (by rfl) ⟨743694, by rfl⟩ : syracuseStep 1983185 = 1487389) B1487389
theorem B1983203 : Blo 880569 1983203 := bstep (se 1 (by rfl) ⟨1487402, by rfl⟩ : syracuseStep 1983203 = 2974805) B2974805
theorem B1786673 : Blo 880569 1786673 := bstep (se 2 (by rfl) ⟨670002, by rfl⟩ : syracuseStep 1786673 = 1340005) B1340005
theorem B1491763 : Blo 880569 1491763 := bstep (se 1 (by rfl) ⟨1118822, by rfl⟩ : syracuseStep 1491763 = 2237645) B2237645
theorem B1786691 : Blo 880569 1786691 := bstep (se 1 (by rfl) ⟨1340018, by rfl⟩ : syracuseStep 1786691 = 2680037) B2680037
theorem B1491905 : Blo 880569 1491905 := bstep (se 2 (by rfl) ⟨559464, by rfl⟩ : syracuseStep 1491905 = 1118929) B1118929
theorem B1983473 : Blo 880569 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1983491 : Blo 880569 1983491 := bstep (se 1 (by rfl) ⟨1487618, by rfl⟩ : syracuseStep 1983491 = 2975237) B2975237
theorem B1885187 : Blo 880569 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B1492033 : Blo 880569 1492033 := bstep (se 2 (by rfl) ⟨559512, by rfl⟩ : syracuseStep 1492033 = 1119025) B1119025
theorem B5031011 : Blo 880569 5031011 := bstep (se 1 (by rfl) ⟨3773258, by rfl⟩ : syracuseStep 5031011 = 7546517) B7546517
theorem B1492067 : Blo 880569 1492067 := bstep (se 1 (by rfl) ⟨1119050, by rfl⟩ : syracuseStep 1492067 = 2238101) B2238101
theorem B1885297 : Blo 880569 1885297 := bstep (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) B1413973
theorem B5653637 : Blo 880569 5653637 := bstep (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) B1060057
theorem B1492195 : Blo 880569 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B1983761 : Blo 880569 1983761 := bstep (se 2 (by rfl) ⟨743910, by rfl⟩ : syracuseStep 1983761 = 1487821) B1487821
theorem B1983779 : Blo 880569 1983779 := bstep (se 1 (by rfl) ⟨1487834, by rfl⟩ : syracuseStep 1983779 = 2975669) B2975669
theorem B1492337 : Blo 880569 1492337 := bstep (se 2 (by rfl) ⟨559626, by rfl⟩ : syracuseStep 1492337 = 1119253) B1119253
theorem B1590691 : Blo 880569 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B4244899 : Blo 880569 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B2508205 : Blo 880569 2508205 := bstep (se 3 (by rfl) ⟨470288, by rfl⟩ : syracuseStep 2508205 = 940577) B940577
theorem B1492465 : Blo 880569 1492465 := bstep (se 2 (by rfl) ⟨559674, by rfl⟩ : syracuseStep 1492465 = 1119349) B1119349
theorem B1492499 : Blo 880569 1492499 := bstep (se 1 (by rfl) ⟨1119374, by rfl⟩ : syracuseStep 1492499 = 2238749) B2238749
theorem B1984049 : Blo 880569 1984049 := bstep (se 2 (by rfl) ⟨744018, by rfl⟩ : syracuseStep 1984049 = 1488037) B1488037
theorem B1984067 : Blo 880569 1984067 := bstep (se 1 (by rfl) ⟨1488050, by rfl⟩ : syracuseStep 1984067 = 2976101) B2976101
theorem B1492627 : Blo 880569 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B1984337 : Blo 880569 1984337 := bstep (se 2 (by rfl) ⟨744126, by rfl⟩ : syracuseStep 1984337 = 1488253) B1488253
theorem B1984355 : Blo 880569 1984355 := bstep (se 1 (by rfl) ⟨1488266, by rfl⟩ : syracuseStep 1984355 = 2976533) B2976533
theorem B5359729 : Blo 880569 5359729 := bstep (se 2 (by rfl) ⟨2009898, by rfl⟩ : syracuseStep 5359729 = 4019797) B4019797
theorem B1984625 : Blo 880569 1984625 := bstep (se 2 (by rfl) ⟨744234, by rfl⟩ : syracuseStep 1984625 = 1488469) B1488469
theorem B1984643 : Blo 880569 1984643 := bstep (se 1 (by rfl) ⟨1488482, by rfl⟩ : syracuseStep 1984643 = 2976965) B2976965
theorem B4475249 : Blo 880569 4475249 := bstep (se 2 (by rfl) ⟨1678218, by rfl⟩ : syracuseStep 4475249 = 3356437) B3356437
theorem B1984913 : Blo 880569 1984913 := bstep (se 2 (by rfl) ⟨744342, by rfl⟩ : syracuseStep 1984913 = 1488685) B1488685
theorem B1984931 : Blo 880569 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B2116145 : Blo 880569 2116145 := bstep (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) B1587109
theorem B1985201 : Blo 880569 1985201 := bstep (se 2 (by rfl) ⟨744450, by rfl⟩ : syracuseStep 1985201 = 1488901) B1488901
theorem B1985219 : Blo 880569 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B1985489 : Blo 880569 1985489 := bstep (se 2 (by rfl) ⟨744558, by rfl⟩ : syracuseStep 1985489 = 1489117) B1489117
theorem B1985507 : Blo 880569 1985507 := bstep (se 1 (by rfl) ⟨1489130, by rfl⟩ : syracuseStep 1985507 = 2978261) B2978261
theorem B3820621 : Blo 880569 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B1887313 : Blo 880569 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B2509937 : Blo 880569 2509937 := bstep (se 2 (by rfl) ⟨941226, by rfl⟩ : syracuseStep 2509937 = 1882453) B1882453
theorem B8473841 : Blo 880569 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B1985777 : Blo 880569 1985777 := bstep (se 2 (by rfl) ⟨744666, by rfl⟩ : syracuseStep 1985777 = 1489333) B1489333
theorem B6704369 : Blo 880569 6704369 := bstep (se 2 (by rfl) ⟨2514138, by rfl⟩ : syracuseStep 6704369 = 5028277) B5028277
theorem B1985795 : Blo 880569 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B2510129 : Blo 880569 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B10177973 : Blo 880569 10177973 := bstep (se 5 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 10177973 = 954185) B954185
theorem B1887715 : Blo 880569 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B1986065 : Blo 880569 1986065 := bstep (se 2 (by rfl) ⟨744774, by rfl⟩ : syracuseStep 1986065 = 1489549) B1489549
theorem B1986083 : Blo 880569 1986083 := bstep (se 1 (by rfl) ⟨1489562, by rfl⟩ : syracuseStep 1986083 = 2979125) B2979125
theorem B4476707 : Blo 880569 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B1986353 : Blo 880569 1986353 := bstep (se 2 (by rfl) ⟨744882, by rfl⟩ : syracuseStep 1986353 = 1489765) B1489765
theorem B1986371 : Blo 880569 1986371 := bstep (se 1 (by rfl) ⟨1489778, by rfl⟩ : syracuseStep 1986371 = 2979557) B2979557
theorem B1986641 : Blo 880569 1986641 := bstep (se 2 (by rfl) ⟨744990, by rfl⟩ : syracuseStep 1986641 = 1489981) B1489981
theorem B1986659 : Blo 880569 1986659 := bstep (se 1 (by rfl) ⟨1489994, by rfl⟩ : syracuseStep 1986659 = 2979989) B2979989
theorem B4018339 : Blo 880569 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B2511121 : Blo 880569 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B1986929 : Blo 880569 1986929 := bstep (se 2 (by rfl) ⟨745098, by rfl⟩ : syracuseStep 1986929 = 1490197) B1490197
theorem B1986947 : Blo 880569 1986947 := bstep (se 1 (by rfl) ⟨1490210, by rfl⟩ : syracuseStep 1986947 = 2980421) B2980421
theorem B2380241 : Blo 880569 2380241 := bstep (se 2 (by rfl) ⟨892590, by rfl⟩ : syracuseStep 2380241 = 1785181) B1785181
theorem B2511395 : Blo 880569 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B4477517 : Blo 880569 4477517 := bstep (se 3 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 4477517 = 1679069) B1679069
theorem B5657201 : Blo 880569 5657201 := bstep (se 2 (by rfl) ⟨2121450, by rfl⟩ : syracuseStep 5657201 = 4242901) B4242901
theorem B1987217 : Blo 880569 1987217 := bstep (se 2 (by rfl) ⟨745206, by rfl⟩ : syracuseStep 1987217 = 1490413) B1490413
theorem B2118307 : Blo 880569 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B1987235 : Blo 880569 1987235 := bstep (se 1 (by rfl) ⟨1490426, by rfl⟩ : syracuseStep 1987235 = 2980853) B2980853
theorem B2511587 : Blo 880569 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B24171317 : Blo 880569 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B19059569 : Blo 880569 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B1987505 : Blo 880569 1987505 := bstep (se 2 (by rfl) ⟨745314, by rfl⟩ : syracuseStep 1987505 = 1490629) B1490629
theorem B1987523 : Blo 880569 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B1430641 : Blo 880569 1430641 := bstep (se 2 (by rfl) ⟨536490, by rfl⟩ : syracuseStep 1430641 = 1072981) B1072981
theorem B6804593 : Blo 880569 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B1987793 : Blo 880569 1987793 := bstep (se 2 (by rfl) ⟨745422, by rfl⟩ : syracuseStep 1987793 = 1490845) B1490845
theorem B1987811 : Blo 880569 1987811 := bstep (se 1 (by rfl) ⟨1490858, by rfl⟩ : syracuseStep 1987811 = 2981717) B2981717
theorem B1791409 : Blo 880569 1791409 := bstep (se 2 (by rfl) ⟨671778, by rfl⟩ : syracuseStep 1791409 = 1343557) B1343557
theorem B1988081 : Blo 880569 1988081 := bstep (se 2 (by rfl) ⟨745530, by rfl⟩ : syracuseStep 1988081 = 1491061) B1491061
theorem B1988099 : Blo 880569 1988099 := bstep (se 1 (by rfl) ⟨1491074, by rfl⟩ : syracuseStep 1988099 = 2982149) B2982149
theorem B2512397 : Blo 880569 2512397 := bstep (se 3 (by rfl) ⟨471074, by rfl⟩ : syracuseStep 2512397 = 942149) B942149
theorem B4085261 : Blo 880569 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B40818289 : Blo 880569 40818289 := bstep (se 2 (by rfl) ⟨15306858, by rfl⟩ : syracuseStep 40818289 = 30613717) B30613717
theorem B2512579 : Blo 880569 2512579 := bstep (se 1 (by rfl) ⟨1884434, by rfl⟩ : syracuseStep 2512579 = 3768869) B3768869
theorem B2545393 : Blo 880569 2545393 := bstep (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) B1909045
theorem B1988369 : Blo 880569 1988369 := bstep (se 2 (by rfl) ⟨745638, by rfl⟩ : syracuseStep 1988369 = 1491277) B1491277
theorem B1988387 : Blo 880569 1988387 := bstep (se 1 (by rfl) ⟨1491290, by rfl⟩ : syracuseStep 1988387 = 2982581) B2982581
theorem B2119537 : Blo 880569 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B5658659 : Blo 880569 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B1988657 : Blo 880569 1988657 := bstep (se 2 (by rfl) ⟨745746, by rfl⟩ : syracuseStep 1988657 = 1491493) B1491493
theorem B1988675 : Blo 880569 1988675 := bstep (se 1 (by rfl) ⟨1491506, by rfl⟩ : syracuseStep 1988675 = 2983013) B2983013
theorem B2513069 : Blo 880569 2513069 := bstep (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) B942401
theorem B1988945 : Blo 880569 1988945 := bstep (se 2 (by rfl) ⟨745854, by rfl⟩ : syracuseStep 1988945 = 1491709) B1491709
theorem B1988963 : Blo 880569 1988963 := bstep (se 1 (by rfl) ⟨1491722, by rfl⟩ : syracuseStep 1988963 = 2983445) B2983445
theorem B907795 : Blo 880569 907795 := bstep (se 1 (by rfl) ⟨680846, by rfl⟩ : syracuseStep 907795 = 1361693) B1361693
theorem B4020785 : Blo 880569 4020785 := bstep (se 2 (by rfl) ⟨1507794, by rfl⟩ : syracuseStep 4020785 = 3015589) B3015589
theorem B1989233 : Blo 880569 1989233 := bstep (se 2 (by rfl) ⟨745962, by rfl⟩ : syracuseStep 1989233 = 1491925) B1491925
theorem B1989251 : Blo 880569 1989251 := bstep (se 1 (by rfl) ⟨1491938, by rfl⟩ : syracuseStep 1989251 = 2983877) B2983877
theorem B10902197 : Blo 880569 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B2972429 : Blo 880569 2972429 := bstep (se 3 (by rfl) ⟨557330, by rfl⟩ : syracuseStep 2972429 = 1114661) B1114661
theorem B2972483 : Blo 880569 2972483 := bstep (se 1 (by rfl) ⟨2229362, by rfl⟩ : syracuseStep 2972483 = 4458725) B4458725
theorem B1792835 : Blo 880569 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B1989521 : Blo 880569 1989521 := bstep (se 2 (by rfl) ⟨746070, by rfl⟩ : syracuseStep 1989521 = 1492141) B1492141
theorem B1989539 : Blo 880569 1989539 := bstep (se 1 (by rfl) ⟨1492154, by rfl⟩ : syracuseStep 1989539 = 2984309) B2984309
theorem B2972753 : Blo 880569 2972753 := bstep (se 2 (by rfl) ⟨1114782, by rfl⟩ : syracuseStep 2972753 = 2229565) B2229565
theorem B1989809 : Blo 880569 1989809 := bstep (se 2 (by rfl) ⟨746178, by rfl⟩ : syracuseStep 1989809 = 1492357) B1492357
theorem B1989827 : Blo 880569 1989827 := bstep (se 1 (by rfl) ⟨1492370, by rfl⟩ : syracuseStep 1989827 = 2984741) B2984741
theorem B1400113 : Blo 880569 1400113 := bstep (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) B1050085
theorem B2514253 : Blo 880569 2514253 := bstep (se 3 (by rfl) ⟨471422, by rfl⟩ : syracuseStep 2514253 = 942845) B942845
theorem B1007011 : Blo 880569 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B1990097 : Blo 880569 1990097 := bstep (se 2 (by rfl) ⟨746286, by rfl⟩ : syracuseStep 1990097 = 1492573) B1492573
theorem B1990115 : Blo 880569 1990115 := bstep (se 1 (by rfl) ⟨1492586, by rfl⟩ : syracuseStep 1990115 = 2985173) B2985173
theorem B941555 : Blo 880569 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B2973293 : Blo 880569 2973293 := bstep (se 3 (by rfl) ⟨557492, by rfl⟩ : syracuseStep 2973293 = 1114985) B1114985
theorem B2973347 : Blo 880569 2973347 := bstep (se 1 (by rfl) ⟨2230010, by rfl⟩ : syracuseStep 2973347 = 4460021) B4460021
theorem B2416355 : Blo 880569 2416355 := bstep (se 1 (by rfl) ⟨1812266, by rfl⟩ : syracuseStep 2416355 = 3624533) B3624533
theorem B5660401 : Blo 880569 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B2383789 : Blo 880569 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B2973617 : Blo 880569 2973617 := bstep (se 2 (by rfl) ⟨1115106, by rfl⟩ : syracuseStep 2973617 = 2230213) B2230213
theorem B4907141 : Blo 880569 4907141 := bstep (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) B920089
theorem B8478917 : Blo 880569 8478917 := bstep (se 4 (by rfl) ⟨794898, by rfl⟩ : syracuseStep 8478917 = 1589797) B1589797
theorem B5366051 : Blo 880569 5366051 := bstep (se 1 (by rfl) ⟨4024538, by rfl⟩ : syracuseStep 5366051 = 8049077) B8049077
theorem B2515313 : Blo 880569 2515313 := bstep (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) B1886485
theorem B2974157 : Blo 880569 2974157 := bstep (se 3 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 2974157 = 1115309) B1115309
theorem B942563 : Blo 880569 942563 := bstep (se 1 (by rfl) ⟨706922, by rfl⟩ : syracuseStep 942563 = 1413845) B1413845
theorem B2974211 : Blo 880569 2974211 := bstep (se 1 (by rfl) ⟨2230658, by rfl⟩ : syracuseStep 2974211 = 4461317) B4461317
theorem B2384653 : Blo 880569 2384653 := bstep (se 3 (by rfl) ⟨447122, by rfl⟩ : syracuseStep 2384653 = 894245) B894245
theorem B2974481 : Blo 880569 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B51602197 : Blo 880569 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B2515985 : Blo 880569 2515985 := bstep (se 2 (by rfl) ⟨943494, by rfl⟩ : syracuseStep 2515985 = 1886989) B1886989
theorem B2975021 : Blo 880569 2975021 := bstep (se 3 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 2975021 = 1115633) B1115633
theorem B2975075 : Blo 880569 2975075 := bstep (se 1 (by rfl) ⟨2231306, by rfl⟩ : syracuseStep 2975075 = 4462613) B4462613
theorem B7530083 : Blo 880569 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B3761777 : Blo 880569 3761777 := bstep (se 2 (by rfl) ⟨1410666, by rfl⟩ : syracuseStep 3761777 = 2821333) B2821333
theorem B2975345 : Blo 880569 2975345 := bstep (se 2 (by rfl) ⟨1115754, by rfl⟩ : syracuseStep 2975345 = 2231509) B2231509
theorem B2385539 : Blo 880569 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B5662349 : Blo 880569 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B2123459 : Blo 880569 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B2516771 : Blo 880569 2516771 := bstep (se 1 (by rfl) ⟨1887578, by rfl⟩ : syracuseStep 2516771 = 3775157) B3775157
theorem B2385713 : Blo 880569 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B944131 : Blo 880569 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B2517101 : Blo 880569 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B2975885 : Blo 880569 2975885 := bstep (se 3 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 2975885 = 1115957) B1115957
theorem B2517169 : Blo 880569 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B2975939 : Blo 880569 2975939 := bstep (se 1 (by rfl) ⟨2231954, by rfl⟩ : syracuseStep 2975939 = 4463909) B4463909
theorem B27519203 : Blo 880569 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B2386253 : Blo 880569 2386253 := bstep (se 3 (by rfl) ⟨447422, by rfl⟩ : syracuseStep 2386253 = 894845) B894845
theorem B9562481 : Blo 880569 9562481 := bstep (se 2 (by rfl) ⟨3585930, by rfl⟩ : syracuseStep 9562481 = 7171861) B7171861
theorem B2517443 : Blo 880569 2517443 := bstep (se 1 (by rfl) ⟨1888082, by rfl⟩ : syracuseStep 2517443 = 3776165) B3776165
theorem B2124227 : Blo 880569 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B944579 : Blo 880569 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B2976209 : Blo 880569 2976209 := bstep (se 2 (by rfl) ⟨1116078, by rfl⟩ : syracuseStep 2976209 = 2232157) B2232157
theorem B2386513 : Blo 880569 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B6285923 : Blo 880569 6285923 := bstep (se 1 (by rfl) ⟨4714442, by rfl⟩ : syracuseStep 6285923 = 9428885) B9428885
theorem B4778801 : Blo 880569 4778801 := bstep (se 2 (by rfl) ⟨1792050, by rfl⟩ : syracuseStep 4778801 = 3584101) B3584101
theorem B3763043 : Blo 880569 3763043 := bstep (se 1 (by rfl) ⟨2822282, by rfl⟩ : syracuseStep 3763043 = 5644565) B5644565
theorem B4025251 : Blo 880569 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B1698769 : Blo 880569 1698769 := bstep (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) B1274077
theorem B2976749 : Blo 880569 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B2124785 : Blo 880569 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2976803 : Blo 880569 2976803 := bstep (se 1 (by rfl) ⟨2232602, by rfl⟩ : syracuseStep 2976803 = 4465205) B4465205
theorem B2583587 : Blo 880569 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B1076371 : Blo 880569 1076371 := bstep (se 1 (by rfl) ⟨807278, by rfl⟩ : syracuseStep 1076371 = 1614557) B1614557
theorem B2518285 : Blo 880569 2518285 := bstep (se 3 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 2518285 = 944357) B944357
theorem B2977073 : Blo 880569 2977073 := bstep (se 2 (by rfl) ⟨1116402, by rfl⟩ : syracuseStep 2977073 = 2232805) B2232805
theorem B2551213 : Blo 880569 2551213 := bstep (se 3 (by rfl) ⟨478352, by rfl⟩ : syracuseStep 2551213 = 956705) B956705
theorem B2518445 : Blo 880569 2518445 := bstep (se 3 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 2518445 = 944417) B944417
theorem B3173987 : Blo 880569 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B2518627 : Blo 880569 2518627 := bstep (se 1 (by rfl) ⟨1888970, by rfl⟩ : syracuseStep 2518627 = 3777941) B3777941
theorem B2715245 : Blo 880569 2715245 := bstep (se 3 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 2715245 = 1018217) B1018217
theorem B2977613 : Blo 880569 2977613 := bstep (se 3 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 2977613 = 1116605) B1116605
theorem B2387789 : Blo 880569 2387789 := bstep (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) B895421
theorem B2977667 : Blo 880569 2977667 := bstep (se 1 (by rfl) ⟨2233250, by rfl⟩ : syracuseStep 2977667 = 4466501) B4466501
theorem B4026289 : Blo 880569 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B880579 : Blo 880569 880579 := bstep (se 1 (by rfl) ⟨660434, by rfl⟩ : syracuseStep 880579 = 1320869) B1320869
theorem B1699793 : Blo 880569 1699793 := bstep (se 2 (by rfl) ⟨637422, by rfl⟩ : syracuseStep 1699793 = 1274845) B1274845
theorem B880595 : Blo 880569 880595 := bstep (se 1 (by rfl) ⟨660446, by rfl⟩ : syracuseStep 880595 = 1320893) B1320893
theorem B880611 : Blo 880569 880611 := bstep (se 1 (by rfl) ⟨660458, by rfl⟩ : syracuseStep 880611 = 1320917) B1320917
theorem B880627 : Blo 880569 880627 := bstep (se 1 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 880627 = 1320941) B1320941
theorem B880643 : Blo 880569 880643 := bstep (se 1 (by rfl) ⟨660482, by rfl⟩ : syracuseStep 880643 = 1320965) B1320965
theorem B880659 : Blo 880569 880659 := bstep (se 1 (by rfl) ⟨660494, by rfl⟩ : syracuseStep 880659 = 1320989) B1320989
theorem B880675 : Blo 880569 880675 := bstep (se 1 (by rfl) ⟨660506, by rfl⟩ : syracuseStep 880675 = 1321013) B1321013
theorem B2388017 : Blo 880569 2388017 := bstep (se 2 (by rfl) ⟨895506, by rfl⟩ : syracuseStep 2388017 = 1791013) B1791013
theorem B880691 : Blo 880569 880691 := bstep (se 1 (by rfl) ⟨660518, by rfl⟩ : syracuseStep 880691 = 1321037) B1321037
theorem B880707 : Blo 880569 880707 := bstep (se 1 (by rfl) ⟨660530, by rfl⟩ : syracuseStep 880707 = 1321061) B1321061
theorem B7270469 : Blo 880569 7270469 := bstep (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) B1363213
theorem B880723 : Blo 880569 880723 := bstep (se 1 (by rfl) ⟨660542, by rfl⟩ : syracuseStep 880723 = 1321085) B1321085
theorem B880739 : Blo 880569 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B880755 : Blo 880569 880755 := bstep (se 1 (by rfl) ⟨660566, by rfl⟩ : syracuseStep 880755 = 1321133) B1321133
theorem B880771 : Blo 880569 880771 := bstep (se 1 (by rfl) ⟨660578, by rfl⟩ : syracuseStep 880771 = 1321157) B1321157
theorem B2977937 : Blo 880569 2977937 := bstep (se 2 (by rfl) ⟨1116726, by rfl⟩ : syracuseStep 2977937 = 2233453) B2233453
theorem B880787 : Blo 880569 880787 := bstep (se 1 (by rfl) ⟨660590, by rfl⟩ : syracuseStep 880787 = 1321181) B1321181
theorem B2388113 : Blo 880569 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B880803 : Blo 880569 880803 := bstep (se 1 (by rfl) ⟨660602, by rfl⟩ : syracuseStep 880803 = 1321205) B1321205
theorem B880819 : Blo 880569 880819 := bstep (se 1 (by rfl) ⟨660614, by rfl⟩ : syracuseStep 880819 = 1321229) B1321229
theorem B880835 : Blo 880569 880835 := bstep (se 1 (by rfl) ⟨660626, by rfl⟩ : syracuseStep 880835 = 1321253) B1321253
theorem B880851 : Blo 880569 880851 := bstep (se 1 (by rfl) ⟨660638, by rfl⟩ : syracuseStep 880851 = 1321277) B1321277
theorem B880867 : Blo 880569 880867 := bstep (se 1 (by rfl) ⟨660650, by rfl⟩ : syracuseStep 880867 = 1321301) B1321301
theorem B880883 : Blo 880569 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B880899 : Blo 880569 880899 := bstep (se 1 (by rfl) ⟨660674, by rfl⟩ : syracuseStep 880899 = 1321349) B1321349
theorem B880915 : Blo 880569 880915 := bstep (se 1 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 880915 = 1321373) B1321373
theorem B880931 : Blo 880569 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B880947 : Blo 880569 880947 := bstep (se 1 (by rfl) ⟨660710, by rfl⟩ : syracuseStep 880947 = 1321421) B1321421
theorem B880963 : Blo 880569 880963 := bstep (se 1 (by rfl) ⟨660722, by rfl⟩ : syracuseStep 880963 = 1321445) B1321445
theorem B880979 : Blo 880569 880979 := bstep (se 1 (by rfl) ⟨660734, by rfl⟩ : syracuseStep 880979 = 1321469) B1321469
theorem B880995 : Blo 880569 880995 := bstep (se 1 (by rfl) ⟨660746, by rfl⟩ : syracuseStep 880995 = 1321493) B1321493
theorem B881011 : Blo 880569 881011 := bstep (se 1 (by rfl) ⟨660758, by rfl⟩ : syracuseStep 881011 = 1321517) B1321517
theorem B881027 : Blo 880569 881027 := bstep (se 1 (by rfl) ⟨660770, by rfl⟩ : syracuseStep 881027 = 1321541) B1321541
theorem B881043 : Blo 880569 881043 := bstep (se 1 (by rfl) ⟨660782, by rfl⟩ : syracuseStep 881043 = 1321565) B1321565
theorem B881059 : Blo 880569 881059 := bstep (se 1 (by rfl) ⟨660794, by rfl⟩ : syracuseStep 881059 = 1321589) B1321589
theorem B881075 : Blo 880569 881075 := bstep (se 1 (by rfl) ⟨660806, by rfl⟩ : syracuseStep 881075 = 1321613) B1321613
theorem B881091 : Blo 880569 881091 := bstep (se 1 (by rfl) ⟨660818, by rfl⟩ : syracuseStep 881091 = 1321637) B1321637
theorem B881107 : Blo 880569 881107 := bstep (se 1 (by rfl) ⟨660830, by rfl⟩ : syracuseStep 881107 = 1321661) B1321661
theorem B881123 : Blo 880569 881123 := bstep (se 1 (by rfl) ⟨660842, by rfl⟩ : syracuseStep 881123 = 1321685) B1321685
theorem B881139 : Blo 880569 881139 := bstep (se 1 (by rfl) ⟨660854, by rfl⟩ : syracuseStep 881139 = 1321709) B1321709
theorem B881155 : Blo 880569 881155 := bstep (se 1 (by rfl) ⟨660866, by rfl⟩ : syracuseStep 881155 = 1321733) B1321733
theorem B881171 : Blo 880569 881171 := bstep (se 1 (by rfl) ⟨660878, by rfl⟩ : syracuseStep 881171 = 1321757) B1321757
theorem B881187 : Blo 880569 881187 := bstep (se 1 (by rfl) ⟨660890, by rfl⟩ : syracuseStep 881187 = 1321781) B1321781
theorem B881203 : Blo 880569 881203 := bstep (se 1 (by rfl) ⟨660902, by rfl⟩ : syracuseStep 881203 = 1321805) B1321805
theorem B881219 : Blo 880569 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B881235 : Blo 880569 881235 := bstep (se 1 (by rfl) ⟨660926, by rfl⟩ : syracuseStep 881235 = 1321853) B1321853
theorem B881251 : Blo 880569 881251 := bstep (se 1 (by rfl) ⟨660938, by rfl⟩ : syracuseStep 881251 = 1321877) B1321877
theorem B881267 : Blo 880569 881267 := bstep (se 1 (by rfl) ⟨660950, by rfl⟩ : syracuseStep 881267 = 1321901) B1321901
theorem B881283 : Blo 880569 881283 := bstep (se 1 (by rfl) ⟨660962, by rfl⟩ : syracuseStep 881283 = 1321925) B1321925
theorem B881299 : Blo 880569 881299 := bstep (se 1 (by rfl) ⟨660974, by rfl⟩ : syracuseStep 881299 = 1321949) B1321949
theorem B881315 : Blo 880569 881315 := bstep (se 1 (by rfl) ⟨660986, by rfl⟩ : syracuseStep 881315 = 1321973) B1321973
theorem B2978477 : Blo 880569 2978477 := bstep (se 3 (by rfl) ⟨558464, by rfl⟩ : syracuseStep 2978477 = 1116929) B1116929
theorem B881331 : Blo 880569 881331 := bstep (se 1 (by rfl) ⟨660998, by rfl⟩ : syracuseStep 881331 = 1321997) B1321997
theorem B881347 : Blo 880569 881347 := bstep (se 1 (by rfl) ⟨661010, by rfl⟩ : syracuseStep 881347 = 1322021) B1322021
theorem B881363 : Blo 880569 881363 := bstep (se 1 (by rfl) ⟨661022, by rfl⟩ : syracuseStep 881363 = 1322045) B1322045
theorem B881379 : Blo 880569 881379 := bstep (se 1 (by rfl) ⟨661034, by rfl⟩ : syracuseStep 881379 = 1322069) B1322069
theorem B2978531 : Blo 880569 2978531 := bstep (se 1 (by rfl) ⟨2233898, by rfl⟩ : syracuseStep 2978531 = 4467797) B4467797
theorem B881395 : Blo 880569 881395 := bstep (se 1 (by rfl) ⟨661046, by rfl⟩ : syracuseStep 881395 = 1322093) B1322093
theorem B881411 : Blo 880569 881411 := bstep (se 1 (by rfl) ⟨661058, by rfl⟩ : syracuseStep 881411 = 1322117) B1322117
theorem B881427 : Blo 880569 881427 := bstep (se 1 (by rfl) ⟨661070, by rfl⟩ : syracuseStep 881427 = 1322141) B1322141
theorem B881443 : Blo 880569 881443 := bstep (se 1 (by rfl) ⟨661082, by rfl⟩ : syracuseStep 881443 = 1322165) B1322165
theorem B881459 : Blo 880569 881459 := bstep (se 1 (by rfl) ⟨661094, by rfl⟩ : syracuseStep 881459 = 1322189) B1322189
theorem B881475 : Blo 880569 881475 := bstep (se 1 (by rfl) ⟨661106, by rfl⟩ : syracuseStep 881475 = 1322213) B1322213
theorem B881491 : Blo 880569 881491 := bstep (se 1 (by rfl) ⟨661118, by rfl⟩ : syracuseStep 881491 = 1322237) B1322237
theorem B881507 : Blo 880569 881507 := bstep (se 1 (by rfl) ⟨661130, by rfl⟩ : syracuseStep 881507 = 1322261) B1322261
theorem B881523 : Blo 880569 881523 := bstep (se 1 (by rfl) ⟨661142, by rfl⟩ : syracuseStep 881523 = 1322285) B1322285
theorem B881539 : Blo 880569 881539 := bstep (se 1 (by rfl) ⟨661154, by rfl⟩ : syracuseStep 881539 = 1322309) B1322309
theorem B881555 : Blo 880569 881555 := bstep (se 1 (by rfl) ⟨661166, by rfl⟩ : syracuseStep 881555 = 1322333) B1322333
theorem B881571 : Blo 880569 881571 := bstep (se 1 (by rfl) ⟨661178, by rfl⟩ : syracuseStep 881571 = 1322357) B1322357
theorem B881587 : Blo 880569 881587 := bstep (se 1 (by rfl) ⟨661190, by rfl⟩ : syracuseStep 881587 = 1322381) B1322381
theorem B881603 : Blo 880569 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B5665733 : Blo 880569 5665733 := bstep (se 4 (by rfl) ⟨531162, by rfl⟩ : syracuseStep 5665733 = 1062325) B1062325
theorem B881619 : Blo 880569 881619 := bstep (se 1 (by rfl) ⟨661214, by rfl⟩ : syracuseStep 881619 = 1322429) B1322429
theorem B881635 : Blo 880569 881635 := bstep (se 1 (by rfl) ⟨661226, by rfl⟩ : syracuseStep 881635 = 1322453) B1322453
theorem B2978801 : Blo 880569 2978801 := bstep (se 2 (by rfl) ⟨1117050, by rfl⟩ : syracuseStep 2978801 = 2234101) B2234101
theorem B881651 : Blo 880569 881651 := bstep (se 1 (by rfl) ⟨661238, by rfl⟩ : syracuseStep 881651 = 1322477) B1322477
theorem B881667 : Blo 880569 881667 := bstep (se 1 (by rfl) ⟨661250, by rfl⟩ : syracuseStep 881667 = 1322501) B1322501
theorem B881683 : Blo 880569 881683 := bstep (se 1 (by rfl) ⟨661262, by rfl⟩ : syracuseStep 881683 = 1322525) B1322525
theorem B881699 : Blo 880569 881699 := bstep (se 1 (by rfl) ⟨661274, by rfl⟩ : syracuseStep 881699 = 1322549) B1322549
theorem B881715 : Blo 880569 881715 := bstep (se 1 (by rfl) ⟨661286, by rfl⟩ : syracuseStep 881715 = 1322573) B1322573
theorem B881731 : Blo 880569 881731 := bstep (se 1 (by rfl) ⟨661298, by rfl⟩ : syracuseStep 881731 = 1322597) B1322597
theorem B881747 : Blo 880569 881747 := bstep (se 1 (by rfl) ⟨661310, by rfl⟩ : syracuseStep 881747 = 1322621) B1322621
theorem B881763 : Blo 880569 881763 := bstep (se 1 (by rfl) ⟨661322, by rfl⟩ : syracuseStep 881763 = 1322645) B1322645
theorem B2290801 : Blo 880569 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B881779 : Blo 880569 881779 := bstep (se 1 (by rfl) ⟨661334, by rfl⟩ : syracuseStep 881779 = 1322669) B1322669
theorem B881795 : Blo 880569 881795 := bstep (se 1 (by rfl) ⟨661346, by rfl⟩ : syracuseStep 881795 = 1322693) B1322693
theorem B881811 : Blo 880569 881811 := bstep (se 1 (by rfl) ⟨661358, by rfl⟩ : syracuseStep 881811 = 1322717) B1322717
theorem B881827 : Blo 880569 881827 := bstep (se 1 (by rfl) ⟨661370, by rfl⟩ : syracuseStep 881827 = 1322741) B1322741
theorem B881843 : Blo 880569 881843 := bstep (se 1 (by rfl) ⟨661382, by rfl⟩ : syracuseStep 881843 = 1322765) B1322765
theorem B881859 : Blo 880569 881859 := bstep (se 1 (by rfl) ⟨661394, by rfl⟩ : syracuseStep 881859 = 1322789) B1322789
theorem B881875 : Blo 880569 881875 := bstep (se 1 (by rfl) ⟨661406, by rfl⟩ : syracuseStep 881875 = 1322813) B1322813
theorem B881891 : Blo 880569 881891 := bstep (se 1 (by rfl) ⟨661418, by rfl⟩ : syracuseStep 881891 = 1322837) B1322837
theorem B881907 : Blo 880569 881907 := bstep (se 1 (by rfl) ⟨661430, by rfl⟩ : syracuseStep 881907 = 1322861) B1322861
theorem B881923 : Blo 880569 881923 := bstep (se 1 (by rfl) ⟨661442, by rfl⟩ : syracuseStep 881923 = 1322885) B1322885
theorem B881939 : Blo 880569 881939 := bstep (se 1 (by rfl) ⟨661454, by rfl⟩ : syracuseStep 881939 = 1322909) B1322909
theorem B881955 : Blo 880569 881955 := bstep (se 1 (by rfl) ⟨661466, by rfl⟩ : syracuseStep 881955 = 1322933) B1322933
theorem B3175729 : Blo 880569 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B881971 : Blo 880569 881971 := bstep (se 1 (by rfl) ⟨661478, by rfl⟩ : syracuseStep 881971 = 1322957) B1322957
theorem B881987 : Blo 880569 881987 := bstep (se 1 (by rfl) ⟨661490, by rfl⟩ : syracuseStep 881987 = 1322981) B1322981
theorem B882003 : Blo 880569 882003 := bstep (se 1 (by rfl) ⟨661502, by rfl⟩ : syracuseStep 882003 = 1323005) B1323005
theorem B882019 : Blo 880569 882019 := bstep (se 1 (by rfl) ⟨661514, by rfl⟩ : syracuseStep 882019 = 1323029) B1323029
theorem B882035 : Blo 880569 882035 := bstep (se 1 (by rfl) ⟨661526, by rfl⟩ : syracuseStep 882035 = 1323053) B1323053
theorem B882051 : Blo 880569 882051 := bstep (se 1 (by rfl) ⟨661538, by rfl⟩ : syracuseStep 882051 = 1323077) B1323077
theorem B882067 : Blo 880569 882067 := bstep (se 1 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 882067 = 1323101) B1323101
theorem B882083 : Blo 880569 882083 := bstep (se 1 (by rfl) ⟨661562, by rfl⟩ : syracuseStep 882083 = 1323125) B1323125
theorem B882099 : Blo 880569 882099 := bstep (se 1 (by rfl) ⟨661574, by rfl⟩ : syracuseStep 882099 = 1323149) B1323149
theorem B882115 : Blo 880569 882115 := bstep (se 1 (by rfl) ⟨661586, by rfl⟩ : syracuseStep 882115 = 1323173) B1323173
theorem B882131 : Blo 880569 882131 := bstep (se 1 (by rfl) ⟨661598, by rfl⟩ : syracuseStep 882131 = 1323197) B1323197
theorem B882147 : Blo 880569 882147 := bstep (se 1 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 882147 = 1323221) B1323221
theorem B882163 : Blo 880569 882163 := bstep (se 1 (by rfl) ⟨661622, by rfl⟩ : syracuseStep 882163 = 1323245) B1323245
theorem B882179 : Blo 880569 882179 := bstep (se 1 (by rfl) ⟨661634, by rfl⟩ : syracuseStep 882179 = 1323269) B1323269
theorem B2979341 : Blo 880569 2979341 := bstep (se 3 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 2979341 = 1117253) B1117253
theorem B882195 : Blo 880569 882195 := bstep (se 1 (by rfl) ⟨661646, by rfl⟩ : syracuseStep 882195 = 1323293) B1323293
theorem B882211 : Blo 880569 882211 := bstep (se 1 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 882211 = 1323317) B1323317
theorem B882227 : Blo 880569 882227 := bstep (se 1 (by rfl) ⟨661670, by rfl⟩ : syracuseStep 882227 = 1323341) B1323341
theorem B882243 : Blo 880569 882243 := bstep (se 1 (by rfl) ⟨661682, by rfl⟩ : syracuseStep 882243 = 1323365) B1323365
theorem B2979395 : Blo 880569 2979395 := bstep (se 1 (by rfl) ⟨2234546, by rfl⟩ : syracuseStep 2979395 = 4469093) B4469093
theorem B882259 : Blo 880569 882259 := bstep (se 1 (by rfl) ⟨661694, by rfl⟩ : syracuseStep 882259 = 1323389) B1323389
theorem B882275 : Blo 880569 882275 := bstep (se 1 (by rfl) ⟨661706, by rfl⟩ : syracuseStep 882275 = 1323413) B1323413
theorem B882291 : Blo 880569 882291 := bstep (se 1 (by rfl) ⟨661718, by rfl⟩ : syracuseStep 882291 = 1323437) B1323437
theorem B882307 : Blo 880569 882307 := bstep (se 1 (by rfl) ⟨661730, by rfl⟩ : syracuseStep 882307 = 1323461) B1323461
theorem B882323 : Blo 880569 882323 := bstep (se 1 (by rfl) ⟨661742, by rfl⟩ : syracuseStep 882323 = 1323485) B1323485
theorem B882339 : Blo 880569 882339 := bstep (se 1 (by rfl) ⟨661754, by rfl⟩ : syracuseStep 882339 = 1323509) B1323509
theorem B882355 : Blo 880569 882355 := bstep (se 1 (by rfl) ⟨661766, by rfl⟩ : syracuseStep 882355 = 1323533) B1323533
theorem B882371 : Blo 880569 882371 := bstep (se 1 (by rfl) ⟨661778, by rfl⟩ : syracuseStep 882371 = 1323557) B1323557
theorem B882387 : Blo 880569 882387 := bstep (se 1 (by rfl) ⟨661790, by rfl⟩ : syracuseStep 882387 = 1323581) B1323581
theorem B882403 : Blo 880569 882403 := bstep (se 1 (by rfl) ⟨661802, by rfl⟩ : syracuseStep 882403 = 1323605) B1323605
theorem B882419 : Blo 880569 882419 := bstep (se 1 (by rfl) ⟨661814, by rfl⟩ : syracuseStep 882419 = 1323629) B1323629
theorem B882435 : Blo 880569 882435 := bstep (se 1 (by rfl) ⟨661826, by rfl⟩ : syracuseStep 882435 = 1323653) B1323653
theorem B882451 : Blo 880569 882451 := bstep (se 1 (by rfl) ⟨661838, by rfl⟩ : syracuseStep 882451 = 1323677) B1323677
theorem B882467 : Blo 880569 882467 := bstep (se 1 (by rfl) ⟨661850, by rfl⟩ : syracuseStep 882467 = 1323701) B1323701
theorem B882483 : Blo 880569 882483 := bstep (se 1 (by rfl) ⟨661862, by rfl⟩ : syracuseStep 882483 = 1323725) B1323725
theorem B882499 : Blo 880569 882499 := bstep (se 1 (by rfl) ⟨661874, by rfl⟩ : syracuseStep 882499 = 1323749) B1323749
theorem B2979665 : Blo 880569 2979665 := bstep (se 2 (by rfl) ⟨1117374, by rfl⟩ : syracuseStep 2979665 = 2234749) B2234749
theorem B882515 : Blo 880569 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B882531 : Blo 880569 882531 := bstep (se 1 (by rfl) ⟨661898, by rfl⟩ : syracuseStep 882531 = 1323797) B1323797
theorem B882547 : Blo 880569 882547 := bstep (se 1 (by rfl) ⟨661910, by rfl⟩ : syracuseStep 882547 = 1323821) B1323821
theorem B882563 : Blo 880569 882563 := bstep (se 1 (by rfl) ⟨661922, by rfl⟩ : syracuseStep 882563 = 1323845) B1323845
theorem B882579 : Blo 880569 882579 := bstep (se 1 (by rfl) ⟨661934, by rfl⟩ : syracuseStep 882579 = 1323869) B1323869
theorem B882595 : Blo 880569 882595 := bstep (se 1 (by rfl) ⟨661946, by rfl⟩ : syracuseStep 882595 = 1323893) B1323893
theorem B882611 : Blo 880569 882611 := bstep (se 1 (by rfl) ⟨661958, by rfl⟩ : syracuseStep 882611 = 1323917) B1323917
theorem B882627 : Blo 880569 882627 := bstep (se 1 (by rfl) ⟨661970, by rfl⟩ : syracuseStep 882627 = 1323941) B1323941
theorem B882643 : Blo 880569 882643 := bstep (se 1 (by rfl) ⟨661982, by rfl⟩ : syracuseStep 882643 = 1323965) B1323965
theorem B882659 : Blo 880569 882659 := bstep (se 1 (by rfl) ⟨661994, by rfl⟩ : syracuseStep 882659 = 1323989) B1323989
theorem B882675 : Blo 880569 882675 := bstep (se 1 (by rfl) ⟨662006, by rfl⟩ : syracuseStep 882675 = 1324013) B1324013
theorem B882691 : Blo 880569 882691 := bstep (se 1 (by rfl) ⟨662018, by rfl⟩ : syracuseStep 882691 = 1324037) B1324037
theorem B882707 : Blo 880569 882707 := bstep (se 1 (by rfl) ⟨662030, by rfl⟩ : syracuseStep 882707 = 1324061) B1324061
theorem B882723 : Blo 880569 882723 := bstep (se 1 (by rfl) ⟨662042, by rfl⟩ : syracuseStep 882723 = 1324085) B1324085
theorem B882739 : Blo 880569 882739 := bstep (se 1 (by rfl) ⟨662054, by rfl⟩ : syracuseStep 882739 = 1324109) B1324109
theorem B882755 : Blo 880569 882755 := bstep (se 1 (by rfl) ⟨662066, by rfl⟩ : syracuseStep 882755 = 1324133) B1324133
theorem B882771 : Blo 880569 882771 := bstep (se 1 (by rfl) ⟨662078, by rfl⟩ : syracuseStep 882771 = 1324157) B1324157
theorem B882787 : Blo 880569 882787 := bstep (se 1 (by rfl) ⟨662090, by rfl⟩ : syracuseStep 882787 = 1324181) B1324181
theorem B882803 : Blo 880569 882803 := bstep (se 1 (by rfl) ⟨662102, by rfl⟩ : syracuseStep 882803 = 1324205) B1324205
theorem B882819 : Blo 880569 882819 := bstep (se 1 (by rfl) ⟨662114, by rfl⟩ : syracuseStep 882819 = 1324229) B1324229
theorem B2685059 : Blo 880569 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B882835 : Blo 880569 882835 := bstep (se 1 (by rfl) ⟨662126, by rfl⟩ : syracuseStep 882835 = 1324253) B1324253
theorem B882851 : Blo 880569 882851 := bstep (se 1 (by rfl) ⟨662138, by rfl⟩ : syracuseStep 882851 = 1324277) B1324277
theorem B882867 : Blo 880569 882867 := bstep (se 1 (by rfl) ⟨662150, by rfl⟩ : syracuseStep 882867 = 1324301) B1324301
theorem B882883 : Blo 880569 882883 := bstep (se 1 (by rfl) ⟨662162, by rfl⟩ : syracuseStep 882883 = 1324325) B1324325
theorem B9173189 : Blo 880569 9173189 := bstep (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) B1719973
theorem B882899 : Blo 880569 882899 := bstep (se 1 (by rfl) ⟨662174, by rfl⟩ : syracuseStep 882899 = 1324349) B1324349
theorem B882915 : Blo 880569 882915 := bstep (se 1 (by rfl) ⟨662186, by rfl⟩ : syracuseStep 882915 = 1324373) B1324373
theorem B882931 : Blo 880569 882931 := bstep (se 1 (by rfl) ⟨662198, by rfl⟩ : syracuseStep 882931 = 1324397) B1324397
theorem B882947 : Blo 880569 882947 := bstep (se 1 (by rfl) ⟨662210, by rfl⟩ : syracuseStep 882947 = 1324421) B1324421
theorem B882963 : Blo 880569 882963 := bstep (se 1 (by rfl) ⟨662222, by rfl⟩ : syracuseStep 882963 = 1324445) B1324445
theorem B882979 : Blo 880569 882979 := bstep (se 1 (by rfl) ⟨662234, by rfl⟩ : syracuseStep 882979 = 1324469) B1324469
theorem B882995 : Blo 880569 882995 := bstep (se 1 (by rfl) ⟨662246, by rfl⟩ : syracuseStep 882995 = 1324493) B1324493
theorem B883011 : Blo 880569 883011 := bstep (se 1 (by rfl) ⟨662258, by rfl⟩ : syracuseStep 883011 = 1324517) B1324517
theorem B883027 : Blo 880569 883027 := bstep (se 1 (by rfl) ⟨662270, by rfl⟩ : syracuseStep 883027 = 1324541) B1324541
theorem B883043 : Blo 880569 883043 := bstep (se 1 (by rfl) ⟨662282, by rfl⟩ : syracuseStep 883043 = 1324565) B1324565
theorem B2980205 : Blo 880569 2980205 := bstep (se 3 (by rfl) ⟨558788, by rfl⟩ : syracuseStep 2980205 = 1117577) B1117577
theorem B883059 : Blo 880569 883059 := bstep (se 1 (by rfl) ⟨662294, by rfl⟩ : syracuseStep 883059 = 1324589) B1324589
theorem B883075 : Blo 880569 883075 := bstep (se 1 (by rfl) ⟨662306, by rfl⟩ : syracuseStep 883075 = 1324613) B1324613
theorem B883091 : Blo 880569 883091 := bstep (se 1 (by rfl) ⟨662318, by rfl⟩ : syracuseStep 883091 = 1324637) B1324637
theorem B2980259 : Blo 880569 2980259 := bstep (se 1 (by rfl) ⟨2235194, by rfl⟩ : syracuseStep 2980259 = 4470389) B4470389
theorem B883107 : Blo 880569 883107 := bstep (se 1 (by rfl) ⟨662330, by rfl⟩ : syracuseStep 883107 = 1324661) B1324661
theorem B4028849 : Blo 880569 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B883123 : Blo 880569 883123 := bstep (se 1 (by rfl) ⟨662342, by rfl⟩ : syracuseStep 883123 = 1324685) B1324685
theorem B883139 : Blo 880569 883139 := bstep (se 1 (by rfl) ⟨662354, by rfl⟩ : syracuseStep 883139 = 1324709) B1324709
theorem B3766733 : Blo 880569 3766733 := bstep (se 3 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 3766733 = 1412525) B1412525
theorem B883155 : Blo 880569 883155 := bstep (se 1 (by rfl) ⟨662366, by rfl⟩ : syracuseStep 883155 = 1324733) B1324733
theorem B883171 : Blo 880569 883171 := bstep (se 1 (by rfl) ⟨662378, by rfl⟩ : syracuseStep 883171 = 1324757) B1324757
theorem B883187 : Blo 880569 883187 := bstep (se 1 (by rfl) ⟨662390, by rfl⟩ : syracuseStep 883187 = 1324781) B1324781
theorem B883203 : Blo 880569 883203 := bstep (se 1 (by rfl) ⟨662402, by rfl⟩ : syracuseStep 883203 = 1324805) B1324805
theorem B883219 : Blo 880569 883219 := bstep (se 1 (by rfl) ⟨662414, by rfl⟩ : syracuseStep 883219 = 1324829) B1324829
theorem B883235 : Blo 880569 883235 := bstep (se 1 (by rfl) ⟨662426, by rfl⟩ : syracuseStep 883235 = 1324853) B1324853
theorem B883251 : Blo 880569 883251 := bstep (se 1 (by rfl) ⟨662438, by rfl⟩ : syracuseStep 883251 = 1324877) B1324877
theorem B883267 : Blo 880569 883267 := bstep (se 1 (by rfl) ⟨662450, by rfl⟩ : syracuseStep 883267 = 1324901) B1324901
theorem B883283 : Blo 880569 883283 := bstep (se 1 (by rfl) ⟨662462, by rfl⟩ : syracuseStep 883283 = 1324925) B1324925
theorem B883299 : Blo 880569 883299 := bstep (se 1 (by rfl) ⟨662474, by rfl⟩ : syracuseStep 883299 = 1324949) B1324949
theorem B883315 : Blo 880569 883315 := bstep (se 1 (by rfl) ⟨662486, by rfl⟩ : syracuseStep 883315 = 1324973) B1324973
theorem B883331 : Blo 880569 883331 := bstep (se 1 (by rfl) ⟨662498, by rfl⟩ : syracuseStep 883331 = 1324997) B1324997
theorem B883347 : Blo 880569 883347 := bstep (se 1 (by rfl) ⟨662510, by rfl⟩ : syracuseStep 883347 = 1325021) B1325021
theorem B883363 : Blo 880569 883363 := bstep (se 1 (by rfl) ⟨662522, by rfl⟩ : syracuseStep 883363 = 1325045) B1325045
theorem B2980529 : Blo 880569 2980529 := bstep (se 2 (by rfl) ⟨1117698, by rfl⟩ : syracuseStep 2980529 = 2235397) B2235397
theorem B883379 : Blo 880569 883379 := bstep (se 1 (by rfl) ⟨662534, by rfl⟩ : syracuseStep 883379 = 1325069) B1325069
theorem B883395 : Blo 880569 883395 := bstep (se 1 (by rfl) ⟨662546, by rfl⟩ : syracuseStep 883395 = 1325093) B1325093
theorem B883411 : Blo 880569 883411 := bstep (se 1 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 883411 = 1325117) B1325117
theorem B883427 : Blo 880569 883427 := bstep (se 1 (by rfl) ⟨662570, by rfl⟩ : syracuseStep 883427 = 1325141) B1325141
theorem B883443 : Blo 880569 883443 := bstep (se 1 (by rfl) ⟨662582, by rfl⟩ : syracuseStep 883443 = 1325165) B1325165
theorem B883459 : Blo 880569 883459 := bstep (se 1 (by rfl) ⟨662594, by rfl⟩ : syracuseStep 883459 = 1325189) B1325189
theorem B883475 : Blo 880569 883475 := bstep (se 1 (by rfl) ⟨662606, by rfl⟩ : syracuseStep 883475 = 1325213) B1325213
theorem B883491 : Blo 880569 883491 := bstep (se 1 (by rfl) ⟨662618, by rfl⟩ : syracuseStep 883491 = 1325237) B1325237
theorem B883507 : Blo 880569 883507 := bstep (se 1 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 883507 = 1325261) B1325261
theorem B883523 : Blo 880569 883523 := bstep (se 1 (by rfl) ⟨662642, by rfl⟩ : syracuseStep 883523 = 1325285) B1325285
theorem B883539 : Blo 880569 883539 := bstep (se 1 (by rfl) ⟨662654, by rfl⟩ : syracuseStep 883539 = 1325309) B1325309
theorem B883555 : Blo 880569 883555 := bstep (se 1 (by rfl) ⟨662666, by rfl⟩ : syracuseStep 883555 = 1325333) B1325333
theorem B883571 : Blo 880569 883571 := bstep (se 1 (by rfl) ⟨662678, by rfl⟩ : syracuseStep 883571 = 1325357) B1325357
theorem B883587 : Blo 880569 883587 := bstep (se 1 (by rfl) ⟨662690, by rfl⟩ : syracuseStep 883587 = 1325381) B1325381
theorem B883603 : Blo 880569 883603 := bstep (se 1 (by rfl) ⟨662702, by rfl⟩ : syracuseStep 883603 = 1325405) B1325405
theorem B883619 : Blo 880569 883619 := bstep (se 1 (by rfl) ⟨662714, by rfl⟩ : syracuseStep 883619 = 1325429) B1325429
theorem B883635 : Blo 880569 883635 := bstep (se 1 (by rfl) ⟨662726, by rfl⟩ : syracuseStep 883635 = 1325453) B1325453
theorem B883651 : Blo 880569 883651 := bstep (se 1 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 883651 = 1325477) B1325477
theorem B883667 : Blo 880569 883667 := bstep (se 1 (by rfl) ⟨662750, by rfl⟩ : syracuseStep 883667 = 1325501) B1325501
theorem B883683 : Blo 880569 883683 := bstep (se 1 (by rfl) ⟨662762, by rfl⟩ : syracuseStep 883683 = 1325525) B1325525
theorem B883699 : Blo 880569 883699 := bstep (se 1 (by rfl) ⟨662774, by rfl⟩ : syracuseStep 883699 = 1325549) B1325549
theorem B883715 : Blo 880569 883715 := bstep (se 1 (by rfl) ⟨662786, by rfl⟩ : syracuseStep 883715 = 1325573) B1325573
theorem B883731 : Blo 880569 883731 := bstep (se 1 (by rfl) ⟨662798, by rfl⟩ : syracuseStep 883731 = 1325597) B1325597
theorem B883747 : Blo 880569 883747 := bstep (se 1 (by rfl) ⟨662810, by rfl⟩ : syracuseStep 883747 = 1325621) B1325621
theorem B1506355 : Blo 880569 1506355 := bstep (se 1 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 1506355 = 2259533) B2259533
theorem B883763 : Blo 880569 883763 := bstep (se 1 (by rfl) ⟨662822, by rfl⟩ : syracuseStep 883763 = 1325645) B1325645
theorem B883779 : Blo 880569 883779 := bstep (se 1 (by rfl) ⟨662834, by rfl⟩ : syracuseStep 883779 = 1325669) B1325669
theorem B883795 : Blo 880569 883795 := bstep (se 1 (by rfl) ⟨662846, by rfl⟩ : syracuseStep 883795 = 1325693) B1325693
theorem B883811 : Blo 880569 883811 := bstep (se 1 (by rfl) ⟨662858, by rfl⟩ : syracuseStep 883811 = 1325717) B1325717
theorem B883827 : Blo 880569 883827 := bstep (se 1 (by rfl) ⟨662870, by rfl⟩ : syracuseStep 883827 = 1325741) B1325741
theorem B883843 : Blo 880569 883843 := bstep (se 1 (by rfl) ⟨662882, by rfl⟩ : syracuseStep 883843 = 1325765) B1325765
theorem B883859 : Blo 880569 883859 := bstep (se 1 (by rfl) ⟨662894, by rfl⟩ : syracuseStep 883859 = 1325789) B1325789
theorem B883875 : Blo 880569 883875 := bstep (se 1 (by rfl) ⟨662906, by rfl⟩ : syracuseStep 883875 = 1325813) B1325813
theorem B883891 : Blo 880569 883891 := bstep (se 1 (by rfl) ⟨662918, by rfl⟩ : syracuseStep 883891 = 1325837) B1325837
theorem B883907 : Blo 880569 883907 := bstep (se 1 (by rfl) ⟨662930, by rfl⟩ : syracuseStep 883907 = 1325861) B1325861
theorem B3177677 : Blo 880569 3177677 := bstep (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) B1191629
theorem B2981069 : Blo 880569 2981069 := bstep (se 3 (by rfl) ⟨558950, by rfl⟩ : syracuseStep 2981069 = 1117901) B1117901
theorem B883923 : Blo 880569 883923 := bstep (se 1 (by rfl) ⟨662942, by rfl⟩ : syracuseStep 883923 = 1325885) B1325885
theorem B883939 : Blo 880569 883939 := bstep (se 1 (by rfl) ⟨662954, by rfl⟩ : syracuseStep 883939 = 1325909) B1325909
theorem B883955 : Blo 880569 883955 := bstep (se 1 (by rfl) ⟨662966, by rfl⟩ : syracuseStep 883955 = 1325933) B1325933
theorem B2981123 : Blo 880569 2981123 := bstep (se 1 (by rfl) ⟨2235842, by rfl⟩ : syracuseStep 2981123 = 4471685) B4471685
theorem B883971 : Blo 880569 883971 := bstep (se 1 (by rfl) ⟨662978, by rfl⟩ : syracuseStep 883971 = 1325957) B1325957
theorem B883987 : Blo 880569 883987 := bstep (se 1 (by rfl) ⟨662990, by rfl⟩ : syracuseStep 883987 = 1325981) B1325981
theorem B884003 : Blo 880569 884003 := bstep (se 1 (by rfl) ⟨663002, by rfl⟩ : syracuseStep 884003 = 1326005) B1326005
theorem B884019 : Blo 880569 884019 := bstep (se 1 (by rfl) ⟨663014, by rfl⟩ : syracuseStep 884019 = 1326029) B1326029
theorem B22609205 : Blo 880569 22609205 := bstep (se 5 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 22609205 = 2119613) B2119613
theorem B884035 : Blo 880569 884035 := bstep (se 1 (by rfl) ⟨663026, by rfl⟩ : syracuseStep 884035 = 1326053) B1326053
theorem B884051 : Blo 880569 884051 := bstep (se 1 (by rfl) ⟨663038, by rfl⟩ : syracuseStep 884051 = 1326077) B1326077
theorem B884067 : Blo 880569 884067 := bstep (se 1 (by rfl) ⟨663050, by rfl⟩ : syracuseStep 884067 = 1326101) B1326101
theorem B884083 : Blo 880569 884083 := bstep (se 1 (by rfl) ⟨663062, by rfl⟩ : syracuseStep 884083 = 1326125) B1326125
theorem B884099 : Blo 880569 884099 := bstep (se 1 (by rfl) ⟨663074, by rfl⟩ : syracuseStep 884099 = 1326149) B1326149
theorem B884115 : Blo 880569 884115 := bstep (se 1 (by rfl) ⟨663086, by rfl⟩ : syracuseStep 884115 = 1326173) B1326173
theorem B884131 : Blo 880569 884131 := bstep (se 1 (by rfl) ⟨663098, by rfl⟩ : syracuseStep 884131 = 1326197) B1326197
theorem B2686385 : Blo 880569 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B884147 : Blo 880569 884147 := bstep (se 1 (by rfl) ⟨663110, by rfl⟩ : syracuseStep 884147 = 1326221) B1326221
theorem B884163 : Blo 880569 884163 := bstep (se 1 (by rfl) ⟨663122, by rfl⟩ : syracuseStep 884163 = 1326245) B1326245
theorem B884179 : Blo 880569 884179 := bstep (se 1 (by rfl) ⟨663134, by rfl⟩ : syracuseStep 884179 = 1326269) B1326269
theorem B884195 : Blo 880569 884195 := bstep (se 1 (by rfl) ⟨663146, by rfl⟩ : syracuseStep 884195 = 1326293) B1326293
theorem B884211 : Blo 880569 884211 := bstep (se 1 (by rfl) ⟨663158, by rfl⟩ : syracuseStep 884211 = 1326317) B1326317
theorem B884227 : Blo 880569 884227 := bstep (se 1 (by rfl) ⟨663170, by rfl⟩ : syracuseStep 884227 = 1326341) B1326341
theorem B2981393 : Blo 880569 2981393 := bstep (se 2 (by rfl) ⟨1118022, by rfl⟩ : syracuseStep 2981393 = 2236045) B2236045
theorem B884243 : Blo 880569 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B884259 : Blo 880569 884259 := bstep (se 1 (by rfl) ⟨663194, by rfl⟩ : syracuseStep 884259 = 1326389) B1326389
theorem B884275 : Blo 880569 884275 := bstep (se 1 (by rfl) ⟨663206, by rfl⟩ : syracuseStep 884275 = 1326413) B1326413
theorem B884291 : Blo 880569 884291 := bstep (se 1 (by rfl) ⟨663218, by rfl⟩ : syracuseStep 884291 = 1326437) B1326437
theorem B884307 : Blo 880569 884307 := bstep (se 1 (by rfl) ⟨663230, by rfl⟩ : syracuseStep 884307 = 1326461) B1326461
theorem B884323 : Blo 880569 884323 := bstep (se 1 (by rfl) ⟨663242, by rfl⟩ : syracuseStep 884323 = 1326485) B1326485
theorem B884339 : Blo 880569 884339 := bstep (se 1 (by rfl) ⟨663254, by rfl⟩ : syracuseStep 884339 = 1326509) B1326509
theorem B884355 : Blo 880569 884355 := bstep (se 1 (by rfl) ⟨663266, by rfl⟩ : syracuseStep 884355 = 1326533) B1326533
theorem B884371 : Blo 880569 884371 := bstep (se 1 (by rfl) ⟨663278, by rfl⟩ : syracuseStep 884371 = 1326557) B1326557
theorem B884387 : Blo 880569 884387 := bstep (se 1 (by rfl) ⟨663290, by rfl⟩ : syracuseStep 884387 = 1326581) B1326581
theorem B884403 : Blo 880569 884403 := bstep (se 1 (by rfl) ⟨663302, by rfl⟩ : syracuseStep 884403 = 1326605) B1326605
theorem B884419 : Blo 880569 884419 := bstep (se 1 (by rfl) ⟨663314, by rfl⟩ : syracuseStep 884419 = 1326629) B1326629
theorem B884435 : Blo 880569 884435 := bstep (se 1 (by rfl) ⟨663326, by rfl⟩ : syracuseStep 884435 = 1326653) B1326653
theorem B884451 : Blo 880569 884451 := bstep (se 1 (by rfl) ⟨663338, by rfl⟩ : syracuseStep 884451 = 1326677) B1326677
theorem B884467 : Blo 880569 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B884483 : Blo 880569 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B884499 : Blo 880569 884499 := bstep (se 1 (by rfl) ⟨663374, by rfl⟩ : syracuseStep 884499 = 1326749) B1326749
theorem B884515 : Blo 880569 884515 := bstep (se 1 (by rfl) ⟨663386, by rfl⟩ : syracuseStep 884515 = 1326773) B1326773
theorem B884531 : Blo 880569 884531 := bstep (se 1 (by rfl) ⟨663398, by rfl⟩ : syracuseStep 884531 = 1326797) B1326797
theorem B10714933 : Blo 880569 10714933 := bstep (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) B1004525
theorem B884547 : Blo 880569 884547 := bstep (se 1 (by rfl) ⟨663410, by rfl⟩ : syracuseStep 884547 = 1326821) B1326821
theorem B884563 : Blo 880569 884563 := bstep (se 1 (by rfl) ⟨663422, by rfl⟩ : syracuseStep 884563 = 1326845) B1326845
theorem B2260931 : Blo 880569 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B1343459 : Blo 880569 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B17170805 : Blo 880569 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B2982365 : Blo 880569 2982365 := bstep (se 3 (by rfl) ⟨559193, by rfl⟩ : syracuseStep 2982365 = 1118387) B1118387
theorem B1671833 : Blo 880569 1671833 := bstep (se 2 (by rfl) ⟨626937, by rfl⟩ : syracuseStep 1671833 = 1253875) B1253875
theorem B3769091 : Blo 880569 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B1508107 : Blo 880569 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B1115147 : Blo 880569 1115147 := bstep (se 1 (by rfl) ⟨836360, by rfl⟩ : syracuseStep 1115147 = 1672721) B1672721
theorem B3179537 : Blo 880569 3179537 := bstep (se 2 (by rfl) ⟨1192326, by rfl⟩ : syracuseStep 3179537 = 2384653) B2384653
theorem B3343619 : Blo 880569 3343619 := bstep (se 1 (by rfl) ⟨2507714, by rfl⟩ : syracuseStep 3343619 = 5015429) B5015429
theorem B5375297 : Blo 880569 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B2229707 : Blo 880569 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B2983499 : Blo 880569 2983499 := bstep (se 1 (by rfl) ⟨2237624, by rfl⟩ : syracuseStep 2983499 = 4475249) B4475249
theorem B4458077 : Blo 880569 4458077 := bstep (se 3 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 4458077 = 1671779) B1671779
theorem B40699523 : Blo 880569 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B5375639 : Blo 880569 5375639 := bstep (se 1 (by rfl) ⟨4031729, by rfl⟩ : syracuseStep 5375639 = 8063459) B8063459
theorem B3344075 : Blo 880569 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B1115851 : Blo 880569 1115851 := bstep (se 1 (by rfl) ⟨836888, by rfl⟩ : syracuseStep 1115851 = 1673777) B1673777
theorem B2983769 : Blo 880569 2983769 := bstep (se 2 (by rfl) ⟨1118913, by rfl⟩ : syracuseStep 2983769 = 2237827) B2237827
theorem B3344273 : Blo 880569 3344273 := bstep (se 2 (by rfl) ⟨1254102, by rfl⟩ : syracuseStep 3344273 = 2508205) B2508205
theorem B1116119 : Blo 880569 1116119 := bstep (se 1 (by rfl) ⟨837089, by rfl⟩ : syracuseStep 1116119 = 1674179) B1674179
theorem B1673291 : Blo 880569 1673291 := bstep (se 1 (by rfl) ⟨1254968, by rfl⟩ : syracuseStep 1673291 = 2509937) B2509937
theorem B4130909 : Blo 880569 4130909 := bstep (se 3 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 4130909 = 1549091) B1549091
theorem B4032605 : Blo 880569 4032605 := bstep (se 3 (by rfl) ⟨756113, by rfl⟩ : syracuseStep 4032605 = 1512227) B1512227
theorem B1673473 : Blo 880569 1673473 := bstep (se 2 (by rfl) ⟨627552, by rfl⟩ : syracuseStep 1673473 = 1255105) B1255105
theorem B6785315 : Blo 880569 6785315 := bstep (se 1 (by rfl) ⟨5088986, by rfl⟩ : syracuseStep 6785315 = 10177973) B10177973
theorem B2230679 : Blo 880569 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B1411481 : Blo 880569 1411481 := bstep (se 2 (by rfl) ⟨529305, by rfl⟩ : syracuseStep 1411481 = 1058611) B1058611
theorem B2984471 : Blo 880569 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B3345047 : Blo 880569 3345047 := bstep (se 1 (by rfl) ⟨2508785, by rfl⟩ : syracuseStep 3345047 = 5017571) B5017571
theorem B1116823 : Blo 880569 1116823 := bstep (se 1 (by rfl) ⟨837617, by rfl⟩ : syracuseStep 1116823 = 1675235) B1675235
theorem B1673921 : Blo 880569 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B7146305 : Blo 880569 7146305 := bstep (se 2 (by rfl) ⟨2679864, by rfl⟩ : syracuseStep 7146305 = 5359729) B5359729
theorem B3345245 : Blo 880569 3345245 := bstep (se 3 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 3345245 = 1254467) B1254467
theorem B1674263 : Blo 880569 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B2231347 : Blo 880569 2231347 := bstep (se 1 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 2231347 = 3347021) B3347021
theorem B2985011 : Blo 880569 2985011 := bstep (se 1 (by rfl) ⟨2238758, by rfl⟩ : syracuseStep 2985011 = 4477517) B4477517
theorem B3771467 : Blo 880569 3771467 := bstep (se 1 (by rfl) ⟨2828600, by rfl⟩ : syracuseStep 3771467 = 5657201) B5657201
theorem B6687845 : Blo 880569 6687845 := bstep (se 4 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 6687845 = 1253971) B1253971
theorem B2231489 : Blo 880569 2231489 := bstep (se 2 (by rfl) ⟨836808, by rfl⟩ : syracuseStep 2231489 = 1673617) B1673617
theorem B2985281 : Blo 880569 2985281 := bstep (se 2 (by rfl) ⟨1119480, by rfl⟩ : syracuseStep 2985281 = 2238961) B2238961
theorem B3182017 : Blo 880569 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B7540229 : Blo 880569 7540229 := bstep (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) B1413793
theorem B6688331 : Blo 880569 6688331 := bstep (se 1 (by rfl) ⟨5016248, by rfl⟩ : syracuseStep 6688331 = 10032497) B10032497
theorem B4460183 : Blo 880569 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B1674931 : Blo 880569 1674931 := bstep (se 1 (by rfl) ⟨1256198, by rfl⟩ : syracuseStep 1674931 = 2512397) B2512397
theorem B2723507 : Blo 880569 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B4034393 : Blo 880569 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B3772439 : Blo 880569 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B1675379 : Blo 880569 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B1675417 : Blo 880569 1675417 := bstep (se 2 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 1675417 = 1256563) B1256563
theorem B1118539 : Blo 880569 1118539 := bstep (se 1 (by rfl) ⟨838904, by rfl⟩ : syracuseStep 1118539 = 1677809) B1677809
theorem B2232755 : Blo 880569 2232755 := bstep (se 1 (by rfl) ⟨1674566, by rfl⟩ : syracuseStep 2232755 = 3349133) B3349133
theorem B1675865 : Blo 880569 1675865 := bstep (se 2 (by rfl) ⟨628449, by rfl⟩ : syracuseStep 1675865 = 1256899) B1256899
theorem B3347203 : Blo 880569 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B6361901 : Blo 880569 6361901 := bstep (se 3 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 6361901 = 2385713) B2385713
theorem B5378995 : Blo 880569 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B2233291 : Blo 880569 2233291 := bstep (se 1 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 2233291 = 3349937) B3349937
theorem B3347507 : Blo 880569 3347507 := bstep (se 1 (by rfl) ⟨2510630, by rfl⟩ : syracuseStep 3347507 = 5021261) B5021261
theorem B2233433 : Blo 880569 2233433 := bstep (se 2 (by rfl) ⟨837537, by rfl⟩ : syracuseStep 2233433 = 1675075) B1675075
theorem B2331737 : Blo 880569 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B1610903 : Blo 880569 1610903 := bstep (se 1 (by rfl) ⟨1208177, by rfl⟩ : syracuseStep 1610903 = 2416355) B2416355
theorem B1119511 : Blo 880569 1119511 := bstep (se 1 (by rfl) ⟨839633, by rfl⟩ : syracuseStep 1119511 = 1679267) B1679267
theorem B1676609 : Blo 880569 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B3577367 : Blo 880569 3577367 := bstep (se 1 (by rfl) ⟨2683025, by rfl⟩ : syracuseStep 3577367 = 5366051) B5366051
theorem B1676875 : Blo 880569 1676875 := bstep (se 1 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 1676875 = 2515313) B2515313
theorem B3348161 : Blo 880569 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B2234263 : Blo 880569 2234263 := bstep (se 1 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 2234263 = 3351395) B3351395
theorem B1677323 : Blo 880569 1677323 := bstep (se 1 (by rfl) ⟨1257992, by rfl⟩ : syracuseStep 1677323 = 2515985) B2515985
theorem B5740645 : Blo 880569 5740645 := bstep (se 4 (by rfl) ⟨538185, by rfl⟩ : syracuseStep 5740645 = 1076371) B1076371
theorem B1677505 : Blo 880569 1677505 := bstep (se 2 (by rfl) ⟨629064, by rfl⟩ : syracuseStep 1677505 = 1258129) B1258129
theorem B2824409 : Blo 880569 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B2234699 : Blo 880569 2234699 := bstep (se 1 (by rfl) ⟨1676024, by rfl⟩ : syracuseStep 2234699 = 3352049) B3352049
theorem B3021131 : Blo 880569 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B5020055 : Blo 880569 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B3774899 : Blo 880569 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B1415639 : Blo 880569 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B1677847 : Blo 880569 1677847 := bstep (se 1 (by rfl) ⟨1258385, by rfl⟩ : syracuseStep 1677847 = 2516771) B2516771
theorem B2235073 : Blo 880569 2235073 := bstep (se 2 (by rfl) ⟨838152, by rfl⟩ : syracuseStep 2235073 = 1676305) B1676305
theorem B1678067 : Blo 880569 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B5643053 : Blo 880569 5643053 := bstep (se 3 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 5643053 = 2116145) B2116145
theorem B3054401 : Blo 880569 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B11443045 : Blo 880569 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B3349421 : Blo 880569 3349421 := bstep (se 3 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 3349421 = 1256033) B1256033
theorem B3349451 : Blo 880569 3349451 := bstep (se 1 (by rfl) ⟨2512088, by rfl⟩ : syracuseStep 3349451 = 5024177) B5024177
theorem B1678295 : Blo 880569 1678295 := bstep (se 1 (by rfl) ⟨1258721, by rfl⟩ : syracuseStep 1678295 = 2517443) B2517443
theorem B1416151 : Blo 880569 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B7543853 : Blo 880569 7543853 := bstep (se 3 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 7543853 = 2828945) B2828945
theorem B6364261 : Blo 880569 6364261 := bstep (se 4 (by rfl) ⟨596649, by rfl⟩ : syracuseStep 6364261 = 1193299) B1193299
theorem B4463747 : Blo 880569 4463747 := bstep (se 1 (by rfl) ⟨3347810, by rfl⟩ : syracuseStep 4463747 = 6695621) B6695621
theorem B3185867 : Blo 880569 3185867 := bstep (se 1 (by rfl) ⟨2389400, by rfl⟩ : syracuseStep 3185867 = 4778801) B4778801
theorem B1678553 : Blo 880569 1678553 := bstep (se 2 (by rfl) ⟨629457, by rfl⟩ : syracuseStep 1678553 = 1258915) B1258915
theorem B2235671 : Blo 880569 2235671 := bstep (se 1 (by rfl) ⟨1676753, by rfl⟩ : syracuseStep 2235671 = 3353507) B3353507
theorem B1416523 : Blo 880569 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B990679 : Blo 880569 990679 := bstep (se 1 (by rfl) ⟨743009, by rfl⟩ : syracuseStep 990679 = 1486019) B1486019
theorem B3350105 : Blo 880569 3350105 := bstep (se 2 (by rfl) ⟨1256289, by rfl⟩ : syracuseStep 3350105 = 2512579) B2512579
theorem B1678963 : Blo 880569 1678963 := bstep (se 1 (by rfl) ⟨1259222, by rfl⟩ : syracuseStep 1678963 = 2518445) B2518445
theorem B990859 : Blo 880569 990859 := bstep (se 1 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 990859 = 1486289) B1486289
theorem B1810163 : Blo 880569 1810163 := bstep (se 1 (by rfl) ⟨1357622, by rfl⟩ : syracuseStep 1810163 = 2715245) B2715245
theorem B990967 : Blo 880569 990967 := bstep (se 1 (by rfl) ⟨743225, by rfl⟩ : syracuseStep 990967 = 1486451) B1486451
theorem B2826049 : Blo 880569 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B3350423 : Blo 880569 3350423 := bstep (se 1 (by rfl) ⟨2512817, by rfl⟩ : syracuseStep 3350423 = 5025635) B5025635
theorem B991147 : Blo 880569 991147 := bstep (se 1 (by rfl) ⟨743360, by rfl⟩ : syracuseStep 991147 = 1486721) B1486721
theorem B7741457 : Blo 880569 7741457 := bstep (se 2 (by rfl) ⟨2903046, by rfl⟩ : syracuseStep 7741457 = 5806093) B5806093
theorem B991255 : Blo 880569 991255 := bstep (se 1 (by rfl) ⟨743441, by rfl⟩ : syracuseStep 991255 = 1486883) B1486883
theorem B2236481 : Blo 880569 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B991435 : Blo 880569 991435 := bstep (se 1 (by rfl) ⟨743576, by rfl⟩ : syracuseStep 991435 = 1487153) B1487153
theorem B3776813 : Blo 880569 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B991543 : Blo 880569 991543 := bstep (se 1 (by rfl) ⟨743657, by rfl⟩ : syracuseStep 991543 = 1487315) B1487315
theorem B991723 : Blo 880569 991723 := bstep (se 1 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 991723 = 1487585) B1487585
theorem B3351091 : Blo 880569 3351091 := bstep (se 1 (by rfl) ⟨2513318, by rfl⟩ : syracuseStep 3351091 = 5026637) B5026637
theorem B991831 : Blo 880569 991831 := bstep (se 1 (by rfl) ⟨743873, by rfl⟩ : syracuseStep 991831 = 1487747) B1487747
theorem B2237017 : Blo 880569 2237017 := bstep (se 2 (by rfl) ⟨838881, by rfl⟩ : syracuseStep 2237017 = 1677763) B1677763
theorem B3777155 : Blo 880569 3777155 := bstep (se 1 (by rfl) ⟨2832866, by rfl⟩ : syracuseStep 3777155 = 5665733) B5665733
theorem B992011 : Blo 880569 992011 := bstep (se 1 (by rfl) ⟨744008, by rfl⟩ : syracuseStep 992011 = 1488017) B1488017
theorem B6693677 : Blo 880569 6693677 := bstep (se 3 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 6693677 = 2510129) B2510129
theorem B992119 : Blo 880569 992119 := bstep (se 1 (by rfl) ⟨744089, by rfl⟩ : syracuseStep 992119 = 1488179) B1488179
theorem B992299 : Blo 880569 992299 := bstep (se 1 (by rfl) ⟨744224, by rfl⟩ : syracuseStep 992299 = 1488449) B1488449
theorem B992407 : Blo 880569 992407 := bstep (se 1 (by rfl) ⟨744305, by rfl⟩ : syracuseStep 992407 = 1488611) B1488611
theorem B992587 : Blo 880569 992587 := bstep (se 1 (by rfl) ⟨744440, by rfl⟩ : syracuseStep 992587 = 1488881) B1488881
theorem B7546243 : Blo 880569 7546243 := bstep (se 1 (by rfl) ⟨5659682, by rfl⟩ : syracuseStep 7546243 = 11319365) B11319365
theorem B1910155 : Blo 880569 1910155 := bstep (se 1 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 1910155 = 2865233) B2865233
theorem B992695 : Blo 880569 992695 := bstep (se 1 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 992695 = 1489043) B1489043
theorem B992875 : Blo 880569 992875 := bstep (se 1 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 992875 = 1489313) B1489313
theorem B2238131 : Blo 880569 2238131 := bstep (se 1 (by rfl) ⟨1678598, by rfl⟩ : syracuseStep 2238131 = 3357197) B3357197
theorem B992983 : Blo 880569 992983 := bstep (se 1 (by rfl) ⟨744737, by rfl⟩ : syracuseStep 992983 = 1489475) B1489475
theorem B2827997 : Blo 880569 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B3352337 : Blo 880569 3352337 := bstep (se 2 (by rfl) ⟨1257126, by rfl⟩ : syracuseStep 3352337 = 2514253) B2514253
theorem B2828125 : Blo 880569 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B993163 : Blo 880569 993163 := bstep (se 1 (by rfl) ⟨744872, by rfl⟩ : syracuseStep 993163 = 1489745) B1489745
theorem B1320857 : Blo 880569 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B2238425 : Blo 880569 2238425 := bstep (se 2 (by rfl) ⟨839409, by rfl⟩ : syracuseStep 2238425 = 1678819) B1678819
theorem B993271 : Blo 880569 993271 := bstep (se 1 (by rfl) ⟨744953, by rfl⟩ : syracuseStep 993271 = 1489907) B1489907
theorem B1320971 : Blo 880569 1320971 := bstep (se 1 (by rfl) ⟨990728, by rfl⟩ : syracuseStep 1320971 = 1981457) B1981457
theorem B1058827 : Blo 880569 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B1320983 : Blo 880569 1320983 := bstep (se 1 (by rfl) ⟨990737, by rfl⟩ : syracuseStep 1320983 = 1981475) B1981475
theorem B1321049 : Blo 880569 1321049 := bstep (se 2 (by rfl) ⟨495393, by rfl⟩ : syracuseStep 1321049 = 990787) B990787
theorem B993451 : Blo 880569 993451 := bstep (se 1 (by rfl) ⟨745088, by rfl⟩ : syracuseStep 993451 = 1490177) B1490177
theorem B15050933 : Blo 880569 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B1321163 : Blo 880569 1321163 := bstep (se 1 (by rfl) ⟨990872, by rfl⟩ : syracuseStep 1321163 = 1981745) B1981745
theorem B1321175 : Blo 880569 1321175 := bstep (se 1 (by rfl) ⟨990881, by rfl⟩ : syracuseStep 1321175 = 1981763) B1981763
theorem B993559 : Blo 880569 993559 := bstep (se 1 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 993559 = 1490339) B1490339
theorem B1321241 : Blo 880569 1321241 := bstep (se 2 (by rfl) ⟨495465, by rfl⟩ : syracuseStep 1321241 = 990931) B990931
theorem B7547201 : Blo 880569 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B1321355 : Blo 880569 1321355 := bstep (se 1 (by rfl) ⟨991016, by rfl⟩ : syracuseStep 1321355 = 1982033) B1982033
theorem B5646743 : Blo 880569 5646743 := bstep (se 1 (by rfl) ⟨4235057, by rfl⟩ : syracuseStep 5646743 = 8470115) B8470115
theorem B1321367 : Blo 880569 1321367 := bstep (se 1 (by rfl) ⟨991025, by rfl⟩ : syracuseStep 1321367 = 1982051) B1982051
theorem B3353035 : Blo 880569 3353035 := bstep (se 1 (by rfl) ⟨2514776, by rfl⟩ : syracuseStep 3353035 = 5029553) B5029553
theorem B993739 : Blo 880569 993739 := bstep (se 1 (by rfl) ⟨745304, by rfl⟩ : syracuseStep 993739 = 1490609) B1490609
theorem B1321433 : Blo 880569 1321433 := bstep (se 2 (by rfl) ⟨495537, by rfl⟩ : syracuseStep 1321433 = 991075) B991075
theorem B993847 : Blo 880569 993847 := bstep (se 1 (by rfl) ⟨745385, by rfl⟩ : syracuseStep 993847 = 1490771) B1490771
theorem B1321547 : Blo 880569 1321547 := bstep (se 1 (by rfl) ⟨991160, by rfl⟩ : syracuseStep 1321547 = 1982321) B1982321
theorem B1321559 : Blo 880569 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B3582557 : Blo 880569 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B1321625 : Blo 880569 1321625 := bstep (se 2 (by rfl) ⟨495609, by rfl⟩ : syracuseStep 1321625 = 991219) B991219
theorem B3353309 : Blo 880569 3353309 := bstep (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) B1257491
theorem B994027 : Blo 880569 994027 := bstep (se 1 (by rfl) ⟨745520, by rfl⟩ : syracuseStep 994027 = 1491041) B1491041
theorem B1321739 : Blo 880569 1321739 := bstep (se 1 (by rfl) ⟨991304, by rfl⟩ : syracuseStep 1321739 = 1982609) B1982609
theorem B4467473 : Blo 880569 4467473 := bstep (se 2 (by rfl) ⟨1675302, by rfl⟩ : syracuseStep 4467473 = 3350605) B3350605
theorem B1321751 : Blo 880569 1321751 := bstep (se 1 (by rfl) ⟨991313, by rfl⟩ : syracuseStep 1321751 = 1982627) B1982627
theorem B994135 : Blo 880569 994135 := bstep (se 1 (by rfl) ⟨745601, by rfl⟩ : syracuseStep 994135 = 1491203) B1491203
theorem B1321817 : Blo 880569 1321817 := bstep (se 2 (by rfl) ⟨495681, by rfl⟩ : syracuseStep 1321817 = 991363) B991363
theorem B4467635 : Blo 880569 4467635 := bstep (se 1 (by rfl) ⟨3350726, by rfl⟩ : syracuseStep 4467635 = 6701453) B6701453
theorem B1321931 : Blo 880569 1321931 := bstep (se 1 (by rfl) ⟨991448, by rfl⟩ : syracuseStep 1321931 = 1982897) B1982897
theorem B1321943 : Blo 880569 1321943 := bstep (se 1 (by rfl) ⟨991457, by rfl⟩ : syracuseStep 1321943 = 1982915) B1982915
theorem B994315 : Blo 880569 994315 := bstep (se 1 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 994315 = 1491473) B1491473
theorem B1322009 : Blo 880569 1322009 := bstep (se 2 (by rfl) ⟨495753, by rfl⟩ : syracuseStep 1322009 = 991507) B991507
theorem B5024861 : Blo 880569 5024861 := bstep (se 3 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 5024861 = 1884323) B1884323
theorem B994423 : Blo 880569 994423 := bstep (se 1 (by rfl) ⟨745817, by rfl⟩ : syracuseStep 994423 = 1491635) B1491635
theorem B1322123 : Blo 880569 1322123 := bstep (se 1 (by rfl) ⟨991592, by rfl⟩ : syracuseStep 1322123 = 1983185) B1983185
theorem B1322135 : Blo 880569 1322135 := bstep (se 1 (by rfl) ⟨991601, by rfl⟩ : syracuseStep 1322135 = 1983203) B1983203
theorem B1191115 : Blo 880569 1191115 := bstep (se 1 (by rfl) ⟨893336, by rfl⟩ : syracuseStep 1191115 = 1786673) B1786673
theorem B1486039 : Blo 880569 1486039 := bstep (se 1 (by rfl) ⟨1114529, by rfl⟩ : syracuseStep 1486039 = 2229059) B2229059
theorem B1191127 : Blo 880569 1191127 := bstep (se 1 (by rfl) ⟨893345, by rfl⟩ : syracuseStep 1191127 = 1786691) B1786691
theorem B1322201 : Blo 880569 1322201 := bstep (se 2 (by rfl) ⟨495825, by rfl⟩ : syracuseStep 1322201 = 991651) B991651
theorem B994603 : Blo 880569 994603 := bstep (se 1 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 994603 = 1491905) B1491905
theorem B1322315 : Blo 880569 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B1322327 : Blo 880569 1322327 := bstep (se 1 (by rfl) ⟨991745, by rfl⟩ : syracuseStep 1322327 = 1983491) B1983491
theorem B1256791 : Blo 880569 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B3354007 : Blo 880569 3354007 := bstep (se 1 (by rfl) ⟨2515505, by rfl⟩ : syracuseStep 3354007 = 5031011) B5031011
theorem B994711 : Blo 880569 994711 := bstep (se 1 (by rfl) ⟨746033, by rfl⟩ : syracuseStep 994711 = 1492067) B1492067
theorem B1322393 : Blo 880569 1322393 := bstep (se 2 (by rfl) ⟨495897, by rfl⟩ : syracuseStep 1322393 = 991795) B991795
theorem B1322507 : Blo 880569 1322507 := bstep (se 1 (by rfl) ⟨991880, by rfl⟩ : syracuseStep 1322507 = 1983761) B1983761
theorem B1322519 : Blo 880569 1322519 := bstep (se 1 (by rfl) ⟨991889, by rfl⟩ : syracuseStep 1322519 = 1983779) B1983779
theorem B994891 : Blo 880569 994891 := bstep (se 1 (by rfl) ⟨746168, by rfl⟩ : syracuseStep 994891 = 1492337) B1492337
theorem B1322585 : Blo 880569 1322585 := bstep (se 2 (by rfl) ⟨495969, by rfl⟩ : syracuseStep 1322585 = 991939) B991939
theorem B4238999 : Blo 880569 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B994999 : Blo 880569 994999 := bstep (se 1 (by rfl) ⟨746249, by rfl⟩ : syracuseStep 994999 = 1492499) B1492499
theorem B1322699 : Blo 880569 1322699 := bstep (se 1 (by rfl) ⟨992024, by rfl⟩ : syracuseStep 1322699 = 1984049) B1984049
theorem B1322711 : Blo 880569 1322711 := bstep (se 1 (by rfl) ⟨992033, by rfl⟩ : syracuseStep 1322711 = 1984067) B1984067
theorem B1322777 : Blo 880569 1322777 := bstep (se 2 (by rfl) ⟨496041, by rfl⟩ : syracuseStep 1322777 = 992083) B992083
theorem B24162113 : Blo 880569 24162113 := bstep (se 2 (by rfl) ⟨9060792, by rfl⟩ : syracuseStep 24162113 = 18121585) B18121585
theorem B1486667 : Blo 880569 1486667 := bstep (se 1 (by rfl) ⟨1115000, by rfl⟩ : syracuseStep 1486667 = 2230001) B2230001
theorem B1322891 : Blo 880569 1322891 := bstep (se 1 (by rfl) ⟨992168, by rfl⟩ : syracuseStep 1322891 = 1984337) B1984337
theorem B1322903 : Blo 880569 1322903 := bstep (se 1 (by rfl) ⟨992177, by rfl⟩ : syracuseStep 1322903 = 1984355) B1984355
theorem B1486795 : Blo 880569 1486795 := bstep (se 1 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 1486795 = 2230193) B2230193
theorem B1322969 : Blo 880569 1322969 := bstep (se 2 (by rfl) ⟨496113, by rfl⟩ : syracuseStep 1322969 = 992227) B992227
theorem B1323083 : Blo 880569 1323083 := bstep (se 1 (by rfl) ⟨992312, by rfl⟩ : syracuseStep 1323083 = 1984625) B1984625
theorem B1323095 : Blo 880569 1323095 := bstep (se 1 (by rfl) ⟨992321, by rfl⟩ : syracuseStep 1323095 = 1984643) B1984643
theorem B1486937 : Blo 880569 1486937 := bstep (se 2 (by rfl) ⟨557601, by rfl⟩ : syracuseStep 1486937 = 1115203) B1115203
theorem B1323161 : Blo 880569 1323161 := bstep (se 2 (by rfl) ⟨496185, by rfl⟩ : syracuseStep 1323161 = 992371) B992371
theorem B3354797 : Blo 880569 3354797 := bstep (se 3 (by rfl) ⟨629024, by rfl⟩ : syracuseStep 3354797 = 1258049) B1258049
theorem B1487065 : Blo 880569 1487065 := bstep (se 2 (by rfl) ⟨557649, by rfl⟩ : syracuseStep 1487065 = 1115299) B1115299
theorem B1323275 : Blo 880569 1323275 := bstep (se 1 (by rfl) ⟨992456, by rfl⟩ : syracuseStep 1323275 = 1984913) B1984913
theorem B1323287 : Blo 880569 1323287 := bstep (se 1 (by rfl) ⟨992465, by rfl⟩ : syracuseStep 1323287 = 1984931) B1984931
theorem B1323353 : Blo 880569 1323353 := bstep (se 2 (by rfl) ⟨496257, by rfl⟩ : syracuseStep 1323353 = 992515) B992515
theorem B15085925 : Blo 880569 15085925 := bstep (se 4 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 15085925 = 2828611) B2828611
theorem B1323467 : Blo 880569 1323467 := bstep (se 1 (by rfl) ⟨992600, by rfl⟩ : syracuseStep 1323467 = 1985201) B1985201
theorem B1323479 : Blo 880569 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B1323545 : Blo 880569 1323545 := bstep (se 2 (by rfl) ⟨496329, by rfl⟩ : syracuseStep 1323545 = 992659) B992659
theorem B6697565 : Blo 880569 6697565 := bstep (se 3 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 6697565 = 2511587) B2511587
theorem B1323659 : Blo 880569 1323659 := bstep (se 1 (by rfl) ⟨992744, by rfl⟩ : syracuseStep 1323659 = 1985489) B1985489
theorem B1323671 : Blo 880569 1323671 := bstep (se 1 (by rfl) ⟨992753, by rfl⟩ : syracuseStep 1323671 = 1985507) B1985507
theorem B1323737 : Blo 880569 1323737 := bstep (se 2 (by rfl) ⟨496401, by rfl⟩ : syracuseStep 1323737 = 992803) B992803
theorem B9679621 : Blo 880569 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B1487639 : Blo 880569 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B4469579 : Blo 880569 4469579 := bstep (se 1 (by rfl) ⟨3352184, by rfl⟩ : syracuseStep 4469579 = 6704369) B6704369
theorem B5649227 : Blo 880569 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B1323851 : Blo 880569 1323851 := bstep (se 1 (by rfl) ⟨992888, by rfl⟩ : syracuseStep 1323851 = 1985777) B1985777
theorem B1323863 : Blo 880569 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B1487767 : Blo 880569 1487767 := bstep (se 1 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 1487767 = 2231651) B2231651
theorem B1323929 : Blo 880569 1323929 := bstep (se 2 (by rfl) ⟨496473, by rfl⟩ : syracuseStep 1323929 = 992947) B992947
theorem B1324043 : Blo 880569 1324043 := bstep (se 1 (by rfl) ⟨993032, by rfl⟩ : syracuseStep 1324043 = 1986065) B1986065
theorem B1324055 : Blo 880569 1324055 := bstep (se 1 (by rfl) ⟨993041, by rfl⟩ : syracuseStep 1324055 = 1986083) B1986083
theorem B1324121 : Blo 880569 1324121 := bstep (se 2 (by rfl) ⟨496545, by rfl⟩ : syracuseStep 1324121 = 993091) B993091
theorem B4764851 : Blo 880569 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B1324235 : Blo 880569 1324235 := bstep (se 1 (by rfl) ⟨993176, by rfl⟩ : syracuseStep 1324235 = 1986353) B1986353
theorem B1324247 : Blo 880569 1324247 := bstep (se 1 (by rfl) ⟨993185, by rfl⟩ : syracuseStep 1324247 = 1986371) B1986371
theorem B2012417 : Blo 880569 2012417 := bstep (se 2 (by rfl) ⟨754656, by rfl⟩ : syracuseStep 2012417 = 1509313) B1509313
theorem B1324313 : Blo 880569 1324313 := bstep (se 2 (by rfl) ⟨496617, by rfl⟩ : syracuseStep 1324313 = 993235) B993235
theorem B1258841 : Blo 880569 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B1324427 : Blo 880569 1324427 := bstep (se 1 (by rfl) ⟨993320, by rfl⟩ : syracuseStep 1324427 = 1986641) B1986641
theorem B1324439 : Blo 880569 1324439 := bstep (se 1 (by rfl) ⟨993329, by rfl⟩ : syracuseStep 1324439 = 1986659) B1986659
theorem B1324505 : Blo 880569 1324505 := bstep (se 2 (by rfl) ⟨496689, by rfl⟩ : syracuseStep 1324505 = 993379) B993379
theorem B1488395 : Blo 880569 1488395 := bstep (se 1 (by rfl) ⟨1116296, by rfl⟩ : syracuseStep 1488395 = 2232593) B2232593
theorem B5027345 : Blo 880569 5027345 := bstep (se 2 (by rfl) ⟨1885254, by rfl⟩ : syracuseStep 5027345 = 3770509) B3770509
theorem B3356225 : Blo 880569 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B1324619 : Blo 880569 1324619 := bstep (se 1 (by rfl) ⟨993464, by rfl⟩ : syracuseStep 1324619 = 1986929) B1986929
theorem B1324631 : Blo 880569 1324631 := bstep (se 1 (by rfl) ⟨993473, by rfl⟩ : syracuseStep 1324631 = 1986947) B1986947
theorem B1586827 : Blo 880569 1586827 := bstep (se 1 (by rfl) ⟨1190120, by rfl⟩ : syracuseStep 1586827 = 2380241) B2380241
theorem B1488523 : Blo 880569 1488523 := bstep (se 1 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 1488523 = 2232785) B2232785
theorem B1324697 : Blo 880569 1324697 := bstep (se 2 (by rfl) ⟨496761, by rfl⟩ : syracuseStep 1324697 = 993523) B993523
theorem B1324811 : Blo 880569 1324811 := bstep (se 1 (by rfl) ⟨993608, by rfl⟩ : syracuseStep 1324811 = 1987217) B1987217
theorem B1324823 : Blo 880569 1324823 := bstep (se 1 (by rfl) ⟨993617, by rfl⟩ : syracuseStep 1324823 = 1987235) B1987235
theorem B1488665 : Blo 880569 1488665 := bstep (se 2 (by rfl) ⟨558249, by rfl⟩ : syracuseStep 1488665 = 1116499) B1116499
theorem B1324889 : Blo 880569 1324889 := bstep (se 2 (by rfl) ⟨496833, by rfl⟩ : syracuseStep 1324889 = 993667) B993667
theorem B1488793 : Blo 880569 1488793 := bstep (se 2 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 1488793 = 1116595) B1116595
theorem B1325003 : Blo 880569 1325003 := bstep (se 1 (by rfl) ⟨993752, by rfl⟩ : syracuseStep 1325003 = 1987505) B1987505
theorem B1325015 : Blo 880569 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B1325081 : Blo 880569 1325081 := bstep (se 2 (by rfl) ⟨496905, by rfl⟩ : syracuseStep 1325081 = 993811) B993811
theorem B4536395 : Blo 880569 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B1587289 : Blo 880569 1587289 := bstep (se 2 (by rfl) ⟨595233, by rfl⟩ : syracuseStep 1587289 = 1190467) B1190467
theorem B1325195 : Blo 880569 1325195 := bstep (se 1 (by rfl) ⟨993896, by rfl⟩ : syracuseStep 1325195 = 1987793) B1987793
theorem B1325207 : Blo 880569 1325207 := bstep (se 1 (by rfl) ⟨993905, by rfl⟩ : syracuseStep 1325207 = 1987811) B1987811
theorem B1325273 : Blo 880569 1325273 := bstep (se 2 (by rfl) ⟨496977, by rfl⟩ : syracuseStep 1325273 = 993955) B993955
theorem B1325387 : Blo 880569 1325387 := bstep (se 1 (by rfl) ⟨994040, by rfl⟩ : syracuseStep 1325387 = 1988081) B1988081
theorem B1325399 : Blo 880569 1325399 := bstep (se 1 (by rfl) ⟨994049, by rfl⟩ : syracuseStep 1325399 = 1988099) B1988099
theorem B1325465 : Blo 880569 1325465 := bstep (se 2 (by rfl) ⟨497049, by rfl⟩ : syracuseStep 1325465 = 994099) B994099
theorem B1489367 : Blo 880569 1489367 := bstep (se 1 (by rfl) ⟨1117025, by rfl⟩ : syracuseStep 1489367 = 2234051) B2234051
theorem B1325579 : Blo 880569 1325579 := bstep (se 1 (by rfl) ⟨994184, by rfl⟩ : syracuseStep 1325579 = 1988369) B1988369
theorem B1325591 : Blo 880569 1325591 := bstep (se 1 (by rfl) ⟨994193, by rfl⟩ : syracuseStep 1325591 = 1988387) B1988387
theorem B4471361 : Blo 880569 4471361 := bstep (se 2 (by rfl) ⟨1676760, by rfl⟩ : syracuseStep 4471361 = 3353521) B3353521
theorem B1489495 : Blo 880569 1489495 := bstep (se 1 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 1489495 = 2234243) B2234243
theorem B1325657 : Blo 880569 1325657 := bstep (se 2 (by rfl) ⟨497121, by rfl⟩ : syracuseStep 1325657 = 994243) B994243
theorem B1325771 : Blo 880569 1325771 := bstep (se 1 (by rfl) ⟨994328, by rfl⟩ : syracuseStep 1325771 = 1988657) B1988657
theorem B1325783 : Blo 880569 1325783 := bstep (se 1 (by rfl) ⟨994337, by rfl⟩ : syracuseStep 1325783 = 1988675) B1988675
theorem B5094161 : Blo 880569 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B1325849 : Blo 880569 1325849 := bstep (se 2 (by rfl) ⟨497193, by rfl⟩ : syracuseStep 1325849 = 994387) B994387
theorem B16169827 : Blo 880569 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B1981313 : Blo 880569 1981313 := bstep (se 2 (by rfl) ⟨742992, by rfl⟩ : syracuseStep 1981313 = 1485985) B1485985
theorem B1325963 : Blo 880569 1325963 := bstep (se 1 (by rfl) ⟨994472, by rfl⟩ : syracuseStep 1325963 = 1988945) B1988945
theorem B1325975 : Blo 880569 1325975 := bstep (se 1 (by rfl) ⟨994481, by rfl⟩ : syracuseStep 1325975 = 1988963) B1988963
theorem B1326041 : Blo 880569 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B3357713 : Blo 880569 3357713 := bstep (se 2 (by rfl) ⟨1259142, by rfl⟩ : syracuseStep 3357713 = 2518285) B2518285
theorem B1326155 : Blo 880569 1326155 := bstep (se 1 (by rfl) ⟨994616, by rfl⟩ : syracuseStep 1326155 = 1989233) B1989233
theorem B1326167 : Blo 880569 1326167 := bstep (se 1 (by rfl) ⟨994625, by rfl⟩ : syracuseStep 1326167 = 1989251) B1989251
theorem B1981529 : Blo 880569 1981529 := bstep (se 2 (by rfl) ⟨743073, by rfl⟩ : syracuseStep 1981529 = 1486147) B1486147
theorem B1326233 : Blo 880569 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B1981619 : Blo 880569 1981619 := bstep (se 1 (by rfl) ⟨1486214, by rfl⟩ : syracuseStep 1981619 = 2972429) B2972429
theorem B1490123 : Blo 880569 1490123 := bstep (se 1 (by rfl) ⟨1117592, by rfl⟩ : syracuseStep 1490123 = 2235185) B2235185
theorem B1981655 : Blo 880569 1981655 := bstep (se 1 (by rfl) ⟨1486241, by rfl⟩ : syracuseStep 1981655 = 2972483) B2972483
theorem B1326347 : Blo 880569 1326347 := bstep (se 1 (by rfl) ⟨994760, by rfl⟩ : syracuseStep 1326347 = 1989521) B1989521
theorem B1326359 : Blo 880569 1326359 := bstep (se 1 (by rfl) ⟨994769, by rfl⟩ : syracuseStep 1326359 = 1989539) B1989539
theorem B1883417 : Blo 880569 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B1490251 : Blo 880569 1490251 := bstep (se 1 (by rfl) ⟨1117688, by rfl⟩ : syracuseStep 1490251 = 2235377) B2235377
theorem B1326425 : Blo 880569 1326425 := bstep (se 2 (by rfl) ⟨497409, by rfl⟩ : syracuseStep 1326425 = 994819) B994819
theorem B1981835 : Blo 880569 1981835 := bstep (se 1 (by rfl) ⟨1486376, by rfl⟩ : syracuseStep 1981835 = 2972753) B2972753
theorem B1981889 : Blo 880569 1981889 := bstep (se 2 (by rfl) ⟨743208, by rfl⟩ : syracuseStep 1981889 = 1486417) B1486417
theorem B1326539 : Blo 880569 1326539 := bstep (se 1 (by rfl) ⟨994904, by rfl⟩ : syracuseStep 1326539 = 1989809) B1989809
theorem B1326551 : Blo 880569 1326551 := bstep (se 1 (by rfl) ⟨994913, by rfl⟩ : syracuseStep 1326551 = 1989827) B1989827
theorem B1490393 : Blo 880569 1490393 := bstep (se 2 (by rfl) ⟨558897, by rfl⟩ : syracuseStep 1490393 = 1117795) B1117795
theorem B3358169 : Blo 880569 3358169 := bstep (se 2 (by rfl) ⟨1259313, by rfl⟩ : syracuseStep 3358169 = 2518627) B2518627
theorem B1359385 : Blo 880569 1359385 := bstep (se 2 (by rfl) ⟨509769, by rfl⟩ : syracuseStep 1359385 = 1019539) B1019539
theorem B1326617 : Blo 880569 1326617 := bstep (se 2 (by rfl) ⟨497481, by rfl⟩ : syracuseStep 1326617 = 994963) B994963
theorem B3063361 : Blo 880569 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B1490521 : Blo 880569 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B1326731 : Blo 880569 1326731 := bstep (se 1 (by rfl) ⟨995048, by rfl⟩ : syracuseStep 1326731 = 1990097) B1990097
theorem B1326743 : Blo 880569 1326743 := bstep (se 1 (by rfl) ⟨995057, by rfl⟩ : syracuseStep 1326743 = 1990115) B1990115
theorem B1982105 : Blo 880569 1982105 := bstep (se 2 (by rfl) ⟨743289, by rfl⟩ : syracuseStep 1982105 = 1486579) B1486579
theorem B3358381 : Blo 880569 3358381 := bstep (se 3 (by rfl) ⟨629696, by rfl⟩ : syracuseStep 3358381 = 1259393) B1259393
theorem B1883827 : Blo 880569 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B1326809 : Blo 880569 1326809 := bstep (se 2 (by rfl) ⟨497553, by rfl⟩ : syracuseStep 1326809 = 995107) B995107
theorem B1982195 : Blo 880569 1982195 := bstep (se 1 (by rfl) ⟨1486646, by rfl⟩ : syracuseStep 1982195 = 2973293) B2973293
theorem B9060101 : Blo 880569 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B1982231 : Blo 880569 1982231 := bstep (se 1 (by rfl) ⟨1486673, by rfl⟩ : syracuseStep 1982231 = 2973347) B2973347
theorem B4767619 : Blo 880569 4767619 := bstep (se 1 (by rfl) ⟨3575714, by rfl⟩ : syracuseStep 4767619 = 7151429) B7151429
theorem B1982411 : Blo 880569 1982411 := bstep (se 1 (by rfl) ⟨1486808, by rfl⟩ : syracuseStep 1982411 = 2973617) B2973617
theorem B1982465 : Blo 880569 1982465 := bstep (se 2 (by rfl) ⟨743424, by rfl⟩ : syracuseStep 1982465 = 1486849) B1486849
theorem B1589249 : Blo 880569 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B1884161 : Blo 880569 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B5652611 : Blo 880569 5652611 := bstep (se 1 (by rfl) ⟨4239458, by rfl⟩ : syracuseStep 5652611 = 8478917) B8478917
theorem B1491095 : Blo 880569 1491095 := bstep (se 1 (by rfl) ⟨1118321, by rfl⟩ : syracuseStep 1491095 = 2236643) B2236643
theorem B5357785 : Blo 880569 5357785 := bstep (se 2 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 5357785 = 4018339) B4018339
theorem B1982681 : Blo 880569 1982681 := bstep (se 2 (by rfl) ⟨743505, by rfl⟩ : syracuseStep 1982681 = 1487011) B1487011
theorem B1491223 : Blo 880569 1491223 := bstep (se 1 (by rfl) ⟨1118417, by rfl⟩ : syracuseStep 1491223 = 2236835) B2236835
theorem B1982771 : Blo 880569 1982771 := bstep (se 1 (by rfl) ⟨1487078, by rfl⟩ : syracuseStep 1982771 = 2974157) B2974157
theorem B1982807 : Blo 880569 1982807 := bstep (se 1 (by rfl) ⟨1487105, by rfl⟩ : syracuseStep 1982807 = 2974211) B2974211
theorem B4473305 : Blo 880569 4473305 := bstep (se 2 (by rfl) ⟨1677489, by rfl⟩ : syracuseStep 4473305 = 3354979) B3354979
theorem B1982987 : Blo 880569 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B24461837 : Blo 880569 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B1983041 : Blo 880569 1983041 := bstep (se 2 (by rfl) ⟨743640, by rfl⟩ : syracuseStep 1983041 = 1487281) B1487281
theorem B1884887 : Blo 880569 1884887 := bstep (se 1 (by rfl) ⟨1413665, by rfl⟩ : syracuseStep 1884887 = 2827331) B2827331
theorem B1983257 : Blo 880569 1983257 := bstep (se 2 (by rfl) ⟨743721, by rfl⟩ : syracuseStep 1983257 = 1487443) B1487443
theorem B1983347 : Blo 880569 1983347 := bstep (se 1 (by rfl) ⟨1487510, by rfl⟩ : syracuseStep 1983347 = 2975021) B2975021
theorem B3392387 : Blo 880569 3392387 := bstep (se 1 (by rfl) ⟨2544290, by rfl⟩ : syracuseStep 3392387 = 5088581) B5088581
theorem B1491851 : Blo 880569 1491851 := bstep (se 1 (by rfl) ⟨1118888, by rfl⟩ : syracuseStep 1491851 = 2237777) B2237777
theorem B1983383 : Blo 880569 1983383 := bstep (se 1 (by rfl) ⟨1487537, by rfl⟩ : syracuseStep 1983383 = 2975075) B2975075
theorem B1491979 : Blo 880569 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B2507851 : Blo 880569 2507851 := bstep (se 1 (by rfl) ⟨1880888, by rfl⟩ : syracuseStep 2507851 = 3761777) B3761777
theorem B1983563 : Blo 880569 1983563 := bstep (se 1 (by rfl) ⟨1487672, by rfl⟩ : syracuseStep 1983563 = 2975345) B2975345
theorem B1590359 : Blo 880569 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1983617 : Blo 880569 1983617 := bstep (se 2 (by rfl) ⟨743856, by rfl⟩ : syracuseStep 1983617 = 1487713) B1487713
theorem B1492121 : Blo 880569 1492121 := bstep (se 2 (by rfl) ⟨559545, by rfl⟩ : syracuseStep 1492121 = 1119091) B1119091
theorem B1361099 : Blo 880569 1361099 := bstep (se 1 (by rfl) ⟨1020824, by rfl⟩ : syracuseStep 1361099 = 2041649) B2041649
theorem B1492249 : Blo 880569 1492249 := bstep (se 2 (by rfl) ⟨559593, by rfl⟩ : syracuseStep 1492249 = 1119187) B1119187
theorem B1983833 : Blo 880569 1983833 := bstep (se 2 (by rfl) ⟨743937, by rfl⟩ : syracuseStep 1983833 = 1487875) B1487875
theorem B1983923 : Blo 880569 1983923 := bstep (se 1 (by rfl) ⟨1487942, by rfl⟩ : syracuseStep 1983923 = 2975885) B2975885
theorem B1983959 : Blo 880569 1983959 := bstep (se 1 (by rfl) ⟨1487969, by rfl⟩ : syracuseStep 1983959 = 2975939) B2975939
theorem B1590835 : Blo 880569 1590835 := bstep (se 1 (by rfl) ⟨1193126, by rfl⟩ : syracuseStep 1590835 = 2386253) B2386253
theorem B2508353 : Blo 880569 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B6374987 : Blo 880569 6374987 := bstep (se 1 (by rfl) ⟨4781240, by rfl⟩ : syracuseStep 6374987 = 9562481) B9562481
theorem B1984139 : Blo 880569 1984139 := bstep (se 1 (by rfl) ⟨1488104, by rfl⟩ : syracuseStep 1984139 = 2976209) B2976209
theorem B1984193 : Blo 880569 1984193 := bstep (se 2 (by rfl) ⟨744072, by rfl⟩ : syracuseStep 1984193 = 1488145) B1488145
theorem B2508695 : Blo 880569 2508695 := bstep (se 1 (by rfl) ⟨1881521, by rfl⟩ : syracuseStep 2508695 = 3763043) B3763043
theorem B1984409 : Blo 880569 1984409 := bstep (se 2 (by rfl) ⟨744153, by rfl⟩ : syracuseStep 1984409 = 1488307) B1488307
theorem B1984499 : Blo 880569 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B1984535 : Blo 880569 1984535 := bstep (se 1 (by rfl) ⟨1488401, by rfl⟩ : syracuseStep 1984535 = 2976803) B2976803
theorem B1722391 : Blo 880569 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B4474925 : Blo 880569 4474925 := bstep (se 3 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 4474925 = 1678097) B1678097
theorem B1984715 : Blo 880569 1984715 := bstep (se 1 (by rfl) ⟨1488536, by rfl⟩ : syracuseStep 1984715 = 2977073) B2977073
theorem B1984769 : Blo 880569 1984769 := bstep (se 2 (by rfl) ⟨744288, by rfl⟩ : syracuseStep 1984769 = 1488577) B1488577
theorem B3393857 : Blo 880569 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B2115991 : Blo 880569 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B1984985 : Blo 880569 1984985 := bstep (se 2 (by rfl) ⟨744369, by rfl⟩ : syracuseStep 1984985 = 1488739) B1488739
theorem B1985075 : Blo 880569 1985075 := bstep (se 1 (by rfl) ⟨1488806, by rfl⟩ : syracuseStep 1985075 = 2977613) B2977613
theorem B1591859 : Blo 880569 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B1985111 : Blo 880569 1985111 := bstep (se 1 (by rfl) ⟨1488833, by rfl⟩ : syracuseStep 1985111 = 2977667) B2977667
theorem B1133195 : Blo 880569 1133195 := bstep (se 1 (by rfl) ⟨849896, by rfl⟩ : syracuseStep 1133195 = 1699793) B1699793
theorem B1592011 : Blo 880569 1592011 := bstep (se 1 (by rfl) ⟨1194008, by rfl⟩ : syracuseStep 1592011 = 2388017) B2388017
theorem B1985291 : Blo 880569 1985291 := bstep (se 1 (by rfl) ⟨1488968, by rfl⟩ : syracuseStep 1985291 = 2977937) B2977937
theorem B1592075 : Blo 880569 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1985345 : Blo 880569 1985345 := bstep (se 2 (by rfl) ⟨744504, by rfl⟩ : syracuseStep 1985345 = 1489009) B1489009
theorem B3394507 : Blo 880569 3394507 := bstep (se 1 (by rfl) ⟨2545880, by rfl⟩ : syracuseStep 3394507 = 5091761) B5091761
theorem B1985561 : Blo 880569 1985561 := bstep (se 2 (by rfl) ⟨744585, by rfl⟩ : syracuseStep 1985561 = 1489171) B1489171
theorem B1985651 : Blo 880569 1985651 := bstep (se 1 (by rfl) ⟨1489238, by rfl⟩ : syracuseStep 1985651 = 2978477) B2978477
theorem B1887347 : Blo 880569 1887347 := bstep (se 1 (by rfl) ⟨1415510, by rfl⟩ : syracuseStep 1887347 = 2831021) B2831021
theorem B1985687 : Blo 880569 1985687 := bstep (se 1 (by rfl) ⟨1489265, by rfl⟩ : syracuseStep 1985687 = 2978531) B2978531
theorem B1592473 : Blo 880569 1592473 := bstep (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) B1194355
theorem B8473805 : Blo 880569 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B5033177 : Blo 880569 5033177 := bstep (se 2 (by rfl) ⟨1887441, by rfl⟩ : syracuseStep 5033177 = 3774883) B3774883
theorem B1985867 : Blo 880569 1985867 := bstep (se 1 (by rfl) ⟨1489400, by rfl⟩ : syracuseStep 1985867 = 2978801) B2978801
theorem B19123573 : Blo 880569 19123573 := bstep (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) B1792835
theorem B1985921 : Blo 880569 1985921 := bstep (se 2 (by rfl) ⟨744720, by rfl⟩ : syracuseStep 1985921 = 1489441) B1489441
theorem B1986137 : Blo 880569 1986137 := bstep (se 2 (by rfl) ⟨744801, by rfl⟩ : syracuseStep 1986137 = 1489603) B1489603
theorem B1986227 : Blo 880569 1986227 := bstep (se 1 (by rfl) ⟨1489670, by rfl⟩ : syracuseStep 1986227 = 2979341) B2979341
theorem B1986263 : Blo 880569 1986263 := bstep (se 1 (by rfl) ⟨1489697, by rfl⟩ : syracuseStep 1986263 = 2979395) B2979395
theorem B1986443 : Blo 880569 1986443 := bstep (se 1 (by rfl) ⟨1489832, by rfl⟩ : syracuseStep 1986443 = 2979665) B2979665
theorem B1986497 : Blo 880569 1986497 := bstep (se 2 (by rfl) ⟨744936, by rfl⟩ : syracuseStep 1986497 = 1489873) B1489873
theorem B2510813 : Blo 880569 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B1790039 : Blo 880569 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1986713 : Blo 880569 1986713 := bstep (se 2 (by rfl) ⟨745017, by rfl⟩ : syracuseStep 1986713 = 1490035) B1490035
theorem B1986803 : Blo 880569 1986803 := bstep (se 1 (by rfl) ⟨1490102, by rfl⟩ : syracuseStep 1986803 = 2980205) B2980205
theorem B1986839 : Blo 880569 1986839 := bstep (se 1 (by rfl) ⟨1490129, by rfl⟩ : syracuseStep 1986839 = 2980259) B2980259
theorem B1888535 : Blo 880569 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B2511155 : Blo 880569 2511155 := bstep (se 1 (by rfl) ⟨1883366, by rfl⟩ : syracuseStep 2511155 = 3766733) B3766733
theorem B1593689 : Blo 880569 1593689 := bstep (se 2 (by rfl) ⟨597633, by rfl⟩ : syracuseStep 1593689 = 1195267) B1195267
theorem B9163109 : Blo 880569 9163109 := bstep (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) B1718083
theorem B1987019 : Blo 880569 1987019 := bstep (se 1 (by rfl) ⟨1490264, by rfl⟩ : syracuseStep 1987019 = 2980529) B2980529
theorem B1987073 : Blo 880569 1987073 := bstep (se 2 (by rfl) ⟨745152, by rfl⟩ : syracuseStep 1987073 = 1490305) B1490305
theorem B1593857 : Blo 880569 1593857 := bstep (se 2 (by rfl) ⟨597696, by rfl⟩ : syracuseStep 1593857 = 1195393) B1195393
theorem B1987289 : Blo 880569 1987289 := bstep (se 2 (by rfl) ⟨745233, by rfl⟩ : syracuseStep 1987289 = 1490467) B1490467
theorem B1987379 : Blo 880569 1987379 := bstep (se 1 (by rfl) ⟨1490534, by rfl⟩ : syracuseStep 1987379 = 2981069) B2981069
theorem B1987415 : Blo 880569 1987415 := bstep (se 1 (by rfl) ⟨1490561, by rfl⟩ : syracuseStep 1987415 = 2981123) B2981123
theorem B1790923 : Blo 880569 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B1987595 : Blo 880569 1987595 := bstep (se 1 (by rfl) ⟨1490696, by rfl⟩ : syracuseStep 1987595 = 2981393) B2981393
theorem B1987649 : Blo 880569 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B2381021 : Blo 880569 2381021 := bstep (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) B892883
theorem B1987865 : Blo 880569 1987865 := bstep (se 2 (by rfl) ⟨745449, by rfl⟩ : syracuseStep 1987865 = 1490899) B1490899
theorem B1987955 : Blo 880569 1987955 := bstep (se 1 (by rfl) ⟨1490966, by rfl⟩ : syracuseStep 1987955 = 2981933) B2981933
theorem B1987991 : Blo 880569 1987991 := bstep (se 1 (by rfl) ⟨1490993, by rfl⟩ : syracuseStep 1987991 = 2981987) B2981987
theorem B2119115 : Blo 880569 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B1988171 : Blo 880569 1988171 := bstep (se 1 (by rfl) ⟨1491128, by rfl⟩ : syracuseStep 1988171 = 2982257) B2982257
theorem B1988225 : Blo 880569 1988225 := bstep (se 2 (by rfl) ⟨745584, by rfl⟩ : syracuseStep 1988225 = 1491169) B1491169
theorem B9557635 : Blo 880569 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B1005259 : Blo 880569 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B5035841 : Blo 880569 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B1988441 : Blo 880569 1988441 := bstep (se 2 (by rfl) ⟨745665, by rfl⟩ : syracuseStep 1988441 = 1491331) B1491331
theorem B1988531 : Blo 880569 1988531 := bstep (se 1 (by rfl) ⟨1491398, by rfl⟩ : syracuseStep 1988531 = 2982797) B2982797
theorem B1988567 : Blo 880569 1988567 := bstep (se 1 (by rfl) ⟨1491425, by rfl⟩ : syracuseStep 1988567 = 2982851) B2982851
theorem B1792025 : Blo 880569 1792025 := bstep (se 2 (by rfl) ⟨672009, by rfl⟩ : syracuseStep 1792025 = 1344019) B1344019
theorem B1792115 : Blo 880569 1792115 := bstep (se 1 (by rfl) ⟨1344086, by rfl⟩ : syracuseStep 1792115 = 2688173) B2688173
theorem B1988747 : Blo 880569 1988747 := bstep (se 1 (by rfl) ⟨1491560, by rfl⟩ : syracuseStep 1988747 = 2983121) B2983121
theorem B1988801 : Blo 880569 1988801 := bstep (se 2 (by rfl) ⟨745800, by rfl⟩ : syracuseStep 1988801 = 1491601) B1491601
theorem B2971997 : Blo 880569 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B68802929 : Blo 880569 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B32135573 : Blo 880569 32135573 := bstep (se 6 (by rfl) ⟨753177, by rfl⟩ : syracuseStep 32135573 = 1506355) B1506355
theorem B1989017 : Blo 880569 1989017 := bstep (se 2 (by rfl) ⟨745881, by rfl⟩ : syracuseStep 1989017 = 1491763) B1491763
theorem B1989107 : Blo 880569 1989107 := bstep (se 1 (by rfl) ⟨1491830, by rfl⟩ : syracuseStep 1989107 = 2983661) B2983661
theorem B1989143 : Blo 880569 1989143 := bstep (se 1 (by rfl) ⟨1491857, by rfl⟩ : syracuseStep 1989143 = 2983715) B2983715
theorem B2513501 : Blo 880569 2513501 := bstep (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) B942563
theorem B29055685 : Blo 880569 29055685 := bstep (se 4 (by rfl) ⟨2723970, by rfl⟩ : syracuseStep 29055685 = 5447941) B5447941
theorem B1989323 : Blo 880569 1989323 := bstep (se 1 (by rfl) ⟨1491992, by rfl⟩ : syracuseStep 1989323 = 2983985) B2983985
theorem B1989377 : Blo 880569 1989377 := bstep (se 2 (by rfl) ⟨746016, by rfl⟩ : syracuseStep 1989377 = 1492033) B1492033
theorem B2513729 : Blo 880569 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B1989593 : Blo 880569 1989593 := bstep (se 2 (by rfl) ⟨746097, by rfl⟩ : syracuseStep 1989593 = 1492195) B1492195
theorem B1989683 : Blo 880569 1989683 := bstep (se 1 (by rfl) ⟨1492262, by rfl⟩ : syracuseStep 1989683 = 2984525) B2984525
theorem B1989719 : Blo 880569 1989719 := bstep (se 1 (by rfl) ⟨1492289, by rfl⟩ : syracuseStep 1989719 = 2984579) B2984579
theorem B2514071 : Blo 880569 2514071 := bstep (se 1 (by rfl) ⟨1885553, by rfl⟩ : syracuseStep 2514071 = 3771107) B3771107
theorem B2120921 : Blo 880569 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B5659865 : Blo 880569 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B1989899 : Blo 880569 1989899 := bstep (se 1 (by rfl) ⟨1492424, by rfl⟩ : syracuseStep 1989899 = 2984849) B2984849
theorem B1989953 : Blo 880569 1989953 := bstep (se 2 (by rfl) ⟨746232, by rfl⟩ : syracuseStep 1989953 = 1492465) B1492465
theorem B2973131 : Blo 880569 2973131 := bstep (se 1 (by rfl) ⟨2229848, by rfl⟩ : syracuseStep 2973131 = 4459697) B4459697
theorem B7167449 : Blo 880569 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B6348293 : Blo 880569 6348293 := bstep (se 4 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 6348293 = 1190305) B1190305
theorem B1990169 : Blo 880569 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B1990259 : Blo 880569 1990259 := bstep (se 1 (by rfl) ⟨1492694, by rfl⟩ : syracuseStep 1990259 = 2985389) B2985389
theorem B2973401 : Blo 880569 2973401 := bstep (se 2 (by rfl) ⟨1115025, by rfl⟩ : syracuseStep 2973401 = 2230051) B2230051
theorem B4087883 : Blo 880569 4087883 := bstep (se 1 (by rfl) ⟨3065912, by rfl⟩ : syracuseStep 4087883 = 6131825) B6131825
theorem B2974103 : Blo 880569 2974103 := bstep (se 1 (by rfl) ⟨2230577, by rfl⟩ : syracuseStep 2974103 = 4461155) B4461155
theorem B16114211 : Blo 880569 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B12706379 : Blo 880569 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B2974643 : Blo 880569 2974643 := bstep (se 1 (by rfl) ⟨2230982, by rfl⟩ : syracuseStep 2974643 = 4461965) B4461965
theorem B943255 : Blo 880569 943255 := bstep (se 1 (by rfl) ⟨707441, by rfl⟩ : syracuseStep 943255 = 1414883) B1414883
theorem B2974913 : Blo 880569 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B5367001 : Blo 880569 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B10052909 : Blo 880569 10052909 := bstep (se 3 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 10052909 = 3769841) B3769841
theorem B2516417 : Blo 880569 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B2680523 : Blo 880569 2680523 := bstep (se 1 (by rfl) ⟨2010392, by rfl⟩ : syracuseStep 2680523 = 4020785) B4020785
theorem B2975453 : Blo 880569 2975453 := bstep (se 3 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 2975453 = 1115795) B1115795
theorem B7268131 : Blo 880569 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B3401617 : Blo 880569 3401617 := bstep (se 2 (by rfl) ⟨1275606, by rfl⟩ : syracuseStep 3401617 = 2551213) B2551213
theorem B9529265 : Blo 880569 9529265 := bstep (se 2 (by rfl) ⟨3573474, by rfl⟩ : syracuseStep 9529265 = 7146949) B7146949
theorem B2516953 : Blo 880569 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B7170565 : Blo 880569 7170565 := bstep (se 4 (by rfl) ⟨672240, by rfl⟩ : syracuseStep 7170565 = 1344481) B1344481
theorem B5368385 : Blo 880569 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B3271427 : Blo 880569 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B2976587 : Blo 880569 2976587 := bstep (se 1 (by rfl) ⟨2232440, by rfl⟩ : syracuseStep 2976587 = 4464881) B4464881
theorem B7531481 : Blo 880569 7531481 := bstep (se 2 (by rfl) ⟨2824305, by rfl⟩ : syracuseStep 7531481 = 5648611) B5648611
theorem B2976857 : Blo 880569 2976857 := bstep (se 2 (by rfl) ⟨1116321, by rfl⟩ : syracuseStep 2976857 = 2232643) B2232643
theorem B3763417 : Blo 880569 3763417 := bstep (se 2 (by rfl) ⟨1411281, by rfl⟩ : syracuseStep 3763417 = 2822563) B2822563
theorem B7630085 : Blo 880569 7630085 := bstep (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) B1430641
theorem B2977559 : Blo 880569 2977559 := bstep (se 1 (by rfl) ⟨2233169, by rfl⟩ : syracuseStep 2977559 = 4466339) B4466339
theorem B3764033 : Blo 880569 3764033 := bstep (se 2 (by rfl) ⟨1411512, by rfl⟩ : syracuseStep 3764033 = 2823025) B2823025
theorem B21458753 : Blo 880569 21458753 := bstep (se 2 (by rfl) ⟨8047032, by rfl⟩ : syracuseStep 21458753 = 16094065) B16094065
theorem B2518877 : Blo 880569 2518877 := bstep (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) B944579
theorem B880587 : Blo 880569 880587 := bstep (se 1 (by rfl) ⟨660440, by rfl⟩ : syracuseStep 880587 = 1320881) B1320881
theorem B880599 : Blo 880569 880599 := bstep (se 1 (by rfl) ⟨660449, by rfl⟩ : syracuseStep 880599 = 1320899) B1320899
theorem B2551769 : Blo 880569 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B880619 : Blo 880569 880619 := bstep (se 1 (by rfl) ⟨660464, by rfl⟩ : syracuseStep 880619 = 1320929) B1320929
theorem B880631 : Blo 880569 880631 := bstep (se 1 (by rfl) ⟨660473, by rfl⟩ : syracuseStep 880631 = 1320947) B1320947
theorem B880651 : Blo 880569 880651 := bstep (se 1 (by rfl) ⟨660488, by rfl⟩ : syracuseStep 880651 = 1320977) B1320977
theorem B880663 : Blo 880569 880663 := bstep (se 1 (by rfl) ⟨660497, by rfl⟩ : syracuseStep 880663 = 1320995) B1320995
theorem B880683 : Blo 880569 880683 := bstep (se 1 (by rfl) ⟨660512, by rfl⟩ : syracuseStep 880683 = 1321025) B1321025
theorem B880695 : Blo 880569 880695 := bstep (se 1 (by rfl) ⟨660521, by rfl⟩ : syracuseStep 880695 = 1321043) B1321043
theorem B880715 : Blo 880569 880715 := bstep (se 1 (by rfl) ⟨660536, by rfl⟩ : syracuseStep 880715 = 1321073) B1321073
theorem B880727 : Blo 880569 880727 := bstep (se 1 (by rfl) ⟨660545, by rfl⟩ : syracuseStep 880727 = 1321091) B1321091
theorem B880747 : Blo 880569 880747 := bstep (se 1 (by rfl) ⟨660560, by rfl⟩ : syracuseStep 880747 = 1321121) B1321121
theorem B880759 : Blo 880569 880759 := bstep (se 1 (by rfl) ⟨660569, by rfl⟩ : syracuseStep 880759 = 1321139) B1321139
theorem B880779 : Blo 880569 880779 := bstep (se 1 (by rfl) ⟨660584, by rfl⟩ : syracuseStep 880779 = 1321169) B1321169
theorem B880791 : Blo 880569 880791 := bstep (se 1 (by rfl) ⟨660593, by rfl⟩ : syracuseStep 880791 = 1321187) B1321187
theorem B18346135 : Blo 880569 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B880811 : Blo 880569 880811 := bstep (se 1 (by rfl) ⟨660608, by rfl⟩ : syracuseStep 880811 = 1321217) B1321217
theorem B880823 : Blo 880569 880823 := bstep (se 1 (by rfl) ⟨660617, by rfl⟩ : syracuseStep 880823 = 1321235) B1321235
theorem B880843 : Blo 880569 880843 := bstep (se 1 (by rfl) ⟨660632, by rfl⟩ : syracuseStep 880843 = 1321265) B1321265
theorem B880855 : Blo 880569 880855 := bstep (se 1 (by rfl) ⟨660641, by rfl⟩ : syracuseStep 880855 = 1321283) B1321283
theorem B880875 : Blo 880569 880875 := bstep (se 1 (by rfl) ⟨660656, by rfl⟩ : syracuseStep 880875 = 1321313) B1321313
theorem B880887 : Blo 880569 880887 := bstep (se 1 (by rfl) ⟨660665, by rfl⟩ : syracuseStep 880887 = 1321331) B1321331
theorem B16937221 : Blo 880569 16937221 := bstep (se 4 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 16937221 = 3175729) B3175729
theorem B880907 : Blo 880569 880907 := bstep (se 1 (by rfl) ⟨660680, by rfl⟩ : syracuseStep 880907 = 1321361) B1321361
theorem B880919 : Blo 880569 880919 := bstep (se 1 (by rfl) ⟨660689, by rfl⟩ : syracuseStep 880919 = 1321379) B1321379
theorem B880939 : Blo 880569 880939 := bstep (se 1 (by rfl) ⟨660704, by rfl⟩ : syracuseStep 880939 = 1321409) B1321409
theorem B2978099 : Blo 880569 2978099 := bstep (se 1 (by rfl) ⟨2233574, by rfl⟩ : syracuseStep 2978099 = 4467149) B4467149
theorem B880951 : Blo 880569 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B880971 : Blo 880569 880971 := bstep (se 1 (by rfl) ⟨660728, by rfl⟩ : syracuseStep 880971 = 1321457) B1321457
theorem B880983 : Blo 880569 880983 := bstep (se 1 (by rfl) ⟨660737, by rfl⟩ : syracuseStep 880983 = 1321475) B1321475
theorem B881003 : Blo 880569 881003 := bstep (se 1 (by rfl) ⟨660752, by rfl⟩ : syracuseStep 881003 = 1321505) B1321505
theorem B881015 : Blo 880569 881015 := bstep (se 1 (by rfl) ⟨660761, by rfl⟩ : syracuseStep 881015 = 1321523) B1321523
theorem B881035 : Blo 880569 881035 := bstep (se 1 (by rfl) ⟨660776, by rfl⟩ : syracuseStep 881035 = 1321553) B1321553
theorem B881047 : Blo 880569 881047 := bstep (se 1 (by rfl) ⟨660785, by rfl⟩ : syracuseStep 881047 = 1321571) B1321571
theorem B4190615 : Blo 880569 4190615 := bstep (se 1 (by rfl) ⟨3142961, by rfl⟩ : syracuseStep 4190615 = 6285923) B6285923
theorem B881067 : Blo 880569 881067 := bstep (se 1 (by rfl) ⟨660800, by rfl⟩ : syracuseStep 881067 = 1321601) B1321601
theorem B881079 : Blo 880569 881079 := bstep (se 1 (by rfl) ⟨660809, by rfl⟩ : syracuseStep 881079 = 1321619) B1321619
theorem B881099 : Blo 880569 881099 := bstep (se 1 (by rfl) ⟨660824, by rfl⟩ : syracuseStep 881099 = 1321649) B1321649
theorem B881111 : Blo 880569 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B881131 : Blo 880569 881131 := bstep (se 1 (by rfl) ⟨660848, by rfl⟩ : syracuseStep 881131 = 1321697) B1321697
theorem B881143 : Blo 880569 881143 := bstep (se 1 (by rfl) ⟨660857, by rfl⟩ : syracuseStep 881143 = 1321715) B1321715
theorem B881163 : Blo 880569 881163 := bstep (se 1 (by rfl) ⟨660872, by rfl⟩ : syracuseStep 881163 = 1321745) B1321745
theorem B881175 : Blo 880569 881175 := bstep (se 1 (by rfl) ⟨660881, by rfl⟩ : syracuseStep 881175 = 1321763) B1321763
theorem B881195 : Blo 880569 881195 := bstep (se 1 (by rfl) ⟨660896, by rfl⟩ : syracuseStep 881195 = 1321793) B1321793
theorem B881207 : Blo 880569 881207 := bstep (se 1 (by rfl) ⟨660905, by rfl⟩ : syracuseStep 881207 = 1321811) B1321811
theorem B7533121 : Blo 880569 7533121 := bstep (se 2 (by rfl) ⟨2824920, by rfl⟩ : syracuseStep 7533121 = 5649841) B5649841
theorem B2978369 : Blo 880569 2978369 := bstep (se 2 (by rfl) ⟨1116888, by rfl⟩ : syracuseStep 2978369 = 2233777) B2233777
theorem B2388545 : Blo 880569 2388545 := bstep (se 2 (by rfl) ⟨895704, by rfl⟩ : syracuseStep 2388545 = 1791409) B1791409
theorem B881227 : Blo 880569 881227 := bstep (se 1 (by rfl) ⟨660920, by rfl⟩ : syracuseStep 881227 = 1321841) B1321841
theorem B881239 : Blo 880569 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B881259 : Blo 880569 881259 := bstep (se 1 (by rfl) ⟨660944, by rfl⟩ : syracuseStep 881259 = 1321889) B1321889
theorem B881271 : Blo 880569 881271 := bstep (se 1 (by rfl) ⟨660953, by rfl⟩ : syracuseStep 881271 = 1321907) B1321907
theorem B881291 : Blo 880569 881291 := bstep (se 1 (by rfl) ⟨660968, by rfl⟩ : syracuseStep 881291 = 1321937) B1321937
theorem B881303 : Blo 880569 881303 := bstep (se 1 (by rfl) ⟨660977, by rfl⟩ : syracuseStep 881303 = 1321955) B1321955
theorem B881323 : Blo 880569 881323 := bstep (se 1 (by rfl) ⟨660992, by rfl⟩ : syracuseStep 881323 = 1321985) B1321985
theorem B881335 : Blo 880569 881335 := bstep (se 1 (by rfl) ⟨661001, by rfl⟩ : syracuseStep 881335 = 1322003) B1322003
theorem B881355 : Blo 880569 881355 := bstep (se 1 (by rfl) ⟨661016, by rfl⟩ : syracuseStep 881355 = 1322033) B1322033
theorem B881367 : Blo 880569 881367 := bstep (se 1 (by rfl) ⟨661025, by rfl⟩ : syracuseStep 881367 = 1322051) B1322051
theorem B881387 : Blo 880569 881387 := bstep (se 1 (by rfl) ⟨661040, by rfl⟩ : syracuseStep 881387 = 1322081) B1322081
theorem B881399 : Blo 880569 881399 := bstep (se 1 (by rfl) ⟨661049, by rfl⟩ : syracuseStep 881399 = 1322099) B1322099
theorem B881419 : Blo 880569 881419 := bstep (se 1 (by rfl) ⟨661064, by rfl⟩ : syracuseStep 881419 = 1322129) B1322129
theorem B881431 : Blo 880569 881431 := bstep (se 1 (by rfl) ⟨661073, by rfl⟩ : syracuseStep 881431 = 1322147) B1322147
theorem B881451 : Blo 880569 881451 := bstep (se 1 (by rfl) ⟨661088, by rfl⟩ : syracuseStep 881451 = 1322177) B1322177
theorem B881463 : Blo 880569 881463 := bstep (se 1 (by rfl) ⟨661097, by rfl⟩ : syracuseStep 881463 = 1322195) B1322195
theorem B54424385 : Blo 880569 54424385 := bstep (se 2 (by rfl) ⟨20409144, by rfl⟩ : syracuseStep 54424385 = 40818289) B40818289
theorem B881483 : Blo 880569 881483 := bstep (se 1 (by rfl) ⟨661112, by rfl⟩ : syracuseStep 881483 = 1322225) B1322225
theorem B881495 : Blo 880569 881495 := bstep (se 1 (by rfl) ⟨661121, by rfl⟩ : syracuseStep 881495 = 1322243) B1322243
theorem B5370725 : Blo 880569 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B881515 : Blo 880569 881515 := bstep (se 1 (by rfl) ⟨661136, by rfl⟩ : syracuseStep 881515 = 1322273) B1322273
theorem B881527 : Blo 880569 881527 := bstep (se 1 (by rfl) ⟨661145, by rfl⟩ : syracuseStep 881527 = 1322291) B1322291
theorem B881547 : Blo 880569 881547 := bstep (se 1 (by rfl) ⟨661160, by rfl⟩ : syracuseStep 881547 = 1322321) B1322321
theorem B881559 : Blo 880569 881559 := bstep (se 1 (by rfl) ⟨661169, by rfl⟩ : syracuseStep 881559 = 1322339) B1322339
theorem B881579 : Blo 880569 881579 := bstep (se 1 (by rfl) ⟨661184, by rfl⟩ : syracuseStep 881579 = 1322369) B1322369
theorem B4027315 : Blo 880569 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B881591 : Blo 880569 881591 := bstep (se 1 (by rfl) ⟨661193, by rfl⟩ : syracuseStep 881591 = 1322387) B1322387
theorem B881611 : Blo 880569 881611 := bstep (se 1 (by rfl) ⟨661208, by rfl⟩ : syracuseStep 881611 = 1322417) B1322417
theorem B881623 : Blo 880569 881623 := bstep (se 1 (by rfl) ⟨661217, by rfl⟩ : syracuseStep 881623 = 1322435) B1322435
theorem B881643 : Blo 880569 881643 := bstep (se 1 (by rfl) ⟨661232, by rfl⟩ : syracuseStep 881643 = 1322465) B1322465
theorem B881655 : Blo 880569 881655 := bstep (se 1 (by rfl) ⟨661241, by rfl⟩ : syracuseStep 881655 = 1322483) B1322483
theorem B881675 : Blo 880569 881675 := bstep (se 1 (by rfl) ⟨661256, by rfl⟩ : syracuseStep 881675 = 1322513) B1322513
theorem B881687 : Blo 880569 881687 := bstep (se 1 (by rfl) ⟨661265, by rfl⟩ : syracuseStep 881687 = 1322531) B1322531
theorem B881707 : Blo 880569 881707 := bstep (se 1 (by rfl) ⟨661280, by rfl⟩ : syracuseStep 881707 = 1322561) B1322561
theorem B881719 : Blo 880569 881719 := bstep (se 1 (by rfl) ⟨661289, by rfl⟩ : syracuseStep 881719 = 1322579) B1322579
theorem B3175499 : Blo 880569 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B881739 : Blo 880569 881739 := bstep (se 1 (by rfl) ⟨661304, by rfl⟩ : syracuseStep 881739 = 1322609) B1322609
theorem B881751 : Blo 880569 881751 := bstep (se 1 (by rfl) ⟨661313, by rfl⟩ : syracuseStep 881751 = 1322627) B1322627
theorem B2978909 : Blo 880569 2978909 := bstep (se 3 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 2978909 = 1117091) B1117091
theorem B881771 : Blo 880569 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B881783 : Blo 880569 881783 := bstep (se 1 (by rfl) ⟨661337, by rfl⟩ : syracuseStep 881783 = 1322675) B1322675
theorem B881803 : Blo 880569 881803 := bstep (se 1 (by rfl) ⟨661352, by rfl⟩ : syracuseStep 881803 = 1322705) B1322705
theorem B881815 : Blo 880569 881815 := bstep (se 1 (by rfl) ⟨661361, by rfl⟩ : syracuseStep 881815 = 1322723) B1322723
theorem B881835 : Blo 880569 881835 := bstep (se 1 (by rfl) ⟨661376, by rfl⟩ : syracuseStep 881835 = 1322753) B1322753
theorem B881847 : Blo 880569 881847 := bstep (se 1 (by rfl) ⟨661385, by rfl⟩ : syracuseStep 881847 = 1322771) B1322771
theorem B881867 : Blo 880569 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B881879 : Blo 880569 881879 := bstep (se 1 (by rfl) ⟨661409, by rfl⟩ : syracuseStep 881879 = 1322819) B1322819
theorem B3175645 : Blo 880569 3175645 := bstep (se 3 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 3175645 = 1190867) B1190867
theorem B881899 : Blo 880569 881899 := bstep (se 1 (by rfl) ⟨661424, by rfl⟩ : syracuseStep 881899 = 1322849) B1322849
theorem B881911 : Blo 880569 881911 := bstep (se 1 (by rfl) ⟨661433, by rfl⟩ : syracuseStep 881911 = 1322867) B1322867
theorem B881931 : Blo 880569 881931 := bstep (se 1 (by rfl) ⟨661448, by rfl⟩ : syracuseStep 881931 = 1322897) B1322897
theorem B881943 : Blo 880569 881943 := bstep (se 1 (by rfl) ⟨661457, by rfl⟩ : syracuseStep 881943 = 1322915) B1322915
theorem B881963 : Blo 880569 881963 := bstep (se 1 (by rfl) ⟨661472, by rfl⟩ : syracuseStep 881963 = 1322945) B1322945
theorem B881975 : Blo 880569 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B881995 : Blo 880569 881995 := bstep (se 1 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 881995 = 1322993) B1322993
theorem B882007 : Blo 880569 882007 := bstep (se 1 (by rfl) ⟨661505, by rfl⟩ : syracuseStep 882007 = 1323011) B1323011
theorem B882027 : Blo 880569 882027 := bstep (se 1 (by rfl) ⟨661520, by rfl⟩ : syracuseStep 882027 = 1323041) B1323041
theorem B882039 : Blo 880569 882039 := bstep (se 1 (by rfl) ⟨661529, by rfl⟩ : syracuseStep 882039 = 1323059) B1323059
theorem B4846979 : Blo 880569 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B882059 : Blo 880569 882059 := bstep (se 1 (by rfl) ⟨661544, by rfl⟩ : syracuseStep 882059 = 1323089) B1323089
theorem B882071 : Blo 880569 882071 := bstep (se 1 (by rfl) ⟨661553, by rfl⟩ : syracuseStep 882071 = 1323107) B1323107
theorem B882091 : Blo 880569 882091 := bstep (se 1 (by rfl) ⟨661568, by rfl⟩ : syracuseStep 882091 = 1323137) B1323137
theorem B882103 : Blo 880569 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B882123 : Blo 880569 882123 := bstep (se 1 (by rfl) ⟨661592, by rfl⟩ : syracuseStep 882123 = 1323185) B1323185
theorem B882135 : Blo 880569 882135 := bstep (se 1 (by rfl) ⟨661601, by rfl⟩ : syracuseStep 882135 = 1323203) B1323203
theorem B882155 : Blo 880569 882155 := bstep (se 1 (by rfl) ⟨661616, by rfl⟩ : syracuseStep 882155 = 1323233) B1323233
theorem B882167 : Blo 880569 882167 := bstep (se 1 (by rfl) ⟨661625, by rfl⟩ : syracuseStep 882167 = 1323251) B1323251
theorem B882187 : Blo 880569 882187 := bstep (se 1 (by rfl) ⟨661640, by rfl⟩ : syracuseStep 882187 = 1323281) B1323281
theorem B882199 : Blo 880569 882199 := bstep (se 1 (by rfl) ⟨661649, by rfl⟩ : syracuseStep 882199 = 1323299) B1323299
theorem B882219 : Blo 880569 882219 := bstep (se 1 (by rfl) ⟨661664, by rfl⟩ : syracuseStep 882219 = 1323329) B1323329
theorem B882231 : Blo 880569 882231 := bstep (se 1 (by rfl) ⟨661673, by rfl⟩ : syracuseStep 882231 = 1323347) B1323347
theorem B882251 : Blo 880569 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B882263 : Blo 880569 882263 := bstep (se 1 (by rfl) ⟨661697, by rfl⟩ : syracuseStep 882263 = 1323395) B1323395
theorem B882283 : Blo 880569 882283 := bstep (se 1 (by rfl) ⟨661712, by rfl⟩ : syracuseStep 882283 = 1323425) B1323425
theorem B882295 : Blo 880569 882295 := bstep (se 1 (by rfl) ⟨661721, by rfl⟩ : syracuseStep 882295 = 1323443) B1323443
theorem B882315 : Blo 880569 882315 := bstep (se 1 (by rfl) ⟨661736, by rfl⟩ : syracuseStep 882315 = 1323473) B1323473
theorem B882327 : Blo 880569 882327 := bstep (se 1 (by rfl) ⟨661745, by rfl⟩ : syracuseStep 882327 = 1323491) B1323491
theorem B882347 : Blo 880569 882347 := bstep (se 1 (by rfl) ⟨661760, by rfl⟩ : syracuseStep 882347 = 1323521) B1323521
theorem B882359 : Blo 880569 882359 := bstep (se 1 (by rfl) ⟨661769, by rfl⟩ : syracuseStep 882359 = 1323539) B1323539
theorem B882379 : Blo 880569 882379 := bstep (se 1 (by rfl) ⟨661784, by rfl⟩ : syracuseStep 882379 = 1323569) B1323569
theorem B882391 : Blo 880569 882391 := bstep (se 1 (by rfl) ⟨661793, by rfl⟩ : syracuseStep 882391 = 1323587) B1323587
theorem B882411 : Blo 880569 882411 := bstep (se 1 (by rfl) ⟨661808, by rfl⟩ : syracuseStep 882411 = 1323617) B1323617
theorem B882423 : Blo 880569 882423 := bstep (se 1 (by rfl) ⟨661817, by rfl⟩ : syracuseStep 882423 = 1323635) B1323635
theorem B882443 : Blo 880569 882443 := bstep (se 1 (by rfl) ⟨661832, by rfl⟩ : syracuseStep 882443 = 1323665) B1323665
theorem B882455 : Blo 880569 882455 := bstep (se 1 (by rfl) ⟨661841, by rfl⟩ : syracuseStep 882455 = 1323683) B1323683
theorem B882475 : Blo 880569 882475 := bstep (se 1 (by rfl) ⟨661856, by rfl⟩ : syracuseStep 882475 = 1323713) B1323713
theorem B882487 : Blo 880569 882487 := bstep (se 1 (by rfl) ⟨661865, by rfl⟩ : syracuseStep 882487 = 1323731) B1323731
theorem B882507 : Blo 880569 882507 := bstep (se 1 (by rfl) ⟨661880, by rfl⟩ : syracuseStep 882507 = 1323761) B1323761
theorem B882519 : Blo 880569 882519 := bstep (se 1 (by rfl) ⟨661889, by rfl⟩ : syracuseStep 882519 = 1323779) B1323779
theorem B882539 : Blo 880569 882539 := bstep (se 1 (by rfl) ⟨661904, by rfl⟩ : syracuseStep 882539 = 1323809) B1323809
theorem B882551 : Blo 880569 882551 := bstep (se 1 (by rfl) ⟨661913, by rfl⟩ : syracuseStep 882551 = 1323827) B1323827
theorem B882571 : Blo 880569 882571 := bstep (se 1 (by rfl) ⟨661928, by rfl⟩ : syracuseStep 882571 = 1323857) B1323857
theorem B882583 : Blo 880569 882583 := bstep (se 1 (by rfl) ⟨661937, by rfl⟩ : syracuseStep 882583 = 1323875) B1323875
theorem B882603 : Blo 880569 882603 := bstep (se 1 (by rfl) ⟨661952, by rfl⟩ : syracuseStep 882603 = 1323905) B1323905
theorem B882615 : Blo 880569 882615 := bstep (se 1 (by rfl) ⟨661961, by rfl⟩ : syracuseStep 882615 = 1323923) B1323923
theorem B882635 : Blo 880569 882635 := bstep (se 1 (by rfl) ⟨661976, by rfl⟩ : syracuseStep 882635 = 1323953) B1323953
theorem B882647 : Blo 880569 882647 := bstep (se 1 (by rfl) ⟨661985, by rfl⟩ : syracuseStep 882647 = 1323971) B1323971
theorem B882667 : Blo 880569 882667 := bstep (se 1 (by rfl) ⟨662000, by rfl⟩ : syracuseStep 882667 = 1324001) B1324001
theorem B882679 : Blo 880569 882679 := bstep (se 1 (by rfl) ⟨662009, by rfl⟩ : syracuseStep 882679 = 1324019) B1324019
theorem B882699 : Blo 880569 882699 := bstep (se 1 (by rfl) ⟨662024, by rfl⟩ : syracuseStep 882699 = 1324049) B1324049
theorem B882711 : Blo 880569 882711 := bstep (se 1 (by rfl) ⟨662033, by rfl⟩ : syracuseStep 882711 = 1324067) B1324067
theorem B1210393 : Blo 880569 1210393 := bstep (se 2 (by rfl) ⟨453897, by rfl⟩ : syracuseStep 1210393 = 907795) B907795
theorem B882731 : Blo 880569 882731 := bstep (se 1 (by rfl) ⟨662048, by rfl⟩ : syracuseStep 882731 = 1324097) B1324097
theorem B882743 : Blo 880569 882743 := bstep (se 1 (by rfl) ⟨662057, by rfl⟩ : syracuseStep 882743 = 1324115) B1324115
theorem B882763 : Blo 880569 882763 := bstep (se 1 (by rfl) ⟨662072, by rfl⟩ : syracuseStep 882763 = 1324145) B1324145
theorem B882775 : Blo 880569 882775 := bstep (se 1 (by rfl) ⟨662081, by rfl⟩ : syracuseStep 882775 = 1324163) B1324163
theorem B882795 : Blo 880569 882795 := bstep (se 1 (by rfl) ⟨662096, by rfl⟩ : syracuseStep 882795 = 1324193) B1324193
theorem B882807 : Blo 880569 882807 := bstep (se 1 (by rfl) ⟨662105, by rfl⟩ : syracuseStep 882807 = 1324211) B1324211
theorem B882827 : Blo 880569 882827 := bstep (se 1 (by rfl) ⟨662120, by rfl⟩ : syracuseStep 882827 = 1324241) B1324241
theorem B882839 : Blo 880569 882839 := bstep (se 1 (by rfl) ⟨662129, by rfl⟩ : syracuseStep 882839 = 1324259) B1324259
theorem B882859 : Blo 880569 882859 := bstep (se 1 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 882859 = 1324289) B1324289
theorem B882871 : Blo 880569 882871 := bstep (se 1 (by rfl) ⟨662153, by rfl⟩ : syracuseStep 882871 = 1324307) B1324307
theorem B882891 : Blo 880569 882891 := bstep (se 1 (by rfl) ⟨662168, by rfl⟩ : syracuseStep 882891 = 1324337) B1324337
theorem B2980043 : Blo 880569 2980043 := bstep (se 1 (by rfl) ⟨2235032, by rfl⟩ : syracuseStep 2980043 = 4470065) B4470065
theorem B882903 : Blo 880569 882903 := bstep (se 1 (by rfl) ⟨662177, by rfl⟩ : syracuseStep 882903 = 1324355) B1324355
theorem B3766493 : Blo 880569 3766493 := bstep (se 3 (by rfl) ⟨706217, by rfl⟩ : syracuseStep 3766493 = 1412435) B1412435
theorem B882923 : Blo 880569 882923 := bstep (se 1 (by rfl) ⟨662192, by rfl⟩ : syracuseStep 882923 = 1324385) B1324385
theorem B882935 : Blo 880569 882935 := bstep (se 1 (by rfl) ⟨662201, by rfl⟩ : syracuseStep 882935 = 1324403) B1324403
theorem B1341707 : Blo 880569 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B882955 : Blo 880569 882955 := bstep (se 1 (by rfl) ⟨662216, by rfl⟩ : syracuseStep 882955 = 1324433) B1324433
theorem B882967 : Blo 880569 882967 := bstep (se 1 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 882967 = 1324451) B1324451
theorem B882987 : Blo 880569 882987 := bstep (se 1 (by rfl) ⟨662240, by rfl⟩ : syracuseStep 882987 = 1324481) B1324481
theorem B882999 : Blo 880569 882999 := bstep (se 1 (by rfl) ⟨662249, by rfl⟩ : syracuseStep 882999 = 1324499) B1324499
theorem B883019 : Blo 880569 883019 := bstep (se 1 (by rfl) ⟨662264, by rfl⟩ : syracuseStep 883019 = 1324529) B1324529
theorem B883031 : Blo 880569 883031 := bstep (se 1 (by rfl) ⟨662273, by rfl⟩ : syracuseStep 883031 = 1324547) B1324547
theorem B883051 : Blo 880569 883051 := bstep (se 1 (by rfl) ⟨662288, by rfl⟩ : syracuseStep 883051 = 1324577) B1324577
theorem B883063 : Blo 880569 883063 := bstep (se 1 (by rfl) ⟨662297, by rfl⟩ : syracuseStep 883063 = 1324595) B1324595
theorem B883083 : Blo 880569 883083 := bstep (se 1 (by rfl) ⟨662312, by rfl⟩ : syracuseStep 883083 = 1324625) B1324625
theorem B883095 : Blo 880569 883095 := bstep (se 1 (by rfl) ⟨662321, by rfl⟩ : syracuseStep 883095 = 1324643) B1324643
theorem B883115 : Blo 880569 883115 := bstep (se 1 (by rfl) ⟨662336, by rfl⟩ : syracuseStep 883115 = 1324673) B1324673
theorem B883127 : Blo 880569 883127 := bstep (se 1 (by rfl) ⟨662345, by rfl⟩ : syracuseStep 883127 = 1324691) B1324691
theorem B883147 : Blo 880569 883147 := bstep (se 1 (by rfl) ⟨662360, by rfl⟩ : syracuseStep 883147 = 1324721) B1324721
theorem B883159 : Blo 880569 883159 := bstep (se 1 (by rfl) ⟨662369, by rfl⟩ : syracuseStep 883159 = 1324739) B1324739
theorem B2980313 : Blo 880569 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B883179 : Blo 880569 883179 := bstep (se 1 (by rfl) ⟨662384, by rfl⟩ : syracuseStep 883179 = 1324769) B1324769
theorem B883191 : Blo 880569 883191 := bstep (se 1 (by rfl) ⟨662393, by rfl⟩ : syracuseStep 883191 = 1324787) B1324787
theorem B883211 : Blo 880569 883211 := bstep (se 1 (by rfl) ⟨662408, by rfl⟩ : syracuseStep 883211 = 1324817) B1324817
theorem B883223 : Blo 880569 883223 := bstep (se 1 (by rfl) ⟨662417, by rfl⟩ : syracuseStep 883223 = 1324835) B1324835
theorem B883243 : Blo 880569 883243 := bstep (se 1 (by rfl) ⟨662432, by rfl⟩ : syracuseStep 883243 = 1324865) B1324865
theorem B883255 : Blo 880569 883255 := bstep (se 1 (by rfl) ⟨662441, by rfl⟩ : syracuseStep 883255 = 1324883) B1324883
theorem B883275 : Blo 880569 883275 := bstep (se 1 (by rfl) ⟨662456, by rfl⟩ : syracuseStep 883275 = 1324913) B1324913
theorem B883287 : Blo 880569 883287 := bstep (se 1 (by rfl) ⟨662465, by rfl⟩ : syracuseStep 883287 = 1324931) B1324931
theorem B883307 : Blo 880569 883307 := bstep (se 1 (by rfl) ⟨662480, by rfl⟩ : syracuseStep 883307 = 1324961) B1324961
theorem B883319 : Blo 880569 883319 := bstep (se 1 (by rfl) ⟨662489, by rfl⟩ : syracuseStep 883319 = 1324979) B1324979
theorem B883339 : Blo 880569 883339 := bstep (se 1 (by rfl) ⟨662504, by rfl⟩ : syracuseStep 883339 = 1325009) B1325009
theorem B883351 : Blo 880569 883351 := bstep (se 1 (by rfl) ⟨662513, by rfl⟩ : syracuseStep 883351 = 1325027) B1325027
theorem B883371 : Blo 880569 883371 := bstep (se 1 (by rfl) ⟨662528, by rfl⟩ : syracuseStep 883371 = 1325057) B1325057
theorem B883383 : Blo 880569 883383 := bstep (se 1 (by rfl) ⟨662537, by rfl⟩ : syracuseStep 883383 = 1325075) B1325075
theorem B2259659 : Blo 880569 2259659 := bstep (se 1 (by rfl) ⟨1694744, by rfl⟩ : syracuseStep 2259659 = 3389489) B3389489
theorem B883403 : Blo 880569 883403 := bstep (se 1 (by rfl) ⟨662552, by rfl⟩ : syracuseStep 883403 = 1325105) B1325105
theorem B883415 : Blo 880569 883415 := bstep (se 1 (by rfl) ⟨662561, by rfl⟩ : syracuseStep 883415 = 1325123) B1325123
theorem B883435 : Blo 880569 883435 := bstep (se 1 (by rfl) ⟨662576, by rfl⟩ : syracuseStep 883435 = 1325153) B1325153
theorem B883447 : Blo 880569 883447 := bstep (se 1 (by rfl) ⟨662585, by rfl⟩ : syracuseStep 883447 = 1325171) B1325171
theorem B883467 : Blo 880569 883467 := bstep (se 1 (by rfl) ⟨662600, by rfl⟩ : syracuseStep 883467 = 1325201) B1325201
theorem B883479 : Blo 880569 883479 := bstep (se 1 (by rfl) ⟨662609, by rfl⟩ : syracuseStep 883479 = 1325219) B1325219
theorem B883499 : Blo 880569 883499 := bstep (se 1 (by rfl) ⟨662624, by rfl⟩ : syracuseStep 883499 = 1325249) B1325249
theorem B883511 : Blo 880569 883511 := bstep (se 1 (by rfl) ⟨662633, by rfl⟩ : syracuseStep 883511 = 1325267) B1325267
theorem B8584001 : Blo 880569 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B883531 : Blo 880569 883531 := bstep (se 1 (by rfl) ⟨662648, by rfl⟩ : syracuseStep 883531 = 1325297) B1325297
theorem B883543 : Blo 880569 883543 := bstep (se 1 (by rfl) ⟨662657, by rfl⟩ : syracuseStep 883543 = 1325315) B1325315
theorem B883563 : Blo 880569 883563 := bstep (se 1 (by rfl) ⟨662672, by rfl⟩ : syracuseStep 883563 = 1325345) B1325345
theorem B11598709 : Blo 880569 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B883575 : Blo 880569 883575 := bstep (se 1 (by rfl) ⟨662681, by rfl⟩ : syracuseStep 883575 = 1325363) B1325363
theorem B883595 : Blo 880569 883595 := bstep (se 1 (by rfl) ⟨662696, by rfl⟩ : syracuseStep 883595 = 1325393) B1325393
theorem B883607 : Blo 880569 883607 := bstep (se 1 (by rfl) ⟨662705, by rfl⟩ : syracuseStep 883607 = 1325411) B1325411
theorem B883627 : Blo 880569 883627 := bstep (se 1 (by rfl) ⟨662720, by rfl⟩ : syracuseStep 883627 = 1325441) B1325441
theorem B883639 : Blo 880569 883639 := bstep (se 1 (by rfl) ⟨662729, by rfl⟩ : syracuseStep 883639 = 1325459) B1325459
theorem B2685899 : Blo 880569 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B883659 : Blo 880569 883659 := bstep (se 1 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 883659 = 1325489) B1325489
theorem B883671 : Blo 880569 883671 := bstep (se 1 (by rfl) ⟨662753, by rfl⟩ : syracuseStep 883671 = 1325507) B1325507
theorem B883691 : Blo 880569 883691 := bstep (se 1 (by rfl) ⟨662768, by rfl⟩ : syracuseStep 883691 = 1325537) B1325537
theorem B883703 : Blo 880569 883703 := bstep (se 1 (by rfl) ⟨662777, by rfl⟩ : syracuseStep 883703 = 1325555) B1325555
theorem B883723 : Blo 880569 883723 := bstep (se 1 (by rfl) ⟨662792, by rfl⟩ : syracuseStep 883723 = 1325585) B1325585
theorem B883735 : Blo 880569 883735 := bstep (se 1 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 883735 = 1325603) B1325603
theorem B883755 : Blo 880569 883755 := bstep (se 1 (by rfl) ⟨662816, by rfl⟩ : syracuseStep 883755 = 1325633) B1325633
theorem B883767 : Blo 880569 883767 := bstep (se 1 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 883767 = 1325651) B1325651
theorem B1866817 : Blo 880569 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B883787 : Blo 880569 883787 := bstep (se 1 (by rfl) ⟨662840, by rfl⟩ : syracuseStep 883787 = 1325681) B1325681
theorem B883799 : Blo 880569 883799 := bstep (se 1 (by rfl) ⟨662849, by rfl⟩ : syracuseStep 883799 = 1325699) B1325699
theorem B883819 : Blo 880569 883819 := bstep (se 1 (by rfl) ⟨662864, by rfl⟩ : syracuseStep 883819 = 1325729) B1325729
theorem B883831 : Blo 880569 883831 := bstep (se 1 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 883831 = 1325747) B1325747
theorem B883851 : Blo 880569 883851 := bstep (se 1 (by rfl) ⟨662888, by rfl⟩ : syracuseStep 883851 = 1325777) B1325777
theorem B2981015 : Blo 880569 2981015 := bstep (se 1 (by rfl) ⟨2235761, by rfl⟩ : syracuseStep 2981015 = 4471523) B4471523
theorem B883863 : Blo 880569 883863 := bstep (se 1 (by rfl) ⟨662897, by rfl⟩ : syracuseStep 883863 = 1325795) B1325795
theorem B883883 : Blo 880569 883883 := bstep (se 1 (by rfl) ⟨662912, by rfl⟩ : syracuseStep 883883 = 1325825) B1325825
theorem B883895 : Blo 880569 883895 := bstep (se 1 (by rfl) ⟨662921, by rfl⟩ : syracuseStep 883895 = 1325843) B1325843
theorem B883915 : Blo 880569 883915 := bstep (se 1 (by rfl) ⟨662936, by rfl⟩ : syracuseStep 883915 = 1325873) B1325873
theorem B883927 : Blo 880569 883927 := bstep (se 1 (by rfl) ⟨662945, by rfl⟩ : syracuseStep 883927 = 1325891) B1325891
theorem B883947 : Blo 880569 883947 := bstep (se 1 (by rfl) ⟨662960, by rfl⟩ : syracuseStep 883947 = 1325921) B1325921
theorem B883959 : Blo 880569 883959 := bstep (se 1 (by rfl) ⟨662969, by rfl⟩ : syracuseStep 883959 = 1325939) B1325939
theorem B883979 : Blo 880569 883979 := bstep (se 1 (by rfl) ⟨662984, by rfl⟩ : syracuseStep 883979 = 1325969) B1325969
theorem B883991 : Blo 880569 883991 := bstep (se 1 (by rfl) ⟨662993, by rfl⟩ : syracuseStep 883991 = 1325987) B1325987
theorem B884011 : Blo 880569 884011 := bstep (se 1 (by rfl) ⟨663008, by rfl⟩ : syracuseStep 884011 = 1326017) B1326017
theorem B5373229 : Blo 880569 5373229 := bstep (se 3 (by rfl) ⟨1007480, by rfl⟩ : syracuseStep 5373229 = 2014961) B2014961
theorem B884023 : Blo 880569 884023 := bstep (se 1 (by rfl) ⟨663017, by rfl⟩ : syracuseStep 884023 = 1326035) B1326035
theorem B884043 : Blo 880569 884043 := bstep (se 1 (by rfl) ⟨663032, by rfl⟩ : syracuseStep 884043 = 1326065) B1326065
theorem B884055 : Blo 880569 884055 := bstep (se 1 (by rfl) ⟨663041, by rfl⟩ : syracuseStep 884055 = 1326083) B1326083
theorem B884075 : Blo 880569 884075 := bstep (se 1 (by rfl) ⟨663056, by rfl⟩ : syracuseStep 884075 = 1326113) B1326113
theorem B884087 : Blo 880569 884087 := bstep (se 1 (by rfl) ⟨663065, by rfl⟩ : syracuseStep 884087 = 1326131) B1326131
theorem B3571075 : Blo 880569 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B884107 : Blo 880569 884107 := bstep (se 1 (by rfl) ⟨663080, by rfl⟩ : syracuseStep 884107 = 1326161) B1326161
theorem B884119 : Blo 880569 884119 := bstep (se 1 (by rfl) ⟨663089, by rfl⟩ : syracuseStep 884119 = 1326179) B1326179
theorem B884139 : Blo 880569 884139 := bstep (se 1 (by rfl) ⟨663104, by rfl⟩ : syracuseStep 884139 = 1326209) B1326209
theorem B884151 : Blo 880569 884151 := bstep (se 1 (by rfl) ⟨663113, by rfl⟩ : syracuseStep 884151 = 1326227) B1326227
theorem B884171 : Blo 880569 884171 := bstep (se 1 (by rfl) ⟨663128, by rfl⟩ : syracuseStep 884171 = 1326257) B1326257
theorem B884183 : Blo 880569 884183 := bstep (se 1 (by rfl) ⟨663137, by rfl⟩ : syracuseStep 884183 = 1326275) B1326275
theorem B884203 : Blo 880569 884203 := bstep (se 1 (by rfl) ⟨663152, by rfl⟩ : syracuseStep 884203 = 1326305) B1326305
theorem B884215 : Blo 880569 884215 := bstep (se 1 (by rfl) ⟨663161, by rfl⟩ : syracuseStep 884215 = 1326323) B1326323
theorem B884235 : Blo 880569 884235 := bstep (se 1 (by rfl) ⟨663176, by rfl⟩ : syracuseStep 884235 = 1326353) B1326353
theorem B884247 : Blo 880569 884247 := bstep (se 1 (by rfl) ⟨663185, by rfl⟩ : syracuseStep 884247 = 1326371) B1326371
theorem B15072803 : Blo 880569 15072803 := bstep (se 1 (by rfl) ⟨11304602, by rfl⟩ : syracuseStep 15072803 = 22609205) B22609205
theorem B884267 : Blo 880569 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B884279 : Blo 880569 884279 := bstep (se 1 (by rfl) ⟨663209, by rfl⟩ : syracuseStep 884279 = 1326419) B1326419
theorem B2686529 : Blo 880569 2686529 := bstep (se 2 (by rfl) ⟨1007448, by rfl⟩ : syracuseStep 2686529 = 2014897) B2014897
theorem B884299 : Blo 880569 884299 := bstep (se 1 (by rfl) ⟨663224, by rfl⟩ : syracuseStep 884299 = 1326449) B1326449
theorem B884311 : Blo 880569 884311 := bstep (se 1 (by rfl) ⟨663233, by rfl⟩ : syracuseStep 884311 = 1326467) B1326467
theorem B884331 : Blo 880569 884331 := bstep (se 1 (by rfl) ⟨663248, by rfl⟩ : syracuseStep 884331 = 1326497) B1326497
theorem B884343 : Blo 880569 884343 := bstep (se 1 (by rfl) ⟨663257, by rfl⟩ : syracuseStep 884343 = 1326515) B1326515
theorem B8486531 : Blo 880569 8486531 := bstep (se 1 (by rfl) ⟨6364898, by rfl⟩ : syracuseStep 8486531 = 12729797) B12729797
theorem B884363 : Blo 880569 884363 := bstep (se 1 (by rfl) ⟨663272, by rfl⟩ : syracuseStep 884363 = 1326545) B1326545
theorem B884375 : Blo 880569 884375 := bstep (se 1 (by rfl) ⟨663281, by rfl⟩ : syracuseStep 884375 = 1326563) B1326563
theorem B884395 : Blo 880569 884395 := bstep (se 1 (by rfl) ⟨663296, by rfl⟩ : syracuseStep 884395 = 1326593) B1326593
theorem B2981555 : Blo 880569 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B884407 : Blo 880569 884407 := bstep (se 1 (by rfl) ⟨663305, by rfl⟩ : syracuseStep 884407 = 1326611) B1326611
theorem B884427 : Blo 880569 884427 := bstep (se 1 (by rfl) ⟨663320, by rfl⟩ : syracuseStep 884427 = 1326641) B1326641
theorem B884439 : Blo 880569 884439 := bstep (se 1 (by rfl) ⟨663329, by rfl⟩ : syracuseStep 884439 = 1326659) B1326659
theorem B884459 : Blo 880569 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B14286577 : Blo 880569 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B884471 : Blo 880569 884471 := bstep (se 1 (by rfl) ⟨663353, by rfl⟩ : syracuseStep 884471 = 1326707) B1326707
theorem B884491 : Blo 880569 884491 := bstep (se 1 (by rfl) ⟨663368, by rfl⟩ : syracuseStep 884491 = 1326737) B1326737
theorem B884503 : Blo 880569 884503 := bstep (se 1 (by rfl) ⟨663377, by rfl⟩ : syracuseStep 884503 = 1326755) B1326755
theorem B884523 : Blo 880569 884523 := bstep (se 1 (by rfl) ⟨663392, by rfl⟩ : syracuseStep 884523 = 1326785) B1326785
theorem B884535 : Blo 880569 884535 := bstep (se 1 (by rfl) ⟨663401, by rfl⟩ : syracuseStep 884535 = 1326803) B1326803
theorem B884555 : Blo 880569 884555 := bstep (se 1 (by rfl) ⟨663416, by rfl⟩ : syracuseStep 884555 = 1326833) B1326833
theorem B884567 : Blo 880569 884567 := bstep (se 1 (by rfl) ⟨663425, by rfl⟩ : syracuseStep 884567 = 1326851) B1326851
theorem B6029149 : Blo 880569 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B3178385 : Blo 880569 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B2981825 : Blo 880569 2981825 := bstep (se 2 (by rfl) ⟨1118184, by rfl⟩ : syracuseStep 2981825 = 2236369) B2236369
theorem B3768407 : Blo 880569 3768407 := bstep (se 1 (by rfl) ⟨2826305, by rfl⟩ : syracuseStep 3768407 = 5652611) B5652611
theorem B7143713 : Blo 880569 7143713 := bstep (se 2 (by rfl) ⟨2678892, by rfl⟩ : syracuseStep 7143713 = 5357785) B5357785
theorem B2982203 : Blo 880569 2982203 := bstep (se 1 (by rfl) ⟨2236652, by rfl⟩ : syracuseStep 2982203 = 4473305) B4473305
theorem B1114555 : Blo 880569 1114555 := bstep (se 1 (by rfl) ⟨835916, by rfl⟩ : syracuseStep 1114555 = 1671833) B1671833
theorem B29000213 : Blo 880569 29000213 := bstep (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) B1359385
theorem B2261591 : Blo 880569 2261591 := bstep (se 1 (by rfl) ⟨1696193, by rfl⟩ : syracuseStep 2261591 = 3392387) B3392387
theorem B2982689 : Blo 880569 2982689 := bstep (se 2 (by rfl) ⟨1118508, by rfl⟩ : syracuseStep 2982689 = 2237017) B2237017
theorem B2229079 : Blo 880569 2229079 := bstep (se 1 (by rfl) ⟨1671809, by rfl⟩ : syracuseStep 2229079 = 3343619) B3343619
theorem B1672235 : Blo 880569 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B2229383 : Blo 880569 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B2229515 : Blo 880569 2229515 := bstep (se 1 (by rfl) ⟨1672136, by rfl⟩ : syracuseStep 2229515 = 3344273) B3344273
theorem B1672463 : Blo 880569 1672463 := bstep (se 1 (by rfl) ⟨1254347, by rfl⟩ : syracuseStep 1672463 = 2508695) B2508695
theorem B2983283 : Blo 880569 2983283 := bstep (se 1 (by rfl) ⟨2237462, by rfl⟩ : syracuseStep 2983283 = 4474925) B4474925
theorem B1115527 : Blo 880569 1115527 := bstep (se 1 (by rfl) ⟨836645, by rfl⟩ : syracuseStep 1115527 = 1673291) B1673291
theorem B2753939 : Blo 880569 2753939 := bstep (se 1 (by rfl) ⟨2065454, by rfl⟩ : syracuseStep 2753939 = 4130909) B4130909
theorem B2688403 : Blo 880569 2688403 := bstep (se 1 (by rfl) ⟨2016302, by rfl⟩ : syracuseStep 2688403 = 4032605) B4032605
theorem B3343801 : Blo 880569 3343801 := bstep (se 2 (by rfl) ⟨1253925, by rfl⟩ : syracuseStep 3343801 = 2507851) B2507851
theorem B4523543 : Blo 880569 4523543 := bstep (se 1 (by rfl) ⟨3392657, by rfl⟩ : syracuseStep 4523543 = 6785315) B6785315
theorem B2230031 : Blo 880569 2230031 := bstep (se 1 (by rfl) ⟨1672523, by rfl⟩ : syracuseStep 2230031 = 3345047) B3345047
theorem B1115947 : Blo 880569 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B10061657 : Blo 880569 10061657 := bstep (se 2 (by rfl) ⟨3773121, by rfl⟩ : syracuseStep 10061657 = 7546243) B7546243
theorem B2230163 : Blo 880569 2230163 := bstep (se 1 (by rfl) ⟨1672622, by rfl⟩ : syracuseStep 2230163 = 3345245) B3345245
theorem B1116175 : Blo 880569 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B4458563 : Blo 880569 4458563 := bstep (se 1 (by rfl) ⟨3343922, by rfl⟩ : syracuseStep 4458563 = 6687845) B6687845
theorem B4458887 : Blo 880569 4458887 := bstep (se 1 (by rfl) ⟨3344165, by rfl⟩ : syracuseStep 4458887 = 6688331) B6688331
theorem B3770833 : Blo 880569 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B2689595 : Blo 880569 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B1673875 : Blo 880569 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B1411769 : Blo 880569 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B1116919 : Blo 880569 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B1674103 : Blo 880569 1674103 := bstep (se 1 (by rfl) ⟨1255577, by rfl⟩ : syracuseStep 1674103 = 2511155) B2511155
theorem B2231297 : Blo 880569 2231297 := bstep (se 2 (by rfl) ⟨836736, by rfl⟩ : syracuseStep 2231297 = 1673473) B1673473
theorem B1117243 : Blo 880569 1117243 := bstep (se 1 (by rfl) ⟨837932, by rfl⟩ : syracuseStep 1117243 = 1675865) B1675865
theorem B2821321 : Blo 880569 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B2231671 : Blo 880569 2231671 := bstep (se 1 (by rfl) ⟨1673753, by rfl⟩ : syracuseStep 2231671 = 3347507) B3347507
theorem B1117739 : Blo 880569 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B1412743 : Blo 880569 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B2232107 : Blo 880569 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B4526009 : Blo 880569 4526009 := bstep (se 2 (by rfl) ⟨1697253, by rfl⟩ : syracuseStep 4526009 = 3394507) B3394507
theorem B1118215 : Blo 880569 1118215 := bstep (se 1 (by rfl) ⟨838661, by rfl⟩ : syracuseStep 1118215 = 1677323) B1677323
theorem B3346703 : Blo 880569 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B5017889 : Blo 880569 5017889 := bstep (se 2 (by rfl) ⟨1881708, by rfl⟩ : syracuseStep 5017889 = 3763417) B3763417
theorem B108532061 : Blo 880569 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B1675667 : Blo 880569 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B1675721 : Blo 880569 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B25498097 : Blo 880569 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B1118711 : Blo 880569 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B2036267 : Blo 880569 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B1675819 : Blo 880569 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B2232947 : Blo 880569 2232947 := bstep (se 1 (by rfl) ⟨1674710, by rfl⟩ : syracuseStep 2232947 = 3349421) B3349421
theorem B2232967 : Blo 880569 2232967 := bstep (se 1 (by rfl) ⟨1674725, by rfl⟩ : syracuseStep 2232967 = 3349451) B3349451
theorem B1118863 : Blo 880569 1118863 := bstep (se 1 (by rfl) ⟨839147, by rfl⟩ : syracuseStep 1118863 = 1678295) B1678295
theorem B1676047 : Blo 880569 1676047 := bstep (se 1 (by rfl) ⟨1257035, by rfl⟩ : syracuseStep 1676047 = 2514071) B2514071
theorem B1413947 : Blo 880569 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B3773243 : Blo 880569 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B1119035 : Blo 880569 1119035 := bstep (se 1 (by rfl) ⟨839276, by rfl⟩ : syracuseStep 1119035 = 1678553) B1678553
theorem B2233241 : Blo 880569 2233241 := bstep (se 2 (by rfl) ⟨837465, by rfl⟩ : syracuseStep 2233241 = 1674931) B1674931
theorem B4232195 : Blo 880569 4232195 := bstep (se 1 (by rfl) ⟨3174146, by rfl⟩ : syracuseStep 4232195 = 6348293) B6348293
theorem B2233403 : Blo 880569 2233403 := bstep (se 1 (by rfl) ⟨1675052, by rfl⟩ : syracuseStep 2233403 = 3350105) B3350105
theorem B2233615 : Blo 880569 2233615 := bstep (se 1 (by rfl) ⟨1675211, by rfl⟩ : syracuseStep 2233615 = 3350423) B3350423
theorem B2725255 : Blo 880569 2725255 := bstep (se 1 (by rfl) ⟨2043941, by rfl⟩ : syracuseStep 2725255 = 4087883) B4087883
theorem B2233889 : Blo 880569 2233889 := bstep (se 2 (by rfl) ⟨837708, by rfl⟩ : syracuseStep 2233889 = 1675417) B1675417
theorem B22582961 : Blo 880569 22582961 := bstep (se 2 (by rfl) ⟨8468610, by rfl⟩ : syracuseStep 22582961 = 16937221) B16937221
theorem B4462451 : Blo 880569 4462451 := bstep (se 1 (by rfl) ⟨3346838, by rfl⟩ : syracuseStep 4462451 = 6693677) B6693677
theorem B9050285 : Blo 880569 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B1677611 : Blo 880569 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B4462937 : Blo 880569 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B85694861 : Blo 880569 85694861 := bstep (se 3 (by rfl) ⟨16067786, by rfl⟩ : syracuseStep 85694861 = 32135573) B32135573
theorem B2234891 : Blo 880569 2234891 := bstep (se 1 (by rfl) ⟨1676168, by rfl⟩ : syracuseStep 2234891 = 3352337) B3352337
theorem B10033955 : Blo 880569 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B4234193 : Blo 880569 4234193 := bstep (se 2 (by rfl) ⟨1587822, by rfl⟩ : syracuseStep 4234193 = 3175645) B3175645
theorem B3578923 : Blo 880569 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B2235539 : Blo 880569 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B5020987 : Blo 880569 5020987 := bstep (se 1 (by rfl) ⟨3765740, by rfl⟩ : syracuseStep 5020987 = 7531481) B7531481
theorem B3349907 : Blo 880569 3349907 := bstep (se 1 (by rfl) ⟨2512430, by rfl⟩ : syracuseStep 3349907 = 5024861) B5024861
theorem B2235833 : Blo 880569 2235833 := bstep (se 2 (by rfl) ⟨838437, by rfl⟩ : syracuseStep 2235833 = 1676875) B1676875
theorem B5086723 : Blo 880569 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B2825999 : Blo 880569 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B991111 : Blo 880569 991111 := bstep (se 1 (by rfl) ⟨743333, by rfl⟩ : syracuseStep 991111 = 1486667) B1486667
theorem B1613857 : Blo 880569 1613857 := bstep (se 2 (by rfl) ⟨605196, by rfl⟩ : syracuseStep 1613857 = 1210393) B1210393
theorem B991291 : Blo 880569 991291 := bstep (se 1 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 991291 = 1486937) B1486937
theorem B2236531 : Blo 880569 2236531 := bstep (se 1 (by rfl) ⟨1677398, by rfl⟩ : syracuseStep 2236531 = 3354797) B3354797
theorem B2236673 : Blo 880569 2236673 := bstep (se 2 (by rfl) ⟨838752, by rfl⟩ : syracuseStep 2236673 = 1677505) B1677505
theorem B2793743 : Blo 880569 2793743 := bstep (se 1 (by rfl) ⟨2095307, by rfl⟩ : syracuseStep 2793743 = 4190615) B4190615
theorem B4465043 : Blo 880569 4465043 := bstep (se 1 (by rfl) ⟨3348782, by rfl⟩ : syracuseStep 4465043 = 6697565) B6697565
theorem B991759 : Blo 880569 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B36282923 : Blo 880569 36282923 := bstep (se 1 (by rfl) ⟨27212192, by rfl⟩ : syracuseStep 36282923 = 54424385) B54424385
theorem B3580483 : Blo 880569 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B2237129 : Blo 880569 2237129 := bstep (se 2 (by rfl) ⟨838923, by rfl⟩ : syracuseStep 2237129 = 1677847) B1677847
theorem B5022445 : Blo 880569 5022445 := bstep (se 3 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 5022445 = 1883417) B1883417
theorem B38740913 : Blo 880569 38740913 := bstep (se 2 (by rfl) ⟨14527842, by rfl⟩ : syracuseStep 38740913 = 29055685) B29055685
theorem B992263 : Blo 880569 992263 := bstep (se 1 (by rfl) ⟨744197, by rfl⟩ : syracuseStep 992263 = 1488395) B1488395
theorem B3351563 : Blo 880569 3351563 := bstep (se 1 (by rfl) ⟨2513672, by rfl⟩ : syracuseStep 3351563 = 5027345) B5027345
theorem B2237483 : Blo 880569 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B992443 : Blo 880569 992443 := bstep (se 1 (by rfl) ⟨744332, by rfl⟩ : syracuseStep 992443 = 1488665) B1488665
theorem B3024263 : Blo 880569 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B992911 : Blo 880569 992911 := bstep (se 1 (by rfl) ⟨744683, by rfl⟩ : syracuseStep 992911 = 1489367) B1489367
theorem B4761433 : Blo 880569 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B1320875 : Blo 880569 1320875 := bstep (se 1 (by rfl) ⟨990656, by rfl⟩ : syracuseStep 1320875 = 1981313) B1981313
theorem B1320905 : Blo 880569 1320905 := bstep (se 2 (by rfl) ⟨495339, by rfl⟩ : syracuseStep 1320905 = 990679) B990679
theorem B2238475 : Blo 880569 2238475 := bstep (se 1 (by rfl) ⟨1678856, by rfl⟩ : syracuseStep 2238475 = 3357713) B3357713
theorem B1321019 : Blo 880569 1321019 := bstep (se 1 (by rfl) ⟨990764, by rfl⟩ : syracuseStep 1321019 = 1981529) B1981529
theorem B1321079 : Blo 880569 1321079 := bstep (se 1 (by rfl) ⟨990809, by rfl⟩ : syracuseStep 1321079 = 1981619) B1981619
theorem B993415 : Blo 880569 993415 := bstep (se 1 (by rfl) ⟨745061, by rfl⟩ : syracuseStep 993415 = 1490123) B1490123
theorem B1321103 : Blo 880569 1321103 := bstep (se 1 (by rfl) ⟨990827, by rfl⟩ : syracuseStep 1321103 = 1981655) B1981655
theorem B2238617 : Blo 880569 2238617 := bstep (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) B1678963
theorem B1321145 : Blo 880569 1321145 := bstep (se 2 (by rfl) ⟨495429, by rfl⟩ : syracuseStep 1321145 = 990859) B990859
theorem B1321223 : Blo 880569 1321223 := bstep (se 1 (by rfl) ⟨990917, by rfl⟩ : syracuseStep 1321223 = 1981835) B1981835
theorem B1321259 : Blo 880569 1321259 := bstep (se 1 (by rfl) ⟨990944, by rfl⟩ : syracuseStep 1321259 = 1981889) B1981889
theorem B993595 : Blo 880569 993595 := bstep (se 1 (by rfl) ⟨745196, by rfl⟩ : syracuseStep 993595 = 1490393) B1490393
theorem B2238779 : Blo 880569 2238779 := bstep (se 1 (by rfl) ⟨1679084, by rfl⟩ : syracuseStep 2238779 = 3358169) B3358169
theorem B19048769 : Blo 880569 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B1321289 : Blo 880569 1321289 := bstep (se 2 (by rfl) ⟨495483, by rfl⟩ : syracuseStep 1321289 = 990967) B990967
theorem B1321403 : Blo 880569 1321403 := bstep (se 1 (by rfl) ⟨991052, by rfl⟩ : syracuseStep 1321403 = 1982105) B1982105
theorem B8038865 : Blo 880569 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B1321463 : Blo 880569 1321463 := bstep (se 1 (by rfl) ⟨991097, by rfl⟩ : syracuseStep 1321463 = 1982195) B1982195
theorem B6040067 : Blo 880569 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B1321487 : Blo 880569 1321487 := bstep (se 1 (by rfl) ⟨991115, by rfl⟩ : syracuseStep 1321487 = 1982231) B1982231
theorem B1321529 : Blo 880569 1321529 := bstep (se 2 (by rfl) ⟨495573, by rfl⟩ : syracuseStep 1321529 = 991147) B991147
theorem B1321607 : Blo 880569 1321607 := bstep (se 1 (by rfl) ⟨991205, by rfl⟩ : syracuseStep 1321607 = 1982411) B1982411
theorem B1321643 : Blo 880569 1321643 := bstep (se 1 (by rfl) ⟨991232, by rfl⟩ : syracuseStep 1321643 = 1982465) B1982465
theorem B1059499 : Blo 880569 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B5024429 : Blo 880569 5024429 := bstep (se 3 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 5024429 = 1884161) B1884161
theorem B1321673 : Blo 880569 1321673 := bstep (se 2 (by rfl) ⟨495627, by rfl⟩ : syracuseStep 1321673 = 991255) B991255
theorem B994063 : Blo 880569 994063 := bstep (se 1 (by rfl) ⟨745547, by rfl⟩ : syracuseStep 994063 = 1491095) B1491095
theorem B9186085 : Blo 880569 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1321787 : Blo 880569 1321787 := bstep (se 1 (by rfl) ⟨991340, by rfl⟩ : syracuseStep 1321787 = 1982681) B1982681
theorem B1321847 : Blo 880569 1321847 := bstep (se 1 (by rfl) ⟨991385, by rfl⟩ : syracuseStep 1321847 = 1982771) B1982771
theorem B1321871 : Blo 880569 1321871 := bstep (se 1 (by rfl) ⟨991403, by rfl⟩ : syracuseStep 1321871 = 1982807) B1982807
theorem B11447203 : Blo 880569 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1321913 : Blo 880569 1321913 := bstep (se 2 (by rfl) ⟨495717, by rfl⟩ : syracuseStep 1321913 = 991435) B991435
theorem B1321991 : Blo 880569 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B1322027 : Blo 880569 1322027 := bstep (se 1 (by rfl) ⟨991520, by rfl⟩ : syracuseStep 1322027 = 1983041) B1983041
theorem B1322057 : Blo 880569 1322057 := bstep (se 2 (by rfl) ⟨495771, by rfl⟩ : syracuseStep 1322057 = 991543) B991543
theorem B1256591 : Blo 880569 1256591 := bstep (se 1 (by rfl) ⟨942443, by rfl⟩ : syracuseStep 1256591 = 1884887) B1884887
theorem B1322171 : Blo 880569 1322171 := bstep (se 1 (by rfl) ⟨991628, by rfl⟩ : syracuseStep 1322171 = 1983257) B1983257
theorem B1322231 : Blo 880569 1322231 := bstep (se 1 (by rfl) ⟨991673, by rfl⟩ : syracuseStep 1322231 = 1983347) B1983347
theorem B994567 : Blo 880569 994567 := bstep (se 1 (by rfl) ⟨745925, by rfl⟩ : syracuseStep 994567 = 1491851) B1491851
theorem B1322255 : Blo 880569 1322255 := bstep (se 1 (by rfl) ⟨991691, by rfl⟩ : syracuseStep 1322255 = 1983383) B1983383
theorem B1322297 : Blo 880569 1322297 := bstep (se 2 (by rfl) ⟨495861, by rfl⟩ : syracuseStep 1322297 = 991723) B991723
theorem B1322375 : Blo 880569 1322375 := bstep (se 1 (by rfl) ⟨991781, by rfl⟩ : syracuseStep 1322375 = 1983563) B1983563
theorem B4468121 : Blo 880569 4468121 := bstep (se 2 (by rfl) ⟨1675545, by rfl⟩ : syracuseStep 4468121 = 3351091) B3351091
theorem B1322411 : Blo 880569 1322411 := bstep (se 1 (by rfl) ⟨991808, by rfl⟩ : syracuseStep 1322411 = 1983617) B1983617
theorem B994747 : Blo 880569 994747 := bstep (se 1 (by rfl) ⟨746060, by rfl⟩ : syracuseStep 994747 = 1492121) B1492121
theorem B1322441 : Blo 880569 1322441 := bstep (se 2 (by rfl) ⟨495915, by rfl⟩ : syracuseStep 1322441 = 991831) B991831
theorem B3583531 : Blo 880569 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B1322555 : Blo 880569 1322555 := bstep (se 1 (by rfl) ⟨991916, by rfl⟩ : syracuseStep 1322555 = 1983833) B1983833
theorem B1322615 : Blo 880569 1322615 := bstep (se 1 (by rfl) ⟨991961, by rfl⟩ : syracuseStep 1322615 = 1983923) B1983923
theorem B1486471 : Blo 880569 1486471 := bstep (se 1 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 1486471 = 2229707) B2229707
theorem B1322639 : Blo 880569 1322639 := bstep (se 1 (by rfl) ⟨991979, by rfl⟩ : syracuseStep 1322639 = 1983959) B1983959
theorem B2010809 : Blo 880569 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1322681 : Blo 880569 1322681 := bstep (se 2 (by rfl) ⟨496005, by rfl⟩ : syracuseStep 1322681 = 992011) B992011
theorem B1322759 : Blo 880569 1322759 := bstep (se 1 (by rfl) ⟨992069, by rfl⟩ : syracuseStep 1322759 = 1984139) B1984139
theorem B3583759 : Blo 880569 3583759 := bstep (se 1 (by rfl) ⟨2687819, by rfl⟩ : syracuseStep 3583759 = 5375639) B5375639
theorem B1322795 : Blo 880569 1322795 := bstep (se 1 (by rfl) ⟨992096, by rfl⟩ : syracuseStep 1322795 = 1984193) B1984193
theorem B1322825 : Blo 880569 1322825 := bstep (se 2 (by rfl) ⟨496059, by rfl⟩ : syracuseStep 1322825 = 992119) B992119
theorem B1322939 : Blo 880569 1322939 := bstep (se 1 (by rfl) ⟨992204, by rfl⟩ : syracuseStep 1322939 = 1984409) B1984409
theorem B1322999 : Blo 880569 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B1323023 : Blo 880569 1323023 := bstep (se 1 (by rfl) ⟨992267, by rfl⟩ : syracuseStep 1323023 = 1984535) B1984535
theorem B1323065 : Blo 880569 1323065 := bstep (se 2 (by rfl) ⟨496149, by rfl⟩ : syracuseStep 1323065 = 992299) B992299
theorem B1323143 : Blo 880569 1323143 := bstep (se 1 (by rfl) ⟨992357, by rfl⟩ : syracuseStep 1323143 = 1984715) B1984715
theorem B1323179 : Blo 880569 1323179 := bstep (se 1 (by rfl) ⟨992384, by rfl⟩ : syracuseStep 1323179 = 1984769) B1984769
theorem B1323209 : Blo 880569 1323209 := bstep (se 2 (by rfl) ⟨496203, by rfl⟩ : syracuseStep 1323209 = 992407) B992407
theorem B1487119 : Blo 880569 1487119 := bstep (se 1 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 1487119 = 2230679) B2230679
theorem B7156001 : Blo 880569 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B1323323 : Blo 880569 1323323 := bstep (se 1 (by rfl) ⟨992492, by rfl⟩ : syracuseStep 1323323 = 1984985) B1984985
theorem B1323383 : Blo 880569 1323383 := bstep (se 1 (by rfl) ⟨992537, by rfl⟩ : syracuseStep 1323383 = 1985075) B1985075
theorem B1323407 : Blo 880569 1323407 := bstep (se 1 (by rfl) ⟨992555, by rfl⟩ : syracuseStep 1323407 = 1985111) B1985111
theorem B1323449 : Blo 880569 1323449 := bstep (se 2 (by rfl) ⟨496293, by rfl⟩ : syracuseStep 1323449 = 992587) B992587
theorem B1323527 : Blo 880569 1323527 := bstep (se 1 (by rfl) ⟨992645, by rfl⟩ : syracuseStep 1323527 = 1985291) B1985291
theorem B4764203 : Blo 880569 4764203 := bstep (se 1 (by rfl) ⟨3573152, by rfl⟩ : syracuseStep 4764203 = 7146305) B7146305
theorem B1323563 : Blo 880569 1323563 := bstep (se 1 (by rfl) ⟨992672, by rfl⟩ : syracuseStep 1323563 = 1985345) B1985345
theorem B1323593 : Blo 880569 1323593 := bstep (se 2 (by rfl) ⟨496347, by rfl⟩ : syracuseStep 1323593 = 992695) B992695
theorem B1323707 : Blo 880569 1323707 := bstep (se 1 (by rfl) ⟨992780, by rfl⟩ : syracuseStep 1323707 = 1985561) B1985561
theorem B1323767 : Blo 880569 1323767 := bstep (se 1 (by rfl) ⟨992825, by rfl⟩ : syracuseStep 1323767 = 1985651) B1985651
theorem B1323791 : Blo 880569 1323791 := bstep (se 1 (by rfl) ⟨992843, by rfl⟩ : syracuseStep 1323791 = 1985687) B1985687
theorem B1487659 : Blo 880569 1487659 := bstep (se 1 (by rfl) ⟨1115744, by rfl⟩ : syracuseStep 1487659 = 2231489) B2231489
theorem B5649203 : Blo 880569 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B1323833 : Blo 880569 1323833 := bstep (se 2 (by rfl) ⟨496437, by rfl⟩ : syracuseStep 1323833 = 992875) B992875
theorem B3355451 : Blo 880569 3355451 := bstep (se 1 (by rfl) ⟨2516588, by rfl⟩ : syracuseStep 3355451 = 5033177) B5033177
theorem B1323911 : Blo 880569 1323911 := bstep (se 1 (by rfl) ⟨992933, by rfl⟩ : syracuseStep 1323911 = 1985867) B1985867
theorem B1323947 : Blo 880569 1323947 := bstep (se 1 (by rfl) ⟨992960, by rfl⟩ : syracuseStep 1323947 = 1985921) B1985921
theorem B1487801 : Blo 880569 1487801 := bstep (se 2 (by rfl) ⟨557925, by rfl⟩ : syracuseStep 1487801 = 1115851) B1115851
theorem B1323977 : Blo 880569 1323977 := bstep (se 2 (by rfl) ⟨496491, by rfl⟩ : syracuseStep 1323977 = 992983) B992983
theorem B5026819 : Blo 880569 5026819 := bstep (se 1 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 5026819 = 7540229) B7540229
theorem B1324091 : Blo 880569 1324091 := bstep (se 1 (by rfl) ⟨993068, by rfl⟩ : syracuseStep 1324091 = 1986137) B1986137
theorem B1324151 : Blo 880569 1324151 := bstep (se 1 (by rfl) ⟨993113, by rfl⟩ : syracuseStep 1324151 = 1986227) B1986227
theorem B1815671 : Blo 880569 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B1324175 : Blo 880569 1324175 := bstep (se 1 (by rfl) ⟨993131, by rfl⟩ : syracuseStep 1324175 = 1986263) B1986263
theorem B1324217 : Blo 880569 1324217 := bstep (se 2 (by rfl) ⟨496581, by rfl⟩ : syracuseStep 1324217 = 993163) B993163
theorem B4535489 : Blo 880569 4535489 := bstep (se 2 (by rfl) ⟨1700808, by rfl⟩ : syracuseStep 4535489 = 3401617) B3401617
theorem B1324295 : Blo 880569 1324295 := bstep (se 1 (by rfl) ⟨993221, by rfl⟩ : syracuseStep 1324295 = 1986443) B1986443
theorem B3355937 : Blo 880569 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B1324331 : Blo 880569 1324331 := bstep (se 1 (by rfl) ⟨993248, by rfl⟩ : syracuseStep 1324331 = 1986497) B1986497
theorem B1324361 : Blo 880569 1324361 := bstep (se 2 (by rfl) ⟨496635, by rfl⟩ : syracuseStep 1324361 = 993271) B993271
theorem B1324475 : Blo 880569 1324475 := bstep (se 1 (by rfl) ⟨993356, by rfl⟩ : syracuseStep 1324475 = 1986713) B1986713
theorem B1324535 : Blo 880569 1324535 := bstep (se 1 (by rfl) ⟨993401, by rfl⟩ : syracuseStep 1324535 = 1986803) B1986803
theorem B1324559 : Blo 880569 1324559 := bstep (se 1 (by rfl) ⟨993419, by rfl⟩ : syracuseStep 1324559 = 1986839) B1986839
theorem B1324601 : Blo 880569 1324601 := bstep (se 2 (by rfl) ⟨496725, by rfl⟩ : syracuseStep 1324601 = 993451) B993451
theorem B6108739 : Blo 880569 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B1488503 : Blo 880569 1488503 := bstep (se 1 (by rfl) ⟨1116377, by rfl⟩ : syracuseStep 1488503 = 2232755) B2232755
theorem B1324679 : Blo 880569 1324679 := bstep (se 1 (by rfl) ⟨993509, by rfl⟩ : syracuseStep 1324679 = 1987019) B1987019
theorem B1324715 : Blo 880569 1324715 := bstep (se 1 (by rfl) ⟨993536, by rfl⟩ : syracuseStep 1324715 = 1987073) B1987073
theorem B1062571 : Blo 880569 1062571 := bstep (se 1 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 1062571 = 1593857) B1593857
theorem B1324745 : Blo 880569 1324745 := bstep (se 2 (by rfl) ⟨496779, by rfl⟩ : syracuseStep 1324745 = 993559) B993559
theorem B1324859 : Blo 880569 1324859 := bstep (se 1 (by rfl) ⟨993644, by rfl⟩ : syracuseStep 1324859 = 1987289) B1987289
theorem B4241267 : Blo 880569 4241267 := bstep (se 1 (by rfl) ⟨3180950, by rfl⟩ : syracuseStep 4241267 = 6361901) B6361901
theorem B1324919 : Blo 880569 1324919 := bstep (se 1 (by rfl) ⟨993689, by rfl⟩ : syracuseStep 1324919 = 1987379) B1987379
theorem B1324943 : Blo 880569 1324943 := bstep (se 1 (by rfl) ⟨993707, by rfl⟩ : syracuseStep 1324943 = 1987415) B1987415
theorem B4470713 : Blo 880569 4470713 := bstep (se 2 (by rfl) ⟨1676517, by rfl⟩ : syracuseStep 4470713 = 3353035) B3353035
theorem B1324985 : Blo 880569 1324985 := bstep (se 2 (by rfl) ⟨496869, by rfl⟩ : syracuseStep 1324985 = 993739) B993739
theorem B1325063 : Blo 880569 1325063 := bstep (se 1 (by rfl) ⟨993797, by rfl⟩ : syracuseStep 1325063 = 1987595) B1987595
theorem B1325099 : Blo 880569 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B1488955 : Blo 880569 1488955 := bstep (se 1 (by rfl) ⟨1116716, by rfl⟩ : syracuseStep 1488955 = 2233433) B2233433
theorem B1554491 : Blo 880569 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B1325129 : Blo 880569 1325129 := bstep (se 2 (by rfl) ⟨496923, by rfl⟩ : syracuseStep 1325129 = 993847) B993847
theorem B1587347 : Blo 880569 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B1325243 : Blo 880569 1325243 := bstep (se 1 (by rfl) ⟨993932, by rfl⟩ : syracuseStep 1325243 = 1987865) B1987865
theorem B1489097 : Blo 880569 1489097 := bstep (se 2 (by rfl) ⟨558411, by rfl⟩ : syracuseStep 1489097 = 1116823) B1116823
theorem B3356909 : Blo 880569 3356909 := bstep (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) B1258841
theorem B1325303 : Blo 880569 1325303 := bstep (se 1 (by rfl) ⟨993977, by rfl⟩ : syracuseStep 1325303 = 1987955) B1987955
theorem B1325327 : Blo 880569 1325327 := bstep (se 1 (by rfl) ⟨993995, by rfl⟩ : syracuseStep 1325327 = 1987991) B1987991
theorem B1325369 : Blo 880569 1325369 := bstep (se 2 (by rfl) ⟨497013, by rfl⟩ : syracuseStep 1325369 = 994027) B994027
theorem B12925277 : Blo 880569 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B1325447 : Blo 880569 1325447 := bstep (se 1 (by rfl) ⟨994085, by rfl⟩ : syracuseStep 1325447 = 1988171) B1988171
theorem B1325483 : Blo 880569 1325483 := bstep (se 1 (by rfl) ⟨994112, by rfl⟩ : syracuseStep 1325483 = 1988225) B1988225
theorem B1325513 : Blo 880569 1325513 := bstep (se 2 (by rfl) ⟨497067, by rfl⟩ : syracuseStep 1325513 = 994135) B994135
theorem B3357227 : Blo 880569 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B1325627 : Blo 880569 1325627 := bstep (se 1 (by rfl) ⟨994220, by rfl⟩ : syracuseStep 1325627 = 1988441) B1988441
theorem B1325687 : Blo 880569 1325687 := bstep (se 1 (by rfl) ⟨994265, by rfl⟩ : syracuseStep 1325687 = 1988531) B1988531
theorem B1325711 : Blo 880569 1325711 := bstep (se 1 (by rfl) ⟨994283, by rfl⟩ : syracuseStep 1325711 = 1988567) B1988567
theorem B1325753 : Blo 880569 1325753 := bstep (se 2 (by rfl) ⟨497157, by rfl⟩ : syracuseStep 1325753 = 994315) B994315
theorem B1194683 : Blo 880569 1194683 := bstep (se 1 (by rfl) ⟨896012, by rfl⟩ : syracuseStep 1194683 = 1792025) B1792025
theorem B1194743 : Blo 880569 1194743 := bstep (se 1 (by rfl) ⟨896057, by rfl⟩ : syracuseStep 1194743 = 1792115) B1792115
theorem B1325831 : Blo 880569 1325831 := bstep (se 1 (by rfl) ⟨994373, by rfl⟩ : syracuseStep 1325831 = 1988747) B1988747
theorem B1325867 : Blo 880569 1325867 := bstep (se 1 (by rfl) ⟨994400, by rfl⟩ : syracuseStep 1325867 = 1988801) B1988801
theorem B1882939 : Blo 880569 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B1325897 : Blo 880569 1325897 := bstep (se 2 (by rfl) ⟨497211, by rfl⟩ : syracuseStep 1325897 = 994423) B994423
theorem B1489799 : Blo 880569 1489799 := bstep (se 1 (by rfl) ⟨1117349, by rfl⟩ : syracuseStep 1489799 = 2234699) B2234699
theorem B2014087 : Blo 880569 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B1981331 : Blo 880569 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B1326011 : Blo 880569 1326011 := bstep (se 1 (by rfl) ⟨994508, by rfl⟩ : syracuseStep 1326011 = 1989017) B1989017
theorem B1981385 : Blo 880569 1981385 := bstep (se 2 (by rfl) ⟨743019, by rfl⟩ : syracuseStep 1981385 = 1486039) B1486039
theorem B1588169 : Blo 880569 1588169 := bstep (se 2 (by rfl) ⟨595563, by rfl⟩ : syracuseStep 1588169 = 1191127) B1191127
theorem B1326071 : Blo 880569 1326071 := bstep (se 1 (by rfl) ⟨994553, by rfl⟩ : syracuseStep 1326071 = 1989107) B1989107
theorem B1326095 : Blo 880569 1326095 := bstep (se 1 (by rfl) ⟨994571, by rfl⟩ : syracuseStep 1326095 = 1989143) B1989143
theorem B1326137 : Blo 880569 1326137 := bstep (se 2 (by rfl) ⟨497301, by rfl⟩ : syracuseStep 1326137 = 994603) B994603
theorem B1326215 : Blo 880569 1326215 := bstep (se 1 (by rfl) ⟨994661, by rfl⟩ : syracuseStep 1326215 = 1989323) B1989323
theorem B1326251 : Blo 880569 1326251 := bstep (se 1 (by rfl) ⟨994688, by rfl⟩ : syracuseStep 1326251 = 1989377) B1989377
theorem B4472009 : Blo 880569 4472009 := bstep (se 2 (by rfl) ⟨1677003, by rfl⟩ : syracuseStep 4472009 = 3354007) B3354007
theorem B1326281 : Blo 880569 1326281 := bstep (se 2 (by rfl) ⟨497355, by rfl⟩ : syracuseStep 1326281 = 994711) B994711
theorem B4242689 : Blo 880569 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B1326395 : Blo 880569 1326395 := bstep (se 1 (by rfl) ⟨994796, by rfl⟩ : syracuseStep 1326395 = 1989593) B1989593
theorem B5029235 : Blo 880569 5029235 := bstep (se 1 (by rfl) ⟨3771926, by rfl⟩ : syracuseStep 5029235 = 7543853) B7543853
theorem B1326455 : Blo 880569 1326455 := bstep (se 1 (by rfl) ⟨994841, by rfl⟩ : syracuseStep 1326455 = 1989683) B1989683
theorem B1326479 : Blo 880569 1326479 := bstep (se 1 (by rfl) ⟨994859, by rfl⟩ : syracuseStep 1326479 = 1989719) B1989719
theorem B1326521 : Blo 880569 1326521 := bstep (se 2 (by rfl) ⟨497445, by rfl⟩ : syracuseStep 1326521 = 994891) B994891
theorem B1326599 : Blo 880569 1326599 := bstep (se 1 (by rfl) ⟨994949, by rfl⟩ : syracuseStep 1326599 = 1989899) B1989899
theorem B1490447 : Blo 880569 1490447 := bstep (se 1 (by rfl) ⟨1117835, by rfl⟩ : syracuseStep 1490447 = 2235671) B2235671
theorem B1326635 : Blo 880569 1326635 := bstep (se 1 (by rfl) ⟨994976, by rfl⟩ : syracuseStep 1326635 = 1989953) B1989953
theorem B1326665 : Blo 880569 1326665 := bstep (se 2 (by rfl) ⟨497499, by rfl⟩ : syracuseStep 1326665 = 994999) B994999
theorem B1982087 : Blo 880569 1982087 := bstep (se 1 (by rfl) ⟨1486565, by rfl⟩ : syracuseStep 1982087 = 2973131) B2973131
theorem B1326779 : Blo 880569 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B1326839 : Blo 880569 1326839 := bstep (se 1 (by rfl) ⟨995129, by rfl⟩ : syracuseStep 1326839 = 1990259) B1990259
theorem B1982267 : Blo 880569 1982267 := bstep (se 1 (by rfl) ⟨1486700, by rfl⟩ : syracuseStep 1982267 = 2973401) B2973401
theorem B1982393 : Blo 880569 1982393 := bstep (se 2 (by rfl) ⟨743397, by rfl⟩ : syracuseStep 1982393 = 1486795) B1486795
theorem B5160971 : Blo 880569 5160971 := bstep (se 1 (by rfl) ⟨3870728, by rfl⟩ : syracuseStep 5160971 = 7741457) B7741457
theorem B1490987 : Blo 880569 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B24461513 : Blo 880569 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B1982735 : Blo 880569 1982735 := bstep (se 1 (by rfl) ⟨1487051, by rfl⟩ : syracuseStep 1982735 = 2974103) B2974103
theorem B1982753 : Blo 880569 1982753 := bstep (se 2 (by rfl) ⟨743532, by rfl⟩ : syracuseStep 1982753 = 1487065) B1487065
theorem B8470919 : Blo 880569 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B1491385 : Blo 880569 1491385 := bstep (se 2 (by rfl) ⟨559269, by rfl⟩ : syracuseStep 1491385 = 1118539) B1118539
theorem B1983095 : Blo 880569 1983095 := bstep (se 1 (by rfl) ⟨1487321, by rfl⟩ : syracuseStep 1983095 = 2974643) B2974643
theorem B10044161 : Blo 880569 10044161 := bstep (se 2 (by rfl) ⟨3766560, by rfl⟩ : syracuseStep 10044161 = 7533121) B7533121
theorem B5030693 : Blo 880569 5030693 := bstep (se 4 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 5030693 = 943255) B943255
theorem B1983275 : Blo 880569 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B6701939 : Blo 880569 6701939 := bstep (se 1 (by rfl) ⟨5026454, by rfl⟩ : syracuseStep 6701939 = 10052909) B10052909
theorem B1492087 : Blo 880569 1492087 := bstep (se 1 (by rfl) ⟨1119065, by rfl⟩ : syracuseStep 1492087 = 2238131) B2238131
theorem B1787015 : Blo 880569 1787015 := bstep (se 1 (by rfl) ⟨1340261, by rfl⟩ : syracuseStep 1787015 = 2680523) B2680523
theorem B1983635 : Blo 880569 1983635 := bstep (se 1 (by rfl) ⟨1487726, by rfl⟩ : syracuseStep 1983635 = 2975453) B2975453
theorem B1885331 : Blo 880569 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1983689 : Blo 880569 1983689 := bstep (se 2 (by rfl) ⟨743883, by rfl⟩ : syracuseStep 1983689 = 1487767) B1487767
theorem B1492283 : Blo 880569 1492283 := bstep (se 1 (by rfl) ⟨1119212, by rfl⟩ : syracuseStep 1492283 = 2238425) B2238425
theorem B4244957 : Blo 880569 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B5031467 : Blo 880569 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B1492681 : Blo 880569 1492681 := bstep (se 2 (by rfl) ⟨559755, by rfl⟩ : syracuseStep 1492681 = 1119511) B1119511
theorem B2180951 : Blo 880569 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B1984391 : Blo 880569 1984391 := bstep (se 1 (by rfl) ⟨1488293, by rfl⟩ : syracuseStep 1984391 = 2976587) B2976587
theorem B4245533 : Blo 880569 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B1984571 : Blo 880569 1984571 := bstep (se 1 (by rfl) ⟨1488428, by rfl⟩ : syracuseStep 1984571 = 2976857) B2976857
theorem B2115769 : Blo 880569 2115769 := bstep (se 2 (by rfl) ⟨793413, by rfl⟩ : syracuseStep 2115769 = 1586827) B1586827
theorem B1984697 : Blo 880569 1984697 := bstep (se 2 (by rfl) ⟨744261, by rfl⟩ : syracuseStep 1984697 = 1488523) B1488523
theorem B1985039 : Blo 880569 1985039 := bstep (se 1 (by rfl) ⟨1488779, by rfl⟩ : syracuseStep 1985039 = 2977559) B2977559
theorem B1985057 : Blo 880569 1985057 := bstep (se 2 (by rfl) ⟨744396, by rfl⟩ : syracuseStep 1985057 = 1488793) B1488793
theorem B2509355 : Blo 880569 2509355 := bstep (se 1 (by rfl) ⟨1882016, by rfl⟩ : syracuseStep 2509355 = 3764033) B3764033
theorem B14305835 : Blo 880569 14305835 := bstep (se 1 (by rfl) ⟨10729376, by rfl⟩ : syracuseStep 14305835 = 21458753) B21458753
theorem B16108075 : Blo 880569 16108075 := bstep (se 1 (by rfl) ⟨12081056, by rfl⟩ : syracuseStep 16108075 = 24162113) B24162113
theorem B2116385 : Blo 880569 2116385 := bstep (se 2 (by rfl) ⟨793644, by rfl⟩ : syracuseStep 2116385 = 1587289) B1587289
theorem B7654193 : Blo 880569 7654193 := bstep (se 2 (by rfl) ⟨2870322, by rfl⟩ : syracuseStep 7654193 = 5740645) B5740645
theorem B1985399 : Blo 880569 1985399 := bstep (se 1 (by rfl) ⟨1489049, by rfl⟩ : syracuseStep 1985399 = 2978099) B2978099
theorem B5032925 : Blo 880569 5032925 := bstep (se 3 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 5032925 = 1887347) B1887347
theorem B1985579 : Blo 880569 1985579 := bstep (se 1 (by rfl) ⟨1489184, by rfl⟩ : syracuseStep 1985579 = 2978369) B2978369
theorem B1592363 : Blo 880569 1592363 := bstep (se 1 (by rfl) ⟨1194272, by rfl⟩ : syracuseStep 1592363 = 2388545) B2388545
theorem B2116999 : Blo 880569 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B1985939 : Blo 880569 1985939 := bstep (se 1 (by rfl) ⟨1489454, by rfl⟩ : syracuseStep 1985939 = 2978909) B2978909
theorem B1985993 : Blo 880569 1985993 := bstep (se 2 (by rfl) ⟨744747, by rfl⟩ : syracuseStep 1985993 = 1489495) B1489495
theorem B10047077 : Blo 880569 10047077 := bstep (se 4 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 10047077 = 1883827) B1883827
theorem B15257393 : Blo 880569 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B1888201 : Blo 880569 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1986695 : Blo 880569 1986695 := bstep (se 1 (by rfl) ⟨1490021, by rfl⟩ : syracuseStep 1986695 = 2980043) B2980043
theorem B2510995 : Blo 880569 2510995 := bstep (se 1 (by rfl) ⟨1883246, by rfl⟩ : syracuseStep 2510995 = 3766493) B3766493
theorem B1986875 : Blo 880569 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B7164305 : Blo 880569 7164305 := bstep (se 2 (by rfl) ⟨2686614, by rfl⟩ : syracuseStep 7164305 = 5373229) B5373229
theorem B1987001 : Blo 880569 1987001 := bstep (se 2 (by rfl) ⟨745125, by rfl⟩ : syracuseStep 1987001 = 1490251) B1490251
theorem B1888697 : Blo 880569 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B3396107 : Blo 880569 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B5722667 : Blo 880569 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B1790599 : Blo 880569 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B4084481 : Blo 880569 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1987343 : Blo 880569 1987343 := bstep (se 1 (by rfl) ⟨1490507, by rfl⟩ : syracuseStep 1987343 = 2981015) B2981015
theorem B1987361 : Blo 880569 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B4477841 : Blo 880569 4477841 := bstep (se 2 (by rfl) ⟨1679190, by rfl⟩ : syracuseStep 4477841 = 3358381) B3358381
theorem B10048535 : Blo 880569 10048535 := bstep (se 1 (by rfl) ⟨7536401, by rfl⟩ : syracuseStep 10048535 = 15072803) B15072803
theorem B1791019 : Blo 880569 1791019 := bstep (se 1 (by rfl) ⟨1343264, by rfl⟩ : syracuseStep 1791019 = 2686529) B2686529
theorem B5657687 : Blo 880569 5657687 := bstep (se 1 (by rfl) ⟨4243265, by rfl⟩ : syracuseStep 5657687 = 8486531) B8486531
theorem B1987703 : Blo 880569 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B2118923 : Blo 880569 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B1987883 : Blo 880569 1987883 := bstep (se 1 (by rfl) ⟨1490912, by rfl⟩ : syracuseStep 1987883 = 2981825) B2981825
theorem B4773437 : Blo 880569 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B1988243 : Blo 880569 1988243 := bstep (se 1 (by rfl) ⟨1491182, by rfl⟩ : syracuseStep 1988243 = 2982365) B2982365
theorem B16307891 : Blo 880569 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B1988297 : Blo 880569 1988297 := bstep (se 2 (by rfl) ⟨745611, by rfl⟩ : syracuseStep 1988297 = 1491223) B1491223
theorem B2512727 : Blo 880569 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B2119691 : Blo 880569 2119691 := bstep (se 1 (by rfl) ⟨1589768, by rfl⟩ : syracuseStep 2119691 = 3179537) B3179537
theorem B5036093 : Blo 880569 5036093 := bstep (se 3 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 5036093 = 1888535) B1888535
theorem B907399 : Blo 880569 907399 := bstep (se 1 (by rfl) ⟨680549, by rfl⟩ : syracuseStep 907399 = 1361099) B1361099
theorem B4249837 : Blo 880569 4249837 := bstep (se 3 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 4249837 = 1593689) B1593689
theorem B16963829 : Blo 880569 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B1988999 : Blo 880569 1988999 := bstep (se 1 (by rfl) ⟨1491749, by rfl⟩ : syracuseStep 1988999 = 2983499) B2983499
theorem B4249991 : Blo 880569 4249991 := bstep (se 1 (by rfl) ⟨3187493, by rfl⟩ : syracuseStep 4249991 = 6374987) B6374987
theorem B2972051 : Blo 880569 2972051 := bstep (se 1 (by rfl) ⟨2229038, by rfl⟩ : syracuseStep 2972051 = 4458077) B4458077
theorem B1989179 : Blo 880569 1989179 := bstep (se 1 (by rfl) ⟨1491884, by rfl⟩ : syracuseStep 1989179 = 2983769) B2983769
theorem B1989305 : Blo 880569 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B940987 : Blo 880569 940987 := bstep (se 1 (by rfl) ⟨705740, by rfl⟩ : syracuseStep 940987 = 1411481) B1411481
theorem B1989647 : Blo 880569 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B1989665 : Blo 880569 1989665 := bstep (se 2 (by rfl) ⟨746124, by rfl⟩ : syracuseStep 1989665 = 1492249) B1492249
theorem B2546873 : Blo 880569 2546873 := bstep (se 2 (by rfl) ⟨955077, by rfl⟩ : syracuseStep 2546873 = 1910155) B1910155
theorem B1990007 : Blo 880569 1990007 := bstep (se 1 (by rfl) ⟨1492505, by rfl⟩ : syracuseStep 1990007 = 2985011) B2985011
theorem B2514311 : Blo 880569 2514311 := bstep (se 1 (by rfl) ⟨1885733, by rfl⟩ : syracuseStep 2514311 = 3771467) B3771467
theorem B2121113 : Blo 880569 2121113 := bstep (se 2 (by rfl) ⟨795417, by rfl⟩ : syracuseStep 2121113 = 1590835) B1590835
theorem B1990187 : Blo 880569 1990187 := bstep (se 1 (by rfl) ⟨1492640, by rfl⟩ : syracuseStep 1990187 = 2985281) B2985281
theorem B9690841 : Blo 880569 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B2973455 : Blo 880569 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B2514959 : Blo 880569 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B2973725 : Blo 880569 2973725 := bstep (se 3 (by rfl) ⟨557573, by rfl⟩ : syracuseStep 2973725 = 1115147) B1115147
theorem B14311541 : Blo 880569 14311541 := bstep (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) B1341707
theorem B9560753 : Blo 880569 9560753 := bstep (se 2 (by rfl) ⟨3585282, by rfl⟩ : syracuseStep 9560753 = 7170565) B7170565
theorem B1073935 : Blo 880569 1073935 := bstep (se 1 (by rfl) ⟨805451, by rfl⟩ : syracuseStep 1073935 = 1610903) B1610903
theorem B2122681 : Blo 880569 2122681 := bstep (se 2 (by rfl) ⟨796005, by rfl⟩ : syracuseStep 2122681 = 1592011) B1592011
theorem B2384911 : Blo 880569 2384911 := bstep (se 1 (by rfl) ⟨1788683, by rfl⟩ : syracuseStep 2384911 = 3577367) B3577367
theorem B2975129 : Blo 880569 2975129 := bstep (se 2 (by rfl) ⟨1115673, by rfl⟩ : syracuseStep 2975129 = 2231347) B2231347
theorem B2123297 : Blo 880569 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B45868619 : Blo 880569 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B2516599 : Blo 880569 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B943759 : Blo 880569 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B3762035 : Blo 880569 3762035 := bstep (se 1 (by rfl) ⟨2821526, by rfl⟩ : syracuseStep 3762035 = 5643053) B5643053
theorem B2975831 : Blo 880569 2975831 := bstep (se 1 (by rfl) ⟨2231873, by rfl⟩ : syracuseStep 2975831 = 4463747) B4463747
theorem B2123911 : Blo 880569 2123911 := bstep (se 1 (by rfl) ⟨1592933, by rfl⟩ : syracuseStep 2123911 = 3185867) B3185867
theorem B4778299 : Blo 880569 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B1206775 : Blo 880569 1206775 := bstep (se 1 (by rfl) ⟨905081, by rfl⟩ : syracuseStep 1206775 = 1810163) B1810163
theorem B2976317 : Blo 880569 2976317 := bstep (se 3 (by rfl) ⟨558059, by rfl⟩ : syracuseStep 2976317 = 1116119) B1116119
theorem B2517875 : Blo 880569 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B9956357 : Blo 880569 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B10742807 : Blo 880569 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B2518103 : Blo 880569 2518103 := bstep (se 1 (by rfl) ⟨1888577, by rfl⟩ : syracuseStep 2518103 = 3777155) B3777155
theorem B12906161 : Blo 880569 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B6352613 : Blo 880569 6352613 := bstep (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) B1191115
theorem B5369753 : Blo 880569 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B7171993 : Blo 880569 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B2977721 : Blo 880569 2977721 := bstep (se 2 (by rfl) ⟨1116645, by rfl⟩ : syracuseStep 2977721 = 2233291) B2233291
theorem B2387897 : Blo 880569 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B880571 : Blo 880569 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B6352843 : Blo 880569 6352843 := bstep (se 1 (by rfl) ⟨4764632, by rfl⟩ : syracuseStep 6352843 = 9529265) B9529265
theorem B880647 : Blo 880569 880647 := bstep (se 1 (by rfl) ⟨660485, by rfl⟩ : syracuseStep 880647 = 1320971) B1320971
theorem B880655 : Blo 880569 880655 := bstep (se 1 (by rfl) ⟨660491, by rfl⟩ : syracuseStep 880655 = 1320983) B1320983
theorem B880699 : Blo 880569 880699 := bstep (se 1 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 880699 = 1321049) B1321049
theorem B12087413 : Blo 880569 12087413 := bstep (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) B1133195
theorem B880775 : Blo 880569 880775 := bstep (se 1 (by rfl) ⟨660581, by rfl⟩ : syracuseStep 880775 = 1321163) B1321163
theorem B880783 : Blo 880569 880783 := bstep (se 1 (by rfl) ⟨660587, by rfl⟩ : syracuseStep 880783 = 1321175) B1321175
theorem B880827 : Blo 880569 880827 := bstep (se 1 (by rfl) ⟨660620, by rfl⟩ : syracuseStep 880827 = 1321241) B1321241
theorem B880903 : Blo 880569 880903 := bstep (se 1 (by rfl) ⟨660677, by rfl⟩ : syracuseStep 880903 = 1321355) B1321355
theorem B880911 : Blo 880569 880911 := bstep (se 1 (by rfl) ⟨660683, by rfl⟩ : syracuseStep 880911 = 1321367) B1321367
theorem B3764495 : Blo 880569 3764495 := bstep (se 1 (by rfl) ⟨2823371, by rfl⟩ : syracuseStep 3764495 = 5646743) B5646743
theorem B880955 : Blo 880569 880955 := bstep (se 1 (by rfl) ⟨660716, by rfl⟩ : syracuseStep 880955 = 1321433) B1321433
theorem B881031 : Blo 880569 881031 := bstep (se 1 (by rfl) ⟨660773, by rfl⟩ : syracuseStep 881031 = 1321547) B1321547
theorem B881039 : Blo 880569 881039 := bstep (se 1 (by rfl) ⟨660779, by rfl⟩ : syracuseStep 881039 = 1321559) B1321559
theorem B2388371 : Blo 880569 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B881083 : Blo 880569 881083 := bstep (se 1 (by rfl) ⟨660812, by rfl⟩ : syracuseStep 881083 = 1321625) B1321625
theorem B881159 : Blo 880569 881159 := bstep (se 1 (by rfl) ⟨660869, by rfl⟩ : syracuseStep 881159 = 1321739) B1321739
theorem B2978315 : Blo 880569 2978315 := bstep (se 1 (by rfl) ⟨2233736, by rfl⟩ : syracuseStep 2978315 = 4467473) B4467473
theorem B881167 : Blo 880569 881167 := bstep (se 1 (by rfl) ⟨660875, by rfl⟩ : syracuseStep 881167 = 1321751) B1321751
theorem B881211 : Blo 880569 881211 := bstep (se 1 (by rfl) ⟨660908, by rfl⟩ : syracuseStep 881211 = 1321817) B1321817
theorem B2978423 : Blo 880569 2978423 := bstep (se 1 (by rfl) ⟨2233817, by rfl⟩ : syracuseStep 2978423 = 4467635) B4467635
theorem B881287 : Blo 880569 881287 := bstep (se 1 (by rfl) ⟨660965, by rfl⟩ : syracuseStep 881287 = 1321931) B1321931
theorem B881295 : Blo 880569 881295 := bstep (se 1 (by rfl) ⟨660971, by rfl⟩ : syracuseStep 881295 = 1321943) B1321943
theorem B881339 : Blo 880569 881339 := bstep (se 1 (by rfl) ⟨661004, by rfl⟩ : syracuseStep 881339 = 1322009) B1322009
theorem B881415 : Blo 880569 881415 := bstep (se 1 (by rfl) ⟨661061, by rfl⟩ : syracuseStep 881415 = 1322123) B1322123
theorem B881423 : Blo 880569 881423 := bstep (se 1 (by rfl) ⟨661067, by rfl⟩ : syracuseStep 881423 = 1322135) B1322135
theorem B881467 : Blo 880569 881467 := bstep (se 1 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 881467 = 1322201) B1322201
theorem B12743513 : Blo 880569 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B881543 : Blo 880569 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B881551 : Blo 880569 881551 := bstep (se 1 (by rfl) ⟨661163, by rfl⟩ : syracuseStep 881551 = 1322327) B1322327
theorem B1340345 : Blo 880569 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B881595 : Blo 880569 881595 := bstep (se 1 (by rfl) ⟨661196, by rfl⟩ : syracuseStep 881595 = 1322393) B1322393
theorem B881671 : Blo 880569 881671 := bstep (se 1 (by rfl) ⟨661253, by rfl⟩ : syracuseStep 881671 = 1322507) B1322507
theorem B881679 : Blo 880569 881679 := bstep (se 1 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 881679 = 1322519) B1322519
theorem B881723 : Blo 880569 881723 := bstep (se 1 (by rfl) ⟨661292, by rfl⟩ : syracuseStep 881723 = 1322585) B1322585
theorem B881799 : Blo 880569 881799 := bstep (se 1 (by rfl) ⟨661349, by rfl⟩ : syracuseStep 881799 = 1322699) B1322699
theorem B881807 : Blo 880569 881807 := bstep (se 1 (by rfl) ⟨661355, by rfl⟩ : syracuseStep 881807 = 1322711) B1322711
theorem B881851 : Blo 880569 881851 := bstep (se 1 (by rfl) ⟨661388, by rfl⟩ : syracuseStep 881851 = 1322777) B1322777
theorem B2979017 : Blo 880569 2979017 := bstep (se 2 (by rfl) ⟨1117131, by rfl⟩ : syracuseStep 2979017 = 2234263) B2234263
theorem B881927 : Blo 880569 881927 := bstep (se 1 (by rfl) ⟨661445, by rfl⟩ : syracuseStep 881927 = 1322891) B1322891
theorem B881935 : Blo 880569 881935 := bstep (se 1 (by rfl) ⟨661451, by rfl⟩ : syracuseStep 881935 = 1322903) B1322903
theorem B881979 : Blo 880569 881979 := bstep (se 1 (by rfl) ⟨661484, by rfl⟩ : syracuseStep 881979 = 1322969) B1322969
theorem B1701179 : Blo 880569 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B882055 : Blo 880569 882055 := bstep (se 1 (by rfl) ⟨661541, by rfl⟩ : syracuseStep 882055 = 1323083) B1323083
theorem B882063 : Blo 880569 882063 := bstep (se 1 (by rfl) ⟨661547, by rfl⟩ : syracuseStep 882063 = 1323095) B1323095
theorem B882107 : Blo 880569 882107 := bstep (se 1 (by rfl) ⟨661580, by rfl⟩ : syracuseStep 882107 = 1323161) B1323161
theorem B882183 : Blo 880569 882183 := bstep (se 1 (by rfl) ⟨661637, by rfl⟩ : syracuseStep 882183 = 1323275) B1323275
theorem B882191 : Blo 880569 882191 := bstep (se 1 (by rfl) ⟨661643, by rfl⟩ : syracuseStep 882191 = 1323287) B1323287
theorem B882235 : Blo 880569 882235 := bstep (se 1 (by rfl) ⟨661676, by rfl⟩ : syracuseStep 882235 = 1323353) B1323353
theorem B10057283 : Blo 880569 10057283 := bstep (se 1 (by rfl) ⟨7542962, by rfl⟩ : syracuseStep 10057283 = 15085925) B15085925
theorem B882311 : Blo 880569 882311 := bstep (se 1 (by rfl) ⟨661733, by rfl⟩ : syracuseStep 882311 = 1323467) B1323467
theorem B882319 : Blo 880569 882319 := bstep (se 1 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 882319 = 1323479) B1323479
theorem B882363 : Blo 880569 882363 := bstep (se 1 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 882363 = 1323545) B1323545
theorem B882439 : Blo 880569 882439 := bstep (se 1 (by rfl) ⟨661829, by rfl⟩ : syracuseStep 882439 = 1323659) B1323659
theorem B882447 : Blo 880569 882447 := bstep (se 1 (by rfl) ⟨661835, by rfl⟩ : syracuseStep 882447 = 1323671) B1323671
theorem B882491 : Blo 880569 882491 := bstep (se 1 (by rfl) ⟨661868, by rfl⟩ : syracuseStep 882491 = 1323737) B1323737
theorem B3766151 : Blo 880569 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B882567 : Blo 880569 882567 := bstep (se 1 (by rfl) ⟨661925, by rfl⟩ : syracuseStep 882567 = 1323851) B1323851
theorem B2979719 : Blo 880569 2979719 := bstep (se 1 (by rfl) ⟨2234789, by rfl⟩ : syracuseStep 2979719 = 4469579) B4469579
theorem B882575 : Blo 880569 882575 := bstep (se 1 (by rfl) ⟨661931, by rfl⟩ : syracuseStep 882575 = 1323863) B1323863
theorem B882619 : Blo 880569 882619 := bstep (se 1 (by rfl) ⟨661964, by rfl⟩ : syracuseStep 882619 = 1323929) B1323929
theorem B882695 : Blo 880569 882695 := bstep (se 1 (by rfl) ⟨662021, by rfl⟩ : syracuseStep 882695 = 1324043) B1324043
theorem B882703 : Blo 880569 882703 := bstep (se 1 (by rfl) ⟨662027, by rfl⟩ : syracuseStep 882703 = 1324055) B1324055
theorem B882747 : Blo 880569 882747 := bstep (se 1 (by rfl) ⟨662060, by rfl⟩ : syracuseStep 882747 = 1324121) B1324121
theorem B3176567 : Blo 880569 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B882823 : Blo 880569 882823 := bstep (se 1 (by rfl) ⟨662117, by rfl⟩ : syracuseStep 882823 = 1324235) B1324235
theorem B882831 : Blo 880569 882831 := bstep (se 1 (by rfl) ⟨662123, by rfl⟩ : syracuseStep 882831 = 1324247) B1324247
theorem B1341611 : Blo 880569 1341611 := bstep (se 1 (by rfl) ⟨1006208, by rfl⟩ : syracuseStep 1341611 = 2012417) B2012417
theorem B882875 : Blo 880569 882875 := bstep (se 1 (by rfl) ⟨662156, by rfl⟩ : syracuseStep 882875 = 1324313) B1324313
theorem B2980097 : Blo 880569 2980097 := bstep (se 2 (by rfl) ⟨1117536, by rfl⟩ : syracuseStep 2980097 = 2235073) B2235073
theorem B882951 : Blo 880569 882951 := bstep (se 1 (by rfl) ⟨662213, by rfl⟩ : syracuseStep 882951 = 1324427) B1324427
theorem B882959 : Blo 880569 882959 := bstep (se 1 (by rfl) ⟨662219, by rfl⟩ : syracuseStep 882959 = 1324439) B1324439
theorem B883003 : Blo 880569 883003 := bstep (se 1 (by rfl) ⟨662252, by rfl⟩ : syracuseStep 883003 = 1324505) B1324505
theorem B883079 : Blo 880569 883079 := bstep (se 1 (by rfl) ⟨662309, by rfl⟩ : syracuseStep 883079 = 1324619) B1324619
theorem B883087 : Blo 880569 883087 := bstep (se 1 (by rfl) ⟨662315, by rfl⟩ : syracuseStep 883087 = 1324631) B1324631
theorem B883131 : Blo 880569 883131 := bstep (se 1 (by rfl) ⟨662348, by rfl⟩ : syracuseStep 883131 = 1324697) B1324697
theorem B21559769 : Blo 880569 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B15464945 : Blo 880569 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B883207 : Blo 880569 883207 := bstep (se 1 (by rfl) ⟨662405, by rfl⟩ : syracuseStep 883207 = 1324811) B1324811
theorem B883215 : Blo 880569 883215 := bstep (se 1 (by rfl) ⟨662411, by rfl⟩ : syracuseStep 883215 = 1324823) B1324823
theorem B883259 : Blo 880569 883259 := bstep (se 1 (by rfl) ⟨662444, by rfl⟩ : syracuseStep 883259 = 1324889) B1324889
theorem B883335 : Blo 880569 883335 := bstep (se 1 (by rfl) ⟨662501, by rfl⟩ : syracuseStep 883335 = 1325003) B1325003
theorem B883343 : Blo 880569 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B883387 : Blo 880569 883387 := bstep (se 1 (by rfl) ⟨662540, by rfl⟩ : syracuseStep 883387 = 1325081) B1325081
theorem B883463 : Blo 880569 883463 := bstep (se 1 (by rfl) ⟨662597, by rfl⟩ : syracuseStep 883463 = 1325195) B1325195
theorem B883471 : Blo 880569 883471 := bstep (se 1 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 883471 = 1325207) B1325207
theorem B8485681 : Blo 880569 8485681 := bstep (se 2 (by rfl) ⟨3182130, by rfl⟩ : syracuseStep 8485681 = 6364261) B6364261
theorem B883515 : Blo 880569 883515 := bstep (se 1 (by rfl) ⟨662636, by rfl⟩ : syracuseStep 883515 = 1325273) B1325273
theorem B883591 : Blo 880569 883591 := bstep (se 1 (by rfl) ⟨662693, by rfl⟩ : syracuseStep 883591 = 1325387) B1325387
theorem B883599 : Blo 880569 883599 := bstep (se 1 (by rfl) ⟨662699, by rfl⟩ : syracuseStep 883599 = 1325399) B1325399
theorem B883643 : Blo 880569 883643 := bstep (se 1 (by rfl) ⟨662732, by rfl⟩ : syracuseStep 883643 = 1325465) B1325465
theorem B883719 : Blo 880569 883719 := bstep (se 1 (by rfl) ⟨662789, by rfl⟩ : syracuseStep 883719 = 1325579) B1325579
theorem B883727 : Blo 880569 883727 := bstep (se 1 (by rfl) ⟨662795, by rfl⟩ : syracuseStep 883727 = 1325591) B1325591
theorem B2980907 : Blo 880569 2980907 := bstep (se 1 (by rfl) ⟨2235680, by rfl⟩ : syracuseStep 2980907 = 4471361) B4471361
theorem B883771 : Blo 880569 883771 := bstep (se 1 (by rfl) ⟨662828, by rfl⟩ : syracuseStep 883771 = 1325657) B1325657
theorem B1506439 : Blo 880569 1506439 := bstep (se 1 (by rfl) ⟨1129829, by rfl⟩ : syracuseStep 1506439 = 2259659) B2259659
theorem B883847 : Blo 880569 883847 := bstep (se 1 (by rfl) ⟨662885, by rfl⟩ : syracuseStep 883847 = 1325771) B1325771
theorem B883855 : Blo 880569 883855 := bstep (se 1 (by rfl) ⟨662891, by rfl⟩ : syracuseStep 883855 = 1325783) B1325783
theorem B883899 : Blo 880569 883899 := bstep (se 1 (by rfl) ⟨662924, by rfl⟩ : syracuseStep 883899 = 1325849) B1325849
theorem B883975 : Blo 880569 883975 := bstep (se 1 (by rfl) ⟨662981, by rfl⟩ : syracuseStep 883975 = 1325963) B1325963
theorem B883983 : Blo 880569 883983 := bstep (se 1 (by rfl) ⟨662987, by rfl⟩ : syracuseStep 883983 = 1325975) B1325975
theorem B884027 : Blo 880569 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B884103 : Blo 880569 884103 := bstep (se 1 (by rfl) ⟨663077, by rfl⟩ : syracuseStep 884103 = 1326155) B1326155
theorem B884111 : Blo 880569 884111 := bstep (se 1 (by rfl) ⟨663083, by rfl⟩ : syracuseStep 884111 = 1326167) B1326167
theorem B884155 : Blo 880569 884155 := bstep (se 1 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 884155 = 1326233) B1326233
theorem B884231 : Blo 880569 884231 := bstep (se 1 (by rfl) ⟨663173, by rfl⟩ : syracuseStep 884231 = 1326347) B1326347
theorem B884239 : Blo 880569 884239 := bstep (se 1 (by rfl) ⟨663179, by rfl⟩ : syracuseStep 884239 = 1326359) B1326359
theorem B884283 : Blo 880569 884283 := bstep (se 1 (by rfl) ⟨663212, by rfl⟩ : syracuseStep 884283 = 1326425) B1326425
theorem B6717005 : Blo 880569 6717005 := bstep (se 3 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 6717005 = 2518877) B2518877
theorem B884359 : Blo 880569 884359 := bstep (se 1 (by rfl) ⟨663269, by rfl⟩ : syracuseStep 884359 = 1326539) B1326539
theorem B884367 : Blo 880569 884367 := bstep (se 1 (by rfl) ⟨663275, by rfl⟩ : syracuseStep 884367 = 1326551) B1326551
theorem B884411 : Blo 880569 884411 := bstep (se 1 (by rfl) ⟨663308, by rfl⟩ : syracuseStep 884411 = 1326617) B1326617
theorem B3768065 : Blo 880569 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B884487 : Blo 880569 884487 := bstep (se 1 (by rfl) ⟨663365, by rfl⟩ : syracuseStep 884487 = 1326731) B1326731
theorem B884495 : Blo 880569 884495 := bstep (se 1 (by rfl) ⟨663371, by rfl⟩ : syracuseStep 884495 = 1326743) B1326743
theorem B884539 : Blo 880569 884539 := bstep (se 1 (by rfl) ⟨663404, by rfl⟩ : syracuseStep 884539 = 1326809) B1326809
theorem B6356825 : Blo 880569 6356825 := bstep (se 2 (by rfl) ⟨2383809, by rfl⟩ : syracuseStep 6356825 = 4767619) B4767619
theorem B3440647 : Blo 880569 3440647 := bstep (se 1 (by rfl) ⟨2580485, by rfl⟩ : syracuseStep 3440647 = 5160971) B5160971
theorem B2982041 : Blo 880569 2982041 := bstep (se 2 (by rfl) ⟨1118265, by rfl⟩ : syracuseStep 2982041 = 2236531) B2236531
theorem B19333475 : Blo 880569 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B1507727 : Blo 880569 1507727 := bstep (se 1 (by rfl) ⟨1130795, by rfl⟩ : syracuseStep 1507727 = 2261591) B2261591
theorem B1114823 : Blo 880569 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B1114975 : Blo 880569 1114975 := bstep (se 1 (by rfl) ⟨836231, by rfl⟩ : syracuseStep 1114975 = 1672463) B1672463
theorem B1835959 : Blo 880569 1835959 := bstep (se 1 (by rfl) ⟨1376969, by rfl⟩ : syracuseStep 1835959 = 2753939) B2753939
theorem B3015695 : Blo 880569 3015695 := bstep (se 1 (by rfl) ⟨2261771, by rfl⟩ : syracuseStep 3015695 = 4523543) B4523543
theorem B2983229 : Blo 880569 2983229 := bstep (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) B1118711
theorem B3179881 : Blo 880569 3179881 := bstep (se 2 (by rfl) ⟨1192455, by rfl⟩ : syracuseStep 3179881 = 2384911) B2384911
theorem B1672903 : Blo 880569 1672903 := bstep (se 1 (by rfl) ⟨1254677, by rfl⟩ : syracuseStep 1672903 = 2509355) B2509355
theorem B9537223 : Blo 880569 9537223 := bstep (se 1 (by rfl) ⟨7152917, by rfl⟩ : syracuseStep 9537223 = 14305835) B14305835
theorem B1410923 : Blo 880569 1410923 := bstep (se 1 (by rfl) ⟨1058192, by rfl⟩ : syracuseStep 1410923 = 2116385) B2116385
theorem B4458401 : Blo 880569 4458401 := bstep (se 2 (by rfl) ⟨1671900, by rfl⟩ : syracuseStep 4458401 = 3343801) B3343801
theorem B3770525 : Blo 880569 3770525 := bstep (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) B1413947
theorem B2984093 : Blo 880569 2984093 := bstep (se 3 (by rfl) ⟨559517, by rfl⟩ : syracuseStep 2984093 = 1119035) B1119035
theorem B3574253 : Blo 880569 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B3017339 : Blo 880569 3017339 := bstep (se 1 (by rfl) ⟨2263004, by rfl⟩ : syracuseStep 3017339 = 4526009) B4526009
theorem B2984633 : Blo 880569 2984633 := bstep (se 2 (by rfl) ⟨1119237, by rfl⟩ : syracuseStep 2984633 = 2238475) B2238475
theorem B2231135 : Blo 880569 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B3345259 : Blo 880569 3345259 := bstep (se 1 (by rfl) ⟨2508944, by rfl⟩ : syracuseStep 3345259 = 5017889) B5017889
theorem B72354707 : Blo 880569 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B2821025 : Blo 880569 2821025 := bstep (se 2 (by rfl) ⟨1057884, by rfl⟩ : syracuseStep 2821025 = 2115769) B2115769
theorem B1117147 : Blo 880569 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B2722987 : Blo 880569 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B2985227 : Blo 880569 2985227 := bstep (se 1 (by rfl) ⟨2238920, by rfl⟩ : syracuseStep 2985227 = 4477841) B4477841
theorem B1609033 : Blo 880569 1609033 := bstep (se 2 (by rfl) ⟨603387, by rfl⟩ : syracuseStep 1609033 = 1206775) B1206775
theorem B2821463 : Blo 880569 2821463 := bstep (se 1 (by rfl) ⟨2116097, by rfl⟩ : syracuseStep 2821463 = 4232195) B4232195
theorem B3771791 : Blo 880569 3771791 := bstep (se 1 (by rfl) ⟨2828843, by rfl⟩ : syracuseStep 3771791 = 5657687) B5657687
theorem B1412615 : Blo 880569 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B2231833 : Blo 880569 2231833 := bstep (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) B1673875
theorem B3182291 : Blo 880569 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B2232137 : Blo 880569 2232137 := bstep (se 2 (by rfl) ⟨837051, by rfl⟩ : syracuseStep 2232137 = 1674103) B1674103
theorem B1675151 : Blo 880569 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B1413127 : Blo 880569 1413127 := bstep (se 1 (by rfl) ⟨1059845, by rfl⟩ : syracuseStep 1413127 = 2119691) B2119691
theorem B6033523 : Blo 880569 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B11309219 : Blo 880569 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B6689303 : Blo 880569 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B2822795 : Blo 880569 2822795 := bstep (se 1 (by rfl) ⟨2117096, by rfl⟩ : syracuseStep 2822795 = 4234193) B4234193
theorem B1676207 : Blo 880569 1676207 := bstep (se 1 (by rfl) ⟨1257155, by rfl⟩ : syracuseStep 1676207 = 2514311) B2514311
theorem B2233271 : Blo 880569 2233271 := bstep (se 1 (by rfl) ⟨1674953, by rfl⟩ : syracuseStep 2233271 = 3349907) B3349907
theorem B5018597 : Blo 880569 5018597 := bstep (se 4 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 5018597 = 940987) B940987
theorem B1676639 : Blo 880569 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B9541027 : Blo 880569 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B3347993 : Blo 880569 3347993 := bstep (se 2 (by rfl) ⟨1255497, by rfl⟩ : syracuseStep 3347993 = 2510995) B2510995
theorem B24188615 : Blo 880569 24188615 := bstep (se 1 (by rfl) ⟨18141461, by rfl⟩ : syracuseStep 24188615 = 36282923) B36282923
theorem B25827275 : Blo 880569 25827275 := bstep (se 1 (by rfl) ⟨19370456, by rfl⟩ : syracuseStep 25827275 = 38740913) B38740913
theorem B2234375 : Blo 880569 2234375 := bstep (se 1 (by rfl) ⟨1675781, by rfl⟩ : syracuseStep 2234375 = 3351563) B3351563
theorem B2234425 : Blo 880569 2234425 := bstep (se 2 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 2234425 = 1675819) B1675819
theorem B2234729 : Blo 880569 2234729 := bstep (se 2 (by rfl) ⟨838023, by rfl⟩ : syracuseStep 2234729 = 1676047) B1676047
theorem B1415531 : Blo 880569 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B30579079 : Blo 880569 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B3349619 : Blo 880569 3349619 := bstep (se 1 (by rfl) ⟨2512214, by rfl⟩ : syracuseStep 3349619 = 5024429) B5024429
theorem B3185821 : Blo 880569 3185821 := bstep (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) B1194683
theorem B1678583 : Blo 880569 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B3185981 : Blo 880569 3185981 := bstep (se 3 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 3185981 = 1194743) B1194743
theorem B1678735 : Blo 880569 1678735 := bstep (se 1 (by rfl) ⟨1259051, by rfl⟩ : syracuseStep 1678735 = 2518103) B2518103
theorem B1416761 : Blo 880569 1416761 := bstep (se 2 (by rfl) ⟨531285, by rfl⟩ : syracuseStep 1416761 = 1062571) B1062571
theorem B4235075 : Blo 880569 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B3579835 : Blo 880569 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B32579941 : Blo 880569 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B3350909 : Blo 880569 3350909 := bstep (se 3 (by rfl) ⟨628295, by rfl⟩ : syracuseStep 3350909 = 1256591) B1256591
theorem B2236967 : Blo 880569 2236967 := bstep (se 1 (by rfl) ⟨1677725, by rfl⟩ : syracuseStep 2236967 = 3355451) B3355451
theorem B8495675 : Blo 880569 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B991867 : Blo 880569 991867 := bstep (se 1 (by rfl) ⟨743900, by rfl⟩ : syracuseStep 991867 = 1487801) B1487801
theorem B3023659 : Blo 880569 3023659 := bstep (se 1 (by rfl) ⟨2267744, by rfl⟩ : syracuseStep 3023659 = 4535489) B4535489
theorem B2237291 : Blo 880569 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B11314241 : Blo 880569 11314241 := bstep (se 2 (by rfl) ⟨4242840, by rfl⟩ : syracuseStep 11314241 = 8485681) B8485681
theorem B992335 : Blo 880569 992335 := bstep (se 1 (by rfl) ⟨744251, by rfl⟩ : syracuseStep 992335 = 1488503) B1488503
theorem B2827511 : Blo 880569 2827511 := bstep (se 1 (by rfl) ⟨2120633, by rfl⟩ : syracuseStep 2827511 = 4241267) B4241267
theorem B1058231 : Blo 880569 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B894407 : Blo 880569 894407 := bstep (se 1 (by rfl) ⟨670805, by rfl⟩ : syracuseStep 894407 = 1341611) B1341611
theorem B992731 : Blo 880569 992731 := bstep (se 1 (by rfl) ⟨744548, by rfl⟩ : syracuseStep 992731 = 1489097) B1489097
theorem B2237939 : Blo 880569 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B2008585 : Blo 880569 2008585 := bstep (se 2 (by rfl) ⟨753219, by rfl⟩ : syracuseStep 2008585 = 1506439) B1506439
theorem B2238151 : Blo 880569 2238151 := bstep (se 1 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 2238151 = 3357227) B3357227
theorem B6694649 : Blo 880569 6694649 := bstep (se 2 (by rfl) ⟨2510493, by rfl⟩ : syracuseStep 6694649 = 5020987) B5020987
theorem B993199 : Blo 880569 993199 := bstep (se 1 (by rfl) ⟨744899, by rfl⟩ : syracuseStep 993199 = 1489799) B1489799
theorem B1320887 : Blo 880569 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B1058779 : Blo 880569 1058779 := bstep (se 1 (by rfl) ⟨794084, by rfl⟩ : syracuseStep 1058779 = 1588169) B1588169
theorem B1320923 : Blo 880569 1320923 := bstep (se 1 (by rfl) ⟨990692, by rfl⟩ : syracuseStep 1320923 = 1981385) B1981385
theorem B2828459 : Blo 880569 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B3352823 : Blo 880569 3352823 := bstep (se 1 (by rfl) ⟨2514617, by rfl⟩ : syracuseStep 3352823 = 5029235) B5029235
theorem B12921121 : Blo 880569 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B993631 : Blo 880569 993631 := bstep (se 1 (by rfl) ⟨745223, by rfl⟩ : syracuseStep 993631 = 1490447) B1490447
theorem B10070405 : Blo 880569 10070405 := bstep (se 4 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 10070405 = 1888201) B1888201
theorem B1321391 : Blo 880569 1321391 := bstep (se 1 (by rfl) ⟨991043, by rfl⟩ : syracuseStep 1321391 = 1982087) B1982087
theorem B1321481 : Blo 880569 1321481 := bstep (se 2 (by rfl) ⟨495555, by rfl⟩ : syracuseStep 1321481 = 991111) B991111
theorem B1321511 : Blo 880569 1321511 := bstep (se 1 (by rfl) ⟨991133, by rfl⟩ : syracuseStep 1321511 = 1982267) B1982267
theorem B4237883 : Blo 880569 4237883 := bstep (se 1 (by rfl) ⟨3178412, by rfl⟩ : syracuseStep 4237883 = 6356825) B6356825
theorem B1321595 : Blo 880569 1321595 := bstep (se 1 (by rfl) ⟨991196, by rfl⟩ : syracuseStep 1321595 = 1982393) B1982393
theorem B993991 : Blo 880569 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B1321721 : Blo 880569 1321721 := bstep (se 2 (by rfl) ⟨495645, by rfl⟩ : syracuseStep 1321721 = 991291) B991291
theorem B1321823 : Blo 880569 1321823 := bstep (se 1 (by rfl) ⟨991367, by rfl⟩ : syracuseStep 1321823 = 1982735) B1982735
theorem B4762475 : Blo 880569 4762475 := bstep (se 1 (by rfl) ⟨3571856, by rfl⟩ : syracuseStep 4762475 = 7143713) B7143713
theorem B1321835 : Blo 880569 1321835 := bstep (se 1 (by rfl) ⟨991376, by rfl⟩ : syracuseStep 1321835 = 1982753) B1982753
theorem B5647279 : Blo 880569 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B1322063 : Blo 880569 1322063 := bstep (se 1 (by rfl) ⟨991547, by rfl⟩ : syracuseStep 1322063 = 1983095) B1983095
theorem B6696107 : Blo 880569 6696107 := bstep (se 1 (by rfl) ⟨5022080, by rfl⟩ : syracuseStep 6696107 = 10044161) B10044161
theorem B3353795 : Blo 880569 3353795 := bstep (se 1 (by rfl) ⟨2515346, by rfl⟩ : syracuseStep 3353795 = 5030693) B5030693
theorem B1322183 : Blo 880569 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B4467959 : Blo 880569 4467959 := bstep (se 1 (by rfl) ⟨3350969, by rfl⟩ : syracuseStep 4467959 = 6701939) B6701939
theorem B1486073 : Blo 880569 1486073 := bstep (se 2 (by rfl) ⟨557277, by rfl⟩ : syracuseStep 1486073 = 1114555) B1114555
theorem B1322345 : Blo 880569 1322345 := bstep (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) B991759
theorem B1486255 : Blo 880569 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B1191343 : Blo 880569 1191343 := bstep (se 1 (by rfl) ⟨893507, by rfl⟩ : syracuseStep 1191343 = 1787015) B1787015
theorem B1322423 : Blo 880569 1322423 := bstep (se 1 (by rfl) ⟨991817, by rfl⟩ : syracuseStep 1322423 = 1983635) B1983635
theorem B1256887 : Blo 880569 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B1322459 : Blo 880569 1322459 := bstep (se 1 (by rfl) ⟨991844, by rfl⟩ : syracuseStep 1322459 = 1983689) B1983689
theorem B1486343 : Blo 880569 1486343 := bstep (se 1 (by rfl) ⟨1114757, by rfl⟩ : syracuseStep 1486343 = 2229515) B2229515
theorem B994855 : Blo 880569 994855 := bstep (se 1 (by rfl) ⟨746141, by rfl⟩ : syracuseStep 994855 = 1492283) B1492283
theorem B6696593 : Blo 880569 6696593 := bstep (se 2 (by rfl) ⟨2511222, by rfl⟩ : syracuseStep 6696593 = 5022445) B5022445
theorem B2829971 : Blo 880569 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B3354311 : Blo 880569 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B4468445 : Blo 880569 4468445 := bstep (se 3 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 4468445 = 1675667) B1675667
theorem B6368989 : Blo 880569 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B1486687 : Blo 880569 1486687 := bstep (se 1 (by rfl) ⟨1115015, by rfl⟩ : syracuseStep 1486687 = 2230031) B2230031
theorem B1453967 : Blo 880569 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B2830241 : Blo 880569 2830241 := bstep (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) B2122681
theorem B1322927 : Blo 880569 1322927 := bstep (se 1 (by rfl) ⟨992195, by rfl⟩ : syracuseStep 1322927 = 1984391) B1984391
theorem B1486775 : Blo 880569 1486775 := bstep (se 1 (by rfl) ⟨1115081, by rfl⟩ : syracuseStep 1486775 = 2230163) B2230163
theorem B1323017 : Blo 880569 1323017 := bstep (se 2 (by rfl) ⟨496131, by rfl⟩ : syracuseStep 1323017 = 992263) B992263
theorem B2830355 : Blo 880569 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B9056285 : Blo 880569 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B1323047 : Blo 880569 1323047 := bstep (se 1 (by rfl) ⟨992285, by rfl⟩ : syracuseStep 1323047 = 1984571) B1984571
theorem B1323131 : Blo 880569 1323131 := bstep (se 1 (by rfl) ⟨992348, by rfl⟩ : syracuseStep 1323131 = 1984697) B1984697
theorem B1323257 : Blo 880569 1323257 := bstep (se 2 (by rfl) ⟨496221, by rfl⟩ : syracuseStep 1323257 = 992443) B992443
theorem B1323359 : Blo 880569 1323359 := bstep (se 1 (by rfl) ⟨992519, by rfl⟩ : syracuseStep 1323359 = 1985039) B1985039
theorem B1323371 : Blo 880569 1323371 := bstep (se 1 (by rfl) ⟨992528, by rfl⟩ : syracuseStep 1323371 = 1985057) B1985057
theorem B1487369 : Blo 880569 1487369 := bstep (se 2 (by rfl) ⟨557763, by rfl⟩ : syracuseStep 1487369 = 1115527) B1115527
theorem B3584537 : Blo 880569 3584537 := bstep (se 2 (by rfl) ⟨1344201, by rfl⟩ : syracuseStep 3584537 = 2688403) B2688403
theorem B1323599 : Blo 880569 1323599 := bstep (se 1 (by rfl) ⟨992699, by rfl⟩ : syracuseStep 1323599 = 1985399) B1985399
theorem B3355283 : Blo 880569 3355283 := bstep (se 1 (by rfl) ⟨2516462, by rfl⟩ : syracuseStep 3355283 = 5032925) B5032925
theorem B1487531 : Blo 880569 1487531 := bstep (se 1 (by rfl) ⟨1115648, by rfl⟩ : syracuseStep 1487531 = 2231297) B2231297
theorem B1323719 : Blo 880569 1323719 := bstep (se 1 (by rfl) ⟨992789, by rfl⟩ : syracuseStep 1323719 = 1985579) B1985579
theorem B1061575 : Blo 880569 1061575 := bstep (se 1 (by rfl) ⟨796181, by rfl⟩ : syracuseStep 1061575 = 1592363) B1592363
theorem B3355465 : Blo 880569 3355465 := bstep (se 2 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 3355465 = 2516599) B2516599
theorem B1323881 : Blo 880569 1323881 := bstep (se 2 (by rfl) ⟨496455, by rfl⟩ : syracuseStep 1323881 = 992911) B992911
theorem B1258345 : Blo 880569 1258345 := bstep (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) B943759
theorem B1323959 : Blo 880569 1323959 := bstep (se 1 (by rfl) ⟨992969, by rfl⟩ : syracuseStep 1323959 = 1985939) B1985939
theorem B1323995 : Blo 880569 1323995 := bstep (se 1 (by rfl) ⟨992996, by rfl⟩ : syracuseStep 1323995 = 1985993) B1985993
theorem B1487929 : Blo 880569 1487929 := bstep (se 2 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 1487929 = 1115947) B1115947
theorem B6698051 : Blo 880569 6698051 := bstep (se 1 (by rfl) ⟨5023538, by rfl⟩ : syracuseStep 6698051 = 10047077) B10047077
theorem B1488071 : Blo 880569 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B10171595 : Blo 880569 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B1488233 : Blo 880569 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B1324463 : Blo 880569 1324463 := bstep (se 1 (by rfl) ⟨993347, by rfl⟩ : syracuseStep 1324463 = 1986695) B1986695
theorem B1324553 : Blo 880569 1324553 := bstep (se 2 (by rfl) ⟨496707, by rfl⟩ : syracuseStep 1324553 = 993415) B993415
theorem B2831881 : Blo 880569 2831881 := bstep (se 2 (by rfl) ⟨1061955, by rfl⟩ : syracuseStep 2831881 = 2123911) B2123911
theorem B1324583 : Blo 880569 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B1324667 : Blo 880569 1324667 := bstep (se 1 (by rfl) ⟨993500, by rfl⟩ : syracuseStep 1324667 = 1987001) B1987001
theorem B1357511 : Blo 880569 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B3815111 : Blo 880569 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B1488631 : Blo 880569 1488631 := bstep (se 1 (by rfl) ⟨1116473, by rfl⟩ : syracuseStep 1488631 = 2232947) B2232947
theorem B1324793 : Blo 880569 1324793 := bstep (se 2 (by rfl) ⟨496797, by rfl⟩ : syracuseStep 1324793 = 993595) B993595
theorem B6371065 : Blo 880569 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B1324895 : Blo 880569 1324895 := bstep (se 1 (by rfl) ⟨993671, by rfl⟩ : syracuseStep 1324895 = 1987343) B1987343
theorem B1324907 : Blo 880569 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B1488827 : Blo 880569 1488827 := bstep (se 1 (by rfl) ⟨1116620, by rfl⟩ : syracuseStep 1488827 = 2233241) B2233241
theorem B5027777 : Blo 880569 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B6699023 : Blo 880569 6699023 := bstep (se 1 (by rfl) ⟨5024267, by rfl⟩ : syracuseStep 6699023 = 10048535) B10048535
theorem B1488935 : Blo 880569 1488935 := bstep (se 1 (by rfl) ⟨1116701, by rfl⟩ : syracuseStep 1488935 = 2233403) B2233403
theorem B1325135 : Blo 880569 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B1325255 : Blo 880569 1325255 := bstep (se 1 (by rfl) ⟨993941, by rfl⟩ : syracuseStep 1325255 = 1987883) B1987883
theorem B5650661 : Blo 880569 5650661 := bstep (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) B1059499
theorem B1489225 : Blo 880569 1489225 := bstep (se 2 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 1489225 = 1116919) B1116919
theorem B1325417 : Blo 880569 1325417 := bstep (se 2 (by rfl) ⟨497031, by rfl⟩ : syracuseStep 1325417 = 994063) B994063
theorem B1489259 : Blo 880569 1489259 := bstep (se 1 (by rfl) ⟨1116944, by rfl⟩ : syracuseStep 1489259 = 2233889) B2233889
theorem B1325495 : Blo 880569 1325495 := bstep (se 1 (by rfl) ⟨994121, by rfl⟩ : syracuseStep 1325495 = 1988243) B1988243
theorem B15055307 : Blo 880569 15055307 := bstep (se 1 (by rfl) ⟨11291480, by rfl⟩ : syracuseStep 15055307 = 22582961) B22582961
theorem B1325531 : Blo 880569 1325531 := bstep (se 1 (by rfl) ⟨994148, by rfl⟩ : syracuseStep 1325531 = 1988297) B1988297
theorem B3357395 : Blo 880569 3357395 := bstep (se 1 (by rfl) ⟨2518046, by rfl⟩ : syracuseStep 3357395 = 5036093) B5036093
theorem B1489657 : Blo 880569 1489657 := bstep (se 2 (by rfl) ⟨558621, by rfl⟩ : syracuseStep 1489657 = 1117243) B1117243
theorem B1325999 : Blo 880569 1325999 := bstep (se 1 (by rfl) ⟨994499, by rfl⟩ : syracuseStep 1325999 = 1988999) B1988999
theorem B2833327 : Blo 880569 2833327 := bstep (se 1 (by rfl) ⟨2124995, by rfl⟩ : syracuseStep 2833327 = 4249991) B4249991
theorem B57129907 : Blo 880569 57129907 := bstep (se 1 (by rfl) ⟨42847430, by rfl⟩ : syracuseStep 57129907 = 85694861) B85694861
theorem B1981367 : Blo 880569 1981367 := bstep (se 1 (by rfl) ⟨1486025, by rfl⟩ : syracuseStep 1981367 = 2972051) B2972051
theorem B1489927 : Blo 880569 1489927 := bstep (se 1 (by rfl) ⟨1117445, by rfl⟩ : syracuseStep 1489927 = 2234891) B2234891
theorem B1326089 : Blo 880569 1326089 := bstep (se 2 (by rfl) ⟨497283, by rfl⟩ : syracuseStep 1326089 = 994567) B994567
theorem B1326119 : Blo 880569 1326119 := bstep (se 1 (by rfl) ⟨994589, by rfl⟩ : syracuseStep 1326119 = 1989179) B1989179
theorem B1326203 : Blo 880569 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B1326329 : Blo 880569 1326329 := bstep (se 2 (by rfl) ⟨497373, by rfl⟩ : syracuseStep 1326329 = 994747) B994747
theorem B1326431 : Blo 880569 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1326443 : Blo 880569 1326443 := bstep (se 1 (by rfl) ⟨994832, by rfl⟩ : syracuseStep 1326443 = 1989665) B1989665
theorem B1490359 : Blo 880569 1490359 := bstep (se 1 (by rfl) ⟨1117769, by rfl⟩ : syracuseStep 1490359 = 2235539) B2235539
theorem B1981961 : Blo 880569 1981961 := bstep (se 2 (by rfl) ⟨743235, by rfl⟩ : syracuseStep 1981961 = 1486471) B1486471
theorem B1883657 : Blo 880569 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1326671 : Blo 880569 1326671 := bstep (se 1 (by rfl) ⟨995003, by rfl⟩ : syracuseStep 1326671 = 1990007) B1990007
theorem B1490555 : Blo 880569 1490555 := bstep (se 1 (by rfl) ⟨1117916, by rfl⟩ : syracuseStep 1490555 = 2235833) B2235833
theorem B1326791 : Blo 880569 1326791 := bstep (se 1 (by rfl) ⟨995093, by rfl⟩ : syracuseStep 1326791 = 1990187) B1990187
theorem B1982303 : Blo 880569 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B1883999 : Blo 880569 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B8470457 : Blo 880569 8470457 := bstep (se 2 (by rfl) ⟨3176421, by rfl⟩ : syracuseStep 8470457 = 6352843) B6352843
theorem B1490953 : Blo 880569 1490953 := bstep (se 2 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 1490953 = 1118215) B1118215
theorem B1982483 : Blo 880569 1982483 := bstep (se 1 (by rfl) ⟨1486862, by rfl⟩ : syracuseStep 1982483 = 2973725) B2973725
theorem B1491115 : Blo 880569 1491115 := bstep (se 1 (by rfl) ⟨1118336, by rfl⟩ : syracuseStep 1491115 = 2236673) B2236673
theorem B19087589 : Blo 880569 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B1982825 : Blo 880569 1982825 := bstep (se 2 (by rfl) ⟨743559, by rfl⟩ : syracuseStep 1982825 = 1487119) B1487119
theorem B6373835 : Blo 880569 6373835 := bstep (se 1 (by rfl) ⟨4780376, by rfl⟩ : syracuseStep 6373835 = 9560753) B9560753
theorem B1491419 : Blo 880569 1491419 := bstep (se 1 (by rfl) ⟨1118564, by rfl⟩ : syracuseStep 1491419 = 2237129) B2237129
theorem B1491655 : Blo 880569 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B4473629 : Blo 880569 4473629 := bstep (se 3 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 4473629 = 1677611) B1677611
theorem B1491817 : Blo 880569 1491817 := bstep (se 2 (by rfl) ⟨559431, by rfl⟩ : syracuseStep 1491817 = 1118863) B1118863
theorem B2016175 : Blo 880569 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B1983419 : Blo 880569 1983419 := bstep (se 1 (by rfl) ⟨1487564, by rfl⟩ : syracuseStep 1983419 = 2975129) B2975129
theorem B1983545 : Blo 880569 1983545 := bstep (se 2 (by rfl) ⟨743829, by rfl⟩ : syracuseStep 1983545 = 1487659) B1487659
theorem B2508023 : Blo 880569 2508023 := bstep (se 1 (by rfl) ⟨1881017, by rfl⟩ : syracuseStep 2508023 = 3762035) B3762035
theorem B6702425 : Blo 880569 6702425 := bstep (se 2 (by rfl) ⟨2513409, by rfl⟩ : syracuseStep 6702425 = 5026819) B5026819
theorem B16106845 : Blo 880569 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B1983887 : Blo 880569 1983887 := bstep (se 1 (by rfl) ⟨1487915, by rfl⟩ : syracuseStep 1983887 = 2975831) B2975831
theorem B1492411 : Blo 880569 1492411 := bstep (se 1 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 1492411 = 2238617) B2238617
theorem B1492519 : Blo 880569 1492519 := bstep (se 1 (by rfl) ⟨1119389, by rfl⟩ : syracuseStep 1492519 = 2238779) B2238779
theorem B12699179 : Blo 880569 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B5359243 : Blo 880569 5359243 := bstep (se 1 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 5359243 = 8038865) B8038865
theorem B1984211 : Blo 880569 1984211 := bstep (se 1 (by rfl) ⟨1488158, by rfl⟩ : syracuseStep 1984211 = 2976317) B2976317
theorem B6637571 : Blo 880569 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B7161871 : Blo 880569 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B11290661 : Blo 880569 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B8604107 : Blo 880569 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B1985147 : Blo 880569 1985147 := bstep (se 1 (by rfl) ⟨1488860, by rfl⟩ : syracuseStep 1985147 = 2977721) B2977721
theorem B1591931 : Blo 880569 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B1985273 : Blo 880569 1985273 := bstep (se 2 (by rfl) ⟨744477, by rfl⟩ : syracuseStep 1985273 = 1488955) B1488955
theorem B2509663 : Blo 880569 2509663 := bstep (se 1 (by rfl) ⟨1882247, by rfl⟩ : syracuseStep 2509663 = 3764495) B3764495
theorem B4770667 : Blo 880569 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B1985543 : Blo 880569 1985543 := bstep (se 1 (by rfl) ⟨1489157, by rfl⟩ : syracuseStep 1985543 = 2978315) B2978315
theorem B1985615 : Blo 880569 1985615 := bstep (se 1 (by rfl) ⟨1489211, by rfl⟩ : syracuseStep 1985615 = 2978423) B2978423
theorem B1986011 : Blo 880569 1986011 := bstep (se 1 (by rfl) ⟨1489508, by rfl⟩ : syracuseStep 1986011 = 2979017) B2979017
theorem B1134119 : Blo 880569 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B6704855 : Blo 880569 6704855 := bstep (se 1 (by rfl) ⟨5028641, by rfl⟩ : syracuseStep 6704855 = 10057283) B10057283
theorem B5656301 : Blo 880569 5656301 := bstep (se 3 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 5656301 = 2121113) B2121113
theorem B2510585 : Blo 880569 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B2510767 : Blo 880569 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B1986479 : Blo 880569 1986479 := bstep (se 1 (by rfl) ⟨1489859, by rfl⟩ : syracuseStep 1986479 = 2979719) B2979719
theorem B1036327 : Blo 880569 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B2117711 : Blo 880569 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B1986731 : Blo 880569 1986731 := bstep (se 1 (by rfl) ⟨1490048, by rfl⟩ : syracuseStep 1986731 = 2980097) B2980097
theorem B14373179 : Blo 880569 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B10309963 : Blo 880569 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B5362157 : Blo 880569 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B1987271 : Blo 880569 1987271 := bstep (se 1 (by rfl) ⟨1490453, by rfl⟩ : syracuseStep 1987271 = 2980907) B2980907
theorem B4478003 : Blo 880569 4478003 := bstep (se 1 (by rfl) ⟨3358502, by rfl⟩ : syracuseStep 4478003 = 6717005) B6717005
theorem B2512043 : Blo 880569 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B2151809 : Blo 880569 2151809 := bstep (se 2 (by rfl) ⟨806928, by rfl⟩ : syracuseStep 2151809 = 1613857) B1613857
theorem B2512271 : Blo 880569 2512271 := bstep (se 1 (by rfl) ⟨1884203, by rfl⟩ : syracuseStep 2512271 = 3768407) B3768407
theorem B16307675 : Blo 880569 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B1988135 : Blo 880569 1988135 := bstep (se 1 (by rfl) ⟨1491101, by rfl⟩ : syracuseStep 1988135 = 2982203) B2982203
theorem B1988459 : Blo 880569 1988459 := bstep (se 1 (by rfl) ⟨1491344, by rfl⟩ : syracuseStep 1988459 = 2982689) B2982689
theorem B1988513 : Blo 880569 1988513 := bstep (se 2 (by rfl) ⟨745692, by rfl⟩ : syracuseStep 1988513 = 1491385) B1491385
theorem B4773977 : Blo 880569 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B1988855 : Blo 880569 1988855 := bstep (se 1 (by rfl) ⟨1491641, by rfl⟩ : syracuseStep 1988855 = 2983283) B2983283
theorem B2972105 : Blo 880569 2972105 := bstep (se 2 (by rfl) ⟨1114539, by rfl⟩ : syracuseStep 2972105 = 2229079) B2229079
theorem B5036525 : Blo 880569 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B6707771 : Blo 880569 6707771 := bstep (se 1 (by rfl) ⟨5030828, by rfl⟩ : syracuseStep 6707771 = 10061657) B10061657
theorem B2972375 : Blo 880569 2972375 := bstep (se 1 (by rfl) ⟨2229281, by rfl⟩ : syracuseStep 2972375 = 4458563) B4458563
theorem B1989449 : Blo 880569 1989449 := bstep (se 2 (by rfl) ⟨746043, by rfl⟩ : syracuseStep 1989449 = 1492087) B1492087
theorem B2972591 : Blo 880569 2972591 := bstep (se 1 (by rfl) ⟨2229443, by rfl⟩ : syracuseStep 2972591 = 4458887) B4458887
theorem B1793063 : Blo 880569 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B5102795 : Blo 880569 5102795 := bstep (se 1 (by rfl) ⟨3827096, by rfl⟩ : syracuseStep 5102795 = 7654193) B7654193
theorem B1990241 : Blo 880569 1990241 := bstep (se 2 (by rfl) ⟨746340, by rfl⟩ : syracuseStep 1990241 = 1492681) B1492681
theorem B6348577 : Blo 880569 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B85909733 : Blo 880569 85909733 := bstep (se 4 (by rfl) ⟨8054037, by rfl⟩ : syracuseStep 85909733 = 16108075) B16108075
theorem B4776203 : Blo 880569 4776203 := bstep (se 1 (by rfl) ⟨3582152, by rfl⟩ : syracuseStep 4776203 = 7164305) B7164305
theorem B16998731 : Blo 880569 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B2515495 : Blo 880569 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B12248113 : Blo 880569 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B10871927 : Blo 880569 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B15262937 : Blo 880569 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B2974967 : Blo 880569 2974967 := bstep (se 1 (by rfl) ⟨2231225, by rfl⟩ : syracuseStep 2974967 = 4462451) B4462451
theorem B5727653 : Blo 880569 5727653 := bstep (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) B1073935
theorem B2975291 : Blo 880569 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B3761761 : Blo 880569 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B2975561 : Blo 880569 2975561 := bstep (se 2 (by rfl) ⟨1115835, by rfl⟩ : syracuseStep 2975561 = 2231671) B2231671
theorem B4778041 : Blo 880569 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B1697915 : Blo 880569 1697915 := bstep (se 1 (by rfl) ⟨1273436, by rfl⟩ : syracuseStep 1697915 = 2546873) B2546873
theorem B4778345 : Blo 880569 4778345 := bstep (se 2 (by rfl) ⟨1791879, by rfl⟩ : syracuseStep 4778345 = 3583759) B3583759
theorem B9562657 : Blo 880569 9562657 := bstep (se 2 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 9562657 = 7171993) B7171993
theorem B1862495 : Blo 880569 1862495 := bstep (se 1 (by rfl) ⟨1396871, by rfl⟩ : syracuseStep 1862495 = 2793743) B2793743
theorem B2976695 : Blo 880569 2976695 := bstep (se 1 (by rfl) ⟨2232521, by rfl⟩ : syracuseStep 2976695 = 4465043) B4465043
theorem B2977289 : Blo 880569 2977289 := bstep (se 2 (by rfl) ⟨1116483, by rfl⟩ : syracuseStep 2977289 = 2232967) B2232967
theorem B2387465 : Blo 880569 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B880583 : Blo 880569 880583 := bstep (se 1 (by rfl) ⟨660437, by rfl⟩ : syracuseStep 880583 = 1320875) B1320875
theorem B880603 : Blo 880569 880603 := bstep (se 1 (by rfl) ⟨660452, by rfl⟩ : syracuseStep 880603 = 1320905) B1320905
theorem B880679 : Blo 880569 880679 := bstep (se 1 (by rfl) ⟨660509, by rfl⟩ : syracuseStep 880679 = 1321019) B1321019
theorem B2388025 : Blo 880569 2388025 := bstep (se 2 (by rfl) ⟨895509, by rfl⟩ : syracuseStep 2388025 = 1791019) B1791019
theorem B880719 : Blo 880569 880719 := bstep (se 1 (by rfl) ⟨660539, by rfl⟩ : syracuseStep 880719 = 1321079) B1321079
theorem B880735 : Blo 880569 880735 := bstep (se 1 (by rfl) ⟨660551, by rfl⟩ : syracuseStep 880735 = 1321103) B1321103
theorem B880763 : Blo 880569 880763 := bstep (se 1 (by rfl) ⟨660572, by rfl⟩ : syracuseStep 880763 = 1321145) B1321145
theorem B880815 : Blo 880569 880815 := bstep (se 1 (by rfl) ⟨660611, by rfl⟩ : syracuseStep 880815 = 1321223) B1321223
theorem B880839 : Blo 880569 880839 := bstep (se 1 (by rfl) ⟨660629, by rfl⟩ : syracuseStep 880839 = 1321259) B1321259
theorem B880859 : Blo 880569 880859 := bstep (se 1 (by rfl) ⟨660644, by rfl⟩ : syracuseStep 880859 = 1321289) B1321289
theorem B880935 : Blo 880569 880935 := bstep (se 1 (by rfl) ⟨660701, by rfl⟩ : syracuseStep 880935 = 1321403) B1321403
theorem B880975 : Blo 880569 880975 := bstep (se 1 (by rfl) ⟨660731, by rfl⟩ : syracuseStep 880975 = 1321463) B1321463
theorem B880991 : Blo 880569 880991 := bstep (se 1 (by rfl) ⟨660743, by rfl⟩ : syracuseStep 880991 = 1321487) B1321487
theorem B2978153 : Blo 880569 2978153 := bstep (se 2 (by rfl) ⟨1116807, by rfl⟩ : syracuseStep 2978153 = 2233615) B2233615
theorem B881019 : Blo 880569 881019 := bstep (se 1 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 881019 = 1321529) B1321529
theorem B881071 : Blo 880569 881071 := bstep (se 1 (by rfl) ⟨660803, by rfl⟩ : syracuseStep 881071 = 1321607) B1321607
theorem B881095 : Blo 880569 881095 := bstep (se 1 (by rfl) ⟨660821, by rfl⟩ : syracuseStep 881095 = 1321643) B1321643
theorem B881115 : Blo 880569 881115 := bstep (se 1 (by rfl) ⟨660836, by rfl⟩ : syracuseStep 881115 = 1321673) B1321673
theorem B3764717 : Blo 880569 3764717 := bstep (se 3 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 3764717 = 1411769) B1411769
theorem B3633673 : Blo 880569 3633673 := bstep (se 2 (by rfl) ⟨1362627, by rfl⟩ : syracuseStep 3633673 = 2725255) B2725255
theorem B881191 : Blo 880569 881191 := bstep (se 1 (by rfl) ⟨660893, by rfl⟩ : syracuseStep 881191 = 1321787) B1321787
theorem B881231 : Blo 880569 881231 := bstep (se 1 (by rfl) ⟨660923, by rfl⟩ : syracuseStep 881231 = 1321847) B1321847
theorem B881247 : Blo 880569 881247 := bstep (se 1 (by rfl) ⟨660935, by rfl⟩ : syracuseStep 881247 = 1321871) B1321871
theorem B881275 : Blo 880569 881275 := bstep (se 1 (by rfl) ⟨660956, by rfl⟩ : syracuseStep 881275 = 1321913) B1321913
theorem B881327 : Blo 880569 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B881351 : Blo 880569 881351 := bstep (se 1 (by rfl) ⟨661013, by rfl⟩ : syracuseStep 881351 = 1322027) B1322027
theorem B881371 : Blo 880569 881371 := bstep (se 1 (by rfl) ⟨661028, by rfl⟩ : syracuseStep 881371 = 1322057) B1322057
theorem B881447 : Blo 880569 881447 := bstep (se 1 (by rfl) ⟨661085, by rfl⟩ : syracuseStep 881447 = 1322171) B1322171
theorem B881487 : Blo 880569 881487 := bstep (se 1 (by rfl) ⟨661115, by rfl⟩ : syracuseStep 881487 = 1322231) B1322231
theorem B881503 : Blo 880569 881503 := bstep (se 1 (by rfl) ⟨661127, by rfl⟩ : syracuseStep 881503 = 1322255) B1322255
theorem B881531 : Blo 880569 881531 := bstep (se 1 (by rfl) ⟨661148, by rfl⟩ : syracuseStep 881531 = 1322297) B1322297
theorem B881583 : Blo 880569 881583 := bstep (se 1 (by rfl) ⟨661187, by rfl⟩ : syracuseStep 881583 = 1322375) B1322375
theorem B2978747 : Blo 880569 2978747 := bstep (se 1 (by rfl) ⟨2234060, by rfl⟩ : syracuseStep 2978747 = 4468121) B4468121
theorem B881607 : Blo 880569 881607 := bstep (se 1 (by rfl) ⟨661205, by rfl⟩ : syracuseStep 881607 = 1322411) B1322411
theorem B881627 : Blo 880569 881627 := bstep (se 1 (by rfl) ⟨661220, by rfl⟩ : syracuseStep 881627 = 1322441) B1322441
theorem B881703 : Blo 880569 881703 := bstep (se 1 (by rfl) ⟨661277, by rfl⟩ : syracuseStep 881703 = 1322555) B1322555
theorem B881743 : Blo 880569 881743 := bstep (se 1 (by rfl) ⟨661307, by rfl⟩ : syracuseStep 881743 = 1322615) B1322615
theorem B881759 : Blo 880569 881759 := bstep (se 1 (by rfl) ⟨661319, by rfl⟩ : syracuseStep 881759 = 1322639) B1322639
theorem B881787 : Blo 880569 881787 := bstep (se 1 (by rfl) ⟨661340, by rfl⟩ : syracuseStep 881787 = 1322681) B1322681
theorem B881839 : Blo 880569 881839 := bstep (se 1 (by rfl) ⟨661379, by rfl⟩ : syracuseStep 881839 = 1322759) B1322759
theorem B881863 : Blo 880569 881863 := bstep (se 1 (by rfl) ⟨661397, by rfl⟩ : syracuseStep 881863 = 1322795) B1322795
theorem B881883 : Blo 880569 881883 := bstep (se 1 (by rfl) ⟨661412, by rfl⟩ : syracuseStep 881883 = 1322825) B1322825
theorem B881959 : Blo 880569 881959 := bstep (se 1 (by rfl) ⟨661469, by rfl⟩ : syracuseStep 881959 = 1322939) B1322939
theorem B881999 : Blo 880569 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B882015 : Blo 880569 882015 := bstep (se 1 (by rfl) ⟨661511, by rfl⟩ : syracuseStep 882015 = 1323023) B1323023
theorem B882043 : Blo 880569 882043 := bstep (se 1 (by rfl) ⟨661532, by rfl⟩ : syracuseStep 882043 = 1323065) B1323065
theorem B8058275 : Blo 880569 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B882095 : Blo 880569 882095 := bstep (se 1 (by rfl) ⟨661571, by rfl⟩ : syracuseStep 882095 = 1323143) B1323143
theorem B882119 : Blo 880569 882119 := bstep (se 1 (by rfl) ⟨661589, by rfl⟩ : syracuseStep 882119 = 1323179) B1323179
theorem B882139 : Blo 880569 882139 := bstep (se 1 (by rfl) ⟨661604, by rfl⟩ : syracuseStep 882139 = 1323209) B1323209
theorem B1209865 : Blo 880569 1209865 := bstep (se 2 (by rfl) ⟨453699, by rfl⟩ : syracuseStep 1209865 = 907399) B907399
theorem B882215 : Blo 880569 882215 := bstep (se 1 (by rfl) ⟨661661, by rfl⟩ : syracuseStep 882215 = 1323323) B1323323
theorem B882255 : Blo 880569 882255 := bstep (se 1 (by rfl) ⟨661691, by rfl⟩ : syracuseStep 882255 = 1323383) B1323383
theorem B882271 : Blo 880569 882271 := bstep (se 1 (by rfl) ⟨661703, by rfl⟩ : syracuseStep 882271 = 1323407) B1323407
theorem B882299 : Blo 880569 882299 := bstep (se 1 (by rfl) ⟨661724, by rfl⟩ : syracuseStep 882299 = 1323449) B1323449
theorem B5666449 : Blo 880569 5666449 := bstep (se 2 (by rfl) ⟨2124918, by rfl⟩ : syracuseStep 5666449 = 4249837) B4249837
theorem B882351 : Blo 880569 882351 := bstep (se 1 (by rfl) ⟨661763, by rfl⟩ : syracuseStep 882351 = 1323527) B1323527
theorem B3176135 : Blo 880569 3176135 := bstep (se 1 (by rfl) ⟨2382101, by rfl⟩ : syracuseStep 3176135 = 4764203) B4764203
theorem B882375 : Blo 880569 882375 := bstep (se 1 (by rfl) ⟨661781, by rfl⟩ : syracuseStep 882375 = 1323563) B1323563
theorem B882395 : Blo 880569 882395 := bstep (se 1 (by rfl) ⟨661796, by rfl⟩ : syracuseStep 882395 = 1323593) B1323593
theorem B882471 : Blo 880569 882471 := bstep (se 1 (by rfl) ⟨661853, by rfl⟩ : syracuseStep 882471 = 1323707) B1323707
theorem B882511 : Blo 880569 882511 := bstep (se 1 (by rfl) ⟨661883, by rfl⟩ : syracuseStep 882511 = 1323767) B1323767
theorem B882527 : Blo 880569 882527 := bstep (se 1 (by rfl) ⟨661895, by rfl⟩ : syracuseStep 882527 = 1323791) B1323791
theorem B3766135 : Blo 880569 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B882555 : Blo 880569 882555 := bstep (se 1 (by rfl) ⟨661916, by rfl⟩ : syracuseStep 882555 = 1323833) B1323833
theorem B882607 : Blo 880569 882607 := bstep (se 1 (by rfl) ⟨661955, by rfl⟩ : syracuseStep 882607 = 1323911) B1323911
theorem B882631 : Blo 880569 882631 := bstep (se 1 (by rfl) ⟨661973, by rfl⟩ : syracuseStep 882631 = 1323947) B1323947
theorem B882651 : Blo 880569 882651 := bstep (se 1 (by rfl) ⟨661988, by rfl⟩ : syracuseStep 882651 = 1323977) B1323977
theorem B882727 : Blo 880569 882727 := bstep (se 1 (by rfl) ⟨662045, by rfl⟩ : syracuseStep 882727 = 1324091) B1324091
theorem B882767 : Blo 880569 882767 := bstep (se 1 (by rfl) ⟨662075, by rfl⟩ : syracuseStep 882767 = 1324151) B1324151
theorem B1210447 : Blo 880569 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B882783 : Blo 880569 882783 := bstep (se 1 (by rfl) ⟨662087, by rfl⟩ : syracuseStep 882783 = 1324175) B1324175
theorem B882811 : Blo 880569 882811 := bstep (se 1 (by rfl) ⟨662108, by rfl⟩ : syracuseStep 882811 = 1324217) B1324217
theorem B882863 : Blo 880569 882863 := bstep (se 1 (by rfl) ⟨662147, by rfl⟩ : syracuseStep 882863 = 1324295) B1324295
theorem B882887 : Blo 880569 882887 := bstep (se 1 (by rfl) ⟨662165, by rfl⟩ : syracuseStep 882887 = 1324331) B1324331
theorem B882907 : Blo 880569 882907 := bstep (se 1 (by rfl) ⟨662180, by rfl⟩ : syracuseStep 882907 = 1324361) B1324361
theorem B882983 : Blo 880569 882983 := bstep (se 1 (by rfl) ⟨662237, by rfl⟩ : syracuseStep 882983 = 1324475) B1324475
theorem B883023 : Blo 880569 883023 := bstep (se 1 (by rfl) ⟨662267, by rfl⟩ : syracuseStep 883023 = 1324535) B1324535
theorem B883039 : Blo 880569 883039 := bstep (se 1 (by rfl) ⟨662279, by rfl⟩ : syracuseStep 883039 = 1324559) B1324559
theorem B883067 : Blo 880569 883067 := bstep (se 1 (by rfl) ⟨662300, by rfl⟩ : syracuseStep 883067 = 1324601) B1324601
theorem B883119 : Blo 880569 883119 := bstep (se 1 (by rfl) ⟨662339, by rfl⟩ : syracuseStep 883119 = 1324679) B1324679
theorem B883143 : Blo 880569 883143 := bstep (se 1 (by rfl) ⟨662357, by rfl⟩ : syracuseStep 883143 = 1324715) B1324715
theorem B883163 : Blo 880569 883163 := bstep (se 1 (by rfl) ⟨662372, by rfl⟩ : syracuseStep 883163 = 1324745) B1324745
theorem B2685449 : Blo 880569 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B883239 : Blo 880569 883239 := bstep (se 1 (by rfl) ⟨662429, by rfl⟩ : syracuseStep 883239 = 1324859) B1324859
theorem B883279 : Blo 880569 883279 := bstep (se 1 (by rfl) ⟨662459, by rfl⟩ : syracuseStep 883279 = 1324919) B1324919
theorem B883295 : Blo 880569 883295 := bstep (se 1 (by rfl) ⟨662471, by rfl⟩ : syracuseStep 883295 = 1324943) B1324943
theorem B2980475 : Blo 880569 2980475 := bstep (se 1 (by rfl) ⟨2235356, by rfl⟩ : syracuseStep 2980475 = 4470713) B4470713
theorem B883323 : Blo 880569 883323 := bstep (se 1 (by rfl) ⟨662492, by rfl⟩ : syracuseStep 883323 = 1324985) B1324985
theorem B883375 : Blo 880569 883375 := bstep (se 1 (by rfl) ⟨662531, by rfl⟩ : syracuseStep 883375 = 1325063) B1325063
theorem B883399 : Blo 880569 883399 := bstep (se 1 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 883399 = 1325099) B1325099
theorem B883419 : Blo 880569 883419 := bstep (se 1 (by rfl) ⟨662564, by rfl⟩ : syracuseStep 883419 = 1325129) B1325129
theorem B2980637 : Blo 880569 2980637 := bstep (se 3 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 2980637 = 1117739) B1117739
theorem B883495 : Blo 880569 883495 := bstep (se 1 (by rfl) ⟨662621, by rfl⟩ : syracuseStep 883495 = 1325243) B1325243
theorem B883535 : Blo 880569 883535 := bstep (se 1 (by rfl) ⟨662651, by rfl⟩ : syracuseStep 883535 = 1325303) B1325303
theorem B883551 : Blo 880569 883551 := bstep (se 1 (by rfl) ⟨662663, by rfl⟩ : syracuseStep 883551 = 1325327) B1325327
theorem B883579 : Blo 880569 883579 := bstep (se 1 (by rfl) ⟨662684, by rfl⟩ : syracuseStep 883579 = 1325369) B1325369
theorem B8616851 : Blo 880569 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B883631 : Blo 880569 883631 := bstep (se 1 (by rfl) ⟨662723, by rfl⟩ : syracuseStep 883631 = 1325447) B1325447
theorem B883655 : Blo 880569 883655 := bstep (se 1 (by rfl) ⟨662741, by rfl⟩ : syracuseStep 883655 = 1325483) B1325483
theorem B883675 : Blo 880569 883675 := bstep (se 1 (by rfl) ⟨662756, by rfl⟩ : syracuseStep 883675 = 1325513) B1325513
theorem B883751 : Blo 880569 883751 := bstep (se 1 (by rfl) ⟨662813, by rfl⟩ : syracuseStep 883751 = 1325627) B1325627
theorem B883791 : Blo 880569 883791 := bstep (se 1 (by rfl) ⟨662843, by rfl⟩ : syracuseStep 883791 = 1325687) B1325687
theorem B883807 : Blo 880569 883807 := bstep (se 1 (by rfl) ⟨662855, by rfl⟩ : syracuseStep 883807 = 1325711) B1325711
theorem B883835 : Blo 880569 883835 := bstep (se 1 (by rfl) ⟨662876, by rfl⟩ : syracuseStep 883835 = 1325753) B1325753
theorem B883887 : Blo 880569 883887 := bstep (se 1 (by rfl) ⟨662915, by rfl⟩ : syracuseStep 883887 = 1325831) B1325831
theorem B883911 : Blo 880569 883911 := bstep (se 1 (by rfl) ⟨662933, by rfl⟩ : syracuseStep 883911 = 1325867) B1325867
theorem B883931 : Blo 880569 883931 := bstep (se 1 (by rfl) ⟨662948, by rfl⟩ : syracuseStep 883931 = 1325897) B1325897
theorem B884007 : Blo 880569 884007 := bstep (se 1 (by rfl) ⟨663005, by rfl⟩ : syracuseStep 884007 = 1326011) B1326011
theorem B884047 : Blo 880569 884047 := bstep (se 1 (by rfl) ⟨663035, by rfl⟩ : syracuseStep 884047 = 1326071) B1326071
theorem B6782297 : Blo 880569 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B884063 : Blo 880569 884063 := bstep (se 1 (by rfl) ⟨663047, by rfl⟩ : syracuseStep 884063 = 1326095) B1326095
theorem B884091 : Blo 880569 884091 := bstep (se 1 (by rfl) ⟨663068, by rfl⟩ : syracuseStep 884091 = 1326137) B1326137
theorem B884143 : Blo 880569 884143 := bstep (se 1 (by rfl) ⟨663107, by rfl⟩ : syracuseStep 884143 = 1326215) B1326215
theorem B884167 : Blo 880569 884167 := bstep (se 1 (by rfl) ⟨663125, by rfl⟩ : syracuseStep 884167 = 1326251) B1326251
theorem B2981339 : Blo 880569 2981339 := bstep (se 1 (by rfl) ⟨2236004, by rfl⟩ : syracuseStep 2981339 = 4472009) B4472009
theorem B884187 : Blo 880569 884187 := bstep (se 1 (by rfl) ⟨663140, by rfl⟩ : syracuseStep 884187 = 1326281) B1326281
theorem B884263 : Blo 880569 884263 := bstep (se 1 (by rfl) ⟨663197, by rfl⟩ : syracuseStep 884263 = 1326395) B1326395
theorem B884303 : Blo 880569 884303 := bstep (se 1 (by rfl) ⟨663227, by rfl⟩ : syracuseStep 884303 = 1326455) B1326455
theorem B884319 : Blo 880569 884319 := bstep (se 1 (by rfl) ⟨663239, by rfl⟩ : syracuseStep 884319 = 1326479) B1326479
theorem B884347 : Blo 880569 884347 := bstep (se 1 (by rfl) ⟨663260, by rfl⟩ : syracuseStep 884347 = 1326521) B1326521
theorem B884399 : Blo 880569 884399 := bstep (se 1 (by rfl) ⟨663299, by rfl⟩ : syracuseStep 884399 = 1326599) B1326599
theorem B884423 : Blo 880569 884423 := bstep (se 1 (by rfl) ⟨663317, by rfl⟩ : syracuseStep 884423 = 1326635) B1326635
theorem B884443 : Blo 880569 884443 := bstep (se 1 (by rfl) ⟨663332, by rfl⟩ : syracuseStep 884443 = 1326665) B1326665
theorem B884519 : Blo 880569 884519 := bstep (se 1 (by rfl) ⟨663389, by rfl⟩ : syracuseStep 884519 = 1326779) B1326779
theorem B884559 : Blo 880569 884559 := bstep (se 1 (by rfl) ⟨663419, by rfl⟩ : syracuseStep 884559 = 1326839) B1326839
theorem B4587529 : Blo 880569 4587529 := bstep (se 2 (by rfl) ⟨1720323, by rfl⟩ : syracuseStep 4587529 = 3440647) B3440647
theorem B6455717 : Blo 880569 6455717 := bstep (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) B1210447
theorem B2982419 : Blo 880569 2982419 := bstep (se 1 (by rfl) ⟨2236814, by rfl⟩ : syracuseStep 2982419 = 4473629) B4473629
theorem B1672015 : Blo 880569 1672015 := bstep (se 1 (by rfl) ⟨1254011, by rfl⟩ : syracuseStep 1672015 = 2508023) B2508023
theorem B4031545 : Blo 880569 4031545 := bstep (se 2 (by rfl) ⟨1511829, by rfl⟩ : syracuseStep 4031545 = 3023659) B3023659
theorem B2688233 : Blo 880569 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B4425047 : Blo 880569 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B5736071 : Blo 880569 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B48236471 : Blo 880569 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B5015681 : Blo 880569 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B7145657 : Blo 880569 7145657 := bstep (se 2 (by rfl) ⟨2679621, by rfl⟩ : syracuseStep 7145657 = 5359243) B5359243
theorem B2230537 : Blo 880569 2230537 := bstep (se 2 (by rfl) ⟨836451, by rfl⟩ : syracuseStep 2230537 = 1672903) B1672903
theorem B12716297 : Blo 880569 12716297 := bstep (se 2 (by rfl) ⟨4768611, by rfl⟩ : syracuseStep 12716297 = 9537223) B9537223
theorem B2984201 : Blo 880569 2984201 := bstep (se 2 (by rfl) ⟨1119075, by rfl⟩ : syracuseStep 2984201 = 2238151) B2238151
theorem B3770867 : Blo 880569 3770867 := bstep (se 1 (by rfl) ⟨2828150, by rfl⟩ : syracuseStep 3770867 = 5656301) B5656301
theorem B1673723 : Blo 880569 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B1116767 : Blo 880569 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B1411705 : Blo 880569 1411705 := bstep (se 2 (by rfl) ⟨529389, by rfl⟩ : syracuseStep 1411705 = 1058779) B1058779
theorem B7539479 : Blo 880569 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B4459535 : Blo 880569 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B1117471 : Blo 880569 1117471 := bstep (se 1 (by rfl) ⟨838103, by rfl⟩ : syracuseStep 1117471 = 1676207) B1676207
theorem B3345731 : Blo 880569 3345731 := bstep (se 1 (by rfl) ⟨2509298, by rfl⟩ : syracuseStep 3345731 = 5018597) B5018597
theorem B2985335 : Blo 880569 2985335 := bstep (se 1 (by rfl) ⟨2239001, by rfl⟩ : syracuseStep 2985335 = 4478003) B4478003
theorem B12750209 : Blo 880569 12750209 := bstep (se 2 (by rfl) ⟨4781328, by rfl⟩ : syracuseStep 12750209 = 9562657) B9562657
theorem B1674695 : Blo 880569 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B1674847 : Blo 880569 1674847 := bstep (se 1 (by rfl) ⟨1256135, by rfl⟩ : syracuseStep 1674847 = 2512271) B2512271
theorem B2231995 : Blo 880569 2231995 := bstep (se 1 (by rfl) ⟨1673996, by rfl⟩ : syracuseStep 2231995 = 3347993) B3347993
theorem B3346217 : Blo 880569 3346217 := bstep (se 2 (by rfl) ⟨1254831, by rfl⟩ : syracuseStep 3346217 = 2509663) B2509663
theorem B16125743 : Blo 880569 16125743 := bstep (se 1 (by rfl) ⟨12094307, by rfl⟩ : syracuseStep 16125743 = 24188615) B24188615
theorem B4460345 : Blo 880569 4460345 := bstep (se 2 (by rfl) ⟨1672629, by rfl⟩ : syracuseStep 4460345 = 3345259) B3345259
theorem B2821949 : Blo 880569 2821949 := bstep (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) B1058231
theorem B3182651 : Blo 880569 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B2233079 : Blo 880569 2233079 := bstep (se 1 (by rfl) ⟨1674809, by rfl⟩ : syracuseStep 2233079 = 3349619) B3349619
theorem B8491985 : Blo 880569 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B2823383 : Blo 880569 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B3347689 : Blo 880569 3347689 := bstep (se 2 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 3347689 = 2510767) B2510767
theorem B1381769 : Blo 880569 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B3184033 : Blo 880569 3184033 := bstep (se 2 (by rfl) ⟨1194012, by rfl⟩ : syracuseStep 3184033 = 2388025) B2388025
theorem B2233939 : Blo 880569 2233939 := bstep (se 1 (by rfl) ⟨1675454, by rfl⟩ : syracuseStep 2233939 = 3350909) B3350909
theorem B7542827 : Blo 880569 7542827 := bstep (se 1 (by rfl) ⟨5657120, by rfl⟩ : syracuseStep 7542827 = 11314241) B11314241
theorem B7247951 : Blo 880569 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B14522597 : Blo 880569 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B4463099 : Blo 880569 4463099 := bstep (se 1 (by rfl) ⟨3347324, by rfl⟩ : syracuseStep 4463099 = 6694649) B6694649
theorem B2235215 : Blo 880569 2235215 := bstep (se 1 (by rfl) ⟨1676411, by rfl⟩ : syracuseStep 2235215 = 3352823) B3352823
theorem B3185563 : Blo 880569 3185563 := bstep (se 1 (by rfl) ⟨2389172, by rfl⟩ : syracuseStep 3185563 = 4778345) B4778345
theorem B2825255 : Blo 880569 2825255 := bstep (se 1 (by rfl) ⟨2118941, by rfl⟩ : syracuseStep 2825255 = 4237883) B4237883
theorem B12721369 : Blo 880569 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B1613153 : Blo 880569 1613153 := bstep (se 2 (by rfl) ⟨604932, by rfl⟩ : syracuseStep 1613153 = 1209865) B1209865
theorem B3775841 : Blo 880569 3775841 := bstep (se 2 (by rfl) ⟨1415940, by rfl⟩ : syracuseStep 3775841 = 2831881) B2831881
theorem B4464071 : Blo 880569 4464071 := bstep (se 1 (by rfl) ⟨3348053, by rfl⟩ : syracuseStep 4464071 = 6696107) B6696107
theorem B2235863 : Blo 880569 2235863 := bstep (se 1 (by rfl) ⟨1676897, by rfl⟩ : syracuseStep 2235863 = 3353795) B3353795
theorem B990715 : Blo 880569 990715 := bstep (se 1 (by rfl) ⟨743036, by rfl⟩ : syracuseStep 990715 = 1486073) B1486073
theorem B8494753 : Blo 880569 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B990895 : Blo 880569 990895 := bstep (se 1 (by rfl) ⟨743171, by rfl⟩ : syracuseStep 990895 = 1486343) B1486343
theorem B4464395 : Blo 880569 4464395 := bstep (se 1 (by rfl) ⟨3348296, by rfl⟩ : syracuseStep 4464395 = 6696593) B6696593
theorem B2236207 : Blo 880569 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B5021513 : Blo 880569 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B991183 : Blo 880569 991183 := bstep (se 1 (by rfl) ⟨743387, by rfl⟩ : syracuseStep 991183 = 1486775) B1486775
theorem B6037523 : Blo 880569 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B991579 : Blo 880569 991579 := bstep (se 1 (by rfl) ⟨743684, by rfl⟩ : syracuseStep 991579 = 1487369) B1487369
theorem B2236855 : Blo 880569 2236855 := bstep (se 1 (by rfl) ⟨1677641, by rfl⟩ : syracuseStep 2236855 = 3355283) B3355283
theorem B991687 : Blo 880569 991687 := bstep (se 1 (by rfl) ⟨743765, by rfl⟩ : syracuseStep 991687 = 1487531) B1487531
theorem B40772105 : Blo 880569 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B13607453 : Blo 880569 13607453 := bstep (se 3 (by rfl) ⟨2551397, by rfl⟩ : syracuseStep 13607453 = 5102795) B5102795
theorem B4465367 : Blo 880569 4465367 := bstep (se 1 (by rfl) ⟨3349025, by rfl⟩ : syracuseStep 4465367 = 6698051) B6698051
theorem B992047 : Blo 880569 992047 := bstep (se 1 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 992047 = 1488071) B1488071
theorem B992155 : Blo 880569 992155 := bstep (se 1 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 992155 = 1488233) B1488233
theorem B3777769 : Blo 880569 3777769 := bstep (se 2 (by rfl) ⟨1416663, by rfl⟩ : syracuseStep 3777769 = 2833327) B2833327
theorem B992551 : Blo 880569 992551 := bstep (se 1 (by rfl) ⟨744413, by rfl⟩ : syracuseStep 992551 = 1488827) B1488827
theorem B3351851 : Blo 880569 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B4466015 : Blo 880569 4466015 := bstep (se 1 (by rfl) ⟨3349511, by rfl⟩ : syracuseStep 4466015 = 6699023) B6699023
theorem B992623 : Blo 880569 992623 := bstep (se 1 (by rfl) ⟨744467, by rfl⟩ : syracuseStep 992623 = 1488935) B1488935
theorem B3024317 : Blo 880569 3024317 := bstep (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) B1134119
theorem B992839 : Blo 880569 992839 := bstep (se 1 (by rfl) ⟨744629, by rfl⟩ : syracuseStep 992839 = 1489259) B1489259
theorem B10036871 : Blo 880569 10036871 := bstep (se 1 (by rfl) ⟨7527653, by rfl⟩ : syracuseStep 10036871 = 15055307) B15055307
theorem B2238263 : Blo 880569 2238263 := bstep (se 1 (by rfl) ⟨1678697, by rfl⟩ : syracuseStep 2238263 = 3357395) B3357395
theorem B2238313 : Blo 880569 2238313 := bstep (se 2 (by rfl) ⟨839367, by rfl⟩ : syracuseStep 2238313 = 1678735) B1678735
theorem B5744567 : Blo 880569 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B1320911 : Blo 880569 1320911 := bstep (se 1 (by rfl) ⟨990683, by rfl⟩ : syracuseStep 1320911 = 1981367) B1981367
theorem B1321307 : Blo 880569 1321307 := bstep (se 1 (by rfl) ⟨990980, by rfl⟩ : syracuseStep 1321307 = 1981961) B1981961
theorem B1255771 : Blo 880569 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B8464769 : Blo 880569 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B993703 : Blo 880569 993703 := bstep (se 1 (by rfl) ⟨745277, by rfl⟩ : syracuseStep 993703 = 1490555) B1490555
theorem B1321535 : Blo 880569 1321535 := bstep (se 1 (by rfl) ⟨991151, by rfl⟩ : syracuseStep 1321535 = 1982303) B1982303
theorem B1255999 : Blo 880569 1255999 := bstep (se 1 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 1255999 = 1883999) B1883999
theorem B5646971 : Blo 880569 5646971 := bstep (se 1 (by rfl) ⟨4235228, by rfl⟩ : syracuseStep 5646971 = 8470457) B8470457
theorem B1321655 : Blo 880569 1321655 := bstep (se 1 (by rfl) ⟨991241, by rfl⟩ : syracuseStep 1321655 = 1982483) B1982483
theorem B5647229 : Blo 880569 5647229 := bstep (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) B2117711
theorem B12888983 : Blo 880569 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B1321883 : Blo 880569 1321883 := bstep (se 1 (by rfl) ⟨991412, by rfl⟩ : syracuseStep 1321883 = 1982825) B1982825
theorem B994279 : Blo 880569 994279 := bstep (se 1 (by rfl) ⟨745709, by rfl⟩ : syracuseStep 994279 = 1491419) B1491419
theorem B50900237 : Blo 880569 50900237 := bstep (se 3 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 50900237 = 19087589) B19087589
theorem B1322279 : Blo 880569 1322279 := bstep (se 1 (by rfl) ⟨991709, by rfl⟩ : syracuseStep 1322279 = 1983419) B1983419
theorem B2010463 : Blo 880569 2010463 := bstep (se 1 (by rfl) ⟨1507847, by rfl⟩ : syracuseStep 2010463 = 3015695) B3015695
theorem B1322363 : Blo 880569 1322363 := bstep (se 1 (by rfl) ⟨991772, by rfl⟩ : syracuseStep 1322363 = 1983545) B1983545
theorem B3353993 : Blo 880569 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B1322489 : Blo 880569 1322489 := bstep (se 2 (by rfl) ⟨495933, by rfl⟩ : syracuseStep 1322489 = 991867) B991867
theorem B4468283 : Blo 880569 4468283 := bstep (se 1 (by rfl) ⟨3351212, by rfl⟩ : syracuseStep 4468283 = 6702425) B6702425
theorem B1322591 : Blo 880569 1322591 := bstep (se 1 (by rfl) ⟨991943, by rfl⟩ : syracuseStep 1322591 = 1983887) B1983887
theorem B8466119 : Blo 880569 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B1486633 : Blo 880569 1486633 := bstep (se 2 (by rfl) ⟨557487, by rfl⟩ : syracuseStep 1486633 = 1114975) B1114975
theorem B1322807 : Blo 880569 1322807 := bstep (se 1 (by rfl) ⟨992105, by rfl⟩ : syracuseStep 1322807 = 1984211) B1984211
theorem B14299085 : Blo 880569 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B16330817 : Blo 880569 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1323113 : Blo 880569 1323113 := bstep (se 2 (by rfl) ⟨496167, by rfl⟩ : syracuseStep 1323113 = 992335) B992335
theorem B2011559 : Blo 880569 2011559 := bstep (se 1 (by rfl) ⟨1508669, by rfl⟩ : syracuseStep 2011559 = 3017339) B3017339
theorem B1323431 : Blo 880569 1323431 := bstep (se 1 (by rfl) ⟨992573, by rfl⟩ : syracuseStep 1323431 = 1985147) B1985147
theorem B21475793 : Blo 880569 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B1323515 : Blo 880569 1323515 := bstep (se 1 (by rfl) ⟨992636, by rfl⟩ : syracuseStep 1323515 = 1985273) B1985273
theorem B1487423 : Blo 880569 1487423 := bstep (se 1 (by rfl) ⟨1115567, by rfl⟩ : syracuseStep 1487423 = 2231135) B2231135
theorem B1323641 : Blo 880569 1323641 := bstep (se 2 (by rfl) ⟨496365, by rfl⟩ : syracuseStep 1323641 = 992731) B992731
theorem B1323695 : Blo 880569 1323695 := bstep (se 1 (by rfl) ⟨992771, by rfl⟩ : syracuseStep 1323695 = 1985543) B1985543
theorem B1323743 : Blo 880569 1323743 := bstep (se 1 (by rfl) ⟨992807, by rfl⟩ : syracuseStep 1323743 = 1985615) B1985615
theorem B1880975 : Blo 880569 1880975 := bstep (se 1 (by rfl) ⟨1410731, by rfl⟩ : syracuseStep 1880975 = 2821463) B2821463
theorem B1324007 : Blo 880569 1324007 := bstep (se 1 (by rfl) ⟨993005, by rfl⟩ : syracuseStep 1324007 = 1986011) B1986011
theorem B4469903 : Blo 880569 4469903 := bstep (se 1 (by rfl) ⟨3352427, by rfl⟩ : syracuseStep 4469903 = 6704855) B6704855
theorem B1488091 : Blo 880569 1488091 := bstep (se 1 (by rfl) ⟨1116068, by rfl⟩ : syracuseStep 1488091 = 2232137) B2232137
theorem B1324265 : Blo 880569 1324265 := bstep (se 2 (by rfl) ⟨496599, by rfl⟩ : syracuseStep 1324265 = 993199) B993199
theorem B1324319 : Blo 880569 1324319 := bstep (se 1 (by rfl) ⟨993239, by rfl⟩ : syracuseStep 1324319 = 1986479) B1986479
theorem B9549161 : Blo 880569 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B6370721 : Blo 880569 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B1324487 : Blo 880569 1324487 := bstep (se 1 (by rfl) ⟨993365, by rfl⟩ : syracuseStep 1324487 = 1986731) B1986731
theorem B9582119 : Blo 880569 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B1881863 : Blo 880569 1881863 := bstep (se 1 (by rfl) ⟨1411397, by rfl⟩ : syracuseStep 1881863 = 2822795) B2822795
theorem B1324841 : Blo 880569 1324841 := bstep (se 2 (by rfl) ⟨496815, by rfl⟩ : syracuseStep 1324841 = 993631) B993631
theorem B1324847 : Blo 880569 1324847 := bstep (se 1 (by rfl) ⟨993635, by rfl⟩ : syracuseStep 1324847 = 1987271) B1987271
theorem B1488847 : Blo 880569 1488847 := bstep (se 1 (by rfl) ⟨1116635, by rfl⟩ : syracuseStep 1488847 = 2233271) B2233271
theorem B4471037 : Blo 880569 4471037 := bstep (se 3 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 4471037 = 1676639) B1676639
theorem B1325321 : Blo 880569 1325321 := bstep (se 2 (by rfl) ⟨496995, by rfl⟩ : syracuseStep 1325321 = 993991) B993991
theorem B1325423 : Blo 880569 1325423 := bstep (se 1 (by rfl) ⟨994067, by rfl⟩ : syracuseStep 1325423 = 1988135) B1988135
theorem B1325639 : Blo 880569 1325639 := bstep (se 1 (by rfl) ⟨994229, by rfl⟩ : syracuseStep 1325639 = 1988459) B1988459
theorem B1325675 : Blo 880569 1325675 := bstep (se 1 (by rfl) ⟨994256, by rfl⟩ : syracuseStep 1325675 = 1988513) B1988513
theorem B1489529 : Blo 880569 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B17218183 : Blo 880569 17218183 := bstep (se 1 (by rfl) ⟨12913637, by rfl⟩ : syracuseStep 17218183 = 25827275) B25827275
theorem B1489583 : Blo 880569 1489583 := bstep (se 1 (by rfl) ⟨1117187, by rfl⟩ : syracuseStep 1489583 = 2234375) B2234375
theorem B1325903 : Blo 880569 1325903 := bstep (se 1 (by rfl) ⟨994427, by rfl⟩ : syracuseStep 1325903 = 1988855) B1988855
theorem B1489819 : Blo 880569 1489819 := bstep (se 1 (by rfl) ⟨1117364, by rfl⟩ : syracuseStep 1489819 = 2234729) B2234729
theorem B1981403 : Blo 880569 1981403 := bstep (se 1 (by rfl) ⟨1486052, by rfl⟩ : syracuseStep 1981403 = 2972105) B2972105
theorem B3357683 : Blo 880569 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B4471847 : Blo 880569 4471847 := bstep (se 1 (by rfl) ⟨3353885, by rfl⟩ : syracuseStep 4471847 = 6707771) B6707771
theorem B2145377 : Blo 880569 2145377 := bstep (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) B1609033
theorem B1981583 : Blo 880569 1981583 := bstep (se 1 (by rfl) ⟨1486187, by rfl⟩ : syracuseStep 1981583 = 2972375) B2972375
theorem B1326299 : Blo 880569 1326299 := bstep (se 1 (by rfl) ⟨994724, by rfl⟩ : syracuseStep 1326299 = 1989449) B1989449
theorem B25443557 : Blo 880569 25443557 := bstep (se 4 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 25443557 = 4770667) B4770667
theorem B1981673 : Blo 880569 1981673 := bstep (se 2 (by rfl) ⟨743127, by rfl⟩ : syracuseStep 1981673 = 1486255) B1486255
theorem B1588457 : Blo 880569 1588457 := bstep (se 2 (by rfl) ⟨595671, by rfl⟩ : syracuseStep 1588457 = 1191343) B1191343
theorem B1981727 : Blo 880569 1981727 := bstep (se 1 (by rfl) ⟨1486295, by rfl⟩ : syracuseStep 1981727 = 2972591) B2972591
theorem B1326473 : Blo 880569 1326473 := bstep (se 2 (by rfl) ⟨497427, by rfl⟩ : syracuseStep 1326473 = 994855) B994855
theorem B1326827 : Blo 880569 1326827 := bstep (se 1 (by rfl) ⟨995120, by rfl⟩ : syracuseStep 1326827 = 1990241) B1990241
theorem B1982249 : Blo 880569 1982249 := bstep (se 2 (by rfl) ⟨743343, by rfl⟩ : syracuseStep 1982249 = 1486687) B1486687
theorem B1884169 : Blo 880569 1884169 := bstep (se 2 (by rfl) ⟨706563, by rfl⟩ : syracuseStep 1884169 = 1413127) B1413127
theorem B8044697 : Blo 880569 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B1491311 : Blo 880569 1491311 := bstep (se 1 (by rfl) ⟨1118483, by rfl⟩ : syracuseStep 1491311 = 2236967) B2236967
theorem B13746617 : Blo 880569 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B1491527 : Blo 880569 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B10175291 : Blo 880569 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B16991045 : Blo 880569 16991045 := bstep (se 4 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 16991045 = 3185821) B3185821
theorem B1983311 : Blo 880569 1983311 := bstep (se 1 (by rfl) ⟨1487483, by rfl⟩ : syracuseStep 1983311 = 2974967) B2974967
theorem B1885007 : Blo 880569 1885007 := bstep (se 1 (by rfl) ⟨1413755, by rfl⟩ : syracuseStep 1885007 = 2827511) B2827511
theorem B3818435 : Blo 880569 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B1491959 : Blo 880569 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1983527 : Blo 880569 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B4473953 : Blo 880569 4473953 := bstep (se 2 (by rfl) ⟨1677732, by rfl⟩ : syracuseStep 4473953 = 3355465) B3355465
theorem B1983707 : Blo 880569 1983707 := bstep (se 1 (by rfl) ⟨1487780, by rfl⟩ : syracuseStep 1983707 = 2975561) B2975561
theorem B1983905 : Blo 880569 1983905 := bstep (se 2 (by rfl) ⟨743964, by rfl⟩ : syracuseStep 1983905 = 1487929) B1487929
theorem B1131943 : Blo 880569 1131943 := bstep (se 1 (by rfl) ⟨848957, by rfl⟩ : syracuseStep 1131943 = 1697915) B1697915
theorem B1885639 : Blo 880569 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B4245149 : Blo 880569 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B16959365 : Blo 880569 16959365 := bstep (se 4 (by rfl) ⟨1589940, by rfl⟩ : syracuseStep 16959365 = 3179881) B3179881
theorem B1984463 : Blo 880569 1984463 := bstep (se 1 (by rfl) ⟨1488347, by rfl⟩ : syracuseStep 1984463 = 2976695) B2976695
theorem B7555265 : Blo 880569 7555265 := bstep (se 2 (by rfl) ⟨2833224, by rfl⟩ : syracuseStep 7555265 = 5666449) B5666449
theorem B6703397 : Blo 880569 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1984841 : Blo 880569 1984841 := bstep (se 2 (by rfl) ⟨744315, by rfl⟩ : syracuseStep 1984841 = 1488631) B1488631
theorem B1984859 : Blo 880569 1984859 := bstep (se 1 (by rfl) ⟨1488644, by rfl⟩ : syracuseStep 1984859 = 2977289) B2977289
theorem B1591643 : Blo 880569 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B7522733 : Blo 880569 7522733 := bstep (se 3 (by rfl) ⟨1410512, by rfl⟩ : syracuseStep 7522733 = 2821025) B2821025
theorem B1886647 : Blo 880569 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B969311 : Blo 880569 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B1886827 : Blo 880569 1886827 := bstep (se 1 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 1886827 = 2830241) B2830241
theorem B1886903 : Blo 880569 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B1985435 : Blo 880569 1985435 := bstep (se 1 (by rfl) ⟨1489076, by rfl⟩ : syracuseStep 1985435 = 2978153) B2978153
theorem B2509811 : Blo 880569 2509811 := bstep (se 1 (by rfl) ⟨1882358, by rfl⟩ : syracuseStep 2509811 = 3764717) B3764717
theorem B1985633 : Blo 880569 1985633 := bstep (se 2 (by rfl) ⟨744612, by rfl⟩ : syracuseStep 1985633 = 1489225) B1489225
theorem B1985831 : Blo 880569 1985831 := bstep (se 1 (by rfl) ⟨1489373, by rfl⟩ : syracuseStep 1985831 = 2978747) B2978747
theorem B4476221 : Blo 880569 4476221 := bstep (se 3 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 4476221 = 1678583) B1678583
theorem B1986209 : Blo 880569 1986209 := bstep (se 2 (by rfl) ⟨744828, by rfl⟩ : syracuseStep 1986209 = 1489657) B1489657
theorem B2543407 : Blo 880569 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B2117423 : Blo 880569 2117423 := bstep (se 1 (by rfl) ⟨1588067, by rfl⟩ : syracuseStep 2117423 = 3176135) B3176135
theorem B76173209 : Blo 880569 76173209 := bstep (se 2 (by rfl) ⟨28564953, by rfl⟩ : syracuseStep 76173209 = 57129907) B57129907
theorem B1986569 : Blo 880569 1986569 := bstep (se 2 (by rfl) ⟨744963, by rfl⟩ : syracuseStep 1986569 = 1489927) B1489927
theorem B1790299 : Blo 880569 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B1986983 : Blo 880569 1986983 := bstep (se 1 (by rfl) ⟨1490237, by rfl⟩ : syracuseStep 1986983 = 2980475) B2980475
theorem B1987091 : Blo 880569 1987091 := bstep (se 1 (by rfl) ⟨1490318, by rfl⟩ : syracuseStep 1987091 = 2980637) B2980637
theorem B1987145 : Blo 880569 1987145 := bstep (se 2 (by rfl) ⟨745179, by rfl⟩ : syracuseStep 1987145 = 1490359) B1490359
theorem B1987559 : Blo 880569 1987559 := bstep (se 1 (by rfl) ⟨1490669, by rfl⟩ : syracuseStep 1987559 = 2981339) B2981339
theorem B4773113 : Blo 880569 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B1987937 : Blo 880569 1987937 := bstep (se 2 (by rfl) ⟨745476, by rfl⟩ : syracuseStep 1987937 = 1490953) B1490953
theorem B1988027 : Blo 880569 1988027 := bstep (se 1 (by rfl) ⟨1491020, by rfl⟩ : syracuseStep 1988027 = 2982041) B2982041
theorem B1988153 : Blo 880569 1988153 := bstep (se 2 (by rfl) ⟨745557, by rfl⟩ : syracuseStep 1988153 = 1491115) B1491115
theorem B1005151 : Blo 880569 1005151 := bstep (se 1 (by rfl) ⟨753863, by rfl⟩ : syracuseStep 1005151 = 1507727) B1507727
theorem B4249223 : Blo 880569 4249223 := bstep (se 1 (by rfl) ⟨3186917, by rfl⟩ : syracuseStep 4249223 = 6373835) B6373835
theorem B43439921 : Blo 880569 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B12736541 : Blo 880569 12736541 := bstep (se 3 (by rfl) ⟨2388101, by rfl⟩ : syracuseStep 12736541 = 4776203) B4776203
theorem B1988819 : Blo 880569 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B1988873 : Blo 880569 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B1989089 : Blo 880569 1989089 := bstep (se 2 (by rfl) ⟨745908, by rfl⟩ : syracuseStep 1989089 = 1491817) B1491817
theorem B940615 : Blo 880569 940615 := bstep (se 1 (by rfl) ⟨705461, by rfl⟩ : syracuseStep 940615 = 1410923) B1410923
theorem B2447945 : Blo 880569 2447945 := bstep (se 2 (by rfl) ⟨917979, by rfl⟩ : syracuseStep 2447945 = 1835959) B1835959
theorem B2972267 : Blo 880569 2972267 := bstep (se 1 (by rfl) ⟨2229200, by rfl⟩ : syracuseStep 2972267 = 4458401) B4458401
theorem B7527107 : Blo 880569 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B2513683 : Blo 880569 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B1989395 : Blo 880569 1989395 := bstep (se 1 (by rfl) ⟨1492046, by rfl⟩ : syracuseStep 1989395 = 2984093) B2984093
theorem B1989755 : Blo 880569 1989755 := bstep (se 1 (by rfl) ⟨1492316, by rfl⟩ : syracuseStep 1989755 = 2984633) B2984633
theorem B2972861 : Blo 880569 2972861 := bstep (se 3 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 2972861 = 1114823) B1114823
theorem B1989881 : Blo 880569 1989881 := bstep (se 2 (by rfl) ⟨746205, by rfl⟩ : syracuseStep 1989881 = 1492411) B1492411
theorem B2678113 : Blo 880569 2678113 := bstep (se 2 (by rfl) ⟨1004292, by rfl⟩ : syracuseStep 2678113 = 2008585) B2008585
theorem B1990025 : Blo 880569 1990025 := bstep (se 2 (by rfl) ⟨746259, by rfl⟩ : syracuseStep 1990025 = 1492519) B1492519
theorem B1990151 : Blo 880569 1990151 := bstep (se 1 (by rfl) ⟨1492613, by rfl⟩ : syracuseStep 1990151 = 2985227) B2985227
theorem B2514527 : Blo 880569 2514527 := bstep (se 1 (by rfl) ⟨1885895, by rfl⟩ : syracuseStep 2514527 = 3771791) B3771791
theorem B941743 : Blo 880569 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B2121527 : Blo 880569 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B17228161 : Blo 880569 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B27124253 : Blo 880569 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B1434539 : Blo 880569 1434539 := bstep (se 1 (by rfl) ⟨1075904, by rfl⟩ : syracuseStep 1434539 = 2151809) B2151809
theorem B10871783 : Blo 880569 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B5661733 : Blo 880569 5661733 := bstep (se 4 (by rfl) ⟨530787, by rfl⟩ : syracuseStep 5661733 = 1061575) B1061575
theorem B2385085 : Blo 880569 2385085 := bstep (se 3 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 2385085 = 894407) B894407
theorem B7529705 : Blo 880569 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B943687 : Blo 880569 943687 := bstep (se 1 (by rfl) ⟨707765, by rfl⟩ : syracuseStep 943687 = 1415531) B1415531
theorem B6711173 : Blo 880569 6711173 := bstep (se 4 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 6711173 = 1258345) B1258345
theorem B2975777 : Blo 880569 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B2123987 : Blo 880569 2123987 := bstep (se 1 (by rfl) ⟨1592990, by rfl⟩ : syracuseStep 2123987 = 3185981) B3185981
theorem B944507 : Blo 880569 944507 := bstep (se 1 (by rfl) ⟨708380, by rfl⟩ : syracuseStep 944507 = 1416761) B1416761
theorem B57273155 : Blo 880569 57273155 := bstep (se 1 (by rfl) ⟨42954866, by rfl⟩ : syracuseStep 57273155 = 85909733) B85909733
theorem B11332487 : Blo 880569 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B5663783 : Blo 880569 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B15068429 : Blo 880569 15068429 := bstep (se 3 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 15068429 = 5650661) B5650661
theorem B4844897 : Blo 880569 4844897 := bstep (se 2 (by rfl) ⟨1816836, by rfl⟩ : syracuseStep 4844897 = 3633673) B3633673
theorem B9531341 : Blo 880569 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B880591 : Blo 880569 880591 := bstep (se 1 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 880591 = 1320887) B1320887
theorem B880615 : Blo 880569 880615 := bstep (se 1 (by rfl) ⟨660461, by rfl⟩ : syracuseStep 880615 = 1320923) B1320923
theorem B6713603 : Blo 880569 6713603 := bstep (se 1 (by rfl) ⟨5035202, by rfl⟩ : syracuseStep 6713603 = 10070405) B10070405
theorem B880927 : Blo 880569 880927 := bstep (se 1 (by rfl) ⟨660695, by rfl⟩ : syracuseStep 880927 = 1321391) B1321391
theorem B880987 : Blo 880569 880987 := bstep (se 1 (by rfl) ⟨660740, by rfl⟩ : syracuseStep 880987 = 1321481) B1321481
theorem B881007 : Blo 880569 881007 := bstep (se 1 (by rfl) ⟨660755, by rfl⟩ : syracuseStep 881007 = 1321511) B1321511
theorem B881063 : Blo 880569 881063 := bstep (se 1 (by rfl) ⟨660797, by rfl⟩ : syracuseStep 881063 = 1321595) B1321595
theorem B881147 : Blo 880569 881147 := bstep (se 1 (by rfl) ⟨660860, by rfl⟩ : syracuseStep 881147 = 1321721) B1321721
theorem B881215 : Blo 880569 881215 := bstep (se 1 (by rfl) ⟨660911, by rfl⟩ : syracuseStep 881215 = 1321823) B1321823
theorem B1241663 : Blo 880569 1241663 := bstep (se 1 (by rfl) ⟨931247, by rfl⟩ : syracuseStep 1241663 = 1862495) B1862495
theorem B3174983 : Blo 880569 3174983 := bstep (se 1 (by rfl) ⟨2381237, by rfl⟩ : syracuseStep 3174983 = 4762475) B4762475
theorem B881223 : Blo 880569 881223 := bstep (se 1 (by rfl) ⟨660917, by rfl⟩ : syracuseStep 881223 = 1321835) B1321835
theorem B881375 : Blo 880569 881375 := bstep (se 1 (by rfl) ⟨661031, by rfl⟩ : syracuseStep 881375 = 1322063) B1322063
theorem B14480117 : Blo 880569 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B881455 : Blo 880569 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B2978639 : Blo 880569 2978639 := bstep (se 1 (by rfl) ⟨2233979, by rfl⟩ : syracuseStep 2978639 = 4467959) B4467959
theorem B881563 : Blo 880569 881563 := bstep (se 1 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 881563 = 1322345) B1322345
theorem B881615 : Blo 880569 881615 := bstep (se 1 (by rfl) ⟨661211, by rfl⟩ : syracuseStep 881615 = 1322423) B1322423
theorem B881639 : Blo 880569 881639 := bstep (se 1 (by rfl) ⟨661229, by rfl⟩ : syracuseStep 881639 = 1322459) B1322459
theorem B2978963 : Blo 880569 2978963 := bstep (se 1 (by rfl) ⟨2234222, by rfl⟩ : syracuseStep 2978963 = 4468445) B4468445
theorem B881951 : Blo 880569 881951 := bstep (se 1 (by rfl) ⟨661463, by rfl⟩ : syracuseStep 881951 = 1322927) B1322927
theorem B882011 : Blo 880569 882011 := bstep (se 1 (by rfl) ⟨661508, by rfl⟩ : syracuseStep 882011 = 1323017) B1323017
theorem B882031 : Blo 880569 882031 := bstep (se 1 (by rfl) ⟨661523, by rfl⟩ : syracuseStep 882031 = 1323047) B1323047
theorem B2979233 : Blo 880569 2979233 := bstep (se 2 (by rfl) ⟨1117212, by rfl⟩ : syracuseStep 2979233 = 2234425) B2234425
theorem B882087 : Blo 880569 882087 := bstep (se 1 (by rfl) ⟨661565, by rfl⟩ : syracuseStep 882087 = 1323131) B1323131
theorem B4781501 : Blo 880569 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B882171 : Blo 880569 882171 := bstep (se 1 (by rfl) ⟨661628, by rfl⟩ : syracuseStep 882171 = 1323257) B1323257
theorem B882239 : Blo 880569 882239 := bstep (se 1 (by rfl) ⟨661679, by rfl⟩ : syracuseStep 882239 = 1323359) B1323359
theorem B882247 : Blo 880569 882247 := bstep (se 1 (by rfl) ⟨661685, by rfl⟩ : syracuseStep 882247 = 1323371) B1323371
theorem B2389691 : Blo 880569 2389691 := bstep (se 1 (by rfl) ⟨1792268, by rfl⟩ : syracuseStep 2389691 = 3584537) B3584537
theorem B882399 : Blo 880569 882399 := bstep (se 1 (by rfl) ⟨661799, by rfl⟩ : syracuseStep 882399 = 1323599) B1323599
theorem B882479 : Blo 880569 882479 := bstep (se 1 (by rfl) ⟨661859, by rfl⟩ : syracuseStep 882479 = 1323719) B1323719
theorem B882587 : Blo 880569 882587 := bstep (se 1 (by rfl) ⟨661940, by rfl⟩ : syracuseStep 882587 = 1323881) B1323881
theorem B882639 : Blo 880569 882639 := bstep (se 1 (by rfl) ⟨661979, by rfl⟩ : syracuseStep 882639 = 1323959) B1323959
theorem B882663 : Blo 880569 882663 := bstep (se 1 (by rfl) ⟨661997, by rfl⟩ : syracuseStep 882663 = 1323995) B1323995
theorem B18086125 : Blo 880569 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B5372183 : Blo 880569 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B882975 : Blo 880569 882975 := bstep (se 1 (by rfl) ⟨662231, by rfl⟩ : syracuseStep 882975 = 1324463) B1324463
theorem B883035 : Blo 880569 883035 := bstep (se 1 (by rfl) ⟨662276, by rfl⟩ : syracuseStep 883035 = 1324553) B1324553
theorem B883055 : Blo 880569 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B883111 : Blo 880569 883111 := bstep (se 1 (by rfl) ⟨662333, by rfl⟩ : syracuseStep 883111 = 1324667) B1324667
theorem B883195 : Blo 880569 883195 := bstep (se 1 (by rfl) ⟨662396, by rfl⟩ : syracuseStep 883195 = 1324793) B1324793
theorem B883263 : Blo 880569 883263 := bstep (se 1 (by rfl) ⟨662447, by rfl⟩ : syracuseStep 883263 = 1324895) B1324895
theorem B883271 : Blo 880569 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B883423 : Blo 880569 883423 := bstep (se 1 (by rfl) ⟨662567, by rfl⟩ : syracuseStep 883423 = 1325135) B1325135
theorem B883503 : Blo 880569 883503 := bstep (se 1 (by rfl) ⟨662627, by rfl⟩ : syracuseStep 883503 = 1325255) B1325255
theorem B883611 : Blo 880569 883611 := bstep (se 1 (by rfl) ⟨662708, by rfl⟩ : syracuseStep 883611 = 1325417) B1325417
theorem B883663 : Blo 880569 883663 := bstep (se 1 (by rfl) ⟨662747, by rfl⟩ : syracuseStep 883663 = 1325495) B1325495
theorem B883687 : Blo 880569 883687 := bstep (se 1 (by rfl) ⟨662765, by rfl⟩ : syracuseStep 883687 = 1325531) B1325531
theorem B883999 : Blo 880569 883999 := bstep (se 1 (by rfl) ⟨662999, by rfl⟩ : syracuseStep 883999 = 1325999) B1325999
theorem B884059 : Blo 880569 884059 := bstep (se 1 (by rfl) ⟨663044, by rfl⟩ : syracuseStep 884059 = 1326089) B1326089
theorem B884079 : Blo 880569 884079 := bstep (se 1 (by rfl) ⟨663059, by rfl⟩ : syracuseStep 884079 = 1326119) B1326119
theorem B884135 : Blo 880569 884135 := bstep (se 1 (by rfl) ⟨663101, by rfl⟩ : syracuseStep 884135 = 1326203) B1326203
theorem B884219 : Blo 880569 884219 := bstep (se 1 (by rfl) ⟨663164, by rfl⟩ : syracuseStep 884219 = 1326329) B1326329
theorem B884287 : Blo 880569 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B884295 : Blo 880569 884295 := bstep (se 1 (by rfl) ⟨663221, by rfl⟩ : syracuseStep 884295 = 1326443) B1326443
theorem B884447 : Blo 880569 884447 := bstep (se 1 (by rfl) ⟨663335, by rfl⟩ : syracuseStep 884447 = 1326671) B1326671
theorem B884527 : Blo 880569 884527 := bstep (se 1 (by rfl) ⟨663395, by rfl⟩ : syracuseStep 884527 = 1326791) B1326791
theorem B22970881 : Blo 880569 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B6783527 : Blo 880569 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B2982473 : Blo 880569 2982473 := bstep (se 2 (by rfl) ⟨1118427, by rfl⟩ : syracuseStep 2982473 = 2236855) B2236855
theorem B2982635 : Blo 880569 2982635 := bstep (se 1 (by rfl) ⟨2236976, by rfl⟩ : syracuseStep 2982635 = 4473953) B4473953
theorem B2950031 : Blo 880569 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B2229353 : Blo 880569 2229353 := bstep (se 2 (by rfl) ⟨836007, by rfl⟩ : syracuseStep 2229353 = 1672015) B1672015
theorem B11306243 : Blo 880569 11306243 := bstep (se 1 (by rfl) ⟨8479682, by rfl⟩ : syracuseStep 11306243 = 16959365) B16959365
theorem B5375393 : Blo 880569 5375393 := bstep (se 2 (by rfl) ⟨2015772, by rfl⟩ : syracuseStep 5375393 = 4031545) B4031545
theorem B3343787 : Blo 880569 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B3311101 : Blo 880569 3311101 := bstep (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) B1241663
theorem B3180113 : Blo 880569 3180113 := bstep (se 2 (by rfl) ⟨1192542, by rfl⟩ : syracuseStep 3180113 = 2385085) B2385085
theorem B5015155 : Blo 880569 5015155 := bstep (se 1 (by rfl) ⟨3761366, by rfl⟩ : syracuseStep 5015155 = 7522733) B7522733
theorem B1509257 : Blo 880569 1509257 := bstep (se 2 (by rfl) ⟨565971, by rfl⟩ : syracuseStep 1509257 = 1131943) B1131943
theorem B1673207 : Blo 880569 1673207 := bstep (se 1 (by rfl) ⟨1254905, by rfl⟩ : syracuseStep 1673207 = 2509811) B2509811
theorem B2984147 : Blo 880569 2984147 := bstep (se 1 (by rfl) ⟨2238110, by rfl⟩ : syracuseStep 2984147 = 4476221) B4476221
theorem B2230487 : Blo 880569 2230487 := bstep (se 1 (by rfl) ⟨1672865, by rfl⟩ : syracuseStep 2230487 = 3345731) B3345731
theorem B2984417 : Blo 880569 2984417 := bstep (se 2 (by rfl) ⟨1119156, by rfl⟩ : syracuseStep 2984417 = 2238313) B2238313
theorem B2230811 : Blo 880569 2230811 := bstep (se 1 (by rfl) ⟨1673108, by rfl⟩ : syracuseStep 2230811 = 3346217) B3346217
theorem B1411615 : Blo 880569 1411615 := bstep (se 1 (by rfl) ⟨1058711, by rfl⟩ : syracuseStep 1411615 = 2117423) B2117423
theorem B10750495 : Blo 880569 10750495 := bstep (se 1 (by rfl) ⟨8062871, by rfl⟩ : syracuseStep 10750495 = 16125743) B16125743
theorem B5016613 : Blo 880569 5016613 := bstep (se 4 (by rfl) ⟨470307, by rfl⟩ : syracuseStep 5016613 = 940615) B940615
theorem B1674361 : Blo 880569 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B1674665 : Blo 880569 1674665 := bstep (se 2 (by rfl) ⟨627999, by rfl⟩ : syracuseStep 1674665 = 1255999) B1255999
theorem B3182075 : Blo 880569 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B921179 : Blo 880569 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B8064845 : Blo 880569 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B8491027 : Blo 880569 8491027 := bstep (se 1 (by rfl) ⟨6368270, by rfl⟩ : syracuseStep 8491027 = 12736541) B12736541
theorem B5018071 : Blo 880569 5018071 := bstep (se 1 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 5018071 = 7527107) B7527107
theorem B2233129 : Blo 880569 2233129 := bstep (se 2 (by rfl) ⟨837423, by rfl⟩ : syracuseStep 2233129 = 1674847) B1674847
theorem B1676351 : Blo 880569 1676351 := bstep (se 1 (by rfl) ⟨1257263, by rfl⟩ : syracuseStep 1676351 = 2514527) B2514527
theorem B1414351 : Blo 880569 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B3347675 : Blo 880569 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B956359 : Blo 880569 956359 := bstep (se 1 (by rfl) ⟨717269, by rfl⟩ : syracuseStep 956359 = 1434539) B1434539
theorem B7247855 : Blo 880569 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B14325821 : Blo 880569 14325821 := bstep (se 3 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 14325821 = 5372183) B5372183
theorem B5019803 : Blo 880569 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B2234567 : Blo 880569 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B6691247 : Blo 880569 6691247 := bstep (se 1 (by rfl) ⟨5018435, by rfl⟩ : syracuseStep 6691247 = 10036871) B10036871
theorem B4463261 : Blo 880569 4463261 := bstep (se 3 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 4463261 = 1673723) B1673723
theorem B5643179 : Blo 880569 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B4463585 : Blo 880569 4463585 := bstep (se 2 (by rfl) ⟨1673844, by rfl⟩ : syracuseStep 4463585 = 3347689) B3347689
theorem B10722469 : Blo 880569 10722469 := bstep (se 4 (by rfl) ⟨1005231, by rfl⟩ : syracuseStep 10722469 = 2010463) B2010463
theorem B38182103 : Blo 880569 38182103 := bstep (se 1 (by rfl) ⟨28636577, by rfl⟩ : syracuseStep 38182103 = 57273155) B57273155
theorem B8592655 : Blo 880569 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B2235995 : Blo 880569 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B5644079 : Blo 880569 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B10887211 : Blo 880569 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B991615 : Blo 880569 991615 := bstep (se 1 (by rfl) ⟨743711, by rfl⟩ : syracuseStep 991615 = 1487423) B1487423
theorem B1253983 : Blo 880569 1253983 := bstep (se 1 (by rfl) ⟨940487, by rfl⟩ : syracuseStep 1253983 = 1880975) B1880975
theorem B4235885 : Blo 880569 4235885 := bstep (se 3 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 4235885 = 1588457) B1588457
theorem B6366107 : Blo 880569 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B3187667 : Blo 880569 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B3351577 : Blo 880569 3351577 := bstep (se 2 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 3351577 = 2513683) B2513683
theorem B1254575 : Blo 880569 1254575 := bstep (se 1 (by rfl) ⟨940931, by rfl⟩ : syracuseStep 1254575 = 1881863) B1881863
theorem B4465853 : Blo 880569 4465853 := bstep (se 3 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 4465853 = 1674695) B1674695
theorem B993019 : Blo 880569 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B993055 : Blo 880569 993055 := bstep (se 1 (by rfl) ⟨744791, by rfl⟩ : syracuseStep 993055 = 1489583) B1489583
theorem B1320935 : Blo 880569 1320935 := bstep (se 1 (by rfl) ⟨990701, by rfl⟩ : syracuseStep 1320935 = 1981403) B1981403
theorem B2238455 : Blo 880569 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B1320953 : Blo 880569 1320953 := bstep (se 2 (by rfl) ⟨495357, by rfl⟩ : syracuseStep 1320953 = 990715) B990715
theorem B1321055 : Blo 880569 1321055 := bstep (se 1 (by rfl) ⟨990791, by rfl⟩ : syracuseStep 1321055 = 1981583) B1981583
theorem B1321115 : Blo 880569 1321115 := bstep (se 1 (by rfl) ⟨990836, by rfl⟩ : syracuseStep 1321115 = 1981673) B1981673
theorem B1321151 : Blo 880569 1321151 := bstep (se 1 (by rfl) ⟨990863, by rfl⟩ : syracuseStep 1321151 = 1981727) B1981727
theorem B1321193 : Blo 880569 1321193 := bstep (se 2 (by rfl) ⟨495447, by rfl⟩ : syracuseStep 1321193 = 990895) B990895
theorem B1255657 : Blo 880569 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B1321499 : Blo 880569 1321499 := bstep (se 1 (by rfl) ⟨991124, by rfl⟩ : syracuseStep 1321499 = 1982249) B1982249
theorem B1321577 : Blo 880569 1321577 := bstep (se 2 (by rfl) ⟨495591, by rfl⟩ : syracuseStep 1321577 = 991183) B991183
theorem B994207 : Blo 880569 994207 := bstep (se 1 (by rfl) ⟨745655, by rfl⟩ : syracuseStep 994207 = 1491311) B1491311
theorem B4303811 : Blo 880569 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B994351 : Blo 880569 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B1322105 : Blo 880569 1322105 := bstep (se 2 (by rfl) ⟨495789, by rfl⟩ : syracuseStep 1322105 = 991579) B991579
theorem B1322207 : Blo 880569 1322207 := bstep (se 1 (by rfl) ⟨991655, by rfl⟩ : syracuseStep 1322207 = 1983311) B1983311
theorem B1256671 : Blo 880569 1256671 := bstep (se 1 (by rfl) ⟨942503, by rfl⟩ : syracuseStep 1256671 = 1885007) B1885007
theorem B1322249 : Blo 880569 1322249 := bstep (se 2 (by rfl) ⟨495843, by rfl⟩ : syracuseStep 1322249 = 991687) B991687
theorem B994639 : Blo 880569 994639 := bstep (se 1 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 994639 = 1491959) B1491959
theorem B1322351 : Blo 880569 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B1322471 : Blo 880569 1322471 := bstep (se 1 (by rfl) ⟨991853, by rfl⟩ : syracuseStep 1322471 = 1983707) B1983707
theorem B1322603 : Blo 880569 1322603 := bstep (se 1 (by rfl) ⟨991952, by rfl⟩ : syracuseStep 1322603 = 1983905) B1983905
theorem B1322729 : Blo 880569 1322729 := bstep (se 2 (by rfl) ⟨496023, by rfl⟩ : syracuseStep 1322729 = 992047) B992047
theorem B2830099 : Blo 880569 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B1322873 : Blo 880569 1322873 := bstep (se 2 (by rfl) ⟨496077, by rfl⟩ : syracuseStep 1322873 = 992155) B992155
theorem B32157647 : Blo 880569 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B1322975 : Blo 880569 1322975 := bstep (se 1 (by rfl) ⟨992231, by rfl⟩ : syracuseStep 1322975 = 1984463) B1984463
theorem B7548977 : Blo 880569 7548977 := bstep (se 2 (by rfl) ⟨2830866, by rfl⟩ : syracuseStep 7548977 = 5661733) B5661733
theorem B4763771 : Blo 880569 4763771 := bstep (se 1 (by rfl) ⟨3572828, by rfl⟩ : syracuseStep 4763771 = 7145657) B7145657
theorem B4468931 : Blo 880569 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1323227 : Blo 880569 1323227 := bstep (se 1 (by rfl) ⟨992420, by rfl⟩ : syracuseStep 1323227 = 1984841) B1984841
theorem B1323239 : Blo 880569 1323239 := bstep (se 1 (by rfl) ⟨992429, by rfl⟩ : syracuseStep 1323239 = 1984859) B1984859
theorem B1061095 : Blo 880569 1061095 := bstep (se 1 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 1061095 = 1591643) B1591643
theorem B1323401 : Blo 880569 1323401 := bstep (se 2 (by rfl) ⟨496275, by rfl⟩ : syracuseStep 1323401 = 992551) B992551
theorem B1257935 : Blo 880569 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B1323497 : Blo 880569 1323497 := bstep (se 2 (by rfl) ⟨496311, by rfl⟩ : syracuseStep 1323497 = 992623) B992623
theorem B5026319 : Blo 880569 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1323623 : Blo 880569 1323623 := bstep (se 1 (by rfl) ⟨992717, by rfl⟩ : syracuseStep 1323623 = 1985435) B1985435
theorem B1323755 : Blo 880569 1323755 := bstep (se 1 (by rfl) ⟨992816, by rfl⟩ : syracuseStep 1323755 = 1985633) B1985633
theorem B1323785 : Blo 880569 1323785 := bstep (se 2 (by rfl) ⟨496419, by rfl⟩ : syracuseStep 1323785 = 992839) B992839
theorem B1258249 : Blo 880569 1258249 := bstep (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) B943687
theorem B1323887 : Blo 880569 1323887 := bstep (se 1 (by rfl) ⟨992915, by rfl⟩ : syracuseStep 1323887 = 1985831) B1985831
theorem B8500139 : Blo 880569 8500139 := bstep (se 1 (by rfl) ⟨6375104, by rfl⟩ : syracuseStep 8500139 = 12750209) B12750209
theorem B1324139 : Blo 880569 1324139 := bstep (se 1 (by rfl) ⟨993104, by rfl⟩ : syracuseStep 1324139 = 1986209) B1986209
theorem B1881299 : Blo 880569 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B1324379 : Blo 880569 1324379 := bstep (se 1 (by rfl) ⟨993284, by rfl⟩ : syracuseStep 1324379 = 1986569) B1986569
theorem B1324655 : Blo 880569 1324655 := bstep (se 1 (by rfl) ⟨993491, by rfl⟩ : syracuseStep 1324655 = 1986983) B1986983
theorem B1324727 : Blo 880569 1324727 := bstep (se 1 (by rfl) ⟨993545, by rfl⟩ : syracuseStep 1324727 = 1987091) B1987091
theorem B1324763 : Blo 880569 1324763 := bstep (se 1 (by rfl) ⟨993572, by rfl⟩ : syracuseStep 1324763 = 1987145) B1987145
theorem B1488719 : Blo 880569 1488719 := bstep (se 1 (by rfl) ⟨1116539, by rfl⟩ : syracuseStep 1488719 = 2233079) B2233079
theorem B1324937 : Blo 880569 1324937 := bstep (se 2 (by rfl) ⟨496851, by rfl⟩ : syracuseStep 1324937 = 993703) B993703
theorem B1325039 : Blo 880569 1325039 := bstep (se 1 (by rfl) ⟨993779, by rfl⟩ : syracuseStep 1325039 = 1987559) B1987559
theorem B1882273 : Blo 880569 1882273 := bstep (se 2 (by rfl) ⟨705852, by rfl⟩ : syracuseStep 1882273 = 1411705) B1411705
theorem B1325291 : Blo 880569 1325291 := bstep (se 1 (by rfl) ⟨993968, by rfl⟩ : syracuseStep 1325291 = 1987937) B1987937
theorem B1325351 : Blo 880569 1325351 := bstep (se 1 (by rfl) ⟨994013, by rfl⟩ : syracuseStep 1325351 = 1988027) B1988027
theorem B1325435 : Blo 880569 1325435 := bstep (se 1 (by rfl) ⟨994076, by rfl⟩ : syracuseStep 1325435 = 1988153) B1988153
theorem B2832815 : Blo 880569 2832815 := bstep (se 1 (by rfl) ⟨2124611, by rfl⟩ : syracuseStep 2832815 = 4249223) B4249223
theorem B1325705 : Blo 880569 1325705 := bstep (se 2 (by rfl) ⟨497139, by rfl⟩ : syracuseStep 1325705 = 994279) B994279
theorem B5028551 : Blo 880569 5028551 := bstep (se 1 (by rfl) ⟨3771413, by rfl⟩ : syracuseStep 5028551 = 7542827) B7542827
theorem B4831967 : Blo 880569 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B1325879 : Blo 880569 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B9681731 : Blo 880569 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B1325915 : Blo 880569 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B1326059 : Blo 880569 1326059 := bstep (se 1 (by rfl) ⟨994544, by rfl⟩ : syracuseStep 1326059 = 1989089) B1989089
theorem B1489961 : Blo 880569 1489961 := bstep (se 2 (by rfl) ⟨558735, by rfl⟩ : syracuseStep 1489961 = 1117471) B1117471
theorem B1981511 : Blo 880569 1981511 := bstep (se 1 (by rfl) ⟨1486133, by rfl⟩ : syracuseStep 1981511 = 2972267) B2972267
theorem B1326263 : Blo 880569 1326263 := bstep (se 1 (by rfl) ⟨994697, by rfl⟩ : syracuseStep 1326263 = 1989395) B1989395
theorem B1490143 : Blo 880569 1490143 := bstep (se 1 (by rfl) ⟨1117607, by rfl⟩ : syracuseStep 1490143 = 2235215) B2235215
theorem B1883503 : Blo 880569 1883503 := bstep (se 1 (by rfl) ⟨1412627, by rfl⟩ : syracuseStep 1883503 = 2825255) B2825255
theorem B1326503 : Blo 880569 1326503 := bstep (se 1 (by rfl) ⟨994877, by rfl⟩ : syracuseStep 1326503 = 1989755) B1989755
theorem B1981907 : Blo 880569 1981907 := bstep (se 1 (by rfl) ⟨1486430, by rfl⟩ : syracuseStep 1981907 = 2972861) B2972861
theorem B1326587 : Blo 880569 1326587 := bstep (se 1 (by rfl) ⟨994940, by rfl⟩ : syracuseStep 1326587 = 1989881) B1989881
theorem B1326683 : Blo 880569 1326683 := bstep (se 1 (by rfl) ⟨995012, by rfl⟩ : syracuseStep 1326683 = 1990025) B1990025
theorem B1490575 : Blo 880569 1490575 := bstep (se 1 (by rfl) ⟨1117931, by rfl⟩ : syracuseStep 1490575 = 2235863) B2235863
theorem B1326767 : Blo 880569 1326767 := bstep (se 1 (by rfl) ⟨995075, by rfl⟩ : syracuseStep 1326767 = 1990151) B1990151
theorem B1982177 : Blo 880569 1982177 := bstep (se 2 (by rfl) ⟨743316, by rfl⟩ : syracuseStep 1982177 = 1486633) B1486633
theorem B15318845 : Blo 880569 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B27181403 : Blo 880569 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B1492175 : Blo 880569 1492175 := bstep (se 1 (by rfl) ⟨1119131, by rfl⟩ : syracuseStep 1492175 = 2238263) B2238263
theorem B4474115 : Blo 880569 4474115 := bstep (se 1 (by rfl) ⟨3355586, by rfl⟩ : syracuseStep 4474115 = 6711173) B6711173
theorem B1983851 : Blo 880569 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B1984121 : Blo 880569 1984121 := bstep (se 2 (by rfl) ⟨744045, by rfl⟩ : syracuseStep 1984121 = 1488091) B1488091
theorem B4245377 : Blo 880569 4245377 := bstep (se 2 (by rfl) ⟨1592016, by rfl⟩ : syracuseStep 4245377 = 3184033) B3184033
theorem B7554991 : Blo 880569 7554991 := bstep (se 1 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 7554991 = 11332487) B11332487
theorem B10045619 : Blo 880569 10045619 := bstep (se 1 (by rfl) ⟨7534214, by rfl⟩ : syracuseStep 10045619 = 15068429) B15068429
theorem B33933491 : Blo 880569 33933491 := bstep (se 1 (by rfl) ⟨25450118, by rfl⟩ : syracuseStep 33933491 = 50900237) B50900237
theorem B3229931 : Blo 880569 3229931 := bstep (se 1 (by rfl) ⟨2422448, by rfl⟩ : syracuseStep 3229931 = 4844897) B4844897
theorem B1985129 : Blo 880569 1985129 := bstep (se 2 (by rfl) ⟨744423, by rfl⟩ : syracuseStep 1985129 = 1488847) B1488847
theorem B4475735 : Blo 880569 4475735 := bstep (se 1 (by rfl) ⟨3356801, by rfl⟩ : syracuseStep 4475735 = 6713603) B6713603
theorem B5721005 : Blo 880569 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B2116655 : Blo 880569 2116655 := bstep (se 1 (by rfl) ⟨1587491, by rfl⟩ : syracuseStep 2116655 = 3174983) B3174983
theorem B9653411 : Blo 880569 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B1985759 : Blo 880569 1985759 := bstep (se 1 (by rfl) ⟨1489319, by rfl⟩ : syracuseStep 1985759 = 2978639) B2978639
theorem B1985975 : Blo 880569 1985975 := bstep (se 1 (by rfl) ⟨1489481, by rfl⟩ : syracuseStep 1985975 = 2978963) B2978963
theorem B22957577 : Blo 880569 22957577 := bstep (se 2 (by rfl) ⟨8609091, by rfl⟩ : syracuseStep 22957577 = 17218183) B17218183
theorem B1986155 : Blo 880569 1986155 := bstep (se 1 (by rfl) ⟨1489616, by rfl⟩ : syracuseStep 1986155 = 2979233) B2979233
theorem B4247147 : Blo 880569 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B1593127 : Blo 880569 1593127 := bstep (se 1 (by rfl) ⟨1194845, by rfl⟩ : syracuseStep 1593127 = 2389691) B2389691
theorem B1986425 : Blo 880569 1986425 := bstep (se 2 (by rfl) ⟨744909, by rfl⟩ : syracuseStep 1986425 = 1489819) B1489819
theorem B4247417 : Blo 880569 4247417 := bstep (se 2 (by rfl) ⟨1592781, by rfl⟩ : syracuseStep 4247417 = 3185563) B3185563
theorem B16961825 : Blo 880569 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B16962371 : Blo 880569 16962371 := bstep (se 1 (by rfl) ⟨12721778, by rfl⟩ : syracuseStep 16962371 = 25443557) B25443557
theorem B11326337 : Blo 880569 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B6116705 : Blo 880569 6116705 := bstep (se 2 (by rfl) ⟨2293764, by rfl⟩ : syracuseStep 6116705 = 4587529) B4587529
theorem B2512225 : Blo 880569 2512225 := bstep (se 2 (by rfl) ⟨942084, by rfl⟩ : syracuseStep 2512225 = 1884169) B1884169
theorem B9164411 : Blo 880569 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B1988279 : Blo 880569 1988279 := bstep (se 1 (by rfl) ⟨1491209, by rfl⟩ : syracuseStep 1988279 = 2982419) B2982419
theorem B21452525 : Blo 880569 21452525 := bstep (se 3 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 21452525 = 8044697) B8044697
theorem B11327363 : Blo 880569 11327363 := bstep (se 1 (by rfl) ⟨8495522, by rfl⟩ : syracuseStep 11327363 = 16991045) B16991045
theorem B3824047 : Blo 880569 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B5364157 : Blo 880569 5364157 := bstep (se 3 (by rfl) ⟨1005779, by rfl⟩ : syracuseStep 5364157 = 2011559) B2011559
theorem B5036843 : Blo 880569 5036843 := bstep (se 1 (by rfl) ⟨3777632, by rfl⟩ : syracuseStep 5036843 = 7555265) B7555265
theorem B8477531 : Blo 880569 8477531 := bstep (se 1 (by rfl) ⟨6358148, by rfl⟩ : syracuseStep 8477531 = 12716297) B12716297
theorem B1989467 : Blo 880569 1989467 := bstep (se 1 (by rfl) ⟨1492100, by rfl⟩ : syracuseStep 1989467 = 2984201) B2984201
theorem B5037025 : Blo 880569 5037025 := bstep (se 2 (by rfl) ⟨1888884, by rfl⟩ : syracuseStep 5037025 = 3777769) B3777769
theorem B2513911 : Blo 880569 2513911 := bstep (se 1 (by rfl) ⟨1885433, by rfl⟩ : syracuseStep 2513911 = 3770867) B3770867
theorem B2514185 : Blo 880569 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B2973023 : Blo 880569 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B1990223 : Blo 880569 1990223 := bstep (se 1 (by rfl) ⟨1492667, by rfl⟩ : syracuseStep 1990223 = 2985335) B2985335
theorem B10182493 : Blo 880569 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B2973563 : Blo 880569 2973563 := bstep (se 1 (by rfl) ⟨2230172, by rfl⟩ : syracuseStep 2973563 = 4460345) B4460345
theorem B50782139 : Blo 880569 50782139 := bstep (se 1 (by rfl) ⟨38086604, by rfl⟩ : syracuseStep 50782139 = 76173209) B76173209
theorem B2121767 : Blo 880569 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B2974049 : Blo 880569 2974049 := bstep (se 2 (by rfl) ⟨1115268, by rfl⟩ : syracuseStep 2974049 = 2230537) B2230537
theorem B7529021 : Blo 880569 7529021 := bstep (se 3 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 7529021 = 2823383) B2823383
theorem B2515529 : Blo 880569 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B7168621 : Blo 880569 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B5661323 : Blo 880569 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B2515769 : Blo 880569 2515769 := bstep (se 2 (by rfl) ⟨943413, by rfl⟩ : syracuseStep 2515769 = 1886827) B1886827
theorem B28959947 : Blo 880569 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B2975399 : Blo 880569 2975399 := bstep (se 1 (by rfl) ⟨2231549, by rfl⟩ : syracuseStep 2975399 = 4463099) B4463099
theorem B1631963 : Blo 880569 1631963 := bstep (se 1 (by rfl) ⟨1223972, by rfl⟩ : syracuseStep 1631963 = 2447945) B2447945
theorem B1075435 : Blo 880569 1075435 := bstep (se 1 (by rfl) ⟨806576, by rfl⟩ : syracuseStep 1075435 = 1613153) B1613153
theorem B2517227 : Blo 880569 2517227 := bstep (se 1 (by rfl) ⟨1887920, by rfl⟩ : syracuseStep 2517227 = 3775841) B3775841
theorem B2975993 : Blo 880569 2975993 := bstep (se 2 (by rfl) ⟨1115997, by rfl⟩ : syracuseStep 2975993 = 2231995) B2231995
theorem B2976047 : Blo 880569 2976047 := bstep (se 1 (by rfl) ⟨2232035, by rfl⟩ : syracuseStep 2976047 = 4464071) B4464071
theorem B2976263 : Blo 880569 2976263 := bstep (se 1 (by rfl) ⟨2232197, by rfl⟩ : syracuseStep 2976263 = 4464395) B4464395
theorem B4025015 : Blo 880569 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B18082835 : Blo 880569 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B9071635 : Blo 880569 9071635 := bstep (se 1 (by rfl) ⟨6803726, by rfl⟩ : syracuseStep 9071635 = 13607453) B13607453
theorem B2387065 : Blo 880569 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B2976911 : Blo 880569 2976911 := bstep (se 1 (by rfl) ⟨2232683, by rfl⟩ : syracuseStep 2976911 = 4465367) B4465367
theorem B5663965 : Blo 880569 5663965 := bstep (se 3 (by rfl) ⟨1061993, by rfl⟩ : syracuseStep 5663965 = 2123987) B2123987
theorem B2977343 : Blo 880569 2977343 := bstep (se 1 (by rfl) ⟨2233007, by rfl⟩ : syracuseStep 2977343 = 4466015) B4466015
theorem B2518685 : Blo 880569 2518685 := bstep (se 3 (by rfl) ⟨472253, by rfl⟩ : syracuseStep 2518685 = 944507) B944507
theorem B880607 : Blo 880569 880607 := bstep (se 1 (by rfl) ⟨660455, by rfl⟩ : syracuseStep 880607 = 1320911) B1320911
theorem B880871 : Blo 880569 880871 := bstep (se 1 (by rfl) ⟨660653, by rfl⟩ : syracuseStep 880871 = 1321307) B1321307
theorem B2978045 : Blo 880569 2978045 := bstep (se 3 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 2978045 = 1116767) B1116767
theorem B2584829 : Blo 880569 2584829 := bstep (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) B969311
theorem B881023 : Blo 880569 881023 := bstep (se 1 (by rfl) ⟨660767, by rfl⟩ : syracuseStep 881023 = 1321535) B1321535
theorem B3764647 : Blo 880569 3764647 := bstep (se 1 (by rfl) ⟨2823485, by rfl⟩ : syracuseStep 3764647 = 5646971) B5646971
theorem B881103 : Blo 880569 881103 := bstep (se 1 (by rfl) ⟨660827, by rfl⟩ : syracuseStep 881103 = 1321655) B1321655
theorem B3764819 : Blo 880569 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B881255 : Blo 880569 881255 := bstep (se 1 (by rfl) ⟨660941, by rfl⟩ : syracuseStep 881255 = 1321883) B1321883
theorem B2978585 : Blo 880569 2978585 := bstep (se 2 (by rfl) ⟨1116969, by rfl⟩ : syracuseStep 2978585 = 2233939) B2233939
theorem B1340201 : Blo 880569 1340201 := bstep (se 2 (by rfl) ⟨502575, by rfl⟩ : syracuseStep 1340201 = 1005151) B1005151
theorem B881519 : Blo 880569 881519 := bstep (se 1 (by rfl) ⟨661139, by rfl⟩ : syracuseStep 881519 = 1322279) B1322279
theorem B881575 : Blo 880569 881575 := bstep (se 1 (by rfl) ⟨661181, by rfl⟩ : syracuseStep 881575 = 1322363) B1322363
theorem B881659 : Blo 880569 881659 := bstep (se 1 (by rfl) ⟨661244, by rfl⟩ : syracuseStep 881659 = 1322489) B1322489
theorem B2978855 : Blo 880569 2978855 := bstep (se 1 (by rfl) ⟨2234141, by rfl⟩ : syracuseStep 2978855 = 4468283) B4468283
theorem B881727 : Blo 880569 881727 := bstep (se 1 (by rfl) ⟨661295, by rfl⟩ : syracuseStep 881727 = 1322591) B1322591
theorem B881871 : Blo 880569 881871 := bstep (se 1 (by rfl) ⟨661403, by rfl⟩ : syracuseStep 881871 = 1322807) B1322807
theorem B6354227 : Blo 880569 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B9532723 : Blo 880569 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B882075 : Blo 880569 882075 := bstep (se 1 (by rfl) ⟨661556, by rfl⟩ : syracuseStep 882075 = 1323113) B1323113
theorem B15103421 : Blo 880569 15103421 := bstep (se 3 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 15103421 = 5663783) B5663783
theorem B882287 : Blo 880569 882287 := bstep (se 1 (by rfl) ⟨661715, by rfl⟩ : syracuseStep 882287 = 1323431) B1323431
theorem B14317195 : Blo 880569 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B24114833 : Blo 880569 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B882343 : Blo 880569 882343 := bstep (se 1 (by rfl) ⟨661757, by rfl⟩ : syracuseStep 882343 = 1323515) B1323515
theorem B882427 : Blo 880569 882427 := bstep (se 1 (by rfl) ⟨661820, by rfl⟩ : syracuseStep 882427 = 1323641) B1323641
theorem B882463 : Blo 880569 882463 := bstep (se 1 (by rfl) ⟨661847, by rfl⟩ : syracuseStep 882463 = 1323695) B1323695
theorem B882495 : Blo 880569 882495 := bstep (se 1 (by rfl) ⟨661871, by rfl⟩ : syracuseStep 882495 = 1323743) B1323743
theorem B882671 : Blo 880569 882671 := bstep (se 1 (by rfl) ⟨662003, by rfl⟩ : syracuseStep 882671 = 1324007) B1324007
theorem B2979935 : Blo 880569 2979935 := bstep (se 1 (by rfl) ⟨2234951, by rfl⟩ : syracuseStep 2979935 = 4469903) B4469903
theorem B882843 : Blo 880569 882843 := bstep (se 1 (by rfl) ⟨662132, by rfl⟩ : syracuseStep 882843 = 1324265) B1324265
theorem B882879 : Blo 880569 882879 := bstep (se 1 (by rfl) ⟨662159, by rfl⟩ : syracuseStep 882879 = 1324319) B1324319
theorem B882991 : Blo 880569 882991 := bstep (se 1 (by rfl) ⟨662243, by rfl⟩ : syracuseStep 882991 = 1324487) B1324487
theorem B6388079 : Blo 880569 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B883227 : Blo 880569 883227 := bstep (se 1 (by rfl) ⟨662420, by rfl⟩ : syracuseStep 883227 = 1324841) B1324841
theorem B883231 : Blo 880569 883231 := bstep (se 1 (by rfl) ⟨662423, by rfl⟩ : syracuseStep 883231 = 1324847) B1324847
theorem B2980691 : Blo 880569 2980691 := bstep (se 1 (by rfl) ⟨2235518, by rfl⟩ : syracuseStep 2980691 = 4471037) B4471037
theorem B883547 : Blo 880569 883547 := bstep (se 1 (by rfl) ⟨662660, by rfl⟩ : syracuseStep 883547 = 1325321) B1325321
theorem B883615 : Blo 880569 883615 := bstep (se 1 (by rfl) ⟨662711, by rfl⟩ : syracuseStep 883615 = 1325423) B1325423
theorem B13564837 : Blo 880569 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B883759 : Blo 880569 883759 := bstep (se 1 (by rfl) ⟨662819, by rfl⟩ : syracuseStep 883759 = 1325639) B1325639
theorem B883783 : Blo 880569 883783 := bstep (se 1 (by rfl) ⟨662837, by rfl⟩ : syracuseStep 883783 = 1325675) B1325675
theorem B3570817 : Blo 880569 3570817 := bstep (se 2 (by rfl) ⟨1339056, by rfl⟩ : syracuseStep 3570817 = 2678113) B2678113
theorem B883935 : Blo 880569 883935 := bstep (se 1 (by rfl) ⟨662951, by rfl⟩ : syracuseStep 883935 = 1325903) B1325903
theorem B2981231 : Blo 880569 2981231 := bstep (se 1 (by rfl) ⟨2235923, by rfl⟩ : syracuseStep 2981231 = 4471847) B4471847
theorem B884199 : Blo 880569 884199 := bstep (se 1 (by rfl) ⟨663149, by rfl⟩ : syracuseStep 884199 = 1326299) B1326299
theorem B884315 : Blo 880569 884315 := bstep (se 1 (by rfl) ⟨663236, by rfl⟩ : syracuseStep 884315 = 1326473) B1326473
theorem B2981609 : Blo 880569 2981609 := bstep (se 2 (by rfl) ⟨1118103, by rfl⟩ : syracuseStep 2981609 = 2236207) B2236207
theorem B884551 : Blo 880569 884551 := bstep (se 1 (by rfl) ⟨663413, by rfl⟩ : syracuseStep 884551 = 1326827) B1326827
theorem B14516281 : Blo 880569 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B18120935 : Blo 880569 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B1966687 : Blo 880569 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B1671977 : Blo 880569 1671977 := bstep (se 2 (by rfl) ⟨626991, by rfl⟩ : syracuseStep 1671977 = 1253983) B1253983
theorem B7537495 : Blo 880569 7537495 := bstep (se 1 (by rfl) ⟨5653121, by rfl⟩ : syracuseStep 7537495 = 11306243) B11306243
theorem B2982743 : Blo 880569 2982743 := bstep (se 1 (by rfl) ⟨2237057, by rfl⟩ : syracuseStep 2982743 = 4474115) B4474115
theorem B2229191 : Blo 880569 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B1115471 : Blo 880569 1115471 := bstep (se 1 (by rfl) ⟨836603, by rfl⟩ : syracuseStep 1115471 = 1673207) B1673207
theorem B18089405 : Blo 880569 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B2983823 : Blo 880569 2983823 := bstep (se 1 (by rfl) ⟨2237867, by rfl⟩ : syracuseStep 2983823 = 4475735) B4475735
theorem B1411103 : Blo 880569 1411103 := bstep (se 1 (by rfl) ⟨1058327, by rfl⟩ : syracuseStep 1411103 = 2116655) B2116655
theorem B6686873 : Blo 880569 6686873 := bstep (se 2 (by rfl) ⟨2507577, by rfl⟩ : syracuseStep 6686873 = 5015155) B5015155
theorem B1116443 : Blo 880569 1116443 := bstep (se 1 (by rfl) ⟨837332, by rfl⟩ : syracuseStep 1116443 = 1674665) B1674665
theorem B15305051 : Blo 880569 15305051 := bstep (se 1 (by rfl) ⟨11478788, by rfl⟩ : syracuseStep 15305051 = 22957577) B22957577
theorem B5376563 : Blo 880569 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B11307883 : Blo 880569 11307883 := bstep (se 1 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 11307883 = 16961825) B16961825
theorem B1674209 : Blo 880569 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B3345533 : Blo 880569 3345533 := bstep (se 3 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 3345533 = 1254575) B1254575
theorem B11308247 : Blo 880569 11308247 := bstep (se 1 (by rfl) ⟨8481185, by rfl⟩ : syracuseStep 11308247 = 16962371) B16962371
theorem B1117567 : Blo 880569 1117567 := bstep (se 1 (by rfl) ⟨838175, by rfl⟩ : syracuseStep 1117567 = 1676351) B1676351
theorem B2231783 : Blo 880569 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B12095513 : Blo 880569 12095513 := bstep (se 2 (by rfl) ⟨4535817, by rfl⟩ : syracuseStep 12095513 = 9071635) B9071635
theorem B6688817 : Blo 880569 6688817 := bstep (se 2 (by rfl) ⟨2508306, by rfl⟩ : syracuseStep 6688817 = 5016613) B5016613
theorem B3346535 : Blo 880569 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B2232481 : Blo 880569 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B3182753 : Blo 880569 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B4460831 : Blo 880569 4460831 := bstep (se 1 (by rfl) ⟨3345623, by rfl⟩ : syracuseStep 4460831 = 6691247) B6691247
theorem B1675561 : Blo 880569 1675561 := bstep (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) B1256671
theorem B1676123 : Blo 880569 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B22942613 : Blo 880569 22942613 := bstep (se 6 (by rfl) ⟨537717, by rfl⟩ : syracuseStep 22942613 = 1075435) B1075435
theorem B3773465 : Blo 880569 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B33854759 : Blo 880569 33854759 := bstep (se 1 (by rfl) ⟨25391069, by rfl⟩ : syracuseStep 33854759 = 50782139) B50782139
theorem B1414511 : Blo 880569 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B1414793 : Blo 880569 1414793 := bstep (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) B1061095
theorem B5019347 : Blo 880569 5019347 := bstep (se 1 (by rfl) ⟨3764510, by rfl⟩ : syracuseStep 5019347 = 7529021) B7529021
theorem B1677019 : Blo 880569 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B2823923 : Blo 880569 2823923 := bstep (se 1 (by rfl) ⟨2117942, by rfl⟩ : syracuseStep 2823923 = 4235885) B4235885
theorem B3774215 : Blo 880569 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B1677179 : Blo 880569 1677179 := bstep (se 1 (by rfl) ⟨1257884, by rfl⟩ : syracuseStep 1677179 = 2515769) B2515769
theorem B5019529 : Blo 880569 5019529 := bstep (se 2 (by rfl) ⟨1882323, by rfl⟩ : syracuseStep 5019529 = 3764647) B3764647
theorem B6690761 : Blo 880569 6690761 := bstep (se 2 (by rfl) ⟨2509035, by rfl⟩ : syracuseStep 6690761 = 5018071) B5018071
theorem B19306631 : Blo 880569 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B1677665 : Blo 880569 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B7543205 : Blo 880569 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B1087975 : Blo 880569 1087975 := bstep (se 1 (by rfl) ⟨815981, by rfl⟩ : syracuseStep 1087975 = 1631963) B1631963
theorem B1678151 : Blo 880569 1678151 := bstep (se 1 (by rfl) ⟨1258613, by rfl⟩ : syracuseStep 1678151 = 2517227) B2517227
theorem B3349633 : Blo 880569 3349633 := bstep (se 2 (by rfl) ⟨1256112, by rfl⟩ : syracuseStep 3349633 = 2512225) B2512225
theorem B1679123 : Blo 880569 1679123 := bstep (se 1 (by rfl) ⟨1259342, by rfl⟩ : syracuseStep 1679123 = 2518685) B2518685
theorem B11476829 : Blo 880569 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B21438431 : Blo 880569 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B3350879 : Blo 880569 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B893467 : Blo 880569 893467 := bstep (se 1 (by rfl) ⟨670100, by rfl⟩ : syracuseStep 893467 = 1340201) B1340201
theorem B7152209 : Blo 880569 7152209 := bstep (se 2 (by rfl) ⟨2682078, by rfl⟩ : syracuseStep 7152209 = 5364157) B5364157
theorem B1254199 : Blo 880569 1254199 := bstep (se 1 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 1254199 = 1881299) B1881299
theorem B4236151 : Blo 880569 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B10068947 : Blo 880569 10068947 := bstep (se 1 (by rfl) ⟨7551710, by rfl⟩ : syracuseStep 10068947 = 15103421) B15103421
theorem B992479 : Blo 880569 992479 := bstep (se 1 (by rfl) ⟨744359, by rfl⟩ : syracuseStep 992479 = 1488719) B1488719
theorem B3351881 : Blo 880569 3351881 := bstep (se 2 (by rfl) ⟨1256955, by rfl⟩ : syracuseStep 3351881 = 2513911) B2513911
theorem B4761089 : Blo 880569 4761089 := bstep (se 2 (by rfl) ⟨1785408, by rfl⟩ : syracuseStep 4761089 = 3570817) B3570817
theorem B8496677 : Blo 880569 8496677 := bstep (se 4 (by rfl) ⟨796563, by rfl⟩ : syracuseStep 8496677 = 1593127) B1593127
theorem B14296625 : Blo 880569 14296625 := bstep (se 2 (by rfl) ⟨5361234, by rfl⟩ : syracuseStep 14296625 = 10722469) B10722469
theorem B3352367 : Blo 880569 3352367 := bstep (se 1 (by rfl) ⟨2514275, by rfl⟩ : syracuseStep 3352367 = 5028551) B5028551
theorem B3221311 : Blo 880569 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B993307 : Blo 880569 993307 := bstep (se 1 (by rfl) ⟨744980, by rfl⟩ : syracuseStep 993307 = 1489961) B1489961
theorem B1321007 : Blo 880569 1321007 := bstep (se 1 (by rfl) ⟨990755, by rfl⟩ : syracuseStep 1321007 = 1981511) B1981511
theorem B1321271 : Blo 880569 1321271 := bstep (se 1 (by rfl) ⟨990953, by rfl⟩ : syracuseStep 1321271 = 1981907) B1981907
theorem B13576657 : Blo 880569 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B1321451 : Blo 880569 1321451 := bstep (se 1 (by rfl) ⟨991088, by rfl⟩ : syracuseStep 1321451 = 1982177) B1982177
theorem B1322153 : Blo 880569 1322153 := bstep (se 2 (by rfl) ⟨495807, by rfl⟩ : syracuseStep 1322153 = 991615) B991615
theorem B6892877 : Blo 880569 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B1486235 : Blo 880569 1486235 := bstep (se 1 (by rfl) ⟨1114676, by rfl⟩ : syracuseStep 1486235 = 2229353) B2229353
theorem B994783 : Blo 880569 994783 := bstep (se 1 (by rfl) ⟨746087, by rfl⟩ : syracuseStep 994783 = 1492175) B1492175
theorem B1322567 : Blo 880569 1322567 := bstep (se 1 (by rfl) ⟨991925, by rfl⟩ : syracuseStep 1322567 = 1983851) B1983851
theorem B3583595 : Blo 880569 3583595 := bstep (se 1 (by rfl) ⟨2687696, by rfl⟩ : syracuseStep 3583595 = 5375393) B5375393
theorem B1322747 : Blo 880569 1322747 := bstep (se 1 (by rfl) ⟨992060, by rfl⟩ : syracuseStep 1322747 = 1984121) B1984121
theorem B3354493 : Blo 880569 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B4468769 : Blo 880569 4468769 := bstep (se 2 (by rfl) ⟨1675788, by rfl⟩ : syracuseStep 4468769 = 3351577) B3351577
theorem B6697079 : Blo 880569 6697079 := bstep (se 1 (by rfl) ⟨5022809, by rfl⟩ : syracuseStep 6697079 = 10045619) B10045619
theorem B22622327 : Blo 880569 22622327 := bstep (se 1 (by rfl) ⟨16966745, by rfl⟩ : syracuseStep 22622327 = 33933491) B33933491
theorem B1486991 : Blo 880569 1486991 := bstep (se 1 (by rfl) ⟨1115243, by rfl⟩ : syracuseStep 1486991 = 2230487) B2230487
theorem B1487207 : Blo 880569 1487207 := bstep (se 1 (by rfl) ⟨1115405, by rfl⟩ : syracuseStep 1487207 = 2230811) B2230811
theorem B1323419 : Blo 880569 1323419 := bstep (se 1 (by rfl) ⟨992564, by rfl⟩ : syracuseStep 1323419 = 1985129) B1985129
theorem B3814003 : Blo 880569 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B6435607 : Blo 880569 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1323839 : Blo 880569 1323839 := bstep (se 1 (by rfl) ⟨992879, by rfl⟩ : syracuseStep 1323839 = 1985759) B1985759
theorem B1323983 : Blo 880569 1323983 := bstep (se 1 (by rfl) ⟨992987, by rfl⟩ : syracuseStep 1323983 = 1985975) B1985975
theorem B1324025 : Blo 880569 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B1324073 : Blo 880569 1324073 := bstep (se 2 (by rfl) ⟨496527, by rfl⟩ : syracuseStep 1324073 = 993055) B993055
theorem B1324103 : Blo 880569 1324103 := bstep (se 1 (by rfl) ⟨993077, by rfl⟩ : syracuseStep 1324103 = 1986155) B1986155
theorem B2831431 : Blo 880569 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B10073321 : Blo 880569 10073321 := bstep (se 2 (by rfl) ⟨3777495, by rfl⟩ : syracuseStep 10073321 = 7554991) B7554991
theorem B2831611 : Blo 880569 2831611 := bstep (se 1 (by rfl) ⟨2123708, by rfl⟩ : syracuseStep 2831611 = 4247417) B4247417
theorem B1324283 : Blo 880569 1324283 := bstep (se 1 (by rfl) ⟨993212, by rfl⟩ : syracuseStep 1324283 = 1986425) B1986425
theorem B7550891 : Blo 880569 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B14333993 : Blo 880569 14333993 := bstep (se 2 (by rfl) ⟨5375247, by rfl⟩ : syracuseStep 14333993 = 10750495) B10750495
theorem B1882153 : Blo 880569 1882153 := bstep (se 2 (by rfl) ⟨705807, by rfl⟩ : syracuseStep 1882153 = 1411615) B1411615
theorem B4077803 : Blo 880569 4077803 := bstep (se 1 (by rfl) ⟨3058352, by rfl⟩ : syracuseStep 4077803 = 6116705) B6116705
theorem B6109607 : Blo 880569 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1325519 : Blo 880569 1325519 := bstep (se 1 (by rfl) ⟨994139, by rfl⟩ : syracuseStep 1325519 = 1988279) B1988279
theorem B14301683 : Blo 880569 14301683 := bstep (se 1 (by rfl) ⟨10726262, by rfl⟩ : syracuseStep 14301683 = 21452525) B21452525
theorem B1325609 : Blo 880569 1325609 := bstep (se 2 (by rfl) ⟨497103, by rfl⟩ : syracuseStep 1325609 = 994207) B994207
theorem B7551575 : Blo 880569 7551575 := bstep (se 1 (by rfl) ⟨5663681, by rfl⟩ : syracuseStep 7551575 = 11327363) B11327363
theorem B4831903 : Blo 880569 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B9550547 : Blo 880569 9550547 := bstep (se 1 (by rfl) ⟨7162910, by rfl⟩ : syracuseStep 9550547 = 14325821) B14325821
theorem B1325801 : Blo 880569 1325801 := bstep (se 2 (by rfl) ⟨497175, by rfl⟩ : syracuseStep 1325801 = 994351) B994351
theorem B1489711 : Blo 880569 1489711 := bstep (se 1 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 1489711 = 2234567) B2234567
theorem B7551953 : Blo 880569 7551953 := bstep (se 2 (by rfl) ⟨2831982, by rfl⟩ : syracuseStep 7551953 = 5663965) B5663965
theorem B1326185 : Blo 880569 1326185 := bstep (se 2 (by rfl) ⟨497319, by rfl⟩ : syracuseStep 1326185 = 994639) B994639
theorem B3357895 : Blo 880569 3357895 := bstep (se 1 (by rfl) ⟨2518421, by rfl⟩ : syracuseStep 3357895 = 5036843) B5036843
theorem B5651687 : Blo 880569 5651687 := bstep (se 1 (by rfl) ⟨4238765, by rfl⟩ : syracuseStep 5651687 = 8477531) B8477531
theorem B1326311 : Blo 880569 1326311 := bstep (se 1 (by rfl) ⟨994733, by rfl⟩ : syracuseStep 1326311 = 1989467) B1989467
theorem B1982015 : Blo 880569 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B11321005 : Blo 880569 11321005 := bstep (se 3 (by rfl) ⟨2122688, by rfl⟩ : syracuseStep 11321005 = 4245377) B4245377
theorem B1326815 : Blo 880569 1326815 := bstep (se 1 (by rfl) ⟨995111, by rfl⟩ : syracuseStep 1326815 = 1990223) B1990223
theorem B1490663 : Blo 880569 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B1982375 : Blo 880569 1982375 := bstep (se 1 (by rfl) ⟨1486781, by rfl⟩ : syracuseStep 1982375 = 2973563) B2973563
theorem B11321369 : Blo 880569 11321369 := bstep (se 2 (by rfl) ⟨4245513, by rfl⟩ : syracuseStep 11321369 = 8491027) B8491027
theorem B1982699 : Blo 880569 1982699 := bstep (se 1 (by rfl) ⟨1487024, by rfl⟩ : syracuseStep 1982699 = 2974049) B2974049
theorem B4244071 : Blo 880569 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B1983599 : Blo 880569 1983599 := bstep (se 1 (by rfl) ⟨1487699, by rfl⟩ : syracuseStep 1983599 = 2975399) B2975399
theorem B1492303 : Blo 880569 1492303 := bstep (se 1 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 1492303 = 2238455) B2238455
theorem B1983995 : Blo 880569 1983995 := bstep (se 1 (by rfl) ⟨1487996, by rfl⟩ : syracuseStep 1983995 = 2975993) B2975993
theorem B1984031 : Blo 880569 1984031 := bstep (se 1 (by rfl) ⟨1488023, by rfl⟩ : syracuseStep 1984031 = 2976047) B2976047
theorem B1984175 : Blo 880569 1984175 := bstep (se 1 (by rfl) ⟨1488131, by rfl⟩ : syracuseStep 1984175 = 2976263) B2976263
theorem B1984607 : Blo 880569 1984607 := bstep (se 1 (by rfl) ⟨1488455, by rfl⟩ : syracuseStep 1984607 = 2976911) B2976911
theorem B19089593 : Blo 880569 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B1984895 : Blo 880569 1984895 := bstep (se 1 (by rfl) ⟨1488671, by rfl⟩ : syracuseStep 1984895 = 2977343) B2977343
theorem B5032651 : Blo 880569 5032651 := bstep (se 1 (by rfl) ⟨3774488, by rfl⟩ : syracuseStep 5032651 = 7548977) B7548977
theorem B1985363 : Blo 880569 1985363 := bstep (se 1 (by rfl) ⟨1489022, by rfl⟩ : syracuseStep 1985363 = 2978045) B2978045
theorem B2509697 : Blo 880569 2509697 := bstep (se 2 (by rfl) ⟨941136, by rfl⟩ : syracuseStep 2509697 = 1882273) B1882273
theorem B2509879 : Blo 880569 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B1985723 : Blo 880569 1985723 := bstep (se 1 (by rfl) ⟨1489292, by rfl⟩ : syracuseStep 1985723 = 2978585) B2978585
theorem B5098729 : Blo 880569 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B1985903 : Blo 880569 1985903 := bstep (se 1 (by rfl) ⟨1489427, by rfl⟩ : syracuseStep 1985903 = 2978855) B2978855
theorem B16076555 : Blo 880569 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B1986623 : Blo 880569 1986623 := bstep (se 1 (by rfl) ⟨1489967, by rfl⟩ : syracuseStep 1986623 = 2979935) B2979935
theorem B1888543 : Blo 880569 1888543 := bstep (se 1 (by rfl) ⟨1416407, by rfl⟩ : syracuseStep 1888543 = 2832815) B2832815
theorem B1986857 : Blo 880569 1986857 := bstep (se 2 (by rfl) ⟨745071, by rfl⟩ : syracuseStep 1986857 = 1490143) B1490143
theorem B11456873 : Blo 880569 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B2511337 : Blo 880569 2511337 := bstep (se 2 (by rfl) ⟨941751, by rfl⟩ : syracuseStep 2511337 = 1883503) B1883503
theorem B1987127 : Blo 880569 1987127 := bstep (se 1 (by rfl) ⟨1490345, by rfl⟩ : syracuseStep 1987127 = 2980691) B2980691
theorem B1987433 : Blo 880569 1987433 := bstep (se 2 (by rfl) ⟨745287, by rfl⟩ : syracuseStep 1987433 = 1490575) B1490575
theorem B1987487 : Blo 880569 1987487 := bstep (se 1 (by rfl) ⟨1490615, by rfl⟩ : syracuseStep 1987487 = 2981231) B2981231
theorem B1987739 : Blo 880569 1987739 := bstep (se 1 (by rfl) ⟨1490804, by rfl⟩ : syracuseStep 1987739 = 2981609) B2981609
theorem B10212563 : Blo 880569 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B1988315 : Blo 880569 1988315 := bstep (se 1 (by rfl) ⟨1491236, by rfl⟩ : syracuseStep 1988315 = 2982473) B2982473
theorem B1988423 : Blo 880569 1988423 := bstep (se 1 (by rfl) ⟨1491317, by rfl⟩ : syracuseStep 1988423 = 2982635) B2982635
theorem B30627841 : Blo 880569 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B9558161 : Blo 880569 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B2120075 : Blo 880569 2120075 := bstep (se 1 (by rfl) ⟨1590056, by rfl⟩ : syracuseStep 2120075 = 3180113) B3180113
theorem B1006171 : Blo 880569 1006171 := bstep (se 1 (by rfl) ⟨754628, by rfl⟩ : syracuseStep 1006171 = 1509257) B1509257
theorem B1989431 : Blo 880569 1989431 := bstep (se 1 (by rfl) ⟨1492073, by rfl⟩ : syracuseStep 1989431 = 2984147) B2984147
theorem B2153287 : Blo 880569 2153287 := bstep (se 1 (by rfl) ⟨1614965, by rfl⟩ : syracuseStep 2153287 = 3229931) B3229931
theorem B1989611 : Blo 880569 1989611 := bstep (se 1 (by rfl) ⟨1492208, by rfl⟩ : syracuseStep 1989611 = 2984417) B2984417
theorem B2121383 : Blo 880569 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B2975507 : Blo 880569 2975507 := bstep (se 1 (by rfl) ⟨2231630, by rfl⟩ : syracuseStep 2975507 = 4463261) B4463261
theorem B3762119 : Blo 880569 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B2975723 : Blo 880569 2975723 := bstep (se 1 (by rfl) ⟨2231792, by rfl⟩ : syracuseStep 2975723 = 4463585) B4463585
theorem B25454735 : Blo 880569 25454735 := bstep (se 1 (by rfl) ⟨19091051, by rfl⟩ : syracuseStep 25454735 = 38182103) B38182103
theorem B3762719 : Blo 880569 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B2125111 : Blo 880569 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2977235 : Blo 880569 2977235 := bstep (se 1 (by rfl) ⟨2232926, by rfl⟩ : syracuseStep 2977235 = 4465853) B4465853
theorem B17034877 : Blo 880569 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B2977505 : Blo 880569 2977505 := bstep (se 2 (by rfl) ⟨1116564, by rfl⟩ : syracuseStep 2977505 = 2233129) B2233129
theorem B880623 : Blo 880569 880623 := bstep (se 1 (by rfl) ⟨660467, by rfl⟩ : syracuseStep 880623 = 1320935) B1320935
theorem B880635 : Blo 880569 880635 := bstep (se 1 (by rfl) ⟨660476, by rfl⟩ : syracuseStep 880635 = 1320953) B1320953
theorem B880703 : Blo 880569 880703 := bstep (se 1 (by rfl) ⟨660527, by rfl⟩ : syracuseStep 880703 = 1321055) B1321055
theorem B880743 : Blo 880569 880743 := bstep (se 1 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 880743 = 1321115) B1321115
theorem B880767 : Blo 880569 880767 := bstep (se 1 (by rfl) ⟨660575, by rfl⟩ : syracuseStep 880767 = 1321151) B1321151
theorem B880795 : Blo 880569 880795 := bstep (se 1 (by rfl) ⟨660596, by rfl⟩ : syracuseStep 880795 = 1321193) B1321193
theorem B880999 : Blo 880569 880999 := bstep (se 1 (by rfl) ⟨660749, by rfl⟩ : syracuseStep 880999 = 1321499) B1321499
theorem B12710297 : Blo 880569 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B881051 : Blo 880569 881051 := bstep (se 1 (by rfl) ⟨660788, by rfl⟩ : syracuseStep 881051 = 1321577) B1321577
theorem B2683343 : Blo 880569 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B12055223 : Blo 880569 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B881403 : Blo 880569 881403 := bstep (se 1 (by rfl) ⟨661052, by rfl⟩ : syracuseStep 881403 = 1322105) B1322105
theorem B881471 : Blo 880569 881471 := bstep (se 1 (by rfl) ⟨661103, by rfl⟩ : syracuseStep 881471 = 1322207) B1322207
theorem B881499 : Blo 880569 881499 := bstep (se 1 (by rfl) ⟨661124, by rfl⟩ : syracuseStep 881499 = 1322249) B1322249
theorem B881567 : Blo 880569 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B881647 : Blo 880569 881647 := bstep (se 1 (by rfl) ⟨661235, by rfl⟩ : syracuseStep 881647 = 1322471) B1322471
theorem B881735 : Blo 880569 881735 := bstep (se 1 (by rfl) ⟨661301, by rfl⟩ : syracuseStep 881735 = 1322603) B1322603
theorem B881819 : Blo 880569 881819 := bstep (se 1 (by rfl) ⟨661364, by rfl⟩ : syracuseStep 881819 = 1322729) B1322729
theorem B881915 : Blo 880569 881915 := bstep (se 1 (by rfl) ⟨661436, by rfl⟩ : syracuseStep 881915 = 1322873) B1322873
theorem B1275145 : Blo 880569 1275145 := bstep (se 2 (by rfl) ⟨478179, by rfl⟩ : syracuseStep 1275145 = 956359) B956359
theorem B881983 : Blo 880569 881983 := bstep (se 1 (by rfl) ⟨661487, by rfl⟩ : syracuseStep 881983 = 1322975) B1322975
theorem B17659205 : Blo 880569 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B3175847 : Blo 880569 3175847 := bstep (se 1 (by rfl) ⟨2381885, by rfl⟩ : syracuseStep 3175847 = 4763771) B4763771
theorem B2979287 : Blo 880569 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B882151 : Blo 880569 882151 := bstep (se 1 (by rfl) ⟨661613, by rfl⟩ : syracuseStep 882151 = 1323227) B1323227
theorem B882159 : Blo 880569 882159 := bstep (se 1 (by rfl) ⟨661619, by rfl⟩ : syracuseStep 882159 = 1323239) B1323239
theorem B882267 : Blo 880569 882267 := bstep (se 1 (by rfl) ⟨661700, by rfl⟩ : syracuseStep 882267 = 1323401) B1323401
theorem B882331 : Blo 880569 882331 := bstep (se 1 (by rfl) ⟨661748, by rfl⟩ : syracuseStep 882331 = 1323497) B1323497
theorem B882415 : Blo 880569 882415 := bstep (se 1 (by rfl) ⟨661811, by rfl⟩ : syracuseStep 882415 = 1323623) B1323623
theorem B882503 : Blo 880569 882503 := bstep (se 1 (by rfl) ⟨661877, by rfl⟩ : syracuseStep 882503 = 1323755) B1323755
theorem B882523 : Blo 880569 882523 := bstep (se 1 (by rfl) ⟨661892, by rfl⟩ : syracuseStep 882523 = 1323785) B1323785
theorem B882591 : Blo 880569 882591 := bstep (se 1 (by rfl) ⟨661943, by rfl⟩ : syracuseStep 882591 = 1323887) B1323887
theorem B5666759 : Blo 880569 5666759 := bstep (se 1 (by rfl) ⟨4250069, by rfl⟩ : syracuseStep 5666759 = 8500139) B8500139
theorem B882759 : Blo 880569 882759 := bstep (se 1 (by rfl) ⟨662069, by rfl⟩ : syracuseStep 882759 = 1324139) B1324139
theorem B882919 : Blo 880569 882919 := bstep (se 1 (by rfl) ⟨662189, by rfl⟩ : syracuseStep 882919 = 1324379) B1324379
theorem B883103 : Blo 880569 883103 := bstep (se 1 (by rfl) ⟨662327, by rfl⟩ : syracuseStep 883103 = 1324655) B1324655
theorem B883151 : Blo 880569 883151 := bstep (se 1 (by rfl) ⟨662363, by rfl⟩ : syracuseStep 883151 = 1324727) B1324727
theorem B883175 : Blo 880569 883175 := bstep (se 1 (by rfl) ⟨662381, by rfl⟩ : syracuseStep 883175 = 1324763) B1324763
theorem B18086449 : Blo 880569 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B883291 : Blo 880569 883291 := bstep (se 1 (by rfl) ⟨662468, by rfl⟩ : syracuseStep 883291 = 1324937) B1324937
theorem B6716033 : Blo 880569 6716033 := bstep (se 2 (by rfl) ⟨2518512, by rfl⟩ : syracuseStep 6716033 = 5037025) B5037025
theorem B883359 : Blo 880569 883359 := bstep (se 1 (by rfl) ⟨662519, by rfl⟩ : syracuseStep 883359 = 1325039) B1325039
theorem B883527 : Blo 880569 883527 := bstep (se 1 (by rfl) ⟨662645, by rfl⟩ : syracuseStep 883527 = 1325291) B1325291
theorem B883567 : Blo 880569 883567 := bstep (se 1 (by rfl) ⟨662675, by rfl⟩ : syracuseStep 883567 = 1325351) B1325351
theorem B2456477 : Blo 880569 2456477 := bstep (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) B921179
theorem B883623 : Blo 880569 883623 := bstep (se 1 (by rfl) ⟨662717, by rfl⟩ : syracuseStep 883623 = 1325435) B1325435
theorem B883803 : Blo 880569 883803 := bstep (se 1 (by rfl) ⟨662852, by rfl⟩ : syracuseStep 883803 = 1325705) B1325705
theorem B883919 : Blo 880569 883919 := bstep (se 1 (by rfl) ⟨662939, by rfl⟩ : syracuseStep 883919 = 1325879) B1325879
theorem B6454487 : Blo 880569 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B883943 : Blo 880569 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B884039 : Blo 880569 884039 := bstep (se 1 (by rfl) ⟨663029, by rfl⟩ : syracuseStep 884039 = 1326059) B1326059
theorem B884175 : Blo 880569 884175 := bstep (se 1 (by rfl) ⟨663131, by rfl⟩ : syracuseStep 884175 = 1326263) B1326263
theorem B884335 : Blo 880569 884335 := bstep (se 1 (by rfl) ⟨663251, by rfl⟩ : syracuseStep 884335 = 1326503) B1326503
theorem B884391 : Blo 880569 884391 := bstep (se 1 (by rfl) ⟨663293, by rfl⟩ : syracuseStep 884391 = 1326587) B1326587
theorem B884455 : Blo 880569 884455 := bstep (se 1 (by rfl) ⟨663341, by rfl⟩ : syracuseStep 884455 = 1326683) B1326683
theorem B884511 : Blo 880569 884511 := bstep (se 1 (by rfl) ⟨663383, by rfl⟩ : syracuseStep 884511 = 1326767) B1326767
theorem B1114651 : Blo 880569 1114651 := bstep (se 1 (by rfl) ⟨835988, by rfl⟩ : syracuseStep 1114651 = 1671977) B1671977
theorem B12059603 : Blo 880569 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B1672265 : Blo 880569 1672265 := bstep (se 2 (by rfl) ⟨627099, by rfl⟩ : syracuseStep 1672265 = 1254199) B1254199
theorem B4457915 : Blo 880569 4457915 := bstep (se 1 (by rfl) ⟨3343436, by rfl⟩ : syracuseStep 4457915 = 6686873) B6686873
theorem B1673131 : Blo 880569 1673131 := bstep (se 1 (by rfl) ⟨1254848, by rfl⟩ : syracuseStep 1673131 = 2509697) B2509697
theorem B2230355 : Blo 880569 2230355 := bstep (se 1 (by rfl) ⟨1672766, by rfl⟩ : syracuseStep 2230355 = 3345533) B3345533
theorem B7538831 : Blo 880569 7538831 := bstep (se 1 (by rfl) ⟨5654123, by rfl⟩ : syracuseStep 7538831 = 11308247) B11308247
theorem B4295081 : Blo 880569 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B10717703 : Blo 880569 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B5802533 : Blo 880569 5802533 := bstep (se 4 (by rfl) ⟨543987, by rfl⟩ : syracuseStep 5802533 = 1087975) B1087975
theorem B8063675 : Blo 880569 8063675 := bstep (se 1 (by rfl) ⟨6047756, by rfl⟩ : syracuseStep 8063675 = 12095513) B12095513
theorem B4459211 : Blo 880569 4459211 := bstep (se 1 (by rfl) ⟨3344408, by rfl⟩ : syracuseStep 4459211 = 6688817) B6688817
theorem B2231023 : Blo 880569 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B7637915 : Blo 880569 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B10488997 : Blo 880569 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B1117415 : Blo 880569 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B3346231 : Blo 880569 3346231 := bstep (se 1 (by rfl) ⟨2509673, by rfl⟩ : syracuseStep 3346231 = 5019347) B5019347
theorem B15077177 : Blo 880569 15077177 := bstep (se 2 (by rfl) ⟨5653941, by rfl⟩ : syracuseStep 15077177 = 11307883) B11307883
theorem B1118119 : Blo 880569 1118119 := bstep (se 1 (by rfl) ⟨838589, by rfl⟩ : syracuseStep 1118119 = 1677179) B1677179
theorem B4460507 : Blo 880569 4460507 := bstep (se 1 (by rfl) ⟨3345380, by rfl⟩ : syracuseStep 4460507 = 6690761) B6690761
theorem B3346505 : Blo 880569 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B1118443 : Blo 880569 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B1413383 : Blo 880569 1413383 := bstep (se 1 (by rfl) ⟨1060037, by rfl⟩ : syracuseStep 1413383 = 2120075) B2120075
theorem B3772781 : Blo 880569 3772781 := bstep (se 3 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 3772781 = 1414793) B1414793
theorem B1118767 : Blo 880569 1118767 := bstep (se 1 (by rfl) ⟨839075, by rfl⟩ : syracuseStep 1118767 = 1678151) B1678151
theorem B10064573 : Blo 880569 10064573 := bstep (se 3 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 10064573 = 3774215) B3774215
theorem B22713169 : Blo 880569 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B1414255 : Blo 880569 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B1119415 : Blo 880569 1119415 := bstep (se 1 (by rfl) ⟨839561, by rfl⟩ : syracuseStep 1119415 = 1679123) B1679123
theorem B14292287 : Blo 880569 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B2233919 : Blo 880569 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B51484349 : Blo 880569 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B2234081 : Blo 880569 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B3348449 : Blo 880569 3348449 := bstep (se 2 (by rfl) ⟨1255668, by rfl⟩ : syracuseStep 3348449 = 2511337) B2511337
theorem B5085337 : Blo 880569 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B2234587 : Blo 880569 2234587 := bstep (se 1 (by rfl) ⟨1675940, by rfl⟩ : syracuseStep 2234587 = 3351881) B3351881
theorem B16292285 : Blo 880569 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B2234911 : Blo 880569 2234911 := bstep (se 1 (by rfl) ⟨1676183, by rfl⟩ : syracuseStep 2234911 = 3352367) B3352367
theorem B3775241 : Blo 880569 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B3775481 : Blo 880569 3775481 := bstep (se 2 (by rfl) ⟨1415805, by rfl⟩ : syracuseStep 3775481 = 2831611) B2831611
theorem B990823 : Blo 880569 990823 := bstep (se 1 (by rfl) ⟨743117, by rfl⟩ : syracuseStep 990823 = 1486235) B1486235
theorem B2236025 : Blo 880569 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B6692705 : Blo 880569 6692705 := bstep (se 2 (by rfl) ⟨2509764, by rfl⟩ : syracuseStep 6692705 = 5019529) B5019529
theorem B4464557 : Blo 880569 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B40837121 : Blo 880569 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B4464719 : Blo 880569 4464719 := bstep (se 1 (by rfl) ⟨3348539, by rfl⟩ : syracuseStep 4464719 = 6697079) B6697079
theorem B15081551 : Blo 880569 15081551 := bstep (se 1 (by rfl) ⟨11311163, by rfl⟩ : syracuseStep 15081551 = 22622327) B22622327
theorem B991327 : Blo 880569 991327 := bstep (se 1 (by rfl) ⟨743495, by rfl⟩ : syracuseStep 991327 = 1486991) B1486991
theorem B991471 : Blo 880569 991471 := bstep (se 1 (by rfl) ⟨743603, by rfl⟩ : syracuseStep 991471 = 1487207) B1487207
theorem B8036815 : Blo 880569 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B11772803 : Blo 880569 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B3777839 : Blo 880569 3777839 := bstep (se 1 (by rfl) ⟨2833379, by rfl⟩ : syracuseStep 3777839 = 5666759) B5666759
theorem B4466177 : Blo 880569 4466177 := bstep (se 2 (by rfl) ⟨1674816, by rfl⟩ : syracuseStep 4466177 = 3349633) B3349633
theorem B6367031 : Blo 880569 6367031 := bstep (se 1 (by rfl) ⟨4775273, by rfl⟩ : syracuseStep 6367031 = 9550547) B9550547
theorem B4302991 : Blo 880569 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B1321343 : Blo 880569 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B993775 : Blo 880569 993775 := bstep (se 1 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 993775 = 1490663) B1490663
theorem B1321583 : Blo 880569 1321583 := bstep (se 1 (by rfl) ⟨991187, by rfl⟩ : syracuseStep 1321583 = 1982375) B1982375
theorem B7547579 : Blo 880569 7547579 := bstep (se 1 (by rfl) ⟨5660684, by rfl⟩ : syracuseStep 7547579 = 11321369) B11321369
theorem B1321799 : Blo 880569 1321799 := bstep (se 1 (by rfl) ⟨991349, by rfl⟩ : syracuseStep 1321799 = 1982699) B1982699
theorem B1486127 : Blo 880569 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B1191289 : Blo 880569 1191289 := bstep (se 2 (by rfl) ⟨446733, by rfl⟩ : syracuseStep 1191289 = 893467) B893467
theorem B1322399 : Blo 880569 1322399 := bstep (se 1 (by rfl) ⟨991799, by rfl⟩ : syracuseStep 1322399 = 1983599) B1983599
theorem B1322663 : Blo 880569 1322663 := bstep (se 1 (by rfl) ⟨991997, by rfl⟩ : syracuseStep 1322663 = 1983995) B1983995
theorem B1322687 : Blo 880569 1322687 := bstep (se 1 (by rfl) ⟨992015, by rfl⟩ : syracuseStep 1322687 = 1984031) B1984031
theorem B33894125 : Blo 880569 33894125 := bstep (se 3 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 33894125 = 12710297) B12710297
theorem B1322783 : Blo 880569 1322783 := bstep (se 1 (by rfl) ⟨992087, by rfl⟩ : syracuseStep 1322783 = 1984175) B1984175
theorem B5648201 : Blo 880569 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B1323071 : Blo 880569 1323071 := bstep (se 1 (by rfl) ⟨992303, by rfl⟩ : syracuseStep 1323071 = 1984607) B1984607
theorem B12726395 : Blo 880569 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B10203367 : Blo 880569 10203367 := bstep (se 1 (by rfl) ⟨7652525, by rfl⟩ : syracuseStep 10203367 = 15305051) B15305051
theorem B1323263 : Blo 880569 1323263 := bstep (se 1 (by rfl) ⟨992447, by rfl⟩ : syracuseStep 1323263 = 1984895) B1984895
theorem B1323305 : Blo 880569 1323305 := bstep (se 2 (by rfl) ⟨496239, by rfl⟩ : syracuseStep 1323305 = 992479) B992479
theorem B3584375 : Blo 880569 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B1323575 : Blo 880569 1323575 := bstep (se 1 (by rfl) ⟨992681, by rfl⟩ : syracuseStep 1323575 = 1985363) B1985363
theorem B1323815 : Blo 880569 1323815 := bstep (se 1 (by rfl) ⟨992861, by rfl⟩ : syracuseStep 1323815 = 1985723) B1985723
theorem B1323935 : Blo 880569 1323935 := bstep (se 1 (by rfl) ⟨992951, by rfl⟩ : syracuseStep 1323935 = 1985903) B1985903
theorem B1487855 : Blo 880569 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B1324409 : Blo 880569 1324409 := bstep (se 2 (by rfl) ⟨496653, by rfl⟩ : syracuseStep 1324409 = 993307) B993307
theorem B1324415 : Blo 880569 1324415 := bstep (se 1 (by rfl) ⟨993311, by rfl⟩ : syracuseStep 1324415 = 1986623) B1986623
theorem B1324571 : Blo 880569 1324571 := bstep (se 1 (by rfl) ⟨993428, by rfl⟩ : syracuseStep 1324571 = 1986857) B1986857
theorem B1324751 : Blo 880569 1324751 := bstep (se 1 (by rfl) ⟨993563, by rfl⟩ : syracuseStep 1324751 = 1987127) B1987127
theorem B1324955 : Blo 880569 1324955 := bstep (se 1 (by rfl) ⟨993716, by rfl⟩ : syracuseStep 1324955 = 1987433) B1987433
theorem B1324991 : Blo 880569 1324991 := bstep (se 1 (by rfl) ⟨993743, by rfl⟩ : syracuseStep 1324991 = 1987487) B1987487
theorem B18102209 : Blo 880569 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B1325159 : Blo 880569 1325159 := bstep (se 1 (by rfl) ⟨993869, by rfl⟩ : syracuseStep 1325159 = 1987739) B1987739
theorem B1325543 : Blo 880569 1325543 := bstep (se 1 (by rfl) ⟨994157, by rfl⟩ : syracuseStep 1325543 = 1988315) B1988315
theorem B1882615 : Blo 880569 1882615 := bstep (se 1 (by rfl) ⟨1411961, by rfl⟩ : syracuseStep 1882615 = 2823923) B2823923
theorem B1325615 : Blo 880569 1325615 := bstep (se 1 (by rfl) ⟨994211, by rfl⟩ : syracuseStep 1325615 = 1988423) B1988423
theorem B6372107 : Blo 880569 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B5028803 : Blo 880569 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B6798305 : Blo 880569 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B2833481 : Blo 880569 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1490089 : Blo 880569 1490089 := bstep (se 2 (by rfl) ⟨558783, by rfl⟩ : syracuseStep 1490089 = 1117567) B1117567
theorem B1326287 : Blo 880569 1326287 := bstep (se 1 (by rfl) ⟨994715, by rfl⟩ : syracuseStep 1326287 = 1989431) B1989431
theorem B1326377 : Blo 880569 1326377 := bstep (se 2 (by rfl) ⟨497391, by rfl⟩ : syracuseStep 1326377 = 994783) B994783
theorem B1326407 : Blo 880569 1326407 := bstep (se 1 (by rfl) ⟨994805, by rfl⟩ : syracuseStep 1326407 = 1989611) B1989611
theorem B4472657 : Blo 880569 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B7651219 : Blo 880569 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B4768139 : Blo 880569 4768139 := bstep (se 1 (by rfl) ⟨3576104, by rfl⟩ : syracuseStep 4768139 = 7152209) B7152209
theorem B1983671 : Blo 880569 1983671 := bstep (se 1 (by rfl) ⟨1487753, by rfl⟩ : syracuseStep 1983671 = 2975507) B2975507
theorem B2508079 : Blo 880569 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B1983815 : Blo 880569 1983815 := bstep (se 1 (by rfl) ⟨1487861, by rfl⟩ : syracuseStep 1983815 = 2975723) B2975723
theorem B6800773 : Blo 880569 6800773 := bstep (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) B1275145
theorem B2508479 : Blo 880569 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B1984823 : Blo 880569 1984823 := bstep (se 1 (by rfl) ⟨1488617, by rfl⟩ : syracuseStep 1984823 = 2977235) B2977235
theorem B1985003 : Blo 880569 1985003 := bstep (se 1 (by rfl) ⟨1488752, by rfl⟩ : syracuseStep 1985003 = 2977505) B2977505
theorem B2509537 : Blo 880569 2509537 := bstep (se 2 (by rfl) ⟨941076, by rfl⟩ : syracuseStep 2509537 = 1882153) B1882153
theorem B1788895 : Blo 880569 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B6442537 : Blo 880569 6442537 := bstep (se 2 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 6442537 = 4831903) B4831903
theorem B2117231 : Blo 880569 2117231 := bstep (se 1 (by rfl) ⟨1587923, by rfl⟩ : syracuseStep 2117231 = 3175847) B3175847
theorem B1986191 : Blo 880569 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B1986281 : Blo 880569 1986281 := bstep (se 2 (by rfl) ⟨744855, by rfl⟩ : syracuseStep 1986281 = 1489711) B1489711
theorem B2871049 : Blo 880569 2871049 := bstep (se 2 (by rfl) ⟨1076643, by rfl⟩ : syracuseStep 2871049 = 2153287) B2153287
theorem B5033927 : Blo 880569 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B9555995 : Blo 880569 9555995 := bstep (se 1 (by rfl) ⟨7166996, by rfl⟩ : syracuseStep 9555995 = 14333993) B14333993
theorem B4477193 : Blo 880569 4477193 := bstep (se 2 (by rfl) ⟨1678947, by rfl⟩ : syracuseStep 4477193 = 3357895) B3357895
theorem B5034383 : Blo 880569 5034383 := bstep (se 1 (by rfl) ⟨3775787, by rfl⟩ : syracuseStep 5034383 = 7551575) B7551575
theorem B4477355 : Blo 880569 4477355 := bstep (se 1 (by rfl) ⟨3358016, by rfl⟩ : syracuseStep 4477355 = 6716033) B6716033
theorem B5034635 : Blo 880569 5034635 := bstep (se 1 (by rfl) ⟨3775976, by rfl⟩ : syracuseStep 5034635 = 7551953) B7551953
theorem B15094673 : Blo 880569 15094673 := bstep (se 2 (by rfl) ⟨5660502, by rfl⟩ : syracuseStep 15094673 = 11321005) B11321005
theorem B19355041 : Blo 880569 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B12080623 : Blo 880569 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B1988495 : Blo 880569 1988495 := bstep (se 1 (by rfl) ⟨1491371, by rfl⟩ : syracuseStep 1988495 = 2982743) B2982743
theorem B5658761 : Blo 880569 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B10049993 : Blo 880569 10049993 := bstep (se 2 (by rfl) ⟨3768747, by rfl⟩ : syracuseStep 10049993 = 7537495) B7537495
theorem B1989215 : Blo 880569 1989215 := bstep (se 1 (by rfl) ⟨1491911, by rfl⟩ : syracuseStep 1989215 = 2983823) B2983823
theorem B940735 : Blo 880569 940735 := bstep (se 1 (by rfl) ⟨705551, by rfl⟩ : syracuseStep 940735 = 1411103) B1411103
theorem B1989737 : Blo 880569 1989737 := bstep (se 2 (by rfl) ⟨746151, by rfl⟩ : syracuseStep 1989737 = 1492303) B1492303
theorem B2121835 : Blo 880569 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B2973887 : Blo 880569 2973887 := bstep (se 1 (by rfl) ⟨2230415, by rfl⟩ : syracuseStep 2973887 = 4460831) B4460831
theorem B5366245 : Blo 880569 5366245 := bstep (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) B1006171
theorem B15295075 : Blo 880569 15295075 := bstep (se 1 (by rfl) ⟨11471306, by rfl⟩ : syracuseStep 15295075 = 22942613) B22942613
theorem B2515643 : Blo 880569 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B6808375 : Blo 880569 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B22569839 : Blo 880569 22569839 := bstep (se 1 (by rfl) ⟨16927379, by rfl⟩ : syracuseStep 22569839 = 33854759) B33854759
theorem B2974589 : Blo 880569 2974589 := bstep (se 3 (by rfl) ⟨557735, by rfl⟩ : syracuseStep 2974589 = 1115471) B1115471
theorem B943007 : Blo 880569 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B6710201 : Blo 880569 6710201 := bstep (se 2 (by rfl) ⟨2516325, by rfl⟩ : syracuseStep 6710201 = 5032651) B5032651
theorem B2976641 : Blo 880569 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B2518057 : Blo 880569 2518057 := bstep (se 2 (by rfl) ⟨944271, by rfl⟩ : syracuseStep 2518057 = 1888543) B1888543
theorem B10874141 : Blo 880569 10874141 := bstep (se 3 (by rfl) ⟨2038901, by rfl⟩ : syracuseStep 10874141 = 4077803) B4077803
theorem B6712631 : Blo 880569 6712631 := bstep (se 1 (by rfl) ⟨5034473, by rfl⟩ : syracuseStep 6712631 = 10068947) B10068947
theorem B2977181 : Blo 880569 2977181 := bstep (se 3 (by rfl) ⟨558221, by rfl⟩ : syracuseStep 2977181 = 1116443) B1116443
theorem B3174059 : Blo 880569 3174059 := bstep (se 1 (by rfl) ⟨2380544, by rfl⟩ : syracuseStep 3174059 = 4761089) B4761089
theorem B5664451 : Blo 880569 5664451 := bstep (se 1 (by rfl) ⟨4248338, by rfl⟩ : syracuseStep 5664451 = 8496677) B8496677
theorem B8580809 : Blo 880569 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B9531083 : Blo 880569 9531083 := bstep (se 1 (by rfl) ⟨7148312, by rfl⟩ : syracuseStep 9531083 = 14296625) B14296625
theorem B880671 : Blo 880569 880671 := bstep (se 1 (by rfl) ⟨660503, by rfl⟩ : syracuseStep 880671 = 1321007) B1321007
theorem B16969823 : Blo 880569 16969823 := bstep (se 1 (by rfl) ⟨12727367, by rfl⟩ : syracuseStep 16969823 = 25454735) B25454735
theorem B880847 : Blo 880569 880847 := bstep (se 1 (by rfl) ⟨660635, by rfl⟩ : syracuseStep 880847 = 1321271) B1321271
theorem B880967 : Blo 880569 880967 := bstep (se 1 (by rfl) ⟨660725, by rfl⟩ : syracuseStep 880967 = 1321451) B1321451
theorem B881435 : Blo 880569 881435 := bstep (se 1 (by rfl) ⟨661076, by rfl⟩ : syracuseStep 881435 = 1322153) B1322153
theorem B881711 : Blo 880569 881711 := bstep (se 1 (by rfl) ⟨661283, by rfl⟩ : syracuseStep 881711 = 1322567) B1322567
theorem B2389063 : Blo 880569 2389063 := bstep (se 1 (by rfl) ⟨1791797, by rfl⟩ : syracuseStep 2389063 = 3583595) B3583595
theorem B881831 : Blo 880569 881831 := bstep (se 1 (by rfl) ⟨661373, by rfl⟩ : syracuseStep 881831 = 1322747) B1322747
theorem B2979179 : Blo 880569 2979179 := bstep (se 1 (by rfl) ⟨2234384, by rfl⟩ : syracuseStep 2979179 = 4468769) B4468769
theorem B882279 : Blo 880569 882279 := bstep (se 1 (by rfl) ⟨661709, by rfl⟩ : syracuseStep 882279 = 1323419) B1323419
theorem B882559 : Blo 880569 882559 := bstep (se 1 (by rfl) ⟨661919, by rfl⟩ : syracuseStep 882559 = 1323839) B1323839
theorem B882655 : Blo 880569 882655 := bstep (se 1 (by rfl) ⟨661991, by rfl⟩ : syracuseStep 882655 = 1323983) B1323983
theorem B882683 : Blo 880569 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B882715 : Blo 880569 882715 := bstep (se 1 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 882715 = 1324073) B1324073
theorem B882735 : Blo 880569 882735 := bstep (se 1 (by rfl) ⟨662051, by rfl⟩ : syracuseStep 882735 = 1324103) B1324103
theorem B24115265 : Blo 880569 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B6715547 : Blo 880569 6715547 := bstep (se 1 (by rfl) ⟨5036660, by rfl⟩ : syracuseStep 6715547 = 10073321) B10073321
theorem B882855 : Blo 880569 882855 := bstep (se 1 (by rfl) ⟨662141, by rfl⟩ : syracuseStep 882855 = 1324283) B1324283
theorem B18381005 : Blo 880569 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B883679 : Blo 880569 883679 := bstep (se 1 (by rfl) ⟨662759, by rfl⟩ : syracuseStep 883679 = 1325519) B1325519
theorem B9534455 : Blo 880569 9534455 := bstep (se 1 (by rfl) ⟨7150841, by rfl⟩ : syracuseStep 9534455 = 14301683) B14301683
theorem B883739 : Blo 880569 883739 := bstep (se 1 (by rfl) ⟨662804, by rfl⟩ : syracuseStep 883739 = 1325609) B1325609
theorem B883867 : Blo 880569 883867 := bstep (se 1 (by rfl) ⟨662900, by rfl⟩ : syracuseStep 883867 = 1325801) B1325801
theorem B1637651 : Blo 880569 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B884123 : Blo 880569 884123 := bstep (se 1 (by rfl) ⟨663092, by rfl⟩ : syracuseStep 884123 = 1326185) B1326185
theorem B3767791 : Blo 880569 3767791 := bstep (se 1 (by rfl) ⟨2825843, by rfl⟩ : syracuseStep 3767791 = 5651687) B5651687
theorem B884207 : Blo 880569 884207 := bstep (se 1 (by rfl) ⟨663155, by rfl⟩ : syracuseStep 884207 = 1326311) B1326311
theorem B884543 : Blo 880569 884543 := bstep (se 1 (by rfl) ⟨663407, by rfl⟩ : syracuseStep 884543 = 1326815) B1326815
theorem B3178759 : Blo 880569 3178759 := bstep (se 1 (by rfl) ⟨2384069, by rfl⟩ : syracuseStep 3178759 = 4768139) B4768139
theorem B10715753 : Blo 880569 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B3769021 : Blo 880569 3769021 := bstep (se 3 (by rfl) ⟨706691, by rfl⟩ : syracuseStep 3769021 = 1413383) B1413383
theorem B9077833 : Blo 880569 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B1672319 : Blo 880569 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B7145135 : Blo 880569 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B3868355 : Blo 880569 3868355 := bstep (se 1 (by rfl) ⟨2901266, by rfl⟩ : syracuseStep 3868355 = 5802533) B5802533
theorem B3344105 : Blo 880569 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B5375783 : Blo 880569 5375783 := bstep (se 1 (by rfl) ⟨4031837, by rfl⟩ : syracuseStep 5375783 = 8063675) B8063675
theorem B1411487 : Blo 880569 1411487 := bstep (se 1 (by rfl) ⟨1058615, by rfl⟩ : syracuseStep 1411487 = 2117231) B2117231
theorem B2230841 : Blo 880569 2230841 := bstep (se 2 (by rfl) ⟨836565, by rfl⟩ : syracuseStep 2230841 = 1673131) B1673131
theorem B2231003 : Blo 880569 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B2984795 : Blo 880569 2984795 := bstep (se 1 (by rfl) ⟨2238596, by rfl⟩ : syracuseStep 2984795 = 4477193) B4477193
theorem B5737321 : Blo 880569 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B4459373 : Blo 880569 4459373 := bstep (se 3 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 4459373 = 1672265) B1672265
theorem B2984903 : Blo 880569 2984903 := bstep (se 1 (by rfl) ⟨2238677, by rfl⟩ : syracuseStep 2984903 = 4477355) B4477355
theorem B10063115 : Blo 880569 10063115 := bstep (se 1 (by rfl) ⟨7547336, by rfl⟩ : syracuseStep 10063115 = 15094673) B15094673
theorem B3346049 : Blo 880569 3346049 := bstep (se 2 (by rfl) ⟨1254768, by rfl⟩ : syracuseStep 3346049 = 2509537) B2509537
theorem B2232299 : Blo 880569 2232299 := bstep (se 1 (by rfl) ⟨1674224, by rfl⟩ : syracuseStep 2232299 = 3348449) B3348449
theorem B3772507 : Blo 880569 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B8590049 : Blo 880569 8590049 := bstep (se 2 (by rfl) ⟨3221268, by rfl⟩ : syracuseStep 8590049 = 6442537) B6442537
theorem B4461641 : Blo 880569 4461641 := bstep (se 2 (by rfl) ⟨1673115, by rfl⟩ : syracuseStep 4461641 = 3346231) B3346231
theorem B9540773 : Blo 880569 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B4461803 : Blo 880569 4461803 := bstep (se 1 (by rfl) ⟨3346352, by rfl⟩ : syracuseStep 4461803 = 6692705) B6692705
theorem B13604489 : Blo 880569 13604489 := bstep (se 2 (by rfl) ⟨5101683, by rfl⟩ : syracuseStep 13604489 = 10203367) B10203367
theorem B1677095 : Blo 880569 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B15046559 : Blo 880569 15046559 := bstep (se 1 (by rfl) ⟨11284919, by rfl⟩ : syracuseStep 15046559 = 22569839) B22569839
theorem B30284225 : Blo 880569 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B3185417 : Blo 880569 3185417 := bstep (se 2 (by rfl) ⟨1194531, by rfl⟩ : syracuseStep 3185417 = 2389063) B2389063
theorem B7249427 : Blo 880569 7249427 := bstep (se 1 (by rfl) ⟨5437070, by rfl⟩ : syracuseStep 7249427 = 10874141) B10874141
theorem B990751 : Blo 880569 990751 := bstep (se 1 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 990751 = 1486127) B1486127
theorem B11313215 : Blo 880569 11313215 := bstep (se 1 (by rfl) ⟨8484911, by rfl⟩ : syracuseStep 11313215 = 16969823) B16969823
theorem B991903 : Blo 880569 991903 := bstep (se 1 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 991903 = 1487855) B1487855
theorem B1254313 : Blo 880569 1254313 := bstep (se 2 (by rfl) ⟨470367, by rfl⟩ : syracuseStep 1254313 = 940735) B940735
theorem B3352535 : Blo 880569 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B5023721 : Blo 880569 5023721 := bstep (se 2 (by rfl) ⟨1883895, by rfl⟩ : syracuseStep 5023721 = 3767791) B3767791
theorem B4532203 : Blo 880569 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B1321097 : Blo 880569 1321097 := bstep (se 2 (by rfl) ⟨495411, by rfl⟩ : syracuseStep 1321097 = 990823) B990823
theorem B1091767 : Blo 880569 1091767 := bstep (se 1 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 1091767 = 1637651) B1637651
theorem B10201625 : Blo 880569 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B1321769 : Blo 880569 1321769 := bstep (se 2 (by rfl) ⟨495663, by rfl⟩ : syracuseStep 1321769 = 991327) B991327
theorem B2829113 : Blo 880569 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B1321961 : Blo 880569 1321961 := bstep (se 2 (by rfl) ⟨495735, by rfl⟩ : syracuseStep 1321961 = 991471) B991471
theorem B7154993 : Blo 880569 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B8039735 : Blo 880569 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B1486201 : Blo 880569 1486201 := bstep (se 2 (by rfl) ⟨557325, by rfl⟩ : syracuseStep 1486201 = 1114651) B1114651
theorem B1322447 : Blo 880569 1322447 := bstep (se 1 (by rfl) ⟨991835, by rfl⟩ : syracuseStep 1322447 = 1983671) B1983671
theorem B1322543 : Blo 880569 1322543 := bstep (se 1 (by rfl) ⟨991907, by rfl⟩ : syracuseStep 1322543 = 1983815) B1983815
theorem B1486903 : Blo 880569 1486903 := bstep (se 1 (by rfl) ⟨1115177, by rfl⟩ : syracuseStep 1486903 = 2230355) B2230355
theorem B5025887 : Blo 880569 5025887 := bstep (se 1 (by rfl) ⟨3769415, by rfl⟩ : syracuseStep 5025887 = 7538831) B7538831
theorem B1323215 : Blo 880569 1323215 := bstep (se 1 (by rfl) ⟨992411, by rfl⟩ : syracuseStep 1323215 = 1984823) B1984823
theorem B2863387 : Blo 880569 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B1323335 : Blo 880569 1323335 := bstep (se 1 (by rfl) ⟨992501, by rfl⟩ : syracuseStep 1323335 = 1985003) B1985003
theorem B1324127 : Blo 880569 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B1324187 : Blo 880569 1324187 := bstep (se 1 (by rfl) ⟨993140, by rfl⟩ : syracuseStep 1324187 = 1986281) B1986281
theorem B3355951 : Blo 880569 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B6370663 : Blo 880569 6370663 := bstep (se 1 (by rfl) ⟨4777997, by rfl⟩ : syracuseStep 6370663 = 9555995) B9555995
theorem B3356255 : Blo 880569 3356255 := bstep (se 1 (by rfl) ⟨2517191, by rfl⟩ : syracuseStep 3356255 = 5034383) B5034383
theorem B3356423 : Blo 880569 3356423 := bstep (se 1 (by rfl) ⟨2517317, by rfl⟩ : syracuseStep 3356423 = 5034635) B5034635
theorem B81573733 : Blo 880569 81573733 := bstep (se 4 (by rfl) ⟨7647537, by rfl⟩ : syracuseStep 81573733 = 15295075) B15295075
theorem B1325033 : Blo 880569 1325033 := bstep (se 2 (by rfl) ⟨496887, by rfl⟩ : syracuseStep 1325033 = 993775) B993775
theorem B1489279 : Blo 880569 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B34322899 : Blo 880569 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B1489387 : Blo 880569 1489387 := bstep (se 1 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 1489387 = 2234081) B2234081
theorem B1325663 : Blo 880569 1325663 := bstep (se 1 (by rfl) ⟨994247, by rfl⟩ : syracuseStep 1325663 = 1988495) B1988495
theorem B3357409 : Blo 880569 3357409 := bstep (se 2 (by rfl) ⟨1259028, by rfl⟩ : syracuseStep 3357409 = 2518057) B2518057
theorem B10861523 : Blo 880569 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B6699995 : Blo 880569 6699995 := bstep (se 1 (by rfl) ⟨5024996, by rfl⟩ : syracuseStep 6699995 = 10049993) B10049993
theorem B1326143 : Blo 880569 1326143 := bstep (se 1 (by rfl) ⟨994607, by rfl⟩ : syracuseStep 1326143 = 1989215) B1989215
theorem B1588385 : Blo 880569 1588385 := bstep (se 2 (by rfl) ⟨595644, by rfl⟩ : syracuseStep 1588385 = 1191289) B1191289
theorem B1326491 : Blo 880569 1326491 := bstep (se 1 (by rfl) ⟨994868, by rfl⟩ : syracuseStep 1326491 = 1989737) B1989737
theorem B7552601 : Blo 880569 7552601 := bstep (se 2 (by rfl) ⟨2832225, by rfl⟩ : syracuseStep 7552601 = 5664451) B5664451
theorem B1490683 : Blo 880569 1490683 := bstep (se 1 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 1490683 = 2236025) B2236025
theorem B1490825 : Blo 880569 1490825 := bstep (se 2 (by rfl) ⟨559059, by rfl⟩ : syracuseStep 1490825 = 1118119) B1118119
theorem B1982591 : Blo 880569 1982591 := bstep (se 1 (by rfl) ⟨1486943, by rfl⟩ : syracuseStep 1982591 = 2973887) B2973887
theorem B1491257 : Blo 880569 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B1983059 : Blo 880569 1983059 := bstep (se 1 (by rfl) ⟨1487294, by rfl⟩ : syracuseStep 1983059 = 2974589) B2974589
theorem B7848535 : Blo 880569 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B4473467 : Blo 880569 4473467 := bstep (se 1 (by rfl) ⟨3355100, by rfl⟩ : syracuseStep 4473467 = 6710201) B6710201
theorem B1491689 : Blo 880569 1491689 := bstep (se 2 (by rfl) ⟨559383, by rfl⟩ : syracuseStep 1491689 = 1118767) B1118767
theorem B4244687 : Blo 880569 4244687 := bstep (se 1 (by rfl) ⟨3183515, by rfl⟩ : syracuseStep 4244687 = 6367031) B6367031
theorem B1885673 : Blo 880569 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B1492553 : Blo 880569 1492553 := bstep (se 2 (by rfl) ⟨559707, by rfl⟩ : syracuseStep 1492553 = 1119415) B1119415
theorem B5031719 : Blo 880569 5031719 := bstep (se 1 (by rfl) ⟨3773789, by rfl⟩ : syracuseStep 5031719 = 7547579) B7547579
theorem B25806721 : Blo 880569 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B1984427 : Blo 880569 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B16107497 : Blo 880569 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B4475087 : Blo 880569 4475087 := bstep (se 1 (by rfl) ⟨3356315, by rfl⟩ : syracuseStep 4475087 = 6712631) B6712631
theorem B1984787 : Blo 880569 1984787 := bstep (se 1 (by rfl) ⟨1488590, by rfl⟩ : syracuseStep 1984787 = 2977181) B2977181
theorem B20367773 : Blo 880569 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B2116039 : Blo 880569 2116039 := bstep (se 1 (by rfl) ⟨1587029, by rfl⟩ : syracuseStep 2116039 = 3174059) B3174059
theorem B5720539 : Blo 880569 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B22596083 : Blo 880569 22596083 := bstep (se 1 (by rfl) ⟨16947062, by rfl⟩ : syracuseStep 22596083 = 33894125) B33894125
theorem B7555949 : Blo 880569 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B2510153 : Blo 880569 2510153 := bstep (se 2 (by rfl) ⟨941307, by rfl⟩ : syracuseStep 2510153 = 1882615) B1882615
theorem B1986119 : Blo 880569 1986119 := bstep (se 1 (by rfl) ⟨1489589, by rfl⟩ : syracuseStep 1986119 = 2979179) B2979179
theorem B16076843 : Blo 880569 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B4477031 : Blo 880569 4477031 := bstep (se 1 (by rfl) ⟨3357773, by rfl⟩ : syracuseStep 4477031 = 6715547) B6715547
theorem B1986785 : Blo 880569 1986785 := bstep (se 2 (by rfl) ⟨745044, by rfl⟩ : syracuseStep 1986785 = 1490089) B1490089
theorem B4248071 : Blo 880569 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B193090229 : Blo 880569 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B2971943 : Blo 880569 2971943 := bstep (se 1 (by rfl) ⟨2228957, by rfl⟩ : syracuseStep 2971943 = 4457915) B4457915
theorem B2972807 : Blo 880569 2972807 := bstep (se 1 (by rfl) ⟨2229605, by rfl⟩ : syracuseStep 2972807 = 4459211) B4459211
theorem B9067697 : Blo 880569 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B10051451 : Blo 880569 10051451 := bstep (se 1 (by rfl) ⟨7538588, by rfl⟩ : syracuseStep 10051451 = 15077177) B15077177
theorem B2973671 : Blo 880569 2973671 := bstep (se 1 (by rfl) ⟨2230253, by rfl⟩ : syracuseStep 2973671 = 4460507) B4460507
theorem B2515187 : Blo 880569 2515187 := bstep (se 1 (by rfl) ⟨1886390, by rfl⟩ : syracuseStep 2515187 = 3772781) B3772781
theorem B6709715 : Blo 880569 6709715 := bstep (se 1 (by rfl) ⟨5032286, by rfl⟩ : syracuseStep 6709715 = 10064573) B10064573
theorem B9528191 : Blo 880569 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B2974697 : Blo 880569 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B13985329 : Blo 880569 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B2516827 : Blo 880569 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B2516987 : Blo 880569 2516987 := bstep (se 1 (by rfl) ⟨1887740, by rfl⟩ : syracuseStep 2516987 = 3775481) B3775481
theorem B3828065 : Blo 880569 3828065 := bstep (se 2 (by rfl) ⟨1435524, by rfl⟩ : syracuseStep 3828065 = 2871049) B2871049
theorem B2976371 : Blo 880569 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B27224747 : Blo 880569 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B2976479 : Blo 880569 2976479 := bstep (se 1 (by rfl) ⟨2232359, by rfl⟩ : syracuseStep 2976479 = 4464719) B4464719
theorem B10054367 : Blo 880569 10054367 := bstep (se 1 (by rfl) ⟨7540775, by rfl⟩ : syracuseStep 10054367 = 15081551) B15081551
theorem B2518559 : Blo 880569 2518559 := bstep (se 1 (by rfl) ⟨1888919, by rfl⟩ : syracuseStep 2518559 = 3777839) B3777839
theorem B2977451 : Blo 880569 2977451 := bstep (se 1 (by rfl) ⟨2233088, by rfl⟩ : syracuseStep 2977451 = 4466177) B4466177
theorem B880895 : Blo 880569 880895 := bstep (se 1 (by rfl) ⟨660671, by rfl⟩ : syracuseStep 880895 = 1321343) B1321343
theorem B881055 : Blo 880569 881055 := bstep (se 1 (by rfl) ⟨660791, by rfl⟩ : syracuseStep 881055 = 1321583) B1321583
theorem B881199 : Blo 880569 881199 := bstep (se 1 (by rfl) ⟨660899, by rfl⟩ : syracuseStep 881199 = 1321799) B1321799
theorem B881599 : Blo 880569 881599 := bstep (se 1 (by rfl) ⟨661199, by rfl⟩ : syracuseStep 881599 = 1322399) B1322399
theorem B881775 : Blo 880569 881775 := bstep (se 1 (by rfl) ⟨661331, by rfl⟩ : syracuseStep 881775 = 1322663) B1322663
theorem B881791 : Blo 880569 881791 := bstep (se 1 (by rfl) ⟨661343, by rfl⟩ : syracuseStep 881791 = 1322687) B1322687
theorem B6354055 : Blo 880569 6354055 := bstep (se 1 (by rfl) ⟨4765541, by rfl⟩ : syracuseStep 6354055 = 9531083) B9531083
theorem B881855 : Blo 880569 881855 := bstep (se 1 (by rfl) ⟨661391, by rfl⟩ : syracuseStep 881855 = 1322783) B1322783
theorem B3765467 : Blo 880569 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B882047 : Blo 880569 882047 := bstep (se 1 (by rfl) ⟨661535, by rfl⟩ : syracuseStep 882047 = 1323071) B1323071
theorem B8484263 : Blo 880569 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B882175 : Blo 880569 882175 := bstep (se 1 (by rfl) ⟨661631, by rfl⟩ : syracuseStep 882175 = 1323263) B1323263
theorem B882203 : Blo 880569 882203 := bstep (se 1 (by rfl) ⟨661652, by rfl⟩ : syracuseStep 882203 = 1323305) B1323305
theorem B6780449 : Blo 880569 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B2389583 : Blo 880569 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B2979449 : Blo 880569 2979449 := bstep (se 2 (by rfl) ⟨1117293, by rfl⟩ : syracuseStep 2979449 = 2234587) B2234587
theorem B882383 : Blo 880569 882383 := bstep (se 1 (by rfl) ⟨661787, by rfl⟩ : syracuseStep 882383 = 1323575) B1323575
theorem B882543 : Blo 880569 882543 := bstep (se 1 (by rfl) ⟨661907, by rfl⟩ : syracuseStep 882543 = 1323815) B1323815
theorem B2979773 : Blo 880569 2979773 := bstep (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) B1117415
theorem B882623 : Blo 880569 882623 := bstep (se 1 (by rfl) ⟨661967, by rfl⟩ : syracuseStep 882623 = 1323935) B1323935
theorem B2979881 : Blo 880569 2979881 := bstep (se 2 (by rfl) ⟨1117455, by rfl⟩ : syracuseStep 2979881 = 2234911) B2234911
theorem B882939 : Blo 880569 882939 := bstep (se 1 (by rfl) ⟨662204, by rfl⟩ : syracuseStep 882939 = 1324409) B1324409
theorem B882943 : Blo 880569 882943 := bstep (se 1 (by rfl) ⟨662207, by rfl⟩ : syracuseStep 882943 = 1324415) B1324415
theorem B883047 : Blo 880569 883047 := bstep (se 1 (by rfl) ⟨662285, by rfl⟩ : syracuseStep 883047 = 1324571) B1324571
theorem B883167 : Blo 880569 883167 := bstep (se 1 (by rfl) ⟨662375, by rfl⟩ : syracuseStep 883167 = 1324751) B1324751
theorem B883303 : Blo 880569 883303 := bstep (se 1 (by rfl) ⟨662477, by rfl⟩ : syracuseStep 883303 = 1324955) B1324955
theorem B883327 : Blo 880569 883327 := bstep (se 1 (by rfl) ⟨662495, by rfl⟩ : syracuseStep 883327 = 1324991) B1324991
theorem B883439 : Blo 880569 883439 := bstep (se 1 (by rfl) ⟨662579, by rfl⟩ : syracuseStep 883439 = 1325159) B1325159
theorem B12254003 : Blo 880569 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B883695 : Blo 880569 883695 := bstep (se 1 (by rfl) ⟨662771, by rfl⟩ : syracuseStep 883695 = 1325543) B1325543
theorem B10058741 : Blo 880569 10058741 := bstep (se 5 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 10058741 = 943007) B943007
theorem B883743 : Blo 880569 883743 := bstep (se 1 (by rfl) ⟨662807, by rfl⟩ : syracuseStep 883743 = 1325615) B1325615
theorem B6356303 : Blo 880569 6356303 := bstep (se 1 (by rfl) ⟨4767227, by rfl⟩ : syracuseStep 6356303 = 9534455) B9534455
theorem B884191 : Blo 880569 884191 := bstep (se 1 (by rfl) ⟨663143, by rfl⟩ : syracuseStep 884191 = 1326287) B1326287
theorem B884251 : Blo 880569 884251 := bstep (se 1 (by rfl) ⟨663188, by rfl⟩ : syracuseStep 884251 = 1326377) B1326377
theorem B884271 : Blo 880569 884271 := bstep (se 1 (by rfl) ⟨663203, by rfl⟩ : syracuseStep 884271 = 1326407) B1326407
theorem B2981771 : Blo 880569 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B2982311 : Blo 880569 2982311 := bstep (se 1 (by rfl) ⟨2236733, by rfl⟩ : syracuseStep 2982311 = 4473467) B4473467
theorem B1114879 : Blo 880569 1114879 := bstep (se 1 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 1114879 = 1672319) B1672319
theorem B2229403 : Blo 880569 2229403 := bstep (se 1 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 2229403 = 3344105) B3344105
theorem B1672417 : Blo 880569 1672417 := bstep (se 2 (by rfl) ⟨627156, by rfl⟩ : syracuseStep 1672417 = 1254313) B1254313
theorem B2983391 : Blo 880569 2983391 := bstep (se 1 (by rfl) ⟨2237543, by rfl⟩ : syracuseStep 2983391 = 4475087) B4475087
theorem B28575341 : Blo 880569 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B18647105 : Blo 880569 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B1673435 : Blo 880569 1673435 := bstep (se 1 (by rfl) ⟨1255076, by rfl⟩ : syracuseStep 1673435 = 2510153) B2510153
theorem B2230699 : Blo 880569 2230699 := bstep (se 1 (by rfl) ⟨1673024, by rfl⟩ : syracuseStep 2230699 = 3346049) B3346049
theorem B34408961 : Blo 880569 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B10717895 : Blo 880569 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B2984687 : Blo 880569 2984687 := bstep (se 1 (by rfl) ⟨2238515, by rfl⟩ : syracuseStep 2984687 = 4477031) B4477031
theorem B2821385 : Blo 880569 2821385 := bstep (se 2 (by rfl) ⟨1058019, by rfl⟩ : syracuseStep 2821385 = 2116039) B2116039
theorem B6360515 : Blo 880569 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B40832693 : Blo 880569 40832693 := bstep (se 5 (by rfl) ⟨1914032, by rfl⟩ : syracuseStep 40832693 = 3828065) B3828065
theorem B1118063 : Blo 880569 1118063 := bstep (se 1 (by rfl) ⟨838547, by rfl⟩ : syracuseStep 1118063 = 1677095) B1677095
theorem B10031039 : Blo 880569 10031039 := bstep (se 1 (by rfl) ⟨7523279, by rfl⟩ : syracuseStep 10031039 = 15046559) B15046559
theorem B20189483 : Blo 880569 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B7542143 : Blo 880569 7542143 := bstep (se 1 (by rfl) ⟨5656607, by rfl⟩ : syracuseStep 7542143 = 11313215) B11313215
theorem B1676791 : Blo 880569 1676791 := bstep (se 1 (by rfl) ⟨1257593, by rfl⟩ : syracuseStep 1676791 = 2515187) B2515187
theorem B2235023 : Blo 880569 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B3349147 : Blo 880569 3349147 := bstep (se 1 (by rfl) ⟨2511860, by rfl⟩ : syracuseStep 3349147 = 5023721) B5023721
theorem B1677991 : Blo 880569 1677991 := bstep (se 1 (by rfl) ⟨1258493, by rfl⟩ : syracuseStep 1677991 = 2516987) B2516987
theorem B8494217 : Blo 880569 8494217 := bstep (se 2 (by rfl) ⟨3185331, by rfl⟩ : syracuseStep 8494217 = 6370663) B6370663
theorem B8494445 : Blo 880569 8494445 := bstep (se 3 (by rfl) ⟨1592708, by rfl⟩ : syracuseStep 8494445 = 3185417) B3185417
theorem B1679039 : Blo 880569 1679039 := bstep (se 1 (by rfl) ⟨1259279, by rfl⟩ : syracuseStep 1679039 = 2518559) B2518559
theorem B108764977 : Blo 880569 108764977 := bstep (se 2 (by rfl) ⟨40786866, by rfl⟩ : syracuseStep 108764977 = 81573733) B81573733
theorem B3350591 : Blo 880569 3350591 := bstep (se 1 (by rfl) ⟨2512943, by rfl⟩ : syracuseStep 3350591 = 5025887) B5025887
theorem B19079981 : Blo 880569 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B2237503 : Blo 880569 2237503 := bstep (se 1 (by rfl) ⟨1678127, by rfl⟩ : syracuseStep 2237503 = 3356255) B3356255
theorem B2237615 : Blo 880569 2237615 := bstep (se 1 (by rfl) ⟨1678211, by rfl⟩ : syracuseStep 2237615 = 3356423) B3356423
theorem B8169335 : Blo 880569 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B4466663 : Blo 880569 4466663 := bstep (se 1 (by rfl) ⟨3349997, by rfl⟩ : syracuseStep 4466663 = 6699995) B6699995
theorem B1321001 : Blo 880569 1321001 := bstep (se 2 (by rfl) ⟨495375, by rfl⟩ : syracuseStep 1321001 = 990751) B990751
theorem B1058923 : Blo 880569 1058923 := bstep (se 1 (by rfl) ⟨794192, by rfl⟩ : syracuseStep 1058923 = 1588385) B1588385
theorem B4237535 : Blo 880569 4237535 := bstep (se 1 (by rfl) ⟨3178151, by rfl⟩ : syracuseStep 4237535 = 6356303) B6356303
theorem B993883 : Blo 880569 993883 := bstep (se 1 (by rfl) ⟨745412, by rfl⟩ : syracuseStep 993883 = 1490825) B1490825
theorem B1321727 : Blo 880569 1321727 := bstep (se 1 (by rfl) ⟨991295, by rfl⟩ : syracuseStep 1321727 = 1982591) B1982591
theorem B994171 : Blo 880569 994171 := bstep (se 1 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 994171 = 1491257) B1491257
theorem B4238345 : Blo 880569 4238345 := bstep (se 2 (by rfl) ⟨1589379, by rfl⟩ : syracuseStep 4238345 = 3178759) B3178759
theorem B1322039 : Blo 880569 1322039 := bstep (se 1 (by rfl) ⟨991529, by rfl⟩ : syracuseStep 1322039 = 1983059) B1983059
theorem B994459 : Blo 880569 994459 := bstep (se 1 (by rfl) ⟨745844, by rfl⟩ : syracuseStep 994459 = 1491689) B1491689
theorem B10464713 : Blo 880569 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B2829791 : Blo 880569 2829791 := bstep (se 1 (by rfl) ⟨2122343, by rfl⟩ : syracuseStep 2829791 = 4244687) B4244687
theorem B1322537 : Blo 880569 1322537 := bstep (se 2 (by rfl) ⟨495951, by rfl⟩ : syracuseStep 1322537 = 991903) B991903
theorem B5025361 : Blo 880569 5025361 := bstep (se 2 (by rfl) ⟨1884510, by rfl⟩ : syracuseStep 5025361 = 3769021) B3769021
theorem B1257115 : Blo 880569 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B995035 : Blo 880569 995035 := bstep (se 1 (by rfl) ⟨746276, by rfl⟩ : syracuseStep 995035 = 1492553) B1492553
theorem B4763423 : Blo 880569 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B3354479 : Blo 880569 3354479 := bstep (se 1 (by rfl) ⟨2515859, by rfl⟩ : syracuseStep 3354479 = 5031719) B5031719
theorem B3583855 : Blo 880569 3583855 := bstep (se 1 (by rfl) ⟨2687891, by rfl⟩ : syracuseStep 3583855 = 5375783) B5375783
theorem B1322951 : Blo 880569 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B12103777 : Blo 880569 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B1323191 : Blo 880569 1323191 := bstep (se 1 (by rfl) ⟨992393, by rfl⟩ : syracuseStep 1323191 = 1984787) B1984787
theorem B13578515 : Blo 880569 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B1487227 : Blo 880569 1487227 := bstep (se 1 (by rfl) ⟨1115420, by rfl⟩ : syracuseStep 1487227 = 2230841) B2230841
theorem B1487335 : Blo 880569 1487335 := bstep (se 1 (by rfl) ⟨1115501, by rfl⟩ : syracuseStep 1487335 = 2231003) B2231003
theorem B1324079 : Blo 880569 1324079 := bstep (se 1 (by rfl) ⟨993059, by rfl⟩ : syracuseStep 1324079 = 1986119) B1986119
theorem B3355769 : Blo 880569 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B6042937 : Blo 880569 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B1488199 : Blo 880569 1488199 := bstep (se 1 (by rfl) ⟨1116149, by rfl⟩ : syracuseStep 1488199 = 2232299) B2232299
theorem B1324523 : Blo 880569 1324523 := bstep (se 1 (by rfl) ⟨993392, by rfl⟩ : syracuseStep 1324523 = 1986785) B1986785
theorem B1455689 : Blo 880569 1455689 := bstep (se 2 (by rfl) ⟨545883, by rfl⟩ : syracuseStep 1455689 = 1091767) B1091767
theorem B2832047 : Blo 880569 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B128726819 : Blo 880569 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B10041245 : Blo 880569 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B7649761 : Blo 880569 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B1981295 : Blo 880569 1981295 := bstep (se 1 (by rfl) ⟨1485971, by rfl⟩ : syracuseStep 1981295 = 2971943) B2971943
theorem B1981601 : Blo 880569 1981601 := bstep (se 2 (by rfl) ⟨743100, by rfl⟩ : syracuseStep 1981601 = 1486201) B1486201
theorem B1981871 : Blo 880569 1981871 := bstep (se 1 (by rfl) ⟨1486403, by rfl⟩ : syracuseStep 1981871 = 2972807) B2972807
theorem B6045131 : Blo 880569 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B4832951 : Blo 880569 4832951 := bstep (se 1 (by rfl) ⟨3624713, by rfl⟩ : syracuseStep 4832951 = 7249427) B7249427
theorem B6700967 : Blo 880569 6700967 := bstep (se 1 (by rfl) ⟨5025725, by rfl⟩ : syracuseStep 6700967 = 10051451) B10051451
theorem B1982447 : Blo 880569 1982447 := bstep (se 1 (by rfl) ⟨1486835, by rfl⟩ : syracuseStep 1982447 = 2973671) B2973671
theorem B1982537 : Blo 880569 1982537 := bstep (se 2 (by rfl) ⟨743451, by rfl⟩ : syracuseStep 1982537 = 1486903) B1486903
theorem B5030009 : Blo 880569 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B4473143 : Blo 880569 4473143 := bstep (se 1 (by rfl) ⟨3354857, by rfl⟩ : syracuseStep 4473143 = 6709715) B6709715
theorem B3817849 : Blo 880569 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B1983131 : Blo 880569 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B8472073 : Blo 880569 8472073 := bstep (se 2 (by rfl) ⟨3177027, by rfl⟩ : syracuseStep 8472073 = 6354055) B6354055
theorem B6801083 : Blo 880569 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B4474601 : Blo 880569 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B1984247 : Blo 880569 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B1984319 : Blo 880569 1984319 := bstep (se 1 (by rfl) ⟨1488239, by rfl⟩ : syracuseStep 1984319 = 2976479) B2976479
theorem B6702911 : Blo 880569 6702911 := bstep (se 1 (by rfl) ⟨5027183, by rfl⟩ : syracuseStep 6702911 = 10054367) B10054367
theorem B1886075 : Blo 880569 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B5359823 : Blo 880569 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B1984967 : Blo 880569 1984967 := bstep (se 1 (by rfl) ⟨1488725, by rfl⟩ : syracuseStep 1984967 = 2977451) B2977451
theorem B1985705 : Blo 880569 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B45763865 : Blo 880569 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B1985849 : Blo 880569 1985849 := bstep (se 2 (by rfl) ⟨744693, by rfl⟩ : syracuseStep 1985849 = 1489387) B1489387
theorem B5656175 : Blo 880569 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B4476545 : Blo 880569 4476545 := bstep (se 2 (by rfl) ⟨1678704, by rfl⟩ : syracuseStep 4476545 = 3357409) B3357409
theorem B1593055 : Blo 880569 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B1986299 : Blo 880569 1986299 := bstep (se 1 (by rfl) ⟨1489724, by rfl⟩ : syracuseStep 1986299 = 2979449) B2979449
theorem B1986515 : Blo 880569 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B1986587 : Blo 880569 1986587 := bstep (se 1 (by rfl) ⟨1489940, by rfl⟩ : syracuseStep 1986587 = 2979881) B2979881
theorem B6705827 : Blo 880569 6705827 := bstep (se 1 (by rfl) ⟨5029370, by rfl⟩ : syracuseStep 6705827 = 10058741) B10058741
theorem B1987577 : Blo 880569 1987577 := bstep (se 2 (by rfl) ⟨745341, by rfl⟩ : syracuseStep 1987577 = 1490683) B1490683
theorem B5035067 : Blo 880569 5035067 := bstep (se 1 (by rfl) ⟨3776300, by rfl⟩ : syracuseStep 5035067 = 7552601) B7552601
theorem B1987847 : Blo 880569 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B10738331 : Blo 880569 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B940991 : Blo 880569 940991 := bstep (se 1 (by rfl) ⟨705743, by rfl⟩ : syracuseStep 940991 = 1411487) B1411487
theorem B15064055 : Blo 880569 15064055 := bstep (se 1 (by rfl) ⟨11298041, by rfl⟩ : syracuseStep 15064055 = 22596083) B22596083
theorem B1989863 : Blo 880569 1989863 := bstep (se 1 (by rfl) ⟨1492397, by rfl⟩ : syracuseStep 1989863 = 2984795) B2984795
theorem B2972915 : Blo 880569 2972915 := bstep (se 1 (by rfl) ⟨2229686, by rfl⟩ : syracuseStep 2972915 = 4459373) B4459373
theorem B5037299 : Blo 880569 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B1989935 : Blo 880569 1989935 := bstep (se 1 (by rfl) ⟨1492451, by rfl⟩ : syracuseStep 1989935 = 2984903) B2984903
theorem B6708743 : Blo 880569 6708743 := bstep (se 1 (by rfl) ⟨5031557, by rfl⟩ : syracuseStep 6708743 = 10063115) B10063115
theorem B5726699 : Blo 880569 5726699 := bstep (se 1 (by rfl) ⟨4295024, by rfl⟩ : syracuseStep 5726699 = 8590049) B8590049
theorem B7627385 : Blo 880569 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B2974427 : Blo 880569 2974427 := bstep (se 1 (by rfl) ⟨2230820, by rfl⟩ : syracuseStep 2974427 = 4461641) B4461641
theorem B2974535 : Blo 880569 2974535 := bstep (se 1 (by rfl) ⟨2230901, by rfl⟩ : syracuseStep 2974535 = 4461803) B4461803
theorem B9069659 : Blo 880569 9069659 := bstep (se 1 (by rfl) ⟨6802244, by rfl⟩ : syracuseStep 9069659 = 13604489) B13604489
theorem B10315613 : Blo 880569 10315613 := bstep (se 3 (by rfl) ⟨1934177, by rfl⟩ : syracuseStep 10315613 = 3868355) B3868355
theorem B6352127 : Blo 880569 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B880731 : Blo 880569 880731 := bstep (se 1 (by rfl) ⟨660548, by rfl⟩ : syracuseStep 880731 = 1321097) B1321097
theorem B18149831 : Blo 880569 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B881179 : Blo 880569 881179 := bstep (se 1 (by rfl) ⟨660884, by rfl⟩ : syracuseStep 881179 = 1321769) B1321769
theorem B881307 : Blo 880569 881307 := bstep (se 1 (by rfl) ⟨660980, by rfl⟩ : syracuseStep 881307 = 1321961) B1321961
theorem B881631 : Blo 880569 881631 := bstep (se 1 (by rfl) ⟨661223, by rfl⟩ : syracuseStep 881631 = 1322447) B1322447
theorem B881695 : Blo 880569 881695 := bstep (se 1 (by rfl) ⟨661271, by rfl⟩ : syracuseStep 881695 = 1322543) B1322543
theorem B882143 : Blo 880569 882143 := bstep (se 1 (by rfl) ⟨661607, by rfl⟩ : syracuseStep 882143 = 1323215) B1323215
theorem B882223 : Blo 880569 882223 := bstep (se 1 (by rfl) ⟨661667, by rfl⟩ : syracuseStep 882223 = 1323335) B1323335
theorem B882751 : Blo 880569 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B882791 : Blo 880569 882791 := bstep (se 1 (by rfl) ⟨662093, by rfl⟩ : syracuseStep 882791 = 1324187) B1324187
theorem B4520299 : Blo 880569 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B883355 : Blo 880569 883355 := bstep (se 1 (by rfl) ⟨662516, by rfl⟩ : syracuseStep 883355 = 1325033) B1325033
theorem B883775 : Blo 880569 883775 := bstep (se 1 (by rfl) ⟨662831, by rfl⟩ : syracuseStep 883775 = 1325663) B1325663
theorem B7241015 : Blo 880569 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B884095 : Blo 880569 884095 := bstep (se 1 (by rfl) ⟨663071, by rfl⟩ : syracuseStep 884095 = 1326143) B1326143
theorem B884327 : Blo 880569 884327 := bstep (se 1 (by rfl) ⟨663245, by rfl⟩ : syracuseStep 884327 = 1326491) B1326491
theorem B2982095 : Blo 880569 2982095 := bstep (se 1 (by rfl) ⟨2236571, by rfl⟩ : syracuseStep 2982095 = 4473143) B4473143
theorem B2983067 : Blo 880569 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B2983337 : Blo 880569 2983337 := bstep (se 2 (by rfl) ⟨1118751, by rfl⟩ : syracuseStep 2983337 = 2237503) B2237503
theorem B3573215 : Blo 880569 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1115623 : Blo 880569 1115623 := bstep (se 1 (by rfl) ⟨836717, by rfl⟩ : syracuseStep 1115623 = 1673435) B1673435
theorem B2229889 : Blo 880569 2229889 := bstep (se 2 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 2229889 = 1672417) B1672417
theorem B22939307 : Blo 880569 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B7145263 : Blo 880569 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B30509243 : Blo 880569 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B3770783 : Blo 880569 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B2984363 : Blo 880569 2984363 := bstep (se 1 (by rfl) ⟨2238272, by rfl⟩ : syracuseStep 2984363 = 4476545) B4476545
theorem B6687359 : Blo 880569 6687359 := bstep (se 1 (by rfl) ⟨5015519, by rfl⟩ : syracuseStep 6687359 = 10031039) B10031039
theorem B1411897 : Blo 880569 1411897 := bstep (se 2 (by rfl) ⟨529461, by rfl⟩ : syracuseStep 1411897 = 1058923) B1058923
theorem B1676153 : Blo 880569 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B1119359 : Blo 880569 1119359 := bstep (se 1 (by rfl) ⟨839519, by rfl⟩ : syracuseStep 1119359 = 1679039) B1679039
theorem B2233727 : Blo 880569 2233727 := bstep (se 1 (by rfl) ⟨1675295, by rfl⟩ : syracuseStep 2233727 = 3350591) B3350591
theorem B12719987 : Blo 880569 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B5446223 : Blo 880569 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B2235721 : Blo 880569 2235721 := bstep (se 2 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 2235721 = 1676791) B1676791
theorem B2825563 : Blo 880569 2825563 := bstep (se 1 (by rfl) ⟨2119172, by rfl⟩ : syracuseStep 2825563 = 4238345) B4238345
theorem B4234751 : Blo 880569 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B2236319 : Blo 880569 2236319 := bstep (se 1 (by rfl) ⟨1677239, by rfl⟩ : syracuseStep 2236319 = 3354479) B3354479
theorem B9052343 : Blo 880569 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B12099887 : Blo 880569 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B10199681 : Blo 880569 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B2237179 : Blo 880569 2237179 := bstep (se 1 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 2237179 = 3355769) B3355769
theorem B19309373 : Blo 880569 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B4465529 : Blo 880569 4465529 := bstep (se 2 (by rfl) ⟨1674573, by rfl⟩ : syracuseStep 4465529 = 3349147) B3349147
theorem B2237321 : Blo 880569 2237321 := bstep (se 2 (by rfl) ⟨838995, by rfl⟩ : syracuseStep 2237321 = 1677991) B1677991
theorem B6694163 : Blo 880569 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B12887869 : Blo 880569 12887869 := bstep (se 3 (by rfl) ⟨2416475, by rfl⟩ : syracuseStep 12887869 = 4832951) B4832951
theorem B1320863 : Blo 880569 1320863 := bstep (se 1 (by rfl) ⟨990647, by rfl⟩ : syracuseStep 1320863 = 1981295) B1981295
theorem B1321067 : Blo 880569 1321067 := bstep (se 1 (by rfl) ⟨990800, by rfl⟩ : syracuseStep 1321067 = 1981601) B1981601
theorem B1321247 : Blo 880569 1321247 := bstep (se 1 (by rfl) ⟨990935, by rfl⟩ : syracuseStep 1321247 = 1981871) B1981871
theorem B4467311 : Blo 880569 4467311 := bstep (se 1 (by rfl) ⟨3350483, by rfl⟩ : syracuseStep 4467311 = 6700967) B6700967
theorem B1321631 : Blo 880569 1321631 := bstep (se 1 (by rfl) ⟨991223, by rfl⟩ : syracuseStep 1321631 = 1982447) B1982447
theorem B1321691 : Blo 880569 1321691 := bstep (se 1 (by rfl) ⟨991268, by rfl⟩ : syracuseStep 1321691 = 1982537) B1982537
theorem B3353339 : Blo 880569 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B1322087 : Blo 880569 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B5090465 : Blo 880569 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B1486505 : Blo 880569 1486505 := bstep (se 2 (by rfl) ⟨557439, by rfl⟩ : syracuseStep 1486505 = 1114879) B1114879
theorem B19050227 : Blo 880569 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B4534055 : Blo 880569 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B1322831 : Blo 880569 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B1322879 : Blo 880569 1322879 := bstep (se 1 (by rfl) ⟨992159, by rfl⟩ : syracuseStep 1322879 = 1984319) B1984319
theorem B4468607 : Blo 880569 4468607 := bstep (se 1 (by rfl) ⟨3351455, by rfl⟩ : syracuseStep 4468607 = 6702911) B6702911
theorem B1257383 : Blo 880569 1257383 := bstep (se 1 (by rfl) ⟨943037, by rfl⟩ : syracuseStep 1257383 = 1886075) B1886075
theorem B1323311 : Blo 880569 1323311 := bstep (se 1 (by rfl) ⟨992483, by rfl⟩ : syracuseStep 1323311 = 1984967) B1984967
theorem B1323803 : Blo 880569 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1880923 : Blo 880569 1880923 := bstep (se 1 (by rfl) ⟨1410692, by rfl⟩ : syracuseStep 1880923 = 2821385) B2821385
theorem B1323899 : Blo 880569 1323899 := bstep (se 1 (by rfl) ⟨992924, by rfl⟩ : syracuseStep 1323899 = 1985849) B1985849
theorem B4240343 : Blo 880569 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B1324199 : Blo 880569 1324199 := bstep (se 1 (by rfl) ⟨993149, by rfl⟩ : syracuseStep 1324199 = 1986299) B1986299
theorem B1324343 : Blo 880569 1324343 := bstep (se 1 (by rfl) ⟨993257, by rfl⟩ : syracuseStep 1324343 = 1986515) B1986515
theorem B1324391 : Blo 880569 1324391 := bstep (se 1 (by rfl) ⟨993293, by rfl⟩ : syracuseStep 1324391 = 1986587) B1986587
theorem B4470551 : Blo 880569 4470551 := bstep (se 1 (by rfl) ⟨3352913, by rfl⟩ : syracuseStep 4470551 = 6705827) B6705827
theorem B1325051 : Blo 880569 1325051 := bstep (se 1 (by rfl) ⟨993788, by rfl⟩ : syracuseStep 1325051 = 1987577) B1987577
theorem B3356711 : Blo 880569 3356711 := bstep (se 1 (by rfl) ⟨2517533, by rfl⟩ : syracuseStep 3356711 = 5035067) B5035067
theorem B1325177 : Blo 880569 1325177 := bstep (se 2 (by rfl) ⟨496941, by rfl⟩ : syracuseStep 1325177 = 993883) B993883
theorem B1325231 : Blo 880569 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B5028095 : Blo 880569 5028095 := bstep (se 1 (by rfl) ⟨3771071, by rfl⟩ : syracuseStep 5028095 = 7542143) B7542143
theorem B1325561 : Blo 880569 1325561 := bstep (se 2 (by rfl) ⟨497085, by rfl⟩ : syracuseStep 1325561 = 994171) B994171
theorem B1325945 : Blo 880569 1325945 := bstep (se 2 (by rfl) ⟨497229, by rfl⟩ : syracuseStep 1325945 = 994459) B994459
theorem B1490015 : Blo 880569 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B7158887 : Blo 880569 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B10042703 : Blo 880569 10042703 := bstep (se 1 (by rfl) ⟨7532027, by rfl⟩ : syracuseStep 10042703 = 15064055) B15064055
theorem B6700481 : Blo 880569 6700481 := bstep (se 2 (by rfl) ⟨2512680, by rfl⟩ : syracuseStep 6700481 = 5025361) B5025361
theorem B1326575 : Blo 880569 1326575 := bstep (se 1 (by rfl) ⟨994931, by rfl⟩ : syracuseStep 1326575 = 1989863) B1989863
theorem B1981943 : Blo 880569 1981943 := bstep (se 1 (by rfl) ⟨1486457, by rfl⟩ : syracuseStep 1981943 = 2972915) B2972915
theorem B3358199 : Blo 880569 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B1326623 : Blo 880569 1326623 := bstep (se 1 (by rfl) ⟨994967, by rfl⟩ : syracuseStep 1326623 = 1989935) B1989935
theorem B27508301 : Blo 880569 27508301 := bstep (se 3 (by rfl) ⟨5157806, by rfl⟩ : syracuseStep 27508301 = 10315613) B10315613
theorem B1326713 : Blo 880569 1326713 := bstep (se 2 (by rfl) ⟨497517, by rfl⟩ : syracuseStep 1326713 = 995035) B995035
theorem B4472495 : Blo 880569 4472495 := bstep (se 1 (by rfl) ⟨3354371, by rfl⟩ : syracuseStep 4472495 = 6708743) B6708743
theorem B16138369 : Blo 880569 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B49725613 : Blo 880569 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B3817799 : Blo 880569 3817799 := bstep (se 1 (by rfl) ⟨2863349, by rfl⟩ : syracuseStep 3817799 = 5726699) B5726699
theorem B1982951 : Blo 880569 1982951 := bstep (se 1 (by rfl) ⟨1487213, by rfl⟩ : syracuseStep 1982951 = 2974427) B2974427
theorem B1982969 : Blo 880569 1982969 := bstep (se 2 (by rfl) ⟨743613, by rfl⟩ : syracuseStep 1982969 = 1487227) B1487227
theorem B1983023 : Blo 880569 1983023 := bstep (se 1 (by rfl) ⟨1487267, by rfl⟩ : syracuseStep 1983023 = 2974535) B2974535
theorem B1983113 : Blo 880569 1983113 := bstep (se 2 (by rfl) ⟨743667, by rfl⟩ : syracuseStep 1983113 = 1487335) B1487335
theorem B6046439 : Blo 880569 6046439 := bstep (se 1 (by rfl) ⟨4534829, by rfl⟩ : syracuseStep 6046439 = 9069659) B9069659
theorem B1491743 : Blo 880569 1491743 := bstep (se 1 (by rfl) ⟨1118807, by rfl⟩ : syracuseStep 1491743 = 2237615) B2237615
theorem B1984265 : Blo 880569 1984265 := bstep (se 2 (by rfl) ⟨744099, by rfl⟩ : syracuseStep 1984265 = 1488199) B1488199
theorem B1886527 : Blo 880569 1886527 := bstep (se 1 (by rfl) ⟨1414895, by rfl⟩ : syracuseStep 1886527 = 2829791) B2829791
theorem B2509309 : Blo 880569 2509309 := bstep (se 3 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 2509309 = 940991) B940991
theorem B970459 : Blo 880569 970459 := bstep (se 1 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 970459 = 1455689) B1455689
theorem B1888031 : Blo 880569 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B145019969 : Blo 880569 145019969 := bstep (se 2 (by rfl) ⟨54382488, by rfl⟩ : syracuseStep 145019969 = 108764977) B108764977
theorem B1988207 : Blo 880569 1988207 := bstep (se 1 (by rfl) ⟨1491155, by rfl⟩ : syracuseStep 1988207 = 2982311) B2982311
theorem B1988927 : Blo 880569 1988927 := bstep (se 1 (by rfl) ⟨1491695, by rfl⟩ : syracuseStep 1988927 = 2983391) B2983391
theorem B2972537 : Blo 880569 2972537 := bstep (se 2 (by rfl) ⟨1114701, by rfl⟩ : syracuseStep 2972537 = 2229403) B2229403
theorem B20339693 : Blo 880569 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B1989791 : Blo 880569 1989791 := bstep (se 1 (by rfl) ⟨1492343, by rfl⟩ : syracuseStep 1989791 = 2984687) B2984687
theorem B11296097 : Blo 880569 11296097 := bstep (se 2 (by rfl) ⟨4236036, by rfl⟩ : syracuseStep 11296097 = 8472073) B8472073
theorem B27221795 : Blo 880569 27221795 := bstep (se 1 (by rfl) ⟨20416346, by rfl⟩ : syracuseStep 27221795 = 40832693) B40832693
theorem B13459655 : Blo 880569 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B2974265 : Blo 880569 2974265 := bstep (se 2 (by rfl) ⟨1115349, by rfl⟩ : syracuseStep 2974265 = 2230699) B2230699
theorem B5662811 : Blo 880569 5662811 := bstep (se 1 (by rfl) ⟨4247108, by rfl⟩ : syracuseStep 5662811 = 8494217) B8494217
theorem B5662963 : Blo 880569 5662963 := bstep (se 1 (by rfl) ⟨4247222, by rfl⟩ : syracuseStep 5662963 = 8494445) B8494445
theorem B2124073 : Blo 880569 2124073 := bstep (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) B1593055
theorem B4778473 : Blo 880569 4778473 := bstep (se 2 (by rfl) ⟨1791927, by rfl⟩ : syracuseStep 4778473 = 3583855) B3583855
theorem B11300093 : Blo 880569 11300093 := bstep (se 3 (by rfl) ⟨2118767, by rfl⟩ : syracuseStep 11300093 = 4237535) B4237535
theorem B2977775 : Blo 880569 2977775 := bstep (se 1 (by rfl) ⟨2233331, by rfl⟩ : syracuseStep 2977775 = 4466663) B4466663
theorem B880667 : Blo 880569 880667 := bstep (se 1 (by rfl) ⟨660500, by rfl⟩ : syracuseStep 880667 = 1321001) B1321001
theorem B8057249 : Blo 880569 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B881151 : Blo 880569 881151 := bstep (se 1 (by rfl) ⟨660863, by rfl⟩ : syracuseStep 881151 = 1321727) B1321727
theorem B881359 : Blo 880569 881359 := bstep (se 1 (by rfl) ⟨661019, by rfl⟩ : syracuseStep 881359 = 1322039) B1322039
theorem B6976475 : Blo 880569 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B881691 : Blo 880569 881691 := bstep (se 1 (by rfl) ⟨661268, by rfl⟩ : syracuseStep 881691 = 1322537) B1322537
theorem B3175615 : Blo 880569 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B881967 : Blo 880569 881967 := bstep (se 1 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 881967 = 1322951) B1322951
theorem B882127 : Blo 880569 882127 := bstep (se 1 (by rfl) ⟨661595, by rfl⟩ : syracuseStep 882127 = 1323191) B1323191
theorem B6027065 : Blo 880569 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B882719 : Blo 880569 882719 := bstep (se 1 (by rfl) ⟨662039, by rfl⟩ : syracuseStep 882719 = 1324079) B1324079
theorem B883015 : Blo 880569 883015 := bstep (se 1 (by rfl) ⟨662261, by rfl⟩ : syracuseStep 883015 = 1324523) B1324523
theorem B85817879 : Blo 880569 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B2981501 : Blo 880569 2981501 := bstep (se 3 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 2981501 = 1118063) B1118063
theorem B4030087 : Blo 880569 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B2982905 : Blo 880569 2982905 := bstep (se 2 (by rfl) ⟨1118589, by rfl⟩ : syracuseStep 2982905 = 2237179) B2237179
theorem B4458239 : Blo 880569 4458239 := bstep (se 1 (by rfl) ⟨3343679, by rfl⟩ : syracuseStep 4458239 = 6687359) B6687359
theorem B2984957 : Blo 880569 2984957 := bstep (se 3 (by rfl) ⟨559679, by rfl⟩ : syracuseStep 2984957 = 1119359) B1119359
theorem B3345745 : Blo 880569 3345745 := bstep (se 2 (by rfl) ⟨1254654, by rfl⟩ : syracuseStep 3345745 = 2509309) B2509309
theorem B2823167 : Blo 880569 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B6034895 : Blo 880569 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B8066591 : Blo 880569 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B4462775 : Blo 880569 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B3775207 : Blo 880569 3775207 := bstep (se 1 (by rfl) ⟨2831405, by rfl⟩ : syracuseStep 3775207 = 5662811) B5662811
theorem B4234153 : Blo 880569 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B2235559 : Blo 880569 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B64495349 : Blo 880569 64495349 := bstep (se 5 (by rfl) ⟨3023219, by rfl⟩ : syracuseStep 64495349 = 6046439) B6046439
theorem B991003 : Blo 880569 991003 := bstep (se 1 (by rfl) ⟨743252, by rfl⟩ : syracuseStep 991003 = 1486505) B1486505
theorem B3022703 : Blo 880569 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B13574573 : Blo 880569 13574573 := bstep (se 3 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 13574573 = 5090465) B5090465
theorem B2826895 : Blo 880569 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B2237807 : Blo 880569 2237807 := bstep (se 1 (by rfl) ⟨1678355, by rfl⟩ : syracuseStep 2237807 = 3356711) B3356711
theorem B3352063 : Blo 880569 3352063 := bstep (se 1 (by rfl) ⟨2514047, by rfl⟩ : syracuseStep 3352063 = 5028095) B5028095
theorem B993343 : Blo 880569 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B6695135 : Blo 880569 6695135 := bstep (se 1 (by rfl) ⟨5021351, by rfl⟩ : syracuseStep 6695135 = 10042703) B10042703
theorem B4466987 : Blo 880569 4466987 := bstep (se 1 (by rfl) ⟨3350240, by rfl⟩ : syracuseStep 4466987 = 6700481) B6700481
theorem B1321295 : Blo 880569 1321295 := bstep (se 1 (by rfl) ⟨990971, by rfl⟩ : syracuseStep 1321295 = 1981943) B1981943
theorem B2238799 : Blo 880569 2238799 := bstep (se 1 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 2238799 = 3358199) B3358199
theorem B3353021 : Blo 880569 3353021 := bstep (se 3 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 3353021 = 1257383) B1257383
theorem B66300817 : Blo 880569 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B1321967 : Blo 880569 1321967 := bstep (se 1 (by rfl) ⟨991475, by rfl⟩ : syracuseStep 1321967 = 1982951) B1982951
theorem B1321979 : Blo 880569 1321979 := bstep (se 1 (by rfl) ⟨991484, by rfl⟩ : syracuseStep 1321979 = 1982969) B1982969
theorem B1322015 : Blo 880569 1322015 := bstep (se 1 (by rfl) ⟨991511, by rfl⟩ : syracuseStep 1322015 = 1983023) B1983023
theorem B1322075 : Blo 880569 1322075 := bstep (se 1 (by rfl) ⟨991556, by rfl⟩ : syracuseStep 1322075 = 1983113) B1983113
theorem B35892413 : Blo 880569 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B994495 : Blo 880569 994495 := bstep (se 1 (by rfl) ⟨745871, by rfl⟩ : syracuseStep 994495 = 1491743) B1491743
theorem B1322843 : Blo 880569 1322843 := bstep (se 1 (by rfl) ⟨992132, by rfl⟩ : syracuseStep 1322843 = 1984265) B1984265
theorem B1487497 : Blo 880569 1487497 := bstep (se 2 (by rfl) ⟨557811, by rfl⟩ : syracuseStep 1487497 = 1115623) B1115623
theorem B4469741 : Blo 880569 4469741 := bstep (se 3 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 4469741 = 1676153) B1676153
theorem B17183825 : Blo 880569 17183825 := bstep (se 2 (by rfl) ⟨6443934, by rfl⟩ : syracuseStep 17183825 = 12887869) B12887869
theorem B1258687 : Blo 880569 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B7550617 : Blo 880569 7550617 := bstep (se 2 (by rfl) ⟨2831481, by rfl⟩ : syracuseStep 7550617 = 5662963) B5662963
theorem B2832097 : Blo 880569 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B6371297 : Blo 880569 6371297 := bstep (se 2 (by rfl) ⟨2389236, by rfl⟩ : syracuseStep 6371297 = 4778473) B4778473
theorem B96679979 : Blo 880569 96679979 := bstep (se 1 (by rfl) ⟨72509984, by rfl⟩ : syracuseStep 96679979 = 145019969) B145019969
theorem B1489151 : Blo 880569 1489151 := bstep (se 1 (by rfl) ⟨1116863, by rfl⟩ : syracuseStep 1489151 = 2233727) B2233727
theorem B1325471 : Blo 880569 1325471 := bstep (se 1 (by rfl) ⟨994103, by rfl⟩ : syracuseStep 1325471 = 1988207) B1988207
theorem B1882529 : Blo 880569 1882529 := bstep (se 2 (by rfl) ⟨705948, by rfl⟩ : syracuseStep 1882529 = 1411897) B1411897
theorem B1325951 : Blo 880569 1325951 := bstep (se 1 (by rfl) ⟨994463, by rfl⟩ : syracuseStep 1325951 = 1988927) B1988927
theorem B1981691 : Blo 880569 1981691 := bstep (se 1 (by rfl) ⟨1486268, by rfl⟩ : syracuseStep 1981691 = 2972537) B2972537
theorem B1326527 : Blo 880569 1326527 := bstep (se 1 (by rfl) ⟨994895, by rfl⟩ : syracuseStep 1326527 = 1989791) B1989791
theorem B1490879 : Blo 880569 1490879 := bstep (se 1 (by rfl) ⟨1118159, by rfl⟩ : syracuseStep 1490879 = 2236319) B2236319
theorem B1982843 : Blo 880569 1982843 := bstep (se 1 (by rfl) ⟨1487132, by rfl⟩ : syracuseStep 1982843 = 2974265) B2974265
theorem B6799787 : Blo 880569 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B1491547 : Blo 880569 1491547 := bstep (se 1 (by rfl) ⟨1118660, by rfl⟩ : syracuseStep 1491547 = 2237321) B2237321
theorem B2507897 : Blo 880569 2507897 := bstep (se 2 (by rfl) ⟨940461, by rfl⟩ : syracuseStep 2507897 = 1880923) B1880923
theorem B12700151 : Blo 880569 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B1985183 : Blo 880569 1985183 := bstep (se 1 (by rfl) ⟨1488887, by rfl⟩ : syracuseStep 1985183 = 2977775) B2977775
theorem B4018043 : Blo 880569 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B4772591 : Blo 880569 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B18338867 : Blo 880569 18338867 := bstep (se 1 (by rfl) ⟨13754150, by rfl⟩ : syracuseStep 18338867 = 27508301) B27508301
theorem B1987667 : Blo 880569 1987667 := bstep (se 1 (by rfl) ⟨1490750, by rfl⟩ : syracuseStep 1987667 = 2981501) B2981501
theorem B1988063 : Blo 880569 1988063 := bstep (se 1 (by rfl) ⟨1491047, by rfl⟩ : syracuseStep 1988063 = 2982095) B2982095
theorem B21517825 : Blo 880569 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B2545199 : Blo 880569 2545199 := bstep (se 1 (by rfl) ⟨1908899, by rfl⟩ : syracuseStep 2545199 = 3817799) B3817799
theorem B1988711 : Blo 880569 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B1988891 : Blo 880569 1988891 := bstep (se 1 (by rfl) ⟨1491668, by rfl⟩ : syracuseStep 1988891 = 2983337) B2983337
theorem B2382143 : Blo 880569 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B15292871 : Blo 880569 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B20339495 : Blo 880569 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B2513855 : Blo 880569 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B1989575 : Blo 880569 1989575 := bstep (se 1 (by rfl) ⟨1492181, by rfl⟩ : syracuseStep 1989575 = 2984363) B2984363
theorem B2973185 : Blo 880569 2973185 := bstep (se 2 (by rfl) ⟨1114944, by rfl⟩ : syracuseStep 2973185 = 2229889) B2229889
theorem B9527017 : Blo 880569 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B2515369 : Blo 880569 2515369 := bstep (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) B1886527
theorem B8479991 : Blo 880569 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B3630815 : Blo 880569 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B20703125 : Blo 880569 20703125 := bstep (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) B970459
theorem B13559795 : Blo 880569 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B7530731 : Blo 880569 7530731 := bstep (se 1 (by rfl) ⟨5648048, by rfl⟩ : syracuseStep 7530731 = 11296097) B11296097
theorem B18147863 : Blo 880569 18147863 := bstep (se 1 (by rfl) ⟨13610897, by rfl⟩ : syracuseStep 18147863 = 27221795) B27221795
theorem B12872915 : Blo 880569 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B2977019 : Blo 880569 2977019 := bstep (se 1 (by rfl) ⟨2232764, by rfl⟩ : syracuseStep 2977019 = 4465529) B4465529
theorem B880575 : Blo 880569 880575 := bstep (se 1 (by rfl) ⟨660431, by rfl⟩ : syracuseStep 880575 = 1320863) B1320863
theorem B880711 : Blo 880569 880711 := bstep (se 1 (by rfl) ⟨660533, by rfl⟩ : syracuseStep 880711 = 1321067) B1321067
theorem B880831 : Blo 880569 880831 := bstep (se 1 (by rfl) ⟨660623, by rfl⟩ : syracuseStep 880831 = 1321247) B1321247
theorem B2978207 : Blo 880569 2978207 := bstep (se 1 (by rfl) ⟨2233655, by rfl⟩ : syracuseStep 2978207 = 4467311) B4467311
theorem B881087 : Blo 880569 881087 := bstep (se 1 (by rfl) ⟨660815, by rfl⟩ : syracuseStep 881087 = 1321631) B1321631
theorem B881127 : Blo 880569 881127 := bstep (se 1 (by rfl) ⟨660845, by rfl⟩ : syracuseStep 881127 = 1321691) B1321691
theorem B881391 : Blo 880569 881391 := bstep (se 1 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 881391 = 1322087) B1322087
theorem B7533395 : Blo 880569 7533395 := bstep (se 1 (by rfl) ⟨5650046, by rfl⟩ : syracuseStep 7533395 = 11300093) B11300093
theorem B881887 : Blo 880569 881887 := bstep (se 1 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 881887 = 1322831) B1322831
theorem B881919 : Blo 880569 881919 := bstep (se 1 (by rfl) ⟨661439, by rfl⟩ : syracuseStep 881919 = 1322879) B1322879
theorem B2979071 : Blo 880569 2979071 := bstep (se 1 (by rfl) ⟨2234303, by rfl⟩ : syracuseStep 2979071 = 4468607) B4468607
theorem B882207 : Blo 880569 882207 := bstep (se 1 (by rfl) ⟨661655, by rfl⟩ : syracuseStep 882207 = 1323311) B1323311
theorem B5371499 : Blo 880569 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B882535 : Blo 880569 882535 := bstep (se 1 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 882535 = 1323803) B1323803
theorem B882599 : Blo 880569 882599 := bstep (se 1 (by rfl) ⟨661949, by rfl⟩ : syracuseStep 882599 = 1323899) B1323899
theorem B4650983 : Blo 880569 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B882799 : Blo 880569 882799 := bstep (se 1 (by rfl) ⟨662099, by rfl⟩ : syracuseStep 882799 = 1324199) B1324199
theorem B882895 : Blo 880569 882895 := bstep (se 1 (by rfl) ⟨662171, by rfl⟩ : syracuseStep 882895 = 1324343) B1324343
theorem B882927 : Blo 880569 882927 := bstep (se 1 (by rfl) ⟨662195, by rfl⟩ : syracuseStep 882927 = 1324391) B1324391
theorem B2980367 : Blo 880569 2980367 := bstep (se 1 (by rfl) ⟨2235275, by rfl⟩ : syracuseStep 2980367 = 4470551) B4470551
theorem B883367 : Blo 880569 883367 := bstep (se 1 (by rfl) ⟨662525, by rfl⟩ : syracuseStep 883367 = 1325051) B1325051
theorem B883451 : Blo 880569 883451 := bstep (se 1 (by rfl) ⟨662588, by rfl⟩ : syracuseStep 883451 = 1325177) B1325177
theorem B883487 : Blo 880569 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B883707 : Blo 880569 883707 := bstep (se 1 (by rfl) ⟨662780, by rfl⟩ : syracuseStep 883707 = 1325561) B1325561
theorem B57211919 : Blo 880569 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B2980961 : Blo 880569 2980961 := bstep (se 2 (by rfl) ⟨1117860, by rfl⟩ : syracuseStep 2980961 = 2235721) B2235721
theorem B3767417 : Blo 880569 3767417 := bstep (se 2 (by rfl) ⟨1412781, by rfl⟩ : syracuseStep 3767417 = 2825563) B2825563
theorem B883963 : Blo 880569 883963 := bstep (se 1 (by rfl) ⟨662972, by rfl⟩ : syracuseStep 883963 = 1325945) B1325945
theorem B5373449 : Blo 880569 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B884383 : Blo 880569 884383 := bstep (se 1 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 884383 = 1326575) B1326575
theorem B884415 : Blo 880569 884415 := bstep (se 1 (by rfl) ⟨663311, by rfl⟩ : syracuseStep 884415 = 1326623) B1326623
theorem B884475 : Blo 880569 884475 := bstep (se 1 (by rfl) ⟨663356, by rfl⟩ : syracuseStep 884475 = 1326713) B1326713
theorem B2981663 : Blo 880569 2981663 := bstep (se 1 (by rfl) ⟨2236247, by rfl⟩ : syracuseStep 2981663 = 4472495) B4472495
theorem B1671931 : Blo 880569 1671931 := bstep (se 1 (by rfl) ⟨1253948, by rfl⟩ : syracuseStep 1671931 = 2507897) B2507897
theorem B3769193 : Blo 880569 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B2985065 : Blo 880569 2985065 := bstep (se 2 (by rfl) ⟨1119399, by rfl⟩ : syracuseStep 2985065 = 2238799) B2238799
theorem B3181727 : Blo 880569 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B12225911 : Blo 880569 12225911 := bstep (se 1 (by rfl) ⟨9169433, by rfl⟩ : syracuseStep 12225911 = 18338867) B18338867
theorem B5377727 : Blo 880569 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B10195247 : Blo 880569 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B4460993 : Blo 880569 4460993 := bstep (se 2 (by rfl) ⟨1672872, by rfl⟩ : syracuseStep 4460993 = 3345745) B3345745
theorem B1675903 : Blo 880569 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B42996899 : Blo 880569 42996899 := bstep (se 1 (by rfl) ⟨32247674, by rfl⟩ : syracuseStep 42996899 = 64495349) B64495349
theorem B9049715 : Blo 880569 9049715 := bstep (se 1 (by rfl) ⟨6787286, by rfl⟩ : syracuseStep 9049715 = 13574573) B13574573
theorem B13802083 : Blo 880569 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B4463423 : Blo 880569 4463423 := bstep (se 1 (by rfl) ⟨3347567, by rfl⟩ : syracuseStep 4463423 = 6695135) B6695135
theorem B5020487 : Blo 880569 5020487 := bstep (se 1 (by rfl) ⟨3765365, by rfl⟩ : syracuseStep 5020487 = 7530731) B7530731
theorem B1678249 : Blo 880569 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B2235347 : Blo 880569 2235347 := bstep (se 1 (by rfl) ⟨1676510, by rfl⟩ : syracuseStep 2235347 = 3353021) B3353021
theorem B12098575 : Blo 880569 12098575 := bstep (se 1 (by rfl) ⟨9073931, by rfl⟩ : syracuseStep 12098575 = 18147863) B18147863
theorem B23928275 : Blo 880569 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B10067489 : Blo 880569 10067489 := bstep (se 2 (by rfl) ⟨3775308, by rfl⟩ : syracuseStep 10067489 = 7550617) B7550617
theorem B3776129 : Blo 880569 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B5022263 : Blo 880569 5022263 := bstep (se 1 (by rfl) ⟨3766697, by rfl⟩ : syracuseStep 5022263 = 7533395) B7533395
theorem B3580999 : Blo 880569 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B5645537 : Blo 880569 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B992767 : Blo 880569 992767 := bstep (se 1 (by rfl) ⟨744575, by rfl⟩ : syracuseStep 992767 = 1489151) B1489151
theorem B1255019 : Blo 880569 1255019 := bstep (se 1 (by rfl) ⟨941264, by rfl⟩ : syracuseStep 1255019 = 1882529) B1882529
theorem B1321127 : Blo 880569 1321127 := bstep (se 1 (by rfl) ⟨990845, by rfl⟩ : syracuseStep 1321127 = 1981691) B1981691
theorem B3582299 : Blo 880569 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B1321337 : Blo 880569 1321337 := bstep (se 2 (by rfl) ⟨495501, by rfl⟩ : syracuseStep 1321337 = 991003) B991003
theorem B993919 : Blo 880569 993919 := bstep (se 1 (by rfl) ⟨745439, by rfl⟩ : syracuseStep 993919 = 1490879) B1490879
theorem B1321895 : Blo 880569 1321895 := bstep (se 1 (by rfl) ⟨991421, by rfl⟩ : syracuseStep 1321895 = 1982843) B1982843
theorem B4533191 : Blo 880569 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B3353825 : Blo 880569 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B8466767 : Blo 880569 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B1323455 : Blo 880569 1323455 := bstep (se 1 (by rfl) ⟨992591, by rfl⟩ : syracuseStep 1323455 = 1985183) B1985183
theorem B4469417 : Blo 880569 4469417 := bstep (se 2 (by rfl) ⟨1676031, by rfl⟩ : syracuseStep 4469417 = 3352063) B3352063
theorem B1324457 : Blo 880569 1324457 := bstep (se 2 (by rfl) ⟨496671, by rfl⟩ : syracuseStep 1324457 = 993343) B993343
theorem B1882111 : Blo 880569 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B1325111 : Blo 880569 1325111 := bstep (se 1 (by rfl) ⟨993833, by rfl⟩ : syracuseStep 1325111 = 1987667) B1987667
theorem B1325375 : Blo 880569 1325375 := bstep (se 1 (by rfl) ⟨994031, by rfl⟩ : syracuseStep 1325375 = 1988063) B1988063
theorem B1325807 : Blo 880569 1325807 := bstep (se 1 (by rfl) ⟨994355, by rfl⟩ : syracuseStep 1325807 = 1988711) B1988711
theorem B1325927 : Blo 880569 1325927 := bstep (se 1 (by rfl) ⟨994445, by rfl⟩ : syracuseStep 1325927 = 1988891) B1988891
theorem B1325993 : Blo 880569 1325993 := bstep (se 2 (by rfl) ⟨497247, by rfl⟩ : syracuseStep 1325993 = 994495) B994495
theorem B1326383 : Blo 880569 1326383 := bstep (se 1 (by rfl) ⟨994787, by rfl⟩ : syracuseStep 1326383 = 1989575) B1989575
theorem B1982123 : Blo 880569 1982123 := bstep (se 1 (by rfl) ⟨1486592, by rfl⟩ : syracuseStep 1982123 = 2973185) B2973185
theorem B2015135 : Blo 880569 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B5653327 : Blo 880569 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B1983329 : Blo 880569 1983329 := bstep (se 2 (by rfl) ⟨743748, by rfl⟩ : syracuseStep 1983329 = 1487497) B1487497
theorem B1491871 : Blo 880569 1491871 := bstep (se 1 (by rfl) ⟨1118903, by rfl⟩ : syracuseStep 1491871 = 2237807) B2237807
theorem B28690433 : Blo 880569 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B1984679 : Blo 880569 1984679 := bstep (se 1 (by rfl) ⟨1488509, by rfl⟩ : syracuseStep 1984679 = 2977019) B2977019
theorem B1985471 : Blo 880569 1985471 := bstep (se 1 (by rfl) ⟨1489103, by rfl⟩ : syracuseStep 1985471 = 2978207) B2978207
theorem B11455883 : Blo 880569 11455883 := bstep (se 1 (by rfl) ⟨8591912, by rfl⟩ : syracuseStep 11455883 = 17183825) B17183825
theorem B1986047 : Blo 880569 1986047 := bstep (se 1 (by rfl) ⟨1489535, by rfl⟩ : syracuseStep 1986047 = 2979071) B2979071
theorem B5033609 : Blo 880569 5033609 := bstep (se 2 (by rfl) ⟨1887603, by rfl⟩ : syracuseStep 5033609 = 3775207) B3775207
theorem B4247531 : Blo 880569 4247531 := bstep (se 1 (by rfl) ⟨3185648, by rfl⟩ : syracuseStep 4247531 = 6371297) B6371297
theorem B3100655 : Blo 880569 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B1986911 : Blo 880569 1986911 := bstep (se 1 (by rfl) ⟨1490183, by rfl⟩ : syracuseStep 1986911 = 2980367) B2980367
theorem B1987307 : Blo 880569 1987307 := bstep (se 1 (by rfl) ⟨1490480, by rfl⟩ : syracuseStep 1987307 = 2980961) B2980961
theorem B2511611 : Blo 880569 2511611 := bstep (se 1 (by rfl) ⟨1883708, by rfl⟩ : syracuseStep 2511611 = 3767417) B3767417
theorem B12702689 : Blo 880569 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B1987775 : Blo 880569 1987775 := bstep (se 1 (by rfl) ⟨1490831, by rfl⟩ : syracuseStep 1987775 = 2981663) B2981663
theorem B1988603 : Blo 880569 1988603 := bstep (se 1 (by rfl) ⟨1491452, by rfl⟩ : syracuseStep 1988603 = 2982905) B2982905
theorem B1988729 : Blo 880569 1988729 := bstep (se 2 (by rfl) ⟨745773, by rfl⟩ : syracuseStep 1988729 = 1491547) B1491547
theorem B2972159 : Blo 880569 2972159 := bstep (se 1 (by rfl) ⟨2229119, by rfl⟩ : syracuseStep 2972159 = 4458239) B4458239
theorem B1989971 : Blo 880569 1989971 := bstep (se 1 (by rfl) ⟨1492478, by rfl⟩ : syracuseStep 1989971 = 2984957) B2984957
theorem B4023263 : Blo 880569 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B1696799 : Blo 880569 1696799 := bstep (se 1 (by rfl) ⟨1272599, by rfl⟩ : syracuseStep 1696799 = 2545199) B2545199
theorem B88401089 : Blo 880569 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B2975183 : Blo 880569 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B13559663 : Blo 880569 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B6352381 : Blo 880569 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B2420543 : Blo 880569 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B9039863 : Blo 880569 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B2977991 : Blo 880569 2977991 := bstep (se 1 (by rfl) ⟨2233493, by rfl⟩ : syracuseStep 2977991 = 4466987) B4466987
theorem B880863 : Blo 880569 880863 := bstep (se 1 (by rfl) ⟨660647, by rfl⟩ : syracuseStep 880863 = 1321295) B1321295
theorem B881311 : Blo 880569 881311 := bstep (se 1 (by rfl) ⟨660983, by rfl⟩ : syracuseStep 881311 = 1321967) B1321967
theorem B881319 : Blo 880569 881319 := bstep (se 1 (by rfl) ⟨660989, by rfl⟩ : syracuseStep 881319 = 1321979) B1321979
theorem B881343 : Blo 880569 881343 := bstep (se 1 (by rfl) ⟨661007, by rfl⟩ : syracuseStep 881343 = 1322015) B1322015
theorem B881383 : Blo 880569 881383 := bstep (se 1 (by rfl) ⟨661037, by rfl⟩ : syracuseStep 881383 = 1322075) B1322075
theorem B8581943 : Blo 880569 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B881895 : Blo 880569 881895 := bstep (se 1 (by rfl) ⟨661421, by rfl⟩ : syracuseStep 881895 = 1322843) B1322843
theorem B2979827 : Blo 880569 2979827 := bstep (se 1 (by rfl) ⟨2234870, by rfl⟩ : syracuseStep 2979827 = 4469741) B4469741
theorem B64453319 : Blo 880569 64453319 := bstep (se 1 (by rfl) ⟨48339989, by rfl⟩ : syracuseStep 64453319 = 96679979) B96679979
theorem B2980745 : Blo 880569 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B883647 : Blo 880569 883647 := bstep (se 1 (by rfl) ⟨662735, by rfl⟩ : syracuseStep 883647 = 1325471) B1325471
theorem B883967 : Blo 880569 883967 := bstep (se 1 (by rfl) ⟨662975, by rfl⟩ : syracuseStep 883967 = 1325951) B1325951
theorem B38141279 : Blo 880569 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B884351 : Blo 880569 884351 := bstep (se 1 (by rfl) ⟨663263, by rfl⟩ : syracuseStep 884351 = 1326527) B1326527
theorem B10714781 : Blo 880569 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B2229241 : Blo 880569 2229241 := bstep (se 2 (by rfl) ⟨835965, by rfl⟩ : syracuseStep 2229241 = 1671931) B1671931
theorem B7537769 : Blo 880569 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B7637255 : Blo 880569 7637255 := bstep (se 1 (by rfl) ⟨5727941, by rfl⟩ : syracuseStep 7637255 = 11455883) B11455883
theorem B2067103 : Blo 880569 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B4524797 : Blo 880569 4524797 := bstep (se 3 (by rfl) ⟨848399, by rfl⟩ : syracuseStep 4524797 = 1696799) B1696799
theorem B1674407 : Blo 880569 1674407 := bstep (se 1 (by rfl) ⟨1255805, by rfl⟩ : syracuseStep 1674407 = 2511611) B2511611
theorem B235736237 : Blo 880569 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B6033143 : Blo 880569 6033143 := bstep (se 1 (by rfl) ⟨4524857, by rfl⟩ : syracuseStep 6033143 = 9049715) B9049715
theorem B3346717 : Blo 880569 3346717 := bstep (se 3 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 3346717 = 1255019) B1255019
theorem B3346991 : Blo 880569 3346991 := bstep (se 1 (by rfl) ⟨2510243, by rfl⟩ : syracuseStep 3346991 = 5020487) B5020487
theorem B3348175 : Blo 880569 3348175 := bstep (se 1 (by rfl) ⟨2511131, by rfl⟩ : syracuseStep 3348175 = 5022263) B5022263
theorem B2234537 : Blo 880569 2234537 := bstep (se 2 (by rfl) ⟨837951, by rfl⟩ : syracuseStep 2234537 = 1675903) B1675903
theorem B3022127 : Blo 880569 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B2235883 : Blo 880569 2235883 := bstep (se 1 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 2235883 = 3353825) B3353825
theorem B1613695 : Blo 880569 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B5644511 : Blo 880569 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B2237665 : Blo 880569 2237665 := bstep (se 2 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 2237665 = 1678249) B1678249
theorem B16131433 : Blo 880569 16131433 := bstep (se 2 (by rfl) ⟨6049287, by rfl⟩ : syracuseStep 16131433 = 12098575) B12098575
theorem B42968879 : Blo 880569 42968879 := bstep (se 1 (by rfl) ⟨32226659, by rfl⟩ : syracuseStep 42968879 = 64453319) B64453319
theorem B1321415 : Blo 880569 1321415 := bstep (se 1 (by rfl) ⟨991061, by rfl⟩ : syracuseStep 1321415 = 1982123) B1982123
theorem B1322219 : Blo 880569 1322219 := bstep (se 1 (by rfl) ⟨991664, by rfl⟩ : syracuseStep 1322219 = 1983329) B1983329
theorem B1323119 : Blo 880569 1323119 := bstep (se 1 (by rfl) ⟨992339, by rfl⟩ : syracuseStep 1323119 = 1984679) B1984679
theorem B1323647 : Blo 880569 1323647 := bstep (se 1 (by rfl) ⟨992735, by rfl⟩ : syracuseStep 1323647 = 1985471) B1985471
theorem B1323689 : Blo 880569 1323689 := bstep (se 2 (by rfl) ⟨496383, by rfl⟩ : syracuseStep 1323689 = 992767) B992767
theorem B1324031 : Blo 880569 1324031 := bstep (se 1 (by rfl) ⟨993023, by rfl⟩ : syracuseStep 1324031 = 1986047) B1986047
theorem B3355739 : Blo 880569 3355739 := bstep (se 1 (by rfl) ⟨2516804, by rfl⟩ : syracuseStep 3355739 = 5033609) B5033609
theorem B3585151 : Blo 880569 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B2831687 : Blo 880569 2831687 := bstep (se 1 (by rfl) ⟨2123765, by rfl⟩ : syracuseStep 2831687 = 4247531) B4247531
theorem B6796831 : Blo 880569 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B1324607 : Blo 880569 1324607 := bstep (se 1 (by rfl) ⟨993455, by rfl⟩ : syracuseStep 1324607 = 1986911) B1986911
theorem B1324871 : Blo 880569 1324871 := bstep (se 1 (by rfl) ⟨993653, by rfl⟩ : syracuseStep 1324871 = 1987307) B1987307
theorem B73611109 : Blo 880569 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B8468459 : Blo 880569 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B1325183 : Blo 880569 1325183 := bstep (se 1 (by rfl) ⟨993887, by rfl⟩ : syracuseStep 1325183 = 1987775) B1987775
theorem B1325225 : Blo 880569 1325225 := bstep (se 2 (by rfl) ⟨496959, by rfl⟩ : syracuseStep 1325225 = 993919) B993919
theorem B1325735 : Blo 880569 1325735 := bstep (se 1 (by rfl) ⟨994301, by rfl⟩ : syracuseStep 1325735 = 1988603) B1988603
theorem B1325819 : Blo 880569 1325819 := bstep (se 1 (by rfl) ⟨994364, by rfl⟩ : syracuseStep 1325819 = 1988729) B1988729
theorem B1981439 : Blo 880569 1981439 := bstep (se 1 (by rfl) ⟨1486079, by rfl⟩ : syracuseStep 1981439 = 2972159) B2972159
theorem B1490231 : Blo 880569 1490231 := bstep (se 1 (by rfl) ⟨1117673, by rfl⟩ : syracuseStep 1490231 = 2235347) B2235347
theorem B8469841 : Blo 880569 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B1326647 : Blo 880569 1326647 := bstep (se 1 (by rfl) ⟨994985, by rfl⟩ : syracuseStep 1326647 = 1989971) B1989971
theorem B1983455 : Blo 880569 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B2509481 : Blo 880569 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B1985327 : Blo 880569 1985327 := bstep (se 1 (by rfl) ⟨1488995, by rfl⟩ : syracuseStep 1985327 = 2977991) B2977991
theorem B5721295 : Blo 880569 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B1986551 : Blo 880569 1986551 := bstep (se 1 (by rfl) ⟨1489913, by rfl⟩ : syracuseStep 1986551 = 2979827) B2979827
theorem B1987163 : Blo 880569 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B2512795 : Blo 880569 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B1989161 : Blo 880569 1989161 := bstep (se 2 (by rfl) ⟨745935, by rfl⟩ : syracuseStep 1989161 = 1491871) B1491871
theorem B19126955 : Blo 880569 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B1990043 : Blo 880569 1990043 := bstep (se 1 (by rfl) ⟨1492532, by rfl⟩ : syracuseStep 1990043 = 2985065) B2985065
theorem B2121151 : Blo 880569 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B2973995 : Blo 880569 2973995 := bstep (se 1 (by rfl) ⟨2230496, by rfl⟩ : syracuseStep 2973995 = 4460993) B4460993
theorem B28664599 : Blo 880569 28664599 := bstep (se 1 (by rfl) ⟨21498449, by rfl⟩ : syracuseStep 28664599 = 42996899) B42996899
theorem B2975615 : Blo 880569 2975615 := bstep (se 1 (by rfl) ⟨2231711, by rfl⟩ : syracuseStep 2975615 = 4463423) B4463423
theorem B15952183 : Blo 880569 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B6711659 : Blo 880569 6711659 := bstep (se 1 (by rfl) ⟨5033744, by rfl⟩ : syracuseStep 6711659 = 10067489) B10067489
theorem B2517419 : Blo 880569 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B19098661 : Blo 880569 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B2682175 : Blo 880569 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B3763691 : Blo 880569 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B9039775 : Blo 880569 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B880751 : Blo 880569 880751 := bstep (se 1 (by rfl) ⟨660563, by rfl⟩ : syracuseStep 880751 = 1321127) B1321127
theorem B2388199 : Blo 880569 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B880891 : Blo 880569 880891 := bstep (se 1 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 880891 = 1321337) B1321337
theorem B881263 : Blo 880569 881263 := bstep (se 1 (by rfl) ⟨660947, by rfl⟩ : syracuseStep 881263 = 1321895) B1321895
theorem B6026575 : Blo 880569 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B882303 : Blo 880569 882303 := bstep (se 1 (by rfl) ⟨661727, by rfl⟩ : syracuseStep 882303 = 1323455) B1323455
theorem B2979611 : Blo 880569 2979611 := bstep (se 1 (by rfl) ⟨2234708, by rfl⟩ : syracuseStep 2979611 = 4469417) B4469417
theorem B882971 : Blo 880569 882971 := bstep (se 1 (by rfl) ⟨662228, by rfl⟩ : syracuseStep 882971 = 1324457) B1324457
theorem B32602429 : Blo 880569 32602429 := bstep (se 3 (by rfl) ⟨6112955, by rfl⟩ : syracuseStep 32602429 = 12225911) B12225911
theorem B883407 : Blo 880569 883407 := bstep (se 1 (by rfl) ⟨662555, by rfl⟩ : syracuseStep 883407 = 1325111) B1325111
theorem B883583 : Blo 880569 883583 := bstep (se 1 (by rfl) ⟨662687, by rfl⟩ : syracuseStep 883583 = 1325375) B1325375
theorem B883871 : Blo 880569 883871 := bstep (se 1 (by rfl) ⟨662903, by rfl⟩ : syracuseStep 883871 = 1325807) B1325807
theorem B883951 : Blo 880569 883951 := bstep (se 1 (by rfl) ⟨662963, by rfl⟩ : syracuseStep 883951 = 1325927) B1325927
theorem B883995 : Blo 880569 883995 := bstep (se 1 (by rfl) ⟨662996, by rfl⟩ : syracuseStep 883995 = 1325993) B1325993
theorem B884255 : Blo 880569 884255 := bstep (se 1 (by rfl) ⟨663191, by rfl⟩ : syracuseStep 884255 = 1326383) B1326383
theorem B25427519 : Blo 880569 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B7143187 : Blo 880569 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B1343423 : Blo 880569 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B2983553 : Blo 880569 2983553 := bstep (se 2 (by rfl) ⟨1118832, by rfl⟩ : syracuseStep 2983553 = 2237665) B2237665
theorem B1672987 : Blo 880569 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B3016531 : Blo 880569 3016531 := bstep (se 1 (by rfl) ⟨2262398, by rfl⟩ : syracuseStep 3016531 = 4524797) B4524797
theorem B1116271 : Blo 880569 1116271 := bstep (se 1 (by rfl) ⟨837203, by rfl⟩ : syracuseStep 1116271 = 1674407) B1674407
theorem B157157491 : Blo 880569 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B2231327 : Blo 880569 2231327 := bstep (se 1 (by rfl) ⟨1673495, by rfl⟩ : syracuseStep 2231327 = 3346991) B3346991
theorem B25464881 : Blo 880569 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B3576233 : Blo 880569 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B12751303 : Blo 880569 12751303 := bstep (se 1 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 12751303 = 19126955) B19126955
theorem B3184265 : Blo 880569 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B4462289 : Blo 880569 4462289 := bstep (se 2 (by rfl) ⟨1673358, by rfl⟩ : syracuseStep 4462289 = 3346717) B3346717
theorem B28645919 : Blo 880569 28645919 := bstep (se 1 (by rfl) ⟨21484439, by rfl⟩ : syracuseStep 28645919 = 42968879) B42968879
theorem B8035433 : Blo 880569 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B4464233 : Blo 880569 4464233 := bstep (se 2 (by rfl) ⟨1674087, by rfl⟩ : syracuseStep 4464233 = 3348175) B3348175
theorem B98148145 : Blo 880569 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B3350393 : Blo 880569 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B2237159 : Blo 880569 2237159 := bstep (se 1 (by rfl) ⟨1677869, by rfl⟩ : syracuseStep 2237159 = 3355739) B3355739
theorem B5645639 : Blo 880569 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B2828201 : Blo 880569 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B1320959 : Blo 880569 1320959 := bstep (se 1 (by rfl) ⟨990719, by rfl⟩ : syracuseStep 1320959 = 1981439) B1981439
theorem B993487 : Blo 880569 993487 := bstep (se 1 (by rfl) ⟨745115, by rfl⟩ : syracuseStep 993487 = 1490231) B1490231
theorem B16951679 : Blo 880569 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B3582461 : Blo 880569 3582461 := bstep (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) B1343423
theorem B1322303 : Blo 880569 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B5025179 : Blo 880569 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B38219465 : Blo 880569 38219465 := bstep (se 2 (by rfl) ⟨14332299, by rfl⟩ : syracuseStep 38219465 = 28664599) B28664599
theorem B5091503 : Blo 880569 5091503 := bstep (se 1 (by rfl) ⟨3818627, by rfl⟩ : syracuseStep 5091503 = 7637255) B7637255
theorem B85078309 : Blo 880569 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B21508577 : Blo 880569 21508577 := bstep (se 2 (by rfl) ⟨8065716, by rfl⟩ : syracuseStep 21508577 = 16131433) B16131433
theorem B1323551 : Blo 880569 1323551 := bstep (se 1 (by rfl) ⟨992663, by rfl⟩ : syracuseStep 1323551 = 1985327) B1985327
theorem B1324367 : Blo 880569 1324367 := bstep (se 1 (by rfl) ⟨993275, by rfl⟩ : syracuseStep 1324367 = 1986551) B1986551
theorem B1324775 : Blo 880569 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B11024549 : Blo 880569 11024549 := bstep (se 4 (by rfl) ⟨1033551, by rfl⟩ : syracuseStep 11024549 = 2067103) B2067103
theorem B1489691 : Blo 880569 1489691 := bstep (se 1 (by rfl) ⟨1117268, by rfl⟩ : syracuseStep 1489691 = 2234537) B2234537
theorem B1326107 : Blo 880569 1326107 := bstep (se 1 (by rfl) ⟨994580, by rfl⟩ : syracuseStep 1326107 = 1989161) B1989161
theorem B2014751 : Blo 880569 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B1326695 : Blo 880569 1326695 := bstep (se 1 (by rfl) ⟨995021, by rfl⟩ : syracuseStep 1326695 = 1990043) B1990043
theorem B1982663 : Blo 880569 1982663 := bstep (se 1 (by rfl) ⟨1486997, by rfl⟩ : syracuseStep 1982663 = 2973995) B2973995
theorem B19120805 : Blo 880569 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B1983743 : Blo 880569 1983743 := bstep (se 1 (by rfl) ⟨1487807, by rfl⟩ : syracuseStep 1983743 = 2975615) B2975615
theorem B4474439 : Blo 880569 4474439 := bstep (se 1 (by rfl) ⟨3355829, by rfl⟩ : syracuseStep 4474439 = 6711659) B6711659
theorem B9062441 : Blo 880569 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B2509127 : Blo 880569 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B43469905 : Blo 880569 43469905 := bstep (se 2 (by rfl) ⟨16301214, by rfl⟩ : syracuseStep 43469905 = 32602429) B32602429
theorem B1887791 : Blo 880569 1887791 := bstep (se 1 (by rfl) ⟨1415843, by rfl⟩ : syracuseStep 1887791 = 2831687) B2831687
theorem B1986407 : Blo 880569 1986407 := bstep (se 1 (by rfl) ⟨1489805, by rfl⟩ : syracuseStep 1986407 = 2979611) B2979611
theorem B11293121 : Blo 880569 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B9524249 : Blo 880569 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B2151593 : Blo 880569 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B2972321 : Blo 880569 2972321 := bstep (se 2 (by rfl) ⟨1114620, by rfl⟩ : syracuseStep 2972321 = 2229241) B2229241
theorem B4022095 : Blo 880569 4022095 := bstep (se 1 (by rfl) ⟨3016571, by rfl⟩ : syracuseStep 4022095 = 6033143) B6033143
theorem B7628393 : Blo 880569 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B12053033 : Blo 880569 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B3763007 : Blo 880569 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B6713117 : Blo 880569 6713117 := bstep (se 3 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 6713117 = 2517419) B2517419
theorem B880943 : Blo 880569 880943 := bstep (se 1 (by rfl) ⟨660707, by rfl⟩ : syracuseStep 880943 = 1321415) B1321415
theorem B881479 : Blo 880569 881479 := bstep (se 1 (by rfl) ⟨661109, by rfl⟩ : syracuseStep 881479 = 1322219) B1322219
theorem B882079 : Blo 880569 882079 := bstep (se 1 (by rfl) ⟨661559, by rfl⟩ : syracuseStep 882079 = 1323119) B1323119
theorem B882431 : Blo 880569 882431 := bstep (se 1 (by rfl) ⟨661823, by rfl⟩ : syracuseStep 882431 = 1323647) B1323647
theorem B882459 : Blo 880569 882459 := bstep (se 1 (by rfl) ⟨661844, by rfl⟩ : syracuseStep 882459 = 1323689) B1323689
theorem B882687 : Blo 880569 882687 := bstep (se 1 (by rfl) ⟨662015, by rfl⟩ : syracuseStep 882687 = 1324031) B1324031
theorem B883071 : Blo 880569 883071 := bstep (se 1 (by rfl) ⟨662303, by rfl⟩ : syracuseStep 883071 = 1324607) B1324607
theorem B883247 : Blo 880569 883247 := bstep (se 1 (by rfl) ⟨662435, by rfl⟩ : syracuseStep 883247 = 1324871) B1324871
theorem B883455 : Blo 880569 883455 := bstep (se 1 (by rfl) ⟨662591, by rfl⟩ : syracuseStep 883455 = 1325183) B1325183
theorem B883483 : Blo 880569 883483 := bstep (se 1 (by rfl) ⟨662612, by rfl⟩ : syracuseStep 883483 = 1325225) B1325225
theorem B883823 : Blo 880569 883823 := bstep (se 1 (by rfl) ⟨662867, by rfl⟩ : syracuseStep 883823 = 1325735) B1325735
theorem B883879 : Blo 880569 883879 := bstep (se 1 (by rfl) ⟨662909, by rfl⟩ : syracuseStep 883879 = 1325819) B1325819
theorem B2981177 : Blo 880569 2981177 := bstep (se 2 (by rfl) ⟨1117941, by rfl⟩ : syracuseStep 2981177 = 2235883) B2235883
theorem B884431 : Blo 880569 884431 := bstep (se 1 (by rfl) ⟨663323, by rfl⟩ : syracuseStep 884431 = 1326647) B1326647
theorem B12747203 : Blo 880569 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B2982959 : Blo 880569 2982959 := bstep (se 1 (by rfl) ⟨2237219, by rfl⟩ : syracuseStep 2982959 = 4474439) B4474439
theorem B1672751 : Blo 880569 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B2230649 : Blo 880569 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B16976587 : Blo 880569 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B7541869 : Blo 880569 7541869 := bstep (se 3 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 7541869 = 2828201) B2828201
theorem B2233595 : Blo 880569 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B5085595 : Blo 880569 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B8035355 : Blo 880569 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B3350119 : Blo 880569 3350119 := bstep (se 1 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 3350119 = 5025179) B5025179
theorem B7349699 : Blo 880569 7349699 := bstep (se 1 (by rfl) ⟨5512274, by rfl⟩ : syracuseStep 7349699 = 11024549) B11024549
theorem B993127 : Blo 880569 993127 := bstep (se 1 (by rfl) ⟨744845, by rfl⟩ : syracuseStep 993127 = 1489691) B1489691
theorem B1321775 : Blo 880569 1321775 := bstep (se 1 (by rfl) ⟨991331, by rfl⟩ : syracuseStep 1321775 = 1982663) B1982663
theorem B13577341 : Blo 880569 13577341 := bstep (se 3 (by rfl) ⟨2545751, by rfl⟩ : syracuseStep 13577341 = 5091503) B5091503
theorem B1322495 : Blo 880569 1322495 := bstep (se 1 (by rfl) ⟨991871, by rfl⟩ : syracuseStep 1322495 = 1983743) B1983743
theorem B6041627 : Blo 880569 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B1487551 : Blo 880569 1487551 := bstep (se 1 (by rfl) ⟨1115663, by rfl⟩ : syracuseStep 1487551 = 2231327) B2231327
theorem B1324271 : Blo 880569 1324271 := bstep (se 1 (by rfl) ⟨993203, by rfl⟩ : syracuseStep 1324271 = 1986407) B1986407
theorem B1488361 : Blo 880569 1488361 := bstep (se 2 (by rfl) ⟨558135, by rfl⟩ : syracuseStep 1488361 = 1116271) B1116271
theorem B1324649 : Blo 880569 1324649 := bstep (se 2 (by rfl) ⟨496743, by rfl⟩ : syracuseStep 1324649 = 993487) B993487
theorem B1981547 : Blo 880569 1981547 := bstep (se 1 (by rfl) ⟨1486160, by rfl⟩ : syracuseStep 1981547 = 2972321) B2972321
theorem B5356955 : Blo 880569 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B1491439 : Blo 880569 1491439 := bstep (se 1 (by rfl) ⟨1118579, by rfl⟩ : syracuseStep 1491439 = 2237159) B2237159
theorem B2508671 : Blo 880569 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B25479643 : Blo 880569 25479643 := bstep (se 1 (by rfl) ⟨19109732, by rfl⟩ : syracuseStep 25479643 = 38219465) B38219465
theorem B4475411 : Blo 880569 4475411 := bstep (se 1 (by rfl) ⟨3356558, by rfl⟩ : syracuseStep 4475411 = 6713117) B6713117
theorem B14339051 : Blo 880569 14339051 := bstep (se 1 (by rfl) ⟨10754288, by rfl⟩ : syracuseStep 14339051 = 21508577) B21508577
theorem B5034109 : Blo 880569 5034109 := bstep (se 3 (by rfl) ⟨943895, by rfl⟩ : syracuseStep 5034109 = 1887791) B1887791
theorem B1987451 : Blo 880569 1987451 := bstep (se 1 (by rfl) ⟨1490588, by rfl⟩ : syracuseStep 1987451 = 2981177) B2981177
theorem B130864193 : Blo 880569 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B5362793 : Blo 880569 5362793 := bstep (se 2 (by rfl) ⟨2011047, by rfl⟩ : syracuseStep 5362793 = 4022095) B4022095
theorem B1989035 : Blo 880569 1989035 := bstep (se 1 (by rfl) ⟨1491776, by rfl⟩ : syracuseStep 1989035 = 2983553) B2983553
theorem B209543321 : Blo 880569 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B2384155 : Blo 880569 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B7528747 : Blo 880569 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B6349499 : Blo 880569 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B1434395 : Blo 880569 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B2122843 : Blo 880569 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B2974859 : Blo 880569 2974859 := bstep (se 1 (by rfl) ⟨2231144, by rfl⟩ : syracuseStep 2974859 = 4462289) B4462289
theorem B57959873 : Blo 880569 57959873 := bstep (se 2 (by rfl) ⟨21734952, by rfl⟩ : syracuseStep 57959873 = 43469905) B43469905
theorem B19097279 : Blo 880569 19097279 := bstep (se 1 (by rfl) ⟨14322959, by rfl⟩ : syracuseStep 19097279 = 28645919) B28645919
theorem B2976155 : Blo 880569 2976155 := bstep (se 1 (by rfl) ⟨2232116, by rfl⟩ : syracuseStep 2976155 = 4464233) B4464233
theorem B113437745 : Blo 880569 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B17001737 : Blo 880569 17001737 := bstep (se 2 (by rfl) ⟨6375651, by rfl⟩ : syracuseStep 17001737 = 12751303) B12751303
theorem B3763759 : Blo 880569 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B880639 : Blo 880569 880639 := bstep (se 1 (by rfl) ⟨660479, by rfl⟩ : syracuseStep 880639 = 1320959) B1320959
theorem B11301119 : Blo 880569 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B2388307 : Blo 880569 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B881535 : Blo 880569 881535 := bstep (se 1 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 881535 = 1322303) B1322303
theorem B882367 : Blo 880569 882367 := bstep (se 1 (by rfl) ⟨661775, by rfl⟩ : syracuseStep 882367 = 1323551) B1323551
theorem B882911 : Blo 880569 882911 := bstep (se 1 (by rfl) ⟨662183, by rfl⟩ : syracuseStep 882911 = 1324367) B1324367
theorem B883183 : Blo 880569 883183 := bstep (se 1 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 883183 = 1324775) B1324775
theorem B5372669 : Blo 880569 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B16088165 : Blo 880569 16088165 := bstep (se 4 (by rfl) ⟨1508265, by rfl⟩ : syracuseStep 16088165 = 3016531) B3016531
theorem B884071 : Blo 880569 884071 := bstep (se 1 (by rfl) ⟨663053, by rfl⟩ : syracuseStep 884071 = 1326107) B1326107
theorem B884463 : Blo 880569 884463 := bstep (se 1 (by rfl) ⟨663347, by rfl⟩ : syracuseStep 884463 = 1326695) B1326695
theorem B3178873 : Blo 880569 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B2983607 : Blo 880569 2983607 := bstep (se 1 (by rfl) ⟨2237705, by rfl⟩ : syracuseStep 2983607 = 4475411) B4475411
theorem B3575195 : Blo 880569 3575195 := bstep (se 1 (by rfl) ⟨2681396, by rfl⟩ : syracuseStep 3575195 = 5362793) B5362793
theorem B4460669 : Blo 880569 4460669 := bstep (se 3 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 4460669 = 1672751) B1672751
theorem B5018345 : Blo 880569 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B6689789 : Blo 880569 6689789 := bstep (se 3 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 6689789 = 2508671) B2508671
theorem B139695547 : Blo 880569 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B3184409 : Blo 880569 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B4232999 : Blo 880569 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B956263 : Blo 880569 956263 := bstep (se 1 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 956263 = 1434395) B1434395
theorem B38639915 : Blo 880569 38639915 := bstep (se 1 (by rfl) ⟨28979936, by rfl⟩ : syracuseStep 38639915 = 57959873) B57959873
theorem B3581779 : Blo 880569 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B10725443 : Blo 880569 10725443 := bstep (se 1 (by rfl) ⟨8044082, by rfl⟩ : syracuseStep 10725443 = 16088165) B16088165
theorem B1321031 : Blo 880569 1321031 := bstep (se 1 (by rfl) ⟨990773, by rfl⟩ : syracuseStep 1321031 = 1981547) B1981547
theorem B4466825 : Blo 880569 4466825 := bstep (se 2 (by rfl) ⟨1675059, by rfl⟩ : syracuseStep 4466825 = 3350119) B3350119
theorem B8498135 : Blo 880569 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B10038329 : Blo 880569 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B2830457 : Blo 880569 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B1487099 : Blo 880569 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B1324169 : Blo 880569 1324169 := bstep (se 2 (by rfl) ⟨496563, by rfl⟩ : syracuseStep 1324169 = 993127) B993127
theorem B1324967 : Blo 880569 1324967 := bstep (se 1 (by rfl) ⟨993725, by rfl⟩ : syracuseStep 1324967 = 1987451) B1987451
theorem B87242795 : Blo 880569 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B1489063 : Blo 880569 1489063 := bstep (se 1 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 1489063 = 2233595) B2233595
theorem B18103121 : Blo 880569 18103121 := bstep (se 2 (by rfl) ⟨6788670, by rfl⟩ : syracuseStep 18103121 = 13577341) B13577341
theorem B1326023 : Blo 880569 1326023 := bstep (se 1 (by rfl) ⟨994517, by rfl⟩ : syracuseStep 1326023 = 1989035) B1989035
theorem B5356903 : Blo 880569 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B1983239 : Blo 880569 1983239 := bstep (se 1 (by rfl) ⟨1487429, by rfl⟩ : syracuseStep 1983239 = 2974859) B2974859
theorem B1983401 : Blo 880569 1983401 := bstep (se 2 (by rfl) ⟨743775, by rfl⟩ : syracuseStep 1983401 = 1487551) B1487551
theorem B4899799 : Blo 880569 4899799 := bstep (se 1 (by rfl) ⟨3674849, by rfl⟩ : syracuseStep 4899799 = 7349699) B7349699
theorem B12731519 : Blo 880569 12731519 := bstep (se 1 (by rfl) ⟨9548639, by rfl⟩ : syracuseStep 12731519 = 19097279) B19097279
theorem B1984103 : Blo 880569 1984103 := bstep (se 1 (by rfl) ⟨1488077, by rfl⟩ : syracuseStep 1984103 = 2976155) B2976155
theorem B1984481 : Blo 880569 1984481 := bstep (se 2 (by rfl) ⟨744180, by rfl⟩ : syracuseStep 1984481 = 1488361) B1488361
theorem B1988585 : Blo 880569 1988585 := bstep (se 2 (by rfl) ⟨745719, by rfl⟩ : syracuseStep 1988585 = 1491439) B1491439
theorem B1988639 : Blo 880569 1988639 := bstep (se 1 (by rfl) ⟨1491479, by rfl⟩ : syracuseStep 1988639 = 2982959) B2982959
theorem B9559367 : Blo 880569 9559367 := bstep (se 1 (by rfl) ⟨7169525, by rfl⟩ : syracuseStep 9559367 = 14339051) B14339051
theorem B27123173 : Blo 880569 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B33972857 : Blo 880569 33972857 := bstep (se 2 (by rfl) ⟨12739821, by rfl⟩ : syracuseStep 33972857 = 25479643) B25479643
theorem B22635449 : Blo 880569 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B6712145 : Blo 880569 6712145 := bstep (se 2 (by rfl) ⟨2517054, by rfl⟩ : syracuseStep 6712145 = 5034109) B5034109
theorem B10055825 : Blo 880569 10055825 := bstep (se 2 (by rfl) ⟨3770934, by rfl⟩ : syracuseStep 10055825 = 7541869) B7541869
theorem B881183 : Blo 880569 881183 := bstep (se 1 (by rfl) ⟨660887, by rfl⟩ : syracuseStep 881183 = 1321775) B1321775
theorem B75625163 : Blo 880569 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B11334491 : Blo 880569 11334491 := bstep (se 1 (by rfl) ⟨8500868, by rfl⟩ : syracuseStep 11334491 = 17001737) B17001737
theorem B881663 : Blo 880569 881663 := bstep (se 1 (by rfl) ⟨661247, by rfl⟩ : syracuseStep 881663 = 1322495) B1322495
theorem B4027751 : Blo 880569 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B7534079 : Blo 880569 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B882847 : Blo 880569 882847 := bstep (se 1 (by rfl) ⟨662135, by rfl⟩ : syracuseStep 882847 = 1324271) B1324271
theorem B883099 : Blo 880569 883099 := bstep (se 1 (by rfl) ⟨662324, by rfl⟩ : syracuseStep 883099 = 1324649) B1324649
theorem B3571303 : Blo 880569 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B8487679 : Blo 880569 8487679 := bstep (se 1 (by rfl) ⟨6365759, by rfl⟩ : syracuseStep 8487679 = 12731519) B12731519
theorem B3345563 : Blo 880569 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B4459859 : Blo 880569 4459859 := bstep (se 1 (by rfl) ⟨3344894, by rfl⟩ : syracuseStep 4459859 = 6689789) B6689789
theorem B25759943 : Blo 880569 25759943 := bstep (se 1 (by rfl) ⟨19319957, by rfl⟩ : syracuseStep 25759943 = 38639915) B38639915
theorem B22648571 : Blo 880569 22648571 := bstep (se 1 (by rfl) ⟨16986428, by rfl⟩ : syracuseStep 22648571 = 33972857) B33972857
theorem B7150295 : Blo 880569 7150295 := bstep (se 1 (by rfl) ⟨5362721, by rfl⟩ : syracuseStep 7150295 = 10725443) B10725443
theorem B186260729 : Blo 880569 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B6692219 : Blo 880569 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B991399 : Blo 880569 991399 := bstep (se 1 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 991399 = 1487099) B1487099
theorem B5022719 : Blo 880569 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B12068747 : Blo 880569 12068747 := bstep (se 1 (by rfl) ⟨9051560, by rfl⟩ : syracuseStep 12068747 = 18103121) B18103121
theorem B4761737 : Blo 880569 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B4238497 : Blo 880569 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B1322159 : Blo 880569 1322159 := bstep (se 1 (by rfl) ⟨991619, by rfl⟩ : syracuseStep 1322159 = 1983239) B1983239
theorem B1322267 : Blo 880569 1322267 := bstep (se 1 (by rfl) ⟨991700, by rfl⟩ : syracuseStep 1322267 = 1983401) B1983401
theorem B1322735 : Blo 880569 1322735 := bstep (se 1 (by rfl) ⟨992051, by rfl⟩ : syracuseStep 1322735 = 1984103) B1984103
theorem B6533065 : Blo 880569 6533065 := bstep (se 2 (by rfl) ⟨2449899, by rfl⟩ : syracuseStep 6533065 = 4899799) B4899799
theorem B1322987 : Blo 880569 1322987 := bstep (se 1 (by rfl) ⟨992240, by rfl⟩ : syracuseStep 1322987 = 1984481) B1984481
theorem B1325723 : Blo 880569 1325723 := bstep (se 1 (by rfl) ⟨994292, by rfl⟩ : syracuseStep 1325723 = 1988585) B1988585
theorem B1325759 : Blo 880569 1325759 := bstep (se 1 (by rfl) ⟨994319, by rfl⟩ : syracuseStep 1325759 = 1988639) B1988639
theorem B11287997 : Blo 880569 11287997 := bstep (se 3 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 11287997 = 4232999) B4232999
theorem B6372911 : Blo 880569 6372911 := bstep (se 1 (by rfl) ⟨4779683, by rfl⟩ : syracuseStep 6372911 = 9559367) B9559367
theorem B15090299 : Blo 880569 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B4474763 : Blo 880569 4474763 := bstep (se 1 (by rfl) ⟨3356072, by rfl⟩ : syracuseStep 4474763 = 6712145) B6712145
theorem B20400277 : Blo 880569 20400277 := bstep (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) B956263
theorem B22661693 : Blo 880569 22661693 := bstep (se 3 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 22661693 = 8498135) B8498135
theorem B1886971 : Blo 880569 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B6703883 : Blo 880569 6703883 := bstep (se 1 (by rfl) ⟨5027912, by rfl⟩ : syracuseStep 6703883 = 10055825) B10055825
theorem B1985417 : Blo 880569 1985417 := bstep (se 2 (by rfl) ⟨744531, by rfl⟩ : syracuseStep 1985417 = 1489063) B1489063
theorem B50416775 : Blo 880569 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B7556327 : Blo 880569 7556327 := bstep (se 1 (by rfl) ⟨5667245, by rfl⟩ : syracuseStep 7556327 = 11334491) B11334491
theorem B1989071 : Blo 880569 1989071 := bstep (se 1 (by rfl) ⟨1491803, by rfl⟩ : syracuseStep 1989071 = 2983607) B2983607
theorem B2383463 : Blo 880569 2383463 := bstep (se 1 (by rfl) ⟨1787597, by rfl⟩ : syracuseStep 2383463 = 3575195) B3575195
theorem B4775705 : Blo 880569 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B2973779 : Blo 880569 2973779 := bstep (se 1 (by rfl) ⟨2230334, by rfl⟩ : syracuseStep 2973779 = 4460669) B4460669
theorem B2122939 : Blo 880569 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B18082115 : Blo 880569 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B880687 : Blo 880569 880687 := bstep (se 1 (by rfl) ⟨660515, by rfl⟩ : syracuseStep 880687 = 1321031) B1321031
theorem B2977883 : Blo 880569 2977883 := bstep (se 1 (by rfl) ⟨2233412, by rfl⟩ : syracuseStep 2977883 = 4466825) B4466825
theorem B882779 : Blo 880569 882779 := bstep (se 1 (by rfl) ⟨662084, by rfl⟩ : syracuseStep 882779 = 1324169) B1324169
theorem B2685167 : Blo 880569 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B883311 : Blo 880569 883311 := bstep (se 1 (by rfl) ⟨662483, by rfl⟩ : syracuseStep 883311 = 1324967) B1324967
theorem B58161863 : Blo 880569 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B7142537 : Blo 880569 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B884015 : Blo 880569 884015 := bstep (se 1 (by rfl) ⟨663011, by rfl⟩ : syracuseStep 884015 = 1326023) B1326023
theorem B10060199 : Blo 880569 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B2983175 : Blo 880569 2983175 := bstep (se 1 (by rfl) ⟨2237381, by rfl⟩ : syracuseStep 2983175 = 4474763) B4474763
theorem B15107795 : Blo 880569 15107795 := bstep (se 1 (by rfl) ⟨11330846, by rfl⟩ : syracuseStep 15107795 = 22661693) B22661693
theorem B2230375 : Blo 880569 2230375 := bstep (se 1 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 2230375 = 3345563) B3345563
theorem B17173295 : Blo 880569 17173295 := bstep (se 1 (by rfl) ⟨12879971, by rfl⟩ : syracuseStep 17173295 = 25759943) B25759943
theorem B27200369 : Blo 880569 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B4461479 : Blo 880569 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B3183803 : Blo 880569 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B3348479 : Blo 880569 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B19046765 : Blo 880569 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B38774575 : Blo 880569 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B1321865 : Blo 880569 1321865 := bstep (se 2 (by rfl) ⟨495699, by rfl⟩ : syracuseStep 1321865 = 991399) B991399
theorem B11316905 : Blo 880569 11316905 := bstep (se 2 (by rfl) ⟨4243839, by rfl⟩ : syracuseStep 11316905 = 8487679) B8487679
theorem B4469255 : Blo 880569 4469255 := bstep (se 1 (by rfl) ⟨3351941, by rfl⟩ : syracuseStep 4469255 = 6703883) B6703883
theorem B1323611 : Blo 880569 1323611 := bstep (se 1 (by rfl) ⟨992708, by rfl⟩ : syracuseStep 1323611 = 1985417) B1985417
theorem B5651329 : Blo 880569 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B1326047 : Blo 880569 1326047 := bstep (se 1 (by rfl) ⟨994535, by rfl⟩ : syracuseStep 1326047 = 1989071) B1989071
theorem B4766863 : Blo 880569 4766863 := bstep (se 1 (by rfl) ⟨3575147, by rfl⟩ : syracuseStep 4766863 = 7150295) B7150295
theorem B1982519 : Blo 880569 1982519 := bstep (se 1 (by rfl) ⟨1486889, by rfl⟩ : syracuseStep 1982519 = 2973779) B2973779
theorem B11322341 : Blo 880569 11322341 := bstep (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) B2122939
theorem B8045831 : Blo 880569 8045831 := bstep (se 1 (by rfl) ⟨6034373, by rfl⟩ : syracuseStep 8045831 = 12068747) B12068747
theorem B1985255 : Blo 880569 1985255 := bstep (se 1 (by rfl) ⟨1488941, by rfl⟩ : syracuseStep 1985255 = 2977883) B2977883
theorem B1790111 : Blo 880569 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B7525331 : Blo 880569 7525331 := bstep (se 1 (by rfl) ⟨5643998, by rfl⟩ : syracuseStep 7525331 = 11287997) B11287997
theorem B4248607 : Blo 880569 4248607 := bstep (se 1 (by rfl) ⟨3186455, by rfl⟩ : syracuseStep 4248607 = 6372911) B6372911
theorem B33611183 : Blo 880569 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B5037551 : Blo 880569 5037551 := bstep (se 1 (by rfl) ⟨3778163, by rfl⟩ : syracuseStep 5037551 = 7556327) B7556327
theorem B2973239 : Blo 880569 2973239 := bstep (se 1 (by rfl) ⟨2229929, by rfl⟩ : syracuseStep 2973239 = 4459859) B4459859
theorem B2515961 : Blo 880569 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B15099047 : Blo 880569 15099047 := bstep (se 1 (by rfl) ⟨11324285, by rfl⟩ : syracuseStep 15099047 = 22648571) B22648571
theorem B8710753 : Blo 880569 8710753 := bstep (se 2 (by rfl) ⟨3266532, by rfl⟩ : syracuseStep 8710753 = 6533065) B6533065
theorem B3174491 : Blo 880569 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B12054743 : Blo 880569 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B881439 : Blo 880569 881439 := bstep (se 1 (by rfl) ⟨661079, by rfl⟩ : syracuseStep 881439 = 1322159) B1322159
theorem B881511 : Blo 880569 881511 := bstep (se 1 (by rfl) ⟨661133, by rfl⟩ : syracuseStep 881511 = 1322267) B1322267
theorem B881823 : Blo 880569 881823 := bstep (se 1 (by rfl) ⟨661367, by rfl⟩ : syracuseStep 881823 = 1322735) B1322735
theorem B881991 : Blo 880569 881991 := bstep (se 1 (by rfl) ⟨661493, by rfl⟩ : syracuseStep 881991 = 1322987) B1322987
theorem B496695277 : Blo 880569 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B6355901 : Blo 880569 6355901 := bstep (se 3 (by rfl) ⟨1191731, by rfl⟩ : syracuseStep 6355901 = 2383463) B2383463
theorem B883815 : Blo 880569 883815 := bstep (se 1 (by rfl) ⟨662861, by rfl⟩ : syracuseStep 883815 = 1325723) B1325723
theorem B883839 : Blo 880569 883839 := bstep (se 1 (by rfl) ⟨662879, by rfl⟩ : syracuseStep 883839 = 1325759) B1325759
theorem B5016887 : Blo 880569 5016887 := bstep (se 1 (by rfl) ⟨3762665, by rfl⟩ : syracuseStep 5016887 = 7525331) B7525331
theorem B2232319 : Blo 880569 2232319 := bstep (se 1 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 2232319 = 3348479) B3348479
theorem B10066031 : Blo 880569 10066031 := bstep (se 1 (by rfl) ⟨7549523, by rfl⟩ : syracuseStep 10066031 = 15099047) B15099047
theorem B7544603 : Blo 880569 7544603 := bstep (se 1 (by rfl) ⟨5658452, by rfl⟩ : syracuseStep 7544603 = 11316905) B11316905
theorem B8036495 : Blo 880569 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B4237267 : Blo 880569 4237267 := bstep (se 1 (by rfl) ⟨3177950, by rfl⟩ : syracuseStep 4237267 = 6355901) B6355901
theorem B1321679 : Blo 880569 1321679 := bstep (se 1 (by rfl) ⟨991259, by rfl⟩ : syracuseStep 1321679 = 1982519) B1982519
theorem B8465309 : Blo 880569 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B7548227 : Blo 880569 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B10071863 : Blo 880569 10071863 := bstep (se 1 (by rfl) ⟨7553897, by rfl⟩ : syracuseStep 10071863 = 15107795) B15107795
theorem B1323503 : Blo 880569 1323503 := bstep (se 1 (by rfl) ⟨992627, by rfl⟩ : syracuseStep 1323503 = 1985255) B1985255
theorem B11448863 : Blo 880569 11448863 := bstep (se 1 (by rfl) ⟨8586647, by rfl⟩ : syracuseStep 11448863 = 17173295) B17173295
theorem B18133579 : Blo 880569 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B11614337 : Blo 880569 11614337 := bstep (se 2 (by rfl) ⟨4355376, by rfl⟩ : syracuseStep 11614337 = 8710753) B8710753
theorem B3358367 : Blo 880569 3358367 := bstep (se 1 (by rfl) ⟨2518775, by rfl⟩ : syracuseStep 3358367 = 5037551) B5037551
theorem B1982159 : Blo 880569 1982159 := bstep (se 1 (by rfl) ⟨1486619, by rfl⟩ : syracuseStep 1982159 = 2973239) B2973239
theorem B12697843 : Blo 880569 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B662260369 : Blo 880569 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B6706799 : Blo 880569 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B4773629 : Blo 880569 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B1988783 : Blo 880569 1988783 := bstep (se 1 (by rfl) ⟨1491587, by rfl⟩ : syracuseStep 1988783 = 2983175) B2983175
theorem B51699433 : Blo 880569 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B6709229 : Blo 880569 6709229 := bstep (se 3 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 6709229 = 2515961) B2515961
theorem B2973833 : Blo 880569 2973833 := bstep (se 2 (by rfl) ⟨1115187, by rfl⟩ : syracuseStep 2973833 = 2230375) B2230375
theorem B2974319 : Blo 880569 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B21455549 : Blo 880569 21455549 := bstep (se 3 (by rfl) ⟨4022915, by rfl⟩ : syracuseStep 21455549 = 8045831) B8045831
theorem B2122535 : Blo 880569 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B22407455 : Blo 880569 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B5664809 : Blo 880569 5664809 := bstep (se 2 (by rfl) ⟨2124303, by rfl⟩ : syracuseStep 5664809 = 4248607) B4248607
theorem B881243 : Blo 880569 881243 := bstep (se 1 (by rfl) ⟨660932, by rfl⟩ : syracuseStep 881243 = 1321865) B1321865
theorem B2979503 : Blo 880569 2979503 := bstep (se 1 (by rfl) ⟨2234627, by rfl⟩ : syracuseStep 2979503 = 4469255) B4469255
theorem B882407 : Blo 880569 882407 := bstep (se 1 (by rfl) ⟨661805, by rfl⟩ : syracuseStep 882407 = 1323611) B1323611
theorem B7535105 : Blo 880569 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B6355817 : Blo 880569 6355817 := bstep (se 2 (by rfl) ⟨2383431, by rfl⟩ : syracuseStep 6355817 = 4766863) B4766863
theorem B884031 : Blo 880569 884031 := bstep (se 1 (by rfl) ⟨663023, by rfl⟩ : syracuseStep 884031 = 1326047) B1326047
theorem B3344591 : Blo 880569 3344591 := bstep (se 1 (by rfl) ⟨2508443, by rfl⟩ : syracuseStep 3344591 = 5016887) B5016887
theorem B3182419 : Blo 880569 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B5643539 : Blo 880569 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B3776539 : Blo 880569 3776539 := bstep (se 1 (by rfl) ⟨2832404, by rfl⟩ : syracuseStep 3776539 = 5664809) B5664809
theorem B7742891 : Blo 880569 7742891 := bstep (se 1 (by rfl) ⟨5807168, by rfl⟩ : syracuseStep 7742891 = 11614337) B11614337
theorem B5023403 : Blo 880569 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B4237211 : Blo 880569 4237211 := bstep (se 1 (by rfl) ⟨3177908, by rfl⟩ : syracuseStep 4237211 = 6355817) B6355817
theorem B2238911 : Blo 880569 2238911 := bstep (se 1 (by rfl) ⟨1679183, by rfl⟩ : syracuseStep 2238911 = 3358367) B3358367
theorem B1321439 : Blo 880569 1321439 := bstep (se 1 (by rfl) ⟨991079, by rfl⟩ : syracuseStep 1321439 = 1982159) B1982159
theorem B5649689 : Blo 880569 5649689 := bstep (se 2 (by rfl) ⟨2118633, by rfl⟩ : syracuseStep 5649689 = 4237267) B4237267
theorem B883013825 : Blo 880569 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B4471199 : Blo 880569 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B1325855 : Blo 880569 1325855 := bstep (se 1 (by rfl) ⟨994391, by rfl⟩ : syracuseStep 1325855 = 1988783) B1988783
theorem B5029735 : Blo 880569 5029735 := bstep (se 1 (by rfl) ⟨3772301, by rfl⟩ : syracuseStep 5029735 = 7544603) B7544603
theorem B4472819 : Blo 880569 4472819 := bstep (se 1 (by rfl) ⟨3354614, by rfl⟩ : syracuseStep 4472819 = 6709229) B6709229
theorem B1982555 : Blo 880569 1982555 := bstep (se 1 (by rfl) ⟨1486916, by rfl⟩ : syracuseStep 1982555 = 2973833) B2973833
theorem B5357663 : Blo 880569 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B1982879 : Blo 880569 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B14303699 : Blo 880569 14303699 := bstep (se 1 (by rfl) ⟨10727774, by rfl⟩ : syracuseStep 14303699 = 21455549) B21455549
theorem B59753213 : Blo 880569 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B5032151 : Blo 880569 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B1986335 : Blo 880569 1986335 := bstep (se 1 (by rfl) ⟨1489751, by rfl⟩ : syracuseStep 1986335 = 2979503) B2979503
theorem B68932577 : Blo 880569 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B16930457 : Blo 880569 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B5660093 : Blo 880569 5660093 := bstep (se 3 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 5660093 = 2122535) B2122535
theorem B6710687 : Blo 880569 6710687 := bstep (se 1 (by rfl) ⟨5033015, by rfl⟩ : syracuseStep 6710687 = 10066031) B10066031
theorem B2976425 : Blo 880569 2976425 := bstep (se 2 (by rfl) ⟨1116159, by rfl⟩ : syracuseStep 2976425 = 2232319) B2232319
theorem B24178105 : Blo 880569 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B881119 : Blo 880569 881119 := bstep (se 1 (by rfl) ⟨660839, by rfl⟩ : syracuseStep 881119 = 1321679) B1321679
theorem B6714575 : Blo 880569 6714575 := bstep (se 1 (by rfl) ⟨5035931, by rfl⟩ : syracuseStep 6714575 = 10071863) B10071863
theorem B882335 : Blo 880569 882335 := bstep (se 1 (by rfl) ⟨661751, by rfl⟩ : syracuseStep 882335 = 1323503) B1323503
theorem B7632575 : Blo 880569 7632575 := bstep (se 1 (by rfl) ⟨5724431, by rfl⟩ : syracuseStep 7632575 = 11448863) B11448863
theorem B3571775 : Blo 880569 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B9535799 : Blo 880569 9535799 := bstep (se 1 (by rfl) ⟨7151849, by rfl⟩ : syracuseStep 9535799 = 14303699) B14303699
theorem B2229727 : Blo 880569 2229727 := bstep (se 1 (by rfl) ⟨1672295, by rfl⟩ : syracuseStep 2229727 = 3344591) B3344591
theorem B20647709 : Blo 880569 20647709 := bstep (se 3 (by rfl) ⟨3871445, by rfl⟩ : syracuseStep 20647709 = 7742891) B7742891
theorem B3773395 : Blo 880569 3773395 := bstep (se 1 (by rfl) ⟨2830046, by rfl⟩ : syracuseStep 3773395 = 5660093) B5660093
theorem B3348935 : Blo 880569 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B2824807 : Blo 880569 2824807 := bstep (se 1 (by rfl) ⟨2118605, by rfl⟩ : syracuseStep 2824807 = 4237211) B4237211
theorem B5088383 : Blo 880569 5088383 := bstep (se 1 (by rfl) ⟨3816287, by rfl⟩ : syracuseStep 5088383 = 7632575) B7632575
theorem B1321703 : Blo 880569 1321703 := bstep (se 1 (by rfl) ⟨991277, by rfl⟩ : syracuseStep 1321703 = 1982555) B1982555
theorem B1321919 : Blo 880569 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B3354767 : Blo 880569 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B1324223 : Blo 880569 1324223 := bstep (se 1 (by rfl) ⟨993167, by rfl⟩ : syracuseStep 1324223 = 1986335) B1986335
theorem B11286971 : Blo 880569 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B4243225 : Blo 880569 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B4473791 : Blo 880569 4473791 := bstep (se 1 (by rfl) ⟨3355343, by rfl⟩ : syracuseStep 4473791 = 6710687) B6710687
theorem B1492607 : Blo 880569 1492607 := bstep (se 1 (by rfl) ⟨1119455, by rfl⟩ : syracuseStep 1492607 = 2238911) B2238911
theorem B1984283 : Blo 880569 1984283 := bstep (se 1 (by rfl) ⟨1488212, by rfl⟩ : syracuseStep 1984283 = 2976425) B2976425
theorem B4476383 : Blo 880569 4476383 := bstep (se 1 (by rfl) ⟨3357287, by rfl⟩ : syracuseStep 4476383 = 6714575) B6714575
theorem B6706313 : Blo 880569 6706313 := bstep (se 2 (by rfl) ⟨2514867, by rfl⟩ : syracuseStep 6706313 = 5029735) B5029735
theorem B5035385 : Blo 880569 5035385 := bstep (se 2 (by rfl) ⟨1888269, by rfl⟩ : syracuseStep 5035385 = 3776539) B3776539
theorem B39835475 : Blo 880569 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B183820205 : Blo 880569 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B32237473 : Blo 880569 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B3762359 : Blo 880569 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B880959 : Blo 880569 880959 := bstep (se 1 (by rfl) ⟨660719, by rfl⟩ : syracuseStep 880959 = 1321439) B1321439
theorem B3766459 : Blo 880569 3766459 := bstep (se 1 (by rfl) ⟨2824844, by rfl⟩ : syracuseStep 3766459 = 5649689) B5649689
theorem B588675883 : Blo 880569 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B2980799 : Blo 880569 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B883903 : Blo 880569 883903 := bstep (se 1 (by rfl) ⟨662927, by rfl⟩ : syracuseStep 883903 = 1325855) B1325855
theorem B2981879 : Blo 880569 2981879 := bstep (se 1 (by rfl) ⟨2236409, by rfl⟩ : syracuseStep 2981879 = 4472819) B4472819
theorem B6357199 : Blo 880569 6357199 := bstep (se 1 (by rfl) ⟨4767899, by rfl⟩ : syracuseStep 6357199 = 9535799) B9535799
theorem B2982527 : Blo 880569 2982527 := bstep (se 1 (by rfl) ⟨2236895, by rfl⟩ : syracuseStep 2982527 = 4473791) B4473791
theorem B2984255 : Blo 880569 2984255 := bstep (se 1 (by rfl) ⟨2238191, by rfl⟩ : syracuseStep 2984255 = 4476383) B4476383
theorem B13765139 : Blo 880569 13765139 := bstep (se 1 (by rfl) ⟨10323854, by rfl⟩ : syracuseStep 13765139 = 20647709) B20647709
theorem B2232623 : Blo 880569 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B2236511 : Blo 880569 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B5021945 : Blo 880569 5021945 := bstep (se 2 (by rfl) ⟨1883229, by rfl⟩ : syracuseStep 5021945 = 3766459) B3766459
theorem B784901177 : Blo 880569 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B995071 : Blo 880569 995071 := bstep (se 1 (by rfl) ⟨746303, by rfl⟩ : syracuseStep 995071 = 1492607) B1492607
theorem B1322855 : Blo 880569 1322855 := bstep (se 1 (by rfl) ⟨992141, by rfl⟩ : syracuseStep 1322855 = 1984283) B1984283
theorem B4470875 : Blo 880569 4470875 := bstep (se 1 (by rfl) ⟨3353156, by rfl⟩ : syracuseStep 4470875 = 6706313) B6706313
theorem B3356923 : Blo 880569 3356923 := bstep (se 1 (by rfl) ⟨2517692, by rfl⟩ : syracuseStep 3356923 = 5035385) B5035385
theorem B26556983 : Blo 880569 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B3392255 : Blo 880569 3392255 := bstep (se 1 (by rfl) ⟨2544191, by rfl⟩ : syracuseStep 3392255 = 5088383) B5088383
theorem B5031193 : Blo 880569 5031193 := bstep (se 2 (by rfl) ⟨1886697, by rfl⟩ : syracuseStep 5031193 = 3773395) B3773395
theorem B2508239 : Blo 880569 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B7524647 : Blo 880569 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B1987199 : Blo 880569 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B5657633 : Blo 880569 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B1987919 : Blo 880569 1987919 := bstep (se 1 (by rfl) ⟨1490939, by rfl⟩ : syracuseStep 1987919 = 2981879) B2981879
theorem B2381183 : Blo 880569 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B2972969 : Blo 880569 2972969 := bstep (se 2 (by rfl) ⟨1114863, by rfl⟩ : syracuseStep 2972969 = 2229727) B2229727
theorem B42983297 : Blo 880569 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B122546803 : Blo 880569 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B881135 : Blo 880569 881135 := bstep (se 1 (by rfl) ⟨660851, by rfl⟩ : syracuseStep 881135 = 1321703) B1321703
theorem B881279 : Blo 880569 881279 := bstep (se 1 (by rfl) ⟨660959, by rfl⟩ : syracuseStep 881279 = 1321919) B1321919
theorem B882815 : Blo 880569 882815 := bstep (se 1 (by rfl) ⟨662111, by rfl⟩ : syracuseStep 882815 = 1324223) B1324223
theorem B3766409 : Blo 880569 3766409 := bstep (se 2 (by rfl) ⟨1412403, by rfl⟩ : syracuseStep 3766409 = 2824807) B2824807
theorem B1672159 : Blo 880569 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B9176759 : Blo 880569 9176759 := bstep (se 1 (by rfl) ⟨6882569, by rfl⟩ : syracuseStep 9176759 = 13765139) B13765139
theorem B9046013 : Blo 880569 9046013 := bstep (se 3 (by rfl) ⟨1696127, by rfl⟩ : syracuseStep 9046013 = 3392255) B3392255
theorem B5016431 : Blo 880569 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B3771755 : Blo 880569 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B3347963 : Blo 880569 3347963 := bstep (se 1 (by rfl) ⟨2510972, by rfl⟩ : syracuseStep 3347963 = 5021945) B5021945
theorem B17704655 : Blo 880569 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B1488415 : Blo 880569 1488415 := bstep (se 1 (by rfl) ⟨1116311, by rfl⟩ : syracuseStep 1488415 = 2232623) B2232623
theorem B1324799 : Blo 880569 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B163395737 : Blo 880569 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B1325279 : Blo 880569 1325279 := bstep (se 1 (by rfl) ⟨993959, by rfl⟩ : syracuseStep 1325279 = 1987919) B1987919
theorem B1587455 : Blo 880569 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B1981979 : Blo 880569 1981979 := bstep (se 1 (by rfl) ⟨1486484, by rfl⟩ : syracuseStep 1981979 = 2972969) B2972969
theorem B1326761 : Blo 880569 1326761 := bstep (se 2 (by rfl) ⟨497535, by rfl⟩ : syracuseStep 1326761 = 995071) B995071
theorem B28655531 : Blo 880569 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B1491007 : Blo 880569 1491007 := bstep (se 1 (by rfl) ⟨1118255, by rfl⟩ : syracuseStep 1491007 = 2236511) B2236511
theorem B4475897 : Blo 880569 4475897 := bstep (se 2 (by rfl) ⟨1678461, by rfl⟩ : syracuseStep 4475897 = 3356923) B3356923
theorem B2510939 : Blo 880569 2510939 := bstep (se 1 (by rfl) ⟨1883204, by rfl⟩ : syracuseStep 2510939 = 3766409) B3766409
theorem B8476265 : Blo 880569 8476265 := bstep (se 2 (by rfl) ⟨3178599, by rfl⟩ : syracuseStep 8476265 = 6357199) B6357199
theorem B1988351 : Blo 880569 1988351 := bstep (se 1 (by rfl) ⟨1491263, by rfl⟩ : syracuseStep 1988351 = 2982527) B2982527
theorem B1989503 : Blo 880569 1989503 := bstep (se 1 (by rfl) ⟨1492127, by rfl⟩ : syracuseStep 1989503 = 2984255) B2984255
theorem B6708257 : Blo 880569 6708257 := bstep (se 2 (by rfl) ⟨2515596, by rfl⟩ : syracuseStep 6708257 = 5031193) B5031193
theorem B523267451 : Blo 880569 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B881903 : Blo 880569 881903 := bstep (se 1 (by rfl) ⟨661427, by rfl⟩ : syracuseStep 881903 = 1322855) B1322855
theorem B2980583 : Blo 880569 2980583 := bstep (se 1 (by rfl) ⟨2235437, by rfl⟩ : syracuseStep 2980583 = 4470875) B4470875
theorem B2229545 : Blo 880569 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B3344287 : Blo 880569 3344287 := bstep (se 1 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 3344287 = 5016431) B5016431
theorem B2983931 : Blo 880569 2983931 := bstep (se 1 (by rfl) ⟨2237948, by rfl⟩ : syracuseStep 2983931 = 4475897) B4475897
theorem B1673959 : Blo 880569 1673959 := bstep (se 1 (by rfl) ⟨1255469, by rfl⟩ : syracuseStep 1673959 = 2510939) B2510939
theorem B2231975 : Blo 880569 2231975 := bstep (se 1 (by rfl) ⟨1673981, by rfl⟩ : syracuseStep 2231975 = 3347963) B3347963
theorem B24122701 : Blo 880569 24122701 := bstep (se 3 (by rfl) ⟨4523006, by rfl⟩ : syracuseStep 24122701 = 9046013) B9046013
theorem B11803103 : Blo 880569 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B108930491 : Blo 880569 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B1058303 : Blo 880569 1058303 := bstep (se 1 (by rfl) ⟨793727, by rfl⟩ : syracuseStep 1058303 = 1587455) B1587455
theorem B1321319 : Blo 880569 1321319 := bstep (se 1 (by rfl) ⟨990989, by rfl⟩ : syracuseStep 1321319 = 1981979) B1981979
theorem B5650843 : Blo 880569 5650843 := bstep (se 1 (by rfl) ⟨4238132, by rfl⟩ : syracuseStep 5650843 = 8476265) B8476265
theorem B1325567 : Blo 880569 1325567 := bstep (se 1 (by rfl) ⟨994175, by rfl⟩ : syracuseStep 1325567 = 1988351) B1988351
theorem B1326335 : Blo 880569 1326335 := bstep (se 1 (by rfl) ⟨994751, by rfl⟩ : syracuseStep 1326335 = 1989503) B1989503
theorem B4472171 : Blo 880569 4472171 := bstep (se 1 (by rfl) ⟨3354128, by rfl⟩ : syracuseStep 4472171 = 6708257) B6708257
theorem B1984553 : Blo 880569 1984553 := bstep (se 2 (by rfl) ⟨744207, by rfl⟩ : syracuseStep 1984553 = 1488415) B1488415
theorem B1987055 : Blo 880569 1987055 := bstep (se 1 (by rfl) ⟨1490291, by rfl⟩ : syracuseStep 1987055 = 2980583) B2980583
theorem B1988009 : Blo 880569 1988009 := bstep (se 2 (by rfl) ⟨745503, by rfl⟩ : syracuseStep 1988009 = 1491007) B1491007
theorem B6117839 : Blo 880569 6117839 := bstep (se 1 (by rfl) ⟨4588379, by rfl⟩ : syracuseStep 6117839 = 9176759) B9176759
theorem B2514503 : Blo 880569 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B348844967 : Blo 880569 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B883199 : Blo 880569 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B883519 : Blo 880569 883519 := bstep (se 1 (by rfl) ⟨662639, by rfl⟩ : syracuseStep 883519 = 1325279) B1325279
theorem B884507 : Blo 880569 884507 := bstep (se 1 (by rfl) ⟨663380, by rfl⟩ : syracuseStep 884507 = 1326761) B1326761
theorem B19103687 : Blo 880569 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B4459049 : Blo 880569 4459049 := bstep (se 2 (by rfl) ⟨1672143, by rfl⟩ : syracuseStep 4459049 = 3344287) B3344287
theorem B2231945 : Blo 880569 2231945 := bstep (se 2 (by rfl) ⟨836979, by rfl⟩ : syracuseStep 2231945 = 1673959) B1673959
theorem B2822141 : Blo 880569 2822141 := bstep (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) B1058303
theorem B7868735 : Blo 880569 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B72620327 : Blo 880569 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B232563311 : Blo 880569 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B1486363 : Blo 880569 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B1323035 : Blo 880569 1323035 := bstep (se 1 (by rfl) ⟨992276, by rfl⟩ : syracuseStep 1323035 = 1984553) B1984553
theorem B1487983 : Blo 880569 1487983 := bstep (se 1 (by rfl) ⟨1115987, by rfl⟩ : syracuseStep 1487983 = 2231975) B2231975
theorem B1324703 : Blo 880569 1324703 := bstep (se 1 (by rfl) ⟨993527, by rfl⟩ : syracuseStep 1324703 = 1987055) B1987055
theorem B1325339 : Blo 880569 1325339 := bstep (se 1 (by rfl) ⟨994004, by rfl⟩ : syracuseStep 1325339 = 1988009) B1988009
theorem B4078559 : Blo 880569 4078559 := bstep (se 1 (by rfl) ⟨3058919, by rfl⟩ : syracuseStep 4078559 = 6117839) B6117839
theorem B32163601 : Blo 880569 32163601 := bstep (se 2 (by rfl) ⟨12061350, by rfl⟩ : syracuseStep 32163601 = 24122701) B24122701
theorem B6705341 : Blo 880569 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B12735791 : Blo 880569 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B1989287 : Blo 880569 1989287 := bstep (se 1 (by rfl) ⟨1491965, by rfl⟩ : syracuseStep 1989287 = 2983931) B2983931
theorem B880879 : Blo 880569 880879 := bstep (se 1 (by rfl) ⟨660659, by rfl⟩ : syracuseStep 880879 = 1321319) B1321319
theorem B7534457 : Blo 880569 7534457 := bstep (se 2 (by rfl) ⟨2825421, by rfl⟩ : syracuseStep 7534457 = 5650843) B5650843
theorem B883711 : Blo 880569 883711 := bstep (se 1 (by rfl) ⟨662783, by rfl⟩ : syracuseStep 883711 = 1325567) B1325567
theorem B884223 : Blo 880569 884223 := bstep (se 1 (by rfl) ⟨663167, by rfl⟩ : syracuseStep 884223 = 1326335) B1326335
theorem B2981447 : Blo 880569 2981447 := bstep (se 1 (by rfl) ⟨2236085, by rfl⟩ : syracuseStep 2981447 = 4472171) B4472171
theorem B5245823 : Blo 880569 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B8490527 : Blo 880569 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B5022971 : Blo 880569 5022971 := bstep (se 1 (by rfl) ⟨3767228, by rfl⟩ : syracuseStep 5022971 = 7534457) B7534457
theorem B1487963 : Blo 880569 1487963 := bstep (se 1 (by rfl) ⟨1115972, by rfl⟩ : syracuseStep 1487963 = 2231945) B2231945
theorem B4470227 : Blo 880569 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B48413551 : Blo 880569 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B1326191 : Blo 880569 1326191 := bstep (se 1 (by rfl) ⟨994643, by rfl⟩ : syracuseStep 1326191 = 1989287) B1989287
theorem B1981817 : Blo 880569 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B155042207 : Blo 880569 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B1983977 : Blo 880569 1983977 := bstep (se 2 (by rfl) ⟨743991, by rfl⟩ : syracuseStep 1983977 = 1487983) B1487983
theorem B1987631 : Blo 880569 1987631 := bstep (se 1 (by rfl) ⟨1490723, by rfl⟩ : syracuseStep 1987631 = 2981447) B2981447
theorem B7525709 : Blo 880569 7525709 := bstep (se 3 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 7525709 = 2822141) B2822141
theorem B2972699 : Blo 880569 2972699 := bstep (se 1 (by rfl) ⟨2229524, by rfl⟩ : syracuseStep 2972699 = 4459049) B4459049
theorem B42884801 : Blo 880569 42884801 := bstep (se 2 (by rfl) ⟨16081800, by rfl⟩ : syracuseStep 42884801 = 32163601) B32163601
theorem B10876157 : Blo 880569 10876157 := bstep (se 3 (by rfl) ⟨2039279, by rfl⟩ : syracuseStep 10876157 = 4078559) B4078559
theorem B882023 : Blo 880569 882023 := bstep (se 1 (by rfl) ⟨661517, by rfl⟩ : syracuseStep 882023 = 1323035) B1323035
theorem B883135 : Blo 880569 883135 := bstep (se 1 (by rfl) ⟨662351, by rfl⟩ : syracuseStep 883135 = 1324703) B1324703
theorem B883559 : Blo 880569 883559 := bstep (se 1 (by rfl) ⟨662669, by rfl⟩ : syracuseStep 883559 = 1325339) B1325339
theorem B5017139 : Blo 880569 5017139 := bstep (se 1 (by rfl) ⟨3762854, by rfl⟩ : syracuseStep 5017139 = 7525709) B7525709
theorem B3348647 : Blo 880569 3348647 := bstep (se 1 (by rfl) ⟨2511485, by rfl⟩ : syracuseStep 3348647 = 5022971) B5022971
theorem B991975 : Blo 880569 991975 := bstep (se 1 (by rfl) ⟨743981, by rfl⟩ : syracuseStep 991975 = 1487963) B1487963
theorem B7250771 : Blo 880569 7250771 := bstep (se 1 (by rfl) ⟨5438078, by rfl⟩ : syracuseStep 7250771 = 10876157) B10876157
theorem B1321211 : Blo 880569 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B103361471 : Blo 880569 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B1322651 : Blo 880569 1322651 := bstep (se 1 (by rfl) ⟨991988, by rfl⟩ : syracuseStep 1322651 = 1983977) B1983977
theorem B1325087 : Blo 880569 1325087 := bstep (se 1 (by rfl) ⟨993815, by rfl⟩ : syracuseStep 1325087 = 1987631) B1987631
theorem B1981799 : Blo 880569 1981799 := bstep (se 1 (by rfl) ⟨1486349, by rfl⟩ : syracuseStep 1981799 = 2972699) B2972699
theorem B28589867 : Blo 880569 28589867 := bstep (se 1 (by rfl) ⟨21442400, by rfl⟩ : syracuseStep 28589867 = 42884801) B42884801
theorem B3497215 : Blo 880569 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B5660351 : Blo 880569 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B2980151 : Blo 880569 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B64551401 : Blo 880569 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B884127 : Blo 880569 884127 := bstep (se 1 (by rfl) ⟨663095, by rfl⟩ : syracuseStep 884127 = 1326191) B1326191
theorem B3344759 : Blo 880569 3344759 := bstep (se 1 (by rfl) ⟨2508569, by rfl⟩ : syracuseStep 3344759 = 5017139) B5017139
theorem B2232431 : Blo 880569 2232431 := bstep (se 1 (by rfl) ⟨1674323, by rfl⟩ : syracuseStep 2232431 = 3348647) B3348647
theorem B3773567 : Blo 880569 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B43034267 : Blo 880569 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B4662953 : Blo 880569 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B1321199 : Blo 880569 1321199 := bstep (se 1 (by rfl) ⟨990899, by rfl⟩ : syracuseStep 1321199 = 1981799) B1981799
theorem B1322633 : Blo 880569 1322633 := bstep (se 2 (by rfl) ⟨495987, by rfl⟩ : syracuseStep 1322633 = 991975) B991975
theorem B4833847 : Blo 880569 4833847 := bstep (se 1 (by rfl) ⟨3625385, by rfl⟩ : syracuseStep 4833847 = 7250771) B7250771
theorem B1986767 : Blo 880569 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B19059911 : Blo 880569 19059911 := bstep (se 1 (by rfl) ⟨14294933, by rfl⟩ : syracuseStep 19059911 = 28589867) B28589867
theorem B880807 : Blo 880569 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B68907647 : Blo 880569 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B881767 : Blo 880569 881767 := bstep (se 1 (by rfl) ⟨661325, by rfl⟩ : syracuseStep 881767 = 1322651) B1322651
theorem B883391 : Blo 880569 883391 := bstep (se 1 (by rfl) ⟨662543, by rfl⟩ : syracuseStep 883391 = 1325087) B1325087
theorem B2229839 : Blo 880569 2229839 := bstep (se 1 (by rfl) ⟨1672379, by rfl⟩ : syracuseStep 2229839 = 3344759) B3344759
theorem B1488287 : Blo 880569 1488287 := bstep (se 1 (by rfl) ⟨1116215, by rfl⟩ : syracuseStep 1488287 = 2232431) B2232431
theorem B1324511 : Blo 880569 1324511 := bstep (se 1 (by rfl) ⟨993383, by rfl⟩ : syracuseStep 1324511 = 1986767) B1986767
theorem B28689511 : Blo 880569 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B6445129 : Blo 880569 6445129 := bstep (se 2 (by rfl) ⟨2416923, by rfl⟩ : syracuseStep 6445129 = 4833847) B4833847
theorem B2515711 : Blo 880569 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B12706607 : Blo 880569 12706607 := bstep (se 1 (by rfl) ⟨9529955, by rfl⟩ : syracuseStep 12706607 = 19059911) B19059911
theorem B3108635 : Blo 880569 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B880799 : Blo 880569 880799 := bstep (se 1 (by rfl) ⟨660599, by rfl⟩ : syracuseStep 880799 = 1321199) B1321199
theorem B881755 : Blo 880569 881755 := bstep (se 1 (by rfl) ⟨661316, by rfl⟩ : syracuseStep 881755 = 1322633) B1322633
theorem B45938431 : Blo 880569 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B61251241 : Blo 880569 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B2072423 : Blo 880569 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B8593505 : Blo 880569 8593505 := bstep (se 2 (by rfl) ⟨3222564, by rfl⟩ : syracuseStep 8593505 = 6445129) B6445129
theorem B992191 : Blo 880569 992191 := bstep (se 1 (by rfl) ⟨744143, by rfl⟩ : syracuseStep 992191 = 1488287) B1488287
theorem B3354281 : Blo 880569 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B1486559 : Blo 880569 1486559 := bstep (se 1 (by rfl) ⟨1114919, by rfl⟩ : syracuseStep 1486559 = 2229839) B2229839
theorem B38252681 : Blo 880569 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B8471071 : Blo 880569 8471071 := bstep (se 1 (by rfl) ⟨6353303, by rfl⟩ : syracuseStep 8471071 = 12706607) B12706607
theorem B883007 : Blo 880569 883007 := bstep (se 1 (by rfl) ⟨662255, by rfl⟩ : syracuseStep 883007 = 1324511) B1324511
theorem B2236187 : Blo 880569 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B991039 : Blo 880569 991039 := bstep (se 1 (by rfl) ⟨743279, by rfl⟩ : syracuseStep 991039 = 1486559) B1486559
theorem B25501787 : Blo 880569 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B81668321 : Blo 880569 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B1322921 : Blo 880569 1322921 := bstep (se 2 (by rfl) ⟨496095, by rfl⟩ : syracuseStep 1322921 = 992191) B992191
theorem B5526461 : Blo 880569 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B11294761 : Blo 880569 11294761 := bstep (se 2 (by rfl) ⟨4235535, by rfl⟩ : syracuseStep 11294761 = 8471071) B8471071
theorem B5729003 : Blo 880569 5729003 := bstep (se 1 (by rfl) ⟨4296752, by rfl⟩ : syracuseStep 5729003 = 8593505) B8593505
theorem B1321385 : Blo 880569 1321385 := bstep (se 2 (by rfl) ⟨495519, by rfl⟩ : syracuseStep 1321385 = 991039) B991039
theorem B3684307 : Blo 880569 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B1490791 : Blo 880569 1490791 := bstep (se 1 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 1490791 = 2236187) B2236187
theorem B54445547 : Blo 880569 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B3819335 : Blo 880569 3819335 := bstep (se 1 (by rfl) ⟨2864501, by rfl⟩ : syracuseStep 3819335 = 5729003) B5729003
theorem B15059681 : Blo 880569 15059681 := bstep (se 2 (by rfl) ⟨5647380, by rfl⟩ : syracuseStep 15059681 = 11294761) B11294761
theorem B17001191 : Blo 880569 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B881947 : Blo 880569 881947 := bstep (se 1 (by rfl) ⟨661460, by rfl⟩ : syracuseStep 881947 = 1322921) B1322921
theorem B40739573 : Blo 880569 40739573 := bstep (se 5 (by rfl) ⟨1909667, by rfl⟩ : syracuseStep 40739573 = 3819335) B3819335
theorem B10039787 : Blo 880569 10039787 := bstep (se 1 (by rfl) ⟨7529840, by rfl⟩ : syracuseStep 10039787 = 15059681) B15059681
theorem B1987721 : Blo 880569 1987721 := bstep (se 2 (by rfl) ⟨745395, by rfl⟩ : syracuseStep 1987721 = 1490791) B1490791
theorem B36297031 : Blo 880569 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B880923 : Blo 880569 880923 := bstep (se 1 (by rfl) ⟨660692, by rfl⟩ : syracuseStep 880923 = 1321385) B1321385
theorem B11334127 : Blo 880569 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B4912409 : Blo 880569 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B15112169 : Blo 880569 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B6693191 : Blo 880569 6693191 := bstep (se 1 (by rfl) ⟨5019893, by rfl⟩ : syracuseStep 6693191 = 10039787) B10039787
theorem B1325147 : Blo 880569 1325147 := bstep (se 1 (by rfl) ⟨993860, by rfl⟩ : syracuseStep 1325147 = 1987721) B1987721
theorem B27159715 : Blo 880569 27159715 := bstep (se 1 (by rfl) ⟨20369786, by rfl⟩ : syracuseStep 27159715 = 40739573) B40739573
theorem B48396041 : Blo 880569 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B3274939 : Blo 880569 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B4462127 : Blo 880569 4462127 := bstep (se 1 (by rfl) ⟨3346595, by rfl⟩ : syracuseStep 4462127 = 6693191) B6693191
theorem B4366585 : Blo 880569 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B10074779 : Blo 880569 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B144851813 : Blo 880569 144851813 := bstep (se 4 (by rfl) ⟨13579857, by rfl⟩ : syracuseStep 144851813 = 27159715) B27159715
theorem B32264027 : Blo 880569 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B883431 : Blo 880569 883431 := bstep (se 1 (by rfl) ⟨662573, by rfl⟩ : syracuseStep 883431 = 1325147) B1325147
theorem B96567875 : Blo 880569 96567875 := bstep (se 1 (by rfl) ⟨72425906, by rfl⟩ : syracuseStep 96567875 = 144851813) B144851813
theorem B21509351 : Blo 880569 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B5822113 : Blo 880569 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B2974751 : Blo 880569 2974751 := bstep (se 1 (by rfl) ⟨2231063, by rfl⟩ : syracuseStep 2974751 = 4462127) B4462127
theorem B6716519 : Blo 880569 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B1983167 : Blo 880569 1983167 := bstep (se 1 (by rfl) ⟨1487375, by rfl⟩ : syracuseStep 1983167 = 2974751) B2974751
theorem B14339567 : Blo 880569 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B4477679 : Blo 880569 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B64378583 : Blo 880569 64378583 := bstep (se 1 (by rfl) ⟨48283937, by rfl⟩ : syracuseStep 64378583 = 96567875) B96567875
theorem B7762817 : Blo 880569 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B2985119 : Blo 880569 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B1322111 : Blo 880569 1322111 := bstep (se 1 (by rfl) ⟨991583, by rfl⟩ : syracuseStep 1322111 = 1983167) B1983167
theorem B9559711 : Blo 880569 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B20700845 : Blo 880569 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B42919055 : Blo 880569 42919055 := bstep (se 1 (by rfl) ⟨32189291, by rfl⟩ : syracuseStep 42919055 = 64378583) B64378583
theorem B13800563 : Blo 880569 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B28612703 : Blo 880569 28612703 := bstep (se 1 (by rfl) ⟨21459527, by rfl⟩ : syracuseStep 28612703 = 42919055) B42919055
theorem B1990079 : Blo 880569 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B881407 : Blo 880569 881407 := bstep (se 1 (by rfl) ⟨661055, by rfl⟩ : syracuseStep 881407 = 1322111) B1322111
theorem B12746281 : Blo 880569 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B19075135 : Blo 880569 19075135 := bstep (se 1 (by rfl) ⟨14306351, by rfl⟩ : syracuseStep 19075135 = 28612703) B28612703
theorem B1326719 : Blo 880569 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B16995041 : Blo 880569 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B9200375 : Blo 880569 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B25433513 : Blo 880569 25433513 := bstep (se 2 (by rfl) ⟨9537567, by rfl⟩ : syracuseStep 25433513 = 19075135) B19075135
theorem B6133583 : Blo 880569 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B11330027 : Blo 880569 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B884479 : Blo 880569 884479 := bstep (se 1 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 884479 = 1326719) B1326719
theorem B16955675 : Blo 880569 16955675 := bstep (se 1 (by rfl) ⟨12716756, by rfl⟩ : syracuseStep 16955675 = 25433513) B25433513
theorem B7553351 : Blo 880569 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B4089055 : Blo 880569 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B5452073 : Blo 880569 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B5035567 : Blo 880569 5035567 := bstep (se 1 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 5035567 = 7553351) B7553351
theorem B11303783 : Blo 880569 11303783 := bstep (se 1 (by rfl) ⟨8477837, by rfl⟩ : syracuseStep 11303783 = 16955675) B16955675
theorem B6714089 : Blo 880569 6714089 := bstep (se 2 (by rfl) ⟨2517783, by rfl⟩ : syracuseStep 6714089 = 5035567) B5035567
theorem B3634715 : Blo 880569 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B7535855 : Blo 880569 7535855 := bstep (se 1 (by rfl) ⟨5651891, by rfl⟩ : syracuseStep 7535855 = 11303783) B11303783
theorem B5023903 : Blo 880569 5023903 := bstep (se 1 (by rfl) ⟨3767927, by rfl⟩ : syracuseStep 5023903 = 7535855) B7535855
theorem B4476059 : Blo 880569 4476059 := bstep (se 1 (by rfl) ⟨3357044, by rfl⟩ : syracuseStep 4476059 = 6714089) B6714089
theorem B2423143 : Blo 880569 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B2984039 : Blo 880569 2984039 := bstep (se 1 (by rfl) ⟨2238029, by rfl⟩ : syracuseStep 2984039 = 4476059) B4476059
theorem B6698537 : Blo 880569 6698537 := bstep (se 2 (by rfl) ⟨2511951, by rfl⟩ : syracuseStep 6698537 = 5023903) B5023903
theorem B3230857 : Blo 880569 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B4465691 : Blo 880569 4465691 := bstep (se 1 (by rfl) ⟨3349268, by rfl⟩ : syracuseStep 4465691 = 6698537) B6698537
theorem B1989359 : Blo 880569 1989359 := bstep (se 1 (by rfl) ⟨1492019, by rfl⟩ : syracuseStep 1989359 = 2984039) B2984039
theorem B17231237 : Blo 880569 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B1326239 : Blo 880569 1326239 := bstep (se 1 (by rfl) ⟨994679, by rfl⟩ : syracuseStep 1326239 = 1989359) B1989359
theorem B11487491 : Blo 880569 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B2977127 : Blo 880569 2977127 := bstep (se 1 (by rfl) ⟨2232845, by rfl⟩ : syracuseStep 2977127 = 4465691) B4465691
theorem B1984751 : Blo 880569 1984751 := bstep (se 1 (by rfl) ⟨1488563, by rfl⟩ : syracuseStep 1984751 = 2977127) B2977127
theorem B7658327 : Blo 880569 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B884159 : Blo 880569 884159 := bstep (se 1 (by rfl) ⟨663119, by rfl⟩ : syracuseStep 884159 = 1326239) B1326239
theorem B1323167 : Blo 880569 1323167 := bstep (se 1 (by rfl) ⟨992375, by rfl⟩ : syracuseStep 1323167 = 1984751) B1984751
theorem B5105551 : Blo 880569 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B6807401 : Blo 880569 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B882111 : Blo 880569 882111 := bstep (se 1 (by rfl) ⟨661583, by rfl⟩ : syracuseStep 882111 = 1323167) B1323167
theorem B4538267 : Blo 880569 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B3025511 : Blo 880569 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B2017007 : Blo 880569 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B1344671 : Blo 880569 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007
theorem B896447 : Blo 880569 896447 := bstep (se 1 (by rfl) ⟨672335, by rfl⟩ : syracuseStep 896447 = 1344671) B1344671
theorem B2390525 : Blo 880569 2390525 := bstep (se 3 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 2390525 = 896447) B896447
theorem B1593683 : Blo 880569 1593683 := bstep (se 1 (by rfl) ⟨1195262, by rfl⟩ : syracuseStep 1593683 = 2390525) B2390525
theorem B1062455 : Blo 880569 1062455 := bstep (se 1 (by rfl) ⟨796841, by rfl⟩ : syracuseStep 1062455 = 1593683) B1593683
theorem B2833213 : Blo 880569 2833213 := bstep (se 3 (by rfl) ⟨531227, by rfl⟩ : syracuseStep 2833213 = 1062455) B1062455
theorem B3777617 : Blo 880569 3777617 := bstep (se 2 (by rfl) ⟨1416606, by rfl⟩ : syracuseStep 3777617 = 2833213) B2833213
theorem B2518411 : Blo 880569 2518411 := bstep (se 1 (by rfl) ⟨1888808, by rfl⟩ : syracuseStep 2518411 = 3777617) B3777617
theorem B3357881 : Blo 880569 3357881 := bstep (se 2 (by rfl) ⟨1259205, by rfl⟩ : syracuseStep 3357881 = 2518411) B2518411
theorem B2238587 : Blo 880569 2238587 := bstep (se 1 (by rfl) ⟨1678940, by rfl⟩ : syracuseStep 2238587 = 3357881) B3357881
theorem B1492391 : Blo 880569 1492391 := bstep (se 1 (by rfl) ⟨1119293, by rfl⟩ : syracuseStep 1492391 = 2238587) B2238587
theorem B994927 : Blo 880569 994927 := bstep (se 1 (by rfl) ⟨746195, by rfl⟩ : syracuseStep 994927 = 1492391) B1492391
theorem B1326569 : Blo 880569 1326569 := bstep (se 2 (by rfl) ⟨497463, by rfl⟩ : syracuseStep 1326569 = 994927) B994927
theorem B884379 : Blo 880569 884379 := bstep (se 1 (by rfl) ⟨663284, by rfl⟩ : syracuseStep 884379 = 1326569) B1326569

theorem C0 (j : ℕ) (h1 : 220142 ≤ j) (h2 : j ≤ 220841) : Blo 880569 (4 * j + 3) := by
  interval_cases j
  · exact B880571
  · exact B880575
  · exact B880579
  · exact B880583
  · exact B880587
  · exact B880591
  · exact B880595
  · exact B880599
  · exact B880603
  · exact B880607
  · exact B880611
  · exact B880615
  · exact B880619
  · exact B880623
  · exact B880627
  · exact B880631
  · exact B880635
  · exact B880639
  · exact B880643
  · exact B880647
  · exact B880651
  · exact B880655
  · exact B880659
  · exact B880663
  · exact B880667
  · exact B880671
  · exact B880675
  · exact B880679
  · exact B880683
  · exact B880687
  · exact B880691
  · exact B880695
  · exact B880699
  · exact B880703
  · exact B880707
  · exact B880711
  · exact B880715
  · exact B880719
  · exact B880723
  · exact B880727
  · exact B880731
  · exact B880735
  · exact B880739
  · exact B880743
  · exact B880747
  · exact B880751
  · exact B880755
  · exact B880759
  · exact B880763
  · exact B880767
  · exact B880771
  · exact B880775
  · exact B880779
  · exact B880783
  · exact B880787
  · exact B880791
  · exact B880795
  · exact B880799
  · exact B880803
  · exact B880807
  · exact B880811
  · exact B880815
  · exact B880819
  · exact B880823
  · exact B880827
  · exact B880831
  · exact B880835
  · exact B880839
  · exact B880843
  · exact B880847
  · exact B880851
  · exact B880855
  · exact B880859
  · exact B880863
  · exact B880867
  · exact B880871
  · exact B880875
  · exact B880879
  · exact B880883
  · exact B880887
  · exact B880891
  · exact B880895
  · exact B880899
  · exact B880903
  · exact B880907
  · exact B880911
  · exact B880915
  · exact B880919
  · exact B880923
  · exact B880927
  · exact B880931
  · exact B880935
  · exact B880939
  · exact B880943
  · exact B880947
  · exact B880951
  · exact B880955
  · exact B880959
  · exact B880963
  · exact B880967
  · exact B880971
  · exact B880975
  · exact B880979
  · exact B880983
  · exact B880987
  · exact B880991
  · exact B880995
  · exact B880999
  · exact B881003
  · exact B881007
  · exact B881011
  · exact B881015
  · exact B881019
  · exact B881023
  · exact B881027
  · exact B881031
  · exact B881035
  · exact B881039
  · exact B881043
  · exact B881047
  · exact B881051
  · exact B881055
  · exact B881059
  · exact B881063
  · exact B881067
  · exact B881071
  · exact B881075
  · exact B881079
  · exact B881083
  · exact B881087
  · exact B881091
  · exact B881095
  · exact B881099
  · exact B881103
  · exact B881107
  · exact B881111
  · exact B881115
  · exact B881119
  · exact B881123
  · exact B881127
  · exact B881131
  · exact B881135
  · exact B881139
  · exact B881143
  · exact B881147
  · exact B881151
  · exact B881155
  · exact B881159
  · exact B881163
  · exact B881167
  · exact B881171
  · exact B881175
  · exact B881179
  · exact B881183
  · exact B881187
  · exact B881191
  · exact B881195
  · exact B881199
  · exact B881203
  · exact B881207
  · exact B881211
  · exact B881215
  · exact B881219
  · exact B881223
  · exact B881227
  · exact B881231
  · exact B881235
  · exact B881239
  · exact B881243
  · exact B881247
  · exact B881251
  · exact B881255
  · exact B881259
  · exact B881263
  · exact B881267
  · exact B881271
  · exact B881275
  · exact B881279
  · exact B881283
  · exact B881287
  · exact B881291
  · exact B881295
  · exact B881299
  · exact B881303
  · exact B881307
  · exact B881311
  · exact B881315
  · exact B881319
  · exact B881323
  · exact B881327
  · exact B881331
  · exact B881335
  · exact B881339
  · exact B881343
  · exact B881347
  · exact B881351
  · exact B881355
  · exact B881359
  · exact B881363
  · exact B881367
  · exact B881371
  · exact B881375
  · exact B881379
  · exact B881383
  · exact B881387
  · exact B881391
  · exact B881395
  · exact B881399
  · exact B881403
  · exact B881407
  · exact B881411
  · exact B881415
  · exact B881419
  · exact B881423
  · exact B881427
  · exact B881431
  · exact B881435
  · exact B881439
  · exact B881443
  · exact B881447
  · exact B881451
  · exact B881455
  · exact B881459
  · exact B881463
  · exact B881467
  · exact B881471
  · exact B881475
  · exact B881479
  · exact B881483
  · exact B881487
  · exact B881491
  · exact B881495
  · exact B881499
  · exact B881503
  · exact B881507
  · exact B881511
  · exact B881515
  · exact B881519
  · exact B881523
  · exact B881527
  · exact B881531
  · exact B881535
  · exact B881539
  · exact B881543
  · exact B881547
  · exact B881551
  · exact B881555
  · exact B881559
  · exact B881563
  · exact B881567
  · exact B881571
  · exact B881575
  · exact B881579
  · exact B881583
  · exact B881587
  · exact B881591
  · exact B881595
  · exact B881599
  · exact B881603
  · exact B881607
  · exact B881611
  · exact B881615
  · exact B881619
  · exact B881623
  · exact B881627
  · exact B881631
  · exact B881635
  · exact B881639
  · exact B881643
  · exact B881647
  · exact B881651
  · exact B881655
  · exact B881659
  · exact B881663
  · exact B881667
  · exact B881671
  · exact B881675
  · exact B881679
  · exact B881683
  · exact B881687
  · exact B881691
  · exact B881695
  · exact B881699
  · exact B881703
  · exact B881707
  · exact B881711
  · exact B881715
  · exact B881719
  · exact B881723
  · exact B881727
  · exact B881731
  · exact B881735
  · exact B881739
  · exact B881743
  · exact B881747
  · exact B881751
  · exact B881755
  · exact B881759
  · exact B881763
  · exact B881767
  · exact B881771
  · exact B881775
  · exact B881779
  · exact B881783
  · exact B881787
  · exact B881791
  · exact B881795
  · exact B881799
  · exact B881803
  · exact B881807
  · exact B881811
  · exact B881815
  · exact B881819
  · exact B881823
  · exact B881827
  · exact B881831
  · exact B881835
  · exact B881839
  · exact B881843
  · exact B881847
  · exact B881851
  · exact B881855
  · exact B881859
  · exact B881863
  · exact B881867
  · exact B881871
  · exact B881875
  · exact B881879
  · exact B881883
  · exact B881887
  · exact B881891
  · exact B881895
  · exact B881899
  · exact B881903
  · exact B881907
  · exact B881911
  · exact B881915
  · exact B881919
  · exact B881923
  · exact B881927
  · exact B881931
  · exact B881935
  · exact B881939
  · exact B881943
  · exact B881947
  · exact B881951
  · exact B881955
  · exact B881959
  · exact B881963
  · exact B881967
  · exact B881971
  · exact B881975
  · exact B881979
  · exact B881983
  · exact B881987
  · exact B881991
  · exact B881995
  · exact B881999
  · exact B882003
  · exact B882007
  · exact B882011
  · exact B882015
  · exact B882019
  · exact B882023
  · exact B882027
  · exact B882031
  · exact B882035
  · exact B882039
  · exact B882043
  · exact B882047
  · exact B882051
  · exact B882055
  · exact B882059
  · exact B882063
  · exact B882067
  · exact B882071
  · exact B882075
  · exact B882079
  · exact B882083
  · exact B882087
  · exact B882091
  · exact B882095
  · exact B882099
  · exact B882103
  · exact B882107
  · exact B882111
  · exact B882115
  · exact B882119
  · exact B882123
  · exact B882127
  · exact B882131
  · exact B882135
  · exact B882139
  · exact B882143
  · exact B882147
  · exact B882151
  · exact B882155
  · exact B882159
  · exact B882163
  · exact B882167
  · exact B882171
  · exact B882175
  · exact B882179
  · exact B882183
  · exact B882187
  · exact B882191
  · exact B882195
  · exact B882199
  · exact B882203
  · exact B882207
  · exact B882211
  · exact B882215
  · exact B882219
  · exact B882223
  · exact B882227
  · exact B882231
  · exact B882235
  · exact B882239
  · exact B882243
  · exact B882247
  · exact B882251
  · exact B882255
  · exact B882259
  · exact B882263
  · exact B882267
  · exact B882271
  · exact B882275
  · exact B882279
  · exact B882283
  · exact B882287
  · exact B882291
  · exact B882295
  · exact B882299
  · exact B882303
  · exact B882307
  · exact B882311
  · exact B882315
  · exact B882319
  · exact B882323
  · exact B882327
  · exact B882331
  · exact B882335
  · exact B882339
  · exact B882343
  · exact B882347
  · exact B882351
  · exact B882355
  · exact B882359
  · exact B882363
  · exact B882367
  · exact B882371
  · exact B882375
  · exact B882379
  · exact B882383
  · exact B882387
  · exact B882391
  · exact B882395
  · exact B882399
  · exact B882403
  · exact B882407
  · exact B882411
  · exact B882415
  · exact B882419
  · exact B882423
  · exact B882427
  · exact B882431
  · exact B882435
  · exact B882439
  · exact B882443
  · exact B882447
  · exact B882451
  · exact B882455
  · exact B882459
  · exact B882463
  · exact B882467
  · exact B882471
  · exact B882475
  · exact B882479
  · exact B882483
  · exact B882487
  · exact B882491
  · exact B882495
  · exact B882499
  · exact B882503
  · exact B882507
  · exact B882511
  · exact B882515
  · exact B882519
  · exact B882523
  · exact B882527
  · exact B882531
  · exact B882535
  · exact B882539
  · exact B882543
  · exact B882547
  · exact B882551
  · exact B882555
  · exact B882559
  · exact B882563
  · exact B882567
  · exact B882571
  · exact B882575
  · exact B882579
  · exact B882583
  · exact B882587
  · exact B882591
  · exact B882595
  · exact B882599
  · exact B882603
  · exact B882607
  · exact B882611
  · exact B882615
  · exact B882619
  · exact B882623
  · exact B882627
  · exact B882631
  · exact B882635
  · exact B882639
  · exact B882643
  · exact B882647
  · exact B882651
  · exact B882655
  · exact B882659
  · exact B882663
  · exact B882667
  · exact B882671
  · exact B882675
  · exact B882679
  · exact B882683
  · exact B882687
  · exact B882691
  · exact B882695
  · exact B882699
  · exact B882703
  · exact B882707
  · exact B882711
  · exact B882715
  · exact B882719
  · exact B882723
  · exact B882727
  · exact B882731
  · exact B882735
  · exact B882739
  · exact B882743
  · exact B882747
  · exact B882751
  · exact B882755
  · exact B882759
  · exact B882763
  · exact B882767
  · exact B882771
  · exact B882775
  · exact B882779
  · exact B882783
  · exact B882787
  · exact B882791
  · exact B882795
  · exact B882799
  · exact B882803
  · exact B882807
  · exact B882811
  · exact B882815
  · exact B882819
  · exact B882823
  · exact B882827
  · exact B882831
  · exact B882835
  · exact B882839
  · exact B882843
  · exact B882847
  · exact B882851
  · exact B882855
  · exact B882859
  · exact B882863
  · exact B882867
  · exact B882871
  · exact B882875
  · exact B882879
  · exact B882883
  · exact B882887
  · exact B882891
  · exact B882895
  · exact B882899
  · exact B882903
  · exact B882907
  · exact B882911
  · exact B882915
  · exact B882919
  · exact B882923
  · exact B882927
  · exact B882931
  · exact B882935
  · exact B882939
  · exact B882943
  · exact B882947
  · exact B882951
  · exact B882955
  · exact B882959
  · exact B882963
  · exact B882967
  · exact B882971
  · exact B882975
  · exact B882979
  · exact B882983
  · exact B882987
  · exact B882991
  · exact B882995
  · exact B882999
  · exact B883003
  · exact B883007
  · exact B883011
  · exact B883015
  · exact B883019
  · exact B883023
  · exact B883027
  · exact B883031
  · exact B883035
  · exact B883039
  · exact B883043
  · exact B883047
  · exact B883051
  · exact B883055
  · exact B883059
  · exact B883063
  · exact B883067
  · exact B883071
  · exact B883075
  · exact B883079
  · exact B883083
  · exact B883087
  · exact B883091
  · exact B883095
  · exact B883099
  · exact B883103
  · exact B883107
  · exact B883111
  · exact B883115
  · exact B883119
  · exact B883123
  · exact B883127
  · exact B883131
  · exact B883135
  · exact B883139
  · exact B883143
  · exact B883147
  · exact B883151
  · exact B883155
  · exact B883159
  · exact B883163
  · exact B883167
  · exact B883171
  · exact B883175
  · exact B883179
  · exact B883183
  · exact B883187
  · exact B883191
  · exact B883195
  · exact B883199
  · exact B883203
  · exact B883207
  · exact B883211
  · exact B883215
  · exact B883219
  · exact B883223
  · exact B883227
  · exact B883231
  · exact B883235
  · exact B883239
  · exact B883243
  · exact B883247
  · exact B883251
  · exact B883255
  · exact B883259
  · exact B883263
  · exact B883267
  · exact B883271
  · exact B883275
  · exact B883279
  · exact B883283
  · exact B883287
  · exact B883291
  · exact B883295
  · exact B883299
  · exact B883303
  · exact B883307
  · exact B883311
  · exact B883315
  · exact B883319
  · exact B883323
  · exact B883327
  · exact B883331
  · exact B883335
  · exact B883339
  · exact B883343
  · exact B883347
  · exact B883351
  · exact B883355
  · exact B883359
  · exact B883363
  · exact B883367

theorem C1 (j : ℕ) (h1 : 220842 ≤ j) (h2 : j ≤ 221141) : Blo 880569 (4 * j + 3) := by
  interval_cases j
  · exact B883371
  · exact B883375
  · exact B883379
  · exact B883383
  · exact B883387
  · exact B883391
  · exact B883395
  · exact B883399
  · exact B883403
  · exact B883407
  · exact B883411
  · exact B883415
  · exact B883419
  · exact B883423
  · exact B883427
  · exact B883431
  · exact B883435
  · exact B883439
  · exact B883443
  · exact B883447
  · exact B883451
  · exact B883455
  · exact B883459
  · exact B883463
  · exact B883467
  · exact B883471
  · exact B883475
  · exact B883479
  · exact B883483
  · exact B883487
  · exact B883491
  · exact B883495
  · exact B883499
  · exact B883503
  · exact B883507
  · exact B883511
  · exact B883515
  · exact B883519
  · exact B883523
  · exact B883527
  · exact B883531
  · exact B883535
  · exact B883539
  · exact B883543
  · exact B883547
  · exact B883551
  · exact B883555
  · exact B883559
  · exact B883563
  · exact B883567
  · exact B883571
  · exact B883575
  · exact B883579
  · exact B883583
  · exact B883587
  · exact B883591
  · exact B883595
  · exact B883599
  · exact B883603
  · exact B883607
  · exact B883611
  · exact B883615
  · exact B883619
  · exact B883623
  · exact B883627
  · exact B883631
  · exact B883635
  · exact B883639
  · exact B883643
  · exact B883647
  · exact B883651
  · exact B883655
  · exact B883659
  · exact B883663
  · exact B883667
  · exact B883671
  · exact B883675
  · exact B883679
  · exact B883683
  · exact B883687
  · exact B883691
  · exact B883695
  · exact B883699
  · exact B883703
  · exact B883707
  · exact B883711
  · exact B883715
  · exact B883719
  · exact B883723
  · exact B883727
  · exact B883731
  · exact B883735
  · exact B883739
  · exact B883743
  · exact B883747
  · exact B883751
  · exact B883755
  · exact B883759
  · exact B883763
  · exact B883767
  · exact B883771
  · exact B883775
  · exact B883779
  · exact B883783
  · exact B883787
  · exact B883791
  · exact B883795
  · exact B883799
  · exact B883803
  · exact B883807
  · exact B883811
  · exact B883815
  · exact B883819
  · exact B883823
  · exact B883827
  · exact B883831
  · exact B883835
  · exact B883839
  · exact B883843
  · exact B883847
  · exact B883851
  · exact B883855
  · exact B883859
  · exact B883863
  · exact B883867
  · exact B883871
  · exact B883875
  · exact B883879
  · exact B883883
  · exact B883887
  · exact B883891
  · exact B883895
  · exact B883899
  · exact B883903
  · exact B883907
  · exact B883911
  · exact B883915
  · exact B883919
  · exact B883923
  · exact B883927
  · exact B883931
  · exact B883935
  · exact B883939
  · exact B883943
  · exact B883947
  · exact B883951
  · exact B883955
  · exact B883959
  · exact B883963
  · exact B883967
  · exact B883971
  · exact B883975
  · exact B883979
  · exact B883983
  · exact B883987
  · exact B883991
  · exact B883995
  · exact B883999
  · exact B884003
  · exact B884007
  · exact B884011
  · exact B884015
  · exact B884019
  · exact B884023
  · exact B884027
  · exact B884031
  · exact B884035
  · exact B884039
  · exact B884043
  · exact B884047
  · exact B884051
  · exact B884055
  · exact B884059
  · exact B884063
  · exact B884067
  · exact B884071
  · exact B884075
  · exact B884079
  · exact B884083
  · exact B884087
  · exact B884091
  · exact B884095
  · exact B884099
  · exact B884103
  · exact B884107
  · exact B884111
  · exact B884115
  · exact B884119
  · exact B884123
  · exact B884127
  · exact B884131
  · exact B884135
  · exact B884139
  · exact B884143
  · exact B884147
  · exact B884151
  · exact B884155
  · exact B884159
  · exact B884163
  · exact B884167
  · exact B884171
  · exact B884175
  · exact B884179
  · exact B884183
  · exact B884187
  · exact B884191
  · exact B884195
  · exact B884199
  · exact B884203
  · exact B884207
  · exact B884211
  · exact B884215
  · exact B884219
  · exact B884223
  · exact B884227
  · exact B884231
  · exact B884235
  · exact B884239
  · exact B884243
  · exact B884247
  · exact B884251
  · exact B884255
  · exact B884259
  · exact B884263
  · exact B884267
  · exact B884271
  · exact B884275
  · exact B884279
  · exact B884283
  · exact B884287
  · exact B884291
  · exact B884295
  · exact B884299
  · exact B884303
  · exact B884307
  · exact B884311
  · exact B884315
  · exact B884319
  · exact B884323
  · exact B884327
  · exact B884331
  · exact B884335
  · exact B884339
  · exact B884343
  · exact B884347
  · exact B884351
  · exact B884355
  · exact B884359
  · exact B884363
  · exact B884367
  · exact B884371
  · exact B884375
  · exact B884379
  · exact B884383
  · exact B884387
  · exact B884391
  · exact B884395
  · exact B884399
  · exact B884403
  · exact B884407
  · exact B884411
  · exact B884415
  · exact B884419
  · exact B884423
  · exact B884427
  · exact B884431
  · exact B884435
  · exact B884439
  · exact B884443
  · exact B884447
  · exact B884451
  · exact B884455
  · exact B884459
  · exact B884463
  · exact B884467
  · exact B884471
  · exact B884475
  · exact B884479
  · exact B884483
  · exact B884487
  · exact B884491
  · exact B884495
  · exact B884499
  · exact B884503
  · exact B884507
  · exact B884511
  · exact B884515
  · exact B884519
  · exact B884523
  · exact B884527
  · exact B884531
  · exact B884535
  · exact B884539
  · exact B884543
  · exact B884547
  · exact B884551
  · exact B884555
  · exact B884559
  · exact B884563
  · exact B884567

theorem solution (m : ℕ) (hlo : 880569 ≤ m) (hhi : m ≤ 884569) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 220142 ≤ j := by omega
    have hj2 : j ≤ 221141 := by omega
    have hb : Blo 880569 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 220842 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
