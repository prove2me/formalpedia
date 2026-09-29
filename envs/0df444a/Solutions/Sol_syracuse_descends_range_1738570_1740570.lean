-- Prove2me | solution 1 for syracuse_descends_range_1738570_1740570
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:33:42.476427+00:00
-- url     : https://prove2.me/submissions/9e5e0df7-b2cf-483b-9268-e86fd288ed38

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


theorem B1957909 : Blo 1738570 1957909 := bbase (se 6 (by rfl) ⟨45888, by rfl⟩ : syracuseStep 1957909 = 91777) (by norm_num)
theorem B1957945 : Blo 1738570 1957945 := bbase (se 2 (by rfl) ⟨734229, by rfl⟩ : syracuseStep 1957945 = 1468459) (by norm_num)
theorem B3915845 : Blo 1738570 3915845 := bbase (se 4 (by rfl) ⟨367110, by rfl⟩ : syracuseStep 3915845 = 734221) (by norm_num)
theorem B1957981 : Blo 1738570 1957981 := bbase (se 3 (by rfl) ⟨367121, by rfl⟩ : syracuseStep 1957981 = 734243) (by norm_num)
theorem B1958017 : Blo 1738570 1958017 := bbase (se 2 (by rfl) ⟨734256, by rfl⟩ : syracuseStep 1958017 = 1468513) (by norm_num)
theorem B8355973 : Blo 1738570 8355973 := bbase (se 4 (by rfl) ⟨783372, by rfl⟩ : syracuseStep 8355973 = 1566745) (by norm_num)
theorem B3915917 : Blo 1738570 3915917 := bbase (se 3 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 3915917 = 1468469) (by norm_num)
theorem B2089109 : Blo 1738570 2089109 := bbase (se 6 (by rfl) ⟨48963, by rfl⟩ : syracuseStep 2089109 = 97927) (by norm_num)
theorem B6602917 : Blo 1738570 6602917 := bbase (se 4 (by rfl) ⟨619023, by rfl⟩ : syracuseStep 6602917 = 1238047) (by norm_num)
theorem B1958053 : Blo 1738570 1958053 := bbase (se 4 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 1958053 = 367135) (by norm_num)
theorem B3301573 : Blo 1738570 3301573 := bbase (se 4 (by rfl) ⟨309522, by rfl⟩ : syracuseStep 3301573 = 619045) (by norm_num)
theorem B1958089 : Blo 1738570 1958089 := bbase (se 2 (by rfl) ⟨734283, by rfl⟩ : syracuseStep 1958089 = 1468567) (by norm_num)
theorem B3915989 : Blo 1738570 3915989 := bbase (se 7 (by rfl) ⟨45890, by rfl⟩ : syracuseStep 3915989 = 91781) (by norm_num)
theorem B2973917 : Blo 1738570 2973917 := bbase (se 3 (by rfl) ⟨557609, by rfl⟩ : syracuseStep 2973917 = 1115219) (by norm_num)
theorem B2785517 : Blo 1738570 2785517 := bbase (se 3 (by rfl) ⟨522284, by rfl⟩ : syracuseStep 2785517 = 1044569) (by norm_num)
theorem B1958125 : Blo 1738570 1958125 := bbase (se 3 (by rfl) ⟨367148, by rfl⟩ : syracuseStep 1958125 = 734297) (by norm_num)
theorem B14106869 : Blo 1738570 14106869 := bbase (se 5 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 14106869 = 1322519) (by norm_num)
theorem B3916061 : Blo 1738570 3916061 := bbase (se 3 (by rfl) ⟨734261, by rfl⟩ : syracuseStep 3916061 = 1468523) (by norm_num)
theorem B5873957 : Blo 1738570 5873957 := bbase (se 4 (by rfl) ⟨550683, by rfl⟩ : syracuseStep 5873957 = 1101367) (by norm_num)
theorem B2974013 : Blo 1738570 2974013 := bbase (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) (by norm_num)
theorem B3301717 : Blo 1738570 3301717 := bbase (se 10 (by rfl) ⟨4836, by rfl⟩ : syracuseStep 3301717 = 9673) (by norm_num)
theorem B3916133 : Blo 1738570 3916133 := bbase (se 4 (by rfl) ⟨367137, by rfl⟩ : syracuseStep 3916133 = 734275) (by norm_num)
theorem B2646413 : Blo 1738570 2646413 := bbase (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) (by norm_num)
theorem B8806805 : Blo 1738570 8806805 := bbase (se 6 (by rfl) ⟨206409, by rfl⟩ : syracuseStep 8806805 = 412819) (by norm_num)
theorem B3916205 : Blo 1738570 3916205 := bbase (se 3 (by rfl) ⟨734288, by rfl⟩ : syracuseStep 3916205 = 1468577) (by norm_num)
theorem B14107061 : Blo 1738570 14107061 := bbase (se 5 (by rfl) ⟨661268, by rfl⟩ : syracuseStep 14107061 = 1322537) (by norm_num)
theorem B2089417 : Blo 1738570 2089417 := bbase (se 2 (by rfl) ⟨783531, by rfl⟩ : syracuseStep 2089417 = 1567063) (by norm_num)
theorem B6603221 : Blo 1738570 6603221 := bbase (se 7 (by rfl) ⟨77381, by rfl⟩ : syracuseStep 6603221 = 154763) (by norm_num)
theorem B3301877 : Blo 1738570 3301877 := bbase (se 5 (by rfl) ⟨154775, by rfl⟩ : syracuseStep 3301877 = 309551) (by norm_num)
theorem B3916277 : Blo 1738570 3916277 := bbase (se 5 (by rfl) ⟨183575, by rfl⟩ : syracuseStep 3916277 = 367151) (by norm_num)
theorem B5571109 : Blo 1738570 5571109 := bbase (se 4 (by rfl) ⟨522291, by rfl⟩ : syracuseStep 5571109 = 1044583) (by norm_num)
theorem B2089585 : Blo 1738570 2089585 := bbase (se 2 (by rfl) ⟨783594, by rfl⟩ : syracuseStep 2089585 = 1567189) (by norm_num)
theorem B9044597 : Blo 1738570 9044597 := bbase (se 5 (by rfl) ⟨423965, by rfl⟩ : syracuseStep 9044597 = 847931) (by norm_num)
theorem B3302021 : Blo 1738570 3302021 := bbase (se 4 (by rfl) ⟨309564, by rfl⟩ : syracuseStep 3302021 = 619129) (by norm_num)
theorem B6357685 : Blo 1738570 6357685 := bbase (se 5 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 6357685 = 596033) (by norm_num)
theorem B5874389 : Blo 1738570 5874389 := bbase (se 7 (by rfl) ⟨68840, by rfl⟩ : syracuseStep 5874389 = 137681) (by norm_num)
theorem B4178717 : Blo 1738570 4178717 := bbase (se 3 (by rfl) ⟨783509, by rfl⟩ : syracuseStep 4178717 = 1567019) (by norm_num)
theorem B2089781 : Blo 1738570 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B7054165 : Blo 1738570 7054165 := bbase (se 9 (by rfl) ⟨20666, by rfl⟩ : syracuseStep 7054165 = 41333) (by norm_num)
theorem B16089941 : Blo 1738570 16089941 := bbase (se 9 (by rfl) ⟨47138, by rfl⟩ : syracuseStep 16089941 = 94277) (by norm_num)
theorem B7054181 : Blo 1738570 7054181 := bbase (se 4 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 7054181 = 1322659) (by norm_num)
theorem B3965861 : Blo 1738570 3965861 := bbase (se 4 (by rfl) ⟨371799, by rfl⟩ : syracuseStep 3965861 = 743599) (by norm_num)
theorem B3302309 : Blo 1738570 3302309 := bbase (se 4 (by rfl) ⟨309591, by rfl⟩ : syracuseStep 3302309 = 619183) (by norm_num)
theorem B2786221 : Blo 1738570 2786221 := bbase (se 3 (by rfl) ⟨522416, by rfl⟩ : syracuseStep 2786221 = 1044833) (by norm_num)
theorem B4178909 : Blo 1738570 4178909 := bbase (se 3 (by rfl) ⟨783545, by rfl⟩ : syracuseStep 4178909 = 1567091) (by norm_num)
theorem B7939093 : Blo 1738570 7939093 := bbase (se 6 (by rfl) ⟨186072, by rfl⟩ : syracuseStep 7939093 = 372145) (by norm_num)
theorem B1762345 : Blo 1738570 1762345 := bbase (se 2 (by rfl) ⟨660879, by rfl⟩ : syracuseStep 1762345 = 1321759) (by norm_num)
theorem B11142197 : Blo 1738570 11142197 := bbase (se 5 (by rfl) ⟨522290, by rfl⟩ : syracuseStep 11142197 = 1044581) (by norm_num)
theorem B3302461 : Blo 1738570 3302461 := bbase (se 3 (by rfl) ⟨619211, by rfl⟩ : syracuseStep 3302461 = 1238423) (by norm_num)
theorem B7939205 : Blo 1738570 7939205 := bbase (se 4 (by rfl) ⟨744300, by rfl⟩ : syracuseStep 7939205 = 1488601) (by norm_num)
theorem B2933941 : Blo 1738570 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1983733 : Blo 1738570 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B2934029 : Blo 1738570 2934029 := bbase (se 3 (by rfl) ⟨550130, by rfl⟩ : syracuseStep 2934029 = 1100261) (by norm_num)
theorem B2786645 : Blo 1738570 2786645 := bbase (se 12 (by rfl) ⟨1020, by rfl⟩ : syracuseStep 2786645 = 2041) (by norm_num)
theorem B3302765 : Blo 1738570 3302765 := bbase (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) (by norm_num)
theorem B2934157 : Blo 1738570 2934157 := bbase (se 3 (by rfl) ⟨550154, by rfl⟩ : syracuseStep 2934157 = 1100309) (by norm_num)
theorem B14853557 : Blo 1738570 14853557 := bbase (se 5 (by rfl) ⟨696260, by rfl⟩ : syracuseStep 14853557 = 1392521) (by norm_num)
theorem B2934245 : Blo 1738570 2934245 := bbase (se 4 (by rfl) ⟨275085, by rfl⟩ : syracuseStep 2934245 = 550171) (by norm_num)
theorem B2262605 : Blo 1738570 2262605 := bbase (se 3 (by rfl) ⟨424238, by rfl⟩ : syracuseStep 2262605 = 848477) (by norm_num)
theorem B2934373 : Blo 1738570 2934373 := bbase (se 4 (by rfl) ⟨275097, by rfl⟩ : syracuseStep 2934373 = 550195) (by norm_num)
theorem B2786933 : Blo 1738570 2786933 := bbase (se 5 (by rfl) ⟨130637, by rfl⟩ : syracuseStep 2786933 = 261275) (by norm_num)
theorem B9905813 : Blo 1738570 9905813 := bbase (se 6 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 9905813 = 464335) (by norm_num)
theorem B2975381 : Blo 1738570 2975381 := bbase (se 6 (by rfl) ⟨69735, by rfl⟩ : syracuseStep 2975381 = 139471) (by norm_num)
theorem B8808101 : Blo 1738570 8808101 := bbase (se 4 (by rfl) ⟨825759, by rfl⟩ : syracuseStep 8808101 = 1651519) (by norm_num)
theorem B2934461 : Blo 1738570 2934461 := bbase (se 3 (by rfl) ⟨550211, by rfl⟩ : syracuseStep 2934461 = 1100423) (by norm_num)
theorem B24463061 : Blo 1738570 24463061 := bbase (se 7 (by rfl) ⟨286676, by rfl⟩ : syracuseStep 24463061 = 573353) (by norm_num)
theorem B4703957 : Blo 1738570 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B5949173 : Blo 1738570 5949173 := bbase (se 5 (by rfl) ⟨278867, by rfl⟩ : syracuseStep 5949173 = 557735) (by norm_num)
theorem B2934589 : Blo 1738570 2934589 := bbase (se 3 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 2934589 = 1100471) (by norm_num)
theorem B2787157 : Blo 1738570 2787157 := bbase (se 9 (by rfl) ⟨8165, by rfl⟩ : syracuseStep 2787157 = 16331) (by norm_num)
theorem B4401013 : Blo 1738570 4401013 := bbase (se 5 (by rfl) ⟨206297, by rfl⟩ : syracuseStep 4401013 = 412595) (by norm_num)
theorem B5572469 : Blo 1738570 5572469 := bbase (se 5 (by rfl) ⟨261209, by rfl⟩ : syracuseStep 5572469 = 522419) (by norm_num)
theorem B2934677 : Blo 1738570 2934677 := bbase (se 6 (by rfl) ⟨68781, by rfl⟩ : syracuseStep 2934677 = 137563) (by norm_num)
theorem B4401125 : Blo 1738570 4401125 := bbase (se 4 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 4401125 = 825211) (by norm_num)
theorem B5572597 : Blo 1738570 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B2934805 : Blo 1738570 2934805 := bbase (se 6 (by rfl) ⟨68784, by rfl⟩ : syracuseStep 2934805 = 137569) (by norm_num)
theorem B17860661 : Blo 1738570 17860661 := bbase (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) (by norm_num)
theorem B13215797 : Blo 1738570 13215797 := bbase (se 5 (by rfl) ⟨619490, by rfl⟩ : syracuseStep 13215797 = 1238981) (by norm_num)
theorem B2476117 : Blo 1738570 2476117 := bbase (se 8 (by rfl) ⟨14508, by rfl⟩ : syracuseStep 2476117 = 29017) (by norm_num)
theorem B11151445 : Blo 1738570 11151445 := bbase (se 8 (by rfl) ⟨65340, by rfl⟩ : syracuseStep 11151445 = 130681) (by norm_num)
theorem B3303517 : Blo 1738570 3303517 := bbase (se 3 (by rfl) ⟨619409, by rfl⟩ : syracuseStep 3303517 = 1238819) (by norm_num)
theorem B2934893 : Blo 1738570 2934893 := bbase (se 3 (by rfl) ⟨550292, by rfl⟩ : syracuseStep 2934893 = 1100585) (by norm_num)
theorem B3967093 : Blo 1738570 3967093 := bbase (se 5 (by rfl) ⟨185957, by rfl⟩ : syracuseStep 3967093 = 371915) (by norm_num)
theorem B4704389 : Blo 1738570 4704389 := bbase (se 4 (by rfl) ⟨441036, by rfl⟩ : syracuseStep 4704389 = 882073) (by norm_num)
theorem B4401317 : Blo 1738570 4401317 := bbase (se 4 (by rfl) ⟨412623, by rfl⟩ : syracuseStep 4401317 = 825247) (by norm_num)
theorem B3573965 : Blo 1738570 3573965 := bbase (se 3 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 3573965 = 1340237) (by norm_num)
theorem B2935021 : Blo 1738570 2935021 := bbase (se 3 (by rfl) ⟨550316, by rfl⟩ : syracuseStep 2935021 = 1100633) (by norm_num)
theorem B3303661 : Blo 1738570 3303661 := bbase (se 3 (by rfl) ⟨619436, by rfl⟩ : syracuseStep 3303661 = 1238873) (by norm_num)
theorem B5572853 : Blo 1738570 5572853 := bbase (se 5 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 5572853 = 522455) (by norm_num)
theorem B2935109 : Blo 1738570 2935109 := bbase (se 4 (by rfl) ⟨275166, by rfl⟩ : syracuseStep 2935109 = 550333) (by norm_num)
theorem B5867909 : Blo 1738570 5867909 := bbase (se 4 (by rfl) ⟨550116, by rfl⟩ : syracuseStep 5867909 = 1100233) (by norm_num)
theorem B3303821 : Blo 1738570 3303821 := bbase (se 3 (by rfl) ⟨619466, by rfl⟩ : syracuseStep 3303821 = 1238933) (by norm_num)
theorem B2935237 : Blo 1738570 2935237 := bbase (se 4 (by rfl) ⟨275178, by rfl⟩ : syracuseStep 2935237 = 550357) (by norm_num)
theorem B13208021 : Blo 1738570 13208021 := bbase (se 7 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 13208021 = 309563) (by norm_num)
theorem B4401661 : Blo 1738570 4401661 := bbase (se 3 (by rfl) ⟨825311, by rfl⟩ : syracuseStep 4401661 = 1650623) (by norm_num)
theorem B6605333 : Blo 1738570 6605333 := bbase (se 6 (by rfl) ⟨154812, by rfl⟩ : syracuseStep 6605333 = 309625) (by norm_num)
theorem B2935325 : Blo 1738570 2935325 := bbase (se 3 (by rfl) ⟨550373, by rfl⟩ : syracuseStep 2935325 = 1100747) (by norm_num)
theorem B3303965 : Blo 1738570 3303965 := bbase (se 3 (by rfl) ⟨619493, by rfl⟩ : syracuseStep 3303965 = 1238987) (by norm_num)
theorem B2230837 : Blo 1738570 2230837 := bbase (se 5 (by rfl) ⟨104570, by rfl⟩ : syracuseStep 2230837 = 209141) (by norm_num)
theorem B3713629 : Blo 1738570 3713629 := bbase (se 3 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 3713629 = 1392611) (by norm_num)
theorem B4401773 : Blo 1738570 4401773 := bbase (se 3 (by rfl) ⟨825332, by rfl⟩ : syracuseStep 4401773 = 1650665) (by norm_num)
theorem B7531157 : Blo 1738570 7531157 := bbase (se 6 (by rfl) ⟨176511, by rfl⟩ : syracuseStep 7531157 = 353023) (by norm_num)
theorem B2935453 : Blo 1738570 2935453 := bbase (se 3 (by rfl) ⟨550397, by rfl⟩ : syracuseStep 2935453 = 1100795) (by norm_num)
theorem B2935541 : Blo 1738570 2935541 := bbase (se 5 (by rfl) ⟨137603, by rfl⟩ : syracuseStep 2935541 = 275207) (by norm_num)
theorem B2607869 : Blo 1738570 2607869 := bbase (se 3 (by rfl) ⟨488975, by rfl⟩ : syracuseStep 2607869 = 977951) (by norm_num)
theorem B2607893 : Blo 1738570 2607893 := bbase (se 6 (by rfl) ⟨61122, by rfl⟩ : syracuseStep 2607893 = 122245) (by norm_num)
theorem B2607917 : Blo 1738570 2607917 := bbase (se 3 (by rfl) ⟨488984, by rfl⟩ : syracuseStep 2607917 = 977969) (by norm_num)
theorem B4401965 : Blo 1738570 4401965 := bbase (se 3 (by rfl) ⟨825368, by rfl⟩ : syracuseStep 4401965 = 1650737) (by norm_num)
theorem B5868341 : Blo 1738570 5868341 := bbase (se 5 (by rfl) ⟨275078, by rfl⟩ : syracuseStep 5868341 = 550157) (by norm_num)
theorem B6605621 : Blo 1738570 6605621 := bbase (se 5 (by rfl) ⟨309638, by rfl⟩ : syracuseStep 6605621 = 619277) (by norm_num)
theorem B3304253 : Blo 1738570 3304253 := bbase (se 3 (by rfl) ⟨619547, by rfl⟩ : syracuseStep 3304253 = 1239095) (by norm_num)
theorem B2607941 : Blo 1738570 2607941 := bbase (se 4 (by rfl) ⟨244494, by rfl⟩ : syracuseStep 2607941 = 488989) (by norm_num)
theorem B1764161 : Blo 1738570 1764161 := bbase (se 2 (by rfl) ⟨661560, by rfl⟩ : syracuseStep 1764161 = 1323121) (by norm_num)
theorem B2607965 : Blo 1738570 2607965 := bbase (se 3 (by rfl) ⟨488993, by rfl⟩ : syracuseStep 2607965 = 977987) (by norm_num)
theorem B2476909 : Blo 1738570 2476909 := bbase (se 3 (by rfl) ⟨464420, by rfl⟩ : syracuseStep 2476909 = 928841) (by norm_num)
theorem B2607989 : Blo 1738570 2607989 := bbase (se 5 (by rfl) ⟨122249, by rfl⟩ : syracuseStep 2607989 = 244499) (by norm_num)
theorem B2935669 : Blo 1738570 2935669 := bbase (se 5 (by rfl) ⟨137609, by rfl⟩ : syracuseStep 2935669 = 275219) (by norm_num)
theorem B2608013 : Blo 1738570 2608013 := bbase (se 3 (by rfl) ⟨489002, by rfl⟩ : syracuseStep 2608013 = 978005) (by norm_num)
theorem B2608037 : Blo 1738570 2608037 := bbase (se 4 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 2608037 = 489007) (by norm_num)
theorem B4180909 : Blo 1738570 4180909 := bbase (se 3 (by rfl) ⟨783920, by rfl⟩ : syracuseStep 4180909 = 1567841) (by norm_num)
theorem B8809397 : Blo 1738570 8809397 := bbase (se 5 (by rfl) ⟨412940, by rfl⟩ : syracuseStep 8809397 = 825881) (by norm_num)
theorem B2608061 : Blo 1738570 2608061 := bbase (se 3 (by rfl) ⟨489011, by rfl⟩ : syracuseStep 2608061 = 978023) (by norm_num)
theorem B2935757 : Blo 1738570 2935757 := bbase (se 3 (by rfl) ⟨550454, by rfl⟩ : syracuseStep 2935757 = 1100909) (by norm_num)
theorem B2608085 : Blo 1738570 2608085 := bbase (se 7 (by rfl) ⟨30563, by rfl⟩ : syracuseStep 2608085 = 61127) (by norm_num)
theorem B3714005 : Blo 1738570 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B2608109 : Blo 1738570 2608109 := bbase (se 3 (by rfl) ⟨489020, by rfl⟩ : syracuseStep 2608109 = 978041) (by norm_num)
theorem B2608133 : Blo 1738570 2608133 := bbase (se 4 (by rfl) ⟨244512, by rfl⟩ : syracuseStep 2608133 = 489025) (by norm_num)
theorem B2608157 : Blo 1738570 2608157 := bbase (se 3 (by rfl) ⟨489029, by rfl⟩ : syracuseStep 2608157 = 978059) (by norm_num)
theorem B2608181 : Blo 1738570 2608181 := bbase (se 5 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 2608181 = 244517) (by norm_num)
theorem B8924213 : Blo 1738570 8924213 := bbase (se 5 (by rfl) ⟨418322, by rfl⟩ : syracuseStep 8924213 = 836645) (by norm_num)
theorem B2608205 : Blo 1738570 2608205 := bbase (se 3 (by rfl) ⟨489038, by rfl⟩ : syracuseStep 2608205 = 978077) (by norm_num)
theorem B2935885 : Blo 1738570 2935885 := bbase (se 3 (by rfl) ⟨550478, by rfl⟩ : syracuseStep 2935885 = 1100957) (by norm_num)
theorem B2608229 : Blo 1738570 2608229 := bbase (se 4 (by rfl) ⟨244521, by rfl⟩ : syracuseStep 2608229 = 489043) (by norm_num)
theorem B2608253 : Blo 1738570 2608253 := bbase (se 3 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 2608253 = 978095) (by norm_num)
theorem B4402309 : Blo 1738570 4402309 := bbase (se 4 (by rfl) ⟨412716, by rfl⟩ : syracuseStep 4402309 = 825433) (by norm_num)
theorem B2608277 : Blo 1738570 2608277 := bbase (se 6 (by rfl) ⟨61131, by rfl⟩ : syracuseStep 2608277 = 122263) (by norm_num)
theorem B2935973 : Blo 1738570 2935973 := bbase (se 4 (by rfl) ⟨275247, by rfl⟩ : syracuseStep 2935973 = 550495) (by norm_num)
theorem B2608301 : Blo 1738570 2608301 := bbase (se 3 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 2608301 = 978113) (by norm_num)
theorem B2477245 : Blo 1738570 2477245 := bbase (se 3 (by rfl) ⟨464483, by rfl⟩ : syracuseStep 2477245 = 928967) (by norm_num)
theorem B2608325 : Blo 1738570 2608325 := bbase (se 4 (by rfl) ⟨244530, by rfl⟩ : syracuseStep 2608325 = 489061) (by norm_num)
theorem B8359109 : Blo 1738570 8359109 := bbase (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) (by norm_num)
theorem B2608349 : Blo 1738570 2608349 := bbase (se 3 (by rfl) ⟨489065, by rfl⟩ : syracuseStep 2608349 = 978131) (by norm_num)
theorem B5868773 : Blo 1738570 5868773 := bbase (se 4 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 5868773 = 1100395) (by norm_num)
theorem B2608373 : Blo 1738570 2608373 := bbase (se 5 (by rfl) ⟨122267, by rfl⟩ : syracuseStep 2608373 = 244535) (by norm_num)
theorem B4402421 : Blo 1738570 4402421 := bbase (se 5 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 4402421 = 412727) (by norm_num)
theorem B3968261 : Blo 1738570 3968261 := bbase (se 4 (by rfl) ⟨372024, by rfl⟩ : syracuseStep 3968261 = 744049) (by norm_num)
theorem B7433477 : Blo 1738570 7433477 := bbase (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) (by norm_num)
theorem B2608397 : Blo 1738570 2608397 := bbase (se 3 (by rfl) ⟨489074, by rfl⟩ : syracuseStep 2608397 = 978149) (by norm_num)
theorem B2608421 : Blo 1738570 2608421 := bbase (se 4 (by rfl) ⟨244539, by rfl⟩ : syracuseStep 2608421 = 489079) (by norm_num)
theorem B2936101 : Blo 1738570 2936101 := bbase (se 4 (by rfl) ⟨275259, by rfl⟩ : syracuseStep 2936101 = 550519) (by norm_num)
theorem B2608445 : Blo 1738570 2608445 := bbase (se 3 (by rfl) ⟨489083, by rfl⟩ : syracuseStep 2608445 = 978167) (by norm_num)
theorem B8801621 : Blo 1738570 8801621 := bbase (se 11 (by rfl) ⟨6446, by rfl⟩ : syracuseStep 8801621 = 12893) (by norm_num)
theorem B2608469 : Blo 1738570 2608469 := bbase (se 11 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 2608469 = 3821) (by norm_num)
theorem B2608493 : Blo 1738570 2608493 := bbase (se 3 (by rfl) ⟨489092, by rfl⟩ : syracuseStep 2608493 = 978185) (by norm_num)
theorem B2936189 : Blo 1738570 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B2608517 : Blo 1738570 2608517 := bbase (se 4 (by rfl) ⟨244548, by rfl⟩ : syracuseStep 2608517 = 489097) (by norm_num)
theorem B2477461 : Blo 1738570 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B2608541 : Blo 1738570 2608541 := bbase (se 3 (by rfl) ⟨489101, by rfl⟩ : syracuseStep 2608541 = 978203) (by norm_num)
theorem B2608565 : Blo 1738570 2608565 := bbase (se 5 (by rfl) ⟨122276, by rfl⟩ : syracuseStep 2608565 = 244553) (by norm_num)
theorem B4402613 : Blo 1738570 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B6032837 : Blo 1738570 6032837 := bbase (se 4 (by rfl) ⟨565578, by rfl⟩ : syracuseStep 6032837 = 1131157) (by norm_num)
theorem B2608589 : Blo 1738570 2608589 := bbase (se 3 (by rfl) ⟨489110, by rfl⟩ : syracuseStep 2608589 = 978221) (by norm_num)
theorem B2608613 : Blo 1738570 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B4181485 : Blo 1738570 4181485 := bbase (se 3 (by rfl) ⟨784028, by rfl⟩ : syracuseStep 4181485 = 1568057) (by norm_num)
theorem B2608637 : Blo 1738570 2608637 := bbase (se 3 (by rfl) ⟨489119, by rfl⟩ : syracuseStep 2608637 = 978239) (by norm_num)
theorem B2936317 : Blo 1738570 2936317 := bbase (se 3 (by rfl) ⟨550559, by rfl⟩ : syracuseStep 2936317 = 1101119) (by norm_num)
theorem B2608661 : Blo 1738570 2608661 := bbase (se 6 (by rfl) ⟨61140, by rfl⟩ : syracuseStep 2608661 = 122281) (by norm_num)
theorem B2608685 : Blo 1738570 2608685 := bbase (se 3 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 2608685 = 978257) (by norm_num)
theorem B2608709 : Blo 1738570 2608709 := bbase (se 4 (by rfl) ⟨244566, by rfl⟩ : syracuseStep 2608709 = 489133) (by norm_num)
theorem B2936405 : Blo 1738570 2936405 := bbase (se 8 (by rfl) ⟨17205, by rfl⟩ : syracuseStep 2936405 = 34411) (by norm_num)
theorem B2608733 : Blo 1738570 2608733 := bbase (se 3 (by rfl) ⟨489137, by rfl⟩ : syracuseStep 2608733 = 978275) (by norm_num)
theorem B2608757 : Blo 1738570 2608757 := bbase (se 5 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 2608757 = 244571) (by norm_num)
theorem B2608781 : Blo 1738570 2608781 := bbase (se 3 (by rfl) ⟨489146, by rfl⟩ : syracuseStep 2608781 = 978293) (by norm_num)
theorem B5869205 : Blo 1738570 5869205 := bbase (se 6 (by rfl) ⟨137559, by rfl⟩ : syracuseStep 5869205 = 275119) (by norm_num)
theorem B2608805 : Blo 1738570 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B2608829 : Blo 1738570 2608829 := bbase (se 3 (by rfl) ⟨489155, by rfl⟩ : syracuseStep 2608829 = 978311) (by norm_num)
theorem B23793365 : Blo 1738570 23793365 := bbase (se 7 (by rfl) ⟨278828, by rfl⟩ : syracuseStep 23793365 = 557657) (by norm_num)
theorem B2608853 : Blo 1738570 2608853 := bbase (se 7 (by rfl) ⟨30572, by rfl⟩ : syracuseStep 2608853 = 61145) (by norm_num)
theorem B3968725 : Blo 1738570 3968725 := bbase (se 7 (by rfl) ⟨46508, by rfl⟩ : syracuseStep 3968725 = 93017) (by norm_num)
theorem B2936533 : Blo 1738570 2936533 := bbase (se 7 (by rfl) ⟨34412, by rfl⟩ : syracuseStep 2936533 = 68825) (by norm_num)
theorem B2608877 : Blo 1738570 2608877 := bbase (se 3 (by rfl) ⟨489164, by rfl⟩ : syracuseStep 2608877 = 978329) (by norm_num)
theorem B4951813 : Blo 1738570 4951813 := bbase (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) (by norm_num)
theorem B2608901 : Blo 1738570 2608901 := bbase (se 4 (by rfl) ⟨244584, by rfl⟩ : syracuseStep 2608901 = 489169) (by norm_num)
theorem B4402957 : Blo 1738570 4402957 := bbase (se 3 (by rfl) ⟨825554, by rfl⟩ : syracuseStep 4402957 = 1651109) (by norm_num)
theorem B2477837 : Blo 1738570 2477837 := bbase (se 3 (by rfl) ⟨464594, by rfl⟩ : syracuseStep 2477837 = 929189) (by norm_num)
theorem B2608925 : Blo 1738570 2608925 := bbase (se 3 (by rfl) ⟨489173, by rfl⟩ : syracuseStep 2608925 = 978347) (by norm_num)
theorem B2936621 : Blo 1738570 2936621 := bbase (se 3 (by rfl) ⟨550616, by rfl⟩ : syracuseStep 2936621 = 1101233) (by norm_num)
theorem B2608949 : Blo 1738570 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B9908021 : Blo 1738570 9908021 := bbase (se 5 (by rfl) ⟨464438, by rfl⟩ : syracuseStep 9908021 = 928877) (by norm_num)
theorem B4181813 : Blo 1738570 4181813 := bbase (se 5 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 4181813 = 392045) (by norm_num)
theorem B2608973 : Blo 1738570 2608973 := bbase (se 3 (by rfl) ⟨489182, by rfl⟩ : syracuseStep 2608973 = 978365) (by norm_num)
theorem B2608997 : Blo 1738570 2608997 := bbase (se 4 (by rfl) ⟨244593, by rfl⟩ : syracuseStep 2608997 = 489187) (by norm_num)
theorem B2117485 : Blo 1738570 2117485 := bbase (se 3 (by rfl) ⟨397028, by rfl⟩ : syracuseStep 2117485 = 794057) (by norm_num)
theorem B4181869 : Blo 1738570 4181869 := bbase (se 3 (by rfl) ⟨784100, by rfl⟩ : syracuseStep 4181869 = 1568201) (by norm_num)
theorem B2609021 : Blo 1738570 2609021 := bbase (se 3 (by rfl) ⟨489191, by rfl⟩ : syracuseStep 2609021 = 978383) (by norm_num)
theorem B4403069 : Blo 1738570 4403069 := bbase (se 3 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 4403069 = 1651151) (by norm_num)
theorem B2609045 : Blo 1738570 2609045 := bbase (se 6 (by rfl) ⟨61149, by rfl⟩ : syracuseStep 2609045 = 122299) (by norm_num)
theorem B2609069 : Blo 1738570 2609069 := bbase (se 3 (by rfl) ⟨489200, by rfl⟩ : syracuseStep 2609069 = 978401) (by norm_num)
theorem B2936749 : Blo 1738570 2936749 := bbase (se 3 (by rfl) ⟨550640, by rfl⟩ : syracuseStep 2936749 = 1101281) (by norm_num)
theorem B2609093 : Blo 1738570 2609093 := bbase (se 4 (by rfl) ⟨244602, by rfl⟩ : syracuseStep 2609093 = 489205) (by norm_num)
theorem B6606805 : Blo 1738570 6606805 := bbase (se 7 (by rfl) ⟨77423, by rfl⟩ : syracuseStep 6606805 = 154847) (by norm_num)
theorem B2609117 : Blo 1738570 2609117 := bbase (se 3 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 2609117 = 978419) (by norm_num)
theorem B2609141 : Blo 1738570 2609141 := bbase (se 5 (by rfl) ⟨122303, by rfl⟩ : syracuseStep 2609141 = 244607) (by norm_num)
theorem B2936837 : Blo 1738570 2936837 := bbase (se 4 (by rfl) ⟨275328, by rfl⟩ : syracuseStep 2936837 = 550657) (by norm_num)
theorem B2609165 : Blo 1738570 2609165 := bbase (se 3 (by rfl) ⟨489218, by rfl⟩ : syracuseStep 2609165 = 978437) (by norm_num)
theorem B2609189 : Blo 1738570 2609189 := bbase (se 4 (by rfl) ⟨244611, by rfl⟩ : syracuseStep 2609189 = 489223) (by norm_num)
theorem B2609213 : Blo 1738570 2609213 := bbase (se 3 (by rfl) ⟨489227, by rfl⟩ : syracuseStep 2609213 = 978455) (by norm_num)
theorem B4403261 : Blo 1738570 4403261 := bbase (se 3 (by rfl) ⟨825611, by rfl⟩ : syracuseStep 4403261 = 1651223) (by norm_num)
theorem B5869637 : Blo 1738570 5869637 := bbase (se 4 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 5869637 = 1100557) (by norm_num)
theorem B2609237 : Blo 1738570 2609237 := bbase (se 8 (by rfl) ⟨15288, by rfl⟩ : syracuseStep 2609237 = 30577) (by norm_num)
theorem B2609261 : Blo 1738570 2609261 := bbase (se 3 (by rfl) ⟨489236, by rfl⟩ : syracuseStep 2609261 = 978473) (by norm_num)
theorem B2117749 : Blo 1738570 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B3911813 : Blo 1738570 3911813 := bbase (se 4 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 3911813 = 733465) (by norm_num)
theorem B2609285 : Blo 1738570 2609285 := bbase (se 4 (by rfl) ⟨244620, by rfl⟩ : syracuseStep 2609285 = 489241) (by norm_num)
theorem B2936965 : Blo 1738570 2936965 := bbase (se 4 (by rfl) ⟨275340, by rfl⟩ : syracuseStep 2936965 = 550681) (by norm_num)
theorem B2609309 : Blo 1738570 2609309 := bbase (se 3 (by rfl) ⟨489245, by rfl⟩ : syracuseStep 2609309 = 978491) (by norm_num)
theorem B3969181 : Blo 1738570 3969181 := bbase (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) (by norm_num)
theorem B11145397 : Blo 1738570 11145397 := bbase (se 5 (by rfl) ⟨522440, by rfl⟩ : syracuseStep 11145397 = 1044881) (by norm_num)
theorem B2609333 : Blo 1738570 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B8810693 : Blo 1738570 8810693 := bbase (se 4 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 8810693 = 1652005) (by norm_num)
theorem B3911885 : Blo 1738570 3911885 := bbase (se 3 (by rfl) ⟨733478, by rfl⟩ : syracuseStep 3911885 = 1466957) (by norm_num)
theorem B2609357 : Blo 1738570 2609357 := bbase (se 3 (by rfl) ⟨489254, by rfl⟩ : syracuseStep 2609357 = 978509) (by norm_num)
theorem B2937053 : Blo 1738570 2937053 := bbase (se 3 (by rfl) ⟨550697, by rfl⟩ : syracuseStep 2937053 = 1101395) (by norm_num)
theorem B2609381 : Blo 1738570 2609381 := bbase (se 4 (by rfl) ⟨244629, by rfl⟩ : syracuseStep 2609381 = 489259) (by norm_num)
theorem B2609405 : Blo 1738570 2609405 := bbase (se 3 (by rfl) ⟨489263, by rfl⟩ : syracuseStep 2609405 = 978527) (by norm_num)
theorem B6607109 : Blo 1738570 6607109 := bbase (se 4 (by rfl) ⟨619416, by rfl⟩ : syracuseStep 6607109 = 1238833) (by norm_num)
theorem B3911957 : Blo 1738570 3911957 := bbase (se 6 (by rfl) ⟨91686, by rfl⟩ : syracuseStep 3911957 = 183373) (by norm_num)
theorem B2609429 : Blo 1738570 2609429 := bbase (se 6 (by rfl) ⟨61158, by rfl⟩ : syracuseStep 2609429 = 122317) (by norm_num)
theorem B2609453 : Blo 1738570 2609453 := bbase (se 3 (by rfl) ⟨489272, by rfl⟩ : syracuseStep 2609453 = 978545) (by norm_num)
theorem B2609477 : Blo 1738570 2609477 := bbase (se 4 (by rfl) ⟨244638, by rfl⟩ : syracuseStep 2609477 = 489277) (by norm_num)
theorem B14856533 : Blo 1738570 14856533 := bbase (se 10 (by rfl) ⟨21762, by rfl⟩ : syracuseStep 14856533 = 43525) (by norm_num)
theorem B3912029 : Blo 1738570 3912029 := bbase (se 3 (by rfl) ⟨733505, by rfl⟩ : syracuseStep 3912029 = 1467011) (by norm_num)
theorem B2609501 : Blo 1738570 2609501 := bbase (se 3 (by rfl) ⟨489281, by rfl⟩ : syracuseStep 2609501 = 978563) (by norm_num)
theorem B2937181 : Blo 1738570 2937181 := bbase (se 3 (by rfl) ⟨550721, by rfl⟩ : syracuseStep 2937181 = 1101443) (by norm_num)
theorem B2609525 : Blo 1738570 2609525 := bbase (se 5 (by rfl) ⟨122321, by rfl⟩ : syracuseStep 2609525 = 244643) (by norm_num)
theorem B2609549 : Blo 1738570 2609549 := bbase (se 3 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 2609549 = 978581) (by norm_num)
theorem B4403605 : Blo 1738570 4403605 := bbase (se 6 (by rfl) ⟨103209, by rfl⟩ : syracuseStep 4403605 = 206419) (by norm_num)
theorem B3912101 : Blo 1738570 3912101 := bbase (se 4 (by rfl) ⟨366759, by rfl⟩ : syracuseStep 3912101 = 733519) (by norm_num)
theorem B2609573 : Blo 1738570 2609573 := bbase (se 4 (by rfl) ⟨244647, by rfl⟩ : syracuseStep 2609573 = 489295) (by norm_num)
theorem B2609597 : Blo 1738570 2609597 := bbase (se 3 (by rfl) ⟨489299, by rfl⟩ : syracuseStep 2609597 = 978599) (by norm_num)
theorem B4526533 : Blo 1738570 4526533 := bbase (se 4 (by rfl) ⟨424362, by rfl⟩ : syracuseStep 4526533 = 848725) (by norm_num)
theorem B2609621 : Blo 1738570 2609621 := bbase (se 7 (by rfl) ⟨30581, by rfl⟩ : syracuseStep 2609621 = 61163) (by norm_num)
theorem B3912173 : Blo 1738570 3912173 := bbase (se 3 (by rfl) ⟨733532, by rfl⟩ : syracuseStep 3912173 = 1467065) (by norm_num)
theorem B2609645 : Blo 1738570 2609645 := bbase (se 3 (by rfl) ⟨489308, by rfl⟩ : syracuseStep 2609645 = 978617) (by norm_num)
theorem B5870069 : Blo 1738570 5870069 := bbase (se 5 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 5870069 = 550319) (by norm_num)
theorem B4403717 : Blo 1738570 4403717 := bbase (se 4 (by rfl) ⟨412848, by rfl⟩ : syracuseStep 4403717 = 825697) (by norm_num)
theorem B2609669 : Blo 1738570 2609669 := bbase (se 4 (by rfl) ⟨244656, by rfl⟩ : syracuseStep 2609669 = 489313) (by norm_num)
theorem B2609693 : Blo 1738570 2609693 := bbase (se 3 (by rfl) ⟨489317, by rfl⟩ : syracuseStep 2609693 = 978635) (by norm_num)
theorem B3912245 : Blo 1738570 3912245 := bbase (se 5 (by rfl) ⟨183386, by rfl⟩ : syracuseStep 3912245 = 366773) (by norm_num)
theorem B2609717 : Blo 1738570 2609717 := bbase (se 5 (by rfl) ⟨122330, by rfl⟩ : syracuseStep 2609717 = 244661) (by norm_num)
theorem B3715645 : Blo 1738570 3715645 := bbase (se 3 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 3715645 = 1393367) (by norm_num)
theorem B2609741 : Blo 1738570 2609741 := bbase (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) (by norm_num)
theorem B8802917 : Blo 1738570 8802917 := bbase (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) (by norm_num)
theorem B2609765 : Blo 1738570 2609765 := bbase (se 4 (by rfl) ⟨244665, by rfl⟩ : syracuseStep 2609765 = 489331) (by norm_num)
theorem B3912317 : Blo 1738570 3912317 := bbase (se 3 (by rfl) ⟨733559, by rfl⟩ : syracuseStep 3912317 = 1467119) (by norm_num)
theorem B2609789 : Blo 1738570 2609789 := bbase (se 3 (by rfl) ⟨489335, by rfl⟩ : syracuseStep 2609789 = 978671) (by norm_num)
theorem B5575301 : Blo 1738570 5575301 := bbase (se 4 (by rfl) ⟨522684, by rfl⟩ : syracuseStep 5575301 = 1045369) (by norm_num)
theorem B2609813 : Blo 1738570 2609813 := bbase (se 6 (by rfl) ⟨61167, by rfl⟩ : syracuseStep 2609813 = 122335) (by norm_num)
theorem B2609837 : Blo 1738570 2609837 := bbase (se 3 (by rfl) ⟨489344, by rfl⟩ : syracuseStep 2609837 = 978689) (by norm_num)
theorem B3912389 : Blo 1738570 3912389 := bbase (se 4 (by rfl) ⟨366786, by rfl⟩ : syracuseStep 3912389 = 733573) (by norm_num)
theorem B4403909 : Blo 1738570 4403909 := bbase (se 4 (by rfl) ⟨412866, by rfl⟩ : syracuseStep 4403909 = 825733) (by norm_num)
theorem B2609861 : Blo 1738570 2609861 := bbase (se 4 (by rfl) ⟨244674, by rfl⟩ : syracuseStep 2609861 = 489349) (by norm_num)
theorem B7533269 : Blo 1738570 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B2609885 : Blo 1738570 2609885 := bbase (se 3 (by rfl) ⟨489353, by rfl⟩ : syracuseStep 2609885 = 978707) (by norm_num)
theorem B2609909 : Blo 1738570 2609909 := bbase (se 5 (by rfl) ⟨122339, by rfl⟩ : syracuseStep 2609909 = 244679) (by norm_num)
theorem B3912461 : Blo 1738570 3912461 := bbase (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) (by norm_num)
theorem B2609933 : Blo 1738570 2609933 := bbase (se 3 (by rfl) ⟨489362, by rfl⟩ : syracuseStep 2609933 = 978725) (by norm_num)
theorem B5952293 : Blo 1738570 5952293 := bbase (se 4 (by rfl) ⟨558027, by rfl⟩ : syracuseStep 5952293 = 1116055) (by norm_num)
theorem B2609957 : Blo 1738570 2609957 := bbase (se 4 (by rfl) ⟨244683, by rfl⟩ : syracuseStep 2609957 = 489367) (by norm_num)
theorem B2609981 : Blo 1738570 2609981 := bbase (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) (by norm_num)
theorem B2200385 : Blo 1738570 2200385 := bbase (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) (by norm_num)
theorem B3912533 : Blo 1738570 3912533 := bbase (se 9 (by rfl) ⟨11462, by rfl⟩ : syracuseStep 3912533 = 22925) (by norm_num)
theorem B4952917 : Blo 1738570 4952917 := bbase (se 9 (by rfl) ⟨14510, by rfl⟩ : syracuseStep 4952917 = 29021) (by norm_num)
theorem B2610005 : Blo 1738570 2610005 := bbase (se 9 (by rfl) ⟨7646, by rfl⟩ : syracuseStep 2610005 = 15293) (by norm_num)
theorem B3765085 : Blo 1738570 3765085 := bbase (se 3 (by rfl) ⟨705953, by rfl⟩ : syracuseStep 3765085 = 1411907) (by norm_num)
theorem B2610029 : Blo 1738570 2610029 := bbase (se 3 (by rfl) ⟨489380, by rfl⟩ : syracuseStep 2610029 = 978761) (by norm_num)
theorem B2200441 : Blo 1738570 2200441 := bbase (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) (by norm_num)
theorem B2610053 : Blo 1738570 2610053 := bbase (se 4 (by rfl) ⟨244692, by rfl⟩ : syracuseStep 2610053 = 489385) (by norm_num)
theorem B3912605 : Blo 1738570 3912605 := bbase (se 3 (by rfl) ⟨733613, by rfl⟩ : syracuseStep 3912605 = 1467227) (by norm_num)
theorem B2610077 : Blo 1738570 2610077 := bbase (se 3 (by rfl) ⟨489389, by rfl⟩ : syracuseStep 2610077 = 978779) (by norm_num)
theorem B5870501 : Blo 1738570 5870501 := bbase (se 4 (by rfl) ⟨550359, by rfl⟩ : syracuseStep 5870501 = 1100719) (by norm_num)
theorem B2610101 : Blo 1738570 2610101 := bbase (se 5 (by rfl) ⟨122348, by rfl⟩ : syracuseStep 2610101 = 244697) (by norm_num)
theorem B3134413 : Blo 1738570 3134413 := bbase (se 3 (by rfl) ⟨587702, by rfl⟩ : syracuseStep 3134413 = 1175405) (by norm_num)
theorem B2118605 : Blo 1738570 2118605 := bbase (se 3 (by rfl) ⟨397238, by rfl⟩ : syracuseStep 2118605 = 794477) (by norm_num)
theorem B2610125 : Blo 1738570 2610125 := bbase (se 3 (by rfl) ⟨489398, by rfl⟩ : syracuseStep 2610125 = 978797) (by norm_num)
theorem B2200537 : Blo 1738570 2200537 := bbase (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) (by norm_num)
theorem B3912677 : Blo 1738570 3912677 := bbase (se 4 (by rfl) ⟨366813, by rfl⟩ : syracuseStep 3912677 = 733627) (by norm_num)
theorem B2610149 : Blo 1738570 2610149 := bbase (se 4 (by rfl) ⟨244701, by rfl⟩ : syracuseStep 2610149 = 489403) (by norm_num)
theorem B2610173 : Blo 1738570 2610173 := bbase (se 3 (by rfl) ⟨489407, by rfl⟩ : syracuseStep 2610173 = 978815) (by norm_num)
theorem B2610197 : Blo 1738570 2610197 := bbase (se 6 (by rfl) ⟨61176, by rfl⟩ : syracuseStep 2610197 = 122353) (by norm_num)
theorem B4404253 : Blo 1738570 4404253 := bbase (se 3 (by rfl) ⟨825797, by rfl⟩ : syracuseStep 4404253 = 1651595) (by norm_num)
theorem B3912749 : Blo 1738570 3912749 := bbase (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) (by norm_num)
theorem B2610221 : Blo 1738570 2610221 := bbase (se 3 (by rfl) ⟨489416, by rfl⟩ : syracuseStep 2610221 = 978833) (by norm_num)
theorem B2610245 : Blo 1738570 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B2610269 : Blo 1738570 2610269 := bbase (se 3 (by rfl) ⟨489425, by rfl⟩ : syracuseStep 2610269 = 978851) (by norm_num)
theorem B7427173 : Blo 1738570 7427173 := bbase (se 4 (by rfl) ⟨696297, by rfl⟩ : syracuseStep 7427173 = 1392595) (by norm_num)
theorem B7427189 : Blo 1738570 7427189 := bbase (se 5 (by rfl) ⟨348149, by rfl⟩ : syracuseStep 7427189 = 696299) (by norm_num)
theorem B3912821 : Blo 1738570 3912821 := bbase (se 5 (by rfl) ⟨183413, by rfl⟩ : syracuseStep 3912821 = 366827) (by norm_num)
theorem B2610293 : Blo 1738570 2610293 := bbase (se 5 (by rfl) ⟨122357, by rfl⟩ : syracuseStep 2610293 = 244715) (by norm_num)
theorem B2200709 : Blo 1738570 2200709 := bbase (se 4 (by rfl) ⟨206316, by rfl⟩ : syracuseStep 2200709 = 412633) (by norm_num)
theorem B4404365 : Blo 1738570 4404365 := bbase (se 3 (by rfl) ⟨825818, by rfl⟩ : syracuseStep 4404365 = 1651637) (by norm_num)
theorem B2610317 : Blo 1738570 2610317 := bbase (se 3 (by rfl) ⟨489434, by rfl⟩ : syracuseStep 2610317 = 978869) (by norm_num)
theorem B3134629 : Blo 1738570 3134629 := bbase (se 4 (by rfl) ⟨293871, by rfl⟩ : syracuseStep 3134629 = 587743) (by norm_num)
theorem B2610341 : Blo 1738570 2610341 := bbase (se 4 (by rfl) ⟨244719, by rfl⟩ : syracuseStep 2610341 = 489439) (by norm_num)
theorem B2200765 : Blo 1738570 2200765 := bbase (se 3 (by rfl) ⟨412643, by rfl⟩ : syracuseStep 2200765 = 825287) (by norm_num)
theorem B3912893 : Blo 1738570 3912893 := bbase (se 3 (by rfl) ⟨733667, by rfl⟩ : syracuseStep 3912893 = 1467335) (by norm_num)
theorem B3527869 : Blo 1738570 3527869 := bbase (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) (by norm_num)
theorem B2610365 : Blo 1738570 2610365 := bbase (se 3 (by rfl) ⟨489443, by rfl⟩ : syracuseStep 2610365 = 978887) (by norm_num)
theorem B2610389 : Blo 1738570 2610389 := bbase (se 7 (by rfl) ⟨30590, by rfl⟩ : syracuseStep 2610389 = 61181) (by norm_num)
theorem B1856729 : Blo 1738570 1856729 := bbase (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) (by norm_num)
theorem B2610413 : Blo 1738570 2610413 := bbase (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) (by norm_num)
theorem B3527933 : Blo 1738570 3527933 := bbase (se 3 (by rfl) ⟨661487, by rfl⟩ : syracuseStep 3527933 = 1322975) (by norm_num)
theorem B3912965 : Blo 1738570 3912965 := bbase (se 4 (by rfl) ⟨366840, by rfl⟩ : syracuseStep 3912965 = 733681) (by norm_num)
theorem B2610437 : Blo 1738570 2610437 := bbase (se 4 (by rfl) ⟨244728, by rfl⟩ : syracuseStep 2610437 = 489457) (by norm_num)
theorem B2200861 : Blo 1738570 2200861 := bbase (se 3 (by rfl) ⟨412661, by rfl⟩ : syracuseStep 2200861 = 825323) (by norm_num)
theorem B2610461 : Blo 1738570 2610461 := bbase (se 3 (by rfl) ⟨489461, by rfl⟩ : syracuseStep 2610461 = 978923) (by norm_num)
theorem B2610485 : Blo 1738570 2610485 := bbase (se 5 (by rfl) ⟨122366, by rfl⟩ : syracuseStep 2610485 = 244733) (by norm_num)
theorem B3913037 : Blo 1738570 3913037 := bbase (se 3 (by rfl) ⟨733694, by rfl⟩ : syracuseStep 3913037 = 1467389) (by norm_num)
theorem B4404557 : Blo 1738570 4404557 := bbase (se 3 (by rfl) ⟨825854, by rfl⟩ : syracuseStep 4404557 = 1651709) (by norm_num)
theorem B2610509 : Blo 1738570 2610509 := bbase (se 3 (by rfl) ⟨489470, by rfl⟩ : syracuseStep 2610509 = 978941) (by norm_num)
theorem B7050581 : Blo 1738570 7050581 := bbase (se 14 (by rfl) ⟨645, by rfl⟩ : syracuseStep 7050581 = 1291) (by norm_num)
theorem B5870933 : Blo 1738570 5870933 := bbase (se 14 (by rfl) ⟨537, by rfl⟩ : syracuseStep 5870933 = 1075) (by norm_num)
theorem B2610533 : Blo 1738570 2610533 := bbase (se 4 (by rfl) ⟨244737, by rfl⟩ : syracuseStep 2610533 = 489475) (by norm_num)
theorem B2610557 : Blo 1738570 2610557 := bbase (se 3 (by rfl) ⟨489479, by rfl⟩ : syracuseStep 2610557 = 978959) (by norm_num)
theorem B3913109 : Blo 1738570 3913109 := bbase (se 6 (by rfl) ⟨91713, by rfl⟩ : syracuseStep 3913109 = 183427) (by norm_num)
theorem B2610581 : Blo 1738570 2610581 := bbase (se 6 (by rfl) ⟨61185, by rfl⟩ : syracuseStep 2610581 = 122371) (by norm_num)
theorem B2717093 : Blo 1738570 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B2610605 : Blo 1738570 2610605 := bbase (se 3 (by rfl) ⟨489488, by rfl⟩ : syracuseStep 2610605 = 978977) (by norm_num)
theorem B3716533 : Blo 1738570 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B2610629 : Blo 1738570 2610629 := bbase (se 4 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 2610629 = 489493) (by norm_num)
theorem B2201033 : Blo 1738570 2201033 := bbase (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) (by norm_num)
theorem B3913181 : Blo 1738570 3913181 := bbase (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) (by norm_num)
theorem B2610653 : Blo 1738570 2610653 := bbase (se 3 (by rfl) ⟨489497, by rfl⟩ : syracuseStep 2610653 = 978995) (by norm_num)
theorem B2610677 : Blo 1738570 2610677 := bbase (se 5 (by rfl) ⟨122375, by rfl⟩ : syracuseStep 2610677 = 244751) (by norm_num)
theorem B2201089 : Blo 1738570 2201089 := bbase (se 2 (by rfl) ⟨825408, by rfl⟩ : syracuseStep 2201089 = 1650817) (by norm_num)
theorem B2610701 : Blo 1738570 2610701 := bbase (se 3 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 2610701 = 979013) (by norm_num)
theorem B3913253 : Blo 1738570 3913253 := bbase (se 4 (by rfl) ⟨366867, by rfl⟩ : syracuseStep 3913253 = 733735) (by norm_num)
theorem B2610725 : Blo 1738570 2610725 := bbase (se 4 (by rfl) ⟨244755, by rfl⟩ : syracuseStep 2610725 = 489511) (by norm_num)
theorem B2610749 : Blo 1738570 2610749 := bbase (se 3 (by rfl) ⟨489515, by rfl⟩ : syracuseStep 2610749 = 979031) (by norm_num)
theorem B2610773 : Blo 1738570 2610773 := bbase (se 8 (by rfl) ⟨15297, by rfl⟩ : syracuseStep 2610773 = 30595) (by norm_num)
theorem B2201185 : Blo 1738570 2201185 := bbase (se 2 (by rfl) ⟨825444, by rfl⟩ : syracuseStep 2201185 = 1650889) (by norm_num)
theorem B3913325 : Blo 1738570 3913325 := bbase (se 3 (by rfl) ⟨733748, by rfl⟩ : syracuseStep 3913325 = 1467497) (by norm_num)
theorem B2610797 : Blo 1738570 2610797 := bbase (se 3 (by rfl) ⟨489524, by rfl⟩ : syracuseStep 2610797 = 979049) (by norm_num)
theorem B2610821 : Blo 1738570 2610821 := bbase (se 4 (by rfl) ⟨244764, by rfl⟩ : syracuseStep 2610821 = 489529) (by norm_num)
theorem B1857173 : Blo 1738570 1857173 := bbase (se 6 (by rfl) ⟨43527, by rfl⟩ : syracuseStep 1857173 = 87055) (by norm_num)
theorem B2610845 : Blo 1738570 2610845 := bbase (se 3 (by rfl) ⟨489533, by rfl⟩ : syracuseStep 2610845 = 979067) (by norm_num)
theorem B4404901 : Blo 1738570 4404901 := bbase (se 4 (by rfl) ⟨412959, by rfl⟩ : syracuseStep 4404901 = 825919) (by norm_num)
theorem B3913397 : Blo 1738570 3913397 := bbase (se 5 (by rfl) ⟨183440, by rfl⟩ : syracuseStep 3913397 = 366881) (by norm_num)
theorem B3913469 : Blo 1738570 3913469 := bbase (se 3 (by rfl) ⟨733775, by rfl⟩ : syracuseStep 3913469 = 1467551) (by norm_num)
theorem B5871365 : Blo 1738570 5871365 := bbase (se 4 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 5871365 = 1100881) (by norm_num)
theorem B2201357 : Blo 1738570 2201357 := bbase (se 3 (by rfl) ⟨412754, by rfl⟩ : syracuseStep 2201357 = 825509) (by norm_num)
theorem B4405013 : Blo 1738570 4405013 := bbase (se 6 (by rfl) ⟨103242, by rfl⟩ : syracuseStep 4405013 = 206485) (by norm_num)
theorem B3913541 : Blo 1738570 3913541 := bbase (se 4 (by rfl) ⟨366894, by rfl⟩ : syracuseStep 3913541 = 733789) (by norm_num)
theorem B2201413 : Blo 1738570 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B8804213 : Blo 1738570 8804213 := bbase (se 5 (by rfl) ⟨412697, by rfl⟩ : syracuseStep 8804213 = 825395) (by norm_num)
theorem B5289845 : Blo 1738570 5289845 := bbase (se 5 (by rfl) ⟨247961, by rfl⟩ : syracuseStep 5289845 = 495923) (by norm_num)
theorem B2643853 : Blo 1738570 2643853 := bbase (se 3 (by rfl) ⟨495722, by rfl⟩ : syracuseStep 2643853 = 991445) (by norm_num)
theorem B1857421 : Blo 1738570 1857421 := bbase (se 3 (by rfl) ⟨348266, by rfl⟩ : syracuseStep 1857421 = 696533) (by norm_num)
theorem B3913613 : Blo 1738570 3913613 := bbase (se 3 (by rfl) ⟨733802, by rfl⟩ : syracuseStep 3913613 = 1467605) (by norm_num)
theorem B2201509 : Blo 1738570 2201509 := bbase (se 4 (by rfl) ⟨206391, by rfl⟩ : syracuseStep 2201509 = 412783) (by norm_num)
theorem B8361893 : Blo 1738570 8361893 := bbase (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) (by norm_num)
theorem B3717029 : Blo 1738570 3717029 := bbase (se 4 (by rfl) ⟨348471, by rfl⟩ : syracuseStep 3717029 = 696943) (by norm_num)
theorem B3135437 : Blo 1738570 3135437 := bbase (se 3 (by rfl) ⟨587894, by rfl⟩ : syracuseStep 3135437 = 1175789) (by norm_num)
theorem B3913685 : Blo 1738570 3913685 := bbase (se 7 (by rfl) ⟨45863, by rfl⟩ : syracuseStep 3913685 = 91727) (by norm_num)
theorem B4405205 : Blo 1738570 4405205 := bbase (se 7 (by rfl) ⟨51623, by rfl⟩ : syracuseStep 4405205 = 103247) (by norm_num)
theorem B2578405 : Blo 1738570 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B3913757 : Blo 1738570 3913757 := bbase (se 3 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 3913757 = 1467659) (by norm_num)
theorem B1955893 : Blo 1738570 1955893 := bbase (se 5 (by rfl) ⟨91682, by rfl⟩ : syracuseStep 1955893 = 183365) (by norm_num)
theorem B2201681 : Blo 1738570 2201681 := bbase (se 2 (by rfl) ⟨825630, by rfl⟩ : syracuseStep 2201681 = 1651261) (by norm_num)
theorem B12064853 : Blo 1738570 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B1955929 : Blo 1738570 1955929 := bbase (se 2 (by rfl) ⟨733473, by rfl⟩ : syracuseStep 1955929 = 1466947) (by norm_num)
theorem B3913829 : Blo 1738570 3913829 := bbase (se 4 (by rfl) ⟨366921, by rfl⟩ : syracuseStep 3913829 = 733843) (by norm_num)
theorem B1955965 : Blo 1738570 1955965 := bbase (se 3 (by rfl) ⟨366743, by rfl⟩ : syracuseStep 1955965 = 733487) (by norm_num)
theorem B2201737 : Blo 1738570 2201737 := bbase (se 2 (by rfl) ⟨825651, by rfl⟩ : syracuseStep 2201737 = 1651303) (by norm_num)
theorem B1956001 : Blo 1738570 1956001 := bbase (se 2 (by rfl) ⟨733500, by rfl⟩ : syracuseStep 1956001 = 1467001) (by norm_num)
theorem B3913901 : Blo 1738570 3913901 := bbase (se 3 (by rfl) ⟨733856, by rfl⟩ : syracuseStep 3913901 = 1467713) (by norm_num)
theorem B5871797 : Blo 1738570 5871797 := bbase (se 5 (by rfl) ⟨275240, by rfl⟩ : syracuseStep 5871797 = 550481) (by norm_num)
theorem B1956037 : Blo 1738570 1956037 := bbase (se 4 (by rfl) ⟨183378, by rfl⟩ : syracuseStep 1956037 = 366757) (by norm_num)
theorem B1956073 : Blo 1738570 1956073 := bbase (se 2 (by rfl) ⟨733527, by rfl⟩ : syracuseStep 1956073 = 1467055) (by norm_num)
theorem B2201833 : Blo 1738570 2201833 := bbase (se 2 (by rfl) ⟨825687, by rfl⟩ : syracuseStep 2201833 = 1651375) (by norm_num)
theorem B3913973 : Blo 1738570 3913973 := bbase (se 5 (by rfl) ⟨183467, by rfl⟩ : syracuseStep 3913973 = 366935) (by norm_num)
theorem B1956109 : Blo 1738570 1956109 := bbase (se 3 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 1956109 = 733541) (by norm_num)
theorem B4405549 : Blo 1738570 4405549 := bbase (se 3 (by rfl) ⟨826040, by rfl⟩ : syracuseStep 4405549 = 1652081) (by norm_num)
theorem B1956145 : Blo 1738570 1956145 := bbase (se 2 (by rfl) ⟨733554, by rfl⟩ : syracuseStep 1956145 = 1467109) (by norm_num)
theorem B4954421 : Blo 1738570 4954421 := bbase (se 5 (by rfl) ⟨232238, by rfl⟩ : syracuseStep 4954421 = 464477) (by norm_num)
theorem B3914045 : Blo 1738570 3914045 := bbase (se 3 (by rfl) ⟨733883, by rfl⟩ : syracuseStep 3914045 = 1467767) (by norm_num)
theorem B1857853 : Blo 1738570 1857853 := bbase (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) (by norm_num)
theorem B1956181 : Blo 1738570 1956181 := bbase (se 10 (by rfl) ⟨2865, by rfl⟩ : syracuseStep 1956181 = 5731) (by norm_num)
theorem B1956217 : Blo 1738570 1956217 := bbase (se 2 (by rfl) ⟨733581, by rfl⟩ : syracuseStep 1956217 = 1467163) (by norm_num)
theorem B3914117 : Blo 1738570 3914117 := bbase (se 4 (by rfl) ⟨366948, by rfl⟩ : syracuseStep 3914117 = 733897) (by norm_num)
theorem B1857925 : Blo 1738570 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B2202005 : Blo 1738570 2202005 := bbase (se 6 (by rfl) ⟨51609, by rfl⟩ : syracuseStep 2202005 = 103219) (by norm_num)
theorem B1956253 : Blo 1738570 1956253 := bbase (se 3 (by rfl) ⟨366797, by rfl⟩ : syracuseStep 1956253 = 733595) (by norm_num)
theorem B4405661 : Blo 1738570 4405661 := bbase (se 3 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 4405661 = 1652123) (by norm_num)
theorem B1956289 : Blo 1738570 1956289 := bbase (se 2 (by rfl) ⟨733608, by rfl⟩ : syracuseStep 1956289 = 1467217) (by norm_num)
theorem B3914189 : Blo 1738570 3914189 := bbase (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) (by norm_num)
theorem B2202061 : Blo 1738570 2202061 := bbase (se 3 (by rfl) ⟨412886, by rfl⟩ : syracuseStep 2202061 = 825773) (by norm_num)
theorem B1956325 : Blo 1738570 1956325 := bbase (se 4 (by rfl) ⟨183405, by rfl⟩ : syracuseStep 1956325 = 366811) (by norm_num)
theorem B1956361 : Blo 1738570 1956361 := bbase (se 2 (by rfl) ⟨733635, by rfl⟩ : syracuseStep 1956361 = 1467271) (by norm_num)
theorem B3914261 : Blo 1738570 3914261 := bbase (se 6 (by rfl) ⟨91740, by rfl⟩ : syracuseStep 3914261 = 183481) (by norm_num)
theorem B1956397 : Blo 1738570 1956397 := bbase (se 3 (by rfl) ⟨366824, by rfl⟩ : syracuseStep 1956397 = 733649) (by norm_num)
theorem B2202157 : Blo 1738570 2202157 := bbase (se 3 (by rfl) ⟨412904, by rfl⟩ : syracuseStep 2202157 = 825809) (by norm_num)
theorem B9902645 : Blo 1738570 9902645 := bbase (se 5 (by rfl) ⟨464186, by rfl⟩ : syracuseStep 9902645 = 928373) (by norm_num)
theorem B15874613 : Blo 1738570 15874613 := bbase (se 5 (by rfl) ⟨744122, by rfl⟩ : syracuseStep 15874613 = 1488245) (by norm_num)
theorem B1956433 : Blo 1738570 1956433 := bbase (se 2 (by rfl) ⟨733662, by rfl⟩ : syracuseStep 1956433 = 1467325) (by norm_num)
theorem B10582613 : Blo 1738570 10582613 := bbase (se 8 (by rfl) ⟨62007, by rfl⟩ : syracuseStep 10582613 = 124015) (by norm_num)
theorem B3914333 : Blo 1738570 3914333 := bbase (se 3 (by rfl) ⟨733937, by rfl⟩ : syracuseStep 3914333 = 1467875) (by norm_num)
theorem B5872229 : Blo 1738570 5872229 := bbase (se 4 (by rfl) ⟨550521, by rfl⟩ : syracuseStep 5872229 = 1101043) (by norm_num)
theorem B1956469 : Blo 1738570 1956469 := bbase (se 5 (by rfl) ⟨91709, by rfl⟩ : syracuseStep 1956469 = 183419) (by norm_num)
theorem B1956505 : Blo 1738570 1956505 := bbase (se 2 (by rfl) ⟨733689, by rfl⟩ : syracuseStep 1956505 = 1467379) (by norm_num)
theorem B3914405 : Blo 1738570 3914405 := bbase (se 4 (by rfl) ⟨366975, by rfl⟩ : syracuseStep 3914405 = 733951) (by norm_num)
theorem B1956541 : Blo 1738570 1956541 := bbase (se 3 (by rfl) ⟨366851, by rfl⟩ : syracuseStep 1956541 = 733703) (by norm_num)
theorem B7051973 : Blo 1738570 7051973 := bbase (se 4 (by rfl) ⟨661122, by rfl⟩ : syracuseStep 7051973 = 1322245) (by norm_num)
theorem B2202329 : Blo 1738570 2202329 := bbase (se 2 (by rfl) ⟨825873, by rfl⟩ : syracuseStep 2202329 = 1651747) (by norm_num)
theorem B1956577 : Blo 1738570 1956577 := bbase (se 2 (by rfl) ⟨733716, by rfl⟩ : syracuseStep 1956577 = 1467433) (by norm_num)
theorem B6601445 : Blo 1738570 6601445 := bbase (se 4 (by rfl) ⟨618885, by rfl⟩ : syracuseStep 6601445 = 1237771) (by norm_num)
theorem B3914477 : Blo 1738570 3914477 := bbase (se 3 (by rfl) ⟨733964, by rfl⟩ : syracuseStep 3914477 = 1467929) (by norm_num)
theorem B1858297 : Blo 1738570 1858297 := bbase (se 2 (by rfl) ⟨696861, by rfl⟩ : syracuseStep 1858297 = 1393723) (by norm_num)
theorem B1956613 : Blo 1738570 1956613 := bbase (se 4 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 1956613 = 366865) (by norm_num)
theorem B2202385 : Blo 1738570 2202385 := bbase (se 2 (by rfl) ⟨825894, by rfl⟩ : syracuseStep 2202385 = 1651789) (by norm_num)
theorem B10582805 : Blo 1738570 10582805 := bbase (se 6 (by rfl) ⟨248034, by rfl⟩ : syracuseStep 10582805 = 496069) (by norm_num)
theorem B1956649 : Blo 1738570 1956649 := bbase (se 2 (by rfl) ⟨733743, by rfl⟩ : syracuseStep 1956649 = 1467487) (by norm_num)
theorem B3914549 : Blo 1738570 3914549 := bbase (se 5 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 3914549 = 366989) (by norm_num)
theorem B1956685 : Blo 1738570 1956685 := bbase (se 3 (by rfl) ⟨366878, by rfl⟩ : syracuseStep 1956685 = 733757) (by norm_num)
theorem B1956721 : Blo 1738570 1956721 := bbase (se 2 (by rfl) ⟨733770, by rfl⟩ : syracuseStep 1956721 = 1467541) (by norm_num)
theorem B2202481 : Blo 1738570 2202481 := bbase (se 2 (by rfl) ⟨825930, by rfl⟩ : syracuseStep 2202481 = 1651861) (by norm_num)
theorem B3914621 : Blo 1738570 3914621 := bbase (se 3 (by rfl) ⟨733991, by rfl⟩ : syracuseStep 3914621 = 1467983) (by norm_num)
theorem B1956757 : Blo 1738570 1956757 := bbase (se 6 (by rfl) ⟨45861, by rfl⟩ : syracuseStep 1956757 = 91723) (by norm_num)
theorem B3349397 : Blo 1738570 3349397 := bbase (se 6 (by rfl) ⟨78501, by rfl⟩ : syracuseStep 3349397 = 157003) (by norm_num)
theorem B4463525 : Blo 1738570 4463525 := bbase (se 4 (by rfl) ⟨418455, by rfl⟩ : syracuseStep 4463525 = 836911) (by norm_num)
theorem B1956793 : Blo 1738570 1956793 := bbase (se 2 (by rfl) ⟨733797, by rfl⟩ : syracuseStep 1956793 = 1467595) (by norm_num)
theorem B3914693 : Blo 1738570 3914693 := bbase (se 4 (by rfl) ⟨367002, by rfl⟩ : syracuseStep 3914693 = 734005) (by norm_num)
theorem B1956829 : Blo 1738570 1956829 := bbase (se 3 (by rfl) ⟨366905, by rfl⟩ : syracuseStep 1956829 = 733811) (by norm_num)
theorem B1956865 : Blo 1738570 1956865 := bbase (se 2 (by rfl) ⟨733824, by rfl⟩ : syracuseStep 1956865 = 1467649) (by norm_num)
theorem B6601733 : Blo 1738570 6601733 := bbase (se 4 (by rfl) ⟨618912, by rfl⟩ : syracuseStep 6601733 = 1237825) (by norm_num)
theorem B3914765 : Blo 1738570 3914765 := bbase (se 3 (by rfl) ⟨734018, by rfl⟩ : syracuseStep 3914765 = 1468037) (by norm_num)
theorem B5872661 : Blo 1738570 5872661 := bbase (se 6 (by rfl) ⟨137640, by rfl⟩ : syracuseStep 5872661 = 275281) (by norm_num)
theorem B2202653 : Blo 1738570 2202653 := bbase (se 3 (by rfl) ⟨412997, by rfl⟩ : syracuseStep 2202653 = 825995) (by norm_num)
theorem B1956901 : Blo 1738570 1956901 := bbase (se 4 (by rfl) ⟨183459, by rfl⟩ : syracuseStep 1956901 = 366919) (by norm_num)
theorem B4701253 : Blo 1738570 4701253 := bbase (se 4 (by rfl) ⟨440742, by rfl⟩ : syracuseStep 4701253 = 881485) (by norm_num)
theorem B1956937 : Blo 1738570 1956937 := bbase (se 2 (by rfl) ⟨733851, by rfl⟩ : syracuseStep 1956937 = 1467703) (by norm_num)
theorem B3914837 : Blo 1738570 3914837 := bbase (se 8 (by rfl) ⟨22938, by rfl⟩ : syracuseStep 3914837 = 45877) (by norm_num)
theorem B2202709 : Blo 1738570 2202709 := bbase (se 8 (by rfl) ⟨12906, by rfl⟩ : syracuseStep 2202709 = 25813) (by norm_num)
theorem B1956973 : Blo 1738570 1956973 := bbase (se 3 (by rfl) ⟨366932, by rfl⟩ : syracuseStep 1956973 = 733865) (by norm_num)
theorem B1858673 : Blo 1738570 1858673 := bbase (se 2 (by rfl) ⟨697002, by rfl⟩ : syracuseStep 1858673 = 1394005) (by norm_num)
theorem B8805509 : Blo 1738570 8805509 := bbase (se 4 (by rfl) ⟨825516, by rfl⟩ : syracuseStep 8805509 = 1651033) (by norm_num)
theorem B1957009 : Blo 1738570 1957009 := bbase (se 2 (by rfl) ⟨733878, by rfl⟩ : syracuseStep 1957009 = 1467757) (by norm_num)
theorem B3914909 : Blo 1738570 3914909 := bbase (se 3 (by rfl) ⟨734045, by rfl⟩ : syracuseStep 3914909 = 1468091) (by norm_num)
theorem B5291173 : Blo 1738570 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B1957045 : Blo 1738570 1957045 := bbase (se 5 (by rfl) ⟨91736, by rfl⟩ : syracuseStep 1957045 = 183473) (by norm_num)
theorem B2202805 : Blo 1738570 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1957081 : Blo 1738570 1957081 := bbase (se 2 (by rfl) ⟨733905, by rfl⟩ : syracuseStep 1957081 = 1467811) (by norm_num)
theorem B3914981 : Blo 1738570 3914981 := bbase (se 4 (by rfl) ⟨367029, by rfl⟩ : syracuseStep 3914981 = 734059) (by norm_num)
theorem B1957117 : Blo 1738570 1957117 := bbase (se 3 (by rfl) ⟨366959, by rfl⟩ : syracuseStep 1957117 = 733919) (by norm_num)
theorem B2645245 : Blo 1738570 2645245 := bbase (se 3 (by rfl) ⟨495983, by rfl⟩ : syracuseStep 2645245 = 991967) (by norm_num)
theorem B1957153 : Blo 1738570 1957153 := bbase (se 2 (by rfl) ⟨733932, by rfl⟩ : syracuseStep 1957153 = 1467865) (by norm_num)
theorem B5569829 : Blo 1738570 5569829 := bbase (se 4 (by rfl) ⟨522171, by rfl⟩ : syracuseStep 5569829 = 1044343) (by norm_num)
theorem B3915053 : Blo 1738570 3915053 := bbase (se 3 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 3915053 = 1468145) (by norm_num)
theorem B7429445 : Blo 1738570 7429445 := bbase (se 4 (by rfl) ⟨696510, by rfl⟩ : syracuseStep 7429445 = 1393021) (by norm_num)
theorem B1957189 : Blo 1738570 1957189 := bbase (se 4 (by rfl) ⟨183486, by rfl⟩ : syracuseStep 1957189 = 366973) (by norm_num)
theorem B1957225 : Blo 1738570 1957225 := bbase (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) (by norm_num)
theorem B2350453 : Blo 1738570 2350453 := bbase (se 5 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 2350453 = 220355) (by norm_num)
theorem B3915125 : Blo 1738570 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B1957261 : Blo 1738570 1957261 := bbase (se 3 (by rfl) ⟨366986, by rfl⟩ : syracuseStep 1957261 = 733973) (by norm_num)
theorem B6266261 : Blo 1738570 6266261 := bbase (se 6 (by rfl) ⟨146865, by rfl⟩ : syracuseStep 6266261 = 293731) (by norm_num)
theorem B4177325 : Blo 1738570 4177325 := bbase (se 3 (by rfl) ⟨783248, by rfl⟩ : syracuseStep 4177325 = 1566497) (by norm_num)
theorem B1957297 : Blo 1738570 1957297 := bbase (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) (by norm_num)
theorem B3915197 : Blo 1738570 3915197 := bbase (se 3 (by rfl) ⟨734099, by rfl⟩ : syracuseStep 3915197 = 1468199) (by norm_num)
theorem B5873093 : Blo 1738570 5873093 := bbase (se 4 (by rfl) ⟨550602, by rfl⟩ : syracuseStep 5873093 = 1101205) (by norm_num)
theorem B3300821 : Blo 1738570 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B1957333 : Blo 1738570 1957333 := bbase (se 7 (by rfl) ⟨22937, by rfl⟩ : syracuseStep 1957333 = 45875) (by norm_num)
theorem B3915773 : Blo 1738570 3915773 := bbase (se 3 (by rfl) ⟨734207, by rfl⟩ : syracuseStep 3915773 = 1468415) (by norm_num)
theorem B1957369 : Blo 1738570 1957369 := bbase (se 2 (by rfl) ⟨734013, by rfl⟩ : syracuseStep 1957369 = 1468027) (by norm_num)
theorem B3915269 : Blo 1738570 3915269 := bbase (se 4 (by rfl) ⟨367056, by rfl⟩ : syracuseStep 3915269 = 734113) (by norm_num)
theorem B1957405 : Blo 1738570 1957405 := bbase (se 3 (by rfl) ⟨367013, by rfl⟩ : syracuseStep 1957405 = 734027) (by norm_num)
theorem B1957441 : Blo 1738570 1957441 := bbase (se 2 (by rfl) ⟨734040, by rfl⟩ : syracuseStep 1957441 = 1468081) (by norm_num)
theorem B3915341 : Blo 1738570 3915341 := bbase (se 3 (by rfl) ⟨734126, by rfl⟩ : syracuseStep 3915341 = 1468253) (by norm_num)
theorem B1957477 : Blo 1738570 1957477 := bbase (se 4 (by rfl) ⟨183513, by rfl⟩ : syracuseStep 1957477 = 367027) (by norm_num)
theorem B1957513 : Blo 1738570 1957513 := bbase (se 2 (by rfl) ⟨734067, by rfl⟩ : syracuseStep 1957513 = 1468135) (by norm_num)
theorem B3915413 : Blo 1738570 3915413 := bbase (se 6 (by rfl) ⟨91767, by rfl⟩ : syracuseStep 3915413 = 183535) (by norm_num)
theorem B1957549 : Blo 1738570 1957549 := bbase (se 3 (by rfl) ⟨367040, by rfl⟩ : syracuseStep 1957549 = 734081) (by norm_num)
theorem B1957585 : Blo 1738570 1957585 := bbase (se 2 (by rfl) ⟨734094, by rfl⟩ : syracuseStep 1957585 = 1468189) (by norm_num)
theorem B9903829 : Blo 1738570 9903829 := bbase (se 7 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 9903829 = 232121) (by norm_num)
theorem B6356693 : Blo 1738570 6356693 := bbase (se 7 (by rfl) ⟨74492, by rfl⟩ : syracuseStep 6356693 = 148985) (by norm_num)
theorem B3915485 : Blo 1738570 3915485 := bbase (se 3 (by rfl) ⟨734153, by rfl⟩ : syracuseStep 3915485 = 1468307) (by norm_num)
theorem B1957621 : Blo 1738570 1957621 := bbase (se 5 (by rfl) ⟨91763, by rfl⟩ : syracuseStep 1957621 = 183527) (by norm_num)
theorem B1957657 : Blo 1738570 1957657 := bbase (se 2 (by rfl) ⟨734121, by rfl⟩ : syracuseStep 1957657 = 1468243) (by norm_num)
theorem B3915557 : Blo 1738570 3915557 := bbase (se 4 (by rfl) ⟨367083, by rfl⟩ : syracuseStep 3915557 = 734167) (by norm_num)
theorem B1957693 : Blo 1738570 1957693 := bbase (se 3 (by rfl) ⟨367067, by rfl⟩ : syracuseStep 1957693 = 734135) (by norm_num)
theorem B1957729 : Blo 1738570 1957729 := bbase (se 2 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 1957729 = 1468297) (by norm_num)
theorem B4956005 : Blo 1738570 4956005 := bbase (se 4 (by rfl) ⟨464625, by rfl⟩ : syracuseStep 4956005 = 929251) (by norm_num)
theorem B3915629 : Blo 1738570 3915629 := bbase (se 3 (by rfl) ⟨734180, by rfl⟩ : syracuseStep 3915629 = 1468361) (by norm_num)
theorem B5873525 : Blo 1738570 5873525 := bbase (se 5 (by rfl) ⟨275321, by rfl⟩ : syracuseStep 5873525 = 550643) (by norm_num)
theorem B1957765 : Blo 1738570 1957765 := bbase (se 4 (by rfl) ⟨183540, by rfl⟩ : syracuseStep 1957765 = 367081) (by norm_num)
theorem B2383781 : Blo 1738570 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B1957801 : Blo 1738570 1957801 := bbase (se 2 (by rfl) ⟨734175, by rfl⟩ : syracuseStep 1957801 = 1468351) (by norm_num)
theorem B3915701 : Blo 1738570 3915701 := bbase (se 5 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 3915701 = 367097) (by norm_num)
theorem B1957837 : Blo 1738570 1957837 := bbase (se 3 (by rfl) ⟨367094, by rfl⟩ : syracuseStep 1957837 = 734189) (by norm_num)
theorem B2785261 : Blo 1738570 2785261 := bbase (se 3 (by rfl) ⟨522236, by rfl⟩ : syracuseStep 2785261 = 1044473) (by norm_num)
theorem B1957873 : Blo 1738570 1957873 := bbase (se 2 (by rfl) ⟨734202, by rfl⟩ : syracuseStep 1957873 = 1468405) (by norm_num)
theorem B1957891 : Blo 1738570 1957891 := bstep (se 1 (by rfl) ⟨1468418, by rfl⟩ : syracuseStep 1957891 = 2936837) B2936837
theorem B5873741 : Blo 1738570 5873741 := bstep (se 3 (by rfl) ⟨1101326, by rfl⟩ : syracuseStep 5873741 = 2202653) B2202653
theorem B3301489 : Blo 1738570 3301489 := bstep (se 2 (by rfl) ⟨1238058, by rfl⟩ : syracuseStep 3301489 = 2476117) B2476117
theorem B14868593 : Blo 1738570 14868593 := bstep (se 2 (by rfl) ⟨5575722, by rfl⟩ : syracuseStep 14868593 = 11151445) B11151445
theorem B5873795 : Blo 1738570 5873795 := bstep (se 1 (by rfl) ⟨4405346, by rfl⟩ : syracuseStep 5873795 = 8810693) B8810693
theorem B23797901 : Blo 1738570 23797901 := bstep (se 3 (by rfl) ⟨4462106, by rfl⟩ : syracuseStep 23797901 = 8924213) B8924213
theorem B1982611 : Blo 1738570 1982611 := bstep (se 1 (by rfl) ⟨1486958, by rfl⟩ : syracuseStep 1982611 = 2973917) B2973917
theorem B1958035 : Blo 1738570 1958035 := bstep (se 1 (by rfl) ⟨1468526, by rfl⟩ : syracuseStep 1958035 = 2937053) B2937053
theorem B9404579 : Blo 1738570 9404579 := bstep (se 1 (by rfl) ⟨7053434, by rfl⟩ : syracuseStep 9404579 = 14106869) B14106869
theorem B11141297 : Blo 1738570 11141297 := bstep (se 2 (by rfl) ⟨4177986, by rfl⟩ : syracuseStep 11141297 = 8355973) B8355973
theorem B3915953 : Blo 1738570 3915953 := bstep (se 2 (by rfl) ⟨1468482, by rfl⟩ : syracuseStep 3915953 = 2936965) B2936965
theorem B3915971 : Blo 1738570 3915971 := bstep (se 1 (by rfl) ⟨2936978, by rfl⟩ : syracuseStep 3915971 = 5873957) B5873957
theorem B29712581 : Blo 1738570 29712581 := bstep (se 4 (by rfl) ⟨2785554, by rfl⟩ : syracuseStep 29712581 = 5571109) B5571109
theorem B1982675 : Blo 1738570 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B9904355 : Blo 1738570 9904355 := bstep (se 1 (by rfl) ⟨7428266, by rfl⟩ : syracuseStep 9904355 = 14856533) B14856533
theorem B14860529 : Blo 1738570 14860529 := bstep (se 2 (by rfl) ⟨5572698, by rfl⟩ : syracuseStep 14860529 = 11145397) B11145397
theorem B4956461 : Blo 1738570 4956461 := bstep (se 3 (by rfl) ⟨929336, by rfl⟩ : syracuseStep 4956461 = 1858673) B1858673
theorem B5570957 : Blo 1738570 5570957 := bstep (se 3 (by rfl) ⟨1044554, by rfl⟩ : syracuseStep 5570957 = 2089109) B2089109
theorem B5874065 : Blo 1738570 5874065 := bstep (se 2 (by rfl) ⟨2202774, by rfl⟩ : syracuseStep 5874065 = 4405549) B4405549
theorem B6029731 : Blo 1738570 6029731 := bstep (se 1 (by rfl) ⟨4522298, by rfl⟩ : syracuseStep 6029731 = 9044597) B9044597
theorem B3916241 : Blo 1738570 3916241 := bstep (se 2 (by rfl) ⟨1468590, by rfl⟩ : syracuseStep 3916241 = 2937181) B2937181
theorem B5022179 : Blo 1738570 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3916259 : Blo 1738570 3916259 := bstep (se 1 (by rfl) ⟨2937194, by rfl⟩ : syracuseStep 3916259 = 5874389) B5874389
theorem B2785811 : Blo 1738570 2785811 := bstep (se 1 (by rfl) ⟨2089358, by rfl⟩ : syracuseStep 2785811 = 4178717) B4178717
theorem B22290997 : Blo 1738570 22290997 := bstep (se 5 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 22290997 = 2089781) B2089781
theorem B4702787 : Blo 1738570 4702787 := bstep (se 1 (by rfl) ⟨3527090, by rfl⟩ : syracuseStep 4702787 = 7054181) B7054181
theorem B2785889 : Blo 1738570 2785889 := bstep (se 2 (by rfl) ⟨1044708, by rfl⟩ : syracuseStep 2785889 = 2089417) B2089417
theorem B5292803 : Blo 1738570 5292803 := bstep (se 1 (by rfl) ⟨3969602, by rfl⟩ : syracuseStep 5292803 = 7939205) B7939205
theorem B2786113 : Blo 1738570 2786113 := bstep (se 2 (by rfl) ⟨1044792, by rfl⟩ : syracuseStep 2786113 = 2089585) B2089585
theorem B21168965 : Blo 1738570 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B1811395 : Blo 1738570 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B6603875 : Blo 1738570 6603875 := bstep (se 1 (by rfl) ⟨4952906, by rfl⟩ : syracuseStep 6603875 = 9905813) B9905813
theorem B1983587 : Blo 1738570 1983587 := bstep (se 1 (by rfl) ⟨1487690, by rfl⟩ : syracuseStep 1983587 = 2975381) B2975381
theorem B6603889 : Blo 1738570 6603889 := bstep (se 2 (by rfl) ⟨2476458, by rfl⟩ : syracuseStep 6603889 = 4952917) B4952917
theorem B9405553 : Blo 1738570 9405553 := bstep (se 2 (by rfl) ⟨3527082, by rfl⟩ : syracuseStep 9405553 = 7054165) B7054165
theorem B37618829 : Blo 1738570 37618829 := bstep (se 3 (by rfl) ⟨7053530, by rfl⟩ : syracuseStep 37618829 = 14107061) B14107061
theorem B3302545 : Blo 1738570 3302545 := bstep (se 2 (by rfl) ⟨1238454, by rfl⟩ : syracuseStep 3302545 = 2476909) B2476909
theorem B2933921 : Blo 1738570 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B4179217 : Blo 1738570 4179217 := bstep (se 2 (by rfl) ⟨1567206, by rfl⟩ : syracuseStep 4179217 = 3134413) B3134413
theorem B2934049 : Blo 1738570 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B2090291 : Blo 1738570 2090291 := bstep (se 1 (by rfl) ⟨1567718, by rfl⟩ : syracuseStep 2090291 = 3135437) B3135437
theorem B2934083 : Blo 1738570 2934083 := bstep (se 1 (by rfl) ⟨2200562, by rfl⟩ : syracuseStep 2934083 = 4401125) B4401125
theorem B10585457 : Blo 1738570 10585457 := bstep (se 2 (by rfl) ⟨3969546, by rfl⟩ : syracuseStep 10585457 = 7939093) B7939093
theorem B6268337 : Blo 1738570 6268337 := bstep (se 2 (by rfl) ⟨2350626, by rfl⟩ : syracuseStep 6268337 = 4701253) B4701253
theorem B2934211 : Blo 1738570 2934211 := bstep (se 1 (by rfl) ⟨2200658, by rfl⟩ : syracuseStep 2934211 = 4401317) B4401317
theorem B3302947 : Blo 1738570 3302947 := bstep (se 1 (by rfl) ⟨2477210, by rfl⟩ : syracuseStep 3302947 = 4954421) B4954421
theorem B7054897 : Blo 1738570 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B19809845 : Blo 1738570 19809845 := bstep (se 5 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 19809845 = 1857173) B1857173
theorem B2934353 : Blo 1738570 2934353 := bstep (se 2 (by rfl) ⟨1100382, by rfl⟩ : syracuseStep 2934353 = 2200765) B2200765
theorem B3302993 : Blo 1738570 3302993 := bstep (se 2 (by rfl) ⟨1238622, by rfl⟩ : syracuseStep 3302993 = 2477245) B2477245
theorem B4703825 : Blo 1738570 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B7431821 : Blo 1738570 7431821 := bstep (se 3 (by rfl) ⟨1393466, by rfl⟩ : syracuseStep 7431821 = 2786933) B2786933
theorem B2934481 : Blo 1738570 2934481 := bstep (se 2 (by rfl) ⟨1100430, by rfl⟩ : syracuseStep 2934481 = 2200861) B2200861
theorem B7055075 : Blo 1738570 7055075 := bstep (se 1 (by rfl) ⟨5291306, by rfl⟩ : syracuseStep 7055075 = 10582613) B10582613
theorem B2934515 : Blo 1738570 2934515 := bstep (se 1 (by rfl) ⟨2200886, by rfl⟩ : syracuseStep 2934515 = 4401773) B4401773
theorem B4400963 : Blo 1738570 4400963 := bstep (se 1 (by rfl) ⟨3300722, by rfl⟩ : syracuseStep 4400963 = 6601445) B6601445
theorem B1738579 : Blo 1738570 1738579 := bstep (se 1 (by rfl) ⟨1303934, by rfl⟩ : syracuseStep 1738579 = 2607869) B2607869
theorem B1738595 : Blo 1738570 1738595 := bstep (se 1 (by rfl) ⟨1303946, by rfl⟩ : syracuseStep 1738595 = 2607893) B2607893
theorem B7055203 : Blo 1738570 7055203 := bstep (se 1 (by rfl) ⟨5291402, by rfl⟩ : syracuseStep 7055203 = 10582805) B10582805
theorem B3303281 : Blo 1738570 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1738611 : Blo 1738570 1738611 := bstep (se 1 (by rfl) ⟨1303958, by rfl⟩ : syracuseStep 1738611 = 2607917) B2607917
theorem B2934643 : Blo 1738570 2934643 := bstep (se 1 (by rfl) ⟨2200982, by rfl⟩ : syracuseStep 2934643 = 4401965) B4401965
theorem B1738627 : Blo 1738570 1738627 := bstep (se 1 (by rfl) ⟨1303970, by rfl⟩ : syracuseStep 1738627 = 2607941) B2607941
theorem B1738643 : Blo 1738570 1738643 := bstep (se 1 (by rfl) ⟨1303982, by rfl⟩ : syracuseStep 1738643 = 2607965) B2607965
theorem B1738659 : Blo 1738570 1738659 := bstep (se 1 (by rfl) ⟨1303994, by rfl⟩ : syracuseStep 1738659 = 2607989) B2607989
theorem B1738675 : Blo 1738570 1738675 := bstep (se 1 (by rfl) ⟨1304006, by rfl⟩ : syracuseStep 1738675 = 2608013) B2608013
theorem B1738691 : Blo 1738570 1738691 := bstep (se 1 (by rfl) ⟨1304018, by rfl⟩ : syracuseStep 1738691 = 2608037) B2608037
theorem B1738707 : Blo 1738570 1738707 := bstep (se 1 (by rfl) ⟨1304030, by rfl⟩ : syracuseStep 1738707 = 2608061) B2608061
theorem B1738723 : Blo 1738570 1738723 := bstep (se 1 (by rfl) ⟨1304042, by rfl⟩ : syracuseStep 1738723 = 2608085) B2608085
theorem B2476003 : Blo 1738570 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B1738739 : Blo 1738570 1738739 := bstep (se 1 (by rfl) ⟨1304054, by rfl⟩ : syracuseStep 1738739 = 2608109) B2608109
theorem B2934785 : Blo 1738570 2934785 := bstep (se 2 (by rfl) ⟨1100544, by rfl⟩ : syracuseStep 2934785 = 2201089) B2201089
theorem B4401155 : Blo 1738570 4401155 := bstep (se 1 (by rfl) ⟨3300866, by rfl⟩ : syracuseStep 4401155 = 6601733) B6601733
theorem B1738755 : Blo 1738570 1738755 := bstep (se 1 (by rfl) ⟨1304066, by rfl⟩ : syracuseStep 1738755 = 2608133) B2608133
theorem B1738771 : Blo 1738570 1738771 := bstep (se 1 (by rfl) ⟨1304078, by rfl⟩ : syracuseStep 1738771 = 2608157) B2608157
theorem B1738787 : Blo 1738570 1738787 := bstep (se 1 (by rfl) ⟨1304090, by rfl⟩ : syracuseStep 1738787 = 2608181) B2608181
theorem B1738803 : Blo 1738570 1738803 := bstep (se 1 (by rfl) ⟨1304102, by rfl⟩ : syracuseStep 1738803 = 2608205) B2608205
theorem B75221045 : Blo 1738570 75221045 := bstep (se 5 (by rfl) ⟨3525986, by rfl⟩ : syracuseStep 75221045 = 7051973) B7051973
theorem B1738819 : Blo 1738570 1738819 := bstep (se 1 (by rfl) ⟨1304114, by rfl⟩ : syracuseStep 1738819 = 2608229) B2608229
theorem B9906245 : Blo 1738570 9906245 := bstep (se 4 (by rfl) ⟨928710, by rfl⟩ : syracuseStep 9906245 = 1857421) B1857421
theorem B1738835 : Blo 1738570 1738835 := bstep (se 1 (by rfl) ⟨1304126, by rfl⟩ : syracuseStep 1738835 = 2608253) B2608253
theorem B1738851 : Blo 1738570 1738851 := bstep (se 1 (by rfl) ⟨1304138, by rfl⟩ : syracuseStep 1738851 = 2608277) B2608277
theorem B1738867 : Blo 1738570 1738867 := bstep (se 1 (by rfl) ⟨1304150, by rfl⟩ : syracuseStep 1738867 = 2608301) B2608301
theorem B2934913 : Blo 1738570 2934913 := bstep (se 2 (by rfl) ⟨1100592, by rfl⟩ : syracuseStep 2934913 = 2201185) B2201185
theorem B1738883 : Blo 1738570 1738883 := bstep (se 1 (by rfl) ⟨1304162, by rfl⟩ : syracuseStep 1738883 = 2608325) B2608325
theorem B5572739 : Blo 1738570 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B1738899 : Blo 1738570 1738899 := bstep (se 1 (by rfl) ⟨1304174, by rfl⟩ : syracuseStep 1738899 = 2608349) B2608349
theorem B1738915 : Blo 1738570 1738915 := bstep (se 1 (by rfl) ⟨1304186, by rfl⟩ : syracuseStep 1738915 = 2608373) B2608373
theorem B2934947 : Blo 1738570 2934947 := bstep (se 1 (by rfl) ⟨2201210, by rfl⟩ : syracuseStep 2934947 = 4402421) B4402421
theorem B5867693 : Blo 1738570 5867693 := bstep (se 3 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 5867693 = 2200385) B2200385
theorem B1738931 : Blo 1738570 1738931 := bstep (se 1 (by rfl) ⟨1304198, by rfl⟩ : syracuseStep 1738931 = 2608397) B2608397
theorem B3713219 : Blo 1738570 3713219 := bstep (se 1 (by rfl) ⟨2784914, by rfl⟩ : syracuseStep 3713219 = 5569829) B5569829
theorem B1738947 : Blo 1738570 1738947 := bstep (se 1 (by rfl) ⟨1304210, by rfl⟩ : syracuseStep 1738947 = 2608421) B2608421
theorem B1738963 : Blo 1738570 1738963 := bstep (se 1 (by rfl) ⟨1304222, by rfl⟩ : syracuseStep 1738963 = 2608445) B2608445
theorem B5867747 : Blo 1738570 5867747 := bstep (se 1 (by rfl) ⟨4400810, by rfl⟩ : syracuseStep 5867747 = 8801621) B8801621
theorem B1738979 : Blo 1738570 1738979 := bstep (se 1 (by rfl) ⟨1304234, by rfl⟩ : syracuseStep 1738979 = 2608469) B2608469
theorem B1738995 : Blo 1738570 1738995 := bstep (se 1 (by rfl) ⟨1304246, by rfl⟩ : syracuseStep 1738995 = 2608493) B2608493
theorem B1739011 : Blo 1738570 1739011 := bstep (se 1 (by rfl) ⟨1304258, by rfl⟩ : syracuseStep 1739011 = 2608517) B2608517
theorem B1739027 : Blo 1738570 1739027 := bstep (se 1 (by rfl) ⟨1304270, by rfl⟩ : syracuseStep 1739027 = 2608541) B2608541
theorem B1739043 : Blo 1738570 1739043 := bstep (se 1 (by rfl) ⟨1304282, by rfl⟩ : syracuseStep 1739043 = 2608565) B2608565
theorem B2935075 : Blo 1738570 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B1739059 : Blo 1738570 1739059 := bstep (se 1 (by rfl) ⟨1304294, by rfl⟩ : syracuseStep 1739059 = 2608589) B2608589
theorem B1739075 : Blo 1738570 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B1739091 : Blo 1738570 1739091 := bstep (se 1 (by rfl) ⟨1304318, by rfl⟩ : syracuseStep 1739091 = 2608637) B2608637
theorem B1739107 : Blo 1738570 1739107 := bstep (se 1 (by rfl) ⟨1304330, by rfl⟩ : syracuseStep 1739107 = 2608661) B2608661
theorem B1739123 : Blo 1738570 1739123 := bstep (se 1 (by rfl) ⟨1304342, by rfl⟩ : syracuseStep 1739123 = 2608685) B2608685
theorem B1739139 : Blo 1738570 1739139 := bstep (se 1 (by rfl) ⟨1304354, by rfl⟩ : syracuseStep 1739139 = 2608709) B2608709
theorem B1739155 : Blo 1738570 1739155 := bstep (se 1 (by rfl) ⟨1304366, by rfl⟩ : syracuseStep 1739155 = 2608733) B2608733
theorem B1739171 : Blo 1738570 1739171 := bstep (se 1 (by rfl) ⟨1304378, by rfl⟩ : syracuseStep 1739171 = 2608757) B2608757
theorem B2935217 : Blo 1738570 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B1739187 : Blo 1738570 1739187 := bstep (se 1 (by rfl) ⟨1304390, by rfl⟩ : syracuseStep 1739187 = 2608781) B2608781
theorem B1739203 : Blo 1738570 1739203 := bstep (se 1 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 1739203 = 2608805) B2608805
theorem B1739219 : Blo 1738570 1739219 := bstep (se 1 (by rfl) ⟨1304414, by rfl⟩ : syracuseStep 1739219 = 2608829) B2608829
theorem B15862243 : Blo 1738570 15862243 := bstep (se 1 (by rfl) ⟨11896682, by rfl⟩ : syracuseStep 15862243 = 23793365) B23793365
theorem B1739235 : Blo 1738570 1739235 := bstep (se 1 (by rfl) ⟨1304426, by rfl⟩ : syracuseStep 1739235 = 2608853) B2608853
theorem B4237795 : Blo 1738570 4237795 := bstep (se 1 (by rfl) ⟨3178346, by rfl⟩ : syracuseStep 4237795 = 6356693) B6356693
theorem B5868017 : Blo 1738570 5868017 := bstep (se 2 (by rfl) ⟨2200506, by rfl⟩ : syracuseStep 5868017 = 4401013) B4401013
theorem B1739251 : Blo 1738570 1739251 := bstep (se 1 (by rfl) ⟨1304438, by rfl⟩ : syracuseStep 1739251 = 2608877) B2608877
theorem B1739267 : Blo 1738570 1739267 := bstep (se 1 (by rfl) ⟨1304450, by rfl⟩ : syracuseStep 1739267 = 2608901) B2608901
theorem B3525137 : Blo 1738570 3525137 := bstep (se 2 (by rfl) ⟨1321926, by rfl⟩ : syracuseStep 3525137 = 2643853) B2643853
theorem B1739283 : Blo 1738570 1739283 := bstep (se 1 (by rfl) ⟨1304462, by rfl⟩ : syracuseStep 1739283 = 2608925) B2608925
theorem B1739299 : Blo 1738570 1739299 := bstep (se 1 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 1739299 = 2608949) B2608949
theorem B6605347 : Blo 1738570 6605347 := bstep (se 1 (by rfl) ⟨4954010, by rfl⟩ : syracuseStep 6605347 = 9908021) B9908021
theorem B2787875 : Blo 1738570 2787875 := bstep (se 1 (by rfl) ⟨2090906, by rfl⟩ : syracuseStep 2787875 = 4181813) B4181813
theorem B2935345 : Blo 1738570 2935345 := bstep (se 2 (by rfl) ⟨1100754, by rfl⟩ : syracuseStep 2935345 = 2201509) B2201509
theorem B1739315 : Blo 1738570 1739315 := bstep (se 1 (by rfl) ⟨1304486, by rfl⟩ : syracuseStep 1739315 = 2608973) B2608973
theorem B1739331 : Blo 1738570 1739331 := bstep (se 1 (by rfl) ⟨1304498, by rfl⟩ : syracuseStep 1739331 = 2608997) B2608997
theorem B3304003 : Blo 1738570 3304003 := bstep (se 1 (by rfl) ⟨2478002, by rfl⟩ : syracuseStep 3304003 = 4956005) B4956005
theorem B11143757 : Blo 1738570 11143757 := bstep (se 3 (by rfl) ⟨2089454, by rfl⟩ : syracuseStep 11143757 = 4178909) B4178909
theorem B1739347 : Blo 1738570 1739347 := bstep (se 1 (by rfl) ⟨1304510, by rfl⟩ : syracuseStep 1739347 = 2609021) B2609021
theorem B2935379 : Blo 1738570 2935379 := bstep (se 1 (by rfl) ⟨2201534, by rfl⟩ : syracuseStep 2935379 = 4403069) B4403069
theorem B1739363 : Blo 1738570 1739363 := bstep (se 1 (by rfl) ⟨1304522, by rfl⟩ : syracuseStep 1739363 = 2609045) B2609045
theorem B8809073 : Blo 1738570 8809073 := bstep (se 2 (by rfl) ⟨3303402, by rfl⟩ : syracuseStep 8809073 = 6606805) B6606805
theorem B1739379 : Blo 1738570 1739379 := bstep (se 1 (by rfl) ⟨1304534, by rfl⟩ : syracuseStep 1739379 = 2609069) B2609069
theorem B1739395 : Blo 1738570 1739395 := bstep (se 1 (by rfl) ⟨1304546, by rfl⟩ : syracuseStep 1739395 = 2609093) B2609093
theorem B3713681 : Blo 1738570 3713681 := bstep (se 2 (by rfl) ⟨1392630, by rfl⟩ : syracuseStep 3713681 = 2785261) B2785261
theorem B1739411 : Blo 1738570 1739411 := bstep (se 1 (by rfl) ⟨1304558, by rfl⟩ : syracuseStep 1739411 = 2609117) B2609117
theorem B1739427 : Blo 1738570 1739427 := bstep (se 1 (by rfl) ⟨1304570, by rfl⟩ : syracuseStep 1739427 = 2609141) B2609141
theorem B1739443 : Blo 1738570 1739443 := bstep (se 1 (by rfl) ⟨1304582, by rfl⟩ : syracuseStep 1739443 = 2609165) B2609165
theorem B1739459 : Blo 1738570 1739459 := bstep (se 1 (by rfl) ⟨1304594, by rfl⟩ : syracuseStep 1739459 = 2609189) B2609189
theorem B1739475 : Blo 1738570 1739475 := bstep (se 1 (by rfl) ⟨1304606, by rfl⟩ : syracuseStep 1739475 = 2609213) B2609213
theorem B2935507 : Blo 1738570 2935507 := bstep (se 1 (by rfl) ⟨2201630, by rfl⟩ : syracuseStep 2935507 = 4403261) B4403261
theorem B75270869 : Blo 1738570 75270869 := bstep (se 7 (by rfl) ⟨882080, by rfl⟩ : syracuseStep 75270869 = 1764161) B1764161
theorem B1739491 : Blo 1738570 1739491 := bstep (se 1 (by rfl) ⟨1304618, by rfl⟩ : syracuseStep 1739491 = 2609237) B2609237
theorem B2607857 : Blo 1738570 2607857 := bstep (se 2 (by rfl) ⟨977946, by rfl⟩ : syracuseStep 2607857 = 1955893) B1955893
theorem B1739507 : Blo 1738570 1739507 := bstep (se 1 (by rfl) ⟨1304630, by rfl⟩ : syracuseStep 1739507 = 2609261) B2609261
theorem B2607875 : Blo 1738570 2607875 := bstep (se 1 (by rfl) ⟨1955906, by rfl⟩ : syracuseStep 2607875 = 3911813) B3911813
theorem B1739523 : Blo 1738570 1739523 := bstep (se 1 (by rfl) ⟨1304642, by rfl⟩ : syracuseStep 1739523 = 2609285) B2609285
theorem B1739539 : Blo 1738570 1739539 := bstep (se 1 (by rfl) ⟨1304654, by rfl⟩ : syracuseStep 1739539 = 2609309) B2609309
theorem B2607905 : Blo 1738570 2607905 := bstep (se 2 (by rfl) ⟨977964, by rfl⟩ : syracuseStep 2607905 = 1955929) B1955929
theorem B1739555 : Blo 1738570 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B2607923 : Blo 1738570 2607923 := bstep (se 1 (by rfl) ⟨1955942, by rfl⟩ : syracuseStep 2607923 = 3911885) B3911885
theorem B1739571 : Blo 1738570 1739571 := bstep (se 1 (by rfl) ⟨1304678, by rfl⟩ : syracuseStep 1739571 = 2609357) B2609357
theorem B1739587 : Blo 1738570 1739587 := bstep (se 1 (by rfl) ⟨1304690, by rfl⟩ : syracuseStep 1739587 = 2609381) B2609381
theorem B2607953 : Blo 1738570 2607953 := bstep (se 2 (by rfl) ⟨977982, by rfl⟩ : syracuseStep 2607953 = 1955965) B1955965
theorem B1739603 : Blo 1738570 1739603 := bstep (se 1 (by rfl) ⟨1304702, by rfl⟩ : syracuseStep 1739603 = 2609405) B2609405
theorem B2935649 : Blo 1738570 2935649 := bstep (se 2 (by rfl) ⟨1100868, by rfl⟩ : syracuseStep 2935649 = 2201737) B2201737
theorem B2607971 : Blo 1738570 2607971 := bstep (se 1 (by rfl) ⟨1955978, by rfl⟩ : syracuseStep 2607971 = 3911957) B3911957
theorem B1739619 : Blo 1738570 1739619 := bstep (se 1 (by rfl) ⟨1304714, by rfl⟩ : syracuseStep 1739619 = 2609429) B2609429
theorem B1739635 : Blo 1738570 1739635 := bstep (se 1 (by rfl) ⟨1304726, by rfl⟩ : syracuseStep 1739635 = 2609453) B2609453
theorem B2608001 : Blo 1738570 2608001 := bstep (se 2 (by rfl) ⟨978000, by rfl⟩ : syracuseStep 2608001 = 1956001) B1956001
theorem B1739651 : Blo 1738570 1739651 := bstep (se 1 (by rfl) ⟨1304738, by rfl⟩ : syracuseStep 1739651 = 2609477) B2609477
theorem B2608019 : Blo 1738570 2608019 := bstep (se 1 (by rfl) ⟨1956014, by rfl⟩ : syracuseStep 2608019 = 3912029) B3912029
theorem B1739667 : Blo 1738570 1739667 := bstep (se 1 (by rfl) ⟨1304750, by rfl⟩ : syracuseStep 1739667 = 2609501) B2609501
theorem B1739683 : Blo 1738570 1739683 := bstep (se 1 (by rfl) ⟨1304762, by rfl⟩ : syracuseStep 1739683 = 2609525) B2609525
theorem B2608049 : Blo 1738570 2608049 := bstep (se 2 (by rfl) ⟨978018, by rfl⟩ : syracuseStep 2608049 = 1956037) B1956037
theorem B4402097 : Blo 1738570 4402097 := bstep (se 2 (by rfl) ⟨1650786, by rfl⟩ : syracuseStep 4402097 = 3301573) B3301573
theorem B1739699 : Blo 1738570 1739699 := bstep (se 1 (by rfl) ⟨1304774, by rfl⟩ : syracuseStep 1739699 = 2609549) B2609549
theorem B1764275 : Blo 1738570 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B2608067 : Blo 1738570 2608067 := bstep (se 1 (by rfl) ⟨1956050, by rfl⟩ : syracuseStep 2608067 = 3912101) B3912101
theorem B1739715 : Blo 1738570 1739715 := bstep (se 1 (by rfl) ⟨1304786, by rfl⟩ : syracuseStep 1739715 = 2609573) B2609573
theorem B1739731 : Blo 1738570 1739731 := bstep (se 1 (by rfl) ⟨1304798, by rfl⟩ : syracuseStep 1739731 = 2609597) B2609597
theorem B2608097 : Blo 1738570 2608097 := bstep (se 2 (by rfl) ⟨978036, by rfl⟩ : syracuseStep 2608097 = 1956073) B1956073
theorem B2935777 : Blo 1738570 2935777 := bstep (se 2 (by rfl) ⟨1100916, by rfl⟩ : syracuseStep 2935777 = 2201833) B2201833
theorem B4402147 : Blo 1738570 4402147 := bstep (se 1 (by rfl) ⟨3301610, by rfl⟩ : syracuseStep 4402147 = 6603221) B6603221
theorem B1739747 : Blo 1738570 1739747 := bstep (se 1 (by rfl) ⟨1304810, by rfl⟩ : syracuseStep 1739747 = 2609621) B2609621
theorem B2608115 : Blo 1738570 2608115 := bstep (se 1 (by rfl) ⟨1956086, by rfl⟩ : syracuseStep 2608115 = 3912173) B3912173
theorem B1739763 : Blo 1738570 1739763 := bstep (se 1 (by rfl) ⟨1304822, by rfl⟩ : syracuseStep 1739763 = 2609645) B2609645
theorem B2935811 : Blo 1738570 2935811 := bstep (se 1 (by rfl) ⟨2201858, by rfl⟩ : syracuseStep 2935811 = 4403717) B4403717
theorem B1739779 : Blo 1738570 1739779 := bstep (se 1 (by rfl) ⟨1304834, by rfl⟩ : syracuseStep 1739779 = 2609669) B2609669
theorem B5868557 : Blo 1738570 5868557 := bstep (se 3 (by rfl) ⟨1100354, by rfl⟩ : syracuseStep 5868557 = 2200709) B2200709
theorem B2608145 : Blo 1738570 2608145 := bstep (se 2 (by rfl) ⟨978054, by rfl⟩ : syracuseStep 2608145 = 1956109) B1956109
theorem B1739795 : Blo 1738570 1739795 := bstep (se 1 (by rfl) ⟨1304846, by rfl⟩ : syracuseStep 1739795 = 2609693) B2609693
theorem B2608163 : Blo 1738570 2608163 := bstep (se 1 (by rfl) ⟨1956122, by rfl⟩ : syracuseStep 2608163 = 3912245) B3912245
theorem B1739811 : Blo 1738570 1739811 := bstep (se 1 (by rfl) ⟨1304858, by rfl⟩ : syracuseStep 1739811 = 2609717) B2609717
theorem B1739827 : Blo 1738570 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B2608193 : Blo 1738570 2608193 := bstep (se 2 (by rfl) ⟨978072, by rfl⟩ : syracuseStep 2608193 = 1956145) B1956145
theorem B5868611 : Blo 1738570 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B1739843 : Blo 1738570 1739843 := bstep (se 1 (by rfl) ⟨1304882, by rfl⟩ : syracuseStep 1739843 = 2609765) B2609765
theorem B2477137 : Blo 1738570 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B2608211 : Blo 1738570 2608211 := bstep (se 1 (by rfl) ⟨1956158, by rfl⟩ : syracuseStep 2608211 = 3912317) B3912317
theorem B1739859 : Blo 1738570 1739859 := bstep (se 1 (by rfl) ⟨1304894, by rfl⟩ : syracuseStep 1739859 = 2609789) B2609789
theorem B1739875 : Blo 1738570 1739875 := bstep (se 1 (by rfl) ⟨1304906, by rfl⟩ : syracuseStep 1739875 = 2609813) B2609813
theorem B2608241 : Blo 1738570 2608241 := bstep (se 2 (by rfl) ⟨978090, by rfl⟩ : syracuseStep 2608241 = 1956181) B1956181
theorem B4402289 : Blo 1738570 4402289 := bstep (se 2 (by rfl) ⟨1650858, by rfl⟩ : syracuseStep 4402289 = 3301717) B3301717
theorem B1739891 : Blo 1738570 1739891 := bstep (se 1 (by rfl) ⟨1304918, by rfl⟩ : syracuseStep 1739891 = 2609837) B2609837
theorem B2608259 : Blo 1738570 2608259 := bstep (se 1 (by rfl) ⟨1956194, by rfl⟩ : syracuseStep 2608259 = 3912389) B3912389
theorem B2935939 : Blo 1738570 2935939 := bstep (se 1 (by rfl) ⟨2201954, by rfl⟩ : syracuseStep 2935939 = 4403909) B4403909
theorem B1739907 : Blo 1738570 1739907 := bstep (se 1 (by rfl) ⟨1304930, by rfl⟩ : syracuseStep 1739907 = 2609861) B2609861
theorem B1739923 : Blo 1738570 1739923 := bstep (se 1 (by rfl) ⟨1304942, by rfl⟩ : syracuseStep 1739923 = 2609885) B2609885
theorem B2608289 : Blo 1738570 2608289 := bstep (se 2 (by rfl) ⟨978108, by rfl⟩ : syracuseStep 2608289 = 1956217) B1956217
theorem B1739939 : Blo 1738570 1739939 := bstep (se 1 (by rfl) ⟨1304954, by rfl⟩ : syracuseStep 1739939 = 2609909) B2609909
theorem B2477233 : Blo 1738570 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B2608307 : Blo 1738570 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B1739955 : Blo 1738570 1739955 := bstep (se 1 (by rfl) ⟨1304966, by rfl⟩ : syracuseStep 1739955 = 2609933) B2609933
theorem B3968195 : Blo 1738570 3968195 := bstep (se 1 (by rfl) ⟨2976146, by rfl⟩ : syracuseStep 3968195 = 5952293) B5952293
theorem B1739971 : Blo 1738570 1739971 := bstep (se 1 (by rfl) ⟨1304978, by rfl⟩ : syracuseStep 1739971 = 2609957) B2609957
theorem B2608337 : Blo 1738570 2608337 := bstep (se 2 (by rfl) ⟨978126, by rfl⟩ : syracuseStep 2608337 = 1956253) B1956253
theorem B1739987 : Blo 1738570 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B2608355 : Blo 1738570 2608355 := bstep (se 1 (by rfl) ⟨1956266, by rfl⟩ : syracuseStep 2608355 = 3912533) B3912533
theorem B10726627 : Blo 1738570 10726627 := bstep (se 1 (by rfl) ⟨8044970, by rfl⟩ : syracuseStep 10726627 = 16089941) B16089941
theorem B1740003 : Blo 1738570 1740003 := bstep (se 1 (by rfl) ⟨1305002, by rfl⟩ : syracuseStep 1740003 = 2610005) B2610005
theorem B4951277 : Blo 1738570 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B1740019 : Blo 1738570 1740019 := bstep (se 1 (by rfl) ⟨1305014, by rfl⟩ : syracuseStep 1740019 = 2610029) B2610029
theorem B2608385 : Blo 1738570 2608385 := bstep (se 2 (by rfl) ⟨978144, by rfl⟩ : syracuseStep 2608385 = 1956289) B1956289
theorem B1740035 : Blo 1738570 1740035 := bstep (se 1 (by rfl) ⟨1305026, by rfl⟩ : syracuseStep 1740035 = 2610053) B2610053
theorem B2936081 : Blo 1738570 2936081 := bstep (se 2 (by rfl) ⟨1101030, by rfl⟩ : syracuseStep 2936081 = 2202061) B2202061
theorem B2608403 : Blo 1738570 2608403 := bstep (se 1 (by rfl) ⟨1956302, by rfl⟩ : syracuseStep 2608403 = 3912605) B3912605
theorem B1740051 : Blo 1738570 1740051 := bstep (se 1 (by rfl) ⟨1305038, by rfl⟩ : syracuseStep 1740051 = 2610077) B2610077
theorem B1740067 : Blo 1738570 1740067 := bstep (se 1 (by rfl) ⟨1305050, by rfl⟩ : syracuseStep 1740067 = 2610101) B2610101
theorem B2608433 : Blo 1738570 2608433 := bstep (se 2 (by rfl) ⟨978162, by rfl⟩ : syracuseStep 2608433 = 1956325) B1956325
theorem B1740083 : Blo 1738570 1740083 := bstep (se 1 (by rfl) ⟨1305062, by rfl⟩ : syracuseStep 1740083 = 2610125) B2610125
theorem B2608451 : Blo 1738570 2608451 := bstep (se 1 (by rfl) ⟨1956338, by rfl⟩ : syracuseStep 2608451 = 3912677) B3912677
theorem B1740099 : Blo 1738570 1740099 := bstep (se 1 (by rfl) ⟨1305074, by rfl⟩ : syracuseStep 1740099 = 2610149) B2610149
theorem B9407821 : Blo 1738570 9407821 := bstep (se 3 (by rfl) ⟨1763966, by rfl⟩ : syracuseStep 9407821 = 3527933) B3527933
theorem B5868881 : Blo 1738570 5868881 := bstep (se 2 (by rfl) ⟨2200830, by rfl⟩ : syracuseStep 5868881 = 4401661) B4401661
theorem B1740115 : Blo 1738570 1740115 := bstep (se 1 (by rfl) ⟨1305086, by rfl⟩ : syracuseStep 1740115 = 2610173) B2610173
theorem B2608481 : Blo 1738570 2608481 := bstep (se 2 (by rfl) ⟨978180, by rfl⟩ : syracuseStep 2608481 = 1956361) B1956361
theorem B1740131 : Blo 1738570 1740131 := bstep (se 1 (by rfl) ⟨1305098, by rfl⟩ : syracuseStep 1740131 = 2610197) B2610197
theorem B2608499 : Blo 1738570 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B1740147 : Blo 1738570 1740147 := bstep (se 1 (by rfl) ⟨1305110, by rfl⟩ : syracuseStep 1740147 = 2610221) B2610221
theorem B1740163 : Blo 1738570 1740163 := bstep (se 1 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 1740163 = 2610245) B2610245
theorem B2608529 : Blo 1738570 2608529 := bstep (se 2 (by rfl) ⟨978198, by rfl⟩ : syracuseStep 2608529 = 1956397) B1956397
theorem B2936209 : Blo 1738570 2936209 := bstep (se 2 (by rfl) ⟨1101078, by rfl⟩ : syracuseStep 2936209 = 2202157) B2202157
theorem B1740179 : Blo 1738570 1740179 := bstep (se 1 (by rfl) ⟨1305134, by rfl⟩ : syracuseStep 1740179 = 2610269) B2610269
theorem B4951459 : Blo 1738570 4951459 := bstep (se 1 (by rfl) ⟨3713594, by rfl⟩ : syracuseStep 4951459 = 7427189) B7427189
theorem B2608547 : Blo 1738570 2608547 := bstep (se 1 (by rfl) ⟨1956410, by rfl⟩ : syracuseStep 2608547 = 3912821) B3912821
theorem B1740195 : Blo 1738570 1740195 := bstep (se 1 (by rfl) ⟨1305146, by rfl⟩ : syracuseStep 1740195 = 2610293) B2610293
theorem B2936243 : Blo 1738570 2936243 := bstep (se 1 (by rfl) ⟨2202182, by rfl⟩ : syracuseStep 2936243 = 4404365) B4404365
theorem B1740211 : Blo 1738570 1740211 := bstep (se 1 (by rfl) ⟨1305158, by rfl⟩ : syracuseStep 1740211 = 2610317) B2610317
theorem B2608577 : Blo 1738570 2608577 := bstep (se 2 (by rfl) ⟨978216, by rfl⟩ : syracuseStep 2608577 = 1956433) B1956433
theorem B1740227 : Blo 1738570 1740227 := bstep (se 1 (by rfl) ⟨1305170, by rfl⟩ : syracuseStep 1740227 = 2610341) B2610341
theorem B4951505 : Blo 1738570 4951505 := bstep (se 2 (by rfl) ⟨1856814, by rfl⟩ : syracuseStep 4951505 = 3713629) B3713629
theorem B2608595 : Blo 1738570 2608595 := bstep (se 1 (by rfl) ⟨1956446, by rfl⟩ : syracuseStep 2608595 = 3912893) B3912893
theorem B1740243 : Blo 1738570 1740243 := bstep (se 1 (by rfl) ⟨1305182, by rfl⟩ : syracuseStep 1740243 = 2610365) B2610365
theorem B1740259 : Blo 1738570 1740259 := bstep (se 1 (by rfl) ⟨1305194, by rfl⟩ : syracuseStep 1740259 = 2610389) B2610389
theorem B2608625 : Blo 1738570 2608625 := bstep (se 2 (by rfl) ⟨978234, by rfl⟩ : syracuseStep 2608625 = 1956469) B1956469
theorem B1740275 : Blo 1738570 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B2608643 : Blo 1738570 2608643 := bstep (se 1 (by rfl) ⟨1956482, by rfl⟩ : syracuseStep 2608643 = 3912965) B3912965
theorem B1740291 : Blo 1738570 1740291 := bstep (se 1 (by rfl) ⟨1305218, by rfl⟩ : syracuseStep 1740291 = 2610437) B2610437
theorem B1740307 : Blo 1738570 1740307 := bstep (se 1 (by rfl) ⟨1305230, by rfl⟩ : syracuseStep 1740307 = 2610461) B2610461
theorem B2608673 : Blo 1738570 2608673 := bstep (se 2 (by rfl) ⟨978252, by rfl⟩ : syracuseStep 2608673 = 1956505) B1956505
theorem B1740323 : Blo 1738570 1740323 := bstep (se 1 (by rfl) ⟨1305242, by rfl⟩ : syracuseStep 1740323 = 2610485) B2610485
theorem B2608691 : Blo 1738570 2608691 := bstep (se 1 (by rfl) ⟨1956518, by rfl⟩ : syracuseStep 2608691 = 3913037) B3913037
theorem B2936371 : Blo 1738570 2936371 := bstep (se 1 (by rfl) ⟨2202278, by rfl⟩ : syracuseStep 2936371 = 4404557) B4404557
theorem B1740339 : Blo 1738570 1740339 := bstep (se 1 (by rfl) ⟨1305254, by rfl⟩ : syracuseStep 1740339 = 2610509) B2610509
theorem B1740355 : Blo 1738570 1740355 := bstep (se 1 (by rfl) ⟨1305266, by rfl⟩ : syracuseStep 1740355 = 2610533) B2610533
theorem B2608721 : Blo 1738570 2608721 := bstep (se 2 (by rfl) ⟨978270, by rfl⟩ : syracuseStep 2608721 = 1956541) B1956541
theorem B1740371 : Blo 1738570 1740371 := bstep (se 1 (by rfl) ⟨1305278, by rfl⟩ : syracuseStep 1740371 = 2610557) B2610557
theorem B2608739 : Blo 1738570 2608739 := bstep (se 1 (by rfl) ⟨1956554, by rfl⟩ : syracuseStep 2608739 = 3913109) B3913109
theorem B1740387 : Blo 1738570 1740387 := bstep (se 1 (by rfl) ⟨1305290, by rfl⟩ : syracuseStep 1740387 = 2610581) B2610581
theorem B1740403 : Blo 1738570 1740403 := bstep (se 1 (by rfl) ⟨1305302, by rfl⟩ : syracuseStep 1740403 = 2610605) B2610605
theorem B2608769 : Blo 1738570 2608769 := bstep (se 2 (by rfl) ⟨978288, by rfl⟩ : syracuseStep 2608769 = 1956577) B1956577
theorem B1740419 : Blo 1738570 1740419 := bstep (se 1 (by rfl) ⟨1305314, by rfl⟩ : syracuseStep 1740419 = 2610629) B2610629
theorem B2608787 : Blo 1738570 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B1740435 : Blo 1738570 1740435 := bstep (se 1 (by rfl) ⟨1305326, by rfl⟩ : syracuseStep 1740435 = 2610653) B2610653
theorem B2477729 : Blo 1738570 2477729 := bstep (se 2 (by rfl) ⟨929148, by rfl⟩ : syracuseStep 2477729 = 1858297) B1858297
theorem B1740451 : Blo 1738570 1740451 := bstep (se 1 (by rfl) ⟨1305338, by rfl⟩ : syracuseStep 1740451 = 2610677) B2610677
theorem B2608817 : Blo 1738570 2608817 := bstep (se 2 (by rfl) ⟨978306, by rfl⟩ : syracuseStep 2608817 = 1956613) B1956613
theorem B1740467 : Blo 1738570 1740467 := bstep (se 1 (by rfl) ⟨1305350, by rfl⟩ : syracuseStep 1740467 = 2610701) B2610701
theorem B2936513 : Blo 1738570 2936513 := bstep (se 2 (by rfl) ⟨1101192, by rfl⟩ : syracuseStep 2936513 = 2202385) B2202385
theorem B2608835 : Blo 1738570 2608835 := bstep (se 1 (by rfl) ⟨1956626, by rfl⟩ : syracuseStep 2608835 = 3913253) B3913253
theorem B1740483 : Blo 1738570 1740483 := bstep (se 1 (by rfl) ⟨1305362, by rfl⟩ : syracuseStep 1740483 = 2610725) B2610725
theorem B1740499 : Blo 1738570 1740499 := bstep (se 1 (by rfl) ⟨1305374, by rfl⟩ : syracuseStep 1740499 = 2610749) B2610749
theorem B2608865 : Blo 1738570 2608865 := bstep (se 2 (by rfl) ⟨978324, by rfl⟩ : syracuseStep 2608865 = 1956649) B1956649
theorem B1740515 : Blo 1738570 1740515 := bstep (se 1 (by rfl) ⟨1305386, by rfl⟩ : syracuseStep 1740515 = 2610773) B2610773
theorem B2608883 : Blo 1738570 2608883 := bstep (se 1 (by rfl) ⟨1956662, by rfl⟩ : syracuseStep 2608883 = 3913325) B3913325
theorem B1740531 : Blo 1738570 1740531 := bstep (se 1 (by rfl) ⟨1305398, by rfl⟩ : syracuseStep 1740531 = 2610797) B2610797
theorem B1740547 : Blo 1738570 1740547 := bstep (se 1 (by rfl) ⟨1305410, by rfl⟩ : syracuseStep 1740547 = 2610821) B2610821
theorem B2608913 : Blo 1738570 2608913 := bstep (se 2 (by rfl) ⟨978342, by rfl⟩ : syracuseStep 2608913 = 1956685) B1956685
theorem B47591189 : Blo 1738570 47591189 := bstep (se 6 (by rfl) ⟨1115418, by rfl⟩ : syracuseStep 47591189 = 2230837) B2230837
theorem B1740563 : Blo 1738570 1740563 := bstep (se 1 (by rfl) ⟨1305422, by rfl⟩ : syracuseStep 1740563 = 2610845) B2610845
theorem B2608931 : Blo 1738570 2608931 := bstep (se 1 (by rfl) ⟨1956698, by rfl⟩ : syracuseStep 2608931 = 3913397) B3913397
theorem B2608961 : Blo 1738570 2608961 := bstep (se 2 (by rfl) ⟨978360, by rfl⟩ : syracuseStep 2608961 = 1956721) B1956721
theorem B2936641 : Blo 1738570 2936641 := bstep (se 2 (by rfl) ⟨1101240, by rfl⟩ : syracuseStep 2936641 = 2202481) B2202481
theorem B2608979 : Blo 1738570 2608979 := bstep (se 1 (by rfl) ⟨1956734, by rfl⟩ : syracuseStep 2608979 = 3913469) B3913469
theorem B2936675 : Blo 1738570 2936675 := bstep (se 1 (by rfl) ⟨2202506, by rfl⟩ : syracuseStep 2936675 = 4405013) B4405013
theorem B5869421 : Blo 1738570 5869421 := bstep (se 3 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 5869421 = 2201033) B2201033
theorem B2609009 : Blo 1738570 2609009 := bstep (se 2 (by rfl) ⟨978378, by rfl⟩ : syracuseStep 2609009 = 1956757) B1956757
theorem B2609027 : Blo 1738570 2609027 := bstep (se 1 (by rfl) ⟨1956770, by rfl⟩ : syracuseStep 2609027 = 3913541) B3913541
theorem B5574545 : Blo 1738570 5574545 := bstep (se 2 (by rfl) ⟨2090454, by rfl⟩ : syracuseStep 5574545 = 4180909) B4180909
theorem B2609057 : Blo 1738570 2609057 := bstep (se 2 (by rfl) ⟨978396, by rfl⟩ : syracuseStep 2609057 = 1956793) B1956793
theorem B5869475 : Blo 1738570 5869475 := bstep (se 1 (by rfl) ⟨4402106, by rfl⟩ : syracuseStep 5869475 = 8804213) B8804213
theorem B3714979 : Blo 1738570 3714979 := bstep (se 1 (by rfl) ⟨2786234, by rfl⟩ : syracuseStep 3714979 = 5572469) B5572469
theorem B2609075 : Blo 1738570 2609075 := bstep (se 1 (by rfl) ⟨1956806, by rfl⟩ : syracuseStep 2609075 = 3913613) B3913613
theorem B5574595 : Blo 1738570 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B10579909 : Blo 1738570 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B2609105 : Blo 1738570 2609105 := bstep (se 2 (by rfl) ⟨978414, by rfl⟩ : syracuseStep 2609105 = 1956829) B1956829
theorem B2609123 : Blo 1738570 2609123 := bstep (se 1 (by rfl) ⟨1956842, by rfl⟩ : syracuseStep 2609123 = 3913685) B3913685
theorem B2936803 : Blo 1738570 2936803 := bstep (se 1 (by rfl) ⟨2202602, by rfl⟩ : syracuseStep 2936803 = 4405205) B4405205
theorem B2609153 : Blo 1738570 2609153 := bstep (se 2 (by rfl) ⟨978432, by rfl⟩ : syracuseStep 2609153 = 1956865) B1956865
theorem B2609171 : Blo 1738570 2609171 := bstep (se 1 (by rfl) ⟨1956878, by rfl⟩ : syracuseStep 2609171 = 3913757) B3913757
theorem B11907107 : Blo 1738570 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B8810531 : Blo 1738570 8810531 := bstep (se 1 (by rfl) ⟨6607898, by rfl⟩ : syracuseStep 8810531 = 13215797) B13215797
theorem B2609201 : Blo 1738570 2609201 := bstep (se 2 (by rfl) ⟨978450, by rfl⟩ : syracuseStep 2609201 = 1956901) B1956901
theorem B2609219 : Blo 1738570 2609219 := bstep (se 1 (by rfl) ⟨1956914, by rfl⟩ : syracuseStep 2609219 = 3913829) B3913829
theorem B4403281 : Blo 1738570 4403281 := bstep (se 2 (by rfl) ⟨1651230, by rfl⟩ : syracuseStep 4403281 = 3302461) B3302461
theorem B2609249 : Blo 1738570 2609249 := bstep (se 2 (by rfl) ⟨978468, by rfl⟩ : syracuseStep 2609249 = 1956937) B1956937
theorem B2936945 : Blo 1738570 2936945 := bstep (se 2 (by rfl) ⟨1101354, by rfl⟩ : syracuseStep 2936945 = 2202709) B2202709
theorem B2609267 : Blo 1738570 2609267 := bstep (se 1 (by rfl) ⟨1956950, by rfl⟩ : syracuseStep 2609267 = 3913901) B3913901
theorem B2609297 : Blo 1738570 2609297 := bstep (se 2 (by rfl) ⟨978486, by rfl⟩ : syracuseStep 2609297 = 1956973) B1956973
theorem B2609315 : Blo 1738570 2609315 := bstep (se 1 (by rfl) ⟨1956986, by rfl⟩ : syracuseStep 2609315 = 3913973) B3913973
theorem B3715235 : Blo 1738570 3715235 := bstep (se 1 (by rfl) ⟨2786426, by rfl⟩ : syracuseStep 3715235 = 5572853) B5572853
theorem B5869745 : Blo 1738570 5869745 := bstep (se 2 (by rfl) ⟨2201154, by rfl⟩ : syracuseStep 5869745 = 4402309) B4402309
theorem B2609345 : Blo 1738570 2609345 := bstep (se 2 (by rfl) ⟨978504, by rfl⟩ : syracuseStep 2609345 = 1957009) B1957009
theorem B6033613 : Blo 1738570 6033613 := bstep (se 3 (by rfl) ⟨1131302, by rfl⟩ : syracuseStep 6033613 = 2262605) B2262605
theorem B2609363 : Blo 1738570 2609363 := bstep (se 1 (by rfl) ⟨1957022, by rfl⟩ : syracuseStep 2609363 = 3914045) B3914045
theorem B3911921 : Blo 1738570 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B2609393 : Blo 1738570 2609393 := bstep (se 2 (by rfl) ⟨978522, by rfl⟩ : syracuseStep 2609393 = 1957045) B1957045
theorem B2937073 : Blo 1738570 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B3911939 : Blo 1738570 3911939 := bstep (se 1 (by rfl) ⟨2933954, by rfl⟩ : syracuseStep 3911939 = 5867909) B5867909
theorem B2609411 : Blo 1738570 2609411 := bstep (se 1 (by rfl) ⟨1957058, by rfl⟩ : syracuseStep 2609411 = 3914117) B3914117
theorem B2937107 : Blo 1738570 2937107 := bstep (se 1 (by rfl) ⟨2202830, by rfl⟩ : syracuseStep 2937107 = 4405661) B4405661
theorem B2609441 : Blo 1738570 2609441 := bstep (se 2 (by rfl) ⟨978540, by rfl⟩ : syracuseStep 2609441 = 1957081) B1957081
theorem B2609459 : Blo 1738570 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B2609489 : Blo 1738570 2609489 := bstep (se 2 (by rfl) ⟨978558, by rfl⟩ : syracuseStep 2609489 = 1957117) B1957117
theorem B3526993 : Blo 1738570 3526993 := bstep (se 2 (by rfl) ⟨1322622, by rfl⟩ : syracuseStep 3526993 = 2645245) B2645245
theorem B2609507 : Blo 1738570 2609507 := bstep (se 1 (by rfl) ⟨1957130, by rfl⟩ : syracuseStep 2609507 = 3914261) B3914261
theorem B4403555 : Blo 1738570 4403555 := bstep (se 1 (by rfl) ⟨3302666, by rfl⟩ : syracuseStep 4403555 = 6605333) B6605333
theorem B2609537 : Blo 1738570 2609537 := bstep (se 2 (by rfl) ⟨978576, by rfl⟩ : syracuseStep 2609537 = 1957153) B1957153
theorem B20083085 : Blo 1738570 20083085 := bstep (se 3 (by rfl) ⟨3765578, by rfl⟩ : syracuseStep 20083085 = 7531157) B7531157
theorem B2609555 : Blo 1738570 2609555 := bstep (se 1 (by rfl) ⟨1957166, by rfl⟩ : syracuseStep 2609555 = 3914333) B3914333
theorem B2609585 : Blo 1738570 2609585 := bstep (se 2 (by rfl) ⟨978594, by rfl⟩ : syracuseStep 2609585 = 1957189) B1957189
theorem B2609603 : Blo 1738570 2609603 := bstep (se 1 (by rfl) ⟨1957202, by rfl⟩ : syracuseStep 2609603 = 3914405) B3914405
theorem B2609633 : Blo 1738570 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B3133937 : Blo 1738570 3133937 := bstep (se 2 (by rfl) ⟨1175226, by rfl⟩ : syracuseStep 3133937 = 2350453) B2350453
theorem B2609651 : Blo 1738570 2609651 := bstep (se 1 (by rfl) ⟨1957238, by rfl⟩ : syracuseStep 2609651 = 3914477) B3914477
theorem B3912209 : Blo 1738570 3912209 := bstep (se 2 (by rfl) ⟨1467078, by rfl⟩ : syracuseStep 3912209 = 2934157) B2934157
theorem B2609681 : Blo 1738570 2609681 := bstep (se 2 (by rfl) ⟨978630, by rfl⟩ : syracuseStep 2609681 = 1957261) B1957261
theorem B3912227 : Blo 1738570 3912227 := bstep (se 1 (by rfl) ⟨2934170, by rfl⟩ : syracuseStep 3912227 = 5868341) B5868341
theorem B4403747 : Blo 1738570 4403747 := bstep (se 1 (by rfl) ⟨3302810, by rfl⟩ : syracuseStep 4403747 = 6605621) B6605621
theorem B2609699 : Blo 1738570 2609699 := bstep (se 1 (by rfl) ⟨1957274, by rfl⟩ : syracuseStep 2609699 = 3914549) B3914549
theorem B2609729 : Blo 1738570 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B11293253 : Blo 1738570 11293253 := bstep (se 4 (by rfl) ⟨1058742, by rfl⟩ : syracuseStep 11293253 = 2117485) B2117485
theorem B2609747 : Blo 1738570 2609747 := bstep (se 1 (by rfl) ⟨1957310, by rfl⟩ : syracuseStep 2609747 = 3914621) B3914621
theorem B2232931 : Blo 1738570 2232931 := bstep (se 1 (by rfl) ⟨1674698, by rfl⟩ : syracuseStep 2232931 = 3349397) B3349397
theorem B2609777 : Blo 1738570 2609777 := bstep (se 2 (by rfl) ⟨978666, by rfl⟩ : syracuseStep 2609777 = 1957333) B1957333
theorem B2609795 : Blo 1738570 2609795 := bstep (se 1 (by rfl) ⟨1957346, by rfl⟩ : syracuseStep 2609795 = 3914693) B3914693
theorem B15864461 : Blo 1738570 15864461 := bstep (se 3 (by rfl) ⟨2974586, by rfl⟩ : syracuseStep 15864461 = 5949173) B5949173
theorem B5575313 : Blo 1738570 5575313 := bstep (se 2 (by rfl) ⟨2090742, by rfl⟩ : syracuseStep 5575313 = 4181485) B4181485
theorem B2609825 : Blo 1738570 2609825 := bstep (se 2 (by rfl) ⟨978684, by rfl⟩ : syracuseStep 2609825 = 1957369) B1957369
theorem B2609843 : Blo 1738570 2609843 := bstep (se 1 (by rfl) ⟨1957382, by rfl⟩ : syracuseStep 2609843 = 3914765) B3914765
theorem B5870285 : Blo 1738570 5870285 := bstep (se 3 (by rfl) ⟨1100678, by rfl⟩ : syracuseStep 5870285 = 2201357) B2201357
theorem B6607565 : Blo 1738570 6607565 := bstep (se 3 (by rfl) ⟨1238918, by rfl⟩ : syracuseStep 6607565 = 2477837) B2477837
theorem B2609873 : Blo 1738570 2609873 := bstep (se 2 (by rfl) ⟨978702, by rfl⟩ : syracuseStep 2609873 = 1957405) B1957405
theorem B2609891 : Blo 1738570 2609891 := bstep (se 1 (by rfl) ⟨1957418, by rfl⟩ : syracuseStep 2609891 = 3914837) B3914837
theorem B2609921 : Blo 1738570 2609921 := bstep (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) B1957441
theorem B5870339 : Blo 1738570 5870339 := bstep (se 1 (by rfl) ⟨4402754, by rfl⟩ : syracuseStep 5870339 = 8805509) B8805509
theorem B2609939 : Blo 1738570 2609939 := bstep (se 1 (by rfl) ⟨1957454, by rfl⟩ : syracuseStep 2609939 = 3914909) B3914909
theorem B3912497 : Blo 1738570 3912497 := bstep (se 2 (by rfl) ⟨1467186, by rfl⟩ : syracuseStep 3912497 = 2934373) B2934373
theorem B2609969 : Blo 1738570 2609969 := bstep (se 2 (by rfl) ⟨978738, by rfl⟩ : syracuseStep 2609969 = 1957477) B1957477
theorem B22598453 : Blo 1738570 22598453 := bstep (se 5 (by rfl) ⟨1059302, by rfl⟩ : syracuseStep 22598453 = 2118605) B2118605
theorem B3912515 : Blo 1738570 3912515 := bstep (se 1 (by rfl) ⟨2934386, by rfl⟩ : syracuseStep 3912515 = 5868773) B5868773
theorem B2609987 : Blo 1738570 2609987 := bstep (se 1 (by rfl) ⟨1957490, by rfl⟩ : syracuseStep 2609987 = 3914981) B3914981
theorem B8811341 : Blo 1738570 8811341 := bstep (se 3 (by rfl) ⟨1652126, by rfl⟩ : syracuseStep 8811341 = 3304253) B3304253
theorem B2610017 : Blo 1738570 2610017 := bstep (se 2 (by rfl) ⟨978756, by rfl⟩ : syracuseStep 2610017 = 1957513) B1957513
theorem B2610035 : Blo 1738570 2610035 := bstep (se 1 (by rfl) ⟨1957526, by rfl⟩ : syracuseStep 2610035 = 3915053) B3915053
theorem B4952963 : Blo 1738570 4952963 := bstep (se 1 (by rfl) ⟨3714722, by rfl⟩ : syracuseStep 4952963 = 7429445) B7429445
theorem B2610065 : Blo 1738570 2610065 := bstep (se 2 (by rfl) ⟨978774, by rfl⟩ : syracuseStep 2610065 = 1957549) B1957549
theorem B2610083 : Blo 1738570 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B2610113 : Blo 1738570 2610113 := bstep (se 2 (by rfl) ⟨978792, by rfl⟩ : syracuseStep 2610113 = 1957585) B1957585
theorem B19821509 : Blo 1738570 19821509 := bstep (se 4 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 19821509 = 3716533) B3716533
theorem B2610131 : Blo 1738570 2610131 := bstep (se 1 (by rfl) ⟨1957598, by rfl⟩ : syracuseStep 2610131 = 3915197) B3915197
theorem B2200547 : Blo 1738570 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B2610161 : Blo 1738570 2610161 := bstep (se 2 (by rfl) ⟨978810, by rfl⟩ : syracuseStep 2610161 = 1957621) B1957621
theorem B2610179 : Blo 1738570 2610179 := bstep (se 1 (by rfl) ⟨1957634, by rfl⟩ : syracuseStep 2610179 = 3915269) B3915269
theorem B5870609 : Blo 1738570 5870609 := bstep (se 2 (by rfl) ⟨2201478, by rfl⟩ : syracuseStep 5870609 = 4402957) B4402957
theorem B2610209 : Blo 1738570 2610209 := bstep (se 2 (by rfl) ⟨978828, by rfl⟩ : syracuseStep 2610209 = 1957657) B1957657
theorem B2610227 : Blo 1738570 2610227 := bstep (se 1 (by rfl) ⟨1957670, by rfl⟩ : syracuseStep 2610227 = 3915341) B3915341
theorem B3912785 : Blo 1738570 3912785 := bstep (se 2 (by rfl) ⟨1467294, by rfl⟩ : syracuseStep 3912785 = 2934589) B2934589
theorem B2610257 : Blo 1738570 2610257 := bstep (se 2 (by rfl) ⟨978846, by rfl⟩ : syracuseStep 2610257 = 1957693) B1957693
theorem B3912803 : Blo 1738570 3912803 := bstep (se 1 (by rfl) ⟨2934602, by rfl⟩ : syracuseStep 3912803 = 5869205) B5869205
theorem B2610275 : Blo 1738570 2610275 := bstep (se 1 (by rfl) ⟨1957706, by rfl⟩ : syracuseStep 2610275 = 3915413) B3915413
theorem B3716209 : Blo 1738570 3716209 := bstep (se 2 (by rfl) ⟨1393578, by rfl⟩ : syracuseStep 3716209 = 2787157) B2787157
theorem B2610305 : Blo 1738570 2610305 := bstep (se 2 (by rfl) ⟨978864, by rfl⟩ : syracuseStep 2610305 = 1957729) B1957729
theorem B5575825 : Blo 1738570 5575825 := bstep (se 2 (by rfl) ⟨2090934, by rfl⟩ : syracuseStep 5575825 = 4181869) B4181869
theorem B2610323 : Blo 1738570 2610323 := bstep (se 1 (by rfl) ⟨1957742, by rfl⟩ : syracuseStep 2610323 = 3915485) B3915485
theorem B2610353 : Blo 1738570 2610353 := bstep (se 2 (by rfl) ⟨978882, by rfl⟩ : syracuseStep 2610353 = 1957765) B1957765
theorem B2610371 : Blo 1738570 2610371 := bstep (se 1 (by rfl) ⟨1957778, by rfl⟩ : syracuseStep 2610371 = 3915557) B3915557
theorem B2610401 : Blo 1738570 2610401 := bstep (se 2 (by rfl) ⟨978900, by rfl⟩ : syracuseStep 2610401 = 1957801) B1957801
theorem B2610419 : Blo 1738570 2610419 := bstep (se 1 (by rfl) ⟨1957814, by rfl⟩ : syracuseStep 2610419 = 3915629) B3915629
theorem B2610449 : Blo 1738570 2610449 := bstep (se 2 (by rfl) ⟨978918, by rfl⟩ : syracuseStep 2610449 = 1957837) B1957837
theorem B2610467 : Blo 1738570 2610467 := bstep (se 1 (by rfl) ⟨1957850, by rfl⟩ : syracuseStep 2610467 = 3915701) B3915701
theorem B3437873 : Blo 1738570 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B2610497 : Blo 1738570 2610497 := bstep (se 2 (by rfl) ⟨978936, by rfl⟩ : syracuseStep 2610497 = 1957873) B1957873
theorem B2610515 : Blo 1738570 2610515 := bstep (se 1 (by rfl) ⟨1957886, by rfl⟩ : syracuseStep 2610515 = 3915773) B3915773
theorem B3913073 : Blo 1738570 3913073 := bstep (se 2 (by rfl) ⟨1467402, by rfl⟩ : syracuseStep 3913073 = 2934805) B2934805
theorem B2610545 : Blo 1738570 2610545 := bstep (se 2 (by rfl) ⟨978954, by rfl⟩ : syracuseStep 2610545 = 1957909) B1957909
theorem B3913091 : Blo 1738570 3913091 := bstep (se 1 (by rfl) ⟨2934818, by rfl⟩ : syracuseStep 3913091 = 5869637) B5869637
theorem B2610563 : Blo 1738570 2610563 := bstep (se 1 (by rfl) ⟨1957922, by rfl⟩ : syracuseStep 2610563 = 3915845) B3915845
theorem B2610593 : Blo 1738570 2610593 := bstep (se 2 (by rfl) ⟨978972, by rfl⟩ : syracuseStep 2610593 = 1957945) B1957945
theorem B2610611 : Blo 1738570 2610611 := bstep (se 1 (by rfl) ⟨1957958, by rfl⟩ : syracuseStep 2610611 = 3915917) B3915917
theorem B4404689 : Blo 1738570 4404689 := bstep (se 2 (by rfl) ⟨1651758, by rfl⟩ : syracuseStep 4404689 = 3303517) B3303517
theorem B2610641 : Blo 1738570 2610641 := bstep (se 2 (by rfl) ⟨978990, by rfl⟩ : syracuseStep 2610641 = 1957981) B1957981
theorem B2610659 : Blo 1738570 2610659 := bstep (se 1 (by rfl) ⟨1957994, by rfl⟩ : syracuseStep 2610659 = 3915989) B3915989
theorem B2823665 : Blo 1738570 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B5289457 : Blo 1738570 5289457 := bstep (se 2 (by rfl) ⟨1983546, by rfl⟩ : syracuseStep 5289457 = 3967093) B3967093
theorem B1857011 : Blo 1738570 1857011 := bstep (se 1 (by rfl) ⟨1392758, by rfl⟩ : syracuseStep 1857011 = 2785517) B2785517
theorem B4404739 : Blo 1738570 4404739 := bstep (se 1 (by rfl) ⟨3303554, by rfl⟩ : syracuseStep 4404739 = 6607109) B6607109
theorem B2610689 : Blo 1738570 2610689 := bstep (se 2 (by rfl) ⟨979008, by rfl⟩ : syracuseStep 2610689 = 1958017) B1958017
theorem B2610707 : Blo 1738570 2610707 := bstep (se 1 (by rfl) ⟨1958030, by rfl⟩ : syracuseStep 2610707 = 3916061) B3916061
theorem B5871149 : Blo 1738570 5871149 := bstep (se 3 (by rfl) ⟨1100840, by rfl⟩ : syracuseStep 5871149 = 2201681) B2201681
theorem B8803889 : Blo 1738570 8803889 := bstep (se 2 (by rfl) ⟨3301458, by rfl⟩ : syracuseStep 8803889 = 6602917) B6602917
theorem B2610737 : Blo 1738570 2610737 := bstep (se 2 (by rfl) ⟨979026, by rfl⟩ : syracuseStep 2610737 = 1958053) B1958053
theorem B2610755 : Blo 1738570 2610755 := bstep (se 1 (by rfl) ⟨1958066, by rfl⟩ : syracuseStep 2610755 = 3916133) B3916133
theorem B5871203 : Blo 1738570 5871203 := bstep (se 1 (by rfl) ⟨4403402, by rfl⟩ : syracuseStep 5871203 = 8806805) B8806805
theorem B2610785 : Blo 1738570 2610785 := bstep (se 2 (by rfl) ⟨979044, by rfl⟩ : syracuseStep 2610785 = 1958089) B1958089
theorem B2610803 : Blo 1738570 2610803 := bstep (se 1 (by rfl) ⟨1958102, by rfl⟩ : syracuseStep 2610803 = 3916205) B3916205
theorem B3913361 : Blo 1738570 3913361 := bstep (se 2 (by rfl) ⟨1467510, by rfl⟩ : syracuseStep 3913361 = 2935021) B2935021
theorem B4404881 : Blo 1738570 4404881 := bstep (se 2 (by rfl) ⟨1651830, by rfl⟩ : syracuseStep 4404881 = 3303661) B3303661
theorem B2610833 : Blo 1738570 2610833 := bstep (se 2 (by rfl) ⟨979062, by rfl⟩ : syracuseStep 2610833 = 1958125) B1958125
theorem B2201251 : Blo 1738570 2201251 := bstep (se 1 (by rfl) ⟨1650938, by rfl⟩ : syracuseStep 2201251 = 3301877) B3301877
theorem B3913379 : Blo 1738570 3913379 := bstep (se 1 (by rfl) ⟨2935034, by rfl⟩ : syracuseStep 3913379 = 5870069) B5870069
theorem B2610851 : Blo 1738570 2610851 := bstep (se 1 (by rfl) ⟨1958138, by rfl⟩ : syracuseStep 2610851 = 3916277) B3916277
theorem B2201347 : Blo 1738570 2201347 := bstep (se 1 (by rfl) ⟨1651010, by rfl⟩ : syracuseStep 2201347 = 3302021) B3302021
theorem B3716867 : Blo 1738570 3716867 := bstep (se 1 (by rfl) ⟨2787650, by rfl⟩ : syracuseStep 3716867 = 5575301) B5575301
theorem B5871473 : Blo 1738570 5871473 := bstep (se 2 (by rfl) ⟨2201802, by rfl⟩ : syracuseStep 5871473 = 4403605) B4403605
theorem B3913649 : Blo 1738570 3913649 := bstep (se 2 (by rfl) ⟨1467618, by rfl⟩ : syracuseStep 3913649 = 2935237) B2935237
theorem B2643907 : Blo 1738570 2643907 := bstep (se 1 (by rfl) ⟨1982930, by rfl⟩ : syracuseStep 2643907 = 3965861) B3965861
theorem B3913667 : Blo 1738570 3913667 := bstep (se 1 (by rfl) ⟨2935250, by rfl⟩ : syracuseStep 3913667 = 5870501) B5870501
theorem B7428131 : Blo 1738570 7428131 := bstep (se 1 (by rfl) ⟨5571098, by rfl⟩ : syracuseStep 7428131 = 11142197) B11142197
theorem B4954193 : Blo 1738570 4954193 := bstep (se 2 (by rfl) ⟨1857822, by rfl⟩ : syracuseStep 4954193 = 3715645) B3715645
theorem B1956019 : Blo 1738570 1956019 := bstep (se 1 (by rfl) ⟨1467014, by rfl⟩ : syracuseStep 1956019 = 2934029) B2934029
theorem B16718021 : Blo 1738570 16718021 := bstep (se 4 (by rfl) ⟨1567314, by rfl⟩ : syracuseStep 16718021 = 3134629) B3134629
theorem B3913937 : Blo 1738570 3913937 := bstep (se 2 (by rfl) ⟨1467726, by rfl⟩ : syracuseStep 3913937 = 2935453) B2935453
theorem B4700387 : Blo 1738570 4700387 := bstep (se 1 (by rfl) ⟨3525290, by rfl⟩ : syracuseStep 4700387 = 7050581) B7050581
theorem B3913955 : Blo 1738570 3913955 := bstep (se 1 (by rfl) ⟨2935466, by rfl⟩ : syracuseStep 3913955 = 5870933) B5870933
theorem B1857763 : Blo 1738570 1857763 := bstep (se 1 (by rfl) ⟨1393322, by rfl⟩ : syracuseStep 1857763 = 2786645) B2786645
theorem B8476913 : Blo 1738570 8476913 := bstep (se 2 (by rfl) ⟨3178842, by rfl⟩ : syracuseStep 8476913 = 6357685) B6357685
theorem B2201843 : Blo 1738570 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B9902371 : Blo 1738570 9902371 := bstep (se 1 (by rfl) ⟨7426778, by rfl⟩ : syracuseStep 9902371 = 14853557) B14853557
theorem B1956163 : Blo 1738570 1956163 := bstep (se 1 (by rfl) ⟨1467122, by rfl⟩ : syracuseStep 1956163 = 2934245) B2934245
theorem B5872013 : Blo 1738570 5872013 := bstep (se 3 (by rfl) ⟨1101002, by rfl⟩ : syracuseStep 5872013 = 2202005) B2202005
theorem B5872067 : Blo 1738570 5872067 := bstep (se 1 (by rfl) ⟨4404050, by rfl⟩ : syracuseStep 5872067 = 8808101) B8808101
theorem B1956307 : Blo 1738570 1956307 := bstep (se 1 (by rfl) ⟨1467230, by rfl⟩ : syracuseStep 1956307 = 2934461) B2934461
theorem B16308707 : Blo 1738570 16308707 := bstep (se 1 (by rfl) ⟨12231530, by rfl⟩ : syracuseStep 16308707 = 24463061) B24463061
theorem B3135971 : Blo 1738570 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B3914225 : Blo 1738570 3914225 := bstep (se 2 (by rfl) ⟨1467834, by rfl⟩ : syracuseStep 3914225 = 2935669) B2935669
theorem B3914243 : Blo 1738570 3914243 := bstep (se 1 (by rfl) ⟨2935682, by rfl⟩ : syracuseStep 3914243 = 5871365) B5871365
theorem B16087565 : Blo 1738570 16087565 := bstep (se 3 (by rfl) ⟨3016418, by rfl⟩ : syracuseStep 16087565 = 6032837) B6032837
theorem B1956451 : Blo 1738570 1956451 := bstep (se 1 (by rfl) ⟨1467338, by rfl⟩ : syracuseStep 1956451 = 2934677) B2934677
theorem B5872337 : Blo 1738570 5872337 := bstep (se 2 (by rfl) ⟨2202126, by rfl⟩ : syracuseStep 5872337 = 4404253) B4404253
theorem B2349793 : Blo 1738570 2349793 := bstep (se 2 (by rfl) ⟨881172, by rfl⟩ : syracuseStep 2349793 = 1762345) B1762345
theorem B8043235 : Blo 1738570 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B1956595 : Blo 1738570 1956595 := bstep (se 1 (by rfl) ⟨1467446, by rfl⟩ : syracuseStep 1956595 = 2934893) B2934893
theorem B3136259 : Blo 1738570 3136259 := bstep (se 1 (by rfl) ⟨2352194, by rfl⟩ : syracuseStep 3136259 = 4704389) B4704389
theorem B3914513 : Blo 1738570 3914513 := bstep (se 2 (by rfl) ⟨1467942, by rfl⟩ : syracuseStep 3914513 = 2935885) B2935885
theorem B3914531 : Blo 1738570 3914531 := bstep (se 1 (by rfl) ⟨2935898, by rfl⟩ : syracuseStep 3914531 = 5871797) B5871797
theorem B9902897 : Blo 1738570 9902897 := bstep (se 2 (by rfl) ⟨3713586, by rfl⟩ : syracuseStep 9902897 = 7427173) B7427173
theorem B2382643 : Blo 1738570 2382643 := bstep (se 1 (by rfl) ⟨1786982, by rfl⟩ : syracuseStep 2382643 = 3573965) B3573965
theorem B1956739 : Blo 1738570 1956739 := bstep (se 1 (by rfl) ⟨1467554, by rfl⟩ : syracuseStep 1956739 = 2935109) B2935109
theorem B2202547 : Blo 1738570 2202547 := bstep (se 1 (by rfl) ⟨1651910, by rfl⟩ : syracuseStep 2202547 = 3303821) B3303821
theorem B8805347 : Blo 1738570 8805347 := bstep (se 1 (by rfl) ⟨6604010, by rfl⟩ : syracuseStep 8805347 = 13208021) B13208021
theorem B1956883 : Blo 1738570 1956883 := bstep (se 1 (by rfl) ⟨1467662, by rfl⟩ : syracuseStep 1956883 = 2935325) B2935325
theorem B2202643 : Blo 1738570 2202643 := bstep (se 1 (by rfl) ⟨1651982, by rfl⟩ : syracuseStep 2202643 = 3303965) B3303965
theorem B6601763 : Blo 1738570 6601763 := bstep (se 1 (by rfl) ⟨4951322, by rfl⟩ : syracuseStep 6601763 = 9902645) B9902645
theorem B10583075 : Blo 1738570 10583075 := bstep (se 1 (by rfl) ⟨7937306, by rfl⟩ : syracuseStep 10583075 = 15874613) B15874613
theorem B3914801 : Blo 1738570 3914801 := bstep (se 2 (by rfl) ⟨1468050, by rfl⟩ : syracuseStep 3914801 = 2936101) B2936101
theorem B25426997 : Blo 1738570 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B3914819 : Blo 1738570 3914819 := bstep (se 1 (by rfl) ⟨2936114, by rfl⟩ : syracuseStep 3914819 = 5872229) B5872229
theorem B1957027 : Blo 1738570 1957027 := bstep (se 1 (by rfl) ⟨1467770, by rfl⟩ : syracuseStep 1957027 = 2935541) B2935541
theorem B5872877 : Blo 1738570 5872877 := bstep (se 3 (by rfl) ⟨1101164, by rfl⟩ : syracuseStep 5872877 = 2202329) B2202329
theorem B80321813 : Blo 1738570 80321813 := bstep (se 6 (by rfl) ⟨1882542, by rfl⟩ : syracuseStep 80321813 = 3765085) B3765085
theorem B5872931 : Blo 1738570 5872931 := bstep (se 1 (by rfl) ⟨4404698, by rfl⟩ : syracuseStep 5872931 = 8809397) B8809397
theorem B1957171 : Blo 1738570 1957171 := bstep (se 1 (by rfl) ⟨1467878, by rfl⟩ : syracuseStep 1957171 = 2935757) B2935757
theorem B3915089 : Blo 1738570 3915089 := bstep (se 2 (by rfl) ⟨1468158, by rfl⟩ : syracuseStep 3915089 = 2936317) B2936317
theorem B3915107 : Blo 1738570 3915107 := bstep (se 1 (by rfl) ⟨2936330, by rfl⟩ : syracuseStep 3915107 = 5872661) B5872661
theorem B1957315 : Blo 1738570 1957315 := bstep (se 1 (by rfl) ⟨1467986, by rfl⟩ : syracuseStep 1957315 = 2935973) B2935973
theorem B2645507 : Blo 1738570 2645507 := bstep (se 1 (by rfl) ⟨1984130, by rfl⟩ : syracuseStep 2645507 = 3968261) B3968261
theorem B4955651 : Blo 1738570 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B5873201 : Blo 1738570 5873201 := bstep (se 2 (by rfl) ⟨2202450, by rfl⟩ : syracuseStep 5873201 = 4404901) B4404901
theorem B14859845 : Blo 1738570 14859845 := bstep (se 4 (by rfl) ⟨1393110, by rfl⟩ : syracuseStep 14859845 = 2786221) B2786221
theorem B1957459 : Blo 1738570 1957459 := bstep (se 1 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 1957459 = 2936189) B2936189
theorem B4177507 : Blo 1738570 4177507 := bstep (se 1 (by rfl) ⟨3133130, by rfl⟩ : syracuseStep 4177507 = 6266261) B6266261
theorem B13205105 : Blo 1738570 13205105 := bstep (se 2 (by rfl) ⟨4951914, by rfl⟩ : syracuseStep 13205105 = 9903829) B9903829
theorem B5291633 : Blo 1738570 5291633 := bstep (se 2 (by rfl) ⟨1984362, by rfl⟩ : syracuseStep 5291633 = 3968725) B3968725
theorem B2784883 : Blo 1738570 2784883 := bstep (se 1 (by rfl) ⟨2088662, by rfl⟩ : syracuseStep 2784883 = 4177325) B4177325
theorem B3915377 : Blo 1738570 3915377 := bstep (se 2 (by rfl) ⟨1468266, by rfl⟩ : syracuseStep 3915377 = 2936533) B2936533
theorem B3915395 : Blo 1738570 3915395 := bstep (se 1 (by rfl) ⟨2936546, by rfl⟩ : syracuseStep 3915395 = 5873093) B5873093
theorem B14106253 : Blo 1738570 14106253 := bstep (se 3 (by rfl) ⟨2644922, by rfl⟩ : syracuseStep 14106253 = 5289845) B5289845
theorem B6602417 : Blo 1738570 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B24141509 : Blo 1738570 24141509 := bstep (se 4 (by rfl) ⟨2263266, by rfl⟩ : syracuseStep 24141509 = 4526533) B4526533
theorem B1957603 : Blo 1738570 1957603 := bstep (se 1 (by rfl) ⟨1468202, by rfl⟩ : syracuseStep 1957603 = 2936405) B2936405
theorem B8806157 : Blo 1738570 8806157 := bstep (se 3 (by rfl) ⟨1651154, by rfl⟩ : syracuseStep 8806157 = 3302309) B3302309
theorem B11902733 : Blo 1738570 11902733 := bstep (se 3 (by rfl) ⟨2231762, by rfl⟩ : syracuseStep 11902733 = 4463525) B4463525
theorem B9912077 : Blo 1738570 9912077 := bstep (se 3 (by rfl) ⟨1858514, by rfl⟩ : syracuseStep 9912077 = 3717029) B3717029
theorem B1957747 : Blo 1738570 1957747 := bstep (se 1 (by rfl) ⟨1468310, by rfl⟩ : syracuseStep 1957747 = 2936621) B2936621
theorem B3915665 : Blo 1738570 3915665 := bstep (se 2 (by rfl) ⟨1468374, by rfl⟩ : syracuseStep 3915665 = 2936749) B2936749
theorem B3915683 : Blo 1738570 3915683 := bstep (se 1 (by rfl) ⟨2936762, by rfl⟩ : syracuseStep 3915683 = 5873525) B5873525
theorem B7430129 : Blo 1738570 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B7938071 : Blo 1738570 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B5873687 : Blo 1738570 5873687 := bstep (se 1 (by rfl) ⟨4405265, by rfl⟩ : syracuseStep 5873687 = 8810531) B8810531
theorem B3915827 : Blo 1738570 3915827 := bstep (se 1 (by rfl) ⟨2936870, by rfl⟩ : syracuseStep 3915827 = 5873741) B5873741
theorem B1957963 : Blo 1738570 1957963 := bstep (se 1 (by rfl) ⟨1468472, by rfl⟩ : syracuseStep 1957963 = 2936945) B2936945
theorem B9912395 : Blo 1738570 9912395 := bstep (se 1 (by rfl) ⟨7434296, by rfl⟩ : syracuseStep 9912395 = 14868593) B14868593
theorem B3915863 : Blo 1738570 3915863 := bstep (se 1 (by rfl) ⟨2936897, by rfl⟩ : syracuseStep 3915863 = 5873795) B5873795
theorem B19808387 : Blo 1738570 19808387 := bstep (se 1 (by rfl) ⟨14856290, by rfl⟩ : syracuseStep 19808387 = 29712581) B29712581
theorem B6602903 : Blo 1738570 6602903 := bstep (se 1 (by rfl) ⟨4952177, by rfl⟩ : syracuseStep 6602903 = 9904355) B9904355
theorem B1958071 : Blo 1738570 1958071 := bstep (se 1 (by rfl) ⟨1468553, by rfl⟩ : syracuseStep 1958071 = 2937107) B2937107
theorem B3916043 : Blo 1738570 3916043 := bstep (se 1 (by rfl) ⟨2937032, by rfl⟩ : syracuseStep 3916043 = 5874065) B5874065
theorem B8044817 : Blo 1738570 8044817 := bstep (se 2 (by rfl) ⟨3016806, by rfl⟩ : syracuseStep 8044817 = 6033613) B6033613
theorem B3916097 : Blo 1738570 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B7528835 : Blo 1738570 7528835 := bstep (se 1 (by rfl) ⟨5646626, by rfl⟩ : syracuseStep 7528835 = 11293253) B11293253
theorem B10576307 : Blo 1738570 10576307 := bstep (se 1 (by rfl) ⟨7932230, by rfl⟩ : syracuseStep 10576307 = 15864461) B15864461
theorem B15065635 : Blo 1738570 15065635 := bstep (se 1 (by rfl) ⟨11299226, by rfl⟩ : syracuseStep 15065635 = 22598453) B22598453
theorem B5874227 : Blo 1738570 5874227 := bstep (se 1 (by rfl) ⟨4405670, by rfl⟩ : syracuseStep 5874227 = 8811341) B8811341
theorem B3301975 : Blo 1738570 3301975 := bstep (se 1 (by rfl) ⟨2476481, by rfl⟩ : syracuseStep 3301975 = 4952963) B4952963
theorem B12534365 : Blo 1738570 12534365 := bstep (se 3 (by rfl) ⟨2350193, by rfl⟩ : syracuseStep 12534365 = 4700387) B4700387
theorem B13214339 : Blo 1738570 13214339 := bstep (se 1 (by rfl) ⟨9910754, by rfl⟩ : syracuseStep 13214339 = 19821509) B19821509
theorem B8807129 : Blo 1738570 8807129 := bstep (se 2 (by rfl) ⟨3302673, by rfl⟩ : syracuseStep 8807129 = 6605347) B6605347
theorem B29721329 : Blo 1738570 29721329 := bstep (se 2 (by rfl) ⟨11145498, by rfl⟩ : syracuseStep 29721329 = 22290997) B22290997
theorem B4178891 : Blo 1738570 4178891 := bstep (se 1 (by rfl) ⟨3134168, by rfl⟩ : syracuseStep 4178891 = 6268337) B6268337
theorem B13206563 : Blo 1738570 13206563 := bstep (se 1 (by rfl) ⟨9904922, by rfl⟩ : syracuseStep 13206563 = 19809845) B19809845
theorem B4703383 : Blo 1738570 4703383 := bstep (se 1 (by rfl) ⟨3527537, by rfl⟩ : syracuseStep 4703383 = 7055075) B7055075
theorem B2933975 : Blo 1738570 2933975 := bstep (se 1 (by rfl) ⟨2200481, by rfl⟩ : syracuseStep 2933975 = 4400963) B4400963
theorem B7529773 : Blo 1738570 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B8357165 : Blo 1738570 8357165 := bstep (se 3 (by rfl) ⟨1566968, by rfl⟩ : syracuseStep 8357165 = 3133937) B3133937
theorem B2934103 : Blo 1738570 2934103 := bstep (se 1 (by rfl) ⟨2200577, by rfl⟩ : syracuseStep 2934103 = 4401155) B4401155
theorem B7054685 : Blo 1738570 7054685 := bstep (se 3 (by rfl) ⟨1322753, by rfl⟩ : syracuseStep 7054685 = 2645507) B2645507
theorem B6604163 : Blo 1738570 6604163 := bstep (se 1 (by rfl) ⟨4953122, by rfl⟩ : syracuseStep 6604163 = 9906245) B9906245
theorem B3302795 : Blo 1738570 3302795 := bstep (se 1 (by rfl) ⟨2477096, by rfl⟩ : syracuseStep 3302795 = 4954193) B4954193
theorem B3302849 : Blo 1738570 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B2475479 : Blo 1738570 2475479 := bstep (se 1 (by rfl) ⟨1856609, by rfl⟩ : syracuseStep 2475479 = 3713219) B3713219
theorem B2090647 : Blo 1738570 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B10725043 : Blo 1738570 10725043 := bstep (se 1 (by rfl) ⟨8043782, by rfl⟩ : syracuseStep 10725043 = 16087565) B16087565
theorem B5572289 : Blo 1738570 5572289 := bstep (se 2 (by rfl) ⟨2089608, by rfl⟩ : syracuseStep 5572289 = 4179217) B4179217
theorem B18810629 : Blo 1738570 18810629 := bstep (se 4 (by rfl) ⟨1763496, by rfl⟩ : syracuseStep 18810629 = 3526993) B3526993
theorem B2475787 : Blo 1738570 2475787 := bstep (se 1 (by rfl) ⟨1856840, by rfl⟩ : syracuseStep 2475787 = 3713681) B3713681
theorem B12543761 : Blo 1738570 12543761 := bstep (se 2 (by rfl) ⟨4703910, by rfl⟩ : syracuseStep 12543761 = 9407821) B9407821
theorem B1738571 : Blo 1738570 1738571 := bstep (se 1 (by rfl) ⟨1303928, by rfl⟩ : syracuseStep 1738571 = 2607857) B2607857
theorem B1738583 : Blo 1738570 1738583 := bstep (se 1 (by rfl) ⟨1303937, by rfl⟩ : syracuseStep 1738583 = 2607875) B2607875
theorem B2090839 : Blo 1738570 2090839 := bstep (se 1 (by rfl) ⟨1568129, by rfl⟩ : syracuseStep 2090839 = 3136259) B3136259
theorem B1738603 : Blo 1738570 1738603 := bstep (se 1 (by rfl) ⟨1303952, by rfl⟩ : syracuseStep 1738603 = 2607905) B2607905
theorem B1738615 : Blo 1738570 1738615 := bstep (se 1 (by rfl) ⟨1303961, by rfl⟩ : syracuseStep 1738615 = 2607923) B2607923
theorem B1738635 : Blo 1738570 1738635 := bstep (se 1 (by rfl) ⟨1303976, by rfl⟩ : syracuseStep 1738635 = 2607953) B2607953
theorem B1738647 : Blo 1738570 1738647 := bstep (se 1 (by rfl) ⟨1303985, by rfl⟩ : syracuseStep 1738647 = 2607971) B2607971
theorem B1738667 : Blo 1738570 1738667 := bstep (se 1 (by rfl) ⟨1304000, by rfl⟩ : syracuseStep 1738667 = 2608001) B2608001
theorem B1738679 : Blo 1738570 1738679 := bstep (se 1 (by rfl) ⟨1304009, by rfl⟩ : syracuseStep 1738679 = 2608019) B2608019
theorem B1738699 : Blo 1738570 1738699 := bstep (se 1 (by rfl) ⟨1304024, by rfl⟩ : syracuseStep 1738699 = 2608049) B2608049
theorem B2934731 : Blo 1738570 2934731 := bstep (se 1 (by rfl) ⟨2201048, by rfl⟩ : syracuseStep 2934731 = 4402097) B4402097
theorem B1738711 : Blo 1738570 1738711 := bstep (se 1 (by rfl) ⟨1304033, by rfl⟩ : syracuseStep 1738711 = 2608067) B2608067
theorem B1738731 : Blo 1738570 1738731 := bstep (se 1 (by rfl) ⟨1304048, by rfl⟩ : syracuseStep 1738731 = 2608097) B2608097
theorem B1738743 : Blo 1738570 1738743 := bstep (se 1 (by rfl) ⟨1304057, by rfl⟩ : syracuseStep 1738743 = 2608115) B2608115
theorem B1738763 : Blo 1738570 1738763 := bstep (se 1 (by rfl) ⟨1304072, by rfl⟩ : syracuseStep 1738763 = 2608145) B2608145
theorem B4401175 : Blo 1738570 4401175 := bstep (se 1 (by rfl) ⟨3300881, by rfl⟩ : syracuseStep 4401175 = 6601763) B6601763
theorem B1738775 : Blo 1738570 1738775 := bstep (se 1 (by rfl) ⟨1304081, by rfl⟩ : syracuseStep 1738775 = 2608163) B2608163
theorem B7055383 : Blo 1738570 7055383 := bstep (se 1 (by rfl) ⟨5291537, by rfl⟩ : syracuseStep 7055383 = 10583075) B10583075
theorem B16951331 : Blo 1738570 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B1738795 : Blo 1738570 1738795 := bstep (se 1 (by rfl) ⟨1304096, by rfl⟩ : syracuseStep 1738795 = 2608193) B2608193
theorem B1738807 : Blo 1738570 1738807 := bstep (se 1 (by rfl) ⟨1304105, by rfl⟩ : syracuseStep 1738807 = 2608211) B2608211
theorem B9406529 : Blo 1738570 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B1738827 : Blo 1738570 1738827 := bstep (se 1 (by rfl) ⟨1304120, by rfl⟩ : syracuseStep 1738827 = 2608241) B2608241
theorem B2934859 : Blo 1738570 2934859 := bstep (se 1 (by rfl) ⟨2201144, by rfl⟩ : syracuseStep 2934859 = 4402289) B4402289
theorem B1738839 : Blo 1738570 1738839 := bstep (se 1 (by rfl) ⟨1304129, by rfl⟩ : syracuseStep 1738839 = 2608259) B2608259
theorem B1738859 : Blo 1738570 1738859 := bstep (se 1 (by rfl) ⟨1304144, by rfl⟩ : syracuseStep 1738859 = 2608289) B2608289
theorem B1738871 : Blo 1738570 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B1738891 : Blo 1738570 1738891 := bstep (se 1 (by rfl) ⟨1304168, by rfl⟩ : syracuseStep 1738891 = 2608337) B2608337
theorem B1738903 : Blo 1738570 1738903 := bstep (se 1 (by rfl) ⟨1304177, by rfl⟩ : syracuseStep 1738903 = 2608355) B2608355
theorem B3713177 : Blo 1738570 3713177 := bstep (se 2 (by rfl) ⟨1392441, by rfl⟩ : syracuseStep 3713177 = 2784883) B2784883
theorem B1738923 : Blo 1738570 1738923 := bstep (se 1 (by rfl) ⟨1304192, by rfl⟩ : syracuseStep 1738923 = 2608385) B2608385
theorem B1738935 : Blo 1738570 1738935 := bstep (se 1 (by rfl) ⟨1304201, by rfl⟩ : syracuseStep 1738935 = 2608403) B2608403
theorem B1738955 : Blo 1738570 1738955 := bstep (se 1 (by rfl) ⟨1304216, by rfl⟩ : syracuseStep 1738955 = 2608433) B2608433
theorem B1738967 : Blo 1738570 1738967 := bstep (se 1 (by rfl) ⟨1304225, by rfl⟩ : syracuseStep 1738967 = 2608451) B2608451
theorem B2935001 : Blo 1738570 2935001 := bstep (se 2 (by rfl) ⟨1100625, by rfl⟩ : syracuseStep 2935001 = 2201251) B2201251
theorem B1738987 : Blo 1738570 1738987 := bstep (se 1 (by rfl) ⟨1304240, by rfl⟩ : syracuseStep 1738987 = 2608481) B2608481
theorem B1738999 : Blo 1738570 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B1739019 : Blo 1738570 1739019 := bstep (se 1 (by rfl) ⟨1304264, by rfl⟩ : syracuseStep 1739019 = 2608529) B2608529
theorem B1739031 : Blo 1738570 1739031 := bstep (se 1 (by rfl) ⟨1304273, by rfl⟩ : syracuseStep 1739031 = 2608547) B2608547
theorem B1739051 : Blo 1738570 1739051 := bstep (se 1 (by rfl) ⟨1304288, by rfl⟩ : syracuseStep 1739051 = 2608577) B2608577
theorem B8808749 : Blo 1738570 8808749 := bstep (se 3 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 8808749 = 3303281) B3303281
theorem B1739063 : Blo 1738570 1739063 := bstep (se 1 (by rfl) ⟨1304297, by rfl⟩ : syracuseStep 1739063 = 2608595) B2608595
theorem B1739083 : Blo 1738570 1739083 := bstep (se 1 (by rfl) ⟨1304312, by rfl⟩ : syracuseStep 1739083 = 2608625) B2608625
theorem B1739095 : Blo 1738570 1739095 := bstep (se 1 (by rfl) ⟨1304321, by rfl⟩ : syracuseStep 1739095 = 2608643) B2608643
theorem B3303767 : Blo 1738570 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B2935129 : Blo 1738570 2935129 := bstep (se 2 (by rfl) ⟨1100673, by rfl⟩ : syracuseStep 2935129 = 2201347) B2201347
theorem B1739115 : Blo 1738570 1739115 := bstep (se 1 (by rfl) ⟨1304336, by rfl⟩ : syracuseStep 1739115 = 2608673) B2608673
theorem B1739127 : Blo 1738570 1739127 := bstep (se 1 (by rfl) ⟨1304345, by rfl⟩ : syracuseStep 1739127 = 2608691) B2608691
theorem B9906563 : Blo 1738570 9906563 := bstep (se 1 (by rfl) ⟨7429922, by rfl⟩ : syracuseStep 9906563 = 14859845) B14859845
theorem B1739147 : Blo 1738570 1739147 := bstep (se 1 (by rfl) ⟨1304360, by rfl⟩ : syracuseStep 1739147 = 2608721) B2608721
theorem B1739159 : Blo 1738570 1739159 := bstep (se 1 (by rfl) ⟨1304369, by rfl⟩ : syracuseStep 1739159 = 2608739) B2608739
theorem B1739179 : Blo 1738570 1739179 := bstep (se 1 (by rfl) ⟨1304384, by rfl⟩ : syracuseStep 1739179 = 2608769) B2608769
theorem B1739191 : Blo 1738570 1739191 := bstep (se 1 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 1739191 = 2608787) B2608787
theorem B4401611 : Blo 1738570 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B1739211 : Blo 1738570 1739211 := bstep (se 1 (by rfl) ⟨1304408, by rfl⟩ : syracuseStep 1739211 = 2608817) B2608817
theorem B1739223 : Blo 1738570 1739223 := bstep (se 1 (by rfl) ⟨1304417, by rfl⟩ : syracuseStep 1739223 = 2608835) B2608835
theorem B9406937 : Blo 1738570 9406937 := bstep (se 2 (by rfl) ⟨3527601, by rfl⟩ : syracuseStep 9406937 = 7055203) B7055203
theorem B4704733 : Blo 1738570 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B1739243 : Blo 1738570 1739243 := bstep (se 1 (by rfl) ⟨1304432, by rfl⟩ : syracuseStep 1739243 = 2608865) B2608865
theorem B1739255 : Blo 1738570 1739255 := bstep (se 1 (by rfl) ⟨1304441, by rfl⟩ : syracuseStep 1739255 = 2608883) B2608883
theorem B1739275 : Blo 1738570 1739275 := bstep (se 1 (by rfl) ⟨1304456, by rfl⟩ : syracuseStep 1739275 = 2608913) B2608913
theorem B1739287 : Blo 1738570 1739287 := bstep (se 1 (by rfl) ⟨1304465, by rfl⟩ : syracuseStep 1739287 = 2608931) B2608931
theorem B1739307 : Blo 1738570 1739307 := bstep (se 1 (by rfl) ⟨1304480, by rfl⟩ : syracuseStep 1739307 = 2608961) B2608961
theorem B1739319 : Blo 1738570 1739319 := bstep (se 1 (by rfl) ⟨1304489, by rfl⟩ : syracuseStep 1739319 = 2608979) B2608979
theorem B1739339 : Blo 1738570 1739339 := bstep (se 1 (by rfl) ⟨1304504, by rfl⟩ : syracuseStep 1739339 = 2609009) B2609009
theorem B1739351 : Blo 1738570 1739351 := bstep (se 1 (by rfl) ⟨1304513, by rfl⟩ : syracuseStep 1739351 = 2609027) B2609027
theorem B3525209 : Blo 1738570 3525209 := bstep (se 2 (by rfl) ⟨1321953, by rfl⟩ : syracuseStep 3525209 = 2643907) B2643907
theorem B7432793 : Blo 1738570 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B5868125 : Blo 1738570 5868125 := bstep (se 3 (by rfl) ⟨1100273, by rfl⟩ : syracuseStep 5868125 = 2200547) B2200547
theorem B1739371 : Blo 1738570 1739371 := bstep (se 1 (by rfl) ⟨1304528, by rfl⟩ : syracuseStep 1739371 = 2609057) B2609057
theorem B1739383 : Blo 1738570 1739383 := bstep (se 1 (by rfl) ⟨1304537, by rfl⟩ : syracuseStep 1739383 = 2609075) B2609075
theorem B1739403 : Blo 1738570 1739403 := bstep (se 1 (by rfl) ⟨1304552, by rfl⟩ : syracuseStep 1739403 = 2609105) B2609105
theorem B1739415 : Blo 1738570 1739415 := bstep (se 1 (by rfl) ⟨1304561, by rfl⟩ : syracuseStep 1739415 = 2609123) B2609123
theorem B1739435 : Blo 1738570 1739435 := bstep (se 1 (by rfl) ⟨1304576, by rfl⟩ : syracuseStep 1739435 = 2609153) B2609153
theorem B1739447 : Blo 1738570 1739447 := bstep (se 1 (by rfl) ⟨1304585, by rfl⟩ : syracuseStep 1739447 = 2609171) B2609171
theorem B1739467 : Blo 1738570 1739467 := bstep (se 1 (by rfl) ⟨1304600, by rfl⟩ : syracuseStep 1739467 = 2609201) B2609201
theorem B1739479 : Blo 1738570 1739479 := bstep (se 1 (by rfl) ⟨1304609, by rfl⟩ : syracuseStep 1739479 = 2609219) B2609219
theorem B1739499 : Blo 1738570 1739499 := bstep (se 1 (by rfl) ⟨1304624, by rfl⟩ : syracuseStep 1739499 = 2609249) B2609249
theorem B1739511 : Blo 1738570 1739511 := bstep (se 1 (by rfl) ⟨1304633, by rfl⟩ : syracuseStep 1739511 = 2609267) B2609267
theorem B1739531 : Blo 1738570 1739531 := bstep (se 1 (by rfl) ⟨1304648, by rfl⟩ : syracuseStep 1739531 = 2609297) B2609297
theorem B1739543 : Blo 1738570 1739543 := bstep (se 1 (by rfl) ⟨1304657, by rfl⟩ : syracuseStep 1739543 = 2609315) B2609315
theorem B2476823 : Blo 1738570 2476823 := bstep (se 1 (by rfl) ⟨1857617, by rfl⟩ : syracuseStep 2476823 = 3715235) B3715235
theorem B6269719 : Blo 1738570 6269719 := bstep (se 1 (by rfl) ⟨4702289, by rfl⟩ : syracuseStep 6269719 = 9404579) B9404579
theorem B1739563 : Blo 1738570 1739563 := bstep (se 1 (by rfl) ⟨1304672, by rfl⟩ : syracuseStep 1739563 = 2609345) B2609345
theorem B1739575 : Blo 1738570 1739575 := bstep (se 1 (by rfl) ⟨1304681, by rfl⟩ : syracuseStep 1739575 = 2609363) B2609363
theorem B4401985 : Blo 1738570 4401985 := bstep (se 2 (by rfl) ⟨1650744, by rfl⟩ : syracuseStep 4401985 = 3301489) B3301489
theorem B2607947 : Blo 1738570 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B9907019 : Blo 1738570 9907019 := bstep (se 1 (by rfl) ⟨7430264, by rfl⟩ : syracuseStep 9907019 = 14860529) B14860529
theorem B1739595 : Blo 1738570 1739595 := bstep (se 1 (by rfl) ⟨1304696, by rfl⟩ : syracuseStep 1739595 = 2609393) B2609393
theorem B2607959 : Blo 1738570 2607959 := bstep (se 1 (by rfl) ⟨1955969, by rfl⟩ : syracuseStep 2607959 = 3911939) B3911939
theorem B1739607 : Blo 1738570 1739607 := bstep (se 1 (by rfl) ⟨1304705, by rfl⟩ : syracuseStep 1739607 = 2609411) B2609411
theorem B1739627 : Blo 1738570 1739627 := bstep (se 1 (by rfl) ⟨1304720, by rfl⟩ : syracuseStep 1739627 = 2609441) B2609441
theorem B3304307 : Blo 1738570 3304307 := bstep (se 1 (by rfl) ⟨2478230, by rfl⟩ : syracuseStep 3304307 = 4956461) B4956461
theorem B1739639 : Blo 1738570 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B1739659 : Blo 1738570 1739659 := bstep (se 1 (by rfl) ⟨1304744, by rfl⟩ : syracuseStep 1739659 = 2609489) B2609489
theorem B1739671 : Blo 1738570 1739671 := bstep (se 1 (by rfl) ⟨1304753, by rfl⟩ : syracuseStep 1739671 = 2609507) B2609507
theorem B2935703 : Blo 1738570 2935703 := bstep (se 1 (by rfl) ⟨2201777, by rfl⟩ : syracuseStep 2935703 = 4403555) B4403555
theorem B2608025 : Blo 1738570 2608025 := bstep (se 2 (by rfl) ⟨978009, by rfl⟩ : syracuseStep 2608025 = 1956019) B1956019
theorem B1739691 : Blo 1738570 1739691 := bstep (se 1 (by rfl) ⟨1304768, by rfl⟩ : syracuseStep 1739691 = 2609537) B2609537
theorem B3713971 : Blo 1738570 3713971 := bstep (se 1 (by rfl) ⟨2785478, by rfl⟩ : syracuseStep 3713971 = 5570957) B5570957
theorem B13388723 : Blo 1738570 13388723 := bstep (se 1 (by rfl) ⟨10041542, by rfl⟩ : syracuseStep 13388723 = 20083085) B20083085
theorem B1739703 : Blo 1738570 1739703 := bstep (se 1 (by rfl) ⟨1304777, by rfl⟩ : syracuseStep 1739703 = 2609555) B2609555
theorem B1739723 : Blo 1738570 1739723 := bstep (se 1 (by rfl) ⟨1304792, by rfl⟩ : syracuseStep 1739723 = 2609585) B2609585
theorem B1739735 : Blo 1738570 1739735 := bstep (se 1 (by rfl) ⟨1304801, by rfl⟩ : syracuseStep 1739735 = 2609603) B2609603
theorem B2477017 : Blo 1738570 2477017 := bstep (se 2 (by rfl) ⟨928881, by rfl⟩ : syracuseStep 2477017 = 1857763) B1857763
theorem B1739755 : Blo 1738570 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B1739767 : Blo 1738570 1739767 := bstep (se 1 (by rfl) ⟨1304825, by rfl⟩ : syracuseStep 1739767 = 2609651) B2609651
theorem B2608139 : Blo 1738570 2608139 := bstep (se 1 (by rfl) ⟨1956104, by rfl⟩ : syracuseStep 2608139 = 3912209) B3912209
theorem B1739787 : Blo 1738570 1739787 := bstep (se 1 (by rfl) ⟨1304840, by rfl⟩ : syracuseStep 1739787 = 2609681) B2609681
theorem B2608151 : Blo 1738570 2608151 := bstep (se 1 (by rfl) ⟨1956113, by rfl⟩ : syracuseStep 2608151 = 3912227) B3912227
theorem B2935831 : Blo 1738570 2935831 := bstep (se 1 (by rfl) ⟨2201873, by rfl⟩ : syracuseStep 2935831 = 4403747) B4403747
theorem B1739799 : Blo 1738570 1739799 := bstep (se 1 (by rfl) ⟨1304849, by rfl⟩ : syracuseStep 1739799 = 2609699) B2609699
theorem B1739819 : Blo 1738570 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B1739831 : Blo 1738570 1739831 := bstep (se 1 (by rfl) ⟨1304873, by rfl⟩ : syracuseStep 1739831 = 2609747) B2609747
theorem B1739851 : Blo 1738570 1739851 := bstep (se 1 (by rfl) ⟨1304888, by rfl⟩ : syracuseStep 1739851 = 2609777) B2609777
theorem B1739863 : Blo 1738570 1739863 := bstep (se 1 (by rfl) ⟨1304897, by rfl⟩ : syracuseStep 1739863 = 2609795) B2609795
theorem B2608217 : Blo 1738570 2608217 := bstep (se 2 (by rfl) ⟨978081, by rfl⟩ : syracuseStep 2608217 = 1956163) B1956163
theorem B1739883 : Blo 1738570 1739883 := bstep (se 1 (by rfl) ⟨1304912, by rfl⟩ : syracuseStep 1739883 = 2609825) B2609825
theorem B1739895 : Blo 1738570 1739895 := bstep (se 1 (by rfl) ⟨1304921, by rfl⟩ : syracuseStep 1739895 = 2609843) B2609843
theorem B1739915 : Blo 1738570 1739915 := bstep (se 1 (by rfl) ⟨1304936, by rfl⟩ : syracuseStep 1739915 = 2609873) B2609873
theorem B1739927 : Blo 1738570 1739927 := bstep (se 1 (by rfl) ⟨1304945, by rfl⟩ : syracuseStep 1739927 = 2609891) B2609891
theorem B1739947 : Blo 1738570 1739947 := bstep (se 1 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 1739947 = 2609921) B2609921
theorem B1739959 : Blo 1738570 1739959 := bstep (se 1 (by rfl) ⟨1304969, by rfl⟩ : syracuseStep 1739959 = 2609939) B2609939
theorem B2608331 : Blo 1738570 2608331 := bstep (se 1 (by rfl) ⟨1956248, by rfl⟩ : syracuseStep 2608331 = 3912497) B3912497
theorem B1739979 : Blo 1738570 1739979 := bstep (se 1 (by rfl) ⟨1304984, by rfl⟩ : syracuseStep 1739979 = 2609969) B2609969
theorem B2608343 : Blo 1738570 2608343 := bstep (se 1 (by rfl) ⟨1956257, by rfl⟩ : syracuseStep 2608343 = 3912515) B3912515
theorem B1739991 : Blo 1738570 1739991 := bstep (se 1 (by rfl) ⟨1304993, by rfl⟩ : syracuseStep 1739991 = 2609987) B2609987
theorem B5287133 : Blo 1738570 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B1740011 : Blo 1738570 1740011 := bstep (se 1 (by rfl) ⟨1305008, by rfl⟩ : syracuseStep 1740011 = 2610017) B2610017
theorem B1740023 : Blo 1738570 1740023 := bstep (se 1 (by rfl) ⟨1305017, by rfl⟩ : syracuseStep 1740023 = 2610035) B2610035
theorem B1740043 : Blo 1738570 1740043 := bstep (se 1 (by rfl) ⟨1305032, by rfl⟩ : syracuseStep 1740043 = 2610065) B2610065
theorem B1740055 : Blo 1738570 1740055 := bstep (se 1 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 1740055 = 2610083) B2610083
theorem B2608409 : Blo 1738570 2608409 := bstep (se 2 (by rfl) ⟨978153, by rfl⟩ : syracuseStep 2608409 = 1956307) B1956307
theorem B1740075 : Blo 1738570 1740075 := bstep (se 1 (by rfl) ⟨1305056, by rfl⟩ : syracuseStep 1740075 = 2610113) B2610113
theorem B22605101 : Blo 1738570 22605101 := bstep (se 3 (by rfl) ⟨4238456, by rfl⟩ : syracuseStep 22605101 = 8476913) B8476913
theorem B1740087 : Blo 1738570 1740087 := bstep (se 1 (by rfl) ⟨1305065, by rfl⟩ : syracuseStep 1740087 = 2610131) B2610131
theorem B1740107 : Blo 1738570 1740107 := bstep (se 1 (by rfl) ⟨1305080, by rfl⟩ : syracuseStep 1740107 = 2610161) B2610161
theorem B1740119 : Blo 1738570 1740119 := bstep (se 1 (by rfl) ⟨1305089, by rfl⟩ : syracuseStep 1740119 = 2610179) B2610179
theorem B1740139 : Blo 1738570 1740139 := bstep (se 1 (by rfl) ⟨1305104, by rfl⟩ : syracuseStep 1740139 = 2610209) B2610209
theorem B1740151 : Blo 1738570 1740151 := bstep (se 1 (by rfl) ⟨1305113, by rfl⟩ : syracuseStep 1740151 = 2610227) B2610227
theorem B2608523 : Blo 1738570 2608523 := bstep (se 1 (by rfl) ⟨1956392, by rfl⟩ : syracuseStep 2608523 = 3912785) B3912785
theorem B1740171 : Blo 1738570 1740171 := bstep (se 1 (by rfl) ⟨1305128, by rfl⟩ : syracuseStep 1740171 = 2610257) B2610257
theorem B2608535 : Blo 1738570 2608535 := bstep (se 1 (by rfl) ⟨1956401, by rfl⟩ : syracuseStep 2608535 = 3912803) B3912803
theorem B4402583 : Blo 1738570 4402583 := bstep (se 1 (by rfl) ⟨3301937, by rfl⟩ : syracuseStep 4402583 = 6603875) B6603875
theorem B1740183 : Blo 1738570 1740183 := bstep (se 1 (by rfl) ⟨1305137, by rfl⟩ : syracuseStep 1740183 = 2610275) B2610275
theorem B1740203 : Blo 1738570 1740203 := bstep (se 1 (by rfl) ⟨1305152, by rfl⟩ : syracuseStep 1740203 = 2610305) B2610305
theorem B25079219 : Blo 1738570 25079219 := bstep (se 1 (by rfl) ⟨18809414, by rfl⟩ : syracuseStep 25079219 = 37618829) B37618829
theorem B1740215 : Blo 1738570 1740215 := bstep (se 1 (by rfl) ⟨1305161, by rfl⟩ : syracuseStep 1740215 = 2610323) B2610323
theorem B1740235 : Blo 1738570 1740235 := bstep (se 1 (by rfl) ⟨1305176, by rfl⟩ : syracuseStep 1740235 = 2610353) B2610353
theorem B1740247 : Blo 1738570 1740247 := bstep (se 1 (by rfl) ⟨1305185, by rfl⟩ : syracuseStep 1740247 = 2610371) B2610371
theorem B2608601 : Blo 1738570 2608601 := bstep (se 2 (by rfl) ⟨978225, by rfl⟩ : syracuseStep 2608601 = 1956451) B1956451
theorem B2977241 : Blo 1738570 2977241 := bstep (se 2 (by rfl) ⟨1116465, by rfl⟩ : syracuseStep 2977241 = 2232931) B2232931
theorem B5574109 : Blo 1738570 5574109 := bstep (se 3 (by rfl) ⟨1045145, by rfl⟩ : syracuseStep 5574109 = 2090291) B2090291
theorem B1740267 : Blo 1738570 1740267 := bstep (se 1 (by rfl) ⟨1305200, by rfl⟩ : syracuseStep 1740267 = 2610401) B2610401
theorem B1740279 : Blo 1738570 1740279 := bstep (se 1 (by rfl) ⟨1305209, by rfl⟩ : syracuseStep 1740279 = 2610419) B2610419
theorem B1740299 : Blo 1738570 1740299 := bstep (se 1 (by rfl) ⟨1305224, by rfl⟩ : syracuseStep 1740299 = 2610449) B2610449
theorem B1740311 : Blo 1738570 1740311 := bstep (se 1 (by rfl) ⟨1305233, by rfl⟩ : syracuseStep 1740311 = 2610467) B2610467
theorem B1740331 : Blo 1738570 1740331 := bstep (se 1 (by rfl) ⟨1305248, by rfl⟩ : syracuseStep 1740331 = 2610497) B2610497
theorem B1740343 : Blo 1738570 1740343 := bstep (se 1 (by rfl) ⟨1305257, by rfl⟩ : syracuseStep 1740343 = 2610515) B2610515
theorem B2608715 : Blo 1738570 2608715 := bstep (se 1 (by rfl) ⟨1956536, by rfl⟩ : syracuseStep 2608715 = 3913073) B3913073
theorem B1740363 : Blo 1738570 1740363 := bstep (se 1 (by rfl) ⟨1305272, by rfl⟩ : syracuseStep 1740363 = 2610545) B2610545
theorem B7056971 : Blo 1738570 7056971 := bstep (se 1 (by rfl) ⟨5292728, by rfl⟩ : syracuseStep 7056971 = 10585457) B10585457
theorem B2608727 : Blo 1738570 2608727 := bstep (se 1 (by rfl) ⟨1956545, by rfl⟩ : syracuseStep 2608727 = 3913091) B3913091
theorem B1740375 : Blo 1738570 1740375 := bstep (se 1 (by rfl) ⟨1305281, by rfl⟩ : syracuseStep 1740375 = 2610563) B2610563
theorem B1740395 : Blo 1738570 1740395 := bstep (se 1 (by rfl) ⟨1305296, by rfl⟩ : syracuseStep 1740395 = 2610593) B2610593
theorem B1740407 : Blo 1738570 1740407 := bstep (se 1 (by rfl) ⟨1305305, by rfl⟩ : syracuseStep 1740407 = 2610611) B2610611
theorem B2936459 : Blo 1738570 2936459 := bstep (se 1 (by rfl) ⟨2202344, by rfl⟩ : syracuseStep 2936459 = 4404689) B4404689
theorem B1740427 : Blo 1738570 1740427 := bstep (se 1 (by rfl) ⟨1305320, by rfl⟩ : syracuseStep 1740427 = 2610641) B2610641
theorem B1740439 : Blo 1738570 1740439 := bstep (se 1 (by rfl) ⟨1305329, by rfl⟩ : syracuseStep 1740439 = 2610659) B2610659
theorem B2608793 : Blo 1738570 2608793 := bstep (se 2 (by rfl) ⟨978297, by rfl⟩ : syracuseStep 2608793 = 1956595) B1956595
theorem B1740459 : Blo 1738570 1740459 := bstep (se 1 (by rfl) ⟨1305344, by rfl⟩ : syracuseStep 1740459 = 2610689) B2610689
theorem B1740471 : Blo 1738570 1740471 := bstep (se 1 (by rfl) ⟨1305353, by rfl⟩ : syracuseStep 1740471 = 2610707) B2610707
theorem B5869259 : Blo 1738570 5869259 := bstep (se 1 (by rfl) ⟨4401944, by rfl⟩ : syracuseStep 5869259 = 8803889) B8803889
theorem B1740491 : Blo 1738570 1740491 := bstep (se 1 (by rfl) ⟨1305368, by rfl⟩ : syracuseStep 1740491 = 2610737) B2610737
theorem B1740503 : Blo 1738570 1740503 := bstep (se 1 (by rfl) ⟨1305377, by rfl⟩ : syracuseStep 1740503 = 2610755) B2610755
theorem B1740523 : Blo 1738570 1740523 := bstep (se 1 (by rfl) ⟨1305392, by rfl⟩ : syracuseStep 1740523 = 2610785) B2610785
theorem B1740535 : Blo 1738570 1740535 := bstep (se 1 (by rfl) ⟨1305401, by rfl⟩ : syracuseStep 1740535 = 2610803) B2610803
theorem B3714817 : Blo 1738570 3714817 := bstep (se 2 (by rfl) ⟨1393056, by rfl⟩ : syracuseStep 3714817 = 2786113) B2786113
theorem B2608907 : Blo 1738570 2608907 := bstep (se 1 (by rfl) ⟨1956680, by rfl⟩ : syracuseStep 2608907 = 3913361) B3913361
theorem B2936587 : Blo 1738570 2936587 := bstep (se 1 (by rfl) ⟨2202440, by rfl⟩ : syracuseStep 2936587 = 4404881) B4404881
theorem B1740555 : Blo 1738570 1740555 := bstep (se 1 (by rfl) ⟨1305416, by rfl⟩ : syracuseStep 1740555 = 2610833) B2610833
theorem B2608919 : Blo 1738570 2608919 := bstep (se 1 (by rfl) ⟨1956689, by rfl⟩ : syracuseStep 2608919 = 3913379) B3913379
theorem B1740567 : Blo 1738570 1740567 := bstep (se 1 (by rfl) ⟨1305425, by rfl⟩ : syracuseStep 1740567 = 2610851) B2610851
theorem B2608985 : Blo 1738570 2608985 := bstep (se 2 (by rfl) ⟨978369, by rfl⟩ : syracuseStep 2608985 = 1956739) B1956739
theorem B2936729 : Blo 1738570 2936729 := bstep (se 2 (by rfl) ⟨1101273, by rfl⟩ : syracuseStep 2936729 = 2202547) B2202547
theorem B2609099 : Blo 1738570 2609099 := bstep (se 1 (by rfl) ⟨1956824, by rfl⟩ : syracuseStep 2609099 = 3913649) B3913649
theorem B2609111 : Blo 1738570 2609111 := bstep (se 1 (by rfl) ⟨1956833, by rfl⟩ : syracuseStep 2609111 = 3913667) B3913667
theorem B5869529 : Blo 1738570 5869529 := bstep (se 2 (by rfl) ⟨2201073, by rfl⟩ : syracuseStep 5869529 = 4402147) B4402147
theorem B4952029 : Blo 1738570 4952029 := bstep (se 3 (by rfl) ⟨928505, by rfl⟩ : syracuseStep 4952029 = 1857011) B1857011
theorem B4952087 : Blo 1738570 4952087 := bstep (se 1 (by rfl) ⟨3714065, by rfl⟩ : syracuseStep 4952087 = 7428131) B7428131
theorem B2609177 : Blo 1738570 2609177 := bstep (se 2 (by rfl) ⟨978441, by rfl⟩ : syracuseStep 2609177 = 1956883) B1956883
theorem B2936857 : Blo 1738570 2936857 := bstep (se 2 (by rfl) ⟨1101321, by rfl⟩ : syracuseStep 2936857 = 2202643) B2202643
theorem B50147363 : Blo 1738570 50147363 := bstep (se 1 (by rfl) ⟨37610522, by rfl⟩ : syracuseStep 50147363 = 75221045) B75221045
theorem B3715159 : Blo 1738570 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B3911795 : Blo 1738570 3911795 := bstep (se 1 (by rfl) ⟨2933846, by rfl⟩ : syracuseStep 3911795 = 5867693) B5867693
theorem B11145347 : Blo 1738570 11145347 := bstep (se 1 (by rfl) ⟨8359010, by rfl⟩ : syracuseStep 11145347 = 16718021) B16718021
theorem B2609291 : Blo 1738570 2609291 := bstep (se 1 (by rfl) ⟨1956968, by rfl⟩ : syracuseStep 2609291 = 3913937) B3913937
theorem B3911831 : Blo 1738570 3911831 := bstep (se 1 (by rfl) ⟨2933873, by rfl⟩ : syracuseStep 3911831 = 5867747) B5867747
theorem B2609303 : Blo 1738570 2609303 := bstep (se 1 (by rfl) ⟨1956977, by rfl⟩ : syracuseStep 2609303 = 3913955) B3913955
theorem B4403393 : Blo 1738570 4403393 := bstep (se 2 (by rfl) ⟨1651272, by rfl⟩ : syracuseStep 4403393 = 3302545) B3302545
theorem B7434433 : Blo 1738570 7434433 := bstep (se 2 (by rfl) ⟨2787912, by rfl⟩ : syracuseStep 7434433 = 5575825) B5575825
theorem B2609369 : Blo 1738570 2609369 := bstep (se 2 (by rfl) ⟨978513, by rfl⟩ : syracuseStep 2609369 = 1957027) B1957027
theorem B3912011 : Blo 1738570 3912011 := bstep (se 1 (by rfl) ⟨2934008, by rfl⟩ : syracuseStep 3912011 = 5868017) B5868017
theorem B2609483 : Blo 1738570 2609483 := bstep (se 1 (by rfl) ⟨1957112, by rfl⟩ : syracuseStep 2609483 = 3914225) B3914225
theorem B2609495 : Blo 1738570 2609495 := bstep (se 1 (by rfl) ⟨1957121, by rfl⟩ : syracuseStep 2609495 = 3914243) B3914243
theorem B3912065 : Blo 1738570 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B2609561 : Blo 1738570 2609561 := bstep (se 2 (by rfl) ⟨978585, by rfl⟩ : syracuseStep 2609561 = 1957171) B1957171
theorem B6607277 : Blo 1738570 6607277 := bstep (se 3 (by rfl) ⟨1238864, by rfl⟩ : syracuseStep 6607277 = 2477729) B2477729
theorem B50180579 : Blo 1738570 50180579 := bstep (se 1 (by rfl) ⟨37635434, by rfl⟩ : syracuseStep 50180579 = 75270869) B75270869
theorem B2609675 : Blo 1738570 2609675 := bstep (se 1 (by rfl) ⟨1957256, by rfl⟩ : syracuseStep 2609675 = 3914513) B3914513
theorem B2609687 : Blo 1738570 2609687 := bstep (se 1 (by rfl) ⟨1957265, by rfl⟩ : syracuseStep 2609687 = 3914531) B3914531
theorem B3912281 : Blo 1738570 3912281 := bstep (se 2 (by rfl) ⟨1467105, by rfl⟩ : syracuseStep 3912281 = 2934211) B2934211
theorem B2609753 : Blo 1738570 2609753 := bstep (se 2 (by rfl) ⟨978657, by rfl⟩ : syracuseStep 2609753 = 1957315) B1957315
theorem B5870231 : Blo 1738570 5870231 := bstep (se 1 (by rfl) ⟨4402673, by rfl⟩ : syracuseStep 5870231 = 8805347) B8805347
theorem B3912371 : Blo 1738570 3912371 := bstep (se 1 (by rfl) ⟨2934278, by rfl⟩ : syracuseStep 3912371 = 5868557) B5868557
theorem B2609867 : Blo 1738570 2609867 := bstep (se 1 (by rfl) ⟨1957400, by rfl⟩ : syracuseStep 2609867 = 3914801) B3914801
theorem B3912407 : Blo 1738570 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B2609879 : Blo 1738570 2609879 := bstep (se 1 (by rfl) ⟨1957409, by rfl⟩ : syracuseStep 2609879 = 3914819) B3914819
theorem B4403929 : Blo 1738570 4403929 := bstep (se 2 (by rfl) ⟨1651473, by rfl⟩ : syracuseStep 4403929 = 3302947) B3302947
theorem B2609945 : Blo 1738570 2609945 := bstep (se 2 (by rfl) ⟨978729, by rfl⟩ : syracuseStep 2609945 = 1957459) B1957459
theorem B53547875 : Blo 1738570 53547875 := bstep (se 1 (by rfl) ⟨40160906, by rfl⟩ : syracuseStep 53547875 = 80321813) B80321813
theorem B32158565 : Blo 1738570 32158565 := bstep (se 4 (by rfl) ⟨3014865, by rfl⟩ : syracuseStep 32158565 = 6029731) B6029731
theorem B3912587 : Blo 1738570 3912587 := bstep (se 1 (by rfl) ⟨2934440, by rfl⟩ : syracuseStep 3912587 = 5868881) B5868881
theorem B2610059 : Blo 1738570 2610059 := bstep (se 1 (by rfl) ⟨1957544, by rfl⟩ : syracuseStep 2610059 = 3915089) B3915089
theorem B2610071 : Blo 1738570 2610071 := bstep (se 1 (by rfl) ⟨1957553, by rfl⟩ : syracuseStep 2610071 = 3915107) B3915107
theorem B3912641 : Blo 1738570 3912641 := bstep (se 2 (by rfl) ⟨1467240, by rfl⟩ : syracuseStep 3912641 = 2934481) B2934481
theorem B2610137 : Blo 1738570 2610137 := bstep (se 2 (by rfl) ⟨978801, by rfl⟩ : syracuseStep 2610137 = 1957603) B1957603
theorem B8803403 : Blo 1738570 8803403 := bstep (se 1 (by rfl) ⟨6602552, by rfl⟩ : syracuseStep 8803403 = 13205105) B13205105
theorem B3527755 : Blo 1738570 3527755 := bstep (se 1 (by rfl) ⟨2645816, by rfl⟩ : syracuseStep 3527755 = 5291633) B5291633
theorem B2610251 : Blo 1738570 2610251 := bstep (se 1 (by rfl) ⟨1957688, by rfl⟩ : syracuseStep 2610251 = 3915377) B3915377
theorem B2610263 : Blo 1738570 2610263 := bstep (se 1 (by rfl) ⟨1957697, by rfl⟩ : syracuseStep 2610263 = 3915395) B3915395
theorem B16094339 : Blo 1738570 16094339 := bstep (se 1 (by rfl) ⟨12070754, by rfl⟩ : syracuseStep 16094339 = 24141509) B24141509
theorem B3912857 : Blo 1738570 3912857 := bstep (se 2 (by rfl) ⟨1467321, by rfl⟩ : syracuseStep 3912857 = 2934643) B2934643
theorem B2610329 : Blo 1738570 2610329 := bstep (se 2 (by rfl) ⟨978873, by rfl⟩ : syracuseStep 2610329 = 1957747) B1957747
theorem B5870771 : Blo 1738570 5870771 := bstep (se 1 (by rfl) ⟨4403078, by rfl⟩ : syracuseStep 5870771 = 8806157) B8806157
theorem B7935155 : Blo 1738570 7935155 := bstep (se 1 (by rfl) ⟨5951366, by rfl⟩ : syracuseStep 7935155 = 11902733) B11902733
theorem B6608051 : Blo 1738570 6608051 := bstep (se 1 (by rfl) ⟨4956038, by rfl⟩ : syracuseStep 6608051 = 9912077) B9912077
theorem B4953305 : Blo 1738570 4953305 := bstep (se 2 (by rfl) ⟨1857489, by rfl⟩ : syracuseStep 4953305 = 3714979) B3714979
theorem B3912947 : Blo 1738570 3912947 := bstep (se 1 (by rfl) ⟨2934710, by rfl⟩ : syracuseStep 3912947 = 5869421) B5869421
theorem B3716363 : Blo 1738570 3716363 := bstep (se 1 (by rfl) ⟨2787272, by rfl⟩ : syracuseStep 3716363 = 5574545) B5574545
theorem B2610443 : Blo 1738570 2610443 := bstep (se 1 (by rfl) ⟨1957832, by rfl⟩ : syracuseStep 2610443 = 3915665) B3915665
theorem B3912983 : Blo 1738570 3912983 := bstep (se 1 (by rfl) ⟨2934737, by rfl⟩ : syracuseStep 3912983 = 5869475) B5869475
theorem B2610455 : Blo 1738570 2610455 := bstep (se 1 (by rfl) ⟨1957841, by rfl⟩ : syracuseStep 2610455 = 3915683) B3915683
theorem B4953419 : Blo 1738570 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B2610521 : Blo 1738570 2610521 := bstep (se 2 (by rfl) ⟨978945, by rfl⟩ : syracuseStep 2610521 = 1957891) B1957891
theorem B5871041 : Blo 1738570 5871041 := bstep (se 2 (by rfl) ⟨2201640, by rfl⟩ : syracuseStep 5871041 = 4403281) B4403281
theorem B7427531 : Blo 1738570 7427531 := bstep (se 1 (by rfl) ⟨5570648, by rfl⟩ : syracuseStep 7427531 = 11141297) B11141297
theorem B3913163 : Blo 1738570 3913163 := bstep (se 1 (by rfl) ⟨2934872, by rfl⟩ : syracuseStep 3913163 = 5869745) B5869745
theorem B2610635 : Blo 1738570 2610635 := bstep (se 1 (by rfl) ⟨1957976, by rfl⟩ : syracuseStep 2610635 = 3915953) B3915953
theorem B2610647 : Blo 1738570 2610647 := bstep (se 1 (by rfl) ⟨1957985, by rfl⟩ : syracuseStep 2610647 = 3915971) B3915971
theorem B3913217 : Blo 1738570 3913217 := bstep (se 2 (by rfl) ⟨1467456, by rfl⟩ : syracuseStep 3913217 = 2934913) B2934913
theorem B2643481 : Blo 1738570 2643481 := bstep (se 2 (by rfl) ⟨991305, by rfl⟩ : syracuseStep 2643481 = 1982611) B1982611
theorem B2610713 : Blo 1738570 2610713 := bstep (se 2 (by rfl) ⟨979017, by rfl⟩ : syracuseStep 2610713 = 1958035) B1958035
theorem B5289565 : Blo 1738570 5289565 := bstep (se 3 (by rfl) ⟨991793, by rfl⟩ : syracuseStep 5289565 = 1983587) B1983587
theorem B2610827 : Blo 1738570 2610827 := bstep (se 1 (by rfl) ⟨1958120, by rfl⟩ : syracuseStep 2610827 = 3916241) B3916241
theorem B3348119 : Blo 1738570 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2610839 : Blo 1738570 2610839 := bstep (se 1 (by rfl) ⟨1958129, by rfl⟩ : syracuseStep 2610839 = 3916259) B3916259
theorem B63461069 : Blo 1738570 63461069 := bstep (se 3 (by rfl) ⟨11898950, by rfl⟩ : syracuseStep 63461069 = 23797901) B23797901
theorem B3135191 : Blo 1738570 3135191 := bstep (se 1 (by rfl) ⟨2351393, by rfl⟩ : syracuseStep 3135191 = 4702787) B4702787
theorem B13203161 : Blo 1738570 13203161 := bstep (se 2 (by rfl) ⟨4951185, by rfl⟩ : syracuseStep 13203161 = 9902371) B9902371
theorem B3913433 : Blo 1738570 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B1857259 : Blo 1738570 1857259 := bstep (se 1 (by rfl) ⟨1392944, by rfl⟩ : syracuseStep 1857259 = 2785889) B2785889
theorem B3716875 : Blo 1738570 3716875 := bstep (se 1 (by rfl) ⟨2787656, by rfl⟩ : syracuseStep 3716875 = 5575313) B5575313
theorem B3913523 : Blo 1738570 3913523 := bstep (se 1 (by rfl) ⟨2935142, by rfl⟩ : syracuseStep 3913523 = 5870285) B5870285
theorem B4405043 : Blo 1738570 4405043 := bstep (se 1 (by rfl) ⟨3303782, by rfl⟩ : syracuseStep 4405043 = 6607565) B6607565
theorem B3913559 : Blo 1738570 3913559 := bstep (se 1 (by rfl) ⟨2935169, by rfl⟩ : syracuseStep 3913559 = 5870339) B5870339
theorem B3528535 : Blo 1738570 3528535 := bstep (se 1 (by rfl) ⟨2646401, by rfl⟩ : syracuseStep 3528535 = 5292803) B5292803
theorem B10581853 : Blo 1738570 10581853 := bstep (se 3 (by rfl) ⟨1984097, by rfl⟩ : syracuseStep 10581853 = 3968195) B3968195
theorem B14112643 : Blo 1738570 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B21149657 : Blo 1738570 21149657 := bstep (se 2 (by rfl) ⟨7931121, by rfl⟩ : syracuseStep 21149657 = 15862243) B15862243
theorem B5650393 : Blo 1738570 5650393 := bstep (se 2 (by rfl) ⟨2118897, by rfl⟩ : syracuseStep 5650393 = 4237795) B4237795
theorem B5871581 : Blo 1738570 5871581 := bstep (se 3 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 5871581 = 2201843) B2201843
theorem B3913739 : Blo 1738570 3913739 := bstep (se 1 (by rfl) ⟨2935304, by rfl⟩ : syracuseStep 3913739 = 5870609) B5870609
theorem B3913793 : Blo 1738570 3913793 := bstep (se 2 (by rfl) ⟨1467672, by rfl⟩ : syracuseStep 3913793 = 2935345) B2935345
theorem B4405337 : Blo 1738570 4405337 := bstep (se 2 (by rfl) ⟨1652001, by rfl⟩ : syracuseStep 4405337 = 3304003) B3304003
theorem B1955947 : Blo 1738570 1955947 := bstep (se 1 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 1955947 = 2933921) B2933921
theorem B2291915 : Blo 1738570 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B1956055 : Blo 1738570 1956055 := bstep (se 1 (by rfl) ⟨1467041, by rfl⟩ : syracuseStep 1956055 = 2934083) B2934083
theorem B13211909 : Blo 1738570 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B3914009 : Blo 1738570 3914009 := bstep (se 2 (by rfl) ⟨1467753, by rfl⟩ : syracuseStep 3914009 = 2935507) B2935507
theorem B3914099 : Blo 1738570 3914099 := bstep (se 1 (by rfl) ⟨2935574, by rfl⟩ : syracuseStep 3914099 = 5871149) B5871149
theorem B1956235 : Blo 1738570 1956235 := bstep (se 1 (by rfl) ⟨1467176, by rfl⟩ : syracuseStep 1956235 = 2934353) B2934353
theorem B2201995 : Blo 1738570 2201995 := bstep (se 1 (by rfl) ⟨1651496, by rfl⟩ : syracuseStep 2201995 = 3302993) B3302993
theorem B3135883 : Blo 1738570 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B3914135 : Blo 1738570 3914135 := bstep (se 1 (by rfl) ⟨2935601, by rfl⟩ : syracuseStep 3914135 = 5871203) B5871203
theorem B3176857 : Blo 1738570 3176857 := bstep (se 2 (by rfl) ⟨1191321, by rfl⟩ : syracuseStep 3176857 = 2382643) B2382643
theorem B4954547 : Blo 1738570 4954547 := bstep (se 1 (by rfl) ⟨3715910, by rfl⟩ : syracuseStep 4954547 = 7431821) B7431821
theorem B1956343 : Blo 1738570 1956343 := bstep (se 1 (by rfl) ⟨1467257, by rfl⟩ : syracuseStep 1956343 = 2934515) B2934515
theorem B12532229 : Blo 1738570 12532229 := bstep (se 4 (by rfl) ⟨1174896, by rfl⟩ : syracuseStep 12532229 = 2349793) B2349793
theorem B3914315 : Blo 1738570 3914315 := bstep (se 1 (by rfl) ⟨2935736, by rfl⟩ : syracuseStep 3914315 = 5871473) B5871473
theorem B2415193 : Blo 1738570 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B43489885 : Blo 1738570 43489885 := bstep (se 3 (by rfl) ⟨8154353, by rfl⟩ : syracuseStep 43489885 = 16308707) B16308707
theorem B3914369 : Blo 1738570 3914369 := bstep (se 2 (by rfl) ⟨1467888, by rfl⟩ : syracuseStep 3914369 = 2935777) B2935777
theorem B1956523 : Blo 1738570 1956523 := bstep (se 1 (by rfl) ⟨1467392, by rfl⟩ : syracuseStep 1956523 = 2934785) B2934785
theorem B7428829 : Blo 1738570 7428829 := bstep (se 3 (by rfl) ⟨1392905, by rfl⟩ : syracuseStep 7428829 = 2785811) B2785811
theorem B1956631 : Blo 1738570 1956631 := bstep (se 1 (by rfl) ⟨1467473, by rfl⟩ : syracuseStep 1956631 = 2934947) B2934947
theorem B8805185 : Blo 1738570 8805185 := bstep (se 2 (by rfl) ⟨3301944, by rfl⟩ : syracuseStep 8805185 = 6603889) B6603889
theorem B12540737 : Blo 1738570 12540737 := bstep (se 2 (by rfl) ⟨4702776, by rfl⟩ : syracuseStep 12540737 = 9405553) B9405553
theorem B4954945 : Blo 1738570 4954945 := bstep (se 2 (by rfl) ⟨1858104, by rfl⟩ : syracuseStep 4954945 = 3716209) B3716209
theorem B3914585 : Blo 1738570 3914585 := bstep (se 2 (by rfl) ⟨1467969, by rfl⟩ : syracuseStep 3914585 = 2935939) B2935939
theorem B3914675 : Blo 1738570 3914675 := bstep (se 1 (by rfl) ⟨2936006, by rfl⟩ : syracuseStep 3914675 = 5872013) B5872013
theorem B1956811 : Blo 1738570 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B3914711 : Blo 1738570 3914711 := bstep (se 1 (by rfl) ⟨2936033, by rfl⟩ : syracuseStep 3914711 = 5872067) B5872067
theorem B14302169 : Blo 1738570 14302169 := bstep (se 2 (by rfl) ⟨5363313, by rfl⟩ : syracuseStep 14302169 = 10726627) B10726627
theorem B2350091 : Blo 1738570 2350091 := bstep (se 1 (by rfl) ⟨1762568, by rfl⟩ : syracuseStep 2350091 = 3525137) B3525137
theorem B1858583 : Blo 1738570 1858583 := bstep (se 1 (by rfl) ⟨1393937, by rfl⟩ : syracuseStep 1858583 = 2787875) B2787875
theorem B7429171 : Blo 1738570 7429171 := bstep (se 1 (by rfl) ⟨5571878, by rfl⟩ : syracuseStep 7429171 = 11143757) B11143757
theorem B1956919 : Blo 1738570 1956919 := bstep (se 1 (by rfl) ⟨1467689, by rfl⟩ : syracuseStep 1956919 = 2935379) B2935379
theorem B5872715 : Blo 1738570 5872715 := bstep (se 1 (by rfl) ⟨4404536, by rfl⟩ : syracuseStep 5872715 = 8809073) B8809073
theorem B3914891 : Blo 1738570 3914891 := bstep (se 1 (by rfl) ⟨2936168, by rfl⟩ : syracuseStep 3914891 = 5872337) B5872337
theorem B3914945 : Blo 1738570 3914945 := bstep (se 2 (by rfl) ⟨1468104, by rfl⟩ : syracuseStep 3914945 = 2936209) B2936209
theorem B6601931 : Blo 1738570 6601931 := bstep (se 1 (by rfl) ⟨4951448, by rfl⟩ : syracuseStep 6601931 = 9902897) B9902897
theorem B6601945 : Blo 1738570 6601945 := bstep (se 2 (by rfl) ⟨2475729, by rfl⟩ : syracuseStep 6601945 = 4951459) B4951459
theorem B1957099 : Blo 1738570 1957099 := bstep (se 1 (by rfl) ⟨1467824, by rfl⟩ : syracuseStep 1957099 = 2935649) B2935649
theorem B7052609 : Blo 1738570 7052609 := bstep (se 2 (by rfl) ⟨2644728, by rfl⟩ : syracuseStep 7052609 = 5289457) B5289457
theorem B1957207 : Blo 1738570 1957207 := bstep (se 1 (by rfl) ⟨1467905, by rfl⟩ : syracuseStep 1957207 = 2935811) B2935811
theorem B5872985 : Blo 1738570 5872985 := bstep (se 2 (by rfl) ⟨2202369, by rfl⟩ : syracuseStep 5872985 = 4404739) B4404739
theorem B9911645 : Blo 1738570 9911645 := bstep (se 3 (by rfl) ⟨1858433, by rfl⟩ : syracuseStep 9911645 = 3716867) B3716867
theorem B171589013 : Blo 1738570 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B3915161 : Blo 1738570 3915161 := bstep (se 2 (by rfl) ⟨1468185, by rfl⟩ : syracuseStep 3915161 = 2936371) B2936371
theorem B5570009 : Blo 1738570 5570009 := bstep (se 2 (by rfl) ⟨2088753, by rfl⟩ : syracuseStep 5570009 = 4177507) B4177507
theorem B3300851 : Blo 1738570 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B3915251 : Blo 1738570 3915251 := bstep (se 1 (by rfl) ⟨2936438, by rfl⟩ : syracuseStep 3915251 = 5872877) B5872877
theorem B1957387 : Blo 1738570 1957387 := bstep (se 1 (by rfl) ⟨1468040, by rfl⟩ : syracuseStep 1957387 = 2936081) B2936081
theorem B18808337 : Blo 1738570 18808337 := bstep (se 2 (by rfl) ⟨7053126, by rfl⟩ : syracuseStep 18808337 = 14106253) B14106253
theorem B3915287 : Blo 1738570 3915287 := bstep (se 1 (by rfl) ⟨2936465, by rfl⟩ : syracuseStep 3915287 = 5872931) B5872931
theorem B1957495 : Blo 1738570 1957495 := bstep (se 1 (by rfl) ⟨1468121, by rfl⟩ : syracuseStep 1957495 = 2936243) B2936243
theorem B3301003 : Blo 1738570 3301003 := bstep (se 1 (by rfl) ⟨2475752, by rfl⟩ : syracuseStep 3301003 = 4951505) B4951505
theorem B3915467 : Blo 1738570 3915467 := bstep (se 1 (by rfl) ⟨2936600, by rfl⟩ : syracuseStep 3915467 = 5873201) B5873201
theorem B3915521 : Blo 1738570 3915521 := bstep (se 2 (by rfl) ⟨1468320, by rfl⟩ : syracuseStep 3915521 = 2936641) B2936641
theorem B1957675 : Blo 1738570 1957675 := bstep (se 1 (by rfl) ⟨1468256, by rfl⟩ : syracuseStep 1957675 = 2936513) B2936513
theorem B31727459 : Blo 1738570 31727459 := bstep (se 1 (by rfl) ⟨23795594, by rfl⟩ : syracuseStep 31727459 = 47591189) B47591189
theorem B1957783 : Blo 1738570 1957783 := bstep (se 1 (by rfl) ⟨1468337, by rfl⟩ : syracuseStep 1957783 = 2936675) B2936675
theorem B14106545 : Blo 1738570 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B3301337 : Blo 1738570 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B3915737 : Blo 1738570 3915737 := bstep (se 2 (by rfl) ⟨1468401, by rfl⟩ : syracuseStep 3915737 = 2936803) B2936803
theorem B3301391 : Blo 1738570 3301391 := bstep (se 1 (by rfl) ⟨2476043, by rfl⟩ : syracuseStep 3301391 = 4952087) B4952087
theorem B5292047 : Blo 1738570 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B3915791 : Blo 1738570 3915791 := bstep (se 1 (by rfl) ⟨2936843, by rfl⟩ : syracuseStep 3915791 = 5873687) B5873687
theorem B33431575 : Blo 1738570 33431575 := bstep (se 1 (by rfl) ⟨25073681, by rfl⟩ : syracuseStep 33431575 = 50147363) B50147363
theorem B6266909 : Blo 1738570 6266909 := bstep (se 3 (by rfl) ⟨1175045, by rfl⟩ : syracuseStep 6266909 = 2350091) B2350091
theorem B3915809 : Blo 1738570 3915809 := bstep (se 2 (by rfl) ⟨1468428, by rfl⟩ : syracuseStep 3915809 = 2936857) B2936857
theorem B4956221 : Blo 1738570 4956221 := bstep (se 3 (by rfl) ⟨929291, by rfl⟩ : syracuseStep 4956221 = 1858583) B1858583
theorem B13205591 : Blo 1738570 13205591 := bstep (se 1 (by rfl) ⟨9904193, by rfl⟩ : syracuseStep 13205591 = 19808387) B19808387
theorem B7430231 : Blo 1738570 7430231 := bstep (se 1 (by rfl) ⟨5572673, by rfl⟩ : syracuseStep 7430231 = 11145347) B11145347
theorem B9912577 : Blo 1738570 9912577 := bstep (se 2 (by rfl) ⟨3717216, by rfl⟩ : syracuseStep 9912577 = 7434433) B7434433
theorem B3916151 : Blo 1738570 3916151 := bstep (se 1 (by rfl) ⟨2937113, by rfl⟩ : syracuseStep 3916151 = 5874227) B5874227
theorem B8356243 : Blo 1738570 8356243 := bstep (se 1 (by rfl) ⟨6267182, by rfl⟩ : syracuseStep 8356243 = 12534365) B12534365
theorem B6111773 : Blo 1738570 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B4235809 : Blo 1738570 4235809 := bstep (se 2 (by rfl) ⟨1588428, by rfl⟩ : syracuseStep 4235809 = 3176857) B3176857
theorem B21439043 : Blo 1738570 21439043 := bstep (se 1 (by rfl) ⟨16079282, by rfl⟩ : syracuseStep 21439043 = 32158565) B32158565
theorem B14099021 : Blo 1738570 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B2785927 : Blo 1738570 2785927 := bstep (se 1 (by rfl) ⟨2089445, by rfl⟩ : syracuseStep 2785927 = 4178891) B4178891
theorem B20087513 : Blo 1738570 20087513 := bstep (se 2 (by rfl) ⟨7532817, by rfl⟩ : syracuseStep 20087513 = 15065635) B15065635
theorem B3302203 : Blo 1738570 3302203 := bstep (se 1 (by rfl) ⟨2476652, by rfl⟩ : syracuseStep 3302203 = 4953305) B4953305
theorem B5571443 : Blo 1738570 5571443 := bstep (se 1 (by rfl) ⟨4178582, by rfl⟩ : syracuseStep 5571443 = 8357165) B8357165
theorem B3302279 : Blo 1738570 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B4703123 : Blo 1738570 4703123 := bstep (se 1 (by rfl) ⟨3527342, by rfl⟩ : syracuseStep 4703123 = 7054685) B7054685
theorem B9905105 : Blo 1738570 9905105 := bstep (se 2 (by rfl) ⟨3714414, by rfl⟩ : syracuseStep 9905105 = 7428829) B7428829
theorem B8807453 : Blo 1738570 8807453 := bstep (se 3 (by rfl) ⟨1651397, by rfl⟩ : syracuseStep 8807453 = 3302795) B3302795
theorem B7939309 : Blo 1738570 7939309 := bstep (se 3 (by rfl) ⟨1488620, by rfl⟩ : syracuseStep 7939309 = 2977241) B2977241
theorem B3302689 : Blo 1738570 3302689 := bstep (se 2 (by rfl) ⟨1238508, by rfl⟩ : syracuseStep 3302689 = 2477017) B2477017
theorem B14099771 : Blo 1738570 14099771 := bstep (se 1 (by rfl) ⟨10574828, by rfl⟩ : syracuseStep 14099771 = 21149657) B21149657
theorem B9905561 : Blo 1738570 9905561 := bstep (se 2 (by rfl) ⟨3714585, by rfl⟩ : syracuseStep 9905561 = 7429171) B7429171
theorem B2475451 : Blo 1738570 2475451 := bstep (se 1 (by rfl) ⟨1856588, by rfl⟩ : syracuseStep 2475451 = 3713177) B3713177
theorem B8807939 : Blo 1738570 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B6604375 : Blo 1738570 6604375 := bstep (se 1 (by rfl) ⟨4953281, by rfl⟩ : syracuseStep 6604375 = 9906563) B9906563
theorem B3303031 : Blo 1738570 3303031 := bstep (se 1 (by rfl) ⟨2477273, by rfl⟩ : syracuseStep 3303031 = 4954547) B4954547
theorem B2934407 : Blo 1738570 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B1738631 : Blo 1738570 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B6604679 : Blo 1738570 6604679 := bstep (se 1 (by rfl) ⟨4953509, by rfl⟩ : syracuseStep 6604679 = 9907019) B9907019
theorem B1738639 : Blo 1738570 1738639 := bstep (se 1 (by rfl) ⟨1303979, by rfl⟩ : syracuseStep 1738639 = 2607959) B2607959
theorem B1738683 : Blo 1738570 1738683 := bstep (se 1 (by rfl) ⟨1304012, by rfl⟩ : syracuseStep 1738683 = 2608025) B2608025
theorem B7432145 : Blo 1738570 7432145 := bstep (se 2 (by rfl) ⟨2787054, by rfl⟩ : syracuseStep 7432145 = 5574109) B5574109
theorem B1738759 : Blo 1738570 1738759 := bstep (se 1 (by rfl) ⟨1304069, by rfl⟩ : syracuseStep 1738759 = 2608139) B2608139
theorem B1738767 : Blo 1738570 1738767 := bstep (se 1 (by rfl) ⟨1304075, by rfl⟩ : syracuseStep 1738767 = 2608151) B2608151
theorem B3524641 : Blo 1738570 3524641 := bstep (se 2 (by rfl) ⟨1321740, by rfl⟩ : syracuseStep 3524641 = 2643481) B2643481
theorem B33450029 : Blo 1738570 33450029 := bstep (se 3 (by rfl) ⟨6271880, by rfl⟩ : syracuseStep 33450029 = 12543761) B12543761
theorem B1738811 : Blo 1738570 1738811 := bstep (se 1 (by rfl) ⟨1304108, by rfl⟩ : syracuseStep 1738811 = 2608217) B2608217
theorem B6604861 : Blo 1738570 6604861 := bstep (se 3 (by rfl) ⟨1238411, by rfl⟩ : syracuseStep 6604861 = 2476823) B2476823
theorem B4401287 : Blo 1738570 4401287 := bstep (se 1 (by rfl) ⟨3300965, by rfl⟩ : syracuseStep 4401287 = 6601931) B6601931
theorem B1738887 : Blo 1738570 1738887 := bstep (se 1 (by rfl) ⟨1304165, by rfl⟩ : syracuseStep 1738887 = 2608331) B2608331
theorem B1738895 : Blo 1738570 1738895 := bstep (se 1 (by rfl) ⟨1304171, by rfl⟩ : syracuseStep 1738895 = 2608343) B2608343
theorem B4401337 : Blo 1738570 4401337 := bstep (se 2 (by rfl) ⟨1650501, by rfl⟩ : syracuseStep 4401337 = 3301003) B3301003
theorem B1738939 : Blo 1738570 1738939 := bstep (se 1 (by rfl) ⟨1304204, by rfl⟩ : syracuseStep 1738939 = 2608409) B2608409
theorem B2787529 : Blo 1738570 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B1739015 : Blo 1738570 1739015 := bstep (se 1 (by rfl) ⟨1304261, by rfl⟩ : syracuseStep 1739015 = 2608523) B2608523
theorem B1739023 : Blo 1738570 1739023 := bstep (se 1 (by rfl) ⟨1304267, by rfl⟩ : syracuseStep 1739023 = 2608535) B2608535
theorem B2935055 : Blo 1738570 2935055 := bstep (se 1 (by rfl) ⟨2201291, by rfl⟩ : syracuseStep 2935055 = 4402583) B4402583
theorem B2476345 : Blo 1738570 2476345 := bstep (se 2 (by rfl) ⟨928629, by rfl⟩ : syracuseStep 2476345 = 1857259) B1857259
theorem B3713339 : Blo 1738570 3713339 := bstep (se 1 (by rfl) ⟨2785004, by rfl⟩ : syracuseStep 3713339 = 5570009) B5570009
theorem B1739067 : Blo 1738570 1739067 := bstep (se 1 (by rfl) ⟨1304300, by rfl⟩ : syracuseStep 1739067 = 2608601) B2608601
theorem B1739143 : Blo 1738570 1739143 := bstep (se 1 (by rfl) ⟨1304357, by rfl⟩ : syracuseStep 1739143 = 2608715) B2608715
theorem B4704647 : Blo 1738570 4704647 := bstep (se 1 (by rfl) ⟨3528485, by rfl⟩ : syracuseStep 4704647 = 7056971) B7056971
theorem B1739151 : Blo 1738570 1739151 := bstep (se 1 (by rfl) ⟨1304363, by rfl⟩ : syracuseStep 1739151 = 2608727) B2608727
theorem B1739195 : Blo 1738570 1739195 := bstep (se 1 (by rfl) ⟨1304396, by rfl⟩ : syracuseStep 1739195 = 2608793) B2608793
theorem B2787785 : Blo 1738570 2787785 := bstep (se 2 (by rfl) ⟨1045419, by rfl⟩ : syracuseStep 2787785 = 2090839) B2090839
theorem B4704713 : Blo 1738570 4704713 := bstep (se 2 (by rfl) ⟨1764267, by rfl⟩ : syracuseStep 4704713 = 3528535) B3528535
theorem B14109137 : Blo 1738570 14109137 := bstep (se 2 (by rfl) ⟨5290926, by rfl⟩ : syracuseStep 14109137 = 10581853) B10581853
theorem B1739271 : Blo 1738570 1739271 := bstep (se 1 (by rfl) ⟨1304453, by rfl⟩ : syracuseStep 1739271 = 2608907) B2608907
theorem B1739279 : Blo 1738570 1739279 := bstep (se 1 (by rfl) ⟨1304459, by rfl⟩ : syracuseStep 1739279 = 2608919) B2608919
theorem B1739323 : Blo 1738570 1739323 := bstep (se 1 (by rfl) ⟨1304492, by rfl⟩ : syracuseStep 1739323 = 2608985) B2608985
theorem B1739399 : Blo 1738570 1739399 := bstep (se 1 (by rfl) ⟨1304549, by rfl⟩ : syracuseStep 1739399 = 2609099) B2609099
theorem B1739407 : Blo 1738570 1739407 := bstep (se 1 (by rfl) ⟨1304555, by rfl⟩ : syracuseStep 1739407 = 2609111) B2609111
theorem B1739451 : Blo 1738570 1739451 := bstep (se 1 (by rfl) ⟨1304588, by rfl⟩ : syracuseStep 1739451 = 2609177) B2609177
theorem B5868233 : Blo 1738570 5868233 := bstep (se 2 (by rfl) ⟨2200587, by rfl⟩ : syracuseStep 5868233 = 4401175) B4401175
theorem B9407177 : Blo 1738570 9407177 := bstep (se 2 (by rfl) ⟨3527691, by rfl⟩ : syracuseStep 9407177 = 7055383) B7055383
theorem B2607863 : Blo 1738570 2607863 := bstep (se 1 (by rfl) ⟨1955897, by rfl⟩ : syracuseStep 2607863 = 3911795) B3911795
theorem B1739527 : Blo 1738570 1739527 := bstep (se 1 (by rfl) ⟨1304645, by rfl⟩ : syracuseStep 1739527 = 2609291) B2609291
theorem B2607887 : Blo 1738570 2607887 := bstep (se 1 (by rfl) ⟨1955915, by rfl⟩ : syracuseStep 2607887 = 3911831) B3911831
theorem B4401935 : Blo 1738570 4401935 := bstep (se 1 (by rfl) ⟨3301451, by rfl⟩ : syracuseStep 4401935 = 6602903) B6602903
theorem B1739535 : Blo 1738570 1739535 := bstep (se 1 (by rfl) ⟨1304651, by rfl⟩ : syracuseStep 1739535 = 2609303) B2609303
theorem B2935595 : Blo 1738570 2935595 := bstep (se 1 (by rfl) ⟨2201696, by rfl⟩ : syracuseStep 2935595 = 4403393) B4403393
theorem B2607929 : Blo 1738570 2607929 := bstep (se 2 (by rfl) ⟨977973, by rfl⟩ : syracuseStep 2607929 = 1955947) B1955947
theorem B1739579 : Blo 1738570 1739579 := bstep (se 1 (by rfl) ⟨1304684, by rfl⟩ : syracuseStep 1739579 = 2609369) B2609369
theorem B2608007 : Blo 1738570 2608007 := bstep (se 1 (by rfl) ⟨1956005, by rfl⟩ : syracuseStep 2608007 = 3912011) B3912011
theorem B1739655 : Blo 1738570 1739655 := bstep (se 1 (by rfl) ⟨1304741, by rfl⟩ : syracuseStep 1739655 = 2609483) B2609483
theorem B1739663 : Blo 1738570 1739663 := bstep (se 1 (by rfl) ⟨1304747, by rfl⟩ : syracuseStep 1739663 = 2609495) B2609495
theorem B2608043 : Blo 1738570 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1739707 : Blo 1738570 1739707 := bstep (se 1 (by rfl) ⟨1304780, by rfl⟩ : syracuseStep 1739707 = 2609561) B2609561
theorem B2608073 : Blo 1738570 2608073 := bstep (se 2 (by rfl) ⟨978027, by rfl⟩ : syracuseStep 2608073 = 1956055) B1956055
theorem B1739783 : Blo 1738570 1739783 := bstep (se 1 (by rfl) ⟨1304837, by rfl⟩ : syracuseStep 1739783 = 2609675) B2609675
theorem B1739791 : Blo 1738570 1739791 := bstep (se 1 (by rfl) ⟨1304843, by rfl⟩ : syracuseStep 1739791 = 2609687) B2609687
theorem B2608187 : Blo 1738570 2608187 := bstep (se 1 (by rfl) ⟨1956140, by rfl⟩ : syracuseStep 2608187 = 3912281) B3912281
theorem B1739835 : Blo 1738570 1739835 := bstep (se 1 (by rfl) ⟨1304876, by rfl⟩ : syracuseStep 1739835 = 2609753) B2609753
theorem B8809559 : Blo 1738570 8809559 := bstep (se 1 (by rfl) ⟨6607169, by rfl⟩ : syracuseStep 8809559 = 13214339) B13214339
theorem B2608247 : Blo 1738570 2608247 := bstep (se 1 (by rfl) ⟨1956185, by rfl⟩ : syracuseStep 2608247 = 3912371) B3912371
theorem B12881029 : Blo 1738570 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B1739911 : Blo 1738570 1739911 := bstep (se 1 (by rfl) ⟨1304933, by rfl⟩ : syracuseStep 1739911 = 2609867) B2609867
theorem B2608271 : Blo 1738570 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B1739919 : Blo 1738570 1739919 := bstep (se 1 (by rfl) ⟨1304939, by rfl⟩ : syracuseStep 1739919 = 2609879) B2609879
theorem B2608313 : Blo 1738570 2608313 := bstep (se 2 (by rfl) ⟨978117, by rfl⟩ : syracuseStep 2608313 = 1956235) B1956235
theorem B2935993 : Blo 1738570 2935993 := bstep (se 2 (by rfl) ⟨1100997, by rfl⟩ : syracuseStep 2935993 = 2201995) B2201995
theorem B1739963 : Blo 1738570 1739963 := bstep (se 1 (by rfl) ⟨1304972, by rfl⟩ : syracuseStep 1739963 = 2609945) B2609945
theorem B4181177 : Blo 1738570 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B2608391 : Blo 1738570 2608391 := bstep (se 1 (by rfl) ⟨1956293, by rfl⟩ : syracuseStep 2608391 = 3912587) B3912587
theorem B1740039 : Blo 1738570 1740039 := bstep (se 1 (by rfl) ⟨1305029, by rfl⟩ : syracuseStep 1740039 = 2610059) B2610059
theorem B1740047 : Blo 1738570 1740047 := bstep (se 1 (by rfl) ⟨1305035, by rfl⟩ : syracuseStep 1740047 = 2610071) B2610071
theorem B2608427 : Blo 1738570 2608427 := bstep (se 1 (by rfl) ⟨1956320, by rfl⟩ : syracuseStep 2608427 = 3912641) B3912641
theorem B1740091 : Blo 1738570 1740091 := bstep (se 1 (by rfl) ⟨1305068, by rfl⟩ : syracuseStep 1740091 = 2610137) B2610137
theorem B2608457 : Blo 1738570 2608457 := bstep (se 2 (by rfl) ⟨978171, by rfl⟩ : syracuseStep 2608457 = 1956343) B1956343
theorem B5868935 : Blo 1738570 5868935 := bstep (se 1 (by rfl) ⟨4401701, by rfl⟩ : syracuseStep 5868935 = 8803403) B8803403
theorem B1740167 : Blo 1738570 1740167 := bstep (se 1 (by rfl) ⟨1305125, by rfl⟩ : syracuseStep 1740167 = 2610251) B2610251
theorem B1740175 : Blo 1738570 1740175 := bstep (se 1 (by rfl) ⟨1305131, by rfl⟩ : syracuseStep 1740175 = 2610263) B2610263
theorem B2608571 : Blo 1738570 2608571 := bstep (se 1 (by rfl) ⟨1956428, by rfl⟩ : syracuseStep 2608571 = 3912857) B3912857
theorem B1740219 : Blo 1738570 1740219 := bstep (se 1 (by rfl) ⟨1305164, by rfl⟩ : syracuseStep 1740219 = 2610329) B2610329
theorem B4402633 : Blo 1738570 4402633 := bstep (se 2 (by rfl) ⟨1650987, by rfl⟩ : syracuseStep 4402633 = 3301975) B3301975
theorem B57986513 : Blo 1738570 57986513 := bstep (se 2 (by rfl) ⟨21744942, by rfl⟩ : syracuseStep 57986513 = 43489885) B43489885
theorem B2608631 : Blo 1738570 2608631 := bstep (se 1 (by rfl) ⟨1956473, by rfl⟩ : syracuseStep 2608631 = 3912947) B3912947
theorem B2477575 : Blo 1738570 2477575 := bstep (se 1 (by rfl) ⟨1858181, by rfl⟩ : syracuseStep 2477575 = 3716363) B3716363
theorem B1740295 : Blo 1738570 1740295 := bstep (se 1 (by rfl) ⟨1305221, by rfl⟩ : syracuseStep 1740295 = 2610443) B2610443
theorem B2608655 : Blo 1738570 2608655 := bstep (se 1 (by rfl) ⟨1956491, by rfl⟩ : syracuseStep 2608655 = 3912983) B3912983
theorem B1740303 : Blo 1738570 1740303 := bstep (se 1 (by rfl) ⟨1305227, by rfl⟩ : syracuseStep 1740303 = 2610455) B2610455
theorem B2608697 : Blo 1738570 2608697 := bstep (se 2 (by rfl) ⟨978261, by rfl⟩ : syracuseStep 2608697 = 1956523) B1956523
theorem B1740347 : Blo 1738570 1740347 := bstep (se 1 (by rfl) ⟨1305260, by rfl⟩ : syracuseStep 1740347 = 2610521) B2610521
theorem B8810045 : Blo 1738570 8810045 := bstep (se 3 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 8810045 = 3303767) B3303767
theorem B4402775 : Blo 1738570 4402775 := bstep (se 1 (by rfl) ⟨3302081, by rfl⟩ : syracuseStep 4402775 = 6604163) B6604163
theorem B4951687 : Blo 1738570 4951687 := bstep (se 1 (by rfl) ⟨3713765, by rfl⟩ : syracuseStep 4951687 = 7427531) B7427531
theorem B2608775 : Blo 1738570 2608775 := bstep (se 1 (by rfl) ⟨1956581, by rfl⟩ : syracuseStep 2608775 = 3913163) B3913163
theorem B1740423 : Blo 1738570 1740423 := bstep (se 1 (by rfl) ⟨1305317, by rfl⟩ : syracuseStep 1740423 = 2610635) B2610635
theorem B1740431 : Blo 1738570 1740431 := bstep (se 1 (by rfl) ⟨1305323, by rfl⟩ : syracuseStep 1740431 = 2610647) B2610647
theorem B2608811 : Blo 1738570 2608811 := bstep (se 1 (by rfl) ⟨1956608, by rfl⟩ : syracuseStep 2608811 = 3913217) B3913217
theorem B1740475 : Blo 1738570 1740475 := bstep (se 1 (by rfl) ⟨1305356, by rfl⟩ : syracuseStep 1740475 = 2610713) B2610713
theorem B2608841 : Blo 1738570 2608841 := bstep (se 2 (by rfl) ⟨978315, by rfl⟩ : syracuseStep 2608841 = 1956631) B1956631
theorem B8359625 : Blo 1738570 8359625 := bstep (se 2 (by rfl) ⟨3134859, by rfl⟩ : syracuseStep 8359625 = 6269719) B6269719
theorem B5869313 : Blo 1738570 5869313 := bstep (se 2 (by rfl) ⟨2200992, by rfl⟩ : syracuseStep 5869313 = 4401985) B4401985
theorem B6606593 : Blo 1738570 6606593 := bstep (se 2 (by rfl) ⟨2477472, by rfl⟩ : syracuseStep 6606593 = 4954945) B4954945
theorem B1740551 : Blo 1738570 1740551 := bstep (se 1 (by rfl) ⟨1305413, by rfl⟩ : syracuseStep 1740551 = 2610827) B2610827
theorem B1740559 : Blo 1738570 1740559 := bstep (se 1 (by rfl) ⟨1305419, by rfl⟩ : syracuseStep 1740559 = 2610839) B2610839
theorem B3714859 : Blo 1738570 3714859 := bstep (se 1 (by rfl) ⟨2786144, by rfl⟩ : syracuseStep 3714859 = 5572289) B5572289
theorem B42307379 : Blo 1738570 42307379 := bstep (se 1 (by rfl) ⟨31730534, by rfl⟩ : syracuseStep 42307379 = 63461069) B63461069
theorem B8802107 : Blo 1738570 8802107 := bstep (se 1 (by rfl) ⟨6601580, by rfl⟩ : syracuseStep 8802107 = 13203161) B13203161
theorem B2608955 : Blo 1738570 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B2609015 : Blo 1738570 2609015 := bstep (se 1 (by rfl) ⟨1956761, by rfl⟩ : syracuseStep 2609015 = 3913523) B3913523
theorem B2936695 : Blo 1738570 2936695 := bstep (se 1 (by rfl) ⟨2202521, by rfl⟩ : syracuseStep 2936695 = 4405043) B4405043
theorem B2609039 : Blo 1738570 2609039 := bstep (se 1 (by rfl) ⟨1956779, by rfl⟩ : syracuseStep 2609039 = 3913559) B3913559
theorem B4951961 : Blo 1738570 4951961 := bstep (se 2 (by rfl) ⟨1856985, by rfl⟩ : syracuseStep 4951961 = 3713971) B3713971
theorem B2609081 : Blo 1738570 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B8802269 : Blo 1738570 8802269 := bstep (se 3 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 8802269 = 3300851) B3300851
theorem B2609159 : Blo 1738570 2609159 := bstep (se 1 (by rfl) ⟨1956869, by rfl⟩ : syracuseStep 2609159 = 3913739) B3913739
theorem B11300887 : Blo 1738570 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B2609195 : Blo 1738570 2609195 := bstep (se 1 (by rfl) ⟨1956896, by rfl⟩ : syracuseStep 2609195 = 3913793) B3913793
theorem B6271019 : Blo 1738570 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B2936891 : Blo 1738570 2936891 := bstep (se 1 (by rfl) ⟨2202668, by rfl⟩ : syracuseStep 2936891 = 4405337) B4405337
theorem B2609225 : Blo 1738570 2609225 := bstep (se 2 (by rfl) ⟨978459, by rfl⟩ : syracuseStep 2609225 = 1956919) B1956919
theorem B2609339 : Blo 1738570 2609339 := bstep (se 1 (by rfl) ⟨1957004, by rfl⟩ : syracuseStep 2609339 = 3914009) B3914009
theorem B6271177 : Blo 1738570 6271177 := bstep (se 2 (by rfl) ⟨2351691, by rfl⟩ : syracuseStep 6271177 = 4703383) B4703383
theorem B2609399 : Blo 1738570 2609399 := bstep (se 1 (by rfl) ⟨1957049, by rfl⟩ : syracuseStep 2609399 = 3914099) B3914099
theorem B2609423 : Blo 1738570 2609423 := bstep (se 1 (by rfl) ⟨1957067, by rfl⟩ : syracuseStep 2609423 = 3914135) B3914135
theorem B8802593 : Blo 1738570 8802593 := bstep (se 2 (by rfl) ⟨3300972, by rfl⟩ : syracuseStep 8802593 = 6601945) B6601945
theorem B2609465 : Blo 1738570 2609465 := bstep (se 2 (by rfl) ⟨978549, by rfl⟩ : syracuseStep 2609465 = 1957099) B1957099
theorem B6271291 : Blo 1738570 6271291 := bstep (se 1 (by rfl) ⟨4703468, by rfl⟩ : syracuseStep 6271291 = 9406937) B9406937
theorem B2609543 : Blo 1738570 2609543 := bstep (se 1 (by rfl) ⟨1957157, by rfl⟩ : syracuseStep 2609543 = 3914315) B3914315
theorem B10039697 : Blo 1738570 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B3912083 : Blo 1738570 3912083 := bstep (se 1 (by rfl) ⟨2934062, by rfl⟩ : syracuseStep 3912083 = 5868125) B5868125
theorem B2609579 : Blo 1738570 2609579 := bstep (se 1 (by rfl) ⟨1957184, by rfl⟩ : syracuseStep 2609579 = 3914369) B3914369
theorem B3912137 : Blo 1738570 3912137 := bstep (se 2 (by rfl) ⟨1467051, by rfl⟩ : syracuseStep 3912137 = 2934103) B2934103
theorem B2609609 : Blo 1738570 2609609 := bstep (se 2 (by rfl) ⟨978603, by rfl⟩ : syracuseStep 2609609 = 1957207) B1957207
theorem B5870123 : Blo 1738570 5870123 := bstep (se 1 (by rfl) ⟨4402592, by rfl⟩ : syracuseStep 5870123 = 8805185) B8805185
theorem B8360491 : Blo 1738570 8360491 := bstep (se 1 (by rfl) ⟨6270368, by rfl⟩ : syracuseStep 8360491 = 12540737) B12540737
theorem B2609723 : Blo 1738570 2609723 := bstep (se 1 (by rfl) ⟨1957292, by rfl⟩ : syracuseStep 2609723 = 3914585) B3914585
theorem B8360509 : Blo 1738570 8360509 := bstep (se 3 (by rfl) ⟨1567595, by rfl⟩ : syracuseStep 8360509 = 3135191) B3135191
theorem B8925815 : Blo 1738570 8925815 := bstep (se 1 (by rfl) ⟨6694361, by rfl⟩ : syracuseStep 8925815 = 13388723) B13388723
theorem B2609783 : Blo 1738570 2609783 := bstep (se 1 (by rfl) ⟨1957337, by rfl⟩ : syracuseStep 2609783 = 3914675) B3914675
theorem B2609807 : Blo 1738570 2609807 := bstep (se 1 (by rfl) ⟨1957355, by rfl⟩ : syracuseStep 2609807 = 3914711) B3914711
theorem B2609849 : Blo 1738570 2609849 := bstep (se 2 (by rfl) ⟨978693, by rfl⟩ : syracuseStep 2609849 = 1957387) B1957387
theorem B2609927 : Blo 1738570 2609927 := bstep (se 1 (by rfl) ⟨1957445, by rfl⟩ : syracuseStep 2609927 = 3914891) B3914891
theorem B2609963 : Blo 1738570 2609963 := bstep (se 1 (by rfl) ⟨1957472, by rfl⟩ : syracuseStep 2609963 = 3914945) B3914945
theorem B2609993 : Blo 1738570 2609993 := bstep (se 2 (by rfl) ⟨978747, by rfl⟩ : syracuseStep 2609993 = 1957495) B1957495
theorem B15070067 : Blo 1738570 15070067 := bstep (se 1 (by rfl) ⟨11302550, by rfl⟩ : syracuseStep 15070067 = 22605101) B22605101
theorem B6607763 : Blo 1738570 6607763 := bstep (se 1 (by rfl) ⟨4955822, by rfl⟩ : syracuseStep 6607763 = 9911645) B9911645
theorem B14300057 : Blo 1738570 14300057 := bstep (se 2 (by rfl) ⟨5362521, by rfl⟩ : syracuseStep 14300057 = 10725043) B10725043
theorem B2610107 : Blo 1738570 2610107 := bstep (se 1 (by rfl) ⟨1957580, by rfl⟩ : syracuseStep 2610107 = 3915161) B3915161
theorem B2610167 : Blo 1738570 2610167 := bstep (se 1 (by rfl) ⟨1957625, by rfl⟩ : syracuseStep 2610167 = 3915251) B3915251
theorem B4953089 : Blo 1738570 4953089 := bstep (se 2 (by rfl) ⟨1857408, by rfl⟩ : syracuseStep 4953089 = 3714817) B3714817
theorem B12538891 : Blo 1738570 12538891 := bstep (se 1 (by rfl) ⟨9404168, by rfl⟩ : syracuseStep 12538891 = 18808337) B18808337
theorem B2610191 : Blo 1738570 2610191 := bstep (se 1 (by rfl) ⟨1957643, by rfl⟩ : syracuseStep 2610191 = 3915287) B3915287
theorem B2610233 : Blo 1738570 2610233 := bstep (se 2 (by rfl) ⟨978837, by rfl⟩ : syracuseStep 2610233 = 1957675) B1957675
theorem B3912839 : Blo 1738570 3912839 := bstep (se 1 (by rfl) ⟨2934629, by rfl⟩ : syracuseStep 3912839 = 5869259) B5869259
theorem B2610311 : Blo 1738570 2610311 := bstep (se 1 (by rfl) ⟨1957733, by rfl⟩ : syracuseStep 2610311 = 3915467) B3915467
theorem B2610347 : Blo 1738570 2610347 := bstep (se 1 (by rfl) ⟨1957760, by rfl⟩ : syracuseStep 2610347 = 3915521) B3915521
theorem B2610377 : Blo 1738570 2610377 := bstep (se 2 (by rfl) ⟨978891, by rfl⟩ : syracuseStep 2610377 = 1957783) B1957783
theorem B8803565 : Blo 1738570 8803565 := bstep (se 3 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 8803565 = 3301337) B3301337
theorem B7533857 : Blo 1738570 7533857 := bstep (se 2 (by rfl) ⟨2825196, by rfl⟩ : syracuseStep 7533857 = 5650393) B5650393
theorem B3913019 : Blo 1738570 3913019 := bstep (se 1 (by rfl) ⟨2934764, by rfl⟩ : syracuseStep 3913019 = 5869529) B5869529
theorem B2610491 : Blo 1738570 2610491 := bstep (se 1 (by rfl) ⟨1957868, by rfl⟩ : syracuseStep 2610491 = 3915737) B3915737
theorem B2610551 : Blo 1738570 2610551 := bstep (se 1 (by rfl) ⟨1957913, by rfl⟩ : syracuseStep 2610551 = 3915827) B3915827
theorem B6608263 : Blo 1738570 6608263 := bstep (se 1 (by rfl) ⟨4956197, by rfl⟩ : syracuseStep 6608263 = 9912395) B9912395
theorem B2610575 : Blo 1738570 2610575 := bstep (se 1 (by rfl) ⟨1957931, by rfl⟩ : syracuseStep 2610575 = 3915863) B3915863
theorem B3913145 : Blo 1738570 3913145 := bstep (se 2 (by rfl) ⟨1467429, by rfl⟩ : syracuseStep 3913145 = 2934859) B2934859
theorem B2610617 : Blo 1738570 2610617 := bstep (se 2 (by rfl) ⟨978981, by rfl⟩ : syracuseStep 2610617 = 1957963) B1957963
theorem B4953545 : Blo 1738570 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B2610695 : Blo 1738570 2610695 := bstep (se 1 (by rfl) ⟨1958021, by rfl⟩ : syracuseStep 2610695 = 3916043) B3916043
theorem B2610731 : Blo 1738570 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B2610761 : Blo 1738570 2610761 := bstep (se 2 (by rfl) ⟨979035, by rfl⟩ : syracuseStep 2610761 = 1958071) B1958071
theorem B4404851 : Blo 1738570 4404851 := bstep (se 1 (by rfl) ⟨3303638, by rfl⟩ : syracuseStep 4404851 = 6607277) B6607277
theorem B7050871 : Blo 1738570 7050871 := bstep (se 1 (by rfl) ⟨5288153, by rfl⟩ : syracuseStep 7050871 = 10576307) B10576307
theorem B33453719 : Blo 1738570 33453719 := bstep (se 1 (by rfl) ⟨25090289, by rfl⟩ : syracuseStep 33453719 = 50180579) B50180579
theorem B18814693 : Blo 1738570 18814693 := bstep (se 4 (by rfl) ⟨1763877, by rfl⟩ : syracuseStep 18814693 = 3527755) B3527755
theorem B3913487 : Blo 1738570 3913487 := bstep (se 1 (by rfl) ⟨2935115, by rfl⟩ : syracuseStep 3913487 = 5870231) B5870231
theorem B3913505 : Blo 1738570 3913505 := bstep (se 2 (by rfl) ⟨1467564, by rfl⟩ : syracuseStep 3913505 = 2935129) B2935129
theorem B5871419 : Blo 1738570 5871419 := bstep (se 1 (by rfl) ⟨4403564, by rfl⟩ : syracuseStep 5871419 = 8807129) B8807129
theorem B19814219 : Blo 1738570 19814219 := bstep (se 1 (by rfl) ⟨14860664, by rfl⟩ : syracuseStep 19814219 = 29721329) B29721329
theorem B35698583 : Blo 1738570 35698583 := bstep (se 1 (by rfl) ⟨26773937, by rfl⟩ : syracuseStep 35698583 = 53547875) B53547875
theorem B6272977 : Blo 1738570 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B8804375 : Blo 1738570 8804375 := bstep (se 1 (by rfl) ⟨6603281, by rfl⟩ : syracuseStep 8804375 = 13206563) B13206563
theorem B21452845 : Blo 1738570 21452845 := bstep (se 3 (by rfl) ⟨4022408, by rfl⟩ : syracuseStep 21452845 = 8044817) B8044817
theorem B10729559 : Blo 1738570 10729559 := bstep (se 1 (by rfl) ⟨8047169, by rfl⟩ : syracuseStep 10729559 = 16094339) B16094339
theorem B3913847 : Blo 1738570 3913847 := bstep (se 1 (by rfl) ⟨2935385, by rfl⟩ : syracuseStep 3913847 = 5870771) B5870771
theorem B5290103 : Blo 1738570 5290103 := bstep (se 1 (by rfl) ⟨3967577, by rfl⟩ : syracuseStep 5290103 = 7935155) B7935155
theorem B4405367 : Blo 1738570 4405367 := bstep (se 1 (by rfl) ⟨3304025, by rfl⟩ : syracuseStep 4405367 = 6608051) B6608051
theorem B1955983 : Blo 1738570 1955983 := bstep (se 1 (by rfl) ⟨1466987, by rfl⟩ : syracuseStep 1955983 = 2933975) B2933975
theorem B5871905 : Blo 1738570 5871905 := bstep (se 2 (by rfl) ⟨2201964, by rfl⟩ : syracuseStep 5871905 = 4403929) B4403929
theorem B3914027 : Blo 1738570 3914027 := bstep (se 1 (by rfl) ⟨2935520, by rfl⟩ : syracuseStep 3914027 = 5871041) B5871041
theorem B2201899 : Blo 1738570 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B20076893 : Blo 1738570 20076893 := bstep (se 3 (by rfl) ⟨3764417, by rfl⟩ : syracuseStep 20076893 = 7528835) B7528835
theorem B12540419 : Blo 1738570 12540419 := bstep (se 1 (by rfl) ⟨9405314, by rfl⟩ : syracuseStep 12540419 = 18810629) B18810629
theorem B6601277 : Blo 1738570 6601277 := bstep (se 3 (by rfl) ⟨1237739, by rfl⟩ : syracuseStep 6601277 = 2475479) B2475479
theorem B1956487 : Blo 1738570 1956487 := bstep (se 1 (by rfl) ⟨1467365, by rfl⟩ : syracuseStep 1956487 = 2934731) B2934731
theorem B3914387 : Blo 1738570 3914387 := bstep (se 1 (by rfl) ⟨2935790, by rfl⟩ : syracuseStep 3914387 = 5871581) B5871581
theorem B3914441 : Blo 1738570 3914441 := bstep (se 2 (by rfl) ⟨1467915, by rfl⟩ : syracuseStep 3914441 = 2935831) B2935831
theorem B1956667 : Blo 1738570 1956667 := bstep (se 1 (by rfl) ⟨1467500, by rfl⟩ : syracuseStep 1956667 = 2935001) B2935001
theorem B5872499 : Blo 1738570 5872499 := bstep (se 1 (by rfl) ⟨4404374, by rfl⟩ : syracuseStep 5872499 = 8808749) B8808749
theorem B8354819 : Blo 1738570 8354819 := bstep (se 1 (by rfl) ⟨6266114, by rfl⟩ : syracuseStep 8354819 = 12532229) B12532229
theorem B2350139 : Blo 1738570 2350139 := bstep (se 1 (by rfl) ⟨1762604, by rfl⟩ : syracuseStep 2350139 = 3525209) B3525209
theorem B4955195 : Blo 1738570 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B8928317 : Blo 1738570 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B2202871 : Blo 1738570 2202871 := bstep (se 1 (by rfl) ⟨1652153, by rfl⟩ : syracuseStep 2202871 = 3304307) B3304307
theorem B1957135 : Blo 1738570 1957135 := bstep (se 1 (by rfl) ⟨1467851, by rfl⟩ : syracuseStep 1957135 = 2935703) B2935703
theorem B9534779 : Blo 1738570 9534779 := bstep (se 1 (by rfl) ⟨7151084, by rfl⟩ : syracuseStep 9534779 = 14302169) B14302169
theorem B3915143 : Blo 1738570 3915143 := bstep (se 1 (by rfl) ⟨2936357, by rfl⟩ : syracuseStep 3915143 = 5872715) B5872715
theorem B7052753 : Blo 1738570 7052753 := bstep (se 2 (by rfl) ⟨2644782, by rfl⟩ : syracuseStep 7052753 = 5289565) B5289565
theorem B4701739 : Blo 1738570 4701739 := bstep (se 1 (by rfl) ⟨3526304, by rfl⟩ : syracuseStep 4701739 = 7052609) B7052609
theorem B3915323 : Blo 1738570 3915323 := bstep (se 1 (by rfl) ⟨2936492, by rfl⟩ : syracuseStep 3915323 = 5872985) B5872985
theorem B114392675 : Blo 1738570 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B16719479 : Blo 1738570 16719479 := bstep (se 1 (by rfl) ⟨12539609, by rfl⟩ : syracuseStep 16719479 = 25079219) B25079219
theorem B3301049 : Blo 1738570 3301049 := bstep (se 2 (by rfl) ⟨1237893, by rfl⟩ : syracuseStep 3301049 = 2475787) B2475787
theorem B3915449 : Blo 1738570 3915449 := bstep (se 2 (by rfl) ⟨1468293, by rfl⟩ : syracuseStep 3915449 = 2936587) B2936587
theorem B4955833 : Blo 1738570 4955833 := bstep (se 2 (by rfl) ⟨1858437, by rfl⟩ : syracuseStep 4955833 = 3716875) B3716875
theorem B1957639 : Blo 1738570 1957639 := bstep (se 1 (by rfl) ⟨1468229, by rfl⟩ : syracuseStep 1957639 = 2936459) B2936459
theorem B18816857 : Blo 1738570 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B21151639 : Blo 1738570 21151639 := bstep (se 1 (by rfl) ⟨15863729, by rfl⟩ : syracuseStep 21151639 = 31727459) B31727459
theorem B1957819 : Blo 1738570 1957819 := bstep (se 1 (by rfl) ⟨1468364, by rfl⟩ : syracuseStep 1957819 = 2936729) B2936729
theorem B9404363 : Blo 1738570 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B6602705 : Blo 1738570 6602705 := bstep (se 2 (by rfl) ⟨2476014, by rfl⟩ : syracuseStep 6602705 = 4952029) B4952029
theorem B1957927 : Blo 1738570 1957927 := bstep (se 1 (by rfl) ⟨1468445, by rfl⟩ : syracuseStep 1957927 = 2936891) B2936891
theorem B16711757 : Blo 1738570 16711757 := bstep (se 3 (by rfl) ⟨3133454, by rfl⟩ : syracuseStep 16711757 = 6266909) B6266909
theorem B8806481 : Blo 1738570 8806481 := bstep (se 2 (by rfl) ⟨3302430, by rfl⟩ : syracuseStep 8806481 = 6604861) B6604861
theorem B6267037 : Blo 1738570 6267037 := bstep (se 3 (by rfl) ⟨1175069, by rfl⟩ : syracuseStep 6267037 = 2350139) B2350139
theorem B13213853 : Blo 1738570 13213853 := bstep (se 3 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 13213853 = 4955195) B4955195
theorem B6693131 : Blo 1738570 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B3301793 : Blo 1738570 3301793 := bstep (se 2 (by rfl) ⟨1238172, by rfl⟩ : syracuseStep 3301793 = 2476345) B2476345
theorem B11149805 : Blo 1738570 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B11141657 : Blo 1738570 11141657 := bstep (se 2 (by rfl) ⟨4178121, by rfl⟩ : syracuseStep 11141657 = 8356243) B8356243
theorem B6603403 : Blo 1738570 6603403 := bstep (se 1 (by rfl) ⟨4952552, by rfl⟩ : syracuseStep 6603403 = 9905105) B9905105
theorem B3302059 : Blo 1738570 3302059 := bstep (se 1 (by rfl) ⟨2476544, by rfl⟩ : syracuseStep 3302059 = 4953089) B4953089
theorem B5022571 : Blo 1738570 5022571 := bstep (se 1 (by rfl) ⟨3766928, by rfl⟩ : syracuseStep 5022571 = 7533857) B7533857
theorem B6603707 : Blo 1738570 6603707 := bstep (se 1 (by rfl) ⟨4952780, by rfl⟩ : syracuseStep 6603707 = 9905561) B9905561
theorem B3302363 : Blo 1738570 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B23799055 : Blo 1738570 23799055 := bstep (se 1 (by rfl) ⟨17849291, by rfl⟩ : syracuseStep 23799055 = 35698583) B35698583
theorem B22300019 : Blo 1738570 22300019 := bstep (se 1 (by rfl) ⟨16725014, by rfl⟩ : syracuseStep 22300019 = 33450029) B33450029
theorem B7153039 : Blo 1738570 7153039 := bstep (se 1 (by rfl) ⟨5364779, by rfl⟩ : syracuseStep 7153039 = 10729559) B10729559
theorem B2934191 : Blo 1738570 2934191 := bstep (se 1 (by rfl) ⟨2200643, by rfl⟩ : syracuseStep 2934191 = 4401287) B4401287
theorem B2475559 : Blo 1738570 2475559 := bstep (se 1 (by rfl) ⟨1856669, by rfl⟩ : syracuseStep 2475559 = 3713339) B3713339
theorem B9406091 : Blo 1738570 9406091 := bstep (se 1 (by rfl) ⟨7054568, by rfl⟩ : syracuseStep 9406091 = 14109137) B14109137
theorem B10585745 : Blo 1738570 10585745 := bstep (se 2 (by rfl) ⟨3969654, by rfl⟩ : syracuseStep 10585745 = 7939309) B7939309
theorem B4400851 : Blo 1738570 4400851 := bstep (se 1 (by rfl) ⟨3300638, by rfl⟩ : syracuseStep 4400851 = 6601277) B6601277
theorem B1738575 : Blo 1738570 1738575 := bstep (se 1 (by rfl) ⟨1303931, by rfl⟩ : syracuseStep 1738575 = 2607863) B2607863
theorem B1738591 : Blo 1738570 1738591 := bstep (se 1 (by rfl) ⟨1303943, by rfl⟩ : syracuseStep 1738591 = 2607887) B2607887
theorem B2934623 : Blo 1738570 2934623 := bstep (se 1 (by rfl) ⟨2200967, by rfl⟩ : syracuseStep 2934623 = 4401935) B4401935
theorem B22292333 : Blo 1738570 22292333 := bstep (se 3 (by rfl) ⟨4179812, by rfl⟩ : syracuseStep 22292333 = 8359625) B8359625
theorem B1738619 : Blo 1738570 1738619 := bstep (se 1 (by rfl) ⟨1303964, by rfl⟩ : syracuseStep 1738619 = 2607929) B2607929
theorem B1738671 : Blo 1738570 1738671 := bstep (se 1 (by rfl) ⟨1304003, by rfl⟩ : syracuseStep 1738671 = 2608007) B2608007
theorem B1738695 : Blo 1738570 1738695 := bstep (se 1 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 1738695 = 2608043) B2608043
theorem B1738715 : Blo 1738570 1738715 := bstep (se 1 (by rfl) ⟨1304036, by rfl⟩ : syracuseStep 1738715 = 2608073) B2608073
theorem B3303433 : Blo 1738570 3303433 := bstep (se 2 (by rfl) ⟨1238787, by rfl⟩ : syracuseStep 3303433 = 2477575) B2477575
theorem B1738791 : Blo 1738570 1738791 := bstep (se 1 (by rfl) ⟨1304093, by rfl⟩ : syracuseStep 1738791 = 2608187) B2608187
theorem B6268985 : Blo 1738570 6268985 := bstep (se 2 (by rfl) ⟨2350869, by rfl⟩ : syracuseStep 6268985 = 4701739) B4701739
theorem B1738831 : Blo 1738570 1738831 := bstep (se 1 (by rfl) ⟨1304123, by rfl⟩ : syracuseStep 1738831 = 2608247) B2608247
theorem B1738847 : Blo 1738570 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B1738875 : Blo 1738570 1738875 := bstep (se 1 (by rfl) ⟨1304156, by rfl⟩ : syracuseStep 1738875 = 2608313) B2608313
theorem B1738927 : Blo 1738570 1738927 := bstep (se 1 (by rfl) ⟨1304195, by rfl⟩ : syracuseStep 1738927 = 2608391) B2608391
theorem B1738951 : Blo 1738570 1738951 := bstep (se 1 (by rfl) ⟨1304213, by rfl⟩ : syracuseStep 1738951 = 2608427) B2608427
theorem B1738971 : Blo 1738570 1738971 := bstep (se 1 (by rfl) ⟨1304228, by rfl⟩ : syracuseStep 1738971 = 2608457) B2608457
theorem B1739047 : Blo 1738570 1739047 := bstep (se 1 (by rfl) ⟨1304285, by rfl⟩ : syracuseStep 1739047 = 2608571) B2608571
theorem B25086257 : Blo 1738570 25086257 := bstep (se 2 (by rfl) ⟨9407346, by rfl⟩ : syracuseStep 25086257 = 18814693) B18814693
theorem B1739087 : Blo 1738570 1739087 := bstep (se 1 (by rfl) ⟨1304315, by rfl⟩ : syracuseStep 1739087 = 2608631) B2608631
theorem B1739103 : Blo 1738570 1739103 := bstep (se 1 (by rfl) ⟨1304327, by rfl⟩ : syracuseStep 1739103 = 2608655) B2608655
theorem B1739131 : Blo 1738570 1739131 := bstep (se 1 (by rfl) ⟨1304348, by rfl⟩ : syracuseStep 1739131 = 2608697) B2608697
theorem B2935183 : Blo 1738570 2935183 := bstep (se 1 (by rfl) ⟨2201387, by rfl⟩ : syracuseStep 2935183 = 4402775) B4402775
theorem B76261783 : Blo 1738570 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B1739183 : Blo 1738570 1739183 := bstep (se 1 (by rfl) ⟨1304387, by rfl⟩ : syracuseStep 1739183 = 2608775) B2608775
theorem B1739207 : Blo 1738570 1739207 := bstep (se 1 (by rfl) ⟨1304405, by rfl⟩ : syracuseStep 1739207 = 2608811) B2608811
theorem B1739227 : Blo 1738570 1739227 := bstep (se 1 (by rfl) ⟨1304420, by rfl⟩ : syracuseStep 1739227 = 2608841) B2608841
theorem B5868071 : Blo 1738570 5868071 := bstep (se 1 (by rfl) ⟨4401053, by rfl⟩ : syracuseStep 5868071 = 8802107) B8802107
theorem B1739303 : Blo 1738570 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B12544571 : Blo 1738570 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B1739343 : Blo 1738570 1739343 := bstep (se 1 (by rfl) ⟨1304507, by rfl⟩ : syracuseStep 1739343 = 2609015) B2609015
theorem B1739359 : Blo 1738570 1739359 := bstep (se 1 (by rfl) ⟨1304519, by rfl⟩ : syracuseStep 1739359 = 2609039) B2609039
theorem B1739387 : Blo 1738570 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B6269575 : Blo 1738570 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B4401803 : Blo 1738570 4401803 := bstep (se 1 (by rfl) ⟨3301352, by rfl⟩ : syracuseStep 4401803 = 6602705) B6602705
theorem B5868179 : Blo 1738570 5868179 := bstep (se 1 (by rfl) ⟨4401134, by rfl⟩ : syracuseStep 5868179 = 8802269) B8802269
theorem B1739439 : Blo 1738570 1739439 := bstep (se 1 (by rfl) ⟨1304579, by rfl⟩ : syracuseStep 1739439 = 2609159) B2609159
theorem B1739463 : Blo 1738570 1739463 := bstep (se 1 (by rfl) ⟨1304597, by rfl⟩ : syracuseStep 1739463 = 2609195) B2609195
theorem B4180679 : Blo 1738570 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B44575433 : Blo 1738570 44575433 := bstep (se 2 (by rfl) ⟨16715787, by rfl⟩ : syracuseStep 44575433 = 33431575) B33431575
theorem B3304147 : Blo 1738570 3304147 := bstep (se 1 (by rfl) ⟨2478110, by rfl⟩ : syracuseStep 3304147 = 4956221) B4956221
theorem B1739483 : Blo 1738570 1739483 := bstep (se 1 (by rfl) ⟨1304612, by rfl⟩ : syracuseStep 1739483 = 2609225) B2609225
theorem B60271397 : Blo 1738570 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B1739559 : Blo 1738570 1739559 := bstep (se 1 (by rfl) ⟨1304669, by rfl⟩ : syracuseStep 1739559 = 2609339) B2609339
theorem B1739599 : Blo 1738570 1739599 := bstep (se 1 (by rfl) ⟨1304699, by rfl⟩ : syracuseStep 1739599 = 2609399) B2609399
theorem B1739615 : Blo 1738570 1739615 := bstep (se 1 (by rfl) ⟨1304711, by rfl⟩ : syracuseStep 1739615 = 2609423) B2609423
theorem B2607977 : Blo 1738570 2607977 := bstep (se 2 (by rfl) ⟨977991, by rfl⟩ : syracuseStep 2607977 = 1955983) B1955983
theorem B5868395 : Blo 1738570 5868395 := bstep (se 1 (by rfl) ⟨4401296, by rfl⟩ : syracuseStep 5868395 = 8802593) B8802593
theorem B1739643 : Blo 1738570 1739643 := bstep (se 1 (by rfl) ⟨1304732, by rfl⟩ : syracuseStep 1739643 = 2609465) B2609465
theorem B5868449 : Blo 1738570 5868449 := bstep (se 2 (by rfl) ⟨2200668, by rfl⟩ : syracuseStep 5868449 = 4401337) B4401337
theorem B1739695 : Blo 1738570 1739695 := bstep (se 1 (by rfl) ⟨1304771, by rfl⟩ : syracuseStep 1739695 = 2609543) B2609543
theorem B2608055 : Blo 1738570 2608055 := bstep (se 1 (by rfl) ⟨1956041, by rfl⟩ : syracuseStep 2608055 = 3912083) B3912083
theorem B1739719 : Blo 1738570 1739719 := bstep (se 1 (by rfl) ⟨1304789, by rfl⟩ : syracuseStep 1739719 = 2609579) B2609579
theorem B2608091 : Blo 1738570 2608091 := bstep (se 1 (by rfl) ⟨1956068, by rfl⟩ : syracuseStep 2608091 = 3912137) B3912137
theorem B1739739 : Blo 1738570 1739739 := bstep (se 1 (by rfl) ⟨1304804, by rfl⟩ : syracuseStep 1739739 = 2609609) B2609609
theorem B13216769 : Blo 1738570 13216769 := bstep (se 2 (by rfl) ⟨4956288, by rfl⟩ : syracuseStep 13216769 = 9912577) B9912577
theorem B4074515 : Blo 1738570 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B1739815 : Blo 1738570 1739815 := bstep (se 1 (by rfl) ⟨1304861, by rfl⟩ : syracuseStep 1739815 = 2609723) B2609723
theorem B9399347 : Blo 1738570 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B2935865 : Blo 1738570 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B5950543 : Blo 1738570 5950543 := bstep (se 1 (by rfl) ⟨4462907, by rfl⟩ : syracuseStep 5950543 = 8925815) B8925815
theorem B1739855 : Blo 1738570 1739855 := bstep (se 1 (by rfl) ⟨1304891, by rfl⟩ : syracuseStep 1739855 = 2609783) B2609783
theorem B1739871 : Blo 1738570 1739871 := bstep (se 1 (by rfl) ⟨1304903, by rfl⟩ : syracuseStep 1739871 = 2609807) B2609807
theorem B1739899 : Blo 1738570 1739899 := bstep (se 1 (by rfl) ⟨1304924, by rfl⟩ : syracuseStep 1739899 = 2609849) B2609849
theorem B1739951 : Blo 1738570 1739951 := bstep (se 1 (by rfl) ⟨1304963, by rfl⟩ : syracuseStep 1739951 = 2609927) B2609927
theorem B1739975 : Blo 1738570 1739975 := bstep (se 1 (by rfl) ⟨1304981, by rfl⟩ : syracuseStep 1739975 = 2609963) B2609963
theorem B1739995 : Blo 1738570 1739995 := bstep (se 1 (by rfl) ⟨1304996, by rfl⟩ : syracuseStep 1739995 = 2609993) B2609993
theorem B10046711 : Blo 1738570 10046711 := bstep (se 1 (by rfl) ⟨7535033, by rfl⟩ : syracuseStep 10046711 = 15070067) B15070067
theorem B37604645 : Blo 1738570 37604645 := bstep (se 4 (by rfl) ⟨3525435, by rfl⟩ : syracuseStep 37604645 = 7050871) B7050871
theorem B1740071 : Blo 1738570 1740071 := bstep (se 1 (by rfl) ⟨1305053, by rfl⟩ : syracuseStep 1740071 = 2610107) B2610107
theorem B1740111 : Blo 1738570 1740111 := bstep (se 1 (by rfl) ⟨1305083, by rfl⟩ : syracuseStep 1740111 = 2610167) B2610167
theorem B1740127 : Blo 1738570 1740127 := bstep (se 1 (by rfl) ⟨1305095, by rfl⟩ : syracuseStep 1740127 = 2610191) B2610191
theorem B1740155 : Blo 1738570 1740155 := bstep (se 1 (by rfl) ⟨1305116, by rfl⟩ : syracuseStep 1740155 = 2610233) B2610233
theorem B5647745 : Blo 1738570 5647745 := bstep (se 2 (by rfl) ⟨2117904, by rfl⟩ : syracuseStep 5647745 = 4235809) B4235809
theorem B2608559 : Blo 1738570 2608559 := bstep (se 1 (by rfl) ⟨1956419, by rfl⟩ : syracuseStep 2608559 = 3912839) B3912839
theorem B1740207 : Blo 1738570 1740207 := bstep (se 1 (by rfl) ⟨1305155, by rfl⟩ : syracuseStep 1740207 = 2610311) B2610311
theorem B1740231 : Blo 1738570 1740231 := bstep (se 1 (by rfl) ⟨1305173, by rfl⟩ : syracuseStep 1740231 = 2610347) B2610347
theorem B1740251 : Blo 1738570 1740251 := bstep (se 1 (by rfl) ⟨1305188, by rfl⟩ : syracuseStep 1740251 = 2610377) B2610377
theorem B5869043 : Blo 1738570 5869043 := bstep (se 1 (by rfl) ⟨4401782, by rfl⟩ : syracuseStep 5869043 = 8803565) B8803565
theorem B2608649 : Blo 1738570 2608649 := bstep (se 2 (by rfl) ⟨978243, by rfl⟩ : syracuseStep 2608649 = 1956487) B1956487
theorem B3714569 : Blo 1738570 3714569 := bstep (se 2 (by rfl) ⟨1392963, by rfl⟩ : syracuseStep 3714569 = 2785927) B2785927
theorem B9399847 : Blo 1738570 9399847 := bstep (se 1 (by rfl) ⟨7049885, by rfl⟩ : syracuseStep 9399847 = 14099771) B14099771
theorem B2608679 : Blo 1738570 2608679 := bstep (se 1 (by rfl) ⟨1956509, by rfl⟩ : syracuseStep 2608679 = 3913019) B3913019
theorem B1740327 : Blo 1738570 1740327 := bstep (se 1 (by rfl) ⟨1305245, by rfl⟩ : syracuseStep 1740327 = 2610491) B2610491
theorem B1740367 : Blo 1738570 1740367 := bstep (se 1 (by rfl) ⟨1305275, by rfl⟩ : syracuseStep 1740367 = 2610551) B2610551
theorem B1740383 : Blo 1738570 1740383 := bstep (se 1 (by rfl) ⟨1305287, by rfl⟩ : syracuseStep 1740383 = 2610575) B2610575
theorem B2608763 : Blo 1738570 2608763 := bstep (se 1 (by rfl) ⟨1956572, by rfl⟩ : syracuseStep 2608763 = 3913145) B3913145
theorem B1740411 : Blo 1738570 1740411 := bstep (se 1 (by rfl) ⟨1305308, by rfl⟩ : syracuseStep 1740411 = 2610617) B2610617
theorem B1740463 : Blo 1738570 1740463 := bstep (se 1 (by rfl) ⟨1305347, by rfl⟩ : syracuseStep 1740463 = 2610695) B2610695
theorem B12545725 : Blo 1738570 12545725 := bstep (se 3 (by rfl) ⟨2352323, by rfl⟩ : syracuseStep 12545725 = 4704647) B4704647
theorem B1740487 : Blo 1738570 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B1740507 : Blo 1738570 1740507 := bstep (se 1 (by rfl) ⟨1305380, by rfl⟩ : syracuseStep 1740507 = 2610761) B2610761
theorem B2936567 : Blo 1738570 2936567 := bstep (se 1 (by rfl) ⟨2202425, by rfl⟩ : syracuseStep 2936567 = 4404851) B4404851
theorem B2608889 : Blo 1738570 2608889 := bstep (se 2 (by rfl) ⟨978333, by rfl⟩ : syracuseStep 2608889 = 1956667) B1956667
theorem B4402937 : Blo 1738570 4402937 := bstep (se 2 (by rfl) ⟨1651101, by rfl⟩ : syracuseStep 4402937 = 3302203) B3302203
theorem B22302479 : Blo 1738570 22302479 := bstep (se 1 (by rfl) ⟨16726859, by rfl⟩ : syracuseStep 22302479 = 33453719) B33453719
theorem B2608991 : Blo 1738570 2608991 := bstep (se 1 (by rfl) ⟨1956743, by rfl⟩ : syracuseStep 2608991 = 3913487) B3913487
theorem B2609003 : Blo 1738570 2609003 := bstep (se 1 (by rfl) ⟨1956752, by rfl⟩ : syracuseStep 2609003 = 3913505) B3913505
theorem B13209479 : Blo 1738570 13209479 := bstep (se 1 (by rfl) ⟨9907109, by rfl⟩ : syracuseStep 13209479 = 19814219) B19814219
theorem B4403119 : Blo 1738570 4403119 := bstep (se 1 (by rfl) ⟨3302339, by rfl⟩ : syracuseStep 4403119 = 6604679) B6604679
theorem B5869583 : Blo 1738570 5869583 := bstep (se 1 (by rfl) ⟨4402187, by rfl⟩ : syracuseStep 5869583 = 8804375) B8804375
theorem B2609231 : Blo 1738570 2609231 := bstep (se 1 (by rfl) ⟨1956923, by rfl⟩ : syracuseStep 2609231 = 3913847) B3913847
theorem B3526735 : Blo 1738570 3526735 := bstep (se 1 (by rfl) ⟨2645051, by rfl⟩ : syracuseStep 3526735 = 5290103) B5290103
theorem B2936911 : Blo 1738570 2936911 := bstep (se 1 (by rfl) ⟨2202683, by rfl⟩ : syracuseStep 2936911 = 4405367) B4405367
theorem B17174705 : Blo 1738570 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B2609351 : Blo 1738570 2609351 := bstep (se 1 (by rfl) ⟨1957013, by rfl⟩ : syracuseStep 2609351 = 3914027) B3914027
theorem B2937161 : Blo 1738570 2937161 := bstep (se 2 (by rfl) ⟨1101435, by rfl⟩ : syracuseStep 2937161 = 2202871) B2202871
theorem B8360279 : Blo 1738570 8360279 := bstep (se 1 (by rfl) ⟨6270209, by rfl⟩ : syracuseStep 8360279 = 12540419) B12540419
theorem B2609513 : Blo 1738570 2609513 := bstep (se 2 (by rfl) ⟨978567, by rfl⟩ : syracuseStep 2609513 = 1957135) B1957135
theorem B4403585 : Blo 1738570 4403585 := bstep (se 2 (by rfl) ⟨1651344, by rfl⟩ : syracuseStep 4403585 = 3302689) B3302689
theorem B2609591 : Blo 1738570 2609591 := bstep (se 1 (by rfl) ⟨1957193, by rfl⟩ : syracuseStep 2609591 = 3914387) B3914387
theorem B3912155 : Blo 1738570 3912155 := bstep (se 1 (by rfl) ⟨2934116, by rfl⟩ : syracuseStep 3912155 = 5868233) B5868233
theorem B2609627 : Blo 1738570 2609627 := bstep (se 1 (by rfl) ⟨1957220, by rfl⟩ : syracuseStep 2609627 = 3914441) B3914441
theorem B6271451 : Blo 1738570 6271451 := bstep (se 1 (by rfl) ⟨4703588, by rfl⟩ : syracuseStep 6271451 = 9407177) B9407177
theorem B8811017 : Blo 1738570 8811017 := bstep (se 2 (by rfl) ⟨3304131, by rfl⟩ : syracuseStep 8811017 = 6608263) B6608263
theorem B5870177 : Blo 1738570 5870177 := bstep (se 2 (by rfl) ⟨2201316, by rfl⟩ : syracuseStep 5870177 = 4402633) B4402633
theorem B5952211 : Blo 1738570 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B4404041 : Blo 1738570 4404041 := bstep (se 2 (by rfl) ⟨1651515, by rfl⟩ : syracuseStep 4404041 = 3303031) B3303031
theorem B6607777 : Blo 1738570 6607777 := bstep (se 2 (by rfl) ⟨2477916, by rfl⟩ : syracuseStep 6607777 = 4955833) B4955833
theorem B3912623 : Blo 1738570 3912623 := bstep (se 1 (by rfl) ⟨2934467, by rfl⟩ : syracuseStep 3912623 = 5868935) B5868935
theorem B2610095 : Blo 1738570 2610095 := bstep (se 1 (by rfl) ⟨1957571, by rfl⟩ : syracuseStep 2610095 = 3915143) B3915143
theorem B14857181 : Blo 1738570 14857181 := bstep (se 3 (by rfl) ⟨2785721, by rfl⟩ : syracuseStep 14857181 = 5571443) B5571443
theorem B2610185 : Blo 1738570 2610185 := bstep (se 2 (by rfl) ⟨978819, by rfl⟩ : syracuseStep 2610185 = 1957639) B1957639
theorem B2610215 : Blo 1738570 2610215 := bstep (se 1 (by rfl) ⟨1957661, by rfl⟩ : syracuseStep 2610215 = 3915323) B3915323
theorem B4953145 : Blo 1738570 4953145 := bstep (se 2 (by rfl) ⟨1857429, by rfl⟩ : syracuseStep 4953145 = 3714859) B3714859
theorem B11146319 : Blo 1738570 11146319 := bstep (se 1 (by rfl) ⟨8359739, by rfl⟩ : syracuseStep 11146319 = 16719479) B16719479
theorem B2200699 : Blo 1738570 2200699 := bstep (se 1 (by rfl) ⟨1650524, by rfl⟩ : syracuseStep 2200699 = 3301049) B3301049
theorem B2610299 : Blo 1738570 2610299 := bstep (se 1 (by rfl) ⟨1957724, by rfl⟩ : syracuseStep 2610299 = 3915449) B3915449
theorem B3912875 : Blo 1738570 3912875 := bstep (se 1 (by rfl) ⟨2934656, by rfl⟩ : syracuseStep 3912875 = 5869313) B5869313
theorem B4404395 : Blo 1738570 4404395 := bstep (se 1 (by rfl) ⟨3303296, by rfl⟩ : syracuseStep 4404395 = 6606593) B6606593
theorem B28202185 : Blo 1738570 28202185 := bstep (se 2 (by rfl) ⟨10575819, by rfl⟩ : syracuseStep 28202185 = 21151639) B21151639
theorem B2610425 : Blo 1738570 2610425 := bstep (se 2 (by rfl) ⟨978909, by rfl⟩ : syracuseStep 2610425 = 1957819) B1957819
theorem B2200927 : Blo 1738570 2200927 := bstep (se 1 (by rfl) ⟨1650695, by rfl⟩ : syracuseStep 2200927 = 3301391) B3301391
theorem B3528031 : Blo 1738570 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B2610527 : Blo 1738570 2610527 := bstep (se 1 (by rfl) ⟨1957895, by rfl⟩ : syracuseStep 2610527 = 3915791) B3915791
theorem B2610539 : Blo 1738570 2610539 := bstep (se 1 (by rfl) ⟨1957904, by rfl⟩ : syracuseStep 2610539 = 3915809) B3915809
theorem B8803727 : Blo 1738570 8803727 := bstep (se 1 (by rfl) ⟨6602795, by rfl⟩ : syracuseStep 8803727 = 13205591) B13205591
theorem B4953487 : Blo 1738570 4953487 := bstep (se 1 (by rfl) ⟨3715115, by rfl⟩ : syracuseStep 4953487 = 7430231) B7430231
theorem B28603793 : Blo 1738570 28603793 := bstep (se 2 (by rfl) ⟨10726422, by rfl⟩ : syracuseStep 28603793 = 21452845) B21452845
theorem B18798085 : Blo 1738570 18798085 := bstep (se 4 (by rfl) ⟨1762320, by rfl⟩ : syracuseStep 18798085 = 3524641) B3524641
theorem B2610767 : Blo 1738570 2610767 := bstep (se 1 (by rfl) ⟨1958075, by rfl⟩ : syracuseStep 2610767 = 3916151) B3916151
theorem B8361569 : Blo 1738570 8361569 := bstep (se 2 (by rfl) ⟨3135588, by rfl⟩ : syracuseStep 8361569 = 6271177) B6271177
theorem B3716705 : Blo 1738570 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B3913415 : Blo 1738570 3913415 := bstep (se 1 (by rfl) ⟨2935061, by rfl⟩ : syracuseStep 3913415 = 5870123) B5870123
theorem B14292695 : Blo 1738570 14292695 := bstep (se 1 (by rfl) ⟨10719521, by rfl⟩ : syracuseStep 14292695 = 21439043) B21439043
theorem B8361721 : Blo 1738570 8361721 := bstep (se 2 (by rfl) ⟨3135645, by rfl⟩ : syracuseStep 8361721 = 6271291) B6271291
theorem B13391675 : Blo 1738570 13391675 := bstep (se 1 (by rfl) ⟨10043756, by rfl⟩ : syracuseStep 13391675 = 20087513) B20087513
theorem B2201519 : Blo 1738570 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B4405175 : Blo 1738570 4405175 := bstep (se 1 (by rfl) ⟨3303881, by rfl⟩ : syracuseStep 4405175 = 6607763) B6607763
theorem B9533371 : Blo 1738570 9533371 := bstep (se 1 (by rfl) ⟨7150028, by rfl⟩ : syracuseStep 9533371 = 14300057) B14300057
theorem B5871635 : Blo 1738570 5871635 := bstep (se 1 (by rfl) ⟨4403726, by rfl⟩ : syracuseStep 5871635 = 8807453) B8807453
theorem B11147321 : Blo 1738570 11147321 := bstep (se 2 (by rfl) ⟨4180245, by rfl⟩ : syracuseStep 11147321 = 8360491) B8360491
theorem B11147345 : Blo 1738570 11147345 := bstep (se 2 (by rfl) ⟨4180254, by rfl⟩ : syracuseStep 11147345 = 8360509) B8360509
theorem B5871959 : Blo 1738570 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B1956271 : Blo 1738570 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B3914279 : Blo 1738570 3914279 := bstep (se 1 (by rfl) ⟨2935709, by rfl⟩ : syracuseStep 3914279 = 5871419) B5871419
theorem B4954763 : Blo 1738570 4954763 := bstep (se 1 (by rfl) ⟨3716072, by rfl⟩ : syracuseStep 4954763 = 7432145) B7432145
theorem B16718521 : Blo 1738570 16718521 := bstep (se 2 (by rfl) ⟨6269445, by rfl⟩ : syracuseStep 16718521 = 12538891) B12538891
theorem B1956703 : Blo 1738570 1956703 := bstep (se 1 (by rfl) ⟨1467527, by rfl⟩ : syracuseStep 1956703 = 2935055) B2935055
theorem B3914603 : Blo 1738570 3914603 := bstep (se 1 (by rfl) ⟨2935952, by rfl⟩ : syracuseStep 3914603 = 5871905) B5871905
theorem B13384595 : Blo 1738570 13384595 := bstep (se 1 (by rfl) ⟨10038446, by rfl⟩ : syracuseStep 13384595 = 20076893) B20076893
theorem B3914657 : Blo 1738570 3914657 := bstep (se 2 (by rfl) ⟨1467996, by rfl⟩ : syracuseStep 3914657 = 2935993) B2935993
theorem B1858523 : Blo 1738570 1858523 := bstep (se 1 (by rfl) ⟨1393892, by rfl⟩ : syracuseStep 1858523 = 2787785) B2787785
theorem B3136475 : Blo 1738570 3136475 := bstep (se 1 (by rfl) ⟨2352356, by rfl⟩ : syracuseStep 3136475 = 4704713) B4704713
theorem B1957063 : Blo 1738570 1957063 := bstep (se 1 (by rfl) ⟨1467797, by rfl⟩ : syracuseStep 1957063 = 2935595) B2935595
theorem B3914999 : Blo 1738570 3914999 := bstep (se 1 (by rfl) ⟨2936249, by rfl⟩ : syracuseStep 3914999 = 5872499) B5872499
theorem B3300601 : Blo 1738570 3300601 := bstep (se 2 (by rfl) ⟨1237725, by rfl⟩ : syracuseStep 3300601 = 2475451) B2475451
theorem B5569879 : Blo 1738570 5569879 := bstep (se 1 (by rfl) ⟨4177409, by rfl⟩ : syracuseStep 5569879 = 8354819) B8354819
theorem B5873039 : Blo 1738570 5873039 := bstep (se 1 (by rfl) ⟨4404779, by rfl⟩ : syracuseStep 5873039 = 8809559) B8809559
theorem B8805833 : Blo 1738570 8805833 := bstep (se 2 (by rfl) ⟨3302187, by rfl⟩ : syracuseStep 8805833 = 6604375) B6604375
theorem B6602249 : Blo 1738570 6602249 := bstep (se 2 (by rfl) ⟨2475843, by rfl⟩ : syracuseStep 6602249 = 4951687) B4951687
theorem B6356519 : Blo 1738570 6356519 := bstep (se 1 (by rfl) ⟨4767389, by rfl⟩ : syracuseStep 6356519 = 9534779) B9534779
theorem B4701835 : Blo 1738570 4701835 := bstep (se 1 (by rfl) ⟨3526376, by rfl⟩ : syracuseStep 4701835 = 7052753) B7052753
theorem B38657675 : Blo 1738570 38657675 := bstep (se 1 (by rfl) ⟨28993256, by rfl⟩ : syracuseStep 38657675 = 57986513) B57986513
theorem B5873363 : Blo 1738570 5873363 := bstep (se 1 (by rfl) ⟨4405022, by rfl⟩ : syracuseStep 5873363 = 8810045) B8810045
theorem B12541661 : Blo 1738570 12541661 := bstep (se 3 (by rfl) ⟨2351561, by rfl⟩ : syracuseStep 12541661 = 4703123) B4703123
theorem B3915593 : Blo 1738570 3915593 := bstep (se 2 (by rfl) ⟨1468347, by rfl⟩ : syracuseStep 3915593 = 2936695) B2936695
theorem B28204919 : Blo 1738570 28204919 := bstep (se 1 (by rfl) ⟨21153689, by rfl⟩ : syracuseStep 28204919 = 42307379) B42307379
theorem B3301307 : Blo 1738570 3301307 := bstep (se 1 (by rfl) ⟨2475980, by rfl⟩ : syracuseStep 3301307 = 4951961) B4951961
theorem B8363969 : Blo 1738570 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B11141171 : Blo 1738570 11141171 := bstep (se 1 (by rfl) ⟨8355878, by rfl⟩ : syracuseStep 11141171 = 16711757) B16711757
theorem B4702313 : Blo 1738570 4702313 := bstep (se 2 (by rfl) ⟨1763367, by rfl⟩ : syracuseStep 4702313 = 3526735) B3526735
theorem B3915881 : Blo 1738570 3915881 := bstep (se 2 (by rfl) ⟨1468455, by rfl⟩ : syracuseStep 3915881 = 2936911) B2936911
theorem B8356049 : Blo 1738570 8356049 := bstep (se 2 (by rfl) ⟨3133518, by rfl⟩ : syracuseStep 8356049 = 6267037) B6267037
theorem B1958107 : Blo 1738570 1958107 := bstep (se 1 (by rfl) ⟨1468580, by rfl⟩ : syracuseStep 1958107 = 2937161) B2937161
theorem B5874011 : Blo 1738570 5874011 := bstep (se 1 (by rfl) ⟨4405508, by rfl⟩ : syracuseStep 5874011 = 8811017) B8811017
theorem B9904787 : Blo 1738570 9904787 := bstep (se 1 (by rfl) ⟨7428590, by rfl⟩ : syracuseStep 9904787 = 14857181) B14857181
theorem B7430879 : Blo 1738570 7430879 := bstep (se 1 (by rfl) ⟨5573159, by rfl⟩ : syracuseStep 7430879 = 11146319) B11146319
theorem B22291361 : Blo 1738570 22291361 := bstep (se 2 (by rfl) ⟨8359260, by rfl⟩ : syracuseStep 22291361 = 16718521) B16718521
theorem B31745125 : Blo 1738570 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B9528463 : Blo 1738570 9528463 := bstep (se 1 (by rfl) ⟨7146347, by rfl⟩ : syracuseStep 9528463 = 14292695) B14292695
theorem B14861555 : Blo 1738570 14861555 := bstep (se 1 (by rfl) ⟨11146166, by rfl⟩ : syracuseStep 14861555 = 22292333) B22292333
theorem B4179323 : Blo 1738570 4179323 := bstep (se 1 (by rfl) ⟨3134492, by rfl⟩ : syracuseStep 4179323 = 6268985) B6268985
theorem B7431547 : Blo 1738570 7431547 := bstep (se 1 (by rfl) ⟨5573660, by rfl⟩ : syracuseStep 7431547 = 11147321) B11147321
theorem B7431563 : Blo 1738570 7431563 := bstep (se 1 (by rfl) ⟨5573672, by rfl⟩ : syracuseStep 7431563 = 11147345) B11147345
theorem B6604193 : Blo 1738570 6604193 := bstep (se 2 (by rfl) ⟨2476572, by rfl⟩ : syracuseStep 6604193 = 4953145) B4953145
theorem B2934265 : Blo 1738570 2934265 := bstep (se 2 (by rfl) ⟨1100349, by rfl⟩ : syracuseStep 2934265 = 2200699) B2200699
theorem B37602913 : Blo 1738570 37602913 := bstep (se 2 (by rfl) ⟨14101092, by rfl⟩ : syracuseStep 37602913 = 28202185) B28202185
theorem B4400801 : Blo 1738570 4400801 := bstep (se 2 (by rfl) ⟨1650300, by rfl⟩ : syracuseStep 4400801 = 3300601) B3300601
theorem B2934535 : Blo 1738570 2934535 := bstep (se 1 (by rfl) ⟨2200901, by rfl⟩ : syracuseStep 2934535 = 4401803) B4401803
theorem B3303175 : Blo 1738570 3303175 := bstep (se 1 (by rfl) ⟨2477381, by rfl⟩ : syracuseStep 3303175 = 4954763) B4954763
theorem B2934569 : Blo 1738570 2934569 := bstep (se 2 (by rfl) ⟨1100463, by rfl⟩ : syracuseStep 2934569 = 2200927) B2200927
theorem B4704041 : Blo 1738570 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B2787119 : Blo 1738570 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B6604649 : Blo 1738570 6604649 := bstep (se 2 (by rfl) ⟨2476743, by rfl⟩ : syracuseStep 6604649 = 4953487) B4953487
theorem B1738651 : Blo 1738570 1738651 := bstep (se 1 (by rfl) ⟨1303988, by rfl⟩ : syracuseStep 1738651 = 2607977) B2607977
theorem B8923063 : Blo 1738570 8923063 := bstep (se 1 (by rfl) ⟨6692297, by rfl⟩ : syracuseStep 8923063 = 13384595) B13384595
theorem B1738703 : Blo 1738570 1738703 := bstep (se 1 (by rfl) ⟨1304027, by rfl⟩ : syracuseStep 1738703 = 2608055) B2608055
theorem B1738727 : Blo 1738570 1738727 := bstep (se 1 (by rfl) ⟨1304045, by rfl⟩ : syracuseStep 1738727 = 2608091) B2608091
theorem B2090983 : Blo 1738570 2090983 := bstep (se 1 (by rfl) ⟨1568237, by rfl⟩ : syracuseStep 2090983 = 3136475) B3136475
theorem B6269113 : Blo 1738570 6269113 := bstep (se 2 (by rfl) ⟨2350917, by rfl⟩ : syracuseStep 6269113 = 4701835) B4701835
theorem B25069763 : Blo 1738570 25069763 := bstep (se 1 (by rfl) ⟨18802322, by rfl⟩ : syracuseStep 25069763 = 37604645) B37604645
theorem B5867801 : Blo 1738570 5867801 := bstep (se 2 (by rfl) ⟨2200425, by rfl⟩ : syracuseStep 5867801 = 4400851) B4400851
theorem B1739039 : Blo 1738570 1739039 := bstep (se 1 (by rfl) ⟨1304279, by rfl⟩ : syracuseStep 1739039 = 2608559) B2608559
theorem B4401499 : Blo 1738570 4401499 := bstep (se 1 (by rfl) ⟨3301124, by rfl⟩ : syracuseStep 4401499 = 6602249) B6602249
theorem B1739099 : Blo 1738570 1739099 := bstep (se 1 (by rfl) ⟨1304324, by rfl⟩ : syracuseStep 1739099 = 2608649) B2608649
theorem B2476379 : Blo 1738570 2476379 := bstep (se 1 (by rfl) ⟨1857284, by rfl⟩ : syracuseStep 2476379 = 3714569) B3714569
theorem B1739119 : Blo 1738570 1739119 := bstep (se 1 (by rfl) ⟨1304339, by rfl⟩ : syracuseStep 1739119 = 2608679) B2608679
theorem B4237679 : Blo 1738570 4237679 := bstep (se 1 (by rfl) ⟨3178259, by rfl⟩ : syracuseStep 4237679 = 6356519) B6356519
theorem B1739175 : Blo 1738570 1739175 := bstep (se 1 (by rfl) ⟨1304381, by rfl⟩ : syracuseStep 1739175 = 2608763) B2608763
theorem B1739259 : Blo 1738570 1739259 := bstep (se 1 (by rfl) ⟨1304444, by rfl⟩ : syracuseStep 1739259 = 2608889) B2608889
theorem B2935291 : Blo 1738570 2935291 := bstep (se 1 (by rfl) ⟨2201468, by rfl⟩ : syracuseStep 2935291 = 4402937) B4402937
theorem B1739327 : Blo 1738570 1739327 := bstep (se 1 (by rfl) ⟨1304495, by rfl⟩ : syracuseStep 1739327 = 2608991) B2608991
theorem B1739335 : Blo 1738570 1739335 := bstep (se 1 (by rfl) ⟨1304501, by rfl⟩ : syracuseStep 1739335 = 2609003) B2609003
theorem B18803279 : Blo 1738570 18803279 := bstep (se 1 (by rfl) ⟨14102459, by rfl⟩ : syracuseStep 18803279 = 28204919) B28204919
theorem B1739487 : Blo 1738570 1739487 := bstep (se 1 (by rfl) ⟨1304615, by rfl⟩ : syracuseStep 1739487 = 2609231) B2609231
theorem B8809235 : Blo 1738570 8809235 := bstep (se 1 (by rfl) ⟨6606926, by rfl⟩ : syracuseStep 8809235 = 13213853) B13213853
theorem B1739567 : Blo 1738570 1739567 := bstep (se 1 (by rfl) ⟨1304675, by rfl⟩ : syracuseStep 1739567 = 2609351) B2609351
theorem B5573519 : Blo 1738570 5573519 := bstep (se 1 (by rfl) ⟨4180139, by rfl⟩ : syracuseStep 5573519 = 8360279) B8360279
theorem B1739675 : Blo 1738570 1739675 := bstep (se 1 (by rfl) ⟨1304756, by rfl⟩ : syracuseStep 1739675 = 2609513) B2609513
theorem B2935723 : Blo 1738570 2935723 := bstep (se 1 (by rfl) ⟨2201792, by rfl⟩ : syracuseStep 2935723 = 4403585) B4403585
theorem B1739727 : Blo 1738570 1739727 := bstep (se 1 (by rfl) ⟨1304795, by rfl⟩ : syracuseStep 1739727 = 2609591) B2609591
theorem B2608103 : Blo 1738570 2608103 := bstep (se 1 (by rfl) ⟨1956077, by rfl⟩ : syracuseStep 2608103 = 3912155) B3912155
theorem B1739751 : Blo 1738570 1739751 := bstep (se 1 (by rfl) ⟨1304813, by rfl⟩ : syracuseStep 1739751 = 2609627) B2609627
theorem B4180967 : Blo 1738570 4180967 := bstep (se 1 (by rfl) ⟨3135725, by rfl⟩ : syracuseStep 4180967 = 6271451) B6271451
theorem B7433203 : Blo 1738570 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B101682377 : Blo 1738570 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B2936027 : Blo 1738570 2936027 := bstep (se 1 (by rfl) ⟨2202020, by rfl⟩ : syracuseStep 2936027 = 4404041) B4404041
theorem B2608361 : Blo 1738570 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B2608415 : Blo 1738570 2608415 := bstep (se 1 (by rfl) ⟨1956311, by rfl⟩ : syracuseStep 2608415 = 3912623) B3912623
theorem B1740063 : Blo 1738570 1740063 := bstep (se 1 (by rfl) ⟨1305047, by rfl⟩ : syracuseStep 1740063 = 2610095) B2610095
theorem B4402471 : Blo 1738570 4402471 := bstep (se 1 (by rfl) ⟨3301853, by rfl⟩ : syracuseStep 4402471 = 6603707) B6603707
theorem B26791229 : Blo 1738570 26791229 := bstep (se 3 (by rfl) ⟨5023355, by rfl⟩ : syracuseStep 26791229 = 10046711) B10046711
theorem B1740123 : Blo 1738570 1740123 := bstep (se 1 (by rfl) ⟨1305092, by rfl⟩ : syracuseStep 1740123 = 2610185) B2610185
theorem B1740143 : Blo 1738570 1740143 := bstep (se 1 (by rfl) ⟨1305107, by rfl⟩ : syracuseStep 1740143 = 2610215) B2610215
theorem B1740199 : Blo 1738570 1740199 := bstep (se 1 (by rfl) ⟨1305149, by rfl⟩ : syracuseStep 1740199 = 2610299) B2610299
theorem B2608583 : Blo 1738570 2608583 := bstep (se 1 (by rfl) ⟨1956437, by rfl⟩ : syracuseStep 2608583 = 3912875) B3912875
theorem B2936263 : Blo 1738570 2936263 := bstep (se 1 (by rfl) ⟨2202197, by rfl⟩ : syracuseStep 2936263 = 4404395) B4404395
theorem B1740283 : Blo 1738570 1740283 := bstep (se 1 (by rfl) ⟨1305212, by rfl⟩ : syracuseStep 1740283 = 2610425) B2610425
theorem B8359433 : Blo 1738570 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B4402745 : Blo 1738570 4402745 := bstep (se 2 (by rfl) ⟨1651029, by rfl⟩ : syracuseStep 4402745 = 3302059) B3302059
theorem B1740351 : Blo 1738570 1740351 := bstep (se 1 (by rfl) ⟨1305263, by rfl⟩ : syracuseStep 1740351 = 2610527) B2610527
theorem B1740359 : Blo 1738570 1740359 := bstep (se 1 (by rfl) ⟨1305269, by rfl⟩ : syracuseStep 1740359 = 2610539) B2610539
theorem B5869151 : Blo 1738570 5869151 := bstep (se 1 (by rfl) ⟨4401863, by rfl⟩ : syracuseStep 5869151 = 8803727) B8803727
theorem B15060653 : Blo 1738570 15060653 := bstep (se 3 (by rfl) ⟨2823872, by rfl⟩ : syracuseStep 15060653 = 5647745) B5647745
theorem B1740511 : Blo 1738570 1740511 := bstep (se 1 (by rfl) ⟨1305383, by rfl⟩ : syracuseStep 1740511 = 2610767) B2610767
theorem B5574379 : Blo 1738570 5574379 := bstep (se 1 (by rfl) ⟨4180784, by rfl⟩ : syracuseStep 5574379 = 8361569) B8361569
theorem B2477803 : Blo 1738570 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B7057163 : Blo 1738570 7057163 := bstep (se 1 (by rfl) ⟨5292872, by rfl⟩ : syracuseStep 7057163 = 10585745) B10585745
theorem B2608937 : Blo 1738570 2608937 := bstep (se 2 (by rfl) ⟨978351, by rfl⟩ : syracuseStep 2608937 = 1956703) B1956703
theorem B2608943 : Blo 1738570 2608943 := bstep (se 1 (by rfl) ⟨1956707, by rfl⟩ : syracuseStep 2608943 = 3913415) B3913415
theorem B6696761 : Blo 1738570 6696761 := bstep (se 2 (by rfl) ⟨2511285, by rfl⟩ : syracuseStep 6696761 = 5022571) B5022571
theorem B8810369 : Blo 1738570 8810369 := bstep (se 2 (by rfl) ⟨3303888, by rfl⟩ : syracuseStep 8810369 = 6607777) B6607777
theorem B2936783 : Blo 1738570 2936783 := bstep (se 1 (by rfl) ⟨2202587, by rfl⟩ : syracuseStep 2936783 = 4405175) B4405175
theorem B7934057 : Blo 1738570 7934057 := bstep (se 2 (by rfl) ⟨2975271, by rfl⟩ : syracuseStep 7934057 = 5950543) B5950543
theorem B16724171 : Blo 1738570 16724171 := bstep (se 1 (by rfl) ⟨12543128, by rfl⟩ : syracuseStep 16724171 = 25086257) B25086257
theorem B2609417 : Blo 1738570 2609417 := bstep (se 2 (by rfl) ⟨978531, by rfl⟩ : syracuseStep 2609417 = 1957063) B1957063
theorem B31732073 : Blo 1738570 31732073 := bstep (se 2 (by rfl) ⟨11899527, by rfl⟩ : syracuseStep 31732073 = 23799055) B23799055
theorem B3912047 : Blo 1738570 3912047 := bstep (se 1 (by rfl) ⟨2934035, by rfl⟩ : syracuseStep 3912047 = 5868071) B5868071
theorem B2609519 : Blo 1738570 2609519 := bstep (se 1 (by rfl) ⟨1957139, by rfl⟩ : syracuseStep 2609519 = 3914279) B3914279
theorem B3912119 : Blo 1738570 3912119 := bstep (se 1 (by rfl) ⟨2934089, by rfl⟩ : syracuseStep 3912119 = 5868179) B5868179
theorem B7426505 : Blo 1738570 7426505 := bstep (se 2 (by rfl) ⟨2784939, by rfl⟩ : syracuseStep 7426505 = 5569879) B5569879
theorem B29716955 : Blo 1738570 29716955 := bstep (se 1 (by rfl) ⟨22287716, by rfl⟩ : syracuseStep 29716955 = 44575433) B44575433
theorem B3912263 : Blo 1738570 3912263 := bstep (se 1 (by rfl) ⟨2934197, by rfl⟩ : syracuseStep 3912263 = 5868395) B5868395
theorem B2609735 : Blo 1738570 2609735 := bstep (se 1 (by rfl) ⟨1957301, by rfl⟩ : syracuseStep 2609735 = 3914603) B3914603
theorem B3912299 : Blo 1738570 3912299 := bstep (se 1 (by rfl) ⟨2934224, by rfl⟩ : syracuseStep 3912299 = 5868449) B5868449
theorem B2609771 : Blo 1738570 2609771 := bstep (se 1 (by rfl) ⟨1957328, by rfl⟩ : syracuseStep 2609771 = 3914657) B3914657
theorem B8811179 : Blo 1738570 8811179 := bstep (se 1 (by rfl) ⟨6608384, by rfl⟩ : syracuseStep 8811179 = 13216769) B13216769
theorem B25064113 : Blo 1738570 25064113 := bstep (se 2 (by rfl) ⟨9399042, by rfl⟩ : syracuseStep 25064113 = 18798085) B18798085
theorem B2716343 : Blo 1738570 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B2609999 : Blo 1738570 2609999 := bstep (se 1 (by rfl) ⟨1957499, by rfl⟩ : syracuseStep 2609999 = 3914999) B3914999
theorem B5870555 : Blo 1738570 5870555 := bstep (se 1 (by rfl) ⟨4402916, by rfl⟩ : syracuseStep 5870555 = 8805833) B8805833
theorem B3912695 : Blo 1738570 3912695 := bstep (se 1 (by rfl) ⟨2934521, by rfl⟩ : syracuseStep 3912695 = 5869043) B5869043
theorem B5870717 : Blo 1738570 5870717 := bstep (se 3 (by rfl) ⟨1100759, by rfl⟩ : syracuseStep 5870717 = 2201519) B2201519
theorem B8361107 : Blo 1738570 8361107 := bstep (se 1 (by rfl) ⟨6270830, by rfl⟩ : syracuseStep 8361107 = 12541661) B12541661
theorem B2610395 : Blo 1738570 2610395 := bstep (se 1 (by rfl) ⟨1957796, by rfl⟩ : syracuseStep 2610395 = 3915593) B3915593
theorem B5870825 : Blo 1738570 5870825 := bstep (se 2 (by rfl) ⟨2201559, by rfl⟩ : syracuseStep 5870825 = 4403119) B4403119
theorem B12711161 : Blo 1738570 12711161 := bstep (se 2 (by rfl) ⟨4766685, by rfl⟩ : syracuseStep 12711161 = 9533371) B9533371
theorem B2200871 : Blo 1738570 2200871 := bstep (se 1 (by rfl) ⟨1650653, by rfl⟩ : syracuseStep 2200871 = 3301307) B3301307
theorem B5575979 : Blo 1738570 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B3913055 : Blo 1738570 3913055 := bstep (se 1 (by rfl) ⟨2934791, by rfl⟩ : syracuseStep 3913055 = 5869583) B5869583
theorem B4404577 : Blo 1738570 4404577 := bstep (se 2 (by rfl) ⟨1651716, by rfl⟩ : syracuseStep 4404577 = 3303433) B3303433
theorem B2610569 : Blo 1738570 2610569 := bstep (se 2 (by rfl) ⟨978963, by rfl⟩ : syracuseStep 2610569 = 1957927) B1957927
theorem B5870987 : Blo 1738570 5870987 := bstep (se 1 (by rfl) ⟨4403240, by rfl⟩ : syracuseStep 5870987 = 8806481) B8806481
theorem B2201195 : Blo 1738570 2201195 := bstep (se 1 (by rfl) ⟨1650896, by rfl⟩ : syracuseStep 2201195 = 3301793) B3301793
theorem B7427771 : Blo 1738570 7427771 := bstep (se 1 (by rfl) ⟨5570828, by rfl⟩ : syracuseStep 7427771 = 11141657) B11141657
theorem B3913451 : Blo 1738570 3913451 := bstep (se 1 (by rfl) ⟨2935088, by rfl⟩ : syracuseStep 3913451 = 5870177) B5870177
theorem B3913577 : Blo 1738570 3913577 := bstep (se 2 (by rfl) ⟨1467591, by rfl⟩ : syracuseStep 3913577 = 2935183) B2935183
theorem B2201575 : Blo 1738570 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B17848349 : Blo 1738570 17848349 := bstep (se 3 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 17848349 = 6693131) B6693131
theorem B8804537 : Blo 1738570 8804537 := bstep (se 2 (by rfl) ⟨3301701, by rfl⟩ : syracuseStep 8804537 = 6603403) B6603403
theorem B14866679 : Blo 1738570 14866679 := bstep (se 1 (by rfl) ⟨11150009, by rfl⟩ : syracuseStep 14866679 = 22300019) B22300019
theorem B19069195 : Blo 1738570 19069195 := bstep (se 1 (by rfl) ⟨14301896, by rfl⟩ : syracuseStep 19069195 = 28603793) B28603793
theorem B4405529 : Blo 1738570 4405529 := bstep (se 2 (by rfl) ⟨1652073, by rfl⟩ : syracuseStep 4405529 = 3304147) B3304147
theorem B1956127 : Blo 1738570 1956127 := bstep (se 1 (by rfl) ⟨1467095, by rfl⟩ : syracuseStep 1956127 = 2934191) B2934191
theorem B8927783 : Blo 1738570 8927783 := bstep (se 1 (by rfl) ⟨6695837, by rfl⟩ : syracuseStep 8927783 = 13391675) B13391675
theorem B1956415 : Blo 1738570 1956415 := bstep (se 1 (by rfl) ⟨1467311, by rfl⟩ : syracuseStep 1956415 = 2934623) B2934623
theorem B3914423 : Blo 1738570 3914423 := bstep (se 1 (by rfl) ⟨2935817, by rfl⟩ : syracuseStep 3914423 = 5871635) B5871635
theorem B3914639 : Blo 1738570 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B25082909 : Blo 1738570 25082909 := bstep (se 3 (by rfl) ⟨4703045, by rfl⟩ : syracuseStep 25082909 = 9406091) B9406091
theorem B8363047 : Blo 1738570 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B183196853 : Blo 1738570 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B40180931 : Blo 1738570 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B6266231 : Blo 1738570 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B1957243 : Blo 1738570 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B3300745 : Blo 1738570 3300745 := bstep (se 2 (by rfl) ⟨1237779, by rfl⟩ : syracuseStep 3300745 = 2475559) B2475559
theorem B12533129 : Blo 1738570 12533129 := bstep (se 2 (by rfl) ⟨4699923, by rfl⟩ : syracuseStep 12533129 = 9399847) B9399847
theorem B38149541 : Blo 1738570 38149541 := bstep (se 4 (by rfl) ⟨3576519, by rfl⟩ : syracuseStep 38149541 = 7153039) B7153039
theorem B16727633 : Blo 1738570 16727633 := bstep (se 2 (by rfl) ⟨6272862, by rfl⟩ : syracuseStep 16727633 = 12545725) B12545725
theorem B3915359 : Blo 1738570 3915359 := bstep (se 1 (by rfl) ⟨2936519, by rfl⟩ : syracuseStep 3915359 = 5873039) B5873039
theorem B11148961 : Blo 1738570 11148961 := bstep (se 2 (by rfl) ⟨4180860, by rfl⟩ : syracuseStep 11148961 = 8361721) B8361721
theorem B25771783 : Blo 1738570 25771783 := bstep (se 1 (by rfl) ⟨19328837, by rfl⟩ : syracuseStep 25771783 = 38657675) B38657675
theorem B3915575 : Blo 1738570 3915575 := bstep (se 1 (by rfl) ⟨2936681, by rfl⟩ : syracuseStep 3915575 = 5873363) B5873363
theorem B1957711 : Blo 1738570 1957711 := bstep (se 1 (by rfl) ⟨1468283, by rfl⟩ : syracuseStep 1957711 = 2936567) B2936567
theorem B14868319 : Blo 1738570 14868319 := bstep (se 1 (by rfl) ⟨11151239, by rfl⟩ : syracuseStep 14868319 = 22302479) B22302479
theorem B4956061 : Blo 1738570 4956061 := bstep (se 3 (by rfl) ⟨929261, by rfl⟩ : syracuseStep 4956061 = 1858523) B1858523
theorem B8806319 : Blo 1738570 8806319 := bstep (se 1 (by rfl) ⟨6604739, by rfl⟩ : syracuseStep 8806319 = 13209479) B13209479
theorem B11149447 : Blo 1738570 11149447 := bstep (se 1 (by rfl) ⟨8362085, by rfl⟩ : syracuseStep 11149447 = 16724171) B16724171
theorem B5570699 : Blo 1738570 5570699 := bstep (se 1 (by rfl) ⟨4178024, by rfl⟩ : syracuseStep 5570699 = 8356049) B8356049
theorem B3916007 : Blo 1738570 3916007 := bstep (se 1 (by rfl) ⟨2937005, by rfl⟩ : syracuseStep 3916007 = 5874011) B5874011
theorem B6603191 : Blo 1738570 6603191 := bstep (se 1 (by rfl) ⟨4952393, by rfl⟩ : syracuseStep 6603191 = 9904787) B9904787
theorem B5874119 : Blo 1738570 5874119 := bstep (se 1 (by rfl) ⟨4405589, by rfl⟩ : syracuseStep 5874119 = 8811179) B8811179
theorem B1810895 : Blo 1738570 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B14860907 : Blo 1738570 14860907 := bstep (se 1 (by rfl) ⟨11145680, by rfl⟩ : syracuseStep 14860907 = 22291361) B22291361
theorem B14869277 : Blo 1738570 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B6603677 : Blo 1738570 6603677 := bstep (se 3 (by rfl) ⟨1238189, by rfl⟩ : syracuseStep 6603677 = 2476379) B2476379
theorem B2933867 : Blo 1738570 2933867 := bstep (se 1 (by rfl) ⟨2200400, by rfl⟩ : syracuseStep 2933867 = 4400801) B4400801
theorem B11150729 : Blo 1738570 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B16713175 : Blo 1738570 16713175 := bstep (se 1 (by rfl) ⟨12534881, by rfl⟩ : syracuseStep 16713175 = 25069763) B25069763
theorem B12535519 : Blo 1738570 12535519 := bstep (se 1 (by rfl) ⟨9401639, by rfl⟩ : syracuseStep 12535519 = 18803279) B18803279
theorem B4400993 : Blo 1738570 4400993 := bstep (se 2 (by rfl) ⟨1650372, by rfl⟩ : syracuseStep 4400993 = 3300745) B3300745
theorem B1738735 : Blo 1738570 1738735 := bstep (se 1 (by rfl) ⟨1304051, by rfl⟩ : syracuseStep 1738735 = 2608103) B2608103
theorem B2787311 : Blo 1738570 2787311 := bstep (se 1 (by rfl) ⟨2090483, by rfl⟩ : syracuseStep 2787311 = 4180967) B4180967
theorem B16721939 : Blo 1738570 16721939 := bstep (se 1 (by rfl) ⟨12541454, by rfl⟩ : syracuseStep 16721939 = 25082909) B25082909
theorem B18819101 : Blo 1738570 18819101 := bstep (se 3 (by rfl) ⟨3528581, by rfl⟩ : syracuseStep 18819101 = 7057163) B7057163
theorem B12544109 : Blo 1738570 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B50137217 : Blo 1738570 50137217 := bstep (se 2 (by rfl) ⟨18801456, by rfl⟩ : syracuseStep 50137217 = 37602913) B37602913
theorem B1738907 : Blo 1738570 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B1738943 : Blo 1738570 1738943 := bstep (se 1 (by rfl) ⟨1304207, by rfl⟩ : syracuseStep 1738943 = 2608415) B2608415
theorem B17860819 : Blo 1738570 17860819 := bstep (se 1 (by rfl) ⟨13395614, by rfl⟩ : syracuseStep 17860819 = 26791229) B26791229
theorem B1739055 : Blo 1738570 1739055 := bstep (se 1 (by rfl) ⟨1304291, by rfl⟩ : syracuseStep 1739055 = 2608583) B2608583
theorem B7432505 : Blo 1738570 7432505 := bstep (se 2 (by rfl) ⟨2787189, by rfl⟩ : syracuseStep 7432505 = 5574379) B5574379
theorem B3303737 : Blo 1738570 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B5572955 : Blo 1738570 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B2935163 : Blo 1738570 2935163 := bstep (se 1 (by rfl) ⟨2201372, by rfl⟩ : syracuseStep 2935163 = 4402745) B4402745
theorem B11151755 : Blo 1738570 11151755 := bstep (se 1 (by rfl) ⟨8363816, by rfl⟩ : syracuseStep 11151755 = 16727633) B16727633
theorem B1739291 : Blo 1738570 1739291 := bstep (se 1 (by rfl) ⟨1304468, by rfl⟩ : syracuseStep 1739291 = 2608937) B2608937
theorem B1739295 : Blo 1738570 1739295 := bstep (se 1 (by rfl) ⟨1304471, by rfl⟩ : syracuseStep 1739295 = 2608943) B2608943
theorem B11897417 : Blo 1738570 11897417 := bstep (se 2 (by rfl) ⟨4461531, by rfl⟩ : syracuseStep 11897417 = 8923063) B8923063
theorem B2935433 : Blo 1738570 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B2787977 : Blo 1738570 2787977 := bstep (se 2 (by rfl) ⟨1045491, by rfl⟩ : syracuseStep 2787977 = 2090983) B2090983
theorem B1739611 : Blo 1738570 1739611 := bstep (se 1 (by rfl) ⟨1304708, by rfl⟩ : syracuseStep 1739611 = 2609417) B2609417
theorem B21154715 : Blo 1738570 21154715 := bstep (se 1 (by rfl) ⟨15866036, by rfl⟩ : syracuseStep 21154715 = 31732073) B31732073
theorem B2608031 : Blo 1738570 2608031 := bstep (se 1 (by rfl) ⟨1956023, by rfl⟩ : syracuseStep 2608031 = 3912047) B3912047
theorem B1739679 : Blo 1738570 1739679 := bstep (se 1 (by rfl) ⟨1304759, by rfl⟩ : syracuseStep 1739679 = 2609519) B2609519
theorem B8358817 : Blo 1738570 8358817 := bstep (se 2 (by rfl) ⟨3134556, by rfl⟩ : syracuseStep 8358817 = 6269113) B6269113
theorem B2608079 : Blo 1738570 2608079 := bstep (se 1 (by rfl) ⟨1956059, by rfl⟩ : syracuseStep 2608079 = 3912119) B3912119
theorem B19811303 : Blo 1738570 19811303 := bstep (se 1 (by rfl) ⟨14858477, by rfl⟩ : syracuseStep 19811303 = 29716955) B29716955
theorem B2608169 : Blo 1738570 2608169 := bstep (se 2 (by rfl) ⟨978063, by rfl⟩ : syracuseStep 2608169 = 1956127) B1956127
theorem B2608175 : Blo 1738570 2608175 := bstep (se 1 (by rfl) ⟨1956131, by rfl⟩ : syracuseStep 2608175 = 3912263) B3912263
theorem B1739823 : Blo 1738570 1739823 := bstep (se 1 (by rfl) ⟨1304867, by rfl⟩ : syracuseStep 1739823 = 2609735) B2609735
theorem B2608199 : Blo 1738570 2608199 := bstep (se 1 (by rfl) ⟨1956149, by rfl⟩ : syracuseStep 2608199 = 3912299) B3912299
theorem B1739847 : Blo 1738570 1739847 := bstep (se 1 (by rfl) ⟨1304885, by rfl⟩ : syracuseStep 1739847 = 2609771) B2609771
theorem B5868665 : Blo 1738570 5868665 := bstep (se 2 (by rfl) ⟨2200749, by rfl⟩ : syracuseStep 5868665 = 4401499) B4401499
theorem B1739999 : Blo 1738570 1739999 := bstep (se 1 (by rfl) ⟨1304999, by rfl⟩ : syracuseStep 1739999 = 2609999) B2609999
theorem B2608463 : Blo 1738570 2608463 := bstep (se 1 (by rfl) ⟨1956347, by rfl⟩ : syracuseStep 2608463 = 3912695) B3912695
theorem B2608553 : Blo 1738570 2608553 := bstep (se 2 (by rfl) ⟨978207, by rfl⟩ : syracuseStep 2608553 = 1956415) B1956415
theorem B5574071 : Blo 1738570 5574071 := bstep (se 1 (by rfl) ⟨4180553, by rfl⟩ : syracuseStep 5574071 = 8361107) B8361107
theorem B5868989 : Blo 1738570 5868989 := bstep (se 3 (by rfl) ⟨1100435, by rfl⟩ : syracuseStep 5868989 = 2200871) B2200871
theorem B1740263 : Blo 1738570 1740263 := bstep (se 1 (by rfl) ⟨1305197, by rfl⟩ : syracuseStep 1740263 = 2610395) B2610395
theorem B9907703 : Blo 1738570 9907703 := bstep (se 1 (by rfl) ⟨7430777, by rfl⟩ : syracuseStep 9907703 = 14861555) B14861555
theorem B8474107 : Blo 1738570 8474107 := bstep (se 1 (by rfl) ⟨6355580, by rfl⟩ : syracuseStep 8474107 = 12711161) B12711161
theorem B2608703 : Blo 1738570 2608703 := bstep (se 1 (by rfl) ⟨1956527, by rfl⟩ : syracuseStep 2608703 = 3913055) B3913055
theorem B33418817 : Blo 1738570 33418817 := bstep (se 2 (by rfl) ⟨12532056, by rfl⟩ : syracuseStep 33418817 = 25064113) B25064113
theorem B1740379 : Blo 1738570 1740379 := bstep (se 1 (by rfl) ⟨1305284, by rfl⟩ : syracuseStep 1740379 = 2610569) B2610569
theorem B4402795 : Blo 1738570 4402795 := bstep (se 1 (by rfl) ⟨3302096, by rfl⟩ : syracuseStep 4402795 = 6604193) B6604193
theorem B11144861 : Blo 1738570 11144861 := bstep (se 3 (by rfl) ⟨2089661, by rfl⟩ : syracuseStep 11144861 = 4179323) B4179323
theorem B4951847 : Blo 1738570 4951847 := bstep (se 1 (by rfl) ⟨3713885, by rfl⟩ : syracuseStep 4951847 = 7427771) B7427771
theorem B2608967 : Blo 1738570 2608967 := bstep (se 1 (by rfl) ⟨1956725, by rfl⟩ : syracuseStep 2608967 = 3913451) B3913451
theorem B19804013 : Blo 1738570 19804013 := bstep (se 3 (by rfl) ⟨3713252, by rfl⟩ : syracuseStep 19804013 = 7426505) B7426505
theorem B2609051 : Blo 1738570 2609051 := bstep (se 1 (by rfl) ⟨1956788, by rfl⟩ : syracuseStep 2609051 = 3913577) B3913577
theorem B4403099 : Blo 1738570 4403099 := bstep (se 1 (by rfl) ⟨3302324, by rfl⟩ : syracuseStep 4403099 = 6604649) B6604649
theorem B11898899 : Blo 1738570 11898899 := bstep (se 1 (by rfl) ⟨8924174, by rfl⟩ : syracuseStep 11898899 = 17848349) B17848349
theorem B5869691 : Blo 1738570 5869691 := bstep (se 1 (by rfl) ⟨4402268, by rfl⟩ : syracuseStep 5869691 = 8804537) B8804537
theorem B3911867 : Blo 1738570 3911867 := bstep (se 1 (by rfl) ⟨2933900, by rfl⟩ : syracuseStep 3911867 = 5867801) B5867801
theorem B2937019 : Blo 1738570 2937019 := bstep (se 1 (by rfl) ⟨2202764, by rfl⟩ : syracuseStep 2937019 = 4405529) B4405529
theorem B5869853 : Blo 1738570 5869853 := bstep (se 3 (by rfl) ⟨1100597, by rfl⟩ : syracuseStep 5869853 = 2201195) B2201195
theorem B5951855 : Blo 1738570 5951855 := bstep (se 1 (by rfl) ⟨4463891, by rfl⟩ : syracuseStep 5951855 = 8927783) B8927783
theorem B5869961 : Blo 1738570 5869961 := bstep (se 2 (by rfl) ⟨2201235, by rfl⟩ : syracuseStep 5869961 = 4402471) B4402471
theorem B2609615 : Blo 1738570 2609615 := bstep (se 1 (by rfl) ⟨1957211, by rfl⟩ : syracuseStep 2609615 = 3914423) B3914423
theorem B2609657 : Blo 1738570 2609657 := bstep (se 2 (by rfl) ⟨978621, by rfl⟩ : syracuseStep 2609657 = 1957243) B1957243
theorem B9908729 : Blo 1738570 9908729 := bstep (se 2 (by rfl) ⟨3715773, by rfl⟩ : syracuseStep 9908729 = 7431547) B7431547
theorem B3715679 : Blo 1738570 3715679 := bstep (se 1 (by rfl) ⟨2786759, by rfl⟩ : syracuseStep 3715679 = 5573519) B5573519
theorem B2609759 : Blo 1738570 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B3912353 : Blo 1738570 3912353 := bstep (se 2 (by rfl) ⟨1467132, by rfl⟩ : syracuseStep 3912353 = 2934265) B2934265
theorem B122131235 : Blo 1738570 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B14865281 : Blo 1738570 14865281 := bstep (se 2 (by rfl) ⟨5574480, by rfl⟩ : syracuseStep 14865281 = 11148961) B11148961
theorem B25433027 : Blo 1738570 25433027 := bstep (se 1 (by rfl) ⟨19074770, by rfl⟩ : syracuseStep 25433027 = 38149541) B38149541
theorem B3912713 : Blo 1738570 3912713 := bstep (se 2 (by rfl) ⟨1467267, by rfl⟩ : syracuseStep 3912713 = 2934535) B2934535
theorem B34362377 : Blo 1738570 34362377 := bstep (se 2 (by rfl) ⟨12885891, by rfl⟩ : syracuseStep 34362377 = 25771783) B25771783
theorem B4404233 : Blo 1738570 4404233 := bstep (se 2 (by rfl) ⟨1651587, by rfl⟩ : syracuseStep 4404233 = 3303175) B3303175
theorem B3912767 : Blo 1738570 3912767 := bstep (se 1 (by rfl) ⟨2934575, by rfl⟩ : syracuseStep 3912767 = 5869151) B5869151
theorem B2610239 : Blo 1738570 2610239 := bstep (se 1 (by rfl) ⟨1957679, by rfl⟩ : syracuseStep 2610239 = 3915359) B3915359
theorem B2610281 : Blo 1738570 2610281 := bstep (se 2 (by rfl) ⟨978855, by rfl⟩ : syracuseStep 2610281 = 1957711) B1957711
theorem B10040435 : Blo 1738570 10040435 := bstep (se 1 (by rfl) ⟨7530326, by rfl⟩ : syracuseStep 10040435 = 15060653) B15060653
theorem B2610383 : Blo 1738570 2610383 := bstep (se 1 (by rfl) ⟨1957787, by rfl⟩ : syracuseStep 2610383 = 3915575) B3915575
theorem B6608081 : Blo 1738570 6608081 := bstep (se 2 (by rfl) ⟨2478030, by rfl⟩ : syracuseStep 6608081 = 4956061) B4956061
theorem B5870879 : Blo 1738570 5870879 := bstep (se 1 (by rfl) ⟨4403159, by rfl⟩ : syracuseStep 5870879 = 8806319) B8806319
theorem B7427447 : Blo 1738570 7427447 := bstep (se 1 (by rfl) ⟨5570585, by rfl⟩ : syracuseStep 7427447 = 11141171) B11141171
theorem B5289371 : Blo 1738570 5289371 := bstep (se 1 (by rfl) ⟨3967028, by rfl⟩ : syracuseStep 5289371 = 7934057) B7934057
theorem B3134875 : Blo 1738570 3134875 := bstep (se 1 (by rfl) ⟨2351156, by rfl⟩ : syracuseStep 3134875 = 4702313) B4702313
theorem B2610587 : Blo 1738570 2610587 := bstep (se 1 (by rfl) ⟨1957940, by rfl⟩ : syracuseStep 2610587 = 3915881) B3915881
theorem B2610809 : Blo 1738570 2610809 := bstep (se 2 (by rfl) ⟨979053, by rfl⟩ : syracuseStep 2610809 = 1958107) B1958107
theorem B25425593 : Blo 1738570 25425593 := bstep (se 2 (by rfl) ⟨9534597, by rfl⟩ : syracuseStep 25425593 = 19069195) B19069195
theorem B3913703 : Blo 1738570 3913703 := bstep (se 1 (by rfl) ⟨2935277, by rfl⟩ : syracuseStep 3913703 = 5870555) B5870555
theorem B3913721 : Blo 1738570 3913721 := bstep (se 2 (by rfl) ⟨1467645, by rfl⟩ : syracuseStep 3913721 = 2935291) B2935291
theorem B3913811 : Blo 1738570 3913811 := bstep (se 1 (by rfl) ⟨2935358, by rfl⟩ : syracuseStep 3913811 = 5870717) B5870717
theorem B3913883 : Blo 1738570 3913883 := bstep (se 1 (by rfl) ⟨2935412, by rfl⟩ : syracuseStep 3913883 = 5870825) B5870825
theorem B3913991 : Blo 1738570 3913991 := bstep (se 1 (by rfl) ⟨2935493, by rfl⟩ : syracuseStep 3913991 = 5870987) B5870987
theorem B4954375 : Blo 1738570 4954375 := bstep (se 1 (by rfl) ⟨3715781, by rfl⟩ : syracuseStep 4954375 = 7431563) B7431563
theorem B1956379 : Blo 1738570 1956379 := bstep (se 1 (by rfl) ⟨1467284, by rfl⟩ : syracuseStep 1956379 = 2934569) B2934569
theorem B1858079 : Blo 1738570 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B3914297 : Blo 1738570 3914297 := bstep (se 2 (by rfl) ⟨1467861, by rfl⟩ : syracuseStep 3914297 = 2935723) B2935723
theorem B9910937 : Blo 1738570 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B42326833 : Blo 1738570 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B9911119 : Blo 1738570 9911119 := bstep (se 1 (by rfl) ⟨7433339, by rfl⟩ : syracuseStep 9911119 = 14866679) B14866679
theorem B12704617 : Blo 1738570 12704617 := bstep (se 2 (by rfl) ⟨4764231, by rfl⟩ : syracuseStep 12704617 = 9528463) B9528463
theorem B2825119 : Blo 1738570 2825119 := bstep (se 1 (by rfl) ⟨2118839, by rfl⟩ : syracuseStep 2825119 = 4237679) B4237679
theorem B5872769 : Blo 1738570 5872769 := bstep (se 2 (by rfl) ⟨2202288, by rfl⟩ : syracuseStep 5872769 = 4404577) B4404577
theorem B5872823 : Blo 1738570 5872823 := bstep (se 1 (by rfl) ⟨4404617, by rfl⟩ : syracuseStep 5872823 = 8809235) B8809235
theorem B19815677 : Blo 1738570 19815677 := bstep (se 3 (by rfl) ⟨3715439, by rfl⟩ : syracuseStep 19815677 = 7430879) B7430879
theorem B3915017 : Blo 1738570 3915017 := bstep (se 2 (by rfl) ⟨1468131, by rfl⟩ : syracuseStep 3915017 = 2936263) B2936263
theorem B26787287 : Blo 1738570 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B67788251 : Blo 1738570 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B1957351 : Blo 1738570 1957351 := bstep (se 1 (by rfl) ⟨1468013, by rfl⟩ : syracuseStep 1957351 = 2936027) B2936027
theorem B17858029 : Blo 1738570 17858029 := bstep (se 3 (by rfl) ⟨3348380, by rfl⟩ : syracuseStep 17858029 = 6696761) B6696761
theorem B4177487 : Blo 1738570 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B8355419 : Blo 1738570 8355419 := bstep (se 1 (by rfl) ⟨6266564, by rfl⟩ : syracuseStep 8355419 = 12533129) B12533129
theorem B19824425 : Blo 1738570 19824425 := bstep (se 2 (by rfl) ⟨7434159, by rfl⟩ : syracuseStep 19824425 = 14868319) B14868319
theorem B5873579 : Blo 1738570 5873579 := bstep (se 1 (by rfl) ⟨4405184, by rfl⟩ : syracuseStep 5873579 = 8810369) B8810369
theorem B1957855 : Blo 1738570 1957855 := bstep (se 1 (by rfl) ⟨1468391, by rfl⟩ : syracuseStep 1957855 = 2936783) B2936783
theorem B50184269 : Blo 1738570 50184269 := bstep (se 3 (by rfl) ⟨9409550, by rfl⟩ : syracuseStep 50184269 = 18819101) B18819101
theorem B3916025 : Blo 1738570 3916025 := bstep (se 2 (by rfl) ⟨1468509, by rfl⟩ : syracuseStep 3916025 = 2937019) B2937019
theorem B23814425 : Blo 1738570 23814425 := bstep (se 2 (by rfl) ⟨8930409, by rfl⟩ : syracuseStep 23814425 = 17860819) B17860819
theorem B3916079 : Blo 1738570 3916079 := bstep (se 1 (by rfl) ⟨2937059, by rfl⟩ : syracuseStep 3916079 = 5874119) B5874119
theorem B9912851 : Blo 1738570 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B81420823 : Blo 1738570 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B6693623 : Blo 1738570 6693623 := bstep (se 1 (by rfl) ⟨5020217, by rfl⟩ : syracuseStep 6693623 = 10040435) B10040435
theorem B56435777 : Blo 1738570 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B13214825 : Blo 1738570 13214825 := bstep (se 2 (by rfl) ⟨4955559, by rfl⟩ : syracuseStep 13214825 = 9911119) B9911119
theorem B16950395 : Blo 1738570 16950395 := bstep (se 1 (by rfl) ⟨12712796, by rfl⟩ : syracuseStep 16950395 = 25425593) B25425593
theorem B2933995 : Blo 1738570 2933995 := bstep (se 1 (by rfl) ⟨2200496, by rfl⟩ : syracuseStep 2933995 = 4400993) B4400993
theorem B33424811 : Blo 1738570 33424811 := bstep (se 1 (by rfl) ⟨25068608, by rfl⟩ : syracuseStep 33424811 = 50137217) B50137217
theorem B7931611 : Blo 1738570 7931611 := bstep (se 1 (by rfl) ⟨5948708, by rfl⟩ : syracuseStep 7931611 = 11897417) B11897417
theorem B4179833 : Blo 1738570 4179833 := bstep (se 2 (by rfl) ⟨1567437, by rfl⟩ : syracuseStep 4179833 = 3134875) B3134875
theorem B1738687 : Blo 1738570 1738687 := bstep (se 1 (by rfl) ⟨1304015, by rfl⟩ : syracuseStep 1738687 = 2608031) B2608031
theorem B22284233 : Blo 1738570 22284233 := bstep (se 2 (by rfl) ⟨8356587, by rfl⟩ : syracuseStep 22284233 = 16713175) B16713175
theorem B1738719 : Blo 1738570 1738719 := bstep (se 1 (by rfl) ⟨1304039, by rfl⟩ : syracuseStep 1738719 = 2608079) B2608079
theorem B13207535 : Blo 1738570 13207535 := bstep (se 1 (by rfl) ⟨9905651, by rfl⟩ : syracuseStep 13207535 = 19811303) B19811303
theorem B11298809 : Blo 1738570 11298809 := bstep (se 2 (by rfl) ⟨4237053, by rfl⟩ : syracuseStep 11298809 = 8474107) B8474107
theorem B1738779 : Blo 1738570 1738779 := bstep (se 1 (by rfl) ⟨1304084, by rfl⟩ : syracuseStep 1738779 = 2608169) B2608169
theorem B1738783 : Blo 1738570 1738783 := bstep (se 1 (by rfl) ⟨1304087, by rfl⟩ : syracuseStep 1738783 = 2608175) B2608175
theorem B1738799 : Blo 1738570 1738799 := bstep (se 1 (by rfl) ⟨1304099, by rfl⟩ : syracuseStep 1738799 = 2608199) B2608199
theorem B1738975 : Blo 1738570 1738975 := bstep (se 1 (by rfl) ⟨1304231, by rfl⟩ : syracuseStep 1738975 = 2608463) B2608463
theorem B1739035 : Blo 1738570 1739035 := bstep (se 1 (by rfl) ⟨1304276, by rfl⟩ : syracuseStep 1739035 = 2608553) B2608553
theorem B16714025 : Blo 1738570 16714025 := bstep (se 2 (by rfl) ⟨6267759, by rfl⟩ : syracuseStep 16714025 = 12535519) B12535519
theorem B6605135 : Blo 1738570 6605135 := bstep (se 1 (by rfl) ⟨4953851, by rfl⟩ : syracuseStep 6605135 = 9907703) B9907703
theorem B1739135 : Blo 1738570 1739135 := bstep (se 1 (by rfl) ⟨1304351, by rfl⟩ : syracuseStep 1739135 = 2608703) B2608703
theorem B13216283 : Blo 1738570 13216283 := bstep (se 1 (by rfl) ⟨9912212, by rfl⟩ : syracuseStep 13216283 = 19824425) B19824425
theorem B1739311 : Blo 1738570 1739311 := bstep (se 1 (by rfl) ⟨1304483, by rfl⟩ : syracuseStep 1739311 = 2608967) B2608967
theorem B1739367 : Blo 1738570 1739367 := bstep (se 1 (by rfl) ⟨1304525, by rfl⟩ : syracuseStep 1739367 = 2609051) B2609051
theorem B2935399 : Blo 1738570 2935399 := bstep (se 1 (by rfl) ⟨2201549, by rfl⟩ : syracuseStep 2935399 = 4403099) B4403099
theorem B7432829 : Blo 1738570 7432829 := bstep (se 3 (by rfl) ⟨1393655, by rfl⟩ : syracuseStep 7432829 = 2787311) B2787311
theorem B7932599 : Blo 1738570 7932599 := bstep (se 1 (by rfl) ⟨5949449, by rfl⟩ : syracuseStep 7932599 = 11898899) B11898899
theorem B2607911 : Blo 1738570 2607911 := bstep (se 1 (by rfl) ⟨1955933, by rfl⟩ : syracuseStep 2607911 = 3911867) B3911867
theorem B3967903 : Blo 1738570 3967903 := bstep (se 1 (by rfl) ⟨2975927, by rfl⟩ : syracuseStep 3967903 = 5951855) B5951855
theorem B4402127 : Blo 1738570 4402127 := bstep (se 1 (by rfl) ⟨3301595, by rfl⟩ : syracuseStep 4402127 = 6603191) B6603191
theorem B1739743 : Blo 1738570 1739743 := bstep (se 1 (by rfl) ⟨1304807, by rfl⟩ : syracuseStep 1739743 = 2609615) B2609615
theorem B1739771 : Blo 1738570 1739771 := bstep (se 1 (by rfl) ⟨1304828, by rfl⟩ : syracuseStep 1739771 = 2609657) B2609657
theorem B6605819 : Blo 1738570 6605819 := bstep (se 1 (by rfl) ⟨4954364, by rfl⟩ : syracuseStep 6605819 = 9908729) B9908729
theorem B6605833 : Blo 1738570 6605833 := bstep (se 2 (by rfl) ⟨2477187, by rfl⟩ : syracuseStep 6605833 = 4954375) B4954375
theorem B14855197 : Blo 1738570 14855197 := bstep (se 3 (by rfl) ⟨2785349, by rfl⟩ : syracuseStep 14855197 = 5570699) B5570699
theorem B1739839 : Blo 1738570 1739839 := bstep (se 1 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 1739839 = 2609759) B2609759
theorem B9907271 : Blo 1738570 9907271 := bstep (se 1 (by rfl) ⟨7430453, by rfl⟩ : syracuseStep 9907271 = 14860907) B14860907
theorem B2608235 : Blo 1738570 2608235 := bstep (se 1 (by rfl) ⟨1956176, by rfl⟩ : syracuseStep 2608235 = 3912353) B3912353
theorem B4402451 : Blo 1738570 4402451 := bstep (se 1 (by rfl) ⟨3301838, by rfl⟩ : syracuseStep 4402451 = 6603677) B6603677
theorem B2608475 : Blo 1738570 2608475 := bstep (se 1 (by rfl) ⟨1956356, by rfl⟩ : syracuseStep 2608475 = 3912713) B3912713
theorem B22908251 : Blo 1738570 22908251 := bstep (se 1 (by rfl) ⟨17181188, by rfl⟩ : syracuseStep 22908251 = 34362377) B34362377
theorem B2936155 : Blo 1738570 2936155 := bstep (se 1 (by rfl) ⟨2202116, by rfl⟩ : syracuseStep 2936155 = 4404233) B4404233
theorem B2608505 : Blo 1738570 2608505 := bstep (se 2 (by rfl) ⟨978189, by rfl⟩ : syracuseStep 2608505 = 1956379) B1956379
theorem B2608511 : Blo 1738570 2608511 := bstep (se 1 (by rfl) ⟨1956383, by rfl⟩ : syracuseStep 2608511 = 3912767) B3912767
theorem B1740159 : Blo 1738570 1740159 := bstep (se 1 (by rfl) ⟨1305119, by rfl⟩ : syracuseStep 1740159 = 2610239) B2610239
theorem B1740187 : Blo 1738570 1740187 := bstep (se 1 (by rfl) ⟨1305140, by rfl⟩ : syracuseStep 1740187 = 2610281) B2610281
theorem B1740255 : Blo 1738570 1740255 := bstep (se 1 (by rfl) ⟨1305191, by rfl⟩ : syracuseStep 1740255 = 2610383) B2610383
theorem B4951631 : Blo 1738570 4951631 := bstep (se 1 (by rfl) ⟨3713723, by rfl⟩ : syracuseStep 4951631 = 7427447) B7427447
theorem B7433819 : Blo 1738570 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B3526247 : Blo 1738570 3526247 := bstep (se 1 (by rfl) ⟨2644685, by rfl⟩ : syracuseStep 3526247 = 5289371) B5289371
theorem B1740391 : Blo 1738570 1740391 := bstep (se 1 (by rfl) ⟨1305293, by rfl⟩ : syracuseStep 1740391 = 2610587) B2610587
theorem B1740539 : Blo 1738570 1740539 := bstep (se 1 (by rfl) ⟨1305404, by rfl⟩ : syracuseStep 1740539 = 2610809) B2610809
theorem B4829053 : Blo 1738570 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B11145089 : Blo 1738570 11145089 := bstep (se 2 (by rfl) ⟨4179408, by rfl⟩ : syracuseStep 11145089 = 8358817) B8358817
theorem B2609135 : Blo 1738570 2609135 := bstep (se 1 (by rfl) ⟨1956851, by rfl⟩ : syracuseStep 2609135 = 3913703) B3913703
theorem B2609147 : Blo 1738570 2609147 := bstep (se 1 (by rfl) ⟨1956860, by rfl⟩ : syracuseStep 2609147 = 3913721) B3913721
theorem B2609207 : Blo 1738570 2609207 := bstep (se 1 (by rfl) ⟨1956905, by rfl⟩ : syracuseStep 2609207 = 3913811) B3913811
theorem B2609255 : Blo 1738570 2609255 := bstep (se 1 (by rfl) ⟨1956941, by rfl⟩ : syracuseStep 2609255 = 3913883) B3913883
theorem B2609327 : Blo 1738570 2609327 := bstep (se 1 (by rfl) ⟨1956995, by rfl⟩ : syracuseStep 2609327 = 3913991) B3913991
theorem B3715303 : Blo 1738570 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B9908477 : Blo 1738570 9908477 := bstep (se 3 (by rfl) ⟨1857839, by rfl⟩ : syracuseStep 9908477 = 3715679) B3715679
theorem B7434503 : Blo 1738570 7434503 := bstep (se 1 (by rfl) ⟨5575877, by rfl⟩ : syracuseStep 7434503 = 11151755) B11151755
theorem B7434605 : Blo 1738570 7434605 := bstep (se 3 (by rfl) ⟨1393988, by rfl⟩ : syracuseStep 7434605 = 2787977) B2787977
theorem B2609531 : Blo 1738570 2609531 := bstep (se 1 (by rfl) ⟨1957148, by rfl⟩ : syracuseStep 2609531 = 3914297) B3914297
theorem B6607291 : Blo 1738570 6607291 := bstep (se 1 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 6607291 = 9910937) B9910937
theorem B14103143 : Blo 1738570 14103143 := bstep (se 1 (by rfl) ⟨10577357, by rfl⟩ : syracuseStep 14103143 = 21154715) B21154715
theorem B2609801 : Blo 1738570 2609801 := bstep (se 2 (by rfl) ⟨978675, by rfl⟩ : syracuseStep 2609801 = 1957351) B1957351
theorem B23810705 : Blo 1738570 23810705 := bstep (se 2 (by rfl) ⟨8929014, by rfl⟩ : syracuseStep 23810705 = 17858029) B17858029
theorem B3912443 : Blo 1738570 3912443 := bstep (se 1 (by rfl) ⟨2934332, by rfl⟩ : syracuseStep 3912443 = 5868665) B5868665
theorem B5870393 : Blo 1738570 5870393 := bstep (se 2 (by rfl) ⟨2201397, by rfl⟩ : syracuseStep 5870393 = 4402795) B4402795
theorem B13210451 : Blo 1738570 13210451 := bstep (se 1 (by rfl) ⟨9907838, by rfl⟩ : syracuseStep 13210451 = 19815677) B19815677
theorem B2610011 : Blo 1738570 2610011 := bstep (se 1 (by rfl) ⟨1957508, by rfl⟩ : syracuseStep 2610011 = 3915017) B3915017
theorem B3716047 : Blo 1738570 3716047 := bstep (se 1 (by rfl) ⟨2787035, by rfl⟩ : syracuseStep 3716047 = 5574071) B5574071
theorem B3912659 : Blo 1738570 3912659 := bstep (se 1 (by rfl) ⟨2934494, by rfl⟩ : syracuseStep 3912659 = 5868989) B5868989
theorem B45192167 : Blo 1738570 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B22279211 : Blo 1738570 22279211 := bstep (se 1 (by rfl) ⟨16709408, by rfl⟩ : syracuseStep 22279211 = 33418817) B33418817
theorem B13202675 : Blo 1738570 13202675 := bstep (se 1 (by rfl) ⟨9902006, by rfl⟩ : syracuseStep 13202675 = 19804013) B19804013
theorem B2610473 : Blo 1738570 2610473 := bstep (se 2 (by rfl) ⟨978927, by rfl⟩ : syracuseStep 2610473 = 1957855) B1957855
theorem B3913127 : Blo 1738570 3913127 := bstep (se 1 (by rfl) ⟨2934845, by rfl⟩ : syracuseStep 3913127 = 5869691) B5869691
theorem B2610671 : Blo 1738570 2610671 := bstep (se 1 (by rfl) ⟨1958003, by rfl⟩ : syracuseStep 2610671 = 3916007) B3916007
theorem B14865929 : Blo 1738570 14865929 := bstep (se 2 (by rfl) ⟨5574723, by rfl⟩ : syracuseStep 14865929 = 11149447) B11149447
theorem B3913235 : Blo 1738570 3913235 := bstep (se 1 (by rfl) ⟨2934926, by rfl⟩ : syracuseStep 3913235 = 5869853) B5869853
theorem B3913307 : Blo 1738570 3913307 := bstep (se 1 (by rfl) ⟨2934980, by rfl⟩ : syracuseStep 3913307 = 5869961) B5869961
theorem B9910187 : Blo 1738570 9910187 := bstep (se 1 (by rfl) ⟨7432640, by rfl⟩ : syracuseStep 9910187 = 14865281) B14865281
theorem B16955351 : Blo 1738570 16955351 := bstep (se 1 (by rfl) ⟨12716513, by rfl⟩ : syracuseStep 16955351 = 25433027) B25433027
theorem B1955911 : Blo 1738570 1955911 := bstep (se 1 (by rfl) ⟨1466933, by rfl⟩ : syracuseStep 1955911 = 2933867) B2933867
theorem B4405387 : Blo 1738570 4405387 := bstep (se 1 (by rfl) ⟨3304040, by rfl⟩ : syracuseStep 4405387 = 6608081) B6608081
theorem B3913919 : Blo 1738570 3913919 := bstep (se 1 (by rfl) ⟨2935439, by rfl⟩ : syracuseStep 3913919 = 5870879) B5870879
theorem B16939489 : Blo 1738570 16939489 := bstep (se 2 (by rfl) ⟨6352308, by rfl⟩ : syracuseStep 16939489 = 12704617) B12704617
theorem B3766825 : Blo 1738570 3766825 := bstep (se 2 (by rfl) ⟨1412559, by rfl⟩ : syracuseStep 3766825 = 2825119) B2825119
theorem B71432765 : Blo 1738570 71432765 := bstep (se 3 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 71432765 = 26787287) B26787287
theorem B11147959 : Blo 1738570 11147959 := bstep (se 1 (by rfl) ⟨8360969, by rfl⟩ : syracuseStep 11147959 = 16721939) B16721939
theorem B8362739 : Blo 1738570 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B4954877 : Blo 1738570 4954877 := bstep (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) B1858079
theorem B4955003 : Blo 1738570 4955003 := bstep (se 1 (by rfl) ⟨3716252, by rfl⟩ : syracuseStep 4955003 = 7432505) B7432505
theorem B2202491 : Blo 1738570 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B1956775 : Blo 1738570 1956775 := bstep (se 1 (by rfl) ⟨1467581, by rfl⟩ : syracuseStep 1956775 = 2935163) B2935163
theorem B1956955 : Blo 1738570 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B3915179 : Blo 1738570 3915179 := bstep (se 1 (by rfl) ⟨2936384, by rfl⟩ : syracuseStep 3915179 = 5872769) B5872769
theorem B3915215 : Blo 1738570 3915215 := bstep (se 1 (by rfl) ⟨2936411, by rfl⟩ : syracuseStep 3915215 = 5872823) B5872823
theorem B2784991 : Blo 1738570 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B5570279 : Blo 1738570 5570279 := bstep (se 1 (by rfl) ⟨4177709, by rfl⟩ : syracuseStep 5570279 = 8355419) B8355419
theorem B7429907 : Blo 1738570 7429907 := bstep (se 1 (by rfl) ⟨5572430, by rfl⟩ : syracuseStep 7429907 = 11144861) B11144861
theorem B3301231 : Blo 1738570 3301231 := bstep (se 1 (by rfl) ⟨2475923, by rfl⟩ : syracuseStep 3301231 = 4951847) B4951847
theorem B3915719 : Blo 1738570 3915719 := bstep (se 1 (by rfl) ⟨2936789, by rfl⟩ : syracuseStep 3915719 = 5873579) B5873579
theorem B33456179 : Blo 1738570 33456179 := bstep (se 1 (by rfl) ⟨25092134, by rfl⟩ : syracuseStep 33456179 = 50184269) B50184269
theorem B4956335 : Blo 1738570 4956335 := bstep (se 1 (by rfl) ⟨3717251, by rfl⟩ : syracuseStep 4956335 = 7434503) B7434503
theorem B5873849 : Blo 1738570 5873849 := bstep (se 2 (by rfl) ⟨2202693, by rfl⟩ : syracuseStep 5873849 = 4405387) B4405387
theorem B15876283 : Blo 1738570 15876283 := bstep (se 1 (by rfl) ⟨11907212, by rfl⟩ : syracuseStep 15876283 = 23814425) B23814425
theorem B4956403 : Blo 1738570 4956403 := bstep (se 1 (by rfl) ⟨3717302, by rfl⟩ : syracuseStep 4956403 = 7434605) B7434605
theorem B8806967 : Blo 1738570 8806967 := bstep (se 1 (by rfl) ⟨6605225, by rfl⟩ : syracuseStep 8806967 = 13210451) B13210451
theorem B22585985 : Blo 1738570 22585985 := bstep (se 2 (by rfl) ⟨8469744, by rfl⟩ : syracuseStep 22585985 = 16939489) B16939489
theorem B14852807 : Blo 1738570 14852807 := bstep (se 1 (by rfl) ⟨11139605, by rfl⟩ : syracuseStep 14852807 = 22279211) B22279211
theorem B108561097 : Blo 1738570 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B5022433 : Blo 1738570 5022433 := bstep (se 2 (by rfl) ⟨1883412, by rfl⟩ : syracuseStep 5022433 = 3766825) B3766825
theorem B22283207 : Blo 1738570 22283207 := bstep (se 1 (by rfl) ⟨16712405, by rfl⟩ : syracuseStep 22283207 = 33424811) B33424811
theorem B2786555 : Blo 1738570 2786555 := bstep (se 1 (by rfl) ⟨2089916, by rfl⟩ : syracuseStep 2786555 = 4179833) B4179833
theorem B8807777 : Blo 1738570 8807777 := bstep (se 2 (by rfl) ⟨3302916, by rfl⟩ : syracuseStep 8807777 = 6605833) B6605833
theorem B11142683 : Blo 1738570 11142683 := bstep (se 1 (by rfl) ⟨8357012, by rfl⟩ : syracuseStep 11142683 = 16714025) B16714025
theorem B47621843 : Blo 1738570 47621843 := bstep (se 1 (by rfl) ⟨35716382, by rfl⟩ : syracuseStep 47621843 = 71432765) B71432765
theorem B3303251 : Blo 1738570 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B1738607 : Blo 1738570 1738607 := bstep (se 1 (by rfl) ⟨1303955, by rfl⟩ : syracuseStep 1738607 = 2607911) B2607911
theorem B3303335 : Blo 1738570 3303335 := bstep (se 1 (by rfl) ⟨2477501, by rfl⟩ : syracuseStep 3303335 = 4955003) B4955003
theorem B2934751 : Blo 1738570 2934751 := bstep (se 1 (by rfl) ⟨2201063, by rfl⟩ : syracuseStep 2934751 = 4402127) B4402127
theorem B6604847 : Blo 1738570 6604847 := bstep (se 1 (by rfl) ⟨4953635, by rfl⟩ : syracuseStep 6604847 = 9907271) B9907271
theorem B1738823 : Blo 1738570 1738823 := bstep (se 1 (by rfl) ⟨1304117, by rfl⟩ : syracuseStep 1738823 = 2608235) B2608235
theorem B2934967 : Blo 1738570 2934967 := bstep (se 1 (by rfl) ⟨2201225, by rfl⟩ : syracuseStep 2934967 = 4402451) B4402451
theorem B1738983 : Blo 1738570 1738983 := bstep (se 1 (by rfl) ⟨1304237, by rfl⟩ : syracuseStep 1738983 = 2608475) B2608475
theorem B15272167 : Blo 1738570 15272167 := bstep (se 1 (by rfl) ⟨11454125, by rfl⟩ : syracuseStep 15272167 = 22908251) B22908251
theorem B1739003 : Blo 1738570 1739003 := bstep (se 1 (by rfl) ⟨1304252, by rfl⟩ : syracuseStep 1739003 = 2608505) B2608505
theorem B1739007 : Blo 1738570 1739007 := bstep (se 1 (by rfl) ⟨1304255, by rfl⟩ : syracuseStep 1739007 = 2608511) B2608511
theorem B3713321 : Blo 1738570 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B4401641 : Blo 1738570 4401641 := bstep (se 2 (by rfl) ⟨1650615, by rfl⟩ : syracuseStep 4401641 = 3301231) B3301231
theorem B3713519 : Blo 1738570 3713519 := bstep (se 1 (by rfl) ⟨2785139, by rfl⟩ : syracuseStep 3713519 = 5570279) B5570279
theorem B1739423 : Blo 1738570 1739423 := bstep (se 1 (by rfl) ⟨1304567, by rfl⟩ : syracuseStep 1739423 = 2609135) B2609135
theorem B1739431 : Blo 1738570 1739431 := bstep (se 1 (by rfl) ⟨1304573, by rfl⟩ : syracuseStep 1739431 = 2609147) B2609147
theorem B1739471 : Blo 1738570 1739471 := bstep (se 1 (by rfl) ⟨1304603, by rfl⟩ : syracuseStep 1739471 = 2609207) B2609207
theorem B1739503 : Blo 1738570 1739503 := bstep (se 1 (by rfl) ⟨1304627, by rfl⟩ : syracuseStep 1739503 = 2609255) B2609255
theorem B2607881 : Blo 1738570 2607881 := bstep (se 2 (by rfl) ⟨977955, by rfl⟩ : syracuseStep 2607881 = 1955911) B1955911
theorem B1739551 : Blo 1738570 1739551 := bstep (se 1 (by rfl) ⟨1304663, by rfl⟩ : syracuseStep 1739551 = 2609327) B2609327
theorem B6605651 : Blo 1738570 6605651 := bstep (se 1 (by rfl) ⟨4954238, by rfl⟩ : syracuseStep 6605651 = 9908477) B9908477
theorem B1739687 : Blo 1738570 1739687 := bstep (se 1 (by rfl) ⟨1304765, by rfl⟩ : syracuseStep 1739687 = 2609531) B2609531
theorem B1739867 : Blo 1738570 1739867 := bstep (se 1 (by rfl) ⟨1304900, by rfl⟩ : syracuseStep 1739867 = 2609801) B2609801
theorem B2608295 : Blo 1738570 2608295 := bstep (se 1 (by rfl) ⟨1956221, by rfl⟩ : syracuseStep 2608295 = 3912443) B3912443
theorem B1740007 : Blo 1738570 1740007 := bstep (se 1 (by rfl) ⟨1305005, by rfl⟩ : syracuseStep 1740007 = 2610011) B2610011
theorem B8809721 : Blo 1738570 8809721 := bstep (se 2 (by rfl) ⟨3303645, by rfl⟩ : syracuseStep 8809721 = 6607291) B6607291
theorem B2608439 : Blo 1738570 2608439 := bstep (se 1 (by rfl) ⟨1956329, by rfl⟩ : syracuseStep 2608439 = 3912659) B3912659
theorem B8809883 : Blo 1738570 8809883 := bstep (se 1 (by rfl) ⟨6607412, by rfl⟩ : syracuseStep 8809883 = 13214825) B13214825
theorem B8801783 : Blo 1738570 8801783 := bstep (se 1 (by rfl) ⟨6601337, by rfl⟩ : syracuseStep 8801783 = 13202675) B13202675
theorem B1740315 : Blo 1738570 1740315 := bstep (se 1 (by rfl) ⟨1305236, by rfl⟩ : syracuseStep 1740315 = 2610473) B2610473
theorem B14863945 : Blo 1738570 14863945 := bstep (se 2 (by rfl) ⟨5573979, by rfl⟩ : syracuseStep 14863945 = 11147959) B11147959
theorem B2608751 : Blo 1738570 2608751 := bstep (se 1 (by rfl) ⟨1956563, by rfl⟩ : syracuseStep 2608751 = 3913127) B3913127
theorem B1740447 : Blo 1738570 1740447 := bstep (se 1 (by rfl) ⟨1305335, by rfl⟩ : syracuseStep 1740447 = 2610671) B2610671
theorem B2608823 : Blo 1738570 2608823 := bstep (se 1 (by rfl) ⟨1956617, by rfl⟩ : syracuseStep 2608823 = 3913235) B3913235
theorem B2608871 : Blo 1738570 2608871 := bstep (se 1 (by rfl) ⟨1956653, by rfl⟩ : syracuseStep 2608871 = 3913307) B3913307
theorem B2609033 : Blo 1738570 2609033 := bstep (se 2 (by rfl) ⟨978387, by rfl⟩ : syracuseStep 2609033 = 1956775) B1956775
theorem B6606791 : Blo 1738570 6606791 := bstep (se 1 (by rfl) ⟨4955093, by rfl⟩ : syracuseStep 6606791 = 9910187) B9910187
theorem B14856155 : Blo 1738570 14856155 := bstep (se 1 (by rfl) ⟨11142116, by rfl⟩ : syracuseStep 14856155 = 22284233) B22284233
theorem B2609273 : Blo 1738570 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B2609279 : Blo 1738570 2609279 := bstep (se 1 (by rfl) ⟨1956959, by rfl⟩ : syracuseStep 2609279 = 3913919) B3913919
theorem B4403423 : Blo 1738570 4403423 := bstep (se 1 (by rfl) ⟨3302567, by rfl⟩ : syracuseStep 4403423 = 6605135) B6605135
theorem B3911993 : Blo 1738570 3911993 := bstep (se 2 (by rfl) ⟨1466997, by rfl⟩ : syracuseStep 3911993 = 2933995) B2933995
theorem B8810855 : Blo 1738570 8810855 := bstep (se 1 (by rfl) ⟨6608141, by rfl⟩ : syracuseStep 8810855 = 13216283) B13216283
theorem B5288399 : Blo 1738570 5288399 := bstep (se 1 (by rfl) ⟨3966299, by rfl⟩ : syracuseStep 5288399 = 7932599) B7932599
theorem B5575159 : Blo 1738570 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B4403879 : Blo 1738570 4403879 := bstep (se 1 (by rfl) ⟨3302909, by rfl⟩ : syracuseStep 4403879 = 6605819) B6605819
theorem B2610119 : Blo 1738570 2610119 := bstep (se 1 (by rfl) ⟨1957589, by rfl⟩ : syracuseStep 2610119 = 3915179) B3915179
theorem B2610143 : Blo 1738570 2610143 := bstep (se 1 (by rfl) ⟨1957607, by rfl⟩ : syracuseStep 2610143 = 3915215) B3915215
theorem B4953271 : Blo 1738570 4953271 := bstep (se 1 (by rfl) ⟨3714953, by rfl⟩ : syracuseStep 4953271 = 7429907) B7429907
theorem B2610479 : Blo 1738570 2610479 := bstep (se 1 (by rfl) ⟨1957859, by rfl⟩ : syracuseStep 2610479 = 3915719) B3915719
theorem B2610683 : Blo 1738570 2610683 := bstep (se 1 (by rfl) ⟨1958012, by rfl⟩ : syracuseStep 2610683 = 3916025) B3916025
theorem B2610719 : Blo 1738570 2610719 := bstep (se 1 (by rfl) ⟨1958039, by rfl⟩ : syracuseStep 2610719 = 3916079) B3916079
theorem B4953737 : Blo 1738570 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B45201053 : Blo 1738570 45201053 := bstep (se 3 (by rfl) ⟨8475197, by rfl⟩ : syracuseStep 45201053 = 16950395) B16950395
theorem B6608567 : Blo 1738570 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B9402095 : Blo 1738570 9402095 := bstep (se 1 (by rfl) ⟨7051571, by rfl⟩ : syracuseStep 9402095 = 14103143) B14103143
theorem B15873803 : Blo 1738570 15873803 := bstep (se 1 (by rfl) ⟨11905352, by rfl⟩ : syracuseStep 15873803 = 23810705) B23810705
theorem B4462415 : Blo 1738570 4462415 := bstep (se 1 (by rfl) ⟨3346811, by rfl⟩ : syracuseStep 4462415 = 6693623) B6693623
theorem B3913595 : Blo 1738570 3913595 := bstep (se 1 (by rfl) ⟨2935196, by rfl⟩ : syracuseStep 3913595 = 5870393) B5870393
theorem B30128111 : Blo 1738570 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B37623851 : Blo 1738570 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B3913865 : Blo 1738570 3913865 := bstep (se 2 (by rfl) ⟨1467699, by rfl⟩ : syracuseStep 3913865 = 2935399) B2935399
theorem B9910619 : Blo 1738570 9910619 := bstep (se 1 (by rfl) ⟨7432964, by rfl⟩ : syracuseStep 9910619 = 14865929) B14865929
theorem B42301925 : Blo 1738570 42301925 := bstep (se 4 (by rfl) ⟨3965805, by rfl⟩ : syracuseStep 42301925 = 7931611) B7931611
theorem B5290537 : Blo 1738570 5290537 := bstep (se 2 (by rfl) ⟨1983951, by rfl⟩ : syracuseStep 5290537 = 3967903) B3967903
theorem B4954729 : Blo 1738570 4954729 := bstep (se 2 (by rfl) ⟨1858023, by rfl⟩ : syracuseStep 4954729 = 3716047) B3716047
theorem B11303567 : Blo 1738570 11303567 := bstep (se 1 (by rfl) ⟨8477675, by rfl⟩ : syracuseStep 11303567 = 16955351) B16955351
theorem B8805023 : Blo 1738570 8805023 := bstep (se 1 (by rfl) ⟨6603767, by rfl⟩ : syracuseStep 8805023 = 13207535) B13207535
theorem B19806929 : Blo 1738570 19806929 := bstep (se 2 (by rfl) ⟨7427598, by rfl⟩ : syracuseStep 19806929 = 14855197) B14855197
theorem B4955219 : Blo 1738570 4955219 := bstep (se 1 (by rfl) ⟨3716414, by rfl⟩ : syracuseStep 4955219 = 7432829) B7432829
theorem B3914873 : Blo 1738570 3914873 := bstep (se 2 (by rfl) ⟨1468077, by rfl⟩ : syracuseStep 3914873 = 2936155) B2936155
theorem B5873309 : Blo 1738570 5873309 := bstep (se 3 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 5873309 = 2202491) B2202491
theorem B3301087 : Blo 1738570 3301087 := bstep (se 1 (by rfl) ⟨2475815, by rfl⟩ : syracuseStep 3301087 = 4951631) B4951631
theorem B4955879 : Blo 1738570 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B2350831 : Blo 1738570 2350831 := bstep (se 1 (by rfl) ⟨1763123, by rfl⟩ : syracuseStep 2350831 = 3526247) B3526247
theorem B6438737 : Blo 1738570 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B7430059 : Blo 1738570 7430059 := bstep (se 1 (by rfl) ⟨5572544, by rfl⟩ : syracuseStep 7430059 = 11145089) B11145089
theorem B30130157 : Blo 1738570 30130157 := bstep (se 3 (by rfl) ⟨5649404, by rfl⟩ : syracuseStep 30130157 = 11298809) B11298809
theorem B3915899 : Blo 1738570 3915899 := bstep (se 1 (by rfl) ⟨2936924, by rfl⟩ : syracuseStep 3915899 = 5873849) B5873849
theorem B5873903 : Blo 1738570 5873903 := bstep (se 1 (by rfl) ⟨4405427, by rfl⟩ : syracuseStep 5873903 = 8810855) B8810855
theorem B21168377 : Blo 1738570 21168377 := bstep (se 2 (by rfl) ⟨7938141, by rfl⟩ : syracuseStep 21168377 = 15876283) B15876283
theorem B15057323 : Blo 1738570 15057323 := bstep (se 1 (by rfl) ⟨11292992, by rfl⟩ : syracuseStep 15057323 = 22585985) B22585985
theorem B7054049 : Blo 1738570 7054049 := bstep (se 2 (by rfl) ⟨2645268, by rfl⟩ : syracuseStep 7054049 = 5290537) B5290537
theorem B6268063 : Blo 1738570 6268063 := bstep (se 1 (by rfl) ⟨4701047, by rfl⟩ : syracuseStep 6268063 = 9402095) B9402095
theorem B2974943 : Blo 1738570 2974943 := bstep (se 1 (by rfl) ⟨2231207, by rfl⟩ : syracuseStep 2974943 = 4462415) B4462415
theorem B6604361 : Blo 1738570 6604361 := bstep (se 2 (by rfl) ⟨2476635, by rfl⟩ : syracuseStep 6604361 = 4953271) B4953271
theorem B2934427 : Blo 1738570 2934427 := bstep (se 1 (by rfl) ⟨2200820, by rfl⟩ : syracuseStep 2934427 = 4401641) B4401641
theorem B2475679 : Blo 1738570 2475679 := bstep (se 1 (by rfl) ⟨1856759, by rfl⟩ : syracuseStep 2475679 = 3713519) B3713519
theorem B1738587 : Blo 1738570 1738587 := bstep (se 1 (by rfl) ⟨1303940, by rfl⟩ : syracuseStep 1738587 = 2607881) B2607881
theorem B3303479 : Blo 1738570 3303479 := bstep (se 1 (by rfl) ⟨2477609, by rfl⟩ : syracuseStep 3303479 = 4955219) B4955219
theorem B19818593 : Blo 1738570 19818593 := bstep (se 2 (by rfl) ⟨7431972, by rfl⟩ : syracuseStep 19818593 = 14863945) B14863945
theorem B1738863 : Blo 1738570 1738863 := bstep (se 1 (by rfl) ⟨1304147, by rfl⟩ : syracuseStep 1738863 = 2608295) B2608295
theorem B1738959 : Blo 1738570 1738959 := bstep (se 1 (by rfl) ⟨1304219, by rfl⟩ : syracuseStep 1738959 = 2608439) B2608439
theorem B4401449 : Blo 1738570 4401449 := bstep (se 2 (by rfl) ⟨1650543, by rfl⟩ : syracuseStep 4401449 = 3301087) B3301087
theorem B5867855 : Blo 1738570 5867855 := bstep (se 1 (by rfl) ⟨4400891, by rfl⟩ : syracuseStep 5867855 = 8801783) B8801783
theorem B1739167 : Blo 1738570 1739167 := bstep (se 1 (by rfl) ⟨1304375, by rfl⟩ : syracuseStep 1739167 = 2608751) B2608751
theorem B1739215 : Blo 1738570 1739215 := bstep (se 1 (by rfl) ⟨1304411, by rfl⟩ : syracuseStep 1739215 = 2608823) B2608823
theorem B1739247 : Blo 1738570 1739247 := bstep (se 1 (by rfl) ⟨1304435, by rfl⟩ : syracuseStep 1739247 = 2608871) B2608871
theorem B3303919 : Blo 1738570 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B9906745 : Blo 1738570 9906745 := bstep (se 2 (by rfl) ⟨3715029, by rfl⟩ : syracuseStep 9906745 = 7430059) B7430059
theorem B1739355 : Blo 1738570 1739355 := bstep (se 1 (by rfl) ⟨1304516, by rfl⟩ : syracuseStep 1739355 = 2609033) B2609033
theorem B1739515 : Blo 1738570 1739515 := bstep (se 1 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 1739515 = 2609273) B2609273
theorem B1739519 : Blo 1738570 1739519 := bstep (se 1 (by rfl) ⟨1304639, by rfl⟩ : syracuseStep 1739519 = 2609279) B2609279
theorem B3304223 : Blo 1738570 3304223 := bstep (se 1 (by rfl) ⟨2478167, by rfl⟩ : syracuseStep 3304223 = 4956335) B4956335
theorem B2935615 : Blo 1738570 2935615 := bstep (se 1 (by rfl) ⟨2201711, by rfl⟩ : syracuseStep 2935615 = 4403423) B4403423
theorem B2607995 : Blo 1738570 2607995 := bstep (se 1 (by rfl) ⟨1955996, by rfl⟩ : syracuseStep 2607995 = 3911993) B3911993
theorem B3525599 : Blo 1738570 3525599 := bstep (se 1 (by rfl) ⟨2644199, by rfl⟩ : syracuseStep 3525599 = 5288399) B5288399
theorem B2935919 : Blo 1738570 2935919 := bstep (se 1 (by rfl) ⟨2201939, by rfl⟩ : syracuseStep 2935919 = 4403879) B4403879
theorem B14855471 : Blo 1738570 14855471 := bstep (se 1 (by rfl) ⟨11141603, by rfl⟩ : syracuseStep 14855471 = 22283207) B22283207
theorem B1740079 : Blo 1738570 1740079 := bstep (se 1 (by rfl) ⟨1305059, by rfl⟩ : syracuseStep 1740079 = 2610119) B2610119
theorem B1740095 : Blo 1738570 1740095 := bstep (se 1 (by rfl) ⟨1305071, by rfl⟩ : syracuseStep 1740095 = 2610143) B2610143
theorem B7433545 : Blo 1738570 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B6606305 : Blo 1738570 6606305 := bstep (se 2 (by rfl) ⟨2477364, by rfl⟩ : syracuseStep 6606305 = 4954729) B4954729
theorem B1740319 : Blo 1738570 1740319 := bstep (se 1 (by rfl) ⟨1305239, by rfl⟩ : syracuseStep 1740319 = 2610479) B2610479
theorem B144748129 : Blo 1738570 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B6696577 : Blo 1738570 6696577 := bstep (se 2 (by rfl) ⟨2511216, by rfl⟩ : syracuseStep 6696577 = 5022433) B5022433
theorem B1740455 : Blo 1738570 1740455 := bstep (se 1 (by rfl) ⟨1305341, by rfl⟩ : syracuseStep 1740455 = 2610683) B2610683
theorem B1740479 : Blo 1738570 1740479 := bstep (se 1 (by rfl) ⟨1305359, by rfl⟩ : syracuseStep 1740479 = 2610719) B2610719
theorem B30134035 : Blo 1738570 30134035 := bstep (se 1 (by rfl) ⟨22600526, by rfl⟩ : syracuseStep 30134035 = 45201053) B45201053
theorem B31747895 : Blo 1738570 31747895 := bstep (se 1 (by rfl) ⟨23810921, by rfl⟩ : syracuseStep 31747895 = 47621843) B47621843
theorem B2609063 : Blo 1738570 2609063 := bstep (se 1 (by rfl) ⟨1956797, by rfl⟩ : syracuseStep 2609063 = 3913595) B3913595
theorem B4403231 : Blo 1738570 4403231 := bstep (se 1 (by rfl) ⟨3302423, by rfl⟩ : syracuseStep 4403231 = 6604847) B6604847
theorem B2609243 : Blo 1738570 2609243 := bstep (se 1 (by rfl) ⟨1956932, by rfl⟩ : syracuseStep 2609243 = 3913865) B3913865
theorem B6607079 : Blo 1738570 6607079 := bstep (se 1 (by rfl) ⟨4955309, by rfl⟩ : syracuseStep 6607079 = 9910619) B9910619
theorem B28201283 : Blo 1738570 28201283 := bstep (se 1 (by rfl) ⟨21150962, by rfl⟩ : syracuseStep 28201283 = 42301925) B42301925
theorem B13209965 : Blo 1738570 13209965 := bstep (se 3 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 13209965 = 4953737) B4953737
theorem B5870015 : Blo 1738570 5870015 := bstep (se 1 (by rfl) ⟨4402511, by rfl⟩ : syracuseStep 5870015 = 8805023) B8805023
theorem B4403767 : Blo 1738570 4403767 := bstep (se 1 (by rfl) ⟨3302825, by rfl⟩ : syracuseStep 4403767 = 6605651) B6605651
theorem B2609915 : Blo 1738570 2609915 := bstep (se 1 (by rfl) ⟨1957436, by rfl⟩ : syracuseStep 2609915 = 3914873) B3914873
theorem B3134441 : Blo 1738570 3134441 := bstep (se 2 (by rfl) ⟨1175415, by rfl⟩ : syracuseStep 3134441 = 2350831) B2350831
theorem B3913001 : Blo 1738570 3913001 := bstep (se 2 (by rfl) ⟨1467375, by rfl⟩ : syracuseStep 3913001 = 2934751) B2934751
theorem B4404527 : Blo 1738570 4404527 := bstep (se 1 (by rfl) ⟨3303395, by rfl⟩ : syracuseStep 4404527 = 6606791) B6606791
theorem B22304119 : Blo 1738570 22304119 := bstep (se 1 (by rfl) ⟨16728089, by rfl⟩ : syracuseStep 22304119 = 33456179) B33456179
theorem B3913289 : Blo 1738570 3913289 := bstep (se 2 (by rfl) ⟨1467483, by rfl⟩ : syracuseStep 3913289 = 2934967) B2934967
theorem B20362889 : Blo 1738570 20362889 := bstep (se 2 (by rfl) ⟨7636083, by rfl⟩ : syracuseStep 20362889 = 15272167) B15272167
theorem B6608537 : Blo 1738570 6608537 := bstep (se 2 (by rfl) ⟨2478201, by rfl⟩ : syracuseStep 6608537 = 4956403) B4956403
theorem B5871311 : Blo 1738570 5871311 := bstep (se 1 (by rfl) ⟨4403483, by rfl⟩ : syracuseStep 5871311 = 8806967) B8806967
theorem B9901871 : Blo 1738570 9901871 := bstep (se 1 (by rfl) ⟨7426403, by rfl⟩ : syracuseStep 9901871 = 14852807) B14852807
theorem B9902189 : Blo 1738570 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B1857703 : Blo 1738570 1857703 := bstep (se 1 (by rfl) ⟨1393277, by rfl⟩ : syracuseStep 1857703 = 2786555) B2786555
theorem B5871851 : Blo 1738570 5871851 := bstep (se 1 (by rfl) ⟨4403888, by rfl⟩ : syracuseStep 5871851 = 8807777) B8807777
theorem B7428455 : Blo 1738570 7428455 := bstep (se 1 (by rfl) ⟨5571341, by rfl⟩ : syracuseStep 7428455 = 11142683) B11142683
theorem B4405711 : Blo 1738570 4405711 := bstep (se 1 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 4405711 = 6608567) B6608567
theorem B10582535 : Blo 1738570 10582535 := bstep (se 1 (by rfl) ⟨7936901, by rfl⟩ : syracuseStep 10582535 = 15873803) B15873803
theorem B2202167 : Blo 1738570 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B2202223 : Blo 1738570 2202223 := bstep (se 1 (by rfl) ⟨1651667, by rfl⟩ : syracuseStep 2202223 = 3303335) B3303335
theorem B20085407 : Blo 1738570 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B25082567 : Blo 1738570 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B7535711 : Blo 1738570 7535711 := bstep (se 1 (by rfl) ⟨5651783, by rfl⟩ : syracuseStep 7535711 = 11303567) B11303567
theorem B13204619 : Blo 1738570 13204619 := bstep (se 1 (by rfl) ⟨9903464, by rfl⟩ : syracuseStep 13204619 = 19806929) B19806929
theorem B5873147 : Blo 1738570 5873147 := bstep (se 1 (by rfl) ⟨4404860, by rfl⟩ : syracuseStep 5873147 = 8809721) B8809721
theorem B17169965 : Blo 1738570 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B5873255 : Blo 1738570 5873255 := bstep (se 1 (by rfl) ⟨4404941, by rfl⟩ : syracuseStep 5873255 = 8809883) B8809883
theorem B3915539 : Blo 1738570 3915539 := bstep (se 1 (by rfl) ⟨2936654, by rfl⟩ : syracuseStep 3915539 = 5873309) B5873309
theorem B80347085 : Blo 1738570 80347085 := bstep (se 3 (by rfl) ⟨15065078, by rfl⟩ : syracuseStep 80347085 = 30130157) B30130157
theorem B9904103 : Blo 1738570 9904103 := bstep (se 1 (by rfl) ⟨7428077, by rfl⟩ : syracuseStep 9904103 = 14856155) B14856155
theorem B3915935 : Blo 1738570 3915935 := bstep (se 1 (by rfl) ⟨2936951, by rfl⟩ : syracuseStep 3915935 = 5873903) B5873903
theorem B18800855 : Blo 1738570 18800855 := bstep (se 1 (by rfl) ⟨14100641, by rfl⟩ : syracuseStep 18800855 = 28201283) B28201283
theorem B8806643 : Blo 1738570 8806643 := bstep (se 1 (by rfl) ⟨6604982, by rfl⟩ : syracuseStep 8806643 = 13209965) B13209965
theorem B20095229 : Blo 1738570 20095229 := bstep (se 3 (by rfl) ⟨3767855, by rfl⟩ : syracuseStep 20095229 = 7535711) B7535711
theorem B5874281 : Blo 1738570 5874281 := bstep (se 2 (by rfl) ⟨2202855, by rfl⟩ : syracuseStep 5874281 = 4405711) B4405711
theorem B1983295 : Blo 1738570 1983295 := bstep (se 1 (by rfl) ⟨1487471, by rfl⟩ : syracuseStep 1983295 = 2974943) B2974943
theorem B13575259 : Blo 1738570 13575259 := bstep (se 1 (by rfl) ⟨10181444, by rfl⟩ : syracuseStep 13575259 = 20362889) B20362889
theorem B2934299 : Blo 1738570 2934299 := bstep (se 1 (by rfl) ⟨2200724, by rfl⟩ : syracuseStep 2934299 = 4401449) B4401449
theorem B8357417 : Blo 1738570 8357417 := bstep (se 2 (by rfl) ⟨3134031, by rfl⟩ : syracuseStep 8357417 = 6268063) B6268063
theorem B7055023 : Blo 1738570 7055023 := bstep (se 1 (by rfl) ⟨5291267, by rfl⟩ : syracuseStep 7055023 = 10582535) B10582535
theorem B16721711 : Blo 1738570 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B29738825 : Blo 1738570 29738825 := bstep (se 2 (by rfl) ⟨11152059, by rfl⟩ : syracuseStep 29738825 = 22304119) B22304119
theorem B1738663 : Blo 1738570 1738663 := bstep (se 1 (by rfl) ⟨1303997, by rfl⟩ : syracuseStep 1738663 = 2607995) B2607995
theorem B18810797 : Blo 1738570 18810797 := bstep (se 3 (by rfl) ⟨3527024, by rfl⟩ : syracuseStep 18810797 = 7054049) B7054049
theorem B192997505 : Blo 1738570 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B11446643 : Blo 1738570 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B8358509 : Blo 1738570 8358509 := bstep (se 3 (by rfl) ⟨1567220, by rfl⟩ : syracuseStep 8358509 = 3134441) B3134441
theorem B1739375 : Blo 1738570 1739375 := bstep (se 1 (by rfl) ⟨1304531, by rfl⟩ : syracuseStep 1739375 = 2609063) B2609063
theorem B2935487 : Blo 1738570 2935487 := bstep (se 1 (by rfl) ⟨2201615, by rfl⟩ : syracuseStep 2935487 = 4403231) B4403231
theorem B1739495 : Blo 1738570 1739495 := bstep (se 1 (by rfl) ⟨1304621, by rfl⟩ : syracuseStep 1739495 = 2609243) B2609243
theorem B2476937 : Blo 1738570 2476937 := bstep (se 2 (by rfl) ⟨928851, by rfl⟩ : syracuseStep 2476937 = 1857703) B1857703
theorem B10038215 : Blo 1738570 10038215 := bstep (se 1 (by rfl) ⟨7528661, by rfl⟩ : syracuseStep 10038215 = 15057323) B15057323
theorem B1739943 : Blo 1738570 1739943 := bstep (se 1 (by rfl) ⟨1304957, by rfl⟩ : syracuseStep 1739943 = 2609915) B2609915
theorem B13208993 : Blo 1738570 13208993 := bstep (se 2 (by rfl) ⟨4953372, by rfl⟩ : syracuseStep 13208993 = 9906745) B9906745
theorem B2936297 : Blo 1738570 2936297 := bstep (se 2 (by rfl) ⟨1101111, by rfl⟩ : syracuseStep 2936297 = 2202223) B2202223
theorem B2608667 : Blo 1738570 2608667 := bstep (se 1 (by rfl) ⟨1956500, by rfl⟩ : syracuseStep 2608667 = 3913001) B3913001
theorem B2936351 : Blo 1738570 2936351 := bstep (se 1 (by rfl) ⟨2202263, by rfl⟩ : syracuseStep 2936351 = 4404527) B4404527
theorem B2608859 : Blo 1738570 2608859 := bstep (se 1 (by rfl) ⟨1956644, by rfl⟩ : syracuseStep 2608859 = 3913289) B3913289
theorem B4402907 : Blo 1738570 4402907 := bstep (se 1 (by rfl) ⟨3302180, by rfl⟩ : syracuseStep 4402907 = 6604361) B6604361
theorem B160714853 : Blo 1738570 160714853 := bstep (se 4 (by rfl) ⟨15067017, by rfl⟩ : syracuseStep 160714853 = 30134035) B30134035
theorem B3911903 : Blo 1738570 3911903 := bstep (se 1 (by rfl) ⟨2933927, by rfl⟩ : syracuseStep 3911903 = 5867855) B5867855
theorem B4952303 : Blo 1738570 4952303 := bstep (se 1 (by rfl) ⟨3714227, by rfl⟩ : syracuseStep 4952303 = 7428455) B7428455
theorem B13390271 : Blo 1738570 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B8803079 : Blo 1738570 8803079 := bstep (se 1 (by rfl) ⟨6602309, by rfl⟩ : syracuseStep 8803079 = 13204619) B13204619
theorem B3912569 : Blo 1738570 3912569 := bstep (se 2 (by rfl) ⟨1467213, by rfl⟩ : syracuseStep 3912569 = 2934427) B2934427
theorem B4404203 : Blo 1738570 4404203 := bstep (se 1 (by rfl) ⟨3303152, by rfl⟩ : syracuseStep 4404203 = 6606305) B6606305
theorem B2610359 : Blo 1738570 2610359 := bstep (se 1 (by rfl) ⟨1957769, by rfl⟩ : syracuseStep 2610359 = 3915539) B3915539
theorem B21165263 : Blo 1738570 21165263 := bstep (se 1 (by rfl) ⟨15873947, by rfl⟩ : syracuseStep 21165263 = 31747895) B31747895
theorem B53564723 : Blo 1738570 53564723 := bstep (se 1 (by rfl) ⟨40173542, by rfl⟩ : syracuseStep 53564723 = 80347085) B80347085
theorem B2610599 : Blo 1738570 2610599 := bstep (se 1 (by rfl) ⟨1957949, by rfl⟩ : syracuseStep 2610599 = 3915899) B3915899
theorem B4404719 : Blo 1738570 4404719 := bstep (se 1 (by rfl) ⟨3303539, by rfl⟩ : syracuseStep 4404719 = 6607079) B6607079
theorem B14112251 : Blo 1738570 14112251 := bstep (se 1 (by rfl) ⟨10584188, by rfl⟩ : syracuseStep 14112251 = 21168377) B21168377
theorem B3913343 : Blo 1738570 3913343 := bstep (se 1 (by rfl) ⟨2935007, by rfl⟩ : syracuseStep 3913343 = 5870015) B5870015
theorem B4405225 : Blo 1738570 4405225 := bstep (se 2 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 4405225 = 3303919) B3303919
theorem B35715077 : Blo 1738570 35715077 := bstep (se 4 (by rfl) ⟨3348288, by rfl⟩ : syracuseStep 35715077 = 6696577) B6696577
theorem B5871689 : Blo 1738570 5871689 := bstep (se 2 (by rfl) ⟨2201883, by rfl⟩ : syracuseStep 5871689 = 4403767) B4403767
theorem B3914153 : Blo 1738570 3914153 := bstep (se 2 (by rfl) ⟨1467807, by rfl⟩ : syracuseStep 3914153 = 2935615) B2935615
theorem B4405691 : Blo 1738570 4405691 := bstep (se 1 (by rfl) ⟨3304268, by rfl⟩ : syracuseStep 4405691 = 6608537) B6608537
theorem B3914207 : Blo 1738570 3914207 := bstep (se 1 (by rfl) ⟨2935655, by rfl⟩ : syracuseStep 3914207 = 5871311) B5871311
theorem B6601247 : Blo 1738570 6601247 := bstep (se 1 (by rfl) ⟨4950935, by rfl⟩ : syracuseStep 6601247 = 9901871) B9901871
theorem B2202319 : Blo 1738570 2202319 := bstep (se 1 (by rfl) ⟨1651739, by rfl⟩ : syracuseStep 2202319 = 3303479) B3303479
theorem B13212395 : Blo 1738570 13212395 := bstep (se 1 (by rfl) ⟨9909296, by rfl⟩ : syracuseStep 13212395 = 19818593) B19818593
theorem B6601459 : Blo 1738570 6601459 := bstep (se 1 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 6601459 = 9902189) B9902189
theorem B5872445 : Blo 1738570 5872445 := bstep (se 3 (by rfl) ⟨1101083, by rfl⟩ : syracuseStep 5872445 = 2202167) B2202167
theorem B3914567 : Blo 1738570 3914567 := bstep (se 1 (by rfl) ⟨2935925, by rfl⟩ : syracuseStep 3914567 = 5871851) B5871851
theorem B9911393 : Blo 1738570 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B2202815 : Blo 1738570 2202815 := bstep (se 1 (by rfl) ⟨1652111, by rfl⟩ : syracuseStep 2202815 = 3304223) B3304223
theorem B2350399 : Blo 1738570 2350399 := bstep (se 1 (by rfl) ⟨1762799, by rfl⟩ : syracuseStep 2350399 = 3525599) B3525599
theorem B1957279 : Blo 1738570 1957279 := bstep (se 1 (by rfl) ⟨1467959, by rfl⟩ : syracuseStep 1957279 = 2935919) B2935919
theorem B9903647 : Blo 1738570 9903647 := bstep (se 1 (by rfl) ⟨7427735, by rfl⟩ : syracuseStep 9903647 = 14855471) B14855471
theorem B3300905 : Blo 1738570 3300905 := bstep (se 2 (by rfl) ⟨1237839, by rfl⟩ : syracuseStep 3300905 = 2475679) B2475679
theorem B3915431 : Blo 1738570 3915431 := bstep (se 1 (by rfl) ⟨2936573, by rfl⟩ : syracuseStep 3915431 = 5873147) B5873147
theorem B3915503 : Blo 1738570 3915503 := bstep (se 1 (by rfl) ⟨2936627, by rfl⟩ : syracuseStep 3915503 = 5873255) B5873255
theorem B6602735 : Blo 1738570 6602735 := bstep (se 1 (by rfl) ⟨4952051, by rfl⟩ : syracuseStep 6602735 = 9904103) B9904103
theorem B107143235 : Blo 1738570 107143235 := bstep (se 1 (by rfl) ⟨80357426, by rfl⟩ : syracuseStep 107143235 = 160714853) B160714853
theorem B12533903 : Blo 1738570 12533903 := bstep (se 1 (by rfl) ⟨9400427, by rfl⟩ : syracuseStep 12533903 = 18800855) B18800855
theorem B3301535 : Blo 1738570 3301535 := bstep (se 1 (by rfl) ⟨2476151, by rfl⟩ : syracuseStep 3301535 = 4952303) B4952303
theorem B3916187 : Blo 1738570 3916187 := bstep (se 1 (by rfl) ⟨2937140, by rfl⟩ : syracuseStep 3916187 = 5874281) B5874281
theorem B5874173 : Blo 1738570 5874173 := bstep (se 3 (by rfl) ⟨1101407, by rfl⟩ : syracuseStep 5874173 = 2202815) B2202815
theorem B35709815 : Blo 1738570 35709815 := bstep (se 1 (by rfl) ⟨26782361, by rfl⟩ : syracuseStep 35709815 = 53564723) B53564723
theorem B30524381 : Blo 1738570 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B5571611 : Blo 1738570 5571611 := bstep (se 1 (by rfl) ⟨4178708, by rfl⟩ : syracuseStep 5571611 = 8357417) B8357417
theorem B19825883 : Blo 1738570 19825883 := bstep (se 1 (by rfl) ⟨14869412, by rfl⟩ : syracuseStep 19825883 = 29738825) B29738825
theorem B10577573 : Blo 1738570 10577573 := bstep (se 4 (by rfl) ⟨991647, by rfl⟩ : syracuseStep 10577573 = 1983295) B1983295
theorem B4400831 : Blo 1738570 4400831 := bstep (se 1 (by rfl) ⟨3300623, by rfl⟩ : syracuseStep 4400831 = 6601247) B6601247
theorem B8808263 : Blo 1738570 8808263 := bstep (se 1 (by rfl) ⟨6606197, by rfl⟩ : syracuseStep 8808263 = 13212395) B13212395
theorem B9406697 : Blo 1738570 9406697 := bstep (se 2 (by rfl) ⟨3527511, by rfl⟩ : syracuseStep 9406697 = 7055023) B7055023
theorem B1739111 : Blo 1738570 1739111 := bstep (se 1 (by rfl) ⟨1304333, by rfl⟩ : syracuseStep 1739111 = 2608667) B2608667
theorem B6605165 : Blo 1738570 6605165 := bstep (se 3 (by rfl) ⟨1238468, by rfl⟩ : syracuseStep 6605165 = 2476937) B2476937
theorem B50162125 : Blo 1738570 50162125 := bstep (se 3 (by rfl) ⟨9405398, by rfl⟩ : syracuseStep 50162125 = 18810797) B18810797
theorem B1739239 : Blo 1738570 1739239 := bstep (se 1 (by rfl) ⟨1304429, by rfl⟩ : syracuseStep 1739239 = 2608859) B2608859
theorem B2935271 : Blo 1738570 2935271 := bstep (se 1 (by rfl) ⟨2201453, by rfl⟩ : syracuseStep 2935271 = 4402907) B4402907
theorem B4401823 : Blo 1738570 4401823 := bstep (se 1 (by rfl) ⟨3301367, by rfl⟩ : syracuseStep 4401823 = 6602735) B6602735
theorem B2607935 : Blo 1738570 2607935 := bstep (se 1 (by rfl) ⟨1955951, by rfl⟩ : syracuseStep 2607935 = 3911903) B3911903
theorem B5868719 : Blo 1738570 5868719 := bstep (se 1 (by rfl) ⟨4401539, by rfl⟩ : syracuseStep 5868719 = 8803079) B8803079
theorem B2608379 : Blo 1738570 2608379 := bstep (se 1 (by rfl) ⟨1956284, by rfl⟩ : syracuseStep 2608379 = 3912569) B3912569
theorem B2936135 : Blo 1738570 2936135 := bstep (se 1 (by rfl) ⟨2202101, by rfl⟩ : syracuseStep 2936135 = 4404203) B4404203
theorem B53587277 : Blo 1738570 53587277 := bstep (se 3 (by rfl) ⟨10047614, by rfl⟩ : syracuseStep 53587277 = 20095229) B20095229
theorem B1740239 : Blo 1738570 1740239 := bstep (se 1 (by rfl) ⟨1305179, by rfl⟩ : syracuseStep 1740239 = 2610359) B2610359
theorem B14110175 : Blo 1738570 14110175 := bstep (se 1 (by rfl) ⟨10582631, by rfl⟩ : syracuseStep 14110175 = 21165263) B21165263
theorem B2936425 : Blo 1738570 2936425 := bstep (se 2 (by rfl) ⟨1101159, by rfl⟩ : syracuseStep 2936425 = 2202319) B2202319
theorem B1740399 : Blo 1738570 1740399 := bstep (se 1 (by rfl) ⟨1305299, by rfl⟩ : syracuseStep 1740399 = 2610599) B2610599
theorem B8801945 : Blo 1738570 8801945 := bstep (se 2 (by rfl) ⟨3300729, by rfl⟩ : syracuseStep 8801945 = 6601459) B6601459
theorem B2936479 : Blo 1738570 2936479 := bstep (se 1 (by rfl) ⟨2202359, by rfl⟩ : syracuseStep 2936479 = 4404719) B4404719
theorem B9408167 : Blo 1738570 9408167 := bstep (se 1 (by rfl) ⟨7056125, by rfl⟩ : syracuseStep 9408167 = 14112251) B14112251
theorem B2608895 : Blo 1738570 2608895 := bstep (se 1 (by rfl) ⟨1956671, by rfl⟩ : syracuseStep 2608895 = 3913343) B3913343
theorem B23810051 : Blo 1738570 23810051 := bstep (se 1 (by rfl) ⟨17857538, by rfl⟩ : syracuseStep 23810051 = 35715077) B35715077
theorem B18100345 : Blo 1738570 18100345 := bstep (se 2 (by rfl) ⟨6787629, by rfl⟩ : syracuseStep 18100345 = 13575259) B13575259
theorem B2609435 : Blo 1738570 2609435 := bstep (se 1 (by rfl) ⟨1957076, by rfl⟩ : syracuseStep 2609435 = 3914153) B3914153
theorem B2937127 : Blo 1738570 2937127 := bstep (se 1 (by rfl) ⟨2202845, by rfl⟩ : syracuseStep 2937127 = 4405691) B4405691
theorem B2609471 : Blo 1738570 2609471 := bstep (se 1 (by rfl) ⟨1957103, by rfl⟩ : syracuseStep 2609471 = 3914207) B3914207
theorem B3133865 : Blo 1738570 3133865 := bstep (se 2 (by rfl) ⟨1175199, by rfl⟩ : syracuseStep 3133865 = 2350399) B2350399
theorem B2609705 : Blo 1738570 2609705 := bstep (se 2 (by rfl) ⟨978639, by rfl⟩ : syracuseStep 2609705 = 1957279) B1957279
theorem B2609711 : Blo 1738570 2609711 := bstep (se 1 (by rfl) ⟨1957283, by rfl⟩ : syracuseStep 2609711 = 3914567) B3914567
theorem B6607595 : Blo 1738570 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B2200603 : Blo 1738570 2200603 := bstep (se 1 (by rfl) ⟨1650452, by rfl⟩ : syracuseStep 2200603 = 3300905) B3300905
theorem B2610287 : Blo 1738570 2610287 := bstep (se 1 (by rfl) ⟨1957715, by rfl⟩ : syracuseStep 2610287 = 3915431) B3915431
theorem B2610335 : Blo 1738570 2610335 := bstep (se 1 (by rfl) ⟨1957751, by rfl⟩ : syracuseStep 2610335 = 3915503) B3915503
theorem B26768573 : Blo 1738570 26768573 := bstep (se 3 (by rfl) ⟨5019107, by rfl⟩ : syracuseStep 26768573 = 10038215) B10038215
theorem B2610623 : Blo 1738570 2610623 := bstep (se 1 (by rfl) ⟨1957967, by rfl⟩ : syracuseStep 2610623 = 3915935) B3915935
theorem B5871095 : Blo 1738570 5871095 := bstep (se 1 (by rfl) ⟨4403321, by rfl⟩ : syracuseStep 5871095 = 8806643) B8806643
theorem B8926847 : Blo 1738570 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B514660013 : Blo 1738570 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B1956199 : Blo 1738570 1956199 := bstep (se 1 (by rfl) ⟨1467149, by rfl⟩ : syracuseStep 1956199 = 2934299) B2934299
theorem B11147807 : Blo 1738570 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B3914459 : Blo 1738570 3914459 := bstep (se 1 (by rfl) ⟨2935844, by rfl⟩ : syracuseStep 3914459 = 5871689) B5871689
theorem B22289357 : Blo 1738570 22289357 := bstep (se 3 (by rfl) ⟨4179254, by rfl⟩ : syracuseStep 22289357 = 8358509) B8358509
theorem B1956991 : Blo 1738570 1956991 := bstep (se 1 (by rfl) ⟨1467743, by rfl⟩ : syracuseStep 1956991 = 2935487) B2935487
theorem B3914963 : Blo 1738570 3914963 := bstep (se 1 (by rfl) ⟨2936222, by rfl⟩ : syracuseStep 3914963 = 5872445) B5872445
theorem B8805995 : Blo 1738570 8805995 := bstep (se 1 (by rfl) ⟨6604496, by rfl⟩ : syracuseStep 8805995 = 13208993) B13208993
theorem B1957531 : Blo 1738570 1957531 := bstep (se 1 (by rfl) ⟨1468148, by rfl⟩ : syracuseStep 1957531 = 2936297) B2936297
theorem B6602431 : Blo 1738570 6602431 := bstep (se 1 (by rfl) ⟨4951823, by rfl⟩ : syracuseStep 6602431 = 9903647) B9903647
theorem B1957567 : Blo 1738570 1957567 := bstep (se 1 (by rfl) ⟨1468175, by rfl⟩ : syracuseStep 1957567 = 2936351) B2936351
theorem B5873633 : Blo 1738570 5873633 := bstep (se 2 (by rfl) ⟨2202612, by rfl⟩ : syracuseStep 5873633 = 4405225) B4405225
theorem B8355935 : Blo 1738570 8355935 := bstep (se 1 (by rfl) ⟨6266951, by rfl⟩ : syracuseStep 8355935 = 12533903) B12533903
theorem B24133793 : Blo 1738570 24133793 := bstep (se 2 (by rfl) ⟨9050172, by rfl⟩ : syracuseStep 24133793 = 18100345) B18100345
theorem B2089243 : Blo 1738570 2089243 := bstep (se 1 (by rfl) ⟨1566932, by rfl⟩ : syracuseStep 2089243 = 3133865) B3133865
theorem B3916115 : Blo 1738570 3916115 := bstep (se 1 (by rfl) ⟨2937086, by rfl⟩ : syracuseStep 3916115 = 5874173) B5874173
theorem B3916169 : Blo 1738570 3916169 := bstep (se 2 (by rfl) ⟨1468563, by rfl⟩ : syracuseStep 3916169 = 2937127) B2937127
theorem B23806543 : Blo 1738570 23806543 := bstep (se 1 (by rfl) ⟨17854907, by rfl⟩ : syracuseStep 23806543 = 35709815) B35709815
theorem B25084525 : Blo 1738570 25084525 := bstep (se 3 (by rfl) ⟨4703348, by rfl⟩ : syracuseStep 25084525 = 9406697) B9406697
theorem B20349587 : Blo 1738570 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B343106675 : Blo 1738570 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B2933887 : Blo 1738570 2933887 := bstep (se 1 (by rfl) ⟨2200415, by rfl⟩ : syracuseStep 2933887 = 4400831) B4400831
theorem B2934137 : Blo 1738570 2934137 := bstep (se 2 (by rfl) ⟨1100301, by rfl⟩ : syracuseStep 2934137 = 2200603) B2200603
theorem B7431871 : Blo 1738570 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B1738623 : Blo 1738570 1738623 := bstep (se 1 (by rfl) ⟨1303967, by rfl⟩ : syracuseStep 1738623 = 2607935) B2607935
theorem B1738919 : Blo 1738570 1738919 := bstep (se 1 (by rfl) ⟨1304189, by rfl⟩ : syracuseStep 1738919 = 2608379) B2608379
theorem B9406783 : Blo 1738570 9406783 := bstep (se 1 (by rfl) ⟨7055087, by rfl⟩ : syracuseStep 9406783 = 14110175) B14110175
theorem B5867963 : Blo 1738570 5867963 := bstep (se 1 (by rfl) ⟨4400972, by rfl⟩ : syracuseStep 5867963 = 8801945) B8801945
theorem B1739263 : Blo 1738570 1739263 := bstep (se 1 (by rfl) ⟨1304447, by rfl⟩ : syracuseStep 1739263 = 2608895) B2608895
theorem B71428823 : Blo 1738570 71428823 := bstep (se 1 (by rfl) ⟨53571617, by rfl⟩ : syracuseStep 71428823 = 107143235) B107143235
theorem B1739623 : Blo 1738570 1739623 := bstep (se 1 (by rfl) ⟨1304717, by rfl⟩ : syracuseStep 1739623 = 2609435) B2609435
theorem B1739647 : Blo 1738570 1739647 := bstep (se 1 (by rfl) ⟨1304735, by rfl⟩ : syracuseStep 1739647 = 2609471) B2609471
theorem B1739803 : Blo 1738570 1739803 := bstep (se 1 (by rfl) ⟨1304852, by rfl⟩ : syracuseStep 1739803 = 2609705) B2609705
theorem B1739807 : Blo 1738570 1739807 := bstep (se 1 (by rfl) ⟨1304855, by rfl⟩ : syracuseStep 1739807 = 2609711) B2609711
theorem B2608265 : Blo 1738570 2608265 := bstep (se 2 (by rfl) ⟨978099, by rfl⟩ : syracuseStep 2608265 = 1956199) B1956199
theorem B66882833 : Blo 1738570 66882833 := bstep (se 2 (by rfl) ⟨25081062, by rfl⟩ : syracuseStep 66882833 = 50162125) B50162125
theorem B3714407 : Blo 1738570 3714407 := bstep (se 1 (by rfl) ⟨2785805, by rfl⟩ : syracuseStep 3714407 = 5571611) B5571611
theorem B1740191 : Blo 1738570 1740191 := bstep (se 1 (by rfl) ⟨1305143, by rfl⟩ : syracuseStep 1740191 = 2610287) B2610287
theorem B1740223 : Blo 1738570 1740223 := bstep (se 1 (by rfl) ⟨1305167, by rfl⟩ : syracuseStep 1740223 = 2610335) B2610335
theorem B17845715 : Blo 1738570 17845715 := bstep (se 1 (by rfl) ⟨13384286, by rfl⟩ : syracuseStep 17845715 = 26768573) B26768573
theorem B13217255 : Blo 1738570 13217255 := bstep (se 1 (by rfl) ⟨9912941, by rfl⟩ : syracuseStep 13217255 = 19825883) B19825883
theorem B5869097 : Blo 1738570 5869097 := bstep (se 2 (by rfl) ⟨2200911, by rfl⟩ : syracuseStep 5869097 = 4401823) B4401823
theorem B1740415 : Blo 1738570 1740415 := bstep (se 1 (by rfl) ⟨1305311, by rfl⟩ : syracuseStep 1740415 = 2610623) B2610623
theorem B5951231 : Blo 1738570 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B2609321 : Blo 1738570 2609321 := bstep (se 2 (by rfl) ⟨978495, by rfl⟩ : syracuseStep 2609321 = 1956991) B1956991
theorem B4403443 : Blo 1738570 4403443 := bstep (se 1 (by rfl) ⟨3302582, by rfl⟩ : syracuseStep 4403443 = 6605165) B6605165
theorem B2609639 : Blo 1738570 2609639 := bstep (se 1 (by rfl) ⟨1957229, by rfl⟩ : syracuseStep 2609639 = 3914459) B3914459
theorem B3912479 : Blo 1738570 3912479 := bstep (se 1 (by rfl) ⟨2934359, by rfl⟩ : syracuseStep 3912479 = 5868719) B5868719
theorem B2609975 : Blo 1738570 2609975 := bstep (se 1 (by rfl) ⟨1957481, by rfl⟩ : syracuseStep 2609975 = 3914963) B3914963
theorem B2610041 : Blo 1738570 2610041 := bstep (se 2 (by rfl) ⟨978765, by rfl⟩ : syracuseStep 2610041 = 1957531) B1957531
theorem B8803241 : Blo 1738570 8803241 := bstep (se 2 (by rfl) ⟨3301215, by rfl⟩ : syracuseStep 8803241 = 6602431) B6602431
theorem B2610089 : Blo 1738570 2610089 := bstep (se 2 (by rfl) ⟨978783, by rfl⟩ : syracuseStep 2610089 = 1957567) B1957567
theorem B5870663 : Blo 1738570 5870663 := bstep (se 1 (by rfl) ⟨4402997, by rfl⟩ : syracuseStep 5870663 = 8805995) B8805995
theorem B6272111 : Blo 1738570 6272111 := bstep (se 1 (by rfl) ⟨4704083, by rfl⟩ : syracuseStep 6272111 = 9408167) B9408167
theorem B15873367 : Blo 1738570 15873367 := bstep (se 1 (by rfl) ⟨11905025, by rfl⟩ : syracuseStep 15873367 = 23810051) B23810051
theorem B2201023 : Blo 1738570 2201023 := bstep (se 1 (by rfl) ⟨1650767, by rfl⟩ : syracuseStep 2201023 = 3301535) B3301535
theorem B2610791 : Blo 1738570 2610791 := bstep (se 1 (by rfl) ⟨1958093, by rfl⟩ : syracuseStep 2610791 = 3916187) B3916187
theorem B4405063 : Blo 1738570 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B3914063 : Blo 1738570 3914063 := bstep (se 1 (by rfl) ⟨2935547, by rfl⟩ : syracuseStep 3914063 = 5871095) B5871095
theorem B7051715 : Blo 1738570 7051715 := bstep (se 1 (by rfl) ⟨5288786, by rfl⟩ : syracuseStep 7051715 = 10577573) B10577573
theorem B5872175 : Blo 1738570 5872175 := bstep (se 1 (by rfl) ⟨4404131, by rfl⟩ : syracuseStep 5872175 = 8808263) B8808263
theorem B1956847 : Blo 1738570 1956847 := bstep (se 1 (by rfl) ⟨1467635, by rfl⟩ : syracuseStep 1956847 = 2935271) B2935271
theorem B14859571 : Blo 1738570 14859571 := bstep (se 1 (by rfl) ⟨11144678, by rfl⟩ : syracuseStep 14859571 = 22289357) B22289357
theorem B3915233 : Blo 1738570 3915233 := bstep (se 2 (by rfl) ⟨1468212, by rfl⟩ : syracuseStep 3915233 = 2936425) B2936425
theorem B3915305 : Blo 1738570 3915305 := bstep (se 2 (by rfl) ⟨1468239, by rfl⟩ : syracuseStep 3915305 = 2936479) B2936479
theorem B1957423 : Blo 1738570 1957423 := bstep (se 1 (by rfl) ⟨1468067, by rfl⟩ : syracuseStep 1957423 = 2936135) B2936135
theorem B35724851 : Blo 1738570 35724851 := bstep (se 1 (by rfl) ⟨26793638, by rfl⟩ : syracuseStep 35724851 = 53587277) B53587277
theorem B3915755 : Blo 1738570 3915755 := bstep (se 1 (by rfl) ⟨2936816, by rfl⟩ : syracuseStep 3915755 = 5873633) B5873633
theorem B5570623 : Blo 1738570 5570623 := bstep (se 1 (by rfl) ⟨4177967, by rfl⟩ : syracuseStep 5570623 = 8355935) B8355935
theorem B12542377 : Blo 1738570 12542377 := bstep (se 2 (by rfl) ⟨4703391, by rfl⟩ : syracuseStep 12542377 = 9406783) B9406783
theorem B64356781 : Blo 1738570 64356781 := bstep (se 3 (by rfl) ⟨12066896, by rfl⟩ : syracuseStep 64356781 = 24133793) B24133793
theorem B228737783 : Blo 1738570 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B47588573 : Blo 1738570 47588573 := bstep (se 3 (by rfl) ⟨8922857, by rfl⟩ : syracuseStep 47588573 = 17845715) B17845715
theorem B11142629 : Blo 1738570 11142629 := bstep (se 4 (by rfl) ⟨1044621, by rfl⟩ : syracuseStep 11142629 = 2089243) B2089243
theorem B54265565 : Blo 1738570 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B2934697 : Blo 1738570 2934697 := bstep (se 2 (by rfl) ⟨1100511, by rfl⟩ : syracuseStep 2934697 = 2201023) B2201023
theorem B1738843 : Blo 1738570 1738843 := bstep (se 1 (by rfl) ⟨1304132, by rfl⟩ : syracuseStep 1738843 = 2608265) B2608265
theorem B2476271 : Blo 1738570 2476271 := bstep (se 1 (by rfl) ⟨1857203, by rfl⟩ : syracuseStep 2476271 = 3714407) B3714407
theorem B23816567 : Blo 1738570 23816567 := bstep (se 1 (by rfl) ⟨17862425, by rfl⟩ : syracuseStep 23816567 = 35724851) B35724851
theorem B3967487 : Blo 1738570 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B1739547 : Blo 1738570 1739547 := bstep (se 1 (by rfl) ⟨1304660, by rfl⟩ : syracuseStep 1739547 = 2609321) B2609321
theorem B1739759 : Blo 1738570 1739759 := bstep (se 1 (by rfl) ⟨1304819, by rfl⟩ : syracuseStep 1739759 = 2609639) B2609639
theorem B2608319 : Blo 1738570 2608319 := bstep (se 1 (by rfl) ⟨1956239, by rfl⟩ : syracuseStep 2608319 = 3912479) B3912479
theorem B1739983 : Blo 1738570 1739983 := bstep (se 1 (by rfl) ⟨1304987, by rfl⟩ : syracuseStep 1739983 = 2609975) B2609975
theorem B1740027 : Blo 1738570 1740027 := bstep (se 1 (by rfl) ⟨1305020, by rfl⟩ : syracuseStep 1740027 = 2610041) B2610041
theorem B5868827 : Blo 1738570 5868827 := bstep (se 1 (by rfl) ⟨4401620, by rfl⟩ : syracuseStep 5868827 = 8803241) B8803241
theorem B1740059 : Blo 1738570 1740059 := bstep (se 1 (by rfl) ⟨1305044, by rfl⟩ : syracuseStep 1740059 = 2610089) B2610089
theorem B1740527 : Blo 1738570 1740527 := bstep (se 1 (by rfl) ⟨1305395, by rfl⟩ : syracuseStep 1740527 = 2610791) B2610791
theorem B2609129 : Blo 1738570 2609129 := bstep (se 2 (by rfl) ⟨978423, by rfl⟩ : syracuseStep 2609129 = 1956847) B1956847
theorem B3911849 : Blo 1738570 3911849 := bstep (se 2 (by rfl) ⟨1466943, by rfl⟩ : syracuseStep 3911849 = 2933887) B2933887
theorem B2609375 : Blo 1738570 2609375 := bstep (se 1 (by rfl) ⟨1957031, by rfl⟩ : syracuseStep 2609375 = 3914063) B3914063
theorem B3911975 : Blo 1738570 3911975 := bstep (se 1 (by rfl) ⟨2933981, by rfl⟩ : syracuseStep 3911975 = 5867963) B5867963
theorem B19812761 : Blo 1738570 19812761 := bstep (se 2 (by rfl) ⟨7429785, by rfl⟩ : syracuseStep 19812761 = 14859571) B14859571
theorem B21164489 : Blo 1738570 21164489 := bstep (se 2 (by rfl) ⟨7936683, by rfl⟩ : syracuseStep 21164489 = 15873367) B15873367
theorem B2609897 : Blo 1738570 2609897 := bstep (se 2 (by rfl) ⟨978711, by rfl⟩ : syracuseStep 2609897 = 1957423) B1957423
theorem B9909161 : Blo 1738570 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B2610155 : Blo 1738570 2610155 := bstep (se 1 (by rfl) ⟨1957616, by rfl⟩ : syracuseStep 2610155 = 3915233) B3915233
theorem B8811503 : Blo 1738570 8811503 := bstep (se 1 (by rfl) ⟨6608627, by rfl⟩ : syracuseStep 8811503 = 13217255) B13217255
theorem B3912731 : Blo 1738570 3912731 := bstep (se 1 (by rfl) ⟨2934548, by rfl⟩ : syracuseStep 3912731 = 5869097) B5869097
theorem B2610203 : Blo 1738570 2610203 := bstep (se 1 (by rfl) ⟨1957652, by rfl⟩ : syracuseStep 2610203 = 3915305) B3915305
theorem B2610503 : Blo 1738570 2610503 := bstep (se 1 (by rfl) ⟨1957877, by rfl⟩ : syracuseStep 2610503 = 3915755) B3915755
theorem B2610743 : Blo 1738570 2610743 := bstep (se 1 (by rfl) ⟨1958057, by rfl⟩ : syracuseStep 2610743 = 3916115) B3916115
theorem B2610779 : Blo 1738570 2610779 := bstep (se 1 (by rfl) ⟨1958084, by rfl⟩ : syracuseStep 2610779 = 3916169) B3916169
theorem B16725629 : Blo 1738570 16725629 := bstep (se 3 (by rfl) ⟨3136055, by rfl⟩ : syracuseStep 16725629 = 6272111) B6272111
theorem B5871257 : Blo 1738570 5871257 := bstep (se 2 (by rfl) ⟨2201721, by rfl⟩ : syracuseStep 5871257 = 4403443) B4403443
theorem B3913775 : Blo 1738570 3913775 := bstep (se 1 (by rfl) ⟨2935331, by rfl⟩ : syracuseStep 3913775 = 5870663) B5870663
theorem B31742057 : Blo 1738570 31742057 := bstep (se 2 (by rfl) ⟨11903271, by rfl⟩ : syracuseStep 31742057 = 23806543) B23806543
theorem B33446033 : Blo 1738570 33446033 := bstep (se 2 (by rfl) ⟨12542262, by rfl⟩ : syracuseStep 33446033 = 25084525) B25084525
theorem B1956091 : Blo 1738570 1956091 := bstep (se 1 (by rfl) ⟨1467068, by rfl⟩ : syracuseStep 1956091 = 2934137) B2934137
theorem B4701143 : Blo 1738570 4701143 := bstep (se 1 (by rfl) ⟨3525857, by rfl⟩ : syracuseStep 4701143 = 7051715) B7051715
theorem B3914783 : Blo 1738570 3914783 := bstep (se 1 (by rfl) ⟨2936087, by rfl⟩ : syracuseStep 3914783 = 5872175) B5872175
theorem B47619215 : Blo 1738570 47619215 := bstep (se 1 (by rfl) ⟨35714411, by rfl⟩ : syracuseStep 47619215 = 71428823) B71428823
theorem B44588555 : Blo 1738570 44588555 := bstep (se 1 (by rfl) ⟨33441416, by rfl⟩ : syracuseStep 44588555 = 66882833) B66882833
theorem B5873417 : Blo 1738570 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B6603389 : Blo 1738570 6603389 := bstep (se 3 (by rfl) ⟨1238135, by rfl⟩ : syracuseStep 6603389 = 2476271) B2476271
theorem B5874335 : Blo 1738570 5874335 := bstep (se 1 (by rfl) ⟨4405751, by rfl⟩ : syracuseStep 5874335 = 8811503) B8811503
theorem B36177043 : Blo 1738570 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B21161371 : Blo 1738570 21161371 := bstep (se 1 (by rfl) ⟨15871028, by rfl⟩ : syracuseStep 21161371 = 31742057) B31742057
theorem B15877711 : Blo 1738570 15877711 := bstep (se 1 (by rfl) ⟨11908283, by rfl⟩ : syracuseStep 15877711 = 23816567) B23816567
theorem B31746143 : Blo 1738570 31746143 := bstep (se 1 (by rfl) ⟨23809607, by rfl⟩ : syracuseStep 31746143 = 47619215) B47619215
theorem B1738879 : Blo 1738570 1738879 := bstep (se 1 (by rfl) ⟨1304159, by rfl⟩ : syracuseStep 1738879 = 2608319) B2608319
theorem B1739419 : Blo 1738570 1739419 := bstep (se 1 (by rfl) ⟨1304564, by rfl⟩ : syracuseStep 1739419 = 2609129) B2609129
theorem B2607899 : Blo 1738570 2607899 := bstep (se 1 (by rfl) ⟨1955924, by rfl⟩ : syracuseStep 2607899 = 3911849) B3911849
theorem B1739583 : Blo 1738570 1739583 := bstep (se 1 (by rfl) ⟨1304687, by rfl⟩ : syracuseStep 1739583 = 2609375) B2609375
theorem B2607983 : Blo 1738570 2607983 := bstep (se 1 (by rfl) ⟨1955987, by rfl⟩ : syracuseStep 2607983 = 3911975) B3911975
theorem B13208507 : Blo 1738570 13208507 := bstep (se 1 (by rfl) ⟨9906380, by rfl⟩ : syracuseStep 13208507 = 19812761) B19812761
theorem B14109659 : Blo 1738570 14109659 := bstep (se 1 (by rfl) ⟨10582244, by rfl⟩ : syracuseStep 14109659 = 21164489) B21164489
theorem B2608121 : Blo 1738570 2608121 := bstep (se 2 (by rfl) ⟨978045, by rfl⟩ : syracuseStep 2608121 = 1956091) B1956091
theorem B1739931 : Blo 1738570 1739931 := bstep (se 1 (by rfl) ⟨1304948, by rfl⟩ : syracuseStep 1739931 = 2609897) B2609897
theorem B16723169 : Blo 1738570 16723169 := bstep (se 2 (by rfl) ⟨6271188, by rfl⟩ : syracuseStep 16723169 = 12542377) B12542377
theorem B6606107 : Blo 1738570 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B1740103 : Blo 1738570 1740103 := bstep (se 1 (by rfl) ⟨1305077, by rfl⟩ : syracuseStep 1740103 = 2610155) B2610155
theorem B2608487 : Blo 1738570 2608487 := bstep (se 1 (by rfl) ⟨1956365, by rfl⟩ : syracuseStep 2608487 = 3912731) B3912731
theorem B1740135 : Blo 1738570 1740135 := bstep (se 1 (by rfl) ⟨1305101, by rfl⟩ : syracuseStep 1740135 = 2610203) B2610203
theorem B1740335 : Blo 1738570 1740335 := bstep (se 1 (by rfl) ⟨1305251, by rfl⟩ : syracuseStep 1740335 = 2610503) B2610503
theorem B1740495 : Blo 1738570 1740495 := bstep (se 1 (by rfl) ⟨1305371, by rfl⟩ : syracuseStep 1740495 = 2610743) B2610743
theorem B1740519 : Blo 1738570 1740519 := bstep (se 1 (by rfl) ⟨1305389, by rfl⟩ : syracuseStep 1740519 = 2610779) B2610779
theorem B2609183 : Blo 1738570 2609183 := bstep (se 1 (by rfl) ⟨1956887, by rfl⟩ : syracuseStep 2609183 = 3913775) B3913775
theorem B44601677 : Blo 1738570 44601677 := bstep (se 3 (by rfl) ⟨8362814, by rfl⟩ : syracuseStep 44601677 = 16725629) B16725629
theorem B3134095 : Blo 1738570 3134095 := bstep (se 1 (by rfl) ⟨2350571, by rfl⟩ : syracuseStep 3134095 = 4701143) B4701143
theorem B2609855 : Blo 1738570 2609855 := bstep (se 1 (by rfl) ⟨1957391, by rfl⟩ : syracuseStep 2609855 = 3914783) B3914783
theorem B3912551 : Blo 1738570 3912551 := bstep (se 1 (by rfl) ⟨2934413, by rfl⟩ : syracuseStep 3912551 = 5868827) B5868827
theorem B29725703 : Blo 1738570 29725703 := bstep (se 1 (by rfl) ⟨22294277, by rfl⟩ : syracuseStep 29725703 = 44588555) B44588555
theorem B3912929 : Blo 1738570 3912929 := bstep (se 2 (by rfl) ⟨1467348, by rfl⟩ : syracuseStep 3912929 = 2934697) B2934697
theorem B7427497 : Blo 1738570 7427497 := bstep (se 2 (by rfl) ⟨2785311, by rfl⟩ : syracuseStep 7427497 = 5570623) B5570623
theorem B152491855 : Blo 1738570 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B85809041 : Blo 1738570 85809041 := bstep (se 2 (by rfl) ⟨32178390, by rfl⟩ : syracuseStep 85809041 = 64356781) B64356781
theorem B31725715 : Blo 1738570 31725715 := bstep (se 1 (by rfl) ⟨23794286, by rfl⟩ : syracuseStep 31725715 = 47588573) B47588573
theorem B7428419 : Blo 1738570 7428419 := bstep (se 1 (by rfl) ⟨5571314, by rfl⟩ : syracuseStep 7428419 = 11142629) B11142629
theorem B3914171 : Blo 1738570 3914171 := bstep (se 1 (by rfl) ⟨2935628, by rfl⟩ : syracuseStep 3914171 = 5871257) B5871257
theorem B22297355 : Blo 1738570 22297355 := bstep (se 1 (by rfl) ⟨16723016, by rfl⟩ : syracuseStep 22297355 = 33446033) B33446033
theorem B2644991 : Blo 1738570 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B3915611 : Blo 1738570 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B3916223 : Blo 1738570 3916223 := bstep (se 1 (by rfl) ⟨2937167, by rfl⟩ : syracuseStep 3916223 = 5874335) B5874335
theorem B19817135 : Blo 1738570 19817135 := bstep (se 1 (by rfl) ⟨14862851, by rfl⟩ : syracuseStep 19817135 = 29725703) B29725703
theorem B57206027 : Blo 1738570 57206027 := bstep (se 1 (by rfl) ⟨42904520, by rfl⟩ : syracuseStep 57206027 = 85809041) B85809041
theorem B48236057 : Blo 1738570 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B1738599 : Blo 1738570 1738599 := bstep (se 1 (by rfl) ⟨1303949, by rfl⟩ : syracuseStep 1738599 = 2607899) B2607899
theorem B28215161 : Blo 1738570 28215161 := bstep (se 2 (by rfl) ⟨10580685, by rfl⟩ : syracuseStep 28215161 = 21161371) B21161371
theorem B1738655 : Blo 1738570 1738655 := bstep (se 1 (by rfl) ⟨1303991, by rfl⟩ : syracuseStep 1738655 = 2607983) B2607983
theorem B9406439 : Blo 1738570 9406439 := bstep (se 1 (by rfl) ⟨7054829, by rfl⟩ : syracuseStep 9406439 = 14109659) B14109659
theorem B1738747 : Blo 1738570 1738747 := bstep (se 1 (by rfl) ⟨1304060, by rfl⟩ : syracuseStep 1738747 = 2608121) B2608121
theorem B1763327 : Blo 1738570 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B21170281 : Blo 1738570 21170281 := bstep (se 2 (by rfl) ⟨7938855, by rfl⟩ : syracuseStep 21170281 = 15877711) B15877711
theorem B1738991 : Blo 1738570 1738991 := bstep (se 1 (by rfl) ⟨1304243, by rfl⟩ : syracuseStep 1738991 = 2608487) B2608487
theorem B1739455 : Blo 1738570 1739455 := bstep (se 1 (by rfl) ⟨1304591, by rfl⟩ : syracuseStep 1739455 = 2609183) B2609183
theorem B4402259 : Blo 1738570 4402259 := bstep (se 1 (by rfl) ⟨3301694, by rfl⟩ : syracuseStep 4402259 = 6603389) B6603389
theorem B1739903 : Blo 1738570 1739903 := bstep (se 1 (by rfl) ⟨1304927, by rfl⟩ : syracuseStep 1739903 = 2609855) B2609855
theorem B2608367 : Blo 1738570 2608367 := bstep (se 1 (by rfl) ⟨1956275, by rfl⟩ : syracuseStep 2608367 = 3912551) B3912551
theorem B16715173 : Blo 1738570 16715173 := bstep (se 4 (by rfl) ⟨1567047, by rfl⟩ : syracuseStep 16715173 = 3134095) B3134095
theorem B2608619 : Blo 1738570 2608619 := bstep (se 1 (by rfl) ⟨1956464, by rfl⟩ : syracuseStep 2608619 = 3912929) B3912929
theorem B21164095 : Blo 1738570 21164095 := bstep (se 1 (by rfl) ⟨15873071, by rfl⟩ : syracuseStep 21164095 = 31746143) B31746143
theorem B4952279 : Blo 1738570 4952279 := bstep (se 1 (by rfl) ⟨3714209, by rfl⟩ : syracuseStep 4952279 = 7428419) B7428419
theorem B2609447 : Blo 1738570 2609447 := bstep (se 1 (by rfl) ⟨1957085, by rfl⟩ : syracuseStep 2609447 = 3914171) B3914171
theorem B14864903 : Blo 1738570 14864903 := bstep (se 1 (by rfl) ⟨11148677, by rfl⟩ : syracuseStep 14864903 = 22297355) B22297355
theorem B4404071 : Blo 1738570 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B203322473 : Blo 1738570 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B2610407 : Blo 1738570 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B42300953 : Blo 1738570 42300953 := bstep (se 2 (by rfl) ⟨15862857, by rfl⟩ : syracuseStep 42300953 = 31725715) B31725715
theorem B29734451 : Blo 1738570 29734451 := bstep (se 1 (by rfl) ⟨22300838, by rfl⟩ : syracuseStep 29734451 = 44601677) B44601677
theorem B9903329 : Blo 1738570 9903329 := bstep (se 2 (by rfl) ⟨3713748, by rfl⟩ : syracuseStep 9903329 = 7427497) B7427497
theorem B8805671 : Blo 1738570 8805671 := bstep (se 1 (by rfl) ⟨6604253, by rfl⟩ : syracuseStep 8805671 = 13208507) B13208507
theorem B11148779 : Blo 1738570 11148779 := bstep (se 1 (by rfl) ⟨8361584, by rfl⟩ : syracuseStep 11148779 = 16723169) B16723169
theorem B13206077 : Blo 1738570 13206077 := bstep (se 3 (by rfl) ⟨2476139, by rfl⟩ : syracuseStep 13206077 = 4952279) B4952279
theorem B18810107 : Blo 1738570 18810107 := bstep (se 1 (by rfl) ⟨14107580, by rfl⟩ : syracuseStep 18810107 = 28215161) B28215161
theorem B29730077 : Blo 1738570 29730077 := bstep (se 3 (by rfl) ⟨5574389, by rfl⟩ : syracuseStep 29730077 = 11148779) B11148779
theorem B2934839 : Blo 1738570 2934839 := bstep (se 1 (by rfl) ⟨2201129, by rfl⟩ : syracuseStep 2934839 = 4402259) B4402259
theorem B1738911 : Blo 1738570 1738911 := bstep (se 1 (by rfl) ⟨1304183, by rfl⟩ : syracuseStep 1738911 = 2608367) B2608367
theorem B1739079 : Blo 1738570 1739079 := bstep (se 1 (by rfl) ⟨1304309, by rfl⟩ : syracuseStep 1739079 = 2608619) B2608619
theorem B1739631 : Blo 1738570 1739631 := bstep (se 1 (by rfl) ⟨1304723, by rfl⟩ : syracuseStep 1739631 = 2609447) B2609447
theorem B2936047 : Blo 1738570 2936047 := bstep (se 1 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 2936047 = 4404071) B4404071
theorem B135548315 : Blo 1738570 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B1740271 : Blo 1738570 1740271 := bstep (se 1 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 1740271 = 2610407) B2610407
theorem B38137351 : Blo 1738570 38137351 := bstep (se 1 (by rfl) ⟨28603013, by rfl⟩ : syracuseStep 38137351 = 57206027) B57206027
theorem B32157371 : Blo 1738570 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B28200635 : Blo 1738570 28200635 := bstep (se 1 (by rfl) ⟨21150476, by rfl⟩ : syracuseStep 28200635 = 42300953) B42300953
theorem B6270959 : Blo 1738570 6270959 := bstep (se 1 (by rfl) ⟨4703219, by rfl⟩ : syracuseStep 6270959 = 9406439) B9406439
theorem B22286897 : Blo 1738570 22286897 := bstep (se 2 (by rfl) ⟨8357586, by rfl⟩ : syracuseStep 22286897 = 16715173) B16715173
theorem B5870447 : Blo 1738570 5870447 := bstep (se 1 (by rfl) ⟨4402835, by rfl⟩ : syracuseStep 5870447 = 8805671) B8805671
theorem B28218793 : Blo 1738570 28218793 := bstep (se 2 (by rfl) ⟨10582047, by rfl⟩ : syracuseStep 28218793 = 21164095) B21164095
theorem B28227041 : Blo 1738570 28227041 := bstep (se 2 (by rfl) ⟨10585140, by rfl⟩ : syracuseStep 28227041 = 21170281) B21170281
theorem B2610815 : Blo 1738570 2610815 := bstep (se 1 (by rfl) ⟨1958111, by rfl⟩ : syracuseStep 2610815 = 3916223) B3916223
theorem B9909935 : Blo 1738570 9909935 := bstep (se 1 (by rfl) ⟨7432451, by rfl⟩ : syracuseStep 9909935 = 14864903) B14864903
theorem B13211423 : Blo 1738570 13211423 := bstep (se 1 (by rfl) ⟨9908567, by rfl⟩ : syracuseStep 13211423 = 19817135) B19817135
theorem B19822967 : Blo 1738570 19822967 := bstep (se 1 (by rfl) ⟨14867225, by rfl⟩ : syracuseStep 19822967 = 29734451) B29734451
theorem B6602219 : Blo 1738570 6602219 := bstep (se 1 (by rfl) ⟨4951664, by rfl⟩ : syracuseStep 6602219 = 9903329) B9903329
theorem B4702205 : Blo 1738570 4702205 := bstep (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) B1763327
theorem B18818027 : Blo 1738570 18818027 := bstep (se 1 (by rfl) ⟨14113520, by rfl⟩ : syracuseStep 18818027 = 28227041) B28227041
theorem B8807615 : Blo 1738570 8807615 := bstep (se 1 (by rfl) ⟨6605711, by rfl⟩ : syracuseStep 8807615 = 13211423) B13211423
theorem B13215311 : Blo 1738570 13215311 := bstep (se 1 (by rfl) ⟨9911483, by rfl⟩ : syracuseStep 13215311 = 19822967) B19822967
theorem B50849801 : Blo 1738570 50849801 := bstep (se 2 (by rfl) ⟨19068675, by rfl⟩ : syracuseStep 50849801 = 38137351) B38137351
theorem B4401479 : Blo 1738570 4401479 := bstep (se 1 (by rfl) ⟨3301109, by rfl⟩ : syracuseStep 4401479 = 6602219) B6602219
theorem B4180639 : Blo 1738570 4180639 := bstep (se 1 (by rfl) ⟨3135479, by rfl⟩ : syracuseStep 4180639 = 6270959) B6270959
theorem B19820051 : Blo 1738570 19820051 := bstep (se 1 (by rfl) ⟨14865038, by rfl⟩ : syracuseStep 19820051 = 29730077) B29730077
theorem B1740543 : Blo 1738570 1740543 := bstep (se 1 (by rfl) ⟨1305407, by rfl⟩ : syracuseStep 1740543 = 2610815) B2610815
theorem B6606623 : Blo 1738570 6606623 := bstep (se 1 (by rfl) ⟨4954967, by rfl⟩ : syracuseStep 6606623 = 9909935) B9909935
theorem B3134803 : Blo 1738570 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B14857931 : Blo 1738570 14857931 := bstep (se 1 (by rfl) ⟨11143448, by rfl⟩ : syracuseStep 14857931 = 22286897) B22286897
theorem B8804051 : Blo 1738570 8804051 := bstep (se 1 (by rfl) ⟨6603038, by rfl⟩ : syracuseStep 8804051 = 13206077) B13206077
theorem B3913631 : Blo 1738570 3913631 := bstep (se 1 (by rfl) ⟨2935223, by rfl⟩ : syracuseStep 3913631 = 5870447) B5870447
theorem B12540071 : Blo 1738570 12540071 := bstep (se 1 (by rfl) ⟨9405053, by rfl⟩ : syracuseStep 12540071 = 18810107) B18810107
theorem B1956559 : Blo 1738570 1956559 := bstep (se 1 (by rfl) ⟨1467419, by rfl⟩ : syracuseStep 1956559 = 2934839) B2934839
theorem B3914729 : Blo 1738570 3914729 := bstep (se 2 (by rfl) ⟨1468023, by rfl⟩ : syracuseStep 3914729 = 2936047) B2936047
theorem B85752989 : Blo 1738570 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B37625057 : Blo 1738570 37625057 := bstep (se 2 (by rfl) ⟨14109396, by rfl⟩ : syracuseStep 37625057 = 28218793) B28218793
theorem B90365543 : Blo 1738570 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B18800423 : Blo 1738570 18800423 := bstep (se 1 (by rfl) ⟨14100317, by rfl⟩ : syracuseStep 18800423 = 28200635) B28200635
theorem B9905287 : Blo 1738570 9905287 := bstep (se 1 (by rfl) ⟨7428965, by rfl⟩ : syracuseStep 9905287 = 14857931) B14857931
theorem B33899867 : Blo 1738570 33899867 := bstep (se 1 (by rfl) ⟨25424900, by rfl⟩ : syracuseStep 33899867 = 50849801) B50849801
theorem B2934319 : Blo 1738570 2934319 := bstep (se 1 (by rfl) ⟨2200739, by rfl⟩ : syracuseStep 2934319 = 4401479) B4401479
theorem B4179737 : Blo 1738570 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B12545351 : Blo 1738570 12545351 := bstep (se 1 (by rfl) ⟨9409013, by rfl⟩ : syracuseStep 12545351 = 18818027) B18818027
theorem B5574185 : Blo 1738570 5574185 := bstep (se 2 (by rfl) ⟨2090319, by rfl⟩ : syracuseStep 5574185 = 4180639) B4180639
theorem B2608745 : Blo 1738570 2608745 := bstep (se 2 (by rfl) ⟨978279, by rfl⟩ : syracuseStep 2608745 = 1956559) B1956559
theorem B8810207 : Blo 1738570 8810207 := bstep (se 1 (by rfl) ⟨6607655, by rfl⟩ : syracuseStep 8810207 = 13215311) B13215311
theorem B5869367 : Blo 1738570 5869367 := bstep (se 1 (by rfl) ⟨4402025, by rfl⟩ : syracuseStep 5869367 = 8804051) B8804051
theorem B2609087 : Blo 1738570 2609087 := bstep (se 1 (by rfl) ⟨1956815, by rfl⟩ : syracuseStep 2609087 = 3913631) B3913631
theorem B8360047 : Blo 1738570 8360047 := bstep (se 1 (by rfl) ⟨6270035, by rfl⟩ : syracuseStep 8360047 = 12540071) B12540071
theorem B2609819 : Blo 1738570 2609819 := bstep (se 1 (by rfl) ⟨1957364, by rfl⟩ : syracuseStep 2609819 = 3914729) B3914729
theorem B57168659 : Blo 1738570 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B4404415 : Blo 1738570 4404415 := bstep (se 1 (by rfl) ⟨3303311, by rfl⟩ : syracuseStep 4404415 = 6606623) B6606623
theorem B5871743 : Blo 1738570 5871743 := bstep (se 1 (by rfl) ⟨4403807, by rfl⟩ : syracuseStep 5871743 = 8807615) B8807615
theorem B25083371 : Blo 1738570 25083371 := bstep (se 1 (by rfl) ⟨18812528, by rfl⟩ : syracuseStep 25083371 = 37625057) B37625057
theorem B13213367 : Blo 1738570 13213367 := bstep (se 1 (by rfl) ⟨9910025, by rfl⟩ : syracuseStep 13213367 = 19820051) B19820051
theorem B60243695 : Blo 1738570 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B12533615 : Blo 1738570 12533615 := bstep (se 1 (by rfl) ⟨9400211, by rfl⟩ : syracuseStep 12533615 = 18800423) B18800423
theorem B2786491 : Blo 1738570 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B13207049 : Blo 1738570 13207049 := bstep (se 2 (by rfl) ⟨4952643, by rfl⟩ : syracuseStep 13207049 = 9905287) B9905287
theorem B16722247 : Blo 1738570 16722247 := bstep (se 1 (by rfl) ⟨12541685, by rfl⟩ : syracuseStep 16722247 = 25083371) B25083371
theorem B1739163 : Blo 1738570 1739163 := bstep (se 1 (by rfl) ⟨1304372, by rfl⟩ : syracuseStep 1739163 = 2608745) B2608745
theorem B8808911 : Blo 1738570 8808911 := bstep (se 1 (by rfl) ⟨6606683, by rfl⟩ : syracuseStep 8808911 = 13213367) B13213367
theorem B1739391 : Blo 1738570 1739391 := bstep (se 1 (by rfl) ⟨1304543, by rfl⟩ : syracuseStep 1739391 = 2609087) B2609087
theorem B1739879 : Blo 1738570 1739879 := bstep (se 1 (by rfl) ⟨1304909, by rfl⟩ : syracuseStep 1739879 = 2609819) B2609819
theorem B38112439 : Blo 1738570 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B3912425 : Blo 1738570 3912425 := bstep (se 2 (by rfl) ⟨1467159, by rfl⟩ : syracuseStep 3912425 = 2934319) B2934319
theorem B3716123 : Blo 1738570 3716123 := bstep (se 1 (by rfl) ⟨2787092, by rfl⟩ : syracuseStep 3716123 = 5574185) B5574185
theorem B40162463 : Blo 1738570 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B3912911 : Blo 1738570 3912911 := bstep (se 1 (by rfl) ⟨2934683, by rfl⟩ : syracuseStep 3912911 = 5869367) B5869367
theorem B11146729 : Blo 1738570 11146729 := bstep (se 2 (by rfl) ⟨4180023, by rfl⟩ : syracuseStep 11146729 = 8360047) B8360047
theorem B22599911 : Blo 1738570 22599911 := bstep (se 1 (by rfl) ⟨16949933, by rfl⟩ : syracuseStep 22599911 = 33899867) B33899867
theorem B3914495 : Blo 1738570 3914495 := bstep (se 1 (by rfl) ⟨2935871, by rfl⟩ : syracuseStep 3914495 = 5871743) B5871743
theorem B5872553 : Blo 1738570 5872553 := bstep (se 2 (by rfl) ⟨2202207, by rfl⟩ : syracuseStep 5872553 = 4404415) B4404415
theorem B8363567 : Blo 1738570 8363567 := bstep (se 1 (by rfl) ⟨6272675, by rfl⟩ : syracuseStep 8363567 = 12545351) B12545351
theorem B5873471 : Blo 1738570 5873471 := bstep (se 1 (by rfl) ⟨4405103, by rfl⟩ : syracuseStep 5873471 = 8810207) B8810207
theorem B8355743 : Blo 1738570 8355743 := bstep (se 1 (by rfl) ⟨6266807, by rfl⟩ : syracuseStep 8355743 = 12533615) B12533615
theorem B50816585 : Blo 1738570 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B14862305 : Blo 1738570 14862305 := bstep (se 2 (by rfl) ⟨5573364, by rfl⟩ : syracuseStep 14862305 = 11146729) B11146729
theorem B2608283 : Blo 1738570 2608283 := bstep (se 1 (by rfl) ⟨1956212, by rfl⟩ : syracuseStep 2608283 = 3912425) B3912425
theorem B26774975 : Blo 1738570 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2608607 : Blo 1738570 2608607 := bstep (se 1 (by rfl) ⟨1956455, by rfl⟩ : syracuseStep 2608607 = 3912911) B3912911
theorem B3715321 : Blo 1738570 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B2609663 : Blo 1738570 2609663 := bstep (se 1 (by rfl) ⟨1957247, by rfl⟩ : syracuseStep 2609663 = 3914495) B3914495
theorem B5575711 : Blo 1738570 5575711 := bstep (se 1 (by rfl) ⟨4181783, by rfl⟩ : syracuseStep 5575711 = 8363567) B8363567
theorem B9909661 : Blo 1738570 9909661 := bstep (se 3 (by rfl) ⟨1858061, by rfl⟩ : syracuseStep 9909661 = 3716123) B3716123
theorem B22296329 : Blo 1738570 22296329 := bstep (se 2 (by rfl) ⟨8361123, by rfl⟩ : syracuseStep 22296329 = 16722247) B16722247
theorem B60266429 : Blo 1738570 60266429 := bstep (se 3 (by rfl) ⟨11299955, by rfl⟩ : syracuseStep 60266429 = 22599911) B22599911
theorem B8804699 : Blo 1738570 8804699 := bstep (se 1 (by rfl) ⟨6603524, by rfl⟩ : syracuseStep 8804699 = 13207049) B13207049
theorem B5872607 : Blo 1738570 5872607 := bstep (se 1 (by rfl) ⟨4404455, by rfl⟩ : syracuseStep 5872607 = 8808911) B8808911
theorem B3915035 : Blo 1738570 3915035 := bstep (se 1 (by rfl) ⟨2936276, by rfl⟩ : syracuseStep 3915035 = 5872553) B5872553
theorem B3915647 : Blo 1738570 3915647 := bstep (se 1 (by rfl) ⟨2936735, by rfl⟩ : syracuseStep 3915647 = 5873471) B5873471
theorem B5570495 : Blo 1738570 5570495 := bstep (se 1 (by rfl) ⟨4177871, by rfl⟩ : syracuseStep 5570495 = 8355743) B8355743
theorem B1738855 : Blo 1738570 1738855 := bstep (se 1 (by rfl) ⟨1304141, by rfl⟩ : syracuseStep 1738855 = 2608283) B2608283
theorem B1739071 : Blo 1738570 1739071 := bstep (se 1 (by rfl) ⟨1304303, by rfl⟩ : syracuseStep 1739071 = 2608607) B2608607
theorem B3713663 : Blo 1738570 3713663 := bstep (se 1 (by rfl) ⟨2785247, by rfl⟩ : syracuseStep 3713663 = 5570495) B5570495
theorem B1739775 : Blo 1738570 1739775 := bstep (se 1 (by rfl) ⟨1304831, by rfl⟩ : syracuseStep 1739775 = 2609663) B2609663
theorem B14864219 : Blo 1738570 14864219 := bstep (se 1 (by rfl) ⟨11148164, by rfl⟩ : syracuseStep 14864219 = 22296329) B22296329
theorem B40177619 : Blo 1738570 40177619 := bstep (se 1 (by rfl) ⟨30133214, by rfl⟩ : syracuseStep 40177619 = 60266429) B60266429
theorem B9908203 : Blo 1738570 9908203 := bstep (se 1 (by rfl) ⟨7431152, by rfl⟩ : syracuseStep 9908203 = 14862305) B14862305
theorem B7434281 : Blo 1738570 7434281 := bstep (se 2 (by rfl) ⟨2787855, by rfl⟩ : syracuseStep 7434281 = 5575711) B5575711
theorem B5869799 : Blo 1738570 5869799 := bstep (se 1 (by rfl) ⟨4402349, by rfl⟩ : syracuseStep 5869799 = 8804699) B8804699
theorem B2610023 : Blo 1738570 2610023 := bstep (se 1 (by rfl) ⟨1957517, by rfl⟩ : syracuseStep 2610023 = 3915035) B3915035
theorem B2610431 : Blo 1738570 2610431 := bstep (se 1 (by rfl) ⟨1957823, by rfl⟩ : syracuseStep 2610431 = 3915647) B3915647
theorem B4953761 : Blo 1738570 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B135510893 : Blo 1738570 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B13212881 : Blo 1738570 13212881 := bstep (se 2 (by rfl) ⟨4954830, by rfl⟩ : syracuseStep 13212881 = 9909661) B9909661
theorem B3915071 : Blo 1738570 3915071 := bstep (se 1 (by rfl) ⟨2936303, by rfl⟩ : syracuseStep 3915071 = 5872607) B5872607
theorem B17849983 : Blo 1738570 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B4956187 : Blo 1738570 4956187 := bstep (se 1 (by rfl) ⟨3717140, by rfl⟩ : syracuseStep 4956187 = 7434281) B7434281
theorem B3302507 : Blo 1738570 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B2475775 : Blo 1738570 2475775 := bstep (se 1 (by rfl) ⟨1856831, by rfl⟩ : syracuseStep 2475775 = 3713663) B3713663
theorem B8808587 : Blo 1738570 8808587 := bstep (se 1 (by rfl) ⟨6606440, by rfl⟩ : syracuseStep 8808587 = 13212881) B13212881
theorem B23799977 : Blo 1738570 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B1740015 : Blo 1738570 1740015 := bstep (se 1 (by rfl) ⟨1305011, by rfl⟩ : syracuseStep 1740015 = 2610023) B2610023
theorem B1740287 : Blo 1738570 1740287 := bstep (se 1 (by rfl) ⟨1305215, by rfl⟩ : syracuseStep 1740287 = 2610431) B2610431
theorem B2610047 : Blo 1738570 2610047 := bstep (se 1 (by rfl) ⟨1957535, by rfl⟩ : syracuseStep 2610047 = 3915071) B3915071
theorem B9909479 : Blo 1738570 9909479 := bstep (se 1 (by rfl) ⟨7432109, by rfl⟩ : syracuseStep 9909479 = 14864219) B14864219
theorem B26785079 : Blo 1738570 26785079 := bstep (se 1 (by rfl) ⟨20088809, by rfl⟩ : syracuseStep 26785079 = 40177619) B40177619
theorem B13210937 : Blo 1738570 13210937 := bstep (se 2 (by rfl) ⟨4954101, by rfl⟩ : syracuseStep 13210937 = 9908203) B9908203
theorem B3913199 : Blo 1738570 3913199 := bstep (se 1 (by rfl) ⟨2934899, by rfl⟩ : syracuseStep 3913199 = 5869799) B5869799
theorem B90340595 : Blo 1738570 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B8807291 : Blo 1738570 8807291 := bstep (se 1 (by rfl) ⟨6605468, by rfl⟩ : syracuseStep 8807291 = 13210937) B13210937
theorem B1740031 : Blo 1738570 1740031 := bstep (se 1 (by rfl) ⟨1305023, by rfl⟩ : syracuseStep 1740031 = 2610047) B2610047
theorem B6606319 : Blo 1738570 6606319 := bstep (se 1 (by rfl) ⟨4954739, by rfl⟩ : syracuseStep 6606319 = 9909479) B9909479
theorem B2608799 : Blo 1738570 2608799 := bstep (se 1 (by rfl) ⟨1956599, by rfl⟩ : syracuseStep 2608799 = 3913199) B3913199
theorem B6608249 : Blo 1738570 6608249 := bstep (se 2 (by rfl) ⟨2478093, by rfl⟩ : syracuseStep 6608249 = 4956187) B4956187
theorem B2201671 : Blo 1738570 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B17856719 : Blo 1738570 17856719 := bstep (se 1 (by rfl) ⟨13392539, by rfl⟩ : syracuseStep 17856719 = 26785079) B26785079
theorem B13204133 : Blo 1738570 13204133 := bstep (se 4 (by rfl) ⟨1237887, by rfl⟩ : syracuseStep 13204133 = 2475775) B2475775
theorem B5872391 : Blo 1738570 5872391 := bstep (se 1 (by rfl) ⟨4404293, by rfl⟩ : syracuseStep 5872391 = 8808587) B8808587
theorem B15866651 : Blo 1738570 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B60227063 : Blo 1738570 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B11904479 : Blo 1738570 11904479 := bstep (se 1 (by rfl) ⟨8928359, by rfl⟩ : syracuseStep 11904479 = 17856719) B17856719
theorem B8808425 : Blo 1738570 8808425 := bstep (se 2 (by rfl) ⟨3303159, by rfl⟩ : syracuseStep 8808425 = 6606319) B6606319
theorem B40151375 : Blo 1738570 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B1739199 : Blo 1738570 1739199 := bstep (se 1 (by rfl) ⟨1304399, by rfl⟩ : syracuseStep 1739199 = 2608799) B2608799
theorem B2935561 : Blo 1738570 2935561 := bstep (se 2 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 2935561 = 2201671) B2201671
theorem B8802755 : Blo 1738570 8802755 := bstep (se 1 (by rfl) ⟨6602066, by rfl⟩ : syracuseStep 8802755 = 13204133) B13204133
theorem B5871527 : Blo 1738570 5871527 := bstep (se 1 (by rfl) ⟨4403645, by rfl⟩ : syracuseStep 5871527 = 8807291) B8807291
theorem B4405499 : Blo 1738570 4405499 := bstep (se 1 (by rfl) ⟨3304124, by rfl⟩ : syracuseStep 4405499 = 6608249) B6608249
theorem B3914927 : Blo 1738570 3914927 := bstep (se 1 (by rfl) ⟨2936195, by rfl⟩ : syracuseStep 3914927 = 5872391) B5872391
theorem B42311069 : Blo 1738570 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B28207379 : Blo 1738570 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B5868503 : Blo 1738570 5868503 := bstep (se 1 (by rfl) ⟨4401377, by rfl⟩ : syracuseStep 5868503 = 8802755) B8802755
theorem B2936999 : Blo 1738570 2936999 := bstep (se 1 (by rfl) ⟨2202749, by rfl⟩ : syracuseStep 2936999 = 4405499) B4405499
theorem B26767583 : Blo 1738570 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B2609951 : Blo 1738570 2609951 := bstep (se 1 (by rfl) ⟨1957463, by rfl⟩ : syracuseStep 2609951 = 3914927) B3914927
theorem B7936319 : Blo 1738570 7936319 := bstep (se 1 (by rfl) ⟨5952239, by rfl⟩ : syracuseStep 7936319 = 11904479) B11904479
theorem B3914081 : Blo 1738570 3914081 := bstep (se 2 (by rfl) ⟨1467780, by rfl⟩ : syracuseStep 3914081 = 2935561) B2935561
theorem B3914351 : Blo 1738570 3914351 := bstep (se 1 (by rfl) ⟨2935763, by rfl⟩ : syracuseStep 3914351 = 5871527) B5871527
theorem B5872283 : Blo 1738570 5872283 := bstep (se 1 (by rfl) ⟨4404212, by rfl⟩ : syracuseStep 5872283 = 8808425) B8808425
theorem B1957999 : Blo 1738570 1957999 := bstep (se 1 (by rfl) ⟨1468499, by rfl⟩ : syracuseStep 1957999 = 2936999) B2936999
theorem B17845055 : Blo 1738570 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B1739967 : Blo 1738570 1739967 := bstep (se 1 (by rfl) ⟨1304975, by rfl⟩ : syracuseStep 1739967 = 2609951) B2609951
theorem B21163517 : Blo 1738570 21163517 := bstep (se 3 (by rfl) ⟨3968159, by rfl⟩ : syracuseStep 21163517 = 7936319) B7936319
theorem B18804919 : Blo 1738570 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B2609387 : Blo 1738570 2609387 := bstep (se 1 (by rfl) ⟨1957040, by rfl⟩ : syracuseStep 2609387 = 3914081) B3914081
theorem B2609567 : Blo 1738570 2609567 := bstep (se 1 (by rfl) ⟨1957175, by rfl⟩ : syracuseStep 2609567 = 3914351) B3914351
theorem B3912335 : Blo 1738570 3912335 := bstep (se 1 (by rfl) ⟨2934251, by rfl⟩ : syracuseStep 3912335 = 5868503) B5868503
theorem B3914855 : Blo 1738570 3914855 := bstep (se 1 (by rfl) ⟨2936141, by rfl⟩ : syracuseStep 3914855 = 5872283) B5872283
theorem B11896703 : Blo 1738570 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B14109011 : Blo 1738570 14109011 := bstep (se 1 (by rfl) ⟨10581758, by rfl⟩ : syracuseStep 14109011 = 21163517) B21163517
theorem B1739591 : Blo 1738570 1739591 := bstep (se 1 (by rfl) ⟨1304693, by rfl⟩ : syracuseStep 1739591 = 2609387) B2609387
theorem B1739711 : Blo 1738570 1739711 := bstep (se 1 (by rfl) ⟨1304783, by rfl⟩ : syracuseStep 1739711 = 2609567) B2609567
theorem B2608223 : Blo 1738570 2608223 := bstep (se 1 (by rfl) ⟨1956167, by rfl⟩ : syracuseStep 2608223 = 3912335) B3912335
theorem B2609903 : Blo 1738570 2609903 := bstep (se 1 (by rfl) ⟨1957427, by rfl⟩ : syracuseStep 2609903 = 3914855) B3914855
theorem B2610665 : Blo 1738570 2610665 := bstep (se 2 (by rfl) ⟨978999, by rfl⟩ : syracuseStep 2610665 = 1957999) B1957999
theorem B25073225 : Blo 1738570 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B7931135 : Blo 1738570 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B9406007 : Blo 1738570 9406007 := bstep (se 1 (by rfl) ⟨7054505, by rfl⟩ : syracuseStep 9406007 = 14109011) B14109011
theorem B1738815 : Blo 1738570 1738815 := bstep (se 1 (by rfl) ⟨1304111, by rfl⟩ : syracuseStep 1738815 = 2608223) B2608223
theorem B1739935 : Blo 1738570 1739935 := bstep (se 1 (by rfl) ⟨1304951, by rfl⟩ : syracuseStep 1739935 = 2609903) B2609903
theorem B1740443 : Blo 1738570 1740443 := bstep (se 1 (by rfl) ⟨1305332, by rfl⟩ : syracuseStep 1740443 = 2610665) B2610665
theorem B16715483 : Blo 1738570 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B11143655 : Blo 1738570 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B5287423 : Blo 1738570 5287423 := bstep (se 1 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 5287423 = 7931135) B7931135
theorem B6270671 : Blo 1738570 6270671 := bstep (se 1 (by rfl) ⟨4703003, by rfl⟩ : syracuseStep 6270671 = 9406007) B9406007
theorem B4180447 : Blo 1738570 4180447 := bstep (se 1 (by rfl) ⟨3135335, by rfl⟩ : syracuseStep 4180447 = 6270671) B6270671
theorem B7049897 : Blo 1738570 7049897 := bstep (se 2 (by rfl) ⟨2643711, by rfl⟩ : syracuseStep 7049897 = 5287423) B5287423
theorem B7429103 : Blo 1738570 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B5573929 : Blo 1738570 5573929 := bstep (se 2 (by rfl) ⟨2090223, by rfl⟩ : syracuseStep 5573929 = 4180447) B4180447
theorem B75198901 : Blo 1738570 75198901 := bstep (se 5 (by rfl) ⟨3524948, by rfl⟩ : syracuseStep 75198901 = 7049897) B7049897
theorem B4952735 : Blo 1738570 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B3301823 : Blo 1738570 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B7431905 : Blo 1738570 7431905 := bstep (se 2 (by rfl) ⟨2786964, by rfl⟩ : syracuseStep 7431905 = 5573929) B5573929
theorem B100265201 : Blo 1738570 100265201 := bstep (se 2 (by rfl) ⟨37599450, by rfl⟩ : syracuseStep 100265201 = 75198901) B75198901
theorem B66843467 : Blo 1738570 66843467 := bstep (se 1 (by rfl) ⟨50132600, by rfl⟩ : syracuseStep 66843467 = 100265201) B100265201
theorem B4954603 : Blo 1738570 4954603 := bstep (se 1 (by rfl) ⟨3715952, by rfl⟩ : syracuseStep 4954603 = 7431905) B7431905
theorem B8804861 : Blo 1738570 8804861 := bstep (se 3 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 8804861 = 3301823) B3301823
theorem B6606137 : Blo 1738570 6606137 := bstep (se 2 (by rfl) ⟨2477301, by rfl⟩ : syracuseStep 6606137 = 4954603) B4954603
theorem B5869907 : Blo 1738570 5869907 := bstep (se 1 (by rfl) ⟨4402430, by rfl⟩ : syracuseStep 5869907 = 8804861) B8804861
theorem B44562311 : Blo 1738570 44562311 := bstep (se 1 (by rfl) ⟨33421733, by rfl⟩ : syracuseStep 44562311 = 66843467) B66843467
theorem B29708207 : Blo 1738570 29708207 := bstep (se 1 (by rfl) ⟨22281155, by rfl⟩ : syracuseStep 29708207 = 44562311) B44562311
theorem B4404091 : Blo 1738570 4404091 := bstep (se 1 (by rfl) ⟨3303068, by rfl⟩ : syracuseStep 4404091 = 6606137) B6606137
theorem B3913271 : Blo 1738570 3913271 := bstep (se 1 (by rfl) ⟨2934953, by rfl⟩ : syracuseStep 3913271 = 5869907) B5869907
theorem B2608847 : Blo 1738570 2608847 := bstep (se 1 (by rfl) ⟨1956635, by rfl⟩ : syracuseStep 2608847 = 3913271) B3913271
theorem B19805471 : Blo 1738570 19805471 := bstep (se 1 (by rfl) ⟨14854103, by rfl⟩ : syracuseStep 19805471 = 29708207) B29708207
theorem B5872121 : Blo 1738570 5872121 := bstep (se 2 (by rfl) ⟨2202045, by rfl⟩ : syracuseStep 5872121 = 4404091) B4404091
theorem B1739231 : Blo 1738570 1739231 := bstep (se 1 (by rfl) ⟨1304423, by rfl⟩ : syracuseStep 1739231 = 2608847) B2608847
theorem B13203647 : Blo 1738570 13203647 := bstep (se 1 (by rfl) ⟨9902735, by rfl⟩ : syracuseStep 13203647 = 19805471) B19805471
theorem B3914747 : Blo 1738570 3914747 := bstep (se 1 (by rfl) ⟨2936060, by rfl⟩ : syracuseStep 3914747 = 5872121) B5872121
theorem B8802431 : Blo 1738570 8802431 := bstep (se 1 (by rfl) ⟨6601823, by rfl⟩ : syracuseStep 8802431 = 13203647) B13203647
theorem B2609831 : Blo 1738570 2609831 := bstep (se 1 (by rfl) ⟨1957373, by rfl⟩ : syracuseStep 2609831 = 3914747) B3914747
theorem B5868287 : Blo 1738570 5868287 := bstep (se 1 (by rfl) ⟨4401215, by rfl⟩ : syracuseStep 5868287 = 8802431) B8802431
theorem B1739887 : Blo 1738570 1739887 := bstep (se 1 (by rfl) ⟨1304915, by rfl⟩ : syracuseStep 1739887 = 2609831) B2609831
theorem B3912191 : Blo 1738570 3912191 := bstep (se 1 (by rfl) ⟨2934143, by rfl⟩ : syracuseStep 3912191 = 5868287) B5868287
theorem B2608127 : Blo 1738570 2608127 := bstep (se 1 (by rfl) ⟨1956095, by rfl⟩ : syracuseStep 2608127 = 3912191) B3912191
theorem B1738751 : Blo 1738570 1738751 := bstep (se 1 (by rfl) ⟨1304063, by rfl⟩ : syracuseStep 1738751 = 2608127) B2608127

theorem C0 (j : ℕ) (h1 : 434642 ≤ j) (h2 : j ≤ 435141) : Blo 1738570 (4 * j + 3) := by
  interval_cases j
  · exact B1738571
  · exact B1738575
  · exact B1738579
  · exact B1738583
  · exact B1738587
  · exact B1738591
  · exact B1738595
  · exact B1738599
  · exact B1738603
  · exact B1738607
  · exact B1738611
  · exact B1738615
  · exact B1738619
  · exact B1738623
  · exact B1738627
  · exact B1738631
  · exact B1738635
  · exact B1738639
  · exact B1738643
  · exact B1738647
  · exact B1738651
  · exact B1738655
  · exact B1738659
  · exact B1738663
  · exact B1738667
  · exact B1738671
  · exact B1738675
  · exact B1738679
  · exact B1738683
  · exact B1738687
  · exact B1738691
  · exact B1738695
  · exact B1738699
  · exact B1738703
  · exact B1738707
  · exact B1738711
  · exact B1738715
  · exact B1738719
  · exact B1738723
  · exact B1738727
  · exact B1738731
  · exact B1738735
  · exact B1738739
  · exact B1738743
  · exact B1738747
  · exact B1738751
  · exact B1738755
  · exact B1738759
  · exact B1738763
  · exact B1738767
  · exact B1738771
  · exact B1738775
  · exact B1738779
  · exact B1738783
  · exact B1738787
  · exact B1738791
  · exact B1738795
  · exact B1738799
  · exact B1738803
  · exact B1738807
  · exact B1738811
  · exact B1738815
  · exact B1738819
  · exact B1738823
  · exact B1738827
  · exact B1738831
  · exact B1738835
  · exact B1738839
  · exact B1738843
  · exact B1738847
  · exact B1738851
  · exact B1738855
  · exact B1738859
  · exact B1738863
  · exact B1738867
  · exact B1738871
  · exact B1738875
  · exact B1738879
  · exact B1738883
  · exact B1738887
  · exact B1738891
  · exact B1738895
  · exact B1738899
  · exact B1738903
  · exact B1738907
  · exact B1738911
  · exact B1738915
  · exact B1738919
  · exact B1738923
  · exact B1738927
  · exact B1738931
  · exact B1738935
  · exact B1738939
  · exact B1738943
  · exact B1738947
  · exact B1738951
  · exact B1738955
  · exact B1738959
  · exact B1738963
  · exact B1738967
  · exact B1738971
  · exact B1738975
  · exact B1738979
  · exact B1738983
  · exact B1738987
  · exact B1738991
  · exact B1738995
  · exact B1738999
  · exact B1739003
  · exact B1739007
  · exact B1739011
  · exact B1739015
  · exact B1739019
  · exact B1739023
  · exact B1739027
  · exact B1739031
  · exact B1739035
  · exact B1739039
  · exact B1739043
  · exact B1739047
  · exact B1739051
  · exact B1739055
  · exact B1739059
  · exact B1739063
  · exact B1739067
  · exact B1739071
  · exact B1739075
  · exact B1739079
  · exact B1739083
  · exact B1739087
  · exact B1739091
  · exact B1739095
  · exact B1739099
  · exact B1739103
  · exact B1739107
  · exact B1739111
  · exact B1739115
  · exact B1739119
  · exact B1739123
  · exact B1739127
  · exact B1739131
  · exact B1739135
  · exact B1739139
  · exact B1739143
  · exact B1739147
  · exact B1739151
  · exact B1739155
  · exact B1739159
  · exact B1739163
  · exact B1739167
  · exact B1739171
  · exact B1739175
  · exact B1739179
  · exact B1739183
  · exact B1739187
  · exact B1739191
  · exact B1739195
  · exact B1739199
  · exact B1739203
  · exact B1739207
  · exact B1739211
  · exact B1739215
  · exact B1739219
  · exact B1739223
  · exact B1739227
  · exact B1739231
  · exact B1739235
  · exact B1739239
  · exact B1739243
  · exact B1739247
  · exact B1739251
  · exact B1739255
  · exact B1739259
  · exact B1739263
  · exact B1739267
  · exact B1739271
  · exact B1739275
  · exact B1739279
  · exact B1739283
  · exact B1739287
  · exact B1739291
  · exact B1739295
  · exact B1739299
  · exact B1739303
  · exact B1739307
  · exact B1739311
  · exact B1739315
  · exact B1739319
  · exact B1739323
  · exact B1739327
  · exact B1739331
  · exact B1739335
  · exact B1739339
  · exact B1739343
  · exact B1739347
  · exact B1739351
  · exact B1739355
  · exact B1739359
  · exact B1739363
  · exact B1739367
  · exact B1739371
  · exact B1739375
  · exact B1739379
  · exact B1739383
  · exact B1739387
  · exact B1739391
  · exact B1739395
  · exact B1739399
  · exact B1739403
  · exact B1739407
  · exact B1739411
  · exact B1739415
  · exact B1739419
  · exact B1739423
  · exact B1739427
  · exact B1739431
  · exact B1739435
  · exact B1739439
  · exact B1739443
  · exact B1739447
  · exact B1739451
  · exact B1739455
  · exact B1739459
  · exact B1739463
  · exact B1739467
  · exact B1739471
  · exact B1739475
  · exact B1739479
  · exact B1739483
  · exact B1739487
  · exact B1739491
  · exact B1739495
  · exact B1739499
  · exact B1739503
  · exact B1739507
  · exact B1739511
  · exact B1739515
  · exact B1739519
  · exact B1739523
  · exact B1739527
  · exact B1739531
  · exact B1739535
  · exact B1739539
  · exact B1739543
  · exact B1739547
  · exact B1739551
  · exact B1739555
  · exact B1739559
  · exact B1739563
  · exact B1739567
  · exact B1739571
  · exact B1739575
  · exact B1739579
  · exact B1739583
  · exact B1739587
  · exact B1739591
  · exact B1739595
  · exact B1739599
  · exact B1739603
  · exact B1739607
  · exact B1739611
  · exact B1739615
  · exact B1739619
  · exact B1739623
  · exact B1739627
  · exact B1739631
  · exact B1739635
  · exact B1739639
  · exact B1739643
  · exact B1739647
  · exact B1739651
  · exact B1739655
  · exact B1739659
  · exact B1739663
  · exact B1739667
  · exact B1739671
  · exact B1739675
  · exact B1739679
  · exact B1739683
  · exact B1739687
  · exact B1739691
  · exact B1739695
  · exact B1739699
  · exact B1739703
  · exact B1739707
  · exact B1739711
  · exact B1739715
  · exact B1739719
  · exact B1739723
  · exact B1739727
  · exact B1739731
  · exact B1739735
  · exact B1739739
  · exact B1739743
  · exact B1739747
  · exact B1739751
  · exact B1739755
  · exact B1739759
  · exact B1739763
  · exact B1739767
  · exact B1739771
  · exact B1739775
  · exact B1739779
  · exact B1739783
  · exact B1739787
  · exact B1739791
  · exact B1739795
  · exact B1739799
  · exact B1739803
  · exact B1739807
  · exact B1739811
  · exact B1739815
  · exact B1739819
  · exact B1739823
  · exact B1739827
  · exact B1739831
  · exact B1739835
  · exact B1739839
  · exact B1739843
  · exact B1739847
  · exact B1739851
  · exact B1739855
  · exact B1739859
  · exact B1739863
  · exact B1739867
  · exact B1739871
  · exact B1739875
  · exact B1739879
  · exact B1739883
  · exact B1739887
  · exact B1739891
  · exact B1739895
  · exact B1739899
  · exact B1739903
  · exact B1739907
  · exact B1739911
  · exact B1739915
  · exact B1739919
  · exact B1739923
  · exact B1739927
  · exact B1739931
  · exact B1739935
  · exact B1739939
  · exact B1739943
  · exact B1739947
  · exact B1739951
  · exact B1739955
  · exact B1739959
  · exact B1739963
  · exact B1739967
  · exact B1739971
  · exact B1739975
  · exact B1739979
  · exact B1739983
  · exact B1739987
  · exact B1739991
  · exact B1739995
  · exact B1739999
  · exact B1740003
  · exact B1740007
  · exact B1740011
  · exact B1740015
  · exact B1740019
  · exact B1740023
  · exact B1740027
  · exact B1740031
  · exact B1740035
  · exact B1740039
  · exact B1740043
  · exact B1740047
  · exact B1740051
  · exact B1740055
  · exact B1740059
  · exact B1740063
  · exact B1740067
  · exact B1740071
  · exact B1740075
  · exact B1740079
  · exact B1740083
  · exact B1740087
  · exact B1740091
  · exact B1740095
  · exact B1740099
  · exact B1740103
  · exact B1740107
  · exact B1740111
  · exact B1740115
  · exact B1740119
  · exact B1740123
  · exact B1740127
  · exact B1740131
  · exact B1740135
  · exact B1740139
  · exact B1740143
  · exact B1740147
  · exact B1740151
  · exact B1740155
  · exact B1740159
  · exact B1740163
  · exact B1740167
  · exact B1740171
  · exact B1740175
  · exact B1740179
  · exact B1740183
  · exact B1740187
  · exact B1740191
  · exact B1740195
  · exact B1740199
  · exact B1740203
  · exact B1740207
  · exact B1740211
  · exact B1740215
  · exact B1740219
  · exact B1740223
  · exact B1740227
  · exact B1740231
  · exact B1740235
  · exact B1740239
  · exact B1740243
  · exact B1740247
  · exact B1740251
  · exact B1740255
  · exact B1740259
  · exact B1740263
  · exact B1740267
  · exact B1740271
  · exact B1740275
  · exact B1740279
  · exact B1740283
  · exact B1740287
  · exact B1740291
  · exact B1740295
  · exact B1740299
  · exact B1740303
  · exact B1740307
  · exact B1740311
  · exact B1740315
  · exact B1740319
  · exact B1740323
  · exact B1740327
  · exact B1740331
  · exact B1740335
  · exact B1740339
  · exact B1740343
  · exact B1740347
  · exact B1740351
  · exact B1740355
  · exact B1740359
  · exact B1740363
  · exact B1740367
  · exact B1740371
  · exact B1740375
  · exact B1740379
  · exact B1740383
  · exact B1740387
  · exact B1740391
  · exact B1740395
  · exact B1740399
  · exact B1740403
  · exact B1740407
  · exact B1740411
  · exact B1740415
  · exact B1740419
  · exact B1740423
  · exact B1740427
  · exact B1740431
  · exact B1740435
  · exact B1740439
  · exact B1740443
  · exact B1740447
  · exact B1740451
  · exact B1740455
  · exact B1740459
  · exact B1740463
  · exact B1740467
  · exact B1740471
  · exact B1740475
  · exact B1740479
  · exact B1740483
  · exact B1740487
  · exact B1740491
  · exact B1740495
  · exact B1740499
  · exact B1740503
  · exact B1740507
  · exact B1740511
  · exact B1740515
  · exact B1740519
  · exact B1740523
  · exact B1740527
  · exact B1740531
  · exact B1740535
  · exact B1740539
  · exact B1740543
  · exact B1740547
  · exact B1740551
  · exact B1740555
  · exact B1740559
  · exact B1740563
  · exact B1740567

theorem solution (m : ℕ) (hlo : 1738570 ≤ m) (hhi : m ≤ 1740570) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 434642 ≤ j := by omega
    have hj2 : j ≤ 435141 := by omega
    have hb : Blo 1738570 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
