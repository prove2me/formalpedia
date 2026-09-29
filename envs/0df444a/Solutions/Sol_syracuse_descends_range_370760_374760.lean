-- Prove2me | solution 1 for syracuse_descends_range_370760_374760
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:40.873326+00:00
-- url     : https://prove2.me/submissions/14cb711c-df20-4449-9972-46621979e9f0

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


theorem B557069 : Blo 370760 557069 := bbase (se 3 (by rfl) ⟨104450, by rfl⟩ : syracuseStep 557069 = 208901) (by norm_num)
theorem B557093 : Blo 370760 557093 := bbase (se 4 (by rfl) ⟨52227, by rfl⟩ : syracuseStep 557093 = 104455) (by norm_num)
theorem B557117 : Blo 370760 557117 := bbase (se 3 (by rfl) ⟨104459, by rfl⟩ : syracuseStep 557117 = 208919) (by norm_num)
theorem B557141 : Blo 370760 557141 := bbase (se 8 (by rfl) ⟨3264, by rfl⟩ : syracuseStep 557141 = 6529) (by norm_num)
theorem B557165 : Blo 370760 557165 := bbase (se 3 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 557165 = 208937) (by norm_num)
theorem B557189 : Blo 370760 557189 := bbase (se 4 (by rfl) ⟨52236, by rfl⟩ : syracuseStep 557189 = 104473) (by norm_num)
theorem B557213 : Blo 370760 557213 := bbase (se 3 (by rfl) ⟨104477, by rfl⟩ : syracuseStep 557213 = 208955) (by norm_num)
theorem B557237 : Blo 370760 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B557261 : Blo 370760 557261 := bbase (se 3 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 557261 = 208973) (by norm_num)
theorem B557285 : Blo 370760 557285 := bbase (se 4 (by rfl) ⟨52245, by rfl⟩ : syracuseStep 557285 = 104491) (by norm_num)
theorem B557309 : Blo 370760 557309 := bbase (se 3 (by rfl) ⟨104495, by rfl⟩ : syracuseStep 557309 = 208991) (by norm_num)
theorem B557333 : Blo 370760 557333 := bbase (se 6 (by rfl) ⟨13062, by rfl⟩ : syracuseStep 557333 = 26125) (by norm_num)
theorem B557357 : Blo 370760 557357 := bbase (se 3 (by rfl) ⟨104504, by rfl⟩ : syracuseStep 557357 = 209009) (by norm_num)
theorem B557381 : Blo 370760 557381 := bbase (se 4 (by rfl) ⟨52254, by rfl⟩ : syracuseStep 557381 = 104509) (by norm_num)
theorem B557405 : Blo 370760 557405 := bbase (se 3 (by rfl) ⟨104513, by rfl⟩ : syracuseStep 557405 = 209027) (by norm_num)
theorem B557429 : Blo 370760 557429 := bbase (se 5 (by rfl) ⟨26129, by rfl⟩ : syracuseStep 557429 = 52259) (by norm_num)
theorem B557453 : Blo 370760 557453 := bbase (se 3 (by rfl) ⟨104522, by rfl⟩ : syracuseStep 557453 = 209045) (by norm_num)
theorem B557477 : Blo 370760 557477 := bbase (se 4 (by rfl) ⟨52263, by rfl⟩ : syracuseStep 557477 = 104527) (by norm_num)
theorem B557501 : Blo 370760 557501 := bbase (se 3 (by rfl) ⟨104531, by rfl⟩ : syracuseStep 557501 = 209063) (by norm_num)
theorem B557525 : Blo 370760 557525 := bbase (se 7 (by rfl) ⟨6533, by rfl⟩ : syracuseStep 557525 = 13067) (by norm_num)
theorem B557549 : Blo 370760 557549 := bbase (se 3 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 557549 = 209081) (by norm_num)
theorem B557573 : Blo 370760 557573 := bbase (se 4 (by rfl) ⟨52272, by rfl⟩ : syracuseStep 557573 = 104545) (by norm_num)
theorem B557597 : Blo 370760 557597 := bbase (se 3 (by rfl) ⟨104549, by rfl⟩ : syracuseStep 557597 = 209099) (by norm_num)
theorem B557621 : Blo 370760 557621 := bbase (se 5 (by rfl) ⟨26138, by rfl⟩ : syracuseStep 557621 = 52277) (by norm_num)
theorem B557645 : Blo 370760 557645 := bbase (se 3 (by rfl) ⟨104558, by rfl⟩ : syracuseStep 557645 = 209117) (by norm_num)
theorem B557669 : Blo 370760 557669 := bbase (se 4 (by rfl) ⟨52281, by rfl⟩ : syracuseStep 557669 = 104563) (by norm_num)
theorem B557693 : Blo 370760 557693 := bbase (se 3 (by rfl) ⟨104567, by rfl⟩ : syracuseStep 557693 = 209135) (by norm_num)
theorem B557717 : Blo 370760 557717 := bbase (se 6 (by rfl) ⟨13071, by rfl⟩ : syracuseStep 557717 = 26143) (by norm_num)
theorem B557741 : Blo 370760 557741 := bbase (se 3 (by rfl) ⟨104576, by rfl⟩ : syracuseStep 557741 = 209153) (by norm_num)
theorem B557765 : Blo 370760 557765 := bbase (se 4 (by rfl) ⟨52290, by rfl⟩ : syracuseStep 557765 = 104581) (by norm_num)
theorem B557789 : Blo 370760 557789 := bbase (se 3 (by rfl) ⟨104585, by rfl⟩ : syracuseStep 557789 = 209171) (by norm_num)
theorem B557813 : Blo 370760 557813 := bbase (se 5 (by rfl) ⟨26147, by rfl⟩ : syracuseStep 557813 = 52295) (by norm_num)
theorem B557837 : Blo 370760 557837 := bbase (se 3 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 557837 = 209189) (by norm_num)
theorem B557861 : Blo 370760 557861 := bbase (se 4 (by rfl) ⟨52299, by rfl⟩ : syracuseStep 557861 = 104599) (by norm_num)
theorem B557885 : Blo 370760 557885 := bbase (se 3 (by rfl) ⟨104603, by rfl⟩ : syracuseStep 557885 = 209207) (by norm_num)
theorem B557909 : Blo 370760 557909 := bbase (se 9 (by rfl) ⟨1634, by rfl⟩ : syracuseStep 557909 = 3269) (by norm_num)
theorem B557933 : Blo 370760 557933 := bbase (se 3 (by rfl) ⟨104612, by rfl⟩ : syracuseStep 557933 = 209225) (by norm_num)
theorem B557957 : Blo 370760 557957 := bbase (se 4 (by rfl) ⟨52308, by rfl⟩ : syracuseStep 557957 = 104617) (by norm_num)
theorem B557981 : Blo 370760 557981 := bbase (se 3 (by rfl) ⟨104621, by rfl⟩ : syracuseStep 557981 = 209243) (by norm_num)
theorem B558005 : Blo 370760 558005 := bbase (se 5 (by rfl) ⟨26156, by rfl⟩ : syracuseStep 558005 = 52313) (by norm_num)
theorem B558029 : Blo 370760 558029 := bbase (se 3 (by rfl) ⟨104630, by rfl⟩ : syracuseStep 558029 = 209261) (by norm_num)
theorem B558053 : Blo 370760 558053 := bbase (se 4 (by rfl) ⟨52317, by rfl⟩ : syracuseStep 558053 = 104635) (by norm_num)
theorem B558077 : Blo 370760 558077 := bbase (se 3 (by rfl) ⟨104639, by rfl⟩ : syracuseStep 558077 = 209279) (by norm_num)
theorem B558101 : Blo 370760 558101 := bbase (se 6 (by rfl) ⟨13080, by rfl⟩ : syracuseStep 558101 = 26161) (by norm_num)
theorem B558125 : Blo 370760 558125 := bbase (se 3 (by rfl) ⟨104648, by rfl⟩ : syracuseStep 558125 = 209297) (by norm_num)
theorem B558149 : Blo 370760 558149 := bbase (se 4 (by rfl) ⟨52326, by rfl⟩ : syracuseStep 558149 = 104653) (by norm_num)
theorem B558173 : Blo 370760 558173 := bbase (se 3 (by rfl) ⟨104657, by rfl⟩ : syracuseStep 558173 = 209315) (by norm_num)
theorem B558197 : Blo 370760 558197 := bbase (se 5 (by rfl) ⟨26165, by rfl⟩ : syracuseStep 558197 = 52331) (by norm_num)
theorem B558221 : Blo 370760 558221 := bbase (se 3 (by rfl) ⟨104666, by rfl⟩ : syracuseStep 558221 = 209333) (by norm_num)
theorem B558245 : Blo 370760 558245 := bbase (se 4 (by rfl) ⟨52335, by rfl⟩ : syracuseStep 558245 = 104671) (by norm_num)
theorem B558269 : Blo 370760 558269 := bbase (se 3 (by rfl) ⟨104675, by rfl⟩ : syracuseStep 558269 = 209351) (by norm_num)
theorem B2819285 : Blo 370760 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B558293 : Blo 370760 558293 := bbase (se 7 (by rfl) ⟨6542, by rfl⟩ : syracuseStep 558293 = 13085) (by norm_num)
theorem B951517 : Blo 370760 951517 := bbase (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) (by norm_num)
theorem B558317 : Blo 370760 558317 := bbase (se 3 (by rfl) ⟨104684, by rfl⟩ : syracuseStep 558317 = 209369) (by norm_num)
theorem B558341 : Blo 370760 558341 := bbase (se 4 (by rfl) ⟨52344, by rfl⟩ : syracuseStep 558341 = 104689) (by norm_num)
theorem B558365 : Blo 370760 558365 := bbase (se 3 (by rfl) ⟨104693, by rfl⟩ : syracuseStep 558365 = 209387) (by norm_num)
theorem B558389 : Blo 370760 558389 := bbase (se 5 (by rfl) ⟨26174, by rfl⟩ : syracuseStep 558389 = 52349) (by norm_num)
theorem B558413 : Blo 370760 558413 := bbase (se 3 (by rfl) ⟨104702, by rfl⟩ : syracuseStep 558413 = 209405) (by norm_num)
theorem B558437 : Blo 370760 558437 := bbase (se 4 (by rfl) ⟨52353, by rfl⟩ : syracuseStep 558437 = 104707) (by norm_num)
theorem B558461 : Blo 370760 558461 := bbase (se 3 (by rfl) ⟨104711, by rfl⟩ : syracuseStep 558461 = 209423) (by norm_num)
theorem B755077 : Blo 370760 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B558485 : Blo 370760 558485 := bbase (se 6 (by rfl) ⟨13089, by rfl⟩ : syracuseStep 558485 = 26179) (by norm_num)
theorem B558509 : Blo 370760 558509 := bbase (se 3 (by rfl) ⟨104720, by rfl⟩ : syracuseStep 558509 = 209441) (by norm_num)
theorem B558533 : Blo 370760 558533 := bbase (se 4 (by rfl) ⟨52362, by rfl⟩ : syracuseStep 558533 = 104725) (by norm_num)
theorem B558557 : Blo 370760 558557 := bbase (se 3 (by rfl) ⟨104729, by rfl⟩ : syracuseStep 558557 = 209459) (by norm_num)
theorem B558581 : Blo 370760 558581 := bbase (se 5 (by rfl) ⟨26183, by rfl⟩ : syracuseStep 558581 = 52367) (by norm_num)
theorem B558605 : Blo 370760 558605 := bbase (se 3 (by rfl) ⟨104738, by rfl⟩ : syracuseStep 558605 = 209477) (by norm_num)
theorem B558629 : Blo 370760 558629 := bbase (se 4 (by rfl) ⟨52371, by rfl⟩ : syracuseStep 558629 = 104743) (by norm_num)
theorem B558653 : Blo 370760 558653 := bbase (se 3 (by rfl) ⟨104747, by rfl⟩ : syracuseStep 558653 = 209495) (by norm_num)
theorem B558677 : Blo 370760 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B558701 : Blo 370760 558701 := bbase (se 3 (by rfl) ⟨104756, by rfl⟩ : syracuseStep 558701 = 209513) (by norm_num)
theorem B558725 : Blo 370760 558725 := bbase (se 4 (by rfl) ⟨52380, by rfl⟩ : syracuseStep 558725 = 104761) (by norm_num)
theorem B558749 : Blo 370760 558749 := bbase (se 3 (by rfl) ⟨104765, by rfl⟩ : syracuseStep 558749 = 209531) (by norm_num)
theorem B558773 : Blo 370760 558773 := bbase (se 5 (by rfl) ⟨26192, by rfl⟩ : syracuseStep 558773 = 52385) (by norm_num)
theorem B558797 : Blo 370760 558797 := bbase (se 3 (by rfl) ⟨104774, by rfl⟩ : syracuseStep 558797 = 209549) (by norm_num)
theorem B558821 : Blo 370760 558821 := bbase (se 4 (by rfl) ⟨52389, by rfl⟩ : syracuseStep 558821 = 104779) (by norm_num)
theorem B558845 : Blo 370760 558845 := bbase (se 3 (by rfl) ⟨104783, by rfl⟩ : syracuseStep 558845 = 209567) (by norm_num)
theorem B558869 : Blo 370760 558869 := bbase (se 6 (by rfl) ⟨13098, by rfl⟩ : syracuseStep 558869 = 26197) (by norm_num)
theorem B558893 : Blo 370760 558893 := bbase (se 3 (by rfl) ⟨104792, by rfl⟩ : syracuseStep 558893 = 209585) (by norm_num)
theorem B558917 : Blo 370760 558917 := bbase (se 4 (by rfl) ⟨52398, by rfl⟩ : syracuseStep 558917 = 104797) (by norm_num)
theorem B558941 : Blo 370760 558941 := bbase (se 3 (by rfl) ⟨104801, by rfl⟩ : syracuseStep 558941 = 209603) (by norm_num)
theorem B558965 : Blo 370760 558965 := bbase (se 5 (by rfl) ⟨26201, by rfl⟩ : syracuseStep 558965 = 52403) (by norm_num)
theorem B558989 : Blo 370760 558989 := bbase (se 3 (by rfl) ⟨104810, by rfl⟩ : syracuseStep 558989 = 209621) (by norm_num)
theorem B1410965 : Blo 370760 1410965 := bbase (se 6 (by rfl) ⟨33069, by rfl⟩ : syracuseStep 1410965 = 66139) (by norm_num)
theorem B559013 : Blo 370760 559013 := bbase (se 4 (by rfl) ⟨52407, by rfl⟩ : syracuseStep 559013 = 104815) (by norm_num)
theorem B559037 : Blo 370760 559037 := bbase (se 3 (by rfl) ⟨104819, by rfl⟩ : syracuseStep 559037 = 209639) (by norm_num)
theorem B559061 : Blo 370760 559061 := bbase (se 7 (by rfl) ⟨6551, by rfl⟩ : syracuseStep 559061 = 13103) (by norm_num)
theorem B559085 : Blo 370760 559085 := bbase (se 3 (by rfl) ⟨104828, by rfl⟩ : syracuseStep 559085 = 209657) (by norm_num)
theorem B559109 : Blo 370760 559109 := bbase (se 4 (by rfl) ⟨52416, by rfl⟩ : syracuseStep 559109 = 104833) (by norm_num)
theorem B559133 : Blo 370760 559133 := bbase (se 3 (by rfl) ⟨104837, by rfl⟩ : syracuseStep 559133 = 209675) (by norm_num)
theorem B559157 : Blo 370760 559157 := bbase (se 5 (by rfl) ⟨26210, by rfl⟩ : syracuseStep 559157 = 52421) (by norm_num)
theorem B559181 : Blo 370760 559181 := bbase (se 3 (by rfl) ⟨104846, by rfl⟩ : syracuseStep 559181 = 209693) (by norm_num)
theorem B559205 : Blo 370760 559205 := bbase (se 4 (by rfl) ⟨52425, by rfl⟩ : syracuseStep 559205 = 104851) (by norm_num)
theorem B559229 : Blo 370760 559229 := bbase (se 3 (by rfl) ⟨104855, by rfl⟩ : syracuseStep 559229 = 209711) (by norm_num)
theorem B559253 : Blo 370760 559253 := bbase (se 6 (by rfl) ⟨13107, by rfl⟩ : syracuseStep 559253 = 26215) (by norm_num)
theorem B2427029 : Blo 370760 2427029 := bbase (se 6 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 2427029 = 113767) (by norm_num)
theorem B559277 : Blo 370760 559277 := bbase (se 3 (by rfl) ⟨104864, by rfl⟩ : syracuseStep 559277 = 209729) (by norm_num)
theorem B1411253 : Blo 370760 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B559301 : Blo 370760 559301 := bbase (se 4 (by rfl) ⟨52434, by rfl⟩ : syracuseStep 559301 = 104869) (by norm_num)
theorem B559325 : Blo 370760 559325 := bbase (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) (by norm_num)
theorem B559349 : Blo 370760 559349 := bbase (se 5 (by rfl) ⟨26219, by rfl⟩ : syracuseStep 559349 = 52439) (by norm_num)
theorem B559373 : Blo 370760 559373 := bbase (se 3 (by rfl) ⟨104882, by rfl⟩ : syracuseStep 559373 = 209765) (by norm_num)
theorem B559397 : Blo 370760 559397 := bbase (se 4 (by rfl) ⟨52443, by rfl⟩ : syracuseStep 559397 = 104887) (by norm_num)
theorem B559421 : Blo 370760 559421 := bbase (se 3 (by rfl) ⟨104891, by rfl⟩ : syracuseStep 559421 = 209783) (by norm_num)
theorem B559445 : Blo 370760 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B559469 : Blo 370760 559469 := bbase (se 3 (by rfl) ⟨104900, by rfl⟩ : syracuseStep 559469 = 209801) (by norm_num)
theorem B559493 : Blo 370760 559493 := bbase (se 4 (by rfl) ⟨52452, by rfl⟩ : syracuseStep 559493 = 104905) (by norm_num)
theorem B559517 : Blo 370760 559517 := bbase (se 3 (by rfl) ⟨104909, by rfl⟩ : syracuseStep 559517 = 209819) (by norm_num)
theorem B559541 : Blo 370760 559541 := bbase (se 5 (by rfl) ⟨26228, by rfl⟩ : syracuseStep 559541 = 52457) (by norm_num)
theorem B559565 : Blo 370760 559565 := bbase (se 3 (by rfl) ⟨104918, by rfl⟩ : syracuseStep 559565 = 209837) (by norm_num)
theorem B559589 : Blo 370760 559589 := bbase (se 4 (by rfl) ⟨52461, by rfl⟩ : syracuseStep 559589 = 104923) (by norm_num)
theorem B559613 : Blo 370760 559613 := bbase (se 3 (by rfl) ⟨104927, by rfl⟩ : syracuseStep 559613 = 209855) (by norm_num)
theorem B559637 : Blo 370760 559637 := bbase (se 6 (by rfl) ⟨13116, by rfl⟩ : syracuseStep 559637 = 26233) (by norm_num)
theorem B559661 : Blo 370760 559661 := bbase (se 3 (by rfl) ⟨104936, by rfl⟩ : syracuseStep 559661 = 209873) (by norm_num)
theorem B559685 : Blo 370760 559685 := bbase (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) (by norm_num)
theorem B559709 : Blo 370760 559709 := bbase (se 3 (by rfl) ⟨104945, by rfl⟩ : syracuseStep 559709 = 209891) (by norm_num)
theorem B559733 : Blo 370760 559733 := bbase (se 5 (by rfl) ⟨26237, by rfl⟩ : syracuseStep 559733 = 52475) (by norm_num)
theorem B559757 : Blo 370760 559757 := bbase (se 3 (by rfl) ⟨104954, by rfl⟩ : syracuseStep 559757 = 209909) (by norm_num)
theorem B3410581 : Blo 370760 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B559781 : Blo 370760 559781 := bbase (se 4 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 559781 = 104959) (by norm_num)
theorem B559805 : Blo 370760 559805 := bbase (se 3 (by rfl) ⟨104963, by rfl⟩ : syracuseStep 559805 = 209927) (by norm_num)
theorem B559829 : Blo 370760 559829 := bbase (se 7 (by rfl) ⟨6560, by rfl⟩ : syracuseStep 559829 = 13121) (by norm_num)
theorem B559853 : Blo 370760 559853 := bbase (se 3 (by rfl) ⟨104972, by rfl⟩ : syracuseStep 559853 = 209945) (by norm_num)
theorem B559877 : Blo 370760 559877 := bbase (se 4 (by rfl) ⟨52488, by rfl⟩ : syracuseStep 559877 = 104977) (by norm_num)
theorem B559901 : Blo 370760 559901 := bbase (se 3 (by rfl) ⟨104981, by rfl⟩ : syracuseStep 559901 = 209963) (by norm_num)
theorem B559925 : Blo 370760 559925 := bbase (se 5 (by rfl) ⟨26246, by rfl⟩ : syracuseStep 559925 = 52493) (by norm_num)
theorem B559949 : Blo 370760 559949 := bbase (se 3 (by rfl) ⟨104990, by rfl⟩ : syracuseStep 559949 = 209981) (by norm_num)
theorem B559973 : Blo 370760 559973 := bbase (se 4 (by rfl) ⟨52497, by rfl⟩ : syracuseStep 559973 = 104995) (by norm_num)
theorem B559997 : Blo 370760 559997 := bbase (se 3 (by rfl) ⟨104999, by rfl⟩ : syracuseStep 559997 = 209999) (by norm_num)
theorem B560021 : Blo 370760 560021 := bbase (se 6 (by rfl) ⟨13125, by rfl⟩ : syracuseStep 560021 = 26251) (by norm_num)
theorem B560045 : Blo 370760 560045 := bbase (se 3 (by rfl) ⟨105008, by rfl⟩ : syracuseStep 560045 = 210017) (by norm_num)
theorem B560069 : Blo 370760 560069 := bbase (se 4 (by rfl) ⟨52506, by rfl⟩ : syracuseStep 560069 = 105013) (by norm_num)
theorem B560093 : Blo 370760 560093 := bbase (se 3 (by rfl) ⟨105017, by rfl⟩ : syracuseStep 560093 = 210035) (by norm_num)
theorem B396257 : Blo 370760 396257 := bbase (se 2 (by rfl) ⟨148596, by rfl⟩ : syracuseStep 396257 = 297193) (by norm_num)
theorem B560117 : Blo 370760 560117 := bbase (se 5 (by rfl) ⟨26255, by rfl⟩ : syracuseStep 560117 = 52511) (by norm_num)
theorem B560141 : Blo 370760 560141 := bbase (se 3 (by rfl) ⟨105026, by rfl⟩ : syracuseStep 560141 = 210053) (by norm_num)
theorem B560165 : Blo 370760 560165 := bbase (se 4 (by rfl) ⟨52515, by rfl⟩ : syracuseStep 560165 = 105031) (by norm_num)
theorem B560189 : Blo 370760 560189 := bbase (se 3 (by rfl) ⟨105035, by rfl⟩ : syracuseStep 560189 = 210071) (by norm_num)
theorem B560213 : Blo 370760 560213 := bbase (se 8 (by rfl) ⟨3282, by rfl⟩ : syracuseStep 560213 = 6565) (by norm_num)
theorem B625765 : Blo 370760 625765 := bbase (se 4 (by rfl) ⟨58665, by rfl⟩ : syracuseStep 625765 = 117331) (by norm_num)
theorem B560237 : Blo 370760 560237 := bbase (se 3 (by rfl) ⟨105044, by rfl⟩ : syracuseStep 560237 = 210089) (by norm_num)
theorem B756869 : Blo 370760 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B560261 : Blo 370760 560261 := bbase (se 4 (by rfl) ⟨52524, by rfl⟩ : syracuseStep 560261 = 105049) (by norm_num)
theorem B560285 : Blo 370760 560285 := bbase (se 3 (by rfl) ⟨105053, by rfl⟩ : syracuseStep 560285 = 210107) (by norm_num)
theorem B560309 : Blo 370760 560309 := bbase (se 5 (by rfl) ⟨26264, by rfl⟩ : syracuseStep 560309 = 52529) (by norm_num)
theorem B625853 : Blo 370760 625853 := bbase (se 3 (by rfl) ⟨117347, by rfl⟩ : syracuseStep 625853 = 234695) (by norm_num)
theorem B560333 : Blo 370760 560333 := bbase (se 3 (by rfl) ⟨105062, by rfl⟩ : syracuseStep 560333 = 210125) (by norm_num)
theorem B396505 : Blo 370760 396505 := bbase (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) (by norm_num)
theorem B560357 : Blo 370760 560357 := bbase (se 4 (by rfl) ⟨52533, by rfl⟩ : syracuseStep 560357 = 105067) (by norm_num)
theorem B560381 : Blo 370760 560381 := bbase (se 3 (by rfl) ⟨105071, by rfl⟩ : syracuseStep 560381 = 210143) (by norm_num)
theorem B560405 : Blo 370760 560405 := bbase (se 6 (by rfl) ⟨13134, by rfl⟩ : syracuseStep 560405 = 26269) (by norm_num)
theorem B560429 : Blo 370760 560429 := bbase (se 3 (by rfl) ⟨105080, by rfl⟩ : syracuseStep 560429 = 210161) (by norm_num)
theorem B625981 : Blo 370760 625981 := bbase (se 3 (by rfl) ⟨117371, by rfl⟩ : syracuseStep 625981 = 234743) (by norm_num)
theorem B560453 : Blo 370760 560453 := bbase (se 4 (by rfl) ⟨52542, by rfl⟩ : syracuseStep 560453 = 105085) (by norm_num)
theorem B1412437 : Blo 370760 1412437 := bbase (se 11 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 1412437 = 2069) (by norm_num)
theorem B560477 : Blo 370760 560477 := bbase (se 3 (by rfl) ⟨105089, by rfl⟩ : syracuseStep 560477 = 210179) (by norm_num)
theorem B560501 : Blo 370760 560501 := bbase (se 5 (by rfl) ⟨26273, by rfl⟩ : syracuseStep 560501 = 52547) (by norm_num)
theorem B560525 : Blo 370760 560525 := bbase (se 3 (by rfl) ⟨105098, by rfl⟩ : syracuseStep 560525 = 210197) (by norm_num)
theorem B626069 : Blo 370760 626069 := bbase (se 6 (by rfl) ⟨14673, by rfl⟩ : syracuseStep 626069 = 29347) (by norm_num)
theorem B560549 : Blo 370760 560549 := bbase (se 4 (by rfl) ⟨52551, by rfl⟩ : syracuseStep 560549 = 105103) (by norm_num)
theorem B560573 : Blo 370760 560573 := bbase (se 3 (by rfl) ⟨105107, by rfl⟩ : syracuseStep 560573 = 210215) (by norm_num)
theorem B560597 : Blo 370760 560597 := bbase (se 7 (by rfl) ⟨6569, by rfl⟩ : syracuseStep 560597 = 13139) (by norm_num)
theorem B560621 : Blo 370760 560621 := bbase (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) (by norm_num)
theorem B560645 : Blo 370760 560645 := bbase (se 4 (by rfl) ⟨52560, by rfl⟩ : syracuseStep 560645 = 105121) (by norm_num)
theorem B626197 : Blo 370760 626197 := bbase (se 6 (by rfl) ⟨14676, by rfl⟩ : syracuseStep 626197 = 29353) (by norm_num)
theorem B1510933 : Blo 370760 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B560669 : Blo 370760 560669 := bbase (se 3 (by rfl) ⟨105125, by rfl⟩ : syracuseStep 560669 = 210251) (by norm_num)
theorem B3018293 : Blo 370760 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B560693 : Blo 370760 560693 := bbase (se 5 (by rfl) ⟨26282, by rfl⟩ : syracuseStep 560693 = 52565) (by norm_num)
theorem B560717 : Blo 370760 560717 := bbase (se 3 (by rfl) ⟨105134, by rfl⟩ : syracuseStep 560717 = 210269) (by norm_num)
theorem B560741 : Blo 370760 560741 := bbase (se 4 (by rfl) ⟨52569, by rfl⟩ : syracuseStep 560741 = 105139) (by norm_num)
theorem B626285 : Blo 370760 626285 := bbase (se 3 (by rfl) ⟨117428, by rfl⟩ : syracuseStep 626285 = 234857) (by norm_num)
theorem B560765 : Blo 370760 560765 := bbase (se 3 (by rfl) ⟨105143, by rfl⟩ : syracuseStep 560765 = 210287) (by norm_num)
theorem B1412741 : Blo 370760 1412741 := bbase (se 4 (by rfl) ⟨132444, by rfl⟩ : syracuseStep 1412741 = 264889) (by norm_num)
theorem B396937 : Blo 370760 396937 := bbase (se 2 (by rfl) ⟨148851, by rfl⟩ : syracuseStep 396937 = 297703) (by norm_num)
theorem B560789 : Blo 370760 560789 := bbase (se 6 (by rfl) ⟨13143, by rfl⟩ : syracuseStep 560789 = 26287) (by norm_num)
theorem B560813 : Blo 370760 560813 := bbase (se 3 (by rfl) ⟨105152, by rfl⟩ : syracuseStep 560813 = 210305) (by norm_num)
theorem B560837 : Blo 370760 560837 := bbase (se 4 (by rfl) ⟨52578, by rfl⟩ : syracuseStep 560837 = 105157) (by norm_num)
theorem B397009 : Blo 370760 397009 := bbase (se 2 (by rfl) ⟨148878, by rfl⟩ : syracuseStep 397009 = 297757) (by norm_num)
theorem B560861 : Blo 370760 560861 := bbase (se 3 (by rfl) ⟨105161, by rfl⟩ : syracuseStep 560861 = 210323) (by norm_num)
theorem B626413 : Blo 370760 626413 := bbase (se 3 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 626413 = 234905) (by norm_num)
theorem B560885 : Blo 370760 560885 := bbase (se 5 (by rfl) ⟨26291, by rfl⟩ : syracuseStep 560885 = 52583) (by norm_num)
theorem B560909 : Blo 370760 560909 := bbase (se 3 (by rfl) ⟨105170, by rfl⟩ : syracuseStep 560909 = 210341) (by norm_num)
theorem B560933 : Blo 370760 560933 := bbase (se 4 (by rfl) ⟨52587, by rfl⟩ : syracuseStep 560933 = 105175) (by norm_num)
theorem B560957 : Blo 370760 560957 := bbase (se 3 (by rfl) ⟨105179, by rfl⟩ : syracuseStep 560957 = 210359) (by norm_num)
theorem B626501 : Blo 370760 626501 := bbase (se 4 (by rfl) ⟨58734, by rfl⟩ : syracuseStep 626501 = 117469) (by norm_num)
theorem B560981 : Blo 370760 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B528229 : Blo 370760 528229 := bbase (se 4 (by rfl) ⟨49521, by rfl⟩ : syracuseStep 528229 = 99043) (by norm_num)
theorem B561005 : Blo 370760 561005 := bbase (se 3 (by rfl) ⟨105188, by rfl⟩ : syracuseStep 561005 = 210377) (by norm_num)
theorem B1347461 : Blo 370760 1347461 := bbase (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) (by norm_num)
theorem B561029 : Blo 370760 561029 := bbase (se 4 (by rfl) ⟨52596, by rfl⟩ : syracuseStep 561029 = 105193) (by norm_num)
theorem B561053 : Blo 370760 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B561077 : Blo 370760 561077 := bbase (se 5 (by rfl) ⟨26300, by rfl⟩ : syracuseStep 561077 = 52601) (by norm_num)
theorem B626629 : Blo 370760 626629 := bbase (se 4 (by rfl) ⟨58746, by rfl⟩ : syracuseStep 626629 = 117493) (by norm_num)
theorem B561101 : Blo 370760 561101 := bbase (se 3 (by rfl) ⟨105206, by rfl⟩ : syracuseStep 561101 = 210413) (by norm_num)
theorem B3411925 : Blo 370760 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B561125 : Blo 370760 561125 := bbase (se 4 (by rfl) ⟨52605, by rfl⟩ : syracuseStep 561125 = 105211) (by norm_num)
theorem B561149 : Blo 370760 561149 := bbase (se 3 (by rfl) ⟨105215, by rfl⟩ : syracuseStep 561149 = 210431) (by norm_num)
theorem B561173 : Blo 370760 561173 := bbase (se 6 (by rfl) ⟨13152, by rfl⟩ : syracuseStep 561173 = 26305) (by norm_num)
theorem B626717 : Blo 370760 626717 := bbase (se 3 (by rfl) ⟨117509, by rfl⟩ : syracuseStep 626717 = 235019) (by norm_num)
theorem B561197 : Blo 370760 561197 := bbase (se 3 (by rfl) ⟨105224, by rfl⟩ : syracuseStep 561197 = 210449) (by norm_num)
theorem B397381 : Blo 370760 397381 := bbase (se 4 (by rfl) ⟨37254, by rfl⟩ : syracuseStep 397381 = 74509) (by norm_num)
theorem B561221 : Blo 370760 561221 := bbase (se 4 (by rfl) ⟨52614, by rfl⟩ : syracuseStep 561221 = 105229) (by norm_num)
theorem B561245 : Blo 370760 561245 := bbase (se 3 (by rfl) ⟨105233, by rfl⟩ : syracuseStep 561245 = 210467) (by norm_num)
theorem B561269 : Blo 370760 561269 := bbase (se 5 (by rfl) ⟨26309, by rfl⟩ : syracuseStep 561269 = 52619) (by norm_num)
theorem B561293 : Blo 370760 561293 := bbase (se 3 (by rfl) ⟨105242, by rfl⟩ : syracuseStep 561293 = 210485) (by norm_num)
theorem B626845 : Blo 370760 626845 := bbase (se 3 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 626845 = 235067) (by norm_num)
theorem B1347749 : Blo 370760 1347749 := bbase (se 4 (by rfl) ⟨126351, by rfl⟩ : syracuseStep 1347749 = 252703) (by norm_num)
theorem B561317 : Blo 370760 561317 := bbase (se 4 (by rfl) ⟨52623, by rfl⟩ : syracuseStep 561317 = 105247) (by norm_num)
theorem B561341 : Blo 370760 561341 := bbase (se 3 (by rfl) ⟨105251, by rfl⟩ : syracuseStep 561341 = 210503) (by norm_num)
theorem B561365 : Blo 370760 561365 := bbase (se 7 (by rfl) ⟨6578, by rfl⟩ : syracuseStep 561365 = 13157) (by norm_num)
theorem B561389 : Blo 370760 561389 := bbase (se 3 (by rfl) ⟨105260, by rfl⟩ : syracuseStep 561389 = 210521) (by norm_num)
theorem B626933 : Blo 370760 626933 := bbase (se 5 (by rfl) ⟨29387, by rfl⟩ : syracuseStep 626933 = 58775) (by norm_num)
theorem B2396405 : Blo 370760 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B561413 : Blo 370760 561413 := bbase (se 4 (by rfl) ⟨52632, by rfl⟩ : syracuseStep 561413 = 105265) (by norm_num)
theorem B561437 : Blo 370760 561437 := bbase (se 3 (by rfl) ⟨105269, by rfl⟩ : syracuseStep 561437 = 210539) (by norm_num)
theorem B561461 : Blo 370760 561461 := bbase (se 5 (by rfl) ⟨26318, by rfl⟩ : syracuseStep 561461 = 52637) (by norm_num)
theorem B561485 : Blo 370760 561485 := bbase (se 3 (by rfl) ⟨105278, by rfl⟩ : syracuseStep 561485 = 210557) (by norm_num)
theorem B561509 : Blo 370760 561509 := bbase (se 4 (by rfl) ⟨52641, by rfl⟩ : syracuseStep 561509 = 105283) (by norm_num)
theorem B627061 : Blo 370760 627061 := bbase (se 5 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 627061 = 58787) (by norm_num)
theorem B561533 : Blo 370760 561533 := bbase (se 3 (by rfl) ⟨105287, by rfl⟩ : syracuseStep 561533 = 210575) (by norm_num)
theorem B561557 : Blo 370760 561557 := bbase (se 6 (by rfl) ⟨13161, by rfl⟩ : syracuseStep 561557 = 26323) (by norm_num)
theorem B561581 : Blo 370760 561581 := bbase (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) (by norm_num)
theorem B397757 : Blo 370760 397757 := bbase (se 3 (by rfl) ⟨74579, by rfl⟩ : syracuseStep 397757 = 149159) (by norm_num)
theorem B561605 : Blo 370760 561605 := bbase (se 4 (by rfl) ⟨52650, by rfl⟩ : syracuseStep 561605 = 105301) (by norm_num)
theorem B627149 : Blo 370760 627149 := bbase (se 3 (by rfl) ⟨117590, by rfl⟩ : syracuseStep 627149 = 235181) (by norm_num)
theorem B561629 : Blo 370760 561629 := bbase (se 3 (by rfl) ⟨105305, by rfl⟩ : syracuseStep 561629 = 210611) (by norm_num)
theorem B561653 : Blo 370760 561653 := bbase (se 5 (by rfl) ⟨26327, by rfl⟩ : syracuseStep 561653 = 52655) (by norm_num)
theorem B594437 : Blo 370760 594437 := bbase (se 4 (by rfl) ⟨55728, by rfl⟩ : syracuseStep 594437 = 111457) (by norm_num)
theorem B397829 : Blo 370760 397829 := bbase (se 4 (by rfl) ⟨37296, by rfl⟩ : syracuseStep 397829 = 74593) (by norm_num)
theorem B561677 : Blo 370760 561677 := bbase (se 3 (by rfl) ⟨105314, by rfl⟩ : syracuseStep 561677 = 210629) (by norm_num)
theorem B561701 : Blo 370760 561701 := bbase (se 4 (by rfl) ⟨52659, by rfl⟩ : syracuseStep 561701 = 105319) (by norm_num)
theorem B561725 : Blo 370760 561725 := bbase (se 3 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 561725 = 210647) (by norm_num)
theorem B627277 : Blo 370760 627277 := bbase (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) (by norm_num)
theorem B561749 : Blo 370760 561749 := bbase (se 8 (by rfl) ⟨3291, by rfl⟩ : syracuseStep 561749 = 6583) (by norm_num)
theorem B561773 : Blo 370760 561773 := bbase (se 3 (by rfl) ⟨105332, by rfl⟩ : syracuseStep 561773 = 210665) (by norm_num)
theorem B529021 : Blo 370760 529021 := bbase (se 3 (by rfl) ⟨99191, by rfl⟩ : syracuseStep 529021 = 198383) (by norm_num)
theorem B561797 : Blo 370760 561797 := bbase (se 4 (by rfl) ⟨52668, by rfl⟩ : syracuseStep 561797 = 105337) (by norm_num)
theorem B561821 : Blo 370760 561821 := bbase (se 3 (by rfl) ⟨105341, by rfl⟩ : syracuseStep 561821 = 210683) (by norm_num)
theorem B627365 : Blo 370760 627365 := bbase (se 4 (by rfl) ⟨58815, by rfl⟩ : syracuseStep 627365 = 117631) (by norm_num)
theorem B561845 : Blo 370760 561845 := bbase (se 5 (by rfl) ⟨26336, by rfl⟩ : syracuseStep 561845 = 52673) (by norm_num)
theorem B398017 : Blo 370760 398017 := bbase (se 2 (by rfl) ⟨149256, by rfl⟩ : syracuseStep 398017 = 298513) (by norm_num)
theorem B561869 : Blo 370760 561869 := bbase (se 3 (by rfl) ⟨105350, by rfl⟩ : syracuseStep 561869 = 210701) (by norm_num)
theorem B561893 : Blo 370760 561893 := bbase (se 4 (by rfl) ⟨52677, by rfl⟩ : syracuseStep 561893 = 105355) (by norm_num)
theorem B561917 : Blo 370760 561917 := bbase (se 3 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 561917 = 210719) (by norm_num)
theorem B561941 : Blo 370760 561941 := bbase (se 6 (by rfl) ⟨13170, by rfl⟩ : syracuseStep 561941 = 26341) (by norm_num)
theorem B627493 : Blo 370760 627493 := bbase (se 4 (by rfl) ⟨58827, by rfl⟩ : syracuseStep 627493 = 117655) (by norm_num)
theorem B561965 : Blo 370760 561965 := bbase (se 3 (by rfl) ⟨105368, by rfl⟩ : syracuseStep 561965 = 210737) (by norm_num)
theorem B561989 : Blo 370760 561989 := bbase (se 4 (by rfl) ⟨52686, by rfl⟩ : syracuseStep 561989 = 105373) (by norm_num)
theorem B562013 : Blo 370760 562013 := bbase (se 3 (by rfl) ⟨105377, by rfl⟩ : syracuseStep 562013 = 210755) (by norm_num)
theorem B562037 : Blo 370760 562037 := bbase (se 5 (by rfl) ⟨26345, by rfl⟩ : syracuseStep 562037 = 52691) (by norm_num)
theorem B398201 : Blo 370760 398201 := bbase (se 2 (by rfl) ⟨149325, by rfl⟩ : syracuseStep 398201 = 298651) (by norm_num)
theorem B627581 : Blo 370760 627581 := bbase (se 3 (by rfl) ⟨117671, by rfl⟩ : syracuseStep 627581 = 235343) (by norm_num)
theorem B562061 : Blo 370760 562061 := bbase (se 3 (by rfl) ⟨105386, by rfl⟩ : syracuseStep 562061 = 210773) (by norm_num)
theorem B758693 : Blo 370760 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B562085 : Blo 370760 562085 := bbase (se 4 (by rfl) ⟨52695, by rfl⟩ : syracuseStep 562085 = 105391) (by norm_num)
theorem B562109 : Blo 370760 562109 := bbase (se 3 (by rfl) ⟨105395, by rfl⟩ : syracuseStep 562109 = 210791) (by norm_num)
theorem B529357 : Blo 370760 529357 := bbase (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) (by norm_num)
theorem B562133 : Blo 370760 562133 := bbase (se 7 (by rfl) ⟨6587, by rfl⟩ : syracuseStep 562133 = 13175) (by norm_num)
theorem B627709 : Blo 370760 627709 := bbase (se 3 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 627709 = 235391) (by norm_num)
theorem B627797 : Blo 370760 627797 := bbase (se 8 (by rfl) ⟨3678, by rfl⟩ : syracuseStep 627797 = 7357) (by norm_num)
theorem B529573 : Blo 370760 529573 := bbase (se 4 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 529573 = 99295) (by norm_num)
theorem B595117 : Blo 370760 595117 := bbase (se 3 (by rfl) ⟨111584, by rfl⟩ : syracuseStep 595117 = 223169) (by norm_num)
theorem B627925 : Blo 370760 627925 := bbase (se 7 (by rfl) ⟨7358, by rfl⟩ : syracuseStep 627925 = 14717) (by norm_num)
theorem B595181 : Blo 370760 595181 := bbase (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) (by norm_num)
theorem B1348901 : Blo 370760 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B628013 : Blo 370760 628013 := bbase (se 3 (by rfl) ⟨117752, by rfl⟩ : syracuseStep 628013 = 235505) (by norm_num)
theorem B628141 : Blo 370760 628141 := bbase (se 3 (by rfl) ⟨117776, by rfl⟩ : syracuseStep 628141 = 235553) (by norm_num)
theorem B628229 : Blo 370760 628229 := bbase (se 4 (by rfl) ⟨58896, by rfl⟩ : syracuseStep 628229 = 117793) (by norm_num)
theorem B529949 : Blo 370760 529949 := bbase (se 3 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 529949 = 198731) (by norm_num)
theorem B398953 : Blo 370760 398953 := bbase (se 2 (by rfl) ⟨149607, by rfl⟩ : syracuseStep 398953 = 299215) (by norm_num)
theorem B792173 : Blo 370760 792173 := bbase (se 3 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 792173 = 297065) (by norm_num)
theorem B628357 : Blo 370760 628357 := bbase (se 4 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 628357 = 117817) (by norm_num)
theorem B399025 : Blo 370760 399025 := bbase (se 2 (by rfl) ⟨149634, by rfl⟩ : syracuseStep 399025 = 299269) (by norm_num)
theorem B1414853 : Blo 370760 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B628445 : Blo 370760 628445 := bbase (se 3 (by rfl) ⟨117833, by rfl⟩ : syracuseStep 628445 = 235667) (by norm_num)
theorem B628573 : Blo 370760 628573 := bbase (se 3 (by rfl) ⟨117857, by rfl⟩ : syracuseStep 628573 = 235715) (by norm_num)
theorem B399205 : Blo 370760 399205 := bbase (se 4 (by rfl) ⟨37425, by rfl⟩ : syracuseStep 399205 = 74851) (by norm_num)
theorem B628661 : Blo 370760 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B1415141 : Blo 370760 1415141 := bbase (se 4 (by rfl) ⟨132669, by rfl⟩ : syracuseStep 1415141 = 265339) (by norm_num)
theorem B628789 : Blo 370760 628789 := bbase (se 5 (by rfl) ⟨29474, by rfl⟩ : syracuseStep 628789 = 58949) (by norm_num)
theorem B956549 : Blo 370760 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B628877 : Blo 370760 628877 := bbase (se 3 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 628877 = 235829) (by norm_num)
theorem B5445845 : Blo 370760 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B1251557 : Blo 370760 1251557 := bbase (se 4 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 1251557 = 234667) (by norm_num)
theorem B629005 : Blo 370760 629005 := bbase (se 3 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 629005 = 235877) (by norm_num)
theorem B891157 : Blo 370760 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B399649 : Blo 370760 399649 := bbase (se 2 (by rfl) ⟨149868, by rfl⟩ : syracuseStep 399649 = 299737) (by norm_num)
theorem B629093 : Blo 370760 629093 := bbase (se 4 (by rfl) ⟨58977, by rfl⟩ : syracuseStep 629093 = 117955) (by norm_num)
theorem B399773 : Blo 370760 399773 := bbase (se 3 (by rfl) ⟨74957, by rfl⟩ : syracuseStep 399773 = 149915) (by norm_num)
theorem B629221 : Blo 370760 629221 := bbase (se 4 (by rfl) ⟨58989, by rfl⟩ : syracuseStep 629221 = 117979) (by norm_num)
theorem B596501 : Blo 370760 596501 := bbase (se 6 (by rfl) ⟨13980, by rfl⟩ : syracuseStep 596501 = 27961) (by norm_num)
theorem B629309 : Blo 370760 629309 := bbase (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) (by norm_num)
theorem B1350229 : Blo 370760 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B1251989 : Blo 370760 1251989 := bbase (se 6 (by rfl) ⟨29343, by rfl⟩ : syracuseStep 1251989 = 58687) (by norm_num)
theorem B400025 : Blo 370760 400025 := bbase (se 2 (by rfl) ⟨150009, by rfl⟩ : syracuseStep 400025 = 300019) (by norm_num)
theorem B629437 : Blo 370760 629437 := bbase (se 3 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 629437 = 236039) (by norm_num)
theorem B596693 : Blo 370760 596693 := bbase (se 7 (by rfl) ⟨6992, by rfl⟩ : syracuseStep 596693 = 13985) (by norm_num)
theorem B3185365 : Blo 370760 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B629525 : Blo 370760 629525 := bbase (se 6 (by rfl) ⟨14754, by rfl⟩ : syracuseStep 629525 = 29509) (by norm_num)
theorem B596821 : Blo 370760 596821 := bbase (se 9 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 596821 = 3497) (by norm_num)
theorem B8624981 : Blo 370760 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B891773 : Blo 370760 891773 := bbase (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) (by norm_num)
theorem B629653 : Blo 370760 629653 := bbase (se 6 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 629653 = 29515) (by norm_num)
theorem B531373 : Blo 370760 531373 := bbase (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) (by norm_num)
theorem B629741 : Blo 370760 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B1252421 : Blo 370760 1252421 := bbase (se 4 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 1252421 = 234829) (by norm_num)
theorem B629869 : Blo 370760 629869 := bbase (se 3 (by rfl) ⟨118100, by rfl⟩ : syracuseStep 629869 = 236201) (by norm_num)
theorem B1416325 : Blo 370760 1416325 := bbase (se 4 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 1416325 = 265561) (by norm_num)
theorem B2399381 : Blo 370760 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B629957 : Blo 370760 629957 := bbase (se 4 (by rfl) ⟨59058, by rfl⟩ : syracuseStep 629957 = 118117) (by norm_num)
theorem B892109 : Blo 370760 892109 := bbase (se 3 (by rfl) ⟨167270, by rfl⟩ : syracuseStep 892109 = 334541) (by norm_num)
theorem B793813 : Blo 370760 793813 := bbase (se 7 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 793813 = 18605) (by norm_num)
theorem B1056037 : Blo 370760 1056037 := bbase (se 4 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 1056037 = 198007) (by norm_num)
theorem B630085 : Blo 370760 630085 := bbase (se 4 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 630085 = 118141) (by norm_num)
theorem B630173 : Blo 370760 630173 := bbase (se 3 (by rfl) ⟨118157, by rfl⟩ : syracuseStep 630173 = 236315) (by norm_num)
theorem B1416629 : Blo 370760 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B597461 : Blo 370760 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B1252853 : Blo 370760 1252853 := bbase (se 5 (by rfl) ⟨58727, by rfl⟩ : syracuseStep 1252853 = 117455) (by norm_num)
theorem B531965 : Blo 370760 531965 := bbase (se 3 (by rfl) ⟨99743, by rfl⟩ : syracuseStep 531965 = 199487) (by norm_num)
theorem B630301 : Blo 370760 630301 := bbase (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) (by norm_num)
theorem B532045 : Blo 370760 532045 := bbase (se 3 (by rfl) ⟨99758, by rfl⟩ : syracuseStep 532045 = 199517) (by norm_num)
theorem B892501 : Blo 370760 892501 := bbase (se 8 (by rfl) ⟨5229, by rfl⟩ : syracuseStep 892501 = 10459) (by norm_num)
theorem B630389 : Blo 370760 630389 := bbase (se 5 (by rfl) ⟨29549, by rfl⟩ : syracuseStep 630389 = 59099) (by norm_num)
theorem B532165 : Blo 370760 532165 := bbase (se 4 (by rfl) ⟨49890, by rfl⟩ : syracuseStep 532165 = 99781) (by norm_num)
theorem B630517 : Blo 370760 630517 := bbase (se 5 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 630517 = 59111) (by norm_num)
theorem B532261 : Blo 370760 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B630605 : Blo 370760 630605 := bbase (se 3 (by rfl) ⟨118238, by rfl⟩ : syracuseStep 630605 = 236477) (by norm_num)
theorem B597917 : Blo 370760 597917 := bbase (se 3 (by rfl) ⟨112109, by rfl⟩ : syracuseStep 597917 = 224219) (by norm_num)
theorem B1253285 : Blo 370760 1253285 := bbase (se 4 (by rfl) ⟨117495, by rfl⟩ : syracuseStep 1253285 = 234991) (by norm_num)
theorem B630733 : Blo 370760 630733 := bbase (se 3 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 630733 = 236525) (by norm_num)
theorem B630821 : Blo 370760 630821 := bbase (se 4 (by rfl) ⟨59139, by rfl⟩ : syracuseStep 630821 = 118279) (by norm_num)
theorem B794701 : Blo 370760 794701 := bbase (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) (by norm_num)
theorem B598141 : Blo 370760 598141 := bbase (se 3 (by rfl) ⟨112151, by rfl⟩ : syracuseStep 598141 = 224303) (by norm_num)
theorem B630949 : Blo 370760 630949 := bbase (se 4 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 630949 = 118303) (by norm_num)
theorem B598205 : Blo 370760 598205 := bbase (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) (by norm_num)
theorem B631037 : Blo 370760 631037 := bbase (se 3 (by rfl) ⟨118319, by rfl⟩ : syracuseStep 631037 = 236639) (by norm_num)
theorem B532757 : Blo 370760 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B598333 : Blo 370760 598333 := bbase (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) (by norm_num)
theorem B1253717 : Blo 370760 1253717 := bbase (se 10 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 1253717 = 3673) (by norm_num)
theorem B1057141 : Blo 370760 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B631165 : Blo 370760 631165 := bbase (se 3 (by rfl) ⟨118343, by rfl⟩ : syracuseStep 631165 = 236687) (by norm_num)
theorem B631253 : Blo 370760 631253 := bbase (se 7 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 631253 = 14795) (by norm_num)
theorem B795197 : Blo 370760 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B631381 : Blo 370760 631381 := bbase (se 8 (by rfl) ⟨3699, by rfl⟩ : syracuseStep 631381 = 7399) (by norm_num)
theorem B3187349 : Blo 370760 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B631469 : Blo 370760 631469 := bbase (se 3 (by rfl) ⟨118400, by rfl⟩ : syracuseStep 631469 = 236801) (by norm_num)
theorem B402149 : Blo 370760 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B1254149 : Blo 370760 1254149 := bbase (se 4 (by rfl) ⟨117576, by rfl⟩ : syracuseStep 1254149 = 235153) (by norm_num)
theorem B631597 : Blo 370760 631597 := bbase (se 3 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 631597 = 236849) (by norm_num)
theorem B2827061 : Blo 370760 2827061 := bbase (se 5 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 2827061 = 265037) (by norm_num)
theorem B533309 : Blo 370760 533309 := bbase (se 3 (by rfl) ⟨99995, by rfl⟩ : syracuseStep 533309 = 199991) (by norm_num)
theorem B828245 : Blo 370760 828245 := bbase (se 9 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 828245 = 4853) (by norm_num)
theorem B631685 : Blo 370760 631685 := bbase (se 4 (by rfl) ⟨59220, by rfl⟩ : syracuseStep 631685 = 118441) (by norm_num)
theorem B3449749 : Blo 370760 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B631813 : Blo 370760 631813 := bbase (se 4 (by rfl) ⟨59232, by rfl⟩ : syracuseStep 631813 = 118465) (by norm_num)
theorem B631901 : Blo 370760 631901 := bbase (se 3 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 631901 = 236963) (by norm_num)
theorem B1877093 : Blo 370760 1877093 := bbase (se 4 (by rfl) ⟨175977, by rfl⟩ : syracuseStep 1877093 = 351955) (by norm_num)
theorem B1254581 : Blo 370760 1254581 := bbase (se 5 (by rfl) ⟨58808, by rfl⟩ : syracuseStep 1254581 = 117617) (by norm_num)
theorem B632029 : Blo 370760 632029 := bbase (se 3 (by rfl) ⟨118505, by rfl⟩ : syracuseStep 632029 = 237011) (by norm_num)
theorem B632117 : Blo 370760 632117 := bbase (se 5 (by rfl) ⟨29630, by rfl⟩ : syracuseStep 632117 = 59261) (by norm_num)
theorem B796061 : Blo 370760 796061 := bbase (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) (by norm_num)
theorem B632245 : Blo 370760 632245 := bbase (se 5 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 632245 = 59273) (by norm_num)
theorem B1418741 : Blo 370760 1418741 := bbase (se 5 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 1418741 = 133007) (by norm_num)
theorem B599557 : Blo 370760 599557 := bbase (se 4 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 599557 = 112417) (by norm_num)
theorem B632333 : Blo 370760 632333 := bbase (se 3 (by rfl) ⟨118562, by rfl⟩ : syracuseStep 632333 = 237125) (by norm_num)
theorem B796205 : Blo 370760 796205 := bbase (se 3 (by rfl) ⟨149288, by rfl⟩ : syracuseStep 796205 = 298577) (by norm_num)
theorem B1517125 : Blo 370760 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1255013 : Blo 370760 1255013 := bbase (se 4 (by rfl) ⟨117657, by rfl⟩ : syracuseStep 1255013 = 235315) (by norm_num)
theorem B1189541 : Blo 370760 1189541 := bbase (se 4 (by rfl) ⟨111519, by rfl⟩ : syracuseStep 1189541 = 223039) (by norm_num)
theorem B1419029 : Blo 370760 1419029 := bbase (se 6 (by rfl) ⟨33258, by rfl⟩ : syracuseStep 1419029 = 66517) (by norm_num)
theorem B1058645 : Blo 370760 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B1255445 : Blo 370760 1255445 := bbase (se 6 (by rfl) ⟨29424, by rfl⟩ : syracuseStep 1255445 = 58849) (by norm_num)
theorem B600229 : Blo 370760 600229 := bbase (se 4 (by rfl) ⟨56271, by rfl⟩ : syracuseStep 600229 = 112543) (by norm_num)
theorem B2697461 : Blo 370760 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B469253 : Blo 370760 469253 := bbase (se 4 (by rfl) ⟨43992, by rfl⟩ : syracuseStep 469253 = 87985) (by norm_num)
theorem B796949 : Blo 370760 796949 := bbase (se 6 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 796949 = 37357) (by norm_num)
theorem B469309 : Blo 370760 469309 := bbase (se 3 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 469309 = 175991) (by norm_num)
theorem B1878389 : Blo 370760 1878389 := bbase (se 5 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 1878389 = 176099) (by norm_num)
theorem B469405 : Blo 370760 469405 := bbase (se 3 (by rfl) ⟨88013, by rfl⟩ : syracuseStep 469405 = 176027) (by norm_num)
theorem B502205 : Blo 370760 502205 := bbase (se 3 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 502205 = 188327) (by norm_num)
theorem B1255877 : Blo 370760 1255877 := bbase (se 4 (by rfl) ⟨117738, by rfl⟩ : syracuseStep 1255877 = 235477) (by norm_num)
theorem B469577 : Blo 370760 469577 := bbase (se 2 (by rfl) ⟨176091, by rfl⟩ : syracuseStep 469577 = 352183) (by norm_num)
theorem B502357 : Blo 370760 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B469633 : Blo 370760 469633 := bbase (se 2 (by rfl) ⟨176112, by rfl⟩ : syracuseStep 469633 = 352225) (by norm_num)
theorem B895645 : Blo 370760 895645 := bbase (se 3 (by rfl) ⟨167933, by rfl⟩ : syracuseStep 895645 = 335867) (by norm_num)
theorem B895693 : Blo 370760 895693 := bbase (se 3 (by rfl) ⟨167942, by rfl⟩ : syracuseStep 895693 = 335885) (by norm_num)
theorem B469729 : Blo 370760 469729 := bbase (se 2 (by rfl) ⟨176148, by rfl⟩ : syracuseStep 469729 = 352297) (by norm_num)
theorem B1256309 : Blo 370760 1256309 := bbase (se 5 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 1256309 = 117779) (by norm_num)
theorem B469901 : Blo 370760 469901 := bbase (se 3 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 469901 = 176213) (by norm_num)
theorem B1420213 : Blo 370760 1420213 := bbase (se 5 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 1420213 = 133145) (by norm_num)
theorem B469957 : Blo 370760 469957 := bbase (se 4 (by rfl) ⟨44058, by rfl⟩ : syracuseStep 469957 = 88117) (by norm_num)
theorem B797701 : Blo 370760 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B568333 : Blo 370760 568333 := bbase (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) (by norm_num)
theorem B470053 : Blo 370760 470053 := bbase (se 4 (by rfl) ⟨44067, by rfl⟩ : syracuseStep 470053 = 88135) (by norm_num)
theorem B797845 : Blo 370760 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B470225 : Blo 370760 470225 := bbase (se 2 (by rfl) ⟨176334, by rfl⟩ : syracuseStep 470225 = 352669) (by norm_num)
theorem B1420517 : Blo 370760 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B404713 : Blo 370760 404713 := bbase (se 2 (by rfl) ⟨151767, by rfl⟩ : syracuseStep 404713 = 303535) (by norm_num)
theorem B470281 : Blo 370760 470281 := bbase (se 2 (by rfl) ⟨176355, by rfl⟩ : syracuseStep 470281 = 352711) (by norm_num)
theorem B1256741 : Blo 370760 1256741 := bbase (se 4 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 1256741 = 235639) (by norm_num)
theorem B896309 : Blo 370760 896309 := bbase (se 5 (by rfl) ⟨42014, by rfl⟩ : syracuseStep 896309 = 84029) (by norm_num)
theorem B470377 : Blo 370760 470377 := bbase (se 2 (by rfl) ⟨176391, by rfl⟩ : syracuseStep 470377 = 352783) (by norm_num)
theorem B1060229 : Blo 370760 1060229 := bbase (se 4 (by rfl) ⟨99396, by rfl⟩ : syracuseStep 1060229 = 198793) (by norm_num)
theorem B798221 : Blo 370760 798221 := bbase (se 3 (by rfl) ⟨149666, by rfl⟩ : syracuseStep 798221 = 299333) (by norm_num)
theorem B470549 : Blo 370760 470549 := bbase (se 6 (by rfl) ⟨11028, by rfl⟩ : syracuseStep 470549 = 22057) (by norm_num)
theorem B470605 : Blo 370760 470605 := bbase (se 3 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 470605 = 176477) (by norm_num)
theorem B1879685 : Blo 370760 1879685 := bbase (se 4 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 1879685 = 352441) (by norm_num)
theorem B896653 : Blo 370760 896653 := bbase (se 3 (by rfl) ⟨168122, by rfl⟩ : syracuseStep 896653 = 336245) (by norm_num)
theorem B470701 : Blo 370760 470701 := bbase (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) (by norm_num)
theorem B1257173 : Blo 370760 1257173 := bbase (se 7 (by rfl) ⟨14732, by rfl⟩ : syracuseStep 1257173 = 29465) (by norm_num)
theorem B438049 : Blo 370760 438049 := bbase (se 2 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 438049 = 328537) (by norm_num)
theorem B470873 : Blo 370760 470873 := bbase (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) (by norm_num)
theorem B1191797 : Blo 370760 1191797 := bbase (se 5 (by rfl) ⟨55865, by rfl⟩ : syracuseStep 1191797 = 111731) (by norm_num)
theorem B896885 : Blo 370760 896885 := bbase (se 5 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 896885 = 84083) (by norm_num)
theorem B798589 : Blo 370760 798589 := bbase (se 3 (by rfl) ⟨149735, by rfl⟩ : syracuseStep 798589 = 299471) (by norm_num)
theorem B470929 : Blo 370760 470929 := bbase (se 2 (by rfl) ⟨176598, by rfl⟩ : syracuseStep 470929 = 353197) (by norm_num)
theorem B3583925 : Blo 370760 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B471025 : Blo 370760 471025 := bbase (se 2 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 471025 = 353269) (by norm_num)
theorem B1060901 : Blo 370760 1060901 := bbase (se 4 (by rfl) ⟨99459, by rfl⟩ : syracuseStep 1060901 = 198919) (by norm_num)
theorem B1781813 : Blo 370760 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B897077 : Blo 370760 897077 := bbase (se 5 (by rfl) ⟨42050, by rfl⟩ : syracuseStep 897077 = 84101) (by norm_num)
theorem B1257605 : Blo 370760 1257605 := bbase (se 4 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 1257605 = 235801) (by norm_num)
theorem B471197 : Blo 370760 471197 := bbase (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) (by norm_num)
theorem B471253 : Blo 370760 471253 := bbase (se 7 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 471253 = 11045) (by norm_num)
theorem B2699477 : Blo 370760 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B471349 : Blo 370760 471349 := bbase (se 5 (by rfl) ⟨22094, by rfl⟩ : syracuseStep 471349 = 44189) (by norm_num)
theorem B635221 : Blo 370760 635221 := bbase (se 10 (by rfl) ⟨930, by rfl⟩ : syracuseStep 635221 = 1861) (by norm_num)
theorem B897365 : Blo 370760 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B1061333 : Blo 370760 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B471521 : Blo 370760 471521 := bbase (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) (by norm_num)
theorem B471577 : Blo 370760 471577 := bbase (se 2 (by rfl) ⟨176841, by rfl⟩ : syracuseStep 471577 = 353683) (by norm_num)
theorem B602653 : Blo 370760 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B1258037 : Blo 370760 1258037 := bbase (se 5 (by rfl) ⟨58970, by rfl⟩ : syracuseStep 1258037 = 117941) (by norm_num)
theorem B1585781 : Blo 370760 1585781 := bbase (se 5 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 1585781 = 148667) (by norm_num)
theorem B1192565 : Blo 370760 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B471673 : Blo 370760 471673 := bbase (se 2 (by rfl) ⟨176877, by rfl⟩ : syracuseStep 471673 = 353755) (by norm_num)
theorem B471845 : Blo 370760 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B471901 : Blo 370760 471901 := bbase (se 3 (by rfl) ⟨88481, by rfl⟩ : syracuseStep 471901 = 176963) (by norm_num)
theorem B1848197 : Blo 370760 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B1880981 : Blo 370760 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B471997 : Blo 370760 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B1258469 : Blo 370760 1258469 := bbase (se 4 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 1258469 = 235963) (by norm_num)
theorem B472169 : Blo 370760 472169 := bbase (se 2 (by rfl) ⟨177063, by rfl⟩ : syracuseStep 472169 = 354127) (by norm_num)
theorem B1193077 : Blo 370760 1193077 := bbase (se 5 (by rfl) ⟨55925, by rfl⟩ : syracuseStep 1193077 = 111851) (by norm_num)
theorem B504973 : Blo 370760 504973 := bbase (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) (by norm_num)
theorem B472225 : Blo 370760 472225 := bbase (se 2 (by rfl) ⟨177084, by rfl⟩ : syracuseStep 472225 = 354169) (by norm_num)
theorem B1062085 : Blo 370760 1062085 := bbase (se 4 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 1062085 = 199141) (by norm_num)
theorem B472321 : Blo 370760 472321 := bbase (se 2 (by rfl) ⟨177120, by rfl⟩ : syracuseStep 472321 = 354241) (by norm_num)
theorem B1422629 : Blo 370760 1422629 := bbase (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) (by norm_num)
theorem B636221 : Blo 370760 636221 := bbase (se 3 (by rfl) ⟨119291, by rfl⟩ : syracuseStep 636221 = 238583) (by norm_num)
theorem B800093 : Blo 370760 800093 := bbase (se 3 (by rfl) ⟨150017, by rfl⟩ : syracuseStep 800093 = 300035) (by norm_num)
theorem B1258901 : Blo 370760 1258901 := bbase (se 6 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 1258901 = 59011) (by norm_num)
theorem B472493 : Blo 370760 472493 := bbase (se 3 (by rfl) ⟨88592, by rfl⟩ : syracuseStep 472493 = 177185) (by norm_num)
theorem B472549 : Blo 370760 472549 := bbase (se 4 (by rfl) ⟨44301, by rfl⟩ : syracuseStep 472549 = 88603) (by norm_num)
theorem B800237 : Blo 370760 800237 := bbase (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) (by norm_num)
theorem B669197 : Blo 370760 669197 := bbase (se 3 (by rfl) ⟨125474, by rfl⟩ : syracuseStep 669197 = 250949) (by norm_num)
theorem B3814933 : Blo 370760 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B472645 : Blo 370760 472645 := bbase (se 4 (by rfl) ⟨44310, by rfl⟩ : syracuseStep 472645 = 88621) (by norm_num)
theorem B1619525 : Blo 370760 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B1422917 : Blo 370760 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B636589 : Blo 370760 636589 := bbase (se 3 (by rfl) ⟨119360, by rfl⟩ : syracuseStep 636589 = 238721) (by norm_num)
theorem B964325 : Blo 370760 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B472817 : Blo 370760 472817 := bbase (se 2 (by rfl) ⟨177306, by rfl⟩ : syracuseStep 472817 = 354613) (by norm_num)
theorem B472873 : Blo 370760 472873 := bbase (se 2 (by rfl) ⟨177327, by rfl⟩ : syracuseStep 472873 = 354655) (by norm_num)
theorem B1259333 : Blo 370760 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B472969 : Blo 370760 472969 := bbase (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) (by norm_num)
theorem B1718261 : Blo 370760 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B473141 : Blo 370760 473141 := bbase (se 5 (by rfl) ⟨22178, by rfl⟩ : syracuseStep 473141 = 44357) (by norm_num)
theorem B473197 : Blo 370760 473197 := bbase (se 3 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 473197 = 177449) (by norm_num)
theorem B768125 : Blo 370760 768125 := bbase (se 3 (by rfl) ⟨144023, by rfl⟩ : syracuseStep 768125 = 288047) (by norm_num)
theorem B2144405 : Blo 370760 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B1882277 : Blo 370760 1882277 := bbase (se 4 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 1882277 = 352927) (by norm_num)
theorem B473293 : Blo 370760 473293 := bbase (se 3 (by rfl) ⟨88742, by rfl⟩ : syracuseStep 473293 = 177485) (by norm_num)
theorem B2865365 : Blo 370760 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1259765 : Blo 370760 1259765 := bbase (se 5 (by rfl) ⟨59051, by rfl⟩ : syracuseStep 1259765 = 118103) (by norm_num)
theorem B1128725 : Blo 370760 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B735517 : Blo 370760 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B604445 : Blo 370760 604445 := bbase (se 3 (by rfl) ⟨113333, by rfl⟩ : syracuseStep 604445 = 226667) (by norm_num)
theorem B36256085 : Blo 370760 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B473465 : Blo 370760 473465 := bbase (se 2 (by rfl) ⟨177549, by rfl⟩ : syracuseStep 473465 = 355099) (by norm_num)
theorem B473521 : Blo 370760 473521 := bbase (se 2 (by rfl) ⟨177570, by rfl⟩ : syracuseStep 473521 = 355141) (by norm_num)
theorem B670141 : Blo 370760 670141 := bbase (se 3 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 670141 = 251303) (by norm_num)
theorem B473617 : Blo 370760 473617 := bbase (se 2 (by rfl) ⟨177606, by rfl⟩ : syracuseStep 473617 = 355213) (by norm_num)
theorem B1096325 : Blo 370760 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B604829 : Blo 370760 604829 := bbase (se 3 (by rfl) ⟨113405, by rfl⟩ : syracuseStep 604829 = 226811) (by norm_num)
theorem B1260197 : Blo 370760 1260197 := bbase (se 4 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 1260197 = 236287) (by norm_num)
theorem B473789 : Blo 370760 473789 := bbase (se 3 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 473789 = 177671) (by norm_num)
theorem B834245 : Blo 370760 834245 := bbase (se 4 (by rfl) ⟨78210, by rfl⟩ : syracuseStep 834245 = 156421) (by norm_num)
theorem B473845 : Blo 370760 473845 := bbase (se 5 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 473845 = 44423) (by norm_num)
theorem B834317 : Blo 370760 834317 := bbase (se 3 (by rfl) ⟨156434, by rfl⟩ : syracuseStep 834317 = 312869) (by norm_num)
theorem B2112277 : Blo 370760 2112277 := bbase (se 6 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 2112277 = 99013) (by norm_num)
theorem B637733 : Blo 370760 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B1194821 : Blo 370760 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B834389 : Blo 370760 834389 := bbase (se 9 (by rfl) ⟨2444, by rfl⟩ : syracuseStep 834389 = 4889) (by norm_num)
theorem B473941 : Blo 370760 473941 := bbase (se 9 (by rfl) ⟨1388, by rfl⟩ : syracuseStep 473941 = 2777) (by norm_num)
theorem B834461 : Blo 370760 834461 := bbase (se 3 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 834461 = 312923) (by norm_num)
theorem B834533 : Blo 370760 834533 := bbase (se 4 (by rfl) ⟨78237, by rfl⟩ : syracuseStep 834533 = 156475) (by norm_num)
theorem B474113 : Blo 370760 474113 := bbase (se 2 (by rfl) ⟨177792, by rfl⟩ : syracuseStep 474113 = 355585) (by norm_num)
theorem B1195013 : Blo 370760 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B834605 : Blo 370760 834605 := bbase (se 3 (by rfl) ⟨156488, by rfl⟩ : syracuseStep 834605 = 312977) (by norm_num)
theorem B474169 : Blo 370760 474169 := bbase (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) (by norm_num)
theorem B1260629 : Blo 370760 1260629 := bbase (se 8 (by rfl) ⟨7386, by rfl⟩ : syracuseStep 1260629 = 14773) (by norm_num)
theorem B834677 : Blo 370760 834677 := bbase (se 5 (by rfl) ⟨39125, by rfl⟩ : syracuseStep 834677 = 78251) (by norm_num)
theorem B474265 : Blo 370760 474265 := bbase (se 2 (by rfl) ⟨177849, by rfl⟩ : syracuseStep 474265 = 355699) (by norm_num)
theorem B375989 : Blo 370760 375989 := bbase (se 5 (by rfl) ⟨17624, by rfl⟩ : syracuseStep 375989 = 35249) (by norm_num)
theorem B834749 : Blo 370760 834749 := bbase (se 3 (by rfl) ⟨156515, by rfl⟩ : syracuseStep 834749 = 313031) (by norm_num)
theorem B1621205 : Blo 370760 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B572653 : Blo 370760 572653 := bbase (se 3 (by rfl) ⟨107372, by rfl⟩ : syracuseStep 572653 = 214745) (by norm_num)
theorem B834821 : Blo 370760 834821 := bbase (se 4 (by rfl) ⟨78264, by rfl⟩ : syracuseStep 834821 = 156529) (by norm_num)
theorem B1359125 : Blo 370760 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B834893 : Blo 370760 834893 := bbase (se 3 (by rfl) ⟨156542, by rfl⟩ : syracuseStep 834893 = 313085) (by norm_num)
theorem B834965 : Blo 370760 834965 := bbase (se 6 (by rfl) ⟨19569, by rfl⟩ : syracuseStep 834965 = 39139) (by norm_num)
theorem B1883573 : Blo 370760 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B835037 : Blo 370760 835037 := bbase (se 3 (by rfl) ⟨156569, by rfl⟩ : syracuseStep 835037 = 313139) (by norm_num)
theorem B1261061 : Blo 370760 1261061 := bbase (se 4 (by rfl) ⟨118224, by rfl⟩ : syracuseStep 1261061 = 236449) (by norm_num)
theorem B835109 : Blo 370760 835109 := bbase (se 4 (by rfl) ⟨78291, by rfl⟩ : syracuseStep 835109 = 156583) (by norm_num)
theorem B638533 : Blo 370760 638533 := bbase (se 4 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 638533 = 119725) (by norm_num)
theorem B769637 : Blo 370760 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B835181 : Blo 370760 835181 := bbase (se 3 (by rfl) ⟨156596, by rfl⟩ : syracuseStep 835181 = 313193) (by norm_num)
theorem B835253 : Blo 370760 835253 := bbase (se 5 (by rfl) ⟨39152, by rfl⟩ : syracuseStep 835253 = 78305) (by norm_num)
theorem B638669 : Blo 370760 638669 := bbase (se 3 (by rfl) ⟨119750, by rfl⟩ : syracuseStep 638669 = 239501) (by norm_num)
theorem B376553 : Blo 370760 376553 := bbase (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) (by norm_num)
theorem B835325 : Blo 370760 835325 := bbase (se 3 (by rfl) ⟨156623, by rfl⟩ : syracuseStep 835325 = 313247) (by norm_num)
theorem B835397 : Blo 370760 835397 := bbase (se 4 (by rfl) ⟨78318, by rfl⟩ : syracuseStep 835397 = 156637) (by norm_num)
theorem B704389 : Blo 370760 704389 := bbase (se 4 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 704389 = 132073) (by norm_num)
theorem B835469 : Blo 370760 835469 := bbase (se 3 (by rfl) ⟨156650, by rfl⟩ : syracuseStep 835469 = 313301) (by norm_num)
theorem B1261493 : Blo 370760 1261493 := bbase (se 5 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 1261493 = 118265) (by norm_num)
theorem B835541 : Blo 370760 835541 := bbase (se 7 (by rfl) ⟨9791, by rfl⟩ : syracuseStep 835541 = 19583) (by norm_num)
theorem B1064933 : Blo 370760 1064933 := bbase (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) (by norm_num)
theorem B671741 : Blo 370760 671741 := bbase (se 3 (by rfl) ⟨125951, by rfl⟩ : syracuseStep 671741 = 251903) (by norm_num)
theorem B704533 : Blo 370760 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B835613 : Blo 370760 835613 := bbase (se 3 (by rfl) ⟨156677, by rfl⟩ : syracuseStep 835613 = 313355) (by norm_num)
theorem B1785925 : Blo 370760 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B835685 : Blo 370760 835685 := bbase (se 4 (by rfl) ⟨78345, by rfl⟩ : syracuseStep 835685 = 156691) (by norm_num)
theorem B835757 : Blo 370760 835757 := bbase (se 3 (by rfl) ⟨156704, by rfl⟩ : syracuseStep 835757 = 313409) (by norm_num)
theorem B704693 : Blo 370760 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B835829 : Blo 370760 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B835901 : Blo 370760 835901 := bbase (se 3 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 835901 = 313463) (by norm_num)
theorem B704837 : Blo 370760 704837 := bbase (se 4 (by rfl) ⟨66078, by rfl⟩ : syracuseStep 704837 = 132157) (by norm_num)
theorem B1261925 : Blo 370760 1261925 := bbase (se 4 (by rfl) ⟨118305, by rfl⟩ : syracuseStep 1261925 = 236611) (by norm_num)
theorem B835973 : Blo 370760 835973 := bbase (se 4 (by rfl) ⟨78372, by rfl⟩ : syracuseStep 835973 = 156745) (by norm_num)
theorem B2834837 : Blo 370760 2834837 := bbase (se 6 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 2834837 = 132883) (by norm_num)
theorem B836045 : Blo 370760 836045 := bbase (se 3 (by rfl) ⟨156758, by rfl⟩ : syracuseStep 836045 = 313517) (by norm_num)
theorem B836117 : Blo 370760 836117 := bbase (se 6 (by rfl) ⟨19596, by rfl⟩ : syracuseStep 836117 = 39193) (by norm_num)
theorem B6242837 : Blo 370760 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1589813 : Blo 370760 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B377417 : Blo 370760 377417 := bbase (se 2 (by rfl) ⟨141531, by rfl⟩ : syracuseStep 377417 = 283063) (by norm_num)
theorem B836189 : Blo 370760 836189 := bbase (se 3 (by rfl) ⟨156785, by rfl⟩ : syracuseStep 836189 = 313571) (by norm_num)
theorem B705125 : Blo 370760 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B377465 : Blo 370760 377465 := bbase (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) (by norm_num)
theorem B836261 : Blo 370760 836261 := bbase (se 4 (by rfl) ⟨78399, by rfl⟩ : syracuseStep 836261 = 156799) (by norm_num)
theorem B1884869 : Blo 370760 1884869 := bbase (se 4 (by rfl) ⟨176706, by rfl⟩ : syracuseStep 1884869 = 353413) (by norm_num)
theorem B2114261 : Blo 370760 2114261 := bbase (se 7 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 2114261 = 49553) (by norm_num)
theorem B836333 : Blo 370760 836333 := bbase (se 3 (by rfl) ⟨156812, by rfl⟩ : syracuseStep 836333 = 313625) (by norm_num)
theorem B705277 : Blo 370760 705277 := bbase (se 3 (by rfl) ⟨132239, by rfl⟩ : syracuseStep 705277 = 264479) (by norm_num)
theorem B1262357 : Blo 370760 1262357 := bbase (se 6 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 1262357 = 59173) (by norm_num)
theorem B836405 : Blo 370760 836405 := bbase (se 5 (by rfl) ⟨39206, by rfl⟩ : syracuseStep 836405 = 78413) (by norm_num)
theorem B672605 : Blo 370760 672605 := bbase (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) (by norm_num)
theorem B836477 : Blo 370760 836477 := bbase (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) (by norm_num)
theorem B836549 : Blo 370760 836549 := bbase (se 4 (by rfl) ⟨78426, by rfl⟩ : syracuseStep 836549 = 156853) (by norm_num)
theorem B836621 : Blo 370760 836621 := bbase (se 3 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 836621 = 313733) (by norm_num)
theorem B705581 : Blo 370760 705581 := bbase (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) (by norm_num)
theorem B836693 : Blo 370760 836693 := bbase (se 8 (by rfl) ⟨4902, by rfl⟩ : syracuseStep 836693 = 9805) (by norm_num)
theorem B1066117 : Blo 370760 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B836765 : Blo 370760 836765 := bbase (se 3 (by rfl) ⟨156893, by rfl⟩ : syracuseStep 836765 = 313787) (by norm_num)
theorem B1262789 : Blo 370760 1262789 := bbase (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) (by norm_num)
theorem B378065 : Blo 370760 378065 := bbase (se 2 (by rfl) ⟨141774, by rfl⟩ : syracuseStep 378065 = 283549) (by norm_num)
theorem B836837 : Blo 370760 836837 := bbase (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) (by norm_num)
theorem B804125 : Blo 370760 804125 := bbase (se 3 (by rfl) ⟨150773, by rfl⟩ : syracuseStep 804125 = 301547) (by norm_num)
theorem B1066277 : Blo 370760 1066277 := bbase (se 4 (by rfl) ⟨99963, by rfl⟩ : syracuseStep 1066277 = 199927) (by norm_num)
theorem B836909 : Blo 370760 836909 := bbase (se 3 (by rfl) ⟨156920, by rfl⟩ : syracuseStep 836909 = 313841) (by norm_num)
theorem B836981 : Blo 370760 836981 := bbase (se 5 (by rfl) ⟨39233, by rfl⟩ : syracuseStep 836981 = 78467) (by norm_num)
theorem B640381 : Blo 370760 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B837053 : Blo 370760 837053 := bbase (se 3 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 837053 = 313895) (by norm_num)
theorem B378317 : Blo 370760 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B837125 : Blo 370760 837125 := bbase (se 4 (by rfl) ⟨78480, by rfl⟩ : syracuseStep 837125 = 156961) (by norm_num)
theorem B1066517 : Blo 370760 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B837197 : Blo 370760 837197 := bbase (se 3 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 837197 = 313949) (by norm_num)
theorem B1263221 : Blo 370760 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B837269 : Blo 370760 837269 := bbase (se 6 (by rfl) ⟨19623, by rfl⟩ : syracuseStep 837269 = 39247) (by norm_num)
theorem B1066709 : Blo 370760 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B837341 : Blo 370760 837341 := bbase (se 3 (by rfl) ⟨157001, by rfl⟩ : syracuseStep 837341 = 314003) (by norm_num)
theorem B706333 : Blo 370760 706333 := bbase (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) (by norm_num)
theorem B837413 : Blo 370760 837413 := bbase (se 4 (by rfl) ⟨78507, by rfl⟩ : syracuseStep 837413 = 157015) (by norm_num)
theorem B837485 : Blo 370760 837485 := bbase (se 3 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 837485 = 314057) (by norm_num)
theorem B706477 : Blo 370760 706477 := bbase (se 3 (by rfl) ⟨132464, by rfl⟩ : syracuseStep 706477 = 264929) (by norm_num)
theorem B837557 : Blo 370760 837557 := bbase (se 5 (by rfl) ⟨39260, by rfl⟩ : syracuseStep 837557 = 78521) (by norm_num)
theorem B1886165 : Blo 370760 1886165 := bbase (se 7 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 1886165 = 44207) (by norm_num)
theorem B837629 : Blo 370760 837629 := bbase (se 3 (by rfl) ⟨157055, by rfl⟩ : syracuseStep 837629 = 314111) (by norm_num)
theorem B1263653 : Blo 370760 1263653 := bbase (se 4 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 1263653 = 236935) (by norm_num)
theorem B837701 : Blo 370760 837701 := bbase (se 4 (by rfl) ⟨78534, by rfl⟩ : syracuseStep 837701 = 157069) (by norm_num)
theorem B706637 : Blo 370760 706637 := bbase (se 3 (by rfl) ⟨132494, by rfl⟩ : syracuseStep 706637 = 264989) (by norm_num)
theorem B1427557 : Blo 370760 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B837773 : Blo 370760 837773 := bbase (se 3 (by rfl) ⟨157082, by rfl⟩ : syracuseStep 837773 = 314165) (by norm_num)
theorem B673933 : Blo 370760 673933 := bbase (se 3 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 673933 = 252725) (by norm_num)
theorem B837845 : Blo 370760 837845 := bbase (se 7 (by rfl) ⟨9818, by rfl⟩ : syracuseStep 837845 = 19637) (by norm_num)
theorem B706781 : Blo 370760 706781 := bbase (se 3 (by rfl) ⟨132521, by rfl⟩ : syracuseStep 706781 = 265043) (by norm_num)
theorem B837917 : Blo 370760 837917 := bbase (se 3 (by rfl) ⟨157109, by rfl⟩ : syracuseStep 837917 = 314219) (by norm_num)
theorem B674077 : Blo 370760 674077 := bbase (se 3 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 674077 = 252779) (by norm_num)
theorem B1591589 : Blo 370760 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B379225 : Blo 370760 379225 := bbase (se 2 (by rfl) ⟨142209, by rfl⟩ : syracuseStep 379225 = 284419) (by norm_num)
theorem B837989 : Blo 370760 837989 := bbase (se 4 (by rfl) ⟨78561, by rfl⟩ : syracuseStep 837989 = 157123) (by norm_num)
theorem B838061 : Blo 370760 838061 := bbase (se 3 (by rfl) ⟨157136, by rfl⟩ : syracuseStep 838061 = 314273) (by norm_num)
theorem B1264085 : Blo 370760 1264085 := bbase (se 7 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 1264085 = 29627) (by norm_num)
theorem B838133 : Blo 370760 838133 := bbase (se 5 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 838133 = 78575) (by norm_num)
theorem B707069 : Blo 370760 707069 := bbase (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) (by norm_num)
theorem B2378261 : Blo 370760 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B1198613 : Blo 370760 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B838205 : Blo 370760 838205 := bbase (se 3 (by rfl) ⟨157163, by rfl⟩ : syracuseStep 838205 = 314327) (by norm_num)
theorem B838277 : Blo 370760 838277 := bbase (se 4 (by rfl) ⟨78588, by rfl⟩ : syracuseStep 838277 = 157177) (by norm_num)
theorem B707221 : Blo 370760 707221 := bbase (se 6 (by rfl) ⟨16575, by rfl⟩ : syracuseStep 707221 = 33151) (by norm_num)
theorem B838349 : Blo 370760 838349 := bbase (se 3 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 838349 = 314381) (by norm_num)
theorem B674509 : Blo 370760 674509 := bbase (se 3 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 674509 = 252941) (by norm_num)
theorem B838421 : Blo 370760 838421 := bbase (se 6 (by rfl) ⟨19650, by rfl⟩ : syracuseStep 838421 = 39301) (by norm_num)
theorem B838493 : Blo 370760 838493 := bbase (se 3 (by rfl) ⟨157217, by rfl⟩ : syracuseStep 838493 = 314435) (by norm_num)
theorem B2116469 : Blo 370760 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B1264517 : Blo 370760 1264517 := bbase (se 4 (by rfl) ⟨118548, by rfl⟩ : syracuseStep 1264517 = 237097) (by norm_num)
theorem B838565 : Blo 370760 838565 := bbase (se 4 (by rfl) ⟨78615, by rfl⟩ : syracuseStep 838565 = 157231) (by norm_num)
theorem B707525 : Blo 370760 707525 := bbase (se 4 (by rfl) ⟨66330, by rfl⟩ : syracuseStep 707525 = 132661) (by norm_num)
theorem B838637 : Blo 370760 838637 := bbase (se 3 (by rfl) ⟨157244, by rfl⟩ : syracuseStep 838637 = 314489) (by norm_num)
theorem B674797 : Blo 370760 674797 := bbase (se 3 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 674797 = 253049) (by norm_num)
theorem B838709 : Blo 370760 838709 := bbase (se 5 (by rfl) ⟨39314, by rfl⟩ : syracuseStep 838709 = 78629) (by norm_num)
theorem B478325 : Blo 370760 478325 := bbase (se 5 (by rfl) ⟨22421, by rfl⟩ : syracuseStep 478325 = 44843) (by norm_num)
theorem B838781 : Blo 370760 838781 := bbase (se 3 (by rfl) ⟨157271, by rfl⟩ : syracuseStep 838781 = 314543) (by norm_num)
theorem B1428629 : Blo 370760 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B838853 : Blo 370760 838853 := bbase (se 4 (by rfl) ⟨78642, by rfl⟩ : syracuseStep 838853 = 157285) (by norm_num)
theorem B1887461 : Blo 370760 1887461 := bbase (se 4 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 1887461 = 353899) (by norm_num)
theorem B1592581 : Blo 370760 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B838925 : Blo 370760 838925 := bbase (se 3 (by rfl) ⟨157298, by rfl⟩ : syracuseStep 838925 = 314597) (by norm_num)
theorem B838997 : Blo 370760 838997 := bbase (se 11 (by rfl) ⟨614, by rfl⟩ : syracuseStep 838997 = 1229) (by norm_num)
theorem B839069 : Blo 370760 839069 := bbase (se 3 (by rfl) ⟨157325, by rfl⟩ : syracuseStep 839069 = 314651) (by norm_num)
theorem B839141 : Blo 370760 839141 := bbase (se 4 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 839141 = 157339) (by norm_num)
theorem B675317 : Blo 370760 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B1789445 : Blo 370760 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B1134101 : Blo 370760 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B839213 : Blo 370760 839213 := bbase (se 3 (by rfl) ⟨157352, by rfl⟩ : syracuseStep 839213 = 314705) (by norm_num)
theorem B839285 : Blo 370760 839285 := bbase (se 5 (by rfl) ⟨39341, by rfl⟩ : syracuseStep 839285 = 78683) (by norm_num)
theorem B708277 : Blo 370760 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B839357 : Blo 370760 839357 := bbase (se 3 (by rfl) ⟨157379, by rfl⟩ : syracuseStep 839357 = 314759) (by norm_num)
theorem B839429 : Blo 370760 839429 := bbase (se 4 (by rfl) ⟨78696, by rfl⟩ : syracuseStep 839429 = 157393) (by norm_num)
theorem B708421 : Blo 370760 708421 := bbase (se 4 (by rfl) ⟨66414, by rfl⟩ : syracuseStep 708421 = 132829) (by norm_num)
theorem B839501 : Blo 370760 839501 := bbase (se 3 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 839501 = 314813) (by norm_num)
theorem B839573 : Blo 370760 839573 := bbase (se 6 (by rfl) ⟨19677, by rfl⟩ : syracuseStep 839573 = 39355) (by norm_num)
theorem B839645 : Blo 370760 839645 := bbase (se 3 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 839645 = 314867) (by norm_num)
theorem B708581 : Blo 370760 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B839717 : Blo 370760 839717 := bbase (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) (by norm_num)
theorem B839789 : Blo 370760 839789 := bbase (se 3 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 839789 = 314921) (by norm_num)
theorem B708725 : Blo 370760 708725 := bbase (se 5 (by rfl) ⟨33221, by rfl⟩ : syracuseStep 708725 = 66443) (by norm_num)
theorem B839861 : Blo 370760 839861 := bbase (se 5 (by rfl) ⟨39368, by rfl⟩ : syracuseStep 839861 = 78737) (by norm_num)
theorem B446693 : Blo 370760 446693 := bbase (se 4 (by rfl) ⟨41877, by rfl⟩ : syracuseStep 446693 = 83755) (by norm_num)
theorem B839933 : Blo 370760 839933 := bbase (se 3 (by rfl) ⟨157487, by rfl⟩ : syracuseStep 839933 = 314975) (by norm_num)
theorem B3232021 : Blo 370760 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B446789 : Blo 370760 446789 := bbase (se 4 (by rfl) ⟨41886, by rfl⟩ : syracuseStep 446789 = 83773) (by norm_num)
theorem B840005 : Blo 370760 840005 := bbase (se 4 (by rfl) ⟨78750, by rfl⟩ : syracuseStep 840005 = 157501) (by norm_num)
theorem B446809 : Blo 370760 446809 := bbase (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) (by norm_num)
theorem B840077 : Blo 370760 840077 := bbase (se 3 (by rfl) ⟨157514, by rfl⟩ : syracuseStep 840077 = 315029) (by norm_num)
theorem B709013 : Blo 370760 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B840149 : Blo 370760 840149 := bbase (se 7 (by rfl) ⟨9845, by rfl⟩ : syracuseStep 840149 = 19691) (by norm_num)
theorem B3199445 : Blo 370760 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B446953 : Blo 370760 446953 := bbase (se 2 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 446953 = 335215) (by norm_num)
theorem B1888757 : Blo 370760 1888757 := bbase (se 5 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 1888757 = 177071) (by norm_num)
theorem B840221 : Blo 370760 840221 := bbase (se 3 (by rfl) ⟨157541, by rfl⟩ : syracuseStep 840221 = 315083) (by norm_num)
theorem B709165 : Blo 370760 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B840293 : Blo 370760 840293 := bbase (se 4 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 840293 = 157555) (by norm_num)
theorem B840365 : Blo 370760 840365 := bbase (se 3 (by rfl) ⟨157568, by rfl⟩ : syracuseStep 840365 = 315137) (by norm_num)
theorem B1790693 : Blo 370760 1790693 := bbase (se 4 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 1790693 = 335755) (by norm_num)
theorem B840437 : Blo 370760 840437 := bbase (se 5 (by rfl) ⟨39395, by rfl⟩ : syracuseStep 840437 = 78791) (by norm_num)
theorem B938749 : Blo 370760 938749 := bbase (se 3 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 938749 = 352031) (by norm_num)
theorem B840509 : Blo 370760 840509 := bbase (se 3 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 840509 = 315191) (by norm_num)
theorem B709469 : Blo 370760 709469 := bbase (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) (by norm_num)
theorem B938861 : Blo 370760 938861 := bbase (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) (by norm_num)
theorem B840581 : Blo 370760 840581 := bbase (se 4 (by rfl) ⟨78804, by rfl⟩ : syracuseStep 840581 = 157609) (by norm_num)
theorem B840653 : Blo 370760 840653 := bbase (se 3 (by rfl) ⟨157622, by rfl⟩ : syracuseStep 840653 = 315245) (by norm_num)
theorem B840725 : Blo 370760 840725 := bbase (se 6 (by rfl) ⟨19704, by rfl⟩ : syracuseStep 840725 = 39409) (by norm_num)
theorem B939053 : Blo 370760 939053 := bbase (se 3 (by rfl) ⟨176072, by rfl⟩ : syracuseStep 939053 = 352145) (by norm_num)
theorem B840797 : Blo 370760 840797 := bbase (se 3 (by rfl) ⟨157649, by rfl⟩ : syracuseStep 840797 = 315299) (by norm_num)
theorem B840869 : Blo 370760 840869 := bbase (se 4 (by rfl) ⟨78831, by rfl⟩ : syracuseStep 840869 = 157663) (by norm_num)
theorem B840941 : Blo 370760 840941 := bbase (se 3 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 840941 = 315353) (by norm_num)
theorem B4510997 : Blo 370760 4510997 := bbase (se 6 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 4510997 = 211453) (by norm_num)
theorem B841013 : Blo 370760 841013 := bbase (se 5 (by rfl) ⟨39422, by rfl⟩ : syracuseStep 841013 = 78845) (by norm_num)
theorem B841085 : Blo 370760 841085 := bbase (se 3 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 841085 = 315407) (by norm_num)
theorem B939397 : Blo 370760 939397 := bbase (se 4 (by rfl) ⟨88068, by rfl⟩ : syracuseStep 939397 = 176137) (by norm_num)
theorem B841157 : Blo 370760 841157 := bbase (se 4 (by rfl) ⟨78858, by rfl⟩ : syracuseStep 841157 = 157717) (by norm_num)
theorem B939509 : Blo 370760 939509 := bbase (se 5 (by rfl) ⟨44039, by rfl⟩ : syracuseStep 939509 = 88079) (by norm_num)
theorem B1136117 : Blo 370760 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B841229 : Blo 370760 841229 := bbase (se 3 (by rfl) ⟨157730, by rfl⟩ : syracuseStep 841229 = 315461) (by norm_num)
theorem B710221 : Blo 370760 710221 := bbase (se 3 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 710221 = 266333) (by norm_num)
theorem B841301 : Blo 370760 841301 := bbase (se 8 (by rfl) ⟨4929, by rfl⟩ : syracuseStep 841301 = 9859) (by norm_num)
theorem B1070725 : Blo 370760 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B841373 : Blo 370760 841373 := bbase (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) (by norm_num)
theorem B939701 : Blo 370760 939701 := bbase (se 5 (by rfl) ⟨44048, by rfl⟩ : syracuseStep 939701 = 88097) (by norm_num)
theorem B710365 : Blo 370760 710365 := bbase (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) (by norm_num)
theorem B841445 : Blo 370760 841445 := bbase (se 4 (by rfl) ⟨78885, by rfl⟩ : syracuseStep 841445 = 157771) (by norm_num)
theorem B1890053 : Blo 370760 1890053 := bbase (se 4 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 1890053 = 354385) (by norm_num)
theorem B841517 : Blo 370760 841517 := bbase (se 3 (by rfl) ⟨157784, by rfl⟩ : syracuseStep 841517 = 315569) (by norm_num)
theorem B841589 : Blo 370760 841589 := bbase (se 5 (by rfl) ⟨39449, by rfl⟩ : syracuseStep 841589 = 78899) (by norm_num)
theorem B710525 : Blo 370760 710525 := bbase (se 3 (by rfl) ⟨133223, by rfl⟩ : syracuseStep 710525 = 266447) (by norm_num)
theorem B6805397 : Blo 370760 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B841661 : Blo 370760 841661 := bbase (se 3 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 841661 = 315623) (by norm_num)
theorem B1366021 : Blo 370760 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B841733 : Blo 370760 841733 := bbase (se 4 (by rfl) ⟨78912, by rfl⟩ : syracuseStep 841733 = 157825) (by norm_num)
theorem B940045 : Blo 370760 940045 := bbase (se 3 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 940045 = 352517) (by norm_num)
theorem B710669 : Blo 370760 710669 := bbase (se 3 (by rfl) ⟨133250, by rfl⟩ : syracuseStep 710669 = 266501) (by norm_num)
theorem B841805 : Blo 370760 841805 := bbase (se 3 (by rfl) ⟨157838, by rfl⟩ : syracuseStep 841805 = 315677) (by norm_num)
theorem B940157 : Blo 370760 940157 := bbase (se 3 (by rfl) ⟨176279, by rfl⟩ : syracuseStep 940157 = 352559) (by norm_num)
theorem B841877 : Blo 370760 841877 := bbase (se 6 (by rfl) ⟨19731, by rfl⟩ : syracuseStep 841877 = 39463) (by norm_num)
theorem B3037333 : Blo 370760 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B841949 : Blo 370760 841949 := bbase (se 3 (by rfl) ⟨157865, by rfl⟩ : syracuseStep 841949 = 315731) (by norm_num)
theorem B448745 : Blo 370760 448745 := bbase (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) (by norm_num)
theorem B612613 : Blo 370760 612613 := bbase (se 4 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 612613 = 114865) (by norm_num)
theorem B842021 : Blo 370760 842021 := bbase (se 4 (by rfl) ⟨78939, by rfl⟩ : syracuseStep 842021 = 157879) (by norm_num)
theorem B710957 : Blo 370760 710957 := bbase (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) (by norm_num)
theorem B940349 : Blo 370760 940349 := bbase (se 3 (by rfl) ⟨176315, by rfl⟩ : syracuseStep 940349 = 352631) (by norm_num)
theorem B842093 : Blo 370760 842093 := bbase (se 3 (by rfl) ⟨157892, by rfl⟩ : syracuseStep 842093 = 315785) (by norm_num)
theorem B1431989 : Blo 370760 1431989 := bbase (se 5 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 1431989 = 134249) (by norm_num)
theorem B842165 : Blo 370760 842165 := bbase (se 5 (by rfl) ⟨39476, by rfl⟩ : syracuseStep 842165 = 78953) (by norm_num)
theorem B711109 : Blo 370760 711109 := bbase (se 4 (by rfl) ⟨66666, by rfl⟩ : syracuseStep 711109 = 133333) (by norm_num)
theorem B4250069 : Blo 370760 4250069 := bbase (se 7 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 4250069 = 99611) (by norm_num)
theorem B842237 : Blo 370760 842237 := bbase (se 3 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 842237 = 315839) (by norm_num)
theorem B449077 : Blo 370760 449077 := bbase (se 5 (by rfl) ⟨21050, by rfl⟩ : syracuseStep 449077 = 42101) (by norm_num)
theorem B842309 : Blo 370760 842309 := bbase (se 4 (by rfl) ⟨78966, by rfl⟩ : syracuseStep 842309 = 157933) (by norm_num)
theorem B2677333 : Blo 370760 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B842381 : Blo 370760 842381 := bbase (se 3 (by rfl) ⟨157946, by rfl⟩ : syracuseStep 842381 = 315893) (by norm_num)
theorem B940693 : Blo 370760 940693 := bbase (se 6 (by rfl) ⟨22047, by rfl⟩ : syracuseStep 940693 = 44095) (by norm_num)
theorem B449221 : Blo 370760 449221 := bbase (se 4 (by rfl) ⟨42114, by rfl⟩ : syracuseStep 449221 = 84229) (by norm_num)
theorem B842453 : Blo 370760 842453 := bbase (se 7 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 842453 = 19745) (by norm_num)
theorem B711413 : Blo 370760 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B940805 : Blo 370760 940805 := bbase (se 4 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 940805 = 176401) (by norm_num)
theorem B842525 : Blo 370760 842525 := bbase (se 3 (by rfl) ⟨157973, by rfl⟩ : syracuseStep 842525 = 315947) (by norm_num)
theorem B2087765 : Blo 370760 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B842597 : Blo 370760 842597 := bbase (se 4 (by rfl) ⟨78993, by rfl⟩ : syracuseStep 842597 = 157987) (by norm_num)
theorem B842669 : Blo 370760 842669 := bbase (se 3 (by rfl) ⟨158000, by rfl⟩ : syracuseStep 842669 = 316001) (by norm_num)
theorem B3169205 : Blo 370760 3169205 := bbase (se 5 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 3169205 = 297113) (by norm_num)
theorem B940997 : Blo 370760 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B842741 : Blo 370760 842741 := bbase (se 5 (by rfl) ⟨39503, by rfl⟩ : syracuseStep 842741 = 79007) (by norm_num)
theorem B1891349 : Blo 370760 1891349 := bbase (se 6 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 1891349 = 88657) (by norm_num)
theorem B842813 : Blo 370760 842813 := bbase (se 3 (by rfl) ⟨158027, by rfl⟩ : syracuseStep 842813 = 316055) (by norm_num)
theorem B842885 : Blo 370760 842885 := bbase (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) (by norm_num)
theorem B842957 : Blo 370760 842957 := bbase (se 3 (by rfl) ⟨158054, by rfl⟩ : syracuseStep 842957 = 316109) (by norm_num)
theorem B1137941 : Blo 370760 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B843029 : Blo 370760 843029 := bbase (se 6 (by rfl) ⟨19758, by rfl⟩ : syracuseStep 843029 = 39517) (by norm_num)
theorem B941341 : Blo 370760 941341 := bbase (se 3 (by rfl) ⟨176501, by rfl⟩ : syracuseStep 941341 = 353003) (by norm_num)
theorem B417109 : Blo 370760 417109 := bbase (se 11 (by rfl) ⟨305, by rfl⟩ : syracuseStep 417109 = 611) (by norm_num)
theorem B843101 : Blo 370760 843101 := bbase (se 3 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 843101 = 316163) (by norm_num)
theorem B417145 : Blo 370760 417145 := bbase (se 2 (by rfl) ⟨156429, by rfl⟩ : syracuseStep 417145 = 312859) (by norm_num)
theorem B941453 : Blo 370760 941453 := bbase (se 3 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 941453 = 353045) (by norm_num)
theorem B417181 : Blo 370760 417181 := bbase (se 3 (by rfl) ⟨78221, by rfl⟩ : syracuseStep 417181 = 156443) (by norm_num)
theorem B843173 : Blo 370760 843173 := bbase (se 4 (by rfl) ⟨79047, by rfl⟩ : syracuseStep 843173 = 158095) (by norm_num)
theorem B1793461 : Blo 370760 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B417217 : Blo 370760 417217 := bbase (se 2 (by rfl) ⟨156456, by rfl⟩ : syracuseStep 417217 = 312913) (by norm_num)
theorem B417253 : Blo 370760 417253 := bbase (se 4 (by rfl) ⟨39117, by rfl⟩ : syracuseStep 417253 = 78235) (by norm_num)
theorem B417289 : Blo 370760 417289 := bbase (se 2 (by rfl) ⟨156483, by rfl⟩ : syracuseStep 417289 = 312967) (by norm_num)
theorem B908813 : Blo 370760 908813 := bbase (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) (by norm_num)
theorem B417325 : Blo 370760 417325 := bbase (se 3 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 417325 = 156497) (by norm_num)
theorem B941645 : Blo 370760 941645 := bbase (se 3 (by rfl) ⟨176558, by rfl⟩ : syracuseStep 941645 = 353117) (by norm_num)
theorem B417361 : Blo 370760 417361 := bbase (se 2 (by rfl) ⟨156510, by rfl⟩ : syracuseStep 417361 = 313021) (by norm_num)
theorem B417397 : Blo 370760 417397 := bbase (se 5 (by rfl) ⟨19565, by rfl⟩ : syracuseStep 417397 = 39131) (by norm_num)
theorem B417433 : Blo 370760 417433 := bbase (se 2 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 417433 = 313075) (by norm_num)
theorem B417469 : Blo 370760 417469 := bbase (se 3 (by rfl) ⟨78275, by rfl⟩ : syracuseStep 417469 = 156551) (by norm_num)
theorem B417505 : Blo 370760 417505 := bbase (se 2 (by rfl) ⟨156564, by rfl⟩ : syracuseStep 417505 = 313129) (by norm_num)
theorem B417541 : Blo 370760 417541 := bbase (se 4 (by rfl) ⟨39144, by rfl⟩ : syracuseStep 417541 = 78289) (by norm_num)
theorem B417577 : Blo 370760 417577 := bbase (se 2 (by rfl) ⟨156591, by rfl⟩ : syracuseStep 417577 = 313183) (by norm_num)
theorem B417613 : Blo 370760 417613 := bbase (se 3 (by rfl) ⟨78302, by rfl⟩ : syracuseStep 417613 = 156605) (by norm_num)
theorem B417649 : Blo 370760 417649 := bbase (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) (by norm_num)
theorem B417685 : Blo 370760 417685 := bbase (se 6 (by rfl) ⟨9789, by rfl⟩ : syracuseStep 417685 = 19579) (by norm_num)
theorem B941989 : Blo 370760 941989 := bbase (se 4 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 941989 = 176623) (by norm_num)
theorem B417721 : Blo 370760 417721 := bbase (se 2 (by rfl) ⟨156645, by rfl⟩ : syracuseStep 417721 = 313291) (by norm_num)
theorem B417757 : Blo 370760 417757 := bbase (se 3 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 417757 = 156659) (by norm_num)
theorem B2842613 : Blo 370760 2842613 := bbase (se 5 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 2842613 = 266495) (by norm_num)
theorem B417793 : Blo 370760 417793 := bbase (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) (by norm_num)
theorem B942101 : Blo 370760 942101 := bbase (se 6 (by rfl) ⟨22080, by rfl⟩ : syracuseStep 942101 = 44161) (by norm_num)
theorem B417829 : Blo 370760 417829 := bbase (se 4 (by rfl) ⟨39171, by rfl⟩ : syracuseStep 417829 = 78343) (by norm_num)
theorem B417865 : Blo 370760 417865 := bbase (se 2 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 417865 = 313399) (by norm_num)
theorem B417901 : Blo 370760 417901 := bbase (se 3 (by rfl) ⟨78356, by rfl⟩ : syracuseStep 417901 = 156713) (by norm_num)
theorem B417937 : Blo 370760 417937 := bbase (se 2 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 417937 = 313453) (by norm_num)
theorem B1597589 : Blo 370760 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B417973 : Blo 370760 417973 := bbase (se 5 (by rfl) ⟨19592, by rfl⟩ : syracuseStep 417973 = 39185) (by norm_num)
theorem B942293 : Blo 370760 942293 := bbase (se 7 (by rfl) ⟨11042, by rfl⟩ : syracuseStep 942293 = 22085) (by norm_num)
theorem B418009 : Blo 370760 418009 := bbase (se 2 (by rfl) ⟨156753, by rfl⟩ : syracuseStep 418009 = 313507) (by norm_num)
theorem B418045 : Blo 370760 418045 := bbase (se 3 (by rfl) ⟨78383, by rfl⟩ : syracuseStep 418045 = 156767) (by norm_num)
theorem B1073413 : Blo 370760 1073413 := bbase (se 4 (by rfl) ⟨100632, by rfl⟩ : syracuseStep 1073413 = 201265) (by norm_num)
theorem B418081 : Blo 370760 418081 := bbase (se 2 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 418081 = 313561) (by norm_num)
theorem B1892645 : Blo 370760 1892645 := bbase (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) (by norm_num)
theorem B418117 : Blo 370760 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B483685 : Blo 370760 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B680293 : Blo 370760 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B418153 : Blo 370760 418153 := bbase (se 2 (by rfl) ⟨156807, by rfl⟩ : syracuseStep 418153 = 313615) (by norm_num)
theorem B418189 : Blo 370760 418189 := bbase (se 3 (by rfl) ⟨78410, by rfl⟩ : syracuseStep 418189 = 156821) (by norm_num)
theorem B418225 : Blo 370760 418225 := bbase (se 2 (by rfl) ⟨156834, by rfl⟩ : syracuseStep 418225 = 313669) (by norm_num)
theorem B2384309 : Blo 370760 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B1597877 : Blo 370760 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B418261 : Blo 370760 418261 := bbase (se 7 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 418261 = 9803) (by norm_num)
theorem B418297 : Blo 370760 418297 := bbase (se 2 (by rfl) ⟨156861, by rfl⟩ : syracuseStep 418297 = 313723) (by norm_num)
theorem B418333 : Blo 370760 418333 := bbase (se 3 (by rfl) ⟨78437, by rfl⟩ : syracuseStep 418333 = 156875) (by norm_num)
theorem B942637 : Blo 370760 942637 := bbase (se 3 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 942637 = 353489) (by norm_num)
theorem B418369 : Blo 370760 418369 := bbase (se 2 (by rfl) ⟨156888, by rfl⟩ : syracuseStep 418369 = 313777) (by norm_num)
theorem B418405 : Blo 370760 418405 := bbase (se 4 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 418405 = 78451) (by norm_num)
theorem B418441 : Blo 370760 418441 := bbase (se 2 (by rfl) ⟨156915, by rfl⟩ : syracuseStep 418441 = 313831) (by norm_num)
theorem B942749 : Blo 370760 942749 := bbase (se 3 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 942749 = 353531) (by norm_num)
theorem B418477 : Blo 370760 418477 := bbase (se 3 (by rfl) ⟨78464, by rfl⟩ : syracuseStep 418477 = 156929) (by norm_num)
theorem B418513 : Blo 370760 418513 := bbase (se 2 (by rfl) ⟨156942, by rfl⟩ : syracuseStep 418513 = 313885) (by norm_num)
theorem B418549 : Blo 370760 418549 := bbase (se 5 (by rfl) ⟨19619, by rfl⟩ : syracuseStep 418549 = 39239) (by norm_num)
theorem B418585 : Blo 370760 418585 := bbase (se 2 (by rfl) ⟨156969, by rfl⟩ : syracuseStep 418585 = 313939) (by norm_num)
theorem B418621 : Blo 370760 418621 := bbase (se 3 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 418621 = 156983) (by norm_num)
theorem B942941 : Blo 370760 942941 := bbase (se 3 (by rfl) ⟨176801, by rfl⟩ : syracuseStep 942941 = 353603) (by norm_num)
theorem B418657 : Blo 370760 418657 := bbase (se 2 (by rfl) ⟨156996, by rfl⟩ : syracuseStep 418657 = 313993) (by norm_num)
theorem B418693 : Blo 370760 418693 := bbase (se 4 (by rfl) ⟨39252, by rfl⟩ : syracuseStep 418693 = 78505) (by norm_num)
theorem B418729 : Blo 370760 418729 := bbase (se 2 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 418729 = 314047) (by norm_num)
theorem B418765 : Blo 370760 418765 := bbase (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) (by norm_num)
theorem B418801 : Blo 370760 418801 := bbase (se 2 (by rfl) ⟨157050, by rfl⟩ : syracuseStep 418801 = 314101) (by norm_num)
theorem B418837 : Blo 370760 418837 := bbase (se 6 (by rfl) ⟨9816, by rfl⟩ : syracuseStep 418837 = 19633) (by norm_num)
theorem B418873 : Blo 370760 418873 := bbase (se 2 (by rfl) ⟨157077, by rfl⟩ : syracuseStep 418873 = 314155) (by norm_num)
theorem B418909 : Blo 370760 418909 := bbase (se 3 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 418909 = 157091) (by norm_num)
theorem B418945 : Blo 370760 418945 := bbase (se 2 (by rfl) ⟨157104, by rfl⟩ : syracuseStep 418945 = 314209) (by norm_num)
theorem B418981 : Blo 370760 418981 := bbase (se 4 (by rfl) ⟨39279, by rfl⟩ : syracuseStep 418981 = 78559) (by norm_num)
theorem B1598629 : Blo 370760 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B943285 : Blo 370760 943285 := bbase (se 5 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 943285 = 88433) (by norm_num)
theorem B419017 : Blo 370760 419017 := bbase (se 2 (by rfl) ⟨157131, by rfl⟩ : syracuseStep 419017 = 314263) (by norm_num)
theorem B419053 : Blo 370760 419053 := bbase (se 3 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 419053 = 157145) (by norm_num)
theorem B419089 : Blo 370760 419089 := bbase (se 2 (by rfl) ⟨157158, by rfl⟩ : syracuseStep 419089 = 314317) (by norm_num)
theorem B943397 : Blo 370760 943397 := bbase (se 4 (by rfl) ⟨88443, by rfl⟩ : syracuseStep 943397 = 176887) (by norm_num)
theorem B419125 : Blo 370760 419125 := bbase (se 5 (by rfl) ⟨19646, by rfl⟩ : syracuseStep 419125 = 39293) (by norm_num)
theorem B2876725 : Blo 370760 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B419161 : Blo 370760 419161 := bbase (se 2 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 419161 = 314371) (by norm_num)
theorem B419197 : Blo 370760 419197 := bbase (se 3 (by rfl) ⟨78599, by rfl⟩ : syracuseStep 419197 = 157199) (by norm_num)
theorem B419233 : Blo 370760 419233 := bbase (se 2 (by rfl) ⟨157212, by rfl⟩ : syracuseStep 419233 = 314425) (by norm_num)
theorem B419269 : Blo 370760 419269 := bbase (se 4 (by rfl) ⟨39306, by rfl⟩ : syracuseStep 419269 = 78613) (by norm_num)
theorem B943589 : Blo 370760 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B419305 : Blo 370760 419305 := bbase (se 2 (by rfl) ⟨157239, by rfl⟩ : syracuseStep 419305 = 314479) (by norm_num)
theorem B419341 : Blo 370760 419341 := bbase (se 3 (by rfl) ⟨78626, by rfl⟩ : syracuseStep 419341 = 157253) (by norm_num)
theorem B419377 : Blo 370760 419377 := bbase (se 2 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 419377 = 314533) (by norm_num)
theorem B1893941 : Blo 370760 1893941 := bbase (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) (by norm_num)
theorem B419413 : Blo 370760 419413 := bbase (se 8 (by rfl) ⟨2457, by rfl⟩ : syracuseStep 419413 = 4915) (by norm_num)
theorem B419449 : Blo 370760 419449 := bbase (se 2 (by rfl) ⟨157293, by rfl⟩ : syracuseStep 419449 = 314587) (by norm_num)
theorem B419485 : Blo 370760 419485 := bbase (se 3 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 419485 = 157307) (by norm_num)
theorem B419521 : Blo 370760 419521 := bbase (se 2 (by rfl) ⟨157320, by rfl⟩ : syracuseStep 419521 = 314641) (by norm_num)
theorem B419557 : Blo 370760 419557 := bbase (se 4 (by rfl) ⟨39333, by rfl⟩ : syracuseStep 419557 = 78667) (by norm_num)
theorem B419593 : Blo 370760 419593 := bbase (se 2 (by rfl) ⟨157347, by rfl⟩ : syracuseStep 419593 = 314695) (by norm_num)
theorem B419629 : Blo 370760 419629 := bbase (se 3 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 419629 = 157361) (by norm_num)
theorem B943933 : Blo 370760 943933 := bbase (se 3 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 943933 = 353975) (by norm_num)
theorem B419665 : Blo 370760 419665 := bbase (se 2 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 419665 = 314749) (by norm_num)
theorem B419701 : Blo 370760 419701 := bbase (se 5 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 419701 = 39347) (by norm_num)
theorem B1599365 : Blo 370760 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B419737 : Blo 370760 419737 := bbase (se 2 (by rfl) ⟨157401, by rfl⟩ : syracuseStep 419737 = 314803) (by norm_num)
theorem B944045 : Blo 370760 944045 := bbase (se 3 (by rfl) ⟨177008, by rfl⟩ : syracuseStep 944045 = 354017) (by norm_num)
theorem B419773 : Blo 370760 419773 := bbase (se 3 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 419773 = 157415) (by norm_num)
theorem B419809 : Blo 370760 419809 := bbase (se 2 (by rfl) ⟨157428, by rfl⟩ : syracuseStep 419809 = 314857) (by norm_num)
theorem B419845 : Blo 370760 419845 := bbase (se 4 (by rfl) ⟨39360, by rfl⟩ : syracuseStep 419845 = 78721) (by norm_num)
theorem B419881 : Blo 370760 419881 := bbase (se 2 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 419881 = 314911) (by norm_num)
theorem B419917 : Blo 370760 419917 := bbase (se 3 (by rfl) ⟨78734, by rfl⟩ : syracuseStep 419917 = 157469) (by norm_num)
theorem B682069 : Blo 370760 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B944237 : Blo 370760 944237 := bbase (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) (by norm_num)
theorem B419953 : Blo 370760 419953 := bbase (se 2 (by rfl) ⟨157482, by rfl⟩ : syracuseStep 419953 = 314965) (by norm_num)
theorem B419989 : Blo 370760 419989 := bbase (se 6 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 419989 = 19687) (by norm_num)
theorem B420025 : Blo 370760 420025 := bbase (se 2 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 420025 = 315019) (by norm_num)
theorem B3565781 : Blo 370760 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B420061 : Blo 370760 420061 := bbase (se 3 (by rfl) ⟨78761, by rfl⟩ : syracuseStep 420061 = 157523) (by norm_num)
theorem B420097 : Blo 370760 420097 := bbase (se 2 (by rfl) ⟨157536, by rfl⟩ : syracuseStep 420097 = 315073) (by norm_num)
theorem B420133 : Blo 370760 420133 := bbase (se 4 (by rfl) ⟨39387, by rfl⟩ : syracuseStep 420133 = 78775) (by norm_num)
theorem B420169 : Blo 370760 420169 := bbase (se 2 (by rfl) ⟨157563, by rfl⟩ : syracuseStep 420169 = 315127) (by norm_num)
theorem B4811093 : Blo 370760 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B420205 : Blo 370760 420205 := bbase (se 3 (by rfl) ⟨78788, by rfl⟩ : syracuseStep 420205 = 157577) (by norm_num)
theorem B1272181 : Blo 370760 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B420241 : Blo 370760 420241 := bbase (se 2 (by rfl) ⟨157590, by rfl⟩ : syracuseStep 420241 = 315181) (by norm_num)
theorem B420277 : Blo 370760 420277 := bbase (se 5 (by rfl) ⟨19700, by rfl⟩ : syracuseStep 420277 = 39401) (by norm_num)
theorem B944581 : Blo 370760 944581 := bbase (se 4 (by rfl) ⟨88554, by rfl⟩ : syracuseStep 944581 = 177109) (by norm_num)
theorem B420313 : Blo 370760 420313 := bbase (se 2 (by rfl) ⟨157617, by rfl⟩ : syracuseStep 420313 = 315235) (by norm_num)
theorem B420349 : Blo 370760 420349 := bbase (se 3 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 420349 = 157631) (by norm_num)
theorem B420385 : Blo 370760 420385 := bbase (se 2 (by rfl) ⟨157644, by rfl⟩ : syracuseStep 420385 = 315289) (by norm_num)
theorem B944693 : Blo 370760 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B420421 : Blo 370760 420421 := bbase (se 4 (by rfl) ⟨39414, by rfl⟩ : syracuseStep 420421 = 78829) (by norm_num)
theorem B420457 : Blo 370760 420457 := bbase (se 2 (by rfl) ⟨157671, by rfl⟩ : syracuseStep 420457 = 315343) (by norm_num)
theorem B420493 : Blo 370760 420493 := bbase (se 3 (by rfl) ⟨78842, by rfl⟩ : syracuseStep 420493 = 157685) (by norm_num)
theorem B420529 : Blo 370760 420529 := bbase (se 2 (by rfl) ⟨157698, by rfl⟩ : syracuseStep 420529 = 315397) (by norm_num)
theorem B420565 : Blo 370760 420565 := bbase (se 7 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 420565 = 9857) (by norm_num)
theorem B715501 : Blo 370760 715501 := bbase (se 3 (by rfl) ⟨134156, by rfl⟩ : syracuseStep 715501 = 268313) (by norm_num)
theorem B944885 : Blo 370760 944885 := bbase (se 5 (by rfl) ⟨44291, by rfl⟩ : syracuseStep 944885 = 88583) (by norm_num)
theorem B420601 : Blo 370760 420601 := bbase (se 2 (by rfl) ⟨157725, by rfl⟩ : syracuseStep 420601 = 315451) (by norm_num)
theorem B420637 : Blo 370760 420637 := bbase (se 3 (by rfl) ⟨78869, by rfl⟩ : syracuseStep 420637 = 157739) (by norm_num)
theorem B420673 : Blo 370760 420673 := bbase (se 2 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 420673 = 315505) (by norm_num)
theorem B1895237 : Blo 370760 1895237 := bbase (se 4 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 1895237 = 355357) (by norm_num)
theorem B420709 : Blo 370760 420709 := bbase (se 4 (by rfl) ⟨39441, by rfl⟩ : syracuseStep 420709 = 78883) (by norm_num)
theorem B420745 : Blo 370760 420745 := bbase (se 2 (by rfl) ⟨157779, by rfl⟩ : syracuseStep 420745 = 315559) (by norm_num)
theorem B420781 : Blo 370760 420781 := bbase (se 3 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 420781 = 157793) (by norm_num)
theorem B420817 : Blo 370760 420817 := bbase (se 2 (by rfl) ⟨157806, by rfl⟩ : syracuseStep 420817 = 315613) (by norm_num)
theorem B420853 : Blo 370760 420853 := bbase (se 5 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 420853 = 39455) (by norm_num)
theorem B2419733 : Blo 370760 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B1534997 : Blo 370760 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B420889 : Blo 370760 420889 := bbase (se 2 (by rfl) ⟨157833, by rfl⟩ : syracuseStep 420889 = 315667) (by norm_num)
theorem B420925 : Blo 370760 420925 := bbase (se 3 (by rfl) ⟨78923, by rfl⟩ : syracuseStep 420925 = 157847) (by norm_num)
theorem B1338437 : Blo 370760 1338437 := bbase (se 4 (by rfl) ⟨125478, by rfl⟩ : syracuseStep 1338437 = 250957) (by norm_num)
theorem B945229 : Blo 370760 945229 := bbase (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) (by norm_num)
theorem B420961 : Blo 370760 420961 := bbase (se 2 (by rfl) ⟨157860, by rfl⟩ : syracuseStep 420961 = 315721) (by norm_num)
theorem B420997 : Blo 370760 420997 := bbase (se 4 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 420997 = 78937) (by norm_num)
theorem B421033 : Blo 370760 421033 := bbase (se 2 (by rfl) ⟨157887, by rfl⟩ : syracuseStep 421033 = 315775) (by norm_num)
theorem B945341 : Blo 370760 945341 := bbase (se 3 (by rfl) ⟨177251, by rfl⟩ : syracuseStep 945341 = 354503) (by norm_num)
theorem B421069 : Blo 370760 421069 := bbase (se 3 (by rfl) ⟨78950, by rfl⟩ : syracuseStep 421069 = 157901) (by norm_num)
theorem B1338581 : Blo 370760 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B421105 : Blo 370760 421105 := bbase (se 2 (by rfl) ⟨157914, by rfl⟩ : syracuseStep 421105 = 315829) (by norm_num)
theorem B421141 : Blo 370760 421141 := bbase (se 6 (by rfl) ⟨9870, by rfl⟩ : syracuseStep 421141 = 19741) (by norm_num)
theorem B421177 : Blo 370760 421177 := bbase (se 2 (by rfl) ⟨157941, by rfl⟩ : syracuseStep 421177 = 315883) (by norm_num)
theorem B814429 : Blo 370760 814429 := bbase (se 3 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 814429 = 305411) (by norm_num)
theorem B421213 : Blo 370760 421213 := bbase (se 3 (by rfl) ⟨78977, by rfl⟩ : syracuseStep 421213 = 157955) (by norm_num)
theorem B945533 : Blo 370760 945533 := bbase (se 3 (by rfl) ⟨177287, by rfl⟩ : syracuseStep 945533 = 354575) (by norm_num)
theorem B421249 : Blo 370760 421249 := bbase (se 2 (by rfl) ⟨157968, by rfl⟩ : syracuseStep 421249 = 315937) (by norm_num)
theorem B1535365 : Blo 370760 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B716197 : Blo 370760 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B421285 : Blo 370760 421285 := bbase (se 4 (by rfl) ⟨39495, by rfl⟩ : syracuseStep 421285 = 78991) (by norm_num)
theorem B421321 : Blo 370760 421321 := bbase (se 2 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 421321 = 315991) (by norm_num)
theorem B454093 : Blo 370760 454093 := bbase (se 3 (by rfl) ⟨85142, by rfl⟩ : syracuseStep 454093 = 170285) (by norm_num)
theorem B421357 : Blo 370760 421357 := bbase (se 3 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 421357 = 158009) (by norm_num)
theorem B1338869 : Blo 370760 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B421393 : Blo 370760 421393 := bbase (se 2 (by rfl) ⟨158022, by rfl⟩ : syracuseStep 421393 = 316045) (by norm_num)
theorem B1797653 : Blo 370760 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B421429 : Blo 370760 421429 := bbase (se 5 (by rfl) ⟨19754, by rfl⟩ : syracuseStep 421429 = 39509) (by norm_num)
theorem B421465 : Blo 370760 421465 := bbase (se 2 (by rfl) ⟨158049, by rfl⟩ : syracuseStep 421465 = 316099) (by norm_num)
theorem B421501 : Blo 370760 421501 := bbase (se 3 (by rfl) ⟨79031, by rfl⟩ : syracuseStep 421501 = 158063) (by norm_num)
theorem B421537 : Blo 370760 421537 := bbase (se 2 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 421537 = 316153) (by norm_num)
theorem B421573 : Blo 370760 421573 := bbase (se 4 (by rfl) ⟨39522, by rfl⟩ : syracuseStep 421573 = 79045) (by norm_num)
theorem B945877 : Blo 370760 945877 := bbase (se 7 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 945877 = 22169) (by norm_num)
theorem B945989 : Blo 370760 945989 := bbase (se 4 (by rfl) ⟨88686, by rfl⟩ : syracuseStep 945989 = 177373) (by norm_num)
theorem B6123413 : Blo 370760 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B847829 : Blo 370760 847829 := bbase (se 7 (by rfl) ⟨9935, by rfl⟩ : syracuseStep 847829 = 19871) (by norm_num)
theorem B847837 : Blo 370760 847837 := bbase (se 3 (by rfl) ⟨158969, by rfl⟩ : syracuseStep 847837 = 317939) (by norm_num)
theorem B946181 : Blo 370760 946181 := bbase (se 4 (by rfl) ⟨88704, by rfl⟩ : syracuseStep 946181 = 177409) (by norm_num)
theorem B454717 : Blo 370760 454717 := bbase (se 3 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 454717 = 170519) (by norm_num)
theorem B1896533 : Blo 370760 1896533 := bbase (se 8 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 1896533 = 22225) (by norm_num)
theorem B2355317 : Blo 370760 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B389269 : Blo 370760 389269 := bbase (se 6 (by rfl) ⟨9123, by rfl⟩ : syracuseStep 389269 = 18247) (by norm_num)
theorem B946525 : Blo 370760 946525 := bbase (se 3 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 946525 = 354947) (by norm_num)
theorem B946637 : Blo 370760 946637 := bbase (se 3 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 946637 = 354989) (by norm_num)
theorem B2126357 : Blo 370760 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B946829 : Blo 370760 946829 := bbase (se 3 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 946829 = 355061) (by norm_num)
theorem B1077941 : Blo 370760 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B455429 : Blo 370760 455429 := bbase (se 4 (by rfl) ⟨42696, by rfl⟩ : syracuseStep 455429 = 85393) (by norm_num)
theorem B1504021 : Blo 370760 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B4027157 : Blo 370760 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B1143733 : Blo 370760 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B947173 : Blo 370760 947173 := bbase (se 4 (by rfl) ⟨88797, by rfl⟩ : syracuseStep 947173 = 177595) (by norm_num)
theorem B947285 : Blo 370760 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B1340597 : Blo 370760 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B947477 : Blo 370760 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B423517 : Blo 370760 423517 := bbase (se 3 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 423517 = 158819) (by norm_num)
theorem B947821 : Blo 370760 947821 := bbase (se 3 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 947821 = 355433) (by norm_num)
theorem B947933 : Blo 370760 947933 := bbase (se 3 (by rfl) ⟨177737, by rfl⟩ : syracuseStep 947933 = 355475) (by norm_num)
theorem B24180565 : Blo 370760 24180565 := bbase (se 9 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 24180565 = 141683) (by norm_num)
theorem B948125 : Blo 370760 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B948469 : Blo 370760 948469 := bbase (se 5 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 948469 = 88919) (by norm_num)
theorem B948581 : Blo 370760 948581 := bbase (se 4 (by rfl) ⟨88929, by rfl⟩ : syracuseStep 948581 = 177859) (by norm_num)
theorem B752141 : Blo 370760 752141 := bbase (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) (by norm_num)
theorem B490093 : Blo 370760 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B687109 : Blo 370760 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B556157 : Blo 370760 556157 := bbase (se 3 (by rfl) ⟨104279, by rfl⟩ : syracuseStep 556157 = 208559) (by norm_num)
theorem B556181 : Blo 370760 556181 := bbase (se 6 (by rfl) ⟨13035, by rfl⟩ : syracuseStep 556181 = 26071) (by norm_num)
theorem B752789 : Blo 370760 752789 := bbase (se 6 (by rfl) ⟨17643, by rfl⟩ : syracuseStep 752789 = 35287) (by norm_num)
theorem B556205 : Blo 370760 556205 := bbase (se 3 (by rfl) ⟨104288, by rfl⟩ : syracuseStep 556205 = 208577) (by norm_num)
theorem B1440949 : Blo 370760 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B556229 : Blo 370760 556229 := bbase (se 4 (by rfl) ⟨52146, by rfl⟩ : syracuseStep 556229 = 104293) (by norm_num)
theorem B556253 : Blo 370760 556253 := bbase (se 3 (by rfl) ⟨104297, by rfl⟩ : syracuseStep 556253 = 208595) (by norm_num)
theorem B556277 : Blo 370760 556277 := bbase (se 5 (by rfl) ⟨26075, by rfl⟩ : syracuseStep 556277 = 52151) (by norm_num)
theorem B556301 : Blo 370760 556301 := bbase (se 3 (by rfl) ⟨104306, by rfl⟩ : syracuseStep 556301 = 208613) (by norm_num)
theorem B556325 : Blo 370760 556325 := bbase (se 4 (by rfl) ⟨52155, by rfl⟩ : syracuseStep 556325 = 104311) (by norm_num)
theorem B425269 : Blo 370760 425269 := bbase (se 5 (by rfl) ⟨19934, by rfl⟩ : syracuseStep 425269 = 39869) (by norm_num)
theorem B556349 : Blo 370760 556349 := bbase (se 3 (by rfl) ⟨104315, by rfl⟩ : syracuseStep 556349 = 208631) (by norm_num)
theorem B556373 : Blo 370760 556373 := bbase (se 11 (by rfl) ⟨407, by rfl⟩ : syracuseStep 556373 = 815) (by norm_num)
theorem B556397 : Blo 370760 556397 := bbase (se 3 (by rfl) ⟨104324, by rfl⟩ : syracuseStep 556397 = 208649) (by norm_num)
theorem B2293109 : Blo 370760 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B556421 : Blo 370760 556421 := bbase (se 4 (by rfl) ⟨52164, by rfl⟩ : syracuseStep 556421 = 104329) (by norm_num)
theorem B556445 : Blo 370760 556445 := bbase (se 3 (by rfl) ⟨104333, by rfl⟩ : syracuseStep 556445 = 208667) (by norm_num)
theorem B556469 : Blo 370760 556469 := bbase (se 5 (by rfl) ⟨26084, by rfl⟩ : syracuseStep 556469 = 52169) (by norm_num)
theorem B556493 : Blo 370760 556493 := bbase (se 3 (by rfl) ⟨104342, by rfl⟩ : syracuseStep 556493 = 208685) (by norm_num)
theorem B425425 : Blo 370760 425425 := bbase (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) (by norm_num)
theorem B556517 : Blo 370760 556517 := bbase (se 4 (by rfl) ⟨52173, by rfl⟩ : syracuseStep 556517 = 104347) (by norm_num)
theorem B556541 : Blo 370760 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B556565 : Blo 370760 556565 := bbase (se 6 (by rfl) ⟨13044, by rfl⟩ : syracuseStep 556565 = 26089) (by norm_num)
theorem B1408549 : Blo 370760 1408549 := bbase (se 4 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 1408549 = 264103) (by norm_num)
theorem B556589 : Blo 370760 556589 := bbase (se 3 (by rfl) ⟨104360, by rfl⟩ : syracuseStep 556589 = 208721) (by norm_num)
theorem B556613 : Blo 370760 556613 := bbase (se 4 (by rfl) ⟨52182, by rfl⟩ : syracuseStep 556613 = 104365) (by norm_num)
theorem B556637 : Blo 370760 556637 := bbase (se 3 (by rfl) ⟨104369, by rfl⟩ : syracuseStep 556637 = 208739) (by norm_num)
theorem B556661 : Blo 370760 556661 := bbase (se 5 (by rfl) ⟨26093, by rfl⟩ : syracuseStep 556661 = 52187) (by norm_num)
theorem B556685 : Blo 370760 556685 := bbase (se 3 (by rfl) ⟨104378, by rfl⟩ : syracuseStep 556685 = 208757) (by norm_num)
theorem B556709 : Blo 370760 556709 := bbase (se 4 (by rfl) ⟨52191, by rfl⟩ : syracuseStep 556709 = 104383) (by norm_num)
theorem B556733 : Blo 370760 556733 := bbase (se 3 (by rfl) ⟨104387, by rfl⟩ : syracuseStep 556733 = 208775) (by norm_num)
theorem B556757 : Blo 370760 556757 := bbase (se 7 (by rfl) ⟨6524, by rfl⟩ : syracuseStep 556757 = 13049) (by norm_num)
theorem B556781 : Blo 370760 556781 := bbase (se 3 (by rfl) ⟨104396, by rfl⟩ : syracuseStep 556781 = 208793) (by norm_num)
theorem B556805 : Blo 370760 556805 := bbase (se 4 (by rfl) ⟨52200, by rfl⟩ : syracuseStep 556805 = 104401) (by norm_num)
theorem B556829 : Blo 370760 556829 := bbase (se 3 (by rfl) ⟨104405, by rfl⟩ : syracuseStep 556829 = 208811) (by norm_num)
theorem B556853 : Blo 370760 556853 := bbase (se 5 (by rfl) ⟨26102, by rfl⟩ : syracuseStep 556853 = 52205) (by norm_num)
theorem B556877 : Blo 370760 556877 := bbase (se 3 (by rfl) ⟨104414, by rfl⟩ : syracuseStep 556877 = 208829) (by norm_num)
theorem B3211093 : Blo 370760 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1408853 : Blo 370760 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B556901 : Blo 370760 556901 := bbase (se 4 (by rfl) ⟨52209, by rfl⟩ : syracuseStep 556901 = 104419) (by norm_num)
theorem B556925 : Blo 370760 556925 := bbase (se 3 (by rfl) ⟨104423, by rfl⟩ : syracuseStep 556925 = 208847) (by norm_num)
theorem B556949 : Blo 370760 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B556973 : Blo 370760 556973 := bbase (se 3 (by rfl) ⟨104432, by rfl⟩ : syracuseStep 556973 = 208865) (by norm_num)
theorem B556997 : Blo 370760 556997 := bbase (se 4 (by rfl) ⟨52218, by rfl⟩ : syracuseStep 556997 = 104437) (by norm_num)
theorem B557021 : Blo 370760 557021 := bbase (se 3 (by rfl) ⟨104441, by rfl⟩ : syracuseStep 557021 = 208883) (by norm_num)
theorem B557045 : Blo 370760 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B557057 : Blo 370760 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B557075 : Blo 370760 557075 := bstep (se 1 (by rfl) ⟨417806, by rfl⟩ : syracuseStep 557075 = 835613) B835613
theorem B557105 : Blo 370760 557105 := bstep (se 2 (by rfl) ⟨208914, by rfl⟩ : syracuseStep 557105 = 417829) B417829
theorem B557123 : Blo 370760 557123 := bstep (se 1 (by rfl) ⟨417842, by rfl⟩ : syracuseStep 557123 = 835685) B835685
theorem B557153 : Blo 370760 557153 := bstep (se 2 (by rfl) ⟨208932, by rfl⟩ : syracuseStep 557153 = 417865) B417865
theorem B557171 : Blo 370760 557171 := bstep (se 1 (by rfl) ⟨417878, by rfl⟩ : syracuseStep 557171 = 835757) B835757
theorem B557201 : Blo 370760 557201 := bstep (se 2 (by rfl) ⟨208950, by rfl⟩ : syracuseStep 557201 = 417901) B417901
theorem B557219 : Blo 370760 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B557249 : Blo 370760 557249 := bstep (se 2 (by rfl) ⟨208968, by rfl⟩ : syracuseStep 557249 = 417937) B417937
theorem B557267 : Blo 370760 557267 := bstep (se 1 (by rfl) ⟨417950, by rfl⟩ : syracuseStep 557267 = 835901) B835901
theorem B557297 : Blo 370760 557297 := bstep (se 2 (by rfl) ⟨208986, by rfl⟩ : syracuseStep 557297 = 417973) B417973
theorem B557315 : Blo 370760 557315 := bstep (se 1 (by rfl) ⟨417986, by rfl⟩ : syracuseStep 557315 = 835973) B835973
theorem B557345 : Blo 370760 557345 := bstep (se 2 (by rfl) ⟨209004, by rfl⟩ : syracuseStep 557345 = 418009) B418009
theorem B557363 : Blo 370760 557363 := bstep (se 1 (by rfl) ⟨418022, by rfl⟩ : syracuseStep 557363 = 836045) B836045
theorem B557393 : Blo 370760 557393 := bstep (se 2 (by rfl) ⟨209022, by rfl⟩ : syracuseStep 557393 = 418045) B418045
theorem B557411 : Blo 370760 557411 := bstep (se 1 (by rfl) ⟨418058, by rfl⟩ : syracuseStep 557411 = 836117) B836117
theorem B557441 : Blo 370760 557441 := bstep (se 2 (by rfl) ⟨209040, by rfl⟩ : syracuseStep 557441 = 418081) B418081
theorem B557459 : Blo 370760 557459 := bstep (se 1 (by rfl) ⟨418094, by rfl⟩ : syracuseStep 557459 = 836189) B836189
theorem B557489 : Blo 370760 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B557507 : Blo 370760 557507 := bstep (se 1 (by rfl) ⟨418130, by rfl⟩ : syracuseStep 557507 = 836261) B836261
theorem B557537 : Blo 370760 557537 := bstep (se 2 (by rfl) ⟨209076, by rfl⟩ : syracuseStep 557537 = 418153) B418153
theorem B1409507 : Blo 370760 1409507 := bstep (se 1 (by rfl) ⟨1057130, by rfl⟩ : syracuseStep 1409507 = 2114261) B2114261
theorem B1409521 : Blo 370760 1409521 := bstep (se 2 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 1409521 = 1057141) B1057141
theorem B557555 : Blo 370760 557555 := bstep (se 1 (by rfl) ⟨418166, by rfl⟩ : syracuseStep 557555 = 836333) B836333
theorem B557585 : Blo 370760 557585 := bstep (se 2 (by rfl) ⟨209094, by rfl⟩ : syracuseStep 557585 = 418189) B418189
theorem B557603 : Blo 370760 557603 := bstep (se 1 (by rfl) ⟨418202, by rfl⟩ : syracuseStep 557603 = 836405) B836405
theorem B557633 : Blo 370760 557633 := bstep (se 2 (by rfl) ⟨209112, by rfl⟩ : syracuseStep 557633 = 418225) B418225
theorem B557651 : Blo 370760 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B557681 : Blo 370760 557681 := bstep (se 2 (by rfl) ⟨209130, by rfl⟩ : syracuseStep 557681 = 418261) B418261
theorem B557699 : Blo 370760 557699 := bstep (se 1 (by rfl) ⟨418274, by rfl⟩ : syracuseStep 557699 = 836549) B836549
theorem B6390413 : Blo 370760 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B557729 : Blo 370760 557729 := bstep (se 2 (by rfl) ⟨209148, by rfl⟩ : syracuseStep 557729 = 418297) B418297
theorem B557747 : Blo 370760 557747 := bstep (se 1 (by rfl) ⟨418310, by rfl⟩ : syracuseStep 557747 = 836621) B836621
theorem B557777 : Blo 370760 557777 := bstep (se 2 (by rfl) ⟨209166, by rfl⟩ : syracuseStep 557777 = 418333) B418333
theorem B557795 : Blo 370760 557795 := bstep (se 1 (by rfl) ⟨418346, by rfl⟩ : syracuseStep 557795 = 836693) B836693
theorem B557825 : Blo 370760 557825 := bstep (se 2 (by rfl) ⟨209184, by rfl⟩ : syracuseStep 557825 = 418369) B418369
theorem B557843 : Blo 370760 557843 := bstep (se 1 (by rfl) ⟨418382, by rfl⟩ : syracuseStep 557843 = 836765) B836765
theorem B557873 : Blo 370760 557873 := bstep (se 2 (by rfl) ⟨209202, by rfl⟩ : syracuseStep 557873 = 418405) B418405
theorem B557891 : Blo 370760 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B557921 : Blo 370760 557921 := bstep (se 2 (by rfl) ⟨209220, by rfl⟩ : syracuseStep 557921 = 418441) B418441
theorem B557939 : Blo 370760 557939 := bstep (se 1 (by rfl) ⟨418454, by rfl⟩ : syracuseStep 557939 = 836909) B836909
theorem B2392973 : Blo 370760 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B557969 : Blo 370760 557969 := bstep (se 2 (by rfl) ⟨209238, by rfl⟩ : syracuseStep 557969 = 418477) B418477
theorem B557987 : Blo 370760 557987 := bstep (se 1 (by rfl) ⟨418490, by rfl⟩ : syracuseStep 557987 = 836981) B836981
theorem B558017 : Blo 370760 558017 := bstep (se 2 (by rfl) ⟨209256, by rfl⟩ : syracuseStep 558017 = 418513) B418513
theorem B558035 : Blo 370760 558035 := bstep (se 1 (by rfl) ⟨418526, by rfl⟩ : syracuseStep 558035 = 837053) B837053
theorem B558065 : Blo 370760 558065 := bstep (se 2 (by rfl) ⟨209274, by rfl⟩ : syracuseStep 558065 = 418549) B418549
theorem B558083 : Blo 370760 558083 := bstep (se 1 (by rfl) ⟨418562, by rfl⟩ : syracuseStep 558083 = 837125) B837125
theorem B558113 : Blo 370760 558113 := bstep (se 2 (by rfl) ⟨209292, by rfl⟩ : syracuseStep 558113 = 418585) B418585
theorem B558131 : Blo 370760 558131 := bstep (se 1 (by rfl) ⟨418598, by rfl⟩ : syracuseStep 558131 = 837197) B837197
theorem B558161 : Blo 370760 558161 := bstep (se 2 (by rfl) ⟨209310, by rfl⟩ : syracuseStep 558161 = 418621) B418621
theorem B558179 : Blo 370760 558179 := bstep (se 1 (by rfl) ⟨418634, by rfl⟩ : syracuseStep 558179 = 837269) B837269
theorem B558209 : Blo 370760 558209 := bstep (se 2 (by rfl) ⟨209328, by rfl⟩ : syracuseStep 558209 = 418657) B418657
theorem B558227 : Blo 370760 558227 := bstep (se 1 (by rfl) ⟨418670, by rfl⟩ : syracuseStep 558227 = 837341) B837341
theorem B558257 : Blo 370760 558257 := bstep (se 2 (by rfl) ⟨209346, by rfl⟩ : syracuseStep 558257 = 418693) B418693
theorem B558275 : Blo 370760 558275 := bstep (se 1 (by rfl) ⟨418706, by rfl⟩ : syracuseStep 558275 = 837413) B837413
theorem B558305 : Blo 370760 558305 := bstep (se 2 (by rfl) ⟨209364, by rfl⟩ : syracuseStep 558305 = 418729) B418729
theorem B558323 : Blo 370760 558323 := bstep (se 1 (by rfl) ⟨418742, by rfl⟩ : syracuseStep 558323 = 837485) B837485
theorem B558353 : Blo 370760 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B558371 : Blo 370760 558371 := bstep (se 1 (by rfl) ⟨418778, by rfl⟩ : syracuseStep 558371 = 837557) B837557
theorem B558401 : Blo 370760 558401 := bstep (se 2 (by rfl) ⟨209400, by rfl⟩ : syracuseStep 558401 = 418801) B418801
theorem B558419 : Blo 370760 558419 := bstep (se 1 (by rfl) ⟨418814, by rfl⟩ : syracuseStep 558419 = 837629) B837629
theorem B558449 : Blo 370760 558449 := bstep (se 2 (by rfl) ⟨209418, by rfl⟩ : syracuseStep 558449 = 418837) B418837
theorem B558467 : Blo 370760 558467 := bstep (se 1 (by rfl) ⟨418850, by rfl⟩ : syracuseStep 558467 = 837701) B837701
theorem B16647565 : Blo 370760 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B558497 : Blo 370760 558497 := bstep (se 2 (by rfl) ⟨209436, by rfl⟩ : syracuseStep 558497 = 418873) B418873
theorem B558515 : Blo 370760 558515 := bstep (se 1 (by rfl) ⟨418886, by rfl⟩ : syracuseStep 558515 = 837773) B837773
theorem B558545 : Blo 370760 558545 := bstep (se 2 (by rfl) ⟨209454, by rfl⟩ : syracuseStep 558545 = 418909) B418909
theorem B558563 : Blo 370760 558563 := bstep (se 1 (by rfl) ⟨418922, by rfl⟩ : syracuseStep 558563 = 837845) B837845
theorem B558593 : Blo 370760 558593 := bstep (se 2 (by rfl) ⟨209472, by rfl⟩ : syracuseStep 558593 = 418945) B418945
theorem B558611 : Blo 370760 558611 := bstep (se 1 (by rfl) ⟨418958, by rfl⟩ : syracuseStep 558611 = 837917) B837917
theorem B558641 : Blo 370760 558641 := bstep (se 2 (by rfl) ⟨209490, by rfl⟩ : syracuseStep 558641 = 418981) B418981
theorem B2131505 : Blo 370760 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B15238709 : Blo 370760 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B558659 : Blo 370760 558659 := bstep (se 1 (by rfl) ⟨418994, by rfl⟩ : syracuseStep 558659 = 837989) B837989
theorem B558689 : Blo 370760 558689 := bstep (se 2 (by rfl) ⟨209508, by rfl⟩ : syracuseStep 558689 = 419017) B419017
theorem B558707 : Blo 370760 558707 := bstep (se 1 (by rfl) ⟨419030, by rfl⟩ : syracuseStep 558707 = 838061) B838061
theorem B558737 : Blo 370760 558737 := bstep (se 2 (by rfl) ⟨209526, by rfl⟩ : syracuseStep 558737 = 419053) B419053
theorem B558755 : Blo 370760 558755 := bstep (se 1 (by rfl) ⟨419066, by rfl⟩ : syracuseStep 558755 = 838133) B838133
theorem B558785 : Blo 370760 558785 := bstep (se 2 (by rfl) ⟨209544, by rfl⟩ : syracuseStep 558785 = 419089) B419089
theorem B558803 : Blo 370760 558803 := bstep (se 1 (by rfl) ⟨419102, by rfl⟩ : syracuseStep 558803 = 838205) B838205
theorem B558833 : Blo 370760 558833 := bstep (se 2 (by rfl) ⟨209562, by rfl⟩ : syracuseStep 558833 = 419125) B419125
theorem B3835633 : Blo 370760 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B558851 : Blo 370760 558851 := bstep (se 1 (by rfl) ⟨419138, by rfl⟩ : syracuseStep 558851 = 838277) B838277
theorem B558881 : Blo 370760 558881 := bstep (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) B419161
theorem B558899 : Blo 370760 558899 := bstep (se 1 (by rfl) ⟨419174, by rfl⟩ : syracuseStep 558899 = 838349) B838349
theorem B558929 : Blo 370760 558929 := bstep (se 2 (by rfl) ⟨209598, by rfl⟩ : syracuseStep 558929 = 419197) B419197
theorem B853841 : Blo 370760 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B558947 : Blo 370760 558947 := bstep (se 1 (by rfl) ⟨419210, by rfl⟩ : syracuseStep 558947 = 838421) B838421
theorem B558977 : Blo 370760 558977 := bstep (se 2 (by rfl) ⟨209616, by rfl⟩ : syracuseStep 558977 = 419233) B419233
theorem B558995 : Blo 370760 558995 := bstep (se 1 (by rfl) ⟨419246, by rfl⟩ : syracuseStep 558995 = 838493) B838493
theorem B1410979 : Blo 370760 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B559025 : Blo 370760 559025 := bstep (se 2 (by rfl) ⟨209634, by rfl⟩ : syracuseStep 559025 = 419269) B419269
theorem B559043 : Blo 370760 559043 := bstep (se 1 (by rfl) ⟨419282, by rfl⟩ : syracuseStep 559043 = 838565) B838565
theorem B559073 : Blo 370760 559073 := bstep (se 2 (by rfl) ⟨209652, by rfl⟩ : syracuseStep 559073 = 419305) B419305
theorem B559091 : Blo 370760 559091 := bstep (se 1 (by rfl) ⟨419318, by rfl⟩ : syracuseStep 559091 = 838637) B838637
theorem B1214477 : Blo 370760 1214477 := bstep (se 3 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 1214477 = 455429) B455429
theorem B559121 : Blo 370760 559121 := bstep (se 2 (by rfl) ⟨209670, by rfl⟩ : syracuseStep 559121 = 419341) B419341
theorem B559139 : Blo 370760 559139 := bstep (se 1 (by rfl) ⟨419354, by rfl⟩ : syracuseStep 559139 = 838709) B838709
theorem B559169 : Blo 370760 559169 := bstep (se 2 (by rfl) ⟨209688, by rfl⟩ : syracuseStep 559169 = 419377) B419377
theorem B559187 : Blo 370760 559187 := bstep (se 1 (by rfl) ⟨419390, by rfl⟩ : syracuseStep 559187 = 838781) B838781
theorem B559217 : Blo 370760 559217 := bstep (se 2 (by rfl) ⟨209706, by rfl⟩ : syracuseStep 559217 = 419413) B419413
theorem B559235 : Blo 370760 559235 := bstep (se 1 (by rfl) ⟨419426, by rfl⟩ : syracuseStep 559235 = 838853) B838853
theorem B559265 : Blo 370760 559265 := bstep (se 2 (by rfl) ⟨209724, by rfl⟩ : syracuseStep 559265 = 419449) B419449
theorem B559283 : Blo 370760 559283 := bstep (se 1 (by rfl) ⟨419462, by rfl⟩ : syracuseStep 559283 = 838925) B838925
theorem B559313 : Blo 370760 559313 := bstep (se 2 (by rfl) ⟨209742, by rfl⟩ : syracuseStep 559313 = 419485) B419485
theorem B559331 : Blo 370760 559331 := bstep (se 1 (by rfl) ⟨419498, by rfl⟩ : syracuseStep 559331 = 838997) B838997
theorem B559361 : Blo 370760 559361 := bstep (se 2 (by rfl) ⟨209760, by rfl⟩ : syracuseStep 559361 = 419521) B419521
theorem B559379 : Blo 370760 559379 := bstep (se 1 (by rfl) ⟨419534, by rfl⟩ : syracuseStep 559379 = 839069) B839069
theorem B10455317 : Blo 370760 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B559409 : Blo 370760 559409 := bstep (se 2 (by rfl) ⟨209778, by rfl⟩ : syracuseStep 559409 = 419557) B419557
theorem B559427 : Blo 370760 559427 := bstep (se 1 (by rfl) ⟨419570, by rfl⟩ : syracuseStep 559427 = 839141) B839141
theorem B559457 : Blo 370760 559457 := bstep (se 2 (by rfl) ⟨209796, by rfl⟩ : syracuseStep 559457 = 419593) B419593
theorem B756067 : Blo 370760 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B559475 : Blo 370760 559475 := bstep (se 1 (by rfl) ⟨419606, by rfl⟩ : syracuseStep 559475 = 839213) B839213
theorem B559505 : Blo 370760 559505 := bstep (se 2 (by rfl) ⟨209814, by rfl⟩ : syracuseStep 559505 = 419629) B419629
theorem B559523 : Blo 370760 559523 := bstep (se 1 (by rfl) ⟨419642, by rfl⟩ : syracuseStep 559523 = 839285) B839285
theorem B4786613 : Blo 370760 4786613 := bstep (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) B448745
theorem B559553 : Blo 370760 559553 := bstep (se 2 (by rfl) ⟨209832, by rfl⟩ : syracuseStep 559553 = 419665) B419665
theorem B559571 : Blo 370760 559571 := bstep (se 1 (by rfl) ⟨419678, by rfl⟩ : syracuseStep 559571 = 839357) B839357
theorem B559601 : Blo 370760 559601 := bstep (se 2 (by rfl) ⟨209850, by rfl⟩ : syracuseStep 559601 = 419701) B419701
theorem B559619 : Blo 370760 559619 := bstep (se 1 (by rfl) ⟨419714, by rfl⟩ : syracuseStep 559619 = 839429) B839429
theorem B559649 : Blo 370760 559649 := bstep (se 2 (by rfl) ⟨209868, by rfl⟩ : syracuseStep 559649 = 419737) B419737
theorem B559667 : Blo 370760 559667 := bstep (se 1 (by rfl) ⟨419750, by rfl⟩ : syracuseStep 559667 = 839501) B839501
theorem B559697 : Blo 370760 559697 := bstep (se 2 (by rfl) ⟨209886, by rfl⟩ : syracuseStep 559697 = 419773) B419773
theorem B559715 : Blo 370760 559715 := bstep (se 1 (by rfl) ⟨419786, by rfl⟩ : syracuseStep 559715 = 839573) B839573
theorem B559745 : Blo 370760 559745 := bstep (se 2 (by rfl) ⟨209904, by rfl⟩ : syracuseStep 559745 = 419809) B419809
theorem B559763 : Blo 370760 559763 := bstep (se 1 (by rfl) ⟨419822, by rfl⟩ : syracuseStep 559763 = 839645) B839645
theorem B559793 : Blo 370760 559793 := bstep (se 2 (by rfl) ⟨209922, by rfl⟩ : syracuseStep 559793 = 419845) B419845
theorem B559811 : Blo 370760 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B559841 : Blo 370760 559841 := bstep (se 2 (by rfl) ⟨209940, by rfl⟩ : syracuseStep 559841 = 419881) B419881
theorem B559859 : Blo 370760 559859 := bstep (se 1 (by rfl) ⟨419894, by rfl⟩ : syracuseStep 559859 = 839789) B839789
theorem B559889 : Blo 370760 559889 := bstep (se 2 (by rfl) ⟨209958, by rfl⟩ : syracuseStep 559889 = 419917) B419917
theorem B559907 : Blo 370760 559907 := bstep (se 1 (by rfl) ⟨419930, by rfl⟩ : syracuseStep 559907 = 839861) B839861
theorem B1903409 : Blo 370760 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B559937 : Blo 370760 559937 := bstep (se 2 (by rfl) ⟨209976, by rfl⟩ : syracuseStep 559937 = 419953) B419953
theorem B559955 : Blo 370760 559955 := bstep (se 1 (by rfl) ⟨419966, by rfl⟩ : syracuseStep 559955 = 839933) B839933
theorem B559985 : Blo 370760 559985 := bstep (se 2 (by rfl) ⟨209994, by rfl⟩ : syracuseStep 559985 = 419989) B419989
theorem B560003 : Blo 370760 560003 := bstep (se 1 (by rfl) ⟨420002, by rfl⟩ : syracuseStep 560003 = 840005) B840005
theorem B560033 : Blo 370760 560033 := bstep (se 2 (by rfl) ⟨210012, by rfl⟩ : syracuseStep 560033 = 420025) B420025
theorem B560051 : Blo 370760 560051 := bstep (se 1 (by rfl) ⟨420038, by rfl⟩ : syracuseStep 560051 = 840077) B840077
theorem B560081 : Blo 370760 560081 := bstep (se 2 (by rfl) ⟨210030, by rfl⟩ : syracuseStep 560081 = 420061) B420061
theorem B560099 : Blo 370760 560099 := bstep (se 1 (by rfl) ⟨420074, by rfl⟩ : syracuseStep 560099 = 840149) B840149
theorem B2132963 : Blo 370760 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B560129 : Blo 370760 560129 := bstep (se 2 (by rfl) ⟨210048, by rfl⟩ : syracuseStep 560129 = 420097) B420097
theorem B560147 : Blo 370760 560147 := bstep (se 1 (by rfl) ⟨420110, by rfl⟩ : syracuseStep 560147 = 840221) B840221
theorem B560177 : Blo 370760 560177 := bstep (se 2 (by rfl) ⟨210066, by rfl⟩ : syracuseStep 560177 = 420133) B420133
theorem B560195 : Blo 370760 560195 := bstep (se 1 (by rfl) ⟨420146, by rfl⟩ : syracuseStep 560195 = 840293) B840293
theorem B625745 : Blo 370760 625745 := bstep (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) B469309
theorem B560225 : Blo 370760 560225 := bstep (se 2 (by rfl) ⟨210084, by rfl⟩ : syracuseStep 560225 = 420169) B420169
theorem B560243 : Blo 370760 560243 := bstep (se 1 (by rfl) ⟨420182, by rfl⟩ : syracuseStep 560243 = 840365) B840365
theorem B3574925 : Blo 370760 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B560273 : Blo 370760 560273 := bstep (se 2 (by rfl) ⟨210102, by rfl⟩ : syracuseStep 560273 = 420205) B420205
theorem B560291 : Blo 370760 560291 := bstep (se 1 (by rfl) ⟨420218, by rfl⟩ : syracuseStep 560291 = 840437) B840437
theorem B560321 : Blo 370760 560321 := bstep (se 2 (by rfl) ⟨210120, by rfl⟩ : syracuseStep 560321 = 420241) B420241
theorem B625873 : Blo 370760 625873 := bstep (se 2 (by rfl) ⟨234702, by rfl⟩ : syracuseStep 625873 = 469405) B469405
theorem B560339 : Blo 370760 560339 := bstep (se 1 (by rfl) ⟨420254, by rfl⟩ : syracuseStep 560339 = 840509) B840509
theorem B560369 : Blo 370760 560369 := bstep (se 2 (by rfl) ⟨210138, by rfl⟩ : syracuseStep 560369 = 420277) B420277
theorem B625907 : Blo 370760 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B560387 : Blo 370760 560387 := bstep (se 1 (by rfl) ⟨420290, by rfl⟩ : syracuseStep 560387 = 840581) B840581
theorem B560417 : Blo 370760 560417 := bstep (se 2 (by rfl) ⟨210156, by rfl⟩ : syracuseStep 560417 = 420313) B420313
theorem B560435 : Blo 370760 560435 := bstep (se 1 (by rfl) ⟨420326, by rfl⟩ : syracuseStep 560435 = 840653) B840653
theorem B560465 : Blo 370760 560465 := bstep (se 2 (by rfl) ⟨210174, by rfl⟩ : syracuseStep 560465 = 420349) B420349
theorem B560483 : Blo 370760 560483 := bstep (se 1 (by rfl) ⟨420362, by rfl⟩ : syracuseStep 560483 = 840725) B840725
theorem B626035 : Blo 370760 626035 := bstep (se 1 (by rfl) ⟨469526, by rfl⟩ : syracuseStep 626035 = 939053) B939053
theorem B560513 : Blo 370760 560513 := bstep (se 2 (by rfl) ⟨210192, by rfl⟩ : syracuseStep 560513 = 420385) B420385
theorem B560531 : Blo 370760 560531 := bstep (se 1 (by rfl) ⟨420398, by rfl⟩ : syracuseStep 560531 = 840797) B840797
theorem B560561 : Blo 370760 560561 := bstep (se 2 (by rfl) ⟨210210, by rfl⟩ : syracuseStep 560561 = 420421) B420421
theorem B560579 : Blo 370760 560579 := bstep (se 1 (by rfl) ⟨420434, by rfl⟩ : syracuseStep 560579 = 840869) B840869
theorem B560609 : Blo 370760 560609 := bstep (se 2 (by rfl) ⟨210228, by rfl⟩ : syracuseStep 560609 = 420457) B420457
theorem B396787 : Blo 370760 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B560627 : Blo 370760 560627 := bstep (se 1 (by rfl) ⟨420470, by rfl⟩ : syracuseStep 560627 = 840941) B840941
theorem B626177 : Blo 370760 626177 := bstep (se 2 (by rfl) ⟨234816, by rfl⟩ : syracuseStep 626177 = 469633) B469633
theorem B560657 : Blo 370760 560657 := bstep (se 2 (by rfl) ⟨210246, by rfl⟩ : syracuseStep 560657 = 420493) B420493
theorem B560675 : Blo 370760 560675 := bstep (se 1 (by rfl) ⟨420506, by rfl⟩ : syracuseStep 560675 = 841013) B841013
theorem B560705 : Blo 370760 560705 := bstep (se 2 (by rfl) ⟨210264, by rfl⟩ : syracuseStep 560705 = 420529) B420529
theorem B560723 : Blo 370760 560723 := bstep (se 1 (by rfl) ⟨420542, by rfl⟩ : syracuseStep 560723 = 841085) B841085
theorem B560753 : Blo 370760 560753 := bstep (se 2 (by rfl) ⟨210282, by rfl⟩ : syracuseStep 560753 = 420565) B420565
theorem B626305 : Blo 370760 626305 := bstep (se 2 (by rfl) ⟨234864, by rfl⟩ : syracuseStep 626305 = 469729) B469729
theorem B560771 : Blo 370760 560771 := bstep (se 1 (by rfl) ⟨420578, by rfl⟩ : syracuseStep 560771 = 841157) B841157
theorem B954001 : Blo 370760 954001 := bstep (se 2 (by rfl) ⟨357750, by rfl⟩ : syracuseStep 954001 = 715501) B715501
theorem B560801 : Blo 370760 560801 := bstep (se 2 (by rfl) ⟨210300, by rfl⟩ : syracuseStep 560801 = 420601) B420601
theorem B626339 : Blo 370760 626339 := bstep (se 1 (by rfl) ⟨469754, by rfl⟩ : syracuseStep 626339 = 939509) B939509
theorem B560819 : Blo 370760 560819 := bstep (se 1 (by rfl) ⟨420614, by rfl⟩ : syracuseStep 560819 = 841229) B841229
theorem B560849 : Blo 370760 560849 := bstep (se 2 (by rfl) ⟨210318, by rfl⟩ : syracuseStep 560849 = 420637) B420637
theorem B560867 : Blo 370760 560867 := bstep (se 1 (by rfl) ⟨420650, by rfl⟩ : syracuseStep 560867 = 841301) B841301
theorem B528115 : Blo 370760 528115 := bstep (se 1 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 528115 = 792173) B792173
theorem B560897 : Blo 370760 560897 := bstep (se 2 (by rfl) ⟨210336, by rfl⟩ : syracuseStep 560897 = 420673) B420673
theorem B560915 : Blo 370760 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B626467 : Blo 370760 626467 := bstep (se 1 (by rfl) ⟨469850, by rfl⟩ : syracuseStep 626467 = 939701) B939701
theorem B560945 : Blo 370760 560945 := bstep (se 2 (by rfl) ⟨210354, by rfl⟩ : syracuseStep 560945 = 420709) B420709
theorem B560963 : Blo 370760 560963 := bstep (se 1 (by rfl) ⟨420722, by rfl⟩ : syracuseStep 560963 = 841445) B841445
theorem B560993 : Blo 370760 560993 := bstep (se 2 (by rfl) ⟨210372, by rfl⟩ : syracuseStep 560993 = 420745) B420745
theorem B561011 : Blo 370760 561011 := bstep (se 1 (by rfl) ⟨420758, by rfl⟩ : syracuseStep 561011 = 841517) B841517
theorem B561041 : Blo 370760 561041 := bstep (se 2 (by rfl) ⟨210390, by rfl⟩ : syracuseStep 561041 = 420781) B420781
theorem B561059 : Blo 370760 561059 := bstep (se 1 (by rfl) ⟨420794, by rfl⟩ : syracuseStep 561059 = 841589) B841589
theorem B626609 : Blo 370760 626609 := bstep (se 2 (by rfl) ⟨234978, by rfl⟩ : syracuseStep 626609 = 469957) B469957
theorem B561089 : Blo 370760 561089 := bstep (se 2 (by rfl) ⟨210408, by rfl⟩ : syracuseStep 561089 = 420817) B420817
theorem B2133965 : Blo 370760 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B561107 : Blo 370760 561107 := bstep (se 1 (by rfl) ⟨420830, by rfl⟩ : syracuseStep 561107 = 841661) B841661
theorem B561137 : Blo 370760 561137 := bstep (se 2 (by rfl) ⟨210426, by rfl⟩ : syracuseStep 561137 = 420853) B420853
theorem B561155 : Blo 370760 561155 := bstep (se 1 (by rfl) ⟨420866, by rfl⟩ : syracuseStep 561155 = 841733) B841733
theorem B757777 : Blo 370760 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B561185 : Blo 370760 561185 := bstep (se 2 (by rfl) ⟨210444, by rfl⟩ : syracuseStep 561185 = 420889) B420889
theorem B626737 : Blo 370760 626737 := bstep (se 2 (by rfl) ⟨235026, by rfl⟩ : syracuseStep 626737 = 470053) B470053
theorem B561203 : Blo 370760 561203 := bstep (se 1 (by rfl) ⟨420902, by rfl⟩ : syracuseStep 561203 = 841805) B841805
theorem B1413197 : Blo 370760 1413197 := bstep (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) B529949
theorem B561233 : Blo 370760 561233 := bstep (se 2 (by rfl) ⟨210462, by rfl⟩ : syracuseStep 561233 = 420925) B420925
theorem B626771 : Blo 370760 626771 := bstep (se 1 (by rfl) ⟨470078, by rfl⟩ : syracuseStep 626771 = 940157) B940157
theorem B561251 : Blo 370760 561251 := bstep (se 1 (by rfl) ⟨420938, by rfl⟩ : syracuseStep 561251 = 841877) B841877
theorem B561281 : Blo 370760 561281 := bstep (se 2 (by rfl) ⟨210480, by rfl⟩ : syracuseStep 561281 = 420961) B420961
theorem B561299 : Blo 370760 561299 := bstep (se 1 (by rfl) ⟨420974, by rfl⟩ : syracuseStep 561299 = 841949) B841949
theorem B561329 : Blo 370760 561329 := bstep (se 2 (by rfl) ⟨210498, by rfl⟩ : syracuseStep 561329 = 420997) B420997
theorem B561347 : Blo 370760 561347 := bstep (se 1 (by rfl) ⟨421010, by rfl⟩ : syracuseStep 561347 = 842021) B842021
theorem B626899 : Blo 370760 626899 := bstep (se 1 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 626899 = 940349) B940349
theorem B561377 : Blo 370760 561377 := bstep (se 2 (by rfl) ⟨210516, by rfl⟩ : syracuseStep 561377 = 421033) B421033
theorem B561395 : Blo 370760 561395 := bstep (se 1 (by rfl) ⟨421046, by rfl⟩ : syracuseStep 561395 = 842093) B842093
theorem B561425 : Blo 370760 561425 := bstep (se 2 (by rfl) ⟨210534, by rfl⟩ : syracuseStep 561425 = 421069) B421069
theorem B954659 : Blo 370760 954659 := bstep (se 1 (by rfl) ⟨715994, by rfl⟩ : syracuseStep 954659 = 1431989) B1431989
theorem B561443 : Blo 370760 561443 := bstep (se 1 (by rfl) ⟨421082, by rfl⟩ : syracuseStep 561443 = 842165) B842165
theorem B561473 : Blo 370760 561473 := bstep (se 2 (by rfl) ⟨210552, by rfl⟩ : syracuseStep 561473 = 421105) B421105
theorem B561491 : Blo 370760 561491 := bstep (se 1 (by rfl) ⟨421118, by rfl⟩ : syracuseStep 561491 = 842237) B842237
theorem B627041 : Blo 370760 627041 := bstep (se 2 (by rfl) ⟨235140, by rfl⟩ : syracuseStep 627041 = 470281) B470281
theorem B397667 : Blo 370760 397667 := bstep (se 1 (by rfl) ⟨298250, by rfl⟩ : syracuseStep 397667 = 596501) B596501
theorem B561521 : Blo 370760 561521 := bstep (se 2 (by rfl) ⟨210570, by rfl⟩ : syracuseStep 561521 = 421141) B421141
theorem B561539 : Blo 370760 561539 := bstep (se 1 (by rfl) ⟨421154, by rfl⟩ : syracuseStep 561539 = 842309) B842309
theorem B561569 : Blo 370760 561569 := bstep (se 2 (by rfl) ⟨210588, by rfl⟩ : syracuseStep 561569 = 421177) B421177
theorem B561587 : Blo 370760 561587 := bstep (se 1 (by rfl) ⟨421190, by rfl⟩ : syracuseStep 561587 = 842381) B842381
theorem B1085905 : Blo 370760 1085905 := bstep (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) B814429
theorem B561617 : Blo 370760 561617 := bstep (se 2 (by rfl) ⟨210606, by rfl⟩ : syracuseStep 561617 = 421213) B421213
theorem B627169 : Blo 370760 627169 := bstep (se 2 (by rfl) ⟨235188, by rfl⟩ : syracuseStep 627169 = 470377) B470377
theorem B397795 : Blo 370760 397795 := bstep (se 1 (by rfl) ⟨298346, by rfl⟩ : syracuseStep 397795 = 596693) B596693
theorem B561635 : Blo 370760 561635 := bstep (se 1 (by rfl) ⟨421226, by rfl⟩ : syracuseStep 561635 = 842453) B842453
theorem B561665 : Blo 370760 561665 := bstep (se 2 (by rfl) ⟨210624, by rfl⟩ : syracuseStep 561665 = 421249) B421249
theorem B627203 : Blo 370760 627203 := bstep (se 1 (by rfl) ⟨470402, by rfl⟩ : syracuseStep 627203 = 940805) B940805
theorem B561683 : Blo 370760 561683 := bstep (se 1 (by rfl) ⟨421262, by rfl⟩ : syracuseStep 561683 = 842525) B842525
theorem B954929 : Blo 370760 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B561713 : Blo 370760 561713 := bstep (se 2 (by rfl) ⟨210642, by rfl⟩ : syracuseStep 561713 = 421285) B421285
theorem B561731 : Blo 370760 561731 := bstep (se 1 (by rfl) ⟨421298, by rfl⟩ : syracuseStep 561731 = 842597) B842597
theorem B594515 : Blo 370760 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B561761 : Blo 370760 561761 := bstep (se 2 (by rfl) ⟨210660, by rfl⟩ : syracuseStep 561761 = 421321) B421321
theorem B561779 : Blo 370760 561779 := bstep (se 1 (by rfl) ⟨421334, by rfl⟩ : syracuseStep 561779 = 842669) B842669
theorem B627331 : Blo 370760 627331 := bstep (se 1 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 627331 = 940997) B940997
theorem B561809 : Blo 370760 561809 := bstep (se 2 (by rfl) ⟨210678, by rfl⟩ : syracuseStep 561809 = 421357) B421357
theorem B561827 : Blo 370760 561827 := bstep (se 1 (by rfl) ⟨421370, by rfl⟩ : syracuseStep 561827 = 842741) B842741
theorem B561857 : Blo 370760 561857 := bstep (se 2 (by rfl) ⟨210696, by rfl⟩ : syracuseStep 561857 = 421393) B421393
theorem B561875 : Blo 370760 561875 := bstep (se 1 (by rfl) ⟨421406, by rfl⟩ : syracuseStep 561875 = 842813) B842813
theorem B561905 : Blo 370760 561905 := bstep (se 2 (by rfl) ⟨210714, by rfl⟩ : syracuseStep 561905 = 421429) B421429
theorem B561923 : Blo 370760 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B627473 : Blo 370760 627473 := bstep (se 2 (by rfl) ⟨235302, by rfl⟩ : syracuseStep 627473 = 470605) B470605
theorem B561953 : Blo 370760 561953 := bstep (se 2 (by rfl) ⟨210732, by rfl⟩ : syracuseStep 561953 = 421465) B421465
theorem B594739 : Blo 370760 594739 := bstep (se 1 (by rfl) ⟨446054, by rfl⟩ : syracuseStep 594739 = 892109) B892109
theorem B561971 : Blo 370760 561971 := bstep (se 1 (by rfl) ⟨421478, by rfl⟩ : syracuseStep 561971 = 842957) B842957
theorem B562001 : Blo 370760 562001 := bstep (se 2 (by rfl) ⟨210750, by rfl⟩ : syracuseStep 562001 = 421501) B421501
theorem B529249 : Blo 370760 529249 := bstep (se 2 (by rfl) ⟨198468, by rfl⟩ : syracuseStep 529249 = 396937) B396937
theorem B758627 : Blo 370760 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B562019 : Blo 370760 562019 := bstep (se 1 (by rfl) ⟨421514, by rfl⟩ : syracuseStep 562019 = 843029) B843029
theorem B562049 : Blo 370760 562049 := bstep (se 2 (by rfl) ⟨210768, by rfl⟩ : syracuseStep 562049 = 421537) B421537
theorem B627601 : Blo 370760 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B562067 : Blo 370760 562067 := bstep (se 1 (by rfl) ⟨421550, by rfl⟩ : syracuseStep 562067 = 843101) B843101
theorem B562097 : Blo 370760 562097 := bstep (se 2 (by rfl) ⟨210786, by rfl⟩ : syracuseStep 562097 = 421573) B421573
theorem B627635 : Blo 370760 627635 := bstep (se 1 (by rfl) ⟨470726, by rfl⟩ : syracuseStep 627635 = 941453) B941453
theorem B529345 : Blo 370760 529345 := bstep (se 2 (by rfl) ⟨198504, by rfl⟩ : syracuseStep 529345 = 397009) B397009
theorem B562115 : Blo 370760 562115 := bstep (se 1 (by rfl) ⟨421586, by rfl⟩ : syracuseStep 562115 = 843173) B843173
theorem B627763 : Blo 370760 627763 := bstep (se 1 (by rfl) ⟨470822, by rfl⟩ : syracuseStep 627763 = 941645) B941645
theorem B627905 : Blo 370760 627905 := bstep (se 2 (by rfl) ⟨235464, by rfl⟩ : syracuseStep 627905 = 470929) B470929
theorem B398611 : Blo 370760 398611 := bstep (se 1 (by rfl) ⟨298958, by rfl⟩ : syracuseStep 398611 = 597917) B597917
theorem B628033 : Blo 370760 628033 := bstep (se 2 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 628033 = 471025) B471025
theorem B628067 : Blo 370760 628067 := bstep (se 1 (by rfl) ⟨471050, by rfl⟩ : syracuseStep 628067 = 942101) B942101
theorem B529841 : Blo 370760 529841 := bstep (se 2 (by rfl) ⟨198690, by rfl⟩ : syracuseStep 529841 = 397381) B397381
theorem B628195 : Blo 370760 628195 := bstep (se 1 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 628195 = 942293) B942293
theorem B628337 : Blo 370760 628337 := bstep (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) B471253
theorem B628465 : Blo 370760 628465 := bstep (se 2 (by rfl) ⟨235674, by rfl⟩ : syracuseStep 628465 = 471349) B471349
theorem B628499 : Blo 370760 628499 := bstep (se 1 (by rfl) ⟨471374, by rfl⟩ : syracuseStep 628499 = 942749) B942749
theorem B595745 : Blo 370760 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B628627 : Blo 370760 628627 := bstep (se 1 (by rfl) ⟨471470, by rfl⟩ : syracuseStep 628627 = 942941) B942941
theorem B595937 : Blo 370760 595937 := bstep (se 2 (by rfl) ⟨223476, by rfl⟩ : syracuseStep 595937 = 446953) B446953
theorem B1251341 : Blo 370760 1251341 := bstep (se 3 (by rfl) ⟨234626, by rfl⟩ : syracuseStep 1251341 = 469253) B469253
theorem B628769 : Blo 370760 628769 := bstep (se 2 (by rfl) ⟨235788, by rfl⟩ : syracuseStep 628769 = 471577) B471577
theorem B1251395 : Blo 370760 1251395 := bstep (se 1 (by rfl) ⟨938546, by rfl⟩ : syracuseStep 1251395 = 1877093) B1877093
theorem B2693189 : Blo 370760 2693189 := bstep (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) B504973
theorem B628897 : Blo 370760 628897 := bstep (se 2 (by rfl) ⟨235836, by rfl⟩ : syracuseStep 628897 = 471673) B471673
theorem B628931 : Blo 370760 628931 := bstep (se 1 (by rfl) ⟨471698, by rfl⟩ : syracuseStep 628931 = 943397) B943397
theorem B530707 : Blo 370760 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B629059 : Blo 370760 629059 := bstep (se 1 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 629059 = 943589) B943589
theorem B1251665 : Blo 370760 1251665 := bstep (se 2 (by rfl) ⟨469374, by rfl⟩ : syracuseStep 1251665 = 938749) B938749
theorem B2005361 : Blo 370760 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B530803 : Blo 370760 530803 := bstep (se 1 (by rfl) ⟨398102, by rfl⟩ : syracuseStep 530803 = 796205) B796205
theorem B793027 : Blo 370760 793027 := bstep (se 1 (by rfl) ⟨594770, by rfl⟩ : syracuseStep 793027 = 1189541) B1189541
theorem B629201 : Blo 370760 629201 := bstep (se 2 (by rfl) ⟨235950, by rfl⟩ : syracuseStep 629201 = 471901) B471901
theorem B629329 : Blo 370760 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B629363 : Blo 370760 629363 := bstep (se 1 (by rfl) ⟨472022, by rfl⟩ : syracuseStep 629363 = 944045) B944045
theorem B629491 : Blo 370760 629491 := bstep (se 1 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 629491 = 944237) B944237
theorem B531299 : Blo 370760 531299 := bstep (se 1 (by rfl) ⟨398474, by rfl⟩ : syracuseStep 531299 = 796949) B796949
theorem B1252205 : Blo 370760 1252205 := bstep (se 3 (by rfl) ⟨234788, by rfl⟩ : syracuseStep 1252205 = 469577) B469577
theorem B629633 : Blo 370760 629633 := bstep (se 2 (by rfl) ⟨236112, by rfl⟩ : syracuseStep 629633 = 472225) B472225
theorem B793489 : Blo 370760 793489 := bstep (se 2 (by rfl) ⟨297558, by rfl⟩ : syracuseStep 793489 = 595117) B595117
theorem B1252259 : Blo 370760 1252259 := bstep (se 1 (by rfl) ⟨939194, by rfl⟩ : syracuseStep 1252259 = 1878389) B1878389
theorem B1416113 : Blo 370760 1416113 := bstep (se 2 (by rfl) ⟨531042, by rfl⟩ : syracuseStep 1416113 = 1062085) B1062085
theorem B2268101 : Blo 370760 2268101 := bstep (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) B425269
theorem B629761 : Blo 370760 629761 := bstep (se 2 (by rfl) ⟨236160, by rfl⟩ : syracuseStep 629761 = 472321) B472321
theorem B629795 : Blo 370760 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B629923 : Blo 370760 629923 := bstep (se 1 (by rfl) ⟨472442, by rfl⟩ : syracuseStep 629923 = 944885) B944885
theorem B1252529 : Blo 370760 1252529 := bstep (se 2 (by rfl) ⟨469698, by rfl⟩ : syracuseStep 1252529 = 939397) B939397
theorem B630065 : Blo 370760 630065 := bstep (se 2 (by rfl) ⟨236274, by rfl⟩ : syracuseStep 630065 = 472549) B472549
theorem B1023331 : Blo 370760 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B5086577 : Blo 370760 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B892291 : Blo 370760 892291 := bstep (se 1 (by rfl) ⟨669218, by rfl⟩ : syracuseStep 892291 = 1338437) B1338437
theorem B630193 : Blo 370760 630193 := bstep (se 2 (by rfl) ⟨236322, by rfl⟩ : syracuseStep 630193 = 472645) B472645
theorem B564689 : Blo 370760 564689 := bstep (se 2 (by rfl) ⟨211758, by rfl⟩ : syracuseStep 564689 = 423517) B423517
theorem B630227 : Blo 370760 630227 := bstep (se 1 (by rfl) ⟨472670, by rfl⟩ : syracuseStep 630227 = 945341) B945341
theorem B531937 : Blo 370760 531937 := bstep (se 2 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 531937 = 398953) B398953
theorem B892387 : Blo 370760 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B597539 : Blo 370760 597539 := bstep (se 1 (by rfl) ⟨448154, by rfl⟩ : syracuseStep 597539 = 896309) B896309
theorem B630355 : Blo 370760 630355 := bstep (se 1 (by rfl) ⟨472766, by rfl⟩ : syracuseStep 630355 = 945533) B945533
theorem B892579 : Blo 370760 892579 := bstep (se 1 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 892579 = 1338869) B1338869
theorem B1253069 : Blo 370760 1253069 := bstep (se 3 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 1253069 = 469901) B469901
theorem B630497 : Blo 370760 630497 := bstep (se 2 (by rfl) ⟨236436, by rfl⟩ : syracuseStep 630497 = 472873) B472873
theorem B1253123 : Blo 370760 1253123 := bstep (se 1 (by rfl) ⟨939842, by rfl⟩ : syracuseStep 1253123 = 1879685) B1879685
theorem B532273 : Blo 370760 532273 := bstep (se 2 (by rfl) ⟨199602, by rfl⟩ : syracuseStep 532273 = 399205) B399205
theorem B630625 : Blo 370760 630625 := bstep (se 2 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 630625 = 472969) B472969
theorem B630659 : Blo 370760 630659 := bstep (se 1 (by rfl) ⟨472994, by rfl⟩ : syracuseStep 630659 = 945989) B945989
theorem B794531 : Blo 370760 794531 := bstep (se 1 (by rfl) ⟨595898, by rfl⟩ : syracuseStep 794531 = 1191797) B1191797
theorem B597923 : Blo 370760 597923 := bstep (se 1 (by rfl) ⟨448442, by rfl⟩ : syracuseStep 597923 = 896885) B896885
theorem B565219 : Blo 370760 565219 := bstep (se 1 (by rfl) ⟨423914, by rfl⟩ : syracuseStep 565219 = 847829) B847829
theorem B630787 : Blo 370760 630787 := bstep (se 1 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 630787 = 946181) B946181
theorem B3186701 : Blo 370760 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B1253393 : Blo 370760 1253393 := bstep (se 2 (by rfl) ⟨470022, by rfl⟩ : syracuseStep 1253393 = 940045) B940045
theorem B1187875 : Blo 370760 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B598051 : Blo 370760 598051 := bstep (se 1 (by rfl) ⟨448538, by rfl⟩ : syracuseStep 598051 = 897077) B897077
theorem B630929 : Blo 370760 630929 := bstep (se 2 (by rfl) ⟨236598, by rfl⟩ : syracuseStep 630929 = 473197) B473197
theorem B631057 : Blo 370760 631057 := bstep (se 2 (by rfl) ⟨236646, by rfl⟩ : syracuseStep 631057 = 473293) B473293
theorem B631091 : Blo 370760 631091 := bstep (se 1 (by rfl) ⟨473318, by rfl⟩ : syracuseStep 631091 = 946637) B946637
theorem B1417571 : Blo 370760 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B1188209 : Blo 370760 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B532865 : Blo 370760 532865 := bstep (se 2 (by rfl) ⟨199824, by rfl⟩ : syracuseStep 532865 = 399649) B399649
theorem B1057187 : Blo 370760 1057187 := bstep (se 1 (by rfl) ⟨792890, by rfl⟩ : syracuseStep 1057187 = 1585781) B1585781
theorem B795043 : Blo 370760 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B631219 : Blo 370760 631219 := bstep (se 1 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 631219 = 946829) B946829
theorem B4760005 : Blo 370760 4760005 := bstep (se 4 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 4760005 = 892501) B892501
theorem B1253933 : Blo 370760 1253933 := bstep (se 3 (by rfl) ⟨235112, by rfl⟩ : syracuseStep 1253933 = 470225) B470225
theorem B631361 : Blo 370760 631361 := bstep (se 2 (by rfl) ⟨236760, by rfl⟩ : syracuseStep 631361 = 473521) B473521
theorem B893521 : Blo 370760 893521 := bstep (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) B670141
theorem B1253987 : Blo 370760 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B631489 : Blo 370760 631489 := bstep (se 2 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 631489 = 473617) B473617
theorem B631523 : Blo 370760 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B598769 : Blo 370760 598769 := bstep (se 2 (by rfl) ⟨224538, by rfl⟩ : syracuseStep 598769 = 449077) B449077
theorem B631651 : Blo 370760 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B1254257 : Blo 370760 1254257 := bstep (se 2 (by rfl) ⟨470346, by rfl⟩ : syracuseStep 1254257 = 940693) B940693
theorem B533395 : Blo 370760 533395 := bstep (se 1 (by rfl) ⟨400046, by rfl⟩ : syracuseStep 533395 = 800093) B800093
theorem B598961 : Blo 370760 598961 := bstep (se 2 (by rfl) ⟨224610, by rfl⟩ : syracuseStep 598961 = 449221) B449221
theorem B631793 : Blo 370760 631793 := bstep (se 2 (by rfl) ⟨236922, by rfl⟩ : syracuseStep 631793 = 473845) B473845
theorem B795761 : Blo 370760 795761 := bstep (se 2 (by rfl) ⟨298410, by rfl⟩ : syracuseStep 795761 = 596821) B596821
theorem B631921 : Blo 370760 631921 := bstep (se 2 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 631921 = 473941) B473941
theorem B631955 : Blo 370760 631955 := bstep (se 1 (by rfl) ⟨473966, by rfl⟩ : syracuseStep 631955 = 947933) B947933
theorem B632083 : Blo 370760 632083 := bstep (se 1 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 632083 = 948125) B948125
theorem B1418573 : Blo 370760 1418573 := bstep (se 3 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 1418573 = 531965) B531965
theorem B1254797 : Blo 370760 1254797 := bstep (se 3 (by rfl) ⟨235274, by rfl⟩ : syracuseStep 1254797 = 470549) B470549
theorem B632225 : Blo 370760 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B1254851 : Blo 370760 1254851 := bstep (se 1 (by rfl) ⟨941138, by rfl⟩ : syracuseStep 1254851 = 1882277) B1882277
theorem B1910243 : Blo 370760 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B2336261 : Blo 370760 2336261 := bstep (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) B438049
theorem B632353 : Blo 370760 632353 := bstep (se 2 (by rfl) ⟨237132, by rfl⟩ : syracuseStep 632353 = 474265) B474265
theorem B632387 : Blo 370760 632387 := bstep (se 1 (by rfl) ⟨474290, by rfl⟩ : syracuseStep 632387 = 948581) B948581
theorem B1058417 : Blo 370760 1058417 := bstep (se 2 (by rfl) ⟨396906, by rfl⟩ : syracuseStep 1058417 = 793813) B793813
theorem B763537 : Blo 370760 763537 := bstep (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) B572653
theorem B501427 : Blo 370760 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B1255121 : Blo 370760 1255121 := bstep (se 2 (by rfl) ⟨470670, by rfl⟩ : syracuseStep 1255121 = 941341) B941341
theorem B730883 : Blo 370760 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B403219 : Blo 370760 403219 := bstep (se 1 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 403219 = 604829) B604829
theorem B796547 : Blo 370760 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B567233 : Blo 370760 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B1878065 : Blo 370760 1878065 := bstep (se 2 (by rfl) ⟨704274, by rfl⟩ : syracuseStep 1878065 = 1408549) B1408549
theorem B370771 : Blo 370760 370771 := bstep (se 1 (by rfl) ⟨278078, by rfl⟩ : syracuseStep 370771 = 556157) B556157
theorem B370787 : Blo 370760 370787 := bstep (se 1 (by rfl) ⟨278090, by rfl⟩ : syracuseStep 370787 = 556181) B556181
theorem B501859 : Blo 370760 501859 := bstep (se 1 (by rfl) ⟨376394, by rfl⟩ : syracuseStep 501859 = 752789) B752789
theorem B370803 : Blo 370760 370803 := bstep (se 1 (by rfl) ⟨278102, by rfl⟩ : syracuseStep 370803 = 556205) B556205
theorem B370819 : Blo 370760 370819 := bstep (se 1 (by rfl) ⟨278114, by rfl⟩ : syracuseStep 370819 = 556229) B556229
theorem B370835 : Blo 370760 370835 := bstep (se 1 (by rfl) ⟨278126, by rfl⟩ : syracuseStep 370835 = 556253) B556253
theorem B370851 : Blo 370760 370851 := bstep (se 1 (by rfl) ⟨278138, by rfl⟩ : syracuseStep 370851 = 556277) B556277
theorem B370867 : Blo 370760 370867 := bstep (se 1 (by rfl) ⟨278150, by rfl⟩ : syracuseStep 370867 = 556301) B556301
theorem B370883 : Blo 370760 370883 := bstep (se 1 (by rfl) ⟨278162, by rfl⟩ : syracuseStep 370883 = 556325) B556325
theorem B370899 : Blo 370760 370899 := bstep (se 1 (by rfl) ⟨278174, by rfl⟩ : syracuseStep 370899 = 556349) B556349
theorem B370915 : Blo 370760 370915 := bstep (se 1 (by rfl) ⟨278186, by rfl⟩ : syracuseStep 370915 = 556373) B556373
theorem B1255661 : Blo 370760 1255661 := bstep (se 3 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 1255661 = 470873) B470873
theorem B370931 : Blo 370760 370931 := bstep (se 1 (by rfl) ⟨278198, by rfl⟩ : syracuseStep 370931 = 556397) B556397
theorem B370947 : Blo 370760 370947 := bstep (se 1 (by rfl) ⟨278210, by rfl⟩ : syracuseStep 370947 = 556421) B556421
theorem B370963 : Blo 370760 370963 := bstep (se 1 (by rfl) ⟨278222, by rfl⟩ : syracuseStep 370963 = 556445) B556445
theorem B370979 : Blo 370760 370979 := bstep (se 1 (by rfl) ⟨278234, by rfl⟩ : syracuseStep 370979 = 556469) B556469
theorem B1255715 : Blo 370760 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B370995 : Blo 370760 370995 := bstep (se 1 (by rfl) ⟨278246, by rfl⟩ : syracuseStep 370995 = 556493) B556493
theorem B371011 : Blo 370760 371011 := bstep (se 1 (by rfl) ⟨278258, by rfl⟩ : syracuseStep 371011 = 556517) B556517
theorem B371027 : Blo 370760 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B371043 : Blo 370760 371043 := bstep (se 1 (by rfl) ⟨278282, by rfl⟩ : syracuseStep 371043 = 556565) B556565
theorem B371059 : Blo 370760 371059 := bstep (se 1 (by rfl) ⟨278294, by rfl⟩ : syracuseStep 371059 = 556589) B556589
theorem B371075 : Blo 370760 371075 := bstep (se 1 (by rfl) ⟨278306, by rfl⟩ : syracuseStep 371075 = 556613) B556613
theorem B371091 : Blo 370760 371091 := bstep (se 1 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 371091 = 556637) B556637
theorem B371107 : Blo 370760 371107 := bstep (se 1 (by rfl) ⟨278330, by rfl⟩ : syracuseStep 371107 = 556661) B556661
theorem B371123 : Blo 370760 371123 := bstep (se 1 (by rfl) ⟨278342, by rfl⟩ : syracuseStep 371123 = 556685) B556685
theorem B371139 : Blo 370760 371139 := bstep (se 1 (by rfl) ⟨278354, by rfl⟩ : syracuseStep 371139 = 556709) B556709
theorem B18196933 : Blo 370760 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B371155 : Blo 370760 371155 := bstep (se 1 (by rfl) ⟨278366, by rfl⟩ : syracuseStep 371155 = 556733) B556733
theorem B371171 : Blo 370760 371171 := bstep (se 1 (by rfl) ⟨278378, by rfl⟩ : syracuseStep 371171 = 556757) B556757
theorem B371187 : Blo 370760 371187 := bstep (se 1 (by rfl) ⟨278390, by rfl⟩ : syracuseStep 371187 = 556781) B556781
theorem B371203 : Blo 370760 371203 := bstep (se 1 (by rfl) ⟨278402, by rfl⟩ : syracuseStep 371203 = 556805) B556805
theorem B371219 : Blo 370760 371219 := bstep (se 1 (by rfl) ⟨278414, by rfl⟩ : syracuseStep 371219 = 556829) B556829
theorem B371235 : Blo 370760 371235 := bstep (se 1 (by rfl) ⟨278426, by rfl⟩ : syracuseStep 371235 = 556853) B556853
theorem B1255985 : Blo 370760 1255985 := bstep (se 2 (by rfl) ⟨470994, by rfl⟩ : syracuseStep 1255985 = 941989) B941989
theorem B371251 : Blo 370760 371251 := bstep (se 1 (by rfl) ⟨278438, by rfl⟩ : syracuseStep 371251 = 556877) B556877
theorem B371267 : Blo 370760 371267 := bstep (se 1 (by rfl) ⟨278450, by rfl⟩ : syracuseStep 371267 = 556901) B556901
theorem B371283 : Blo 370760 371283 := bstep (se 1 (by rfl) ⟨278462, by rfl⟩ : syracuseStep 371283 = 556925) B556925
theorem B371299 : Blo 370760 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B371315 : Blo 370760 371315 := bstep (se 1 (by rfl) ⟨278486, by rfl⟩ : syracuseStep 371315 = 556973) B556973
theorem B371331 : Blo 370760 371331 := bstep (se 1 (by rfl) ⟨278498, by rfl⟩ : syracuseStep 371331 = 556997) B556997
theorem B371347 : Blo 370760 371347 := bstep (se 1 (by rfl) ⟨278510, by rfl⟩ : syracuseStep 371347 = 557021) B557021
theorem B371363 : Blo 370760 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B371379 : Blo 370760 371379 := bstep (se 1 (by rfl) ⟨278534, by rfl⟩ : syracuseStep 371379 = 557069) B557069
theorem B371395 : Blo 370760 371395 := bstep (se 1 (by rfl) ⟨278546, by rfl⟩ : syracuseStep 371395 = 557093) B557093
theorem B371411 : Blo 370760 371411 := bstep (se 1 (by rfl) ⟨278558, by rfl⟩ : syracuseStep 371411 = 557117) B557117
theorem B371427 : Blo 370760 371427 := bstep (se 1 (by rfl) ⟨278570, by rfl⟩ : syracuseStep 371427 = 557141) B557141
theorem B371443 : Blo 370760 371443 := bstep (se 1 (by rfl) ⟨278582, by rfl⟩ : syracuseStep 371443 = 557165) B557165
theorem B371459 : Blo 370760 371459 := bstep (se 1 (by rfl) ⟨278594, by rfl⟩ : syracuseStep 371459 = 557189) B557189
theorem B371475 : Blo 370760 371475 := bstep (se 1 (by rfl) ⟨278606, by rfl⟩ : syracuseStep 371475 = 557213) B557213
theorem B469795 : Blo 370760 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B371491 : Blo 370760 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B371507 : Blo 370760 371507 := bstep (se 1 (by rfl) ⟨278630, by rfl⟩ : syracuseStep 371507 = 557261) B557261
theorem B371523 : Blo 370760 371523 := bstep (se 1 (by rfl) ⟨278642, by rfl⟩ : syracuseStep 371523 = 557285) B557285
theorem B797521 : Blo 370760 797521 := bstep (se 2 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 797521 = 598141) B598141
theorem B371539 : Blo 370760 371539 := bstep (se 1 (by rfl) ⟨278654, by rfl⟩ : syracuseStep 371539 = 557309) B557309
theorem B371555 : Blo 370760 371555 := bstep (se 1 (by rfl) ⟨278666, by rfl⟩ : syracuseStep 371555 = 557333) B557333
theorem B371571 : Blo 370760 371571 := bstep (se 1 (by rfl) ⟨278678, by rfl⟩ : syracuseStep 371571 = 557357) B557357
theorem B469891 : Blo 370760 469891 := bstep (se 1 (by rfl) ⟨352418, by rfl⟩ : syracuseStep 469891 = 704837) B704837
theorem B371587 : Blo 370760 371587 := bstep (se 1 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 371587 = 557381) B557381
theorem B371603 : Blo 370760 371603 := bstep (se 1 (by rfl) ⟨278702, by rfl⟩ : syracuseStep 371603 = 557405) B557405
theorem B371619 : Blo 370760 371619 := bstep (se 1 (by rfl) ⟨278714, by rfl⟩ : syracuseStep 371619 = 557429) B557429
theorem B371635 : Blo 370760 371635 := bstep (se 1 (by rfl) ⟨278726, by rfl⟩ : syracuseStep 371635 = 557453) B557453
theorem B371651 : Blo 370760 371651 := bstep (se 1 (by rfl) ⟨278738, by rfl⟩ : syracuseStep 371651 = 557477) B557477
theorem B371667 : Blo 370760 371667 := bstep (se 1 (by rfl) ⟨278750, by rfl⟩ : syracuseStep 371667 = 557501) B557501
theorem B371683 : Blo 370760 371683 := bstep (se 1 (by rfl) ⟨278762, by rfl⟩ : syracuseStep 371683 = 557525) B557525
theorem B371699 : Blo 370760 371699 := bstep (se 1 (by rfl) ⟨278774, by rfl⟩ : syracuseStep 371699 = 557549) B557549
theorem B371715 : Blo 370760 371715 := bstep (se 1 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 371715 = 557573) B557573
theorem B371731 : Blo 370760 371731 := bstep (se 1 (by rfl) ⟨278798, by rfl⟩ : syracuseStep 371731 = 557597) B557597
theorem B371747 : Blo 370760 371747 := bstep (se 1 (by rfl) ⟨278810, by rfl⟩ : syracuseStep 371747 = 557621) B557621
theorem B1059875 : Blo 370760 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B371763 : Blo 370760 371763 := bstep (se 1 (by rfl) ⟨278822, by rfl⟩ : syracuseStep 371763 = 557645) B557645
theorem B371779 : Blo 370760 371779 := bstep (se 1 (by rfl) ⟨278834, by rfl⟩ : syracuseStep 371779 = 557669) B557669
theorem B4238405 : Blo 370760 4238405 := bstep (se 4 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 4238405 = 794701) B794701
theorem B1256525 : Blo 370760 1256525 := bstep (se 3 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 1256525 = 471197) B471197
theorem B797777 : Blo 370760 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B371795 : Blo 370760 371795 := bstep (se 1 (by rfl) ⟨278846, by rfl⟩ : syracuseStep 371795 = 557693) B557693
theorem B371811 : Blo 370760 371811 := bstep (se 1 (by rfl) ⟨278858, by rfl⟩ : syracuseStep 371811 = 557717) B557717
theorem B371827 : Blo 370760 371827 := bstep (se 1 (by rfl) ⟨278870, by rfl⟩ : syracuseStep 371827 = 557741) B557741
theorem B371843 : Blo 370760 371843 := bstep (se 1 (by rfl) ⟨278882, by rfl⟩ : syracuseStep 371843 = 557765) B557765
theorem B1256579 : Blo 370760 1256579 := bstep (se 1 (by rfl) ⟨942434, by rfl⟩ : syracuseStep 1256579 = 1884869) B1884869
theorem B371859 : Blo 370760 371859 := bstep (se 1 (by rfl) ⟨278894, by rfl⟩ : syracuseStep 371859 = 557789) B557789
theorem B371875 : Blo 370760 371875 := bstep (se 1 (by rfl) ⟨278906, by rfl⟩ : syracuseStep 371875 = 557813) B557813
theorem B371891 : Blo 370760 371891 := bstep (se 1 (by rfl) ⟨278918, by rfl⟩ : syracuseStep 371891 = 557837) B557837
theorem B371907 : Blo 370760 371907 := bstep (se 1 (by rfl) ⟨278930, by rfl⟩ : syracuseStep 371907 = 557861) B557861
theorem B371923 : Blo 370760 371923 := bstep (se 1 (by rfl) ⟨278942, by rfl⟩ : syracuseStep 371923 = 557885) B557885
theorem B371939 : Blo 370760 371939 := bstep (se 1 (by rfl) ⟨278954, by rfl⟩ : syracuseStep 371939 = 557909) B557909
theorem B371955 : Blo 370760 371955 := bstep (se 1 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 371955 = 557933) B557933
theorem B371971 : Blo 370760 371971 := bstep (se 1 (by rfl) ⟨278978, by rfl⟩ : syracuseStep 371971 = 557957) B557957
theorem B1191181 : Blo 370760 1191181 := bstep (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) B446693
theorem B371987 : Blo 370760 371987 := bstep (se 1 (by rfl) ⟨278990, by rfl⟩ : syracuseStep 371987 = 557981) B557981
theorem B372003 : Blo 370760 372003 := bstep (se 1 (by rfl) ⟨279002, by rfl⟩ : syracuseStep 372003 = 558005) B558005
theorem B372019 : Blo 370760 372019 := bstep (se 1 (by rfl) ⟨279014, by rfl⟩ : syracuseStep 372019 = 558029) B558029
theorem B372035 : Blo 370760 372035 := bstep (se 1 (by rfl) ⟨279026, by rfl⟩ : syracuseStep 372035 = 558053) B558053
theorem B372051 : Blo 370760 372051 := bstep (se 1 (by rfl) ⟨279038, by rfl⟩ : syracuseStep 372051 = 558077) B558077
theorem B372067 : Blo 370760 372067 := bstep (se 1 (by rfl) ⟨279050, by rfl⟩ : syracuseStep 372067 = 558101) B558101
theorem B470387 : Blo 370760 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B372083 : Blo 370760 372083 := bstep (se 1 (by rfl) ⟨279062, by rfl⟩ : syracuseStep 372083 = 558125) B558125
theorem B372099 : Blo 370760 372099 := bstep (se 1 (by rfl) ⟨279074, by rfl⟩ : syracuseStep 372099 = 558149) B558149
theorem B1420685 : Blo 370760 1420685 := bstep (se 3 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 1420685 = 532757) B532757
theorem B1256849 : Blo 370760 1256849 := bstep (se 2 (by rfl) ⟨471318, by rfl⟩ : syracuseStep 1256849 = 942637) B942637
theorem B372115 : Blo 370760 372115 := bstep (se 1 (by rfl) ⟨279086, by rfl⟩ : syracuseStep 372115 = 558173) B558173
theorem B372131 : Blo 370760 372131 := bstep (se 1 (by rfl) ⟨279098, by rfl⟩ : syracuseStep 372131 = 558197) B558197
theorem B372147 : Blo 370760 372147 := bstep (se 1 (by rfl) ⟨279110, by rfl⟩ : syracuseStep 372147 = 558221) B558221
theorem B372163 : Blo 370760 372163 := bstep (se 1 (by rfl) ⟨279122, by rfl⟩ : syracuseStep 372163 = 558245) B558245
theorem B2076101 : Blo 370760 2076101 := bstep (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) B389269
theorem B372179 : Blo 370760 372179 := bstep (se 1 (by rfl) ⟨279134, by rfl⟩ : syracuseStep 372179 = 558269) B558269
theorem B1879523 : Blo 370760 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B372195 : Blo 370760 372195 := bstep (se 1 (by rfl) ⟨279146, by rfl⟩ : syracuseStep 372195 = 558293) B558293
theorem B372211 : Blo 370760 372211 := bstep (se 1 (by rfl) ⟨279158, by rfl⟩ : syracuseStep 372211 = 558317) B558317
theorem B372227 : Blo 370760 372227 := bstep (se 1 (by rfl) ⟨279170, by rfl⟩ : syracuseStep 372227 = 558341) B558341
theorem B1191437 : Blo 370760 1191437 := bstep (se 3 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 1191437 = 446789) B446789
theorem B372243 : Blo 370760 372243 := bstep (se 1 (by rfl) ⟨279182, by rfl⟩ : syracuseStep 372243 = 558365) B558365
theorem B372259 : Blo 370760 372259 := bstep (se 1 (by rfl) ⟨279194, by rfl⟩ : syracuseStep 372259 = 558389) B558389
theorem B372275 : Blo 370760 372275 := bstep (se 1 (by rfl) ⟨279206, by rfl⟩ : syracuseStep 372275 = 558413) B558413
theorem B372291 : Blo 370760 372291 := bstep (se 1 (by rfl) ⟨279218, by rfl⟩ : syracuseStep 372291 = 558437) B558437
theorem B372307 : Blo 370760 372307 := bstep (se 1 (by rfl) ⟨279230, by rfl⟩ : syracuseStep 372307 = 558461) B558461
theorem B372323 : Blo 370760 372323 := bstep (se 1 (by rfl) ⟨279242, by rfl⟩ : syracuseStep 372323 = 558485) B558485
theorem B372339 : Blo 370760 372339 := bstep (se 1 (by rfl) ⟨279254, by rfl⟩ : syracuseStep 372339 = 558509) B558509
theorem B372355 : Blo 370760 372355 := bstep (se 1 (by rfl) ⟨279266, by rfl⟩ : syracuseStep 372355 = 558533) B558533
theorem B372371 : Blo 370760 372371 := bstep (se 1 (by rfl) ⟨279278, by rfl⟩ : syracuseStep 372371 = 558557) B558557
theorem B372387 : Blo 370760 372387 := bstep (se 1 (by rfl) ⟨279290, by rfl⟩ : syracuseStep 372387 = 558581) B558581
theorem B372403 : Blo 370760 372403 := bstep (se 1 (by rfl) ⟨279302, by rfl⟩ : syracuseStep 372403 = 558605) B558605
theorem B372419 : Blo 370760 372419 := bstep (se 1 (by rfl) ⟨279314, by rfl⟩ : syracuseStep 372419 = 558629) B558629
theorem B372435 : Blo 370760 372435 := bstep (se 1 (by rfl) ⟨279326, by rfl⟩ : syracuseStep 372435 = 558653) B558653
theorem B372451 : Blo 370760 372451 := bstep (se 1 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 372451 = 558677) B558677
theorem B372467 : Blo 370760 372467 := bstep (se 1 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 372467 = 558701) B558701
theorem B372483 : Blo 370760 372483 := bstep (se 1 (by rfl) ⟨279362, by rfl⟩ : syracuseStep 372483 = 558725) B558725
theorem B372499 : Blo 370760 372499 := bstep (se 1 (by rfl) ⟨279374, by rfl⟩ : syracuseStep 372499 = 558749) B558749
theorem B372515 : Blo 370760 372515 := bstep (se 1 (by rfl) ⟨279386, by rfl⟩ : syracuseStep 372515 = 558773) B558773
theorem B372531 : Blo 370760 372531 := bstep (se 1 (by rfl) ⟨279398, by rfl⟩ : syracuseStep 372531 = 558797) B558797
theorem B372547 : Blo 370760 372547 := bstep (se 1 (by rfl) ⟨279410, by rfl⟩ : syracuseStep 372547 = 558821) B558821
theorem B1060685 : Blo 370760 1060685 := bstep (se 3 (by rfl) ⟨198878, by rfl⟩ : syracuseStep 1060685 = 397757) B397757
theorem B372563 : Blo 370760 372563 := bstep (se 1 (by rfl) ⟨279422, by rfl⟩ : syracuseStep 372563 = 558845) B558845
theorem B372579 : Blo 370760 372579 := bstep (se 1 (by rfl) ⟨279434, by rfl⟩ : syracuseStep 372579 = 558869) B558869
theorem B4599665 : Blo 370760 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B372595 : Blo 370760 372595 := bstep (se 1 (by rfl) ⟨279446, by rfl⟩ : syracuseStep 372595 = 558893) B558893
theorem B372611 : Blo 370760 372611 := bstep (se 1 (by rfl) ⟨279458, by rfl⟩ : syracuseStep 372611 = 558917) B558917
theorem B372627 : Blo 370760 372627 := bstep (se 1 (by rfl) ⟨279470, by rfl⟩ : syracuseStep 372627 = 558941) B558941
theorem B372643 : Blo 370760 372643 := bstep (se 1 (by rfl) ⟨279482, by rfl⟩ : syracuseStep 372643 = 558965) B558965
theorem B1257389 : Blo 370760 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B372659 : Blo 370760 372659 := bstep (se 1 (by rfl) ⟨279494, by rfl⟩ : syracuseStep 372659 = 558989) B558989
theorem B372675 : Blo 370760 372675 := bstep (se 1 (by rfl) ⟨279506, by rfl⟩ : syracuseStep 372675 = 559013) B559013
theorem B372691 : Blo 370760 372691 := bstep (se 1 (by rfl) ⟨279518, by rfl⟩ : syracuseStep 372691 = 559037) B559037
theorem B1257443 : Blo 370760 1257443 := bstep (se 1 (by rfl) ⟨943082, by rfl⟩ : syracuseStep 1257443 = 1886165) B1886165
theorem B372707 : Blo 370760 372707 := bstep (se 1 (by rfl) ⟨279530, by rfl⟩ : syracuseStep 372707 = 559061) B559061
theorem B372723 : Blo 370760 372723 := bstep (se 1 (by rfl) ⟨279542, by rfl⟩ : syracuseStep 372723 = 559085) B559085
theorem B372739 : Blo 370760 372739 := bstep (se 1 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 372739 = 559109) B559109
theorem B1585165 : Blo 370760 1585165 := bstep (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) B594437
theorem B1060877 : Blo 370760 1060877 := bstep (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) B397829
theorem B372755 : Blo 370760 372755 := bstep (se 1 (by rfl) ⟨279566, by rfl⟩ : syracuseStep 372755 = 559133) B559133
theorem B372771 : Blo 370760 372771 := bstep (se 1 (by rfl) ⟨279578, by rfl⟩ : syracuseStep 372771 = 559157) B559157
theorem B471091 : Blo 370760 471091 := bstep (se 1 (by rfl) ⟨353318, by rfl⟩ : syracuseStep 471091 = 706637) B706637
theorem B372787 : Blo 370760 372787 := bstep (se 1 (by rfl) ⟨279590, by rfl⟩ : syracuseStep 372787 = 559181) B559181
theorem B372803 : Blo 370760 372803 := bstep (se 1 (by rfl) ⟨279602, by rfl⟩ : syracuseStep 372803 = 559205) B559205
theorem B372819 : Blo 370760 372819 := bstep (se 1 (by rfl) ⟨279614, by rfl⟩ : syracuseStep 372819 = 559229) B559229
theorem B372835 : Blo 370760 372835 := bstep (se 1 (by rfl) ⟨279626, by rfl⟩ : syracuseStep 372835 = 559253) B559253
theorem B1618019 : Blo 370760 1618019 := bstep (se 1 (by rfl) ⟨1213514, by rfl⟩ : syracuseStep 1618019 = 2427029) B2427029
theorem B372851 : Blo 370760 372851 := bstep (se 1 (by rfl) ⟨279638, by rfl⟩ : syracuseStep 372851 = 559277) B559277
theorem B372867 : Blo 370760 372867 := bstep (se 1 (by rfl) ⟨279650, by rfl⟩ : syracuseStep 372867 = 559301) B559301
theorem B471187 : Blo 370760 471187 := bstep (se 1 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 471187 = 706781) B706781
theorem B372883 : Blo 370760 372883 := bstep (se 1 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 372883 = 559325) B559325
theorem B372899 : Blo 370760 372899 := bstep (se 1 (by rfl) ⟨279674, by rfl⟩ : syracuseStep 372899 = 559349) B559349
theorem B1421489 : Blo 370760 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B372915 : Blo 370760 372915 := bstep (se 1 (by rfl) ⟨279686, by rfl⟩ : syracuseStep 372915 = 559373) B559373
theorem B372931 : Blo 370760 372931 := bstep (se 1 (by rfl) ⟨279698, by rfl⟩ : syracuseStep 372931 = 559397) B559397
theorem B372947 : Blo 370760 372947 := bstep (se 1 (by rfl) ⟨279710, by rfl⟩ : syracuseStep 372947 = 559421) B559421
theorem B372963 : Blo 370760 372963 := bstep (se 1 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 372963 = 559445) B559445
theorem B1257713 : Blo 370760 1257713 := bstep (se 2 (by rfl) ⟨471642, by rfl⟩ : syracuseStep 1257713 = 943285) B943285
theorem B372979 : Blo 370760 372979 := bstep (se 1 (by rfl) ⟨279734, by rfl⟩ : syracuseStep 372979 = 559469) B559469
theorem B372995 : Blo 370760 372995 := bstep (se 1 (by rfl) ⟨279746, by rfl⟩ : syracuseStep 372995 = 559493) B559493
theorem B1880333 : Blo 370760 1880333 := bstep (se 3 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 1880333 = 705125) B705125
theorem B373011 : Blo 370760 373011 := bstep (se 1 (by rfl) ⟨279758, by rfl⟩ : syracuseStep 373011 = 559517) B559517
theorem B373027 : Blo 370760 373027 := bstep (se 1 (by rfl) ⟨279770, by rfl⟩ : syracuseStep 373027 = 559541) B559541
theorem B373043 : Blo 370760 373043 := bstep (se 1 (by rfl) ⟨279782, by rfl⟩ : syracuseStep 373043 = 559565) B559565
theorem B373059 : Blo 370760 373059 := bstep (se 1 (by rfl) ⟨279794, by rfl⟩ : syracuseStep 373059 = 559589) B559589
theorem B373075 : Blo 370760 373075 := bstep (se 1 (by rfl) ⟨279806, by rfl⟩ : syracuseStep 373075 = 559613) B559613
theorem B1585507 : Blo 370760 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B373091 : Blo 370760 373091 := bstep (se 1 (by rfl) ⟨279818, by rfl⟩ : syracuseStep 373091 = 559637) B559637
theorem B799075 : Blo 370760 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B373107 : Blo 370760 373107 := bstep (se 1 (by rfl) ⟨279830, by rfl⟩ : syracuseStep 373107 = 559661) B559661
theorem B373123 : Blo 370760 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B373139 : Blo 370760 373139 := bstep (se 1 (by rfl) ⟨279854, by rfl⟩ : syracuseStep 373139 = 559709) B559709
theorem B373155 : Blo 370760 373155 := bstep (se 1 (by rfl) ⟨279866, by rfl⟩ : syracuseStep 373155 = 559733) B559733
theorem B373171 : Blo 370760 373171 := bstep (se 1 (by rfl) ⟨279878, by rfl⟩ : syracuseStep 373171 = 559757) B559757
theorem B373187 : Blo 370760 373187 := bstep (se 1 (by rfl) ⟨279890, by rfl⟩ : syracuseStep 373187 = 559781) B559781
theorem B3387845 : Blo 370760 3387845 := bstep (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) B635221
theorem B373203 : Blo 370760 373203 := bstep (se 1 (by rfl) ⟨279902, by rfl⟩ : syracuseStep 373203 = 559805) B559805
theorem B373219 : Blo 370760 373219 := bstep (se 1 (by rfl) ⟨279914, by rfl⟩ : syracuseStep 373219 = 559829) B559829
theorem B373235 : Blo 370760 373235 := bstep (se 1 (by rfl) ⟨279926, by rfl⟩ : syracuseStep 373235 = 559853) B559853
theorem B373251 : Blo 370760 373251 := bstep (se 1 (by rfl) ⟨279938, by rfl⟩ : syracuseStep 373251 = 559877) B559877
theorem B373267 : Blo 370760 373267 := bstep (se 1 (by rfl) ⟨279950, by rfl⟩ : syracuseStep 373267 = 559901) B559901
theorem B373283 : Blo 370760 373283 := bstep (se 1 (by rfl) ⟨279962, by rfl⟩ : syracuseStep 373283 = 559925) B559925
theorem B373299 : Blo 370760 373299 := bstep (se 1 (by rfl) ⟨279974, by rfl⟩ : syracuseStep 373299 = 559949) B559949
theorem B373315 : Blo 370760 373315 := bstep (se 1 (by rfl) ⟨279986, by rfl⟩ : syracuseStep 373315 = 559973) B559973
theorem B373331 : Blo 370760 373331 := bstep (se 1 (by rfl) ⟨279998, by rfl⟩ : syracuseStep 373331 = 559997) B559997
theorem B373347 : Blo 370760 373347 := bstep (se 1 (by rfl) ⟨280010, by rfl⟩ : syracuseStep 373347 = 560021) B560021
theorem B373363 : Blo 370760 373363 := bstep (se 1 (by rfl) ⟨280022, by rfl⟩ : syracuseStep 373363 = 560045) B560045
theorem B471683 : Blo 370760 471683 := bstep (se 1 (by rfl) ⟨353762, by rfl⟩ : syracuseStep 471683 = 707525) B707525
theorem B373379 : Blo 370760 373379 := bstep (se 1 (by rfl) ⟨280034, by rfl⟩ : syracuseStep 373379 = 560069) B560069
theorem B373395 : Blo 370760 373395 := bstep (se 1 (by rfl) ⟨280046, by rfl⟩ : syracuseStep 373395 = 560093) B560093
theorem B373411 : Blo 370760 373411 := bstep (se 1 (by rfl) ⟨280058, by rfl⟩ : syracuseStep 373411 = 560117) B560117
theorem B799409 : Blo 370760 799409 := bstep (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) B599557
theorem B373427 : Blo 370760 373427 := bstep (se 1 (by rfl) ⟨280070, by rfl⟩ : syracuseStep 373427 = 560141) B560141
theorem B373443 : Blo 370760 373443 := bstep (se 1 (by rfl) ⟨280082, by rfl⟩ : syracuseStep 373443 = 560165) B560165
theorem B373459 : Blo 370760 373459 := bstep (se 1 (by rfl) ⟨280094, by rfl⟩ : syracuseStep 373459 = 560189) B560189
theorem B373475 : Blo 370760 373475 := bstep (se 1 (by rfl) ⟨280106, by rfl⟩ : syracuseStep 373475 = 560213) B560213
theorem B373491 : Blo 370760 373491 := bstep (se 1 (by rfl) ⟨280118, by rfl⟩ : syracuseStep 373491 = 560237) B560237
theorem B373507 : Blo 370760 373507 := bstep (se 1 (by rfl) ⟨280130, by rfl⟩ : syracuseStep 373507 = 560261) B560261
theorem B1258253 : Blo 370760 1258253 := bstep (se 3 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 1258253 = 471845) B471845
theorem B373523 : Blo 370760 373523 := bstep (se 1 (by rfl) ⟨280142, by rfl⟩ : syracuseStep 373523 = 560285) B560285
theorem B373539 : Blo 370760 373539 := bstep (se 1 (by rfl) ⟨280154, by rfl⟩ : syracuseStep 373539 = 560309) B560309
theorem B373555 : Blo 370760 373555 := bstep (se 1 (by rfl) ⟨280166, by rfl⟩ : syracuseStep 373555 = 560333) B560333
theorem B1258307 : Blo 370760 1258307 := bstep (se 1 (by rfl) ⟨943730, by rfl⟩ : syracuseStep 1258307 = 1887461) B1887461
theorem B373571 : Blo 370760 373571 := bstep (se 1 (by rfl) ⟨280178, by rfl⟩ : syracuseStep 373571 = 560357) B560357
theorem B1422157 : Blo 370760 1422157 := bstep (se 3 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 1422157 = 533309) B533309
theorem B373587 : Blo 370760 373587 := bstep (se 1 (by rfl) ⟨280190, by rfl⟩ : syracuseStep 373587 = 560381) B560381
theorem B373603 : Blo 370760 373603 := bstep (se 1 (by rfl) ⟨280202, by rfl⟩ : syracuseStep 373603 = 560405) B560405
theorem B373619 : Blo 370760 373619 := bstep (se 1 (by rfl) ⟨280214, by rfl⟩ : syracuseStep 373619 = 560429) B560429
theorem B373635 : Blo 370760 373635 := bstep (se 1 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 373635 = 560453) B560453
theorem B2208653 : Blo 370760 2208653 := bstep (se 3 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 2208653 = 828245) B828245
theorem B373651 : Blo 370760 373651 := bstep (se 1 (by rfl) ⟨280238, by rfl⟩ : syracuseStep 373651 = 560477) B560477
theorem B373667 : Blo 370760 373667 := bstep (se 1 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 373667 = 560501) B560501
theorem B373683 : Blo 370760 373683 := bstep (se 1 (by rfl) ⟨280262, by rfl⟩ : syracuseStep 373683 = 560525) B560525
theorem B373699 : Blo 370760 373699 := bstep (se 1 (by rfl) ⟨280274, by rfl⟩ : syracuseStep 373699 = 560549) B560549
theorem B373715 : Blo 370760 373715 := bstep (se 1 (by rfl) ⟨280286, by rfl⟩ : syracuseStep 373715 = 560573) B560573
theorem B373731 : Blo 370760 373731 := bstep (se 1 (by rfl) ⟨280298, by rfl⟩ : syracuseStep 373731 = 560597) B560597
theorem B1061869 : Blo 370760 1061869 := bstep (se 3 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 1061869 = 398201) B398201
theorem B373747 : Blo 370760 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B1192963 : Blo 370760 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B373763 : Blo 370760 373763 := bstep (se 1 (by rfl) ⟨280322, by rfl⟩ : syracuseStep 373763 = 560645) B560645
theorem B373779 : Blo 370760 373779 := bstep (se 1 (by rfl) ⟨280334, by rfl⟩ : syracuseStep 373779 = 560669) B560669
theorem B2012195 : Blo 370760 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B373795 : Blo 370760 373795 := bstep (se 1 (by rfl) ⟨280346, by rfl⟩ : syracuseStep 373795 = 560693) B560693
theorem B373811 : Blo 370760 373811 := bstep (se 1 (by rfl) ⟨280358, by rfl⟩ : syracuseStep 373811 = 560717) B560717
theorem B373827 : Blo 370760 373827 := bstep (se 1 (by rfl) ⟨280370, by rfl⟩ : syracuseStep 373827 = 560741) B560741
theorem B1258577 : Blo 370760 1258577 := bstep (se 2 (by rfl) ⟨471966, by rfl⟩ : syracuseStep 1258577 = 943933) B943933
theorem B373843 : Blo 370760 373843 := bstep (se 1 (by rfl) ⟨280382, by rfl⟩ : syracuseStep 373843 = 560765) B560765
theorem B373859 : Blo 370760 373859 := bstep (se 1 (by rfl) ⟨280394, by rfl⟩ : syracuseStep 373859 = 560789) B560789
theorem B373875 : Blo 370760 373875 := bstep (se 1 (by rfl) ⟨280406, by rfl⟩ : syracuseStep 373875 = 560813) B560813
theorem B373891 : Blo 370760 373891 := bstep (se 1 (by rfl) ⟨280418, by rfl⟩ : syracuseStep 373891 = 560837) B560837
theorem B373907 : Blo 370760 373907 := bstep (se 1 (by rfl) ⟨280430, by rfl⟩ : syracuseStep 373907 = 560861) B560861
theorem B373923 : Blo 370760 373923 := bstep (se 1 (by rfl) ⟨280442, by rfl⟩ : syracuseStep 373923 = 560885) B560885
theorem B373939 : Blo 370760 373939 := bstep (se 1 (by rfl) ⟨280454, by rfl⟩ : syracuseStep 373939 = 560909) B560909
theorem B373955 : Blo 370760 373955 := bstep (se 1 (by rfl) ⟨280466, by rfl⟩ : syracuseStep 373955 = 560933) B560933
theorem B373971 : Blo 370760 373971 := bstep (se 1 (by rfl) ⟨280478, by rfl⟩ : syracuseStep 373971 = 560957) B560957
theorem B373987 : Blo 370760 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B374003 : Blo 370760 374003 := bstep (se 1 (by rfl) ⟨280502, by rfl⟩ : syracuseStep 374003 = 561005) B561005
theorem B898307 : Blo 370760 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B374019 : Blo 370760 374019 := bstep (se 1 (by rfl) ⟨280514, by rfl⟩ : syracuseStep 374019 = 561029) B561029
theorem B374035 : Blo 370760 374035 := bstep (se 1 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 374035 = 561053) B561053
theorem B374051 : Blo 370760 374051 := bstep (se 1 (by rfl) ⟨280538, by rfl⟩ : syracuseStep 374051 = 561077) B561077
theorem B374067 : Blo 370760 374067 := bstep (se 1 (by rfl) ⟨280550, by rfl⟩ : syracuseStep 374067 = 561101) B561101
theorem B472387 : Blo 370760 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B374083 : Blo 370760 374083 := bstep (se 1 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 374083 = 561125) B561125
theorem B374099 : Blo 370760 374099 := bstep (se 1 (by rfl) ⟨280574, by rfl⟩ : syracuseStep 374099 = 561149) B561149
theorem B374115 : Blo 370760 374115 := bstep (se 1 (by rfl) ⟨280586, by rfl⟩ : syracuseStep 374115 = 561173) B561173
theorem B374131 : Blo 370760 374131 := bstep (se 1 (by rfl) ⟨280598, by rfl⟩ : syracuseStep 374131 = 561197) B561197
theorem B374147 : Blo 370760 374147 := bstep (se 1 (by rfl) ⟨280610, by rfl⟩ : syracuseStep 374147 = 561221) B561221
theorem B374163 : Blo 370760 374163 := bstep (se 1 (by rfl) ⟨280622, by rfl⟩ : syracuseStep 374163 = 561245) B561245
theorem B472483 : Blo 370760 472483 := bstep (se 1 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 472483 = 708725) B708725
theorem B374179 : Blo 370760 374179 := bstep (se 1 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 374179 = 561269) B561269
theorem B374195 : Blo 370760 374195 := bstep (se 1 (by rfl) ⟨280646, by rfl⟩ : syracuseStep 374195 = 561293) B561293
theorem B898499 : Blo 370760 898499 := bstep (se 1 (by rfl) ⟨673874, by rfl⟩ : syracuseStep 898499 = 1347749) B1347749
theorem B374211 : Blo 370760 374211 := bstep (se 1 (by rfl) ⟨280658, by rfl⟩ : syracuseStep 374211 = 561317) B561317
theorem B374227 : Blo 370760 374227 := bstep (se 1 (by rfl) ⟨280670, by rfl⟩ : syracuseStep 374227 = 561341) B561341
theorem B374243 : Blo 370760 374243 := bstep (se 1 (by rfl) ⟨280682, by rfl⟩ : syracuseStep 374243 = 561365) B561365
theorem B374259 : Blo 370760 374259 := bstep (se 1 (by rfl) ⟨280694, by rfl⟩ : syracuseStep 374259 = 561389) B561389
theorem B374275 : Blo 370760 374275 := bstep (se 1 (by rfl) ⟨280706, by rfl⟩ : syracuseStep 374275 = 561413) B561413
theorem B898577 : Blo 370760 898577 := bstep (se 2 (by rfl) ⟨336966, by rfl⟩ : syracuseStep 898577 = 673933) B673933
theorem B374291 : Blo 370760 374291 := bstep (se 1 (by rfl) ⟨280718, by rfl⟩ : syracuseStep 374291 = 561437) B561437
theorem B374307 : Blo 370760 374307 := bstep (se 1 (by rfl) ⟨280730, by rfl⟩ : syracuseStep 374307 = 561461) B561461
theorem B374323 : Blo 370760 374323 := bstep (se 1 (by rfl) ⟨280742, by rfl⟩ : syracuseStep 374323 = 561485) B561485
theorem B374339 : Blo 370760 374339 := bstep (se 1 (by rfl) ⟨280754, by rfl⟩ : syracuseStep 374339 = 561509) B561509
theorem B374355 : Blo 370760 374355 := bstep (se 1 (by rfl) ⟨280766, by rfl⟩ : syracuseStep 374355 = 561533) B561533
theorem B374371 : Blo 370760 374371 := bstep (se 1 (by rfl) ⟨280778, by rfl⟩ : syracuseStep 374371 = 561557) B561557
theorem B1259117 : Blo 370760 1259117 := bstep (se 3 (by rfl) ⟨236084, by rfl⟩ : syracuseStep 1259117 = 472169) B472169
theorem B374387 : Blo 370760 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B374403 : Blo 370760 374403 := bstep (se 1 (by rfl) ⟨280802, by rfl⟩ : syracuseStep 374403 = 561605) B561605
theorem B374419 : Blo 370760 374419 := bstep (se 1 (by rfl) ⟨280814, by rfl⟩ : syracuseStep 374419 = 561629) B561629
theorem B1259171 : Blo 370760 1259171 := bstep (se 1 (by rfl) ⟨944378, by rfl⟩ : syracuseStep 1259171 = 1888757) B1888757
theorem B374435 : Blo 370760 374435 := bstep (se 1 (by rfl) ⟨280826, by rfl⟩ : syracuseStep 374435 = 561653) B561653
theorem B374451 : Blo 370760 374451 := bstep (se 1 (by rfl) ⟨280838, by rfl⟩ : syracuseStep 374451 = 561677) B561677
theorem B374467 : Blo 370760 374467 := bstep (se 1 (by rfl) ⟨280850, by rfl⟩ : syracuseStep 374467 = 561701) B561701
theorem B898769 : Blo 370760 898769 := bstep (se 2 (by rfl) ⟨337038, by rfl⟩ : syracuseStep 898769 = 674077) B674077
theorem B374483 : Blo 370760 374483 := bstep (se 1 (by rfl) ⟨280862, by rfl⟩ : syracuseStep 374483 = 561725) B561725
theorem B374499 : Blo 370760 374499 := bstep (se 1 (by rfl) ⟨280874, by rfl⟩ : syracuseStep 374499 = 561749) B561749
theorem B374515 : Blo 370760 374515 := bstep (se 1 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 374515 = 561773) B561773
theorem B374531 : Blo 370760 374531 := bstep (se 1 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 374531 = 561797) B561797
theorem B374547 : Blo 370760 374547 := bstep (se 1 (by rfl) ⟨280910, by rfl⟩ : syracuseStep 374547 = 561821) B561821
theorem B505633 : Blo 370760 505633 := bstep (se 2 (by rfl) ⟨189612, by rfl⟩ : syracuseStep 505633 = 379225) B379225
theorem B374563 : Blo 370760 374563 := bstep (se 1 (by rfl) ⟨280922, by rfl⟩ : syracuseStep 374563 = 561845) B561845
theorem B374579 : Blo 370760 374579 := bstep (se 1 (by rfl) ⟨280934, by rfl⟩ : syracuseStep 374579 = 561869) B561869
theorem B1193795 : Blo 370760 1193795 := bstep (se 1 (by rfl) ⟨895346, by rfl⟩ : syracuseStep 1193795 = 1790693) B1790693
theorem B374595 : Blo 370760 374595 := bstep (se 1 (by rfl) ⟨280946, by rfl⟩ : syracuseStep 374595 = 561893) B561893
theorem B374611 : Blo 370760 374611 := bstep (se 1 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 374611 = 561917) B561917
theorem B374627 : Blo 370760 374627 := bstep (se 1 (by rfl) ⟨280970, by rfl⟩ : syracuseStep 374627 = 561941) B561941
theorem B374643 : Blo 370760 374643 := bstep (se 1 (by rfl) ⟨280982, by rfl⟩ : syracuseStep 374643 = 561965) B561965
theorem B374659 : Blo 370760 374659 := bstep (se 1 (by rfl) ⟨280994, by rfl⟩ : syracuseStep 374659 = 561989) B561989
theorem B472979 : Blo 370760 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B374675 : Blo 370760 374675 := bstep (se 1 (by rfl) ⟨281006, by rfl⟩ : syracuseStep 374675 = 562013) B562013
theorem B374691 : Blo 370760 374691 := bstep (se 1 (by rfl) ⟨281018, by rfl⟩ : syracuseStep 374691 = 562037) B562037
theorem B1259441 : Blo 370760 1259441 := bstep (se 2 (by rfl) ⟨472290, by rfl⟩ : syracuseStep 1259441 = 944581) B944581
theorem B374707 : Blo 370760 374707 := bstep (se 1 (by rfl) ⟨281030, by rfl⟩ : syracuseStep 374707 = 562061) B562061
theorem B374723 : Blo 370760 374723 := bstep (se 1 (by rfl) ⟨281042, by rfl⟩ : syracuseStep 374723 = 562085) B562085
theorem B374739 : Blo 370760 374739 := bstep (se 1 (by rfl) ⟨281054, by rfl⟩ : syracuseStep 374739 = 562109) B562109
theorem B374755 : Blo 370760 374755 := bstep (se 1 (by rfl) ⟨281066, by rfl⟩ : syracuseStep 374755 = 562133) B562133
theorem B2144333 : Blo 370760 2144333 := bstep (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) B804125
theorem B669809 : Blo 370760 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B899267 : Blo 370760 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B1194193 : Blo 370760 1194193 := bstep (se 2 (by rfl) ⟨447822, by rfl⟩ : syracuseStep 1194193 = 895645) B895645
theorem B1194257 : Blo 370760 1194257 := bstep (se 2 (by rfl) ⟨447846, by rfl⟩ : syracuseStep 1194257 = 895693) B895693
theorem B899345 : Blo 370760 899345 := bstep (se 2 (by rfl) ⟨337254, by rfl⟩ : syracuseStep 899345 = 674509) B674509
theorem B1259981 : Blo 370760 1259981 := bstep (se 3 (by rfl) ⟨236246, by rfl⟩ : syracuseStep 1259981 = 472493) B472493
theorem B1260035 : Blo 370760 1260035 := bstep (se 1 (by rfl) ⟨945026, by rfl⟩ : syracuseStep 1260035 = 1890053) B1890053
theorem B473683 : Blo 370760 473683 := bstep (se 1 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 473683 = 710525) B710525
theorem B3029645 : Blo 370760 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B899729 : Blo 370760 899729 := bstep (se 2 (by rfl) ⟨337398, by rfl⟩ : syracuseStep 899729 = 674797) B674797
theorem B1063601 : Blo 370760 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B473779 : Blo 370760 473779 := bstep (se 1 (by rfl) ⟨355334, by rfl⟩ : syracuseStep 473779 = 710669) B710669
theorem B637699 : Blo 370760 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B1260305 : Blo 370760 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B834353 : Blo 370760 834353 := bstep (se 2 (by rfl) ⟨312882, by rfl⟩ : syracuseStep 834353 = 625765) B625765
theorem B834371 : Blo 370760 834371 := bstep (se 1 (by rfl) ⟨625778, by rfl⟩ : syracuseStep 834371 = 1251557) B1251557
theorem B1063793 : Blo 370760 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B539617 : Blo 370760 539617 := bstep (se 2 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 539617 = 404713) B404713
theorem B2833379 : Blo 370760 2833379 := bstep (se 1 (by rfl) ⟨2125034, by rfl⟩ : syracuseStep 2833379 = 4250069) B4250069
theorem B834641 : Blo 370760 834641 := bstep (se 2 (by rfl) ⟨312990, by rfl⟩ : syracuseStep 834641 = 625981) B625981
theorem B834659 : Blo 370760 834659 := bstep (se 1 (by rfl) ⟨625994, by rfl⟩ : syracuseStep 834659 = 1251989) B1251989
theorem B1883249 : Blo 370760 1883249 := bstep (se 2 (by rfl) ⟨706218, by rfl⟩ : syracuseStep 1883249 = 1412437) B1412437
theorem B474275 : Blo 370760 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B2047153 : Blo 370760 2047153 := bstep (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) B1535365
theorem B1391843 : Blo 370760 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B2112803 : Blo 370760 2112803 := bstep (se 1 (by rfl) ⟨1584602, by rfl⟩ : syracuseStep 2112803 = 3169205) B3169205
theorem B1260845 : Blo 370760 1260845 := bstep (se 3 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 1260845 = 472817) B472817
theorem B5356853 : Blo 370760 5356853 := bstep (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) B502205
theorem B1260899 : Blo 370760 1260899 := bstep (se 1 (by rfl) ⟨945674, by rfl⟩ : syracuseStep 1260899 = 1891349) B1891349
theorem B834929 : Blo 370760 834929 := bstep (se 2 (by rfl) ⟨313098, by rfl⟩ : syracuseStep 834929 = 626197) B626197
theorem B2014577 : Blo 370760 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B834947 : Blo 370760 834947 := bstep (se 1 (by rfl) ⟨626210, by rfl⟩ : syracuseStep 834947 = 1252421) B1252421
theorem B6372917 : Blo 370760 6372917 := bstep (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) B597461
theorem B1261169 : Blo 370760 1261169 := bstep (se 2 (by rfl) ⟨472938, by rfl⟩ : syracuseStep 1261169 = 945877) B945877
theorem B835217 : Blo 370760 835217 := bstep (se 2 (by rfl) ⟨313206, by rfl⟩ : syracuseStep 835217 = 626413) B626413
theorem B835235 : Blo 370760 835235 := bstep (se 1 (by rfl) ⟨626426, by rfl⟩ : syracuseStep 835235 = 1252853) B1252853
theorem B605875 : Blo 370760 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B704305 : Blo 370760 704305 := bstep (se 2 (by rfl) ⟨264114, by rfl⟩ : syracuseStep 704305 = 528229) B528229
theorem B1064785 : Blo 370760 1064785 := bstep (se 2 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 1064785 = 798589) B798589
theorem B835505 : Blo 370760 835505 := bstep (se 2 (by rfl) ⟨313314, by rfl⟩ : syracuseStep 835505 = 626629) B626629
theorem B835523 : Blo 370760 835523 := bstep (se 1 (by rfl) ⟨626642, by rfl⟩ : syracuseStep 835523 = 1253285) B1253285
theorem B1130449 : Blo 370760 1130449 := bstep (se 2 (by rfl) ⟨423918, by rfl⟩ : syracuseStep 1130449 = 847837) B847837
theorem B606289 : Blo 370760 606289 := bstep (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) B454717
theorem B1065059 : Blo 370760 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B1261709 : Blo 370760 1261709 := bstep (se 3 (by rfl) ⟨236570, by rfl⟩ : syracuseStep 1261709 = 473141) B473141
theorem B1261763 : Blo 370760 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B835793 : Blo 370760 835793 := bstep (se 2 (by rfl) ⟨313422, by rfl⟩ : syracuseStep 835793 = 626845) B626845
theorem B835811 : Blo 370760 835811 := bstep (se 1 (by rfl) ⟨626858, by rfl⟩ : syracuseStep 835811 = 1253717) B1253717
theorem B1589539 : Blo 370760 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B1065251 : Blo 370760 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B4309361 : Blo 370760 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B5718413 : Blo 370760 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B1262033 : Blo 370760 1262033 := bstep (se 2 (by rfl) ⟨473262, by rfl⟩ : syracuseStep 1262033 = 946525) B946525
theorem B836081 : Blo 370760 836081 := bstep (se 2 (by rfl) ⟨313530, by rfl⟩ : syracuseStep 836081 = 627061) B627061
theorem B836099 : Blo 370760 836099 := bstep (se 1 (by rfl) ⟨627074, by rfl⟩ : syracuseStep 836099 = 1254149) B1254149
theorem B1884707 : Blo 370760 1884707 := bstep (se 1 (by rfl) ⟨1413530, by rfl⟩ : syracuseStep 1884707 = 2827061) B2827061
theorem B803537 : Blo 370760 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B4244237 : Blo 370760 4244237 := bstep (se 3 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 4244237 = 1591589) B1591589
theorem B836369 : Blo 370760 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B836387 : Blo 370760 836387 := bstep (se 1 (by rfl) ⟨627290, by rfl⟩ : syracuseStep 836387 = 1254581) B1254581
theorem B705361 : Blo 370760 705361 := bstep (se 2 (by rfl) ⟨264510, by rfl⟩ : syracuseStep 705361 = 529021) B529021
theorem B1262573 : Blo 370760 1262573 := bstep (se 3 (by rfl) ⟨236732, by rfl⟩ : syracuseStep 1262573 = 473465) B473465
theorem B1262627 : Blo 370760 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B836657 : Blo 370760 836657 := bstep (se 2 (by rfl) ⟨313746, by rfl⟩ : syracuseStep 836657 = 627493) B627493
theorem B836675 : Blo 370760 836675 := bstep (se 1 (by rfl) ⟨627506, by rfl⟩ : syracuseStep 836675 = 1255013) B1255013
theorem B1066061 : Blo 370760 1066061 := bstep (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) B399773
theorem B2114693 : Blo 370760 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B705763 : Blo 370760 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B1524977 : Blo 370760 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B1066243 : Blo 370760 1066243 := bstep (se 1 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 1066243 = 1599365) B1599365
theorem B705809 : Blo 370760 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B1262897 : Blo 370760 1262897 := bstep (se 2 (by rfl) ⟨473586, by rfl⟩ : syracuseStep 1262897 = 947173) B947173
theorem B1885517 : Blo 370760 1885517 := bstep (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) B707069
theorem B836945 : Blo 370760 836945 := bstep (se 2 (by rfl) ⟨313854, by rfl⟩ : syracuseStep 836945 = 627709) B627709
theorem B836963 : Blo 370760 836963 := bstep (se 1 (by rfl) ⟨627722, by rfl⟩ : syracuseStep 836963 = 1255445) B1255445
theorem B2377187 : Blo 370760 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B1590769 : Blo 370760 1590769 := bstep (se 2 (by rfl) ⟨596538, by rfl⟩ : syracuseStep 1590769 = 1193077) B1193077
theorem B706097 : Blo 370760 706097 := bstep (se 2 (by rfl) ⟨264786, by rfl⟩ : syracuseStep 706097 = 529573) B529573
theorem B837233 : Blo 370760 837233 := bstep (se 2 (by rfl) ⟨313962, by rfl⟩ : syracuseStep 837233 = 627925) B627925
theorem B837251 : Blo 370760 837251 := bstep (se 1 (by rfl) ⟨627938, by rfl⟩ : syracuseStep 837251 = 1255877) B1255877
theorem B1066733 : Blo 370760 1066733 := bstep (se 3 (by rfl) ⟨200012, by rfl⟩ : syracuseStep 1066733 = 400025) B400025
theorem B1263437 : Blo 370760 1263437 := bstep (se 3 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 1263437 = 473789) B473789
theorem B1263491 : Blo 370760 1263491 := bstep (se 1 (by rfl) ⟨947618, by rfl⟩ : syracuseStep 1263491 = 1895237) B1895237
theorem B837521 : Blo 370760 837521 := bstep (se 2 (by rfl) ⟨314070, by rfl⟩ : syracuseStep 837521 = 628141) B628141
theorem B837539 : Blo 370760 837539 := bstep (se 1 (by rfl) ⟨628154, by rfl⟩ : syracuseStep 837539 = 1256309) B1256309
theorem B1263761 : Blo 370760 1263761 := bstep (se 2 (by rfl) ⟨473910, by rfl⟩ : syracuseStep 1263761 = 947821) B947821
theorem B1427633 : Blo 370760 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B837809 : Blo 370760 837809 := bstep (se 2 (by rfl) ⟨314178, by rfl⟩ : syracuseStep 837809 = 628357) B628357
theorem B837827 : Blo 370760 837827 := bstep (se 1 (by rfl) ⟨628370, by rfl⟩ : syracuseStep 837827 = 1256741) B1256741
theorem B706819 : Blo 370760 706819 := bstep (se 1 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 706819 = 1060229) B1060229
theorem B1198435 : Blo 370760 1198435 := bstep (se 1 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 1198435 = 1797653) B1797653
theorem B838097 : Blo 370760 838097 := bstep (se 2 (by rfl) ⟨314286, by rfl⟩ : syracuseStep 838097 = 628573) B628573
theorem B838115 : Blo 370760 838115 := bstep (se 1 (by rfl) ⟨628586, by rfl⟩ : syracuseStep 838115 = 1257173) B1257173
theorem B4082275 : Blo 370760 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B1264301 : Blo 370760 1264301 := bstep (se 3 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 1264301 = 474113) B474113
theorem B1821361 : Blo 370760 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B707267 : Blo 370760 707267 := bstep (se 1 (by rfl) ⟨530450, by rfl⟩ : syracuseStep 707267 = 1060901) B1060901
theorem B1264355 : Blo 370760 1264355 := bstep (se 1 (by rfl) ⟨948266, by rfl⟩ : syracuseStep 1264355 = 1896533) B1896533
theorem B838385 : Blo 370760 838385 := bstep (se 2 (by rfl) ⟨314394, by rfl⟩ : syracuseStep 838385 = 628789) B628789
theorem B838403 : Blo 370760 838403 := bstep (se 1 (by rfl) ⟨628802, by rfl⟩ : syracuseStep 838403 = 1257605) B1257605
theorem B4049777 : Blo 370760 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B707555 : Blo 370760 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B1264625 : Blo 370760 1264625 := bstep (se 2 (by rfl) ⟨474234, by rfl⟩ : syracuseStep 1264625 = 948469) B948469
theorem B2018317 : Blo 370760 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B838673 : Blo 370760 838673 := bstep (se 2 (by rfl) ⟨314502, by rfl⟩ : syracuseStep 838673 = 629005) B629005
theorem B838691 : Blo 370760 838691 := bstep (se 1 (by rfl) ⟨629018, by rfl⟩ : syracuseStep 838691 = 1258037) B1258037
theorem B1002637 : Blo 370760 1002637 := bstep (se 3 (by rfl) ⟨187994, by rfl⟩ : syracuseStep 1002637 = 375989) B375989
theorem B1232131 : Blo 370760 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B838961 : Blo 370760 838961 := bstep (se 2 (by rfl) ⟨314610, by rfl⟩ : syracuseStep 838961 = 629221) B629221
theorem B838979 : Blo 370760 838979 := bstep (se 1 (by rfl) ⟨629234, by rfl⟩ : syracuseStep 838979 = 1258469) B1258469
theorem B3395141 : Blo 370760 3395141 := bstep (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) B636589
theorem B839249 : Blo 370760 839249 := bstep (se 2 (by rfl) ⟨314718, by rfl⟩ : syracuseStep 839249 = 629437) B629437
theorem B839267 : Blo 370760 839267 := bstep (se 1 (by rfl) ⟨629450, by rfl⟩ : syracuseStep 839267 = 1258901) B1258901
theorem B4247153 : Blo 370760 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B446131 : Blo 370760 446131 := bstep (se 1 (by rfl) ⟨334598, by rfl⟩ : syracuseStep 446131 = 669197) B669197
theorem B642883 : Blo 370760 642883 := bstep (se 1 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 642883 = 964325) B964325
theorem B839537 : Blo 370760 839537 := bstep (se 2 (by rfl) ⟨314826, by rfl⟩ : syracuseStep 839537 = 629653) B629653
theorem B839555 : Blo 370760 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B708497 : Blo 370760 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B512083 : Blo 370760 512083 := bstep (se 1 (by rfl) ⟨384062, by rfl⟩ : syracuseStep 512083 = 768125) B768125
theorem B839825 : Blo 370760 839825 := bstep (se 2 (by rfl) ⟨314934, by rfl⟩ : syracuseStep 839825 = 629869) B629869
theorem B839843 : Blo 370760 839843 := bstep (se 1 (by rfl) ⟨629882, by rfl⟩ : syracuseStep 839843 = 1259765) B1259765
theorem B1888433 : Blo 370760 1888433 := bstep (se 2 (by rfl) ⟨708162, by rfl⟩ : syracuseStep 1888433 = 1416325) B1416325
theorem B2838725 : Blo 370760 2838725 := bstep (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) B532261
theorem B24170723 : Blo 370760 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B1921265 : Blo 370760 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B840113 : Blo 370760 840113 := bstep (se 2 (by rfl) ⟨315042, by rfl⟩ : syracuseStep 840113 = 630085) B630085
theorem B840131 : Blo 370760 840131 := bstep (se 1 (by rfl) ⟨630098, by rfl⟩ : syracuseStep 840131 = 1260197) B1260197
theorem B17125829 : Blo 370760 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B1004141 : Blo 370760 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B840401 : Blo 370760 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B840419 : Blo 370760 840419 := bstep (se 1 (by rfl) ⟨630314, by rfl⟩ : syracuseStep 840419 = 1260629) B1260629
theorem B709393 : Blo 370760 709393 := bstep (se 2 (by rfl) ⟨266022, by rfl⟩ : syracuseStep 709393 = 532045) B532045
theorem B906083 : Blo 370760 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B1528739 : Blo 370760 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B709553 : Blo 370760 709553 := bstep (se 2 (by rfl) ⟨266082, by rfl⟩ : syracuseStep 709553 = 532165) B532165
theorem B840689 : Blo 370760 840689 := bstep (se 2 (by rfl) ⟨315258, by rfl⟩ : syracuseStep 840689 = 630517) B630517
theorem B840707 : Blo 370760 840707 := bstep (se 1 (by rfl) ⟨630530, by rfl⟩ : syracuseStep 840707 = 1261061) B1261061
theorem B513091 : Blo 370760 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B939185 : Blo 370760 939185 := bstep (se 2 (by rfl) ⟨352194, by rfl⟩ : syracuseStep 939185 = 704389) B704389
theorem B939235 : Blo 370760 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B840977 : Blo 370760 840977 := bstep (se 2 (by rfl) ⟨315366, by rfl⟩ : syracuseStep 840977 = 630733) B630733
theorem B840995 : Blo 370760 840995 := bstep (se 1 (by rfl) ⟨630746, by rfl⟩ : syracuseStep 840995 = 1261493) B1261493
theorem B709955 : Blo 370760 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B447827 : Blo 370760 447827 := bstep (se 1 (by rfl) ⟨335870, by rfl⟩ : syracuseStep 447827 = 671741) B671741
theorem B939377 : Blo 370760 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B2381233 : Blo 370760 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B841265 : Blo 370760 841265 := bstep (se 2 (by rfl) ⟨315474, by rfl⟩ : syracuseStep 841265 = 630949) B630949
theorem B841283 : Blo 370760 841283 := bstep (se 1 (by rfl) ⟨630962, by rfl⟩ : syracuseStep 841283 = 1261925) B1261925
theorem B1889891 : Blo 370760 1889891 := bstep (se 1 (by rfl) ⟨1417418, by rfl⟩ : syracuseStep 1889891 = 2834837) B2834837
theorem B1431217 : Blo 370760 1431217 := bstep (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) B1073413
theorem B907057 : Blo 370760 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B1595213 : Blo 370760 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B841553 : Blo 370760 841553 := bstep (se 2 (by rfl) ⟨315582, by rfl⟩ : syracuseStep 841553 = 631165) B631165
theorem B841571 : Blo 370760 841571 := bstep (se 1 (by rfl) ⟨631178, by rfl⟩ : syracuseStep 841571 = 1262357) B1262357
theorem B841841 : Blo 370760 841841 := bstep (se 2 (by rfl) ⟨315690, by rfl⟩ : syracuseStep 841841 = 631381) B631381
theorem B841859 : Blo 370760 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B710851 : Blo 370760 710851 := bstep (se 1 (by rfl) ⟨533138, by rfl⟩ : syracuseStep 710851 = 1066277) B1066277
theorem B3201221 : Blo 370760 3201221 := bstep (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) B600229
theorem B940369 : Blo 370760 940369 := bstep (se 2 (by rfl) ⟨352638, by rfl⟩ : syracuseStep 940369 = 705277) B705277
theorem B711011 : Blo 370760 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B1890701 : Blo 370760 1890701 := bstep (se 3 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 1890701 = 709013) B709013
theorem B842129 : Blo 370760 842129 := bstep (se 2 (by rfl) ⟨315798, by rfl⟩ : syracuseStep 842129 = 631597) B631597
theorem B842147 : Blo 370760 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B940643 : Blo 370760 940643 := bstep (se 1 (by rfl) ⟨705482, by rfl⟩ : syracuseStep 940643 = 1410965) B1410965
theorem B842417 : Blo 370760 842417 := bstep (se 2 (by rfl) ⟨315906, by rfl⟩ : syracuseStep 842417 = 631813) B631813
theorem B842435 : Blo 370760 842435 := bstep (se 1 (by rfl) ⟨631826, by rfl⟩ : syracuseStep 842435 = 1263653) B1263653
theorem B940835 : Blo 370760 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B2120525 : Blo 370760 2120525 := bstep (se 3 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 2120525 = 795197) B795197
theorem B1006445 : Blo 370760 1006445 := bstep (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) B377417
theorem B842705 : Blo 370760 842705 := bstep (se 2 (by rfl) ⟨316014, by rfl⟩ : syracuseStep 842705 = 632029) B632029
theorem B842723 : Blo 370760 842723 := bstep (se 1 (by rfl) ⟨632042, by rfl⟩ : syracuseStep 842723 = 1264085) B1264085
theorem B1006573 : Blo 370760 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B1006769 : Blo 370760 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B2579653 : Blo 370760 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B842993 : Blo 370760 842993 := bstep (se 2 (by rfl) ⟨316122, by rfl⟩ : syracuseStep 842993 = 632245) B632245
theorem B843011 : Blo 370760 843011 := bstep (se 1 (by rfl) ⟨632258, by rfl⟩ : syracuseStep 843011 = 1264517) B1264517
theorem B1072397 : Blo 370760 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B2022833 : Blo 370760 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B417235 : Blo 370760 417235 := bstep (se 1 (by rfl) ⟨312926, by rfl⟩ : syracuseStep 417235 = 625853) B625853
theorem B417379 : Blo 370760 417379 := bstep (se 1 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 417379 = 626069) B626069
theorem B450211 : Blo 370760 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B941777 : Blo 370760 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B417523 : Blo 370760 417523 := bstep (se 1 (by rfl) ⟨313142, by rfl⟩ : syracuseStep 417523 = 626285) B626285
theorem B941827 : Blo 370760 941827 := bstep (se 1 (by rfl) ⟨706370, by rfl⟩ : syracuseStep 941827 = 1412741) B1412741
theorem B2023181 : Blo 370760 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B417667 : Blo 370760 417667 := bstep (se 1 (by rfl) ⟨313250, by rfl⟩ : syracuseStep 417667 = 626501) B626501
theorem B941969 : Blo 370760 941969 := bstep (se 2 (by rfl) ⟨353238, by rfl⟩ : syracuseStep 941969 = 706477) B706477
theorem B417811 : Blo 370760 417811 := bstep (se 1 (by rfl) ⟨313358, by rfl⟩ : syracuseStep 417811 = 626717) B626717
theorem B909425 : Blo 370760 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B417955 : Blo 370760 417955 := bstep (se 1 (by rfl) ⟨313466, by rfl⟩ : syracuseStep 417955 = 626933) B626933
theorem B418099 : Blo 370760 418099 := bstep (se 1 (by rfl) ⟨313574, by rfl⟩ : syracuseStep 418099 = 627149) B627149
theorem B6447413 : Blo 370760 6447413 := bstep (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) B604445
theorem B418243 : Blo 370760 418243 := bstep (se 1 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 418243 = 627365) B627365
theorem B1696241 : Blo 370760 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1008173 : Blo 370760 1008173 := bstep (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) B378065
theorem B418387 : Blo 370760 418387 := bstep (se 1 (by rfl) ⟨313790, by rfl⟩ : syracuseStep 418387 = 627581) B627581
theorem B418531 : Blo 370760 418531 := bstep (se 1 (by rfl) ⟨313898, by rfl⟩ : syracuseStep 418531 = 627797) B627797
theorem B1696589 : Blo 370760 1696589 := bstep (se 3 (by rfl) ⟨318110, by rfl⟩ : syracuseStep 1696589 = 636221) B636221
theorem B3007331 : Blo 370760 3007331 := bstep (se 1 (by rfl) ⟨2255498, by rfl⟩ : syracuseStep 3007331 = 4510997) B4510997
theorem B942961 : Blo 370760 942961 := bstep (se 2 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 942961 = 707221) B707221
theorem B4547441 : Blo 370760 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B418675 : Blo 370760 418675 := bstep (se 1 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 418675 = 628013) B628013
theorem B418819 : Blo 370760 418819 := bstep (se 1 (by rfl) ⟨314114, by rfl⟩ : syracuseStep 418819 = 628229) B628229
theorem B2122757 : Blo 370760 2122757 := bstep (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) B398017
theorem B943235 : Blo 370760 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B418963 : Blo 370760 418963 := bstep (se 1 (by rfl) ⟨314222, by rfl⟩ : syracuseStep 418963 = 628445) B628445
theorem B1008845 : Blo 370760 1008845 := bstep (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) B378317
theorem B1893617 : Blo 370760 1893617 := bstep (se 2 (by rfl) ⟨710106, by rfl⟩ : syracuseStep 1893617 = 1420213) B1420213
theorem B419107 : Blo 370760 419107 := bstep (se 1 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 419107 = 628661) B628661
theorem B943427 : Blo 370760 943427 := bstep (se 1 (by rfl) ⟨707570, by rfl⟩ : syracuseStep 943427 = 1415141) B1415141
theorem B419251 : Blo 370760 419251 := bstep (se 1 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 419251 = 628877) B628877
theorem B3630563 : Blo 370760 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B4318733 : Blo 370760 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B419395 : Blo 370760 419395 := bstep (se 1 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 419395 = 629093) B629093
theorem B2123441 : Blo 370760 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B419539 : Blo 370760 419539 := bstep (se 1 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 419539 = 629309) B629309
theorem B419683 : Blo 370760 419683 := bstep (se 1 (by rfl) ⟨314762, by rfl⟩ : syracuseStep 419683 = 629525) B629525
theorem B2844557 : Blo 370760 2844557 := bstep (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) B1066709
theorem B419827 : Blo 370760 419827 := bstep (se 1 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 419827 = 629741) B629741
theorem B1599587 : Blo 370760 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B419971 : Blo 370760 419971 := bstep (se 1 (by rfl) ⟨314978, by rfl⟩ : syracuseStep 419971 = 629957) B629957
theorem B944369 : Blo 370760 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B420115 : Blo 370760 420115 := bstep (se 1 (by rfl) ⟨315086, by rfl⟩ : syracuseStep 420115 = 630173) B630173
theorem B944419 : Blo 370760 944419 := bstep (se 1 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 944419 = 1416629) B1416629
theorem B18147725 : Blo 370760 18147725 := bstep (se 3 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 18147725 = 6805397) B6805397
theorem B420259 : Blo 370760 420259 := bstep (se 1 (by rfl) ⟨315194, by rfl⟩ : syracuseStep 420259 = 630389) B630389
theorem B944561 : Blo 370760 944561 := bstep (se 2 (by rfl) ⟨354210, by rfl⟩ : syracuseStep 944561 = 708421) B708421
theorem B420403 : Blo 370760 420403 := bstep (se 1 (by rfl) ⟨315302, by rfl⟩ : syracuseStep 420403 = 630605) B630605
theorem B1895075 : Blo 370760 1895075 := bstep (se 1 (by rfl) ⟨1421306, by rfl⟩ : syracuseStep 1895075 = 2842613) B2842613
theorem B420547 : Blo 370760 420547 := bstep (se 1 (by rfl) ⟨315410, by rfl⟩ : syracuseStep 420547 = 630821) B630821
theorem B420691 : Blo 370760 420691 := bstep (se 1 (by rfl) ⟨315518, by rfl⟩ : syracuseStep 420691 = 631037) B631037
theorem B420835 : Blo 370760 420835 := bstep (se 1 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 420835 = 631253) B631253
theorem B2124899 : Blo 370760 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B420979 : Blo 370760 420979 := bstep (se 1 (by rfl) ⟨315734, by rfl⟩ : syracuseStep 420979 = 631469) B631469
theorem B421123 : Blo 370760 421123 := bstep (se 1 (by rfl) ⟨315842, by rfl⟩ : syracuseStep 421123 = 631685) B631685
theorem B945553 : Blo 370760 945553 := bstep (se 2 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 945553 = 709165) B709165
theorem B421267 : Blo 370760 421267 := bstep (se 1 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 421267 = 631901) B631901
theorem B1895885 : Blo 370760 1895885 := bstep (se 3 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 1895885 = 710957) B710957
theorem B421411 : Blo 370760 421411 := bstep (se 1 (by rfl) ⟨316058, by rfl⟩ : syracuseStep 421411 = 632117) B632117
theorem B945827 : Blo 370760 945827 := bstep (se 1 (by rfl) ⟨709370, by rfl⟩ : syracuseStep 945827 = 1418741) B1418741
theorem B421555 : Blo 370760 421555 := bstep (se 1 (by rfl) ⟨316166, by rfl⟩ : syracuseStep 421555 = 632333) B632333
theorem B5074757 : Blo 370760 5074757 := bstep (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) B951517
theorem B946019 : Blo 370760 946019 := bstep (se 1 (by rfl) ⟨709514, by rfl⟩ : syracuseStep 946019 = 1419029) B1419029
theorem B1798307 : Blo 370760 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B3207395 : Blo 370760 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1700621 : Blo 370760 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B946961 : Blo 370760 946961 := bstep (se 2 (by rfl) ⟨355110, by rfl⟩ : syracuseStep 946961 = 710221) B710221
theorem B947011 : Blo 370760 947011 := bstep (se 1 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 947011 = 1420517) B1420517
theorem B22999949 : Blo 370760 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B947153 : Blo 370760 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B2421829 : Blo 370760 2421829 := bstep (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) B454093
theorem B32240753 : Blo 370760 32240753 := bstep (se 2 (by rfl) ⟨12090282, by rfl⟩ : syracuseStep 32240753 = 24180565) B24180565
theorem B2389283 : Blo 370760 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B6452621 : Blo 370760 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B1570211 : Blo 370760 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B1799651 : Blo 370760 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B1275533 : Blo 370760 1275533 := bstep (se 3 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 1275533 = 478325) B478325
theorem B816817 : Blo 370760 816817 := bstep (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) B612613
theorem B3405509 : Blo 370760 3405509 := bstep (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) B638533
theorem B980689 : Blo 370760 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B718627 : Blo 370760 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B2684771 : Blo 370760 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B948145 : Blo 370760 948145 := bstep (se 2 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 948145 = 711109) B711109
theorem B4782149 : Blo 370760 4782149 := bstep (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) B896653
theorem B3569777 : Blo 370760 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B1800305 : Blo 370760 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B948419 : Blo 370760 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B2128133 : Blo 370760 2128133 := bstep (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) B399025
theorem B7174453 : Blo 370760 7174453 := bstep (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) B672605
theorem B2816369 : Blo 370760 2816369 := bstep (se 2 (by rfl) ⟨1056138, by rfl⟩ : syracuseStep 2816369 = 2112277) B2112277
theorem B948611 : Blo 370760 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B1145507 : Blo 370760 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B916145 : Blo 370760 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B2128589 : Blo 370760 2128589 := bstep (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) B798221
theorem B752483 : Blo 370760 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B1408049 : Blo 370760 1408049 := bstep (se 2 (by rfl) ⟨528018, by rfl⟩ : syracuseStep 1408049 = 1056037) B1056037
theorem B556145 : Blo 370760 556145 := bstep (se 2 (by rfl) ⟨208554, by rfl⟩ : syracuseStep 556145 = 417109) B417109
theorem B556163 : Blo 370760 556163 := bstep (se 1 (by rfl) ⟨417122, by rfl⟩ : syracuseStep 556163 = 834245) B834245
theorem B556193 : Blo 370760 556193 := bstep (se 2 (by rfl) ⟨208572, by rfl⟩ : syracuseStep 556193 = 417145) B417145
theorem B556211 : Blo 370760 556211 := bstep (se 1 (by rfl) ⟨417158, by rfl⟩ : syracuseStep 556211 = 834317) B834317
theorem B556241 : Blo 370760 556241 := bstep (se 2 (by rfl) ⟨208590, by rfl⟩ : syracuseStep 556241 = 417181) B417181
theorem B556259 : Blo 370760 556259 := bstep (se 1 (by rfl) ⟨417194, by rfl⟩ : syracuseStep 556259 = 834389) B834389
theorem B2391281 : Blo 370760 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B556289 : Blo 370760 556289 := bstep (se 2 (by rfl) ⟨208608, by rfl⟩ : syracuseStep 556289 = 417217) B417217
theorem B556307 : Blo 370760 556307 := bstep (se 1 (by rfl) ⟨417230, by rfl⟩ : syracuseStep 556307 = 834461) B834461
theorem B556337 : Blo 370760 556337 := bstep (se 2 (by rfl) ⟨208626, by rfl⟩ : syracuseStep 556337 = 417253) B417253
theorem B556355 : Blo 370760 556355 := bstep (se 1 (by rfl) ⟨417266, by rfl⟩ : syracuseStep 556355 = 834533) B834533
theorem B556385 : Blo 370760 556385 := bstep (se 2 (by rfl) ⟨208644, by rfl⟩ : syracuseStep 556385 = 417289) B417289
theorem B556403 : Blo 370760 556403 := bstep (se 1 (by rfl) ⟨417302, by rfl⟩ : syracuseStep 556403 = 834605) B834605
theorem B556433 : Blo 370760 556433 := bstep (se 2 (by rfl) ⟨208662, by rfl⟩ : syracuseStep 556433 = 417325) B417325
theorem B556451 : Blo 370760 556451 := bstep (se 1 (by rfl) ⟨417338, by rfl⟩ : syracuseStep 556451 = 834677) B834677
theorem B556481 : Blo 370760 556481 := bstep (se 2 (by rfl) ⟨208680, by rfl⟩ : syracuseStep 556481 = 417361) B417361
theorem B556499 : Blo 370760 556499 := bstep (se 1 (by rfl) ⟨417374, by rfl⟩ : syracuseStep 556499 = 834749) B834749
theorem B1080803 : Blo 370760 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B556529 : Blo 370760 556529 := bstep (se 2 (by rfl) ⟨208698, by rfl⟩ : syracuseStep 556529 = 417397) B417397
theorem B556547 : Blo 370760 556547 := bstep (se 1 (by rfl) ⟨417410, by rfl⟩ : syracuseStep 556547 = 834821) B834821
theorem B556577 : Blo 370760 556577 := bstep (se 2 (by rfl) ⟨208716, by rfl⟩ : syracuseStep 556577 = 417433) B417433
theorem B556595 : Blo 370760 556595 := bstep (se 1 (by rfl) ⟨417446, by rfl⟩ : syracuseStep 556595 = 834893) B834893
theorem B556625 : Blo 370760 556625 := bstep (se 2 (by rfl) ⟨208734, by rfl⟩ : syracuseStep 556625 = 417469) B417469
theorem B556643 : Blo 370760 556643 := bstep (se 1 (by rfl) ⟨417482, by rfl⟩ : syracuseStep 556643 = 834965) B834965
theorem B556673 : Blo 370760 556673 := bstep (se 2 (by rfl) ⟨208752, by rfl⟩ : syracuseStep 556673 = 417505) B417505
theorem B556691 : Blo 370760 556691 := bstep (se 1 (by rfl) ⟨417518, by rfl⟩ : syracuseStep 556691 = 835037) B835037
theorem B556721 : Blo 370760 556721 := bstep (se 2 (by rfl) ⟨208770, by rfl⟩ : syracuseStep 556721 = 417541) B417541
theorem B4226741 : Blo 370760 4226741 := bstep (se 5 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 4226741 = 396257) B396257
theorem B556739 : Blo 370760 556739 := bstep (se 1 (by rfl) ⟨417554, by rfl⟩ : syracuseStep 556739 = 835109) B835109
theorem B556769 : Blo 370760 556769 := bstep (se 2 (by rfl) ⟨208788, by rfl⟩ : syracuseStep 556769 = 417577) B417577
theorem B556787 : Blo 370760 556787 := bstep (se 1 (by rfl) ⟨417590, by rfl⟩ : syracuseStep 556787 = 835181) B835181
theorem B556817 : Blo 370760 556817 := bstep (se 2 (by rfl) ⟨208806, by rfl⟩ : syracuseStep 556817 = 417613) B417613
theorem B556835 : Blo 370760 556835 := bstep (se 1 (by rfl) ⟨417626, by rfl⟩ : syracuseStep 556835 = 835253) B835253
theorem B425779 : Blo 370760 425779 := bstep (se 1 (by rfl) ⟨319334, by rfl⟩ : syracuseStep 425779 = 638669) B638669
theorem B556865 : Blo 370760 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B556883 : Blo 370760 556883 := bstep (se 1 (by rfl) ⟨417662, by rfl⟩ : syracuseStep 556883 = 835325) B835325
theorem B556913 : Blo 370760 556913 := bstep (se 2 (by rfl) ⟨208842, by rfl⟩ : syracuseStep 556913 = 417685) B417685
theorem B556931 : Blo 370760 556931 := bstep (se 1 (by rfl) ⟨417698, by rfl⟩ : syracuseStep 556931 = 835397) B835397
theorem B556961 : Blo 370760 556961 := bstep (se 2 (by rfl) ⟨208860, by rfl⟩ : syracuseStep 556961 = 417721) B417721
theorem B556979 : Blo 370760 556979 := bstep (se 1 (by rfl) ⟨417734, by rfl⟩ : syracuseStep 556979 = 835469) B835469
theorem B557009 : Blo 370760 557009 := bstep (se 2 (by rfl) ⟨208878, by rfl⟩ : syracuseStep 557009 = 417757) B417757
theorem B557027 : Blo 370760 557027 := bstep (se 1 (by rfl) ⟨417770, by rfl⟩ : syracuseStep 557027 = 835541) B835541
theorem B557081 : Blo 370760 557081 := bstep (se 2 (by rfl) ⟨208905, by rfl⟩ : syracuseStep 557081 = 417811) B417811
theorem B557195 : Blo 370760 557195 := bstep (se 1 (by rfl) ⟨417896, by rfl⟩ : syracuseStep 557195 = 835793) B835793
theorem B557207 : Blo 370760 557207 := bstep (se 1 (by rfl) ⟨417905, by rfl⟩ : syracuseStep 557207 = 835811) B835811
theorem B557273 : Blo 370760 557273 := bstep (se 2 (by rfl) ⟨208977, by rfl⟩ : syracuseStep 557273 = 417955) B417955
theorem B2425133 : Blo 370760 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B557387 : Blo 370760 557387 := bstep (se 1 (by rfl) ⟨418040, by rfl⟩ : syracuseStep 557387 = 836081) B836081
theorem B557399 : Blo 370760 557399 := bstep (se 1 (by rfl) ⟨418049, by rfl⟩ : syracuseStep 557399 = 836099) B836099
theorem B557465 : Blo 370760 557465 := bstep (se 2 (by rfl) ⟨209049, by rfl⟩ : syracuseStep 557465 = 418099) B418099
theorem B4260275 : Blo 370760 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B557579 : Blo 370760 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B557591 : Blo 370760 557591 := bstep (se 1 (by rfl) ⟨418193, by rfl⟩ : syracuseStep 557591 = 836387) B836387
theorem B557657 : Blo 370760 557657 := bstep (se 2 (by rfl) ⟨209121, by rfl⟩ : syracuseStep 557657 = 418243) B418243
theorem B8553053 : Blo 370760 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B557771 : Blo 370760 557771 := bstep (se 1 (by rfl) ⟨418328, by rfl⟩ : syracuseStep 557771 = 836657) B836657
theorem B557783 : Blo 370760 557783 := bstep (se 1 (by rfl) ⟨418337, by rfl⟩ : syracuseStep 557783 = 836675) B836675
theorem B1409795 : Blo 370760 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B557849 : Blo 370760 557849 := bstep (se 2 (by rfl) ⟨209193, by rfl⟩ : syracuseStep 557849 = 418387) B418387
theorem B1016651 : Blo 370760 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B557963 : Blo 370760 557963 := bstep (se 1 (by rfl) ⟨418472, by rfl⟩ : syracuseStep 557963 = 836945) B836945
theorem B557975 : Blo 370760 557975 := bstep (se 1 (by rfl) ⟨418481, by rfl⟩ : syracuseStep 557975 = 836963) B836963
theorem B558041 : Blo 370760 558041 := bstep (se 2 (by rfl) ⟨209265, by rfl⟩ : syracuseStep 558041 = 418531) B418531
theorem B10159139 : Blo 370760 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B558155 : Blo 370760 558155 := bstep (se 1 (by rfl) ⟨418616, by rfl⟩ : syracuseStep 558155 = 837233) B837233
theorem B558167 : Blo 370760 558167 := bstep (se 1 (by rfl) ⟨418625, by rfl⟩ : syracuseStep 558167 = 837251) B837251
theorem B558233 : Blo 370760 558233 := bstep (se 2 (by rfl) ⟨209337, by rfl⟩ : syracuseStep 558233 = 418675) B418675
theorem B558347 : Blo 370760 558347 := bstep (se 1 (by rfl) ⟨418760, by rfl⟩ : syracuseStep 558347 = 837521) B837521
theorem B558359 : Blo 370760 558359 := bstep (se 1 (by rfl) ⟨418769, by rfl⟩ : syracuseStep 558359 = 837539) B837539
theorem B4523309 : Blo 370760 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B558425 : Blo 370760 558425 := bstep (se 2 (by rfl) ⟨209409, by rfl⟩ : syracuseStep 558425 = 418819) B418819
theorem B951755 : Blo 370760 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B558539 : Blo 370760 558539 := bstep (se 1 (by rfl) ⟨418904, by rfl⟩ : syracuseStep 558539 = 837809) B837809
theorem B2688461 : Blo 370760 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B558551 : Blo 370760 558551 := bstep (se 1 (by rfl) ⟨418913, by rfl⟩ : syracuseStep 558551 = 837827) B837827
theorem B558617 : Blo 370760 558617 := bstep (se 2 (by rfl) ⟨209481, by rfl⟩ : syracuseStep 558617 = 418963) B418963
theorem B558731 : Blo 370760 558731 := bstep (se 1 (by rfl) ⟨419048, by rfl⟩ : syracuseStep 558731 = 838097) B838097
theorem B558743 : Blo 370760 558743 := bstep (se 1 (by rfl) ⟨419057, by rfl⟩ : syracuseStep 558743 = 838115) B838115
theorem B558809 : Blo 370760 558809 := bstep (se 2 (by rfl) ⟨209553, by rfl⟩ : syracuseStep 558809 = 419107) B419107
theorem B2131757 : Blo 370760 2131757 := bstep (se 3 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 2131757 = 799409) B799409
theorem B558923 : Blo 370760 558923 := bstep (se 1 (by rfl) ⟨419192, by rfl⟩ : syracuseStep 558923 = 838385) B838385
theorem B558935 : Blo 370760 558935 := bstep (se 1 (by rfl) ⟨419201, by rfl⟩ : syracuseStep 558935 = 838403) B838403
theorem B4261733 : Blo 370760 4261733 := bstep (se 4 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 4261733 = 799075) B799075
theorem B559001 : Blo 370760 559001 := bstep (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) B419251
theorem B559115 : Blo 370760 559115 := bstep (se 1 (by rfl) ⟨419336, by rfl⟩ : syracuseStep 559115 = 838673) B838673
theorem B559127 : Blo 370760 559127 := bstep (se 1 (by rfl) ⟨419345, by rfl⟩ : syracuseStep 559127 = 838691) B838691
theorem B559193 : Blo 370760 559193 := bstep (se 2 (by rfl) ⟨209697, by rfl⟩ : syracuseStep 559193 = 419395) B419395
theorem B1018049 : Blo 370760 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B559307 : Blo 370760 559307 := bstep (se 1 (by rfl) ⟨419480, by rfl⟩ : syracuseStep 559307 = 838961) B838961
theorem B559319 : Blo 370760 559319 := bstep (se 1 (by rfl) ⟨419489, by rfl⟩ : syracuseStep 559319 = 838979) B838979
theorem B559385 : Blo 370760 559385 := bstep (se 2 (by rfl) ⟨209769, by rfl⟩ : syracuseStep 559385 = 419539) B419539
theorem B5114177 : Blo 370760 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B2263427 : Blo 370760 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B559499 : Blo 370760 559499 := bstep (se 1 (by rfl) ⟨419624, by rfl⟩ : syracuseStep 559499 = 839249) B839249
theorem B559511 : Blo 370760 559511 := bstep (se 1 (by rfl) ⟨419633, by rfl⟩ : syracuseStep 559511 = 839267) B839267
theorem B559577 : Blo 370760 559577 := bstep (se 2 (by rfl) ⟨209841, by rfl⟩ : syracuseStep 559577 = 419683) B419683
theorem B559691 : Blo 370760 559691 := bstep (se 1 (by rfl) ⟨419768, by rfl⟩ : syracuseStep 559691 = 839537) B839537
theorem B559703 : Blo 370760 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B559769 : Blo 370760 559769 := bstep (se 2 (by rfl) ⟨209913, by rfl⟩ : syracuseStep 559769 = 419827) B419827
theorem B559883 : Blo 370760 559883 := bstep (se 1 (by rfl) ⟨419912, by rfl⟩ : syracuseStep 559883 = 839825) B839825
theorem B559895 : Blo 370760 559895 := bstep (se 1 (by rfl) ⟨419921, by rfl⟩ : syracuseStep 559895 = 839843) B839843
theorem B1280843 : Blo 370760 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B559961 : Blo 370760 559961 := bstep (se 2 (by rfl) ⟨209985, by rfl⟩ : syracuseStep 559961 = 419971) B419971
theorem B560075 : Blo 370760 560075 := bstep (se 1 (by rfl) ⟨420056, by rfl⟩ : syracuseStep 560075 = 840113) B840113
theorem B560087 : Blo 370760 560087 := bstep (se 1 (by rfl) ⟨420065, by rfl⟩ : syracuseStep 560087 = 840131) B840131
theorem B560153 : Blo 370760 560153 := bstep (se 2 (by rfl) ⟨210057, by rfl⟩ : syracuseStep 560153 = 420115) B420115
theorem B396343 : Blo 370760 396343 := bstep (se 1 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 396343 = 594515) B594515
theorem B560267 : Blo 370760 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B560279 : Blo 370760 560279 := bstep (se 1 (by rfl) ⟨420209, by rfl⟩ : syracuseStep 560279 = 840419) B840419
theorem B560345 : Blo 370760 560345 := bstep (se 2 (by rfl) ⟨210129, by rfl⟩ : syracuseStep 560345 = 420259) B420259
theorem B1019159 : Blo 370760 1019159 := bstep (se 1 (by rfl) ⟨764369, by rfl⟩ : syracuseStep 1019159 = 1528739) B1528739
theorem B560459 : Blo 370760 560459 := bstep (se 1 (by rfl) ⟨420344, by rfl⟩ : syracuseStep 560459 = 840689) B840689
theorem B560471 : Blo 370760 560471 := bstep (se 1 (by rfl) ⟨420353, by rfl⟩ : syracuseStep 560471 = 840707) B840707
theorem B560537 : Blo 370760 560537 := bstep (se 2 (by rfl) ⟨210201, by rfl⟩ : syracuseStep 560537 = 420403) B420403
theorem B626123 : Blo 370760 626123 := bstep (se 1 (by rfl) ⟨469592, by rfl⟩ : syracuseStep 626123 = 939185) B939185
theorem B5443033 : Blo 370760 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B560651 : Blo 370760 560651 := bstep (se 1 (by rfl) ⟨420488, by rfl⟩ : syracuseStep 560651 = 840977) B840977
theorem B560663 : Blo 370760 560663 := bstep (se 1 (by rfl) ⟨420497, by rfl⟩ : syracuseStep 560663 = 840995) B840995
theorem B2428481 : Blo 370760 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B626251 : Blo 370760 626251 := bstep (se 1 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 626251 = 939377) B939377
theorem B560729 : Blo 370760 560729 := bstep (se 2 (by rfl) ⟨210273, by rfl⟩ : syracuseStep 560729 = 420547) B420547
theorem B560843 : Blo 370760 560843 := bstep (se 1 (by rfl) ⟨420632, by rfl⟩ : syracuseStep 560843 = 841265) B841265
theorem B560855 : Blo 370760 560855 := bstep (se 1 (by rfl) ⟨420641, by rfl⟩ : syracuseStep 560855 = 841283) B841283
theorem B626393 : Blo 370760 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B560921 : Blo 370760 560921 := bstep (se 2 (by rfl) ⟨210345, by rfl⟩ : syracuseStep 560921 = 420691) B420691
theorem B1412909 : Blo 370760 1412909 := bstep (se 3 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 1412909 = 529841) B529841
theorem B626521 : Blo 370760 626521 := bstep (se 2 (by rfl) ⟨234945, by rfl⟩ : syracuseStep 626521 = 469891) B469891
theorem B397163 : Blo 370760 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B561035 : Blo 370760 561035 := bstep (se 1 (by rfl) ⟨420776, by rfl⟩ : syracuseStep 561035 = 841553) B841553
theorem B561047 : Blo 370760 561047 := bstep (se 1 (by rfl) ⟨420785, by rfl⟩ : syracuseStep 561047 = 841571) B841571
theorem B561113 : Blo 370760 561113 := bstep (se 2 (by rfl) ⟨210417, by rfl⟩ : syracuseStep 561113 = 420835) B420835
theorem B6230029 : Blo 370760 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2691089 : Blo 370760 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B561227 : Blo 370760 561227 := bstep (se 1 (by rfl) ⟨420920, by rfl⟩ : syracuseStep 561227 = 841841) B841841
theorem B561239 : Blo 370760 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B2134147 : Blo 370760 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B561305 : Blo 370760 561305 := bstep (se 2 (by rfl) ⟨210489, by rfl⟩ : syracuseStep 561305 = 420979) B420979
theorem B561419 : Blo 370760 561419 := bstep (se 1 (by rfl) ⟨421064, by rfl⟩ : syracuseStep 561419 = 842129) B842129
theorem B561431 : Blo 370760 561431 := bstep (se 1 (by rfl) ⟨421073, by rfl⟩ : syracuseStep 561431 = 842147) B842147
theorem B1642841 : Blo 370760 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B561497 : Blo 370760 561497 := bstep (se 2 (by rfl) ⟨210561, by rfl⟩ : syracuseStep 561497 = 421123) B421123
theorem B627095 : Blo 370760 627095 := bstep (se 1 (by rfl) ⟨470321, by rfl⟩ : syracuseStep 627095 = 940643) B940643
theorem B561611 : Blo 370760 561611 := bstep (se 1 (by rfl) ⟨421208, by rfl⟩ : syracuseStep 561611 = 842417) B842417
theorem B561623 : Blo 370760 561623 := bstep (se 1 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 561623 = 842435) B842435
theorem B627223 : Blo 370760 627223 := bstep (se 1 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 627223 = 940835) B940835
theorem B561689 : Blo 370760 561689 := bstep (se 2 (by rfl) ⟨210633, by rfl⟩ : syracuseStep 561689 = 421267) B421267
theorem B1413683 : Blo 370760 1413683 := bstep (se 1 (by rfl) ⟨1060262, by rfl⟩ : syracuseStep 1413683 = 2120525) B2120525
theorem B1512067 : Blo 370760 1512067 := bstep (se 1 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 1512067 = 2268101) B2268101
theorem B561803 : Blo 370760 561803 := bstep (se 1 (by rfl) ⟨421352, by rfl⟩ : syracuseStep 561803 = 842705) B842705
theorem B561815 : Blo 370760 561815 := bstep (se 1 (by rfl) ⟨421361, by rfl⟩ : syracuseStep 561815 = 842723) B842723
theorem B529049 : Blo 370760 529049 := bstep (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) B396787
theorem B561881 : Blo 370760 561881 := bstep (se 2 (by rfl) ⟨210705, by rfl⟩ : syracuseStep 561881 = 421411) B421411
theorem B561995 : Blo 370760 561995 := bstep (se 1 (by rfl) ⟨421496, by rfl⟩ : syracuseStep 561995 = 842993) B842993
theorem B562007 : Blo 370760 562007 := bstep (se 1 (by rfl) ⟨421505, by rfl⟩ : syracuseStep 562007 = 843011) B843011
theorem B562073 : Blo 370760 562073 := bstep (se 2 (by rfl) ⟨210777, by rfl⟩ : syracuseStep 562073 = 421555) B421555
theorem B2823173 : Blo 370760 2823173 := bstep (se 4 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 2823173 = 529345) B529345
theorem B398359 : Blo 370760 398359 := bstep (se 1 (by rfl) ⟨298769, by rfl⟩ : syracuseStep 398359 = 597539) B597539
theorem B857177 : Blo 370760 857177 := bstep (se 2 (by rfl) ⟨321441, by rfl⟩ : syracuseStep 857177 = 642883) B642883
theorem B627851 : Blo 370760 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B1348787 : Blo 370760 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B627979 : Blo 370760 627979 := bstep (se 1 (by rfl) ⟨470984, by rfl⟩ : syracuseStep 627979 = 941969) B941969
theorem B529687 : Blo 370760 529687 := bstep (se 1 (by rfl) ⟨397265, by rfl⟩ : syracuseStep 529687 = 794531) B794531
theorem B398615 : Blo 370760 398615 := bstep (se 1 (by rfl) ⟨298961, by rfl⟩ : syracuseStep 398615 = 597923) B597923
theorem B628121 : Blo 370760 628121 := bstep (se 2 (by rfl) ⟨235545, by rfl⟩ : syracuseStep 628121 = 471091) B471091
theorem B628249 : Blo 370760 628249 := bstep (se 2 (by rfl) ⟨235593, by rfl⟩ : syracuseStep 628249 = 471187) B471187
theorem B4298275 : Blo 370760 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B792139 : Blo 370760 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B12916421 : Blo 370760 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B399179 : Blo 370760 399179 := bstep (se 1 (by rfl) ⟨299384, by rfl⟩ : syracuseStep 399179 = 598769) B598769
theorem B2004887 : Blo 370760 2004887 := bstep (se 1 (by rfl) ⟨1503665, by rfl⟩ : syracuseStep 2004887 = 3007331) B3007331
theorem B530393 : Blo 370760 530393 := bstep (se 2 (by rfl) ⟨198897, by rfl⟩ : syracuseStep 530393 = 397795) B397795
theorem B1415171 : Blo 370760 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B5347397 : Blo 370760 5347397 := bstep (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) B1002637
theorem B530507 : Blo 370760 530507 := bstep (se 1 (by rfl) ⟨397880, by rfl⟩ : syracuseStep 530507 = 795761) B795761
theorem B628823 : Blo 370760 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B628951 : Blo 370760 628951 := bstep (se 1 (by rfl) ⟨471713, by rfl⟩ : syracuseStep 628951 = 943427) B943427
theorem B9083285 : Blo 370760 9083285 := bstep (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) B425779
theorem B792985 : Blo 370760 792985 := bstep (se 2 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 792985 = 594739) B594739
theorem B1415627 : Blo 370760 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B531031 : Blo 370760 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B1415825 : Blo 370760 1415825 := bstep (se 2 (by rfl) ⟨530934, by rfl⟩ : syracuseStep 1415825 = 1061869) B1061869
theorem B1252043 : Blo 370760 1252043 := bstep (se 1 (by rfl) ⟨939032, by rfl⟩ : syracuseStep 1252043 = 1878065) B1878065
theorem B629579 : Blo 370760 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B12098483 : Blo 370760 12098483 := bstep (se 1 (by rfl) ⟨9073862, by rfl⟩ : syracuseStep 12098483 = 18147725) B18147725
theorem B629707 : Blo 370760 629707 := bstep (se 1 (by rfl) ⟨472280, by rfl⟩ : syracuseStep 629707 = 944561) B944561
theorem B1252313 : Blo 370760 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B629849 : Blo 370760 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B3054685 : Blo 370760 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B629977 : Blo 370760 629977 := bstep (se 2 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 629977 = 472483) B472483
theorem B2825603 : Blo 370760 2825603 := bstep (se 1 (by rfl) ⟨2119202, by rfl⟩ : syracuseStep 2825603 = 4238405) B4238405
theorem B531851 : Blo 370760 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B1416599 : Blo 370760 1416599 := bstep (se 1 (by rfl) ⟨1062449, by rfl⟩ : syracuseStep 1416599 = 2124899) B2124899
theorem B1908289 : Blo 370760 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B1089089 : Blo 370760 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B1416797 : Blo 370760 1416797 := bstep (se 3 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 1416797 = 531299) B531299
theorem B1384067 : Blo 370760 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B1253015 : Blo 370760 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B794291 : Blo 370760 794291 := bstep (se 1 (by rfl) ⟨595718, by rfl⟩ : syracuseStep 794291 = 1191437) B1191437
theorem B958169 : Blo 370760 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B630551 : Blo 370760 630551 := bstep (se 1 (by rfl) ⟨472913, by rfl⟩ : syracuseStep 630551 = 945827) B945827
theorem B3383171 : Blo 370760 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B630679 : Blo 370760 630679 := bstep (se 1 (by rfl) ⟨473009, by rfl⟩ : syracuseStep 630679 = 946019) B946019
theorem B1253555 : Blo 370760 1253555 := bstep (se 1 (by rfl) ⟨940166, by rfl⟩ : syracuseStep 1253555 = 1880333) B1880333
theorem B1253825 : Blo 370760 1253825 := bstep (se 2 (by rfl) ⟨470184, by rfl⟩ : syracuseStep 1253825 = 940369) B940369
theorem B631307 : Blo 370760 631307 := bstep (se 1 (by rfl) ⟨473480, by rfl⟩ : syracuseStep 631307 = 946961) B946961
theorem B1057369 : Blo 370760 1057369 := bstep (se 2 (by rfl) ⟨396513, by rfl⟩ : syracuseStep 1057369 = 793027) B793027
theorem B3711581 : Blo 370760 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B631435 : Blo 370760 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B2859725 : Blo 370760 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B5088005 : Blo 370760 5088005 := bstep (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) B954001
theorem B631577 : Blo 370760 631577 := bstep (se 2 (by rfl) ⟨236841, by rfl⟩ : syracuseStep 631577 = 473683) B473683
theorem B598871 : Blo 370760 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B631705 : Blo 370760 631705 := bstep (se 2 (by rfl) ⟨236889, by rfl⟩ : syracuseStep 631705 = 473779) B473779
theorem B4301747 : Blo 370760 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B598999 : Blo 370760 598999 := bstep (se 1 (by rfl) ⟨449249, by rfl⟩ : syracuseStep 598999 = 898499) B898499
theorem B1254365 : Blo 370760 1254365 := bstep (se 3 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 1254365 = 470387) B470387
theorem B599051 : Blo 370760 599051 := bstep (se 1 (by rfl) ⟨449288, by rfl⟩ : syracuseStep 599051 = 898577) B898577
theorem B2270339 : Blo 370760 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B599179 : Blo 370760 599179 := bstep (se 1 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 599179 = 898769) B898769
theorem B1057985 : Blo 370760 1057985 := bstep (se 2 (by rfl) ⟨396744, by rfl⟩ : syracuseStep 1057985 = 793489) B793489
theorem B795863 : Blo 370760 795863 := bstep (se 1 (by rfl) ⟨596897, by rfl⟩ : syracuseStep 795863 = 1193795) B1193795
theorem B3188099 : Blo 370760 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B632279 : Blo 370760 632279 := bstep (se 1 (by rfl) ⟨474209, by rfl⟩ : syracuseStep 632279 = 948419) B948419
theorem B1418755 : Blo 370760 1418755 := bstep (se 1 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 1418755 = 2128133) B2128133
theorem B796171 : Blo 370760 796171 := bstep (se 1 (by rfl) ⟨597128, by rfl⟩ : syracuseStep 796171 = 1194257) B1194257
theorem B599563 : Blo 370760 599563 := bstep (se 1 (by rfl) ⟨449672, by rfl⟩ : syracuseStep 599563 = 899345) B899345
theorem B2729537 : Blo 370760 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B1877579 : Blo 370760 1877579 := bstep (se 1 (by rfl) ⟨1408184, by rfl⟩ : syracuseStep 1877579 = 2816369) B2816369
theorem B632407 : Blo 370760 632407 := bstep (se 1 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 632407 = 948611) B948611
theorem B599819 : Blo 370760 599819 := bstep (se 1 (by rfl) ⟨449864, by rfl⟩ : syracuseStep 599819 = 899729) B899729
theorem B1419059 : Blo 370760 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B1189721 : Blo 370760 1189721 := bstep (se 2 (by rfl) ⟨446145, by rfl⟩ : syracuseStep 1189721 = 892291) B892291
theorem B501655 : Blo 370760 501655 := bstep (se 1 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 501655 = 752483) B752483
theorem B1189849 : Blo 370760 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B370763 : Blo 370760 370763 := bstep (se 1 (by rfl) ⟨278072, by rfl⟩ : syracuseStep 370763 = 556145) B556145
theorem B1255499 : Blo 370760 1255499 := bstep (se 1 (by rfl) ⟨941624, by rfl⟩ : syracuseStep 1255499 = 1883249) B1883249
theorem B370775 : Blo 370760 370775 := bstep (se 1 (by rfl) ⟨278081, by rfl⟩ : syracuseStep 370775 = 556163) B556163
theorem B370795 : Blo 370760 370795 := bstep (se 1 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 370795 = 556193) B556193
theorem B370807 : Blo 370760 370807 := bstep (se 1 (by rfl) ⟨278105, by rfl⟩ : syracuseStep 370807 = 556211) B556211
theorem B370827 : Blo 370760 370827 := bstep (se 1 (by rfl) ⟨278120, by rfl⟩ : syracuseStep 370827 = 556241) B556241
theorem B370839 : Blo 370760 370839 := bstep (se 1 (by rfl) ⟨278129, by rfl⟩ : syracuseStep 370839 = 556259) B556259
theorem B370859 : Blo 370760 370859 := bstep (se 1 (by rfl) ⟨278144, by rfl⟩ : syracuseStep 370859 = 556289) B556289
theorem B370871 : Blo 370760 370871 := bstep (se 1 (by rfl) ⟨278153, by rfl⟩ : syracuseStep 370871 = 556307) B556307
theorem B370891 : Blo 370760 370891 := bstep (se 1 (by rfl) ⟨278168, by rfl⟩ : syracuseStep 370891 = 556337) B556337
theorem B370903 : Blo 370760 370903 := bstep (se 1 (by rfl) ⟨278177, by rfl⟩ : syracuseStep 370903 = 556355) B556355
theorem B1190105 : Blo 370760 1190105 := bstep (se 2 (by rfl) ⟨446289, by rfl⟩ : syracuseStep 1190105 = 892579) B892579
theorem B600281 : Blo 370760 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B370923 : Blo 370760 370923 := bstep (se 1 (by rfl) ⟨278192, by rfl⟩ : syracuseStep 370923 = 556385) B556385
theorem B370935 : Blo 370760 370935 := bstep (se 1 (by rfl) ⟨278201, by rfl⟩ : syracuseStep 370935 = 556403) B556403
theorem B370955 : Blo 370760 370955 := bstep (se 1 (by rfl) ⟨278216, by rfl⟩ : syracuseStep 370955 = 556433) B556433
theorem B370967 : Blo 370760 370967 := bstep (se 1 (by rfl) ⟨278225, by rfl⟩ : syracuseStep 370967 = 556451) B556451
theorem B370987 : Blo 370760 370987 := bstep (se 1 (by rfl) ⟨278240, by rfl⟩ : syracuseStep 370987 = 556481) B556481
theorem B370999 : Blo 370760 370999 := bstep (se 1 (by rfl) ⟨278249, by rfl⟩ : syracuseStep 370999 = 556499) B556499
theorem B371019 : Blo 370760 371019 := bstep (se 1 (by rfl) ⟨278264, by rfl⟩ : syracuseStep 371019 = 556529) B556529
theorem B371031 : Blo 370760 371031 := bstep (se 1 (by rfl) ⟨278273, by rfl⟩ : syracuseStep 371031 = 556547) B556547
theorem B1255769 : Blo 370760 1255769 := bstep (se 2 (by rfl) ⟨470913, by rfl⟩ : syracuseStep 1255769 = 941827) B941827
theorem B371051 : Blo 370760 371051 := bstep (se 1 (by rfl) ⟨278288, by rfl⟩ : syracuseStep 371051 = 556577) B556577
theorem B371063 : Blo 370760 371063 := bstep (se 1 (by rfl) ⟨278297, by rfl⟩ : syracuseStep 371063 = 556595) B556595
theorem B371083 : Blo 370760 371083 := bstep (se 1 (by rfl) ⟨278312, by rfl⟩ : syracuseStep 371083 = 556625) B556625
theorem B371095 : Blo 370760 371095 := bstep (se 1 (by rfl) ⟨278321, by rfl⟩ : syracuseStep 371095 = 556643) B556643
theorem B371115 : Blo 370760 371115 := bstep (se 1 (by rfl) ⟨278336, by rfl⟩ : syracuseStep 371115 = 556673) B556673
theorem B371127 : Blo 370760 371127 := bstep (se 1 (by rfl) ⟨278345, by rfl⟩ : syracuseStep 371127 = 556691) B556691
theorem B1419713 : Blo 370760 1419713 := bstep (se 2 (by rfl) ⟨532392, by rfl⟩ : syracuseStep 1419713 = 1064785) B1064785
theorem B371147 : Blo 370760 371147 := bstep (se 1 (by rfl) ⟨278360, by rfl⟩ : syracuseStep 371147 = 556721) B556721
theorem B371159 : Blo 370760 371159 := bstep (se 1 (by rfl) ⟨278369, by rfl⟩ : syracuseStep 371159 = 556739) B556739
theorem B371179 : Blo 370760 371179 := bstep (se 1 (by rfl) ⟨278384, by rfl⟩ : syracuseStep 371179 = 556769) B556769
theorem B371191 : Blo 370760 371191 := bstep (se 1 (by rfl) ⟨278393, by rfl⟩ : syracuseStep 371191 = 556787) B556787
theorem B371211 : Blo 370760 371211 := bstep (se 1 (by rfl) ⟨278408, by rfl⟩ : syracuseStep 371211 = 556817) B556817
theorem B371223 : Blo 370760 371223 := bstep (se 1 (by rfl) ⟨278417, by rfl⟩ : syracuseStep 371223 = 556835) B556835
theorem B371243 : Blo 370760 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B371255 : Blo 370760 371255 := bstep (se 1 (by rfl) ⟨278441, by rfl⟩ : syracuseStep 371255 = 556883) B556883
theorem B371275 : Blo 370760 371275 := bstep (se 1 (by rfl) ⟨278456, by rfl⟩ : syracuseStep 371275 = 556913) B556913
theorem B371287 : Blo 370760 371287 := bstep (se 1 (by rfl) ⟨278465, by rfl⟩ : syracuseStep 371287 = 556931) B556931
theorem B371307 : Blo 370760 371307 := bstep (se 1 (by rfl) ⟨278480, by rfl⟩ : syracuseStep 371307 = 556961) B556961
theorem B371319 : Blo 370760 371319 := bstep (se 1 (by rfl) ⟨278489, by rfl⟩ : syracuseStep 371319 = 556979) B556979
theorem B371339 : Blo 370760 371339 := bstep (se 1 (by rfl) ⟨278504, by rfl⟩ : syracuseStep 371339 = 557009) B557009
theorem B371351 : Blo 370760 371351 := bstep (se 1 (by rfl) ⟨278513, by rfl⟩ : syracuseStep 371351 = 557027) B557027
theorem B371371 : Blo 370760 371371 := bstep (se 1 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 371371 = 557057) B557057
theorem B371383 : Blo 370760 371383 := bstep (se 1 (by rfl) ⟨278537, by rfl⟩ : syracuseStep 371383 = 557075) B557075
theorem B371403 : Blo 370760 371403 := bstep (se 1 (by rfl) ⟨278552, by rfl⟩ : syracuseStep 371403 = 557105) B557105
theorem B2829005 : Blo 370760 2829005 := bstep (se 3 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 2829005 = 1060877) B1060877
theorem B371415 : Blo 370760 371415 := bstep (se 1 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 371415 = 557123) B557123
theorem B1583833 : Blo 370760 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B797401 : Blo 370760 797401 := bstep (se 2 (by rfl) ⟨299025, by rfl⟩ : syracuseStep 797401 = 598051) B598051
theorem B371435 : Blo 370760 371435 := bstep (se 1 (by rfl) ⟨278576, by rfl⟩ : syracuseStep 371435 = 557153) B557153
theorem B371447 : Blo 370760 371447 := bstep (se 1 (by rfl) ⟨278585, by rfl⟩ : syracuseStep 371447 = 557171) B557171
theorem B371467 : Blo 370760 371467 := bstep (se 1 (by rfl) ⟨278600, by rfl⟩ : syracuseStep 371467 = 557201) B557201
theorem B371479 : Blo 370760 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B371499 : Blo 370760 371499 := bstep (se 1 (by rfl) ⟨278624, by rfl⟩ : syracuseStep 371499 = 557249) B557249
theorem B371511 : Blo 370760 371511 := bstep (se 1 (by rfl) ⟨278633, by rfl⟩ : syracuseStep 371511 = 557267) B557267
theorem B371531 : Blo 370760 371531 := bstep (se 1 (by rfl) ⟨278648, by rfl⟩ : syracuseStep 371531 = 557297) B557297
theorem B371543 : Blo 370760 371543 := bstep (se 1 (by rfl) ⟨278657, by rfl⟩ : syracuseStep 371543 = 557315) B557315
theorem B371563 : Blo 370760 371563 := bstep (se 1 (by rfl) ⟨278672, by rfl⟩ : syracuseStep 371563 = 557345) B557345
theorem B371575 : Blo 370760 371575 := bstep (se 1 (by rfl) ⟨278681, by rfl⟩ : syracuseStep 371575 = 557363) B557363
theorem B371595 : Blo 370760 371595 := bstep (se 1 (by rfl) ⟨278696, by rfl⟩ : syracuseStep 371595 = 557393) B557393
theorem B371607 : Blo 370760 371607 := bstep (se 1 (by rfl) ⟨278705, by rfl⟩ : syracuseStep 371607 = 557411) B557411
theorem B371627 : Blo 370760 371627 := bstep (se 1 (by rfl) ⟨278720, by rfl⟩ : syracuseStep 371627 = 557441) B557441
theorem B3812275 : Blo 370760 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B371639 : Blo 370760 371639 := bstep (se 1 (by rfl) ⟨278729, by rfl⟩ : syracuseStep 371639 = 557459) B557459
theorem B371659 : Blo 370760 371659 := bstep (se 1 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 371659 = 557489) B557489
theorem B371671 : Blo 370760 371671 := bstep (se 1 (by rfl) ⟨278753, by rfl⟩ : syracuseStep 371671 = 557507) B557507
theorem B371691 : Blo 370760 371691 := bstep (se 1 (by rfl) ⟨278768, by rfl⟩ : syracuseStep 371691 = 557537) B557537
theorem B371703 : Blo 370760 371703 := bstep (se 1 (by rfl) ⟨278777, by rfl⟩ : syracuseStep 371703 = 557555) B557555
theorem B371723 : Blo 370760 371723 := bstep (se 1 (by rfl) ⟨278792, by rfl⟩ : syracuseStep 371723 = 557585) B557585
theorem B371735 : Blo 370760 371735 := bstep (se 1 (by rfl) ⟨278801, by rfl⟩ : syracuseStep 371735 = 557603) B557603
theorem B1256471 : Blo 370760 1256471 := bstep (se 1 (by rfl) ⟨942353, by rfl⟩ : syracuseStep 1256471 = 1884707) B1884707
theorem B371755 : Blo 370760 371755 := bstep (se 1 (by rfl) ⟨278816, by rfl⟩ : syracuseStep 371755 = 557633) B557633
theorem B371767 : Blo 370760 371767 := bstep (se 1 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 371767 = 557651) B557651
theorem B371787 : Blo 370760 371787 := bstep (se 1 (by rfl) ⟨278840, by rfl⟩ : syracuseStep 371787 = 557681) B557681
theorem B371799 : Blo 370760 371799 := bstep (se 1 (by rfl) ⟨278849, by rfl⟩ : syracuseStep 371799 = 557699) B557699
theorem B371819 : Blo 370760 371819 := bstep (se 1 (by rfl) ⟨278864, by rfl⟩ : syracuseStep 371819 = 557729) B557729
theorem B371831 : Blo 370760 371831 := bstep (se 1 (by rfl) ⟨278873, by rfl⟩ : syracuseStep 371831 = 557747) B557747
theorem B535691 : Blo 370760 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B371851 : Blo 370760 371851 := bstep (se 1 (by rfl) ⟨278888, by rfl⟩ : syracuseStep 371851 = 557777) B557777
theorem B371863 : Blo 370760 371863 := bstep (se 1 (by rfl) ⟨278897, by rfl⟩ : syracuseStep 371863 = 557795) B557795
theorem B371883 : Blo 370760 371883 := bstep (se 1 (by rfl) ⟨278912, by rfl⟩ : syracuseStep 371883 = 557825) B557825
theorem B2829491 : Blo 370760 2829491 := bstep (se 1 (by rfl) ⟨2122118, by rfl⟩ : syracuseStep 2829491 = 4244237) B4244237
theorem B371895 : Blo 370760 371895 := bstep (se 1 (by rfl) ⟨278921, by rfl⟩ : syracuseStep 371895 = 557843) B557843
theorem B371915 : Blo 370760 371915 := bstep (se 1 (by rfl) ⟨278936, by rfl⟩ : syracuseStep 371915 = 557873) B557873
theorem B371927 : Blo 370760 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B1060057 : Blo 370760 1060057 := bstep (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) B795043
theorem B371947 : Blo 370760 371947 := bstep (se 1 (by rfl) ⟨278960, by rfl⟩ : syracuseStep 371947 = 557921) B557921
theorem B371959 : Blo 370760 371959 := bstep (se 1 (by rfl) ⟨278969, by rfl⟩ : syracuseStep 371959 = 557939) B557939
theorem B371979 : Blo 370760 371979 := bstep (se 1 (by rfl) ⟨278984, by rfl⟩ : syracuseStep 371979 = 557969) B557969
theorem B371991 : Blo 370760 371991 := bstep (se 1 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 371991 = 557987) B557987
theorem B372011 : Blo 370760 372011 := bstep (se 1 (by rfl) ⟨279008, by rfl⟩ : syracuseStep 372011 = 558017) B558017
theorem B372023 : Blo 370760 372023 := bstep (se 1 (by rfl) ⟨279017, by rfl⟩ : syracuseStep 372023 = 558035) B558035
theorem B1879361 : Blo 370760 1879361 := bstep (se 2 (by rfl) ⟨704760, by rfl⟩ : syracuseStep 1879361 = 1409521) B1409521
theorem B372043 : Blo 370760 372043 := bstep (se 1 (by rfl) ⟨279032, by rfl⟩ : syracuseStep 372043 = 558065) B558065
theorem B372055 : Blo 370760 372055 := bstep (se 1 (by rfl) ⟨279041, by rfl⟩ : syracuseStep 372055 = 558083) B558083
theorem B372075 : Blo 370760 372075 := bstep (se 1 (by rfl) ⟨279056, by rfl⟩ : syracuseStep 372075 = 558113) B558113
theorem B372087 : Blo 370760 372087 := bstep (se 1 (by rfl) ⟨279065, by rfl⟩ : syracuseStep 372087 = 558131) B558131
theorem B372107 : Blo 370760 372107 := bstep (se 1 (by rfl) ⟨279080, by rfl⟩ : syracuseStep 372107 = 558161) B558161
theorem B372119 : Blo 370760 372119 := bstep (se 1 (by rfl) ⟨279089, by rfl⟩ : syracuseStep 372119 = 558179) B558179
theorem B372139 : Blo 370760 372139 := bstep (se 1 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 372139 = 558209) B558209
theorem B372151 : Blo 370760 372151 := bstep (se 1 (by rfl) ⟨279113, by rfl⟩ : syracuseStep 372151 = 558227) B558227
theorem B1191361 : Blo 370760 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B372171 : Blo 370760 372171 := bstep (se 1 (by rfl) ⟨279128, by rfl⟩ : syracuseStep 372171 = 558257) B558257
theorem B372183 : Blo 370760 372183 := bstep (se 1 (by rfl) ⟨279137, by rfl⟩ : syracuseStep 372183 = 558275) B558275
theorem B372203 : Blo 370760 372203 := bstep (se 1 (by rfl) ⟨279152, by rfl⟩ : syracuseStep 372203 = 558305) B558305
theorem B372215 : Blo 370760 372215 := bstep (se 1 (by rfl) ⟨279161, by rfl⟩ : syracuseStep 372215 = 558323) B558323
theorem B470539 : Blo 370760 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B372235 : Blo 370760 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B372247 : Blo 370760 372247 := bstep (se 1 (by rfl) ⟨279185, by rfl⟩ : syracuseStep 372247 = 558371) B558371
theorem B372267 : Blo 370760 372267 := bstep (se 1 (by rfl) ⟨279200, by rfl⟩ : syracuseStep 372267 = 558401) B558401
theorem B1257011 : Blo 370760 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B372279 : Blo 370760 372279 := bstep (se 1 (by rfl) ⟨279209, by rfl⟩ : syracuseStep 372279 = 558419) B558419
theorem B372299 : Blo 370760 372299 := bstep (se 1 (by rfl) ⟨279224, by rfl⟩ : syracuseStep 372299 = 558449) B558449
theorem B372311 : Blo 370760 372311 := bstep (se 1 (by rfl) ⟨279233, by rfl⟩ : syracuseStep 372311 = 558467) B558467
theorem B1060445 : Blo 370760 1060445 := bstep (se 3 (by rfl) ⟨198833, by rfl⟩ : syracuseStep 1060445 = 397667) B397667
theorem B372331 : Blo 370760 372331 := bstep (se 1 (by rfl) ⟨279248, by rfl⟩ : syracuseStep 372331 = 558497) B558497
theorem B372343 : Blo 370760 372343 := bstep (se 1 (by rfl) ⟨279257, by rfl⟩ : syracuseStep 372343 = 558515) B558515
theorem B372363 : Blo 370760 372363 := bstep (se 1 (by rfl) ⟨279272, by rfl⟩ : syracuseStep 372363 = 558545) B558545
theorem B1584791 : Blo 370760 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B372375 : Blo 370760 372375 := bstep (se 1 (by rfl) ⟨279281, by rfl⟩ : syracuseStep 372375 = 558563) B558563
theorem B372395 : Blo 370760 372395 := bstep (se 1 (by rfl) ⟨279296, by rfl⟩ : syracuseStep 372395 = 558593) B558593
theorem B1420973 : Blo 370760 1420973 := bstep (se 3 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 1420973 = 532865) B532865
theorem B372407 : Blo 370760 372407 := bstep (se 1 (by rfl) ⟨279305, by rfl⟩ : syracuseStep 372407 = 558611) B558611
theorem B372427 : Blo 370760 372427 := bstep (se 1 (by rfl) ⟨279320, by rfl⟩ : syracuseStep 372427 = 558641) B558641
theorem B1421003 : Blo 370760 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B372439 : Blo 370760 372439 := bstep (se 1 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 372439 = 558659) B558659
theorem B372459 : Blo 370760 372459 := bstep (se 1 (by rfl) ⟨279344, by rfl⟩ : syracuseStep 372459 = 558689) B558689
theorem B372471 : Blo 370760 372471 := bstep (se 1 (by rfl) ⟨279353, by rfl⟩ : syracuseStep 372471 = 558707) B558707
theorem B372491 : Blo 370760 372491 := bstep (se 1 (by rfl) ⟨279368, by rfl⟩ : syracuseStep 372491 = 558737) B558737
theorem B372503 : Blo 370760 372503 := bstep (se 1 (by rfl) ⟨279377, by rfl⟩ : syracuseStep 372503 = 558755) B558755
theorem B372523 : Blo 370760 372523 := bstep (se 1 (by rfl) ⟨279392, by rfl⟩ : syracuseStep 372523 = 558785) B558785
theorem B372535 : Blo 370760 372535 := bstep (se 1 (by rfl) ⟨279401, by rfl⟩ : syracuseStep 372535 = 558803) B558803
theorem B1257281 : Blo 370760 1257281 := bstep (se 2 (by rfl) ⟨471480, by rfl⟩ : syracuseStep 1257281 = 942961) B942961
theorem B372555 : Blo 370760 372555 := bstep (se 1 (by rfl) ⟨279416, by rfl⟩ : syracuseStep 372555 = 558833) B558833
theorem B372567 : Blo 370760 372567 := bstep (se 1 (by rfl) ⟨279425, by rfl⟩ : syracuseStep 372567 = 558851) B558851
theorem B372587 : Blo 370760 372587 := bstep (se 1 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 372587 = 558881) B558881
theorem B372599 : Blo 370760 372599 := bstep (se 1 (by rfl) ⟨279449, by rfl⟩ : syracuseStep 372599 = 558899) B558899
theorem B372619 : Blo 370760 372619 := bstep (se 1 (by rfl) ⟨279464, by rfl⟩ : syracuseStep 372619 = 558929) B558929
theorem B372631 : Blo 370760 372631 := bstep (se 1 (by rfl) ⟨279473, by rfl⟩ : syracuseStep 372631 = 558947) B558947
theorem B372651 : Blo 370760 372651 := bstep (se 1 (by rfl) ⟨279488, by rfl⟩ : syracuseStep 372651 = 558977) B558977
theorem B372663 : Blo 370760 372663 := bstep (se 1 (by rfl) ⟨279497, by rfl⟩ : syracuseStep 372663 = 558995) B558995
theorem B372683 : Blo 370760 372683 := bstep (se 1 (by rfl) ⟨279512, by rfl⟩ : syracuseStep 372683 = 559025) B559025
theorem B372695 : Blo 370760 372695 := bstep (se 1 (by rfl) ⟨279521, by rfl⟩ : syracuseStep 372695 = 559043) B559043
theorem B372715 : Blo 370760 372715 := bstep (se 1 (by rfl) ⟨279536, by rfl⟩ : syracuseStep 372715 = 559073) B559073
theorem B372727 : Blo 370760 372727 := bstep (se 1 (by rfl) ⟨279545, by rfl⟩ : syracuseStep 372727 = 559091) B559091
theorem B372747 : Blo 370760 372747 := bstep (se 1 (by rfl) ⟨279560, by rfl⟩ : syracuseStep 372747 = 559121) B559121
theorem B372759 : Blo 370760 372759 := bstep (se 1 (by rfl) ⟨279569, by rfl⟩ : syracuseStep 372759 = 559139) B559139
theorem B372779 : Blo 370760 372779 := bstep (se 1 (by rfl) ⟨279584, by rfl⟩ : syracuseStep 372779 = 559169) B559169
theorem B372791 : Blo 370760 372791 := bstep (se 1 (by rfl) ⟨279593, by rfl⟩ : syracuseStep 372791 = 559187) B559187
theorem B372811 : Blo 370760 372811 := bstep (se 1 (by rfl) ⟨279608, by rfl⟩ : syracuseStep 372811 = 559217) B559217
theorem B372823 : Blo 370760 372823 := bstep (se 1 (by rfl) ⟨279617, by rfl⟩ : syracuseStep 372823 = 559235) B559235
theorem B372843 : Blo 370760 372843 := bstep (se 1 (by rfl) ⟨279632, by rfl⟩ : syracuseStep 372843 = 559265) B559265
theorem B372855 : Blo 370760 372855 := bstep (se 1 (by rfl) ⟨279641, by rfl⟩ : syracuseStep 372855 = 559283) B559283
theorem B372875 : Blo 370760 372875 := bstep (se 1 (by rfl) ⟨279656, by rfl⟩ : syracuseStep 372875 = 559313) B559313
theorem B372887 : Blo 370760 372887 := bstep (se 1 (by rfl) ⟨279665, by rfl⟩ : syracuseStep 372887 = 559331) B559331
theorem B372907 : Blo 370760 372907 := bstep (se 1 (by rfl) ⟨279680, by rfl⟩ : syracuseStep 372907 = 559361) B559361
theorem B372919 : Blo 370760 372919 := bstep (se 1 (by rfl) ⟨279689, by rfl⟩ : syracuseStep 372919 = 559379) B559379
theorem B372939 : Blo 370760 372939 := bstep (se 1 (by rfl) ⟨279704, by rfl⟩ : syracuseStep 372939 = 559409) B559409
theorem B372951 : Blo 370760 372951 := bstep (se 1 (by rfl) ⟨279713, by rfl⟩ : syracuseStep 372951 = 559427) B559427
theorem B372971 : Blo 370760 372971 := bstep (se 1 (by rfl) ⟨279728, by rfl⟩ : syracuseStep 372971 = 559457) B559457
theorem B372983 : Blo 370760 372983 := bstep (se 1 (by rfl) ⟨279737, by rfl⟩ : syracuseStep 372983 = 559475) B559475
theorem B373003 : Blo 370760 373003 := bstep (se 1 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 373003 = 559505) B559505
theorem B373015 : Blo 370760 373015 := bstep (se 1 (by rfl) ⟨279761, by rfl⟩ : syracuseStep 373015 = 559523) B559523
theorem B3191075 : Blo 370760 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B373035 : Blo 370760 373035 := bstep (se 1 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 373035 = 559553) B559553
theorem B373047 : Blo 370760 373047 := bstep (se 1 (by rfl) ⟨279785, by rfl⟩ : syracuseStep 373047 = 559571) B559571
theorem B373067 : Blo 370760 373067 := bstep (se 1 (by rfl) ⟨279800, by rfl⟩ : syracuseStep 373067 = 559601) B559601
theorem B373079 : Blo 370760 373079 := bstep (se 1 (by rfl) ⟨279809, by rfl⟩ : syracuseStep 373079 = 559619) B559619
theorem B1421657 : Blo 370760 1421657 := bstep (se 2 (by rfl) ⟨533121, by rfl⟩ : syracuseStep 1421657 = 1066243) B1066243
theorem B1257821 : Blo 370760 1257821 := bstep (se 3 (by rfl) ⟨235841, by rfl⟩ : syracuseStep 1257821 = 471683) B471683
theorem B373099 : Blo 370760 373099 := bstep (se 1 (by rfl) ⟨279824, by rfl⟩ : syracuseStep 373099 = 559649) B559649
theorem B373111 : Blo 370760 373111 := bstep (se 1 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 373111 = 559667) B559667
theorem B373131 : Blo 370760 373131 := bstep (se 1 (by rfl) ⟨279848, by rfl⟩ : syracuseStep 373131 = 559697) B559697
theorem B373143 : Blo 370760 373143 := bstep (se 1 (by rfl) ⟨279857, by rfl⟩ : syracuseStep 373143 = 559715) B559715
theorem B373163 : Blo 370760 373163 := bstep (se 1 (by rfl) ⟨279872, by rfl⟩ : syracuseStep 373163 = 559745) B559745
theorem B373175 : Blo 370760 373175 := bstep (se 1 (by rfl) ⟨279881, by rfl⟩ : syracuseStep 373175 = 559763) B559763
theorem B373195 : Blo 370760 373195 := bstep (se 1 (by rfl) ⟨279896, by rfl⟩ : syracuseStep 373195 = 559793) B559793
theorem B471511 : Blo 370760 471511 := bstep (se 1 (by rfl) ⟨353633, by rfl⟩ : syracuseStep 471511 = 707267) B707267
theorem B373207 : Blo 370760 373207 := bstep (se 1 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 373207 = 559811) B559811
theorem B373227 : Blo 370760 373227 := bstep (se 1 (by rfl) ⟨279920, by rfl⟩ : syracuseStep 373227 = 559841) B559841
theorem B373239 : Blo 370760 373239 := bstep (se 1 (by rfl) ⟨279929, by rfl⟩ : syracuseStep 373239 = 559859) B559859
theorem B373259 : Blo 370760 373259 := bstep (se 1 (by rfl) ⟨279944, by rfl⟩ : syracuseStep 373259 = 559889) B559889
theorem B22196753 : Blo 370760 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B373271 : Blo 370760 373271 := bstep (se 1 (by rfl) ⟨279953, by rfl⟩ : syracuseStep 373271 = 559907) B559907
theorem B373291 : Blo 370760 373291 := bstep (se 1 (by rfl) ⟨279968, by rfl⟩ : syracuseStep 373291 = 559937) B559937
theorem B373303 : Blo 370760 373303 := bstep (se 1 (by rfl) ⟨279977, by rfl⟩ : syracuseStep 373303 = 559955) B559955
theorem B373323 : Blo 370760 373323 := bstep (se 1 (by rfl) ⟨279992, by rfl⟩ : syracuseStep 373323 = 559985) B559985
theorem B373335 : Blo 370760 373335 := bstep (se 1 (by rfl) ⟨280001, by rfl⟩ : syracuseStep 373335 = 560003) B560003
theorem B2830949 : Blo 370760 2830949 := bstep (se 4 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 2830949 = 530803) B530803
theorem B373355 : Blo 370760 373355 := bstep (se 1 (by rfl) ⟨280016, by rfl⟩ : syracuseStep 373355 = 560033) B560033
theorem B373367 : Blo 370760 373367 := bstep (se 1 (by rfl) ⟨280025, by rfl⟩ : syracuseStep 373367 = 560051) B560051
theorem B373387 : Blo 370760 373387 := bstep (se 1 (by rfl) ⟨280040, by rfl⟩ : syracuseStep 373387 = 560081) B560081
theorem B373399 : Blo 370760 373399 := bstep (se 1 (by rfl) ⟨280049, by rfl⟩ : syracuseStep 373399 = 560099) B560099
theorem B1421975 : Blo 370760 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B373419 : Blo 370760 373419 := bstep (se 1 (by rfl) ⟨280064, by rfl⟩ : syracuseStep 373419 = 560129) B560129
theorem B373431 : Blo 370760 373431 := bstep (se 1 (by rfl) ⟨280073, by rfl⟩ : syracuseStep 373431 = 560147) B560147
theorem B373451 : Blo 370760 373451 := bstep (se 1 (by rfl) ⟨280088, by rfl⟩ : syracuseStep 373451 = 560177) B560177
theorem B373463 : Blo 370760 373463 := bstep (se 1 (by rfl) ⟨280097, by rfl⟩ : syracuseStep 373463 = 560195) B560195
theorem B373483 : Blo 370760 373483 := bstep (se 1 (by rfl) ⟨280112, by rfl⟩ : syracuseStep 373483 = 560225) B560225
theorem B373495 : Blo 370760 373495 := bstep (se 1 (by rfl) ⟨280121, by rfl⟩ : syracuseStep 373495 = 560243) B560243
theorem B373515 : Blo 370760 373515 := bstep (se 1 (by rfl) ⟨280136, by rfl⟩ : syracuseStep 373515 = 560273) B560273
theorem B373527 : Blo 370760 373527 := bstep (se 1 (by rfl) ⟨280145, by rfl⟩ : syracuseStep 373527 = 560291) B560291
theorem B373547 : Blo 370760 373547 := bstep (se 1 (by rfl) ⟨280160, by rfl⟩ : syracuseStep 373547 = 560321) B560321
theorem B373559 : Blo 370760 373559 := bstep (se 1 (by rfl) ⟨280169, by rfl⟩ : syracuseStep 373559 = 560339) B560339
theorem B373579 : Blo 370760 373579 := bstep (se 1 (by rfl) ⟨280184, by rfl⟩ : syracuseStep 373579 = 560369) B560369
theorem B373591 : Blo 370760 373591 := bstep (se 1 (by rfl) ⟨280193, by rfl⟩ : syracuseStep 373591 = 560387) B560387
theorem B373611 : Blo 370760 373611 := bstep (se 1 (by rfl) ⟨280208, by rfl⟩ : syracuseStep 373611 = 560417) B560417
theorem B373623 : Blo 370760 373623 := bstep (se 1 (by rfl) ⟨280217, by rfl⟩ : syracuseStep 373623 = 560435) B560435
theorem B373643 : Blo 370760 373643 := bstep (se 1 (by rfl) ⟨280232, by rfl⟩ : syracuseStep 373643 = 560465) B560465
theorem B373655 : Blo 370760 373655 := bstep (se 1 (by rfl) ⟨280241, by rfl⟩ : syracuseStep 373655 = 560483) B560483
theorem B668569 : Blo 370760 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B373675 : Blo 370760 373675 := bstep (se 1 (by rfl) ⟨280256, by rfl⟩ : syracuseStep 373675 = 560513) B560513
theorem B373687 : Blo 370760 373687 := bstep (se 1 (by rfl) ⟨280265, by rfl⟩ : syracuseStep 373687 = 560531) B560531
theorem B373707 : Blo 370760 373707 := bstep (se 1 (by rfl) ⟨280280, by rfl⟩ : syracuseStep 373707 = 560561) B560561
theorem B373719 : Blo 370760 373719 := bstep (se 1 (by rfl) ⟨280289, by rfl⟩ : syracuseStep 373719 = 560579) B560579
theorem B373739 : Blo 370760 373739 := bstep (se 1 (by rfl) ⟨280304, by rfl⟩ : syracuseStep 373739 = 560609) B560609
theorem B373751 : Blo 370760 373751 := bstep (se 1 (by rfl) ⟨280313, by rfl⟩ : syracuseStep 373751 = 560627) B560627
theorem B373771 : Blo 370760 373771 := bstep (se 1 (by rfl) ⟨280328, by rfl⟩ : syracuseStep 373771 = 560657) B560657
theorem B373783 : Blo 370760 373783 := bstep (se 1 (by rfl) ⟨280337, by rfl⟩ : syracuseStep 373783 = 560675) B560675
theorem B537625 : Blo 370760 537625 := bstep (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) B403219
theorem B373803 : Blo 370760 373803 := bstep (se 1 (by rfl) ⟨280352, by rfl⟩ : syracuseStep 373803 = 560705) B560705
theorem B373815 : Blo 370760 373815 := bstep (se 1 (by rfl) ⟨280361, by rfl⟩ : syracuseStep 373815 = 560723) B560723
theorem B2831435 : Blo 370760 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B373835 : Blo 370760 373835 := bstep (se 1 (by rfl) ⟨280376, by rfl⟩ : syracuseStep 373835 = 560753) B560753
theorem B373847 : Blo 370760 373847 := bstep (se 1 (by rfl) ⟨280385, by rfl⟩ : syracuseStep 373847 = 560771) B560771
theorem B373867 : Blo 370760 373867 := bstep (se 1 (by rfl) ⟨280400, by rfl⟩ : syracuseStep 373867 = 560801) B560801
theorem B373879 : Blo 370760 373879 := bstep (se 1 (by rfl) ⟨280409, by rfl⟩ : syracuseStep 373879 = 560819) B560819
theorem B373899 : Blo 370760 373899 := bstep (se 1 (by rfl) ⟨280424, by rfl⟩ : syracuseStep 373899 = 560849) B560849
theorem B373911 : Blo 370760 373911 := bstep (se 1 (by rfl) ⟨280433, by rfl⟩ : syracuseStep 373911 = 560867) B560867
theorem B373931 : Blo 370760 373931 := bstep (se 1 (by rfl) ⟨280448, by rfl⟩ : syracuseStep 373931 = 560897) B560897
theorem B373943 : Blo 370760 373943 := bstep (se 1 (by rfl) ⟨280457, by rfl⟩ : syracuseStep 373943 = 560915) B560915
theorem B373963 : Blo 370760 373963 := bstep (se 1 (by rfl) ⟨280472, by rfl⟩ : syracuseStep 373963 = 560945) B560945
theorem B373975 : Blo 370760 373975 := bstep (se 1 (by rfl) ⟨280481, by rfl⟩ : syracuseStep 373975 = 560963) B560963
theorem B1881305 : Blo 370760 1881305 := bstep (se 2 (by rfl) ⟨705489, by rfl⟩ : syracuseStep 1881305 = 1410979) B1410979
theorem B373995 : Blo 370760 373995 := bstep (se 1 (by rfl) ⟨280496, by rfl⟩ : syracuseStep 373995 = 560993) B560993
theorem B374007 : Blo 370760 374007 := bstep (se 1 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 374007 = 561011) B561011
theorem B472331 : Blo 370760 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B374027 : Blo 370760 374027 := bstep (se 1 (by rfl) ⟨280520, by rfl⟩ : syracuseStep 374027 = 561041) B561041
theorem B374039 : Blo 370760 374039 := bstep (se 1 (by rfl) ⟨280529, by rfl⟩ : syracuseStep 374039 = 561059) B561059
theorem B374059 : Blo 370760 374059 := bstep (se 1 (by rfl) ⟨280544, by rfl⟩ : syracuseStep 374059 = 561089) B561089
theorem B1422643 : Blo 370760 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B374071 : Blo 370760 374071 := bstep (se 1 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 374071 = 561107) B561107
theorem B374091 : Blo 370760 374091 := bstep (se 1 (by rfl) ⟨280568, by rfl⟩ : syracuseStep 374091 = 561137) B561137
theorem B374103 : Blo 370760 374103 := bstep (se 1 (by rfl) ⟨280577, by rfl⟩ : syracuseStep 374103 = 561155) B561155
theorem B374123 : Blo 370760 374123 := bstep (se 1 (by rfl) ⟨280592, by rfl⟩ : syracuseStep 374123 = 561185) B561185
theorem B374135 : Blo 370760 374135 := bstep (se 1 (by rfl) ⟨280601, by rfl⟩ : syracuseStep 374135 = 561203) B561203
theorem B374155 : Blo 370760 374155 := bstep (se 1 (by rfl) ⟨280616, by rfl⟩ : syracuseStep 374155 = 561233) B561233
theorem B374167 : Blo 370760 374167 := bstep (se 1 (by rfl) ⟨280625, by rfl⟩ : syracuseStep 374167 = 561251) B561251
theorem B374187 : Blo 370760 374187 := bstep (se 1 (by rfl) ⟨280640, by rfl⟩ : syracuseStep 374187 = 561281) B561281
theorem B374199 : Blo 370760 374199 := bstep (se 1 (by rfl) ⟨280649, by rfl⟩ : syracuseStep 374199 = 561299) B561299
theorem B1258955 : Blo 370760 1258955 := bstep (se 1 (by rfl) ⟨944216, by rfl⟩ : syracuseStep 1258955 = 1888433) B1888433
theorem B374219 : Blo 370760 374219 := bstep (se 1 (by rfl) ⟨280664, by rfl⟩ : syracuseStep 374219 = 561329) B561329
theorem B374231 : Blo 370760 374231 := bstep (se 1 (by rfl) ⟨280673, by rfl⟩ : syracuseStep 374231 = 561347) B561347
theorem B374251 : Blo 370760 374251 := bstep (se 1 (by rfl) ⟨280688, by rfl⟩ : syracuseStep 374251 = 561377) B561377
theorem B374263 : Blo 370760 374263 := bstep (se 1 (by rfl) ⟨280697, by rfl⟩ : syracuseStep 374263 = 561395) B561395
theorem B374283 : Blo 370760 374283 := bstep (se 1 (by rfl) ⟨280712, by rfl⟩ : syracuseStep 374283 = 561425) B561425
theorem B636439 : Blo 370760 636439 := bstep (se 1 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 636439 = 954659) B954659
theorem B374295 : Blo 370760 374295 := bstep (se 1 (by rfl) ⟨280721, by rfl⟩ : syracuseStep 374295 = 561443) B561443
theorem B374315 : Blo 370760 374315 := bstep (se 1 (by rfl) ⟨280736, by rfl⟩ : syracuseStep 374315 = 561473) B561473
theorem B374327 : Blo 370760 374327 := bstep (se 1 (by rfl) ⟨280745, by rfl⟩ : syracuseStep 374327 = 561491) B561491
theorem B374347 : Blo 370760 374347 := bstep (se 1 (by rfl) ⟨280760, by rfl⟩ : syracuseStep 374347 = 561521) B561521
theorem B374359 : Blo 370760 374359 := bstep (se 1 (by rfl) ⟨280769, by rfl⟩ : syracuseStep 374359 = 561539) B561539
theorem B374379 : Blo 370760 374379 := bstep (se 1 (by rfl) ⟨280784, by rfl⟩ : syracuseStep 374379 = 561569) B561569
theorem B374391 : Blo 370760 374391 := bstep (se 1 (by rfl) ⟨280793, by rfl⟩ : syracuseStep 374391 = 561587) B561587
theorem B11417219 : Blo 370760 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B374411 : Blo 370760 374411 := bstep (se 1 (by rfl) ⟨280808, by rfl⟩ : syracuseStep 374411 = 561617) B561617
theorem B374423 : Blo 370760 374423 := bstep (se 1 (by rfl) ⟨280817, by rfl⟩ : syracuseStep 374423 = 561635) B561635
theorem B374443 : Blo 370760 374443 := bstep (se 1 (by rfl) ⟨280832, by rfl⟩ : syracuseStep 374443 = 561665) B561665
theorem B374455 : Blo 370760 374455 := bstep (se 1 (by rfl) ⟨280841, by rfl⟩ : syracuseStep 374455 = 561683) B561683
theorem B636619 : Blo 370760 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B374475 : Blo 370760 374475 := bstep (se 1 (by rfl) ⟨280856, by rfl⟩ : syracuseStep 374475 = 561713) B561713
theorem B374487 : Blo 370760 374487 := bstep (se 1 (by rfl) ⟨280865, by rfl⟩ : syracuseStep 374487 = 561731) B561731
theorem B1259225 : Blo 370760 1259225 := bstep (se 2 (by rfl) ⟨472209, by rfl⟩ : syracuseStep 1259225 = 944419) B944419
theorem B374507 : Blo 370760 374507 := bstep (se 1 (by rfl) ⟨280880, by rfl⟩ : syracuseStep 374507 = 561761) B561761
theorem B669427 : Blo 370760 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B374519 : Blo 370760 374519 := bstep (se 1 (by rfl) ⟨280889, by rfl⟩ : syracuseStep 374519 = 561779) B561779
theorem B374539 : Blo 370760 374539 := bstep (se 1 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 374539 = 561809) B561809
theorem B374551 : Blo 370760 374551 := bstep (se 1 (by rfl) ⟨280913, by rfl⟩ : syracuseStep 374551 = 561827) B561827
theorem B374571 : Blo 370760 374571 := bstep (se 1 (by rfl) ⟨280928, by rfl⟩ : syracuseStep 374571 = 561857) B561857
theorem B374583 : Blo 370760 374583 := bstep (se 1 (by rfl) ⟨280937, by rfl⟩ : syracuseStep 374583 = 561875) B561875
theorem B374603 : Blo 370760 374603 := bstep (se 1 (by rfl) ⟨280952, by rfl⟩ : syracuseStep 374603 = 561905) B561905
theorem B374615 : Blo 370760 374615 := bstep (se 1 (by rfl) ⟨280961, by rfl⟩ : syracuseStep 374615 = 561923) B561923
theorem B374635 : Blo 370760 374635 := bstep (se 1 (by rfl) ⟨280976, by rfl⟩ : syracuseStep 374635 = 561953) B561953
theorem B374647 : Blo 370760 374647 := bstep (se 1 (by rfl) ⟨280985, by rfl⟩ : syracuseStep 374647 = 561971) B561971
theorem B374667 : Blo 370760 374667 := bstep (se 1 (by rfl) ⟨281000, by rfl⟩ : syracuseStep 374667 = 562001) B562001
theorem B604055 : Blo 370760 604055 := bstep (se 1 (by rfl) ⟨453041, by rfl⟩ : syracuseStep 604055 = 906083) B906083
theorem B374679 : Blo 370760 374679 := bstep (se 1 (by rfl) ⟨281009, by rfl⟩ : syracuseStep 374679 = 562019) B562019
theorem B374699 : Blo 370760 374699 := bstep (se 1 (by rfl) ⟨281024, by rfl⟩ : syracuseStep 374699 = 562049) B562049
theorem B24262577 : Blo 370760 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B374711 : Blo 370760 374711 := bstep (se 1 (by rfl) ⟨281033, by rfl⟩ : syracuseStep 374711 = 562067) B562067
theorem B473035 : Blo 370760 473035 := bstep (se 1 (by rfl) ⟨354776, by rfl⟩ : syracuseStep 473035 = 709553) B709553
theorem B374731 : Blo 370760 374731 := bstep (se 1 (by rfl) ⟨281048, by rfl⟩ : syracuseStep 374731 = 562097) B562097
theorem B374743 : Blo 370760 374743 := bstep (se 1 (by rfl) ⟨281057, by rfl⟩ : syracuseStep 374743 = 562115) B562115
theorem B473303 : Blo 370760 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B1194205 : Blo 370760 1194205 := bstep (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) B447827
theorem B1259927 : Blo 370760 1259927 := bstep (se 1 (by rfl) ⟨944945, by rfl⟩ : syracuseStep 1259927 = 1889891) B1889891
theorem B1063361 : Blo 370760 1063361 := bstep (se 2 (by rfl) ⟨398760, by rfl⟩ : syracuseStep 1063361 = 797521) B797521
theorem B1063475 : Blo 370760 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B834227 : Blo 370760 834227 := bstep (se 1 (by rfl) ⟨625670, by rfl⟩ : syracuseStep 834227 = 1251341) B1251341
theorem B834263 : Blo 370760 834263 := bstep (se 1 (by rfl) ⟨625697, by rfl⟩ : syracuseStep 834263 = 1251395) B1251395
theorem B1882925 : Blo 370760 1882925 := bstep (se 3 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 1882925 = 706097) B706097
theorem B834443 : Blo 370760 834443 := bstep (se 1 (by rfl) ⟨625832, by rfl⟩ : syracuseStep 834443 = 1251665) B1251665
theorem B474007 : Blo 370760 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B1260467 : Blo 370760 1260467 := bstep (se 1 (by rfl) ⟨945350, by rfl⟩ : syracuseStep 1260467 = 1890701) B1890701
theorem B834497 : Blo 370760 834497 := bstep (se 2 (by rfl) ⟨312936, by rfl⟩ : syracuseStep 834497 = 625873) B625873
theorem B1588241 : Blo 370760 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B834713 : Blo 370760 834713 := bstep (se 2 (by rfl) ⟨313017, by rfl⟩ : syracuseStep 834713 = 626035) B626035
theorem B1260737 : Blo 370760 1260737 := bstep (se 2 (by rfl) ⟨472776, by rfl⟩ : syracuseStep 1260737 = 945553) B945553
theorem B834803 : Blo 370760 834803 := bstep (se 1 (by rfl) ⟨626102, by rfl⟩ : syracuseStep 834803 = 1252205) B1252205
theorem B670963 : Blo 370760 670963 := bstep (se 1 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 670963 = 1006445) B1006445
theorem B834839 : Blo 370760 834839 := bstep (se 1 (by rfl) ⟨626129, by rfl⟩ : syracuseStep 834839 = 1252259) B1252259
theorem B1949021 : Blo 370760 1949021 := bstep (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) B730883
theorem B835019 : Blo 370760 835019 := bstep (se 1 (by rfl) ⟨626264, by rfl⟩ : syracuseStep 835019 = 1252529) B1252529
theorem B671179 : Blo 370760 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B835073 : Blo 370760 835073 := bstep (se 2 (by rfl) ⟨313152, by rfl⟩ : syracuseStep 835073 = 626305) B626305
theorem B2276909 : Blo 370760 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B3391051 : Blo 370760 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B704153 : Blo 370760 704153 := bstep (se 2 (by rfl) ⟨264057, by rfl⟩ : syracuseStep 704153 = 528115) B528115
theorem B835289 : Blo 370760 835289 := bstep (se 2 (by rfl) ⟨313233, by rfl⟩ : syracuseStep 835289 = 626467) B626467
theorem B1261277 : Blo 370760 1261277 := bstep (se 3 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 1261277 = 472979) B472979
theorem B835379 : Blo 370760 835379 := bstep (se 1 (by rfl) ⟨626534, by rfl⟩ : syracuseStep 835379 = 1253069) B1253069
theorem B835415 : Blo 370760 835415 := bstep (se 1 (by rfl) ⟨626561, by rfl⟩ : syracuseStep 835415 = 1253123) B1253123
theorem B1589165 : Blo 370760 1589165 := bstep (se 3 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 1589165 = 595937) B595937
theorem B835595 : Blo 370760 835595 := bstep (se 1 (by rfl) ⟨626696, by rfl⟩ : syracuseStep 835595 = 1253393) B1253393
theorem B2113553 : Blo 370760 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B835649 : Blo 370760 835649 := bstep (se 2 (by rfl) ⟨313368, by rfl⟩ : syracuseStep 835649 = 626737) B626737
theorem B5718221 : Blo 370760 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B704791 : Blo 370760 704791 := bstep (se 1 (by rfl) ⟨528593, by rfl⟩ : syracuseStep 704791 = 1057187) B1057187
theorem B835865 : Blo 370760 835865 := bstep (se 2 (by rfl) ⟨313449, by rfl⟩ : syracuseStep 835865 = 626899) B626899
theorem B1786157 : Blo 370760 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B835955 : Blo 370760 835955 := bstep (se 1 (by rfl) ⟨626966, by rfl⟩ : syracuseStep 835955 = 1253933) B1253933
theorem B835991 : Blo 370760 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B2114009 : Blo 370760 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B1131059 : Blo 370760 1131059 := bstep (se 1 (by rfl) ⟨848294, by rfl⟩ : syracuseStep 1131059 = 1696589) B1696589
theorem B836171 : Blo 370760 836171 := bstep (se 1 (by rfl) ⟨627128, by rfl⟩ : syracuseStep 836171 = 1254257) B1254257
theorem B3031627 : Blo 370760 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B836225 : Blo 370760 836225 := bstep (se 2 (by rfl) ⟨313584, by rfl⟩ : syracuseStep 836225 = 627169) B627169
theorem B672563 : Blo 370760 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B1262411 : Blo 370760 1262411 := bstep (se 1 (by rfl) ⟨946808, by rfl⟩ : syracuseStep 1262411 = 1893617) B1893617
theorem B836441 : Blo 370760 836441 := bstep (se 2 (by rfl) ⟨313665, by rfl⟩ : syracuseStep 836441 = 627331) B627331
theorem B836531 : Blo 370760 836531 := bstep (se 1 (by rfl) ⟨627398, by rfl⟩ : syracuseStep 836531 = 1254797) B1254797
theorem B836567 : Blo 370760 836567 := bstep (se 1 (by rfl) ⟨627425, by rfl⟩ : syracuseStep 836567 = 1254851) B1254851
theorem B705611 : Blo 370760 705611 := bstep (se 1 (by rfl) ⟨529208, by rfl⟩ : syracuseStep 705611 = 1058417) B1058417
theorem B1262681 : Blo 370760 1262681 := bstep (se 2 (by rfl) ⟨473505, by rfl⟩ : syracuseStep 1262681 = 947011) B947011
theorem B705665 : Blo 370760 705665 := bstep (se 2 (by rfl) ⟨264624, by rfl⟩ : syracuseStep 705665 = 529249) B529249
theorem B836747 : Blo 370760 836747 := bstep (se 1 (by rfl) ⟨627560, by rfl⟩ : syracuseStep 836747 = 1255121) B1255121
theorem B836801 : Blo 370760 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B378155 : Blo 370760 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B1590617 : Blo 370760 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B1066391 : Blo 370760 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B837017 : Blo 370760 837017 := bstep (se 2 (by rfl) ⟨313881, by rfl⟩ : syracuseStep 837017 = 627763) B627763
theorem B837107 : Blo 370760 837107 := bstep (se 1 (by rfl) ⟨627830, by rfl⟩ : syracuseStep 837107 = 1255661) B1255661
theorem B837143 : Blo 370760 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B837323 : Blo 370760 837323 := bstep (se 1 (by rfl) ⟨627992, by rfl⟩ : syracuseStep 837323 = 1255985) B1255985
theorem B837377 : Blo 370760 837377 := bstep (se 2 (by rfl) ⟨314016, by rfl⟩ : syracuseStep 837377 = 628033) B628033
theorem B1263383 : Blo 370760 1263383 := bstep (se 1 (by rfl) ⟨947537, by rfl⟩ : syracuseStep 1263383 = 1895075) B1895075
theorem B837593 : Blo 370760 837593 := bstep (se 2 (by rfl) ⟨314097, by rfl⟩ : syracuseStep 837593 = 628195) B628195
theorem B706583 : Blo 370760 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B837683 : Blo 370760 837683 := bstep (se 1 (by rfl) ⟨628262, by rfl⟩ : syracuseStep 837683 = 1256525) B1256525
theorem B837719 : Blo 370760 837719 := bstep (se 1 (by rfl) ⟨628289, by rfl⟩ : syracuseStep 837719 = 1256579) B1256579
theorem B837899 : Blo 370760 837899 := bstep (se 1 (by rfl) ⟨628424, by rfl⟩ : syracuseStep 837899 = 1256849) B1256849
theorem B2836781 : Blo 370760 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B10799405 : Blo 370760 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B1263923 : Blo 370760 1263923 := bstep (se 1 (by rfl) ⟨947942, by rfl⟩ : syracuseStep 1263923 = 1895885) B1895885
theorem B837953 : Blo 370760 837953 := bstep (se 2 (by rfl) ⟨314232, by rfl⟩ : syracuseStep 837953 = 628465) B628465
theorem B674177 : Blo 370760 674177 := bstep (se 2 (by rfl) ⟨252816, by rfl⟩ : syracuseStep 674177 = 505633) B505633
theorem B838169 : Blo 370760 838169 := bstep (se 2 (by rfl) ⟨314313, by rfl⟩ : syracuseStep 838169 = 628627) B628627
theorem B707123 : Blo 370760 707123 := bstep (se 1 (by rfl) ⟨530342, by rfl⟩ : syracuseStep 707123 = 1060685) B1060685
theorem B1264193 : Blo 370760 1264193 := bstep (se 2 (by rfl) ⟨474072, by rfl⟩ : syracuseStep 1264193 = 948145) B948145
theorem B3066443 : Blo 370760 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B1886813 : Blo 370760 1886813 := bstep (se 3 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 1886813 = 707555) B707555
theorem B838259 : Blo 370760 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B838295 : Blo 370760 838295 := bstep (se 1 (by rfl) ⟨628721, by rfl⟩ : syracuseStep 838295 = 1257443) B1257443
theorem B1198871 : Blo 370760 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B838475 : Blo 370760 838475 := bstep (se 1 (by rfl) ⟨628856, by rfl⟩ : syracuseStep 838475 = 1257713) B1257713
theorem B838529 : Blo 370760 838529 := bstep (se 2 (by rfl) ⟨314448, by rfl⟩ : syracuseStep 838529 = 628897) B628897
theorem B1592257 : Blo 370760 1592257 := bstep (se 2 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 1592257 = 1194193) B1194193
theorem B707609 : Blo 370760 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B838745 : Blo 370760 838745 := bstep (se 2 (by rfl) ⟨314529, by rfl⟩ : syracuseStep 838745 = 629059) B629059
theorem B1264733 : Blo 370760 1264733 := bstep (se 3 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 1264733 = 474275) B474275
theorem B838835 : Blo 370760 838835 := bstep (se 1 (by rfl) ⟨629126, by rfl⟩ : syracuseStep 838835 = 1258253) B1258253
theorem B1133747 : Blo 370760 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B838871 : Blo 370760 838871 := bstep (se 1 (by rfl) ⟨629153, by rfl⟩ : syracuseStep 838871 = 1258307) B1258307
theorem B839051 : Blo 370760 839051 := bstep (se 1 (by rfl) ⟨629288, by rfl⟩ : syracuseStep 839051 = 1258577) B1258577
theorem B839105 : Blo 370760 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B1592855 : Blo 370760 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B2379365 : Blo 370760 2379365 := bstep (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) B446131
theorem B1199767 : Blo 370760 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B839321 : Blo 370760 839321 := bstep (se 2 (by rfl) ⟨314745, by rfl⟩ : syracuseStep 839321 = 629491) B629491
theorem B839411 : Blo 370760 839411 := bstep (se 1 (by rfl) ⟨629558, by rfl⟩ : syracuseStep 839411 = 1259117) B1259117
theorem B839447 : Blo 370760 839447 := bstep (se 1 (by rfl) ⟨629585, by rfl⟩ : syracuseStep 839447 = 1259171) B1259171
theorem B5394221 : Blo 370760 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B1789847 : Blo 370760 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B839627 : Blo 370760 839627 := bstep (se 1 (by rfl) ⟨629720, by rfl⟩ : syracuseStep 839627 = 1259441) B1259441
theorem B839681 : Blo 370760 839681 := bstep (se 2 (by rfl) ⟨314880, by rfl⟩ : syracuseStep 839681 = 629761) B629761
theorem B2379851 : Blo 370760 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B1200203 : Blo 370760 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B839897 : Blo 370760 839897 := bstep (se 2 (by rfl) ⟨314961, by rfl⟩ : syracuseStep 839897 = 629923) B629923
theorem B4837637 : Blo 370760 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B839987 : Blo 370760 839987 := bstep (se 1 (by rfl) ⟨629990, by rfl⟩ : syracuseStep 839987 = 1259981) B1259981
theorem B840023 : Blo 370760 840023 := bstep (se 1 (by rfl) ⟨630017, by rfl⟩ : syracuseStep 840023 = 1260035) B1260035
theorem B2019763 : Blo 370760 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B610763 : Blo 370760 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B709067 : Blo 370760 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B1364441 : Blo 370760 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B840203 : Blo 370760 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B840257 : Blo 370760 840257 := bstep (se 2 (by rfl) ⟨315096, by rfl⟩ : syracuseStep 840257 = 630193) B630193
theorem B709249 : Blo 370760 709249 := bstep (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) B531937
theorem B1888919 : Blo 370760 1888919 := bstep (se 1 (by rfl) ⟨1416689, by rfl⟩ : syracuseStep 1888919 = 2833379) B2833379
theorem B938699 : Blo 370760 938699 := bstep (se 1 (by rfl) ⟨704024, by rfl⟩ : syracuseStep 938699 = 1408049) B1408049
theorem B840473 : Blo 370760 840473 := bstep (se 2 (by rfl) ⟨315177, by rfl⟩ : syracuseStep 840473 = 630355) B630355
theorem B1594187 : Blo 370760 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B840563 : Blo 370760 840563 := bstep (se 1 (by rfl) ⟨630422, by rfl⟩ : syracuseStep 840563 = 1260845) B1260845
theorem B840599 : Blo 370760 840599 := bstep (se 1 (by rfl) ⟨630449, by rfl⟩ : syracuseStep 840599 = 1260899) B1260899
theorem B807833 : Blo 370760 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B4248611 : Blo 370760 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B939073 : Blo 370760 939073 := bstep (se 2 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 939073 = 704305) B704305
theorem B709697 : Blo 370760 709697 := bstep (se 2 (by rfl) ⟨266136, by rfl⟩ : syracuseStep 709697 = 532273) B532273
theorem B840779 : Blo 370760 840779 := bstep (se 1 (by rfl) ⟨630584, by rfl⟩ : syracuseStep 840779 = 1261169) B1261169
theorem B840833 : Blo 370760 840833 := bstep (se 2 (by rfl) ⟨315312, by rfl⟩ : syracuseStep 840833 = 630625) B630625
theorem B841049 : Blo 370760 841049 := bstep (se 2 (by rfl) ⟨315393, by rfl⟩ : syracuseStep 841049 = 630787) B630787
theorem B710039 : Blo 370760 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B841139 : Blo 370760 841139 := bstep (se 1 (by rfl) ⟨630854, by rfl⟩ : syracuseStep 841139 = 1261709) B1261709
theorem B808385 : Blo 370760 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B841175 : Blo 370760 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B2872907 : Blo 370760 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B841355 : Blo 370760 841355 := bstep (se 1 (by rfl) ⟨631016, by rfl⟩ : syracuseStep 841355 = 1262033) B1262033
theorem B939671 : Blo 370760 939671 := bstep (se 1 (by rfl) ⟨704753, by rfl⟩ : syracuseStep 939671 = 1409507) B1409507
theorem B841409 : Blo 370760 841409 := bstep (se 2 (by rfl) ⟨315528, by rfl⟩ : syracuseStep 841409 = 631057) B631057
theorem B2119385 : Blo 370760 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B2676581 : Blo 370760 2676581 := bstep (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) B501859
theorem B841625 : Blo 370760 841625 := bstep (se 2 (by rfl) ⟨315609, by rfl⟩ : syracuseStep 841625 = 631219) B631219
theorem B6346673 : Blo 370760 6346673 := bstep (se 2 (by rfl) ⟨2380002, by rfl⟩ : syracuseStep 6346673 = 4760005) B4760005
theorem B1595315 : Blo 370760 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B841715 : Blo 370760 841715 := bstep (se 1 (by rfl) ⟨631286, by rfl⟩ : syracuseStep 841715 = 1262573) B1262573
theorem B841751 : Blo 370760 841751 := bstep (se 1 (by rfl) ⟨631313, by rfl⟩ : syracuseStep 841751 = 1262627) B1262627
theorem B710707 : Blo 370760 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B2840669 : Blo 370760 2840669 := bstep (se 3 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 2840669 = 1065251) B1065251
theorem B841931 : Blo 370760 841931 := bstep (se 1 (by rfl) ⟨631448, by rfl⟩ : syracuseStep 841931 = 1262897) B1262897
theorem B841985 : Blo 370760 841985 := bstep (se 2 (by rfl) ⟨315744, by rfl⟩ : syracuseStep 841985 = 631489) B631489
theorem B940481 : Blo 370760 940481 := bstep (se 2 (by rfl) ⟨352680, by rfl⟩ : syracuseStep 940481 = 705361) B705361
theorem B842201 : Blo 370760 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B711155 : Blo 370760 711155 := bstep (se 1 (by rfl) ⟨533366, by rfl⟩ : syracuseStep 711155 = 1066733) B1066733
theorem B711193 : Blo 370760 711193 := bstep (se 2 (by rfl) ⟨266697, by rfl⟩ : syracuseStep 711193 = 533395) B533395
theorem B842291 : Blo 370760 842291 := bstep (se 1 (by rfl) ⟨631718, by rfl⟩ : syracuseStep 842291 = 1263437) B1263437
theorem B842327 : Blo 370760 842327 := bstep (se 1 (by rfl) ⟨631745, by rfl⟩ : syracuseStep 842327 = 1263491) B1263491
theorem B809651 : Blo 370760 809651 := bstep (se 1 (by rfl) ⟨607238, by rfl⟩ : syracuseStep 809651 = 1214477) B1214477
theorem B842507 : Blo 370760 842507 := bstep (se 1 (by rfl) ⟨631880, by rfl⟩ : syracuseStep 842507 = 1263761) B1263761
theorem B842561 : Blo 370760 842561 := bstep (se 2 (by rfl) ⟨315960, by rfl⟩ : syracuseStep 842561 = 631921) B631921
theorem B6970211 : Blo 370760 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B941017 : Blo 370760 941017 := bstep (se 2 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 941017 = 705763) B705763
theorem B842777 : Blo 370760 842777 := bstep (se 2 (by rfl) ⟨316041, by rfl⟩ : syracuseStep 842777 = 632083) B632083
theorem B842867 : Blo 370760 842867 := bstep (se 1 (by rfl) ⟨632150, by rfl⟩ : syracuseStep 842867 = 1264301) B1264301
theorem B842903 : Blo 370760 842903 := bstep (se 1 (by rfl) ⟨632177, by rfl⟩ : syracuseStep 842903 = 1264355) B1264355
theorem B1268939 : Blo 370760 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B2121025 : Blo 370760 2121025 := bstep (se 2 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 2121025 = 1590769) B1590769
theorem B843083 : Blo 370760 843083 := bstep (se 1 (by rfl) ⟨632312, by rfl⟩ : syracuseStep 843083 = 1264625) B1264625
theorem B9592181 : Blo 370760 9592181 := bstep (se 5 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 9592181 = 899267) B899267
theorem B843137 : Blo 370760 843137 := bstep (se 2 (by rfl) ⟨316176, by rfl⟩ : syracuseStep 843137 = 632353) B632353
theorem B417163 : Blo 370760 417163 := bstep (se 1 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 417163 = 625745) B625745
theorem B2383283 : Blo 370760 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B417271 : Blo 370760 417271 := bstep (se 1 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 417271 = 625907) B625907
theorem B417451 : Blo 370760 417451 := bstep (se 1 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 417451 = 626177) B626177
theorem B5791493 : Blo 370760 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B417559 : Blo 370760 417559 := bstep (se 1 (by rfl) ⟨313169, by rfl⟩ : syracuseStep 417559 = 626339) B626339
theorem B1597229 : Blo 370760 1597229 := bstep (se 3 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 1597229 = 598961) B598961
theorem B417739 : Blo 370760 417739 := bstep (se 1 (by rfl) ⟨313304, by rfl⟩ : syracuseStep 417739 = 626609) B626609
theorem B942131 : Blo 370760 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B417847 : Blo 370760 417847 := bstep (se 1 (by rfl) ⟨313385, by rfl⟩ : syracuseStep 417847 = 626771) B626771
theorem B1892483 : Blo 370760 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B16113815 : Blo 370760 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B418027 : Blo 370760 418027 := bstep (se 1 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 418027 = 627041) B627041
theorem B418135 : Blo 370760 418135 := bstep (se 1 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 418135 = 627203) B627203
theorem B942425 : Blo 370760 942425 := bstep (se 2 (by rfl) ⟨353409, by rfl⟩ : syracuseStep 942425 = 706819) B706819
theorem B1008089 : Blo 370760 1008089 := bstep (se 2 (by rfl) ⟨378033, by rfl⟩ : syracuseStep 1008089 = 756067) B756067
theorem B1597913 : Blo 370760 1597913 := bstep (se 2 (by rfl) ⟨599217, by rfl⟩ : syracuseStep 1597913 = 1198435) B1198435
theorem B418315 : Blo 370760 418315 := bstep (se 1 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 418315 = 627473) B627473
theorem B418423 : Blo 370760 418423 := bstep (se 1 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 418423 = 627635) B627635
theorem B418603 : Blo 370760 418603 := bstep (se 1 (by rfl) ⟨313952, by rfl⟩ : syracuseStep 418603 = 627905) B627905
theorem B418711 : Blo 370760 418711 := bstep (se 1 (by rfl) ⟨314033, by rfl⟩ : syracuseStep 418711 = 628067) B628067
theorem B418891 : Blo 370760 418891 := bstep (se 1 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 418891 = 628337) B628337
theorem B418999 : Blo 370760 418999 := bstep (se 1 (by rfl) ⟨314249, by rfl⟩ : syracuseStep 418999 = 628499) B628499
theorem B419179 : Blo 370760 419179 := bstep (se 1 (by rfl) ⟨314384, by rfl⟩ : syracuseStep 419179 = 628769) B628769
theorem B1795459 : Blo 370760 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B419287 : Blo 370760 419287 := bstep (se 1 (by rfl) ⟨314465, by rfl⟩ : syracuseStep 419287 = 628931) B628931
theorem B1336907 : Blo 370760 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B419467 : Blo 370760 419467 := bstep (se 1 (by rfl) ⟨314600, by rfl⟩ : syracuseStep 419467 = 629201) B629201
theorem B419575 : Blo 370760 419575 := bstep (se 1 (by rfl) ⟨314681, by rfl⟩ : syracuseStep 419575 = 629363) B629363
theorem B419755 : Blo 370760 419755 := bstep (se 1 (by rfl) ⟨314816, by rfl⟩ : syracuseStep 419755 = 629633) B629633
theorem B944075 : Blo 370760 944075 := bstep (se 1 (by rfl) ⟨708056, by rfl⟩ : syracuseStep 944075 = 1416113) B1416113
theorem B419863 : Blo 370760 419863 := bstep (se 1 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 419863 = 629795) B629795
theorem B420043 : Blo 370760 420043 := bstep (se 1 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 420043 = 630065) B630065
theorem B420151 : Blo 370760 420151 := bstep (se 1 (by rfl) ⟨315113, by rfl⟩ : syracuseStep 420151 = 630227) B630227
theorem B420331 : Blo 370760 420331 := bstep (se 1 (by rfl) ⟨315248, by rfl⟩ : syracuseStep 420331 = 630497) B630497
theorem B420439 : Blo 370760 420439 := bstep (se 1 (by rfl) ⟨315329, by rfl⟩ : syracuseStep 420439 = 630659) B630659
theorem B2124467 : Blo 370760 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B1010369 : Blo 370760 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B420619 : Blo 370760 420619 := bstep (se 1 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 420619 = 630929) B630929
theorem B682777 : Blo 370760 682777 := bstep (se 2 (by rfl) ⟨256041, by rfl⟩ : syracuseStep 682777 = 512083) B512083
theorem B420727 : Blo 370760 420727 := bstep (se 1 (by rfl) ⟨315545, by rfl⟩ : syracuseStep 420727 = 631091) B631091
theorem B945047 : Blo 370760 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B420907 : Blo 370760 420907 := bstep (se 1 (by rfl) ⟨315680, by rfl⟩ : syracuseStep 420907 = 631361) B631361
theorem B421015 : Blo 370760 421015 := bstep (se 1 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 421015 = 631523) B631523
theorem B421195 : Blo 370760 421195 := bstep (se 1 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 421195 = 631793) B631793
theorem B421303 : Blo 370760 421303 := bstep (se 1 (by rfl) ⟨315977, by rfl⟩ : syracuseStep 421303 = 631955) B631955
theorem B945715 : Blo 370760 945715 := bstep (se 1 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 945715 = 1418573) B1418573
theorem B421483 : Blo 370760 421483 := bstep (se 1 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 421483 = 632225) B632225
theorem B1273495 : Blo 370760 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2420375 : Blo 370760 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B2879155 : Blo 370760 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B945857 : Blo 370760 945857 := bstep (se 2 (by rfl) ⟨354696, by rfl⟩ : syracuseStep 945857 = 709393) B709393
theorem B13758149 : Blo 370760 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B421591 : Blo 370760 421591 := bstep (se 1 (by rfl) ⟨316193, by rfl⟩ : syracuseStep 421591 = 632387) B632387
theorem B1896209 : Blo 370760 1896209 := bstep (se 2 (by rfl) ⟨711078, by rfl⟩ : syracuseStep 1896209 = 1422157) B1422157
theorem B1896371 : Blo 370760 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B684121 : Blo 370760 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B2125925 : Blo 370760 2125925 := bstep (se 4 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 2125925 = 398611) B398611
theorem B3174977 : Blo 370760 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B947123 : Blo 370760 947123 := bstep (se 1 (by rfl) ⟨710342, by rfl⟩ : syracuseStep 947123 = 1420685) B1420685
theorem B1307585 : Blo 370760 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B1078679 : Blo 370760 1078679 := bstep (se 1 (by rfl) ⟨809009, by rfl⟩ : syracuseStep 1078679 = 1618019) B1618019
theorem B947659 : Blo 370760 947659 := bstep (se 1 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 947659 = 1421489) B1421489
theorem B947801 : Blo 370760 947801 := bstep (se 2 (by rfl) ⟨355425, by rfl⟩ : syracuseStep 947801 = 710851) B710851
theorem B2258563 : Blo 370760 2258563 := bstep (se 1 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 2258563 = 3387845) B3387845
theorem B9565937 : Blo 370760 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B1472435 : Blo 370760 1472435 := bstep (se 1 (by rfl) ⟨1104326, by rfl⟩ : syracuseStep 1472435 = 2208653) B2208653
theorem B15333299 : Blo 370760 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B1341463 : Blo 370760 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B21493835 : Blo 370760 21493835 := bstep (se 1 (by rfl) ⟨16120376, by rfl⟩ : syracuseStep 21493835 = 32240753) B32240753
theorem B1046807 : Blo 370760 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B850265 : Blo 370760 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B8092021 : Blo 370760 8092021 := bstep (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) B758627
theorem B850355 : Blo 370760 850355 := bstep (se 1 (by rfl) ⟨637766, by rfl⟩ : syracuseStep 850355 = 1275533) B1275533
theorem B1505837 : Blo 370760 1505837 := bstep (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) B564689
theorem B2882141 : Blo 370760 2882141 := bstep (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) B1080803
theorem B719489 : Blo 370760 719489 := bstep (se 2 (by rfl) ⟨269808, by rfl⟩ : syracuseStep 719489 = 539617) B539617
theorem B1342097 : Blo 370760 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B556235 : Blo 370760 556235 := bstep (se 1 (by rfl) ⟨417176, by rfl⟩ : syracuseStep 556235 = 834353) B834353
theorem B556247 : Blo 370760 556247 := bstep (se 1 (by rfl) ⟨417185, by rfl⟩ : syracuseStep 556247 = 834371) B834371
theorem B556313 : Blo 370760 556313 := bstep (se 2 (by rfl) ⟨208617, by rfl⟩ : syracuseStep 556313 = 417235) B417235
theorem B556427 : Blo 370760 556427 := bstep (se 1 (by rfl) ⟨417320, by rfl⟩ : syracuseStep 556427 = 834641) B834641
theorem B556439 : Blo 370760 556439 := bstep (se 1 (by rfl) ⟨417329, by rfl⟩ : syracuseStep 556439 = 834659) B834659
theorem B556505 : Blo 370760 556505 := bstep (se 2 (by rfl) ⟨208689, by rfl⟩ : syracuseStep 556505 = 417379) B417379
theorem B1408535 : Blo 370760 1408535 := bstep (se 1 (by rfl) ⟨1056401, by rfl⟩ : syracuseStep 1408535 = 2112803) B2112803
theorem B3571235 : Blo 370760 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B556619 : Blo 370760 556619 := bstep (se 1 (by rfl) ⟨417464, by rfl⟩ : syracuseStep 556619 = 834929) B834929
theorem B1343051 : Blo 370760 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B556631 : Blo 370760 556631 := bstep (se 1 (by rfl) ⟨417473, by rfl⟩ : syracuseStep 556631 = 834947) B834947
theorem B556697 : Blo 370760 556697 := bstep (se 2 (by rfl) ⟨208761, by rfl⟩ : syracuseStep 556697 = 417523) B417523
theorem B556811 : Blo 370760 556811 := bstep (se 1 (by rfl) ⟨417608, by rfl⟩ : syracuseStep 556811 = 835217) B835217
theorem B556823 : Blo 370760 556823 := bstep (se 1 (by rfl) ⟨417617, by rfl⟩ : syracuseStep 556823 = 835235) B835235
theorem B2817827 : Blo 370760 2817827 := bstep (se 1 (by rfl) ⟨2113370, by rfl⟩ : syracuseStep 2817827 = 4226741) B4226741
theorem B556889 : Blo 370760 556889 := bstep (se 2 (by rfl) ⟨208833, by rfl⟩ : syracuseStep 556889 = 417667) B417667
theorem B1507265 : Blo 370760 1507265 := bstep (se 2 (by rfl) ⟨565224, by rfl⟩ : syracuseStep 1507265 = 1130449) B1130449
theorem B557003 : Blo 370760 557003 := bstep (se 1 (by rfl) ⟨417752, by rfl⟩ : syracuseStep 557003 = 835505) B835505
theorem B557015 : Blo 370760 557015 := bstep (se 1 (by rfl) ⟨417761, by rfl⟩ : syracuseStep 557015 = 835523) B835523
theorem B753625 : Blo 370760 753625 := bstep (se 2 (by rfl) ⟨282609, by rfl⟩ : syracuseStep 753625 = 565219) B565219
theorem B557063 : Blo 370760 557063 := bstep (se 1 (by rfl) ⟨417797, by rfl⟩ : syracuseStep 557063 = 835595) B835595
theorem B1409035 : Blo 370760 1409035 := bstep (se 1 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 1409035 = 2113553) B2113553
theorem B557099 : Blo 370760 557099 := bstep (se 1 (by rfl) ⟨417824, by rfl⟩ : syracuseStep 557099 = 835649) B835649
theorem B557129 : Blo 370760 557129 := bstep (se 2 (by rfl) ⟨208923, by rfl⟩ : syracuseStep 557129 = 417847) B417847
theorem B557243 : Blo 370760 557243 := bstep (se 1 (by rfl) ⟨417932, by rfl⟩ : syracuseStep 557243 = 835865) B835865
theorem B557303 : Blo 370760 557303 := bstep (se 1 (by rfl) ⟨417977, by rfl⟩ : syracuseStep 557303 = 835955) B835955
theorem B557327 : Blo 370760 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B557369 : Blo 370760 557369 := bstep (se 2 (by rfl) ⟨209013, by rfl⟩ : syracuseStep 557369 = 418027) B418027
theorem B1409339 : Blo 370760 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B754039 : Blo 370760 754039 := bstep (se 1 (by rfl) ⟨565529, by rfl⟩ : syracuseStep 754039 = 1131059) B1131059
theorem B557447 : Blo 370760 557447 := bstep (se 1 (by rfl) ⟨418085, by rfl⟩ : syracuseStep 557447 = 836171) B836171
theorem B557483 : Blo 370760 557483 := bstep (se 1 (by rfl) ⟨418112, by rfl⟩ : syracuseStep 557483 = 836225) B836225
theorem B557513 : Blo 370760 557513 := bstep (se 2 (by rfl) ⟨209067, by rfl⟩ : syracuseStep 557513 = 418135) B418135
theorem B557627 : Blo 370760 557627 := bstep (se 1 (by rfl) ⟨418220, by rfl⟩ : syracuseStep 557627 = 836441) B836441
theorem B557687 : Blo 370760 557687 := bstep (se 1 (by rfl) ⟨418265, by rfl⟩ : syracuseStep 557687 = 836531) B836531
theorem B557711 : Blo 370760 557711 := bstep (se 1 (by rfl) ⟨418283, by rfl⟩ : syracuseStep 557711 = 836567) B836567
theorem B557753 : Blo 370760 557753 := bstep (se 2 (by rfl) ⟨209157, by rfl⟩ : syracuseStep 557753 = 418315) B418315
theorem B557831 : Blo 370760 557831 := bstep (se 1 (by rfl) ⟨418373, by rfl⟩ : syracuseStep 557831 = 836747) B836747
theorem B1409825 : Blo 370760 1409825 := bstep (se 2 (by rfl) ⟨528684, by rfl⟩ : syracuseStep 1409825 = 1057369) B1057369
theorem B557867 : Blo 370760 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B557897 : Blo 370760 557897 := bstep (se 2 (by rfl) ⟨209211, by rfl⟩ : syracuseStep 557897 = 418423) B418423
theorem B3015539 : Blo 370760 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B558011 : Blo 370760 558011 := bstep (se 1 (by rfl) ⟨418508, by rfl⟩ : syracuseStep 558011 = 837017) B837017
theorem B558071 : Blo 370760 558071 := bstep (se 1 (by rfl) ⟨418553, by rfl⟩ : syracuseStep 558071 = 837107) B837107
theorem B558095 : Blo 370760 558095 := bstep (se 1 (by rfl) ⟨418571, by rfl⟩ : syracuseStep 558095 = 837143) B837143
theorem B558137 : Blo 370760 558137 := bstep (se 2 (by rfl) ⟨209301, by rfl⟩ : syracuseStep 558137 = 418603) B418603
theorem B558215 : Blo 370760 558215 := bstep (se 1 (by rfl) ⟨418661, by rfl⟩ : syracuseStep 558215 = 837323) B837323
theorem B558251 : Blo 370760 558251 := bstep (se 1 (by rfl) ⟨418688, by rfl⟩ : syracuseStep 558251 = 837377) B837377
theorem B558281 : Blo 370760 558281 := bstep (se 2 (by rfl) ⟨209355, by rfl⟩ : syracuseStep 558281 = 418711) B418711
theorem B558395 : Blo 370760 558395 := bstep (se 1 (by rfl) ⟨418796, by rfl⟩ : syracuseStep 558395 = 837593) B837593
theorem B558455 : Blo 370760 558455 := bstep (se 1 (by rfl) ⟨418841, by rfl⟩ : syracuseStep 558455 = 837683) B837683
theorem B558479 : Blo 370760 558479 := bstep (se 1 (by rfl) ⟨418859, by rfl⟩ : syracuseStep 558479 = 837719) B837719
theorem B558521 : Blo 370760 558521 := bstep (se 2 (by rfl) ⟨209445, by rfl⟩ : syracuseStep 558521 = 418891) B418891
theorem B558599 : Blo 370760 558599 := bstep (se 1 (by rfl) ⟨418949, by rfl⟩ : syracuseStep 558599 = 837899) B837899
theorem B558635 : Blo 370760 558635 := bstep (se 1 (by rfl) ⟨418976, by rfl⟩ : syracuseStep 558635 = 837953) B837953
theorem B3409451 : Blo 370760 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B558665 : Blo 370760 558665 := bstep (se 2 (by rfl) ⟨209499, by rfl⟩ : syracuseStep 558665 = 418999) B418999
theorem B22808141 : Blo 370760 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B1508951 : Blo 370760 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B558779 : Blo 370760 558779 := bstep (se 1 (by rfl) ⟨419084, by rfl⟩ : syracuseStep 558779 = 838169) B838169
theorem B1410797 : Blo 370760 1410797 := bstep (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) B529049
theorem B558839 : Blo 370760 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B558863 : Blo 370760 558863 := bstep (se 1 (by rfl) ⟨419147, by rfl⟩ : syracuseStep 558863 = 838295) B838295
theorem B558905 : Blo 370760 558905 := bstep (se 2 (by rfl) ⟨209589, by rfl⟩ : syracuseStep 558905 = 419179) B419179
theorem B2393945 : Blo 370760 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B558983 : Blo 370760 558983 := bstep (se 1 (by rfl) ⟨419237, by rfl⟩ : syracuseStep 558983 = 838475) B838475
theorem B853895 : Blo 370760 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B559019 : Blo 370760 559019 := bstep (se 1 (by rfl) ⟨419264, by rfl⟩ : syracuseStep 559019 = 838529) B838529
theorem B559049 : Blo 370760 559049 := bstep (se 2 (by rfl) ⟨209643, by rfl⟩ : syracuseStep 559049 = 419287) B419287
theorem B559163 : Blo 370760 559163 := bstep (se 1 (by rfl) ⟨419372, by rfl⟩ : syracuseStep 559163 = 838745) B838745
theorem B559223 : Blo 370760 559223 := bstep (se 1 (by rfl) ⟨419417, by rfl⟩ : syracuseStep 559223 = 838835) B838835
theorem B755831 : Blo 370760 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B559247 : Blo 370760 559247 := bstep (se 1 (by rfl) ⟨419435, by rfl⟩ : syracuseStep 559247 = 838871) B838871
theorem B559289 : Blo 370760 559289 := bstep (se 2 (by rfl) ⟨209733, by rfl⟩ : syracuseStep 559289 = 419467) B419467
theorem B559367 : Blo 370760 559367 := bstep (se 1 (by rfl) ⟨419525, by rfl⟩ : syracuseStep 559367 = 839051) B839051
theorem B559403 : Blo 370760 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B559433 : Blo 370760 559433 := bstep (se 2 (by rfl) ⟨209787, by rfl⟩ : syracuseStep 559433 = 419575) B419575
theorem B559547 : Blo 370760 559547 := bstep (se 1 (by rfl) ⟨419660, by rfl⟩ : syracuseStep 559547 = 839321) B839321
theorem B559607 : Blo 370760 559607 := bstep (se 1 (by rfl) ⟨419705, by rfl⟩ : syracuseStep 559607 = 839411) B839411
theorem B559631 : Blo 370760 559631 := bstep (se 1 (by rfl) ⟨419723, by rfl⟩ : syracuseStep 559631 = 839447) B839447
theorem B559673 : Blo 370760 559673 := bstep (se 2 (by rfl) ⟨209877, by rfl⟩ : syracuseStep 559673 = 419755) B419755
theorem B559751 : Blo 370760 559751 := bstep (se 1 (by rfl) ⟨419813, by rfl⟩ : syracuseStep 559751 = 839627) B839627
theorem B559787 : Blo 370760 559787 := bstep (se 1 (by rfl) ⟨419840, by rfl⟩ : syracuseStep 559787 = 839681) B839681
theorem B559817 : Blo 370760 559817 := bstep (se 2 (by rfl) ⟨209931, by rfl⟩ : syracuseStep 559817 = 419863) B419863
theorem B559931 : Blo 370760 559931 := bstep (se 1 (by rfl) ⟨419948, by rfl⟩ : syracuseStep 559931 = 839897) B839897
theorem B559991 : Blo 370760 559991 := bstep (se 1 (by rfl) ⟨419993, by rfl⟩ : syracuseStep 559991 = 839987) B839987
theorem B560015 : Blo 370760 560015 := bstep (se 1 (by rfl) ⟨420011, by rfl⟩ : syracuseStep 560015 = 840023) B840023
theorem B560057 : Blo 370760 560057 := bstep (se 2 (by rfl) ⟨210021, by rfl⟩ : syracuseStep 560057 = 420043) B420043
theorem B560135 : Blo 370760 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B560171 : Blo 370760 560171 := bstep (se 1 (by rfl) ⟨420128, by rfl⟩ : syracuseStep 560171 = 840257) B840257
theorem B560201 : Blo 370760 560201 := bstep (se 2 (by rfl) ⟨210075, by rfl⟩ : syracuseStep 560201 = 420151) B420151
theorem B625799 : Blo 370760 625799 := bstep (se 1 (by rfl) ⟨469349, by rfl⟩ : syracuseStep 625799 = 938699) B938699
theorem B560315 : Blo 370760 560315 := bstep (se 1 (by rfl) ⟨420236, by rfl⟩ : syracuseStep 560315 = 840473) B840473
theorem B560375 : Blo 370760 560375 := bstep (se 1 (by rfl) ⟨420281, by rfl⟩ : syracuseStep 560375 = 840563) B840563
theorem B560399 : Blo 370760 560399 := bstep (se 1 (by rfl) ⟨420299, by rfl⟩ : syracuseStep 560399 = 840599) B840599
theorem B560441 : Blo 370760 560441 := bstep (se 2 (by rfl) ⟨210165, by rfl⟩ : syracuseStep 560441 = 420331) B420331
theorem B560519 : Blo 370760 560519 := bstep (se 1 (by rfl) ⟨420389, by rfl⟩ : syracuseStep 560519 = 840779) B840779
theorem B560555 : Blo 370760 560555 := bstep (se 1 (by rfl) ⟨420416, by rfl⟩ : syracuseStep 560555 = 840833) B840833
theorem B560585 : Blo 370760 560585 := bstep (se 2 (by rfl) ⟨210219, by rfl⟩ : syracuseStep 560585 = 420439) B420439
theorem B560699 : Blo 370760 560699 := bstep (se 1 (by rfl) ⟨420524, by rfl⟩ : syracuseStep 560699 = 841049) B841049
theorem B560759 : Blo 370760 560759 := bstep (se 1 (by rfl) ⟨420569, by rfl⟩ : syracuseStep 560759 = 841139) B841139
theorem B560783 : Blo 370760 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B560825 : Blo 370760 560825 := bstep (se 2 (by rfl) ⟨210309, by rfl⟩ : syracuseStep 560825 = 420619) B420619
theorem B560903 : Blo 370760 560903 := bstep (se 1 (by rfl) ⟨420677, by rfl⟩ : syracuseStep 560903 = 841355) B841355
theorem B626447 : Blo 370760 626447 := bstep (se 1 (by rfl) ⟨469835, by rfl⟩ : syracuseStep 626447 = 939671) B939671
theorem B560939 : Blo 370760 560939 := bstep (se 1 (by rfl) ⟨420704, by rfl⟩ : syracuseStep 560939 = 841409) B841409
theorem B1412923 : Blo 370760 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B560969 : Blo 370760 560969 := bstep (se 2 (by rfl) ⟨210363, by rfl⟩ : syracuseStep 560969 = 420727) B420727
theorem B5083033 : Blo 370760 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B561083 : Blo 370760 561083 := bstep (se 1 (by rfl) ⟨420812, by rfl⟩ : syracuseStep 561083 = 841625) B841625
theorem B4231115 : Blo 370760 4231115 := bstep (se 1 (by rfl) ⟨3173336, by rfl⟩ : syracuseStep 4231115 = 6346673) B6346673
theorem B561143 : Blo 370760 561143 := bstep (se 1 (by rfl) ⟨420857, by rfl⟩ : syracuseStep 561143 = 841715) B841715
theorem B561167 : Blo 370760 561167 := bstep (se 1 (by rfl) ⟨420875, by rfl⟩ : syracuseStep 561167 = 841751) B841751
theorem B561209 : Blo 370760 561209 := bstep (se 2 (by rfl) ⟨210453, by rfl⟩ : syracuseStep 561209 = 420907) B420907
theorem B528457 : Blo 370760 528457 := bstep (se 2 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 528457 = 396343) B396343
theorem B561287 : Blo 370760 561287 := bstep (se 1 (by rfl) ⟨420965, by rfl⟩ : syracuseStep 561287 = 841931) B841931
theorem B561323 : Blo 370760 561323 := bstep (se 1 (by rfl) ⟨420992, by rfl⟩ : syracuseStep 561323 = 841985) B841985
theorem B561353 : Blo 370760 561353 := bstep (se 2 (by rfl) ⟨210507, by rfl⟩ : syracuseStep 561353 = 421015) B421015
theorem B1413409 : Blo 370760 1413409 := bstep (se 2 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 1413409 = 1060057) B1060057
theorem B626987 : Blo 370760 626987 := bstep (se 1 (by rfl) ⟨470240, by rfl⟩ : syracuseStep 626987 = 940481) B940481
theorem B561467 : Blo 370760 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B561527 : Blo 370760 561527 := bstep (se 1 (by rfl) ⟨421145, by rfl⟩ : syracuseStep 561527 = 842291) B842291
theorem B561551 : Blo 370760 561551 := bstep (se 1 (by rfl) ⟨421163, by rfl⟩ : syracuseStep 561551 = 842327) B842327
theorem B561593 : Blo 370760 561593 := bstep (se 2 (by rfl) ⟨210597, by rfl⟩ : syracuseStep 561593 = 421195) B421195
theorem B561671 : Blo 370760 561671 := bstep (se 1 (by rfl) ⟨421253, by rfl⟩ : syracuseStep 561671 = 842507) B842507
theorem B561707 : Blo 370760 561707 := bstep (se 1 (by rfl) ⟨421280, by rfl⟩ : syracuseStep 561707 = 842561) B842561
theorem B561737 : Blo 370760 561737 := bstep (se 2 (by rfl) ⟨210651, by rfl⟩ : syracuseStep 561737 = 421303) B421303
theorem B8065655 : Blo 370760 8065655 := bstep (se 1 (by rfl) ⟨6049241, by rfl⟩ : syracuseStep 8065655 = 12098483) B12098483
theorem B8622773 : Blo 370760 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B627385 : Blo 370760 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B561851 : Blo 370760 561851 := bstep (se 1 (by rfl) ⟨421388, by rfl⟩ : syracuseStep 561851 = 842777) B842777
theorem B561911 : Blo 370760 561911 := bstep (se 1 (by rfl) ⟨421433, by rfl⟩ : syracuseStep 561911 = 842867) B842867
theorem B561935 : Blo 370760 561935 := bstep (se 1 (by rfl) ⟨421451, by rfl⟩ : syracuseStep 561935 = 842903) B842903
theorem B561977 : Blo 370760 561977 := bstep (se 2 (by rfl) ⟨210741, by rfl⟩ : syracuseStep 561977 = 421483) B421483
theorem B562055 : Blo 370760 562055 := bstep (se 1 (by rfl) ⟨421541, by rfl⟩ : syracuseStep 562055 = 843083) B843083
theorem B3838873 : Blo 370760 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B6394787 : Blo 370760 6394787 := bstep (se 1 (by rfl) ⟨4796090, by rfl⟩ : syracuseStep 6394787 = 9592181) B9592181
theorem B562091 : Blo 370760 562091 := bstep (se 1 (by rfl) ⟨421568, by rfl⟩ : syracuseStep 562091 = 843137) B843137
theorem B14554037 : Blo 370760 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B562121 : Blo 370760 562121 := bstep (se 2 (by rfl) ⟨210795, by rfl⟩ : syracuseStep 562121 = 421591) B421591
theorem B726059 : Blo 370760 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B1610813 : Blo 370760 1610813 := bstep (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) B604055
theorem B922711 : Blo 370760 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B1414381 : Blo 370760 1414381 := bstep (se 3 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 1414381 = 530393) B530393
theorem B628087 : Blo 370760 628087 := bstep (se 1 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 628087 = 942131) B942131
theorem B1414685 : Blo 370760 1414685 := bstep (se 3 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 1414685 = 530507) B530507
theorem B628283 : Blo 370760 628283 := bstep (se 1 (by rfl) ⟨471212, by rfl⟩ : syracuseStep 628283 = 942425) B942425
theorem B2693017 : Blo 370760 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B628681 : Blo 370760 628681 := bstep (se 2 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 628681 = 471511) B471511
theorem B399367 : Blo 370760 399367 := bstep (se 1 (by rfl) ⟨299525, by rfl⟩ : syracuseStep 399367 = 599051) B599051
theorem B1513559 : Blo 370760 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B1251719 : Blo 370760 1251719 := bstep (se 1 (by rfl) ⟨938789, by rfl⟩ : syracuseStep 1251719 = 1877579) B1877579
theorem B891271 : Blo 370760 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B891425 : Blo 370760 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B793147 : Blo 370760 793147 := bstep (se 1 (by rfl) ⟨594860, by rfl⟩ : syracuseStep 793147 = 1189721) B1189721
theorem B629383 : Blo 370760 629383 := bstep (se 1 (by rfl) ⟨472037, by rfl⟩ : syracuseStep 629383 = 944075) B944075
theorem B531145 : Blo 370760 531145 := bstep (se 2 (by rfl) ⟨199179, by rfl⟩ : syracuseStep 531145 = 398359) B398359
theorem B1252097 : Blo 370760 1252097 := bstep (se 2 (by rfl) ⟨469536, by rfl⟩ : syracuseStep 1252097 = 939073) B939073
theorem B793403 : Blo 370760 793403 := bstep (se 1 (by rfl) ⟨595052, by rfl⟩ : syracuseStep 793403 = 1190105) B1190105
theorem B400187 : Blo 370760 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B1416311 : Blo 370760 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B630031 : Blo 370760 630031 := bstep (se 1 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 630031 = 945047) B945047
theorem B1056185 : Blo 370760 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B1252907 : Blo 370760 1252907 := bstep (se 1 (by rfl) ⟨939680, by rfl⟩ : syracuseStep 1252907 = 1879361) B1879361
theorem B1056527 : Blo 370760 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B630571 : Blo 370760 630571 := bstep (se 1 (by rfl) ⟨472928, by rfl⟩ : syracuseStep 630571 = 945857) B945857
theorem B630713 : Blo 370760 630713 := bstep (se 2 (by rfl) ⟨236517, by rfl⟩ : syracuseStep 630713 = 473035) B473035
theorem B1417283 : Blo 370760 1417283 := bstep (se 1 (by rfl) ⟨1062962, by rfl⟩ : syracuseStep 1417283 = 2125925) B2125925
theorem B10789361 : Blo 370760 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B1057313 : Blo 370760 1057313 := bstep (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) B792985
theorem B631415 : Blo 370760 631415 := bstep (se 1 (by rfl) ⟨473561, by rfl⟩ : syracuseStep 631415 = 947123) B947123
theorem B1254203 : Blo 370760 1254203 := bstep (se 1 (by rfl) ⟨940652, by rfl⟩ : syracuseStep 1254203 = 1881305) B1881305
theorem B1418269 : Blo 370760 1418269 := bstep (se 3 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 1418269 = 531851) B531851
theorem B631867 : Blo 370760 631867 := bstep (se 1 (by rfl) ⟨473900, by rfl⟩ : syracuseStep 631867 = 947801) B947801
theorem B7611479 : Blo 370760 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B632009 : Blo 370760 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B1254689 : Blo 370760 1254689 := bstep (se 2 (by rfl) ⟨470508, by rfl⟩ : syracuseStep 1254689 = 941017) B941017
theorem B14329223 : Blo 370760 14329223 := bstep (se 1 (by rfl) ⟨10746917, by rfl⟩ : syracuseStep 14329223 = 21493835) B21493835
theorem B4072913 : Blo 370760 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B697871 : Blo 370760 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B566843 : Blo 370760 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B566903 : Blo 370760 566903 := bstep (se 1 (by rfl) ⟨425177, by rfl⟩ : syracuseStep 566903 = 850355) B850355
theorem B894617 : Blo 370760 894617 := bstep (se 2 (by rfl) ⟨335481, by rfl⟩ : syracuseStep 894617 = 670963) B670963
theorem B1877741 : Blo 370760 1877741 := bstep (se 3 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 1877741 = 704153) B704153
theorem B2828033 : Blo 370760 2828033 := bstep (se 2 (by rfl) ⟨1060512, by rfl⟩ : syracuseStep 2828033 = 2121025) B2121025
theorem B894731 : Blo 370760 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1255283 : Blo 370760 1255283 := bstep (se 1 (by rfl) ⟨941462, by rfl⟩ : syracuseStep 1255283 = 1882925) B1882925
theorem B894905 : Blo 370760 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B1058827 : Blo 370760 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B370823 : Blo 370760 370823 := bstep (se 1 (by rfl) ⟨278117, by rfl⟩ : syracuseStep 370823 = 556235) B556235
theorem B370831 : Blo 370760 370831 := bstep (se 1 (by rfl) ⟨278123, by rfl⟩ : syracuseStep 370831 = 556247) B556247
theorem B370875 : Blo 370760 370875 := bstep (se 1 (by rfl) ⟨278156, by rfl⟩ : syracuseStep 370875 = 556313) B556313
theorem B370951 : Blo 370760 370951 := bstep (se 1 (by rfl) ⟨278213, by rfl⟩ : syracuseStep 370951 = 556427) B556427
theorem B370959 : Blo 370760 370959 := bstep (se 1 (by rfl) ⟨278219, by rfl⟩ : syracuseStep 370959 = 556439) B556439
theorem B1059101 : Blo 370760 1059101 := bstep (se 3 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 1059101 = 397163) B397163
theorem B371003 : Blo 370760 371003 := bstep (se 1 (by rfl) ⟨278252, by rfl⟩ : syracuseStep 371003 = 556505) B556505
theorem B1517939 : Blo 370760 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B371079 : Blo 370760 371079 := bstep (se 1 (by rfl) ⟨278309, by rfl⟩ : syracuseStep 371079 = 556619) B556619
theorem B895367 : Blo 370760 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B371087 : Blo 370760 371087 := bstep (se 1 (by rfl) ⟨278315, by rfl⟩ : syracuseStep 371087 = 556631) B556631
theorem B371131 : Blo 370760 371131 := bstep (se 1 (by rfl) ⟨278348, by rfl⟩ : syracuseStep 371131 = 556697) B556697
theorem B371207 : Blo 370760 371207 := bstep (se 1 (by rfl) ⟨278405, by rfl⟩ : syracuseStep 371207 = 556811) B556811
theorem B371215 : Blo 370760 371215 := bstep (se 1 (by rfl) ⟨278411, by rfl⟩ : syracuseStep 371215 = 556823) B556823
theorem B1878551 : Blo 370760 1878551 := bstep (se 1 (by rfl) ⟨1408913, by rfl⟩ : syracuseStep 1878551 = 2817827) B2817827
theorem B371259 : Blo 370760 371259 := bstep (se 1 (by rfl) ⟨278444, by rfl⟩ : syracuseStep 371259 = 556889) B556889
theorem B1059443 : Blo 370760 1059443 := bstep (se 1 (by rfl) ⟨794582, by rfl⟩ : syracuseStep 1059443 = 1589165) B1589165
theorem B371335 : Blo 370760 371335 := bstep (se 1 (by rfl) ⟨278501, by rfl⟩ : syracuseStep 371335 = 557003) B557003
theorem B371343 : Blo 370760 371343 := bstep (se 1 (by rfl) ⟨278507, by rfl⟩ : syracuseStep 371343 = 557015) B557015
theorem B371387 : Blo 370760 371387 := bstep (se 1 (by rfl) ⟨278540, by rfl⟩ : syracuseStep 371387 = 557081) B557081
theorem B371463 : Blo 370760 371463 := bstep (se 1 (by rfl) ⟨278597, by rfl⟩ : syracuseStep 371463 = 557195) B557195
theorem B371471 : Blo 370760 371471 := bstep (se 1 (by rfl) ⟨278603, by rfl⟩ : syracuseStep 371471 = 557207) B557207
theorem B3812147 : Blo 370760 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B371515 : Blo 370760 371515 := bstep (se 1 (by rfl) ⟨278636, by rfl⟩ : syracuseStep 371515 = 557273) B557273
theorem B1190771 : Blo 370760 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B1616755 : Blo 370760 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B371591 : Blo 370760 371591 := bstep (se 1 (by rfl) ⟨278693, by rfl⟩ : syracuseStep 371591 = 557387) B557387
theorem B371599 : Blo 370760 371599 := bstep (se 1 (by rfl) ⟨278699, by rfl⟩ : syracuseStep 371599 = 557399) B557399
theorem B371643 : Blo 370760 371643 := bstep (se 1 (by rfl) ⟨278732, by rfl⟩ : syracuseStep 371643 = 557465) B557465
theorem B371719 : Blo 370760 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B371727 : Blo 370760 371727 := bstep (se 1 (by rfl) ⟨278795, by rfl⟩ : syracuseStep 371727 = 557591) B557591
theorem B371771 : Blo 370760 371771 := bstep (se 1 (by rfl) ⟨278828, by rfl⟩ : syracuseStep 371771 = 557657) B557657
theorem B371847 : Blo 370760 371847 := bstep (se 1 (by rfl) ⟨278885, by rfl⟩ : syracuseStep 371847 = 557771) B557771
theorem B371855 : Blo 370760 371855 := bstep (se 1 (by rfl) ⟨278891, by rfl⟩ : syracuseStep 371855 = 557783) B557783
theorem B371899 : Blo 370760 371899 := bstep (se 1 (by rfl) ⟨278924, by rfl⟩ : syracuseStep 371899 = 557849) B557849
theorem B371975 : Blo 370760 371975 := bstep (se 1 (by rfl) ⟨278981, by rfl⟩ : syracuseStep 371975 = 557963) B557963
theorem B371983 : Blo 370760 371983 := bstep (se 1 (by rfl) ⟨278987, by rfl⟩ : syracuseStep 371983 = 557975) B557975
theorem B372027 : Blo 370760 372027 := bstep (se 1 (by rfl) ⟨279020, by rfl⟩ : syracuseStep 372027 = 558041) B558041
theorem B372103 : Blo 370760 372103 := bstep (se 1 (by rfl) ⟨279077, by rfl⟩ : syracuseStep 372103 = 558155) B558155
theorem B372111 : Blo 370760 372111 := bstep (se 1 (by rfl) ⟨279083, by rfl⟩ : syracuseStep 372111 = 558167) B558167
theorem B470443 : Blo 370760 470443 := bstep (se 1 (by rfl) ⟨352832, by rfl⟩ : syracuseStep 470443 = 705665) B705665
theorem B4042169 : Blo 370760 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B372155 : Blo 370760 372155 := bstep (se 1 (by rfl) ⟨279116, by rfl⟩ : syracuseStep 372155 = 558233) B558233
theorem B372231 : Blo 370760 372231 := bstep (se 1 (by rfl) ⟨279173, by rfl⟩ : syracuseStep 372231 = 558347) B558347
theorem B372239 : Blo 370760 372239 := bstep (se 1 (by rfl) ⟨279179, by rfl⟩ : syracuseStep 372239 = 558359) B558359
theorem B372283 : Blo 370760 372283 := bstep (se 1 (by rfl) ⟨279212, by rfl⟩ : syracuseStep 372283 = 558425) B558425
theorem B1060411 : Blo 370760 1060411 := bstep (se 1 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 1060411 = 1590617) B1590617
theorem B372359 : Blo 370760 372359 := bstep (se 1 (by rfl) ⟨279269, by rfl⟩ : syracuseStep 372359 = 558539) B558539
theorem B372367 : Blo 370760 372367 := bstep (se 1 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 372367 = 558551) B558551
theorem B372411 : Blo 370760 372411 := bstep (se 1 (by rfl) ⟨279308, by rfl⟩ : syracuseStep 372411 = 558617) B558617
theorem B372487 : Blo 370760 372487 := bstep (se 1 (by rfl) ⟨279365, by rfl⟩ : syracuseStep 372487 = 558731) B558731
theorem B372495 : Blo 370760 372495 := bstep (se 1 (by rfl) ⟨279371, by rfl⟩ : syracuseStep 372495 = 558743) B558743
theorem B372539 : Blo 370760 372539 := bstep (se 1 (by rfl) ⟨279404, by rfl⟩ : syracuseStep 372539 = 558809) B558809
theorem B1421171 : Blo 370760 1421171 := bstep (se 1 (by rfl) ⟨1065878, by rfl⟩ : syracuseStep 1421171 = 2131757) B2131757
theorem B372615 : Blo 370760 372615 := bstep (se 1 (by rfl) ⟨279461, by rfl⟩ : syracuseStep 372615 = 558923) B558923
theorem B372623 : Blo 370760 372623 := bstep (se 1 (by rfl) ⟨279467, by rfl⟩ : syracuseStep 372623 = 558935) B558935
theorem B372667 : Blo 370760 372667 := bstep (se 1 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 372667 = 559001) B559001
theorem B798665 : Blo 370760 798665 := bstep (se 2 (by rfl) ⟨299499, by rfl⟩ : syracuseStep 798665 = 598999) B598999
theorem B372743 : Blo 370760 372743 := bstep (se 1 (by rfl) ⟨279557, by rfl⟩ : syracuseStep 372743 = 559115) B559115
theorem B372751 : Blo 370760 372751 := bstep (se 1 (by rfl) ⟨279563, by rfl⟩ : syracuseStep 372751 = 559127) B559127
theorem B372795 : Blo 370760 372795 := bstep (se 1 (by rfl) ⟨279596, by rfl⟩ : syracuseStep 372795 = 559193) B559193
theorem B372871 : Blo 370760 372871 := bstep (se 1 (by rfl) ⟨279653, by rfl⟩ : syracuseStep 372871 = 559307) B559307
theorem B372879 : Blo 370760 372879 := bstep (se 1 (by rfl) ⟨279659, by rfl⟩ : syracuseStep 372879 = 559319) B559319
theorem B798905 : Blo 370760 798905 := bstep (se 2 (by rfl) ⟨299589, by rfl⟩ : syracuseStep 798905 = 599179) B599179
theorem B372923 : Blo 370760 372923 := bstep (se 1 (by rfl) ⟨279692, by rfl⟩ : syracuseStep 372923 = 559385) B559385
theorem B372999 : Blo 370760 372999 := bstep (se 1 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 372999 = 559499) B559499
theorem B373007 : Blo 370760 373007 := bstep (se 1 (by rfl) ⟨279755, by rfl⟩ : syracuseStep 373007 = 559511) B559511
theorem B373051 : Blo 370760 373051 := bstep (se 1 (by rfl) ⟨279788, by rfl⟩ : syracuseStep 373051 = 559577) B559577
theorem B471415 : Blo 370760 471415 := bstep (se 1 (by rfl) ⟨353561, by rfl⟩ : syracuseStep 471415 = 707123) B707123
theorem B2044295 : Blo 370760 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B373127 : Blo 370760 373127 := bstep (se 1 (by rfl) ⟨279845, by rfl⟩ : syracuseStep 373127 = 559691) B559691
theorem B373135 : Blo 370760 373135 := bstep (se 1 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 373135 = 559703) B559703
theorem B1257875 : Blo 370760 1257875 := bstep (se 1 (by rfl) ⟨943406, by rfl⟩ : syracuseStep 1257875 = 1886813) B1886813
theorem B373179 : Blo 370760 373179 := bstep (se 1 (by rfl) ⟨279884, by rfl⟩ : syracuseStep 373179 = 559769) B559769
theorem B373255 : Blo 370760 373255 := bstep (se 1 (by rfl) ⟨279941, by rfl⟩ : syracuseStep 373255 = 559883) B559883
theorem B373263 : Blo 370760 373263 := bstep (se 1 (by rfl) ⟨279947, by rfl⟩ : syracuseStep 373263 = 559895) B559895
theorem B799247 : Blo 370760 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B373307 : Blo 370760 373307 := bstep (se 1 (by rfl) ⟨279980, by rfl⟩ : syracuseStep 373307 = 559961) B559961
theorem B373383 : Blo 370760 373383 := bstep (se 1 (by rfl) ⟨280037, by rfl⟩ : syracuseStep 373383 = 560075) B560075
theorem B373391 : Blo 370760 373391 := bstep (se 1 (by rfl) ⟨280043, by rfl⟩ : syracuseStep 373391 = 560087) B560087
theorem B1061561 : Blo 370760 1061561 := bstep (se 2 (by rfl) ⟨398085, by rfl⟩ : syracuseStep 1061561 = 796171) B796171
theorem B799417 : Blo 370760 799417 := bstep (se 2 (by rfl) ⟨299781, by rfl⟩ : syracuseStep 799417 = 599563) B599563
theorem B471739 : Blo 370760 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B373435 : Blo 370760 373435 := bstep (se 1 (by rfl) ⟨280076, by rfl⟩ : syracuseStep 373435 = 560153) B560153
theorem B373511 : Blo 370760 373511 := bstep (se 1 (by rfl) ⟨280133, by rfl⟩ : syracuseStep 373511 = 560267) B560267
theorem B373519 : Blo 370760 373519 := bstep (se 1 (by rfl) ⟨280139, by rfl⟩ : syracuseStep 373519 = 560279) B560279
theorem B373563 : Blo 370760 373563 := bstep (se 1 (by rfl) ⟨280172, by rfl⟩ : syracuseStep 373563 = 560345) B560345
theorem B373639 : Blo 370760 373639 := bstep (se 1 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 373639 = 560459) B560459
theorem B373647 : Blo 370760 373647 := bstep (se 1 (by rfl) ⟨280235, by rfl⟩ : syracuseStep 373647 = 560471) B560471
theorem B373691 : Blo 370760 373691 := bstep (se 1 (by rfl) ⟨280268, by rfl⟩ : syracuseStep 373691 = 560537) B560537
theorem B373767 : Blo 370760 373767 := bstep (se 1 (by rfl) ⟨280325, by rfl⟩ : syracuseStep 373767 = 560651) B560651
theorem B1061903 : Blo 370760 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B373775 : Blo 370760 373775 := bstep (se 1 (by rfl) ⟨280331, by rfl⟩ : syracuseStep 373775 = 560663) B560663
theorem B373819 : Blo 370760 373819 := bstep (se 1 (by rfl) ⟨280364, by rfl⟩ : syracuseStep 373819 = 560729) B560729
theorem B1586243 : Blo 370760 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B373895 : Blo 370760 373895 := bstep (se 1 (by rfl) ⟨280421, by rfl⟩ : syracuseStep 373895 = 560843) B560843
theorem B373903 : Blo 370760 373903 := bstep (se 1 (by rfl) ⟨280427, by rfl⟩ : syracuseStep 373903 = 560855) B560855
theorem B373947 : Blo 370760 373947 := bstep (se 1 (by rfl) ⟨280460, by rfl⟩ : syracuseStep 373947 = 560921) B560921
theorem B668873 : Blo 370760 668873 := bstep (se 2 (by rfl) ⟨250827, by rfl⟩ : syracuseStep 668873 = 501655) B501655
theorem B374023 : Blo 370760 374023 := bstep (se 1 (by rfl) ⟨280517, by rfl⟩ : syracuseStep 374023 = 561035) B561035
theorem B1193231 : Blo 370760 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B374031 : Blo 370760 374031 := bstep (se 1 (by rfl) ⟨280523, by rfl⟩ : syracuseStep 374031 = 561047) B561047
theorem B1586465 : Blo 370760 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B374075 : Blo 370760 374075 := bstep (se 1 (by rfl) ⟨280556, by rfl⟩ : syracuseStep 374075 = 561113) B561113
theorem B1586567 : Blo 370760 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B374151 : Blo 370760 374151 := bstep (se 1 (by rfl) ⟨280613, by rfl⟩ : syracuseStep 374151 = 561227) B561227
theorem B800135 : Blo 370760 800135 := bstep (se 1 (by rfl) ⟨600101, by rfl⟩ : syracuseStep 800135 = 1200203) B1200203
theorem B374159 : Blo 370760 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B374203 : Blo 370760 374203 := bstep (se 1 (by rfl) ⟨280652, by rfl⟩ : syracuseStep 374203 = 561305) B561305
theorem B3225091 : Blo 370760 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B374279 : Blo 370760 374279 := bstep (se 1 (by rfl) ⟨280709, by rfl⟩ : syracuseStep 374279 = 561419) B561419
theorem B374287 : Blo 370760 374287 := bstep (se 1 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 374287 = 561431) B561431
theorem B1881629 : Blo 370760 1881629 := bstep (se 3 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 1881629 = 705611) B705611
theorem B1095227 : Blo 370760 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B374331 : Blo 370760 374331 := bstep (se 1 (by rfl) ⟨280748, by rfl⟩ : syracuseStep 374331 = 561497) B561497
theorem B472711 : Blo 370760 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B374407 : Blo 370760 374407 := bstep (se 1 (by rfl) ⟨280805, by rfl⟩ : syracuseStep 374407 = 561611) B561611
theorem B374415 : Blo 370760 374415 := bstep (se 1 (by rfl) ⟨280811, by rfl⟩ : syracuseStep 374415 = 561623) B561623
theorem B374459 : Blo 370760 374459 := bstep (se 1 (by rfl) ⟨280844, by rfl⟩ : syracuseStep 374459 = 561689) B561689
theorem B374535 : Blo 370760 374535 := bstep (se 1 (by rfl) ⟨280901, by rfl⟩ : syracuseStep 374535 = 561803) B561803
theorem B1259279 : Blo 370760 1259279 := bstep (se 1 (by rfl) ⟨944459, by rfl⟩ : syracuseStep 1259279 = 1888919) B1888919
theorem B374543 : Blo 370760 374543 := bstep (se 1 (by rfl) ⟨280907, by rfl⟩ : syracuseStep 374543 = 561815) B561815
theorem B374587 : Blo 370760 374587 := bstep (se 1 (by rfl) ⟨280940, by rfl⟩ : syracuseStep 374587 = 561881) B561881
theorem B1062791 : Blo 370760 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B374663 : Blo 370760 374663 := bstep (se 1 (by rfl) ⟨280997, by rfl⟩ : syracuseStep 374663 = 561995) B561995
theorem B374671 : Blo 370760 374671 := bstep (se 1 (by rfl) ⟨281003, by rfl⟩ : syracuseStep 374671 = 562007) B562007
theorem B538555 : Blo 370760 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B374715 : Blo 370760 374715 := bstep (se 1 (by rfl) ⟨281036, by rfl⟩ : syracuseStep 374715 = 562073) B562073
theorem B1882115 : Blo 370760 1882115 := bstep (se 1 (by rfl) ⟨1411586, by rfl⟩ : syracuseStep 1882115 = 2823173) B2823173
theorem B2832407 : Blo 370760 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B1259549 : Blo 370760 1259549 := bstep (se 3 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 1259549 = 472331) B472331
theorem B473131 : Blo 370760 473131 := bstep (se 1 (by rfl) ⟨354848, by rfl⟩ : syracuseStep 473131 = 709697) B709697
theorem B571451 : Blo 370760 571451 := bstep (se 1 (by rfl) ⟨428588, by rfl⟩ : syracuseStep 571451 = 857177) B857177
theorem B1062973 : Blo 370760 1062973 := bstep (se 3 (by rfl) ⟨199307, by rfl⟩ : syracuseStep 1062973 = 398615) B398615
theorem B899191 : Blo 370760 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B473359 : Blo 370760 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B2111777 : Blo 370760 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B1063201 : Blo 370760 1063201 := bstep (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) B797401
theorem B1915271 : Blo 370760 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B1784387 : Blo 370760 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B1063543 : Blo 370760 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B474103 : Blo 370760 474103 := bstep (se 1 (by rfl) ⟨355577, by rfl⟩ : syracuseStep 474103 = 711155) B711155
theorem B539767 : Blo 370760 539767 := bstep (se 1 (by rfl) ⟨404825, by rfl⟩ : syracuseStep 539767 = 809651) B809651
theorem B834695 : Blo 370760 834695 := bstep (se 1 (by rfl) ⟨626021, by rfl⟩ : syracuseStep 834695 = 1252043) B1252043
theorem B1588481 : Blo 370760 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B7257377 : Blo 370760 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B834875 : Blo 370760 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B1260953 : Blo 370760 1260953 := bstep (se 2 (by rfl) ⟨472857, by rfl⟩ : syracuseStep 1260953 = 945715) B945715
theorem B835001 : Blo 370760 835001 := bstep (se 2 (by rfl) ⟨313125, by rfl⟩ : syracuseStep 835001 = 626251) B626251
theorem B1064477 : Blo 370760 1064477 := bstep (se 3 (by rfl) ⟨199589, by rfl⟩ : syracuseStep 1064477 = 399179) B399179
theorem B1883735 : Blo 370760 1883735 := bstep (se 1 (by rfl) ⟨1412801, by rfl⟩ : syracuseStep 1883735 = 2825603) B2825603
theorem B835343 : Blo 370760 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B835361 : Blo 370760 835361 := bstep (se 2 (by rfl) ⟨313260, by rfl⟩ : syracuseStep 835361 = 626521) B626521
theorem B638779 : Blo 370760 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B1064819 : Blo 370760 1064819 := bstep (se 1 (by rfl) ⟨798614, by rfl⟩ : syracuseStep 1064819 = 1597229) B1597229
theorem B8306705 : Blo 370760 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1884221 : Blo 370760 1884221 := bstep (se 3 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 1884221 = 706583) B706583
theorem B1261655 : Blo 370760 1261655 := bstep (se 1 (by rfl) ⟨946241, by rfl⟩ : syracuseStep 1261655 = 1892483) B1892483
theorem B835703 : Blo 370760 835703 := bstep (se 1 (by rfl) ⟨626777, by rfl⟩ : syracuseStep 835703 = 1253555) B1253555
theorem B835883 : Blo 370760 835883 := bstep (se 1 (by rfl) ⟨626912, by rfl⟩ : syracuseStep 835883 = 1253825) B1253825
theorem B672059 : Blo 370760 672059 := bstep (se 1 (by rfl) ⟨504044, by rfl⟩ : syracuseStep 672059 = 1008089) B1008089
theorem B1065275 : Blo 370760 1065275 := bstep (se 1 (by rfl) ⟨798956, by rfl⟩ : syracuseStep 1065275 = 1597913) B1597913
theorem B2474387 : Blo 370760 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B3392003 : Blo 370760 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B1262141 : Blo 370760 1262141 := bstep (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) B473303
theorem B2867831 : Blo 370760 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B836243 : Blo 370760 836243 := bstep (se 1 (by rfl) ⟨627182, by rfl⟩ : syracuseStep 836243 = 1254365) B1254365
theorem B836297 : Blo 370760 836297 := bstep (se 2 (by rfl) ⟨313611, by rfl⟩ : syracuseStep 836297 = 627223) B627223
theorem B705323 : Blo 370760 705323 := bstep (se 1 (by rfl) ⟨528992, by rfl⟩ : syracuseStep 705323 = 1057985) B1057985
theorem B2016089 : Blo 370760 2016089 := bstep (se 2 (by rfl) ⟨756033, by rfl⟩ : syracuseStep 2016089 = 1512067) B1512067
theorem B1819691 : Blo 370760 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B836999 : Blo 370760 836999 := bstep (se 1 (by rfl) ⟨627749, by rfl⟩ : syracuseStep 836999 = 1255499) B1255499
theorem B4015565 : Blo 370760 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B837179 : Blo 370760 837179 := bstep (se 1 (by rfl) ⟨627884, by rfl⟩ : syracuseStep 837179 = 1255769) B1255769
theorem B1918637 : Blo 370760 1918637 := bstep (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) B719489
theorem B837305 : Blo 370760 837305 := bstep (se 2 (by rfl) ⟨313989, by rfl⟩ : syracuseStep 837305 = 627979) B627979
theorem B706249 : Blo 370760 706249 := bstep (se 2 (by rfl) ⟨264843, by rfl⟩ : syracuseStep 706249 = 529687) B529687
theorem B673579 : Blo 370760 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B1886003 : Blo 370760 1886003 := bstep (se 1 (by rfl) ⟨1414502, by rfl⟩ : syracuseStep 1886003 = 2829005) B2829005
theorem B1263545 : Blo 370760 1263545 := bstep (se 2 (by rfl) ⟨473829, by rfl⟩ : syracuseStep 1263545 = 947659) B947659
theorem B837647 : Blo 370760 837647 := bstep (se 1 (by rfl) ⟨628235, by rfl⟩ : syracuseStep 837647 = 1256471) B1256471
theorem B837665 : Blo 370760 837665 := bstep (se 2 (by rfl) ⟨314124, by rfl⟩ : syracuseStep 837665 = 628249) B628249
theorem B1886327 : Blo 370760 1886327 := bstep (se 1 (by rfl) ⟨1414745, by rfl⟩ : syracuseStep 1886327 = 2829491) B2829491
theorem B838007 : Blo 370760 838007 := bstep (se 1 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 838007 = 1257011) B1257011
theorem B706963 : Blo 370760 706963 := bstep (se 1 (by rfl) ⟨530222, by rfl⟩ : syracuseStep 706963 = 1060445) B1060445
theorem B1264139 : Blo 370760 1264139 := bstep (se 1 (by rfl) ⟨948104, by rfl⟩ : syracuseStep 1264139 = 1896209) B1896209
theorem B838187 : Blo 370760 838187 := bstep (se 1 (by rfl) ⟨628640, by rfl⟩ : syracuseStep 838187 = 1257281) B1257281
theorem B1264247 : Blo 370760 1264247 := bstep (se 1 (by rfl) ⟨948185, by rfl⟩ : syracuseStep 1264247 = 1896371) B1896371
theorem B1788617 : Blo 370760 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B838547 : Blo 370760 838547 := bstep (se 1 (by rfl) ⟨628910, by rfl⟩ : syracuseStep 838547 = 1257821) B1257821
theorem B838601 : Blo 370760 838601 := bstep (se 2 (by rfl) ⟨314475, by rfl⟩ : syracuseStep 838601 = 628951) B628951
theorem B1592273 : Blo 370760 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B14797835 : Blo 370760 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B1428509 : Blo 370760 1428509 := bstep (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) B535691
theorem B2116651 : Blo 370760 2116651 := bstep (se 1 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 2116651 = 3174977) B3174977
theorem B1887299 : Blo 370760 1887299 := bstep (se 1 (by rfl) ⟨1415474, by rfl⟩ : syracuseStep 1887299 = 2830949) B2830949
theorem B871723 : Blo 370760 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B1887623 : Blo 370760 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B708041 : Blo 370760 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B839303 : Blo 370760 839303 := bstep (se 1 (by rfl) ⟨629477, by rfl⟩ : syracuseStep 839303 = 1258955) B1258955
theorem B839483 : Blo 370760 839483 := bstep (se 1 (by rfl) ⟨629612, by rfl⟩ : syracuseStep 839483 = 1259225) B1259225
theorem B6377291 : Blo 370760 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B839609 : Blo 370760 839609 := bstep (se 2 (by rfl) ⟨314853, by rfl⟩ : syracuseStep 839609 = 629707) B629707
theorem B16175051 : Blo 370760 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B6475949 : Blo 370760 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B839951 : Blo 370760 839951 := bstep (se 1 (by rfl) ⟨629963, by rfl⟩ : syracuseStep 839951 = 1259927) B1259927
theorem B839969 : Blo 370760 839969 := bstep (se 2 (by rfl) ⟨314988, by rfl⟩ : syracuseStep 839969 = 629977) B629977
theorem B708907 : Blo 370760 708907 := bstep (se 1 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 708907 = 1063361) B1063361
theorem B708983 : Blo 370760 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B1921427 : Blo 370760 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B2118109 : Blo 370760 2118109 := bstep (se 3 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 2118109 = 794291) B794291
theorem B840311 : Blo 370760 840311 := bstep (se 1 (by rfl) ⟨630233, by rfl⟩ : syracuseStep 840311 = 1260467) B1260467
theorem B2544385 : Blo 370760 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B840491 : Blo 370760 840491 := bstep (se 1 (by rfl) ⟨630368, by rfl⟩ : syracuseStep 840491 = 1260737) B1260737
theorem B1299347 : Blo 370760 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B939023 : Blo 370760 939023 := bstep (se 1 (by rfl) ⟨704267, by rfl⟩ : syracuseStep 939023 = 1408535) B1408535
theorem B2380823 : Blo 370760 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B840851 : Blo 370760 840851 := bstep (se 1 (by rfl) ⟨630638, by rfl⟩ : syracuseStep 840851 = 1261277) B1261277
theorem B840905 : Blo 370760 840905 := bstep (se 2 (by rfl) ⟨315339, by rfl⟩ : syracuseStep 840905 = 630679) B630679
theorem B1004833 : Blo 370760 1004833 := bstep (se 2 (by rfl) ⟨376812, by rfl⟩ : syracuseStep 1004833 = 753625) B753625
theorem B1004843 : Blo 370760 1004843 := bstep (se 1 (by rfl) ⟨753632, by rfl⟩ : syracuseStep 1004843 = 1507265) B1507265
theorem B2840183 : Blo 370760 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B939721 : Blo 370760 939721 := bstep (se 2 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 939721 = 704791) B704791
theorem B939863 : Blo 370760 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B841607 : Blo 370760 841607 := bstep (se 1 (by rfl) ⟨631205, by rfl⟩ : syracuseStep 841607 = 1262411) B1262411
theorem B841787 : Blo 370760 841787 := bstep (se 1 (by rfl) ⟨631340, by rfl⟩ : syracuseStep 841787 = 1262681) B1262681
theorem B841913 : Blo 370760 841913 := bstep (se 2 (by rfl) ⟨315717, by rfl⟩ : syracuseStep 841913 = 631435) B631435
theorem B710927 : Blo 370760 710927 := bstep (se 1 (by rfl) ⟨533195, by rfl⟩ : syracuseStep 710927 = 1066391) B1066391
theorem B1792307 : Blo 370760 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B842255 : Blo 370760 842255 := bstep (se 1 (by rfl) ⟨631691, by rfl⟩ : syracuseStep 842255 = 1263383) B1263383
theorem B842273 : Blo 370760 842273 := bstep (se 2 (by rfl) ⟨315852, by rfl⟩ : syracuseStep 842273 = 631705) B631705
theorem B2841155 : Blo 370760 2841155 := bstep (se 1 (by rfl) ⟨2130866, by rfl⟩ : syracuseStep 2841155 = 4261733) B4261733
theorem B1891187 : Blo 370760 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B7199603 : Blo 370760 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B842615 : Blo 370760 842615 := bstep (se 1 (by rfl) ⟨631961, by rfl⟩ : syracuseStep 842615 = 1263923) B1263923
theorem B842795 : Blo 370760 842795 := bstep (se 1 (by rfl) ⟨632096, by rfl⟩ : syracuseStep 842795 = 1264193) B1264193
theorem B7625933 : Blo 370760 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B1891673 : Blo 370760 1891673 := bstep (se 2 (by rfl) ⟨709377, by rfl⟩ : syracuseStep 1891673 = 1418755) B1418755
theorem B843155 : Blo 370760 843155 := bstep (se 1 (by rfl) ⟨632366, by rfl⟩ : syracuseStep 843155 = 1264733) B1264733
theorem B843209 : Blo 370760 843209 := bstep (se 2 (by rfl) ⟨316203, by rfl⟩ : syracuseStep 843209 = 632407) B632407
theorem B1793501 : Blo 370760 1793501 := bstep (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) B672563
theorem B679439 : Blo 370760 679439 := bstep (se 1 (by rfl) ⟨509579, by rfl⟩ : syracuseStep 679439 = 1019159) B1019159
theorem B2711069 : Blo 370760 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B1596989 : Blo 370760 1596989 := bstep (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) B598871
theorem B417415 : Blo 370760 417415 := bstep (se 1 (by rfl) ⟨313061, by rfl⟩ : syracuseStep 417415 = 626123) B626123
theorem B417595 : Blo 370760 417595 := bstep (se 1 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 417595 = 626393) B626393
theorem B941939 : Blo 370760 941939 := bstep (se 1 (by rfl) ⟨706454, by rfl⟩ : syracuseStep 941939 = 1412909) B1412909
theorem B3596147 : Blo 370760 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B1794059 : Blo 370760 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B27091037 : Blo 370760 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B418063 : Blo 370760 418063 := bstep (se 1 (by rfl) ⟨313547, by rfl⟩ : syracuseStep 418063 = 627095) B627095
theorem B942455 : Blo 370760 942455 := bstep (se 1 (by rfl) ⟨706841, by rfl⟩ : syracuseStep 942455 = 1413683) B1413683
theorem B2122301 : Blo 370760 2122301 := bstep (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) B795863
theorem B418567 : Blo 370760 418567 := bstep (se 1 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 418567 = 627851) B627851
theorem B1008413 : Blo 370760 1008413 := bstep (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) B378155
theorem B418747 : Blo 370760 418747 := bstep (se 1 (by rfl) ⟨314060, by rfl⟩ : syracuseStep 418747 = 628121) B628121
theorem B910369 : Blo 370760 910369 := bstep (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) B682777
theorem B8610947 : Blo 370760 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B2123009 : Blo 370760 2123009 := bstep (se 2 (by rfl) ⟨796128, by rfl⟩ : syracuseStep 2123009 = 1592257) B1592257
theorem B1336591 : Blo 370760 1336591 := bstep (se 1 (by rfl) ⟨1002443, by rfl⟩ : syracuseStep 1336591 = 2004887) B2004887
theorem B943447 : Blo 370760 943447 := bstep (se 1 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 943447 = 1415171) B1415171
theorem B3564931 : Blo 370760 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B419215 : Blo 370760 419215 := bstep (se 1 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 419215 = 628823) B628823
theorem B1893779 : Blo 370760 1893779 := bstep (se 1 (by rfl) ⟨1420334, by rfl⟩ : syracuseStep 1893779 = 2840669) B2840669
theorem B6055523 : Blo 370760 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B943751 : Blo 370760 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B943883 : Blo 370760 943883 := bstep (se 1 (by rfl) ⟨707912, by rfl⟩ : syracuseStep 943883 = 1415825) B1415825
theorem B419719 : Blo 370760 419719 := bstep (se 1 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 419719 = 629579) B629579
theorem B4646807 : Blo 370760 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B1599517 : Blo 370760 1599517 := bstep (se 3 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 1599517 = 599819) B599819
theorem B419899 : Blo 370760 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B10152053 : Blo 370760 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B6514805 : Blo 370760 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B845959 : Blo 370760 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B1697993 : Blo 370760 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B1599689 : Blo 370760 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B944399 : Blo 370760 944399 := bstep (se 1 (by rfl) ⟨708299, by rfl⟩ : syracuseStep 944399 = 1416599) B1416599
theorem B944531 : Blo 370760 944531 := bstep (se 1 (by rfl) ⟨708398, by rfl⟩ : syracuseStep 944531 = 1416797) B1416797
theorem B3860995 : Blo 370760 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B420367 : Blo 370760 420367 := bstep (se 1 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 420367 = 630551) B630551
theorem B2255447 : Blo 370760 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B10742543 : Blo 370760 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B912161 : Blo 370760 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B2845529 : Blo 370760 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B420871 : Blo 370760 420871 := bstep (se 1 (by rfl) ⟨315653, by rfl⟩ : syracuseStep 420871 = 631307) B631307
theorem B2714797 : Blo 370760 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B421051 : Blo 370760 421051 := bstep (se 1 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 421051 = 631577) B631577
theorem B945665 : Blo 370760 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B2125399 : Blo 370760 2125399 := bstep (se 1 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 2125399 = 3188099) B3188099
theorem B421519 : Blo 370760 421519 := bstep (se 1 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 421519 = 632279) B632279
theorem B1797805 : Blo 370760 1797805 := bstep (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) B674177
theorem B946039 : Blo 370760 946039 := bstep (se 1 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 946039 = 1419059) B1419059
theorem B716833 : Blo 370760 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B946475 : Blo 370760 946475 := bstep (se 1 (by rfl) ⟨709856, by rfl⟩ : syracuseStep 946475 = 1419713) B1419713
theorem B1896857 : Blo 370760 1896857 := bstep (se 2 (by rfl) ⟨711321, by rfl⟩ : syracuseStep 1896857 = 1422643) B1422643
theorem B848585 : Blo 370760 848585 := bstep (se 2 (by rfl) ⟨318219, by rfl⟩ : syracuseStep 848585 = 636439) B636439
theorem B5731033 : Blo 370760 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B3011417 : Blo 370760 3011417 := bstep (se 2 (by rfl) ⟨1129281, by rfl⟩ : syracuseStep 3011417 = 2258563) B2258563
theorem B848825 : Blo 370760 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B947315 : Blo 370760 947315 := bstep (se 1 (by rfl) ⟨710486, by rfl⟩ : syracuseStep 947315 = 1420973) B1420973
theorem B9172099 : Blo 370760 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B947335 : Blo 370760 947335 := bstep (se 1 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 947335 = 1421003) B1421003
theorem B947609 : Blo 370760 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B2127383 : Blo 370760 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B947771 : Blo 370760 947771 := bstep (se 1 (by rfl) ⟨710828, by rfl⟩ : syracuseStep 947771 = 1421657) B1421657
theorem B947983 : Blo 370760 947983 := bstep (se 1 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 947983 = 1421975) B1421975
theorem B948257 : Blo 370760 948257 := bstep (se 2 (by rfl) ⟨355596, by rfl⟩ : syracuseStep 948257 = 711193) B711193
theorem B719119 : Blo 370760 719119 := bstep (se 1 (by rfl) ⟨539339, by rfl⟩ : syracuseStep 719119 = 1078679) B1078679
theorem B6355421 : Blo 370760 6355421 := bstep (se 3 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 6355421 = 2383283) B2383283
theorem B3570277 : Blo 370760 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B981623 : Blo 370760 981623 := bstep (se 1 (by rfl) ⟨736217, by rfl⟩ : syracuseStep 981623 = 1472435) B1472435
theorem B10222199 : Blo 370760 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B6454333 : Blo 370760 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B556151 : Blo 370760 556151 := bstep (se 1 (by rfl) ⟨417113, by rfl⟩ : syracuseStep 556151 = 834227) B834227
theorem B556175 : Blo 370760 556175 := bstep (se 1 (by rfl) ⟨417131, by rfl⟩ : syracuseStep 556175 = 834263) B834263
theorem B556217 : Blo 370760 556217 := bstep (se 2 (by rfl) ⟨208581, by rfl⟩ : syracuseStep 556217 = 417163) B417163
theorem B556295 : Blo 370760 556295 := bstep (se 1 (by rfl) ⟨417221, by rfl⟩ : syracuseStep 556295 = 834443) B834443
theorem B556331 : Blo 370760 556331 := bstep (se 1 (by rfl) ⟨417248, by rfl⟩ : syracuseStep 556331 = 834497) B834497
theorem B556361 : Blo 370760 556361 := bstep (se 2 (by rfl) ⟨208635, by rfl⟩ : syracuseStep 556361 = 417271) B417271
theorem B4521401 : Blo 370760 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B556475 : Blo 370760 556475 := bstep (se 1 (by rfl) ⟨417356, by rfl⟩ : syracuseStep 556475 = 834713) B834713
theorem B556535 : Blo 370760 556535 := bstep (se 1 (by rfl) ⟨417401, by rfl⟩ : syracuseStep 556535 = 834803) B834803
theorem B556559 : Blo 370760 556559 := bstep (se 1 (by rfl) ⟨417419, by rfl⟩ : syracuseStep 556559 = 834839) B834839
theorem B556601 : Blo 370760 556601 := bstep (se 2 (by rfl) ⟨208725, by rfl⟩ : syracuseStep 556601 = 417451) B417451
theorem B556679 : Blo 370760 556679 := bstep (se 1 (by rfl) ⟨417509, by rfl⟩ : syracuseStep 556679 = 835019) B835019
theorem B556715 : Blo 370760 556715 := bstep (se 1 (by rfl) ⟨417536, by rfl⟩ : syracuseStep 556715 = 835073) B835073
theorem B556745 : Blo 370760 556745 := bstep (se 2 (by rfl) ⟨208779, by rfl⟩ : syracuseStep 556745 = 417559) B417559
theorem B556859 : Blo 370760 556859 := bstep (se 1 (by rfl) ⟨417644, by rfl⟩ : syracuseStep 556859 = 835289) B835289
theorem B556919 : Blo 370760 556919 := bstep (se 1 (by rfl) ⟨417689, by rfl⟩ : syracuseStep 556919 = 835379) B835379
theorem B556943 : Blo 370760 556943 := bstep (se 1 (by rfl) ⟨417707, by rfl⟩ : syracuseStep 556943 = 835415) B835415
theorem B556985 : Blo 370760 556985 := bstep (se 2 (by rfl) ⟨208869, by rfl⟩ : syracuseStep 556985 = 417739) B417739
theorem B5537803 : Blo 370760 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B557135 : Blo 370760 557135 := bstep (se 1 (by rfl) ⟨417851, by rfl⟩ : syracuseStep 557135 = 835703) B835703
theorem B557255 : Blo 370760 557255 := bstep (se 1 (by rfl) ⟨417941, by rfl⟩ : syracuseStep 557255 = 835883) B835883
theorem B557417 : Blo 370760 557417 := bstep (se 2 (by rfl) ⟨209031, by rfl⟩ : syracuseStep 557417 = 418063) B418063
theorem B557495 : Blo 370760 557495 := bstep (se 1 (by rfl) ⟨418121, by rfl⟩ : syracuseStep 557495 = 836243) B836243
theorem B557531 : Blo 370760 557531 := bstep (se 1 (by rfl) ⟨418148, by rfl⟩ : syracuseStep 557531 = 836297) B836297
theorem B1344059 : Blo 370760 1344059 := bstep (se 1 (by rfl) ⟨1008044, by rfl⟩ : syracuseStep 1344059 = 2016089) B2016089
theorem B6095477 : Blo 370760 6095477 := bstep (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) B571451
theorem B1213127 : Blo 370760 1213127 := bstep (se 1 (by rfl) ⟨909845, by rfl⟩ : syracuseStep 1213127 = 1819691) B1819691
theorem B557999 : Blo 370760 557999 := bstep (se 1 (by rfl) ⟨418499, by rfl⟩ : syracuseStep 557999 = 836999) B836999
theorem B558089 : Blo 370760 558089 := bstep (se 2 (by rfl) ⟨209283, by rfl⟩ : syracuseStep 558089 = 418567) B418567
theorem B558119 : Blo 370760 558119 := bstep (se 1 (by rfl) ⟨418589, by rfl⟩ : syracuseStep 558119 = 837179) B837179
theorem B15205427 : Blo 370760 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1279091 : Blo 370760 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B558203 : Blo 370760 558203 := bstep (se 1 (by rfl) ⟨418652, by rfl⟩ : syracuseStep 558203 = 837305) B837305
theorem B558329 : Blo 370760 558329 := bstep (se 2 (by rfl) ⟨209373, by rfl⟩ : syracuseStep 558329 = 418747) B418747
theorem B9045341 : Blo 370760 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B558431 : Blo 370760 558431 := bstep (se 1 (by rfl) ⟨418823, by rfl⟩ : syracuseStep 558431 = 837647) B837647
theorem B558443 : Blo 370760 558443 := bstep (se 1 (by rfl) ⟨418832, by rfl⟩ : syracuseStep 558443 = 837665) B837665
theorem B558671 : Blo 370760 558671 := bstep (se 1 (by rfl) ⟨419003, by rfl⟩ : syracuseStep 558671 = 838007) B838007
theorem B558791 : Blo 370760 558791 := bstep (se 1 (by rfl) ⟨419093, by rfl⟩ : syracuseStep 558791 = 838187) B838187
theorem B4753241 : Blo 370760 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B558953 : Blo 370760 558953 := bstep (se 2 (by rfl) ⟨209607, by rfl⟩ : syracuseStep 558953 = 419215) B419215
theorem B559031 : Blo 370760 559031 := bstep (se 1 (by rfl) ⟨419273, by rfl⟩ : syracuseStep 559031 = 838547) B838547
theorem B559067 : Blo 370760 559067 := bstep (se 1 (by rfl) ⟨419300, by rfl⟩ : syracuseStep 559067 = 838601) B838601
theorem B9865223 : Blo 370760 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B952339 : Blo 370760 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B559535 : Blo 370760 559535 := bstep (se 1 (by rfl) ⟨419651, by rfl⟩ : syracuseStep 559535 = 839303) B839303
theorem B559625 : Blo 370760 559625 := bstep (se 2 (by rfl) ⟨209859, by rfl⟩ : syracuseStep 559625 = 419719) B419719
theorem B559655 : Blo 370760 559655 := bstep (se 1 (by rfl) ⟨419741, by rfl⟩ : syracuseStep 559655 = 839483) B839483
theorem B559739 : Blo 370760 559739 := bstep (se 1 (by rfl) ⟨419804, by rfl⟩ : syracuseStep 559739 = 839609) B839609
theorem B2820743 : Blo 370760 2820743 := bstep (se 1 (by rfl) ⟨2115557, by rfl⟩ : syracuseStep 2820743 = 4231115) B4231115
theorem B10783367 : Blo 370760 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B1411769 : Blo 370760 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B2132689 : Blo 370760 2132689 := bstep (se 2 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 2132689 = 1599517) B1599517
theorem B559865 : Blo 370760 559865 := bstep (se 2 (by rfl) ⟨209949, by rfl⟩ : syracuseStep 559865 = 419899) B419899
theorem B4295501 : Blo 370760 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B559967 : Blo 370760 559967 := bstep (se 1 (by rfl) ⟨419975, by rfl⟩ : syracuseStep 559967 = 839951) B839951
theorem B559979 : Blo 370760 559979 := bstep (se 1 (by rfl) ⟨419984, by rfl⟩ : syracuseStep 559979 = 839969) B839969
theorem B1280951 : Blo 370760 1280951 := bstep (se 1 (by rfl) ⟨960713, by rfl⟩ : syracuseStep 1280951 = 1921427) B1921427
theorem B5377103 : Blo 370760 5377103 := bstep (se 1 (by rfl) ⟨4032827, by rfl⟩ : syracuseStep 5377103 = 8065655) B8065655
theorem B560207 : Blo 370760 560207 := bstep (se 1 (by rfl) ⟨420155, by rfl⟩ : syracuseStep 560207 = 840311) B840311
theorem B560327 : Blo 370760 560327 := bstep (se 1 (by rfl) ⟨420245, by rfl⟩ : syracuseStep 560327 = 840491) B840491
theorem B4263191 : Blo 370760 4263191 := bstep (se 1 (by rfl) ⟨3197393, by rfl⟩ : syracuseStep 4263191 = 6394787) B6394787
theorem B5147993 : Blo 370760 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B626015 : Blo 370760 626015 := bstep (se 1 (by rfl) ⟨469511, by rfl⟩ : syracuseStep 626015 = 939023) B939023
theorem B560489 : Blo 370760 560489 := bstep (se 2 (by rfl) ⟨210183, by rfl⟩ : syracuseStep 560489 = 420367) B420367
theorem B3181949 : Blo 370760 3181949 := bstep (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) B1193231
theorem B560567 : Blo 370760 560567 := bstep (se 1 (by rfl) ⟨420425, by rfl⟩ : syracuseStep 560567 = 840851) B840851
theorem B560603 : Blo 370760 560603 := bstep (se 1 (by rfl) ⟨420452, by rfl⟩ : syracuseStep 560603 = 840905) B840905
theorem B626575 : Blo 370760 626575 := bstep (se 1 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 626575 = 939863) B939863
theorem B561071 : Blo 370760 561071 := bstep (se 1 (by rfl) ⟨420803, by rfl⟩ : syracuseStep 561071 = 841607) B841607
theorem B561161 : Blo 370760 561161 := bstep (se 2 (by rfl) ⟨210435, by rfl⟩ : syracuseStep 561161 = 420871) B420871
theorem B561191 : Blo 370760 561191 := bstep (se 1 (by rfl) ⟨420893, by rfl⟩ : syracuseStep 561191 = 841787) B841787
theorem B2822201 : Blo 370760 2822201 := bstep (se 2 (by rfl) ⟨1058325, by rfl⟩ : syracuseStep 2822201 = 2116651) B2116651
theorem B561275 : Blo 370760 561275 := bstep (se 1 (by rfl) ⟨420956, by rfl⟩ : syracuseStep 561275 = 841913) B841913
theorem B561401 : Blo 370760 561401 := bstep (se 2 (by rfl) ⟨210525, by rfl⟩ : syracuseStep 561401 = 421051) B421051
theorem B1511741 : Blo 370760 1511741 := bstep (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) B566903
theorem B561503 : Blo 370760 561503 := bstep (se 1 (by rfl) ⟨421127, by rfl⟩ : syracuseStep 561503 = 842255) B842255
theorem B561515 : Blo 370760 561515 := bstep (se 1 (by rfl) ⟨421136, by rfl⟩ : syracuseStep 561515 = 842273) B842273
theorem B528935 : Blo 370760 528935 := bstep (se 1 (by rfl) ⟨396701, by rfl⟩ : syracuseStep 528935 = 793403) B793403
theorem B627257 : Blo 370760 627257 := bstep (se 2 (by rfl) ⟨235221, by rfl⟩ : syracuseStep 627257 = 470443) B470443
theorem B561743 : Blo 370760 561743 := bstep (se 1 (by rfl) ⟨421307, by rfl⟩ : syracuseStep 561743 = 842615) B842615
theorem B561863 : Blo 370760 561863 := bstep (se 1 (by rfl) ⟨421397, by rfl⟩ : syracuseStep 561863 = 842795) B842795
theorem B1413881 : Blo 370760 1413881 := bstep (se 2 (by rfl) ⟨530205, by rfl⟩ : syracuseStep 1413881 = 1060411) B1060411
theorem B5083955 : Blo 370760 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B562025 : Blo 370760 562025 := bstep (se 2 (by rfl) ⟨210759, by rfl⟩ : syracuseStep 562025 = 421519) B421519
theorem B2397073 : Blo 370760 2397073 := bstep (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) B1797805
theorem B562103 : Blo 370760 562103 := bstep (se 1 (by rfl) ⟨421577, by rfl⟩ : syracuseStep 562103 = 843155) B843155
theorem B562139 : Blo 370760 562139 := bstep (se 1 (by rfl) ⟨421604, by rfl⟩ : syracuseStep 562139 = 843209) B843209
theorem B1807379 : Blo 370760 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B627959 : Blo 370760 627959 := bstep (se 1 (by rfl) ⟨470969, by rfl⟩ : syracuseStep 627959 = 941939) B941939
theorem B2397431 : Blo 370760 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B18060691 : Blo 370760 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B4855301 : Blo 370760 4855301 := bstep (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) B910369
theorem B628303 : Blo 370760 628303 := bstep (se 1 (by rfl) ⟨471227, by rfl⟩ : syracuseStep 628303 = 942455) B942455
theorem B1414867 : Blo 370760 1414867 := bstep (se 1 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 1414867 = 2122301) B2122301
theorem B628553 : Blo 370760 628553 := bstep (se 2 (by rfl) ⟨235707, by rfl⟩ : syracuseStep 628553 = 471415) B471415
theorem B2824145 : Blo 370760 2824145 := bstep (se 2 (by rfl) ⟨1059054, by rfl⟩ : syracuseStep 2824145 = 2118109) B2118109
theorem B5740631 : Blo 370760 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B1415339 : Blo 370760 1415339 := bstep (se 1 (by rfl) ⟨1061504, by rfl⟩ : syracuseStep 1415339 = 2123009) B2123009
theorem B628985 : Blo 370760 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B7641377 : Blo 370760 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B4037015 : Blo 370760 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B629167 : Blo 370760 629167 := bstep (se 1 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 629167 = 943751) B943751
theorem B596411 : Blo 370760 596411 := bstep (se 1 (by rfl) ⟨447308, by rfl⟩ : syracuseStep 596411 = 894617) B894617
theorem B1251827 : Blo 370760 1251827 := bstep (se 1 (by rfl) ⟨938870, by rfl⟩ : syracuseStep 1251827 = 1877741) B1877741
theorem B629255 : Blo 370760 629255 := bstep (se 1 (by rfl) ⟨471941, by rfl⟩ : syracuseStep 629255 = 943883) B943883
theorem B5118497 : Blo 370760 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B596603 : Blo 370760 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B12229465 : Blo 370760 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B4758365 : Blo 370760 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B629599 : Blo 370760 629599 := bstep (se 1 (by rfl) ⟨472199, by rfl⟩ : syracuseStep 629599 = 944399) B944399
theorem B596911 : Blo 370760 596911 := bstep (se 1 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 596911 = 895367) B895367
theorem B629687 : Blo 370760 629687 := bstep (se 1 (by rfl) ⟨472265, by rfl⟩ : syracuseStep 629687 = 944531) B944531
theorem B1252367 : Blo 370760 1252367 := bstep (se 1 (by rfl) ⟨939275, by rfl⟩ : syracuseStep 1252367 = 1878551) B1878551
theorem B793847 : Blo 370760 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B4300121 : Blo 370760 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B2432429 : Blo 370760 2432429 := bstep (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) B912161
theorem B630281 : Blo 370760 630281 := bstep (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) B472711
theorem B1252961 : Blo 370760 1252961 := bstep (se 2 (by rfl) ⟨469860, by rfl⟩ : syracuseStep 1252961 = 939721) B939721
theorem B2694779 : Blo 370760 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B630443 : Blo 370760 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B532489 : Blo 370760 532489 := bstep (se 2 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 532489 = 399367) B399367
theorem B630841 : Blo 370760 630841 := bstep (se 2 (by rfl) ⟨236565, by rfl⟩ : syracuseStep 630841 = 473131) B473131
theorem B1417297 : Blo 370760 1417297 := bstep (se 2 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 1417297 = 1062973) B1062973
theorem B532603 : Blo 370760 532603 := bstep (se 1 (by rfl) ⟨399452, by rfl⟩ : syracuseStep 532603 = 798905) B798905
theorem B630983 : Blo 370760 630983 := bstep (se 1 (by rfl) ⟨473237, by rfl⟩ : syracuseStep 630983 = 946475) B946475
theorem B532831 : Blo 370760 532831 := bstep (se 1 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 532831 = 799247) B799247
theorem B958825 : Blo 370760 958825 := bstep (se 2 (by rfl) ⟨359559, by rfl⟩ : syracuseStep 958825 = 719119) B719119
theorem B631145 : Blo 370760 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B1417601 : Blo 370760 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B565723 : Blo 370760 565723 := bstep (se 1 (by rfl) ⟨424292, by rfl⟩ : syracuseStep 565723 = 848585) B848585
theorem B1188361 : Blo 370760 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B2007611 : Blo 370760 2007611 := bstep (se 1 (by rfl) ⟨1505708, by rfl⟩ : syracuseStep 2007611 = 3011417) B3011417
theorem B565883 : Blo 370760 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B1057495 : Blo 370760 1057495 := bstep (se 1 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 1057495 = 1586243) B1586243
theorem B631543 : Blo 370760 631543 := bstep (se 1 (by rfl) ⟨473657, by rfl⟩ : syracuseStep 631543 = 947315) B947315
theorem B1057529 : Blo 370760 1057529 := bstep (se 2 (by rfl) ⟨396573, by rfl⟩ : syracuseStep 1057529 = 793147) B793147
theorem B4760369 : Blo 370760 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B1418057 : Blo 370760 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B1057643 : Blo 370760 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B1057711 : Blo 370760 1057711 := bstep (se 1 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 1057711 = 1586567) B1586567
theorem B533423 : Blo 370760 533423 := bstep (se 1 (by rfl) ⟨400067, by rfl⟩ : syracuseStep 533423 = 800135) B800135
theorem B631739 : Blo 370760 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B1418255 : Blo 370760 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B1254419 : Blo 370760 1254419 := bstep (se 1 (by rfl) ⟨940814, by rfl⟩ : syracuseStep 1254419 = 1881629) B1881629
theorem B730151 : Blo 370760 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B631847 : Blo 370760 631847 := bstep (se 1 (by rfl) ⟨473885, by rfl⟩ : syracuseStep 631847 = 947771) B947771
theorem B632137 : Blo 370760 632137 := bstep (se 2 (by rfl) ⟨237051, by rfl⟩ : syracuseStep 632137 = 474103) B474103
theorem B1254743 : Blo 370760 1254743 := bstep (se 1 (by rfl) ⟨941057, by rfl⟩ : syracuseStep 1254743 = 1882115) B1882115
theorem B632171 : Blo 370760 632171 := bstep (se 1 (by rfl) ⟨474128, by rfl⟩ : syracuseStep 632171 = 948257) B948257
theorem B4236947 : Blo 370760 4236947 := bstep (se 1 (by rfl) ⟨3177710, by rfl⟩ : syracuseStep 4236947 = 6355421) B6355421
theorem B370767 : Blo 370760 370767 := bstep (se 1 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 370767 = 556151) B556151
theorem B370783 : Blo 370760 370783 := bstep (se 1 (by rfl) ⟨278087, by rfl⟩ : syracuseStep 370783 = 556175) B556175
theorem B370811 : Blo 370760 370811 := bstep (se 1 (by rfl) ⟨278108, by rfl⟩ : syracuseStep 370811 = 556217) B556217
theorem B1058987 : Blo 370760 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B370863 : Blo 370760 370863 := bstep (se 1 (by rfl) ⟨278147, by rfl⟩ : syracuseStep 370863 = 556295) B556295
theorem B370887 : Blo 370760 370887 := bstep (se 1 (by rfl) ⟨278165, by rfl⟩ : syracuseStep 370887 = 556331) B556331
theorem B370907 : Blo 370760 370907 := bstep (se 1 (by rfl) ⟨278180, by rfl⟩ : syracuseStep 370907 = 556361) B556361
theorem B370983 : Blo 370760 370983 := bstep (se 1 (by rfl) ⟨278237, by rfl⟩ : syracuseStep 370983 = 556475) B556475
theorem B371023 : Blo 370760 371023 := bstep (se 1 (by rfl) ⟨278267, by rfl⟩ : syracuseStep 371023 = 556535) B556535
theorem B371039 : Blo 370760 371039 := bstep (se 1 (by rfl) ⟨278279, by rfl⟩ : syracuseStep 371039 = 556559) B556559
theorem B371067 : Blo 370760 371067 := bstep (se 1 (by rfl) ⟨278300, by rfl⟩ : syracuseStep 371067 = 556601) B556601
theorem B1255823 : Blo 370760 1255823 := bstep (se 1 (by rfl) ⟨941867, by rfl⟩ : syracuseStep 1255823 = 1883735) B1883735
theorem B371119 : Blo 370760 371119 := bstep (se 1 (by rfl) ⟨278339, by rfl⟩ : syracuseStep 371119 = 556679) B556679
theorem B371143 : Blo 370760 371143 := bstep (se 1 (by rfl) ⟨278357, by rfl⟩ : syracuseStep 371143 = 556715) B556715
theorem B371163 : Blo 370760 371163 := bstep (se 1 (by rfl) ⟨278372, by rfl⟩ : syracuseStep 371163 = 556745) B556745
theorem B371239 : Blo 370760 371239 := bstep (se 1 (by rfl) ⟨278429, by rfl⟩ : syracuseStep 371239 = 556859) B556859
theorem B371279 : Blo 370760 371279 := bstep (se 1 (by rfl) ⟨278459, by rfl⟩ : syracuseStep 371279 = 556919) B556919
theorem B371295 : Blo 370760 371295 := bstep (se 1 (by rfl) ⟨278471, by rfl⟩ : syracuseStep 371295 = 556943) B556943
theorem B371323 : Blo 370760 371323 := bstep (se 1 (by rfl) ⟨278492, by rfl⟩ : syracuseStep 371323 = 556985) B556985
theorem B371375 : Blo 370760 371375 := bstep (se 1 (by rfl) ⟨278531, by rfl⟩ : syracuseStep 371375 = 557063) B557063
theorem B1878713 : Blo 370760 1878713 := bstep (se 2 (by rfl) ⟨704517, by rfl⟩ : syracuseStep 1878713 = 1409035) B1409035
theorem B371399 : Blo 370760 371399 := bstep (se 1 (by rfl) ⟨278549, by rfl⟩ : syracuseStep 371399 = 557099) B557099
theorem B1256147 : Blo 370760 1256147 := bstep (se 1 (by rfl) ⟨942110, by rfl⟩ : syracuseStep 1256147 = 1884221) B1884221
theorem B371419 : Blo 370760 371419 := bstep (se 1 (by rfl) ⟨278564, by rfl⟩ : syracuseStep 371419 = 557129) B557129
theorem B371495 : Blo 370760 371495 := bstep (se 1 (by rfl) ⟨278621, by rfl⟩ : syracuseStep 371495 = 557243) B557243
theorem B371535 : Blo 370760 371535 := bstep (se 1 (by rfl) ⟨278651, by rfl⟩ : syracuseStep 371535 = 557303) B557303
theorem B371551 : Blo 370760 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B371579 : Blo 370760 371579 := bstep (se 1 (by rfl) ⟨278684, by rfl⟩ : syracuseStep 371579 = 557369) B557369
theorem B371631 : Blo 370760 371631 := bstep (se 1 (by rfl) ⟨278723, by rfl⟩ : syracuseStep 371631 = 557447) B557447
theorem B1649591 : Blo 370760 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B371655 : Blo 370760 371655 := bstep (se 1 (by rfl) ⟨278741, by rfl⟩ : syracuseStep 371655 = 557483) B557483
theorem B371675 : Blo 370760 371675 := bstep (se 1 (by rfl) ⟨278756, by rfl⟩ : syracuseStep 371675 = 557513) B557513
theorem B371751 : Blo 370760 371751 := bstep (se 1 (by rfl) ⟨278813, by rfl⟩ : syracuseStep 371751 = 557627) B557627
theorem B371791 : Blo 370760 371791 := bstep (se 1 (by rfl) ⟨278843, by rfl⟩ : syracuseStep 371791 = 557687) B557687
theorem B1911887 : Blo 370760 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B371807 : Blo 370760 371807 := bstep (se 1 (by rfl) ⟨278855, by rfl⟩ : syracuseStep 371807 = 557711) B557711
theorem B371835 : Blo 370760 371835 := bstep (se 1 (by rfl) ⟨278876, by rfl⟩ : syracuseStep 371835 = 557753) B557753
theorem B371887 : Blo 370760 371887 := bstep (se 1 (by rfl) ⟨278915, by rfl⟩ : syracuseStep 371887 = 557831) B557831
theorem B470215 : Blo 370760 470215 := bstep (se 1 (by rfl) ⟨352661, by rfl⟩ : syracuseStep 470215 = 705323) B705323
theorem B371911 : Blo 370760 371911 := bstep (se 1 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 371911 = 557867) B557867
theorem B371931 : Blo 370760 371931 := bstep (se 1 (by rfl) ⟨278948, by rfl⟩ : syracuseStep 371931 = 557897) B557897
theorem B2010359 : Blo 370760 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B372007 : Blo 370760 372007 := bstep (se 1 (by rfl) ⟨279005, by rfl⟩ : syracuseStep 372007 = 558011) B558011
theorem B372047 : Blo 370760 372047 := bstep (se 1 (by rfl) ⟨279035, by rfl⟩ : syracuseStep 372047 = 558071) B558071
theorem B372063 : Blo 370760 372063 := bstep (se 1 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 372063 = 558095) B558095
theorem B372091 : Blo 370760 372091 := bstep (se 1 (by rfl) ⟨279068, by rfl⟩ : syracuseStep 372091 = 558137) B558137
theorem B372143 : Blo 370760 372143 := bstep (se 1 (by rfl) ⟨279107, by rfl⟩ : syracuseStep 372143 = 558215) B558215
theorem B372167 : Blo 370760 372167 := bstep (se 1 (by rfl) ⟨279125, by rfl⟩ : syracuseStep 372167 = 558251) B558251
theorem B372187 : Blo 370760 372187 := bstep (se 1 (by rfl) ⟨279140, by rfl⟩ : syracuseStep 372187 = 558281) B558281
theorem B372263 : Blo 370760 372263 := bstep (se 1 (by rfl) ⟨279197, by rfl⟩ : syracuseStep 372263 = 558395) B558395
theorem B372303 : Blo 370760 372303 := bstep (se 1 (by rfl) ⟨279227, by rfl⟩ : syracuseStep 372303 = 558455) B558455
theorem B372319 : Blo 370760 372319 := bstep (se 1 (by rfl) ⟨279239, by rfl⟩ : syracuseStep 372319 = 558479) B558479
theorem B372347 : Blo 370760 372347 := bstep (se 1 (by rfl) ⟨279260, by rfl⟩ : syracuseStep 372347 = 558521) B558521
theorem B372399 : Blo 370760 372399 := bstep (se 1 (by rfl) ⟨279299, by rfl⟩ : syracuseStep 372399 = 558599) B558599
theorem B372423 : Blo 370760 372423 := bstep (se 1 (by rfl) ⟨279317, by rfl⟩ : syracuseStep 372423 = 558635) B558635
theorem B2272967 : Blo 370760 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B372443 : Blo 370760 372443 := bstep (se 1 (by rfl) ⟨279332, by rfl⟩ : syracuseStep 372443 = 558665) B558665
theorem B372519 : Blo 370760 372519 := bstep (se 1 (by rfl) ⟨279389, by rfl⟩ : syracuseStep 372519 = 558779) B558779
theorem B372559 : Blo 370760 372559 := bstep (se 1 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 372559 = 558839) B558839
theorem B372575 : Blo 370760 372575 := bstep (se 1 (by rfl) ⟨279431, by rfl⟩ : syracuseStep 372575 = 558863) B558863
theorem B1257335 : Blo 370760 1257335 := bstep (se 1 (by rfl) ⟨943001, by rfl⟩ : syracuseStep 1257335 = 1886003) B1886003
theorem B372603 : Blo 370760 372603 := bstep (se 1 (by rfl) ⟨279452, by rfl⟩ : syracuseStep 372603 = 558905) B558905
theorem B372655 : Blo 370760 372655 := bstep (se 1 (by rfl) ⟨279491, by rfl⟩ : syracuseStep 372655 = 558983) B558983
theorem B569263 : Blo 370760 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B372679 : Blo 370760 372679 := bstep (se 1 (by rfl) ⟨279509, by rfl⟩ : syracuseStep 372679 = 559019) B559019
theorem B372699 : Blo 370760 372699 := bstep (se 1 (by rfl) ⟨279524, by rfl⟩ : syracuseStep 372699 = 559049) B559049
theorem B372775 : Blo 370760 372775 := bstep (se 1 (by rfl) ⟨279581, by rfl⟩ : syracuseStep 372775 = 559163) B559163
theorem B1257551 : Blo 370760 1257551 := bstep (se 1 (by rfl) ⟨943163, by rfl⟩ : syracuseStep 1257551 = 1886327) B1886327
theorem B372815 : Blo 370760 372815 := bstep (se 1 (by rfl) ⟨279611, by rfl⟩ : syracuseStep 372815 = 559223) B559223
theorem B372831 : Blo 370760 372831 := bstep (se 1 (by rfl) ⟨279623, by rfl⟩ : syracuseStep 372831 = 559247) B559247
theorem B372859 : Blo 370760 372859 := bstep (se 1 (by rfl) ⟨279644, by rfl⟩ : syracuseStep 372859 = 559289) B559289
theorem B372911 : Blo 370760 372911 := bstep (se 1 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 372911 = 559367) B559367
theorem B372935 : Blo 370760 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B372955 : Blo 370760 372955 := bstep (se 1 (by rfl) ⟨279716, by rfl⟩ : syracuseStep 372955 = 559433) B559433
theorem B373031 : Blo 370760 373031 := bstep (se 1 (by rfl) ⟨279773, by rfl⟩ : syracuseStep 373031 = 559547) B559547
theorem B373071 : Blo 370760 373071 := bstep (se 1 (by rfl) ⟨279803, by rfl⟩ : syracuseStep 373071 = 559607) B559607
theorem B373087 : Blo 370760 373087 := bstep (se 1 (by rfl) ⟨279815, by rfl⟩ : syracuseStep 373087 = 559631) B559631
theorem B1782121 : Blo 370760 1782121 := bstep (se 2 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 1782121 = 1336591) B1336591
theorem B373115 : Blo 370760 373115 := bstep (se 1 (by rfl) ⟨279836, by rfl⟩ : syracuseStep 373115 = 559673) B559673
theorem B373167 : Blo 370760 373167 := bstep (se 1 (by rfl) ⟨279875, by rfl⟩ : syracuseStep 373167 = 559751) B559751
theorem B373191 : Blo 370760 373191 := bstep (se 1 (by rfl) ⟨279893, by rfl⟩ : syracuseStep 373191 = 559787) B559787
theorem B1257929 : Blo 370760 1257929 := bstep (se 2 (by rfl) ⟨471723, by rfl⟩ : syracuseStep 1257929 = 943447) B943447
theorem B1192411 : Blo 370760 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B373211 : Blo 370760 373211 := bstep (se 1 (by rfl) ⟨279908, by rfl⟩ : syracuseStep 373211 = 559817) B559817
theorem B373287 : Blo 370760 373287 := bstep (se 1 (by rfl) ⟨279965, by rfl⟩ : syracuseStep 373287 = 559931) B559931
theorem B373327 : Blo 370760 373327 := bstep (se 1 (by rfl) ⟨279995, by rfl⟩ : syracuseStep 373327 = 559991) B559991
theorem B373343 : Blo 370760 373343 := bstep (se 1 (by rfl) ⟨280007, by rfl⟩ : syracuseStep 373343 = 560015) B560015
theorem B373371 : Blo 370760 373371 := bstep (se 1 (by rfl) ⟨280028, by rfl⟩ : syracuseStep 373371 = 560057) B560057
theorem B1061515 : Blo 370760 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B373423 : Blo 370760 373423 := bstep (se 1 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 373423 = 560135) B560135
theorem B373447 : Blo 370760 373447 := bstep (se 1 (by rfl) ⟨280085, by rfl⟩ : syracuseStep 373447 = 560171) B560171
theorem B1258199 : Blo 370760 1258199 := bstep (se 1 (by rfl) ⟨943649, by rfl⟩ : syracuseStep 1258199 = 1887299) B1887299
theorem B373467 : Blo 370760 373467 := bstep (se 1 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 373467 = 560201) B560201
theorem B373543 : Blo 370760 373543 := bstep (se 1 (by rfl) ⟨280157, by rfl⟩ : syracuseStep 373543 = 560315) B560315
theorem B373583 : Blo 370760 373583 := bstep (se 1 (by rfl) ⟨280187, by rfl⟩ : syracuseStep 373583 = 560375) B560375
theorem B373599 : Blo 370760 373599 := bstep (se 1 (by rfl) ⟨280199, by rfl⟩ : syracuseStep 373599 = 560399) B560399
theorem B373627 : Blo 370760 373627 := bstep (se 1 (by rfl) ⟨280220, by rfl⟩ : syracuseStep 373627 = 560441) B560441
theorem B1258415 : Blo 370760 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B373679 : Blo 370760 373679 := bstep (se 1 (by rfl) ⟨280259, by rfl⟩ : syracuseStep 373679 = 560519) B560519
theorem B373703 : Blo 370760 373703 := bstep (se 1 (by rfl) ⟨280277, by rfl⟩ : syracuseStep 373703 = 560555) B560555
theorem B373723 : Blo 370760 373723 := bstep (se 1 (by rfl) ⟨280292, by rfl⟩ : syracuseStep 373723 = 560585) B560585
theorem B373799 : Blo 370760 373799 := bstep (se 1 (by rfl) ⟨280349, by rfl⟩ : syracuseStep 373799 = 560699) B560699
theorem B373839 : Blo 370760 373839 := bstep (se 1 (by rfl) ⟨280379, by rfl⟩ : syracuseStep 373839 = 560759) B560759
theorem B373855 : Blo 370760 373855 := bstep (se 1 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 373855 = 560783) B560783
theorem B373883 : Blo 370760 373883 := bstep (se 1 (by rfl) ⟨280412, by rfl⟩ : syracuseStep 373883 = 560825) B560825
theorem B38810765 : Blo 370760 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B373935 : Blo 370760 373935 := bstep (se 1 (by rfl) ⟨280451, by rfl⟩ : syracuseStep 373935 = 560903) B560903
theorem B373959 : Blo 370760 373959 := bstep (se 1 (by rfl) ⟨280469, by rfl⟩ : syracuseStep 373959 = 560939) B560939
theorem B373979 : Blo 370760 373979 := bstep (se 1 (by rfl) ⟨280484, by rfl⟩ : syracuseStep 373979 = 560969) B560969
theorem B374055 : Blo 370760 374055 := bstep (se 1 (by rfl) ⟨280541, by rfl⟩ : syracuseStep 374055 = 561083) B561083
theorem B374095 : Blo 370760 374095 := bstep (se 1 (by rfl) ⟨280571, by rfl⟩ : syracuseStep 374095 = 561143) B561143
theorem B374111 : Blo 370760 374111 := bstep (se 1 (by rfl) ⟨280583, by rfl⟩ : syracuseStep 374111 = 561167) B561167
theorem B374139 : Blo 370760 374139 := bstep (se 1 (by rfl) ⟨280604, by rfl⟩ : syracuseStep 374139 = 561209) B561209
theorem B374191 : Blo 370760 374191 := bstep (se 1 (by rfl) ⟨280643, by rfl⟩ : syracuseStep 374191 = 561287) B561287
theorem B374215 : Blo 370760 374215 := bstep (se 1 (by rfl) ⟨280661, by rfl⟩ : syracuseStep 374215 = 561323) B561323
theorem B374235 : Blo 370760 374235 := bstep (se 1 (by rfl) ⟨280676, by rfl⟩ : syracuseStep 374235 = 561353) B561353
theorem B1127945 : Blo 370760 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B374311 : Blo 370760 374311 := bstep (se 1 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 374311 = 561467) B561467
theorem B472655 : Blo 370760 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B374351 : Blo 370760 374351 := bstep (se 1 (by rfl) ⟨280763, by rfl⟩ : syracuseStep 374351 = 561527) B561527
theorem B374367 : Blo 370760 374367 := bstep (se 1 (by rfl) ⟨280775, by rfl⟩ : syracuseStep 374367 = 561551) B561551
theorem B374395 : Blo 370760 374395 := bstep (se 1 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 374395 = 561593) B561593
theorem B374447 : Blo 370760 374447 := bstep (se 1 (by rfl) ⟨280835, by rfl⟩ : syracuseStep 374447 = 561671) B561671
theorem B374471 : Blo 370760 374471 := bstep (se 1 (by rfl) ⟨280853, by rfl⟩ : syracuseStep 374471 = 561707) B561707
theorem B374491 : Blo 370760 374491 := bstep (se 1 (by rfl) ⟨280868, by rfl⟩ : syracuseStep 374491 = 561737) B561737
theorem B5748515 : Blo 370760 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B374567 : Blo 370760 374567 := bstep (se 1 (by rfl) ⟨280925, by rfl⟩ : syracuseStep 374567 = 561851) B561851
theorem B374607 : Blo 370760 374607 := bstep (se 1 (by rfl) ⟨280955, by rfl⟩ : syracuseStep 374607 = 561911) B561911
theorem B374623 : Blo 370760 374623 := bstep (se 1 (by rfl) ⟨280967, by rfl⟩ : syracuseStep 374623 = 561935) B561935
theorem B374651 : Blo 370760 374651 := bstep (se 1 (by rfl) ⟨280988, by rfl⟩ : syracuseStep 374651 = 561977) B561977
theorem B374703 : Blo 370760 374703 := bstep (se 1 (by rfl) ⟨281027, by rfl⟩ : syracuseStep 374703 = 562055) B562055
theorem B866231 : Blo 370760 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B374727 : Blo 370760 374727 := bstep (se 1 (by rfl) ⟨281045, by rfl⟩ : syracuseStep 374727 = 562091) B562091
theorem B374747 : Blo 370760 374747 := bstep (se 1 (by rfl) ⟨281060, by rfl⟩ : syracuseStep 374747 = 562121) B562121
theorem B1587215 : Blo 370760 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B473951 : Blo 370760 473951 := bstep (se 1 (by rfl) ⟨355463, by rfl⟩ : syracuseStep 473951 = 710927) B710927
theorem B3619729 : Blo 370760 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B834479 : Blo 370760 834479 := bstep (se 1 (by rfl) ⟨625859, by rfl⟩ : syracuseStep 834479 = 1251719) B1251719
theorem B1162297 : Blo 370760 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B834731 : Blo 370760 834731 := bstep (se 1 (by rfl) ⟨626048, by rfl⟩ : syracuseStep 834731 = 1252097) B1252097
theorem B1260791 : Blo 370760 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B4799735 : Blo 370760 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B2833865 : Blo 370760 2833865 := bstep (se 2 (by rfl) ⟨1062699, by rfl⟩ : syracuseStep 2833865 = 2125399) B2125399
theorem B1261115 : Blo 370760 1261115 := bstep (se 1 (by rfl) ⟨945836, by rfl⟩ : syracuseStep 1261115 = 1891673) B1891673
theorem B704123 : Blo 370760 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B1195667 : Blo 370760 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B835271 : Blo 370760 835271 := bstep (se 1 (by rfl) ⟨626453, by rfl⟩ : syracuseStep 835271 = 1252907) B1252907
theorem B1064659 : Blo 370760 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B1883897 : Blo 370760 1883897 := bstep (se 2 (by rfl) ⟨706461, by rfl⟩ : syracuseStep 1883897 = 1412923) B1412923
theorem B1261385 : Blo 370760 1261385 := bstep (se 2 (by rfl) ⟨473019, by rfl⟩ : syracuseStep 1261385 = 946039) B946039
theorem B704351 : Blo 370760 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B1196039 : Blo 370760 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B704609 : Blo 370760 704609 := bstep (se 2 (by rfl) ⟨264228, by rfl⟩ : syracuseStep 704609 = 528457) B528457
theorem B2015549 : Blo 370760 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B7192907 : Blo 370760 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B704875 : Blo 370760 704875 := bstep (se 1 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 704875 = 1057313) B1057313
theorem B1884545 : Blo 370760 1884545 := bstep (se 2 (by rfl) ⟨706704, by rfl⟩ : syracuseStep 1884545 = 1413409) B1413409
theorem B672275 : Blo 370760 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B836135 : Blo 370760 836135 := bstep (se 1 (by rfl) ⟨627101, by rfl⟩ : syracuseStep 836135 = 1254203) B1254203
theorem B6046325 : Blo 370760 6046325 := bstep (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) B566843
theorem B836459 : Blo 370760 836459 := bstep (se 1 (by rfl) ⟨627344, by rfl⟩ : syracuseStep 836459 = 1254689) B1254689
theorem B836513 : Blo 370760 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B1065889 : Blo 370760 1065889 := bstep (se 2 (by rfl) ⟨399708, by rfl⟩ : syracuseStep 1065889 = 799417) B799417
theorem B9552815 : Blo 370760 9552815 := bstep (se 1 (by rfl) ⟨7164611, by rfl⟩ : syracuseStep 9552815 = 14329223) B14329223
theorem B1262519 : Blo 370760 1262519 := bstep (se 1 (by rfl) ⟨946889, by rfl⟩ : syracuseStep 1262519 = 1893779) B1893779
theorem B3392513 : Blo 370760 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B1885355 : Blo 370760 1885355 := bstep (se 1 (by rfl) ⟨1414016, by rfl⟩ : syracuseStep 1885355 = 2828033) B2828033
theorem B836855 : Blo 370760 836855 := bstep (se 1 (by rfl) ⟨627641, by rfl⟩ : syracuseStep 836855 = 1255283) B1255283
theorem B3097871 : Blo 370760 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B6768035 : Blo 370760 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B4343203 : Blo 370760 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B2377133 : Blo 370760 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B1230281 : Blo 370760 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B1131995 : Blo 370760 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B1066459 : Blo 370760 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B1263113 : Blo 370760 1263113 := bstep (se 2 (by rfl) ⟨473667, by rfl⟩ : syracuseStep 1263113 = 947335) B947335
theorem B706067 : Blo 370760 706067 := bstep (se 1 (by rfl) ⟨529550, by rfl⟩ : syracuseStep 706067 = 1059101) B1059101
theorem B1885841 : Blo 370760 1885841 := bstep (se 2 (by rfl) ⟨707190, by rfl⟩ : syracuseStep 1885841 = 1414381) B1414381
theorem B706295 : Blo 370760 706295 := bstep (se 1 (by rfl) ⟨529721, by rfl⟩ : syracuseStep 706295 = 1059443) B1059443
theorem B837449 : Blo 370760 837449 := bstep (se 2 (by rfl) ⟨314043, by rfl⟩ : syracuseStep 837449 = 628087) B628087
theorem B7161695 : Blo 370760 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B2541431 : Blo 370760 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B1067165 : Blo 370760 1067165 := bstep (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) B400187
theorem B1263977 : Blo 370760 1263977 := bstep (se 2 (by rfl) ⟨473991, by rfl⟩ : syracuseStep 1263977 = 947983) B947983
theorem B3590689 : Blo 370760 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B838241 : Blo 370760 838241 := bstep (se 2 (by rfl) ⟨314340, by rfl⟩ : syracuseStep 838241 = 628681) B628681
theorem B1198921 : Blo 370760 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B1362863 : Blo 370760 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B838583 : Blo 370760 838583 := bstep (se 1 (by rfl) ⟨628937, by rfl⟩ : syracuseStep 838583 = 1257875) B1257875
theorem B1264571 : Blo 370760 1264571 := bstep (se 1 (by rfl) ⟨948428, by rfl⟩ : syracuseStep 1264571 = 1896857) B1896857
theorem B707707 : Blo 370760 707707 := bstep (se 1 (by rfl) ⟨530780, by rfl⟩ : syracuseStep 707707 = 1061561) B1061561
theorem B707935 : Blo 370760 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B19353005 : Blo 370760 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B445915 : Blo 370760 445915 := bstep (se 1 (by rfl) ⟨334436, by rfl⟩ : syracuseStep 445915 = 668873) B668873
theorem B839177 : Blo 370760 839177 := bstep (se 2 (by rfl) ⟨314691, by rfl⟩ : syracuseStep 839177 = 629383) B629383
theorem B708193 : Blo 370760 708193 := bstep (se 2 (by rfl) ⟨265572, by rfl⟩ : syracuseStep 708193 = 531145) B531145
theorem B839519 : Blo 370760 839519 := bstep (se 1 (by rfl) ⟨629639, by rfl⟩ : syracuseStep 839519 = 1259279) B1259279
theorem B1888109 : Blo 370760 1888109 := bstep (se 3 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 1888109 = 708041) B708041
theorem B708527 : Blo 370760 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B1888271 : Blo 370760 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B839699 : Blo 370760 839699 := bstep (se 1 (by rfl) ⟨629774, by rfl⟩ : syracuseStep 839699 = 1259549) B1259549
theorem B8605777 : Blo 370760 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B3592421 : Blo 370760 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B840041 : Blo 370760 840041 := bstep (se 2 (by rfl) ⟨315015, by rfl⟩ : syracuseStep 840041 = 630031) B630031
theorem B840635 : Blo 370760 840635 := bstep (se 1 (by rfl) ⟨630476, by rfl⟩ : syracuseStep 840635 = 1260953) B1260953
theorem B709651 : Blo 370760 709651 := bstep (se 1 (by rfl) ⟨532238, by rfl⟩ : syracuseStep 709651 = 1064477) B1064477
theorem B840761 : Blo 370760 840761 := bstep (se 2 (by rfl) ⟨315285, by rfl⟩ : syracuseStep 840761 = 630571) B630571
theorem B709879 : Blo 370760 709879 := bstep (se 1 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 709879 = 1064819) B1064819
theorem B841103 : Blo 370760 841103 := bstep (se 1 (by rfl) ⟨630827, by rfl⟩ : syracuseStep 841103 = 1261655) B1261655
theorem B3823109 : Blo 370760 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B939559 : Blo 370760 939559 := bstep (se 1 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 939559 = 1409339) B1409339
theorem B448039 : Blo 370760 448039 := bstep (se 1 (by rfl) ⟨336029, by rfl⟩ : syracuseStep 448039 = 672059) B672059
theorem B710183 : Blo 370760 710183 := bstep (se 1 (by rfl) ⟨532637, by rfl⟩ : syracuseStep 710183 = 1065275) B1065275
theorem B841427 : Blo 370760 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B1005385 : Blo 370760 1005385 := bstep (se 2 (by rfl) ⟨377019, by rfl⟩ : syracuseStep 1005385 = 754039) B754039
theorem B939883 : Blo 370760 939883 := bstep (se 1 (by rfl) ⟨704912, by rfl⟩ : syracuseStep 939883 = 1409825) B1409825
theorem B2677043 : Blo 370760 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1005967 : Blo 370760 1005967 := bstep (se 1 (by rfl) ⟨754475, by rfl⟩ : syracuseStep 1005967 = 1508951) B1508951
theorem B940531 : Blo 370760 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B1595963 : Blo 370760 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B842363 : Blo 370760 842363 := bstep (se 1 (by rfl) ⟨631772, by rfl⟩ : syracuseStep 842363 = 1263545) B1263545
theorem B1891025 : Blo 370760 1891025 := bstep (se 2 (by rfl) ⟨709134, by rfl⟩ : syracuseStep 1891025 = 1418269) B1418269
theorem B842489 : Blo 370760 842489 := bstep (se 2 (by rfl) ⟨315933, by rfl⟩ : syracuseStep 842489 = 631867) B631867
theorem B842759 : Blo 370760 842759 := bstep (se 1 (by rfl) ⟨632069, by rfl⟩ : syracuseStep 842759 = 1264139) B1264139
theorem B842831 : Blo 370760 842831 := bstep (se 1 (by rfl) ⟨632123, by rfl⟩ : syracuseStep 842831 = 1264247) B1264247
theorem B417199 : Blo 370760 417199 := bstep (se 1 (by rfl) ⟨312899, by rfl⟩ : syracuseStep 417199 = 625799) B625799
theorem B941665 : Blo 370760 941665 := bstep (se 2 (by rfl) ⟨353124, by rfl⟩ : syracuseStep 941665 = 706249) B706249
theorem B417631 : Blo 370760 417631 := bstep (se 1 (by rfl) ⟨313223, by rfl⟩ : syracuseStep 417631 = 626447) B626447
theorem B4251527 : Blo 370760 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B4317299 : Blo 370760 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B417991 : Blo 370760 417991 := bstep (se 1 (by rfl) ⟨313493, by rfl⟩ : syracuseStep 417991 = 626987) B626987
theorem B942617 : Blo 370760 942617 := bstep (se 2 (by rfl) ⟨353481, by rfl⟩ : syracuseStep 942617 = 706963) B706963
theorem B484039 : Blo 370760 484039 := bstep (se 1 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 484039 = 726059) B726059
theorem B2679581 : Blo 370760 2679581 := bstep (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) B1004843
theorem B943123 : Blo 370760 943123 := bstep (se 1 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 943123 = 1414685) B1414685
theorem B418855 : Blo 370760 418855 := bstep (se 1 (by rfl) ⟨314141, by rfl⟩ : syracuseStep 418855 = 628283) B628283
theorem B1893455 : Blo 370760 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B2155673 : Blo 370760 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B1860989 : Blo 370760 1860989 := bstep (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) B697871
theorem B1009039 : Blo 370760 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B1894103 : Blo 370760 1894103 := bstep (se 1 (by rfl) ⟨1420577, by rfl⟩ : syracuseStep 1894103 = 2841155) B2841155
theorem B2385949 : Blo 370760 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B944207 : Blo 370760 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B452959 : Blo 370760 452959 := bstep (se 1 (by rfl) ⟨339719, by rfl⟩ : syracuseStep 452959 = 679439) B679439
theorem B6777377 : Blo 370760 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B420475 : Blo 370760 420475 := bstep (se 1 (by rfl) ⟨315356, by rfl⟩ : syracuseStep 420475 = 630713) B630713
theorem B944855 : Blo 370760 944855 := bstep (se 1 (by rfl) ⟨708641, by rfl⟩ : syracuseStep 944855 = 1417283) B1417283
theorem B945209 : Blo 370760 945209 := bstep (se 2 (by rfl) ⟨354453, by rfl⟩ : syracuseStep 945209 = 708907) B708907
theorem B420943 : Blo 370760 420943 := bstep (se 1 (by rfl) ⟨315707, by rfl⟩ : syracuseStep 420943 = 631415) B631415
theorem B5074319 : Blo 370760 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B421339 : Blo 370760 421339 := bstep (se 1 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 421339 = 632009) B632009
theorem B4779485 : Blo 370760 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B2715275 : Blo 370760 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B1011959 : Blo 370760 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B2617661 : Blo 370760 2617661 := bstep (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) B981623
theorem B1339777 : Blo 370760 1339777 := bstep (se 2 (by rfl) ⟨502416, by rfl⟩ : syracuseStep 1339777 = 1004833) B1004833
theorem B1503631 : Blo 370760 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B1897019 : Blo 370760 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B947447 : Blo 370760 947447 := bstep (se 1 (by rfl) ⟨710585, by rfl⟩ : syracuseStep 947447 = 1421171) B1421171
theorem B718073 : Blo 370760 718073 := bstep (se 2 (by rfl) ⟨269277, by rfl⟩ : syracuseStep 718073 = 538555) B538555
theorem B719689 : Blo 370760 719689 := bstep (se 2 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 719689 = 539767) B539767
theorem B1407851 : Blo 370760 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B1276847 : Blo 370760 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B6814799 : Blo 370760 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B556463 : Blo 370760 556463 := bstep (se 1 (by rfl) ⟨417347, by rfl⟩ : syracuseStep 556463 = 834695) B834695
theorem B556553 : Blo 370760 556553 := bstep (se 2 (by rfl) ⟨208707, by rfl⟩ : syracuseStep 556553 = 417415) B417415
theorem B556583 : Blo 370760 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B556667 : Blo 370760 556667 := bstep (se 1 (by rfl) ⟨417500, by rfl⟩ : syracuseStep 556667 = 835001) B835001
theorem B3014267 : Blo 370760 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B556793 : Blo 370760 556793 := bstep (se 2 (by rfl) ⟨208797, by rfl⟩ : syracuseStep 556793 = 417595) B417595
theorem B851705 : Blo 370760 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B556895 : Blo 370760 556895 := bstep (se 1 (by rfl) ⟨417671, by rfl⟩ : syracuseStep 556895 = 835343) B835343
theorem B556907 : Blo 370760 556907 := bstep (se 1 (by rfl) ⟨417680, by rfl⟩ : syracuseStep 556907 = 835361) B835361
theorem B2129773 : Blo 370760 2129773 := bstep (se 3 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 2129773 = 798665) B798665
theorem B1343699 : Blo 370760 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B557321 : Blo 370760 557321 := bstep (se 2 (by rfl) ⟨208995, by rfl⟩ : syracuseStep 557321 = 417991) B417991
theorem B557423 : Blo 370760 557423 := bstep (se 1 (by rfl) ⟨418067, by rfl⟩ : syracuseStep 557423 = 836135) B836135
theorem B4063651 : Blo 370760 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B4030883 : Blo 370760 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B1278433 : Blo 370760 1278433 := bstep (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) B958825
theorem B557639 : Blo 370760 557639 := bstep (se 1 (by rfl) ⟨418229, by rfl⟩ : syracuseStep 557639 = 836459) B836459
theorem B557675 : Blo 370760 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B2261675 : Blo 370760 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B852727 : Blo 370760 852727 := bstep (se 1 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 852727 = 1279091) B1279091
theorem B4031309 : Blo 370760 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B557903 : Blo 370760 557903 := bstep (se 1 (by rfl) ⟨418427, by rfl⟩ : syracuseStep 557903 = 836855) B836855
theorem B2065247 : Blo 370760 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B6030227 : Blo 370760 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B1409993 : Blo 370760 1409993 := bstep (se 2 (by rfl) ⟨528747, by rfl⟩ : syracuseStep 1409993 = 1057495) B1057495
theorem B820187 : Blo 370760 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B558299 : Blo 370760 558299 := bstep (se 1 (by rfl) ⟨418724, by rfl⟩ : syracuseStep 558299 = 837449) B837449
theorem B1410281 : Blo 370760 1410281 := bstep (se 2 (by rfl) ⟨528855, by rfl⟩ : syracuseStep 1410281 = 1057711) B1057711
theorem B558473 : Blo 370760 558473 := bstep (se 2 (by rfl) ⟨209427, by rfl⟩ : syracuseStep 558473 = 418855) B418855
theorem B1410493 : Blo 370760 1410493 := bstep (se 3 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 1410493 = 528935) B528935
theorem B558827 : Blo 370760 558827 := bstep (se 1 (by rfl) ⟨419120, by rfl⟩ : syracuseStep 558827 = 838241) B838241
theorem B1345385 : Blo 370760 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B559055 : Blo 370760 559055 := bstep (se 1 (by rfl) ⟨419291, by rfl⟩ : syracuseStep 559055 = 838583) B838583
theorem B853967 : Blo 370760 853967 := bstep (se 1 (by rfl) ⟨640475, by rfl⟩ : syracuseStep 853967 = 1280951) B1280951
theorem B559451 : Blo 370760 559451 := bstep (se 1 (by rfl) ⟨419588, by rfl⟩ : syracuseStep 559451 = 839177) B839177
theorem B3017189 : Blo 370760 3017189 := bstep (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) B565723
theorem B559679 : Blo 370760 559679 := bstep (se 1 (by rfl) ⟨419759, by rfl⟩ : syracuseStep 559679 = 839519) B839519
theorem B559799 : Blo 370760 559799 := bstep (se 1 (by rfl) ⟨419849, by rfl⟩ : syracuseStep 559799 = 839699) B839699
theorem B3181265 : Blo 370760 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B2394947 : Blo 370760 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B560027 : Blo 370760 560027 := bstep (se 1 (by rfl) ⟨420020, by rfl⟩ : syracuseStep 560027 = 840041) B840041
theorem B560423 : Blo 370760 560423 := bstep (se 1 (by rfl) ⟨420317, by rfl⟩ : syracuseStep 560423 = 840635) B840635
theorem B560507 : Blo 370760 560507 := bstep (se 1 (by rfl) ⟨420380, by rfl⟩ : syracuseStep 560507 = 840761) B840761
theorem B4787585 : Blo 370760 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B560633 : Blo 370760 560633 := bstep (se 2 (by rfl) ⟨210237, by rfl⟩ : syracuseStep 560633 = 420475) B420475
theorem B560735 : Blo 370760 560735 := bstep (se 1 (by rfl) ⟨420551, by rfl⟩ : syracuseStep 560735 = 841103) B841103
theorem B560951 : Blo 370760 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B3018653 : Blo 370760 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B561257 : Blo 370760 561257 := bstep (se 2 (by rfl) ⟨210471, by rfl⟩ : syracuseStep 561257 = 420943) B420943
theorem B626953 : Blo 370760 626953 := bstep (se 2 (by rfl) ⟨235107, by rfl⟩ : syracuseStep 626953 = 470215) B470215
theorem B2691343 : Blo 370760 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B397607 : Blo 370760 397607 := bstep (se 1 (by rfl) ⟨298205, by rfl⟩ : syracuseStep 397607 = 596411) B596411
theorem B3412331 : Blo 370760 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B561575 : Blo 370760 561575 := bstep (se 1 (by rfl) ⟨421181, by rfl⟩ : syracuseStep 561575 = 842363) B842363
theorem B561659 : Blo 370760 561659 := bstep (se 1 (by rfl) ⟨421244, by rfl⟩ : syracuseStep 561659 = 842489) B842489
theorem B594553 : Blo 370760 594553 := bstep (se 2 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 594553 = 445915) B445915
theorem B561785 : Blo 370760 561785 := bstep (se 2 (by rfl) ⟨210669, by rfl⟩ : syracuseStep 561785 = 421339) B421339
theorem B561839 : Blo 370760 561839 := bstep (se 1 (by rfl) ⟨421379, by rfl⟩ : syracuseStep 561839 = 842759) B842759
theorem B561887 : Blo 370760 561887 := bstep (se 1 (by rfl) ⟨421415, by rfl⟩ : syracuseStep 561887 = 842831) B842831
theorem B759017 : Blo 370760 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B4232573 : Blo 370760 4232573 := bstep (se 3 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 4232573 = 1587215) B1587215
theorem B11474369 : Blo 370760 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B628411 : Blo 370760 628411 := bstep (se 1 (by rfl) ⟨471308, by rfl⟩ : syracuseStep 628411 = 942617) B942617
theorem B2004841 : Blo 370760 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B1415353 : Blo 370760 1415353 := bstep (se 2 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 1415353 = 1061515) B1061515
theorem B2824631 : Blo 370760 2824631 := bstep (se 1 (by rfl) ⟨2118473, by rfl⟩ : syracuseStep 2824631 = 4236947) B4236947
theorem B629471 : Blo 370760 629471 := bstep (se 1 (by rfl) ⟨472103, by rfl⟩ : syracuseStep 629471 = 944207) B944207
theorem B1252475 : Blo 370760 1252475 := bstep (se 1 (by rfl) ⟨939356, by rfl⟩ : syracuseStep 1252475 = 1878713) B1878713
theorem B629903 : Blo 370760 629903 := bstep (se 1 (by rfl) ⟨472427, by rfl⟩ : syracuseStep 629903 = 944855) B944855
theorem B630139 : Blo 370760 630139 := bstep (se 1 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 630139 = 945209) B945209
theorem B1252745 : Blo 370760 1252745 := bstep (se 2 (by rfl) ⟨469779, by rfl⟩ : syracuseStep 1252745 = 939559) B939559
theorem B597385 : Blo 370760 597385 := bstep (se 2 (by rfl) ⟨224019, by rfl⟩ : syracuseStep 597385 = 448039) B448039
theorem B3382879 : Blo 370760 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B3186323 : Blo 370760 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B1810183 : Blo 370760 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B1515311 : Blo 370760 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B1253177 : Blo 370760 1253177 := bstep (se 2 (by rfl) ⟨469941, by rfl⟩ : syracuseStep 1253177 = 939883) B939883
theorem B1745107 : Blo 370760 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B1254041 : Blo 370760 1254041 := bstep (se 2 (by rfl) ⟨470265, by rfl⟩ : syracuseStep 1254041 = 940531) B940531
theorem B631631 : Blo 370760 631631 := bstep (se 1 (by rfl) ⟨473723, by rfl⟩ : syracuseStep 631631 = 947447) B947447
theorem B959585 : Blo 370760 959585 := bstep (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) B719689
theorem B4826305 : Blo 370760 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B795881 : Blo 370760 795881 := bstep (se 2 (by rfl) ⟨298455, by rfl⟩ : syracuseStep 795881 = 596911) B596911
theorem B1549729 : Blo 370760 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B8038045 : Blo 370760 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B1255553 : Blo 370760 1255553 := bstep (se 2 (by rfl) ⟨470832, by rfl⟩ : syracuseStep 1255553 = 941665) B941665
theorem B1419545 : Blo 370760 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B370975 : Blo 370760 370975 := bstep (se 1 (by rfl) ⟨278231, by rfl⟩ : syracuseStep 370975 = 556463) B556463
theorem B371035 : Blo 370760 371035 := bstep (se 1 (by rfl) ⟨278276, by rfl⟩ : syracuseStep 371035 = 556553) B556553
theorem B371055 : Blo 370760 371055 := bstep (se 1 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 371055 = 556583) B556583
theorem B469415 : Blo 370760 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B371111 : Blo 370760 371111 := bstep (se 1 (by rfl) ⟨278333, by rfl⟩ : syracuseStep 371111 = 556667) B556667
theorem B797111 : Blo 370760 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B371195 : Blo 370760 371195 := bstep (se 1 (by rfl) ⟨278396, by rfl⟩ : syracuseStep 371195 = 556793) B556793
theorem B1255931 : Blo 370760 1255931 := bstep (se 1 (by rfl) ⟨941948, by rfl⟩ : syracuseStep 1255931 = 1883897) B1883897
theorem B567803 : Blo 370760 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B469567 : Blo 370760 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B371263 : Blo 370760 371263 := bstep (se 1 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 371263 = 556895) B556895
theorem B371271 : Blo 370760 371271 := bstep (se 1 (by rfl) ⟨278453, by rfl⟩ : syracuseStep 371271 = 556907) B556907
theorem B797359 : Blo 370760 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B7383737 : Blo 370760 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B371423 : Blo 370760 371423 := bstep (se 1 (by rfl) ⟨278567, by rfl⟩ : syracuseStep 371423 = 557135) B557135
theorem B469739 : Blo 370760 469739 := bstep (se 1 (by rfl) ⟨352304, by rfl⟩ : syracuseStep 469739 = 704609) B704609
theorem B371503 : Blo 370760 371503 := bstep (se 1 (by rfl) ⟨278627, by rfl⟩ : syracuseStep 371503 = 557255) B557255
theorem B4795271 : Blo 370760 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B371611 : Blo 370760 371611 := bstep (se 1 (by rfl) ⟨278708, by rfl⟩ : syracuseStep 371611 = 557417) B557417
theorem B1256363 : Blo 370760 1256363 := bstep (se 1 (by rfl) ⟨942272, by rfl⟩ : syracuseStep 1256363 = 1884545) B1884545
theorem B371663 : Blo 370760 371663 := bstep (se 1 (by rfl) ⟨278747, by rfl⟩ : syracuseStep 371663 = 557495) B557495
theorem B371687 : Blo 370760 371687 := bstep (se 1 (by rfl) ⟨278765, by rfl⟩ : syracuseStep 371687 = 557531) B557531
theorem B896039 : Blo 370760 896039 := bstep (se 1 (by rfl) ⟨672029, by rfl⟩ : syracuseStep 896039 = 1344059) B1344059
theorem B371999 : Blo 370760 371999 := bstep (se 1 (by rfl) ⟨278999, by rfl⟩ : syracuseStep 371999 = 557999) B557999
theorem B6368543 : Blo 370760 6368543 := bstep (se 1 (by rfl) ⟨4776407, by rfl⟩ : syracuseStep 6368543 = 9552815) B9552815
theorem B372059 : Blo 370760 372059 := bstep (se 1 (by rfl) ⟨279044, by rfl⟩ : syracuseStep 372059 = 558089) B558089
theorem B372079 : Blo 370760 372079 := bstep (se 1 (by rfl) ⟨279059, by rfl⟩ : syracuseStep 372079 = 558119) B558119
theorem B10136951 : Blo 370760 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B372135 : Blo 370760 372135 := bstep (se 1 (by rfl) ⟨279101, by rfl⟩ : syracuseStep 372135 = 558203) B558203
theorem B1256903 : Blo 370760 1256903 := bstep (se 1 (by rfl) ⟨942677, by rfl⟩ : syracuseStep 1256903 = 1885355) B1885355
theorem B372219 : Blo 370760 372219 := bstep (se 1 (by rfl) ⟨279164, by rfl⟩ : syracuseStep 372219 = 558329) B558329
theorem B372287 : Blo 370760 372287 := bstep (se 1 (by rfl) ⟨279215, by rfl⟩ : syracuseStep 372287 = 558431) B558431
theorem B372295 : Blo 370760 372295 := bstep (se 1 (by rfl) ⟨279221, by rfl⟩ : syracuseStep 372295 = 558443) B558443
theorem B1584755 : Blo 370760 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B470711 : Blo 370760 470711 := bstep (se 1 (by rfl) ⟨353033, by rfl⟩ : syracuseStep 470711 = 706067) B706067
theorem B372447 : Blo 370760 372447 := bstep (se 1 (by rfl) ⟨279335, by rfl⟩ : syracuseStep 372447 = 558671) B558671
theorem B1257227 : Blo 370760 1257227 := bstep (se 1 (by rfl) ⟨942920, by rfl⟩ : syracuseStep 1257227 = 1885841) B1885841
theorem B372527 : Blo 370760 372527 := bstep (se 1 (by rfl) ⟨279395, by rfl⟩ : syracuseStep 372527 = 558791) B558791
theorem B470863 : Blo 370760 470863 := bstep (se 1 (by rfl) ⟨353147, by rfl⟩ : syracuseStep 470863 = 706295) B706295
theorem B1421185 : Blo 370760 1421185 := bstep (se 2 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 1421185 = 1065889) B1065889
theorem B372635 : Blo 370760 372635 := bstep (se 1 (by rfl) ⟨279476, by rfl⟩ : syracuseStep 372635 = 558953) B558953
theorem B372687 : Blo 370760 372687 := bstep (se 1 (by rfl) ⟨279515, by rfl⟩ : syracuseStep 372687 = 559031) B559031
theorem B372711 : Blo 370760 372711 := bstep (se 1 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 372711 = 559067) B559067
theorem B1257497 : Blo 370760 1257497 := bstep (se 2 (by rfl) ⟨471561, by rfl⟩ : syracuseStep 1257497 = 943123) B943123
theorem B373023 : Blo 370760 373023 := bstep (se 1 (by rfl) ⟨279767, by rfl⟩ : syracuseStep 373023 = 559535) B559535
theorem B373083 : Blo 370760 373083 := bstep (se 1 (by rfl) ⟨279812, by rfl⟩ : syracuseStep 373083 = 559625) B559625
theorem B373103 : Blo 370760 373103 := bstep (se 1 (by rfl) ⟨279827, by rfl⟩ : syracuseStep 373103 = 559655) B559655
theorem B373159 : Blo 370760 373159 := bstep (se 1 (by rfl) ⟨279869, by rfl⟩ : syracuseStep 373159 = 559739) B559739
theorem B1880495 : Blo 370760 1880495 := bstep (se 1 (by rfl) ⟨1410371, by rfl⟩ : syracuseStep 1880495 = 2820743) B2820743
theorem B7188911 : Blo 370760 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B373243 : Blo 370760 373243 := bstep (se 1 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 373243 = 559865) B559865
theorem B2863667 : Blo 370760 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B373311 : Blo 370760 373311 := bstep (se 1 (by rfl) ⟨279983, by rfl⟩ : syracuseStep 373311 = 559967) B559967
theorem B373319 : Blo 370760 373319 := bstep (se 1 (by rfl) ⟨279989, by rfl⟩ : syracuseStep 373319 = 559979) B559979
theorem B1421945 : Blo 370760 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B3584735 : Blo 370760 3584735 := bstep (se 1 (by rfl) ⟨2688551, by rfl⟩ : syracuseStep 3584735 = 5377103) B5377103
theorem B373471 : Blo 370760 373471 := bstep (se 1 (by rfl) ⟨280103, by rfl⟩ : syracuseStep 373471 = 560207) B560207
theorem B373551 : Blo 370760 373551 := bstep (se 1 (by rfl) ⟨280163, by rfl⟩ : syracuseStep 373551 = 560327) B560327
theorem B373659 : Blo 370760 373659 := bstep (se 1 (by rfl) ⟨280244, by rfl⟩ : syracuseStep 373659 = 560489) B560489
theorem B373711 : Blo 370760 373711 := bstep (se 1 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 373711 = 560567) B560567
theorem B373735 : Blo 370760 373735 := bstep (se 1 (by rfl) ⟨280301, by rfl⟩ : syracuseStep 373735 = 560603) B560603
theorem B1422461 : Blo 370760 1422461 := bstep (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) B533423
theorem B1258739 : Blo 370760 1258739 := bstep (se 1 (by rfl) ⟨944054, by rfl⟩ : syracuseStep 1258739 = 1888109) B1888109
theorem B374047 : Blo 370760 374047 := bstep (se 1 (by rfl) ⟨280535, by rfl⟩ : syracuseStep 374047 = 561071) B561071
theorem B374107 : Blo 370760 374107 := bstep (se 1 (by rfl) ⟨280580, by rfl⟩ : syracuseStep 374107 = 561161) B561161
theorem B1258847 : Blo 370760 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B374127 : Blo 370760 374127 := bstep (se 1 (by rfl) ⟨280595, by rfl⟩ : syracuseStep 374127 = 561191) B561191
theorem B1881467 : Blo 370760 1881467 := bstep (se 1 (by rfl) ⟨1411100, by rfl⟩ : syracuseStep 1881467 = 2822201) B2822201
theorem B6337925 : Blo 370760 6337925 := bstep (se 4 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 6337925 = 1188361) B1188361
theorem B374183 : Blo 370760 374183 := bstep (se 1 (by rfl) ⟨280637, by rfl⟩ : syracuseStep 374183 = 561275) B561275
theorem B374267 : Blo 370760 374267 := bstep (se 1 (by rfl) ⟨280700, by rfl⟩ : syracuseStep 374267 = 561401) B561401
theorem B374335 : Blo 370760 374335 := bstep (se 1 (by rfl) ⟨280751, by rfl⟩ : syracuseStep 374335 = 561503) B561503
theorem B374343 : Blo 370760 374343 := bstep (se 1 (by rfl) ⟨280757, by rfl⟩ : syracuseStep 374343 = 561515) B561515
theorem B374495 : Blo 370760 374495 := bstep (se 1 (by rfl) ⟨280871, by rfl⟩ : syracuseStep 374495 = 561743) B561743
theorem B374575 : Blo 370760 374575 := bstep (se 1 (by rfl) ⟨280931, by rfl⟩ : syracuseStep 374575 = 561863) B561863
theorem B3389303 : Blo 370760 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B374683 : Blo 370760 374683 := bstep (se 1 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 374683 = 562025) B562025
theorem B374735 : Blo 370760 374735 := bstep (se 1 (by rfl) ⟨281051, by rfl⟩ : syracuseStep 374735 = 562103) B562103
theorem B374759 : Blo 370760 374759 := bstep (se 1 (by rfl) ⟨281069, by rfl⟩ : syracuseStep 374759 = 562139) B562139
theorem B4962637 : Blo 370760 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B473455 : Blo 370760 473455 := bstep (se 1 (by rfl) ⟨355091, by rfl⟩ : syracuseStep 473455 = 710183) B710183
theorem B1882763 : Blo 370760 1882763 := bstep (se 1 (by rfl) ⟨1412072, by rfl⟩ : syracuseStep 1882763 = 2824145) B2824145
theorem B5094251 : Blo 370760 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B1784695 : Blo 370760 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B1260413 : Blo 370760 1260413 := bstep (se 3 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 1260413 = 472655) B472655
theorem B834551 : Blo 370760 834551 := bstep (se 1 (by rfl) ⟨625913, by rfl⟩ : syracuseStep 834551 = 1251827) B1251827
theorem B1260683 : Blo 370760 1260683 := bstep (se 1 (by rfl) ⟨945512, by rfl⟩ : syracuseStep 1260683 = 1891025) B1891025
theorem B834911 : Blo 370760 834911 := bstep (se 1 (by rfl) ⟨626183, by rfl⟩ : syracuseStep 834911 = 1252367) B1252367
theorem B2866747 : Blo 370760 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1621619 : Blo 370760 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B835307 : Blo 370760 835307 := bstep (se 1 (by rfl) ⟨626480, by rfl⟩ : syracuseStep 835307 = 1252961) B1252961
theorem B835433 : Blo 370760 835433 := bstep (se 2 (by rfl) ⟨313287, by rfl⟩ : syracuseStep 835433 = 626575) B626575
theorem B2834351 : Blo 370760 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B377255 : Blo 370760 377255 := bstep (se 1 (by rfl) ⟨282941, by rfl⟩ : syracuseStep 377255 = 565883) B565883
theorem B2376161 : Blo 370760 2376161 := bstep (se 2 (by rfl) ⟨891060, by rfl⟩ : syracuseStep 2376161 = 1782121) B1782121
theorem B705019 : Blo 370760 705019 := bstep (se 1 (by rfl) ⟨528764, by rfl⟩ : syracuseStep 705019 = 1057529) B1057529
theorem B1786369 : Blo 370760 1786369 := bstep (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) B1339777
theorem B1786387 : Blo 370760 1786387 := bstep (se 1 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 1786387 = 2679581) B2679581
theorem B705095 : Blo 370760 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B1589881 : Blo 370760 1589881 := bstep (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) B1192411
theorem B836279 : Blo 370760 836279 := bstep (se 1 (by rfl) ⟨627209, by rfl⟩ : syracuseStep 836279 = 1254419) B1254419
theorem B1262303 : Blo 370760 1262303 := bstep (se 1 (by rfl) ⟨946727, by rfl⟩ : syracuseStep 1262303 = 1893455) B1893455
theorem B836495 : Blo 370760 836495 := bstep (se 1 (by rfl) ⟨627371, by rfl⟩ : syracuseStep 836495 = 1254743) B1254743
theorem B1262735 : Blo 370760 1262735 := bstep (se 1 (by rfl) ⟨947051, by rfl⟩ : syracuseStep 1262735 = 1894103) B1894103
theorem B3196097 : Blo 370760 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B705991 : Blo 370760 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B837215 : Blo 370760 837215 := bstep (se 1 (by rfl) ⟨627911, by rfl⟩ : syracuseStep 837215 = 1255823) B1255823
theorem B1590941 : Blo 370760 1590941 := bstep (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) B596603
theorem B837431 : Blo 370760 837431 := bstep (se 1 (by rfl) ⟨628073, by rfl⟩ : syracuseStep 837431 = 1256147) B1256147
theorem B1099727 : Blo 370760 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B837737 : Blo 370760 837737 := bstep (se 2 (by rfl) ⟨314151, by rfl⟩ : syracuseStep 837737 = 628303) B628303
theorem B1263869 : Blo 370760 1263869 := bstep (se 3 (by rfl) ⟨236975, by rfl⟩ : syracuseStep 1263869 = 473951) B473951
theorem B1886489 : Blo 370760 1886489 := bstep (se 2 (by rfl) ⟨707433, by rfl⟩ : syracuseStep 1886489 = 1414867) B1414867
theorem B838223 : Blo 370760 838223 := bstep (se 1 (by rfl) ⟨628667, by rfl⟩ : syracuseStep 838223 = 1257335) B1257335
theorem B838367 : Blo 370760 838367 := bstep (se 1 (by rfl) ⟨628775, by rfl⟩ : syracuseStep 838367 = 1257551) B1257551
theorem B674639 : Blo 370760 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B838619 : Blo 370760 838619 := bstep (se 1 (by rfl) ⟨628964, by rfl⟩ : syracuseStep 838619 = 1257929) B1257929
theorem B1264679 : Blo 370760 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B838799 : Blo 370760 838799 := bstep (se 1 (by rfl) ⟨629099, by rfl⟩ : syracuseStep 838799 = 1258199) B1258199
theorem B838889 : Blo 370760 838889 := bstep (se 2 (by rfl) ⟨314583, by rfl⟩ : syracuseStep 838889 = 629167) B629167
theorem B838943 : Blo 370760 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B2116925 : Blo 370760 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B25873843 : Blo 370760 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B478715 : Blo 370760 478715 := bstep (se 1 (by rfl) ⟨359036, by rfl⟩ : syracuseStep 478715 = 718073) B718073
theorem B16305953 : Blo 370760 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B839465 : Blo 370760 839465 := bstep (se 2 (by rfl) ⟨314799, by rfl⟩ : syracuseStep 839465 = 629599) B629599
theorem B577487 : Blo 370760 577487 := bstep (se 1 (by rfl) ⟨433115, by rfl⟩ : syracuseStep 577487 = 866231) B866231
theorem B938567 : Blo 370760 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B4543199 : Blo 370760 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B840527 : Blo 370760 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B3199823 : Blo 370760 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B1889243 : Blo 370760 1889243 := bstep (se 1 (by rfl) ⟨1416932, by rfl⟩ : syracuseStep 1889243 = 2833865) B2833865
theorem B840743 : Blo 370760 840743 := bstep (se 1 (by rfl) ⟨630557, by rfl⟩ : syracuseStep 840743 = 1261115) B1261115
theorem B1889405 : Blo 370760 1889405 := bstep (se 3 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 1889405 = 708527) B708527
theorem B2839697 : Blo 370760 2839697 := bstep (se 2 (by rfl) ⟨1064886, by rfl⟩ : syracuseStep 2839697 = 2129773) B2129773
theorem B840923 : Blo 370760 840923 := bstep (se 1 (by rfl) ⟨630692, by rfl⟩ : syracuseStep 840923 = 1261385) B1261385
theorem B709985 : Blo 370760 709985 := bstep (se 2 (by rfl) ⟨266244, by rfl⟩ : syracuseStep 709985 = 532489) B532489
theorem B841121 : Blo 370760 841121 := bstep (se 2 (by rfl) ⟨315420, by rfl⟩ : syracuseStep 841121 = 630841) B630841
theorem B1889729 : Blo 370760 1889729 := bstep (se 2 (by rfl) ⟨708648, by rfl⟩ : syracuseStep 1889729 = 1417297) B1417297
theorem B710137 : Blo 370760 710137 := bstep (se 2 (by rfl) ⟨266301, by rfl⟩ : syracuseStep 710137 = 532603) B532603
theorem B448183 : Blo 370760 448183 := bstep (se 1 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 448183 = 672275) B672275
theorem B710441 : Blo 370760 710441 := bstep (se 2 (by rfl) ⟨266415, by rfl⟩ : syracuseStep 710441 = 532831) B532831
theorem B808751 : Blo 370760 808751 := bstep (se 1 (by rfl) ⟨606563, by rfl⟩ : syracuseStep 808751 = 1213127) B1213127
theorem B939833 : Blo 370760 939833 := bstep (se 2 (by rfl) ⟨352437, by rfl⟩ : syracuseStep 939833 = 704875) B704875
theorem B841679 : Blo 370760 841679 := bstep (se 1 (by rfl) ⟨631259, by rfl⟩ : syracuseStep 841679 = 1262519) B1262519
theorem B645385 : Blo 370760 645385 := bstep (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) B484039
theorem B4512023 : Blo 370760 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B842057 : Blo 370760 842057 := bstep (se 2 (by rfl) ⟨315771, by rfl⟩ : syracuseStep 842057 = 631543) B631543
theorem B842075 : Blo 370760 842075 := bstep (se 1 (by rfl) ⟨631556, by rfl⟩ : syracuseStep 842075 = 1263113) B1263113
theorem B3168827 : Blo 370760 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B4774463 : Blo 370760 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B1694287 : Blo 370760 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B6576815 : Blo 370760 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B711443 : Blo 370760 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B842651 : Blo 370760 842651 := bstep (se 1 (by rfl) ⟨631988, by rfl⟩ : syracuseStep 842651 = 1263977) B1263977
theorem B842849 : Blo 370760 842849 := bstep (se 2 (by rfl) ⟨316068, by rfl⟩ : syracuseStep 842849 = 632137) B632137
theorem B941179 : Blo 370760 941179 := bstep (se 1 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 941179 = 1411769) B1411769
theorem B2415781 : Blo 370760 2415781 := bstep (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) B452959
theorem B5790937 : Blo 370760 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B843047 : Blo 370760 843047 := bstep (se 1 (by rfl) ⟨632285, by rfl⟩ : syracuseStep 843047 = 1264571) B1264571
theorem B2842127 : Blo 370760 2842127 := bstep (se 1 (by rfl) ⟨2131595, by rfl⟩ : syracuseStep 2842127 = 4263191) B4263191
theorem B417343 : Blo 370760 417343 := bstep (se 1 (by rfl) ⟨313007, by rfl⟩ : syracuseStep 417343 = 626015) B626015
theorem B2121299 : Blo 370760 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B12902003 : Blo 370760 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B1269785 : Blo 370760 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B418171 : Blo 370760 418171 := bstep (se 1 (by rfl) ⟨313628, by rfl⟩ : syracuseStep 418171 = 627257) B627257
theorem B942587 : Blo 370760 942587 := bstep (se 1 (by rfl) ⟨706940, by rfl⟩ : syracuseStep 942587 = 1413881) B1413881
theorem B1204919 : Blo 370760 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B418639 : Blo 370760 418639 := bstep (se 1 (by rfl) ⟨313979, by rfl⟩ : syracuseStep 418639 = 627959) B627959
theorem B1598287 : Blo 370760 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B2843585 : Blo 370760 2843585 := bstep (se 2 (by rfl) ⟨1066344, by rfl⟩ : syracuseStep 2843585 = 2132689) B2132689
theorem B2548739 : Blo 370760 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B3236867 : Blo 370760 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B1598561 : Blo 370760 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B419035 : Blo 370760 419035 := bstep (se 1 (by rfl) ⟨314276, by rfl⟩ : syracuseStep 419035 = 628553) B628553
theorem B3007853 : Blo 370760 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B3827087 : Blo 370760 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B943559 : Blo 370760 943559 := bstep (se 1 (by rfl) ⟨707669, by rfl⟩ : syracuseStep 943559 = 1415339) B1415339
theorem B943609 : Blo 370760 943609 := bstep (se 2 (by rfl) ⟨353853, by rfl⟩ : syracuseStep 943609 = 707707) B707707
theorem B419323 : Blo 370760 419323 := bstep (se 1 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 419323 = 628985) B628985
theorem B419503 : Blo 370760 419503 := bstep (se 1 (by rfl) ⟨314627, by rfl⟩ : syracuseStep 419503 = 629255) B629255
theorem B943913 : Blo 370760 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B3172243 : Blo 370760 3172243 := bstep (se 1 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 3172243 = 4758365) B4758365
theorem B419791 : Blo 370760 419791 := bstep (se 1 (by rfl) ⟨314843, by rfl⟩ : syracuseStep 419791 = 629687) B629687
theorem B944257 : Blo 370760 944257 := bstep (se 2 (by rfl) ⟨354096, by rfl⟩ : syracuseStep 944257 = 708193) B708193
theorem B420187 : Blo 370760 420187 := bstep (se 1 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 420187 = 630281) B630281
theorem B1796519 : Blo 370760 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B420295 : Blo 370760 420295 := bstep (se 1 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 420295 = 630443) B630443
theorem B2878199 : Blo 370760 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B420655 : Blo 370760 420655 := bstep (se 1 (by rfl) ⟨315491, by rfl⟩ : syracuseStep 420655 = 630983) B630983
theorem B420763 : Blo 370760 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B945067 : Blo 370760 945067 := bstep (se 1 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 945067 = 1417601) B1417601
theorem B1338407 : Blo 370760 1338407 := bstep (se 1 (by rfl) ⟨1003805, by rfl⟩ : syracuseStep 1338407 = 2007611) B2007611
theorem B3173579 : Blo 370760 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B945371 : Blo 370760 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B421159 : Blo 370760 421159 := bstep (se 1 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 421159 = 631739) B631739
theorem B945503 : Blo 370760 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B486767 : Blo 370760 486767 := bstep (se 1 (by rfl) ⟨365075, by rfl⟩ : syracuseStep 486767 = 730151) B730151
theorem B421231 : Blo 370760 421231 := bstep (se 1 (by rfl) ⟨315923, by rfl⟩ : syracuseStep 421231 = 631847) B631847
theorem B1437115 : Blo 370760 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B421447 : Blo 370760 421447 := bstep (se 1 (by rfl) ⟨316085, by rfl⟩ : syracuseStep 421447 = 632171) B632171
theorem B946201 : Blo 370760 946201 := bstep (se 2 (by rfl) ⟨354825, by rfl⟩ : syracuseStep 946201 = 709651) B709651
theorem B4255901 : Blo 370760 4255901 := bstep (se 3 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 4255901 = 1595963) B1595963
theorem B946505 : Blo 370760 946505 := bstep (se 2 (by rfl) ⟨354939, by rfl⟩ : syracuseStep 946505 = 709879) B709879
theorem B4518251 : Blo 370760 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B24080921 : Blo 370760 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B1274591 : Blo 370760 1274591 := bstep (se 1 (by rfl) ⟨955943, by rfl⟩ : syracuseStep 1274591 = 1911887) B1911887
theorem B1340239 : Blo 370760 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B1340513 : Blo 370760 1340513 := bstep (se 2 (by rfl) ⟨502692, by rfl⟩ : syracuseStep 1340513 = 1005385) B1005385
theorem B3634301 : Blo 370760 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B1341289 : Blo 370760 1341289 := bstep (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) B1005967
theorem B13727981 : Blo 370760 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B3832343 : Blo 370760 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B556265 : Blo 370760 556265 := bstep (se 2 (by rfl) ⟨208599, by rfl⟩ : syracuseStep 556265 = 417199) B417199
theorem B556319 : Blo 370760 556319 := bstep (se 1 (by rfl) ⟨417239, by rfl⟩ : syracuseStep 556319 = 834479) B834479
theorem B851231 : Blo 370760 851231 := bstep (se 1 (by rfl) ⟨638423, by rfl⟩ : syracuseStep 851231 = 1276847) B1276847
theorem B556487 : Blo 370760 556487 := bstep (se 1 (by rfl) ⟨417365, by rfl⟩ : syracuseStep 556487 = 834731) B834731
theorem B556841 : Blo 370760 556841 := bstep (se 2 (by rfl) ⟨208815, by rfl⟩ : syracuseStep 556841 = 417631) B417631
theorem B556847 : Blo 370760 556847 := bstep (se 1 (by rfl) ⟨417635, by rfl⟩ : syracuseStep 556847 = 835271) B835271
theorem B2687255 : Blo 370760 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B1507783 : Blo 370760 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B557519 : Blo 370760 557519 := bstep (se 1 (by rfl) ⟨418139, by rfl⟩ : syracuseStep 557519 = 836279) B836279
theorem B557561 : Blo 370760 557561 := bstep (se 2 (by rfl) ⟨209085, by rfl⟩ : syracuseStep 557561 = 418171) B418171
theorem B2687539 : Blo 370760 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B1376831 : Blo 370760 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B557663 : Blo 370760 557663 := bstep (se 1 (by rfl) ⟨418247, by rfl⟩ : syracuseStep 557663 = 836495) B836495
theorem B1704577 : Blo 370760 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B2130731 : Blo 370760 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B558143 : Blo 370760 558143 := bstep (se 1 (by rfl) ⟨418607, by rfl⟩ : syracuseStep 558143 = 837215) B837215
theorem B9307237 : Blo 370760 9307237 := bstep (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) B1745107
theorem B558185 : Blo 370760 558185 := bstep (se 2 (by rfl) ⟨209319, by rfl⟩ : syracuseStep 558185 = 418639) B418639
theorem B2131049 : Blo 370760 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B558287 : Blo 370760 558287 := bstep (se 1 (by rfl) ⟨418715, by rfl⟩ : syracuseStep 558287 = 837431) B837431
theorem B558491 : Blo 370760 558491 := bstep (se 1 (by rfl) ⟨418868, by rfl⟩ : syracuseStep 558491 = 837737) B837737
theorem B558713 : Blo 370760 558713 := bstep (se 2 (by rfl) ⟨209517, by rfl⟩ : syracuseStep 558713 = 419035) B419035
theorem B558815 : Blo 370760 558815 := bstep (se 1 (by rfl) ⟨419111, by rfl⟩ : syracuseStep 558815 = 838223) B838223
theorem B558911 : Blo 370760 558911 := bstep (se 1 (by rfl) ⟨419183, by rfl⟩ : syracuseStep 558911 = 838367) B838367
theorem B2066305 : Blo 370760 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B559079 : Blo 370760 559079 := bstep (se 1 (by rfl) ⟨419309, by rfl⟩ : syracuseStep 559079 = 838619) B838619
theorem B559097 : Blo 370760 559097 := bstep (se 2 (by rfl) ⟨209661, by rfl⟩ : syracuseStep 559097 = 419323) B419323
theorem B559199 : Blo 370760 559199 := bstep (se 1 (by rfl) ⟨419399, by rfl⟩ : syracuseStep 559199 = 838799) B838799
theorem B559259 : Blo 370760 559259 := bstep (se 1 (by rfl) ⟨419444, by rfl⟩ : syracuseStep 559259 = 838889) B838889
theorem B559295 : Blo 370760 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B10717393 : Blo 370760 10717393 := bstep (se 2 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 10717393 = 8038045) B8038045
theorem B1411283 : Blo 370760 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B559337 : Blo 370760 559337 := bstep (se 2 (by rfl) ⟨209751, by rfl⟩ : syracuseStep 559337 = 419503) B419503
theorem B4229657 : Blo 370760 4229657 := bstep (se 2 (by rfl) ⟨1586121, by rfl⟩ : syracuseStep 4229657 = 3172243) B3172243
theorem B559643 : Blo 370760 559643 := bstep (se 1 (by rfl) ⟨419732, by rfl⟩ : syracuseStep 559643 = 839465) B839465
theorem B559721 : Blo 370760 559721 := bstep (se 2 (by rfl) ⟨209895, by rfl⟩ : syracuseStep 559721 = 419791) B419791
theorem B2558893 : Blo 370760 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B625711 : Blo 370760 625711 := bstep (se 1 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 625711 = 938567) B938567
theorem B560249 : Blo 370760 560249 := bstep (se 2 (by rfl) ⟨210093, by rfl⟩ : syracuseStep 560249 = 420187) B420187
theorem B560351 : Blo 370760 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B2133215 : Blo 370760 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B560393 : Blo 370760 560393 := bstep (se 2 (by rfl) ⟨210147, by rfl⟩ : syracuseStep 560393 = 420295) B420295
theorem B560495 : Blo 370760 560495 := bstep (se 1 (by rfl) ⟨420371, by rfl⟩ : syracuseStep 560495 = 840743) B840743
theorem B626089 : Blo 370760 626089 := bstep (se 2 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 626089 = 469567) B469567
theorem B560615 : Blo 370760 560615 := bstep (se 1 (by rfl) ⟨420461, by rfl⟩ : syracuseStep 560615 = 840923) B840923
theorem B2821715 : Blo 370760 2821715 := bstep (se 1 (by rfl) ⟨2116286, by rfl⟩ : syracuseStep 2821715 = 4232573) B4232573
theorem B560747 : Blo 370760 560747 := bstep (se 1 (by rfl) ⟨420560, by rfl⟩ : syracuseStep 560747 = 841121) B841121
theorem B560873 : Blo 370760 560873 := bstep (se 2 (by rfl) ⟨210327, by rfl⟩ : syracuseStep 560873 = 420655) B420655
theorem B561017 : Blo 370760 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B626555 : Blo 370760 626555 := bstep (se 1 (by rfl) ⟨469916, by rfl⟩ : syracuseStep 626555 = 939833) B939833
theorem B561119 : Blo 370760 561119 := bstep (se 1 (by rfl) ⟨420839, by rfl⟩ : syracuseStep 561119 = 841679) B841679
theorem B561371 : Blo 370760 561371 := bstep (se 1 (by rfl) ⟨421028, by rfl⟩ : syracuseStep 561371 = 842057) B842057
theorem B561383 : Blo 370760 561383 := bstep (se 1 (by rfl) ⟨421037, by rfl⟩ : syracuseStep 561383 = 842075) B842075
theorem B3182975 : Blo 370760 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B561545 : Blo 370760 561545 := bstep (se 2 (by rfl) ⟨210579, by rfl⟩ : syracuseStep 561545 = 421159) B421159
theorem B561641 : Blo 370760 561641 := bstep (se 2 (by rfl) ⟨210615, by rfl⟩ : syracuseStep 561641 = 421231) B421231
theorem B561767 : Blo 370760 561767 := bstep (se 1 (by rfl) ⟨421325, by rfl⟩ : syracuseStep 561767 = 842651) B842651
theorem B561899 : Blo 370760 561899 := bstep (se 1 (by rfl) ⟨421424, by rfl⟩ : syracuseStep 561899 = 842849) B842849
theorem B561929 : Blo 370760 561929 := bstep (se 2 (by rfl) ⟨210723, by rfl⟩ : syracuseStep 561929 = 421447) B421447
theorem B562031 : Blo 370760 562031 := bstep (se 1 (by rfl) ⟨421523, by rfl⟩ : syracuseStep 562031 = 843047) B843047
theorem B1414199 : Blo 370760 1414199 := bstep (se 1 (by rfl) ⟨1060649, by rfl⟩ : syracuseStep 1414199 = 2121299) B2121299
theorem B627817 : Blo 370760 627817 := bstep (se 2 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 627817 = 470863) B470863
theorem B628391 : Blo 370760 628391 := bstep (se 1 (by rfl) ⟨471293, by rfl⟩ : syracuseStep 628391 = 942587) B942587
theorem B530587 : Blo 370760 530587 := bstep (se 1 (by rfl) ⟨397940, by rfl⟩ : syracuseStep 530587 = 795881) B795881
theorem B792737 : Blo 370760 792737 := bstep (se 2 (by rfl) ⟨297276, by rfl⟩ : syracuseStep 792737 = 594553) B594553
theorem B2005235 : Blo 370760 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B629039 : Blo 370760 629039 := bstep (se 1 (by rfl) ⟨471779, by rfl⟩ : syracuseStep 629039 = 943559) B943559
theorem B1251773 : Blo 370760 1251773 := bstep (se 3 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 1251773 = 469415) B469415
theorem B629275 : Blo 370760 629275 := bstep (se 1 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 629275 = 943913) B943913
theorem B1514141 : Blo 370760 1514141 := bstep (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) B567803
theorem B531407 : Blo 370760 531407 := bstep (se 1 (by rfl) ⟨398555, by rfl⟩ : syracuseStep 531407 = 797111) B797111
theorem B4922491 : Blo 370760 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B1252637 : Blo 370760 1252637 := bstep (se 3 (by rfl) ⟨234869, by rfl⟩ : syracuseStep 1252637 = 469739) B469739
theorem B892271 : Blo 370760 892271 := bstep (se 1 (by rfl) ⟨669203, by rfl⟩ : syracuseStep 892271 = 1338407) B1338407
theorem B597359 : Blo 370760 597359 := bstep (se 1 (by rfl) ⟨448019, by rfl⟩ : syracuseStep 597359 = 896039) B896039
theorem B630247 : Blo 370760 630247 := bstep (se 1 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 630247 = 945371) B945371
theorem B630335 : Blo 370760 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B6757967 : Blo 370760 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1056503 : Blo 370760 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B631003 : Blo 370760 631003 := bstep (se 1 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 631003 = 946505) B946505
theorem B1253663 : Blo 370760 1253663 := bstep (se 1 (by rfl) ⟨940247, by rfl⟩ : syracuseStep 1253663 = 1880495) B1880495
theorem B4792607 : Blo 370760 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B860513 : Blo 370760 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B1909111 : Blo 370760 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B631273 : Blo 370760 631273 := bstep (se 2 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 631273 = 473455) B473455
theorem B893675 : Blo 370760 893675 := bstep (se 1 (by rfl) ⟨670256, by rfl⟩ : syracuseStep 893675 = 1340513) B1340513
theorem B1254311 : Blo 370760 1254311 := bstep (se 1 (by rfl) ⟨940733, by rfl⟩ : syracuseStep 1254311 = 1881467) B1881467
theorem B9151987 : Blo 370760 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B1254905 : Blo 370760 1254905 := bstep (se 2 (by rfl) ⟨470589, by rfl⟩ : syracuseStep 1254905 = 941179) B941179
theorem B3221041 : Blo 370760 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1255175 : Blo 370760 1255175 := bstep (se 1 (by rfl) ⟨941381, by rfl⟩ : syracuseStep 1255175 = 1882763) B1882763
theorem B1255229 : Blo 370760 1255229 := bstep (se 3 (by rfl) ⟨235355, by rfl⟩ : syracuseStep 1255229 = 470711) B470711
theorem B796513 : Blo 370760 796513 := bstep (se 2 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 796513 = 597385) B597385
theorem B10692485 : Blo 370760 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B7153541 : Blo 370760 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B370843 : Blo 370760 370843 := bstep (se 1 (by rfl) ⟨278132, by rfl⟩ : syracuseStep 370843 = 556265) B556265
theorem B370879 : Blo 370760 370879 := bstep (se 1 (by rfl) ⟨278159, by rfl⟩ : syracuseStep 370879 = 556319) B556319
theorem B567487 : Blo 370760 567487 := bstep (se 1 (by rfl) ⟨425615, by rfl⟩ : syracuseStep 567487 = 851231) B851231
theorem B370991 : Blo 370760 370991 := bstep (se 1 (by rfl) ⟨278243, by rfl⟩ : syracuseStep 370991 = 556487) B556487
theorem B371227 : Blo 370760 371227 := bstep (se 1 (by rfl) ⟨278420, by rfl⟩ : syracuseStep 371227 = 556841) B556841
theorem B371231 : Blo 370760 371231 := bstep (se 1 (by rfl) ⟨278423, by rfl⟩ : syracuseStep 371231 = 556847) B556847
theorem B895799 : Blo 370760 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B371547 : Blo 370760 371547 := bstep (se 1 (by rfl) ⟨278660, by rfl⟩ : syracuseStep 371547 = 557321) B557321
theorem B371615 : Blo 370760 371615 := bstep (se 1 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 371615 = 557423) B557423
theorem B1584107 : Blo 370760 1584107 := bstep (se 1 (by rfl) ⟨1188080, by rfl⟩ : syracuseStep 1584107 = 2376161) B2376161
theorem B470063 : Blo 370760 470063 := bstep (se 1 (by rfl) ⟨352547, by rfl⟩ : syracuseStep 470063 = 705095) B705095
theorem B371759 : Blo 370760 371759 := bstep (se 1 (by rfl) ⟨278819, by rfl⟩ : syracuseStep 371759 = 557639) B557639
theorem B371783 : Blo 370760 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B371935 : Blo 370760 371935 := bstep (se 1 (by rfl) ⟨278951, by rfl⟩ : syracuseStep 371935 = 557903) B557903
theorem B1060285 : Blo 370760 1060285 := bstep (se 3 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 1060285 = 397607) B397607
theorem B372199 : Blo 370760 372199 := bstep (se 1 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 372199 = 558299) B558299
theorem B372315 : Blo 370760 372315 := bstep (se 1 (by rfl) ⟨279236, by rfl⟩ : syracuseStep 372315 = 558473) B558473
theorem B1060627 : Blo 370760 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B372551 : Blo 370760 372551 := bstep (se 1 (by rfl) ⟨279413, by rfl⟩ : syracuseStep 372551 = 558827) B558827
theorem B896923 : Blo 370760 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B733151 : Blo 370760 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B372703 : Blo 370760 372703 := bstep (se 1 (by rfl) ⟨279527, by rfl⟩ : syracuseStep 372703 = 559055) B559055
theorem B569311 : Blo 370760 569311 := bstep (se 1 (by rfl) ⟨426983, by rfl⟩ : syracuseStep 569311 = 853967) B853967
theorem B1257659 : Blo 370760 1257659 := bstep (se 1 (by rfl) ⟨943244, by rfl⟩ : syracuseStep 1257659 = 1886489) B1886489
theorem B372967 : Blo 370760 372967 := bstep (se 1 (by rfl) ⟨279725, by rfl⟩ : syracuseStep 372967 = 559451) B559451
theorem B6435073 : Blo 370760 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B373119 : Blo 370760 373119 := bstep (se 1 (by rfl) ⟨279839, by rfl⟩ : syracuseStep 373119 = 559679) B559679
theorem B373199 : Blo 370760 373199 := bstep (se 1 (by rfl) ⟨279899, by rfl⟩ : syracuseStep 373199 = 559799) B559799
theorem B1880657 : Blo 370760 1880657 := bstep (se 2 (by rfl) ⟨705246, by rfl⟩ : syracuseStep 1880657 = 1410493) B1410493
theorem B373351 : Blo 370760 373351 := bstep (se 1 (by rfl) ⟨280013, by rfl⟩ : syracuseStep 373351 = 560027) B560027
theorem B1258145 : Blo 370760 1258145 := bstep (se 2 (by rfl) ⟨471804, by rfl⟩ : syracuseStep 1258145 = 943609) B943609
theorem B21672805 : Blo 370760 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B373615 : Blo 370760 373615 := bstep (se 1 (by rfl) ⟨280211, by rfl⟩ : syracuseStep 373615 = 560423) B560423
theorem B373671 : Blo 370760 373671 := bstep (se 1 (by rfl) ⟨280253, by rfl⟩ : syracuseStep 373671 = 560507) B560507
theorem B3191723 : Blo 370760 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B373755 : Blo 370760 373755 := bstep (se 1 (by rfl) ⟨280316, by rfl⟩ : syracuseStep 373755 = 560633) B560633
theorem B373823 : Blo 370760 373823 := bstep (se 1 (by rfl) ⟨280367, by rfl⟩ : syracuseStep 373823 = 560735) B560735
theorem B373967 : Blo 370760 373967 := bstep (se 1 (by rfl) ⟨280475, by rfl⟩ : syracuseStep 373967 = 560951) B560951
theorem B2012435 : Blo 370760 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B374171 : Blo 370760 374171 := bstep (se 1 (by rfl) ⟨280628, by rfl⟩ : syracuseStep 374171 = 561257) B561257
theorem B1259009 : Blo 370760 1259009 := bstep (se 2 (by rfl) ⟨472128, by rfl⟩ : syracuseStep 1259009 = 944257) B944257
theorem B2274887 : Blo 370760 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B374383 : Blo 370760 374383 := bstep (se 1 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 374383 = 561575) B561575
theorem B374439 : Blo 370760 374439 := bstep (se 1 (by rfl) ⟨280829, by rfl⟩ : syracuseStep 374439 = 561659) B561659
theorem B374523 : Blo 370760 374523 := bstep (se 1 (by rfl) ⟨280892, by rfl⟩ : syracuseStep 374523 = 561785) B561785
theorem B374559 : Blo 370760 374559 := bstep (se 1 (by rfl) ⟨280919, by rfl⟩ : syracuseStep 374559 = 561839) B561839
theorem B3028799 : Blo 370760 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B374591 : Blo 370760 374591 := bstep (se 1 (by rfl) ⟨280943, by rfl⟩ : syracuseStep 374591 = 561887) B561887
theorem B1259495 : Blo 370760 1259495 := bstep (se 1 (by rfl) ⟨944621, by rfl⟩ : syracuseStep 1259495 = 1889243) B1889243
theorem B1259603 : Blo 370760 1259603 := bstep (se 1 (by rfl) ⟨944702, by rfl⟩ : syracuseStep 1259603 = 1889405) B1889405
theorem B506011 : Blo 370760 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B1063145 : Blo 370760 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B7649579 : Blo 370760 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1259819 : Blo 370760 1259819 := bstep (se 1 (by rfl) ⟨944864, by rfl⟩ : syracuseStep 1259819 = 1889729) B1889729
theorem B473627 : Blo 370760 473627 := bstep (se 1 (by rfl) ⟨355220, by rfl⟩ : syracuseStep 473627 = 710441) B710441
theorem B539167 : Blo 370760 539167 := bstep (se 1 (by rfl) ⟨404375, by rfl⟩ : syracuseStep 539167 = 808751) B808751
theorem B1260089 : Blo 370760 1260089 := bstep (se 2 (by rfl) ⟨472533, by rfl⟩ : syracuseStep 1260089 = 945067) B945067
theorem B1883087 : Blo 370760 1883087 := bstep (se 1 (by rfl) ⟨1412315, by rfl⟩ : syracuseStep 1883087 = 2824631) B2824631
theorem B2112551 : Blo 370760 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B1916153 : Blo 370760 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B834983 : Blo 370760 834983 := bstep (se 1 (by rfl) ⟨626237, by rfl⟩ : syracuseStep 834983 = 1252475) B1252475
theorem B835163 : Blo 370760 835163 := bstep (se 1 (by rfl) ⟨626372, by rfl⟩ : syracuseStep 835163 = 1252745) B1252745
theorem B8601335 : Blo 370760 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B835451 : Blo 370760 835451 := bstep (se 1 (by rfl) ⟨626588, by rfl⟩ : syracuseStep 835451 = 1253177) B1253177
theorem B1261601 : Blo 370760 1261601 := bstep (se 2 (by rfl) ⟨473100, by rfl⟩ : syracuseStep 1261601 = 946201) B946201
theorem B835937 : Blo 370760 835937 := bstep (se 2 (by rfl) ⟨313476, by rfl⟩ : syracuseStep 835937 = 626953) B626953
theorem B3588457 : Blo 370760 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B836027 : Blo 370760 836027 := bstep (se 1 (by rfl) ⟨627020, by rfl⟩ : syracuseStep 836027 = 1254041) B1254041
theorem B803279 : Blo 370760 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B1065707 : Blo 370760 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B1786985 : Blo 370760 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B8045837 : Blo 370760 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B837035 : Blo 370760 837035 := bstep (se 1 (by rfl) ⟨627776, by rfl⟩ : syracuseStep 837035 = 1255553) B1255553
theorem B1197679 : Blo 370760 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B837287 : Blo 370760 837287 := bstep (se 1 (by rfl) ⟨627965, by rfl⟩ : syracuseStep 837287 = 1255931) B1255931
theorem B1918799 : Blo 370760 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B3196847 : Blo 370760 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B837575 : Blo 370760 837575 := bstep (se 1 (by rfl) ⟨628181, by rfl⟩ : syracuseStep 837575 = 1256363) B1256363
theorem B2115719 : Blo 370760 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B4245695 : Blo 370760 4245695 := bstep (se 1 (by rfl) ⟨3184271, by rfl⟩ : syracuseStep 4245695 = 6368543) B6368543
theorem B837881 : Blo 370760 837881 := bstep (se 2 (by rfl) ⟨314205, by rfl⟩ : syracuseStep 837881 = 628411) B628411
theorem B837935 : Blo 370760 837935 := bstep (se 1 (by rfl) ⟨628451, by rfl⟩ : syracuseStep 837935 = 1256903) B1256903
theorem B838151 : Blo 370760 838151 := bstep (se 1 (by rfl) ⟨628613, by rfl⟩ : syracuseStep 838151 = 1257227) B1257227
theorem B838331 : Blo 370760 838331 := bstep (se 1 (by rfl) ⟨628748, by rfl⟩ : syracuseStep 838331 = 1257497) B1257497
theorem B2837267 : Blo 370760 2837267 := bstep (se 1 (by rfl) ⟨2127950, by rfl⟩ : syracuseStep 2837267 = 4255901) B4255901
theorem B1887137 : Blo 370760 1887137 := bstep (se 2 (by rfl) ⟨707676, by rfl⟩ : syracuseStep 1887137 = 1415353) B1415353
theorem B839159 : Blo 370760 839159 := bstep (se 1 (by rfl) ⟨629369, by rfl⟩ : syracuseStep 839159 = 1258739) B1258739
theorem B839231 : Blo 370760 839231 := bstep (se 1 (by rfl) ⟨629423, by rfl⟩ : syracuseStep 839231 = 1258847) B1258847
theorem B1298045 : Blo 370760 1298045 := bstep (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) B486767
theorem B2379593 : Blo 370760 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B7721249 : Blo 370760 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B840185 : Blo 370760 840185 := bstep (se 2 (by rfl) ⟨315069, by rfl⟩ : syracuseStep 840185 = 630139) B630139
theorem B3396167 : Blo 370760 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B840275 : Blo 370760 840275 := bstep (se 1 (by rfl) ⟨630206, by rfl⟩ : syracuseStep 840275 = 1260413) B1260413
theorem B3822329 : Blo 370760 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B840455 : Blo 370760 840455 := bstep (se 1 (by rfl) ⟨630341, by rfl⟩ : syracuseStep 840455 = 1260683) B1260683
theorem B4510505 : Blo 370760 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B2413577 : Blo 370760 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1889567 : Blo 370760 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B841535 : Blo 370760 841535 := bstep (se 1 (by rfl) ⟨631151, by rfl⟩ : syracuseStep 841535 = 1262303) B1262303
theorem B4020151 : Blo 370760 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B939995 : Blo 370760 939995 := bstep (se 1 (by rfl) ⟨704996, by rfl⟩ : syracuseStep 939995 = 1409993) B1409993
theorem B546791 : Blo 370760 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B940025 : Blo 370760 940025 := bstep (se 2 (by rfl) ⟨352509, by rfl⟩ : syracuseStep 940025 = 705019) B705019
theorem B2381825 : Blo 370760 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B2381849 : Blo 370760 2381849 := bstep (se 2 (by rfl) ⟨893193, by rfl⟩ : syracuseStep 2381849 = 1786387) B1786387
theorem B841823 : Blo 370760 841823 := bstep (se 1 (by rfl) ⟨631367, by rfl⟩ : syracuseStep 841823 = 1262735) B1262735
theorem B940187 : Blo 370760 940187 := bstep (se 1 (by rfl) ⟨705140, by rfl⟩ : syracuseStep 940187 = 1410281) B1410281
theorem B2119841 : Blo 370760 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B1136969 : Blo 370760 1136969 := bstep (se 2 (by rfl) ⟨426363, by rfl⟩ : syracuseStep 1136969 = 852727) B852727
theorem B1006013 : Blo 370760 1006013 := bstep (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) B377255
theorem B842579 : Blo 370760 842579 := bstep (se 1 (by rfl) ⟨631934, by rfl⟩ : syracuseStep 842579 = 1263869) B1263869
theorem B2120843 : Blo 370760 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B1596631 : Blo 370760 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B449759 : Blo 370760 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B941321 : Blo 370760 941321 := bstep (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) B705991
theorem B843119 : Blo 370760 843119 := bstep (se 1 (by rfl) ⟨632339, by rfl⟩ : syracuseStep 843119 = 1264679) B1264679
theorem B9691469 : Blo 370760 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B1893131 : Blo 370760 1893131 := bstep (se 1 (by rfl) ⟨1419848, by rfl⟩ : syracuseStep 1893131 = 2839697) B2839697
theorem B1893293 : Blo 370760 1893293 := bstep (se 3 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 1893293 = 709985) B709985
theorem B3008015 : Blo 370760 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B4384543 : Blo 370760 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B419647 : Blo 370760 419647 := bstep (se 1 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 419647 = 629471) B629471
theorem B34498457 : Blo 370760 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B419935 : Blo 370760 419935 := bstep (se 1 (by rfl) ⟨314951, by rfl⟩ : syracuseStep 419935 = 629903) B629903
theorem B9038141 : Blo 370760 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B1894751 : Blo 370760 1894751 := bstep (se 1 (by rfl) ⟨1421063, by rfl⟩ : syracuseStep 1894751 = 2842127) B2842127
theorem B2124215 : Blo 370760 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B1894913 : Blo 370760 1894913 := bstep (se 2 (by rfl) ⟨710592, by rfl⟩ : syracuseStep 1894913 = 1421185) B1421185
theorem B1010207 : Blo 370760 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B846523 : Blo 370760 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B421087 : Blo 370760 421087 := bstep (se 1 (by rfl) ⟨315815, by rfl⟩ : syracuseStep 421087 = 631631) B631631
theorem B1895723 : Blo 370760 1895723 := bstep (se 1 (by rfl) ⟨1421792, by rfl⟩ : syracuseStep 1895723 = 2843585) B2843585
theorem B2157911 : Blo 370760 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B1699159 : Blo 370760 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B2551391 : Blo 370760 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B946363 : Blo 370760 946363 := bstep (se 1 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 946363 = 1419545) B1419545
theorem B946849 : Blo 370760 946849 := bstep (se 2 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 946849 = 710137) B710137
theorem B1897181 : Blo 370760 1897181 := bstep (se 3 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 1897181 = 711443) B711443
theorem B3012167 : Blo 370760 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B173930165 : Blo 370760 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B16053947 : Blo 370760 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B947963 : Blo 370760 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B6616849 : Blo 370760 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B849727 : Blo 370760 849727 := bstep (se 1 (by rfl) ⟨637295, by rfl⟩ : syracuseStep 849727 = 1274591) B1274591
theorem B2389823 : Blo 370760 2389823 := bstep (se 1 (by rfl) ⟨1792367, by rfl⟩ : syracuseStep 2389823 = 3584735) B3584735
theorem B948307 : Blo 370760 948307 := bstep (se 1 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 948307 = 1422461) B1422461
theorem B2259049 : Blo 370760 2259049 := bstep (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) B1694287
theorem B4225283 : Blo 370760 4225283 := bstep (se 1 (by rfl) ⟨3168962, by rfl⟩ : syracuseStep 4225283 = 6337925) B6337925
theorem B2390309 : Blo 370760 2390309 := bstep (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) B448183
theorem B1276573 : Blo 370760 1276573 := bstep (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) B478715
theorem B2554895 : Blo 370760 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B556367 : Blo 370760 556367 := bstep (se 1 (by rfl) ⟨417275, by rfl⟩ : syracuseStep 556367 = 834551) B834551
theorem B556457 : Blo 370760 556457 := bstep (se 2 (by rfl) ⟨208671, by rfl⟩ : syracuseStep 556457 = 417343) B417343
theorem B556607 : Blo 370760 556607 := bstep (se 1 (by rfl) ⟨417455, by rfl⟩ : syracuseStep 556607 = 834911) B834911
theorem B1081079 : Blo 370760 1081079 := bstep (se 1 (by rfl) ⟨810809, by rfl⟩ : syracuseStep 1081079 = 1621619) B1621619
theorem B556871 : Blo 370760 556871 := bstep (se 1 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 556871 = 835307) B835307
theorem B1539965 : Blo 370760 1539965 := bstep (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) B577487
theorem B556955 : Blo 370760 556955 := bstep (se 1 (by rfl) ⟨417716, by rfl⟩ : syracuseStep 556955 = 835433) B835433
theorem B557291 : Blo 370760 557291 := bstep (se 1 (by rfl) ⟨417968, by rfl⟩ : syracuseStep 557291 = 835937) B835937
theorem B557351 : Blo 370760 557351 := bstep (se 1 (by rfl) ⟨418013, by rfl⟩ : syracuseStep 557351 = 836027) B836027
theorem B917887 : Blo 370760 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B4784609 : Blo 370760 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B2294701 : Blo 370760 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B558023 : Blo 370760 558023 := bstep (se 1 (by rfl) ⟨418517, by rfl⟩ : syracuseStep 558023 = 837035) B837035
theorem B558191 : Blo 370760 558191 := bstep (se 1 (by rfl) ⟨418643, by rfl⟩ : syracuseStep 558191 = 837287) B837287
theorem B1279199 : Blo 370760 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B2131231 : Blo 370760 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B558383 : Blo 370760 558383 := bstep (se 1 (by rfl) ⟨418787, by rfl⟩ : syracuseStep 558383 = 837575) B837575
theorem B1410479 : Blo 370760 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B558587 : Blo 370760 558587 := bstep (se 1 (by rfl) ⟨418940, by rfl⟩ : syracuseStep 558587 = 837881) B837881
theorem B558623 : Blo 370760 558623 := bstep (se 1 (by rfl) ⟨418967, by rfl⟩ : syracuseStep 558623 = 837935) B837935
theorem B558767 : Blo 370760 558767 := bstep (se 1 (by rfl) ⟨419075, by rfl⟩ : syracuseStep 558767 = 838151) B838151
theorem B2819771 : Blo 370760 2819771 := bstep (se 1 (by rfl) ⟨2114828, by rfl⟩ : syracuseStep 2819771 = 4229657) B4229657
theorem B558887 : Blo 370760 558887 := bstep (se 1 (by rfl) ⟨419165, by rfl⟩ : syracuseStep 558887 = 838331) B838331
theorem B10192877 : Blo 370760 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B4294721 : Blo 370760 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B559439 : Blo 370760 559439 := bstep (se 1 (by rfl) ⟨419579, by rfl⟩ : syracuseStep 559439 = 839159) B839159
theorem B559487 : Blo 370760 559487 := bstep (se 1 (by rfl) ⟨419615, by rfl⟩ : syracuseStep 559487 = 839231) B839231
theorem B559529 : Blo 370760 559529 := bstep (se 2 (by rfl) ⟨209823, by rfl⟩ : syracuseStep 559529 = 419647) B419647
theorem B2755073 : Blo 370760 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B559913 : Blo 370760 559913 := bstep (se 2 (by rfl) ⟨209967, by rfl⟩ : syracuseStep 559913 = 419935) B419935
theorem B756649 : Blo 370760 756649 := bstep (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) B567487
theorem B14289857 : Blo 370760 14289857 := bstep (se 2 (by rfl) ⟨5358696, by rfl⟩ : syracuseStep 14289857 = 10717393) B10717393
theorem B560123 : Blo 370760 560123 := bstep (se 1 (by rfl) ⟨420092, by rfl⟩ : syracuseStep 560123 = 840185) B840185
theorem B2264111 : Blo 370760 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B560183 : Blo 370760 560183 := bstep (se 1 (by rfl) ⟨420137, by rfl⟩ : syracuseStep 560183 = 840275) B840275
theorem B560303 : Blo 370760 560303 := bstep (se 1 (by rfl) ⟨420227, by rfl⟩ : syracuseStep 560303 = 840455) B840455
theorem B561023 : Blo 370760 561023 := bstep (se 1 (by rfl) ⟨420767, by rfl⟩ : syracuseStep 561023 = 841535) B841535
theorem B3411857 : Blo 370760 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B626663 : Blo 370760 626663 := bstep (se 1 (by rfl) ⟨469997, by rfl⟩ : syracuseStep 626663 = 939995) B939995
theorem B626683 : Blo 370760 626683 := bstep (se 1 (by rfl) ⟨470012, by rfl⟩ : syracuseStep 626683 = 940025) B940025
theorem B561215 : Blo 370760 561215 := bstep (se 1 (by rfl) ⟨420911, by rfl⟩ : syracuseStep 561215 = 841823) B841823
theorem B626791 : Blo 370760 626791 := bstep (se 1 (by rfl) ⟨470093, by rfl⟩ : syracuseStep 626791 = 940187) B940187
theorem B528491 : Blo 370760 528491 := bstep (se 1 (by rfl) ⟨396368, by rfl⟩ : syracuseStep 528491 = 792737) B792737
theorem B1413227 : Blo 370760 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B757979 : Blo 370760 757979 := bstep (se 1 (by rfl) ⟨568484, by rfl⟩ : syracuseStep 757979 = 1136969) B1136969
theorem B561449 : Blo 370760 561449 := bstep (se 2 (by rfl) ⟨210543, by rfl⟩ : syracuseStep 561449 = 421087) B421087
theorem B2265545 : Blo 370760 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B561719 : Blo 370760 561719 := bstep (se 1 (by rfl) ⟨421289, by rfl⟩ : syracuseStep 561719 = 842579) B842579
theorem B1413713 : Blo 370760 1413713 := bstep (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) B1060285
theorem B1413895 : Blo 370760 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B627547 : Blo 370760 627547 := bstep (se 1 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 627547 = 941321) B941321
theorem B594847 : Blo 370760 594847 := bstep (se 1 (by rfl) ⟨446135, by rfl⟩ : syracuseStep 594847 = 892271) B892271
theorem B398239 : Blo 370760 398239 := bstep (se 1 (by rfl) ⟨298679, by rfl⟩ : syracuseStep 398239 = 597359) B597359
theorem B562079 : Blo 370760 562079 := bstep (se 1 (by rfl) ⟨421559, by rfl⟩ : syracuseStep 562079 = 843119) B843119
theorem B1414169 : Blo 370760 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B6460979 : Blo 370760 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B595783 : Blo 370760 595783 := bstep (se 1 (by rfl) ⟨446837, by rfl⟩ : syracuseStep 595783 = 893675) B893675
theorem B2005343 : Blo 370760 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B1416143 : Blo 370760 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B1056071 : Blo 370760 1056071 := bstep (se 1 (by rfl) ⟨792053, by rfl⟩ : syracuseStep 1056071 = 1584107) B1584107
theorem B8822465 : Blo 370760 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1417085 : Blo 370760 1417085 := bstep (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) B531407
theorem B1253501 : Blo 370760 1253501 := bstep (se 3 (by rfl) ⟨235031, by rfl⟩ : syracuseStep 1253501 = 470063) B470063
theorem B1253771 : Blo 370760 1253771 := bstep (se 1 (by rfl) ⟨940328, by rfl⟩ : syracuseStep 1253771 = 1880657) B1880657
theorem B2008111 : Blo 370760 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B1516591 : Blo 370760 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B631975 : Blo 370760 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B6563321 : Blo 370760 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B1255391 : Blo 370760 1255391 := bstep (se 1 (by rfl) ⟨941543, by rfl⟩ : syracuseStep 1255391 = 1883087) B1883087
theorem B370911 : Blo 370760 370911 := bstep (se 1 (by rfl) ⟨278183, by rfl⟩ : syracuseStep 370911 = 556367) B556367
theorem B370971 : Blo 370760 370971 := bstep (se 1 (by rfl) ⟨278228, by rfl⟩ : syracuseStep 370971 = 556457) B556457
theorem B371071 : Blo 370760 371071 := bstep (se 1 (by rfl) ⟨278303, by rfl⟩ : syracuseStep 371071 = 556607) B556607
theorem B371247 : Blo 370760 371247 := bstep (se 1 (by rfl) ⟨278435, by rfl⟩ : syracuseStep 371247 = 556871) B556871
theorem B1026643 : Blo 370760 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B371303 : Blo 370760 371303 := bstep (se 1 (by rfl) ⟨278477, by rfl⟩ : syracuseStep 371303 = 556955) B556955
theorem B535519 : Blo 370760 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B371679 : Blo 370760 371679 := bstep (se 1 (by rfl) ⟨278759, by rfl⟩ : syracuseStep 371679 = 557519) B557519
theorem B371707 : Blo 370760 371707 := bstep (se 1 (by rfl) ⟨278780, by rfl⟩ : syracuseStep 371707 = 557561) B557561
theorem B371775 : Blo 370760 371775 := bstep (se 1 (by rfl) ⟨278831, by rfl⟩ : syracuseStep 371775 = 557663) B557663
theorem B1420487 : Blo 370760 1420487 := bstep (se 1 (by rfl) ⟨1065365, by rfl⟩ : syracuseStep 1420487 = 2130731) B2130731
theorem B2010377 : Blo 370760 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B372095 : Blo 370760 372095 := bstep (se 1 (by rfl) ⟨279071, by rfl⟩ : syracuseStep 372095 = 558143) B558143
theorem B3583385 : Blo 370760 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B1191323 : Blo 370760 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B372123 : Blo 370760 372123 := bstep (se 1 (by rfl) ⟨279092, by rfl⟩ : syracuseStep 372123 = 558185) B558185
theorem B1420699 : Blo 370760 1420699 := bstep (se 1 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 1420699 = 2131049) B2131049
theorem B20589997 : Blo 370760 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B372191 : Blo 370760 372191 := bstep (se 1 (by rfl) ⟨279143, by rfl⟩ : syracuseStep 372191 = 558287) B558287
theorem B2272769 : Blo 370760 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B372327 : Blo 370760 372327 := bstep (se 1 (by rfl) ⟨279245, by rfl⟩ : syracuseStep 372327 = 558491) B558491
theorem B372475 : Blo 370760 372475 := bstep (se 1 (by rfl) ⟨279356, by rfl⟩ : syracuseStep 372475 = 558713) B558713
theorem B372543 : Blo 370760 372543 := bstep (se 1 (by rfl) ⟨279407, by rfl⟩ : syracuseStep 372543 = 558815) B558815
theorem B372607 : Blo 370760 372607 := bstep (se 1 (by rfl) ⟨279455, by rfl⟩ : syracuseStep 372607 = 558911) B558911
theorem B372719 : Blo 370760 372719 := bstep (se 1 (by rfl) ⟨279539, by rfl⟩ : syracuseStep 372719 = 559079) B559079
theorem B372731 : Blo 370760 372731 := bstep (se 1 (by rfl) ⟨279548, by rfl⟩ : syracuseStep 372731 = 559097) B559097
theorem B372799 : Blo 370760 372799 := bstep (se 1 (by rfl) ⟨279599, by rfl⟩ : syracuseStep 372799 = 559199) B559199
theorem B372839 : Blo 370760 372839 := bstep (se 1 (by rfl) ⟨279629, by rfl⟩ : syracuseStep 372839 = 559259) B559259
theorem B2830463 : Blo 370760 2830463 := bstep (se 1 (by rfl) ⟨2122847, by rfl⟩ : syracuseStep 2830463 = 4245695) B4245695
theorem B372863 : Blo 370760 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B372891 : Blo 370760 372891 := bstep (se 1 (by rfl) ⟨279668, by rfl⟩ : syracuseStep 372891 = 559337) B559337
theorem B373095 : Blo 370760 373095 := bstep (se 1 (by rfl) ⟨279821, by rfl⟩ : syracuseStep 373095 = 559643) B559643
theorem B373147 : Blo 370760 373147 := bstep (se 1 (by rfl) ⟨279860, by rfl⟩ : syracuseStep 373147 = 559721) B559721
theorem B1258091 : Blo 370760 1258091 := bstep (se 1 (by rfl) ⟨943568, by rfl⟩ : syracuseStep 1258091 = 1887137) B1887137
theorem B12202649 : Blo 370760 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B373499 : Blo 370760 373499 := bstep (se 1 (by rfl) ⟨280124, by rfl⟩ : syracuseStep 373499 = 560249) B560249
theorem B373567 : Blo 370760 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B1422143 : Blo 370760 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B373595 : Blo 370760 373595 := bstep (se 1 (by rfl) ⟨280196, by rfl⟩ : syracuseStep 373595 = 560393) B560393
theorem B373663 : Blo 370760 373663 := bstep (se 1 (by rfl) ⟨280247, by rfl⟩ : syracuseStep 373663 = 560495) B560495
theorem B373743 : Blo 370760 373743 := bstep (se 1 (by rfl) ⟨280307, by rfl⟩ : syracuseStep 373743 = 560615) B560615
theorem B5846057 : Blo 370760 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1881143 : Blo 370760 1881143 := bstep (se 1 (by rfl) ⟨1410857, by rfl⟩ : syracuseStep 1881143 = 2821715) B2821715
theorem B373831 : Blo 370760 373831 := bstep (se 1 (by rfl) ⟨280373, by rfl⟩ : syracuseStep 373831 = 560747) B560747
theorem B1062017 : Blo 370760 1062017 := bstep (se 2 (by rfl) ⟨398256, by rfl⟩ : syracuseStep 1062017 = 796513) B796513
theorem B373915 : Blo 370760 373915 := bstep (se 1 (by rfl) ⟨280436, by rfl⟩ : syracuseStep 373915 = 560873) B560873
theorem B1586395 : Blo 370760 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B374011 : Blo 370760 374011 := bstep (se 1 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 374011 = 561017) B561017
theorem B374079 : Blo 370760 374079 := bstep (se 1 (by rfl) ⟨280559, by rfl⟩ : syracuseStep 374079 = 561119) B561119
theorem B6436205 : Blo 370760 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B374247 : Blo 370760 374247 := bstep (se 1 (by rfl) ⟨280685, by rfl⟩ : syracuseStep 374247 = 561371) B561371
theorem B374255 : Blo 370760 374255 := bstep (se 1 (by rfl) ⟨280691, by rfl⟩ : syracuseStep 374255 = 561383) B561383
theorem B374363 : Blo 370760 374363 := bstep (se 1 (by rfl) ⟨280772, by rfl⟩ : syracuseStep 374363 = 561545) B561545
theorem B374427 : Blo 370760 374427 := bstep (se 1 (by rfl) ⟨280820, by rfl⟩ : syracuseStep 374427 = 561641) B561641
theorem B374511 : Blo 370760 374511 := bstep (se 1 (by rfl) ⟨280883, by rfl⟩ : syracuseStep 374511 = 561767) B561767
theorem B374599 : Blo 370760 374599 := bstep (se 1 (by rfl) ⟨280949, by rfl⟩ : syracuseStep 374599 = 561899) B561899
theorem B374619 : Blo 370760 374619 := bstep (se 1 (by rfl) ⟨280964, by rfl⟩ : syracuseStep 374619 = 561929) B561929
theorem B374687 : Blo 370760 374687 := bstep (se 1 (by rfl) ⟨281015, by rfl⟩ : syracuseStep 374687 = 562031) B562031
theorem B1259711 : Blo 370760 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B1128697 : Blo 370760 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B1587883 : Blo 370760 1587883 := bstep (se 1 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 1587883 = 2381825) B2381825
theorem B1587899 : Blo 370760 1587899 := bstep (se 1 (by rfl) ⟨1190924, by rfl⟩ : syracuseStep 1587899 = 2381849) B2381849
theorem B834281 : Blo 370760 834281 := bstep (se 2 (by rfl) ⟨312855, by rfl⟩ : syracuseStep 834281 = 625711) B625711
theorem B834515 : Blo 370760 834515 := bstep (se 1 (by rfl) ⟨625886, by rfl⟩ : syracuseStep 834515 = 1251773) B1251773
theorem B670675 : Blo 370760 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B834785 : Blo 370760 834785 := bstep (se 2 (by rfl) ⟨313044, by rfl⟩ : syracuseStep 834785 = 626089) B626089
theorem B8076797 : Blo 370760 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B835091 : Blo 370760 835091 := bstep (se 1 (by rfl) ⟨626318, by rfl⟩ : syracuseStep 835091 = 1252637) B1252637
theorem B4505311 : Blo 370760 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1195897 : Blo 370760 1195897 := bstep (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) B896923
theorem B1458109 : Blo 370760 1458109 := bstep (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) B546791
theorem B835775 : Blo 370760 835775 := bstep (se 1 (by rfl) ⟨626831, by rfl⟩ : syracuseStep 835775 = 1253663) B1253663
theorem B3195071 : Blo 370760 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B1261817 : Blo 370760 1261817 := bstep (se 2 (by rfl) ⟨473181, by rfl⟩ : syracuseStep 1261817 = 946363) B946363
theorem B1262087 : Blo 370760 1262087 := bstep (se 1 (by rfl) ⟨946565, by rfl⟩ : syracuseStep 1262087 = 1893131) B1893131
theorem B836207 : Blo 370760 836207 := bstep (se 1 (by rfl) ⟨627155, by rfl⟩ : syracuseStep 836207 = 1254311) B1254311
theorem B1262195 : Blo 370760 1262195 := bstep (se 1 (by rfl) ⟨946646, by rfl⟩ : syracuseStep 1262195 = 1893293) B1893293
theorem B1262465 : Blo 370760 1262465 := bstep (se 2 (by rfl) ⟨473424, by rfl⟩ : syracuseStep 1262465 = 946849) B946849
theorem B836603 : Blo 370760 836603 := bstep (se 1 (by rfl) ⟨627452, by rfl⟩ : syracuseStep 836603 = 1254905) B1254905
theorem B836783 : Blo 370760 836783 := bstep (se 1 (by rfl) ⟨627587, by rfl⟩ : syracuseStep 836783 = 1255175) B1255175
theorem B836819 : Blo 370760 836819 := bstep (se 1 (by rfl) ⟨627614, by rfl⟩ : syracuseStep 836819 = 1255229) B1255229
theorem B7128323 : Blo 370760 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B4769027 : Blo 370760 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B1263005 : Blo 370760 1263005 := bstep (se 3 (by rfl) ⟨236813, by rfl⟩ : syracuseStep 1263005 = 473627) B473627
theorem B837089 : Blo 370760 837089 := bstep (se 2 (by rfl) ⟨313908, by rfl⟩ : syracuseStep 837089 = 627817) B627817
theorem B1263167 : Blo 370760 1263167 := bstep (se 1 (by rfl) ⟨947375, by rfl⟩ : syracuseStep 1263167 = 1894751) B1894751
theorem B1263275 : Blo 370760 1263275 := bstep (se 1 (by rfl) ⟨947456, by rfl⟩ : syracuseStep 1263275 = 1894913) B1894913
theorem B673471 : Blo 370760 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B1263815 : Blo 370760 1263815 := bstep (se 1 (by rfl) ⟨947861, by rfl⟩ : syracuseStep 1263815 = 1895723) B1895723
theorem B1132969 : Blo 370760 1132969 := bstep (se 2 (by rfl) ⟨424863, by rfl⟩ : syracuseStep 1132969 = 849727) B849727
theorem B5360201 : Blo 370760 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B1264409 : Blo 370760 1264409 := bstep (se 2 (by rfl) ⟨474153, by rfl⟩ : syracuseStep 1264409 = 948307) B948307
theorem B838439 : Blo 370760 838439 := bstep (se 1 (by rfl) ⟨628829, by rfl⟩ : syracuseStep 838439 = 1257659) B1257659
theorem B707449 : Blo 370760 707449 := bstep (se 2 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 707449 = 530587) B530587
theorem B674681 : Blo 370760 674681 := bstep (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) B506011
theorem B838763 : Blo 370760 838763 := bstep (se 1 (by rfl) ⟨629072, by rfl⟩ : syracuseStep 838763 = 1258145) B1258145
theorem B1264787 : Blo 370760 1264787 := bstep (se 1 (by rfl) ⟨948590, by rfl⟩ : syracuseStep 1264787 = 1897181) B1897181
theorem B1199357 : Blo 370760 1199357 := bstep (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) B449759
theorem B839033 : Blo 370760 839033 := bstep (se 2 (by rfl) ⟨314637, by rfl⟩ : syracuseStep 839033 = 629275) B629275
theorem B839339 : Blo 370760 839339 := bstep (se 1 (by rfl) ⟨629504, by rfl⟩ : syracuseStep 839339 = 1259009) B1259009
theorem B115953443 : Blo 370760 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B10702631 : Blo 370760 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B1593215 : Blo 370760 1593215 := bstep (se 1 (by rfl) ⟨1194911, by rfl⟩ : syracuseStep 1593215 = 2389823) B2389823
theorem B839663 : Blo 370760 839663 := bstep (se 1 (by rfl) ⟨629747, by rfl⟩ : syracuseStep 839663 = 1259495) B1259495
theorem B839735 : Blo 370760 839735 := bstep (se 1 (by rfl) ⟨629801, by rfl⟩ : syracuseStep 839735 = 1259603) B1259603
theorem B708763 : Blo 370760 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B1593539 : Blo 370760 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B5099719 : Blo 370760 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B839879 : Blo 370760 839879 := bstep (se 1 (by rfl) ⟨629909, by rfl⟩ : syracuseStep 839879 = 1259819) B1259819
theorem B3461453 : Blo 370760 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B840059 : Blo 370760 840059 := bstep (se 1 (by rfl) ⟨630044, by rfl⟩ : syracuseStep 840059 = 1260089) B1260089
theorem B840329 : Blo 370760 840329 := bstep (se 2 (by rfl) ⟨315123, by rfl⟩ : syracuseStep 840329 = 630247) B630247
theorem B12145301 : Blo 370760 12145301 := bstep (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) B569311
theorem B841067 : Blo 370760 841067 := bstep (se 1 (by rfl) ⟨630800, by rfl⟩ : syracuseStep 841067 = 1261601) B1261601
theorem B1791503 : Blo 370760 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B841337 : Blo 370760 841337 := bstep (se 2 (by rfl) ⟨315501, by rfl⟩ : syracuseStep 841337 = 631003) B631003
theorem B710471 : Blo 370760 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B2545481 : Blo 370760 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B841697 : Blo 370760 841697 := bstep (se 2 (by rfl) ⟨315636, by rfl⟩ : syracuseStep 841697 = 631273) B631273
theorem B5363891 : Blo 370760 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B12409649 : Blo 370760 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B940855 : Blo 370760 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B1891511 : Blo 370760 1891511 := bstep (se 1 (by rfl) ⟨1418633, by rfl⟩ : syracuseStep 1891511 = 2837267) B2837267
theorem B1596905 : Blo 370760 1596905 := bstep (se 2 (by rfl) ⟨598839, by rfl⟩ : syracuseStep 1596905 = 1197679) B1197679
theorem B417703 : Blo 370760 417703 := bstep (se 1 (by rfl) ⟨313277, by rfl⟩ : syracuseStep 417703 = 626555) B626555
theorem B2121983 : Blo 370760 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B3007003 : Blo 370760 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B942799 : Blo 370760 942799 := bstep (se 1 (by rfl) ⟨707099, by rfl⟩ : syracuseStep 942799 = 1414199) B1414199
theorem B418927 : Blo 370760 418927 := bstep (se 1 (by rfl) ⟨314195, by rfl⟩ : syracuseStep 418927 = 628391) B628391
theorem B1336823 : Blo 370760 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B419359 : Blo 370760 419359 := bstep (se 1 (by rfl) ⟨314519, by rfl⟩ : syracuseStep 419359 = 629039) B629039
theorem B1009427 : Blo 370760 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B420223 : Blo 370760 420223 := bstep (se 1 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 420223 = 630335) B630335
theorem B8580097 : Blo 370760 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B28897073 : Blo 370760 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B22998971 : Blo 370760 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B6025427 : Blo 370760 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B2388797 : Blo 370760 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B1438607 : Blo 370760 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B1700927 : Blo 370760 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B488767 : Blo 370760 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B3012065 : Blo 370760 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B2127815 : Blo 370760 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B718889 : Blo 370760 718889 := bstep (se 2 (by rfl) ⟨269583, by rfl⟩ : syracuseStep 718889 = 539167) B539167
theorem B1341623 : Blo 370760 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B1702097 : Blo 370760 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B2816855 : Blo 370760 2816855 := bstep (se 1 (by rfl) ⟨2112641, by rfl⟩ : syracuseStep 2816855 = 4225283) B4225283
theorem B2128841 : Blo 370760 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B2817341 : Blo 370760 2817341 := bstep (se 3 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 2817341 = 1056503) B1056503
theorem B1703263 : Blo 370760 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B1408367 : Blo 370760 1408367 := bstep (se 1 (by rfl) ⟨1056275, by rfl⟩ : syracuseStep 1408367 = 2112551) B2112551
theorem B1277435 : Blo 370760 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B556655 : Blo 370760 556655 := bstep (se 1 (by rfl) ⟨417491, by rfl⟩ : syracuseStep 556655 = 834983) B834983
theorem B556775 : Blo 370760 556775 := bstep (se 1 (by rfl) ⟨417581, by rfl⟩ : syracuseStep 556775 = 835163) B835163
theorem B5734223 : Blo 370760 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B720719 : Blo 370760 720719 := bstep (se 1 (by rfl) ⟨540539, by rfl⟩ : syracuseStep 720719 = 1081079) B1081079
theorem B556967 : Blo 370760 556967 := bstep (se 1 (by rfl) ⟨417725, by rfl⟩ : syracuseStep 556967 = 835451) B835451
theorem B557183 : Blo 370760 557183 := bstep (se 1 (by rfl) ⟨417887, by rfl⟩ : syracuseStep 557183 = 835775) B835775
theorem B2130047 : Blo 370760 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B1409309 : Blo 370760 1409309 := bstep (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) B528491
theorem B557471 : Blo 370760 557471 := bstep (se 1 (by rfl) ⟨418103, by rfl⟩ : syracuseStep 557471 = 836207) B836207
theorem B557735 : Blo 370760 557735 := bstep (se 1 (by rfl) ⟨418301, by rfl⟩ : syracuseStep 557735 = 836603) B836603
theorem B557855 : Blo 370760 557855 := bstep (se 1 (by rfl) ⟨418391, by rfl⟩ : syracuseStep 557855 = 836783) B836783
theorem B557879 : Blo 370760 557879 := bstep (se 1 (by rfl) ⟨418409, by rfl⟩ : syracuseStep 557879 = 836819) B836819
theorem B4752215 : Blo 370760 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B3179351 : Blo 370760 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B558059 : Blo 370760 558059 := bstep (se 1 (by rfl) ⟨418544, by rfl⟩ : syracuseStep 558059 = 837089) B837089
theorem B558569 : Blo 370760 558569 := bstep (se 2 (by rfl) ⟨209463, by rfl⟩ : syracuseStep 558569 = 418927) B418927
theorem B1836715 : Blo 370760 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B3573467 : Blo 370760 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B558959 : Blo 370760 558959 := bstep (se 1 (by rfl) ⟨419219, by rfl⟩ : syracuseStep 558959 = 838439) B838439
theorem B1509407 : Blo 370760 1509407 := bstep (se 1 (by rfl) ⟨1132055, by rfl⟩ : syracuseStep 1509407 = 2264111) B2264111
theorem B559145 : Blo 370760 559145 := bstep (se 2 (by rfl) ⟨209679, by rfl⟩ : syracuseStep 559145 = 419359) B419359
theorem B559175 : Blo 370760 559175 := bstep (se 1 (by rfl) ⟨419381, by rfl⟩ : syracuseStep 559175 = 838763) B838763
theorem B559355 : Blo 370760 559355 := bstep (se 1 (by rfl) ⟨419516, by rfl⟩ : syracuseStep 559355 = 839033) B839033
theorem B559559 : Blo 370760 559559 := bstep (se 1 (by rfl) ⟨419669, by rfl⟩ : syracuseStep 559559 = 839339) B839339
theorem B77302295 : Blo 370760 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B559775 : Blo 370760 559775 := bstep (se 1 (by rfl) ⟨419831, by rfl⟩ : syracuseStep 559775 = 839663) B839663
theorem B559823 : Blo 370760 559823 := bstep (se 1 (by rfl) ⟨419867, by rfl⟩ : syracuseStep 559823 = 839735) B839735
theorem B559919 : Blo 370760 559919 := bstep (se 1 (by rfl) ⟨419939, by rfl⟩ : syracuseStep 559919 = 839879) B839879
theorem B560039 : Blo 370760 560039 := bstep (se 1 (by rfl) ⟨420029, by rfl⟩ : syracuseStep 560039 = 840059) B840059
theorem B1510363 : Blo 370760 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B560219 : Blo 370760 560219 := bstep (se 1 (by rfl) ⟨420164, by rfl⟩ : syracuseStep 560219 = 840329) B840329
theorem B8096867 : Blo 370760 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B560297 : Blo 370760 560297 := bstep (se 2 (by rfl) ⟨210111, by rfl⟩ : syracuseStep 560297 = 420223) B420223
theorem B1510625 : Blo 370760 1510625 := bstep (se 2 (by rfl) ⟨566484, by rfl⟩ : syracuseStep 1510625 = 1132969) B1132969
theorem B3411197 : Blo 370760 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B560711 : Blo 370760 560711 := bstep (se 1 (by rfl) ⟨420533, by rfl⟩ : syracuseStep 560711 = 841067) B841067
theorem B560891 : Blo 370760 560891 := bstep (se 1 (by rfl) ⟨420668, by rfl⟩ : syracuseStep 560891 = 841337) B841337
theorem B561131 : Blo 370760 561131 := bstep (se 1 (by rfl) ⟨420848, by rfl⟩ : syracuseStep 561131 = 841697) B841697
theorem B11440129 : Blo 370760 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B3575927 : Blo 370760 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B2691805 : Blo 370760 2691805 := bstep (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) B1009427
theorem B1414655 : Blo 370760 1414655 := bstep (se 1 (by rfl) ⟨1060991, by rfl⟩ : syracuseStep 1414655 = 2121983) B2121983
theorem B891215 : Blo 370760 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B794215 : Blo 370760 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B1515179 : Blo 370760 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B794377 : Blo 370760 794377 := bstep (se 2 (by rfl) ⟨297891, by rfl⟩ : syracuseStep 794377 = 595783) B595783
theorem B8135099 : Blo 370760 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B959071 : Blo 370760 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B1254095 : Blo 370760 1254095 := bstep (se 1 (by rfl) ⟨940571, by rfl⟩ : syracuseStep 1254095 = 1881143) B1881143
theorem B2008043 : Blo 370760 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B1254473 : Blo 370760 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B894233 : Blo 370760 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B1418543 : Blo 370760 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B894415 : Blo 370760 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B1058599 : Blo 370760 1058599 := bstep (se 1 (by rfl) ⟨793949, by rfl⟩ : syracuseStep 1058599 = 1587899) B1587899
theorem B2271017 : Blo 370760 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B1877903 : Blo 370760 1877903 := bstep (se 1 (by rfl) ⟨1408427, by rfl⟩ : syracuseStep 1877903 = 2816855) B2816855
theorem B1419227 : Blo 370760 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B1878227 : Blo 370760 1878227 := bstep (se 1 (by rfl) ⟨1408670, by rfl⟩ : syracuseStep 1878227 = 2817341) B2817341
theorem B6007081 : Blo 370760 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B5384531 : Blo 370760 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B371103 : Blo 370760 371103 := bstep (se 1 (by rfl) ⟨278327, by rfl⟩ : syracuseStep 371103 = 556655) B556655
theorem B371183 : Blo 370760 371183 := bstep (se 1 (by rfl) ⟨278387, by rfl⟩ : syracuseStep 371183 = 556775) B556775
theorem B1944145 : Blo 370760 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B371311 : Blo 370760 371311 := bstep (se 1 (by rfl) ⟨278483, by rfl⟩ : syracuseStep 371311 = 556967) B556967
theorem B371527 : Blo 370760 371527 := bstep (se 1 (by rfl) ⟨278645, by rfl⟩ : syracuseStep 371527 = 557291) B557291
theorem B371567 : Blo 370760 371567 := bstep (se 1 (by rfl) ⟨278675, by rfl⟩ : syracuseStep 371567 = 557351) B557351
theorem B3189739 : Blo 370760 3189739 := bstep (se 1 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 3189739 = 4784609) B4784609
theorem B1223849 : Blo 370760 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B372015 : Blo 370760 372015 := bstep (se 1 (by rfl) ⟨279011, by rfl⟩ : syracuseStep 372015 = 558023) B558023
theorem B4009337 : Blo 370760 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B372127 : Blo 370760 372127 := bstep (se 1 (by rfl) ⟨279095, by rfl⟩ : syracuseStep 372127 = 558191) B558191
theorem B372255 : Blo 370760 372255 := bstep (se 1 (by rfl) ⟨279191, by rfl⟩ : syracuseStep 372255 = 558383) B558383
theorem B1257065 : Blo 370760 1257065 := bstep (se 2 (by rfl) ⟨471399, by rfl⟩ : syracuseStep 1257065 = 942799) B942799
theorem B372391 : Blo 370760 372391 := bstep (se 1 (by rfl) ⟨279293, by rfl⟩ : syracuseStep 372391 = 558587) B558587
theorem B372415 : Blo 370760 372415 := bstep (se 1 (by rfl) ⟨279311, by rfl⟩ : syracuseStep 372415 = 558623) B558623
theorem B372511 : Blo 370760 372511 := bstep (se 1 (by rfl) ⟨279383, by rfl⟩ : syracuseStep 372511 = 558767) B558767
theorem B1879847 : Blo 370760 1879847 := bstep (se 1 (by rfl) ⟨1409885, by rfl⟩ : syracuseStep 1879847 = 2819771) B2819771
theorem B372591 : Blo 370760 372591 := bstep (se 1 (by rfl) ⟨279443, by rfl⟩ : syracuseStep 372591 = 558887) B558887
theorem B6795251 : Blo 370760 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B372959 : Blo 370760 372959 := bstep (se 1 (by rfl) ⟨279719, by rfl⟩ : syracuseStep 372959 = 559439) B559439
theorem B372991 : Blo 370760 372991 := bstep (se 1 (by rfl) ⟨279743, by rfl⟩ : syracuseStep 372991 = 559487) B559487
theorem B373019 : Blo 370760 373019 := bstep (se 1 (by rfl) ⟨279764, by rfl⟩ : syracuseStep 373019 = 559529) B559529
theorem B373275 : Blo 370760 373275 := bstep (se 1 (by rfl) ⟨279956, by rfl⟩ : syracuseStep 373275 = 559913) B559913
theorem B373415 : Blo 370760 373415 := bstep (se 1 (by rfl) ⟨280061, by rfl⟩ : syracuseStep 373415 = 560123) B560123
theorem B373455 : Blo 370760 373455 := bstep (se 1 (by rfl) ⟨280091, by rfl⟩ : syracuseStep 373455 = 560183) B560183
theorem B373535 : Blo 370760 373535 := bstep (se 1 (by rfl) ⟨280151, by rfl⟩ : syracuseStep 373535 = 560303) B560303
theorem B799571 : Blo 370760 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B897961 : Blo 370760 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B1062143 : Blo 370760 1062143 := bstep (se 1 (by rfl) ⟨796607, by rfl⟩ : syracuseStep 1062143 = 1593215) B1593215
theorem B374015 : Blo 370760 374015 := bstep (se 1 (by rfl) ⟨280511, by rfl⟩ : syracuseStep 374015 = 561023) B561023
theorem B2274571 : Blo 370760 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B374143 : Blo 370760 374143 := bstep (se 1 (by rfl) ⟨280607, by rfl⟩ : syracuseStep 374143 = 561215) B561215
theorem B1062359 : Blo 370760 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B505319 : Blo 370760 505319 := bstep (se 1 (by rfl) ⟨378989, by rfl⟩ : syracuseStep 505319 = 757979) B757979
theorem B374299 : Blo 370760 374299 := bstep (se 1 (by rfl) ⟨280724, by rfl⟩ : syracuseStep 374299 = 561449) B561449
theorem B2307635 : Blo 370760 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B374479 : Blo 370760 374479 := bstep (se 1 (by rfl) ⟨280859, by rfl⟩ : syracuseStep 374479 = 561719) B561719
theorem B374719 : Blo 370760 374719 := bstep (se 1 (by rfl) ⟨281039, by rfl⟩ : syracuseStep 374719 = 562079) B562079
theorem B1194335 : Blo 370760 1194335 := bstep (se 1 (by rfl) ⟨895751, by rfl⟩ : syracuseStep 1194335 = 1791503) B1791503
theorem B8273099 : Blo 370760 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B1261007 : Blo 370760 1261007 := bstep (se 1 (by rfl) ⟨945755, by rfl⟩ : syracuseStep 1261007 = 1891511) B1891511
theorem B704047 : Blo 370760 704047 := bstep (se 1 (by rfl) ⟨528035, by rfl⟩ : syracuseStep 704047 = 1056071) B1056071
theorem B1064603 : Blo 370760 1064603 := bstep (se 1 (by rfl) ⟨798452, by rfl⟩ : syracuseStep 1064603 = 1596905) B1596905
theorem B5881643 : Blo 370760 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B835577 : Blo 370760 835577 := bstep (se 2 (by rfl) ⟨313341, by rfl⟩ : syracuseStep 835577 = 626683) B626683
theorem B835667 : Blo 370760 835667 := bstep (se 1 (by rfl) ⟨626750, by rfl⟩ : syracuseStep 835667 = 1253501) B1253501
theorem B1917037 : Blo 370760 1917037 := bstep (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) B718889
theorem B835721 : Blo 370760 835721 := bstep (se 2 (by rfl) ⟨313395, by rfl⟩ : syracuseStep 835721 = 626791) B626791
theorem B11452589 : Blo 370760 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B835847 : Blo 370760 835847 := bstep (se 1 (by rfl) ⟨626885, by rfl⟩ : syracuseStep 835847 = 1253771) B1253771
theorem B6799625 : Blo 370760 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B4375547 : Blo 370760 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1885193 : Blo 370760 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B836729 : Blo 370760 836729 := bstep (se 2 (by rfl) ⟨313773, by rfl⟩ : syracuseStep 836729 = 627547) B627547
theorem B836927 : Blo 370760 836927 := bstep (se 1 (by rfl) ⟨627695, by rfl⟩ : syracuseStep 836927 = 1255391) B1255391
theorem B2115193 : Blo 370760 2115193 := bstep (se 2 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 2115193 = 1586395) B1586395
theorem B1886975 : Blo 370760 1886975 := bstep (se 1 (by rfl) ⟨1415231, by rfl⟩ : syracuseStep 1886975 = 2830463) B2830463
theorem B4016951 : Blo 370760 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B838727 : Blo 370760 838727 := bstep (se 1 (by rfl) ⟨629045, by rfl⟩ : syracuseStep 838727 = 1258091) B1258091
theorem B1592531 : Blo 370760 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B5361005 : Blo 370760 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B1133951 : Blo 370760 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B708011 : Blo 370760 708011 := bstep (se 1 (by rfl) ⟨531008, by rfl⟩ : syracuseStep 708011 = 1062017) B1062017
theorem B7687669 : Blo 370760 7687669 := bstep (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) B720719
theorem B2117177 : Blo 370760 2117177 := bstep (se 2 (by rfl) ⟨793941, by rfl⟩ : syracuseStep 2117177 = 1587883) B1587883
theorem B7196597 : Blo 370760 7196597 := bstep (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) B674681
theorem B839807 : Blo 370760 839807 := bstep (se 1 (by rfl) ⟨629855, by rfl⟩ : syracuseStep 839807 = 1259711) B1259711
theorem B1134731 : Blo 370760 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B938911 : Blo 370760 938911 := bstep (se 1 (by rfl) ⟨704183, by rfl⟩ : syracuseStep 938911 = 1408367) B1408367
theorem B1594529 : Blo 370760 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B3822815 : Blo 370760 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B841211 : Blo 370760 841211 := bstep (se 1 (by rfl) ⟨630908, by rfl⟩ : syracuseStep 841211 = 1261817) B1261817
theorem B841391 : Blo 370760 841391 := bstep (se 1 (by rfl) ⟨631043, by rfl⟩ : syracuseStep 841391 = 1262087) B1262087
theorem B841463 : Blo 370760 841463 := bstep (se 1 (by rfl) ⟨631097, by rfl⟩ : syracuseStep 841463 = 1262195) B1262195
theorem B841643 : Blo 370760 841643 := bstep (se 1 (by rfl) ⟨631232, by rfl⟩ : syracuseStep 841643 = 1262465) B1262465
theorem B842003 : Blo 370760 842003 := bstep (se 1 (by rfl) ⟨631502, by rfl⟩ : syracuseStep 842003 = 1263005) B1263005
theorem B940319 : Blo 370760 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B842111 : Blo 370760 842111 := bstep (se 1 (by rfl) ⟨631583, by rfl⟩ : syracuseStep 842111 = 1263167) B1263167
theorem B842183 : Blo 370760 842183 := bstep (se 1 (by rfl) ⟨631637, by rfl⟩ : syracuseStep 842183 = 1263275) B1263275
theorem B6019717 : Blo 370760 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B2677481 : Blo 370760 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B2022121 : Blo 370760 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B842543 : Blo 370760 842543 := bstep (se 1 (by rfl) ⟨631907, by rfl⟩ : syracuseStep 842543 = 1263815) B1263815
theorem B842633 : Blo 370760 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B2841641 : Blo 370760 2841641 := bstep (se 2 (by rfl) ⟨1065615, by rfl⟩ : syracuseStep 2841641 = 2131231) B2131231
theorem B842939 : Blo 370760 842939 := bstep (se 1 (by rfl) ⟨632204, by rfl⟩ : syracuseStep 842939 = 1264409) B1264409
theorem B9526571 : Blo 370760 9526571 := bstep (se 1 (by rfl) ⟨7144928, by rfl⟩ : syracuseStep 9526571 = 14289857) B14289857
theorem B843191 : Blo 370760 843191 := bstep (se 1 (by rfl) ⟨632393, by rfl⟩ : syracuseStep 843191 = 1264787) B1264787
theorem B7135087 : Blo 370760 7135087 := bstep (se 1 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 7135087 = 10702631) B10702631
theorem B417775 : Blo 370760 417775 := bstep (se 1 (by rfl) ⟨313331, by rfl⟩ : syracuseStep 417775 = 626663) B626663
theorem B942151 : Blo 370760 942151 := bstep (se 1 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 942151 = 1413227) B1413227
theorem B942475 : Blo 370760 942475 := bstep (se 1 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 942475 = 1413713) B1413713
theorem B942779 : Blo 370760 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B1368857 : Blo 370760 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B943265 : Blo 370760 943265 := bstep (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) B707449
theorem B1696987 : Blo 370760 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B1008865 : Blo 370760 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B714025 : Blo 370760 714025 := bstep (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) B535519
theorem B17229277 : Blo 370760 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B1336895 : Blo 370760 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B1894265 : Blo 370760 1894265 := bstep (se 2 (by rfl) ⟨710349, by rfl⟩ : syracuseStep 1894265 = 1420699) B1420699
theorem B27453329 : Blo 370760 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B944095 : Blo 370760 944095 := bstep (se 1 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 944095 = 1416143) B1416143
theorem B3172517 : Blo 370760 3172517 := bstep (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) B594847
theorem B2123941 : Blo 370760 2123941 := bstep (se 4 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 2123941 = 398239) B398239
theorem B1894589 : Blo 370760 1894589 := bstep (se 3 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 1894589 = 710471) B710471
theorem B944723 : Blo 370760 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B945017 : Blo 370760 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B651689 : Blo 370760 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B946991 : Blo 370760 946991 := bstep (se 1 (by rfl) ⟨710243, by rfl⟩ : syracuseStep 946991 = 1420487) B1420487
theorem B2388923 : Blo 370760 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B19264715 : Blo 370760 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B15332647 : Blo 370760 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B948095 : Blo 370760 948095 := bstep (se 1 (by rfl) ⟨711071, by rfl⟩ : syracuseStep 948095 = 1422143) B1422143
theorem B3897371 : Blo 370760 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B4290803 : Blo 370760 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B48953621 : Blo 370760 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B556187 : Blo 370760 556187 := bstep (se 1 (by rfl) ⟨417140, by rfl⟩ : syracuseStep 556187 = 834281) B834281
theorem B556343 : Blo 370760 556343 := bstep (se 1 (by rfl) ⟨417257, by rfl⟩ : syracuseStep 556343 = 834515) B834515
theorem B556523 : Blo 370760 556523 := bstep (se 1 (by rfl) ⟨417392, by rfl⟩ : syracuseStep 556523 = 834785) B834785
theorem B851623 : Blo 370760 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B556727 : Blo 370760 556727 := bstep (se 1 (by rfl) ⟨417545, by rfl⟩ : syracuseStep 556727 = 835091) B835091
theorem B556937 : Blo 370760 556937 := bstep (se 2 (by rfl) ⟨208851, by rfl⟩ : syracuseStep 556937 = 417703) B417703
theorem B557111 : Blo 370760 557111 := bstep (se 1 (by rfl) ⟨417833, by rfl⟩ : syracuseStep 557111 = 835667) B835667
theorem B557147 : Blo 370760 557147 := bstep (se 1 (by rfl) ⟨417860, by rfl⟩ : syracuseStep 557147 = 835721) B835721
theorem B7635059 : Blo 370760 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B2556049 : Blo 370760 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B557231 : Blo 370760 557231 := bstep (se 1 (by rfl) ⟨417923, by rfl⟩ : syracuseStep 557231 = 835847) B835847
theorem B2917031 : Blo 370760 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B557819 : Blo 370760 557819 := bstep (se 1 (by rfl) ⟨418364, by rfl⟩ : syracuseStep 557819 = 836729) B836729
theorem B1278761 : Blo 370760 1278761 := bstep (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) B959071
theorem B557951 : Blo 370760 557951 := bstep (se 1 (by rfl) ⟨418463, by rfl⟩ : syracuseStep 557951 = 836927) B836927
theorem B2262649 : Blo 370760 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B952033 : Blo 370760 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B22972369 : Blo 370760 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B559151 : Blo 370760 559151 := bstep (se 1 (by rfl) ⟨419363, by rfl⟩ : syracuseStep 559151 = 838727) B838727
theorem B2820257 : Blo 370760 2820257 := bstep (se 2 (by rfl) ⟨1057596, by rfl⟩ : syracuseStep 2820257 = 2115193) B2115193
theorem B2132189 : Blo 370760 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B3574003 : Blo 370760 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B1411451 : Blo 370760 1411451 := bstep (se 1 (by rfl) ⟨1058588, by rfl⟩ : syracuseStep 1411451 = 2117177) B2117177
theorem B1411465 : Blo 370760 1411465 := bstep (se 2 (by rfl) ⟨529299, by rfl⟩ : syracuseStep 1411465 = 1058599) B1058599
theorem B559871 : Blo 370760 559871 := bstep (se 1 (by rfl) ⟨419903, by rfl⟩ : syracuseStep 559871 = 839807) B839807
theorem B756487 : Blo 370760 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B10194173 : Blo 370760 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B560807 : Blo 370760 560807 := bstep (se 1 (by rfl) ⟨420605, by rfl⟩ : syracuseStep 560807 = 841211) B841211
theorem B560927 : Blo 370760 560927 := bstep (se 1 (by rfl) ⟨420695, by rfl⟩ : syracuseStep 560927 = 841391) B841391
theorem B560975 : Blo 370760 560975 := bstep (se 1 (by rfl) ⟨420731, by rfl⟩ : syracuseStep 560975 = 841463) B841463
theorem B1347517 : Blo 370760 1347517 := bstep (se 3 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 1347517 = 505319) B505319
theorem B561095 : Blo 370760 561095 := bstep (se 1 (by rfl) ⟨420821, by rfl⟩ : syracuseStep 561095 = 841643) B841643
theorem B12095477 : Blo 370760 12095477 := bstep (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) B1133951
theorem B561335 : Blo 370760 561335 := bstep (se 1 (by rfl) ⟨421001, by rfl⟩ : syracuseStep 561335 = 842003) B842003
theorem B626879 : Blo 370760 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B594143 : Blo 370760 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B561407 : Blo 370760 561407 := bstep (se 1 (by rfl) ⟨421055, by rfl⟩ : syracuseStep 561407 = 842111) B842111
theorem B561455 : Blo 370760 561455 := bstep (se 1 (by rfl) ⟨421091, by rfl⟩ : syracuseStep 561455 = 842183) B842183
theorem B6951349 : Blo 370760 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B561695 : Blo 370760 561695 := bstep (se 1 (by rfl) ⟨421271, by rfl⟩ : syracuseStep 561695 = 842543) B842543
theorem B561755 : Blo 370760 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B561959 : Blo 370760 561959 := bstep (se 1 (by rfl) ⟨421469, by rfl⟩ : syracuseStep 561959 = 842939) B842939
theorem B562127 : Blo 370760 562127 := bstep (se 1 (by rfl) ⟨421595, by rfl⟩ : syracuseStep 562127 = 843191) B843191
theorem B628519 : Blo 370760 628519 := bstep (se 1 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 628519 = 942779) B942779
theorem B628843 : Blo 370760 628843 := bstep (se 1 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 628843 = 943265) B943265
theorem B596155 : Blo 370760 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B891263 : Blo 370760 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B5380613 : Blo 370760 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B1251881 : Blo 370760 1251881 := bstep (se 2 (by rfl) ⟨469455, by rfl⟩ : syracuseStep 1251881 = 938911) B938911
theorem B1251935 : Blo 370760 1251935 := bstep (se 1 (by rfl) ⟨938951, by rfl⟩ : syracuseStep 1251935 = 1877903) B1877903
theorem B1252151 : Blo 370760 1252151 := bstep (se 1 (by rfl) ⟨939113, by rfl⟩ : syracuseStep 1252151 = 1878227) B1878227
theorem B629815 : Blo 370760 629815 := bstep (se 1 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 629815 = 944723) B944723
theorem B630011 : Blo 370760 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B1253231 : Blo 370760 1253231 := bstep (se 1 (by rfl) ⟨939923, by rfl⟩ : syracuseStep 1253231 = 1879847) B1879847
theorem B4530167 : Blo 370760 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B631327 : Blo 370760 631327 := bstep (se 1 (by rfl) ⟨473495, by rfl⟩ : syracuseStep 631327 = 946991) B946991
theorem B2696161 : Blo 370760 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B632063 : Blo 370760 632063 := bstep (se 1 (by rfl) ⟨474047, by rfl⟩ : syracuseStep 632063 = 948095) B948095
theorem B2598247 : Blo 370760 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B2860535 : Blo 370760 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B796223 : Blo 370760 796223 := bstep (se 1 (by rfl) ⟨597167, by rfl⟩ : syracuseStep 796223 = 1194335) B1194335
theorem B370791 : Blo 370760 370791 := bstep (se 1 (by rfl) ⟨278093, by rfl⟩ : syracuseStep 370791 = 556187) B556187
theorem B5515399 : Blo 370760 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B1058953 : Blo 370760 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B370895 : Blo 370760 370895 := bstep (se 1 (by rfl) ⟨278171, by rfl⟩ : syracuseStep 370895 = 556343) B556343
theorem B371015 : Blo 370760 371015 := bstep (se 1 (by rfl) ⟨278261, by rfl⟩ : syracuseStep 371015 = 556523) B556523
theorem B1059169 : Blo 370760 1059169 := bstep (se 2 (by rfl) ⟨397188, by rfl⟩ : syracuseStep 1059169 = 794377) B794377
theorem B371151 : Blo 370760 371151 := bstep (se 1 (by rfl) ⟨278363, by rfl⟩ : syracuseStep 371151 = 556727) B556727
theorem B9513449 : Blo 370760 9513449 := bstep (se 2 (by rfl) ⟨3567543, by rfl⟩ : syracuseStep 9513449 = 7135087) B7135087
theorem B371291 : Blo 370760 371291 := bstep (se 1 (by rfl) ⟨278468, by rfl⟩ : syracuseStep 371291 = 556937) B556937
theorem B371455 : Blo 370760 371455 := bstep (se 1 (by rfl) ⟨278591, by rfl⟩ : syracuseStep 371455 = 557183) B557183
theorem B1420031 : Blo 370760 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B1256201 : Blo 370760 1256201 := bstep (se 2 (by rfl) ⟨471075, by rfl⟩ : syracuseStep 1256201 = 942151) B942151
theorem B4533083 : Blo 370760 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B371647 : Blo 370760 371647 := bstep (se 1 (by rfl) ⟨278735, by rfl⟩ : syracuseStep 371647 = 557471) B557471
theorem B371823 : Blo 370760 371823 := bstep (se 1 (by rfl) ⟨278867, by rfl⟩ : syracuseStep 371823 = 557735) B557735
theorem B1256633 : Blo 370760 1256633 := bstep (se 2 (by rfl) ⟨471237, by rfl⟩ : syracuseStep 1256633 = 942475) B942475
theorem B371903 : Blo 370760 371903 := bstep (se 1 (by rfl) ⟨278927, by rfl⟩ : syracuseStep 371903 = 557855) B557855
theorem B371919 : Blo 370760 371919 := bstep (se 1 (by rfl) ⟨278939, by rfl⟩ : syracuseStep 371919 = 557879) B557879
theorem B372039 : Blo 370760 372039 := bstep (se 1 (by rfl) ⟨279029, by rfl⟩ : syracuseStep 372039 = 558059) B558059
theorem B1256795 : Blo 370760 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B372379 : Blo 370760 372379 := bstep (se 1 (by rfl) ⟨279284, by rfl⟩ : syracuseStep 372379 = 558569) B558569
theorem B372639 : Blo 370760 372639 := bstep (se 1 (by rfl) ⟨279479, by rfl⟩ : syracuseStep 372639 = 558959) B558959
theorem B372763 : Blo 370760 372763 := bstep (se 1 (by rfl) ⟨279572, by rfl⟩ : syracuseStep 372763 = 559145) B559145
theorem B372783 : Blo 370760 372783 := bstep (se 1 (by rfl) ⟨279587, by rfl⟩ : syracuseStep 372783 = 559175) B559175
theorem B372903 : Blo 370760 372903 := bstep (se 1 (by rfl) ⟨279677, by rfl⟩ : syracuseStep 372903 = 559355) B559355
theorem B373039 : Blo 370760 373039 := bstep (se 1 (by rfl) ⟨279779, by rfl⟩ : syracuseStep 373039 = 559559) B559559
theorem B373183 : Blo 370760 373183 := bstep (se 1 (by rfl) ⟨279887, by rfl⟩ : syracuseStep 373183 = 559775) B559775
theorem B373215 : Blo 370760 373215 := bstep (se 1 (by rfl) ⟨279911, by rfl⟩ : syracuseStep 373215 = 559823) B559823
theorem B1257983 : Blo 370760 1257983 := bstep (se 1 (by rfl) ⟨943487, by rfl⟩ : syracuseStep 1257983 = 1886975) B1886975
theorem B373279 : Blo 370760 373279 := bstep (se 1 (by rfl) ⟨279959, by rfl⟩ : syracuseStep 373279 = 559919) B559919
theorem B1192553 : Blo 370760 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B373359 : Blo 370760 373359 := bstep (se 1 (by rfl) ⟨280019, by rfl⟩ : syracuseStep 373359 = 560039) B560039
theorem B373479 : Blo 370760 373479 := bstep (se 1 (by rfl) ⟨280109, by rfl⟩ : syracuseStep 373479 = 560219) B560219
theorem B3650285 : Blo 370760 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B373531 : Blo 370760 373531 := bstep (se 1 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 373531 = 560297) B560297
theorem B1061687 : Blo 370760 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B2274131 : Blo 370760 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B472007 : Blo 370760 472007 := bstep (se 1 (by rfl) ⟨354005, by rfl⟩ : syracuseStep 472007 = 708011) B708011
theorem B373807 : Blo 370760 373807 := bstep (se 1 (by rfl) ⟨280355, by rfl⟩ : syracuseStep 373807 = 560711) B560711
theorem B373927 : Blo 370760 373927 := bstep (se 1 (by rfl) ⟨280445, by rfl⟩ : syracuseStep 373927 = 560891) B560891
theorem B4797731 : Blo 370760 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1258793 : Blo 370760 1258793 := bstep (se 2 (by rfl) ⟨472047, by rfl⟩ : syracuseStep 1258793 = 944095) B944095
theorem B374087 : Blo 370760 374087 := bstep (se 1 (by rfl) ⟨280565, by rfl⟩ : syracuseStep 374087 = 561131) B561131
theorem B2831921 : Blo 370760 2831921 := bstep (se 2 (by rfl) ⟨1061970, by rfl⟩ : syracuseStep 2831921 = 2123941) B2123941
theorem B8009441 : Blo 370760 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B10368773 : Blo 370760 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B1063019 : Blo 370760 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B2013817 : Blo 370760 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B1784987 : Blo 370760 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B15253505 : Blo 370760 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B5423399 : Blo 370760 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B836063 : Blo 370760 836063 := bstep (se 1 (by rfl) ⟨627047, by rfl⟩ : syracuseStep 836063 = 1254095) B1254095
theorem B836315 : Blo 370760 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B3589073 : Blo 370760 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B1197281 : Blo 370760 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B1262843 : Blo 370760 1262843 := bstep (se 1 (by rfl) ⟨947132, by rfl⟩ : syracuseStep 1262843 = 1894265) B1894265
theorem B18302219 : Blo 370760 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B2115011 : Blo 370760 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B1263059 : Blo 370760 1263059 := bstep (se 1 (by rfl) ⟨947294, by rfl⟩ : syracuseStep 1263059 = 1894589) B1894589
theorem B3589687 : Blo 370760 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B3032761 : Blo 370760 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B2672891 : Blo 370760 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B838043 : Blo 370760 838043 := bstep (se 1 (by rfl) ⟨628532, by rfl⟩ : syracuseStep 838043 = 1257065) B1257065
theorem B3263597 : Blo 370760 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B1592615 : Blo 370760 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B708095 : Blo 370760 708095 := bstep (se 1 (by rfl) ⟨531071, by rfl⟩ : syracuseStep 708095 = 1062143) B1062143
theorem B4541989 : Blo 370760 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B708239 : Blo 370760 708239 := bstep (se 1 (by rfl) ⟨531179, by rfl⟩ : syracuseStep 708239 = 1062359) B1062359
theorem B938729 : Blo 370760 938729 := bstep (se 2 (by rfl) ⟨352023, by rfl⟩ : syracuseStep 938729 = 704047) B704047
theorem B840671 : Blo 370760 840671 := bstep (se 1 (by rfl) ⟨630503, by rfl⟩ : syracuseStep 840671 = 1261007) B1261007
theorem B709735 : Blo 370760 709735 := bstep (se 1 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 709735 = 1064603) B1064603
theorem B3921095 : Blo 370760 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B939539 : Blo 370760 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B3168143 : Blo 370760 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B2119567 : Blo 370760 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B2382311 : Blo 370760 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B1006271 : Blo 370760 1006271 := bstep (se 1 (by rfl) ⟨754703, by rfl⟩ : syracuseStep 1006271 = 1509407) B1509407
theorem B51534863 : Blo 370760 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B2677967 : Blo 370760 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B5397911 : Blo 370760 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B1007083 : Blo 370760 1007083 := bstep (se 1 (by rfl) ⟨755312, by rfl⟩ : syracuseStep 1007083 = 1510625) B1510625
theorem B2448953 : Blo 370760 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B2383951 : Blo 370760 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B943103 : Blo 370760 943103 := bstep (se 1 (by rfl) ⟨707327, by rfl⟩ : syracuseStep 943103 = 1414655) B1414655
theorem B4252985 : Blo 370760 4252985 := bstep (se 2 (by rfl) ⟨1594869, by rfl⟩ : syracuseStep 4252985 = 3189739) B3189739
theorem B10250225 : Blo 370760 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B1894427 : Blo 370760 1894427 := bstep (se 1 (by rfl) ⟨1420820, by rfl⟩ : syracuseStep 1894427 = 2841641) B2841641
theorem B6056045 : Blo 370760 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B6351047 : Blo 370760 6351047 := bstep (se 1 (by rfl) ⟨4763285, by rfl⟩ : syracuseStep 6351047 = 9526571) B9526571
theorem B1010119 : Blo 370760 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B1338695 : Blo 370760 1338695 := bstep (se 1 (by rfl) ⟨1004021, by rfl⟩ : syracuseStep 1338695 = 2008043) B2008043
theorem B945695 : Blo 370760 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B946151 : Blo 370760 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B20443529 : Blo 370760 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B12843143 : Blo 370760 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B8026289 : Blo 370760 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B1538423 : Blo 370760 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B32635747 : Blo 370760 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B557033 : Blo 370760 557033 := bstep (se 2 (by rfl) ⟨208887, by rfl⟩ : syracuseStep 557033 = 417775) B417775
theorem B557051 : Blo 370760 557051 := bstep (se 1 (by rfl) ⟨417788, by rfl⟩ : syracuseStep 557051 = 835577) B835577
theorem B3178601 : Blo 370760 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B3408065 : Blo 370760 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B557375 : Blo 370760 557375 := bstep (se 1 (by rfl) ⟨418031, by rfl⟩ : syracuseStep 557375 = 836063) B836063
theorem B557543 : Blo 370760 557543 := bstep (se 1 (by rfl) ⟨418157, by rfl⟩ : syracuseStep 557543 = 836315) B836315
theorem B2392715 : Blo 370760 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B1410007 : Blo 370760 1410007 := bstep (se 1 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 1410007 = 2115011) B2115011
theorem B558695 : Blo 370760 558695 := bstep (se 1 (by rfl) ⟨419021, by rfl⟩ : syracuseStep 558695 = 838043) B838043
theorem B9734093 : Blo 370760 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B4786249 : Blo 370760 4786249 := bstep (se 2 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 4786249 = 3589687) B3589687
theorem B3410029 : Blo 370760 3410029 := bstep (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) B1278761
theorem B3016865 : Blo 370760 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B8063651 : Blo 370760 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B396095 : Blo 370760 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B1411937 : Blo 370760 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B1412225 : Blo 370760 1412225 := bstep (se 2 (by rfl) ⟨529584, by rfl⟩ : syracuseStep 1412225 = 1059169) B1059169
theorem B625819 : Blo 370760 625819 := bstep (se 1 (by rfl) ⟨469364, by rfl⟩ : syracuseStep 625819 = 938729) B938729
theorem B10456253 : Blo 370760 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B1346825 : Blo 370760 1346825 := bstep (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) B1010119
theorem B560447 : Blo 370760 560447 := bstep (se 1 (by rfl) ⟨420335, by rfl⟩ : syracuseStep 560447 = 840671) B840671
theorem B626359 : Blo 370760 626359 := bstep (se 1 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 626359 = 939539) B939539
theorem B3020111 : Blo 370760 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B628735 : Blo 370760 628735 := bstep (se 1 (by rfl) ⟨471551, by rfl⟩ : syracuseStep 628735 = 943103) B943103
theorem B1907023 : Blo 370760 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B530815 : Blo 370760 530815 := bstep (se 1 (by rfl) ⟨398111, by rfl⟩ : syracuseStep 530815 = 796223) B796223
theorem B4037363 : Blo 370760 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B4234031 : Blo 370760 4234031 := bstep (se 1 (by rfl) ⟨3175523, by rfl⟩ : syracuseStep 4234031 = 6351047) B6351047
theorem B3022055 : Blo 370760 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B892463 : Blo 370760 892463 := bstep (se 1 (by rfl) ⟨669347, by rfl⟩ : syracuseStep 892463 = 1338695) B1338695
theorem B630463 : Blo 370760 630463 := bstep (se 1 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 630463 = 945695) B945695
theorem B2826089 : Blo 370760 2826089 := bstep (se 2 (by rfl) ⟨1059783, by rfl⟩ : syracuseStep 2826089 = 2119567) B2119567
theorem B630767 : Blo 370760 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B794873 : Blo 370760 794873 := bstep (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) B596155
theorem B795035 : Blo 370760 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B1516087 : Blo 370760 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B8562095 : Blo 370760 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B5350859 : Blo 370760 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B1025615 : Blo 370760 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B1189991 : Blo 370760 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B371355 : Blo 370760 371355 := bstep (se 1 (by rfl) ⟨278516, by rfl⟩ : syracuseStep 371355 = 557033) B557033
theorem B371367 : Blo 370760 371367 := bstep (se 1 (by rfl) ⟨278525, by rfl⟩ : syracuseStep 371367 = 557051) B557051
theorem B10169003 : Blo 370760 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B371407 : Blo 370760 371407 := bstep (se 1 (by rfl) ⟨278555, by rfl⟩ : syracuseStep 371407 = 557111) B557111
theorem B371431 : Blo 370760 371431 := bstep (se 1 (by rfl) ⟨278573, by rfl⟩ : syracuseStep 371431 = 557147) B557147
theorem B5090039 : Blo 370760 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B371487 : Blo 370760 371487 := bstep (se 1 (by rfl) ⟨278615, by rfl⟩ : syracuseStep 371487 = 557231) B557231
theorem B3615599 : Blo 370760 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B371879 : Blo 370760 371879 := bstep (se 1 (by rfl) ⟨278909, by rfl⟩ : syracuseStep 371879 = 557819) B557819
theorem B371967 : Blo 370760 371967 := bstep (se 1 (by rfl) ⟨278975, by rfl⟩ : syracuseStep 371967 = 557951) B557951
theorem B798187 : Blo 370760 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B12201479 : Blo 370760 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B372767 : Blo 370760 372767 := bstep (se 1 (by rfl) ⟨279575, by rfl⟩ : syracuseStep 372767 = 559151) B559151
theorem B1880171 : Blo 370760 1880171 := bstep (se 1 (by rfl) ⟨1410128, by rfl⟩ : syracuseStep 1880171 = 2820257) B2820257
theorem B1421459 : Blo 370760 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B1781927 : Blo 370760 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B7778749 : Blo 370760 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B373247 : Blo 370760 373247 := bstep (se 1 (by rfl) ⟨279935, by rfl⟩ : syracuseStep 373247 = 559871) B559871
theorem B2175731 : Blo 370760 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B6796115 : Blo 370760 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B1061743 : Blo 370760 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B4043681 : Blo 370760 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B472063 : Blo 370760 472063 := bstep (se 1 (by rfl) ⟨354047, by rfl⟩ : syracuseStep 472063 = 708095) B708095
theorem B472159 : Blo 370760 472159 := bstep (se 1 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 472159 = 708239) B708239
theorem B373871 : Blo 370760 373871 := bstep (se 1 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 373871 = 560807) B560807
theorem B1258685 : Blo 370760 1258685 := bstep (se 3 (by rfl) ⟨236003, by rfl⟩ : syracuseStep 1258685 = 472007) B472007
theorem B373951 : Blo 370760 373951 := bstep (se 1 (by rfl) ⟨280463, by rfl⟩ : syracuseStep 373951 = 560927) B560927
theorem B373983 : Blo 370760 373983 := bstep (se 1 (by rfl) ⟨280487, by rfl⟩ : syracuseStep 373983 = 560975) B560975
theorem B374063 : Blo 370760 374063 := bstep (se 1 (by rfl) ⟨280547, by rfl⟩ : syracuseStep 374063 = 561095) B561095
theorem B374223 : Blo 370760 374223 := bstep (se 1 (by rfl) ⟨280667, by rfl⟩ : syracuseStep 374223 = 561335) B561335
theorem B374271 : Blo 370760 374271 := bstep (se 1 (by rfl) ⟨280703, by rfl⟩ : syracuseStep 374271 = 561407) B561407
theorem B7353865 : Blo 370760 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B374303 : Blo 370760 374303 := bstep (se 1 (by rfl) ⟨280727, by rfl⟩ : syracuseStep 374303 = 561455) B561455
theorem B4765337 : Blo 370760 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B374463 : Blo 370760 374463 := bstep (se 1 (by rfl) ⟨280847, by rfl⟩ : syracuseStep 374463 = 561695) B561695
theorem B374503 : Blo 370760 374503 := bstep (se 1 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 374503 = 561755) B561755
theorem B1881953 : Blo 370760 1881953 := bstep (se 2 (by rfl) ⟨705732, by rfl⟩ : syracuseStep 1881953 = 1411465) B1411465
theorem B374639 : Blo 370760 374639 := bstep (se 1 (by rfl) ⟨280979, by rfl⟩ : syracuseStep 374639 = 561959) B561959
theorem B374751 : Blo 370760 374751 := bstep (se 1 (by rfl) ⟨281063, by rfl⟩ : syracuseStep 374751 = 562127) B562127
theorem B2112095 : Blo 370760 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B1588207 : Blo 370760 1588207 := bstep (se 1 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 1588207 = 2382311) B2382311
theorem B3587075 : Blo 370760 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B834587 : Blo 370760 834587 := bstep (se 1 (by rfl) ⟨625940, by rfl⟩ : syracuseStep 834587 = 1251881) B1251881
theorem B834623 : Blo 370760 834623 := bstep (se 1 (by rfl) ⟨625967, by rfl⟩ : syracuseStep 834623 = 1251935) B1251935
theorem B670847 : Blo 370760 670847 := bstep (se 1 (by rfl) ⟨503135, by rfl⟩ : syracuseStep 670847 = 1006271) B1006271
theorem B834767 : Blo 370760 834767 := bstep (se 1 (by rfl) ⟨626075, by rfl⟩ : syracuseStep 834767 = 1252151) B1252151
theorem B34356575 : Blo 370760 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B1785311 : Blo 370760 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B835487 : Blo 370760 835487 := bstep (se 1 (by rfl) ⟨626615, by rfl⟩ : syracuseStep 835487 = 1253231) B1253231
theorem B2835323 : Blo 370760 2835323 := bstep (se 1 (by rfl) ⟨2126492, by rfl⟩ : syracuseStep 2835323 = 4252985) B4252985
theorem B2376701 : Blo 370760 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B6833483 : Blo 370760 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B1262951 : Blo 370760 1262951 := bstep (se 1 (by rfl) ⟨947213, by rfl⟩ : syracuseStep 1262951 = 1894427) B1894427
theorem B6342299 : Blo 370760 6342299 := bstep (se 1 (by rfl) ⟨4756724, by rfl⟩ : syracuseStep 6342299 = 9513449) B9513449
theorem B837467 : Blo 370760 837467 := bstep (se 1 (by rfl) ⟨628100, by rfl⟩ : syracuseStep 837467 = 1256201) B1256201
theorem B837755 : Blo 370760 837755 := bstep (se 1 (by rfl) ⟨628316, by rfl⟩ : syracuseStep 837755 = 1256633) B1256633
theorem B837863 : Blo 370760 837863 := bstep (se 1 (by rfl) ⟨628397, by rfl⟩ : syracuseStep 837863 = 1256795) B1256795
theorem B838025 : Blo 370760 838025 := bstep (se 2 (by rfl) ⟨314259, by rfl⟩ : syracuseStep 838025 = 628519) B628519
theorem B838457 : Blo 370760 838457 := bstep (se 2 (by rfl) ⟨314421, by rfl⟩ : syracuseStep 838457 = 628843) B628843
theorem B838655 : Blo 370760 838655 := bstep (se 1 (by rfl) ⟨628991, by rfl⟩ : syracuseStep 838655 = 1257983) B1257983
theorem B707791 : Blo 370760 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B3198487 : Blo 370760 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B839195 : Blo 370760 839195 := bstep (se 1 (by rfl) ⟨629396, by rfl⟩ : syracuseStep 839195 = 1258793) B1258793
theorem B1887947 : Blo 370760 1887947 := bstep (se 1 (by rfl) ⟨1415960, by rfl⟩ : syracuseStep 1887947 = 2831921) B2831921
theorem B708679 : Blo 370760 708679 := bstep (se 1 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 708679 = 1063019) B1063019
theorem B839753 : Blo 370760 839753 := bstep (se 2 (by rfl) ⟨314907, by rfl⟩ : syracuseStep 839753 = 629815) B629815
theorem B841769 : Blo 370760 841769 := bstep (se 2 (by rfl) ⟨315663, by rfl⟩ : syracuseStep 841769 = 631327) B631327
theorem B841895 : Blo 370760 841895 := bstep (se 1 (by rfl) ⟨631421, by rfl⟩ : syracuseStep 841895 = 1262843) B1262843
theorem B842039 : Blo 370760 842039 := bstep (se 1 (by rfl) ⟨631529, by rfl⟩ : syracuseStep 842039 = 1263059) B1263059
theorem B3594881 : Blo 370760 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B940967 : Blo 370760 940967 := bstep (se 1 (by rfl) ⟨705725, by rfl⟩ : syracuseStep 940967 = 1411451) B1411451
theorem B3464329 : Blo 370760 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1269377 : Blo 370760 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B30629825 : Blo 370760 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B417919 : Blo 370760 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B1008649 : Blo 370760 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B6055985 : Blo 370760 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B420007 : Blo 370760 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B3598607 : Blo 370760 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B1632635 : Blo 370760 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B1796689 : Blo 370760 1796689 := bstep (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) B1347517
theorem B9268465 : Blo 370760 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B421375 : Blo 370760 421375 := bstep (se 1 (by rfl) ⟨316031, by rfl⟩ : syracuseStep 421375 = 632063) B632063
theorem B946313 : Blo 370760 946313 := bstep (se 2 (by rfl) ⟨354867, by rfl⟩ : syracuseStep 946313 = 709735) B709735
theorem B946687 : Blo 370760 946687 := bstep (se 1 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 946687 = 1420031) B1420031
theorem B13629019 : Blo 370760 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B2685089 : Blo 370760 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B43514329 : Blo 370760 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B5339627 : Blo 370760 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B6912515 : Blo 370760 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B1342777 : Blo 370760 1342777 := bstep (se 2 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 1342777 = 1007083) B1007083
theorem B557225 : Blo 370760 557225 := bstep (se 2 (by rfl) ⟨208959, by rfl⟩ : syracuseStep 557225 = 417919) B417919
theorem B4555655 : Blo 370760 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B4228199 : Blo 370760 4228199 := bstep (se 1 (by rfl) ⟨3171149, by rfl⟩ : syracuseStep 4228199 = 6342299) B6342299
theorem B558311 : Blo 370760 558311 := bstep (se 1 (by rfl) ⟨418733, by rfl⟩ : syracuseStep 558311 = 837467) B837467
theorem B6489395 : Blo 370760 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B1344865 : Blo 370760 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B558503 : Blo 370760 558503 := bstep (se 1 (by rfl) ⟨418877, by rfl⟩ : syracuseStep 558503 = 837755) B837755
theorem B558575 : Blo 370760 558575 := bstep (se 1 (by rfl) ⟨418931, by rfl⟩ : syracuseStep 558575 = 837863) B837863
theorem B558683 : Blo 370760 558683 := bstep (se 1 (by rfl) ⟨419012, by rfl⟩ : syracuseStep 558683 = 838025) B838025
theorem B5375767 : Blo 370760 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B558971 : Blo 370760 558971 := bstep (se 1 (by rfl) ⟨419228, by rfl⟩ : syracuseStep 558971 = 838457) B838457
theorem B559103 : Blo 370760 559103 := bstep (se 1 (by rfl) ⟨419327, by rfl⟩ : syracuseStep 559103 = 838655) B838655
theorem B559463 : Blo 370760 559463 := bstep (se 1 (by rfl) ⟨419597, by rfl⟩ : syracuseStep 559463 = 839195) B839195
theorem B559835 : Blo 370760 559835 := bstep (se 1 (by rfl) ⟨419876, by rfl⟩ : syracuseStep 559835 = 839753) B839753
theorem B560009 : Blo 370760 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B2395585 : Blo 370760 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B561179 : Blo 370760 561179 := bstep (se 1 (by rfl) ⟨420884, by rfl⟩ : syracuseStep 561179 = 841769) B841769
theorem B561263 : Blo 370760 561263 := bstep (se 1 (by rfl) ⟨420947, by rfl⟩ : syracuseStep 561263 = 841895) B841895
theorem B561359 : Blo 370760 561359 := bstep (se 1 (by rfl) ⟨421019, by rfl⟩ : syracuseStep 561359 = 842039) B842039
theorem B12357953 : Blo 370760 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B2396587 : Blo 370760 2396587 := bstep (se 1 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 2396587 = 3594881) B3594881
theorem B2691575 : Blo 370760 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B2822687 : Blo 370760 2822687 := bstep (se 1 (by rfl) ⟨2117015, by rfl⟩ : syracuseStep 2822687 = 4234031) B4234031
theorem B627311 : Blo 370760 627311 := bstep (se 1 (by rfl) ⟨470483, by rfl⟩ : syracuseStep 627311 = 940967) B940967
theorem B561833 : Blo 370760 561833 := bstep (se 2 (by rfl) ⟨210687, by rfl⟩ : syracuseStep 561833 = 421375) B421375
theorem B4264649 : Blo 370760 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B20419883 : Blo 370760 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B529915 : Blo 370760 529915 := bstep (se 1 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 529915 = 794873) B794873
theorem B5708063 : Blo 370760 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B1415657 : Blo 370760 1415657 := bstep (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) B1061743
theorem B629417 : Blo 370760 629417 := bstep (se 2 (by rfl) ⟨236031, by rfl⟩ : syracuseStep 629417 = 472063) B472063
theorem B4037323 : Blo 370760 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B793327 : Blo 370760 793327 := bstep (se 1 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 793327 = 1189991) B1189991
theorem B629545 : Blo 370760 629545 := bstep (se 2 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 629545 = 472159) B472159
theorem B2399071 : Blo 370760 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B1088423 : Blo 370760 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B9805153 : Blo 370760 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B1056253 : Blo 370760 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B8134319 : Blo 370760 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B1253447 : Blo 370760 1253447 := bstep (se 1 (by rfl) ⟨940085, by rfl⟩ : syracuseStep 1253447 = 1880171) B1880171
theorem B630875 : Blo 370760 630875 := bstep (se 1 (by rfl) ⟨473156, by rfl⟩ : syracuseStep 630875 = 946313) B946313
theorem B1187951 : Blo 370760 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B1450487 : Blo 370760 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B4530743 : Blo 370760 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B2695787 : Blo 370760 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B1254635 : Blo 370760 1254635 := bstep (se 1 (by rfl) ⟨940976, by rfl⟩ : syracuseStep 1254635 = 1881953) B1881953
theorem B1190207 : Blo 370760 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B2272043 : Blo 370760 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B371583 : Blo 370760 371583 := bstep (se 1 (by rfl) ⟨278687, by rfl⟩ : syracuseStep 371583 = 557375) B557375
theorem B371695 : Blo 370760 371695 := bstep (se 1 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 371695 = 557543) B557543
theorem B1584467 : Blo 370760 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B372463 : Blo 370760 372463 := bstep (se 1 (by rfl) ⟨279347, by rfl⟩ : syracuseStep 372463 = 558695) B558695
theorem B1880009 : Blo 370760 1880009 := bstep (se 2 (by rfl) ⟨705003, by rfl⟩ : syracuseStep 1880009 = 1410007) B1410007
theorem B2011243 : Blo 370760 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B373631 : Blo 370760 373631 := bstep (se 1 (by rfl) ⟨280223, by rfl⟩ : syracuseStep 373631 = 560447) B560447
theorem B1258631 : Blo 370760 1258631 := bstep (se 1 (by rfl) ⟨943973, by rfl⟩ : syracuseStep 1258631 = 1887947) B1887947
theorem B2013407 : Blo 370760 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B834425 : Blo 370760 834425 := bstep (se 2 (by rfl) ⟨312909, by rfl⟩ : syracuseStep 834425 = 625819) B625819
theorem B1064249 : Blo 370760 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B2014703 : Blo 370760 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B835145 : Blo 370760 835145 := bstep (se 2 (by rfl) ⟨313179, by rfl⟩ : syracuseStep 835145 = 626359) B626359
theorem B1884059 : Blo 370760 1884059 := bstep (se 1 (by rfl) ⟨1413044, by rfl⟩ : syracuseStep 1884059 = 2826089) B2826089
theorem B7160237 : Blo 370760 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B10371665 : Blo 370760 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B1262249 : Blo 370760 1262249 := bstep (se 2 (by rfl) ⟨473343, by rfl⟩ : syracuseStep 1262249 = 946687) B946687
theorem B3393359 : Blo 370760 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2410399 : Blo 370760 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B18172025 : Blo 370760 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B838313 : Blo 370760 838313 := bstep (se 2 (by rfl) ⟨314367, by rfl⟩ : syracuseStep 838313 = 628735) B628735
theorem B1788925 : Blo 370760 1788925 := bstep (se 3 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 1788925 = 670847) B670847
theorem B2542697 : Blo 370760 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B707753 : Blo 370760 707753 := bstep (se 2 (by rfl) ⟨265407, by rfl⟩ : syracuseStep 707753 = 530815) B530815
theorem B58019105 : Blo 370760 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B3591533 : Blo 370760 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B839123 : Blo 370760 839123 := bstep (se 1 (by rfl) ⟨629342, by rfl⟩ : syracuseStep 839123 = 1258685) B1258685
theorem B2117609 : Blo 370760 2117609 := bstep (se 2 (by rfl) ⟨794103, by rfl⟩ : syracuseStep 2117609 = 1588207) B1588207
theorem B2379901 : Blo 370760 2379901 := bstep (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) B892463
theorem B3559751 : Blo 370760 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B4608343 : Blo 370760 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B1790369 : Blo 370760 1790369 := bstep (se 2 (by rfl) ⟨671388, by rfl⟩ : syracuseStep 1790369 = 1342777) B1342777
theorem B840617 : Blo 370760 840617 := bstep (se 2 (by rfl) ⟨315231, by rfl⟩ : syracuseStep 840617 = 630463) B630463
theorem B2119067 : Blo 370760 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B1595143 : Blo 370760 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B1890215 : Blo 370760 1890215 := bstep (se 1 (by rfl) ⟨1417661, by rfl⟩ : syracuseStep 1890215 = 2835323) B2835323
theorem B2021449 : Blo 370760 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B841967 : Blo 370760 841967 := bstep (se 1 (by rfl) ⟨631475, by rfl⟩ : syracuseStep 841967 = 1262951) B1262951
theorem B2120093 : Blo 370760 2120093 := bstep (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) B795035
theorem B941291 : Blo 370760 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B941483 : Blo 370760 941483 := bstep (se 1 (by rfl) ⟨706112, by rfl⟩ : syracuseStep 941483 = 1412225) B1412225
theorem B6970835 : Blo 370760 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B6381665 : Blo 370760 6381665 := bstep (se 2 (by rfl) ⟨2393124, by rfl⟩ : syracuseStep 6381665 = 4786249) B4786249
theorem B4546705 : Blo 370760 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B943721 : Blo 370760 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B846251 : Blo 370760 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B420511 : Blo 370760 420511 := bstep (se 1 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 420511 = 630767) B630767
theorem B944905 : Blo 370760 944905 := bstep (se 2 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 944905 = 708679) B708679
theorem B3567239 : Blo 370760 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B683743 : Blo 370760 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B6779335 : Blo 370760 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B947639 : Blo 370760 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B3176891 : Blo 370760 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B4619105 : Blo 370760 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B1408063 : Blo 370760 1408063 := bstep (se 1 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 1408063 = 2112095) B2112095
theorem B2391383 : Blo 370760 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B556391 : Blo 370760 556391 := bstep (se 1 (by rfl) ⟨417293, by rfl⟩ : syracuseStep 556391 = 834587) B834587
theorem B556415 : Blo 370760 556415 := bstep (se 1 (by rfl) ⟨417311, by rfl⟩ : syracuseStep 556415 = 834623) B834623
theorem B556511 : Blo 370760 556511 := bstep (se 1 (by rfl) ⟨417383, by rfl⟩ : syracuseStep 556511 = 834767) B834767
theorem B22904383 : Blo 370760 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B556991 : Blo 370760 556991 := bstep (se 1 (by rfl) ⟨417743, by rfl⟩ : syracuseStep 556991 = 835487) B835487
theorem B6062273 : Blo 370760 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B6914443 : Blo 370760 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B2818799 : Blo 370760 2818799 := bstep (se 1 (by rfl) ⟨2114099, by rfl⟩ : syracuseStep 2818799 = 4228199) B4228199
theorem B4326263 : Blo 370760 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B2262239 : Blo 370760 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B558875 : Blo 370760 558875 := bstep (se 1 (by rfl) ⟨419156, by rfl⟩ : syracuseStep 558875 = 838313) B838313
theorem B2394355 : Blo 370760 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B559415 : Blo 370760 559415 := bstep (se 1 (by rfl) ⟨419561, by rfl⟩ : syracuseStep 559415 = 839123) B839123
theorem B3213865 : Blo 370760 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B1411739 : Blo 370760 1411739 := bstep (se 1 (by rfl) ⟨1058804, by rfl⟩ : syracuseStep 1411739 = 2117609) B2117609
theorem B560411 : Blo 370760 560411 := bstep (se 1 (by rfl) ⟨420308, by rfl⟩ : syracuseStep 560411 = 840617) B840617
theorem B560681 : Blo 370760 560681 := bstep (se 2 (by rfl) ⟨210255, by rfl⟩ : syracuseStep 560681 = 420511) B420511
theorem B1412711 : Blo 370760 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B561311 : Blo 370760 561311 := bstep (se 1 (by rfl) ⟨420983, by rfl⟩ : syracuseStep 561311 = 841967) B841967
theorem B3805375 : Blo 370760 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B1413395 : Blo 370760 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B725615 : Blo 370760 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B627527 : Blo 370760 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B627655 : Blo 370760 627655 := bstep (se 1 (by rfl) ⟨470741, by rfl⟩ : syracuseStep 627655 = 941483) B941483
theorem B3020495 : Blo 370760 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B629147 : Blo 370760 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B793471 : Blo 370760 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B564167 : Blo 370760 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B1514695 : Blo 370760 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B1056311 : Blo 370760 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B1253339 : Blo 370760 1253339 := bstep (se 1 (by rfl) ⟨940004, by rfl⟩ : syracuseStep 1253339 = 1880009) B1880009
theorem B2695265 : Blo 370760 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B5383097 : Blo 370760 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B631759 : Blo 370760 631759 := bstep (se 1 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 631759 = 947639) B947639
theorem B1057769 : Blo 370760 1057769 := bstep (se 2 (by rfl) ⟨396663, by rfl⟩ : syracuseStep 1057769 = 793327) B793327
theorem B1877417 : Blo 370760 1877417 := bstep (se 2 (by rfl) ⟨704031, by rfl⟩ : syracuseStep 1877417 = 1408063) B1408063
theorem B370927 : Blo 370760 370927 := bstep (se 1 (by rfl) ⟨278195, by rfl⟩ : syracuseStep 370927 = 556391) B556391
theorem B370943 : Blo 370760 370943 := bstep (se 1 (by rfl) ⟨278207, by rfl⟩ : syracuseStep 370943 = 556415) B556415
theorem B371007 : Blo 370760 371007 := bstep (se 1 (by rfl) ⟨278255, by rfl⟩ : syracuseStep 371007 = 556511) B556511
theorem B1256039 : Blo 370760 1256039 := bstep (se 1 (by rfl) ⟨942029, by rfl⟩ : syracuseStep 1256039 = 1884059) B1884059
theorem B371327 : Blo 370760 371327 := bstep (se 1 (by rfl) ⟨278495, by rfl⟩ : syracuseStep 371327 = 556991) B556991
theorem B371483 : Blo 370760 371483 := bstep (se 1 (by rfl) ⟨278612, by rfl⟩ : syracuseStep 371483 = 557225) B557225
theorem B372207 : Blo 370760 372207 := bstep (se 1 (by rfl) ⟨279155, by rfl⟩ : syracuseStep 372207 = 558311) B558311
theorem B372335 : Blo 370760 372335 := bstep (se 1 (by rfl) ⟨279251, by rfl⟩ : syracuseStep 372335 = 558503) B558503
theorem B372383 : Blo 370760 372383 := bstep (se 1 (by rfl) ⟨279287, by rfl⟩ : syracuseStep 372383 = 558575) B558575
theorem B372455 : Blo 370760 372455 := bstep (se 1 (by rfl) ⟨279341, by rfl⟩ : syracuseStep 372455 = 558683) B558683
theorem B372647 : Blo 370760 372647 := bstep (se 1 (by rfl) ⟨279485, by rfl⟩ : syracuseStep 372647 = 558971) B558971
theorem B372735 : Blo 370760 372735 := bstep (se 1 (by rfl) ⟨279551, by rfl⟩ : syracuseStep 372735 = 559103) B559103
theorem B372975 : Blo 370760 372975 := bstep (se 1 (by rfl) ⟨279731, by rfl⟩ : syracuseStep 372975 = 559463) B559463
theorem B373223 : Blo 370760 373223 := bstep (se 1 (by rfl) ⟨279917, by rfl⟩ : syracuseStep 373223 = 559835) B559835
theorem B373339 : Blo 370760 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B471835 : Blo 370760 471835 := bstep (se 1 (by rfl) ⟨353876, by rfl⟩ : syracuseStep 471835 = 707753) B707753
theorem B38679403 : Blo 370760 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B374119 : Blo 370760 374119 := bstep (se 1 (by rfl) ⟨280589, by rfl⟩ : syracuseStep 374119 = 561179) B561179
theorem B374175 : Blo 370760 374175 := bstep (se 1 (by rfl) ⟨280631, by rfl⟩ : syracuseStep 374175 = 561263) B561263
theorem B374239 : Blo 370760 374239 := bstep (se 1 (by rfl) ⟨280679, by rfl⟩ : syracuseStep 374239 = 561359) B561359
theorem B8238635 : Blo 370760 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B2373167 : Blo 370760 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B1193579 : Blo 370760 1193579 := bstep (se 1 (by rfl) ⟨895184, by rfl⟩ : syracuseStep 1193579 = 1790369) B1790369
theorem B1881791 : Blo 370760 1881791 := bstep (se 1 (by rfl) ⟨1411343, by rfl⟩ : syracuseStep 1881791 = 2822687) B2822687
theorem B374555 : Blo 370760 374555 := bstep (se 1 (by rfl) ⟨280916, by rfl⟩ : syracuseStep 374555 = 561833) B561833
theorem B13613255 : Blo 370760 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B1259873 : Blo 370760 1259873 := bstep (se 2 (by rfl) ⟨472452, by rfl⟩ : syracuseStep 1259873 = 944905) B944905
theorem B1260143 : Blo 370760 1260143 := bstep (se 1 (by rfl) ⟨945107, by rfl⟩ : syracuseStep 1260143 = 1890215) B1890215
theorem B3194113 : Blo 370760 3194113 := bstep (se 2 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 3194113 = 2395585) B2395585
theorem B5422879 : Blo 370760 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B835631 : Blo 370760 835631 := bstep (se 1 (by rfl) ⟨626723, by rfl⟩ : syracuseStep 835631 = 1253447) B1253447
theorem B966991 : Blo 370760 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B6144457 : Blo 370760 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B3195449 : Blo 370760 3195449 := bstep (se 2 (by rfl) ⟨1198293, by rfl⟩ : syracuseStep 3195449 = 2396587) B2396587
theorem B836423 : Blo 370760 836423 := bstep (se 1 (by rfl) ⟨627317, by rfl⟩ : syracuseStep 836423 = 1254635) B1254635
theorem B706553 : Blo 370760 706553 := bstep (se 2 (by rfl) ⟨264957, by rfl⟩ : syracuseStep 706553 = 529915) B529915
theorem B2378159 : Blo 370760 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B839087 : Blo 370760 839087 := bstep (se 1 (by rfl) ⟨629315, by rfl⟩ : syracuseStep 839087 = 1258631) B1258631
theorem B839393 : Blo 370760 839393 := bstep (se 2 (by rfl) ⟨314772, by rfl⟩ : syracuseStep 839393 = 629545) B629545
theorem B3198761 : Blo 370760 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B2117927 : Blo 370760 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B709499 : Blo 370760 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B1594255 : Blo 370760 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B4773491 : Blo 370760 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B3167869 : Blo 370760 3167869 := bstep (se 3 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 3167869 = 1187951) B1187951
theorem B841499 : Blo 370760 841499 := bstep (se 1 (by rfl) ⟨631124, by rfl⟩ : syracuseStep 841499 = 1262249) B1262249
theorem B3037103 : Blo 370760 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B12114683 : Blo 370760 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B1793153 : Blo 370760 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B1695131 : Blo 370760 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B7167689 : Blo 370760 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B1794383 : Blo 370760 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B418207 : Blo 370760 418207 := bstep (se 1 (by rfl) ⟨313655, by rfl⟩ : syracuseStep 418207 = 627311) B627311
theorem B2843099 : Blo 370760 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B2385233 : Blo 370760 2385233 := bstep (se 2 (by rfl) ⟨894462, by rfl⟩ : syracuseStep 2385233 = 1788925) B1788925
theorem B943771 : Blo 370760 943771 := bstep (se 1 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 943771 = 1415657) B1415657
theorem B419611 : Blo 370760 419611 := bstep (se 1 (by rfl) ⟨314708, by rfl⟩ : syracuseStep 419611 = 629417) B629417
theorem B911657 : Blo 370760 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B4647223 : Blo 370760 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B420583 : Blo 370760 420583 := bstep (se 1 (by rfl) ⟨315437, by rfl⟩ : syracuseStep 420583 = 630875) B630875
theorem B4254443 : Blo 370760 4254443 := bstep (se 1 (by rfl) ⟨3190832, by rfl⟩ : syracuseStep 4254443 = 6381665) B6381665
theorem B2681657 : Blo 370760 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B3173201 : Blo 370760 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B1797191 : Blo 370760 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B9039113 : Blo 370760 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B2126857 : Blo 370760 2126857 := bstep (se 2 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 2126857 = 1595143) B1595143
theorem B1342271 : Blo 370760 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B13073537 : Blo 370760 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B3079403 : Blo 370760 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B556283 : Blo 370760 556283 := bstep (se 1 (by rfl) ⟨417212, by rfl⟩ : syracuseStep 556283 = 834425) B834425
theorem B1408337 : Blo 370760 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B30539177 : Blo 370760 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B1343135 : Blo 370760 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B556763 : Blo 370760 556763 := bstep (se 1 (by rfl) ⟨417572, by rfl⟩ : syracuseStep 556763 = 835145) B835145
theorem B557087 : Blo 370760 557087 := bstep (se 1 (by rfl) ⟨417815, by rfl⟩ : syracuseStep 557087 = 835631) B835631
theorem B2130299 : Blo 370760 2130299 := bstep (se 1 (by rfl) ⟨1597724, by rfl⟩ : syracuseStep 2130299 = 3195449) B3195449
theorem B557609 : Blo 370760 557609 := bstep (se 2 (by rfl) ⟨209103, by rfl⟩ : syracuseStep 557609 = 418207) B418207
theorem B557615 : Blo 370760 557615 := bstep (se 1 (by rfl) ⟨418211, by rfl⟩ : syracuseStep 557615 = 836423) B836423
theorem B2884175 : Blo 370760 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B8192609 : Blo 370760 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B1508159 : Blo 370760 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B559391 : Blo 370760 559391 := bstep (se 1 (by rfl) ⟨419543, by rfl⟩ : syracuseStep 559391 = 839087) B839087
theorem B559481 : Blo 370760 559481 := bstep (se 2 (by rfl) ⟨209805, by rfl⟩ : syracuseStep 559481 = 419611) B419611
theorem B559595 : Blo 370760 559595 := bstep (se 1 (by rfl) ⟨419696, by rfl⟩ : syracuseStep 559595 = 839393) B839393
theorem B2132507 : Blo 370760 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B1411951 : Blo 370760 1411951 := bstep (se 1 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 1411951 = 2117927) B2117927
theorem B560777 : Blo 370760 560777 := bstep (se 2 (by rfl) ⟨210291, by rfl⟩ : syracuseStep 560777 = 420583) B420583
theorem B3182327 : Blo 370760 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B560999 : Blo 370760 560999 := bstep (se 1 (by rfl) ⟨420749, by rfl⟩ : syracuseStep 560999 = 841499) B841499
theorem B1251611 : Blo 370760 1251611 := bstep (se 1 (by rfl) ⟨938708, by rfl⟩ : syracuseStep 1251611 = 1877417) B1877417
theorem B629113 : Blo 370760 629113 := bstep (se 2 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 629113 = 471835) B471835
theorem B3579389 : Blo 370760 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1582111 : Blo 370760 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B795719 : Blo 370760 795719 := bstep (se 1 (by rfl) ⟨596789, by rfl⟩ : syracuseStep 795719 = 1193579) B1193579
theorem B1254527 : Blo 370760 1254527 := bstep (se 1 (by rfl) ⟨940895, by rfl⟩ : syracuseStep 1254527 = 1881791) B1881791
theorem B1057961 : Blo 370760 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B370855 : Blo 370760 370855 := bstep (se 1 (by rfl) ⟨278141, by rfl⟩ : syracuseStep 370855 = 556283) B556283
theorem B20359451 : Blo 370760 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B895423 : Blo 370760 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B371175 : Blo 370760 371175 := bstep (se 1 (by rfl) ⟨278381, by rfl⟩ : syracuseStep 371175 = 556763) B556763
theorem B4041515 : Blo 370760 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B1289321 : Blo 370760 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B1879199 : Blo 370760 1879199 := bstep (se 1 (by rfl) ⟨1409399, by rfl⟩ : syracuseStep 1879199 = 2818799) B2818799
theorem B9219257 : Blo 370760 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B372583 : Blo 370760 372583 := bstep (se 1 (by rfl) ⟨279437, by rfl⟩ : syracuseStep 372583 = 558875) B558875
theorem B471035 : Blo 370760 471035 := bstep (se 1 (by rfl) ⟨353276, by rfl⟩ : syracuseStep 471035 = 706553) B706553
theorem B372943 : Blo 370760 372943 := bstep (se 1 (by rfl) ⟨279707, by rfl⟩ : syracuseStep 372943 = 559415) B559415
theorem B1585439 : Blo 370760 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B24785189 : Blo 370760 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B373607 : Blo 370760 373607 := bstep (se 1 (by rfl) ⟨280205, by rfl⟩ : syracuseStep 373607 = 560411) B560411
theorem B1258361 : Blo 370760 1258361 := bstep (se 2 (by rfl) ⟨471885, by rfl⟩ : syracuseStep 1258361 = 943771) B943771
theorem B373787 : Blo 370760 373787 := bstep (se 1 (by rfl) ⟨280340, by rfl⟩ : syracuseStep 373787 = 560681) B560681
theorem B374207 : Blo 370760 374207 := bstep (se 1 (by rfl) ⟨280655, by rfl⟩ : syracuseStep 374207 = 561311) B561311
theorem B3192473 : Blo 370760 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B8076455 : Blo 370760 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B376111 : Blo 370760 376111 := bstep (se 1 (by rfl) ⟨282083, by rfl⟩ : syracuseStep 376111 = 564167) B564167
theorem B1195435 : Blo 370760 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B1130087 : Blo 370760 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B704207 : Blo 370760 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B835559 : Blo 370760 835559 := bstep (se 1 (by rfl) ⟨626669, by rfl⟩ : syracuseStep 835559 = 1253339) B1253339
theorem B1196255 : Blo 370760 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B3588731 : Blo 370760 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B705179 : Blo 370760 705179 := bstep (se 1 (by rfl) ⟨528884, by rfl⟩ : syracuseStep 705179 = 1057769) B1057769
theorem B1590155 : Blo 370760 1590155 := bstep (se 1 (by rfl) ⟨1192616, by rfl⟩ : syracuseStep 1590155 = 2385233) B2385233
theorem B836873 : Blo 370760 836873 := bstep (se 2 (by rfl) ⟨313827, by rfl⟩ : syracuseStep 836873 = 627655) B627655
theorem B2835809 : Blo 370760 2835809 := bstep (se 2 (by rfl) ⟨1063428, by rfl⟩ : syracuseStep 2835809 = 2126857) B2126857
theorem B607771 : Blo 370760 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B837359 : Blo 370760 837359 := bstep (se 1 (by rfl) ⟨628019, by rfl⟩ : syracuseStep 837359 = 1256039) B1256039
theorem B2836295 : Blo 370760 2836295 := bstep (se 1 (by rfl) ⟨2127221, by rfl⟩ : syracuseStep 2836295 = 4254443) B4254443
theorem B1787771 : Blo 370760 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B2115467 : Blo 370760 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B1198127 : Blo 370760 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B5492423 : Blo 370760 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B839915 : Blo 370760 839915 := bstep (se 1 (by rfl) ⟨629936, by rfl⟩ : syracuseStep 839915 = 1259873) B1259873
theorem B2019593 : Blo 370760 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B840095 : Blo 370760 840095 := bstep (se 1 (by rfl) ⟨630071, by rfl⟩ : syracuseStep 840095 = 1260143) B1260143
theorem B2052935 : Blo 370760 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B938891 : Blo 370760 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B7230505 : Blo 370760 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B842345 : Blo 370760 842345 := bstep (se 2 (by rfl) ⟨315879, by rfl⟩ : syracuseStep 842345 = 631759) B631759
theorem B941159 : Blo 370760 941159 := bstep (se 1 (by rfl) ⟨705869, by rfl⟩ : syracuseStep 941159 = 1411739) B1411739
theorem B1891997 : Blo 370760 1891997 := bstep (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) B709499
theorem B941807 : Blo 370760 941807 := bstep (se 1 (by rfl) ⟨706355, by rfl⟩ : syracuseStep 941807 = 1412711) B1412711
theorem B942263 : Blo 370760 942263 := bstep (se 1 (by rfl) ⟨706697, by rfl⟩ : syracuseStep 942263 = 1413395) B1413395
theorem B483743 : Blo 370760 483743 := bstep (se 1 (by rfl) ⟨362807, by rfl⟩ : syracuseStep 483743 = 725615) B725615
theorem B418351 : Blo 370760 418351 := bstep (se 1 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 418351 = 627527) B627527
theorem B4285153 : Blo 370760 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B2024735 : Blo 370760 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B419431 : Blo 370760 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B8054653 : Blo 370760 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B4778459 : Blo 370760 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B1796843 : Blo 370760 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B5073833 : Blo 370760 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B1895399 : Blo 370760 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B51572537 : Blo 370760 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B2125673 : Blo 370760 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B4223825 : Blo 370760 4223825 := bstep (se 2 (by rfl) ⟨1583934, by rfl⟩ : syracuseStep 4223825 = 3167869) B3167869
theorem B6026075 : Blo 370760 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B9075503 : Blo 370760 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B4258817 : Blo 370760 4258817 := bstep (se 2 (by rfl) ⟨1597056, by rfl⟩ : syracuseStep 4258817 = 3194113) B3194113
theorem B8715691 : Blo 370760 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B2392487 : Blo 370760 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B557801 : Blo 370760 557801 := bstep (se 2 (by rfl) ⟨209175, by rfl⟩ : syracuseStep 557801 = 418351) B418351
theorem B557915 : Blo 370760 557915 := bstep (se 1 (by rfl) ⟨418436, by rfl⟩ : syracuseStep 557915 = 836873) B836873
theorem B558239 : Blo 370760 558239 := bstep (se 1 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 558239 = 837359) B837359
theorem B1410311 : Blo 370760 1410311 := bstep (se 1 (by rfl) ⟨1057733, by rfl⟩ : syracuseStep 1410311 = 2115467) B2115467
theorem B559241 : Blo 370760 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B559943 : Blo 370760 559943 := bstep (se 1 (by rfl) ⟨419957, by rfl⟩ : syracuseStep 559943 = 839915) B839915
theorem B1346395 : Blo 370760 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B560063 : Blo 370760 560063 := bstep (se 1 (by rfl) ⟨420047, by rfl⟩ : syracuseStep 560063 = 840095) B840095
theorem B2821229 : Blo 370760 2821229 := bstep (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) B1057961
theorem B625927 : Blo 370760 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B561563 : Blo 370760 561563 := bstep (se 1 (by rfl) ⟨421172, by rfl⟩ : syracuseStep 561563 = 842345) B842345
theorem B627439 : Blo 370760 627439 := bstep (se 1 (by rfl) ⟨470579, by rfl⟩ : syracuseStep 627439 = 941159) B941159
theorem B627871 : Blo 370760 627871 := bstep (se 1 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 627871 = 941807) B941807
theorem B628175 : Blo 370760 628175 := bstep (se 1 (by rfl) ⟨471131, by rfl⟩ : syracuseStep 628175 = 942263) B942263
theorem B530479 : Blo 370760 530479 := bstep (se 1 (by rfl) ⟨397859, by rfl⟩ : syracuseStep 530479 = 795719) B795719
theorem B9640673 : Blo 370760 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B13572967 : Blo 370760 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B3185639 : Blo 370760 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B2694343 : Blo 370760 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B3382555 : Blo 370760 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B4791581 : Blo 370760 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B859547 : Blo 370760 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B1252799 : Blo 370760 1252799 := bstep (se 1 (by rfl) ⟨939599, by rfl⟩ : syracuseStep 1252799 = 1879199) B1879199
theorem B34381691 : Blo 370760 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B1417115 : Blo 370760 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B1056959 : Blo 370760 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B16523459 : Blo 370760 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B501481 : Blo 370760 501481 := bstep (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) B376111
theorem B5384303 : Blo 370760 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B469471 : Blo 370760 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B1256093 : Blo 370760 1256093 := bstep (se 3 (by rfl) ⟨235517, by rfl⟩ : syracuseStep 1256093 = 471035) B471035
theorem B371391 : Blo 370760 371391 := bstep (se 1 (by rfl) ⟨278543, by rfl⟩ : syracuseStep 371391 = 557087) B557087
theorem B1420199 : Blo 370760 1420199 := bstep (se 1 (by rfl) ⟨1065149, by rfl⟩ : syracuseStep 1420199 = 2130299) B2130299
theorem B371739 : Blo 370760 371739 := bstep (se 1 (by rfl) ⟨278804, by rfl⟩ : syracuseStep 371739 = 557609) B557609
theorem B371743 : Blo 370760 371743 := bstep (se 1 (by rfl) ⟨278807, by rfl⟩ : syracuseStep 371743 = 557615) B557615
theorem B470119 : Blo 370760 470119 := bstep (se 1 (by rfl) ⟨352589, by rfl⟩ : syracuseStep 470119 = 705179) B705179
theorem B3190013 : Blo 370760 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B1060103 : Blo 370760 1060103 := bstep (se 1 (by rfl) ⟨795077, by rfl⟩ : syracuseStep 1060103 = 1590155) B1590155
theorem B5713537 : Blo 370760 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B1289981 : Blo 370760 1289981 := bstep (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) B483743
theorem B1191847 : Blo 370760 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B798751 : Blo 370760 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B372927 : Blo 370760 372927 := bstep (se 1 (by rfl) ⟨279695, by rfl⟩ : syracuseStep 372927 = 559391) B559391
theorem B372987 : Blo 370760 372987 := bstep (se 1 (by rfl) ⟨279740, by rfl⟩ : syracuseStep 372987 = 559481) B559481
theorem B373063 : Blo 370760 373063 := bstep (se 1 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 373063 = 559595) B559595
theorem B1421671 : Blo 370760 1421671 := bstep (se 1 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 1421671 = 2132507) B2132507
theorem B373851 : Blo 370760 373851 := bstep (se 1 (by rfl) ⟨280388, by rfl⟩ : syracuseStep 373851 = 560777) B560777
theorem B373999 : Blo 370760 373999 := bstep (se 1 (by rfl) ⟨280499, by rfl⟩ : syracuseStep 373999 = 560999) B560999
theorem B1193897 : Blo 370760 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1882601 : Blo 370760 1882601 := bstep (se 2 (by rfl) ⟨705975, by rfl⟩ : syracuseStep 1882601 = 1411951) B1411951
theorem B834407 : Blo 370760 834407 := bstep (se 1 (by rfl) ⟨625805, by rfl⟩ : syracuseStep 834407 = 1251611) B1251611
theorem B1261331 : Blo 370760 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B8437925 : Blo 370760 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B836351 : Blo 370760 836351 := bstep (se 1 (by rfl) ⟨627263, by rfl⟩ : syracuseStep 836351 = 1254527) B1254527
theorem B1263599 : Blo 370760 1263599 := bstep (se 1 (by rfl) ⟨947699, by rfl⟩ : syracuseStep 1263599 = 1895399) B1895399
theorem B6146171 : Blo 370760 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B838817 : Blo 370760 838817 := bstep (se 2 (by rfl) ⟨314556, by rfl⟩ : syracuseStep 838817 = 629113) B629113
theorem B4017383 : Blo 370760 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B838907 : Blo 370760 838907 := bstep (se 1 (by rfl) ⟨629180, by rfl⟩ : syracuseStep 838907 = 1258361) B1258361
theorem B6050335 : Blo 370760 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B11620921 : Blo 370760 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B1593913 : Blo 370760 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B2839211 : Blo 370760 2839211 := bstep (se 1 (by rfl) ⟨2129408, by rfl⟩ : syracuseStep 2839211 = 4258817) B4258817
theorem B1922783 : Blo 370760 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B5461739 : Blo 370760 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B1890539 : Blo 370760 1890539 := bstep (se 1 (by rfl) ⟨1417904, by rfl⟩ : syracuseStep 1890539 = 2835809) B2835809
theorem B1890863 : Blo 370760 1890863 := bstep (se 1 (by rfl) ⟨1418147, by rfl⟩ : syracuseStep 1890863 = 2836295) B2836295
theorem B810361 : Blo 370760 810361 := bstep (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) B607771
theorem B4021757 : Blo 370760 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B3661615 : Blo 370760 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2121551 : Blo 370760 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B10739537 : Blo 370760 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B1368623 : Blo 370760 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B5399293 : Blo 370760 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B2386259 : Blo 370760 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B2815883 : Blo 370760 2815883 := bstep (se 1 (by rfl) ⟨2111912, by rfl⟩ : syracuseStep 2815883 = 4223825) B4223825
theorem B2128315 : Blo 370760 2128315 := bstep (se 1 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 2128315 = 3192473) B3192473
theorem B753391 : Blo 370760 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B557039 : Blo 370760 557039 := bstep (se 1 (by rfl) ⟨417779, by rfl⟩ : syracuseStep 557039 = 835559) B835559
theorem B557567 : Blo 370760 557567 := bstep (se 1 (by rfl) ⟨418175, by rfl⟩ : syracuseStep 557567 = 836351) B836351
theorem B4097447 : Blo 370760 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B559211 : Blo 370760 559211 := bstep (se 1 (by rfl) ⟨419408, by rfl⟩ : syracuseStep 559211 = 838817) B838817
theorem B559271 : Blo 370760 559271 := bstep (se 1 (by rfl) ⟨419453, by rfl⟩ : syracuseStep 559271 = 838907) B838907
theorem B625961 : Blo 370760 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B3641159 : Blo 370760 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B626825 : Blo 370760 626825 := bstep (se 2 (by rfl) ⟨235059, by rfl⟩ : syracuseStep 626825 = 470119) B470119
theorem B6427115 : Blo 370760 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B3183725 : Blo 370760 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B1414367 : Blo 370760 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B11015639 : Blo 370760 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B8067113 : Blo 370760 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B18097289 : Blo 370760 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B1877255 : Blo 370760 1877255 := bstep (se 1 (by rfl) ⟨1407941, by rfl⟩ : syracuseStep 1877255 = 2815883) B2815883
theorem B1255067 : Blo 370760 1255067 := bstep (se 1 (by rfl) ⟨941300, by rfl⟩ : syracuseStep 1255067 = 1882601) B1882601
theorem B371359 : Blo 370760 371359 := bstep (se 1 (by rfl) ⟨278519, by rfl⟩ : syracuseStep 371359 = 557039) B557039
theorem B371867 : Blo 370760 371867 := bstep (se 1 (by rfl) ⟨278900, by rfl⟩ : syracuseStep 371867 = 557801) B557801
theorem B371943 : Blo 370760 371943 := bstep (se 1 (by rfl) ⟨278957, by rfl⟩ : syracuseStep 371943 = 557915) B557915
theorem B372159 : Blo 370760 372159 := bstep (se 1 (by rfl) ⟨279119, by rfl⟩ : syracuseStep 372159 = 558239) B558239
theorem B372827 : Blo 370760 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B373295 : Blo 370760 373295 := bstep (se 1 (by rfl) ⟨279971, by rfl⟩ : syracuseStep 373295 = 559943) B559943
theorem B373375 : Blo 370760 373375 := bstep (se 1 (by rfl) ⟨280031, by rfl⟩ : syracuseStep 373375 = 560063) B560063
theorem B1880819 : Blo 370760 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B374375 : Blo 370760 374375 := bstep (se 1 (by rfl) ⟨280781, by rfl⟩ : syracuseStep 374375 = 561563) B561563
theorem B1260359 : Blo 370760 1260359 := bstep (se 1 (by rfl) ⟨945269, by rfl⟩ : syracuseStep 1260359 = 1890539) B1890539
theorem B834569 : Blo 370760 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B1260575 : Blo 370760 1260575 := bstep (se 1 (by rfl) ⟨945431, by rfl⟩ : syracuseStep 1260575 = 1890863) B1890863
theorem B7618049 : Blo 370760 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B3194387 : Blo 370760 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B573031 : Blo 370760 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B835199 : Blo 370760 835199 := bstep (se 1 (by rfl) ⟨626399, by rfl⟩ : syracuseStep 835199 = 1252799) B1252799
theorem B1589129 : Blo 370760 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B7159691 : Blo 370760 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B22921127 : Blo 370760 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B1065001 : Blo 370760 1065001 := bstep (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) B798751
theorem B704639 : Blo 370760 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B836585 : Blo 370760 836585 := bstep (se 2 (by rfl) ⟨313719, by rfl⟩ : syracuseStep 836585 = 627439) B627439
theorem B3589535 : Blo 370760 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B837161 : Blo 370760 837161 := bstep (se 2 (by rfl) ⟨313935, by rfl⟩ : syracuseStep 837161 = 627871) B627871
theorem B1590839 : Blo 370760 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B837395 : Blo 370760 837395 := bstep (se 1 (by rfl) ⟨628046, by rfl⟩ : syracuseStep 837395 = 1256093) B1256093
theorem B706735 : Blo 370760 706735 := bstep (se 1 (by rfl) ⟨530051, by rfl⟩ : syracuseStep 706735 = 1060103) B1060103
theorem B707305 : Blo 370760 707305 := bstep (se 2 (by rfl) ⟨265239, by rfl⟩ : syracuseStep 707305 = 530479) B530479
theorem B2837753 : Blo 370760 2837753 := bstep (se 2 (by rfl) ⟨1064157, by rfl⟩ : syracuseStep 2837753 = 2128315) B2128315
theorem B2674565 : Blo 370760 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B3592457 : Blo 370760 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B4510073 : Blo 370760 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B1004521 : Blo 370760 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B840887 : Blo 370760 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B5625283 : Blo 370760 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B1594991 : Blo 370760 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B940207 : Blo 370760 940207 := bstep (se 1 (by rfl) ⟨705155, by rfl⟩ : syracuseStep 940207 = 1410311) B1410311
theorem B7199057 : Blo 370760 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B842399 : Blo 370760 842399 := bstep (se 1 (by rfl) ⟨631799, by rfl⟩ : syracuseStep 842399 = 1263599) B1263599
theorem B2678255 : Blo 370760 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B1892807 : Blo 370760 1892807 := bstep (se 1 (by rfl) ⟨1419605, by rfl⟩ : syracuseStep 1892807 = 2839211) B2839211
theorem B418783 : Blo 370760 418783 := bstep (se 1 (by rfl) ⟨314087, by rfl⟩ : syracuseStep 418783 = 628175) B628175
theorem B1795193 : Blo 370760 1795193 := bstep (se 2 (by rfl) ⟨673197, by rfl⟩ : syracuseStep 1795193 = 1346395) B1346395
theorem B2123759 : Blo 370760 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B2681171 : Blo 370760 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B944743 : Blo 370760 944743 := bstep (se 1 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 944743 = 1417115) B1417115
theorem B912415 : Blo 370760 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1895561 : Blo 370760 1895561 := bstep (se 2 (by rfl) ⟨710835, by rfl⟩ : syracuseStep 1895561 = 1421671) B1421671
theorem B15494561 : Blo 370760 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B2125217 : Blo 370760 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B946799 : Blo 370760 946799 := bstep (se 1 (by rfl) ⟨710099, by rfl⟩ : syracuseStep 946799 = 1420199) B1420199
theorem B2126675 : Blo 370760 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B20509685 : Blo 370760 20509685 := bstep (se 5 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 20509685 = 1922783) B1922783
theorem B19528613 : Blo 370760 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B1080481 : Blo 370760 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B556271 : Blo 370760 556271 := bstep (se 1 (by rfl) ⟨417203, by rfl⟩ : syracuseStep 556271 = 834407) B834407
theorem B3439949 : Blo 370760 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B557723 : Blo 370760 557723 := bstep (se 1 (by rfl) ⟨418292, by rfl⟩ : syracuseStep 557723 = 836585) B836585
theorem B2393023 : Blo 370760 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B558107 : Blo 370760 558107 := bstep (se 1 (by rfl) ⟨418580, by rfl⟩ : syracuseStep 558107 = 837161) B837161
theorem B558263 : Blo 370760 558263 := bstep (se 1 (by rfl) ⟨418697, by rfl⟩ : syracuseStep 558263 = 837395) B837395
theorem B558377 : Blo 370760 558377 := bstep (se 2 (by rfl) ⟨209391, by rfl⟩ : syracuseStep 558377 = 418783) B418783
theorem B2394971 : Blo 370760 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B560591 : Blo 370760 560591 := bstep (se 1 (by rfl) ⟨420443, by rfl⟩ : syracuseStep 560591 = 840887) B840887
theorem B7343759 : Blo 370760 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B5378075 : Blo 370760 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B1216553 : Blo 370760 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B561599 : Blo 370760 561599 := bstep (se 1 (by rfl) ⟨421199, by rfl⟩ : syracuseStep 561599 = 842399) B842399
theorem B12064859 : Blo 370760 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B1251503 : Blo 370760 1251503 := bstep (se 1 (by rfl) ⟨938627, by rfl⟩ : syracuseStep 1251503 = 1877255) B1877255
theorem B1415839 : Blo 370760 1415839 := bstep (se 1 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 1415839 = 2123759) B2123759
theorem B10329707 : Blo 370760 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B1416811 : Blo 370760 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B1253609 : Blo 370760 1253609 := bstep (se 2 (by rfl) ⟨470103, by rfl⟩ : syracuseStep 1253609 = 940207) B940207
theorem B631199 : Blo 370760 631199 := bstep (se 1 (by rfl) ⟨473399, by rfl⟩ : syracuseStep 631199 = 946799) B946799
theorem B1253879 : Blo 370760 1253879 := bstep (se 1 (by rfl) ⟨940409, by rfl⟩ : syracuseStep 1253879 = 1880819) B1880819
theorem B1417783 : Blo 370760 1417783 := bstep (se 1 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 1417783 = 2126675) B2126675
theorem B13673123 : Blo 370760 13673123 := bstep (se 1 (by rfl) ⟨10254842, by rfl⟩ : syracuseStep 13673123 = 20509685) B20509685
theorem B13019075 : Blo 370760 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B764041 : Blo 370760 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B370847 : Blo 370760 370847 := bstep (se 1 (by rfl) ⟨278135, by rfl⟩ : syracuseStep 370847 = 556271) B556271
theorem B9709757 : Blo 370760 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B1059419 : Blo 370760 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B15280751 : Blo 370760 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1420001 : Blo 370760 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B1879037 : Blo 370760 1879037 := bstep (se 3 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 1879037 = 704639) B704639
theorem B371711 : Blo 370760 371711 := bstep (se 1 (by rfl) ⟨278783, by rfl⟩ : syracuseStep 371711 = 557567) B557567
theorem B1060559 : Blo 370760 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B372807 : Blo 370760 372807 := bstep (se 1 (by rfl) ⟨279605, by rfl⟩ : syracuseStep 372807 = 559211) B559211
theorem B372847 : Blo 370760 372847 := bstep (se 1 (by rfl) ⟨279635, by rfl⟩ : syracuseStep 372847 = 559271) B559271
theorem B1783043 : Blo 370760 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B1259657 : Blo 370760 1259657 := bstep (se 2 (by rfl) ⟨472371, by rfl⟩ : syracuseStep 1259657 = 944743) B944743
theorem B1063327 : Blo 370760 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B4799371 : Blo 370760 4799371 := bstep (se 1 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 4799371 = 7199057) B7199057
theorem B1785503 : Blo 370760 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B1261871 : Blo 370760 1261871 := bstep (se 1 (by rfl) ⟨946403, by rfl⟩ : syracuseStep 1261871 = 1892807) B1892807
theorem B1196795 : Blo 370760 1196795 := bstep (se 1 (by rfl) ⟨897596, by rfl⟩ : syracuseStep 1196795 = 1795193) B1795193
theorem B836711 : Blo 370760 836711 := bstep (se 1 (by rfl) ⟨627533, by rfl⟩ : syracuseStep 836711 = 1255067) B1255067
theorem B1787447 : Blo 370760 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B1263707 : Blo 370760 1263707 := bstep (se 1 (by rfl) ⟨947780, by rfl⟩ : syracuseStep 1263707 = 1895561) B1895561
theorem B840239 : Blo 370760 840239 := bstep (se 1 (by rfl) ⟨630179, by rfl⟩ : syracuseStep 840239 = 1260359) B1260359
theorem B840383 : Blo 370760 840383 := bstep (se 1 (by rfl) ⟨630287, by rfl⟩ : syracuseStep 840383 = 1260575) B1260575
theorem B4773127 : Blo 370760 4773127 := bstep (se 1 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 4773127 = 7159691) B7159691
theorem B1891835 : Blo 370760 1891835 := bstep (se 1 (by rfl) ⟨1418876, by rfl⟩ : syracuseStep 1891835 = 2837753) B2837753
theorem B417307 : Blo 370760 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B417883 : Blo 370760 417883 := bstep (se 1 (by rfl) ⟨313412, by rfl⟩ : syracuseStep 417883 = 626825) B626825
theorem B942313 : Blo 370760 942313 := bstep (se 2 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 942313 = 706735) B706735
theorem B3006715 : Blo 370760 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B4284743 : Blo 370760 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B2122483 : Blo 370760 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B942911 : Blo 370760 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B943073 : Blo 370760 943073 := bstep (se 2 (by rfl) ⟨353652, by rfl⟩ : syracuseStep 943073 = 707305) B707305
theorem B43706101 : Blo 370760 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B1339361 : Blo 370760 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B7500377 : Blo 370760 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B9173197 : Blo 370760 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B1440641 : Blo 370760 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B556379 : Blo 370760 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B5078699 : Blo 370760 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B2129591 : Blo 370760 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B556799 : Blo 370760 556799 := bstep (se 1 (by rfl) ⟨417599, by rfl⟩ : syracuseStep 556799 = 835199) B835199
theorem B3244141 : Blo 370760 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B557177 : Blo 370760 557177 := bstep (se 2 (by rfl) ⟨208941, by rfl⟩ : syracuseStep 557177 = 417883) B417883
theorem B557807 : Blo 370760 557807 := bstep (se 1 (by rfl) ⟨418355, by rfl⟩ : syracuseStep 557807 = 836711) B836711
theorem B1018721 : Blo 370760 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B560159 : Blo 370760 560159 := bstep (se 1 (by rfl) ⟨420119, by rfl⟩ : syracuseStep 560159 = 840239) B840239
theorem B560255 : Blo 370760 560255 := bstep (se 1 (by rfl) ⟨420191, by rfl⟩ : syracuseStep 560255 = 840383) B840383
theorem B6886471 : Blo 370760 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B9115415 : Blo 370760 9115415 := bstep (se 1 (by rfl) ⟨6836561, by rfl⟩ : syracuseStep 9115415 = 13673123) B13673123
theorem B628607 : Blo 370760 628607 := bstep (se 1 (by rfl) ⟨471455, by rfl⟩ : syracuseStep 628607 = 942911) B942911
theorem B628715 : Blo 370760 628715 := bstep (se 1 (by rfl) ⟨471536, by rfl⟩ : syracuseStep 628715 = 943073) B943073
theorem B2825117 : Blo 370760 2825117 := bstep (se 3 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 2825117 = 1059419) B1059419
theorem B6364169 : Blo 370760 6364169 := bstep (se 2 (by rfl) ⟨2386563, by rfl⟩ : syracuseStep 6364169 = 4773127) B4773127
theorem B1252691 : Blo 370760 1252691 := bstep (se 1 (by rfl) ⟨939518, by rfl⟩ : syracuseStep 1252691 = 1879037) B1879037
theorem B892907 : Blo 370760 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B12230929 : Blo 370760 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1417769 : Blo 370760 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B1188695 : Blo 370760 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B6399161 : Blo 370760 6399161 := bstep (se 2 (by rfl) ⟨2399685, by rfl⟩ : syracuseStep 6399161 = 4799371) B4799371
theorem B4761341 : Blo 370760 4761341 := bstep (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) B1785503
theorem B960427 : Blo 370760 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B370919 : Blo 370760 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B3385799 : Blo 370760 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B1419727 : Blo 370760 1419727 := bstep (se 1 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 1419727 = 2129591) B2129591
theorem B371199 : Blo 370760 371199 := bstep (se 1 (by rfl) ⟨278399, by rfl⟩ : syracuseStep 371199 = 556799) B556799
theorem B1256417 : Blo 370760 1256417 := bstep (se 2 (by rfl) ⟨471156, by rfl⟩ : syracuseStep 1256417 = 942313) B942313
theorem B4008953 : Blo 370760 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B371815 : Blo 370760 371815 := bstep (se 1 (by rfl) ⟨278861, by rfl⟩ : syracuseStep 371815 = 557723) B557723
theorem B797863 : Blo 370760 797863 := bstep (se 1 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 797863 = 1196795) B1196795
theorem B372071 : Blo 370760 372071 := bstep (se 1 (by rfl) ⟨279053, by rfl⟩ : syracuseStep 372071 = 558107) B558107
theorem B372175 : Blo 370760 372175 := bstep (se 1 (by rfl) ⟨279131, by rfl⟩ : syracuseStep 372175 = 558263) B558263
theorem B372251 : Blo 370760 372251 := bstep (se 1 (by rfl) ⟨279188, by rfl⟩ : syracuseStep 372251 = 558377) B558377
theorem B2829977 : Blo 370760 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B1191631 : Blo 370760 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B3190697 : Blo 370760 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B20001005 : Blo 370760 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B373727 : Blo 370760 373727 := bstep (se 1 (by rfl) ⟨280295, by rfl⟩ : syracuseStep 373727 = 560591) B560591
theorem B58274801 : Blo 370760 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B4895839 : Blo 370760 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B3585383 : Blo 370760 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B374399 : Blo 370760 374399 := bstep (se 1 (by rfl) ⟨280799, by rfl⟩ : syracuseStep 374399 = 561599) B561599
theorem B8043239 : Blo 370760 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B834335 : Blo 370760 834335 := bstep (se 1 (by rfl) ⟨625751, by rfl⟩ : syracuseStep 834335 = 1251503) B1251503
theorem B1261223 : Blo 370760 1261223 := bstep (se 1 (by rfl) ⟨945917, by rfl⟩ : syracuseStep 1261223 = 1891835) B1891835
theorem B835739 : Blo 370760 835739 := bstep (se 1 (by rfl) ⟨626804, by rfl⟩ : syracuseStep 835739 = 1253609) B1253609
theorem B835919 : Blo 370760 835919 := bstep (se 1 (by rfl) ⟨626939, by rfl⟩ : syracuseStep 835919 = 1253879) B1253879
theorem B6473171 : Blo 370760 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B707039 : Blo 370760 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B1887785 : Blo 370760 1887785 := bstep (se 2 (by rfl) ⟨707919, by rfl⟩ : syracuseStep 1887785 = 1415839) B1415839
theorem B839771 : Blo 370760 839771 := bstep (se 1 (by rfl) ⟨629828, by rfl⟩ : syracuseStep 839771 = 1259657) B1259657
theorem B1889081 : Blo 370760 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B841247 : Blo 370760 841247 := bstep (se 1 (by rfl) ⟨630935, by rfl⟩ : syracuseStep 841247 = 1261871) B1261871
theorem B1890377 : Blo 370760 1890377 := bstep (se 2 (by rfl) ⟨708891, by rfl⟩ : syracuseStep 1890377 = 1417783) B1417783
theorem B842471 : Blo 370760 842471 := bstep (se 1 (by rfl) ⟨631853, by rfl⟩ : syracuseStep 842471 = 1263707) B1263707
theorem B1596647 : Blo 370760 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B45703925 : Blo 370760 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B420799 : Blo 370760 420799 := bstep (se 1 (by rfl) ⟨315599, by rfl⟩ : syracuseStep 420799 = 631199) B631199
theorem B8679383 : Blo 370760 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B10187167 : Blo 370760 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B946667 : Blo 370760 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B556409 : Blo 370760 556409 := bstep (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) B417307
theorem B557159 : Blo 370760 557159 := bstep (se 1 (by rfl) ⟨417869, by rfl⟩ : syracuseStep 557159 = 835739) B835739
theorem B4325521 : Blo 370760 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B557279 : Blo 370760 557279 := bstep (se 1 (by rfl) ⟨417959, by rfl⟩ : syracuseStep 557279 = 835919) B835919
theorem B1280569 : Blo 370760 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B559847 : Blo 370760 559847 := bstep (se 1 (by rfl) ⟨419885, by rfl⟩ : syracuseStep 559847 = 839771) B839771
theorem B560831 : Blo 370760 560831 := bstep (se 1 (by rfl) ⟨420623, by rfl⟩ : syracuseStep 560831 = 841247) B841247
theorem B561065 : Blo 370760 561065 := bstep (se 2 (by rfl) ⟨210399, by rfl⟩ : syracuseStep 561065 = 420799) B420799
theorem B561647 : Blo 370760 561647 := bstep (se 1 (by rfl) ⟨421235, by rfl⟩ : syracuseStep 561647 = 842471) B842471
theorem B595271 : Blo 370760 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B4266107 : Blo 370760 4266107 := bstep (se 1 (by rfl) ⟨3199580, by rfl⟩ : syracuseStep 4266107 = 6399161) B6399161
theorem B9181961 : Blo 370760 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B6527785 : Blo 370760 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B631111 : Blo 370760 631111 := bstep (se 1 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 631111 = 946667) B946667
theorem B370939 : Blo 370760 370939 := bstep (se 1 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 370939 = 556409) B556409
theorem B371451 : Blo 370760 371451 := bstep (se 1 (by rfl) ⟨278588, by rfl⟩ : syracuseStep 371451 = 557177) B557177
theorem B371871 : Blo 370760 371871 := bstep (se 1 (by rfl) ⟨278903, by rfl⟩ : syracuseStep 371871 = 557807) B557807
theorem B471359 : Blo 370760 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B373439 : Blo 370760 373439 := bstep (se 1 (by rfl) ⟨280079, by rfl⟩ : syracuseStep 373439 = 560159) B560159
theorem B373503 : Blo 370760 373503 := bstep (se 1 (by rfl) ⟨280127, by rfl⟩ : syracuseStep 373503 = 560255) B560255
theorem B1258523 : Blo 370760 1258523 := bstep (se 1 (by rfl) ⟨943892, by rfl⟩ : syracuseStep 1258523 = 1887785) B1887785
theorem B1259387 : Blo 370760 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B6076943 : Blo 370760 6076943 := bstep (se 1 (by rfl) ⟨4557707, by rfl⟩ : syracuseStep 6076943 = 9115415) B9115415
theorem B1260251 : Blo 370760 1260251 := bstep (se 1 (by rfl) ⟨945188, by rfl⟩ : syracuseStep 1260251 = 1890377) B1890377
theorem B1063817 : Blo 370760 1063817 := bstep (se 2 (by rfl) ⟨398931, by rfl⟩ : syracuseStep 1063817 = 797863) B797863
theorem B1883411 : Blo 370760 1883411 := bstep (se 1 (by rfl) ⟨1412558, by rfl⟩ : syracuseStep 1883411 = 2825117) B2825117
theorem B4242779 : Blo 370760 4242779 := bstep (se 1 (by rfl) ⟨3182084, by rfl⟩ : syracuseStep 4242779 = 6364169) B6364169
theorem B1064431 : Blo 370760 1064431 := bstep (se 1 (by rfl) ⟨798323, by rfl⟩ : syracuseStep 1064431 = 1596647) B1596647
theorem B835127 : Blo 370760 835127 := bstep (se 1 (by rfl) ⟨626345, by rfl⟩ : syracuseStep 835127 = 1252691) B1252691
theorem B1588841 : Blo 370760 1588841 := bstep (se 2 (by rfl) ⟨595815, by rfl⟩ : syracuseStep 1588841 = 1191631) B1191631
theorem B13582889 : Blo 370760 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B837611 : Blo 370760 837611 := bstep (se 1 (by rfl) ⟨628208, by rfl⟩ : syracuseStep 837611 = 1256417) B1256417
theorem B2672635 : Blo 370760 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B1886651 : Blo 370760 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B5786255 : Blo 370760 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B38849867 : Blo 370760 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B5362159 : Blo 370760 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B840815 : Blo 370760 840815 := bstep (se 1 (by rfl) ⟨630611, by rfl⟩ : syracuseStep 840815 = 1261223) B1261223
theorem B16307905 : Blo 370760 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B4315447 : Blo 370760 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B679147 : Blo 370760 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B3169853 : Blo 370760 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B1892969 : Blo 370760 1892969 := bstep (se 2 (by rfl) ⟨709863, by rfl⟩ : syracuseStep 1892969 = 1419727) B1419727
theorem B419071 : Blo 370760 419071 := bstep (se 1 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 419071 = 628607) B628607
theorem B419143 : Blo 370760 419143 := bstep (se 1 (by rfl) ⟨314357, by rfl⟩ : syracuseStep 419143 = 628715) B628715
theorem B945179 : Blo 370760 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B30469283 : Blo 370760 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B3174227 : Blo 370760 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B2257199 : Blo 370760 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B2127131 : Blo 370760 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B13334003 : Blo 370760 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B2390255 : Blo 370760 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B556223 : Blo 370760 556223 := bstep (se 1 (by rfl) ⟨417167, by rfl⟩ : syracuseStep 556223 = 834335) B834335
theorem B5767361 : Blo 370760 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B558407 : Blo 370760 558407 := bstep (se 1 (by rfl) ⟨418805, by rfl⟩ : syracuseStep 558407 = 837611) B837611
theorem B558761 : Blo 370760 558761 := bstep (se 2 (by rfl) ⟨209535, by rfl⟩ : syracuseStep 558761 = 419071) B419071
theorem B558857 : Blo 370760 558857 := bstep (se 2 (by rfl) ⟨209571, by rfl⟩ : syracuseStep 558857 = 419143) B419143
theorem B560543 : Blo 370760 560543 := bstep (se 1 (by rfl) ⟨420407, by rfl⟩ : syracuseStep 560543 = 840815) B840815
theorem B1707425 : Blo 370760 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B396847 : Blo 370760 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B7149545 : Blo 370760 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B630119 : Blo 370760 630119 := bstep (se 1 (by rfl) ⟨472589, by rfl⟩ : syracuseStep 630119 = 945179) B945179
theorem B1418087 : Blo 370760 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B8889335 : Blo 370760 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B1419241 : Blo 370760 1419241 := bstep (se 2 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 1419241 = 1064431) B1064431
theorem B370815 : Blo 370760 370815 := bstep (se 1 (by rfl) ⟨278111, by rfl⟩ : syracuseStep 370815 = 556223) B556223
theorem B1255607 : Blo 370760 1255607 := bstep (se 1 (by rfl) ⟨941705, by rfl⟩ : syracuseStep 1255607 = 1883411) B1883411
theorem B2828519 : Blo 370760 2828519 := bstep (se 1 (by rfl) ⟨2121389, by rfl⟩ : syracuseStep 2828519 = 4242779) B4242779
theorem B1059227 : Blo 370760 1059227 := bstep (se 1 (by rfl) ⟨794420, by rfl⟩ : syracuseStep 1059227 = 1588841) B1588841
theorem B371439 : Blo 370760 371439 := bstep (se 1 (by rfl) ⟨278579, by rfl⟩ : syracuseStep 371439 = 557159) B557159
theorem B371519 : Blo 370760 371519 := bstep (se 1 (by rfl) ⟨278639, by rfl⟩ : syracuseStep 371519 = 557279) B557279
theorem B9055259 : Blo 370760 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B1256957 : Blo 370760 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B1257767 : Blo 370760 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B373231 : Blo 370760 373231 := bstep (se 1 (by rfl) ⟨279923, by rfl⟩ : syracuseStep 373231 = 559847) B559847
theorem B25899911 : Blo 370760 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B373887 : Blo 370760 373887 := bstep (se 1 (by rfl) ⟨280415, by rfl⟩ : syracuseStep 373887 = 560831) B560831
theorem B374043 : Blo 370760 374043 := bstep (se 1 (by rfl) ⟨280532, by rfl⟩ : syracuseStep 374043 = 561065) B561065
theorem B374431 : Blo 370760 374431 := bstep (se 1 (by rfl) ⟨280823, by rfl⟩ : syracuseStep 374431 = 561647) B561647
theorem B2113235 : Blo 370760 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B1261979 : Blo 370760 1261979 := bstep (se 1 (by rfl) ⟨946484, by rfl⟩ : syracuseStep 1261979 = 1892969) B1892969
theorem B3622117 : Blo 370760 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B21743873 : Blo 370760 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B2116151 : Blo 370760 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B5753929 : Blo 370760 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B839015 : Blo 370760 839015 := bstep (se 1 (by rfl) ⟨629261, by rfl⟩ : syracuseStep 839015 = 1258523) B1258523
theorem B8703713 : Blo 370760 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B839591 : Blo 370760 839591 := bstep (se 1 (by rfl) ⟨629693, by rfl⟩ : syracuseStep 839591 = 1259387) B1259387
theorem B1593503 : Blo 370760 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B4051295 : Blo 370760 4051295 := bstep (se 1 (by rfl) ⟨3038471, by rfl⟩ : syracuseStep 4051295 = 6076943) B6076943
theorem B840167 : Blo 370760 840167 := bstep (se 1 (by rfl) ⟨630125, by rfl⟩ : syracuseStep 840167 = 1260251) B1260251
theorem B709211 : Blo 370760 709211 := bstep (se 1 (by rfl) ⟨531908, by rfl⟩ : syracuseStep 709211 = 1063817) B1063817
theorem B841481 : Blo 370760 841481 := bstep (se 2 (by rfl) ⟨315555, by rfl⟩ : syracuseStep 841481 = 631111) B631111
theorem B3857503 : Blo 370760 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B3563513 : Blo 370760 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B2844071 : Blo 370760 2844071 := bstep (se 1 (by rfl) ⟨2133053, by rfl⟩ : syracuseStep 2844071 = 4266107) B4266107
theorem B6121307 : Blo 370760 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B20312855 : Blo 370760 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B1504799 : Blo 370760 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B556751 : Blo 370760 556751 := bstep (se 1 (by rfl) ⟨417563, by rfl⟩ : syracuseStep 556751 = 835127) B835127
theorem B1410767 : Blo 370760 1410767 := bstep (se 1 (by rfl) ⟨1058075, by rfl⟩ : syracuseStep 1410767 = 2116151) B2116151
theorem B559343 : Blo 370760 559343 := bstep (se 1 (by rfl) ⟨419507, by rfl⟩ : syracuseStep 559343 = 839015) B839015
theorem B559727 : Blo 370760 559727 := bstep (se 1 (by rfl) ⟨419795, by rfl⟩ : syracuseStep 559727 = 839591) B839591
theorem B560111 : Blo 370760 560111 := bstep (se 1 (by rfl) ⟨420083, by rfl⟩ : syracuseStep 560111 = 840167) B840167
theorem B560987 : Blo 370760 560987 := bstep (se 1 (by rfl) ⟨420740, by rfl⟩ : syracuseStep 560987 = 841481) B841481
theorem B7671905 : Blo 370760 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B529129 : Blo 370760 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B6036839 : Blo 370760 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B13541903 : Blo 370760 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B23209901 : Blo 370760 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B371167 : Blo 370760 371167 := bstep (se 1 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 371167 = 556751) B556751
theorem B3844907 : Blo 370760 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B372271 : Blo 370760 372271 := bstep (se 1 (by rfl) ⟨279203, by rfl⟩ : syracuseStep 372271 = 558407) B558407
theorem B372507 : Blo 370760 372507 := bstep (se 1 (by rfl) ⟨279380, by rfl⟩ : syracuseStep 372507 = 558761) B558761
theorem B372571 : Blo 370760 372571 := bstep (se 1 (by rfl) ⟨279428, by rfl⟩ : syracuseStep 372571 = 558857) B558857
theorem B14495915 : Blo 370760 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B4829489 : Blo 370760 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B373695 : Blo 370760 373695 := bstep (se 1 (by rfl) ⟨280271, by rfl⟩ : syracuseStep 373695 = 560543) B560543
theorem B1062335 : Blo 370760 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B2700863 : Blo 370760 2700863 := bstep (se 1 (by rfl) ⟨2025647, by rfl⟩ : syracuseStep 2700863 = 4051295) B4051295
theorem B472807 : Blo 370760 472807 := bstep (se 1 (by rfl) ⟨354605, by rfl⟩ : syracuseStep 472807 = 709211) B709211
theorem B4766363 : Blo 370760 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B2375675 : Blo 370760 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B4080871 : Blo 370760 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B837071 : Blo 370760 837071 := bstep (se 1 (by rfl) ⟨627803, by rfl⟩ : syracuseStep 837071 = 1255607) B1255607
theorem B1885679 : Blo 370760 1885679 := bstep (se 1 (by rfl) ⟨1414259, by rfl⟩ : syracuseStep 1885679 = 2828519) B2828519
theorem B706151 : Blo 370760 706151 := bstep (se 1 (by rfl) ⟨529613, by rfl⟩ : syracuseStep 706151 = 1059227) B1059227
theorem B837971 : Blo 370760 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B838511 : Blo 370760 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B1003199 : Blo 370760 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B841319 : Blo 370760 841319 := bstep (se 1 (by rfl) ⟨630989, by rfl⟩ : syracuseStep 841319 = 1261979) B1261979
theorem B1138283 : Blo 370760 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B1892321 : Blo 370760 1892321 := bstep (se 2 (by rfl) ⟨709620, by rfl⟩ : syracuseStep 1892321 = 1419241) B1419241
theorem B420079 : Blo 370760 420079 := bstep (se 1 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 420079 = 630119) B630119
theorem B945391 : Blo 370760 945391 := bstep (se 1 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 945391 = 1418087) B1418087
theorem B5926223 : Blo 370760 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B1896047 : Blo 370760 1896047 := bstep (se 1 (by rfl) ⟨1422035, by rfl⟩ : syracuseStep 1896047 = 2844071) B2844071
theorem B17266607 : Blo 370760 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B5143337 : Blo 370760 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1408823 : Blo 370760 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B558047 : Blo 370760 558047 := bstep (se 1 (by rfl) ⟨418535, by rfl⟩ : syracuseStep 558047 = 837071) B837071
theorem B558647 : Blo 370760 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B559007 : Blo 370760 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B5114603 : Blo 370760 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B560105 : Blo 370760 560105 := bstep (se 2 (by rfl) ⟨210039, by rfl⟩ : syracuseStep 560105 = 420079) B420079
theorem B560879 : Blo 370760 560879 := bstep (se 1 (by rfl) ⟨420659, by rfl⟩ : syracuseStep 560879 = 841319) B841319
theorem B758855 : Blo 370760 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B21764645 : Blo 370760 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B15473267 : Blo 370760 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B2563271 : Blo 370760 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B630409 : Blo 370760 630409 := bstep (se 2 (by rfl) ⟨236403, by rfl⟩ : syracuseStep 630409 = 472807) B472807
theorem B3219659 : Blo 370760 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B11511071 : Blo 370760 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B1583783 : Blo 370760 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B1257119 : Blo 370760 1257119 := bstep (se 1 (by rfl) ⟨942839, by rfl⟩ : syracuseStep 1257119 = 1885679) B1885679
theorem B470767 : Blo 370760 470767 := bstep (se 1 (by rfl) ⟨353075, by rfl⟩ : syracuseStep 470767 = 706151) B706151
theorem B372895 : Blo 370760 372895 := bstep (se 1 (by rfl) ⟨279671, by rfl⟩ : syracuseStep 372895 = 559343) B559343
theorem B373151 : Blo 370760 373151 := bstep (se 1 (by rfl) ⟨279863, by rfl⟩ : syracuseStep 373151 = 559727) B559727
theorem B373407 : Blo 370760 373407 := bstep (se 1 (by rfl) ⟨280055, by rfl⟩ : syracuseStep 373407 = 560111) B560111
theorem B373991 : Blo 370760 373991 := bstep (se 1 (by rfl) ⟨280493, by rfl⟩ : syracuseStep 373991 = 560987) B560987
theorem B2832893 : Blo 370760 2832893 := bstep (se 3 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 2832893 = 1062335) B1062335
theorem B1260521 : Blo 370760 1260521 := bstep (se 2 (by rfl) ⟨472695, by rfl⟩ : syracuseStep 1260521 = 945391) B945391
theorem B1261547 : Blo 370760 1261547 := bstep (se 1 (by rfl) ⟨946160, by rfl⟩ : syracuseStep 1261547 = 1892321) B1892321
theorem B9027935 : Blo 370760 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B705505 : Blo 370760 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B3950815 : Blo 370760 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B1264031 : Blo 370760 1264031 := bstep (se 1 (by rfl) ⟨948023, by rfl⟩ : syracuseStep 1264031 = 1896047) B1896047
theorem B2675197 : Blo 370760 2675197 := bstep (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) B1003199
theorem B3428891 : Blo 370760 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B939215 : Blo 370760 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B940511 : Blo 370760 940511 := bstep (se 1 (by rfl) ⟨705383, by rfl⟩ : syracuseStep 940511 = 1410767) B1410767
theorem B4024559 : Blo 370760 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B9663943 : Blo 370760 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B1800575 : Blo 370760 1800575 := bstep (se 1 (by rfl) ⟨1350431, by rfl⟩ : syracuseStep 1800575 = 2700863) B2700863
theorem B3177575 : Blo 370760 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B3409735 : Blo 370760 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B626143 : Blo 370760 626143 := bstep (se 1 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 626143 = 939215) B939215
theorem B627007 : Blo 370760 627007 := bstep (se 1 (by rfl) ⟨470255, by rfl⟩ : syracuseStep 627007 = 940511) B940511
theorem B1708847 : Blo 370760 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B627689 : Blo 370760 627689 := bstep (se 2 (by rfl) ⟨235383, by rfl⟩ : syracuseStep 627689 = 470767) B470767
theorem B7674047 : Blo 370760 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B1055855 : Blo 370760 1055855 := bstep (se 1 (by rfl) ⟨791891, by rfl⟩ : syracuseStep 1055855 = 1583783) B1583783
theorem B12885257 : Blo 370760 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B372031 : Blo 370760 372031 := bstep (se 1 (by rfl) ⟨279023, by rfl⟩ : syracuseStep 372031 = 558047) B558047
theorem B372431 : Blo 370760 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B372671 : Blo 370760 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B373403 : Blo 370760 373403 := bstep (se 1 (by rfl) ⟨280052, by rfl⟩ : syracuseStep 373403 = 560105) B560105
theorem B373919 : Blo 370760 373919 := bstep (se 1 (by rfl) ⟨280439, by rfl⟩ : syracuseStep 373919 = 560879) B560879
theorem B2146439 : Blo 370760 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B838079 : Blo 370760 838079 := bstep (se 1 (by rfl) ⟨628559, by rfl⟩ : syracuseStep 838079 = 1257119) B1257119
theorem B1200383 : Blo 370760 1200383 := bstep (se 1 (by rfl) ⟨900287, by rfl⟩ : syracuseStep 1200383 = 1800575) B1800575
theorem B1888595 : Blo 370760 1888595 := bstep (se 1 (by rfl) ⟨1416446, by rfl⟩ : syracuseStep 1888595 = 2832893) B2832893
theorem B840347 : Blo 370760 840347 := bstep (se 1 (by rfl) ⟨630260, by rfl⟩ : syracuseStep 840347 = 1260521) B1260521
theorem B2118383 : Blo 370760 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B840545 : Blo 370760 840545 := bstep (se 2 (by rfl) ⟨315204, by rfl⟩ : syracuseStep 840545 = 630409) B630409
theorem B841031 : Blo 370760 841031 := bstep (se 1 (by rfl) ⟨630773, by rfl⟩ : syracuseStep 841031 = 1261547) B1261547
theorem B6018623 : Blo 370760 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B940673 : Blo 370760 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B842687 : Blo 370760 842687 := bstep (se 1 (by rfl) ⟨632015, by rfl⟩ : syracuseStep 842687 = 1264031) B1264031
theorem B2023613 : Blo 370760 2023613 := bstep (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) B758855
theorem B5267753 : Blo 370760 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B2285927 : Blo 370760 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B14509763 : Blo 370760 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B10315511 : Blo 370760 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B3566929 : Blo 370760 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B2683039 : Blo 370760 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B558719 : Blo 370760 558719 := bstep (se 1 (by rfl) ⟨419039, by rfl⟩ : syracuseStep 558719 = 838079) B838079
theorem B560231 : Blo 370760 560231 := bstep (se 1 (by rfl) ⟨420173, by rfl⟩ : syracuseStep 560231 = 840347) B840347
theorem B1412255 : Blo 370760 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B560363 : Blo 370760 560363 := bstep (se 1 (by rfl) ⟨420272, by rfl⟩ : syracuseStep 560363 = 840545) B840545
theorem B560687 : Blo 370760 560687 := bstep (se 1 (by rfl) ⟨420515, by rfl⟩ : syracuseStep 560687 = 841031) B841031
theorem B5116031 : Blo 370760 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B627115 : Blo 370760 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B4755905 : Blo 370760 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B561791 : Blo 370760 561791 := bstep (se 1 (by rfl) ⟨421343, by rfl⟩ : syracuseStep 561791 = 842687) B842687
theorem B8590171 : Blo 370760 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B1349075 : Blo 370760 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B3511835 : Blo 370760 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B3577385 : Blo 370760 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B9673175 : Blo 370760 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B800255 : Blo 370760 800255 := bstep (se 1 (by rfl) ⟨600191, by rfl⟩ : syracuseStep 800255 = 1200383) B1200383
theorem B1259063 : Blo 370760 1259063 := bstep (se 1 (by rfl) ⟨944297, by rfl⟩ : syracuseStep 1259063 = 1888595) B1888595
theorem B4012415 : Blo 370760 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B834857 : Blo 370760 834857 := bstep (se 2 (by rfl) ⟨313071, by rfl⟩ : syracuseStep 834857 = 626143) B626143
theorem B703903 : Blo 370760 703903 := bstep (se 1 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 703903 = 1055855) B1055855
theorem B1523951 : Blo 370760 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B836009 : Blo 370760 836009 := bstep (se 2 (by rfl) ⟨313503, by rfl⟩ : syracuseStep 836009 = 627007) B627007
theorem B1430959 : Blo 370760 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B4546313 : Blo 370760 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B1139231 : Blo 370760 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B418459 : Blo 370760 418459 := bstep (se 1 (by rfl) ⟨313844, by rfl⟩ : syracuseStep 418459 = 627689) B627689
theorem B6877007 : Blo 370760 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B1015967 : Blo 370760 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B557339 : Blo 370760 557339 := bstep (se 1 (by rfl) ⟨418004, by rfl⟩ : syracuseStep 557339 = 836009) B836009
theorem B557945 : Blo 370760 557945 := bstep (se 2 (by rfl) ⟨209229, by rfl⟩ : syracuseStep 557945 = 418459) B418459
theorem B3410687 : Blo 370760 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B9539693 : Blo 370760 9539693 := bstep (se 3 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 9539693 = 3577385) B3577385
theorem B1907945 : Blo 370760 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B533503 : Blo 370760 533503 := bstep (se 1 (by rfl) ⟨400127, by rfl⟩ : syracuseStep 533503 = 800255) B800255
theorem B372479 : Blo 370760 372479 := bstep (se 1 (by rfl) ⟨279359, by rfl⟩ : syracuseStep 372479 = 558719) B558719
theorem B373487 : Blo 370760 373487 := bstep (se 1 (by rfl) ⟨280115, by rfl⟩ : syracuseStep 373487 = 560231) B560231
theorem B373575 : Blo 370760 373575 := bstep (se 1 (by rfl) ⟨280181, by rfl⟩ : syracuseStep 373575 = 560363) B560363
theorem B373791 : Blo 370760 373791 := bstep (se 1 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 373791 = 560687) B560687
theorem B374527 : Blo 370760 374527 := bstep (se 1 (by rfl) ⟨280895, by rfl⟩ : syracuseStep 374527 = 561791) B561791
theorem B2341223 : Blo 370760 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B3030875 : Blo 370760 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B836153 : Blo 370760 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B11453561 : Blo 370760 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B839375 : Blo 370760 839375 := bstep (se 1 (by rfl) ⟨629531, by rfl⟩ : syracuseStep 839375 = 1259063) B1259063
theorem B2674943 : Blo 370760 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B938537 : Blo 370760 938537 := bstep (se 2 (by rfl) ⟨351951, by rfl⟩ : syracuseStep 938537 = 703903) B703903
theorem B3037949 : Blo 370760 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B941503 : Blo 370760 941503 := bstep (se 1 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 941503 = 1412255) B1412255
theorem B3170603 : Blo 370760 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B3597533 : Blo 370760 3597533 := bstep (se 3 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 3597533 = 1349075) B1349075
theorem B6448783 : Blo 370760 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B4584671 : Blo 370760 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B556571 : Blo 370760 556571 := bstep (se 1 (by rfl) ⟨417428, by rfl⟩ : syracuseStep 556571 = 834857) B834857
theorem B557435 : Blo 370760 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B7635707 : Blo 370760 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B559583 : Blo 370760 559583 := bstep (se 1 (by rfl) ⟨419687, by rfl⟩ : syracuseStep 559583 = 839375) B839375
theorem B6359795 : Blo 370760 6359795 := bstep (se 1 (by rfl) ⟨4769846, by rfl⟩ : syracuseStep 6359795 = 9539693) B9539693
theorem B625691 : Blo 370760 625691 := bstep (se 1 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 625691 = 938537) B938537
theorem B2398355 : Blo 370760 2398355 := bstep (se 1 (by rfl) ⟨1798766, by rfl⟩ : syracuseStep 2398355 = 3597533) B3597533
theorem B3056447 : Blo 370760 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B1255337 : Blo 370760 1255337 := bstep (se 2 (by rfl) ⟨470751, by rfl⟩ : syracuseStep 1255337 = 941503) B941503
theorem B371047 : Blo 370760 371047 := bstep (se 1 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 371047 = 556571) B556571
theorem B371559 : Blo 370760 371559 := bstep (se 1 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 371559 = 557339) B557339
theorem B371963 : Blo 370760 371963 := bstep (se 1 (by rfl) ⟨278972, by rfl⟩ : syracuseStep 371963 = 557945) B557945
theorem B8598377 : Blo 370760 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B1783295 : Blo 370760 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B2113735 : Blo 370760 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B9095165 : Blo 370760 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B1560815 : Blo 370760 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B2020583 : Blo 370760 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B2709245 : Blo 370760 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B711337 : Blo 370760 711337 := bstep (se 2 (by rfl) ⟨266751, by rfl⟩ : syracuseStep 711337 = 533503) B533503
theorem B2025299 : Blo 370760 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B1271963 : Blo 370760 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B2818313 : Blo 370760 2818313 := bstep (se 2 (by rfl) ⟨1056867, by rfl⟩ : syracuseStep 2818313 = 2113735) B2113735
theorem B6063443 : Blo 370760 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B2037631 : Blo 370760 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B1350199 : Blo 370760 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B1188863 : Blo 370760 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B371623 : Blo 370760 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B5090471 : Blo 370760 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B373055 : Blo 370760 373055 := bstep (se 1 (by rfl) ⟨279791, by rfl⟩ : syracuseStep 373055 = 559583) B559583
theorem B4239863 : Blo 370760 4239863 := bstep (se 1 (by rfl) ⟨3179897, by rfl⟩ : syracuseStep 4239863 = 6359795) B6359795
theorem B5388221 : Blo 370760 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B7224653 : Blo 370760 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B3391901 : Blo 370760 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B836891 : Blo 370760 836891 := bstep (se 1 (by rfl) ⟨627668, by rfl⟩ : syracuseStep 836891 = 1255337) B1255337
theorem B417127 : Blo 370760 417127 := bstep (se 1 (by rfl) ⟨312845, by rfl⟩ : syracuseStep 417127 = 625691) B625691
theorem B1040543 : Blo 370760 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B1598903 : Blo 370760 1598903 := bstep (se 1 (by rfl) ⟨1199177, by rfl⟩ : syracuseStep 1598903 = 2398355) B2398355
theorem B5732251 : Blo 370760 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B948449 : Blo 370760 948449 := bstep (se 2 (by rfl) ⟨355668, by rfl⟩ : syracuseStep 948449 = 711337) B711337
theorem B2261267 : Blo 370760 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B557927 : Blo 370760 557927 := bstep (se 1 (by rfl) ⟨418445, by rfl⟩ : syracuseStep 557927 = 836891) B836891
theorem B693695 : Blo 370760 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B792575 : Blo 370760 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B2826575 : Blo 370760 2826575 := bstep (se 1 (by rfl) ⟨2119931, by rfl⟩ : syracuseStep 2826575 = 4239863) B4239863
theorem B632299 : Blo 370760 632299 := bstep (se 1 (by rfl) ⟨474224, by rfl⟩ : syracuseStep 632299 = 948449) B948449
theorem B1878875 : Blo 370760 1878875 := bstep (se 1 (by rfl) ⟨1409156, by rfl⟩ : syracuseStep 1878875 = 2818313) B2818313
theorem B4042295 : Blo 370760 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B14368589 : Blo 370760 14368589 := bstep (se 3 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 14368589 = 5388221) B5388221
theorem B1065935 : Blo 370760 1065935 := bstep (se 1 (by rfl) ⟨799451, by rfl⟩ : syracuseStep 1065935 = 1598903) B1598903
theorem B3393647 : Blo 370760 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B7201061 : Blo 370760 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B2716841 : Blo 370760 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B556169 : Blo 370760 556169 := bstep (se 2 (by rfl) ⟨208563, by rfl⟩ : syracuseStep 556169 = 417127) B417127
theorem B30572005 : Blo 370760 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B4816435 : Blo 370760 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B1507511 : Blo 370760 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B2262431 : Blo 370760 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B7244909 : Blo 370760 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B528383 : Blo 370760 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B1252583 : Blo 370760 1252583 := bstep (se 1 (by rfl) ⟨939437, by rfl⟩ : syracuseStep 1252583 = 1878875) B1878875
theorem B2694863 : Blo 370760 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B370779 : Blo 370760 370779 := bstep (se 1 (by rfl) ⟨278084, by rfl⟩ : syracuseStep 370779 = 556169) B556169
theorem B9579059 : Blo 370760 9579059 := bstep (se 1 (by rfl) ⟨7184294, by rfl⟩ : syracuseStep 9579059 = 14368589) B14368589
theorem B371951 : Blo 370760 371951 := bstep (se 1 (by rfl) ⟨278963, by rfl⟩ : syracuseStep 371951 = 557927) B557927
theorem B1849853 : Blo 370760 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B4800707 : Blo 370760 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B1884383 : Blo 370760 1884383 := bstep (se 1 (by rfl) ⟨1413287, by rfl⟩ : syracuseStep 1884383 = 2826575) B2826575
theorem B710623 : Blo 370760 710623 := bstep (se 1 (by rfl) ⟨532967, by rfl⟩ : syracuseStep 710623 = 1065935) B1065935
theorem B843065 : Blo 370760 843065 := bstep (se 2 (by rfl) ⟨316149, by rfl⟩ : syracuseStep 843065 = 632299) B632299
theorem B40762673 : Blo 370760 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B6421913 : Blo 370760 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B6033149 : Blo 370760 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B562043 : Blo 370760 562043 := bstep (se 1 (by rfl) ⟨421532, by rfl⟩ : syracuseStep 562043 = 843065) B843065
theorem B27175115 : Blo 370760 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B1256255 : Blo 370760 1256255 := bstep (se 1 (by rfl) ⟨942191, by rfl⟩ : syracuseStep 1256255 = 1884383) B1884383
theorem B4829939 : Blo 370760 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B835055 : Blo 370760 835055 := bstep (se 1 (by rfl) ⟨626291, by rfl⟩ : syracuseStep 835055 = 1252583) B1252583
theorem B1233235 : Blo 370760 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B4281275 : Blo 370760 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B1005007 : Blo 370760 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B3200471 : Blo 370760 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B1796575 : Blo 370760 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B6386039 : Blo 370760 6386039 := bstep (se 1 (by rfl) ⟨4789529, by rfl⟩ : syracuseStep 6386039 = 9579059) B9579059
theorem B947497 : Blo 370760 947497 := bstep (se 2 (by rfl) ⟨355311, by rfl⟩ : syracuseStep 947497 = 710623) B710623
theorem B1409021 : Blo 370760 1409021 := bstep (se 3 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 1409021 = 528383) B528383
theorem B2395433 : Blo 370760 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B2133647 : Blo 370760 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B1644313 : Blo 370760 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B3219959 : Blo 370760 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B11416733 : Blo 370760 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B374695 : Blo 370760 374695 := bstep (se 1 (by rfl) ⟨281021, by rfl⟩ : syracuseStep 374695 = 562043) B562043
theorem B1263329 : Blo 370760 1263329 := bstep (se 2 (by rfl) ⟨473748, by rfl⟩ : syracuseStep 1263329 = 947497) B947497
theorem B837503 : Blo 370760 837503 := bstep (se 1 (by rfl) ⟨628127, by rfl⟩ : syracuseStep 837503 = 1256255) B1256255
theorem B939347 : Blo 370760 939347 := bstep (se 1 (by rfl) ⟨704510, by rfl⟩ : syracuseStep 939347 = 1409021) B1409021
theorem B4022099 : Blo 370760 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B18116743 : Blo 370760 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B1340009 : Blo 370760 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B4257359 : Blo 370760 4257359 := bstep (se 1 (by rfl) ⟨3193019, by rfl⟩ : syracuseStep 4257359 = 6386039) B6386039
theorem B556703 : Blo 370760 556703 := bstep (se 1 (by rfl) ⟨417527, by rfl⟩ : syracuseStep 556703 = 835055) B835055
theorem B558335 : Blo 370760 558335 := bstep (se 1 (by rfl) ⟨418751, by rfl⟩ : syracuseStep 558335 = 837503) B837503
theorem B626231 : Blo 370760 626231 := bstep (se 1 (by rfl) ⟨469673, by rfl⟩ : syracuseStep 626231 = 939347) B939347
theorem B24155657 : Blo 370760 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B893339 : Blo 370760 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B7611155 : Blo 370760 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B371135 : Blo 370760 371135 := bstep (se 1 (by rfl) ⟨278351, by rfl⟩ : syracuseStep 371135 = 556703) B556703
theorem B1422431 : Blo 370760 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B2146639 : Blo 370760 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B2838239 : Blo 370760 2838239 := bstep (se 1 (by rfl) ⟨2128679, by rfl⟩ : syracuseStep 2838239 = 4257359) B4257359
theorem B842219 : Blo 370760 842219 := bstep (se 1 (by rfl) ⟨631664, by rfl⟩ : syracuseStep 842219 = 1263329) B1263329
theorem B1596955 : Blo 370760 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B2681399 : Blo 370760 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B2192417 : Blo 370760 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B561479 : Blo 370760 561479 := bstep (se 1 (by rfl) ⟨421109, by rfl⟩ : syracuseStep 561479 = 842219) B842219
theorem B595559 : Blo 370760 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B2862185 : Blo 370760 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B372223 : Blo 370760 372223 := bstep (se 1 (by rfl) ⟨279167, by rfl⟩ : syracuseStep 372223 = 558335) B558335
theorem B16103771 : Blo 370760 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B1787599 : Blo 370760 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B1461611 : Blo 370760 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B417487 : Blo 370760 417487 := bstep (se 1 (by rfl) ⟨313115, by rfl⟩ : syracuseStep 417487 = 626231) B626231
theorem B1892159 : Blo 370760 1892159 := bstep (se 1 (by rfl) ⟨1419119, by rfl⟩ : syracuseStep 1892159 = 2838239) B2838239
theorem B5074103 : Blo 370760 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B948287 : Blo 370760 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B2129273 : Blo 370760 2129273 := bstep (se 2 (by rfl) ⟨798477, by rfl⟩ : syracuseStep 2129273 = 1596955) B1596955
theorem B3382735 : Blo 370760 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B632191 : Blo 370760 632191 := bstep (se 1 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 632191 = 948287) B948287
theorem B1419515 : Blo 370760 1419515 := bstep (se 1 (by rfl) ⟨1064636, by rfl⟩ : syracuseStep 1419515 = 2129273) B2129273
theorem B374319 : Blo 370760 374319 := bstep (se 1 (by rfl) ⟨280739, by rfl⟩ : syracuseStep 374319 = 561479) B561479
theorem B1588157 : Blo 370760 1588157 := bstep (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) B595559
theorem B1261439 : Blo 370760 1261439 := bstep (se 1 (by rfl) ⟨946079, by rfl⟩ : syracuseStep 1261439 = 1892159) B1892159
theorem B10735847 : Blo 370760 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B30529973 : Blo 370760 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B2383465 : Blo 370760 2383465 := bstep (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) B1787599
theorem B3897629 : Blo 370760 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B556649 : Blo 370760 556649 := bstep (se 2 (by rfl) ⟨208743, by rfl⟩ : syracuseStep 556649 = 417487) B417487
theorem B20353315 : Blo 370760 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B2598419 : Blo 370760 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B1058771 : Blo 370760 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B371099 : Blo 370760 371099 := bstep (se 1 (by rfl) ⟨278324, by rfl⟩ : syracuseStep 371099 = 556649) B556649
theorem B7157231 : Blo 370760 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B4510313 : Blo 370760 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B840959 : Blo 370760 840959 := bstep (se 1 (by rfl) ⟨630719, by rfl⟩ : syracuseStep 840959 = 1261439) B1261439
theorem B842921 : Blo 370760 842921 := bstep (se 2 (by rfl) ⟨316095, by rfl⟩ : syracuseStep 842921 = 632191) B632191
theorem B946343 : Blo 370760 946343 := bstep (se 1 (by rfl) ⟨709757, by rfl⟩ : syracuseStep 946343 = 1419515) B1419515
theorem B3177953 : Blo 370760 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B560639 : Blo 370760 560639 := bstep (se 1 (by rfl) ⟨420479, by rfl⟩ : syracuseStep 560639 = 840959) B840959
theorem B561947 : Blo 370760 561947 := bstep (se 1 (by rfl) ⟨421460, by rfl⟩ : syracuseStep 561947 = 842921) B842921
theorem B27137753 : Blo 370760 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B630895 : Blo 370760 630895 := bstep (se 1 (by rfl) ⟨473171, by rfl⟩ : syracuseStep 630895 = 946343) B946343
theorem B705847 : Blo 370760 705847 := bstep (se 1 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 705847 = 1058771) B1058771
theorem B4771487 : Blo 370760 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B2118635 : Blo 370760 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B3006875 : Blo 370760 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B1732279 : Blo 370760 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B3180991 : Blo 370760 3180991 := bstep (se 1 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 3180991 = 4771487) B4771487
theorem B1412423 : Blo 370760 1412423 := bstep (se 1 (by rfl) ⟨1059317, by rfl⟩ : syracuseStep 1412423 = 2118635) B2118635
theorem B18091835 : Blo 370760 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B2004583 : Blo 370760 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B373759 : Blo 370760 373759 := bstep (se 1 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 373759 = 560639) B560639
theorem B374631 : Blo 370760 374631 := bstep (se 1 (by rfl) ⟨280973, by rfl⟩ : syracuseStep 374631 = 561947) B561947
theorem B2309705 : Blo 370760 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B841193 : Blo 370760 841193 := bstep (se 2 (by rfl) ⟨315447, by rfl⟩ : syracuseStep 841193 = 630895) B630895
theorem B941129 : Blo 370760 941129 := bstep (se 2 (by rfl) ⟨352923, by rfl⟩ : syracuseStep 941129 = 705847) B705847
theorem B12061223 : Blo 370760 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B560795 : Blo 370760 560795 := bstep (se 1 (by rfl) ⟨420596, by rfl⟩ : syracuseStep 560795 = 841193) B841193
theorem B627419 : Blo 370760 627419 := bstep (se 1 (by rfl) ⟨470564, by rfl⟩ : syracuseStep 627419 = 941129) B941129
theorem B4241321 : Blo 370760 4241321 := bstep (se 2 (by rfl) ⟨1590495, by rfl⟩ : syracuseStep 4241321 = 3180991) B3180991
theorem B2672777 : Blo 370760 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B941615 : Blo 370760 941615 := bstep (se 1 (by rfl) ⟨706211, by rfl⟩ : syracuseStep 941615 = 1412423) B1412423
theorem B1539803 : Blo 370760 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B627743 : Blo 370760 627743 := bstep (se 1 (by rfl) ⟨470807, by rfl⟩ : syracuseStep 627743 = 941615) B941615
theorem B2827547 : Blo 370760 2827547 := bstep (se 1 (by rfl) ⟨2120660, by rfl⟩ : syracuseStep 2827547 = 4241321) B4241321
theorem B1026535 : Blo 370760 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B1781851 : Blo 370760 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B8040815 : Blo 370760 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B373863 : Blo 370760 373863 := bstep (se 1 (by rfl) ⟨280397, by rfl⟩ : syracuseStep 373863 = 560795) B560795
theorem B418279 : Blo 370760 418279 := bstep (se 1 (by rfl) ⟨313709, by rfl⟩ : syracuseStep 418279 = 627419) B627419
theorem B557705 : Blo 370760 557705 := bstep (se 2 (by rfl) ⟨209139, by rfl⟩ : syracuseStep 557705 = 418279) B418279
theorem B2375801 : Blo 370760 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B1885031 : Blo 370760 1885031 := bstep (se 1 (by rfl) ⟨1413773, by rfl⟩ : syracuseStep 1885031 = 2827547) B2827547
theorem B5360543 : Blo 370760 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B1368713 : Blo 370760 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B418495 : Blo 370760 418495 := bstep (se 1 (by rfl) ⟨313871, by rfl⟩ : syracuseStep 418495 = 627743) B627743
theorem B557993 : Blo 370760 557993 := bstep (se 2 (by rfl) ⟨209247, by rfl⟩ : syracuseStep 557993 = 418495) B418495
theorem B3573695 : Blo 370760 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B1583867 : Blo 370760 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B371803 : Blo 370760 371803 := bstep (se 1 (by rfl) ⟨278852, by rfl⟩ : syracuseStep 371803 = 557705) B557705
theorem B1256687 : Blo 370760 1256687 := bstep (se 1 (by rfl) ⟨942515, by rfl⟩ : syracuseStep 1256687 = 1885031) B1885031
theorem B912475 : Blo 370760 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B1216633 : Blo 370760 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B1055911 : Blo 370760 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B371995 : Blo 370760 371995 := bstep (se 1 (by rfl) ⟨278996, by rfl⟩ : syracuseStep 371995 = 557993) B557993
theorem B837791 : Blo 370760 837791 := bstep (se 1 (by rfl) ⟨628343, by rfl⟩ : syracuseStep 837791 = 1256687) B1256687
theorem B2382463 : Blo 370760 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B558527 : Blo 370760 558527 := bstep (se 1 (by rfl) ⟨418895, by rfl⟩ : syracuseStep 558527 = 837791) B837791
theorem B1622177 : Blo 370760 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B3176617 : Blo 370760 3176617 := bstep (se 2 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 3176617 = 2382463) B2382463
theorem B1407881 : Blo 370760 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B1081451 : Blo 370760 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B4235489 : Blo 370760 4235489 := bstep (se 2 (by rfl) ⟨1588308, by rfl⟩ : syracuseStep 4235489 = 3176617) B3176617
theorem B372351 : Blo 370760 372351 := bstep (se 1 (by rfl) ⟨279263, by rfl⟩ : syracuseStep 372351 = 558527) B558527
theorem B938587 : Blo 370760 938587 := bstep (se 1 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 938587 = 1407881) B1407881
theorem B2883869 : Blo 370760 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B2823659 : Blo 370760 2823659 := bstep (se 1 (by rfl) ⟨2117744, by rfl⟩ : syracuseStep 2823659 = 4235489) B4235489
theorem B1251449 : Blo 370760 1251449 := bstep (se 2 (by rfl) ⟨469293, by rfl⟩ : syracuseStep 1251449 = 938587) B938587
theorem B1882439 : Blo 370760 1882439 := bstep (se 1 (by rfl) ⟨1411829, by rfl⟩ : syracuseStep 1882439 = 2823659) B2823659
theorem B834299 : Blo 370760 834299 := bstep (se 1 (by rfl) ⟨625724, by rfl⟩ : syracuseStep 834299 = 1251449) B1251449
theorem B1922579 : Blo 370760 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B1281719 : Blo 370760 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B1254959 : Blo 370760 1254959 := bstep (se 1 (by rfl) ⟨941219, by rfl⟩ : syracuseStep 1254959 = 1882439) B1882439
theorem B556199 : Blo 370760 556199 := bstep (se 1 (by rfl) ⟨417149, by rfl⟩ : syracuseStep 556199 = 834299) B834299
theorem B854479 : Blo 370760 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B370799 : Blo 370760 370799 := bstep (se 1 (by rfl) ⟨278099, by rfl⟩ : syracuseStep 370799 = 556199) B556199
theorem B836639 : Blo 370760 836639 := bstep (se 1 (by rfl) ⟨627479, by rfl⟩ : syracuseStep 836639 = 1254959) B1254959
theorem B557759 : Blo 370760 557759 := bstep (se 1 (by rfl) ⟨418319, by rfl⟩ : syracuseStep 557759 = 836639) B836639
theorem B1139305 : Blo 370760 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B371839 : Blo 370760 371839 := bstep (se 1 (by rfl) ⟨278879, by rfl⟩ : syracuseStep 371839 = 557759) B557759
theorem B1519073 : Blo 370760 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B1012715 : Blo 370760 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B675143 : Blo 370760 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715
theorem B450095 : Blo 370760 450095 := bstep (se 1 (by rfl) ⟨337571, by rfl⟩ : syracuseStep 450095 = 675143) B675143
theorem B1200253 : Blo 370760 1200253 := bstep (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) B450095
theorem B1600337 : Blo 370760 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B4267565 : Blo 370760 4267565 := bstep (se 3 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 4267565 = 1600337) B1600337
theorem B2845043 : Blo 370760 2845043 := bstep (se 1 (by rfl) ⟨2133782, by rfl⟩ : syracuseStep 2845043 = 4267565) B4267565
theorem B1896695 : Blo 370760 1896695 := bstep (se 1 (by rfl) ⟨1422521, by rfl⟩ : syracuseStep 1896695 = 2845043) B2845043
theorem B1264463 : Blo 370760 1264463 := bstep (se 1 (by rfl) ⟨948347, by rfl⟩ : syracuseStep 1264463 = 1896695) B1896695
theorem B842975 : Blo 370760 842975 := bstep (se 1 (by rfl) ⟨632231, by rfl⟩ : syracuseStep 842975 = 1264463) B1264463
theorem B561983 : Blo 370760 561983 := bstep (se 1 (by rfl) ⟨421487, by rfl⟩ : syracuseStep 561983 = 842975) B842975
theorem B374655 : Blo 370760 374655 := bstep (se 1 (by rfl) ⟨280991, by rfl⟩ : syracuseStep 374655 = 561983) B561983

theorem C0 (j : ℕ) (h1 : 92690 ≤ j) (h2 : j ≤ 93389) : Blo 370760 (4 * j + 3) := by
  interval_cases j
  · exact B370763
  · exact B370767
  · exact B370771
  · exact B370775
  · exact B370779
  · exact B370783
  · exact B370787
  · exact B370791
  · exact B370795
  · exact B370799
  · exact B370803
  · exact B370807
  · exact B370811
  · exact B370815
  · exact B370819
  · exact B370823
  · exact B370827
  · exact B370831
  · exact B370835
  · exact B370839
  · exact B370843
  · exact B370847
  · exact B370851
  · exact B370855
  · exact B370859
  · exact B370863
  · exact B370867
  · exact B370871
  · exact B370875
  · exact B370879
  · exact B370883
  · exact B370887
  · exact B370891
  · exact B370895
  · exact B370899
  · exact B370903
  · exact B370907
  · exact B370911
  · exact B370915
  · exact B370919
  · exact B370923
  · exact B370927
  · exact B370931
  · exact B370935
  · exact B370939
  · exact B370943
  · exact B370947
  · exact B370951
  · exact B370955
  · exact B370959
  · exact B370963
  · exact B370967
  · exact B370971
  · exact B370975
  · exact B370979
  · exact B370983
  · exact B370987
  · exact B370991
  · exact B370995
  · exact B370999
  · exact B371003
  · exact B371007
  · exact B371011
  · exact B371015
  · exact B371019
  · exact B371023
  · exact B371027
  · exact B371031
  · exact B371035
  · exact B371039
  · exact B371043
  · exact B371047
  · exact B371051
  · exact B371055
  · exact B371059
  · exact B371063
  · exact B371067
  · exact B371071
  · exact B371075
  · exact B371079
  · exact B371083
  · exact B371087
  · exact B371091
  · exact B371095
  · exact B371099
  · exact B371103
  · exact B371107
  · exact B371111
  · exact B371115
  · exact B371119
  · exact B371123
  · exact B371127
  · exact B371131
  · exact B371135
  · exact B371139
  · exact B371143
  · exact B371147
  · exact B371151
  · exact B371155
  · exact B371159
  · exact B371163
  · exact B371167
  · exact B371171
  · exact B371175
  · exact B371179
  · exact B371183
  · exact B371187
  · exact B371191
  · exact B371195
  · exact B371199
  · exact B371203
  · exact B371207
  · exact B371211
  · exact B371215
  · exact B371219
  · exact B371223
  · exact B371227
  · exact B371231
  · exact B371235
  · exact B371239
  · exact B371243
  · exact B371247
  · exact B371251
  · exact B371255
  · exact B371259
  · exact B371263
  · exact B371267
  · exact B371271
  · exact B371275
  · exact B371279
  · exact B371283
  · exact B371287
  · exact B371291
  · exact B371295
  · exact B371299
  · exact B371303
  · exact B371307
  · exact B371311
  · exact B371315
  · exact B371319
  · exact B371323
  · exact B371327
  · exact B371331
  · exact B371335
  · exact B371339
  · exact B371343
  · exact B371347
  · exact B371351
  · exact B371355
  · exact B371359
  · exact B371363
  · exact B371367
  · exact B371371
  · exact B371375
  · exact B371379
  · exact B371383
  · exact B371387
  · exact B371391
  · exact B371395
  · exact B371399
  · exact B371403
  · exact B371407
  · exact B371411
  · exact B371415
  · exact B371419
  · exact B371423
  · exact B371427
  · exact B371431
  · exact B371435
  · exact B371439
  · exact B371443
  · exact B371447
  · exact B371451
  · exact B371455
  · exact B371459
  · exact B371463
  · exact B371467
  · exact B371471
  · exact B371475
  · exact B371479
  · exact B371483
  · exact B371487
  · exact B371491
  · exact B371495
  · exact B371499
  · exact B371503
  · exact B371507
  · exact B371511
  · exact B371515
  · exact B371519
  · exact B371523
  · exact B371527
  · exact B371531
  · exact B371535
  · exact B371539
  · exact B371543
  · exact B371547
  · exact B371551
  · exact B371555
  · exact B371559
  · exact B371563
  · exact B371567
  · exact B371571
  · exact B371575
  · exact B371579
  · exact B371583
  · exact B371587
  · exact B371591
  · exact B371595
  · exact B371599
  · exact B371603
  · exact B371607
  · exact B371611
  · exact B371615
  · exact B371619
  · exact B371623
  · exact B371627
  · exact B371631
  · exact B371635
  · exact B371639
  · exact B371643
  · exact B371647
  · exact B371651
  · exact B371655
  · exact B371659
  · exact B371663
  · exact B371667
  · exact B371671
  · exact B371675
  · exact B371679
  · exact B371683
  · exact B371687
  · exact B371691
  · exact B371695
  · exact B371699
  · exact B371703
  · exact B371707
  · exact B371711
  · exact B371715
  · exact B371719
  · exact B371723
  · exact B371727
  · exact B371731
  · exact B371735
  · exact B371739
  · exact B371743
  · exact B371747
  · exact B371751
  · exact B371755
  · exact B371759
  · exact B371763
  · exact B371767
  · exact B371771
  · exact B371775
  · exact B371779
  · exact B371783
  · exact B371787
  · exact B371791
  · exact B371795
  · exact B371799
  · exact B371803
  · exact B371807
  · exact B371811
  · exact B371815
  · exact B371819
  · exact B371823
  · exact B371827
  · exact B371831
  · exact B371835
  · exact B371839
  · exact B371843
  · exact B371847
  · exact B371851
  · exact B371855
  · exact B371859
  · exact B371863
  · exact B371867
  · exact B371871
  · exact B371875
  · exact B371879
  · exact B371883
  · exact B371887
  · exact B371891
  · exact B371895
  · exact B371899
  · exact B371903
  · exact B371907
  · exact B371911
  · exact B371915
  · exact B371919
  · exact B371923
  · exact B371927
  · exact B371931
  · exact B371935
  · exact B371939
  · exact B371943
  · exact B371947
  · exact B371951
  · exact B371955
  · exact B371959
  · exact B371963
  · exact B371967
  · exact B371971
  · exact B371975
  · exact B371979
  · exact B371983
  · exact B371987
  · exact B371991
  · exact B371995
  · exact B371999
  · exact B372003
  · exact B372007
  · exact B372011
  · exact B372015
  · exact B372019
  · exact B372023
  · exact B372027
  · exact B372031
  · exact B372035
  · exact B372039
  · exact B372043
  · exact B372047
  · exact B372051
  · exact B372055
  · exact B372059
  · exact B372063
  · exact B372067
  · exact B372071
  · exact B372075
  · exact B372079
  · exact B372083
  · exact B372087
  · exact B372091
  · exact B372095
  · exact B372099
  · exact B372103
  · exact B372107
  · exact B372111
  · exact B372115
  · exact B372119
  · exact B372123
  · exact B372127
  · exact B372131
  · exact B372135
  · exact B372139
  · exact B372143
  · exact B372147
  · exact B372151
  · exact B372155
  · exact B372159
  · exact B372163
  · exact B372167
  · exact B372171
  · exact B372175
  · exact B372179
  · exact B372183
  · exact B372187
  · exact B372191
  · exact B372195
  · exact B372199
  · exact B372203
  · exact B372207
  · exact B372211
  · exact B372215
  · exact B372219
  · exact B372223
  · exact B372227
  · exact B372231
  · exact B372235
  · exact B372239
  · exact B372243
  · exact B372247
  · exact B372251
  · exact B372255
  · exact B372259
  · exact B372263
  · exact B372267
  · exact B372271
  · exact B372275
  · exact B372279
  · exact B372283
  · exact B372287
  · exact B372291
  · exact B372295
  · exact B372299
  · exact B372303
  · exact B372307
  · exact B372311
  · exact B372315
  · exact B372319
  · exact B372323
  · exact B372327
  · exact B372331
  · exact B372335
  · exact B372339
  · exact B372343
  · exact B372347
  · exact B372351
  · exact B372355
  · exact B372359
  · exact B372363
  · exact B372367
  · exact B372371
  · exact B372375
  · exact B372379
  · exact B372383
  · exact B372387
  · exact B372391
  · exact B372395
  · exact B372399
  · exact B372403
  · exact B372407
  · exact B372411
  · exact B372415
  · exact B372419
  · exact B372423
  · exact B372427
  · exact B372431
  · exact B372435
  · exact B372439
  · exact B372443
  · exact B372447
  · exact B372451
  · exact B372455
  · exact B372459
  · exact B372463
  · exact B372467
  · exact B372471
  · exact B372475
  · exact B372479
  · exact B372483
  · exact B372487
  · exact B372491
  · exact B372495
  · exact B372499
  · exact B372503
  · exact B372507
  · exact B372511
  · exact B372515
  · exact B372519
  · exact B372523
  · exact B372527
  · exact B372531
  · exact B372535
  · exact B372539
  · exact B372543
  · exact B372547
  · exact B372551
  · exact B372555
  · exact B372559
  · exact B372563
  · exact B372567
  · exact B372571
  · exact B372575
  · exact B372579
  · exact B372583
  · exact B372587
  · exact B372591
  · exact B372595
  · exact B372599
  · exact B372603
  · exact B372607
  · exact B372611
  · exact B372615
  · exact B372619
  · exact B372623
  · exact B372627
  · exact B372631
  · exact B372635
  · exact B372639
  · exact B372643
  · exact B372647
  · exact B372651
  · exact B372655
  · exact B372659
  · exact B372663
  · exact B372667
  · exact B372671
  · exact B372675
  · exact B372679
  · exact B372683
  · exact B372687
  · exact B372691
  · exact B372695
  · exact B372699
  · exact B372703
  · exact B372707
  · exact B372711
  · exact B372715
  · exact B372719
  · exact B372723
  · exact B372727
  · exact B372731
  · exact B372735
  · exact B372739
  · exact B372743
  · exact B372747
  · exact B372751
  · exact B372755
  · exact B372759
  · exact B372763
  · exact B372767
  · exact B372771
  · exact B372775
  · exact B372779
  · exact B372783
  · exact B372787
  · exact B372791
  · exact B372795
  · exact B372799
  · exact B372803
  · exact B372807
  · exact B372811
  · exact B372815
  · exact B372819
  · exact B372823
  · exact B372827
  · exact B372831
  · exact B372835
  · exact B372839
  · exact B372843
  · exact B372847
  · exact B372851
  · exact B372855
  · exact B372859
  · exact B372863
  · exact B372867
  · exact B372871
  · exact B372875
  · exact B372879
  · exact B372883
  · exact B372887
  · exact B372891
  · exact B372895
  · exact B372899
  · exact B372903
  · exact B372907
  · exact B372911
  · exact B372915
  · exact B372919
  · exact B372923
  · exact B372927
  · exact B372931
  · exact B372935
  · exact B372939
  · exact B372943
  · exact B372947
  · exact B372951
  · exact B372955
  · exact B372959
  · exact B372963
  · exact B372967
  · exact B372971
  · exact B372975
  · exact B372979
  · exact B372983
  · exact B372987
  · exact B372991
  · exact B372995
  · exact B372999
  · exact B373003
  · exact B373007
  · exact B373011
  · exact B373015
  · exact B373019
  · exact B373023
  · exact B373027
  · exact B373031
  · exact B373035
  · exact B373039
  · exact B373043
  · exact B373047
  · exact B373051
  · exact B373055
  · exact B373059
  · exact B373063
  · exact B373067
  · exact B373071
  · exact B373075
  · exact B373079
  · exact B373083
  · exact B373087
  · exact B373091
  · exact B373095
  · exact B373099
  · exact B373103
  · exact B373107
  · exact B373111
  · exact B373115
  · exact B373119
  · exact B373123
  · exact B373127
  · exact B373131
  · exact B373135
  · exact B373139
  · exact B373143
  · exact B373147
  · exact B373151
  · exact B373155
  · exact B373159
  · exact B373163
  · exact B373167
  · exact B373171
  · exact B373175
  · exact B373179
  · exact B373183
  · exact B373187
  · exact B373191
  · exact B373195
  · exact B373199
  · exact B373203
  · exact B373207
  · exact B373211
  · exact B373215
  · exact B373219
  · exact B373223
  · exact B373227
  · exact B373231
  · exact B373235
  · exact B373239
  · exact B373243
  · exact B373247
  · exact B373251
  · exact B373255
  · exact B373259
  · exact B373263
  · exact B373267
  · exact B373271
  · exact B373275
  · exact B373279
  · exact B373283
  · exact B373287
  · exact B373291
  · exact B373295
  · exact B373299
  · exact B373303
  · exact B373307
  · exact B373311
  · exact B373315
  · exact B373319
  · exact B373323
  · exact B373327
  · exact B373331
  · exact B373335
  · exact B373339
  · exact B373343
  · exact B373347
  · exact B373351
  · exact B373355
  · exact B373359
  · exact B373363
  · exact B373367
  · exact B373371
  · exact B373375
  · exact B373379
  · exact B373383
  · exact B373387
  · exact B373391
  · exact B373395
  · exact B373399
  · exact B373403
  · exact B373407
  · exact B373411
  · exact B373415
  · exact B373419
  · exact B373423
  · exact B373427
  · exact B373431
  · exact B373435
  · exact B373439
  · exact B373443
  · exact B373447
  · exact B373451
  · exact B373455
  · exact B373459
  · exact B373463
  · exact B373467
  · exact B373471
  · exact B373475
  · exact B373479
  · exact B373483
  · exact B373487
  · exact B373491
  · exact B373495
  · exact B373499
  · exact B373503
  · exact B373507
  · exact B373511
  · exact B373515
  · exact B373519
  · exact B373523
  · exact B373527
  · exact B373531
  · exact B373535
  · exact B373539
  · exact B373543
  · exact B373547
  · exact B373551
  · exact B373555
  · exact B373559

theorem C1 (j : ℕ) (h1 : 93390 ≤ j) (h2 : j ≤ 93689) : Blo 370760 (4 * j + 3) := by
  interval_cases j
  · exact B373563
  · exact B373567
  · exact B373571
  · exact B373575
  · exact B373579
  · exact B373583
  · exact B373587
  · exact B373591
  · exact B373595
  · exact B373599
  · exact B373603
  · exact B373607
  · exact B373611
  · exact B373615
  · exact B373619
  · exact B373623
  · exact B373627
  · exact B373631
  · exact B373635
  · exact B373639
  · exact B373643
  · exact B373647
  · exact B373651
  · exact B373655
  · exact B373659
  · exact B373663
  · exact B373667
  · exact B373671
  · exact B373675
  · exact B373679
  · exact B373683
  · exact B373687
  · exact B373691
  · exact B373695
  · exact B373699
  · exact B373703
  · exact B373707
  · exact B373711
  · exact B373715
  · exact B373719
  · exact B373723
  · exact B373727
  · exact B373731
  · exact B373735
  · exact B373739
  · exact B373743
  · exact B373747
  · exact B373751
  · exact B373755
  · exact B373759
  · exact B373763
  · exact B373767
  · exact B373771
  · exact B373775
  · exact B373779
  · exact B373783
  · exact B373787
  · exact B373791
  · exact B373795
  · exact B373799
  · exact B373803
  · exact B373807
  · exact B373811
  · exact B373815
  · exact B373819
  · exact B373823
  · exact B373827
  · exact B373831
  · exact B373835
  · exact B373839
  · exact B373843
  · exact B373847
  · exact B373851
  · exact B373855
  · exact B373859
  · exact B373863
  · exact B373867
  · exact B373871
  · exact B373875
  · exact B373879
  · exact B373883
  · exact B373887
  · exact B373891
  · exact B373895
  · exact B373899
  · exact B373903
  · exact B373907
  · exact B373911
  · exact B373915
  · exact B373919
  · exact B373923
  · exact B373927
  · exact B373931
  · exact B373935
  · exact B373939
  · exact B373943
  · exact B373947
  · exact B373951
  · exact B373955
  · exact B373959
  · exact B373963
  · exact B373967
  · exact B373971
  · exact B373975
  · exact B373979
  · exact B373983
  · exact B373987
  · exact B373991
  · exact B373995
  · exact B373999
  · exact B374003
  · exact B374007
  · exact B374011
  · exact B374015
  · exact B374019
  · exact B374023
  · exact B374027
  · exact B374031
  · exact B374035
  · exact B374039
  · exact B374043
  · exact B374047
  · exact B374051
  · exact B374055
  · exact B374059
  · exact B374063
  · exact B374067
  · exact B374071
  · exact B374075
  · exact B374079
  · exact B374083
  · exact B374087
  · exact B374091
  · exact B374095
  · exact B374099
  · exact B374103
  · exact B374107
  · exact B374111
  · exact B374115
  · exact B374119
  · exact B374123
  · exact B374127
  · exact B374131
  · exact B374135
  · exact B374139
  · exact B374143
  · exact B374147
  · exact B374151
  · exact B374155
  · exact B374159
  · exact B374163
  · exact B374167
  · exact B374171
  · exact B374175
  · exact B374179
  · exact B374183
  · exact B374187
  · exact B374191
  · exact B374195
  · exact B374199
  · exact B374203
  · exact B374207
  · exact B374211
  · exact B374215
  · exact B374219
  · exact B374223
  · exact B374227
  · exact B374231
  · exact B374235
  · exact B374239
  · exact B374243
  · exact B374247
  · exact B374251
  · exact B374255
  · exact B374259
  · exact B374263
  · exact B374267
  · exact B374271
  · exact B374275
  · exact B374279
  · exact B374283
  · exact B374287
  · exact B374291
  · exact B374295
  · exact B374299
  · exact B374303
  · exact B374307
  · exact B374311
  · exact B374315
  · exact B374319
  · exact B374323
  · exact B374327
  · exact B374331
  · exact B374335
  · exact B374339
  · exact B374343
  · exact B374347
  · exact B374351
  · exact B374355
  · exact B374359
  · exact B374363
  · exact B374367
  · exact B374371
  · exact B374375
  · exact B374379
  · exact B374383
  · exact B374387
  · exact B374391
  · exact B374395
  · exact B374399
  · exact B374403
  · exact B374407
  · exact B374411
  · exact B374415
  · exact B374419
  · exact B374423
  · exact B374427
  · exact B374431
  · exact B374435
  · exact B374439
  · exact B374443
  · exact B374447
  · exact B374451
  · exact B374455
  · exact B374459
  · exact B374463
  · exact B374467
  · exact B374471
  · exact B374475
  · exact B374479
  · exact B374483
  · exact B374487
  · exact B374491
  · exact B374495
  · exact B374499
  · exact B374503
  · exact B374507
  · exact B374511
  · exact B374515
  · exact B374519
  · exact B374523
  · exact B374527
  · exact B374531
  · exact B374535
  · exact B374539
  · exact B374543
  · exact B374547
  · exact B374551
  · exact B374555
  · exact B374559
  · exact B374563
  · exact B374567
  · exact B374571
  · exact B374575
  · exact B374579
  · exact B374583
  · exact B374587
  · exact B374591
  · exact B374595
  · exact B374599
  · exact B374603
  · exact B374607
  · exact B374611
  · exact B374615
  · exact B374619
  · exact B374623
  · exact B374627
  · exact B374631
  · exact B374635
  · exact B374639
  · exact B374643
  · exact B374647
  · exact B374651
  · exact B374655
  · exact B374659
  · exact B374663
  · exact B374667
  · exact B374671
  · exact B374675
  · exact B374679
  · exact B374683
  · exact B374687
  · exact B374691
  · exact B374695
  · exact B374699
  · exact B374703
  · exact B374707
  · exact B374711
  · exact B374715
  · exact B374719
  · exact B374723
  · exact B374727
  · exact B374731
  · exact B374735
  · exact B374739
  · exact B374743
  · exact B374747
  · exact B374751
  · exact B374755
  · exact B374759

theorem solution (m : ℕ) (hlo : 370760 ≤ m) (hhi : m ≤ 374760) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 92690 ≤ j := by omega
    have hj2 : j ≤ 93689 := by omega
    have hb : Blo 370760 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 93390 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
