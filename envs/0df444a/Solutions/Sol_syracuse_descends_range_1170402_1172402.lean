-- Prove2me | solution 1 for syracuse_descends_range_1170402_1172402
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:20.879223+00:00
-- url     : https://prove2.me/submissions/691cc629-494f-4196-b0c4-6c227e3ae5ec

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


theorem B3956741 : Blo 1170402 3956741 := bbase (se 4 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 3956741 = 741889) (by norm_num)
theorem B2637845 : Blo 1170402 2637845 := bbase (se 6 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 2637845 = 123649) (by norm_num)
theorem B1482781 : Blo 1170402 1482781 := bbase (se 3 (by rfl) ⟨278021, by rfl⟩ : syracuseStep 1482781 = 556043) (by norm_num)
theorem B1318945 : Blo 1170402 1318945 := bbase (se 2 (by rfl) ⟨494604, by rfl⟩ : syracuseStep 1318945 = 989209) (by norm_num)
theorem B1187893 : Blo 1170402 1187893 := bbase (se 5 (by rfl) ⟨55682, by rfl⟩ : syracuseStep 1187893 = 111365) (by norm_num)
theorem B3752021 : Blo 1170402 3752021 := bbase (se 8 (by rfl) ⟨21984, by rfl⟩ : syracuseStep 3752021 = 43969) (by norm_num)
theorem B1482877 : Blo 1170402 1482877 := bbase (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) (by norm_num)
theorem B2965693 : Blo 1170402 2965693 := bbase (se 3 (by rfl) ⟨556067, by rfl⟩ : syracuseStep 2965693 = 1112135) (by norm_num)
theorem B1409233 : Blo 1170402 1409233 := bbase (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) (by norm_num)
theorem B1318909 : Blo 1170402 1318909 := bbase (se 3 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 1318909 = 494591) (by norm_num)
theorem B1483049 : Blo 1170402 1483049 := bbase (se 2 (by rfl) ⟨556143, by rfl⟩ : syracuseStep 1483049 = 1112287) (by norm_num)
theorem B2965805 : Blo 1170402 2965805 := bbase (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) (by norm_num)
theorem B1483105 : Blo 1170402 1483105 := bbase (se 2 (by rfl) ⟨556164, by rfl⟩ : syracuseStep 1483105 = 1112329) (by norm_num)
theorem B1483201 : Blo 1170402 1483201 := bbase (se 2 (by rfl) ⟨556200, by rfl⟩ : syracuseStep 1483201 = 1112401) (by norm_num)
theorem B1876421 : Blo 1170402 1876421 := bbase (se 4 (by rfl) ⟨175914, by rfl⟩ : syracuseStep 1876421 = 351829) (by norm_num)
theorem B2965997 : Blo 1170402 2965997 := bbase (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) (by norm_num)
theorem B2892277 : Blo 1170402 2892277 := bbase (se 5 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 2892277 = 271151) (by norm_num)
theorem B2253349 : Blo 1170402 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B3334709 : Blo 1170402 3334709 := bbase (se 5 (by rfl) ⟨156314, by rfl⟩ : syracuseStep 3334709 = 312629) (by norm_num)
theorem B1876549 : Blo 1170402 1876549 := bbase (se 4 (by rfl) ⟨175926, by rfl⟩ : syracuseStep 1876549 = 351853) (by norm_num)
theorem B8438357 : Blo 1170402 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B1483373 : Blo 1170402 1483373 := bbase (se 3 (by rfl) ⟨278132, by rfl⟩ : syracuseStep 1483373 = 556265) (by norm_num)
theorem B1876613 : Blo 1170402 1876613 := bbase (se 4 (by rfl) ⟨175932, by rfl⟩ : syracuseStep 1876613 = 351865) (by norm_num)
theorem B1483429 : Blo 1170402 1483429 := bbase (se 4 (by rfl) ⟨139071, by rfl⟩ : syracuseStep 1483429 = 278143) (by norm_num)
theorem B4448965 : Blo 1170402 4448965 := bbase (se 4 (by rfl) ⟨417090, by rfl⟩ : syracuseStep 4448965 = 834181) (by norm_num)
theorem B2286341 : Blo 1170402 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1483525 : Blo 1170402 1483525 := bbase (se 4 (by rfl) ⟨139080, by rfl⟩ : syracuseStep 1483525 = 278161) (by norm_num)
theorem B2966341 : Blo 1170402 2966341 := bbase (se 4 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 2966341 = 556189) (by norm_num)
theorem B1975117 : Blo 1170402 1975117 := bbase (se 3 (by rfl) ⟨370334, by rfl⟩ : syracuseStep 1975117 = 740669) (by norm_num)
theorem B3801941 : Blo 1170402 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B1975205 : Blo 1170402 1975205 := bbase (se 4 (by rfl) ⟨185175, by rfl⟩ : syracuseStep 1975205 = 370351) (by norm_num)
theorem B4219813 : Blo 1170402 4219813 := bbase (se 4 (by rfl) ⟨395607, by rfl⟩ : syracuseStep 4219813 = 791215) (by norm_num)
theorem B1483697 : Blo 1170402 1483697 := bbase (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) (by norm_num)
theorem B2966453 : Blo 1170402 2966453 := bbase (se 5 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 2966453 = 278105) (by norm_num)
theorem B2253781 : Blo 1170402 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B1483753 : Blo 1170402 1483753 := bbase (se 2 (by rfl) ⟨556407, by rfl⟩ : syracuseStep 1483753 = 1112815) (by norm_num)
theorem B4449269 : Blo 1170402 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B1975333 : Blo 1170402 1975333 := bbase (se 4 (by rfl) ⟨185187, by rfl⟩ : syracuseStep 1975333 = 370375) (by norm_num)
theorem B6759509 : Blo 1170402 6759509 := bbase (se 8 (by rfl) ⟨39606, by rfl⟩ : syracuseStep 6759509 = 79213) (by norm_num)
theorem B2966645 : Blo 1170402 2966645 := bbase (se 5 (by rfl) ⟨139061, by rfl⟩ : syracuseStep 2966645 = 278123) (by norm_num)
theorem B1975421 : Blo 1170402 1975421 := bbase (se 3 (by rfl) ⟨370391, by rfl⟩ : syracuseStep 1975421 = 740783) (by norm_num)
theorem B3753125 : Blo 1170402 3753125 := bbase (se 4 (by rfl) ⟨351855, by rfl⟩ : syracuseStep 3753125 = 703711) (by norm_num)
theorem B3335381 : Blo 1170402 3335381 := bbase (se 7 (by rfl) ⟨39086, by rfl⟩ : syracuseStep 3335381 = 78173) (by norm_num)
theorem B5932277 : Blo 1170402 5932277 := bbase (se 5 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 5932277 = 556151) (by norm_num)
theorem B1975549 : Blo 1170402 1975549 := bbase (se 3 (by rfl) ⟨370415, by rfl⟩ : syracuseStep 1975549 = 740831) (by norm_num)
theorem B2671949 : Blo 1170402 2671949 := bbase (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) (by norm_num)
theorem B1975637 : Blo 1170402 1975637 := bbase (se 12 (by rfl) ⟨723, by rfl⟩ : syracuseStep 1975637 = 1447) (by norm_num)
theorem B4752773 : Blo 1170402 4752773 := bbase (se 4 (by rfl) ⟨445572, by rfl⟩ : syracuseStep 4752773 = 891145) (by norm_num)
theorem B1582517 : Blo 1170402 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B2966989 : Blo 1170402 2966989 := bbase (se 3 (by rfl) ⟨556310, by rfl⟩ : syracuseStep 2966989 = 1112621) (by norm_num)
theorem B1975765 : Blo 1170402 1975765 := bbase (se 7 (by rfl) ⟨23153, by rfl⟩ : syracuseStep 1975765 = 46307) (by norm_num)
theorem B27059669 : Blo 1170402 27059669 := bbase (se 7 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 27059669 = 634211) (by norm_num)
theorem B1975853 : Blo 1170402 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B5629493 : Blo 1170402 5629493 := bbase (se 5 (by rfl) ⟨263882, by rfl⟩ : syracuseStep 5629493 = 527765) (by norm_num)
theorem B2967101 : Blo 1170402 2967101 := bbase (se 3 (by rfl) ⟨556331, by rfl⟩ : syracuseStep 2967101 = 1112663) (by norm_num)
theorem B5006933 : Blo 1170402 5006933 := bbase (se 8 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 5006933 = 58675) (by norm_num)
theorem B3335813 : Blo 1170402 3335813 := bbase (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) (by norm_num)
theorem B2500237 : Blo 1170402 2500237 := bbase (se 3 (by rfl) ⟨468794, by rfl⟩ : syracuseStep 2500237 = 937589) (by norm_num)
theorem B1975981 : Blo 1170402 1975981 := bbase (se 3 (by rfl) ⟨370496, by rfl⟩ : syracuseStep 1975981 = 740993) (by norm_num)
theorem B3950261 : Blo 1170402 3950261 := bbase (se 5 (by rfl) ⟨185168, by rfl⟩ : syracuseStep 3950261 = 370337) (by norm_num)
theorem B2967293 : Blo 1170402 2967293 := bbase (se 3 (by rfl) ⟨556367, by rfl⟩ : syracuseStep 2967293 = 1112735) (by norm_num)
theorem B1976069 : Blo 1170402 1976069 := bbase (se 4 (by rfl) ⟨185256, by rfl⟩ : syracuseStep 1976069 = 370513) (by norm_num)
theorem B1976197 : Blo 1170402 1976197 := bbase (se 4 (by rfl) ⟨185268, by rfl⟩ : syracuseStep 1976197 = 370537) (by norm_num)
theorem B1689509 : Blo 1170402 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B1877933 : Blo 1170402 1877933 := bbase (se 3 (by rfl) ⟨352112, by rfl⟩ : syracuseStep 1877933 = 704225) (by norm_num)
theorem B1976285 : Blo 1170402 1976285 := bbase (se 3 (by rfl) ⟨370553, by rfl⟩ : syracuseStep 1976285 = 741107) (by norm_num)
theorem B2967637 : Blo 1170402 2967637 := bbase (se 8 (by rfl) ⟨17388, by rfl⟩ : syracuseStep 2967637 = 34777) (by norm_num)
theorem B1976413 : Blo 1170402 1976413 := bbase (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) (by norm_num)
theorem B3950693 : Blo 1170402 3950693 := bbase (se 4 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 3950693 = 740755) (by norm_num)
theorem B2500733 : Blo 1170402 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B1976501 : Blo 1170402 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B1583317 : Blo 1170402 1583317 := bbase (se 7 (by rfl) ⟨18554, by rfl⟩ : syracuseStep 1583317 = 37109) (by norm_num)
theorem B1976629 : Blo 1170402 1976629 := bbase (se 5 (by rfl) ⟨92654, by rfl⟩ : syracuseStep 1976629 = 185309) (by norm_num)
theorem B2812277 : Blo 1170402 2812277 := bbase (se 5 (by rfl) ⟨131825, by rfl⟩ : syracuseStep 2812277 = 263651) (by norm_num)
theorem B3336565 : Blo 1170402 3336565 := bbase (se 5 (by rfl) ⟨156401, by rfl⟩ : syracuseStep 3336565 = 312803) (by norm_num)
theorem B1976717 : Blo 1170402 1976717 := bbase (se 3 (by rfl) ⟨370634, by rfl⟩ : syracuseStep 1976717 = 741269) (by norm_num)
theorem B1755605 : Blo 1170402 1755605 := bbase (se 7 (by rfl) ⟨20573, by rfl⟩ : syracuseStep 1755605 = 41147) (by norm_num)
theorem B1755629 : Blo 1170402 1755629 := bbase (se 3 (by rfl) ⟨329180, by rfl⟩ : syracuseStep 1755629 = 658361) (by norm_num)
theorem B1755653 : Blo 1170402 1755653 := bbase (se 4 (by rfl) ⟨164592, by rfl⟩ : syracuseStep 1755653 = 329185) (by norm_num)
theorem B5933573 : Blo 1170402 5933573 := bbase (se 4 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 5933573 = 1112545) (by norm_num)
theorem B1976845 : Blo 1170402 1976845 := bbase (se 3 (by rfl) ⟨370658, by rfl⟩ : syracuseStep 1976845 = 741317) (by norm_num)
theorem B3951125 : Blo 1170402 3951125 := bbase (se 6 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 3951125 = 185209) (by norm_num)
theorem B1755677 : Blo 1170402 1755677 := bbase (se 3 (by rfl) ⟨329189, by rfl⟩ : syracuseStep 1755677 = 658379) (by norm_num)
theorem B2673197 : Blo 1170402 2673197 := bbase (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) (by norm_num)
theorem B1755701 : Blo 1170402 1755701 := bbase (se 5 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 1755701 = 164597) (by norm_num)
theorem B2222653 : Blo 1170402 2222653 := bbase (se 3 (by rfl) ⟨416747, by rfl⟩ : syracuseStep 2222653 = 833495) (by norm_num)
theorem B1755725 : Blo 1170402 1755725 := bbase (se 3 (by rfl) ⟨329198, by rfl⟩ : syracuseStep 1755725 = 658397) (by norm_num)
theorem B1755749 : Blo 1170402 1755749 := bbase (se 4 (by rfl) ⟨164601, by rfl⟩ : syracuseStep 1755749 = 329203) (by norm_num)
theorem B1976933 : Blo 1170402 1976933 := bbase (se 4 (by rfl) ⟨185337, by rfl⟩ : syracuseStep 1976933 = 370675) (by norm_num)
theorem B1755773 : Blo 1170402 1755773 := bbase (se 3 (by rfl) ⟨329207, by rfl⟩ : syracuseStep 1755773 = 658415) (by norm_num)
theorem B1755797 : Blo 1170402 1755797 := bbase (se 6 (by rfl) ⟨41151, by rfl⟩ : syracuseStep 1755797 = 82303) (by norm_num)
theorem B1755821 : Blo 1170402 1755821 := bbase (se 3 (by rfl) ⟨329216, by rfl⟩ : syracuseStep 1755821 = 658433) (by norm_num)
theorem B4999877 : Blo 1170402 4999877 := bbase (se 4 (by rfl) ⟨468738, by rfl⟩ : syracuseStep 4999877 = 937477) (by norm_num)
theorem B1755845 : Blo 1170402 1755845 := bbase (se 4 (by rfl) ⟨164610, by rfl⟩ : syracuseStep 1755845 = 329221) (by norm_num)
theorem B2222797 : Blo 1170402 2222797 := bbase (se 3 (by rfl) ⟨416774, by rfl⟩ : syracuseStep 2222797 = 833549) (by norm_num)
theorem B1780429 : Blo 1170402 1780429 := bbase (se 3 (by rfl) ⟨333830, by rfl⟩ : syracuseStep 1780429 = 667661) (by norm_num)
theorem B1755869 : Blo 1170402 1755869 := bbase (se 3 (by rfl) ⟨329225, by rfl⟩ : syracuseStep 1755869 = 658451) (by norm_num)
theorem B1977061 : Blo 1170402 1977061 := bbase (se 4 (by rfl) ⟨185349, by rfl⟩ : syracuseStep 1977061 = 370699) (by norm_num)
theorem B1755893 : Blo 1170402 1755893 := bbase (se 5 (by rfl) ⟨82307, by rfl⟩ : syracuseStep 1755893 = 164615) (by norm_num)
theorem B1755917 : Blo 1170402 1755917 := bbase (se 3 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 1755917 = 658469) (by norm_num)
theorem B1755941 : Blo 1170402 1755941 := bbase (se 4 (by rfl) ⟨164619, by rfl⟩ : syracuseStep 1755941 = 329239) (by norm_num)
theorem B1755965 : Blo 1170402 1755965 := bbase (se 3 (by rfl) ⟨329243, by rfl⟩ : syracuseStep 1755965 = 658487) (by norm_num)
theorem B1977149 : Blo 1170402 1977149 := bbase (se 3 (by rfl) ⟨370715, by rfl⟩ : syracuseStep 1977149 = 741431) (by norm_num)
theorem B1755989 : Blo 1170402 1755989 := bbase (se 9 (by rfl) ⟨5144, by rfl⟩ : syracuseStep 1755989 = 10289) (by norm_num)
theorem B1756013 : Blo 1170402 1756013 := bbase (se 3 (by rfl) ⟨329252, by rfl⟩ : syracuseStep 1756013 = 658505) (by norm_num)
theorem B2222957 : Blo 1170402 2222957 := bbase (se 3 (by rfl) ⟨416804, by rfl⟩ : syracuseStep 2222957 = 833609) (by norm_num)
theorem B1756037 : Blo 1170402 1756037 := bbase (se 4 (by rfl) ⟨164628, by rfl⟩ : syracuseStep 1756037 = 329257) (by norm_num)
theorem B3165077 : Blo 1170402 3165077 := bbase (se 6 (by rfl) ⟨74181, by rfl⟩ : syracuseStep 3165077 = 148363) (by norm_num)
theorem B1756061 : Blo 1170402 1756061 := bbase (se 3 (by rfl) ⟨329261, by rfl⟩ : syracuseStep 1756061 = 658523) (by norm_num)
theorem B5925797 : Blo 1170402 5925797 := bbase (se 4 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 5925797 = 1111087) (by norm_num)
theorem B1756085 : Blo 1170402 1756085 := bbase (se 5 (by rfl) ⟨82316, by rfl⟩ : syracuseStep 1756085 = 164633) (by norm_num)
theorem B1977277 : Blo 1170402 1977277 := bbase (se 3 (by rfl) ⟨370739, by rfl⟩ : syracuseStep 1977277 = 741479) (by norm_num)
theorem B3951557 : Blo 1170402 3951557 := bbase (se 4 (by rfl) ⟨370458, by rfl⟩ : syracuseStep 3951557 = 740917) (by norm_num)
theorem B5630917 : Blo 1170402 5630917 := bbase (se 4 (by rfl) ⟨527898, by rfl⟩ : syracuseStep 5630917 = 1055797) (by norm_num)
theorem B1756109 : Blo 1170402 1756109 := bbase (se 3 (by rfl) ⟨329270, by rfl⟩ : syracuseStep 1756109 = 658541) (by norm_num)
theorem B1756133 : Blo 1170402 1756133 := bbase (se 4 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 1756133 = 329275) (by norm_num)
theorem B2501621 : Blo 1170402 2501621 := bbase (se 5 (by rfl) ⟨117263, by rfl⟩ : syracuseStep 2501621 = 234527) (by norm_num)
theorem B1756157 : Blo 1170402 1756157 := bbase (se 3 (by rfl) ⟨329279, by rfl⟩ : syracuseStep 1756157 = 658559) (by norm_num)
theorem B2223101 : Blo 1170402 2223101 := bbase (se 3 (by rfl) ⟨416831, by rfl⟩ : syracuseStep 2223101 = 833663) (by norm_num)
theorem B1756181 : Blo 1170402 1756181 := bbase (se 6 (by rfl) ⟨41160, by rfl⟩ : syracuseStep 1756181 = 82321) (by norm_num)
theorem B1977365 : Blo 1170402 1977365 := bbase (se 6 (by rfl) ⟨46344, by rfl⟩ : syracuseStep 1977365 = 92689) (by norm_num)
theorem B3755045 : Blo 1170402 3755045 := bbase (se 4 (by rfl) ⟨352035, by rfl⟩ : syracuseStep 3755045 = 704071) (by norm_num)
theorem B1756205 : Blo 1170402 1756205 := bbase (se 3 (by rfl) ⟨329288, by rfl⟩ : syracuseStep 1756205 = 658577) (by norm_num)
theorem B4451381 : Blo 1170402 4451381 := bbase (se 5 (by rfl) ⟨208658, by rfl⟩ : syracuseStep 4451381 = 417317) (by norm_num)
theorem B1756229 : Blo 1170402 1756229 := bbase (se 4 (by rfl) ⟨164646, by rfl⟩ : syracuseStep 1756229 = 329293) (by norm_num)
theorem B1756253 : Blo 1170402 1756253 := bbase (se 3 (by rfl) ⟨329297, by rfl⟩ : syracuseStep 1756253 = 658595) (by norm_num)
theorem B2501741 : Blo 1170402 2501741 := bbase (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) (by norm_num)
theorem B1756277 : Blo 1170402 1756277 := bbase (se 5 (by rfl) ⟨82325, by rfl⟩ : syracuseStep 1756277 = 164651) (by norm_num)
theorem B2256005 : Blo 1170402 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B1756301 : Blo 1170402 1756301 := bbase (se 3 (by rfl) ⟨329306, by rfl⟩ : syracuseStep 1756301 = 658613) (by norm_num)
theorem B13347989 : Blo 1170402 13347989 := bbase (se 6 (by rfl) ⟨312843, by rfl⟩ : syracuseStep 13347989 = 625687) (by norm_num)
theorem B1977493 : Blo 1170402 1977493 := bbase (se 6 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 1977493 = 92695) (by norm_num)
theorem B1756325 : Blo 1170402 1756325 := bbase (se 4 (by rfl) ⟨164655, by rfl⟩ : syracuseStep 1756325 = 329311) (by norm_num)
theorem B1756349 : Blo 1170402 1756349 := bbase (se 3 (by rfl) ⟨329315, by rfl⟩ : syracuseStep 1756349 = 658631) (by norm_num)
theorem B1756373 : Blo 1170402 1756373 := bbase (se 7 (by rfl) ⟨20582, by rfl⟩ : syracuseStep 1756373 = 41165) (by norm_num)
theorem B1756397 : Blo 1170402 1756397 := bbase (se 3 (by rfl) ⟨329324, by rfl⟩ : syracuseStep 1756397 = 658649) (by norm_num)
theorem B1977581 : Blo 1170402 1977581 := bbase (se 3 (by rfl) ⟨370796, by rfl⟩ : syracuseStep 1977581 = 741593) (by norm_num)
theorem B1756421 : Blo 1170402 1756421 := bbase (se 4 (by rfl) ⟨164664, by rfl⟩ : syracuseStep 1756421 = 329329) (by norm_num)
theorem B2223389 : Blo 1170402 2223389 := bbase (se 3 (by rfl) ⟨416885, by rfl⟩ : syracuseStep 2223389 = 833771) (by norm_num)
theorem B1756445 : Blo 1170402 1756445 := bbase (se 3 (by rfl) ⟨329333, by rfl⟩ : syracuseStep 1756445 = 658667) (by norm_num)
theorem B1756469 : Blo 1170402 1756469 := bbase (se 5 (by rfl) ⟨82334, by rfl⟩ : syracuseStep 1756469 = 164669) (by norm_num)
theorem B1756493 : Blo 1170402 1756493 := bbase (se 3 (by rfl) ⟨329342, by rfl⟩ : syracuseStep 1756493 = 658685) (by norm_num)
theorem B1756517 : Blo 1170402 1756517 := bbase (se 4 (by rfl) ⟨164673, by rfl⟩ : syracuseStep 1756517 = 329347) (by norm_num)
theorem B1977709 : Blo 1170402 1977709 := bbase (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) (by norm_num)
theorem B3951989 : Blo 1170402 3951989 := bbase (se 5 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 3951989 = 370499) (by norm_num)
theorem B1756541 : Blo 1170402 1756541 := bbase (se 3 (by rfl) ⟨329351, by rfl⟩ : syracuseStep 1756541 = 658703) (by norm_num)
theorem B1756565 : Blo 1170402 1756565 := bbase (se 6 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 1756565 = 82339) (by norm_num)
theorem B8449429 : Blo 1170402 8449429 := bbase (se 6 (by rfl) ⟨198033, by rfl⟩ : syracuseStep 8449429 = 396067) (by norm_num)
theorem B1756589 : Blo 1170402 1756589 := bbase (se 3 (by rfl) ⟨329360, by rfl⟩ : syracuseStep 1756589 = 658721) (by norm_num)
theorem B2223541 : Blo 1170402 2223541 := bbase (se 5 (by rfl) ⟨104228, by rfl⟩ : syracuseStep 2223541 = 208457) (by norm_num)
theorem B1756613 : Blo 1170402 1756613 := bbase (se 4 (by rfl) ⟨164682, by rfl⟩ : syracuseStep 1756613 = 329365) (by norm_num)
theorem B1977797 : Blo 1170402 1977797 := bbase (se 4 (by rfl) ⟨185418, by rfl⟩ : syracuseStep 1977797 = 370837) (by norm_num)
theorem B1756637 : Blo 1170402 1756637 := bbase (se 3 (by rfl) ⟨329369, by rfl⟩ : syracuseStep 1756637 = 658739) (by norm_num)
theorem B1756661 : Blo 1170402 1756661 := bbase (se 5 (by rfl) ⟨82343, by rfl⟩ : syracuseStep 1756661 = 164687) (by norm_num)
theorem B4509173 : Blo 1170402 4509173 := bbase (se 5 (by rfl) ⟨211367, by rfl⟩ : syracuseStep 4509173 = 422735) (by norm_num)
theorem B1756685 : Blo 1170402 1756685 := bbase (se 3 (by rfl) ⟨329378, by rfl⟩ : syracuseStep 1756685 = 658757) (by norm_num)
theorem B8900117 : Blo 1170402 8900117 := bbase (se 6 (by rfl) ⟨208596, by rfl⟩ : syracuseStep 8900117 = 417193) (by norm_num)
theorem B1666597 : Blo 1170402 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B1756709 : Blo 1170402 1756709 := bbase (se 4 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 1756709 = 329383) (by norm_num)
theorem B1756733 : Blo 1170402 1756733 := bbase (se 3 (by rfl) ⟨329387, by rfl⟩ : syracuseStep 1756733 = 658775) (by norm_num)
theorem B1977925 : Blo 1170402 1977925 := bbase (se 4 (by rfl) ⟨185430, by rfl⟩ : syracuseStep 1977925 = 370861) (by norm_num)
theorem B1756757 : Blo 1170402 1756757 := bbase (se 8 (by rfl) ⟨10293, by rfl⟩ : syracuseStep 1756757 = 20587) (by norm_num)
theorem B1756781 : Blo 1170402 1756781 := bbase (se 3 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 1756781 = 658793) (by norm_num)
theorem B1756805 : Blo 1170402 1756805 := bbase (se 4 (by rfl) ⟨164700, by rfl⟩ : syracuseStep 1756805 = 329401) (by norm_num)
theorem B2002573 : Blo 1170402 2002573 := bbase (se 3 (by rfl) ⟨375482, by rfl⟩ : syracuseStep 2002573 = 750965) (by norm_num)
theorem B18992789 : Blo 1170402 18992789 := bbase (se 6 (by rfl) ⟨445143, by rfl⟩ : syracuseStep 18992789 = 890287) (by norm_num)
theorem B1756829 : Blo 1170402 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B1978013 : Blo 1170402 1978013 := bbase (se 3 (by rfl) ⟨370877, by rfl⟩ : syracuseStep 1978013 = 741755) (by norm_num)
theorem B5000885 : Blo 1170402 5000885 := bbase (se 5 (by rfl) ⟨234416, by rfl⟩ : syracuseStep 5000885 = 468833) (by norm_num)
theorem B1756853 : Blo 1170402 1756853 := bbase (se 5 (by rfl) ⟨82352, by rfl⟩ : syracuseStep 1756853 = 164705) (by norm_num)
theorem B1756877 : Blo 1170402 1756877 := bbase (se 3 (by rfl) ⟨329414, by rfl⟩ : syracuseStep 1756877 = 658829) (by norm_num)
theorem B1756901 : Blo 1170402 1756901 := bbase (se 4 (by rfl) ⟨164709, by rfl⟩ : syracuseStep 1756901 = 329419) (by norm_num)
theorem B2223845 : Blo 1170402 2223845 := bbase (se 4 (by rfl) ⟨208485, by rfl⟩ : syracuseStep 2223845 = 416971) (by norm_num)
theorem B2502373 : Blo 1170402 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B2633453 : Blo 1170402 2633453 := bbase (se 3 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 2633453 = 987545) (by norm_num)
theorem B4443893 : Blo 1170402 4443893 := bbase (se 5 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 4443893 = 416615) (by norm_num)
theorem B1666813 : Blo 1170402 1666813 := bbase (se 3 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 1666813 = 625055) (by norm_num)
theorem B1756925 : Blo 1170402 1756925 := bbase (se 3 (by rfl) ⟨329423, by rfl⟩ : syracuseStep 1756925 = 658847) (by norm_num)
theorem B1756949 : Blo 1170402 1756949 := bbase (se 6 (by rfl) ⟨41178, by rfl⟩ : syracuseStep 1756949 = 82357) (by norm_num)
theorem B5934869 : Blo 1170402 5934869 := bbase (se 6 (by rfl) ⟨139098, by rfl⟩ : syracuseStep 5934869 = 278197) (by norm_num)
theorem B1978141 : Blo 1170402 1978141 := bbase (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) (by norm_num)
theorem B3952421 : Blo 1170402 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B1756973 : Blo 1170402 1756973 := bbase (se 3 (by rfl) ⟨329432, by rfl⟩ : syracuseStep 1756973 = 658865) (by norm_num)
theorem B2633525 : Blo 1170402 2633525 := bbase (se 5 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 2633525 = 246893) (by norm_num)
theorem B1756997 : Blo 1170402 1756997 := bbase (se 4 (by rfl) ⟨164718, by rfl⟩ : syracuseStep 1756997 = 329437) (by norm_num)
theorem B1757021 : Blo 1170402 1757021 := bbase (se 3 (by rfl) ⟨329441, by rfl⟩ : syracuseStep 1757021 = 658883) (by norm_num)
theorem B1757045 : Blo 1170402 1757045 := bbase (se 5 (by rfl) ⟨82361, by rfl⟩ : syracuseStep 1757045 = 164723) (by norm_num)
theorem B1978229 : Blo 1170402 1978229 := bbase (se 5 (by rfl) ⟨92729, by rfl⟩ : syracuseStep 1978229 = 185459) (by norm_num)
theorem B2633597 : Blo 1170402 2633597 := bbase (se 3 (by rfl) ⟨493799, by rfl⟩ : syracuseStep 2633597 = 987599) (by norm_num)
theorem B1757069 : Blo 1170402 1757069 := bbase (se 3 (by rfl) ⟨329450, by rfl⟩ : syracuseStep 1757069 = 658901) (by norm_num)
theorem B1757093 : Blo 1170402 1757093 := bbase (se 4 (by rfl) ⟨164727, by rfl⟩ : syracuseStep 1757093 = 329455) (by norm_num)
theorem B8892341 : Blo 1170402 8892341 := bbase (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) (by norm_num)
theorem B1757117 : Blo 1170402 1757117 := bbase (se 3 (by rfl) ⟨329459, by rfl⟩ : syracuseStep 1757117 = 658919) (by norm_num)
theorem B2633669 : Blo 1170402 2633669 := bbase (se 4 (by rfl) ⟨246906, by rfl⟩ : syracuseStep 2633669 = 493813) (by norm_num)
theorem B1757141 : Blo 1170402 1757141 := bbase (se 7 (by rfl) ⟨20591, by rfl⟩ : syracuseStep 1757141 = 41183) (by norm_num)
theorem B1757165 : Blo 1170402 1757165 := bbase (se 3 (by rfl) ⟨329468, by rfl⟩ : syracuseStep 1757165 = 658937) (by norm_num)
theorem B1978357 : Blo 1170402 1978357 := bbase (se 5 (by rfl) ⟨92735, by rfl⟩ : syracuseStep 1978357 = 185471) (by norm_num)
theorem B2109445 : Blo 1170402 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B1757189 : Blo 1170402 1757189 := bbase (se 4 (by rfl) ⟨164736, by rfl⟩ : syracuseStep 1757189 = 329473) (by norm_num)
theorem B2633741 : Blo 1170402 2633741 := bbase (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) (by norm_num)
theorem B1757213 : Blo 1170402 1757213 := bbase (se 3 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 1757213 = 658955) (by norm_num)
theorem B1757237 : Blo 1170402 1757237 := bbase (se 5 (by rfl) ⟨82370, by rfl⟩ : syracuseStep 1757237 = 164741) (by norm_num)
theorem B4223029 : Blo 1170402 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B1757261 : Blo 1170402 1757261 := bbase (se 3 (by rfl) ⟨329486, by rfl⟩ : syracuseStep 1757261 = 658973) (by norm_num)
theorem B2633813 : Blo 1170402 2633813 := bbase (se 8 (by rfl) ⟨15432, by rfl⟩ : syracuseStep 2633813 = 30865) (by norm_num)
theorem B2535509 : Blo 1170402 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B1757285 : Blo 1170402 1757285 := bbase (se 4 (by rfl) ⟨164745, by rfl⟩ : syracuseStep 1757285 = 329491) (by norm_num)
theorem B1667189 : Blo 1170402 1667189 := bbase (se 5 (by rfl) ⟨78149, by rfl⟩ : syracuseStep 1667189 = 156299) (by norm_num)
theorem B1757309 : Blo 1170402 1757309 := bbase (se 3 (by rfl) ⟨329495, by rfl⟩ : syracuseStep 1757309 = 658991) (by norm_num)
theorem B1757333 : Blo 1170402 1757333 := bbase (se 6 (by rfl) ⟨41187, by rfl⟩ : syracuseStep 1757333 = 82375) (by norm_num)
theorem B2633885 : Blo 1170402 2633885 := bbase (se 3 (by rfl) ⟨493853, by rfl⟩ : syracuseStep 2633885 = 987707) (by norm_num)
theorem B1757357 : Blo 1170402 1757357 := bbase (se 3 (by rfl) ⟨329504, by rfl⟩ : syracuseStep 1757357 = 659009) (by norm_num)
theorem B5927093 : Blo 1170402 5927093 := bbase (se 5 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 5927093 = 555665) (by norm_num)
theorem B1757381 : Blo 1170402 1757381 := bbase (se 4 (by rfl) ⟨164754, by rfl⟩ : syracuseStep 1757381 = 329509) (by norm_num)
theorem B3952853 : Blo 1170402 3952853 := bbase (se 7 (by rfl) ⟨46322, by rfl⟩ : syracuseStep 3952853 = 92645) (by norm_num)
theorem B1757405 : Blo 1170402 1757405 := bbase (se 3 (by rfl) ⟨329513, by rfl⟩ : syracuseStep 1757405 = 659027) (by norm_num)
theorem B2633957 : Blo 1170402 2633957 := bbase (se 4 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 2633957 = 493867) (by norm_num)
theorem B1503469 : Blo 1170402 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1757429 : Blo 1170402 1757429 := bbase (se 5 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 1757429 = 164759) (by norm_num)
theorem B1757453 : Blo 1170402 1757453 := bbase (se 3 (by rfl) ⟨329522, by rfl⟩ : syracuseStep 1757453 = 659045) (by norm_num)
theorem B2855197 : Blo 1170402 2855197 := bbase (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) (by norm_num)
theorem B1757477 : Blo 1170402 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B2634029 : Blo 1170402 2634029 := bbase (se 3 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 2634029 = 987761) (by norm_num)
theorem B1757501 : Blo 1170402 1757501 := bbase (se 3 (by rfl) ⟨329531, by rfl⟩ : syracuseStep 1757501 = 659063) (by norm_num)
theorem B2814277 : Blo 1170402 2814277 := bbase (se 4 (by rfl) ⟨263838, by rfl⟩ : syracuseStep 2814277 = 527677) (by norm_num)
theorem B1757525 : Blo 1170402 1757525 := bbase (se 10 (by rfl) ⟨2574, by rfl⟩ : syracuseStep 1757525 = 5149) (by norm_num)
theorem B1757549 : Blo 1170402 1757549 := bbase (se 3 (by rfl) ⟨329540, by rfl⟩ : syracuseStep 1757549 = 659081) (by norm_num)
theorem B2634101 : Blo 1170402 2634101 := bbase (se 5 (by rfl) ⟨123473, by rfl⟩ : syracuseStep 2634101 = 246947) (by norm_num)
theorem B1757573 : Blo 1170402 1757573 := bbase (se 4 (by rfl) ⟨164772, by rfl⟩ : syracuseStep 1757573 = 329545) (by norm_num)
theorem B19001749 : Blo 1170402 19001749 := bbase (se 6 (by rfl) ⟨445353, by rfl⟩ : syracuseStep 19001749 = 890707) (by norm_num)
theorem B1757597 : Blo 1170402 1757597 := bbase (se 3 (by rfl) ⟨329549, by rfl⟩ : syracuseStep 1757597 = 659099) (by norm_num)
theorem B1757621 : Blo 1170402 1757621 := bbase (se 5 (by rfl) ⟨82388, by rfl⟩ : syracuseStep 1757621 = 164777) (by norm_num)
theorem B2634173 : Blo 1170402 2634173 := bbase (se 3 (by rfl) ⟨493907, by rfl⟩ : syracuseStep 2634173 = 987815) (by norm_num)
theorem B2109901 : Blo 1170402 2109901 := bbase (se 3 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 2109901 = 791213) (by norm_num)
theorem B1757645 : Blo 1170402 1757645 := bbase (se 3 (by rfl) ⟨329558, by rfl⟩ : syracuseStep 1757645 = 659117) (by norm_num)
theorem B2224597 : Blo 1170402 2224597 := bbase (se 7 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 2224597 = 52139) (by norm_num)
theorem B1782229 : Blo 1170402 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B1757669 : Blo 1170402 1757669 := bbase (se 4 (by rfl) ⟨164781, by rfl⟩ : syracuseStep 1757669 = 329563) (by norm_num)
theorem B2535925 : Blo 1170402 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B1757693 : Blo 1170402 1757693 := bbase (se 3 (by rfl) ⟨329567, by rfl⟩ : syracuseStep 1757693 = 659135) (by norm_num)
theorem B2634245 : Blo 1170402 2634245 := bbase (se 4 (by rfl) ⟨246960, by rfl⟩ : syracuseStep 2634245 = 493921) (by norm_num)
theorem B1757717 : Blo 1170402 1757717 := bbase (se 6 (by rfl) ⟨41196, by rfl⟩ : syracuseStep 1757717 = 82393) (by norm_num)
theorem B1757741 : Blo 1170402 1757741 := bbase (se 3 (by rfl) ⟨329576, by rfl⟩ : syracuseStep 1757741 = 659153) (by norm_num)
theorem B1757765 : Blo 1170402 1757765 := bbase (se 4 (by rfl) ⟨164790, by rfl⟩ : syracuseStep 1757765 = 329581) (by norm_num)
theorem B2634317 : Blo 1170402 2634317 := bbase (se 3 (by rfl) ⟨493934, by rfl⟩ : syracuseStep 2634317 = 987869) (by norm_num)
theorem B1757789 : Blo 1170402 1757789 := bbase (se 3 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 1757789 = 659171) (by norm_num)
theorem B2503261 : Blo 1170402 2503261 := bbase (se 3 (by rfl) ⟨469361, by rfl⟩ : syracuseStep 2503261 = 938723) (by norm_num)
theorem B2224741 : Blo 1170402 2224741 := bbase (se 4 (by rfl) ⟨208569, by rfl⟩ : syracuseStep 2224741 = 417139) (by norm_num)
theorem B1757813 : Blo 1170402 1757813 := bbase (se 5 (by rfl) ⟨82397, by rfl⟩ : syracuseStep 1757813 = 164795) (by norm_num)
theorem B3953285 : Blo 1170402 3953285 := bbase (se 4 (by rfl) ⟨370620, by rfl⟩ : syracuseStep 3953285 = 741241) (by norm_num)
theorem B1757837 : Blo 1170402 1757837 := bbase (se 3 (by rfl) ⟨329594, by rfl⟩ : syracuseStep 1757837 = 659189) (by norm_num)
theorem B2634389 : Blo 1170402 2634389 := bbase (se 6 (by rfl) ⟨61743, by rfl⟩ : syracuseStep 2634389 = 123487) (by norm_num)
theorem B1757861 : Blo 1170402 1757861 := bbase (se 4 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 1757861 = 329599) (by norm_num)
theorem B1757885 : Blo 1170402 1757885 := bbase (se 3 (by rfl) ⟨329603, by rfl⟩ : syracuseStep 1757885 = 659207) (by norm_num)
theorem B1757909 : Blo 1170402 1757909 := bbase (se 7 (by rfl) ⟨20600, by rfl⟩ : syracuseStep 1757909 = 41201) (by norm_num)
theorem B2503381 : Blo 1170402 2503381 := bbase (se 7 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 2503381 = 58673) (by norm_num)
theorem B2634461 : Blo 1170402 2634461 := bbase (se 3 (by rfl) ⟨493961, by rfl⟩ : syracuseStep 2634461 = 987923) (by norm_num)
theorem B1757933 : Blo 1170402 1757933 := bbase (se 3 (by rfl) ⟨329612, by rfl⟩ : syracuseStep 1757933 = 659225) (by norm_num)
theorem B2224901 : Blo 1170402 2224901 := bbase (se 4 (by rfl) ⟨208584, by rfl⟩ : syracuseStep 2224901 = 417169) (by norm_num)
theorem B1757957 : Blo 1170402 1757957 := bbase (se 4 (by rfl) ⟨164808, by rfl⟩ : syracuseStep 1757957 = 329617) (by norm_num)
theorem B4223765 : Blo 1170402 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B1757981 : Blo 1170402 1757981 := bbase (se 3 (by rfl) ⟨329621, by rfl⟩ : syracuseStep 1757981 = 659243) (by norm_num)
theorem B2634533 : Blo 1170402 2634533 := bbase (se 4 (by rfl) ⟨246987, by rfl⟩ : syracuseStep 2634533 = 493975) (by norm_num)
theorem B1250093 : Blo 1170402 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B1758005 : Blo 1170402 1758005 := bbase (se 5 (by rfl) ⟨82406, by rfl⟩ : syracuseStep 1758005 = 164813) (by norm_num)
theorem B1758029 : Blo 1170402 1758029 := bbase (se 3 (by rfl) ⟨329630, by rfl⟩ : syracuseStep 1758029 = 659261) (by norm_num)
theorem B1758053 : Blo 1170402 1758053 := bbase (se 4 (by rfl) ⟨164817, by rfl⟩ : syracuseStep 1758053 = 329635) (by norm_num)
theorem B2634605 : Blo 1170402 2634605 := bbase (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) (by norm_num)
theorem B1758077 : Blo 1170402 1758077 := bbase (se 3 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 1758077 = 659279) (by norm_num)
theorem B4445077 : Blo 1170402 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B2225045 : Blo 1170402 2225045 := bbase (se 6 (by rfl) ⟨52149, by rfl⟩ : syracuseStep 2225045 = 104299) (by norm_num)
theorem B1758101 : Blo 1170402 1758101 := bbase (se 6 (by rfl) ⟨41205, by rfl⟩ : syracuseStep 1758101 = 82411) (by norm_num)
theorem B1758125 : Blo 1170402 1758125 := bbase (se 3 (by rfl) ⟨329648, by rfl⟩ : syracuseStep 1758125 = 659297) (by norm_num)
theorem B2634677 : Blo 1170402 2634677 := bbase (se 5 (by rfl) ⟨123500, by rfl⟩ : syracuseStep 2634677 = 247001) (by norm_num)
theorem B1758149 : Blo 1170402 1758149 := bbase (se 4 (by rfl) ⟨164826, by rfl⟩ : syracuseStep 1758149 = 329653) (by norm_num)
theorem B2503637 : Blo 1170402 2503637 := bbase (se 7 (by rfl) ⟨29339, by rfl⟩ : syracuseStep 2503637 = 58679) (by norm_num)
theorem B1758173 : Blo 1170402 1758173 := bbase (se 3 (by rfl) ⟨329657, by rfl⟩ : syracuseStep 1758173 = 659315) (by norm_num)
theorem B1758197 : Blo 1170402 1758197 := bbase (se 5 (by rfl) ⟨82415, by rfl⟩ : syracuseStep 1758197 = 164831) (by norm_num)
theorem B2634749 : Blo 1170402 2634749 := bbase (se 3 (by rfl) ⟨494015, by rfl⟩ : syracuseStep 2634749 = 988031) (by norm_num)
theorem B1758221 : Blo 1170402 1758221 := bbase (se 3 (by rfl) ⟨329666, by rfl⟩ : syracuseStep 1758221 = 659333) (by norm_num)
theorem B1758245 : Blo 1170402 1758245 := bbase (se 4 (by rfl) ⟨164835, by rfl⟩ : syracuseStep 1758245 = 329671) (by norm_num)
theorem B3953717 : Blo 1170402 3953717 := bbase (se 5 (by rfl) ⟨185330, by rfl⟩ : syracuseStep 3953717 = 370661) (by norm_num)
theorem B1758269 : Blo 1170402 1758269 := bbase (se 3 (by rfl) ⟨329675, by rfl⟩ : syracuseStep 1758269 = 659351) (by norm_num)
theorem B2634821 : Blo 1170402 2634821 := bbase (se 4 (by rfl) ⟨247014, by rfl⟩ : syracuseStep 2634821 = 494029) (by norm_num)
theorem B1758293 : Blo 1170402 1758293 := bbase (se 8 (by rfl) ⟨10302, by rfl⟩ : syracuseStep 1758293 = 20605) (by norm_num)
theorem B1758317 : Blo 1170402 1758317 := bbase (se 3 (by rfl) ⟨329684, by rfl⟩ : syracuseStep 1758317 = 659369) (by norm_num)
theorem B1758341 : Blo 1170402 1758341 := bbase (se 4 (by rfl) ⟨164844, by rfl⟩ : syracuseStep 1758341 = 329689) (by norm_num)
theorem B2634893 : Blo 1170402 2634893 := bbase (se 3 (by rfl) ⟨494042, by rfl⟩ : syracuseStep 2634893 = 988085) (by norm_num)
theorem B1406101 : Blo 1170402 1406101 := bbase (se 6 (by rfl) ⟨32955, by rfl⟩ : syracuseStep 1406101 = 65911) (by norm_num)
theorem B1758365 : Blo 1170402 1758365 := bbase (se 3 (by rfl) ⟨329693, by rfl⟩ : syracuseStep 1758365 = 659387) (by norm_num)
theorem B2536613 : Blo 1170402 2536613 := bbase (se 4 (by rfl) ⟨237807, by rfl⟩ : syracuseStep 2536613 = 475615) (by norm_num)
theorem B2225333 : Blo 1170402 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1758389 : Blo 1170402 1758389 := bbase (se 5 (by rfl) ⟨82424, by rfl⟩ : syracuseStep 1758389 = 164849) (by norm_num)
theorem B4445381 : Blo 1170402 4445381 := bbase (se 4 (by rfl) ⟨416754, by rfl⟩ : syracuseStep 4445381 = 833509) (by norm_num)
theorem B1758413 : Blo 1170402 1758413 := bbase (se 3 (by rfl) ⟨329702, by rfl⟩ : syracuseStep 1758413 = 659405) (by norm_num)
theorem B2634965 : Blo 1170402 2634965 := bbase (se 7 (by rfl) ⟨30878, by rfl⟩ : syracuseStep 2634965 = 61757) (by norm_num)
theorem B1758437 : Blo 1170402 1758437 := bbase (se 4 (by rfl) ⟨164853, by rfl⟩ : syracuseStep 1758437 = 329707) (by norm_num)
theorem B1250537 : Blo 1170402 1250537 := bbase (se 2 (by rfl) ⟨468951, by rfl⟩ : syracuseStep 1250537 = 937903) (by norm_num)
theorem B7501045 : Blo 1170402 7501045 := bbase (se 5 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 7501045 = 703223) (by norm_num)
theorem B1758461 : Blo 1170402 1758461 := bbase (se 3 (by rfl) ⟨329711, by rfl⟩ : syracuseStep 1758461 = 659423) (by norm_num)
theorem B1758485 : Blo 1170402 1758485 := bbase (se 6 (by rfl) ⟨41214, by rfl⟩ : syracuseStep 1758485 = 82429) (by norm_num)
theorem B2635037 : Blo 1170402 2635037 := bbase (se 3 (by rfl) ⟨494069, by rfl⟩ : syracuseStep 2635037 = 988139) (by norm_num)
theorem B1250597 : Blo 1170402 1250597 := bbase (se 4 (by rfl) ⟨117243, by rfl⟩ : syracuseStep 1250597 = 234487) (by norm_num)
theorem B1758509 : Blo 1170402 1758509 := bbase (se 3 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 1758509 = 659441) (by norm_num)
theorem B2962757 : Blo 1170402 2962757 := bbase (se 4 (by rfl) ⟨277758, by rfl⟩ : syracuseStep 2962757 = 555517) (by norm_num)
theorem B1758533 : Blo 1170402 1758533 := bbase (se 4 (by rfl) ⟨164862, by rfl⟩ : syracuseStep 1758533 = 329725) (by norm_num)
theorem B2225485 : Blo 1170402 2225485 := bbase (se 3 (by rfl) ⟨417278, by rfl⟩ : syracuseStep 2225485 = 834557) (by norm_num)
theorem B1758557 : Blo 1170402 1758557 := bbase (se 3 (by rfl) ⟨329729, by rfl⟩ : syracuseStep 1758557 = 659459) (by norm_num)
theorem B2635109 : Blo 1170402 2635109 := bbase (se 4 (by rfl) ⟨247041, by rfl⟩ : syracuseStep 2635109 = 494083) (by norm_num)
theorem B1758581 : Blo 1170402 1758581 := bbase (se 5 (by rfl) ⟨82433, by rfl⟩ : syracuseStep 1758581 = 164867) (by norm_num)
theorem B2373013 : Blo 1170402 2373013 := bbase (se 6 (by rfl) ⟨55617, by rfl⟩ : syracuseStep 2373013 = 111235) (by norm_num)
theorem B5002661 : Blo 1170402 5002661 := bbase (se 4 (by rfl) ⟨468999, by rfl⟩ : syracuseStep 5002661 = 937999) (by norm_num)
theorem B1250725 : Blo 1170402 1250725 := bbase (se 4 (by rfl) ⟨117255, by rfl⟩ : syracuseStep 1250725 = 234511) (by norm_num)
theorem B2635181 : Blo 1170402 2635181 := bbase (se 3 (by rfl) ⟨494096, by rfl⟩ : syracuseStep 2635181 = 988193) (by norm_num)
theorem B2373061 : Blo 1170402 2373061 := bbase (se 4 (by rfl) ⟨222474, by rfl⟩ : syracuseStep 2373061 = 444949) (by norm_num)
theorem B5928389 : Blo 1170402 5928389 := bbase (se 4 (by rfl) ⟨555786, by rfl⟩ : syracuseStep 5928389 = 1111573) (by norm_num)
theorem B3954149 : Blo 1170402 3954149 := bbase (se 4 (by rfl) ⟨370701, by rfl⟩ : syracuseStep 3954149 = 741403) (by norm_num)
theorem B2635253 : Blo 1170402 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B1267201 : Blo 1170402 1267201 := bbase (se 2 (by rfl) ⟨475200, by rfl⟩ : syracuseStep 1267201 = 950401) (by norm_num)
theorem B1668613 : Blo 1170402 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B2110997 : Blo 1170402 2110997 := bbase (se 6 (by rfl) ⟨49476, by rfl⟩ : syracuseStep 2110997 = 98953) (by norm_num)
theorem B1406489 : Blo 1170402 1406489 := bbase (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) (by norm_num)
theorem B2635325 : Blo 1170402 2635325 := bbase (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) (by norm_num)
theorem B2635397 : Blo 1170402 2635397 := bbase (se 4 (by rfl) ⟨247068, by rfl⟩ : syracuseStep 2635397 = 494137) (by norm_num)
theorem B5346965 : Blo 1170402 5346965 := bbase (se 6 (by rfl) ⟨125319, by rfl⟩ : syracuseStep 5346965 = 250639) (by norm_num)
theorem B2963101 : Blo 1170402 2963101 := bbase (se 3 (by rfl) ⟨555581, by rfl⟩ : syracuseStep 2963101 = 1111163) (by norm_num)
theorem B2815661 : Blo 1170402 2815661 := bbase (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) (by norm_num)
theorem B2815669 : Blo 1170402 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B2635469 : Blo 1170402 2635469 := bbase (se 3 (by rfl) ⟨494150, by rfl⟩ : syracuseStep 2635469 = 988301) (by norm_num)
theorem B2537173 : Blo 1170402 2537173 := bbase (se 7 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 2537173 = 59465) (by norm_num)
theorem B2963213 : Blo 1170402 2963213 := bbase (se 3 (by rfl) ⟨555602, by rfl⟩ : syracuseStep 2963213 = 1111205) (by norm_num)
theorem B2635541 : Blo 1170402 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B2111285 : Blo 1170402 2111285 := bbase (se 5 (by rfl) ⟨98966, by rfl⟩ : syracuseStep 2111285 = 197933) (by norm_num)
theorem B3610453 : Blo 1170402 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B2635613 : Blo 1170402 2635613 := bbase (se 3 (by rfl) ⟨494177, by rfl⟩ : syracuseStep 2635613 = 988355) (by norm_num)
theorem B1251169 : Blo 1170402 1251169 := bbase (se 2 (by rfl) ⟨469188, by rfl⟩ : syracuseStep 1251169 = 938377) (by norm_num)
theorem B1316713 : Blo 1170402 1316713 := bbase (se 2 (by rfl) ⟨493767, by rfl⟩ : syracuseStep 1316713 = 987535) (by norm_num)
theorem B1406845 : Blo 1170402 1406845 := bbase (se 3 (by rfl) ⟨263783, by rfl⟩ : syracuseStep 1406845 = 527567) (by norm_num)
theorem B1316749 : Blo 1170402 1316749 := bbase (se 3 (by rfl) ⟨246890, by rfl⟩ : syracuseStep 1316749 = 493781) (by norm_num)
theorem B2930573 : Blo 1170402 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B3954581 : Blo 1170402 3954581 := bbase (se 6 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 3954581 = 185371) (by norm_num)
theorem B2635685 : Blo 1170402 2635685 := bbase (se 4 (by rfl) ⟨247095, by rfl⟩ : syracuseStep 2635685 = 494191) (by norm_num)
theorem B1316785 : Blo 1170402 1316785 := bbase (se 2 (by rfl) ⟨493794, by rfl⟩ : syracuseStep 1316785 = 987589) (by norm_num)
theorem B2963405 : Blo 1170402 2963405 := bbase (se 3 (by rfl) ⟨555638, by rfl⟩ : syracuseStep 2963405 = 1111277) (by norm_num)
theorem B1316821 : Blo 1170402 1316821 := bbase (se 7 (by rfl) ⟨15431, by rfl⟩ : syracuseStep 1316821 = 30863) (by norm_num)
theorem B1251289 : Blo 1170402 1251289 := bbase (se 2 (by rfl) ⟨469233, by rfl⟩ : syracuseStep 1251289 = 938467) (by norm_num)
theorem B2635757 : Blo 1170402 2635757 := bbase (se 3 (by rfl) ⟨494204, by rfl⟩ : syracuseStep 2635757 = 988409) (by norm_num)
theorem B1316857 : Blo 1170402 1316857 := bbase (se 2 (by rfl) ⟨493821, by rfl⟩ : syracuseStep 1316857 = 987643) (by norm_num)
theorem B1316893 : Blo 1170402 1316893 := bbase (se 3 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 1316893 = 493835) (by norm_num)
theorem B2635829 : Blo 1170402 2635829 := bbase (se 5 (by rfl) ⟨123554, by rfl⟩ : syracuseStep 2635829 = 247109) (by norm_num)
theorem B1316929 : Blo 1170402 1316929 := bbase (se 2 (by rfl) ⟨493848, by rfl⟩ : syracuseStep 1316929 = 987697) (by norm_num)
theorem B1669205 : Blo 1170402 1669205 := bbase (se 8 (by rfl) ⟨9780, by rfl⟩ : syracuseStep 1669205 = 19561) (by norm_num)
theorem B1316965 : Blo 1170402 1316965 := bbase (se 4 (by rfl) ⟨123465, by rfl⟩ : syracuseStep 1316965 = 246931) (by norm_num)
theorem B2635901 : Blo 1170402 2635901 := bbase (se 3 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 2635901 = 988463) (by norm_num)
theorem B1317001 : Blo 1170402 1317001 := bbase (se 2 (by rfl) ⟨493875, by rfl⟩ : syracuseStep 1317001 = 987751) (by norm_num)
theorem B8124565 : Blo 1170402 8124565 := bbase (se 6 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 8124565 = 380839) (by norm_num)
theorem B1669285 : Blo 1170402 1669285 := bbase (se 4 (by rfl) ⟨156495, by rfl⟩ : syracuseStep 1669285 = 312991) (by norm_num)
theorem B1317037 : Blo 1170402 1317037 := bbase (se 3 (by rfl) ⟨246944, by rfl⟩ : syracuseStep 1317037 = 493889) (by norm_num)
theorem B5339317 : Blo 1170402 5339317 := bbase (se 5 (by rfl) ⟨250280, by rfl⟩ : syracuseStep 5339317 = 500561) (by norm_num)
theorem B2635973 : Blo 1170402 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B1407181 : Blo 1170402 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B1317073 : Blo 1170402 1317073 := bbase (se 2 (by rfl) ⟨493902, by rfl⟩ : syracuseStep 1317073 = 987805) (by norm_num)
theorem B1251541 : Blo 1170402 1251541 := bbase (se 7 (by rfl) ⟨14666, by rfl⟩ : syracuseStep 1251541 = 29333) (by norm_num)
theorem B1251545 : Blo 1170402 1251545 := bbase (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) (by norm_num)
theorem B1317109 : Blo 1170402 1317109 := bbase (se 5 (by rfl) ⟨61739, by rfl⟩ : syracuseStep 1317109 = 123479) (by norm_num)
theorem B2636045 : Blo 1170402 2636045 := bbase (se 3 (by rfl) ⟨494258, by rfl⟩ : syracuseStep 2636045 = 988517) (by norm_num)
theorem B1317145 : Blo 1170402 1317145 := bbase (se 2 (by rfl) ⟨493929, by rfl⟩ : syracuseStep 1317145 = 987859) (by norm_num)
theorem B2963749 : Blo 1170402 2963749 := bbase (se 4 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 2963749 = 555703) (by norm_num)
theorem B8444213 : Blo 1170402 8444213 := bbase (se 5 (by rfl) ⟨395822, by rfl⟩ : syracuseStep 8444213 = 791645) (by norm_num)
theorem B1317181 : Blo 1170402 1317181 := bbase (se 3 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 1317181 = 493943) (by norm_num)
theorem B3955013 : Blo 1170402 3955013 := bbase (se 4 (by rfl) ⟨370782, by rfl⟩ : syracuseStep 3955013 = 741565) (by norm_num)
theorem B2636117 : Blo 1170402 2636117 := bbase (se 10 (by rfl) ⟨3861, by rfl⟩ : syracuseStep 2636117 = 7723) (by norm_num)
theorem B1317217 : Blo 1170402 1317217 := bbase (se 2 (by rfl) ⟨493956, by rfl⟩ : syracuseStep 1317217 = 987913) (by norm_num)
theorem B1317253 : Blo 1170402 1317253 := bbase (se 4 (by rfl) ⟨123492, by rfl⟩ : syracuseStep 1317253 = 246985) (by norm_num)
theorem B2963861 : Blo 1170402 2963861 := bbase (se 6 (by rfl) ⟨69465, by rfl⟩ : syracuseStep 2963861 = 138931) (by norm_num)
theorem B2636189 : Blo 1170402 2636189 := bbase (se 3 (by rfl) ⟨494285, by rfl⟩ : syracuseStep 2636189 = 988571) (by norm_num)
theorem B1317289 : Blo 1170402 1317289 := bbase (se 2 (by rfl) ⟨493983, by rfl⟩ : syracuseStep 1317289 = 987967) (by norm_num)
theorem B5339573 : Blo 1170402 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B1317325 : Blo 1170402 1317325 := bbase (se 3 (by rfl) ⟨246998, by rfl⟩ : syracuseStep 1317325 = 493997) (by norm_num)
theorem B2636261 : Blo 1170402 2636261 := bbase (se 4 (by rfl) ⟨247149, by rfl⟩ : syracuseStep 2636261 = 494299) (by norm_num)
theorem B1317361 : Blo 1170402 1317361 := bbase (se 2 (by rfl) ⟨494010, by rfl⟩ : syracuseStep 1317361 = 988021) (by norm_num)
theorem B2374157 : Blo 1170402 2374157 := bbase (se 3 (by rfl) ⟨445154, by rfl⟩ : syracuseStep 2374157 = 890309) (by norm_num)
theorem B3750421 : Blo 1170402 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B1317397 : Blo 1170402 1317397 := bbase (se 6 (by rfl) ⟨30876, by rfl⟩ : syracuseStep 1317397 = 61753) (by norm_num)
theorem B2636333 : Blo 1170402 2636333 := bbase (se 3 (by rfl) ⟨494312, by rfl⟩ : syracuseStep 2636333 = 988625) (by norm_num)
theorem B1317433 : Blo 1170402 1317433 := bbase (se 2 (by rfl) ⟨494037, by rfl⟩ : syracuseStep 1317433 = 988075) (by norm_num)
theorem B1186385 : Blo 1170402 1186385 := bbase (se 2 (by rfl) ⟨444894, by rfl⟩ : syracuseStep 1186385 = 889789) (by norm_num)
theorem B2964053 : Blo 1170402 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B2374229 : Blo 1170402 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B20019797 : Blo 1170402 20019797 := bbase (se 8 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 20019797 = 234607) (by norm_num)
theorem B1317469 : Blo 1170402 1317469 := bbase (se 3 (by rfl) ⟨247025, by rfl⟩ : syracuseStep 1317469 = 494051) (by norm_num)
theorem B2636405 : Blo 1170402 2636405 := bbase (se 5 (by rfl) ⟨123581, by rfl⟩ : syracuseStep 2636405 = 247163) (by norm_num)
theorem B1317505 : Blo 1170402 1317505 := bbase (se 2 (by rfl) ⟨494064, by rfl⟩ : syracuseStep 1317505 = 988129) (by norm_num)
theorem B2816669 : Blo 1170402 2816669 := bbase (se 3 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 2816669 = 1056251) (by norm_num)
theorem B1317541 : Blo 1170402 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B2636477 : Blo 1170402 2636477 := bbase (se 3 (by rfl) ⟨494339, by rfl⟩ : syracuseStep 2636477 = 988679) (by norm_num)
theorem B1317577 : Blo 1170402 1317577 := bbase (se 2 (by rfl) ⟨494091, by rfl⟩ : syracuseStep 1317577 = 988183) (by norm_num)
theorem B1481429 : Blo 1170402 1481429 := bbase (se 7 (by rfl) ⟨17360, by rfl⟩ : syracuseStep 1481429 = 34721) (by norm_num)
theorem B5929685 : Blo 1170402 5929685 := bbase (se 7 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 5929685 = 138977) (by norm_num)
theorem B1317613 : Blo 1170402 1317613 := bbase (se 3 (by rfl) ⟨247052, by rfl⟩ : syracuseStep 1317613 = 494105) (by norm_num)
theorem B3955445 : Blo 1170402 3955445 := bbase (se 5 (by rfl) ⟨185411, by rfl⟩ : syracuseStep 3955445 = 370823) (by norm_num)
theorem B2636549 : Blo 1170402 2636549 := bbase (se 4 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 2636549 = 494353) (by norm_num)
theorem B1481485 : Blo 1170402 1481485 := bbase (se 3 (by rfl) ⟨277778, by rfl⟩ : syracuseStep 1481485 = 555557) (by norm_num)
theorem B1317649 : Blo 1170402 1317649 := bbase (se 2 (by rfl) ⟨494118, by rfl⟩ : syracuseStep 1317649 = 988237) (by norm_num)
theorem B1317685 : Blo 1170402 1317685 := bbase (se 5 (by rfl) ⟨61766, by rfl⟩ : syracuseStep 1317685 = 123533) (by norm_num)
theorem B2636621 : Blo 1170402 2636621 := bbase (se 3 (by rfl) ⟨494366, by rfl⟩ : syracuseStep 2636621 = 988733) (by norm_num)
theorem B1604437 : Blo 1170402 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B1317721 : Blo 1170402 1317721 := bbase (se 2 (by rfl) ⟨494145, by rfl⟩ : syracuseStep 1317721 = 988291) (by norm_num)
theorem B1481581 : Blo 1170402 1481581 := bbase (se 3 (by rfl) ⟨277796, by rfl⟩ : syracuseStep 1481581 = 555593) (by norm_num)
theorem B6675317 : Blo 1170402 6675317 := bbase (se 5 (by rfl) ⟨312905, by rfl⟩ : syracuseStep 6675317 = 625811) (by norm_num)
theorem B1317757 : Blo 1170402 1317757 := bbase (se 3 (by rfl) ⟨247079, by rfl⟩ : syracuseStep 1317757 = 494159) (by norm_num)
theorem B2636693 : Blo 1170402 2636693 := bbase (se 6 (by rfl) ⟨61797, by rfl⟩ : syracuseStep 2636693 = 123595) (by norm_num)
theorem B1317793 : Blo 1170402 1317793 := bbase (se 2 (by rfl) ⟨494172, by rfl⟩ : syracuseStep 1317793 = 988345) (by norm_num)
theorem B2964397 : Blo 1170402 2964397 := bbase (se 3 (by rfl) ⟨555824, by rfl⟩ : syracuseStep 2964397 = 1111649) (by norm_num)
theorem B2112437 : Blo 1170402 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B1317829 : Blo 1170402 1317829 := bbase (se 4 (by rfl) ⟨123546, by rfl⟩ : syracuseStep 1317829 = 247093) (by norm_num)
theorem B1874909 : Blo 1170402 1874909 := bbase (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) (by norm_num)
theorem B2636765 : Blo 1170402 2636765 := bbase (se 3 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 2636765 = 988787) (by norm_num)
theorem B1317865 : Blo 1170402 1317865 := bbase (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) (by norm_num)
theorem B3333125 : Blo 1170402 3333125 := bbase (se 4 (by rfl) ⟨312480, by rfl⟩ : syracuseStep 3333125 = 624961) (by norm_num)
theorem B4815877 : Blo 1170402 4815877 := bbase (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) (by norm_num)
theorem B2112517 : Blo 1170402 2112517 := bbase (se 4 (by rfl) ⟨198048, by rfl⟩ : syracuseStep 2112517 = 396097) (by norm_num)
theorem B1317901 : Blo 1170402 1317901 := bbase (se 3 (by rfl) ⟨247106, by rfl⟩ : syracuseStep 1317901 = 494213) (by norm_num)
theorem B1481753 : Blo 1170402 1481753 := bbase (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) (by norm_num)
theorem B2964509 : Blo 1170402 2964509 := bbase (se 3 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 2964509 = 1111691) (by norm_num)
theorem B2636837 : Blo 1170402 2636837 := bbase (se 4 (by rfl) ⟨247203, by rfl⟩ : syracuseStep 2636837 = 494407) (by norm_num)
theorem B1317937 : Blo 1170402 1317937 := bbase (se 2 (by rfl) ⟨494226, by rfl⟩ : syracuseStep 1317937 = 988453) (by norm_num)
theorem B1408061 : Blo 1170402 1408061 := bbase (se 3 (by rfl) ⟨264011, by rfl⟩ : syracuseStep 1408061 = 528023) (by norm_num)
theorem B1481809 : Blo 1170402 1481809 := bbase (se 2 (by rfl) ⟨555678, by rfl⟩ : syracuseStep 1481809 = 1111357) (by norm_num)
theorem B5069909 : Blo 1170402 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B1317973 : Blo 1170402 1317973 := bbase (se 8 (by rfl) ⟨7722, by rfl⟩ : syracuseStep 1317973 = 15445) (by norm_num)
theorem B2636909 : Blo 1170402 2636909 := bbase (se 3 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 2636909 = 988841) (by norm_num)
theorem B1318009 : Blo 1170402 1318009 := bbase (se 2 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 1318009 = 988507) (by norm_num)
theorem B1186969 : Blo 1170402 1186969 := bbase (se 2 (by rfl) ⟨445113, by rfl⟩ : syracuseStep 1186969 = 890227) (by norm_num)
theorem B1318045 : Blo 1170402 1318045 := bbase (se 3 (by rfl) ⟨247133, by rfl⟩ : syracuseStep 1318045 = 494267) (by norm_num)
theorem B3955877 : Blo 1170402 3955877 := bbase (se 4 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 3955877 = 741727) (by norm_num)
theorem B1481905 : Blo 1170402 1481905 := bbase (se 2 (by rfl) ⟨555714, by rfl⟩ : syracuseStep 1481905 = 1111429) (by norm_num)
theorem B2636981 : Blo 1170402 2636981 := bbase (se 5 (by rfl) ⟨123608, by rfl⟩ : syracuseStep 2636981 = 247217) (by norm_num)
theorem B2170037 : Blo 1170402 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B1318081 : Blo 1170402 1318081 := bbase (se 2 (by rfl) ⟨494280, by rfl⟩ : syracuseStep 1318081 = 988561) (by norm_num)
theorem B2964701 : Blo 1170402 2964701 := bbase (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) (by norm_num)
theorem B1318117 : Blo 1170402 1318117 := bbase (se 4 (by rfl) ⟨123573, by rfl⟩ : syracuseStep 1318117 = 247147) (by norm_num)
theorem B1219825 : Blo 1170402 1219825 := bbase (se 2 (by rfl) ⟨457434, by rfl⟩ : syracuseStep 1219825 = 914869) (by norm_num)
theorem B2637053 : Blo 1170402 2637053 := bbase (se 3 (by rfl) ⟨494447, by rfl⟩ : syracuseStep 2637053 = 988895) (by norm_num)
theorem B4447493 : Blo 1170402 4447493 := bbase (se 4 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 4447493 = 833905) (by norm_num)
theorem B1318153 : Blo 1170402 1318153 := bbase (se 2 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 1318153 = 988615) (by norm_num)
theorem B1318189 : Blo 1170402 1318189 := bbase (se 3 (by rfl) ⟨247160, by rfl⟩ : syracuseStep 1318189 = 494321) (by norm_num)
theorem B2637125 : Blo 1170402 2637125 := bbase (se 4 (by rfl) ⟨247230, by rfl⟩ : syracuseStep 2637125 = 494461) (by norm_num)
theorem B1318225 : Blo 1170402 1318225 := bbase (se 2 (by rfl) ⟨494334, by rfl⟩ : syracuseStep 1318225 = 988669) (by norm_num)
theorem B1482077 : Blo 1170402 1482077 := bbase (se 3 (by rfl) ⟨277889, by rfl⟩ : syracuseStep 1482077 = 555779) (by norm_num)
theorem B1408369 : Blo 1170402 1408369 := bbase (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) (by norm_num)
theorem B1318261 : Blo 1170402 1318261 := bbase (se 5 (by rfl) ⟨61793, by rfl⟩ : syracuseStep 1318261 = 123587) (by norm_num)
theorem B2637197 : Blo 1170402 2637197 := bbase (se 3 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 2637197 = 988949) (by norm_num)
theorem B1482133 : Blo 1170402 1482133 := bbase (se 6 (by rfl) ⟨34737, by rfl⟩ : syracuseStep 1482133 = 69475) (by norm_num)
theorem B1318297 : Blo 1170402 1318297 := bbase (se 2 (by rfl) ⟨494361, by rfl⟩ : syracuseStep 1318297 = 988723) (by norm_num)
theorem B1187245 : Blo 1170402 1187245 := bbase (se 3 (by rfl) ⟨222608, by rfl⟩ : syracuseStep 1187245 = 445217) (by norm_num)
theorem B1318333 : Blo 1170402 1318333 := bbase (se 3 (by rfl) ⟨247187, by rfl⟩ : syracuseStep 1318333 = 494375) (by norm_num)
theorem B11263445 : Blo 1170402 11263445 := bbase (se 7 (by rfl) ⟨131993, by rfl⟩ : syracuseStep 11263445 = 263987) (by norm_num)
theorem B2637269 : Blo 1170402 2637269 := bbase (se 7 (by rfl) ⟨30905, by rfl⟩ : syracuseStep 2637269 = 61811) (by norm_num)
theorem B1875421 : Blo 1170402 1875421 := bbase (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) (by norm_num)
theorem B1318369 : Blo 1170402 1318369 := bbase (se 2 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 1318369 = 988777) (by norm_num)
theorem B1482229 : Blo 1170402 1482229 := bbase (se 5 (by rfl) ⟨69479, by rfl⟩ : syracuseStep 1482229 = 138959) (by norm_num)
theorem B1318405 : Blo 1170402 1318405 := bbase (se 4 (by rfl) ⟨123600, by rfl⟩ : syracuseStep 1318405 = 247201) (by norm_num)
theorem B2637341 : Blo 1170402 2637341 := bbase (se 3 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 2637341 = 989003) (by norm_num)
theorem B1523233 : Blo 1170402 1523233 := bbase (se 2 (by rfl) ⟨571212, by rfl⟩ : syracuseStep 1523233 = 1142425) (by norm_num)
theorem B4447781 : Blo 1170402 4447781 := bbase (se 4 (by rfl) ⟨416979, by rfl⟩ : syracuseStep 4447781 = 833959) (by norm_num)
theorem B1318441 : Blo 1170402 1318441 := bbase (se 2 (by rfl) ⟨494415, by rfl⟩ : syracuseStep 1318441 = 988831) (by norm_num)
theorem B2965045 : Blo 1170402 2965045 := bbase (se 5 (by rfl) ⟨138986, by rfl⟩ : syracuseStep 2965045 = 277973) (by norm_num)
theorem B1318477 : Blo 1170402 1318477 := bbase (se 3 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 1318477 = 494429) (by norm_num)
theorem B3956309 : Blo 1170402 3956309 := bbase (se 8 (by rfl) ⟨23181, by rfl⟩ : syracuseStep 3956309 = 46363) (by norm_num)
theorem B2637413 : Blo 1170402 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B1318513 : Blo 1170402 1318513 := bbase (se 2 (by rfl) ⟨494442, by rfl⟩ : syracuseStep 1318513 = 988885) (by norm_num)
theorem B1318549 : Blo 1170402 1318549 := bbase (se 6 (by rfl) ⟨30903, by rfl⟩ : syracuseStep 1318549 = 61807) (by norm_num)
theorem B1482401 : Blo 1170402 1482401 := bbase (se 2 (by rfl) ⟨555900, by rfl⟩ : syracuseStep 1482401 = 1111801) (by norm_num)
theorem B2965157 : Blo 1170402 2965157 := bbase (se 4 (by rfl) ⟨277983, by rfl⟩ : syracuseStep 2965157 = 555967) (by norm_num)
theorem B2375333 : Blo 1170402 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B2637485 : Blo 1170402 2637485 := bbase (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) (by norm_num)
theorem B1318585 : Blo 1170402 1318585 := bbase (se 2 (by rfl) ⟨494469, by rfl⟩ : syracuseStep 1318585 = 988939) (by norm_num)
theorem B2375365 : Blo 1170402 2375365 := bbase (se 4 (by rfl) ⟨222690, by rfl⟩ : syracuseStep 2375365 = 445381) (by norm_num)
theorem B1482457 : Blo 1170402 1482457 := bbase (se 2 (by rfl) ⟨555921, by rfl⟩ : syracuseStep 1482457 = 1111843) (by norm_num)
theorem B1318621 : Blo 1170402 1318621 := bbase (se 3 (by rfl) ⟨247241, by rfl⟩ : syracuseStep 1318621 = 494483) (by norm_num)
theorem B1187569 : Blo 1170402 1187569 := bbase (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) (by norm_num)
theorem B2637557 : Blo 1170402 2637557 := bbase (se 5 (by rfl) ⟨123635, by rfl⟩ : syracuseStep 2637557 = 247271) (by norm_num)
theorem B1318657 : Blo 1170402 1318657 := bbase (se 2 (by rfl) ⟨494496, by rfl⟩ : syracuseStep 1318657 = 988993) (by norm_num)
theorem B4275989 : Blo 1170402 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B1318693 : Blo 1170402 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B1482553 : Blo 1170402 1482553 := bbase (se 2 (by rfl) ⟨555957, by rfl⟩ : syracuseStep 1482553 = 1111915) (by norm_num)
theorem B2637629 : Blo 1170402 2637629 := bbase (se 3 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 2637629 = 989111) (by norm_num)
theorem B1318729 : Blo 1170402 1318729 := bbase (se 2 (by rfl) ⟨494523, by rfl⟩ : syracuseStep 1318729 = 989047) (by norm_num)
theorem B2965349 : Blo 1170402 2965349 := bbase (se 4 (by rfl) ⟨278001, by rfl⟩ : syracuseStep 2965349 = 556003) (by norm_num)
theorem B1318765 : Blo 1170402 1318765 := bbase (se 3 (by rfl) ⟨247268, by rfl⟩ : syracuseStep 1318765 = 494537) (by norm_num)
theorem B2637701 : Blo 1170402 2637701 := bbase (se 4 (by rfl) ⟨247284, by rfl⟩ : syracuseStep 2637701 = 494569) (by norm_num)
theorem B1425289 : Blo 1170402 1425289 := bbase (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) (by norm_num)
theorem B1318801 : Blo 1170402 1318801 := bbase (se 2 (by rfl) ⟨494550, by rfl⟩ : syracuseStep 1318801 = 989101) (by norm_num)
theorem B1318837 : Blo 1170402 1318837 := bbase (se 5 (by rfl) ⟨61820, by rfl⟩ : syracuseStep 1318837 = 123641) (by norm_num)
theorem B2637773 : Blo 1170402 2637773 := bbase (se 3 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 2637773 = 989165) (by norm_num)
theorem B1318873 : Blo 1170402 1318873 := bbase (se 2 (by rfl) ⟨494577, by rfl⟩ : syracuseStep 1318873 = 989155) (by norm_num)
theorem B1482725 : Blo 1170402 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B5930981 : Blo 1170402 5930981 := bbase (se 4 (by rfl) ⟨556029, by rfl⟩ : syracuseStep 5930981 = 1112059) (by norm_num)
theorem B1933301 : Blo 1170402 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B1171459 : Blo 1170402 1171459 := bstep (se 1 (by rfl) ⟨878594, by rfl⟩ : syracuseStep 1171459 = 1757189) B1757189
theorem B2637827 : Blo 1170402 2637827 := bstep (se 1 (by rfl) ⟨1978370, by rfl⟩ : syracuseStep 2637827 = 3956741) B3956741
theorem B1171475 : Blo 1170402 1171475 := bstep (se 1 (by rfl) ⟨878606, by rfl⟩ : syracuseStep 1171475 = 1757213) B1757213
theorem B1171491 : Blo 1170402 1171491 := bstep (se 1 (by rfl) ⟨878618, by rfl⟩ : syracuseStep 1171491 = 1757237) B1757237
theorem B1171507 : Blo 1170402 1171507 := bstep (se 1 (by rfl) ⟨878630, by rfl⟩ : syracuseStep 1171507 = 1757261) B1757261
theorem B1171523 : Blo 1170402 1171523 := bstep (se 1 (by rfl) ⟨878642, by rfl⟩ : syracuseStep 1171523 = 1757285) B1757285
theorem B1171539 : Blo 1170402 1171539 := bstep (se 1 (by rfl) ⟨878654, by rfl⟩ : syracuseStep 1171539 = 1757309) B1757309
theorem B1171555 : Blo 1170402 1171555 := bstep (se 1 (by rfl) ⟨878666, by rfl⟩ : syracuseStep 1171555 = 1757333) B1757333
theorem B3956849 : Blo 1170402 3956849 := bstep (se 2 (by rfl) ⟨1483818, by rfl⟩ : syracuseStep 3956849 = 2967637) B2967637
theorem B1171571 : Blo 1170402 1171571 := bstep (se 1 (by rfl) ⟨878678, by rfl⟩ : syracuseStep 1171571 = 1757357) B1757357
theorem B1171587 : Blo 1170402 1171587 := bstep (se 1 (by rfl) ⟨878690, by rfl⟩ : syracuseStep 1171587 = 1757381) B1757381
theorem B1171603 : Blo 1170402 1171603 := bstep (se 1 (by rfl) ⟨878702, by rfl⟩ : syracuseStep 1171603 = 1757405) B1757405
theorem B1171619 : Blo 1170402 1171619 := bstep (se 1 (by rfl) ⟨878714, by rfl⟩ : syracuseStep 1171619 = 1757429) B1757429
theorem B1171635 : Blo 1170402 1171635 := bstep (se 1 (by rfl) ⟨878726, by rfl⟩ : syracuseStep 1171635 = 1757453) B1757453
theorem B1171651 : Blo 1170402 1171651 := bstep (se 1 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 1171651 = 1757477) B1757477
theorem B1171667 : Blo 1170402 1171667 := bstep (se 1 (by rfl) ⟨878750, by rfl⟩ : syracuseStep 1171667 = 1757501) B1757501
theorem B1171683 : Blo 1170402 1171683 := bstep (se 1 (by rfl) ⟨878762, by rfl⟩ : syracuseStep 1171683 = 1757525) B1757525
theorem B7119089 : Blo 1170402 7119089 := bstep (se 2 (by rfl) ⟨2669658, by rfl⟩ : syracuseStep 7119089 = 5339317) B5339317
theorem B1171699 : Blo 1170402 1171699 := bstep (se 1 (by rfl) ⟨878774, by rfl⟩ : syracuseStep 1171699 = 1757549) B1757549
theorem B1171715 : Blo 1170402 1171715 := bstep (se 1 (by rfl) ⟨878786, by rfl⟩ : syracuseStep 1171715 = 1757573) B1757573
theorem B1876241 : Blo 1170402 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1171731 : Blo 1170402 1171731 := bstep (se 1 (by rfl) ⟨878798, by rfl⟩ : syracuseStep 1171731 = 1757597) B1757597
theorem B1171747 : Blo 1170402 1171747 := bstep (se 1 (by rfl) ⟨878810, by rfl⟩ : syracuseStep 1171747 = 1757621) B1757621
theorem B1171763 : Blo 1170402 1171763 := bstep (se 1 (by rfl) ⟨878822, by rfl⟩ : syracuseStep 1171763 = 1757645) B1757645
theorem B1171779 : Blo 1170402 1171779 := bstep (se 1 (by rfl) ⟨878834, by rfl⟩ : syracuseStep 1171779 = 1757669) B1757669
theorem B1171795 : Blo 1170402 1171795 := bstep (se 1 (by rfl) ⟨878846, by rfl⟩ : syracuseStep 1171795 = 1757693) B1757693
theorem B1171811 : Blo 1170402 1171811 := bstep (se 1 (by rfl) ⟨878858, by rfl⟩ : syracuseStep 1171811 = 1757717) B1757717
theorem B1171827 : Blo 1170402 1171827 := bstep (se 1 (by rfl) ⟨878870, by rfl⟩ : syracuseStep 1171827 = 1757741) B1757741
theorem B1171843 : Blo 1170402 1171843 := bstep (se 1 (by rfl) ⟨878882, by rfl⟩ : syracuseStep 1171843 = 1757765) B1757765
theorem B1171859 : Blo 1170402 1171859 := bstep (se 1 (by rfl) ⟨878894, by rfl⟩ : syracuseStep 1171859 = 1757789) B1757789
theorem B1171875 : Blo 1170402 1171875 := bstep (se 1 (by rfl) ⟨878906, by rfl⟩ : syracuseStep 1171875 = 1757813) B1757813
theorem B3752369 : Blo 1170402 3752369 := bstep (se 2 (by rfl) ⟨1407138, by rfl⟩ : syracuseStep 3752369 = 2814277) B2814277
theorem B1171891 : Blo 1170402 1171891 := bstep (se 1 (by rfl) ⟨878918, by rfl⟩ : syracuseStep 1171891 = 1757837) B1757837
theorem B1171907 : Blo 1170402 1171907 := bstep (se 1 (by rfl) ⟨878930, by rfl⟩ : syracuseStep 1171907 = 1757861) B1757861
theorem B1171923 : Blo 1170402 1171923 := bstep (se 1 (by rfl) ⟨878942, by rfl⟩ : syracuseStep 1171923 = 1757885) B1757885
theorem B1171939 : Blo 1170402 1171939 := bstep (se 1 (by rfl) ⟨878954, by rfl⟩ : syracuseStep 1171939 = 1757909) B1757909
theorem B4448753 : Blo 1170402 4448753 := bstep (se 2 (by rfl) ⟨1668282, by rfl⟩ : syracuseStep 4448753 = 3336565) B3336565
theorem B1171955 : Blo 1170402 1171955 := bstep (se 1 (by rfl) ⟨878966, by rfl⟩ : syracuseStep 1171955 = 1757933) B1757933
theorem B1483267 : Blo 1170402 1483267 := bstep (se 1 (by rfl) ⟨1112450, by rfl⟩ : syracuseStep 1483267 = 2224901) B2224901
theorem B1171971 : Blo 1170402 1171971 := bstep (se 1 (by rfl) ⟨878978, by rfl⟩ : syracuseStep 1171971 = 1757957) B1757957
theorem B1524227 : Blo 1170402 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B1171987 : Blo 1170402 1171987 := bstep (se 1 (by rfl) ⟨878990, by rfl⟩ : syracuseStep 1171987 = 1757981) B1757981
theorem B1172003 : Blo 1170402 1172003 := bstep (se 1 (by rfl) ⟨879002, by rfl⟩ : syracuseStep 1172003 = 1758005) B1758005
theorem B1172019 : Blo 1170402 1172019 := bstep (se 1 (by rfl) ⟨879014, by rfl⟩ : syracuseStep 1172019 = 1758029) B1758029
theorem B1172035 : Blo 1170402 1172035 := bstep (se 1 (by rfl) ⟨879026, by rfl⟩ : syracuseStep 1172035 = 1758053) B1758053
theorem B1172051 : Blo 1170402 1172051 := bstep (se 1 (by rfl) ⟨879038, by rfl⟩ : syracuseStep 1172051 = 1758077) B1758077
theorem B1483363 : Blo 1170402 1483363 := bstep (se 1 (by rfl) ⟨1112522, by rfl⟩ : syracuseStep 1483363 = 2225045) B2225045
theorem B1172067 : Blo 1170402 1172067 := bstep (se 1 (by rfl) ⟨879050, by rfl⟩ : syracuseStep 1172067 = 1758101) B1758101
theorem B3334765 : Blo 1170402 3334765 := bstep (se 3 (by rfl) ⟨625268, by rfl⟩ : syracuseStep 3334765 = 1250537) B1250537
theorem B2966129 : Blo 1170402 2966129 := bstep (se 2 (by rfl) ⟨1112298, by rfl⟩ : syracuseStep 2966129 = 2224597) B2224597
theorem B1172083 : Blo 1170402 1172083 := bstep (se 1 (by rfl) ⟨879062, by rfl⟩ : syracuseStep 1172083 = 1758125) B1758125
theorem B2376305 : Blo 1170402 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B1172099 : Blo 1170402 1172099 := bstep (se 1 (by rfl) ⟨879074, by rfl⟩ : syracuseStep 1172099 = 1758149) B1758149
theorem B1172115 : Blo 1170402 1172115 := bstep (se 1 (by rfl) ⟨879086, by rfl⟩ : syracuseStep 1172115 = 1758173) B1758173
theorem B2966179 : Blo 1170402 2966179 := bstep (se 1 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 2966179 = 4449269) B4449269
theorem B1172131 : Blo 1170402 1172131 := bstep (se 1 (by rfl) ⟨879098, by rfl⟩ : syracuseStep 1172131 = 1758197) B1758197
theorem B1172147 : Blo 1170402 1172147 := bstep (se 1 (by rfl) ⟨879110, by rfl⟩ : syracuseStep 1172147 = 1758221) B1758221
theorem B1172163 : Blo 1170402 1172163 := bstep (se 1 (by rfl) ⟨879122, by rfl⟩ : syracuseStep 1172163 = 1758245) B1758245
theorem B1172179 : Blo 1170402 1172179 := bstep (se 1 (by rfl) ⟨879134, by rfl⟩ : syracuseStep 1172179 = 1758269) B1758269
theorem B1172195 : Blo 1170402 1172195 := bstep (se 1 (by rfl) ⟨879146, by rfl⟩ : syracuseStep 1172195 = 1758293) B1758293
theorem B1172211 : Blo 1170402 1172211 := bstep (se 1 (by rfl) ⟨879158, by rfl⟩ : syracuseStep 1172211 = 1758317) B1758317
theorem B1172227 : Blo 1170402 1172227 := bstep (se 1 (by rfl) ⟨879170, by rfl⟩ : syracuseStep 1172227 = 1758341) B1758341
theorem B3334925 : Blo 1170402 3334925 := bstep (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) B1250597
theorem B1172243 : Blo 1170402 1172243 := bstep (se 1 (by rfl) ⟨879182, by rfl⟩ : syracuseStep 1172243 = 1758365) B1758365
theorem B1172259 : Blo 1170402 1172259 := bstep (se 1 (by rfl) ⟨879194, by rfl⟩ : syracuseStep 1172259 = 1758389) B1758389
theorem B2966321 : Blo 1170402 2966321 := bstep (se 2 (by rfl) ⟨1112370, by rfl⟩ : syracuseStep 2966321 = 2224741) B2224741
theorem B1172275 : Blo 1170402 1172275 := bstep (se 1 (by rfl) ⟨879206, by rfl⟩ : syracuseStep 1172275 = 1758413) B1758413
theorem B1172291 : Blo 1170402 1172291 := bstep (se 1 (by rfl) ⟨879218, by rfl⟩ : syracuseStep 1172291 = 1758437) B1758437
theorem B1172307 : Blo 1170402 1172307 := bstep (se 1 (by rfl) ⟨879230, by rfl⟩ : syracuseStep 1172307 = 1758461) B1758461
theorem B1172323 : Blo 1170402 1172323 := bstep (se 1 (by rfl) ⟨879242, by rfl⟩ : syracuseStep 1172323 = 1758485) B1758485
theorem B1172339 : Blo 1170402 1172339 := bstep (se 1 (by rfl) ⟨879254, by rfl⟩ : syracuseStep 1172339 = 1758509) B1758509
theorem B1975171 : Blo 1170402 1975171 := bstep (se 1 (by rfl) ⟨1481378, by rfl⟩ : syracuseStep 1975171 = 2962757) B2962757
theorem B1172355 : Blo 1170402 1172355 := bstep (se 1 (by rfl) ⟨879266, by rfl⟩ : syracuseStep 1172355 = 1758533) B1758533
theorem B1172371 : Blo 1170402 1172371 := bstep (se 1 (by rfl) ⟨879278, by rfl⟩ : syracuseStep 1172371 = 1758557) B1758557
theorem B1172387 : Blo 1170402 1172387 := bstep (se 1 (by rfl) ⟨879290, by rfl⟩ : syracuseStep 1172387 = 1758581) B1758581
theorem B5931953 : Blo 1170402 5931953 := bstep (se 2 (by rfl) ⟨2224482, by rfl⟩ : syracuseStep 5931953 = 4448965) B4448965
theorem B3335107 : Blo 1170402 3335107 := bstep (se 1 (by rfl) ⟨2501330, by rfl⟩ : syracuseStep 3335107 = 5002661) B5002661
theorem B18039779 : Blo 1170402 18039779 := bstep (se 1 (by rfl) ⟨13529834, by rfl⟩ : syracuseStep 18039779 = 27059669) B27059669
theorem B1975313 : Blo 1170402 1975313 := bstep (se 2 (by rfl) ⟨740742, by rfl⟩ : syracuseStep 1975313 = 1481485) B1481485
theorem B3752995 : Blo 1170402 3752995 := bstep (se 1 (by rfl) ⟨2814746, by rfl⟩ : syracuseStep 3752995 = 5629493) B5629493
theorem B3564643 : Blo 1170402 3564643 := bstep (se 1 (by rfl) ⟨2673482, by rfl⟩ : syracuseStep 3564643 = 5346965) B5346965
theorem B1877107 : Blo 1170402 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B4220045 : Blo 1170402 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B1975441 : Blo 1170402 1975441 := bstep (se 2 (by rfl) ⟨740790, by rfl⟩ : syracuseStep 1975441 = 1481581) B1481581
theorem B1975475 : Blo 1170402 1975475 := bstep (se 1 (by rfl) ⟨1481606, by rfl⟩ : syracuseStep 1975475 = 2963213) B2963213
theorem B6505733 : Blo 1170402 6505733 := bstep (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) B1219825
theorem B1975603 : Blo 1170402 1975603 := bstep (se 1 (by rfl) ⟨1481702, by rfl⟩ : syracuseStep 1975603 = 2963405) B2963405
theorem B1975745 : Blo 1170402 1975745 := bstep (se 2 (by rfl) ⟨740904, by rfl⟩ : syracuseStep 1975745 = 1481809) B1481809
theorem B1582625 : Blo 1170402 1582625 := bstep (se 2 (by rfl) ⟨593484, by rfl⟩ : syracuseStep 1582625 = 1186969) B1186969
theorem B5629475 : Blo 1170402 5629475 := bstep (se 1 (by rfl) ⟨4222106, by rfl⟩ : syracuseStep 5629475 = 8444213) B8444213
theorem B3163693 : Blo 1170402 3163693 := bstep (se 3 (by rfl) ⟨593192, by rfl⟩ : syracuseStep 3163693 = 1186385) B1186385
theorem B1975873 : Blo 1170402 1975873 := bstep (se 2 (by rfl) ⟨740952, by rfl⟩ : syracuseStep 1975873 = 1481905) B1481905
theorem B1975907 : Blo 1170402 1975907 := bstep (se 1 (by rfl) ⟨1481930, by rfl⟩ : syracuseStep 1975907 = 2963861) B2963861
theorem B1976035 : Blo 1170402 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B13346531 : Blo 1170402 13346531 := bstep (se 1 (by rfl) ⟨10009898, by rfl⟩ : syracuseStep 13346531 = 20019797) B20019797
theorem B2967313 : Blo 1170402 2967313 := bstep (se 2 (by rfl) ⟨1112742, by rfl⟩ : syracuseStep 2967313 = 2225485) B2225485
theorem B1877779 : Blo 1170402 1877779 := bstep (se 1 (by rfl) ⟨1408334, by rfl⟩ : syracuseStep 1877779 = 2816669) B2816669
theorem B1877825 : Blo 1170402 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B3164017 : Blo 1170402 3164017 := bstep (se 2 (by rfl) ⟨1186506, by rfl⟩ : syracuseStep 3164017 = 2373013) B2373013
theorem B1976177 : Blo 1170402 1976177 := bstep (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) B1482133
theorem B11265905 : Blo 1170402 11265905 := bstep (se 2 (by rfl) ⟨4224714, by rfl⟩ : syracuseStep 11265905 = 8449429) B8449429
theorem B3950477 : Blo 1170402 3950477 := bstep (se 3 (by rfl) ⟨740714, by rfl⟩ : syracuseStep 3950477 = 1481429) B1481429
theorem B1582993 : Blo 1170402 1582993 := bstep (se 2 (by rfl) ⟨593622, by rfl⟩ : syracuseStep 1582993 = 1187245) B1187245
theorem B4450211 : Blo 1170402 4450211 := bstep (se 1 (by rfl) ⟨3337658, by rfl⟩ : syracuseStep 4450211 = 6675317) B6675317
theorem B3164081 : Blo 1170402 3164081 := bstep (se 2 (by rfl) ⟨1186530, by rfl⟩ : syracuseStep 3164081 = 2373061) B2373061
theorem B3950531 : Blo 1170402 3950531 := bstep (se 1 (by rfl) ⟨2962898, by rfl⟩ : syracuseStep 3950531 = 5925797) B5925797
theorem B2500561 : Blo 1170402 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B1976305 : Blo 1170402 1976305 := bstep (se 2 (by rfl) ⟨741114, by rfl⟩ : syracuseStep 1976305 = 1482229) B1482229
theorem B1689601 : Blo 1170402 1689601 := bstep (se 2 (by rfl) ⟨633600, by rfl⟩ : syracuseStep 1689601 = 1267201) B1267201
theorem B2222083 : Blo 1170402 2222083 := bstep (se 1 (by rfl) ⟨1666562, by rfl⟩ : syracuseStep 2222083 = 3333125) B3333125
theorem B1976339 : Blo 1170402 1976339 := bstep (se 1 (by rfl) ⟨1482254, by rfl⟩ : syracuseStep 1976339 = 2964509) B2964509
theorem B2967587 : Blo 1170402 2967587 := bstep (se 1 (by rfl) ⟨2225690, by rfl⟩ : syracuseStep 2967587 = 4451381) B4451381
theorem B2222129 : Blo 1170402 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B8898659 : Blo 1170402 8898659 := bstep (se 1 (by rfl) ⟨6673994, by rfl⟩ : syracuseStep 8898659 = 13347989) B13347989
theorem B1976467 : Blo 1170402 1976467 := bstep (se 1 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 1976467 = 2964701) B2964701
theorem B3950801 : Blo 1170402 3950801 := bstep (se 2 (by rfl) ⟨1481550, by rfl⟩ : syracuseStep 3950801 = 2963101) B2963101
theorem B3754225 : Blo 1170402 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B1976609 : Blo 1170402 1976609 := bstep (se 2 (by rfl) ⟨741228, by rfl⟩ : syracuseStep 1976609 = 1482457) B1482457
theorem B3336497 : Blo 1170402 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B1583425 : Blo 1170402 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B2222417 : Blo 1170402 2222417 := bstep (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) B1666813
theorem B5933411 : Blo 1170402 5933411 := bstep (se 1 (by rfl) ⟨4450058, by rfl⟩ : syracuseStep 5933411 = 8900117) B8900117
theorem B1976737 : Blo 1170402 1976737 := bstep (se 2 (by rfl) ⟨741276, by rfl⟩ : syracuseStep 1976737 = 1482553) B1482553
theorem B1976771 : Blo 1170402 1976771 := bstep (se 1 (by rfl) ⟨1482578, by rfl⟩ : syracuseStep 1976771 = 2965157) B2965157
theorem B1583555 : Blo 1170402 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B1755617 : Blo 1170402 1755617 := bstep (se 2 (by rfl) ⟨658356, by rfl⟩ : syracuseStep 1755617 = 1316713) B1316713
theorem B1755635 : Blo 1170402 1755635 := bstep (se 1 (by rfl) ⟨1316726, by rfl⟩ : syracuseStep 1755635 = 2633453) B2633453
theorem B1755665 : Blo 1170402 1755665 := bstep (se 2 (by rfl) ⟨658374, by rfl⟩ : syracuseStep 1755665 = 1316749) B1316749
theorem B1755683 : Blo 1170402 1755683 := bstep (se 1 (by rfl) ⟨1316762, by rfl⟩ : syracuseStep 1755683 = 2633525) B2633525
theorem B1755713 : Blo 1170402 1755713 := bstep (se 2 (by rfl) ⟨658392, by rfl⟩ : syracuseStep 1755713 = 1316785) B1316785
theorem B1976899 : Blo 1170402 1976899 := bstep (se 1 (by rfl) ⟨1482674, by rfl⟩ : syracuseStep 1976899 = 2965349) B2965349
theorem B1755731 : Blo 1170402 1755731 := bstep (se 1 (by rfl) ⟨1316798, by rfl⟩ : syracuseStep 1755731 = 2633597) B2633597
theorem B1755761 : Blo 1170402 1755761 := bstep (se 2 (by rfl) ⟨658410, by rfl⟩ : syracuseStep 1755761 = 1316821) B1316821
theorem B1755779 : Blo 1170402 1755779 := bstep (se 1 (by rfl) ⟨1316834, by rfl⟩ : syracuseStep 1755779 = 2633669) B2633669
theorem B1755809 : Blo 1170402 1755809 := bstep (se 2 (by rfl) ⟨658428, by rfl⟩ : syracuseStep 1755809 = 1316857) B1316857
theorem B1288867 : Blo 1170402 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B1755827 : Blo 1170402 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B11250373 : Blo 1170402 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B1755857 : Blo 1170402 1755857 := bstep (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) B1316893
theorem B1977041 : Blo 1170402 1977041 := bstep (se 2 (by rfl) ⟨741390, by rfl⟩ : syracuseStep 1977041 = 1482781) B1482781
theorem B1755875 : Blo 1170402 1755875 := bstep (se 1 (by rfl) ⟨1316906, by rfl⟩ : syracuseStep 1755875 = 2633813) B2633813
theorem B3951341 : Blo 1170402 3951341 := bstep (se 3 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 3951341 = 1481753) B1481753
theorem B5630705 : Blo 1170402 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B1583857 : Blo 1170402 1583857 := bstep (se 2 (by rfl) ⟨593946, by rfl⟩ : syracuseStep 1583857 = 1187893) B1187893
theorem B1755905 : Blo 1170402 1755905 := bstep (se 2 (by rfl) ⟨658464, by rfl⟩ : syracuseStep 1755905 = 1316929) B1316929
theorem B10013453 : Blo 1170402 10013453 := bstep (se 3 (by rfl) ⟨1877522, by rfl⟩ : syracuseStep 10013453 = 3755045) B3755045
theorem B1755923 : Blo 1170402 1755923 := bstep (se 1 (by rfl) ⟨1316942, by rfl⟩ : syracuseStep 1755923 = 2633885) B2633885
theorem B3951395 : Blo 1170402 3951395 := bstep (se 1 (by rfl) ⟨2963546, by rfl⟩ : syracuseStep 3951395 = 5927093) B5927093
theorem B1755953 : Blo 1170402 1755953 := bstep (se 2 (by rfl) ⟨658482, by rfl⟩ : syracuseStep 1755953 = 1316965) B1316965
theorem B1755971 : Blo 1170402 1755971 := bstep (se 1 (by rfl) ⟨1316978, by rfl⟩ : syracuseStep 1755971 = 2633957) B2633957
theorem B3754829 : Blo 1170402 3754829 := bstep (se 3 (by rfl) ⟨704030, by rfl⟩ : syracuseStep 3754829 = 1408061) B1408061
theorem B1977169 : Blo 1170402 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B1756001 : Blo 1170402 1756001 := bstep (se 2 (by rfl) ⟨658500, by rfl⟩ : syracuseStep 1756001 = 1317001) B1317001
theorem B10832753 : Blo 1170402 10832753 := bstep (se 2 (by rfl) ⟨4062282, by rfl⟩ : syracuseStep 10832753 = 8124565) B8124565
theorem B1756019 : Blo 1170402 1756019 := bstep (se 1 (by rfl) ⟨1317014, by rfl⟩ : syracuseStep 1756019 = 2634029) B2634029
theorem B1977203 : Blo 1170402 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B6761357 : Blo 1170402 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B18025357 : Blo 1170402 18025357 := bstep (se 3 (by rfl) ⟨3379754, by rfl⟩ : syracuseStep 18025357 = 6759509) B6759509
theorem B13519757 : Blo 1170402 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B1756049 : Blo 1170402 1756049 := bstep (se 2 (by rfl) ⟨658518, by rfl⟩ : syracuseStep 1756049 = 1317037) B1317037
theorem B10005389 : Blo 1170402 10005389 := bstep (se 3 (by rfl) ⟨1876010, by rfl⟩ : syracuseStep 10005389 = 3752021) B3752021
theorem B4451213 : Blo 1170402 4451213 := bstep (se 3 (by rfl) ⟨834602, by rfl⟩ : syracuseStep 4451213 = 1669205) B1669205
theorem B1756067 : Blo 1170402 1756067 := bstep (se 1 (by rfl) ⟨1317050, by rfl⟩ : syracuseStep 1756067 = 2634101) B2634101
theorem B1756097 : Blo 1170402 1756097 := bstep (se 2 (by rfl) ⟨658536, by rfl⟩ : syracuseStep 1756097 = 1317073) B1317073
theorem B1756115 : Blo 1170402 1756115 := bstep (se 1 (by rfl) ⟨1317086, by rfl⟩ : syracuseStep 1756115 = 2634173) B2634173
theorem B1756145 : Blo 1170402 1756145 := bstep (se 2 (by rfl) ⟨658554, by rfl⟩ : syracuseStep 1756145 = 1317109) B1317109
theorem B1977331 : Blo 1170402 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B1756163 : Blo 1170402 1756163 := bstep (se 1 (by rfl) ⟨1317122, by rfl⟩ : syracuseStep 1756163 = 2634245) B2634245
theorem B1756193 : Blo 1170402 1756193 := bstep (se 2 (by rfl) ⟨658572, by rfl⟩ : syracuseStep 1756193 = 1317145) B1317145
theorem B2223139 : Blo 1170402 2223139 := bstep (se 1 (by rfl) ⟨1667354, by rfl⟩ : syracuseStep 2223139 = 3334709) B3334709
theorem B3951665 : Blo 1170402 3951665 := bstep (se 2 (by rfl) ⟨1481874, by rfl⟩ : syracuseStep 3951665 = 2963749) B2963749
theorem B1756211 : Blo 1170402 1756211 := bstep (se 1 (by rfl) ⟨1317158, by rfl⟩ : syracuseStep 1756211 = 2634317) B2634317
theorem B1756241 : Blo 1170402 1756241 := bstep (se 2 (by rfl) ⟨658590, by rfl⟩ : syracuseStep 1756241 = 1317181) B1317181
theorem B1756259 : Blo 1170402 1756259 := bstep (se 1 (by rfl) ⟨1317194, by rfl⟩ : syracuseStep 1756259 = 2634389) B2634389
theorem B1756289 : Blo 1170402 1756289 := bstep (se 2 (by rfl) ⟨658608, by rfl⟩ : syracuseStep 1756289 = 1317217) B1317217
theorem B1977473 : Blo 1170402 1977473 := bstep (se 2 (by rfl) ⟨741552, by rfl⟩ : syracuseStep 1977473 = 1483105) B1483105
theorem B5786765 : Blo 1170402 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B5934221 : Blo 1170402 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B1756307 : Blo 1170402 1756307 := bstep (se 1 (by rfl) ⟨1317230, by rfl⟩ : syracuseStep 1756307 = 2634461) B2634461
theorem B1756337 : Blo 1170402 1756337 := bstep (se 2 (by rfl) ⟨658626, by rfl⟩ : syracuseStep 1756337 = 1317253) B1317253
theorem B1756355 : Blo 1170402 1756355 := bstep (se 1 (by rfl) ⟨1317266, by rfl⟩ : syracuseStep 1756355 = 2634533) B2634533
theorem B1756385 : Blo 1170402 1756385 := bstep (se 2 (by rfl) ⟨658644, by rfl⟩ : syracuseStep 1756385 = 1317289) B1317289
theorem B2534627 : Blo 1170402 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B3337453 : Blo 1170402 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B1756403 : Blo 1170402 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B1977601 : Blo 1170402 1977601 := bstep (se 2 (by rfl) ⟨741600, by rfl⟩ : syracuseStep 1977601 = 1483201) B1483201
theorem B2813201 : Blo 1170402 2813201 := bstep (se 2 (by rfl) ⟨1054950, by rfl⟩ : syracuseStep 2813201 = 2109901) B2109901
theorem B1756433 : Blo 1170402 1756433 := bstep (se 2 (by rfl) ⟨658662, by rfl⟩ : syracuseStep 1756433 = 1317325) B1317325
theorem B1756451 : Blo 1170402 1756451 := bstep (se 1 (by rfl) ⟨1317338, by rfl⟩ : syracuseStep 1756451 = 2634677) B2634677
theorem B1977635 : Blo 1170402 1977635 := bstep (se 1 (by rfl) ⟨1483226, by rfl⟩ : syracuseStep 1977635 = 2966453) B2966453
theorem B1756481 : Blo 1170402 1756481 := bstep (se 2 (by rfl) ⟨658680, by rfl⟩ : syracuseStep 1756481 = 1317361) B1317361
theorem B1756499 : Blo 1170402 1756499 := bstep (se 1 (by rfl) ⟨1317374, by rfl⟩ : syracuseStep 1756499 = 2634749) B2634749
theorem B5000561 : Blo 1170402 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B1756529 : Blo 1170402 1756529 := bstep (se 2 (by rfl) ⟨658698, by rfl⟩ : syracuseStep 1756529 = 1317397) B1317397
theorem B1756547 : Blo 1170402 1756547 := bstep (se 1 (by rfl) ⟨1317410, by rfl⟩ : syracuseStep 1756547 = 2634821) B2634821
theorem B1756577 : Blo 1170402 1756577 := bstep (se 2 (by rfl) ⟨658716, by rfl⟩ : syracuseStep 1756577 = 1317433) B1317433
theorem B1977763 : Blo 1170402 1977763 := bstep (se 1 (by rfl) ⟨1483322, by rfl⟩ : syracuseStep 1977763 = 2966645) B2966645
theorem B2502065 : Blo 1170402 2502065 := bstep (se 2 (by rfl) ⟨938274, by rfl⟩ : syracuseStep 2502065 = 1876549) B1876549
theorem B1756595 : Blo 1170402 1756595 := bstep (se 1 (by rfl) ⟨1317446, by rfl⟩ : syracuseStep 1756595 = 2634893) B2634893
theorem B2502083 : Blo 1170402 2502083 := bstep (se 1 (by rfl) ⟨1876562, by rfl⟩ : syracuseStep 2502083 = 3753125) B3753125
theorem B1691075 : Blo 1170402 1691075 := bstep (se 1 (by rfl) ⟨1268306, by rfl⟩ : syracuseStep 1691075 = 2536613) B2536613
theorem B1756625 : Blo 1170402 1756625 := bstep (se 2 (by rfl) ⟨658734, by rfl⟩ : syracuseStep 1756625 = 1317469) B1317469
theorem B3337681 : Blo 1170402 3337681 := bstep (se 2 (by rfl) ⟨1251630, by rfl⟩ : syracuseStep 3337681 = 2503261) B2503261
theorem B1756643 : Blo 1170402 1756643 := bstep (se 1 (by rfl) ⟨1317482, by rfl⟩ : syracuseStep 1756643 = 2634965) B2634965
theorem B2223587 : Blo 1170402 2223587 := bstep (se 1 (by rfl) ⟨1667690, by rfl⟩ : syracuseStep 2223587 = 3335381) B3335381
theorem B1756673 : Blo 1170402 1756673 := bstep (se 2 (by rfl) ⟨658752, by rfl⟩ : syracuseStep 1756673 = 1317505) B1317505
theorem B1756691 : Blo 1170402 1756691 := bstep (se 1 (by rfl) ⟨1317518, by rfl⟩ : syracuseStep 1756691 = 2635037) B2635037
theorem B1756721 : Blo 1170402 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B1977905 : Blo 1170402 1977905 := bstep (se 2 (by rfl) ⟨741714, by rfl⟩ : syracuseStep 1977905 = 1483429) B1483429
theorem B1781299 : Blo 1170402 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B1756739 : Blo 1170402 1756739 := bstep (se 1 (by rfl) ⟨1317554, by rfl⟩ : syracuseStep 1756739 = 2635109) B2635109
theorem B3952205 : Blo 1170402 3952205 := bstep (se 3 (by rfl) ⟨741038, by rfl⟩ : syracuseStep 3952205 = 1482077) B1482077
theorem B1756769 : Blo 1170402 1756769 := bstep (se 2 (by rfl) ⟨658788, by rfl⟩ : syracuseStep 1756769 = 1317577) B1317577
theorem B3337841 : Blo 1170402 3337841 := bstep (se 2 (by rfl) ⟨1251690, by rfl⟩ : syracuseStep 3337841 = 2503381) B2503381
theorem B1756787 : Blo 1170402 1756787 := bstep (se 1 (by rfl) ⟨1317590, by rfl⟩ : syracuseStep 1756787 = 2635181) B2635181
theorem B3952259 : Blo 1170402 3952259 := bstep (se 1 (by rfl) ⟨2964194, by rfl⟩ : syracuseStep 3952259 = 5928389) B5928389
theorem B7499405 : Blo 1170402 7499405 := bstep (se 3 (by rfl) ⟨1406138, by rfl⟩ : syracuseStep 7499405 = 2812277) B2812277
theorem B1756817 : Blo 1170402 1756817 := bstep (se 2 (by rfl) ⟨658806, by rfl⟩ : syracuseStep 1756817 = 1317613) B1317613
theorem B1756835 : Blo 1170402 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B1978033 : Blo 1170402 1978033 := bstep (se 2 (by rfl) ⟨741762, by rfl⟩ : syracuseStep 1978033 = 1483525) B1483525
theorem B1756865 : Blo 1170402 1756865 := bstep (se 2 (by rfl) ⟨658824, by rfl⟩ : syracuseStep 1756865 = 1317649) B1317649
theorem B1756883 : Blo 1170402 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B1978067 : Blo 1170402 1978067 := bstep (se 1 (by rfl) ⟨1483550, by rfl⟩ : syracuseStep 1978067 = 2967101) B2967101
theorem B3337955 : Blo 1170402 3337955 := bstep (se 1 (by rfl) ⟨2503466, by rfl⟩ : syracuseStep 3337955 = 5006933) B5006933
theorem B1756913 : Blo 1170402 1756913 := bstep (se 2 (by rfl) ⟨658842, by rfl⟩ : syracuseStep 1756913 = 1317685) B1317685
theorem B1756931 : Blo 1170402 1756931 := bstep (se 1 (by rfl) ⟨1317698, by rfl⟩ : syracuseStep 1756931 = 2635397) B2635397
theorem B2223875 : Blo 1170402 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B2633489 : Blo 1170402 2633489 := bstep (se 2 (by rfl) ⟨987558, by rfl⟩ : syracuseStep 2633489 = 1975117) B1975117
theorem B1756961 : Blo 1170402 1756961 := bstep (se 2 (by rfl) ⟨658860, by rfl⟩ : syracuseStep 1756961 = 1317721) B1317721
theorem B2633507 : Blo 1170402 2633507 := bstep (se 1 (by rfl) ⟨1975130, by rfl⟩ : syracuseStep 2633507 = 3950261) B3950261
theorem B1756979 : Blo 1170402 1756979 := bstep (se 1 (by rfl) ⟨1317734, by rfl⟩ : syracuseStep 1756979 = 2635469) B2635469
theorem B1757009 : Blo 1170402 1757009 := bstep (se 2 (by rfl) ⟨658878, by rfl⟩ : syracuseStep 1757009 = 1317757) B1317757
theorem B1978195 : Blo 1170402 1978195 := bstep (se 1 (by rfl) ⟨1483646, by rfl⟩ : syracuseStep 1978195 = 2967293) B2967293
theorem B1757027 : Blo 1170402 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B5926769 : Blo 1170402 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B1757057 : Blo 1170402 1757057 := bstep (se 2 (by rfl) ⟨658896, by rfl⟩ : syracuseStep 1757057 = 1317793) B1317793
theorem B3952529 : Blo 1170402 3952529 := bstep (se 2 (by rfl) ⟨1482198, by rfl⟩ : syracuseStep 3952529 = 2964397) B2964397
theorem B1757075 : Blo 1170402 1757075 := bstep (se 1 (by rfl) ⟨1317806, by rfl⟩ : syracuseStep 1757075 = 2635613) B2635613
theorem B1757105 : Blo 1170402 1757105 := bstep (se 2 (by rfl) ⟨658914, by rfl⟩ : syracuseStep 1757105 = 1317829) B1317829
theorem B7507889 : Blo 1170402 7507889 := bstep (se 2 (by rfl) ⟨2815458, by rfl⟩ : syracuseStep 7507889 = 5630917) B5630917
theorem B1953715 : Blo 1170402 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B1757123 : Blo 1170402 1757123 := bstep (se 1 (by rfl) ⟨1317842, by rfl⟩ : syracuseStep 1757123 = 2635685) B2635685
theorem B1757153 : Blo 1170402 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B1978337 : Blo 1170402 1978337 := bstep (se 2 (by rfl) ⟨741876, by rfl⟩ : syracuseStep 1978337 = 1483753) B1483753
theorem B1757171 : Blo 1170402 1757171 := bstep (se 1 (by rfl) ⟨1317878, by rfl⟩ : syracuseStep 1757171 = 2635757) B2635757
theorem B1757201 : Blo 1170402 1757201 := bstep (se 2 (by rfl) ⟨658950, by rfl⟩ : syracuseStep 1757201 = 1317901) B1317901
theorem B1757219 : Blo 1170402 1757219 := bstep (se 1 (by rfl) ⟨1317914, by rfl⟩ : syracuseStep 1757219 = 2635829) B2635829
theorem B2633777 : Blo 1170402 2633777 := bstep (se 2 (by rfl) ⟨987666, by rfl⟩ : syracuseStep 2633777 = 1975333) B1975333
theorem B1757249 : Blo 1170402 1757249 := bstep (se 2 (by rfl) ⟨658968, by rfl⟩ : syracuseStep 1757249 = 1317937) B1317937
theorem B2633795 : Blo 1170402 2633795 := bstep (se 1 (by rfl) ⟨1975346, by rfl⟩ : syracuseStep 2633795 = 3950693) B3950693
theorem B1667155 : Blo 1170402 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B1757267 : Blo 1170402 1757267 := bstep (se 1 (by rfl) ⟨1317950, by rfl⟩ : syracuseStep 1757267 = 2635901) B2635901
theorem B1757297 : Blo 1170402 1757297 := bstep (se 2 (by rfl) ⟨658986, by rfl⟩ : syracuseStep 1757297 = 1317973) B1317973
theorem B1757315 : Blo 1170402 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1757345 : Blo 1170402 1757345 := bstep (se 2 (by rfl) ⟨659004, by rfl⟩ : syracuseStep 1757345 = 1318009) B1318009
theorem B1757363 : Blo 1170402 1757363 := bstep (se 1 (by rfl) ⟨1318022, by rfl⟩ : syracuseStep 1757363 = 2636045) B2636045
theorem B1757393 : Blo 1170402 1757393 := bstep (se 2 (by rfl) ⟨659022, by rfl⟩ : syracuseStep 1757393 = 1318045) B1318045
theorem B1757411 : Blo 1170402 1757411 := bstep (se 1 (by rfl) ⟨1318058, by rfl⟩ : syracuseStep 1757411 = 2636117) B2636117
theorem B1757441 : Blo 1170402 1757441 := bstep (se 2 (by rfl) ⟨659040, by rfl⟩ : syracuseStep 1757441 = 1318081) B1318081
theorem B1757459 : Blo 1170402 1757459 := bstep (se 1 (by rfl) ⟨1318094, by rfl⟩ : syracuseStep 1757459 = 2636189) B2636189
theorem B3559715 : Blo 1170402 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B1757489 : Blo 1170402 1757489 := bstep (se 2 (by rfl) ⟨659058, by rfl⟩ : syracuseStep 1757489 = 1318117) B1318117
theorem B1757507 : Blo 1170402 1757507 := bstep (se 1 (by rfl) ⟨1318130, by rfl⟩ : syracuseStep 1757507 = 2636261) B2636261
theorem B2634065 : Blo 1170402 2634065 := bstep (se 2 (by rfl) ⟨987774, by rfl⟩ : syracuseStep 2634065 = 1975549) B1975549
theorem B1757537 : Blo 1170402 1757537 := bstep (se 2 (by rfl) ⟨659076, by rfl⟩ : syracuseStep 1757537 = 1318153) B1318153
theorem B2634083 : Blo 1170402 2634083 := bstep (se 1 (by rfl) ⟨1975562, by rfl⟩ : syracuseStep 2634083 = 3951125) B3951125
theorem B1757555 : Blo 1170402 1757555 := bstep (se 1 (by rfl) ⟨1318166, by rfl⟩ : syracuseStep 1757555 = 2636333) B2636333
theorem B1782131 : Blo 1170402 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1757585 : Blo 1170402 1757585 := bstep (se 2 (by rfl) ⟨659094, by rfl⟩ : syracuseStep 1757585 = 1318189) B1318189
theorem B1757603 : Blo 1170402 1757603 := bstep (se 1 (by rfl) ⟨1318202, by rfl⟩ : syracuseStep 1757603 = 2636405) B2636405
theorem B3953069 : Blo 1170402 3953069 := bstep (se 3 (by rfl) ⟨741200, by rfl⟩ : syracuseStep 3953069 = 1482401) B1482401
theorem B1757633 : Blo 1170402 1757633 := bstep (se 2 (by rfl) ⟨659112, by rfl⟩ : syracuseStep 1757633 = 1318225) B1318225
theorem B8556997 : Blo 1170402 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B1757651 : Blo 1170402 1757651 := bstep (se 1 (by rfl) ⟨1318238, by rfl⟩ : syracuseStep 1757651 = 2636477) B2636477
theorem B3953123 : Blo 1170402 3953123 := bstep (se 1 (by rfl) ⟨2964842, by rfl⟩ : syracuseStep 3953123 = 5929685) B5929685
theorem B1757681 : Blo 1170402 1757681 := bstep (se 2 (by rfl) ⟨659130, by rfl⟩ : syracuseStep 1757681 = 1318261) B1318261
theorem B1757699 : Blo 1170402 1757699 := bstep (se 1 (by rfl) ⟨1318274, by rfl⟩ : syracuseStep 1757699 = 2636549) B2636549
theorem B6672901 : Blo 1170402 6672901 := bstep (se 4 (by rfl) ⟨625584, by rfl⟩ : syracuseStep 6672901 = 1251169) B1251169
theorem B1757729 : Blo 1170402 1757729 := bstep (se 2 (by rfl) ⟨659148, by rfl⟩ : syracuseStep 1757729 = 1318297) B1318297
theorem B1667633 : Blo 1170402 1667633 := bstep (se 2 (by rfl) ⟨625362, by rfl⟩ : syracuseStep 1667633 = 1250725) B1250725
theorem B1757747 : Blo 1170402 1757747 := bstep (se 1 (by rfl) ⟨1318310, by rfl⟩ : syracuseStep 1757747 = 2636621) B2636621
theorem B1757777 : Blo 1170402 1757777 := bstep (se 2 (by rfl) ⟨659166, by rfl⟩ : syracuseStep 1757777 = 1318333) B1318333
theorem B2110051 : Blo 1170402 2110051 := bstep (se 1 (by rfl) ⟨1582538, by rfl⟩ : syracuseStep 2110051 = 3165077) B3165077
theorem B1757795 : Blo 1170402 1757795 := bstep (se 1 (by rfl) ⟨1318346, by rfl⟩ : syracuseStep 1757795 = 2636693) B2636693
theorem B2634353 : Blo 1170402 2634353 := bstep (se 2 (by rfl) ⟨987882, by rfl⟩ : syracuseStep 2634353 = 1975765) B1975765
theorem B1757825 : Blo 1170402 1757825 := bstep (se 2 (by rfl) ⟨659184, by rfl⟩ : syracuseStep 1757825 = 1318369) B1318369
theorem B2634371 : Blo 1170402 2634371 := bstep (se 1 (by rfl) ⟨1975778, by rfl⟩ : syracuseStep 2634371 = 3951557) B3951557
theorem B1249939 : Blo 1170402 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1757843 : Blo 1170402 1757843 := bstep (se 1 (by rfl) ⟨1318382, by rfl⟩ : syracuseStep 1757843 = 2636765) B2636765
theorem B1667747 : Blo 1170402 1667747 := bstep (se 1 (by rfl) ⟨1250810, by rfl⟩ : syracuseStep 1667747 = 2501621) B2501621
theorem B1757873 : Blo 1170402 1757873 := bstep (se 2 (by rfl) ⟨659202, by rfl⟩ : syracuseStep 1757873 = 1318405) B1318405
theorem B2224817 : Blo 1170402 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B1757891 : Blo 1170402 1757891 := bstep (se 1 (by rfl) ⟨1318418, by rfl⟩ : syracuseStep 1757891 = 2636837) B2636837
theorem B1757921 : Blo 1170402 1757921 := bstep (se 2 (by rfl) ⟨659220, by rfl⟩ : syracuseStep 1757921 = 1318441) B1318441
theorem B3953393 : Blo 1170402 3953393 := bstep (se 2 (by rfl) ⟨1482522, by rfl⟩ : syracuseStep 3953393 = 2965045) B2965045
theorem B1667827 : Blo 1170402 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B1757939 : Blo 1170402 1757939 := bstep (se 1 (by rfl) ⟨1318454, by rfl⟩ : syracuseStep 1757939 = 2636909) B2636909
theorem B1504003 : Blo 1170402 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B1757969 : Blo 1170402 1757969 := bstep (se 2 (by rfl) ⟨659238, by rfl⟩ : syracuseStep 1757969 = 1318477) B1318477
theorem B1757987 : Blo 1170402 1757987 := bstep (se 1 (by rfl) ⟨1318490, by rfl⟩ : syracuseStep 1757987 = 2636981) B2636981
theorem B1758017 : Blo 1170402 1758017 := bstep (se 2 (by rfl) ⟨659256, by rfl⟩ : syracuseStep 1758017 = 1318513) B1318513
theorem B1758035 : Blo 1170402 1758035 := bstep (se 1 (by rfl) ⟨1318526, by rfl⟩ : syracuseStep 1758035 = 2637053) B2637053
theorem B1758065 : Blo 1170402 1758065 := bstep (se 2 (by rfl) ⟨659274, by rfl⟩ : syracuseStep 1758065 = 1318549) B1318549
theorem B1758083 : Blo 1170402 1758083 := bstep (se 1 (by rfl) ⟨1318562, by rfl⟩ : syracuseStep 1758083 = 2637125) B2637125
theorem B2634641 : Blo 1170402 2634641 := bstep (se 2 (by rfl) ⟨987990, by rfl⟩ : syracuseStep 2634641 = 1975981) B1975981
theorem B1758113 : Blo 1170402 1758113 := bstep (se 2 (by rfl) ⟨659292, by rfl⟩ : syracuseStep 1758113 = 1318585) B1318585
theorem B2634659 : Blo 1170402 2634659 := bstep (se 1 (by rfl) ⟨1975994, by rfl⟩ : syracuseStep 2634659 = 3951989) B3951989
theorem B3167153 : Blo 1170402 3167153 := bstep (se 2 (by rfl) ⟨1187682, by rfl⟩ : syracuseStep 3167153 = 2375365) B2375365
theorem B1758131 : Blo 1170402 1758131 := bstep (se 1 (by rfl) ⟨1318598, by rfl⟩ : syracuseStep 1758131 = 2637197) B2637197
theorem B1758161 : Blo 1170402 1758161 := bstep (se 2 (by rfl) ⟨659310, by rfl⟩ : syracuseStep 1758161 = 1318621) B1318621
theorem B7508963 : Blo 1170402 7508963 := bstep (se 1 (by rfl) ⟨5631722, by rfl⟩ : syracuseStep 7508963 = 11263445) B11263445
theorem B1758179 : Blo 1170402 1758179 := bstep (se 1 (by rfl) ⟨1318634, by rfl⟩ : syracuseStep 1758179 = 2637269) B2637269
theorem B1758209 : Blo 1170402 1758209 := bstep (se 2 (by rfl) ⟨659328, by rfl⟩ : syracuseStep 1758209 = 1318657) B1318657
theorem B1758227 : Blo 1170402 1758227 := bstep (se 1 (by rfl) ⟨1318670, by rfl⟩ : syracuseStep 1758227 = 2637341) B2637341
theorem B1758257 : Blo 1170402 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B1758275 : Blo 1170402 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1758305 : Blo 1170402 1758305 := bstep (se 2 (by rfl) ⟨659364, by rfl⟩ : syracuseStep 1758305 = 1318729) B1318729
theorem B12661859 : Blo 1170402 12661859 := bstep (se 1 (by rfl) ⟨9496394, by rfl⟩ : syracuseStep 12661859 = 18992789) B18992789
theorem B4813937 : Blo 1170402 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B1758323 : Blo 1170402 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B5633165 : Blo 1170402 5633165 := bstep (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) B2112437
theorem B1758353 : Blo 1170402 1758353 := bstep (se 2 (by rfl) ⟨659382, by rfl⟩ : syracuseStep 1758353 = 1318765) B1318765
theorem B2962595 : Blo 1170402 2962595 := bstep (se 1 (by rfl) ⟨2221946, by rfl⟩ : syracuseStep 2962595 = 4443893) B4443893
theorem B1758371 : Blo 1170402 1758371 := bstep (se 1 (by rfl) ⟨1318778, by rfl⟩ : syracuseStep 1758371 = 2637557) B2637557
theorem B2634929 : Blo 1170402 2634929 := bstep (se 2 (by rfl) ⟨988098, by rfl⟩ : syracuseStep 2634929 = 1976197) B1976197
theorem B1758401 : Blo 1170402 1758401 := bstep (se 2 (by rfl) ⟨659400, by rfl⟩ : syracuseStep 1758401 = 1318801) B1318801
theorem B2634947 : Blo 1170402 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B1758419 : Blo 1170402 1758419 := bstep (se 1 (by rfl) ⟨1318814, by rfl⟩ : syracuseStep 1758419 = 2637629) B2637629
theorem B1758449 : Blo 1170402 1758449 := bstep (se 2 (by rfl) ⟨659418, by rfl⟩ : syracuseStep 1758449 = 1318837) B1318837
theorem B1758467 : Blo 1170402 1758467 := bstep (se 1 (by rfl) ⟨1318850, by rfl⟩ : syracuseStep 1758467 = 2637701) B2637701
theorem B3953933 : Blo 1170402 3953933 := bstep (se 3 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 3953933 = 1482725) B1482725
theorem B1668385 : Blo 1170402 1668385 := bstep (se 2 (by rfl) ⟨625644, by rfl⟩ : syracuseStep 1668385 = 1251289) B1251289
theorem B1758497 : Blo 1170402 1758497 := bstep (se 2 (by rfl) ⟨659436, by rfl⟩ : syracuseStep 1758497 = 1318873) B1318873
theorem B5928227 : Blo 1170402 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B1758515 : Blo 1170402 1758515 := bstep (se 1 (by rfl) ⟨1318886, by rfl⟩ : syracuseStep 1758515 = 2637773) B2637773
theorem B3953987 : Blo 1170402 3953987 := bstep (se 1 (by rfl) ⟨2965490, by rfl⟩ : syracuseStep 3953987 = 5930981) B5930981
theorem B1758545 : Blo 1170402 1758545 := bstep (se 2 (by rfl) ⟨659454, by rfl⟩ : syracuseStep 1758545 = 1318909) B1318909
theorem B1758563 : Blo 1170402 1758563 := bstep (se 1 (by rfl) ⟨1318922, by rfl⟩ : syracuseStep 1758563 = 2637845) B2637845
theorem B1758593 : Blo 1170402 1758593 := bstep (se 2 (by rfl) ⟨659472, by rfl⟩ : syracuseStep 1758593 = 1318945) B1318945
theorem B2635217 : Blo 1170402 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B2635235 : Blo 1170402 2635235 := bstep (se 1 (by rfl) ⟨1976426, by rfl⟩ : syracuseStep 2635235 = 3952853) B3952853
theorem B2225713 : Blo 1170402 2225713 := bstep (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) B1669285
theorem B3954257 : Blo 1170402 3954257 := bstep (se 2 (by rfl) ⟨1482846, by rfl⟩ : syracuseStep 3954257 = 2965693) B2965693
theorem B1250947 : Blo 1170402 1250947 := bstep (se 1 (by rfl) ⟨938210, by rfl⟩ : syracuseStep 1250947 = 1876421) B1876421
theorem B4445837 : Blo 1170402 4445837 := bstep (se 3 (by rfl) ⟨833594, by rfl⟩ : syracuseStep 4445837 = 1667189) B1667189
theorem B2004625 : Blo 1170402 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B3806929 : Blo 1170402 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B2635505 : Blo 1170402 2635505 := bstep (se 2 (by rfl) ⟨988314, by rfl⟩ : syracuseStep 2635505 = 1976629) B1976629
theorem B2635523 : Blo 1170402 2635523 := bstep (se 1 (by rfl) ⟨1976642, by rfl⟩ : syracuseStep 2635523 = 3953285) B3953285
theorem B2815843 : Blo 1170402 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B25335665 : Blo 1170402 25335665 := bstep (se 2 (by rfl) ⟨9500874, by rfl⟩ : syracuseStep 25335665 = 19001749) B19001749
theorem B1316803 : Blo 1170402 1316803 := bstep (se 1 (by rfl) ⟨987602, by rfl⟩ : syracuseStep 1316803 = 1975205) B1975205
theorem B1669091 : Blo 1170402 1669091 := bstep (se 1 (by rfl) ⟨1251818, by rfl⟩ : syracuseStep 1669091 = 2503637) B2503637
theorem B3381233 : Blo 1170402 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B3856369 : Blo 1170402 3856369 := bstep (se 2 (by rfl) ⟨1446138, by rfl⟩ : syracuseStep 3856369 = 2892277) B2892277
theorem B2635793 : Blo 1170402 2635793 := bstep (se 2 (by rfl) ⟨988422, by rfl⟩ : syracuseStep 2635793 = 1976845) B1976845
theorem B2635811 : Blo 1170402 2635811 := bstep (se 1 (by rfl) ⟨1976858, by rfl⟩ : syracuseStep 2635811 = 3953717) B3953717
theorem B3004465 : Blo 1170402 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B5929037 : Blo 1170402 5929037 := bstep (se 3 (by rfl) ⟨1111694, by rfl⟩ : syracuseStep 5929037 = 2223389) B2223389
theorem B2963537 : Blo 1170402 2963537 := bstep (se 2 (by rfl) ⟨1111326, by rfl⟩ : syracuseStep 2963537 = 2222653) B2222653
theorem B1316947 : Blo 1170402 1316947 := bstep (se 1 (by rfl) ⟨987710, by rfl⟩ : syracuseStep 1316947 = 1975421) B1975421
theorem B3954797 : Blo 1170402 3954797 := bstep (se 3 (by rfl) ⟨741524, by rfl⟩ : syracuseStep 3954797 = 1483049) B1483049
theorem B2963587 : Blo 1170402 2963587 := bstep (se 1 (by rfl) ⟨2222690, by rfl⟩ : syracuseStep 2963587 = 4445381) B4445381
theorem B3954851 : Blo 1170402 3954851 := bstep (se 1 (by rfl) ⟨2966138, by rfl⟩ : syracuseStep 3954851 = 5932277) B5932277
theorem B1317091 : Blo 1170402 1317091 := bstep (se 1 (by rfl) ⟨987818, by rfl⟩ : syracuseStep 1317091 = 1975637) B1975637
theorem B3168515 : Blo 1170402 3168515 := bstep (se 1 (by rfl) ⟨2376386, by rfl⟩ : syracuseStep 3168515 = 4752773) B4752773
theorem B2963729 : Blo 1170402 2963729 := bstep (se 2 (by rfl) ⟨1111398, by rfl⟩ : syracuseStep 2963729 = 2222797) B2222797
theorem B2373905 : Blo 1170402 2373905 := bstep (se 2 (by rfl) ⟨890214, by rfl⟩ : syracuseStep 2373905 = 1780429) B1780429
theorem B2636081 : Blo 1170402 2636081 := bstep (se 2 (by rfl) ⟨988530, by rfl⟩ : syracuseStep 2636081 = 1977061) B1977061
theorem B2636099 : Blo 1170402 2636099 := bstep (se 1 (by rfl) ⟨1977074, by rfl⟩ : syracuseStep 2636099 = 3954149) B3954149
theorem B1407331 : Blo 1170402 1407331 := bstep (se 1 (by rfl) ⟨1055498, by rfl⟩ : syracuseStep 1407331 = 2110997) B2110997
theorem B1317235 : Blo 1170402 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B3955121 : Blo 1170402 3955121 := bstep (se 2 (by rfl) ⟨1483170, by rfl⟩ : syracuseStep 3955121 = 2966341) B2966341
theorem B8444357 : Blo 1170402 8444357 := bstep (se 4 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 8444357 = 1583317) B1583317
theorem B6674885 : Blo 1170402 6674885 := bstep (se 4 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 6674885 = 1251541) B1251541
theorem B1317379 : Blo 1170402 1317379 := bstep (se 1 (by rfl) ⟨988034, by rfl⟩ : syracuseStep 1317379 = 1976069) B1976069
theorem B1407523 : Blo 1170402 1407523 := bstep (se 1 (by rfl) ⟨1055642, by rfl⟩ : syracuseStep 1407523 = 2111285) B2111285
theorem B5626417 : Blo 1170402 5626417 := bstep (se 2 (by rfl) ⟨2109906, by rfl⟩ : syracuseStep 5626417 = 4219813) B4219813
theorem B2636369 : Blo 1170402 2636369 := bstep (se 2 (by rfl) ⟨988638, by rfl⟩ : syracuseStep 2636369 = 1977277) B1977277
theorem B2636387 : Blo 1170402 2636387 := bstep (se 1 (by rfl) ⟨1977290, by rfl⟩ : syracuseStep 2636387 = 3954581) B3954581
theorem B3005041 : Blo 1170402 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B1251955 : Blo 1170402 1251955 := bstep (se 1 (by rfl) ⟨938966, by rfl⟩ : syracuseStep 1251955 = 1877933) B1877933
theorem B1317523 : Blo 1170402 1317523 := bstep (se 1 (by rfl) ⟨988142, by rfl⟩ : syracuseStep 1317523 = 1976285) B1976285
theorem B6421169 : Blo 1170402 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B2816689 : Blo 1170402 2816689 := bstep (se 2 (by rfl) ⟨1056258, by rfl⟩ : syracuseStep 2816689 = 2112517) B2112517
theorem B6331085 : Blo 1170402 6331085 := bstep (se 3 (by rfl) ⟨1187078, by rfl⟩ : syracuseStep 6331085 = 2374157) B2374157
theorem B3750637 : Blo 1170402 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B1317667 : Blo 1170402 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B1874801 : Blo 1170402 1874801 := bstep (se 2 (by rfl) ⟨703050, by rfl⟩ : syracuseStep 1874801 = 1406101) B1406101
theorem B2636657 : Blo 1170402 2636657 := bstep (se 2 (by rfl) ⟨988746, by rfl⟩ : syracuseStep 2636657 = 1977493) B1977493
theorem B2636675 : Blo 1170402 2636675 := bstep (se 1 (by rfl) ⟨1977506, by rfl⟩ : syracuseStep 2636675 = 3955013) B3955013
theorem B22502285 : Blo 1170402 22502285 := bstep (se 3 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 22502285 = 8438357) B8438357
theorem B6331277 : Blo 1170402 6331277 := bstep (se 3 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 6331277 = 2374229) B2374229
theorem B1317811 : Blo 1170402 1317811 := bstep (se 1 (by rfl) ⟨988358, by rfl⟩ : syracuseStep 1317811 = 1976717) B1976717
theorem B3955661 : Blo 1170402 3955661 := bstep (se 3 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 3955661 = 1483373) B1483373
theorem B1170403 : Blo 1170402 1170403 := bstep (se 1 (by rfl) ⟨877802, by rfl⟩ : syracuseStep 1170403 = 1755605) B1755605
theorem B10001393 : Blo 1170402 10001393 := bstep (se 2 (by rfl) ⟨3750522, by rfl⟩ : syracuseStep 10001393 = 7501045) B7501045
theorem B1170419 : Blo 1170402 1170419 := bstep (se 1 (by rfl) ⟨877814, by rfl⟩ : syracuseStep 1170419 = 1755629) B1755629
theorem B1170435 : Blo 1170402 1170435 := bstep (se 1 (by rfl) ⟨877826, by rfl⟩ : syracuseStep 1170435 = 1755653) B1755653
theorem B3955715 : Blo 1170402 3955715 := bstep (se 1 (by rfl) ⟨2966786, by rfl⟩ : syracuseStep 3955715 = 5933573) B5933573
theorem B5004301 : Blo 1170402 5004301 := bstep (se 3 (by rfl) ⟨938306, by rfl⟩ : syracuseStep 5004301 = 1876613) B1876613
theorem B1170451 : Blo 1170402 1170451 := bstep (se 1 (by rfl) ⟨877838, by rfl⟩ : syracuseStep 1170451 = 1755677) B1755677
theorem B30063637 : Blo 1170402 30063637 := bstep (se 6 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 30063637 = 1409233) B1409233
theorem B1170467 : Blo 1170402 1170467 := bstep (se 1 (by rfl) ⟨877850, by rfl⟩ : syracuseStep 1170467 = 1755701) B1755701
theorem B1170483 : Blo 1170402 1170483 := bstep (se 1 (by rfl) ⟨877862, by rfl⟩ : syracuseStep 1170483 = 1755725) B1755725
theorem B1170499 : Blo 1170402 1170499 := bstep (se 1 (by rfl) ⟨877874, by rfl⟩ : syracuseStep 1170499 = 1755749) B1755749
theorem B1317955 : Blo 1170402 1317955 := bstep (se 1 (by rfl) ⟨988466, by rfl⟩ : syracuseStep 1317955 = 1976933) B1976933
theorem B1170515 : Blo 1170402 1170515 := bstep (se 1 (by rfl) ⟨877886, by rfl⟩ : syracuseStep 1170515 = 1755773) B1755773
theorem B1170531 : Blo 1170402 1170531 := bstep (se 1 (by rfl) ⟨877898, by rfl⟩ : syracuseStep 1170531 = 1755797) B1755797
theorem B1170547 : Blo 1170402 1170547 := bstep (se 1 (by rfl) ⟨877910, by rfl⟩ : syracuseStep 1170547 = 1755821) B1755821
theorem B3333251 : Blo 1170402 3333251 := bstep (se 1 (by rfl) ⟨2499938, by rfl⟩ : syracuseStep 3333251 = 4999877) B4999877
theorem B1170563 : Blo 1170402 1170563 := bstep (se 1 (by rfl) ⟨877922, by rfl⟩ : syracuseStep 1170563 = 1755845) B1755845
theorem B2636945 : Blo 1170402 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B1170579 : Blo 1170402 1170579 := bstep (se 1 (by rfl) ⟨877934, by rfl⟩ : syracuseStep 1170579 = 1755869) B1755869
theorem B1170595 : Blo 1170402 1170595 := bstep (se 1 (by rfl) ⟨877946, by rfl⟩ : syracuseStep 1170595 = 1755893) B1755893
theorem B2636963 : Blo 1170402 2636963 := bstep (se 1 (by rfl) ⟨1977722, by rfl⟩ : syracuseStep 2636963 = 3955445) B3955445
theorem B1170611 : Blo 1170402 1170611 := bstep (se 1 (by rfl) ⟨877958, by rfl⟩ : syracuseStep 1170611 = 1755917) B1755917
theorem B1170627 : Blo 1170402 1170627 := bstep (se 1 (by rfl) ⟨877970, by rfl⟩ : syracuseStep 1170627 = 1755941) B1755941
theorem B1170643 : Blo 1170402 1170643 := bstep (se 1 (by rfl) ⟨877982, by rfl⟩ : syracuseStep 1170643 = 1755965) B1755965
theorem B1318099 : Blo 1170402 1318099 := bstep (se 1 (by rfl) ⟨988574, by rfl⟩ : syracuseStep 1318099 = 1977149) B1977149
theorem B1170659 : Blo 1170402 1170659 := bstep (se 1 (by rfl) ⟨877994, by rfl⟩ : syracuseStep 1170659 = 1755989) B1755989
theorem B2964721 : Blo 1170402 2964721 := bstep (se 2 (by rfl) ⟨1111770, by rfl⟩ : syracuseStep 2964721 = 2223541) B2223541
theorem B1170675 : Blo 1170402 1170675 := bstep (se 1 (by rfl) ⟨878006, by rfl⟩ : syracuseStep 1170675 = 1756013) B1756013
theorem B1481971 : Blo 1170402 1481971 := bstep (se 1 (by rfl) ⟨1111478, by rfl⟩ : syracuseStep 1481971 = 2222957) B2222957
theorem B1170691 : Blo 1170402 1170691 := bstep (se 1 (by rfl) ⟨878018, by rfl⟩ : syracuseStep 1170691 = 1756037) B1756037
theorem B3955985 : Blo 1170402 3955985 := bstep (se 2 (by rfl) ⟨1483494, by rfl⟩ : syracuseStep 3955985 = 2966989) B2966989
theorem B1170707 : Blo 1170402 1170707 := bstep (se 1 (by rfl) ⟨878030, by rfl⟩ : syracuseStep 1170707 = 1756061) B1756061
theorem B1170723 : Blo 1170402 1170723 := bstep (se 1 (by rfl) ⟨878042, by rfl⟩ : syracuseStep 1170723 = 1756085) B1756085
theorem B1170739 : Blo 1170402 1170739 := bstep (se 1 (by rfl) ⟨878054, by rfl⟩ : syracuseStep 1170739 = 1756109) B1756109
theorem B1170755 : Blo 1170402 1170755 := bstep (se 1 (by rfl) ⟨878066, by rfl⟩ : syracuseStep 1170755 = 1756133) B1756133
theorem B1170771 : Blo 1170402 1170771 := bstep (se 1 (by rfl) ⟨878078, by rfl⟩ : syracuseStep 1170771 = 1756157) B1756157
theorem B1482067 : Blo 1170402 1482067 := bstep (se 1 (by rfl) ⟨1111550, by rfl⟩ : syracuseStep 1482067 = 2223101) B2223101
theorem B1170787 : Blo 1170402 1170787 := bstep (se 1 (by rfl) ⟨878090, by rfl⟩ : syracuseStep 1170787 = 1756181) B1756181
theorem B1318243 : Blo 1170402 1318243 := bstep (se 1 (by rfl) ⟨988682, by rfl⟩ : syracuseStep 1318243 = 1977365) B1977365
theorem B1170803 : Blo 1170402 1170803 := bstep (se 1 (by rfl) ⟨878102, by rfl⟩ : syracuseStep 1170803 = 1756205) B1756205
theorem B2030977 : Blo 1170402 2030977 := bstep (se 2 (by rfl) ⟨761616, by rfl⟩ : syracuseStep 2030977 = 1523233) B1523233
theorem B1170819 : Blo 1170402 1170819 := bstep (se 1 (by rfl) ⟨878114, by rfl⟩ : syracuseStep 1170819 = 1756229) B1756229
theorem B1170835 : Blo 1170402 1170835 := bstep (se 1 (by rfl) ⟨878126, by rfl⟩ : syracuseStep 1170835 = 1756253) B1756253
theorem B1170851 : Blo 1170402 1170851 := bstep (se 1 (by rfl) ⟨878138, by rfl⟩ : syracuseStep 1170851 = 1756277) B1756277
theorem B2637233 : Blo 1170402 2637233 := bstep (se 2 (by rfl) ⟨988962, by rfl⟩ : syracuseStep 2637233 = 1977925) B1977925
theorem B1170867 : Blo 1170402 1170867 := bstep (se 1 (by rfl) ⟨878150, by rfl⟩ : syracuseStep 1170867 = 1756301) B1756301
theorem B1170883 : Blo 1170402 1170883 := bstep (se 1 (by rfl) ⟨878162, by rfl⟩ : syracuseStep 1170883 = 1756325) B1756325
theorem B2637251 : Blo 1170402 2637251 := bstep (se 1 (by rfl) ⟨1977938, by rfl⟩ : syracuseStep 2637251 = 3955877) B3955877
theorem B3333581 : Blo 1170402 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B1170899 : Blo 1170402 1170899 := bstep (se 1 (by rfl) ⟨878174, by rfl⟩ : syracuseStep 1170899 = 1756349) B1756349
theorem B1170915 : Blo 1170402 1170915 := bstep (se 1 (by rfl) ⟨878186, by rfl⟩ : syracuseStep 1170915 = 1756373) B1756373
theorem B1170931 : Blo 1170402 1170931 := bstep (se 1 (by rfl) ⟨878198, by rfl⟩ : syracuseStep 1170931 = 1756397) B1756397
theorem B1318387 : Blo 1170402 1318387 := bstep (se 1 (by rfl) ⟨988790, by rfl⟩ : syracuseStep 1318387 = 1977581) B1977581
theorem B1170947 : Blo 1170402 1170947 := bstep (se 1 (by rfl) ⟨878210, by rfl⟩ : syracuseStep 1170947 = 1756421) B1756421
theorem B2964995 : Blo 1170402 2964995 := bstep (se 1 (by rfl) ⟨2223746, by rfl⟩ : syracuseStep 2964995 = 4447493) B4447493
theorem B3333649 : Blo 1170402 3333649 := bstep (se 2 (by rfl) ⟨1250118, by rfl⟩ : syracuseStep 3333649 = 2500237) B2500237
theorem B2670097 : Blo 1170402 2670097 := bstep (se 2 (by rfl) ⟨1001286, by rfl⟩ : syracuseStep 2670097 = 2002573) B2002573
theorem B1170963 : Blo 1170402 1170963 := bstep (se 1 (by rfl) ⟨878222, by rfl⟩ : syracuseStep 1170963 = 1756445) B1756445
theorem B1170979 : Blo 1170402 1170979 := bstep (se 1 (by rfl) ⟨878234, by rfl⟩ : syracuseStep 1170979 = 1756469) B1756469
theorem B1170995 : Blo 1170402 1170995 := bstep (se 1 (by rfl) ⟨878246, by rfl⟩ : syracuseStep 1170995 = 1756493) B1756493
theorem B1171011 : Blo 1170402 1171011 := bstep (se 1 (by rfl) ⟨878258, by rfl⟩ : syracuseStep 1171011 = 1756517) B1756517
theorem B1171027 : Blo 1170402 1171027 := bstep (se 1 (by rfl) ⟨878270, by rfl⟩ : syracuseStep 1171027 = 1756541) B1756541
theorem B1171043 : Blo 1170402 1171043 := bstep (se 1 (by rfl) ⟨878282, by rfl⟩ : syracuseStep 1171043 = 1756565) B1756565
theorem B3382897 : Blo 1170402 3382897 := bstep (se 2 (by rfl) ⟨1268586, by rfl⟩ : syracuseStep 3382897 = 2537173) B2537173
theorem B1171059 : Blo 1170402 1171059 := bstep (se 1 (by rfl) ⟨878294, by rfl⟩ : syracuseStep 1171059 = 1756589) B1756589
theorem B1171075 : Blo 1170402 1171075 := bstep (se 1 (by rfl) ⟨878306, by rfl⟩ : syracuseStep 1171075 = 1756613) B1756613
theorem B1318531 : Blo 1170402 1318531 := bstep (se 1 (by rfl) ⟨988898, by rfl⟩ : syracuseStep 1318531 = 1977797) B1977797
theorem B1171091 : Blo 1170402 1171091 := bstep (se 1 (by rfl) ⟨878318, by rfl⟩ : syracuseStep 1171091 = 1756637) B1756637
theorem B1171107 : Blo 1170402 1171107 := bstep (se 1 (by rfl) ⟨878330, by rfl⟩ : syracuseStep 1171107 = 1756661) B1756661
theorem B3006115 : Blo 1170402 3006115 := bstep (se 1 (by rfl) ⟨2254586, by rfl⟩ : syracuseStep 3006115 = 4509173) B4509173
theorem B1171123 : Blo 1170402 1171123 := bstep (se 1 (by rfl) ⟨878342, by rfl⟩ : syracuseStep 1171123 = 1756685) B1756685
theorem B1171139 : Blo 1170402 1171139 := bstep (se 1 (by rfl) ⟨878354, by rfl⟩ : syracuseStep 1171139 = 1756709) B1756709
theorem B2965187 : Blo 1170402 2965187 := bstep (se 1 (by rfl) ⟨2223890, by rfl⟩ : syracuseStep 2965187 = 4447781) B4447781
theorem B2637521 : Blo 1170402 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B1171155 : Blo 1170402 1171155 := bstep (se 1 (by rfl) ⟨878366, by rfl⟩ : syracuseStep 1171155 = 1756733) B1756733
theorem B1171171 : Blo 1170402 1171171 := bstep (se 1 (by rfl) ⟨878378, by rfl⟩ : syracuseStep 1171171 = 1756757) B1756757
theorem B2637539 : Blo 1170402 2637539 := bstep (se 1 (by rfl) ⟨1978154, by rfl⟩ : syracuseStep 2637539 = 3956309) B3956309
theorem B1171187 : Blo 1170402 1171187 := bstep (se 1 (by rfl) ⟨878390, by rfl⟩ : syracuseStep 1171187 = 1756781) B1756781
theorem B1171203 : Blo 1170402 1171203 := bstep (se 1 (by rfl) ⟨878402, by rfl⟩ : syracuseStep 1171203 = 1756805) B1756805
theorem B4505357 : Blo 1170402 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B1171219 : Blo 1170402 1171219 := bstep (se 1 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 1171219 = 1756829) B1756829
theorem B1318675 : Blo 1170402 1318675 := bstep (se 1 (by rfl) ⟨989006, by rfl⟩ : syracuseStep 1318675 = 1978013) B1978013
theorem B3333923 : Blo 1170402 3333923 := bstep (se 1 (by rfl) ⟨2500442, by rfl⟩ : syracuseStep 3333923 = 5000885) B5000885
theorem B1171235 : Blo 1170402 1171235 := bstep (se 1 (by rfl) ⟨878426, by rfl⟩ : syracuseStep 1171235 = 1756853) B1756853
theorem B3956525 : Blo 1170402 3956525 := bstep (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) B1483697
theorem B1171251 : Blo 1170402 1171251 := bstep (se 1 (by rfl) ⟨878438, by rfl⟩ : syracuseStep 1171251 = 1756877) B1756877
theorem B1171267 : Blo 1170402 1171267 := bstep (se 1 (by rfl) ⟨878450, by rfl⟩ : syracuseStep 1171267 = 1756901) B1756901
theorem B1482563 : Blo 1170402 1482563 := bstep (se 1 (by rfl) ⟨1111922, by rfl⟩ : syracuseStep 1482563 = 2223845) B2223845
theorem B1875793 : Blo 1170402 1875793 := bstep (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) B1406845
theorem B1171283 : Blo 1170402 1171283 := bstep (se 1 (by rfl) ⟨878462, by rfl⟩ : syracuseStep 1171283 = 1756925) B1756925
theorem B1900385 : Blo 1170402 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B2850659 : Blo 1170402 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B1171299 : Blo 1170402 1171299 := bstep (se 1 (by rfl) ⟨878474, by rfl⟩ : syracuseStep 1171299 = 1756949) B1756949
theorem B3956579 : Blo 1170402 3956579 := bstep (se 1 (by rfl) ⟨2967434, by rfl⟩ : syracuseStep 3956579 = 5934869) B5934869
theorem B1171315 : Blo 1170402 1171315 := bstep (se 1 (by rfl) ⟨878486, by rfl⟩ : syracuseStep 1171315 = 1756973) B1756973
theorem B1171331 : Blo 1170402 1171331 := bstep (se 1 (by rfl) ⟨878498, by rfl⟩ : syracuseStep 1171331 = 1756997) B1756997
theorem B1171347 : Blo 1170402 1171347 := bstep (se 1 (by rfl) ⟨878510, by rfl⟩ : syracuseStep 1171347 = 1757021) B1757021
theorem B1171363 : Blo 1170402 1171363 := bstep (se 1 (by rfl) ⟨878522, by rfl⟩ : syracuseStep 1171363 = 1757045) B1757045
theorem B1318819 : Blo 1170402 1318819 := bstep (se 1 (by rfl) ⟨989114, by rfl⟩ : syracuseStep 1318819 = 1978229) B1978229
theorem B1171379 : Blo 1170402 1171379 := bstep (se 1 (by rfl) ⟨878534, by rfl⟩ : syracuseStep 1171379 = 1757069) B1757069
theorem B1171395 : Blo 1170402 1171395 := bstep (se 1 (by rfl) ⟨878546, by rfl⟩ : syracuseStep 1171395 = 1757093) B1757093
theorem B1171411 : Blo 1170402 1171411 := bstep (se 1 (by rfl) ⟨878558, by rfl⟩ : syracuseStep 1171411 = 1757117) B1757117
theorem B1171427 : Blo 1170402 1171427 := bstep (se 1 (by rfl) ⟨878570, by rfl⟩ : syracuseStep 1171427 = 1757141) B1757141
theorem B2637809 : Blo 1170402 2637809 := bstep (se 2 (by rfl) ⟨989178, by rfl⟩ : syracuseStep 2637809 = 1978357) B1978357
theorem B1171443 : Blo 1170402 1171443 := bstep (se 1 (by rfl) ⟨878582, by rfl⟩ : syracuseStep 1171443 = 1757165) B1757165
theorem B2252801 : Blo 1170402 2252801 := bstep (se 2 (by rfl) ⟨844800, by rfl⟩ : syracuseStep 2252801 = 1689601) B1689601
theorem B1171467 : Blo 1170402 1171467 := bstep (se 1 (by rfl) ⟨878600, by rfl⟩ : syracuseStep 1171467 = 1757201) B1757201
theorem B1171479 : Blo 1170402 1171479 := bstep (se 1 (by rfl) ⟨878609, by rfl⟩ : syracuseStep 1171479 = 1757219) B1757219
theorem B1171499 : Blo 1170402 1171499 := bstep (se 1 (by rfl) ⟨878624, by rfl⟩ : syracuseStep 1171499 = 1757249) B1757249
theorem B1171511 : Blo 1170402 1171511 := bstep (se 1 (by rfl) ⟨878633, by rfl⟩ : syracuseStep 1171511 = 1757267) B1757267
theorem B4005953 : Blo 1170402 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B1171531 : Blo 1170402 1171531 := bstep (se 1 (by rfl) ⟨878648, by rfl⟩ : syracuseStep 1171531 = 1757297) B1757297
theorem B2637899 : Blo 1170402 2637899 := bstep (se 1 (by rfl) ⟨1978424, by rfl⟩ : syracuseStep 2637899 = 3956849) B3956849
theorem B1171543 : Blo 1170402 1171543 := bstep (se 1 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 1171543 = 1757315) B1757315
theorem B1171563 : Blo 1170402 1171563 := bstep (se 1 (by rfl) ⟨878672, by rfl⟩ : syracuseStep 1171563 = 1757345) B1757345
theorem B1171575 : Blo 1170402 1171575 := bstep (se 1 (by rfl) ⟨878681, by rfl⟩ : syracuseStep 1171575 = 1757363) B1757363
theorem B1171595 : Blo 1170402 1171595 := bstep (se 1 (by rfl) ⟨878696, by rfl⟩ : syracuseStep 1171595 = 1757393) B1757393
theorem B1171607 : Blo 1170402 1171607 := bstep (se 1 (by rfl) ⟨878705, by rfl⟩ : syracuseStep 1171607 = 1757411) B1757411
theorem B1171627 : Blo 1170402 1171627 := bstep (se 1 (by rfl) ⟨878720, by rfl⟩ : syracuseStep 1171627 = 1757441) B1757441
theorem B1171639 : Blo 1170402 1171639 := bstep (se 1 (by rfl) ⟨878729, by rfl⟩ : syracuseStep 1171639 = 1757459) B1757459
theorem B1171659 : Blo 1170402 1171659 := bstep (se 1 (by rfl) ⟨878744, by rfl⟩ : syracuseStep 1171659 = 1757489) B1757489
theorem B1171671 : Blo 1170402 1171671 := bstep (se 1 (by rfl) ⟨878753, by rfl⟩ : syracuseStep 1171671 = 1757507) B1757507
theorem B1171691 : Blo 1170402 1171691 := bstep (se 1 (by rfl) ⟨878768, by rfl⟩ : syracuseStep 1171691 = 1757537) B1757537
theorem B1171703 : Blo 1170402 1171703 := bstep (se 1 (by rfl) ⟨878777, by rfl⟩ : syracuseStep 1171703 = 1757555) B1757555
theorem B1171723 : Blo 1170402 1171723 := bstep (se 1 (by rfl) ⟨878792, by rfl⟩ : syracuseStep 1171723 = 1757585) B1757585
theorem B1171735 : Blo 1170402 1171735 := bstep (se 1 (by rfl) ⟨878801, by rfl⟩ : syracuseStep 1171735 = 1757603) B1757603
theorem B1171755 : Blo 1170402 1171755 := bstep (se 1 (by rfl) ⟨878816, by rfl⟩ : syracuseStep 1171755 = 1757633) B1757633
theorem B1171767 : Blo 1170402 1171767 := bstep (se 1 (by rfl) ⟨878825, by rfl⟩ : syracuseStep 1171767 = 1757651) B1757651
theorem B5005633 : Blo 1170402 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B2965835 : Blo 1170402 2965835 := bstep (se 1 (by rfl) ⟨2224376, by rfl⟩ : syracuseStep 2965835 = 4448753) B4448753
theorem B1171787 : Blo 1170402 1171787 := bstep (se 1 (by rfl) ⟨878840, by rfl⟩ : syracuseStep 1171787 = 1757681) B1757681
theorem B1171799 : Blo 1170402 1171799 := bstep (se 1 (by rfl) ⟨878849, by rfl⟩ : syracuseStep 1171799 = 1757699) B1757699
theorem B1171819 : Blo 1170402 1171819 := bstep (se 1 (by rfl) ⟨878864, by rfl⟩ : syracuseStep 1171819 = 1757729) B1757729
theorem B1171831 : Blo 1170402 1171831 := bstep (se 1 (by rfl) ⟨878873, by rfl⟩ : syracuseStep 1171831 = 1757747) B1757747
theorem B1171851 : Blo 1170402 1171851 := bstep (se 1 (by rfl) ⟨878888, by rfl⟩ : syracuseStep 1171851 = 1757777) B1757777
theorem B1171863 : Blo 1170402 1171863 := bstep (se 1 (by rfl) ⟨878897, by rfl⟩ : syracuseStep 1171863 = 1757795) B1757795
theorem B1171883 : Blo 1170402 1171883 := bstep (se 1 (by rfl) ⟨878912, by rfl⟩ : syracuseStep 1171883 = 1757825) B1757825
theorem B1171895 : Blo 1170402 1171895 := bstep (se 1 (by rfl) ⟨878921, by rfl⟩ : syracuseStep 1171895 = 1757843) B1757843
theorem B1171915 : Blo 1170402 1171915 := bstep (se 1 (by rfl) ⟨878936, by rfl⟩ : syracuseStep 1171915 = 1757873) B1757873
theorem B1483211 : Blo 1170402 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B1171927 : Blo 1170402 1171927 := bstep (se 1 (by rfl) ⟨878945, by rfl⟩ : syracuseStep 1171927 = 1757891) B1757891
theorem B1876441 : Blo 1170402 1876441 := bstep (se 2 (by rfl) ⟨703665, by rfl⟩ : syracuseStep 1876441 = 1407331) B1407331
theorem B1171947 : Blo 1170402 1171947 := bstep (se 1 (by rfl) ⟨878960, by rfl⟩ : syracuseStep 1171947 = 1757921) B1757921
theorem B1171959 : Blo 1170402 1171959 := bstep (se 1 (by rfl) ⟨878969, by rfl⟩ : syracuseStep 1171959 = 1757939) B1757939
theorem B1171979 : Blo 1170402 1171979 := bstep (se 1 (by rfl) ⟨878984, by rfl⟩ : syracuseStep 1171979 = 1757969) B1757969
theorem B1171991 : Blo 1170402 1171991 := bstep (se 1 (by rfl) ⟨878993, by rfl⟩ : syracuseStep 1171991 = 1757987) B1757987
theorem B1172011 : Blo 1170402 1172011 := bstep (se 1 (by rfl) ⟨879008, by rfl⟩ : syracuseStep 1172011 = 1758017) B1758017
theorem B1172023 : Blo 1170402 1172023 := bstep (se 1 (by rfl) ⟨879017, by rfl⟩ : syracuseStep 1172023 = 1758035) B1758035
theorem B1172043 : Blo 1170402 1172043 := bstep (se 1 (by rfl) ⟨879032, by rfl⟩ : syracuseStep 1172043 = 1758065) B1758065
theorem B1172055 : Blo 1170402 1172055 := bstep (se 1 (by rfl) ⟨879041, by rfl⟩ : syracuseStep 1172055 = 1758083) B1758083
theorem B6677093 : Blo 1170402 6677093 := bstep (se 4 (by rfl) ⟨625977, by rfl⟩ : syracuseStep 6677093 = 1251955) B1251955
theorem B1172075 : Blo 1170402 1172075 := bstep (se 1 (by rfl) ⟨879056, by rfl⟩ : syracuseStep 1172075 = 1758113) B1758113
theorem B1172087 : Blo 1170402 1172087 := bstep (se 1 (by rfl) ⟨879065, by rfl⟩ : syracuseStep 1172087 = 1758131) B1758131
theorem B1172107 : Blo 1170402 1172107 := bstep (se 1 (by rfl) ⟨879080, by rfl⟩ : syracuseStep 1172107 = 1758161) B1758161
theorem B12026519 : Blo 1170402 12026519 := bstep (se 1 (by rfl) ⟨9019889, by rfl⟩ : syracuseStep 12026519 = 18039779) B18039779
theorem B5005975 : Blo 1170402 5005975 := bstep (se 1 (by rfl) ⟨3754481, by rfl⟩ : syracuseStep 5005975 = 7508963) B7508963
theorem B1172119 : Blo 1170402 1172119 := bstep (se 1 (by rfl) ⟨879089, by rfl⟩ : syracuseStep 1172119 = 1758179) B1758179
theorem B1172139 : Blo 1170402 1172139 := bstep (se 1 (by rfl) ⟨879104, by rfl⟩ : syracuseStep 1172139 = 1758209) B1758209
theorem B8897201 : Blo 1170402 8897201 := bstep (se 2 (by rfl) ⟨3336450, by rfl⟩ : syracuseStep 8897201 = 6672901) B6672901
theorem B1172151 : Blo 1170402 1172151 := bstep (se 1 (by rfl) ⟨879113, by rfl⟩ : syracuseStep 1172151 = 1758227) B1758227
theorem B1172171 : Blo 1170402 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B1172183 : Blo 1170402 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1876697 : Blo 1170402 1876697 := bstep (se 2 (by rfl) ⟨703761, by rfl⟩ : syracuseStep 1876697 = 1407523) B1407523
theorem B1172203 : Blo 1170402 1172203 := bstep (se 1 (by rfl) ⟨879152, by rfl⟩ : syracuseStep 1172203 = 1758305) B1758305
theorem B1172215 : Blo 1170402 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B1172235 : Blo 1170402 1172235 := bstep (se 1 (by rfl) ⟨879176, by rfl⟩ : syracuseStep 1172235 = 1758353) B1758353
theorem B1975063 : Blo 1170402 1975063 := bstep (se 1 (by rfl) ⟨1481297, by rfl⟩ : syracuseStep 1975063 = 2962595) B2962595
theorem B1172247 : Blo 1170402 1172247 := bstep (se 1 (by rfl) ⟨879185, by rfl⟩ : syracuseStep 1172247 = 1758371) B1758371
theorem B1172267 : Blo 1170402 1172267 := bstep (se 1 (by rfl) ⟨879200, by rfl⟩ : syracuseStep 1172267 = 1758401) B1758401
theorem B1172279 : Blo 1170402 1172279 := bstep (se 1 (by rfl) ⟨879209, by rfl⟩ : syracuseStep 1172279 = 1758419) B1758419
theorem B4006721 : Blo 1170402 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B1172299 : Blo 1170402 1172299 := bstep (se 1 (by rfl) ⟨879224, by rfl⟩ : syracuseStep 1172299 = 1758449) B1758449
theorem B1172311 : Blo 1170402 1172311 := bstep (se 1 (by rfl) ⟨879233, by rfl⟩ : syracuseStep 1172311 = 1758467) B1758467
theorem B16032613 : Blo 1170402 16032613 := bstep (se 4 (by rfl) ⟨1503057, by rfl⟩ : syracuseStep 16032613 = 3006115) B3006115
theorem B1172331 : Blo 1170402 1172331 := bstep (se 1 (by rfl) ⟨879248, by rfl⟩ : syracuseStep 1172331 = 1758497) B1758497
theorem B1172343 : Blo 1170402 1172343 := bstep (se 1 (by rfl) ⟨879257, by rfl⟩ : syracuseStep 1172343 = 1758515) B1758515
theorem B1172363 : Blo 1170402 1172363 := bstep (se 1 (by rfl) ⟨879272, by rfl⟩ : syracuseStep 1172363 = 1758545) B1758545
theorem B1172375 : Blo 1170402 1172375 := bstep (se 1 (by rfl) ⟨879281, by rfl⟩ : syracuseStep 1172375 = 1758563) B1758563
theorem B1172395 : Blo 1170402 1172395 := bstep (se 1 (by rfl) ⟨879296, by rfl⟩ : syracuseStep 1172395 = 1758593) B1758593
theorem B15000497 : Blo 1170402 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B3752983 : Blo 1170402 3752983 := bstep (se 1 (by rfl) ⟨2814737, by rfl⟩ : syracuseStep 3752983 = 5629475) B5629475
theorem B8897687 : Blo 1170402 8897687 := bstep (se 1 (by rfl) ⟨6673265, by rfl⟩ : syracuseStep 8897687 = 13346531) B13346531
theorem B8447237 : Blo 1170402 8447237 := bstep (se 4 (by rfl) ⟨791928, by rfl⟩ : syracuseStep 8447237 = 1583857) B1583857
theorem B2966807 : Blo 1170402 2966807 := bstep (se 1 (by rfl) ⟨2225105, by rfl⟩ : syracuseStep 2966807 = 4450211) B4450211
theorem B1975691 : Blo 1170402 1975691 := bstep (se 1 (by rfl) ⟨1481768, by rfl⟩ : syracuseStep 1975691 = 2963537) B2963537
theorem B5932439 : Blo 1170402 5932439 := bstep (se 1 (by rfl) ⟨4449329, by rfl⟩ : syracuseStep 5932439 = 8898659) B8898659
theorem B4220333 : Blo 1170402 4220333 := bstep (se 3 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 4220333 = 1582625) B1582625
theorem B4752857 : Blo 1170402 4752857 := bstep (se 2 (by rfl) ⟨1782321, by rfl⟩ : syracuseStep 4752857 = 3564643) B3564643
theorem B1975819 : Blo 1170402 1975819 := bstep (se 1 (by rfl) ⟨1481864, by rfl⟩ : syracuseStep 1975819 = 2963729) B2963729
theorem B5629571 : Blo 1170402 5629571 := bstep (se 1 (by rfl) ⟨4222178, by rfl⟩ : syracuseStep 5629571 = 8444357) B8444357
theorem B4449923 : Blo 1170402 4449923 := bstep (se 1 (by rfl) ⟨3337442, by rfl⟩ : syracuseStep 4449923 = 6674885) B6674885
theorem B4449937 : Blo 1170402 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B1975961 : Blo 1170402 1975961 := bstep (se 2 (by rfl) ⟨740985, by rfl⟩ : syracuseStep 1975961 = 1481971) B1481971
theorem B1976089 : Blo 1170402 1976089 := bstep (se 2 (by rfl) ⟨741033, by rfl⟩ : syracuseStep 1976089 = 1482067) B1482067
theorem B4220723 : Blo 1170402 4220723 := bstep (se 1 (by rfl) ⟨3165542, by rfl⟩ : syracuseStep 4220723 = 6331085) B6331085
theorem B3753803 : Blo 1170402 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B4507571 : Blo 1170402 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B6670259 : Blo 1170402 6670259 := bstep (se 1 (by rfl) ⟨5002694, by rfl⟩ : syracuseStep 6670259 = 10005389) B10005389
theorem B15001523 : Blo 1170402 15001523 := bstep (se 1 (by rfl) ⟨11251142, by rfl⟩ : syracuseStep 15001523 = 22502285) B22502285
theorem B4220851 : Blo 1170402 4220851 := bstep (se 1 (by rfl) ⟨3165638, by rfl⟩ : syracuseStep 4220851 = 6331277) B6331277
theorem B2967475 : Blo 1170402 2967475 := bstep (se 1 (by rfl) ⟨2225606, by rfl⟩ : syracuseStep 2967475 = 4451213) B4451213
theorem B4450241 : Blo 1170402 4450241 := bstep (se 2 (by rfl) ⟨1668840, by rfl⟩ : syracuseStep 4450241 = 3337681) B3337681
theorem B10831877 : Blo 1170402 10831877 := bstep (se 4 (by rfl) ⟨1015488, by rfl⟩ : syracuseStep 10831877 = 2030977) B2030977
theorem B2967617 : Blo 1170402 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B2222167 : Blo 1170402 2222167 := bstep (se 1 (by rfl) ⟨1666625, by rfl⟩ : syracuseStep 2222167 = 3333251) B3333251
theorem B1689751 : Blo 1170402 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B2672833 : Blo 1170402 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B2222387 : Blo 1170402 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B1976663 : Blo 1170402 1976663 := bstep (se 1 (by rfl) ⟨1482497, by rfl⟩ : syracuseStep 1976663 = 2964995) B2964995
theorem B4999603 : Blo 1170402 4999603 := bstep (se 1 (by rfl) ⟨3749702, by rfl⟩ : syracuseStep 4999603 = 7499405) B7499405
theorem B2501057 : Blo 1170402 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B1976791 : Blo 1170402 1976791 := bstep (se 1 (by rfl) ⟨1482593, by rfl⟩ : syracuseStep 1976791 = 2965187) B2965187
theorem B3754457 : Blo 1170402 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B1755659 : Blo 1170402 1755659 := bstep (se 1 (by rfl) ⟨1316744, by rfl⟩ : syracuseStep 1755659 = 2633489) B2633489
theorem B1755671 : Blo 1170402 1755671 := bstep (se 1 (by rfl) ⟨1316753, by rfl⟩ : syracuseStep 1755671 = 2633507) B2633507
theorem B2222615 : Blo 1170402 2222615 := bstep (se 1 (by rfl) ⟨1666961, by rfl⟩ : syracuseStep 2222615 = 3333923) B3333923
theorem B3951179 : Blo 1170402 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B1755737 : Blo 1170402 1755737 := bstep (se 2 (by rfl) ⟨658401, by rfl⟩ : syracuseStep 1755737 = 1316803) B1316803
theorem B4450909 : Blo 1170402 4450909 := bstep (se 3 (by rfl) ⟨834545, by rfl⟩ : syracuseStep 4450909 = 1669091) B1669091
theorem B1755851 : Blo 1170402 1755851 := bstep (se 1 (by rfl) ⟨1316888, by rfl⟩ : syracuseStep 1755851 = 2633777) B2633777
theorem B1755863 : Blo 1170402 1755863 := bstep (se 1 (by rfl) ⟨1316897, by rfl⟩ : syracuseStep 1755863 = 2633795) B2633795
theorem B1755929 : Blo 1170402 1755929 := bstep (se 2 (by rfl) ⟨658473, by rfl⟩ : syracuseStep 1755929 = 1316947) B1316947
theorem B2222873 : Blo 1170402 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B4746059 : Blo 1170402 4746059 := bstep (se 1 (by rfl) ⟨3559544, by rfl⟩ : syracuseStep 4746059 = 7119089) B7119089
theorem B3951449 : Blo 1170402 3951449 := bstep (se 2 (by rfl) ⟨1481793, by rfl⟩ : syracuseStep 3951449 = 2963587) B2963587
theorem B1756043 : Blo 1170402 1756043 := bstep (se 1 (by rfl) ⟨1317032, by rfl⟩ : syracuseStep 1756043 = 2634065) B2634065
theorem B1756055 : Blo 1170402 1756055 := bstep (se 1 (by rfl) ⟨1317041, by rfl⟩ : syracuseStep 1756055 = 2634083) B2634083
theorem B2501579 : Blo 1170402 2501579 := bstep (se 1 (by rfl) ⟨1876184, by rfl⟩ : syracuseStep 2501579 = 3752369) B3752369
theorem B1756121 : Blo 1170402 1756121 := bstep (se 2 (by rfl) ⟨658545, by rfl⟩ : syracuseStep 1756121 = 1317091) B1317091
theorem B1756235 : Blo 1170402 1756235 := bstep (se 1 (by rfl) ⟨1317176, by rfl⟩ : syracuseStep 1756235 = 2634353) B2634353
theorem B1977419 : Blo 1170402 1977419 := bstep (se 1 (by rfl) ⟨1483064, by rfl⟩ : syracuseStep 1977419 = 2966129) B2966129
theorem B1584203 : Blo 1170402 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B1756247 : Blo 1170402 1756247 := bstep (se 1 (by rfl) ⟨1317185, by rfl⟩ : syracuseStep 1756247 = 2634371) B2634371
theorem B1756313 : Blo 1170402 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B2223283 : Blo 1170402 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B1977547 : Blo 1170402 1977547 := bstep (se 1 (by rfl) ⟨1483160, by rfl⟩ : syracuseStep 1977547 = 2966321) B2966321
theorem B1756427 : Blo 1170402 1756427 := bstep (se 1 (by rfl) ⟨1317320, by rfl⟩ : syracuseStep 1756427 = 2634641) B2634641
theorem B1756439 : Blo 1170402 1756439 := bstep (se 1 (by rfl) ⟨1317329, by rfl⟩ : syracuseStep 1756439 = 2634659) B2634659
theorem B1756505 : Blo 1170402 1756505 := bstep (se 2 (by rfl) ⟨658689, by rfl⟩ : syracuseStep 1756505 = 1317379) B1317379
theorem B1977689 : Blo 1170402 1977689 := bstep (se 2 (by rfl) ⟨741633, by rfl⟩ : syracuseStep 1977689 = 1483267) B1483267
theorem B8449373 : Blo 1170402 8449373 := bstep (se 3 (by rfl) ⟨1584257, by rfl⟩ : syracuseStep 8449373 = 3168515) B3168515
theorem B6671717 : Blo 1170402 6671717 := bstep (se 4 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 6671717 = 1250947) B1250947
theorem B2813363 : Blo 1170402 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B1756619 : Blo 1170402 1756619 := bstep (se 1 (by rfl) ⟨1317464, by rfl⟩ : syracuseStep 1756619 = 2634929) B2634929
theorem B1756631 : Blo 1170402 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B2813401 : Blo 1170402 2813401 := bstep (se 2 (by rfl) ⟨1055025, by rfl⟩ : syracuseStep 2813401 = 2110051) B2110051
theorem B1977817 : Blo 1170402 1977817 := bstep (se 2 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 1977817 = 1483363) B1483363
theorem B4337155 : Blo 1170402 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B3952151 : Blo 1170402 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B1666585 : Blo 1170402 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B1756697 : Blo 1170402 1756697 := bstep (se 2 (by rfl) ⟨658761, by rfl⟩ : syracuseStep 1756697 = 1317523) B1317523
theorem B5926445 : Blo 1170402 5926445 := bstep (se 3 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 5926445 = 2222417) B2222417
theorem B3755585 : Blo 1170402 3755585 := bstep (se 2 (by rfl) ⟨1408344, by rfl⟩ : syracuseStep 3755585 = 2816689) B2816689
theorem B1756811 : Blo 1170402 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B5000849 : Blo 1170402 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B1756823 : Blo 1170402 1756823 := bstep (se 1 (by rfl) ⟨1317617, by rfl⟩ : syracuseStep 1756823 = 2635235) B2635235
theorem B2223769 : Blo 1170402 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B1756889 : Blo 1170402 1756889 := bstep (se 2 (by rfl) ⟨658833, by rfl⟩ : syracuseStep 1756889 = 1317667) B1317667
theorem B1757003 : Blo 1170402 1757003 := bstep (se 1 (by rfl) ⟨1317752, by rfl⟩ : syracuseStep 1757003 = 2635505) B2635505
theorem B1757015 : Blo 1170402 1757015 := bstep (se 1 (by rfl) ⟨1317761, by rfl⟩ : syracuseStep 1757015 = 2635523) B2635523
theorem B2633561 : Blo 1170402 2633561 := bstep (se 2 (by rfl) ⟨987585, by rfl⟩ : syracuseStep 2633561 = 1975171) B1975171
theorem B4222813 : Blo 1170402 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B4509533 : Blo 1170402 4509533 := bstep (se 3 (by rfl) ⟨845537, by rfl⟩ : syracuseStep 4509533 = 1691075) B1691075
theorem B19009397 : Blo 1170402 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B1757081 : Blo 1170402 1757081 := bstep (se 2 (by rfl) ⟨658905, by rfl⟩ : syracuseStep 1757081 = 1317811) B1317811
theorem B2633651 : Blo 1170402 2633651 := bstep (se 1 (by rfl) ⟨1975238, by rfl⟩ : syracuseStep 2633651 = 3950477) B3950477
theorem B2633687 : Blo 1170402 2633687 := bstep (se 1 (by rfl) ⟨1975265, by rfl⟩ : syracuseStep 2633687 = 3950531) B3950531
theorem B1757195 : Blo 1170402 1757195 := bstep (se 1 (by rfl) ⟨1317896, by rfl⟩ : syracuseStep 1757195 = 2635793) B2635793
theorem B6672401 : Blo 1170402 6672401 := bstep (se 2 (by rfl) ⟨2502150, by rfl⟩ : syracuseStep 6672401 = 5004301) B5004301
theorem B1757207 : Blo 1170402 1757207 := bstep (se 1 (by rfl) ⟨1317905, by rfl⟩ : syracuseStep 1757207 = 2635811) B2635811
theorem B1978391 : Blo 1170402 1978391 := bstep (se 1 (by rfl) ⟨1483793, by rfl⟩ : syracuseStep 1978391 = 2967587) B2967587
theorem B3952691 : Blo 1170402 3952691 := bstep (se 1 (by rfl) ⟨2964518, by rfl⟩ : syracuseStep 3952691 = 5929037) B5929037
theorem B1757273 : Blo 1170402 1757273 := bstep (se 2 (by rfl) ⟨658977, by rfl⟩ : syracuseStep 1757273 = 1317955) B1317955
theorem B2633867 : Blo 1170402 2633867 := bstep (se 1 (by rfl) ⟨1975400, by rfl⟩ : syracuseStep 2633867 = 3950801) B3950801
theorem B2502809 : Blo 1170402 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B2633921 : Blo 1170402 2633921 := bstep (se 2 (by rfl) ⟨987720, by rfl⟩ : syracuseStep 2633921 = 1975441) B1975441
theorem B1757387 : Blo 1170402 1757387 := bstep (se 1 (by rfl) ⟨1318040, by rfl⟩ : syracuseStep 1757387 = 2636081) B2636081
theorem B2224331 : Blo 1170402 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B1757399 : Blo 1170402 1757399 := bstep (se 1 (by rfl) ⟨1318049, by rfl⟩ : syracuseStep 1757399 = 2636099) B2636099
theorem B1757465 : Blo 1170402 1757465 := bstep (se 2 (by rfl) ⟨659049, by rfl⟩ : syracuseStep 1757465 = 1318099) B1318099
theorem B3952961 : Blo 1170402 3952961 := bstep (se 2 (by rfl) ⟨1482360, by rfl⟩ : syracuseStep 3952961 = 2964721) B2964721
theorem B2224513 : Blo 1170402 2224513 := bstep (se 2 (by rfl) ⟨834192, by rfl⟩ : syracuseStep 2224513 = 1668385) B1668385
theorem B1757579 : Blo 1170402 1757579 := bstep (se 1 (by rfl) ⟨1318184, by rfl⟩ : syracuseStep 1757579 = 2636369) B2636369
theorem B1757591 : Blo 1170402 1757591 := bstep (se 1 (by rfl) ⟨1318193, by rfl⟩ : syracuseStep 1757591 = 2636387) B2636387
theorem B2634137 : Blo 1170402 2634137 := bstep (se 2 (by rfl) ⟨987801, by rfl⟩ : syracuseStep 2634137 = 1975603) B1975603
theorem B4280779 : Blo 1170402 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B1757657 : Blo 1170402 1757657 := bstep (se 2 (by rfl) ⟨659121, by rfl⟩ : syracuseStep 1757657 = 1318243) B1318243
theorem B2634227 : Blo 1170402 2634227 := bstep (se 1 (by rfl) ⟨1975670, by rfl⟩ : syracuseStep 2634227 = 3951341) B3951341
theorem B2634263 : Blo 1170402 2634263 := bstep (se 1 (by rfl) ⟨1975697, by rfl⟩ : syracuseStep 2634263 = 3951395) B3951395
theorem B2503219 : Blo 1170402 2503219 := bstep (se 1 (by rfl) ⟨1877414, by rfl⟩ : syracuseStep 2503219 = 3754829) B3754829
theorem B1249867 : Blo 1170402 1249867 := bstep (se 1 (by rfl) ⟨937400, by rfl⟩ : syracuseStep 1249867 = 1874801) B1874801
theorem B7221835 : Blo 1170402 7221835 := bstep (se 1 (by rfl) ⟨5416376, by rfl⟩ : syracuseStep 7221835 = 10832753) B10832753
theorem B1757771 : Blo 1170402 1757771 := bstep (se 1 (by rfl) ⟨1318328, by rfl⟩ : syracuseStep 1757771 = 2636657) B2636657
theorem B1757783 : Blo 1170402 1757783 := bstep (se 1 (by rfl) ⟨1318337, by rfl⟩ : syracuseStep 1757783 = 2636675) B2636675
theorem B1757849 : Blo 1170402 1757849 := bstep (se 2 (by rfl) ⟨659193, by rfl⟩ : syracuseStep 1757849 = 1318387) B1318387
theorem B4444865 : Blo 1170402 4444865 := bstep (se 2 (by rfl) ⟨1666824, by rfl⟩ : syracuseStep 4444865 = 3333649) B3333649
theorem B3560129 : Blo 1170402 3560129 := bstep (se 2 (by rfl) ⟨1335048, by rfl⟩ : syracuseStep 3560129 = 2670097) B2670097
theorem B2634443 : Blo 1170402 2634443 := bstep (se 1 (by rfl) ⟨1975832, by rfl⟩ : syracuseStep 2634443 = 3951665) B3951665
theorem B2634497 : Blo 1170402 2634497 := bstep (se 2 (by rfl) ⟨987936, by rfl⟩ : syracuseStep 2634497 = 1975873) B1975873
theorem B1757963 : Blo 1170402 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B1757975 : Blo 1170402 1757975 := bstep (se 1 (by rfl) ⟨1318481, by rfl⟩ : syracuseStep 1757975 = 2636963) B2636963
theorem B4510529 : Blo 1170402 4510529 := bstep (se 2 (by rfl) ⟨1691448, by rfl⟩ : syracuseStep 4510529 = 3382897) B3382897
theorem B1758041 : Blo 1170402 1758041 := bstep (se 2 (by rfl) ⟨659265, by rfl⟩ : syracuseStep 1758041 = 1318531) B1318531
theorem B3953501 : Blo 1170402 3953501 := bstep (se 3 (by rfl) ⟨741281, by rfl⟩ : syracuseStep 3953501 = 1482563) B1482563
theorem B5075905 : Blo 1170402 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B1668043 : Blo 1170402 1668043 := bstep (se 1 (by rfl) ⟨1251032, by rfl⟩ : syracuseStep 1668043 = 2502065) B2502065
theorem B1758155 : Blo 1170402 1758155 := bstep (se 1 (by rfl) ⟨1318616, by rfl⟩ : syracuseStep 1758155 = 2637233) B2637233
theorem B1668055 : Blo 1170402 1668055 := bstep (se 1 (by rfl) ⟨1251041, by rfl⟩ : syracuseStep 1668055 = 2502083) B2502083
theorem B1758167 : Blo 1170402 1758167 := bstep (se 1 (by rfl) ⟨1318625, by rfl⟩ : syracuseStep 1758167 = 2637251) B2637251
theorem B2634713 : Blo 1170402 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B1758233 : Blo 1170402 1758233 := bstep (se 2 (by rfl) ⟨659337, by rfl⟩ : syracuseStep 1758233 = 1318675) B1318675
theorem B2503705 : Blo 1170402 2503705 := bstep (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) B1877779
theorem B2634803 : Blo 1170402 2634803 := bstep (se 1 (by rfl) ⟨1976102, by rfl⟩ : syracuseStep 2634803 = 3952205) B3952205
theorem B2225227 : Blo 1170402 2225227 := bstep (se 1 (by rfl) ⟨1668920, by rfl⟩ : syracuseStep 2225227 = 3337841) B3337841
theorem B2634839 : Blo 1170402 2634839 := bstep (se 1 (by rfl) ⟨1976129, by rfl⟩ : syracuseStep 2634839 = 3952259) B3952259
theorem B1758347 : Blo 1170402 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B2225303 : Blo 1170402 2225303 := bstep (se 1 (by rfl) ⟨1668977, by rfl⟩ : syracuseStep 2225303 = 3337955) B3337955
theorem B1758359 : Blo 1170402 1758359 := bstep (se 1 (by rfl) ⟨1318769, by rfl⟩ : syracuseStep 1758359 = 2637539) B2637539
theorem B3003571 : Blo 1170402 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B36066485 : Blo 1170402 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B2110657 : Blo 1170402 2110657 := bstep (se 2 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 2110657 = 1582993) B1582993
theorem B1758425 : Blo 1170402 1758425 := bstep (se 2 (by rfl) ⟨659409, by rfl⟩ : syracuseStep 1758425 = 1318819) B1318819
theorem B1266923 : Blo 1170402 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B2635019 : Blo 1170402 2635019 := bstep (se 1 (by rfl) ⟨1976264, by rfl⟩ : syracuseStep 2635019 = 3952529) B3952529
theorem B2635073 : Blo 1170402 2635073 := bstep (se 2 (by rfl) ⟨988152, by rfl⟩ : syracuseStep 2635073 = 1976305) B1976305
theorem B5141825 : Blo 1170402 5141825 := bstep (se 2 (by rfl) ⟨1928184, by rfl⟩ : syracuseStep 5141825 = 3856369) B3856369
theorem B1758539 : Blo 1170402 1758539 := bstep (se 1 (by rfl) ⟨1318904, by rfl⟩ : syracuseStep 1758539 = 2637809) B2637809
theorem B1758551 : Blo 1170402 1758551 := bstep (se 1 (by rfl) ⟨1318913, by rfl⟩ : syracuseStep 1758551 = 2637827) B2637827
theorem B2962777 : Blo 1170402 2962777 := bstep (se 2 (by rfl) ⟨1111041, by rfl⟩ : syracuseStep 2962777 = 2222083) B2222083
theorem B16258421 : Blo 1170402 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B160339397 : Blo 1170402 160339397 := bstep (se 4 (by rfl) ⟨15031818, by rfl⟩ : syracuseStep 160339397 = 30063637) B30063637
theorem B2373143 : Blo 1170402 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B2635289 : Blo 1170402 2635289 := bstep (se 2 (by rfl) ⟨988233, by rfl⟩ : syracuseStep 2635289 = 1976467) B1976467
theorem B33764957 : Blo 1170402 33764957 := bstep (se 3 (by rfl) ⟨6330929, by rfl⟩ : syracuseStep 33764957 = 12661859) B12661859
theorem B2635379 : Blo 1170402 2635379 := bstep (se 1 (by rfl) ⟨1976534, by rfl⟩ : syracuseStep 2635379 = 3953069) B3953069
theorem B2635415 : Blo 1170402 2635415 := bstep (se 1 (by rfl) ⟨1976561, by rfl⟩ : syracuseStep 2635415 = 3953123) B3953123
theorem B15021773 : Blo 1170402 15021773 := bstep (se 3 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 15021773 = 5633165) B5633165
theorem B2111233 : Blo 1170402 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B2635595 : Blo 1170402 2635595 := bstep (se 1 (by rfl) ⟨1976696, by rfl⟩ : syracuseStep 2635595 = 3953393) B3953393
theorem B2635649 : Blo 1170402 2635649 := bstep (se 2 (by rfl) ⟨988368, by rfl⟩ : syracuseStep 2635649 = 1976737) B1976737
theorem B11409329 : Blo 1170402 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B2111435 : Blo 1170402 2111435 := bstep (se 1 (by rfl) ⟨1583576, by rfl⟩ : syracuseStep 2111435 = 3167153) B3167153
theorem B3954635 : Blo 1170402 3954635 := bstep (se 1 (by rfl) ⟨2965976, by rfl⟩ : syracuseStep 3954635 = 5931953) B5931953
theorem B1316875 : Blo 1170402 1316875 := bstep (se 1 (by rfl) ⟨987656, by rfl⟩ : syracuseStep 1316875 = 1975313) B1975313
theorem B6330413 : Blo 1170402 6330413 := bstep (se 3 (by rfl) ⟨1186952, by rfl⟩ : syracuseStep 6330413 = 2373905) B2373905
theorem B5003309 : Blo 1170402 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B7501889 : Blo 1170402 7501889 := bstep (se 2 (by rfl) ⟨2813208, by rfl⟩ : syracuseStep 7501889 = 5626417) B5626417
theorem B3209291 : Blo 1170402 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B2635865 : Blo 1170402 2635865 := bstep (se 2 (by rfl) ⟨988449, by rfl⟩ : syracuseStep 2635865 = 1976899) B1976899
theorem B1316983 : Blo 1170402 1316983 := bstep (se 1 (by rfl) ⟨987737, by rfl⟩ : syracuseStep 1316983 = 1975475) B1975475
theorem B4446353 : Blo 1170402 4446353 := bstep (se 2 (by rfl) ⟨1667382, by rfl⟩ : syracuseStep 4446353 = 3334765) B3334765
theorem B2635955 : Blo 1170402 2635955 := bstep (se 1 (by rfl) ⟨1976966, by rfl⟩ : syracuseStep 2635955 = 3953933) B3953933
theorem B2635991 : Blo 1170402 2635991 := bstep (se 1 (by rfl) ⟨1976993, by rfl⟩ : syracuseStep 2635991 = 3953987) B3953987
theorem B3954905 : Blo 1170402 3954905 := bstep (se 2 (by rfl) ⟨1483089, by rfl⟩ : syracuseStep 3954905 = 2966179) B2966179
theorem B1718489 : Blo 1170402 1718489 := bstep (se 2 (by rfl) ⟨644433, by rfl⟩ : syracuseStep 1718489 = 1288867) B1288867
theorem B1317163 : Blo 1170402 1317163 := bstep (se 1 (by rfl) ⟨987872, by rfl⟩ : syracuseStep 1317163 = 1975745) B1975745
theorem B2005337 : Blo 1170402 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B2636171 : Blo 1170402 2636171 := bstep (se 1 (by rfl) ⟨1977128, by rfl⟩ : syracuseStep 2636171 = 3954257) B3954257
theorem B1317271 : Blo 1170402 1317271 := bstep (se 1 (by rfl) ⟨987953, by rfl⟩ : syracuseStep 1317271 = 1975907) B1975907
theorem B2963891 : Blo 1170402 2963891 := bstep (se 1 (by rfl) ⟨2222918, by rfl⟩ : syracuseStep 2963891 = 4445837) B4445837
theorem B2636225 : Blo 1170402 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B24033809 : Blo 1170402 24033809 := bstep (se 2 (by rfl) ⟨9012678, by rfl⟩ : syracuseStep 24033809 = 18025357) B18025357
theorem B1251883 : Blo 1170402 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B1317451 : Blo 1170402 1317451 := bstep (se 1 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 1317451 = 1976177) B1976177
theorem B16890443 : Blo 1170402 16890443 := bstep (se 1 (by rfl) ⟨12667832, by rfl⟩ : syracuseStep 16890443 = 25335665) B25335665
theorem B7510603 : Blo 1170402 7510603 := bstep (se 1 (by rfl) ⟨5632952, by rfl⟩ : syracuseStep 7510603 = 11265905) B11265905
theorem B4446809 : Blo 1170402 4446809 := bstep (se 2 (by rfl) ⟨1667553, by rfl⟩ : syracuseStep 4446809 = 3335107) B3335107
theorem B2636441 : Blo 1170402 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B1317559 : Blo 1170402 1317559 := bstep (se 1 (by rfl) ⟨988169, by rfl⟩ : syracuseStep 1317559 = 1976339) B1976339
theorem B1481419 : Blo 1170402 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B2964185 : Blo 1170402 2964185 := bstep (se 2 (by rfl) ⟨1111569, by rfl⟩ : syracuseStep 2964185 = 2223139) B2223139
theorem B5003993 : Blo 1170402 5003993 := bstep (se 2 (by rfl) ⟨1876497, by rfl⟩ : syracuseStep 5003993 = 3752995) B3752995
theorem B2636531 : Blo 1170402 2636531 := bstep (se 1 (by rfl) ⟨1977398, by rfl⟩ : syracuseStep 2636531 = 3954797) B3954797
theorem B2636567 : Blo 1170402 2636567 := bstep (se 1 (by rfl) ⟨1977425, by rfl⟩ : syracuseStep 2636567 = 3954851) B3954851
theorem B4447021 : Blo 1170402 4447021 := bstep (se 3 (by rfl) ⟨833816, by rfl⟩ : syracuseStep 4447021 = 1667633) B1667633
theorem B1317739 : Blo 1170402 1317739 := bstep (se 1 (by rfl) ⟨988304, by rfl⟩ : syracuseStep 1317739 = 1976609) B1976609
theorem B3955607 : Blo 1170402 3955607 := bstep (se 1 (by rfl) ⟨2966705, by rfl⟩ : syracuseStep 3955607 = 5933411) B5933411
theorem B2636747 : Blo 1170402 2636747 := bstep (se 1 (by rfl) ⟨1977560, by rfl⟩ : syracuseStep 2636747 = 3955121) B3955121
theorem B1317847 : Blo 1170402 1317847 := bstep (se 1 (by rfl) ⟨988385, by rfl⟩ : syracuseStep 1317847 = 1976771) B1976771
theorem B1170411 : Blo 1170402 1170411 := bstep (se 1 (by rfl) ⟨877808, by rfl⟩ : syracuseStep 1170411 = 1755617) B1755617
theorem B1170423 : Blo 1170402 1170423 := bstep (se 1 (by rfl) ⟨877817, by rfl⟩ : syracuseStep 1170423 = 1755635) B1755635
theorem B2636801 : Blo 1170402 2636801 := bstep (se 2 (by rfl) ⟨988800, by rfl⟩ : syracuseStep 2636801 = 1977601) B1977601
theorem B1170443 : Blo 1170402 1170443 := bstep (se 1 (by rfl) ⟨877832, by rfl⟩ : syracuseStep 1170443 = 1755665) B1755665
theorem B1170455 : Blo 1170402 1170455 := bstep (se 1 (by rfl) ⟨877841, by rfl⟩ : syracuseStep 1170455 = 1755683) B1755683
theorem B1170475 : Blo 1170402 1170475 := bstep (se 1 (by rfl) ⟨877856, by rfl⟩ : syracuseStep 1170475 = 1755713) B1755713
theorem B1170487 : Blo 1170402 1170487 := bstep (se 1 (by rfl) ⟨877865, by rfl⟩ : syracuseStep 1170487 = 1755731) B1755731
theorem B1170507 : Blo 1170402 1170507 := bstep (se 1 (by rfl) ⟨877880, by rfl⟩ : syracuseStep 1170507 = 1755761) B1755761
theorem B1170519 : Blo 1170402 1170519 := bstep (se 1 (by rfl) ⟨877889, by rfl⟩ : syracuseStep 1170519 = 1755779) B1755779
theorem B4447325 : Blo 1170402 4447325 := bstep (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) B1667747
theorem B1170539 : Blo 1170402 1170539 := bstep (se 1 (by rfl) ⟨877904, by rfl⟩ : syracuseStep 1170539 = 1755809) B1755809
theorem B1170551 : Blo 1170402 1170551 := bstep (se 1 (by rfl) ⟨877913, by rfl⟩ : syracuseStep 1170551 = 1755827) B1755827
theorem B1170571 : Blo 1170402 1170571 := bstep (se 1 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 1170571 = 1755857) B1755857
theorem B1318027 : Blo 1170402 1318027 := bstep (se 1 (by rfl) ⟨988520, by rfl⟩ : syracuseStep 1318027 = 1977041) B1977041
theorem B1170583 : Blo 1170402 1170583 := bstep (se 1 (by rfl) ⟨877937, by rfl⟩ : syracuseStep 1170583 = 1755875) B1755875
theorem B1170603 : Blo 1170402 1170603 := bstep (se 1 (by rfl) ⟨877952, by rfl⟩ : syracuseStep 1170603 = 1755905) B1755905
theorem B6675635 : Blo 1170402 6675635 := bstep (se 1 (by rfl) ⟨5006726, by rfl⟩ : syracuseStep 6675635 = 10013453) B10013453
theorem B1170615 : Blo 1170402 1170615 := bstep (se 1 (by rfl) ⟨877961, by rfl⟩ : syracuseStep 1170615 = 1755923) B1755923
theorem B1170635 : Blo 1170402 1170635 := bstep (se 1 (by rfl) ⟨877976, by rfl⟩ : syracuseStep 1170635 = 1755953) B1755953
theorem B1170647 : Blo 1170402 1170647 := bstep (se 1 (by rfl) ⟨877985, by rfl⟩ : syracuseStep 1170647 = 1755971) B1755971
theorem B2637017 : Blo 1170402 2637017 := bstep (se 2 (by rfl) ⟨988881, by rfl⟩ : syracuseStep 2637017 = 1977763) B1977763
theorem B1170667 : Blo 1170402 1170667 := bstep (se 1 (by rfl) ⟨878000, by rfl⟩ : syracuseStep 1170667 = 1756001) B1756001
theorem B1170679 : Blo 1170402 1170679 := bstep (se 1 (by rfl) ⟨878009, by rfl⟩ : syracuseStep 1170679 = 1756019) B1756019
theorem B1318135 : Blo 1170402 1318135 := bstep (se 1 (by rfl) ⟨988601, by rfl⟩ : syracuseStep 1318135 = 1977203) B1977203
theorem B1170699 : Blo 1170402 1170699 := bstep (se 1 (by rfl) ⟨878024, by rfl⟩ : syracuseStep 1170699 = 1756049) B1756049
theorem B1170711 : Blo 1170402 1170711 := bstep (se 1 (by rfl) ⟨878033, by rfl⟩ : syracuseStep 1170711 = 1756067) B1756067
theorem B1170731 : Blo 1170402 1170731 := bstep (se 1 (by rfl) ⟨878048, by rfl⟩ : syracuseStep 1170731 = 1756097) B1756097
theorem B2637107 : Blo 1170402 2637107 := bstep (se 1 (by rfl) ⟨1977830, by rfl⟩ : syracuseStep 2637107 = 3955661) B3955661
theorem B1170743 : Blo 1170402 1170743 := bstep (se 1 (by rfl) ⟨878057, by rfl⟩ : syracuseStep 1170743 = 1756115) B1756115
theorem B6667595 : Blo 1170402 6667595 := bstep (se 1 (by rfl) ⟨5000696, by rfl⟩ : syracuseStep 6667595 = 10001393) B10001393
theorem B1170763 : Blo 1170402 1170763 := bstep (se 1 (by rfl) ⟨878072, by rfl⟩ : syracuseStep 1170763 = 1756145) B1756145
theorem B1170775 : Blo 1170402 1170775 := bstep (se 1 (by rfl) ⟨878081, by rfl⟩ : syracuseStep 1170775 = 1756163) B1756163
theorem B2637143 : Blo 1170402 2637143 := bstep (se 1 (by rfl) ⟨1977857, by rfl⟩ : syracuseStep 2637143 = 3955715) B3955715
theorem B5930333 : Blo 1170402 5930333 := bstep (se 3 (by rfl) ⟨1111937, by rfl⟩ : syracuseStep 5930333 = 2223875) B2223875
theorem B1170795 : Blo 1170402 1170795 := bstep (se 1 (by rfl) ⟨878096, by rfl⟩ : syracuseStep 1170795 = 1756193) B1756193
theorem B1170807 : Blo 1170402 1170807 := bstep (se 1 (by rfl) ⟨878105, by rfl⟩ : syracuseStep 1170807 = 1756211) B1756211
theorem B1170827 : Blo 1170402 1170827 := bstep (se 1 (by rfl) ⟨878120, by rfl⟩ : syracuseStep 1170827 = 1756241) B1756241
theorem B4218257 : Blo 1170402 4218257 := bstep (se 2 (by rfl) ⟨1581846, by rfl⟩ : syracuseStep 4218257 = 3163693) B3163693
theorem B1170839 : Blo 1170402 1170839 := bstep (se 1 (by rfl) ⟨878129, by rfl⟩ : syracuseStep 1170839 = 1756259) B1756259
theorem B2375065 : Blo 1170402 2375065 := bstep (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) B1781299
theorem B1170859 : Blo 1170402 1170859 := bstep (se 1 (by rfl) ⟨878144, by rfl⟩ : syracuseStep 1170859 = 1756289) B1756289
theorem B1318315 : Blo 1170402 1318315 := bstep (se 1 (by rfl) ⟨988736, by rfl⟩ : syracuseStep 1318315 = 1977473) B1977473
theorem B3857843 : Blo 1170402 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B3956147 : Blo 1170402 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B1170871 : Blo 1170402 1170871 := bstep (se 1 (by rfl) ⟨878153, by rfl⟩ : syracuseStep 1170871 = 1756307) B1756307
theorem B1170891 : Blo 1170402 1170891 := bstep (se 1 (by rfl) ⟨878168, by rfl⟩ : syracuseStep 1170891 = 1756337) B1756337
theorem B1170903 : Blo 1170402 1170903 := bstep (se 1 (by rfl) ⟨878177, by rfl⟩ : syracuseStep 1170903 = 1756355) B1756355
theorem B1170923 : Blo 1170402 1170923 := bstep (se 1 (by rfl) ⟨878192, by rfl⟩ : syracuseStep 1170923 = 1756385) B1756385
theorem B1170935 : Blo 1170402 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B1875467 : Blo 1170402 1875467 := bstep (se 1 (by rfl) ⟨1406600, by rfl⟩ : syracuseStep 1875467 = 2813201) B2813201
theorem B1170955 : Blo 1170402 1170955 := bstep (se 1 (by rfl) ⟨878216, by rfl⟩ : syracuseStep 1170955 = 1756433) B1756433
theorem B2637323 : Blo 1170402 2637323 := bstep (se 1 (by rfl) ⟨1977992, by rfl⟩ : syracuseStep 2637323 = 3955985) B3955985
theorem B1170967 : Blo 1170402 1170967 := bstep (se 1 (by rfl) ⟨878225, by rfl⟩ : syracuseStep 1170967 = 1756451) B1756451
theorem B1318423 : Blo 1170402 1318423 := bstep (se 1 (by rfl) ⟨988817, by rfl⟩ : syracuseStep 1318423 = 1977635) B1977635
theorem B1170987 : Blo 1170402 1170987 := bstep (se 1 (by rfl) ⟨878240, by rfl⟩ : syracuseStep 1170987 = 1756481) B1756481
theorem B1170999 : Blo 1170402 1170999 := bstep (se 1 (by rfl) ⟨878249, by rfl⟩ : syracuseStep 1170999 = 1756499) B1756499
theorem B2637377 : Blo 1170402 2637377 := bstep (se 2 (by rfl) ⟨989016, by rfl⟩ : syracuseStep 2637377 = 1978033) B1978033
theorem B3333707 : Blo 1170402 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1171019 : Blo 1170402 1171019 := bstep (se 1 (by rfl) ⟨878264, by rfl⟩ : syracuseStep 1171019 = 1756529) B1756529
theorem B1171031 : Blo 1170402 1171031 := bstep (se 1 (by rfl) ⟨878273, by rfl⟩ : syracuseStep 1171031 = 1756547) B1756547
theorem B1171051 : Blo 1170402 1171051 := bstep (se 1 (by rfl) ⟨878288, by rfl⟩ : syracuseStep 1171051 = 1756577) B1756577
theorem B1171063 : Blo 1170402 1171063 := bstep (se 1 (by rfl) ⟨878297, by rfl⟩ : syracuseStep 1171063 = 1756595) B1756595
theorem B1171083 : Blo 1170402 1171083 := bstep (se 1 (by rfl) ⟨878312, by rfl⟩ : syracuseStep 1171083 = 1756625) B1756625
theorem B1171095 : Blo 1170402 1171095 := bstep (se 1 (by rfl) ⟨878321, by rfl⟩ : syracuseStep 1171095 = 1756643) B1756643
theorem B1482391 : Blo 1170402 1482391 := bstep (se 1 (by rfl) ⟨1111793, by rfl⟩ : syracuseStep 1482391 = 2223587) B2223587
theorem B1171115 : Blo 1170402 1171115 := bstep (se 1 (by rfl) ⟨878336, by rfl⟩ : syracuseStep 1171115 = 1756673) B1756673
theorem B1171127 : Blo 1170402 1171127 := bstep (se 1 (by rfl) ⟨878345, by rfl⟩ : syracuseStep 1171127 = 1756691) B1756691
theorem B3956417 : Blo 1170402 3956417 := bstep (se 2 (by rfl) ⟨1483656, by rfl⟩ : syracuseStep 3956417 = 2967313) B2967313
theorem B1171147 : Blo 1170402 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B1318603 : Blo 1170402 1318603 := bstep (se 1 (by rfl) ⟨988952, by rfl⟩ : syracuseStep 1318603 = 1977905) B1977905
theorem B36052685 : Blo 1170402 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B1171159 : Blo 1170402 1171159 := bstep (se 1 (by rfl) ⟨878369, by rfl⟩ : syracuseStep 1171159 = 1756739) B1756739
theorem B1171179 : Blo 1170402 1171179 := bstep (se 1 (by rfl) ⟨878384, by rfl⟩ : syracuseStep 1171179 = 1756769) B1756769
theorem B1171191 : Blo 1170402 1171191 := bstep (se 1 (by rfl) ⟨878393, by rfl⟩ : syracuseStep 1171191 = 1756787) B1756787
theorem B13336325 : Blo 1170402 13336325 := bstep (se 4 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 13336325 = 2500561) B2500561
theorem B1171211 : Blo 1170402 1171211 := bstep (se 1 (by rfl) ⟨878408, by rfl⟩ : syracuseStep 1171211 = 1756817) B1756817
theorem B1171223 : Blo 1170402 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B2637593 : Blo 1170402 2637593 := bstep (se 2 (by rfl) ⟨989097, by rfl⟩ : syracuseStep 2637593 = 1978195) B1978195
theorem B1171243 : Blo 1170402 1171243 := bstep (se 1 (by rfl) ⟨878432, by rfl⟩ : syracuseStep 1171243 = 1756865) B1756865
theorem B8437549 : Blo 1170402 8437549 := bstep (se 3 (by rfl) ⟨1582040, by rfl⟩ : syracuseStep 8437549 = 3164081) B3164081
theorem B1171255 : Blo 1170402 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B1318711 : Blo 1170402 1318711 := bstep (se 1 (by rfl) ⟨989033, by rfl⟩ : syracuseStep 1318711 = 1978067) B1978067
theorem B4218689 : Blo 1170402 4218689 := bstep (se 2 (by rfl) ⟨1582008, by rfl⟩ : syracuseStep 4218689 = 3164017) B3164017
theorem B1171275 : Blo 1170402 1171275 := bstep (se 1 (by rfl) ⟨878456, by rfl⟩ : syracuseStep 1171275 = 1756913) B1756913
theorem B1171287 : Blo 1170402 1171287 := bstep (se 1 (by rfl) ⟨878465, by rfl⟩ : syracuseStep 1171287 = 1756931) B1756931
theorem B1171307 : Blo 1170402 1171307 := bstep (se 1 (by rfl) ⟨878480, by rfl⟩ : syracuseStep 1171307 = 1756961) B1756961
theorem B2637683 : Blo 1170402 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B1171319 : Blo 1170402 1171319 := bstep (se 1 (by rfl) ⟨878489, by rfl⟩ : syracuseStep 1171319 = 1756979) B1756979
theorem B1171339 : Blo 1170402 1171339 := bstep (se 1 (by rfl) ⟨878504, by rfl⟩ : syracuseStep 1171339 = 1757009) B1757009
theorem B1900439 : Blo 1170402 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B1171351 : Blo 1170402 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B2604953 : Blo 1170402 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B2637719 : Blo 1170402 2637719 := bstep (se 1 (by rfl) ⟨1978289, by rfl⟩ : syracuseStep 2637719 = 3956579) B3956579
theorem B1171371 : Blo 1170402 1171371 := bstep (se 1 (by rfl) ⟨878528, by rfl⟩ : syracuseStep 1171371 = 1757057) B1757057
theorem B1171383 : Blo 1170402 1171383 := bstep (se 1 (by rfl) ⟨878537, by rfl⟩ : syracuseStep 1171383 = 1757075) B1757075
theorem B1171403 : Blo 1170402 1171403 := bstep (se 1 (by rfl) ⟨878552, by rfl⟩ : syracuseStep 1171403 = 1757105) B1757105
theorem B5005259 : Blo 1170402 5005259 := bstep (se 1 (by rfl) ⟨3753944, by rfl⟩ : syracuseStep 5005259 = 7507889) B7507889
theorem B1171415 : Blo 1170402 1171415 := bstep (se 1 (by rfl) ⟨878561, by rfl⟩ : syracuseStep 1171415 = 1757123) B1757123
theorem B1171435 : Blo 1170402 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B1318891 : Blo 1170402 1318891 := bstep (se 1 (by rfl) ⟨989168, by rfl⟩ : syracuseStep 1318891 = 1978337) B1978337
theorem B1171447 : Blo 1170402 1171447 := bstep (se 1 (by rfl) ⟨878585, by rfl⟩ : syracuseStep 1171447 = 1757171) B1757171
theorem B1171463 : Blo 1170402 1171463 := bstep (se 1 (by rfl) ⟨878597, by rfl⟩ : syracuseStep 1171463 = 1757195) B1757195
theorem B4448267 : Blo 1170402 4448267 := bstep (se 1 (by rfl) ⟨3336200, by rfl⟩ : syracuseStep 4448267 = 6672401) B6672401
theorem B1171471 : Blo 1170402 1171471 := bstep (se 1 (by rfl) ⟨878603, by rfl⟩ : syracuseStep 1171471 = 1757207) B1757207
theorem B1318927 : Blo 1170402 1318927 := bstep (se 1 (by rfl) ⟨989195, by rfl⟩ : syracuseStep 1318927 = 1978391) B1978391
theorem B2670635 : Blo 1170402 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1171515 : Blo 1170402 1171515 := bstep (se 1 (by rfl) ⟨878636, by rfl⟩ : syracuseStep 1171515 = 1757273) B1757273
theorem B8888453 : Blo 1170402 8888453 := bstep (se 4 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 8888453 = 1666585) B1666585
theorem B1171591 : Blo 1170402 1171591 := bstep (se 1 (by rfl) ⟨878693, by rfl⟩ : syracuseStep 1171591 = 1757387) B1757387
theorem B1482887 : Blo 1170402 1482887 := bstep (se 1 (by rfl) ⟨1112165, by rfl⟩ : syracuseStep 1482887 = 2224331) B2224331
theorem B1171599 : Blo 1170402 1171599 := bstep (se 1 (by rfl) ⟨878699, by rfl⟩ : syracuseStep 1171599 = 1757399) B1757399
theorem B1171643 : Blo 1170402 1171643 := bstep (se 1 (by rfl) ⟨878732, by rfl⟩ : syracuseStep 1171643 = 1757465) B1757465
theorem B3563777 : Blo 1170402 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B1171719 : Blo 1170402 1171719 := bstep (se 1 (by rfl) ⟨878789, by rfl⟩ : syracuseStep 1171719 = 1757579) B1757579
theorem B1171727 : Blo 1170402 1171727 := bstep (se 1 (by rfl) ⟨878795, by rfl⟩ : syracuseStep 1171727 = 1757591) B1757591
theorem B1171771 : Blo 1170402 1171771 := bstep (se 1 (by rfl) ⟨878828, by rfl⟩ : syracuseStep 1171771 = 1757657) B1757657
theorem B1171847 : Blo 1170402 1171847 := bstep (se 1 (by rfl) ⟨878885, by rfl⟩ : syracuseStep 1171847 = 1757771) B1757771
theorem B1171855 : Blo 1170402 1171855 := bstep (se 1 (by rfl) ⟨878891, by rfl⟩ : syracuseStep 1171855 = 1757783) B1757783
theorem B1171899 : Blo 1170402 1171899 := bstep (se 1 (by rfl) ⟨878924, by rfl⟩ : syracuseStep 1171899 = 1757849) B1757849
theorem B5931467 : Blo 1170402 5931467 := bstep (se 1 (by rfl) ⟨4448600, by rfl⟩ : syracuseStep 5931467 = 8897201) B8897201
theorem B2966017 : Blo 1170402 2966017 := bstep (se 2 (by rfl) ⟨1112256, by rfl⟩ : syracuseStep 2966017 = 2224513) B2224513
theorem B1171975 : Blo 1170402 1171975 := bstep (se 1 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 1171975 = 1757963) B1757963
theorem B1171983 : Blo 1170402 1171983 := bstep (se 1 (by rfl) ⟨878987, by rfl⟩ : syracuseStep 1171983 = 1757975) B1757975
theorem B2671147 : Blo 1170402 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B3007019 : Blo 1170402 3007019 := bstep (se 1 (by rfl) ⟨2255264, by rfl⟩ : syracuseStep 3007019 = 4510529) B4510529
theorem B1172027 : Blo 1170402 1172027 := bstep (se 1 (by rfl) ⟨879020, by rfl⟩ : syracuseStep 1172027 = 1758041) B1758041
theorem B1172103 : Blo 1170402 1172103 := bstep (se 1 (by rfl) ⟨879077, by rfl⟩ : syracuseStep 1172103 = 1758155) B1758155
theorem B1172111 : Blo 1170402 1172111 := bstep (se 1 (by rfl) ⟨879083, by rfl⟩ : syracuseStep 1172111 = 1758167) B1758167
theorem B1172155 : Blo 1170402 1172155 := bstep (se 1 (by rfl) ⟨879116, by rfl⟩ : syracuseStep 1172155 = 1758233) B1758233
theorem B1172231 : Blo 1170402 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B5931791 : Blo 1170402 5931791 := bstep (se 1 (by rfl) ⟨4448843, by rfl⟩ : syracuseStep 5931791 = 8897687) B8897687
theorem B1483535 : Blo 1170402 1483535 := bstep (se 1 (by rfl) ⟨1112651, by rfl⟩ : syracuseStep 1483535 = 2225303) B2225303
theorem B1172239 : Blo 1170402 1172239 := bstep (se 1 (by rfl) ⟨879179, by rfl⟩ : syracuseStep 1172239 = 1758359) B1758359
theorem B24044323 : Blo 1170402 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B9012005 : Blo 1170402 9012005 := bstep (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) B1689751
theorem B1172283 : Blo 1170402 1172283 := bstep (se 1 (by rfl) ⟨879212, by rfl⟩ : syracuseStep 1172283 = 1758425) B1758425
theorem B1172359 : Blo 1170402 1172359 := bstep (se 1 (by rfl) ⟨879269, by rfl⟩ : syracuseStep 1172359 = 1758539) B1758539
theorem B1172367 : Blo 1170402 1172367 := bstep (se 1 (by rfl) ⟨879275, by rfl⟩ : syracuseStep 1172367 = 1758551) B1758551
theorem B10838947 : Blo 1170402 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B1975225 : Blo 1170402 1975225 := bstep (se 2 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 1975225 = 1481419) B1481419
theorem B3753047 : Blo 1170402 3753047 := bstep (se 1 (by rfl) ⟨2814785, by rfl⟩ : syracuseStep 3753047 = 5629571) B5629571
theorem B2966615 : Blo 1170402 2966615 := bstep (se 1 (by rfl) ⟨2224961, by rfl⟩ : syracuseStep 2966615 = 4449923) B4449923
theorem B6669485 : Blo 1170402 6669485 := bstep (se 3 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 6669485 = 2501057) B2501057
theorem B6767873 : Blo 1170402 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B2966827 : Blo 1170402 2966827 := bstep (se 1 (by rfl) ⟨2225120, by rfl⟩ : syracuseStep 2966827 = 4450241) B4450241
theorem B4220275 : Blo 1170402 4220275 := bstep (se 1 (by rfl) ⟨3165206, by rfl⟩ : syracuseStep 4220275 = 6330413) B6330413
theorem B2139527 : Blo 1170402 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B2966969 : Blo 1170402 2966969 := bstep (se 2 (by rfl) ⟨1112613, by rfl⟩ : syracuseStep 2966969 = 2225227) B2225227
theorem B1975927 : Blo 1170402 1975927 := bstep (se 1 (by rfl) ⟨1481945, by rfl⟩ : syracuseStep 1975927 = 2963891) B2963891
theorem B3950369 : Blo 1170402 3950369 := bstep (se 2 (by rfl) ⟨1481388, by rfl⟩ : syracuseStep 3950369 = 2962777) B2962777
theorem B1976123 : Blo 1170402 1976123 := bstep (se 1 (by rfl) ⟨1482092, by rfl⟩ : syracuseStep 1976123 = 2964185) B2964185
theorem B3335995 : Blo 1170402 3335995 := bstep (se 1 (by rfl) ⟨2501996, by rfl⟩ : syracuseStep 3335995 = 5003993) B5003993
theorem B3164039 : Blo 1170402 3164039 := bstep (se 1 (by rfl) ⟨2373029, by rfl⟩ : syracuseStep 3164039 = 4746059) B4746059
theorem B4450423 : Blo 1170402 4450423 := bstep (se 1 (by rfl) ⟨3337817, by rfl⟩ : syracuseStep 4450423 = 6675635) B6675635
theorem B12667013 : Blo 1170402 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B11249837 : Blo 1170402 11249837 := bstep (se 3 (by rfl) ⟨2109344, by rfl⟩ : syracuseStep 11249837 = 4218689) B4218689
theorem B5933249 : Blo 1170402 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B1976521 : Blo 1170402 1976521 := bstep (se 2 (by rfl) ⟨741195, by rfl⟩ : syracuseStep 1976521 = 1482391) B1482391
theorem B2812171 : Blo 1170402 2812171 := bstep (se 1 (by rfl) ⟨2109128, by rfl⟩ : syracuseStep 2812171 = 4218257) B4218257
theorem B3950963 : Blo 1170402 3950963 := bstep (se 1 (by rfl) ⟨2963222, by rfl⟩ : syracuseStep 3950963 = 5926445) B5926445
theorem B2222471 : Blo 1170402 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B11250065 : Blo 1170402 11250065 := bstep (se 2 (by rfl) ⟨4218774, by rfl⟩ : syracuseStep 11250065 = 8437549) B8437549
theorem B5630417 : Blo 1170402 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B8890883 : Blo 1170402 8890883 := bstep (se 1 (by rfl) ⟨6668162, by rfl⟩ : syracuseStep 8890883 = 13336325) B13336325
theorem B1755707 : Blo 1170402 1755707 := bstep (se 1 (by rfl) ⟨1316780, by rfl⟩ : syracuseStep 1755707 = 2633561) B2633561
theorem B1755767 : Blo 1170402 1755767 := bstep (se 1 (by rfl) ⟨1316825, by rfl⟩ : syracuseStep 1755767 = 2633651) B2633651
theorem B3336839 : Blo 1170402 3336839 := bstep (se 1 (by rfl) ⟨2502629, by rfl⟩ : syracuseStep 3336839 = 5005259) B5005259
theorem B1755791 : Blo 1170402 1755791 := bstep (se 1 (by rfl) ⟨1316843, by rfl⟩ : syracuseStep 1755791 = 2633687) B2633687
theorem B1501867 : Blo 1170402 1501867 := bstep (se 1 (by rfl) ⟨1126400, by rfl⟩ : syracuseStep 1501867 = 2252801) B2252801
theorem B1755833 : Blo 1170402 1755833 := bstep (se 2 (by rfl) ⟨658437, by rfl⟩ : syracuseStep 1755833 = 1316875) B1316875
theorem B1755911 : Blo 1170402 1755911 := bstep (se 1 (by rfl) ⟨1316933, by rfl⟩ : syracuseStep 1755911 = 2633867) B2633867
theorem B1755947 : Blo 1170402 1755947 := bstep (se 1 (by rfl) ⟨1316960, by rfl⟩ : syracuseStep 1755947 = 2633921) B2633921
theorem B1755977 : Blo 1170402 1755977 := bstep (se 2 (by rfl) ⟨658491, by rfl⟩ : syracuseStep 1755977 = 1316983) B1316983
theorem B1977223 : Blo 1170402 1977223 := bstep (se 1 (by rfl) ⟨1482917, by rfl⟩ : syracuseStep 1977223 = 2965835) B2965835
theorem B1756091 : Blo 1170402 1756091 := bstep (se 1 (by rfl) ⟨1317068, by rfl⟩ : syracuseStep 1756091 = 2634137) B2634137
theorem B1756151 : Blo 1170402 1756151 := bstep (se 1 (by rfl) ⟨1317113, by rfl⟩ : syracuseStep 1756151 = 2634227) B2634227
theorem B1756175 : Blo 1170402 1756175 := bstep (se 1 (by rfl) ⟨1317131, by rfl⟩ : syracuseStep 1756175 = 2634263) B2634263
theorem B1756217 : Blo 1170402 1756217 := bstep (se 2 (by rfl) ⟨658581, by rfl⟩ : syracuseStep 1756217 = 1317163) B1317163
theorem B4451395 : Blo 1170402 4451395 := bstep (se 1 (by rfl) ⟨3338546, by rfl⟩ : syracuseStep 4451395 = 6677093) B6677093
theorem B1756295 : Blo 1170402 1756295 := bstep (se 1 (by rfl) ⟨1317221, by rfl⟩ : syracuseStep 1756295 = 2634443) B2634443
theorem B1756331 : Blo 1170402 1756331 := bstep (se 1 (by rfl) ⟨1317248, by rfl⟩ : syracuseStep 1756331 = 2634497) B2634497
theorem B1756361 : Blo 1170402 1756361 := bstep (se 2 (by rfl) ⟨658635, by rfl⟩ : syracuseStep 1756361 = 1317271) B1317271
theorem B4582637 : Blo 1170402 4582637 := bstep (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) B1718489
theorem B3378461 : Blo 1170402 3378461 := bstep (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) B1266923
theorem B2501921 : Blo 1170402 2501921 := bstep (se 2 (by rfl) ⟨938220, by rfl⟩ : syracuseStep 2501921 = 1876441) B1876441
theorem B1756475 : Blo 1170402 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B1756535 : Blo 1170402 1756535 := bstep (se 1 (by rfl) ⟨1317401, by rfl⟩ : syracuseStep 1756535 = 2634803) B2634803
theorem B1756559 : Blo 1170402 1756559 := bstep (se 1 (by rfl) ⟨1317419, by rfl⟩ : syracuseStep 1756559 = 2634839) B2634839
theorem B3337625 : Blo 1170402 3337625 := bstep (se 2 (by rfl) ⟨1251609, by rfl⟩ : syracuseStep 3337625 = 2503219) B2503219
theorem B1666489 : Blo 1170402 1666489 := bstep (se 2 (by rfl) ⟨624933, by rfl⟩ : syracuseStep 1666489 = 1249867) B1249867
theorem B1756601 : Blo 1170402 1756601 := bstep (se 2 (by rfl) ⟨658725, by rfl⟩ : syracuseStep 1756601 = 1317451) B1317451
theorem B9629113 : Blo 1170402 9629113 := bstep (se 2 (by rfl) ⟨3610917, by rfl⟩ : syracuseStep 9629113 = 7221835) B7221835
theorem B10014137 : Blo 1170402 10014137 := bstep (se 2 (by rfl) ⟨3755301, by rfl⟩ : syracuseStep 10014137 = 7510603) B7510603
theorem B5934545 : Blo 1170402 5934545 := bstep (se 2 (by rfl) ⟨2225454, by rfl⟩ : syracuseStep 5934545 = 4450909) B4450909
theorem B5631491 : Blo 1170402 5631491 := bstep (se 1 (by rfl) ⟨4223618, by rfl⟩ : syracuseStep 5631491 = 8447237) B8447237
theorem B1756679 : Blo 1170402 1756679 := bstep (se 1 (by rfl) ⟨1317509, by rfl⟩ : syracuseStep 1756679 = 2635019) B2635019
theorem B1977871 : Blo 1170402 1977871 := bstep (se 1 (by rfl) ⟨1483403, by rfl⟩ : syracuseStep 1977871 = 2966807) B2966807
theorem B1756715 : Blo 1170402 1756715 := bstep (se 1 (by rfl) ⟨1317536, by rfl⟩ : syracuseStep 1756715 = 2635073) B2635073
theorem B3427883 : Blo 1170402 3427883 := bstep (se 1 (by rfl) ⟨2570912, by rfl⟩ : syracuseStep 3427883 = 5141825) B5141825
theorem B1756745 : Blo 1170402 1756745 := bstep (se 2 (by rfl) ⟨658779, by rfl⟩ : syracuseStep 1756745 = 1317559) B1317559
theorem B16019045 : Blo 1170402 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B2813555 : Blo 1170402 2813555 := bstep (se 1 (by rfl) ⟨2110166, by rfl⟩ : syracuseStep 2813555 = 4220333) B4220333
theorem B1756859 : Blo 1170402 1756859 := bstep (se 1 (by rfl) ⟨1317644, by rfl⟩ : syracuseStep 1756859 = 2635289) B2635289
theorem B2633417 : Blo 1170402 2633417 := bstep (se 2 (by rfl) ⟨987531, by rfl⟩ : syracuseStep 2633417 = 1975063) B1975063
theorem B1756919 : Blo 1170402 1756919 := bstep (se 1 (by rfl) ⟨1317689, by rfl⟩ : syracuseStep 1756919 = 2635379) B2635379
theorem B1756943 : Blo 1170402 1756943 := bstep (se 1 (by rfl) ⟨1317707, by rfl⟩ : syracuseStep 1756943 = 2635415) B2635415
theorem B21376817 : Blo 1170402 21376817 := bstep (se 2 (by rfl) ⟨8016306, by rfl⟩ : syracuseStep 21376817 = 16032613) B16032613
theorem B10014515 : Blo 1170402 10014515 := bstep (se 1 (by rfl) ⟨7510886, by rfl⟩ : syracuseStep 10014515 = 15021773) B15021773
theorem B1756985 : Blo 1170402 1756985 := bstep (se 2 (by rfl) ⟨658869, by rfl⟩ : syracuseStep 1756985 = 1317739) B1317739
theorem B2813815 : Blo 1170402 2813815 := bstep (se 1 (by rfl) ⟨2110361, by rfl⟩ : syracuseStep 2813815 = 4220723) B4220723
theorem B1757063 : Blo 1170402 1757063 := bstep (se 1 (by rfl) ⟨1317797, by rfl⟩ : syracuseStep 1757063 = 2635595) B2635595
theorem B1757099 : Blo 1170402 1757099 := bstep (se 1 (by rfl) ⟨1317824, by rfl⟩ : syracuseStep 1757099 = 2635649) B2635649
theorem B1757129 : Blo 1170402 1757129 := bstep (se 2 (by rfl) ⟨658923, by rfl⟩ : syracuseStep 1757129 = 1317847) B1317847
theorem B7606219 : Blo 1170402 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B2224073 : Blo 1170402 2224073 := bstep (se 2 (by rfl) ⟨834027, by rfl⟩ : syracuseStep 2224073 = 1668055) B1668055
theorem B7221251 : Blo 1170402 7221251 := bstep (se 1 (by rfl) ⟨5415938, by rfl⟩ : syracuseStep 7221251 = 10831877) B10831877
theorem B3338273 : Blo 1170402 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B5001259 : Blo 1170402 5001259 := bstep (se 1 (by rfl) ⟨3750944, by rfl⟩ : syracuseStep 5001259 = 7501889) B7501889
theorem B1978411 : Blo 1170402 1978411 := bstep (se 1 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 1978411 = 2967617) B2967617
theorem B1757243 : Blo 1170402 1757243 := bstep (se 1 (by rfl) ⟨1317932, by rfl⟩ : syracuseStep 1757243 = 2635865) B2635865
theorem B6328381 : Blo 1170402 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B1757303 : Blo 1170402 1757303 := bstep (se 1 (by rfl) ⟨1317977, by rfl⟩ : syracuseStep 1757303 = 2635955) B2635955
theorem B1757327 : Blo 1170402 1757327 := bstep (se 1 (by rfl) ⟨1317995, by rfl⟩ : syracuseStep 1757327 = 2635991) B2635991
theorem B1757369 : Blo 1170402 1757369 := bstep (se 2 (by rfl) ⟨659013, by rfl⟩ : syracuseStep 1757369 = 1318027) B1318027
theorem B2814209 : Blo 1170402 2814209 := bstep (se 2 (by rfl) ⟨1055328, by rfl⟩ : syracuseStep 2814209 = 2110657) B2110657
theorem B1757447 : Blo 1170402 1757447 := bstep (se 1 (by rfl) ⟨1318085, by rfl⟩ : syracuseStep 1757447 = 2636171) B2636171
theorem B1757483 : Blo 1170402 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B2502971 : Blo 1170402 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B1757513 : Blo 1170402 1757513 := bstep (se 2 (by rfl) ⟨659067, by rfl⟩ : syracuseStep 1757513 = 1318135) B1318135
theorem B2634119 : Blo 1170402 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B11260295 : Blo 1170402 11260295 := bstep (se 1 (by rfl) ⟨8445221, by rfl⟩ : syracuseStep 11260295 = 16890443) B16890443
theorem B1757627 : Blo 1170402 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B1757687 : Blo 1170402 1757687 := bstep (se 1 (by rfl) ⟨1318265, by rfl⟩ : syracuseStep 1757687 = 2636531) B2636531
theorem B1757711 : Blo 1170402 1757711 := bstep (se 1 (by rfl) ⟨1318283, by rfl⟩ : syracuseStep 1757711 = 2636567) B2636567
theorem B1757753 : Blo 1170402 1757753 := bstep (se 2 (by rfl) ⟨659157, by rfl⟩ : syracuseStep 1757753 = 1318315) B1318315
theorem B2634299 : Blo 1170402 2634299 := bstep (se 1 (by rfl) ⟨1975724, by rfl⟩ : syracuseStep 2634299 = 3951449) B3951449
theorem B1667719 : Blo 1170402 1667719 := bstep (se 1 (by rfl) ⟨1250789, by rfl⟩ : syracuseStep 1667719 = 2501579) B2501579
theorem B1757831 : Blo 1170402 1757831 := bstep (se 1 (by rfl) ⟨1318373, by rfl⟩ : syracuseStep 1757831 = 2636747) B2636747
theorem B1757867 : Blo 1170402 1757867 := bstep (se 1 (by rfl) ⟨1318400, by rfl⟩ : syracuseStep 1757867 = 2636801) B2636801
theorem B2634425 : Blo 1170402 2634425 := bstep (se 2 (by rfl) ⟨987909, by rfl⟩ : syracuseStep 2634425 = 1975819) B1975819
theorem B1757897 : Blo 1170402 1757897 := bstep (se 2 (by rfl) ⟨659211, by rfl⟩ : syracuseStep 1757897 = 1318423) B1318423
theorem B1758011 : Blo 1170402 1758011 := bstep (se 1 (by rfl) ⟨1318508, by rfl⟩ : syracuseStep 1758011 = 2637017) B2637017
theorem B1758071 : Blo 1170402 1758071 := bstep (se 1 (by rfl) ⟨1318553, by rfl⟩ : syracuseStep 1758071 = 2637107) B2637107
theorem B4445063 : Blo 1170402 4445063 := bstep (se 1 (by rfl) ⟨3333797, by rfl⟩ : syracuseStep 4445063 = 6667595) B6667595
theorem B1758095 : Blo 1170402 1758095 := bstep (se 1 (by rfl) ⟨1318571, by rfl⟩ : syracuseStep 1758095 = 2637143) B2637143
theorem B3953555 : Blo 1170402 3953555 := bstep (se 1 (by rfl) ⟨2965166, by rfl⟩ : syracuseStep 3953555 = 5930333) B5930333
theorem B5632915 : Blo 1170402 5632915 := bstep (se 1 (by rfl) ⟨4224686, by rfl⟩ : syracuseStep 5632915 = 8449373) B8449373
theorem B1758137 : Blo 1170402 1758137 := bstep (se 2 (by rfl) ⟨659301, by rfl⟩ : syracuseStep 1758137 = 1318603) B1318603
theorem B2814977 : Blo 1170402 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B1250311 : Blo 1170402 1250311 := bstep (se 1 (by rfl) ⟨937733, by rfl⟩ : syracuseStep 1250311 = 1875467) B1875467
theorem B1758215 : Blo 1170402 1758215 := bstep (se 1 (by rfl) ⟨1318661, by rfl⟩ : syracuseStep 1758215 = 2637323) B2637323
theorem B2634767 : Blo 1170402 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B2634785 : Blo 1170402 2634785 := bstep (se 2 (by rfl) ⟨988044, by rfl⟩ : syracuseStep 2634785 = 1976089) B1976089
theorem B1758251 : Blo 1170402 1758251 := bstep (se 1 (by rfl) ⟨1318688, by rfl⟩ : syracuseStep 1758251 = 2637377) B2637377
theorem B2503723 : Blo 1170402 2503723 := bstep (se 1 (by rfl) ⟨1877792, by rfl⟩ : syracuseStep 2503723 = 3755585) B3755585
theorem B1758281 : Blo 1170402 1758281 := bstep (se 2 (by rfl) ⟨659355, by rfl⟩ : syracuseStep 1758281 = 1318711) B1318711
theorem B1758395 : Blo 1170402 1758395 := bstep (se 1 (by rfl) ⟨1318796, by rfl⟩ : syracuseStep 1758395 = 2637593) B2637593
theorem B1758455 : Blo 1170402 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B1266959 : Blo 1170402 1266959 := bstep (se 1 (by rfl) ⟨950219, by rfl⟩ : syracuseStep 1266959 = 1900439) B1900439
theorem B1758479 : Blo 1170402 1758479 := bstep (se 1 (by rfl) ⟨1318859, by rfl⟩ : syracuseStep 1758479 = 2637719) B2637719
theorem B1758521 : Blo 1170402 1758521 := bstep (se 2 (by rfl) ⟨659445, by rfl⟩ : syracuseStep 1758521 = 1318891) B1318891
theorem B2635127 : Blo 1170402 2635127 := bstep (se 1 (by rfl) ⟨1976345, by rfl⟩ : syracuseStep 2635127 = 3952691) B3952691
theorem B1758599 : Blo 1170402 1758599 := bstep (se 1 (by rfl) ⟨1318949, by rfl⟩ : syracuseStep 1758599 = 2637899) B2637899
theorem B1668539 : Blo 1170402 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B2962889 : Blo 1170402 2962889 := bstep (se 2 (by rfl) ⟨1111083, by rfl⟩ : syracuseStep 2962889 = 2222167) B2222167
theorem B13342157 : Blo 1170402 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B2635307 : Blo 1170402 2635307 := bstep (se 1 (by rfl) ⟨1976480, by rfl⟩ : syracuseStep 2635307 = 3952961) B3952961
theorem B6674177 : Blo 1170402 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B8017679 : Blo 1170402 8017679 := bstep (se 1 (by rfl) ⟨6013259, by rfl⟩ : syracuseStep 8017679 = 12026519) B12026519
theorem B2963243 : Blo 1170402 2963243 := bstep (se 1 (by rfl) ⟨2222432, by rfl⟩ : syracuseStep 2963243 = 4444865) B4444865
theorem B2373419 : Blo 1170402 2373419 := bstep (se 1 (by rfl) ⟨1780064, by rfl⟩ : syracuseStep 2373419 = 3560129) B3560129
theorem B1251131 : Blo 1170402 1251131 := bstep (se 1 (by rfl) ⟨938348, by rfl⟩ : syracuseStep 1251131 = 1876697) B1876697
theorem B2635667 : Blo 1170402 2635667 := bstep (se 1 (by rfl) ⟨1976750, by rfl⟩ : syracuseStep 2635667 = 3953501) B3953501
theorem B6666137 : Blo 1170402 6666137 := bstep (se 2 (by rfl) ⟨2499801, by rfl⟩ : syracuseStep 6666137 = 4999603) B4999603
theorem B5707705 : Blo 1170402 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B2635721 : Blo 1170402 2635721 := bstep (se 2 (by rfl) ⟨988395, by rfl⟩ : syracuseStep 2635721 = 1976791) B1976791
theorem B10000331 : Blo 1170402 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B1669177 : Blo 1170402 1669177 := bstep (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) B1251883
theorem B16898165 : Blo 1170402 16898165 := bstep (se 5 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 16898165 = 1584203) B1584203
theorem B6674633 : Blo 1170402 6674633 := bstep (se 2 (by rfl) ⟨2502987, by rfl⟩ : syracuseStep 6674633 = 5005975) B5005975
theorem B5347565 : Blo 1170402 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B1317127 : Blo 1170402 1317127 := bstep (se 1 (by rfl) ⟨987845, by rfl⟩ : syracuseStep 1317127 = 1975691) B1975691
theorem B3954959 : Blo 1170402 3954959 := bstep (se 1 (by rfl) ⟨2966219, by rfl⟩ : syracuseStep 3954959 = 5932439) B5932439
theorem B3168571 : Blo 1170402 3168571 := bstep (se 1 (by rfl) ⟨2376428, by rfl⟩ : syracuseStep 3168571 = 4752857) B4752857
theorem B5929361 : Blo 1170402 5929361 := bstep (se 2 (by rfl) ⟨2223510, by rfl⟩ : syracuseStep 5929361 = 4447021) B4447021
theorem B22509971 : Blo 1170402 22509971 := bstep (se 1 (by rfl) ⟨16882478, by rfl⟩ : syracuseStep 22509971 = 33764957) B33764957
theorem B1317307 : Blo 1170402 1317307 := bstep (se 1 (by rfl) ⟨987980, by rfl⟩ : syracuseStep 1317307 = 1975961) B1975961
theorem B427571725 : Blo 1170402 427571725 := bstep (se 3 (by rfl) ⟨80169698, by rfl⟩ : syracuseStep 427571725 = 160339397) B160339397
theorem B3955229 : Blo 1170402 3955229 := bstep (se 3 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 3955229 = 1483211) B1483211
theorem B10001015 : Blo 1170402 10001015 := bstep (se 1 (by rfl) ⟨7500761, by rfl⟩ : syracuseStep 10001015 = 15001523) B15001523
theorem B4446839 : Blo 1170402 4446839 := bstep (se 1 (by rfl) ⟨3335129, by rfl⟩ : syracuseStep 4446839 = 6670259) B6670259
theorem B3005047 : Blo 1170402 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B1407623 : Blo 1170402 1407623 := bstep (se 1 (by rfl) ⟨1055717, by rfl⟩ : syracuseStep 1407623 = 2111435) B2111435
theorem B2636423 : Blo 1170402 2636423 := bstep (se 1 (by rfl) ⟨1977317, by rfl⟩ : syracuseStep 2636423 = 3954635) B3954635
theorem B5003977 : Blo 1170402 5003977 := bstep (se 2 (by rfl) ⟨1876491, by rfl⟩ : syracuseStep 5003977 = 3752983) B3752983
theorem B2964235 : Blo 1170402 2964235 := bstep (se 1 (by rfl) ⟨2223176, by rfl⟩ : syracuseStep 2964235 = 4446353) B4446353
theorem B2636603 : Blo 1170402 2636603 := bstep (se 1 (by rfl) ⟨1977452, by rfl⟩ : syracuseStep 2636603 = 3954905) B3954905
theorem B1481591 : Blo 1170402 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1317775 : Blo 1170402 1317775 := bstep (se 1 (by rfl) ⟨988331, by rfl⟩ : syracuseStep 1317775 = 1976663) B1976663
theorem B2964377 : Blo 1170402 2964377 := bstep (se 2 (by rfl) ⟨1111641, by rfl⟩ : syracuseStep 2964377 = 2223283) B2223283
theorem B2636729 : Blo 1170402 2636729 := bstep (se 2 (by rfl) ⟨988773, by rfl⟩ : syracuseStep 2636729 = 1977547) B1977547
theorem B1170439 : Blo 1170402 1170439 := bstep (se 1 (by rfl) ⟨877829, by rfl⟩ : syracuseStep 1170439 = 1755659) B1755659
theorem B16022539 : Blo 1170402 16022539 := bstep (se 1 (by rfl) ⟨12016904, by rfl⟩ : syracuseStep 16022539 = 24033809) B24033809
theorem B1170447 : Blo 1170402 1170447 := bstep (se 1 (by rfl) ⟨877835, by rfl⟩ : syracuseStep 1170447 = 1755671) B1755671
theorem B1481743 : Blo 1170402 1481743 := bstep (se 1 (by rfl) ⟨1111307, by rfl⟩ : syracuseStep 1481743 = 2222615) B2222615
theorem B1170491 : Blo 1170402 1170491 := bstep (se 1 (by rfl) ⟨877868, by rfl⟩ : syracuseStep 1170491 = 1755737) B1755737
theorem B2964539 : Blo 1170402 2964539 := bstep (se 1 (by rfl) ⟨2223404, by rfl⟩ : syracuseStep 2964539 = 4446809) B4446809
theorem B1170567 : Blo 1170402 1170567 := bstep (se 1 (by rfl) ⟨877925, by rfl⟩ : syracuseStep 1170567 = 1755851) B1755851
theorem B1170575 : Blo 1170402 1170575 := bstep (se 1 (by rfl) ⟨877931, by rfl⟩ : syracuseStep 1170575 = 1755863) B1755863
theorem B1170619 : Blo 1170402 1170619 := bstep (se 1 (by rfl) ⟨877964, by rfl⟩ : syracuseStep 1170619 = 1755929) B1755929
theorem B1481915 : Blo 1170402 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B1170695 : Blo 1170402 1170695 := bstep (se 1 (by rfl) ⟨878021, by rfl⟩ : syracuseStep 1170695 = 1756043) B1756043
theorem B1170703 : Blo 1170402 1170703 := bstep (se 1 (by rfl) ⟨878027, by rfl⟩ : syracuseStep 1170703 = 1756055) B1756055
theorem B2637071 : Blo 1170402 2637071 := bstep (se 1 (by rfl) ⟨1977803, by rfl⟩ : syracuseStep 2637071 = 3955607) B3955607
theorem B3751201 : Blo 1170402 3751201 := bstep (se 2 (by rfl) ⟨1406700, by rfl⟩ : syracuseStep 3751201 = 2813401) B2813401
theorem B2637089 : Blo 1170402 2637089 := bstep (se 2 (by rfl) ⟨988908, by rfl⟩ : syracuseStep 2637089 = 1977817) B1977817
theorem B1170747 : Blo 1170402 1170747 := bstep (se 1 (by rfl) ⟨878060, by rfl⟩ : syracuseStep 1170747 = 1756121) B1756121
theorem B5782873 : Blo 1170402 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B1170823 : Blo 1170402 1170823 := bstep (se 1 (by rfl) ⟨878117, by rfl⟩ : syracuseStep 1170823 = 1756235) B1756235
theorem B1318279 : Blo 1170402 1318279 := bstep (se 1 (by rfl) ⟨988709, by rfl⟩ : syracuseStep 1318279 = 1977419) B1977419
theorem B1170831 : Blo 1170402 1170831 := bstep (se 1 (by rfl) ⟨878123, by rfl⟩ : syracuseStep 1170831 = 1756247) B1756247
theorem B2964883 : Blo 1170402 2964883 := bstep (se 1 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 2964883 = 4447325) B4447325
theorem B1170875 : Blo 1170402 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B1170951 : Blo 1170402 1170951 := bstep (se 1 (by rfl) ⟨878213, by rfl⟩ : syracuseStep 1170951 = 1756427) B1756427
theorem B1170959 : Blo 1170402 1170959 := bstep (se 1 (by rfl) ⟨878219, by rfl⟩ : syracuseStep 1170959 = 1756439) B1756439
theorem B10010141 : Blo 1170402 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B2965025 : Blo 1170402 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B1171003 : Blo 1170402 1171003 := bstep (se 1 (by rfl) ⟨878252, by rfl⟩ : syracuseStep 1171003 = 1756505) B1756505
theorem B1318459 : Blo 1170402 1318459 := bstep (se 1 (by rfl) ⟨988844, by rfl⟩ : syracuseStep 1318459 = 1977689) B1977689
theorem B4447811 : Blo 1170402 4447811 := bstep (se 1 (by rfl) ⟨3335858, by rfl⟩ : syracuseStep 4447811 = 6671717) B6671717
theorem B1875575 : Blo 1170402 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B2571895 : Blo 1170402 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B2637431 : Blo 1170402 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B1171079 : Blo 1170402 1171079 := bstep (se 1 (by rfl) ⟨878309, by rfl⟩ : syracuseStep 1171079 = 1756619) B1756619
theorem B1171087 : Blo 1170402 1171087 := bstep (se 1 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 1171087 = 1756631) B1756631
theorem B1171131 : Blo 1170402 1171131 := bstep (se 1 (by rfl) ⟨878348, by rfl⟩ : syracuseStep 1171131 = 1756697) B1756697
theorem B8896229 : Blo 1170402 8896229 := bstep (se 4 (by rfl) ⟨834021, by rfl⟩ : syracuseStep 8896229 = 1668043) B1668043
theorem B6946541 : Blo 1170402 6946541 := bstep (se 3 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 6946541 = 2604953) B2604953
theorem B1171207 : Blo 1170402 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B3333899 : Blo 1170402 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B1171215 : Blo 1170402 1171215 := bstep (se 1 (by rfl) ⟨878411, by rfl⟩ : syracuseStep 1171215 = 1756823) B1756823
theorem B2637611 : Blo 1170402 2637611 := bstep (se 1 (by rfl) ⟨1978208, by rfl⟩ : syracuseStep 2637611 = 3956417) B3956417
theorem B24035123 : Blo 1170402 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B1171259 : Blo 1170402 1171259 := bstep (se 1 (by rfl) ⟨878444, by rfl⟩ : syracuseStep 1171259 = 1756889) B1756889
theorem B1171335 : Blo 1170402 1171335 := bstep (se 1 (by rfl) ⟨878501, by rfl⟩ : syracuseStep 1171335 = 1757003) B1757003
theorem B1171343 : Blo 1170402 1171343 := bstep (se 1 (by rfl) ⟨878507, by rfl⟩ : syracuseStep 1171343 = 1757015) B1757015
theorem B3006355 : Blo 1170402 3006355 := bstep (se 1 (by rfl) ⟨2254766, by rfl⟩ : syracuseStep 3006355 = 4509533) B4509533
theorem B5627801 : Blo 1170402 5627801 := bstep (se 2 (by rfl) ⟨2110425, by rfl⟩ : syracuseStep 5627801 = 4220851) B4220851
theorem B3956633 : Blo 1170402 3956633 := bstep (se 2 (by rfl) ⟨1483737, by rfl⟩ : syracuseStep 3956633 = 2967475) B2967475
theorem B12672931 : Blo 1170402 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B1171387 : Blo 1170402 1171387 := bstep (se 1 (by rfl) ⟨878540, by rfl⟩ : syracuseStep 1171387 = 1757081) B1757081
theorem B2965511 : Blo 1170402 2965511 := bstep (se 1 (by rfl) ⟨2224133, by rfl⟩ : syracuseStep 2965511 = 4448267) B4448267
theorem B1171495 : Blo 1170402 1171495 := bstep (se 1 (by rfl) ⟨878621, by rfl⟩ : syracuseStep 1171495 = 1757243) B1757243
theorem B6668345 : Blo 1170402 6668345 := bstep (se 2 (by rfl) ⟨2500629, by rfl⟩ : syracuseStep 6668345 = 5001259) B5001259
theorem B2637881 : Blo 1170402 2637881 := bstep (se 2 (by rfl) ⟨989205, by rfl⟩ : syracuseStep 2637881 = 1978411) B1978411
theorem B1171535 : Blo 1170402 1171535 := bstep (se 1 (by rfl) ⟨878651, by rfl⟩ : syracuseStep 1171535 = 1757303) B1757303
theorem B8437841 : Blo 1170402 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B1171551 : Blo 1170402 1171551 := bstep (se 1 (by rfl) ⟨878663, by rfl⟩ : syracuseStep 1171551 = 1757327) B1757327
theorem B1171579 : Blo 1170402 1171579 := bstep (se 1 (by rfl) ⟨878684, by rfl⟩ : syracuseStep 1171579 = 1757369) B1757369
theorem B1876139 : Blo 1170402 1876139 := bstep (se 1 (by rfl) ⟨1407104, by rfl⟩ : syracuseStep 1876139 = 2814209) B2814209
theorem B1171631 : Blo 1170402 1171631 := bstep (se 1 (by rfl) ⟨878723, by rfl⟩ : syracuseStep 1171631 = 1757447) B1757447
theorem B1171655 : Blo 1170402 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B1171675 : Blo 1170402 1171675 := bstep (se 1 (by rfl) ⟨878756, by rfl⟩ : syracuseStep 1171675 = 1757513) B1757513
theorem B14246117 : Blo 1170402 14246117 := bstep (se 4 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 14246117 = 2671147) B2671147
theorem B1171751 : Blo 1170402 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B36036917 : Blo 1170402 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B1171791 : Blo 1170402 1171791 := bstep (se 1 (by rfl) ⟨878843, by rfl⟩ : syracuseStep 1171791 = 1757687) B1757687
theorem B1171807 : Blo 1170402 1171807 := bstep (se 1 (by rfl) ⟨878855, by rfl⟩ : syracuseStep 1171807 = 1757711) B1757711
theorem B1171835 : Blo 1170402 1171835 := bstep (se 1 (by rfl) ⟨878876, by rfl⟩ : syracuseStep 1171835 = 1757753) B1757753
theorem B1171887 : Blo 1170402 1171887 := bstep (se 1 (by rfl) ⟨878915, by rfl⟩ : syracuseStep 1171887 = 1757831) B1757831
theorem B1171911 : Blo 1170402 1171911 := bstep (se 1 (by rfl) ⟨878933, by rfl⟩ : syracuseStep 1171911 = 1757867) B1757867
theorem B1171931 : Blo 1170402 1171931 := bstep (se 1 (by rfl) ⟨878948, by rfl⟩ : syracuseStep 1171931 = 1757897) B1757897
theorem B1172007 : Blo 1170402 1172007 := bstep (se 1 (by rfl) ⟨879005, by rfl⟩ : syracuseStep 1172007 = 1758011) B1758011
theorem B1172047 : Blo 1170402 1172047 := bstep (se 1 (by rfl) ⟨879035, by rfl⟩ : syracuseStep 1172047 = 1758071) B1758071
theorem B1172063 : Blo 1170402 1172063 := bstep (se 1 (by rfl) ⟨879047, by rfl⟩ : syracuseStep 1172063 = 1758095) B1758095
theorem B1172091 : Blo 1170402 1172091 := bstep (se 1 (by rfl) ⟨879068, by rfl⟩ : syracuseStep 1172091 = 1758137) B1758137
theorem B1876651 : Blo 1170402 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B9503405 : Blo 1170402 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B1172143 : Blo 1170402 1172143 := bstep (se 1 (by rfl) ⟨879107, by rfl⟩ : syracuseStep 1172143 = 1758215) B1758215
theorem B1172167 : Blo 1170402 1172167 := bstep (se 1 (by rfl) ⟨879125, by rfl⟩ : syracuseStep 1172167 = 1758251) B1758251
theorem B1172187 : Blo 1170402 1172187 := bstep (se 1 (by rfl) ⟨879140, by rfl⟩ : syracuseStep 1172187 = 1758281) B1758281
theorem B1172263 : Blo 1170402 1172263 := bstep (se 1 (by rfl) ⟨879197, by rfl⟩ : syracuseStep 1172263 = 1758395) B1758395
theorem B1172303 : Blo 1170402 1172303 := bstep (se 1 (by rfl) ⟨879227, by rfl⟩ : syracuseStep 1172303 = 1758455) B1758455
theorem B1172319 : Blo 1170402 1172319 := bstep (se 1 (by rfl) ⟨879239, by rfl⟩ : syracuseStep 1172319 = 1758479) B1758479
theorem B1172347 : Blo 1170402 1172347 := bstep (se 1 (by rfl) ⟨879260, by rfl⟩ : syracuseStep 1172347 = 1758521) B1758521
theorem B1172399 : Blo 1170402 1172399 := bstep (se 1 (by rfl) ⟨879299, by rfl⟩ : syracuseStep 1172399 = 1758599) B1758599
theorem B1975259 : Blo 1170402 1975259 := bstep (se 1 (by rfl) ⟨1481444, by rfl⟩ : syracuseStep 1975259 = 2962889) B2962889
theorem B4449437 : Blo 1170402 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B4449451 : Blo 1170402 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B1975495 : Blo 1170402 1975495 := bstep (se 1 (by rfl) ⟨1481621, by rfl⟩ : syracuseStep 1975495 = 2963243) B2963243
theorem B14451929 : Blo 1170402 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B15017309 : Blo 1170402 15017309 := bstep (se 3 (by rfl) ⟨2815745, by rfl⟩ : syracuseStep 15017309 = 5631491) B5631491
theorem B1975657 : Blo 1170402 1975657 := bstep (se 2 (by rfl) ⟨740871, by rfl⟩ : syracuseStep 1975657 = 1481743) B1481743
theorem B11265443 : Blo 1170402 11265443 := bstep (se 1 (by rfl) ⟨8449082, by rfl⟩ : syracuseStep 11265443 = 16898165) B16898165
theorem B4449755 : Blo 1170402 4449755 := bstep (se 1 (by rfl) ⟨3337316, by rfl⟩ : syracuseStep 4449755 = 6674633) B6674633
theorem B3565043 : Blo 1170402 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B3753611 : Blo 1170402 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B7710497 : Blo 1170402 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B2221985 : Blo 1170402 2221985 := bstep (se 2 (by rfl) ⟨833244, by rfl⟩ : syracuseStep 2221985 = 1666489) B1666489
theorem B12838817 : Blo 1170402 12838817 := bstep (se 2 (by rfl) ⟨4814556, by rfl⟩ : syracuseStep 12838817 = 9629113) B9629113
theorem B1976251 : Blo 1170402 1976251 := bstep (se 1 (by rfl) ⟨1482188, by rfl⟩ : syracuseStep 1976251 = 2964377) B2964377
theorem B8890397 : Blo 1170402 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B1976359 : Blo 1170402 1976359 := bstep (se 1 (by rfl) ⟨1482269, by rfl⟩ : syracuseStep 1976359 = 2964539) B2964539
theorem B3336349 : Blo 1170402 3336349 := bstep (se 3 (by rfl) ⟨625565, by rfl⟩ : syracuseStep 3336349 = 1251131) B1251131
theorem B3950909 : Blo 1170402 3950909 := bstep (se 3 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 3950909 = 1481591) B1481591
theorem B1976683 : Blo 1170402 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B1755611 : Blo 1170402 1755611 := bstep (se 1 (by rfl) ⟨1316708, by rfl⟩ : syracuseStep 1755611 = 2633417) B2633417
theorem B4631027 : Blo 1170402 4631027 := bstep (se 1 (by rfl) ⟨3473270, by rfl⟩ : syracuseStep 4631027 = 6946541) B6946541
theorem B4008473 : Blo 1170402 4008473 := bstep (se 2 (by rfl) ⟨1503177, by rfl⟩ : syracuseStep 4008473 = 3006355) B3006355
theorem B1780423 : Blo 1170402 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B85453541 : Blo 1170402 85453541 := bstep (se 4 (by rfl) ⟨8011269, by rfl⟩ : syracuseStep 85453541 = 16022539) B16022539
theorem B5925635 : Blo 1170402 5925635 := bstep (se 1 (by rfl) ⟨4444226, by rfl⟩ : syracuseStep 5925635 = 8888453) B8888453
theorem B5933897 : Blo 1170402 5933897 := bstep (se 2 (by rfl) ⟨2225211, by rfl⟩ : syracuseStep 5933897 = 4450423) B4450423
theorem B1756079 : Blo 1170402 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B7506863 : Blo 1170402 7506863 := bstep (se 1 (by rfl) ⟨5630147, by rfl⟩ : syracuseStep 7506863 = 11260295) B11260295
theorem B1756169 : Blo 1170402 1756169 := bstep (se 2 (by rfl) ⟨658563, by rfl⟩ : syracuseStep 1756169 = 1317127) B1317127
theorem B1756199 : Blo 1170402 1756199 := bstep (se 1 (by rfl) ⟨1317149, by rfl⟩ : syracuseStep 1756199 = 2634299) B2634299
theorem B1756283 : Blo 1170402 1756283 := bstep (se 1 (by rfl) ⟨1317212, by rfl⟩ : syracuseStep 1756283 = 2634425) B2634425
theorem B3951773 : Blo 1170402 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B6008003 : Blo 1170402 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B1756409 : Blo 1170402 1756409 := bstep (se 2 (by rfl) ⟨658653, by rfl⟩ : syracuseStep 1756409 = 1317307) B1317307
theorem B16026917 : Blo 1170402 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B13716773 : Blo 1170402 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B1756511 : Blo 1170402 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B1756523 : Blo 1170402 1756523 := bstep (se 1 (by rfl) ⟨1317392, by rfl⟩ : syracuseStep 1756523 = 2634785) B2634785
theorem B3378557 : Blo 1170402 3378557 := bstep (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) B1266959
theorem B2502031 : Blo 1170402 2502031 := bstep (se 1 (by rfl) ⟨1876523, by rfl⟩ : syracuseStep 2502031 = 3753047) B3753047
theorem B1977743 : Blo 1170402 1977743 := bstep (se 1 (by rfl) ⟨1483307, by rfl⟩ : syracuseStep 1977743 = 2966615) B2966615
theorem B2223625 : Blo 1170402 2223625 := bstep (se 2 (by rfl) ⟨833859, by rfl⟩ : syracuseStep 2223625 = 1667719) B1667719
theorem B2002489 : Blo 1170402 2002489 := bstep (se 2 (by rfl) ⟨750933, by rfl⟩ : syracuseStep 2002489 = 1501867) B1501867
theorem B1756751 : Blo 1170402 1756751 := bstep (se 1 (by rfl) ⟨1317563, by rfl⟩ : syracuseStep 1756751 = 2635127) B2635127
theorem B6671969 : Blo 1170402 6671969 := bstep (se 2 (by rfl) ⟨2501988, by rfl⟩ : syracuseStep 6671969 = 5003977) B5003977
theorem B1977979 : Blo 1170402 1977979 := bstep (se 1 (by rfl) ⟨1483484, by rfl⟩ : syracuseStep 1977979 = 2966969) B2966969
theorem B3952313 : Blo 1170402 3952313 := bstep (se 2 (by rfl) ⟨1482117, by rfl⟩ : syracuseStep 3952313 = 2964235) B2964235
theorem B5705405 : Blo 1170402 5705405 := bstep (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) B2139527
theorem B1756871 : Blo 1170402 1756871 := bstep (se 1 (by rfl) ⟨1317653, by rfl⟩ : syracuseStep 1756871 = 2635307) B2635307
theorem B32059097 : Blo 1170402 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B5345119 : Blo 1170402 5345119 := bstep (se 1 (by rfl) ⟨4008839, by rfl⟩ : syracuseStep 5345119 = 8017679) B8017679
theorem B1757033 : Blo 1170402 1757033 := bstep (se 2 (by rfl) ⟨658887, by rfl⟩ : syracuseStep 1757033 = 1317775) B1317775
theorem B2633579 : Blo 1170402 2633579 := bstep (se 1 (by rfl) ⟨1975184, by rfl⟩ : syracuseStep 2633579 = 3950369) B3950369
theorem B2633633 : Blo 1170402 2633633 := bstep (se 2 (by rfl) ⟨987612, by rfl⟩ : syracuseStep 2633633 = 1975225) B1975225
theorem B2109359 : Blo 1170402 2109359 := bstep (se 1 (by rfl) ⟨1582019, by rfl⟩ : syracuseStep 2109359 = 3164039) B3164039
theorem B1757111 : Blo 1170402 1757111 := bstep (se 1 (by rfl) ⟨1317833, by rfl⟩ : syracuseStep 1757111 = 2635667) B2635667
theorem B4444091 : Blo 1170402 4444091 := bstep (se 1 (by rfl) ⟨3333068, by rfl⟩ : syracuseStep 4444091 = 6666137) B6666137
theorem B1757147 : Blo 1170402 1757147 := bstep (se 1 (by rfl) ⟨1317860, by rfl⟩ : syracuseStep 1757147 = 2635721) B2635721
theorem B1667081 : Blo 1170402 1667081 := bstep (se 2 (by rfl) ⟨625155, by rfl⟩ : syracuseStep 1667081 = 1250311) B1250311
theorem B3338297 : Blo 1170402 3338297 := bstep (se 2 (by rfl) ⟨1251861, by rfl⟩ : syracuseStep 3338297 = 2503723) B2503723
theorem B5935193 : Blo 1170402 5935193 := bstep (se 2 (by rfl) ⟨2225697, by rfl⟩ : syracuseStep 5935193 = 4451395) B4451395
theorem B7499891 : Blo 1170402 7499891 := bstep (se 1 (by rfl) ⟨5624918, by rfl⟩ : syracuseStep 7499891 = 11249837) B11249837
theorem B2633975 : Blo 1170402 2633975 := bstep (se 1 (by rfl) ⟨1975481, by rfl⟩ : syracuseStep 2633975 = 3950963) B3950963
theorem B7500043 : Blo 1170402 7500043 := bstep (se 1 (by rfl) ⟨5625032, by rfl⟩ : syracuseStep 7500043 = 11250065) B11250065
theorem B3952907 : Blo 1170402 3952907 := bstep (se 1 (by rfl) ⟨2964680, by rfl⟩ : syracuseStep 3952907 = 5929361) B5929361
theorem B5001533 : Blo 1170402 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B5927255 : Blo 1170402 5927255 := bstep (se 1 (by rfl) ⟨4445441, by rfl⟩ : syracuseStep 5927255 = 8890883) B8890883
theorem B5001601 : Blo 1170402 5001601 := bstep (se 2 (by rfl) ⟨1875600, by rfl⟩ : syracuseStep 5001601 = 3751201) B3751201
theorem B1757615 : Blo 1170402 1757615 := bstep (se 1 (by rfl) ⟨1318211, by rfl⟩ : syracuseStep 1757615 = 2636423) B2636423
theorem B2224559 : Blo 1170402 2224559 := bstep (se 1 (by rfl) ⟨1668419, by rfl⟩ : syracuseStep 2224559 = 3336839) B3336839
theorem B1757705 : Blo 1170402 1757705 := bstep (se 2 (by rfl) ⟨659139, by rfl⟩ : syracuseStep 1757705 = 1318279) B1318279
theorem B3953177 : Blo 1170402 3953177 := bstep (se 2 (by rfl) ⟨1482441, by rfl⟩ : syracuseStep 3953177 = 2964883) B2964883
theorem B1757735 : Blo 1170402 1757735 := bstep (se 1 (by rfl) ⟨1318301, by rfl⟩ : syracuseStep 1757735 = 2636603) B2636603
theorem B1757819 : Blo 1170402 1757819 := bstep (se 1 (by rfl) ⟨1318364, by rfl⟩ : syracuseStep 1757819 = 2636729) B2636729
theorem B1757945 : Blo 1170402 1757945 := bstep (se 2 (by rfl) ⟨659229, by rfl⟩ : syracuseStep 1757945 = 1318459) B1318459
theorem B6329117 : Blo 1170402 6329117 := bstep (se 3 (by rfl) ⟨1186709, by rfl⟩ : syracuseStep 6329117 = 2373419) B2373419
theorem B2634569 : Blo 1170402 2634569 := bstep (se 2 (by rfl) ⟨987963, by rfl⟩ : syracuseStep 2634569 = 1975927) B1975927
theorem B1758047 : Blo 1170402 1758047 := bstep (se 1 (by rfl) ⟨1318535, by rfl⟩ : syracuseStep 1758047 = 2637071) B2637071
theorem B1667947 : Blo 1170402 1667947 := bstep (se 1 (by rfl) ⟨1250960, by rfl⟩ : syracuseStep 1667947 = 2501921) B2501921
theorem B1758059 : Blo 1170402 1758059 := bstep (se 1 (by rfl) ⟨1318544, by rfl⟩ : syracuseStep 1758059 = 2637089) B2637089
theorem B2225083 : Blo 1170402 2225083 := bstep (se 1 (by rfl) ⟨1668812, by rfl⟩ : syracuseStep 2225083 = 3337625) B3337625
theorem B6673427 : Blo 1170402 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B10679363 : Blo 1170402 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B1758287 : Blo 1170402 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B1758407 : Blo 1170402 1758407 := bstep (se 1 (by rfl) ⟨1318805, by rfl⟩ : syracuseStep 1758407 = 2637611) B2637611
theorem B14251211 : Blo 1170402 14251211 := bstep (se 1 (by rfl) ⟨10688408, by rfl⟩ : syracuseStep 14251211 = 21376817) B21376817
theorem B16897241 : Blo 1170402 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B4814167 : Blo 1170402 4814167 := bstep (se 1 (by rfl) ⟨3610625, by rfl⟩ : syracuseStep 4814167 = 7221251) B7221251
theorem B1758569 : Blo 1170402 1758569 := bstep (se 2 (by rfl) ⟨659463, by rfl⟩ : syracuseStep 1758569 = 1318927) B1318927
theorem B2225569 : Blo 1170402 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B8902061 : Blo 1170402 8902061 := bstep (se 3 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 8902061 = 3338273) B3338273
theorem B1668647 : Blo 1170402 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B2635361 : Blo 1170402 2635361 := bstep (se 2 (by rfl) ⟨988260, by rfl⟩ : syracuseStep 2635361 = 1976521) B1976521
theorem B3954311 : Blo 1170402 3954311 := bstep (se 1 (by rfl) ⟨2965733, by rfl⟩ : syracuseStep 3954311 = 5931467) B5931467
theorem B3749561 : Blo 1170402 3749561 := bstep (se 2 (by rfl) ⟨1406085, by rfl⟩ : syracuseStep 3749561 = 2812171) B2812171
theorem B3954365 : Blo 1170402 3954365 := bstep (se 3 (by rfl) ⟨741443, by rfl⟩ : syracuseStep 3954365 = 1482887) B1482887
theorem B2004679 : Blo 1170402 2004679 := bstep (se 1 (by rfl) ⟨1503509, by rfl⟩ : syracuseStep 2004679 = 3007019) B3007019
theorem B4224761 : Blo 1170402 4224761 := bstep (se 2 (by rfl) ⟨1584285, by rfl⟩ : syracuseStep 4224761 = 3168571) B3168571
theorem B3954527 : Blo 1170402 3954527 := bstep (se 1 (by rfl) ⟨2965895, by rfl⟩ : syracuseStep 3954527 = 5931791) B5931791
theorem B2963375 : Blo 1170402 2963375 := bstep (se 1 (by rfl) ⟨2222531, by rfl⟩ : syracuseStep 2963375 = 4445063) B4445063
theorem B2635703 : Blo 1170402 2635703 := bstep (se 1 (by rfl) ⟨1976777, by rfl⟩ : syracuseStep 2635703 = 3953555) B3953555
theorem B3954689 : Blo 1170402 3954689 := bstep (se 2 (by rfl) ⟨1483008, by rfl⟩ : syracuseStep 3954689 = 2966017) B2966017
theorem B570095633 : Blo 1170402 570095633 := bstep (se 2 (by rfl) ⟨213785862, by rfl⟩ : syracuseStep 570095633 = 427571725) B427571725
theorem B4446323 : Blo 1170402 4446323 := bstep (se 1 (by rfl) ⟨3334742, by rfl⟩ : syracuseStep 4446323 = 6669485) B6669485
theorem B4511915 : Blo 1170402 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B8894771 : Blo 1170402 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B2636297 : Blo 1170402 2636297 := bstep (se 2 (by rfl) ⟨988611, by rfl⟩ : syracuseStep 2636297 = 1977223) B1977223
theorem B7510553 : Blo 1170402 7510553 := bstep (se 2 (by rfl) ⟨2816457, by rfl⟩ : syracuseStep 7510553 = 5632915) B5632915
theorem B1317415 : Blo 1170402 1317415 := bstep (se 1 (by rfl) ⟨988061, by rfl⟩ : syracuseStep 1317415 = 1976123) B1976123
theorem B6666887 : Blo 1170402 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B15014645 : Blo 1170402 15014645 := bstep (se 5 (by rfl) ⟨703811, by rfl⟩ : syracuseStep 15014645 = 1407623) B1407623
theorem B8444675 : Blo 1170402 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B3955499 : Blo 1170402 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B2636639 : Blo 1170402 2636639 := bstep (se 1 (by rfl) ⟨1977479, by rfl⟩ : syracuseStep 2636639 = 3954959) B3954959
theorem B1481647 : Blo 1170402 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B15006647 : Blo 1170402 15006647 := bstep (se 1 (by rfl) ⟨11254985, by rfl⟩ : syracuseStep 15006647 = 22509971) B22509971
theorem B7502813 : Blo 1170402 7502813 := bstep (se 3 (by rfl) ⟨1406777, by rfl⟩ : syracuseStep 7502813 = 2813555) B2813555
theorem B2636819 : Blo 1170402 2636819 := bstep (se 1 (by rfl) ⟨1977614, by rfl⟩ : syracuseStep 2636819 = 3955229) B3955229
theorem B1170471 : Blo 1170402 1170471 := bstep (se 1 (by rfl) ⟨877853, by rfl⟩ : syracuseStep 1170471 = 1755707) B1755707
theorem B3955769 : Blo 1170402 3955769 := bstep (se 2 (by rfl) ⟨1483413, by rfl⟩ : syracuseStep 3955769 = 2966827) B2966827
theorem B1170511 : Blo 1170402 1170511 := bstep (se 1 (by rfl) ⟨877883, by rfl⟩ : syracuseStep 1170511 = 1755767) B1755767
theorem B6667343 : Blo 1170402 6667343 := bstep (se 1 (by rfl) ⟨5000507, by rfl⟩ : syracuseStep 6667343 = 10001015) B10001015
theorem B2964559 : Blo 1170402 2964559 := bstep (se 1 (by rfl) ⟨2223419, by rfl⟩ : syracuseStep 2964559 = 4446839) B4446839
theorem B1170527 : Blo 1170402 1170527 := bstep (se 1 (by rfl) ⟨877895, by rfl⟩ : syracuseStep 1170527 = 1755791) B1755791
theorem B1170555 : Blo 1170402 1170555 := bstep (se 1 (by rfl) ⟨877916, by rfl⟩ : syracuseStep 1170555 = 1755833) B1755833
theorem B5627033 : Blo 1170402 5627033 := bstep (se 2 (by rfl) ⟨2110137, by rfl⟩ : syracuseStep 5627033 = 4220275) B4220275
theorem B1170607 : Blo 1170402 1170607 := bstep (se 1 (by rfl) ⟨877955, by rfl⟩ : syracuseStep 1170607 = 1755911) B1755911
theorem B1170631 : Blo 1170402 1170631 := bstep (se 1 (by rfl) ⟨877973, by rfl⟩ : syracuseStep 1170631 = 1755947) B1755947
theorem B1170651 : Blo 1170402 1170651 := bstep (se 1 (by rfl) ⟨877988, by rfl⟩ : syracuseStep 1170651 = 1755977) B1755977
theorem B1170727 : Blo 1170402 1170727 := bstep (se 1 (by rfl) ⟨878045, by rfl⟩ : syracuseStep 1170727 = 1756091) B1756091
theorem B1170767 : Blo 1170402 1170767 := bstep (se 1 (by rfl) ⟨878075, by rfl⟩ : syracuseStep 1170767 = 1756151) B1756151
theorem B1170783 : Blo 1170402 1170783 := bstep (se 1 (by rfl) ⟨878087, by rfl⟩ : syracuseStep 1170783 = 1756175) B1756175
theorem B2637161 : Blo 1170402 2637161 := bstep (se 2 (by rfl) ⟨988935, by rfl⟩ : syracuseStep 2637161 = 1977871) B1977871
theorem B1170811 : Blo 1170402 1170811 := bstep (se 1 (by rfl) ⟨878108, by rfl⟩ : syracuseStep 1170811 = 1756217) B1756217
theorem B3956093 : Blo 1170402 3956093 := bstep (se 3 (by rfl) ⟨741767, by rfl⟩ : syracuseStep 3956093 = 1483535) B1483535
theorem B1170863 : Blo 1170402 1170863 := bstep (se 1 (by rfl) ⟨878147, by rfl⟩ : syracuseStep 1170863 = 1756295) B1756295
theorem B1170887 : Blo 1170402 1170887 := bstep (se 1 (by rfl) ⟨878165, by rfl⟩ : syracuseStep 1170887 = 1756331) B1756331
theorem B1170907 : Blo 1170402 1170907 := bstep (se 1 (by rfl) ⟨878180, by rfl⟩ : syracuseStep 1170907 = 1756361) B1756361
theorem B3055091 : Blo 1170402 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B1170983 : Blo 1170402 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B1171023 : Blo 1170402 1171023 := bstep (se 1 (by rfl) ⟨878267, by rfl⟩ : syracuseStep 1171023 = 1756535) B1756535
theorem B1171039 : Blo 1170402 1171039 := bstep (se 1 (by rfl) ⟨878279, by rfl⟩ : syracuseStep 1171039 = 1756559) B1756559
theorem B1171067 : Blo 1170402 1171067 := bstep (se 1 (by rfl) ⟨878300, by rfl⟩ : syracuseStep 1171067 = 1756601) B1756601
theorem B6676091 : Blo 1170402 6676091 := bstep (se 1 (by rfl) ⟨5007068, by rfl⟩ : syracuseStep 6676091 = 10014137) B10014137
theorem B3956363 : Blo 1170402 3956363 := bstep (se 1 (by rfl) ⟨2967272, by rfl⟩ : syracuseStep 3956363 = 5934545) B5934545
theorem B1171119 : Blo 1170402 1171119 := bstep (se 1 (by rfl) ⟨878339, by rfl⟩ : syracuseStep 1171119 = 1756679) B1756679
theorem B1171143 : Blo 1170402 1171143 := bstep (se 1 (by rfl) ⟨878357, by rfl⟩ : syracuseStep 1171143 = 1756715) B1756715
theorem B2285255 : Blo 1170402 2285255 := bstep (se 1 (by rfl) ⟨1713941, by rfl⟩ : syracuseStep 2285255 = 3427883) B3427883
theorem B2965207 : Blo 1170402 2965207 := bstep (se 1 (by rfl) ⟨2223905, by rfl⟩ : syracuseStep 2965207 = 4447811) B4447811
theorem B1171163 : Blo 1170402 1171163 := bstep (se 1 (by rfl) ⟨878372, by rfl⟩ : syracuseStep 1171163 = 1756745) B1756745
theorem B4447993 : Blo 1170402 4447993 := bstep (se 2 (by rfl) ⟨1667997, by rfl⟩ : syracuseStep 4447993 = 3335995) B3335995
theorem B1171239 : Blo 1170402 1171239 := bstep (se 1 (by rfl) ⟨878429, by rfl⟩ : syracuseStep 1171239 = 1756859) B1756859
theorem B5930819 : Blo 1170402 5930819 := bstep (se 1 (by rfl) ⟨4448114, by rfl⟩ : syracuseStep 5930819 = 8896229) B8896229
theorem B3751753 : Blo 1170402 3751753 := bstep (se 2 (by rfl) ⟨1406907, by rfl⟩ : syracuseStep 3751753 = 2813815) B2813815
theorem B1171279 : Blo 1170402 1171279 := bstep (se 1 (by rfl) ⟨878459, by rfl⟩ : syracuseStep 1171279 = 1756919) B1756919
theorem B1171295 : Blo 1170402 1171295 := bstep (se 1 (by rfl) ⟨878471, by rfl⟩ : syracuseStep 1171295 = 1756943) B1756943
theorem B16023415 : Blo 1170402 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B6676343 : Blo 1170402 6676343 := bstep (se 1 (by rfl) ⟨5007257, by rfl⟩ : syracuseStep 6676343 = 10014515) B10014515
theorem B1171323 : Blo 1170402 1171323 := bstep (se 1 (by rfl) ⟨878492, by rfl⟩ : syracuseStep 1171323 = 1756985) B1756985
theorem B7610273 : Blo 1170402 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B1171375 : Blo 1170402 1171375 := bstep (se 1 (by rfl) ⟨878531, by rfl⟩ : syracuseStep 1171375 = 1757063) B1757063
theorem B10141625 : Blo 1170402 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B3751867 : Blo 1170402 3751867 := bstep (se 1 (by rfl) ⟨2813900, by rfl⟩ : syracuseStep 3751867 = 5627801) B5627801
theorem B2637755 : Blo 1170402 2637755 := bstep (se 1 (by rfl) ⟨1978316, by rfl⟩ : syracuseStep 2637755 = 3956633) B3956633
theorem B1171399 : Blo 1170402 1171399 := bstep (se 1 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 1171399 = 1757099) B1757099
theorem B1171419 : Blo 1170402 1171419 := bstep (se 1 (by rfl) ⟨878564, by rfl⟩ : syracuseStep 1171419 = 1757129) B1757129
theorem B1482715 : Blo 1170402 1482715 := bstep (se 1 (by rfl) ⟨1112036, by rfl⟩ : syracuseStep 1482715 = 2224073) B2224073
theorem B3956795 : Blo 1170402 3956795 := bstep (se 1 (by rfl) ⟨2967596, by rfl⟩ : syracuseStep 3956795 = 5935193) B5935193
theorem B4448465 : Blo 1170402 4448465 := bstep (se 2 (by rfl) ⟨1668174, by rfl⟩ : syracuseStep 4448465 = 3336349) B3336349
theorem B3334355 : Blo 1170402 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B1171743 : Blo 1170402 1171743 := bstep (se 1 (by rfl) ⟨878807, by rfl⟩ : syracuseStep 1171743 = 1757615) B1757615
theorem B1483039 : Blo 1170402 1483039 := bstep (se 1 (by rfl) ⟨1112279, by rfl⟩ : syracuseStep 1483039 = 2224559) B2224559
theorem B1171803 : Blo 1170402 1171803 := bstep (se 1 (by rfl) ⟨878852, by rfl⟩ : syracuseStep 1171803 = 1757705) B1757705
theorem B1171823 : Blo 1170402 1171823 := bstep (se 1 (by rfl) ⟨878867, by rfl⟩ : syracuseStep 1171823 = 1757735) B1757735
theorem B1171879 : Blo 1170402 1171879 := bstep (se 1 (by rfl) ⟨878909, by rfl⟩ : syracuseStep 1171879 = 1757819) B1757819
theorem B1171963 : Blo 1170402 1171963 := bstep (se 1 (by rfl) ⟨878972, by rfl⟩ : syracuseStep 1171963 = 1757945) B1757945
theorem B6668801 : Blo 1170402 6668801 := bstep (se 2 (by rfl) ⟨2500800, by rfl⟩ : syracuseStep 6668801 = 5001601) B5001601
theorem B4219411 : Blo 1170402 4219411 := bstep (se 1 (by rfl) ⟨3164558, by rfl⟩ : syracuseStep 4219411 = 6329117) B6329117
theorem B1172031 : Blo 1170402 1172031 := bstep (se 1 (by rfl) ⟨879023, by rfl⟩ : syracuseStep 1172031 = 1758047) B1758047
theorem B1172039 : Blo 1170402 1172039 := bstep (se 1 (by rfl) ⟨879029, by rfl⟩ : syracuseStep 1172039 = 1758059) B1758059
theorem B4448951 : Blo 1170402 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B7119575 : Blo 1170402 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B1172191 : Blo 1170402 1172191 := bstep (se 1 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 1172191 = 1758287) B1758287
theorem B42738445 : Blo 1170402 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B2966291 : Blo 1170402 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1172271 : Blo 1170402 1172271 := bstep (se 1 (by rfl) ⟨879203, by rfl⟩ : syracuseStep 1172271 = 1758407) B1758407
theorem B11264827 : Blo 1170402 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B9634619 : Blo 1170402 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B10011539 : Blo 1170402 10011539 := bstep (se 1 (by rfl) ⟨7508654, by rfl⟩ : syracuseStep 10011539 = 15017309) B15017309
theorem B1172379 : Blo 1170402 1172379 := bstep (se 1 (by rfl) ⟨879284, by rfl⟩ : syracuseStep 1172379 = 1758569) B1758569
theorem B2966503 : Blo 1170402 2966503 := bstep (se 1 (by rfl) ⟨2224877, by rfl⟩ : syracuseStep 2966503 = 4449755) B4449755
theorem B2376695 : Blo 1170402 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B9495589 : Blo 1170402 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B2499707 : Blo 1170402 2499707 := bstep (se 1 (by rfl) ⟨1874780, by rfl⟩ : syracuseStep 2499707 = 3749561) B3749561
theorem B1975529 : Blo 1170402 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B2966777 : Blo 1170402 2966777 := bstep (se 2 (by rfl) ⟨1112541, by rfl⟩ : syracuseStep 2966777 = 2225083) B2225083
theorem B1975583 : Blo 1170402 1975583 := bstep (se 1 (by rfl) ⟨1481687, by rfl⟩ : syracuseStep 1975583 = 2963375) B2963375
theorem B4449725 : Blo 1170402 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B3007943 : Blo 1170402 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B5932601 : Blo 1170402 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B2672315 : Blo 1170402 2672315 := bstep (se 1 (by rfl) ⟨2004236, by rfl⟩ : syracuseStep 2672315 = 4008473) B4008473
theorem B5007035 : Blo 1170402 5007035 := bstep (se 1 (by rfl) ⟨3755276, by rfl⟩ : syracuseStep 5007035 = 7510553) B7510553
theorem B56969027 : Blo 1170402 56969027 := bstep (se 1 (by rfl) ⟨42726770, by rfl⟩ : syracuseStep 56969027 = 85453541) B85453541
theorem B3950423 : Blo 1170402 3950423 := bstep (se 1 (by rfl) ⟨2962817, by rfl⟩ : syracuseStep 3950423 = 5925635) B5925635
theorem B5629783 : Blo 1170402 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B3336041 : Blo 1170402 3336041 := bstep (se 2 (by rfl) ⟨1251015, by rfl⟩ : syracuseStep 3336041 = 2502031) B2502031
theorem B2967425 : Blo 1170402 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B10004431 : Blo 1170402 10004431 := bstep (se 1 (by rfl) ⟨7503323, by rfl⟩ : syracuseStep 10004431 = 15006647) B15006647
theorem B9144515 : Blo 1170402 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B2672905 : Blo 1170402 2672905 := bstep (se 2 (by rfl) ⟨1002339, by rfl⟩ : syracuseStep 2672905 = 2004679) B2004679
theorem B4450727 : Blo 1170402 4450727 := bstep (se 1 (by rfl) ⟨3338045, by rfl⟩ : syracuseStep 4450727 = 6676091) B6676091
theorem B34236845 : Blo 1170402 34236845 := bstep (se 3 (by rfl) ⟨6419408, by rfl⟩ : syracuseStep 34236845 = 12838817) B12838817
theorem B3803603 : Blo 1170402 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B1755719 : Blo 1170402 1755719 := bstep (se 1 (by rfl) ⟨1316789, by rfl⟩ : syracuseStep 1755719 = 2633579) B2633579
theorem B4450895 : Blo 1170402 4450895 := bstep (se 1 (by rfl) ⟨3338171, by rfl⟩ : syracuseStep 4450895 = 6676343) B6676343
theorem B1755755 : Blo 1170402 1755755 := bstep (se 1 (by rfl) ⟨1316816, by rfl⟩ : syracuseStep 1755755 = 2633633) B2633633
theorem B5073515 : Blo 1170402 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B1976953 : Blo 1170402 1976953 := bstep (se 2 (by rfl) ⟨741357, by rfl⟩ : syracuseStep 1976953 = 1482715) B1482715
theorem B6761083 : Blo 1170402 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B1977007 : Blo 1170402 1977007 := bstep (se 1 (by rfl) ⟨1482755, by rfl⟩ : syracuseStep 1977007 = 2965511) B2965511
theorem B4999927 : Blo 1170402 4999927 := bstep (se 1 (by rfl) ⟨3749945, by rfl⟩ : syracuseStep 4999927 = 7499891) B7499891
theorem B9497411 : Blo 1170402 9497411 := bstep (se 1 (by rfl) ⟨7123058, by rfl⟩ : syracuseStep 9497411 = 14246117) B14246117
theorem B1755983 : Blo 1170402 1755983 := bstep (se 1 (by rfl) ⟨1316987, by rfl⟩ : syracuseStep 1755983 = 2633975) B2633975
theorem B3951503 : Blo 1170402 3951503 := bstep (se 1 (by rfl) ⟨2963627, by rfl⟩ : syracuseStep 3951503 = 5927255) B5927255
theorem B6335603 : Blo 1170402 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B1756379 : Blo 1170402 1756379 := bstep (se 1 (by rfl) ⟨1317284, by rfl⟩ : syracuseStep 1756379 = 2634569) B2634569
theorem B1756553 : Blo 1170402 1756553 := bstep (se 2 (by rfl) ⟨658707, by rfl⟩ : syracuseStep 1756553 = 1317415) B1317415
theorem B5934707 : Blo 1170402 5934707 := bstep (se 1 (by rfl) ⟨4451030, by rfl⟩ : syracuseStep 5934707 = 8902061) B8902061
theorem B1756907 : Blo 1170402 1756907 := bstep (se 1 (by rfl) ⟨1317680, by rfl⟩ : syracuseStep 1756907 = 2635361) B2635361
theorem B2502407 : Blo 1170402 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B2223929 : Blo 1170402 2223929 := bstep (se 2 (by rfl) ⟨833973, by rfl⟩ : syracuseStep 2223929 = 1667947) B1667947
theorem B5140331 : Blo 1170402 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B1757135 : Blo 1170402 1757135 := bstep (se 1 (by rfl) ⟨1317851, by rfl⟩ : syracuseStep 1757135 = 2635703) B2635703
theorem B8146909 : Blo 1170402 8146909 := bstep (se 3 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 8146909 = 3055091) B3055091
theorem B380063755 : Blo 1170402 380063755 := bstep (se 1 (by rfl) ⟨285047816, by rfl⟩ : syracuseStep 380063755 = 570095633) B570095633
theorem B5926931 : Blo 1170402 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B3952745 : Blo 1170402 3952745 := bstep (se 2 (by rfl) ⟨1482279, by rfl⟩ : syracuseStep 3952745 = 2964559) B2964559
theorem B2633939 : Blo 1170402 2633939 := bstep (se 1 (by rfl) ⟨1975454, by rfl⟩ : syracuseStep 2633939 = 3950909) B3950909
theorem B2633993 : Blo 1170402 2633993 := bstep (se 2 (by rfl) ⟨987747, by rfl⟩ : syracuseStep 2633993 = 1975495) B1975495
theorem B1757531 : Blo 1170402 1757531 := bstep (se 1 (by rfl) ⟨1318148, by rfl⟩ : syracuseStep 1757531 = 2636297) B2636297
theorem B4444591 : Blo 1170402 4444591 := bstep (se 1 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 4444591 = 6666887) B6666887
theorem B6418889 : Blo 1170402 6418889 := bstep (se 2 (by rfl) ⟨2407083, by rfl⟩ : syracuseStep 6418889 = 4814167) B4814167
theorem B2634209 : Blo 1170402 2634209 := bstep (se 2 (by rfl) ⟨987828, by rfl⟩ : syracuseStep 2634209 = 1975657) B1975657
theorem B1757759 : Blo 1170402 1757759 := bstep (se 1 (by rfl) ⟨1318319, by rfl⟩ : syracuseStep 1757759 = 2636639) B2636639
theorem B5001875 : Blo 1170402 5001875 := bstep (se 1 (by rfl) ⟨3751406, by rfl⟩ : syracuseStep 5001875 = 7502813) B7502813
theorem B1757879 : Blo 1170402 1757879 := bstep (se 1 (by rfl) ⟨1318409, by rfl⟩ : syracuseStep 1757879 = 2636819) B2636819
theorem B4444895 : Blo 1170402 4444895 := bstep (se 1 (by rfl) ⟨3333671, by rfl⟩ : syracuseStep 4444895 = 6667343) B6667343
theorem B2634515 : Blo 1170402 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B1758107 : Blo 1170402 1758107 := bstep (se 1 (by rfl) ⟨1318580, by rfl⟩ : syracuseStep 1758107 = 2637161) B2637161
theorem B3953609 : Blo 1170402 3953609 := bstep (se 2 (by rfl) ⟨1482603, by rfl⟩ : syracuseStep 3953609 = 2965207) B2965207
theorem B5002337 : Blo 1170402 5002337 := bstep (se 2 (by rfl) ⟨1875876, by rfl⟩ : syracuseStep 5002337 = 3751753) B3751753
theorem B2634875 : Blo 1170402 2634875 := bstep (se 1 (by rfl) ⟨1976156, by rfl⟩ : syracuseStep 2634875 = 3952313) B3952313
theorem B5624957 : Blo 1170402 5624957 := bstep (se 3 (by rfl) ⟨1054679, by rfl⟩ : syracuseStep 5624957 = 2109359) B2109359
theorem B3953879 : Blo 1170402 3953879 := bstep (se 1 (by rfl) ⟨2965409, by rfl⟩ : syracuseStep 3953879 = 5930819) B5930819
theorem B2635001 : Blo 1170402 2635001 := bstep (se 2 (by rfl) ⟨988125, by rfl⟩ : syracuseStep 2635001 = 1976251) B1976251
theorem B5002489 : Blo 1170402 5002489 := bstep (se 2 (by rfl) ⟨1875933, by rfl⟩ : syracuseStep 5002489 = 3751867) B3751867
theorem B2962727 : Blo 1170402 2962727 := bstep (se 1 (by rfl) ⟨2222045, by rfl⟩ : syracuseStep 2962727 = 4444091) B4444091
theorem B1758503 : Blo 1170402 1758503 := bstep (se 1 (by rfl) ⟨1318877, by rfl⟩ : syracuseStep 1758503 = 2637755) B2637755
theorem B4445549 : Blo 1170402 4445549 := bstep (se 3 (by rfl) ⟨833540, by rfl⟩ : syracuseStep 4445549 = 1667081) B1667081
theorem B4445563 : Blo 1170402 4445563 := bstep (se 1 (by rfl) ⟨3334172, by rfl⟩ : syracuseStep 4445563 = 6668345) B6668345
theorem B2225531 : Blo 1170402 2225531 := bstep (se 1 (by rfl) ⟨1669148, by rfl⟩ : syracuseStep 2225531 = 3338297) B3338297
theorem B1758587 : Blo 1170402 1758587 := bstep (se 1 (by rfl) ⟨1318940, by rfl⟩ : syracuseStep 1758587 = 2637881) B2637881
theorem B2635145 : Blo 1170402 2635145 := bstep (se 2 (by rfl) ⟨988179, by rfl⟩ : syracuseStep 2635145 = 1976359) B1976359
theorem B5625227 : Blo 1170402 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B1250759 : Blo 1170402 1250759 := bstep (se 1 (by rfl) ⟨938069, by rfl⟩ : syracuseStep 1250759 = 1876139) B1876139
theorem B2635271 : Blo 1170402 2635271 := bstep (se 1 (by rfl) ⟨1976453, by rfl⟩ : syracuseStep 2635271 = 3952907) B3952907
theorem B24024611 : Blo 1170402 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B10679941 : Blo 1170402 10679941 := bstep (se 4 (by rfl) ⟨1001244, by rfl⟩ : syracuseStep 10679941 = 2002489) B2002489
theorem B10000057 : Blo 1170402 10000057 := bstep (se 2 (by rfl) ⟨3750021, by rfl⟩ : syracuseStep 10000057 = 7500043) B7500043
theorem B2635451 : Blo 1170402 2635451 := bstep (se 1 (by rfl) ⟨1976588, by rfl⟩ : syracuseStep 2635451 = 3953177) B3953177
theorem B2635577 : Blo 1170402 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B1316839 : Blo 1170402 1316839 := bstep (se 1 (by rfl) ⟨987629, by rfl⟩ : syracuseStep 1316839 = 1975259) B1975259
theorem B9500807 : Blo 1170402 9500807 := bstep (se 1 (by rfl) ⟨7125605, by rfl⟩ : syracuseStep 9500807 = 14251211) B14251211
theorem B10008805 : Blo 1170402 10008805 := bstep (se 4 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 10008805 = 1876651) B1876651
theorem B7510295 : Blo 1170402 7510295 := bstep (se 1 (by rfl) ⟨5632721, by rfl⟩ : syracuseStep 7510295 = 11265443) B11265443
theorem B2636207 : Blo 1170402 2636207 := bstep (se 1 (by rfl) ⟨1977155, by rfl⟩ : syracuseStep 2636207 = 3954311) B3954311
theorem B2636243 : Blo 1170402 2636243 := bstep (se 1 (by rfl) ⟨1977182, by rfl⟩ : syracuseStep 2636243 = 3954365) B3954365
theorem B2816507 : Blo 1170402 2816507 := bstep (se 1 (by rfl) ⟨2112380, by rfl⟩ : syracuseStep 2816507 = 4224761) B4224761
theorem B2636351 : Blo 1170402 2636351 := bstep (se 1 (by rfl) ⟨1977263, by rfl⟩ : syracuseStep 2636351 = 3954527) B3954527
theorem B1481323 : Blo 1170402 1481323 := bstep (se 1 (by rfl) ⟨1110992, by rfl⟩ : syracuseStep 1481323 = 2221985) B2221985
theorem B2636459 : Blo 1170402 2636459 := bstep (se 1 (by rfl) ⟨1977344, by rfl⟩ : syracuseStep 2636459 = 3954689) B3954689
theorem B2964215 : Blo 1170402 2964215 := bstep (se 1 (by rfl) ⟨2223161, by rfl⟩ : syracuseStep 2964215 = 4446323) B4446323
theorem B5929847 : Blo 1170402 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B1170407 : Blo 1170402 1170407 := bstep (se 1 (by rfl) ⟨877805, by rfl⟩ : syracuseStep 1170407 = 1755611) B1755611
theorem B10009763 : Blo 1170402 10009763 := bstep (se 1 (by rfl) ⟨7507322, by rfl⟩ : syracuseStep 10009763 = 15014645) B15014645
theorem B6094013 : Blo 1170402 6094013 := bstep (se 3 (by rfl) ⟨1142627, by rfl⟩ : syracuseStep 6094013 = 2285255) B2285255
theorem B2636999 : Blo 1170402 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B3955931 : Blo 1170402 3955931 := bstep (se 1 (by rfl) ⟨2966948, by rfl⟩ : syracuseStep 3955931 = 5933897) B5933897
theorem B1170719 : Blo 1170402 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B5004575 : Blo 1170402 5004575 := bstep (se 1 (by rfl) ⟨3753431, by rfl⟩ : syracuseStep 5004575 = 7506863) B7506863
theorem B1170779 : Blo 1170402 1170779 := bstep (se 1 (by rfl) ⟨878084, by rfl⟩ : syracuseStep 1170779 = 1756169) B1756169
theorem B2964833 : Blo 1170402 2964833 := bstep (se 2 (by rfl) ⟨1111812, by rfl⟩ : syracuseStep 2964833 = 2223625) B2223625
theorem B1170799 : Blo 1170402 1170799 := bstep (se 1 (by rfl) ⟨878099, by rfl⟩ : syracuseStep 1170799 = 1756199) B1756199
theorem B2637179 : Blo 1170402 2637179 := bstep (se 1 (by rfl) ⟨1977884, by rfl⟩ : syracuseStep 2637179 = 3955769) B3955769
theorem B1170855 : Blo 1170402 1170855 := bstep (se 1 (by rfl) ⟨878141, by rfl⟩ : syracuseStep 1170855 = 1756283) B1756283
theorem B3751355 : Blo 1170402 3751355 := bstep (se 1 (by rfl) ⟨2813516, by rfl⟩ : syracuseStep 3751355 = 5627033) B5627033
theorem B4005335 : Blo 1170402 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B2637305 : Blo 1170402 2637305 := bstep (se 2 (by rfl) ⟨988989, by rfl⟩ : syracuseStep 2637305 = 1977979) B1977979
theorem B1170939 : Blo 1170402 1170939 := bstep (se 1 (by rfl) ⟨878204, by rfl⟩ : syracuseStep 1170939 = 1756409) B1756409
theorem B1171007 : Blo 1170402 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B1171015 : Blo 1170402 1171015 := bstep (se 1 (by rfl) ⟨878261, by rfl⟩ : syracuseStep 1171015 = 1756523) B1756523
theorem B2252371 : Blo 1170402 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B2637395 : Blo 1170402 2637395 := bstep (se 1 (by rfl) ⟨1978046, by rfl⟩ : syracuseStep 2637395 = 3956093) B3956093
theorem B1318495 : Blo 1170402 1318495 := bstep (se 1 (by rfl) ⟨988871, by rfl⟩ : syracuseStep 1318495 = 1977743) B1977743
theorem B5930657 : Blo 1170402 5930657 := bstep (se 2 (by rfl) ⟨2223996, by rfl⟩ : syracuseStep 5930657 = 4447993) B4447993
theorem B1171167 : Blo 1170402 1171167 := bstep (se 1 (by rfl) ⟨878375, by rfl⟩ : syracuseStep 1171167 = 1756751) B1756751
theorem B4447979 : Blo 1170402 4447979 := bstep (se 1 (by rfl) ⟨3335984, by rfl⟩ : syracuseStep 4447979 = 6671969) B6671969
theorem B2637575 : Blo 1170402 2637575 := bstep (se 1 (by rfl) ⟨1978181, by rfl⟩ : syracuseStep 2637575 = 3956363) B3956363
theorem B7126825 : Blo 1170402 7126825 := bstep (se 2 (by rfl) ⟨2672559, by rfl⟩ : syracuseStep 7126825 = 5345119) B5345119
theorem B1171247 : Blo 1170402 1171247 := bstep (se 1 (by rfl) ⟨878435, by rfl⟩ : syracuseStep 1171247 = 1756871) B1756871
theorem B21372731 : Blo 1170402 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B21364553 : Blo 1170402 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B49397621 : Blo 1170402 49397621 := bstep (se 5 (by rfl) ⟨2315513, by rfl⟩ : syracuseStep 49397621 = 4631027) B4631027
theorem B1171355 : Blo 1170402 1171355 := bstep (se 1 (by rfl) ⟨878516, by rfl⟩ : syracuseStep 1171355 = 1757033) B1757033
theorem B1171407 : Blo 1170402 1171407 := bstep (se 1 (by rfl) ⟨878555, by rfl⟩ : syracuseStep 1171407 = 1757111) B1757111
theorem B1171431 : Blo 1170402 1171431 := bstep (se 1 (by rfl) ⟨878573, by rfl⟩ : syracuseStep 1171431 = 1757147) B1757147
theorem B2637863 : Blo 1170402 2637863 := bstep (se 1 (by rfl) ⟨1978397, by rfl⟩ : syracuseStep 2637863 = 3956795) B3956795
theorem B2965643 : Blo 1170402 2965643 := bstep (se 1 (by rfl) ⟨2224232, by rfl⟩ : syracuseStep 2965643 = 4448465) B4448465
theorem B1171687 : Blo 1170402 1171687 := bstep (se 1 (by rfl) ⟨878765, by rfl⟩ : syracuseStep 1171687 = 1757531) B1757531
theorem B13345073 : Blo 1170402 13345073 := bstep (se 2 (by rfl) ⟨5004402, by rfl⟩ : syracuseStep 13345073 = 10008805) B10008805
theorem B3563873 : Blo 1170402 3563873 := bstep (se 2 (by rfl) ⟨1336452, by rfl⟩ : syracuseStep 3563873 = 2672905) B2672905
theorem B1171839 : Blo 1170402 1171839 := bstep (se 1 (by rfl) ⟨878879, by rfl⟩ : syracuseStep 1171839 = 1757759) B1757759
theorem B3334583 : Blo 1170402 3334583 := bstep (se 1 (by rfl) ⟨2500937, by rfl⟩ : syracuseStep 3334583 = 5001875) B5001875
theorem B2965967 : Blo 1170402 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B1171919 : Blo 1170402 1171919 := bstep (se 1 (by rfl) ⟨878939, by rfl⟩ : syracuseStep 1171919 = 1757879) B1757879
theorem B6423079 : Blo 1170402 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B1172071 : Blo 1170402 1172071 := bstep (se 1 (by rfl) ⟨879053, by rfl⟩ : syracuseStep 1172071 = 1758107) B1758107
theorem B56959685 : Blo 1170402 56959685 := bstep (se 4 (by rfl) ⟨5339970, by rfl⟩ : syracuseStep 56959685 = 10679941) B10679941
theorem B3334891 : Blo 1170402 3334891 := bstep (se 1 (by rfl) ⟨2501168, by rfl⟩ : syracuseStep 3334891 = 5002337) B5002337
theorem B1975097 : Blo 1170402 1975097 := bstep (se 2 (by rfl) ⟨740661, by rfl⟩ : syracuseStep 1975097 = 1481323) B1481323
theorem B1975151 : Blo 1170402 1975151 := bstep (se 1 (by rfl) ⟨1481363, by rfl⟩ : syracuseStep 1975151 = 2962727) B2962727
theorem B1172335 : Blo 1170402 1172335 := bstep (se 1 (by rfl) ⟨879251, by rfl⟩ : syracuseStep 1172335 = 1758503) B1758503
theorem B1483687 : Blo 1170402 1483687 := bstep (se 1 (by rfl) ⟨1112765, by rfl⟩ : syracuseStep 1483687 = 2225531) B2225531
theorem B1172391 : Blo 1170402 1172391 := bstep (se 1 (by rfl) ⟨879293, by rfl⟩ : syracuseStep 1172391 = 1758587) B1758587
theorem B2966483 : Blo 1170402 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B56984593 : Blo 1170402 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B3335357 : Blo 1170402 3335357 := bstep (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) B1250759
theorem B37979351 : Blo 1170402 37979351 := bstep (se 1 (by rfl) ⟨28484513, by rfl⟩ : syracuseStep 37979351 = 56969027) B56969027
theorem B10142941 : Blo 1170402 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B6333871 : Blo 1170402 6333871 := bstep (se 1 (by rfl) ⟨4750403, by rfl⟩ : syracuseStep 6333871 = 9500807) B9500807
theorem B6096343 : Blo 1170402 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B5006863 : Blo 1170402 5006863 := bstep (se 1 (by rfl) ⟨3755147, by rfl⟩ : syracuseStep 5006863 = 7510295) B7510295
theorem B2967151 : Blo 1170402 2967151 := bstep (se 1 (by rfl) ⟨2225363, by rfl⟩ : syracuseStep 2967151 = 4450727) B4450727
theorem B22824563 : Blo 1170402 22824563 := bstep (se 1 (by rfl) ⟨17118422, by rfl⟩ : syracuseStep 22824563 = 34236845) B34236845
theorem B6669985 : Blo 1170402 6669985 := bstep (se 2 (by rfl) ⟨2501244, by rfl⟩ : syracuseStep 6669985 = 5002489) B5002489
theorem B1877671 : Blo 1170402 1877671 := bstep (se 1 (by rfl) ⟨1408253, by rfl⟩ : syracuseStep 1877671 = 2816507) B2816507
theorem B2967263 : Blo 1170402 2967263 := bstep (se 1 (by rfl) ⟨2225447, by rfl⟩ : syracuseStep 2967263 = 4450895) B4450895
theorem B1976143 : Blo 1170402 1976143 := bstep (se 1 (by rfl) ⟨1482107, by rfl⟩ : syracuseStep 1976143 = 2964215) B2964215
theorem B3336383 : Blo 1170402 3336383 := bstep (se 1 (by rfl) ⟨2502287, by rfl⟩ : syracuseStep 3336383 = 5004575) B5004575
theorem B1976555 : Blo 1170402 1976555 := bstep (se 1 (by rfl) ⟨1482416, by rfl⟩ : syracuseStep 1976555 = 2964833) B2964833
theorem B2500903 : Blo 1170402 2500903 := bstep (se 1 (by rfl) ⟨1875677, by rfl⟩ : syracuseStep 2500903 = 3751355) B3751355
theorem B7506377 : Blo 1170402 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B14248487 : Blo 1170402 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B3426887 : Blo 1170402 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B13339241 : Blo 1170402 13339241 := bstep (se 2 (by rfl) ⟨5002215, by rfl⟩ : syracuseStep 13339241 = 10004431) B10004431
theorem B1755785 : Blo 1170402 1755785 := bstep (se 2 (by rfl) ⟨658419, by rfl⟩ : syracuseStep 1755785 = 1316839) B1316839
theorem B3951287 : Blo 1170402 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B506751673 : Blo 1170402 506751673 := bstep (se 2 (by rfl) ⟨190031877, by rfl⟩ : syracuseStep 506751673 = 380063755) B380063755
theorem B1755959 : Blo 1170402 1755959 := bstep (se 1 (by rfl) ⟨1316969, by rfl⟩ : syracuseStep 1755959 = 2633939) B2633939
theorem B2222903 : Blo 1170402 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B1755995 : Blo 1170402 1755995 := bstep (se 1 (by rfl) ⟨1316996, by rfl⟩ : syracuseStep 1755995 = 2633993) B2633993
theorem B4279259 : Blo 1170402 4279259 := bstep (se 1 (by rfl) ⟨3209444, by rfl⟩ : syracuseStep 4279259 = 6418889) B6418889
theorem B1756139 : Blo 1170402 1756139 := bstep (se 1 (by rfl) ⟨1317104, by rfl⟩ : syracuseStep 1756139 = 2634209) B2634209
theorem B1977385 : Blo 1170402 1977385 := bstep (se 2 (by rfl) ⟨741519, by rfl⟩ : syracuseStep 1977385 = 1483039) B1483039
theorem B4746383 : Blo 1170402 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B1756343 : Blo 1170402 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B1977527 : Blo 1170402 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B5926121 : Blo 1170402 5926121 := bstep (se 2 (by rfl) ⟨2222295, by rfl⟩ : syracuseStep 5926121 = 4444591) B4444591
theorem B1584463 : Blo 1170402 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B1756583 : Blo 1170402 1756583 := bstep (se 1 (by rfl) ⟨1317437, by rfl⟩ : syracuseStep 1756583 = 2634875) B2634875
theorem B9014777 : Blo 1170402 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1756667 : Blo 1170402 1756667 := bstep (se 1 (by rfl) ⟨1317500, by rfl⟩ : syracuseStep 1756667 = 2635001) B2635001
theorem B1977851 : Blo 1170402 1977851 := bstep (se 1 (by rfl) ⟨1483388, by rfl⟩ : syracuseStep 1977851 = 2966777) B2966777
theorem B1756763 : Blo 1170402 1756763 := bstep (se 1 (by rfl) ⟨1317572, by rfl⟩ : syracuseStep 1756763 = 2635145) B2635145
theorem B1756847 : Blo 1170402 1756847 := bstep (se 1 (by rfl) ⟨1317635, by rfl⟩ : syracuseStep 1756847 = 2635271) B2635271
theorem B15019769 : Blo 1170402 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B1756967 : Blo 1170402 1756967 := bstep (se 1 (by rfl) ⟨1317725, by rfl⟩ : syracuseStep 1756967 = 2635451) B2635451
theorem B1781543 : Blo 1170402 1781543 := bstep (se 1 (by rfl) ⟨1336157, by rfl⟩ : syracuseStep 1781543 = 2672315) B2672315
theorem B3338023 : Blo 1170402 3338023 := bstep (se 1 (by rfl) ⟨2503517, by rfl⟩ : syracuseStep 3338023 = 5007035) B5007035
theorem B1757051 : Blo 1170402 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B2633615 : Blo 1170402 2633615 := bstep (se 1 (by rfl) ⟨1975211, by rfl⟩ : syracuseStep 2633615 = 3950423) B3950423
theorem B2224027 : Blo 1170402 2224027 := bstep (se 1 (by rfl) ⟨1668020, by rfl⟩ : syracuseStep 2224027 = 3336041) B3336041
theorem B1978283 : Blo 1170402 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B12660785 : Blo 1170402 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B64065629 : Blo 1170402 64065629 := bstep (se 3 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 64065629 = 24024611) B24024611
theorem B1757471 : Blo 1170402 1757471 := bstep (se 1 (by rfl) ⟨1318103, by rfl⟩ : syracuseStep 1757471 = 2636207) B2636207
theorem B1757495 : Blo 1170402 1757495 := bstep (se 1 (by rfl) ⟨1318121, by rfl⟩ : syracuseStep 1757495 = 2636243) B2636243
theorem B1757567 : Blo 1170402 1757567 := bstep (se 1 (by rfl) ⟨1318175, by rfl⟩ : syracuseStep 1757567 = 2636351) B2636351
theorem B1757639 : Blo 1170402 1757639 := bstep (se 1 (by rfl) ⟨1318229, by rfl⟩ : syracuseStep 1757639 = 2636459) B2636459
theorem B5927417 : Blo 1170402 5927417 := bstep (se 2 (by rfl) ⟨2222781, by rfl⟩ : syracuseStep 5927417 = 4445563) B4445563
theorem B3953231 : Blo 1170402 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B2634335 : Blo 1170402 2634335 := bstep (se 1 (by rfl) ⟨1975751, by rfl⟩ : syracuseStep 2634335 = 3951503) B3951503
theorem B4223735 : Blo 1170402 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B6673175 : Blo 1170402 6673175 := bstep (se 1 (by rfl) ⟨5004881, by rfl⟩ : syracuseStep 6673175 = 10009763) B10009763
theorem B3003161 : Blo 1170402 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B1757993 : Blo 1170402 1757993 := bstep (se 2 (by rfl) ⟨659247, by rfl⟩ : syracuseStep 1757993 = 1318495) B1318495
theorem B1757999 : Blo 1170402 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B13333409 : Blo 1170402 13333409 := bstep (se 2 (by rfl) ⟨5000028, by rfl⟩ : syracuseStep 13333409 = 10000057) B10000057
theorem B1758119 : Blo 1170402 1758119 := bstep (se 1 (by rfl) ⟨1318589, by rfl⟩ : syracuseStep 1758119 = 2637179) B2637179
theorem B1758203 : Blo 1170402 1758203 := bstep (se 1 (by rfl) ⟨1318652, by rfl⟩ : syracuseStep 1758203 = 2637305) B2637305
theorem B1758263 : Blo 1170402 1758263 := bstep (se 1 (by rfl) ⟨1318697, by rfl⟩ : syracuseStep 1758263 = 2637395) B2637395
theorem B3953771 : Blo 1170402 3953771 := bstep (se 1 (by rfl) ⟨2965328, by rfl⟩ : syracuseStep 3953771 = 5930657) B5930657
theorem B1668271 : Blo 1170402 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B1758383 : Blo 1170402 1758383 := bstep (se 1 (by rfl) ⟨1318787, by rfl⟩ : syracuseStep 1758383 = 2637575) B2637575
theorem B14243035 : Blo 1170402 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B2635163 : Blo 1170402 2635163 := bstep (se 1 (by rfl) ⟨1976372, by rfl⟩ : syracuseStep 2635163 = 3952745) B3952745
theorem B6665885 : Blo 1170402 6665885 := bstep (se 3 (by rfl) ⟨1249853, by rfl⟩ : syracuseStep 6665885 = 2499707) B2499707
theorem B4445867 : Blo 1170402 4445867 := bstep (se 1 (by rfl) ⟨3334400, by rfl⟩ : syracuseStep 4445867 = 6668801) B6668801
theorem B2963263 : Blo 1170402 2963263 := bstep (se 1 (by rfl) ⟨2222447, by rfl⟩ : syracuseStep 2963263 = 4444895) B4444895
theorem B16250701 : Blo 1170402 16250701 := bstep (se 3 (by rfl) ⟨3047006, by rfl⟩ : syracuseStep 16250701 = 6094013) B6094013
theorem B6674359 : Blo 1170402 6674359 := bstep (se 1 (by rfl) ⟨5005769, by rfl⟩ : syracuseStep 6674359 = 10011539) B10011539
theorem B2635739 : Blo 1170402 2635739 := bstep (se 1 (by rfl) ⟨1976804, by rfl⟩ : syracuseStep 2635739 = 3953609) B3953609
theorem B5625881 : Blo 1170402 5625881 := bstep (se 2 (by rfl) ⟨2109705, by rfl⟩ : syracuseStep 5625881 = 4219411) B4219411
theorem B3749971 : Blo 1170402 3749971 := bstep (se 1 (by rfl) ⟨2812478, by rfl⟩ : syracuseStep 3749971 = 5624957) B5624957
theorem B2635919 : Blo 1170402 2635919 := bstep (se 1 (by rfl) ⟨1976939, by rfl⟩ : syracuseStep 2635919 = 3953879) B3953879
theorem B1317019 : Blo 1170402 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B2635937 : Blo 1170402 2635937 := bstep (se 2 (by rfl) ⟨988476, by rfl⟩ : syracuseStep 2635937 = 1976953) B1976953
theorem B1317055 : Blo 1170402 1317055 := bstep (se 1 (by rfl) ⟨987791, by rfl⟩ : syracuseStep 1317055 = 1975583) B1975583
theorem B2636009 : Blo 1170402 2636009 := bstep (se 2 (by rfl) ⟨988503, by rfl⟩ : syracuseStep 2636009 = 1977007) B1977007
theorem B2963699 : Blo 1170402 2963699 := bstep (se 1 (by rfl) ⟨2222774, by rfl⟩ : syracuseStep 2963699 = 4445549) B4445549
theorem B3750151 : Blo 1170402 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B2005295 : Blo 1170402 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B6666569 : Blo 1170402 6666569 := bstep (se 2 (by rfl) ⟨2499963, by rfl⟩ : syracuseStep 6666569 = 4999927) B4999927
theorem B3955067 : Blo 1170402 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B10680893 : Blo 1170402 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B3955337 : Blo 1170402 3955337 := bstep (se 2 (by rfl) ⟨1483251, by rfl⟩ : syracuseStep 3955337 = 2966503) B2966503
theorem B1170479 : Blo 1170402 1170479 := bstep (se 1 (by rfl) ⟨877859, by rfl⟩ : syracuseStep 1170479 = 1755719) B1755719
theorem B1170503 : Blo 1170402 1170503 := bstep (se 1 (by rfl) ⟨877877, by rfl⟩ : syracuseStep 1170503 = 1755755) B1755755
theorem B3382343 : Blo 1170402 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B6331607 : Blo 1170402 6331607 := bstep (se 1 (by rfl) ⟨4748705, by rfl⟩ : syracuseStep 6331607 = 9497411) B9497411
theorem B1170655 : Blo 1170402 1170655 := bstep (se 1 (by rfl) ⟨877991, by rfl⟩ : syracuseStep 1170655 = 1755983) B1755983
theorem B1170919 : Blo 1170402 1170919 := bstep (se 1 (by rfl) ⟨878189, by rfl⟩ : syracuseStep 1170919 = 1756379) B1756379
theorem B2637287 : Blo 1170402 2637287 := bstep (se 1 (by rfl) ⟨1977965, by rfl⟩ : syracuseStep 2637287 = 3955931) B3955931
theorem B1171035 : Blo 1170402 1171035 := bstep (se 1 (by rfl) ⟨878276, by rfl⟩ : syracuseStep 1171035 = 1756553) B1756553
theorem B131726989 : Blo 1170402 131726989 := bstep (se 3 (by rfl) ⟨24698810, by rfl⟩ : syracuseStep 131726989 = 49397621) B49397621
theorem B9502433 : Blo 1170402 9502433 := bstep (se 2 (by rfl) ⟨3563412, by rfl⟩ : syracuseStep 9502433 = 7126825) B7126825
theorem B3956471 : Blo 1170402 3956471 := bstep (se 1 (by rfl) ⟨2967353, by rfl⟩ : syracuseStep 3956471 = 5934707) B5934707
theorem B1171271 : Blo 1170402 1171271 := bstep (se 1 (by rfl) ⟨878453, by rfl⟩ : syracuseStep 1171271 = 1756907) B1756907
theorem B2965319 : Blo 1170402 2965319 := bstep (se 1 (by rfl) ⟨2223989, by rfl⟩ : syracuseStep 2965319 = 4447979) B4447979
theorem B1482619 : Blo 1170402 1482619 := bstep (se 1 (by rfl) ⟨1111964, by rfl⟩ : syracuseStep 1482619 = 2223929) B2223929
theorem B10862545 : Blo 1170402 10862545 := bstep (se 2 (by rfl) ⟨4073454, by rfl⟩ : syracuseStep 10862545 = 8146909) B8146909
theorem B1171423 : Blo 1170402 1171423 := bstep (se 1 (by rfl) ⟨878567, by rfl⟩ : syracuseStep 1171423 = 1757135) B1757135
theorem B1171647 : Blo 1170402 1171647 := bstep (se 1 (by rfl) ⟨878735, by rfl⟩ : syracuseStep 1171647 = 1757471) B1757471
theorem B8896715 : Blo 1170402 8896715 := bstep (se 1 (by rfl) ⟨6672536, by rfl⟩ : syracuseStep 8896715 = 13345073) B13345073
theorem B1171663 : Blo 1170402 1171663 := bstep (se 1 (by rfl) ⟨878747, by rfl⟩ : syracuseStep 1171663 = 1757495) B1757495
theorem B2375915 : Blo 1170402 2375915 := bstep (se 1 (by rfl) ⟨1781936, by rfl⟩ : syracuseStep 2375915 = 3563873) B3563873
theorem B1171711 : Blo 1170402 1171711 := bstep (se 1 (by rfl) ⟨878783, by rfl⟩ : syracuseStep 1171711 = 1757567) B1757567
theorem B1171759 : Blo 1170402 1171759 := bstep (se 1 (by rfl) ⟨878819, by rfl⟩ : syracuseStep 1171759 = 1757639) B1757639
theorem B3334537 : Blo 1170402 3334537 := bstep (se 2 (by rfl) ⟨1250451, by rfl⟩ : syracuseStep 3334537 = 2500903) B2500903
theorem B4448783 : Blo 1170402 4448783 := bstep (se 1 (by rfl) ⟨3336587, by rfl⟩ : syracuseStep 4448783 = 6673175) B6673175
theorem B1171995 : Blo 1170402 1171995 := bstep (se 1 (by rfl) ⟨878996, by rfl⟩ : syracuseStep 1171995 = 1757993) B1757993
theorem B1171999 : Blo 1170402 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B8888939 : Blo 1170402 8888939 := bstep (se 1 (by rfl) ⟨6666704, by rfl⟩ : syracuseStep 8888939 = 13333409) B13333409
theorem B1172079 : Blo 1170402 1172079 := bstep (se 1 (by rfl) ⟨879059, by rfl⟩ : syracuseStep 1172079 = 1758119) B1758119
theorem B1172135 : Blo 1170402 1172135 := bstep (se 1 (by rfl) ⟨879101, by rfl⟩ : syracuseStep 1172135 = 1758203) B1758203
theorem B1172175 : Blo 1170402 1172175 := bstep (se 1 (by rfl) ⟨879131, by rfl⟩ : syracuseStep 1172175 = 1758263) B1758263
theorem B1172255 : Blo 1170402 1172255 := bstep (se 1 (by rfl) ⟨879191, by rfl⟩ : syracuseStep 1172255 = 1758383) B1758383
theorem B675668897 : Blo 1170402 675668897 := bstep (se 2 (by rfl) ⟨253375836, by rfl⟩ : syracuseStep 675668897 = 506751673) B506751673
theorem B1975799 : Blo 1170402 1975799 := bstep (se 1 (by rfl) ⟨1481849, by rfl⟩ : syracuseStep 1975799 = 2963699) B2963699
theorem B18990713 : Blo 1170402 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B7120595 : Blo 1170402 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B8128457 : Blo 1170402 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B2852839 : Blo 1170402 2852839 := bstep (se 1 (by rfl) ⟨2139629, by rfl⟩ : syracuseStep 2852839 = 4279259) B4279259
theorem B2254895 : Blo 1170402 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B3164255 : Blo 1170402 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B4221071 : Blo 1170402 4221071 := bstep (se 1 (by rfl) ⟨3165803, by rfl⟩ : syracuseStep 4221071 = 6331607) B6331607
theorem B3950747 : Blo 1170402 3950747 := bstep (se 1 (by rfl) ⟨2963060, by rfl⟩ : syracuseStep 3950747 = 5926121) B5926121
theorem B4450697 : Blo 1170402 4450697 := bstep (se 2 (by rfl) ⟨1669011, by rfl⟩ : syracuseStep 4450697 = 3338023) B3338023
theorem B3951017 : Blo 1170402 3951017 := bstep (se 2 (by rfl) ⟨1481631, by rfl⟩ : syracuseStep 3951017 = 2963263) B2963263
theorem B6334955 : Blo 1170402 6334955 := bstep (se 1 (by rfl) ⟨4751216, by rfl⟩ : syracuseStep 6334955 = 9502433) B9502433
theorem B1976825 : Blo 1170402 1976825 := bstep (se 2 (by rfl) ⟨741309, by rfl⟩ : syracuseStep 1976825 = 1482619) B1482619
theorem B10013179 : Blo 1170402 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B1976879 : Blo 1170402 1976879 := bstep (se 1 (by rfl) ⟨1482659, by rfl⟩ : syracuseStep 1976879 = 2965319) B2965319
theorem B8899145 : Blo 1170402 8899145 := bstep (se 2 (by rfl) ⟨3337179, by rfl⟩ : syracuseStep 8899145 = 6674359) B6674359
theorem B1755743 : Blo 1170402 1755743 := bstep (se 1 (by rfl) ⟨1316807, by rfl⟩ : syracuseStep 1755743 = 2633615) B2633615
theorem B8440523 : Blo 1170402 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B1977095 : Blo 1170402 1977095 := bstep (se 1 (by rfl) ⟨1482821, by rfl⟩ : syracuseStep 1977095 = 2965643) B2965643
theorem B4999961 : Blo 1170402 4999961 := bstep (se 2 (by rfl) ⟨1874985, by rfl⟩ : syracuseStep 4999961 = 3749971) B3749971
theorem B1756025 : Blo 1170402 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B1756073 : Blo 1170402 1756073 := bstep (se 2 (by rfl) ⟨658527, by rfl⟩ : syracuseStep 1756073 = 1317055) B1317055
theorem B2223055 : Blo 1170402 2223055 := bstep (se 1 (by rfl) ⟨1667291, by rfl⟩ : syracuseStep 2223055 = 3334583) B3334583
theorem B1977311 : Blo 1170402 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B3951611 : Blo 1170402 3951611 := bstep (se 1 (by rfl) ⟨2963708, by rfl⟩ : syracuseStep 3951611 = 5927417) B5927417
theorem B5000201 : Blo 1170402 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B1756223 : Blo 1170402 1756223 := bstep (se 1 (by rfl) ⟨1317167, by rfl⟩ : syracuseStep 1756223 = 2634335) B2634335
theorem B37973123 : Blo 1170402 37973123 := bstep (se 1 (by rfl) ⟨28479842, by rfl⟩ : syracuseStep 37973123 = 56959685) B56959685
theorem B1977655 : Blo 1170402 1977655 := bstep (se 1 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 1977655 = 2966483) B2966483
theorem B8564105 : Blo 1170402 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B1756775 : Blo 1170402 1756775 := bstep (se 1 (by rfl) ⟨1317581, by rfl⟩ : syracuseStep 1756775 = 2635163) B2635163
theorem B4443923 : Blo 1170402 4443923 := bstep (se 1 (by rfl) ⟨3332942, by rfl⟩ : syracuseStep 4443923 = 6665885) B6665885
theorem B1978175 : Blo 1170402 1978175 := bstep (se 1 (by rfl) ⟨1483631, by rfl⟩ : syracuseStep 1978175 = 2967263) B2967263
theorem B1978249 : Blo 1170402 1978249 := bstep (se 2 (by rfl) ⟨741843, by rfl⟩ : syracuseStep 1978249 = 1483687) B1483687
theorem B1757159 : Blo 1170402 1757159 := bstep (se 1 (by rfl) ⟨1317869, by rfl⟩ : syracuseStep 1757159 = 2635739) B2635739
theorem B1757279 : Blo 1170402 1757279 := bstep (se 1 (by rfl) ⟨1317959, by rfl⟩ : syracuseStep 1757279 = 2635919) B2635919
theorem B1757291 : Blo 1170402 1757291 := bstep (se 1 (by rfl) ⟨1317968, by rfl⟩ : syracuseStep 1757291 = 2635937) B2635937
theorem B2224255 : Blo 1170402 2224255 := bstep (se 1 (by rfl) ⟨1668191, by rfl⟩ : syracuseStep 2224255 = 3336383) B3336383
theorem B1757339 : Blo 1170402 1757339 := bstep (se 1 (by rfl) ⟨1318004, by rfl⟩ : syracuseStep 1757339 = 2636009) B2636009
theorem B9138365 : Blo 1170402 9138365 := bstep (se 3 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 9138365 = 3426887) B3426887
theorem B4444379 : Blo 1170402 4444379 := bstep (se 1 (by rfl) ⟨3333284, by rfl⟩ : syracuseStep 4444379 = 6666569) B6666569
theorem B2224361 : Blo 1170402 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B9498991 : Blo 1170402 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B8892827 : Blo 1170402 8892827 := bstep (se 1 (by rfl) ⟨6669620, by rfl⟩ : syracuseStep 8892827 = 13339241) B13339241
theorem B2634191 : Blo 1170402 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B8008429 : Blo 1170402 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B5927741 : Blo 1170402 5927741 := bstep (se 3 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 5927741 = 2222903) B2222903
theorem B8893313 : Blo 1170402 8893313 := bstep (se 2 (by rfl) ⟨3334992, by rfl⟩ : syracuseStep 8893313 = 6669985) B6669985
theorem B2503561 : Blo 1170402 2503561 := bstep (se 2 (by rfl) ⟨938835, by rfl⟩ : syracuseStep 2503561 = 1877671) B1877671
theorem B1758191 : Blo 1170402 1758191 := bstep (se 1 (by rfl) ⟨1318643, by rfl⟩ : syracuseStep 1758191 = 2637287) B2637287
theorem B6009851 : Blo 1170402 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B2634857 : Blo 1170402 2634857 := bstep (se 2 (by rfl) ⟨988071, by rfl⟩ : syracuseStep 2634857 = 1976143) B1976143
theorem B1758575 : Blo 1170402 1758575 := bstep (se 1 (by rfl) ⟨1318931, by rfl⟩ : syracuseStep 1758575 = 2637863) B2637863
theorem B42710419 : Blo 1170402 42710419 := bstep (se 1 (by rfl) ⟨32032814, by rfl⟩ : syracuseStep 42710419 = 64065629) B64065629
theorem B2635487 : Blo 1170402 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B8894285 : Blo 1170402 8894285 := bstep (se 3 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 8894285 = 3335357) B3335357
theorem B2815823 : Blo 1170402 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B1316731 : Blo 1170402 1316731 := bstep (se 1 (by rfl) ⟨987548, by rfl⟩ : syracuseStep 1316731 = 1975097) B1975097
theorem B1316767 : Blo 1170402 1316767 := bstep (se 1 (by rfl) ⟨987575, by rfl⟩ : syracuseStep 1316767 = 1975151) B1975151
theorem B2635847 : Blo 1170402 2635847 := bstep (se 1 (by rfl) ⟨1976885, by rfl⟩ : syracuseStep 2635847 = 3953771) B3953771
theorem B5347453 : Blo 1170402 5347453 := bstep (se 3 (by rfl) ⟨1002647, by rfl⟩ : syracuseStep 5347453 = 2005295) B2005295
theorem B25319567 : Blo 1170402 25319567 := bstep (se 1 (by rfl) ⟨18989675, by rfl⟩ : syracuseStep 25319567 = 37979351) B37979351
theorem B4446521 : Blo 1170402 4446521 := bstep (se 2 (by rfl) ⟨1667445, by rfl⟩ : syracuseStep 4446521 = 3334891) B3334891
theorem B2963911 : Blo 1170402 2963911 := bstep (se 1 (by rfl) ⟨2222933, by rfl⟩ : syracuseStep 2963911 = 4445867) B4445867
theorem B3750587 : Blo 1170402 3750587 := bstep (se 1 (by rfl) ⟨2812940, by rfl⟩ : syracuseStep 3750587 = 5625881) B5625881
theorem B75979457 : Blo 1170402 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B2636513 : Blo 1170402 2636513 := bstep (se 2 (by rfl) ⟨988692, by rfl⟩ : syracuseStep 2636513 = 1977385) B1977385
theorem B1317703 : Blo 1170402 1317703 := bstep (se 1 (by rfl) ⟨988277, by rfl⟩ : syracuseStep 1317703 = 1976555) B1976555
theorem B2636711 : Blo 1170402 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B13523921 : Blo 1170402 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B5004251 : Blo 1170402 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B60865501 : Blo 1170402 60865501 := bstep (se 3 (by rfl) ⟨11412281, by rfl⟩ : syracuseStep 60865501 = 22824563) B22824563
theorem B1170523 : Blo 1170402 1170523 := bstep (se 1 (by rfl) ⟨877892, by rfl⟩ : syracuseStep 1170523 = 1755785) B1755785
theorem B2636891 : Blo 1170402 2636891 := bstep (se 1 (by rfl) ⟨1977668, by rfl⟩ : syracuseStep 2636891 = 3955337) B3955337
theorem B2112617 : Blo 1170402 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B1170639 : Blo 1170402 1170639 := bstep (se 1 (by rfl) ⟨877979, by rfl⟩ : syracuseStep 1170639 = 1755959) B1755959
theorem B1170663 : Blo 1170402 1170663 := bstep (se 1 (by rfl) ⟨877997, by rfl⟩ : syracuseStep 1170663 = 1755995) B1755995
theorem B8445161 : Blo 1170402 8445161 := bstep (se 2 (by rfl) ⟨3166935, by rfl⟩ : syracuseStep 8445161 = 6333871) B6333871
theorem B1170759 : Blo 1170402 1170759 := bstep (se 1 (by rfl) ⟨878069, by rfl⟩ : syracuseStep 1170759 = 1756139) B1756139
theorem B6675817 : Blo 1170402 6675817 := bstep (se 2 (by rfl) ⟨2503431, by rfl⟩ : syracuseStep 6675817 = 5006863) B5006863
theorem B1170895 : Blo 1170402 1170895 := bstep (se 1 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 1170895 = 1756343) B1756343
theorem B1318351 : Blo 1170402 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B3956201 : Blo 1170402 3956201 := bstep (se 2 (by rfl) ⟨1483575, by rfl⟩ : syracuseStep 3956201 = 2967151) B2967151
theorem B175635985 : Blo 1170402 175635985 := bstep (se 2 (by rfl) ⟨65863494, by rfl⟩ : syracuseStep 175635985 = 131726989) B131726989
theorem B1171055 : Blo 1170402 1171055 := bstep (se 1 (by rfl) ⟨878291, by rfl⟩ : syracuseStep 1171055 = 1756583) B1756583
theorem B1171111 : Blo 1170402 1171111 := bstep (se 1 (by rfl) ⟨878333, by rfl⟩ : syracuseStep 1171111 = 1756667) B1756667
theorem B1318567 : Blo 1170402 1318567 := bstep (se 1 (by rfl) ⟨988925, by rfl⟩ : syracuseStep 1318567 = 1977851) B1977851
theorem B1171175 : Blo 1170402 1171175 := bstep (se 1 (by rfl) ⟨878381, by rfl⟩ : syracuseStep 1171175 = 1756763) B1756763
theorem B21667601 : Blo 1170402 21667601 := bstep (se 2 (by rfl) ⟨8125350, by rfl⟩ : syracuseStep 21667601 = 16250701) B16250701
theorem B1171231 : Blo 1170402 1171231 := bstep (se 1 (by rfl) ⟨878423, by rfl⟩ : syracuseStep 1171231 = 1756847) B1756847
theorem B2637647 : Blo 1170402 2637647 := bstep (se 1 (by rfl) ⟨1978235, by rfl⟩ : syracuseStep 2637647 = 3956471) B3956471
theorem B1171311 : Blo 1170402 1171311 := bstep (se 1 (by rfl) ⟨878483, by rfl⟩ : syracuseStep 1171311 = 1756967) B1756967
theorem B1187695 : Blo 1170402 1187695 := bstep (se 1 (by rfl) ⟨890771, by rfl⟩ : syracuseStep 1187695 = 1781543) B1781543
theorem B2965369 : Blo 1170402 2965369 := bstep (se 2 (by rfl) ⟨1112013, by rfl⟩ : syracuseStep 2965369 = 2224027) B2224027
theorem B1171367 : Blo 1170402 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B14483393 : Blo 1170402 14483393 := bstep (se 2 (by rfl) ⟨5431272, by rfl⟩ : syracuseStep 14483393 = 10862545) B10862545
theorem B1318855 : Blo 1170402 1318855 := bstep (se 1 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 1318855 = 1978283) B1978283
theorem B1171519 : Blo 1170402 1171519 := bstep (se 1 (by rfl) ⟨878639, by rfl⟩ : syracuseStep 1171519 = 1757279) B1757279
theorem B1171527 : Blo 1170402 1171527 := bstep (se 1 (by rfl) ⟨878645, by rfl⟩ : syracuseStep 1171527 = 1757291) B1757291
theorem B1171559 : Blo 1170402 1171559 := bstep (se 1 (by rfl) ⟨878669, by rfl⟩ : syracuseStep 1171559 = 1757339) B1757339
theorem B5931143 : Blo 1170402 5931143 := bstep (se 1 (by rfl) ⟨4448357, by rfl⟩ : syracuseStep 5931143 = 8896715) B8896715
theorem B2965673 : Blo 1170402 2965673 := bstep (se 2 (by rfl) ⟨1112127, by rfl⟩ : syracuseStep 2965673 = 2224255) B2224255
theorem B2965855 : Blo 1170402 2965855 := bstep (se 1 (by rfl) ⟨2224391, by rfl⟩ : syracuseStep 2965855 = 4448783) B4448783
theorem B12665321 : Blo 1170402 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B450445931 : Blo 1170402 450445931 := bstep (se 1 (by rfl) ⟨337834448, by rfl⟩ : syracuseStep 450445931 = 675668897) B675668897
theorem B22520429 : Blo 1170402 22520429 := bstep (se 3 (by rfl) ⟨4222580, by rfl⟩ : syracuseStep 22520429 = 8445161) B8445161
theorem B5931629 : Blo 1170402 5931629 := bstep (se 3 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 5931629 = 2224361) B2224361
theorem B1172127 : Blo 1170402 1172127 := bstep (se 1 (by rfl) ⟨879095, by rfl⟩ : syracuseStep 1172127 = 1758191) B1758191
theorem B4006567 : Blo 1170402 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B1172383 : Blo 1170402 1172383 := bstep (se 1 (by rfl) ⟨879287, by rfl⟩ : syracuseStep 1172383 = 1758575) B1758575
theorem B2967131 : Blo 1170402 2967131 := bstep (se 1 (by rfl) ⟨2225348, by rfl⟩ : syracuseStep 2967131 = 4450697) B4450697
theorem B5932763 : Blo 1170402 5932763 := bstep (se 1 (by rfl) ⟨4449572, by rfl⟩ : syracuseStep 5932763 = 8899145) B8899145
theorem B2500391 : Blo 1170402 2500391 := bstep (se 1 (by rfl) ⟨1875293, by rfl⟩ : syracuseStep 2500391 = 3750587) B3750587
theorem B50652971 : Blo 1170402 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B3336167 : Blo 1170402 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B25315415 : Blo 1170402 25315415 := bstep (se 1 (by rfl) ⟨18986561, by rfl⟩ : syracuseStep 25315415 = 37973123) B37973123
theorem B1583593 : Blo 1170402 1583593 := bstep (se 2 (by rfl) ⟨593847, by rfl⟩ : syracuseStep 1583593 = 1187695) B1187695
theorem B1755641 : Blo 1170402 1755641 := bstep (se 2 (by rfl) ⟨658365, by rfl⟩ : syracuseStep 1755641 = 1316731) B1316731
theorem B14445067 : Blo 1170402 14445067 := bstep (se 1 (by rfl) ⟨10833800, by rfl⟩ : syracuseStep 14445067 = 21667601) B21667601
theorem B15215141 : Blo 1170402 15215141 := bstep (se 4 (by rfl) ⟨1426419, by rfl⟩ : syracuseStep 15215141 = 2852839) B2852839
theorem B1755689 : Blo 1170402 1755689 := bstep (se 2 (by rfl) ⟨658383, by rfl⟩ : syracuseStep 1755689 = 1316767) B1316767
theorem B7129937 : Blo 1170402 7129937 := bstep (se 2 (by rfl) ⟨2673726, by rfl⟩ : syracuseStep 7129937 = 5347453) B5347453
theorem B1756127 : Blo 1170402 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B5925959 : Blo 1170402 5925959 := bstep (se 1 (by rfl) ⟨4444469, by rfl⟩ : syracuseStep 5925959 = 8888939) B8888939
theorem B3951827 : Blo 1170402 3951827 := bstep (se 1 (by rfl) ⟨2963870, by rfl⟩ : syracuseStep 3951827 = 5927741) B5927741
theorem B3951881 : Blo 1170402 3951881 := bstep (se 2 (by rfl) ⟨1481955, by rfl⟩ : syracuseStep 3951881 = 2963911) B2963911
theorem B1756571 : Blo 1170402 1756571 := bstep (se 1 (by rfl) ⟨1317428, by rfl⟩ : syracuseStep 1756571 = 2634857) B2634857
theorem B10677905 : Blo 1170402 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B12660475 : Blo 1170402 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B1756937 : Blo 1170402 1756937 := bstep (se 2 (by rfl) ⟨658851, by rfl⟩ : syracuseStep 1756937 = 1317703) B1317703
theorem B1756991 : Blo 1170402 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B3338081 : Blo 1170402 3338081 := bstep (se 2 (by rfl) ⟨1251780, by rfl⟩ : syracuseStep 3338081 = 2503561) B2503561
theorem B81154001 : Blo 1170402 81154001 := bstep (se 2 (by rfl) ⟨30432750, by rfl⟩ : syracuseStep 81154001 = 60865501) B60865501
theorem B5418971 : Blo 1170402 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B1503263 : Blo 1170402 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B1757231 : Blo 1170402 1757231 := bstep (se 1 (by rfl) ⟨1317923, by rfl⟩ : syracuseStep 1757231 = 2635847) B2635847
theorem B2109503 : Blo 1170402 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B16879711 : Blo 1170402 16879711 := bstep (se 1 (by rfl) ⟨12659783, by rfl⟩ : syracuseStep 16879711 = 25319567) B25319567
theorem B2814047 : Blo 1170402 2814047 := bstep (se 1 (by rfl) ⟨2110535, by rfl⟩ : syracuseStep 2814047 = 4221071) B4221071
theorem B2633831 : Blo 1170402 2633831 := bstep (se 1 (by rfl) ⟨1975373, by rfl⟩ : syracuseStep 2633831 = 3950747) B3950747
theorem B2634011 : Blo 1170402 2634011 := bstep (se 1 (by rfl) ⟨1975508, by rfl⟩ : syracuseStep 2634011 = 3951017) B3951017
theorem B4223303 : Blo 1170402 4223303 := bstep (se 1 (by rfl) ⟨3167477, by rfl⟩ : syracuseStep 4223303 = 6334955) B6334955
theorem B8901089 : Blo 1170402 8901089 := bstep (se 2 (by rfl) ⟨3337908, by rfl⟩ : syracuseStep 8901089 = 6675817) B6675817
theorem B1757675 : Blo 1170402 1757675 := bstep (se 1 (by rfl) ⟨1318256, by rfl⟩ : syracuseStep 1757675 = 2636513) B2636513
theorem B56947225 : Blo 1170402 56947225 := bstep (se 2 (by rfl) ⟨21355209, by rfl⟩ : syracuseStep 56947225 = 42710419) B42710419
theorem B1757801 : Blo 1170402 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B1757807 : Blo 1170402 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B9015947 : Blo 1170402 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B2634407 : Blo 1170402 2634407 := bstep (se 1 (by rfl) ⟨1975805, by rfl⟩ : syracuseStep 2634407 = 3951611) B3951611
theorem B234181313 : Blo 1170402 234181313 := bstep (se 2 (by rfl) ⟨87817992, by rfl⟩ : syracuseStep 234181313 = 175635985) B175635985
theorem B1757927 : Blo 1170402 1757927 := bstep (se 1 (by rfl) ⟨1318445, by rfl⟩ : syracuseStep 1757927 = 2636891) B2636891
theorem B7508861 : Blo 1170402 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B1758089 : Blo 1170402 1758089 := bstep (se 2 (by rfl) ⟨659283, by rfl⟩ : syracuseStep 1758089 = 1318567) B1318567
theorem B25343093 : Blo 1170402 25343093 := bstep (se 5 (by rfl) ⟨1187957, by rfl⟩ : syracuseStep 25343093 = 2375915) B2375915
theorem B3953825 : Blo 1170402 3953825 := bstep (se 2 (by rfl) ⟨1482684, by rfl⟩ : syracuseStep 3953825 = 2965369) B2965369
theorem B2962615 : Blo 1170402 2962615 := bstep (se 1 (by rfl) ⟨2221961, by rfl⟩ : syracuseStep 2962615 = 4443923) B4443923
theorem B1758431 : Blo 1170402 1758431 := bstep (se 1 (by rfl) ⟨1318823, by rfl⟩ : syracuseStep 1758431 = 2637647) B2637647
theorem B1758473 : Blo 1170402 1758473 := bstep (se 2 (by rfl) ⟨659427, by rfl⟩ : syracuseStep 1758473 = 1318855) B1318855
theorem B9655595 : Blo 1170402 9655595 := bstep (se 1 (by rfl) ⟨7241696, by rfl⟩ : syracuseStep 9655595 = 14483393) B14483393
theorem B6092243 : Blo 1170402 6092243 := bstep (se 1 (by rfl) ⟨4569182, by rfl⟩ : syracuseStep 6092243 = 9138365) B9138365
theorem B2962919 : Blo 1170402 2962919 := bstep (se 1 (by rfl) ⟨2222189, by rfl⟩ : syracuseStep 2962919 = 4444379) B4444379
theorem B5928551 : Blo 1170402 5928551 := bstep (se 1 (by rfl) ⟨4446413, by rfl⟩ : syracuseStep 5928551 = 8892827) B8892827
theorem B4446049 : Blo 1170402 4446049 := bstep (se 2 (by rfl) ⟨1667268, by rfl⟩ : syracuseStep 4446049 = 3334537) B3334537
theorem B5928875 : Blo 1170402 5928875 := bstep (se 1 (by rfl) ⟨4446656, by rfl⟩ : syracuseStep 5928875 = 8893313) B8893313
theorem B13350905 : Blo 1170402 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B1317199 : Blo 1170402 1317199 := bstep (se 1 (by rfl) ⟨987899, by rfl⟩ : syracuseStep 1317199 = 1975799) B1975799
theorem B5929523 : Blo 1170402 5929523 := bstep (se 1 (by rfl) ⟨4447142, by rfl⟩ : syracuseStep 5929523 = 8894285) B8894285
theorem B2964073 : Blo 1170402 2964073 := bstep (se 2 (by rfl) ⟨1111527, by rfl⟩ : syracuseStep 2964073 = 2223055) B2223055
theorem B2964347 : Blo 1170402 2964347 := bstep (se 1 (by rfl) ⟨2223260, by rfl⟩ : syracuseStep 2964347 = 4446521) B4446521
theorem B1317883 : Blo 1170402 1317883 := bstep (se 1 (by rfl) ⟨988412, by rfl⟩ : syracuseStep 1317883 = 1976825) B1976825
theorem B1317919 : Blo 1170402 1317919 := bstep (se 1 (by rfl) ⟨988439, by rfl⟩ : syracuseStep 1317919 = 1976879) B1976879
theorem B1170495 : Blo 1170402 1170495 := bstep (se 1 (by rfl) ⟨877871, by rfl⟩ : syracuseStep 1170495 = 1755743) B1755743
theorem B2636873 : Blo 1170402 2636873 := bstep (se 2 (by rfl) ⟨988827, by rfl⟩ : syracuseStep 2636873 = 1977655) B1977655
theorem B5627015 : Blo 1170402 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B1318063 : Blo 1170402 1318063 := bstep (se 1 (by rfl) ⟨988547, by rfl⟩ : syracuseStep 1318063 = 1977095) B1977095
theorem B3333307 : Blo 1170402 3333307 := bstep (se 1 (by rfl) ⟨2499980, by rfl⟩ : syracuseStep 3333307 = 4999961) B4999961
theorem B18988253 : Blo 1170402 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B1170683 : Blo 1170402 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B1170715 : Blo 1170402 1170715 := bstep (se 1 (by rfl) ⟨878036, by rfl⟩ : syracuseStep 1170715 = 1756073) B1756073
theorem B1318207 : Blo 1170402 1318207 := bstep (se 1 (by rfl) ⟨988655, by rfl⟩ : syracuseStep 1318207 = 1977311) B1977311
theorem B3333467 : Blo 1170402 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B1170815 : Blo 1170402 1170815 := bstep (se 1 (by rfl) ⟨878111, by rfl⟩ : syracuseStep 1170815 = 1756223) B1756223
theorem B1408411 : Blo 1170402 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B5709403 : Blo 1170402 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B2637467 : Blo 1170402 2637467 := bstep (se 1 (by rfl) ⟨1978100, by rfl⟩ : syracuseStep 2637467 = 3956201) B3956201
theorem B1171183 : Blo 1170402 1171183 := bstep (se 1 (by rfl) ⟨878387, by rfl⟩ : syracuseStep 1171183 = 1756775) B1756775
theorem B2637665 : Blo 1170402 2637665 := bstep (se 2 (by rfl) ⟨989124, by rfl⟩ : syracuseStep 2637665 = 1978249) B1978249
theorem B1318783 : Blo 1170402 1318783 := bstep (se 1 (by rfl) ⟨989087, by rfl⟩ : syracuseStep 1318783 = 1978175) B1978175
theorem B1171439 : Blo 1170402 1171439 := bstep (se 1 (by rfl) ⟨878579, by rfl⟩ : syracuseStep 1171439 = 1757159) B1757159
theorem B1171487 : Blo 1170402 1171487 := bstep (se 1 (by rfl) ⟨878615, by rfl⟩ : syracuseStep 1171487 = 1757231) B1757231
theorem B1876031 : Blo 1170402 1876031 := bstep (se 1 (by rfl) ⟨1407023, by rfl⟩ : syracuseStep 1876031 = 2814047) B2814047
theorem B1171783 : Blo 1170402 1171783 := bstep (se 1 (by rfl) ⟨878837, by rfl⟩ : syracuseStep 1171783 = 1757675) B1757675
theorem B1171867 : Blo 1170402 1171867 := bstep (se 1 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 1171867 = 1757801) B1757801
theorem B1171871 : Blo 1170402 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B1171951 : Blo 1170402 1171951 := bstep (se 1 (by rfl) ⟨878963, by rfl⟩ : syracuseStep 1171951 = 1757927) B1757927
theorem B5005907 : Blo 1170402 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B1172059 : Blo 1170402 1172059 := bstep (se 1 (by rfl) ⟨879044, by rfl⟩ : syracuseStep 1172059 = 1758089) B1758089
theorem B19260089 : Blo 1170402 19260089 := bstep (se 2 (by rfl) ⟨7222533, by rfl⟩ : syracuseStep 19260089 = 14445067) B14445067
theorem B1172287 : Blo 1170402 1172287 := bstep (se 1 (by rfl) ⟨879215, by rfl⟩ : syracuseStep 1172287 = 1758431) B1758431
theorem B1172315 : Blo 1170402 1172315 := bstep (se 1 (by rfl) ⟨879236, by rfl⟩ : syracuseStep 1172315 = 1758473) B1758473
theorem B1975279 : Blo 1170402 1975279 := bstep (se 1 (by rfl) ⟨1481459, by rfl⟩ : syracuseStep 1975279 = 2962919) B2962919
theorem B33768647 : Blo 1170402 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B16876943 : Blo 1170402 16876943 := bstep (se 1 (by rfl) ⟨12657707, by rfl⟩ : syracuseStep 16876943 = 25315415) B25315415
theorem B3950153 : Blo 1170402 3950153 := bstep (se 2 (by rfl) ⟨1481307, by rfl⟩ : syracuseStep 3950153 = 2962615) B2962615
theorem B10143427 : Blo 1170402 10143427 := bstep (se 1 (by rfl) ⟨7607570, by rfl⟩ : syracuseStep 10143427 = 15215141) B15215141
theorem B4753291 : Blo 1170402 4753291 := bstep (se 1 (by rfl) ⟨3564968, by rfl⟩ : syracuseStep 4753291 = 7129937) B7129937
theorem B1976231 : Blo 1170402 1976231 := bstep (se 1 (by rfl) ⟨1482173, by rfl⟩ : syracuseStep 1976231 = 2964347) B2964347
theorem B3950639 : Blo 1170402 3950639 := bstep (se 1 (by rfl) ⟨2962979, by rfl⟩ : syracuseStep 3950639 = 5925959) B5925959
theorem B7612537 : Blo 1170402 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B12658835 : Blo 1170402 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B2222311 : Blo 1170402 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B54102667 : Blo 1170402 54102667 := bstep (se 1 (by rfl) ⟨40577000, by rfl⟩ : syracuseStep 54102667 = 81154001) B81154001
theorem B1755887 : Blo 1170402 1755887 := bstep (se 1 (by rfl) ⟨1316915, by rfl⟩ : syracuseStep 1755887 = 2633831) B2633831
theorem B4008701 : Blo 1170402 4008701 := bstep (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) B1503263
theorem B1977115 : Blo 1170402 1977115 := bstep (se 1 (by rfl) ⟨1482836, by rfl⟩ : syracuseStep 1977115 = 2965673) B2965673
theorem B22506281 : Blo 1170402 22506281 := bstep (se 2 (by rfl) ⟨8439855, by rfl⟩ : syracuseStep 22506281 = 16879711) B16879711
theorem B1756007 : Blo 1170402 1756007 := bstep (se 1 (by rfl) ⟨1317005, by rfl⟩ : syracuseStep 1756007 = 2634011) B2634011
theorem B5934059 : Blo 1170402 5934059 := bstep (se 1 (by rfl) ⟨4450544, by rfl⟩ : syracuseStep 5934059 = 8901089) B8901089
theorem B300297287 : Blo 1170402 300297287 := bstep (se 1 (by rfl) ⟨225222965, by rfl⟩ : syracuseStep 300297287 = 450445931) B450445931
theorem B1756265 : Blo 1170402 1756265 := bstep (se 2 (by rfl) ⟨658599, by rfl⟩ : syracuseStep 1756265 = 1317199) B1317199
theorem B1756271 : Blo 1170402 1756271 := bstep (se 1 (by rfl) ⟨1317203, by rfl⟩ : syracuseStep 1756271 = 2634407) B2634407
theorem B16895395 : Blo 1170402 16895395 := bstep (se 1 (by rfl) ⟨12671546, by rfl⟩ : syracuseStep 16895395 = 25343093) B25343093
theorem B3952097 : Blo 1170402 3952097 := bstep (se 2 (by rfl) ⟨1482036, by rfl⟩ : syracuseStep 3952097 = 2964073) B2964073
theorem B21368357 : Blo 1170402 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B1978087 : Blo 1170402 1978087 := bstep (se 1 (by rfl) ⟨1483565, by rfl⟩ : syracuseStep 1978087 = 2967131) B2967131
theorem B3952367 : Blo 1170402 3952367 := bstep (se 1 (by rfl) ⟨2964275, by rfl⟩ : syracuseStep 3952367 = 5928551) B5928551
theorem B1666927 : Blo 1170402 1666927 := bstep (se 1 (by rfl) ⟨1250195, by rfl⟩ : syracuseStep 1666927 = 2500391) B2500391
theorem B3952583 : Blo 1170402 3952583 := bstep (se 1 (by rfl) ⟨2964437, by rfl⟩ : syracuseStep 3952583 = 5928875) B5928875
theorem B2224111 : Blo 1170402 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B1757177 : Blo 1170402 1757177 := bstep (se 2 (by rfl) ⟨658941, by rfl⟩ : syracuseStep 1757177 = 1317883) B1317883
theorem B8900603 : Blo 1170402 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B1757225 : Blo 1170402 1757225 := bstep (se 2 (by rfl) ⟨658959, by rfl⟩ : syracuseStep 1757225 = 1317919) B1317919
theorem B1757417 : Blo 1170402 1757417 := bstep (se 2 (by rfl) ⟨659031, by rfl⟩ : syracuseStep 1757417 = 1318063) B1318063
theorem B4444409 : Blo 1170402 4444409 := bstep (se 2 (by rfl) ⟨1666653, by rfl⟩ : syracuseStep 4444409 = 3333307) B3333307
theorem B3953015 : Blo 1170402 3953015 := bstep (se 1 (by rfl) ⟨2964761, by rfl⟩ : syracuseStep 3953015 = 5929523) B5929523
theorem B1757609 : Blo 1170402 1757609 := bstep (se 2 (by rfl) ⟨659103, by rfl⟩ : syracuseStep 1757609 = 1318207) B1318207
theorem B1757915 : Blo 1170402 1757915 := bstep (se 1 (by rfl) ⟨1318436, by rfl⟩ : syracuseStep 1757915 = 2636873) B2636873
theorem B2634551 : Blo 1170402 2634551 := bstep (se 1 (by rfl) ⟨1975913, by rfl⟩ : syracuseStep 2634551 = 3951827) B3951827
theorem B2634587 : Blo 1170402 2634587 := bstep (se 1 (by rfl) ⟨1975940, by rfl⟩ : syracuseStep 2634587 = 3951881) B3951881
theorem B16880633 : Blo 1170402 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B1758311 : Blo 1170402 1758311 := bstep (se 1 (by rfl) ⟨1318733, by rfl⟩ : syracuseStep 1758311 = 2637467) B2637467
theorem B5928065 : Blo 1170402 5928065 := bstep (se 2 (by rfl) ⟨2223024, by rfl⟩ : syracuseStep 5928065 = 4446049) B4446049
theorem B1758377 : Blo 1170402 1758377 := bstep (se 2 (by rfl) ⟨659391, by rfl⟩ : syracuseStep 1758377 = 1318783) B1318783
theorem B2225387 : Blo 1170402 2225387 := bstep (se 1 (by rfl) ⟨1669040, by rfl⟩ : syracuseStep 2225387 = 3338081) B3338081
theorem B1758443 : Blo 1170402 1758443 := bstep (se 1 (by rfl) ⟨1318832, by rfl⟩ : syracuseStep 1758443 = 2637665) B2637665
theorem B3954095 : Blo 1170402 3954095 := bstep (se 1 (by rfl) ⟨2965571, by rfl⟩ : syracuseStep 3954095 = 5931143) B5931143
theorem B5625341 : Blo 1170402 5625341 := bstep (se 3 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 5625341 = 2109503) B2109503
theorem B2815535 : Blo 1170402 2815535 := bstep (se 1 (by rfl) ⟨2111651, by rfl⟩ : syracuseStep 2815535 = 4223303) B4223303
theorem B8443547 : Blo 1170402 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B15013619 : Blo 1170402 15013619 := bstep (se 1 (by rfl) ⟨11260214, by rfl⟩ : syracuseStep 15013619 = 22520429) B22520429
theorem B3954419 : Blo 1170402 3954419 := bstep (se 1 (by rfl) ⟨2965814, by rfl⟩ : syracuseStep 3954419 = 5931629) B5931629
theorem B6010631 : Blo 1170402 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B3954473 : Blo 1170402 3954473 := bstep (se 2 (by rfl) ⟨1482927, by rfl⟩ : syracuseStep 3954473 = 2965855) B2965855
theorem B156120875 : Blo 1170402 156120875 := bstep (se 1 (by rfl) ⟨117090656, by rfl⟩ : syracuseStep 156120875 = 234181313) B234181313
theorem B75929633 : Blo 1170402 75929633 := bstep (se 2 (by rfl) ⟨28473612, by rfl⟩ : syracuseStep 75929633 = 56947225) B56947225
theorem B2635883 : Blo 1170402 2635883 := bstep (se 1 (by rfl) ⟨1976912, by rfl⟩ : syracuseStep 2635883 = 3953825) B3953825
theorem B6437063 : Blo 1170402 6437063 := bstep (se 1 (by rfl) ⟨4827797, by rfl⟩ : syracuseStep 6437063 = 9655595) B9655595
theorem B4061495 : Blo 1170402 4061495 := bstep (se 1 (by rfl) ⟨3046121, by rfl⟩ : syracuseStep 4061495 = 6092243) B6092243
theorem B3955175 : Blo 1170402 3955175 := bstep (se 1 (by rfl) ⟨2966381, by rfl⟩ : syracuseStep 3955175 = 5932763) B5932763
theorem B1170427 : Blo 1170402 1170427 := bstep (se 1 (by rfl) ⟨877820, by rfl⟩ : syracuseStep 1170427 = 1755641) B1755641
theorem B1170459 : Blo 1170402 1170459 := bstep (se 1 (by rfl) ⟨877844, by rfl⟩ : syracuseStep 1170459 = 1755689) B1755689
theorem B1170751 : Blo 1170402 1170751 := bstep (se 1 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 1170751 = 1756127) B1756127
theorem B3751343 : Blo 1170402 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B7511525 : Blo 1170402 7511525 := bstep (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) B1408411
theorem B1171047 : Blo 1170402 1171047 := bstep (se 1 (by rfl) ⟨878285, by rfl⟩ : syracuseStep 1171047 = 1756571) B1756571
theorem B7118603 : Blo 1170402 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B1171291 : Blo 1170402 1171291 := bstep (se 1 (by rfl) ⟨878468, by rfl⟩ : syracuseStep 1171291 = 1756937) B1756937
theorem B1171327 : Blo 1170402 1171327 := bstep (se 1 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 1171327 = 1756991) B1756991
theorem B8445829 : Blo 1170402 8445829 := bstep (se 4 (by rfl) ⟨791796, by rfl⟩ : syracuseStep 8445829 = 1583593) B1583593
theorem B3612647 : Blo 1170402 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B1171483 : Blo 1170402 1171483 := bstep (se 1 (by rfl) ⟨878612, by rfl⟩ : syracuseStep 1171483 = 1757225) B1757225
theorem B1171611 : Blo 1170402 1171611 := bstep (se 1 (by rfl) ⟨878708, by rfl⟩ : syracuseStep 1171611 = 1757417) B1757417
theorem B10150049 : Blo 1170402 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B1171739 : Blo 1170402 1171739 := bstep (se 1 (by rfl) ⟨878804, by rfl⟩ : syracuseStep 1171739 = 1757609) B1757609
theorem B1171943 : Blo 1170402 1171943 := bstep (se 1 (by rfl) ⟨878957, by rfl⟩ : syracuseStep 1171943 = 1757915) B1757915
theorem B1172207 : Blo 1170402 1172207 := bstep (se 1 (by rfl) ⟨879155, by rfl⟩ : syracuseStep 1172207 = 1758311) B1758311
theorem B1172251 : Blo 1170402 1172251 := bstep (se 1 (by rfl) ⟨879188, by rfl⟩ : syracuseStep 1172251 = 1758377) B1758377
theorem B22512431 : Blo 1170402 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B1483591 : Blo 1170402 1483591 := bstep (se 1 (by rfl) ⟨1112693, by rfl⟩ : syracuseStep 1483591 = 2225387) B2225387
theorem B1172295 : Blo 1170402 1172295 := bstep (se 1 (by rfl) ⟨879221, by rfl⟩ : syracuseStep 1172295 = 1758443) B1758443
theorem B1877023 : Blo 1170402 1877023 := bstep (se 1 (by rfl) ⟨1407767, by rfl⟩ : syracuseStep 1877023 = 2815535) B2815535
theorem B5629031 : Blo 1170402 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B4007087 : Blo 1170402 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B104080583 : Blo 1170402 104080583 := bstep (se 1 (by rfl) ⟨78060437, by rfl⟩ : syracuseStep 104080583 = 156120875) B156120875
theorem B50619755 : Blo 1170402 50619755 := bstep (se 1 (by rfl) ⟨37964816, by rfl⟩ : syracuseStep 50619755 = 75929633) B75929633
theorem B8439223 : Blo 1170402 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B200198191 : Blo 1170402 200198191 := bstep (se 1 (by rfl) ⟨150148643, by rfl⟩ : syracuseStep 200198191 = 300297287) B300297287
theorem B2500895 : Blo 1170402 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B5007683 : Blo 1170402 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B2222569 : Blo 1170402 2222569 := bstep (se 2 (by rfl) ⟨833463, by rfl⟩ : syracuseStep 2222569 = 1666927) B1666927
theorem B4745735 : Blo 1170402 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B5933735 : Blo 1170402 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B3337271 : Blo 1170402 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B12840059 : Blo 1170402 12840059 := bstep (se 1 (by rfl) ⟨9630044, by rfl⟩ : syracuseStep 12840059 = 19260089) B19260089
theorem B1756367 : Blo 1170402 1756367 := bstep (se 1 (by rfl) ⟨1317275, by rfl⟩ : syracuseStep 1756367 = 2634551) B2634551
theorem B1756391 : Blo 1170402 1756391 := bstep (se 1 (by rfl) ⟨1317293, by rfl⟩ : syracuseStep 1756391 = 2634587) B2634587
theorem B3952043 : Blo 1170402 3952043 := bstep (se 1 (by rfl) ⟨2964032, by rfl⟩ : syracuseStep 3952043 = 5928065) B5928065
theorem B11251295 : Blo 1170402 11251295 := bstep (se 1 (by rfl) ⟨8438471, by rfl⟩ : syracuseStep 11251295 = 16876943) B16876943
theorem B2633435 : Blo 1170402 2633435 := bstep (se 1 (by rfl) ⟨1975076, by rfl⟩ : syracuseStep 2633435 = 3950153) B3950153
theorem B2633705 : Blo 1170402 2633705 := bstep (se 2 (by rfl) ⟨987639, by rfl⟩ : syracuseStep 2633705 = 1975279) B1975279
theorem B2633759 : Blo 1170402 2633759 := bstep (se 1 (by rfl) ⟨1975319, by rfl⟩ : syracuseStep 2633759 = 3950639) B3950639
theorem B1757255 : Blo 1170402 1757255 := bstep (se 1 (by rfl) ⟨1317941, by rfl⟩ : syracuseStep 1757255 = 2635883) B2635883
theorem B2707663 : Blo 1170402 2707663 := bstep (se 1 (by rfl) ⟨2030747, by rfl⟩ : syracuseStep 2707663 = 4061495) B4061495
theorem B15004187 : Blo 1170402 15004187 := bstep (se 1 (by rfl) ⟨11253140, by rfl⟩ : syracuseStep 15004187 = 22506281) B22506281
theorem B2634731 : Blo 1170402 2634731 := bstep (se 1 (by rfl) ⟨1976048, by rfl⟩ : syracuseStep 2634731 = 3952097) B3952097
theorem B2634911 : Blo 1170402 2634911 := bstep (se 1 (by rfl) ⟨1976183, by rfl⟩ : syracuseStep 2634911 = 3952367) B3952367
theorem B11261105 : Blo 1170402 11261105 := bstep (se 2 (by rfl) ⟨4222914, by rfl⟩ : syracuseStep 11261105 = 8445829) B8445829
theorem B6337721 : Blo 1170402 6337721 := bstep (se 2 (by rfl) ⟨2376645, by rfl⟩ : syracuseStep 6337721 = 4753291) B4753291
theorem B2635055 : Blo 1170402 2635055 := bstep (se 1 (by rfl) ⟨1976291, by rfl⟩ : syracuseStep 2635055 = 3952583) B3952583
theorem B1250687 : Blo 1170402 1250687 := bstep (se 1 (by rfl) ⟨938015, by rfl⟩ : syracuseStep 1250687 = 1876031) B1876031
theorem B2962939 : Blo 1170402 2962939 := bstep (se 1 (by rfl) ⟨2222204, by rfl⟩ : syracuseStep 2962939 = 4444409) B4444409
theorem B2635343 : Blo 1170402 2635343 := bstep (se 1 (by rfl) ⟨1976507, by rfl⟩ : syracuseStep 2635343 = 3953015) B3953015
theorem B2963081 : Blo 1170402 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B11253755 : Blo 1170402 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B72136889 : Blo 1170402 72136889 := bstep (se 2 (by rfl) ⟨27051333, by rfl⟩ : syracuseStep 72136889 = 54102667) B54102667
theorem B2636063 : Blo 1170402 2636063 := bstep (se 1 (by rfl) ⟨1977047, by rfl⟩ : syracuseStep 2636063 = 3954095) B3954095
theorem B3750227 : Blo 1170402 3750227 := bstep (se 1 (by rfl) ⟨2812670, by rfl⟩ : syracuseStep 3750227 = 5625341) B5625341
theorem B2636153 : Blo 1170402 2636153 := bstep (se 2 (by rfl) ⟨988557, by rfl⟩ : syracuseStep 2636153 = 1977115) B1977115
theorem B10009079 : Blo 1170402 10009079 := bstep (se 1 (by rfl) ⟨7506809, by rfl⟩ : syracuseStep 10009079 = 15013619) B15013619
theorem B2636279 : Blo 1170402 2636279 := bstep (se 1 (by rfl) ⟨1977209, by rfl⟩ : syracuseStep 2636279 = 3954419) B3954419
theorem B2636315 : Blo 1170402 2636315 := bstep (se 1 (by rfl) ⟨1977236, by rfl⟩ : syracuseStep 2636315 = 3954473) B3954473
theorem B1317487 : Blo 1170402 1317487 := bstep (se 1 (by rfl) ⟨988115, by rfl⟩ : syracuseStep 1317487 = 1976231) B1976231
theorem B4291375 : Blo 1170402 4291375 := bstep (se 1 (by rfl) ⟨3218531, by rfl⟩ : syracuseStep 4291375 = 6437063) B6437063
theorem B2636783 : Blo 1170402 2636783 := bstep (se 1 (by rfl) ⟨1977587, by rfl⟩ : syracuseStep 2636783 = 3955175) B3955175
theorem B1170591 : Blo 1170402 1170591 := bstep (se 1 (by rfl) ⟨877943, by rfl⟩ : syracuseStep 1170591 = 1755887) B1755887
theorem B22527193 : Blo 1170402 22527193 := bstep (se 2 (by rfl) ⟨8447697, by rfl⟩ : syracuseStep 22527193 = 16895395) B16895395
theorem B1170671 : Blo 1170402 1170671 := bstep (se 1 (by rfl) ⟨878003, by rfl⟩ : syracuseStep 1170671 = 1756007) B1756007
theorem B3956039 : Blo 1170402 3956039 := bstep (se 1 (by rfl) ⟨2967029, by rfl⟩ : syracuseStep 3956039 = 5934059) B5934059
theorem B10689869 : Blo 1170402 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B1170843 : Blo 1170402 1170843 := bstep (se 1 (by rfl) ⟨878132, by rfl⟩ : syracuseStep 1170843 = 1756265) B1756265
theorem B1170847 : Blo 1170402 1170847 := bstep (se 1 (by rfl) ⟨878135, by rfl⟩ : syracuseStep 1170847 = 1756271) B1756271
theorem B13524569 : Blo 1170402 13524569 := bstep (se 2 (by rfl) ⟨5071713, by rfl⟩ : syracuseStep 13524569 = 10143427) B10143427
theorem B2637449 : Blo 1170402 2637449 := bstep (se 2 (by rfl) ⟨989043, by rfl⟩ : syracuseStep 2637449 = 1978087) B1978087
theorem B14245571 : Blo 1170402 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B9633725 : Blo 1170402 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B2965481 : Blo 1170402 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B1171451 : Blo 1170402 1171451 := bstep (se 1 (by rfl) ⟨878588, by rfl⟩ : syracuseStep 1171451 = 1757177) B1757177
theorem B1171503 : Blo 1170402 1171503 := bstep (se 1 (by rfl) ⟨878627, by rfl⟩ : syracuseStep 1171503 = 1757255) B1757255
theorem B6766699 : Blo 1170402 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B10010789 : Blo 1170402 10010789 := bstep (se 4 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 10010789 = 1877023) B1877023
theorem B10002791 : Blo 1170402 10002791 := bstep (se 1 (by rfl) ⟨7502093, by rfl⟩ : syracuseStep 10002791 = 15004187) B15004187
theorem B16900589 : Blo 1170402 16900589 := bstep (se 3 (by rfl) ⟨3168860, by rfl⟩ : syracuseStep 16900589 = 6337721) B6337721
theorem B15008287 : Blo 1170402 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B3752687 : Blo 1170402 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B6669053 : Blo 1170402 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B2671391 : Blo 1170402 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B13353821 : Blo 1170402 13353821 := bstep (se 3 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 13353821 = 5007683) B5007683
theorem B3335165 : Blo 1170402 3335165 := bstep (se 3 (by rfl) ⟨625343, by rfl⟩ : syracuseStep 3335165 = 1250687) B1250687
theorem B1975387 : Blo 1170402 1975387 := bstep (se 1 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 1975387 = 2963081) B2963081
theorem B2500151 : Blo 1170402 2500151 := bstep (se 1 (by rfl) ⟨1875113, by rfl⟩ : syracuseStep 2500151 = 3750227) B3750227
theorem B3163823 : Blo 1170402 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B37988189 : Blo 1170402 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B3950585 : Blo 1170402 3950585 := bstep (se 2 (by rfl) ⟨1481469, by rfl⟩ : syracuseStep 3950585 = 2962939) B2962939
theorem B1755623 : Blo 1170402 1755623 := bstep (se 1 (by rfl) ⟨1316717, by rfl⟩ : syracuseStep 1755623 = 2633435) B2633435
theorem B1755803 : Blo 1170402 1755803 := bstep (se 1 (by rfl) ⟨1316852, by rfl⟩ : syracuseStep 1755803 = 2633705) B2633705
theorem B1976987 : Blo 1170402 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B30010013 : Blo 1170402 30010013 := bstep (se 3 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 30010013 = 11253755) B11253755
theorem B1755839 : Blo 1170402 1755839 := bstep (se 1 (by rfl) ⟨1316879, by rfl⟩ : syracuseStep 1755839 = 2633759) B2633759
theorem B266930921 : Blo 1170402 266930921 := bstep (se 2 (by rfl) ⟨100099095, by rfl⟩ : syracuseStep 266930921 = 200198191) B200198191
theorem B277548221 : Blo 1170402 277548221 := bstep (se 3 (by rfl) ⟨52040291, by rfl⟩ : syracuseStep 277548221 = 104080583) B104080583
theorem B1756487 : Blo 1170402 1756487 := bstep (se 1 (by rfl) ⟨1317365, by rfl⟩ : syracuseStep 1756487 = 2634731) B2634731
theorem B1756607 : Blo 1170402 1756607 := bstep (se 1 (by rfl) ⟨1317455, by rfl⟩ : syracuseStep 1756607 = 2634911) B2634911
theorem B7507403 : Blo 1170402 7507403 := bstep (se 1 (by rfl) ⟨5630552, by rfl⟩ : syracuseStep 7507403 = 11261105) B11261105
theorem B1756649 : Blo 1170402 1756649 := bstep (se 2 (by rfl) ⟨658743, by rfl⟩ : syracuseStep 1756649 = 1317487) B1317487
theorem B1756703 : Blo 1170402 1756703 := bstep (se 1 (by rfl) ⟨1317527, by rfl⟩ : syracuseStep 1756703 = 2635055) B2635055
theorem B33746503 : Blo 1170402 33746503 := bstep (se 1 (by rfl) ⟨25309877, by rfl⟩ : syracuseStep 33746503 = 50619755) B50619755
theorem B1756895 : Blo 1170402 1756895 := bstep (se 1 (by rfl) ⟨1317671, by rfl⟩ : syracuseStep 1756895 = 2635343) B2635343
theorem B5721833 : Blo 1170402 5721833 := bstep (se 2 (by rfl) ⟨2145687, by rfl⟩ : syracuseStep 5721833 = 4291375) B4291375
theorem B1978121 : Blo 1170402 1978121 := bstep (se 2 (by rfl) ⟨741795, by rfl⟩ : syracuseStep 1978121 = 1483591) B1483591
theorem B48091259 : Blo 1170402 48091259 := bstep (se 1 (by rfl) ⟨36068444, by rfl⟩ : syracuseStep 48091259 = 72136889) B72136889
theorem B1757375 : Blo 1170402 1757375 := bstep (se 1 (by rfl) ⟨1318031, by rfl⟩ : syracuseStep 1757375 = 2636063) B2636063
theorem B1757435 : Blo 1170402 1757435 := bstep (se 1 (by rfl) ⟨1318076, by rfl⟩ : syracuseStep 1757435 = 2636153) B2636153
theorem B30036257 : Blo 1170402 30036257 := bstep (se 2 (by rfl) ⟨11263596, by rfl⟩ : syracuseStep 30036257 = 22527193) B22527193
theorem B6672719 : Blo 1170402 6672719 := bstep (se 1 (by rfl) ⟨5004539, by rfl⟩ : syracuseStep 6672719 = 10009079) B10009079
theorem B1757519 : Blo 1170402 1757519 := bstep (se 1 (by rfl) ⟨1318139, by rfl⟩ : syracuseStep 1757519 = 2636279) B2636279
theorem B1757543 : Blo 1170402 1757543 := bstep (se 1 (by rfl) ⟨1318157, by rfl⟩ : syracuseStep 1757543 = 2636315) B2636315
theorem B11252297 : Blo 1170402 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B1757855 : Blo 1170402 1757855 := bstep (se 1 (by rfl) ⟨1318391, by rfl⟩ : syracuseStep 1757855 = 2636783) B2636783
theorem B2224847 : Blo 1170402 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B2634695 : Blo 1170402 2634695 := bstep (se 1 (by rfl) ⟨1976021, by rfl⟩ : syracuseStep 2634695 = 3952043) B3952043
theorem B9016379 : Blo 1170402 9016379 := bstep (se 1 (by rfl) ⟨6762284, by rfl⟩ : syracuseStep 9016379 = 13524569) B13524569
theorem B7500863 : Blo 1170402 7500863 := bstep (se 1 (by rfl) ⟨5625647, by rfl⟩ : syracuseStep 7500863 = 11251295) B11251295
theorem B1758299 : Blo 1170402 1758299 := bstep (se 1 (by rfl) ⟨1318724, by rfl⟩ : syracuseStep 1758299 = 2637449) B2637449
theorem B3610217 : Blo 1170402 3610217 := bstep (se 2 (by rfl) ⟨1353831, by rfl⟩ : syracuseStep 3610217 = 2707663) B2707663
theorem B2963425 : Blo 1170402 2963425 := bstep (se 2 (by rfl) ⟨1111284, by rfl⟩ : syracuseStep 2963425 = 2222569) B2222569
theorem B3955823 : Blo 1170402 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B8560039 : Blo 1170402 8560039 := bstep (se 1 (by rfl) ⟨6420029, by rfl⟩ : syracuseStep 8560039 = 12840059) B12840059
theorem B1170911 : Blo 1170402 1170911 := bstep (se 1 (by rfl) ⟨878183, by rfl⟩ : syracuseStep 1170911 = 1756367) B1756367
theorem B1170927 : Blo 1170402 1170927 := bstep (se 1 (by rfl) ⟨878195, by rfl⟩ : syracuseStep 1170927 = 1756391) B1756391
theorem B2637359 : Blo 1170402 2637359 := bstep (se 1 (by rfl) ⟨1978019, by rfl⟩ : syracuseStep 2637359 = 3956039) B3956039
theorem B7126579 : Blo 1170402 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B6422483 : Blo 1170402 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B1171583 : Blo 1170402 1171583 := bstep (se 1 (by rfl) ⟨878687, by rfl⟩ : syracuseStep 1171583 = 1757375) B1757375
theorem B1171623 : Blo 1170402 1171623 := bstep (se 1 (by rfl) ⟨878717, by rfl⟩ : syracuseStep 1171623 = 1757435) B1757435
theorem B4448479 : Blo 1170402 4448479 := bstep (se 1 (by rfl) ⟨3336359, by rfl⟩ : syracuseStep 4448479 = 6672719) B6672719
theorem B1171679 : Blo 1170402 1171679 := bstep (se 1 (by rfl) ⟨878759, by rfl⟩ : syracuseStep 1171679 = 1757519) B1757519
theorem B6668527 : Blo 1170402 6668527 := bstep (se 1 (by rfl) ⟨5001395, by rfl⟩ : syracuseStep 6668527 = 10002791) B10002791
theorem B1171695 : Blo 1170402 1171695 := bstep (se 1 (by rfl) ⟨878771, by rfl⟩ : syracuseStep 1171695 = 1757543) B1757543
theorem B1171903 : Blo 1170402 1171903 := bstep (se 1 (by rfl) ⟨878927, by rfl⟩ : syracuseStep 1171903 = 1757855) B1757855
theorem B1172199 : Blo 1170402 1172199 := bstep (se 1 (by rfl) ⟨879149, by rfl⟩ : syracuseStep 1172199 = 1758299) B1758299
theorem B9627245 : Blo 1170402 9627245 := bstep (se 3 (by rfl) ⟨1805108, by rfl⟩ : syracuseStep 9627245 = 3610217) B3610217
theorem B20006675 : Blo 1170402 20006675 := bstep (se 1 (by rfl) ⟨15005006, by rfl⟩ : syracuseStep 20006675 = 30010013) B30010013
theorem B5932925 : Blo 1170402 5932925 := bstep (se 3 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 5932925 = 2224847) B2224847
theorem B11413385 : Blo 1170402 11413385 := bstep (se 2 (by rfl) ⟨4280019, by rfl⟩ : syracuseStep 11413385 = 8560039) B8560039
theorem B3951233 : Blo 1170402 3951233 := bstep (se 2 (by rfl) ⟨1481712, by rfl⟩ : syracuseStep 3951233 = 2963425) B2963425
theorem B9022265 : Blo 1170402 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B20024171 : Blo 1170402 20024171 := bstep (se 1 (by rfl) ⟨15018128, by rfl⟩ : syracuseStep 20024171 = 30036257) B30036257
theorem B11267059 : Blo 1170402 11267059 := bstep (se 1 (by rfl) ⟨8450294, by rfl⟩ : syracuseStep 11267059 = 16900589) B16900589
theorem B1756463 : Blo 1170402 1756463 := bstep (se 1 (by rfl) ⟨1317347, by rfl⟩ : syracuseStep 1756463 = 2634695) B2634695
theorem B2223443 : Blo 1170402 2223443 := bstep (se 1 (by rfl) ⟨1667582, by rfl⟩ : syracuseStep 2223443 = 3335165) B3335165
theorem B2109215 : Blo 1170402 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B25325459 : Blo 1170402 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B2633723 : Blo 1170402 2633723 := bstep (se 1 (by rfl) ⟨1975292, by rfl⟩ : syracuseStep 2633723 = 3950585) B3950585
theorem B2633849 : Blo 1170402 2633849 := bstep (se 2 (by rfl) ⟨987693, by rfl⟩ : syracuseStep 2633849 = 1975387) B1975387
theorem B711815789 : Blo 1170402 711815789 := bstep (se 3 (by rfl) ⟨133465460, by rfl⟩ : syracuseStep 711815789 = 266930921) B266930921
theorem B10007165 : Blo 1170402 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B7123709 : Blo 1170402 7123709 := bstep (se 3 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 7123709 = 2671391) B2671391
theorem B44995337 : Blo 1170402 44995337 := bstep (se 2 (by rfl) ⟨16873251, by rfl⟩ : syracuseStep 44995337 = 33746503) B33746503
theorem B1758239 : Blo 1170402 1758239 := bstep (se 1 (by rfl) ⟨1318679, by rfl⟩ : syracuseStep 1758239 = 2637359) B2637359
theorem B3814555 : Blo 1170402 3814555 := bstep (se 1 (by rfl) ⟨2860916, by rfl⟩ : syracuseStep 3814555 = 5721833) B5721833
theorem B4281655 : Blo 1170402 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B6673859 : Blo 1170402 6673859 := bstep (se 1 (by rfl) ⟨5005394, by rfl⟩ : syracuseStep 6673859 = 10010789) B10010789
theorem B20002301 : Blo 1170402 20002301 := bstep (se 3 (by rfl) ⟨3750431, by rfl⟩ : syracuseStep 20002301 = 7500863) B7500863
theorem B128243357 : Blo 1170402 128243357 := bstep (se 3 (by rfl) ⟨24045629, by rfl⟩ : syracuseStep 128243357 = 48091259) B48091259
theorem B7501531 : Blo 1170402 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B740128589 : Blo 1170402 740128589 := bstep (se 3 (by rfl) ⟨138774110, by rfl⟩ : syracuseStep 740128589 = 277548221) B277548221
theorem B4446035 : Blo 1170402 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B8902547 : Blo 1170402 8902547 := bstep (se 1 (by rfl) ⟨6676910, by rfl⟩ : syracuseStep 8902547 = 13353821) B13353821
theorem B6010919 : Blo 1170402 6010919 := bstep (se 1 (by rfl) ⟨4508189, by rfl⟩ : syracuseStep 6010919 = 9016379) B9016379
theorem B20011049 : Blo 1170402 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B6667069 : Blo 1170402 6667069 := bstep (se 3 (by rfl) ⟨1250075, by rfl⟩ : syracuseStep 6667069 = 2500151) B2500151
theorem B1170415 : Blo 1170402 1170415 := bstep (se 1 (by rfl) ⟨877811, by rfl⟩ : syracuseStep 1170415 = 1755623) B1755623
theorem B1170535 : Blo 1170402 1170535 := bstep (se 1 (by rfl) ⟨877901, by rfl⟩ : syracuseStep 1170535 = 1755803) B1755803
theorem B1317991 : Blo 1170402 1317991 := bstep (se 1 (by rfl) ⟨988493, by rfl⟩ : syracuseStep 1317991 = 1976987) B1976987
theorem B1170559 : Blo 1170402 1170559 := bstep (se 1 (by rfl) ⟨877919, by rfl⟩ : syracuseStep 1170559 = 1755839) B1755839
theorem B9502105 : Blo 1170402 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B2637215 : Blo 1170402 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B1170991 : Blo 1170402 1170991 := bstep (se 1 (by rfl) ⟨878243, by rfl⟩ : syracuseStep 1170991 = 1756487) B1756487
theorem B1171071 : Blo 1170402 1171071 := bstep (se 1 (by rfl) ⟨878303, by rfl⟩ : syracuseStep 1171071 = 1756607) B1756607
theorem B5004935 : Blo 1170402 5004935 := bstep (se 1 (by rfl) ⟨3753701, by rfl⟩ : syracuseStep 5004935 = 7507403) B7507403
theorem B1171099 : Blo 1170402 1171099 := bstep (se 1 (by rfl) ⟨878324, by rfl⟩ : syracuseStep 1171099 = 1756649) B1756649
theorem B1171135 : Blo 1170402 1171135 := bstep (se 1 (by rfl) ⟨878351, by rfl⟩ : syracuseStep 1171135 = 1756703) B1756703
theorem B1171263 : Blo 1170402 1171263 := bstep (se 1 (by rfl) ⟨878447, by rfl⟩ : syracuseStep 1171263 = 1756895) B1756895
theorem B1318747 : Blo 1170402 1318747 := bstep (se 1 (by rfl) ⟨989060, by rfl⟩ : syracuseStep 1318747 = 1978121) B1978121
theorem B5931305 : Blo 1170402 5931305 := bstep (se 2 (by rfl) ⟨2224239, by rfl⟩ : syracuseStep 5931305 = 4448479) B4448479
theorem B1172159 : Blo 1170402 1172159 := bstep (se 1 (by rfl) ⟨879119, by rfl⟩ : syracuseStep 1172159 = 1758239) B1758239
theorem B4449239 : Blo 1170402 4449239 := bstep (se 1 (by rfl) ⟨3336929, by rfl⟩ : syracuseStep 4449239 = 6673859) B6673859
theorem B8889425 : Blo 1170402 8889425 := bstep (se 2 (by rfl) ⟨3333534, by rfl⟩ : syracuseStep 8889425 = 6667069) B6667069
theorem B13337783 : Blo 1170402 13337783 := bstep (se 1 (by rfl) ⟨10003337, by rfl⟩ : syracuseStep 13337783 = 20006675) B20006675
theorem B4007279 : Blo 1170402 4007279 := bstep (se 1 (by rfl) ⟨3005459, by rfl⟩ : syracuseStep 4007279 = 6010919) B6010919
theorem B6014843 : Blo 1170402 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B3336623 : Blo 1170402 3336623 := bstep (se 1 (by rfl) ⟨2502467, by rfl⟩ : syracuseStep 3336623 = 5004935) B5004935
theorem B1755815 : Blo 1170402 1755815 := bstep (se 1 (by rfl) ⟨1316861, by rfl⟩ : syracuseStep 1755815 = 2633723) B2633723
theorem B1755899 : Blo 1170402 1755899 := bstep (se 1 (by rfl) ⟨1316924, by rfl⟩ : syracuseStep 1755899 = 2633849) B2633849
theorem B8891369 : Blo 1170402 8891369 := bstep (se 2 (by rfl) ⟨3334263, by rfl⟩ : syracuseStep 8891369 = 6668527) B6668527
theorem B6671443 : Blo 1170402 6671443 := bstep (se 1 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 6671443 = 10007165) B10007165
theorem B6418163 : Blo 1170402 6418163 := bstep (se 1 (by rfl) ⟨4813622, by rfl⟩ : syracuseStep 6418163 = 9627245) B9627245
theorem B85495571 : Blo 1170402 85495571 := bstep (se 1 (by rfl) ⟨64121678, by rfl⟩ : syracuseStep 85495571 = 128243357) B128243357
theorem B5935031 : Blo 1170402 5935031 := bstep (se 1 (by rfl) ⟨4451273, by rfl⟩ : syracuseStep 5935031 = 8902547) B8902547
theorem B13340699 : Blo 1170402 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B1757321 : Blo 1170402 1757321 := bstep (se 2 (by rfl) ⟨658995, by rfl⟩ : syracuseStep 1757321 = 1317991) B1317991
theorem B2634155 : Blo 1170402 2634155 := bstep (se 1 (by rfl) ⟨1975616, by rfl⟩ : syracuseStep 2634155 = 3951233) B3951233
theorem B12669473 : Blo 1170402 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B13349447 : Blo 1170402 13349447 := bstep (se 1 (by rfl) ⟨10012085, by rfl⟩ : syracuseStep 13349447 = 20024171) B20024171
theorem B1758143 : Blo 1170402 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B1758329 : Blo 1170402 1758329 := bstep (se 2 (by rfl) ⟨659373, by rfl⟩ : syracuseStep 1758329 = 1318747) B1318747
theorem B1406143 : Blo 1170402 1406143 := bstep (se 1 (by rfl) ⟨1054607, by rfl⟩ : syracuseStep 1406143 = 2109215) B2109215
theorem B474543859 : Blo 1170402 474543859 := bstep (se 1 (by rfl) ⟨355907894, by rfl⟩ : syracuseStep 474543859 = 711815789) B711815789
theorem B4749139 : Blo 1170402 4749139 := bstep (se 1 (by rfl) ⟨3561854, by rfl⟩ : syracuseStep 4749139 = 7123709) B7123709
theorem B29996891 : Blo 1170402 29996891 := bstep (se 1 (by rfl) ⟨22497668, by rfl⟩ : syracuseStep 29996891 = 44995337) B44995337
theorem B13334867 : Blo 1170402 13334867 := bstep (se 1 (by rfl) ⟨10001150, by rfl⟩ : syracuseStep 13334867 = 20002301) B20002301
theorem B493419059 : Blo 1170402 493419059 := bstep (se 1 (by rfl) ⟨370064294, by rfl⟩ : syracuseStep 493419059 = 740128589) B740128589
theorem B2964023 : Blo 1170402 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B3955283 : Blo 1170402 3955283 := bstep (se 1 (by rfl) ⟨2966462, by rfl⟩ : syracuseStep 3955283 = 5932925) B5932925
theorem B7608923 : Blo 1170402 7608923 := bstep (se 1 (by rfl) ⟨5706692, by rfl⟩ : syracuseStep 7608923 = 11413385) B11413385
theorem B15022745 : Blo 1170402 15022745 := bstep (se 2 (by rfl) ⟨5633529, by rfl⟩ : syracuseStep 15022745 = 11267059) B11267059
theorem B5086073 : Blo 1170402 5086073 := bstep (se 2 (by rfl) ⟨1907277, by rfl⟩ : syracuseStep 5086073 = 3814555) B3814555
theorem B5708873 : Blo 1170402 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B1170975 : Blo 1170402 1170975 := bstep (se 1 (by rfl) ⟨878231, by rfl⟩ : syracuseStep 1170975 = 1756463) B1756463
theorem B1482295 : Blo 1170402 1482295 := bstep (se 1 (by rfl) ⟨1111721, by rfl⟩ : syracuseStep 1482295 = 2223443) B2223443
theorem B10002041 : Blo 1170402 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B16883639 : Blo 1170402 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B1171547 : Blo 1170402 1171547 := bstep (se 1 (by rfl) ⟨878660, by rfl⟩ : syracuseStep 1171547 = 1757321) B1757321
theorem B8446315 : Blo 1170402 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B1172095 : Blo 1170402 1172095 := bstep (se 1 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 1172095 = 1758143) B1758143
theorem B2966159 : Blo 1170402 2966159 := bstep (se 1 (by rfl) ⟨2224619, by rfl⟩ : syracuseStep 2966159 = 4449239) B4449239
theorem B1172219 : Blo 1170402 1172219 := bstep (se 1 (by rfl) ⟨879164, by rfl⟩ : syracuseStep 1172219 = 1758329) B1758329
theorem B19997927 : Blo 1170402 19997927 := bstep (se 1 (by rfl) ⟨14998445, by rfl⟩ : syracuseStep 19997927 = 29996891) B29996891
theorem B8889911 : Blo 1170402 8889911 := bstep (se 1 (by rfl) ⟨6667433, by rfl⟩ : syracuseStep 8889911 = 13334867) B13334867
theorem B1976015 : Blo 1170402 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B5072615 : Blo 1170402 5072615 := bstep (se 1 (by rfl) ⟨3804461, by rfl⟩ : syracuseStep 5072615 = 7608923) B7608923
theorem B17115101 : Blo 1170402 17115101 := bstep (se 3 (by rfl) ⟨3209081, by rfl⟩ : syracuseStep 17115101 = 6418163) B6418163
theorem B1976393 : Blo 1170402 1976393 := bstep (se 2 (by rfl) ⟨741147, by rfl⟩ : syracuseStep 1976393 = 1482295) B1482295
theorem B1756103 : Blo 1170402 1756103 := bstep (se 1 (by rfl) ⟨1317077, by rfl⟩ : syracuseStep 1756103 = 2634155) B2634155
theorem B8899631 : Blo 1170402 8899631 := bstep (se 1 (by rfl) ⟨6674723, by rfl⟩ : syracuseStep 8899631 = 13349447) B13349447
theorem B5926283 : Blo 1170402 5926283 := bstep (se 1 (by rfl) ⟨4444712, by rfl⟩ : syracuseStep 5926283 = 8889425) B8889425
theorem B8891855 : Blo 1170402 8891855 := bstep (se 1 (by rfl) ⟨6668891, by rfl⟩ : syracuseStep 8891855 = 13337783) B13337783
theorem B10686077 : Blo 1170402 10686077 := bstep (se 3 (by rfl) ⟨2003639, by rfl⟩ : syracuseStep 10686077 = 4007279) B4007279
theorem B7499429 : Blo 1170402 7499429 := bstep (se 4 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 7499429 = 1406143) B1406143
theorem B4009895 : Blo 1170402 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B2224415 : Blo 1170402 2224415 := bstep (se 1 (by rfl) ⟨1668311, by rfl⟩ : syracuseStep 2224415 = 3336623) B3336623
theorem B328946039 : Blo 1170402 328946039 := bstep (se 1 (by rfl) ⟨246709529, by rfl⟩ : syracuseStep 328946039 = 493419059) B493419059
theorem B10015163 : Blo 1170402 10015163 := bstep (se 1 (by rfl) ⟨7511372, by rfl⟩ : syracuseStep 10015163 = 15022745) B15022745
theorem B5927579 : Blo 1170402 5927579 := bstep (se 1 (by rfl) ⟨4445684, by rfl⟩ : syracuseStep 5927579 = 8891369) B8891369
theorem B3805915 : Blo 1170402 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B13562861 : Blo 1170402 13562861 := bstep (se 3 (by rfl) ⟨2543036, by rfl⟩ : syracuseStep 13562861 = 5086073) B5086073
theorem B56997047 : Blo 1170402 56997047 := bstep (se 1 (by rfl) ⟨42747785, by rfl⟩ : syracuseStep 56997047 = 85495571) B85495571
theorem B8893799 : Blo 1170402 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B3954203 : Blo 1170402 3954203 := bstep (se 1 (by rfl) ⟨2965652, by rfl⟩ : syracuseStep 3954203 = 5931305) B5931305
theorem B8895257 : Blo 1170402 8895257 := bstep (se 2 (by rfl) ⟨3335721, by rfl⟩ : syracuseStep 8895257 = 6671443) B6671443
theorem B2636855 : Blo 1170402 2636855 := bstep (se 1 (by rfl) ⟨1977641, by rfl⟩ : syracuseStep 2636855 = 3955283) B3955283
theorem B1170543 : Blo 1170402 1170543 := bstep (se 1 (by rfl) ⟨877907, by rfl⟩ : syracuseStep 1170543 = 1755815) B1755815
theorem B1170599 : Blo 1170402 1170599 := bstep (se 1 (by rfl) ⟨877949, by rfl⟩ : syracuseStep 1170599 = 1755899) B1755899
theorem B632725145 : Blo 1170402 632725145 := bstep (se 2 (by rfl) ⟨237271929, by rfl⟩ : syracuseStep 632725145 = 474543859) B474543859
theorem B6668027 : Blo 1170402 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B6332185 : Blo 1170402 6332185 := bstep (se 2 (by rfl) ⟨2374569, by rfl⟩ : syracuseStep 6332185 = 4749139) B4749139
theorem B11255759 : Blo 1170402 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B3956687 : Blo 1170402 3956687 := bstep (se 1 (by rfl) ⟨2967515, by rfl⟩ : syracuseStep 3956687 = 5935031) B5935031
theorem B1482943 : Blo 1170402 1482943 := bstep (se 1 (by rfl) ⟨1112207, by rfl⟩ : syracuseStep 1482943 = 2224415) B2224415
theorem B6676775 : Blo 1170402 6676775 := bstep (se 1 (by rfl) ⟨5007581, by rfl⟩ : syracuseStep 6676775 = 10015163) B10015163
theorem B5933087 : Blo 1170402 5933087 := bstep (se 1 (by rfl) ⟨4449815, by rfl⟩ : syracuseStep 5933087 = 8899631) B8899631
theorem B3950855 : Blo 1170402 3950855 := bstep (se 1 (by rfl) ⟨2963141, by rfl⟩ : syracuseStep 3950855 = 5926283) B5926283
theorem B421816763 : Blo 1170402 421816763 := bstep (se 1 (by rfl) ⟨316362572, by rfl⟩ : syracuseStep 421816763 = 632725145) B632725145
theorem B4999619 : Blo 1170402 4999619 := bstep (se 1 (by rfl) ⟨3749714, by rfl⟩ : syracuseStep 4999619 = 7499429) B7499429
theorem B2673263 : Blo 1170402 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B1977439 : Blo 1170402 1977439 := bstep (se 1 (by rfl) ⟨1483079, by rfl⟩ : syracuseStep 1977439 = 2966159) B2966159
theorem B3951719 : Blo 1170402 3951719 := bstep (se 1 (by rfl) ⟨2963789, by rfl⟩ : syracuseStep 3951719 = 5927579) B5927579
theorem B13331951 : Blo 1170402 13331951 := bstep (se 1 (by rfl) ⟨9998963, by rfl⟩ : syracuseStep 13331951 = 19997927) B19997927
theorem B5074553 : Blo 1170402 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B5926607 : Blo 1170402 5926607 := bstep (se 1 (by rfl) ⟨4444955, by rfl⟩ : syracuseStep 5926607 = 8889911) B8889911
theorem B33771653 : Blo 1170402 33771653 := bstep (se 4 (by rfl) ⟨3166092, by rfl⟩ : syracuseStep 33771653 = 6332185) B6332185
theorem B1757903 : Blo 1170402 1757903 := bstep (se 1 (by rfl) ⟨1318427, by rfl⟩ : syracuseStep 1757903 = 2636855) B2636855
theorem B5927903 : Blo 1170402 5927903 := bstep (se 1 (by rfl) ⟨4445927, by rfl⟩ : syracuseStep 5927903 = 8891855) B8891855
theorem B7124051 : Blo 1170402 7124051 := bstep (se 1 (by rfl) ⟨5343038, by rfl⟩ : syracuseStep 7124051 = 10686077) B10686077
theorem B4445351 : Blo 1170402 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B219297359 : Blo 1170402 219297359 := bstep (se 1 (by rfl) ⟨164473019, by rfl⟩ : syracuseStep 219297359 = 328946039) B328946039
theorem B11261753 : Blo 1170402 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B151992125 : Blo 1170402 151992125 := bstep (se 3 (by rfl) ⟨28498523, by rfl⟩ : syracuseStep 151992125 = 56997047) B56997047
theorem B5929199 : Blo 1170402 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B2636135 : Blo 1170402 2636135 := bstep (se 1 (by rfl) ⟨1977101, by rfl⟩ : syracuseStep 2636135 = 3954203) B3954203
theorem B1317343 : Blo 1170402 1317343 := bstep (se 1 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 1317343 = 1976015) B1976015
theorem B3381743 : Blo 1170402 3381743 := bstep (se 1 (by rfl) ⟨2536307, by rfl⟩ : syracuseStep 3381743 = 5072615) B5072615
theorem B11410067 : Blo 1170402 11410067 := bstep (se 1 (by rfl) ⟨8557550, by rfl⟩ : syracuseStep 11410067 = 17115101) B17115101
theorem B1317595 : Blo 1170402 1317595 := bstep (se 1 (by rfl) ⟨988196, by rfl⟩ : syracuseStep 1317595 = 1976393) B1976393
theorem B5930171 : Blo 1170402 5930171 := bstep (se 1 (by rfl) ⟨4447628, by rfl⟩ : syracuseStep 5930171 = 8895257) B8895257
theorem B1170735 : Blo 1170402 1170735 := bstep (se 1 (by rfl) ⟨878051, by rfl⟩ : syracuseStep 1170735 = 1756103) B1756103
theorem B36167629 : Blo 1170402 36167629 := bstep (se 3 (by rfl) ⟨6781430, by rfl⟩ : syracuseStep 36167629 = 13562861) B13562861
theorem B7503839 : Blo 1170402 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B2637791 : Blo 1170402 2637791 := bstep (se 1 (by rfl) ⟨1978343, by rfl⟩ : syracuseStep 2637791 = 3956687) B3956687
theorem B1171935 : Blo 1170402 1171935 := bstep (se 1 (by rfl) ⟨878951, by rfl⟩ : syracuseStep 1171935 = 1757903) B1757903
theorem B101328083 : Blo 1170402 101328083 := bstep (se 1 (by rfl) ⟨75996062, by rfl⟩ : syracuseStep 101328083 = 151992125) B151992125
theorem B2254495 : Blo 1170402 2254495 := bstep (se 1 (by rfl) ⟨1690871, by rfl⟩ : syracuseStep 2254495 = 3381743) B3381743
theorem B3951071 : Blo 1170402 3951071 := bstep (se 1 (by rfl) ⟨2963303, by rfl⟩ : syracuseStep 3951071 = 5926607) B5926607
theorem B22514435 : Blo 1170402 22514435 := bstep (se 1 (by rfl) ⟨16885826, by rfl⟩ : syracuseStep 22514435 = 33771653) B33771653
theorem B4451183 : Blo 1170402 4451183 := bstep (se 1 (by rfl) ⟨3338387, by rfl⟩ : syracuseStep 4451183 = 6676775) B6676775
theorem B1977257 : Blo 1170402 1977257 := bstep (se 2 (by rfl) ⟨741471, by rfl⟩ : syracuseStep 1977257 = 1482943) B1482943
theorem B1756457 : Blo 1170402 1756457 := bstep (se 2 (by rfl) ⟨658671, by rfl⟩ : syracuseStep 1756457 = 1317343) B1317343
theorem B3951935 : Blo 1170402 3951935 := bstep (se 1 (by rfl) ⟨2963951, by rfl⟩ : syracuseStep 3951935 = 5927903) B5927903
theorem B1756793 : Blo 1170402 1756793 := bstep (se 2 (by rfl) ⟨658797, by rfl⟩ : syracuseStep 1756793 = 1317595) B1317595
theorem B146198239 : Blo 1170402 146198239 := bstep (se 1 (by rfl) ⟨109648679, by rfl⟩ : syracuseStep 146198239 = 219297359) B219297359
theorem B7507835 : Blo 1170402 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B3952799 : Blo 1170402 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B2633903 : Blo 1170402 2633903 := bstep (se 1 (by rfl) ⟨1975427, by rfl⟩ : syracuseStep 2633903 = 3950855) B3950855
theorem B1757423 : Blo 1170402 1757423 := bstep (se 1 (by rfl) ⟨1318067, by rfl⟩ : syracuseStep 1757423 = 2636135) B2636135
theorem B281211175 : Blo 1170402 281211175 := bstep (se 1 (by rfl) ⟨210908381, by rfl⟩ : syracuseStep 281211175 = 421816763) B421816763
theorem B1782175 : Blo 1170402 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B7606711 : Blo 1170402 7606711 := bstep (se 1 (by rfl) ⟨5705033, by rfl⟩ : syracuseStep 7606711 = 11410067) B11410067
theorem B2634479 : Blo 1170402 2634479 := bstep (se 1 (by rfl) ⟨1975859, by rfl⟩ : syracuseStep 2634479 = 3951719) B3951719
theorem B3953447 : Blo 1170402 3953447 := bstep (se 1 (by rfl) ⟨2965085, by rfl⟩ : syracuseStep 3953447 = 5930171) B5930171
theorem B48223505 : Blo 1170402 48223505 := bstep (se 2 (by rfl) ⟨18083814, by rfl⟩ : syracuseStep 48223505 = 36167629) B36167629
theorem B5002559 : Blo 1170402 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B1758527 : Blo 1170402 1758527 := bstep (se 1 (by rfl) ⟨1318895, by rfl⟩ : syracuseStep 1758527 = 2637791) B2637791
theorem B4749367 : Blo 1170402 4749367 := bstep (se 1 (by rfl) ⟨3562025, by rfl⟩ : syracuseStep 4749367 = 7124051) B7124051
theorem B2963567 : Blo 1170402 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B3955391 : Blo 1170402 3955391 := bstep (se 1 (by rfl) ⟨2966543, by rfl⟩ : syracuseStep 3955391 = 5933087) B5933087
theorem B2636585 : Blo 1170402 2636585 := bstep (se 2 (by rfl) ⟨988719, by rfl⟩ : syracuseStep 2636585 = 1977439) B1977439
theorem B3333079 : Blo 1170402 3333079 := bstep (se 1 (by rfl) ⟨2499809, by rfl⟩ : syracuseStep 3333079 = 4999619) B4999619
theorem B8887967 : Blo 1170402 8887967 := bstep (se 1 (by rfl) ⟨6665975, by rfl⟩ : syracuseStep 8887967 = 13331951) B13331951
theorem B3383035 : Blo 1170402 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B6332489 : Blo 1170402 6332489 := bstep (se 2 (by rfl) ⟨2374683, by rfl⟩ : syracuseStep 6332489 = 4749367) B4749367
theorem B1171615 : Blo 1170402 1171615 := bstep (se 1 (by rfl) ⟨878711, by rfl⟩ : syracuseStep 1171615 = 1757423) B1757423
theorem B374948233 : Blo 1170402 374948233 := bstep (se 2 (by rfl) ⟨140605587, by rfl⟩ : syracuseStep 374948233 = 281211175) B281211175
theorem B2376233 : Blo 1170402 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B10142281 : Blo 1170402 10142281 := bstep (se 2 (by rfl) ⟨3803355, by rfl⟩ : syracuseStep 10142281 = 7606711) B7606711
theorem B67552055 : Blo 1170402 67552055 := bstep (se 1 (by rfl) ⟨50664041, by rfl⟩ : syracuseStep 67552055 = 101328083) B101328083
theorem B3335039 : Blo 1170402 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B1172351 : Blo 1170402 1172351 := bstep (se 1 (by rfl) ⟨879263, by rfl⟩ : syracuseStep 1172351 = 1758527) B1758527
theorem B779723941 : Blo 1170402 779723941 := bstep (se 4 (by rfl) ⟨73099119, by rfl⟩ : syracuseStep 779723941 = 146198239) B146198239
theorem B1975711 : Blo 1170402 1975711 := bstep (se 1 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 1975711 = 2963567) B2963567
theorem B15009623 : Blo 1170402 15009623 := bstep (se 1 (by rfl) ⟨11257217, by rfl⟩ : syracuseStep 15009623 = 22514435) B22514435
theorem B2967455 : Blo 1170402 2967455 := bstep (se 1 (by rfl) ⟨2225591, by rfl⟩ : syracuseStep 2967455 = 4451183) B4451183
theorem B5925311 : Blo 1170402 5925311 := bstep (se 1 (by rfl) ⟨4443983, by rfl⟩ : syracuseStep 5925311 = 8887967) B8887967
theorem B1755935 : Blo 1170402 1755935 := bstep (se 1 (by rfl) ⟨1316951, by rfl⟩ : syracuseStep 1755935 = 2633903) B2633903
theorem B1756319 : Blo 1170402 1756319 := bstep (se 1 (by rfl) ⟨1317239, by rfl⟩ : syracuseStep 1756319 = 2634479) B2634479
theorem B32149003 : Blo 1170402 32149003 := bstep (se 1 (by rfl) ⟨24111752, by rfl⟩ : syracuseStep 32149003 = 48223505) B48223505
theorem B4444105 : Blo 1170402 4444105 := bstep (se 2 (by rfl) ⟨1666539, by rfl⟩ : syracuseStep 4444105 = 3333079) B3333079
theorem B18042853 : Blo 1170402 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B2634047 : Blo 1170402 2634047 := bstep (se 1 (by rfl) ⟨1975535, by rfl⟩ : syracuseStep 2634047 = 3951071) B3951071
theorem B1757723 : Blo 1170402 1757723 := bstep (se 1 (by rfl) ⟨1318292, by rfl⟩ : syracuseStep 1757723 = 2636585) B2636585
theorem B2634623 : Blo 1170402 2634623 := bstep (se 1 (by rfl) ⟨1975967, by rfl⟩ : syracuseStep 2634623 = 3951935) B3951935
theorem B2635199 : Blo 1170402 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B2635631 : Blo 1170402 2635631 := bstep (se 1 (by rfl) ⟨1976723, by rfl⟩ : syracuseStep 2635631 = 3953447) B3953447
theorem B2636927 : Blo 1170402 2636927 := bstep (se 1 (by rfl) ⟨1977695, by rfl⟩ : syracuseStep 2636927 = 3955391) B3955391
theorem B1318171 : Blo 1170402 1318171 := bstep (se 1 (by rfl) ⟨988628, by rfl⟩ : syracuseStep 1318171 = 1977257) B1977257
theorem B1170971 : Blo 1170402 1170971 := bstep (se 1 (by rfl) ⟨878228, by rfl⟩ : syracuseStep 1170971 = 1756457) B1756457
theorem B3005993 : Blo 1170402 3005993 := bstep (se 2 (by rfl) ⟨1127247, by rfl⟩ : syracuseStep 3005993 = 2254495) B2254495
theorem B1171195 : Blo 1170402 1171195 := bstep (se 1 (by rfl) ⟨878396, by rfl⟩ : syracuseStep 1171195 = 1756793) B1756793
theorem B5005223 : Blo 1170402 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B1171815 : Blo 1170402 1171815 := bstep (se 1 (by rfl) ⟨878861, by rfl⟩ : syracuseStep 1171815 = 1757723) B1757723
theorem B1039631921 : Blo 1170402 1039631921 := bstep (se 2 (by rfl) ⟨389861970, by rfl⟩ : syracuseStep 1039631921 = 779723941) B779723941
theorem B3950207 : Blo 1170402 3950207 := bstep (se 1 (by rfl) ⟨2962655, by rfl⟩ : syracuseStep 3950207 = 5925311) B5925311
theorem B5925473 : Blo 1170402 5925473 := bstep (se 2 (by rfl) ⟨2222052, by rfl⟩ : syracuseStep 5925473 = 4444105) B4444105
theorem B3336815 : Blo 1170402 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B4221659 : Blo 1170402 4221659 := bstep (se 1 (by rfl) ⟨3166244, by rfl⟩ : syracuseStep 4221659 = 6332489) B6332489
theorem B1756031 : Blo 1170402 1756031 := bstep (se 1 (by rfl) ⟨1317023, by rfl⟩ : syracuseStep 1756031 = 2634047) B2634047
theorem B1584155 : Blo 1170402 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B45034703 : Blo 1170402 45034703 := bstep (se 1 (by rfl) ⟨33776027, by rfl⟩ : syracuseStep 45034703 = 67552055) B67552055
theorem B1756415 : Blo 1170402 1756415 := bstep (se 1 (by rfl) ⟨1317311, by rfl⟩ : syracuseStep 1756415 = 2634623) B2634623
theorem B2223359 : Blo 1170402 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B1756799 : Blo 1170402 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B10006415 : Blo 1170402 10006415 := bstep (se 1 (by rfl) ⟨7504811, by rfl⟩ : syracuseStep 10006415 = 15009623) B15009623
theorem B1757087 : Blo 1170402 1757087 := bstep (se 1 (by rfl) ⟨1317815, by rfl⟩ : syracuseStep 1757087 = 2635631) B2635631
theorem B1978303 : Blo 1170402 1978303 := bstep (se 1 (by rfl) ⟨1483727, by rfl⟩ : syracuseStep 1978303 = 2967455) B2967455
theorem B1757561 : Blo 1170402 1757561 := bstep (se 2 (by rfl) ⟨659085, by rfl⟩ : syracuseStep 1757561 = 1318171) B1318171
theorem B2634281 : Blo 1170402 2634281 := bstep (se 2 (by rfl) ⟨987855, by rfl⟩ : syracuseStep 2634281 = 1975711) B1975711
theorem B42865337 : Blo 1170402 42865337 := bstep (se 2 (by rfl) ⟨16074501, by rfl⟩ : syracuseStep 42865337 = 32149003) B32149003
theorem B1757951 : Blo 1170402 1757951 := bstep (se 1 (by rfl) ⟨1318463, by rfl⟩ : syracuseStep 1757951 = 2636927) B2636927
theorem B2003995 : Blo 1170402 2003995 := bstep (se 1 (by rfl) ⟨1502996, by rfl⟩ : syracuseStep 2003995 = 3005993) B3005993
theorem B24057137 : Blo 1170402 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B7998895637 : Blo 1170402 7998895637 := bstep (se 6 (by rfl) ⟨187474116, by rfl⟩ : syracuseStep 7998895637 = 374948233) B374948233
theorem B13523041 : Blo 1170402 13523041 := bstep (se 2 (by rfl) ⟨5071140, by rfl⟩ : syracuseStep 13523041 = 10142281) B10142281
theorem B1170623 : Blo 1170402 1170623 := bstep (se 1 (by rfl) ⟨877967, by rfl⟩ : syracuseStep 1170623 = 1755935) B1755935
theorem B1170879 : Blo 1170402 1170879 := bstep (se 1 (by rfl) ⟨878159, by rfl⟩ : syracuseStep 1170879 = 1756319) B1756319
theorem B1171707 : Blo 1170402 1171707 := bstep (se 1 (by rfl) ⟨878780, by rfl⟩ : syracuseStep 1171707 = 1757561) B1757561
theorem B1171967 : Blo 1170402 1171967 := bstep (se 1 (by rfl) ⟨878975, by rfl⟩ : syracuseStep 1171967 = 1757951) B1757951
theorem B72122885 : Blo 1170402 72122885 := bstep (se 4 (by rfl) ⟨6761520, by rfl⟩ : syracuseStep 72122885 = 13523041) B13523041
theorem B2671993 : Blo 1170402 2671993 := bstep (se 2 (by rfl) ⟨1001997, by rfl⟩ : syracuseStep 2671993 = 2003995) B2003995
theorem B8898173 : Blo 1170402 8898173 := bstep (se 3 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 8898173 = 3336815) B3336815
theorem B3950315 : Blo 1170402 3950315 := bstep (se 1 (by rfl) ⟨2962736, by rfl⟩ : syracuseStep 3950315 = 5925473) B5925473
theorem B6670943 : Blo 1170402 6670943 := bstep (se 1 (by rfl) ⟨5003207, by rfl⟩ : syracuseStep 6670943 = 10006415) B10006415
theorem B1756187 : Blo 1170402 1756187 := bstep (se 1 (by rfl) ⟨1317140, by rfl⟩ : syracuseStep 1756187 = 2634281) B2634281
theorem B28576891 : Blo 1170402 28576891 := bstep (se 1 (by rfl) ⟨21432668, by rfl⟩ : syracuseStep 28576891 = 42865337) B42865337
theorem B693087947 : Blo 1170402 693087947 := bstep (se 1 (by rfl) ⟨519815960, by rfl⟩ : syracuseStep 693087947 = 1039631921) B1039631921
theorem B2633471 : Blo 1170402 2633471 := bstep (se 1 (by rfl) ⟨1975103, by rfl⟩ : syracuseStep 2633471 = 3950207) B3950207
theorem B2814439 : Blo 1170402 2814439 := bstep (se 1 (by rfl) ⟨2110829, by rfl⟩ : syracuseStep 2814439 = 4221659) B4221659
theorem B4224413 : Blo 1170402 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B16038091 : Blo 1170402 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B5332597091 : Blo 1170402 5332597091 := bstep (se 1 (by rfl) ⟨3999447818, by rfl⟩ : syracuseStep 5332597091 = 7998895637) B7998895637
theorem B1170687 : Blo 1170402 1170687 := bstep (se 1 (by rfl) ⟨878015, by rfl⟩ : syracuseStep 1170687 = 1756031) B1756031
theorem B30023135 : Blo 1170402 30023135 := bstep (se 1 (by rfl) ⟨22517351, by rfl⟩ : syracuseStep 30023135 = 45034703) B45034703
theorem B1170943 : Blo 1170402 1170943 := bstep (se 1 (by rfl) ⟨878207, by rfl⟩ : syracuseStep 1170943 = 1756415) B1756415
theorem B1482239 : Blo 1170402 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B1171199 : Blo 1170402 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B2637737 : Blo 1170402 2637737 := bstep (se 2 (by rfl) ⟨989151, by rfl⟩ : syracuseStep 2637737 = 1978303) B1978303
theorem B1171391 : Blo 1170402 1171391 := bstep (se 1 (by rfl) ⟨878543, by rfl⟩ : syracuseStep 1171391 = 1757087) B1757087
theorem B3752585 : Blo 1170402 3752585 := bstep (se 2 (by rfl) ⟨1407219, by rfl⟩ : syracuseStep 3752585 = 2814439) B2814439
theorem B11265101 : Blo 1170402 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B5932115 : Blo 1170402 5932115 := bstep (se 1 (by rfl) ⟨4449086, by rfl⟩ : syracuseStep 5932115 = 8898173) B8898173
theorem B20015423 : Blo 1170402 20015423 := bstep (se 1 (by rfl) ⟨15011567, by rfl⟩ : syracuseStep 20015423 = 30023135) B30023135
theorem B1755647 : Blo 1170402 1755647 := bstep (se 1 (by rfl) ⟨1316735, by rfl⟩ : syracuseStep 1755647 = 2633471) B2633471
theorem B21384121 : Blo 1170402 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B48081923 : Blo 1170402 48081923 := bstep (se 1 (by rfl) ⟨36061442, by rfl⟩ : syracuseStep 48081923 = 72122885) B72122885
theorem B2633543 : Blo 1170402 2633543 := bstep (se 1 (by rfl) ⟨1975157, by rfl⟩ : syracuseStep 2633543 = 3950315) B3950315
theorem B3952637 : Blo 1170402 3952637 := bstep (se 3 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 3952637 = 1482239) B1482239
theorem B14250629 : Blo 1170402 14250629 := bstep (se 4 (by rfl) ⟨1335996, by rfl⟩ : syracuseStep 14250629 = 2671993) B2671993
theorem B462058631 : Blo 1170402 462058631 := bstep (se 1 (by rfl) ⟨346543973, by rfl⟩ : syracuseStep 462058631 = 693087947) B693087947
theorem B1758491 : Blo 1170402 1758491 := bstep (se 1 (by rfl) ⟨1318868, by rfl⟩ : syracuseStep 1758491 = 2637737) B2637737
theorem B152410085 : Blo 1170402 152410085 := bstep (se 4 (by rfl) ⟨14288445, by rfl⟩ : syracuseStep 152410085 = 28576891) B28576891
theorem B3555064727 : Blo 1170402 3555064727 := bstep (se 1 (by rfl) ⟨2666298545, by rfl⟩ : syracuseStep 3555064727 = 5332597091) B5332597091
theorem B4447295 : Blo 1170402 4447295 := bstep (se 1 (by rfl) ⟨3335471, by rfl⟩ : syracuseStep 4447295 = 6670943) B6670943
theorem B1170791 : Blo 1170402 1170791 := bstep (se 1 (by rfl) ⟨878093, by rfl⟩ : syracuseStep 1170791 = 1756187) B1756187
theorem B1172327 : Blo 1170402 1172327 := bstep (se 1 (by rfl) ⟨879245, by rfl⟩ : syracuseStep 1172327 = 1758491) B1758491
theorem B101606723 : Blo 1170402 101606723 := bstep (se 1 (by rfl) ⟨76205042, by rfl⟩ : syracuseStep 101606723 = 152410085) B152410085
theorem B1755695 : Blo 1170402 1755695 := bstep (se 1 (by rfl) ⟨1316771, by rfl⟩ : syracuseStep 1755695 = 2633543) B2633543
theorem B2501723 : Blo 1170402 2501723 := bstep (se 1 (by rfl) ⟨1876292, by rfl⟩ : syracuseStep 2501723 = 3752585) B3752585
theorem B308039087 : Blo 1170402 308039087 := bstep (se 1 (by rfl) ⟨231029315, by rfl⟩ : syracuseStep 308039087 = 462058631) B462058631
theorem B28512161 : Blo 1170402 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B2635091 : Blo 1170402 2635091 := bstep (se 1 (by rfl) ⟨1976318, by rfl⟩ : syracuseStep 2635091 = 3952637) B3952637
theorem B9500419 : Blo 1170402 9500419 := bstep (se 1 (by rfl) ⟨7125314, by rfl⟩ : syracuseStep 9500419 = 14250629) B14250629
theorem B7510067 : Blo 1170402 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B3954743 : Blo 1170402 3954743 := bstep (se 1 (by rfl) ⟨2966057, by rfl⟩ : syracuseStep 3954743 = 5932115) B5932115
theorem B13343615 : Blo 1170402 13343615 := bstep (se 1 (by rfl) ⟨10007711, by rfl⟩ : syracuseStep 13343615 = 20015423) B20015423
theorem B1170431 : Blo 1170402 1170431 := bstep (se 1 (by rfl) ⟨877823, by rfl⟩ : syracuseStep 1170431 = 1755647) B1755647
theorem B2370043151 : Blo 1170402 2370043151 := bstep (se 1 (by rfl) ⟨1777532363, by rfl⟩ : syracuseStep 2370043151 = 3555064727) B3555064727
theorem B32054615 : Blo 1170402 32054615 := bstep (se 1 (by rfl) ⟨24040961, by rfl⟩ : syracuseStep 32054615 = 48081923) B48081923
theorem B2964863 : Blo 1170402 2964863 := bstep (se 1 (by rfl) ⟨2223647, by rfl⟩ : syracuseStep 2964863 = 4447295) B4447295
theorem B5006711 : Blo 1170402 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B1976575 : Blo 1170402 1976575 := bstep (se 1 (by rfl) ⟨1482431, by rfl⟩ : syracuseStep 1976575 = 2964863) B2964863
theorem B205359391 : Blo 1170402 205359391 := bstep (se 1 (by rfl) ⟨154019543, by rfl⟩ : syracuseStep 205359391 = 308039087) B308039087
theorem B12667225 : Blo 1170402 12667225 := bstep (se 2 (by rfl) ⟨4750209, by rfl⟩ : syracuseStep 12667225 = 9500419) B9500419
theorem B19008107 : Blo 1170402 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B6671261 : Blo 1170402 6671261 := bstep (se 3 (by rfl) ⟨1250861, by rfl⟩ : syracuseStep 6671261 = 2501723) B2501723
theorem B1756727 : Blo 1170402 1756727 := bstep (se 1 (by rfl) ⟨1317545, by rfl⟩ : syracuseStep 1756727 = 2635091) B2635091
theorem B1580028767 : Blo 1170402 1580028767 := bstep (se 1 (by rfl) ⟨1185021575, by rfl⟩ : syracuseStep 1580028767 = 2370043151) B2370043151
theorem B21369743 : Blo 1170402 21369743 := bstep (se 1 (by rfl) ⟨16027307, by rfl⟩ : syracuseStep 21369743 = 32054615) B32054615
theorem B67737815 : Blo 1170402 67737815 := bstep (se 1 (by rfl) ⟨50803361, by rfl⟩ : syracuseStep 67737815 = 101606723) B101606723
theorem B2636495 : Blo 1170402 2636495 := bstep (se 1 (by rfl) ⟨1977371, by rfl⟩ : syracuseStep 2636495 = 3954743) B3954743
theorem B1170463 : Blo 1170402 1170463 := bstep (se 1 (by rfl) ⟨877847, by rfl⟩ : syracuseStep 1170463 = 1755695) B1755695
theorem B8895743 : Blo 1170402 8895743 := bstep (se 1 (by rfl) ⟨6671807, by rfl⟩ : syracuseStep 8895743 = 13343615) B13343615
theorem B1053352511 : Blo 1170402 1053352511 := bstep (se 1 (by rfl) ⟨790014383, by rfl⟩ : syracuseStep 1053352511 = 1580028767) B1580028767
theorem B14246495 : Blo 1170402 14246495 := bstep (se 1 (by rfl) ⟨10684871, by rfl⟩ : syracuseStep 14246495 = 21369743) B21369743
theorem B273812521 : Blo 1170402 273812521 := bstep (se 2 (by rfl) ⟨102679695, by rfl⟩ : syracuseStep 273812521 = 205359391) B205359391
theorem B3337807 : Blo 1170402 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B45158543 : Blo 1170402 45158543 := bstep (se 1 (by rfl) ⟨33868907, by rfl⟩ : syracuseStep 45158543 = 67737815) B67737815
theorem B1757663 : Blo 1170402 1757663 := bstep (se 1 (by rfl) ⟨1318247, by rfl⟩ : syracuseStep 1757663 = 2636495) B2636495
theorem B2635433 : Blo 1170402 2635433 := bstep (se 2 (by rfl) ⟨988287, by rfl⟩ : syracuseStep 2635433 = 1976575) B1976575
theorem B16889633 : Blo 1170402 16889633 := bstep (se 2 (by rfl) ⟨6333612, by rfl⟩ : syracuseStep 16889633 = 12667225) B12667225
theorem B12672071 : Blo 1170402 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B4447507 : Blo 1170402 4447507 := bstep (se 1 (by rfl) ⟨3335630, by rfl⟩ : syracuseStep 4447507 = 6671261) B6671261
theorem B5930495 : Blo 1170402 5930495 := bstep (se 1 (by rfl) ⟨4447871, by rfl⟩ : syracuseStep 5930495 = 8895743) B8895743
theorem B1171151 : Blo 1170402 1171151 := bstep (se 1 (by rfl) ⟨878363, by rfl⟩ : syracuseStep 1171151 = 1756727) B1756727
theorem B30105695 : Blo 1170402 30105695 := bstep (se 1 (by rfl) ⟨22579271, by rfl⟩ : syracuseStep 30105695 = 45158543) B45158543
theorem B1171775 : Blo 1170402 1171775 := bstep (se 1 (by rfl) ⟨878831, by rfl⟩ : syracuseStep 1171775 = 1757663) B1757663
theorem B702235007 : Blo 1170402 702235007 := bstep (se 1 (by rfl) ⟨526676255, by rfl⟩ : syracuseStep 702235007 = 1053352511) B1053352511
theorem B8448047 : Blo 1170402 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B4450409 : Blo 1170402 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B9497663 : Blo 1170402 9497663 := bstep (se 1 (by rfl) ⟨7123247, by rfl⟩ : syracuseStep 9497663 = 14246495) B14246495
theorem B1756955 : Blo 1170402 1756955 := bstep (se 1 (by rfl) ⟨1317716, by rfl⟩ : syracuseStep 1756955 = 2635433) B2635433
theorem B11259755 : Blo 1170402 11259755 := bstep (se 1 (by rfl) ⟨8444816, by rfl⟩ : syracuseStep 11259755 = 16889633) B16889633
theorem B3953663 : Blo 1170402 3953663 := bstep (se 1 (by rfl) ⟨2965247, by rfl⟩ : syracuseStep 3953663 = 5930495) B5930495
theorem B365083361 : Blo 1170402 365083361 := bstep (se 2 (by rfl) ⟨136906260, by rfl⟩ : syracuseStep 365083361 = 273812521) B273812521
theorem B5930009 : Blo 1170402 5930009 := bstep (se 2 (by rfl) ⟨2223753, by rfl⟩ : syracuseStep 5930009 = 4447507) B4447507
theorem B80281853 : Blo 1170402 80281853 := bstep (se 3 (by rfl) ⟨15052847, by rfl⟩ : syracuseStep 80281853 = 30105695) B30105695
theorem B468156671 : Blo 1170402 468156671 := bstep (se 1 (by rfl) ⟨351117503, by rfl⟩ : syracuseStep 468156671 = 702235007) B702235007
theorem B2966939 : Blo 1170402 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B7506503 : Blo 1170402 7506503 := bstep (se 1 (by rfl) ⟨5629877, by rfl⟩ : syracuseStep 7506503 = 11259755) B11259755
theorem B5632031 : Blo 1170402 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B243388907 : Blo 1170402 243388907 := bstep (se 1 (by rfl) ⟨182541680, by rfl⟩ : syracuseStep 243388907 = 365083361) B365083361
theorem B3953339 : Blo 1170402 3953339 := bstep (se 1 (by rfl) ⟨2965004, by rfl⟩ : syracuseStep 3953339 = 5930009) B5930009
theorem B2635775 : Blo 1170402 2635775 := bstep (se 1 (by rfl) ⟨1976831, by rfl⟩ : syracuseStep 2635775 = 3953663) B3953663
theorem B6331775 : Blo 1170402 6331775 := bstep (se 1 (by rfl) ⟨4748831, by rfl⟩ : syracuseStep 6331775 = 9497663) B9497663
theorem B1171303 : Blo 1170402 1171303 := bstep (se 1 (by rfl) ⟨878477, by rfl⟩ : syracuseStep 1171303 = 1756955) B1756955
theorem B162259271 : Blo 1170402 162259271 := bstep (se 1 (by rfl) ⟨121694453, by rfl⟩ : syracuseStep 162259271 = 243388907) B243388907
theorem B16884733 : Blo 1170402 16884733 := bstep (se 3 (by rfl) ⟨3165887, by rfl⟩ : syracuseStep 16884733 = 6331775) B6331775
theorem B3754687 : Blo 1170402 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B53521235 : Blo 1170402 53521235 := bstep (se 1 (by rfl) ⟨40140926, by rfl⟩ : syracuseStep 53521235 = 80281853) B80281853
theorem B1977959 : Blo 1170402 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B1757183 : Blo 1170402 1757183 := bstep (se 1 (by rfl) ⟨1317887, by rfl⟩ : syracuseStep 1757183 = 2635775) B2635775
theorem B312104447 : Blo 1170402 312104447 := bstep (se 1 (by rfl) ⟨234078335, by rfl⟩ : syracuseStep 312104447 = 468156671) B468156671
theorem B2635559 : Blo 1170402 2635559 := bstep (se 1 (by rfl) ⟨1976669, by rfl⟩ : syracuseStep 2635559 = 3953339) B3953339
theorem B5004335 : Blo 1170402 5004335 := bstep (se 1 (by rfl) ⟨3753251, by rfl⟩ : syracuseStep 5004335 = 7506503) B7506503
theorem B5006249 : Blo 1170402 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B208069631 : Blo 1170402 208069631 := bstep (se 1 (by rfl) ⟨156052223, by rfl⟩ : syracuseStep 208069631 = 312104447) B312104447
theorem B22512977 : Blo 1170402 22512977 := bstep (se 2 (by rfl) ⟨8442366, by rfl⟩ : syracuseStep 22512977 = 16884733) B16884733
theorem B3336223 : Blo 1170402 3336223 := bstep (se 1 (by rfl) ⟨2502167, by rfl⟩ : syracuseStep 3336223 = 5004335) B5004335
theorem B1757039 : Blo 1170402 1757039 := bstep (se 1 (by rfl) ⟨1317779, by rfl⟩ : syracuseStep 1757039 = 2635559) B2635559
theorem B35680823 : Blo 1170402 35680823 := bstep (se 1 (by rfl) ⟨26760617, by rfl⟩ : syracuseStep 35680823 = 53521235) B53521235
theorem B108172847 : Blo 1170402 108172847 := bstep (se 1 (by rfl) ⟨81129635, by rfl⟩ : syracuseStep 108172847 = 162259271) B162259271
theorem B1318639 : Blo 1170402 1318639 := bstep (se 1 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 1318639 = 1977959) B1977959
theorem B1171455 : Blo 1170402 1171455 := bstep (se 1 (by rfl) ⟨878591, by rfl⟩ : syracuseStep 1171455 = 1757183) B1757183
theorem B4448297 : Blo 1170402 4448297 := bstep (se 2 (by rfl) ⟨1668111, by rfl⟩ : syracuseStep 4448297 = 3336223) B3336223
theorem B15008651 : Blo 1170402 15008651 := bstep (se 1 (by rfl) ⟨11256488, by rfl⟩ : syracuseStep 15008651 = 22512977) B22512977
theorem B72115231 : Blo 1170402 72115231 := bstep (se 1 (by rfl) ⟨54086423, by rfl⟩ : syracuseStep 72115231 = 108172847) B108172847
theorem B3337499 : Blo 1170402 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B1758185 : Blo 1170402 1758185 := bstep (se 2 (by rfl) ⟨659319, by rfl⟩ : syracuseStep 1758185 = 1318639) B1318639
theorem B23787215 : Blo 1170402 23787215 := bstep (se 1 (by rfl) ⟨17840411, by rfl⟩ : syracuseStep 23787215 = 35680823) B35680823
theorem B138713087 : Blo 1170402 138713087 := bstep (se 1 (by rfl) ⟨104034815, by rfl⟩ : syracuseStep 138713087 = 208069631) B208069631
theorem B1171359 : Blo 1170402 1171359 := bstep (se 1 (by rfl) ⟨878519, by rfl⟩ : syracuseStep 1171359 = 1757039) B1757039
theorem B2965531 : Blo 1170402 2965531 := bstep (se 1 (by rfl) ⟨2224148, by rfl⟩ : syracuseStep 2965531 = 4448297) B4448297
theorem B1172123 : Blo 1170402 1172123 := bstep (se 1 (by rfl) ⟨879092, by rfl⟩ : syracuseStep 1172123 = 1758185) B1758185
theorem B10005767 : Blo 1170402 10005767 := bstep (se 1 (by rfl) ⟨7504325, by rfl⟩ : syracuseStep 10005767 = 15008651) B15008651
theorem B96153641 : Blo 1170402 96153641 := bstep (se 2 (by rfl) ⟨36057615, by rfl⟩ : syracuseStep 96153641 = 72115231) B72115231
theorem B2224999 : Blo 1170402 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B15858143 : Blo 1170402 15858143 := bstep (se 1 (by rfl) ⟨11893607, by rfl⟩ : syracuseStep 15858143 = 23787215) B23787215
theorem B369901565 : Blo 1170402 369901565 := bstep (se 3 (by rfl) ⟨69356543, by rfl⟩ : syracuseStep 369901565 = 138713087) B138713087
theorem B64102427 : Blo 1170402 64102427 := bstep (se 1 (by rfl) ⟨48076820, by rfl⟩ : syracuseStep 64102427 = 96153641) B96153641
theorem B2966665 : Blo 1170402 2966665 := bstep (se 2 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 2966665 = 2224999) B2224999
theorem B6670511 : Blo 1170402 6670511 := bstep (se 1 (by rfl) ⟨5002883, by rfl⟩ : syracuseStep 6670511 = 10005767) B10005767
theorem B10572095 : Blo 1170402 10572095 := bstep (se 1 (by rfl) ⟨7929071, by rfl⟩ : syracuseStep 10572095 = 15858143) B15858143
theorem B246601043 : Blo 1170402 246601043 := bstep (se 1 (by rfl) ⟨184950782, by rfl⟩ : syracuseStep 246601043 = 369901565) B369901565
theorem B3954041 : Blo 1170402 3954041 := bstep (se 2 (by rfl) ⟨1482765, by rfl⟩ : syracuseStep 3954041 = 2965531) B2965531
theorem B7048063 : Blo 1170402 7048063 := bstep (se 1 (by rfl) ⟨5286047, by rfl⟩ : syracuseStep 7048063 = 10572095) B10572095
theorem B164400695 : Blo 1170402 164400695 := bstep (se 1 (by rfl) ⟨123300521, by rfl⟩ : syracuseStep 164400695 = 246601043) B246601043
theorem B42734951 : Blo 1170402 42734951 := bstep (se 1 (by rfl) ⟨32051213, by rfl⟩ : syracuseStep 42734951 = 64102427) B64102427
theorem B2636027 : Blo 1170402 2636027 := bstep (se 1 (by rfl) ⟨1977020, by rfl⟩ : syracuseStep 2636027 = 3954041) B3954041
theorem B4447007 : Blo 1170402 4447007 := bstep (se 1 (by rfl) ⟨3335255, by rfl⟩ : syracuseStep 4447007 = 6670511) B6670511
theorem B3955553 : Blo 1170402 3955553 := bstep (se 2 (by rfl) ⟨1483332, by rfl⟩ : syracuseStep 3955553 = 2966665) B2966665
theorem B9397417 : Blo 1170402 9397417 := bstep (se 2 (by rfl) ⟨3524031, by rfl⟩ : syracuseStep 9397417 = 7048063) B7048063
theorem B1757351 : Blo 1170402 1757351 := bstep (se 1 (by rfl) ⟨1318013, by rfl⟩ : syracuseStep 1757351 = 2636027) B2636027
theorem B28489967 : Blo 1170402 28489967 := bstep (se 1 (by rfl) ⟨21367475, by rfl⟩ : syracuseStep 28489967 = 42734951) B42734951
theorem B2964671 : Blo 1170402 2964671 := bstep (se 1 (by rfl) ⟨2223503, by rfl⟩ : syracuseStep 2964671 = 4447007) B4447007
theorem B2637035 : Blo 1170402 2637035 := bstep (se 1 (by rfl) ⟨1977776, by rfl⟩ : syracuseStep 2637035 = 3955553) B3955553
theorem B109600463 : Blo 1170402 109600463 := bstep (se 1 (by rfl) ⟨82200347, by rfl⟩ : syracuseStep 109600463 = 164400695) B164400695
theorem B1171567 : Blo 1170402 1171567 := bstep (se 1 (by rfl) ⟨878675, by rfl⟩ : syracuseStep 1171567 = 1757351) B1757351
theorem B292267901 : Blo 1170402 292267901 := bstep (se 3 (by rfl) ⟨54800231, by rfl⟩ : syracuseStep 292267901 = 109600463) B109600463
theorem B1976447 : Blo 1170402 1976447 := bstep (se 1 (by rfl) ⟨1482335, by rfl⟩ : syracuseStep 1976447 = 2964671) B2964671
theorem B18993311 : Blo 1170402 18993311 := bstep (se 1 (by rfl) ⟨14244983, by rfl⟩ : syracuseStep 18993311 = 28489967) B28489967
theorem B12529889 : Blo 1170402 12529889 := bstep (se 2 (by rfl) ⟨4698708, by rfl⟩ : syracuseStep 12529889 = 9397417) B9397417
theorem B1758023 : Blo 1170402 1758023 := bstep (se 1 (by rfl) ⟨1318517, by rfl⟩ : syracuseStep 1758023 = 2637035) B2637035
theorem B1172015 : Blo 1170402 1172015 := bstep (se 1 (by rfl) ⟨879011, by rfl⟩ : syracuseStep 1172015 = 1758023) B1758023
theorem B12662207 : Blo 1170402 12662207 := bstep (se 1 (by rfl) ⟨9496655, by rfl⟩ : syracuseStep 12662207 = 18993311) B18993311
theorem B8353259 : Blo 1170402 8353259 := bstep (se 1 (by rfl) ⟨6264944, by rfl⟩ : syracuseStep 8353259 = 12529889) B12529889
theorem B194845267 : Blo 1170402 194845267 := bstep (se 1 (by rfl) ⟨146133950, by rfl⟩ : syracuseStep 194845267 = 292267901) B292267901
theorem B1317631 : Blo 1170402 1317631 := bstep (se 1 (by rfl) ⟨988223, by rfl⟩ : syracuseStep 1317631 = 1976447) B1976447
theorem B259793689 : Blo 1170402 259793689 := bstep (se 2 (by rfl) ⟨97422633, by rfl⟩ : syracuseStep 259793689 = 194845267) B194845267
theorem B8441471 : Blo 1170402 8441471 := bstep (se 1 (by rfl) ⟨6331103, by rfl⟩ : syracuseStep 8441471 = 12662207) B12662207
theorem B1756841 : Blo 1170402 1756841 := bstep (se 2 (by rfl) ⟨658815, by rfl⟩ : syracuseStep 1756841 = 1317631) B1317631
theorem B5568839 : Blo 1170402 5568839 := bstep (se 1 (by rfl) ⟨4176629, by rfl⟩ : syracuseStep 5568839 = 8353259) B8353259
theorem B346391585 : Blo 1170402 346391585 := bstep (se 2 (by rfl) ⟨129896844, by rfl⟩ : syracuseStep 346391585 = 259793689) B259793689
theorem B3712559 : Blo 1170402 3712559 := bstep (se 1 (by rfl) ⟨2784419, by rfl⟩ : syracuseStep 3712559 = 5568839) B5568839
theorem B5627647 : Blo 1170402 5627647 := bstep (se 1 (by rfl) ⟨4220735, by rfl⟩ : syracuseStep 5627647 = 8441471) B8441471
theorem B1171227 : Blo 1170402 1171227 := bstep (se 1 (by rfl) ⟨878420, by rfl⟩ : syracuseStep 1171227 = 1756841) B1756841
theorem B230927723 : Blo 1170402 230927723 := bstep (se 1 (by rfl) ⟨173195792, by rfl⟩ : syracuseStep 230927723 = 346391585) B346391585
theorem B9900157 : Blo 1170402 9900157 := bstep (se 3 (by rfl) ⟨1856279, by rfl⟩ : syracuseStep 9900157 = 3712559) B3712559
theorem B7503529 : Blo 1170402 7503529 := bstep (se 2 (by rfl) ⟨2813823, by rfl⟩ : syracuseStep 7503529 = 5627647) B5627647
theorem B10004705 : Blo 1170402 10004705 := bstep (se 2 (by rfl) ⟨3751764, by rfl⟩ : syracuseStep 10004705 = 7503529) B7503529
theorem B13200209 : Blo 1170402 13200209 := bstep (se 2 (by rfl) ⟨4950078, by rfl⟩ : syracuseStep 13200209 = 9900157) B9900157
theorem B153951815 : Blo 1170402 153951815 := bstep (se 1 (by rfl) ⟨115463861, by rfl⟩ : syracuseStep 153951815 = 230927723) B230927723
theorem B6669803 : Blo 1170402 6669803 := bstep (se 1 (by rfl) ⟨5002352, by rfl⟩ : syracuseStep 6669803 = 10004705) B10004705
theorem B8800139 : Blo 1170402 8800139 := bstep (se 1 (by rfl) ⟨6600104, by rfl⟩ : syracuseStep 8800139 = 13200209) B13200209
theorem B102634543 : Blo 1170402 102634543 := bstep (se 1 (by rfl) ⟨76975907, by rfl⟩ : syracuseStep 102634543 = 153951815) B153951815
theorem B5866759 : Blo 1170402 5866759 := bstep (se 1 (by rfl) ⟨4400069, by rfl⟩ : syracuseStep 5866759 = 8800139) B8800139
theorem B4446535 : Blo 1170402 4446535 := bstep (se 1 (by rfl) ⟨3334901, by rfl⟩ : syracuseStep 4446535 = 6669803) B6669803
theorem B136846057 : Blo 1170402 136846057 := bstep (se 2 (by rfl) ⟨51317271, by rfl⟩ : syracuseStep 136846057 = 102634543) B102634543
theorem B182461409 : Blo 1170402 182461409 := bstep (se 2 (by rfl) ⟨68423028, by rfl⟩ : syracuseStep 182461409 = 136846057) B136846057
theorem B5928713 : Blo 1170402 5928713 := bstep (se 2 (by rfl) ⟨2223267, by rfl⟩ : syracuseStep 5928713 = 4446535) B4446535
theorem B7822345 : Blo 1170402 7822345 := bstep (se 2 (by rfl) ⟨2933379, by rfl⟩ : syracuseStep 7822345 = 5866759) B5866759
theorem B10429793 : Blo 1170402 10429793 := bstep (se 2 (by rfl) ⟨3911172, by rfl⟩ : syracuseStep 10429793 = 7822345) B7822345
theorem B3952475 : Blo 1170402 3952475 := bstep (se 1 (by rfl) ⟨2964356, by rfl⟩ : syracuseStep 3952475 = 5928713) B5928713
theorem B121640939 : Blo 1170402 121640939 := bstep (se 1 (by rfl) ⟨91230704, by rfl⟩ : syracuseStep 121640939 = 182461409) B182461409
theorem B81093959 : Blo 1170402 81093959 := bstep (se 1 (by rfl) ⟨60820469, by rfl⟩ : syracuseStep 81093959 = 121640939) B121640939
theorem B2634983 : Blo 1170402 2634983 := bstep (se 1 (by rfl) ⟨1976237, by rfl⟩ : syracuseStep 2634983 = 3952475) B3952475
theorem B6953195 : Blo 1170402 6953195 := bstep (se 1 (by rfl) ⟨5214896, by rfl⟩ : syracuseStep 6953195 = 10429793) B10429793
theorem B1756655 : Blo 1170402 1756655 := bstep (se 1 (by rfl) ⟨1317491, by rfl⟩ : syracuseStep 1756655 = 2634983) B2634983
theorem B54062639 : Blo 1170402 54062639 := bstep (se 1 (by rfl) ⟨40546979, by rfl⟩ : syracuseStep 54062639 = 81093959) B81093959
theorem B4635463 : Blo 1170402 4635463 := bstep (se 1 (by rfl) ⟨3476597, by rfl⟩ : syracuseStep 4635463 = 6953195) B6953195
theorem B6180617 : Blo 1170402 6180617 := bstep (se 2 (by rfl) ⟨2317731, by rfl⟩ : syracuseStep 6180617 = 4635463) B4635463
theorem B36041759 : Blo 1170402 36041759 := bstep (se 1 (by rfl) ⟨27031319, by rfl⟩ : syracuseStep 36041759 = 54062639) B54062639
theorem B1171103 : Blo 1170402 1171103 := bstep (se 1 (by rfl) ⟨878327, by rfl⟩ : syracuseStep 1171103 = 1756655) B1756655
theorem B24027839 : Blo 1170402 24027839 := bstep (se 1 (by rfl) ⟨18020879, by rfl⟩ : syracuseStep 24027839 = 36041759) B36041759
theorem B4120411 : Blo 1170402 4120411 := bstep (se 1 (by rfl) ⟨3090308, by rfl⟩ : syracuseStep 4120411 = 6180617) B6180617
theorem B16018559 : Blo 1170402 16018559 := bstep (se 1 (by rfl) ⟨12013919, by rfl⟩ : syracuseStep 16018559 = 24027839) B24027839
theorem B5493881 : Blo 1170402 5493881 := bstep (se 2 (by rfl) ⟨2060205, by rfl⟩ : syracuseStep 5493881 = 4120411) B4120411
theorem B3662587 : Blo 1170402 3662587 := bstep (se 1 (by rfl) ⟨2746940, by rfl⟩ : syracuseStep 3662587 = 5493881) B5493881
theorem B10679039 : Blo 1170402 10679039 := bstep (se 1 (by rfl) ⟨8009279, by rfl⟩ : syracuseStep 10679039 = 16018559) B16018559
theorem B7119359 : Blo 1170402 7119359 := bstep (se 1 (by rfl) ⟨5339519, by rfl⟩ : syracuseStep 7119359 = 10679039) B10679039
theorem B19533797 : Blo 1170402 19533797 := bstep (se 4 (by rfl) ⟨1831293, by rfl⟩ : syracuseStep 19533797 = 3662587) B3662587
theorem B4746239 : Blo 1170402 4746239 := bstep (se 1 (by rfl) ⟨3559679, by rfl⟩ : syracuseStep 4746239 = 7119359) B7119359
theorem B13022531 : Blo 1170402 13022531 := bstep (se 1 (by rfl) ⟨9766898, by rfl⟩ : syracuseStep 13022531 = 19533797) B19533797
theorem B3164159 : Blo 1170402 3164159 := bstep (se 1 (by rfl) ⟨2373119, by rfl⟩ : syracuseStep 3164159 = 4746239) B4746239
theorem B8681687 : Blo 1170402 8681687 := bstep (se 1 (by rfl) ⟨6511265, by rfl⟩ : syracuseStep 8681687 = 13022531) B13022531
theorem B2109439 : Blo 1170402 2109439 := bstep (se 1 (by rfl) ⟨1582079, by rfl⟩ : syracuseStep 2109439 = 3164159) B3164159
theorem B5787791 : Blo 1170402 5787791 := bstep (se 1 (by rfl) ⟨4340843, by rfl⟩ : syracuseStep 5787791 = 8681687) B8681687
theorem B3858527 : Blo 1170402 3858527 := bstep (se 1 (by rfl) ⟨2893895, by rfl⟩ : syracuseStep 3858527 = 5787791) B5787791
theorem B2812585 : Blo 1170402 2812585 := bstep (se 2 (by rfl) ⟨1054719, by rfl⟩ : syracuseStep 2812585 = 2109439) B2109439
theorem B10289405 : Blo 1170402 10289405 := bstep (se 3 (by rfl) ⟨1929263, by rfl⟩ : syracuseStep 10289405 = 3858527) B3858527
theorem B3750113 : Blo 1170402 3750113 := bstep (se 2 (by rfl) ⟨1406292, by rfl⟩ : syracuseStep 3750113 = 2812585) B2812585
theorem B2500075 : Blo 1170402 2500075 := bstep (se 1 (by rfl) ⟨1875056, by rfl⟩ : syracuseStep 2500075 = 3750113) B3750113
theorem B6859603 : Blo 1170402 6859603 := bstep (se 1 (by rfl) ⟨5144702, by rfl⟩ : syracuseStep 6859603 = 10289405) B10289405
theorem B9146137 : Blo 1170402 9146137 := bstep (se 2 (by rfl) ⟨3429801, by rfl⟩ : syracuseStep 9146137 = 6859603) B6859603
theorem B3333433 : Blo 1170402 3333433 := bstep (se 2 (by rfl) ⟨1250037, by rfl⟩ : syracuseStep 3333433 = 2500075) B2500075
theorem B4444577 : Blo 1170402 4444577 := bstep (se 2 (by rfl) ⟨1666716, by rfl⟩ : syracuseStep 4444577 = 3333433) B3333433
theorem B12194849 : Blo 1170402 12194849 := bstep (se 2 (by rfl) ⟨4573068, by rfl⟩ : syracuseStep 12194849 = 9146137) B9146137
theorem B8129899 : Blo 1170402 8129899 := bstep (se 1 (by rfl) ⟨6097424, by rfl⟩ : syracuseStep 8129899 = 12194849) B12194849
theorem B2963051 : Blo 1170402 2963051 := bstep (se 1 (by rfl) ⟨2222288, by rfl⟩ : syracuseStep 2963051 = 4444577) B4444577
theorem B1975367 : Blo 1170402 1975367 := bstep (se 1 (by rfl) ⟨1481525, by rfl⟩ : syracuseStep 1975367 = 2963051) B2963051
theorem B10839865 : Blo 1170402 10839865 := bstep (se 2 (by rfl) ⟨4064949, by rfl⟩ : syracuseStep 10839865 = 8129899) B8129899
theorem B14453153 : Blo 1170402 14453153 := bstep (se 2 (by rfl) ⟨5419932, by rfl⟩ : syracuseStep 14453153 = 10839865) B10839865
theorem B1316911 : Blo 1170402 1316911 := bstep (se 1 (by rfl) ⟨987683, by rfl⟩ : syracuseStep 1316911 = 1975367) B1975367
theorem B9635435 : Blo 1170402 9635435 := bstep (se 1 (by rfl) ⟨7226576, by rfl⟩ : syracuseStep 9635435 = 14453153) B14453153
theorem B1755881 : Blo 1170402 1755881 := bstep (se 2 (by rfl) ⟨658455, by rfl⟩ : syracuseStep 1755881 = 1316911) B1316911
theorem B6423623 : Blo 1170402 6423623 := bstep (se 1 (by rfl) ⟨4817717, by rfl⟩ : syracuseStep 6423623 = 9635435) B9635435
theorem B1170587 : Blo 1170402 1170587 := bstep (se 1 (by rfl) ⟨877940, by rfl⟩ : syracuseStep 1170587 = 1755881) B1755881
theorem B4282415 : Blo 1170402 4282415 := bstep (se 1 (by rfl) ⟨3211811, by rfl⟩ : syracuseStep 4282415 = 6423623) B6423623
theorem B2854943 : Blo 1170402 2854943 := bstep (se 1 (by rfl) ⟨2141207, by rfl⟩ : syracuseStep 2854943 = 4282415) B4282415
theorem B1903295 : Blo 1170402 1903295 := bstep (se 1 (by rfl) ⟨1427471, by rfl⟩ : syracuseStep 1903295 = 2854943) B2854943
theorem B5075453 : Blo 1170402 5075453 := bstep (se 3 (by rfl) ⟨951647, by rfl⟩ : syracuseStep 5075453 = 1903295) B1903295
theorem B3383635 : Blo 1170402 3383635 := bstep (se 1 (by rfl) ⟨2537726, by rfl⟩ : syracuseStep 3383635 = 5075453) B5075453
theorem B4511513 : Blo 1170402 4511513 := bstep (se 2 (by rfl) ⟨1691817, by rfl⟩ : syracuseStep 4511513 = 3383635) B3383635
theorem B3007675 : Blo 1170402 3007675 := bstep (se 1 (by rfl) ⟨2255756, by rfl⟩ : syracuseStep 3007675 = 4511513) B4511513
theorem B4010233 : Blo 1170402 4010233 := bstep (se 2 (by rfl) ⟨1503837, by rfl⟩ : syracuseStep 4010233 = 3007675) B3007675
theorem B5346977 : Blo 1170402 5346977 := bstep (se 2 (by rfl) ⟨2005116, by rfl⟩ : syracuseStep 5346977 = 4010233) B4010233
theorem B14258605 : Blo 1170402 14258605 := bstep (se 3 (by rfl) ⟨2673488, by rfl⟩ : syracuseStep 14258605 = 5346977) B5346977
theorem B19011473 : Blo 1170402 19011473 := bstep (se 2 (by rfl) ⟨7129302, by rfl⟩ : syracuseStep 19011473 = 14258605) B14258605
theorem B12674315 : Blo 1170402 12674315 := bstep (se 1 (by rfl) ⟨9505736, by rfl⟩ : syracuseStep 12674315 = 19011473) B19011473
theorem B8449543 : Blo 1170402 8449543 := bstep (se 1 (by rfl) ⟨6337157, by rfl⟩ : syracuseStep 8449543 = 12674315) B12674315
theorem B11266057 : Blo 1170402 11266057 := bstep (se 2 (by rfl) ⟨4224771, by rfl⟩ : syracuseStep 11266057 = 8449543) B8449543
theorem B15021409 : Blo 1170402 15021409 := bstep (se 2 (by rfl) ⟨5633028, by rfl⟩ : syracuseStep 15021409 = 11266057) B11266057
theorem B20028545 : Blo 1170402 20028545 := bstep (se 2 (by rfl) ⟨7510704, by rfl⟩ : syracuseStep 20028545 = 15021409) B15021409
theorem B13352363 : Blo 1170402 13352363 := bstep (se 1 (by rfl) ⟨10014272, by rfl⟩ : syracuseStep 13352363 = 20028545) B20028545
theorem B8901575 : Blo 1170402 8901575 := bstep (se 1 (by rfl) ⟨6676181, by rfl⟩ : syracuseStep 8901575 = 13352363) B13352363
theorem B5934383 : Blo 1170402 5934383 := bstep (se 1 (by rfl) ⟨4450787, by rfl⟩ : syracuseStep 5934383 = 8901575) B8901575
theorem B3956255 : Blo 1170402 3956255 := bstep (se 1 (by rfl) ⟨2967191, by rfl⟩ : syracuseStep 3956255 = 5934383) B5934383
theorem B2637503 : Blo 1170402 2637503 := bstep (se 1 (by rfl) ⟨1978127, by rfl⟩ : syracuseStep 2637503 = 3956255) B3956255
theorem B1758335 : Blo 1170402 1758335 := bstep (se 1 (by rfl) ⟨1318751, by rfl⟩ : syracuseStep 1758335 = 2637503) B2637503
theorem B1172223 : Blo 1170402 1172223 := bstep (se 1 (by rfl) ⟨879167, by rfl⟩ : syracuseStep 1172223 = 1758335) B1758335

theorem C0 (j : ℕ) (h1 : 292600 ≤ j) (h2 : j ≤ 293099) : Blo 1170402 (4 * j + 3) := by
  interval_cases j
  · exact B1170403
  · exact B1170407
  · exact B1170411
  · exact B1170415
  · exact B1170419
  · exact B1170423
  · exact B1170427
  · exact B1170431
  · exact B1170435
  · exact B1170439
  · exact B1170443
  · exact B1170447
  · exact B1170451
  · exact B1170455
  · exact B1170459
  · exact B1170463
  · exact B1170467
  · exact B1170471
  · exact B1170475
  · exact B1170479
  · exact B1170483
  · exact B1170487
  · exact B1170491
  · exact B1170495
  · exact B1170499
  · exact B1170503
  · exact B1170507
  · exact B1170511
  · exact B1170515
  · exact B1170519
  · exact B1170523
  · exact B1170527
  · exact B1170531
  · exact B1170535
  · exact B1170539
  · exact B1170543
  · exact B1170547
  · exact B1170551
  · exact B1170555
  · exact B1170559
  · exact B1170563
  · exact B1170567
  · exact B1170571
  · exact B1170575
  · exact B1170579
  · exact B1170583
  · exact B1170587
  · exact B1170591
  · exact B1170595
  · exact B1170599
  · exact B1170603
  · exact B1170607
  · exact B1170611
  · exact B1170615
  · exact B1170619
  · exact B1170623
  · exact B1170627
  · exact B1170631
  · exact B1170635
  · exact B1170639
  · exact B1170643
  · exact B1170647
  · exact B1170651
  · exact B1170655
  · exact B1170659
  · exact B1170663
  · exact B1170667
  · exact B1170671
  · exact B1170675
  · exact B1170679
  · exact B1170683
  · exact B1170687
  · exact B1170691
  · exact B1170695
  · exact B1170699
  · exact B1170703
  · exact B1170707
  · exact B1170711
  · exact B1170715
  · exact B1170719
  · exact B1170723
  · exact B1170727
  · exact B1170731
  · exact B1170735
  · exact B1170739
  · exact B1170743
  · exact B1170747
  · exact B1170751
  · exact B1170755
  · exact B1170759
  · exact B1170763
  · exact B1170767
  · exact B1170771
  · exact B1170775
  · exact B1170779
  · exact B1170783
  · exact B1170787
  · exact B1170791
  · exact B1170795
  · exact B1170799
  · exact B1170803
  · exact B1170807
  · exact B1170811
  · exact B1170815
  · exact B1170819
  · exact B1170823
  · exact B1170827
  · exact B1170831
  · exact B1170835
  · exact B1170839
  · exact B1170843
  · exact B1170847
  · exact B1170851
  · exact B1170855
  · exact B1170859
  · exact B1170863
  · exact B1170867
  · exact B1170871
  · exact B1170875
  · exact B1170879
  · exact B1170883
  · exact B1170887
  · exact B1170891
  · exact B1170895
  · exact B1170899
  · exact B1170903
  · exact B1170907
  · exact B1170911
  · exact B1170915
  · exact B1170919
  · exact B1170923
  · exact B1170927
  · exact B1170931
  · exact B1170935
  · exact B1170939
  · exact B1170943
  · exact B1170947
  · exact B1170951
  · exact B1170955
  · exact B1170959
  · exact B1170963
  · exact B1170967
  · exact B1170971
  · exact B1170975
  · exact B1170979
  · exact B1170983
  · exact B1170987
  · exact B1170991
  · exact B1170995
  · exact B1170999
  · exact B1171003
  · exact B1171007
  · exact B1171011
  · exact B1171015
  · exact B1171019
  · exact B1171023
  · exact B1171027
  · exact B1171031
  · exact B1171035
  · exact B1171039
  · exact B1171043
  · exact B1171047
  · exact B1171051
  · exact B1171055
  · exact B1171059
  · exact B1171063
  · exact B1171067
  · exact B1171071
  · exact B1171075
  · exact B1171079
  · exact B1171083
  · exact B1171087
  · exact B1171091
  · exact B1171095
  · exact B1171099
  · exact B1171103
  · exact B1171107
  · exact B1171111
  · exact B1171115
  · exact B1171119
  · exact B1171123
  · exact B1171127
  · exact B1171131
  · exact B1171135
  · exact B1171139
  · exact B1171143
  · exact B1171147
  · exact B1171151
  · exact B1171155
  · exact B1171159
  · exact B1171163
  · exact B1171167
  · exact B1171171
  · exact B1171175
  · exact B1171179
  · exact B1171183
  · exact B1171187
  · exact B1171191
  · exact B1171195
  · exact B1171199
  · exact B1171203
  · exact B1171207
  · exact B1171211
  · exact B1171215
  · exact B1171219
  · exact B1171223
  · exact B1171227
  · exact B1171231
  · exact B1171235
  · exact B1171239
  · exact B1171243
  · exact B1171247
  · exact B1171251
  · exact B1171255
  · exact B1171259
  · exact B1171263
  · exact B1171267
  · exact B1171271
  · exact B1171275
  · exact B1171279
  · exact B1171283
  · exact B1171287
  · exact B1171291
  · exact B1171295
  · exact B1171299
  · exact B1171303
  · exact B1171307
  · exact B1171311
  · exact B1171315
  · exact B1171319
  · exact B1171323
  · exact B1171327
  · exact B1171331
  · exact B1171335
  · exact B1171339
  · exact B1171343
  · exact B1171347
  · exact B1171351
  · exact B1171355
  · exact B1171359
  · exact B1171363
  · exact B1171367
  · exact B1171371
  · exact B1171375
  · exact B1171379
  · exact B1171383
  · exact B1171387
  · exact B1171391
  · exact B1171395
  · exact B1171399
  · exact B1171403
  · exact B1171407
  · exact B1171411
  · exact B1171415
  · exact B1171419
  · exact B1171423
  · exact B1171427
  · exact B1171431
  · exact B1171435
  · exact B1171439
  · exact B1171443
  · exact B1171447
  · exact B1171451
  · exact B1171455
  · exact B1171459
  · exact B1171463
  · exact B1171467
  · exact B1171471
  · exact B1171475
  · exact B1171479
  · exact B1171483
  · exact B1171487
  · exact B1171491
  · exact B1171495
  · exact B1171499
  · exact B1171503
  · exact B1171507
  · exact B1171511
  · exact B1171515
  · exact B1171519
  · exact B1171523
  · exact B1171527
  · exact B1171531
  · exact B1171535
  · exact B1171539
  · exact B1171543
  · exact B1171547
  · exact B1171551
  · exact B1171555
  · exact B1171559
  · exact B1171563
  · exact B1171567
  · exact B1171571
  · exact B1171575
  · exact B1171579
  · exact B1171583
  · exact B1171587
  · exact B1171591
  · exact B1171595
  · exact B1171599
  · exact B1171603
  · exact B1171607
  · exact B1171611
  · exact B1171615
  · exact B1171619
  · exact B1171623
  · exact B1171627
  · exact B1171631
  · exact B1171635
  · exact B1171639
  · exact B1171643
  · exact B1171647
  · exact B1171651
  · exact B1171655
  · exact B1171659
  · exact B1171663
  · exact B1171667
  · exact B1171671
  · exact B1171675
  · exact B1171679
  · exact B1171683
  · exact B1171687
  · exact B1171691
  · exact B1171695
  · exact B1171699
  · exact B1171703
  · exact B1171707
  · exact B1171711
  · exact B1171715
  · exact B1171719
  · exact B1171723
  · exact B1171727
  · exact B1171731
  · exact B1171735
  · exact B1171739
  · exact B1171743
  · exact B1171747
  · exact B1171751
  · exact B1171755
  · exact B1171759
  · exact B1171763
  · exact B1171767
  · exact B1171771
  · exact B1171775
  · exact B1171779
  · exact B1171783
  · exact B1171787
  · exact B1171791
  · exact B1171795
  · exact B1171799
  · exact B1171803
  · exact B1171807
  · exact B1171811
  · exact B1171815
  · exact B1171819
  · exact B1171823
  · exact B1171827
  · exact B1171831
  · exact B1171835
  · exact B1171839
  · exact B1171843
  · exact B1171847
  · exact B1171851
  · exact B1171855
  · exact B1171859
  · exact B1171863
  · exact B1171867
  · exact B1171871
  · exact B1171875
  · exact B1171879
  · exact B1171883
  · exact B1171887
  · exact B1171891
  · exact B1171895
  · exact B1171899
  · exact B1171903
  · exact B1171907
  · exact B1171911
  · exact B1171915
  · exact B1171919
  · exact B1171923
  · exact B1171927
  · exact B1171931
  · exact B1171935
  · exact B1171939
  · exact B1171943
  · exact B1171947
  · exact B1171951
  · exact B1171955
  · exact B1171959
  · exact B1171963
  · exact B1171967
  · exact B1171971
  · exact B1171975
  · exact B1171979
  · exact B1171983
  · exact B1171987
  · exact B1171991
  · exact B1171995
  · exact B1171999
  · exact B1172003
  · exact B1172007
  · exact B1172011
  · exact B1172015
  · exact B1172019
  · exact B1172023
  · exact B1172027
  · exact B1172031
  · exact B1172035
  · exact B1172039
  · exact B1172043
  · exact B1172047
  · exact B1172051
  · exact B1172055
  · exact B1172059
  · exact B1172063
  · exact B1172067
  · exact B1172071
  · exact B1172075
  · exact B1172079
  · exact B1172083
  · exact B1172087
  · exact B1172091
  · exact B1172095
  · exact B1172099
  · exact B1172103
  · exact B1172107
  · exact B1172111
  · exact B1172115
  · exact B1172119
  · exact B1172123
  · exact B1172127
  · exact B1172131
  · exact B1172135
  · exact B1172139
  · exact B1172143
  · exact B1172147
  · exact B1172151
  · exact B1172155
  · exact B1172159
  · exact B1172163
  · exact B1172167
  · exact B1172171
  · exact B1172175
  · exact B1172179
  · exact B1172183
  · exact B1172187
  · exact B1172191
  · exact B1172195
  · exact B1172199
  · exact B1172203
  · exact B1172207
  · exact B1172211
  · exact B1172215
  · exact B1172219
  · exact B1172223
  · exact B1172227
  · exact B1172231
  · exact B1172235
  · exact B1172239
  · exact B1172243
  · exact B1172247
  · exact B1172251
  · exact B1172255
  · exact B1172259
  · exact B1172263
  · exact B1172267
  · exact B1172271
  · exact B1172275
  · exact B1172279
  · exact B1172283
  · exact B1172287
  · exact B1172291
  · exact B1172295
  · exact B1172299
  · exact B1172303
  · exact B1172307
  · exact B1172311
  · exact B1172315
  · exact B1172319
  · exact B1172323
  · exact B1172327
  · exact B1172331
  · exact B1172335
  · exact B1172339
  · exact B1172343
  · exact B1172347
  · exact B1172351
  · exact B1172355
  · exact B1172359
  · exact B1172363
  · exact B1172367
  · exact B1172371
  · exact B1172375
  · exact B1172379
  · exact B1172383
  · exact B1172387
  · exact B1172391
  · exact B1172395
  · exact B1172399

theorem solution (m : ℕ) (hlo : 1170402 ≤ m) (hhi : m ≤ 1172402) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 292600 ≤ j := by omega
    have hj2 : j ≤ 293099 := by omega
    have hb : Blo 1170402 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
