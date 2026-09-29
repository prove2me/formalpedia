-- Prove2me | solution 1 for syracuse_descends_range_1285961_1287961
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:21.282914+00:00
-- url     : https://prove2.me/submissions/d79d1610-365f-40ca-a6c3-12c90c1b6615

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


theorem B2170901 : Blo 1285961 2170901 := bbase (se 6 (by rfl) ⟨50880, by rfl⟩ : syracuseStep 2170901 = 101761) (by norm_num)
theorem B2089093 : Blo 1285961 2089093 := bbase (se 4 (by rfl) ⟨195852, by rfl⟩ : syracuseStep 2089093 = 391705) (by norm_num)
theorem B2171029 : Blo 1285961 2171029 := bbase (se 6 (by rfl) ⟨50883, by rfl⟩ : syracuseStep 2171029 = 101767) (by norm_num)
theorem B21979349 : Blo 1285961 21979349 := bbase (se 7 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 21979349 = 515141) (by norm_num)
theorem B2171117 : Blo 1285961 2171117 := bbase (se 3 (by rfl) ⟨407084, by rfl⟩ : syracuseStep 2171117 = 814169) (by norm_num)
theorem B6512885 : Blo 1285961 6512885 := bbase (se 5 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 6512885 = 610583) (by norm_num)
theorem B6955253 : Blo 1285961 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B4342085 : Blo 1285961 4342085 := bbase (se 4 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 4342085 = 814141) (by norm_num)
theorem B35225941 : Blo 1285961 35225941 := bbase (se 10 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 35225941 = 103201) (by norm_num)
theorem B2441573 : Blo 1285961 2441573 := bbase (se 4 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 2441573 = 457795) (by norm_num)
theorem B2171245 : Blo 1285961 2171245 := bbase (se 3 (by rfl) ⟨407108, by rfl⟩ : syracuseStep 2171245 = 814217) (by norm_num)
theorem B2171333 : Blo 1285961 2171333 := bbase (se 4 (by rfl) ⟨203562, by rfl⟩ : syracuseStep 2171333 = 407125) (by norm_num)
theorem B4882949 : Blo 1285961 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B2318885 : Blo 1285961 2318885 := bbase (se 4 (by rfl) ⟨217395, by rfl⟩ : syracuseStep 2318885 = 434791) (by norm_num)
theorem B1696297 : Blo 1285961 1696297 := bbase (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) (by norm_num)
theorem B3662405 : Blo 1285961 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B2171461 : Blo 1285961 2171461 := bbase (se 4 (by rfl) ⟨203574, by rfl⟩ : syracuseStep 2171461 = 407149) (by norm_num)
theorem B10429013 : Blo 1285961 10429013 := bbase (se 8 (by rfl) ⟨61107, by rfl⟩ : syracuseStep 10429013 = 122215) (by norm_num)
theorem B2171549 : Blo 1285961 2171549 := bbase (se 3 (by rfl) ⟨407165, by rfl⟩ : syracuseStep 2171549 = 814331) (by norm_num)
theorem B4342517 : Blo 1285961 4342517 := bbase (se 5 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 4342517 = 407111) (by norm_num)
theorem B2171677 : Blo 1285961 2171677 := bbase (se 3 (by rfl) ⟨407189, by rfl⟩ : syracuseStep 2171677 = 814379) (by norm_num)
theorem B4883237 : Blo 1285961 4883237 := bbase (se 4 (by rfl) ⟨457803, by rfl⟩ : syracuseStep 4883237 = 915607) (by norm_num)
theorem B2171765 : Blo 1285961 2171765 := bbase (se 5 (by rfl) ⟨101801, by rfl⟩ : syracuseStep 2171765 = 203603) (by norm_num)
theorem B11740085 : Blo 1285961 11740085 := bbase (se 5 (by rfl) ⟨550316, by rfl⟩ : syracuseStep 11740085 = 1100633) (by norm_num)
theorem B2171893 : Blo 1285961 2171893 := bbase (se 5 (by rfl) ⟨101807, by rfl⟩ : syracuseStep 2171893 = 203615) (by norm_num)
theorem B2171981 : Blo 1285961 2171981 := bbase (se 3 (by rfl) ⟨407246, by rfl⟩ : syracuseStep 2171981 = 814493) (by norm_num)
theorem B2442325 : Blo 1285961 2442325 := bbase (se 8 (by rfl) ⟨14310, by rfl⟩ : syracuseStep 2442325 = 28621) (by norm_num)
theorem B4342949 : Blo 1285961 4342949 := bbase (se 4 (by rfl) ⟨407151, by rfl⟩ : syracuseStep 4342949 = 814303) (by norm_num)
theorem B2172109 : Blo 1285961 2172109 := bbase (se 3 (by rfl) ⟨407270, by rfl⟩ : syracuseStep 2172109 = 814541) (by norm_num)
theorem B2442469 : Blo 1285961 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B2475301 : Blo 1285961 2475301 := bbase (se 4 (by rfl) ⟨232059, by rfl⟩ : syracuseStep 2475301 = 464119) (by norm_num)
theorem B2172197 : Blo 1285961 2172197 := bbase (se 4 (by rfl) ⟨203643, by rfl⟩ : syracuseStep 2172197 = 407287) (by norm_num)
theorem B3663157 : Blo 1285961 3663157 := bbase (se 5 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 3663157 = 343421) (by norm_num)
theorem B2442629 : Blo 1285961 2442629 := bbase (se 4 (by rfl) ⟨228996, by rfl⟩ : syracuseStep 2442629 = 457993) (by norm_num)
theorem B2172325 : Blo 1285961 2172325 := bbase (se 4 (by rfl) ⟨203655, by rfl⟩ : syracuseStep 2172325 = 407311) (by norm_num)
theorem B1467821 : Blo 1285961 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B1304057 : Blo 1285961 1304057 := bbase (se 2 (by rfl) ⟨489021, by rfl⟩ : syracuseStep 1304057 = 978043) (by norm_num)
theorem B2172413 : Blo 1285961 2172413 := bbase (se 3 (by rfl) ⟨407327, by rfl⟩ : syracuseStep 2172413 = 814655) (by norm_num)
theorem B6514181 : Blo 1285961 6514181 := bbase (se 4 (by rfl) ⟨610704, by rfl⟩ : syracuseStep 6514181 = 1221409) (by norm_num)
theorem B2442773 : Blo 1285961 2442773 := bbase (se 6 (by rfl) ⟨57252, by rfl⟩ : syracuseStep 2442773 = 114505) (by norm_num)
theorem B3712549 : Blo 1285961 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B4343381 : Blo 1285961 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B6186613 : Blo 1285961 6186613 := bbase (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) (by norm_num)
theorem B2172541 : Blo 1285961 2172541 := bbase (se 3 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 2172541 = 814703) (by norm_num)
theorem B2893445 : Blo 1285961 2893445 := bbase (se 4 (by rfl) ⟨271260, by rfl⟩ : syracuseStep 2893445 = 542521) (by norm_num)
theorem B4122245 : Blo 1285961 4122245 := bbase (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) (by norm_num)
theorem B2893517 : Blo 1285961 2893517 := bbase (se 3 (by rfl) ⟨542534, by rfl⟩ : syracuseStep 2893517 = 1085069) (by norm_num)
theorem B2172629 : Blo 1285961 2172629 := bbase (se 7 (by rfl) ⟨25460, by rfl⟩ : syracuseStep 2172629 = 50921) (by norm_num)
theorem B5498597 : Blo 1285961 5498597 := bbase (se 4 (by rfl) ⟨515493, by rfl⟩ : syracuseStep 5498597 = 1030987) (by norm_num)
theorem B8922869 : Blo 1285961 8922869 := bbase (se 5 (by rfl) ⟨418259, by rfl⟩ : syracuseStep 8922869 = 836519) (by norm_num)
theorem B2893589 : Blo 1285961 2893589 := bbase (se 6 (by rfl) ⟨67818, by rfl⟩ : syracuseStep 2893589 = 135637) (by norm_num)
theorem B2443061 : Blo 1285961 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B1304405 : Blo 1285961 1304405 := bbase (se 9 (by rfl) ⟨3821, by rfl⟩ : syracuseStep 1304405 = 7643) (by norm_num)
theorem B2172757 : Blo 1285961 2172757 := bbase (se 9 (by rfl) ⟨6365, by rfl⟩ : syracuseStep 2172757 = 12731) (by norm_num)
theorem B2893661 : Blo 1285961 2893661 := bbase (se 3 (by rfl) ⟨542561, by rfl⟩ : syracuseStep 2893661 = 1085123) (by norm_num)
theorem B20875157 : Blo 1285961 20875157 := bbase (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) (by norm_num)
theorem B2893733 : Blo 1285961 2893733 := bbase (se 4 (by rfl) ⟨271287, by rfl⟩ : syracuseStep 2893733 = 542575) (by norm_num)
theorem B2172845 : Blo 1285961 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B4884421 : Blo 1285961 4884421 := bbase (se 4 (by rfl) ⟨457914, by rfl⟩ : syracuseStep 4884421 = 915829) (by norm_num)
theorem B2443213 : Blo 1285961 2443213 := bbase (se 3 (by rfl) ⟨458102, by rfl⟩ : syracuseStep 2443213 = 916205) (by norm_num)
theorem B16484309 : Blo 1285961 16484309 := bbase (se 7 (by rfl) ⟨193175, by rfl⟩ : syracuseStep 16484309 = 386351) (by norm_num)
theorem B5498837 : Blo 1285961 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B2893805 : Blo 1285961 2893805 := bbase (se 3 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 2893805 = 1085177) (by norm_num)
theorem B1468405 : Blo 1285961 1468405 := bbase (se 5 (by rfl) ⟨68831, by rfl⟩ : syracuseStep 1468405 = 137663) (by norm_num)
theorem B4343813 : Blo 1285961 4343813 := bbase (se 4 (by rfl) ⟨407232, by rfl⟩ : syracuseStep 4343813 = 814465) (by norm_num)
theorem B2172973 : Blo 1285961 2172973 := bbase (se 3 (by rfl) ⟨407432, by rfl⟩ : syracuseStep 2172973 = 814865) (by norm_num)
theorem B2893877 : Blo 1285961 2893877 := bbase (se 5 (by rfl) ⟨135650, by rfl⟩ : syracuseStep 2893877 = 271301) (by norm_num)
theorem B1304633 : Blo 1285961 1304633 := bbase (se 2 (by rfl) ⟨489237, by rfl⟩ : syracuseStep 1304633 = 978475) (by norm_num)
theorem B2893949 : Blo 1285961 2893949 := bbase (se 3 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 2893949 = 1085231) (by norm_num)
theorem B2173061 : Blo 1285961 2173061 := bbase (se 4 (by rfl) ⟨203724, by rfl⟩ : syracuseStep 2173061 = 407449) (by norm_num)
theorem B2746565 : Blo 1285961 2746565 := bbase (se 4 (by rfl) ⟨257490, by rfl⟩ : syracuseStep 2746565 = 514981) (by norm_num)
theorem B2894021 : Blo 1285961 2894021 := bbase (se 4 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 2894021 = 542629) (by norm_num)
theorem B5867765 : Blo 1285961 5867765 := bbase (se 5 (by rfl) ⟨275051, by rfl⟩ : syracuseStep 5867765 = 550103) (by norm_num)
theorem B4884725 : Blo 1285961 4884725 := bbase (se 5 (by rfl) ⟨228971, by rfl⟩ : syracuseStep 4884725 = 457943) (by norm_num)
theorem B2443517 : Blo 1285961 2443517 := bbase (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) (by norm_num)
theorem B2173189 : Blo 1285961 2173189 := bbase (se 4 (by rfl) ⟨203736, by rfl⟩ : syracuseStep 2173189 = 407473) (by norm_num)
theorem B2894093 : Blo 1285961 2894093 := bbase (se 3 (by rfl) ⟨542642, by rfl⟩ : syracuseStep 2894093 = 1085285) (by norm_num)
theorem B2746685 : Blo 1285961 2746685 := bbase (se 3 (by rfl) ⟨515003, by rfl⟩ : syracuseStep 2746685 = 1030007) (by norm_num)
theorem B2894165 : Blo 1285961 2894165 := bbase (se 10 (by rfl) ⟨4239, by rfl⟩ : syracuseStep 2894165 = 8479) (by norm_num)
theorem B2173277 : Blo 1285961 2173277 := bbase (se 3 (by rfl) ⟨407489, by rfl⟩ : syracuseStep 2173277 = 814979) (by norm_num)
theorem B2894237 : Blo 1285961 2894237 := bbase (se 3 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 2894237 = 1085339) (by norm_num)
theorem B2935205 : Blo 1285961 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B4344245 : Blo 1285961 4344245 := bbase (se 5 (by rfl) ⟨203636, by rfl⟩ : syracuseStep 4344245 = 407273) (by norm_num)
theorem B2173405 : Blo 1285961 2173405 := bbase (se 3 (by rfl) ⟨407513, by rfl⟩ : syracuseStep 2173405 = 815027) (by norm_num)
theorem B2894309 : Blo 1285961 2894309 := bbase (se 4 (by rfl) ⟨271341, by rfl⟩ : syracuseStep 2894309 = 542683) (by norm_num)
theorem B1739293 : Blo 1285961 1739293 := bbase (se 3 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 1739293 = 652235) (by norm_num)
theorem B2894381 : Blo 1285961 2894381 := bbase (se 3 (by rfl) ⟨542696, by rfl⟩ : syracuseStep 2894381 = 1085393) (by norm_num)
theorem B2787901 : Blo 1285961 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B4639301 : Blo 1285961 4639301 := bbase (se 4 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 4639301 = 869869) (by norm_num)
theorem B2894453 : Blo 1285961 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B7531157 : Blo 1285961 7531157 := bbase (se 6 (by rfl) ⟨176511, by rfl⟩ : syracuseStep 7531157 = 353023) (by norm_num)
theorem B2894525 : Blo 1285961 2894525 := bbase (se 3 (by rfl) ⟨542723, by rfl⟩ : syracuseStep 2894525 = 1085447) (by norm_num)
theorem B4401877 : Blo 1285961 4401877 := bbase (se 7 (by rfl) ⟨51584, by rfl⟩ : syracuseStep 4401877 = 103169) (by norm_num)
theorem B2894597 : Blo 1285961 2894597 := bbase (se 4 (by rfl) ⟨271368, by rfl⟩ : syracuseStep 2894597 = 542737) (by norm_num)
theorem B6515477 : Blo 1285961 6515477 := bbase (se 6 (by rfl) ⟨152706, by rfl⟩ : syracuseStep 6515477 = 305413) (by norm_num)
theorem B5221189 : Blo 1285961 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B2894669 : Blo 1285961 2894669 := bbase (se 3 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 2894669 = 1085501) (by norm_num)
theorem B4344677 : Blo 1285961 4344677 := bbase (se 4 (by rfl) ⟨407313, by rfl⟩ : syracuseStep 4344677 = 814627) (by norm_num)
theorem B2894741 : Blo 1285961 2894741 := bbase (se 6 (by rfl) ⟨67845, by rfl⟩ : syracuseStep 2894741 = 135691) (by norm_num)
theorem B5721013 : Blo 1285961 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B2747317 : Blo 1285961 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B3091405 : Blo 1285961 3091405 := bbase (se 3 (by rfl) ⟨579638, by rfl⟩ : syracuseStep 3091405 = 1159277) (by norm_num)
theorem B2894813 : Blo 1285961 2894813 := bbase (se 3 (by rfl) ⟨542777, by rfl⟩ : syracuseStep 2894813 = 1085555) (by norm_num)
theorem B2444269 : Blo 1285961 2444269 := bbase (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) (by norm_num)
theorem B2894885 : Blo 1285961 2894885 := bbase (se 4 (by rfl) ⟨271395, by rfl⟩ : syracuseStep 2894885 = 542791) (by norm_num)
theorem B3255349 : Blo 1285961 3255349 := bbase (se 5 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 3255349 = 305189) (by norm_num)
theorem B2894957 : Blo 1285961 2894957 := bbase (se 3 (by rfl) ⟨542804, by rfl⟩ : syracuseStep 2894957 = 1085609) (by norm_num)
theorem B2444413 : Blo 1285961 2444413 := bbase (se 3 (by rfl) ⟨458327, by rfl⟩ : syracuseStep 2444413 = 916655) (by norm_num)
theorem B3255461 : Blo 1285961 3255461 := bbase (se 4 (by rfl) ⟨305199, by rfl⟩ : syracuseStep 3255461 = 610399) (by norm_num)
theorem B2895029 : Blo 1285961 2895029 := bbase (se 5 (by rfl) ⟨135704, by rfl⟩ : syracuseStep 2895029 = 271409) (by norm_num)
theorem B1739981 : Blo 1285961 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B2608357 : Blo 1285961 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B2895101 : Blo 1285961 2895101 := bbase (se 3 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 2895101 = 1085663) (by norm_num)
theorem B4345109 : Blo 1285961 4345109 := bbase (se 6 (by rfl) ⟨101838, by rfl⟩ : syracuseStep 4345109 = 203677) (by norm_num)
theorem B2444573 : Blo 1285961 2444573 := bbase (se 3 (by rfl) ⟨458357, by rfl⟩ : syracuseStep 2444573 = 916715) (by norm_num)
theorem B2895173 : Blo 1285961 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B3255653 : Blo 1285961 3255653 := bbase (se 4 (by rfl) ⟨305217, by rfl⟩ : syracuseStep 3255653 = 610435) (by norm_num)
theorem B2936189 : Blo 1285961 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B2895245 : Blo 1285961 2895245 := bbase (se 3 (by rfl) ⟨542858, by rfl⟩ : syracuseStep 2895245 = 1085717) (by norm_num)
theorem B2444717 : Blo 1285961 2444717 := bbase (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) (by norm_num)
theorem B2895317 : Blo 1285961 2895317 := bbase (se 7 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 2895317 = 67859) (by norm_num)
theorem B2895389 : Blo 1285961 2895389 := bbase (se 3 (by rfl) ⟨542885, by rfl⟩ : syracuseStep 2895389 = 1085771) (by norm_num)
theorem B2895461 : Blo 1285961 2895461 := bbase (se 4 (by rfl) ⟨271449, by rfl⟩ : syracuseStep 2895461 = 542899) (by norm_num)
theorem B3092069 : Blo 1285961 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B2059949 : Blo 1285961 2059949 := bbase (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) (by norm_num)
theorem B2895533 : Blo 1285961 2895533 := bbase (se 3 (by rfl) ⟨542912, by rfl⟩ : syracuseStep 2895533 = 1085825) (by norm_num)
theorem B3255997 : Blo 1285961 3255997 := bbase (se 3 (by rfl) ⟨610499, by rfl⟩ : syracuseStep 3255997 = 1220999) (by norm_num)
theorem B4345541 : Blo 1285961 4345541 := bbase (se 4 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 4345541 = 814789) (by norm_num)
theorem B2445005 : Blo 1285961 2445005 := bbase (se 3 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 2445005 = 916877) (by norm_num)
theorem B2895605 : Blo 1285961 2895605 := bbase (se 5 (by rfl) ⟨135731, by rfl⟩ : syracuseStep 2895605 = 271463) (by norm_num)
theorem B1928957 : Blo 1285961 1928957 := bbase (se 3 (by rfl) ⟨361679, by rfl⟩ : syracuseStep 1928957 = 723359) (by norm_num)
theorem B1928981 : Blo 1285961 1928981 := bbase (se 6 (by rfl) ⟨45210, by rfl⟩ : syracuseStep 1928981 = 90421) (by norm_num)
theorem B1929005 : Blo 1285961 1929005 := bbase (se 3 (by rfl) ⟨361688, by rfl⟩ : syracuseStep 1929005 = 723377) (by norm_num)
theorem B3256109 : Blo 1285961 3256109 := bbase (se 3 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 3256109 = 1221041) (by norm_num)
theorem B2748205 : Blo 1285961 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B2895677 : Blo 1285961 2895677 := bbase (se 3 (by rfl) ⟨542939, by rfl⟩ : syracuseStep 2895677 = 1085879) (by norm_num)
theorem B1929029 : Blo 1285961 1929029 := bbase (se 4 (by rfl) ⟨180846, by rfl⟩ : syracuseStep 1929029 = 361693) (by norm_num)
theorem B1740613 : Blo 1285961 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B18550613 : Blo 1285961 18550613 := bbase (se 9 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 18550613 = 108695) (by norm_num)
theorem B1929053 : Blo 1285961 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B1929077 : Blo 1285961 1929077 := bbase (se 5 (by rfl) ⟨90425, by rfl⟩ : syracuseStep 1929077 = 180851) (by norm_num)
theorem B2060149 : Blo 1285961 2060149 := bbase (se 5 (by rfl) ⟨96569, by rfl⟩ : syracuseStep 2060149 = 193139) (by norm_num)
theorem B2895749 : Blo 1285961 2895749 := bbase (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) (by norm_num)
theorem B1740677 : Blo 1285961 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B1929101 : Blo 1285961 1929101 := bbase (se 3 (by rfl) ⟨361706, by rfl⟩ : syracuseStep 1929101 = 723413) (by norm_num)
theorem B1929125 : Blo 1285961 1929125 := bbase (se 4 (by rfl) ⟨180855, by rfl⟩ : syracuseStep 1929125 = 361711) (by norm_num)
theorem B2748325 : Blo 1285961 2748325 := bbase (se 4 (by rfl) ⟨257655, by rfl⟩ : syracuseStep 2748325 = 515311) (by norm_num)
theorem B1929149 : Blo 1285961 1929149 := bbase (se 3 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 1929149 = 723431) (by norm_num)
theorem B1486793 : Blo 1285961 1486793 := bbase (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) (by norm_num)
theorem B2895821 : Blo 1285961 2895821 := bbase (se 3 (by rfl) ⟨542966, by rfl⟩ : syracuseStep 2895821 = 1085933) (by norm_num)
theorem B1929173 : Blo 1285961 1929173 := bbase (se 7 (by rfl) ⟨22607, by rfl⟩ : syracuseStep 1929173 = 45215) (by norm_num)
theorem B1929197 : Blo 1285961 1929197 := bbase (se 3 (by rfl) ⟨361724, by rfl⟩ : syracuseStep 1929197 = 723449) (by norm_num)
theorem B3256301 : Blo 1285961 3256301 := bbase (se 3 (by rfl) ⟨610556, by rfl⟩ : syracuseStep 3256301 = 1221113) (by norm_num)
theorem B2543605 : Blo 1285961 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B1929221 : Blo 1285961 1929221 := bbase (se 4 (by rfl) ⟨180864, by rfl⟩ : syracuseStep 1929221 = 361729) (by norm_num)
theorem B2895893 : Blo 1285961 2895893 := bbase (se 6 (by rfl) ⟨67872, by rfl⟩ : syracuseStep 2895893 = 135745) (by norm_num)
theorem B1929245 : Blo 1285961 1929245 := bbase (se 3 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 1929245 = 723467) (by norm_num)
theorem B6516773 : Blo 1285961 6516773 := bbase (se 4 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 6516773 = 1221895) (by norm_num)
theorem B1929269 : Blo 1285961 1929269 := bbase (se 5 (by rfl) ⟨90434, by rfl⟩ : syracuseStep 1929269 = 180869) (by norm_num)
theorem B1929293 : Blo 1285961 1929293 := bbase (se 3 (by rfl) ⟨361742, by rfl⟩ : syracuseStep 1929293 = 723485) (by norm_num)
theorem B3666005 : Blo 1285961 3666005 := bbase (se 8 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 3666005 = 42961) (by norm_num)
theorem B2895965 : Blo 1285961 2895965 := bbase (se 3 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 2895965 = 1085987) (by norm_num)
theorem B1929317 : Blo 1285961 1929317 := bbase (se 4 (by rfl) ⟨180873, by rfl⟩ : syracuseStep 1929317 = 361747) (by norm_num)
theorem B2060405 : Blo 1285961 2060405 := bbase (se 5 (by rfl) ⟨96581, by rfl⟩ : syracuseStep 2060405 = 193163) (by norm_num)
theorem B4345973 : Blo 1285961 4345973 := bbase (se 5 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 4345973 = 407435) (by norm_num)
theorem B1929341 : Blo 1285961 1929341 := bbase (se 3 (by rfl) ⟨361751, by rfl⟩ : syracuseStep 1929341 = 723503) (by norm_num)
theorem B2199701 : Blo 1285961 2199701 := bbase (se 6 (by rfl) ⟨51555, by rfl⟩ : syracuseStep 2199701 = 103111) (by norm_num)
theorem B1929365 : Blo 1285961 1929365 := bbase (se 6 (by rfl) ⟨45219, by rfl⟩ : syracuseStep 1929365 = 90439) (by norm_num)
theorem B2748581 : Blo 1285961 2748581 := bbase (se 4 (by rfl) ⟨257679, by rfl⟩ : syracuseStep 2748581 = 515359) (by norm_num)
theorem B2896037 : Blo 1285961 2896037 := bbase (se 4 (by rfl) ⟨271503, by rfl⟩ : syracuseStep 2896037 = 543007) (by norm_num)
theorem B1929389 : Blo 1285961 1929389 := bbase (se 3 (by rfl) ⟨361760, by rfl⟩ : syracuseStep 1929389 = 723521) (by norm_num)
theorem B1929413 : Blo 1285961 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B5501125 : Blo 1285961 5501125 := bbase (se 4 (by rfl) ⟨515730, by rfl⟩ : syracuseStep 5501125 = 1031461) (by norm_num)
theorem B18084053 : Blo 1285961 18084053 := bbase (se 7 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 18084053 = 423845) (by norm_num)
theorem B1323221 : Blo 1285961 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B1929437 : Blo 1285961 1929437 := bbase (se 3 (by rfl) ⟨361769, by rfl⟩ : syracuseStep 1929437 = 723539) (by norm_num)
theorem B2896109 : Blo 1285961 2896109 := bbase (se 3 (by rfl) ⟨543020, by rfl⟩ : syracuseStep 2896109 = 1086041) (by norm_num)
theorem B1929461 : Blo 1285961 1929461 := bbase (se 5 (by rfl) ⟨90443, by rfl⟩ : syracuseStep 1929461 = 180887) (by norm_num)
theorem B8589557 : Blo 1285961 8589557 := bbase (se 5 (by rfl) ⟨402635, by rfl⟩ : syracuseStep 8589557 = 805271) (by norm_num)
theorem B1929485 : Blo 1285961 1929485 := bbase (se 3 (by rfl) ⟨361778, by rfl⟩ : syracuseStep 1929485 = 723557) (by norm_num)
theorem B1929509 : Blo 1285961 1929509 := bbase (se 4 (by rfl) ⟨180891, by rfl⟩ : syracuseStep 1929509 = 361783) (by norm_num)
theorem B4886837 : Blo 1285961 4886837 := bbase (se 5 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 4886837 = 458141) (by norm_num)
theorem B2896181 : Blo 1285961 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B1929533 : Blo 1285961 1929533 := bbase (se 3 (by rfl) ⟨361787, by rfl⟩ : syracuseStep 1929533 = 723575) (by norm_num)
theorem B3256645 : Blo 1285961 3256645 := bbase (se 4 (by rfl) ⟨305310, by rfl⟩ : syracuseStep 3256645 = 610621) (by norm_num)
theorem B1929557 : Blo 1285961 1929557 := bbase (se 10 (by rfl) ⟨2826, by rfl⟩ : syracuseStep 1929557 = 5653) (by norm_num)
theorem B1929581 : Blo 1285961 1929581 := bbase (se 3 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 1929581 = 723593) (by norm_num)
theorem B2896253 : Blo 1285961 2896253 := bbase (se 3 (by rfl) ⟨543047, by rfl⟩ : syracuseStep 2896253 = 1086095) (by norm_num)
theorem B1929605 : Blo 1285961 1929605 := bbase (se 4 (by rfl) ⟨180900, by rfl⟩ : syracuseStep 1929605 = 361801) (by norm_num)
theorem B4125077 : Blo 1285961 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B1929629 : Blo 1285961 1929629 := bbase (se 3 (by rfl) ⟨361805, by rfl⟩ : syracuseStep 1929629 = 723611) (by norm_num)
theorem B1929653 : Blo 1285961 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B3256757 : Blo 1285961 3256757 := bbase (se 5 (by rfl) ⟨152660, by rfl⟩ : syracuseStep 3256757 = 305321) (by norm_num)
theorem B3969461 : Blo 1285961 3969461 := bbase (se 5 (by rfl) ⟨186068, by rfl⟩ : syracuseStep 3969461 = 372137) (by norm_num)
theorem B2896325 : Blo 1285961 2896325 := bbase (se 4 (by rfl) ⟨271530, by rfl⟩ : syracuseStep 2896325 = 543061) (by norm_num)
theorem B1929677 : Blo 1285961 1929677 := bbase (se 3 (by rfl) ⟨361814, by rfl⟩ : syracuseStep 1929677 = 723629) (by norm_num)
theorem B1929701 : Blo 1285961 1929701 := bbase (se 4 (by rfl) ⟨180909, by rfl⟩ : syracuseStep 1929701 = 361819) (by norm_num)
theorem B1929725 : Blo 1285961 1929725 := bbase (se 3 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 1929725 = 723647) (by norm_num)
theorem B2896397 : Blo 1285961 2896397 := bbase (se 3 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 2896397 = 1086149) (by norm_num)
theorem B1929749 : Blo 1285961 1929749 := bbase (se 6 (by rfl) ⟨45228, by rfl⟩ : syracuseStep 1929749 = 90457) (by norm_num)
theorem B4346405 : Blo 1285961 4346405 := bbase (se 4 (by rfl) ⟨407475, by rfl⟩ : syracuseStep 4346405 = 814951) (by norm_num)
theorem B1929773 : Blo 1285961 1929773 := bbase (se 3 (by rfl) ⟨361832, by rfl⟩ : syracuseStep 1929773 = 723665) (by norm_num)
theorem B1929797 : Blo 1285961 1929797 := bbase (se 4 (by rfl) ⟨180918, by rfl⟩ : syracuseStep 1929797 = 361837) (by norm_num)
theorem B4887125 : Blo 1285961 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B2896469 : Blo 1285961 2896469 := bbase (se 8 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 2896469 = 33943) (by norm_num)
theorem B1929821 : Blo 1285961 1929821 := bbase (se 3 (by rfl) ⟨361841, by rfl⟩ : syracuseStep 1929821 = 723683) (by norm_num)
theorem B1929845 : Blo 1285961 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B3256949 : Blo 1285961 3256949 := bbase (se 5 (by rfl) ⟨152669, by rfl⟩ : syracuseStep 3256949 = 305339) (by norm_num)
theorem B1929869 : Blo 1285961 1929869 := bbase (se 3 (by rfl) ⟨361850, by rfl⟩ : syracuseStep 1929869 = 723701) (by norm_num)
theorem B2896541 : Blo 1285961 2896541 := bbase (se 3 (by rfl) ⟨543101, by rfl⟩ : syracuseStep 2896541 = 1086203) (by norm_num)
theorem B6181541 : Blo 1285961 6181541 := bbase (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) (by norm_num)
theorem B1929893 : Blo 1285961 1929893 := bbase (se 4 (by rfl) ⟨180927, by rfl⟩ : syracuseStep 1929893 = 361855) (by norm_num)
theorem B5870245 : Blo 1285961 5870245 := bbase (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) (by norm_num)
theorem B2200253 : Blo 1285961 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B1929917 : Blo 1285961 1929917 := bbase (se 3 (by rfl) ⟨361859, by rfl⟩ : syracuseStep 1929917 = 723719) (by norm_num)
theorem B1929941 : Blo 1285961 1929941 := bbase (se 7 (by rfl) ⟨22616, by rfl⟩ : syracuseStep 1929941 = 45233) (by norm_num)
theorem B2896613 : Blo 1285961 2896613 := bbase (se 4 (by rfl) ⟨271557, by rfl⟩ : syracuseStep 2896613 = 543115) (by norm_num)
theorem B1651433 : Blo 1285961 1651433 := bbase (se 2 (by rfl) ⟨619287, by rfl⟩ : syracuseStep 1651433 = 1238575) (by norm_num)
theorem B1929965 : Blo 1285961 1929965 := bbase (se 3 (by rfl) ⟨361868, by rfl⟩ : syracuseStep 1929965 = 723737) (by norm_num)
theorem B3912437 : Blo 1285961 3912437 := bbase (se 5 (by rfl) ⟨183395, by rfl⟩ : syracuseStep 3912437 = 366791) (by norm_num)
theorem B7328501 : Blo 1285961 7328501 := bbase (se 5 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 7328501 = 687047) (by norm_num)
theorem B1929989 : Blo 1285961 1929989 := bbase (se 4 (by rfl) ⟨180936, by rfl⟩ : syracuseStep 1929989 = 361873) (by norm_num)
theorem B1930013 : Blo 1285961 1930013 := bbase (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) (by norm_num)
theorem B2896685 : Blo 1285961 2896685 := bbase (se 3 (by rfl) ⟨543128, by rfl⟩ : syracuseStep 2896685 = 1086257) (by norm_num)
theorem B1446709 : Blo 1285961 1446709 := bbase (se 5 (by rfl) ⟨67814, by rfl⟩ : syracuseStep 1446709 = 135629) (by norm_num)
theorem B1930037 : Blo 1285961 1930037 := bbase (se 5 (by rfl) ⟨90470, by rfl⟩ : syracuseStep 1930037 = 180941) (by norm_num)
theorem B1930061 : Blo 1285961 1930061 := bbase (se 3 (by rfl) ⟨361886, by rfl⟩ : syracuseStep 1930061 = 723773) (by norm_num)
theorem B1446745 : Blo 1285961 1446745 := bbase (se 2 (by rfl) ⟨542529, by rfl⟩ : syracuseStep 1446745 = 1085059) (by norm_num)
theorem B1930085 : Blo 1285961 1930085 := bbase (se 4 (by rfl) ⟨180945, by rfl⟩ : syracuseStep 1930085 = 361891) (by norm_num)
theorem B2896757 : Blo 1285961 2896757 := bbase (se 5 (by rfl) ⟨135785, by rfl⟩ : syracuseStep 2896757 = 271571) (by norm_num)
theorem B1446781 : Blo 1285961 1446781 := bbase (se 3 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 1446781 = 542543) (by norm_num)
theorem B1930109 : Blo 1285961 1930109 := bbase (se 3 (by rfl) ⟨361895, by rfl⟩ : syracuseStep 1930109 = 723791) (by norm_num)
theorem B1545097 : Blo 1285961 1545097 := bbase (se 2 (by rfl) ⟨579411, by rfl⟩ : syracuseStep 1545097 = 1158823) (by norm_num)
theorem B1930133 : Blo 1285961 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B1446817 : Blo 1285961 1446817 := bbase (se 2 (by rfl) ⟨542556, by rfl⟩ : syracuseStep 1446817 = 1085113) (by norm_num)
theorem B5215141 : Blo 1285961 5215141 := bbase (se 4 (by rfl) ⟨488919, by rfl⟩ : syracuseStep 5215141 = 977839) (by norm_num)
theorem B1930157 : Blo 1285961 1930157 := bbase (se 3 (by rfl) ⟨361904, by rfl⟩ : syracuseStep 1930157 = 723809) (by norm_num)
theorem B2896829 : Blo 1285961 2896829 := bbase (se 3 (by rfl) ⟨543155, by rfl⟩ : syracuseStep 2896829 = 1086311) (by norm_num)
theorem B1446853 : Blo 1285961 1446853 := bbase (se 4 (by rfl) ⟨135642, by rfl⟩ : syracuseStep 1446853 = 271285) (by norm_num)
theorem B6181829 : Blo 1285961 6181829 := bbase (se 4 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 6181829 = 1159093) (by norm_num)
theorem B1930181 : Blo 1285961 1930181 := bbase (se 4 (by rfl) ⟨180954, by rfl⟩ : syracuseStep 1930181 = 361909) (by norm_num)
theorem B3257293 : Blo 1285961 3257293 := bbase (se 3 (by rfl) ⟨610742, by rfl⟩ : syracuseStep 3257293 = 1221485) (by norm_num)
theorem B3093461 : Blo 1285961 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B4641749 : Blo 1285961 4641749 := bbase (se 7 (by rfl) ⟨54395, by rfl⟩ : syracuseStep 4641749 = 108791) (by norm_num)
theorem B4346837 : Blo 1285961 4346837 := bbase (se 7 (by rfl) ⟨50939, by rfl⟩ : syracuseStep 4346837 = 101879) (by norm_num)
theorem B1930205 : Blo 1285961 1930205 := bbase (se 3 (by rfl) ⟨361913, by rfl⟩ : syracuseStep 1930205 = 723827) (by norm_num)
theorem B1831909 : Blo 1285961 1831909 := bbase (se 4 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 1831909 = 343483) (by norm_num)
theorem B1446889 : Blo 1285961 1446889 := bbase (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) (by norm_num)
theorem B1545193 : Blo 1285961 1545193 := bbase (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) (by norm_num)
theorem B1930229 : Blo 1285961 1930229 := bbase (se 5 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 1930229 = 180959) (by norm_num)
theorem B2896901 : Blo 1285961 2896901 := bbase (se 4 (by rfl) ⟨271584, by rfl⟩ : syracuseStep 2896901 = 543169) (by norm_num)
theorem B2642957 : Blo 1285961 2642957 := bbase (se 3 (by rfl) ⟨495554, by rfl⟩ : syracuseStep 2642957 = 991109) (by norm_num)
theorem B1446925 : Blo 1285961 1446925 := bbase (se 3 (by rfl) ⟨271298, by rfl⟩ : syracuseStep 1446925 = 542597) (by norm_num)
theorem B1930253 : Blo 1285961 1930253 := bbase (se 3 (by rfl) ⟨361922, by rfl⟩ : syracuseStep 1930253 = 723845) (by norm_num)
theorem B1545241 : Blo 1285961 1545241 := bbase (se 2 (by rfl) ⟨579465, by rfl⟩ : syracuseStep 1545241 = 1158931) (by norm_num)
theorem B2749469 : Blo 1285961 2749469 := bbase (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) (by norm_num)
theorem B1930277 : Blo 1285961 1930277 := bbase (se 4 (by rfl) ⟨180963, by rfl⟩ : syracuseStep 1930277 = 361927) (by norm_num)
theorem B1446961 : Blo 1285961 1446961 := bbase (se 2 (by rfl) ⟨542610, by rfl⟩ : syracuseStep 1446961 = 1085221) (by norm_num)
theorem B3093557 : Blo 1285961 3093557 := bbase (se 5 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 3093557 = 290021) (by norm_num)
theorem B1930301 : Blo 1285961 1930301 := bbase (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) (by norm_num)
theorem B3257405 : Blo 1285961 3257405 := bbase (se 3 (by rfl) ⟨610763, by rfl⟩ : syracuseStep 3257405 = 1221527) (by norm_num)
theorem B2896973 : Blo 1285961 2896973 := bbase (se 3 (by rfl) ⟨543182, by rfl⟩ : syracuseStep 2896973 = 1086365) (by norm_num)
theorem B1446997 : Blo 1285961 1446997 := bbase (se 8 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 1446997 = 16957) (by norm_num)
theorem B1930325 : Blo 1285961 1930325 := bbase (se 8 (by rfl) ⟨11310, by rfl⟩ : syracuseStep 1930325 = 22621) (by norm_num)
theorem B8246357 : Blo 1285961 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B1930349 : Blo 1285961 1930349 := bbase (se 3 (by rfl) ⟨361940, by rfl⟩ : syracuseStep 1930349 = 723881) (by norm_num)
theorem B1447033 : Blo 1285961 1447033 := bbase (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) (by norm_num)
theorem B1930373 : Blo 1285961 1930373 := bbase (se 4 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 1930373 = 361945) (by norm_num)
theorem B2897045 : Blo 1285961 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B1447069 : Blo 1285961 1447069 := bbase (se 3 (by rfl) ⟨271325, by rfl⟩ : syracuseStep 1447069 = 542651) (by norm_num)
theorem B1930397 : Blo 1285961 1930397 := bbase (se 3 (by rfl) ⟨361949, by rfl⟩ : syracuseStep 1930397 = 723899) (by norm_num)
theorem B1930421 : Blo 1285961 1930421 := bbase (se 5 (by rfl) ⟨90488, by rfl⟩ : syracuseStep 1930421 = 180977) (by norm_num)
theorem B1447105 : Blo 1285961 1447105 := bbase (se 2 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 1447105 = 1085329) (by norm_num)
theorem B1930445 : Blo 1285961 1930445 := bbase (se 3 (by rfl) ⟨361958, by rfl⟩ : syracuseStep 1930445 = 723917) (by norm_num)
theorem B2061533 : Blo 1285961 2061533 := bbase (se 3 (by rfl) ⟨386537, by rfl⟩ : syracuseStep 2061533 = 773075) (by norm_num)
theorem B2897117 : Blo 1285961 2897117 := bbase (se 3 (by rfl) ⟨543209, by rfl⟩ : syracuseStep 2897117 = 1086419) (by norm_num)
theorem B1447141 : Blo 1285961 1447141 := bbase (se 4 (by rfl) ⟨135669, by rfl⟩ : syracuseStep 1447141 = 271339) (by norm_num)
theorem B1930469 : Blo 1285961 1930469 := bbase (se 4 (by rfl) ⟨180981, by rfl⟩ : syracuseStep 1930469 = 361963) (by norm_num)
theorem B3667189 : Blo 1285961 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B3257597 : Blo 1285961 3257597 := bbase (se 3 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 3257597 = 1221599) (by norm_num)
theorem B1930493 : Blo 1285961 1930493 := bbase (se 3 (by rfl) ⟨361967, by rfl⟩ : syracuseStep 1930493 = 723935) (by norm_num)
theorem B1447177 : Blo 1285961 1447177 := bbase (se 2 (by rfl) ⟨542691, by rfl⟩ : syracuseStep 1447177 = 1085383) (by norm_num)
theorem B2749709 : Blo 1285961 2749709 := bbase (se 3 (by rfl) ⟨515570, by rfl⟩ : syracuseStep 2749709 = 1031141) (by norm_num)
theorem B1930517 : Blo 1285961 1930517 := bbase (se 6 (by rfl) ⟨45246, by rfl⟩ : syracuseStep 1930517 = 90493) (by norm_num)
theorem B4125973 : Blo 1285961 4125973 := bbase (se 6 (by rfl) ⟨96702, by rfl⟩ : syracuseStep 4125973 = 193405) (by norm_num)
theorem B2897189 : Blo 1285961 2897189 := bbase (se 4 (by rfl) ⟨271611, by rfl⟩ : syracuseStep 2897189 = 543223) (by norm_num)
theorem B1447213 : Blo 1285961 1447213 := bbase (se 3 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 1447213 = 542705) (by norm_num)
theorem B1930541 : Blo 1285961 1930541 := bbase (se 3 (by rfl) ⟨361976, by rfl⟩ : syracuseStep 1930541 = 723953) (by norm_num)
theorem B6518069 : Blo 1285961 6518069 := bbase (se 5 (by rfl) ⟨305534, by rfl⟩ : syracuseStep 6518069 = 611069) (by norm_num)
theorem B1930565 : Blo 1285961 1930565 := bbase (se 4 (by rfl) ⟨180990, by rfl⟩ : syracuseStep 1930565 = 361981) (by norm_num)
theorem B1447249 : Blo 1285961 1447249 := bbase (se 2 (by rfl) ⟨542718, by rfl⟩ : syracuseStep 1447249 = 1085437) (by norm_num)
theorem B1930589 : Blo 1285961 1930589 := bbase (se 3 (by rfl) ⟨361985, by rfl⟩ : syracuseStep 1930589 = 723971) (by norm_num)
theorem B2897261 : Blo 1285961 2897261 := bbase (se 3 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 2897261 = 1086473) (by norm_num)
theorem B1447285 : Blo 1285961 1447285 := bbase (se 5 (by rfl) ⟨67841, by rfl⟩ : syracuseStep 1447285 = 135683) (by norm_num)
theorem B1930613 : Blo 1285961 1930613 := bbase (se 5 (by rfl) ⟨90497, by rfl⟩ : syracuseStep 1930613 = 180995) (by norm_num)
theorem B1930637 : Blo 1285961 1930637 := bbase (se 3 (by rfl) ⟨361994, by rfl⟩ : syracuseStep 1930637 = 723989) (by norm_num)
theorem B3667349 : Blo 1285961 3667349 := bbase (se 6 (by rfl) ⟨85953, by rfl⟩ : syracuseStep 3667349 = 171907) (by norm_num)
theorem B1447321 : Blo 1285961 1447321 := bbase (se 2 (by rfl) ⟨542745, by rfl⟩ : syracuseStep 1447321 = 1085491) (by norm_num)
theorem B1627553 : Blo 1285961 1627553 := bbase (se 2 (by rfl) ⟨610332, by rfl⟩ : syracuseStep 1627553 = 1220665) (by norm_num)
theorem B1930661 : Blo 1285961 1930661 := bbase (se 4 (by rfl) ⟨180999, by rfl⟩ : syracuseStep 1930661 = 361999) (by norm_num)
theorem B3716533 : Blo 1285961 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B2897333 : Blo 1285961 2897333 := bbase (se 5 (by rfl) ⟨135812, by rfl⟩ : syracuseStep 2897333 = 271625) (by norm_num)
theorem B1447357 : Blo 1285961 1447357 := bbase (se 3 (by rfl) ⟨271379, by rfl⟩ : syracuseStep 1447357 = 542759) (by norm_num)
theorem B1930685 : Blo 1285961 1930685 := bbase (se 3 (by rfl) ⟨362003, by rfl⟩ : syracuseStep 1930685 = 724007) (by norm_num)
theorem B1373641 : Blo 1285961 1373641 := bbase (se 2 (by rfl) ⟨515115, by rfl⟩ : syracuseStep 1373641 = 1030231) (by norm_num)
theorem B1930709 : Blo 1285961 1930709 := bbase (se 7 (by rfl) ⟨22625, by rfl⟩ : syracuseStep 1930709 = 45251) (by norm_num)
theorem B1627609 : Blo 1285961 1627609 := bbase (se 2 (by rfl) ⟨610353, by rfl⟩ : syracuseStep 1627609 = 1220707) (by norm_num)
theorem B1447393 : Blo 1285961 1447393 := bbase (se 2 (by rfl) ⟨542772, by rfl⟩ : syracuseStep 1447393 = 1085545) (by norm_num)
theorem B1930733 : Blo 1285961 1930733 := bbase (se 3 (by rfl) ⟨362012, by rfl⟩ : syracuseStep 1930733 = 724025) (by norm_num)
theorem B12367349 : Blo 1285961 12367349 := bbase (se 5 (by rfl) ⟨579719, by rfl⟩ : syracuseStep 12367349 = 1159439) (by norm_num)
theorem B2897405 : Blo 1285961 2897405 := bbase (se 3 (by rfl) ⟨543263, by rfl⟩ : syracuseStep 2897405 = 1086527) (by norm_num)
theorem B1447429 : Blo 1285961 1447429 := bbase (se 4 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 1447429 = 271393) (by norm_num)
theorem B1930757 : Blo 1285961 1930757 := bbase (se 4 (by rfl) ⟨181008, by rfl⟩ : syracuseStep 1930757 = 362017) (by norm_num)
theorem B1930781 : Blo 1285961 1930781 := bbase (se 3 (by rfl) ⟨362021, by rfl⟩ : syracuseStep 1930781 = 724043) (by norm_num)
theorem B1447465 : Blo 1285961 1447465 := bbase (se 2 (by rfl) ⟨542799, by rfl⟩ : syracuseStep 1447465 = 1085599) (by norm_num)
theorem B1832501 : Blo 1285961 1832501 := bbase (se 5 (by rfl) ⟨85898, by rfl⟩ : syracuseStep 1832501 = 171797) (by norm_num)
theorem B1930805 : Blo 1285961 1930805 := bbase (se 5 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 1930805 = 181013) (by norm_num)
theorem B1627705 : Blo 1285961 1627705 := bbase (se 2 (by rfl) ⟨610389, by rfl⟩ : syracuseStep 1627705 = 1220779) (by norm_num)
theorem B1373761 : Blo 1285961 1373761 := bbase (se 2 (by rfl) ⟨515160, by rfl⟩ : syracuseStep 1373761 = 1030321) (by norm_num)
theorem B2897477 : Blo 1285961 2897477 := bbase (se 4 (by rfl) ⟨271638, by rfl⟩ : syracuseStep 2897477 = 543277) (by norm_num)
theorem B1447501 : Blo 1285961 1447501 := bbase (se 3 (by rfl) ⟨271406, by rfl⟩ : syracuseStep 1447501 = 542813) (by norm_num)
theorem B1930829 : Blo 1285961 1930829 := bbase (se 3 (by rfl) ⟨362030, by rfl⟩ : syracuseStep 1930829 = 724061) (by norm_num)
theorem B3257941 : Blo 1285961 3257941 := bbase (se 8 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 3257941 = 38179) (by norm_num)
theorem B1930853 : Blo 1285961 1930853 := bbase (se 4 (by rfl) ⟨181017, by rfl⟩ : syracuseStep 1930853 = 362035) (by norm_num)
theorem B1447537 : Blo 1285961 1447537 := bbase (se 2 (by rfl) ⟨542826, by rfl⟩ : syracuseStep 1447537 = 1085653) (by norm_num)
theorem B9778805 : Blo 1285961 9778805 := bbase (se 5 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 9778805 = 916763) (by norm_num)
theorem B1930877 : Blo 1285961 1930877 := bbase (se 3 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 1930877 = 724079) (by norm_num)
theorem B1832581 : Blo 1285961 1832581 := bbase (se 4 (by rfl) ⟨171804, by rfl⟩ : syracuseStep 1832581 = 343609) (by norm_num)
theorem B3667589 : Blo 1285961 3667589 := bbase (se 4 (by rfl) ⟨343836, by rfl⟩ : syracuseStep 3667589 = 687673) (by norm_num)
theorem B2897549 : Blo 1285961 2897549 := bbase (se 3 (by rfl) ⟨543290, by rfl⟩ : syracuseStep 2897549 = 1086581) (by norm_num)
theorem B1447573 : Blo 1285961 1447573 := bbase (se 6 (by rfl) ⟨33927, by rfl⟩ : syracuseStep 1447573 = 67855) (by norm_num)
theorem B1930901 : Blo 1285961 1930901 := bbase (se 6 (by rfl) ⟨45255, by rfl⟩ : syracuseStep 1930901 = 90511) (by norm_num)
theorem B1930925 : Blo 1285961 1930925 := bbase (se 3 (by rfl) ⟨362048, by rfl⟩ : syracuseStep 1930925 = 724097) (by norm_num)
theorem B1447609 : Blo 1285961 1447609 := bbase (se 2 (by rfl) ⟨542853, by rfl⟩ : syracuseStep 1447609 = 1085707) (by norm_num)
theorem B3258053 : Blo 1285961 3258053 := bbase (se 4 (by rfl) ⟨305442, by rfl⟩ : syracuseStep 3258053 = 610885) (by norm_num)
theorem B3479237 : Blo 1285961 3479237 := bbase (se 4 (by rfl) ⟨326178, by rfl⟩ : syracuseStep 3479237 = 652357) (by norm_num)
theorem B1930949 : Blo 1285961 1930949 := bbase (se 4 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 1930949 = 362053) (by norm_num)
theorem B6510293 : Blo 1285961 6510293 := bbase (se 7 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 6510293 = 152585) (by norm_num)
theorem B2897621 : Blo 1285961 2897621 := bbase (se 7 (by rfl) ⟨33956, by rfl⟩ : syracuseStep 2897621 = 67913) (by norm_num)
theorem B1447645 : Blo 1285961 1447645 := bbase (se 3 (by rfl) ⟨271433, by rfl⟩ : syracuseStep 1447645 = 542867) (by norm_num)
theorem B1930973 : Blo 1285961 1930973 := bbase (se 3 (by rfl) ⟨362057, by rfl⟩ : syracuseStep 1930973 = 724115) (by norm_num)
theorem B2062045 : Blo 1285961 2062045 := bbase (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) (by norm_num)
theorem B1627877 : Blo 1285961 1627877 := bbase (se 4 (by rfl) ⟨152613, by rfl⟩ : syracuseStep 1627877 = 305227) (by norm_num)
theorem B1930997 : Blo 1285961 1930997 := bbase (se 5 (by rfl) ⟨90515, by rfl⟩ : syracuseStep 1930997 = 181031) (by norm_num)
theorem B4888309 : Blo 1285961 4888309 := bbase (se 5 (by rfl) ⟨229139, by rfl⟩ : syracuseStep 4888309 = 458279) (by norm_num)
theorem B1832701 : Blo 1285961 1832701 := bbase (se 3 (by rfl) ⟨343631, by rfl⟩ : syracuseStep 1832701 = 687263) (by norm_num)
theorem B1447681 : Blo 1285961 1447681 := bbase (se 2 (by rfl) ⟨542880, by rfl⟩ : syracuseStep 1447681 = 1085761) (by norm_num)
theorem B2750213 : Blo 1285961 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B1931021 : Blo 1285961 1931021 := bbase (se 3 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 1931021 = 724133) (by norm_num)
theorem B2750221 : Blo 1285961 2750221 := bbase (se 3 (by rfl) ⟨515666, by rfl⟩ : syracuseStep 2750221 = 1031333) (by norm_num)
theorem B16496405 : Blo 1285961 16496405 := bbase (se 6 (by rfl) ⟨386634, by rfl⟩ : syracuseStep 16496405 = 773269) (by norm_num)
theorem B1627933 : Blo 1285961 1627933 := bbase (se 3 (by rfl) ⟨305237, by rfl⟩ : syracuseStep 1627933 = 610475) (by norm_num)
theorem B2897693 : Blo 1285961 2897693 := bbase (se 3 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 2897693 = 1086635) (by norm_num)
theorem B1447717 : Blo 1285961 1447717 := bbase (se 4 (by rfl) ⟨135723, by rfl⟩ : syracuseStep 1447717 = 271447) (by norm_num)
theorem B1931045 : Blo 1285961 1931045 := bbase (se 4 (by rfl) ⟨181035, by rfl⟩ : syracuseStep 1931045 = 362071) (by norm_num)
theorem B1341241 : Blo 1285961 1341241 := bbase (se 2 (by rfl) ⟨502965, by rfl⟩ : syracuseStep 1341241 = 1005931) (by norm_num)
theorem B1374013 : Blo 1285961 1374013 := bbase (se 3 (by rfl) ⟨257627, by rfl⟩ : syracuseStep 1374013 = 515255) (by norm_num)
theorem B1931069 : Blo 1285961 1931069 := bbase (se 3 (by rfl) ⟨362075, by rfl⟩ : syracuseStep 1931069 = 724151) (by norm_num)
theorem B1374017 : Blo 1285961 1374017 := bbase (se 2 (by rfl) ⟨515256, by rfl⟩ : syracuseStep 1374017 = 1030513) (by norm_num)
theorem B3479365 : Blo 1285961 3479365 := bbase (se 4 (by rfl) ⟨326190, by rfl⟩ : syracuseStep 3479365 = 652381) (by norm_num)
theorem B1447753 : Blo 1285961 1447753 := bbase (se 2 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 1447753 = 1085815) (by norm_num)
theorem B1931093 : Blo 1285961 1931093 := bbase (se 9 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 1931093 = 11315) (by norm_num)
theorem B1832797 : Blo 1285961 1832797 := bbase (se 3 (by rfl) ⟨343649, by rfl⟩ : syracuseStep 1832797 = 687299) (by norm_num)
theorem B2897765 : Blo 1285961 2897765 := bbase (se 4 (by rfl) ⟨271665, by rfl⟩ : syracuseStep 2897765 = 543331) (by norm_num)
theorem B1447789 : Blo 1285961 1447789 := bbase (se 3 (by rfl) ⟨271460, by rfl⟩ : syracuseStep 1447789 = 542921) (by norm_num)
theorem B1931117 : Blo 1285961 1931117 := bbase (se 3 (by rfl) ⟨362084, by rfl⟩ : syracuseStep 1931117 = 724169) (by norm_num)
theorem B1628029 : Blo 1285961 1628029 := bbase (se 3 (by rfl) ⟨305255, by rfl⟩ : syracuseStep 1628029 = 610511) (by norm_num)
theorem B3258245 : Blo 1285961 3258245 := bbase (se 4 (by rfl) ⟨305460, by rfl⟩ : syracuseStep 3258245 = 610921) (by norm_num)
theorem B1931141 : Blo 1285961 1931141 := bbase (se 4 (by rfl) ⟨181044, by rfl⟩ : syracuseStep 1931141 = 362089) (by norm_num)
theorem B1447825 : Blo 1285961 1447825 := bbase (se 2 (by rfl) ⟨542934, by rfl⟩ : syracuseStep 1447825 = 1085869) (by norm_num)
theorem B1931165 : Blo 1285961 1931165 := bbase (se 3 (by rfl) ⟨362093, by rfl⟩ : syracuseStep 1931165 = 724187) (by norm_num)
theorem B2897837 : Blo 1285961 2897837 := bbase (se 3 (by rfl) ⟨543344, by rfl⟩ : syracuseStep 2897837 = 1086689) (by norm_num)
theorem B1447861 : Blo 1285961 1447861 := bbase (se 5 (by rfl) ⟨67868, by rfl⟩ : syracuseStep 1447861 = 135737) (by norm_num)
theorem B1931189 : Blo 1285961 1931189 := bbase (se 5 (by rfl) ⟨90524, by rfl⟩ : syracuseStep 1931189 = 181049) (by norm_num)
theorem B1931213 : Blo 1285961 1931213 := bbase (se 3 (by rfl) ⟨362102, by rfl⟩ : syracuseStep 1931213 = 724205) (by norm_num)
theorem B1447897 : Blo 1285961 1447897 := bbase (se 2 (by rfl) ⟨542961, by rfl⟩ : syracuseStep 1447897 = 1085923) (by norm_num)
theorem B1931237 : Blo 1285961 1931237 := bbase (se 4 (by rfl) ⟨181053, by rfl⟩ : syracuseStep 1931237 = 362107) (by norm_num)
theorem B2897909 : Blo 1285961 2897909 := bbase (se 5 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 2897909 = 271679) (by norm_num)
theorem B1447933 : Blo 1285961 1447933 := bbase (se 3 (by rfl) ⟨271487, by rfl⟩ : syracuseStep 1447933 = 542975) (by norm_num)
theorem B1931261 : Blo 1285961 1931261 := bbase (se 3 (by rfl) ⟨362111, by rfl⟩ : syracuseStep 1931261 = 724223) (by norm_num)
theorem B9771029 : Blo 1285961 9771029 := bbase (se 6 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 9771029 = 458017) (by norm_num)
theorem B1931285 : Blo 1285961 1931285 := bbase (se 6 (by rfl) ⟨45264, by rfl⟩ : syracuseStep 1931285 = 90529) (by norm_num)
theorem B1447969 : Blo 1285961 1447969 := bbase (se 2 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 1447969 = 1085977) (by norm_num)
theorem B4888613 : Blo 1285961 4888613 := bbase (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) (by norm_num)
theorem B1628201 : Blo 1285961 1628201 := bbase (se 2 (by rfl) ⟨610575, by rfl⟩ : syracuseStep 1628201 = 1221151) (by norm_num)
theorem B1931309 : Blo 1285961 1931309 := bbase (se 3 (by rfl) ⟨362120, by rfl⟩ : syracuseStep 1931309 = 724241) (by norm_num)
theorem B1448005 : Blo 1285961 1448005 := bbase (se 4 (by rfl) ⟨135750, by rfl⟩ : syracuseStep 1448005 = 271501) (by norm_num)
theorem B1931333 : Blo 1285961 1931333 := bbase (se 4 (by rfl) ⟨181062, by rfl⟩ : syracuseStep 1931333 = 362125) (by norm_num)
theorem B3135581 : Blo 1285961 3135581 := bbase (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) (by norm_num)
theorem B1931357 : Blo 1285961 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B1628257 : Blo 1285961 1628257 := bbase (se 2 (by rfl) ⟨610596, by rfl⟩ : syracuseStep 1628257 = 1221193) (by norm_num)
theorem B1448041 : Blo 1285961 1448041 := bbase (se 2 (by rfl) ⟨543015, by rfl⟩ : syracuseStep 1448041 = 1086031) (by norm_num)
theorem B11147381 : Blo 1285961 11147381 := bbase (se 5 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 11147381 = 1045067) (by norm_num)
theorem B1931381 : Blo 1285961 1931381 := bbase (se 5 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 1931381 = 181067) (by norm_num)
theorem B1448077 : Blo 1285961 1448077 := bbase (se 3 (by rfl) ⟨271514, by rfl⟩ : syracuseStep 1448077 = 543029) (by norm_num)
theorem B1931405 : Blo 1285961 1931405 := bbase (se 3 (by rfl) ⟨362138, by rfl⟩ : syracuseStep 1931405 = 724277) (by norm_num)
theorem B1931429 : Blo 1285961 1931429 := bbase (se 4 (by rfl) ⟨181071, by rfl⟩ : syracuseStep 1931429 = 362143) (by norm_num)
theorem B1448113 : Blo 1285961 1448113 := bbase (se 2 (by rfl) ⟨543042, by rfl⟩ : syracuseStep 1448113 = 1086085) (by norm_num)
theorem B1931453 : Blo 1285961 1931453 := bbase (se 3 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 1931453 = 724295) (by norm_num)
theorem B1628353 : Blo 1285961 1628353 := bbase (se 2 (by rfl) ⟨610632, by rfl⟩ : syracuseStep 1628353 = 1221265) (by norm_num)
theorem B1956037 : Blo 1285961 1956037 := bbase (se 4 (by rfl) ⟨183378, by rfl⟩ : syracuseStep 1956037 = 366757) (by norm_num)
theorem B1448149 : Blo 1285961 1448149 := bbase (se 7 (by rfl) ⟨16970, by rfl⟩ : syracuseStep 1448149 = 33941) (by norm_num)
theorem B1931477 : Blo 1285961 1931477 := bbase (se 7 (by rfl) ⟨22634, by rfl⟩ : syracuseStep 1931477 = 45269) (by norm_num)
theorem B1546457 : Blo 1285961 1546457 := bbase (se 2 (by rfl) ⟨579921, by rfl⟩ : syracuseStep 1546457 = 1159843) (by norm_num)
theorem B3258589 : Blo 1285961 3258589 := bbase (se 3 (by rfl) ⟨610985, by rfl⟩ : syracuseStep 3258589 = 1221971) (by norm_num)
theorem B1931501 : Blo 1285961 1931501 := bbase (se 3 (by rfl) ⟨362156, by rfl⟩ : syracuseStep 1931501 = 724313) (by norm_num)
theorem B1448185 : Blo 1285961 1448185 := bbase (se 2 (by rfl) ⟨543069, by rfl⟩ : syracuseStep 1448185 = 1086139) (by norm_num)
theorem B2062589 : Blo 1285961 2062589 := bbase (se 3 (by rfl) ⟨386735, by rfl⟩ : syracuseStep 2062589 = 773471) (by norm_num)
theorem B1931525 : Blo 1285961 1931525 := bbase (se 4 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 1931525 = 362161) (by norm_num)
theorem B1448221 : Blo 1285961 1448221 := bbase (se 3 (by rfl) ⟨271541, by rfl⟩ : syracuseStep 1448221 = 543083) (by norm_num)
theorem B1931549 : Blo 1285961 1931549 := bbase (se 3 (by rfl) ⟨362165, by rfl⟩ : syracuseStep 1931549 = 724331) (by norm_num)
theorem B1931573 : Blo 1285961 1931573 := bbase (se 5 (by rfl) ⟨90542, by rfl⟩ : syracuseStep 1931573 = 181085) (by norm_num)
theorem B1448257 : Blo 1285961 1448257 := bbase (se 2 (by rfl) ⟨543096, by rfl⟩ : syracuseStep 1448257 = 1086193) (by norm_num)
theorem B3258701 : Blo 1285961 3258701 := bbase (se 3 (by rfl) ⟨611006, by rfl⟩ : syracuseStep 3258701 = 1222013) (by norm_num)
theorem B1833293 : Blo 1285961 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B1931597 : Blo 1285961 1931597 := bbase (se 3 (by rfl) ⟨362174, by rfl⟩ : syracuseStep 1931597 = 724349) (by norm_num)
theorem B3348821 : Blo 1285961 3348821 := bbase (se 10 (by rfl) ⟨4905, by rfl⟩ : syracuseStep 3348821 = 9811) (by norm_num)
theorem B1448293 : Blo 1285961 1448293 := bbase (se 4 (by rfl) ⟨135777, by rfl⟩ : syracuseStep 1448293 = 271555) (by norm_num)
theorem B1931621 : Blo 1285961 1931621 := bbase (se 4 (by rfl) ⟨181089, by rfl⟩ : syracuseStep 1931621 = 362179) (by norm_num)
theorem B1628525 : Blo 1285961 1628525 := bbase (se 3 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 1628525 = 610697) (by norm_num)
theorem B1374581 : Blo 1285961 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B1931645 : Blo 1285961 1931645 := bbase (se 3 (by rfl) ⟨362183, by rfl⟩ : syracuseStep 1931645 = 724367) (by norm_num)
theorem B1546625 : Blo 1285961 1546625 := bbase (se 2 (by rfl) ⟨579984, by rfl⟩ : syracuseStep 1546625 = 1159969) (by norm_num)
theorem B1448329 : Blo 1285961 1448329 := bbase (se 2 (by rfl) ⟨543123, by rfl⟩ : syracuseStep 1448329 = 1086247) (by norm_num)
theorem B1931669 : Blo 1285961 1931669 := bbase (se 6 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 1931669 = 90547) (by norm_num)
theorem B1628581 : Blo 1285961 1628581 := bbase (se 4 (by rfl) ⟨152679, by rfl⟩ : syracuseStep 1628581 = 305359) (by norm_num)
theorem B1448365 : Blo 1285961 1448365 := bbase (se 3 (by rfl) ⟨271568, by rfl⟩ : syracuseStep 1448365 = 543137) (by norm_num)
theorem B1931693 : Blo 1285961 1931693 := bbase (se 3 (by rfl) ⟨362192, by rfl⟩ : syracuseStep 1931693 = 724385) (by norm_num)
theorem B10041781 : Blo 1285961 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B1931717 : Blo 1285961 1931717 := bbase (se 4 (by rfl) ⟨181098, by rfl⟩ : syracuseStep 1931717 = 362197) (by norm_num)
theorem B1448401 : Blo 1285961 1448401 := bbase (se 2 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 1448401 = 1086301) (by norm_num)
theorem B1931741 : Blo 1285961 1931741 := bbase (se 3 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 1931741 = 724403) (by norm_num)
theorem B1448437 : Blo 1285961 1448437 := bbase (se 5 (by rfl) ⟨67895, by rfl⟩ : syracuseStep 1448437 = 135791) (by norm_num)
theorem B1931765 : Blo 1285961 1931765 := bbase (se 5 (by rfl) ⟨90551, by rfl⟩ : syracuseStep 1931765 = 181103) (by norm_num)
theorem B1628677 : Blo 1285961 1628677 := bbase (se 4 (by rfl) ⟨152688, by rfl⟩ : syracuseStep 1628677 = 305377) (by norm_num)
theorem B3258893 : Blo 1285961 3258893 := bbase (se 3 (by rfl) ⟨611042, by rfl⟩ : syracuseStep 3258893 = 1222085) (by norm_num)
theorem B1931789 : Blo 1285961 1931789 := bbase (se 3 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 1931789 = 724421) (by norm_num)
theorem B1448473 : Blo 1285961 1448473 := bbase (se 2 (by rfl) ⟨543177, by rfl⟩ : syracuseStep 1448473 = 1086355) (by norm_num)
theorem B1931813 : Blo 1285961 1931813 := bbase (se 4 (by rfl) ⟨181107, by rfl⟩ : syracuseStep 1931813 = 362215) (by norm_num)
theorem B1374769 : Blo 1285961 1374769 := bbase (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) (by norm_num)
theorem B1448509 : Blo 1285961 1448509 := bbase (se 3 (by rfl) ⟨271595, by rfl⟩ : syracuseStep 1448509 = 543191) (by norm_num)
theorem B1931837 : Blo 1285961 1931837 := bbase (se 3 (by rfl) ⟨362219, by rfl⟩ : syracuseStep 1931837 = 724439) (by norm_num)
theorem B6519365 : Blo 1285961 6519365 := bbase (se 4 (by rfl) ⟨611190, by rfl⟩ : syracuseStep 6519365 = 1222381) (by norm_num)
theorem B1931861 : Blo 1285961 1931861 := bbase (se 8 (by rfl) ⟨11319, by rfl⟩ : syracuseStep 1931861 = 22639) (by norm_num)
theorem B1448545 : Blo 1285961 1448545 := bbase (se 2 (by rfl) ⟨543204, by rfl⟩ : syracuseStep 1448545 = 1086409) (by norm_num)
theorem B1931885 : Blo 1285961 1931885 := bbase (se 3 (by rfl) ⟨362228, by rfl⟩ : syracuseStep 1931885 = 724457) (by norm_num)
theorem B4340357 : Blo 1285961 4340357 := bbase (se 4 (by rfl) ⟨406908, by rfl⟩ : syracuseStep 4340357 = 813817) (by norm_num)
theorem B1448581 : Blo 1285961 1448581 := bbase (se 4 (by rfl) ⟨135804, by rfl⟩ : syracuseStep 1448581 = 271609) (by norm_num)
theorem B1931909 : Blo 1285961 1931909 := bbase (se 4 (by rfl) ⟨181116, by rfl⟩ : syracuseStep 1931909 = 362233) (by norm_num)
theorem B1931933 : Blo 1285961 1931933 := bbase (se 3 (by rfl) ⟨362237, by rfl⟩ : syracuseStep 1931933 = 724475) (by norm_num)
theorem B1448617 : Blo 1285961 1448617 := bbase (se 2 (by rfl) ⟨543231, by rfl⟩ : syracuseStep 1448617 = 1086463) (by norm_num)
theorem B1628849 : Blo 1285961 1628849 := bbase (se 2 (by rfl) ⟨610818, by rfl⟩ : syracuseStep 1628849 = 1221637) (by norm_num)
theorem B1546933 : Blo 1285961 1546933 := bbase (se 5 (by rfl) ⟨72512, by rfl⟩ : syracuseStep 1546933 = 145025) (by norm_num)
theorem B1448653 : Blo 1285961 1448653 := bbase (se 3 (by rfl) ⟨271622, by rfl⟩ : syracuseStep 1448653 = 543245) (by norm_num)
theorem B9910997 : Blo 1285961 9910997 := bbase (se 7 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 9910997 = 232289) (by norm_num)
theorem B1628905 : Blo 1285961 1628905 := bbase (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) (by norm_num)
theorem B1448689 : Blo 1285961 1448689 := bbase (se 2 (by rfl) ⟨543258, by rfl⟩ : syracuseStep 1448689 = 1086517) (by norm_num)
theorem B1448725 : Blo 1285961 1448725 := bbase (se 6 (by rfl) ⟨33954, by rfl⟩ : syracuseStep 1448725 = 67909) (by norm_num)
theorem B1448761 : Blo 1285961 1448761 := bbase (se 2 (by rfl) ⟨543285, by rfl⟩ : syracuseStep 1448761 = 1086571) (by norm_num)
theorem B1629001 : Blo 1285961 1629001 := bbase (se 2 (by rfl) ⟨610875, by rfl⟩ : syracuseStep 1629001 = 1221751) (by norm_num)
theorem B1448797 : Blo 1285961 1448797 := bbase (se 3 (by rfl) ⟨271649, by rfl⟩ : syracuseStep 1448797 = 543299) (by norm_num)
theorem B3259237 : Blo 1285961 3259237 := bbase (se 4 (by rfl) ⟨305553, by rfl⟩ : syracuseStep 3259237 = 611107) (by norm_num)
theorem B1858405 : Blo 1285961 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1448833 : Blo 1285961 1448833 := bbase (se 2 (by rfl) ⟨543312, by rfl⟩ : syracuseStep 1448833 = 1086625) (by norm_num)
theorem B1547149 : Blo 1285961 1547149 := bbase (se 3 (by rfl) ⟨290090, by rfl⟩ : syracuseStep 1547149 = 580181) (by norm_num)
theorem B14654357 : Blo 1285961 14654357 := bbase (se 6 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 14654357 = 686923) (by norm_num)
theorem B1448869 : Blo 1285961 1448869 := bbase (se 4 (by rfl) ⟨135831, by rfl⟩ : syracuseStep 1448869 = 271663) (by norm_num)
theorem B1448905 : Blo 1285961 1448905 := bbase (se 2 (by rfl) ⟨543339, by rfl⟩ : syracuseStep 1448905 = 1086679) (by norm_num)
theorem B3259349 : Blo 1285961 3259349 := bbase (se 7 (by rfl) ⟨38195, by rfl⟩ : syracuseStep 3259349 = 76391) (by norm_num)
theorem B6511589 : Blo 1285961 6511589 := bbase (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) (by norm_num)
theorem B1448941 : Blo 1285961 1448941 := bbase (se 3 (by rfl) ⟨271676, by rfl⟩ : syracuseStep 1448941 = 543353) (by norm_num)
theorem B1629173 : Blo 1285961 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B1629229 : Blo 1285961 1629229 := bbase (se 3 (by rfl) ⟨305480, by rfl⟩ : syracuseStep 1629229 = 610961) (by norm_num)
theorem B4340789 : Blo 1285961 4340789 := bbase (se 5 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 4340789 = 406949) (by norm_num)
theorem B1629325 : Blo 1285961 1629325 := bbase (se 3 (by rfl) ⟨305498, by rfl⟩ : syracuseStep 1629325 = 610997) (by norm_num)
theorem B3259541 : Blo 1285961 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B2317501 : Blo 1285961 2317501 := bbase (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) (by norm_num)
theorem B14851349 : Blo 1285961 14851349 := bbase (se 6 (by rfl) ⟨348078, by rfl⟩ : syracuseStep 14851349 = 696157) (by norm_num)
theorem B2170165 : Blo 1285961 2170165 := bbase (se 5 (by rfl) ⟨101726, by rfl⟩ : syracuseStep 2170165 = 203453) (by norm_num)
theorem B1629497 : Blo 1285961 1629497 := bbase (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) (by norm_num)
theorem B1629553 : Blo 1285961 1629553 := bbase (se 2 (by rfl) ⟨611082, by rfl⟩ : syracuseStep 1629553 = 1222165) (by norm_num)
theorem B2170253 : Blo 1285961 2170253 := bbase (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) (by norm_num)
theorem B1629649 : Blo 1285961 1629649 := bbase (se 2 (by rfl) ⟨611118, by rfl⟩ : syracuseStep 1629649 = 1222237) (by norm_num)
theorem B5291477 : Blo 1285961 5291477 := bbase (se 7 (by rfl) ⟨62009, by rfl⟩ : syracuseStep 5291477 = 124019) (by norm_num)
theorem B4341221 : Blo 1285961 4341221 := bbase (se 4 (by rfl) ⟨406989, by rfl⟩ : syracuseStep 4341221 = 813979) (by norm_num)
theorem B2317805 : Blo 1285961 2317805 := bbase (se 3 (by rfl) ⟨434588, by rfl⟩ : syracuseStep 2317805 = 869177) (by norm_num)
theorem B3259885 : Blo 1285961 3259885 := bbase (se 3 (by rfl) ⟨611228, by rfl⟩ : syracuseStep 3259885 = 1222457) (by norm_num)
theorem B2170381 : Blo 1285961 2170381 := bbase (se 3 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 2170381 = 813893) (by norm_num)
theorem B3259997 : Blo 1285961 3259997 := bbase (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) (by norm_num)
theorem B2170469 : Blo 1285961 2170469 := bbase (se 4 (by rfl) ⟨203481, by rfl⟩ : syracuseStep 2170469 = 406963) (by norm_num)
theorem B1629821 : Blo 1285961 1629821 := bbase (se 3 (by rfl) ⟨305591, by rfl⟩ : syracuseStep 1629821 = 611183) (by norm_num)
theorem B1629877 : Blo 1285961 1629877 := bbase (se 5 (by rfl) ⟨76400, by rfl⟩ : syracuseStep 1629877 = 152801) (by norm_num)
theorem B2170597 : Blo 1285961 2170597 := bbase (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) (by norm_num)
theorem B6602485 : Blo 1285961 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B1629973 : Blo 1285961 1629973 := bbase (se 6 (by rfl) ⟨38202, by rfl⟩ : syracuseStep 1629973 = 76405) (by norm_num)
theorem B2170685 : Blo 1285961 2170685 := bbase (se 3 (by rfl) ⟨407003, by rfl⟩ : syracuseStep 2170685 = 814007) (by norm_num)
theorem B4341653 : Blo 1285961 4341653 := bbase (se 6 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 4341653 = 203515) (by norm_num)
theorem B2170813 : Blo 1285961 2170813 := bbase (se 3 (by rfl) ⟨407027, by rfl⟩ : syracuseStep 2170813 = 814055) (by norm_num)
theorem B1933301 : Blo 1285961 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B5496821 : Blo 1285961 5496821 := bbase (se 5 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 5496821 = 515327) (by norm_num)
theorem B1286147 : Blo 1285961 1286147 := bstep (se 1 (by rfl) ⟨964610, by rfl⟩ : syracuseStep 1286147 = 1929221) B1929221
theorem B1286163 : Blo 1285961 1286163 := bstep (se 1 (by rfl) ⟨964622, by rfl⟩ : syracuseStep 1286163 = 1929245) B1929245
theorem B1286179 : Blo 1285961 1286179 := bstep (se 1 (by rfl) ⟨964634, by rfl⟩ : syracuseStep 1286179 = 1929269) B1929269
theorem B1286195 : Blo 1285961 1286195 := bstep (se 1 (by rfl) ⟨964646, by rfl⟩ : syracuseStep 1286195 = 1929293) B1929293
theorem B1286211 : Blo 1285961 1286211 := bstep (se 1 (by rfl) ⟨964658, by rfl⟩ : syracuseStep 1286211 = 1929317) B1929317
theorem B7331917 : Blo 1285961 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B1286227 : Blo 1285961 1286227 := bstep (se 1 (by rfl) ⟨964670, by rfl⟩ : syracuseStep 1286227 = 1929341) B1929341
theorem B1466467 : Blo 1285961 1466467 := bstep (se 1 (by rfl) ⟨1099850, by rfl⟩ : syracuseStep 1466467 = 2199701) B2199701
theorem B1286243 : Blo 1285961 1286243 := bstep (se 1 (by rfl) ⟨964682, by rfl⟩ : syracuseStep 1286243 = 1929365) B1929365
theorem B4341869 : Blo 1285961 4341869 := bstep (se 3 (by rfl) ⟨814100, by rfl⟩ : syracuseStep 4341869 = 1628201) B1628201
theorem B1286259 : Blo 1285961 1286259 := bstep (se 1 (by rfl) ⟨964694, by rfl⟩ : syracuseStep 1286259 = 1929389) B1929389
theorem B2171009 : Blo 1285961 2171009 := bstep (se 2 (by rfl) ⟨814128, by rfl⟩ : syracuseStep 2171009 = 1628257) B1628257
theorem B1286275 : Blo 1285961 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B8249485 : Blo 1285961 8249485 := bstep (se 3 (by rfl) ⟨1546778, by rfl⟩ : syracuseStep 8249485 = 3093557) B3093557
theorem B1286291 : Blo 1285961 1286291 := bstep (se 1 (by rfl) ⟨964718, by rfl⟩ : syracuseStep 1286291 = 1929437) B1929437
theorem B1286307 : Blo 1285961 1286307 := bstep (se 1 (by rfl) ⟨964730, by rfl⟩ : syracuseStep 1286307 = 1929461) B1929461
theorem B4341923 : Blo 1285961 4341923 := bstep (se 1 (by rfl) ⟨3256442, by rfl⟩ : syracuseStep 4341923 = 6512885) B6512885
theorem B4636835 : Blo 1285961 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B5726371 : Blo 1285961 5726371 := bstep (se 1 (by rfl) ⟨4294778, by rfl⟩ : syracuseStep 5726371 = 8589557) B8589557
theorem B2785457 : Blo 1285961 2785457 := bstep (se 2 (by rfl) ⟨1044546, by rfl⟩ : syracuseStep 2785457 = 2089093) B2089093
theorem B1286323 : Blo 1285961 1286323 := bstep (se 1 (by rfl) ⟨964742, by rfl⟩ : syracuseStep 1286323 = 1929485) B1929485
theorem B1286339 : Blo 1285961 1286339 := bstep (se 1 (by rfl) ⟨964754, by rfl⟩ : syracuseStep 1286339 = 1929509) B1929509
theorem B1286355 : Blo 1285961 1286355 := bstep (se 1 (by rfl) ⟨964766, by rfl⟩ : syracuseStep 1286355 = 1929533) B1929533
theorem B1286371 : Blo 1285961 1286371 := bstep (se 1 (by rfl) ⟨964778, by rfl⟩ : syracuseStep 1286371 = 1929557) B1929557
theorem B1286387 : Blo 1285961 1286387 := bstep (se 1 (by rfl) ⟨964790, by rfl⟩ : syracuseStep 1286387 = 1929581) B1929581
theorem B2171137 : Blo 1285961 2171137 := bstep (se 2 (by rfl) ⟨814176, by rfl⟩ : syracuseStep 2171137 = 1628353) B1628353
theorem B1286403 : Blo 1285961 1286403 := bstep (se 1 (by rfl) ⟨964802, by rfl⟩ : syracuseStep 1286403 = 1929605) B1929605
theorem B1286419 : Blo 1285961 1286419 := bstep (se 1 (by rfl) ⟨964814, by rfl⟩ : syracuseStep 1286419 = 1929629) B1929629
theorem B1286435 : Blo 1285961 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B2171171 : Blo 1285961 2171171 := bstep (se 1 (by rfl) ⟨1628378, by rfl⟩ : syracuseStep 2171171 = 3256757) B3256757
theorem B2646307 : Blo 1285961 2646307 := bstep (se 1 (by rfl) ⟨1984730, by rfl⟩ : syracuseStep 2646307 = 3969461) B3969461
theorem B1286451 : Blo 1285961 1286451 := bstep (se 1 (by rfl) ⟨964838, by rfl⟩ : syracuseStep 1286451 = 1929677) B1929677
theorem B1286467 : Blo 1285961 1286467 := bstep (se 1 (by rfl) ⟨964850, by rfl⟩ : syracuseStep 1286467 = 1929701) B1929701
theorem B14868805 : Blo 1285961 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B1286483 : Blo 1285961 1286483 := bstep (se 1 (by rfl) ⟨964862, by rfl⟩ : syracuseStep 1286483 = 1929725) B1929725
theorem B1286499 : Blo 1285961 1286499 := bstep (se 1 (by rfl) ⟨964874, by rfl⟩ : syracuseStep 1286499 = 1929749) B1929749
theorem B1286515 : Blo 1285961 1286515 := bstep (se 1 (by rfl) ⟨964886, by rfl⟩ : syracuseStep 1286515 = 1929773) B1929773
theorem B2441603 : Blo 1285961 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B1286531 : Blo 1285961 1286531 := bstep (se 1 (by rfl) ⟨964898, by rfl⟩ : syracuseStep 1286531 = 1929797) B1929797
theorem B1286547 : Blo 1285961 1286547 := bstep (se 1 (by rfl) ⟨964910, by rfl⟩ : syracuseStep 1286547 = 1929821) B1929821
theorem B1286563 : Blo 1285961 1286563 := bstep (se 1 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 1286563 = 1929845) B1929845
theorem B2171299 : Blo 1285961 2171299 := bstep (se 1 (by rfl) ⟨1628474, by rfl⟩ : syracuseStep 2171299 = 3256949) B3256949
theorem B4342193 : Blo 1285961 4342193 := bstep (se 2 (by rfl) ⟨1628322, by rfl⟩ : syracuseStep 4342193 = 3256645) B3256645
theorem B1286579 : Blo 1285961 1286579 := bstep (se 1 (by rfl) ⟨964934, by rfl⟩ : syracuseStep 1286579 = 1929869) B1929869
theorem B4121027 : Blo 1285961 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B1286595 : Blo 1285961 1286595 := bstep (se 1 (by rfl) ⟨964946, by rfl⟩ : syracuseStep 1286595 = 1929893) B1929893
theorem B1286611 : Blo 1285961 1286611 := bstep (se 1 (by rfl) ⟨964958, by rfl⟩ : syracuseStep 1286611 = 1929917) B1929917
theorem B1286627 : Blo 1285961 1286627 := bstep (se 1 (by rfl) ⟨964970, by rfl⟩ : syracuseStep 1286627 = 1929941) B1929941
theorem B1286643 : Blo 1285961 1286643 := bstep (se 1 (by rfl) ⟨964982, by rfl⟩ : syracuseStep 1286643 = 1929965) B1929965
theorem B1286659 : Blo 1285961 1286659 := bstep (se 1 (by rfl) ⟨964994, by rfl⟩ : syracuseStep 1286659 = 1929989) B1929989
theorem B1286675 : Blo 1285961 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B1286691 : Blo 1285961 1286691 := bstep (se 1 (by rfl) ⟨965018, by rfl⟩ : syracuseStep 1286691 = 1930037) B1930037
theorem B2171441 : Blo 1285961 2171441 := bstep (se 2 (by rfl) ⟨814290, by rfl⟩ : syracuseStep 2171441 = 1628581) B1628581
theorem B1286707 : Blo 1285961 1286707 := bstep (se 1 (by rfl) ⟨965030, by rfl⟩ : syracuseStep 1286707 = 1930061) B1930061
theorem B1286723 : Blo 1285961 1286723 := bstep (se 1 (by rfl) ⟨965042, by rfl⟩ : syracuseStep 1286723 = 1930085) B1930085
theorem B1286739 : Blo 1285961 1286739 := bstep (se 1 (by rfl) ⟨965054, by rfl⟩ : syracuseStep 1286739 = 1930109) B1930109
theorem B1286755 : Blo 1285961 1286755 := bstep (se 1 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 1286755 = 1930133) B1930133
theorem B1286771 : Blo 1285961 1286771 := bstep (se 1 (by rfl) ⟨965078, by rfl⟩ : syracuseStep 1286771 = 1930157) B1930157
theorem B4121219 : Blo 1285961 4121219 := bstep (se 1 (by rfl) ⟨3090914, by rfl⟩ : syracuseStep 4121219 = 6181829) B6181829
theorem B1286787 : Blo 1285961 1286787 := bstep (se 1 (by rfl) ⟨965090, by rfl⟩ : syracuseStep 1286787 = 1930181) B1930181
theorem B1286803 : Blo 1285961 1286803 := bstep (se 1 (by rfl) ⟨965102, by rfl⟩ : syracuseStep 1286803 = 1930205) B1930205
theorem B1286819 : Blo 1285961 1286819 := bstep (se 1 (by rfl) ⟨965114, by rfl⟩ : syracuseStep 1286819 = 1930229) B1930229
theorem B2171569 : Blo 1285961 2171569 := bstep (se 2 (by rfl) ⟨814338, by rfl⟩ : syracuseStep 2171569 = 1628677) B1628677
theorem B1761971 : Blo 1285961 1761971 := bstep (se 1 (by rfl) ⟨1321478, by rfl⟩ : syracuseStep 1761971 = 2642957) B2642957
theorem B1286835 : Blo 1285961 1286835 := bstep (se 1 (by rfl) ⟨965126, by rfl⟩ : syracuseStep 1286835 = 1930253) B1930253
theorem B1286851 : Blo 1285961 1286851 := bstep (se 1 (by rfl) ⟨965138, by rfl⟩ : syracuseStep 1286851 = 1930277) B1930277
theorem B1286867 : Blo 1285961 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B2171603 : Blo 1285961 2171603 := bstep (se 1 (by rfl) ⟨1628702, by rfl⟩ : syracuseStep 2171603 = 3257405) B3257405
theorem B2261729 : Blo 1285961 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B1286883 : Blo 1285961 1286883 := bstep (se 1 (by rfl) ⟨965162, by rfl⟩ : syracuseStep 1286883 = 1930325) B1930325
theorem B5497571 : Blo 1285961 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B1286899 : Blo 1285961 1286899 := bstep (se 1 (by rfl) ⟨965174, by rfl⟩ : syracuseStep 1286899 = 1930349) B1930349
theorem B1286915 : Blo 1285961 1286915 := bstep (se 1 (by rfl) ⟨965186, by rfl⟩ : syracuseStep 1286915 = 1930373) B1930373
theorem B1286931 : Blo 1285961 1286931 := bstep (se 1 (by rfl) ⟨965198, by rfl⟩ : syracuseStep 1286931 = 1930397) B1930397
theorem B1286947 : Blo 1285961 1286947 := bstep (se 1 (by rfl) ⟨965210, by rfl⟩ : syracuseStep 1286947 = 1930421) B1930421
theorem B1286963 : Blo 1285961 1286963 := bstep (se 1 (by rfl) ⟨965222, by rfl⟩ : syracuseStep 1286963 = 1930445) B1930445
theorem B1286979 : Blo 1285961 1286979 := bstep (se 1 (by rfl) ⟨965234, by rfl⟩ : syracuseStep 1286979 = 1930469) B1930469
theorem B2171731 : Blo 1285961 2171731 := bstep (se 1 (by rfl) ⟨1628798, by rfl⟩ : syracuseStep 2171731 = 3257597) B3257597
theorem B1286995 : Blo 1285961 1286995 := bstep (se 1 (by rfl) ⟨965246, by rfl⟩ : syracuseStep 1286995 = 1930493) B1930493
theorem B1287011 : Blo 1285961 1287011 := bstep (se 1 (by rfl) ⟨965258, by rfl⟩ : syracuseStep 1287011 = 1930517) B1930517
theorem B1287027 : Blo 1285961 1287027 := bstep (se 1 (by rfl) ⟨965270, by rfl⟩ : syracuseStep 1287027 = 1930541) B1930541
theorem B1287043 : Blo 1285961 1287043 := bstep (se 1 (by rfl) ⟨965282, by rfl⟩ : syracuseStep 1287043 = 1930565) B1930565
theorem B8930189 : Blo 1285961 8930189 := bstep (se 3 (by rfl) ⟨1674410, by rfl⟩ : syracuseStep 8930189 = 3348821) B3348821
theorem B1287059 : Blo 1285961 1287059 := bstep (se 1 (by rfl) ⟨965294, by rfl⟩ : syracuseStep 1287059 = 1930589) B1930589
theorem B1287075 : Blo 1285961 1287075 := bstep (se 1 (by rfl) ⟨965306, by rfl⟩ : syracuseStep 1287075 = 1930613) B1930613
theorem B1287091 : Blo 1285961 1287091 := bstep (se 1 (by rfl) ⟨965318, by rfl⟩ : syracuseStep 1287091 = 1930637) B1930637
theorem B1287107 : Blo 1285961 1287107 := bstep (se 1 (by rfl) ⟨965330, by rfl⟩ : syracuseStep 1287107 = 1930661) B1930661
theorem B4342733 : Blo 1285961 4342733 := bstep (se 3 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 4342733 = 1628525) B1628525
theorem B1287123 : Blo 1285961 1287123 := bstep (se 1 (by rfl) ⟨965342, by rfl⟩ : syracuseStep 1287123 = 1930685) B1930685
theorem B2171873 : Blo 1285961 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B1287139 : Blo 1285961 1287139 := bstep (se 1 (by rfl) ⟨965354, by rfl⟩ : syracuseStep 1287139 = 1930709) B1930709
theorem B1287155 : Blo 1285961 1287155 := bstep (se 1 (by rfl) ⟨965366, by rfl⟩ : syracuseStep 1287155 = 1930733) B1930733
theorem B4342787 : Blo 1285961 4342787 := bstep (se 1 (by rfl) ⟨3257090, by rfl⟩ : syracuseStep 4342787 = 6514181) B6514181
theorem B1287171 : Blo 1285961 1287171 := bstep (se 1 (by rfl) ⟨965378, by rfl⟩ : syracuseStep 1287171 = 1930757) B1930757
theorem B1287187 : Blo 1285961 1287187 := bstep (se 1 (by rfl) ⟨965390, by rfl⟩ : syracuseStep 1287187 = 1930781) B1930781
theorem B1287203 : Blo 1285961 1287203 := bstep (se 1 (by rfl) ⟨965402, by rfl⟩ : syracuseStep 1287203 = 1930805) B1930805
theorem B1287219 : Blo 1285961 1287219 := bstep (se 1 (by rfl) ⟨965414, by rfl⟩ : syracuseStep 1287219 = 1930829) B1930829
theorem B1287235 : Blo 1285961 1287235 := bstep (se 1 (by rfl) ⟨965426, by rfl⟩ : syracuseStep 1287235 = 1930853) B1930853
theorem B1287251 : Blo 1285961 1287251 := bstep (se 1 (by rfl) ⟨965438, by rfl⟩ : syracuseStep 1287251 = 1930877) B1930877
theorem B2172001 : Blo 1285961 2172001 := bstep (se 2 (by rfl) ⟨814500, by rfl⟩ : syracuseStep 2172001 = 1629001) B1629001
theorem B1287267 : Blo 1285961 1287267 := bstep (se 1 (by rfl) ⟨965450, by rfl⟩ : syracuseStep 1287267 = 1930901) B1930901
theorem B1287283 : Blo 1285961 1287283 := bstep (se 1 (by rfl) ⟨965462, by rfl⟩ : syracuseStep 1287283 = 1930925) B1930925
theorem B2172035 : Blo 1285961 2172035 := bstep (se 1 (by rfl) ⟨1629026, by rfl⟩ : syracuseStep 2172035 = 3258053) B3258053
theorem B2319491 : Blo 1285961 2319491 := bstep (se 1 (by rfl) ⟨1739618, by rfl⟩ : syracuseStep 2319491 = 3479237) B3479237
theorem B1287299 : Blo 1285961 1287299 := bstep (se 1 (by rfl) ⟨965474, by rfl⟩ : syracuseStep 1287299 = 1930949) B1930949
theorem B1287315 : Blo 1285961 1287315 := bstep (se 1 (by rfl) ⟨965486, by rfl⟩ : syracuseStep 1287315 = 1930973) B1930973
theorem B5948579 : Blo 1285961 5948579 := bstep (se 1 (by rfl) ⟨4461434, by rfl⟩ : syracuseStep 5948579 = 8922869) B8922869
theorem B1287331 : Blo 1285961 1287331 := bstep (se 1 (by rfl) ⟨965498, by rfl⟩ : syracuseStep 1287331 = 1930997) B1930997
theorem B1287347 : Blo 1285961 1287347 := bstep (se 1 (by rfl) ⟨965510, by rfl⟩ : syracuseStep 1287347 = 1931021) B1931021
theorem B1287363 : Blo 1285961 1287363 := bstep (se 1 (by rfl) ⟨965522, by rfl⟩ : syracuseStep 1287363 = 1931045) B1931045
theorem B1287379 : Blo 1285961 1287379 := bstep (se 1 (by rfl) ⟨965534, by rfl⟩ : syracuseStep 1287379 = 1931069) B1931069
theorem B1287395 : Blo 1285961 1287395 := bstep (se 1 (by rfl) ⟨965546, by rfl⟩ : syracuseStep 1287395 = 1931093) B1931093
theorem B7628017 : Blo 1285961 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B3663089 : Blo 1285961 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B1287411 : Blo 1285961 1287411 := bstep (se 1 (by rfl) ⟨965558, by rfl⟩ : syracuseStep 1287411 = 1931117) B1931117
theorem B2172163 : Blo 1285961 2172163 := bstep (se 1 (by rfl) ⟨1629122, by rfl⟩ : syracuseStep 2172163 = 3258245) B3258245
theorem B1287427 : Blo 1285961 1287427 := bstep (se 1 (by rfl) ⟨965570, by rfl⟩ : syracuseStep 1287427 = 1931141) B1931141
theorem B4121873 : Blo 1285961 4121873 := bstep (se 2 (by rfl) ⟨1545702, by rfl⟩ : syracuseStep 4121873 = 3091405) B3091405
theorem B4343057 : Blo 1285961 4343057 := bstep (se 2 (by rfl) ⟨1628646, by rfl⟩ : syracuseStep 4343057 = 3257293) B3257293
theorem B1287443 : Blo 1285961 1287443 := bstep (se 1 (by rfl) ⟨965582, by rfl⟩ : syracuseStep 1287443 = 1931165) B1931165
theorem B1287459 : Blo 1285961 1287459 := bstep (se 1 (by rfl) ⟨965594, by rfl⟩ : syracuseStep 1287459 = 1931189) B1931189
theorem B2442545 : Blo 1285961 2442545 := bstep (se 2 (by rfl) ⟨915954, by rfl⟩ : syracuseStep 2442545 = 1831909) B1831909
theorem B1287475 : Blo 1285961 1287475 := bstep (se 1 (by rfl) ⟨965606, by rfl⟩ : syracuseStep 1287475 = 1931213) B1931213
theorem B1287491 : Blo 1285961 1287491 := bstep (se 1 (by rfl) ⟨965618, by rfl⟩ : syracuseStep 1287491 = 1931237) B1931237
theorem B1287507 : Blo 1285961 1287507 := bstep (se 1 (by rfl) ⟨965630, by rfl⟩ : syracuseStep 1287507 = 1931261) B1931261
theorem B6514019 : Blo 1285961 6514019 := bstep (se 1 (by rfl) ⟨4885514, by rfl⟩ : syracuseStep 6514019 = 9771029) B9771029
theorem B1287523 : Blo 1285961 1287523 := bstep (se 1 (by rfl) ⟨965642, by rfl⟩ : syracuseStep 1287523 = 1931285) B1931285
theorem B1287539 : Blo 1285961 1287539 := bstep (se 1 (by rfl) ⟨965654, by rfl⟩ : syracuseStep 1287539 = 1931309) B1931309
theorem B1287555 : Blo 1285961 1287555 := bstep (se 1 (by rfl) ⟨965666, by rfl⟩ : syracuseStep 1287555 = 1931333) B1931333
theorem B2172305 : Blo 1285961 2172305 := bstep (se 2 (by rfl) ⟨814614, by rfl⟩ : syracuseStep 2172305 = 1629229) B1629229
theorem B2090387 : Blo 1285961 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B1287571 : Blo 1285961 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B7431587 : Blo 1285961 7431587 := bstep (se 1 (by rfl) ⟨5573690, by rfl⟩ : syracuseStep 7431587 = 11147381) B11147381
theorem B1287587 : Blo 1285961 1287587 := bstep (se 1 (by rfl) ⟨965690, by rfl⟩ : syracuseStep 1287587 = 1931381) B1931381
theorem B1287603 : Blo 1285961 1287603 := bstep (se 1 (by rfl) ⟨965702, by rfl⟩ : syracuseStep 1287603 = 1931405) B1931405
theorem B1287619 : Blo 1285961 1287619 := bstep (se 1 (by rfl) ⟨965714, by rfl⟩ : syracuseStep 1287619 = 1931429) B1931429
theorem B1287635 : Blo 1285961 1287635 := bstep (se 1 (by rfl) ⟨965726, by rfl⟩ : syracuseStep 1287635 = 1931453) B1931453
theorem B1287651 : Blo 1285961 1287651 := bstep (se 1 (by rfl) ⟨965738, by rfl⟩ : syracuseStep 1287651 = 1931477) B1931477
theorem B1287667 : Blo 1285961 1287667 := bstep (se 1 (by rfl) ⟨965750, by rfl⟩ : syracuseStep 1287667 = 1931501) B1931501
theorem B1287683 : Blo 1285961 1287683 := bstep (se 1 (by rfl) ⟨965762, by rfl⟩ : syracuseStep 1287683 = 1931525) B1931525
theorem B2172433 : Blo 1285961 2172433 := bstep (se 2 (by rfl) ⟨814662, by rfl⟩ : syracuseStep 2172433 = 1629325) B1629325
theorem B1287699 : Blo 1285961 1287699 := bstep (se 1 (by rfl) ⟨965774, by rfl⟩ : syracuseStep 1287699 = 1931549) B1931549
theorem B1287715 : Blo 1285961 1287715 := bstep (se 1 (by rfl) ⟨965786, by rfl⟩ : syracuseStep 1287715 = 1931573) B1931573
theorem B2172467 : Blo 1285961 2172467 := bstep (se 1 (by rfl) ⟨1629350, by rfl⟩ : syracuseStep 2172467 = 3258701) B3258701
theorem B1287731 : Blo 1285961 1287731 := bstep (se 1 (by rfl) ⟨965798, by rfl⟩ : syracuseStep 1287731 = 1931597) B1931597
theorem B1287747 : Blo 1285961 1287747 := bstep (se 1 (by rfl) ⟨965810, by rfl⟩ : syracuseStep 1287747 = 1931621) B1931621
theorem B3090001 : Blo 1285961 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B1287763 : Blo 1285961 1287763 := bstep (se 1 (by rfl) ⟨965822, by rfl⟩ : syracuseStep 1287763 = 1931645) B1931645
theorem B1287779 : Blo 1285961 1287779 := bstep (se 1 (by rfl) ⟨965834, by rfl⟩ : syracuseStep 1287779 = 1931669) B1931669
theorem B1287795 : Blo 1285961 1287795 := bstep (se 1 (by rfl) ⟨965846, by rfl⟩ : syracuseStep 1287795 = 1931693) B1931693
theorem B1287811 : Blo 1285961 1287811 := bstep (se 1 (by rfl) ⟨965858, by rfl⟩ : syracuseStep 1287811 = 1931717) B1931717
theorem B7153285 : Blo 1285961 7153285 := bstep (se 4 (by rfl) ⟨670620, by rfl⟩ : syracuseStep 7153285 = 1341241) B1341241
theorem B1287827 : Blo 1285961 1287827 := bstep (se 1 (by rfl) ⟨965870, by rfl⟩ : syracuseStep 1287827 = 1931741) B1931741
theorem B1287843 : Blo 1285961 1287843 := bstep (se 1 (by rfl) ⟨965882, by rfl⟩ : syracuseStep 1287843 = 1931765) B1931765
theorem B2172595 : Blo 1285961 2172595 := bstep (se 1 (by rfl) ⟨1629446, by rfl⟩ : syracuseStep 2172595 = 3258893) B3258893
theorem B1287859 : Blo 1285961 1287859 := bstep (se 1 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 1287859 = 1931789) B1931789
theorem B1287875 : Blo 1285961 1287875 := bstep (se 1 (by rfl) ⟨965906, by rfl⟩ : syracuseStep 1287875 = 1931813) B1931813
theorem B18556613 : Blo 1285961 18556613 := bstep (se 4 (by rfl) ⟨1739682, by rfl⟩ : syracuseStep 18556613 = 3479365) B3479365
theorem B27846341 : Blo 1285961 27846341 := bstep (se 4 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 27846341 = 5221189) B5221189
theorem B1287891 : Blo 1285961 1287891 := bstep (se 1 (by rfl) ⟨965918, by rfl⟩ : syracuseStep 1287891 = 1931837) B1931837
theorem B1287907 : Blo 1285961 1287907 := bstep (se 1 (by rfl) ⟨965930, by rfl⟩ : syracuseStep 1287907 = 1931861) B1931861
theorem B2893553 : Blo 1285961 2893553 := bstep (se 2 (by rfl) ⟨1085082, by rfl⟩ : syracuseStep 2893553 = 2170165) B2170165
theorem B4884209 : Blo 1285961 4884209 := bstep (se 2 (by rfl) ⟨1831578, by rfl⟩ : syracuseStep 4884209 = 3663157) B3663157
theorem B1287923 : Blo 1285961 1287923 := bstep (se 1 (by rfl) ⟨965942, by rfl⟩ : syracuseStep 1287923 = 1931885) B1931885
theorem B2893571 : Blo 1285961 2893571 := bstep (se 1 (by rfl) ⟨2170178, by rfl⟩ : syracuseStep 2893571 = 4340357) B4340357
theorem B1287939 : Blo 1285961 1287939 := bstep (se 1 (by rfl) ⟨965954, by rfl⟩ : syracuseStep 1287939 = 1931909) B1931909
theorem B1287955 : Blo 1285961 1287955 := bstep (se 1 (by rfl) ⟨965966, by rfl⟩ : syracuseStep 1287955 = 1931933) B1931933
theorem B4343597 : Blo 1285961 4343597 := bstep (se 3 (by rfl) ⟨814424, by rfl⟩ : syracuseStep 4343597 = 1628849) B1628849
theorem B2172737 : Blo 1285961 2172737 := bstep (se 2 (by rfl) ⟨814776, by rfl⟩ : syracuseStep 2172737 = 1629553) B1629553
theorem B9774917 : Blo 1285961 9774917 := bstep (se 4 (by rfl) ⟨916398, by rfl⟩ : syracuseStep 9774917 = 1832797) B1832797
theorem B4343651 : Blo 1285961 4343651 := bstep (se 1 (by rfl) ⟨3257738, by rfl⟩ : syracuseStep 4343651 = 6515477) B6515477
theorem B2172865 : Blo 1285961 2172865 := bstep (se 2 (by rfl) ⟨814824, by rfl⟩ : syracuseStep 2172865 = 1629649) B1629649
theorem B2172899 : Blo 1285961 2172899 := bstep (se 1 (by rfl) ⟨1629674, by rfl⟩ : syracuseStep 2172899 = 3259349) B3259349
theorem B7333901 : Blo 1285961 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B2893841 : Blo 1285961 2893841 := bstep (se 2 (by rfl) ⟨1085190, by rfl⟩ : syracuseStep 2893841 = 2170381) B2170381
theorem B2893859 : Blo 1285961 2893859 := bstep (se 1 (by rfl) ⟨2170394, by rfl⟩ : syracuseStep 2893859 = 4340789) B4340789
theorem B4950065 : Blo 1285961 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B2173027 : Blo 1285961 2173027 := bstep (se 1 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 2173027 = 3259541) B3259541
theorem B4343921 : Blo 1285961 4343921 := bstep (se 2 (by rfl) ⟨1628970, by rfl⟩ : syracuseStep 4343921 = 3257941) B3257941
theorem B6514829 : Blo 1285961 6514829 := bstep (se 3 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 6514829 = 2443061) B2443061
theorem B3664045 : Blo 1285961 3664045 := bstep (se 3 (by rfl) ⟨687008, by rfl⟩ : syracuseStep 3664045 = 1374017) B1374017
theorem B2443441 : Blo 1285961 2443441 := bstep (se 2 (by rfl) ⟨916290, by rfl⟩ : syracuseStep 2443441 = 1832581) B1832581
theorem B2173169 : Blo 1285961 2173169 := bstep (se 2 (by rfl) ⟨814938, by rfl⟩ : syracuseStep 2173169 = 1629877) B1629877
theorem B2894129 : Blo 1285961 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B2894147 : Blo 1285961 2894147 := bstep (se 1 (by rfl) ⟨2170610, by rfl⟩ : syracuseStep 2894147 = 4341221) B4341221
theorem B2443601 : Blo 1285961 2443601 := bstep (se 2 (by rfl) ⟨916350, by rfl⟩ : syracuseStep 2443601 = 1832701) B1832701
theorem B2173297 : Blo 1285961 2173297 := bstep (se 2 (by rfl) ⟨814986, by rfl⟩ : syracuseStep 2173297 = 1629973) B1629973
theorem B7326085 : Blo 1285961 7326085 := bstep (se 4 (by rfl) ⟨686820, by rfl⟩ : syracuseStep 7326085 = 1373641) B1373641
theorem B3664273 : Blo 1285961 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B2173331 : Blo 1285961 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B2320817 : Blo 1285961 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B2746865 : Blo 1285961 2746865 := bstep (se 2 (by rfl) ⟨1030074, by rfl⟩ : syracuseStep 2746865 = 2060149) B2060149
theorem B3664433 : Blo 1285961 3664433 := bstep (se 2 (by rfl) ⟨1374162, by rfl⟩ : syracuseStep 3664433 = 2748325) B2748325
theorem B2894417 : Blo 1285961 2894417 := bstep (se 2 (by rfl) ⟨1085406, by rfl⟩ : syracuseStep 2894417 = 2170813) B2170813
theorem B2894435 : Blo 1285961 2894435 := bstep (se 1 (by rfl) ⟨2170826, by rfl⟩ : syracuseStep 2894435 = 4341653) B4341653
theorem B4344461 : Blo 1285961 4344461 := bstep (se 3 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 4344461 = 1629173) B1629173
theorem B1288867 : Blo 1285961 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B3664547 : Blo 1285961 3664547 := bstep (se 1 (by rfl) ⟨2748410, by rfl⟩ : syracuseStep 3664547 = 5496821) B5496821
theorem B4344515 : Blo 1285961 4344515 := bstep (se 1 (by rfl) ⟨3258386, by rfl⟩ : syracuseStep 4344515 = 6516773) B6516773
theorem B2444003 : Blo 1285961 2444003 := bstep (se 1 (by rfl) ⟨1833002, by rfl⟩ : syracuseStep 2444003 = 3666005) B3666005
theorem B9276229 : Blo 1285961 9276229 := bstep (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) B1739293
theorem B2894705 : Blo 1285961 2894705 := bstep (se 2 (by rfl) ⟨1085514, by rfl⟩ : syracuseStep 2894705 = 2171029) B2171029
theorem B2894723 : Blo 1285961 2894723 := bstep (se 1 (by rfl) ⟨2171042, by rfl⟩ : syracuseStep 2894723 = 4342085) B4342085
theorem B2608049 : Blo 1285961 2608049 := bstep (se 2 (by rfl) ⟨978018, by rfl⟩ : syracuseStep 2608049 = 1956037) B1956037
theorem B7334833 : Blo 1285961 7334833 := bstep (se 2 (by rfl) ⟨2750562, by rfl⟩ : syracuseStep 7334833 = 5501125) B5501125
theorem B4344785 : Blo 1285961 4344785 := bstep (se 2 (by rfl) ⟨1629294, by rfl⟩ : syracuseStep 4344785 = 3258589) B3258589
theorem B3255299 : Blo 1285961 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B46967921 : Blo 1285961 46967921 := bstep (se 2 (by rfl) ⟨17612970, by rfl⟩ : syracuseStep 46967921 = 35225941) B35225941
theorem B2894993 : Blo 1285961 2894993 := bstep (se 2 (by rfl) ⟨1085622, by rfl⟩ : syracuseStep 2894993 = 2171245) B2171245
theorem B2608291 : Blo 1285961 2608291 := bstep (se 1 (by rfl) ⟨1956218, by rfl⟩ : syracuseStep 2608291 = 3912437) B3912437
theorem B2895011 : Blo 1285961 2895011 := bstep (se 1 (by rfl) ⟨2171258, by rfl⟩ : syracuseStep 2895011 = 4342517) B4342517
theorem B4885667 : Blo 1285961 4885667 := bstep (se 1 (by rfl) ⟨3664250, by rfl⟩ : syracuseStep 4885667 = 7328501) B7328501
theorem B3255491 : Blo 1285961 3255491 := bstep (se 1 (by rfl) ⟨2441618, by rfl⟩ : syracuseStep 3255491 = 4883237) B4883237
theorem B4639949 : Blo 1285961 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B4123885 : Blo 1285961 4123885 := bstep (se 3 (by rfl) ⟨773228, by rfl⟩ : syracuseStep 4123885 = 1546457) B1546457
theorem B13389041 : Blo 1285961 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B7826723 : Blo 1285961 7826723 := bstep (se 1 (by rfl) ⟨5870042, by rfl⟩ : syracuseStep 7826723 = 11740085) B11740085
theorem B5500237 : Blo 1285961 5500237 := bstep (se 3 (by rfl) ⟨1031294, by rfl⟩ : syracuseStep 5500237 = 2062589) B2062589
theorem B2895281 : Blo 1285961 2895281 := bstep (se 2 (by rfl) ⟨1085730, by rfl⟩ : syracuseStep 2895281 = 2171461) B2171461
theorem B2895299 : Blo 1285961 2895299 := bstep (se 1 (by rfl) ⟨2171474, by rfl⟩ : syracuseStep 2895299 = 4342949) B4342949
theorem B4345325 : Blo 1285961 4345325 := bstep (se 3 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 4345325 = 1629497) B1629497
theorem B4345379 : Blo 1285961 4345379 := bstep (se 1 (by rfl) ⟨3259034, by rfl⟩ : syracuseStep 4345379 = 6518069) B6518069
theorem B7826993 : Blo 1285961 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B13913653 : Blo 1285961 13913653 := bstep (se 5 (by rfl) ⟨652202, by rfl⟩ : syracuseStep 13913653 = 1304405) B1304405
theorem B2444899 : Blo 1285961 2444899 := bstep (se 1 (by rfl) ⟨1833674, by rfl⟩ : syracuseStep 2444899 = 3667349) B3667349
theorem B5869169 : Blo 1285961 5869169 := bstep (se 2 (by rfl) ⟨2200938, by rfl⟩ : syracuseStep 5869169 = 4401877) B4401877
theorem B3665549 : Blo 1285961 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B8244899 : Blo 1285961 8244899 := bstep (se 1 (by rfl) ⟨6183674, by rfl⟩ : syracuseStep 8244899 = 12367349) B12367349
theorem B4124333 : Blo 1285961 4124333 := bstep (se 3 (by rfl) ⟨773312, by rfl⟩ : syracuseStep 4124333 = 1546625) B1546625
theorem B2895569 : Blo 1285961 2895569 := bstep (se 2 (by rfl) ⟨1085838, by rfl⟩ : syracuseStep 2895569 = 2171677) B2171677
theorem B2895587 : Blo 1285961 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B1928945 : Blo 1285961 1928945 := bstep (se 2 (by rfl) ⟨723354, by rfl⟩ : syracuseStep 1928945 = 1446709) B1446709
theorem B1928963 : Blo 1285961 1928963 := bstep (se 1 (by rfl) ⟨1446722, by rfl⟩ : syracuseStep 1928963 = 2893445) B2893445
theorem B2748163 : Blo 1285961 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B2445059 : Blo 1285961 2445059 := bstep (se 1 (by rfl) ⟨1833794, by rfl⟩ : syracuseStep 2445059 = 3667589) B3667589
theorem B1928993 : Blo 1285961 1928993 := bstep (se 2 (by rfl) ⟨723372, by rfl⟩ : syracuseStep 1928993 = 1446745) B1446745
theorem B4345649 : Blo 1285961 4345649 := bstep (se 2 (by rfl) ⟨1629618, by rfl⟩ : syracuseStep 4345649 = 3259237) B3259237
theorem B2477873 : Blo 1285961 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B1929011 : Blo 1285961 1929011 := bstep (se 1 (by rfl) ⟨1446758, by rfl⟩ : syracuseStep 1929011 = 2893517) B2893517
theorem B3665731 : Blo 1285961 3665731 := bstep (se 1 (by rfl) ⟨2749298, by rfl⟩ : syracuseStep 3665731 = 5498597) B5498597
theorem B1929041 : Blo 1285961 1929041 := bstep (se 2 (by rfl) ⟨723390, by rfl⟩ : syracuseStep 1929041 = 1446781) B1446781
theorem B2060129 : Blo 1285961 2060129 := bstep (se 2 (by rfl) ⟨772548, by rfl⟩ : syracuseStep 2060129 = 1545097) B1545097
theorem B1929059 : Blo 1285961 1929059 := bstep (se 1 (by rfl) ⟨1446794, by rfl⟩ : syracuseStep 1929059 = 2893589) B2893589
theorem B10997603 : Blo 1285961 10997603 := bstep (se 1 (by rfl) ⟨8248202, by rfl⟩ : syracuseStep 10997603 = 16496405) B16496405
theorem B1929089 : Blo 1285961 1929089 := bstep (se 2 (by rfl) ⟨723408, by rfl⟩ : syracuseStep 1929089 = 1446817) B1446817
theorem B1929107 : Blo 1285961 1929107 := bstep (se 1 (by rfl) ⟨1446830, by rfl⟩ : syracuseStep 1929107 = 2893661) B2893661
theorem B1929137 : Blo 1285961 1929137 := bstep (se 2 (by rfl) ⟨723426, by rfl⟩ : syracuseStep 1929137 = 1446853) B1446853
theorem B1929155 : Blo 1285961 1929155 := bstep (se 1 (by rfl) ⟨1446866, by rfl⟩ : syracuseStep 1929155 = 2893733) B2893733
theorem B1929185 : Blo 1285961 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B2060257 : Blo 1285961 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B10989539 : Blo 1285961 10989539 := bstep (se 1 (by rfl) ⟨8242154, by rfl⟩ : syracuseStep 10989539 = 16484309) B16484309
theorem B3665891 : Blo 1285961 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B3477485 : Blo 1285961 3477485 := bstep (se 3 (by rfl) ⟨652028, by rfl⟩ : syracuseStep 3477485 = 1304057) B1304057
theorem B2895857 : Blo 1285961 2895857 := bstep (se 2 (by rfl) ⟨1085946, by rfl⟩ : syracuseStep 2895857 = 2171893) B2171893
theorem B1929203 : Blo 1285961 1929203 := bstep (se 1 (by rfl) ⟨1446902, by rfl⟩ : syracuseStep 1929203 = 2893805) B2893805
theorem B2895875 : Blo 1285961 2895875 := bstep (se 1 (by rfl) ⟨2171906, by rfl⟩ : syracuseStep 2895875 = 4343813) B4343813
theorem B1929233 : Blo 1285961 1929233 := bstep (se 2 (by rfl) ⟨723462, by rfl⟩ : syracuseStep 1929233 = 1446925) B1446925
theorem B2060321 : Blo 1285961 2060321 := bstep (se 2 (by rfl) ⟨772620, by rfl⟩ : syracuseStep 2060321 = 1545241) B1545241
theorem B1929251 : Blo 1285961 1929251 := bstep (se 1 (by rfl) ⟨1446938, by rfl⟩ : syracuseStep 1929251 = 2893877) B2893877
theorem B1929281 : Blo 1285961 1929281 := bstep (se 2 (by rfl) ⟨723480, by rfl⟩ : syracuseStep 1929281 = 1446961) B1446961
theorem B1929299 : Blo 1285961 1929299 := bstep (se 1 (by rfl) ⟨1446974, by rfl⟩ : syracuseStep 1929299 = 2893949) B2893949
theorem B1929329 : Blo 1285961 1929329 := bstep (se 2 (by rfl) ⟨723498, by rfl⟩ : syracuseStep 1929329 = 1446997) B1446997
theorem B3256433 : Blo 1285961 3256433 := bstep (se 2 (by rfl) ⟨1221162, by rfl⟩ : syracuseStep 3256433 = 2442325) B2442325
theorem B1831043 : Blo 1285961 1831043 := bstep (se 1 (by rfl) ⟨1373282, by rfl⟩ : syracuseStep 1831043 = 2746565) B2746565
theorem B1929347 : Blo 1285961 1929347 := bstep (se 1 (by rfl) ⟨1447010, by rfl⟩ : syracuseStep 1929347 = 2894021) B2894021
theorem B4886669 : Blo 1285961 4886669 := bstep (se 3 (by rfl) ⟨916250, by rfl⟩ : syracuseStep 4886669 = 1832501) B1832501
theorem B1929377 : Blo 1285961 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B3911843 : Blo 1285961 3911843 := bstep (se 1 (by rfl) ⟨2933882, by rfl⟩ : syracuseStep 3911843 = 5867765) B5867765
theorem B3256483 : Blo 1285961 3256483 := bstep (se 1 (by rfl) ⟨2442362, by rfl⟩ : syracuseStep 3256483 = 4884725) B4884725
theorem B1929395 : Blo 1285961 1929395 := bstep (se 1 (by rfl) ⟨1447046, by rfl⟩ : syracuseStep 1929395 = 2894093) B2894093
theorem B1929425 : Blo 1285961 1929425 := bstep (se 2 (by rfl) ⟨723534, by rfl⟩ : syracuseStep 1929425 = 1447069) B1447069
theorem B1831123 : Blo 1285961 1831123 := bstep (se 1 (by rfl) ⟨1373342, by rfl⟩ : syracuseStep 1831123 = 2746685) B2746685
theorem B1929443 : Blo 1285961 1929443 := bstep (se 1 (by rfl) ⟨1447082, by rfl⟩ : syracuseStep 1929443 = 2894165) B2894165
theorem B1929473 : Blo 1285961 1929473 := bstep (se 2 (by rfl) ⟨723552, by rfl⟩ : syracuseStep 1929473 = 1447105) B1447105
theorem B2896145 : Blo 1285961 2896145 := bstep (se 2 (by rfl) ⟨1086054, by rfl⟩ : syracuseStep 2896145 = 2172109) B2172109
theorem B1929491 : Blo 1285961 1929491 := bstep (se 1 (by rfl) ⟨1447118, by rfl⟩ : syracuseStep 1929491 = 2894237) B2894237
theorem B2896163 : Blo 1285961 2896163 := bstep (se 1 (by rfl) ⟨2172122, by rfl⟩ : syracuseStep 2896163 = 4344245) B4344245
theorem B1929521 : Blo 1285961 1929521 := bstep (se 2 (by rfl) ⟨723570, by rfl⟩ : syracuseStep 1929521 = 1447141) B1447141
theorem B3256625 : Blo 1285961 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B3477809 : Blo 1285961 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1929539 : Blo 1285961 1929539 := bstep (se 1 (by rfl) ⟨1447154, by rfl⟩ : syracuseStep 1929539 = 2894309) B2894309
theorem B7328069 : Blo 1285961 7328069 := bstep (se 4 (by rfl) ⟨687006, by rfl⟩ : syracuseStep 7328069 = 1374013) B1374013
theorem B4346189 : Blo 1285961 4346189 := bstep (se 3 (by rfl) ⟨814910, by rfl⟩ : syracuseStep 4346189 = 1629821) B1629821
theorem B1929569 : Blo 1285961 1929569 := bstep (se 2 (by rfl) ⟨723588, by rfl⟩ : syracuseStep 1929569 = 1447177) B1447177
theorem B5501297 : Blo 1285961 5501297 := bstep (se 2 (by rfl) ⟨2062986, by rfl⟩ : syracuseStep 5501297 = 4125973) B4125973
theorem B1929587 : Blo 1285961 1929587 := bstep (se 1 (by rfl) ⟨1447190, by rfl⟩ : syracuseStep 1929587 = 2894381) B2894381
theorem B3092867 : Blo 1285961 3092867 := bstep (se 1 (by rfl) ⟨2319650, by rfl⟩ : syracuseStep 3092867 = 4639301) B4639301
theorem B4346243 : Blo 1285961 4346243 := bstep (se 1 (by rfl) ⟨3259682, by rfl⟩ : syracuseStep 4346243 = 6519365) B6519365
theorem B20083085 : Blo 1285961 20083085 := bstep (se 3 (by rfl) ⟨3765578, by rfl⟩ : syracuseStep 20083085 = 7531157) B7531157
theorem B1929617 : Blo 1285961 1929617 := bstep (se 2 (by rfl) ⟨723606, by rfl⟩ : syracuseStep 1929617 = 1447213) B1447213
theorem B1929635 : Blo 1285961 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B1929665 : Blo 1285961 1929665 := bstep (se 2 (by rfl) ⟨723624, by rfl⟩ : syracuseStep 1929665 = 1447249) B1447249
theorem B5493197 : Blo 1285961 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B1929683 : Blo 1285961 1929683 := bstep (se 1 (by rfl) ⟨1447262, by rfl⟩ : syracuseStep 1929683 = 2894525) B2894525
theorem B6607331 : Blo 1285961 6607331 := bstep (se 1 (by rfl) ⟨4955498, by rfl⟩ : syracuseStep 6607331 = 9910997) B9910997
theorem B1929713 : Blo 1285961 1929713 := bstep (se 2 (by rfl) ⟨723642, by rfl⟩ : syracuseStep 1929713 = 1447285) B1447285
theorem B1929731 : Blo 1285961 1929731 := bstep (se 1 (by rfl) ⟨1447298, by rfl⟩ : syracuseStep 1929731 = 2894597) B2894597
theorem B1929761 : Blo 1285961 1929761 := bstep (se 2 (by rfl) ⟨723660, by rfl⟩ : syracuseStep 1929761 = 1447321) B1447321
theorem B2896433 : Blo 1285961 2896433 := bstep (se 2 (by rfl) ⟨1086162, by rfl⟩ : syracuseStep 2896433 = 2172325) B2172325
theorem B1929779 : Blo 1285961 1929779 := bstep (se 1 (by rfl) ⟨1447334, by rfl⟩ : syracuseStep 1929779 = 2894669) B2894669
theorem B2896451 : Blo 1285961 2896451 := bstep (se 1 (by rfl) ⟨2172338, by rfl⟩ : syracuseStep 2896451 = 4344677) B4344677
theorem B1929809 : Blo 1285961 1929809 := bstep (se 2 (by rfl) ⟨723678, by rfl⟩ : syracuseStep 1929809 = 1447357) B1447357
theorem B9769571 : Blo 1285961 9769571 := bstep (se 1 (by rfl) ⟨7327178, by rfl⟩ : syracuseStep 9769571 = 14654357) B14654357
theorem B1929827 : Blo 1285961 1929827 := bstep (se 1 (by rfl) ⟨1447370, by rfl⟩ : syracuseStep 1929827 = 2894741) B2894741
theorem B4403821 : Blo 1285961 4403821 := bstep (se 3 (by rfl) ⟨825716, by rfl⟩ : syracuseStep 4403821 = 1651433) B1651433
theorem B1929857 : Blo 1285961 1929857 := bstep (se 2 (by rfl) ⟨723696, by rfl⟩ : syracuseStep 1929857 = 1447393) B1447393
theorem B4346513 : Blo 1285961 4346513 := bstep (se 2 (by rfl) ⟨1629942, by rfl⟩ : syracuseStep 4346513 = 3259885) B3259885
theorem B1929875 : Blo 1285961 1929875 := bstep (se 1 (by rfl) ⟨1447406, by rfl⟩ : syracuseStep 1929875 = 2894813) B2894813
theorem B1929905 : Blo 1285961 1929905 := bstep (se 2 (by rfl) ⟨723714, by rfl⟩ : syracuseStep 1929905 = 1447429) B1447429
theorem B1929923 : Blo 1285961 1929923 := bstep (se 1 (by rfl) ⟨1447442, by rfl⟩ : syracuseStep 1929923 = 2894885) B2894885
theorem B1929953 : Blo 1285961 1929953 := bstep (se 2 (by rfl) ⟨723732, by rfl⟩ : syracuseStep 1929953 = 1447465) B1447465
theorem B1929971 : Blo 1285961 1929971 := bstep (se 1 (by rfl) ⟨1447478, by rfl⟩ : syracuseStep 1929971 = 2894957) B2894957
theorem B1831681 : Blo 1285961 1831681 := bstep (se 2 (by rfl) ⟨686880, by rfl⟩ : syracuseStep 1831681 = 1373761) B1373761
theorem B1930001 : Blo 1285961 1930001 := bstep (se 2 (by rfl) ⟨723750, by rfl⟩ : syracuseStep 1930001 = 1447501) B1447501
theorem B1930019 : Blo 1285961 1930019 := bstep (se 1 (by rfl) ⟨1447514, by rfl⟩ : syracuseStep 1930019 = 2895029) B2895029
theorem B1930049 : Blo 1285961 1930049 := bstep (se 2 (by rfl) ⟨723768, by rfl⟩ : syracuseStep 1930049 = 1447537) B1447537
theorem B2896721 : Blo 1285961 2896721 := bstep (se 2 (by rfl) ⟨1086270, by rfl⟩ : syracuseStep 2896721 = 2172541) B2172541
theorem B1930067 : Blo 1285961 1930067 := bstep (se 1 (by rfl) ⟨1447550, by rfl⟩ : syracuseStep 1930067 = 2895101) B2895101
theorem B9900899 : Blo 1285961 9900899 := bstep (se 1 (by rfl) ⟨7425674, by rfl⟩ : syracuseStep 9900899 = 14851349) B14851349
theorem B2896739 : Blo 1285961 2896739 := bstep (se 1 (by rfl) ⟨2172554, by rfl⟩ : syracuseStep 2896739 = 4345109) B4345109
theorem B1930097 : Blo 1285961 1930097 := bstep (se 2 (by rfl) ⟨723786, by rfl⟩ : syracuseStep 1930097 = 1447573) B1447573
theorem B1930115 : Blo 1285961 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B1930145 : Blo 1285961 1930145 := bstep (se 2 (by rfl) ⟨723804, by rfl⟩ : syracuseStep 1930145 = 1447609) B1447609
theorem B1446835 : Blo 1285961 1446835 := bstep (se 1 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 1446835 = 2170253) B2170253
theorem B1930163 : Blo 1285961 1930163 := bstep (se 1 (by rfl) ⟨1447622, by rfl⟩ : syracuseStep 1930163 = 2895245) B2895245
theorem B1930193 : Blo 1285961 1930193 := bstep (se 2 (by rfl) ⟨723822, by rfl⟩ : syracuseStep 1930193 = 1447645) B1447645
theorem B2749393 : Blo 1285961 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B1930211 : Blo 1285961 1930211 := bstep (se 1 (by rfl) ⟨1447658, by rfl⟩ : syracuseStep 1930211 = 2895317) B2895317
theorem B3527651 : Blo 1285961 3527651 := bstep (se 1 (by rfl) ⟨2645738, by rfl⟩ : syracuseStep 3527651 = 5291477) B5291477
theorem B8803313 : Blo 1285961 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B6517745 : Blo 1285961 6517745 := bstep (se 2 (by rfl) ⟨2444154, by rfl⟩ : syracuseStep 6517745 = 4888309) B4888309
theorem B1545203 : Blo 1285961 1545203 := bstep (se 1 (by rfl) ⟨1158902, by rfl⟩ : syracuseStep 1545203 = 2317805) B2317805
theorem B1930241 : Blo 1285961 1930241 := bstep (se 2 (by rfl) ⟨723840, by rfl⟩ : syracuseStep 1930241 = 1447681) B1447681
theorem B3666961 : Blo 1285961 3666961 := bstep (se 2 (by rfl) ⟨1375110, by rfl⟩ : syracuseStep 3666961 = 2750221) B2750221
theorem B1930259 : Blo 1285961 1930259 := bstep (se 1 (by rfl) ⟨1447694, by rfl⟩ : syracuseStep 1930259 = 2895389) B2895389
theorem B4641805 : Blo 1285961 4641805 := bstep (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) B1740677
theorem B1930289 : Blo 1285961 1930289 := bstep (se 2 (by rfl) ⟨723858, by rfl⟩ : syracuseStep 1930289 = 1447717) B1447717
theorem B1446979 : Blo 1285961 1446979 := bstep (se 1 (by rfl) ⟨1085234, by rfl⟩ : syracuseStep 1446979 = 2170469) B2170469
theorem B1930307 : Blo 1285961 1930307 := bstep (se 1 (by rfl) ⟨1447730, by rfl⟩ : syracuseStep 1930307 = 2895461) B2895461
theorem B2061379 : Blo 1285961 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B1930337 : Blo 1285961 1930337 := bstep (se 2 (by rfl) ⟨723876, by rfl⟩ : syracuseStep 1930337 = 1447753) B1447753
theorem B2897009 : Blo 1285961 2897009 := bstep (se 2 (by rfl) ⟨1086378, by rfl⟩ : syracuseStep 2897009 = 2172757) B2172757
theorem B1930355 : Blo 1285961 1930355 := bstep (se 1 (by rfl) ⟨1447766, by rfl⟩ : syracuseStep 1930355 = 2895533) B2895533
theorem B2897027 : Blo 1285961 2897027 := bstep (se 1 (by rfl) ⟨2172770, by rfl⟩ : syracuseStep 2897027 = 4345541) B4345541
theorem B1930385 : Blo 1285961 1930385 := bstep (se 2 (by rfl) ⟨723894, by rfl⟩ : syracuseStep 1930385 = 1447789) B1447789
theorem B1930403 : Blo 1285961 1930403 := bstep (se 1 (by rfl) ⟨1447802, by rfl⟩ : syracuseStep 1930403 = 2895605) B2895605
theorem B1930433 : Blo 1285961 1930433 := bstep (se 2 (by rfl) ⟨723912, by rfl⟩ : syracuseStep 1930433 = 1447825) B1447825
theorem B1447123 : Blo 1285961 1447123 := bstep (se 1 (by rfl) ⟨1085342, by rfl⟩ : syracuseStep 1447123 = 2170685) B2170685
theorem B1930451 : Blo 1285961 1930451 := bstep (se 1 (by rfl) ⟨1447838, by rfl⟩ : syracuseStep 1930451 = 2895677) B2895677
theorem B12367075 : Blo 1285961 12367075 := bstep (se 1 (by rfl) ⟨9275306, by rfl⟩ : syracuseStep 12367075 = 18550613) B18550613
theorem B1930481 : Blo 1285961 1930481 := bstep (se 2 (by rfl) ⟨723930, by rfl⟩ : syracuseStep 1930481 = 1447861) B1447861
theorem B1930499 : Blo 1285961 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B3257617 : Blo 1285961 3257617 := bstep (se 2 (by rfl) ⟨1221606, by rfl⟩ : syracuseStep 3257617 = 2443213) B2443213
theorem B1930529 : Blo 1285961 1930529 := bstep (se 2 (by rfl) ⟨723948, by rfl⟩ : syracuseStep 1930529 = 1447897) B1447897
theorem B1930547 : Blo 1285961 1930547 := bstep (se 1 (by rfl) ⟨1447910, by rfl⟩ : syracuseStep 1930547 = 2895821) B2895821
theorem B1930577 : Blo 1285961 1930577 := bstep (se 2 (by rfl) ⟨723966, by rfl⟩ : syracuseStep 1930577 = 1447933) B1447933
theorem B1447267 : Blo 1285961 1447267 := bstep (se 1 (by rfl) ⟨1085450, by rfl⟩ : syracuseStep 1447267 = 2170901) B2170901
theorem B1930595 : Blo 1285961 1930595 := bstep (se 1 (by rfl) ⟨1447946, by rfl⟩ : syracuseStep 1930595 = 2895893) B2895893
theorem B1930625 : Blo 1285961 1930625 := bstep (se 2 (by rfl) ⟨723984, by rfl⟩ : syracuseStep 1930625 = 1447969) B1447969
theorem B2897297 : Blo 1285961 2897297 := bstep (se 2 (by rfl) ⟨1086486, by rfl⟩ : syracuseStep 2897297 = 2172973) B2172973
theorem B1930643 : Blo 1285961 1930643 := bstep (se 1 (by rfl) ⟨1447982, by rfl⟩ : syracuseStep 1930643 = 2895965) B2895965
theorem B1373603 : Blo 1285961 1373603 := bstep (se 1 (by rfl) ⟨1030202, by rfl⟩ : syracuseStep 1373603 = 2060405) B2060405
theorem B2897315 : Blo 1285961 2897315 := bstep (se 1 (by rfl) ⟨2172986, by rfl⟩ : syracuseStep 2897315 = 4345973) B4345973
theorem B1930673 : Blo 1285961 1930673 := bstep (se 2 (by rfl) ⟨724002, by rfl⟩ : syracuseStep 1930673 = 1448005) B1448005
theorem B1832387 : Blo 1285961 1832387 := bstep (se 1 (by rfl) ⟨1374290, by rfl⟩ : syracuseStep 1832387 = 2748581) B2748581
theorem B1930691 : Blo 1285961 1930691 := bstep (se 1 (by rfl) ⟨1448018, by rfl⟩ : syracuseStep 1930691 = 2896037) B2896037
theorem B1930721 : Blo 1285961 1930721 := bstep (se 2 (by rfl) ⟨724020, by rfl⟩ : syracuseStep 1930721 = 1448041) B1448041
theorem B12056035 : Blo 1285961 12056035 := bstep (se 1 (by rfl) ⟨9042026, by rfl⟩ : syracuseStep 12056035 = 18084053) B18084053
theorem B14652899 : Blo 1285961 14652899 := bstep (se 1 (by rfl) ⟨10989674, by rfl⟩ : syracuseStep 14652899 = 21979349) B21979349
theorem B3479021 : Blo 1285961 3479021 := bstep (se 3 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 3479021 = 1304633) B1304633
theorem B1447411 : Blo 1285961 1447411 := bstep (se 1 (by rfl) ⟨1085558, by rfl⟩ : syracuseStep 1447411 = 2171117) B2171117
theorem B1930739 : Blo 1285961 1930739 := bstep (se 1 (by rfl) ⟨1448054, by rfl⟩ : syracuseStep 1930739 = 2896109) B2896109
theorem B1930769 : Blo 1285961 1930769 := bstep (se 2 (by rfl) ⟨724038, by rfl⟩ : syracuseStep 1930769 = 1448077) B1448077
theorem B3257891 : Blo 1285961 3257891 := bstep (se 1 (by rfl) ⟨2443418, by rfl⟩ : syracuseStep 3257891 = 4886837) B4886837
theorem B1930787 : Blo 1285961 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B1627715 : Blo 1285961 1627715 := bstep (se 1 (by rfl) ⟨1220786, by rfl⟩ : syracuseStep 1627715 = 2441573) B2441573
theorem B1930817 : Blo 1285961 1930817 := bstep (se 2 (by rfl) ⟨724056, by rfl⟩ : syracuseStep 1930817 = 1448113) B1448113
theorem B1930835 : Blo 1285961 1930835 := bstep (se 1 (by rfl) ⟨1448126, by rfl⟩ : syracuseStep 1930835 = 2896253) B2896253
theorem B2750051 : Blo 1285961 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B1930865 : Blo 1285961 1930865 := bstep (se 2 (by rfl) ⟨724074, by rfl⟩ : syracuseStep 1930865 = 1448149) B1448149
theorem B1447555 : Blo 1285961 1447555 := bstep (se 1 (by rfl) ⟨1085666, by rfl⟩ : syracuseStep 1447555 = 2171333) B2171333
theorem B1930883 : Blo 1285961 1930883 := bstep (se 1 (by rfl) ⟨1448162, by rfl⟩ : syracuseStep 1930883 = 2896325) B2896325
theorem B1930913 : Blo 1285961 1930913 := bstep (se 2 (by rfl) ⟨724092, by rfl⟩ : syracuseStep 1930913 = 1448185) B1448185
theorem B2897585 : Blo 1285961 2897585 := bstep (se 2 (by rfl) ⟨1086594, by rfl⟩ : syracuseStep 2897585 = 2173189) B2173189
theorem B1930931 : Blo 1285961 1930931 := bstep (se 1 (by rfl) ⟨1448198, by rfl⟩ : syracuseStep 1930931 = 2896397) B2896397
theorem B1545923 : Blo 1285961 1545923 := bstep (se 1 (by rfl) ⟨1159442, by rfl⟩ : syracuseStep 1545923 = 2318885) B2318885
theorem B2897603 : Blo 1285961 2897603 := bstep (se 1 (by rfl) ⟨2173202, by rfl⟩ : syracuseStep 2897603 = 4346405) B4346405
theorem B1930961 : Blo 1285961 1930961 := bstep (se 2 (by rfl) ⟨724110, by rfl⟩ : syracuseStep 1930961 = 1448221) B1448221
theorem B6952675 : Blo 1285961 6952675 := bstep (se 1 (by rfl) ⟨5214506, by rfl⟩ : syracuseStep 6952675 = 10429013) B10429013
theorem B3258083 : Blo 1285961 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B1930979 : Blo 1285961 1930979 := bstep (se 1 (by rfl) ⟨1448234, by rfl⟩ : syracuseStep 1930979 = 2896469) B2896469
theorem B1931009 : Blo 1285961 1931009 := bstep (se 2 (by rfl) ⟨724128, by rfl⟩ : syracuseStep 1931009 = 1448257) B1448257
theorem B1447699 : Blo 1285961 1447699 := bstep (se 1 (by rfl) ⟨1085774, by rfl⟩ : syracuseStep 1447699 = 2171549) B2171549
theorem B1931027 : Blo 1285961 1931027 := bstep (se 1 (by rfl) ⟨1448270, by rfl⟩ : syracuseStep 1931027 = 2896541) B2896541
theorem B1931057 : Blo 1285961 1931057 := bstep (se 2 (by rfl) ⟨724146, by rfl⟩ : syracuseStep 1931057 = 1448293) B1448293
theorem B1931075 : Blo 1285961 1931075 := bstep (se 1 (by rfl) ⟨1448306, by rfl⟩ : syracuseStep 1931075 = 2896613) B2896613
theorem B1931105 : Blo 1285961 1931105 := bstep (se 2 (by rfl) ⟨724164, by rfl⟩ : syracuseStep 1931105 = 1448329) B1448329
theorem B1931123 : Blo 1285961 1931123 := bstep (se 1 (by rfl) ⟨1448342, by rfl⟩ : syracuseStep 1931123 = 2896685) B2896685
theorem B1931153 : Blo 1285961 1931153 := bstep (se 2 (by rfl) ⟨724182, by rfl⟩ : syracuseStep 1931153 = 1448365) B1448365
theorem B1447843 : Blo 1285961 1447843 := bstep (se 1 (by rfl) ⟨1085882, by rfl⟩ : syracuseStep 1447843 = 2171765) B2171765
theorem B1931171 : Blo 1285961 1931171 := bstep (se 1 (by rfl) ⟨1448378, by rfl⟩ : syracuseStep 1931171 = 2896757) B2896757
theorem B1931201 : Blo 1285961 1931201 := bstep (se 2 (by rfl) ⟨724200, by rfl⟩ : syracuseStep 1931201 = 1448401) B1448401
theorem B2897873 : Blo 1285961 2897873 := bstep (se 2 (by rfl) ⟨1086702, by rfl⟩ : syracuseStep 2897873 = 2173405) B2173405
theorem B1931219 : Blo 1285961 1931219 := bstep (se 1 (by rfl) ⟨1448414, by rfl⟩ : syracuseStep 1931219 = 2896829) B2896829
theorem B2062307 : Blo 1285961 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B3094499 : Blo 1285961 3094499 := bstep (se 1 (by rfl) ⟨2320874, by rfl⟩ : syracuseStep 3094499 = 4641749) B4641749
theorem B2897891 : Blo 1285961 2897891 := bstep (se 1 (by rfl) ⟨2173418, by rfl⟩ : syracuseStep 2897891 = 4346837) B4346837
theorem B1931249 : Blo 1285961 1931249 := bstep (se 2 (by rfl) ⟨724218, by rfl⟩ : syracuseStep 1931249 = 1448437) B1448437
theorem B1931267 : Blo 1285961 1931267 := bstep (se 1 (by rfl) ⟨1448450, by rfl⟩ : syracuseStep 1931267 = 2896901) B2896901
theorem B1931297 : Blo 1285961 1931297 := bstep (se 2 (by rfl) ⟨724236, by rfl⟩ : syracuseStep 1931297 = 1448473) B1448473
theorem B1447987 : Blo 1285961 1447987 := bstep (se 1 (by rfl) ⟨1085990, by rfl⟩ : syracuseStep 1447987 = 2171981) B2171981
theorem B1931315 : Blo 1285961 1931315 := bstep (se 1 (by rfl) ⟨1448486, by rfl⟩ : syracuseStep 1931315 = 2896973) B2896973
theorem B1833025 : Blo 1285961 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B1931345 : Blo 1285961 1931345 := bstep (se 2 (by rfl) ⟨724254, by rfl⟩ : syracuseStep 1931345 = 1448509) B1448509
theorem B1931363 : Blo 1285961 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B1931393 : Blo 1285961 1931393 := bstep (se 2 (by rfl) ⟨724272, by rfl⟩ : syracuseStep 1931393 = 1448545) B1448545
theorem B1374355 : Blo 1285961 1374355 := bstep (se 1 (by rfl) ⟨1030766, by rfl⟩ : syracuseStep 1374355 = 2061533) B2061533
theorem B1931411 : Blo 1285961 1931411 := bstep (se 1 (by rfl) ⟨1448558, by rfl⟩ : syracuseStep 1931411 = 2897117) B2897117
theorem B1931441 : Blo 1285961 1931441 := bstep (se 2 (by rfl) ⟨724290, by rfl⟩ : syracuseStep 1931441 = 1448581) B1448581
theorem B1833139 : Blo 1285961 1833139 := bstep (se 1 (by rfl) ⟨1374854, by rfl⟩ : syracuseStep 1833139 = 2749709) B2749709
theorem B1448131 : Blo 1285961 1448131 := bstep (se 1 (by rfl) ⟨1086098, by rfl⟩ : syracuseStep 1448131 = 2172197) B2172197
theorem B1931459 : Blo 1285961 1931459 := bstep (se 1 (by rfl) ⟨1448594, by rfl⟩ : syracuseStep 1931459 = 2897189) B2897189
theorem B4888781 : Blo 1285961 4888781 := bstep (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) B1833293
theorem B1931489 : Blo 1285961 1931489 := bstep (se 2 (by rfl) ⟨724308, by rfl⟩ : syracuseStep 1931489 = 1448617) B1448617
theorem B2062577 : Blo 1285961 2062577 := bstep (se 2 (by rfl) ⟨773466, by rfl⟩ : syracuseStep 2062577 = 1546933) B1546933
theorem B1931507 : Blo 1285961 1931507 := bstep (se 1 (by rfl) ⟨1448630, by rfl⟩ : syracuseStep 1931507 = 2897261) B2897261
theorem B1628419 : Blo 1285961 1628419 := bstep (se 1 (by rfl) ⟨1221314, by rfl⟩ : syracuseStep 1628419 = 2442629) B2442629
theorem B1931537 : Blo 1285961 1931537 := bstep (se 2 (by rfl) ⟨724326, by rfl⟩ : syracuseStep 1931537 = 1448653) B1448653
theorem B1931555 : Blo 1285961 1931555 := bstep (se 1 (by rfl) ⟨1448666, by rfl⟩ : syracuseStep 1931555 = 2897333) B2897333
theorem B1931585 : Blo 1285961 1931585 := bstep (se 2 (by rfl) ⟨724344, by rfl⟩ : syracuseStep 1931585 = 1448689) B1448689
theorem B7829837 : Blo 1285961 7829837 := bstep (se 3 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 7829837 = 2936189) B2936189
theorem B1448275 : Blo 1285961 1448275 := bstep (se 1 (by rfl) ⟨1086206, by rfl⟩ : syracuseStep 1448275 = 2172413) B2172413
theorem B1931603 : Blo 1285961 1931603 := bstep (se 1 (by rfl) ⟨1448702, by rfl⟩ : syracuseStep 1931603 = 2897405) B2897405
theorem B1628515 : Blo 1285961 1628515 := bstep (se 1 (by rfl) ⟨1221386, by rfl⟩ : syracuseStep 1628515 = 2442773) B2442773
theorem B1931633 : Blo 1285961 1931633 := bstep (se 2 (by rfl) ⟨724362, by rfl⟩ : syracuseStep 1931633 = 1448725) B1448725
theorem B1931651 : Blo 1285961 1931651 := bstep (se 1 (by rfl) ⟨1448738, by rfl⟩ : syracuseStep 1931651 = 2897477) B2897477
theorem B1931681 : Blo 1285961 1931681 := bstep (se 2 (by rfl) ⟨724380, by rfl⟩ : syracuseStep 1931681 = 1448761) B1448761
theorem B6519203 : Blo 1285961 6519203 := bstep (se 1 (by rfl) ⟨4889402, by rfl⟩ : syracuseStep 6519203 = 9778805) B9778805
theorem B4340141 : Blo 1285961 4340141 := bstep (se 3 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 4340141 = 1627553) B1627553
theorem B1931699 : Blo 1285961 1931699 := bstep (se 1 (by rfl) ⟨1448774, by rfl⟩ : syracuseStep 1931699 = 2897549) B2897549
theorem B3914189 : Blo 1285961 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B1931729 : Blo 1285961 1931729 := bstep (se 2 (by rfl) ⟨724398, by rfl⟩ : syracuseStep 1931729 = 1448797) B1448797
theorem B4340195 : Blo 1285961 4340195 := bstep (se 1 (by rfl) ⟨3255146, by rfl⟩ : syracuseStep 4340195 = 6510293) B6510293
theorem B1448419 : Blo 1285961 1448419 := bstep (se 1 (by rfl) ⟨1086314, by rfl⟩ : syracuseStep 1448419 = 2172629) B2172629
theorem B1931747 : Blo 1285961 1931747 := bstep (se 1 (by rfl) ⟨1448810, by rfl⟩ : syracuseStep 1931747 = 2897621) B2897621
theorem B1931777 : Blo 1285961 1931777 := bstep (se 2 (by rfl) ⟨724416, by rfl⟩ : syracuseStep 1931777 = 1448833) B1448833
theorem B2062865 : Blo 1285961 2062865 := bstep (se 2 (by rfl) ⟨773574, by rfl⟩ : syracuseStep 2062865 = 1547149) B1547149
theorem B1931795 : Blo 1285961 1931795 := bstep (se 1 (by rfl) ⟨1448846, by rfl⟩ : syracuseStep 1931795 = 2897693) B2897693
theorem B6953521 : Blo 1285961 6953521 := bstep (se 2 (by rfl) ⟨2607570, by rfl⟩ : syracuseStep 6953521 = 5215141) B5215141
theorem B1931825 : Blo 1285961 1931825 := bstep (se 2 (by rfl) ⟨724434, by rfl⟩ : syracuseStep 1931825 = 1448869) B1448869
theorem B1931843 : Blo 1285961 1931843 := bstep (se 1 (by rfl) ⟨1448882, by rfl⟩ : syracuseStep 1931843 = 2897765) B2897765
theorem B1931873 : Blo 1285961 1931873 := bstep (se 2 (by rfl) ⟨724452, by rfl⟩ : syracuseStep 1931873 = 1448905) B1448905
theorem B13916771 : Blo 1285961 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B1448563 : Blo 1285961 1448563 := bstep (se 1 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 1448563 = 2172845) B2172845
theorem B1931891 : Blo 1285961 1931891 := bstep (se 1 (by rfl) ⟨1448918, by rfl⟩ : syracuseStep 1931891 = 2897837) B2897837
theorem B3259025 : Blo 1285961 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B1931921 : Blo 1285961 1931921 := bstep (se 2 (by rfl) ⟨724470, by rfl⟩ : syracuseStep 1931921 = 1448941) B1448941
theorem B1931939 : Blo 1285961 1931939 := bstep (se 1 (by rfl) ⟨1448954, by rfl⟩ : syracuseStep 1931939 = 2897909) B2897909
theorem B3259075 : Blo 1285961 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B4340465 : Blo 1285961 4340465 := bstep (se 2 (by rfl) ⟨1627674, by rfl⟩ : syracuseStep 4340465 = 3255349) B3255349
theorem B1448707 : Blo 1285961 1448707 := bstep (se 1 (by rfl) ⟨1086530, by rfl⟩ : syracuseStep 1448707 = 2173061) B2173061
theorem B3259217 : Blo 1285961 3259217 := bstep (se 2 (by rfl) ⟨1222206, by rfl⟩ : syracuseStep 3259217 = 2444413) B2444413
theorem B1629011 : Blo 1285961 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B1448851 : Blo 1285961 1448851 := bstep (se 1 (by rfl) ⟨1086638, by rfl⟩ : syracuseStep 1448851 = 2173277) B2173277
theorem B1956803 : Blo 1285961 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B4889585 : Blo 1285961 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B3300401 : Blo 1285961 3300401 := bstep (se 2 (by rfl) ⟨1237650, by rfl⟩ : syracuseStep 3300401 = 2475301) B2475301
theorem B6520013 : Blo 1285961 6520013 := bstep (se 3 (by rfl) ⟨1222502, by rfl⟩ : syracuseStep 6520013 = 2445005) B2445005
theorem B4955377 : Blo 1285961 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B4341005 : Blo 1285961 4341005 := bstep (se 3 (by rfl) ⟨813938, by rfl⟩ : syracuseStep 4341005 = 1627877) B1627877
theorem B2170145 : Blo 1285961 2170145 := bstep (se 2 (by rfl) ⟨813804, by rfl⟩ : syracuseStep 2170145 = 1627609) B1627609
theorem B23469365 : Blo 1285961 23469365 := bstep (se 5 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 23469365 = 2200253) B2200253
theorem B4341059 : Blo 1285961 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B2170273 : Blo 1285961 2170273 := bstep (se 2 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 2170273 = 1627705) B1627705
theorem B2170307 : Blo 1285961 2170307 := bstep (se 1 (by rfl) ⟨1627730, by rfl⟩ : syracuseStep 2170307 = 3255461) B3255461
theorem B8248817 : Blo 1285961 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B1629715 : Blo 1285961 1629715 := bstep (se 1 (by rfl) ⟨1222286, by rfl⟩ : syracuseStep 1629715 = 2444573) B2444573
theorem B14114357 : Blo 1285961 14114357 := bstep (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) B1323221
theorem B2170435 : Blo 1285961 2170435 := bstep (se 1 (by rfl) ⟨1627826, by rfl⟩ : syracuseStep 2170435 = 3255653) B3255653
theorem B4341329 : Blo 1285961 4341329 := bstep (se 2 (by rfl) ⟨1627998, by rfl⟩ : syracuseStep 4341329 = 3255997) B3255997
theorem B1629811 : Blo 1285961 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B2170577 : Blo 1285961 2170577 := bstep (se 2 (by rfl) ⟨813966, by rfl⟩ : syracuseStep 2170577 = 1627933) B1627933
theorem B2170705 : Blo 1285961 2170705 := bstep (se 2 (by rfl) ⟨814014, by rfl⟩ : syracuseStep 2170705 = 1628029) B1628029
theorem B1285971 : Blo 1285961 1285971 := bstep (se 1 (by rfl) ⟨964478, by rfl⟩ : syracuseStep 1285971 = 1928957) B1928957
theorem B1285987 : Blo 1285961 1285987 := bstep (se 1 (by rfl) ⟨964490, by rfl⟩ : syracuseStep 1285987 = 1928981) B1928981
theorem B3964781 : Blo 1285961 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B1286003 : Blo 1285961 1286003 := bstep (se 1 (by rfl) ⟨964502, by rfl⟩ : syracuseStep 1286003 = 1929005) B1929005
theorem B2170739 : Blo 1285961 2170739 := bstep (se 1 (by rfl) ⟨1628054, by rfl⟩ : syracuseStep 2170739 = 3256109) B3256109
theorem B1286019 : Blo 1285961 1286019 := bstep (se 1 (by rfl) ⟨964514, by rfl⟩ : syracuseStep 1286019 = 1929029) B1929029
theorem B1286035 : Blo 1285961 1286035 := bstep (se 1 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 1286035 = 1929053) B1929053
theorem B1286051 : Blo 1285961 1286051 := bstep (se 1 (by rfl) ⟨964538, by rfl⟩ : syracuseStep 1286051 = 1929077) B1929077
theorem B6512561 : Blo 1285961 6512561 := bstep (se 2 (by rfl) ⟨2442210, by rfl⟩ : syracuseStep 6512561 = 4884421) B4884421
theorem B1286067 : Blo 1285961 1286067 := bstep (se 1 (by rfl) ⟨964550, by rfl⟩ : syracuseStep 1286067 = 1929101) B1929101
theorem B1286083 : Blo 1285961 1286083 := bstep (se 1 (by rfl) ⟨964562, by rfl⟩ : syracuseStep 1286083 = 1929125) B1929125
theorem B13565893 : Blo 1285961 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B1286099 : Blo 1285961 1286099 := bstep (se 1 (by rfl) ⟨964574, by rfl⟩ : syracuseStep 1286099 = 1929149) B1929149
theorem B1286115 : Blo 1285961 1286115 := bstep (se 1 (by rfl) ⟨964586, by rfl⟩ : syracuseStep 1286115 = 1929173) B1929173
theorem B1957873 : Blo 1285961 1957873 := bstep (se 2 (by rfl) ⟨734202, by rfl⟩ : syracuseStep 1957873 = 1468405) B1468405
theorem B1286131 : Blo 1285961 1286131 := bstep (se 1 (by rfl) ⟨964598, by rfl⟩ : syracuseStep 1286131 = 1929197) B1929197
theorem B2170867 : Blo 1285961 2170867 := bstep (se 1 (by rfl) ⟨1628150, by rfl⟩ : syracuseStep 2170867 = 3256301) B3256301
theorem B1286155 : Blo 1285961 1286155 := bstep (se 1 (by rfl) ⟨964616, by rfl⟩ : syracuseStep 1286155 = 1929233) B1929233
theorem B1286167 : Blo 1285961 1286167 := bstep (se 1 (by rfl) ⟨964625, by rfl⟩ : syracuseStep 1286167 = 1929251) B1929251
theorem B1286187 : Blo 1285961 1286187 := bstep (se 1 (by rfl) ⟨964640, by rfl⟩ : syracuseStep 1286187 = 1929281) B1929281
theorem B1286199 : Blo 1285961 1286199 := bstep (se 1 (by rfl) ⟨964649, by rfl⟩ : syracuseStep 1286199 = 1929299) B1929299
theorem B24756293 : Blo 1285961 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B1286219 : Blo 1285961 1286219 := bstep (se 1 (by rfl) ⟨964664, by rfl⟩ : syracuseStep 1286219 = 1929329) B1929329
theorem B2170955 : Blo 1285961 2170955 := bstep (se 1 (by rfl) ⟨1628216, by rfl⟩ : syracuseStep 2170955 = 3256433) B3256433
theorem B1286231 : Blo 1285961 1286231 := bstep (se 1 (by rfl) ⟨964673, by rfl⟩ : syracuseStep 1286231 = 1929347) B1929347
theorem B1286251 : Blo 1285961 1286251 := bstep (se 1 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 1286251 = 1929377) B1929377
theorem B1286263 : Blo 1285961 1286263 := bstep (se 1 (by rfl) ⟨964697, by rfl⟩ : syracuseStep 1286263 = 1929395) B1929395
theorem B1286283 : Blo 1285961 1286283 := bstep (se 1 (by rfl) ⟨964712, by rfl⟩ : syracuseStep 1286283 = 1929425) B1929425
theorem B1286295 : Blo 1285961 1286295 := bstep (se 1 (by rfl) ⟨964721, by rfl⟩ : syracuseStep 1286295 = 1929443) B1929443
theorem B1286315 : Blo 1285961 1286315 := bstep (se 1 (by rfl) ⟨964736, by rfl⟩ : syracuseStep 1286315 = 1929473) B1929473
theorem B1286327 : Blo 1285961 1286327 := bstep (se 1 (by rfl) ⟨964745, by rfl⟩ : syracuseStep 1286327 = 1929491) B1929491
theorem B1286347 : Blo 1285961 1286347 := bstep (se 1 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 1286347 = 1929521) B1929521
theorem B2171083 : Blo 1285961 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B2318539 : Blo 1285961 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B1286359 : Blo 1285961 1286359 := bstep (se 1 (by rfl) ⟨964769, by rfl⟩ : syracuseStep 1286359 = 1929539) B1929539
theorem B4341977 : Blo 1285961 4341977 := bstep (se 2 (by rfl) ⟨1628241, by rfl⟩ : syracuseStep 4341977 = 3256483) B3256483
theorem B7635161 : Blo 1285961 7635161 := bstep (se 2 (by rfl) ⟨2863185, by rfl⟩ : syracuseStep 7635161 = 5726371) B5726371
theorem B1286379 : Blo 1285961 1286379 := bstep (se 1 (by rfl) ⟨964784, by rfl⟩ : syracuseStep 1286379 = 1929569) B1929569
theorem B1286391 : Blo 1285961 1286391 := bstep (se 1 (by rfl) ⟨964793, by rfl⟩ : syracuseStep 1286391 = 1929587) B1929587
theorem B1286411 : Blo 1285961 1286411 := bstep (se 1 (by rfl) ⟨964808, by rfl⟩ : syracuseStep 1286411 = 1929617) B1929617
theorem B1286423 : Blo 1285961 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B2441497 : Blo 1285961 2441497 := bstep (se 2 (by rfl) ⟨915561, by rfl⟩ : syracuseStep 2441497 = 1831123) B1831123
theorem B1286443 : Blo 1285961 1286443 := bstep (se 1 (by rfl) ⟨964832, by rfl⟩ : syracuseStep 1286443 = 1929665) B1929665
theorem B1286455 : Blo 1285961 1286455 := bstep (se 1 (by rfl) ⟨964841, by rfl⟩ : syracuseStep 1286455 = 1929683) B1929683
theorem B1286475 : Blo 1285961 1286475 := bstep (se 1 (by rfl) ⟨964856, by rfl⟩ : syracuseStep 1286475 = 1929713) B1929713
theorem B1286487 : Blo 1285961 1286487 := bstep (se 1 (by rfl) ⟨964865, by rfl⟩ : syracuseStep 1286487 = 1929731) B1929731
theorem B2171225 : Blo 1285961 2171225 := bstep (se 2 (by rfl) ⟨814209, by rfl⟩ : syracuseStep 2171225 = 1628419) B1628419
theorem B4882781 : Blo 1285961 4882781 := bstep (se 3 (by rfl) ⟨915521, by rfl⟩ : syracuseStep 4882781 = 1831043) B1831043
theorem B1286507 : Blo 1285961 1286507 := bstep (se 1 (by rfl) ⟨964880, by rfl⟩ : syracuseStep 1286507 = 1929761) B1929761
theorem B1286519 : Blo 1285961 1286519 := bstep (se 1 (by rfl) ⟨964889, by rfl⟩ : syracuseStep 1286519 = 1929779) B1929779
theorem B1286539 : Blo 1285961 1286539 := bstep (se 1 (by rfl) ⟨964904, by rfl⟩ : syracuseStep 1286539 = 1929809) B1929809
theorem B6513047 : Blo 1285961 6513047 := bstep (se 1 (by rfl) ⟨4884785, by rfl⟩ : syracuseStep 6513047 = 9769571) B9769571
theorem B1286551 : Blo 1285961 1286551 := bstep (se 1 (by rfl) ⟨964913, by rfl⟩ : syracuseStep 1286551 = 1929827) B1929827
theorem B1286571 : Blo 1285961 1286571 := bstep (se 1 (by rfl) ⟨964928, by rfl⟩ : syracuseStep 1286571 = 1929857) B1929857
theorem B19825073 : Blo 1285961 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B1286583 : Blo 1285961 1286583 := bstep (se 1 (by rfl) ⟨964937, by rfl⟩ : syracuseStep 1286583 = 1929875) B1929875
theorem B1286603 : Blo 1285961 1286603 := bstep (se 1 (by rfl) ⟨964952, by rfl⟩ : syracuseStep 1286603 = 1929905) B1929905
theorem B1286615 : Blo 1285961 1286615 := bstep (se 1 (by rfl) ⟨964961, by rfl⟩ : syracuseStep 1286615 = 1929923) B1929923
theorem B2171353 : Blo 1285961 2171353 := bstep (se 2 (by rfl) ⟨814257, by rfl⟩ : syracuseStep 2171353 = 1628515) B1628515
theorem B1286635 : Blo 1285961 1286635 := bstep (se 1 (by rfl) ⟨964976, by rfl⟩ : syracuseStep 1286635 = 1929953) B1929953
theorem B1286647 : Blo 1285961 1286647 := bstep (se 1 (by rfl) ⟨964985, by rfl⟩ : syracuseStep 1286647 = 1929971) B1929971
theorem B1286667 : Blo 1285961 1286667 := bstep (se 1 (by rfl) ⟨965000, by rfl⟩ : syracuseStep 1286667 = 1930001) B1930001
theorem B1286679 : Blo 1285961 1286679 := bstep (se 1 (by rfl) ⟨965009, by rfl⟩ : syracuseStep 1286679 = 1930019) B1930019
theorem B1286699 : Blo 1285961 1286699 := bstep (se 1 (by rfl) ⟨965024, by rfl⟩ : syracuseStep 1286699 = 1930049) B1930049
theorem B1286711 : Blo 1285961 1286711 := bstep (se 1 (by rfl) ⟨965033, by rfl⟩ : syracuseStep 1286711 = 1930067) B1930067
theorem B1286731 : Blo 1285961 1286731 := bstep (se 1 (by rfl) ⟨965048, by rfl⟩ : syracuseStep 1286731 = 1930097) B1930097
theorem B1286743 : Blo 1285961 1286743 := bstep (se 1 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 1286743 = 1930115) B1930115
theorem B1286763 : Blo 1285961 1286763 := bstep (se 1 (by rfl) ⟨965072, by rfl⟩ : syracuseStep 1286763 = 1930145) B1930145
theorem B1286775 : Blo 1285961 1286775 := bstep (se 1 (by rfl) ⟨965081, by rfl⟩ : syracuseStep 1286775 = 1930163) B1930163
theorem B1286795 : Blo 1285961 1286795 := bstep (se 1 (by rfl) ⟨965096, by rfl⟩ : syracuseStep 1286795 = 1930193) B1930193
theorem B1286807 : Blo 1285961 1286807 := bstep (se 1 (by rfl) ⟨965105, by rfl⟩ : syracuseStep 1286807 = 1930211) B1930211
theorem B2351767 : Blo 1285961 2351767 := bstep (se 1 (by rfl) ⟨1763825, by rfl⟩ : syracuseStep 2351767 = 3527651) B3527651
theorem B1286827 : Blo 1285961 1286827 := bstep (se 1 (by rfl) ⟨965120, by rfl⟩ : syracuseStep 1286827 = 1930241) B1930241
theorem B1286839 : Blo 1285961 1286839 := bstep (se 1 (by rfl) ⟨965129, by rfl⟩ : syracuseStep 1286839 = 1930259) B1930259
theorem B1286859 : Blo 1285961 1286859 := bstep (se 1 (by rfl) ⟨965144, by rfl⟩ : syracuseStep 1286859 = 1930289) B1930289
theorem B1286871 : Blo 1285961 1286871 := bstep (se 1 (by rfl) ⟨965153, by rfl⟩ : syracuseStep 1286871 = 1930307) B1930307
theorem B1286891 : Blo 1285961 1286891 := bstep (se 1 (by rfl) ⟨965168, by rfl⟩ : syracuseStep 1286891 = 1930337) B1930337
theorem B1286903 : Blo 1285961 1286903 := bstep (se 1 (by rfl) ⟨965177, by rfl⟩ : syracuseStep 1286903 = 1930355) B1930355
theorem B1286923 : Blo 1285961 1286923 := bstep (se 1 (by rfl) ⟨965192, by rfl⟩ : syracuseStep 1286923 = 1930385) B1930385
theorem B1286935 : Blo 1285961 1286935 := bstep (se 1 (by rfl) ⟨965201, by rfl⟩ : syracuseStep 1286935 = 1930403) B1930403
theorem B1286955 : Blo 1285961 1286955 := bstep (se 1 (by rfl) ⟨965216, by rfl⟩ : syracuseStep 1286955 = 1930433) B1930433
theorem B1286967 : Blo 1285961 1286967 := bstep (se 1 (by rfl) ⟨965225, by rfl⟩ : syracuseStep 1286967 = 1930451) B1930451
theorem B2442059 : Blo 1285961 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B1286987 : Blo 1285961 1286987 := bstep (se 1 (by rfl) ⟨965240, by rfl⟩ : syracuseStep 1286987 = 1930481) B1930481
theorem B1286999 : Blo 1285961 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B13910885 : Blo 1285961 13910885 := bstep (se 4 (by rfl) ⟨1304145, by rfl⟩ : syracuseStep 13910885 = 2608291) B2608291
theorem B1287019 : Blo 1285961 1287019 := bstep (se 1 (by rfl) ⟨965264, by rfl⟩ : syracuseStep 1287019 = 1930529) B1930529
theorem B1287031 : Blo 1285961 1287031 := bstep (se 1 (by rfl) ⟨965273, by rfl⟩ : syracuseStep 1287031 = 1930547) B1930547
theorem B1287051 : Blo 1285961 1287051 := bstep (se 1 (by rfl) ⟨965288, by rfl⟩ : syracuseStep 1287051 = 1930577) B1930577
theorem B4342679 : Blo 1285961 4342679 := bstep (se 1 (by rfl) ⟨3257009, by rfl⟩ : syracuseStep 4342679 = 6514019) B6514019
theorem B1287063 : Blo 1285961 1287063 := bstep (se 1 (by rfl) ⟨965297, by rfl⟩ : syracuseStep 1287063 = 1930595) B1930595
theorem B1287083 : Blo 1285961 1287083 := bstep (se 1 (by rfl) ⟨965312, by rfl⟩ : syracuseStep 1287083 = 1930625) B1930625
theorem B1287095 : Blo 1285961 1287095 := bstep (se 1 (by rfl) ⟨965321, by rfl⟩ : syracuseStep 1287095 = 1930643) B1930643
theorem B1287115 : Blo 1285961 1287115 := bstep (se 1 (by rfl) ⟨965336, by rfl⟩ : syracuseStep 1287115 = 1930673) B1930673
theorem B1287127 : Blo 1285961 1287127 := bstep (se 1 (by rfl) ⟨965345, by rfl⟩ : syracuseStep 1287127 = 1930691) B1930691
theorem B1287147 : Blo 1285961 1287147 := bstep (se 1 (by rfl) ⟨965360, by rfl⟩ : syracuseStep 1287147 = 1930721) B1930721
theorem B2319347 : Blo 1285961 2319347 := bstep (se 1 (by rfl) ⟨1739510, by rfl⟩ : syracuseStep 2319347 = 3479021) B3479021
theorem B1287159 : Blo 1285961 1287159 := bstep (se 1 (by rfl) ⟨965369, by rfl⟩ : syracuseStep 1287159 = 1930739) B1930739
theorem B2442241 : Blo 1285961 2442241 := bstep (se 2 (by rfl) ⟨915840, by rfl⟩ : syracuseStep 2442241 = 1831681) B1831681
theorem B1287179 : Blo 1285961 1287179 := bstep (se 1 (by rfl) ⟨965384, by rfl⟩ : syracuseStep 1287179 = 1930769) B1930769
theorem B2171927 : Blo 1285961 2171927 := bstep (se 1 (by rfl) ⟨1628945, by rfl⟩ : syracuseStep 2171927 = 3257891) B3257891
theorem B1287191 : Blo 1285961 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B1287211 : Blo 1285961 1287211 := bstep (se 1 (by rfl) ⟨965408, by rfl⟩ : syracuseStep 1287211 = 1930817) B1930817
theorem B1287223 : Blo 1285961 1287223 := bstep (se 1 (by rfl) ⟨965417, by rfl⟩ : syracuseStep 1287223 = 1930835) B1930835
theorem B1287243 : Blo 1285961 1287243 := bstep (se 1 (by rfl) ⟨965432, by rfl⟩ : syracuseStep 1287243 = 1930865) B1930865
theorem B1287255 : Blo 1285961 1287255 := bstep (se 1 (by rfl) ⟨965441, by rfl⟩ : syracuseStep 1287255 = 1930883) B1930883
theorem B3662941 : Blo 1285961 3662941 := bstep (se 3 (by rfl) ⟨686801, by rfl⟩ : syracuseStep 3662941 = 1373603) B1373603
theorem B1287275 : Blo 1285961 1287275 := bstep (se 1 (by rfl) ⟨965456, by rfl⟩ : syracuseStep 1287275 = 1930913) B1930913
theorem B1287287 : Blo 1285961 1287287 := bstep (se 1 (by rfl) ⟨965465, by rfl⟩ : syracuseStep 1287287 = 1930931) B1930931
theorem B12371075 : Blo 1285961 12371075 := bstep (se 1 (by rfl) ⟨9278306, by rfl⟩ : syracuseStep 12371075 = 18556613) B18556613
theorem B18564227 : Blo 1285961 18564227 := bstep (se 1 (by rfl) ⟨13923170, by rfl⟩ : syracuseStep 18564227 = 27846341) B27846341
theorem B1287307 : Blo 1285961 1287307 := bstep (se 1 (by rfl) ⟨965480, by rfl⟩ : syracuseStep 1287307 = 1930961) B1930961
theorem B2172055 : Blo 1285961 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B1287319 : Blo 1285961 1287319 := bstep (se 1 (by rfl) ⟨965489, by rfl⟩ : syracuseStep 1287319 = 1930979) B1930979
theorem B1287339 : Blo 1285961 1287339 := bstep (se 1 (by rfl) ⟨965504, by rfl⟩ : syracuseStep 1287339 = 1931009) B1931009
theorem B1287351 : Blo 1285961 1287351 := bstep (se 1 (by rfl) ⟨965513, by rfl⟩ : syracuseStep 1287351 = 1931027) B1931027
theorem B1287371 : Blo 1285961 1287371 := bstep (se 1 (by rfl) ⟨965528, by rfl⟩ : syracuseStep 1287371 = 1931057) B1931057
theorem B14648525 : Blo 1285961 14648525 := bstep (se 3 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 14648525 = 5493197) B5493197
theorem B1287383 : Blo 1285961 1287383 := bstep (se 1 (by rfl) ⟨965537, by rfl⟩ : syracuseStep 1287383 = 1931075) B1931075
theorem B1287403 : Blo 1285961 1287403 := bstep (se 1 (by rfl) ⟨965552, by rfl⟩ : syracuseStep 1287403 = 1931105) B1931105
theorem B1287415 : Blo 1285961 1287415 := bstep (se 1 (by rfl) ⟨965561, by rfl⟩ : syracuseStep 1287415 = 1931123) B1931123
theorem B1287435 : Blo 1285961 1287435 := bstep (se 1 (by rfl) ⟨965576, by rfl⟩ : syracuseStep 1287435 = 1931153) B1931153
theorem B1287447 : Blo 1285961 1287447 := bstep (se 1 (by rfl) ⟨965585, by rfl⟩ : syracuseStep 1287447 = 1931171) B1931171
theorem B1287467 : Blo 1285961 1287467 := bstep (se 1 (by rfl) ⟨965600, by rfl⟩ : syracuseStep 1287467 = 1931201) B1931201
theorem B21996845 : Blo 1285961 21996845 := bstep (se 3 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 21996845 = 8248817) B8248817
theorem B1287479 : Blo 1285961 1287479 := bstep (se 1 (by rfl) ⟨965609, by rfl⟩ : syracuseStep 1287479 = 1931219) B1931219
theorem B1287499 : Blo 1285961 1287499 := bstep (se 1 (by rfl) ⟨965624, by rfl⟩ : syracuseStep 1287499 = 1931249) B1931249
theorem B1287511 : Blo 1285961 1287511 := bstep (se 1 (by rfl) ⟨965633, by rfl⟩ : syracuseStep 1287511 = 1931267) B1931267
theorem B1287531 : Blo 1285961 1287531 := bstep (se 1 (by rfl) ⟨965648, by rfl⟩ : syracuseStep 1287531 = 1931297) B1931297
theorem B1287543 : Blo 1285961 1287543 := bstep (se 1 (by rfl) ⟨965657, by rfl⟩ : syracuseStep 1287543 = 1931315) B1931315
theorem B1287563 : Blo 1285961 1287563 := bstep (se 1 (by rfl) ⟨965672, by rfl⟩ : syracuseStep 1287563 = 1931345) B1931345
theorem B1287575 : Blo 1285961 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B1287595 : Blo 1285961 1287595 := bstep (se 1 (by rfl) ⟨965696, by rfl⟩ : syracuseStep 1287595 = 1931393) B1931393
theorem B4343219 : Blo 1285961 4343219 := bstep (se 1 (by rfl) ⟨3257414, by rfl⟩ : syracuseStep 4343219 = 6514829) B6514829
theorem B1287607 : Blo 1285961 1287607 := bstep (se 1 (by rfl) ⟨965705, by rfl⟩ : syracuseStep 1287607 = 1931411) B1931411
theorem B1287627 : Blo 1285961 1287627 := bstep (se 1 (by rfl) ⟨965720, by rfl⟩ : syracuseStep 1287627 = 1931441) B1931441
theorem B1287639 : Blo 1285961 1287639 := bstep (se 1 (by rfl) ⟨965729, by rfl⟩ : syracuseStep 1287639 = 1931459) B1931459
theorem B1287659 : Blo 1285961 1287659 := bstep (se 1 (by rfl) ⟨965744, by rfl⟩ : syracuseStep 1287659 = 1931489) B1931489
theorem B1287671 : Blo 1285961 1287671 := bstep (se 1 (by rfl) ⟨965753, by rfl⟩ : syracuseStep 1287671 = 1931507) B1931507
theorem B1287691 : Blo 1285961 1287691 := bstep (se 1 (by rfl) ⟨965768, by rfl⟩ : syracuseStep 1287691 = 1931537) B1931537
theorem B1287703 : Blo 1285961 1287703 := bstep (se 1 (by rfl) ⟨965777, by rfl⟩ : syracuseStep 1287703 = 1931555) B1931555
theorem B1287723 : Blo 1285961 1287723 := bstep (se 1 (by rfl) ⟨965792, by rfl⟩ : syracuseStep 1287723 = 1931585) B1931585
theorem B5219891 : Blo 1285961 5219891 := bstep (se 1 (by rfl) ⟨3914918, by rfl⟩ : syracuseStep 5219891 = 7829837) B7829837
theorem B1287735 : Blo 1285961 1287735 := bstep (se 1 (by rfl) ⟨965801, by rfl⟩ : syracuseStep 1287735 = 1931603) B1931603
theorem B1287755 : Blo 1285961 1287755 := bstep (se 1 (by rfl) ⟨965816, by rfl⟩ : syracuseStep 1287755 = 1931633) B1931633
theorem B1287767 : Blo 1285961 1287767 := bstep (se 1 (by rfl) ⟨965825, by rfl⟩ : syracuseStep 1287767 = 1931651) B1931651
theorem B1287787 : Blo 1285961 1287787 := bstep (se 1 (by rfl) ⟨965840, by rfl⟩ : syracuseStep 1287787 = 1931681) B1931681
theorem B2893427 : Blo 1285961 2893427 := bstep (se 1 (by rfl) ⟨2170070, by rfl⟩ : syracuseStep 2893427 = 4340141) B4340141
theorem B1287799 : Blo 1285961 1287799 := bstep (se 1 (by rfl) ⟨965849, by rfl⟩ : syracuseStep 1287799 = 1931699) B1931699
theorem B1287819 : Blo 1285961 1287819 := bstep (se 1 (by rfl) ⟨965864, by rfl⟩ : syracuseStep 1287819 = 1931729) B1931729
theorem B5498513 : Blo 1285961 5498513 := bstep (se 2 (by rfl) ⟨2061942, by rfl⟩ : syracuseStep 5498513 = 4123885) B4123885
theorem B2893463 : Blo 1285961 2893463 := bstep (se 1 (by rfl) ⟨2170097, by rfl⟩ : syracuseStep 2893463 = 4340195) B4340195
theorem B1287831 : Blo 1285961 1287831 := bstep (se 1 (by rfl) ⟨965873, by rfl⟩ : syracuseStep 1287831 = 1931747) B1931747
theorem B1287851 : Blo 1285961 1287851 := bstep (se 1 (by rfl) ⟨965888, by rfl⟩ : syracuseStep 1287851 = 1931777) B1931777
theorem B1287863 : Blo 1285961 1287863 := bstep (se 1 (by rfl) ⟨965897, by rfl⟩ : syracuseStep 1287863 = 1931795) B1931795
theorem B4343489 : Blo 1285961 4343489 := bstep (se 2 (by rfl) ⟨1628808, by rfl⟩ : syracuseStep 4343489 = 3257617) B3257617
theorem B2442955 : Blo 1285961 2442955 := bstep (se 1 (by rfl) ⟨1832216, by rfl⟩ : syracuseStep 2442955 = 3664433) B3664433
theorem B1287883 : Blo 1285961 1287883 := bstep (se 1 (by rfl) ⟨965912, by rfl⟩ : syracuseStep 1287883 = 1931825) B1931825
theorem B1287895 : Blo 1285961 1287895 := bstep (se 1 (by rfl) ⟨965921, by rfl⟩ : syracuseStep 1287895 = 1931843) B1931843
theorem B1287915 : Blo 1285961 1287915 := bstep (se 1 (by rfl) ⟨965936, by rfl⟩ : syracuseStep 1287915 = 1931873) B1931873
theorem B1287927 : Blo 1285961 1287927 := bstep (se 1 (by rfl) ⟨965945, by rfl⟩ : syracuseStep 1287927 = 1931891) B1931891
theorem B2172683 : Blo 1285961 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B1287947 : Blo 1285961 1287947 := bstep (se 1 (by rfl) ⟨965960, by rfl⟩ : syracuseStep 1287947 = 1931921) B1931921
theorem B7333649 : Blo 1285961 7333649 := bstep (se 2 (by rfl) ⟨2750118, by rfl⟩ : syracuseStep 7333649 = 5500237) B5500237
theorem B2443031 : Blo 1285961 2443031 := bstep (se 1 (by rfl) ⟨1832273, by rfl⟩ : syracuseStep 2443031 = 3664547) B3664547
theorem B1287959 : Blo 1285961 1287959 := bstep (se 1 (by rfl) ⟨965969, by rfl⟩ : syracuseStep 1287959 = 1931939) B1931939
theorem B2893643 : Blo 1285961 2893643 := bstep (se 1 (by rfl) ⟨2170232, by rfl⟩ : syracuseStep 2893643 = 4340465) B4340465
theorem B4122461 : Blo 1285961 4122461 := bstep (se 3 (by rfl) ⟨772961, by rfl⟩ : syracuseStep 4122461 = 1545923) B1545923
theorem B2893697 : Blo 1285961 2893697 := bstep (se 2 (by rfl) ⟨1085136, by rfl⟩ : syracuseStep 2893697 = 2170273) B2170273
theorem B2172811 : Blo 1285961 2172811 := bstep (se 1 (by rfl) ⟨1629608, by rfl⟩ : syracuseStep 2172811 = 3259217) B3259217
theorem B6031277 : Blo 1285961 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B16074713 : Blo 1285961 16074713 := bstep (se 2 (by rfl) ⟨6028017, by rfl⟩ : syracuseStep 16074713 = 12056035) B12056035
theorem B2172953 : Blo 1285961 2172953 := bstep (se 2 (by rfl) ⟨814857, by rfl⟩ : syracuseStep 2172953 = 1629715) B1629715
theorem B31311947 : Blo 1285961 31311947 := bstep (se 1 (by rfl) ⟨23483960, by rfl⟩ : syracuseStep 31311947 = 46967921) B46967921
theorem B2893913 : Blo 1285961 2893913 := bstep (se 2 (by rfl) ⟨1085217, by rfl⟩ : syracuseStep 2893913 = 2170435) B2170435
theorem B2173081 : Blo 1285961 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B9537713 : Blo 1285961 9537713 := bstep (se 2 (by rfl) ⟨3576642, by rfl⟩ : syracuseStep 9537713 = 7153285) B7153285
theorem B2894003 : Blo 1285961 2894003 := bstep (se 1 (by rfl) ⟨2170502, by rfl⟩ : syracuseStep 2894003 = 4341005) B4341005
theorem B2894039 : Blo 1285961 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B4344029 : Blo 1285961 4344029 := bstep (se 3 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 4344029 = 1629011) B1629011
theorem B3664217 : Blo 1285961 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B2894219 : Blo 1285961 2894219 := bstep (se 1 (by rfl) ⟨2170664, by rfl⟩ : syracuseStep 2894219 = 4341329) B4341329
theorem B2443699 : Blo 1285961 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B2894273 : Blo 1285961 2894273 := bstep (se 2 (by rfl) ⟨1085352, by rfl⟩ : syracuseStep 2894273 = 2170705) B2170705
theorem B5499485 : Blo 1285961 5499485 := bstep (se 3 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 5499485 = 2062307) B2062307
theorem B2747009 : Blo 1285961 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B7326359 : Blo 1285961 7326359 := bstep (se 1 (by rfl) ⟨5494769, by rfl⟩ : syracuseStep 7326359 = 10989539) B10989539
theorem B2443927 : Blo 1285961 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B2894489 : Blo 1285961 2894489 := bstep (se 2 (by rfl) ⟨1085433, by rfl⟩ : syracuseStep 2894489 = 2170867) B2170867
theorem B2894579 : Blo 1285961 2894579 := bstep (se 1 (by rfl) ⟨2170934, by rfl⟩ : syracuseStep 2894579 = 4341869) B4341869
theorem B2444033 : Blo 1285961 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B9775889 : Blo 1285961 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B2607895 : Blo 1285961 2607895 := bstep (se 1 (by rfl) ⟨1955921, by rfl⟩ : syracuseStep 2607895 = 3911843) B3911843
theorem B2894615 : Blo 1285961 2894615 := bstep (se 1 (by rfl) ⟨2170961, by rfl⟩ : syracuseStep 2894615 = 4341923) B4341923
theorem B3091223 : Blo 1285961 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B8801069 : Blo 1285961 8801069 := bstep (se 3 (by rfl) ⟨1650200, by rfl⟩ : syracuseStep 8801069 = 3300401) B3300401
theorem B4885379 : Blo 1285961 4885379 := bstep (se 1 (by rfl) ⟨3664034, by rfl⟩ : syracuseStep 4885379 = 7328069) B7328069
theorem B4885393 : Blo 1285961 4885393 := bstep (se 2 (by rfl) ⟨1832022, by rfl⟩ : syracuseStep 4885393 = 3664045) B3664045
theorem B2444185 : Blo 1285961 2444185 := bstep (se 2 (by rfl) ⟨916569, by rfl⟩ : syracuseStep 2444185 = 1833139) B1833139
theorem B13388723 : Blo 1285961 13388723 := bstep (se 1 (by rfl) ⟨10041542, by rfl⟩ : syracuseStep 13388723 = 20083085) B20083085
theorem B2894795 : Blo 1285961 2894795 := bstep (se 1 (by rfl) ⟨2171096, by rfl⟩ : syracuseStep 2894795 = 4342193) B4342193
theorem B2747351 : Blo 1285961 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B2894849 : Blo 1285961 2894849 := bstep (se 2 (by rfl) ⟨1085568, by rfl⟩ : syracuseStep 2894849 = 2171137) B2171137
theorem B15862877 : Blo 1285961 15862877 := bstep (se 3 (by rfl) ⟨2974289, by rfl⟩ : syracuseStep 15862877 = 5948579) B5948579
theorem B9768113 : Blo 1285961 9768113 := bstep (se 2 (by rfl) ⟨3663042, by rfl⟩ : syracuseStep 9768113 = 7326085) B7326085
theorem B4885697 : Blo 1285961 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B2895065 : Blo 1285961 2895065 := bstep (se 2 (by rfl) ⟨1085649, by rfl⟩ : syracuseStep 2895065 = 2171299) B2171299
theorem B2895155 : Blo 1285961 2895155 := bstep (se 1 (by rfl) ⟨2171366, by rfl⟩ : syracuseStep 2895155 = 4342733) B4342733
theorem B5868875 : Blo 1285961 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B4345163 : Blo 1285961 4345163 := bstep (se 1 (by rfl) ⟨3258872, by rfl⟩ : syracuseStep 4345163 = 6517745) B6517745
theorem B2895191 : Blo 1285961 2895191 := bstep (se 1 (by rfl) ⟨2171393, by rfl⟩ : syracuseStep 2895191 = 4342787) B4342787
theorem B2747915 : Blo 1285961 2747915 := bstep (se 1 (by rfl) ⟨2060936, by rfl⟩ : syracuseStep 2747915 = 4121873) B4121873
theorem B2895371 : Blo 1285961 2895371 := bstep (se 1 (by rfl) ⟨2171528, by rfl⟩ : syracuseStep 2895371 = 4343057) B4343057
theorem B2895425 : Blo 1285961 2895425 := bstep (se 2 (by rfl) ⟨1085784, by rfl⟩ : syracuseStep 2895425 = 2171569) B2171569
theorem B4345433 : Blo 1285961 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B9768599 : Blo 1285961 9768599 := bstep (se 1 (by rfl) ⟨7326449, by rfl⟩ : syracuseStep 9768599 = 14652899) B14652899
theorem B5574365 : Blo 1285961 5574365 := bstep (se 3 (by rfl) ⟨1045193, by rfl⟩ : syracuseStep 5574365 = 2090387) B2090387
theorem B2895641 : Blo 1285961 2895641 := bstep (se 2 (by rfl) ⟨1085865, by rfl⟩ : syracuseStep 2895641 = 2171731) B2171731
theorem B6188845 : Blo 1285961 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B1929035 : Blo 1285961 1929035 := bstep (se 1 (by rfl) ⟨1446776, by rfl⟩ : syracuseStep 1929035 = 2893553) B2893553
theorem B3256139 : Blo 1285961 3256139 := bstep (se 1 (by rfl) ⟨2442104, by rfl⟩ : syracuseStep 3256139 = 4884209) B4884209
theorem B1929047 : Blo 1285961 1929047 := bstep (se 1 (by rfl) ⟨1446785, by rfl⟩ : syracuseStep 1929047 = 2893571) B2893571
theorem B4886365 : Blo 1285961 4886365 := bstep (se 3 (by rfl) ⟨916193, by rfl⟩ : syracuseStep 4886365 = 1832387) B1832387
theorem B2895731 : Blo 1285961 2895731 := bstep (se 1 (by rfl) ⟨2171798, by rfl⟩ : syracuseStep 2895731 = 4343597) B4343597
theorem B6516611 : Blo 1285961 6516611 := bstep (se 1 (by rfl) ⟨4887458, by rfl⟩ : syracuseStep 6516611 = 9774917) B9774917
theorem B2895767 : Blo 1285961 2895767 := bstep (se 1 (by rfl) ⟨2171825, by rfl⟩ : syracuseStep 2895767 = 4343651) B4343651
theorem B1929113 : Blo 1285961 1929113 := bstep (se 2 (by rfl) ⟨723417, by rfl⟩ : syracuseStep 1929113 = 1446835) B1446835
theorem B3665857 : Blo 1285961 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B1929227 : Blo 1285961 1929227 := bstep (se 1 (by rfl) ⟨1446920, by rfl⟩ : syracuseStep 1929227 = 2893841) B2893841
theorem B1929239 : Blo 1285961 1929239 := bstep (se 1 (by rfl) ⟨1446929, by rfl⟩ : syracuseStep 1929239 = 2893859) B2893859
theorem B5500973 : Blo 1285961 5500973 := bstep (se 3 (by rfl) ⟨1031432, by rfl⟩ : syracuseStep 5500973 = 2062865) B2062865
theorem B2895947 : Blo 1285961 2895947 := bstep (se 1 (by rfl) ⟨2171960, by rfl⟩ : syracuseStep 2895947 = 4343921) B4343921
theorem B1929305 : Blo 1285961 1929305 := bstep (se 2 (by rfl) ⟨723489, by rfl⟩ : syracuseStep 1929305 = 1446979) B1446979
theorem B2748505 : Blo 1285961 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B2896001 : Blo 1285961 2896001 := bstep (se 2 (by rfl) ⟨1086000, by rfl⟩ : syracuseStep 2896001 = 2172001) B2172001
theorem B1929419 : Blo 1285961 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B1929431 : Blo 1285961 1929431 := bstep (se 1 (by rfl) ⟨1447073, by rfl⟩ : syracuseStep 1929431 = 2894147) B2894147
theorem B4346135 : Blo 1285961 4346135 := bstep (se 1 (by rfl) ⟨3259601, by rfl⟩ : syracuseStep 4346135 = 6519203) B6519203
theorem B1929497 : Blo 1285961 1929497 := bstep (se 2 (by rfl) ⟨723561, by rfl⟩ : syracuseStep 1929497 = 1447123) B1447123
theorem B2609459 : Blo 1285961 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B10170689 : Blo 1285961 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B6607169 : Blo 1285961 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B1831243 : Blo 1285961 1831243 := bstep (se 1 (by rfl) ⟨1373432, by rfl⟩ : syracuseStep 1831243 = 2746865) B2746865
theorem B2896217 : Blo 1285961 2896217 := bstep (se 2 (by rfl) ⟨1086081, by rfl⟩ : syracuseStep 2896217 = 2172163) B2172163
theorem B10989917 : Blo 1285961 10989917 := bstep (se 3 (by rfl) ⟨2060609, by rfl⟩ : syracuseStep 10989917 = 4121219) B4121219
theorem B1929611 : Blo 1285961 1929611 := bstep (se 1 (by rfl) ⟨1447208, by rfl⟩ : syracuseStep 1929611 = 2894417) B2894417
theorem B1929623 : Blo 1285961 1929623 := bstep (se 1 (by rfl) ⟨1447217, by rfl⟩ : syracuseStep 1929623 = 2894435) B2894435
theorem B9277847 : Blo 1285961 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B2896307 : Blo 1285961 2896307 := bstep (se 1 (by rfl) ⟨2172230, by rfl⟩ : syracuseStep 2896307 = 4344461) B4344461
theorem B2896343 : Blo 1285961 2896343 := bstep (se 1 (by rfl) ⟨2172257, by rfl⟩ : syracuseStep 2896343 = 4344515) B4344515
theorem B1929689 : Blo 1285961 1929689 := bstep (se 2 (by rfl) ⟨723633, by rfl⟩ : syracuseStep 1929689 = 1447267) B1447267
theorem B4698589 : Blo 1285961 4698589 := bstep (se 3 (by rfl) ⟨880985, by rfl⟩ : syracuseStep 4698589 = 1761971) B1761971
theorem B1929803 : Blo 1285961 1929803 := bstep (se 1 (by rfl) ⟨1447352, by rfl⟩ : syracuseStep 1929803 = 2894705) B2894705
theorem B1929815 : Blo 1285961 1929815 := bstep (se 1 (by rfl) ⟨1447361, by rfl⟩ : syracuseStep 1929815 = 2894723) B2894723
theorem B14660189 : Blo 1285961 14660189 := bstep (se 3 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 14660189 = 5497571) B5497571
theorem B2896523 : Blo 1285961 2896523 := bstep (se 1 (by rfl) ⟨2172392, by rfl⟩ : syracuseStep 2896523 = 4344785) B4344785
theorem B1929881 : Blo 1285961 1929881 := bstep (se 2 (by rfl) ⟨723705, by rfl⟩ : syracuseStep 1929881 = 1447411) B1447411
theorem B2896577 : Blo 1285961 2896577 := bstep (se 2 (by rfl) ⟨1086216, by rfl⟩ : syracuseStep 2896577 = 2172433) B2172433
theorem B18551537 : Blo 1285961 18551537 := bstep (se 2 (by rfl) ⟨6956826, by rfl⟩ : syracuseStep 18551537 = 13913653) B13913653
theorem B1929995 : Blo 1285961 1929995 := bstep (se 1 (by rfl) ⟨1447496, by rfl⟩ : syracuseStep 1929995 = 2894993) B2894993
theorem B1930007 : Blo 1285961 1930007 := bstep (se 1 (by rfl) ⟨1447505, by rfl⟩ : syracuseStep 1930007 = 2895011) B2895011
theorem B3257111 : Blo 1285961 3257111 := bstep (se 1 (by rfl) ⟨2442833, by rfl⟩ : syracuseStep 3257111 = 4885667) B4885667
theorem B3093299 : Blo 1285961 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B4346675 : Blo 1285961 4346675 := bstep (se 1 (by rfl) ⟨3260006, by rfl⟩ : syracuseStep 4346675 = 6520013) B6520013
theorem B8926027 : Blo 1285961 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B1930073 : Blo 1285961 1930073 := bstep (se 2 (by rfl) ⟨723777, by rfl⟩ : syracuseStep 1930073 = 1447555) B1447555
theorem B1446763 : Blo 1285961 1446763 := bstep (se 1 (by rfl) ⟨1085072, by rfl⟩ : syracuseStep 1446763 = 2170145) B2170145
theorem B2896793 : Blo 1285961 2896793 := bstep (se 2 (by rfl) ⟨1086297, by rfl⟩ : syracuseStep 2896793 = 2172595) B2172595
theorem B1930187 : Blo 1285961 1930187 := bstep (se 1 (by rfl) ⟨1447640, by rfl⟩ : syracuseStep 1930187 = 2895281) B2895281
theorem B10572749 : Blo 1285961 10572749 := bstep (se 3 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 10572749 = 3964781) B3964781
theorem B1446871 : Blo 1285961 1446871 := bstep (se 1 (by rfl) ⟨1085153, by rfl⟩ : syracuseStep 1446871 = 2170307) B2170307
theorem B1930199 : Blo 1285961 1930199 := bstep (se 1 (by rfl) ⟨1447649, by rfl⟩ : syracuseStep 1930199 = 2895299) B2895299
theorem B9270233 : Blo 1285961 9270233 := bstep (se 2 (by rfl) ⟨3476337, by rfl⟩ : syracuseStep 9270233 = 6952675) B6952675
theorem B2896883 : Blo 1285961 2896883 := bstep (se 1 (by rfl) ⟨2172662, by rfl⟩ : syracuseStep 2896883 = 4345325) B4345325
theorem B2896919 : Blo 1285961 2896919 := bstep (se 1 (by rfl) ⟨2172689, by rfl⟩ : syracuseStep 2896919 = 4345379) B4345379
theorem B1930265 : Blo 1285961 1930265 := bstep (se 2 (by rfl) ⟨723849, by rfl⟩ : syracuseStep 1930265 = 1447699) B1447699
theorem B9409571 : Blo 1285961 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B3912779 : Blo 1285961 3912779 := bstep (se 1 (by rfl) ⟨2934584, by rfl⟩ : syracuseStep 3912779 = 5869169) B5869169
theorem B4887641 : Blo 1285961 4887641 := bstep (se 2 (by rfl) ⟨1832865, by rfl⟩ : syracuseStep 4887641 = 3665731) B3665731
theorem B2749555 : Blo 1285961 2749555 := bstep (se 1 (by rfl) ⟨2062166, by rfl⟩ : syracuseStep 2749555 = 4124333) B4124333
theorem B1447051 : Blo 1285961 1447051 := bstep (se 1 (by rfl) ⟨1085288, by rfl⟩ : syracuseStep 1447051 = 2170577) B2170577
theorem B1930379 : Blo 1285961 1930379 := bstep (se 1 (by rfl) ⟨1447784, by rfl⟩ : syracuseStep 1930379 = 2895569) B2895569
theorem B1930391 : Blo 1285961 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B2897099 : Blo 1285961 2897099 := bstep (se 1 (by rfl) ⟨2172824, by rfl⟩ : syracuseStep 2897099 = 4345649) B4345649
theorem B1651915 : Blo 1285961 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B1930457 : Blo 1285961 1930457 := bstep (se 2 (by rfl) ⟨723921, by rfl⟩ : syracuseStep 1930457 = 1447843) B1447843
theorem B1373419 : Blo 1285961 1373419 := bstep (se 1 (by rfl) ⟨1030064, by rfl⟩ : syracuseStep 1373419 = 2060129) B2060129
theorem B1447159 : Blo 1285961 1447159 := bstep (se 1 (by rfl) ⟨1085369, by rfl⟩ : syracuseStep 1447159 = 2170739) B2170739
theorem B2897153 : Blo 1285961 2897153 := bstep (se 2 (by rfl) ⟨1086432, by rfl⟩ : syracuseStep 2897153 = 2172865) B2172865
theorem B2610497 : Blo 1285961 2610497 := bstep (se 2 (by rfl) ⟨978936, by rfl⟩ : syracuseStep 2610497 = 1957873) B1957873
theorem B1930571 : Blo 1285961 1930571 := bstep (se 1 (by rfl) ⟨1447928, by rfl⟩ : syracuseStep 1930571 = 2895857) B2895857
theorem B1930583 : Blo 1285961 1930583 := bstep (se 1 (by rfl) ⟨1447937, by rfl⟩ : syracuseStep 1930583 = 2895875) B2895875
theorem B1930649 : Blo 1285961 1930649 := bstep (se 2 (by rfl) ⟨723993, by rfl⟩ : syracuseStep 1930649 = 1447987) B1447987
theorem B1447339 : Blo 1285961 1447339 := bstep (se 1 (by rfl) ⟨1085504, by rfl⟩ : syracuseStep 1447339 = 2171009) B2171009
theorem B5494189 : Blo 1285961 5494189 := bstep (se 3 (by rfl) ⟨1030160, by rfl⟩ : syracuseStep 5494189 = 2060321) B2060321
theorem B3257779 : Blo 1285961 3257779 := bstep (se 1 (by rfl) ⟨2443334, by rfl⟩ : syracuseStep 3257779 = 4886669) B4886669
theorem B2897369 : Blo 1285961 2897369 := bstep (se 2 (by rfl) ⟨1086513, by rfl⟩ : syracuseStep 2897369 = 2173027) B2173027
theorem B1930763 : Blo 1285961 1930763 := bstep (se 1 (by rfl) ⟨1448072, by rfl⟩ : syracuseStep 1930763 = 2896145) B2896145
theorem B10999313 : Blo 1285961 10999313 := bstep (se 2 (by rfl) ⟨4124742, by rfl⟩ : syracuseStep 10999313 = 8249485) B8249485
theorem B1447447 : Blo 1285961 1447447 := bstep (se 1 (by rfl) ⟨1085585, by rfl⟩ : syracuseStep 1447447 = 2171171) B2171171
theorem B1930775 : Blo 1285961 1930775 := bstep (se 1 (by rfl) ⟨1448081, by rfl⟩ : syracuseStep 1930775 = 2896163) B2896163
theorem B1832473 : Blo 1285961 1832473 := bstep (se 2 (by rfl) ⟨687177, by rfl⟩ : syracuseStep 1832473 = 1374355) B1374355
theorem B2897459 : Blo 1285961 2897459 := bstep (se 1 (by rfl) ⟨2173094, by rfl⟩ : syracuseStep 2897459 = 4346189) B4346189
theorem B3257921 : Blo 1285961 3257921 := bstep (se 2 (by rfl) ⟨1221720, by rfl⟩ : syracuseStep 3257921 = 2443441) B2443441
theorem B3667531 : Blo 1285961 3667531 := bstep (se 1 (by rfl) ⟨2750648, by rfl⟩ : syracuseStep 3667531 = 5501297) B5501297
theorem B2061911 : Blo 1285961 2061911 := bstep (se 1 (by rfl) ⟨1546433, by rfl⟩ : syracuseStep 2061911 = 3092867) B3092867
theorem B2897495 : Blo 1285961 2897495 := bstep (se 1 (by rfl) ⟨2173121, by rfl⟩ : syracuseStep 2897495 = 4346243) B4346243
theorem B1930841 : Blo 1285961 1930841 := bstep (se 2 (by rfl) ⟨724065, by rfl⟩ : syracuseStep 1930841 = 1448131) B1448131
theorem B4404887 : Blo 1285961 4404887 := bstep (se 1 (by rfl) ⟨3303665, by rfl⟩ : syracuseStep 4404887 = 6607331) B6607331
theorem B1447627 : Blo 1285961 1447627 := bstep (se 1 (by rfl) ⟨1085720, by rfl⟩ : syracuseStep 1447627 = 2171441) B2171441
theorem B1930955 : Blo 1285961 1930955 := bstep (se 1 (by rfl) ⟨1448216, by rfl⟩ : syracuseStep 1930955 = 2896433) B2896433
theorem B1930967 : Blo 1285961 1930967 := bstep (se 1 (by rfl) ⟨1448225, by rfl⟩ : syracuseStep 1930967 = 2896451) B2896451
theorem B3528409 : Blo 1285961 3528409 := bstep (se 2 (by rfl) ⟨1323153, by rfl⟩ : syracuseStep 3528409 = 2646307) B2646307
theorem B2897675 : Blo 1285961 2897675 := bstep (se 1 (by rfl) ⟨2173256, by rfl⟩ : syracuseStep 2897675 = 4346513) B4346513
theorem B1931033 : Blo 1285961 1931033 := bstep (se 2 (by rfl) ⟨724137, by rfl⟩ : syracuseStep 1931033 = 1448275) B1448275
theorem B7427885 : Blo 1285961 7427885 := bstep (se 3 (by rfl) ⟨1392728, by rfl⟩ : syracuseStep 7427885 = 2785457) B2785457
theorem B1447735 : Blo 1285961 1447735 := bstep (se 1 (by rfl) ⟨1085801, by rfl⟩ : syracuseStep 1447735 = 2171603) B2171603
theorem B2897729 : Blo 1285961 2897729 := bstep (se 2 (by rfl) ⟨1086648, by rfl⟩ : syracuseStep 2897729 = 2173297) B2173297
theorem B7821157 : Blo 1285961 7821157 := bstep (se 4 (by rfl) ⟨733233, by rfl⟩ : syracuseStep 7821157 = 1466467) B1466467
theorem B1931147 : Blo 1285961 1931147 := bstep (se 1 (by rfl) ⟨1448360, by rfl⟩ : syracuseStep 1931147 = 2896721) B2896721
theorem B6600599 : Blo 1285961 6600599 := bstep (se 1 (by rfl) ⟨4950449, by rfl⟩ : syracuseStep 6600599 = 9900899) B9900899
theorem B1931159 : Blo 1285961 1931159 := bstep (se 1 (by rfl) ⟨1448369, by rfl⟩ : syracuseStep 1931159 = 2896739) B2896739
theorem B5953459 : Blo 1285961 5953459 := bstep (se 1 (by rfl) ⟨4465094, by rfl⟩ : syracuseStep 5953459 = 8930189) B8930189
theorem B1931225 : Blo 1285961 1931225 := bstep (se 2 (by rfl) ⟨724209, by rfl⟩ : syracuseStep 1931225 = 1448419) B1448419
theorem B1447915 : Blo 1285961 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B9271361 : Blo 1285961 9271361 := bstep (se 2 (by rfl) ⟨3476760, by rfl⟩ : syracuseStep 9271361 = 6953521) B6953521
theorem B1931339 : Blo 1285961 1931339 := bstep (se 1 (by rfl) ⟨1448504, by rfl⟩ : syracuseStep 1931339 = 2897009) B2897009
theorem B1448023 : Blo 1285961 1448023 := bstep (se 1 (by rfl) ⟨1086017, by rfl⟩ : syracuseStep 1448023 = 2172035) B2172035
theorem B1546327 : Blo 1285961 1546327 := bstep (se 1 (by rfl) ⟨1159745, by rfl⟩ : syracuseStep 1546327 = 2319491) B2319491
theorem B1931351 : Blo 1285961 1931351 := bstep (se 1 (by rfl) ⟨1448513, by rfl⟩ : syracuseStep 1931351 = 2897027) B2897027
theorem B5871761 : Blo 1285961 5871761 := bstep (se 2 (by rfl) ⟨2201910, by rfl⟩ : syracuseStep 5871761 = 4403821) B4403821
theorem B1931417 : Blo 1285961 1931417 := bstep (se 2 (by rfl) ⟨724281, by rfl⟩ : syracuseStep 1931417 = 1448563) B1448563
theorem B1628363 : Blo 1285961 1628363 := bstep (se 1 (by rfl) ⟨1221272, by rfl⟩ : syracuseStep 1628363 = 2442545) B2442545
theorem B1718489 : Blo 1285961 1718489 := bstep (se 2 (by rfl) ⟨644433, by rfl⟩ : syracuseStep 1718489 = 1288867) B1288867
theorem B1448203 : Blo 1285961 1448203 := bstep (se 1 (by rfl) ⟨1086152, by rfl⟩ : syracuseStep 1448203 = 2172305) B2172305
theorem B1931531 : Blo 1285961 1931531 := bstep (se 1 (by rfl) ⟨1448648, by rfl⟩ : syracuseStep 1931531 = 2897297) B2897297
theorem B4954391 : Blo 1285961 4954391 := bstep (se 1 (by rfl) ⟨3715793, by rfl⟩ : syracuseStep 4954391 = 7431587) B7431587
theorem B1931543 : Blo 1285961 1931543 := bstep (se 1 (by rfl) ⟨1448657, by rfl⟩ : syracuseStep 1931543 = 2897315) B2897315
theorem B1931609 : Blo 1285961 1931609 := bstep (se 2 (by rfl) ⟨724353, by rfl⟩ : syracuseStep 1931609 = 1448707) B1448707
theorem B6510941 : Blo 1285961 6510941 := bstep (se 3 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 6510941 = 2441603) B2441603
theorem B1448311 : Blo 1285961 1448311 := bstep (se 1 (by rfl) ⟨1086233, by rfl⟩ : syracuseStep 1448311 = 2172467) B2172467
theorem B1833367 : Blo 1285961 1833367 := bstep (se 1 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 1833367 = 2750051) B2750051
theorem B12368305 : Blo 1285961 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B1931723 : Blo 1285961 1931723 := bstep (se 1 (by rfl) ⟨1448792, by rfl⟩ : syracuseStep 1931723 = 2897585) B2897585
theorem B1931735 : Blo 1285961 1931735 := bstep (se 1 (by rfl) ⟨1448801, by rfl⟩ : syracuseStep 1931735 = 2897603) B2897603
theorem B1931801 : Blo 1285961 1931801 := bstep (se 2 (by rfl) ⟨724425, by rfl⟩ : syracuseStep 1931801 = 1448851) B1448851
theorem B1448491 : Blo 1285961 1448491 := bstep (se 1 (by rfl) ⟨1086368, by rfl⟩ : syracuseStep 1448491 = 2172737) B2172737
theorem B9779777 : Blo 1285961 9779777 := bstep (se 2 (by rfl) ⟨3667416, by rfl⟩ : syracuseStep 9779777 = 7334833) B7334833
theorem B1931915 : Blo 1285961 1931915 := bstep (se 1 (by rfl) ⟨1448936, by rfl⟩ : syracuseStep 1931915 = 2897873) B2897873
theorem B1448599 : Blo 1285961 1448599 := bstep (se 1 (by rfl) ⟨1086449, by rfl⟩ : syracuseStep 1448599 = 2172899) B2172899
theorem B2062999 : Blo 1285961 2062999 := bstep (se 1 (by rfl) ⟨1547249, by rfl⟩ : syracuseStep 2062999 = 3094499) B3094499
theorem B1931927 : Blo 1285961 1931927 := bstep (se 1 (by rfl) ⟨1448945, by rfl⟩ : syracuseStep 1931927 = 2897891) B2897891
theorem B4889267 : Blo 1285961 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B4889281 : Blo 1285961 4889281 := bstep (se 2 (by rfl) ⟨1833480, by rfl⟩ : syracuseStep 4889281 = 3666961) B3666961
theorem B3300043 : Blo 1285961 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B3259187 : Blo 1285961 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B1375051 : Blo 1285961 1375051 := bstep (se 1 (by rfl) ⟨1031288, by rfl⟩ : syracuseStep 1375051 = 2062577) B2062577
theorem B1448779 : Blo 1285961 1448779 := bstep (se 1 (by rfl) ⟨1086584, by rfl⟩ : syracuseStep 1448779 = 2173169) B2173169
theorem B4340573 : Blo 1285961 4340573 := bstep (se 3 (by rfl) ⟨813857, by rfl⟩ : syracuseStep 4340573 = 1627715) B1627715
theorem B1629067 : Blo 1285961 1629067 := bstep (se 1 (by rfl) ⟨1221800, by rfl⟩ : syracuseStep 1629067 = 2443601) B2443601
theorem B1448887 : Blo 1285961 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B16489433 : Blo 1285961 16489433 := bstep (se 2 (by rfl) ⟨6183537, by rfl⟩ : syracuseStep 16489433 = 12367075) B12367075
theorem B1629335 : Blo 1285961 1629335 := bstep (se 1 (by rfl) ⟨1222001, by rfl⟩ : syracuseStep 1629335 = 2444003) B2444003
theorem B3259723 : Blo 1285961 3259723 := bstep (se 1 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 3259723 = 4889585) B4889585
theorem B2170199 : Blo 1285961 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B4120001 : Blo 1285961 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B2170327 : Blo 1285961 2170327 := bstep (se 1 (by rfl) ⟨1627745, by rfl⟩ : syracuseStep 2170327 = 3255491) B3255491
theorem B3259865 : Blo 1285961 3259865 := bstep (se 2 (by rfl) ⟨1222449, by rfl⟩ : syracuseStep 3259865 = 2444899) B2444899
theorem B5217815 : Blo 1285961 5217815 := bstep (se 1 (by rfl) ⟨3913361, by rfl⟩ : syracuseStep 5217815 = 7826723) B7826723
theorem B15646243 : Blo 1285961 15646243 := bstep (se 1 (by rfl) ⟨11734682, by rfl⟩ : syracuseStep 15646243 = 23469365) B23469365
theorem B5217995 : Blo 1285961 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B5496599 : Blo 1285961 5496599 := bstep (se 1 (by rfl) ⟨4122449, by rfl⟩ : syracuseStep 5496599 = 8244899) B8244899
theorem B6954797 : Blo 1285961 6954797 := bstep (se 3 (by rfl) ⟨1304024, by rfl⟩ : syracuseStep 6954797 = 2608049) B2608049
theorem B1285963 : Blo 1285961 1285963 := bstep (se 1 (by rfl) ⟨964472, by rfl⟩ : syracuseStep 1285963 = 1928945) B1928945
theorem B1285975 : Blo 1285961 1285975 := bstep (se 1 (by rfl) ⟨964481, by rfl⟩ : syracuseStep 1285975 = 1928963) B1928963
theorem B1630039 : Blo 1285961 1630039 := bstep (se 1 (by rfl) ⟨1222529, by rfl⟩ : syracuseStep 1630039 = 2445059) B2445059
theorem B5218141 : Blo 1285961 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B1285995 : Blo 1285961 1285995 := bstep (se 1 (by rfl) ⟨964496, by rfl⟩ : syracuseStep 1285995 = 1928993) B1928993
theorem B1286007 : Blo 1285961 1286007 := bstep (se 1 (by rfl) ⟨964505, by rfl⟩ : syracuseStep 1286007 = 1929011) B1929011
theorem B1286027 : Blo 1285961 1286027 := bstep (se 1 (by rfl) ⟨964520, by rfl⟩ : syracuseStep 1286027 = 1929041) B1929041
theorem B1286039 : Blo 1285961 1286039 := bstep (se 1 (by rfl) ⟨964529, by rfl⟩ : syracuseStep 1286039 = 1929059) B1929059
theorem B7331735 : Blo 1285961 7331735 := bstep (se 1 (by rfl) ⟨5498801, by rfl⟩ : syracuseStep 7331735 = 10997603) B10997603
theorem B1286059 : Blo 1285961 1286059 := bstep (se 1 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 1286059 = 1929089) B1929089
theorem B18087857 : Blo 1285961 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B1286071 : Blo 1285961 1286071 := bstep (se 1 (by rfl) ⟨964553, by rfl⟩ : syracuseStep 1286071 = 1929107) B1929107
theorem B1286091 : Blo 1285961 1286091 := bstep (se 1 (by rfl) ⟨964568, by rfl⟩ : syracuseStep 1286091 = 1929137) B1929137
theorem B4341707 : Blo 1285961 4341707 := bstep (se 1 (by rfl) ⟨3256280, by rfl⟩ : syracuseStep 4341707 = 6512561) B6512561
theorem B1286103 : Blo 1285961 1286103 := bstep (se 1 (by rfl) ⟨964577, by rfl⟩ : syracuseStep 1286103 = 1929155) B1929155
theorem B4120541 : Blo 1285961 4120541 := bstep (se 3 (by rfl) ⟨772601, by rfl⟩ : syracuseStep 4120541 = 1545203) B1545203
theorem B1286123 : Blo 1285961 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B2318323 : Blo 1285961 2318323 := bstep (se 1 (by rfl) ⟨1738742, by rfl⟩ : syracuseStep 2318323 = 3477485) B3477485
theorem B1286135 : Blo 1285961 1286135 := bstep (se 1 (by rfl) ⟨964601, by rfl⟩ : syracuseStep 1286135 = 1929203) B1929203
theorem B1286151 : Blo 1285961 1286151 := bstep (se 1 (by rfl) ⟨964613, by rfl⟩ : syracuseStep 1286151 = 1929227) B1929227
theorem B1286159 : Blo 1285961 1286159 := bstep (se 1 (by rfl) ⟨964619, by rfl⟩ : syracuseStep 1286159 = 1929239) B1929239
theorem B1286203 : Blo 1285961 1286203 := bstep (se 1 (by rfl) ⟨964652, by rfl⟩ : syracuseStep 1286203 = 1929305) B1929305
theorem B1286279 : Blo 1285961 1286279 := bstep (se 1 (by rfl) ⟨964709, by rfl⟩ : syracuseStep 1286279 = 1929419) B1929419
theorem B1286287 : Blo 1285961 1286287 := bstep (se 1 (by rfl) ⟨964715, by rfl⟩ : syracuseStep 1286287 = 1929431) B1929431
theorem B1286331 : Blo 1285961 1286331 := bstep (se 1 (by rfl) ⟨964748, by rfl⟩ : syracuseStep 1286331 = 1929497) B1929497
theorem B1286407 : Blo 1285961 1286407 := bstep (se 1 (by rfl) ⟨964805, by rfl⟩ : syracuseStep 1286407 = 1929611) B1929611
theorem B1286415 : Blo 1285961 1286415 := bstep (se 1 (by rfl) ⟨964811, by rfl⟩ : syracuseStep 1286415 = 1929623) B1929623
theorem B4342031 : Blo 1285961 4342031 := bstep (se 1 (by rfl) ⟨3256523, by rfl⟩ : syracuseStep 4342031 = 6513047) B6513047
theorem B6185231 : Blo 1285961 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B1286459 : Blo 1285961 1286459 := bstep (se 1 (by rfl) ⟨964844, by rfl⟩ : syracuseStep 1286459 = 1929689) B1929689
theorem B1286535 : Blo 1285961 1286535 := bstep (se 1 (by rfl) ⟨964901, by rfl⟩ : syracuseStep 1286535 = 1929803) B1929803
theorem B1286543 : Blo 1285961 1286543 := bstep (se 1 (by rfl) ⟨964907, by rfl⟩ : syracuseStep 1286543 = 1929815) B1929815
theorem B9773459 : Blo 1285961 9773459 := bstep (se 1 (by rfl) ⟨7330094, by rfl⟩ : syracuseStep 9773459 = 14660189) B14660189
theorem B2441657 : Blo 1285961 2441657 := bstep (se 2 (by rfl) ⟨915621, by rfl⟩ : syracuseStep 2441657 = 1831243) B1831243
theorem B1286587 : Blo 1285961 1286587 := bstep (se 1 (by rfl) ⟨964940, by rfl⟩ : syracuseStep 1286587 = 1929881) B1929881
theorem B1286663 : Blo 1285961 1286663 := bstep (se 1 (by rfl) ⟨964997, by rfl⟩ : syracuseStep 1286663 = 1929995) B1929995
theorem B1286671 : Blo 1285961 1286671 := bstep (se 1 (by rfl) ⟨965003, by rfl⟩ : syracuseStep 1286671 = 1930007) B1930007
theorem B2171407 : Blo 1285961 2171407 := bstep (se 1 (by rfl) ⟨1628555, by rfl⟩ : syracuseStep 2171407 = 3257111) B3257111
theorem B4342301 : Blo 1285961 4342301 := bstep (se 3 (by rfl) ⟨814181, by rfl⟩ : syracuseStep 4342301 = 1628363) B1628363
theorem B1286715 : Blo 1285961 1286715 := bstep (se 1 (by rfl) ⟨965036, by rfl⟩ : syracuseStep 1286715 = 1930073) B1930073
theorem B16491073 : Blo 1285961 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B9273923 : Blo 1285961 9273923 := bstep (se 1 (by rfl) ⟨6955442, by rfl⟩ : syracuseStep 9273923 = 13910885) B13910885
theorem B1286791 : Blo 1285961 1286791 := bstep (se 1 (by rfl) ⟨965093, by rfl⟩ : syracuseStep 1286791 = 1930187) B1930187
theorem B1286799 : Blo 1285961 1286799 := bstep (se 1 (by rfl) ⟨965099, by rfl⟩ : syracuseStep 1286799 = 1930199) B1930199
theorem B1286843 : Blo 1285961 1286843 := bstep (se 1 (by rfl) ⟨965132, by rfl⟩ : syracuseStep 1286843 = 1930265) B1930265
theorem B1286919 : Blo 1285961 1286919 := bstep (se 1 (by rfl) ⟨965189, by rfl⟩ : syracuseStep 1286919 = 1930379) B1930379
theorem B1286927 : Blo 1285961 1286927 := bstep (se 1 (by rfl) ⟨965195, by rfl⟩ : syracuseStep 1286927 = 1930391) B1930391
theorem B11002661 : Blo 1285961 11002661 := bstep (se 4 (by rfl) ⟨1031499, by rfl⟩ : syracuseStep 11002661 = 2062999) B2062999
theorem B9765683 : Blo 1285961 9765683 := bstep (se 1 (by rfl) ⟨7324262, by rfl⟩ : syracuseStep 9765683 = 14648525) B14648525
theorem B1286971 : Blo 1285961 1286971 := bstep (se 1 (by rfl) ⟨965228, by rfl⟩ : syracuseStep 1286971 = 1930457) B1930457
theorem B14664563 : Blo 1285961 14664563 := bstep (se 1 (by rfl) ⟨10998422, by rfl⟩ : syracuseStep 14664563 = 21996845) B21996845
theorem B1287047 : Blo 1285961 1287047 := bstep (se 1 (by rfl) ⟨965285, by rfl⟩ : syracuseStep 1287047 = 1930571) B1930571
theorem B1287055 : Blo 1285961 1287055 := bstep (se 1 (by rfl) ⟨965291, by rfl⟩ : syracuseStep 1287055 = 1930583) B1930583
theorem B4400057 : Blo 1285961 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B1287099 : Blo 1285961 1287099 := bstep (se 1 (by rfl) ⟨965324, by rfl⟩ : syracuseStep 1287099 = 1930649) B1930649
theorem B1287175 : Blo 1285961 1287175 := bstep (se 1 (by rfl) ⟨965381, by rfl⟩ : syracuseStep 1287175 = 1930763) B1930763
theorem B7332875 : Blo 1285961 7332875 := bstep (se 1 (by rfl) ⟨5499656, by rfl⟩ : syracuseStep 7332875 = 10999313) B10999313
theorem B1287183 : Blo 1285961 1287183 := bstep (se 1 (by rfl) ⟨965387, by rfl⟩ : syracuseStep 1287183 = 1930775) B1930775
theorem B2171947 : Blo 1285961 2171947 := bstep (se 1 (by rfl) ⟨1628960, by rfl⟩ : syracuseStep 2171947 = 3257921) B3257921
theorem B1287227 : Blo 1285961 1287227 := bstep (se 1 (by rfl) ⟨965420, by rfl⟩ : syracuseStep 1287227 = 1930841) B1930841
theorem B1287303 : Blo 1285961 1287303 := bstep (se 1 (by rfl) ⟨965477, by rfl⟩ : syracuseStep 1287303 = 1930955) B1930955
theorem B1287311 : Blo 1285961 1287311 := bstep (se 1 (by rfl) ⟨965483, by rfl⟩ : syracuseStep 1287311 = 1930967) B1930967
theorem B2172089 : Blo 1285961 2172089 := bstep (se 2 (by rfl) ⟨814533, by rfl⟩ : syracuseStep 2172089 = 1629067) B1629067
theorem B1287355 : Blo 1285961 1287355 := bstep (se 1 (by rfl) ⟨965516, by rfl⟩ : syracuseStep 1287355 = 1931033) B1931033
theorem B6513857 : Blo 1285961 6513857 := bstep (se 2 (by rfl) ⟨2442696, by rfl⟩ : syracuseStep 6513857 = 4885393) B4885393
theorem B7324901 : Blo 1285961 7324901 := bstep (se 4 (by rfl) ⟨686709, by rfl⟩ : syracuseStep 7324901 = 1373419) B1373419
theorem B1287431 : Blo 1285961 1287431 := bstep (se 1 (by rfl) ⟨965573, by rfl⟩ : syracuseStep 1287431 = 1931147) B1931147
theorem B4400399 : Blo 1285961 4400399 := bstep (se 1 (by rfl) ⟨3300299, by rfl⟩ : syracuseStep 4400399 = 6600599) B6600599
theorem B1287439 : Blo 1285961 1287439 := bstep (se 1 (by rfl) ⟨965579, by rfl⟩ : syracuseStep 1287439 = 1931159) B1931159
theorem B10716475 : Blo 1285961 10716475 := bstep (se 1 (by rfl) ⟨8037356, by rfl⟩ : syracuseStep 10716475 = 16074713) B16074713
theorem B1287483 : Blo 1285961 1287483 := bstep (se 1 (by rfl) ⟨965612, by rfl⟩ : syracuseStep 1287483 = 1931225) B1931225
theorem B20874631 : Blo 1285961 20874631 := bstep (se 1 (by rfl) ⟨15655973, by rfl⟩ : syracuseStep 20874631 = 31311947) B31311947
theorem B1287559 : Blo 1285961 1287559 := bstep (se 1 (by rfl) ⟨965669, by rfl⟩ : syracuseStep 1287559 = 1931339) B1931339
theorem B1287567 : Blo 1285961 1287567 := bstep (se 1 (by rfl) ⟨965675, by rfl⟩ : syracuseStep 1287567 = 1931351) B1931351
theorem B1287611 : Blo 1285961 1287611 := bstep (se 1 (by rfl) ⟨965708, by rfl⟩ : syracuseStep 1287611 = 1931417) B1931417
theorem B6358475 : Blo 1285961 6358475 := bstep (se 1 (by rfl) ⟨4768856, by rfl⟩ : syracuseStep 6358475 = 9537713) B9537713
theorem B4883921 : Blo 1285961 4883921 := bstep (se 2 (by rfl) ⟨1831470, by rfl⟩ : syracuseStep 4883921 = 3662941) B3662941
theorem B1287687 : Blo 1285961 1287687 := bstep (se 1 (by rfl) ⟨965765, by rfl⟩ : syracuseStep 1287687 = 1931531) B1931531
theorem B3302927 : Blo 1285961 3302927 := bstep (se 1 (by rfl) ⟨2477195, by rfl⟩ : syracuseStep 3302927 = 4954391) B4954391
theorem B1287695 : Blo 1285961 1287695 := bstep (se 1 (by rfl) ⟨965771, by rfl⟩ : syracuseStep 1287695 = 1931543) B1931543
theorem B2442811 : Blo 1285961 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B1287739 : Blo 1285961 1287739 := bstep (se 1 (by rfl) ⟨965804, by rfl⟩ : syracuseStep 1287739 = 1931609) B1931609
theorem B1287815 : Blo 1285961 1287815 := bstep (se 1 (by rfl) ⟨965861, by rfl⟩ : syracuseStep 1287815 = 1931723) B1931723
theorem B1287823 : Blo 1285961 1287823 := bstep (se 1 (by rfl) ⟨965867, by rfl⟩ : syracuseStep 1287823 = 1931735) B1931735
theorem B1287867 : Blo 1285961 1287867 := bstep (se 1 (by rfl) ⟨965900, by rfl⟩ : syracuseStep 1287867 = 1931801) B1931801
theorem B47605477 : Blo 1285961 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B1287943 : Blo 1285961 1287943 := bstep (se 1 (by rfl) ⟨965957, by rfl⟩ : syracuseStep 1287943 = 1931915) B1931915
theorem B4884239 : Blo 1285961 4884239 := bstep (se 1 (by rfl) ⟨3663179, by rfl⟩ : syracuseStep 4884239 = 7326359) B7326359
theorem B1287951 : Blo 1285961 1287951 := bstep (se 1 (by rfl) ⟨965963, by rfl⟩ : syracuseStep 1287951 = 1931927) B1931927
theorem B2172791 : Blo 1285961 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B7325585 : Blo 1285961 7325585 := bstep (se 2 (by rfl) ⟨2747094, by rfl⟩ : syracuseStep 7325585 = 5494189) B5494189
theorem B2893715 : Blo 1285961 2893715 := bstep (se 1 (by rfl) ⟨2170286, by rfl⟩ : syracuseStep 2893715 = 4340573) B4340573
theorem B4343705 : Blo 1285961 4343705 := bstep (se 2 (by rfl) ⟨1628889, by rfl⟩ : syracuseStep 4343705 = 3257779) B3257779
theorem B2893769 : Blo 1285961 2893769 := bstep (se 2 (by rfl) ⟨1085163, by rfl⟩ : syracuseStep 2893769 = 2170327) B2170327
theorem B2443297 : Blo 1285961 2443297 := bstep (se 2 (by rfl) ⟨916236, by rfl⟩ : syracuseStep 2443297 = 1832473) B1832473
theorem B4704545 : Blo 1285961 4704545 := bstep (se 2 (by rfl) ⟨1764204, by rfl⟩ : syracuseStep 4704545 = 3528409) B3528409
theorem B2746667 : Blo 1285961 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B2173243 : Blo 1285961 2173243 := bstep (se 1 (by rfl) ⟨1629932, by rfl⟩ : syracuseStep 2173243 = 3259865) B3259865
theorem B8251793 : Blo 1285961 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B2173385 : Blo 1285961 2173385 := bstep (se 2 (by rfl) ⟨815019, by rfl⟩ : syracuseStep 2173385 = 1630039) B1630039
theorem B6515153 : Blo 1285961 6515153 := bstep (se 2 (by rfl) ⟨2443182, by rfl⟩ : syracuseStep 6515153 = 4886365) B4886365
theorem B6957521 : Blo 1285961 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B3664399 : Blo 1285961 3664399 := bstep (se 1 (by rfl) ⟨2748299, by rfl⟩ : syracuseStep 3664399 = 5496599) B5496599
theorem B4344407 : Blo 1285961 4344407 := bstep (se 1 (by rfl) ⟨3258305, by rfl⟩ : syracuseStep 4344407 = 6516611) B6516611
theorem B2894471 : Blo 1285961 2894471 := bstep (se 1 (by rfl) ⟨2170853, by rfl⟩ : syracuseStep 2894471 = 4341707) B4341707
theorem B2747027 : Blo 1285961 2747027 := bstep (se 1 (by rfl) ⟨2060270, by rfl⟩ : syracuseStep 2747027 = 4120541) B4120541
theorem B3091097 : Blo 1285961 3091097 := bstep (se 2 (by rfl) ⟨1159161, by rfl⟩ : syracuseStep 3091097 = 2318323) B2318323
theorem B3664673 : Blo 1285961 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B2894651 : Blo 1285961 2894651 := bstep (se 1 (by rfl) ⟨2170988, by rfl⟩ : syracuseStep 2894651 = 4341977) B4341977
theorem B1739639 : Blo 1285961 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B3255187 : Blo 1285961 3255187 := bstep (se 1 (by rfl) ⟨2441390, by rfl⟩ : syracuseStep 3255187 = 4882781) B4882781
theorem B7326611 : Blo 1285961 7326611 := bstep (se 1 (by rfl) ⟨5494958, by rfl⟩ : syracuseStep 7326611 = 10989917) B10989917
theorem B2894777 : Blo 1285961 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B3091385 : Blo 1285961 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B13216715 : Blo 1285961 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B3255329 : Blo 1285961 3255329 := bstep (se 2 (by rfl) ⟨1220748, by rfl⟩ : syracuseStep 3255329 = 2441497) B2441497
theorem B4344893 : Blo 1285961 4344893 := bstep (se 3 (by rfl) ⟨814667, by rfl⟩ : syracuseStep 4344893 = 1629335) B1629335
theorem B2444489 : Blo 1285961 2444489 := bstep (se 2 (by rfl) ⟨916683, by rfl⟩ : syracuseStep 2444489 = 1833367) B1833367
theorem B4582637 : Blo 1285961 4582637 := bstep (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) B1718489
theorem B20360429 : Blo 1285961 20360429 := bstep (se 3 (by rfl) ⟨3817580, by rfl⟩ : syracuseStep 20360429 = 7635161) B7635161
theorem B2895119 : Blo 1285961 2895119 := bstep (se 1 (by rfl) ⟨2171339, by rfl⟩ : syracuseStep 2895119 = 4342679) B4342679
theorem B2895137 : Blo 1285961 2895137 := bstep (se 2 (by rfl) ⟨1085676, by rfl⟩ : syracuseStep 2895137 = 2171353) B2171353
theorem B7048499 : Blo 1285961 7048499 := bstep (se 1 (by rfl) ⟨5286374, by rfl⟩ : syracuseStep 7048499 = 10572749) B10572749
theorem B6180155 : Blo 1285961 6180155 := bstep (se 1 (by rfl) ⟨4635116, by rfl⟩ : syracuseStep 6180155 = 9270233) B9270233
theorem B2608519 : Blo 1285961 2608519 := bstep (se 1 (by rfl) ⟨1956389, by rfl⟩ : syracuseStep 2608519 = 3912779) B3912779
theorem B15650333 : Blo 1285961 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B1740331 : Blo 1285961 1740331 := bstep (se 1 (by rfl) ⟨1305248, by rfl⟩ : syracuseStep 1740331 = 2610497) B2610497
theorem B2895479 : Blo 1285961 2895479 := bstep (se 1 (by rfl) ⟨2171609, by rfl⟩ : syracuseStep 2895479 = 4343219) B4343219
theorem B1928951 : Blo 1285961 1928951 := bstep (se 1 (by rfl) ⟨1446713, by rfl⟩ : syracuseStep 1928951 = 2893427) B2893427
theorem B3665675 : Blo 1285961 3665675 := bstep (se 1 (by rfl) ⟨2749256, by rfl⟩ : syracuseStep 3665675 = 5498513) B5498513
theorem B1928975 : Blo 1285961 1928975 := bstep (se 1 (by rfl) ⟨1446731, by rfl⟩ : syracuseStep 1928975 = 2893463) B2893463
theorem B2936591 : Blo 1285961 2936591 := bstep (se 1 (by rfl) ⟨2202443, by rfl⟩ : syracuseStep 2936591 = 4404887) B4404887
theorem B2895659 : Blo 1285961 2895659 := bstep (se 1 (by rfl) ⟨2171744, by rfl⟩ : syracuseStep 2895659 = 4343489) B4343489
theorem B1929017 : Blo 1285961 1929017 := bstep (se 2 (by rfl) ⟨723381, by rfl⟩ : syracuseStep 1929017 = 1446763) B1446763
theorem B1929095 : Blo 1285961 1929095 := bstep (se 1 (by rfl) ⟨1446821, by rfl⟩ : syracuseStep 1929095 = 2893643) B2893643
theorem B1929131 : Blo 1285961 1929131 := bstep (se 1 (by rfl) ⟨1446848, by rfl⟩ : syracuseStep 1929131 = 2893697) B2893697
theorem B1929161 : Blo 1285961 1929161 := bstep (se 2 (by rfl) ⟨723435, by rfl⟩ : syracuseStep 1929161 = 1446871) B1446871
theorem B3256321 : Blo 1285961 3256321 := bstep (se 2 (by rfl) ⟨1221120, by rfl⟩ : syracuseStep 3256321 = 2442241) B2442241
theorem B6180907 : Blo 1285961 6180907 := bstep (se 1 (by rfl) ⟨4635680, by rfl⟩ : syracuseStep 6180907 = 9271361) B9271361
theorem B1929275 : Blo 1285961 1929275 := bstep (se 1 (by rfl) ⟨1446956, by rfl⟩ : syracuseStep 1929275 = 2893913) B2893913
theorem B13914173 : Blo 1285961 13914173 := bstep (se 3 (by rfl) ⟨2608907, by rfl⟩ : syracuseStep 13914173 = 5217815) B5217815
theorem B1929335 : Blo 1285961 1929335 := bstep (se 1 (by rfl) ⟨1447001, by rfl⟩ : syracuseStep 1929335 = 2894003) B2894003
theorem B1929359 : Blo 1285961 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B2896019 : Blo 1285961 2896019 := bstep (se 1 (by rfl) ⟨2172014, by rfl⟩ : syracuseStep 2896019 = 4344029) B4344029
theorem B3666073 : Blo 1285961 3666073 := bstep (se 2 (by rfl) ⟨1374777, by rfl⟩ : syracuseStep 3666073 = 2749555) B2749555
theorem B1929401 : Blo 1285961 1929401 := bstep (se 2 (by rfl) ⟨723525, by rfl⟩ : syracuseStep 1929401 = 1447051) B1447051
theorem B2896073 : Blo 1285961 2896073 := bstep (se 2 (by rfl) ⟨1086027, by rfl⟩ : syracuseStep 2896073 = 2172055) B2172055
theorem B1929479 : Blo 1285961 1929479 := bstep (se 1 (by rfl) ⟨1447109, by rfl⟩ : syracuseStep 1929479 = 2894219) B2894219
theorem B1929515 : Blo 1285961 1929515 := bstep (se 1 (by rfl) ⟨1447136, by rfl⟩ : syracuseStep 1929515 = 2894273) B2894273
theorem B1929545 : Blo 1285961 1929545 := bstep (se 2 (by rfl) ⟨723579, by rfl⟩ : syracuseStep 1929545 = 1447159) B1447159
theorem B3666323 : Blo 1285961 3666323 := bstep (se 1 (by rfl) ⟨2749742, by rfl⟩ : syracuseStep 3666323 = 5499485) B5499485
theorem B1831339 : Blo 1285961 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B4346297 : Blo 1285961 4346297 := bstep (se 2 (by rfl) ⟨1629861, by rfl⟩ : syracuseStep 4346297 = 3259723) B3259723
theorem B1929659 : Blo 1285961 1929659 := bstep (se 1 (by rfl) ⟨1447244, by rfl⟩ : syracuseStep 1929659 = 2894489) B2894489
theorem B1929719 : Blo 1285961 1929719 := bstep (se 1 (by rfl) ⟨1447289, by rfl⟩ : syracuseStep 1929719 = 2894579) B2894579
theorem B6517259 : Blo 1285961 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B1929743 : Blo 1285961 1929743 := bstep (se 1 (by rfl) ⟨1447307, by rfl⟩ : syracuseStep 1929743 = 2894615) B2894615
theorem B2060815 : Blo 1285961 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B1929785 : Blo 1285961 1929785 := bstep (se 2 (by rfl) ⟨723669, by rfl⟩ : syracuseStep 1929785 = 1447339) B1447339
theorem B3256919 : Blo 1285961 3256919 := bstep (se 1 (by rfl) ⟨2442689, by rfl⟩ : syracuseStep 3256919 = 4885379) B4885379
theorem B8925815 : Blo 1285961 8925815 := bstep (se 1 (by rfl) ⟨6694361, by rfl⟩ : syracuseStep 8925815 = 13388723) B13388723
theorem B1929863 : Blo 1285961 1929863 := bstep (se 1 (by rfl) ⟨1447397, by rfl⟩ : syracuseStep 1929863 = 2894795) B2894795
theorem B1831567 : Blo 1285961 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B1929899 : Blo 1285961 1929899 := bstep (se 1 (by rfl) ⟨1447424, by rfl⟩ : syracuseStep 1929899 = 2894849) B2894849
theorem B6517421 : Blo 1285961 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B1929929 : Blo 1285961 1929929 := bstep (se 2 (by rfl) ⟨723723, by rfl⟩ : syracuseStep 1929929 = 1447447) B1447447
theorem B20861657 : Blo 1285961 20861657 := bstep (se 2 (by rfl) ⟨7823121, by rfl⟩ : syracuseStep 20861657 = 15646243) B15646243
theorem B3257131 : Blo 1285961 3257131 := bstep (se 1 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 3257131 = 4885697) B4885697
theorem B1930043 : Blo 1285961 1930043 := bstep (se 1 (by rfl) ⟨1447532, by rfl⟩ : syracuseStep 1930043 = 2895065) B2895065
theorem B1930103 : Blo 1285961 1930103 := bstep (se 1 (by rfl) ⟨1447577, by rfl⟩ : syracuseStep 1930103 = 2895155) B2895155
theorem B2896775 : Blo 1285961 2896775 := bstep (se 1 (by rfl) ⟨2172581, by rfl⟩ : syracuseStep 2896775 = 4345163) B4345163
theorem B1446799 : Blo 1285961 1446799 := bstep (se 1 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 1446799 = 2170199) B2170199
theorem B1930127 : Blo 1285961 1930127 := bstep (se 1 (by rfl) ⟨1447595, by rfl⟩ : syracuseStep 1930127 = 2895191) B2895191
theorem B1930169 : Blo 1285961 1930169 := bstep (se 2 (by rfl) ⟨723813, by rfl⟩ : syracuseStep 1930169 = 1447627) B1447627
theorem B3257273 : Blo 1285961 3257273 := bstep (se 2 (by rfl) ⟨1221477, by rfl⟩ : syracuseStep 3257273 = 2442955) B2442955
theorem B1831943 : Blo 1285961 1831943 := bstep (se 1 (by rfl) ⟨1373957, by rfl⟩ : syracuseStep 1831943 = 2747915) B2747915
theorem B1930247 : Blo 1285961 1930247 := bstep (se 1 (by rfl) ⟨1447685, by rfl⟩ : syracuseStep 1930247 = 2895371) B2895371
theorem B1930283 : Blo 1285961 1930283 := bstep (se 1 (by rfl) ⟨1447712, by rfl⟩ : syracuseStep 1930283 = 2895425) B2895425
theorem B2896955 : Blo 1285961 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B1930313 : Blo 1285961 1930313 := bstep (se 2 (by rfl) ⟨723867, by rfl⟩ : syracuseStep 1930313 = 1447735) B1447735
theorem B3478663 : Blo 1285961 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B3716243 : Blo 1285961 3716243 := bstep (se 1 (by rfl) ⟨2787182, by rfl⟩ : syracuseStep 3716243 = 5574365) B5574365
theorem B2897081 : Blo 1285961 2897081 := bstep (se 2 (by rfl) ⟨1086405, by rfl⟩ : syracuseStep 2897081 = 2172811) B2172811
theorem B1930427 : Blo 1285961 1930427 := bstep (se 1 (by rfl) ⟨1447820, by rfl⟩ : syracuseStep 1930427 = 2895641) B2895641
theorem B1930487 : Blo 1285961 1930487 := bstep (se 1 (by rfl) ⟨1447865, by rfl⟩ : syracuseStep 1930487 = 2895731) B2895731
theorem B4887809 : Blo 1285961 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B1930511 : Blo 1285961 1930511 := bstep (se 1 (by rfl) ⟨1447883, by rfl⟩ : syracuseStep 1930511 = 2895767) B2895767
theorem B4887823 : Blo 1285961 4887823 := bstep (se 1 (by rfl) ⟨3665867, by rfl⟩ : syracuseStep 4887823 = 7331735) B7331735
theorem B1930553 : Blo 1285961 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B3667315 : Blo 1285961 3667315 := bstep (se 1 (by rfl) ⟨2750486, by rfl⟩ : syracuseStep 3667315 = 5500973) B5500973
theorem B16504195 : Blo 1285961 16504195 := bstep (se 1 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 16504195 = 24756293) B24756293
theorem B1447303 : Blo 1285961 1447303 := bstep (se 1 (by rfl) ⟨1085477, by rfl⟩ : syracuseStep 1447303 = 2170955) B2170955
theorem B1930631 : Blo 1285961 1930631 := bstep (se 1 (by rfl) ⟨1447973, by rfl⟩ : syracuseStep 1930631 = 2895947) B2895947
theorem B1930667 : Blo 1285961 1930667 := bstep (se 1 (by rfl) ⟨1448000, by rfl⟩ : syracuseStep 1930667 = 2896001) B2896001
theorem B1930697 : Blo 1285961 1930697 := bstep (se 2 (by rfl) ⟨724011, by rfl⟩ : syracuseStep 1930697 = 1448023) B1448023
theorem B2061769 : Blo 1285961 2061769 := bstep (se 2 (by rfl) ⟨773163, by rfl⟩ : syracuseStep 2061769 = 1546327) B1546327
theorem B2897423 : Blo 1285961 2897423 := bstep (se 1 (by rfl) ⟨2173067, by rfl⟩ : syracuseStep 2897423 = 4346135) B4346135
theorem B2897441 : Blo 1285961 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B4404779 : Blo 1285961 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B1447483 : Blo 1285961 1447483 := bstep (se 1 (by rfl) ⟨1085612, by rfl⟩ : syracuseStep 1447483 = 2171225) B2171225
theorem B1930811 : Blo 1285961 1930811 := bstep (se 1 (by rfl) ⟨1448108, by rfl⟩ : syracuseStep 1930811 = 2896217) B2896217
theorem B1930871 : Blo 1285961 1930871 := bstep (se 1 (by rfl) ⟨1448153, by rfl⟩ : syracuseStep 1930871 = 2896307) B2896307
theorem B1930895 : Blo 1285961 1930895 := bstep (se 1 (by rfl) ⟨1448171, by rfl⟩ : syracuseStep 1930895 = 2896343) B2896343
theorem B1930937 : Blo 1285961 1930937 := bstep (se 2 (by rfl) ⟨724101, by rfl⟩ : syracuseStep 1930937 = 1448203) B1448203
theorem B1931015 : Blo 1285961 1931015 := bstep (se 1 (by rfl) ⟨1448261, by rfl⟩ : syracuseStep 1931015 = 2896523) B2896523
theorem B1931051 : Blo 1285961 1931051 := bstep (se 1 (by rfl) ⟨1448288, by rfl⟩ : syracuseStep 1931051 = 2896577) B2896577
theorem B79230773 : Blo 1285961 79230773 := bstep (se 5 (by rfl) ⟨3713942, by rfl⟩ : syracuseStep 79230773 = 7427885) B7427885
theorem B1931081 : Blo 1285961 1931081 := bstep (se 2 (by rfl) ⟨724155, by rfl⟩ : syracuseStep 1931081 = 1448311) B1448311
theorem B12367691 : Blo 1285961 12367691 := bstep (se 1 (by rfl) ⟨9275768, by rfl⟩ : syracuseStep 12367691 = 18551537) B18551537
theorem B2062199 : Blo 1285961 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B2897783 : Blo 1285961 2897783 := bstep (se 1 (by rfl) ⟨2173337, by rfl⟩ : syracuseStep 2897783 = 4346675) B4346675
theorem B1628039 : Blo 1285961 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B3258265 : Blo 1285961 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B1931195 : Blo 1285961 1931195 := bstep (se 1 (by rfl) ⟨1448396, by rfl⟩ : syracuseStep 1931195 = 2896793) B2896793
theorem B6264785 : Blo 1285961 6264785 := bstep (se 2 (by rfl) ⟨2349294, by rfl⟩ : syracuseStep 6264785 = 4698589) B4698589
theorem B1546231 : Blo 1285961 1546231 := bstep (se 1 (by rfl) ⟨1159673, by rfl⟩ : syracuseStep 1546231 = 2319347) B2319347
theorem B1931255 : Blo 1285961 1931255 := bstep (se 1 (by rfl) ⟨1448441, by rfl⟩ : syracuseStep 1931255 = 2896883) B2896883
theorem B1447951 : Blo 1285961 1447951 := bstep (se 1 (by rfl) ⟨1085963, by rfl⟩ : syracuseStep 1447951 = 2171927) B2171927
theorem B1931279 : Blo 1285961 1931279 := bstep (se 1 (by rfl) ⟨1448459, by rfl⟩ : syracuseStep 1931279 = 2896919) B2896919
theorem B6273047 : Blo 1285961 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B1931321 : Blo 1285961 1931321 := bstep (se 2 (by rfl) ⟨724245, by rfl⟩ : syracuseStep 1931321 = 1448491) B1448491
theorem B3258427 : Blo 1285961 3258427 := bstep (se 1 (by rfl) ⟨2443820, by rfl⟩ : syracuseStep 3258427 = 4887641) B4887641
theorem B8247383 : Blo 1285961 8247383 := bstep (se 1 (by rfl) ⟨6185537, by rfl⟩ : syracuseStep 8247383 = 12371075) B12371075
theorem B12376151 : Blo 1285961 12376151 := bstep (se 1 (by rfl) ⟨9282113, by rfl⟩ : syracuseStep 12376151 = 18564227) B18564227
theorem B1931399 : Blo 1285961 1931399 := bstep (se 1 (by rfl) ⟨1448549, by rfl⟩ : syracuseStep 1931399 = 2897099) B2897099
theorem B27121837 : Blo 1285961 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B1931435 : Blo 1285961 1931435 := bstep (se 1 (by rfl) ⟨1448576, by rfl⟩ : syracuseStep 1931435 = 2897153) B2897153
theorem B3258569 : Blo 1285961 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B3135689 : Blo 1285961 3135689 := bstep (se 2 (by rfl) ⟨1175883, by rfl⟩ : syracuseStep 3135689 = 2351767) B2351767
theorem B1931465 : Blo 1285961 1931465 := bstep (se 2 (by rfl) ⟨724299, by rfl⟩ : syracuseStep 1931465 = 1448599) B1448599
theorem B6519041 : Blo 1285961 6519041 := bstep (se 2 (by rfl) ⟨2444640, by rfl⟩ : syracuseStep 6519041 = 4889281) B4889281
theorem B1931579 : Blo 1285961 1931579 := bstep (se 1 (by rfl) ⟨1448684, by rfl⟩ : syracuseStep 1931579 = 2897369) B2897369
theorem B3479927 : Blo 1285961 3479927 := bstep (se 1 (by rfl) ⟨2609945, by rfl⟩ : syracuseStep 3479927 = 5219891) B5219891
theorem B1931639 : Blo 1285961 1931639 := bstep (se 1 (by rfl) ⟨1448729, by rfl⟩ : syracuseStep 1931639 = 2897459) B2897459
theorem B1374607 : Blo 1285961 1374607 := bstep (se 1 (by rfl) ⟨1030955, by rfl⟩ : syracuseStep 1374607 = 2061911) B2061911
theorem B1931663 : Blo 1285961 1931663 := bstep (se 1 (by rfl) ⟨1448747, by rfl⟩ : syracuseStep 1931663 = 2897495) B2897495
theorem B1833401 : Blo 1285961 1833401 := bstep (se 2 (by rfl) ⟨687525, by rfl⟩ : syracuseStep 1833401 = 1375051) B1375051
theorem B1931705 : Blo 1285961 1931705 := bstep (se 2 (by rfl) ⟨724389, by rfl⟩ : syracuseStep 1931705 = 1448779) B1448779
theorem B1448455 : Blo 1285961 1448455 := bstep (se 1 (by rfl) ⟨1086341, by rfl⟩ : syracuseStep 1448455 = 2172683) B2172683
theorem B1931783 : Blo 1285961 1931783 := bstep (se 1 (by rfl) ⟨1448837, by rfl⟩ : syracuseStep 1931783 = 2897675) B2897675
theorem B4889099 : Blo 1285961 4889099 := bstep (se 1 (by rfl) ⟨3666824, by rfl⟩ : syracuseStep 4889099 = 7333649) B7333649
theorem B1628687 : Blo 1285961 1628687 := bstep (se 1 (by rfl) ⟨1221515, by rfl⟩ : syracuseStep 1628687 = 2443031) B2443031
theorem B3258913 : Blo 1285961 3258913 := bstep (se 2 (by rfl) ⟨1222092, by rfl⟩ : syracuseStep 3258913 = 2444185) B2444185
theorem B1931819 : Blo 1285961 1931819 := bstep (se 1 (by rfl) ⟨1448864, by rfl⟩ : syracuseStep 1931819 = 2897729) B2897729
theorem B1931849 : Blo 1285961 1931849 := bstep (se 2 (by rfl) ⟨724443, by rfl⟩ : syracuseStep 1931849 = 1448887) B1448887
theorem B4020851 : Blo 1285961 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B1448635 : Blo 1285961 1448635 := bstep (se 1 (by rfl) ⟨1086476, by rfl⟩ : syracuseStep 1448635 = 2172953) B2172953
theorem B3914507 : Blo 1285961 3914507 := bstep (se 1 (by rfl) ⟨2935880, by rfl⟩ : syracuseStep 3914507 = 5871761) B5871761
theorem B13908773 : Blo 1285961 13908773 := bstep (se 4 (by rfl) ⟨1303947, by rfl⟩ : syracuseStep 13908773 = 2607895) B2607895
theorem B4340627 : Blo 1285961 4340627 := bstep (se 1 (by rfl) ⟨3255470, by rfl⟩ : syracuseStep 4340627 = 6510941) B6510941
theorem B2202553 : Blo 1285961 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B6519851 : Blo 1285961 6519851 := bstep (se 1 (by rfl) ⟨4889888, by rfl⟩ : syracuseStep 6519851 = 9779777) B9779777
theorem B3259511 : Blo 1285961 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B10992955 : Blo 1285961 10992955 := bstep (se 1 (by rfl) ⟨8244716, by rfl⟩ : syracuseStep 10992955 = 16489433) B16489433
theorem B10575251 : Blo 1285961 10575251 := bstep (se 1 (by rfl) ⟨7931438, by rfl⟩ : syracuseStep 10575251 = 15862877) B15862877
theorem B4890041 : Blo 1285961 4890041 := bstep (se 2 (by rfl) ⟨1833765, by rfl⟩ : syracuseStep 4890041 = 3667531) B3667531
theorem B6512075 : Blo 1285961 6512075 := bstep (se 1 (by rfl) ⟨4884056, by rfl⟩ : syracuseStep 6512075 = 9768113) B9768113
theorem B23469517 : Blo 1285961 23469517 := bstep (se 3 (by rfl) ⟨4400534, by rfl⟩ : syracuseStep 23469517 = 8801069) B8801069
theorem B10993229 : Blo 1285961 10993229 := bstep (se 3 (by rfl) ⟨2061230, by rfl⟩ : syracuseStep 10993229 = 4122461) B4122461
theorem B6512399 : Blo 1285961 6512399 := bstep (se 1 (by rfl) ⟨4884299, by rfl⟩ : syracuseStep 6512399 = 9768599) B9768599
theorem B10428209 : Blo 1285961 10428209 := bstep (se 2 (by rfl) ⟨3910578, by rfl⟩ : syracuseStep 10428209 = 7821157) B7821157
theorem B4636531 : Blo 1285961 4636531 := bstep (se 1 (by rfl) ⟨3477398, by rfl⟩ : syracuseStep 4636531 = 6954797) B6954797
theorem B1286023 : Blo 1285961 1286023 := bstep (se 1 (by rfl) ⟨964517, by rfl⟩ : syracuseStep 1286023 = 1929035) B1929035
theorem B2170759 : Blo 1285961 2170759 := bstep (se 1 (by rfl) ⟨1628069, by rfl⟩ : syracuseStep 2170759 = 3256139) B3256139
theorem B1286031 : Blo 1285961 1286031 := bstep (se 1 (by rfl) ⟨964523, by rfl⟩ : syracuseStep 1286031 = 1929047) B1929047
theorem B7937945 : Blo 1285961 7937945 := bstep (se 2 (by rfl) ⟨2976729, by rfl⟩ : syracuseStep 7937945 = 5953459) B5953459
theorem B1286075 : Blo 1285961 1286075 := bstep (se 1 (by rfl) ⟨964556, by rfl⟩ : syracuseStep 1286075 = 1929113) B1929113
theorem B12058571 : Blo 1285961 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B4341761 : Blo 1285961 4341761 := bstep (se 2 (by rfl) ⟨1628160, by rfl⟩ : syracuseStep 4341761 = 3256321) B3256321
theorem B1286183 : Blo 1285961 1286183 := bstep (se 1 (by rfl) ⟨964637, by rfl⟩ : syracuseStep 1286183 = 1929275) B1929275
theorem B8241209 : Blo 1285961 8241209 := bstep (se 2 (by rfl) ⟨3090453, by rfl⟩ : syracuseStep 8241209 = 6180907) B6180907
theorem B1286223 : Blo 1285961 1286223 := bstep (se 1 (by rfl) ⟨964667, by rfl⟩ : syracuseStep 1286223 = 1929335) B1929335
theorem B1286239 : Blo 1285961 1286239 := bstep (se 1 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 1286239 = 1929359) B1929359
theorem B1286267 : Blo 1285961 1286267 := bstep (se 1 (by rfl) ⟨964700, by rfl⟩ : syracuseStep 1286267 = 1929401) B1929401
theorem B1286319 : Blo 1285961 1286319 := bstep (se 1 (by rfl) ⟨964739, by rfl⟩ : syracuseStep 1286319 = 1929479) B1929479
theorem B1286343 : Blo 1285961 1286343 := bstep (se 1 (by rfl) ⟨964757, by rfl⟩ : syracuseStep 1286343 = 1929515) B1929515
theorem B1286363 : Blo 1285961 1286363 := bstep (se 1 (by rfl) ⟨964772, by rfl⟩ : syracuseStep 1286363 = 1929545) B1929545
theorem B9281765 : Blo 1285961 9281765 := bstep (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) B1740331
theorem B1286439 : Blo 1285961 1286439 := bstep (se 1 (by rfl) ⟨964829, by rfl⟩ : syracuseStep 1286439 = 1929659) B1929659
theorem B1286479 : Blo 1285961 1286479 := bstep (se 1 (by rfl) ⟨964859, by rfl⟩ : syracuseStep 1286479 = 1929719) B1929719
theorem B1286495 : Blo 1285961 1286495 := bstep (se 1 (by rfl) ⟨964871, by rfl⟩ : syracuseStep 1286495 = 1929743) B1929743
theorem B1286523 : Blo 1285961 1286523 := bstep (se 1 (by rfl) ⟨964892, by rfl⟩ : syracuseStep 1286523 = 1929785) B1929785
theorem B2171279 : Blo 1285961 2171279 := bstep (se 1 (by rfl) ⟨1628459, by rfl⟩ : syracuseStep 2171279 = 3256919) B3256919
theorem B1286575 : Blo 1285961 1286575 := bstep (se 1 (by rfl) ⟨964931, by rfl⟩ : syracuseStep 1286575 = 1929863) B1929863
theorem B1286599 : Blo 1285961 1286599 := bstep (se 1 (by rfl) ⟨964949, by rfl⟩ : syracuseStep 1286599 = 1929899) B1929899
theorem B1286619 : Blo 1285961 1286619 := bstep (se 1 (by rfl) ⟨964964, by rfl⟩ : syracuseStep 1286619 = 1929929) B1929929
theorem B1286695 : Blo 1285961 1286695 := bstep (se 1 (by rfl) ⟨965021, by rfl⟩ : syracuseStep 1286695 = 1930043) B1930043
theorem B1286735 : Blo 1285961 1286735 := bstep (se 1 (by rfl) ⟨965051, by rfl⟩ : syracuseStep 1286735 = 1930103) B1930103
theorem B1286751 : Blo 1285961 1286751 := bstep (se 1 (by rfl) ⟨965063, by rfl⟩ : syracuseStep 1286751 = 1930127) B1930127
theorem B2933371 : Blo 1285961 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B1286779 : Blo 1285961 1286779 := bstep (se 1 (by rfl) ⟨965084, by rfl⟩ : syracuseStep 1286779 = 1930169) B1930169
theorem B2171515 : Blo 1285961 2171515 := bstep (se 1 (by rfl) ⟨1628636, by rfl⟩ : syracuseStep 2171515 = 3257273) B3257273
theorem B1286831 : Blo 1285961 1286831 := bstep (se 1 (by rfl) ⟨965123, by rfl⟩ : syracuseStep 1286831 = 1930247) B1930247
theorem B1286855 : Blo 1285961 1286855 := bstep (se 1 (by rfl) ⟨965141, by rfl⟩ : syracuseStep 1286855 = 1930283) B1930283
theorem B1286875 : Blo 1285961 1286875 := bstep (se 1 (by rfl) ⟨965156, by rfl⟩ : syracuseStep 1286875 = 1930313) B1930313
theorem B21988097 : Blo 1285961 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B7324445 : Blo 1285961 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B1286951 : Blo 1285961 1286951 := bstep (se 1 (by rfl) ⟨965213, by rfl⟩ : syracuseStep 1286951 = 1930427) B1930427
theorem B4342571 : Blo 1285961 4342571 := bstep (se 1 (by rfl) ⟨3256928, by rfl⟩ : syracuseStep 4342571 = 6513857) B6513857
theorem B4883267 : Blo 1285961 4883267 := bstep (se 1 (by rfl) ⟨3662450, by rfl⟩ : syracuseStep 4883267 = 7324901) B7324901
theorem B1286991 : Blo 1285961 1286991 := bstep (se 1 (by rfl) ⟨965243, by rfl⟩ : syracuseStep 1286991 = 1930487) B1930487
theorem B2933599 : Blo 1285961 2933599 := bstep (se 1 (by rfl) ⟨2200199, by rfl⟩ : syracuseStep 2933599 = 4400399) B4400399
theorem B1287007 : Blo 1285961 1287007 := bstep (se 1 (by rfl) ⟨965255, by rfl⟩ : syracuseStep 1287007 = 1930511) B1930511
theorem B2442089 : Blo 1285961 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B1287035 : Blo 1285961 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B1287087 : Blo 1285961 1287087 := bstep (se 1 (by rfl) ⟨965315, by rfl⟩ : syracuseStep 1287087 = 1930631) B1930631
theorem B1287111 : Blo 1285961 1287111 := bstep (se 1 (by rfl) ⟨965333, by rfl⟩ : syracuseStep 1287111 = 1930667) B1930667
theorem B1287131 : Blo 1285961 1287131 := bstep (se 1 (by rfl) ⟨965348, by rfl⟩ : syracuseStep 1287131 = 1930697) B1930697
theorem B1287207 : Blo 1285961 1287207 := bstep (se 1 (by rfl) ⟨965405, by rfl⟩ : syracuseStep 1287207 = 1930811) B1930811
theorem B4342841 : Blo 1285961 4342841 := bstep (se 2 (by rfl) ⟨1628565, by rfl⟩ : syracuseStep 4342841 = 3257131) B3257131
theorem B1287247 : Blo 1285961 1287247 := bstep (se 1 (by rfl) ⟨965435, by rfl⟩ : syracuseStep 1287247 = 1930871) B1930871
theorem B1287263 : Blo 1285961 1287263 := bstep (se 1 (by rfl) ⟨965447, by rfl⟩ : syracuseStep 1287263 = 1930895) B1930895
theorem B1287291 : Blo 1285961 1287291 := bstep (se 1 (by rfl) ⟨965468, by rfl⟩ : syracuseStep 1287291 = 1930937) B1930937
theorem B1287343 : Blo 1285961 1287343 := bstep (se 1 (by rfl) ⟨965507, by rfl⟩ : syracuseStep 1287343 = 1931015) B1931015
theorem B1287367 : Blo 1285961 1287367 := bstep (se 1 (by rfl) ⟨965525, by rfl⟩ : syracuseStep 1287367 = 1931051) B1931051
theorem B1287387 : Blo 1285961 1287387 := bstep (se 1 (by rfl) ⟨965540, by rfl⟩ : syracuseStep 1287387 = 1931081) B1931081
theorem B37119221 : Blo 1285961 37119221 := bstep (se 5 (by rfl) ⟨1739963, by rfl⟩ : syracuseStep 37119221 = 3479927) B3479927
theorem B4883723 : Blo 1285961 4883723 := bstep (se 1 (by rfl) ⟨3662792, by rfl⟩ : syracuseStep 4883723 = 7325585) B7325585
theorem B1287463 : Blo 1285961 1287463 := bstep (se 1 (by rfl) ⟨965597, by rfl⟩ : syracuseStep 1287463 = 1931195) B1931195
theorem B1287503 : Blo 1285961 1287503 := bstep (se 1 (by rfl) ⟨965627, by rfl⟩ : syracuseStep 1287503 = 1931255) B1931255
theorem B1287519 : Blo 1285961 1287519 := bstep (se 1 (by rfl) ⟨965639, by rfl⟩ : syracuseStep 1287519 = 1931279) B1931279
theorem B1287547 : Blo 1285961 1287547 := bstep (se 1 (by rfl) ⟨965660, by rfl⟩ : syracuseStep 1287547 = 1931321) B1931321
theorem B4343165 : Blo 1285961 4343165 := bstep (se 3 (by rfl) ⟨814343, by rfl⟩ : syracuseStep 4343165 = 1628687) B1628687
theorem B5498255 : Blo 1285961 5498255 := bstep (se 1 (by rfl) ⟨4123691, by rfl⟩ : syracuseStep 5498255 = 8247383) B8247383
theorem B8250767 : Blo 1285961 8250767 := bstep (se 1 (by rfl) ⟨6188075, by rfl⟩ : syracuseStep 8250767 = 12376151) B12376151
theorem B1287599 : Blo 1285961 1287599 := bstep (se 1 (by rfl) ⟨965699, by rfl⟩ : syracuseStep 1287599 = 1931399) B1931399
theorem B1287623 : Blo 1285961 1287623 := bstep (se 1 (by rfl) ⟨965717, by rfl⟩ : syracuseStep 1287623 = 1931435) B1931435
theorem B2172379 : Blo 1285961 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B2090459 : Blo 1285961 2090459 := bstep (se 1 (by rfl) ⟨1567844, by rfl⟩ : syracuseStep 2090459 = 3135689) B3135689
theorem B1287643 : Blo 1285961 1287643 := bstep (se 1 (by rfl) ⟨965732, by rfl⟩ : syracuseStep 1287643 = 1931465) B1931465
theorem B4638217 : Blo 1285961 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B1287719 : Blo 1285961 1287719 := bstep (se 1 (by rfl) ⟨965789, by rfl⟩ : syracuseStep 1287719 = 1931579) B1931579
theorem B1287759 : Blo 1285961 1287759 := bstep (se 1 (by rfl) ⟨965819, by rfl⟩ : syracuseStep 1287759 = 1931639) B1931639
theorem B1287775 : Blo 1285961 1287775 := bstep (se 1 (by rfl) ⟨965831, by rfl⟩ : syracuseStep 1287775 = 1931663) B1931663
theorem B1287803 : Blo 1285961 1287803 := bstep (se 1 (by rfl) ⟨965852, by rfl⟩ : syracuseStep 1287803 = 1931705) B1931705
theorem B4343435 : Blo 1285961 4343435 := bstep (se 1 (by rfl) ⟨3257576, by rfl⟩ : syracuseStep 4343435 = 6515153) B6515153
theorem B4638347 : Blo 1285961 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B1287855 : Blo 1285961 1287855 := bstep (se 1 (by rfl) ⟨965891, by rfl⟩ : syracuseStep 1287855 = 1931783) B1931783
theorem B1287879 : Blo 1285961 1287879 := bstep (se 1 (by rfl) ⟨965909, by rfl⟩ : syracuseStep 1287879 = 1931819) B1931819
theorem B1287899 : Blo 1285961 1287899 := bstep (se 1 (by rfl) ⟨965924, by rfl⟩ : syracuseStep 1287899 = 1931849) B1931849
theorem B14288633 : Blo 1285961 14288633 := bstep (se 2 (by rfl) ⟨5358237, by rfl⟩ : syracuseStep 14288633 = 10716475) B10716475
theorem B14657273 : Blo 1285961 14657273 := bstep (se 2 (by rfl) ⟨5496477, by rfl⟩ : syracuseStep 14657273 = 10992955) B10992955
theorem B22005593 : Blo 1285961 22005593 := bstep (se 2 (by rfl) ⟨8252097, by rfl⟩ : syracuseStep 22005593 = 16504195) B16504195
theorem B2443115 : Blo 1285961 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B2893751 : Blo 1285961 2893751 := bstep (se 1 (by rfl) ⟨2170313, by rfl⟩ : syracuseStep 2893751 = 4340627) B4340627
theorem B4884407 : Blo 1285961 4884407 := bstep (se 1 (by rfl) ⟨3663305, by rfl⟩ : syracuseStep 4884407 = 7326611) B7326611
theorem B2173007 : Blo 1285961 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B9767141 : Blo 1285961 9767141 := bstep (se 4 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 9767141 = 1831339) B1831339
theorem B63473969 : Blo 1285961 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B4639037 : Blo 1285961 4639037 := bstep (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) B1739639
theorem B5499197 : Blo 1285961 5499197 := bstep (se 3 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 5499197 = 2062199) B2062199
theorem B8243693 : Blo 1285961 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B2443783 : Blo 1285961 2443783 := bstep (se 1 (by rfl) ⟨1832837, by rfl⟩ : syracuseStep 2443783 = 3665675) B3665675
theorem B2894345 : Blo 1285961 2894345 := bstep (se 2 (by rfl) ⟨1085379, by rfl⟩ : syracuseStep 2894345 = 2170759) B2170759
theorem B32156189 : Blo 1285961 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B4344353 : Blo 1285961 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B4885181 : Blo 1285961 4885181 := bstep (se 3 (by rfl) ⟨915971, by rfl⟩ : syracuseStep 4885181 = 1831943) B1831943
theorem B9276115 : Blo 1285961 9276115 := bstep (se 1 (by rfl) ⟨6957086, by rfl⟩ : syracuseStep 9276115 = 13914173) B13914173
theorem B4344569 : Blo 1285961 4344569 := bstep (se 2 (by rfl) ⟨1629213, by rfl⟩ : syracuseStep 4344569 = 3258427) B3258427
theorem B2894687 : Blo 1285961 2894687 := bstep (se 1 (by rfl) ⟨2171015, by rfl⟩ : syracuseStep 2894687 = 4342031) B4342031
theorem B4123487 : Blo 1285961 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B36162449 : Blo 1285961 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B6515639 : Blo 1285961 6515639 := bstep (se 1 (by rfl) ⟨4886729, by rfl⟩ : syracuseStep 6515639 = 9773459) B9773459
theorem B4344839 : Blo 1285961 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B2894867 : Blo 1285961 2894867 := bstep (se 1 (by rfl) ⟨2171150, by rfl⟩ : syracuseStep 2894867 = 4342301) B4342301
theorem B5950543 : Blo 1285961 5950543 := bstep (se 1 (by rfl) ⟨4462907, by rfl⟩ : syracuseStep 5950543 = 8925815) B8925815
theorem B4344947 : Blo 1285961 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B7335107 : Blo 1285961 7335107 := bstep (se 1 (by rfl) ⟨5501330, by rfl⟩ : syracuseStep 7335107 = 11002661) B11002661
theorem B9776375 : Blo 1285961 9776375 := bstep (se 1 (by rfl) ⟨7332281, by rfl⟩ : syracuseStep 9776375 = 14664563) B14664563
theorem B2747753 : Blo 1285961 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B2895209 : Blo 1285961 2895209 := bstep (se 2 (by rfl) ⟨1085703, by rfl⟩ : syracuseStep 2895209 = 2171407) B2171407
theorem B4885865 : Blo 1285961 4885865 := bstep (se 2 (by rfl) ⟨1832199, by rfl⟩ : syracuseStep 4885865 = 3664399) B3664399
theorem B4345217 : Blo 1285961 4345217 := bstep (se 2 (by rfl) ⟨1629456, by rfl⟩ : syracuseStep 4345217 = 3258913) B3258913
theorem B2477495 : Blo 1285961 2477495 := bstep (se 1 (by rfl) ⟨1858121, by rfl⟩ : syracuseStep 2477495 = 3716243) B3716243
theorem B18795997 : Blo 1285961 18795997 := bstep (se 3 (by rfl) ⟨3524249, by rfl⟩ : syracuseStep 18795997 = 7048499) B7048499
theorem B4238983 : Blo 1285961 4238983 := bstep (se 1 (by rfl) ⟨3179237, by rfl⟩ : syracuseStep 4238983 = 6358475) B6358475
theorem B3255947 : Blo 1285961 3255947 := bstep (se 1 (by rfl) ⟨2441960, by rfl⟩ : syracuseStep 3255947 = 4883921) B4883921
theorem B2936519 : Blo 1285961 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B9776861 : Blo 1285961 9776861 := bstep (se 3 (by rfl) ⟨1833161, by rfl⟩ : syracuseStep 9776861 = 3666323) B3666323
theorem B3256159 : Blo 1285961 3256159 := bstep (se 1 (by rfl) ⟨2442119, by rfl⟩ : syracuseStep 3256159 = 4884239) B4884239
theorem B1929065 : Blo 1285961 1929065 := bstep (se 2 (by rfl) ⟨723399, by rfl⟩ : syracuseStep 1929065 = 1446799) B1446799
theorem B8245127 : Blo 1285961 8245127 := bstep (se 1 (by rfl) ⟨6183845, by rfl⟩ : syracuseStep 8245127 = 12367691) B12367691
theorem B2936737 : Blo 1285961 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B1929143 : Blo 1285961 1929143 := bstep (se 1 (by rfl) ⟨1446857, by rfl⟩ : syracuseStep 1929143 = 2893715) B2893715
theorem B2895803 : Blo 1285961 2895803 := bstep (se 1 (by rfl) ⟨2171852, by rfl⟩ : syracuseStep 2895803 = 4343705) B4343705
theorem B1929179 : Blo 1285961 1929179 := bstep (se 1 (by rfl) ⟨1446884, by rfl⟩ : syracuseStep 1929179 = 2893769) B2893769
theorem B4182031 : Blo 1285961 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B2895929 : Blo 1285961 2895929 := bstep (se 2 (by rfl) ⟨1085973, by rfl⟩ : syracuseStep 2895929 = 2171947) B2171947
theorem B4346027 : Blo 1285961 4346027 := bstep (se 1 (by rfl) ⟨3259520, by rfl⟩ : syracuseStep 4346027 = 6519041) B6519041
theorem B5501195 : Blo 1285961 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B6517097 : Blo 1285961 6517097 := bstep (se 2 (by rfl) ⟨2443911, by rfl⟩ : syracuseStep 6517097 = 4887823) B4887823
theorem B2896271 : Blo 1285961 2896271 := bstep (se 1 (by rfl) ⟨2172203, by rfl⟩ : syracuseStep 2896271 = 4344407) B4344407
theorem B1929647 : Blo 1285961 1929647 := bstep (se 1 (by rfl) ⟨1447235, by rfl⟩ : syracuseStep 1929647 = 2894471) B2894471
theorem B1831351 : Blo 1285961 1831351 := bstep (se 1 (by rfl) ⟨1373513, by rfl⟩ : syracuseStep 1831351 = 2747027) B2747027
theorem B2060731 : Blo 1285961 2060731 := bstep (se 1 (by rfl) ⟨1545548, by rfl⟩ : syracuseStep 2060731 = 3091097) B3091097
theorem B2609671 : Blo 1285961 2609671 := bstep (se 1 (by rfl) ⟨1957253, by rfl⟩ : syracuseStep 2609671 = 3914507) B3914507
theorem B1929737 : Blo 1285961 1929737 := bstep (se 2 (by rfl) ⟨723651, by rfl⟩ : syracuseStep 1929737 = 1447303) B1447303
theorem B3478025 : Blo 1285961 3478025 := bstep (se 2 (by rfl) ⟨1304259, by rfl⟩ : syracuseStep 3478025 = 2608519) B2608519
theorem B27832841 : Blo 1285961 27832841 := bstep (se 2 (by rfl) ⟨10437315, by rfl⟩ : syracuseStep 27832841 = 20874631) B20874631
theorem B1929767 : Blo 1285961 1929767 := bstep (se 1 (by rfl) ⟨1447325, by rfl⟩ : syracuseStep 1929767 = 2894651) B2894651
theorem B2749025 : Blo 1285961 2749025 := bstep (se 2 (by rfl) ⟨1030884, by rfl⟩ : syracuseStep 2749025 = 2061769) B2061769
theorem B1929851 : Blo 1285961 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B8811143 : Blo 1285961 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B4346567 : Blo 1285961 4346567 := bstep (se 1 (by rfl) ⟨3259925, by rfl⟩ : syracuseStep 4346567 = 6519851) B6519851
theorem B2896595 : Blo 1285961 2896595 := bstep (se 1 (by rfl) ⟨2172446, by rfl⟩ : syracuseStep 2896595 = 4344893) B4344893
theorem B1929977 : Blo 1285961 1929977 := bstep (se 2 (by rfl) ⟨723741, by rfl⟩ : syracuseStep 1929977 = 1447483) B1447483
theorem B3257081 : Blo 1285961 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B1930079 : Blo 1285961 1930079 := bstep (se 1 (by rfl) ⟨1447559, by rfl⟩ : syracuseStep 1930079 = 2895119) B2895119
theorem B1930091 : Blo 1285961 1930091 := bstep (se 1 (by rfl) ⟨1447568, by rfl⟩ : syracuseStep 1930091 = 2895137) B2895137
theorem B7050167 : Blo 1285961 7050167 := bstep (se 1 (by rfl) ⟨5287625, by rfl⟩ : syracuseStep 7050167 = 10575251) B10575251
theorem B10433555 : Blo 1285961 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B7328819 : Blo 1285961 7328819 := bstep (se 1 (by rfl) ⟨5496614, by rfl⟩ : syracuseStep 7328819 = 10993229) B10993229
theorem B1930319 : Blo 1285961 1930319 := bstep (se 1 (by rfl) ⟨1447739, by rfl⟩ : syracuseStep 1930319 = 2895479) B2895479
theorem B6182041 : Blo 1285961 6182041 := bstep (se 2 (by rfl) ⟨2318265, by rfl⟩ : syracuseStep 6182041 = 4636531) B4636531
theorem B1930439 : Blo 1285961 1930439 := bstep (se 1 (by rfl) ⟨1447829, by rfl⟩ : syracuseStep 1930439 = 2895659) B2895659
theorem B6952139 : Blo 1285961 6952139 := bstep (se 1 (by rfl) ⟨5214104, by rfl⟩ : syracuseStep 6952139 = 10428209) B10428209
theorem B2061641 : Blo 1285961 2061641 := bstep (se 2 (by rfl) ⟨773115, by rfl⟩ : syracuseStep 2061641 = 1546231) B1546231
theorem B1930601 : Blo 1285961 1930601 := bstep (se 2 (by rfl) ⟨723975, by rfl⟩ : syracuseStep 1930601 = 1447951) B1447951
theorem B3257729 : Blo 1285961 3257729 := bstep (se 2 (by rfl) ⟨1221648, by rfl⟩ : syracuseStep 3257729 = 2443297) B2443297
theorem B1930679 : Blo 1285961 1930679 := bstep (se 1 (by rfl) ⟨1448009, by rfl⟩ : syracuseStep 1930679 = 2896019) B2896019
theorem B1930715 : Blo 1285961 1930715 := bstep (se 1 (by rfl) ⟨1448036, by rfl⟩ : syracuseStep 1930715 = 2896073) B2896073
theorem B4888097 : Blo 1285961 4888097 := bstep (se 2 (by rfl) ⟨1833036, by rfl⟩ : syracuseStep 4888097 = 3666073) B3666073
theorem B1627771 : Blo 1285961 1627771 := bstep (se 1 (by rfl) ⟨1220828, by rfl⟩ : syracuseStep 1627771 = 2441657) B2441657
theorem B2897531 : Blo 1285961 2897531 := bstep (se 1 (by rfl) ⟨2173148, by rfl⟩ : syracuseStep 2897531 = 4346297) B4346297
theorem B6182615 : Blo 1285961 6182615 := bstep (se 1 (by rfl) ⟨4636961, by rfl⟩ : syracuseStep 6182615 = 9273923) B9273923
theorem B2897657 : Blo 1285961 2897657 := bstep (se 2 (by rfl) ⟨1086621, by rfl⟩ : syracuseStep 2897657 = 2173243) B2173243
theorem B13907771 : Blo 1285961 13907771 := bstep (se 1 (by rfl) ⟨10430828, by rfl⟩ : syracuseStep 13907771 = 20861657) B20861657
theorem B1832809 : Blo 1285961 1832809 := bstep (se 2 (by rfl) ⟨687303, by rfl⟩ : syracuseStep 1832809 = 1374607) B1374607
theorem B6510455 : Blo 1285961 6510455 := bstep (se 1 (by rfl) ⟨4882841, by rfl⟩ : syracuseStep 6510455 = 9765683) B9765683
theorem B1931183 : Blo 1285961 1931183 := bstep (se 1 (by rfl) ⟨1448387, by rfl⟩ : syracuseStep 1931183 = 2896775) B2896775
theorem B4888583 : Blo 1285961 4888583 := bstep (se 1 (by rfl) ⟨3666437, by rfl⟩ : syracuseStep 4888583 = 7332875) B7332875
theorem B1931273 : Blo 1285961 1931273 := bstep (se 2 (by rfl) ⟨724227, by rfl⟩ : syracuseStep 1931273 = 1448455) B1448455
theorem B1931303 : Blo 1285961 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B1448059 : Blo 1285961 1448059 := bstep (se 1 (by rfl) ⟨1086044, by rfl⟩ : syracuseStep 1448059 = 2172089) B2172089
theorem B1931387 : Blo 1285961 1931387 := bstep (se 1 (by rfl) ⟨1448540, by rfl⟩ : syracuseStep 1931387 = 2897081) B2897081
theorem B3258539 : Blo 1285961 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B1931513 : Blo 1285961 1931513 := bstep (se 2 (by rfl) ⟨724317, by rfl⟩ : syracuseStep 1931513 = 1448635) B1448635
theorem B2201951 : Blo 1285961 2201951 := bstep (se 1 (by rfl) ⟨1651463, by rfl⟩ : syracuseStep 2201951 = 3302927) B3302927
theorem B1931615 : Blo 1285961 1931615 := bstep (se 1 (by rfl) ⟨1448711, by rfl⟩ : syracuseStep 1931615 = 2897423) B2897423
theorem B1931627 : Blo 1285961 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B4889069 : Blo 1285961 4889069 := bstep (se 3 (by rfl) ⟨916700, by rfl⟩ : syracuseStep 4889069 = 1833401) B1833401
theorem B4340249 : Blo 1285961 4340249 := bstep (se 2 (by rfl) ⟨1627593, by rfl⟩ : syracuseStep 4340249 = 3255187) B3255187
theorem B52820515 : Blo 1285961 52820515 := bstep (se 1 (by rfl) ⟨39615386, by rfl⟩ : syracuseStep 52820515 = 79230773) B79230773
theorem B1448527 : Blo 1285961 1448527 := bstep (se 1 (by rfl) ⟨1086395, by rfl⟩ : syracuseStep 1448527 = 2172791) B2172791
theorem B1931855 : Blo 1285961 1931855 := bstep (se 1 (by rfl) ⟨1448891, by rfl⟩ : syracuseStep 1931855 = 2897783) B2897783
theorem B4176523 : Blo 1285961 4176523 := bstep (se 1 (by rfl) ⟨3132392, by rfl⟩ : syracuseStep 4176523 = 6264785) B6264785
theorem B3136363 : Blo 1285961 3136363 := bstep (se 1 (by rfl) ⟨2352272, by rfl⟩ : syracuseStep 3136363 = 4704545) B4704545
theorem B1448923 : Blo 1285961 1448923 := bstep (se 1 (by rfl) ⟨1086692, by rfl⟩ : syracuseStep 1448923 = 2173385) B2173385
theorem B10722269 : Blo 1285961 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B3259399 : Blo 1285961 3259399 := bstep (se 1 (by rfl) ⟨2444549, by rfl⟩ : syracuseStep 3259399 = 4889099) B4889099
theorem B4889753 : Blo 1285961 4889753 := bstep (se 2 (by rfl) ⟨1833657, by rfl⟩ : syracuseStep 4889753 = 3667315) B3667315
theorem B9272515 : Blo 1285961 9272515 := bstep (se 1 (by rfl) ⟨6954386, by rfl⟩ : syracuseStep 9272515 = 13908773) B13908773
theorem B31292689 : Blo 1285961 31292689 := bstep (se 2 (by rfl) ⟨11734758, by rfl⟩ : syracuseStep 31292689 = 23469517) B23469517
theorem B2170219 : Blo 1285961 2170219 := bstep (se 1 (by rfl) ⟨1627664, by rfl⟩ : syracuseStep 2170219 = 3255329) B3255329
theorem B1629659 : Blo 1285961 1629659 := bstep (se 1 (by rfl) ⟨1222244, by rfl⟩ : syracuseStep 1629659 = 2444489) B2444489
theorem B3055091 : Blo 1285961 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B13573619 : Blo 1285961 13573619 := bstep (se 1 (by rfl) ⟨10180214, by rfl⟩ : syracuseStep 13573619 = 20360429) B20360429
theorem B4120103 : Blo 1285961 4120103 := bstep (se 1 (by rfl) ⟨3090077, by rfl⟩ : syracuseStep 4120103 = 6180155) B6180155
theorem B3260027 : Blo 1285961 3260027 := bstep (se 1 (by rfl) ⟨2445020, by rfl⟩ : syracuseStep 3260027 = 4890041) B4890041
theorem B4341383 : Blo 1285961 4341383 := bstep (se 1 (by rfl) ⟨3256037, by rfl⟩ : syracuseStep 4341383 = 6512075) B6512075
theorem B4341437 : Blo 1285961 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B1285967 : Blo 1285961 1285967 := bstep (se 1 (by rfl) ⟨964475, by rfl⟩ : syracuseStep 1285967 = 1928951) B1928951
theorem B1285983 : Blo 1285961 1285983 := bstep (se 1 (by rfl) ⟨964487, by rfl⟩ : syracuseStep 1285983 = 1928975) B1928975
theorem B4341599 : Blo 1285961 4341599 := bstep (se 1 (by rfl) ⟨3256199, by rfl⟩ : syracuseStep 4341599 = 6512399) B6512399
theorem B1957727 : Blo 1285961 1957727 := bstep (se 1 (by rfl) ⟨1468295, by rfl⟩ : syracuseStep 1957727 = 2936591) B2936591
theorem B1286011 : Blo 1285961 1286011 := bstep (se 1 (by rfl) ⟨964508, by rfl⟩ : syracuseStep 1286011 = 1929017) B1929017
theorem B1286063 : Blo 1285961 1286063 := bstep (se 1 (by rfl) ⟨964547, by rfl⟩ : syracuseStep 1286063 = 1929095) B1929095
theorem B5291963 : Blo 1285961 5291963 := bstep (se 1 (by rfl) ⟨3968972, by rfl⟩ : syracuseStep 5291963 = 7937945) B7937945
theorem B1286087 : Blo 1285961 1286087 := bstep (se 1 (by rfl) ⟨964565, by rfl⟩ : syracuseStep 1286087 = 1929131) B1929131
theorem B1286107 : Blo 1285961 1286107 := bstep (se 1 (by rfl) ⟨964580, by rfl⟩ : syracuseStep 1286107 = 1929161) B1929161
theorem B1286431 : Blo 1285961 1286431 := bstep (se 1 (by rfl) ⟨964823, by rfl⟩ : syracuseStep 1286431 = 1929647) B1929647
theorem B1286491 : Blo 1285961 1286491 := bstep (se 1 (by rfl) ⟨964868, by rfl⟩ : syracuseStep 1286491 = 1929737) B1929737
theorem B18555227 : Blo 1285961 18555227 := bstep (se 1 (by rfl) ⟨13916420, by rfl⟩ : syracuseStep 18555227 = 27832841) B27832841
theorem B1286511 : Blo 1285961 1286511 := bstep (se 1 (by rfl) ⟨964883, by rfl⟩ : syracuseStep 1286511 = 1929767) B1929767
theorem B1286567 : Blo 1285961 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B5874095 : Blo 1285961 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B1286651 : Blo 1285961 1286651 := bstep (se 1 (by rfl) ⟨964988, by rfl⟩ : syracuseStep 1286651 = 1929977) B1929977
theorem B2171387 : Blo 1285961 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B4882963 : Blo 1285961 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B1286719 : Blo 1285961 1286719 := bstep (se 1 (by rfl) ⟨965039, by rfl⟩ : syracuseStep 1286719 = 1930079) B1930079
theorem B1286727 : Blo 1285961 1286727 := bstep (se 1 (by rfl) ⟨965045, by rfl⟩ : syracuseStep 1286727 = 1930091) B1930091
theorem B2441801 : Blo 1285961 2441801 := bstep (se 2 (by rfl) ⟨915675, by rfl⟩ : syracuseStep 2441801 = 1831351) B1831351
theorem B6955703 : Blo 1285961 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B70427353 : Blo 1285961 70427353 := bstep (se 2 (by rfl) ⟨26410257, by rfl⟩ : syracuseStep 70427353 = 52820515) B52820515
theorem B1286879 : Blo 1285961 1286879 := bstep (se 1 (by rfl) ⟨965159, by rfl⟩ : syracuseStep 1286879 = 1930319) B1930319
theorem B1286959 : Blo 1285961 1286959 := bstep (se 1 (by rfl) ⟨965219, by rfl⟩ : syracuseStep 1286959 = 1930439) B1930439
theorem B1287067 : Blo 1285961 1287067 := bstep (se 1 (by rfl) ⟨965300, by rfl⟩ : syracuseStep 1287067 = 1930601) B1930601
theorem B2171819 : Blo 1285961 2171819 := bstep (se 1 (by rfl) ⟨1628864, by rfl⟩ : syracuseStep 2171819 = 3257729) B3257729
theorem B1287119 : Blo 1285961 1287119 := bstep (se 1 (by rfl) ⟨965339, by rfl⟩ : syracuseStep 1287119 = 1930679) B1930679
theorem B1287143 : Blo 1285961 1287143 := bstep (se 1 (by rfl) ⟨965357, by rfl⟩ : syracuseStep 1287143 = 1930715) B1930715
theorem B1287455 : Blo 1285961 1287455 := bstep (se 1 (by rfl) ⟨965591, by rfl⟩ : syracuseStep 1287455 = 1931183) B1931183
theorem B1287515 : Blo 1285961 1287515 := bstep (se 1 (by rfl) ⟨965636, by rfl⟩ : syracuseStep 1287515 = 1931273) B1931273
theorem B9274733 : Blo 1285961 9274733 := bstep (se 3 (by rfl) ⟨1739012, by rfl⟩ : syracuseStep 9274733 = 3478025) B3478025
theorem B1287535 : Blo 1285961 1287535 := bstep (se 1 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 1287535 = 1931303) B1931303
theorem B1287591 : Blo 1285961 1287591 := bstep (se 1 (by rfl) ⟨965693, by rfl⟩ : syracuseStep 1287591 = 1931387) B1931387
theorem B10986941 : Blo 1285961 10986941 := bstep (se 3 (by rfl) ⟨2060051, by rfl⟩ : syracuseStep 10986941 = 4120103) B4120103
theorem B2172359 : Blo 1285961 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B1287675 : Blo 1285961 1287675 := bstep (se 1 (by rfl) ⟨965756, by rfl⟩ : syracuseStep 1287675 = 1931513) B1931513
theorem B8242721 : Blo 1285961 8242721 := bstep (se 2 (by rfl) ⟨3091020, by rfl⟩ : syracuseStep 8242721 = 6182041) B6182041
theorem B1467967 : Blo 1285961 1467967 := bstep (se 1 (by rfl) ⟨1100975, by rfl⟩ : syracuseStep 1467967 = 2201951) B2201951
theorem B1287743 : Blo 1285961 1287743 := bstep (se 1 (by rfl) ⟨965807, by rfl⟩ : syracuseStep 1287743 = 1931615) B1931615
theorem B1287751 : Blo 1285961 1287751 := bstep (se 1 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 1287751 = 1931627) B1931627
theorem B12363353 : Blo 1285961 12363353 := bstep (se 2 (by rfl) ⟨4636257, by rfl⟩ : syracuseStep 12363353 = 9272515) B9272515
theorem B2893499 : Blo 1285961 2893499 := bstep (se 1 (by rfl) ⟨2170124, by rfl⟩ : syracuseStep 2893499 = 4340249) B4340249
theorem B41723585 : Blo 1285961 41723585 := bstep (se 2 (by rfl) ⟨15646344, by rfl⟩ : syracuseStep 41723585 = 31292689) B31292689
theorem B1287903 : Blo 1285961 1287903 := bstep (se 1 (by rfl) ⟨965927, by rfl⟩ : syracuseStep 1287903 = 1931855) B1931855
theorem B2893625 : Blo 1285961 2893625 := bstep (se 2 (by rfl) ⟨1085109, by rfl⟩ : syracuseStep 2893625 = 2170219) B2170219
theorem B4343759 : Blo 1285961 4343759 := bstep (se 1 (by rfl) ⟨3257819, by rfl⟩ : syracuseStep 4343759 = 6515639) B6515639
theorem B25061329 : Blo 1285961 25061329 := bstep (se 2 (by rfl) ⟨9397998, by rfl⟩ : syracuseStep 25061329 = 18795997) B18795997
theorem B5220605 : Blo 1285961 5220605 := bstep (se 3 (by rfl) ⟨978863, by rfl⟩ : syracuseStep 5220605 = 1957727) B1957727
theorem B2173351 : Blo 1285961 2173351 := bstep (se 1 (by rfl) ⟨1630013, by rfl⟩ : syracuseStep 2173351 = 3260027) B3260027
theorem B2894255 : Blo 1285961 2894255 := bstep (se 1 (by rfl) ⟨2170691, by rfl⟩ : syracuseStep 2894255 = 4341383) B4341383
theorem B2894291 : Blo 1285961 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B2443745 : Blo 1285961 2443745 := bstep (se 2 (by rfl) ⟨916404, by rfl⟩ : syracuseStep 2443745 = 1832809) B1832809
theorem B2894399 : Blo 1285961 2894399 := bstep (se 1 (by rfl) ⟨2170799, by rfl⟩ : syracuseStep 2894399 = 4341599) B4341599
theorem B2894507 : Blo 1285961 2894507 := bstep (se 1 (by rfl) ⟨2170880, by rfl⟩ : syracuseStep 2894507 = 4341761) B4341761
theorem B6187843 : Blo 1285961 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B4344731 : Blo 1285961 4344731 := bstep (se 1 (by rfl) ⟨3258548, by rfl⟩ : syracuseStep 4344731 = 6517097) B6517097
theorem B14658731 : Blo 1285961 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B2895047 : Blo 1285961 2895047 := bstep (se 1 (by rfl) ⟨2171285, by rfl⟩ : syracuseStep 2895047 = 4342571) B4342571
theorem B3255511 : Blo 1285961 3255511 := bstep (se 1 (by rfl) ⟨2441633, by rfl⟩ : syracuseStep 3255511 = 4883267) B4883267
theorem B49483061 : Blo 1285961 49483061 := bstep (se 5 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 49483061 = 4639037) B4639037
theorem B4885879 : Blo 1285961 4885879 := bstep (se 1 (by rfl) ⟨3664409, by rfl⟩ : syracuseStep 4885879 = 7328819) B7328819
theorem B2895227 : Blo 1285961 2895227 := bstep (se 1 (by rfl) ⟨2171420, by rfl⟩ : syracuseStep 2895227 = 4342841) B4342841
theorem B3911161 : Blo 1285961 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B2895353 : Blo 1285961 2895353 := bstep (se 2 (by rfl) ⟨1085757, by rfl⟩ : syracuseStep 2895353 = 2171515) B2171515
theorem B3255815 : Blo 1285961 3255815 := bstep (se 1 (by rfl) ⟨2441861, by rfl⟩ : syracuseStep 3255815 = 4883723) B4883723
theorem B2895443 : Blo 1285961 2895443 := bstep (se 1 (by rfl) ⟨2171582, by rfl⟩ : syracuseStep 2895443 = 4343165) B4343165
theorem B3665503 : Blo 1285961 3665503 := bstep (se 1 (by rfl) ⟨2749127, by rfl⟩ : syracuseStep 3665503 = 5498255) B5498255
theorem B5500511 : Blo 1285961 5500511 := bstep (se 1 (by rfl) ⟨4125383, by rfl⟩ : syracuseStep 5500511 = 8250767) B8250767
theorem B2895623 : Blo 1285961 2895623 := bstep (se 1 (by rfl) ⟨2171717, by rfl⟩ : syracuseStep 2895623 = 4343435) B4343435
theorem B3092231 : Blo 1285961 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B3911465 : Blo 1285961 3911465 := bstep (se 2 (by rfl) ⟨1466799, by rfl⟩ : syracuseStep 3911465 = 2933599) B2933599
theorem B5574557 : Blo 1285961 5574557 := bstep (se 3 (by rfl) ⟨1045229, by rfl⟩ : syracuseStep 5574557 = 2090459) B2090459
theorem B4345757 : Blo 1285961 4345757 := bstep (se 3 (by rfl) ⟨814829, by rfl⟩ : syracuseStep 4345757 = 1629659) B1629659
theorem B1929167 : Blo 1285961 1929167 := bstep (se 1 (by rfl) ⟨1446875, by rfl⟩ : syracuseStep 1929167 = 2893751) B2893751
theorem B3256271 : Blo 1285961 3256271 := bstep (se 1 (by rfl) ⟨2442203, by rfl⟩ : syracuseStep 3256271 = 4884407) B4884407
theorem B8146909 : Blo 1285961 8146909 := bstep (se 3 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 8146909 = 3055091) B3055091
theorem B4345865 : Blo 1285961 4345865 := bstep (se 2 (by rfl) ⟨1629699, by rfl⟩ : syracuseStep 4345865 = 3259399) B3259399
theorem B7934057 : Blo 1285961 7934057 := bstep (se 2 (by rfl) ⟨2975271, by rfl⟩ : syracuseStep 7934057 = 5950543) B5950543
theorem B42315979 : Blo 1285961 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B3666131 : Blo 1285961 3666131 := bstep (se 1 (by rfl) ⟨2749598, by rfl⟩ : syracuseStep 3666131 = 5499197) B5499197
theorem B1929563 : Blo 1285961 1929563 := bstep (se 1 (by rfl) ⟨1447172, by rfl⟩ : syracuseStep 1929563 = 2894345) B2894345
theorem B2896235 : Blo 1285961 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B3256787 : Blo 1285961 3256787 := bstep (se 1 (by rfl) ⟨2442590, by rfl⟩ : syracuseStep 3256787 = 4885181) B4885181
theorem B2896379 : Blo 1285961 2896379 := bstep (se 1 (by rfl) ⟨2172284, by rfl⟩ : syracuseStep 2896379 = 4344569) B4344569
theorem B16486973 : Blo 1285961 16486973 := bstep (se 3 (by rfl) ⟨3091307, by rfl⟩ : syracuseStep 16486973 = 6182615) B6182615
theorem B1929791 : Blo 1285961 1929791 := bstep (se 1 (by rfl) ⟨1447343, by rfl⟩ : syracuseStep 1929791 = 2894687) B2894687
theorem B2748991 : Blo 1285961 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B2896505 : Blo 1285961 2896505 := bstep (se 2 (by rfl) ⟨1086189, by rfl⟩ : syracuseStep 2896505 = 2172379) B2172379
theorem B7148179 : Blo 1285961 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B2896559 : Blo 1285961 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B1929911 : Blo 1285961 1929911 := bstep (se 1 (by rfl) ⟨1447433, by rfl⟩ : syracuseStep 1929911 = 2894867) B2894867
theorem B2896631 : Blo 1285961 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B6517583 : Blo 1285961 6517583 := bstep (se 1 (by rfl) ⟨4888187, by rfl⟩ : syracuseStep 6517583 = 9776375) B9776375
theorem B1831835 : Blo 1285961 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B1930139 : Blo 1285961 1930139 := bstep (se 1 (by rfl) ⟨1447604, by rfl⟩ : syracuseStep 1930139 = 2895209) B2895209
theorem B3257243 : Blo 1285961 3257243 := bstep (se 1 (by rfl) ⟨2442932, by rfl⟩ : syracuseStep 3257243 = 4885865) B4885865
theorem B2896811 : Blo 1285961 2896811 := bstep (se 1 (by rfl) ⟨2172608, by rfl⟩ : syracuseStep 2896811 = 4345217) B4345217
theorem B1651663 : Blo 1285961 1651663 := bstep (se 1 (by rfl) ⟨1238747, by rfl⟩ : syracuseStep 1651663 = 2477495) B2477495
theorem B10990565 : Blo 1285961 10990565 := bstep (se 4 (by rfl) ⟨1030365, by rfl⟩ : syracuseStep 10990565 = 2060731) B2060731
theorem B9049079 : Blo 1285961 9049079 := bstep (se 1 (by rfl) ⟨6786809, by rfl⟩ : syracuseStep 9049079 = 13573619) B13573619
theorem B6517907 : Blo 1285961 6517907 := bstep (se 1 (by rfl) ⟨4888430, by rfl⟩ : syracuseStep 6517907 = 9776861) B9776861
theorem B1930535 : Blo 1285961 1930535 := bstep (se 1 (by rfl) ⟨1447901, by rfl⟩ : syracuseStep 1930535 = 2895803) B2895803
theorem B3527975 : Blo 1285961 3527975 := bstep (se 1 (by rfl) ⟨2645981, by rfl⟩ : syracuseStep 3527975 = 5291963) B5291963
theorem B5494139 : Blo 1285961 5494139 := bstep (se 1 (by rfl) ⟨4120604, by rfl⟩ : syracuseStep 5494139 = 8241209) B8241209
theorem B1930619 : Blo 1285961 1930619 := bstep (se 1 (by rfl) ⟨1447964, by rfl⟩ : syracuseStep 1930619 = 2895929) B2895929
theorem B22304165 : Blo 1285961 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B2897351 : Blo 1285961 2897351 := bstep (se 1 (by rfl) ⟨2173013, by rfl⟩ : syracuseStep 2897351 = 4346027) B4346027
theorem B1930745 : Blo 1285961 1930745 := bstep (se 2 (by rfl) ⟨724029, by rfl⟩ : syracuseStep 1930745 = 1448059) B1448059
theorem B3667463 : Blo 1285961 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B1447519 : Blo 1285961 1447519 := bstep (se 1 (by rfl) ⟨1085639, by rfl⟩ : syracuseStep 1447519 = 2171279) B2171279
theorem B1930847 : Blo 1285961 1930847 := bstep (se 1 (by rfl) ⟨1448135, by rfl⟩ : syracuseStep 1930847 = 2896271) B2896271
theorem B2897711 : Blo 1285961 2897711 := bstep (se 1 (by rfl) ⟨2173283, by rfl⟩ : syracuseStep 2897711 = 4346567) B4346567
theorem B1931063 : Blo 1285961 1931063 := bstep (se 1 (by rfl) ⟨1448297, by rfl⟩ : syracuseStep 1931063 = 2896595) B2896595
theorem B4700111 : Blo 1285961 4700111 := bstep (se 1 (by rfl) ⟨3525083, by rfl⟩ : syracuseStep 4700111 = 7050167) B7050167
theorem B3258377 : Blo 1285961 3258377 := bstep (se 2 (by rfl) ⟨1221891, by rfl⟩ : syracuseStep 3258377 = 2443783) B2443783
theorem B3479561 : Blo 1285961 3479561 := bstep (se 2 (by rfl) ⟨1304835, by rfl⟩ : syracuseStep 3479561 = 2609671) B2609671
theorem B22607909 : Blo 1285961 22607909 := bstep (se 4 (by rfl) ⟨2119491, by rfl⟩ : syracuseStep 22607909 = 4238983) B4238983
theorem B1931369 : Blo 1285961 1931369 := bstep (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) B1448527
theorem B4634759 : Blo 1285961 4634759 := bstep (se 1 (by rfl) ⟨3476069, by rfl⟩ : syracuseStep 4634759 = 6952139) B6952139
theorem B24746147 : Blo 1285961 24746147 := bstep (se 1 (by rfl) ⟨18559610, by rfl⟩ : syracuseStep 24746147 = 37119221) B37119221
theorem B5568697 : Blo 1285961 5568697 := bstep (se 2 (by rfl) ⟨2088261, by rfl⟩ : syracuseStep 5568697 = 4176523) B4176523
theorem B1374427 : Blo 1285961 1374427 := bstep (se 1 (by rfl) ⟨1030820, by rfl⟩ : syracuseStep 1374427 = 2061641) B2061641
theorem B12368153 : Blo 1285961 12368153 := bstep (se 2 (by rfl) ⟨4638057, by rfl⟩ : syracuseStep 12368153 = 9276115) B9276115
theorem B3258731 : Blo 1285961 3258731 := bstep (se 1 (by rfl) ⟨2444048, by rfl⟩ : syracuseStep 3258731 = 4888097) B4888097
theorem B1931687 : Blo 1285961 1931687 := bstep (se 1 (by rfl) ⟨1448765, by rfl⟩ : syracuseStep 1931687 = 2897531) B2897531
theorem B9525755 : Blo 1285961 9525755 := bstep (se 1 (by rfl) ⟨7144316, by rfl⟩ : syracuseStep 9525755 = 14288633) B14288633
theorem B9771515 : Blo 1285961 9771515 := bstep (se 1 (by rfl) ⟨7328636, by rfl⟩ : syracuseStep 9771515 = 14657273) B14657273
theorem B1931771 : Blo 1285961 1931771 := bstep (se 1 (by rfl) ⟨1448828, by rfl⟩ : syracuseStep 1931771 = 2897657) B2897657
theorem B9271847 : Blo 1285961 9271847 := bstep (se 1 (by rfl) ⟨6953885, by rfl⟩ : syracuseStep 9271847 = 13907771) B13907771
theorem B14670395 : Blo 1285961 14670395 := bstep (se 1 (by rfl) ⟨11002796, by rfl⟩ : syracuseStep 14670395 = 22005593) B22005593
theorem B1628743 : Blo 1285961 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B4340303 : Blo 1285961 4340303 := bstep (se 1 (by rfl) ⟨3255227, by rfl⟩ : syracuseStep 4340303 = 6510455) B6510455
theorem B1931897 : Blo 1285961 1931897 := bstep (se 2 (by rfl) ⟨724461, by rfl⟩ : syracuseStep 1931897 = 1448923) B1448923
theorem B3259055 : Blo 1285961 3259055 := bstep (se 1 (by rfl) ⟨2444291, by rfl⟩ : syracuseStep 3259055 = 4888583) B4888583
theorem B1448671 : Blo 1285961 1448671 := bstep (se 1 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 1448671 = 2173007) B2173007
theorem B6511427 : Blo 1285961 6511427 := bstep (se 1 (by rfl) ⟨4883570, by rfl⟩ : syracuseStep 6511427 = 9767141) B9767141
theorem B7330733 : Blo 1285961 7330733 := bstep (se 3 (by rfl) ⟨1374512, by rfl⟩ : syracuseStep 7330733 = 2749025) B2749025
theorem B5495795 : Blo 1285961 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B3259379 : Blo 1285961 3259379 := bstep (se 1 (by rfl) ⟨2444534, by rfl⟩ : syracuseStep 3259379 = 4889069) B4889069
theorem B21437459 : Blo 1285961 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B16727269 : Blo 1285961 16727269 := bstep (se 4 (by rfl) ⟨1568181, by rfl⟩ : syracuseStep 16727269 = 3136363) B3136363
theorem B24108299 : Blo 1285961 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B6184289 : Blo 1285961 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B3259835 : Blo 1285961 3259835 := bstep (se 1 (by rfl) ⟨2444876, by rfl⟩ : syracuseStep 3259835 = 4889753) B4889753
theorem B4890071 : Blo 1285961 4890071 := bstep (se 1 (by rfl) ⟨3667553, by rfl⟩ : syracuseStep 4890071 = 7335107) B7335107
theorem B2170361 : Blo 1285961 2170361 := bstep (se 2 (by rfl) ⟨813885, by rfl⟩ : syracuseStep 2170361 = 1627771) B1627771
theorem B6512237 : Blo 1285961 6512237 := bstep (se 3 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 6512237 = 2442089) B2442089
theorem B2170631 : Blo 1285961 2170631 := bstep (se 1 (by rfl) ⟨1627973, by rfl⟩ : syracuseStep 2170631 = 3255947) B3255947
theorem B4341545 : Blo 1285961 4341545 := bstep (se 2 (by rfl) ⟨1628079, by rfl⟩ : syracuseStep 4341545 = 3256159) B3256159
theorem B1957679 : Blo 1285961 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B3915649 : Blo 1285961 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B1286043 : Blo 1285961 1286043 := bstep (se 1 (by rfl) ⟨964532, by rfl⟩ : syracuseStep 1286043 = 1929065) B1929065
theorem B5496751 : Blo 1285961 5496751 := bstep (se 1 (by rfl) ⟨4122563, by rfl⟩ : syracuseStep 5496751 = 8245127) B8245127
theorem B1286095 : Blo 1285961 1286095 := bstep (se 1 (by rfl) ⟨964571, by rfl⟩ : syracuseStep 1286095 = 1929143) B1929143
theorem B1286119 : Blo 1285961 1286119 := bstep (se 1 (by rfl) ⟨964589, by rfl⟩ : syracuseStep 1286119 = 1929179) B1929179
theorem B1286375 : Blo 1285961 1286375 := bstep (se 1 (by rfl) ⟨964781, by rfl⟩ : syracuseStep 1286375 = 1929563) B1929563
theorem B12370151 : Blo 1285961 12370151 := bstep (se 1 (by rfl) ⟨9277613, by rfl⟩ : syracuseStep 12370151 = 18555227) B18555227
theorem B3916063 : Blo 1285961 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B2171191 : Blo 1285961 2171191 := bstep (se 1 (by rfl) ⟨1628393, by rfl⟩ : syracuseStep 2171191 = 3256787) B3256787
theorem B1286527 : Blo 1285961 1286527 := bstep (se 1 (by rfl) ⟨964895, by rfl⟩ : syracuseStep 1286527 = 1929791) B1929791
theorem B1286607 : Blo 1285961 1286607 := bstep (se 1 (by rfl) ⟨964955, by rfl⟩ : syracuseStep 1286607 = 1929911) B1929911
theorem B4637135 : Blo 1285961 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B1286759 : Blo 1285961 1286759 := bstep (se 1 (by rfl) ⟨965069, by rfl⟩ : syracuseStep 1286759 = 1930139) B1930139
theorem B2171495 : Blo 1285961 2171495 := bstep (se 1 (by rfl) ⟨1628621, by rfl⟩ : syracuseStep 2171495 = 3257243) B3257243
theorem B2171657 : Blo 1285961 2171657 := bstep (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) B1628743
theorem B1287023 : Blo 1285961 1287023 := bstep (se 1 (by rfl) ⟨965267, by rfl⟩ : syracuseStep 1287023 = 1930535) B1930535
theorem B3662759 : Blo 1285961 3662759 := bstep (se 1 (by rfl) ⟨2747069, by rfl⟩ : syracuseStep 3662759 = 5494139) B5494139
theorem B1287079 : Blo 1285961 1287079 := bstep (se 1 (by rfl) ⟨965309, by rfl⟩ : syracuseStep 1287079 = 1930619) B1930619
theorem B16491437 : Blo 1285961 16491437 := bstep (se 3 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 16491437 = 6184289) B6184289
theorem B7324627 : Blo 1285961 7324627 := bstep (se 1 (by rfl) ⟨5493470, by rfl⟩ : syracuseStep 7324627 = 10986941) B10986941
theorem B1287163 : Blo 1285961 1287163 := bstep (se 1 (by rfl) ⟨965372, by rfl⟩ : syracuseStep 1287163 = 1930745) B1930745
theorem B8242235 : Blo 1285961 8242235 := bstep (se 1 (by rfl) ⟨6181676, by rfl⟩ : syracuseStep 8242235 = 12363353) B12363353
theorem B1287231 : Blo 1285961 1287231 := bstep (se 1 (by rfl) ⟨965423, by rfl⟩ : syracuseStep 1287231 = 1930847) B1930847
theorem B1287375 : Blo 1285961 1287375 := bstep (se 1 (by rfl) ⟨965531, by rfl⟩ : syracuseStep 1287375 = 1931063) B1931063
theorem B2172251 : Blo 1285961 2172251 := bstep (se 1 (by rfl) ⟨1629188, by rfl⟩ : syracuseStep 2172251 = 3258377) B3258377
theorem B2319707 : Blo 1285961 2319707 := bstep (se 1 (by rfl) ⟨1739780, by rfl⟩ : syracuseStep 2319707 = 3479561) B3479561
theorem B1287579 : Blo 1285961 1287579 := bstep (se 1 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 1287579 = 1931369) B1931369
theorem B3089839 : Blo 1285961 3089839 := bstep (se 1 (by rfl) ⟨2317379, by rfl⟩ : syracuseStep 3089839 = 4634759) B4634759
theorem B24724925 : Blo 1285961 24724925 := bstep (se 3 (by rfl) ⟨4635923, by rfl⟩ : syracuseStep 24724925 = 9271847) B9271847
theorem B2172487 : Blo 1285961 2172487 := bstep (se 1 (by rfl) ⟨1629365, by rfl⟩ : syracuseStep 2172487 = 3258731) B3258731
theorem B1287791 : Blo 1285961 1287791 := bstep (se 1 (by rfl) ⟨965843, by rfl⟩ : syracuseStep 1287791 = 1931687) B1931687
theorem B6350503 : Blo 1285961 6350503 := bstep (se 1 (by rfl) ⟨4762877, by rfl⟩ : syracuseStep 6350503 = 9525755) B9525755
theorem B6514343 : Blo 1285961 6514343 := bstep (se 1 (by rfl) ⟨4885757, by rfl⟩ : syracuseStep 6514343 = 9771515) B9771515
theorem B1287847 : Blo 1285961 1287847 := bstep (se 1 (by rfl) ⟨965885, by rfl⟩ : syracuseStep 1287847 = 1931771) B1931771
theorem B2893535 : Blo 1285961 2893535 := bstep (se 1 (by rfl) ⟨2170151, by rfl⟩ : syracuseStep 2893535 = 4340303) B4340303
theorem B1287931 : Blo 1285961 1287931 := bstep (se 1 (by rfl) ⟨965948, by rfl⟩ : syracuseStep 1287931 = 1931897) B1931897
theorem B2172703 : Blo 1285961 2172703 := bstep (se 1 (by rfl) ⟨1629527, by rfl⟩ : syracuseStep 2172703 = 3259055) B3259055
theorem B6514505 : Blo 1285961 6514505 := bstep (se 2 (by rfl) ⟨2442939, by rfl⟩ : syracuseStep 6514505 = 4885879) B4885879
theorem B3663863 : Blo 1285961 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B2172919 : Blo 1285961 2172919 := bstep (se 1 (by rfl) ⟨1629689, by rfl⟩ : syracuseStep 2172919 = 3259379) B3259379
theorem B2173223 : Blo 1285961 2173223 := bstep (se 1 (by rfl) ⟨1629917, by rfl⟩ : syracuseStep 2173223 = 3259835) B3259835
theorem B4884893 : Blo 1285961 4884893 := bstep (se 3 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 4884893 = 1831835) B1831835
theorem B8808869 : Blo 1285961 8808869 := bstep (se 4 (by rfl) ⟨825831, by rfl⟩ : syracuseStep 8808869 = 1651663) B1651663
theorem B5220865 : Blo 1285961 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B2607643 : Blo 1285961 2607643 := bstep (se 1 (by rfl) ⟨1955732, by rfl⟩ : syracuseStep 2607643 = 3911465) B3911465
theorem B2894363 : Blo 1285961 2894363 := bstep (se 1 (by rfl) ⟨2170772, by rfl⟩ : syracuseStep 2894363 = 4341545) B4341545
theorem B1305119 : Blo 1285961 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B2444087 : Blo 1285961 2444087 := bstep (se 1 (by rfl) ⟨1833065, by rfl⟩ : syracuseStep 2444087 = 3666131) B3666131
theorem B7424929 : Blo 1285961 7424929 := bstep (se 2 (by rfl) ⟨2784348, by rfl⟩ : syracuseStep 7424929 = 5568697) B5568697
theorem B56421305 : Blo 1285961 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B4345055 : Blo 1285961 4345055 := bstep (se 1 (by rfl) ⟨3258791, by rfl⟩ : syracuseStep 4345055 = 6517583) B6517583
theorem B7327043 : Blo 1285961 7327043 := bstep (se 1 (by rfl) ⟨5495282, by rfl⟩ : syracuseStep 7327043 = 10990565) B10990565
theorem B6032719 : Blo 1285961 6032719 := bstep (se 1 (by rfl) ⟨4524539, by rfl⟩ : syracuseStep 6032719 = 9049079) B9049079
theorem B3665321 : Blo 1285961 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B4345271 : Blo 1285961 4345271 := bstep (se 1 (by rfl) ⟨3258953, by rfl⟩ : syracuseStep 4345271 = 6517907) B6517907
theorem B9407933 : Blo 1285961 9407933 := bstep (se 3 (by rfl) ⟨1763987, by rfl⟩ : syracuseStep 9407933 = 3527975) B3527975
theorem B9530905 : Blo 1285961 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B2444975 : Blo 1285961 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B59477773 : Blo 1285961 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B1928999 : Blo 1285961 1928999 := bstep (se 1 (by rfl) ⟨1446749, by rfl⟩ : syracuseStep 1928999 = 2893499) B2893499
theorem B27815723 : Blo 1285961 27815723 := bstep (se 1 (by rfl) ⟨20861792, by rfl⟩ : syracuseStep 27815723 = 41723585) B41723585
theorem B1929083 : Blo 1285961 1929083 := bstep (se 1 (by rfl) ⟨1446812, by rfl⟩ : syracuseStep 1929083 = 2893625) B2893625
theorem B2895839 : Blo 1285961 2895839 := bstep (se 1 (by rfl) ⟨2171879, by rfl⟩ : syracuseStep 2895839 = 4343759) B4343759
theorem B8245435 : Blo 1285961 8245435 := bstep (se 1 (by rfl) ⟨6184076, by rfl⟩ : syracuseStep 8245435 = 12368153) B12368153
theorem B1929503 : Blo 1285961 1929503 := bstep (se 1 (by rfl) ⟨1447127, by rfl⟩ : syracuseStep 1929503 = 2894255) B2894255
theorem B1929527 : Blo 1285961 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B22303025 : Blo 1285961 22303025 := bstep (se 2 (by rfl) ⟨8363634, by rfl⟩ : syracuseStep 22303025 = 16727269) B16727269
theorem B33001829 : Blo 1285961 33001829 := bstep (se 4 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 33001829 = 6187843) B6187843
theorem B1929599 : Blo 1285961 1929599 := bstep (se 1 (by rfl) ⟨1447199, by rfl⟩ : syracuseStep 1929599 = 2894399) B2894399
theorem B1929671 : Blo 1285961 1929671 := bstep (se 1 (by rfl) ⟨1447253, by rfl⟩ : syracuseStep 1929671 = 2894507) B2894507
theorem B2896487 : Blo 1285961 2896487 := bstep (se 1 (by rfl) ⟨2172365, by rfl⟩ : syracuseStep 2896487 = 4344731) B4344731
theorem B4887155 : Blo 1285961 4887155 := bstep (se 1 (by rfl) ⟨3665366, by rfl⟩ : syracuseStep 4887155 = 7330733) B7330733
theorem B5214881 : Blo 1285961 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B14291639 : Blo 1285961 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B1930025 : Blo 1285961 1930025 := bstep (se 2 (by rfl) ⟨723759, by rfl⟩ : syracuseStep 1930025 = 1447519) B1447519
theorem B4887337 : Blo 1285961 4887337 := bstep (se 2 (by rfl) ⟨1832751, by rfl⟩ : syracuseStep 4887337 = 3665503) B3665503
theorem B1930031 : Blo 1285961 1930031 := bstep (se 1 (by rfl) ⟨1447523, by rfl⟩ : syracuseStep 1930031 = 2895047) B2895047
theorem B1930151 : Blo 1285961 1930151 := bstep (se 1 (by rfl) ⟨1447613, by rfl⟩ : syracuseStep 1930151 = 2895227) B2895227
theorem B1446907 : Blo 1285961 1446907 := bstep (se 1 (by rfl) ⟨1085180, by rfl⟩ : syracuseStep 1446907 = 2170361) B2170361
theorem B1930235 : Blo 1285961 1930235 := bstep (se 1 (by rfl) ⟨1447676, by rfl⟩ : syracuseStep 1930235 = 2895353) B2895353
theorem B1930295 : Blo 1285961 1930295 := bstep (se 1 (by rfl) ⟨1447721, by rfl⟩ : syracuseStep 1930295 = 2895443) B2895443
theorem B3667007 : Blo 1285961 3667007 := bstep (se 1 (by rfl) ⟨2750255, by rfl⟩ : syracuseStep 3667007 = 5500511) B5500511
theorem B1447087 : Blo 1285961 1447087 := bstep (se 1 (by rfl) ⟨1085315, by rfl⟩ : syracuseStep 1447087 = 2170631) B2170631
theorem B1930415 : Blo 1285961 1930415 := bstep (se 1 (by rfl) ⟨1447811, by rfl⟩ : syracuseStep 1930415 = 2895623) B2895623
theorem B2061487 : Blo 1285961 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B7329001 : Blo 1285961 7329001 := bstep (se 2 (by rfl) ⟨2748375, by rfl⟩ : syracuseStep 7329001 = 5496751) B5496751
theorem B3716371 : Blo 1285961 3716371 := bstep (se 1 (by rfl) ⟨2787278, by rfl⟩ : syracuseStep 3716371 = 5574557) B5574557
theorem B2897171 : Blo 1285961 2897171 := bstep (se 1 (by rfl) ⟨2172878, by rfl⟩ : syracuseStep 2897171 = 4345757) B4345757
theorem B2897243 : Blo 1285961 2897243 := bstep (se 1 (by rfl) ⟨2172932, by rfl⟩ : syracuseStep 2897243 = 4345865) B4345865
theorem B5289371 : Blo 1285961 5289371 := bstep (se 1 (by rfl) ⟨3967028, by rfl⟩ : syracuseStep 5289371 = 7934057) B7934057
theorem B1930823 : Blo 1285961 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B1447591 : Blo 1285961 1447591 := bstep (se 1 (by rfl) ⟨1085693, by rfl⟩ : syracuseStep 1447591 = 2171387) B2171387
theorem B1930919 : Blo 1285961 1930919 := bstep (se 1 (by rfl) ⟨1448189, by rfl⟩ : syracuseStep 1930919 = 2896379) B2896379
theorem B10991315 : Blo 1285961 10991315 := bstep (se 1 (by rfl) ⟨8243486, by rfl⟩ : syracuseStep 10991315 = 16486973) B16486973
theorem B1627867 : Blo 1285961 1627867 := bstep (se 1 (by rfl) ⟨1220900, by rfl⟩ : syracuseStep 1627867 = 2441801) B2441801
theorem B1931003 : Blo 1285961 1931003 := bstep (se 1 (by rfl) ⟨1448252, by rfl⟩ : syracuseStep 1931003 = 2896505) B2896505
theorem B1931039 : Blo 1285961 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B1931087 : Blo 1285961 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B2897801 : Blo 1285961 2897801 := bstep (se 2 (by rfl) ⟨1086675, by rfl⟩ : syracuseStep 2897801 = 2173351) B2173351
theorem B1447879 : Blo 1285961 1447879 := bstep (se 1 (by rfl) ⟨1085909, by rfl⟩ : syracuseStep 1447879 = 2171819) B2171819
theorem B1931207 : Blo 1285961 1931207 := bstep (se 1 (by rfl) ⟨1448405, by rfl⟩ : syracuseStep 1931207 = 2896811) B2896811
theorem B6510617 : Blo 1285961 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B6183155 : Blo 1285961 6183155 := bstep (se 1 (by rfl) ⟨4637366, by rfl⟩ : syracuseStep 6183155 = 9274733) B9274733
theorem B93903137 : Blo 1285961 93903137 := bstep (se 2 (by rfl) ⟨35213676, by rfl⟩ : syracuseStep 93903137 = 70427353) B70427353
theorem B1931561 : Blo 1285961 1931561 := bstep (se 2 (by rfl) ⟨724335, by rfl⟩ : syracuseStep 1931561 = 1448671) B1448671
theorem B1448239 : Blo 1285961 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B1931567 : Blo 1285961 1931567 := bstep (se 1 (by rfl) ⟨1448675, by rfl⟩ : syracuseStep 1931567 = 2897351) B2897351
theorem B5495147 : Blo 1285961 5495147 := bstep (se 1 (by rfl) ⟨4121360, by rfl⟩ : syracuseStep 5495147 = 8242721) B8242721
theorem B7330277 : Blo 1285961 7330277 := bstep (se 4 (by rfl) ⟨687213, by rfl⟩ : syracuseStep 7330277 = 1374427) B1374427
theorem B1931807 : Blo 1285961 1931807 := bstep (se 1 (by rfl) ⟨1448855, by rfl⟩ : syracuseStep 1931807 = 2897711) B2897711
theorem B15071939 : Blo 1285961 15071939 := bstep (se 1 (by rfl) ⟨11303954, by rfl⟩ : syracuseStep 15071939 = 22607909) B22607909
theorem B16497431 : Blo 1285961 16497431 := bstep (se 1 (by rfl) ⟨12373073, by rfl⟩ : syracuseStep 16497431 = 24746147) B24746147
theorem B3480403 : Blo 1285961 3480403 := bstep (se 1 (by rfl) ⟨2610302, by rfl⟩ : syracuseStep 3480403 = 5220605) B5220605
theorem B4340681 : Blo 1285961 4340681 := bstep (se 2 (by rfl) ⟨1627755, by rfl⟩ : syracuseStep 4340681 = 3255511) B3255511
theorem B1629163 : Blo 1285961 1629163 := bstep (se 1 (by rfl) ⟨1221872, by rfl⟩ : syracuseStep 1629163 = 2443745) B2443745
theorem B9780263 : Blo 1285961 9780263 := bstep (se 1 (by rfl) ⟨7335197, by rfl⟩ : syracuseStep 9780263 = 14670395) B14670395
theorem B4340951 : Blo 1285961 4340951 := bstep (se 1 (by rfl) ⟨3255713, by rfl⟩ : syracuseStep 4340951 = 6511427) B6511427
theorem B1957289 : Blo 1285961 1957289 := bstep (se 2 (by rfl) ⟨733983, by rfl⟩ : syracuseStep 1957289 = 1467967) B1467967
theorem B9772487 : Blo 1285961 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B16072199 : Blo 1285961 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B32988707 : Blo 1285961 32988707 := bstep (se 1 (by rfl) ⟨24741530, by rfl⟩ : syracuseStep 32988707 = 49483061) B49483061
theorem B3260047 : Blo 1285961 3260047 := bstep (se 1 (by rfl) ⟨2445035, by rfl⟩ : syracuseStep 3260047 = 4890071) B4890071
theorem B2170543 : Blo 1285961 2170543 := bstep (se 1 (by rfl) ⟨1627907, by rfl⟩ : syracuseStep 2170543 = 3255815) B3255815
theorem B4341491 : Blo 1285961 4341491 := bstep (se 1 (by rfl) ⟨3256118, by rfl⟩ : syracuseStep 4341491 = 6512237) B6512237
theorem B12533629 : Blo 1285961 12533629 := bstep (se 3 (by rfl) ⟨2350055, by rfl⟩ : syracuseStep 12533629 = 4700111) B4700111
theorem B33415105 : Blo 1285961 33415105 := bstep (se 2 (by rfl) ⟨12530664, by rfl⟩ : syracuseStep 33415105 = 25061329) B25061329
theorem B10862545 : Blo 1285961 10862545 := bstep (se 2 (by rfl) ⟨4073454, by rfl⟩ : syracuseStep 10862545 = 8146909) B8146909
theorem B1286111 : Blo 1285961 1286111 := bstep (se 1 (by rfl) ⟨964583, by rfl⟩ : syracuseStep 1286111 = 1929167) B1929167
theorem B2170847 : Blo 1285961 2170847 := bstep (se 1 (by rfl) ⟨1628135, by rfl⟩ : syracuseStep 2170847 = 3256271) B3256271
theorem B1286335 : Blo 1285961 1286335 := bstep (se 1 (by rfl) ⟨964751, by rfl⟩ : syracuseStep 1286335 = 1929503) B1929503
theorem B14868683 : Blo 1285961 14868683 := bstep (se 1 (by rfl) ⟨11151512, by rfl⟩ : syracuseStep 14868683 = 22303025) B22303025
theorem B1286351 : Blo 1285961 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B10993913 : Blo 1285961 10993913 := bstep (se 2 (by rfl) ⟨4122717, by rfl⟩ : syracuseStep 10993913 = 8245435) B8245435
theorem B1286399 : Blo 1285961 1286399 := bstep (se 1 (by rfl) ⟨964799, by rfl⟩ : syracuseStep 1286399 = 1929599) B1929599
theorem B1286447 : Blo 1285961 1286447 := bstep (se 1 (by rfl) ⟨964835, by rfl⟩ : syracuseStep 1286447 = 1929671) B1929671
theorem B9527759 : Blo 1285961 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B1286683 : Blo 1285961 1286683 := bstep (se 1 (by rfl) ⟨965012, by rfl⟩ : syracuseStep 1286683 = 1930025) B1930025
theorem B1286687 : Blo 1285961 1286687 := bstep (se 1 (by rfl) ⟨965015, by rfl⟩ : syracuseStep 1286687 = 1930031) B1930031
theorem B2441839 : Blo 1285961 2441839 := bstep (se 1 (by rfl) ⟨1831379, by rfl⟩ : syracuseStep 2441839 = 3662759) B3662759
theorem B1286767 : Blo 1285961 1286767 := bstep (se 1 (by rfl) ⟨965075, by rfl⟩ : syracuseStep 1286767 = 1930151) B1930151
theorem B10994291 : Blo 1285961 10994291 := bstep (se 1 (by rfl) ⟨8245718, by rfl⟩ : syracuseStep 10994291 = 16491437) B16491437
theorem B1286823 : Blo 1285961 1286823 := bstep (se 1 (by rfl) ⟨965117, by rfl⟩ : syracuseStep 1286823 = 1930235) B1930235
theorem B1286863 : Blo 1285961 1286863 := bstep (se 1 (by rfl) ⟨965147, by rfl⟩ : syracuseStep 1286863 = 1930295) B1930295
theorem B1286943 : Blo 1285961 1286943 := bstep (se 1 (by rfl) ⟨965207, by rfl⟩ : syracuseStep 1286943 = 1930415) B1930415
theorem B16483283 : Blo 1285961 16483283 := bstep (se 1 (by rfl) ⟨12362462, by rfl⟩ : syracuseStep 16483283 = 24724925) B24724925
theorem B1287215 : Blo 1285961 1287215 := bstep (se 1 (by rfl) ⟨965411, by rfl⟩ : syracuseStep 1287215 = 1930823) B1930823
theorem B5219437 : Blo 1285961 5219437 := bstep (se 3 (by rfl) ⟨978644, by rfl⟩ : syracuseStep 5219437 = 1957289) B1957289
theorem B4342895 : Blo 1285961 4342895 := bstep (se 1 (by rfl) ⟨3257171, by rfl⟩ : syracuseStep 4342895 = 6514343) B6514343
theorem B1287279 : Blo 1285961 1287279 := bstep (se 1 (by rfl) ⟨965459, by rfl⟩ : syracuseStep 1287279 = 1930919) B1930919
theorem B1287335 : Blo 1285961 1287335 := bstep (se 1 (by rfl) ⟨965501, by rfl⟩ : syracuseStep 1287335 = 1931003) B1931003
theorem B1287359 : Blo 1285961 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B4343003 : Blo 1285961 4343003 := bstep (se 1 (by rfl) ⟨3257252, by rfl⟩ : syracuseStep 4343003 = 6514505) B6514505
theorem B1287391 : Blo 1285961 1287391 := bstep (se 1 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 1287391 = 1931087) B1931087
theorem B9766169 : Blo 1285961 9766169 := bstep (se 2 (by rfl) ⟨3662313, by rfl⟩ : syracuseStep 9766169 = 7324627) B7324627
theorem B1287471 : Blo 1285961 1287471 := bstep (se 1 (by rfl) ⟨965603, by rfl⟩ : syracuseStep 1287471 = 1931207) B1931207
theorem B2172217 : Blo 1285961 2172217 := bstep (se 2 (by rfl) ⟨814581, by rfl⟩ : syracuseStep 2172217 = 1629163) B1629163
theorem B2442575 : Blo 1285961 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B4122103 : Blo 1285961 4122103 := bstep (se 1 (by rfl) ⟨3091577, by rfl⟩ : syracuseStep 4122103 = 6183155) B6183155
theorem B1287707 : Blo 1285961 1287707 := bstep (se 1 (by rfl) ⟨965780, by rfl⟩ : syracuseStep 1287707 = 1931561) B1931561
theorem B1287711 : Blo 1285961 1287711 := bstep (se 1 (by rfl) ⟨965783, by rfl⟩ : syracuseStep 1287711 = 1931567) B1931567
theorem B3663431 : Blo 1285961 3663431 := bstep (se 1 (by rfl) ⟨2747573, by rfl⟩ : syracuseStep 3663431 = 5495147) B5495147
theorem B1287871 : Blo 1285961 1287871 := bstep (se 1 (by rfl) ⟨965903, by rfl⟩ : syracuseStep 1287871 = 1931807) B1931807
theorem B2893787 : Blo 1285961 2893787 := bstep (se 1 (by rfl) ⟨2170340, by rfl⟩ : syracuseStep 2893787 = 4340681) B4340681
theorem B12707873 : Blo 1285961 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B2893967 : Blo 1285961 2893967 := bstep (se 1 (by rfl) ⟨2170475, by rfl⟩ : syracuseStep 2893967 = 4340951) B4340951
theorem B4884695 : Blo 1285961 4884695 := bstep (se 1 (by rfl) ⟨3663521, by rfl⟩ : syracuseStep 4884695 = 7327043) B7327043
theorem B2894057 : Blo 1285961 2894057 := bstep (se 2 (by rfl) ⟨1085271, by rfl⟩ : syracuseStep 2894057 = 2170543) B2170543
theorem B2443547 : Blo 1285961 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B6514991 : Blo 1285961 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B2894327 : Blo 1285961 2894327 := bstep (se 1 (by rfl) ⟨2170745, by rfl⟩ : syracuseStep 2894327 = 4341491) B4341491
theorem B5221417 : Blo 1285961 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B2894921 : Blo 1285961 2894921 := bstep (se 2 (by rfl) ⟨1085595, by rfl⟩ : syracuseStep 2894921 = 2171191) B2171191
theorem B3476857 : Blo 1285961 3476857 := bstep (se 2 (by rfl) ⟨1303821, by rfl⟩ : syracuseStep 3476857 = 2607643) B2607643
theorem B2444671 : Blo 1285961 2444671 := bstep (se 1 (by rfl) ⟨1833503, by rfl⟩ : syracuseStep 2444671 = 3667007) B3667007
theorem B3526247 : Blo 1285961 3526247 := bstep (se 1 (by rfl) ⟨2644685, by rfl⟩ : syracuseStep 3526247 = 5289371) B5289371
theorem B6516449 : Blo 1285961 6516449 := bstep (se 2 (by rfl) ⟨2443668, by rfl⟩ : syracuseStep 6516449 = 4887337) B4887337
theorem B23490317 : Blo 1285961 23490317 := bstep (se 3 (by rfl) ⟨4404434, by rfl⟩ : syracuseStep 23490317 = 8808869) B8808869
theorem B4640537 : Blo 1285961 4640537 := bstep (se 2 (by rfl) ⟨1740201, by rfl⟩ : syracuseStep 4640537 = 3480403) B3480403
theorem B7327543 : Blo 1285961 7327543 := bstep (se 1 (by rfl) ⟨5495657, by rfl⟩ : syracuseStep 7327543 = 10991315) B10991315
theorem B1929023 : Blo 1285961 1929023 := bstep (se 1 (by rfl) ⟨1446767, by rfl⟩ : syracuseStep 1929023 = 2893535) B2893535
theorem B12365693 : Blo 1285961 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B1929209 : Blo 1285961 1929209 := bstep (se 2 (by rfl) ⟨723453, by rfl⟩ : syracuseStep 1929209 = 1446907) B1446907
theorem B19820645 : Blo 1285961 19820645 := bstep (se 4 (by rfl) ⟨1858185, by rfl⟩ : syracuseStep 19820645 = 3716371) B3716371
theorem B1929449 : Blo 1285961 1929449 := bstep (se 2 (by rfl) ⟨723543, by rfl⟩ : syracuseStep 1929449 = 1447087) B1447087
theorem B2748649 : Blo 1285961 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B3256595 : Blo 1285961 3256595 := bstep (se 1 (by rfl) ⟨2442446, by rfl⟩ : syracuseStep 3256595 = 4884893) B4884893
theorem B4886851 : Blo 1285961 4886851 := bstep (se 1 (by rfl) ⟨3665138, by rfl⟩ : syracuseStep 4886851 = 7330277) B7330277
theorem B1929575 : Blo 1285961 1929575 := bstep (se 1 (by rfl) ⟨1447181, by rfl⟩ : syracuseStep 1929575 = 2894363) B2894363
theorem B13906349 : Blo 1285961 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B10047959 : Blo 1285961 10047959 := bstep (se 1 (by rfl) ⟨7535969, by rfl⟩ : syracuseStep 10047959 = 15071939) B15071939
theorem B10998287 : Blo 1285961 10998287 := bstep (se 1 (by rfl) ⟨8248715, by rfl⟩ : syracuseStep 10998287 = 16497431) B16497431
theorem B37614203 : Blo 1285961 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B2896649 : Blo 1285961 2896649 := bstep (se 2 (by rfl) ⟨1086243, by rfl⟩ : syracuseStep 2896649 = 2172487) B2172487
theorem B2896703 : Blo 1285961 2896703 := bstep (se 1 (by rfl) ⟨2172527, by rfl⟩ : syracuseStep 2896703 = 4345055) B4345055
theorem B4346729 : Blo 1285961 4346729 := bstep (se 2 (by rfl) ⟨1630023, by rfl⟩ : syracuseStep 4346729 = 3260047) B3260047
theorem B8467337 : Blo 1285961 8467337 := bstep (se 2 (by rfl) ⟨3175251, by rfl⟩ : syracuseStep 8467337 = 6350503) B6350503
theorem B1930121 : Blo 1285961 1930121 := bstep (se 2 (by rfl) ⟨723795, by rfl⟩ : syracuseStep 1930121 = 1447591) B1447591
theorem B2896847 : Blo 1285961 2896847 := bstep (se 1 (by rfl) ⟨2172635, by rfl⟩ : syracuseStep 2896847 = 4345271) B4345271
theorem B6271955 : Blo 1285961 6271955 := bstep (se 1 (by rfl) ⟨4703966, by rfl⟩ : syracuseStep 6271955 = 9407933) B9407933
theorem B79303697 : Blo 1285961 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B21992471 : Blo 1285961 21992471 := bstep (se 1 (by rfl) ⟨16494353, by rfl⟩ : syracuseStep 21992471 = 32988707) B32988707
theorem B2896937 : Blo 1285961 2896937 := bstep (se 2 (by rfl) ⟨1086351, by rfl⟩ : syracuseStep 2896937 = 2172703) B2172703
theorem B18543815 : Blo 1285961 18543815 := bstep (se 1 (by rfl) ⟨13907861, by rfl⟩ : syracuseStep 18543815 = 27815723) B27815723
theorem B44553473 : Blo 1285961 44553473 := bstep (se 2 (by rfl) ⟨16707552, by rfl⟩ : syracuseStep 44553473 = 33415105) B33415105
theorem B1930505 : Blo 1285961 1930505 := bstep (se 2 (by rfl) ⟨723939, by rfl⟩ : syracuseStep 1930505 = 1447879) B1447879
theorem B1447231 : Blo 1285961 1447231 := bstep (se 1 (by rfl) ⟨1085423, by rfl⟩ : syracuseStep 1447231 = 2170847) B2170847
theorem B1930559 : Blo 1285961 1930559 := bstep (se 1 (by rfl) ⟨1447919, by rfl⟩ : syracuseStep 1930559 = 2895839) B2895839
theorem B2897225 : Blo 1285961 2897225 := bstep (se 2 (by rfl) ⟨1086459, by rfl⟩ : syracuseStep 2897225 = 2172919) B2172919
theorem B8246767 : Blo 1285961 8246767 := bstep (se 1 (by rfl) ⟨6185075, by rfl⟩ : syracuseStep 8246767 = 12370151) B12370151
theorem B22001219 : Blo 1285961 22001219 := bstep (se 1 (by rfl) ⟨16500914, by rfl⟩ : syracuseStep 22001219 = 33001829) B33001829
theorem B1930985 : Blo 1285961 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B1447663 : Blo 1285961 1447663 := bstep (se 1 (by rfl) ⟨1085747, by rfl⟩ : syracuseStep 1447663 = 2171495) B2171495
theorem B1930991 : Blo 1285961 1930991 := bstep (se 1 (by rfl) ⟨1448243, by rfl⟩ : syracuseStep 1930991 = 2896487) B2896487
theorem B3258103 : Blo 1285961 3258103 := bstep (se 1 (by rfl) ⟨2443577, by rfl⟩ : syracuseStep 3258103 = 4887155) B4887155
theorem B1447771 : Blo 1285961 1447771 := bstep (se 1 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 1447771 = 2171657) B2171657
theorem B6961153 : Blo 1285961 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B5494823 : Blo 1285961 5494823 := bstep (se 1 (by rfl) ⟨4121117, by rfl⟩ : syracuseStep 5494823 = 8242235) B8242235
theorem B1931447 : Blo 1285961 1931447 := bstep (se 1 (by rfl) ⟨1448585, by rfl⟩ : syracuseStep 1931447 = 2897171) B2897171
theorem B1448167 : Blo 1285961 1448167 := bstep (se 1 (by rfl) ⟨1086125, by rfl⟩ : syracuseStep 1448167 = 2172251) B2172251
theorem B1546471 : Blo 1285961 1546471 := bstep (se 1 (by rfl) ⟨1159853, by rfl⟩ : syracuseStep 1546471 = 2319707) B2319707
theorem B1931495 : Blo 1285961 1931495 := bstep (se 1 (by rfl) ⟨1448621, by rfl⟩ : syracuseStep 1931495 = 2897243) B2897243
theorem B1931867 : Blo 1285961 1931867 := bstep (se 1 (by rfl) ⟨1448900, by rfl⟩ : syracuseStep 1931867 = 2897801) B2897801
theorem B4340411 : Blo 1285961 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B3480317 : Blo 1285961 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B62602091 : Blo 1285961 62602091 := bstep (se 1 (by rfl) ⟨46951568, by rfl⟩ : syracuseStep 62602091 = 93903137) B93903137
theorem B1448815 : Blo 1285961 1448815 := bstep (se 1 (by rfl) ⟨1086611, by rfl⟩ : syracuseStep 1448815 = 2173223) B2173223
theorem B9772001 : Blo 1285961 9772001 := bstep (se 2 (by rfl) ⟨3664500, by rfl⟩ : syracuseStep 9772001 = 7329001) B7329001
theorem B8043625 : Blo 1285961 8043625 := bstep (se 2 (by rfl) ⟨3016359, by rfl⟩ : syracuseStep 8043625 = 6032719) B6032719
theorem B1629391 : Blo 1285961 1629391 := bstep (se 1 (by rfl) ⟨1222043, by rfl⟩ : syracuseStep 1629391 = 2444087) B2444087
theorem B4119785 : Blo 1285961 4119785 := bstep (se 2 (by rfl) ⟨1544919, by rfl⟩ : syracuseStep 4119785 = 3089839) B3089839
theorem B6520175 : Blo 1285961 6520175 := bstep (se 1 (by rfl) ⟨4890131, by rfl⟩ : syracuseStep 6520175 = 9780263) B9780263
theorem B39599621 : Blo 1285961 39599621 := bstep (se 4 (by rfl) ⟨3712464, by rfl⟩ : syracuseStep 39599621 = 7424929) B7424929
theorem B2170489 : Blo 1285961 2170489 := bstep (se 2 (by rfl) ⟨813933, by rfl⟩ : syracuseStep 2170489 = 1627867) B1627867
theorem B10714799 : Blo 1285961 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B1629983 : Blo 1285961 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B16711505 : Blo 1285961 16711505 := bstep (se 2 (by rfl) ⟨6266814, by rfl⟩ : syracuseStep 16711505 = 12533629) B12533629
theorem B1285999 : Blo 1285961 1285999 := bstep (se 1 (by rfl) ⟨964499, by rfl⟩ : syracuseStep 1285999 = 1928999) B1928999
theorem B1286055 : Blo 1285961 1286055 := bstep (se 1 (by rfl) ⟨964541, by rfl⟩ : syracuseStep 1286055 = 1929083) B1929083
theorem B14483393 : Blo 1285961 14483393 := bstep (se 2 (by rfl) ⟨5431272, by rfl⟩ : syracuseStep 14483393 = 10862545) B10862545
theorem B9281537 : Blo 1285961 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B13213763 : Blo 1285961 13213763 := bstep (se 1 (by rfl) ⟨9910322, by rfl⟩ : syracuseStep 13213763 = 19820645) B19820645
theorem B9912455 : Blo 1285961 9912455 := bstep (se 1 (by rfl) ⟨7434341, by rfl⟩ : syracuseStep 9912455 = 14868683) B14868683
theorem B1286299 : Blo 1285961 1286299 := bstep (se 1 (by rfl) ⟨964724, by rfl⟩ : syracuseStep 1286299 = 1929449) B1929449
theorem B2171063 : Blo 1285961 2171063 := bstep (se 1 (by rfl) ⟨1628297, by rfl⟩ : syracuseStep 2171063 = 3256595) B3256595
theorem B1286383 : Blo 1285961 1286383 := bstep (se 1 (by rfl) ⟨964787, by rfl⟩ : syracuseStep 1286383 = 1929575) B1929575
theorem B7332191 : Blo 1285961 7332191 := bstep (se 1 (by rfl) ⟨5499143, by rfl⟩ : syracuseStep 7332191 = 10998287) B10998287
theorem B25076135 : Blo 1285961 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B5644891 : Blo 1285961 5644891 := bstep (se 1 (by rfl) ⟨4233668, by rfl⟩ : syracuseStep 5644891 = 8467337) B8467337
theorem B1286747 : Blo 1285961 1286747 := bstep (se 1 (by rfl) ⟨965060, by rfl⟩ : syracuseStep 1286747 = 1930121) B1930121
theorem B12362543 : Blo 1285961 12362543 := bstep (se 1 (by rfl) ⟨9271907, by rfl⟩ : syracuseStep 12362543 = 18543815) B18543815
theorem B1287003 : Blo 1285961 1287003 := bstep (se 1 (by rfl) ⟨965252, by rfl⟩ : syracuseStep 1287003 = 1930505) B1930505
theorem B6513533 : Blo 1285961 6513533 := bstep (se 3 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 6513533 = 2442575) B2442575
theorem B1287039 : Blo 1285961 1287039 := bstep (se 1 (by rfl) ⟨965279, by rfl⟩ : syracuseStep 1287039 = 1930559) B1930559
theorem B2442287 : Blo 1285961 2442287 := bstep (se 1 (by rfl) ⟨1831715, by rfl⟩ : syracuseStep 2442287 = 3663431) B3663431
theorem B1287323 : Blo 1285961 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B1287327 : Blo 1285961 1287327 := bstep (se 1 (by rfl) ⟨965495, by rfl⟩ : syracuseStep 1287327 = 1930991) B1930991
theorem B8471915 : Blo 1285961 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B3663215 : Blo 1285961 3663215 := bstep (se 1 (by rfl) ⟨2747411, by rfl⟩ : syracuseStep 3663215 = 5494823) B5494823
theorem B1287631 : Blo 1285961 1287631 := bstep (se 1 (by rfl) ⟨965723, by rfl⟩ : syracuseStep 1287631 = 1931447) B1931447
theorem B10724833 : Blo 1285961 10724833 := bstep (se 2 (by rfl) ⟨4021812, by rfl⟩ : syracuseStep 10724833 = 8043625) B8043625
theorem B1287663 : Blo 1285961 1287663 := bstep (se 1 (by rfl) ⟨965747, by rfl⟩ : syracuseStep 1287663 = 1931495) B1931495
theorem B4343327 : Blo 1285961 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B2172521 : Blo 1285961 2172521 := bstep (se 2 (by rfl) ⟨814695, by rfl⟩ : syracuseStep 2172521 = 1629391) B1629391
theorem B1287911 : Blo 1285961 1287911 := bstep (se 1 (by rfl) ⟨965933, by rfl⟩ : syracuseStep 1287911 = 1931867) B1931867
theorem B2893607 : Blo 1285961 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B2320211 : Blo 1285961 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B10995689 : Blo 1285961 10995689 := bstep (se 2 (by rfl) ⟨4123383, by rfl⟩ : syracuseStep 10995689 = 8246767) B8246767
theorem B6514667 : Blo 1285961 6514667 := bstep (se 1 (by rfl) ⟨4886000, by rfl⟩ : syracuseStep 6514667 = 9772001) B9772001
theorem B2746523 : Blo 1285961 2746523 := bstep (se 1 (by rfl) ⟨2059892, by rfl⟩ : syracuseStep 2746523 = 4119785) B4119785
theorem B2893985 : Blo 1285961 2893985 := bstep (se 2 (by rfl) ⟨1085244, by rfl⟩ : syracuseStep 2893985 = 2170489) B2170489
theorem B4344137 : Blo 1285961 4344137 := bstep (se 2 (by rfl) ⟨1629051, by rfl⟩ : syracuseStep 4344137 = 3258103) B3258103
theorem B4344299 : Blo 1285961 4344299 := bstep (se 1 (by rfl) ⟨3258224, by rfl⟩ : syracuseStep 4344299 = 6516449) B6516449
theorem B8243795 : Blo 1285961 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B6351839 : Blo 1285961 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B3664865 : Blo 1285961 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B6515801 : Blo 1285961 6515801 := bstep (se 2 (by rfl) ⟨2443425, by rfl⟩ : syracuseStep 6515801 = 4886851) B4886851
theorem B10988855 : Blo 1285961 10988855 := bstep (se 1 (by rfl) ⟨8241641, by rfl⟩ : syracuseStep 10988855 = 16483283) B16483283
theorem B4181303 : Blo 1285961 4181303 := bstep (se 1 (by rfl) ⟨3135977, by rfl⟩ : syracuseStep 4181303 = 6271955) B6271955
theorem B6516125 : Blo 1285961 6516125 := bstep (se 3 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 6516125 = 2443547) B2443547
theorem B2895263 : Blo 1285961 2895263 := bstep (se 1 (by rfl) ⟨2171447, by rfl⟩ : syracuseStep 2895263 = 4342895) B4342895
theorem B2895335 : Blo 1285961 2895335 := bstep (se 1 (by rfl) ⟨2171501, by rfl⟩ : syracuseStep 2895335 = 4343003) B4343003
theorem B3255785 : Blo 1285961 3255785 := bstep (se 2 (by rfl) ⟨1220919, by rfl⟩ : syracuseStep 3255785 = 2441839) B2441839
theorem B14667479 : Blo 1285961 14667479 := bstep (se 1 (by rfl) ⟨11000609, by rfl⟩ : syracuseStep 14667479 = 22001219) B22001219
theorem B1929191 : Blo 1285961 1929191 := bstep (se 1 (by rfl) ⟨1446893, by rfl⟩ : syracuseStep 1929191 = 2893787) B2893787
theorem B1929311 : Blo 1285961 1929311 := bstep (se 1 (by rfl) ⟨1446983, by rfl⟩ : syracuseStep 1929311 = 2893967) B2893967
theorem B3256463 : Blo 1285961 3256463 := bstep (se 1 (by rfl) ⟨2442347, by rfl⟩ : syracuseStep 3256463 = 4884695) B4884695
theorem B6959249 : Blo 1285961 6959249 := bstep (se 2 (by rfl) ⟨2609718, by rfl⟩ : syracuseStep 6959249 = 5219437) B5219437
theorem B1929371 : Blo 1285961 1929371 := bstep (se 1 (by rfl) ⟨1447028, by rfl⟩ : syracuseStep 1929371 = 2894057) B2894057
theorem B1929551 : Blo 1285961 1929551 := bstep (se 1 (by rfl) ⟨1447163, by rfl⟩ : syracuseStep 1929551 = 2894327) B2894327
theorem B2896289 : Blo 1285961 2896289 := bstep (se 2 (by rfl) ⟨1086108, by rfl⟩ : syracuseStep 2896289 = 2172217) B2172217
theorem B1929641 : Blo 1285961 1929641 := bstep (se 2 (by rfl) ⟨723615, by rfl⟩ : syracuseStep 1929641 = 1447231) B1447231
theorem B41734727 : Blo 1285961 41734727 := bstep (se 1 (by rfl) ⟨31301045, by rfl⟩ : syracuseStep 41734727 = 62602091) B62602091
theorem B1929947 : Blo 1285961 1929947 := bstep (se 1 (by rfl) ⟨1447460, by rfl⟩ : syracuseStep 1929947 = 2894921) B2894921
theorem B12374765 : Blo 1285961 12374765 := bstep (se 3 (by rfl) ⟨2320268, by rfl⟩ : syracuseStep 12374765 = 4640537) B4640537
theorem B4346621 : Blo 1285961 4346621 := bstep (se 3 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 4346621 = 1629983) B1629983
theorem B4346783 : Blo 1285961 4346783 := bstep (se 1 (by rfl) ⟨3260087, by rfl⟩ : syracuseStep 4346783 = 6520175) B6520175
theorem B1930217 : Blo 1285961 1930217 := bstep (se 2 (by rfl) ⟨723831, by rfl⟩ : syracuseStep 1930217 = 1447663) B1447663
theorem B26399747 : Blo 1285961 26399747 := bstep (se 1 (by rfl) ⟨19799810, by rfl⟩ : syracuseStep 26399747 = 39599621) B39599621
theorem B9770057 : Blo 1285961 9770057 := bstep (se 2 (by rfl) ⟨3663771, by rfl⟩ : syracuseStep 9770057 = 7327543) B7327543
theorem B1930361 : Blo 1285961 1930361 := bstep (se 2 (by rfl) ⟨723885, by rfl⟩ : syracuseStep 1930361 = 1447771) B1447771
theorem B15660211 : Blo 1285961 15660211 := bstep (se 1 (by rfl) ⟨11745158, by rfl⟩ : syracuseStep 15660211 = 23490317) B23490317
theorem B9655595 : Blo 1285961 9655595 := bstep (se 1 (by rfl) ⟨7241696, by rfl⟩ : syracuseStep 9655595 = 14483393) B14483393
theorem B7329275 : Blo 1285961 7329275 := bstep (se 1 (by rfl) ⟨5496956, by rfl⟩ : syracuseStep 7329275 = 10993913) B10993913
theorem B9270899 : Blo 1285961 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B1930889 : Blo 1285961 1930889 := bstep (se 2 (by rfl) ⟨724083, by rfl⟩ : syracuseStep 1930889 = 1448167) B1448167
theorem B6698639 : Blo 1285961 6698639 := bstep (se 1 (by rfl) ⟨5023979, by rfl⟩ : syracuseStep 6698639 = 10047959) B10047959
theorem B7329527 : Blo 1285961 7329527 := bstep (se 1 (by rfl) ⟨5497145, by rfl⟩ : syracuseStep 7329527 = 10994291) B10994291
theorem B1931099 : Blo 1285961 1931099 := bstep (se 1 (by rfl) ⟨1448324, by rfl⟩ : syracuseStep 1931099 = 2896649) B2896649
theorem B1931135 : Blo 1285961 1931135 := bstep (se 1 (by rfl) ⟨1448351, by rfl⟩ : syracuseStep 1931135 = 2896703) B2896703
theorem B2897819 : Blo 1285961 2897819 := bstep (se 1 (by rfl) ⟨2173364, by rfl⟩ : syracuseStep 2897819 = 4346729) B4346729
theorem B1931231 : Blo 1285961 1931231 := bstep (se 1 (by rfl) ⟨1448423, by rfl⟩ : syracuseStep 1931231 = 2896847) B2896847
theorem B52869131 : Blo 1285961 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B14661647 : Blo 1285961 14661647 := bstep (se 1 (by rfl) ⟨10996235, by rfl⟩ : syracuseStep 14661647 = 21992471) B21992471
theorem B1931291 : Blo 1285961 1931291 := bstep (se 1 (by rfl) ⟨1448468, by rfl⟩ : syracuseStep 1931291 = 2896937) B2896937
theorem B29702315 : Blo 1285961 29702315 := bstep (se 1 (by rfl) ⟨22276736, by rfl⟩ : syracuseStep 29702315 = 44553473) B44553473
theorem B6510779 : Blo 1285961 6510779 := bstep (se 1 (by rfl) ⟨4883084, by rfl⟩ : syracuseStep 6510779 = 9766169) B9766169
theorem B1931483 : Blo 1285961 1931483 := bstep (se 1 (by rfl) ⟨1448612, by rfl⟩ : syracuseStep 1931483 = 2897225) B2897225
theorem B1931753 : Blo 1285961 1931753 := bstep (se 2 (by rfl) ⟨724407, by rfl⟩ : syracuseStep 1931753 = 1448815) B1448815
theorem B8247845 : Blo 1285961 8247845 := bstep (se 4 (by rfl) ⟨773235, by rfl⟩ : syracuseStep 8247845 = 1546471) B1546471
theorem B6961889 : Blo 1285961 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B28572797 : Blo 1285961 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B4635809 : Blo 1285961 4635809 := bstep (se 2 (by rfl) ⟨1738428, by rfl⟩ : syracuseStep 4635809 = 3476857) B3476857
theorem B3259561 : Blo 1285961 3259561 := bstep (se 2 (by rfl) ⟨1222335, by rfl⟩ : syracuseStep 3259561 = 2444671) B2444671
theorem B5496137 : Blo 1285961 5496137 := bstep (se 2 (by rfl) ⟨2061051, by rfl⟩ : syracuseStep 5496137 = 4122103) B4122103
theorem B2350831 : Blo 1285961 2350831 := bstep (se 1 (by rfl) ⟨1763123, by rfl⟩ : syracuseStep 2350831 = 3526247) B3526247
theorem B1286015 : Blo 1285961 1286015 := bstep (se 1 (by rfl) ⟨964511, by rfl⟩ : syracuseStep 1286015 = 1929023) B1929023
theorem B11141003 : Blo 1285961 11141003 := bstep (se 1 (by rfl) ⟨8355752, by rfl⟩ : syracuseStep 11141003 = 16711505) B16711505
theorem B1286139 : Blo 1285961 1286139 := bstep (se 1 (by rfl) ⟨964604, by rfl⟩ : syracuseStep 1286139 = 1929209) B1929209
theorem B1286207 : Blo 1285961 1286207 := bstep (se 1 (by rfl) ⟨964655, by rfl⟩ : syracuseStep 1286207 = 1929311) B1929311
theorem B2170975 : Blo 1285961 2170975 := bstep (se 1 (by rfl) ⟨1628231, by rfl⟩ : syracuseStep 2170975 = 3256463) B3256463
theorem B1286247 : Blo 1285961 1286247 := bstep (se 1 (by rfl) ⟨964685, by rfl⟩ : syracuseStep 1286247 = 1929371) B1929371
theorem B1286367 : Blo 1285961 1286367 := bstep (se 1 (by rfl) ⟨964775, by rfl⟩ : syracuseStep 1286367 = 1929551) B1929551
theorem B1286427 : Blo 1285961 1286427 := bstep (se 1 (by rfl) ⟨964820, by rfl⟩ : syracuseStep 1286427 = 1929641) B1929641
theorem B1286631 : Blo 1285961 1286631 := bstep (se 1 (by rfl) ⟨964973, by rfl⟩ : syracuseStep 1286631 = 1929947) B1929947
theorem B8249843 : Blo 1285961 8249843 := bstep (se 1 (by rfl) ⟨6187382, by rfl⟩ : syracuseStep 8249843 = 12374765) B12374765
theorem B8241695 : Blo 1285961 8241695 := bstep (se 1 (by rfl) ⟨6181271, by rfl⟩ : syracuseStep 8241695 = 12362543) B12362543
theorem B4342355 : Blo 1285961 4342355 := bstep (se 1 (by rfl) ⟨3256766, by rfl⟩ : syracuseStep 4342355 = 6513533) B6513533
theorem B1286811 : Blo 1285961 1286811 := bstep (se 1 (by rfl) ⟨965108, by rfl⟩ : syracuseStep 1286811 = 1930217) B1930217
theorem B6513371 : Blo 1285961 6513371 := bstep (se 1 (by rfl) ⟨4885028, by rfl⟩ : syracuseStep 6513371 = 9770057) B9770057
theorem B1286907 : Blo 1285961 1286907 := bstep (se 1 (by rfl) ⟨965180, by rfl⟩ : syracuseStep 1286907 = 1930361) B1930361
theorem B11150141 : Blo 1285961 11150141 := bstep (se 3 (by rfl) ⟨2090651, by rfl⟩ : syracuseStep 11150141 = 4181303) B4181303
theorem B2442143 : Blo 1285961 2442143 := bstep (se 1 (by rfl) ⟨1831607, by rfl⟩ : syracuseStep 2442143 = 3663215) B3663215
theorem B1287259 : Blo 1285961 1287259 := bstep (se 1 (by rfl) ⟨965444, by rfl⟩ : syracuseStep 1287259 = 1930889) B1930889
theorem B1287399 : Blo 1285961 1287399 := bstep (se 1 (by rfl) ⟨965549, by rfl⟩ : syracuseStep 1287399 = 1931099) B1931099
theorem B1287423 : Blo 1285961 1287423 := bstep (se 1 (by rfl) ⟨965567, by rfl⟩ : syracuseStep 1287423 = 1931135) B1931135
theorem B1287487 : Blo 1285961 1287487 := bstep (se 1 (by rfl) ⟨965615, by rfl⟩ : syracuseStep 1287487 = 1931231) B1931231
theorem B4343111 : Blo 1285961 4343111 := bstep (se 1 (by rfl) ⟨3257333, by rfl⟩ : syracuseStep 4343111 = 6514667) B6514667
theorem B9774431 : Blo 1285961 9774431 := bstep (se 1 (by rfl) ⟨7330823, by rfl⟩ : syracuseStep 9774431 = 14661647) B14661647
theorem B1287527 : Blo 1285961 1287527 := bstep (se 1 (by rfl) ⟨965645, by rfl⟩ : syracuseStep 1287527 = 1931291) B1931291
theorem B19801543 : Blo 1285961 19801543 := bstep (se 1 (by rfl) ⟨14851157, by rfl⟩ : syracuseStep 19801543 = 29702315) B29702315
theorem B1287655 : Blo 1285961 1287655 := bstep (se 1 (by rfl) ⟨965741, by rfl⟩ : syracuseStep 1287655 = 1931483) B1931483
theorem B1287835 : Blo 1285961 1287835 := bstep (se 1 (by rfl) ⟨965876, by rfl⟩ : syracuseStep 1287835 = 1931753) B1931753
theorem B5498563 : Blo 1285961 5498563 := bstep (se 1 (by rfl) ⟨4123922, by rfl⟩ : syracuseStep 5498563 = 8247845) B8247845
theorem B4343867 : Blo 1285961 4343867 := bstep (se 1 (by rfl) ⟨3257900, by rfl⟩ : syracuseStep 4343867 = 6515801) B6515801
theorem B19048531 : Blo 1285961 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B3090539 : Blo 1285961 3090539 := bstep (se 1 (by rfl) ⟨2317904, by rfl⟩ : syracuseStep 3090539 = 4635809) B4635809
theorem B7325903 : Blo 1285961 7325903 := bstep (se 1 (by rfl) ⟨5494427, by rfl⟩ : syracuseStep 7325903 = 10988855) B10988855
theorem B3664091 : Blo 1285961 3664091 := bstep (se 1 (by rfl) ⟨2748068, by rfl⟩ : syracuseStep 3664091 = 5496137) B5496137
theorem B6187229 : Blo 1285961 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B4344083 : Blo 1285961 4344083 := bstep (se 1 (by rfl) ⟨3258062, by rfl⟩ : syracuseStep 4344083 = 6516125) B6516125
theorem B6187691 : Blo 1285961 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B8809175 : Blo 1285961 8809175 := bstep (se 1 (by rfl) ⟨6606881, by rfl⟩ : syracuseStep 8809175 = 13213763) B13213763
theorem B4639499 : Blo 1285961 4639499 := bstep (se 1 (by rfl) ⟨3479624, by rfl⟩ : syracuseStep 4639499 = 6959249) B6959249
theorem B27823151 : Blo 1285961 27823151 := bstep (se 1 (by rfl) ⟨20867363, by rfl⟩ : syracuseStep 27823151 = 41734727) B41734727
theorem B5647943 : Blo 1285961 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B4886183 : Blo 1285961 4886183 := bstep (se 1 (by rfl) ⟨3664637, by rfl⟩ : syracuseStep 4886183 = 7329275) B7329275
theorem B2895551 : Blo 1285961 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B6180599 : Blo 1285961 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B4886351 : Blo 1285961 4886351 := bstep (se 1 (by rfl) ⟨3664763, by rfl⟩ : syracuseStep 4886351 = 7329527) B7329527
theorem B1929071 : Blo 1285961 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B35246087 : Blo 1285961 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B1831015 : Blo 1285961 1831015 := bstep (se 1 (by rfl) ⟨1373261, by rfl⟩ : syracuseStep 1831015 = 2746523) B2746523
theorem B1929323 : Blo 1285961 1929323 := bstep (se 1 (by rfl) ⟨1446992, by rfl⟩ : syracuseStep 1929323 = 2893985) B2893985
theorem B2896091 : Blo 1285961 2896091 := bstep (se 1 (by rfl) ⟨2172068, by rfl⟩ : syracuseStep 2896091 = 4344137) B4344137
theorem B4346081 : Blo 1285961 4346081 := bstep (se 2 (by rfl) ⟨1629780, by rfl⟩ : syracuseStep 4346081 = 3259561) B3259561
theorem B2896199 : Blo 1285961 2896199 := bstep (se 1 (by rfl) ⟨2172149, by rfl⟩ : syracuseStep 2896199 = 4344299) B4344299
theorem B17863037 : Blo 1285961 17863037 := bstep (se 3 (by rfl) ⟨3349319, by rfl⟩ : syracuseStep 17863037 = 6698639) B6698639
theorem B4641259 : Blo 1285961 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B14299777 : Blo 1285961 14299777 := bstep (se 2 (by rfl) ⟨5362416, by rfl⟩ : syracuseStep 14299777 = 10724833) B10724833
theorem B1930175 : Blo 1285961 1930175 := bstep (se 1 (by rfl) ⟨1447631, by rfl⟩ : syracuseStep 1930175 = 2895263) B2895263
theorem B3134441 : Blo 1285961 3134441 := bstep (se 2 (by rfl) ⟨1175415, by rfl⟩ : syracuseStep 3134441 = 2350831) B2350831
theorem B1930223 : Blo 1285961 1930223 := bstep (se 1 (by rfl) ⟨1447667, by rfl⟩ : syracuseStep 1930223 = 2895335) B2895335
theorem B9778319 : Blo 1285961 9778319 := bstep (se 1 (by rfl) ⟨7333739, by rfl⟩ : syracuseStep 9778319 = 14667479) B14667479
theorem B7427335 : Blo 1285961 7427335 := bstep (se 1 (by rfl) ⟨5570501, by rfl⟩ : syracuseStep 7427335 = 11141003) B11141003
theorem B70399325 : Blo 1285961 70399325 := bstep (se 3 (by rfl) ⟨13199873, by rfl⟩ : syracuseStep 70399325 = 26399747) B26399747
theorem B6608303 : Blo 1285961 6608303 := bstep (se 1 (by rfl) ⟨4956227, by rfl⟩ : syracuseStep 6608303 = 9912455) B9912455
theorem B1447375 : Blo 1285961 1447375 := bstep (se 1 (by rfl) ⟨1085531, by rfl⟩ : syracuseStep 1447375 = 2171063) B2171063
theorem B4888127 : Blo 1285961 4888127 := bstep (se 1 (by rfl) ⟨3666095, by rfl⟩ : syracuseStep 4888127 = 7332191) B7332191
theorem B1930859 : Blo 1285961 1930859 := bstep (se 1 (by rfl) ⟨1448144, by rfl⟩ : syracuseStep 1930859 = 2896289) B2896289
theorem B16717423 : Blo 1285961 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B2897747 : Blo 1285961 2897747 := bstep (se 1 (by rfl) ⟨2173310, by rfl⟩ : syracuseStep 2897747 = 4346621) B4346621
theorem B2897855 : Blo 1285961 2897855 := bstep (se 1 (by rfl) ⟨2173391, by rfl⟩ : syracuseStep 2897855 = 4346783) B4346783
theorem B1628191 : Blo 1285961 1628191 := bstep (se 1 (by rfl) ⟨1221143, by rfl⟩ : syracuseStep 1628191 = 2442287) B2442287
theorem B7526521 : Blo 1285961 7526521 := bstep (se 2 (by rfl) ⟨2822445, by rfl⟩ : syracuseStep 7526521 = 5644891) B5644891
theorem B6437063 : Blo 1285961 6437063 := bstep (se 1 (by rfl) ⟨4827797, by rfl⟩ : syracuseStep 6437063 = 9655595) B9655595
theorem B1448347 : Blo 1285961 1448347 := bstep (se 1 (by rfl) ⟨1086260, by rfl⟩ : syracuseStep 1448347 = 2172521) B2172521
theorem B1931879 : Blo 1285961 1931879 := bstep (se 1 (by rfl) ⟨1448909, by rfl⟩ : syracuseStep 1931879 = 2897819) B2897819
theorem B7330459 : Blo 1285961 7330459 := bstep (se 1 (by rfl) ⟨5497844, by rfl⟩ : syracuseStep 7330459 = 10995689) B10995689
theorem B4340519 : Blo 1285961 4340519 := bstep (se 1 (by rfl) ⟨3255389, by rfl⟩ : syracuseStep 4340519 = 6510779) B6510779
theorem B20880281 : Blo 1285961 20880281 := bstep (se 2 (by rfl) ⟨7830105, by rfl⟩ : syracuseStep 20880281 = 15660211) B15660211
theorem B5495863 : Blo 1285961 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B4234559 : Blo 1285961 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B2170523 : Blo 1285961 2170523 := bstep (se 1 (by rfl) ⟨1627892, by rfl⟩ : syracuseStep 2170523 = 3255785) B3255785
theorem B9772973 : Blo 1285961 9772973 := bstep (se 3 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 9772973 = 3664865) B3664865
theorem B1286127 : Blo 1285961 1286127 := bstep (se 1 (by rfl) ⟨964595, by rfl⟩ : syracuseStep 1286127 = 1929191) B1929191
theorem B2170921 : Blo 1285961 2170921 := bstep (se 2 (by rfl) ⟨814095, by rfl⟩ : syracuseStep 2170921 = 1628191) B1628191
theorem B1286215 : Blo 1285961 1286215 := bstep (se 1 (by rfl) ⟨964661, by rfl⟩ : syracuseStep 1286215 = 1929323) B1929323
theorem B2441353 : Blo 1285961 2441353 := bstep (se 2 (by rfl) ⟨915507, by rfl⟩ : syracuseStep 2441353 = 1831015) B1831015
theorem B10035361 : Blo 1285961 10035361 := bstep (se 2 (by rfl) ⟨3763260, by rfl⟩ : syracuseStep 10035361 = 7526521) B7526521
theorem B4342247 : Blo 1285961 4342247 := bstep (se 1 (by rfl) ⟨3256685, by rfl⟩ : syracuseStep 4342247 = 6513371) B6513371
theorem B1286783 : Blo 1285961 1286783 := bstep (se 1 (by rfl) ⟨965087, by rfl⟩ : syracuseStep 1286783 = 1930175) B1930175
theorem B1286815 : Blo 1285961 1286815 := bstep (se 1 (by rfl) ⟨965111, by rfl⟩ : syracuseStep 1286815 = 1930223) B1930223
theorem B9773945 : Blo 1285961 9773945 := bstep (se 2 (by rfl) ⟨3665229, by rfl⟩ : syracuseStep 9773945 = 7330459) B7330459
theorem B1287239 : Blo 1285961 1287239 := bstep (se 1 (by rfl) ⟨965429, by rfl⟩ : syracuseStep 1287239 = 1930859) B1930859
theorem B4883935 : Blo 1285961 4883935 := bstep (se 1 (by rfl) ⟨3662951, by rfl⟩ : syracuseStep 4883935 = 7325903) B7325903
theorem B2442727 : Blo 1285961 2442727 := bstep (se 1 (by rfl) ⟨1832045, by rfl⟩ : syracuseStep 2442727 = 3664091) B3664091
theorem B1287919 : Blo 1285961 1287919 := bstep (se 1 (by rfl) ⟨965939, by rfl⟩ : syracuseStep 1287919 = 1931879) B1931879
theorem B2893679 : Blo 1285961 2893679 := bstep (se 1 (by rfl) ⟨2170259, by rfl⟩ : syracuseStep 2893679 = 4340519) B4340519
theorem B13920187 : Blo 1285961 13920187 := bstep (se 1 (by rfl) ⟨10440140, by rfl⟩ : syracuseStep 13920187 = 20880281) B20880281
theorem B18548767 : Blo 1285961 18548767 := bstep (se 1 (by rfl) ⟨13911575, by rfl⟩ : syracuseStep 18548767 = 27823151) B27823151
theorem B8358509 : Blo 1285961 8358509 := bstep (se 3 (by rfl) ⟨1567220, by rfl⟩ : syracuseStep 8358509 = 3134441) B3134441
theorem B6515315 : Blo 1285961 6515315 := bstep (se 1 (by rfl) ⟨4886486, by rfl⟩ : syracuseStep 6515315 = 9772973) B9772973
theorem B23497391 : Blo 1285961 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B25398041 : Blo 1285961 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B2894633 : Blo 1285961 2894633 := bstep (se 2 (by rfl) ⟨1085487, by rfl⟩ : syracuseStep 2894633 = 2170975) B2170975
theorem B5499895 : Blo 1285961 5499895 := bstep (se 1 (by rfl) ⟨4124921, by rfl⟩ : syracuseStep 5499895 = 8249843) B8249843
theorem B2894903 : Blo 1285961 2894903 := bstep (se 1 (by rfl) ⟨2171177, by rfl⟩ : syracuseStep 2894903 = 4342355) B4342355
theorem B118934837 : Blo 1285961 118934837 := bstep (se 5 (by rfl) ⟨5575070, by rfl⟩ : syracuseStep 118934837 = 11150141) B11150141
theorem B6188345 : Blo 1285961 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B11292157 : Blo 1285961 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B19066369 : Blo 1285961 19066369 := bstep (se 2 (by rfl) ⟨7149888, by rfl⟩ : syracuseStep 19066369 = 14299777) B14299777
theorem B2895407 : Blo 1285961 2895407 := bstep (se 1 (by rfl) ⟨2171555, by rfl⟩ : syracuseStep 2895407 = 4343111) B4343111
theorem B6516287 : Blo 1285961 6516287 := bstep (se 1 (by rfl) ⟨4887215, by rfl⟩ : syracuseStep 6516287 = 9774431) B9774431
theorem B187731533 : Blo 1285961 187731533 := bstep (se 3 (by rfl) ⟨35199662, by rfl⟩ : syracuseStep 187731533 = 70399325) B70399325
theorem B2895911 : Blo 1285961 2895911 := bstep (se 1 (by rfl) ⟨2171933, by rfl⟩ : syracuseStep 2895911 = 4343867) B4343867
theorem B2060359 : Blo 1285961 2060359 := bstep (se 1 (by rfl) ⟨1545269, by rfl⟩ : syracuseStep 2060359 = 3090539) B3090539
theorem B7327817 : Blo 1285961 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B4124819 : Blo 1285961 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B2896055 : Blo 1285961 2896055 := bstep (se 1 (by rfl) ⟨2172041, by rfl⟩ : syracuseStep 2896055 = 4344083) B4344083
theorem B4125127 : Blo 1285961 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B3092999 : Blo 1285961 3092999 := bstep (se 1 (by rfl) ⟨2319749, by rfl⟩ : syracuseStep 3092999 = 4639499) B4639499
theorem B1929833 : Blo 1285961 1929833 := bstep (se 2 (by rfl) ⟨723687, by rfl⟩ : syracuseStep 1929833 = 1447375) B1447375
theorem B3765295 : Blo 1285961 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B1447015 : Blo 1285961 1447015 := bstep (se 1 (by rfl) ⟨1085261, by rfl⟩ : syracuseStep 1447015 = 2170523) B2170523
theorem B3257455 : Blo 1285961 3257455 := bstep (se 1 (by rfl) ⟨2443091, by rfl⟩ : syracuseStep 3257455 = 4886183) B4886183
theorem B1930367 : Blo 1285961 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B3257567 : Blo 1285961 3257567 := bstep (se 1 (by rfl) ⟨2443175, by rfl⟩ : syracuseStep 3257567 = 4886351) B4886351
theorem B1930727 : Blo 1285961 1930727 := bstep (se 1 (by rfl) ⟨1448045, by rfl⟩ : syracuseStep 1930727 = 2896091) B2896091
theorem B2897387 : Blo 1285961 2897387 := bstep (se 1 (by rfl) ⟨2173040, by rfl⟩ : syracuseStep 2897387 = 4346081) B4346081
theorem B1930799 : Blo 1285961 1930799 := bstep (se 1 (by rfl) ⟨1448099, by rfl⟩ : syracuseStep 1930799 = 2896199) B2896199
theorem B11908691 : Blo 1285961 11908691 := bstep (se 1 (by rfl) ⟨8931518, by rfl⟩ : syracuseStep 11908691 = 17863037) B17863037
theorem B5494463 : Blo 1285961 5494463 := bstep (se 1 (by rfl) ⟨4120847, by rfl⟩ : syracuseStep 5494463 = 8241695) B8241695
theorem B1931129 : Blo 1285961 1931129 := bstep (se 2 (by rfl) ⟨724173, by rfl⟩ : syracuseStep 1931129 = 1448347) B1448347
theorem B1628095 : Blo 1285961 1628095 := bstep (se 1 (by rfl) ⟨1221071, by rfl⟩ : syracuseStep 1628095 = 2442143) B2442143
theorem B6518879 : Blo 1285961 6518879 := bstep (se 1 (by rfl) ⟨4889159, by rfl⟩ : syracuseStep 6518879 = 9778319) B9778319
theorem B4405535 : Blo 1285961 4405535 := bstep (se 1 (by rfl) ⟨3304151, by rfl⟩ : syracuseStep 4405535 = 6608303) B6608303
theorem B3258751 : Blo 1285961 3258751 := bstep (se 1 (by rfl) ⟨2444063, by rfl⟩ : syracuseStep 3258751 = 4888127) B4888127
theorem B1931831 : Blo 1285961 1931831 := bstep (se 1 (by rfl) ⟨1448873, by rfl⟩ : syracuseStep 1931831 = 2897747) B2897747
theorem B1931903 : Blo 1285961 1931903 := bstep (se 1 (by rfl) ⟨1448927, by rfl⟩ : syracuseStep 1931903 = 2897855) B2897855
theorem B4291375 : Blo 1285961 4291375 := bstep (se 1 (by rfl) ⟨3218531, by rfl⟩ : syracuseStep 4291375 = 6437063) B6437063
theorem B9903113 : Blo 1285961 9903113 := bstep (se 2 (by rfl) ⟨3713667, by rfl⟩ : syracuseStep 9903113 = 7427335) B7427335
theorem B5872783 : Blo 1285961 5872783 := bstep (se 1 (by rfl) ⟨4404587, by rfl⟩ : syracuseStep 5872783 = 8809175) B8809175
theorem B26402057 : Blo 1285961 26402057 := bstep (se 2 (by rfl) ⟨9900771, by rfl⟩ : syracuseStep 26402057 = 19801543) B19801543
theorem B22289897 : Blo 1285961 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B7331417 : Blo 1285961 7331417 := bstep (se 2 (by rfl) ⟨2749281, by rfl⟩ : syracuseStep 7331417 = 5498563) B5498563
theorem B4120399 : Blo 1285961 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B1286047 : Blo 1285961 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B24731689 : Blo 1285961 24731689 := bstep (se 2 (by rfl) ⟨9274383, by rfl⟩ : syracuseStep 24731689 = 18548767) B18548767
theorem B1286555 : Blo 1285961 1286555 := bstep (se 1 (by rfl) ⟨964916, by rfl⟩ : syracuseStep 1286555 = 1929833) B1929833
theorem B1286911 : Blo 1285961 1286911 := bstep (se 1 (by rfl) ⟨965183, by rfl⟩ : syracuseStep 1286911 = 1930367) B1930367
theorem B2171711 : Blo 1285961 2171711 := bstep (se 1 (by rfl) ⟨1628783, by rfl⟩ : syracuseStep 2171711 = 3257567) B3257567
theorem B1287151 : Blo 1285961 1287151 := bstep (se 1 (by rfl) ⟨965363, by rfl⟩ : syracuseStep 1287151 = 1930727) B1930727
theorem B1287199 : Blo 1285961 1287199 := bstep (se 1 (by rfl) ⟨965399, by rfl⟩ : syracuseStep 1287199 = 1930799) B1930799
theorem B7939127 : Blo 1285961 7939127 := bstep (se 1 (by rfl) ⟨5954345, by rfl⟩ : syracuseStep 7939127 = 11908691) B11908691
theorem B3662975 : Blo 1285961 3662975 := bstep (se 1 (by rfl) ⟨2747231, by rfl⟩ : syracuseStep 3662975 = 5494463) B5494463
theorem B1287419 : Blo 1285961 1287419 := bstep (se 1 (by rfl) ⟨965564, by rfl⟩ : syracuseStep 1287419 = 1931129) B1931129
theorem B7333193 : Blo 1285961 7333193 := bstep (se 2 (by rfl) ⟨2749947, by rfl⟩ : syracuseStep 7333193 = 5499895) B5499895
theorem B4343273 : Blo 1285961 4343273 := bstep (se 2 (by rfl) ⟨1628727, by rfl⟩ : syracuseStep 4343273 = 3257455) B3257455
theorem B1287887 : Blo 1285961 1287887 := bstep (se 1 (by rfl) ⟨965915, by rfl⟩ : syracuseStep 1287887 = 1931831) B1931831
theorem B4343543 : Blo 1285961 4343543 := bstep (se 1 (by rfl) ⟨3257657, by rfl⟩ : syracuseStep 4343543 = 6515315) B6515315
theorem B1287935 : Blo 1285961 1287935 := bstep (se 1 (by rfl) ⟨965951, by rfl⟩ : syracuseStep 1287935 = 1931903) B1931903
theorem B15664927 : Blo 1285961 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B25421825 : Blo 1285961 25421825 := bstep (se 2 (by rfl) ⟨9533184, by rfl⟩ : syracuseStep 25421825 = 19066369) B19066369
theorem B4344191 : Blo 1285961 4344191 := bstep (se 1 (by rfl) ⟨3258143, by rfl⟩ : syracuseStep 4344191 = 6516287) B6516287
theorem B4885211 : Blo 1285961 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B2894561 : Blo 1285961 2894561 := bstep (se 2 (by rfl) ⟨1085460, by rfl⟩ : syracuseStep 2894561 = 2170921) B2170921
theorem B3255137 : Blo 1285961 3255137 := bstep (se 2 (by rfl) ⟨1220676, by rfl⟩ : syracuseStep 3255137 = 2441353) B2441353
theorem B13380481 : Blo 1285961 13380481 := bstep (se 2 (by rfl) ⟨5017680, by rfl⟩ : syracuseStep 13380481 = 10035361) B10035361
theorem B270912437 : Blo 1285961 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B2894831 : Blo 1285961 2894831 := bstep (se 1 (by rfl) ⟨2171123, by rfl⟩ : syracuseStep 2894831 = 4342247) B4342247
theorem B10988581 : Blo 1285961 10988581 := bstep (se 4 (by rfl) ⟨1030179, by rfl⟩ : syracuseStep 10988581 = 2060359) B2060359
theorem B4345001 : Blo 1285961 4345001 := bstep (se 2 (by rfl) ⟨1629375, by rfl⟩ : syracuseStep 4345001 = 3258751) B3258751
theorem B6515963 : Blo 1285961 6515963 := bstep (se 1 (by rfl) ⟨4886972, by rfl⟩ : syracuseStep 6515963 = 9773945) B9773945
theorem B5500169 : Blo 1285961 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B5721833 : Blo 1285961 5721833 := bstep (se 2 (by rfl) ⟨2145687, by rfl⟩ : syracuseStep 5721833 = 4291375) B4291375
theorem B1929119 : Blo 1285961 1929119 := bstep (se 1 (by rfl) ⟨1446839, by rfl⟩ : syracuseStep 1929119 = 2893679) B2893679
theorem B4345919 : Blo 1285961 4345919 := bstep (se 1 (by rfl) ⟨3259439, by rfl⟩ : syracuseStep 4345919 = 6518879) B6518879
theorem B1929353 : Blo 1285961 1929353 := bstep (se 2 (by rfl) ⟨723507, by rfl⟩ : syracuseStep 1929353 = 1447015) B1447015
theorem B2937023 : Blo 1285961 2937023 := bstep (se 1 (by rfl) ⟨2202767, by rfl⟩ : syracuseStep 2937023 = 4405535) B4405535
theorem B1929755 : Blo 1285961 1929755 := bstep (se 1 (by rfl) ⟨1447316, by rfl⟩ : syracuseStep 1929755 = 2894633) B2894633
theorem B3256969 : Blo 1285961 3256969 := bstep (se 2 (by rfl) ⟨1221363, by rfl⟩ : syracuseStep 3256969 = 2442727) B2442727
theorem B1929935 : Blo 1285961 1929935 := bstep (se 1 (by rfl) ⟨1447451, by rfl⟩ : syracuseStep 1929935 = 2894903) B2894903
theorem B17601371 : Blo 1285961 17601371 := bstep (se 1 (by rfl) ⟨13201028, by rfl⟩ : syracuseStep 17601371 = 26402057) B26402057
theorem B4125563 : Blo 1285961 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B1930271 : Blo 1285961 1930271 := bstep (se 1 (by rfl) ⟨1447703, by rfl⟩ : syracuseStep 1930271 = 2895407) B2895407
theorem B125154355 : Blo 1285961 125154355 := bstep (se 1 (by rfl) ⟨93865766, by rfl⟩ : syracuseStep 125154355 = 187731533) B187731533
theorem B4887611 : Blo 1285961 4887611 := bstep (se 1 (by rfl) ⟨3665708, by rfl⟩ : syracuseStep 4887611 = 7331417) B7331417
theorem B5493865 : Blo 1285961 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B18560249 : Blo 1285961 18560249 := bstep (se 2 (by rfl) ⟨6960093, by rfl⟩ : syracuseStep 18560249 = 13920187) B13920187
theorem B1930607 : Blo 1285961 1930607 := bstep (se 1 (by rfl) ⟨1447955, by rfl⟩ : syracuseStep 1930607 = 2895911) B2895911
theorem B2749879 : Blo 1285961 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B1930703 : Blo 1285961 1930703 := bstep (se 1 (by rfl) ⟨1448027, by rfl⟩ : syracuseStep 1930703 = 2896055) B2896055
theorem B1931591 : Blo 1285961 1931591 := bstep (se 1 (by rfl) ⟨1448693, by rfl⟩ : syracuseStep 1931591 = 2897387) B2897387
theorem B8247997 : Blo 1285961 8247997 := bstep (se 3 (by rfl) ⟨1546499, by rfl⟩ : syracuseStep 8247997 = 3092999) B3092999
theorem B5020393 : Blo 1285961 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B7830377 : Blo 1285961 7830377 := bstep (se 2 (by rfl) ⟨2936391, by rfl⟩ : syracuseStep 7830377 = 5872783) B5872783
theorem B22289357 : Blo 1285961 22289357 := bstep (se 3 (by rfl) ⟨4179254, by rfl⟩ : syracuseStep 22289357 = 8358509) B8358509
theorem B6511913 : Blo 1285961 6511913 := bstep (se 2 (by rfl) ⟨2441967, by rfl⟩ : syracuseStep 6511913 = 4883935) B4883935
theorem B15056209 : Blo 1285961 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B6602075 : Blo 1285961 6602075 := bstep (se 1 (by rfl) ⟨4951556, by rfl⟩ : syracuseStep 6602075 = 9903113) B9903113
theorem B79289891 : Blo 1285961 79289891 := bstep (se 1 (by rfl) ⟨59467418, by rfl⟩ : syracuseStep 79289891 = 118934837) B118934837
theorem B14859931 : Blo 1285961 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B2170793 : Blo 1285961 2170793 := bstep (se 2 (by rfl) ⟨814047, by rfl⟩ : syracuseStep 2170793 = 1628095) B1628095
theorem B1286235 : Blo 1285961 1286235 := bstep (se 1 (by rfl) ⟨964676, by rfl⟩ : syracuseStep 1286235 = 1929353) B1929353
theorem B1958015 : Blo 1285961 1958015 := bstep (se 1 (by rfl) ⟨1468511, by rfl⟩ : syracuseStep 1958015 = 2937023) B2937023
theorem B1286503 : Blo 1285961 1286503 := bstep (se 1 (by rfl) ⟨964877, by rfl⟩ : syracuseStep 1286503 = 1929755) B1929755
theorem B1286623 : Blo 1285961 1286623 := bstep (se 1 (by rfl) ⟨964967, by rfl⟩ : syracuseStep 1286623 = 1929935) B1929935
theorem B1286847 : Blo 1285961 1286847 := bstep (se 1 (by rfl) ⟨965135, by rfl⟩ : syracuseStep 1286847 = 1930271) B1930271
theorem B5292751 : Blo 1285961 5292751 := bstep (se 1 (by rfl) ⟨3969563, by rfl⟩ : syracuseStep 5292751 = 7939127) B7939127
theorem B2441983 : Blo 1285961 2441983 := bstep (se 1 (by rfl) ⟨1831487, by rfl⟩ : syracuseStep 2441983 = 3662975) B3662975
theorem B4342625 : Blo 1285961 4342625 := bstep (se 2 (by rfl) ⟨1628484, by rfl⟩ : syracuseStep 4342625 = 3256969) B3256969
theorem B1287071 : Blo 1285961 1287071 := bstep (se 1 (by rfl) ⟨965303, by rfl⟩ : syracuseStep 1287071 = 1930607) B1930607
theorem B1287135 : Blo 1285961 1287135 := bstep (se 1 (by rfl) ⟨965351, by rfl⟩ : syracuseStep 1287135 = 1930703) B1930703
theorem B6693857 : Blo 1285961 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B166872473 : Blo 1285961 166872473 := bstep (se 2 (by rfl) ⟨62577177, by rfl⟩ : syracuseStep 166872473 = 125154355) B125154355
theorem B7325153 : Blo 1285961 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B1287727 : Blo 1285961 1287727 := bstep (se 1 (by rfl) ⟨965795, by rfl⟩ : syracuseStep 1287727 = 1931591) B1931591
theorem B80299781 : Blo 1285961 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B5220251 : Blo 1285961 5220251 := bstep (se 1 (by rfl) ⟨3915188, by rfl⟩ : syracuseStep 5220251 = 7830377) B7830377
theorem B4343975 : Blo 1285961 4343975 := bstep (se 1 (by rfl) ⟨3257981, by rfl⟩ : syracuseStep 4343975 = 6515963) B6515963
theorem B4401383 : Blo 1285961 4401383 := bstep (se 1 (by rfl) ⟨3301037, by rfl⟩ : syracuseStep 4401383 = 6602075) B6602075
theorem B14666021 : Blo 1285961 14666021 := bstep (se 4 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 14666021 = 2749879) B2749879
theorem B32975585 : Blo 1285961 32975585 := bstep (se 2 (by rfl) ⟨12365844, by rfl⟩ : syracuseStep 32975585 = 24731689) B24731689
theorem B11734247 : Blo 1285961 11734247 := bstep (se 1 (by rfl) ⟨8800685, by rfl⟩ : syracuseStep 11734247 = 17601371) B17601371
theorem B12373499 : Blo 1285961 12373499 := bstep (se 1 (by rfl) ⟨9280124, by rfl⟩ : syracuseStep 12373499 = 18560249) B18560249
theorem B10997329 : Blo 1285961 10997329 := bstep (se 2 (by rfl) ⟨4123998, by rfl⟩ : syracuseStep 10997329 = 8247997) B8247997
theorem B2895515 : Blo 1285961 2895515 := bstep (se 1 (by rfl) ⟨2171636, by rfl⟩ : syracuseStep 2895515 = 4343273) B4343273
theorem B2895695 : Blo 1285961 2895695 := bstep (se 1 (by rfl) ⟨2171771, by rfl⟩ : syracuseStep 2895695 = 4343543) B4343543
theorem B14651441 : Blo 1285961 14651441 := bstep (se 2 (by rfl) ⟨5494290, by rfl⟩ : syracuseStep 14651441 = 10988581) B10988581
theorem B2896127 : Blo 1285961 2896127 := bstep (se 1 (by rfl) ⟨2172095, by rfl⟩ : syracuseStep 2896127 = 4344191) B4344191
theorem B3256807 : Blo 1285961 3256807 := bstep (se 1 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 3256807 = 4885211) B4885211
theorem B1929707 : Blo 1285961 1929707 := bstep (se 1 (by rfl) ⟨1447280, by rfl⟩ : syracuseStep 1929707 = 2894561) B2894561
theorem B1929887 : Blo 1285961 1929887 := bstep (se 1 (by rfl) ⟨1447415, by rfl⟩ : syracuseStep 1929887 = 2894831) B2894831
theorem B2896667 : Blo 1285961 2896667 := bstep (se 1 (by rfl) ⟨2172500, by rfl⟩ : syracuseStep 2896667 = 4345001) B4345001
theorem B3666779 : Blo 1285961 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B19813241 : Blo 1285961 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B52859927 : Blo 1285961 52859927 := bstep (se 1 (by rfl) ⟨39644945, by rfl⟩ : syracuseStep 52859927 = 79289891) B79289891
theorem B20886569 : Blo 1285961 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B3814555 : Blo 1285961 3814555 := bstep (se 1 (by rfl) ⟨2860916, by rfl⟩ : syracuseStep 3814555 = 5721833) B5721833
theorem B59438285 : Blo 1285961 59438285 := bstep (se 3 (by rfl) ⟨11144678, by rfl⟩ : syracuseStep 59438285 = 22289357) B22289357
theorem B1447195 : Blo 1285961 1447195 := bstep (se 1 (by rfl) ⟨1085396, by rfl⟩ : syracuseStep 1447195 = 2170793) B2170793
theorem B2897279 : Blo 1285961 2897279 := bstep (se 1 (by rfl) ⟨2172959, by rfl⟩ : syracuseStep 2897279 = 4345919) B4345919
theorem B1447807 : Blo 1285961 1447807 := bstep (se 1 (by rfl) ⟨1085855, by rfl⟩ : syracuseStep 1447807 = 2171711) B2171711
theorem B2750375 : Blo 1285961 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B3258407 : Blo 1285961 3258407 := bstep (se 1 (by rfl) ⟨2443805, by rfl⟩ : syracuseStep 3258407 = 4887611) B4887611
theorem B4888795 : Blo 1285961 4888795 := bstep (se 1 (by rfl) ⟨3666596, by rfl⟩ : syracuseStep 4888795 = 7333193) B7333193
theorem B17840641 : Blo 1285961 17840641 := bstep (se 2 (by rfl) ⟨6690240, by rfl⟩ : syracuseStep 17840641 = 13380481) B13380481
theorem B16947883 : Blo 1285961 16947883 := bstep (se 1 (by rfl) ⟨12710912, by rfl⟩ : syracuseStep 16947883 = 25421825) B25421825
theorem B2170091 : Blo 1285961 2170091 := bstep (se 1 (by rfl) ⟨1627568, by rfl⟩ : syracuseStep 2170091 = 3255137) B3255137
theorem B180608291 : Blo 1285961 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B4341275 : Blo 1285961 4341275 := bstep (se 1 (by rfl) ⟨3255956, by rfl⟩ : syracuseStep 4341275 = 6511913) B6511913
theorem B1286079 : Blo 1285961 1286079 := bstep (se 1 (by rfl) ⟨964559, by rfl⟩ : syracuseStep 1286079 = 1929119) B1929119
theorem B1286471 : Blo 1285961 1286471 := bstep (se 1 (by rfl) ⟨964853, by rfl⟩ : syracuseStep 1286471 = 1929707) B1929707
theorem B1286591 : Blo 1285961 1286591 := bstep (se 1 (by rfl) ⟨964943, by rfl⟩ : syracuseStep 1286591 = 1929887) B1929887
theorem B4342409 : Blo 1285961 4342409 := bstep (se 2 (by rfl) ⟨1628403, by rfl⟩ : syracuseStep 4342409 = 3256807) B3256807
theorem B39625523 : Blo 1285961 39625523 := bstep (se 1 (by rfl) ⟨29719142, by rfl⟩ : syracuseStep 39625523 = 59438285) B59438285
theorem B111248315 : Blo 1285961 111248315 := bstep (se 1 (by rfl) ⟨83436236, by rfl⟩ : syracuseStep 111248315 = 166872473) B166872473
theorem B4883435 : Blo 1285961 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B2172271 : Blo 1285961 2172271 := bstep (se 1 (by rfl) ⟨1629203, by rfl⟩ : syracuseStep 2172271 = 3258407) B3258407
theorem B2894183 : Blo 1285961 2894183 := bstep (se 1 (by rfl) ⟨2170637, by rfl⟩ : syracuseStep 2894183 = 4341275) B4341275
theorem B7334333 : Blo 1285961 7334333 := bstep (se 3 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 7334333 = 2750375) B2750375
theorem B9767627 : Blo 1285961 9767627 := bstep (se 1 (by rfl) ⟨7325720, by rfl⟩ : syracuseStep 9767627 = 14651441) B14651441
theorem B1305343 : Blo 1285961 1305343 := bstep (se 1 (by rfl) ⟨979007, by rfl⟩ : syracuseStep 1305343 = 1958015) B1958015
theorem B2444519 : Blo 1285961 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B2895083 : Blo 1285961 2895083 := bstep (se 1 (by rfl) ⟨2171312, by rfl⟩ : syracuseStep 2895083 = 4342625) B4342625
theorem B13208827 : Blo 1285961 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B22597177 : Blo 1285961 22597177 := bstep (se 2 (by rfl) ⟨8473941, by rfl⟩ : syracuseStep 22597177 = 16947883) B16947883
theorem B7057001 : Blo 1285961 7057001 := bstep (se 2 (by rfl) ⟨2646375, by rfl⟩ : syracuseStep 7057001 = 5292751) B5292751
theorem B3255977 : Blo 1285961 3255977 := bstep (se 2 (by rfl) ⟨1220991, by rfl⟩ : syracuseStep 3255977 = 2441983) B2441983
theorem B2895983 : Blo 1285961 2895983 := bstep (se 1 (by rfl) ⟨2171987, by rfl⟩ : syracuseStep 2895983 = 4343975) B4343975
theorem B9777347 : Blo 1285961 9777347 := bstep (se 1 (by rfl) ⟨7333010, by rfl⟩ : syracuseStep 9777347 = 14666021) B14666021
theorem B1929593 : Blo 1285961 1929593 := bstep (se 2 (by rfl) ⟨723597, by rfl⟩ : syracuseStep 1929593 = 1447195) B1447195
theorem B21983723 : Blo 1285961 21983723 := bstep (se 1 (by rfl) ⟨16487792, by rfl⟩ : syracuseStep 21983723 = 32975585) B32975585
theorem B1446727 : Blo 1285961 1446727 := bstep (se 1 (by rfl) ⟨1085045, by rfl⟩ : syracuseStep 1446727 = 2170091) B2170091
theorem B1930343 : Blo 1285961 1930343 := bstep (se 1 (by rfl) ⟨1447757, by rfl⟩ : syracuseStep 1930343 = 2895515) B2895515
theorem B1930409 : Blo 1285961 1930409 := bstep (se 2 (by rfl) ⟨723903, by rfl⟩ : syracuseStep 1930409 = 1447807) B1447807
theorem B1930463 : Blo 1285961 1930463 := bstep (se 1 (by rfl) ⟨1447847, by rfl⟩ : syracuseStep 1930463 = 2895695) B2895695
theorem B1930751 : Blo 1285961 1930751 := bstep (se 1 (by rfl) ⟨1448063, by rfl⟩ : syracuseStep 1930751 = 2896127) B2896127
theorem B6518393 : Blo 1285961 6518393 := bstep (se 2 (by rfl) ⟨2444397, by rfl⟩ : syracuseStep 6518393 = 4888795) B4888795
theorem B1931111 : Blo 1285961 1931111 := bstep (se 1 (by rfl) ⟨1448333, by rfl⟩ : syracuseStep 1931111 = 2896667) B2896667
theorem B11737021 : Blo 1285961 11737021 := bstep (se 3 (by rfl) ⟨2200691, by rfl⟩ : syracuseStep 11737021 = 4401383) B4401383
theorem B4462571 : Blo 1285961 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B23787521 : Blo 1285961 23787521 := bstep (se 2 (by rfl) ⟨8920320, by rfl⟩ : syracuseStep 23787521 = 17840641) B17840641
theorem B35239951 : Blo 1285961 35239951 := bstep (se 1 (by rfl) ⟨26429963, by rfl⟩ : syracuseStep 35239951 = 52859927) B52859927
theorem B13924379 : Blo 1285961 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B1931519 : Blo 1285961 1931519 := bstep (se 1 (by rfl) ⟨1448639, by rfl⟩ : syracuseStep 1931519 = 2897279) B2897279
theorem B53533187 : Blo 1285961 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B3480167 : Blo 1285961 3480167 := bstep (se 1 (by rfl) ⟨2610125, by rfl⟩ : syracuseStep 3480167 = 5220251) B5220251
theorem B5086073 : Blo 1285961 5086073 := bstep (se 2 (by rfl) ⟨1907277, by rfl⟩ : syracuseStep 5086073 = 3814555) B3814555
theorem B14663105 : Blo 1285961 14663105 := bstep (se 2 (by rfl) ⟨5498664, by rfl⟩ : syracuseStep 14663105 = 10997329) B10997329
theorem B7822831 : Blo 1285961 7822831 := bstep (se 1 (by rfl) ⟨5867123, by rfl⟩ : syracuseStep 7822831 = 11734247) B11734247
theorem B120405527 : Blo 1285961 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B8248999 : Blo 1285961 8248999 := bstep (se 1 (by rfl) ⟨6186749, by rfl⟩ : syracuseStep 8248999 = 12373499) B12373499
theorem B1286395 : Blo 1285961 1286395 := bstep (se 1 (by rfl) ⟨964796, by rfl⟩ : syracuseStep 1286395 = 1929593) B1929593
theorem B14655815 : Blo 1285961 14655815 := bstep (se 1 (by rfl) ⟨10991861, by rfl⟩ : syracuseStep 14655815 = 21983723) B21983723
theorem B1286895 : Blo 1285961 1286895 := bstep (se 1 (by rfl) ⟨965171, by rfl⟩ : syracuseStep 1286895 = 1930343) B1930343
theorem B1286939 : Blo 1285961 1286939 := bstep (se 1 (by rfl) ⟨965204, by rfl⟩ : syracuseStep 1286939 = 1930409) B1930409
theorem B1286975 : Blo 1285961 1286975 := bstep (se 1 (by rfl) ⟨965231, by rfl⟩ : syracuseStep 1286975 = 1930463) B1930463
theorem B1287167 : Blo 1285961 1287167 := bstep (se 1 (by rfl) ⟨965375, by rfl⟩ : syracuseStep 1287167 = 1930751) B1930751
theorem B1287407 : Blo 1285961 1287407 := bstep (se 1 (by rfl) ⟨965555, by rfl⟩ : syracuseStep 1287407 = 1931111) B1931111
theorem B9282919 : Blo 1285961 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B1287679 : Blo 1285961 1287679 := bstep (se 1 (by rfl) ⟨965759, by rfl⟩ : syracuseStep 1287679 = 1931519) B1931519
theorem B18818669 : Blo 1285961 18818669 := bstep (se 3 (by rfl) ⟨3528500, by rfl⟩ : syracuseStep 18818669 = 7057001) B7057001
theorem B2320111 : Blo 1285961 2320111 := bstep (se 1 (by rfl) ⟨1740083, by rfl⟩ : syracuseStep 2320111 = 3480167) B3480167
theorem B10430441 : Blo 1285961 10430441 := bstep (se 2 (by rfl) ⟨3911415, by rfl⟩ : syracuseStep 10430441 = 7822831) B7822831
theorem B9775403 : Blo 1285961 9775403 := bstep (se 1 (by rfl) ⟨7331552, by rfl⟩ : syracuseStep 9775403 = 14663105) B14663105
theorem B15649361 : Blo 1285961 15649361 := bstep (se 2 (by rfl) ⟨5868510, by rfl⟩ : syracuseStep 15649361 = 11737021) B11737021
theorem B2894939 : Blo 1285961 2894939 := bstep (se 1 (by rfl) ⟨2171204, by rfl⟩ : syracuseStep 2894939 = 4342409) B4342409
theorem B74165543 : Blo 1285961 74165543 := bstep (se 1 (by rfl) ⟨55624157, by rfl⟩ : syracuseStep 74165543 = 111248315) B111248315
theorem B3255623 : Blo 1285961 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B1740457 : Blo 1285961 1740457 := bstep (se 2 (by rfl) ⟨652671, by rfl⟩ : syracuseStep 1740457 = 1305343) B1305343
theorem B4345595 : Blo 1285961 4345595 := bstep (se 1 (by rfl) ⟨3259196, by rfl⟩ : syracuseStep 4345595 = 6518393) B6518393
theorem B1928969 : Blo 1285961 1928969 := bstep (se 2 (by rfl) ⟨723363, by rfl⟩ : syracuseStep 1928969 = 1446727) B1446727
theorem B1929455 : Blo 1285961 1929455 := bstep (se 1 (by rfl) ⟨1447091, by rfl⟩ : syracuseStep 1929455 = 2894183) B2894183
theorem B35688791 : Blo 1285961 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B2896361 : Blo 1285961 2896361 := bstep (se 2 (by rfl) ⟨1086135, by rfl⟩ : syracuseStep 2896361 = 2172271) B2172271
theorem B1930055 : Blo 1285961 1930055 := bstep (se 1 (by rfl) ⟨1447541, by rfl⟩ : syracuseStep 1930055 = 2895083) B2895083
theorem B10998665 : Blo 1285961 10998665 := bstep (se 2 (by rfl) ⟨4124499, by rfl⟩ : syracuseStep 10998665 = 8248999) B8248999
theorem B13562861 : Blo 1285961 13562861 := bstep (se 3 (by rfl) ⟨2543036, by rfl⟩ : syracuseStep 13562861 = 5086073) B5086073
theorem B80270351 : Blo 1285961 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B11900189 : Blo 1285961 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B1930655 : Blo 1285961 1930655 := bstep (se 1 (by rfl) ⟨1447991, by rfl⟩ : syracuseStep 1930655 = 2895983) B2895983
theorem B187946405 : Blo 1285961 187946405 := bstep (se 4 (by rfl) ⟨17619975, by rfl⟩ : syracuseStep 187946405 = 35239951) B35239951
theorem B6518231 : Blo 1285961 6518231 := bstep (se 1 (by rfl) ⟨4888673, by rfl⟩ : syracuseStep 6518231 = 9777347) B9777347
theorem B26417015 : Blo 1285961 26417015 := bstep (se 1 (by rfl) ⟨19812761, by rfl⟩ : syracuseStep 26417015 = 39625523) B39625523
theorem B6518717 : Blo 1285961 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B15858347 : Blo 1285961 15858347 := bstep (se 1 (by rfl) ⟨11893760, by rfl⟩ : syracuseStep 15858347 = 23787521) B23787521
theorem B4889555 : Blo 1285961 4889555 := bstep (se 1 (by rfl) ⟨3667166, by rfl⟩ : syracuseStep 4889555 = 7334333) B7334333
theorem B17611769 : Blo 1285961 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B6511751 : Blo 1285961 6511751 := bstep (se 1 (by rfl) ⟨4883813, by rfl⟩ : syracuseStep 6511751 = 9767627) B9767627
theorem B30129569 : Blo 1285961 30129569 := bstep (se 2 (by rfl) ⟨11298588, by rfl⟩ : syracuseStep 30129569 = 22597177) B22597177
theorem B2170651 : Blo 1285961 2170651 := bstep (se 1 (by rfl) ⟨1627988, by rfl⟩ : syracuseStep 2170651 = 3255977) B3255977
theorem B1286303 : Blo 1285961 1286303 := bstep (se 1 (by rfl) ⟨964727, by rfl⟩ : syracuseStep 1286303 = 1929455) B1929455
theorem B1286703 : Blo 1285961 1286703 := bstep (se 1 (by rfl) ⟨965027, by rfl⟩ : syracuseStep 1286703 = 1930055) B1930055
theorem B7332443 : Blo 1285961 7332443 := bstep (se 1 (by rfl) ⟨5499332, by rfl⟩ : syracuseStep 7332443 = 10998665) B10998665
theorem B1287103 : Blo 1285961 1287103 := bstep (se 1 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 1287103 = 1930655) B1930655
theorem B125297603 : Blo 1285961 125297603 := bstep (se 1 (by rfl) ⟨93973202, by rfl⟩ : syracuseStep 125297603 = 187946405) B187946405
theorem B42288925 : Blo 1285961 42288925 := bstep (se 3 (by rfl) ⟨7929173, by rfl⟩ : syracuseStep 42288925 = 15858347) B15858347
theorem B2320609 : Blo 1285961 2320609 := bstep (se 2 (by rfl) ⟨870228, by rfl⟩ : syracuseStep 2320609 = 1740457) B1740457
theorem B2894201 : Blo 1285961 2894201 := bstep (se 2 (by rfl) ⟨1085325, by rfl⟩ : syracuseStep 2894201 = 2170651) B2170651
theorem B23792527 : Blo 1285961 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B53513567 : Blo 1285961 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B7933459 : Blo 1285961 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B4345487 : Blo 1285961 4345487 := bstep (se 1 (by rfl) ⟨3259115, by rfl⟩ : syracuseStep 4345487 = 6518231) B6518231
theorem B4345811 : Blo 1285961 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B6516935 : Blo 1285961 6516935 := bstep (se 1 (by rfl) ⟨4887701, by rfl⟩ : syracuseStep 6516935 = 9775403) B9775403
theorem B10432907 : Blo 1285961 10432907 := bstep (se 1 (by rfl) ⟨7824680, by rfl⟩ : syracuseStep 10432907 = 15649361) B15649361
theorem B1929959 : Blo 1285961 1929959 := bstep (se 1 (by rfl) ⟨1447469, by rfl⟩ : syracuseStep 1929959 = 2894939) B2894939
theorem B49443695 : Blo 1285961 49443695 := bstep (se 1 (by rfl) ⟨37082771, by rfl⟩ : syracuseStep 49443695 = 74165543) B74165543
theorem B3093481 : Blo 1285961 3093481 := bstep (se 2 (by rfl) ⟨1160055, by rfl⟩ : syracuseStep 3093481 = 2320111) B2320111
theorem B2897063 : Blo 1285961 2897063 := bstep (se 1 (by rfl) ⟨2172797, by rfl⟩ : syracuseStep 2897063 = 4345595) B4345595
theorem B9770543 : Blo 1285961 9770543 := bstep (se 1 (by rfl) ⟨7327907, by rfl⟩ : syracuseStep 9770543 = 14655815) B14655815
theorem B1930907 : Blo 1285961 1930907 := bstep (se 1 (by rfl) ⟨1448180, by rfl⟩ : syracuseStep 1930907 = 2896361) B2896361
theorem B17611343 : Blo 1285961 17611343 := bstep (se 1 (by rfl) ⟨13208507, by rfl⟩ : syracuseStep 17611343 = 26417015) B26417015
theorem B6953627 : Blo 1285961 6953627 := bstep (se 1 (by rfl) ⟨5215220, by rfl⟩ : syracuseStep 6953627 = 10430441) B10430441
theorem B50183117 : Blo 1285961 50183117 := bstep (se 3 (by rfl) ⟨9409334, by rfl⟩ : syracuseStep 50183117 = 18818669) B18818669
theorem B12377225 : Blo 1285961 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B3259703 : Blo 1285961 3259703 := bstep (se 1 (by rfl) ⟨2444777, by rfl⟩ : syracuseStep 3259703 = 4889555) B4889555
theorem B4341167 : Blo 1285961 4341167 := bstep (se 1 (by rfl) ⟨3255875, by rfl⟩ : syracuseStep 4341167 = 6511751) B6511751
theorem B2170415 : Blo 1285961 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B20086379 : Blo 1285961 20086379 := bstep (se 1 (by rfl) ⟨15064784, by rfl⟩ : syracuseStep 20086379 = 30129569) B30129569
theorem B1285979 : Blo 1285961 1285979 := bstep (se 1 (by rfl) ⟨964484, by rfl⟩ : syracuseStep 1285979 = 1928969) B1928969
theorem B36167629 : Blo 1285961 36167629 := bstep (se 3 (by rfl) ⟨6781430, by rfl⟩ : syracuseStep 36167629 = 13562861) B13562861
theorem B46964717 : Blo 1285961 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B6955271 : Blo 1285961 6955271 := bstep (se 1 (by rfl) ⟨5216453, by rfl⟩ : syracuseStep 6955271 = 10432907) B10432907
theorem B1286639 : Blo 1285961 1286639 := bstep (se 1 (by rfl) ⟨964979, by rfl⟩ : syracuseStep 1286639 = 1929959) B1929959
theorem B6513695 : Blo 1285961 6513695 := bstep (se 1 (by rfl) ⟨4885271, by rfl⟩ : syracuseStep 6513695 = 9770543) B9770543
theorem B1287271 : Blo 1285961 1287271 := bstep (se 1 (by rfl) ⟨965453, by rfl⟩ : syracuseStep 1287271 = 1930907) B1930907
theorem B11740895 : Blo 1285961 11740895 := bstep (se 1 (by rfl) ⟨8805671, by rfl⟩ : syracuseStep 11740895 = 17611343) B17611343
theorem B10577945 : Blo 1285961 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B8251483 : Blo 1285961 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B2173135 : Blo 1285961 2173135 := bstep (se 1 (by rfl) ⟨1629851, by rfl⟩ : syracuseStep 2173135 = 3259703) B3259703
theorem B2894111 : Blo 1285961 2894111 := bstep (se 1 (by rfl) ⟨2170583, by rfl⟩ : syracuseStep 2894111 = 4341167) B4341167
theorem B4344623 : Blo 1285961 4344623 := bstep (se 1 (by rfl) ⟨3258467, by rfl⟩ : syracuseStep 4344623 = 6516935) B6516935
theorem B31723369 : Blo 1285961 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B4124641 : Blo 1285961 4124641 := bstep (se 2 (by rfl) ⟨1546740, by rfl⟩ : syracuseStep 4124641 = 3093481) B3093481
theorem B1929467 : Blo 1285961 1929467 := bstep (se 1 (by rfl) ⟨1447100, by rfl⟩ : syracuseStep 1929467 = 2894201) B2894201
theorem B18543005 : Blo 1285961 18543005 := bstep (se 3 (by rfl) ⟨3476813, by rfl⟩ : syracuseStep 18543005 = 6953627) B6953627
theorem B1446943 : Blo 1285961 1446943 := bstep (se 1 (by rfl) ⟨1085207, by rfl⟩ : syracuseStep 1446943 = 2170415) B2170415
theorem B13390919 : Blo 1285961 13390919 := bstep (se 1 (by rfl) ⟨10043189, by rfl⟩ : syracuseStep 13390919 = 20086379) B20086379
theorem B2896991 : Blo 1285961 2896991 := bstep (se 1 (by rfl) ⟨2172743, by rfl⟩ : syracuseStep 2896991 = 4345487) B4345487
theorem B48223505 : Blo 1285961 48223505 := bstep (se 2 (by rfl) ⟨18083814, by rfl⟩ : syracuseStep 48223505 = 36167629) B36167629
theorem B2897207 : Blo 1285961 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B3094145 : Blo 1285961 3094145 := bstep (se 2 (by rfl) ⟨1160304, by rfl⟩ : syracuseStep 3094145 = 2320609) B2320609
theorem B4888295 : Blo 1285961 4888295 := bstep (se 1 (by rfl) ⟨3666221, by rfl⟩ : syracuseStep 4888295 = 7332443) B7332443
theorem B32962463 : Blo 1285961 32962463 := bstep (se 1 (by rfl) ⟨24721847, by rfl⟩ : syracuseStep 32962463 = 49443695) B49443695
theorem B83531735 : Blo 1285961 83531735 := bstep (se 1 (by rfl) ⟨62648801, by rfl⟩ : syracuseStep 83531735 = 125297603) B125297603
theorem B1931375 : Blo 1285961 1931375 := bstep (se 1 (by rfl) ⟨1448531, by rfl⟩ : syracuseStep 1931375 = 2897063) B2897063
theorem B33455411 : Blo 1285961 33455411 := bstep (se 1 (by rfl) ⟨25091558, by rfl⟩ : syracuseStep 33455411 = 50183117) B50183117
theorem B35675711 : Blo 1285961 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B56385233 : Blo 1285961 56385233 := bstep (se 2 (by rfl) ⟨21144462, by rfl⟩ : syracuseStep 56385233 = 42288925) B42288925
theorem B31309811 : Blo 1285961 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B11001977 : Blo 1285961 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B1286311 : Blo 1285961 1286311 := bstep (se 1 (by rfl) ⟨964733, by rfl⟩ : syracuseStep 1286311 = 1929467) B1929467
theorem B4636847 : Blo 1285961 4636847 := bstep (se 1 (by rfl) ⟨3477635, by rfl⟩ : syracuseStep 4636847 = 6955271) B6955271
theorem B12362003 : Blo 1285961 12362003 := bstep (se 1 (by rfl) ⟨9271502, by rfl⟩ : syracuseStep 12362003 = 18543005) B18543005
theorem B4342463 : Blo 1285961 4342463 := bstep (se 1 (by rfl) ⟨3256847, by rfl⟩ : syracuseStep 4342463 = 6513695) B6513695
theorem B1287583 : Blo 1285961 1287583 := bstep (se 1 (by rfl) ⟨965687, by rfl⟩ : syracuseStep 1287583 = 1931375) B1931375
theorem B23783807 : Blo 1285961 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B5499521 : Blo 1285961 5499521 := bstep (se 2 (by rfl) ⟨2062320, by rfl⟩ : syracuseStep 5499521 = 4124641) B4124641
theorem B32149003 : Blo 1285961 32149003 := bstep (se 1 (by rfl) ⟨24111752, by rfl⟩ : syracuseStep 32149003 = 48223505) B48223505
theorem B7827263 : Blo 1285961 7827263 := bstep (se 1 (by rfl) ⟨5870447, by rfl⟩ : syracuseStep 7827263 = 11740895) B11740895
theorem B21974975 : Blo 1285961 21974975 := bstep (se 1 (by rfl) ⟨16481231, by rfl⟩ : syracuseStep 21974975 = 32962463) B32962463
theorem B1929257 : Blo 1285961 1929257 := bstep (se 2 (by rfl) ⟨723471, by rfl⟩ : syracuseStep 1929257 = 1446943) B1446943
theorem B1929407 : Blo 1285961 1929407 := bstep (se 1 (by rfl) ⟨1447055, by rfl⟩ : syracuseStep 1929407 = 2894111) B2894111
theorem B2896415 : Blo 1285961 2896415 := bstep (se 1 (by rfl) ⟨2172311, by rfl⟩ : syracuseStep 2896415 = 4344623) B4344623
theorem B22303607 : Blo 1285961 22303607 := bstep (se 1 (by rfl) ⟨16727705, by rfl⟩ : syracuseStep 22303607 = 33455411) B33455411
theorem B20873207 : Blo 1285961 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B37590155 : Blo 1285961 37590155 := bstep (se 1 (by rfl) ⟨28192616, by rfl⟩ : syracuseStep 37590155 = 56385233) B56385233
theorem B2897513 : Blo 1285961 2897513 := bstep (se 2 (by rfl) ⟨1086567, by rfl⟩ : syracuseStep 2897513 = 2173135) B2173135
theorem B8927279 : Blo 1285961 8927279 := bstep (se 1 (by rfl) ⟨6695459, by rfl⟩ : syracuseStep 8927279 = 13390919) B13390919
theorem B1931327 : Blo 1285961 1931327 := bstep (se 1 (by rfl) ⟨1448495, by rfl⟩ : syracuseStep 1931327 = 2896991) B2896991
theorem B1931471 : Blo 1285961 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B2062763 : Blo 1285961 2062763 := bstep (se 1 (by rfl) ⟨1547072, by rfl⟩ : syracuseStep 2062763 = 3094145) B3094145
theorem B3258863 : Blo 1285961 3258863 := bstep (se 1 (by rfl) ⟨2444147, by rfl⟩ : syracuseStep 3258863 = 4888295) B4888295
theorem B55687823 : Blo 1285961 55687823 := bstep (se 1 (by rfl) ⟨41765867, by rfl⟩ : syracuseStep 55687823 = 83531735) B83531735
theorem B7051963 : Blo 1285961 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B676765205 : Blo 1285961 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B1286171 : Blo 1285961 1286171 := bstep (se 1 (by rfl) ⟨964628, by rfl⟩ : syracuseStep 1286171 = 1929257) B1929257
theorem B1286271 : Blo 1285961 1286271 := bstep (se 1 (by rfl) ⟨964703, by rfl⟩ : syracuseStep 1286271 = 1929407) B1929407
theorem B8241335 : Blo 1285961 8241335 := bstep (se 1 (by rfl) ⟨6181001, by rfl⟩ : syracuseStep 8241335 = 12362003) B12362003
theorem B25060103 : Blo 1285961 25060103 := bstep (se 1 (by rfl) ⟨18795077, by rfl⟩ : syracuseStep 25060103 = 37590155) B37590155
theorem B1287551 : Blo 1285961 1287551 := bstep (se 1 (by rfl) ⟨965663, by rfl⟩ : syracuseStep 1287551 = 1931327) B1931327
theorem B1287647 : Blo 1285961 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B2172575 : Blo 1285961 2172575 := bstep (se 1 (by rfl) ⟨1629431, by rfl⟩ : syracuseStep 2172575 = 3258863) B3258863
theorem B59476285 : Blo 1285961 59476285 := bstep (se 3 (by rfl) ⟨11151803, by rfl⟩ : syracuseStep 59476285 = 22303607) B22303607
theorem B451176803 : Blo 1285961 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B14649983 : Blo 1285961 14649983 := bstep (se 1 (by rfl) ⟨10987487, by rfl⟩ : syracuseStep 14649983 = 21974975) B21974975
theorem B7334651 : Blo 1285961 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B3091231 : Blo 1285961 3091231 := bstep (se 1 (by rfl) ⟨2318423, by rfl⟩ : syracuseStep 3091231 = 4636847) B4636847
theorem B2894975 : Blo 1285961 2894975 := bstep (se 1 (by rfl) ⟨2171231, by rfl⟩ : syracuseStep 2894975 = 4342463) B4342463
theorem B5951519 : Blo 1285961 5951519 := bstep (se 1 (by rfl) ⟨4463639, by rfl⟩ : syracuseStep 5951519 = 8927279) B8927279
theorem B15855871 : Blo 1285961 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B3666347 : Blo 1285961 3666347 := bstep (se 1 (by rfl) ⟨2749760, by rfl⟩ : syracuseStep 3666347 = 5499521) B5499521
theorem B42865337 : Blo 1285961 42865337 := bstep (se 2 (by rfl) ⟨16074501, by rfl⟩ : syracuseStep 42865337 = 32149003) B32149003
theorem B13915471 : Blo 1285961 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B1930943 : Blo 1285961 1930943 := bstep (se 1 (by rfl) ⟨1448207, by rfl⟩ : syracuseStep 1930943 = 2896415) B2896415
theorem B9402617 : Blo 1285961 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B1931675 : Blo 1285961 1931675 := bstep (se 1 (by rfl) ⟨1448756, by rfl⟩ : syracuseStep 1931675 = 2897513) B2897513
theorem B1375175 : Blo 1285961 1375175 := bstep (se 1 (by rfl) ⟨1031381, by rfl⟩ : syracuseStep 1375175 = 2062763) B2062763
theorem B37125215 : Blo 1285961 37125215 := bstep (se 1 (by rfl) ⟨27843911, by rfl⟩ : syracuseStep 37125215 = 55687823) B55687823
theorem B5218175 : Blo 1285961 5218175 := bstep (se 1 (by rfl) ⟨3913631, by rfl⟩ : syracuseStep 5218175 = 7827263) B7827263
theorem B4121641 : Blo 1285961 4121641 := bstep (se 2 (by rfl) ⟨1545615, by rfl⟩ : syracuseStep 4121641 = 3091231) B3091231
theorem B1287295 : Blo 1285961 1287295 := bstep (se 1 (by rfl) ⟨965471, by rfl⟩ : syracuseStep 1287295 = 1930943) B1930943
theorem B6268411 : Blo 1285961 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B1287783 : Blo 1285961 1287783 := bstep (se 1 (by rfl) ⟨965837, by rfl⟩ : syracuseStep 1287783 = 1931675) B1931675
theorem B9766655 : Blo 1285961 9766655 := bstep (se 1 (by rfl) ⟨7324991, by rfl⟩ : syracuseStep 9766655 = 14649983) B14649983
theorem B24750143 : Blo 1285961 24750143 := bstep (se 1 (by rfl) ⟨18562607, by rfl⟩ : syracuseStep 24750143 = 37125215) B37125215
theorem B3967679 : Blo 1285961 3967679 := bstep (se 1 (by rfl) ⟨2975759, by rfl⟩ : syracuseStep 3967679 = 5951519) B5951519
theorem B2444231 : Blo 1285961 2444231 := bstep (se 1 (by rfl) ⟨1833173, by rfl⟩ : syracuseStep 2444231 = 3666347) B3666347
theorem B28576891 : Blo 1285961 28576891 := bstep (se 1 (by rfl) ⟨21432668, by rfl⟩ : syracuseStep 28576891 = 42865337) B42865337
theorem B16706735 : Blo 1285961 16706735 := bstep (se 1 (by rfl) ⟨12530051, by rfl⟩ : syracuseStep 16706735 = 25060103) B25060103
theorem B317206853 : Blo 1285961 317206853 := bstep (se 4 (by rfl) ⟨29738142, by rfl⟩ : syracuseStep 317206853 = 59476285) B59476285
theorem B1929983 : Blo 1285961 1929983 := bstep (se 1 (by rfl) ⟨1447487, by rfl⟩ : syracuseStep 1929983 = 2894975) B2894975
theorem B3667133 : Blo 1285961 3667133 := bstep (se 3 (by rfl) ⟨687587, by rfl⟩ : syracuseStep 3667133 = 1375175) B1375175
theorem B3478783 : Blo 1285961 3478783 := bstep (se 1 (by rfl) ⟨2609087, by rfl⟩ : syracuseStep 3478783 = 5218175) B5218175
theorem B5494223 : Blo 1285961 5494223 := bstep (se 1 (by rfl) ⟨4120667, by rfl⟩ : syracuseStep 5494223 = 8241335) B8241335
theorem B21141161 : Blo 1285961 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B1448383 : Blo 1285961 1448383 := bstep (se 1 (by rfl) ⟨1086287, by rfl⟩ : syracuseStep 1448383 = 2172575) B2172575
theorem B300784535 : Blo 1285961 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B18553961 : Blo 1285961 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B4889767 : Blo 1285961 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B1286655 : Blo 1285961 1286655 := bstep (se 1 (by rfl) ⟨964991, by rfl⟩ : syracuseStep 1286655 = 1929983) B1929983
theorem B3662815 : Blo 1285961 3662815 := bstep (se 1 (by rfl) ⟨2747111, by rfl⟩ : syracuseStep 3662815 = 5494223) B5494223
theorem B16500095 : Blo 1285961 16500095 := bstep (se 1 (by rfl) ⟨12375071, by rfl⟩ : syracuseStep 16500095 = 24750143) B24750143
theorem B4638377 : Blo 1285961 4638377 := bstep (se 2 (by rfl) ⟨1739391, by rfl⟩ : syracuseStep 4638377 = 3478783) B3478783
theorem B211471235 : Blo 1285961 211471235 := bstep (se 1 (by rfl) ⟨158603426, by rfl⟩ : syracuseStep 211471235 = 317206853) B317206853
theorem B2444755 : Blo 1285961 2444755 := bstep (se 1 (by rfl) ⟨1833566, by rfl⟩ : syracuseStep 2444755 = 3667133) B3667133
theorem B14094107 : Blo 1285961 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B11137823 : Blo 1285961 11137823 := bstep (se 1 (by rfl) ⟨8353367, by rfl⟩ : syracuseStep 11137823 = 16706735) B16706735
theorem B1931177 : Blo 1285961 1931177 := bstep (se 2 (by rfl) ⟨724191, by rfl⟩ : syracuseStep 1931177 = 1448383) B1448383
theorem B152410085 : Blo 1285961 152410085 := bstep (se 4 (by rfl) ⟨14288445, by rfl⟩ : syracuseStep 152410085 = 28576891) B28576891
theorem B6511103 : Blo 1285961 6511103 := bstep (se 1 (by rfl) ⟨4883327, by rfl⟩ : syracuseStep 6511103 = 9766655) B9766655
theorem B5495521 : Blo 1285961 5495521 := bstep (se 2 (by rfl) ⟨2060820, by rfl⟩ : syracuseStep 5495521 = 4121641) B4121641
theorem B6519689 : Blo 1285961 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B2645119 : Blo 1285961 2645119 := bstep (se 1 (by rfl) ⟨1983839, by rfl⟩ : syracuseStep 2645119 = 3967679) B3967679
theorem B200523023 : Blo 1285961 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B1629487 : Blo 1285961 1629487 := bstep (se 1 (by rfl) ⟨1222115, by rfl⟩ : syracuseStep 1629487 = 2444231) B2444231
theorem B12369307 : Blo 1285961 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B33431525 : Blo 1285961 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B14107301 : Blo 1285961 14107301 := bstep (se 4 (by rfl) ⟨1322559, by rfl⟩ : syracuseStep 14107301 = 2645119) B2645119
theorem B1287451 : Blo 1285961 1287451 := bstep (se 1 (by rfl) ⟨965588, by rfl⟩ : syracuseStep 1287451 = 1931177) B1931177
theorem B4883753 : Blo 1285961 4883753 := bstep (se 2 (by rfl) ⟨1831407, by rfl⟩ : syracuseStep 4883753 = 3662815) B3662815
theorem B101606723 : Blo 1285961 101606723 := bstep (se 1 (by rfl) ⟨76205042, by rfl⟩ : syracuseStep 101606723 = 152410085) B152410085
theorem B2172649 : Blo 1285961 2172649 := bstep (se 2 (by rfl) ⟨814743, by rfl⟩ : syracuseStep 2172649 = 1629487) B1629487
theorem B16492409 : Blo 1285961 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B7425215 : Blo 1285961 7425215 := bstep (se 1 (by rfl) ⟨5568911, by rfl⟩ : syracuseStep 7425215 = 11137823) B11137823
theorem B7327361 : Blo 1285961 7327361 := bstep (se 2 (by rfl) ⟨2747760, by rfl⟩ : syracuseStep 7327361 = 5495521) B5495521
theorem B3092251 : Blo 1285961 3092251 := bstep (se 1 (by rfl) ⟨2319188, by rfl⟩ : syracuseStep 3092251 = 4638377) B4638377
theorem B140980823 : Blo 1285961 140980823 := bstep (se 1 (by rfl) ⟨105735617, by rfl⟩ : syracuseStep 140980823 = 211471235) B211471235
theorem B4346459 : Blo 1285961 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B133682015 : Blo 1285961 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B22287683 : Blo 1285961 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B11000063 : Blo 1285961 11000063 := bstep (se 1 (by rfl) ⟨8250047, by rfl⟩ : syracuseStep 11000063 = 16500095) B16500095
theorem B4340735 : Blo 1285961 4340735 := bstep (se 1 (by rfl) ⟨3255551, by rfl⟩ : syracuseStep 4340735 = 6511103) B6511103
theorem B3259673 : Blo 1285961 3259673 := bstep (se 2 (by rfl) ⟨1222377, by rfl⟩ : syracuseStep 3259673 = 2444755) B2444755
theorem B9396071 : Blo 1285961 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B93987215 : Blo 1285961 93987215 := bstep (se 1 (by rfl) ⟨70490411, by rfl⟩ : syracuseStep 93987215 = 140980823) B140980823
theorem B9404867 : Blo 1285961 9404867 := bstep (se 1 (by rfl) ⟨7053650, by rfl⟩ : syracuseStep 9404867 = 14107301) B14107301
theorem B89121343 : Blo 1285961 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B59433821 : Blo 1285961 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B10994939 : Blo 1285961 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B7333375 : Blo 1285961 7333375 := bstep (se 1 (by rfl) ⟨5500031, by rfl⟩ : syracuseStep 7333375 = 11000063) B11000063
theorem B2893823 : Blo 1285961 2893823 := bstep (se 1 (by rfl) ⟨2170367, by rfl⟩ : syracuseStep 2893823 = 4340735) B4340735
theorem B4950143 : Blo 1285961 4950143 := bstep (se 1 (by rfl) ⟨3712607, by rfl⟩ : syracuseStep 4950143 = 7425215) B7425215
theorem B2173115 : Blo 1285961 2173115 := bstep (se 1 (by rfl) ⟨1629836, by rfl⟩ : syracuseStep 2173115 = 3259673) B3259673
theorem B4123001 : Blo 1285961 4123001 := bstep (se 2 (by rfl) ⟨1546125, by rfl⟩ : syracuseStep 4123001 = 3092251) B3092251
theorem B4884907 : Blo 1285961 4884907 := bstep (se 1 (by rfl) ⟨3663680, by rfl⟩ : syracuseStep 4884907 = 7327361) B7327361
theorem B3255835 : Blo 1285961 3255835 := bstep (se 1 (by rfl) ⟨2441876, by rfl⟩ : syracuseStep 3255835 = 4883753) B4883753
theorem B2896865 : Blo 1285961 2896865 := bstep (se 2 (by rfl) ⟨1086324, by rfl⟩ : syracuseStep 2896865 = 2172649) B2172649
theorem B6264047 : Blo 1285961 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B2897639 : Blo 1285961 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B67737815 : Blo 1285961 67737815 := bstep (se 1 (by rfl) ⟨50803361, by rfl⟩ : syracuseStep 67737815 = 101606723) B101606723
theorem B6513209 : Blo 1285961 6513209 := bstep (se 2 (by rfl) ⟨2442453, by rfl⟩ : syracuseStep 6513209 = 4884907) B4884907
theorem B118828457 : Blo 1285961 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B25079645 : Blo 1285961 25079645 := bstep (se 3 (by rfl) ⟨4702433, by rfl⟩ : syracuseStep 25079645 = 9404867) B9404867
theorem B1929215 : Blo 1285961 1929215 := bstep (se 1 (by rfl) ⟨1446911, by rfl⟩ : syracuseStep 1929215 = 2893823) B2893823
theorem B45158543 : Blo 1285961 45158543 := bstep (se 1 (by rfl) ⟨33868907, by rfl⟩ : syracuseStep 45158543 = 67737815) B67737815
theorem B2748667 : Blo 1285961 2748667 := bstep (se 1 (by rfl) ⟨2061500, by rfl⟩ : syracuseStep 2748667 = 4123001) B4123001
theorem B9777833 : Blo 1285961 9777833 := bstep (se 2 (by rfl) ⟨3666687, by rfl⟩ : syracuseStep 9777833 = 7333375) B7333375
theorem B62658143 : Blo 1285961 62658143 := bstep (se 1 (by rfl) ⟨46993607, by rfl⟩ : syracuseStep 62658143 = 93987215) B93987215
theorem B39622547 : Blo 1285961 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B1931243 : Blo 1285961 1931243 := bstep (se 1 (by rfl) ⟨1448432, by rfl⟩ : syracuseStep 1931243 = 2896865) B2896865
theorem B4176031 : Blo 1285961 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B7329959 : Blo 1285961 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B1931759 : Blo 1285961 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B3300095 : Blo 1285961 3300095 := bstep (se 1 (by rfl) ⟨2475071, by rfl⟩ : syracuseStep 3300095 = 4950143) B4950143
theorem B1448743 : Blo 1285961 1448743 := bstep (se 1 (by rfl) ⟨1086557, by rfl⟩ : syracuseStep 1448743 = 2173115) B2173115
theorem B4341113 : Blo 1285961 4341113 := bstep (se 2 (by rfl) ⟨1627917, by rfl⟩ : syracuseStep 4341113 = 3255835) B3255835
theorem B30105695 : Blo 1285961 30105695 := bstep (se 1 (by rfl) ⟨22579271, by rfl⟩ : syracuseStep 30105695 = 45158543) B45158543
theorem B4342139 : Blo 1285961 4342139 := bstep (se 1 (by rfl) ⟨3256604, by rfl⟩ : syracuseStep 4342139 = 6513209) B6513209
theorem B41772095 : Blo 1285961 41772095 := bstep (se 1 (by rfl) ⟨31329071, by rfl⟩ : syracuseStep 41772095 = 62658143) B62658143
theorem B1287495 : Blo 1285961 1287495 := bstep (se 1 (by rfl) ⟨965621, by rfl⟩ : syracuseStep 1287495 = 1931243) B1931243
theorem B1287839 : Blo 1285961 1287839 := bstep (se 1 (by rfl) ⟨965879, by rfl⟩ : syracuseStep 1287839 = 1931759) B1931759
theorem B2894075 : Blo 1285961 2894075 := bstep (se 1 (by rfl) ⟨2170556, by rfl⟩ : syracuseStep 2894075 = 4341113) B4341113
theorem B79218971 : Blo 1285961 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B3664889 : Blo 1285961 3664889 := bstep (se 2 (by rfl) ⟨1374333, by rfl⟩ : syracuseStep 3664889 = 2748667) B2748667
theorem B26415031 : Blo 1285961 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B4886639 : Blo 1285961 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B2200063 : Blo 1285961 2200063 := bstep (se 1 (by rfl) ⟨1650047, by rfl⟩ : syracuseStep 2200063 = 3300095) B3300095
theorem B5568041 : Blo 1285961 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B6518555 : Blo 1285961 6518555 := bstep (se 1 (by rfl) ⟨4888916, by rfl⟩ : syracuseStep 6518555 = 9777833) B9777833
theorem B1931657 : Blo 1285961 1931657 := bstep (se 2 (by rfl) ⟨724371, by rfl⟩ : syracuseStep 1931657 = 1448743) B1448743
theorem B66879053 : Blo 1285961 66879053 := bstep (se 3 (by rfl) ⟨12539822, by rfl⟩ : syracuseStep 66879053 = 25079645) B25079645
theorem B1286143 : Blo 1285961 1286143 := bstep (se 1 (by rfl) ⟨964607, by rfl⟩ : syracuseStep 1286143 = 1929215) B1929215
theorem B80281853 : Blo 1285961 80281853 := bstep (se 3 (by rfl) ⟨15052847, by rfl⟩ : syracuseStep 80281853 = 30105695) B30105695
theorem B2933417 : Blo 1285961 2933417 := bstep (se 2 (by rfl) ⟨1100031, by rfl⟩ : syracuseStep 2933417 = 2200063) B2200063
theorem B1287771 : Blo 1285961 1287771 := bstep (se 1 (by rfl) ⟨965828, by rfl⟩ : syracuseStep 1287771 = 1931657) B1931657
theorem B2443259 : Blo 1285961 2443259 := bstep (se 1 (by rfl) ⟨1832444, by rfl⟩ : syracuseStep 2443259 = 3664889) B3664889
theorem B35220041 : Blo 1285961 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B2894759 : Blo 1285961 2894759 := bstep (se 1 (by rfl) ⟨2171069, by rfl⟩ : syracuseStep 2894759 = 4342139) B4342139
theorem B27848063 : Blo 1285961 27848063 := bstep (se 1 (by rfl) ⟨20886047, by rfl⟩ : syracuseStep 27848063 = 41772095) B41772095
theorem B4345703 : Blo 1285961 4345703 := bstep (se 1 (by rfl) ⟨3259277, by rfl⟩ : syracuseStep 4345703 = 6518555) B6518555
theorem B14848109 : Blo 1285961 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B1929383 : Blo 1285961 1929383 := bstep (se 1 (by rfl) ⟨1447037, by rfl⟩ : syracuseStep 1929383 = 2894075) B2894075
theorem B44586035 : Blo 1285961 44586035 := bstep (se 1 (by rfl) ⟨33439526, by rfl⟩ : syracuseStep 44586035 = 66879053) B66879053
theorem B3257759 : Blo 1285961 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B52812647 : Blo 1285961 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B1286255 : Blo 1285961 1286255 := bstep (se 1 (by rfl) ⟨964691, by rfl⟩ : syracuseStep 1286255 = 1929383) B1929383
theorem B2171839 : Blo 1285961 2171839 := bstep (se 1 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 2171839 = 3257759) B3257759
theorem B23480027 : Blo 1285961 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B18565375 : Blo 1285961 18565375 := bstep (se 1 (by rfl) ⟨13924031, by rfl⟩ : syracuseStep 18565375 = 27848063) B27848063
theorem B9898739 : Blo 1285961 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B53521235 : Blo 1285961 53521235 := bstep (se 1 (by rfl) ⟨40140926, by rfl⟩ : syracuseStep 53521235 = 80281853) B80281853
theorem B29724023 : Blo 1285961 29724023 := bstep (se 1 (by rfl) ⟨22293017, by rfl⟩ : syracuseStep 29724023 = 44586035) B44586035
theorem B1929839 : Blo 1285961 1929839 := bstep (se 1 (by rfl) ⟨1447379, by rfl⟩ : syracuseStep 1929839 = 2894759) B2894759
theorem B2897135 : Blo 1285961 2897135 := bstep (se 1 (by rfl) ⟨2172851, by rfl⟩ : syracuseStep 2897135 = 4345703) B4345703
theorem B1955611 : Blo 1285961 1955611 := bstep (se 1 (by rfl) ⟨1466708, by rfl⟩ : syracuseStep 1955611 = 2933417) B2933417
theorem B1628839 : Blo 1285961 1628839 := bstep (se 1 (by rfl) ⟨1221629, by rfl⟩ : syracuseStep 1628839 = 2443259) B2443259
theorem B35208431 : Blo 1285961 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B1286559 : Blo 1285961 1286559 := bstep (se 1 (by rfl) ⟨964919, by rfl⟩ : syracuseStep 1286559 = 1929839) B1929839
theorem B2171785 : Blo 1285961 2171785 := bstep (se 2 (by rfl) ⟨814419, by rfl⟩ : syracuseStep 2171785 = 1628839) B1628839
theorem B23472287 : Blo 1285961 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B2607481 : Blo 1285961 2607481 := bstep (se 2 (by rfl) ⟨977805, by rfl⟩ : syracuseStep 2607481 = 1955611) B1955611
theorem B2895785 : Blo 1285961 2895785 := bstep (se 2 (by rfl) ⟨1085919, by rfl⟩ : syracuseStep 2895785 = 2171839) B2171839
theorem B6599159 : Blo 1285961 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B35680823 : Blo 1285961 35680823 := bstep (se 1 (by rfl) ⟨26760617, by rfl⟩ : syracuseStep 35680823 = 53521235) B53521235
theorem B24753833 : Blo 1285961 24753833 := bstep (se 2 (by rfl) ⟨9282687, by rfl⟩ : syracuseStep 24753833 = 18565375) B18565375
theorem B1931423 : Blo 1285961 1931423 := bstep (se 1 (by rfl) ⟨1448567, by rfl⟩ : syracuseStep 1931423 = 2897135) B2897135
theorem B15653351 : Blo 1285961 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B19816015 : Blo 1285961 19816015 := bstep (se 1 (by rfl) ⟨14862011, by rfl⟩ : syracuseStep 19816015 = 29724023) B29724023
theorem B4399439 : Blo 1285961 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B15648191 : Blo 1285961 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B1287615 : Blo 1285961 1287615 := bstep (se 1 (by rfl) ⟨965711, by rfl⟩ : syracuseStep 1287615 = 1931423) B1931423
theorem B26421353 : Blo 1285961 26421353 := bstep (se 2 (by rfl) ⟨9908007, by rfl⟩ : syracuseStep 26421353 = 19816015) B19816015
theorem B16502555 : Blo 1285961 16502555 := bstep (se 1 (by rfl) ⟨12376916, by rfl⟩ : syracuseStep 16502555 = 24753833) B24753833
theorem B2895713 : Blo 1285961 2895713 := bstep (se 2 (by rfl) ⟨1085892, by rfl⟩ : syracuseStep 2895713 = 2171785) B2171785
theorem B13906565 : Blo 1285961 13906565 := bstep (se 4 (by rfl) ⟨1303740, by rfl⟩ : syracuseStep 13906565 = 2607481) B2607481
theorem B1930523 : Blo 1285961 1930523 := bstep (se 1 (by rfl) ⟨1447892, by rfl⟩ : syracuseStep 1930523 = 2895785) B2895785
theorem B23787215 : Blo 1285961 23787215 := bstep (se 1 (by rfl) ⟨17840411, by rfl⟩ : syracuseStep 23787215 = 35680823) B35680823
theorem B10435567 : Blo 1285961 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B1287015 : Blo 1285961 1287015 := bstep (se 1 (by rfl) ⟨965261, by rfl⟩ : syracuseStep 1287015 = 1930523) B1930523
theorem B17614235 : Blo 1285961 17614235 := bstep (se 1 (by rfl) ⟨13210676, by rfl⟩ : syracuseStep 17614235 = 26421353) B26421353
theorem B46927349 : Blo 1285961 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B10432127 : Blo 1285961 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B13914089 : Blo 1285961 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B1930475 : Blo 1285961 1930475 := bstep (se 1 (by rfl) ⟨1447856, by rfl⟩ : syracuseStep 1930475 = 2895713) B2895713
theorem B9271043 : Blo 1285961 9271043 := bstep (se 1 (by rfl) ⟨6953282, by rfl⟩ : syracuseStep 9271043 = 13906565) B13906565
theorem B15858143 : Blo 1285961 15858143 := bstep (se 1 (by rfl) ⟨11893607, by rfl⟩ : syracuseStep 15858143 = 23787215) B23787215
theorem B11001703 : Blo 1285961 11001703 := bstep (se 1 (by rfl) ⟨8251277, by rfl⟩ : syracuseStep 11001703 = 16502555) B16502555
theorem B1286983 : Blo 1285961 1286983 := bstep (se 1 (by rfl) ⟨965237, by rfl⟩ : syracuseStep 1286983 = 1930475) B1930475
theorem B9276059 : Blo 1285961 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B11742823 : Blo 1285961 11742823 := bstep (se 1 (by rfl) ⟨8807117, by rfl⟩ : syracuseStep 11742823 = 17614235) B17614235
theorem B6180695 : Blo 1285961 6180695 := bstep (se 1 (by rfl) ⟨4635521, by rfl⟩ : syracuseStep 6180695 = 9271043) B9271043
theorem B10572095 : Blo 1285961 10572095 := bstep (se 1 (by rfl) ⟨7929071, by rfl⟩ : syracuseStep 10572095 = 15858143) B15858143
theorem B14668937 : Blo 1285961 14668937 := bstep (se 2 (by rfl) ⟨5500851, by rfl⟩ : syracuseStep 14668937 = 11001703) B11001703
theorem B31284899 : Blo 1285961 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B6954751 : Blo 1285961 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B62628389 : Blo 1285961 62628389 := bstep (se 4 (by rfl) ⟨5871411, by rfl⟩ : syracuseStep 62628389 = 11742823) B11742823
theorem B7048063 : Blo 1285961 7048063 := bstep (se 1 (by rfl) ⟨5286047, by rfl⟩ : syracuseStep 7048063 = 10572095) B10572095
theorem B9779291 : Blo 1285961 9779291 := bstep (se 1 (by rfl) ⟨7334468, by rfl⟩ : syracuseStep 9779291 = 14668937) B14668937
theorem B6184039 : Blo 1285961 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B9273001 : Blo 1285961 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B20856599 : Blo 1285961 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B4120463 : Blo 1285961 4120463 := bstep (se 1 (by rfl) ⟨3090347, by rfl⟩ : syracuseStep 4120463 = 6180695) B6180695
theorem B9397417 : Blo 1285961 9397417 := bstep (se 2 (by rfl) ⟨3524031, by rfl⟩ : syracuseStep 9397417 = 7048063) B7048063
theorem B12364001 : Blo 1285961 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B13904399 : Blo 1285961 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B2746975 : Blo 1285961 2746975 := bstep (se 1 (by rfl) ⟨2060231, by rfl⟩ : syracuseStep 2746975 = 4120463) B4120463
theorem B8245385 : Blo 1285961 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B41752259 : Blo 1285961 41752259 := bstep (se 1 (by rfl) ⟨31314194, by rfl⟩ : syracuseStep 41752259 = 62628389) B62628389
theorem B6519527 : Blo 1285961 6519527 := bstep (se 1 (by rfl) ⟨4889645, by rfl⟩ : syracuseStep 6519527 = 9779291) B9779291
theorem B5496923 : Blo 1285961 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B3662633 : Blo 1285961 3662633 := bstep (se 2 (by rfl) ⟨1373487, by rfl⟩ : syracuseStep 3662633 = 2746975) B2746975
theorem B37078397 : Blo 1285961 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B8242667 : Blo 1285961 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B12529889 : Blo 1285961 12529889 := bstep (se 2 (by rfl) ⟨4698708, by rfl⟩ : syracuseStep 12529889 = 9397417) B9397417
theorem B4346351 : Blo 1285961 4346351 := bstep (se 1 (by rfl) ⟨3259763, by rfl⟩ : syracuseStep 4346351 = 6519527) B6519527
theorem B27834839 : Blo 1285961 27834839 := bstep (se 1 (by rfl) ⟨20876129, by rfl⟩ : syracuseStep 27834839 = 41752259) B41752259
theorem B2441755 : Blo 1285961 2441755 := bstep (se 1 (by rfl) ⟨1831316, by rfl⟩ : syracuseStep 2441755 = 3662633) B3662633
theorem B18556559 : Blo 1285961 18556559 := bstep (se 1 (by rfl) ⟨13917419, by rfl⟩ : syracuseStep 18556559 = 27834839) B27834839
theorem B3664615 : Blo 1285961 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B24718931 : Blo 1285961 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B8353259 : Blo 1285961 8353259 := bstep (se 1 (by rfl) ⟨6264944, by rfl⟩ : syracuseStep 8353259 = 12529889) B12529889
theorem B2897567 : Blo 1285961 2897567 := bstep (se 1 (by rfl) ⟨2173175, by rfl⟩ : syracuseStep 2897567 = 4346351) B4346351
theorem B5495111 : Blo 1285961 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B12371039 : Blo 1285961 12371039 := bstep (se 1 (by rfl) ⟨9278279, by rfl⟩ : syracuseStep 12371039 = 18556559) B18556559
theorem B3663407 : Blo 1285961 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B3255673 : Blo 1285961 3255673 := bstep (se 2 (by rfl) ⟨1220877, by rfl⟩ : syracuseStep 3255673 = 2441755) B2441755
theorem B4886153 : Blo 1285961 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B16479287 : Blo 1285961 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B5568839 : Blo 1285961 5568839 := bstep (se 1 (by rfl) ⟨4176629, by rfl⟩ : syracuseStep 5568839 = 8353259) B8353259
theorem B1931711 : Blo 1285961 1931711 := bstep (se 1 (by rfl) ⟨1448783, by rfl⟩ : syracuseStep 1931711 = 2897567) B2897567
theorem B10986191 : Blo 1285961 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B3712559 : Blo 1285961 3712559 := bstep (se 1 (by rfl) ⟨2784419, by rfl⟩ : syracuseStep 3712559 = 5568839) B5568839
theorem B1287807 : Blo 1285961 1287807 := bstep (se 1 (by rfl) ⟨965855, by rfl⟩ : syracuseStep 1287807 = 1931711) B1931711
theorem B9769085 : Blo 1285961 9769085 := bstep (se 3 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 9769085 = 3663407) B3663407
theorem B3257435 : Blo 1285961 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B8247359 : Blo 1285961 8247359 := bstep (se 1 (by rfl) ⟨6185519, by rfl⟩ : syracuseStep 8247359 = 12371039) B12371039
theorem B4340897 : Blo 1285961 4340897 := bstep (se 2 (by rfl) ⟨1627836, by rfl⟩ : syracuseStep 4340897 = 3255673) B3255673
theorem B6512723 : Blo 1285961 6512723 := bstep (se 1 (by rfl) ⟨4884542, by rfl⟩ : syracuseStep 6512723 = 9769085) B9769085
theorem B7324127 : Blo 1285961 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B2171623 : Blo 1285961 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B5498239 : Blo 1285961 5498239 := bstep (se 1 (by rfl) ⟨4123679, by rfl⟩ : syracuseStep 5498239 = 8247359) B8247359
theorem B2893931 : Blo 1285961 2893931 := bstep (se 1 (by rfl) ⟨2170448, by rfl⟩ : syracuseStep 2893931 = 4340897) B4340897
theorem B9900157 : Blo 1285961 9900157 := bstep (se 3 (by rfl) ⟨1856279, by rfl⟩ : syracuseStep 9900157 = 3712559) B3712559
theorem B4341815 : Blo 1285961 4341815 := bstep (se 1 (by rfl) ⟨3256361, by rfl⟩ : syracuseStep 4341815 = 6512723) B6512723
theorem B4882751 : Blo 1285961 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B13200209 : Blo 1285961 13200209 := bstep (se 2 (by rfl) ⟨4950078, by rfl⟩ : syracuseStep 13200209 = 9900157) B9900157
theorem B2895497 : Blo 1285961 2895497 := bstep (se 2 (by rfl) ⟨1085811, by rfl⟩ : syracuseStep 2895497 = 2171623) B2171623
theorem B1929287 : Blo 1285961 1929287 := bstep (se 1 (by rfl) ⟨1446965, by rfl⟩ : syracuseStep 1929287 = 2893931) B2893931
theorem B7330985 : Blo 1285961 7330985 := bstep (se 2 (by rfl) ⟨2749119, by rfl⟩ : syracuseStep 7330985 = 5498239) B5498239
theorem B1286191 : Blo 1285961 1286191 := bstep (se 1 (by rfl) ⟨964643, by rfl⟩ : syracuseStep 1286191 = 1929287) B1929287
theorem B8800139 : Blo 1285961 8800139 := bstep (se 1 (by rfl) ⟨6600104, by rfl⟩ : syracuseStep 8800139 = 13200209) B13200209
theorem B2894543 : Blo 1285961 2894543 := bstep (se 1 (by rfl) ⟨2170907, by rfl⟩ : syracuseStep 2894543 = 4341815) B4341815
theorem B3255167 : Blo 1285961 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B4887323 : Blo 1285961 4887323 := bstep (se 1 (by rfl) ⟨3665492, by rfl⟩ : syracuseStep 4887323 = 7330985) B7330985
theorem B1930331 : Blo 1285961 1930331 := bstep (se 1 (by rfl) ⟨1447748, by rfl⟩ : syracuseStep 1930331 = 2895497) B2895497
theorem B1286887 : Blo 1285961 1286887 := bstep (se 1 (by rfl) ⟨965165, by rfl⟩ : syracuseStep 1286887 = 1930331) B1930331
theorem B5866759 : Blo 1285961 5866759 := bstep (se 1 (by rfl) ⟨4400069, by rfl⟩ : syracuseStep 5866759 = 8800139) B8800139
theorem B1929695 : Blo 1285961 1929695 := bstep (se 1 (by rfl) ⟨1447271, by rfl⟩ : syracuseStep 1929695 = 2894543) B2894543
theorem B3258215 : Blo 1285961 3258215 := bstep (se 1 (by rfl) ⟨2443661, by rfl⟩ : syracuseStep 3258215 = 4887323) B4887323
theorem B2170111 : Blo 1285961 2170111 := bstep (se 1 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 2170111 = 3255167) B3255167
theorem B1286463 : Blo 1285961 1286463 := bstep (se 1 (by rfl) ⟨964847, by rfl⟩ : syracuseStep 1286463 = 1929695) B1929695
theorem B2172143 : Blo 1285961 2172143 := bstep (se 1 (by rfl) ⟨1629107, by rfl⟩ : syracuseStep 2172143 = 3258215) B3258215
theorem B2893481 : Blo 1285961 2893481 := bstep (se 2 (by rfl) ⟨1085055, by rfl⟩ : syracuseStep 2893481 = 2170111) B2170111
theorem B7822345 : Blo 1285961 7822345 := bstep (se 2 (by rfl) ⟨2933379, by rfl⟩ : syracuseStep 7822345 = 5866759) B5866759
theorem B10429793 : Blo 1285961 10429793 := bstep (se 2 (by rfl) ⟨3911172, by rfl⟩ : syracuseStep 10429793 = 7822345) B7822345
theorem B1928987 : Blo 1285961 1928987 := bstep (se 1 (by rfl) ⟨1446740, by rfl⟩ : syracuseStep 1928987 = 2893481) B2893481
theorem B1448095 : Blo 1285961 1448095 := bstep (se 1 (by rfl) ⟨1086071, by rfl⟩ : syracuseStep 1448095 = 2172143) B2172143
theorem B1930793 : Blo 1285961 1930793 := bstep (se 2 (by rfl) ⟨724047, by rfl⟩ : syracuseStep 1930793 = 1448095) B1448095
theorem B6953195 : Blo 1285961 6953195 := bstep (se 1 (by rfl) ⟨5214896, by rfl⟩ : syracuseStep 6953195 = 10429793) B10429793
theorem B1285991 : Blo 1285961 1285991 := bstep (se 1 (by rfl) ⟨964493, by rfl⟩ : syracuseStep 1285991 = 1928987) B1928987
theorem B1287195 : Blo 1285961 1287195 := bstep (se 1 (by rfl) ⟨965396, by rfl⟩ : syracuseStep 1287195 = 1930793) B1930793
theorem B4635463 : Blo 1285961 4635463 := bstep (se 1 (by rfl) ⟨3476597, by rfl⟩ : syracuseStep 4635463 = 6953195) B6953195
theorem B6180617 : Blo 1285961 6180617 := bstep (se 2 (by rfl) ⟨2317731, by rfl⟩ : syracuseStep 6180617 = 4635463) B4635463
theorem B4120411 : Blo 1285961 4120411 := bstep (se 1 (by rfl) ⟨3090308, by rfl⟩ : syracuseStep 4120411 = 6180617) B6180617
theorem B5493881 : Blo 1285961 5493881 := bstep (se 2 (by rfl) ⟨2060205, by rfl⟩ : syracuseStep 5493881 = 4120411) B4120411
theorem B3662587 : Blo 1285961 3662587 := bstep (se 1 (by rfl) ⟨2746940, by rfl⟩ : syracuseStep 3662587 = 5493881) B5493881
theorem B4883449 : Blo 1285961 4883449 := bstep (se 2 (by rfl) ⟨1831293, by rfl⟩ : syracuseStep 4883449 = 3662587) B3662587
theorem B6511265 : Blo 1285961 6511265 := bstep (se 2 (by rfl) ⟨2441724, by rfl⟩ : syracuseStep 6511265 = 4883449) B4883449
theorem B4340843 : Blo 1285961 4340843 := bstep (se 1 (by rfl) ⟨3255632, by rfl⟩ : syracuseStep 4340843 = 6511265) B6511265
theorem B2893895 : Blo 1285961 2893895 := bstep (se 1 (by rfl) ⟨2170421, by rfl⟩ : syracuseStep 2893895 = 4340843) B4340843
theorem B1929263 : Blo 1285961 1929263 := bstep (se 1 (by rfl) ⟨1446947, by rfl⟩ : syracuseStep 1929263 = 2893895) B2893895
theorem B1286175 : Blo 1285961 1286175 := bstep (se 1 (by rfl) ⟨964631, by rfl⟩ : syracuseStep 1286175 = 1929263) B1929263

theorem C0 (j : ℕ) (h1 : 321490 ≤ j) (h2 : j ≤ 321989) : Blo 1285961 (4 * j + 3) := by
  interval_cases j
  · exact B1285963
  · exact B1285967
  · exact B1285971
  · exact B1285975
  · exact B1285979
  · exact B1285983
  · exact B1285987
  · exact B1285991
  · exact B1285995
  · exact B1285999
  · exact B1286003
  · exact B1286007
  · exact B1286011
  · exact B1286015
  · exact B1286019
  · exact B1286023
  · exact B1286027
  · exact B1286031
  · exact B1286035
  · exact B1286039
  · exact B1286043
  · exact B1286047
  · exact B1286051
  · exact B1286055
  · exact B1286059
  · exact B1286063
  · exact B1286067
  · exact B1286071
  · exact B1286075
  · exact B1286079
  · exact B1286083
  · exact B1286087
  · exact B1286091
  · exact B1286095
  · exact B1286099
  · exact B1286103
  · exact B1286107
  · exact B1286111
  · exact B1286115
  · exact B1286119
  · exact B1286123
  · exact B1286127
  · exact B1286131
  · exact B1286135
  · exact B1286139
  · exact B1286143
  · exact B1286147
  · exact B1286151
  · exact B1286155
  · exact B1286159
  · exact B1286163
  · exact B1286167
  · exact B1286171
  · exact B1286175
  · exact B1286179
  · exact B1286183
  · exact B1286187
  · exact B1286191
  · exact B1286195
  · exact B1286199
  · exact B1286203
  · exact B1286207
  · exact B1286211
  · exact B1286215
  · exact B1286219
  · exact B1286223
  · exact B1286227
  · exact B1286231
  · exact B1286235
  · exact B1286239
  · exact B1286243
  · exact B1286247
  · exact B1286251
  · exact B1286255
  · exact B1286259
  · exact B1286263
  · exact B1286267
  · exact B1286271
  · exact B1286275
  · exact B1286279
  · exact B1286283
  · exact B1286287
  · exact B1286291
  · exact B1286295
  · exact B1286299
  · exact B1286303
  · exact B1286307
  · exact B1286311
  · exact B1286315
  · exact B1286319
  · exact B1286323
  · exact B1286327
  · exact B1286331
  · exact B1286335
  · exact B1286339
  · exact B1286343
  · exact B1286347
  · exact B1286351
  · exact B1286355
  · exact B1286359
  · exact B1286363
  · exact B1286367
  · exact B1286371
  · exact B1286375
  · exact B1286379
  · exact B1286383
  · exact B1286387
  · exact B1286391
  · exact B1286395
  · exact B1286399
  · exact B1286403
  · exact B1286407
  · exact B1286411
  · exact B1286415
  · exact B1286419
  · exact B1286423
  · exact B1286427
  · exact B1286431
  · exact B1286435
  · exact B1286439
  · exact B1286443
  · exact B1286447
  · exact B1286451
  · exact B1286455
  · exact B1286459
  · exact B1286463
  · exact B1286467
  · exact B1286471
  · exact B1286475
  · exact B1286479
  · exact B1286483
  · exact B1286487
  · exact B1286491
  · exact B1286495
  · exact B1286499
  · exact B1286503
  · exact B1286507
  · exact B1286511
  · exact B1286515
  · exact B1286519
  · exact B1286523
  · exact B1286527
  · exact B1286531
  · exact B1286535
  · exact B1286539
  · exact B1286543
  · exact B1286547
  · exact B1286551
  · exact B1286555
  · exact B1286559
  · exact B1286563
  · exact B1286567
  · exact B1286571
  · exact B1286575
  · exact B1286579
  · exact B1286583
  · exact B1286587
  · exact B1286591
  · exact B1286595
  · exact B1286599
  · exact B1286603
  · exact B1286607
  · exact B1286611
  · exact B1286615
  · exact B1286619
  · exact B1286623
  · exact B1286627
  · exact B1286631
  · exact B1286635
  · exact B1286639
  · exact B1286643
  · exact B1286647
  · exact B1286651
  · exact B1286655
  · exact B1286659
  · exact B1286663
  · exact B1286667
  · exact B1286671
  · exact B1286675
  · exact B1286679
  · exact B1286683
  · exact B1286687
  · exact B1286691
  · exact B1286695
  · exact B1286699
  · exact B1286703
  · exact B1286707
  · exact B1286711
  · exact B1286715
  · exact B1286719
  · exact B1286723
  · exact B1286727
  · exact B1286731
  · exact B1286735
  · exact B1286739
  · exact B1286743
  · exact B1286747
  · exact B1286751
  · exact B1286755
  · exact B1286759
  · exact B1286763
  · exact B1286767
  · exact B1286771
  · exact B1286775
  · exact B1286779
  · exact B1286783
  · exact B1286787
  · exact B1286791
  · exact B1286795
  · exact B1286799
  · exact B1286803
  · exact B1286807
  · exact B1286811
  · exact B1286815
  · exact B1286819
  · exact B1286823
  · exact B1286827
  · exact B1286831
  · exact B1286835
  · exact B1286839
  · exact B1286843
  · exact B1286847
  · exact B1286851
  · exact B1286855
  · exact B1286859
  · exact B1286863
  · exact B1286867
  · exact B1286871
  · exact B1286875
  · exact B1286879
  · exact B1286883
  · exact B1286887
  · exact B1286891
  · exact B1286895
  · exact B1286899
  · exact B1286903
  · exact B1286907
  · exact B1286911
  · exact B1286915
  · exact B1286919
  · exact B1286923
  · exact B1286927
  · exact B1286931
  · exact B1286935
  · exact B1286939
  · exact B1286943
  · exact B1286947
  · exact B1286951
  · exact B1286955
  · exact B1286959
  · exact B1286963
  · exact B1286967
  · exact B1286971
  · exact B1286975
  · exact B1286979
  · exact B1286983
  · exact B1286987
  · exact B1286991
  · exact B1286995
  · exact B1286999
  · exact B1287003
  · exact B1287007
  · exact B1287011
  · exact B1287015
  · exact B1287019
  · exact B1287023
  · exact B1287027
  · exact B1287031
  · exact B1287035
  · exact B1287039
  · exact B1287043
  · exact B1287047
  · exact B1287051
  · exact B1287055
  · exact B1287059
  · exact B1287063
  · exact B1287067
  · exact B1287071
  · exact B1287075
  · exact B1287079
  · exact B1287083
  · exact B1287087
  · exact B1287091
  · exact B1287095
  · exact B1287099
  · exact B1287103
  · exact B1287107
  · exact B1287111
  · exact B1287115
  · exact B1287119
  · exact B1287123
  · exact B1287127
  · exact B1287131
  · exact B1287135
  · exact B1287139
  · exact B1287143
  · exact B1287147
  · exact B1287151
  · exact B1287155
  · exact B1287159
  · exact B1287163
  · exact B1287167
  · exact B1287171
  · exact B1287175
  · exact B1287179
  · exact B1287183
  · exact B1287187
  · exact B1287191
  · exact B1287195
  · exact B1287199
  · exact B1287203
  · exact B1287207
  · exact B1287211
  · exact B1287215
  · exact B1287219
  · exact B1287223
  · exact B1287227
  · exact B1287231
  · exact B1287235
  · exact B1287239
  · exact B1287243
  · exact B1287247
  · exact B1287251
  · exact B1287255
  · exact B1287259
  · exact B1287263
  · exact B1287267
  · exact B1287271
  · exact B1287275
  · exact B1287279
  · exact B1287283
  · exact B1287287
  · exact B1287291
  · exact B1287295
  · exact B1287299
  · exact B1287303
  · exact B1287307
  · exact B1287311
  · exact B1287315
  · exact B1287319
  · exact B1287323
  · exact B1287327
  · exact B1287331
  · exact B1287335
  · exact B1287339
  · exact B1287343
  · exact B1287347
  · exact B1287351
  · exact B1287355
  · exact B1287359
  · exact B1287363
  · exact B1287367
  · exact B1287371
  · exact B1287375
  · exact B1287379
  · exact B1287383
  · exact B1287387
  · exact B1287391
  · exact B1287395
  · exact B1287399
  · exact B1287403
  · exact B1287407
  · exact B1287411
  · exact B1287415
  · exact B1287419
  · exact B1287423
  · exact B1287427
  · exact B1287431
  · exact B1287435
  · exact B1287439
  · exact B1287443
  · exact B1287447
  · exact B1287451
  · exact B1287455
  · exact B1287459
  · exact B1287463
  · exact B1287467
  · exact B1287471
  · exact B1287475
  · exact B1287479
  · exact B1287483
  · exact B1287487
  · exact B1287491
  · exact B1287495
  · exact B1287499
  · exact B1287503
  · exact B1287507
  · exact B1287511
  · exact B1287515
  · exact B1287519
  · exact B1287523
  · exact B1287527
  · exact B1287531
  · exact B1287535
  · exact B1287539
  · exact B1287543
  · exact B1287547
  · exact B1287551
  · exact B1287555
  · exact B1287559
  · exact B1287563
  · exact B1287567
  · exact B1287571
  · exact B1287575
  · exact B1287579
  · exact B1287583
  · exact B1287587
  · exact B1287591
  · exact B1287595
  · exact B1287599
  · exact B1287603
  · exact B1287607
  · exact B1287611
  · exact B1287615
  · exact B1287619
  · exact B1287623
  · exact B1287627
  · exact B1287631
  · exact B1287635
  · exact B1287639
  · exact B1287643
  · exact B1287647
  · exact B1287651
  · exact B1287655
  · exact B1287659
  · exact B1287663
  · exact B1287667
  · exact B1287671
  · exact B1287675
  · exact B1287679
  · exact B1287683
  · exact B1287687
  · exact B1287691
  · exact B1287695
  · exact B1287699
  · exact B1287703
  · exact B1287707
  · exact B1287711
  · exact B1287715
  · exact B1287719
  · exact B1287723
  · exact B1287727
  · exact B1287731
  · exact B1287735
  · exact B1287739
  · exact B1287743
  · exact B1287747
  · exact B1287751
  · exact B1287755
  · exact B1287759
  · exact B1287763
  · exact B1287767
  · exact B1287771
  · exact B1287775
  · exact B1287779
  · exact B1287783
  · exact B1287787
  · exact B1287791
  · exact B1287795
  · exact B1287799
  · exact B1287803
  · exact B1287807
  · exact B1287811
  · exact B1287815
  · exact B1287819
  · exact B1287823
  · exact B1287827
  · exact B1287831
  · exact B1287835
  · exact B1287839
  · exact B1287843
  · exact B1287847
  · exact B1287851
  · exact B1287855
  · exact B1287859
  · exact B1287863
  · exact B1287867
  · exact B1287871
  · exact B1287875
  · exact B1287879
  · exact B1287883
  · exact B1287887
  · exact B1287891
  · exact B1287895
  · exact B1287899
  · exact B1287903
  · exact B1287907
  · exact B1287911
  · exact B1287915
  · exact B1287919
  · exact B1287923
  · exact B1287927
  · exact B1287931
  · exact B1287935
  · exact B1287939
  · exact B1287943
  · exact B1287947
  · exact B1287951
  · exact B1287955
  · exact B1287959

theorem solution (m : ℕ) (hlo : 1285961 ≤ m) (hhi : m ≤ 1287961) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 321490 ≤ j := by omega
    have hj2 : j ≤ 321989 := by omega
    have hb : Blo 1285961 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
