-- Prove2me | solution 1 for syracuse_descends_range_1441540_1443540
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:47.848485+00:00
-- url     : https://prove2.me/submissions/84614923-bc93-4ab5-9bda-1c82ce9e2fb9

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


theorem B2162693 : Blo 1441540 2162693 := bbase (se 4 (by rfl) ⟨202752, by rfl⟩ : syracuseStep 2162693 = 405505) (by norm_num)
theorem B2433037 : Blo 1441540 2433037 := bbase (se 3 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 2433037 = 912389) (by norm_num)
theorem B1622029 : Blo 1441540 1622029 := bbase (se 3 (by rfl) ⟨304130, by rfl⟩ : syracuseStep 1622029 = 608261) (by norm_num)
theorem B2162717 : Blo 1441540 2162717 := bbase (se 3 (by rfl) ⟨405509, by rfl⟩ : syracuseStep 2162717 = 811019) (by norm_num)
theorem B1622065 : Blo 1441540 1622065 := bbase (se 2 (by rfl) ⟨608274, by rfl⟩ : syracuseStep 1622065 = 1216549) (by norm_num)
theorem B4866101 : Blo 1441540 4866101 := bbase (se 5 (by rfl) ⟨228098, by rfl⟩ : syracuseStep 4866101 = 456197) (by norm_num)
theorem B3244085 : Blo 1441540 3244085 := bbase (se 5 (by rfl) ⟨152066, by rfl⟩ : syracuseStep 3244085 = 304133) (by norm_num)
theorem B2162741 : Blo 1441540 2162741 := bbase (se 5 (by rfl) ⟨101378, by rfl⟩ : syracuseStep 2162741 = 202757) (by norm_num)
theorem B1826869 : Blo 1441540 1826869 := bbase (se 5 (by rfl) ⟨85634, by rfl⟩ : syracuseStep 1826869 = 171269) (by norm_num)
theorem B7307333 : Blo 1441540 7307333 := bbase (se 4 (by rfl) ⟨685062, by rfl⟩ : syracuseStep 7307333 = 1370125) (by norm_num)
theorem B2162765 : Blo 1441540 2162765 := bbase (se 3 (by rfl) ⟨405518, by rfl⟩ : syracuseStep 2162765 = 811037) (by norm_num)
theorem B1622101 : Blo 1441540 1622101 := bbase (se 8 (by rfl) ⟨9504, by rfl⟩ : syracuseStep 1622101 = 19009) (by norm_num)
theorem B2433125 : Blo 1441540 2433125 := bbase (se 4 (by rfl) ⟨228105, by rfl⟩ : syracuseStep 2433125 = 456211) (by norm_num)
theorem B2162789 : Blo 1441540 2162789 := bbase (se 4 (by rfl) ⟨202761, by rfl⟩ : syracuseStep 2162789 = 405523) (by norm_num)
theorem B1622137 : Blo 1441540 1622137 := bbase (se 2 (by rfl) ⟨608301, by rfl⟩ : syracuseStep 1622137 = 1216603) (by norm_num)
theorem B3244157 : Blo 1441540 3244157 := bbase (se 3 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 3244157 = 1216559) (by norm_num)
theorem B2162813 : Blo 1441540 2162813 := bbase (se 3 (by rfl) ⟨405527, by rfl⟩ : syracuseStep 2162813 = 811055) (by norm_num)
theorem B1540225 : Blo 1441540 1540225 := bbase (se 2 (by rfl) ⟨577584, by rfl⟩ : syracuseStep 1540225 = 1155169) (by norm_num)
theorem B1540229 : Blo 1441540 1540229 := bbase (se 4 (by rfl) ⟨144396, by rfl⟩ : syracuseStep 1540229 = 288793) (by norm_num)
theorem B9863317 : Blo 1441540 9863317 := bbase (se 6 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 9863317 = 462343) (by norm_num)
theorem B2162837 : Blo 1441540 2162837 := bbase (se 6 (by rfl) ⟨50691, by rfl⟩ : syracuseStep 2162837 = 101383) (by norm_num)
theorem B1826965 : Blo 1441540 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B1622173 : Blo 1441540 1622173 := bbase (se 3 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 1622173 = 608315) (by norm_num)
theorem B2162861 : Blo 1441540 2162861 := bbase (se 3 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 2162861 = 811073) (by norm_num)
theorem B1622209 : Blo 1441540 1622209 := bbase (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) (by norm_num)
theorem B3244229 : Blo 1441540 3244229 := bbase (se 4 (by rfl) ⟨304146, by rfl⟩ : syracuseStep 3244229 = 608293) (by norm_num)
theorem B2162885 : Blo 1441540 2162885 := bbase (se 4 (by rfl) ⟨202770, by rfl⟩ : syracuseStep 2162885 = 405541) (by norm_num)
theorem B2162909 : Blo 1441540 2162909 := bbase (se 3 (by rfl) ⟨405545, by rfl⟩ : syracuseStep 2162909 = 811091) (by norm_num)
theorem B2433253 : Blo 1441540 2433253 := bbase (se 4 (by rfl) ⟨228117, by rfl⟩ : syracuseStep 2433253 = 456235) (by norm_num)
theorem B1622245 : Blo 1441540 1622245 := bbase (se 4 (by rfl) ⟨152085, by rfl⟩ : syracuseStep 1622245 = 304171) (by norm_num)
theorem B3653869 : Blo 1441540 3653869 := bbase (se 3 (by rfl) ⟨685100, by rfl⟩ : syracuseStep 3653869 = 1370201) (by norm_num)
theorem B2162933 : Blo 1441540 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1622281 : Blo 1441540 1622281 := bbase (se 2 (by rfl) ⟨608355, by rfl⟩ : syracuseStep 1622281 = 1216711) (by norm_num)
theorem B3244301 : Blo 1441540 3244301 := bbase (se 3 (by rfl) ⟨608306, by rfl⟩ : syracuseStep 3244301 = 1216613) (by norm_num)
theorem B2162957 : Blo 1441540 2162957 := bbase (se 3 (by rfl) ⟨405554, by rfl⟩ : syracuseStep 2162957 = 811109) (by norm_num)
theorem B10952981 : Blo 1441540 10952981 := bbase (se 6 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 10952981 = 513421) (by norm_num)
theorem B2162981 : Blo 1441540 2162981 := bbase (se 4 (by rfl) ⟨202779, by rfl⟩ : syracuseStep 2162981 = 405559) (by norm_num)
theorem B1622317 : Blo 1441540 1622317 := bbase (se 3 (by rfl) ⟨304184, by rfl⟩ : syracuseStep 1622317 = 608369) (by norm_num)
theorem B1851697 : Blo 1441540 1851697 := bbase (se 2 (by rfl) ⟨694386, by rfl⟩ : syracuseStep 1851697 = 1388773) (by norm_num)
theorem B2433341 : Blo 1441540 2433341 := bbase (se 3 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 2433341 = 912503) (by norm_num)
theorem B2163005 : Blo 1441540 2163005 := bbase (se 3 (by rfl) ⟨405563, by rfl⟩ : syracuseStep 2163005 = 811127) (by norm_num)
theorem B1622353 : Blo 1441540 1622353 := bbase (se 2 (by rfl) ⟨608382, by rfl⟩ : syracuseStep 1622353 = 1216765) (by norm_num)
theorem B3244373 : Blo 1441540 3244373 := bbase (se 10 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 3244373 = 9505) (by norm_num)
theorem B2163029 : Blo 1441540 2163029 := bbase (se 10 (by rfl) ⟨3168, by rfl⟩ : syracuseStep 2163029 = 6337) (by norm_num)
theorem B2163053 : Blo 1441540 2163053 := bbase (se 3 (by rfl) ⟨405572, by rfl⟩ : syracuseStep 2163053 = 811145) (by norm_num)
theorem B1622389 : Blo 1441540 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B1851769 : Blo 1441540 1851769 := bbase (se 2 (by rfl) ⟨694413, by rfl⟩ : syracuseStep 1851769 = 1388827) (by norm_num)
theorem B2163077 : Blo 1441540 2163077 := bbase (se 4 (by rfl) ⟨202788, by rfl⟩ : syracuseStep 2163077 = 405577) (by norm_num)
theorem B1622425 : Blo 1441540 1622425 := bbase (se 2 (by rfl) ⟨608409, by rfl⟩ : syracuseStep 1622425 = 1216819) (by norm_num)
theorem B3244445 : Blo 1441540 3244445 := bbase (se 3 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 3244445 = 1216667) (by norm_num)
theorem B2163101 : Blo 1441540 2163101 := bbase (se 3 (by rfl) ⟨405581, by rfl⟩ : syracuseStep 2163101 = 811163) (by norm_num)
theorem B2163125 : Blo 1441540 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B3080629 : Blo 1441540 3080629 := bbase (se 5 (by rfl) ⟨144404, by rfl⟩ : syracuseStep 3080629 = 288809) (by norm_num)
theorem B2433469 : Blo 1441540 2433469 := bbase (se 3 (by rfl) ⟨456275, by rfl⟩ : syracuseStep 2433469 = 912551) (by norm_num)
theorem B1622461 : Blo 1441540 1622461 := bbase (se 3 (by rfl) ⟨304211, by rfl⟩ : syracuseStep 1622461 = 608423) (by norm_num)
theorem B3465661 : Blo 1441540 3465661 := bbase (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) (by norm_num)
theorem B2163149 : Blo 1441540 2163149 := bbase (se 3 (by rfl) ⟨405590, by rfl⟩ : syracuseStep 2163149 = 811181) (by norm_num)
theorem B1622497 : Blo 1441540 1622497 := bbase (se 2 (by rfl) ⟨608436, by rfl⟩ : syracuseStep 1622497 = 1216873) (by norm_num)
theorem B7299557 : Blo 1441540 7299557 := bbase (se 4 (by rfl) ⟨684333, by rfl⟩ : syracuseStep 7299557 = 1368667) (by norm_num)
theorem B4866533 : Blo 1441540 4866533 := bbase (se 4 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 4866533 = 912475) (by norm_num)
theorem B3244517 : Blo 1441540 3244517 := bbase (se 4 (by rfl) ⟨304173, by rfl⟩ : syracuseStep 3244517 = 608347) (by norm_num)
theorem B2163173 : Blo 1441540 2163173 := bbase (se 4 (by rfl) ⟨202797, by rfl⟩ : syracuseStep 2163173 = 405595) (by norm_num)
theorem B2163197 : Blo 1441540 2163197 := bbase (se 3 (by rfl) ⟨405599, by rfl⟩ : syracuseStep 2163197 = 811199) (by norm_num)
theorem B1622533 : Blo 1441540 1622533 := bbase (se 4 (by rfl) ⟨152112, by rfl⟩ : syracuseStep 1622533 = 304225) (by norm_num)
theorem B2433557 : Blo 1441540 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B2163221 : Blo 1441540 2163221 := bbase (se 6 (by rfl) ⟨50700, by rfl⟩ : syracuseStep 2163221 = 101401) (by norm_num)
theorem B1622569 : Blo 1441540 1622569 := bbase (se 2 (by rfl) ⟨608463, by rfl⟩ : syracuseStep 1622569 = 1216927) (by norm_num)
theorem B3244589 : Blo 1441540 3244589 := bbase (se 3 (by rfl) ⟨608360, by rfl⟩ : syracuseStep 3244589 = 1216721) (by norm_num)
theorem B2163245 : Blo 1441540 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B3080749 : Blo 1441540 3080749 := bbase (se 3 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 3080749 = 1155281) (by norm_num)
theorem B2163269 : Blo 1441540 2163269 := bbase (se 4 (by rfl) ⟨202806, by rfl⟩ : syracuseStep 2163269 = 405613) (by norm_num)
theorem B1622605 : Blo 1441540 1622605 := bbase (se 3 (by rfl) ⟨304238, by rfl⟩ : syracuseStep 1622605 = 608477) (by norm_num)
theorem B11248213 : Blo 1441540 11248213 := bbase (se 8 (by rfl) ⟨65907, by rfl⟩ : syracuseStep 11248213 = 131815) (by norm_num)
theorem B2163293 : Blo 1441540 2163293 := bbase (se 3 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 2163293 = 811235) (by norm_num)
theorem B1622641 : Blo 1441540 1622641 := bbase (se 2 (by rfl) ⟨608490, by rfl⟩ : syracuseStep 1622641 = 1216981) (by norm_num)
theorem B2736757 : Blo 1441540 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B6242933 : Blo 1441540 6242933 := bbase (se 5 (by rfl) ⟨292637, by rfl⟩ : syracuseStep 6242933 = 585275) (by norm_num)
theorem B3244661 : Blo 1441540 3244661 := bbase (se 5 (by rfl) ⟨152093, by rfl⟩ : syracuseStep 3244661 = 304187) (by norm_num)
theorem B2163317 : Blo 1441540 2163317 := bbase (se 5 (by rfl) ⟨101405, by rfl⟩ : syracuseStep 2163317 = 202811) (by norm_num)
theorem B2163341 : Blo 1441540 2163341 := bbase (se 3 (by rfl) ⟨405626, by rfl⟩ : syracuseStep 2163341 = 811253) (by norm_num)
theorem B2433685 : Blo 1441540 2433685 := bbase (se 6 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 2433685 = 114079) (by norm_num)
theorem B1622677 : Blo 1441540 1622677 := bbase (se 6 (by rfl) ⟨38031, by rfl⟩ : syracuseStep 1622677 = 76063) (by norm_num)
theorem B2310805 : Blo 1441540 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B2163365 : Blo 1441540 2163365 := bbase (se 4 (by rfl) ⟨202815, by rfl⟩ : syracuseStep 2163365 = 405631) (by norm_num)
theorem B6931109 : Blo 1441540 6931109 := bbase (se 4 (by rfl) ⟨649791, by rfl⟩ : syracuseStep 6931109 = 1299583) (by norm_num)
theorem B1622713 : Blo 1441540 1622713 := bbase (se 2 (by rfl) ⟨608517, by rfl⟩ : syracuseStep 1622713 = 1217035) (by norm_num)
theorem B1540793 : Blo 1441540 1540793 := bbase (se 2 (by rfl) ⟨577797, by rfl⟩ : syracuseStep 1540793 = 1155595) (by norm_num)
theorem B3244733 : Blo 1441540 3244733 := bbase (se 3 (by rfl) ⟨608387, by rfl⟩ : syracuseStep 3244733 = 1216775) (by norm_num)
theorem B2163389 : Blo 1441540 2163389 := bbase (se 3 (by rfl) ⟨405635, by rfl⟩ : syracuseStep 2163389 = 811271) (by norm_num)
theorem B2163413 : Blo 1441540 2163413 := bbase (se 7 (by rfl) ⟨25352, by rfl⟩ : syracuseStep 2163413 = 50705) (by norm_num)
theorem B1622749 : Blo 1441540 1622749 := bbase (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) (by norm_num)
theorem B2433773 : Blo 1441540 2433773 := bbase (se 3 (by rfl) ⟨456332, by rfl⟩ : syracuseStep 2433773 = 912665) (by norm_num)
theorem B2163437 : Blo 1441540 2163437 := bbase (se 3 (by rfl) ⟨405644, by rfl⟩ : syracuseStep 2163437 = 811289) (by norm_num)
theorem B1622785 : Blo 1441540 1622785 := bbase (se 2 (by rfl) ⟨608544, by rfl⟩ : syracuseStep 1622785 = 1217089) (by norm_num)
theorem B3244805 : Blo 1441540 3244805 := bbase (se 4 (by rfl) ⟨304200, by rfl⟩ : syracuseStep 3244805 = 608401) (by norm_num)
theorem B2163461 : Blo 1441540 2163461 := bbase (se 4 (by rfl) ⟨202824, by rfl⟩ : syracuseStep 2163461 = 405649) (by norm_num)
theorem B2163485 : Blo 1441540 2163485 := bbase (se 3 (by rfl) ⟨405653, by rfl⟩ : syracuseStep 2163485 = 811307) (by norm_num)
theorem B1622821 : Blo 1441540 1622821 := bbase (se 4 (by rfl) ⟨152139, by rfl⟩ : syracuseStep 1622821 = 304279) (by norm_num)
theorem B3081005 : Blo 1441540 3081005 := bbase (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) (by norm_num)
theorem B2163509 : Blo 1441540 2163509 := bbase (se 5 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 2163509 = 202829) (by norm_num)
theorem B1622857 : Blo 1441540 1622857 := bbase (se 2 (by rfl) ⟨608571, by rfl⟩ : syracuseStep 1622857 = 1217143) (by norm_num)
theorem B3244877 : Blo 1441540 3244877 := bbase (se 3 (by rfl) ⟨608414, by rfl⟩ : syracuseStep 3244877 = 1216829) (by norm_num)
theorem B2163533 : Blo 1441540 2163533 := bbase (se 3 (by rfl) ⟨405662, by rfl⟩ : syracuseStep 2163533 = 811325) (by norm_num)
theorem B5849941 : Blo 1441540 5849941 := bbase (se 9 (by rfl) ⟨17138, by rfl⟩ : syracuseStep 5849941 = 34277) (by norm_num)
theorem B2163557 : Blo 1441540 2163557 := bbase (se 4 (by rfl) ⟨202833, by rfl⟩ : syracuseStep 2163557 = 405667) (by norm_num)
theorem B2433901 : Blo 1441540 2433901 := bbase (se 3 (by rfl) ⟨456356, by rfl⟩ : syracuseStep 2433901 = 912713) (by norm_num)
theorem B1622893 : Blo 1441540 1622893 := bbase (se 3 (by rfl) ⟨304292, by rfl⟩ : syracuseStep 1622893 = 608585) (by norm_num)
theorem B1540981 : Blo 1441540 1540981 := bbase (se 5 (by rfl) ⟨72233, by rfl⟩ : syracuseStep 1540981 = 144467) (by norm_num)
theorem B2163581 : Blo 1441540 2163581 := bbase (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) (by norm_num)
theorem B1622929 : Blo 1441540 1622929 := bbase (se 2 (by rfl) ⟨608598, by rfl⟩ : syracuseStep 1622929 = 1217197) (by norm_num)
theorem B4866965 : Blo 1441540 4866965 := bbase (se 6 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 4866965 = 228139) (by norm_num)
theorem B3244949 : Blo 1441540 3244949 := bbase (se 6 (by rfl) ⟨76053, by rfl⟩ : syracuseStep 3244949 = 152107) (by norm_num)
theorem B2163605 : Blo 1441540 2163605 := bbase (se 6 (by rfl) ⟨50709, by rfl⟩ : syracuseStep 2163605 = 101419) (by norm_num)
theorem B2737061 : Blo 1441540 2737061 := bbase (se 4 (by rfl) ⟨256599, by rfl⟩ : syracuseStep 2737061 = 513199) (by norm_num)
theorem B2163629 : Blo 1441540 2163629 := bbase (se 3 (by rfl) ⟨405680, by rfl⟩ : syracuseStep 2163629 = 811361) (by norm_num)
theorem B1622965 : Blo 1441540 1622965 := bbase (se 5 (by rfl) ⟨76076, by rfl⟩ : syracuseStep 1622965 = 152153) (by norm_num)
theorem B2433989 : Blo 1441540 2433989 := bbase (se 4 (by rfl) ⟨228186, by rfl⟩ : syracuseStep 2433989 = 456373) (by norm_num)
theorem B2163653 : Blo 1441540 2163653 := bbase (se 4 (by rfl) ⟨202842, by rfl⟩ : syracuseStep 2163653 = 405685) (by norm_num)
theorem B1623001 : Blo 1441540 1623001 := bbase (se 2 (by rfl) ⟨608625, by rfl⟩ : syracuseStep 1623001 = 1217251) (by norm_num)
theorem B3245021 : Blo 1441540 3245021 := bbase (se 3 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 3245021 = 1216883) (by norm_num)
theorem B2163677 : Blo 1441540 2163677 := bbase (se 3 (by rfl) ⟨405689, by rfl⟩ : syracuseStep 2163677 = 811379) (by norm_num)
theorem B4105205 : Blo 1441540 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B2163701 : Blo 1441540 2163701 := bbase (se 5 (by rfl) ⟨101423, by rfl⟩ : syracuseStep 2163701 = 202847) (by norm_num)
theorem B1623037 : Blo 1441540 1623037 := bbase (se 3 (by rfl) ⟨304319, by rfl⟩ : syracuseStep 1623037 = 608639) (by norm_num)
theorem B2163725 : Blo 1441540 2163725 := bbase (se 3 (by rfl) ⟨405698, by rfl⟩ : syracuseStep 2163725 = 811397) (by norm_num)
theorem B1623073 : Blo 1441540 1623073 := bbase (se 2 (by rfl) ⟨608652, by rfl⟩ : syracuseStep 1623073 = 1217305) (by norm_num)
theorem B3245093 : Blo 1441540 3245093 := bbase (se 4 (by rfl) ⟨304227, by rfl⟩ : syracuseStep 3245093 = 608455) (by norm_num)
theorem B2163749 : Blo 1441540 2163749 := bbase (se 4 (by rfl) ⟨202851, by rfl⟩ : syracuseStep 2163749 = 405703) (by norm_num)
theorem B3466277 : Blo 1441540 3466277 := bbase (se 4 (by rfl) ⟨324963, by rfl⟩ : syracuseStep 3466277 = 649927) (by norm_num)
theorem B2163773 : Blo 1441540 2163773 := bbase (se 3 (by rfl) ⟨405707, by rfl⟩ : syracuseStep 2163773 = 811415) (by norm_num)
theorem B2311229 : Blo 1441540 2311229 := bbase (se 3 (by rfl) ⟨433355, by rfl⟩ : syracuseStep 2311229 = 866711) (by norm_num)
theorem B2434117 : Blo 1441540 2434117 := bbase (se 4 (by rfl) ⟨228198, by rfl⟩ : syracuseStep 2434117 = 456397) (by norm_num)
theorem B1623109 : Blo 1441540 1623109 := bbase (se 4 (by rfl) ⟨152166, by rfl⟩ : syracuseStep 1623109 = 304333) (by norm_num)
theorem B2163797 : Blo 1441540 2163797 := bbase (se 8 (by rfl) ⟨12678, by rfl⟩ : syracuseStep 2163797 = 25357) (by norm_num)
theorem B1623145 : Blo 1441540 1623145 := bbase (se 2 (by rfl) ⟨608679, by rfl⟩ : syracuseStep 1623145 = 1217359) (by norm_num)
theorem B3245165 : Blo 1441540 3245165 := bbase (se 3 (by rfl) ⟨608468, by rfl⟩ : syracuseStep 3245165 = 1216937) (by norm_num)
theorem B2163821 : Blo 1441540 2163821 := bbase (se 3 (by rfl) ⟨405716, by rfl⟩ : syracuseStep 2163821 = 811433) (by norm_num)
theorem B2163845 : Blo 1441540 2163845 := bbase (se 4 (by rfl) ⟨202860, by rfl⟩ : syracuseStep 2163845 = 405721) (by norm_num)
theorem B1623181 : Blo 1441540 1623181 := bbase (se 3 (by rfl) ⟨304346, by rfl⟩ : syracuseStep 1623181 = 608693) (by norm_num)
theorem B2434205 : Blo 1441540 2434205 := bbase (se 3 (by rfl) ⟨456413, by rfl⟩ : syracuseStep 2434205 = 912827) (by norm_num)
theorem B2163869 : Blo 1441540 2163869 := bbase (se 3 (by rfl) ⟨405725, by rfl⟩ : syracuseStep 2163869 = 811451) (by norm_num)
theorem B2925733 : Blo 1441540 2925733 := bbase (se 4 (by rfl) ⟨274287, by rfl⟩ : syracuseStep 2925733 = 548575) (by norm_num)
theorem B1623217 : Blo 1441540 1623217 := bbase (se 2 (by rfl) ⟨608706, by rfl⟩ : syracuseStep 1623217 = 1217413) (by norm_num)
theorem B3245237 : Blo 1441540 3245237 := bbase (se 5 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 3245237 = 304241) (by norm_num)
theorem B2163893 : Blo 1441540 2163893 := bbase (se 5 (by rfl) ⟨101432, by rfl⟩ : syracuseStep 2163893 = 202865) (by norm_num)
theorem B2163917 : Blo 1441540 2163917 := bbase (se 3 (by rfl) ⟨405734, by rfl⟩ : syracuseStep 2163917 = 811469) (by norm_num)
theorem B1623253 : Blo 1441540 1623253 := bbase (se 7 (by rfl) ⟨19022, by rfl⟩ : syracuseStep 1623253 = 38045) (by norm_num)
theorem B9872597 : Blo 1441540 9872597 := bbase (se 7 (by rfl) ⟨115694, by rfl⟩ : syracuseStep 9872597 = 231389) (by norm_num)
theorem B2163941 : Blo 1441540 2163941 := bbase (se 4 (by rfl) ⟨202869, by rfl⟩ : syracuseStep 2163941 = 405739) (by norm_num)
theorem B1623289 : Blo 1441540 1623289 := bbase (se 2 (by rfl) ⟨608733, by rfl⟩ : syracuseStep 1623289 = 1217467) (by norm_num)
theorem B3245309 : Blo 1441540 3245309 := bbase (se 3 (by rfl) ⟨608495, by rfl⟩ : syracuseStep 3245309 = 1216991) (by norm_num)
theorem B2163965 : Blo 1441540 2163965 := bbase (se 3 (by rfl) ⟨405743, by rfl⟩ : syracuseStep 2163965 = 811487) (by norm_num)
theorem B6161669 : Blo 1441540 6161669 := bbase (se 4 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 6161669 = 1155313) (by norm_num)
theorem B2163989 : Blo 1441540 2163989 := bbase (se 6 (by rfl) ⟨50718, by rfl⟩ : syracuseStep 2163989 = 101437) (by norm_num)
theorem B2434333 : Blo 1441540 2434333 := bbase (se 3 (by rfl) ⟨456437, by rfl⟩ : syracuseStep 2434333 = 912875) (by norm_num)
theorem B1623325 : Blo 1441540 1623325 := bbase (se 3 (by rfl) ⟨304373, by rfl⟩ : syracuseStep 1623325 = 608747) (by norm_num)
theorem B2164013 : Blo 1441540 2164013 := bbase (se 3 (by rfl) ⟨405752, by rfl⟩ : syracuseStep 2164013 = 811505) (by norm_num)
theorem B1623361 : Blo 1441540 1623361 := bbase (se 2 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 1623361 = 1217521) (by norm_num)
theorem B4867397 : Blo 1441540 4867397 := bbase (se 4 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 4867397 = 912637) (by norm_num)
theorem B3245381 : Blo 1441540 3245381 := bbase (se 4 (by rfl) ⟨304254, by rfl⟩ : syracuseStep 3245381 = 608509) (by norm_num)
theorem B4621637 : Blo 1441540 4621637 := bbase (se 4 (by rfl) ⟨433278, by rfl⟩ : syracuseStep 4621637 = 866557) (by norm_num)
theorem B2164037 : Blo 1441540 2164037 := bbase (se 4 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 2164037 = 405757) (by norm_num)
theorem B2164061 : Blo 1441540 2164061 := bbase (se 3 (by rfl) ⟨405761, by rfl⟩ : syracuseStep 2164061 = 811523) (by norm_num)
theorem B2311517 : Blo 1441540 2311517 := bbase (se 3 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 2311517 = 866819) (by norm_num)
theorem B1623397 : Blo 1441540 1623397 := bbase (se 4 (by rfl) ⟨152193, by rfl⟩ : syracuseStep 1623397 = 304387) (by norm_num)
theorem B2434421 : Blo 1441540 2434421 := bbase (se 5 (by rfl) ⟨114113, by rfl⟩ : syracuseStep 2434421 = 228227) (by norm_num)
theorem B2164085 : Blo 1441540 2164085 := bbase (se 5 (by rfl) ⟨101441, by rfl⟩ : syracuseStep 2164085 = 202883) (by norm_num)
theorem B1623433 : Blo 1441540 1623433 := bbase (se 2 (by rfl) ⟨608787, by rfl⟩ : syracuseStep 1623433 = 1217575) (by norm_num)
theorem B3245453 : Blo 1441540 3245453 := bbase (se 3 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 3245453 = 1217045) (by norm_num)
theorem B2164109 : Blo 1441540 2164109 := bbase (se 3 (by rfl) ⟨405770, by rfl⟩ : syracuseStep 2164109 = 811541) (by norm_num)
theorem B4105637 : Blo 1441540 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2164133 : Blo 1441540 2164133 := bbase (se 4 (by rfl) ⟨202887, by rfl⟩ : syracuseStep 2164133 = 405775) (by norm_num)
theorem B1623469 : Blo 1441540 1623469 := bbase (se 3 (by rfl) ⟨304400, by rfl⟩ : syracuseStep 1623469 = 608801) (by norm_num)
theorem B2164157 : Blo 1441540 2164157 := bbase (se 3 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 2164157 = 811559) (by norm_num)
theorem B3900869 : Blo 1441540 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B1623505 : Blo 1441540 1623505 := bbase (se 2 (by rfl) ⟨608814, by rfl⟩ : syracuseStep 1623505 = 1217629) (by norm_num)
theorem B3245525 : Blo 1441540 3245525 := bbase (se 7 (by rfl) ⟨38033, by rfl⟩ : syracuseStep 3245525 = 76067) (by norm_num)
theorem B2164181 : Blo 1441540 2164181 := bbase (se 7 (by rfl) ⟨25361, by rfl⟩ : syracuseStep 2164181 = 50723) (by norm_num)
theorem B2164205 : Blo 1441540 2164205 := bbase (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) (by norm_num)
theorem B2434549 : Blo 1441540 2434549 := bbase (se 5 (by rfl) ⟨114119, by rfl⟩ : syracuseStep 2434549 = 228239) (by norm_num)
theorem B1623541 : Blo 1441540 1623541 := bbase (se 5 (by rfl) ⟨76103, by rfl⟩ : syracuseStep 1623541 = 152207) (by norm_num)
theorem B2164229 : Blo 1441540 2164229 := bbase (se 4 (by rfl) ⟨202896, by rfl⟩ : syracuseStep 2164229 = 405793) (by norm_num)
theorem B20809237 : Blo 1441540 20809237 := bbase (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) (by norm_num)
theorem B1623577 : Blo 1441540 1623577 := bbase (se 2 (by rfl) ⟨608841, by rfl⟩ : syracuseStep 1623577 = 1217683) (by norm_num)
theorem B3245597 : Blo 1441540 3245597 := bbase (se 3 (by rfl) ⟨608549, by rfl⟩ : syracuseStep 3245597 = 1217099) (by norm_num)
theorem B2164253 : Blo 1441540 2164253 := bbase (se 3 (by rfl) ⟨405797, by rfl⟩ : syracuseStep 2164253 = 811595) (by norm_num)
theorem B2164277 : Blo 1441540 2164277 := bbase (se 5 (by rfl) ⟨101450, by rfl⟩ : syracuseStep 2164277 = 202901) (by norm_num)
theorem B1623613 : Blo 1441540 1623613 := bbase (se 3 (by rfl) ⟨304427, by rfl⟩ : syracuseStep 1623613 = 608855) (by norm_num)
theorem B2434637 : Blo 1441540 2434637 := bbase (se 3 (by rfl) ⟨456494, by rfl⟩ : syracuseStep 2434637 = 912989) (by norm_num)
theorem B2164301 : Blo 1441540 2164301 := bbase (se 3 (by rfl) ⟨405806, by rfl⟩ : syracuseStep 2164301 = 811613) (by norm_num)
theorem B2082397 : Blo 1441540 2082397 := bbase (se 3 (by rfl) ⟨390449, by rfl⟩ : syracuseStep 2082397 = 780899) (by norm_num)
theorem B1623649 : Blo 1441540 1623649 := bbase (se 2 (by rfl) ⟨608868, by rfl⟩ : syracuseStep 1623649 = 1217737) (by norm_num)
theorem B3245669 : Blo 1441540 3245669 := bbase (se 4 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 3245669 = 608563) (by norm_num)
theorem B2164325 : Blo 1441540 2164325 := bbase (se 4 (by rfl) ⟨202905, by rfl⟩ : syracuseStep 2164325 = 405811) (by norm_num)
theorem B2164349 : Blo 1441540 2164349 := bbase (se 3 (by rfl) ⟨405815, by rfl⟩ : syracuseStep 2164349 = 811631) (by norm_num)
theorem B5473925 : Blo 1441540 5473925 := bbase (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) (by norm_num)
theorem B1623685 : Blo 1441540 1623685 := bbase (se 4 (by rfl) ⟨152220, by rfl⟩ : syracuseStep 1623685 = 304441) (by norm_num)
theorem B2737813 : Blo 1441540 2737813 := bbase (se 6 (by rfl) ⟨64167, by rfl⟩ : syracuseStep 2737813 = 128335) (by norm_num)
theorem B2164373 : Blo 1441540 2164373 := bbase (se 6 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 2164373 = 101455) (by norm_num)
theorem B2467493 : Blo 1441540 2467493 := bbase (se 4 (by rfl) ⟨231327, by rfl⟩ : syracuseStep 2467493 = 462655) (by norm_num)
theorem B3081893 : Blo 1441540 3081893 := bbase (se 4 (by rfl) ⟨288927, by rfl⟩ : syracuseStep 3081893 = 577855) (by norm_num)
theorem B1623721 : Blo 1441540 1623721 := bbase (se 2 (by rfl) ⟨608895, by rfl⟩ : syracuseStep 1623721 = 1217791) (by norm_num)
theorem B3245741 : Blo 1441540 3245741 := bbase (se 3 (by rfl) ⟨608576, by rfl⟩ : syracuseStep 3245741 = 1217153) (by norm_num)
theorem B2164397 : Blo 1441540 2164397 := bbase (se 3 (by rfl) ⟨405824, by rfl⟩ : syracuseStep 2164397 = 811649) (by norm_num)
theorem B2598589 : Blo 1441540 2598589 := bbase (se 3 (by rfl) ⟨487235, by rfl⟩ : syracuseStep 2598589 = 974471) (by norm_num)
theorem B2164421 : Blo 1441540 2164421 := bbase (se 4 (by rfl) ⟨202914, by rfl⟩ : syracuseStep 2164421 = 405829) (by norm_num)
theorem B2434765 : Blo 1441540 2434765 := bbase (se 3 (by rfl) ⟨456518, by rfl⟩ : syracuseStep 2434765 = 913037) (by norm_num)
theorem B1623757 : Blo 1441540 1623757 := bbase (se 3 (by rfl) ⟨304454, by rfl⟩ : syracuseStep 1623757 = 608909) (by norm_num)
theorem B15599317 : Blo 1441540 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B2164445 : Blo 1441540 2164445 := bbase (se 3 (by rfl) ⟨405833, by rfl⟩ : syracuseStep 2164445 = 811667) (by norm_num)
theorem B1828585 : Blo 1441540 1828585 := bbase (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) (by norm_num)
theorem B1623793 : Blo 1441540 1623793 := bbase (se 2 (by rfl) ⟨608922, by rfl⟩ : syracuseStep 1623793 = 1217845) (by norm_num)
theorem B7300853 : Blo 1441540 7300853 := bbase (se 5 (by rfl) ⟨342227, by rfl⟩ : syracuseStep 7300853 = 684455) (by norm_num)
theorem B4867829 : Blo 1441540 4867829 := bbase (se 5 (by rfl) ⟨228179, by rfl⟩ : syracuseStep 4867829 = 456359) (by norm_num)
theorem B3245813 : Blo 1441540 3245813 := bbase (se 5 (by rfl) ⟨152147, by rfl⟩ : syracuseStep 3245813 = 304295) (by norm_num)
theorem B2164469 : Blo 1441540 2164469 := bbase (se 5 (by rfl) ⟨101459, by rfl⟩ : syracuseStep 2164469 = 202919) (by norm_num)
theorem B2164493 : Blo 1441540 2164493 := bbase (se 3 (by rfl) ⟨405842, by rfl⟩ : syracuseStep 2164493 = 811685) (by norm_num)
theorem B1623829 : Blo 1441540 1623829 := bbase (se 6 (by rfl) ⟨38058, by rfl⟩ : syracuseStep 1623829 = 76117) (by norm_num)
theorem B2737957 : Blo 1441540 2737957 := bbase (se 4 (by rfl) ⟨256683, by rfl⟩ : syracuseStep 2737957 = 513367) (by norm_num)
theorem B2434853 : Blo 1441540 2434853 := bbase (se 4 (by rfl) ⟨228267, by rfl⟩ : syracuseStep 2434853 = 456535) (by norm_num)
theorem B3467045 : Blo 1441540 3467045 := bbase (se 4 (by rfl) ⟨325035, by rfl⟩ : syracuseStep 3467045 = 650071) (by norm_num)
theorem B2164517 : Blo 1441540 2164517 := bbase (se 4 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 2164517 = 405847) (by norm_num)
theorem B3467053 : Blo 1441540 3467053 := bbase (se 3 (by rfl) ⟨650072, by rfl⟩ : syracuseStep 3467053 = 1300145) (by norm_num)
theorem B1623865 : Blo 1441540 1623865 := bbase (se 2 (by rfl) ⟨608949, by rfl⟩ : syracuseStep 1623865 = 1217899) (by norm_num)
theorem B3245885 : Blo 1441540 3245885 := bbase (se 3 (by rfl) ⟨608603, by rfl⟩ : syracuseStep 3245885 = 1217207) (by norm_num)
theorem B2164541 : Blo 1441540 2164541 := bbase (se 3 (by rfl) ⟨405851, by rfl⟩ : syracuseStep 2164541 = 811703) (by norm_num)
theorem B2598733 : Blo 1441540 2598733 := bbase (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) (by norm_num)
theorem B2164565 : Blo 1441540 2164565 := bbase (se 9 (by rfl) ⟨6341, by rfl⟩ : syracuseStep 2164565 = 12683) (by norm_num)
theorem B1623901 : Blo 1441540 1623901 := bbase (se 3 (by rfl) ⟨304481, by rfl⟩ : syracuseStep 1623901 = 608963) (by norm_num)
theorem B2164589 : Blo 1441540 2164589 := bbase (se 3 (by rfl) ⟨405860, by rfl⟩ : syracuseStep 2164589 = 811721) (by norm_num)
theorem B3901301 : Blo 1441540 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B1623937 : Blo 1441540 1623937 := bbase (se 2 (by rfl) ⟨608976, by rfl⟩ : syracuseStep 1623937 = 1217953) (by norm_num)
theorem B3245957 : Blo 1441540 3245957 := bbase (se 4 (by rfl) ⟨304308, by rfl⟩ : syracuseStep 3245957 = 608617) (by norm_num)
theorem B2164613 : Blo 1441540 2164613 := bbase (se 4 (by rfl) ⟨202932, by rfl⟩ : syracuseStep 2164613 = 405865) (by norm_num)
theorem B3082133 : Blo 1441540 3082133 := bbase (se 6 (by rfl) ⟨72237, by rfl⟩ : syracuseStep 3082133 = 144475) (by norm_num)
theorem B2164637 : Blo 1441540 2164637 := bbase (se 3 (by rfl) ⟨405869, by rfl⟩ : syracuseStep 2164637 = 811739) (by norm_num)
theorem B5474213 : Blo 1441540 5474213 := bbase (se 4 (by rfl) ⟨513207, by rfl⟩ : syracuseStep 5474213 = 1026415) (by norm_num)
theorem B2434981 : Blo 1441540 2434981 := bbase (se 4 (by rfl) ⟨228279, by rfl⟩ : syracuseStep 2434981 = 456559) (by norm_num)
theorem B1623973 : Blo 1441540 1623973 := bbase (se 4 (by rfl) ⟨152247, by rfl⟩ : syracuseStep 1623973 = 304495) (by norm_num)
theorem B2164661 : Blo 1441540 2164661 := bbase (se 5 (by rfl) ⟨101468, by rfl⟩ : syracuseStep 2164661 = 202937) (by norm_num)
theorem B2738117 : Blo 1441540 2738117 := bbase (se 4 (by rfl) ⟨256698, by rfl⟩ : syracuseStep 2738117 = 513397) (by norm_num)
theorem B3246029 : Blo 1441540 3246029 := bbase (se 3 (by rfl) ⟨608630, by rfl⟩ : syracuseStep 3246029 = 1217261) (by norm_num)
theorem B2164685 : Blo 1441540 2164685 := bbase (se 3 (by rfl) ⟨405878, by rfl⟩ : syracuseStep 2164685 = 811757) (by norm_num)
theorem B2164709 : Blo 1441540 2164709 := bbase (se 4 (by rfl) ⟨202941, by rfl⟩ : syracuseStep 2164709 = 405883) (by norm_num)
theorem B2435069 : Blo 1441540 2435069 := bbase (se 3 (by rfl) ⟨456575, by rfl⟩ : syracuseStep 2435069 = 913151) (by norm_num)
theorem B2164733 : Blo 1441540 2164733 := bbase (se 3 (by rfl) ⟨405887, by rfl⟩ : syracuseStep 2164733 = 811775) (by norm_num)
theorem B3246101 : Blo 1441540 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B2164757 : Blo 1441540 2164757 := bbase (se 6 (by rfl) ⟨50736, by rfl⟩ : syracuseStep 2164757 = 101473) (by norm_num)
theorem B2164781 : Blo 1441540 2164781 := bbase (se 3 (by rfl) ⟨405896, by rfl⟩ : syracuseStep 2164781 = 811793) (by norm_num)
theorem B2164805 : Blo 1441540 2164805 := bbase (se 4 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 2164805 = 405901) (by norm_num)
theorem B2738261 : Blo 1441540 2738261 := bbase (se 8 (by rfl) ⟨16044, by rfl⟩ : syracuseStep 2738261 = 32089) (by norm_num)
theorem B3246173 : Blo 1441540 3246173 := bbase (se 3 (by rfl) ⟨608657, by rfl⟩ : syracuseStep 3246173 = 1217315) (by norm_num)
theorem B2164829 : Blo 1441540 2164829 := bbase (se 3 (by rfl) ⟨405905, by rfl⟩ : syracuseStep 2164829 = 811811) (by norm_num)
theorem B2164853 : Blo 1441540 2164853 := bbase (se 5 (by rfl) ⟨101477, by rfl⟩ : syracuseStep 2164853 = 202955) (by norm_num)
theorem B2599037 : Blo 1441540 2599037 := bbase (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) (by norm_num)
theorem B2435197 : Blo 1441540 2435197 := bbase (se 3 (by rfl) ⟨456599, by rfl⟩ : syracuseStep 2435197 = 913199) (by norm_num)
theorem B4384901 : Blo 1441540 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B2164877 : Blo 1441540 2164877 := bbase (se 3 (by rfl) ⟨405914, by rfl⟩ : syracuseStep 2164877 = 811829) (by norm_num)
theorem B4106389 : Blo 1441540 4106389 := bbase (se 6 (by rfl) ⟨96243, by rfl⟩ : syracuseStep 4106389 = 192487) (by norm_num)
theorem B4868261 : Blo 1441540 4868261 := bbase (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) (by norm_num)
theorem B3246245 : Blo 1441540 3246245 := bbase (se 4 (by rfl) ⟨304335, by rfl⟩ : syracuseStep 3246245 = 608671) (by norm_num)
theorem B2164901 : Blo 1441540 2164901 := bbase (se 4 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 2164901 = 405919) (by norm_num)
theorem B2082997 : Blo 1441540 2082997 := bbase (se 5 (by rfl) ⟨97640, by rfl⟩ : syracuseStep 2082997 = 195281) (by norm_num)
theorem B2164925 : Blo 1441540 2164925 := bbase (se 3 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 2164925 = 811847) (by norm_num)
theorem B2435285 : Blo 1441540 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B2164949 : Blo 1441540 2164949 := bbase (se 7 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 2164949 = 50741) (by norm_num)
theorem B3246317 : Blo 1441540 3246317 := bbase (se 3 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 3246317 = 1217369) (by norm_num)
theorem B2164973 : Blo 1441540 2164973 := bbase (se 3 (by rfl) ⟨405932, by rfl⟩ : syracuseStep 2164973 = 811865) (by norm_num)
theorem B2164997 : Blo 1441540 2164997 := bbase (se 4 (by rfl) ⟨202968, by rfl⟩ : syracuseStep 2164997 = 405937) (by norm_num)
theorem B16427285 : Blo 1441540 16427285 := bbase (se 6 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 16427285 = 770029) (by norm_num)
theorem B2165021 : Blo 1441540 2165021 := bbase (se 3 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 2165021 = 811883) (by norm_num)
theorem B3246389 : Blo 1441540 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B2165045 : Blo 1441540 2165045 := bbase (se 5 (by rfl) ⟨101486, by rfl⟩ : syracuseStep 2165045 = 202973) (by norm_num)
theorem B2165069 : Blo 1441540 2165069 := bbase (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) (by norm_num)
theorem B2435413 : Blo 1441540 2435413 := bbase (se 10 (by rfl) ⟨3567, by rfl⟩ : syracuseStep 2435413 = 7135) (by norm_num)
theorem B2165093 : Blo 1441540 2165093 := bbase (se 4 (by rfl) ⟨202977, by rfl⟩ : syracuseStep 2165093 = 405955) (by norm_num)
theorem B2738549 : Blo 1441540 2738549 := bbase (se 5 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 2738549 = 256739) (by norm_num)
theorem B3246461 : Blo 1441540 3246461 := bbase (se 3 (by rfl) ⟨608711, by rfl⟩ : syracuseStep 3246461 = 1217423) (by norm_num)
theorem B2165117 : Blo 1441540 2165117 := bbase (se 3 (by rfl) ⟨405959, by rfl⟩ : syracuseStep 2165117 = 811919) (by norm_num)
theorem B3082637 : Blo 1441540 3082637 := bbase (se 3 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 3082637 = 1155989) (by norm_num)
theorem B3082645 : Blo 1441540 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B2165141 : Blo 1441540 2165141 := bbase (se 6 (by rfl) ⟨50745, by rfl⟩ : syracuseStep 2165141 = 101491) (by norm_num)
theorem B2435501 : Blo 1441540 2435501 := bbase (se 3 (by rfl) ⟨456656, by rfl⟩ : syracuseStep 2435501 = 913313) (by norm_num)
theorem B2165165 : Blo 1441540 2165165 := bbase (se 3 (by rfl) ⟨405968, by rfl⟩ : syracuseStep 2165165 = 811937) (by norm_num)
theorem B3246533 : Blo 1441540 3246533 := bbase (se 4 (by rfl) ⟨304362, by rfl⟩ : syracuseStep 3246533 = 608725) (by norm_num)
theorem B2165189 : Blo 1441540 2165189 := bbase (se 4 (by rfl) ⟨202986, by rfl⟩ : syracuseStep 2165189 = 405973) (by norm_num)
theorem B2165213 : Blo 1441540 2165213 := bbase (se 3 (by rfl) ⟨405977, by rfl⟩ : syracuseStep 2165213 = 811955) (by norm_num)
theorem B2165237 : Blo 1441540 2165237 := bbase (se 5 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 2165237 = 202991) (by norm_num)
theorem B2738701 : Blo 1441540 2738701 := bbase (se 3 (by rfl) ⟨513506, by rfl⟩ : syracuseStep 2738701 = 1027013) (by norm_num)
theorem B3246605 : Blo 1441540 3246605 := bbase (se 3 (by rfl) ⟨608738, by rfl⟩ : syracuseStep 3246605 = 1217477) (by norm_num)
theorem B2165261 : Blo 1441540 2165261 := bbase (se 3 (by rfl) ⟨405986, by rfl⟩ : syracuseStep 2165261 = 811973) (by norm_num)
theorem B2468381 : Blo 1441540 2468381 := bbase (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) (by norm_num)
theorem B2165285 : Blo 1441540 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B2435629 : Blo 1441540 2435629 := bbase (se 3 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 2435629 = 913361) (by norm_num)
theorem B2165309 : Blo 1441540 2165309 := bbase (se 3 (by rfl) ⟨405995, by rfl⟩ : syracuseStep 2165309 = 811991) (by norm_num)
theorem B4868693 : Blo 1441540 4868693 := bbase (se 8 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 4868693 = 57055) (by norm_num)
theorem B3246677 : Blo 1441540 3246677 := bbase (se 8 (by rfl) ⟨19023, by rfl⟩ : syracuseStep 3246677 = 38047) (by norm_num)
theorem B3467861 : Blo 1441540 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B2435717 : Blo 1441540 2435717 := bbase (se 4 (by rfl) ⟨228348, by rfl⟩ : syracuseStep 2435717 = 456697) (by norm_num)
theorem B3246749 : Blo 1441540 3246749 := bbase (se 3 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 3246749 = 1217531) (by norm_num)
theorem B3246821 : Blo 1441540 3246821 := bbase (se 4 (by rfl) ⟨304389, by rfl⟩ : syracuseStep 3246821 = 608779) (by norm_num)
theorem B2435845 : Blo 1441540 2435845 := bbase (se 4 (by rfl) ⟨228360, by rfl⟩ : syracuseStep 2435845 = 456721) (by norm_num)
theorem B3246893 : Blo 1441540 3246893 := bbase (se 3 (by rfl) ⟨608792, by rfl⟩ : syracuseStep 3246893 = 1217585) (by norm_num)
theorem B2739005 : Blo 1441540 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B2435933 : Blo 1441540 2435933 := bbase (se 3 (by rfl) ⟨456737, by rfl⟩ : syracuseStep 2435933 = 913475) (by norm_num)
theorem B3246965 : Blo 1441540 3246965 := bbase (se 5 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 3246965 = 304403) (by norm_num)
theorem B3247037 : Blo 1441540 3247037 := bbase (se 3 (by rfl) ⟨608819, by rfl⟩ : syracuseStep 3247037 = 1217639) (by norm_num)
theorem B6163445 : Blo 1441540 6163445 := bbase (se 5 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 6163445 = 577823) (by norm_num)
theorem B11111413 : Blo 1441540 11111413 := bbase (se 5 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 11111413 = 1041695) (by norm_num)
theorem B7302149 : Blo 1441540 7302149 := bbase (se 4 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 7302149 = 1369153) (by norm_num)
theorem B4869125 : Blo 1441540 4869125 := bbase (se 4 (by rfl) ⟨456480, by rfl⟩ : syracuseStep 4869125 = 912961) (by norm_num)
theorem B3247109 : Blo 1441540 3247109 := bbase (se 4 (by rfl) ⟨304416, by rfl⟩ : syracuseStep 3247109 = 608833) (by norm_num)
theorem B5475397 : Blo 1441540 5475397 := bbase (se 4 (by rfl) ⟨513318, by rfl⟩ : syracuseStep 5475397 = 1026637) (by norm_num)
theorem B3247181 : Blo 1441540 3247181 := bbase (se 3 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 3247181 = 1217693) (by norm_num)
theorem B8891477 : Blo 1441540 8891477 := bbase (se 8 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 8891477 = 104197) (by norm_num)
theorem B3247253 : Blo 1441540 3247253 := bbase (se 6 (by rfl) ⟨76107, by rfl⟩ : syracuseStep 3247253 = 152215) (by norm_num)
theorem B3247325 : Blo 1441540 3247325 := bbase (se 3 (by rfl) ⟨608873, by rfl⟩ : syracuseStep 3247325 = 1217747) (by norm_num)
theorem B6163685 : Blo 1441540 6163685 := bbase (se 4 (by rfl) ⟨577845, by rfl⟩ : syracuseStep 6163685 = 1155691) (by norm_num)
theorem B13864213 : Blo 1441540 13864213 := bbase (se 6 (by rfl) ⟨324942, by rfl⟩ : syracuseStep 13864213 = 649885) (by norm_num)
theorem B3247397 : Blo 1441540 3247397 := bbase (se 4 (by rfl) ⟨304443, by rfl⟩ : syracuseStep 3247397 = 608887) (by norm_num)
theorem B1461557 : Blo 1441540 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B1461569 : Blo 1441540 1461569 := bbase (se 2 (by rfl) ⟨548088, by rfl⟩ : syracuseStep 1461569 = 1096177) (by norm_num)
theorem B3247469 : Blo 1441540 3247469 := bbase (se 3 (by rfl) ⟨608900, by rfl⟩ : syracuseStep 3247469 = 1217801) (by norm_num)
theorem B5475701 : Blo 1441540 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B1731989 : Blo 1441540 1731989 := bbase (se 6 (by rfl) ⟨40593, by rfl⟩ : syracuseStep 1731989 = 81187) (by norm_num)
theorem B4869557 : Blo 1441540 4869557 := bbase (se 5 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 4869557 = 456521) (by norm_num)
theorem B3247541 : Blo 1441540 3247541 := bbase (se 5 (by rfl) ⟨152228, by rfl⟩ : syracuseStep 3247541 = 304457) (by norm_num)
theorem B3648989 : Blo 1441540 3648989 := bbase (se 3 (by rfl) ⟨684185, by rfl⟩ : syracuseStep 3648989 = 1368371) (by norm_num)
theorem B1756669 : Blo 1441540 1756669 := bbase (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) (by norm_num)
theorem B3247613 : Blo 1441540 3247613 := bbase (se 3 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 3247613 = 1217855) (by norm_num)
theorem B2739757 : Blo 1441540 2739757 := bbase (se 3 (by rfl) ⟨513704, by rfl⟩ : syracuseStep 2739757 = 1027409) (by norm_num)
theorem B3247685 : Blo 1441540 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B3247757 : Blo 1441540 3247757 := bbase (se 3 (by rfl) ⟨608954, by rfl⟩ : syracuseStep 3247757 = 1217909) (by norm_num)
theorem B2739901 : Blo 1441540 2739901 := bbase (se 3 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 2739901 = 1027463) (by norm_num)
theorem B3247829 : Blo 1441540 3247829 := bbase (se 7 (by rfl) ⟨38060, by rfl⟩ : syracuseStep 3247829 = 76121) (by norm_num)
theorem B3247901 : Blo 1441540 3247901 := bbase (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) (by norm_num)
theorem B3649333 : Blo 1441540 3649333 := bbase (se 5 (by rfl) ⟨171062, by rfl⟩ : syracuseStep 3649333 = 342125) (by norm_num)
theorem B2740061 : Blo 1441540 2740061 := bbase (se 3 (by rfl) ⟨513761, by rfl⟩ : syracuseStep 2740061 = 1027523) (by norm_num)
theorem B4869989 : Blo 1441540 4869989 := bbase (se 4 (by rfl) ⟨456561, by rfl⟩ : syracuseStep 4869989 = 913123) (by norm_num)
theorem B3288941 : Blo 1441540 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B3649445 : Blo 1441540 3649445 := bbase (se 4 (by rfl) ⟨342135, by rfl⟩ : syracuseStep 3649445 = 684271) (by norm_num)
theorem B1732537 : Blo 1441540 1732537 := bbase (se 2 (by rfl) ⟨649701, by rfl⟩ : syracuseStep 1732537 = 1299403) (by norm_num)
theorem B2740205 : Blo 1441540 2740205 := bbase (se 3 (by rfl) ⟨513788, by rfl⟩ : syracuseStep 2740205 = 1027577) (by norm_num)
theorem B3379229 : Blo 1441540 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B1732681 : Blo 1441540 1732681 := bbase (se 2 (by rfl) ⟨649755, by rfl⟩ : syracuseStep 1732681 = 1299511) (by norm_num)
theorem B3649637 : Blo 1441540 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B1462469 : Blo 1441540 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B4681957 : Blo 1441540 4681957 := bbase (se 4 (by rfl) ⟨438933, by rfl⟩ : syracuseStep 4681957 = 877867) (by norm_num)
theorem B1462501 : Blo 1441540 1462501 := bbase (se 4 (by rfl) ⟨137109, by rfl⟩ : syracuseStep 1462501 = 274219) (by norm_num)
theorem B7303445 : Blo 1441540 7303445 := bbase (se 6 (by rfl) ⟨171174, by rfl⟩ : syracuseStep 7303445 = 342349) (by norm_num)
theorem B4870421 : Blo 1441540 4870421 := bbase (se 6 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 4870421 = 228301) (by norm_num)
theorem B3649981 : Blo 1441540 3649981 := bbase (se 3 (by rfl) ⟨684371, by rfl⟩ : syracuseStep 3649981 = 1368743) (by norm_num)
theorem B12497429 : Blo 1441540 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B3650093 : Blo 1441540 3650093 := bbase (se 3 (by rfl) ⟨684392, by rfl⟩ : syracuseStep 3650093 = 1368785) (by norm_num)
theorem B9245269 : Blo 1441540 9245269 := bbase (se 8 (by rfl) ⟨54171, by rfl⟩ : syracuseStep 9245269 = 108343) (by norm_num)
theorem B28488341 : Blo 1441540 28488341 := bbase (se 6 (by rfl) ⟨667695, by rfl⟩ : syracuseStep 28488341 = 1335391) (by norm_num)
theorem B4870853 : Blo 1441540 4870853 := bbase (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) (by norm_num)
theorem B3650285 : Blo 1441540 3650285 := bbase (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) (by norm_num)
theorem B3208061 : Blo 1441540 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B2192293 : Blo 1441540 2192293 := bbase (se 4 (by rfl) ⟨205527, by rfl⟩ : syracuseStep 2192293 = 411055) (by norm_num)
theorem B4109237 : Blo 1441540 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B2192365 : Blo 1441540 2192365 := bbase (se 3 (by rfl) ⟨411068, by rfl⟩ : syracuseStep 2192365 = 822137) (by norm_num)
theorem B2634773 : Blo 1441540 2634773 := bbase (se 6 (by rfl) ⟨61752, by rfl⟩ : syracuseStep 2634773 = 123505) (by norm_num)
theorem B7402517 : Blo 1441540 7402517 := bbase (se 6 (by rfl) ⟨173496, by rfl⟩ : syracuseStep 7402517 = 346993) (by norm_num)
theorem B3650629 : Blo 1441540 3650629 := bbase (se 4 (by rfl) ⟨342246, by rfl⟩ : syracuseStep 3650629 = 684493) (by norm_num)
theorem B8008789 : Blo 1441540 8008789 := bbase (se 8 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 8008789 = 93853) (by norm_num)
theorem B1733729 : Blo 1441540 1733729 := bbase (se 2 (by rfl) ⟨650148, by rfl⟩ : syracuseStep 1733729 = 1300297) (by norm_num)
theorem B4871285 : Blo 1441540 4871285 := bbase (se 5 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 4871285 = 456683) (by norm_num)
theorem B3650741 : Blo 1441540 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B6935797 : Blo 1441540 6935797 := bbase (se 5 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 6935797 = 650231) (by norm_num)
theorem B24638741 : Blo 1441540 24638741 := bbase (se 6 (by rfl) ⟨577470, by rfl⟩ : syracuseStep 24638741 = 1154941) (by norm_num)
theorem B3650933 : Blo 1441540 3650933 := bbase (se 5 (by rfl) ⟨171137, by rfl⟩ : syracuseStep 3650933 = 342275) (by norm_num)
theorem B2053525 : Blo 1441540 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B1734061 : Blo 1441540 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B5477813 : Blo 1441540 5477813 := bbase (se 5 (by rfl) ⟨256772, by rfl⟩ : syracuseStep 5477813 = 513545) (by norm_num)
theorem B1668541 : Blo 1441540 1668541 := bbase (se 3 (by rfl) ⟨312851, by rfl⟩ : syracuseStep 1668541 = 625703) (by norm_num)
theorem B6165973 : Blo 1441540 6165973 := bbase (se 7 (by rfl) ⟨72257, by rfl⟩ : syracuseStep 6165973 = 144515) (by norm_num)
theorem B5846501 : Blo 1441540 5846501 := bbase (se 4 (by rfl) ⟨548109, by rfl⟩ : syracuseStep 5846501 = 1096219) (by norm_num)
theorem B7796245 : Blo 1441540 7796245 := bbase (se 6 (by rfl) ⟨182724, by rfl⟩ : syracuseStep 7796245 = 365449) (by norm_num)
theorem B7304741 : Blo 1441540 7304741 := bbase (se 4 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 7304741 = 1369639) (by norm_num)
theorem B4871717 : Blo 1441540 4871717 := bbase (se 4 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 4871717 = 913447) (by norm_num)
theorem B4937365 : Blo 1441540 4937365 := bbase (se 6 (by rfl) ⟨115719, by rfl⟩ : syracuseStep 4937365 = 231439) (by norm_num)
theorem B3651277 : Blo 1441540 3651277 := bbase (se 3 (by rfl) ⟨684614, by rfl⟩ : syracuseStep 3651277 = 1369229) (by norm_num)
theorem B5478101 : Blo 1441540 5478101 := bbase (se 7 (by rfl) ⟨64196, by rfl⟩ : syracuseStep 5478101 = 128393) (by norm_num)
theorem B1824545 : Blo 1441540 1824545 := bbase (se 2 (by rfl) ⟨684204, by rfl⟩ : syracuseStep 1824545 = 1368409) (by norm_num)
theorem B3651389 : Blo 1441540 3651389 := bbase (se 3 (by rfl) ⟨684635, by rfl⟩ : syracuseStep 3651389 = 1369271) (by norm_num)
theorem B1824601 : Blo 1441540 1824601 := bbase (se 2 (by rfl) ⟨684225, by rfl⟩ : syracuseStep 1824601 = 1368451) (by norm_num)
theorem B1824697 : Blo 1441540 1824697 := bbase (se 2 (by rfl) ⟨684261, by rfl⟩ : syracuseStep 1824697 = 1368523) (by norm_num)
theorem B2054117 : Blo 1441540 2054117 := bbase (se 4 (by rfl) ⟨192573, by rfl⟩ : syracuseStep 2054117 = 385147) (by norm_num)
theorem B9369589 : Blo 1441540 9369589 := bbase (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) (by norm_num)
theorem B3651581 : Blo 1441540 3651581 := bbase (se 3 (by rfl) ⟨684671, by rfl⟩ : syracuseStep 3651581 = 1369343) (by norm_num)
theorem B2054197 : Blo 1441540 2054197 := bbase (se 5 (by rfl) ⟨96290, by rfl⟩ : syracuseStep 2054197 = 192581) (by norm_num)
theorem B4388917 : Blo 1441540 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B4110421 : Blo 1441540 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B1824869 : Blo 1441540 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B1824925 : Blo 1441540 1824925 := bbase (se 3 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 1824925 = 684347) (by norm_num)
theorem B2054317 : Blo 1441540 2054317 := bbase (se 3 (by rfl) ⟨385184, by rfl⟩ : syracuseStep 2054317 = 770369) (by norm_num)
theorem B4618421 : Blo 1441540 4618421 := bbase (se 5 (by rfl) ⟨216488, by rfl⟩ : syracuseStep 4618421 = 432977) (by norm_num)
theorem B4110581 : Blo 1441540 4110581 := bbase (se 5 (by rfl) ⟨192683, by rfl⟩ : syracuseStep 4110581 = 385367) (by norm_num)
theorem B1825021 : Blo 1441540 1825021 := bbase (se 3 (by rfl) ⟨342191, by rfl⟩ : syracuseStep 1825021 = 684383) (by norm_num)
theorem B2054413 : Blo 1441540 2054413 := bbase (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) (by norm_num)
theorem B2922797 : Blo 1441540 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B1849645 : Blo 1441540 1849645 := bbase (se 3 (by rfl) ⟨346808, by rfl⟩ : syracuseStep 1849645 = 693617) (by norm_num)
theorem B3701045 : Blo 1441540 3701045 := bbase (se 5 (by rfl) ⟨173486, by rfl⟩ : syracuseStep 3701045 = 346973) (by norm_num)
theorem B3651925 : Blo 1441540 3651925 := bbase (se 10 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 3651925 = 10699) (by norm_num)
theorem B1825193 : Blo 1441540 1825193 := bbase (se 2 (by rfl) ⟨684447, by rfl⟩ : syracuseStep 1825193 = 1368895) (by norm_num)
theorem B8214965 : Blo 1441540 8214965 := bbase (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) (by norm_num)
theorem B3652037 : Blo 1441540 3652037 := bbase (se 4 (by rfl) ⟨342378, by rfl⟩ : syracuseStep 3652037 = 684757) (by norm_num)
theorem B1825249 : Blo 1441540 1825249 := bbase (se 2 (by rfl) ⟨684468, by rfl⟩ : syracuseStep 1825249 = 1368937) (by norm_num)
theorem B2193893 : Blo 1441540 2193893 := bbase (se 4 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 2193893 = 411355) (by norm_num)
theorem B1825345 : Blo 1441540 1825345 := bbase (se 2 (by rfl) ⟨684504, by rfl⟩ : syracuseStep 1825345 = 1369009) (by norm_num)
theorem B3652229 : Blo 1441540 3652229 := bbase (se 4 (by rfl) ⟨342396, by rfl⟩ : syracuseStep 3652229 = 684793) (by norm_num)
theorem B1645205 : Blo 1441540 1645205 := bbase (se 6 (by rfl) ⟨38559, by rfl⟩ : syracuseStep 1645205 = 77119) (by norm_num)
theorem B6576805 : Blo 1441540 6576805 := bbase (se 4 (by rfl) ⟨616575, by rfl⟩ : syracuseStep 6576805 = 1233151) (by norm_num)
theorem B3463901 : Blo 1441540 3463901 := bbase (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) (by norm_num)
theorem B1825517 : Blo 1441540 1825517 := bbase (se 3 (by rfl) ⟨342284, by rfl⟩ : syracuseStep 1825517 = 684569) (by norm_num)
theorem B2054909 : Blo 1441540 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B1825573 : Blo 1441540 1825573 := bbase (se 4 (by rfl) ⟨171147, by rfl⟩ : syracuseStep 1825573 = 342295) (by norm_num)
theorem B7306037 : Blo 1441540 7306037 := bbase (se 5 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 7306037 = 684941) (by norm_num)
theorem B3078989 : Blo 1441540 3078989 := bbase (se 3 (by rfl) ⟨577310, by rfl⟩ : syracuseStep 3078989 = 1154621) (by norm_num)
theorem B2923381 : Blo 1441540 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B5479285 : Blo 1441540 5479285 := bbase (se 5 (by rfl) ⟨256841, by rfl⟩ : syracuseStep 5479285 = 513683) (by norm_num)
theorem B3701629 : Blo 1441540 3701629 := bbase (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) (by norm_num)
theorem B1825669 : Blo 1441540 1825669 := bbase (se 4 (by rfl) ⟨171156, by rfl⟩ : syracuseStep 1825669 = 342313) (by norm_num)
theorem B3079109 : Blo 1441540 3079109 := bbase (se 4 (by rfl) ⟨288666, by rfl⟩ : syracuseStep 3079109 = 577333) (by norm_num)
theorem B3652573 : Blo 1441540 3652573 := bbase (se 3 (by rfl) ⟨684857, by rfl⟩ : syracuseStep 3652573 = 1369715) (by norm_num)
theorem B2309165 : Blo 1441540 2309165 := bbase (se 3 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 2309165 = 865937) (by norm_num)
theorem B1825841 : Blo 1441540 1825841 := bbase (se 2 (by rfl) ⟨684690, by rfl⟩ : syracuseStep 1825841 = 1369381) (by norm_num)
theorem B3513413 : Blo 1441540 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B3652685 : Blo 1441540 3652685 := bbase (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) (by norm_num)
theorem B1825897 : Blo 1441540 1825897 := bbase (se 2 (by rfl) ⟨684711, by rfl⟩ : syracuseStep 1825897 = 1369423) (by norm_num)
theorem B6577301 : Blo 1441540 6577301 := bbase (se 6 (by rfl) ⟨154155, by rfl⟩ : syracuseStep 6577301 = 308311) (by norm_num)
theorem B5479589 : Blo 1441540 5479589 := bbase (se 4 (by rfl) ⟨513711, by rfl⟩ : syracuseStep 5479589 = 1027423) (by norm_num)
theorem B1825993 : Blo 1441540 1825993 := bbase (se 2 (by rfl) ⟨684747, by rfl⟩ : syracuseStep 1825993 = 1369495) (by norm_num)
theorem B4865237 : Blo 1441540 4865237 := bbase (se 7 (by rfl) ⟨57014, by rfl⟩ : syracuseStep 4865237 = 114029) (by norm_num)
theorem B7298261 : Blo 1441540 7298261 := bbase (se 7 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 7298261 = 171053) (by norm_num)
theorem B2342125 : Blo 1441540 2342125 := bbase (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) (by norm_num)
theorem B3702029 : Blo 1441540 3702029 := bbase (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) (by norm_num)
theorem B3652877 : Blo 1441540 3652877 := bbase (se 3 (by rfl) ⟨684914, by rfl⟩ : syracuseStep 3652877 = 1369829) (by norm_num)
theorem B1539409 : Blo 1441540 1539409 := bbase (se 2 (by rfl) ⟨577278, by rfl⟩ : syracuseStep 1539409 = 1154557) (by norm_num)
theorem B1826165 : Blo 1441540 1826165 := bbase (se 5 (by rfl) ⟨85601, by rfl⟩ : syracuseStep 1826165 = 171203) (by norm_num)
theorem B1826221 : Blo 1441540 1826221 := bbase (se 3 (by rfl) ⟨342416, by rfl⟩ : syracuseStep 1826221 = 684833) (by norm_num)
theorem B3243509 : Blo 1441540 3243509 := bbase (se 5 (by rfl) ⟨152039, by rfl⟩ : syracuseStep 3243509 = 304079) (by norm_num)
theorem B1646077 : Blo 1441540 1646077 := bbase (se 3 (by rfl) ⟨308639, by rfl⟩ : syracuseStep 1646077 = 617279) (by norm_num)
theorem B1826317 : Blo 1441540 1826317 := bbase (se 3 (by rfl) ⟨342434, by rfl⟩ : syracuseStep 1826317 = 684869) (by norm_num)
theorem B2309677 : Blo 1441540 2309677 := bbase (se 3 (by rfl) ⟨433064, by rfl⟩ : syracuseStep 2309677 = 866129) (by norm_num)
theorem B3243581 : Blo 1441540 3243581 := bbase (se 3 (by rfl) ⟨608171, by rfl⟩ : syracuseStep 3243581 = 1216343) (by norm_num)
theorem B3079741 : Blo 1441540 3079741 := bbase (se 3 (by rfl) ⟨577451, by rfl⟩ : syracuseStep 3079741 = 1154903) (by norm_num)
theorem B2432605 : Blo 1441540 2432605 := bbase (se 3 (by rfl) ⟨456113, by rfl⟩ : syracuseStep 2432605 = 912227) (by norm_num)
theorem B3653221 : Blo 1441540 3653221 := bbase (se 4 (by rfl) ⟨342489, by rfl⟩ : syracuseStep 3653221 = 684979) (by norm_num)
theorem B14810741 : Blo 1441540 14810741 := bbase (se 5 (by rfl) ⟨694253, by rfl⟩ : syracuseStep 14810741 = 1388507) (by norm_num)
theorem B1949309 : Blo 1441540 1949309 := bbase (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) (by norm_num)
theorem B3243653 : Blo 1441540 3243653 := bbase (se 4 (by rfl) ⟨304092, by rfl⟩ : syracuseStep 3243653 = 608185) (by norm_num)
theorem B4865669 : Blo 1441540 4865669 := bbase (se 4 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 4865669 = 912313) (by norm_num)
theorem B2162333 : Blo 1441540 2162333 := bbase (se 3 (by rfl) ⟨405437, by rfl⟩ : syracuseStep 2162333 = 810875) (by norm_num)
theorem B2162357 : Blo 1441540 2162357 := bbase (se 5 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 2162357 = 202721) (by norm_num)
theorem B2432693 : Blo 1441540 2432693 := bbase (se 5 (by rfl) ⟨114032, by rfl⟩ : syracuseStep 2432693 = 228065) (by norm_num)
theorem B1826489 : Blo 1441540 1826489 := bbase (se 2 (by rfl) ⟨684933, by rfl⟩ : syracuseStep 1826489 = 1369867) (by norm_num)
theorem B2162381 : Blo 1441540 2162381 := bbase (se 3 (by rfl) ⟨405446, by rfl⟩ : syracuseStep 2162381 = 810893) (by norm_num)
theorem B3243725 : Blo 1441540 3243725 := bbase (se 3 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 3243725 = 1216397) (by norm_num)
theorem B3653333 : Blo 1441540 3653333 := bbase (se 7 (by rfl) ⟨42812, by rfl⟩ : syracuseStep 3653333 = 85625) (by norm_num)
theorem B2162405 : Blo 1441540 2162405 := bbase (se 4 (by rfl) ⟨202725, by rfl⟩ : syracuseStep 2162405 = 405451) (by norm_num)
theorem B1621741 : Blo 1441540 1621741 := bbase (se 3 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 1621741 = 608153) (by norm_num)
theorem B1826545 : Blo 1441540 1826545 := bbase (se 2 (by rfl) ⟨684954, by rfl⟩ : syracuseStep 1826545 = 1369909) (by norm_num)
theorem B2162429 : Blo 1441540 2162429 := bbase (se 3 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 2162429 = 810911) (by norm_num)
theorem B1539853 : Blo 1441540 1539853 := bbase (se 3 (by rfl) ⟨288722, by rfl⟩ : syracuseStep 1539853 = 577445) (by norm_num)
theorem B1621777 : Blo 1441540 1621777 := bbase (se 2 (by rfl) ⟨608166, by rfl⟩ : syracuseStep 1621777 = 1216333) (by norm_num)
theorem B2162453 : Blo 1441540 2162453 := bbase (se 6 (by rfl) ⟨50682, by rfl⟩ : syracuseStep 2162453 = 101365) (by norm_num)
theorem B3243797 : Blo 1441540 3243797 := bbase (se 6 (by rfl) ⟨76026, by rfl⟩ : syracuseStep 3243797 = 152053) (by norm_num)
theorem B2162477 : Blo 1441540 2162477 := bbase (se 3 (by rfl) ⟨405464, by rfl⟩ : syracuseStep 2162477 = 810929) (by norm_num)
theorem B1621813 : Blo 1441540 1621813 := bbase (se 5 (by rfl) ⟨76022, by rfl⟩ : syracuseStep 1621813 = 152045) (by norm_num)
theorem B2432821 : Blo 1441540 2432821 := bbase (se 5 (by rfl) ⟨114038, by rfl⟩ : syracuseStep 2432821 = 228077) (by norm_num)
theorem B2162501 : Blo 1441540 2162501 := bbase (se 4 (by rfl) ⟨202734, by rfl⟩ : syracuseStep 2162501 = 405469) (by norm_num)
theorem B1826641 : Blo 1441540 1826641 := bbase (se 2 (by rfl) ⟨684990, by rfl⟩ : syracuseStep 1826641 = 1369981) (by norm_num)
theorem B3702613 : Blo 1441540 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B1621849 : Blo 1441540 1621849 := bbase (se 2 (by rfl) ⟨608193, by rfl⟩ : syracuseStep 1621849 = 1216387) (by norm_num)
theorem B2162525 : Blo 1441540 2162525 := bbase (se 3 (by rfl) ⟨405473, by rfl⟩ : syracuseStep 2162525 = 810947) (by norm_num)
theorem B3243869 : Blo 1441540 3243869 := bbase (se 3 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 3243869 = 1216451) (by norm_num)
theorem B5201765 : Blo 1441540 5201765 := bbase (se 4 (by rfl) ⟨487665, by rfl⟩ : syracuseStep 5201765 = 975331) (by norm_num)
theorem B2162549 : Blo 1441540 2162549 := bbase (se 5 (by rfl) ⟨101369, by rfl⟩ : syracuseStep 2162549 = 202739) (by norm_num)
theorem B10960757 : Blo 1441540 10960757 := bbase (se 5 (by rfl) ⟨513785, by rfl⟩ : syracuseStep 10960757 = 1027571) (by norm_num)
theorem B1621885 : Blo 1441540 1621885 := bbase (se 3 (by rfl) ⟨304103, by rfl⟩ : syracuseStep 1621885 = 608207) (by norm_num)
theorem B1539973 : Blo 1441540 1539973 := bbase (se 4 (by rfl) ⟨144372, by rfl⟩ : syracuseStep 1539973 = 288745) (by norm_num)
theorem B2432909 : Blo 1441540 2432909 := bbase (se 3 (by rfl) ⟨456170, by rfl⟩ : syracuseStep 2432909 = 912341) (by norm_num)
theorem B2162573 : Blo 1441540 2162573 := bbase (se 3 (by rfl) ⟨405482, by rfl⟩ : syracuseStep 2162573 = 810965) (by norm_num)
theorem B1851277 : Blo 1441540 1851277 := bbase (se 3 (by rfl) ⟨347114, by rfl⟩ : syracuseStep 1851277 = 694229) (by norm_num)
theorem B29998997 : Blo 1441540 29998997 := bbase (se 6 (by rfl) ⟨703101, by rfl⟩ : syracuseStep 29998997 = 1406203) (by norm_num)
theorem B3653525 : Blo 1441540 3653525 := bbase (se 6 (by rfl) ⟨85629, by rfl⟩ : syracuseStep 3653525 = 171259) (by norm_num)
theorem B1621921 : Blo 1441540 1621921 := bbase (se 2 (by rfl) ⟨608220, by rfl⟩ : syracuseStep 1621921 = 1216441) (by norm_num)
theorem B2162597 : Blo 1441540 2162597 := bbase (se 4 (by rfl) ⟨202743, by rfl⟩ : syracuseStep 2162597 = 405487) (by norm_num)
theorem B3243941 : Blo 1441540 3243941 := bbase (se 4 (by rfl) ⟨304119, by rfl⟩ : syracuseStep 3243941 = 608239) (by norm_num)
theorem B2162621 : Blo 1441540 2162621 := bbase (se 3 (by rfl) ⟨405491, by rfl⟩ : syracuseStep 2162621 = 810983) (by norm_num)
theorem B1621957 : Blo 1441540 1621957 := bbase (se 4 (by rfl) ⟨152058, by rfl⟩ : syracuseStep 1621957 = 304117) (by norm_num)
theorem B2162645 : Blo 1441540 2162645 := bbase (se 7 (by rfl) ⟨25343, by rfl⟩ : syracuseStep 2162645 = 50687) (by norm_num)
theorem B1621993 : Blo 1441540 1621993 := bbase (se 2 (by rfl) ⟨608247, by rfl⟩ : syracuseStep 1621993 = 1216495) (by norm_num)
theorem B2162669 : Blo 1441540 2162669 := bbase (se 3 (by rfl) ⟨405500, by rfl⟩ : syracuseStep 2162669 = 811001) (by norm_num)
theorem B3244013 : Blo 1441540 3244013 := bbase (se 3 (by rfl) ⟨608252, by rfl⟩ : syracuseStep 3244013 = 1216505) (by norm_num)
theorem B2310133 : Blo 1441540 2310133 := bbase (se 5 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 2310133 = 216575) (by norm_num)
theorem B4620277 : Blo 1441540 4620277 := bbase (se 5 (by rfl) ⟨216575, by rfl⟩ : syracuseStep 4620277 = 433151) (by norm_num)
theorem B1826813 : Blo 1441540 1826813 := bbase (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) (by norm_num)
theorem B1441795 : Blo 1441540 1441795 := bstep (se 1 (by rfl) ⟨1081346, by rfl⟩ : syracuseStep 1441795 = 2162693) B2162693
theorem B3244049 : Blo 1441540 3244049 := bstep (se 2 (by rfl) ⟨1216518, by rfl⟩ : syracuseStep 3244049 = 2433037) B2433037
theorem B2162705 : Blo 1441540 2162705 := bstep (se 2 (by rfl) ⟨811014, by rfl⟩ : syracuseStep 2162705 = 1622029) B1622029
theorem B1441811 : Blo 1441540 1441811 := bstep (se 1 (by rfl) ⟨1081358, by rfl⟩ : syracuseStep 1441811 = 2162717) B2162717
theorem B2252819 : Blo 1441540 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B3244067 : Blo 1441540 3244067 := bstep (se 1 (by rfl) ⟨2433050, by rfl⟩ : syracuseStep 3244067 = 4866101) B4866101
theorem B2162723 : Blo 1441540 2162723 := bstep (se 1 (by rfl) ⟨1622042, by rfl⟩ : syracuseStep 2162723 = 3244085) B3244085
theorem B1441827 : Blo 1441540 1441827 := bstep (se 1 (by rfl) ⟨1081370, by rfl⟩ : syracuseStep 1441827 = 2162741) B2162741
theorem B1441843 : Blo 1441540 1441843 := bstep (se 1 (by rfl) ⟨1081382, by rfl⟩ : syracuseStep 1441843 = 2162765) B2162765
theorem B2162753 : Blo 1441540 2162753 := bstep (se 2 (by rfl) ⟨811032, by rfl⟩ : syracuseStep 2162753 = 1622065) B1622065
theorem B2433091 : Blo 1441540 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B1622083 : Blo 1441540 1622083 := bstep (se 1 (by rfl) ⟨1216562, by rfl⟩ : syracuseStep 1622083 = 2433125) B2433125
theorem B1441859 : Blo 1441540 1441859 := bstep (se 1 (by rfl) ⟨1081394, by rfl⟩ : syracuseStep 1441859 = 2162789) B2162789
theorem B2162771 : Blo 1441540 2162771 := bstep (se 1 (by rfl) ⟨1622078, by rfl⟩ : syracuseStep 2162771 = 3244157) B3244157
theorem B1441875 : Blo 1441540 1441875 := bstep (se 1 (by rfl) ⟨1081406, by rfl⟩ : syracuseStep 1441875 = 2162813) B2162813
theorem B1441891 : Blo 1441540 1441891 := bstep (se 1 (by rfl) ⟨1081418, by rfl⟩ : syracuseStep 1441891 = 2162837) B2162837
theorem B2162801 : Blo 1441540 2162801 := bstep (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) B1622101
theorem B5480561 : Blo 1441540 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B1441907 : Blo 1441540 1441907 := bstep (se 1 (by rfl) ⟨1081430, by rfl⟩ : syracuseStep 1441907 = 2162861) B2162861
theorem B2162819 : Blo 1441540 2162819 := bstep (se 1 (by rfl) ⟨1622114, by rfl⟩ : syracuseStep 2162819 = 3244229) B3244229
theorem B1441923 : Blo 1441540 1441923 := bstep (se 1 (by rfl) ⟨1081442, by rfl⟩ : syracuseStep 1441923 = 2162885) B2162885
theorem B1441939 : Blo 1441540 1441939 := bstep (se 1 (by rfl) ⟨1081454, by rfl⟩ : syracuseStep 1441939 = 2162909) B2162909
theorem B2162849 : Blo 1441540 2162849 := bstep (se 2 (by rfl) ⟨811068, by rfl⟩ : syracuseStep 2162849 = 1622137) B1622137
theorem B1441955 : Blo 1441540 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B2162867 : Blo 1441540 2162867 := bstep (se 1 (by rfl) ⟨1622150, by rfl⟩ : syracuseStep 2162867 = 3244301) B3244301
theorem B1441971 : Blo 1441540 1441971 := bstep (se 1 (by rfl) ⟨1081478, by rfl⟩ : syracuseStep 1441971 = 2162957) B2162957
theorem B1441987 : Blo 1441540 1441987 := bstep (se 1 (by rfl) ⟨1081490, by rfl⟩ : syracuseStep 1441987 = 2162981) B2162981
theorem B2433233 : Blo 1441540 2433233 := bstep (se 2 (by rfl) ⟨912462, by rfl⟩ : syracuseStep 2433233 = 1824925) B1824925
theorem B2162897 : Blo 1441540 2162897 := bstep (se 2 (by rfl) ⟨811086, by rfl⟩ : syracuseStep 2162897 = 1622173) B1622173
theorem B1622227 : Blo 1441540 1622227 := bstep (se 1 (by rfl) ⟨1216670, by rfl⟩ : syracuseStep 1622227 = 2433341) B2433341
theorem B1442003 : Blo 1441540 1442003 := bstep (se 1 (by rfl) ⟨1081502, by rfl⟩ : syracuseStep 1442003 = 2163005) B2163005
theorem B2162915 : Blo 1441540 2162915 := bstep (se 1 (by rfl) ⟨1622186, by rfl⟩ : syracuseStep 2162915 = 3244373) B3244373
theorem B1442019 : Blo 1441540 1442019 := bstep (se 1 (by rfl) ⟨1081514, by rfl⟩ : syracuseStep 1442019 = 2163029) B2163029
theorem B2777329 : Blo 1441540 2777329 := bstep (se 2 (by rfl) ⟨1041498, by rfl⟩ : syracuseStep 2777329 = 2082997) B2082997
theorem B1442035 : Blo 1441540 1442035 := bstep (se 1 (by rfl) ⟨1081526, by rfl⟩ : syracuseStep 1442035 = 2163053) B2163053
theorem B2162945 : Blo 1441540 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B1442051 : Blo 1441540 1442051 := bstep (se 1 (by rfl) ⟨1081538, by rfl⟩ : syracuseStep 1442051 = 2163077) B2163077
theorem B4866317 : Blo 1441540 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B2162963 : Blo 1441540 2162963 := bstep (se 1 (by rfl) ⟨1622222, by rfl⟩ : syracuseStep 2162963 = 3244445) B3244445
theorem B1442067 : Blo 1441540 1442067 := bstep (se 1 (by rfl) ⟨1081550, by rfl⟩ : syracuseStep 1442067 = 2163101) B2163101
theorem B1442083 : Blo 1441540 1442083 := bstep (se 1 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 1442083 = 2163125) B2163125
theorem B6242609 : Blo 1441540 6242609 := bstep (se 2 (by rfl) ⟨2340978, by rfl⟩ : syracuseStep 6242609 = 4681957) B4681957
theorem B3244337 : Blo 1441540 3244337 := bstep (se 2 (by rfl) ⟨1216626, by rfl⟩ : syracuseStep 3244337 = 2433253) B2433253
theorem B2162993 : Blo 1441540 2162993 := bstep (se 2 (by rfl) ⟨811122, by rfl⟩ : syracuseStep 2162993 = 1622245) B1622245
theorem B1442099 : Blo 1441540 1442099 := bstep (se 1 (by rfl) ⟨1081574, by rfl⟩ : syracuseStep 1442099 = 2163149) B2163149
theorem B1950001 : Blo 1441540 1950001 := bstep (se 2 (by rfl) ⟨731250, by rfl⟩ : syracuseStep 1950001 = 1462501) B1462501
theorem B4866371 : Blo 1441540 4866371 := bstep (se 1 (by rfl) ⟨3649778, by rfl⟩ : syracuseStep 4866371 = 7299557) B7299557
theorem B3244355 : Blo 1441540 3244355 := bstep (se 1 (by rfl) ⟨2433266, by rfl⟩ : syracuseStep 3244355 = 4866533) B4866533
theorem B2163011 : Blo 1441540 2163011 := bstep (se 1 (by rfl) ⟨1622258, by rfl⟩ : syracuseStep 2163011 = 3244517) B3244517
theorem B1442115 : Blo 1441540 1442115 := bstep (se 1 (by rfl) ⟨1081586, by rfl⟩ : syracuseStep 1442115 = 2163173) B2163173
theorem B2433361 : Blo 1441540 2433361 := bstep (se 2 (by rfl) ⟨912510, by rfl⟩ : syracuseStep 2433361 = 1825021) B1825021
theorem B1442131 : Blo 1441540 1442131 := bstep (se 1 (by rfl) ⟨1081598, by rfl⟩ : syracuseStep 1442131 = 2163197) B2163197
theorem B2163041 : Blo 1441540 2163041 := bstep (se 2 (by rfl) ⟨811140, by rfl⟩ : syracuseStep 2163041 = 1622281) B1622281
theorem B1622371 : Blo 1441540 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B1442147 : Blo 1441540 1442147 := bstep (se 1 (by rfl) ⟨1081610, by rfl⟩ : syracuseStep 1442147 = 2163221) B2163221
theorem B2433395 : Blo 1441540 2433395 := bstep (se 1 (by rfl) ⟨1825046, by rfl⟩ : syracuseStep 2433395 = 3650093) B3650093
theorem B2163059 : Blo 1441540 2163059 := bstep (se 1 (by rfl) ⟨1622294, by rfl⟩ : syracuseStep 2163059 = 3244589) B3244589
theorem B1442163 : Blo 1441540 1442163 := bstep (se 1 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 1442163 = 2163245) B2163245
theorem B1442179 : Blo 1441540 1442179 := bstep (se 1 (by rfl) ⟨1081634, by rfl⟩ : syracuseStep 1442179 = 2163269) B2163269
theorem B9240965 : Blo 1441540 9240965 := bstep (se 4 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 9240965 = 1732681) B1732681
theorem B2163089 : Blo 1441540 2163089 := bstep (se 2 (by rfl) ⟨811158, by rfl⟩ : syracuseStep 2163089 = 1622317) B1622317
theorem B1442195 : Blo 1441540 1442195 := bstep (se 1 (by rfl) ⟨1081646, by rfl⟩ : syracuseStep 1442195 = 2163293) B2163293
theorem B2163107 : Blo 1441540 2163107 := bstep (se 1 (by rfl) ⟨1622330, by rfl⟩ : syracuseStep 2163107 = 3244661) B3244661
theorem B1442211 : Blo 1441540 1442211 := bstep (se 1 (by rfl) ⟨1081658, by rfl⟩ : syracuseStep 1442211 = 2163317) B2163317
theorem B1442227 : Blo 1441540 1442227 := bstep (se 1 (by rfl) ⟨1081670, by rfl⟩ : syracuseStep 1442227 = 2163341) B2163341
theorem B2163137 : Blo 1441540 2163137 := bstep (se 2 (by rfl) ⟨811176, by rfl⟩ : syracuseStep 2163137 = 1622353) B1622353
theorem B1442243 : Blo 1441540 1442243 := bstep (se 1 (by rfl) ⟨1081682, by rfl⟩ : syracuseStep 1442243 = 2163365) B2163365
theorem B4620739 : Blo 1441540 4620739 := bstep (se 1 (by rfl) ⟨3465554, by rfl⟩ : syracuseStep 4620739 = 6931109) B6931109
theorem B2163155 : Blo 1441540 2163155 := bstep (se 1 (by rfl) ⟨1622366, by rfl⟩ : syracuseStep 2163155 = 3244733) B3244733
theorem B1442259 : Blo 1441540 1442259 := bstep (se 1 (by rfl) ⟨1081694, by rfl⟩ : syracuseStep 1442259 = 2163389) B2163389
theorem B1442275 : Blo 1441540 1442275 := bstep (se 1 (by rfl) ⟨1081706, by rfl⟩ : syracuseStep 1442275 = 2163413) B2163413
theorem B2163185 : Blo 1441540 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B2433523 : Blo 1441540 2433523 := bstep (se 1 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 2433523 = 3650285) B3650285
theorem B1622515 : Blo 1441540 1622515 := bstep (se 1 (by rfl) ⟨1216886, by rfl⟩ : syracuseStep 1622515 = 2433773) B2433773
theorem B1442291 : Blo 1441540 1442291 := bstep (se 1 (by rfl) ⟨1081718, by rfl⟩ : syracuseStep 1442291 = 2163437) B2163437
theorem B2163203 : Blo 1441540 2163203 := bstep (se 1 (by rfl) ⟨1622402, by rfl⟩ : syracuseStep 2163203 = 3244805) B3244805
theorem B1442307 : Blo 1441540 1442307 := bstep (se 1 (by rfl) ⟨1081730, by rfl⟩ : syracuseStep 1442307 = 2163461) B2163461
theorem B3899917 : Blo 1441540 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B1442323 : Blo 1441540 1442323 := bstep (se 1 (by rfl) ⟨1081742, by rfl⟩ : syracuseStep 1442323 = 2163485) B2163485
theorem B2163233 : Blo 1441540 2163233 := bstep (se 2 (by rfl) ⟨811212, by rfl⟩ : syracuseStep 2163233 = 1622425) B1622425
theorem B1442339 : Blo 1441540 1442339 := bstep (se 1 (by rfl) ⟨1081754, by rfl⟩ : syracuseStep 1442339 = 2163509) B2163509
theorem B2163251 : Blo 1441540 2163251 := bstep (se 1 (by rfl) ⟨1622438, by rfl⟩ : syracuseStep 2163251 = 3244877) B3244877
theorem B1442355 : Blo 1441540 1442355 := bstep (se 1 (by rfl) ⟨1081766, by rfl⟩ : syracuseStep 1442355 = 2163533) B2163533
theorem B1442371 : Blo 1441540 1442371 := bstep (se 1 (by rfl) ⟨1081778, by rfl⟩ : syracuseStep 1442371 = 2163557) B2163557
theorem B4866641 : Blo 1441540 4866641 := bstep (se 2 (by rfl) ⟨1824990, by rfl⟩ : syracuseStep 4866641 = 3649981) B3649981
theorem B3244625 : Blo 1441540 3244625 := bstep (se 2 (by rfl) ⟨1216734, by rfl⟩ : syracuseStep 3244625 = 2433469) B2433469
theorem B2163281 : Blo 1441540 2163281 := bstep (se 2 (by rfl) ⟨811230, by rfl⟩ : syracuseStep 2163281 = 1622461) B1622461
theorem B2138707 : Blo 1441540 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1442387 : Blo 1441540 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B3244643 : Blo 1441540 3244643 := bstep (se 1 (by rfl) ⟨2433482, by rfl⟩ : syracuseStep 3244643 = 4866965) B4866965
theorem B2163299 : Blo 1441540 2163299 := bstep (se 1 (by rfl) ⟨1622474, by rfl⟩ : syracuseStep 2163299 = 3244949) B3244949
theorem B1442403 : Blo 1441540 1442403 := bstep (se 1 (by rfl) ⟨1081802, by rfl⟩ : syracuseStep 1442403 = 2163605) B2163605
theorem B1442419 : Blo 1441540 1442419 := bstep (se 1 (by rfl) ⟨1081814, by rfl⟩ : syracuseStep 1442419 = 2163629) B2163629
theorem B2433665 : Blo 1441540 2433665 := bstep (se 2 (by rfl) ⟨912624, by rfl⟩ : syracuseStep 2433665 = 1825249) B1825249
theorem B2163329 : Blo 1441540 2163329 := bstep (se 2 (by rfl) ⟨811248, by rfl⟩ : syracuseStep 2163329 = 1622497) B1622497
theorem B1622659 : Blo 1441540 1622659 := bstep (se 1 (by rfl) ⟨1216994, by rfl⟩ : syracuseStep 1622659 = 2433989) B2433989
theorem B1442435 : Blo 1441540 1442435 := bstep (se 1 (by rfl) ⟨1081826, by rfl⟩ : syracuseStep 1442435 = 2163653) B2163653
theorem B2163347 : Blo 1441540 2163347 := bstep (se 1 (by rfl) ⟨1622510, by rfl⟩ : syracuseStep 2163347 = 3245021) B3245021
theorem B1442451 : Blo 1441540 1442451 := bstep (se 1 (by rfl) ⟨1081838, by rfl⟩ : syracuseStep 1442451 = 2163677) B2163677
theorem B2736803 : Blo 1441540 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B1442467 : Blo 1441540 1442467 := bstep (se 1 (by rfl) ⟨1081850, by rfl⟩ : syracuseStep 1442467 = 2163701) B2163701
theorem B2163377 : Blo 1441540 2163377 := bstep (se 2 (by rfl) ⟨811266, by rfl⟩ : syracuseStep 2163377 = 1622533) B1622533
theorem B1442483 : Blo 1441540 1442483 := bstep (se 1 (by rfl) ⟨1081862, by rfl⟩ : syracuseStep 1442483 = 2163725) B2163725
theorem B2163395 : Blo 1441540 2163395 := bstep (se 1 (by rfl) ⟨1622546, by rfl⟩ : syracuseStep 2163395 = 3245093) B3245093
theorem B1442499 : Blo 1441540 1442499 := bstep (se 1 (by rfl) ⟨1081874, by rfl⟩ : syracuseStep 1442499 = 2163749) B2163749
theorem B2310851 : Blo 1441540 2310851 := bstep (se 1 (by rfl) ⟨1733138, by rfl⟩ : syracuseStep 2310851 = 3466277) B3466277
theorem B9872077 : Blo 1441540 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B1442515 : Blo 1441540 1442515 := bstep (se 1 (by rfl) ⟨1081886, by rfl⟩ : syracuseStep 1442515 = 2163773) B2163773
theorem B1540819 : Blo 1441540 1540819 := bstep (se 1 (by rfl) ⟨1155614, by rfl⟩ : syracuseStep 1540819 = 2311229) B2311229
theorem B2163425 : Blo 1441540 2163425 := bstep (se 2 (by rfl) ⟨811284, by rfl⟩ : syracuseStep 2163425 = 1622569) B1622569
theorem B1442531 : Blo 1441540 1442531 := bstep (se 1 (by rfl) ⟨1081898, by rfl⟩ : syracuseStep 1442531 = 2163797) B2163797
theorem B2163443 : Blo 1441540 2163443 := bstep (se 1 (by rfl) ⟨1622582, by rfl⟩ : syracuseStep 2163443 = 3245165) B3245165
theorem B1442547 : Blo 1441540 1442547 := bstep (se 1 (by rfl) ⟨1081910, by rfl⟩ : syracuseStep 1442547 = 2163821) B2163821
theorem B2433793 : Blo 1441540 2433793 := bstep (se 2 (by rfl) ⟨912672, by rfl⟩ : syracuseStep 2433793 = 1825345) B1825345
theorem B1442563 : Blo 1441540 1442563 := bstep (se 1 (by rfl) ⟨1081922, by rfl⟩ : syracuseStep 1442563 = 2163845) B2163845
theorem B2163473 : Blo 1441540 2163473 := bstep (se 2 (by rfl) ⟨811302, by rfl⟩ : syracuseStep 2163473 = 1622605) B1622605
theorem B1622803 : Blo 1441540 1622803 := bstep (se 1 (by rfl) ⟨1217102, by rfl⟩ : syracuseStep 1622803 = 2434205) B2434205
theorem B1442579 : Blo 1441540 1442579 := bstep (se 1 (by rfl) ⟨1081934, by rfl⟩ : syracuseStep 1442579 = 2163869) B2163869
theorem B2433827 : Blo 1441540 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B2163491 : Blo 1441540 2163491 := bstep (se 1 (by rfl) ⟨1622618, by rfl⟩ : syracuseStep 2163491 = 3245237) B3245237
theorem B1442595 : Blo 1441540 1442595 := bstep (se 1 (by rfl) ⟨1081946, by rfl⟩ : syracuseStep 1442595 = 2163893) B2163893
theorem B1442611 : Blo 1441540 1442611 := bstep (se 1 (by rfl) ⟨1081958, by rfl⟩ : syracuseStep 1442611 = 2163917) B2163917
theorem B2163521 : Blo 1441540 2163521 := bstep (se 2 (by rfl) ⟨811320, by rfl⟩ : syracuseStep 2163521 = 1622641) B1622641
theorem B1442627 : Blo 1441540 1442627 := bstep (se 1 (by rfl) ⟨1081970, by rfl⟩ : syracuseStep 1442627 = 2163941) B2163941
theorem B2163539 : Blo 1441540 2163539 := bstep (se 1 (by rfl) ⟨1622654, by rfl⟩ : syracuseStep 2163539 = 3245309) B3245309
theorem B1442643 : Blo 1441540 1442643 := bstep (se 1 (by rfl) ⟨1081982, by rfl⟩ : syracuseStep 1442643 = 2163965) B2163965
theorem B16425827 : Blo 1441540 16425827 := bstep (se 1 (by rfl) ⟨12319370, by rfl⟩ : syracuseStep 16425827 = 24638741) B24638741
theorem B1442659 : Blo 1441540 1442659 := bstep (se 1 (by rfl) ⟨1081994, by rfl⟩ : syracuseStep 1442659 = 2163989) B2163989
theorem B3244913 : Blo 1441540 3244913 := bstep (se 2 (by rfl) ⟨1216842, by rfl⟩ : syracuseStep 3244913 = 2433685) B2433685
theorem B2163569 : Blo 1441540 2163569 := bstep (se 2 (by rfl) ⟨811338, by rfl⟩ : syracuseStep 2163569 = 1622677) B1622677
theorem B3081073 : Blo 1441540 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B1442675 : Blo 1441540 1442675 := bstep (se 1 (by rfl) ⟨1082006, by rfl⟩ : syracuseStep 1442675 = 2164013) B2164013
theorem B3244931 : Blo 1441540 3244931 := bstep (se 1 (by rfl) ⟨2433698, by rfl⟩ : syracuseStep 3244931 = 4867397) B4867397
theorem B2163587 : Blo 1441540 2163587 := bstep (se 1 (by rfl) ⟨1622690, by rfl⟩ : syracuseStep 2163587 = 3245381) B3245381
theorem B3081091 : Blo 1441540 3081091 := bstep (se 1 (by rfl) ⟨2310818, by rfl⟩ : syracuseStep 3081091 = 4621637) B4621637
theorem B1442691 : Blo 1441540 1442691 := bstep (se 1 (by rfl) ⟨1082018, by rfl⟩ : syracuseStep 1442691 = 2164037) B2164037
theorem B1442707 : Blo 1441540 1442707 := bstep (se 1 (by rfl) ⟨1082030, by rfl⟩ : syracuseStep 1442707 = 2164061) B2164061
theorem B2163617 : Blo 1441540 2163617 := bstep (se 2 (by rfl) ⟨811356, by rfl⟩ : syracuseStep 2163617 = 1622713) B1622713
theorem B2433955 : Blo 1441540 2433955 := bstep (se 1 (by rfl) ⟨1825466, by rfl⟩ : syracuseStep 2433955 = 3650933) B3650933
theorem B1622947 : Blo 1441540 1622947 := bstep (se 1 (by rfl) ⟨1217210, by rfl⟩ : syracuseStep 1622947 = 2434421) B2434421
theorem B1442723 : Blo 1441540 1442723 := bstep (se 1 (by rfl) ⟨1082042, by rfl⟩ : syracuseStep 1442723 = 2164085) B2164085
theorem B2163635 : Blo 1441540 2163635 := bstep (se 1 (by rfl) ⟨1622726, by rfl⟩ : syracuseStep 2163635 = 3245453) B3245453
theorem B1442739 : Blo 1441540 1442739 := bstep (se 1 (by rfl) ⟨1082054, by rfl⟩ : syracuseStep 1442739 = 2164109) B2164109
theorem B2737091 : Blo 1441540 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B1442755 : Blo 1441540 1442755 := bstep (se 1 (by rfl) ⟨1082066, by rfl⟩ : syracuseStep 1442755 = 2164133) B2164133
theorem B2163665 : Blo 1441540 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B1442771 : Blo 1441540 1442771 := bstep (se 1 (by rfl) ⟨1082078, by rfl⟩ : syracuseStep 1442771 = 2164157) B2164157
theorem B2163683 : Blo 1441540 2163683 := bstep (se 1 (by rfl) ⟨1622762, by rfl⟩ : syracuseStep 2163683 = 3245525) B3245525
theorem B1442787 : Blo 1441540 1442787 := bstep (se 1 (by rfl) ⟨1082090, by rfl⟩ : syracuseStep 1442787 = 2164181) B2164181
theorem B1442803 : Blo 1441540 1442803 := bstep (se 1 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 1442803 = 2164205) B2164205
theorem B2163713 : Blo 1441540 2163713 := bstep (se 2 (by rfl) ⟨811392, by rfl⟩ : syracuseStep 2163713 = 1622785) B1622785
theorem B1442819 : Blo 1441540 1442819 := bstep (se 1 (by rfl) ⟨1082114, by rfl⟩ : syracuseStep 1442819 = 2164229) B2164229
theorem B2163731 : Blo 1441540 2163731 := bstep (se 1 (by rfl) ⟨1622798, by rfl⟩ : syracuseStep 2163731 = 3245597) B3245597
theorem B1442835 : Blo 1441540 1442835 := bstep (se 1 (by rfl) ⟨1082126, by rfl⟩ : syracuseStep 1442835 = 2164253) B2164253
theorem B1442851 : Blo 1441540 1442851 := bstep (se 1 (by rfl) ⟨1082138, by rfl⟩ : syracuseStep 1442851 = 2164277) B2164277
theorem B2434097 : Blo 1441540 2434097 := bstep (se 2 (by rfl) ⟨912786, by rfl⟩ : syracuseStep 2434097 = 1825573) B1825573
theorem B2163761 : Blo 1441540 2163761 := bstep (se 2 (by rfl) ⟨811410, by rfl⟩ : syracuseStep 2163761 = 1622821) B1622821
theorem B1623091 : Blo 1441540 1623091 := bstep (se 1 (by rfl) ⟨1217318, by rfl⟩ : syracuseStep 1623091 = 2434637) B2434637
theorem B1442867 : Blo 1441540 1442867 := bstep (se 1 (by rfl) ⟨1082150, by rfl⟩ : syracuseStep 1442867 = 2164301) B2164301
theorem B2163779 : Blo 1441540 2163779 := bstep (se 1 (by rfl) ⟨1622834, by rfl⟩ : syracuseStep 2163779 = 3245669) B3245669
theorem B1442883 : Blo 1441540 1442883 := bstep (se 1 (by rfl) ⟨1082162, by rfl⟩ : syracuseStep 1442883 = 2164325) B2164325
theorem B1442899 : Blo 1441540 1442899 := bstep (se 1 (by rfl) ⟨1082174, by rfl⟩ : syracuseStep 1442899 = 2164349) B2164349
theorem B2163809 : Blo 1441540 2163809 := bstep (se 2 (by rfl) ⟨811428, by rfl⟩ : syracuseStep 2163809 = 1622857) B1622857
theorem B1442915 : Blo 1441540 1442915 := bstep (se 1 (by rfl) ⟨1082186, by rfl⟩ : syracuseStep 1442915 = 2164373) B2164373
theorem B4867181 : Blo 1441540 4867181 := bstep (se 3 (by rfl) ⟨912596, by rfl⟩ : syracuseStep 4867181 = 1825193) B1825193
theorem B7799921 : Blo 1441540 7799921 := bstep (se 2 (by rfl) ⟨2924970, by rfl⟩ : syracuseStep 7799921 = 5849941) B5849941
theorem B2163827 : Blo 1441540 2163827 := bstep (se 1 (by rfl) ⟨1622870, by rfl⟩ : syracuseStep 2163827 = 3245741) B3245741
theorem B1442931 : Blo 1441540 1442931 := bstep (se 1 (by rfl) ⟨1082198, by rfl⟩ : syracuseStep 1442931 = 2164397) B2164397
theorem B1442947 : Blo 1441540 1442947 := bstep (se 1 (by rfl) ⟨1082210, by rfl⟩ : syracuseStep 1442947 = 2164421) B2164421
theorem B3245201 : Blo 1441540 3245201 := bstep (se 2 (by rfl) ⟨1216950, by rfl⟩ : syracuseStep 3245201 = 2433901) B2433901
theorem B2163857 : Blo 1441540 2163857 := bstep (se 2 (by rfl) ⟨811446, by rfl⟩ : syracuseStep 2163857 = 1622893) B1622893
theorem B1442963 : Blo 1441540 1442963 := bstep (se 1 (by rfl) ⟨1082222, by rfl⟩ : syracuseStep 1442963 = 2164445) B2164445
theorem B4867235 : Blo 1441540 4867235 := bstep (se 1 (by rfl) ⟨3650426, by rfl⟩ : syracuseStep 4867235 = 7300853) B7300853
theorem B3245219 : Blo 1441540 3245219 := bstep (se 1 (by rfl) ⟨2433914, by rfl⟩ : syracuseStep 3245219 = 4867829) B4867829
theorem B2163875 : Blo 1441540 2163875 := bstep (se 1 (by rfl) ⟨1622906, by rfl⟩ : syracuseStep 2163875 = 3245813) B3245813
theorem B1442979 : Blo 1441540 1442979 := bstep (se 1 (by rfl) ⟨1082234, by rfl⟩ : syracuseStep 1442979 = 2164469) B2164469
theorem B2434225 : Blo 1441540 2434225 := bstep (se 2 (by rfl) ⟨912834, by rfl⟩ : syracuseStep 2434225 = 1825669) B1825669
theorem B1442995 : Blo 1441540 1442995 := bstep (se 1 (by rfl) ⟨1082246, by rfl⟩ : syracuseStep 1442995 = 2164493) B2164493
theorem B2163905 : Blo 1441540 2163905 := bstep (se 2 (by rfl) ⟨811464, by rfl⟩ : syracuseStep 2163905 = 1622929) B1622929
theorem B1623235 : Blo 1441540 1623235 := bstep (se 1 (by rfl) ⟨1217426, by rfl⟩ : syracuseStep 1623235 = 2434853) B2434853
theorem B2311363 : Blo 1441540 2311363 := bstep (se 1 (by rfl) ⟨1733522, by rfl⟩ : syracuseStep 2311363 = 3467045) B3467045
theorem B1443011 : Blo 1441540 1443011 := bstep (se 1 (by rfl) ⟨1082258, by rfl⟩ : syracuseStep 1443011 = 2164517) B2164517
theorem B2434259 : Blo 1441540 2434259 := bstep (se 1 (by rfl) ⟨1825694, by rfl⟩ : syracuseStep 2434259 = 3651389) B3651389
theorem B2163923 : Blo 1441540 2163923 := bstep (se 1 (by rfl) ⟨1622942, by rfl⟩ : syracuseStep 2163923 = 3245885) B3245885
theorem B1443027 : Blo 1441540 1443027 := bstep (se 1 (by rfl) ⟨1082270, by rfl⟩ : syracuseStep 1443027 = 2164541) B2164541
theorem B1443043 : Blo 1441540 1443043 := bstep (se 1 (by rfl) ⟨1082282, by rfl⟩ : syracuseStep 1443043 = 2164565) B2164565
theorem B2163953 : Blo 1441540 2163953 := bstep (se 2 (by rfl) ⟨811482, by rfl⟩ : syracuseStep 2163953 = 1622965) B1622965
theorem B1443059 : Blo 1441540 1443059 := bstep (se 1 (by rfl) ⟨1082294, by rfl⟩ : syracuseStep 1443059 = 2164589) B2164589
theorem B2163971 : Blo 1441540 2163971 := bstep (se 1 (by rfl) ⟨1622978, by rfl⟩ : syracuseStep 2163971 = 3245957) B3245957
theorem B1443075 : Blo 1441540 1443075 := bstep (se 1 (by rfl) ⟨1082306, by rfl⟩ : syracuseStep 1443075 = 2164613) B2164613
theorem B1443091 : Blo 1441540 1443091 := bstep (se 1 (by rfl) ⟨1082318, by rfl⟩ : syracuseStep 1443091 = 2164637) B2164637
theorem B2164001 : Blo 1441540 2164001 := bstep (se 2 (by rfl) ⟨811500, by rfl⟩ : syracuseStep 2164001 = 1623001) B1623001
theorem B1443107 : Blo 1441540 1443107 := bstep (se 1 (by rfl) ⟨1082330, by rfl⟩ : syracuseStep 1443107 = 2164661) B2164661
theorem B2164019 : Blo 1441540 2164019 := bstep (se 1 (by rfl) ⟨1623014, by rfl⟩ : syracuseStep 2164019 = 3246029) B3246029
theorem B20792629 : Blo 1441540 20792629 := bstep (se 5 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 20792629 = 1949309) B1949309
theorem B1443123 : Blo 1441540 1443123 := bstep (se 1 (by rfl) ⟨1082342, by rfl⟩ : syracuseStep 1443123 = 2164685) B2164685
theorem B1443139 : Blo 1441540 1443139 := bstep (se 1 (by rfl) ⟨1082354, by rfl⟩ : syracuseStep 1443139 = 2164709) B2164709
theorem B2164049 : Blo 1441540 2164049 := bstep (se 2 (by rfl) ⟨811518, by rfl⟩ : syracuseStep 2164049 = 1623037) B1623037
theorem B2434387 : Blo 1441540 2434387 := bstep (se 1 (by rfl) ⟨1825790, by rfl⟩ : syracuseStep 2434387 = 3651581) B3651581
theorem B1623379 : Blo 1441540 1623379 := bstep (se 1 (by rfl) ⟨1217534, by rfl⟩ : syracuseStep 1623379 = 2435069) B2435069
theorem B1443155 : Blo 1441540 1443155 := bstep (se 1 (by rfl) ⟨1082366, by rfl⟩ : syracuseStep 1443155 = 2164733) B2164733
theorem B2164067 : Blo 1441540 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B1443171 : Blo 1441540 1443171 := bstep (se 1 (by rfl) ⟨1082378, by rfl⟩ : syracuseStep 1443171 = 2164757) B2164757
theorem B1443187 : Blo 1441540 1443187 := bstep (se 1 (by rfl) ⟨1082390, by rfl⟩ : syracuseStep 1443187 = 2164781) B2164781
theorem B2164097 : Blo 1441540 2164097 := bstep (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) B1623073
theorem B1443203 : Blo 1441540 1443203 := bstep (se 1 (by rfl) ⟨1082402, by rfl⟩ : syracuseStep 1443203 = 2164805) B2164805
theorem B33326477 : Blo 1441540 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B2164115 : Blo 1441540 2164115 := bstep (se 1 (by rfl) ⟨1623086, by rfl⟩ : syracuseStep 2164115 = 3246173) B3246173
theorem B1443219 : Blo 1441540 1443219 := bstep (se 1 (by rfl) ⟨1082414, by rfl⟩ : syracuseStep 1443219 = 2164829) B2164829
theorem B1443235 : Blo 1441540 1443235 := bstep (se 1 (by rfl) ⟨1082426, by rfl⟩ : syracuseStep 1443235 = 2164853) B2164853
theorem B7300529 : Blo 1441540 7300529 := bstep (se 2 (by rfl) ⟨2737698, by rfl⟩ : syracuseStep 7300529 = 5475397) B5475397
theorem B4867505 : Blo 1441540 4867505 := bstep (se 2 (by rfl) ⟨1825314, by rfl⟩ : syracuseStep 4867505 = 3650629) B3650629
theorem B3245489 : Blo 1441540 3245489 := bstep (se 2 (by rfl) ⟨1217058, by rfl⟩ : syracuseStep 3245489 = 2434117) B2434117
theorem B2164145 : Blo 1441540 2164145 := bstep (se 2 (by rfl) ⟨811554, by rfl⟩ : syracuseStep 2164145 = 1623109) B1623109
theorem B1443251 : Blo 1441540 1443251 := bstep (se 1 (by rfl) ⟨1082438, by rfl⟩ : syracuseStep 1443251 = 2164877) B2164877
theorem B3245507 : Blo 1441540 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B2164163 : Blo 1441540 2164163 := bstep (se 1 (by rfl) ⟨1623122, by rfl⟩ : syracuseStep 2164163 = 3246245) B3246245
theorem B1443267 : Blo 1441540 1443267 := bstep (se 1 (by rfl) ⟨1082450, by rfl⟩ : syracuseStep 1443267 = 2164901) B2164901
theorem B1443283 : Blo 1441540 1443283 := bstep (se 1 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 1443283 = 2164925) B2164925
theorem B2434529 : Blo 1441540 2434529 := bstep (se 2 (by rfl) ⟨912948, by rfl⟩ : syracuseStep 2434529 = 1825897) B1825897
theorem B2164193 : Blo 1441540 2164193 := bstep (se 2 (by rfl) ⟨811572, by rfl⟩ : syracuseStep 2164193 = 1623145) B1623145
theorem B1623523 : Blo 1441540 1623523 := bstep (se 1 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 1623523 = 2435285) B2435285
theorem B1443299 : Blo 1441540 1443299 := bstep (se 1 (by rfl) ⟨1082474, by rfl⟩ : syracuseStep 1443299 = 2164949) B2164949
theorem B2164211 : Blo 1441540 2164211 := bstep (se 1 (by rfl) ⟨1623158, by rfl⟩ : syracuseStep 2164211 = 3246317) B3246317
theorem B1443315 : Blo 1441540 1443315 := bstep (se 1 (by rfl) ⟨1082486, by rfl⟩ : syracuseStep 1443315 = 2164973) B2164973
theorem B1443331 : Blo 1441540 1443331 := bstep (se 1 (by rfl) ⟨1082498, by rfl⟩ : syracuseStep 1443331 = 2164997) B2164997
theorem B2164241 : Blo 1441540 2164241 := bstep (se 2 (by rfl) ⟨811590, by rfl⟩ : syracuseStep 2164241 = 1623181) B1623181
theorem B1443347 : Blo 1441540 1443347 := bstep (se 1 (by rfl) ⟨1082510, by rfl⟩ : syracuseStep 1443347 = 2165021) B2165021
theorem B2467363 : Blo 1441540 2467363 := bstep (se 1 (by rfl) ⟨1850522, by rfl⟩ : syracuseStep 2467363 = 3701045) B3701045
theorem B2164259 : Blo 1441540 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B1443363 : Blo 1441540 1443363 := bstep (se 1 (by rfl) ⟨1082522, by rfl⟩ : syracuseStep 1443363 = 2165045) B2165045
theorem B3900977 : Blo 1441540 3900977 := bstep (se 2 (by rfl) ⟨1462866, by rfl⟩ : syracuseStep 3900977 = 2925733) B2925733
theorem B1443379 : Blo 1441540 1443379 := bstep (se 1 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 1443379 = 2165069) B2165069
theorem B2164289 : Blo 1441540 2164289 := bstep (se 2 (by rfl) ⟨811608, by rfl⟩ : syracuseStep 2164289 = 1623217) B1623217
theorem B1443395 : Blo 1441540 1443395 := bstep (se 1 (by rfl) ⟨1082546, by rfl⟩ : syracuseStep 1443395 = 2165093) B2165093
theorem B9864773 : Blo 1441540 9864773 := bstep (se 4 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 9864773 = 1849645) B1849645
theorem B18490949 : Blo 1441540 18490949 := bstep (se 4 (by rfl) ⟨1733526, by rfl⟩ : syracuseStep 18490949 = 3467053) B3467053
theorem B2164307 : Blo 1441540 2164307 := bstep (se 1 (by rfl) ⟨1623230, by rfl⟩ : syracuseStep 2164307 = 3246461) B3246461
theorem B1443411 : Blo 1441540 1443411 := bstep (se 1 (by rfl) ⟨1082558, by rfl⟩ : syracuseStep 1443411 = 2165117) B2165117
theorem B2434657 : Blo 1441540 2434657 := bstep (se 2 (by rfl) ⟨912996, by rfl⟩ : syracuseStep 2434657 = 1825993) B1825993
theorem B1443427 : Blo 1441540 1443427 := bstep (se 1 (by rfl) ⟨1082570, by rfl⟩ : syracuseStep 1443427 = 2165141) B2165141
theorem B2164337 : Blo 1441540 2164337 := bstep (se 2 (by rfl) ⟨811626, by rfl⟩ : syracuseStep 2164337 = 1623253) B1623253
theorem B1623667 : Blo 1441540 1623667 := bstep (se 1 (by rfl) ⟨1217750, by rfl⟩ : syracuseStep 1623667 = 2435501) B2435501
theorem B1443443 : Blo 1441540 1443443 := bstep (se 1 (by rfl) ⟨1082582, by rfl⟩ : syracuseStep 1443443 = 2165165) B2165165
theorem B2434691 : Blo 1441540 2434691 := bstep (se 1 (by rfl) ⟨1826018, by rfl⟩ : syracuseStep 2434691 = 3652037) B3652037
theorem B2164355 : Blo 1441540 2164355 := bstep (se 1 (by rfl) ⟨1623266, by rfl⟩ : syracuseStep 2164355 = 3246533) B3246533
theorem B1443459 : Blo 1441540 1443459 := bstep (se 1 (by rfl) ⟨1082594, by rfl⟩ : syracuseStep 1443459 = 2165189) B2165189
theorem B16647821 : Blo 1441540 16647821 := bstep (se 3 (by rfl) ⟨3121466, by rfl⟩ : syracuseStep 16647821 = 6242933) B6242933
theorem B1443475 : Blo 1441540 1443475 := bstep (se 1 (by rfl) ⟨1082606, by rfl⟩ : syracuseStep 1443475 = 2165213) B2165213
theorem B2164385 : Blo 1441540 2164385 := bstep (se 2 (by rfl) ⟨811644, by rfl⟩ : syracuseStep 2164385 = 1623289) B1623289
theorem B1443491 : Blo 1441540 1443491 := bstep (se 1 (by rfl) ⟨1082618, by rfl⟩ : syracuseStep 1443491 = 2165237) B2165237
theorem B2164403 : Blo 1441540 2164403 := bstep (se 1 (by rfl) ⟨1623302, by rfl⟩ : syracuseStep 2164403 = 3246605) B3246605
theorem B1443507 : Blo 1441540 1443507 := bstep (se 1 (by rfl) ⟨1082630, by rfl⟩ : syracuseStep 1443507 = 2165261) B2165261
theorem B1443523 : Blo 1441540 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B3245777 : Blo 1441540 3245777 := bstep (se 2 (by rfl) ⟨1217166, by rfl⟩ : syracuseStep 3245777 = 2434333) B2434333
theorem B2164433 : Blo 1441540 2164433 := bstep (se 2 (by rfl) ⟨811662, by rfl⟩ : syracuseStep 2164433 = 1623325) B1623325
theorem B1443539 : Blo 1441540 1443539 := bstep (se 1 (by rfl) ⟨1082654, by rfl⟩ : syracuseStep 1443539 = 2165309) B2165309
theorem B3245795 : Blo 1441540 3245795 := bstep (se 1 (by rfl) ⟨2434346, by rfl⟩ : syracuseStep 3245795 = 4868693) B4868693
theorem B2164451 : Blo 1441540 2164451 := bstep (se 1 (by rfl) ⟨1623338, by rfl⟩ : syracuseStep 2164451 = 3246677) B3246677
theorem B2311907 : Blo 1441540 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B2164481 : Blo 1441540 2164481 := bstep (se 2 (by rfl) ⟨811680, by rfl⟩ : syracuseStep 2164481 = 1623361) B1623361
theorem B2434819 : Blo 1441540 2434819 := bstep (se 1 (by rfl) ⟨1826114, by rfl⟩ : syracuseStep 2434819 = 3652229) B3652229
theorem B1623811 : Blo 1441540 1623811 := bstep (se 1 (by rfl) ⟨1217858, by rfl⟩ : syracuseStep 1623811 = 2435717) B2435717
theorem B8218381 : Blo 1441540 8218381 := bstep (se 3 (by rfl) ⟨1540946, by rfl⟩ : syracuseStep 8218381 = 3081893) B3081893
theorem B2164499 : Blo 1441540 2164499 := bstep (se 1 (by rfl) ⟨1623374, by rfl⟩ : syracuseStep 2164499 = 3246749) B3246749
theorem B2164529 : Blo 1441540 2164529 := bstep (se 2 (by rfl) ⟨811698, by rfl⟩ : syracuseStep 2164529 = 1623397) B1623397
theorem B2164547 : Blo 1441540 2164547 := bstep (se 1 (by rfl) ⟨1623410, by rfl⟩ : syracuseStep 2164547 = 3246821) B3246821
theorem B2164577 : Blo 1441540 2164577 := bstep (se 2 (by rfl) ⟨811716, by rfl⟩ : syracuseStep 2164577 = 1623433) B1623433
theorem B2738033 : Blo 1441540 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B2164595 : Blo 1441540 2164595 := bstep (se 1 (by rfl) ⟨1623446, by rfl⟩ : syracuseStep 2164595 = 3246893) B3246893
theorem B2434961 : Blo 1441540 2434961 := bstep (se 2 (by rfl) ⟨913110, by rfl⟩ : syracuseStep 2434961 = 1826221) B1826221
theorem B2164625 : Blo 1441540 2164625 := bstep (se 2 (by rfl) ⟨811734, by rfl⟩ : syracuseStep 2164625 = 1623469) B1623469
theorem B2312081 : Blo 1441540 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B1623955 : Blo 1441540 1623955 := bstep (se 1 (by rfl) ⟨1217966, by rfl⟩ : syracuseStep 1623955 = 2435933) B2435933
theorem B2164643 : Blo 1441540 2164643 := bstep (se 1 (by rfl) ⟨1623482, by rfl⟩ : syracuseStep 2164643 = 3246965) B3246965
theorem B2164673 : Blo 1441540 2164673 := bstep (se 2 (by rfl) ⟨811752, by rfl⟩ : syracuseStep 2164673 = 1623505) B1623505
theorem B15591365 : Blo 1441540 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B4868045 : Blo 1441540 4868045 := bstep (se 3 (by rfl) ⟨912758, by rfl⟩ : syracuseStep 4868045 = 1825517) B1825517
theorem B2164691 : Blo 1441540 2164691 := bstep (se 1 (by rfl) ⟨1623518, by rfl⟩ : syracuseStep 2164691 = 3247037) B3247037
theorem B3246065 : Blo 1441540 3246065 := bstep (se 2 (by rfl) ⟨1217274, by rfl⟩ : syracuseStep 3246065 = 2434549) B2434549
theorem B2164721 : Blo 1441540 2164721 := bstep (se 2 (by rfl) ⟨811770, by rfl⟩ : syracuseStep 2164721 = 1623541) B1623541
theorem B4868099 : Blo 1441540 4868099 := bstep (se 1 (by rfl) ⟨3651074, by rfl⟩ : syracuseStep 4868099 = 7302149) B7302149
theorem B3246083 : Blo 1441540 3246083 := bstep (se 1 (by rfl) ⟨2434562, by rfl⟩ : syracuseStep 3246083 = 4869125) B4869125
theorem B2164739 : Blo 1441540 2164739 := bstep (se 1 (by rfl) ⟨1623554, by rfl⟩ : syracuseStep 2164739 = 3247109) B3247109
theorem B2435089 : Blo 1441540 2435089 := bstep (se 2 (by rfl) ⟨913158, by rfl⟩ : syracuseStep 2435089 = 1826317) B1826317
theorem B2164769 : Blo 1441540 2164769 := bstep (se 2 (by rfl) ⟨811788, by rfl⟩ : syracuseStep 2164769 = 1623577) B1623577
theorem B2435123 : Blo 1441540 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B2164787 : Blo 1441540 2164787 := bstep (se 1 (by rfl) ⟨1623590, by rfl⟩ : syracuseStep 2164787 = 3247181) B3247181
theorem B4106321 : Blo 1441540 4106321 := bstep (se 2 (by rfl) ⟨1539870, by rfl⟩ : syracuseStep 4106321 = 3079741) B3079741
theorem B2164817 : Blo 1441540 2164817 := bstep (se 2 (by rfl) ⟨811806, by rfl⟩ : syracuseStep 2164817 = 1623613) B1623613
theorem B4384867 : Blo 1441540 4384867 := bstep (se 1 (by rfl) ⟨3288650, by rfl⟩ : syracuseStep 4384867 = 6577301) B6577301
theorem B2164835 : Blo 1441540 2164835 := bstep (se 1 (by rfl) ⟨1623626, by rfl⟩ : syracuseStep 2164835 = 3247253) B3247253
theorem B2164865 : Blo 1441540 2164865 := bstep (se 2 (by rfl) ⟨811824, by rfl⟩ : syracuseStep 2164865 = 1623649) B1623649
theorem B2164883 : Blo 1441540 2164883 := bstep (se 1 (by rfl) ⟨1623662, by rfl⟩ : syracuseStep 2164883 = 3247325) B3247325
theorem B2164913 : Blo 1441540 2164913 := bstep (se 2 (by rfl) ⟨811842, by rfl⟩ : syracuseStep 2164913 = 1623685) B1623685
theorem B2435251 : Blo 1441540 2435251 := bstep (se 1 (by rfl) ⟨1826438, by rfl⟩ : syracuseStep 2435251 = 3652877) B3652877
theorem B2164931 : Blo 1441540 2164931 := bstep (se 1 (by rfl) ⟨1623698, by rfl⟩ : syracuseStep 2164931 = 3247397) B3247397
theorem B2164961 : Blo 1441540 2164961 := bstep (se 2 (by rfl) ⟨811860, by rfl⟩ : syracuseStep 2164961 = 1623721) B1623721
theorem B2164979 : Blo 1441540 2164979 := bstep (se 1 (by rfl) ⟨1623734, by rfl⟩ : syracuseStep 2164979 = 3247469) B3247469
theorem B4868369 : Blo 1441540 4868369 := bstep (se 2 (by rfl) ⟨1825638, by rfl⟩ : syracuseStep 4868369 = 3651277) B3651277
theorem B3246353 : Blo 1441540 3246353 := bstep (se 2 (by rfl) ⟨1217382, by rfl⟩ : syracuseStep 3246353 = 2434765) B2434765
theorem B2165009 : Blo 1441540 2165009 := bstep (se 2 (by rfl) ⟨811878, by rfl⟩ : syracuseStep 2165009 = 1623757) B1623757
theorem B3246371 : Blo 1441540 3246371 := bstep (se 1 (by rfl) ⟨2434778, by rfl⟩ : syracuseStep 3246371 = 4869557) B4869557
theorem B2165027 : Blo 1441540 2165027 := bstep (se 1 (by rfl) ⟨1623770, by rfl⟩ : syracuseStep 2165027 = 3247541) B3247541
theorem B2435393 : Blo 1441540 2435393 := bstep (se 2 (by rfl) ⟨913272, by rfl⟩ : syracuseStep 2435393 = 1826545) B1826545
theorem B2165057 : Blo 1441540 2165057 := bstep (se 2 (by rfl) ⟨811896, by rfl⟩ : syracuseStep 2165057 = 1623793) B1623793
theorem B2165075 : Blo 1441540 2165075 := bstep (se 1 (by rfl) ⟨1623806, by rfl⟩ : syracuseStep 2165075 = 3247613) B3247613
theorem B2165105 : Blo 1441540 2165105 := bstep (se 2 (by rfl) ⟨811914, by rfl⟩ : syracuseStep 2165105 = 1623829) B1623829
theorem B2165123 : Blo 1441540 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B2165153 : Blo 1441540 2165153 := bstep (se 2 (by rfl) ⟨811932, by rfl⟩ : syracuseStep 2165153 = 1623865) B1623865
theorem B9873827 : Blo 1441540 9873827 := bstep (se 1 (by rfl) ⟨7405370, by rfl⟩ : syracuseStep 9873827 = 14810741) B14810741
theorem B2165171 : Blo 1441540 2165171 := bstep (se 1 (by rfl) ⟨1623878, by rfl⟩ : syracuseStep 2165171 = 3247757) B3247757
theorem B2435521 : Blo 1441540 2435521 := bstep (se 2 (by rfl) ⟨913320, by rfl⟩ : syracuseStep 2435521 = 1826641) B1826641
theorem B2165201 : Blo 1441540 2165201 := bstep (se 2 (by rfl) ⟨811950, by rfl⟩ : syracuseStep 2165201 = 1623901) B1623901
theorem B2435555 : Blo 1441540 2435555 := bstep (se 1 (by rfl) ⟨1826666, by rfl⟩ : syracuseStep 2435555 = 3653333) B3653333
theorem B2165219 : Blo 1441540 2165219 := bstep (se 1 (by rfl) ⟨1623914, by rfl⟩ : syracuseStep 2165219 = 3247829) B3247829
theorem B2165249 : Blo 1441540 2165249 := bstep (se 2 (by rfl) ⟨811968, by rfl⟩ : syracuseStep 2165249 = 1623937) B1623937
theorem B2468369 : Blo 1441540 2468369 := bstep (se 2 (by rfl) ⟨925638, by rfl⟩ : syracuseStep 2468369 = 1851277) B1851277
theorem B2165267 : Blo 1441540 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B3246641 : Blo 1441540 3246641 := bstep (se 2 (by rfl) ⟨1217490, by rfl⟩ : syracuseStep 3246641 = 2434981) B2434981
theorem B2165297 : Blo 1441540 2165297 := bstep (se 2 (by rfl) ⟨811986, by rfl⟩ : syracuseStep 2165297 = 1623973) B1623973
theorem B3246659 : Blo 1441540 3246659 := bstep (se 1 (by rfl) ⟨2434994, by rfl⟩ : syracuseStep 3246659 = 4869989) B4869989
theorem B3467843 : Blo 1441540 3467843 := bstep (se 1 (by rfl) ⟨2600882, by rfl⟩ : syracuseStep 3467843 = 5201765) B5201765
theorem B11692613 : Blo 1441540 11692613 := bstep (se 4 (by rfl) ⟨1096182, by rfl⟩ : syracuseStep 11692613 = 2192365) B2192365
theorem B19999331 : Blo 1441540 19999331 := bstep (se 1 (by rfl) ⟨14999498, by rfl⟩ : syracuseStep 19999331 = 29998997) B29998997
theorem B2435683 : Blo 1441540 2435683 := bstep (se 1 (by rfl) ⟨1826762, by rfl⟩ : syracuseStep 2435683 = 3653525) B3653525
theorem B2738929 : Blo 1441540 2738929 := bstep (se 2 (by rfl) ⟨1027098, by rfl⟩ : syracuseStep 2738929 = 2054197) B2054197
theorem B5851889 : Blo 1441540 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B2435825 : Blo 1441540 2435825 := bstep (se 2 (by rfl) ⟨913434, by rfl⟩ : syracuseStep 2435825 = 1826869) B1826869
theorem B4868909 : Blo 1441540 4868909 := bstep (se 3 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 4868909 = 1825841) B1825841
theorem B3246929 : Blo 1441540 3246929 := bstep (se 2 (by rfl) ⟨1217598, by rfl⟩ : syracuseStep 3246929 = 2435197) B2435197
theorem B7301987 : Blo 1441540 7301987 := bstep (se 1 (by rfl) ⟨5476490, by rfl⟩ : syracuseStep 7301987 = 10952981) B10952981
theorem B4868963 : Blo 1441540 4868963 := bstep (se 1 (by rfl) ⟨3651722, by rfl⟩ : syracuseStep 4868963 = 7303445) B7303445
theorem B3246947 : Blo 1441540 3246947 := bstep (se 1 (by rfl) ⟨2435210, by rfl⟩ : syracuseStep 3246947 = 4870421) B4870421
theorem B13151089 : Blo 1441540 13151089 := bstep (se 2 (by rfl) ⟨4931658, by rfl⟩ : syracuseStep 13151089 = 9863317) B9863317
theorem B5475185 : Blo 1441540 5475185 := bstep (se 2 (by rfl) ⟨2053194, by rfl⟩ : syracuseStep 5475185 = 4106389) B4106389
theorem B2435953 : Blo 1441540 2435953 := bstep (se 2 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 2435953 = 1826965) B1826965
theorem B2739089 : Blo 1441540 2739089 := bstep (se 2 (by rfl) ⟨1027158, by rfl⟩ : syracuseStep 2739089 = 2054317) B2054317
theorem B4623277 : Blo 1441540 4623277 := bstep (se 3 (by rfl) ⟨866864, by rfl⟩ : syracuseStep 4623277 = 1733729) B1733729
theorem B11693069 : Blo 1441540 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B4107277 : Blo 1441540 4107277 := bstep (se 3 (by rfl) ⟨770114, by rfl⟩ : syracuseStep 4107277 = 1540229) B1540229
theorem B2468929 : Blo 1441540 2468929 := bstep (se 2 (by rfl) ⟨925848, by rfl⟩ : syracuseStep 2468929 = 1851697) B1851697
theorem B18992227 : Blo 1441540 18992227 := bstep (se 1 (by rfl) ⟨14244170, by rfl⟩ : syracuseStep 18992227 = 28488341) B28488341
theorem B4869233 : Blo 1441540 4869233 := bstep (se 2 (by rfl) ⟨1825962, by rfl⟩ : syracuseStep 4869233 = 3651925) B3651925
theorem B3247217 : Blo 1441540 3247217 := bstep (se 2 (by rfl) ⟨1217706, by rfl⟩ : syracuseStep 3247217 = 2435413) B2435413
theorem B3247235 : Blo 1441540 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B2469025 : Blo 1441540 2469025 := bstep (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) B1851769
theorem B4107505 : Blo 1441540 4107505 := bstep (se 2 (by rfl) ⟨1540314, by rfl⟩ : syracuseStep 4107505 = 3080629) B3080629
theorem B2739491 : Blo 1441540 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B4935011 : Blo 1441540 4935011 := bstep (se 1 (by rfl) ⟨3701258, by rfl⟩ : syracuseStep 4935011 = 7402517) B7402517
theorem B4107665 : Blo 1441540 4107665 := bstep (se 2 (by rfl) ⟨1540374, by rfl⟩ : syracuseStep 4107665 = 3080749) B3080749
theorem B3247505 : Blo 1441540 3247505 := bstep (se 2 (by rfl) ⟨1217814, by rfl⟩ : syracuseStep 3247505 = 2435629) B2435629
theorem B3247523 : Blo 1441540 3247523 := bstep (se 1 (by rfl) ⟨2435642, by rfl⟩ : syracuseStep 3247523 = 4871285) B4871285
theorem B6581731 : Blo 1441540 6581731 := bstep (se 1 (by rfl) ⟨4936298, by rfl⟩ : syracuseStep 6581731 = 9872597) B9872597
theorem B3649009 : Blo 1441540 3649009 := bstep (se 2 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 3649009 = 2736757) B2736757
theorem B4107779 : Blo 1441540 4107779 := bstep (se 1 (by rfl) ⟨3080834, by rfl⟩ : syracuseStep 4107779 = 6161669) B6161669
theorem B8769073 : Blo 1441540 8769073 := bstep (se 2 (by rfl) ⟨3288402, by rfl⟩ : syracuseStep 8769073 = 6576805) B6576805
theorem B6164045 : Blo 1441540 6164045 := bstep (se 3 (by rfl) ⟨1155758, by rfl⟩ : syracuseStep 6164045 = 2311517) B2311517
theorem B2600579 : Blo 1441540 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B7302797 : Blo 1441540 7302797 := bstep (se 3 (by rfl) ⟨1369274, by rfl⟩ : syracuseStep 7302797 = 2738549) B2738549
theorem B4869773 : Blo 1441540 4869773 := bstep (se 3 (by rfl) ⟨913082, by rfl⟩ : syracuseStep 4869773 = 1826165) B1826165
theorem B3247793 : Blo 1441540 3247793 := bstep (se 2 (by rfl) ⟨1217922, by rfl⟩ : syracuseStep 3247793 = 2435845) B2435845
theorem B4869827 : Blo 1441540 4869827 := bstep (se 1 (by rfl) ⟨3652370, by rfl⟩ : syracuseStep 4869827 = 7304741) B7304741
theorem B3247811 : Blo 1441540 3247811 := bstep (se 1 (by rfl) ⟨2435858, by rfl⟩ : syracuseStep 3247811 = 4871717) B4871717
theorem B8220365 : Blo 1441540 8220365 := bstep (se 3 (by rfl) ⟨1541318, by rfl⟩ : syracuseStep 8220365 = 3082637) B3082637
theorem B3649283 : Blo 1441540 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B4935505 : Blo 1441540 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B2600867 : Blo 1441540 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B3649475 : Blo 1441540 3649475 := bstep (se 1 (by rfl) ⟨2737106, by rfl⟩ : syracuseStep 3649475 = 5474213) B5474213
theorem B36990917 : Blo 1441540 36990917 := bstep (se 4 (by rfl) ⟨3467898, by rfl⟩ : syracuseStep 36990917 = 6935797) B6935797
theorem B4870097 : Blo 1441540 4870097 := bstep (se 2 (by rfl) ⟨1826286, by rfl⟩ : syracuseStep 4870097 = 3652573) B3652573
theorem B14815217 : Blo 1441540 14815217 := bstep (se 2 (by rfl) ⟨5555706, by rfl⟩ : syracuseStep 14815217 = 11111413) B11111413
theorem B8212549 : Blo 1441540 8212549 := bstep (se 4 (by rfl) ⟨769926, by rfl⟩ : syracuseStep 8212549 = 1539853) B1539853
theorem B10956869 : Blo 1441540 10956869 := bstep (se 4 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 10956869 = 2054413) B2054413
theorem B6582349 : Blo 1441540 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B1732691 : Blo 1441540 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B10678385 : Blo 1441540 10678385 := bstep (se 2 (by rfl) ⟨4004394, by rfl⟩ : syracuseStep 10678385 = 8008789) B8008789
theorem B2740387 : Blo 1441540 2740387 := bstep (se 1 (by rfl) ⟨2055290, by rfl⟩ : syracuseStep 2740387 = 4110581) B4110581
theorem B5476643 : Blo 1441540 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B1462595 : Blo 1441540 1462595 := bstep (se 1 (by rfl) ⟨1096946, by rfl⟩ : syracuseStep 1462595 = 2193893) B2193893
theorem B18485617 : Blo 1441540 18485617 := bstep (se 2 (by rfl) ⟨6932106, by rfl⟩ : syracuseStep 18485617 = 13864213) B13864213
theorem B4387213 : Blo 1441540 4387213 := bstep (se 3 (by rfl) ⟨822602, by rfl⟩ : syracuseStep 4387213 = 1645205) B1645205
theorem B2052545 : Blo 1441540 2052545 := bstep (se 2 (by rfl) ⟨769704, by rfl⟩ : syracuseStep 2052545 = 1539409) B1539409
theorem B4108781 : Blo 1441540 4108781 := bstep (se 3 (by rfl) ⟨770396, by rfl⟩ : syracuseStep 4108781 = 1540793) B1540793
theorem B4870637 : Blo 1441540 4870637 := bstep (se 3 (by rfl) ⟨913244, by rfl⟩ : syracuseStep 4870637 = 1826489) B1826489
theorem B4870691 : Blo 1441540 4870691 := bstep (se 1 (by rfl) ⟨3653018, by rfl⟩ : syracuseStep 4870691 = 7306037) B7306037
theorem B2052659 : Blo 1441540 2052659 := bstep (se 1 (by rfl) ⟨1539494, by rfl⟩ : syracuseStep 2052659 = 3078989) B3078989
theorem B2224721 : Blo 1441540 2224721 := bstep (se 2 (by rfl) ⟨834270, by rfl⟩ : syracuseStep 2224721 = 1668541) B1668541
theorem B8221297 : Blo 1441540 8221297 := bstep (se 2 (by rfl) ⟨3082986, by rfl⟩ : syracuseStep 8221297 = 6165973) B6165973
theorem B2052739 : Blo 1441540 2052739 := bstep (se 1 (by rfl) ⟨1539554, by rfl⟩ : syracuseStep 2052739 = 3079109) B3079109
theorem B4108963 : Blo 1441540 4108963 := bstep (se 1 (by rfl) ⟨3081722, by rfl⟩ : syracuseStep 4108963 = 6163445) B6163445
theorem B5927651 : Blo 1441540 5927651 := bstep (se 1 (by rfl) ⟨4445738, by rfl⟩ : syracuseStep 5927651 = 8891477) B8891477
theorem B4870961 : Blo 1441540 4870961 := bstep (se 2 (by rfl) ⟨1826610, by rfl⟩ : syracuseStep 4870961 = 3653221) B3653221
theorem B4109123 : Blo 1441540 4109123 := bstep (se 1 (by rfl) ⟨3081842, by rfl⟩ : syracuseStep 4109123 = 6163685) B6163685
theorem B3650417 : Blo 1441540 3650417 := bstep (se 2 (by rfl) ⟨1368906, by rfl⟩ : syracuseStep 3650417 = 2737813) B2737813
theorem B6583153 : Blo 1441540 6583153 := bstep (se 2 (by rfl) ⟨2468682, by rfl⟩ : syracuseStep 6583153 = 4937365) B4937365
theorem B3650467 : Blo 1441540 3650467 := bstep (se 1 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 3650467 = 5475701) B5475701
theorem B2438113 : Blo 1441540 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B3650609 : Blo 1441540 3650609 := bstep (se 2 (by rfl) ⟨1368978, by rfl⟩ : syracuseStep 3650609 = 2737957) B2737957
theorem B4936817 : Blo 1441540 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B2053297 : Blo 1441540 2053297 := bstep (se 2 (by rfl) ⟨769986, by rfl⟩ : syracuseStep 2053297 = 1539973) B1539973
theorem B2192627 : Blo 1441540 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B5477645 : Blo 1441540 5477645 := bstep (se 3 (by rfl) ⟨1027058, by rfl⟩ : syracuseStep 5477645 = 2054117) B2054117
theorem B4871501 : Blo 1441540 4871501 := bstep (se 3 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 4871501 = 1826813) B1826813
theorem B4871555 : Blo 1441540 4871555 := bstep (se 1 (by rfl) ⟨3653666, by rfl⟩ : syracuseStep 4871555 = 7307333) B7307333
theorem B9369101 : Blo 1441540 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B28104245 : Blo 1441540 28104245 := bstep (se 5 (by rfl) ⟨1317386, by rfl⟩ : syracuseStep 28104245 = 2634773) B2634773
theorem B12318277 : Blo 1441540 12318277 := bstep (se 4 (by rfl) ⟨1154838, by rfl⟩ : syracuseStep 12318277 = 2309677) B2309677
theorem B4871825 : Blo 1441540 4871825 := bstep (se 2 (by rfl) ⟨1826934, by rfl⟩ : syracuseStep 4871825 = 3653869) B3653869
theorem B4110193 : Blo 1441540 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B2054003 : Blo 1441540 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B1824707 : Blo 1441540 1824707 := bstep (se 1 (by rfl) ⟨1368530, by rfl⟩ : syracuseStep 1824707 = 2737061) B2737061
theorem B8214533 : Blo 1441540 8214533 := bstep (se 4 (by rfl) ⟨770112, by rfl⟩ : syracuseStep 8214533 = 1540225) B1540225
theorem B3651601 : Blo 1441540 3651601 := bstep (se 2 (by rfl) ⟨1369350, by rfl⟩ : syracuseStep 3651601 = 2738701) B2738701
theorem B14997617 : Blo 1441540 14997617 := bstep (se 2 (by rfl) ⟨5624106, by rfl⟩ : syracuseStep 14997617 = 11248213) B11248213
theorem B12327025 : Blo 1441540 12327025 := bstep (se 2 (by rfl) ⟨4622634, by rfl⟩ : syracuseStep 12327025 = 9245269) B9245269
theorem B3897485 : Blo 1441540 3897485 := bstep (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) B1461557
theorem B3897517 : Blo 1441540 3897517 := bstep (se 3 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 3897517 = 1461569) B1461569
theorem B3651875 : Blo 1441540 3651875 := bstep (se 1 (by rfl) ⟨2738906, by rfl⟩ : syracuseStep 3651875 = 5477813) B5477813
theorem B3897667 : Blo 1441540 3897667 := bstep (se 1 (by rfl) ⟨2923250, by rfl⟩ : syracuseStep 3897667 = 5846501) B5846501
theorem B4618637 : Blo 1441540 4618637 := bstep (se 3 (by rfl) ⟨865994, by rfl⟩ : syracuseStep 4618637 = 1731989) B1731989
theorem B1644995 : Blo 1441540 1644995 := bstep (se 1 (by rfl) ⟨1233746, by rfl⟩ : syracuseStep 1644995 = 2467493) B2467493
theorem B3652067 : Blo 1441540 3652067 := bstep (se 1 (by rfl) ⟨2739050, by rfl⟩ : syracuseStep 3652067 = 5478101) B5478101
theorem B2054641 : Blo 1441540 2054641 := bstep (se 2 (by rfl) ⟨770490, by rfl⟩ : syracuseStep 2054641 = 1540981) B1540981
theorem B7305713 : Blo 1441540 7305713 := bstep (se 2 (by rfl) ⟨2739642, by rfl⟩ : syracuseStep 7305713 = 5479285) B5479285
theorem B7307171 : Blo 1441540 7307171 := bstep (se 1 (by rfl) ⟨5480378, by rfl⟩ : syracuseStep 7307171 = 10960757) B10960757
theorem B2923057 : Blo 1441540 2923057 := bstep (se 2 (by rfl) ⟨1096146, by rfl⟩ : syracuseStep 2923057 = 2192293) B2192293
theorem B12491333 : Blo 1441540 12491333 := bstep (se 4 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 12491333 = 2342125) B2342125
theorem B2054755 : Blo 1441540 2054755 := bstep (se 1 (by rfl) ⟨1541066, by rfl⟩ : syracuseStep 2054755 = 3082133) B3082133
theorem B1825411 : Blo 1441540 1825411 := bstep (se 1 (by rfl) ⟨1369058, by rfl⟩ : syracuseStep 1825411 = 2738117) B2738117
theorem B1825507 : Blo 1441540 1825507 := bstep (se 1 (by rfl) ⟨1369130, by rfl⟩ : syracuseStep 1825507 = 2738261) B2738261
theorem B3078947 : Blo 1441540 3078947 := bstep (se 1 (by rfl) ⟨2309210, by rfl⟩ : syracuseStep 3078947 = 4618421) B4618421
theorem B10951523 : Blo 1441540 10951523 := bstep (se 1 (by rfl) ⟨8213642, by rfl⟩ : syracuseStep 10951523 = 16427285) B16427285
theorem B1948531 : Blo 1441540 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B13859909 : Blo 1441540 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B2309267 : Blo 1441540 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B1826003 : Blo 1441540 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B1826707 : Blo 1441540 1826707 := bstep (se 1 (by rfl) ⟨1370030, by rfl⟩ : syracuseStep 1826707 = 2740061) B2740061
theorem B5479757 : Blo 1441540 5479757 := bstep (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) B2054909
theorem B2342225 : Blo 1441540 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B2194769 : Blo 1441540 2194769 := bstep (se 2 (by rfl) ⟨823038, by rfl⟩ : syracuseStep 2194769 = 1646077) B1646077
theorem B10394993 : Blo 1441540 10394993 := bstep (se 2 (by rfl) ⟨3898122, by rfl⟩ : syracuseStep 10394993 = 7796245) B7796245
theorem B27745649 : Blo 1441540 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B1539443 : Blo 1441540 1539443 := bstep (se 1 (by rfl) ⟨1154582, by rfl⟩ : syracuseStep 1539443 = 2309165) B2309165
theorem B3653009 : Blo 1441540 3653009 := bstep (se 2 (by rfl) ⟨1369878, by rfl⟩ : syracuseStep 3653009 = 2739757) B2739757
theorem B4865453 : Blo 1441540 4865453 := bstep (se 3 (by rfl) ⟨912272, by rfl⟩ : syracuseStep 4865453 = 1824545) B1824545
theorem B3653059 : Blo 1441540 3653059 := bstep (se 1 (by rfl) ⟨2739794, by rfl⟩ : syracuseStep 3653059 = 5479589) B5479589
theorem B3243473 : Blo 1441540 3243473 := bstep (se 2 (by rfl) ⟨1216302, by rfl⟩ : syracuseStep 3243473 = 2432605) B2432605
theorem B2776529 : Blo 1441540 2776529 := bstep (se 2 (by rfl) ⟨1041198, by rfl⟩ : syracuseStep 2776529 = 2082397) B2082397
theorem B3243491 : Blo 1441540 3243491 := bstep (se 1 (by rfl) ⟨2432618, by rfl⟩ : syracuseStep 3243491 = 4865237) B4865237
theorem B4865507 : Blo 1441540 4865507 := bstep (se 1 (by rfl) ⟨3649130, by rfl⟩ : syracuseStep 4865507 = 7298261) B7298261
theorem B3464785 : Blo 1441540 3464785 := bstep (se 2 (by rfl) ⟨1299294, by rfl⟩ : syracuseStep 3464785 = 2598589) B2598589
theorem B3653201 : Blo 1441540 3653201 := bstep (se 2 (by rfl) ⟨1369950, by rfl⟩ : syracuseStep 3653201 = 2739901) B2739901
theorem B20799089 : Blo 1441540 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B2162321 : Blo 1441540 2162321 := bstep (se 2 (by rfl) ⟨810870, by rfl⟩ : syracuseStep 2162321 = 1621741) B1621741
theorem B2432659 : Blo 1441540 2432659 := bstep (se 1 (by rfl) ⟨1824494, by rfl⟩ : syracuseStep 2432659 = 3648989) B3648989
theorem B2162339 : Blo 1441540 2162339 := bstep (se 1 (by rfl) ⟨1621754, by rfl⟩ : syracuseStep 2162339 = 3243509) B3243509
theorem B2162369 : Blo 1441540 2162369 := bstep (se 2 (by rfl) ⟨810888, by rfl⟩ : syracuseStep 2162369 = 1621777) B1621777
theorem B2162387 : Blo 1441540 2162387 := bstep (se 1 (by rfl) ⟨1621790, by rfl⟩ : syracuseStep 2162387 = 3243581) B3243581
theorem B2162417 : Blo 1441540 2162417 := bstep (se 2 (by rfl) ⟨810906, by rfl⟩ : syracuseStep 2162417 = 1621813) B1621813
theorem B3243761 : Blo 1441540 3243761 := bstep (se 2 (by rfl) ⟨1216410, by rfl⟩ : syracuseStep 3243761 = 2432821) B2432821
theorem B4865777 : Blo 1441540 4865777 := bstep (se 2 (by rfl) ⟨1824666, by rfl⟩ : syracuseStep 4865777 = 3649333) B3649333
theorem B2162435 : Blo 1441540 2162435 := bstep (se 1 (by rfl) ⟨1621826, by rfl⟩ : syracuseStep 2162435 = 3243653) B3243653
theorem B3243779 : Blo 1441540 3243779 := bstep (se 1 (by rfl) ⟨2432834, by rfl⟩ : syracuseStep 3243779 = 4865669) B4865669
theorem B1441555 : Blo 1441540 1441555 := bstep (se 1 (by rfl) ⟨1081166, by rfl⟩ : syracuseStep 1441555 = 2162333) B2162333
theorem B2162465 : Blo 1441540 2162465 := bstep (se 2 (by rfl) ⟨810924, by rfl⟩ : syracuseStep 2162465 = 1621849) B1621849
theorem B2432801 : Blo 1441540 2432801 := bstep (se 2 (by rfl) ⟨912300, by rfl⟩ : syracuseStep 2432801 = 1824601) B1824601
theorem B1441571 : Blo 1441540 1441571 := bstep (se 1 (by rfl) ⟨1081178, by rfl⟩ : syracuseStep 1441571 = 2162357) B2162357
theorem B1621795 : Blo 1441540 1621795 := bstep (se 1 (by rfl) ⟨1216346, by rfl⟩ : syracuseStep 1621795 = 2432693) B2432693
theorem B1441587 : Blo 1441540 1441587 := bstep (se 1 (by rfl) ⟨1081190, by rfl⟩ : syracuseStep 1441587 = 2162381) B2162381
theorem B2162483 : Blo 1441540 2162483 := bstep (se 1 (by rfl) ⟨1621862, by rfl⟩ : syracuseStep 2162483 = 3243725) B3243725
theorem B1441603 : Blo 1441540 1441603 := bstep (se 1 (by rfl) ⟨1081202, by rfl⟩ : syracuseStep 1441603 = 2162405) B2162405
theorem B2162513 : Blo 1441540 2162513 := bstep (se 2 (by rfl) ⟨810942, by rfl⟩ : syracuseStep 2162513 = 1621885) B1621885
theorem B1441619 : Blo 1441540 1441619 := bstep (se 1 (by rfl) ⟨1081214, by rfl⟩ : syracuseStep 1441619 = 2162429) B2162429
theorem B1441635 : Blo 1441540 1441635 := bstep (se 1 (by rfl) ⟨1081226, by rfl⟩ : syracuseStep 1441635 = 2162453) B2162453
theorem B2162531 : Blo 1441540 2162531 := bstep (se 1 (by rfl) ⟨1621898, by rfl⟩ : syracuseStep 2162531 = 3243797) B3243797
theorem B1441651 : Blo 1441540 1441651 := bstep (se 1 (by rfl) ⟨1081238, by rfl⟩ : syracuseStep 1441651 = 2162477) B2162477
theorem B2162561 : Blo 1441540 2162561 := bstep (se 2 (by rfl) ⟨810960, by rfl⟩ : syracuseStep 2162561 = 1621921) B1621921
theorem B1441667 : Blo 1441540 1441667 := bstep (se 1 (by rfl) ⟨1081250, by rfl⟩ : syracuseStep 1441667 = 2162501) B2162501
theorem B1441683 : Blo 1441540 1441683 := bstep (se 1 (by rfl) ⟨1081262, by rfl⟩ : syracuseStep 1441683 = 2162525) B2162525
theorem B2162579 : Blo 1441540 2162579 := bstep (se 1 (by rfl) ⟨1621934, by rfl⟩ : syracuseStep 2162579 = 3243869) B3243869
theorem B2310049 : Blo 1441540 2310049 := bstep (se 2 (by rfl) ⟨866268, by rfl⟩ : syracuseStep 2310049 = 1732537) B1732537
theorem B1441699 : Blo 1441540 1441699 := bstep (se 1 (by rfl) ⟨1081274, by rfl⟩ : syracuseStep 1441699 = 2162549) B2162549
theorem B2432929 : Blo 1441540 2432929 := bstep (se 2 (by rfl) ⟨912348, by rfl⟩ : syracuseStep 2432929 = 1824697) B1824697
theorem B4620881 : Blo 1441540 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B2162609 : Blo 1441540 2162609 := bstep (se 2 (by rfl) ⟨810978, by rfl⟩ : syracuseStep 2162609 = 1621957) B1621957
theorem B1441715 : Blo 1441540 1441715 := bstep (se 1 (by rfl) ⟨1081286, by rfl⟩ : syracuseStep 1441715 = 2162573) B2162573
theorem B1621939 : Blo 1441540 1621939 := bstep (se 1 (by rfl) ⟨1216454, by rfl⟩ : syracuseStep 1621939 = 2432909) B2432909
theorem B1441731 : Blo 1441540 1441731 := bstep (se 1 (by rfl) ⟨1081298, by rfl⟩ : syracuseStep 1441731 = 2162597) B2162597
theorem B2162627 : Blo 1441540 2162627 := bstep (se 1 (by rfl) ⟨1621970, by rfl⟩ : syracuseStep 2162627 = 3243941) B3243941
theorem B2432963 : Blo 1441540 2432963 := bstep (se 1 (by rfl) ⟨1824722, by rfl⟩ : syracuseStep 2432963 = 3649445) B3649445
theorem B1441747 : Blo 1441540 1441747 := bstep (se 1 (by rfl) ⟨1081310, by rfl⟩ : syracuseStep 1441747 = 2162621) B2162621
theorem B2162657 : Blo 1441540 2162657 := bstep (se 2 (by rfl) ⟨810996, by rfl⟩ : syracuseStep 2162657 = 1621993) B1621993
theorem B1441763 : Blo 1441540 1441763 := bstep (se 1 (by rfl) ⟨1081322, by rfl⟩ : syracuseStep 1441763 = 2162645) B2162645
theorem B3080177 : Blo 1441540 3080177 := bstep (se 2 (by rfl) ⟨1155066, by rfl⟩ : syracuseStep 3080177 = 2310133) B2310133
theorem B6160369 : Blo 1441540 6160369 := bstep (se 2 (by rfl) ⟨2310138, by rfl⟩ : syracuseStep 6160369 = 4620277) B4620277
theorem B1441779 : Blo 1441540 1441779 := bstep (se 1 (by rfl) ⟨1081334, by rfl⟩ : syracuseStep 1441779 = 2162669) B2162669
theorem B2162675 : Blo 1441540 2162675 := bstep (se 1 (by rfl) ⟨1622006, by rfl⟩ : syracuseStep 2162675 = 3244013) B3244013
theorem B12492785 : Blo 1441540 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B1826803 : Blo 1441540 1826803 := bstep (se 1 (by rfl) ⟨1370102, by rfl⟩ : syracuseStep 1826803 = 2740205) B2740205
theorem B2162699 : Blo 1441540 2162699 := bstep (se 1 (by rfl) ⟨1622024, by rfl⟩ : syracuseStep 2162699 = 3244049) B3244049
theorem B1441803 : Blo 1441540 1441803 := bstep (se 1 (by rfl) ⟨1081352, by rfl⟩ : syracuseStep 1441803 = 2162705) B2162705
theorem B2162711 : Blo 1441540 2162711 := bstep (se 1 (by rfl) ⟨1622033, by rfl⟩ : syracuseStep 2162711 = 3244067) B3244067
theorem B1441815 : Blo 1441540 1441815 := bstep (se 1 (by rfl) ⟨1081361, by rfl⟩ : syracuseStep 1441815 = 2162723) B2162723
theorem B1441835 : Blo 1441540 1441835 := bstep (se 1 (by rfl) ⟨1081376, by rfl⟩ : syracuseStep 1441835 = 2162753) B2162753
theorem B1441847 : Blo 1441540 1441847 := bstep (se 1 (by rfl) ⟨1081385, by rfl⟩ : syracuseStep 1441847 = 2162771) B2162771
theorem B7118923 : Blo 1441540 7118923 := bstep (se 1 (by rfl) ⟨5339192, by rfl⟩ : syracuseStep 7118923 = 10678385) B10678385
theorem B1441867 : Blo 1441540 1441867 := bstep (se 1 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 1441867 = 2162801) B2162801
theorem B3653707 : Blo 1441540 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B1441879 : Blo 1441540 1441879 := bstep (se 1 (by rfl) ⟨1081409, by rfl⟩ : syracuseStep 1441879 = 2162819) B2162819
theorem B3244121 : Blo 1441540 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B2162777 : Blo 1441540 2162777 := bstep (se 2 (by rfl) ⟨811041, by rfl⟩ : syracuseStep 2162777 = 1622083) B1622083
theorem B1441899 : Blo 1441540 1441899 := bstep (se 1 (by rfl) ⟨1081424, by rfl⟩ : syracuseStep 1441899 = 2162849) B2162849
theorem B1441911 : Blo 1441540 1441911 := bstep (se 1 (by rfl) ⟨1081433, by rfl⟩ : syracuseStep 1441911 = 2162867) B2162867
theorem B1622155 : Blo 1441540 1622155 := bstep (se 1 (by rfl) ⟨1216616, by rfl⟩ : syracuseStep 1622155 = 2433233) B2433233
theorem B1441931 : Blo 1441540 1441931 := bstep (se 1 (by rfl) ⟨1081448, by rfl⟩ : syracuseStep 1441931 = 2162897) B2162897
theorem B1441943 : Blo 1441540 1441943 := bstep (se 1 (by rfl) ⟨1081457, by rfl⟩ : syracuseStep 1441943 = 2162915) B2162915
theorem B1441963 : Blo 1441540 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B3244211 : Blo 1441540 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B1441975 : Blo 1441540 1441975 := bstep (se 1 (by rfl) ⟨1081481, by rfl⟩ : syracuseStep 1441975 = 2162963) B2162963
theorem B4161739 : Blo 1441540 4161739 := bstep (se 1 (by rfl) ⟨3121304, by rfl⟩ : syracuseStep 4161739 = 6242609) B6242609
theorem B2162891 : Blo 1441540 2162891 := bstep (se 1 (by rfl) ⟨1622168, by rfl⟩ : syracuseStep 2162891 = 3244337) B3244337
theorem B1441995 : Blo 1441540 1441995 := bstep (se 1 (by rfl) ⟨1081496, by rfl⟩ : syracuseStep 1441995 = 2162993) B2162993
theorem B3244247 : Blo 1441540 3244247 := bstep (se 1 (by rfl) ⟨2433185, by rfl⟩ : syracuseStep 3244247 = 4866371) B4866371
theorem B2162903 : Blo 1441540 2162903 := bstep (se 1 (by rfl) ⟨1622177, by rfl⟩ : syracuseStep 2162903 = 3244355) B3244355
theorem B1442007 : Blo 1441540 1442007 := bstep (se 1 (by rfl) ⟨1081505, by rfl⟩ : syracuseStep 1442007 = 2163011) B2163011
theorem B3653849 : Blo 1441540 3653849 := bstep (se 2 (by rfl) ⟨1370193, by rfl⟩ : syracuseStep 3653849 = 2740387) B2740387
theorem B4620509 : Blo 1441540 4620509 := bstep (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) B1732691
theorem B1442027 : Blo 1441540 1442027 := bstep (se 1 (by rfl) ⟨1081520, by rfl⟩ : syracuseStep 1442027 = 2163041) B2163041
theorem B1622263 : Blo 1441540 1622263 := bstep (se 1 (by rfl) ⟨1216697, by rfl⟩ : syracuseStep 1622263 = 2433395) B2433395
theorem B1442039 : Blo 1441540 1442039 := bstep (se 1 (by rfl) ⟨1081529, by rfl⟩ : syracuseStep 1442039 = 2163059) B2163059
theorem B6160643 : Blo 1441540 6160643 := bstep (se 1 (by rfl) ⟨4620482, by rfl⟩ : syracuseStep 6160643 = 9240965) B9240965
theorem B1442059 : Blo 1441540 1442059 := bstep (se 1 (by rfl) ⟨1081544, by rfl⟩ : syracuseStep 1442059 = 2163089) B2163089
theorem B1442071 : Blo 1441540 1442071 := bstep (se 1 (by rfl) ⟨1081553, by rfl⟩ : syracuseStep 1442071 = 2163107) B2163107
theorem B2162969 : Blo 1441540 2162969 := bstep (se 2 (by rfl) ⟨811113, by rfl⟩ : syracuseStep 2162969 = 1622227) B1622227
theorem B1442091 : Blo 1441540 1442091 := bstep (se 1 (by rfl) ⟨1081568, by rfl⟩ : syracuseStep 1442091 = 2163137) B2163137
theorem B1442103 : Blo 1441540 1442103 := bstep (se 1 (by rfl) ⟨1081577, by rfl⟩ : syracuseStep 1442103 = 2163155) B2163155
theorem B3703105 : Blo 1441540 3703105 := bstep (se 2 (by rfl) ⟨1388664, by rfl⟩ : syracuseStep 3703105 = 2777329) B2777329
theorem B1442123 : Blo 1441540 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B1442135 : Blo 1441540 1442135 := bstep (se 1 (by rfl) ⟨1081601, by rfl⟩ : syracuseStep 1442135 = 2163203) B2163203
theorem B1442155 : Blo 1441540 1442155 := bstep (se 1 (by rfl) ⟨1081616, by rfl⟩ : syracuseStep 1442155 = 2163233) B2163233
theorem B1442167 : Blo 1441540 1442167 := bstep (se 1 (by rfl) ⟨1081625, by rfl⟩ : syracuseStep 1442167 = 2163251) B2163251
theorem B3244427 : Blo 1441540 3244427 := bstep (se 1 (by rfl) ⟨2433320, by rfl⟩ : syracuseStep 3244427 = 4866641) B4866641
theorem B2163083 : Blo 1441540 2163083 := bstep (se 1 (by rfl) ⟨1622312, by rfl⟩ : syracuseStep 2163083 = 3244625) B3244625
theorem B1442187 : Blo 1441540 1442187 := bstep (se 1 (by rfl) ⟨1081640, by rfl⟩ : syracuseStep 1442187 = 2163281) B2163281
theorem B3080587 : Blo 1441540 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B1483147 : Blo 1441540 1483147 := bstep (se 1 (by rfl) ⟨1112360, by rfl⟩ : syracuseStep 1483147 = 2224721) B2224721
theorem B2163095 : Blo 1441540 2163095 := bstep (se 1 (by rfl) ⟨1622321, by rfl⟩ : syracuseStep 2163095 = 3244643) B3244643
theorem B1442199 : Blo 1441540 1442199 := bstep (se 1 (by rfl) ⟨1081649, by rfl⟩ : syracuseStep 1442199 = 2163299) B2163299
theorem B1622443 : Blo 1441540 1622443 := bstep (se 1 (by rfl) ⟨1216832, by rfl⟩ : syracuseStep 1622443 = 2433665) B2433665
theorem B1442219 : Blo 1441540 1442219 := bstep (se 1 (by rfl) ⟨1081664, by rfl⟩ : syracuseStep 1442219 = 2163329) B2163329
theorem B1442231 : Blo 1441540 1442231 := bstep (se 1 (by rfl) ⟨1081673, by rfl⟩ : syracuseStep 1442231 = 2163347) B2163347
theorem B3244481 : Blo 1441540 3244481 := bstep (se 2 (by rfl) ⟨1216680, by rfl⟩ : syracuseStep 3244481 = 2433361) B2433361
theorem B1442251 : Blo 1441540 1442251 := bstep (se 1 (by rfl) ⟨1081688, by rfl⟩ : syracuseStep 1442251 = 2163377) B2163377
theorem B1442263 : Blo 1441540 1442263 := bstep (se 1 (by rfl) ⟨1081697, by rfl⟩ : syracuseStep 1442263 = 2163395) B2163395
theorem B2163161 : Blo 1441540 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B1540567 : Blo 1441540 1540567 := bstep (se 1 (by rfl) ⟨1155425, by rfl⟩ : syracuseStep 1540567 = 2310851) B2310851
theorem B1442283 : Blo 1441540 1442283 := bstep (se 1 (by rfl) ⟨1081712, by rfl⟩ : syracuseStep 1442283 = 2163425) B2163425
theorem B1442295 : Blo 1441540 1442295 := bstep (se 1 (by rfl) ⟨1081721, by rfl⟩ : syracuseStep 1442295 = 2163443) B2163443
theorem B1442315 : Blo 1441540 1442315 := bstep (se 1 (by rfl) ⟨1081736, by rfl⟩ : syracuseStep 1442315 = 2163473) B2163473
theorem B5849617 : Blo 1441540 5849617 := bstep (se 2 (by rfl) ⟨2193606, by rfl⟩ : syracuseStep 5849617 = 4387213) B4387213
theorem B1622551 : Blo 1441540 1622551 := bstep (se 1 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 1622551 = 2433827) B2433827
theorem B1442327 : Blo 1441540 1442327 := bstep (se 1 (by rfl) ⟨1081745, by rfl⟩ : syracuseStep 1442327 = 2163491) B2163491
theorem B1442347 : Blo 1441540 1442347 := bstep (se 1 (by rfl) ⟨1081760, by rfl⟩ : syracuseStep 1442347 = 2163521) B2163521
theorem B1442359 : Blo 1441540 1442359 := bstep (se 1 (by rfl) ⟨1081769, by rfl⟩ : syracuseStep 1442359 = 2163539) B2163539
theorem B2433611 : Blo 1441540 2433611 := bstep (se 1 (by rfl) ⟨1825208, by rfl⟩ : syracuseStep 2433611 = 3650417) B3650417
theorem B2163275 : Blo 1441540 2163275 := bstep (se 1 (by rfl) ⟨1622456, by rfl⟩ : syracuseStep 2163275 = 3244913) B3244913
theorem B1442379 : Blo 1441540 1442379 := bstep (se 1 (by rfl) ⟨1081784, by rfl⟩ : syracuseStep 1442379 = 2163569) B2163569
theorem B2163287 : Blo 1441540 2163287 := bstep (se 1 (by rfl) ⟨1622465, by rfl⟩ : syracuseStep 2163287 = 3244931) B3244931
theorem B6160985 : Blo 1441540 6160985 := bstep (se 2 (by rfl) ⟨2310369, by rfl⟩ : syracuseStep 6160985 = 4620739) B4620739
theorem B1442391 : Blo 1441540 1442391 := bstep (se 1 (by rfl) ⟨1081793, by rfl⟩ : syracuseStep 1442391 = 2163587) B2163587
theorem B1442411 : Blo 1441540 1442411 := bstep (se 1 (by rfl) ⟨1081808, by rfl⟩ : syracuseStep 1442411 = 2163617) B2163617
theorem B1442423 : Blo 1441540 1442423 := bstep (se 1 (by rfl) ⟨1081817, by rfl⟩ : syracuseStep 1442423 = 2163635) B2163635
theorem B1442443 : Blo 1441540 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B1442455 : Blo 1441540 1442455 := bstep (se 1 (by rfl) ⟨1081841, by rfl⟩ : syracuseStep 1442455 = 2163683) B2163683
theorem B3244697 : Blo 1441540 3244697 := bstep (se 2 (by rfl) ⟨1216761, by rfl⟩ : syracuseStep 3244697 = 2433523) B2433523
theorem B2163353 : Blo 1441540 2163353 := bstep (se 2 (by rfl) ⟨811257, by rfl⟩ : syracuseStep 2163353 = 1622515) B1622515
theorem B1442475 : Blo 1441540 1442475 := bstep (se 1 (by rfl) ⟨1081856, by rfl⟩ : syracuseStep 1442475 = 2163713) B2163713
theorem B1442487 : Blo 1441540 1442487 := bstep (se 1 (by rfl) ⟨1081865, by rfl⟩ : syracuseStep 1442487 = 2163731) B2163731
theorem B2433739 : Blo 1441540 2433739 := bstep (se 1 (by rfl) ⟨1825304, by rfl⟩ : syracuseStep 2433739 = 3650609) B3650609
theorem B1622731 : Blo 1441540 1622731 := bstep (se 1 (by rfl) ⟨1217048, by rfl⟩ : syracuseStep 1622731 = 2434097) B2434097
theorem B1442507 : Blo 1441540 1442507 := bstep (se 1 (by rfl) ⟨1081880, by rfl⟩ : syracuseStep 1442507 = 2163761) B2163761
theorem B1442519 : Blo 1441540 1442519 := bstep (se 1 (by rfl) ⟨1081889, by rfl⟩ : syracuseStep 1442519 = 2163779) B2163779
theorem B1442539 : Blo 1441540 1442539 := bstep (se 1 (by rfl) ⟨1081904, by rfl⟩ : syracuseStep 1442539 = 2163809) B2163809
theorem B3244787 : Blo 1441540 3244787 := bstep (se 1 (by rfl) ⟨2433590, by rfl⟩ : syracuseStep 3244787 = 4867181) B4867181
theorem B1442551 : Blo 1441540 1442551 := bstep (se 1 (by rfl) ⟨1081913, by rfl⟩ : syracuseStep 1442551 = 2163827) B2163827
theorem B2163467 : Blo 1441540 2163467 := bstep (se 1 (by rfl) ⟨1622600, by rfl⟩ : syracuseStep 2163467 = 3245201) B3245201
theorem B1442571 : Blo 1441540 1442571 := bstep (se 1 (by rfl) ⟨1081928, by rfl⟩ : syracuseStep 1442571 = 2163857) B2163857
theorem B3244823 : Blo 1441540 3244823 := bstep (se 1 (by rfl) ⟨2433617, by rfl⟩ : syracuseStep 3244823 = 4867235) B4867235
theorem B2163479 : Blo 1441540 2163479 := bstep (se 1 (by rfl) ⟨1622609, by rfl⟩ : syracuseStep 2163479 = 3245219) B3245219
theorem B2851609 : Blo 1441540 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B1442583 : Blo 1441540 1442583 := bstep (se 1 (by rfl) ⟨1081937, by rfl⟩ : syracuseStep 1442583 = 2163875) B2163875
theorem B1442603 : Blo 1441540 1442603 := bstep (se 1 (by rfl) ⟨1081952, by rfl⟩ : syracuseStep 1442603 = 2163905) B2163905
theorem B1622839 : Blo 1441540 1622839 := bstep (se 1 (by rfl) ⟨1217129, by rfl⟩ : syracuseStep 1622839 = 2434259) B2434259
theorem B1442615 : Blo 1441540 1442615 := bstep (se 1 (by rfl) ⟨1081961, by rfl⟩ : syracuseStep 1442615 = 2163923) B2163923
theorem B10961729 : Blo 1441540 10961729 := bstep (se 2 (by rfl) ⟨4110648, by rfl⟩ : syracuseStep 10961729 = 8221297) B8221297
theorem B1442635 : Blo 1441540 1442635 := bstep (se 1 (by rfl) ⟨1081976, by rfl⟩ : syracuseStep 1442635 = 2163953) B2163953
theorem B1442647 : Blo 1441540 1442647 := bstep (se 1 (by rfl) ⟨1081985, by rfl⟩ : syracuseStep 1442647 = 2163971) B2163971
theorem B2736985 : Blo 1441540 2736985 := bstep (se 2 (by rfl) ⟨1026369, by rfl⟩ : syracuseStep 2736985 = 2052739) B2052739
theorem B2433881 : Blo 1441540 2433881 := bstep (se 2 (by rfl) ⟨912705, by rfl⟩ : syracuseStep 2433881 = 1825411) B1825411
theorem B2163545 : Blo 1441540 2163545 := bstep (se 2 (by rfl) ⟨811329, by rfl⟩ : syracuseStep 2163545 = 1622659) B1622659
theorem B3900253 : Blo 1441540 3900253 := bstep (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) B1462595
theorem B1442667 : Blo 1441540 1442667 := bstep (se 1 (by rfl) ⟨1082000, by rfl⟩ : syracuseStep 1442667 = 2164001) B2164001
theorem B1442679 : Blo 1441540 1442679 := bstep (se 1 (by rfl) ⟨1082009, by rfl⟩ : syracuseStep 1442679 = 2164019) B2164019
theorem B1442699 : Blo 1441540 1442699 := bstep (se 1 (by rfl) ⟨1082024, by rfl⟩ : syracuseStep 1442699 = 2164049) B2164049
theorem B1442711 : Blo 1441540 1442711 := bstep (se 1 (by rfl) ⟨1082033, by rfl⟩ : syracuseStep 1442711 = 2164067) B2164067
theorem B1442731 : Blo 1441540 1442731 := bstep (se 1 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 1442731 = 2164097) B2164097
theorem B22217651 : Blo 1441540 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B1442743 : Blo 1441540 1442743 := bstep (se 1 (by rfl) ⟨1082057, by rfl⟩ : syracuseStep 1442743 = 2164115) B2164115
theorem B4867019 : Blo 1441540 4867019 := bstep (se 1 (by rfl) ⟨3650264, by rfl⟩ : syracuseStep 4867019 = 7300529) B7300529
theorem B3245003 : Blo 1441540 3245003 := bstep (se 1 (by rfl) ⟨2433752, by rfl⟩ : syracuseStep 3245003 = 4867505) B4867505
theorem B2163659 : Blo 1441540 2163659 := bstep (se 1 (by rfl) ⟨1622744, by rfl⟩ : syracuseStep 2163659 = 3245489) B3245489
theorem B1442763 : Blo 1441540 1442763 := bstep (se 1 (by rfl) ⟨1082072, by rfl⟩ : syracuseStep 1442763 = 2164145) B2164145
theorem B2163671 : Blo 1441540 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B1442775 : Blo 1441540 1442775 := bstep (se 1 (by rfl) ⟨1082081, by rfl⟩ : syracuseStep 1442775 = 2164163) B2164163
theorem B2434009 : Blo 1441540 2434009 := bstep (se 2 (by rfl) ⟨912753, by rfl⟩ : syracuseStep 2434009 = 1825507) B1825507
theorem B4105181 : Blo 1441540 4105181 := bstep (se 3 (by rfl) ⟨769721, by rfl⟩ : syracuseStep 4105181 = 1539443) B1539443
theorem B1623019 : Blo 1441540 1623019 := bstep (se 1 (by rfl) ⟨1217264, by rfl⟩ : syracuseStep 1623019 = 2434529) B2434529
theorem B1442795 : Blo 1441540 1442795 := bstep (se 1 (by rfl) ⟨1082096, by rfl⟩ : syracuseStep 1442795 = 2164193) B2164193
theorem B1442807 : Blo 1441540 1442807 := bstep (se 1 (by rfl) ⟨1082105, by rfl⟩ : syracuseStep 1442807 = 2164211) B2164211
theorem B3245057 : Blo 1441540 3245057 := bstep (se 2 (by rfl) ⟨1216896, by rfl⟩ : syracuseStep 3245057 = 2433793) B2433793
theorem B1442827 : Blo 1441540 1442827 := bstep (se 1 (by rfl) ⟨1082120, by rfl⟩ : syracuseStep 1442827 = 2164241) B2164241
theorem B1442839 : Blo 1441540 1442839 := bstep (se 1 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 1442839 = 2164259) B2164259
theorem B2163737 : Blo 1441540 2163737 := bstep (se 2 (by rfl) ⟨811401, by rfl⟩ : syracuseStep 2163737 = 1622803) B1622803
theorem B18736163 : Blo 1441540 18736163 := bstep (se 1 (by rfl) ⟨14052122, by rfl⟩ : syracuseStep 18736163 = 28104245) B28104245
theorem B1442859 : Blo 1441540 1442859 := bstep (se 1 (by rfl) ⟨1082144, by rfl⟩ : syracuseStep 1442859 = 2164289) B2164289
theorem B1442871 : Blo 1441540 1442871 := bstep (se 1 (by rfl) ⟨1082153, by rfl⟩ : syracuseStep 1442871 = 2164307) B2164307
theorem B1442891 : Blo 1441540 1442891 := bstep (se 1 (by rfl) ⟨1082168, by rfl⟩ : syracuseStep 1442891 = 2164337) B2164337
theorem B1623127 : Blo 1441540 1623127 := bstep (se 1 (by rfl) ⟨1217345, by rfl⟩ : syracuseStep 1623127 = 2434691) B2434691
theorem B1442903 : Blo 1441540 1442903 := bstep (se 1 (by rfl) ⟨1082177, by rfl⟩ : syracuseStep 1442903 = 2164355) B2164355
theorem B1442923 : Blo 1441540 1442923 := bstep (se 1 (by rfl) ⟨1082192, by rfl⟩ : syracuseStep 1442923 = 2164385) B2164385
theorem B1442935 : Blo 1441540 1442935 := bstep (se 1 (by rfl) ⟨1082201, by rfl⟩ : syracuseStep 1442935 = 2164403) B2164403
theorem B2163851 : Blo 1441540 2163851 := bstep (se 1 (by rfl) ⟨1622888, by rfl⟩ : syracuseStep 2163851 = 3245777) B3245777
theorem B1442955 : Blo 1441540 1442955 := bstep (se 1 (by rfl) ⟨1082216, by rfl⟩ : syracuseStep 1442955 = 2164433) B2164433
theorem B2163863 : Blo 1441540 2163863 := bstep (se 1 (by rfl) ⟨1622897, by rfl⟩ : syracuseStep 2163863 = 3245795) B3245795
theorem B1442967 : Blo 1441540 1442967 := bstep (se 1 (by rfl) ⟨1082225, by rfl⟩ : syracuseStep 1442967 = 2164451) B2164451
theorem B2598041 : Blo 1441540 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B1442987 : Blo 1441540 1442987 := bstep (se 1 (by rfl) ⟨1082240, by rfl⟩ : syracuseStep 1442987 = 2164481) B2164481
theorem B5473453 : Blo 1441540 5473453 := bstep (se 3 (by rfl) ⟨1026272, by rfl⟩ : syracuseStep 5473453 = 2052545) B2052545
theorem B1442999 : Blo 1441540 1442999 := bstep (se 1 (by rfl) ⟨1082249, by rfl⟩ : syracuseStep 1442999 = 2164499) B2164499
theorem B1443019 : Blo 1441540 1443019 := bstep (se 1 (by rfl) ⟨1082264, by rfl⟩ : syracuseStep 1443019 = 2164529) B2164529
theorem B1443031 : Blo 1441540 1443031 := bstep (se 1 (by rfl) ⟨1082273, by rfl⟩ : syracuseStep 1443031 = 2164547) B2164547
theorem B4867289 : Blo 1441540 4867289 := bstep (se 2 (by rfl) ⟨1825233, by rfl⟩ : syracuseStep 4867289 = 3650467) B3650467
theorem B3245273 : Blo 1441540 3245273 := bstep (se 2 (by rfl) ⟨1216977, by rfl⟩ : syracuseStep 3245273 = 2433955) B2433955
theorem B2163929 : Blo 1441540 2163929 := bstep (se 2 (by rfl) ⟨811473, by rfl⟩ : syracuseStep 2163929 = 1622947) B1622947
theorem B1443051 : Blo 1441540 1443051 := bstep (se 1 (by rfl) ⟨1082288, by rfl⟩ : syracuseStep 1443051 = 2164577) B2164577
theorem B1443063 : Blo 1441540 1443063 := bstep (se 1 (by rfl) ⟨1082297, by rfl⟩ : syracuseStep 1443063 = 2164595) B2164595
theorem B1623307 : Blo 1441540 1623307 := bstep (se 1 (by rfl) ⟨1217480, by rfl⟩ : syracuseStep 1623307 = 2434961) B2434961
theorem B1443083 : Blo 1441540 1443083 := bstep (se 1 (by rfl) ⟨1082312, by rfl⟩ : syracuseStep 1443083 = 2164625) B2164625
theorem B1541387 : Blo 1441540 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1443095 : Blo 1441540 1443095 := bstep (se 1 (by rfl) ⟨1082321, by rfl⟩ : syracuseStep 1443095 = 2164643) B2164643
theorem B1443115 : Blo 1441540 1443115 := bstep (se 1 (by rfl) ⟨1082336, by rfl⟩ : syracuseStep 1443115 = 2164673) B2164673
theorem B3245363 : Blo 1441540 3245363 := bstep (se 1 (by rfl) ⟨2434022, by rfl⟩ : syracuseStep 3245363 = 4868045) B4868045
theorem B1443127 : Blo 1441540 1443127 := bstep (se 1 (by rfl) ⟨1082345, by rfl⟩ : syracuseStep 1443127 = 2164691) B2164691
theorem B2164043 : Blo 1441540 2164043 := bstep (se 1 (by rfl) ⟨1623032, by rfl⟩ : syracuseStep 2164043 = 3246065) B3246065
theorem B1443147 : Blo 1441540 1443147 := bstep (se 1 (by rfl) ⟨1082360, by rfl⟩ : syracuseStep 1443147 = 2164721) B2164721
theorem B3245399 : Blo 1441540 3245399 := bstep (se 1 (by rfl) ⟨2434049, by rfl⟩ : syracuseStep 3245399 = 4868099) B4868099
theorem B2164055 : Blo 1441540 2164055 := bstep (se 1 (by rfl) ⟨1623041, by rfl⟩ : syracuseStep 2164055 = 3246083) B3246083
theorem B1443159 : Blo 1441540 1443159 := bstep (se 1 (by rfl) ⟨1082369, by rfl⟩ : syracuseStep 1443159 = 2164739) B2164739
theorem B1443179 : Blo 1441540 1443179 := bstep (se 1 (by rfl) ⟨1082384, by rfl⟩ : syracuseStep 1443179 = 2164769) B2164769
theorem B1623415 : Blo 1441540 1623415 := bstep (se 1 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 1623415 = 2435123) B2435123
theorem B1443191 : Blo 1441540 1443191 := bstep (se 1 (by rfl) ⟨1082393, by rfl⟩ : syracuseStep 1443191 = 2164787) B2164787
theorem B2737547 : Blo 1441540 2737547 := bstep (se 1 (by rfl) ⟨2053160, by rfl⟩ : syracuseStep 2737547 = 4106321) B4106321
theorem B1443211 : Blo 1441540 1443211 := bstep (se 1 (by rfl) ⟨1082408, by rfl⟩ : syracuseStep 1443211 = 2164817) B2164817
theorem B1443223 : Blo 1441540 1443223 := bstep (se 1 (by rfl) ⟨1082417, by rfl⟩ : syracuseStep 1443223 = 2164835) B2164835
theorem B2164121 : Blo 1441540 2164121 := bstep (se 2 (by rfl) ⟨811545, by rfl⟩ : syracuseStep 2164121 = 1623091) B1623091
theorem B1443243 : Blo 1441540 1443243 := bstep (se 1 (by rfl) ⟨1082432, by rfl⟩ : syracuseStep 1443243 = 2164865) B2164865
theorem B2598323 : Blo 1441540 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B1443255 : Blo 1441540 1443255 := bstep (se 1 (by rfl) ⟨1082441, by rfl⟩ : syracuseStep 1443255 = 2164883) B2164883
theorem B1443275 : Blo 1441540 1443275 := bstep (se 1 (by rfl) ⟨1082456, by rfl⟩ : syracuseStep 1443275 = 2164913) B2164913
theorem B1443287 : Blo 1441540 1443287 := bstep (se 1 (by rfl) ⟨1082465, by rfl⟩ : syracuseStep 1443287 = 2164931) B2164931
theorem B25322969 : Blo 1441540 25322969 := bstep (se 2 (by rfl) ⟨9496113, by rfl⟩ : syracuseStep 25322969 = 18992227) B18992227
theorem B5473757 : Blo 1441540 5473757 := bstep (se 3 (by rfl) ⟨1026329, by rfl⟩ : syracuseStep 5473757 = 2052659) B2052659
theorem B1443307 : Blo 1441540 1443307 := bstep (se 1 (by rfl) ⟨1082480, by rfl⟩ : syracuseStep 1443307 = 2164961) B2164961
theorem B1443319 : Blo 1441540 1443319 := bstep (se 1 (by rfl) ⟨1082489, by rfl⟩ : syracuseStep 1443319 = 2164979) B2164979
theorem B3245579 : Blo 1441540 3245579 := bstep (se 1 (by rfl) ⟨2434184, by rfl⟩ : syracuseStep 3245579 = 4868369) B4868369
theorem B2164235 : Blo 1441540 2164235 := bstep (se 1 (by rfl) ⟨1623176, by rfl⟩ : syracuseStep 2164235 = 3246353) B3246353
theorem B31180301 : Blo 1441540 31180301 := bstep (se 3 (by rfl) ⟨5846306, by rfl⟩ : syracuseStep 31180301 = 11692613) B11692613
theorem B1443339 : Blo 1441540 1443339 := bstep (se 1 (by rfl) ⟨1082504, by rfl⟩ : syracuseStep 1443339 = 2165009) B2165009
theorem B2434583 : Blo 1441540 2434583 := bstep (se 1 (by rfl) ⟨1825937, by rfl⟩ : syracuseStep 2434583 = 3651875) B3651875
theorem B2164247 : Blo 1441540 2164247 := bstep (se 1 (by rfl) ⟨1623185, by rfl⟩ : syracuseStep 2164247 = 3246371) B3246371
theorem B1443351 : Blo 1441540 1443351 := bstep (se 1 (by rfl) ⟨1082513, by rfl⟩ : syracuseStep 1443351 = 2165027) B2165027
theorem B1623595 : Blo 1441540 1623595 := bstep (se 1 (by rfl) ⟨1217696, by rfl⟩ : syracuseStep 1623595 = 2435393) B2435393
theorem B1443371 : Blo 1441540 1443371 := bstep (se 1 (by rfl) ⟨1082528, by rfl⟩ : syracuseStep 1443371 = 2165057) B2165057
theorem B1443383 : Blo 1441540 1443383 := bstep (se 1 (by rfl) ⟨1082537, by rfl⟩ : syracuseStep 1443383 = 2165075) B2165075
theorem B2737729 : Blo 1441540 2737729 := bstep (se 2 (by rfl) ⟨1026648, by rfl⟩ : syracuseStep 2737729 = 2053297) B2053297
theorem B3245633 : Blo 1441540 3245633 := bstep (se 2 (by rfl) ⟨1217112, by rfl⟩ : syracuseStep 3245633 = 2434225) B2434225
theorem B1443403 : Blo 1441540 1443403 := bstep (se 1 (by rfl) ⟨1082552, by rfl⟩ : syracuseStep 1443403 = 2165105) B2165105
theorem B2164313 : Blo 1441540 2164313 := bstep (se 2 (by rfl) ⟨811617, by rfl⟩ : syracuseStep 2164313 = 1623235) B1623235
theorem B3081817 : Blo 1441540 3081817 := bstep (se 2 (by rfl) ⟨1155681, by rfl⟩ : syracuseStep 3081817 = 2311363) B2311363
theorem B1443415 : Blo 1441540 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B1443435 : Blo 1441540 1443435 := bstep (se 1 (by rfl) ⟨1082576, by rfl⟩ : syracuseStep 1443435 = 2165153) B2165153
theorem B1443447 : Blo 1441540 1443447 := bstep (se 1 (by rfl) ⟨1082585, by rfl⟩ : syracuseStep 1443447 = 2165171) B2165171
theorem B1443467 : Blo 1441540 1443467 := bstep (se 1 (by rfl) ⟨1082600, by rfl⟩ : syracuseStep 1443467 = 2165201) B2165201
theorem B2434711 : Blo 1441540 2434711 := bstep (se 1 (by rfl) ⟨1826033, by rfl⟩ : syracuseStep 2434711 = 3652067) B3652067
theorem B1623703 : Blo 1441540 1623703 := bstep (se 1 (by rfl) ⟨1217777, by rfl⟩ : syracuseStep 1623703 = 2435555) B2435555
theorem B1443479 : Blo 1441540 1443479 := bstep (se 1 (by rfl) ⟨1082609, by rfl⟩ : syracuseStep 1443479 = 2165219) B2165219
theorem B1443499 : Blo 1441540 1443499 := bstep (se 1 (by rfl) ⟨1082624, by rfl⟩ : syracuseStep 1443499 = 2165249) B2165249
theorem B1443511 : Blo 1441540 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B2164427 : Blo 1441540 2164427 := bstep (se 1 (by rfl) ⟨1623320, by rfl⟩ : syracuseStep 2164427 = 3246641) B3246641
theorem B1443531 : Blo 1441540 1443531 := bstep (se 1 (by rfl) ⟨1082648, by rfl⟩ : syracuseStep 1443531 = 2165297) B2165297
theorem B2164439 : Blo 1441540 2164439 := bstep (se 1 (by rfl) ⟨1623329, by rfl⟩ : syracuseStep 2164439 = 3246659) B3246659
theorem B2311895 : Blo 1441540 2311895 := bstep (se 1 (by rfl) ⟨1733921, by rfl⟩ : syracuseStep 2311895 = 3467843) B3467843
theorem B27723505 : Blo 1441540 27723505 := bstep (se 2 (by rfl) ⟨10396314, by rfl⟩ : syracuseStep 27723505 = 20792629) B20792629
theorem B3245849 : Blo 1441540 3245849 := bstep (se 2 (by rfl) ⟨1217193, by rfl⟩ : syracuseStep 3245849 = 2434387) B2434387
theorem B2164505 : Blo 1441540 2164505 := bstep (se 2 (by rfl) ⟨811689, by rfl⟩ : syracuseStep 2164505 = 1623379) B1623379
theorem B3901259 : Blo 1441540 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B1623883 : Blo 1441540 1623883 := bstep (se 1 (by rfl) ⟨1217912, by rfl⟩ : syracuseStep 1623883 = 2435825) B2435825
theorem B3245939 : Blo 1441540 3245939 := bstep (se 1 (by rfl) ⟨2434454, by rfl⟩ : syracuseStep 3245939 = 4868909) B4868909
theorem B2164619 : Blo 1441540 2164619 := bstep (se 1 (by rfl) ⟨1623464, by rfl⟩ : syracuseStep 2164619 = 3246929) B3246929
theorem B7301015 : Blo 1441540 7301015 := bstep (se 1 (by rfl) ⟨5475761, by rfl⟩ : syracuseStep 7301015 = 10951523) B10951523
theorem B4867991 : Blo 1441540 4867991 := bstep (se 1 (by rfl) ⟨3650993, by rfl⟩ : syracuseStep 4867991 = 7301987) B7301987
theorem B3245975 : Blo 1441540 3245975 := bstep (se 1 (by rfl) ⟨2434481, by rfl⟩ : syracuseStep 3245975 = 4868963) B4868963
theorem B2164631 : Blo 1441540 2164631 := bstep (se 1 (by rfl) ⟨1623473, by rfl⟩ : syracuseStep 2164631 = 3246947) B3246947
theorem B8775641 : Blo 1441540 8775641 := bstep (se 2 (by rfl) ⟨3290865, by rfl⟩ : syracuseStep 8775641 = 6581731) B6581731
theorem B2164697 : Blo 1441540 2164697 := bstep (se 2 (by rfl) ⟨811761, by rfl⟩ : syracuseStep 2164697 = 1623523) B1623523
theorem B11692097 : Blo 1441540 11692097 := bstep (se 2 (by rfl) ⟨4384536, by rfl⟩ : syracuseStep 11692097 = 8769073) B8769073
theorem B3246155 : Blo 1441540 3246155 := bstep (se 1 (by rfl) ⟨2434616, by rfl⟩ : syracuseStep 3246155 = 4869233) B4869233
theorem B2164811 : Blo 1441540 2164811 := bstep (se 1 (by rfl) ⟨1623608, by rfl⟩ : syracuseStep 2164811 = 3247217) B3247217
theorem B2164823 : Blo 1441540 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B3246209 : Blo 1441540 3246209 := bstep (se 2 (by rfl) ⟨1217328, by rfl⟩ : syracuseStep 3246209 = 2434657) B2434657
theorem B2164889 : Blo 1441540 2164889 := bstep (se 2 (by rfl) ⟨811833, by rfl⟩ : syracuseStep 2164889 = 1623667) B1623667
theorem B2738443 : Blo 1441540 2738443 := bstep (se 1 (by rfl) ⟨2053832, by rfl⟩ : syracuseStep 2738443 = 4107665) B4107665
theorem B2435339 : Blo 1441540 2435339 := bstep (se 1 (by rfl) ⟨1826504, by rfl⟩ : syracuseStep 2435339 = 3653009) B3653009
theorem B2165003 : Blo 1441540 2165003 := bstep (se 1 (by rfl) ⟨1623752, by rfl⟩ : syracuseStep 2165003 = 3247505) B3247505
theorem B2165015 : Blo 1441540 2165015 := bstep (se 1 (by rfl) ⟨1623761, by rfl⟩ : syracuseStep 2165015 = 3247523) B3247523
theorem B2738519 : Blo 1441540 2738519 := bstep (se 1 (by rfl) ⟨2053889, by rfl⟩ : syracuseStep 2738519 = 4107779) B4107779
theorem B3246425 : Blo 1441540 3246425 := bstep (se 2 (by rfl) ⟨1217409, by rfl⟩ : syracuseStep 3246425 = 2434819) B2434819
theorem B2165081 : Blo 1441540 2165081 := bstep (se 2 (by rfl) ⟨811905, by rfl⟩ : syracuseStep 2165081 = 1623811) B1623811
theorem B2435467 : Blo 1441540 2435467 := bstep (se 1 (by rfl) ⟨1826600, by rfl⟩ : syracuseStep 2435467 = 3653201) B3653201
theorem B4868531 : Blo 1441540 4868531 := bstep (se 1 (by rfl) ⟨3651398, by rfl⟩ : syracuseStep 4868531 = 7302797) B7302797
theorem B3246515 : Blo 1441540 3246515 := bstep (se 1 (by rfl) ⟨2434886, by rfl⟩ : syracuseStep 3246515 = 4869773) B4869773
theorem B6580673 : Blo 1441540 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B2165195 : Blo 1441540 2165195 := bstep (se 1 (by rfl) ⟨1623896, by rfl⟩ : syracuseStep 2165195 = 3247793) B3247793
theorem B3246551 : Blo 1441540 3246551 := bstep (se 1 (by rfl) ⟨2434913, by rfl⟩ : syracuseStep 3246551 = 4869827) B4869827
theorem B2165207 : Blo 1441540 2165207 := bstep (se 1 (by rfl) ⟨1623905, by rfl⟩ : syracuseStep 2165207 = 3247811) B3247811
theorem B2435609 : Blo 1441540 2435609 := bstep (se 2 (by rfl) ⟨913353, by rfl⟩ : syracuseStep 2435609 = 1826707) B1826707
theorem B2165273 : Blo 1441540 2165273 := bstep (se 2 (by rfl) ⟨811977, by rfl⟩ : syracuseStep 2165273 = 1623955) B1623955
theorem B24660611 : Blo 1441540 24660611 := bstep (se 1 (by rfl) ⟨18495458, by rfl⟩ : syracuseStep 24660611 = 36990917) B36990917
theorem B3246731 : Blo 1441540 3246731 := bstep (se 1 (by rfl) ⟨2435048, by rfl⟩ : syracuseStep 3246731 = 4870097) B4870097
theorem B2435737 : Blo 1441540 2435737 := bstep (se 2 (by rfl) ⟨913401, by rfl⟩ : syracuseStep 2435737 = 1826803) B1826803
theorem B4868801 : Blo 1441540 4868801 := bstep (se 2 (by rfl) ⟨1825800, by rfl⟩ : syracuseStep 4868801 = 3651601) B3651601
theorem B3246785 : Blo 1441540 3246785 := bstep (se 2 (by rfl) ⟨1217544, by rfl⟩ : syracuseStep 3246785 = 2435089) B2435089
theorem B6007517 : Blo 1441540 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B16436033 : Blo 1441540 16436033 := bstep (se 2 (by rfl) ⟨6163512, by rfl⟩ : syracuseStep 16436033 = 12327025) B12327025
theorem B5196689 : Blo 1441540 5196689 := bstep (se 2 (by rfl) ⟨1948758, by rfl⟩ : syracuseStep 5196689 = 3897517) B3897517
theorem B3247001 : Blo 1441540 3247001 := bstep (se 2 (by rfl) ⟨1217625, by rfl⟩ : syracuseStep 3247001 = 2435251) B2435251
theorem B2739187 : Blo 1441540 2739187 := bstep (se 1 (by rfl) ⟨2054390, by rfl⟩ : syracuseStep 2739187 = 4108781) B4108781
theorem B3247091 : Blo 1441540 3247091 := bstep (se 1 (by rfl) ⟨2435318, by rfl⟩ : syracuseStep 3247091 = 4870637) B4870637
theorem B3247127 : Blo 1441540 3247127 := bstep (se 1 (by rfl) ⟨2435345, by rfl⟩ : syracuseStep 3247127 = 4870691) B4870691
theorem B35105861 : Blo 1441540 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B5196889 : Blo 1441540 5196889 := bstep (se 2 (by rfl) ⟨1948833, by rfl⟩ : syracuseStep 5196889 = 3897667) B3897667
theorem B3951767 : Blo 1441540 3951767 := bstep (se 1 (by rfl) ⟨2963825, by rfl⟩ : syracuseStep 3951767 = 5927651) B5927651
theorem B3247307 : Blo 1441540 3247307 := bstep (se 1 (by rfl) ⟨2435480, by rfl⟩ : syracuseStep 3247307 = 4870961) B4870961
theorem B2739415 : Blo 1441540 2739415 := bstep (se 1 (by rfl) ⟨2054561, by rfl⟩ : syracuseStep 2739415 = 4109123) B4109123
theorem B4869341 : Blo 1441540 4869341 := bstep (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) B1826003
theorem B3247361 : Blo 1441540 3247361 := bstep (se 2 (by rfl) ⟨1217760, by rfl⟩ : syracuseStep 3247361 = 2435521) B2435521
theorem B2739521 : Blo 1441540 2739521 := bstep (se 2 (by rfl) ⟨1027320, by rfl⟩ : syracuseStep 2739521 = 2054641) B2054641
theorem B2739673 : Blo 1441540 2739673 := bstep (se 2 (by rfl) ⟨1027377, by rfl⟩ : syracuseStep 2739673 = 2054755) B2054755
theorem B3247577 : Blo 1441540 3247577 := bstep (se 2 (by rfl) ⟨1217841, by rfl⟩ : syracuseStep 3247577 = 2435683) B2435683
theorem B13168133 : Blo 1441540 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B3247667 : Blo 1441540 3247667 := bstep (se 1 (by rfl) ⟨2435750, by rfl⟩ : syracuseStep 3247667 = 4871501) B4871501
theorem B3247703 : Blo 1441540 3247703 := bstep (se 1 (by rfl) ⟨2435777, by rfl⟩ : syracuseStep 3247703 = 4871555) B4871555
theorem B13160029 : Blo 1441540 13160029 := bstep (se 3 (by rfl) ⟨2467505, by rfl⟩ : syracuseStep 13160029 = 4935011) B4935011
theorem B6246067 : Blo 1441540 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B2600651 : Blo 1441540 2600651 := bstep (se 1 (by rfl) ⟨1950488, by rfl⟩ : syracuseStep 2600651 = 3900977) B3900977
theorem B3247883 : Blo 1441540 3247883 := bstep (se 1 (by rfl) ⟨2435912, by rfl⟩ : syracuseStep 3247883 = 4871825) B4871825
theorem B4108097 : Blo 1441540 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B8777537 : Blo 1441540 8777537 := bstep (se 2 (by rfl) ⟨3291576, by rfl⟩ : syracuseStep 8777537 = 6583153) B6583153
theorem B3247937 : Blo 1441540 3247937 := bstep (se 2 (by rfl) ⟨1217976, by rfl⟩ : syracuseStep 3247937 = 2435953) B2435953
theorem B4108121 : Blo 1441540 4108121 := bstep (se 2 (by rfl) ⟨1540545, by rfl⟩ : syracuseStep 4108121 = 3081091) B3081091
theorem B4386653 : Blo 1441540 4386653 := bstep (se 3 (by rfl) ⟨822497, by rfl⟩ : syracuseStep 4386653 = 1644995) B1644995
theorem B6164369 : Blo 1441540 6164369 := bstep (se 2 (by rfl) ⟨2311638, by rfl⟩ : syracuseStep 6164369 = 4623277) B4623277
theorem B5476355 : Blo 1441540 5476355 := bstep (se 1 (by rfl) ⟨4107266, by rfl⟩ : syracuseStep 5476355 = 8214533) B8214533
theorem B5476369 : Blo 1441540 5476369 := bstep (se 2 (by rfl) ⟨2053638, by rfl⟩ : syracuseStep 5476369 = 4107277) B4107277
theorem B9998411 : Blo 1441540 9998411 := bstep (se 1 (by rfl) ⟨7498808, by rfl⟩ : syracuseStep 9998411 = 14997617) B14997617
theorem B10400005 : Blo 1441540 10400005 := bstep (se 4 (by rfl) ⟨975000, by rfl⟩ : syracuseStep 10400005 = 1950001) B1950001
theorem B6582551 : Blo 1441540 6582551 := bstep (se 1 (by rfl) ⟨4936913, by rfl⟩ : syracuseStep 6582551 = 9873827) B9873827
theorem B5476673 : Blo 1441540 5476673 := bstep (se 2 (by rfl) ⟨2053752, by rfl⟩ : syracuseStep 5476673 = 4107505) B4107505
theorem B4870475 : Blo 1441540 4870475 := bstep (se 1 (by rfl) ⟨3652856, by rfl⟩ : syracuseStep 4870475 = 7305713) B7305713
theorem B8327555 : Blo 1441540 8327555 := bstep (se 1 (by rfl) ⟨6245666, by rfl⟩ : syracuseStep 8327555 = 12491333) B12491333
theorem B13332887 : Blo 1441540 13332887 := bstep (se 1 (by rfl) ⟨9999665, by rfl⟩ : syracuseStep 13332887 = 19999331) B19999331
theorem B2052631 : Blo 1441540 2052631 := bstep (se 1 (by rfl) ⟨1539473, by rfl⟩ : syracuseStep 2052631 = 3078947) B3078947
theorem B3650123 : Blo 1441540 3650123 := bstep (se 1 (by rfl) ⟨2737592, by rfl⟩ : syracuseStep 3650123 = 5475185) B5475185
theorem B4870745 : Blo 1441540 4870745 := bstep (se 2 (by rfl) ⟨1826529, by rfl⟩ : syracuseStep 4870745 = 3653059) B3653059
theorem B6165085 : Blo 1441540 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B7795379 : Blo 1441540 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B3289817 : Blo 1441540 3289817 := bstep (se 2 (by rfl) ⟨1233681, by rfl⟩ : syracuseStep 3289817 = 2467363) B2467363
theorem B1561483 : Blo 1441540 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B1463179 : Blo 1441540 1463179 := bstep (se 1 (by rfl) ⟨1097384, by rfl⟩ : syracuseStep 1463179 = 2194769) B2194769
theorem B5477341 : Blo 1441540 5477341 := bstep (se 3 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 5477341 = 2054003) B2054003
theorem B10957841 : Blo 1441540 10957841 := bstep (se 2 (by rfl) ⟨4109190, by rfl⟩ : syracuseStep 10957841 = 8218381) B8218381
theorem B4109363 : Blo 1441540 4109363 := bstep (se 1 (by rfl) ⟨3082022, by rfl⟩ : syracuseStep 4109363 = 6164045) B6164045
theorem B13866059 : Blo 1441540 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B1733719 : Blo 1441540 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B6935645 : Blo 1441540 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B4871447 : Blo 1441540 4871447 := bstep (se 1 (by rfl) ⟨3653585, by rfl⟩ : syracuseStep 4871447 = 7307171) B7307171
theorem B33314093 : Blo 1441540 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B8213825 : Blo 1441540 8213825 := bstep (se 2 (by rfl) ⟨3080184, by rfl⟩ : syracuseStep 8213825 = 6160369) B6160369
theorem B2053451 : Blo 1441540 2053451 := bstep (se 1 (by rfl) ⟨1540088, by rfl⟩ : syracuseStep 2053451 = 3080177) B3080177
theorem B9876811 : Blo 1441540 9876811 := bstep (se 1 (by rfl) ⟨7407608, by rfl⟩ : syracuseStep 9876811 = 14815217) B14815217
theorem B7304579 : Blo 1441540 7304579 := bstep (se 1 (by rfl) ⟨5478434, by rfl⟩ : syracuseStep 7304579 = 10956869) B10956869
theorem B10950065 : Blo 1441540 10950065 := bstep (se 2 (by rfl) ⟨4106274, by rfl⟩ : syracuseStep 10950065 = 8212549) B8212549
theorem B5846489 : Blo 1441540 5846489 := bstep (se 2 (by rfl) ⟨2192433, by rfl⟩ : syracuseStep 5846489 = 4384867) B4384867
theorem B3651095 : Blo 1441540 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B6158045 : Blo 1441540 6158045 := bstep (se 3 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 6158045 = 2309267) B2309267
theorem B18478853 : Blo 1441540 18478853 := bstep (se 4 (by rfl) ⟨1732392, by rfl⟩ : syracuseStep 18478853 = 3464785) B3464785
theorem B1824535 : Blo 1441540 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B24647489 : Blo 1441540 24647489 := bstep (se 2 (by rfl) ⟨9242808, by rfl⟩ : syracuseStep 24647489 = 18485617) B18485617
theorem B10950551 : Blo 1441540 10950551 := bstep (se 1 (by rfl) ⟨8212913, by rfl⟩ : syracuseStep 10950551 = 16425827) B16425827
theorem B5847005 : Blo 1441540 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B5199889 : Blo 1441540 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B3897409 : Blo 1441540 3897409 := bstep (se 2 (by rfl) ⟨1461528, by rfl⟩ : syracuseStep 3897409 = 2923057) B2923057
theorem B5199947 : Blo 1441540 5199947 := bstep (se 1 (by rfl) ⟨3899960, by rfl⟩ : syracuseStep 5199947 = 7799921) B7799921
theorem B3291211 : Blo 1441540 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B3651763 : Blo 1441540 3651763 := bstep (se 1 (by rfl) ⟨2738822, by rfl⟩ : syracuseStep 3651763 = 5477645) B5477645
theorem B5478617 : Blo 1441540 5478617 := bstep (se 2 (by rfl) ⟨2054481, by rfl⟩ : syracuseStep 5478617 = 4108963) B4108963
theorem B13162769 : Blo 1441540 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B2054425 : Blo 1441540 2054425 := bstep (se 2 (by rfl) ⟨770409, by rfl⟩ : syracuseStep 2054425 = 1540819) B1540819
theorem B3651905 : Blo 1441540 3651905 := bstep (se 2 (by rfl) ⟨1369464, by rfl⟩ : syracuseStep 3651905 = 2738929) B2738929
theorem B6576515 : Blo 1441540 6576515 := bstep (se 1 (by rfl) ⟨4932386, by rfl⟩ : syracuseStep 6576515 = 9864773) B9864773
theorem B12327299 : Blo 1441540 12327299 := bstep (se 1 (by rfl) ⟨9245474, by rfl⟩ : syracuseStep 12327299 = 18490949) B18490949
theorem B11098547 : Blo 1441540 11098547 := bstep (se 1 (by rfl) ⟨8323910, by rfl⟩ : syracuseStep 11098547 = 16647821) B16647821
theorem B1825355 : Blo 1441540 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B3250817 : Blo 1441540 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B10394243 : Blo 1441540 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B3291905 : Blo 1441540 3291905 := bstep (se 2 (by rfl) ⟨1234464, by rfl⟩ : syracuseStep 3291905 = 2468929) B2468929
theorem B3079091 : Blo 1441540 3079091 := bstep (se 1 (by rfl) ⟨2309318, by rfl⟩ : syracuseStep 3079091 = 4618637) B4618637
theorem B1645579 : Blo 1441540 1645579 := bstep (se 1 (by rfl) ⟨1234184, by rfl⟩ : syracuseStep 1645579 = 2468369) B2468369
theorem B70139141 : Blo 1441540 70139141 := bstep (se 4 (by rfl) ⟨6575544, by rfl⟩ : syracuseStep 70139141 = 13151089) B13151089
theorem B1826059 : Blo 1441540 1826059 := bstep (se 1 (by rfl) ⟨1369544, by rfl⟩ : syracuseStep 1826059 = 2739089) B2739089
theorem B4865345 : Blo 1441540 4865345 := bstep (se 2 (by rfl) ⟨1824504, by rfl⟩ : syracuseStep 4865345 = 3649009) B3649009
theorem B9239939 : Blo 1441540 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B16424369 : Blo 1441540 16424369 := bstep (se 2 (by rfl) ⟨6159138, by rfl⟩ : syracuseStep 16424369 = 12318277) B12318277
theorem B12320261 : Blo 1441540 12320261 := bstep (se 4 (by rfl) ⟨1155024, by rfl⟩ : syracuseStep 12320261 = 2310049) B2310049
theorem B1826327 : Blo 1441540 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B3243545 : Blo 1441540 3243545 := bstep (se 2 (by rfl) ⟨1216329, by rfl⟩ : syracuseStep 3243545 = 2432659) B2432659
theorem B3653171 : Blo 1441540 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B6929995 : Blo 1441540 6929995 := bstep (se 1 (by rfl) ⟨5197496, by rfl⟩ : syracuseStep 6929995 = 10394993) B10394993
theorem B18497099 : Blo 1441540 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B3243635 : Blo 1441540 3243635 := bstep (se 1 (by rfl) ⟨2432726, by rfl⟩ : syracuseStep 3243635 = 4865453) B4865453
theorem B2162315 : Blo 1441540 2162315 := bstep (se 1 (by rfl) ⟨1621736, by rfl⟩ : syracuseStep 2162315 = 3243473) B3243473
theorem B1851019 : Blo 1441540 1851019 := bstep (se 1 (by rfl) ⟨1388264, by rfl⟩ : syracuseStep 1851019 = 2776529) B2776529
theorem B2162327 : Blo 1441540 2162327 := bstep (se 1 (by rfl) ⟨1621745, by rfl⟩ : syracuseStep 2162327 = 3243491) B3243491
theorem B3243671 : Blo 1441540 3243671 := bstep (se 1 (by rfl) ⟨2432753, by rfl⟩ : syracuseStep 3243671 = 4865507) B4865507
theorem B2162393 : Blo 1441540 2162393 := bstep (se 2 (by rfl) ⟨810897, by rfl⟩ : syracuseStep 2162393 = 1621795) B1621795
theorem B1441547 : Blo 1441540 1441547 := bstep (se 1 (by rfl) ⟨1081160, by rfl⟩ : syracuseStep 1441547 = 2162321) B2162321
theorem B1441559 : Blo 1441540 1441559 := bstep (se 1 (by rfl) ⟨1081169, by rfl⟩ : syracuseStep 1441559 = 2162339) B2162339
theorem B1441579 : Blo 1441540 1441579 := bstep (se 1 (by rfl) ⟨1081184, by rfl⟩ : syracuseStep 1441579 = 2162369) B2162369
theorem B1441591 : Blo 1441540 1441591 := bstep (se 1 (by rfl) ⟨1081193, by rfl⟩ : syracuseStep 1441591 = 2162387) B2162387
theorem B5480243 : Blo 1441540 5480243 := bstep (se 1 (by rfl) ⟨4110182, by rfl⟩ : syracuseStep 5480243 = 8220365) B8220365
theorem B5480257 : Blo 1441540 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B1441611 : Blo 1441540 1441611 := bstep (se 1 (by rfl) ⟨1081208, by rfl⟩ : syracuseStep 1441611 = 2162417) B2162417
theorem B2162507 : Blo 1441540 2162507 := bstep (se 1 (by rfl) ⟨1621880, by rfl⟩ : syracuseStep 2162507 = 3243761) B3243761
theorem B3243851 : Blo 1441540 3243851 := bstep (se 1 (by rfl) ⟨2432888, by rfl⟩ : syracuseStep 3243851 = 4865777) B4865777
theorem B1441623 : Blo 1441540 1441623 := bstep (se 1 (by rfl) ⟨1081217, by rfl⟩ : syracuseStep 1441623 = 2162435) B2162435
theorem B2162519 : Blo 1441540 2162519 := bstep (se 1 (by rfl) ⟨1621889, by rfl⟩ : syracuseStep 2162519 = 3243779) B3243779
theorem B2432855 : Blo 1441540 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B4865885 : Blo 1441540 4865885 := bstep (se 3 (by rfl) ⟨912353, by rfl⟩ : syracuseStep 4865885 = 1824707) B1824707
theorem B7298909 : Blo 1441540 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1441643 : Blo 1441540 1441643 := bstep (se 1 (by rfl) ⟨1081232, by rfl⟩ : syracuseStep 1441643 = 2162465) B2162465
theorem B1621867 : Blo 1441540 1621867 := bstep (se 1 (by rfl) ⟨1216400, by rfl⟩ : syracuseStep 1621867 = 2432801) B2432801
theorem B1441655 : Blo 1441540 1441655 := bstep (se 1 (by rfl) ⟨1081241, by rfl⟩ : syracuseStep 1441655 = 2162483) B2162483
theorem B3243905 : Blo 1441540 3243905 := bstep (se 2 (by rfl) ⟨1216464, by rfl⟩ : syracuseStep 3243905 = 2432929) B2432929
theorem B1441675 : Blo 1441540 1441675 := bstep (se 1 (by rfl) ⟨1081256, by rfl⟩ : syracuseStep 1441675 = 2162513) B2162513
theorem B1441687 : Blo 1441540 1441687 := bstep (se 1 (by rfl) ⟨1081265, by rfl⟩ : syracuseStep 1441687 = 2162531) B2162531
theorem B2162585 : Blo 1441540 2162585 := bstep (se 2 (by rfl) ⟨810969, by rfl⟩ : syracuseStep 2162585 = 1621939) B1621939
theorem B1441707 : Blo 1441540 1441707 := bstep (se 1 (by rfl) ⟨1081280, by rfl⟩ : syracuseStep 1441707 = 2162561) B2162561
theorem B1441719 : Blo 1441540 1441719 := bstep (se 1 (by rfl) ⟨1081289, by rfl⟩ : syracuseStep 1441719 = 2162579) B2162579
theorem B1441739 : Blo 1441540 1441739 := bstep (se 1 (by rfl) ⟨1081304, by rfl⟩ : syracuseStep 1441739 = 2162609) B2162609
theorem B1441751 : Blo 1441540 1441751 := bstep (se 1 (by rfl) ⟨1081313, by rfl⟩ : syracuseStep 1441751 = 2162627) B2162627
theorem B1621975 : Blo 1441540 1621975 := bstep (se 1 (by rfl) ⟨1216481, by rfl⟩ : syracuseStep 1621975 = 2432963) B2432963
theorem B2432983 : Blo 1441540 2432983 := bstep (se 1 (by rfl) ⟨1824737, by rfl⟩ : syracuseStep 2432983 = 3649475) B3649475
theorem B1441771 : Blo 1441540 1441771 := bstep (se 1 (by rfl) ⟨1081328, by rfl⟩ : syracuseStep 1441771 = 2162657) B2162657
theorem B1441783 : Blo 1441540 1441783 := bstep (se 1 (by rfl) ⟨1081337, by rfl⟩ : syracuseStep 1441783 = 2162675) B2162675
theorem B1441799 : Blo 1441540 1441799 := bstep (se 1 (by rfl) ⟨1081349, by rfl⟩ : syracuseStep 1441799 = 2162699) B2162699
theorem B1441807 : Blo 1441540 1441807 := bstep (se 1 (by rfl) ⟨1081355, by rfl⟩ : syracuseStep 1441807 = 2162711) B2162711
theorem B2162747 : Blo 1441540 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B1441851 : Blo 1441540 1441851 := bstep (se 1 (by rfl) ⟨1081388, by rfl⟩ : syracuseStep 1441851 = 2162777) B2162777
theorem B2162807 : Blo 1441540 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B1441927 : Blo 1441540 1441927 := bstep (se 1 (by rfl) ⟨1081445, by rfl⟩ : syracuseStep 1441927 = 2162891) B2162891
theorem B2162831 : Blo 1441540 2162831 := bstep (se 1 (by rfl) ⟨1622123, by rfl⟩ : syracuseStep 2162831 = 3244247) B3244247
theorem B1441935 : Blo 1441540 1441935 := bstep (se 1 (by rfl) ⟨1081451, by rfl⟩ : syracuseStep 1441935 = 2162903) B2162903
theorem B3080339 : Blo 1441540 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B2162873 : Blo 1441540 2162873 := bstep (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) B1622155
theorem B1441979 : Blo 1441540 1441979 := bstep (se 1 (by rfl) ⟨1081484, by rfl⟩ : syracuseStep 1441979 = 2162969) B2162969
theorem B70213877 : Blo 1441540 70213877 := bstep (se 5 (by rfl) ⟨3291275, by rfl⟩ : syracuseStep 70213877 = 6582551) B6582551
theorem B2162951 : Blo 1441540 2162951 := bstep (se 1 (by rfl) ⟨1622213, by rfl⟩ : syracuseStep 2162951 = 3244427) B3244427
theorem B1442055 : Blo 1441540 1442055 := bstep (se 1 (by rfl) ⟨1081541, by rfl⟩ : syracuseStep 1442055 = 2163083) B2163083
theorem B8888591 : Blo 1441540 8888591 := bstep (se 1 (by rfl) ⟨6666443, by rfl⟩ : syracuseStep 8888591 = 13332887) B13332887
theorem B1442063 : Blo 1441540 1442063 := bstep (se 1 (by rfl) ⟨1081547, by rfl⟩ : syracuseStep 1442063 = 2163095) B2163095
theorem B2162987 : Blo 1441540 2162987 := bstep (se 1 (by rfl) ⟨1622240, by rfl⟩ : syracuseStep 2162987 = 3244481) B3244481
theorem B1442107 : Blo 1441540 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B2163017 : Blo 1441540 2163017 := bstep (se 2 (by rfl) ⟨811131, by rfl⟩ : syracuseStep 2163017 = 1622263) B1622263
theorem B2433415 : Blo 1441540 2433415 := bstep (se 1 (by rfl) ⟨1825061, by rfl⟩ : syracuseStep 2433415 = 3650123) B3650123
theorem B1622407 : Blo 1441540 1622407 := bstep (se 1 (by rfl) ⟨1216805, by rfl⟩ : syracuseStep 1622407 = 2433611) B2433611
theorem B1442183 : Blo 1441540 1442183 := bstep (se 1 (by rfl) ⟨1081637, by rfl⟩ : syracuseStep 1442183 = 2163275) B2163275
theorem B1442191 : Blo 1441540 1442191 := bstep (se 1 (by rfl) ⟨1081643, by rfl⟩ : syracuseStep 1442191 = 2163287) B2163287
theorem B1442235 : Blo 1441540 1442235 := bstep (se 1 (by rfl) ⟨1081676, by rfl⟩ : syracuseStep 1442235 = 2163353) B2163353
theorem B2163131 : Blo 1441540 2163131 := bstep (se 1 (by rfl) ⟨1622348, by rfl⟩ : syracuseStep 2163131 = 3244697) B3244697
theorem B2163191 : Blo 1441540 2163191 := bstep (se 1 (by rfl) ⟨1622393, by rfl⟩ : syracuseStep 2163191 = 3244787) B3244787
theorem B1442311 : Blo 1441540 1442311 := bstep (se 1 (by rfl) ⟨1081733, by rfl⟩ : syracuseStep 1442311 = 2163467) B2163467
theorem B2163215 : Blo 1441540 2163215 := bstep (se 1 (by rfl) ⟨1622411, by rfl⟩ : syracuseStep 2163215 = 3244823) B3244823
theorem B1442319 : Blo 1441540 1442319 := bstep (se 1 (by rfl) ⟨1081739, by rfl⟩ : syracuseStep 1442319 = 2163479) B2163479
theorem B2163257 : Blo 1441540 2163257 := bstep (se 2 (by rfl) ⟨811221, by rfl⟩ : syracuseStep 2163257 = 1622443) B1622443
theorem B1622587 : Blo 1441540 1622587 := bstep (se 1 (by rfl) ⟨1216940, by rfl⟩ : syracuseStep 1622587 = 2433881) B2433881
theorem B1442363 : Blo 1441540 1442363 := bstep (se 1 (by rfl) ⟨1081772, by rfl⟩ : syracuseStep 1442363 = 2163545) B2163545
theorem B14811767 : Blo 1441540 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B3244679 : Blo 1441540 3244679 := bstep (se 1 (by rfl) ⟨2433509, by rfl⟩ : syracuseStep 3244679 = 4867019) B4867019
theorem B2163335 : Blo 1441540 2163335 := bstep (se 1 (by rfl) ⟨1622501, by rfl⟩ : syracuseStep 2163335 = 3245003) B3245003
theorem B1442439 : Blo 1441540 1442439 := bstep (se 1 (by rfl) ⟨1081829, by rfl⟩ : syracuseStep 1442439 = 2163659) B2163659
theorem B1442447 : Blo 1441540 1442447 := bstep (se 1 (by rfl) ⟨1081835, by rfl⟩ : syracuseStep 1442447 = 2163671) B2163671
theorem B2163371 : Blo 1441540 2163371 := bstep (se 1 (by rfl) ⟨1622528, by rfl⟩ : syracuseStep 2163371 = 3245057) B3245057
theorem B1442491 : Blo 1441540 1442491 := bstep (se 1 (by rfl) ⟨1081868, by rfl⟩ : syracuseStep 1442491 = 2163737) B2163737
theorem B7799489 : Blo 1441540 7799489 := bstep (se 2 (by rfl) ⟨2924808, by rfl⟩ : syracuseStep 7799489 = 5849617) B5849617
theorem B2736841 : Blo 1441540 2736841 := bstep (se 2 (by rfl) ⟨1026315, by rfl⟩ : syracuseStep 2736841 = 2052631) B2052631
theorem B2163401 : Blo 1441540 2163401 := bstep (se 2 (by rfl) ⟨811275, by rfl⟩ : syracuseStep 2163401 = 1622551) B1622551
theorem B2924435 : Blo 1441540 2924435 := bstep (se 1 (by rfl) ⟨2193326, by rfl⟩ : syracuseStep 2924435 = 4386653) B4386653
theorem B9872101 : Blo 1441540 9872101 := bstep (se 4 (by rfl) ⟨925509, by rfl⟩ : syracuseStep 9872101 = 1851019) B1851019
theorem B1442567 : Blo 1441540 1442567 := bstep (se 1 (by rfl) ⟨1081925, by rfl⟩ : syracuseStep 1442567 = 2163851) B2163851
theorem B1442575 : Blo 1441540 1442575 := bstep (se 1 (by rfl) ⟨1081931, by rfl⟩ : syracuseStep 1442575 = 2163863) B2163863
theorem B3244859 : Blo 1441540 3244859 := bstep (se 1 (by rfl) ⟨2433644, by rfl⟩ : syracuseStep 3244859 = 4867289) B4867289
theorem B2163515 : Blo 1441540 2163515 := bstep (se 1 (by rfl) ⟨1622636, by rfl⟩ : syracuseStep 2163515 = 3245273) B3245273
theorem B1442619 : Blo 1441540 1442619 := bstep (se 1 (by rfl) ⟨1081964, by rfl⟩ : syracuseStep 1442619 = 2163929) B2163929
theorem B22209395 : Blo 1441540 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B2163575 : Blo 1441540 2163575 := bstep (se 1 (by rfl) ⟨1622681, by rfl⟩ : syracuseStep 2163575 = 3245363) B3245363
theorem B1442695 : Blo 1441540 1442695 := bstep (se 1 (by rfl) ⟨1082021, by rfl⟩ : syracuseStep 1442695 = 2164043) B2164043
theorem B2163599 : Blo 1441540 2163599 := bstep (se 1 (by rfl) ⟨1622699, by rfl⟩ : syracuseStep 2163599 = 3245399) B3245399
theorem B1442703 : Blo 1441540 1442703 := bstep (se 1 (by rfl) ⟨1082027, by rfl⟩ : syracuseStep 1442703 = 2164055) B2164055
theorem B3244985 : Blo 1441540 3244985 := bstep (se 2 (by rfl) ⟨1216869, by rfl⟩ : syracuseStep 3244985 = 2433739) B2433739
theorem B2163641 : Blo 1441540 2163641 := bstep (se 2 (by rfl) ⟨811365, by rfl⟩ : syracuseStep 2163641 = 1622731) B1622731
theorem B1442747 : Blo 1441540 1442747 := bstep (se 1 (by rfl) ⟨1082060, by rfl⟩ : syracuseStep 1442747 = 2164121) B2164121
theorem B7300043 : Blo 1441540 7300043 := bstep (se 1 (by rfl) ⟨5475032, by rfl⟩ : syracuseStep 7300043 = 10950065) B10950065
theorem B2163719 : Blo 1441540 2163719 := bstep (se 1 (by rfl) ⟨1622789, by rfl⟩ : syracuseStep 2163719 = 3245579) B3245579
theorem B1442823 : Blo 1441540 1442823 := bstep (se 1 (by rfl) ⟨1082117, by rfl⟩ : syracuseStep 1442823 = 2164235) B2164235
theorem B2434063 : Blo 1441540 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B1623055 : Blo 1441540 1623055 := bstep (se 1 (by rfl) ⟨1217291, by rfl⟩ : syracuseStep 1623055 = 2434583) B2434583
theorem B1442831 : Blo 1441540 1442831 := bstep (se 1 (by rfl) ⟨1082123, by rfl⟩ : syracuseStep 1442831 = 2164247) B2164247
theorem B3802145 : Blo 1441540 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B2163755 : Blo 1441540 2163755 := bstep (se 1 (by rfl) ⟨1622816, by rfl⟩ : syracuseStep 2163755 = 3245633) B3245633
theorem B1442875 : Blo 1441540 1442875 := bstep (se 1 (by rfl) ⟨1082156, by rfl⟩ : syracuseStep 1442875 = 2164313) B2164313
theorem B2163785 : Blo 1441540 2163785 := bstep (se 2 (by rfl) ⟨811419, by rfl⟩ : syracuseStep 2163785 = 1622839) B1622839
theorem B1442951 : Blo 1441540 1442951 := bstep (se 1 (by rfl) ⟨1082213, by rfl⟩ : syracuseStep 1442951 = 2164427) B2164427
theorem B1442959 : Blo 1441540 1442959 := bstep (se 1 (by rfl) ⟨1082219, by rfl⟩ : syracuseStep 1442959 = 2164439) B2164439
theorem B1541263 : Blo 1441540 1541263 := bstep (se 1 (by rfl) ⟨1155947, by rfl⟩ : syracuseStep 1541263 = 2311895) B2311895
theorem B1950905 : Blo 1441540 1950905 := bstep (se 2 (by rfl) ⟨731589, by rfl⟩ : syracuseStep 1950905 = 1463179) B1463179
theorem B2163899 : Blo 1441540 2163899 := bstep (se 1 (by rfl) ⟨1622924, by rfl⟩ : syracuseStep 2163899 = 3245849) B3245849
theorem B1443003 : Blo 1441540 1443003 := bstep (se 1 (by rfl) ⟨1082252, by rfl⟩ : syracuseStep 1443003 = 2164505) B2164505
theorem B67527917 : Blo 1441540 67527917 := bstep (se 3 (by rfl) ⟨12661484, by rfl⟩ : syracuseStep 67527917 = 25322969) B25322969
theorem B2163959 : Blo 1441540 2163959 := bstep (se 1 (by rfl) ⟨1622969, by rfl⟩ : syracuseStep 2163959 = 3245939) B3245939
theorem B1443079 : Blo 1441540 1443079 := bstep (se 1 (by rfl) ⟨1082309, by rfl⟩ : syracuseStep 1443079 = 2164619) B2164619
theorem B7300367 : Blo 1441540 7300367 := bstep (se 1 (by rfl) ⟨5475275, by rfl⟩ : syracuseStep 7300367 = 10950551) B10950551
theorem B4867343 : Blo 1441540 4867343 := bstep (se 1 (by rfl) ⟨3650507, by rfl⟩ : syracuseStep 4867343 = 7301015) B7301015
theorem B3245327 : Blo 1441540 3245327 := bstep (se 1 (by rfl) ⟨2433995, by rfl⟩ : syracuseStep 3245327 = 4867991) B4867991
theorem B2163983 : Blo 1441540 2163983 := bstep (se 1 (by rfl) ⟨1622987, by rfl⟩ : syracuseStep 2163983 = 3245975) B3245975
theorem B1443087 : Blo 1441540 1443087 := bstep (se 1 (by rfl) ⟨1082315, by rfl⟩ : syracuseStep 1443087 = 2164631) B2164631
theorem B3245345 : Blo 1441540 3245345 := bstep (se 2 (by rfl) ⟨1217004, by rfl⟩ : syracuseStep 3245345 = 2434009) B2434009
theorem B2164025 : Blo 1441540 2164025 := bstep (se 2 (by rfl) ⟨811509, by rfl⟩ : syracuseStep 2164025 = 1623019) B1623019
theorem B5850427 : Blo 1441540 5850427 := bstep (se 1 (by rfl) ⟨4387820, by rfl⟩ : syracuseStep 5850427 = 8775641) B8775641
theorem B1443131 : Blo 1441540 1443131 := bstep (se 1 (by rfl) ⟨1082348, by rfl⟩ : syracuseStep 1443131 = 2164697) B2164697
theorem B2164103 : Blo 1441540 2164103 := bstep (se 1 (by rfl) ⟨1623077, by rfl⟩ : syracuseStep 2164103 = 3246155) B3246155
theorem B3466631 : Blo 1441540 3466631 := bstep (se 1 (by rfl) ⟨2599973, by rfl⟩ : syracuseStep 3466631 = 5199947) B5199947
theorem B1443207 : Blo 1441540 1443207 := bstep (se 1 (by rfl) ⟨1082405, by rfl⟩ : syracuseStep 1443207 = 2164811) B2164811
theorem B1443215 : Blo 1441540 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B2164139 : Blo 1441540 2164139 := bstep (se 1 (by rfl) ⟨1623104, by rfl⟩ : syracuseStep 2164139 = 3246209) B3246209
theorem B1443259 : Blo 1441540 1443259 := bstep (se 1 (by rfl) ⟨1082444, by rfl⟩ : syracuseStep 1443259 = 2164889) B2164889
theorem B2164169 : Blo 1441540 2164169 := bstep (se 2 (by rfl) ⟨811563, by rfl⟩ : syracuseStep 2164169 = 1623127) B1623127
theorem B2311625 : Blo 1441540 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B1623559 : Blo 1441540 1623559 := bstep (se 1 (by rfl) ⟨1217669, by rfl⟩ : syracuseStep 1623559 = 2435339) B2435339
theorem B1443335 : Blo 1441540 1443335 := bstep (se 1 (by rfl) ⟨1082501, by rfl⟩ : syracuseStep 1443335 = 2165003) B2165003
theorem B8775179 : Blo 1441540 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1443343 : Blo 1441540 1443343 := bstep (se 1 (by rfl) ⟨1082507, by rfl⟩ : syracuseStep 1443343 = 2165015) B2165015
theorem B4867613 : Blo 1441540 4867613 := bstep (se 3 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 4867613 = 1825355) B1825355
theorem B2434603 : Blo 1441540 2434603 := bstep (se 1 (by rfl) ⟨1825952, by rfl⟩ : syracuseStep 2434603 = 3651905) B3651905
theorem B2164283 : Blo 1441540 2164283 := bstep (se 1 (by rfl) ⟨1623212, by rfl⟩ : syracuseStep 2164283 = 3246425) B3246425
theorem B1443387 : Blo 1441540 1443387 := bstep (se 1 (by rfl) ⟨1082540, by rfl⟩ : syracuseStep 1443387 = 2165081) B2165081
theorem B4384343 : Blo 1441540 4384343 := bstep (se 1 (by rfl) ⟨3288257, by rfl⟩ : syracuseStep 4384343 = 6576515) B6576515
theorem B8218199 : Blo 1441540 8218199 := bstep (se 1 (by rfl) ⟨6163649, by rfl⟩ : syracuseStep 8218199 = 12327299) B12327299
theorem B7399031 : Blo 1441540 7399031 := bstep (se 1 (by rfl) ⟨5549273, by rfl⟩ : syracuseStep 7399031 = 11098547) B11098547
theorem B3245687 : Blo 1441540 3245687 := bstep (se 1 (by rfl) ⟨2434265, by rfl⟩ : syracuseStep 3245687 = 4868531) B4868531
theorem B2164343 : Blo 1441540 2164343 := bstep (se 1 (by rfl) ⟨1623257, by rfl⟩ : syracuseStep 2164343 = 3246515) B3246515
theorem B1443463 : Blo 1441540 1443463 := bstep (se 1 (by rfl) ⟨1082597, by rfl⟩ : syracuseStep 1443463 = 2165195) B2165195
theorem B2164367 : Blo 1441540 2164367 := bstep (se 1 (by rfl) ⟨1623275, by rfl⟩ : syracuseStep 2164367 = 3246551) B3246551
theorem B1443471 : Blo 1441540 1443471 := bstep (se 1 (by rfl) ⟨1082603, by rfl⟩ : syracuseStep 1443471 = 2165207) B2165207
theorem B2434745 : Blo 1441540 2434745 := bstep (se 2 (by rfl) ⟨913029, by rfl⟩ : syracuseStep 2434745 = 1826059) B1826059
theorem B2164409 : Blo 1441540 2164409 := bstep (se 2 (by rfl) ⟨811653, by rfl⟩ : syracuseStep 2164409 = 1623307) B1623307
theorem B1623739 : Blo 1441540 1623739 := bstep (se 1 (by rfl) ⟨1217804, by rfl⟩ : syracuseStep 1623739 = 2435609) B2435609
theorem B1443515 : Blo 1441540 1443515 := bstep (se 1 (by rfl) ⟨1082636, by rfl⟩ : syracuseStep 1443515 = 2165273) B2165273
theorem B7307819 : Blo 1441540 7307819 := bstep (se 1 (by rfl) ⟨5480864, by rfl⟩ : syracuseStep 7307819 = 10961729) B10961729
theorem B2164487 : Blo 1441540 2164487 := bstep (se 1 (by rfl) ⟨1623365, by rfl⟩ : syracuseStep 2164487 = 3246731) B3246731
theorem B3245867 : Blo 1441540 3245867 := bstep (se 1 (by rfl) ⟨2434400, by rfl⟩ : syracuseStep 3245867 = 4868801) B4868801
theorem B2164523 : Blo 1441540 2164523 := bstep (se 1 (by rfl) ⟨1623392, by rfl⟩ : syracuseStep 2164523 = 3246785) B3246785
theorem B2164553 : Blo 1441540 2164553 := bstep (se 2 (by rfl) ⟨811707, by rfl⟩ : syracuseStep 2164553 = 1623415) B1623415
theorem B2164667 : Blo 1441540 2164667 := bstep (se 1 (by rfl) ⟨1623500, by rfl⟩ : syracuseStep 2164667 = 3247001) B3247001
theorem B2164727 : Blo 1441540 2164727 := bstep (se 1 (by rfl) ⟨1623545, by rfl⟩ : syracuseStep 2164727 = 3247091) B3247091
theorem B2164751 : Blo 1441540 2164751 := bstep (se 1 (by rfl) ⟨1623563, by rfl⟩ : syracuseStep 2164751 = 3247127) B3247127
theorem B2164793 : Blo 1441540 2164793 := bstep (se 2 (by rfl) ⟨811797, by rfl⟩ : syracuseStep 2164793 = 1623595) B1623595
theorem B2164871 : Blo 1441540 2164871 := bstep (se 1 (by rfl) ⟨1623653, by rfl⟩ : syracuseStep 2164871 = 3247307) B3247307
theorem B3246227 : Blo 1441540 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B2164907 : Blo 1441540 2164907 := bstep (se 1 (by rfl) ⟨1623680, by rfl⟩ : syracuseStep 2164907 = 3247361) B3247361
theorem B10954925 : Blo 1441540 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B3246281 : Blo 1441540 3246281 := bstep (se 2 (by rfl) ⟨1217355, by rfl⟩ : syracuseStep 3246281 = 2434711) B2434711
theorem B2164937 : Blo 1441540 2164937 := bstep (se 2 (by rfl) ⟨811851, by rfl⟩ : syracuseStep 2164937 = 1623703) B1623703
theorem B2165051 : Blo 1441540 2165051 := bstep (se 1 (by rfl) ⟨1623788, by rfl⟩ : syracuseStep 2165051 = 3247577) B3247577
theorem B36964673 : Blo 1441540 36964673 := bstep (se 2 (by rfl) ⟨13861752, by rfl⟩ : syracuseStep 36964673 = 27723505) B27723505
theorem B2435447 : Blo 1441540 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B2165111 : Blo 1441540 2165111 := bstep (se 1 (by rfl) ⟨1623833, by rfl⟩ : syracuseStep 2165111 = 3247667) B3247667
theorem B12331399 : Blo 1441540 12331399 := bstep (se 1 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 12331399 = 18497099) B18497099
theorem B2165135 : Blo 1441540 2165135 := bstep (se 1 (by rfl) ⟨1623851, by rfl⟩ : syracuseStep 2165135 = 3247703) B3247703
theorem B2165177 : Blo 1441540 2165177 := bstep (se 2 (by rfl) ⟨811941, by rfl⟩ : syracuseStep 2165177 = 1623883) B1623883
theorem B8210909 : Blo 1441540 8210909 := bstep (se 3 (by rfl) ⟨1539545, by rfl⟩ : syracuseStep 8210909 = 3079091) B3079091
theorem B2165255 : Blo 1441540 2165255 := bstep (se 1 (by rfl) ⟨1623941, by rfl⟩ : syracuseStep 2165255 = 3247883) B3247883
theorem B5851691 : Blo 1441540 5851691 := bstep (se 1 (by rfl) ⟨4388768, by rfl⟩ : syracuseStep 5851691 = 8777537) B8777537
theorem B2165291 : Blo 1441540 2165291 := bstep (se 1 (by rfl) ⟨1623968, by rfl⟩ : syracuseStep 2165291 = 3247937) B3247937
theorem B2738747 : Blo 1441540 2738747 := bstep (se 1 (by rfl) ⟨2054060, by rfl⟩ : syracuseStep 2738747 = 4108121) B4108121
theorem B10947149 : Blo 1441540 10947149 := bstep (se 3 (by rfl) ⟨2052590, by rfl⟩ : syracuseStep 10947149 = 4105181) B4105181
theorem B15592013 : Blo 1441540 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B7301825 : Blo 1441540 7301825 := bstep (se 2 (by rfl) ⟨2738184, by rfl⟩ : syracuseStep 7301825 = 5476369) B5476369
theorem B6933185 : Blo 1441540 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B8776421 : Blo 1441540 8776421 := bstep (se 4 (by rfl) ⟨822789, by rfl⟩ : syracuseStep 8776421 = 1645579) B1645579
theorem B5196545 : Blo 1441540 5196545 := bstep (se 2 (by rfl) ⟨1948704, by rfl⟩ : syracuseStep 5196545 = 3897409) B3897409
theorem B2435899 : Blo 1441540 2435899 := bstep (se 1 (by rfl) ⟨1826924, by rfl⟩ : syracuseStep 2435899 = 3653849) B3653849
theorem B4107095 : Blo 1441540 4107095 := bstep (se 1 (by rfl) ⟨3080321, by rfl⟩ : syracuseStep 4107095 = 6160643) B6160643
theorem B3246983 : Blo 1441540 3246983 := bstep (se 1 (by rfl) ⟨2435237, by rfl⟩ : syracuseStep 3246983 = 4870475) B4870475
theorem B4869017 : Blo 1441540 4869017 := bstep (se 2 (by rfl) ⟨1825881, by rfl⟩ : syracuseStep 4869017 = 3651763) B3651763
theorem B5548985 : Blo 1441540 5548985 := bstep (se 2 (by rfl) ⟨2080869, by rfl⟩ : syracuseStep 5548985 = 4161739) B4161739
theorem B2739233 : Blo 1441540 2739233 := bstep (se 2 (by rfl) ⟨1027212, by rfl⟩ : syracuseStep 2739233 = 2054425) B2054425
theorem B4107323 : Blo 1441540 4107323 := bstep (se 1 (by rfl) ⟨3080492, by rfl⟩ : syracuseStep 4107323 = 6160985) B6160985
theorem B3247163 : Blo 1441540 3247163 := bstep (se 1 (by rfl) ⟨2435372, by rfl⟩ : syracuseStep 3247163 = 4870745) B4870745
theorem B27716741 : Blo 1441540 27716741 := bstep (se 4 (by rfl) ⟨2598444, by rfl⟩ : syracuseStep 27716741 = 5196889) B5196889
theorem B4107449 : Blo 1441540 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B3247289 : Blo 1441540 3247289 := bstep (se 2 (by rfl) ⟨1217733, by rfl⟩ : syracuseStep 3247289 = 2435467) B2435467
theorem B1977529 : Blo 1441540 1977529 := bstep (se 2 (by rfl) ⟨741573, by rfl⟩ : syracuseStep 1977529 = 1483147) B1483147
theorem B2739575 : Blo 1441540 2739575 := bstep (se 1 (by rfl) ⟨2054681, by rfl⟩ : syracuseStep 2739575 = 4109363) B4109363
theorem B9244039 : Blo 1441540 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B4623763 : Blo 1441540 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B8220113 : Blo 1441540 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B3247631 : Blo 1441540 3247631 := bstep (se 1 (by rfl) ⟨2435723, by rfl⟩ : syracuseStep 3247631 = 4871447) B4871447
theorem B5475869 : Blo 1441540 5475869 := bstep (se 3 (by rfl) ⟨1026725, by rfl⟩ : syracuseStep 5475869 = 2053451) B2053451
theorem B3247649 : Blo 1441540 3247649 := bstep (se 2 (by rfl) ⟨1217868, by rfl⟩ : syracuseStep 3247649 = 2435737) B2435737
theorem B5475883 : Blo 1441540 5475883 := bstep (se 1 (by rfl) ⟨4106912, by rfl⟩ : syracuseStep 5475883 = 8213825) B8213825
theorem B4869719 : Blo 1441540 4869719 := bstep (se 1 (by rfl) ⟨3652289, by rfl⟩ : syracuseStep 4869719 = 7304579) B7304579
theorem B3649171 : Blo 1441540 3649171 := bstep (se 1 (by rfl) ⟨2736878, by rfl⟩ : syracuseStep 3649171 = 5473757) B5473757
theorem B20786867 : Blo 1441540 20786867 := bstep (se 1 (by rfl) ⟨15590150, by rfl⟩ : syracuseStep 20786867 = 31180301) B31180301
theorem B3649313 : Blo 1441540 3649313 := bstep (se 2 (by rfl) ⟨1368492, by rfl⟩ : syracuseStep 3649313 = 2736985) B2736985
theorem B2600839 : Blo 1441540 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B7303121 : Blo 1441540 7303121 := bstep (se 2 (by rfl) ⟨2738670, by rfl⟩ : syracuseStep 7303121 = 5477341) B5477341
theorem B7794731 : Blo 1441540 7794731 := bstep (se 1 (by rfl) ⟨5846048, by rfl⟩ : syracuseStep 7794731 = 11692097) B11692097
theorem B4870205 : Blo 1441540 4870205 := bstep (se 3 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 4870205 = 1826327) B1826327
theorem B4387115 : Blo 1441540 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B2167211 : Blo 1441540 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B13169081 : Blo 1441540 13169081 := bstep (se 2 (by rfl) ⟨4938405, by rfl⟩ : syracuseStep 13169081 = 9876811) B9876811
theorem B20787677 : Blo 1441540 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B10957355 : Blo 1441540 10957355 := bstep (se 1 (by rfl) ⟨8218016, by rfl⟩ : syracuseStep 10957355 = 16436033) B16436033
theorem B16421453 : Blo 1441540 16421453 := bstep (se 3 (by rfl) ⟨3079022, by rfl⟩ : syracuseStep 16421453 = 6158045) B6158045
theorem B8778413 : Blo 1441540 8778413 := bstep (se 3 (by rfl) ⟨1645952, by rfl⟩ : syracuseStep 8778413 = 3291905) B3291905
theorem B8327909 : Blo 1441540 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B3650305 : Blo 1441540 3650305 := bstep (se 2 (by rfl) ⟨1368864, by rfl⟩ : syracuseStep 3650305 = 2737729) B2737729
theorem B2634511 : Blo 1441540 2634511 := bstep (se 1 (by rfl) ⟨1975883, by rfl⟩ : syracuseStep 2634511 = 3951767) B3951767
theorem B4109089 : Blo 1441540 4109089 := bstep (se 2 (by rfl) ⟨1540908, by rfl⟩ : syracuseStep 4109089 = 3081817) B3081817
theorem B8328089 : Blo 1441540 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B10949579 : Blo 1441540 10949579 := bstep (se 1 (by rfl) ⟨8212184, by rfl⟩ : syracuseStep 10949579 = 16424369) B16424369
theorem B8213507 : Blo 1441540 8213507 := bstep (se 1 (by rfl) ⟨6160130, by rfl⟩ : syracuseStep 8213507 = 12320261) B12320261
theorem B8778755 : Blo 1441540 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B1733767 : Blo 1441540 1733767 := bstep (se 1 (by rfl) ⟨1300325, by rfl⟩ : syracuseStep 1733767 = 2600651) B2600651
theorem B4109579 : Blo 1441540 4109579 := bstep (se 1 (by rfl) ⟨3082184, by rfl⟩ : syracuseStep 4109579 = 6164369) B6164369
theorem B3650903 : Blo 1441540 3650903 := bstep (se 1 (by rfl) ⟨2738177, by rfl⟩ : syracuseStep 3650903 = 5476355) B5476355
theorem B9491897 : Blo 1441540 9491897 := bstep (se 2 (by rfl) ⟨3559461, by rfl⟩ : syracuseStep 9491897 = 7118923) B7118923
theorem B4871609 : Blo 1441540 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B26662429 : Blo 1441540 26662429 := bstep (se 3 (by rfl) ⟨4999205, by rfl⟩ : syracuseStep 26662429 = 9998411) B9998411
theorem B3651115 : Blo 1441540 3651115 := bstep (se 1 (by rfl) ⟨2738336, by rfl⟩ : syracuseStep 3651115 = 5476673) B5476673
theorem B5551703 : Blo 1441540 5551703 := bstep (se 1 (by rfl) ⟨4163777, by rfl⟩ : syracuseStep 5551703 = 8327555) B8327555
theorem B3651257 : Blo 1441540 3651257 := bstep (se 2 (by rfl) ⟨1369221, by rfl⟩ : syracuseStep 3651257 = 2738443) B2738443
theorem B17553125 : Blo 1441540 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B6928109 : Blo 1441540 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B4937473 : Blo 1441540 4937473 := bstep (se 2 (by rfl) ⟨1851552, by rfl⟩ : syracuseStep 4937473 = 3703105) B3703105
theorem B2193211 : Blo 1441540 2193211 := bstep (se 1 (by rfl) ⟨1644908, by rfl⟩ : syracuseStep 2193211 = 3289817) B3289817
theorem B2054089 : Blo 1441540 2054089 := bstep (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) B1540567
theorem B7305227 : Blo 1441540 7305227 := bstep (se 1 (by rfl) ⟨5478920, by rfl⟩ : syracuseStep 7305227 = 10957841) B10957841
theorem B12490775 : Blo 1441540 12490775 := bstep (se 1 (by rfl) ⟨9368081, by rfl⟩ : syracuseStep 12490775 = 18736163) B18736163
theorem B4110365 : Blo 1441540 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B7305389 : Blo 1441540 7305389 := bstep (se 3 (by rfl) ⟨1369760, by rfl⟩ : syracuseStep 7305389 = 2739521) B2739521
theorem B1825031 : Blo 1441540 1825031 := bstep (se 1 (by rfl) ⟨1368773, by rfl⟩ : syracuseStep 1825031 = 2737547) B2737547
theorem B3897659 : Blo 1441540 3897659 := bstep (se 1 (by rfl) ⟨2923244, by rfl⟩ : syracuseStep 3897659 = 5846489) B5846489
theorem B5200337 : Blo 1441540 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B6928861 : Blo 1441540 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B12319235 : Blo 1441540 12319235 := bstep (se 1 (by rfl) ⟨9239426, by rfl⟩ : syracuseStep 12319235 = 18478853) B18478853
theorem B16431659 : Blo 1441540 16431659 := bstep (se 1 (by rfl) ⟨12323744, by rfl⟩ : syracuseStep 16431659 = 24647489) B24647489
theorem B3652249 : Blo 1441540 3652249 := bstep (se 2 (by rfl) ⟨1369593, by rfl⟩ : syracuseStep 3652249 = 2739187) B2739187
theorem B55466693 : Blo 1441540 55466693 := bstep (se 4 (by rfl) ⟨5200002, by rfl⟩ : syracuseStep 55466693 = 10400005) B10400005
theorem B3652411 : Blo 1441540 3652411 := bstep (se 1 (by rfl) ⟨2739308, by rfl⟩ : syracuseStep 3652411 = 5478617) B5478617
theorem B1825679 : Blo 1441540 1825679 := bstep (se 1 (by rfl) ⟨1369259, by rfl⟩ : syracuseStep 1825679 = 2738519) B2738519
theorem B7297937 : Blo 1441540 7297937 := bstep (se 2 (by rfl) ⟨2736726, by rfl⟩ : syracuseStep 7297937 = 5473453) B5473453
theorem B3652553 : Blo 1441540 3652553 := bstep (se 2 (by rfl) ⟨1369707, by rfl⟩ : syracuseStep 3652553 = 2739415) B2739415
theorem B6929495 : Blo 1441540 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B16440407 : Blo 1441540 16440407 := bstep (se 1 (by rfl) ⟨12330305, by rfl⟩ : syracuseStep 16440407 = 24660611) B24660611
theorem B4005011 : Blo 1441540 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B3464459 : Blo 1441540 3464459 := bstep (se 1 (by rfl) ⟨2598344, by rfl⟩ : syracuseStep 3464459 = 5196689) B5196689
theorem B3652897 : Blo 1441540 3652897 := bstep (se 2 (by rfl) ⟨1369836, by rfl⟩ : syracuseStep 3652897 = 2739673) B2739673
theorem B23403907 : Blo 1441540 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B9239993 : Blo 1441540 9239993 := bstep (se 2 (by rfl) ⟨3464997, by rfl⟩ : syracuseStep 9239993 = 6929995) B6929995
theorem B17546705 : Blo 1441540 17546705 := bstep (se 2 (by rfl) ⟨6580014, by rfl⟩ : syracuseStep 17546705 = 13160029) B13160029
theorem B46759427 : Blo 1441540 46759427 := bstep (se 1 (by rfl) ⟨35069570, by rfl⟩ : syracuseStep 46759427 = 70139141) B70139141
theorem B3243563 : Blo 1441540 3243563 := bstep (se 1 (by rfl) ⟨2432672, by rfl⟩ : syracuseStep 3243563 = 4865345) B4865345
theorem B6159959 : Blo 1441540 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B2162363 : Blo 1441540 2162363 := bstep (se 1 (by rfl) ⟨1621772, by rfl⟩ : syracuseStep 2162363 = 3243545) B3243545
theorem B2432713 : Blo 1441540 2432713 := bstep (se 2 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 2432713 = 1824535) B1824535
theorem B2162423 : Blo 1441540 2162423 := bstep (se 1 (by rfl) ⟨1621817, by rfl⟩ : syracuseStep 2162423 = 3243635) B3243635
theorem B7307009 : Blo 1441540 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B1441543 : Blo 1441540 1441543 := bstep (se 1 (by rfl) ⟨1081157, by rfl⟩ : syracuseStep 1441543 = 2162315) B2162315
theorem B1441551 : Blo 1441540 1441551 := bstep (se 1 (by rfl) ⟨1081163, by rfl⟩ : syracuseStep 1441551 = 2162327) B2162327
theorem B2162447 : Blo 1441540 2162447 := bstep (se 1 (by rfl) ⟨1621835, by rfl⟩ : syracuseStep 2162447 = 3243671) B3243671
theorem B2162489 : Blo 1441540 2162489 := bstep (se 2 (by rfl) ⟨810933, by rfl⟩ : syracuseStep 2162489 = 1621867) B1621867
theorem B1441595 : Blo 1441540 1441595 := bstep (se 1 (by rfl) ⟨1081196, by rfl⟩ : syracuseStep 1441595 = 2162393) B2162393
theorem B3653495 : Blo 1441540 3653495 := bstep (se 1 (by rfl) ⟨2740121, by rfl⟩ : syracuseStep 3653495 = 5480243) B5480243
theorem B1441671 : Blo 1441540 1441671 := bstep (se 1 (by rfl) ⟨1081253, by rfl⟩ : syracuseStep 1441671 = 2162507) B2162507
theorem B2162567 : Blo 1441540 2162567 := bstep (se 1 (by rfl) ⟨1621925, by rfl⟩ : syracuseStep 2162567 = 3243851) B3243851
theorem B1441679 : Blo 1441540 1441679 := bstep (se 1 (by rfl) ⟨1081259, by rfl⟩ : syracuseStep 1441679 = 2162519) B2162519
theorem B1621903 : Blo 1441540 1621903 := bstep (se 1 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 1621903 = 2432855) B2432855
theorem B3243923 : Blo 1441540 3243923 := bstep (se 1 (by rfl) ⟨2432942, by rfl⟩ : syracuseStep 3243923 = 4865885) B4865885
theorem B4865939 : Blo 1441540 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B2162603 : Blo 1441540 2162603 := bstep (se 1 (by rfl) ⟨1621952, by rfl⟩ : syracuseStep 2162603 = 3243905) B3243905
theorem B1441723 : Blo 1441540 1441723 := bstep (se 1 (by rfl) ⟨1081292, by rfl⟩ : syracuseStep 1441723 = 2162585) B2162585
theorem B2162633 : Blo 1441540 2162633 := bstep (se 2 (by rfl) ⟨810987, by rfl⟩ : syracuseStep 2162633 = 1621975) B1621975
theorem B3243977 : Blo 1441540 3243977 := bstep (se 2 (by rfl) ⟨1216491, by rfl⟩ : syracuseStep 3243977 = 2432983) B2432983
theorem B1441831 : Blo 1441540 1441831 := bstep (se 1 (by rfl) ⟨1081373, by rfl⟩ : syracuseStep 1441831 = 2162747) B2162747
theorem B1441871 : Blo 1441540 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B1441887 : Blo 1441540 1441887 := bstep (se 1 (by rfl) ⟨1081415, by rfl⟩ : syracuseStep 1441887 = 2162831) B2162831
theorem B1441915 : Blo 1441540 1441915 := bstep (se 1 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 1441915 = 2162873) B2162873
theorem B46809251 : Blo 1441540 46809251 := bstep (se 1 (by rfl) ⟨35106938, by rfl⟩ : syracuseStep 46809251 = 70213877) B70213877
theorem B1441967 : Blo 1441540 1441967 := bstep (se 1 (by rfl) ⟨1081475, by rfl⟩ : syracuseStep 1441967 = 2162951) B2162951
theorem B1441991 : Blo 1441540 1441991 := bstep (se 1 (by rfl) ⟨1081493, by rfl⟩ : syracuseStep 1441991 = 2162987) B2162987
theorem B2924743 : Blo 1441540 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B1442011 : Blo 1441540 1442011 := bstep (se 1 (by rfl) ⟨1081508, by rfl⟩ : syracuseStep 1442011 = 2163017) B2163017
theorem B1442087 : Blo 1441540 1442087 := bstep (se 1 (by rfl) ⟨1081565, by rfl⟩ : syracuseStep 1442087 = 2163131) B2163131
theorem B1442127 : Blo 1441540 1442127 := bstep (se 1 (by rfl) ⟨1081595, by rfl⟩ : syracuseStep 1442127 = 2163191) B2163191
theorem B1442143 : Blo 1441540 1442143 := bstep (se 1 (by rfl) ⟨1081607, by rfl⟩ : syracuseStep 1442143 = 2163215) B2163215
theorem B1442171 : Blo 1441540 1442171 := bstep (se 1 (by rfl) ⟨1081628, by rfl⟩ : syracuseStep 1442171 = 2163257) B2163257
theorem B2163119 : Blo 1441540 2163119 := bstep (se 1 (by rfl) ⟨1622339, by rfl⟩ : syracuseStep 2163119 = 3244679) B3244679
theorem B1442223 : Blo 1441540 1442223 := bstep (se 1 (by rfl) ⟨1081667, by rfl⟩ : syracuseStep 1442223 = 2163335) B2163335
theorem B1442247 : Blo 1441540 1442247 := bstep (se 1 (by rfl) ⟨1081685, by rfl⟩ : syracuseStep 1442247 = 2163371) B2163371
theorem B1442267 : Blo 1441540 1442267 := bstep (se 1 (by rfl) ⟨1081700, by rfl⟩ : syracuseStep 1442267 = 2163401) B2163401
theorem B5202413 : Blo 1441540 5202413 := bstep (se 3 (by rfl) ⟨975452, by rfl⟩ : syracuseStep 5202413 = 1950905) B1950905
theorem B3244553 : Blo 1441540 3244553 := bstep (se 2 (by rfl) ⟨1216707, by rfl⟩ : syracuseStep 3244553 = 2433415) B2433415
theorem B2163209 : Blo 1441540 2163209 := bstep (se 2 (by rfl) ⟨811203, by rfl⟩ : syracuseStep 2163209 = 1622407) B1622407
theorem B16441865 : Blo 1441540 16441865 := bstep (se 2 (by rfl) ⟨6165699, by rfl⟩ : syracuseStep 16441865 = 12331399) B12331399
theorem B2163239 : Blo 1441540 2163239 := bstep (se 1 (by rfl) ⟨1622429, by rfl⟩ : syracuseStep 2163239 = 3244859) B3244859
theorem B1442343 : Blo 1441540 1442343 := bstep (se 1 (by rfl) ⟨1081757, by rfl⟩ : syracuseStep 1442343 = 2163515) B2163515
theorem B1442383 : Blo 1441540 1442383 := bstep (se 1 (by rfl) ⟨1081787, by rfl⟩ : syracuseStep 1442383 = 2163575) B2163575
theorem B1442399 : Blo 1441540 1442399 := bstep (se 1 (by rfl) ⟨1081799, by rfl⟩ : syracuseStep 1442399 = 2163599) B2163599
theorem B2163323 : Blo 1441540 2163323 := bstep (se 1 (by rfl) ⟨1622492, by rfl⟩ : syracuseStep 2163323 = 3244985) B3244985
theorem B1442427 : Blo 1441540 1442427 := bstep (se 1 (by rfl) ⟨1081820, by rfl⟩ : syracuseStep 1442427 = 2163641) B2163641
theorem B7299719 : Blo 1441540 7299719 := bstep (se 1 (by rfl) ⟨5474789, by rfl⟩ : syracuseStep 7299719 = 10949579) B10949579
theorem B4866695 : Blo 1441540 4866695 := bstep (se 1 (by rfl) ⟨3650021, by rfl⟩ : syracuseStep 4866695 = 7300043) B7300043
theorem B1442479 : Blo 1441540 1442479 := bstep (se 1 (by rfl) ⟨1081859, by rfl⟩ : syracuseStep 1442479 = 2163719) B2163719
theorem B4866749 : Blo 1441540 4866749 := bstep (se 3 (by rfl) ⟨912515, by rfl⟩ : syracuseStep 4866749 = 1825031) B1825031
theorem B1442503 : Blo 1441540 1442503 := bstep (se 1 (by rfl) ⟨1081877, by rfl⟩ : syracuseStep 1442503 = 2163755) B2163755
theorem B1442523 : Blo 1441540 1442523 := bstep (se 1 (by rfl) ⟨1081892, by rfl⟩ : syracuseStep 1442523 = 2163785) B2163785
theorem B2163449 : Blo 1441540 2163449 := bstep (se 2 (by rfl) ⟨811293, by rfl⟩ : syracuseStep 2163449 = 1622587) B1622587
theorem B1442599 : Blo 1441540 1442599 := bstep (se 1 (by rfl) ⟨1081949, by rfl⟩ : syracuseStep 1442599 = 2163899) B2163899
theorem B1442639 : Blo 1441540 1442639 := bstep (se 1 (by rfl) ⟨1081979, by rfl⟩ : syracuseStep 1442639 = 2163959) B2163959
theorem B4866911 : Blo 1441540 4866911 := bstep (se 1 (by rfl) ⟨3650183, by rfl⟩ : syracuseStep 4866911 = 7300367) B7300367
theorem B3244895 : Blo 1441540 3244895 := bstep (se 1 (by rfl) ⟨2433671, by rfl⟩ : syracuseStep 3244895 = 4867343) B4867343
theorem B2163551 : Blo 1441540 2163551 := bstep (se 1 (by rfl) ⟨1622663, by rfl⟩ : syracuseStep 2163551 = 3245327) B3245327
theorem B1442655 : Blo 1441540 1442655 := bstep (se 1 (by rfl) ⟨1081991, by rfl⟩ : syracuseStep 1442655 = 2163983) B2163983
theorem B2163563 : Blo 1441540 2163563 := bstep (se 1 (by rfl) ⟨1622672, by rfl⟩ : syracuseStep 2163563 = 3245345) B3245345
theorem B1442683 : Blo 1441540 1442683 := bstep (se 1 (by rfl) ⟨1082012, by rfl⟩ : syracuseStep 1442683 = 2164025) B2164025
theorem B2433935 : Blo 1441540 2433935 := bstep (se 1 (by rfl) ⟨1825451, by rfl⟩ : syracuseStep 2433935 = 3650903) B3650903
theorem B1442735 : Blo 1441540 1442735 := bstep (se 1 (by rfl) ⟨1082051, by rfl⟩ : syracuseStep 1442735 = 2164103) B2164103
theorem B2311087 : Blo 1441540 2311087 := bstep (se 1 (by rfl) ⟨1733315, by rfl⟩ : syracuseStep 2311087 = 3466631) B3466631
theorem B1442759 : Blo 1441540 1442759 := bstep (se 1 (by rfl) ⟨1082069, by rfl⟩ : syracuseStep 1442759 = 2164139) B2164139
theorem B1442779 : Blo 1441540 1442779 := bstep (se 1 (by rfl) ⟨1082084, by rfl⟩ : syracuseStep 1442779 = 2164169) B2164169
theorem B4867073 : Blo 1441540 4867073 := bstep (se 2 (by rfl) ⟨1825152, by rfl⟩ : syracuseStep 4867073 = 3650305) B3650305
theorem B5850119 : Blo 1441540 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B3245075 : Blo 1441540 3245075 := bstep (se 1 (by rfl) ⟨2433806, by rfl⟩ : syracuseStep 3245075 = 4867613) B4867613
theorem B1442855 : Blo 1441540 1442855 := bstep (se 1 (by rfl) ⟨1082141, by rfl⟩ : syracuseStep 1442855 = 2164283) B2164283
theorem B2163791 : Blo 1441540 2163791 := bstep (se 1 (by rfl) ⟨1622843, by rfl⟩ : syracuseStep 2163791 = 3245687) B3245687
theorem B1442895 : Blo 1441540 1442895 := bstep (se 1 (by rfl) ⟨1082171, by rfl⟩ : syracuseStep 1442895 = 2164343) B2164343
theorem B1442911 : Blo 1441540 1442911 := bstep (se 1 (by rfl) ⟨1082183, by rfl⟩ : syracuseStep 1442911 = 2164367) B2164367
theorem B2434171 : Blo 1441540 2434171 := bstep (se 1 (by rfl) ⟨1825628, by rfl⟩ : syracuseStep 2434171 = 3651257) B3651257
theorem B1623163 : Blo 1441540 1623163 := bstep (se 1 (by rfl) ⟨1217372, by rfl⟩ : syracuseStep 1623163 = 2434745) B2434745
theorem B1442939 : Blo 1441540 1442939 := bstep (se 1 (by rfl) ⟨1082204, by rfl⟩ : syracuseStep 1442939 = 2164409) B2164409
theorem B1442991 : Blo 1441540 1442991 := bstep (se 1 (by rfl) ⟨1082243, by rfl⟩ : syracuseStep 1442991 = 2164487) B2164487
theorem B52651205 : Blo 1441540 52651205 := bstep (se 4 (by rfl) ⟨4936050, by rfl⟩ : syracuseStep 52651205 = 9872101) B9872101
theorem B2163911 : Blo 1441540 2163911 := bstep (se 1 (by rfl) ⟨1622933, by rfl⟩ : syracuseStep 2163911 = 3245867) B3245867
theorem B1443015 : Blo 1441540 1443015 := bstep (se 1 (by rfl) ⟨1082261, by rfl⟩ : syracuseStep 1443015 = 2164523) B2164523
theorem B1443035 : Blo 1441540 1443035 := bstep (se 1 (by rfl) ⟨1082276, by rfl⟩ : syracuseStep 1443035 = 2164553) B2164553
theorem B1443111 : Blo 1441540 1443111 := bstep (se 1 (by rfl) ⟨1082333, by rfl⟩ : syracuseStep 1443111 = 2164667) B2164667
theorem B1443151 : Blo 1441540 1443151 := bstep (se 1 (by rfl) ⟨1082363, by rfl⟩ : syracuseStep 1443151 = 2164727) B2164727
theorem B1443167 : Blo 1441540 1443167 := bstep (se 1 (by rfl) ⟨1082375, by rfl⟩ : syracuseStep 1443167 = 2164751) B2164751
theorem B3245417 : Blo 1441540 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B2164073 : Blo 1441540 2164073 := bstep (se 2 (by rfl) ⟨811527, by rfl⟩ : syracuseStep 2164073 = 1623055) B1623055
theorem B1443195 : Blo 1441540 1443195 := bstep (se 1 (by rfl) ⟨1082396, by rfl⟩ : syracuseStep 1443195 = 2164793) B2164793
theorem B1443247 : Blo 1441540 1443247 := bstep (se 1 (by rfl) ⟨1082435, by rfl⟩ : syracuseStep 1443247 = 2164871) B2164871
theorem B2164151 : Blo 1441540 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B1443271 : Blo 1441540 1443271 := bstep (se 1 (by rfl) ⟨1082453, by rfl⟩ : syracuseStep 1443271 = 2164907) B2164907
theorem B2164187 : Blo 1441540 2164187 := bstep (se 1 (by rfl) ⟨1623140, by rfl⟩ : syracuseStep 2164187 = 3246281) B3246281
theorem B1443291 : Blo 1441540 1443291 := bstep (se 1 (by rfl) ⟨1082468, by rfl⟩ : syracuseStep 1443291 = 2164937) B2164937
theorem B2598439 : Blo 1441540 2598439 := bstep (se 1 (by rfl) ⟨1948829, by rfl⟩ : syracuseStep 2598439 = 3897659) B3897659
theorem B1443367 : Blo 1441540 1443367 := bstep (se 1 (by rfl) ⟨1082525, by rfl⟩ : syracuseStep 1443367 = 2165051) B2165051
theorem B24643115 : Blo 1441540 24643115 := bstep (se 1 (by rfl) ⟨18482336, by rfl⟩ : syracuseStep 24643115 = 36964673) B36964673
theorem B1623631 : Blo 1441540 1623631 := bstep (se 1 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 1623631 = 2435447) B2435447
theorem B1443407 : Blo 1441540 1443407 := bstep (se 1 (by rfl) ⟨1082555, by rfl⟩ : syracuseStep 1443407 = 2165111) B2165111
theorem B1443423 : Blo 1441540 1443423 := bstep (se 1 (by rfl) ⟨1082567, by rfl⟩ : syracuseStep 1443423 = 2165135) B2165135
theorem B1443451 : Blo 1441540 1443451 := bstep (se 1 (by rfl) ⟨1082588, by rfl⟩ : syracuseStep 1443451 = 2165177) B2165177
theorem B3466891 : Blo 1441540 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B5473939 : Blo 1441540 5473939 := bstep (se 1 (by rfl) ⟨4105454, by rfl⟩ : syracuseStep 5473939 = 8210909) B8210909
theorem B1443503 : Blo 1441540 1443503 := bstep (se 1 (by rfl) ⟨1082627, by rfl⟩ : syracuseStep 1443503 = 2165255) B2165255
theorem B10954439 : Blo 1441540 10954439 := bstep (se 1 (by rfl) ⟨8215829, by rfl⟩ : syracuseStep 10954439 = 16431659) B16431659
theorem B3901127 : Blo 1441540 3901127 := bstep (se 1 (by rfl) ⟨2925845, by rfl⟩ : syracuseStep 3901127 = 5851691) B5851691
theorem B1443527 : Blo 1441540 1443527 := bstep (se 1 (by rfl) ⟨1082645, by rfl⟩ : syracuseStep 1443527 = 2165291) B2165291
theorem B7800569 : Blo 1441540 7800569 := bstep (se 2 (by rfl) ⟨2925213, by rfl⟩ : syracuseStep 7800569 = 5850427) B5850427
theorem B4867883 : Blo 1441540 4867883 := bstep (se 1 (by rfl) ⟨3650912, by rfl⟩ : syracuseStep 4867883 = 7301825) B7301825
theorem B4622123 : Blo 1441540 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B5850947 : Blo 1441540 5850947 := bstep (se 1 (by rfl) ⟨4388210, by rfl⟩ : syracuseStep 5850947 = 8776421) B8776421
theorem B31205209 : Blo 1441540 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B2738063 : Blo 1441540 2738063 := bstep (se 1 (by rfl) ⟨2053547, by rfl⟩ : syracuseStep 2738063 = 4107095) B4107095
theorem B2164655 : Blo 1441540 2164655 := bstep (se 1 (by rfl) ⟨1623491, by rfl⟩ : syracuseStep 2164655 = 3246983) B3246983
theorem B3246011 : Blo 1441540 3246011 := bstep (se 1 (by rfl) ⟨2434508, by rfl⟩ : syracuseStep 3246011 = 4869017) B4869017
theorem B2435035 : Blo 1441540 2435035 := bstep (se 1 (by rfl) ⟨1826276, by rfl⟩ : syracuseStep 2435035 = 3652553) B3652553
theorem B2164745 : Blo 1441540 2164745 := bstep (se 2 (by rfl) ⟨811779, by rfl⟩ : syracuseStep 2164745 = 1623559) B1623559
theorem B2738215 : Blo 1441540 2738215 := bstep (se 1 (by rfl) ⟨2053661, by rfl⟩ : syracuseStep 2738215 = 4107323) B4107323
theorem B2164775 : Blo 1441540 2164775 := bstep (se 1 (by rfl) ⟨1623581, by rfl⟩ : syracuseStep 2164775 = 3247163) B3247163
theorem B7301177 : Blo 1441540 7301177 := bstep (se 2 (by rfl) ⟨2737941, by rfl⟩ : syracuseStep 7301177 = 5475883) B5475883
theorem B4868153 : Blo 1441540 4868153 := bstep (se 2 (by rfl) ⟨1825557, by rfl⟩ : syracuseStep 4868153 = 3651115) B3651115
theorem B3246137 : Blo 1441540 3246137 := bstep (se 2 (by rfl) ⟨1217301, by rfl⟩ : syracuseStep 3246137 = 2434603) B2434603
theorem B2738299 : Blo 1441540 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B2164859 : Blo 1441540 2164859 := bstep (se 1 (by rfl) ⟨1623644, by rfl⟩ : syracuseStep 2164859 = 3247289) B3247289
theorem B2164985 : Blo 1441540 2164985 := bstep (se 2 (by rfl) ⟨811869, by rfl⟩ : syracuseStep 2164985 = 1623739) B1623739
theorem B31172951 : Blo 1441540 31172951 := bstep (se 1 (by rfl) ⟨23379713, by rfl⟩ : syracuseStep 31172951 = 46759427) B46759427
theorem B2165087 : Blo 1441540 2165087 := bstep (se 1 (by rfl) ⟨1623815, by rfl⟩ : syracuseStep 2165087 = 3247631) B3247631
theorem B2165099 : Blo 1441540 2165099 := bstep (se 1 (by rfl) ⟨1623824, by rfl⟩ : syracuseStep 2165099 = 3247649) B3247649
theorem B4868477 : Blo 1441540 4868477 := bstep (se 3 (by rfl) ⟨912839, by rfl⟩ : syracuseStep 4868477 = 1825679) B1825679
theorem B4106639 : Blo 1441540 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B3246479 : Blo 1441540 3246479 := bstep (se 1 (by rfl) ⟨2434859, by rfl⟩ : syracuseStep 3246479 = 4869719) B4869719
theorem B3467785 : Blo 1441540 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B2435663 : Blo 1441540 2435663 := bstep (se 1 (by rfl) ⟨1826747, by rfl⟩ : syracuseStep 2435663 = 3653495) B3653495
theorem B2738785 : Blo 1441540 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B4868747 : Blo 1441540 4868747 := bstep (se 1 (by rfl) ⟨3651560, by rfl⟩ : syracuseStep 4868747 = 7303121) B7303121
theorem B5196487 : Blo 1441540 5196487 := bstep (se 1 (by rfl) ⟨3897365, by rfl⟩ : syracuseStep 5196487 = 7794731) B7794731
theorem B3246803 : Blo 1441540 3246803 := bstep (se 1 (by rfl) ⟨2435102, by rfl⟩ : syracuseStep 3246803 = 4870205) B4870205
theorem B142199621 : Blo 1441540 142199621 := bstep (se 4 (by rfl) ⟨13331214, by rfl⟩ : syracuseStep 142199621 = 26662429) B26662429
theorem B5925727 : Blo 1441540 5925727 := bstep (se 1 (by rfl) ⟨4444295, by rfl⟩ : syracuseStep 5925727 = 8888591) B8888591
theorem B1444807 : Blo 1441540 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B10947635 : Blo 1441540 10947635 := bstep (se 1 (by rfl) ⟨8210726, by rfl⟩ : syracuseStep 10947635 = 16421453) B16421453
theorem B9874511 : Blo 1441540 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B5475671 : Blo 1441540 5475671 := bstep (se 1 (by rfl) ⟨4106753, by rfl⟩ : syracuseStep 5475671 = 8213507) B8213507
theorem B5852503 : Blo 1441540 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B45018611 : Blo 1441540 45018611 := bstep (se 1 (by rfl) ⟨33763958, by rfl⟩ : syracuseStep 45018611 = 67527917) B67527917
theorem B2739719 : Blo 1441540 2739719 := bstep (se 1 (by rfl) ⟨2054789, by rfl⟩ : syracuseStep 2739719 = 4109579) B4109579
theorem B4869665 : Blo 1441540 4869665 := bstep (se 2 (by rfl) ⟨1826124, by rfl⟩ : syracuseStep 4869665 = 3652249) B3652249
theorem B3649121 : Blo 1441540 3649121 := bstep (se 2 (by rfl) ⟨1368420, by rfl⟩ : syracuseStep 3649121 = 2736841) B2736841
theorem B6327931 : Blo 1441540 6327931 := bstep (se 1 (by rfl) ⟨4745948, by rfl⟩ : syracuseStep 6327931 = 9491897) B9491897
theorem B3247739 : Blo 1441540 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B4869881 : Blo 1441540 4869881 := bstep (se 2 (by rfl) ⟨1826205, by rfl⟩ : syracuseStep 4869881 = 3652411) B3652411
theorem B3247865 : Blo 1441540 3247865 := bstep (se 2 (by rfl) ⟨1217949, by rfl⟩ : syracuseStep 3247865 = 2435899) B2435899
theorem B11702083 : Blo 1441540 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B6164333 : Blo 1441540 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B236900213 : Blo 1441540 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B26333189 : Blo 1441540 26333189 := bstep (se 4 (by rfl) ⟨2468736, by rfl⟩ : syracuseStep 26333189 = 4937473) B4937473
theorem B4870151 : Blo 1441540 4870151 := bstep (se 1 (by rfl) ⟨3652613, by rfl⟩ : syracuseStep 4870151 = 7305227) B7305227
theorem B8327183 : Blo 1441540 8327183 := bstep (se 1 (by rfl) ⟨6245387, by rfl⟩ : syracuseStep 8327183 = 12490775) B12490775
theorem B2740243 : Blo 1441540 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B7303283 : Blo 1441540 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B4870259 : Blo 1441540 4870259 := bstep (se 1 (by rfl) ⟨3652694, by rfl⟩ : syracuseStep 4870259 = 7305389) B7305389
theorem B19730749 : Blo 1441540 19730749 := bstep (se 3 (by rfl) ⟨3699515, by rfl⟩ : syracuseStep 19730749 = 7399031) B7399031
theorem B8212823 : Blo 1441540 8212823 := bstep (se 1 (by rfl) ⟨6159617, by rfl⟩ : syracuseStep 8212823 = 12319235) B12319235
theorem B4870529 : Blo 1441540 4870529 := bstep (se 2 (by rfl) ⟨1826448, by rfl⟩ : syracuseStep 4870529 = 3652897) B3652897
theorem B23409101 : Blo 1441540 23409101 := bstep (se 3 (by rfl) ⟨4389206, by rfl⟩ : syracuseStep 23409101 = 8778413) B8778413
theorem B12325385 : Blo 1441540 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B6165017 : Blo 1441540 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B3699323 : Blo 1441540 3699323 := bstep (se 1 (by rfl) ⟨2774492, by rfl⟩ : syracuseStep 3699323 = 5548985) B5548985
theorem B18477827 : Blo 1441540 18477827 := bstep (se 1 (by rfl) ⟨13858370, by rfl⟩ : syracuseStep 18477827 = 27716741) B27716741
theorem B3650579 : Blo 1441540 3650579 := bstep (se 1 (by rfl) ⟨2737934, by rfl⟩ : syracuseStep 3650579 = 5475869) B5475869
theorem B13857911 : Blo 1441540 13857911 := bstep (se 1 (by rfl) ⟨10393433, by rfl⟩ : syracuseStep 13857911 = 20786867) B20786867
theorem B4871339 : Blo 1441540 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B10139053 : Blo 1441540 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B2053559 : Blo 1441540 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B13858451 : Blo 1441540 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B7304903 : Blo 1441540 7304903 := bstep (se 1 (by rfl) ⟨5478677, by rfl⟩ : syracuseStep 7304903 = 10957355) B10957355
theorem B4871879 : Blo 1441540 4871879 := bstep (se 1 (by rfl) ⟨3653909, by rfl⟩ : syracuseStep 4871879 = 7307819) B7307819
theorem B5199659 : Blo 1441540 5199659 := bstep (se 1 (by rfl) ⟨3899744, by rfl⟩ : syracuseStep 5199659 = 7799489) B7799489
theorem B5551939 : Blo 1441540 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B5552059 : Blo 1441540 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B9238481 : Blo 1441540 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B9246757 : Blo 1441540 9246757 := bstep (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) B1733767
theorem B3512681 : Blo 1441540 3512681 := bstep (se 2 (by rfl) ⟨1317255, by rfl⟩ : syracuseStep 3512681 = 2634511) B2634511
theorem B5478785 : Blo 1441540 5478785 := bstep (se 2 (by rfl) ⟨2054544, by rfl⟩ : syracuseStep 5478785 = 4109089) B4109089
theorem B2922895 : Blo 1441540 2922895 := bstep (se 1 (by rfl) ⟨2192171, by rfl⟩ : syracuseStep 2922895 = 4384343) B4384343
theorem B3701135 : Blo 1441540 3701135 := bstep (se 1 (by rfl) ⟨2775851, by rfl⟩ : syracuseStep 3701135 = 5551703) B5551703
theorem B5478799 : Blo 1441540 5478799 := bstep (se 1 (by rfl) ⟨4109099, by rfl⟩ : syracuseStep 5478799 = 8218199) B8218199
theorem B35117549 : Blo 1441540 35117549 := bstep (se 3 (by rfl) ⟨6584540, by rfl⟩ : syracuseStep 35117549 = 13169081) B13169081
theorem B4618739 : Blo 1441540 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B2055017 : Blo 1441540 2055017 := bstep (se 2 (by rfl) ⟨770631, by rfl⟩ : syracuseStep 2055017 = 1541263) B1541263
theorem B2636705 : Blo 1441540 2636705 := bstep (se 2 (by rfl) ⟨988764, by rfl⟩ : syracuseStep 2636705 = 1977529) B1977529
theorem B1825831 : Blo 1441540 1825831 := bstep (se 1 (by rfl) ⟨1369373, by rfl⟩ : syracuseStep 1825831 = 2738747) B2738747
theorem B7298099 : Blo 1441540 7298099 := bstep (se 1 (by rfl) ⟨5473574, by rfl⟩ : syracuseStep 7298099 = 10947149) B10947149
theorem B10394675 : Blo 1441540 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B36977795 : Blo 1441540 36977795 := bstep (se 1 (by rfl) ⟨27733346, by rfl⟩ : syracuseStep 36977795 = 55466693) B55466693
theorem B3464363 : Blo 1441540 3464363 := bstep (se 1 (by rfl) ⟨2598272, by rfl⟩ : syracuseStep 3464363 = 5196545) B5196545
theorem B4865291 : Blo 1441540 4865291 := bstep (se 1 (by rfl) ⟨3648968, by rfl⟩ : syracuseStep 4865291 = 7297937) B7297937
theorem B1826155 : Blo 1441540 1826155 := bstep (se 1 (by rfl) ⟨1369616, by rfl⟩ : syracuseStep 1826155 = 2739233) B2739233
theorem B4619663 : Blo 1441540 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B10960271 : Blo 1441540 10960271 := bstep (se 1 (by rfl) ⟨8220203, by rfl⟩ : syracuseStep 10960271 = 16440407) B16440407
theorem B2670007 : Blo 1441540 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B2309639 : Blo 1441540 2309639 := bstep (se 1 (by rfl) ⟨1732229, by rfl⟩ : syracuseStep 2309639 = 3464459) B3464459
theorem B4865561 : Blo 1441540 4865561 := bstep (se 2 (by rfl) ⟨1824585, by rfl⟩ : syracuseStep 4865561 = 3649171) B3649171
theorem B1826383 : Blo 1441540 1826383 := bstep (se 1 (by rfl) ⟨1369787, by rfl⟩ : syracuseStep 1826383 = 2739575) B2739575
theorem B3243617 : Blo 1441540 3243617 := bstep (se 2 (by rfl) ⟨1216356, by rfl⟩ : syracuseStep 3243617 = 2432713) B2432713
theorem B6159995 : Blo 1441540 6159995 := bstep (se 1 (by rfl) ⟨4619996, by rfl⟩ : syracuseStep 6159995 = 9239993) B9239993
theorem B11697803 : Blo 1441540 11697803 := bstep (se 1 (by rfl) ⟨8773352, by rfl⟩ : syracuseStep 11697803 = 17546705) B17546705
theorem B5480075 : Blo 1441540 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B2162375 : Blo 1441540 2162375 := bstep (se 1 (by rfl) ⟨1621781, by rfl⟩ : syracuseStep 2162375 = 3243563) B3243563
theorem B7798493 : Blo 1441540 7798493 := bstep (se 3 (by rfl) ⟨1462217, by rfl⟩ : syracuseStep 7798493 = 2924435) B2924435
theorem B2924281 : Blo 1441540 2924281 := bstep (se 2 (by rfl) ⟨1096605, by rfl⟩ : syracuseStep 2924281 = 2193211) B2193211
theorem B1441575 : Blo 1441540 1441575 := bstep (se 1 (by rfl) ⟨1081181, by rfl⟩ : syracuseStep 1441575 = 2162363) B2162363
theorem B1441615 : Blo 1441540 1441615 := bstep (se 1 (by rfl) ⟨1081211, by rfl⟩ : syracuseStep 1441615 = 2162423) B2162423
theorem B1441631 : Blo 1441540 1441631 := bstep (se 1 (by rfl) ⟨1081223, by rfl⟩ : syracuseStep 1441631 = 2162447) B2162447
theorem B2162537 : Blo 1441540 2162537 := bstep (se 2 (by rfl) ⟨810951, by rfl⟩ : syracuseStep 2162537 = 1621903) B1621903
theorem B2432875 : Blo 1441540 2432875 := bstep (se 1 (by rfl) ⟨1824656, by rfl⟩ : syracuseStep 2432875 = 3649313) B3649313
theorem B1441659 : Blo 1441540 1441659 := bstep (se 1 (by rfl) ⟨1081244, by rfl⟩ : syracuseStep 1441659 = 2162489) B2162489
theorem B1441711 : Blo 1441540 1441711 := bstep (se 1 (by rfl) ⟨1081283, by rfl⟩ : syracuseStep 1441711 = 2162567) B2162567
theorem B2162615 : Blo 1441540 2162615 := bstep (se 1 (by rfl) ⟨1621961, by rfl⟩ : syracuseStep 2162615 = 3243923) B3243923
theorem B3243959 : Blo 1441540 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B1441735 : Blo 1441540 1441735 := bstep (se 1 (by rfl) ⟨1081301, by rfl⟩ : syracuseStep 1441735 = 2162603) B2162603
theorem B1441755 : Blo 1441540 1441755 := bstep (se 1 (by rfl) ⟨1081316, by rfl⟩ : syracuseStep 1441755 = 2162633) B2162633
theorem B2162651 : Blo 1441540 2162651 := bstep (se 1 (by rfl) ⟨1621988, by rfl⟩ : syracuseStep 2162651 = 3243977) B3243977
theorem B17555459 : Blo 1441540 17555459 := bstep (se 1 (by rfl) ⟨13166594, by rfl⟩ : syracuseStep 17555459 = 26333189) B26333189
theorem B3653657 : Blo 1441540 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B12329009 : Blo 1441540 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B3899657 : Blo 1441540 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B1442079 : Blo 1441540 1442079 := bstep (se 1 (by rfl) ⟨1081559, by rfl⟩ : syracuseStep 1442079 = 2163119) B2163119
theorem B15606067 : Blo 1441540 15606067 := bstep (se 1 (by rfl) ⟨11704550, by rfl⟩ : syracuseStep 15606067 = 23409101) B23409101
theorem B2163035 : Blo 1441540 2163035 := bstep (se 1 (by rfl) ⟨1622276, by rfl⟩ : syracuseStep 2163035 = 3244553) B3244553
theorem B1442139 : Blo 1441540 1442139 := bstep (se 1 (by rfl) ⟨1081604, by rfl⟩ : syracuseStep 1442139 = 2163209) B2163209
theorem B8216923 : Blo 1441540 8216923 := bstep (se 1 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 8216923 = 12325385) B12325385
theorem B10961243 : Blo 1441540 10961243 := bstep (se 1 (by rfl) ⟨8220932, by rfl⟩ : syracuseStep 10961243 = 16441865) B16441865
theorem B1442159 : Blo 1441540 1442159 := bstep (se 1 (by rfl) ⟨1081619, by rfl⟩ : syracuseStep 1442159 = 2163239) B2163239
theorem B1442215 : Blo 1441540 1442215 := bstep (se 1 (by rfl) ⟨1081661, by rfl⟩ : syracuseStep 1442215 = 2163323) B2163323
theorem B2466215 : Blo 1441540 2466215 := bstep (se 1 (by rfl) ⟨1849661, by rfl⟩ : syracuseStep 2466215 = 3699323) B3699323
theorem B4866479 : Blo 1441540 4866479 := bstep (se 1 (by rfl) ⟨3649859, by rfl⟩ : syracuseStep 4866479 = 7299719) B7299719
theorem B3244463 : Blo 1441540 3244463 := bstep (se 1 (by rfl) ⟨2433347, by rfl⟩ : syracuseStep 3244463 = 4866695) B4866695
theorem B3244499 : Blo 1441540 3244499 := bstep (se 1 (by rfl) ⟨2433374, by rfl⟩ : syracuseStep 3244499 = 4866749) B4866749
theorem B1442299 : Blo 1441540 1442299 := bstep (se 1 (by rfl) ⟨1081724, by rfl⟩ : syracuseStep 1442299 = 2163449) B2163449
theorem B3244607 : Blo 1441540 3244607 := bstep (se 1 (by rfl) ⟨2433455, by rfl⟩ : syracuseStep 3244607 = 4866911) B4866911
theorem B2163263 : Blo 1441540 2163263 := bstep (se 1 (by rfl) ⟨1622447, by rfl⟩ : syracuseStep 2163263 = 3244895) B3244895
theorem B1442367 : Blo 1441540 1442367 := bstep (se 1 (by rfl) ⟨1081775, by rfl⟩ : syracuseStep 1442367 = 2163551) B2163551
theorem B1442375 : Blo 1441540 1442375 := bstep (se 1 (by rfl) ⟨1081781, by rfl⟩ : syracuseStep 1442375 = 2163563) B2163563
theorem B1622623 : Blo 1441540 1622623 := bstep (se 1 (by rfl) ⟨1216967, by rfl⟩ : syracuseStep 1622623 = 2433935) B2433935
theorem B3244715 : Blo 1441540 3244715 := bstep (se 1 (by rfl) ⟨2433536, by rfl⟩ : syracuseStep 3244715 = 4867073) B4867073
theorem B3900079 : Blo 1441540 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B2433719 : Blo 1441540 2433719 := bstep (se 1 (by rfl) ⟨1825289, by rfl⟩ : syracuseStep 2433719 = 3650579) B3650579
theorem B2163383 : Blo 1441540 2163383 := bstep (se 1 (by rfl) ⟨1622537, by rfl⟩ : syracuseStep 2163383 = 3245075) B3245075
theorem B1442527 : Blo 1441540 1442527 := bstep (se 1 (by rfl) ⟨1081895, by rfl⟩ : syracuseStep 1442527 = 2163791) B2163791
theorem B1442607 : Blo 1441540 1442607 := bstep (se 1 (by rfl) ⟨1081955, by rfl⟩ : syracuseStep 1442607 = 2163911) B2163911
theorem B2163611 : Blo 1441540 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B1442715 : Blo 1441540 1442715 := bstep (se 1 (by rfl) ⟨1082036, by rfl⟩ : syracuseStep 1442715 = 2164073) B2164073
theorem B1442767 : Blo 1441540 1442767 := bstep (se 1 (by rfl) ⟨1082075, by rfl⟩ : syracuseStep 1442767 = 2164151) B2164151
theorem B1442791 : Blo 1441540 1442791 := bstep (se 1 (by rfl) ⟨1082093, by rfl⟩ : syracuseStep 1442791 = 2164187) B2164187
theorem B3245255 : Blo 1441540 3245255 := bstep (se 1 (by rfl) ⟨2433941, by rfl⟩ : syracuseStep 3245255 = 4867883) B4867883
theorem B3466439 : Blo 1441540 3466439 := bstep (se 1 (by rfl) ⟨2599829, by rfl⟩ : syracuseStep 3466439 = 5199659) B5199659
theorem B3081415 : Blo 1441540 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B3900631 : Blo 1441540 3900631 := bstep (se 1 (by rfl) ⟨2925473, by rfl⟩ : syracuseStep 3900631 = 5850947) B5850947
theorem B3081449 : Blo 1441540 3081449 := bstep (se 2 (by rfl) ⟨1155543, by rfl⟩ : syracuseStep 3081449 = 2311087) B2311087
theorem B1443103 : Blo 1441540 1443103 := bstep (se 1 (by rfl) ⟨1082327, by rfl⟩ : syracuseStep 1443103 = 2164655) B2164655
theorem B2164007 : Blo 1441540 2164007 := bstep (se 1 (by rfl) ⟨1623005, by rfl⟩ : syracuseStep 2164007 = 3246011) B3246011
theorem B1443163 : Blo 1441540 1443163 := bstep (se 1 (by rfl) ⟨1082372, by rfl⟩ : syracuseStep 1443163 = 2164745) B2164745
theorem B1443183 : Blo 1441540 1443183 := bstep (se 1 (by rfl) ⟨1082387, by rfl⟩ : syracuseStep 1443183 = 2164775) B2164775
theorem B4867451 : Blo 1441540 4867451 := bstep (se 1 (by rfl) ⟨3650588, by rfl⟩ : syracuseStep 4867451 = 7301177) B7301177
theorem B3245435 : Blo 1441540 3245435 := bstep (se 1 (by rfl) ⟨2434076, by rfl⟩ : syracuseStep 3245435 = 4868153) B4868153
theorem B2164091 : Blo 1441540 2164091 := bstep (se 1 (by rfl) ⟨1623068, by rfl⟩ : syracuseStep 2164091 = 3246137) B3246137
theorem B2434441 : Blo 1441540 2434441 := bstep (se 2 (by rfl) ⟨912915, by rfl⟩ : syracuseStep 2434441 = 1825831) B1825831
theorem B1443239 : Blo 1441540 1443239 := bstep (se 1 (by rfl) ⟨1082429, by rfl⟩ : syracuseStep 1443239 = 2164859) B2164859
theorem B3245561 : Blo 1441540 3245561 := bstep (se 2 (by rfl) ⟨1217085, by rfl⟩ : syracuseStep 3245561 = 2434171) B2434171
theorem B2164217 : Blo 1441540 2164217 := bstep (se 2 (by rfl) ⟨811581, by rfl⟩ : syracuseStep 2164217 = 1623163) B1623163
theorem B1443323 : Blo 1441540 1443323 := bstep (se 1 (by rfl) ⟨1082492, by rfl⟩ : syracuseStep 1443323 = 2164985) B2164985
theorem B1443391 : Blo 1441540 1443391 := bstep (se 1 (by rfl) ⟨1082543, by rfl⟩ : syracuseStep 1443391 = 2165087) B2165087
theorem B1443399 : Blo 1441540 1443399 := bstep (se 1 (by rfl) ⟨1082549, by rfl⟩ : syracuseStep 1443399 = 2165099) B2165099
theorem B3245651 : Blo 1441540 3245651 := bstep (se 1 (by rfl) ⟨2434238, by rfl⟩ : syracuseStep 3245651 = 4868477) B4868477
theorem B2467423 : Blo 1441540 2467423 := bstep (se 1 (by rfl) ⟨1850567, by rfl⟩ : syracuseStep 2467423 = 3701135) B3701135
theorem B2164319 : Blo 1441540 2164319 := bstep (se 1 (by rfl) ⟨1623239, by rfl⟩ : syracuseStep 2164319 = 3246479) B3246479
theorem B1623775 : Blo 1441540 1623775 := bstep (se 1 (by rfl) ⟨1217831, by rfl⟩ : syracuseStep 1623775 = 2435663) B2435663
theorem B3245831 : Blo 1441540 3245831 := bstep (se 1 (by rfl) ⟨2434373, by rfl⟩ : syracuseStep 3245831 = 4868747) B4868747
theorem B2164535 : Blo 1441540 2164535 := bstep (se 1 (by rfl) ⟨1623401, by rfl⟩ : syracuseStep 2164535 = 3246803) B3246803
theorem B2434873 : Blo 1441540 2434873 := bstep (se 2 (by rfl) ⟨913077, by rfl⟩ : syracuseStep 2434873 = 1826155) B1826155
theorem B94799747 : Blo 1441540 94799747 := bstep (se 1 (by rfl) ⟨71099810, by rfl⟩ : syracuseStep 94799747 = 142199621) B142199621
theorem B13518737 : Blo 1441540 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B24651863 : Blo 1441540 24651863 := bstep (se 1 (by rfl) ⟨18488897, by rfl⟩ : syracuseStep 24651863 = 36977795) B36977795
theorem B2435177 : Blo 1441540 2435177 := bstep (se 2 (by rfl) ⟨913191, by rfl⟩ : syracuseStep 2435177 = 1826383) B1826383
theorem B2164841 : Blo 1441540 2164841 := bstep (se 2 (by rfl) ⟨811815, by rfl⟩ : syracuseStep 2164841 = 1623631) B1623631
theorem B4622521 : Blo 1441540 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B3246443 : Blo 1441540 3246443 := bstep (se 1 (by rfl) ⟨2434832, by rfl⟩ : syracuseStep 3246443 = 4869665) B4869665
theorem B7301501 : Blo 1441540 7301501 := bstep (se 3 (by rfl) ⟨1369031, by rfl⟩ : syracuseStep 7301501 = 2738063) B2738063
theorem B4106663 : Blo 1441540 4106663 := bstep (se 1 (by rfl) ⟨3079997, by rfl⟩ : syracuseStep 4106663 = 6159995) B6159995
theorem B2165159 : Blo 1441540 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B3246587 : Blo 1441540 3246587 := bstep (se 1 (by rfl) ⟨2434940, by rfl⟩ : syracuseStep 3246587 = 4869881) B4869881
theorem B2165243 : Blo 1441540 2165243 := bstep (se 1 (by rfl) ⟨1623932, by rfl⟩ : syracuseStep 2165243 = 3247865) B3247865
theorem B3246713 : Blo 1441540 3246713 := bstep (se 2 (by rfl) ⟨1217517, by rfl⟩ : syracuseStep 3246713 = 2435035) B2435035
theorem B3246767 : Blo 1441540 3246767 := bstep (se 1 (by rfl) ⟨2435075, by rfl⟩ : syracuseStep 3246767 = 4870151) B4870151
theorem B4868855 : Blo 1441540 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B3246839 : Blo 1441540 3246839 := bstep (se 1 (by rfl) ⟨2435129, by rfl⟩ : syracuseStep 3246839 = 4870259) B4870259
theorem B31206167 : Blo 1441540 31206167 := bstep (se 1 (by rfl) ⟨23404625, by rfl⟩ : syracuseStep 31206167 = 46809251) B46809251
theorem B5475215 : Blo 1441540 5475215 := bstep (se 1 (by rfl) ⟨4106411, by rfl⟩ : syracuseStep 5475215 = 8212823) B8212823
theorem B3247019 : Blo 1441540 3247019 := bstep (se 1 (by rfl) ⟨2435264, by rfl⟩ : syracuseStep 3247019 = 4870529) B4870529
theorem B3468275 : Blo 1441540 3468275 := bstep (se 1 (by rfl) ⟨2601206, by rfl⟩ : syracuseStep 3468275 = 5202413) B5202413
theorem B26307665 : Blo 1441540 26307665 := bstep (se 2 (by rfl) ⟨9865374, by rfl⟩ : syracuseStep 26307665 = 19730749) B19730749
theorem B157933475 : Blo 1441540 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B4623713 : Blo 1441540 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B3247559 : Blo 1441540 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B16428743 : Blo 1441540 16428743 := bstep (se 1 (by rfl) ⟨12321557, by rfl⟩ : syracuseStep 16428743 = 24643115) B24643115
theorem B7900969 : Blo 1441540 7900969 := bstep (se 2 (by rfl) ⟨2962863, by rfl⟩ : syracuseStep 7900969 = 5925727) B5925727
theorem B7302959 : Blo 1441540 7302959 := bstep (se 1 (by rfl) ⟨5477219, by rfl⟩ : syracuseStep 7302959 = 10954439) B10954439
theorem B4869935 : Blo 1441540 4869935 := bstep (se 1 (by rfl) ⟨3652451, by rfl⟩ : syracuseStep 4869935 = 7304903) B7304903
theorem B3247919 : Blo 1441540 3247919 := bstep (se 1 (by rfl) ⟨2435939, by rfl⟩ : syracuseStep 3247919 = 4871879) B4871879
theorem B5476157 : Blo 1441540 5476157 := bstep (se 3 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 5476157 = 2053559) B2053559
theorem B12316637 : Blo 1441540 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B7803337 : Blo 1441540 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B3560009 : Blo 1441540 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B1757803 : Blo 1441540 1757803 := bstep (se 1 (by rfl) ⟨1318352, by rfl⟩ : syracuseStep 1757803 = 2636705) B2636705
theorem B6583007 : Blo 1441540 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B3650447 : Blo 1441540 3650447 := bstep (se 1 (by rfl) ⟨2737835, by rfl⟩ : syracuseStep 3650447 = 5475671) B5475671
theorem B30012407 : Blo 1441540 30012407 := bstep (se 1 (by rfl) ⟨22509305, by rfl⟩ : syracuseStep 30012407 = 45018611) B45018611
theorem B7705637 : Blo 1441540 7705637 := bstep (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) B1444807
theorem B7402585 : Blo 1441540 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B15602777 : Blo 1441540 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B5198995 : Blo 1441540 5198995 := bstep (se 1 (by rfl) ⟨3899246, by rfl⟩ : syracuseStep 5198995 = 7798493) B7798493
theorem B4109555 : Blo 1441540 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B7402745 : Blo 1441540 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B22205821 : Blo 1441540 22205821 := bstep (se 3 (by rfl) ⟨4163591, by rfl⟩ : syracuseStep 22205821 = 8327183) B8327183
theorem B3650953 : Blo 1441540 3650953 := bstep (se 2 (by rfl) ⟨1369107, by rfl⟩ : syracuseStep 3650953 = 2738215) B2738215
theorem B3651065 : Blo 1441540 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B4110011 : Blo 1441540 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B12318551 : Blo 1441540 12318551 := bstep (se 1 (by rfl) ⟨9238913, by rfl⟩ : syracuseStep 12318551 = 18477827) B18477827
theorem B3897193 : Blo 1441540 3897193 := bstep (se 2 (by rfl) ⟨1461447, by rfl⟩ : syracuseStep 3897193 = 2922895) B2922895
theorem B7305065 : Blo 1441540 7305065 := bstep (se 2 (by rfl) ⟨2739399, by rfl⟩ : syracuseStep 7305065 = 5478799) B5478799
theorem B9238607 : Blo 1441540 9238607 := bstep (se 1 (by rfl) ⟨6928955, by rfl⟩ : syracuseStep 9238607 = 13857911) B13857911
theorem B3651713 : Blo 1441540 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B35100803 : Blo 1441540 35100803 := bstep (se 1 (by rfl) ⟨26325602, by rfl⟩ : syracuseStep 35100803 = 52651205) B52651205
theorem B6928649 : Blo 1441540 6928649 := bstep (se 2 (by rfl) ⟨2598243, by rfl⟩ : syracuseStep 6928649 = 5196487) B5196487
theorem B10951037 : Blo 1441540 10951037 := bstep (se 3 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 10951037 = 4106639) B4106639
theorem B9238967 : Blo 1441540 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B5200379 : Blo 1441540 5200379 := bstep (se 1 (by rfl) ⟨3900284, by rfl⟩ : syracuseStep 5200379 = 7800569) B7800569
theorem B15596165 : Blo 1441540 15596165 := bstep (se 4 (by rfl) ⟨1462140, by rfl⟩ : syracuseStep 15596165 = 2924281) B2924281
theorem B6158987 : Blo 1441540 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B6159037 : Blo 1441540 6159037 := bstep (se 3 (by rfl) ⟨1154819, by rfl⟩ : syracuseStep 6159037 = 2309639) B2309639
theorem B20781967 : Blo 1441540 20781967 := bstep (se 1 (by rfl) ⟨15586475, by rfl⟩ : syracuseStep 20781967 = 31172951) B31172951
theorem B2341787 : Blo 1441540 2341787 := bstep (se 1 (by rfl) ⟨1756340, by rfl⟩ : syracuseStep 2341787 = 3512681) B3512681
theorem B3652523 : Blo 1441540 3652523 := bstep (se 1 (by rfl) ⟨2739392, by rfl⟩ : syracuseStep 3652523 = 5478785) B5478785
theorem B23411699 : Blo 1441540 23411699 := bstep (se 1 (by rfl) ⟨17558774, by rfl⟩ : syracuseStep 23411699 = 35117549) B35117549
theorem B10403005 : Blo 1441540 10403005 := bstep (se 3 (by rfl) ⟨1950563, by rfl⟩ : syracuseStep 10403005 = 3901127) B3901127
theorem B4865399 : Blo 1441540 4865399 := bstep (se 1 (by rfl) ⟨3649049, by rfl⟩ : syracuseStep 4865399 = 7298099) B7298099
theorem B7298423 : Blo 1441540 7298423 := bstep (se 1 (by rfl) ⟨5473817, by rfl⟩ : syracuseStep 7298423 = 10947635) B10947635
theorem B6929783 : Blo 1441540 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B3464585 : Blo 1441540 3464585 := bstep (se 2 (by rfl) ⟨1299219, by rfl⟩ : syracuseStep 3464585 = 2598439) B2598439
theorem B2309575 : Blo 1441540 2309575 := bstep (se 1 (by rfl) ⟨1732181, by rfl⟩ : syracuseStep 2309575 = 3464363) B3464363
theorem B8437241 : Blo 1441540 8437241 := bstep (se 2 (by rfl) ⟨3163965, by rfl⟩ : syracuseStep 8437241 = 6327931) B6327931
theorem B3243527 : Blo 1441540 3243527 := bstep (se 1 (by rfl) ⟨2432645, by rfl⟩ : syracuseStep 3243527 = 4865291) B4865291
theorem B7298585 : Blo 1441540 7298585 := bstep (se 2 (by rfl) ⟨2736969, by rfl⟩ : syracuseStep 7298585 = 5473939) B5473939
theorem B3079775 : Blo 1441540 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B7306847 : Blo 1441540 7306847 := bstep (se 1 (by rfl) ⟨5480135, by rfl⟩ : syracuseStep 7306847 = 10960271) B10960271
theorem B5480045 : Blo 1441540 5480045 := bstep (se 3 (by rfl) ⟨1027508, by rfl⟩ : syracuseStep 5480045 = 2055017) B2055017
theorem B1826479 : Blo 1441540 1826479 := bstep (se 1 (by rfl) ⟨1369859, by rfl⟩ : syracuseStep 1826479 = 2739719) B2739719
theorem B3243707 : Blo 1441540 3243707 := bstep (se 1 (by rfl) ⟨2432780, by rfl⟩ : syracuseStep 3243707 = 4865561) B4865561
theorem B2162411 : Blo 1441540 2162411 := bstep (se 1 (by rfl) ⟨1621808, by rfl⟩ : syracuseStep 2162411 = 3243617) B3243617
theorem B2432747 : Blo 1441540 2432747 := bstep (se 1 (by rfl) ⟨1824560, by rfl⟩ : syracuseStep 2432747 = 3649121) B3649121
theorem B7798535 : Blo 1441540 7798535 := bstep (se 1 (by rfl) ⟨5848901, by rfl⟩ : syracuseStep 7798535 = 11697803) B11697803
theorem B3653383 : Blo 1441540 3653383 := bstep (se 1 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 3653383 = 5480075) B5480075
theorem B41606945 : Blo 1441540 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B1441583 : Blo 1441540 1441583 := bstep (se 1 (by rfl) ⟨1081187, by rfl⟩ : syracuseStep 1441583 = 2162375) B2162375
theorem B3243833 : Blo 1441540 3243833 := bstep (se 2 (by rfl) ⟨1216437, by rfl⟩ : syracuseStep 3243833 = 2432875) B2432875
theorem B1441691 : Blo 1441540 1441691 := bstep (se 1 (by rfl) ⟨1081268, by rfl⟩ : syracuseStep 1441691 = 2162537) B2162537
theorem B1441743 : Blo 1441540 1441743 := bstep (se 1 (by rfl) ⟨1081307, by rfl⟩ : syracuseStep 1441743 = 2162615) B2162615
theorem B2162639 : Blo 1441540 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B1441767 : Blo 1441540 1441767 := bstep (se 1 (by rfl) ⟨1081325, by rfl⟩ : syracuseStep 1441767 = 2162651) B2162651
theorem B1442023 : Blo 1441540 1442023 := bstep (se 1 (by rfl) ⟨1081517, by rfl⟩ : syracuseStep 1442023 = 2163035) B2163035
theorem B7307495 : Blo 1441540 7307495 := bstep (se 1 (by rfl) ⟨5480621, by rfl⟩ : syracuseStep 7307495 = 10961243) B10961243
theorem B3244319 : Blo 1441540 3244319 := bstep (se 1 (by rfl) ⟨2433239, by rfl⟩ : syracuseStep 3244319 = 4866479) B4866479
theorem B2162975 : Blo 1441540 2162975 := bstep (se 1 (by rfl) ⟨1622231, by rfl⟩ : syracuseStep 2162975 = 3244463) B3244463
theorem B2162999 : Blo 1441540 2162999 := bstep (se 1 (by rfl) ⟨1622249, by rfl⟩ : syracuseStep 2162999 = 3244499) B3244499
theorem B2163071 : Blo 1441540 2163071 := bstep (se 1 (by rfl) ⟨1622303, by rfl⟩ : syracuseStep 2163071 = 3244607) B3244607
theorem B1442175 : Blo 1441540 1442175 := bstep (se 1 (by rfl) ⟨1081631, by rfl⟩ : syracuseStep 1442175 = 2163263) B2163263
theorem B20808089 : Blo 1441540 20808089 := bstep (se 2 (by rfl) ⟨7803033, by rfl⟩ : syracuseStep 20808089 = 15606067) B15606067
theorem B2163143 : Blo 1441540 2163143 := bstep (se 1 (by rfl) ⟨1622357, by rfl⟩ : syracuseStep 2163143 = 3244715) B3244715
theorem B1622479 : Blo 1441540 1622479 := bstep (se 1 (by rfl) ⟨1216859, by rfl⟩ : syracuseStep 1622479 = 2433719) B2433719
theorem B1442255 : Blo 1441540 1442255 := bstep (se 1 (by rfl) ⟨1081691, by rfl⟩ : syracuseStep 1442255 = 2163383) B2163383
theorem B2433631 : Blo 1441540 2433631 := bstep (se 1 (by rfl) ⟨1825223, by rfl⟩ : syracuseStep 2433631 = 3650447) B3650447
theorem B10404449 : Blo 1441540 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B1442407 : Blo 1441540 1442407 := bstep (se 1 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 1442407 = 2163611) B2163611
theorem B8217197 : Blo 1441540 8217197 := bstep (se 3 (by rfl) ⟨1540724, by rfl⟩ : syracuseStep 8217197 = 3081449) B3081449
theorem B5137091 : Blo 1441540 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B2163497 : Blo 1441540 2163497 := bstep (se 2 (by rfl) ⟨811311, by rfl⟩ : syracuseStep 2163497 = 1622623) B1622623
theorem B2163503 : Blo 1441540 2163503 := bstep (se 1 (by rfl) ⟨1622627, by rfl⟩ : syracuseStep 2163503 = 3245255) B3245255
theorem B2310959 : Blo 1441540 2310959 := bstep (se 1 (by rfl) ⟨1733219, by rfl⟩ : syracuseStep 2310959 = 3466439) B3466439
theorem B2343737 : Blo 1441540 2343737 := bstep (se 2 (by rfl) ⟨878901, by rfl⟩ : syracuseStep 2343737 = 1757803) B1757803
theorem B1442671 : Blo 1441540 1442671 := bstep (se 1 (by rfl) ⟨1082003, by rfl⟩ : syracuseStep 1442671 = 2164007) B2164007
theorem B3244967 : Blo 1441540 3244967 := bstep (se 1 (by rfl) ⟨2433725, by rfl⟩ : syracuseStep 3244967 = 4867451) B4867451
theorem B2163623 : Blo 1441540 2163623 := bstep (se 1 (by rfl) ⟨1622717, by rfl⟩ : syracuseStep 2163623 = 3245435) B3245435
theorem B1442727 : Blo 1441540 1442727 := bstep (se 1 (by rfl) ⟨1082045, by rfl⟩ : syracuseStep 1442727 = 2164091) B2164091
theorem B20800421 : Blo 1441540 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B2434043 : Blo 1441540 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B2163707 : Blo 1441540 2163707 := bstep (se 1 (by rfl) ⟨1622780, by rfl⟩ : syracuseStep 2163707 = 3245561) B3245561
theorem B1442811 : Blo 1441540 1442811 := bstep (se 1 (by rfl) ⟨1082108, by rfl⟩ : syracuseStep 1442811 = 2164217) B2164217
theorem B2163767 : Blo 1441540 2163767 := bstep (se 1 (by rfl) ⟨1622825, by rfl⟩ : syracuseStep 2163767 = 3245651) B3245651
theorem B1442879 : Blo 1441540 1442879 := bstep (se 1 (by rfl) ⟨1082159, by rfl⟩ : syracuseStep 1442879 = 2164319) B2164319
theorem B2163887 : Blo 1441540 2163887 := bstep (se 1 (by rfl) ⟨1622915, by rfl⟩ : syracuseStep 2163887 = 3245831) B3245831
theorem B1443023 : Blo 1441540 1443023 := bstep (se 1 (by rfl) ⟨1082267, by rfl⟩ : syracuseStep 1443023 = 2164535) B2164535
theorem B9012491 : Blo 1441540 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B16434575 : Blo 1441540 16434575 := bstep (se 1 (by rfl) ⟨12325931, by rfl⟩ : syracuseStep 16434575 = 24651863) B24651863
theorem B1623451 : Blo 1441540 1623451 := bstep (se 1 (by rfl) ⟨1217588, by rfl⟩ : syracuseStep 1623451 = 2435177) B2435177
theorem B1443227 : Blo 1441540 1443227 := bstep (se 1 (by rfl) ⟨1082420, by rfl⟩ : syracuseStep 1443227 = 2164841) B2164841
theorem B2434475 : Blo 1441540 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B6931993 : Blo 1441540 6931993 := bstep (se 2 (by rfl) ⟨2599497, by rfl⟩ : syracuseStep 6931993 = 5198995) B5198995
theorem B2164295 : Blo 1441540 2164295 := bstep (se 1 (by rfl) ⟨1623221, by rfl⟩ : syracuseStep 2164295 = 3246443) B3246443
theorem B13870673 : Blo 1441540 13870673 := bstep (se 2 (by rfl) ⟨5201502, by rfl⟩ : syracuseStep 13870673 = 10403005) B10403005
theorem B7300691 : Blo 1441540 7300691 := bstep (se 1 (by rfl) ⟨5475518, by rfl⟩ : syracuseStep 7300691 = 10951037) B10951037
theorem B4867667 : Blo 1441540 4867667 := bstep (se 1 (by rfl) ⟨3650750, by rfl⟩ : syracuseStep 4867667 = 7301501) B7301501
theorem B2737775 : Blo 1441540 2737775 := bstep (se 1 (by rfl) ⟨2053331, by rfl⟩ : syracuseStep 2737775 = 4106663) B4106663
theorem B1443439 : Blo 1441540 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B3466919 : Blo 1441540 3466919 := bstep (se 1 (by rfl) ⟨2600189, by rfl⟩ : syracuseStep 3466919 = 5200379) B5200379
theorem B2164391 : Blo 1441540 2164391 := bstep (se 1 (by rfl) ⟨1623293, by rfl⟩ : syracuseStep 2164391 = 3246587) B3246587
theorem B1443495 : Blo 1441540 1443495 := bstep (se 1 (by rfl) ⟨1082621, by rfl⟩ : syracuseStep 1443495 = 2165243) B2165243
theorem B2164475 : Blo 1441540 2164475 := bstep (se 1 (by rfl) ⟨1623356, by rfl⟩ : syracuseStep 2164475 = 3246713) B3246713
theorem B10397443 : Blo 1441540 10397443 := bstep (se 1 (by rfl) ⟨7798082, by rfl⟩ : syracuseStep 10397443 = 15596165) B15596165
theorem B4105991 : Blo 1441540 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B2164511 : Blo 1441540 2164511 := bstep (se 1 (by rfl) ⟨1623383, by rfl⟩ : syracuseStep 2164511 = 3246767) B3246767
theorem B3245903 : Blo 1441540 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B2164559 : Blo 1441540 2164559 := bstep (se 1 (by rfl) ⟨1623419, by rfl⟩ : syracuseStep 2164559 = 3246839) B3246839
theorem B29607761 : Blo 1441540 29607761 := bstep (se 2 (by rfl) ⟨11102910, by rfl⟩ : syracuseStep 29607761 = 22205821) B22205821
theorem B4867937 : Blo 1441540 4867937 := bstep (se 2 (by rfl) ⟨1825476, by rfl⟩ : syracuseStep 4867937 = 3650953) B3650953
theorem B3245921 : Blo 1441540 3245921 := bstep (se 2 (by rfl) ⟨1217220, by rfl⟩ : syracuseStep 3245921 = 2434441) B2434441
theorem B2435015 : Blo 1441540 2435015 := bstep (se 1 (by rfl) ⟨1826261, by rfl⟩ : syracuseStep 2435015 = 3652523) B3652523
theorem B2164679 : Blo 1441540 2164679 := bstep (se 1 (by rfl) ⟨1623509, by rfl⟩ : syracuseStep 2164679 = 3247019) B3247019
theorem B2312183 : Blo 1441540 2312183 := bstep (se 1 (by rfl) ⟨1734137, by rfl⟩ : syracuseStep 2312183 = 3468275) B3468275
theorem B15607799 : Blo 1441540 15607799 := bstep (se 1 (by rfl) ⟨11705849, by rfl⟩ : syracuseStep 15607799 = 23411699) B23411699
theorem B2435305 : Blo 1441540 2435305 := bstep (se 2 (by rfl) ⟨913239, by rfl⟩ : syracuseStep 2435305 = 1826479) B1826479
theorem B3082475 : Blo 1441540 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B2165033 : Blo 1441540 2165033 := bstep (se 2 (by rfl) ⟨811887, by rfl⟩ : syracuseStep 2165033 = 1623775) B1623775
theorem B2165039 : Blo 1441540 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B252799325 : Blo 1441540 252799325 := bstep (se 3 (by rfl) ⟨47399873, by rfl⟩ : syracuseStep 252799325 = 94799747) B94799747
theorem B6244765 : Blo 1441540 6244765 := bstep (se 3 (by rfl) ⟨1170893, by rfl⟩ : syracuseStep 6244765 = 2341787) B2341787
theorem B3246497 : Blo 1441540 3246497 := bstep (se 2 (by rfl) ⟨1217436, by rfl⟩ : syracuseStep 3246497 = 2434873) B2434873
theorem B5196257 : Blo 1441540 5196257 := bstep (se 2 (by rfl) ⟨1948596, by rfl⟩ : syracuseStep 5196257 = 3897193) B3897193
theorem B4868639 : Blo 1441540 4868639 := bstep (se 1 (by rfl) ⟨3651479, by rfl⟩ : syracuseStep 4868639 = 7302959) B7302959
theorem B3246623 : Blo 1441540 3246623 := bstep (se 1 (by rfl) ⟨2434967, by rfl⟩ : syracuseStep 3246623 = 4869935) B4869935
theorem B2165279 : Blo 1441540 2165279 := bstep (se 1 (by rfl) ⟨1623959, by rfl⟩ : syracuseStep 2165279 = 3247919) B3247919
theorem B8211091 : Blo 1441540 8211091 := bstep (se 1 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 8211091 = 12316637) B12316637
theorem B2435771 : Blo 1441540 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B8219339 : Blo 1441540 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B2599771 : Blo 1441540 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B6163361 : Blo 1441540 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B10955897 : Blo 1441540 10955897 := bstep (se 2 (by rfl) ⟨4108461, by rfl⟩ : syracuseStep 10955897 = 8216923) B8216923
theorem B13159589 : Blo 1441540 13159589 := bstep (se 4 (by rfl) ⟨1233711, by rfl⟩ : syracuseStep 13159589 = 2467423) B2467423
theorem B20008271 : Blo 1441540 20008271 := bstep (se 1 (by rfl) ⟨15006203, by rfl⟩ : syracuseStep 20008271 = 30012407) B30012407
theorem B4935163 : Blo 1441540 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B8212049 : Blo 1441540 8212049 := bstep (se 2 (by rfl) ⟨3079518, by rfl⟩ : syracuseStep 8212049 = 6159037) B6159037
theorem B2740007 : Blo 1441540 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B27709289 : Blo 1441540 27709289 := bstep (se 2 (by rfl) ⟨10390983, by rfl⟩ : syracuseStep 27709289 = 20781967) B20781967
theorem B8212367 : Blo 1441540 8212367 := bstep (se 1 (by rfl) ⟨6159275, by rfl⟩ : syracuseStep 8212367 = 12318551) B12318551
theorem B4870043 : Blo 1441540 4870043 := bstep (se 1 (by rfl) ⟨3652532, by rfl⟩ : syracuseStep 4870043 = 7305065) B7305065
theorem B22499309 : Blo 1441540 22499309 := bstep (se 3 (by rfl) ⟨4218620, by rfl⟩ : syracuseStep 22499309 = 8437241) B8437241
theorem B23400535 : Blo 1441540 23400535 := bstep (se 1 (by rfl) ⟨17550401, by rfl⟩ : syracuseStep 23400535 = 35100803) B35100803
theorem B4108553 : Blo 1441540 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B20804111 : Blo 1441540 20804111 := bstep (se 1 (by rfl) ⟨15603083, by rfl⟩ : syracuseStep 20804111 = 31206167) B31206167
theorem B3650143 : Blo 1441540 3650143 := bstep (se 1 (by rfl) ⟨2737607, by rfl⟩ : syracuseStep 3650143 = 5475215) B5475215
theorem B4871177 : Blo 1441540 4871177 := bstep (se 2 (by rfl) ⟨1826691, by rfl⟩ : syracuseStep 4871177 = 3653383) B3653383
theorem B2053183 : Blo 1441540 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B4871231 : Blo 1441540 4871231 := bstep (se 1 (by rfl) ⟨3653423, by rfl⟩ : syracuseStep 4871231 = 7306847) B7306847
theorem B5199023 : Blo 1441540 5199023 := bstep (se 1 (by rfl) ⟨3899267, by rfl⟩ : syracuseStep 5199023 = 7798535) B7798535
theorem B3650771 : Blo 1441540 3650771 := bstep (se 1 (by rfl) ⟨2738078, by rfl⟩ : syracuseStep 3650771 = 5476157) B5476157
theorem B105288983 : Blo 1441540 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B46814557 : Blo 1441540 46814557 := bstep (se 3 (by rfl) ⟨8777729, by rfl⟩ : syracuseStep 46814557 = 17555459) B17555459
theorem B1644143 : Blo 1441540 1644143 := bstep (se 1 (by rfl) ⟨1233107, by rfl⟩ : syracuseStep 1644143 = 2466215) B2466215
theorem B4388671 : Blo 1441540 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B10958813 : Blo 1441540 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B10401851 : Blo 1441540 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B6159071 : Blo 1441540 6159071 := bstep (se 1 (by rfl) ⟨4619303, by rfl⟩ : syracuseStep 6159071 = 9238607) B9238607
theorem B9870113 : Blo 1441540 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B4619099 : Blo 1441540 4619099 := bstep (se 1 (by rfl) ⟨3464324, by rfl⟩ : syracuseStep 4619099 = 6928649) B6928649
theorem B9493357 : Blo 1441540 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B5200841 : Blo 1441540 5200841 := bstep (se 2 (by rfl) ⟨1950315, by rfl⟩ : syracuseStep 5200841 = 3900631) B3900631
theorem B6159311 : Blo 1441540 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B3079433 : Blo 1441540 3079433 := bstep (se 2 (by rfl) ⟨1154787, by rfl⟩ : syracuseStep 3079433 = 2309575) B2309575
theorem B17538443 : Blo 1441540 17538443 := bstep (se 1 (by rfl) ⟨13153832, by rfl⟩ : syracuseStep 17538443 = 26307665) B26307665
theorem B3243599 : Blo 1441540 3243599 := bstep (se 1 (by rfl) ⟨2432699, by rfl⟩ : syracuseStep 3243599 = 4865399) B4865399
theorem B4865615 : Blo 1441540 4865615 := bstep (se 1 (by rfl) ⟨3649211, by rfl⟩ : syracuseStep 4865615 = 7298423) B7298423
theorem B4619855 : Blo 1441540 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B2309723 : Blo 1441540 2309723 := bstep (se 1 (by rfl) ⟨1732292, by rfl⟩ : syracuseStep 2309723 = 3464585) B3464585
theorem B2162351 : Blo 1441540 2162351 := bstep (se 1 (by rfl) ⟨1621763, by rfl⟩ : syracuseStep 2162351 = 3243527) B3243527
theorem B4865723 : Blo 1441540 4865723 := bstep (se 1 (by rfl) ⟨3649292, by rfl⟩ : syracuseStep 4865723 = 7298585) B7298585
theorem B10534625 : Blo 1441540 10534625 := bstep (se 2 (by rfl) ⟨3950484, by rfl⟩ : syracuseStep 10534625 = 7900969) B7900969
theorem B3653363 : Blo 1441540 3653363 := bstep (se 1 (by rfl) ⟨2740022, by rfl⟩ : syracuseStep 3653363 = 5480045) B5480045
theorem B2162471 : Blo 1441540 2162471 := bstep (se 1 (by rfl) ⟨1621853, by rfl⟩ : syracuseStep 2162471 = 3243707) B3243707
theorem B10952495 : Blo 1441540 10952495 := bstep (se 1 (by rfl) ⟨8214371, by rfl⟩ : syracuseStep 10952495 = 16428743) B16428743
theorem B1441607 : Blo 1441540 1441607 := bstep (se 1 (by rfl) ⟨1081205, by rfl⟩ : syracuseStep 1441607 = 2162411) B2162411
theorem B1621831 : Blo 1441540 1621831 := bstep (se 1 (by rfl) ⟨1216373, by rfl⟩ : syracuseStep 1621831 = 2432747) B2432747
theorem B27737963 : Blo 1441540 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B2162555 : Blo 1441540 2162555 := bstep (se 1 (by rfl) ⟨1621916, by rfl⟩ : syracuseStep 2162555 = 3243833) B3243833
theorem B1441759 : Blo 1441540 1441759 := bstep (se 1 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 1441759 = 2162639) B2162639
theorem B2162879 : Blo 1441540 2162879 := bstep (se 1 (by rfl) ⟨1622159, by rfl⟩ : syracuseStep 2162879 = 3244319) B3244319
theorem B1441983 : Blo 1441540 1441983 := bstep (se 1 (by rfl) ⟨1081487, by rfl⟩ : syracuseStep 1441983 = 2162975) B2162975
theorem B1441999 : Blo 1441540 1441999 := bstep (se 1 (by rfl) ⟨1081499, by rfl⟩ : syracuseStep 1441999 = 2162999) B2162999
theorem B1442047 : Blo 1441540 1442047 := bstep (se 1 (by rfl) ⟨1081535, by rfl⟩ : syracuseStep 1442047 = 2163071) B2163071
theorem B1442095 : Blo 1441540 1442095 := bstep (se 1 (by rfl) ⟨1081571, by rfl⟩ : syracuseStep 1442095 = 2163143) B2163143
theorem B13869407 : Blo 1441540 13869407 := bstep (se 1 (by rfl) ⟨10402055, by rfl⟩ : syracuseStep 13869407 = 20804111) B20804111
theorem B3424727 : Blo 1441540 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B1442331 : Blo 1441540 1442331 := bstep (se 1 (by rfl) ⟨1081748, by rfl⟩ : syracuseStep 1442331 = 2163497) B2163497
theorem B1442335 : Blo 1441540 1442335 := bstep (se 1 (by rfl) ⟨1081751, by rfl⟩ : syracuseStep 1442335 = 2163503) B2163503
theorem B1540639 : Blo 1441540 1540639 := bstep (se 1 (by rfl) ⟨1155479, by rfl⟩ : syracuseStep 1540639 = 2310959) B2310959
theorem B2163305 : Blo 1441540 2163305 := bstep (se 2 (by rfl) ⟨811239, by rfl⟩ : syracuseStep 2163305 = 1622479) B1622479
theorem B2163311 : Blo 1441540 2163311 := bstep (se 1 (by rfl) ⟨1622483, by rfl⟩ : syracuseStep 2163311 = 3244967) B3244967
theorem B1442415 : Blo 1441540 1442415 := bstep (se 1 (by rfl) ⟨1081811, by rfl⟩ : syracuseStep 1442415 = 2163623) B2163623
theorem B1622695 : Blo 1441540 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B1442471 : Blo 1441540 1442471 := bstep (se 1 (by rfl) ⟨1081853, by rfl⟩ : syracuseStep 1442471 = 2163707) B2163707
theorem B1442511 : Blo 1441540 1442511 := bstep (se 1 (by rfl) ⟨1081883, by rfl⟩ : syracuseStep 1442511 = 2163767) B2163767
theorem B1442591 : Blo 1441540 1442591 := bstep (se 1 (by rfl) ⟨1081943, by rfl⟩ : syracuseStep 1442591 = 2163887) B2163887
theorem B4866857 : Blo 1441540 4866857 := bstep (se 2 (by rfl) ⟨1825071, by rfl⟩ : syracuseStep 4866857 = 3650143) B3650143
theorem B3244841 : Blo 1441540 3244841 := bstep (se 2 (by rfl) ⟨1216815, by rfl⟩ : syracuseStep 3244841 = 2433631) B2433631
theorem B2433847 : Blo 1441540 2433847 := bstep (se 1 (by rfl) ⟨1825385, by rfl⟩ : syracuseStep 2433847 = 3650771) B3650771
theorem B1622983 : Blo 1441540 1622983 := bstep (se 1 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 1622983 = 2434475) B2434475
theorem B1442863 : Blo 1441540 1442863 := bstep (se 1 (by rfl) ⟨1082147, by rfl⟩ : syracuseStep 1442863 = 2164295) B2164295
theorem B4867127 : Blo 1441540 4867127 := bstep (se 1 (by rfl) ⟨3650345, by rfl⟩ : syracuseStep 4867127 = 7300691) B7300691
theorem B3245111 : Blo 1441540 3245111 := bstep (se 1 (by rfl) ⟨2433833, by rfl⟩ : syracuseStep 3245111 = 4867667) B4867667
theorem B1442927 : Blo 1441540 1442927 := bstep (se 1 (by rfl) ⟨1082195, by rfl⟩ : syracuseStep 1442927 = 2164391) B2164391
theorem B3466361 : Blo 1441540 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B12657809 : Blo 1441540 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B1442983 : Blo 1441540 1442983 := bstep (se 1 (by rfl) ⟨1082237, by rfl⟩ : syracuseStep 1442983 = 2164475) B2164475
theorem B2737327 : Blo 1441540 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B1443007 : Blo 1441540 1443007 := bstep (se 1 (by rfl) ⟨1082255, by rfl⟩ : syracuseStep 1443007 = 2164511) B2164511
theorem B2163935 : Blo 1441540 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B1443039 : Blo 1441540 1443039 := bstep (se 1 (by rfl) ⟨1082279, by rfl⟩ : syracuseStep 1443039 = 2164559) B2164559
theorem B3245291 : Blo 1441540 3245291 := bstep (se 1 (by rfl) ⟨2433968, by rfl⟩ : syracuseStep 3245291 = 4867937) B4867937
theorem B2163947 : Blo 1441540 2163947 := bstep (se 1 (by rfl) ⟨1622960, by rfl⟩ : syracuseStep 2163947 = 3245921) B3245921
theorem B1623343 : Blo 1441540 1623343 := bstep (se 1 (by rfl) ⟨1217507, by rfl⟩ : syracuseStep 1623343 = 2435015) B2435015
theorem B1443119 : Blo 1441540 1443119 := bstep (se 1 (by rfl) ⟨1082339, by rfl⟩ : syracuseStep 1443119 = 2164679) B2164679
theorem B10405199 : Blo 1441540 10405199 := bstep (se 1 (by rfl) ⟨7803899, by rfl⟩ : syracuseStep 10405199 = 15607799) B15607799
theorem B2737577 : Blo 1441540 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B1443355 : Blo 1441540 1443355 := bstep (se 1 (by rfl) ⟨1082516, by rfl⟩ : syracuseStep 1443355 = 2165033) B2165033
theorem B1443359 : Blo 1441540 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B2164331 : Blo 1441540 2164331 := bstep (se 1 (by rfl) ⟨1623248, by rfl⟩ : syracuseStep 2164331 = 3246497) B3246497
theorem B4384381 : Blo 1441540 4384381 := bstep (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) B1644143
theorem B23406245 : Blo 1441540 23406245 := bstep (se 4 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 23406245 = 4388671) B4388671
theorem B3245759 : Blo 1441540 3245759 := bstep (se 1 (by rfl) ⟨2434319, by rfl⟩ : syracuseStep 3245759 = 4868639) B4868639
theorem B2164415 : Blo 1441540 2164415 := bstep (se 1 (by rfl) ⟨1623311, by rfl⟩ : syracuseStep 2164415 = 3246623) B3246623
theorem B1443519 : Blo 1441540 1443519 := bstep (se 1 (by rfl) ⟨1082639, by rfl⟩ : syracuseStep 1443519 = 2165279) B2165279
theorem B1623847 : Blo 1441540 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B4106047 : Blo 1441540 4106047 := bstep (se 1 (by rfl) ⟨3079535, by rfl⟩ : syracuseStep 4106047 = 6159071) B6159071
theorem B6580075 : Blo 1441540 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B2164601 : Blo 1441540 2164601 := bstep (se 2 (by rfl) ⟨811725, by rfl⟩ : syracuseStep 2164601 = 1623451) B1623451
theorem B3467227 : Blo 1441540 3467227 := bstep (se 1 (by rfl) ⟨2600420, by rfl⟩ : syracuseStep 3467227 = 5200841) B5200841
theorem B4106207 : Blo 1441540 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B6580217 : Blo 1441540 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B9242657 : Blo 1441540 9242657 := bstep (se 2 (by rfl) ⟨3465996, by rfl⟩ : syracuseStep 9242657 = 6931993) B6931993
theorem B13338847 : Blo 1441540 13338847 := bstep (se 1 (by rfl) ⟨10004135, by rfl⟩ : syracuseStep 13338847 = 20008271) B20008271
theorem B11692295 : Blo 1441540 11692295 := bstep (se 1 (by rfl) ⟨8769221, by rfl⟩ : syracuseStep 11692295 = 17538443) B17538443
theorem B13863257 : Blo 1441540 13863257 := bstep (se 2 (by rfl) ⟨5198721, by rfl⟩ : syracuseStep 13863257 = 10397443) B10397443
theorem B5474699 : Blo 1441540 5474699 := bstep (se 1 (by rfl) ⟨4106024, by rfl⟩ : syracuseStep 5474699 = 8212049) B8212049
theorem B7023083 : Blo 1441540 7023083 := bstep (se 1 (by rfl) ⟨5267312, by rfl⟩ : syracuseStep 7023083 = 10534625) B10534625
theorem B2435575 : Blo 1441540 2435575 := bstep (se 1 (by rfl) ⟨1826681, by rfl⟩ : syracuseStep 2435575 = 3653363) B3653363
theorem B7301663 : Blo 1441540 7301663 := bstep (se 1 (by rfl) ⟨5476247, by rfl⟩ : syracuseStep 7301663 = 10952495) B10952495
theorem B18491975 : Blo 1441540 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B5474911 : Blo 1441540 5474911 := bstep (se 1 (by rfl) ⟨4106183, by rfl⟩ : syracuseStep 5474911 = 8212367) B8212367
theorem B3246695 : Blo 1441540 3246695 := bstep (se 1 (by rfl) ⟨2435021, by rfl⟩ : syracuseStep 3246695 = 4870043) B4870043
theorem B2739035 : Blo 1441540 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B13872059 : Blo 1441540 13872059 := bstep (se 1 (by rfl) ⟨10404044, by rfl⟩ : syracuseStep 13872059 = 20808089) B20808089
theorem B3247073 : Blo 1441540 3247073 := bstep (se 2 (by rfl) ⟨1217652, by rfl⟩ : syracuseStep 3247073 = 2435305) B2435305
theorem B13864061 : Blo 1441540 13864061 := bstep (se 3 (by rfl) ⟨2599511, by rfl⟩ : syracuseStep 13864061 = 5199023) B5199023
theorem B3247451 : Blo 1441540 3247451 := bstep (se 1 (by rfl) ⟨2435588, by rfl⟩ : syracuseStep 3247451 = 4871177) B4871177
theorem B3247487 : Blo 1441540 3247487 := bstep (se 1 (by rfl) ⟨2435615, by rfl⟩ : syracuseStep 3247487 = 4871231) B4871231
theorem B6008327 : Blo 1441540 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B70192655 : Blo 1441540 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B10948121 : Blo 1441540 10948121 := bstep (se 2 (by rfl) ⟨4105545, by rfl⟩ : syracuseStep 10948121 = 8211091) B8211091
theorem B10956383 : Blo 1441540 10956383 := bstep (se 1 (by rfl) ⟨8217287, by rfl⟩ : syracuseStep 10956383 = 16434575) B16434575
theorem B19738507 : Blo 1441540 19738507 := bstep (se 1 (by rfl) ⟨14803880, by rfl⟩ : syracuseStep 19738507 = 29607761) B29607761
theorem B6934567 : Blo 1441540 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B9245117 : Blo 1441540 9245117 := bstep (se 3 (by rfl) ⟨1733459, by rfl⟩ : syracuseStep 9245117 = 3466919) B3466919
theorem B62419409 : Blo 1441540 62419409 := bstep (se 2 (by rfl) ⟨23407278, by rfl⟩ : syracuseStep 62419409 = 46814557) B46814557
theorem B4108907 : Blo 1441540 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B7303931 : Blo 1441540 7303931 := bstep (se 1 (by rfl) ⟨5477948, by rfl⟩ : syracuseStep 7303931 = 10955897) B10955897
theorem B33305413 : Blo 1441540 33305413 := bstep (se 4 (by rfl) ⟨3122382, by rfl⟩ : syracuseStep 33305413 = 6244765) B6244765
theorem B2052955 : Blo 1441540 2052955 := bstep (se 1 (by rfl) ⟨1539716, by rfl⟩ : syracuseStep 2052955 = 3079433) B3079433
theorem B6165821 : Blo 1441540 6165821 := bstep (se 3 (by rfl) ⟨1156091, by rfl⟩ : syracuseStep 6165821 = 2312183) B2312183
theorem B31200713 : Blo 1441540 31200713 := bstep (se 2 (by rfl) ⟨11700267, by rfl⟩ : syracuseStep 31200713 = 23400535) B23400535
theorem B4871663 : Blo 1441540 4871663 := bstep (se 1 (by rfl) ⟨3653747, by rfl⟩ : syracuseStep 4871663 = 7307495) B7307495
theorem B6936299 : Blo 1441540 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B5478131 : Blo 1441540 5478131 := bstep (se 1 (by rfl) ⟨4108598, by rfl⟩ : syracuseStep 5478131 = 8217197) B8217197
theorem B35092237 : Blo 1441540 35092237 := bstep (se 3 (by rfl) ⟨6579794, by rfl⟩ : syracuseStep 35092237 = 13159589) B13159589
theorem B1562491 : Blo 1441540 1562491 := bstep (se 1 (by rfl) ⟨1171868, by rfl⟩ : syracuseStep 1562491 = 2343737) B2343737
theorem B13866947 : Blo 1441540 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B9247115 : Blo 1441540 9247115 := bstep (se 1 (by rfl) ⟨6935336, by rfl⟩ : syracuseStep 9247115 = 13870673) B13870673
theorem B1825183 : Blo 1441540 1825183 := bstep (se 1 (by rfl) ⟨1368887, by rfl⟩ : syracuseStep 1825183 = 2737775) B2737775
theorem B7305875 : Blo 1441540 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B2054983 : Blo 1441540 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B12319613 : Blo 1441540 12319613 := bstep (se 3 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 12319613 = 4619855) B4619855
theorem B168532883 : Blo 1441540 168532883 := bstep (se 1 (by rfl) ⟨126399662, by rfl⟩ : syracuseStep 168532883 = 252799325) B252799325
theorem B3464171 : Blo 1441540 3464171 := bstep (se 1 (by rfl) ⟨2598128, by rfl⟩ : syracuseStep 3464171 = 5196257) B5196257
theorem B5479559 : Blo 1441540 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B3079399 : Blo 1441540 3079399 := bstep (se 1 (by rfl) ⟨2309549, by rfl⟩ : syracuseStep 3079399 = 4619099) B4619099
theorem B7306685 : Blo 1441540 7306685 := bstep (se 3 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 7306685 = 2740007) B2740007
theorem B2162399 : Blo 1441540 2162399 := bstep (se 1 (by rfl) ⟨1621799, by rfl⟩ : syracuseStep 2162399 = 3243599) B3243599
theorem B3243743 : Blo 1441540 3243743 := bstep (se 1 (by rfl) ⟨2432807, by rfl⟩ : syracuseStep 3243743 = 4865615) B4865615
theorem B1539815 : Blo 1441540 1539815 := bstep (se 1 (by rfl) ⟨1154861, by rfl⟩ : syracuseStep 1539815 = 2309723) B2309723
theorem B2162441 : Blo 1441540 2162441 := bstep (se 2 (by rfl) ⟨810915, by rfl⟩ : syracuseStep 2162441 = 1621831) B1621831
theorem B1441567 : Blo 1441540 1441567 := bstep (se 1 (by rfl) ⟨1081175, by rfl⟩ : syracuseStep 1441567 = 2162351) B2162351
theorem B3243815 : Blo 1441540 3243815 := bstep (se 1 (by rfl) ⟨2432861, by rfl⟩ : syracuseStep 3243815 = 4865723) B4865723
theorem B1441647 : Blo 1441540 1441647 := bstep (se 1 (by rfl) ⟨1081235, by rfl⟩ : syracuseStep 1441647 = 2162471) B2162471
theorem B18472859 : Blo 1441540 18472859 := bstep (se 1 (by rfl) ⟨13854644, by rfl⟩ : syracuseStep 18472859 = 27709289) B27709289
theorem B1441703 : Blo 1441540 1441703 := bstep (se 1 (by rfl) ⟨1081277, by rfl⟩ : syracuseStep 1441703 = 2162555) B2162555
theorem B59998157 : Blo 1441540 59998157 := bstep (se 3 (by rfl) ⟨11249654, by rfl⟩ : syracuseStep 59998157 = 22499309) B22499309
theorem B1441919 : Blo 1441540 1441919 := bstep (se 1 (by rfl) ⟨1081439, by rfl⟩ : syracuseStep 1441919 = 2162879) B2162879
theorem B8216741 : Blo 1441540 8216741 := bstep (se 4 (by rfl) ⟨770319, by rfl⟩ : syracuseStep 8216741 = 1540639) B1540639
theorem B17785129 : Blo 1441540 17785129 := bstep (se 2 (by rfl) ⟨6669423, by rfl⟩ : syracuseStep 17785129 = 13338847) B13338847
theorem B1442203 : Blo 1441540 1442203 := bstep (se 1 (by rfl) ⟨1081652, by rfl⟩ : syracuseStep 1442203 = 2163305) B2163305
theorem B1442207 : Blo 1441540 1442207 := bstep (se 1 (by rfl) ⟨1081655, by rfl⟩ : syracuseStep 1442207 = 2163311) B2163311
theorem B3244571 : Blo 1441540 3244571 := bstep (se 1 (by rfl) ⟨2433428, by rfl⟩ : syracuseStep 3244571 = 4866857) B4866857
theorem B2163227 : Blo 1441540 2163227 := bstep (se 1 (by rfl) ⟨1622420, by rfl⟩ : syracuseStep 2163227 = 3244841) B3244841
theorem B2433577 : Blo 1441540 2433577 := bstep (se 2 (by rfl) ⟨912591, by rfl⟩ : syracuseStep 2433577 = 1825183) B1825183
theorem B3244751 : Blo 1441540 3244751 := bstep (se 1 (by rfl) ⟨2433563, by rfl⟩ : syracuseStep 3244751 = 4867127) B4867127
theorem B2163407 : Blo 1441540 2163407 := bstep (se 1 (by rfl) ⟨1622555, by rfl⟩ : syracuseStep 2163407 = 3245111) B3245111
theorem B8438539 : Blo 1441540 8438539 := bstep (se 1 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 8438539 = 12657809) B12657809
theorem B7299881 : Blo 1441540 7299881 := bstep (se 2 (by rfl) ⟨2737455, by rfl⟩ : syracuseStep 7299881 = 5474911) B5474911
theorem B1442623 : Blo 1441540 1442623 := bstep (se 1 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 1442623 = 2163935) B2163935
theorem B2163527 : Blo 1441540 2163527 := bstep (se 1 (by rfl) ⟨1622645, by rfl⟩ : syracuseStep 2163527 = 3245291) B3245291
theorem B1442631 : Blo 1441540 1442631 := bstep (se 1 (by rfl) ⟨1081973, by rfl⟩ : syracuseStep 1442631 = 2163947) B2163947
theorem B2163593 : Blo 1441540 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B20800475 : Blo 1441540 20800475 := bstep (se 1 (by rfl) ⟨15600356, by rfl⟩ : syracuseStep 20800475 = 31200713) B31200713
theorem B1442887 : Blo 1441540 1442887 := bstep (se 1 (by rfl) ⟨1082165, by rfl⟩ : syracuseStep 1442887 = 2164331) B2164331
theorem B3245129 : Blo 1441540 3245129 := bstep (se 2 (by rfl) ⟨1216923, by rfl⟩ : syracuseStep 3245129 = 2433847) B2433847
theorem B7300205 : Blo 1441540 7300205 := bstep (se 3 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 7300205 = 2737577) B2737577
theorem B2163839 : Blo 1441540 2163839 := bstep (se 1 (by rfl) ⟨1622879, by rfl⟩ : syracuseStep 2163839 = 3245759) B3245759
theorem B1442943 : Blo 1441540 1442943 := bstep (se 1 (by rfl) ⟨1082207, by rfl⟩ : syracuseStep 1442943 = 2164415) B2164415
theorem B1443067 : Blo 1441540 1443067 := bstep (se 1 (by rfl) ⟨1082300, by rfl⟩ : syracuseStep 1443067 = 2164601) B2164601
theorem B2163977 : Blo 1441540 2163977 := bstep (se 2 (by rfl) ⟨811491, by rfl⟩ : syracuseStep 2163977 = 1622983) B1622983
theorem B18728221 : Blo 1441540 18728221 := bstep (se 3 (by rfl) ⟨3511541, by rfl⟩ : syracuseStep 18728221 = 7023083) B7023083
theorem B2737471 : Blo 1441540 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B6161771 : Blo 1441540 6161771 := bstep (se 1 (by rfl) ⟨4621328, by rfl⟩ : syracuseStep 6161771 = 9242657) B9242657
theorem B9242171 : Blo 1441540 9242171 := bstep (se 1 (by rfl) ⟨6931628, by rfl⟩ : syracuseStep 9242171 = 13863257) B13863257
theorem B4105865 : Blo 1441540 4105865 := bstep (se 2 (by rfl) ⟨1539699, by rfl⟩ : syracuseStep 4105865 = 3079399) B3079399
theorem B4867775 : Blo 1441540 4867775 := bstep (se 1 (by rfl) ⟨3650831, by rfl⟩ : syracuseStep 4867775 = 7301663) B7301663
theorem B2164457 : Blo 1441540 2164457 := bstep (se 2 (by rfl) ⟨811671, by rfl⟩ : syracuseStep 2164457 = 1623343) B1623343
theorem B2164463 : Blo 1441540 2164463 := bstep (se 1 (by rfl) ⟨1623347, by rfl⟩ : syracuseStep 2164463 = 3246695) B3246695
theorem B112355255 : Blo 1441540 112355255 := bstep (se 1 (by rfl) ⟨84266441, by rfl⟩ : syracuseStep 112355255 = 168532883) B168532883
theorem B4106173 : Blo 1441540 4106173 := bstep (se 3 (by rfl) ⟨769907, by rfl⟩ : syracuseStep 4106173 = 1539815) B1539815
theorem B2164715 : Blo 1441540 2164715 := bstep (se 1 (by rfl) ⟨1623536, by rfl⟩ : syracuseStep 2164715 = 3247073) B3247073
theorem B9242707 : Blo 1441540 9242707 := bstep (se 1 (by rfl) ⟨6932030, by rfl⟩ : syracuseStep 9242707 = 13864061) B13864061
theorem B2164967 : Blo 1441540 2164967 := bstep (se 1 (by rfl) ⟨1623725, by rfl⟩ : syracuseStep 2164967 = 3247451) B3247451
theorem B2164991 : Blo 1441540 2164991 := bstep (se 1 (by rfl) ⟨1623743, by rfl⟩ : syracuseStep 2164991 = 3247487) B3247487
theorem B46795103 : Blo 1441540 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B2165129 : Blo 1441540 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B5474729 : Blo 1441540 5474729 := bstep (se 2 (by rfl) ⟨2053023, by rfl⟩ : syracuseStep 5474729 = 4106047) B4106047
theorem B2083321 : Blo 1441540 2083321 := bstep (se 2 (by rfl) ⟨781245, by rfl⟩ : syracuseStep 2083321 = 1562491) B1562491
theorem B12315239 : Blo 1441540 12315239 := bstep (se 1 (by rfl) ⟨9236429, by rfl⟩ : syracuseStep 12315239 = 18472859) B18472859
theorem B4622969 : Blo 1441540 4622969 := bstep (se 2 (by rfl) ⟨1733613, by rfl⟩ : syracuseStep 4622969 = 3467227) B3467227
theorem B6163411 : Blo 1441540 6163411 := bstep (se 1 (by rfl) ⟨4622558, by rfl⟩ : syracuseStep 6163411 = 9245117) B9245117
theorem B9243629 : Blo 1441540 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B2739271 : Blo 1441540 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B4869287 : Blo 1441540 4869287 := bstep (se 1 (by rfl) ⟨3651965, by rfl⟩ : syracuseStep 4869287 = 7303931) B7303931
theorem B3247433 : Blo 1441540 3247433 := bstep (se 2 (by rfl) ⟨1217787, by rfl⟩ : syracuseStep 3247433 = 2435575) B2435575
theorem B3247775 : Blo 1441540 3247775 := bstep (se 1 (by rfl) ⟨2435831, by rfl⟩ : syracuseStep 3247775 = 4871663) B4871663
theorem B2739977 : Blo 1441540 2739977 := bstep (se 2 (by rfl) ⟨1027491, by rfl⟩ : syracuseStep 2739977 = 2054983) B2054983
theorem B4624199 : Blo 1441540 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B9244631 : Blo 1441540 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B4386811 : Blo 1441540 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B7794863 : Blo 1441540 7794863 := bstep (se 1 (by rfl) ⟨5846147, by rfl⟩ : syracuseStep 7794863 = 11692295) B11692295
theorem B3649769 : Blo 1441540 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B3649799 : Blo 1441540 3649799 := bstep (se 1 (by rfl) ⟨2737349, by rfl⟩ : syracuseStep 3649799 = 5474699) B5474699
theorem B6164743 : Blo 1441540 6164743 := bstep (se 1 (by rfl) ⟨4623557, by rfl⟩ : syracuseStep 6164743 = 9247115) B9247115
theorem B4870583 : Blo 1441540 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B10949093 : Blo 1441540 10949093 := bstep (se 4 (by rfl) ⟨1026477, by rfl⟩ : syracuseStep 10949093 = 2052955) B2052955
theorem B8213075 : Blo 1441540 8213075 := bstep (se 1 (by rfl) ⟨6159806, by rfl⟩ : syracuseStep 8213075 = 12319613) B12319613
theorem B5845841 : Blo 1441540 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B7304093 : Blo 1441540 7304093 := bstep (se 3 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 7304093 = 2739035) B2739035
theorem B4871123 : Blo 1441540 4871123 := bstep (se 1 (by rfl) ⟨3653342, by rfl⟩ : syracuseStep 4871123 = 7306685) B7306685
theorem B46789649 : Blo 1441540 46789649 := bstep (se 2 (by rfl) ⟨17546118, by rfl⟩ : syracuseStep 46789649 = 35092237) B35092237
theorem B7304255 : Blo 1441540 7304255 := bstep (se 1 (by rfl) ⟨5478191, by rfl⟩ : syracuseStep 7304255 = 10956383) B10956383
theorem B26318009 : Blo 1441540 26318009 := bstep (se 2 (by rfl) ⟨9869253, by rfl⟩ : syracuseStep 26318009 = 19738507) B19738507
theorem B39998771 : Blo 1441540 39998771 := bstep (se 1 (by rfl) ⟨29999078, by rfl⟩ : syracuseStep 39998771 = 59998157) B59998157
theorem B9246089 : Blo 1441540 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B9246271 : Blo 1441540 9246271 := bstep (se 1 (by rfl) ⟨6934703, by rfl⟩ : syracuseStep 9246271 = 13869407) B13869407
theorem B41612939 : Blo 1441540 41612939 := bstep (se 1 (by rfl) ⟨31209704, by rfl⟩ : syracuseStep 41612939 = 62419409) B62419409
theorem B4110547 : Blo 1441540 4110547 := bstep (se 1 (by rfl) ⟨3082910, by rfl⟩ : syracuseStep 4110547 = 6165821) B6165821
theorem B6936799 : Blo 1441540 6936799 := bstep (se 1 (by rfl) ⟨5202599, by rfl⟩ : syracuseStep 6936799 = 10405199) B10405199
theorem B44407217 : Blo 1441540 44407217 := bstep (se 2 (by rfl) ⟨16652706, by rfl⟩ : syracuseStep 44407217 = 33305413) B33305413
theorem B15604163 : Blo 1441540 15604163 := bstep (se 1 (by rfl) ⟨11703122, by rfl⟩ : syracuseStep 15604163 = 23406245) B23406245
theorem B3652087 : Blo 1441540 3652087 := bstep (se 1 (by rfl) ⟨2739065, by rfl⟩ : syracuseStep 3652087 = 5478131) B5478131
theorem B9132605 : Blo 1441540 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B12327983 : Blo 1441540 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B9248039 : Blo 1441540 9248039 := bstep (se 1 (by rfl) ⟨6936029, by rfl⟩ : syracuseStep 9248039 = 13872059) B13872059
theorem B2309447 : Blo 1441540 2309447 := bstep (se 1 (by rfl) ⟨1732085, by rfl⟩ : syracuseStep 2309447 = 3464171) B3464171
theorem B3653039 : Blo 1441540 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B4005551 : Blo 1441540 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B7298747 : Blo 1441540 7298747 := bstep (se 1 (by rfl) ⟨5474060, by rfl⟩ : syracuseStep 7298747 = 10948121) B10948121
theorem B8773433 : Blo 1441540 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B1441599 : Blo 1441540 1441599 := bstep (se 1 (by rfl) ⟨1081199, by rfl⟩ : syracuseStep 1441599 = 2162399) B2162399
theorem B2162495 : Blo 1441540 2162495 := bstep (se 1 (by rfl) ⟨1621871, by rfl⟩ : syracuseStep 2162495 = 3243743) B3243743
theorem B1441627 : Blo 1441540 1441627 := bstep (se 1 (by rfl) ⟨1081220, by rfl⟩ : syracuseStep 1441627 = 2162441) B2162441
theorem B2162543 : Blo 1441540 2162543 := bstep (se 1 (by rfl) ⟨1621907, by rfl⟩ : syracuseStep 2162543 = 3243815) B3243815
theorem B2433179 : Blo 1441540 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B2433199 : Blo 1441540 2433199 := bstep (se 1 (by rfl) ⟨1824899, by rfl⟩ : syracuseStep 2433199 = 3649799) B3649799
theorem B5480729 : Blo 1441540 5480729 := bstep (se 2 (by rfl) ⟨2055273, by rfl⟩ : syracuseStep 5480729 = 4110547) B4110547
theorem B9249065 : Blo 1441540 9249065 := bstep (se 2 (by rfl) ⟨3468399, by rfl⟩ : syracuseStep 9249065 = 6936799) B6936799
theorem B7299395 : Blo 1441540 7299395 := bstep (se 1 (by rfl) ⟨5474546, by rfl⟩ : syracuseStep 7299395 = 10949093) B10949093
theorem B2163047 : Blo 1441540 2163047 := bstep (se 1 (by rfl) ⟨1622285, by rfl⟩ : syracuseStep 2163047 = 3244571) B3244571
theorem B1442151 : Blo 1441540 1442151 := bstep (se 1 (by rfl) ⟨1081613, by rfl⟩ : syracuseStep 1442151 = 2163227) B2163227
theorem B1442271 : Blo 1441540 1442271 := bstep (se 1 (by rfl) ⟨1081703, by rfl⟩ : syracuseStep 1442271 = 2163407) B2163407
theorem B2163167 : Blo 1441540 2163167 := bstep (se 1 (by rfl) ⟨1622375, by rfl⟩ : syracuseStep 2163167 = 3244751) B3244751
theorem B4866587 : Blo 1441540 4866587 := bstep (se 1 (by rfl) ⟨3649940, by rfl⟩ : syracuseStep 4866587 = 7299881) B7299881
theorem B1442351 : Blo 1441540 1442351 := bstep (se 1 (by rfl) ⟨1081763, by rfl⟩ : syracuseStep 1442351 = 2163527) B2163527
theorem B1442395 : Blo 1441540 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B2777761 : Blo 1441540 2777761 := bstep (se 2 (by rfl) ⟨1041660, by rfl⟩ : syracuseStep 2777761 = 2083321) B2083321
theorem B2163419 : Blo 1441540 2163419 := bstep (se 1 (by rfl) ⟨1622564, by rfl⟩ : syracuseStep 2163419 = 3245129) B3245129
theorem B3244769 : Blo 1441540 3244769 := bstep (se 2 (by rfl) ⟨1216788, by rfl⟩ : syracuseStep 3244769 = 2433577) B2433577
theorem B4866803 : Blo 1441540 4866803 := bstep (se 1 (by rfl) ⟨3650102, by rfl⟩ : syracuseStep 4866803 = 7300205) B7300205
theorem B1442559 : Blo 1441540 1442559 := bstep (se 1 (by rfl) ⟨1081919, by rfl⟩ : syracuseStep 1442559 = 2163839) B2163839
theorem B1442651 : Blo 1441540 1442651 := bstep (se 1 (by rfl) ⟨1081988, by rfl⟩ : syracuseStep 1442651 = 2163977) B2163977
theorem B26665847 : Blo 1441540 26665847 := bstep (se 1 (by rfl) ⟨19999385, by rfl⟩ : syracuseStep 26665847 = 39998771) B39998771
theorem B6161447 : Blo 1441540 6161447 := bstep (se 1 (by rfl) ⟨4621085, by rfl⟩ : syracuseStep 6161447 = 9242171) B9242171
theorem B2737243 : Blo 1441540 2737243 := bstep (se 1 (by rfl) ⟨2052932, by rfl⟩ : syracuseStep 2737243 = 4105865) B4105865
theorem B3245183 : Blo 1441540 3245183 := bstep (se 1 (by rfl) ⟨2433887, by rfl⟩ : syracuseStep 3245183 = 4867775) B4867775
theorem B1442971 : Blo 1441540 1442971 := bstep (se 1 (by rfl) ⟨1082228, by rfl⟩ : syracuseStep 1442971 = 2164457) B2164457
theorem B1442975 : Blo 1441540 1442975 := bstep (se 1 (by rfl) ⟨1082231, by rfl⟩ : syracuseStep 1442975 = 2164463) B2164463
theorem B8217881 : Blo 1441540 8217881 := bstep (se 2 (by rfl) ⟨3081705, by rfl⟩ : syracuseStep 8217881 = 6163411) B6163411
theorem B1443143 : Blo 1441540 1443143 := bstep (se 1 (by rfl) ⟨1082357, by rfl⟩ : syracuseStep 1443143 = 2164715) B2164715
theorem B1443311 : Blo 1441540 1443311 := bstep (se 1 (by rfl) ⟨1082483, by rfl⟩ : syracuseStep 1443311 = 2164967) B2164967
theorem B1443327 : Blo 1441540 1443327 := bstep (se 1 (by rfl) ⟨1082495, by rfl⟩ : syracuseStep 1443327 = 2164991) B2164991
theorem B31196735 : Blo 1441540 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B1443419 : Blo 1441540 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B24970961 : Blo 1441540 24970961 := bstep (se 2 (by rfl) ⟨9364110, by rfl⟩ : syracuseStep 24970961 = 18728221) B18728221
theorem B6088403 : Blo 1441540 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B8210159 : Blo 1441540 8210159 := bstep (se 1 (by rfl) ⟨6157619, by rfl⟩ : syracuseStep 8210159 = 12315239) B12315239
theorem B3081979 : Blo 1441540 3081979 := bstep (se 1 (by rfl) ⟨2311484, by rfl⟩ : syracuseStep 3081979 = 4622969) B4622969
theorem B6162419 : Blo 1441540 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B8218655 : Blo 1441540 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B3246191 : Blo 1441540 3246191 := bstep (se 1 (by rfl) ⟨2434643, by rfl⟩ : syracuseStep 3246191 = 4869287) B4869287
theorem B2164955 : Blo 1441540 2164955 := bstep (se 1 (by rfl) ⟨1623716, by rfl⟩ : syracuseStep 2164955 = 3247433) B3247433
theorem B2435359 : Blo 1441540 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B2165183 : Blo 1441540 2165183 := bstep (se 1 (by rfl) ⟨1623887, by rfl⟩ : syracuseStep 2165183 = 3247775) B3247775
theorem B5849081 : Blo 1441540 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B3082799 : Blo 1441540 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B5474897 : Blo 1441540 5474897 := bstep (se 2 (by rfl) ⟨2053086, by rfl⟩ : syracuseStep 5474897 = 4106173) B4106173
theorem B6163087 : Blo 1441540 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B12323609 : Blo 1441540 12323609 := bstep (se 2 (by rfl) ⟨4621353, by rfl⟩ : syracuseStep 12323609 = 9242707) B9242707
theorem B5196575 : Blo 1441540 5196575 := bstep (se 1 (by rfl) ⟨3897431, by rfl⟩ : syracuseStep 5196575 = 7794863) B7794863
theorem B3247055 : Blo 1441540 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B8219657 : Blo 1441540 8219657 := bstep (se 2 (by rfl) ⟨3082371, by rfl⟩ : syracuseStep 8219657 = 6164743) B6164743
theorem B5475383 : Blo 1441540 5475383 := bstep (se 1 (by rfl) ⟨4106537, by rfl⟩ : syracuseStep 5475383 = 8213075) B8213075
theorem B4869395 : Blo 1441540 4869395 := bstep (se 1 (by rfl) ⟨3652046, by rfl⟩ : syracuseStep 4869395 = 7304093) B7304093
theorem B3247415 : Blo 1441540 3247415 := bstep (se 1 (by rfl) ⟨2435561, by rfl⟩ : syracuseStep 3247415 = 4871123) B4871123
theorem B4869449 : Blo 1441540 4869449 := bstep (se 2 (by rfl) ⟨1826043, by rfl⟩ : syracuseStep 4869449 = 3652087) B3652087
theorem B4869503 : Blo 1441540 4869503 := bstep (se 1 (by rfl) ⟨3652127, by rfl⟩ : syracuseStep 4869503 = 7304255) B7304255
theorem B4107847 : Blo 1441540 4107847 := bstep (se 1 (by rfl) ⟨3080885, by rfl⟩ : syracuseStep 4107847 = 6161771) B6161771
theorem B11251385 : Blo 1441540 11251385 := bstep (se 2 (by rfl) ⟨4219269, by rfl⟩ : syracuseStep 11251385 = 8438539) B8438539
theorem B27741959 : Blo 1441540 27741959 := bstep (se 1 (by rfl) ⟨20806469, by rfl⟩ : syracuseStep 27741959 = 41612939) B41612939
theorem B74903503 : Blo 1441540 74903503 := bstep (se 1 (by rfl) ⟨56177627, by rfl⟩ : syracuseStep 74903503 = 112355255) B112355255
theorem B3649819 : Blo 1441540 3649819 := bstep (se 1 (by rfl) ⟨2737364, by rfl⟩ : syracuseStep 3649819 = 5474729) B5474729
theorem B3649961 : Blo 1441540 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B6165359 : Blo 1441540 6165359 := bstep (se 1 (by rfl) ⟨4624019, by rfl⟩ : syracuseStep 6165359 = 9248039) B9248039
theorem B5477827 : Blo 1441540 5477827 := bstep (se 1 (by rfl) ⟨4108370, by rfl⟩ : syracuseStep 5477827 = 8216741) B8216741
theorem B23713505 : Blo 1441540 23713505 := bstep (se 2 (by rfl) ⟨8892564, by rfl⟩ : syracuseStep 23713505 = 17785129) B17785129
theorem B3897227 : Blo 1441540 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B13866983 : Blo 1441540 13866983 := bstep (se 1 (by rfl) ⟨10400237, by rfl⟩ : syracuseStep 13866983 = 20800475) B20800475
theorem B31193099 : Blo 1441540 31193099 := bstep (se 1 (by rfl) ⟨23394824, by rfl⟩ : syracuseStep 31193099 = 46789649) B46789649
theorem B17545339 : Blo 1441540 17545339 := bstep (se 1 (by rfl) ⟨13159004, by rfl⟩ : syracuseStep 17545339 = 26318009) B26318009
theorem B24656237 : Blo 1441540 24656237 := bstep (se 3 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 24656237 = 9246089) B9246089
theorem B3652361 : Blo 1441540 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B29604811 : Blo 1441540 29604811 := bstep (se 1 (by rfl) ⟨22203608, by rfl⟩ : syracuseStep 29604811 = 44407217) B44407217
theorem B10402775 : Blo 1441540 10402775 := bstep (se 1 (by rfl) ⟨7802081, by rfl⟩ : syracuseStep 10402775 = 15604163) B15604163
theorem B10681469 : Blo 1441540 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B12328361 : Blo 1441540 12328361 := bstep (se 2 (by rfl) ⟨4623135, by rfl⟩ : syracuseStep 12328361 = 9246271) B9246271
theorem B1539631 : Blo 1441540 1539631 := bstep (se 1 (by rfl) ⟨1154723, by rfl⟩ : syracuseStep 1539631 = 2309447) B2309447
theorem B4865831 : Blo 1441540 4865831 := bstep (se 1 (by rfl) ⟨3649373, by rfl⟩ : syracuseStep 4865831 = 7298747) B7298747
theorem B1826651 : Blo 1441540 1826651 := bstep (se 1 (by rfl) ⟨1369988, by rfl⟩ : syracuseStep 1826651 = 2739977) B2739977
theorem B5848955 : Blo 1441540 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B1441663 : Blo 1441540 1441663 := bstep (se 1 (by rfl) ⟨1081247, by rfl⟩ : syracuseStep 1441663 = 2162495) B2162495
theorem B1441695 : Blo 1441540 1441695 := bstep (se 1 (by rfl) ⟨1081271, by rfl⟩ : syracuseStep 1441695 = 2162543) B2162543
theorem B1622119 : Blo 1441540 1622119 := bstep (se 1 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 1622119 = 2433179) B2433179
theorem B3653819 : Blo 1441540 3653819 := bstep (se 1 (by rfl) ⟨2740364, by rfl⟩ : syracuseStep 3653819 = 5480729) B5480729
theorem B4866263 : Blo 1441540 4866263 := bstep (se 1 (by rfl) ⟨3649697, by rfl⟩ : syracuseStep 4866263 = 7299395) B7299395
theorem B3244265 : Blo 1441540 3244265 := bstep (se 2 (by rfl) ⟨1216599, by rfl⟩ : syracuseStep 3244265 = 2433199) B2433199
theorem B1442031 : Blo 1441540 1442031 := bstep (se 1 (by rfl) ⟨1081523, by rfl⟩ : syracuseStep 1442031 = 2163047) B2163047
theorem B2433307 : Blo 1441540 2433307 := bstep (se 1 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 2433307 = 3649961) B3649961
theorem B1442111 : Blo 1441540 1442111 := bstep (se 1 (by rfl) ⟨1081583, by rfl⟩ : syracuseStep 1442111 = 2163167) B2163167
theorem B3244391 : Blo 1441540 3244391 := bstep (se 1 (by rfl) ⟨2433293, by rfl⟩ : syracuseStep 3244391 = 4866587) B4866587
theorem B4866425 : Blo 1441540 4866425 := bstep (se 2 (by rfl) ⟨1824909, by rfl⟩ : syracuseStep 4866425 = 3649819) B3649819
theorem B1442279 : Blo 1441540 1442279 := bstep (se 1 (by rfl) ⟨1081709, by rfl⟩ : syracuseStep 1442279 = 2163419) B2163419
theorem B2163179 : Blo 1441540 2163179 := bstep (se 1 (by rfl) ⟨1622384, by rfl⟩ : syracuseStep 2163179 = 3244769) B3244769
theorem B3244535 : Blo 1441540 3244535 := bstep (se 1 (by rfl) ⟨2433401, by rfl⟩ : syracuseStep 3244535 = 4866803) B4866803
theorem B17777231 : Blo 1441540 17777231 := bstep (se 1 (by rfl) ⟨13332923, by rfl⟩ : syracuseStep 17777231 = 26665847) B26665847
theorem B2163455 : Blo 1441540 2163455 := bstep (se 1 (by rfl) ⟨1622591, by rfl⟩ : syracuseStep 2163455 = 3245183) B3245183
theorem B8217449 : Blo 1441540 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B3703681 : Blo 1441540 3703681 := bstep (se 2 (by rfl) ⟨1388880, by rfl⟩ : syracuseStep 3703681 = 2777761) B2777761
theorem B5473439 : Blo 1441540 5473439 := bstep (se 1 (by rfl) ⟨4105079, by rfl⟩ : syracuseStep 5473439 = 8210159) B8210159
theorem B2598151 : Blo 1441540 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B2164127 : Blo 1441540 2164127 := bstep (se 1 (by rfl) ⟨1623095, by rfl⟩ : syracuseStep 2164127 = 3246191) B3246191
theorem B1443303 : Blo 1441540 1443303 := bstep (se 1 (by rfl) ⟨1082477, by rfl⟩ : syracuseStep 1443303 = 2164955) B2164955
theorem B1443455 : Blo 1441540 1443455 := bstep (se 1 (by rfl) ⟨1082591, by rfl⟩ : syracuseStep 1443455 = 2165183) B2165183
theorem B2434907 : Blo 1441540 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B2164703 : Blo 1441540 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B7120979 : Blo 1441540 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B3246263 : Blo 1441540 3246263 := bstep (se 1 (by rfl) ⟨2434697, by rfl⟩ : syracuseStep 3246263 = 4869395) B4869395
theorem B2164943 : Blo 1441540 2164943 := bstep (se 1 (by rfl) ⟨1623707, by rfl⟩ : syracuseStep 2164943 = 3247415) B3247415
theorem B3246299 : Blo 1441540 3246299 := bstep (se 1 (by rfl) ⟨2434724, by rfl⟩ : syracuseStep 3246299 = 4869449) B4869449
theorem B3246335 : Blo 1441540 3246335 := bstep (se 1 (by rfl) ⟨2434751, by rfl⟩ : syracuseStep 3246335 = 4869503) B4869503
theorem B8218907 : Blo 1441540 8218907 := bstep (se 1 (by rfl) ⟨6164180, by rfl⟩ : syracuseStep 8218907 = 12328361) B12328361
theorem B99871337 : Blo 1441540 99871337 := bstep (se 2 (by rfl) ⟨37451751, by rfl⟩ : syracuseStep 99871337 = 74903503) B74903503
theorem B8211365 : Blo 1441540 8211365 := bstep (se 4 (by rfl) ⟨769815, by rfl⟩ : syracuseStep 8211365 = 1539631) B1539631
theorem B3247145 : Blo 1441540 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B4107631 : Blo 1441540 4107631 := bstep (se 1 (by rfl) ⟨3080723, by rfl⟩ : syracuseStep 4107631 = 6161447) B6161447
theorem B39473081 : Blo 1441540 39473081 := bstep (se 2 (by rfl) ⟨14802405, by rfl⟩ : syracuseStep 39473081 = 29604811) B29604811
theorem B9244655 : Blo 1441540 9244655 := bstep (se 1 (by rfl) ⟨6933491, by rfl⟩ : syracuseStep 9244655 = 13866983) B13866983
theorem B20795399 : Blo 1441540 20795399 := bstep (se 1 (by rfl) ⟨15596549, by rfl⟩ : syracuseStep 20795399 = 31193099) B31193099
theorem B3649657 : Blo 1441540 3649657 := bstep (se 2 (by rfl) ⟨1368621, by rfl⟩ : syracuseStep 3649657 = 2737243) B2737243
theorem B8220797 : Blo 1441540 8220797 := bstep (se 3 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 8220797 = 3082799) B3082799
theorem B16437491 : Blo 1441540 16437491 := bstep (se 1 (by rfl) ⟨12328118, by rfl⟩ : syracuseStep 16437491 = 24656237) B24656237
theorem B3649931 : Blo 1441540 3649931 := bstep (se 1 (by rfl) ⟨2737448, by rfl⟩ : syracuseStep 3649931 = 5474897) B5474897
theorem B66589229 : Blo 1441540 66589229 := bstep (se 3 (by rfl) ⟨12485480, by rfl⟩ : syracuseStep 66589229 = 24970961) B24970961
theorem B7303769 : Blo 1441540 7303769 := bstep (se 2 (by rfl) ⟨2738913, by rfl⟩ : syracuseStep 7303769 = 5477827) B5477827
theorem B6935183 : Blo 1441540 6935183 := bstep (se 1 (by rfl) ⟨5201387, by rfl⟩ : syracuseStep 6935183 = 10402775) B10402775
theorem B3650255 : Blo 1441540 3650255 := bstep (se 1 (by rfl) ⟨2737691, by rfl⟩ : syracuseStep 3650255 = 5475383) B5475383
theorem B5477129 : Blo 1441540 5477129 := bstep (se 2 (by rfl) ⟨2053923, by rfl⟩ : syracuseStep 5477129 = 4107847) B4107847
theorem B4871069 : Blo 1441540 4871069 := bstep (se 3 (by rfl) ⟨913325, by rfl⟩ : syracuseStep 4871069 = 1826651) B1826651
theorem B4109305 : Blo 1441540 4109305 := bstep (se 2 (by rfl) ⟨1540989, by rfl⟩ : syracuseStep 4109305 = 3081979) B3081979
theorem B7500923 : Blo 1441540 7500923 := bstep (se 1 (by rfl) ⟨5625692, by rfl⟩ : syracuseStep 7500923 = 11251385) B11251385
theorem B18494639 : Blo 1441540 18494639 := bstep (se 1 (by rfl) ⟨13870979, by rfl⟩ : syracuseStep 18494639 = 27741959) B27741959
theorem B23393785 : Blo 1441540 23393785 := bstep (se 2 (by rfl) ⟨8772669, by rfl⟩ : syracuseStep 23393785 = 17545339) B17545339
theorem B6166043 : Blo 1441540 6166043 := bstep (se 1 (by rfl) ⟨4624532, by rfl⟩ : syracuseStep 6166043 = 9249065) B9249065
theorem B4110239 : Blo 1441540 4110239 := bstep (se 1 (by rfl) ⟨3082679, by rfl⟩ : syracuseStep 4110239 = 6165359) B6165359
theorem B5478587 : Blo 1441540 5478587 := bstep (se 1 (by rfl) ⟨4108940, by rfl⟩ : syracuseStep 5478587 = 8217881) B8217881
theorem B20797823 : Blo 1441540 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B15809003 : Blo 1441540 15809003 := bstep (se 1 (by rfl) ⟨11856752, by rfl⟩ : syracuseStep 15809003 = 23713505) B23713505
theorem B5479103 : Blo 1441540 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B3899387 : Blo 1441540 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B8215739 : Blo 1441540 8215739 := bstep (se 1 (by rfl) ⟨6161804, by rfl⟩ : syracuseStep 8215739 = 12323609) B12323609
theorem B3464383 : Blo 1441540 3464383 := bstep (se 1 (by rfl) ⟨2598287, by rfl⟩ : syracuseStep 3464383 = 5196575) B5196575
theorem B16235741 : Blo 1441540 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B5479771 : Blo 1441540 5479771 := bstep (se 1 (by rfl) ⟨4109828, by rfl⟩ : syracuseStep 5479771 = 8219657) B8219657
theorem B3243887 : Blo 1441540 3243887 := bstep (se 1 (by rfl) ⟨2432915, by rfl⟩ : syracuseStep 3243887 = 4865831) B4865831
theorem B3899303 : Blo 1441540 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B16433117 : Blo 1441540 16433117 := bstep (se 3 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 16433117 = 6162419) B6162419
theorem B5480531 : Blo 1441540 5480531 := bstep (se 1 (by rfl) ⟨4110398, by rfl⟩ : syracuseStep 5480531 = 8220797) B8220797
theorem B2162825 : Blo 1441540 2162825 := bstep (se 2 (by rfl) ⟨811059, by rfl⟩ : syracuseStep 2162825 = 1622119) B1622119
theorem B3244175 : Blo 1441540 3244175 := bstep (se 1 (by rfl) ⟨2433131, by rfl⟩ : syracuseStep 3244175 = 4866263) B4866263
theorem B2162843 : Blo 1441540 2162843 := bstep (se 1 (by rfl) ⟨1622132, by rfl⟩ : syracuseStep 2162843 = 3244265) B3244265
theorem B4866209 : Blo 1441540 4866209 := bstep (se 2 (by rfl) ⟨1824828, by rfl⟩ : syracuseStep 4866209 = 3649657) B3649657
theorem B2162927 : Blo 1441540 2162927 := bstep (se 1 (by rfl) ⟨1622195, by rfl⟩ : syracuseStep 2162927 = 3244391) B3244391
theorem B3244283 : Blo 1441540 3244283 := bstep (se 1 (by rfl) ⟨2433212, by rfl⟩ : syracuseStep 3244283 = 4866425) B4866425
theorem B2433287 : Blo 1441540 2433287 := bstep (se 1 (by rfl) ⟨1824965, by rfl⟩ : syracuseStep 2433287 = 3649931) B3649931
theorem B1442119 : Blo 1441540 1442119 := bstep (se 1 (by rfl) ⟨1081589, by rfl⟩ : syracuseStep 1442119 = 2163179) B2163179
theorem B2163023 : Blo 1441540 2163023 := bstep (se 1 (by rfl) ⟨1622267, by rfl⟩ : syracuseStep 2163023 = 3244535) B3244535
theorem B44392819 : Blo 1441540 44392819 := bstep (se 1 (by rfl) ⟨33294614, by rfl⟩ : syracuseStep 44392819 = 66589229) B66589229
theorem B3244409 : Blo 1441540 3244409 := bstep (se 2 (by rfl) ⟨1216653, by rfl⟩ : syracuseStep 3244409 = 2433307) B2433307
theorem B2433503 : Blo 1441540 2433503 := bstep (se 1 (by rfl) ⟨1825127, by rfl⟩ : syracuseStep 2433503 = 3650255) B3650255
theorem B1442303 : Blo 1441540 1442303 := bstep (se 1 (by rfl) ⟨1081727, by rfl⟩ : syracuseStep 1442303 = 2163455) B2163455
theorem B43295309 : Blo 1441540 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B12329759 : Blo 1441540 12329759 := bstep (se 1 (by rfl) ⟨9247319, by rfl⟩ : syracuseStep 12329759 = 18494639) B18494639
theorem B1442751 : Blo 1441540 1442751 := bstep (se 1 (by rfl) ⟨1082063, by rfl⟩ : syracuseStep 1442751 = 2164127) B2164127
theorem B1623271 : Blo 1441540 1623271 := bstep (se 1 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 1623271 = 2434907) B2434907
theorem B1443135 : Blo 1441540 1443135 := bstep (se 1 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 1443135 = 2164703) B2164703
theorem B2164175 : Blo 1441540 2164175 := bstep (se 1 (by rfl) ⟨1623131, by rfl⟩ : syracuseStep 2164175 = 3246263) B3246263
theorem B1443295 : Blo 1441540 1443295 := bstep (se 1 (by rfl) ⟨1082471, by rfl⟩ : syracuseStep 1443295 = 2164943) B2164943
theorem B2164199 : Blo 1441540 2164199 := bstep (se 1 (by rfl) ⟨1623149, by rfl⟩ : syracuseStep 2164199 = 3246299) B3246299
theorem B2164223 : Blo 1441540 2164223 := bstep (se 1 (by rfl) ⟨1623167, by rfl⟩ : syracuseStep 2164223 = 3246335) B3246335
theorem B266323565 : Blo 1441540 266323565 := bstep (se 3 (by rfl) ⟨49935668, by rfl⟩ : syracuseStep 266323565 = 99871337) B99871337
theorem B5474243 : Blo 1441540 5474243 := bstep (se 1 (by rfl) ⟨4105682, by rfl⟩ : syracuseStep 5474243 = 8211365) B8211365
theorem B2164763 : Blo 1441540 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B2599535 : Blo 1441540 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B26315387 : Blo 1441540 26315387 := bstep (se 1 (by rfl) ⟨19736540, by rfl⟩ : syracuseStep 26315387 = 39473081) B39473081
theorem B10955411 : Blo 1441540 10955411 := bstep (se 1 (by rfl) ⟨8216558, by rfl⟩ : syracuseStep 10955411 = 16433117) B16433117
theorem B10398365 : Blo 1441540 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B6163103 : Blo 1441540 6163103 := bstep (se 1 (by rfl) ⟨4622327, by rfl⟩ : syracuseStep 6163103 = 9244655) B9244655
theorem B13863599 : Blo 1441540 13863599 := bstep (se 1 (by rfl) ⟨10397699, by rfl⟩ : syracuseStep 13863599 = 20795399) B20795399
theorem B2435879 : Blo 1441540 2435879 := bstep (se 1 (by rfl) ⟨1826909, by rfl⟩ : syracuseStep 2435879 = 3653819) B3653819
theorem B4869179 : Blo 1441540 4869179 := bstep (se 1 (by rfl) ⟨3651884, by rfl⟩ : syracuseStep 4869179 = 7303769) B7303769
theorem B4623455 : Blo 1441540 4623455 := bstep (se 1 (by rfl) ⟨3467591, by rfl⟩ : syracuseStep 4623455 = 6935183) B6935183
theorem B3247379 : Blo 1441540 3247379 := bstep (se 1 (by rfl) ⟨2435534, by rfl⟩ : syracuseStep 3247379 = 4871069) B4871069
theorem B5000615 : Blo 1441540 5000615 := bstep (se 1 (by rfl) ⟨3750461, by rfl⟩ : syracuseStep 5000615 = 7500923) B7500923
theorem B3648959 : Blo 1441540 3648959 := bstep (se 1 (by rfl) ⟨2736719, by rfl⟩ : syracuseStep 3648959 = 5473439) B5473439
theorem B2740159 : Blo 1441540 2740159 := bstep (se 1 (by rfl) ⟨2055119, by rfl⟩ : syracuseStep 2740159 = 4110239) B4110239
theorem B4747319 : Blo 1441540 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B13865215 : Blo 1441540 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B10539335 : Blo 1441540 10539335 := bstep (se 1 (by rfl) ⟨7904501, by rfl⟩ : syracuseStep 10539335 = 15809003) B15809003
theorem B5476841 : Blo 1441540 5476841 := bstep (se 2 (by rfl) ⟨2053815, by rfl⟩ : syracuseStep 5476841 = 4107631) B4107631
theorem B31191713 : Blo 1441540 31191713 := bstep (se 2 (by rfl) ⟨11696892, by rfl⟩ : syracuseStep 31191713 = 23393785) B23393785
theorem B5477159 : Blo 1441540 5477159 := bstep (se 1 (by rfl) ⟨4107869, by rfl⟩ : syracuseStep 5477159 = 8215739) B8215739
theorem B10958327 : Blo 1441540 10958327 := bstep (se 1 (by rfl) ⟨8218745, by rfl⟩ : syracuseStep 10958327 = 16437491) B16437491
theorem B11851487 : Blo 1441540 11851487 := bstep (se 1 (by rfl) ⟨8888615, by rfl⟩ : syracuseStep 11851487 = 17777231) B17777231
theorem B3651419 : Blo 1441540 3651419 := bstep (se 1 (by rfl) ⟨2738564, by rfl⟩ : syracuseStep 3651419 = 5477129) B5477129
theorem B5478299 : Blo 1441540 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B4110695 : Blo 1441540 4110695 := bstep (se 1 (by rfl) ⟨3083021, by rfl⟩ : syracuseStep 4110695 = 6166043) B6166043
theorem B4938241 : Blo 1441540 4938241 := bstep (se 2 (by rfl) ⟨1851840, by rfl⟩ : syracuseStep 4938241 = 3703681) B3703681
theorem B5479073 : Blo 1441540 5479073 := bstep (se 2 (by rfl) ⟨2054652, by rfl⟩ : syracuseStep 5479073 = 4109305) B4109305
theorem B3652391 : Blo 1441540 3652391 := bstep (se 1 (by rfl) ⟨2739293, by rfl⟩ : syracuseStep 3652391 = 5478587) B5478587
theorem B5479271 : Blo 1441540 5479271 := bstep (se 1 (by rfl) ⟨4109453, by rfl⟩ : syracuseStep 5479271 = 8218907) B8218907
theorem B4619177 : Blo 1441540 4619177 := bstep (se 2 (by rfl) ⟨1732191, by rfl⟩ : syracuseStep 4619177 = 3464383) B3464383
theorem B3464201 : Blo 1441540 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B7306361 : Blo 1441540 7306361 := bstep (se 2 (by rfl) ⟨2739885, by rfl⟩ : syracuseStep 7306361 = 5479771) B5479771
theorem B3652735 : Blo 1441540 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B2162591 : Blo 1441540 2162591 := bstep (se 1 (by rfl) ⟨1621943, by rfl⟩ : syracuseStep 2162591 = 3243887) B3243887
theorem B3653687 : Blo 1441540 3653687 := bstep (se 1 (by rfl) ⟨2740265, by rfl⟩ : syracuseStep 3653687 = 5480531) B5480531
theorem B1441883 : Blo 1441540 1441883 := bstep (se 1 (by rfl) ⟨1081412, by rfl⟩ : syracuseStep 1441883 = 2162825) B2162825
theorem B2162783 : Blo 1441540 2162783 := bstep (se 1 (by rfl) ⟨1622087, by rfl⟩ : syracuseStep 2162783 = 3244175) B3244175
theorem B1441895 : Blo 1441540 1441895 := bstep (se 1 (by rfl) ⟨1081421, by rfl⟩ : syracuseStep 1441895 = 2162843) B2162843
theorem B3244139 : Blo 1441540 3244139 := bstep (se 1 (by rfl) ⟨2433104, by rfl⟩ : syracuseStep 3244139 = 4866209) B4866209
theorem B1441951 : Blo 1441540 1441951 := bstep (se 1 (by rfl) ⟨1081463, by rfl⟩ : syracuseStep 1441951 = 2162927) B2162927
theorem B2162855 : Blo 1441540 2162855 := bstep (se 1 (by rfl) ⟨1622141, by rfl⟩ : syracuseStep 2162855 = 3244283) B3244283
theorem B1622191 : Blo 1441540 1622191 := bstep (se 1 (by rfl) ⟨1216643, by rfl⟩ : syracuseStep 1622191 = 2433287) B2433287
theorem B1442015 : Blo 1441540 1442015 := bstep (se 1 (by rfl) ⟨1081511, by rfl⟩ : syracuseStep 1442015 = 2163023) B2163023
theorem B2162939 : Blo 1441540 2162939 := bstep (se 1 (by rfl) ⟨1622204, by rfl⟩ : syracuseStep 2162939 = 3244409) B3244409
theorem B1622335 : Blo 1441540 1622335 := bstep (se 1 (by rfl) ⟨1216751, by rfl⟩ : syracuseStep 1622335 = 2433503) B2433503
theorem B1442783 : Blo 1441540 1442783 := bstep (se 1 (by rfl) ⟨1082087, by rfl⟩ : syracuseStep 1442783 = 2164175) B2164175
theorem B1442799 : Blo 1441540 1442799 := bstep (se 1 (by rfl) ⟨1082099, by rfl⟩ : syracuseStep 1442799 = 2164199) B2164199
theorem B1442815 : Blo 1441540 1442815 := bstep (se 1 (by rfl) ⟨1082111, by rfl⟩ : syracuseStep 1442815 = 2164223) B2164223
theorem B2434279 : Blo 1441540 2434279 := bstep (se 1 (by rfl) ⟨1825709, by rfl⟩ : syracuseStep 2434279 = 3651419) B3651419
theorem B1443175 : Blo 1441540 1443175 := bstep (se 1 (by rfl) ⟨1082381, by rfl⟩ : syracuseStep 1443175 = 2164763) B2164763
theorem B2164361 : Blo 1441540 2164361 := bstep (se 2 (by rfl) ⟨811635, by rfl⟩ : syracuseStep 2164361 = 1623271) B1623271
theorem B6932243 : Blo 1441540 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B9242399 : Blo 1441540 9242399 := bstep (se 1 (by rfl) ⟨6931799, by rfl⟩ : syracuseStep 9242399 = 13863599) B13863599
theorem B2434927 : Blo 1441540 2434927 := bstep (se 1 (by rfl) ⟨1826195, by rfl⟩ : syracuseStep 2434927 = 3652391) B3652391
theorem B1623919 : Blo 1441540 1623919 := bstep (se 1 (by rfl) ⟨1217939, by rfl⟩ : syracuseStep 1623919 = 2435879) B2435879
theorem B3246119 : Blo 1441540 3246119 := bstep (se 1 (by rfl) ⟨2434589, by rfl⟩ : syracuseStep 3246119 = 4869179) B4869179
theorem B3082303 : Blo 1441540 3082303 := bstep (se 1 (by rfl) ⟨2311727, by rfl⟩ : syracuseStep 3082303 = 4623455) B4623455
theorem B2164919 : Blo 1441540 2164919 := bstep (se 1 (by rfl) ⟨1623689, by rfl⟩ : syracuseStep 2164919 = 3247379) B3247379
theorem B3164879 : Blo 1441540 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B28863539 : Blo 1441540 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B20794475 : Blo 1441540 20794475 := bstep (se 1 (by rfl) ⟨15595856, by rfl⟩ : syracuseStep 20794475 = 31191713) B31191713
theorem B59190425 : Blo 1441540 59190425 := bstep (se 2 (by rfl) ⟨22196409, by rfl⟩ : syracuseStep 59190425 = 44392819) B44392819
theorem B8219839 : Blo 1441540 8219839 := bstep (se 1 (by rfl) ⟨6164879, by rfl⟩ : syracuseStep 8219839 = 12329759) B12329759
theorem B177549043 : Blo 1441540 177549043 := bstep (se 1 (by rfl) ⟨133161782, by rfl⟩ : syracuseStep 177549043 = 266323565) B266323565
theorem B7900991 : Blo 1441540 7900991 := bstep (se 1 (by rfl) ⟨5925743, by rfl⟩ : syracuseStep 7900991 = 11851487) B11851487
theorem B3649495 : Blo 1441540 3649495 := bstep (se 1 (by rfl) ⟨2737121, by rfl⟩ : syracuseStep 3649495 = 5474243) B5474243
theorem B4870313 : Blo 1441540 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B2740463 : Blo 1441540 2740463 := bstep (se 1 (by rfl) ⟨2055347, by rfl⟩ : syracuseStep 2740463 = 4110695) B4110695
theorem B1733023 : Blo 1441540 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B17543591 : Blo 1441540 17543591 := bstep (se 1 (by rfl) ⟨13157693, by rfl⟩ : syracuseStep 17543591 = 26315387) B26315387
theorem B7303607 : Blo 1441540 7303607 := bstep (se 1 (by rfl) ⟨5477705, by rfl⟩ : syracuseStep 7303607 = 10955411) B10955411
theorem B4108735 : Blo 1441540 4108735 := bstep (se 1 (by rfl) ⟨3081551, by rfl⟩ : syracuseStep 4108735 = 6163103) B6163103
theorem B4870907 : Blo 1441540 4870907 := bstep (se 1 (by rfl) ⟨3653180, by rfl⟩ : syracuseStep 4870907 = 7306361) B7306361
theorem B7026223 : Blo 1441540 7026223 := bstep (se 1 (by rfl) ⟨5269667, by rfl⟩ : syracuseStep 7026223 = 10539335) B10539335
theorem B3651227 : Blo 1441540 3651227 := bstep (se 1 (by rfl) ⟨2738420, by rfl⟩ : syracuseStep 3651227 = 5476841) B5476841
theorem B18486953 : Blo 1441540 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B3651439 : Blo 1441540 3651439 := bstep (se 1 (by rfl) ⟨2738579, by rfl⟩ : syracuseStep 3651439 = 5477159) B5477159
theorem B6584321 : Blo 1441540 6584321 := bstep (se 2 (by rfl) ⟨2469120, by rfl⟩ : syracuseStep 6584321 = 4938241) B4938241
theorem B7305551 : Blo 1441540 7305551 := bstep (se 1 (by rfl) ⟨5479163, by rfl⟩ : syracuseStep 7305551 = 10958327) B10958327
theorem B3652199 : Blo 1441540 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B3652715 : Blo 1441540 3652715 := bstep (se 1 (by rfl) ⟨2739536, by rfl⟩ : syracuseStep 3652715 = 5479073) B5479073
theorem B3652847 : Blo 1441540 3652847 := bstep (se 1 (by rfl) ⟨2739635, by rfl⟩ : syracuseStep 3652847 = 5479271) B5479271
theorem B3079451 : Blo 1441540 3079451 := bstep (se 1 (by rfl) ⟨2309588, by rfl⟩ : syracuseStep 3079451 = 4619177) B4619177
theorem B2309467 : Blo 1441540 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B3333743 : Blo 1441540 3333743 := bstep (se 1 (by rfl) ⟨2500307, by rfl⟩ : syracuseStep 3333743 = 5000615) B5000615
theorem B2432639 : Blo 1441540 2432639 := bstep (se 1 (by rfl) ⟨1824479, by rfl⟩ : syracuseStep 2432639 = 3648959) B3648959
theorem B3653545 : Blo 1441540 3653545 := bstep (se 2 (by rfl) ⟨1370079, by rfl⟩ : syracuseStep 3653545 = 2740159) B2740159
theorem B1441727 : Blo 1441540 1441727 := bstep (se 1 (by rfl) ⟨1081295, by rfl⟩ : syracuseStep 1441727 = 2162591) B2162591
theorem B1441855 : Blo 1441540 1441855 := bstep (se 1 (by rfl) ⟨1081391, by rfl⟩ : syracuseStep 1441855 = 2162783) B2162783
theorem B2162759 : Blo 1441540 2162759 := bstep (se 1 (by rfl) ⟨1622069, by rfl⟩ : syracuseStep 2162759 = 3244139) B3244139
theorem B1441903 : Blo 1441540 1441903 := bstep (se 1 (by rfl) ⟨1081427, by rfl⟩ : syracuseStep 1441903 = 2162855) B2162855
theorem B1826975 : Blo 1441540 1826975 := bstep (se 1 (by rfl) ⟨1370231, by rfl⟩ : syracuseStep 1826975 = 2740463) B2740463
theorem B1441959 : Blo 1441540 1441959 := bstep (se 1 (by rfl) ⟨1081469, by rfl⟩ : syracuseStep 1441959 = 2162939) B2162939
theorem B2162921 : Blo 1441540 2162921 := bstep (se 2 (by rfl) ⟨811095, by rfl⟩ : syracuseStep 2162921 = 1622191) B1622191
theorem B2163113 : Blo 1441540 2163113 := bstep (se 2 (by rfl) ⟨811167, by rfl⟩ : syracuseStep 2163113 = 1622335) B1622335
theorem B2310697 : Blo 1441540 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B1442907 : Blo 1441540 1442907 := bstep (se 1 (by rfl) ⟨1082180, by rfl⟩ : syracuseStep 1442907 = 2164361) B2164361
theorem B2434151 : Blo 1441540 2434151 := bstep (se 1 (by rfl) ⟨1825613, by rfl⟩ : syracuseStep 2434151 = 3651227) B3651227
theorem B6161599 : Blo 1441540 6161599 := bstep (se 1 (by rfl) ⟨4621199, by rfl⟩ : syracuseStep 6161599 = 9242399) B9242399
theorem B2164079 : Blo 1441540 2164079 := bstep (se 1 (by rfl) ⟨1623059, by rfl⟩ : syracuseStep 2164079 = 3246119) B3246119
theorem B1443279 : Blo 1441540 1443279 := bstep (se 1 (by rfl) ⟨1082459, by rfl⟩ : syracuseStep 1443279 = 2164919) B2164919
theorem B3245705 : Blo 1441540 3245705 := bstep (se 2 (by rfl) ⟨1217139, by rfl⟩ : syracuseStep 3245705 = 2434279) B2434279
theorem B2434799 : Blo 1441540 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B8439677 : Blo 1441540 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B13862983 : Blo 1441540 13862983 := bstep (se 1 (by rfl) ⟨10397237, by rfl⟩ : syracuseStep 13862983 = 20794475) B20794475
theorem B2435143 : Blo 1441540 2435143 := bstep (se 1 (by rfl) ⟨1826357, by rfl⟩ : syracuseStep 2435143 = 3652715) B3652715
theorem B2435231 : Blo 1441540 2435231 := bstep (se 1 (by rfl) ⟨1826423, by rfl⟩ : syracuseStep 2435231 = 3652847) B3652847
theorem B2222495 : Blo 1441540 2222495 := bstep (se 1 (by rfl) ⟨1666871, by rfl⟩ : syracuseStep 2222495 = 3333743) B3333743
theorem B4868585 : Blo 1441540 4868585 := bstep (se 2 (by rfl) ⟨1825719, by rfl⟩ : syracuseStep 4868585 = 3651439) B3651439
theorem B3246569 : Blo 1441540 3246569 := bstep (se 2 (by rfl) ⟨1217463, by rfl⟩ : syracuseStep 3246569 = 2434927) B2434927
theorem B2165225 : Blo 1441540 2165225 := bstep (se 2 (by rfl) ⟨811959, by rfl⟩ : syracuseStep 2165225 = 1623919) B1623919
theorem B2435791 : Blo 1441540 2435791 := bstep (se 1 (by rfl) ⟨1826843, by rfl⟩ : syracuseStep 2435791 = 3653687) B3653687
theorem B3246875 : Blo 1441540 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B4869071 : Blo 1441540 4869071 := bstep (se 1 (by rfl) ⟨3651803, by rfl⟩ : syracuseStep 4869071 = 7303607) B7303607
theorem B3247271 : Blo 1441540 3247271 := bstep (se 1 (by rfl) ⟨2435453, by rfl⟩ : syracuseStep 3247271 = 4870907) B4870907
theorem B12324635 : Blo 1441540 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B4870367 : Blo 1441540 4870367 := bstep (se 1 (by rfl) ⟨3652775, by rfl⟩ : syracuseStep 4870367 = 7305551) B7305551
theorem B18485981 : Blo 1441540 18485981 := bstep (se 3 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 18485981 = 6932243) B6932243
theorem B9368297 : Blo 1441540 9368297 := bstep (se 2 (by rfl) ⟨3513111, by rfl⟩ : syracuseStep 9368297 = 7026223) B7026223
theorem B2052967 : Blo 1441540 2052967 := bstep (se 1 (by rfl) ⟨1539725, by rfl⟩ : syracuseStep 2052967 = 3079451) B3079451
theorem B4871393 : Blo 1441540 4871393 := bstep (se 2 (by rfl) ⟨1826772, by rfl⟩ : syracuseStep 4871393 = 3653545) B3653545
theorem B11695727 : Blo 1441540 11695727 := bstep (se 1 (by rfl) ⟨8771795, by rfl⟩ : syracuseStep 11695727 = 17543591) B17543591
theorem B16438949 : Blo 1441540 16438949 := bstep (se 4 (by rfl) ⟨1541151, by rfl⟩ : syracuseStep 16438949 = 3082303) B3082303
theorem B5478313 : Blo 1441540 5478313 := bstep (se 2 (by rfl) ⟨2054367, by rfl⟩ : syracuseStep 5478313 = 4108735) B4108735
theorem B4389547 : Blo 1441540 4389547 := bstep (se 1 (by rfl) ⟨3292160, by rfl⟩ : syracuseStep 4389547 = 6584321) B6584321
theorem B10959785 : Blo 1441540 10959785 := bstep (se 2 (by rfl) ⟨4109919, by rfl⟩ : syracuseStep 10959785 = 8219839) B8219839
theorem B3079289 : Blo 1441540 3079289 := bstep (se 2 (by rfl) ⟨1154733, by rfl⟩ : syracuseStep 3079289 = 2309467) B2309467
theorem B19242359 : Blo 1441540 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B39460283 : Blo 1441540 39460283 := bstep (se 1 (by rfl) ⟨29595212, by rfl⟩ : syracuseStep 39460283 = 59190425) B59190425
theorem B236732057 : Blo 1441540 236732057 := bstep (se 2 (by rfl) ⟨88774521, by rfl⟩ : syracuseStep 236732057 = 177549043) B177549043
theorem B1621759 : Blo 1441540 1621759 := bstep (se 1 (by rfl) ⟨1216319, by rfl⟩ : syracuseStep 1621759 = 2432639) B2432639
theorem B5267327 : Blo 1441540 5267327 := bstep (se 1 (by rfl) ⟨3950495, by rfl⟩ : syracuseStep 5267327 = 7900991) B7900991
theorem B4865993 : Blo 1441540 4865993 := bstep (se 2 (by rfl) ⟨1824747, by rfl⟩ : syracuseStep 4865993 = 3649495) B3649495
theorem B1441839 : Blo 1441540 1441839 := bstep (se 1 (by rfl) ⟨1081379, by rfl⟩ : syracuseStep 1441839 = 2162759) B2162759
theorem B1441947 : Blo 1441540 1441947 := bstep (se 1 (by rfl) ⟨1081460, by rfl⟩ : syracuseStep 1441947 = 2162921) B2162921
theorem B1442075 : Blo 1441540 1442075 := bstep (se 1 (by rfl) ⟨1081556, by rfl⟩ : syracuseStep 1442075 = 2163113) B2163113
theorem B3080929 : Blo 1441540 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B1622767 : Blo 1441540 1622767 := bstep (se 1 (by rfl) ⟨1217075, by rfl⟩ : syracuseStep 1622767 = 2434151) B2434151
theorem B1442719 : Blo 1441540 1442719 := bstep (se 1 (by rfl) ⟨1082039, by rfl⟩ : syracuseStep 1442719 = 2164079) B2164079
theorem B2163803 : Blo 1441540 2163803 := bstep (se 1 (by rfl) ⟨1622852, by rfl⟩ : syracuseStep 2163803 = 3245705) B3245705
theorem B2737289 : Blo 1441540 2737289 := bstep (se 2 (by rfl) ⟨1026483, by rfl⟩ : syracuseStep 2737289 = 2052967) B2052967
theorem B1623199 : Blo 1441540 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B1623487 : Blo 1441540 1623487 := bstep (se 1 (by rfl) ⟨1217615, by rfl⟩ : syracuseStep 1623487 = 2435231) B2435231
theorem B3245723 : Blo 1441540 3245723 := bstep (se 1 (by rfl) ⟨2434292, by rfl⟩ : syracuseStep 3245723 = 4868585) B4868585
theorem B2164379 : Blo 1441540 2164379 := bstep (se 1 (by rfl) ⟨1623284, by rfl⟩ : syracuseStep 2164379 = 3246569) B3246569
theorem B1443483 : Blo 1441540 1443483 := bstep (se 1 (by rfl) ⟨1082612, by rfl⟩ : syracuseStep 1443483 = 2165225) B2165225
theorem B2164583 : Blo 1441540 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B3246047 : Blo 1441540 3246047 := bstep (se 1 (by rfl) ⟨2434535, by rfl⟩ : syracuseStep 3246047 = 4869071) B4869071
theorem B2164847 : Blo 1441540 2164847 := bstep (se 1 (by rfl) ⟨1623635, by rfl⟩ : syracuseStep 2164847 = 3247271) B3247271
theorem B26306855 : Blo 1441540 26306855 := bstep (se 1 (by rfl) ⟨19730141, by rfl⟩ : syracuseStep 26306855 = 39460283) B39460283
theorem B157821371 : Blo 1441540 157821371 := bstep (se 1 (by rfl) ⟨118366028, by rfl⟩ : syracuseStep 157821371 = 236732057) B236732057
theorem B18483977 : Blo 1441540 18483977 := bstep (se 2 (by rfl) ⟨6931491, by rfl⟩ : syracuseStep 18483977 = 13862983) B13862983
theorem B3246857 : Blo 1441540 3246857 := bstep (se 2 (by rfl) ⟨1217571, by rfl⟩ : syracuseStep 3246857 = 2435143) B2435143
theorem B3246911 : Blo 1441540 3246911 := bstep (se 1 (by rfl) ⟨2435183, by rfl⟩ : syracuseStep 3246911 = 4870367) B4870367
theorem B12323987 : Blo 1441540 12323987 := bstep (se 1 (by rfl) ⟨9242990, by rfl⟩ : syracuseStep 12323987 = 18485981) B18485981
theorem B6245531 : Blo 1441540 6245531 := bstep (se 1 (by rfl) ⟨4684148, by rfl⟩ : syracuseStep 6245531 = 9368297) B9368297
theorem B3247595 : Blo 1441540 3247595 := bstep (se 1 (by rfl) ⟨2435696, by rfl⟩ : syracuseStep 3247595 = 4871393) B4871393
theorem B5852729 : Blo 1441540 5852729 := bstep (se 2 (by rfl) ⟨2194773, by rfl⟩ : syracuseStep 5852729 = 4389547) B4389547
theorem B3247721 : Blo 1441540 3247721 := bstep (se 2 (by rfl) ⟨1217895, by rfl⟩ : syracuseStep 3247721 = 2435791) B2435791
theorem B2052859 : Blo 1441540 2052859 := bstep (se 1 (by rfl) ⟨1539644, by rfl⟩ : syracuseStep 2052859 = 3079289) B3079289
theorem B14046205 : Blo 1441540 14046205 := bstep (se 3 (by rfl) ⟨2633663, by rfl⟩ : syracuseStep 14046205 = 5267327) B5267327
theorem B7304417 : Blo 1441540 7304417 := bstep (se 2 (by rfl) ⟨2739156, by rfl⟩ : syracuseStep 7304417 = 5478313) B5478313
theorem B4871933 : Blo 1441540 4871933 := bstep (se 3 (by rfl) ⟨913487, by rfl⟩ : syracuseStep 4871933 = 1826975) B1826975
theorem B7797151 : Blo 1441540 7797151 := bstep (se 1 (by rfl) ⟨5847863, by rfl⟩ : syracuseStep 7797151 = 11695727) B11695727
theorem B10959299 : Blo 1441540 10959299 := bstep (se 1 (by rfl) ⟨8219474, by rfl⟩ : syracuseStep 10959299 = 16438949) B16438949
theorem B5626451 : Blo 1441540 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B8215465 : Blo 1441540 8215465 := bstep (se 2 (by rfl) ⟨3080799, by rfl⟩ : syracuseStep 8215465 = 6161599) B6161599
theorem B1481663 : Blo 1441540 1481663 := bstep (se 1 (by rfl) ⟨1111247, by rfl⟩ : syracuseStep 1481663 = 2222495) B2222495
theorem B7306523 : Blo 1441540 7306523 := bstep (se 1 (by rfl) ⟨5479892, by rfl⟩ : syracuseStep 7306523 = 10959785) B10959785
theorem B12828239 : Blo 1441540 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B2162345 : Blo 1441540 2162345 := bstep (se 2 (by rfl) ⟨810879, by rfl⟩ : syracuseStep 2162345 = 1621759) B1621759
theorem B8216423 : Blo 1441540 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B3243995 : Blo 1441540 3243995 := bstep (se 1 (by rfl) ⟨2432996, by rfl⟩ : syracuseStep 3243995 = 4865993) B4865993
theorem B10396201 : Blo 1441540 10396201 := bstep (se 2 (by rfl) ⟨3898575, by rfl⟩ : syracuseStep 10396201 = 7797151) B7797151
theorem B1442535 : Blo 1441540 1442535 := bstep (se 1 (by rfl) ⟨1081901, by rfl⟩ : syracuseStep 1442535 = 2163803) B2163803
theorem B2163689 : Blo 1441540 2163689 := bstep (se 2 (by rfl) ⟨811383, by rfl⟩ : syracuseStep 2163689 = 1622767) B1622767
theorem B2737145 : Blo 1441540 2737145 := bstep (se 2 (by rfl) ⟨1026429, by rfl⟩ : syracuseStep 2737145 = 2052859) B2052859
theorem B2163815 : Blo 1441540 2163815 := bstep (se 1 (by rfl) ⟨1622861, by rfl⟩ : syracuseStep 2163815 = 3245723) B3245723
theorem B1442919 : Blo 1441540 1442919 := bstep (se 1 (by rfl) ⟨1082189, by rfl⟩ : syracuseStep 1442919 = 2164379) B2164379
theorem B10953953 : Blo 1441540 10953953 := bstep (se 2 (by rfl) ⟨4107732, by rfl⟩ : syracuseStep 10953953 = 8215465) B8215465
theorem B1443055 : Blo 1441540 1443055 := bstep (se 1 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 1443055 = 2164583) B2164583
theorem B2164031 : Blo 1441540 2164031 := bstep (se 1 (by rfl) ⟨1623023, by rfl⟩ : syracuseStep 2164031 = 3246047) B3246047
theorem B18728273 : Blo 1441540 18728273 := bstep (se 2 (by rfl) ⟨7023102, by rfl⟩ : syracuseStep 18728273 = 14046205) B14046205
theorem B1443231 : Blo 1441540 1443231 := bstep (se 1 (by rfl) ⟨1082423, by rfl⟩ : syracuseStep 1443231 = 2164847) B2164847
theorem B2164265 : Blo 1441540 2164265 := bstep (se 2 (by rfl) ⟨811599, by rfl⟩ : syracuseStep 2164265 = 1623199) B1623199
theorem B12322651 : Blo 1441540 12322651 := bstep (se 1 (by rfl) ⟨9241988, by rfl⟩ : syracuseStep 12322651 = 18483977) B18483977
theorem B2164571 : Blo 1441540 2164571 := bstep (se 1 (by rfl) ⟨1623428, by rfl⟩ : syracuseStep 2164571 = 3246857) B3246857
theorem B2164607 : Blo 1441540 2164607 := bstep (se 1 (by rfl) ⟨1623455, by rfl⟩ : syracuseStep 2164607 = 3246911) B3246911
theorem B2164649 : Blo 1441540 2164649 := bstep (se 2 (by rfl) ⟨811743, by rfl⟩ : syracuseStep 2164649 = 1623487) B1623487
theorem B4163687 : Blo 1441540 4163687 := bstep (se 1 (by rfl) ⟨3122765, by rfl⟩ : syracuseStep 4163687 = 6245531) B6245531
theorem B2165063 : Blo 1441540 2165063 := bstep (se 1 (by rfl) ⟨1623797, by rfl⟩ : syracuseStep 2165063 = 3247595) B3247595
theorem B3901819 : Blo 1441540 3901819 := bstep (se 1 (by rfl) ⟨2926364, by rfl⟩ : syracuseStep 3901819 = 5852729) B5852729
theorem B2165147 : Blo 1441540 2165147 := bstep (se 1 (by rfl) ⟨1623860, by rfl⟩ : syracuseStep 2165147 = 3247721) B3247721
theorem B3951101 : Blo 1441540 3951101 := bstep (se 3 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 3951101 = 1481663) B1481663
theorem B4869611 : Blo 1441540 4869611 := bstep (se 1 (by rfl) ⟨3652208, by rfl⟩ : syracuseStep 4869611 = 7304417) B7304417
theorem B4107905 : Blo 1441540 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B3247955 : Blo 1441540 3247955 := bstep (se 1 (by rfl) ⟨2435966, by rfl⟩ : syracuseStep 3247955 = 4871933) B4871933
theorem B105214247 : Blo 1441540 105214247 := bstep (se 1 (by rfl) ⟨78910685, by rfl⟩ : syracuseStep 105214247 = 157821371) B157821371
theorem B4871015 : Blo 1441540 4871015 := bstep (se 1 (by rfl) ⟨3653261, by rfl⟩ : syracuseStep 4871015 = 7306523) B7306523
theorem B5477615 : Blo 1441540 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B1824859 : Blo 1441540 1824859 := bstep (se 1 (by rfl) ⟨1368644, by rfl⟩ : syracuseStep 1824859 = 2737289) B2737289
theorem B17537903 : Blo 1441540 17537903 := bstep (se 1 (by rfl) ⟨13153427, by rfl⟩ : syracuseStep 17537903 = 26306855) B26306855
theorem B7306199 : Blo 1441540 7306199 := bstep (se 1 (by rfl) ⟨5479649, by rfl⟩ : syracuseStep 7306199 = 10959299) B10959299
theorem B3750967 : Blo 1441540 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B8215991 : Blo 1441540 8215991 := bstep (se 1 (by rfl) ⟨6161993, by rfl⟩ : syracuseStep 8215991 = 12323987) B12323987
theorem B8552159 : Blo 1441540 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B1441563 : Blo 1441540 1441563 := bstep (se 1 (by rfl) ⟨1081172, by rfl⟩ : syracuseStep 1441563 = 2162345) B2162345
theorem B2162663 : Blo 1441540 2162663 := bstep (se 1 (by rfl) ⟨1621997, by rfl⟩ : syracuseStep 2162663 = 3243995) B3243995
theorem B2433145 : Blo 1441540 2433145 := bstep (se 2 (by rfl) ⟨912429, by rfl⟩ : syracuseStep 2433145 = 1824859) B1824859
theorem B20005157 : Blo 1441540 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B5202425 : Blo 1441540 5202425 := bstep (se 2 (by rfl) ⟨1950909, by rfl⟩ : syracuseStep 5202425 = 3901819) B3901819
theorem B1442459 : Blo 1441540 1442459 := bstep (se 1 (by rfl) ⟨1081844, by rfl⟩ : syracuseStep 1442459 = 2163689) B2163689
theorem B13861601 : Blo 1441540 13861601 := bstep (se 2 (by rfl) ⟨5198100, by rfl⟩ : syracuseStep 13861601 = 10396201) B10396201
theorem B1442543 : Blo 1441540 1442543 := bstep (se 1 (by rfl) ⟨1081907, by rfl⟩ : syracuseStep 1442543 = 2163815) B2163815
theorem B1442687 : Blo 1441540 1442687 := bstep (se 1 (by rfl) ⟨1082015, by rfl⟩ : syracuseStep 1442687 = 2164031) B2164031
theorem B12485515 : Blo 1441540 12485515 := bstep (se 1 (by rfl) ⟨9364136, by rfl⟩ : syracuseStep 12485515 = 18728273) B18728273
theorem B1442843 : Blo 1441540 1442843 := bstep (se 1 (by rfl) ⟨1082132, by rfl⟩ : syracuseStep 1442843 = 2164265) B2164265
theorem B1443047 : Blo 1441540 1443047 := bstep (se 1 (by rfl) ⟨1082285, by rfl⟩ : syracuseStep 1443047 = 2164571) B2164571
theorem B1443071 : Blo 1441540 1443071 := bstep (se 1 (by rfl) ⟨1082303, by rfl⟩ : syracuseStep 1443071 = 2164607) B2164607
theorem B1443099 : Blo 1441540 1443099 := bstep (se 1 (by rfl) ⟨1082324, by rfl⟩ : syracuseStep 1443099 = 2164649) B2164649
theorem B1443375 : Blo 1441540 1443375 := bstep (se 1 (by rfl) ⟨1082531, by rfl⟩ : syracuseStep 1443375 = 2165063) B2165063
theorem B1443431 : Blo 1441540 1443431 := bstep (se 1 (by rfl) ⟨1082573, by rfl⟩ : syracuseStep 1443431 = 2165147) B2165147
theorem B11691935 : Blo 1441540 11691935 := bstep (se 1 (by rfl) ⟨8768951, by rfl⟩ : syracuseStep 11691935 = 17537903) B17537903
theorem B3246407 : Blo 1441540 3246407 := bstep (se 1 (by rfl) ⟨2434805, by rfl⟩ : syracuseStep 3246407 = 4869611) B4869611
theorem B2738603 : Blo 1441540 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B2165303 : Blo 1441540 2165303 := bstep (se 1 (by rfl) ⟨1623977, by rfl⟩ : syracuseStep 2165303 = 3247955) B3247955
theorem B70142831 : Blo 1441540 70142831 := bstep (se 1 (by rfl) ⟨52607123, by rfl⟩ : syracuseStep 70142831 = 105214247) B105214247
theorem B3247343 : Blo 1441540 3247343 := bstep (se 1 (by rfl) ⟨2435507, by rfl⟩ : syracuseStep 3247343 = 4871015) B4871015
theorem B7302635 : Blo 1441540 7302635 := bstep (se 1 (by rfl) ⟨5476976, by rfl⟩ : syracuseStep 7302635 = 10953953) B10953953
theorem B2634067 : Blo 1441540 2634067 := bstep (se 1 (by rfl) ⟨1975550, by rfl⟩ : syracuseStep 2634067 = 3951101) B3951101
theorem B4870799 : Blo 1441540 4870799 := bstep (se 1 (by rfl) ⟨3653099, by rfl⟩ : syracuseStep 4870799 = 7306199) B7306199
theorem B5477327 : Blo 1441540 5477327 := bstep (se 1 (by rfl) ⟨4107995, by rfl⟩ : syracuseStep 5477327 = 8215991) B8215991
theorem B16430201 : Blo 1441540 16430201 := bstep (se 2 (by rfl) ⟨6161325, by rfl⟩ : syracuseStep 16430201 = 12322651) B12322651
theorem B1824763 : Blo 1441540 1824763 := bstep (se 1 (by rfl) ⟨1368572, by rfl⟩ : syracuseStep 1824763 = 2737145) B2737145
theorem B3651743 : Blo 1441540 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B2775791 : Blo 1441540 2775791 := bstep (se 1 (by rfl) ⟨2081843, by rfl⟩ : syracuseStep 2775791 = 4163687) B4163687
theorem B5701439 : Blo 1441540 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B1441775 : Blo 1441540 1441775 := bstep (se 1 (by rfl) ⟨1081331, by rfl⟩ : syracuseStep 1441775 = 2162663) B2162663
theorem B3244193 : Blo 1441540 3244193 := bstep (se 2 (by rfl) ⟨1216572, by rfl⟩ : syracuseStep 3244193 = 2433145) B2433145
theorem B13336771 : Blo 1441540 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B9241067 : Blo 1441540 9241067 := bstep (se 1 (by rfl) ⟨6930800, by rfl⟩ : syracuseStep 9241067 = 13861601) B13861601
theorem B10953467 : Blo 1441540 10953467 := bstep (se 1 (by rfl) ⟨8215100, by rfl⟩ : syracuseStep 10953467 = 16430201) B16430201
theorem B16647353 : Blo 1441540 16647353 := bstep (se 2 (by rfl) ⟨6242757, by rfl⟩ : syracuseStep 16647353 = 12485515) B12485515
theorem B2434495 : Blo 1441540 2434495 := bstep (se 1 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 2434495 = 3651743) B3651743
theorem B2164271 : Blo 1441540 2164271 := bstep (se 1 (by rfl) ⟨1623203, by rfl⟩ : syracuseStep 2164271 = 3246407) B3246407
theorem B1443535 : Blo 1441540 1443535 := bstep (se 1 (by rfl) ⟨1082651, by rfl⟩ : syracuseStep 1443535 = 2165303) B2165303
theorem B46761887 : Blo 1441540 46761887 := bstep (se 1 (by rfl) ⟨35071415, by rfl⟩ : syracuseStep 46761887 = 70142831) B70142831
theorem B2164895 : Blo 1441540 2164895 := bstep (se 1 (by rfl) ⟨1623671, by rfl⟩ : syracuseStep 2164895 = 3247343) B3247343
theorem B4868423 : Blo 1441540 4868423 := bstep (se 1 (by rfl) ⟨3651317, by rfl⟩ : syracuseStep 4868423 = 7302635) B7302635
theorem B3247199 : Blo 1441540 3247199 := bstep (se 1 (by rfl) ⟨2435399, by rfl⟩ : syracuseStep 3247199 = 4870799) B4870799
theorem B7794623 : Blo 1441540 7794623 := bstep (se 1 (by rfl) ⟨5845967, by rfl⟩ : syracuseStep 7794623 = 11691935) B11691935
theorem B13873133 : Blo 1441540 13873133 := bstep (se 3 (by rfl) ⟨2601212, by rfl⟩ : syracuseStep 13873133 = 5202425) B5202425
theorem B3512089 : Blo 1441540 3512089 := bstep (se 2 (by rfl) ⟨1317033, by rfl⟩ : syracuseStep 3512089 = 2634067) B2634067
theorem B3651551 : Blo 1441540 3651551 := bstep (se 1 (by rfl) ⟨2738663, by rfl⟩ : syracuseStep 3651551 = 5477327) B5477327
theorem B1825735 : Blo 1441540 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B1850527 : Blo 1441540 1850527 := bstep (se 1 (by rfl) ⟨1387895, by rfl⟩ : syracuseStep 1850527 = 2775791) B2775791
theorem B15203837 : Blo 1441540 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B2433017 : Blo 1441540 2433017 := bstep (se 2 (by rfl) ⟨912381, by rfl⟩ : syracuseStep 2433017 = 1824763) B1824763
theorem B2162795 : Blo 1441540 2162795 := bstep (se 1 (by rfl) ⟨1622096, by rfl⟩ : syracuseStep 2162795 = 3244193) B3244193
theorem B6160711 : Blo 1441540 6160711 := bstep (se 1 (by rfl) ⟨4620533, by rfl⟩ : syracuseStep 6160711 = 9241067) B9241067
theorem B1442847 : Blo 1441540 1442847 := bstep (se 1 (by rfl) ⟨1082135, by rfl⟩ : syracuseStep 1442847 = 2164271) B2164271
theorem B2434313 : Blo 1441540 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B2434367 : Blo 1441540 2434367 := bstep (se 1 (by rfl) ⟨1825775, by rfl⟩ : syracuseStep 2434367 = 3651551) B3651551
theorem B1443263 : Blo 1441540 1443263 := bstep (se 1 (by rfl) ⟨1082447, by rfl⟩ : syracuseStep 1443263 = 2164895) B2164895
theorem B2467369 : Blo 1441540 2467369 := bstep (se 2 (by rfl) ⟨925263, by rfl⟩ : syracuseStep 2467369 = 1850527) B1850527
theorem B3245615 : Blo 1441540 3245615 := bstep (se 1 (by rfl) ⟨2434211, by rfl⟩ : syracuseStep 3245615 = 4868423) B4868423
theorem B3245993 : Blo 1441540 3245993 := bstep (se 2 (by rfl) ⟨1217247, by rfl⟩ : syracuseStep 3245993 = 2434495) B2434495
theorem B2164799 : Blo 1441540 2164799 := bstep (se 1 (by rfl) ⟨1623599, by rfl⟩ : syracuseStep 2164799 = 3247199) B3247199
theorem B10135891 : Blo 1441540 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B5196415 : Blo 1441540 5196415 := bstep (se 1 (by rfl) ⟨3897311, by rfl⟩ : syracuseStep 5196415 = 7794623) B7794623
theorem B7302311 : Blo 1441540 7302311 := bstep (se 1 (by rfl) ⟨5476733, by rfl⟩ : syracuseStep 7302311 = 10953467) B10953467
theorem B31174591 : Blo 1441540 31174591 := bstep (se 1 (by rfl) ⟨23380943, by rfl⟩ : syracuseStep 31174591 = 46761887) B46761887
theorem B4682785 : Blo 1441540 4682785 := bstep (se 2 (by rfl) ⟨1756044, by rfl⟩ : syracuseStep 4682785 = 3512089) B3512089
theorem B17782361 : Blo 1441540 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B11098235 : Blo 1441540 11098235 := bstep (se 1 (by rfl) ⟨8323676, by rfl⟩ : syracuseStep 11098235 = 16647353) B16647353
theorem B1622011 : Blo 1441540 1622011 := bstep (se 1 (by rfl) ⟨1216508, by rfl⟩ : syracuseStep 1622011 = 2433017) B2433017
theorem B9248755 : Blo 1441540 9248755 := bstep (se 1 (by rfl) ⟨6936566, by rfl⟩ : syracuseStep 9248755 = 13873133) B13873133
theorem B1441863 : Blo 1441540 1441863 := bstep (se 1 (by rfl) ⟨1081397, by rfl⟩ : syracuseStep 1441863 = 2162795) B2162795
theorem B1622875 : Blo 1441540 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B1622911 : Blo 1441540 1622911 := bstep (se 1 (by rfl) ⟨1217183, by rfl⟩ : syracuseStep 1622911 = 2434367) B2434367
theorem B2163743 : Blo 1441540 2163743 := bstep (se 1 (by rfl) ⟨1622807, by rfl⟩ : syracuseStep 2163743 = 3245615) B3245615
theorem B11854907 : Blo 1441540 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B2163995 : Blo 1441540 2163995 := bstep (se 1 (by rfl) ⟨1622996, by rfl⟩ : syracuseStep 2163995 = 3245993) B3245993
theorem B1443199 : Blo 1441540 1443199 := bstep (se 1 (by rfl) ⟨1082399, by rfl⟩ : syracuseStep 1443199 = 2164799) B2164799
theorem B6243713 : Blo 1441540 6243713 := bstep (se 2 (by rfl) ⟨2341392, by rfl⟩ : syracuseStep 6243713 = 4682785) B4682785
theorem B7398823 : Blo 1441540 7398823 := bstep (se 1 (by rfl) ⟨5549117, by rfl⟩ : syracuseStep 7398823 = 11098235) B11098235
theorem B2162681 : Blo 1441540 2162681 := bstep (se 2 (by rfl) ⟨811005, by rfl⟩ : syracuseStep 2162681 = 1622011) B1622011
theorem B4868207 : Blo 1441540 4868207 := bstep (se 1 (by rfl) ⟨3651155, by rfl⟩ : syracuseStep 4868207 = 7302311) B7302311
theorem B12331673 : Blo 1441540 12331673 := bstep (se 2 (by rfl) ⟨4624377, by rfl⟩ : syracuseStep 12331673 = 9248755) B9248755
theorem B3289825 : Blo 1441540 3289825 := bstep (se 2 (by rfl) ⟨1233684, by rfl⟩ : syracuseStep 3289825 = 2467369) B2467369
theorem B8214281 : Blo 1441540 8214281 := bstep (se 2 (by rfl) ⟨3080355, by rfl⟩ : syracuseStep 8214281 = 6160711) B6160711
theorem B13514521 : Blo 1441540 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B6928553 : Blo 1441540 6928553 := bstep (se 2 (by rfl) ⟨2598207, by rfl⟩ : syracuseStep 6928553 = 5196415) B5196415
theorem B41566121 : Blo 1441540 41566121 := bstep (se 2 (by rfl) ⟨15587295, by rfl⟩ : syracuseStep 41566121 = 31174591) B31174591
theorem B1442495 : Blo 1441540 1442495 := bstep (se 1 (by rfl) ⟨1081871, by rfl⟩ : syracuseStep 1442495 = 2163743) B2163743
theorem B1442663 : Blo 1441540 1442663 := bstep (se 1 (by rfl) ⟨1081997, by rfl⟩ : syracuseStep 1442663 = 2163995) B2163995
theorem B4162475 : Blo 1441540 4162475 := bstep (se 1 (by rfl) ⟨3121856, by rfl⟩ : syracuseStep 4162475 = 6243713) B6243713
theorem B2163833 : Blo 1441540 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B2163881 : Blo 1441540 2163881 := bstep (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) B1622911
theorem B3245471 : Blo 1441540 3245471 := bstep (se 1 (by rfl) ⟨2434103, by rfl⟩ : syracuseStep 3245471 = 4868207) B4868207
theorem B9865097 : Blo 1441540 9865097 := bstep (se 2 (by rfl) ⟨3699411, by rfl⟩ : syracuseStep 9865097 = 7398823) B7398823
theorem B5476187 : Blo 1441540 5476187 := bstep (se 1 (by rfl) ⟨4107140, by rfl⟩ : syracuseStep 5476187 = 8214281) B8214281
theorem B1441787 : Blo 1441540 1441787 := bstep (se 1 (by rfl) ⟨1081340, by rfl⟩ : syracuseStep 1441787 = 2162681) B2162681
theorem B8221115 : Blo 1441540 8221115 := bstep (se 1 (by rfl) ⟨6165836, by rfl⟩ : syracuseStep 8221115 = 12331673) B12331673
theorem B18019361 : Blo 1441540 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B27710747 : Blo 1441540 27710747 := bstep (se 1 (by rfl) ⟨20783060, by rfl⟩ : syracuseStep 27710747 = 41566121) B41566121
theorem B7903271 : Blo 1441540 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B17545733 : Blo 1441540 17545733 := bstep (se 4 (by rfl) ⟨1644912, by rfl⟩ : syracuseStep 17545733 = 3289825) B3289825
theorem B4619035 : Blo 1441540 4619035 := bstep (se 1 (by rfl) ⟨3464276, by rfl⟩ : syracuseStep 4619035 = 6928553) B6928553
theorem B5480743 : Blo 1441540 5480743 := bstep (se 1 (by rfl) ⟨4110557, by rfl⟩ : syracuseStep 5480743 = 8221115) B8221115
theorem B1442555 : Blo 1441540 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B1442587 : Blo 1441540 1442587 := bstep (se 1 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 1442587 = 2163881) B2163881
theorem B18473831 : Blo 1441540 18473831 := bstep (se 1 (by rfl) ⟨13855373, by rfl⟩ : syracuseStep 18473831 = 27710747) B27710747
theorem B2163647 : Blo 1441540 2163647 := bstep (se 1 (by rfl) ⟨1622735, by rfl⟩ : syracuseStep 2163647 = 3245471) B3245471
theorem B5268847 : Blo 1441540 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B12012907 : Blo 1441540 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B3650791 : Blo 1441540 3650791 := bstep (se 1 (by rfl) ⟨2738093, by rfl⟩ : syracuseStep 3650791 = 5476187) B5476187
theorem B2774983 : Blo 1441540 2774983 := bstep (se 1 (by rfl) ⟨2081237, by rfl⟩ : syracuseStep 2774983 = 4162475) B4162475
theorem B6158713 : Blo 1441540 6158713 := bstep (se 2 (by rfl) ⟨2309517, by rfl⟩ : syracuseStep 6158713 = 4619035) B4619035
theorem B6576731 : Blo 1441540 6576731 := bstep (se 1 (by rfl) ⟨4932548, by rfl⟩ : syracuseStep 6576731 = 9865097) B9865097
theorem B11697155 : Blo 1441540 11697155 := bstep (se 1 (by rfl) ⟨8772866, by rfl⟩ : syracuseStep 11697155 = 17545733) B17545733
theorem B7307657 : Blo 1441540 7307657 := bstep (se 2 (by rfl) ⟨2740371, by rfl⟩ : syracuseStep 7307657 = 5480743) B5480743
theorem B1442431 : Blo 1441540 1442431 := bstep (se 1 (by rfl) ⟨1081823, by rfl⟩ : syracuseStep 1442431 = 2163647) B2163647
theorem B4867721 : Blo 1441540 4867721 := bstep (se 2 (by rfl) ⟨1825395, by rfl⟩ : syracuseStep 4867721 = 3650791) B3650791
theorem B4384487 : Blo 1441540 4384487 := bstep (se 1 (by rfl) ⟨3288365, by rfl⟩ : syracuseStep 4384487 = 6576731) B6576731
theorem B16017209 : Blo 1441540 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B8211617 : Blo 1441540 8211617 := bstep (se 2 (by rfl) ⟨3079356, by rfl⟩ : syracuseStep 8211617 = 6158713) B6158713
theorem B12315887 : Blo 1441540 12315887 := bstep (se 1 (by rfl) ⟨9236915, by rfl⟩ : syracuseStep 12315887 = 18473831) B18473831
theorem B7025129 : Blo 1441540 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B3699977 : Blo 1441540 3699977 := bstep (se 2 (by rfl) ⟨1387491, by rfl⟩ : syracuseStep 3699977 = 2774983) B2774983
theorem B7798103 : Blo 1441540 7798103 := bstep (se 1 (by rfl) ⟨5848577, by rfl⟩ : syracuseStep 7798103 = 11697155) B11697155
theorem B3245147 : Blo 1441540 3245147 := bstep (se 1 (by rfl) ⟨2433860, by rfl⟩ : syracuseStep 3245147 = 4867721) B4867721
theorem B11691965 : Blo 1441540 11691965 := bstep (se 3 (by rfl) ⟨2192243, by rfl⟩ : syracuseStep 11691965 = 4384487) B4384487
theorem B5474411 : Blo 1441540 5474411 := bstep (se 1 (by rfl) ⟨4105808, by rfl⟩ : syracuseStep 5474411 = 8211617) B8211617
theorem B8210591 : Blo 1441540 8210591 := bstep (se 1 (by rfl) ⟨6157943, by rfl⟩ : syracuseStep 8210591 = 12315887) B12315887
theorem B9866605 : Blo 1441540 9866605 := bstep (se 3 (by rfl) ⟨1849988, by rfl⟩ : syracuseStep 9866605 = 3699977) B3699977
theorem B10678139 : Blo 1441540 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B5198735 : Blo 1441540 5198735 := bstep (se 1 (by rfl) ⟨3899051, by rfl⟩ : syracuseStep 5198735 = 7798103) B7798103
theorem B4871771 : Blo 1441540 4871771 := bstep (se 1 (by rfl) ⟨3653828, by rfl⟩ : syracuseStep 4871771 = 7307657) B7307657
theorem B4683419 : Blo 1441540 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B3465823 : Blo 1441540 3465823 := bstep (se 1 (by rfl) ⟨2599367, by rfl⟩ : syracuseStep 3465823 = 5198735) B5198735
theorem B2163431 : Blo 1441540 2163431 := bstep (se 1 (by rfl) ⟨1622573, by rfl⟩ : syracuseStep 2163431 = 3245147) B3245147
theorem B3122279 : Blo 1441540 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B5473727 : Blo 1441540 5473727 := bstep (se 1 (by rfl) ⟨4105295, by rfl⟩ : syracuseStep 5473727 = 8210591) B8210591
theorem B3247847 : Blo 1441540 3247847 := bstep (se 1 (by rfl) ⟨2435885, by rfl⟩ : syracuseStep 3247847 = 4871771) B4871771
theorem B7794643 : Blo 1441540 7794643 := bstep (se 1 (by rfl) ⟨5845982, by rfl⟩ : syracuseStep 7794643 = 11691965) B11691965
theorem B3649607 : Blo 1441540 3649607 := bstep (se 1 (by rfl) ⟨2737205, by rfl⟩ : syracuseStep 3649607 = 5474411) B5474411
theorem B13155473 : Blo 1441540 13155473 := bstep (se 2 (by rfl) ⟨4933302, by rfl⟩ : syracuseStep 13155473 = 9866605) B9866605
theorem B7118759 : Blo 1441540 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B2433071 : Blo 1441540 2433071 := bstep (se 1 (by rfl) ⟨1824803, by rfl⟩ : syracuseStep 2433071 = 3649607) B3649607
theorem B1442287 : Blo 1441540 1442287 := bstep (se 1 (by rfl) ⟨1081715, by rfl⟩ : syracuseStep 1442287 = 2163431) B2163431
theorem B2081519 : Blo 1441540 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B4621097 : Blo 1441540 4621097 := bstep (se 2 (by rfl) ⟨1732911, by rfl⟩ : syracuseStep 4621097 = 3465823) B3465823
theorem B18983357 : Blo 1441540 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B2165231 : Blo 1441540 2165231 := bstep (se 1 (by rfl) ⟨1623923, by rfl⟩ : syracuseStep 2165231 = 3247847) B3247847
theorem B3649151 : Blo 1441540 3649151 := bstep (se 1 (by rfl) ⟨2736863, by rfl⟩ : syracuseStep 3649151 = 5473727) B5473727
theorem B8770315 : Blo 1441540 8770315 := bstep (se 1 (by rfl) ⟨6577736, by rfl⟩ : syracuseStep 8770315 = 13155473) B13155473
theorem B10392857 : Blo 1441540 10392857 := bstep (se 2 (by rfl) ⟨3897321, by rfl⟩ : syracuseStep 10392857 = 7794643) B7794643
theorem B1622047 : Blo 1441540 1622047 := bstep (se 1 (by rfl) ⟨1216535, by rfl⟩ : syracuseStep 1622047 = 2433071) B2433071
theorem B1443487 : Blo 1441540 1443487 := bstep (se 1 (by rfl) ⟨1082615, by rfl⟩ : syracuseStep 1443487 = 2165231) B2165231
theorem B12322925 : Blo 1441540 12322925 := bstep (se 3 (by rfl) ⟨2310548, by rfl⟩ : syracuseStep 12322925 = 4621097) B4621097
theorem B22202869 : Blo 1441540 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B11693753 : Blo 1441540 11693753 := bstep (se 2 (by rfl) ⟨4385157, by rfl⟩ : syracuseStep 11693753 = 8770315) B8770315
theorem B6928571 : Blo 1441540 6928571 := bstep (se 1 (by rfl) ⟨5196428, by rfl⟩ : syracuseStep 6928571 = 10392857) B10392857
theorem B12655571 : Blo 1441540 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B2432767 : Blo 1441540 2432767 := bstep (se 1 (by rfl) ⟨1824575, by rfl⟩ : syracuseStep 2432767 = 3649151) B3649151
theorem B2162729 : Blo 1441540 2162729 := bstep (se 2 (by rfl) ⟨811023, by rfl⟩ : syracuseStep 2162729 = 1622047) B1622047
theorem B134992757 : Blo 1441540 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B7795835 : Blo 1441540 7795835 := bstep (se 1 (by rfl) ⟨5846876, by rfl⟩ : syracuseStep 7795835 = 11693753) B11693753
theorem B29603825 : Blo 1441540 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B8215283 : Blo 1441540 8215283 := bstep (se 1 (by rfl) ⟨6161462, by rfl⟩ : syracuseStep 8215283 = 12322925) B12322925
theorem B4619047 : Blo 1441540 4619047 := bstep (se 1 (by rfl) ⟨3464285, by rfl⟩ : syracuseStep 4619047 = 6928571) B6928571
theorem B3243689 : Blo 1441540 3243689 := bstep (se 2 (by rfl) ⟨1216383, by rfl⟩ : syracuseStep 3243689 = 2432767) B2432767
theorem B1441819 : Blo 1441540 1441819 := bstep (se 1 (by rfl) ⟨1081364, by rfl⟩ : syracuseStep 1441819 = 2162729) B2162729
theorem B19735883 : Blo 1441540 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B5197223 : Blo 1441540 5197223 := bstep (se 1 (by rfl) ⟨3897917, by rfl⟩ : syracuseStep 5197223 = 7795835) B7795835
theorem B5476855 : Blo 1441540 5476855 := bstep (se 1 (by rfl) ⟨4107641, by rfl⟩ : syracuseStep 5476855 = 8215283) B8215283
theorem B89995171 : Blo 1441540 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B6158729 : Blo 1441540 6158729 := bstep (se 2 (by rfl) ⟨2309523, by rfl⟩ : syracuseStep 6158729 = 4619047) B4619047
theorem B2162459 : Blo 1441540 2162459 := bstep (se 1 (by rfl) ⟨1621844, by rfl⟩ : syracuseStep 2162459 = 3243689) B3243689
theorem B13157255 : Blo 1441540 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B4105819 : Blo 1441540 4105819 := bstep (se 1 (by rfl) ⟨3079364, by rfl⟩ : syracuseStep 4105819 = 6158729) B6158729
theorem B7302473 : Blo 1441540 7302473 := bstep (se 2 (by rfl) ⟨2738427, by rfl⟩ : syracuseStep 7302473 = 5476855) B5476855
theorem B119993561 : Blo 1441540 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B13859261 : Blo 1441540 13859261 := bstep (se 3 (by rfl) ⟨2598611, by rfl⟩ : syracuseStep 13859261 = 5197223) B5197223
theorem B1441639 : Blo 1441540 1441639 := bstep (se 1 (by rfl) ⟨1081229, by rfl⟩ : syracuseStep 1441639 = 2162459) B2162459
theorem B79995707 : Blo 1441540 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B5474425 : Blo 1441540 5474425 := bstep (se 2 (by rfl) ⟨2052909, by rfl⟩ : syracuseStep 5474425 = 4105819) B4105819
theorem B4868315 : Blo 1441540 4868315 := bstep (se 1 (by rfl) ⟨3651236, by rfl⟩ : syracuseStep 4868315 = 7302473) B7302473
theorem B8771503 : Blo 1441540 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B9239507 : Blo 1441540 9239507 := bstep (se 1 (by rfl) ⟨6929630, by rfl⟩ : syracuseStep 9239507 = 13859261) B13859261
theorem B7299233 : Blo 1441540 7299233 := bstep (se 2 (by rfl) ⟨2737212, by rfl⟩ : syracuseStep 7299233 = 5474425) B5474425
theorem B53330471 : Blo 1441540 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B3245543 : Blo 1441540 3245543 := bstep (se 1 (by rfl) ⟨2434157, by rfl⟩ : syracuseStep 3245543 = 4868315) B4868315
theorem B11695337 : Blo 1441540 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B6159671 : Blo 1441540 6159671 := bstep (se 1 (by rfl) ⟨4619753, by rfl⟩ : syracuseStep 6159671 = 9239507) B9239507
theorem B4866155 : Blo 1441540 4866155 := bstep (se 1 (by rfl) ⟨3649616, by rfl⟩ : syracuseStep 4866155 = 7299233) B7299233
theorem B35553647 : Blo 1441540 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B2163695 : Blo 1441540 2163695 := bstep (se 1 (by rfl) ⟨1622771, by rfl⟩ : syracuseStep 2163695 = 3245543) B3245543
theorem B4106447 : Blo 1441540 4106447 := bstep (se 1 (by rfl) ⟨3079835, by rfl⟩ : syracuseStep 4106447 = 6159671) B6159671
theorem B7796891 : Blo 1441540 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B3244103 : Blo 1441540 3244103 := bstep (se 1 (by rfl) ⟨2433077, by rfl⟩ : syracuseStep 3244103 = 4866155) B4866155
theorem B1442463 : Blo 1441540 1442463 := bstep (se 1 (by rfl) ⟨1081847, by rfl⟩ : syracuseStep 1442463 = 2163695) B2163695
theorem B2737631 : Blo 1441540 2737631 := bstep (se 1 (by rfl) ⟨2053223, by rfl⟩ : syracuseStep 2737631 = 4106447) B4106447
theorem B23702431 : Blo 1441540 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B5197927 : Blo 1441540 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B2162735 : Blo 1441540 2162735 := bstep (se 1 (by rfl) ⟨1622051, by rfl⟩ : syracuseStep 2162735 = 3244103) B3244103
theorem B6930569 : Blo 1441540 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B1825087 : Blo 1441540 1825087 := bstep (se 1 (by rfl) ⟨1368815, by rfl⟩ : syracuseStep 1825087 = 2737631) B2737631
theorem B31603241 : Blo 1441540 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B1441823 : Blo 1441540 1441823 := bstep (se 1 (by rfl) ⟨1081367, by rfl⟩ : syracuseStep 1441823 = 2162735) B2162735
theorem B18481517 : Blo 1441540 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B2433449 : Blo 1441540 2433449 := bstep (se 2 (by rfl) ⟨912543, by rfl⟩ : syracuseStep 2433449 = 1825087) B1825087
theorem B84275309 : Blo 1441540 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B12321011 : Blo 1441540 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B1622299 : Blo 1441540 1622299 := bstep (se 1 (by rfl) ⟨1216724, by rfl⟩ : syracuseStep 1622299 = 2433449) B2433449
theorem B56183539 : Blo 1441540 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B2163065 : Blo 1441540 2163065 := bstep (se 2 (by rfl) ⟨811149, by rfl⟩ : syracuseStep 2163065 = 1622299) B1622299
theorem B74911385 : Blo 1441540 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B8214007 : Blo 1441540 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B1442043 : Blo 1441540 1442043 := bstep (se 1 (by rfl) ⟨1081532, by rfl⟩ : syracuseStep 1442043 = 2163065) B2163065
theorem B49940923 : Blo 1441540 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B10952009 : Blo 1441540 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B7301339 : Blo 1441540 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B66587897 : Blo 1441540 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B4867559 : Blo 1441540 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B44391931 : Blo 1441540 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B3245039 : Blo 1441540 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B947027861 : Blo 1441540 947027861 := bstep (se 6 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 947027861 = 44391931) B44391931
theorem B2163359 : Blo 1441540 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B631351907 : Blo 1441540 631351907 := bstep (se 1 (by rfl) ⟨473513930, by rfl⟩ : syracuseStep 631351907 = 947027861) B947027861
theorem B1442239 : Blo 1441540 1442239 := bstep (se 1 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 1442239 = 2163359) B2163359
theorem B420901271 : Blo 1441540 420901271 := bstep (se 1 (by rfl) ⟨315675953, by rfl⟩ : syracuseStep 420901271 = 631351907) B631351907
theorem B280600847 : Blo 1441540 280600847 := bstep (se 1 (by rfl) ⟨210450635, by rfl⟩ : syracuseStep 280600847 = 420901271) B420901271
theorem B187067231 : Blo 1441540 187067231 := bstep (se 1 (by rfl) ⟨140300423, by rfl⟩ : syracuseStep 187067231 = 280600847) B280600847
theorem B124711487 : Blo 1441540 124711487 := bstep (se 1 (by rfl) ⟨93533615, by rfl⟩ : syracuseStep 124711487 = 187067231) B187067231
theorem B83140991 : Blo 1441540 83140991 := bstep (se 1 (by rfl) ⟨62355743, by rfl⟩ : syracuseStep 83140991 = 124711487) B124711487
theorem B55427327 : Blo 1441540 55427327 := bstep (se 1 (by rfl) ⟨41570495, by rfl⟩ : syracuseStep 55427327 = 83140991) B83140991
theorem B36951551 : Blo 1441540 36951551 := bstep (se 1 (by rfl) ⟨27713663, by rfl⟩ : syracuseStep 36951551 = 55427327) B55427327
theorem B24634367 : Blo 1441540 24634367 := bstep (se 1 (by rfl) ⟨18475775, by rfl⟩ : syracuseStep 24634367 = 36951551) B36951551
theorem B16422911 : Blo 1441540 16422911 := bstep (se 1 (by rfl) ⟨12317183, by rfl⟩ : syracuseStep 16422911 = 24634367) B24634367
theorem B10948607 : Blo 1441540 10948607 := bstep (se 1 (by rfl) ⟨8211455, by rfl⟩ : syracuseStep 10948607 = 16422911) B16422911
theorem B7299071 : Blo 1441540 7299071 := bstep (se 1 (by rfl) ⟨5474303, by rfl⟩ : syracuseStep 7299071 = 10948607) B10948607
theorem B4866047 : Blo 1441540 4866047 := bstep (se 1 (by rfl) ⟨3649535, by rfl⟩ : syracuseStep 4866047 = 7299071) B7299071
theorem B3244031 : Blo 1441540 3244031 := bstep (se 1 (by rfl) ⟨2433023, by rfl⟩ : syracuseStep 3244031 = 4866047) B4866047
theorem B2162687 : Blo 1441540 2162687 := bstep (se 1 (by rfl) ⟨1622015, by rfl⟩ : syracuseStep 2162687 = 3244031) B3244031
theorem B1441791 : Blo 1441540 1441791 := bstep (se 1 (by rfl) ⟨1081343, by rfl⟩ : syracuseStep 1441791 = 2162687) B2162687

theorem C0 (j : ℕ) (h1 : 360385 ≤ j) (h2 : j ≤ 360884) : Blo 1441540 (4 * j + 3) := by
  interval_cases j
  · exact B1441543
  · exact B1441547
  · exact B1441551
  · exact B1441555
  · exact B1441559
  · exact B1441563
  · exact B1441567
  · exact B1441571
  · exact B1441575
  · exact B1441579
  · exact B1441583
  · exact B1441587
  · exact B1441591
  · exact B1441595
  · exact B1441599
  · exact B1441603
  · exact B1441607
  · exact B1441611
  · exact B1441615
  · exact B1441619
  · exact B1441623
  · exact B1441627
  · exact B1441631
  · exact B1441635
  · exact B1441639
  · exact B1441643
  · exact B1441647
  · exact B1441651
  · exact B1441655
  · exact B1441659
  · exact B1441663
  · exact B1441667
  · exact B1441671
  · exact B1441675
  · exact B1441679
  · exact B1441683
  · exact B1441687
  · exact B1441691
  · exact B1441695
  · exact B1441699
  · exact B1441703
  · exact B1441707
  · exact B1441711
  · exact B1441715
  · exact B1441719
  · exact B1441723
  · exact B1441727
  · exact B1441731
  · exact B1441735
  · exact B1441739
  · exact B1441743
  · exact B1441747
  · exact B1441751
  · exact B1441755
  · exact B1441759
  · exact B1441763
  · exact B1441767
  · exact B1441771
  · exact B1441775
  · exact B1441779
  · exact B1441783
  · exact B1441787
  · exact B1441791
  · exact B1441795
  · exact B1441799
  · exact B1441803
  · exact B1441807
  · exact B1441811
  · exact B1441815
  · exact B1441819
  · exact B1441823
  · exact B1441827
  · exact B1441831
  · exact B1441835
  · exact B1441839
  · exact B1441843
  · exact B1441847
  · exact B1441851
  · exact B1441855
  · exact B1441859
  · exact B1441863
  · exact B1441867
  · exact B1441871
  · exact B1441875
  · exact B1441879
  · exact B1441883
  · exact B1441887
  · exact B1441891
  · exact B1441895
  · exact B1441899
  · exact B1441903
  · exact B1441907
  · exact B1441911
  · exact B1441915
  · exact B1441919
  · exact B1441923
  · exact B1441927
  · exact B1441931
  · exact B1441935
  · exact B1441939
  · exact B1441943
  · exact B1441947
  · exact B1441951
  · exact B1441955
  · exact B1441959
  · exact B1441963
  · exact B1441967
  · exact B1441971
  · exact B1441975
  · exact B1441979
  · exact B1441983
  · exact B1441987
  · exact B1441991
  · exact B1441995
  · exact B1441999
  · exact B1442003
  · exact B1442007
  · exact B1442011
  · exact B1442015
  · exact B1442019
  · exact B1442023
  · exact B1442027
  · exact B1442031
  · exact B1442035
  · exact B1442039
  · exact B1442043
  · exact B1442047
  · exact B1442051
  · exact B1442055
  · exact B1442059
  · exact B1442063
  · exact B1442067
  · exact B1442071
  · exact B1442075
  · exact B1442079
  · exact B1442083
  · exact B1442087
  · exact B1442091
  · exact B1442095
  · exact B1442099
  · exact B1442103
  · exact B1442107
  · exact B1442111
  · exact B1442115
  · exact B1442119
  · exact B1442123
  · exact B1442127
  · exact B1442131
  · exact B1442135
  · exact B1442139
  · exact B1442143
  · exact B1442147
  · exact B1442151
  · exact B1442155
  · exact B1442159
  · exact B1442163
  · exact B1442167
  · exact B1442171
  · exact B1442175
  · exact B1442179
  · exact B1442183
  · exact B1442187
  · exact B1442191
  · exact B1442195
  · exact B1442199
  · exact B1442203
  · exact B1442207
  · exact B1442211
  · exact B1442215
  · exact B1442219
  · exact B1442223
  · exact B1442227
  · exact B1442231
  · exact B1442235
  · exact B1442239
  · exact B1442243
  · exact B1442247
  · exact B1442251
  · exact B1442255
  · exact B1442259
  · exact B1442263
  · exact B1442267
  · exact B1442271
  · exact B1442275
  · exact B1442279
  · exact B1442283
  · exact B1442287
  · exact B1442291
  · exact B1442295
  · exact B1442299
  · exact B1442303
  · exact B1442307
  · exact B1442311
  · exact B1442315
  · exact B1442319
  · exact B1442323
  · exact B1442327
  · exact B1442331
  · exact B1442335
  · exact B1442339
  · exact B1442343
  · exact B1442347
  · exact B1442351
  · exact B1442355
  · exact B1442359
  · exact B1442363
  · exact B1442367
  · exact B1442371
  · exact B1442375
  · exact B1442379
  · exact B1442383
  · exact B1442387
  · exact B1442391
  · exact B1442395
  · exact B1442399
  · exact B1442403
  · exact B1442407
  · exact B1442411
  · exact B1442415
  · exact B1442419
  · exact B1442423
  · exact B1442427
  · exact B1442431
  · exact B1442435
  · exact B1442439
  · exact B1442443
  · exact B1442447
  · exact B1442451
  · exact B1442455
  · exact B1442459
  · exact B1442463
  · exact B1442467
  · exact B1442471
  · exact B1442475
  · exact B1442479
  · exact B1442483
  · exact B1442487
  · exact B1442491
  · exact B1442495
  · exact B1442499
  · exact B1442503
  · exact B1442507
  · exact B1442511
  · exact B1442515
  · exact B1442519
  · exact B1442523
  · exact B1442527
  · exact B1442531
  · exact B1442535
  · exact B1442539
  · exact B1442543
  · exact B1442547
  · exact B1442551
  · exact B1442555
  · exact B1442559
  · exact B1442563
  · exact B1442567
  · exact B1442571
  · exact B1442575
  · exact B1442579
  · exact B1442583
  · exact B1442587
  · exact B1442591
  · exact B1442595
  · exact B1442599
  · exact B1442603
  · exact B1442607
  · exact B1442611
  · exact B1442615
  · exact B1442619
  · exact B1442623
  · exact B1442627
  · exact B1442631
  · exact B1442635
  · exact B1442639
  · exact B1442643
  · exact B1442647
  · exact B1442651
  · exact B1442655
  · exact B1442659
  · exact B1442663
  · exact B1442667
  · exact B1442671
  · exact B1442675
  · exact B1442679
  · exact B1442683
  · exact B1442687
  · exact B1442691
  · exact B1442695
  · exact B1442699
  · exact B1442703
  · exact B1442707
  · exact B1442711
  · exact B1442715
  · exact B1442719
  · exact B1442723
  · exact B1442727
  · exact B1442731
  · exact B1442735
  · exact B1442739
  · exact B1442743
  · exact B1442747
  · exact B1442751
  · exact B1442755
  · exact B1442759
  · exact B1442763
  · exact B1442767
  · exact B1442771
  · exact B1442775
  · exact B1442779
  · exact B1442783
  · exact B1442787
  · exact B1442791
  · exact B1442795
  · exact B1442799
  · exact B1442803
  · exact B1442807
  · exact B1442811
  · exact B1442815
  · exact B1442819
  · exact B1442823
  · exact B1442827
  · exact B1442831
  · exact B1442835
  · exact B1442839
  · exact B1442843
  · exact B1442847
  · exact B1442851
  · exact B1442855
  · exact B1442859
  · exact B1442863
  · exact B1442867
  · exact B1442871
  · exact B1442875
  · exact B1442879
  · exact B1442883
  · exact B1442887
  · exact B1442891
  · exact B1442895
  · exact B1442899
  · exact B1442903
  · exact B1442907
  · exact B1442911
  · exact B1442915
  · exact B1442919
  · exact B1442923
  · exact B1442927
  · exact B1442931
  · exact B1442935
  · exact B1442939
  · exact B1442943
  · exact B1442947
  · exact B1442951
  · exact B1442955
  · exact B1442959
  · exact B1442963
  · exact B1442967
  · exact B1442971
  · exact B1442975
  · exact B1442979
  · exact B1442983
  · exact B1442987
  · exact B1442991
  · exact B1442995
  · exact B1442999
  · exact B1443003
  · exact B1443007
  · exact B1443011
  · exact B1443015
  · exact B1443019
  · exact B1443023
  · exact B1443027
  · exact B1443031
  · exact B1443035
  · exact B1443039
  · exact B1443043
  · exact B1443047
  · exact B1443051
  · exact B1443055
  · exact B1443059
  · exact B1443063
  · exact B1443067
  · exact B1443071
  · exact B1443075
  · exact B1443079
  · exact B1443083
  · exact B1443087
  · exact B1443091
  · exact B1443095
  · exact B1443099
  · exact B1443103
  · exact B1443107
  · exact B1443111
  · exact B1443115
  · exact B1443119
  · exact B1443123
  · exact B1443127
  · exact B1443131
  · exact B1443135
  · exact B1443139
  · exact B1443143
  · exact B1443147
  · exact B1443151
  · exact B1443155
  · exact B1443159
  · exact B1443163
  · exact B1443167
  · exact B1443171
  · exact B1443175
  · exact B1443179
  · exact B1443183
  · exact B1443187
  · exact B1443191
  · exact B1443195
  · exact B1443199
  · exact B1443203
  · exact B1443207
  · exact B1443211
  · exact B1443215
  · exact B1443219
  · exact B1443223
  · exact B1443227
  · exact B1443231
  · exact B1443235
  · exact B1443239
  · exact B1443243
  · exact B1443247
  · exact B1443251
  · exact B1443255
  · exact B1443259
  · exact B1443263
  · exact B1443267
  · exact B1443271
  · exact B1443275
  · exact B1443279
  · exact B1443283
  · exact B1443287
  · exact B1443291
  · exact B1443295
  · exact B1443299
  · exact B1443303
  · exact B1443307
  · exact B1443311
  · exact B1443315
  · exact B1443319
  · exact B1443323
  · exact B1443327
  · exact B1443331
  · exact B1443335
  · exact B1443339
  · exact B1443343
  · exact B1443347
  · exact B1443351
  · exact B1443355
  · exact B1443359
  · exact B1443363
  · exact B1443367
  · exact B1443371
  · exact B1443375
  · exact B1443379
  · exact B1443383
  · exact B1443387
  · exact B1443391
  · exact B1443395
  · exact B1443399
  · exact B1443403
  · exact B1443407
  · exact B1443411
  · exact B1443415
  · exact B1443419
  · exact B1443423
  · exact B1443427
  · exact B1443431
  · exact B1443435
  · exact B1443439
  · exact B1443443
  · exact B1443447
  · exact B1443451
  · exact B1443455
  · exact B1443459
  · exact B1443463
  · exact B1443467
  · exact B1443471
  · exact B1443475
  · exact B1443479
  · exact B1443483
  · exact B1443487
  · exact B1443491
  · exact B1443495
  · exact B1443499
  · exact B1443503
  · exact B1443507
  · exact B1443511
  · exact B1443515
  · exact B1443519
  · exact B1443523
  · exact B1443527
  · exact B1443531
  · exact B1443535
  · exact B1443539

theorem solution (m : ℕ) (hlo : 1441540 ≤ m) (hhi : m ≤ 1443540) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 360385 ≤ j := by omega
    have hj2 : j ≤ 360884 := by omega
    have hb : Blo 1441540 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
