-- Prove2me | solution 1 for syracuse_descends_range_678312_682312
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:54.483149+00:00
-- url     : https://prove2.me/submissions/bf1aacb8-16cc-4856-b0f1-e41f080bf560

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


theorem B3309605 : Blo 678312 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B1146973 : Blo 678312 1146973 := bbase (se 3 (by rfl) ⟨215057, by rfl⟩ : syracuseStep 1146973 = 430115) (by norm_num)
theorem B917605 : Blo 678312 917605 := bbase (se 4 (by rfl) ⟨86025, by rfl⟩ : syracuseStep 917605 = 172051) (by norm_num)
theorem B1933445 : Blo 678312 1933445 := bbase (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) (by norm_num)
theorem B1147061 : Blo 678312 1147061 := bbase (se 5 (by rfl) ⟨53768, by rfl⟩ : syracuseStep 1147061 = 107537) (by norm_num)
theorem B2293973 : Blo 678312 2293973 := bbase (se 7 (by rfl) ⟨26882, by rfl⟩ : syracuseStep 2293973 = 53765) (by norm_num)
theorem B1147189 : Blo 678312 1147189 := bbase (se 5 (by rfl) ⟨53774, by rfl⟩ : syracuseStep 1147189 = 107549) (by norm_num)
theorem B2589029 : Blo 678312 2589029 := bbase (se 4 (by rfl) ⟨242721, by rfl⟩ : syracuseStep 2589029 = 485443) (by norm_num)
theorem B1147277 : Blo 678312 1147277 := bbase (se 3 (by rfl) ⟨215114, by rfl⟩ : syracuseStep 1147277 = 430229) (by norm_num)
theorem B3277205 : Blo 678312 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B1147405 : Blo 678312 1147405 := bbase (se 3 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 1147405 = 430277) (by norm_num)
theorem B1147493 : Blo 678312 1147493 := bbase (se 4 (by rfl) ⟨107577, by rfl⟩ : syracuseStep 1147493 = 215155) (by norm_num)
theorem B2294405 : Blo 678312 2294405 := bbase (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) (by norm_num)
theorem B2589317 : Blo 678312 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B3441365 : Blo 678312 3441365 := bbase (se 7 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 3441365 = 80657) (by norm_num)
theorem B1147621 : Blo 678312 1147621 := bbase (se 4 (by rfl) ⟨107589, by rfl⟩ : syracuseStep 1147621 = 215179) (by norm_num)
theorem B1147709 : Blo 678312 1147709 := bbase (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) (by norm_num)
theorem B10617749 : Blo 678312 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B1147837 : Blo 678312 1147837 := bbase (se 3 (by rfl) ⟨215219, by rfl⟩ : syracuseStep 1147837 = 430439) (by norm_num)
theorem B1147925 : Blo 678312 1147925 := bbase (se 6 (by rfl) ⟨26904, by rfl⟩ : syracuseStep 1147925 = 53809) (by norm_num)
theorem B2294837 : Blo 678312 2294837 := bbase (se 5 (by rfl) ⟨107570, by rfl⟩ : syracuseStep 2294837 = 215141) (by norm_num)
theorem B1148053 : Blo 678312 1148053 := bbase (se 6 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 1148053 = 53815) (by norm_num)
theorem B1148141 : Blo 678312 1148141 := bbase (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) (by norm_num)
theorem B2622709 : Blo 678312 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B918821 : Blo 678312 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B1148269 : Blo 678312 1148269 := bbase (se 3 (by rfl) ⟨215300, by rfl⟩ : syracuseStep 1148269 = 430601) (by norm_num)
theorem B1148357 : Blo 678312 1148357 := bbase (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) (by norm_num)
theorem B2295269 : Blo 678312 2295269 := bbase (se 4 (by rfl) ⟨215181, by rfl⟩ : syracuseStep 2295269 = 430363) (by norm_num)
theorem B1148485 : Blo 678312 1148485 := bbase (se 4 (by rfl) ⟨107670, by rfl⟩ : syracuseStep 1148485 = 215341) (by norm_num)
theorem B1377901 : Blo 678312 1377901 := bbase (se 3 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 1377901 = 516713) (by norm_num)
theorem B1017485 : Blo 678312 1017485 := bbase (se 3 (by rfl) ⟨190778, by rfl⟩ : syracuseStep 1017485 = 381557) (by norm_num)
theorem B1148573 : Blo 678312 1148573 := bbase (se 3 (by rfl) ⟨215357, by rfl⟩ : syracuseStep 1148573 = 430715) (by norm_num)
theorem B1017509 : Blo 678312 1017509 := bbase (se 4 (by rfl) ⟨95391, by rfl⟩ : syracuseStep 1017509 = 190783) (by norm_num)
theorem B1935029 : Blo 678312 1935029 := bbase (se 5 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 1935029 = 181409) (by norm_num)
theorem B1017533 : Blo 678312 1017533 := bbase (se 3 (by rfl) ⟨190787, by rfl⟩ : syracuseStep 1017533 = 381575) (by norm_num)
theorem B1017557 : Blo 678312 1017557 := bbase (se 7 (by rfl) ⟨11924, by rfl⟩ : syracuseStep 1017557 = 23849) (by norm_num)
theorem B1017581 : Blo 678312 1017581 := bbase (se 3 (by rfl) ⟨190796, by rfl⟩ : syracuseStep 1017581 = 381593) (by norm_num)
theorem B1017605 : Blo 678312 1017605 := bbase (se 4 (by rfl) ⟨95400, by rfl⟩ : syracuseStep 1017605 = 190801) (by norm_num)
theorem B1017629 : Blo 678312 1017629 := bbase (se 3 (by rfl) ⟨190805, by rfl⟩ : syracuseStep 1017629 = 381611) (by norm_num)
theorem B1148701 : Blo 678312 1148701 := bbase (se 3 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 1148701 = 430763) (by norm_num)
theorem B2590501 : Blo 678312 2590501 := bbase (se 4 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 2590501 = 485719) (by norm_num)
theorem B1017653 : Blo 678312 1017653 := bbase (se 5 (by rfl) ⟨47702, by rfl⟩ : syracuseStep 1017653 = 95405) (by norm_num)
theorem B1017677 : Blo 678312 1017677 := bbase (se 3 (by rfl) ⟨190814, by rfl⟩ : syracuseStep 1017677 = 381629) (by norm_num)
theorem B1017701 : Blo 678312 1017701 := bbase (se 4 (by rfl) ⟨95409, by rfl⟩ : syracuseStep 1017701 = 190819) (by norm_num)
theorem B1148789 : Blo 678312 1148789 := bbase (se 5 (by rfl) ⟨53849, by rfl⟩ : syracuseStep 1148789 = 107699) (by norm_num)
theorem B1017725 : Blo 678312 1017725 := bbase (se 3 (by rfl) ⟨190823, by rfl⟩ : syracuseStep 1017725 = 381647) (by norm_num)
theorem B1017749 : Blo 678312 1017749 := bbase (se 6 (by rfl) ⟨23853, by rfl⟩ : syracuseStep 1017749 = 47707) (by norm_num)
theorem B2295701 : Blo 678312 2295701 := bbase (se 6 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 2295701 = 107611) (by norm_num)
theorem B1017773 : Blo 678312 1017773 := bbase (se 3 (by rfl) ⟨190832, by rfl⟩ : syracuseStep 1017773 = 381665) (by norm_num)
theorem B690097 : Blo 678312 690097 := bbase (se 2 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 690097 = 517573) (by norm_num)
theorem B1017797 : Blo 678312 1017797 := bbase (se 4 (by rfl) ⟨95418, by rfl⟩ : syracuseStep 1017797 = 190837) (by norm_num)
theorem B1017821 : Blo 678312 1017821 := bbase (se 3 (by rfl) ⟨190841, by rfl⟩ : syracuseStep 1017821 = 381683) (by norm_num)
theorem B3442661 : Blo 678312 3442661 := bbase (se 4 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 3442661 = 645499) (by norm_num)
theorem B1017845 : Blo 678312 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B1148917 : Blo 678312 1148917 := bbase (se 5 (by rfl) ⟨53855, by rfl⟩ : syracuseStep 1148917 = 107711) (by norm_num)
theorem B1017869 : Blo 678312 1017869 := bbase (se 3 (by rfl) ⟨190850, by rfl⟩ : syracuseStep 1017869 = 381701) (by norm_num)
theorem B1017893 : Blo 678312 1017893 := bbase (se 4 (by rfl) ⟨95427, by rfl⟩ : syracuseStep 1017893 = 190855) (by norm_num)
theorem B1017917 : Blo 678312 1017917 := bbase (se 3 (by rfl) ⟨190859, by rfl⟩ : syracuseStep 1017917 = 381719) (by norm_num)
theorem B919621 : Blo 678312 919621 := bbase (se 4 (by rfl) ⟨86214, by rfl⟩ : syracuseStep 919621 = 172429) (by norm_num)
theorem B1149005 : Blo 678312 1149005 := bbase (se 3 (by rfl) ⟨215438, by rfl⟩ : syracuseStep 1149005 = 430877) (by norm_num)
theorem B1017941 : Blo 678312 1017941 := bbase (se 8 (by rfl) ⟨5964, by rfl⟩ : syracuseStep 1017941 = 11929) (by norm_num)
theorem B1017965 : Blo 678312 1017965 := bbase (se 3 (by rfl) ⟨190868, by rfl⟩ : syracuseStep 1017965 = 381737) (by norm_num)
theorem B1017989 : Blo 678312 1017989 := bbase (se 4 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 1017989 = 190873) (by norm_num)
theorem B1018013 : Blo 678312 1018013 := bbase (se 3 (by rfl) ⟨190877, by rfl⟩ : syracuseStep 1018013 = 381755) (by norm_num)
theorem B1018037 : Blo 678312 1018037 := bbase (se 5 (by rfl) ⟨47720, by rfl⟩ : syracuseStep 1018037 = 95441) (by norm_num)
theorem B1018061 : Blo 678312 1018061 := bbase (se 3 (by rfl) ⟨190886, by rfl⟩ : syracuseStep 1018061 = 381773) (by norm_num)
theorem B1149133 : Blo 678312 1149133 := bbase (se 3 (by rfl) ⟨215462, by rfl⟩ : syracuseStep 1149133 = 430925) (by norm_num)
theorem B1018085 : Blo 678312 1018085 := bbase (se 4 (by rfl) ⟨95445, by rfl⟩ : syracuseStep 1018085 = 190891) (by norm_num)
theorem B1837285 : Blo 678312 1837285 := bbase (se 4 (by rfl) ⟨172245, by rfl⟩ : syracuseStep 1837285 = 344491) (by norm_num)
theorem B1018109 : Blo 678312 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B1018133 : Blo 678312 1018133 := bbase (se 6 (by rfl) ⟨23862, by rfl⟩ : syracuseStep 1018133 = 47725) (by norm_num)
theorem B1149221 : Blo 678312 1149221 := bbase (se 4 (by rfl) ⟨107739, by rfl⟩ : syracuseStep 1149221 = 215479) (by norm_num)
theorem B1018157 : Blo 678312 1018157 := bbase (se 3 (by rfl) ⟨190904, by rfl⟩ : syracuseStep 1018157 = 381809) (by norm_num)
theorem B1018181 : Blo 678312 1018181 := bbase (se 4 (by rfl) ⟨95454, by rfl⟩ : syracuseStep 1018181 = 190909) (by norm_num)
theorem B2296133 : Blo 678312 2296133 := bbase (se 4 (by rfl) ⟨215262, by rfl⟩ : syracuseStep 2296133 = 430525) (by norm_num)
theorem B1935701 : Blo 678312 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B1018205 : Blo 678312 1018205 := bbase (se 3 (by rfl) ⟨190913, by rfl⟩ : syracuseStep 1018205 = 381827) (by norm_num)
theorem B1018229 : Blo 678312 1018229 := bbase (se 5 (by rfl) ⟨47729, by rfl⟩ : syracuseStep 1018229 = 95459) (by norm_num)
theorem B2623861 : Blo 678312 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B1018253 : Blo 678312 1018253 := bbase (se 3 (by rfl) ⟨190922, by rfl⟩ : syracuseStep 1018253 = 381845) (by norm_num)
theorem B1018277 : Blo 678312 1018277 := bbase (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) (by norm_num)
theorem B1149349 : Blo 678312 1149349 := bbase (se 4 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 1149349 = 215503) (by norm_num)
theorem B1018301 : Blo 678312 1018301 := bbase (se 3 (by rfl) ⟨190931, by rfl⟩ : syracuseStep 1018301 = 381863) (by norm_num)
theorem B1018325 : Blo 678312 1018325 := bbase (se 7 (by rfl) ⟨11933, by rfl⟩ : syracuseStep 1018325 = 23867) (by norm_num)
theorem B1018349 : Blo 678312 1018349 := bbase (se 3 (by rfl) ⟨190940, by rfl⟩ : syracuseStep 1018349 = 381881) (by norm_num)
theorem B1149437 : Blo 678312 1149437 := bbase (se 3 (by rfl) ⟨215519, by rfl⟩ : syracuseStep 1149437 = 431039) (by norm_num)
theorem B1018373 : Blo 678312 1018373 := bbase (se 4 (by rfl) ⟨95472, by rfl⟩ : syracuseStep 1018373 = 190945) (by norm_num)
theorem B1018397 : Blo 678312 1018397 := bbase (se 3 (by rfl) ⟨190949, by rfl⟩ : syracuseStep 1018397 = 381899) (by norm_num)
theorem B1018421 : Blo 678312 1018421 := bbase (se 5 (by rfl) ⟨47738, by rfl⟩ : syracuseStep 1018421 = 95477) (by norm_num)
theorem B1018445 : Blo 678312 1018445 := bbase (se 3 (by rfl) ⟨190958, by rfl⟩ : syracuseStep 1018445 = 381917) (by norm_num)
theorem B1018469 : Blo 678312 1018469 := bbase (se 4 (by rfl) ⟨95481, by rfl⟩ : syracuseStep 1018469 = 190963) (by norm_num)
theorem B1018493 : Blo 678312 1018493 := bbase (se 3 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 1018493 = 381935) (by norm_num)
theorem B1149565 : Blo 678312 1149565 := bbase (se 3 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 1149565 = 431087) (by norm_num)
theorem B1018517 : Blo 678312 1018517 := bbase (se 6 (by rfl) ⟨23871, by rfl⟩ : syracuseStep 1018517 = 47743) (by norm_num)
theorem B1018541 : Blo 678312 1018541 := bbase (se 3 (by rfl) ⟨190976, by rfl⟩ : syracuseStep 1018541 = 381953) (by norm_num)
theorem B1018565 : Blo 678312 1018565 := bbase (se 4 (by rfl) ⟨95490, by rfl⟩ : syracuseStep 1018565 = 190981) (by norm_num)
theorem B1149653 : Blo 678312 1149653 := bbase (se 7 (by rfl) ⟨13472, by rfl⟩ : syracuseStep 1149653 = 26945) (by norm_num)
theorem B1018589 : Blo 678312 1018589 := bbase (se 3 (by rfl) ⟨190985, by rfl⟩ : syracuseStep 1018589 = 381971) (by norm_num)
theorem B1018613 : Blo 678312 1018613 := bbase (se 5 (by rfl) ⟨47747, by rfl⟩ : syracuseStep 1018613 = 95495) (by norm_num)
theorem B2296565 : Blo 678312 2296565 := bbase (se 5 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 2296565 = 215303) (by norm_num)
theorem B1936133 : Blo 678312 1936133 := bbase (se 4 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 1936133 = 363025) (by norm_num)
theorem B1018637 : Blo 678312 1018637 := bbase (se 3 (by rfl) ⟨190994, by rfl⟩ : syracuseStep 1018637 = 381989) (by norm_num)
theorem B1018661 : Blo 678312 1018661 := bbase (se 4 (by rfl) ⟨95499, by rfl⟩ : syracuseStep 1018661 = 190999) (by norm_num)
theorem B1018685 : Blo 678312 1018685 := bbase (se 3 (by rfl) ⟨191003, by rfl⟩ : syracuseStep 1018685 = 382007) (by norm_num)
theorem B1018709 : Blo 678312 1018709 := bbase (se 9 (by rfl) ⟨2984, by rfl⟩ : syracuseStep 1018709 = 5969) (by norm_num)
theorem B1149781 : Blo 678312 1149781 := bbase (se 9 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 1149781 = 6737) (by norm_num)
theorem B1018733 : Blo 678312 1018733 := bbase (se 3 (by rfl) ⟨191012, by rfl⟩ : syracuseStep 1018733 = 382025) (by norm_num)
theorem B1018757 : Blo 678312 1018757 := bbase (se 4 (by rfl) ⟨95508, by rfl⟩ : syracuseStep 1018757 = 191017) (by norm_num)
theorem B1018781 : Blo 678312 1018781 := bbase (se 3 (by rfl) ⟨191021, by rfl⟩ : syracuseStep 1018781 = 382043) (by norm_num)
theorem B1149869 : Blo 678312 1149869 := bbase (se 3 (by rfl) ⟨215600, by rfl⟩ : syracuseStep 1149869 = 431201) (by norm_num)
theorem B1018805 : Blo 678312 1018805 := bbase (se 5 (by rfl) ⟨47756, by rfl⟩ : syracuseStep 1018805 = 95513) (by norm_num)
theorem B1018829 : Blo 678312 1018829 := bbase (se 3 (by rfl) ⟨191030, by rfl⟩ : syracuseStep 1018829 = 382061) (by norm_num)
theorem B1018853 : Blo 678312 1018853 := bbase (se 4 (by rfl) ⟨95517, by rfl⟩ : syracuseStep 1018853 = 191035) (by norm_num)
theorem B1018877 : Blo 678312 1018877 := bbase (se 3 (by rfl) ⟨191039, by rfl⟩ : syracuseStep 1018877 = 382079) (by norm_num)
theorem B1018901 : Blo 678312 1018901 := bbase (se 6 (by rfl) ⟨23880, by rfl⟩ : syracuseStep 1018901 = 47761) (by norm_num)
theorem B1018925 : Blo 678312 1018925 := bbase (se 3 (by rfl) ⟨191048, by rfl⟩ : syracuseStep 1018925 = 382097) (by norm_num)
theorem B1149997 : Blo 678312 1149997 := bbase (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) (by norm_num)
theorem B1018949 : Blo 678312 1018949 := bbase (se 4 (by rfl) ⟨95526, by rfl⟩ : syracuseStep 1018949 = 191053) (by norm_num)
theorem B1018973 : Blo 678312 1018973 := bbase (se 3 (by rfl) ⟨191057, by rfl⟩ : syracuseStep 1018973 = 382115) (by norm_num)
theorem B1018997 : Blo 678312 1018997 := bbase (se 5 (by rfl) ⟨47765, by rfl⟩ : syracuseStep 1018997 = 95531) (by norm_num)
theorem B1150085 : Blo 678312 1150085 := bbase (se 4 (by rfl) ⟨107820, by rfl⟩ : syracuseStep 1150085 = 215641) (by norm_num)
theorem B1019021 : Blo 678312 1019021 := bbase (se 3 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 1019021 = 382133) (by norm_num)
theorem B1019045 : Blo 678312 1019045 := bbase (se 4 (by rfl) ⟨95535, by rfl⟩ : syracuseStep 1019045 = 191071) (by norm_num)
theorem B2296997 : Blo 678312 2296997 := bbase (se 4 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 2296997 = 430687) (by norm_num)
theorem B1019069 : Blo 678312 1019069 := bbase (se 3 (by rfl) ⟨191075, by rfl⟩ : syracuseStep 1019069 = 382151) (by norm_num)
theorem B1019093 : Blo 678312 1019093 := bbase (se 7 (by rfl) ⟨11942, by rfl⟩ : syracuseStep 1019093 = 23885) (by norm_num)
theorem B1019117 : Blo 678312 1019117 := bbase (se 3 (by rfl) ⟨191084, by rfl⟩ : syracuseStep 1019117 = 382169) (by norm_num)
theorem B3443957 : Blo 678312 3443957 := bbase (se 5 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 3443957 = 322871) (by norm_num)
theorem B1019141 : Blo 678312 1019141 := bbase (se 4 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 1019141 = 191089) (by norm_num)
theorem B1150213 : Blo 678312 1150213 := bbase (se 4 (by rfl) ⟨107832, by rfl⟩ : syracuseStep 1150213 = 215665) (by norm_num)
theorem B1019165 : Blo 678312 1019165 := bbase (se 3 (by rfl) ⟨191093, by rfl⟩ : syracuseStep 1019165 = 382187) (by norm_num)
theorem B1019189 : Blo 678312 1019189 := bbase (se 5 (by rfl) ⟨47774, by rfl⟩ : syracuseStep 1019189 = 95549) (by norm_num)
theorem B691525 : Blo 678312 691525 := bbase (se 4 (by rfl) ⟨64830, by rfl⟩ : syracuseStep 691525 = 129661) (by norm_num)
theorem B1019213 : Blo 678312 1019213 := bbase (se 3 (by rfl) ⟨191102, by rfl⟩ : syracuseStep 1019213 = 382205) (by norm_num)
theorem B1150301 : Blo 678312 1150301 := bbase (se 3 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 1150301 = 431363) (by norm_num)
theorem B1019237 : Blo 678312 1019237 := bbase (se 4 (by rfl) ⟨95553, by rfl⟩ : syracuseStep 1019237 = 191107) (by norm_num)
theorem B1019261 : Blo 678312 1019261 := bbase (se 3 (by rfl) ⟨191111, by rfl⟩ : syracuseStep 1019261 = 382223) (by norm_num)
theorem B1019285 : Blo 678312 1019285 := bbase (se 6 (by rfl) ⟨23889, by rfl⟩ : syracuseStep 1019285 = 47779) (by norm_num)
theorem B724393 : Blo 678312 724393 := bbase (se 2 (by rfl) ⟨271647, by rfl⟩ : syracuseStep 724393 = 543295) (by norm_num)
theorem B1019309 : Blo 678312 1019309 := bbase (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) (by norm_num)
theorem B4656565 : Blo 678312 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B1019333 : Blo 678312 1019333 := bbase (se 4 (by rfl) ⟨95562, by rfl⟩ : syracuseStep 1019333 = 191125) (by norm_num)
theorem B7376341 : Blo 678312 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B1019357 : Blo 678312 1019357 := bbase (se 3 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 1019357 = 382259) (by norm_num)
theorem B1150429 : Blo 678312 1150429 := bbase (se 3 (by rfl) ⟨215705, by rfl⟩ : syracuseStep 1150429 = 431411) (by norm_num)
theorem B1019381 : Blo 678312 1019381 := bbase (se 5 (by rfl) ⟨47783, by rfl⟩ : syracuseStep 1019381 = 95567) (by norm_num)
theorem B1936885 : Blo 678312 1936885 := bbase (se 5 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 1936885 = 181583) (by norm_num)
theorem B1019405 : Blo 678312 1019405 := bbase (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) (by norm_num)
theorem B1019429 : Blo 678312 1019429 := bbase (se 4 (by rfl) ⟨95571, by rfl⟩ : syracuseStep 1019429 = 191143) (by norm_num)
theorem B2428453 : Blo 678312 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1150517 : Blo 678312 1150517 := bbase (se 5 (by rfl) ⟨53930, by rfl⟩ : syracuseStep 1150517 = 107861) (by norm_num)
theorem B1019453 : Blo 678312 1019453 := bbase (se 3 (by rfl) ⟨191147, by rfl⟩ : syracuseStep 1019453 = 382295) (by norm_num)
theorem B1019477 : Blo 678312 1019477 := bbase (se 8 (by rfl) ⟨5973, by rfl⟩ : syracuseStep 1019477 = 11947) (by norm_num)
theorem B2297429 : Blo 678312 2297429 := bbase (se 8 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 2297429 = 26923) (by norm_num)
theorem B1019501 : Blo 678312 1019501 := bbase (se 3 (by rfl) ⟨191156, by rfl⟩ : syracuseStep 1019501 = 382313) (by norm_num)
theorem B1019525 : Blo 678312 1019525 := bbase (se 4 (by rfl) ⟨95580, by rfl⟩ : syracuseStep 1019525 = 191161) (by norm_num)
theorem B1019549 : Blo 678312 1019549 := bbase (se 3 (by rfl) ⟨191165, by rfl⟩ : syracuseStep 1019549 = 382331) (by norm_num)
theorem B1019573 : Blo 678312 1019573 := bbase (se 5 (by rfl) ⟨47792, by rfl⟩ : syracuseStep 1019573 = 95585) (by norm_num)
theorem B1150645 : Blo 678312 1150645 := bbase (se 5 (by rfl) ⟨53936, by rfl⟩ : syracuseStep 1150645 = 107873) (by norm_num)
theorem B1838789 : Blo 678312 1838789 := bbase (se 4 (by rfl) ⟨172386, by rfl⟩ : syracuseStep 1838789 = 344773) (by norm_num)
theorem B1019597 : Blo 678312 1019597 := bbase (se 3 (by rfl) ⟨191174, by rfl⟩ : syracuseStep 1019597 = 382349) (by norm_num)
theorem B1019621 : Blo 678312 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B1019645 : Blo 678312 1019645 := bbase (se 3 (by rfl) ⟨191183, by rfl⟩ : syracuseStep 1019645 = 382367) (by norm_num)
theorem B1150733 : Blo 678312 1150733 := bbase (se 3 (by rfl) ⟨215762, by rfl⟩ : syracuseStep 1150733 = 431525) (by norm_num)
theorem B1019669 : Blo 678312 1019669 := bbase (se 6 (by rfl) ⟨23898, by rfl⟩ : syracuseStep 1019669 = 47797) (by norm_num)
theorem B1019693 : Blo 678312 1019693 := bbase (se 3 (by rfl) ⟨191192, by rfl⟩ : syracuseStep 1019693 = 382385) (by norm_num)
theorem B1019717 : Blo 678312 1019717 := bbase (se 4 (by rfl) ⟨95598, by rfl⟩ : syracuseStep 1019717 = 191197) (by norm_num)
theorem B1740629 : Blo 678312 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1019741 : Blo 678312 1019741 := bbase (se 3 (by rfl) ⟨191201, by rfl⟩ : syracuseStep 1019741 = 382403) (by norm_num)
theorem B724837 : Blo 678312 724837 := bbase (se 4 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 724837 = 135907) (by norm_num)
theorem B1019765 : Blo 678312 1019765 := bbase (se 5 (by rfl) ⟨47801, by rfl⟩ : syracuseStep 1019765 = 95603) (by norm_num)
theorem B1019789 : Blo 678312 1019789 := bbase (se 3 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 1019789 = 382421) (by norm_num)
theorem B1150861 : Blo 678312 1150861 := bbase (se 3 (by rfl) ⟨215786, by rfl⟩ : syracuseStep 1150861 = 431573) (by norm_num)
theorem B724897 : Blo 678312 724897 := bbase (se 2 (by rfl) ⟨271836, by rfl⟩ : syracuseStep 724897 = 543673) (by norm_num)
theorem B1019813 : Blo 678312 1019813 := bbase (se 4 (by rfl) ⟨95607, by rfl⟩ : syracuseStep 1019813 = 191215) (by norm_num)
theorem B1019837 : Blo 678312 1019837 := bbase (se 3 (by rfl) ⟨191219, by rfl⟩ : syracuseStep 1019837 = 382439) (by norm_num)
theorem B1019861 : Blo 678312 1019861 := bbase (se 7 (by rfl) ⟨11951, by rfl⟩ : syracuseStep 1019861 = 23903) (by norm_num)
theorem B1150949 : Blo 678312 1150949 := bbase (se 4 (by rfl) ⟨107901, by rfl⟩ : syracuseStep 1150949 = 215803) (by norm_num)
theorem B1019885 : Blo 678312 1019885 := bbase (se 3 (by rfl) ⟨191228, by rfl⟩ : syracuseStep 1019885 = 382457) (by norm_num)
theorem B1019909 : Blo 678312 1019909 := bbase (se 4 (by rfl) ⟨95616, by rfl⟩ : syracuseStep 1019909 = 191233) (by norm_num)
theorem B2297861 : Blo 678312 2297861 := bbase (se 4 (by rfl) ⟨215424, by rfl⟩ : syracuseStep 2297861 = 430849) (by norm_num)
theorem B1019933 : Blo 678312 1019933 := bbase (se 3 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 1019933 = 382475) (by norm_num)
theorem B1019957 : Blo 678312 1019957 := bbase (se 5 (by rfl) ⟨47810, by rfl⟩ : syracuseStep 1019957 = 95621) (by norm_num)
theorem B1019981 : Blo 678312 1019981 := bbase (se 3 (by rfl) ⟨191246, by rfl⟩ : syracuseStep 1019981 = 382493) (by norm_num)
theorem B1020005 : Blo 678312 1020005 := bbase (se 4 (by rfl) ⟨95625, by rfl⟩ : syracuseStep 1020005 = 191251) (by norm_num)
theorem B1151077 : Blo 678312 1151077 := bbase (se 4 (by rfl) ⟨107913, by rfl⟩ : syracuseStep 1151077 = 215827) (by norm_num)
theorem B1020029 : Blo 678312 1020029 := bbase (se 3 (by rfl) ⟨191255, by rfl⟩ : syracuseStep 1020029 = 382511) (by norm_num)
theorem B1020053 : Blo 678312 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B1020077 : Blo 678312 1020077 := bbase (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) (by norm_num)
theorem B4657333 : Blo 678312 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B1151165 : Blo 678312 1151165 := bbase (se 3 (by rfl) ⟨215843, by rfl⟩ : syracuseStep 1151165 = 431687) (by norm_num)
theorem B1020101 : Blo 678312 1020101 := bbase (se 4 (by rfl) ⟨95634, by rfl⟩ : syracuseStep 1020101 = 191269) (by norm_num)
theorem B725213 : Blo 678312 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B1020125 : Blo 678312 1020125 := bbase (se 3 (by rfl) ⟨191273, by rfl⟩ : syracuseStep 1020125 = 382547) (by norm_num)
theorem B1020149 : Blo 678312 1020149 := bbase (se 5 (by rfl) ⟨47819, by rfl⟩ : syracuseStep 1020149 = 95639) (by norm_num)
theorem B1020173 : Blo 678312 1020173 := bbase (se 3 (by rfl) ⟨191282, by rfl⟩ : syracuseStep 1020173 = 382565) (by norm_num)
theorem B1020197 : Blo 678312 1020197 := bbase (se 4 (by rfl) ⟨95643, by rfl⟩ : syracuseStep 1020197 = 191287) (by norm_num)
theorem B1020221 : Blo 678312 1020221 := bbase (se 3 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 1020221 = 382583) (by norm_num)
theorem B1151293 : Blo 678312 1151293 := bbase (se 3 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 1151293 = 431735) (by norm_num)
theorem B1020245 : Blo 678312 1020245 := bbase (se 10 (by rfl) ⟨1494, by rfl⟩ : syracuseStep 1020245 = 2989) (by norm_num)
theorem B1020269 : Blo 678312 1020269 := bbase (se 3 (by rfl) ⟨191300, by rfl⟩ : syracuseStep 1020269 = 382601) (by norm_num)
theorem B1020293 : Blo 678312 1020293 := bbase (se 4 (by rfl) ⟨95652, by rfl⟩ : syracuseStep 1020293 = 191305) (by norm_num)
theorem B1151381 : Blo 678312 1151381 := bbase (se 6 (by rfl) ⟨26985, by rfl⟩ : syracuseStep 1151381 = 53971) (by norm_num)
theorem B1020317 : Blo 678312 1020317 := bbase (se 3 (by rfl) ⟨191309, by rfl⟩ : syracuseStep 1020317 = 382619) (by norm_num)
theorem B1020341 : Blo 678312 1020341 := bbase (se 5 (by rfl) ⟨47828, by rfl⟩ : syracuseStep 1020341 = 95657) (by norm_num)
theorem B2298293 : Blo 678312 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B1020365 : Blo 678312 1020365 := bbase (se 3 (by rfl) ⟨191318, by rfl⟩ : syracuseStep 1020365 = 382637) (by norm_num)
theorem B1020389 : Blo 678312 1020389 := bbase (se 4 (by rfl) ⟨95661, by rfl⟩ : syracuseStep 1020389 = 191323) (by norm_num)
theorem B1020413 : Blo 678312 1020413 := bbase (se 3 (by rfl) ⟨191327, by rfl⟩ : syracuseStep 1020413 = 382655) (by norm_num)
theorem B3445253 : Blo 678312 3445253 := bbase (se 4 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 3445253 = 645985) (by norm_num)
theorem B1020437 : Blo 678312 1020437 := bbase (se 6 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 1020437 = 47833) (by norm_num)
theorem B1020461 : Blo 678312 1020461 := bbase (se 3 (by rfl) ⟨191336, by rfl⟩ : syracuseStep 1020461 = 382673) (by norm_num)
theorem B1020485 : Blo 678312 1020485 := bbase (se 4 (by rfl) ⟨95670, by rfl⟩ : syracuseStep 1020485 = 191341) (by norm_num)
theorem B1020509 : Blo 678312 1020509 := bbase (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) (by norm_num)
theorem B1020533 : Blo 678312 1020533 := bbase (se 5 (by rfl) ⟨47837, by rfl⟩ : syracuseStep 1020533 = 95675) (by norm_num)
theorem B1020557 : Blo 678312 1020557 := bbase (se 3 (by rfl) ⟨191354, by rfl⟩ : syracuseStep 1020557 = 382709) (by norm_num)
theorem B725657 : Blo 678312 725657 := bbase (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) (by norm_num)
theorem B1020581 : Blo 678312 1020581 := bbase (se 4 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 1020581 = 191359) (by norm_num)
theorem B1020605 : Blo 678312 1020605 := bbase (se 3 (by rfl) ⟨191363, by rfl⟩ : syracuseStep 1020605 = 382727) (by norm_num)
theorem B725717 : Blo 678312 725717 := bbase (se 7 (by rfl) ⟨8504, by rfl⟩ : syracuseStep 725717 = 17009) (by norm_num)
theorem B1020629 : Blo 678312 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B1020653 : Blo 678312 1020653 := bbase (se 3 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 1020653 = 382745) (by norm_num)
theorem B1020677 : Blo 678312 1020677 := bbase (se 4 (by rfl) ⟨95688, by rfl⟩ : syracuseStep 1020677 = 191377) (by norm_num)
theorem B1676045 : Blo 678312 1676045 := bbase (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) (by norm_num)
theorem B1020701 : Blo 678312 1020701 := bbase (se 3 (by rfl) ⟨191381, by rfl⟩ : syracuseStep 1020701 = 382763) (by norm_num)
theorem B2790197 : Blo 678312 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B1020725 : Blo 678312 1020725 := bbase (se 5 (by rfl) ⟨47846, by rfl⟩ : syracuseStep 1020725 = 95693) (by norm_num)
theorem B1020749 : Blo 678312 1020749 := bbase (se 3 (by rfl) ⟨191390, by rfl⟩ : syracuseStep 1020749 = 382781) (by norm_num)
theorem B725845 : Blo 678312 725845 := bbase (se 9 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 725845 = 4253) (by norm_num)
theorem B1020773 : Blo 678312 1020773 := bbase (se 4 (by rfl) ⟨95697, by rfl⟩ : syracuseStep 1020773 = 191395) (by norm_num)
theorem B2298725 : Blo 678312 2298725 := bbase (se 4 (by rfl) ⟨215505, by rfl⟩ : syracuseStep 2298725 = 431011) (by norm_num)
theorem B1020797 : Blo 678312 1020797 := bbase (se 3 (by rfl) ⟨191399, by rfl⟩ : syracuseStep 1020797 = 382799) (by norm_num)
theorem B1020821 : Blo 678312 1020821 := bbase (se 6 (by rfl) ⟨23925, by rfl⟩ : syracuseStep 1020821 = 47851) (by norm_num)
theorem B1020845 : Blo 678312 1020845 := bbase (se 3 (by rfl) ⟨191408, by rfl⟩ : syracuseStep 1020845 = 382817) (by norm_num)
theorem B1020869 : Blo 678312 1020869 := bbase (se 4 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 1020869 = 191413) (by norm_num)
theorem B1020893 : Blo 678312 1020893 := bbase (se 3 (by rfl) ⟨191417, by rfl⟩ : syracuseStep 1020893 = 382835) (by norm_num)
theorem B1020917 : Blo 678312 1020917 := bbase (se 5 (by rfl) ⟨47855, by rfl⟩ : syracuseStep 1020917 = 95711) (by norm_num)
theorem B1020941 : Blo 678312 1020941 := bbase (se 3 (by rfl) ⟨191426, by rfl⟩ : syracuseStep 1020941 = 382853) (by norm_num)
theorem B1020965 : Blo 678312 1020965 := bbase (se 4 (by rfl) ⟨95715, by rfl⟩ : syracuseStep 1020965 = 191431) (by norm_num)
theorem B1020989 : Blo 678312 1020989 := bbase (se 3 (by rfl) ⟨191435, by rfl⟩ : syracuseStep 1020989 = 382871) (by norm_num)
theorem B1021013 : Blo 678312 1021013 := bbase (se 8 (by rfl) ⟨5982, by rfl⟩ : syracuseStep 1021013 = 11965) (by norm_num)
theorem B1840229 : Blo 678312 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B1021037 : Blo 678312 1021037 := bbase (se 3 (by rfl) ⟨191444, by rfl⟩ : syracuseStep 1021037 = 382889) (by norm_num)
theorem B1021061 : Blo 678312 1021061 := bbase (se 4 (by rfl) ⟨95724, by rfl⟩ : syracuseStep 1021061 = 191449) (by norm_num)
theorem B1021085 : Blo 678312 1021085 := bbase (se 3 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 1021085 = 382907) (by norm_num)
theorem B1021109 : Blo 678312 1021109 := bbase (se 5 (by rfl) ⟨47864, by rfl⟩ : syracuseStep 1021109 = 95729) (by norm_num)
theorem B1021133 : Blo 678312 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B1021157 : Blo 678312 1021157 := bbase (se 4 (by rfl) ⟨95733, by rfl⟩ : syracuseStep 1021157 = 191467) (by norm_num)
theorem B1021181 : Blo 678312 1021181 := bbase (se 3 (by rfl) ⟨191471, by rfl⟩ : syracuseStep 1021181 = 382943) (by norm_num)
theorem B726289 : Blo 678312 726289 := bbase (se 2 (by rfl) ⟨272358, by rfl⟩ : syracuseStep 726289 = 544717) (by norm_num)
theorem B1021205 : Blo 678312 1021205 := bbase (se 6 (by rfl) ⟨23934, by rfl⟩ : syracuseStep 1021205 = 47869) (by norm_num)
theorem B2299157 : Blo 678312 2299157 := bbase (se 6 (by rfl) ⟨53886, by rfl⟩ : syracuseStep 2299157 = 107773) (by norm_num)
theorem B1021229 : Blo 678312 1021229 := bbase (se 3 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 1021229 = 382961) (by norm_num)
theorem B1021253 : Blo 678312 1021253 := bbase (se 4 (by rfl) ⟨95742, by rfl⟩ : syracuseStep 1021253 = 191485) (by norm_num)
theorem B1021277 : Blo 678312 1021277 := bbase (se 3 (by rfl) ⟨191489, by rfl⟩ : syracuseStep 1021277 = 382979) (by norm_num)
theorem B1021301 : Blo 678312 1021301 := bbase (se 5 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 1021301 = 95747) (by norm_num)
theorem B726409 : Blo 678312 726409 := bbase (se 2 (by rfl) ⟨272403, by rfl⟩ : syracuseStep 726409 = 544807) (by norm_num)
theorem B1021325 : Blo 678312 1021325 := bbase (se 3 (by rfl) ⟨191498, by rfl⟩ : syracuseStep 1021325 = 382997) (by norm_num)
theorem B1021349 : Blo 678312 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B1021373 : Blo 678312 1021373 := bbase (se 3 (by rfl) ⟨191507, by rfl⟩ : syracuseStep 1021373 = 383015) (by norm_num)
theorem B1021397 : Blo 678312 1021397 := bbase (se 7 (by rfl) ⟨11969, by rfl⟩ : syracuseStep 1021397 = 23939) (by norm_num)
theorem B4363733 : Blo 678312 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B1021421 : Blo 678312 1021421 := bbase (se 3 (by rfl) ⟨191516, by rfl⟩ : syracuseStep 1021421 = 383033) (by norm_num)
theorem B6526453 : Blo 678312 6526453 := bbase (se 5 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 6526453 = 611855) (by norm_num)
theorem B1021445 : Blo 678312 1021445 := bbase (se 4 (by rfl) ⟨95760, by rfl⟩ : syracuseStep 1021445 = 191521) (by norm_num)
theorem B1021469 : Blo 678312 1021469 := bbase (se 3 (by rfl) ⟨191525, by rfl⟩ : syracuseStep 1021469 = 383051) (by norm_num)
theorem B1021493 : Blo 678312 1021493 := bbase (se 5 (by rfl) ⟨47882, by rfl⟩ : syracuseStep 1021493 = 95765) (by norm_num)
theorem B1021517 : Blo 678312 1021517 := bbase (se 3 (by rfl) ⟨191534, by rfl⟩ : syracuseStep 1021517 = 383069) (by norm_num)
theorem B1021541 : Blo 678312 1021541 := bbase (se 4 (by rfl) ⟨95769, by rfl⟩ : syracuseStep 1021541 = 191539) (by norm_num)
theorem B1119853 : Blo 678312 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B1021565 : Blo 678312 1021565 := bbase (se 3 (by rfl) ⟨191543, by rfl⟩ : syracuseStep 1021565 = 383087) (by norm_num)
theorem B726661 : Blo 678312 726661 := bbase (se 4 (by rfl) ⟨68124, by rfl⟩ : syracuseStep 726661 = 136249) (by norm_num)
theorem B726665 : Blo 678312 726665 := bbase (se 2 (by rfl) ⟨272499, by rfl⟩ : syracuseStep 726665 = 544999) (by norm_num)
theorem B1021589 : Blo 678312 1021589 := bbase (se 6 (by rfl) ⟨23943, by rfl⟩ : syracuseStep 1021589 = 47887) (by norm_num)
theorem B1021613 : Blo 678312 1021613 := bbase (se 3 (by rfl) ⟨191552, by rfl⟩ : syracuseStep 1021613 = 383105) (by norm_num)
theorem B1021637 : Blo 678312 1021637 := bbase (se 4 (by rfl) ⟨95778, by rfl⟩ : syracuseStep 1021637 = 191557) (by norm_num)
theorem B2299589 : Blo 678312 2299589 := bbase (se 4 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 2299589 = 431173) (by norm_num)
theorem B1021661 : Blo 678312 1021661 := bbase (se 3 (by rfl) ⟨191561, by rfl⟩ : syracuseStep 1021661 = 383123) (by norm_num)
theorem B1021685 : Blo 678312 1021685 := bbase (se 5 (by rfl) ⟨47891, by rfl⟩ : syracuseStep 1021685 = 95783) (by norm_num)
theorem B1021709 : Blo 678312 1021709 := bbase (se 3 (by rfl) ⟨191570, by rfl⟩ : syracuseStep 1021709 = 383141) (by norm_num)
theorem B3446549 : Blo 678312 3446549 := bbase (se 6 (by rfl) ⟨80778, by rfl⟩ : syracuseStep 3446549 = 161557) (by norm_num)
theorem B1021733 : Blo 678312 1021733 := bbase (se 4 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 1021733 = 191575) (by norm_num)
theorem B1021757 : Blo 678312 1021757 := bbase (se 3 (by rfl) ⟨191579, by rfl⟩ : syracuseStep 1021757 = 383159) (by norm_num)
theorem B1021781 : Blo 678312 1021781 := bbase (se 9 (by rfl) ⟨2993, by rfl⟩ : syracuseStep 1021781 = 5987) (by norm_num)
theorem B1021805 : Blo 678312 1021805 := bbase (se 3 (by rfl) ⟨191588, by rfl⟩ : syracuseStep 1021805 = 383177) (by norm_num)
theorem B1021829 : Blo 678312 1021829 := bbase (se 4 (by rfl) ⟨95796, by rfl⟩ : syracuseStep 1021829 = 191593) (by norm_num)
theorem B1021853 : Blo 678312 1021853 := bbase (se 3 (by rfl) ⟨191597, by rfl⟩ : syracuseStep 1021853 = 383195) (by norm_num)
theorem B1021877 : Blo 678312 1021877 := bbase (se 5 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 1021877 = 95801) (by norm_num)
theorem B1841093 : Blo 678312 1841093 := bbase (se 4 (by rfl) ⟨172602, by rfl⟩ : syracuseStep 1841093 = 345205) (by norm_num)
theorem B1021901 : Blo 678312 1021901 := bbase (se 3 (by rfl) ⟨191606, by rfl⟩ : syracuseStep 1021901 = 383213) (by norm_num)
theorem B13277141 : Blo 678312 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B1021925 : Blo 678312 1021925 := bbase (se 4 (by rfl) ⟨95805, by rfl⟩ : syracuseStep 1021925 = 191611) (by norm_num)
theorem B1021949 : Blo 678312 1021949 := bbase (se 3 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 1021949 = 383231) (by norm_num)
theorem B1021973 : Blo 678312 1021973 := bbase (se 6 (by rfl) ⟨23952, by rfl⟩ : syracuseStep 1021973 = 47905) (by norm_num)
theorem B1021997 : Blo 678312 1021997 := bbase (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) (by norm_num)
theorem B1022021 : Blo 678312 1022021 := bbase (se 4 (by rfl) ⟨95814, by rfl⟩ : syracuseStep 1022021 = 191629) (by norm_num)
theorem B1022045 : Blo 678312 1022045 := bbase (se 3 (by rfl) ⟨191633, by rfl⟩ : syracuseStep 1022045 = 383267) (by norm_num)
theorem B1087589 : Blo 678312 1087589 := bbase (se 4 (by rfl) ⟨101961, by rfl⟩ : syracuseStep 1087589 = 203923) (by norm_num)
theorem B1022069 : Blo 678312 1022069 := bbase (se 5 (by rfl) ⟨47909, by rfl⟩ : syracuseStep 1022069 = 95819) (by norm_num)
theorem B2300021 : Blo 678312 2300021 := bbase (se 5 (by rfl) ⟨107813, by rfl⟩ : syracuseStep 2300021 = 215627) (by norm_num)
theorem B1022093 : Blo 678312 1022093 := bbase (se 3 (by rfl) ⟨191642, by rfl⟩ : syracuseStep 1022093 = 383285) (by norm_num)
theorem B1022117 : Blo 678312 1022117 := bbase (se 4 (by rfl) ⟨95823, by rfl⟩ : syracuseStep 1022117 = 191647) (by norm_num)
theorem B727229 : Blo 678312 727229 := bbase (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) (by norm_num)
theorem B1022141 : Blo 678312 1022141 := bbase (se 3 (by rfl) ⟨191651, by rfl⟩ : syracuseStep 1022141 = 383303) (by norm_num)
theorem B1022165 : Blo 678312 1022165 := bbase (se 7 (by rfl) ⟨11978, by rfl⟩ : syracuseStep 1022165 = 23957) (by norm_num)
theorem B1022189 : Blo 678312 1022189 := bbase (se 3 (by rfl) ⟨191660, by rfl⟩ : syracuseStep 1022189 = 383321) (by norm_num)
theorem B1022213 : Blo 678312 1022213 := bbase (se 4 (by rfl) ⟨95832, by rfl⟩ : syracuseStep 1022213 = 191665) (by norm_num)
theorem B1939733 : Blo 678312 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B1022237 : Blo 678312 1022237 := bbase (se 3 (by rfl) ⟨191669, by rfl⟩ : syracuseStep 1022237 = 383339) (by norm_num)
theorem B1022261 : Blo 678312 1022261 := bbase (se 5 (by rfl) ⟨47918, by rfl⟩ : syracuseStep 1022261 = 95837) (by norm_num)
theorem B1022285 : Blo 678312 1022285 := bbase (se 3 (by rfl) ⟨191678, by rfl⟩ : syracuseStep 1022285 = 383357) (by norm_num)
theorem B1022309 : Blo 678312 1022309 := bbase (se 4 (by rfl) ⟨95841, by rfl⟩ : syracuseStep 1022309 = 191683) (by norm_num)
theorem B1382765 : Blo 678312 1382765 := bbase (se 3 (by rfl) ⟨259268, by rfl⟩ : syracuseStep 1382765 = 518537) (by norm_num)
theorem B727417 : Blo 678312 727417 := bbase (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) (by norm_num)
theorem B1022333 : Blo 678312 1022333 := bbase (se 3 (by rfl) ⟨191687, by rfl⟩ : syracuseStep 1022333 = 383375) (by norm_num)
theorem B1382789 : Blo 678312 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B1841557 : Blo 678312 1841557 := bbase (se 6 (by rfl) ⟨43161, by rfl⟩ : syracuseStep 1841557 = 86323) (by norm_num)
theorem B1022357 : Blo 678312 1022357 := bbase (se 6 (by rfl) ⟨23961, by rfl⟩ : syracuseStep 1022357 = 47923) (by norm_num)
theorem B858529 : Blo 678312 858529 := bbase (se 2 (by rfl) ⟨321948, by rfl⟩ : syracuseStep 858529 = 643897) (by norm_num)
theorem B1022381 : Blo 678312 1022381 := bbase (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) (by norm_num)
theorem B1382837 : Blo 678312 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B1022405 : Blo 678312 1022405 := bbase (se 4 (by rfl) ⟨95850, by rfl⟩ : syracuseStep 1022405 = 191701) (by norm_num)
theorem B1022429 : Blo 678312 1022429 := bbase (se 3 (by rfl) ⟨191705, by rfl⟩ : syracuseStep 1022429 = 383411) (by norm_num)
theorem B1022453 : Blo 678312 1022453 := bbase (se 5 (by rfl) ⟨47927, by rfl⟩ : syracuseStep 1022453 = 95855) (by norm_num)
theorem B1022477 : Blo 678312 1022477 := bbase (se 3 (by rfl) ⟨191714, by rfl⟩ : syracuseStep 1022477 = 383429) (by norm_num)
theorem B2300453 : Blo 678312 2300453 := bbase (se 4 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 2300453 = 431335) (by norm_num)
theorem B1022501 : Blo 678312 1022501 := bbase (se 4 (by rfl) ⟨95859, by rfl⟩ : syracuseStep 1022501 = 191719) (by norm_num)
theorem B1022525 : Blo 678312 1022525 := bbase (se 3 (by rfl) ⟨191723, by rfl⟩ : syracuseStep 1022525 = 383447) (by norm_num)
theorem B858701 : Blo 678312 858701 := bbase (se 3 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 858701 = 322013) (by norm_num)
theorem B1022549 : Blo 678312 1022549 := bbase (se 8 (by rfl) ⟨5991, by rfl⟩ : syracuseStep 1022549 = 11983) (by norm_num)
theorem B1088101 : Blo 678312 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B1022573 : Blo 678312 1022573 := bbase (se 3 (by rfl) ⟨191732, by rfl⟩ : syracuseStep 1022573 = 383465) (by norm_num)
theorem B858757 : Blo 678312 858757 := bbase (se 4 (by rfl) ⟨80508, by rfl⟩ : syracuseStep 858757 = 161017) (by norm_num)
theorem B1022597 : Blo 678312 1022597 := bbase (se 4 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 1022597 = 191737) (by norm_num)
theorem B1022621 : Blo 678312 1022621 := bbase (se 3 (by rfl) ⟨191741, by rfl⟩ : syracuseStep 1022621 = 383483) (by norm_num)
theorem B1022645 : Blo 678312 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B1022669 : Blo 678312 1022669 := bbase (se 3 (by rfl) ⟨191750, by rfl⟩ : syracuseStep 1022669 = 383501) (by norm_num)
theorem B858853 : Blo 678312 858853 := bbase (se 4 (by rfl) ⟨80517, by rfl⟩ : syracuseStep 858853 = 161035) (by norm_num)
theorem B1022693 : Blo 678312 1022693 := bbase (se 4 (by rfl) ⟨95877, by rfl⟩ : syracuseStep 1022693 = 191755) (by norm_num)
theorem B1022717 : Blo 678312 1022717 := bbase (se 3 (by rfl) ⟨191759, by rfl⟩ : syracuseStep 1022717 = 383519) (by norm_num)
theorem B1022741 : Blo 678312 1022741 := bbase (se 6 (by rfl) ⟨23970, by rfl⟩ : syracuseStep 1022741 = 47941) (by norm_num)
theorem B1022765 : Blo 678312 1022765 := bbase (se 3 (by rfl) ⟨191768, by rfl⟩ : syracuseStep 1022765 = 383537) (by norm_num)
theorem B1022789 : Blo 678312 1022789 := bbase (se 4 (by rfl) ⟨95886, by rfl⟩ : syracuseStep 1022789 = 191773) (by norm_num)
theorem B1022813 : Blo 678312 1022813 := bbase (se 3 (by rfl) ⟨191777, by rfl⟩ : syracuseStep 1022813 = 383555) (by norm_num)
theorem B1022837 : Blo 678312 1022837 := bbase (se 5 (by rfl) ⟨47945, by rfl⟩ : syracuseStep 1022837 = 95891) (by norm_num)
theorem B1448837 : Blo 678312 1448837 := bbase (se 4 (by rfl) ⟨135828, by rfl⟩ : syracuseStep 1448837 = 271657) (by norm_num)
theorem B1022861 : Blo 678312 1022861 := bbase (se 3 (by rfl) ⟨191786, by rfl⟩ : syracuseStep 1022861 = 383573) (by norm_num)
theorem B859025 : Blo 678312 859025 := bbase (se 2 (by rfl) ⟨322134, by rfl⟩ : syracuseStep 859025 = 644269) (by norm_num)
theorem B1022885 : Blo 678312 1022885 := bbase (se 4 (by rfl) ⟨95895, by rfl⟩ : syracuseStep 1022885 = 191791) (by norm_num)
theorem B1022909 : Blo 678312 1022909 := bbase (se 3 (by rfl) ⟨191795, by rfl⟩ : syracuseStep 1022909 = 383591) (by norm_num)
theorem B859081 : Blo 678312 859081 := bbase (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) (by norm_num)
theorem B2300885 : Blo 678312 2300885 := bbase (se 7 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 2300885 = 53927) (by norm_num)
theorem B1022933 : Blo 678312 1022933 := bbase (se 7 (by rfl) ⟨11987, by rfl⟩ : syracuseStep 1022933 = 23975) (by norm_num)
theorem B1022957 : Blo 678312 1022957 := bbase (se 3 (by rfl) ⟨191804, by rfl⟩ : syracuseStep 1022957 = 383609) (by norm_num)
theorem B1022981 : Blo 678312 1022981 := bbase (se 4 (by rfl) ⟨95904, by rfl⟩ : syracuseStep 1022981 = 191809) (by norm_num)
theorem B1023005 : Blo 678312 1023005 := bbase (se 3 (by rfl) ⟨191813, by rfl⟩ : syracuseStep 1023005 = 383627) (by norm_num)
theorem B3447845 : Blo 678312 3447845 := bbase (se 4 (by rfl) ⟨323235, by rfl⟩ : syracuseStep 3447845 = 646471) (by norm_num)
theorem B859177 : Blo 678312 859177 := bbase (se 2 (by rfl) ⟨322191, by rfl⟩ : syracuseStep 859177 = 644383) (by norm_num)
theorem B1023029 : Blo 678312 1023029 := bbase (se 5 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 1023029 = 95909) (by norm_num)
theorem B1023053 : Blo 678312 1023053 := bbase (se 3 (by rfl) ⟨191822, by rfl⟩ : syracuseStep 1023053 = 383645) (by norm_num)
theorem B1023077 : Blo 678312 1023077 := bbase (se 4 (by rfl) ⟨95913, by rfl⟩ : syracuseStep 1023077 = 191827) (by norm_num)
theorem B1449085 : Blo 678312 1449085 := bbase (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) (by norm_num)
theorem B1023101 : Blo 678312 1023101 := bbase (se 3 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 1023101 = 383663) (by norm_num)
theorem B1023125 : Blo 678312 1023125 := bbase (se 6 (by rfl) ⟨23979, by rfl⟩ : syracuseStep 1023125 = 47959) (by norm_num)
theorem B728237 : Blo 678312 728237 := bbase (se 3 (by rfl) ⟨136544, by rfl⟩ : syracuseStep 728237 = 273089) (by norm_num)
theorem B1023149 : Blo 678312 1023149 := bbase (se 3 (by rfl) ⟨191840, by rfl⟩ : syracuseStep 1023149 = 383681) (by norm_num)
theorem B1023173 : Blo 678312 1023173 := bbase (se 4 (by rfl) ⟨95922, by rfl⟩ : syracuseStep 1023173 = 191845) (by norm_num)
theorem B859349 : Blo 678312 859349 := bbase (se 7 (by rfl) ⟨10070, by rfl⟩ : syracuseStep 859349 = 20141) (by norm_num)
theorem B1023197 : Blo 678312 1023197 := bbase (se 3 (by rfl) ⟨191849, by rfl⟩ : syracuseStep 1023197 = 383699) (by norm_num)
theorem B1023221 : Blo 678312 1023221 := bbase (se 5 (by rfl) ⟨47963, by rfl⟩ : syracuseStep 1023221 = 95927) (by norm_num)
theorem B859405 : Blo 678312 859405 := bbase (se 3 (by rfl) ⟨161138, by rfl⟩ : syracuseStep 859405 = 322277) (by norm_num)
theorem B1023245 : Blo 678312 1023245 := bbase (se 3 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 1023245 = 383717) (by norm_num)
theorem B1023269 : Blo 678312 1023269 := bbase (se 4 (by rfl) ⟨95931, by rfl⟩ : syracuseStep 1023269 = 191863) (by norm_num)
theorem B1842485 : Blo 678312 1842485 := bbase (se 5 (by rfl) ⟨86366, by rfl⟩ : syracuseStep 1842485 = 172733) (by norm_num)
theorem B1023293 : Blo 678312 1023293 := bbase (se 3 (by rfl) ⟨191867, by rfl⟩ : syracuseStep 1023293 = 383735) (by norm_num)
theorem B5152085 : Blo 678312 5152085 := bbase (se 11 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 5152085 = 7547) (by norm_num)
theorem B1023317 : Blo 678312 1023317 := bbase (se 11 (by rfl) ⟨749, by rfl⟩ : syracuseStep 1023317 = 1499) (by norm_num)
theorem B859501 : Blo 678312 859501 := bbase (se 3 (by rfl) ⟨161156, by rfl⟩ : syracuseStep 859501 = 322313) (by norm_num)
theorem B1023341 : Blo 678312 1023341 := bbase (se 3 (by rfl) ⟨191876, by rfl⟩ : syracuseStep 1023341 = 383753) (by norm_num)
theorem B2301317 : Blo 678312 2301317 := bbase (se 4 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 2301317 = 431497) (by norm_num)
theorem B1023365 : Blo 678312 1023365 := bbase (se 4 (by rfl) ⟨95940, by rfl⟩ : syracuseStep 1023365 = 191881) (by norm_num)
theorem B1023389 : Blo 678312 1023389 := bbase (se 3 (by rfl) ⟨191885, by rfl⟩ : syracuseStep 1023389 = 383771) (by norm_num)
theorem B1940917 : Blo 678312 1940917 := bbase (se 5 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 1940917 = 181961) (by norm_num)
theorem B1023413 : Blo 678312 1023413 := bbase (se 5 (by rfl) ⟨47972, by rfl⟩ : syracuseStep 1023413 = 95945) (by norm_num)
theorem B1023437 : Blo 678312 1023437 := bbase (se 3 (by rfl) ⟨191894, by rfl⟩ : syracuseStep 1023437 = 383789) (by norm_num)
theorem B1023461 : Blo 678312 1023461 := bbase (se 4 (by rfl) ⟨95949, by rfl⟩ : syracuseStep 1023461 = 191899) (by norm_num)
theorem B2334197 : Blo 678312 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B859673 : Blo 678312 859673 := bbase (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) (by norm_num)
theorem B1089101 : Blo 678312 1089101 := bbase (se 3 (by rfl) ⟨204206, by rfl⟩ : syracuseStep 1089101 = 408413) (by norm_num)
theorem B859729 : Blo 678312 859729 := bbase (se 2 (by rfl) ⟨322398, by rfl⟩ : syracuseStep 859729 = 644797) (by norm_num)
theorem B7347797 : Blo 678312 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B1941077 : Blo 678312 1941077 := bbase (se 8 (by rfl) ⟨11373, by rfl⟩ : syracuseStep 1941077 = 22747) (by norm_num)
theorem B1449589 : Blo 678312 1449589 := bbase (se 5 (by rfl) ⟨67949, by rfl⟩ : syracuseStep 1449589 = 135899) (by norm_num)
theorem B859825 : Blo 678312 859825 := bbase (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) (by norm_num)
theorem B1089229 : Blo 678312 1089229 := bbase (se 3 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 1089229 = 408461) (by norm_num)
theorem B2072309 : Blo 678312 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B1089293 : Blo 678312 1089293 := bbase (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) (by norm_num)
theorem B2301749 : Blo 678312 2301749 := bbase (se 5 (by rfl) ⟨107894, by rfl⟩ : syracuseStep 2301749 = 215789) (by norm_num)
theorem B1941317 : Blo 678312 1941317 := bbase (se 4 (by rfl) ⟨181998, by rfl⟩ : syracuseStep 1941317 = 363997) (by norm_num)
theorem B859997 : Blo 678312 859997 := bbase (se 3 (by rfl) ⟨161249, by rfl⟩ : syracuseStep 859997 = 322499) (by norm_num)
theorem B1679197 : Blo 678312 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B860053 : Blo 678312 860053 := bbase (se 6 (by rfl) ⟨20157, by rfl⟩ : syracuseStep 860053 = 40315) (by norm_num)
theorem B860149 : Blo 678312 860149 := bbase (se 5 (by rfl) ⟨40319, by rfl⟩ : syracuseStep 860149 = 80639) (by norm_num)
theorem B1941509 : Blo 678312 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B1548389 : Blo 678312 1548389 := bbase (se 4 (by rfl) ⟨145161, by rfl⟩ : syracuseStep 1548389 = 290323) (by norm_num)
theorem B860321 : Blo 678312 860321 := bbase (se 2 (by rfl) ⟨322620, by rfl⟩ : syracuseStep 860321 = 645241) (by norm_num)
theorem B860377 : Blo 678312 860377 := bbase (se 2 (by rfl) ⟨322641, by rfl⟩ : syracuseStep 860377 = 645283) (by norm_num)
theorem B2302181 : Blo 678312 2302181 := bbase (se 4 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 2302181 = 431659) (by norm_num)
theorem B3449141 : Blo 678312 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B860473 : Blo 678312 860473 := bbase (se 2 (by rfl) ⟨322677, by rfl⟩ : syracuseStep 860473 = 645355) (by norm_num)
theorem B3350965 : Blo 678312 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B860645 : Blo 678312 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B1450477 : Blo 678312 1450477 := bbase (se 3 (by rfl) ⟨271964, by rfl⟩ : syracuseStep 1450477 = 543929) (by norm_num)
theorem B860701 : Blo 678312 860701 := bbase (se 3 (by rfl) ⟨161381, by rfl⟩ : syracuseStep 860701 = 322763) (by norm_num)
theorem B860797 : Blo 678312 860797 := bbase (se 3 (by rfl) ⟨161399, by rfl⟩ : syracuseStep 860797 = 322799) (by norm_num)
theorem B1548941 : Blo 678312 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B828049 : Blo 678312 828049 := bbase (se 2 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 828049 = 621037) (by norm_num)
theorem B2302613 : Blo 678312 2302613 := bbase (se 6 (by rfl) ⟨53967, by rfl⟩ : syracuseStep 2302613 = 107935) (by norm_num)
theorem B860969 : Blo 678312 860969 := bbase (se 2 (by rfl) ⟨322863, by rfl⟩ : syracuseStep 860969 = 645727) (by norm_num)
theorem B861025 : Blo 678312 861025 := bbase (se 2 (by rfl) ⟨322884, by rfl⟩ : syracuseStep 861025 = 645769) (by norm_num)
theorem B861121 : Blo 678312 861121 := bbase (se 2 (by rfl) ⟨322920, by rfl⟩ : syracuseStep 861121 = 645841) (by norm_num)
theorem B1450973 : Blo 678312 1450973 := bbase (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) (by norm_num)
theorem B1942501 : Blo 678312 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B1090613 : Blo 678312 1090613 := bbase (se 5 (by rfl) ⟨51122, by rfl⟩ : syracuseStep 1090613 = 102245) (by norm_num)
theorem B861293 : Blo 678312 861293 := bbase (se 3 (by rfl) ⟨161492, by rfl⟩ : syracuseStep 861293 = 322985) (by norm_num)
theorem B3875957 : Blo 678312 3875957 := bbase (se 5 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 3875957 = 363371) (by norm_num)
theorem B861349 : Blo 678312 861349 := bbase (se 4 (by rfl) ⟨80751, by rfl⟩ : syracuseStep 861349 = 161503) (by norm_num)
theorem B1090741 : Blo 678312 1090741 := bbase (se 5 (by rfl) ⟨51128, by rfl⟩ : syracuseStep 1090741 = 102257) (by norm_num)
theorem B828613 : Blo 678312 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B763105 : Blo 678312 763105 := bbase (se 2 (by rfl) ⟨286164, by rfl⟩ : syracuseStep 763105 = 572329) (by norm_num)
theorem B763141 : Blo 678312 763141 := bbase (se 4 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 763141 = 143089) (by norm_num)
theorem B861445 : Blo 678312 861445 := bbase (se 4 (by rfl) ⟨80760, by rfl⟩ : syracuseStep 861445 = 161521) (by norm_num)
theorem B763177 : Blo 678312 763177 := bbase (se 2 (by rfl) ⟨286191, by rfl⟩ : syracuseStep 763177 = 572383) (by norm_num)
theorem B763213 : Blo 678312 763213 := bbase (se 3 (by rfl) ⟨143102, by rfl⟩ : syracuseStep 763213 = 286205) (by norm_num)
theorem B763249 : Blo 678312 763249 := bbase (se 2 (by rfl) ⟨286218, by rfl⟩ : syracuseStep 763249 = 572437) (by norm_num)
theorem B763285 : Blo 678312 763285 := bbase (se 6 (by rfl) ⟨17889, by rfl⟩ : syracuseStep 763285 = 35779) (by norm_num)
theorem B861617 : Blo 678312 861617 := bbase (se 2 (by rfl) ⟨323106, by rfl⟩ : syracuseStep 861617 = 646213) (by norm_num)
theorem B763321 : Blo 678312 763321 := bbase (se 2 (by rfl) ⟨286245, by rfl⟩ : syracuseStep 763321 = 572491) (by norm_num)
theorem B763357 : Blo 678312 763357 := bbase (se 3 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 763357 = 286259) (by norm_num)
theorem B861673 : Blo 678312 861673 := bbase (se 2 (by rfl) ⟨323127, by rfl⟩ : syracuseStep 861673 = 646255) (by norm_num)
theorem B763393 : Blo 678312 763393 := bbase (se 2 (by rfl) ⟨286272, by rfl⟩ : syracuseStep 763393 = 572545) (by norm_num)
theorem B763429 : Blo 678312 763429 := bbase (se 4 (by rfl) ⟨71571, by rfl⟩ : syracuseStep 763429 = 143143) (by norm_num)
theorem B3450437 : Blo 678312 3450437 := bbase (se 4 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 3450437 = 646957) (by norm_num)
theorem B763465 : Blo 678312 763465 := bbase (se 2 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 763465 = 572599) (by norm_num)
theorem B861769 : Blo 678312 861769 := bbase (se 2 (by rfl) ⟨323163, by rfl⟩ : syracuseStep 861769 = 646327) (by norm_num)
theorem B763501 : Blo 678312 763501 := bbase (se 3 (by rfl) ⟨143156, by rfl⟩ : syracuseStep 763501 = 286313) (by norm_num)
theorem B763537 : Blo 678312 763537 := bbase (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) (by norm_num)
theorem B763573 : Blo 678312 763573 := bbase (se 5 (by rfl) ⟨35792, by rfl⟩ : syracuseStep 763573 = 71585) (by norm_num)
theorem B1287893 : Blo 678312 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B763609 : Blo 678312 763609 := bbase (se 2 (by rfl) ⟨286353, by rfl⟩ : syracuseStep 763609 = 572707) (by norm_num)
theorem B861941 : Blo 678312 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B763645 : Blo 678312 763645 := bbase (se 3 (by rfl) ⟨143183, by rfl⟩ : syracuseStep 763645 = 286367) (by norm_num)
theorem B763681 : Blo 678312 763681 := bbase (se 2 (by rfl) ⟨286380, by rfl⟩ : syracuseStep 763681 = 572761) (by norm_num)
theorem B861997 : Blo 678312 861997 := bbase (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) (by norm_num)
theorem B763717 : Blo 678312 763717 := bbase (se 4 (by rfl) ⟨71598, by rfl⟩ : syracuseStep 763717 = 143197) (by norm_num)
theorem B1451861 : Blo 678312 1451861 := bbase (se 9 (by rfl) ⟨4253, by rfl⟩ : syracuseStep 1451861 = 8507) (by norm_num)
theorem B1288037 : Blo 678312 1288037 := bbase (se 4 (by rfl) ⟨120753, by rfl⟩ : syracuseStep 1288037 = 241507) (by norm_num)
theorem B763753 : Blo 678312 763753 := bbase (se 2 (by rfl) ⟨286407, by rfl⟩ : syracuseStep 763753 = 572815) (by norm_num)
theorem B2074501 : Blo 678312 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B763789 : Blo 678312 763789 := bbase (se 3 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 763789 = 286421) (by norm_num)
theorem B862093 : Blo 678312 862093 := bbase (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) (by norm_num)
theorem B763825 : Blo 678312 763825 := bbase (se 2 (by rfl) ⟨286434, by rfl⟩ : syracuseStep 763825 = 572869) (by norm_num)
theorem B1451981 : Blo 678312 1451981 := bbase (se 3 (by rfl) ⟨272246, by rfl⟩ : syracuseStep 1451981 = 544493) (by norm_num)
theorem B763861 : Blo 678312 763861 := bbase (se 7 (by rfl) ⟨8951, by rfl⟩ : syracuseStep 763861 = 17903) (by norm_num)
theorem B1091549 : Blo 678312 1091549 := bbase (se 3 (by rfl) ⟨204665, by rfl⟩ : syracuseStep 1091549 = 409331) (by norm_num)
theorem B763897 : Blo 678312 763897 := bbase (se 2 (by rfl) ⟨286461, by rfl⟩ : syracuseStep 763897 = 572923) (by norm_num)
theorem B763933 : Blo 678312 763933 := bbase (se 3 (by rfl) ⟨143237, by rfl⟩ : syracuseStep 763933 = 286475) (by norm_num)
theorem B862265 : Blo 678312 862265 := bbase (se 2 (by rfl) ⟨323349, by rfl⟩ : syracuseStep 862265 = 646699) (by norm_num)
theorem B763969 : Blo 678312 763969 := bbase (se 2 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 763969 = 572977) (by norm_num)
theorem B764005 : Blo 678312 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B829549 : Blo 678312 829549 := bbase (se 3 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 829549 = 311081) (by norm_num)
theorem B862321 : Blo 678312 862321 := bbase (se 2 (by rfl) ⟨323370, by rfl⟩ : syracuseStep 862321 = 646741) (by norm_num)
theorem B1222781 : Blo 678312 1222781 := bbase (se 3 (by rfl) ⟨229271, by rfl⟩ : syracuseStep 1222781 = 458543) (by norm_num)
theorem B1288325 : Blo 678312 1288325 := bbase (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) (by norm_num)
theorem B764041 : Blo 678312 764041 := bbase (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) (by norm_num)
theorem B764077 : Blo 678312 764077 := bbase (se 3 (by rfl) ⟨143264, by rfl⟩ : syracuseStep 764077 = 286529) (by norm_num)
theorem B1747117 : Blo 678312 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B3582133 : Blo 678312 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B764113 : Blo 678312 764113 := bbase (se 2 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 764113 = 573085) (by norm_num)
theorem B862417 : Blo 678312 862417 := bbase (se 2 (by rfl) ⟨323406, by rfl⟩ : syracuseStep 862417 = 646813) (by norm_num)
theorem B764149 : Blo 678312 764149 := bbase (se 5 (by rfl) ⟨35819, by rfl⟩ : syracuseStep 764149 = 71639) (by norm_num)
theorem B1091837 : Blo 678312 1091837 := bbase (se 3 (by rfl) ⟨204719, by rfl⟩ : syracuseStep 1091837 = 409439) (by norm_num)
theorem B764185 : Blo 678312 764185 := bbase (se 2 (by rfl) ⟨286569, by rfl⟩ : syracuseStep 764185 = 573139) (by norm_num)
theorem B1288477 : Blo 678312 1288477 := bbase (se 3 (by rfl) ⟨241589, by rfl⟩ : syracuseStep 1288477 = 483179) (by norm_num)
theorem B764221 : Blo 678312 764221 := bbase (se 3 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 764221 = 286583) (by norm_num)
theorem B764257 : Blo 678312 764257 := bbase (se 2 (by rfl) ⟨286596, by rfl⟩ : syracuseStep 764257 = 573193) (by norm_num)
theorem B862589 : Blo 678312 862589 := bbase (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) (by norm_num)
theorem B764293 : Blo 678312 764293 := bbase (se 4 (by rfl) ⟨71652, by rfl⟩ : syracuseStep 764293 = 143305) (by norm_num)
theorem B764329 : Blo 678312 764329 := bbase (se 2 (by rfl) ⟨286623, by rfl⟩ : syracuseStep 764329 = 573247) (by norm_num)
theorem B862645 : Blo 678312 862645 := bbase (se 5 (by rfl) ⟨40436, by rfl⟩ : syracuseStep 862645 = 80873) (by norm_num)
theorem B764365 : Blo 678312 764365 := bbase (se 3 (by rfl) ⟨143318, by rfl⟩ : syracuseStep 764365 = 286637) (by norm_num)
theorem B764401 : Blo 678312 764401 := bbase (se 2 (by rfl) ⟨286650, by rfl⟩ : syracuseStep 764401 = 573301) (by norm_num)
theorem B764437 : Blo 678312 764437 := bbase (se 6 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 764437 = 35833) (by norm_num)
theorem B862741 : Blo 678312 862741 := bbase (se 6 (by rfl) ⟨20220, by rfl⟩ : syracuseStep 862741 = 40441) (by norm_num)
theorem B764473 : Blo 678312 764473 := bbase (se 2 (by rfl) ⟨286677, by rfl⟩ : syracuseStep 764473 = 573355) (by norm_num)
theorem B1452613 : Blo 678312 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B1288781 : Blo 678312 1288781 := bbase (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) (by norm_num)
theorem B764509 : Blo 678312 764509 := bbase (se 3 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 764509 = 286691) (by norm_num)
theorem B764545 : Blo 678312 764545 := bbase (se 2 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 764545 = 573409) (by norm_num)
theorem B1092253 : Blo 678312 1092253 := bbase (se 3 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 1092253 = 409595) (by norm_num)
theorem B1813157 : Blo 678312 1813157 := bbase (se 4 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 1813157 = 339967) (by norm_num)
theorem B764581 : Blo 678312 764581 := bbase (se 4 (by rfl) ⟨71679, by rfl⟩ : syracuseStep 764581 = 143359) (by norm_num)
theorem B862913 : Blo 678312 862913 := bbase (se 2 (by rfl) ⟨323592, by rfl⟩ : syracuseStep 862913 = 647185) (by norm_num)
theorem B1223365 : Blo 678312 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B764617 : Blo 678312 764617 := bbase (se 2 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 764617 = 573463) (by norm_num)
theorem B764653 : Blo 678312 764653 := bbase (se 3 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 764653 = 286745) (by norm_num)
theorem B862969 : Blo 678312 862969 := bbase (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) (by norm_num)
theorem B764689 : Blo 678312 764689 := bbase (se 2 (by rfl) ⟨286758, by rfl⟩ : syracuseStep 764689 = 573517) (by norm_num)
theorem B764725 : Blo 678312 764725 := bbase (se 5 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 764725 = 71693) (by norm_num)
theorem B3451733 : Blo 678312 3451733 := bbase (se 9 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 3451733 = 20225) (by norm_num)
theorem B764761 : Blo 678312 764761 := bbase (se 2 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 764761 = 573571) (by norm_num)
theorem B863065 : Blo 678312 863065 := bbase (se 2 (by rfl) ⟨323649, by rfl⟩ : syracuseStep 863065 = 647299) (by norm_num)
theorem B764797 : Blo 678312 764797 := bbase (se 3 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 764797 = 286799) (by norm_num)
theorem B764833 : Blo 678312 764833 := bbase (se 2 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 764833 = 573625) (by norm_num)
theorem B764869 : Blo 678312 764869 := bbase (se 4 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 764869 = 143413) (by norm_num)
theorem B764905 : Blo 678312 764905 := bbase (se 2 (by rfl) ⟨286839, by rfl⟩ : syracuseStep 764905 = 573679) (by norm_num)
theorem B863237 : Blo 678312 863237 := bbase (se 4 (by rfl) ⟨80928, by rfl⟩ : syracuseStep 863237 = 161857) (by norm_num)
theorem B764941 : Blo 678312 764941 := bbase (se 3 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 764941 = 286853) (by norm_num)
theorem B764977 : Blo 678312 764977 := bbase (se 2 (by rfl) ⟨286866, by rfl⟩ : syracuseStep 764977 = 573733) (by norm_num)
theorem B863293 : Blo 678312 863293 := bbase (se 3 (by rfl) ⟨161867, by rfl⟩ : syracuseStep 863293 = 323735) (by norm_num)
theorem B7842901 : Blo 678312 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B765013 : Blo 678312 765013 := bbase (se 8 (by rfl) ⟨4482, by rfl⟩ : syracuseStep 765013 = 8965) (by norm_num)
theorem B765049 : Blo 678312 765049 := bbase (se 2 (by rfl) ⟨286893, by rfl⟩ : syracuseStep 765049 = 573787) (by norm_num)
theorem B765085 : Blo 678312 765085 := bbase (se 3 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 765085 = 286907) (by norm_num)
theorem B863389 : Blo 678312 863389 := bbase (se 3 (by rfl) ⟨161885, by rfl⟩ : syracuseStep 863389 = 323771) (by norm_num)
theorem B765121 : Blo 678312 765121 := bbase (se 2 (by rfl) ⟨286920, by rfl⟩ : syracuseStep 765121 = 573841) (by norm_num)
theorem B765157 : Blo 678312 765157 := bbase (se 4 (by rfl) ⟨71733, by rfl⟩ : syracuseStep 765157 = 143467) (by norm_num)
theorem B765193 : Blo 678312 765193 := bbase (se 2 (by rfl) ⟨286947, by rfl⟩ : syracuseStep 765193 = 573895) (by norm_num)
theorem B765229 : Blo 678312 765229 := bbase (se 3 (by rfl) ⟨143480, by rfl⟩ : syracuseStep 765229 = 286961) (by norm_num)
theorem B4140341 : Blo 678312 4140341 := bbase (se 5 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 4140341 = 388157) (by norm_num)
theorem B1289533 : Blo 678312 1289533 := bbase (se 3 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 1289533 = 483575) (by norm_num)
theorem B765265 : Blo 678312 765265 := bbase (se 2 (by rfl) ⟨286974, by rfl⟩ : syracuseStep 765265 = 573949) (by norm_num)
theorem B765301 : Blo 678312 765301 := bbase (se 5 (by rfl) ⟨35873, by rfl⟩ : syracuseStep 765301 = 71747) (by norm_num)
theorem B2174357 : Blo 678312 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B765337 : Blo 678312 765337 := bbase (se 2 (by rfl) ⟨287001, by rfl⟩ : syracuseStep 765337 = 574003) (by norm_num)
theorem B765373 : Blo 678312 765373 := bbase (se 3 (by rfl) ⟨143507, by rfl⟩ : syracuseStep 765373 = 287015) (by norm_num)
theorem B1453501 : Blo 678312 1453501 := bbase (se 3 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 1453501 = 545063) (by norm_num)
theorem B1289677 : Blo 678312 1289677 := bbase (se 3 (by rfl) ⟨241814, by rfl⟩ : syracuseStep 1289677 = 483629) (by norm_num)
theorem B765409 : Blo 678312 765409 := bbase (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) (by norm_num)
theorem B765445 : Blo 678312 765445 := bbase (se 4 (by rfl) ⟨71760, by rfl⟩ : syracuseStep 765445 = 143521) (by norm_num)
theorem B765481 : Blo 678312 765481 := bbase (se 2 (by rfl) ⟨287055, by rfl⟩ : syracuseStep 765481 = 574111) (by norm_num)
theorem B1453621 : Blo 678312 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B765517 : Blo 678312 765517 := bbase (se 3 (by rfl) ⟨143534, by rfl⟩ : syracuseStep 765517 = 287069) (by norm_num)
theorem B1289837 : Blo 678312 1289837 := bbase (se 3 (by rfl) ⟨241844, by rfl⟩ : syracuseStep 1289837 = 483689) (by norm_num)
theorem B765553 : Blo 678312 765553 := bbase (se 2 (by rfl) ⟨287082, by rfl⟩ : syracuseStep 765553 = 574165) (by norm_num)
theorem B765589 : Blo 678312 765589 := bbase (se 6 (by rfl) ⟨17943, by rfl⟩ : syracuseStep 765589 = 35887) (by norm_num)
theorem B765625 : Blo 678312 765625 := bbase (se 2 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 765625 = 574219) (by norm_num)
theorem B765661 : Blo 678312 765661 := bbase (se 3 (by rfl) ⟨143561, by rfl⟩ : syracuseStep 765661 = 287123) (by norm_num)
theorem B1289981 : Blo 678312 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B765697 : Blo 678312 765697 := bbase (se 2 (by rfl) ⟨287136, by rfl⟩ : syracuseStep 765697 = 574273) (by norm_num)
theorem B765733 : Blo 678312 765733 := bbase (se 4 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 765733 = 143575) (by norm_num)
theorem B1453877 : Blo 678312 1453877 := bbase (se 5 (by rfl) ⟨68150, by rfl⟩ : syracuseStep 1453877 = 136301) (by norm_num)
theorem B765769 : Blo 678312 765769 := bbase (se 2 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 765769 = 574327) (by norm_num)
theorem B1224533 : Blo 678312 1224533 := bbase (se 9 (by rfl) ⟨3587, by rfl⟩ : syracuseStep 1224533 = 7175) (by norm_num)
theorem B765805 : Blo 678312 765805 := bbase (se 3 (by rfl) ⟨143588, by rfl⟩ : syracuseStep 765805 = 287177) (by norm_num)
theorem B765841 : Blo 678312 765841 := bbase (se 2 (by rfl) ⟨287190, by rfl⟩ : syracuseStep 765841 = 574381) (by norm_num)
theorem B765877 : Blo 678312 765877 := bbase (se 5 (by rfl) ⟨35900, by rfl⟩ : syracuseStep 765877 = 71801) (by norm_num)
theorem B765913 : Blo 678312 765913 := bbase (se 2 (by rfl) ⟨287217, by rfl⟩ : syracuseStep 765913 = 574435) (by norm_num)
theorem B765949 : Blo 678312 765949 := bbase (se 3 (by rfl) ⟨143615, by rfl⟩ : syracuseStep 765949 = 287231) (by norm_num)
theorem B1290269 : Blo 678312 1290269 := bbase (se 3 (by rfl) ⟨241925, by rfl⟩ : syracuseStep 1290269 = 483851) (by norm_num)
theorem B765985 : Blo 678312 765985 := bbase (se 2 (by rfl) ⟨287244, by rfl⟩ : syracuseStep 765985 = 574489) (by norm_num)
theorem B766021 : Blo 678312 766021 := bbase (se 4 (by rfl) ⟨71814, by rfl⟩ : syracuseStep 766021 = 143629) (by norm_num)
theorem B3453029 : Blo 678312 3453029 := bbase (se 4 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 3453029 = 647443) (by norm_num)
theorem B766057 : Blo 678312 766057 := bbase (se 2 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 766057 = 574543) (by norm_num)
theorem B766093 : Blo 678312 766093 := bbase (se 3 (by rfl) ⟨143642, by rfl⟩ : syracuseStep 766093 = 287285) (by norm_num)
theorem B766129 : Blo 678312 766129 := bbase (se 2 (by rfl) ⟨287298, by rfl⟩ : syracuseStep 766129 = 574597) (by norm_num)
theorem B4894901 : Blo 678312 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B1290421 : Blo 678312 1290421 := bbase (se 5 (by rfl) ⟨60488, by rfl⟩ : syracuseStep 1290421 = 120977) (by norm_num)
theorem B1323221 : Blo 678312 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B766165 : Blo 678312 766165 := bbase (se 7 (by rfl) ⟨8978, by rfl⟩ : syracuseStep 766165 = 17957) (by norm_num)
theorem B766201 : Blo 678312 766201 := bbase (se 2 (by rfl) ⟨287325, by rfl⟩ : syracuseStep 766201 = 574651) (by norm_num)
theorem B1224973 : Blo 678312 1224973 := bbase (se 3 (by rfl) ⟨229682, by rfl⟩ : syracuseStep 1224973 = 459365) (by norm_num)
theorem B766237 : Blo 678312 766237 := bbase (se 3 (by rfl) ⟨143669, by rfl⟩ : syracuseStep 766237 = 287339) (by norm_num)
theorem B766273 : Blo 678312 766273 := bbase (se 2 (by rfl) ⟨287352, by rfl⟩ : syracuseStep 766273 = 574705) (by norm_num)
theorem B1225037 : Blo 678312 1225037 := bbase (se 3 (by rfl) ⟨229694, by rfl⟩ : syracuseStep 1225037 = 459389) (by norm_num)
theorem B766309 : Blo 678312 766309 := bbase (se 4 (by rfl) ⟨71841, by rfl⟩ : syracuseStep 766309 = 143683) (by norm_num)
theorem B766345 : Blo 678312 766345 := bbase (se 2 (by rfl) ⟨287379, by rfl⟩ : syracuseStep 766345 = 574759) (by norm_num)
theorem B766381 : Blo 678312 766381 := bbase (se 3 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 766381 = 287393) (by norm_num)
theorem B766417 : Blo 678312 766417 := bbase (se 2 (by rfl) ⟨287406, by rfl⟩ : syracuseStep 766417 = 574813) (by norm_num)
theorem B1290725 : Blo 678312 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B766453 : Blo 678312 766453 := bbase (se 5 (by rfl) ⟨35927, by rfl⟩ : syracuseStep 766453 = 71855) (by norm_num)
theorem B766489 : Blo 678312 766489 := bbase (se 2 (by rfl) ⟨287433, by rfl⟩ : syracuseStep 766489 = 574867) (by norm_num)
theorem B766525 : Blo 678312 766525 := bbase (se 3 (by rfl) ⟨143723, by rfl⟩ : syracuseStep 766525 = 287447) (by norm_num)
theorem B766561 : Blo 678312 766561 := bbase (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) (by norm_num)
theorem B1225325 : Blo 678312 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B766597 : Blo 678312 766597 := bbase (se 4 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 766597 = 143737) (by norm_num)
theorem B766633 : Blo 678312 766633 := bbase (se 2 (by rfl) ⟨287487, by rfl⟩ : syracuseStep 766633 = 574975) (by norm_num)
theorem B1454765 : Blo 678312 1454765 := bbase (se 3 (by rfl) ⟨272768, by rfl⟩ : syracuseStep 1454765 = 545537) (by norm_num)
theorem B766669 : Blo 678312 766669 := bbase (se 3 (by rfl) ⟨143750, by rfl⟩ : syracuseStep 766669 = 287501) (by norm_num)
theorem B766705 : Blo 678312 766705 := bbase (se 2 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 766705 = 575029) (by norm_num)
theorem B1716997 : Blo 678312 1716997 := bbase (se 4 (by rfl) ⟨160968, by rfl⟩ : syracuseStep 1716997 = 321937) (by norm_num)
theorem B766741 : Blo 678312 766741 := bbase (se 6 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 766741 = 35941) (by norm_num)
theorem B2175781 : Blo 678312 2175781 := bbase (se 4 (by rfl) ⟨203979, by rfl⟩ : syracuseStep 2175781 = 407959) (by norm_num)
theorem B766777 : Blo 678312 766777 := bbase (se 2 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 766777 = 575083) (by norm_num)
theorem B766813 : Blo 678312 766813 := bbase (se 3 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 766813 = 287555) (by norm_num)
theorem B1717109 : Blo 678312 1717109 := bbase (se 5 (by rfl) ⟨80489, by rfl⟩ : syracuseStep 1717109 = 160979) (by norm_num)
theorem B766849 : Blo 678312 766849 := bbase (se 2 (by rfl) ⟨287568, by rfl⟩ : syracuseStep 766849 = 575137) (by norm_num)
theorem B1455005 : Blo 678312 1455005 := bbase (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) (by norm_num)
theorem B766885 : Blo 678312 766885 := bbase (se 4 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 766885 = 143791) (by norm_num)
theorem B766921 : Blo 678312 766921 := bbase (se 2 (by rfl) ⟨287595, by rfl⟩ : syracuseStep 766921 = 575191) (by norm_num)
theorem B1553357 : Blo 678312 1553357 := bbase (se 3 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 1553357 = 582509) (by norm_num)
theorem B3683285 : Blo 678312 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B766957 : Blo 678312 766957 := bbase (se 3 (by rfl) ⟨143804, by rfl⟩ : syracuseStep 766957 = 287609) (by norm_num)
theorem B766993 : Blo 678312 766993 := bbase (se 2 (by rfl) ⟨287622, by rfl⟩ : syracuseStep 766993 = 575245) (by norm_num)
theorem B1717301 : Blo 678312 1717301 := bbase (se 5 (by rfl) ⟨80498, by rfl⟩ : syracuseStep 1717301 = 160997) (by norm_num)
theorem B767029 : Blo 678312 767029 := bbase (se 5 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 767029 = 71909) (by norm_num)
theorem B767065 : Blo 678312 767065 := bbase (se 2 (by rfl) ⟨287649, by rfl⟩ : syracuseStep 767065 = 575299) (by norm_num)
theorem B767101 : Blo 678312 767101 := bbase (se 3 (by rfl) ⟨143831, by rfl⟩ : syracuseStep 767101 = 287663) (by norm_num)
theorem B767137 : Blo 678312 767137 := bbase (se 2 (by rfl) ⟨287676, by rfl⟩ : syracuseStep 767137 = 575353) (by norm_num)
theorem B767173 : Blo 678312 767173 := bbase (se 4 (by rfl) ⟨71922, by rfl⟩ : syracuseStep 767173 = 143845) (by norm_num)
theorem B1291477 : Blo 678312 1291477 := bbase (se 7 (by rfl) ⟨15134, by rfl⟩ : syracuseStep 1291477 = 30269) (by norm_num)
theorem B767209 : Blo 678312 767209 := bbase (se 2 (by rfl) ⟨287703, by rfl⟩ : syracuseStep 767209 = 575407) (by norm_num)
theorem B767245 : Blo 678312 767245 := bbase (se 3 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 767245 = 287717) (by norm_num)
theorem B767281 : Blo 678312 767281 := bbase (se 2 (by rfl) ⟨287730, by rfl⟩ : syracuseStep 767281 = 575461) (by norm_num)
theorem B767317 : Blo 678312 767317 := bbase (se 13 (by rfl) ⟨140, by rfl⟩ : syracuseStep 767317 = 281) (by norm_num)
theorem B1291621 : Blo 678312 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B767353 : Blo 678312 767353 := bbase (se 2 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 767353 = 575515) (by norm_num)
theorem B1717645 : Blo 678312 1717645 := bbase (se 3 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 1717645 = 644117) (by norm_num)
theorem B1455509 : Blo 678312 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B1455517 : Blo 678312 1455517 := bbase (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) (by norm_num)
theorem B767389 : Blo 678312 767389 := bbase (se 3 (by rfl) ⟨143885, by rfl⟩ : syracuseStep 767389 = 287771) (by norm_num)
theorem B767425 : Blo 678312 767425 := bbase (se 2 (by rfl) ⟨287784, by rfl⟩ : syracuseStep 767425 = 575569) (by norm_num)
theorem B767461 : Blo 678312 767461 := bbase (se 4 (by rfl) ⟨71949, by rfl⟩ : syracuseStep 767461 = 143899) (by norm_num)
theorem B1717757 : Blo 678312 1717757 := bbase (se 3 (by rfl) ⟨322079, by rfl⟩ : syracuseStep 1717757 = 644159) (by norm_num)
theorem B1291781 : Blo 678312 1291781 := bbase (se 4 (by rfl) ⟨121104, by rfl⟩ : syracuseStep 1291781 = 242209) (by norm_num)
theorem B767497 : Blo 678312 767497 := bbase (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) (by norm_num)
theorem B1553941 : Blo 678312 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B767533 : Blo 678312 767533 := bbase (se 3 (by rfl) ⟨143912, by rfl⟩ : syracuseStep 767533 = 287825) (by norm_num)
theorem B767569 : Blo 678312 767569 := bbase (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) (by norm_num)
theorem B1226357 : Blo 678312 1226357 := bbase (se 5 (by rfl) ⟨57485, by rfl⟩ : syracuseStep 1226357 = 114971) (by norm_num)
theorem B1291925 : Blo 678312 1291925 := bbase (se 6 (by rfl) ⟨30279, by rfl⟩ : syracuseStep 1291925 = 60559) (by norm_num)
theorem B1717949 : Blo 678312 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B1292213 : Blo 678312 1292213 := bbase (se 5 (by rfl) ⟨60572, by rfl⟩ : syracuseStep 1292213 = 121145) (by norm_num)
theorem B1718293 : Blo 678312 1718293 := bbase (se 6 (by rfl) ⟨40272, by rfl⟩ : syracuseStep 1718293 = 80545) (by norm_num)
theorem B1292365 : Blo 678312 1292365 := bbase (se 3 (by rfl) ⟨242318, by rfl⟩ : syracuseStep 1292365 = 484637) (by norm_num)
theorem B8697941 : Blo 678312 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B1718405 : Blo 678312 1718405 := bbase (se 4 (by rfl) ⟨161100, by rfl⟩ : syracuseStep 1718405 = 322201) (by norm_num)
theorem B735437 : Blo 678312 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B1718597 : Blo 678312 1718597 := bbase (se 4 (by rfl) ⟨161118, by rfl⟩ : syracuseStep 1718597 = 322237) (by norm_num)
theorem B2177381 : Blo 678312 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B1292669 : Blo 678312 1292669 := bbase (se 3 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 1292669 = 484751) (by norm_num)
theorem B1161733 : Blo 678312 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B1456645 : Blo 678312 1456645 := bbase (se 4 (by rfl) ⟨136560, by rfl⟩ : syracuseStep 1456645 = 273121) (by norm_num)
theorem B10074773 : Blo 678312 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B1718941 : Blo 678312 1718941 := bbase (se 3 (by rfl) ⟨322301, by rfl⟩ : syracuseStep 1718941 = 644603) (by norm_num)
theorem B1555109 : Blo 678312 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1719053 : Blo 678312 1719053 := bbase (se 3 (by rfl) ⟨322322, by rfl⟩ : syracuseStep 1719053 = 644645) (by norm_num)
theorem B1457021 : Blo 678312 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B736165 : Blo 678312 736165 := bbase (se 4 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 736165 = 138031) (by norm_num)
theorem B5159861 : Blo 678312 5159861 := bbase (se 5 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 5159861 = 483737) (by norm_num)
theorem B1719245 : Blo 678312 1719245 := bbase (se 3 (by rfl) ⟨322358, by rfl⟩ : syracuseStep 1719245 = 644717) (by norm_num)
theorem B1293421 : Blo 678312 1293421 := bbase (se 3 (by rfl) ⟨242516, by rfl⟩ : syracuseStep 1293421 = 485033) (by norm_num)
theorem B1293565 : Blo 678312 1293565 := bbase (se 3 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 1293565 = 485087) (by norm_num)
theorem B1719589 : Blo 678312 1719589 := bbase (se 4 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 1719589 = 322423) (by norm_num)
theorem B1719701 : Blo 678312 1719701 := bbase (se 6 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 1719701 = 80611) (by norm_num)
theorem B1293725 : Blo 678312 1293725 := bbase (se 3 (by rfl) ⟨242573, by rfl⟩ : syracuseStep 1293725 = 485147) (by norm_num)
theorem B2178485 : Blo 678312 2178485 := bbase (se 5 (by rfl) ⟨102116, by rfl⟩ : syracuseStep 2178485 = 204233) (by norm_num)
theorem B1293869 : Blo 678312 1293869 := bbase (se 3 (by rfl) ⟨242600, by rfl⟩ : syracuseStep 1293869 = 485201) (by norm_num)
theorem B1719893 : Blo 678312 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B7749269 : Blo 678312 7749269 := bbase (se 6 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 7749269 = 363247) (by norm_num)
theorem B1031837 : Blo 678312 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B1031869 : Blo 678312 1031869 := bbase (se 3 (by rfl) ⟨193475, by rfl⟩ : syracuseStep 1031869 = 386951) (by norm_num)
theorem B2244341 : Blo 678312 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B966421 : Blo 678312 966421 := bbase (se 6 (by rfl) ⟨22650, by rfl⟩ : syracuseStep 966421 = 45301) (by norm_num)
theorem B1294157 : Blo 678312 1294157 := bbase (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) (by norm_num)
theorem B3358549 : Blo 678312 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1720237 : Blo 678312 1720237 := bbase (se 3 (by rfl) ⟨322544, by rfl⟩ : syracuseStep 1720237 = 645089) (by norm_num)
theorem B1294309 : Blo 678312 1294309 := bbase (se 4 (by rfl) ⟨121341, by rfl⟩ : syracuseStep 1294309 = 242683) (by norm_num)
theorem B1720349 : Blo 678312 1720349 := bbase (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) (by norm_num)
theorem B966757 : Blo 678312 966757 := bbase (se 4 (by rfl) ⟨90633, by rfl⟩ : syracuseStep 966757 = 181267) (by norm_num)
theorem B1720541 : Blo 678312 1720541 := bbase (se 3 (by rfl) ⟨322601, by rfl⟩ : syracuseStep 1720541 = 645203) (by norm_num)
theorem B1032421 : Blo 678312 1032421 := bbase (se 4 (by rfl) ⟨96789, by rfl⟩ : syracuseStep 1032421 = 193579) (by norm_num)
theorem B1655045 : Blo 678312 1655045 := bbase (se 4 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 1655045 = 310321) (by norm_num)
theorem B1294613 : Blo 678312 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B966973 : Blo 678312 966973 := bbase (se 3 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 966973 = 362615) (by norm_num)
theorem B2900357 : Blo 678312 2900357 := bbase (se 4 (by rfl) ⟨271908, by rfl⟩ : syracuseStep 2900357 = 543817) (by norm_num)
theorem B1229261 : Blo 678312 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B1163813 : Blo 678312 1163813 := bbase (se 4 (by rfl) ⟨109107, by rfl⟩ : syracuseStep 1163813 = 218215) (by norm_num)
theorem B1720885 : Blo 678312 1720885 := bbase (se 5 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 1720885 = 161333) (by norm_num)
theorem B1229413 : Blo 678312 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B1720997 : Blo 678312 1720997 := bbase (se 4 (by rfl) ⟨161343, by rfl⟩ : syracuseStep 1720997 = 322687) (by norm_num)
theorem B967349 : Blo 678312 967349 := bbase (se 5 (by rfl) ⟨45344, by rfl⟩ : syracuseStep 967349 = 90689) (by norm_num)
theorem B3687221 : Blo 678312 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B1721189 : Blo 678312 1721189 := bbase (se 4 (by rfl) ⟨161361, by rfl⟩ : syracuseStep 1721189 = 322723) (by norm_num)
theorem B3884021 : Blo 678312 3884021 := bbase (se 5 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 3884021 = 364127) (by norm_num)
theorem B1721533 : Blo 678312 1721533 := bbase (se 3 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 1721533 = 645575) (by norm_num)
theorem B1721645 : Blo 678312 1721645 := bbase (se 3 (by rfl) ⟨322808, by rfl⟩ : syracuseStep 1721645 = 645617) (by norm_num)
theorem B2180405 : Blo 678312 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B2901365 : Blo 678312 2901365 := bbase (se 5 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 2901365 = 272003) (by norm_num)
theorem B1033589 : Blo 678312 1033589 := bbase (se 5 (by rfl) ⟨48449, by rfl⟩ : syracuseStep 1033589 = 96899) (by norm_num)
theorem B1721837 : Blo 678312 1721837 := bbase (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) (by norm_num)
theorem B4966069 : Blo 678312 4966069 := bbase (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) (by norm_num)
theorem B1722181 : Blo 678312 1722181 := bbase (se 4 (by rfl) ⟨161454, by rfl⟩ : syracuseStep 1722181 = 322909) (by norm_num)
theorem B1722293 : Blo 678312 1722293 := bbase (se 5 (by rfl) ⟨80732, by rfl⟩ : syracuseStep 1722293 = 161465) (by norm_num)
theorem B968773 : Blo 678312 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B1722485 : Blo 678312 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B3885205 : Blo 678312 3885205 := bbase (se 6 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 3885205 = 182119) (by norm_num)
theorem B1034453 : Blo 678312 1034453 := bbase (se 7 (by rfl) ⟨12122, by rfl⟩ : syracuseStep 1034453 = 24245) (by norm_num)
theorem B1722829 : Blo 678312 1722829 := bbase (se 3 (by rfl) ⟨323030, by rfl⟩ : syracuseStep 1722829 = 646061) (by norm_num)
theorem B1526237 : Blo 678312 1526237 := bbase (se 3 (by rfl) ⟨286169, by rfl⟩ : syracuseStep 1526237 = 572339) (by norm_num)
theorem B3262997 : Blo 678312 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B1526309 : Blo 678312 1526309 := bbase (se 4 (by rfl) ⟨143091, by rfl⟩ : syracuseStep 1526309 = 286183) (by norm_num)
theorem B1722941 : Blo 678312 1722941 := bbase (se 3 (by rfl) ⟨323051, by rfl⟩ : syracuseStep 1722941 = 646103) (by norm_num)
theorem B1526381 : Blo 678312 1526381 := bbase (se 3 (by rfl) ⟨286196, by rfl⟩ : syracuseStep 1526381 = 572393) (by norm_num)
theorem B969365 : Blo 678312 969365 := bbase (se 6 (by rfl) ⟨22719, by rfl⟩ : syracuseStep 969365 = 45439) (by norm_num)
theorem B1526453 : Blo 678312 1526453 := bbase (se 5 (by rfl) ⟨71552, by rfl⟩ : syracuseStep 1526453 = 143105) (by norm_num)
theorem B2181829 : Blo 678312 2181829 := bbase (se 4 (by rfl) ⟨204546, by rfl⟩ : syracuseStep 2181829 = 409093) (by norm_num)
theorem B969445 : Blo 678312 969445 := bbase (se 4 (by rfl) ⟨90885, by rfl⟩ : syracuseStep 969445 = 181771) (by norm_num)
theorem B1526525 : Blo 678312 1526525 := bbase (se 3 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 1526525 = 572447) (by norm_num)
theorem B1723133 : Blo 678312 1723133 := bbase (se 3 (by rfl) ⟨323087, by rfl⟩ : syracuseStep 1723133 = 646175) (by norm_num)
theorem B1526597 : Blo 678312 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B969565 : Blo 678312 969565 := bbase (se 3 (by rfl) ⟨181793, by rfl⟩ : syracuseStep 969565 = 363587) (by norm_num)
theorem B1526669 : Blo 678312 1526669 := bbase (se 3 (by rfl) ⟨286250, by rfl⟩ : syracuseStep 1526669 = 572501) (by norm_num)
theorem B3263381 : Blo 678312 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B969661 : Blo 678312 969661 := bbase (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) (by norm_num)
theorem B1526741 : Blo 678312 1526741 := bbase (se 7 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 1526741 = 35783) (by norm_num)
theorem B1526813 : Blo 678312 1526813 := bbase (se 3 (by rfl) ⟨286277, by rfl⟩ : syracuseStep 1526813 = 572555) (by norm_num)
theorem B1723477 : Blo 678312 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B1526885 : Blo 678312 1526885 := bbase (se 4 (by rfl) ⟨143145, by rfl⟩ : syracuseStep 1526885 = 286291) (by norm_num)
theorem B2903141 : Blo 678312 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B2182277 : Blo 678312 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B1526957 : Blo 678312 1526957 := bbase (se 3 (by rfl) ⟨286304, by rfl⟩ : syracuseStep 1526957 = 572609) (by norm_num)
theorem B1723589 : Blo 678312 1723589 := bbase (se 4 (by rfl) ⟨161586, by rfl⟩ : syracuseStep 1723589 = 323173) (by norm_num)
theorem B1527029 : Blo 678312 1527029 := bbase (se 5 (by rfl) ⟨71579, by rfl⟩ : syracuseStep 1527029 = 143159) (by norm_num)
theorem B5918005 : Blo 678312 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B1527101 : Blo 678312 1527101 := bbase (se 3 (by rfl) ⟨286331, by rfl⟩ : syracuseStep 1527101 = 572663) (by norm_num)
theorem B1527173 : Blo 678312 1527173 := bbase (se 4 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 1527173 = 286345) (by norm_num)
theorem B1723781 : Blo 678312 1723781 := bbase (se 4 (by rfl) ⟨161604, by rfl⟩ : syracuseStep 1723781 = 323209) (by norm_num)
theorem B970157 : Blo 678312 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B1527245 : Blo 678312 1527245 := bbase (se 3 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 1527245 = 572717) (by norm_num)
theorem B1527317 : Blo 678312 1527317 := bbase (se 6 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 1527317 = 71593) (by norm_num)
theorem B1527389 : Blo 678312 1527389 := bbase (se 3 (by rfl) ⟨286385, by rfl⟩ : syracuseStep 1527389 = 572771) (by norm_num)
theorem B1166989 : Blo 678312 1166989 := bbase (se 3 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 1166989 = 437621) (by norm_num)
theorem B1527461 : Blo 678312 1527461 := bbase (se 4 (by rfl) ⟨143199, by rfl⟩ : syracuseStep 1527461 = 286399) (by norm_num)
theorem B1724125 : Blo 678312 1724125 := bbase (se 3 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 1724125 = 646547) (by norm_num)
theorem B1527533 : Blo 678312 1527533 := bbase (se 3 (by rfl) ⟨286412, by rfl⟩ : syracuseStep 1527533 = 572825) (by norm_num)
theorem B773905 : Blo 678312 773905 := bbase (se 2 (by rfl) ⟨290214, by rfl⟩ : syracuseStep 773905 = 580429) (by norm_num)
theorem B1527605 : Blo 678312 1527605 := bbase (se 5 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 1527605 = 143213) (by norm_num)
theorem B1724237 : Blo 678312 1724237 := bbase (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) (by norm_num)
theorem B2445173 : Blo 678312 2445173 := bbase (se 5 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 2445173 = 229235) (by norm_num)
theorem B1527677 : Blo 678312 1527677 := bbase (se 3 (by rfl) ⟨286439, by rfl⟩ : syracuseStep 1527677 = 572879) (by norm_num)
theorem B1527749 : Blo 678312 1527749 := bbase (se 4 (by rfl) ⟨143226, by rfl⟩ : syracuseStep 1527749 = 286453) (by norm_num)
theorem B970709 : Blo 678312 970709 := bbase (se 7 (by rfl) ⟨11375, by rfl⟩ : syracuseStep 970709 = 22751) (by norm_num)
theorem B1527821 : Blo 678312 1527821 := bbase (se 3 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 1527821 = 572933) (by norm_num)
theorem B1724429 : Blo 678312 1724429 := bbase (se 3 (by rfl) ⟨323330, by rfl⟩ : syracuseStep 1724429 = 646661) (by norm_num)
theorem B872501 : Blo 678312 872501 := bbase (se 5 (by rfl) ⟨40898, by rfl⟩ : syracuseStep 872501 = 81797) (by norm_num)
theorem B1036349 : Blo 678312 1036349 := bbase (se 3 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 1036349 = 388631) (by norm_num)
theorem B1527893 : Blo 678312 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B3723413 : Blo 678312 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B1527965 : Blo 678312 1527965 := bbase (se 3 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 1527965 = 572987) (by norm_num)
theorem B1528037 : Blo 678312 1528037 := bbase (se 4 (by rfl) ⟨143253, by rfl⟩ : syracuseStep 1528037 = 286507) (by norm_num)
theorem B1528109 : Blo 678312 1528109 := bbase (se 3 (by rfl) ⟨286520, by rfl⟩ : syracuseStep 1528109 = 573041) (by norm_num)
theorem B1724773 : Blo 678312 1724773 := bbase (se 4 (by rfl) ⟨161697, by rfl⟩ : syracuseStep 1724773 = 323395) (by norm_num)
theorem B1528181 : Blo 678312 1528181 := bbase (se 5 (by rfl) ⟨71633, by rfl⟩ : syracuseStep 1528181 = 143267) (by norm_num)
theorem B1528253 : Blo 678312 1528253 := bbase (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) (by norm_num)
theorem B1724885 : Blo 678312 1724885 := bbase (se 7 (by rfl) ⟨20213, by rfl⟩ : syracuseStep 1724885 = 40427) (by norm_num)
theorem B1528325 : Blo 678312 1528325 := bbase (se 4 (by rfl) ⟨143280, by rfl⟩ : syracuseStep 1528325 = 286561) (by norm_num)
theorem B1528397 : Blo 678312 1528397 := bbase (se 3 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 1528397 = 573149) (by norm_num)
theorem B1528469 : Blo 678312 1528469 := bbase (se 6 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 1528469 = 71647) (by norm_num)
theorem B1725077 : Blo 678312 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B971461 : Blo 678312 971461 := bbase (se 4 (by rfl) ⟨91074, by rfl⟩ : syracuseStep 971461 = 182149) (by norm_num)
theorem B1528541 : Blo 678312 1528541 := bbase (se 3 (by rfl) ⟨286601, by rfl⟩ : syracuseStep 1528541 = 573203) (by norm_num)
theorem B1037045 : Blo 678312 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B1528613 : Blo 678312 1528613 := bbase (se 4 (by rfl) ⟨143307, by rfl⟩ : syracuseStep 1528613 = 286615) (by norm_num)
theorem B1528685 : Blo 678312 1528685 := bbase (se 3 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 1528685 = 573257) (by norm_num)
theorem B1528757 : Blo 678312 1528757 := bbase (se 5 (by rfl) ⟨71660, by rfl⟩ : syracuseStep 1528757 = 143321) (by norm_num)
theorem B2577365 : Blo 678312 2577365 := bbase (se 7 (by rfl) ⟨30203, by rfl⟩ : syracuseStep 2577365 = 60407) (by norm_num)
theorem B1725421 : Blo 678312 1725421 := bbase (se 3 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 1725421 = 647033) (by norm_num)
theorem B1528829 : Blo 678312 1528829 := bbase (se 3 (by rfl) ⟨286655, by rfl⟩ : syracuseStep 1528829 = 573311) (by norm_num)
theorem B1528901 : Blo 678312 1528901 := bbase (se 4 (by rfl) ⟨143334, by rfl⟩ : syracuseStep 1528901 = 286669) (by norm_num)
theorem B1725533 : Blo 678312 1725533 := bbase (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) (by norm_num)
theorem B1528973 : Blo 678312 1528973 := bbase (se 3 (by rfl) ⟨286682, by rfl⟩ : syracuseStep 1528973 = 573365) (by norm_num)
theorem B1529045 : Blo 678312 1529045 := bbase (se 7 (by rfl) ⟨17918, by rfl⟩ : syracuseStep 1529045 = 35837) (by norm_num)
theorem B775397 : Blo 678312 775397 := bbase (se 4 (by rfl) ⟨72693, by rfl⟩ : syracuseStep 775397 = 145387) (by norm_num)
theorem B2577653 : Blo 678312 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B2446613 : Blo 678312 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B1529117 : Blo 678312 1529117 := bbase (se 3 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 1529117 = 573419) (by norm_num)
theorem B1725725 : Blo 678312 1725725 := bbase (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) (by norm_num)
theorem B3495221 : Blo 678312 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B11621717 : Blo 678312 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B2184533 : Blo 678312 2184533 := bbase (se 18 (by rfl) ⟨12, by rfl⟩ : syracuseStep 2184533 = 25) (by norm_num)
theorem B1529189 : Blo 678312 1529189 := bbase (se 4 (by rfl) ⟨143361, by rfl⟩ : syracuseStep 1529189 = 286723) (by norm_num)
theorem B1529261 : Blo 678312 1529261 := bbase (se 3 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 1529261 = 573473) (by norm_num)
theorem B1529333 : Blo 678312 1529333 := bbase (se 5 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 1529333 = 143375) (by norm_num)
theorem B1529405 : Blo 678312 1529405 := bbase (se 3 (by rfl) ⟨286763, by rfl⟩ : syracuseStep 1529405 = 573527) (by norm_num)
theorem B1726069 : Blo 678312 1726069 := bbase (se 5 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 1726069 = 161819) (by norm_num)
theorem B1529477 : Blo 678312 1529477 := bbase (se 4 (by rfl) ⟨143388, by rfl⟩ : syracuseStep 1529477 = 286777) (by norm_num)
theorem B1529549 : Blo 678312 1529549 := bbase (se 3 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 1529549 = 573581) (by norm_num)
theorem B1726181 : Blo 678312 1726181 := bbase (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) (by norm_num)
theorem B1529621 : Blo 678312 1529621 := bbase (se 6 (by rfl) ⟨35850, by rfl⟩ : syracuseStep 1529621 = 71701) (by norm_num)
theorem B1529693 : Blo 678312 1529693 := bbase (se 3 (by rfl) ⟨286817, by rfl⟩ : syracuseStep 1529693 = 573635) (by norm_num)
theorem B1529765 : Blo 678312 1529765 := bbase (se 4 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 1529765 = 286831) (by norm_num)
theorem B1726373 : Blo 678312 1726373 := bbase (se 4 (by rfl) ⟨161847, by rfl⟩ : syracuseStep 1726373 = 323695) (by norm_num)
theorem B1529837 : Blo 678312 1529837 := bbase (se 3 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 1529837 = 573689) (by norm_num)
theorem B4347893 : Blo 678312 4347893 := bbase (se 5 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 4347893 = 407615) (by norm_num)
theorem B776237 : Blo 678312 776237 := bbase (se 3 (by rfl) ⟨145544, by rfl⟩ : syracuseStep 776237 = 291089) (by norm_num)
theorem B1529909 : Blo 678312 1529909 := bbase (se 5 (by rfl) ⟨71714, by rfl⟩ : syracuseStep 1529909 = 143429) (by norm_num)
theorem B1529981 : Blo 678312 1529981 := bbase (se 3 (by rfl) ⟨286871, by rfl⟩ : syracuseStep 1529981 = 573743) (by norm_num)
theorem B1530053 : Blo 678312 1530053 := bbase (se 4 (by rfl) ⟨143442, by rfl⟩ : syracuseStep 1530053 = 286885) (by norm_num)
theorem B874729 : Blo 678312 874729 := bbase (se 2 (by rfl) ⟨328023, by rfl⟩ : syracuseStep 874729 = 656047) (by norm_num)
theorem B1726717 : Blo 678312 1726717 := bbase (se 3 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 1726717 = 647519) (by norm_num)
theorem B1530125 : Blo 678312 1530125 := bbase (se 3 (by rfl) ⟨286898, by rfl⟩ : syracuseStep 1530125 = 573797) (by norm_num)
theorem B1530197 : Blo 678312 1530197 := bbase (se 10 (by rfl) ⟨2241, by rfl⟩ : syracuseStep 1530197 = 4483) (by norm_num)
theorem B1726829 : Blo 678312 1726829 := bbase (se 3 (by rfl) ⟨323780, by rfl⟩ : syracuseStep 1726829 = 647561) (by norm_num)
theorem B776569 : Blo 678312 776569 := bbase (se 2 (by rfl) ⟨291213, by rfl⟩ : syracuseStep 776569 = 582427) (by norm_num)
theorem B2578837 : Blo 678312 2578837 := bbase (se 6 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 2578837 = 120883) (by norm_num)
theorem B1530269 : Blo 678312 1530269 := bbase (se 3 (by rfl) ⟨286925, by rfl⟩ : syracuseStep 1530269 = 573851) (by norm_num)
theorem B1399205 : Blo 678312 1399205 := bbase (se 4 (by rfl) ⟨131175, by rfl⟩ : syracuseStep 1399205 = 262351) (by norm_num)
theorem B1661357 : Blo 678312 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B1530341 : Blo 678312 1530341 := bbase (se 4 (by rfl) ⟨143469, by rfl⟩ : syracuseStep 1530341 = 286939) (by norm_num)
theorem B5167637 : Blo 678312 5167637 := bbase (se 6 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 5167637 = 242233) (by norm_num)
theorem B1530413 : Blo 678312 1530413 := bbase (se 3 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 1530413 = 573905) (by norm_num)
theorem B1727021 : Blo 678312 1727021 := bbase (se 3 (by rfl) ⟨323816, by rfl⟩ : syracuseStep 1727021 = 647633) (by norm_num)
theorem B2447941 : Blo 678312 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B1530485 : Blo 678312 1530485 := bbase (se 5 (by rfl) ⟨71741, by rfl⟩ : syracuseStep 1530485 = 143483) (by norm_num)
theorem B776857 : Blo 678312 776857 := bbase (se 2 (by rfl) ⟨291321, by rfl⟩ : syracuseStep 776857 = 582643) (by norm_num)
theorem B1530557 : Blo 678312 1530557 := bbase (se 3 (by rfl) ⟨286979, by rfl⟩ : syracuseStep 1530557 = 573959) (by norm_num)
theorem B2579141 : Blo 678312 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B3496693 : Blo 678312 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B1530629 : Blo 678312 1530629 := bbase (se 4 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 1530629 = 286993) (by norm_num)
theorem B1530701 : Blo 678312 1530701 := bbase (se 3 (by rfl) ⟨287006, by rfl⟩ : syracuseStep 1530701 = 574013) (by norm_num)
theorem B1530773 : Blo 678312 1530773 := bbase (se 6 (by rfl) ⟨35877, by rfl⟩ : syracuseStep 1530773 = 71755) (by norm_num)
theorem B1530845 : Blo 678312 1530845 := bbase (se 3 (by rfl) ⟨287033, by rfl⟩ : syracuseStep 1530845 = 574067) (by norm_num)
theorem B1530917 : Blo 678312 1530917 := bbase (se 4 (by rfl) ⟨143523, by rfl⟩ : syracuseStep 1530917 = 287047) (by norm_num)
theorem B1530989 : Blo 678312 1530989 := bbase (se 3 (by rfl) ⟨287060, by rfl⟩ : syracuseStep 1530989 = 574121) (by norm_num)
theorem B1531061 : Blo 678312 1531061 := bbase (se 5 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 1531061 = 143537) (by norm_num)
theorem B1399997 : Blo 678312 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B744665 : Blo 678312 744665 := bbase (se 2 (by rfl) ⟨279249, by rfl⟩ : syracuseStep 744665 = 558499) (by norm_num)
theorem B1531133 : Blo 678312 1531133 := bbase (se 3 (by rfl) ⟨287087, by rfl⟩ : syracuseStep 1531133 = 574175) (by norm_num)
theorem B2907413 : Blo 678312 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B1531205 : Blo 678312 1531205 := bbase (se 4 (by rfl) ⟨143550, by rfl⟩ : syracuseStep 1531205 = 287101) (by norm_num)
theorem B1531277 : Blo 678312 1531277 := bbase (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) (by norm_num)
theorem B2448805 : Blo 678312 2448805 := bbase (se 4 (by rfl) ⟨229575, by rfl⟩ : syracuseStep 2448805 = 459151) (by norm_num)
theorem B1531349 : Blo 678312 1531349 := bbase (se 7 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 1531349 = 35891) (by norm_num)
theorem B1531421 : Blo 678312 1531421 := bbase (se 3 (by rfl) ⟨287141, by rfl⟩ : syracuseStep 1531421 = 574283) (by norm_num)
theorem B1531493 : Blo 678312 1531493 := bbase (se 4 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 1531493 = 287155) (by norm_num)
theorem B1531565 : Blo 678312 1531565 := bbase (se 3 (by rfl) ⟨287168, by rfl⟩ : syracuseStep 1531565 = 574337) (by norm_num)
theorem B1531637 : Blo 678312 1531637 := bbase (se 5 (by rfl) ⟨71795, by rfl⟩ : syracuseStep 1531637 = 143591) (by norm_num)
theorem B1531709 : Blo 678312 1531709 := bbase (se 3 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 1531709 = 574391) (by norm_num)
theorem B2449253 : Blo 678312 2449253 := bbase (se 4 (by rfl) ⟨229617, by rfl⟩ : syracuseStep 2449253 = 459235) (by norm_num)
theorem B1531781 : Blo 678312 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B1531853 : Blo 678312 1531853 := bbase (se 3 (by rfl) ⟨287222, by rfl⟩ : syracuseStep 1531853 = 574445) (by norm_num)
theorem B2449381 : Blo 678312 2449381 := bbase (se 4 (by rfl) ⟨229629, by rfl⟩ : syracuseStep 2449381 = 459259) (by norm_num)
theorem B1531925 : Blo 678312 1531925 := bbase (se 6 (by rfl) ⟨35904, by rfl⟩ : syracuseStep 1531925 = 71809) (by norm_num)
theorem B1531997 : Blo 678312 1531997 := bbase (se 3 (by rfl) ⟨287249, by rfl⟩ : syracuseStep 1531997 = 574499) (by norm_num)
theorem B1532069 : Blo 678312 1532069 := bbase (se 4 (by rfl) ⟨143631, by rfl⟩ : syracuseStep 1532069 = 287263) (by norm_num)
theorem B1401013 : Blo 678312 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B1532141 : Blo 678312 1532141 := bbase (se 3 (by rfl) ⟨287276, by rfl⟩ : syracuseStep 1532141 = 574553) (by norm_num)
theorem B1532213 : Blo 678312 1532213 := bbase (se 5 (by rfl) ⟨71822, by rfl⟩ : syracuseStep 1532213 = 143645) (by norm_num)
theorem B1532285 : Blo 678312 1532285 := bbase (se 3 (by rfl) ⟨287303, by rfl⟩ : syracuseStep 1532285 = 574607) (by norm_num)
theorem B1532357 : Blo 678312 1532357 := bbase (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) (by norm_num)
theorem B1532429 : Blo 678312 1532429 := bbase (se 3 (by rfl) ⟨287330, by rfl⟩ : syracuseStep 1532429 = 574661) (by norm_num)
theorem B1532501 : Blo 678312 1532501 := bbase (se 8 (by rfl) ⟨8979, by rfl⟩ : syracuseStep 1532501 = 17959) (by norm_num)
theorem B7365269 : Blo 678312 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B1532573 : Blo 678312 1532573 := bbase (se 3 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 1532573 = 574715) (by norm_num)
theorem B1532645 : Blo 678312 1532645 := bbase (se 4 (by rfl) ⟨143685, by rfl⟩ : syracuseStep 1532645 = 287371) (by norm_num)
theorem B2581253 : Blo 678312 2581253 := bbase (se 4 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 2581253 = 483985) (by norm_num)
theorem B1532717 : Blo 678312 1532717 := bbase (se 3 (by rfl) ⟨287384, by rfl⟩ : syracuseStep 1532717 = 574769) (by norm_num)
theorem B1532789 : Blo 678312 1532789 := bbase (se 5 (by rfl) ⟨71849, by rfl⟩ : syracuseStep 1532789 = 143699) (by norm_num)
theorem B1532861 : Blo 678312 1532861 := bbase (se 3 (by rfl) ⟨287411, by rfl⟩ : syracuseStep 1532861 = 574823) (by norm_num)
theorem B2909189 : Blo 678312 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B1532933 : Blo 678312 1532933 := bbase (se 4 (by rfl) ⟨143712, by rfl⟩ : syracuseStep 1532933 = 287425) (by norm_num)
theorem B2581541 : Blo 678312 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B1533005 : Blo 678312 1533005 := bbase (se 3 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 1533005 = 574877) (by norm_num)
theorem B5825621 : Blo 678312 5825621 := bbase (se 8 (by rfl) ⟨34134, by rfl⟩ : syracuseStep 5825621 = 68269) (by norm_num)
theorem B1533077 : Blo 678312 1533077 := bbase (se 6 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 1533077 = 71863) (by norm_num)
theorem B1533149 : Blo 678312 1533149 := bbase (se 3 (by rfl) ⟨287465, by rfl⟩ : syracuseStep 1533149 = 574931) (by norm_num)
theorem B2909429 : Blo 678312 2909429 := bbase (se 5 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 2909429 = 272759) (by norm_num)
theorem B1533221 : Blo 678312 1533221 := bbase (se 4 (by rfl) ⟨143739, by rfl⟩ : syracuseStep 1533221 = 287479) (by norm_num)
theorem B1533293 : Blo 678312 1533293 := bbase (se 3 (by rfl) ⟨287492, by rfl⟩ : syracuseStep 1533293 = 574985) (by norm_num)
theorem B1631605 : Blo 678312 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B1533365 : Blo 678312 1533365 := bbase (se 5 (by rfl) ⟨71876, by rfl⟩ : syracuseStep 1533365 = 143753) (by norm_num)
theorem B1533437 : Blo 678312 1533437 := bbase (se 3 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 1533437 = 575039) (by norm_num)
theorem B1533509 : Blo 678312 1533509 := bbase (se 4 (by rfl) ⟨143766, by rfl⟩ : syracuseStep 1533509 = 287533) (by norm_num)
theorem B1533581 : Blo 678312 1533581 := bbase (se 3 (by rfl) ⟨287546, by rfl⟩ : syracuseStep 1533581 = 575093) (by norm_num)
theorem B1533653 : Blo 678312 1533653 := bbase (se 7 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 1533653 = 35945) (by norm_num)
theorem B4351765 : Blo 678312 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B1533725 : Blo 678312 1533725 := bbase (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) (by norm_num)
theorem B1533797 : Blo 678312 1533797 := bbase (se 4 (by rfl) ⟨143793, by rfl⟩ : syracuseStep 1533797 = 287587) (by norm_num)
theorem B1533869 : Blo 678312 1533869 := bbase (se 3 (by rfl) ⟨287600, by rfl⟩ : syracuseStep 1533869 = 575201) (by norm_num)
theorem B1632221 : Blo 678312 1632221 := bbase (se 3 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 1632221 = 612083) (by norm_num)
theorem B1533941 : Blo 678312 1533941 := bbase (se 5 (by rfl) ⟨71903, by rfl⟩ : syracuseStep 1533941 = 143807) (by norm_num)
theorem B1534013 : Blo 678312 1534013 := bbase (se 3 (by rfl) ⟨287627, by rfl⟩ : syracuseStep 1534013 = 575255) (by norm_num)
theorem B1534085 : Blo 678312 1534085 := bbase (se 4 (by rfl) ⟨143820, by rfl⟩ : syracuseStep 1534085 = 287641) (by norm_num)
theorem B1632421 : Blo 678312 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B2582725 : Blo 678312 2582725 := bbase (se 4 (by rfl) ⟨242130, by rfl⟩ : syracuseStep 2582725 = 484261) (by norm_num)
theorem B1534157 : Blo 678312 1534157 := bbase (se 3 (by rfl) ⟨287654, by rfl⟩ : syracuseStep 1534157 = 575309) (by norm_num)
theorem B1534229 : Blo 678312 1534229 := bbase (se 6 (by rfl) ⟨35958, by rfl⟩ : syracuseStep 1534229 = 71917) (by norm_num)
theorem B1534301 : Blo 678312 1534301 := bbase (se 3 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 1534301 = 575363) (by norm_num)
theorem B3434885 : Blo 678312 3434885 := bbase (se 4 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 3434885 = 644041) (by norm_num)
theorem B1534373 : Blo 678312 1534373 := bbase (se 4 (by rfl) ⟨143847, by rfl⟩ : syracuseStep 1534373 = 287695) (by norm_num)
theorem B1534445 : Blo 678312 1534445 := bbase (se 3 (by rfl) ⟨287708, by rfl⟩ : syracuseStep 1534445 = 575417) (by norm_num)
theorem B2583029 : Blo 678312 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B3271205 : Blo 678312 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B1534517 : Blo 678312 1534517 := bbase (se 5 (by rfl) ⟨71930, by rfl⟩ : syracuseStep 1534517 = 143861) (by norm_num)
theorem B1534589 : Blo 678312 1534589 := bbase (se 3 (by rfl) ⟨287735, by rfl⟩ : syracuseStep 1534589 = 575471) (by norm_num)
theorem B1534661 : Blo 678312 1534661 := bbase (se 4 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 1534661 = 287749) (by norm_num)
theorem B3304165 : Blo 678312 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B1534733 : Blo 678312 1534733 := bbase (se 3 (by rfl) ⟨287762, by rfl⟩ : syracuseStep 1534733 = 575525) (by norm_num)
theorem B23554901 : Blo 678312 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B1534805 : Blo 678312 1534805 := bbase (se 9 (by rfl) ⟨4496, by rfl⟩ : syracuseStep 1534805 = 8993) (by norm_num)
theorem B1534877 : Blo 678312 1534877 := bbase (se 3 (by rfl) ⟨287789, by rfl⟩ : syracuseStep 1534877 = 575579) (by norm_num)
theorem B1633229 : Blo 678312 1633229 := bbase (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) (by norm_num)
theorem B1534949 : Blo 678312 1534949 := bbase (se 4 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 1534949 = 287803) (by norm_num)
theorem B1535021 : Blo 678312 1535021 := bbase (se 3 (by rfl) ⟨287816, by rfl⟩ : syracuseStep 1535021 = 575633) (by norm_num)
theorem B6548597 : Blo 678312 6548597 := bbase (se 5 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 6548597 = 613931) (by norm_num)
theorem B1535093 : Blo 678312 1535093 := bbase (se 5 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 1535093 = 143915) (by norm_num)
theorem B1535165 : Blo 678312 1535165 := bbase (se 3 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 1535165 = 575687) (by norm_num)
theorem B3140965 : Blo 678312 3140965 := bbase (se 4 (by rfl) ⟨294465, by rfl⟩ : syracuseStep 3140965 = 588931) (by norm_num)
theorem B2911717 : Blo 678312 2911717 := bbase (se 4 (by rfl) ⟨272973, by rfl⟩ : syracuseStep 2911717 = 545947) (by norm_num)
theorem B3141109 : Blo 678312 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B3436181 : Blo 678312 3436181 := bbase (se 6 (by rfl) ⟨80535, by rfl⟩ : syracuseStep 3436181 = 161071) (by norm_num)
theorem B1633997 : Blo 678312 1633997 := bbase (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) (by norm_num)
theorem B1699717 : Blo 678312 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B2289653 : Blo 678312 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B5828597 : Blo 678312 5828597 := bbase (se 5 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 5828597 = 546431) (by norm_num)
theorem B815125 : Blo 678312 815125 := bbase (se 6 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 815125 = 38209) (by norm_num)
theorem B815153 : Blo 678312 815153 := bbase (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) (by norm_num)
theorem B2290085 : Blo 678312 2290085 := bbase (se 4 (by rfl) ⟨214695, by rfl⟩ : syracuseStep 2290085 = 429391) (by norm_num)
theorem B815653 : Blo 678312 815653 := bbase (se 4 (by rfl) ⟨76467, by rfl⟩ : syracuseStep 815653 = 152935) (by norm_num)
theorem B2585141 : Blo 678312 2585141 := bbase (se 5 (by rfl) ⟨121178, by rfl⟩ : syracuseStep 2585141 = 242357) (by norm_num)
theorem B2290517 : Blo 678312 2290517 := bbase (se 9 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 2290517 = 13421) (by norm_num)
theorem B2585429 : Blo 678312 2585429 := bbase (se 9 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 2585429 = 15149) (by norm_num)
theorem B26178389 : Blo 678312 26178389 := bbase (se 9 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 26178389 = 153389) (by norm_num)
theorem B13103957 : Blo 678312 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B3437477 : Blo 678312 3437477 := bbase (se 4 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 3437477 = 644527) (by norm_num)
theorem B2913205 : Blo 678312 2913205 := bbase (se 5 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 2913205 = 273113) (by norm_num)
theorem B2913221 : Blo 678312 2913221 := bbase (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) (by norm_num)
theorem B947197 : Blo 678312 947197 := bbase (se 3 (by rfl) ⟨177599, by rfl⟩ : syracuseStep 947197 = 355199) (by norm_num)
theorem B5796917 : Blo 678312 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B980029 : Blo 678312 980029 := bbase (se 3 (by rfl) ⟨183755, by rfl⟩ : syracuseStep 980029 = 367511) (by norm_num)
theorem B2290949 : Blo 678312 2290949 := bbase (se 4 (by rfl) ⟨214776, by rfl⟩ : syracuseStep 2290949 = 429553) (by norm_num)
theorem B2520341 : Blo 678312 2520341 := bbase (se 6 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 2520341 = 118141) (by norm_num)
theorem B3863861 : Blo 678312 3863861 := bbase (se 5 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 3863861 = 362237) (by norm_num)
theorem B1635709 : Blo 678312 1635709 := bbase (se 3 (by rfl) ⟨306695, by rfl⟩ : syracuseStep 1635709 = 613391) (by norm_num)
theorem B1471981 : Blo 678312 1471981 := bbase (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) (by norm_num)
theorem B3929717 : Blo 678312 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B2619013 : Blo 678312 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B5502613 : Blo 678312 5502613 := bbase (se 6 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 5502613 = 257935) (by norm_num)
theorem B2291381 : Blo 678312 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B816841 : Blo 678312 816841 := bbase (se 2 (by rfl) ⟨306315, by rfl⟩ : syracuseStep 816841 = 612631) (by norm_num)
theorem B6190805 : Blo 678312 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B3143477 : Blo 678312 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B1144685 : Blo 678312 1144685 := bbase (se 3 (by rfl) ⟨214628, by rfl⟩ : syracuseStep 1144685 = 429257) (by norm_num)
theorem B817033 : Blo 678312 817033 := bbase (se 2 (by rfl) ⟨306387, by rfl⟩ : syracuseStep 817033 = 612775) (by norm_num)
theorem B2947013 : Blo 678312 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1636325 : Blo 678312 1636325 := bbase (se 4 (by rfl) ⟨153405, by rfl⟩ : syracuseStep 1636325 = 306811) (by norm_num)
theorem B1144813 : Blo 678312 1144813 := bbase (se 3 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 1144813 = 429305) (by norm_num)
theorem B817133 : Blo 678312 817133 := bbase (se 3 (by rfl) ⟨153212, by rfl⟩ : syracuseStep 817133 = 306425) (by norm_num)
theorem B6191093 : Blo 678312 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B2586613 : Blo 678312 2586613 := bbase (se 5 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 2586613 = 242495) (by norm_num)
theorem B1144901 : Blo 678312 1144901 := bbase (se 4 (by rfl) ⟨107334, by rfl⟩ : syracuseStep 1144901 = 214669) (by norm_num)
theorem B2291813 : Blo 678312 2291813 := bbase (se 4 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 2291813 = 429715) (by norm_num)
theorem B5175413 : Blo 678312 5175413 := bbase (se 5 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 5175413 = 485195) (by norm_num)
theorem B3438773 : Blo 678312 3438773 := bbase (se 5 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 3438773 = 322385) (by norm_num)
theorem B1145029 : Blo 678312 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B1145117 : Blo 678312 1145117 := bbase (se 3 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 1145117 = 429419) (by norm_num)
theorem B2586917 : Blo 678312 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B1636757 : Blo 678312 1636757 := bbase (se 6 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 1636757 = 76723) (by norm_num)
theorem B1145245 : Blo 678312 1145245 := bbase (se 3 (by rfl) ⟨214733, by rfl⟩ : syracuseStep 1145245 = 429467) (by norm_num)
theorem B1145333 : Blo 678312 1145333 := bbase (se 5 (by rfl) ⟨53687, by rfl⟩ : syracuseStep 1145333 = 107375) (by norm_num)
theorem B2292245 : Blo 678312 2292245 := bbase (se 6 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 2292245 = 107449) (by norm_num)
theorem B1145461 : Blo 678312 1145461 := bbase (se 5 (by rfl) ⟨53693, by rfl⟩ : syracuseStep 1145461 = 107387) (by norm_num)
theorem B1931941 : Blo 678312 1931941 := bbase (se 4 (by rfl) ⟨181119, by rfl⟩ : syracuseStep 1931941 = 362239) (by norm_num)
theorem B1145549 : Blo 678312 1145549 := bbase (se 3 (by rfl) ⟨214790, by rfl⟩ : syracuseStep 1145549 = 429581) (by norm_num)
theorem B6224597 : Blo 678312 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B817921 : Blo 678312 817921 := bbase (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) (by norm_num)
theorem B1178389 : Blo 678312 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B1145677 : Blo 678312 1145677 := bbase (se 3 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 1145677 = 429629) (by norm_num)
theorem B2456405 : Blo 678312 2456405 := bbase (se 9 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 2456405 = 14393) (by norm_num)
theorem B1145765 : Blo 678312 1145765 := bbase (se 4 (by rfl) ⟨107415, by rfl⟩ : syracuseStep 1145765 = 214831) (by norm_num)
theorem B2292677 : Blo 678312 2292677 := bbase (se 4 (by rfl) ⟨214938, by rfl⟩ : syracuseStep 2292677 = 429877) (by norm_num)
theorem B7076821 : Blo 678312 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B1145893 : Blo 678312 1145893 := bbase (se 4 (by rfl) ⟨107427, by rfl⟩ : syracuseStep 1145893 = 214855) (by norm_num)
theorem B1145981 : Blo 678312 1145981 := bbase (se 3 (by rfl) ⟨214871, by rfl⟩ : syracuseStep 1145981 = 429743) (by norm_num)
theorem B1309861 : Blo 678312 1309861 := bbase (se 4 (by rfl) ⟨122799, by rfl⟩ : syracuseStep 1309861 = 245599) (by norm_num)
theorem B2456821 : Blo 678312 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B1146109 : Blo 678312 1146109 := bbase (se 3 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 1146109 = 429791) (by norm_num)
theorem B1146197 : Blo 678312 1146197 := bbase (se 11 (by rfl) ⟨839, by rfl⟩ : syracuseStep 1146197 = 1679) (by norm_num)
theorem B916853 : Blo 678312 916853 := bbase (se 5 (by rfl) ⟨42977, by rfl⟩ : syracuseStep 916853 = 85955) (by norm_num)
theorem B2293109 : Blo 678312 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B3440069 : Blo 678312 3440069 := bbase (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) (by norm_num)
theorem B818633 : Blo 678312 818633 := bbase (se 2 (by rfl) ⟨306987, by rfl⟩ : syracuseStep 818633 = 613975) (by norm_num)
theorem B3866069 : Blo 678312 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1146325 : Blo 678312 1146325 := bbase (se 7 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 1146325 = 26867) (by norm_num)
theorem B18906581 : Blo 678312 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B1179109 : Blo 678312 1179109 := bbase (se 4 (by rfl) ⟨110541, by rfl⟩ : syracuseStep 1179109 = 221083) (by norm_num)
theorem B1146413 : Blo 678312 1146413 := bbase (se 3 (by rfl) ⟨214952, by rfl⟩ : syracuseStep 1146413 = 429905) (by norm_num)
theorem B1637957 : Blo 678312 1637957 := bbase (se 4 (by rfl) ⟨153558, by rfl⟩ : syracuseStep 1637957 = 307117) (by norm_num)
theorem B1146541 : Blo 678312 1146541 := bbase (se 3 (by rfl) ⟨214976, by rfl⟩ : syracuseStep 1146541 = 429953) (by norm_num)
theorem B2752181 : Blo 678312 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B1310453 : Blo 678312 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B1146629 : Blo 678312 1146629 := bbase (se 4 (by rfl) ⟨107496, by rfl⟩ : syracuseStep 1146629 = 214993) (by norm_num)
theorem B818969 : Blo 678312 818969 := bbase (se 2 (by rfl) ⟨307113, by rfl⟩ : syracuseStep 818969 = 614227) (by norm_num)
theorem B2293541 : Blo 678312 2293541 := bbase (se 4 (by rfl) ⟨215019, by rfl⟩ : syracuseStep 2293541 = 430039) (by norm_num)
theorem B1146757 : Blo 678312 1146757 := bbase (se 4 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 1146757 = 215017) (by norm_num)
theorem B819085 : Blo 678312 819085 := bbase (se 3 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 819085 = 307157) (by norm_num)
theorem B819109 : Blo 678312 819109 := bbase (se 4 (by rfl) ⟨76791, by rfl⟩ : syracuseStep 819109 = 153583) (by norm_num)
theorem B786361 : Blo 678312 786361 := bbase (se 2 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 786361 = 589771) (by norm_num)
theorem B1146845 : Blo 678312 1146845 := bbase (se 3 (by rfl) ⟨215033, by rfl⟩ : syracuseStep 1146845 = 430067) (by norm_num)
theorem B5177357 : Blo 678312 5177357 := bstep (se 3 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 5177357 = 1941509) B1941509
theorem B1146899 : Blo 678312 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B3440717 : Blo 678312 3440717 := bstep (se 3 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 3440717 = 1290269) B1290269
theorem B1147027 : Blo 678312 1147027 := bstep (se 1 (by rfl) ⟨860270, by rfl⟩ : syracuseStep 1147027 = 1720541) B1720541
theorem B1868017 : Blo 678312 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B1933571 : Blo 678312 1933571 := bstep (se 1 (by rfl) ⟨1450178, by rfl⟩ : syracuseStep 1933571 = 2900357) B2900357
theorem B1147169 : Blo 678312 1147169 := bstep (se 2 (by rfl) ⟨430188, by rfl⟩ : syracuseStep 1147169 = 860377) B860377
theorem B1376561 : Blo 678312 1376561 := bstep (se 2 (by rfl) ⟨516210, by rfl⟩ : syracuseStep 1376561 = 1032421) B1032421
theorem B9929101 : Blo 678312 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B1147297 : Blo 678312 1147297 := bstep (se 2 (by rfl) ⟨430236, by rfl⟩ : syracuseStep 1147297 = 860473) B860473
theorem B2294189 : Blo 678312 2294189 := bstep (se 3 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 2294189 = 860321) B860321
theorem B1147331 : Blo 678312 1147331 := bstep (se 1 (by rfl) ⟨860498, by rfl⟩ : syracuseStep 1147331 = 1720997) B1720997
theorem B2294243 : Blo 678312 2294243 := bstep (se 1 (by rfl) ⟨1720682, by rfl⟩ : syracuseStep 2294243 = 3441365) B3441365
theorem B2458147 : Blo 678312 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B9306677 : Blo 678312 9306677 := bstep (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) B872501
theorem B1147459 : Blo 678312 1147459 := bstep (se 1 (by rfl) ⟨860594, by rfl⟩ : syracuseStep 1147459 = 1721189) B1721189
theorem B1933901 : Blo 678312 1933901 := bstep (se 3 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 1933901 = 725213) B725213
theorem B7078499 : Blo 678312 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B1933969 : Blo 678312 1933969 := bstep (se 2 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 1933969 = 1450477) B1450477
theorem B2589347 : Blo 678312 2589347 := bstep (se 1 (by rfl) ⟨1942010, by rfl⟩ : syracuseStep 2589347 = 3884021) B3884021
theorem B1147601 : Blo 678312 1147601 := bstep (se 2 (by rfl) ⟨430350, by rfl⟩ : syracuseStep 1147601 = 860701) B860701
theorem B2294513 : Blo 678312 2294513 := bstep (se 2 (by rfl) ⟨860442, by rfl⟩ : syracuseStep 2294513 = 1720885) B1720885
theorem B1639217 : Blo 678312 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1147729 : Blo 678312 1147729 := bstep (se 2 (by rfl) ⟨430398, by rfl⟩ : syracuseStep 1147729 = 860797) B860797
theorem B1147763 : Blo 678312 1147763 := bstep (se 1 (by rfl) ⟨860822, by rfl⟩ : syracuseStep 1147763 = 1721645) B1721645
theorem B1934243 : Blo 678312 1934243 := bstep (se 1 (by rfl) ⟨1450682, by rfl⟩ : syracuseStep 1934243 = 2901365) B2901365
theorem B689059 : Blo 678312 689059 := bstep (se 1 (by rfl) ⟨516794, by rfl⟩ : syracuseStep 689059 = 1033589) B1033589
theorem B19104709 : Blo 678312 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1147891 : Blo 678312 1147891 := bstep (se 1 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 1147891 = 1721837) B1721837
theorem B1148033 : Blo 678312 1148033 := bstep (se 2 (by rfl) ⟨430512, by rfl⟩ : syracuseStep 1148033 = 861025) B861025
theorem B9798853 : Blo 678312 9798853 := bstep (se 4 (by rfl) ⟨918642, by rfl⟩ : syracuseStep 9798853 = 1837285) B1837285
theorem B3278029 : Blo 678312 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B1148161 : Blo 678312 1148161 := bstep (se 2 (by rfl) ⟨430560, by rfl⟩ : syracuseStep 1148161 = 861121) B861121
theorem B2295053 : Blo 678312 2295053 := bstep (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) B860645
theorem B1148195 : Blo 678312 1148195 := bstep (se 1 (by rfl) ⟨861146, by rfl⟩ : syracuseStep 1148195 = 1722293) B1722293
theorem B2590001 : Blo 678312 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B2295107 : Blo 678312 2295107 := bstep (se 1 (by rfl) ⟨1721330, by rfl⟩ : syracuseStep 2295107 = 3442661) B3442661
theorem B1148323 : Blo 678312 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B689635 : Blo 678312 689635 := bstep (se 1 (by rfl) ⟨517226, by rfl⟩ : syracuseStep 689635 = 1034453) B1034453
theorem B1148465 : Blo 678312 1148465 := bstep (se 2 (by rfl) ⟨430674, by rfl⟩ : syracuseStep 1148465 = 861349) B861349
theorem B2295377 : Blo 678312 2295377 := bstep (se 2 (by rfl) ⟨860766, by rfl⟩ : syracuseStep 2295377 = 1721533) B1721533
theorem B1017473 : Blo 678312 1017473 := bstep (se 2 (by rfl) ⟨381552, by rfl⟩ : syracuseStep 1017473 = 763105) B763105
theorem B1017491 : Blo 678312 1017491 := bstep (se 1 (by rfl) ⟨763118, by rfl⟩ : syracuseStep 1017491 = 1526237) B1526237
theorem B1017521 : Blo 678312 1017521 := bstep (se 2 (by rfl) ⟨381570, by rfl⟩ : syracuseStep 1017521 = 763141) B763141
theorem B1148593 : Blo 678312 1148593 := bstep (se 2 (by rfl) ⟨430722, by rfl⟩ : syracuseStep 1148593 = 861445) B861445
theorem B1017539 : Blo 678312 1017539 := bstep (se 1 (by rfl) ⟨763154, by rfl⟩ : syracuseStep 1017539 = 1526309) B1526309
theorem B4130509 : Blo 678312 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B1148627 : Blo 678312 1148627 := bstep (se 1 (by rfl) ⟨861470, by rfl⟩ : syracuseStep 1148627 = 1722941) B1722941
theorem B1017569 : Blo 678312 1017569 := bstep (se 2 (by rfl) ⟨381588, by rfl⟩ : syracuseStep 1017569 = 763177) B763177
theorem B1935085 : Blo 678312 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B1017587 : Blo 678312 1017587 := bstep (se 1 (by rfl) ⟨763190, by rfl⟩ : syracuseStep 1017587 = 1526381) B1526381
theorem B1017617 : Blo 678312 1017617 := bstep (se 2 (by rfl) ⟨381606, by rfl⟩ : syracuseStep 1017617 = 763213) B763213
theorem B1017635 : Blo 678312 1017635 := bstep (se 1 (by rfl) ⟨763226, by rfl⟩ : syracuseStep 1017635 = 1526453) B1526453
theorem B1017665 : Blo 678312 1017665 := bstep (se 2 (by rfl) ⟨381624, by rfl⟩ : syracuseStep 1017665 = 763249) B763249
theorem B1017683 : Blo 678312 1017683 := bstep (se 1 (by rfl) ⟨763262, by rfl⟩ : syracuseStep 1017683 = 1526525) B1526525
theorem B1148755 : Blo 678312 1148755 := bstep (se 1 (by rfl) ⟨861566, by rfl⟩ : syracuseStep 1148755 = 1723133) B1723133
theorem B1017713 : Blo 678312 1017713 := bstep (se 2 (by rfl) ⟨381642, by rfl⟩ : syracuseStep 1017713 = 763285) B763285
theorem B1017731 : Blo 678312 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B1935245 : Blo 678312 1935245 := bstep (se 3 (by rfl) ⟨362858, by rfl⟩ : syracuseStep 1935245 = 725717) B725717
theorem B1017761 : Blo 678312 1017761 := bstep (se 2 (by rfl) ⟨381660, by rfl⟩ : syracuseStep 1017761 = 763321) B763321
theorem B1017779 : Blo 678312 1017779 := bstep (se 1 (by rfl) ⟨763334, by rfl⟩ : syracuseStep 1017779 = 1526669) B1526669
theorem B1017809 : Blo 678312 1017809 := bstep (se 2 (by rfl) ⟨381678, by rfl⟩ : syracuseStep 1017809 = 763357) B763357
theorem B1148897 : Blo 678312 1148897 := bstep (se 2 (by rfl) ⟨430836, by rfl⟩ : syracuseStep 1148897 = 861673) B861673
theorem B1017827 : Blo 678312 1017827 := bstep (se 1 (by rfl) ⟨763370, by rfl⟩ : syracuseStep 1017827 = 1526741) B1526741
theorem B1017857 : Blo 678312 1017857 := bstep (se 2 (by rfl) ⟨381696, by rfl⟩ : syracuseStep 1017857 = 763393) B763393
theorem B1017875 : Blo 678312 1017875 := bstep (se 1 (by rfl) ⟨763406, by rfl⟩ : syracuseStep 1017875 = 1526813) B1526813
theorem B1017905 : Blo 678312 1017905 := bstep (se 2 (by rfl) ⟨381714, by rfl⟩ : syracuseStep 1017905 = 763429) B763429
theorem B1017923 : Blo 678312 1017923 := bstep (se 1 (by rfl) ⟨763442, by rfl⟩ : syracuseStep 1017923 = 1526885) B1526885
theorem B1935427 : Blo 678312 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B1017953 : Blo 678312 1017953 := bstep (se 2 (by rfl) ⟨381732, by rfl⟩ : syracuseStep 1017953 = 763465) B763465
theorem B1149025 : Blo 678312 1149025 := bstep (se 2 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 1149025 = 861769) B861769
theorem B2295917 : Blo 678312 2295917 := bstep (se 3 (by rfl) ⟨430484, by rfl⟩ : syracuseStep 2295917 = 860969) B860969
theorem B1017971 : Blo 678312 1017971 := bstep (se 1 (by rfl) ⟨763478, by rfl⟩ : syracuseStep 1017971 = 1526957) B1526957
theorem B1149059 : Blo 678312 1149059 := bstep (se 1 (by rfl) ⟨861794, by rfl⟩ : syracuseStep 1149059 = 1723589) B1723589
theorem B1018001 : Blo 678312 1018001 := bstep (se 2 (by rfl) ⟨381750, by rfl⟩ : syracuseStep 1018001 = 763501) B763501
theorem B1837201 : Blo 678312 1837201 := bstep (se 2 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 1837201 = 1377901) B1377901
theorem B1018019 : Blo 678312 1018019 := bstep (se 1 (by rfl) ⟨763514, by rfl⟩ : syracuseStep 1018019 = 1527029) B1527029
theorem B2295971 : Blo 678312 2295971 := bstep (se 1 (by rfl) ⟨1721978, by rfl⟩ : syracuseStep 2295971 = 3443957) B3443957
theorem B1018049 : Blo 678312 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B1018067 : Blo 678312 1018067 := bstep (se 1 (by rfl) ⟨763550, by rfl⟩ : syracuseStep 1018067 = 1527101) B1527101
theorem B1018097 : Blo 678312 1018097 := bstep (se 2 (by rfl) ⟨381786, by rfl⟩ : syracuseStep 1018097 = 763573) B763573
theorem B6621425 : Blo 678312 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1018115 : Blo 678312 1018115 := bstep (se 1 (by rfl) ⟨763586, by rfl⟩ : syracuseStep 1018115 = 1527173) B1527173
theorem B1149187 : Blo 678312 1149187 := bstep (se 1 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 1149187 = 1723781) B1723781
theorem B1018145 : Blo 678312 1018145 := bstep (se 2 (by rfl) ⟨381804, by rfl⟩ : syracuseStep 1018145 = 763609) B763609
theorem B1018163 : Blo 678312 1018163 := bstep (se 1 (by rfl) ⟨763622, by rfl⟩ : syracuseStep 1018163 = 1527245) B1527245
theorem B1018193 : Blo 678312 1018193 := bstep (se 2 (by rfl) ⟨381822, by rfl⟩ : syracuseStep 1018193 = 763645) B763645
theorem B1018211 : Blo 678312 1018211 := bstep (se 1 (by rfl) ⟨763658, by rfl⟩ : syracuseStep 1018211 = 1527317) B1527317
theorem B5802353 : Blo 678312 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B1018241 : Blo 678312 1018241 := bstep (se 2 (by rfl) ⟨381840, by rfl⟩ : syracuseStep 1018241 = 763681) B763681
theorem B1149329 : Blo 678312 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B1018259 : Blo 678312 1018259 := bstep (se 1 (by rfl) ⟨763694, by rfl⟩ : syracuseStep 1018259 = 1527389) B1527389
theorem B1018289 : Blo 678312 1018289 := bstep (se 2 (by rfl) ⟨381858, by rfl⟩ : syracuseStep 1018289 = 763717) B763717
theorem B2296241 : Blo 678312 2296241 := bstep (se 2 (by rfl) ⟨861090, by rfl⟩ : syracuseStep 2296241 = 1722181) B1722181
theorem B1018307 : Blo 678312 1018307 := bstep (se 1 (by rfl) ⟨763730, by rfl⟩ : syracuseStep 1018307 = 1527461) B1527461
theorem B1018337 : Blo 678312 1018337 := bstep (se 2 (by rfl) ⟨381876, by rfl⟩ : syracuseStep 1018337 = 763753) B763753
theorem B1018355 : Blo 678312 1018355 := bstep (se 1 (by rfl) ⟨763766, by rfl⟩ : syracuseStep 1018355 = 1527533) B1527533
theorem B1018385 : Blo 678312 1018385 := bstep (se 2 (by rfl) ⟨381894, by rfl⟩ : syracuseStep 1018385 = 763789) B763789
theorem B1149457 : Blo 678312 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B1018403 : Blo 678312 1018403 := bstep (se 1 (by rfl) ⟨763802, by rfl⟩ : syracuseStep 1018403 = 1527605) B1527605
theorem B1149491 : Blo 678312 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B1018433 : Blo 678312 1018433 := bstep (se 2 (by rfl) ⟨381912, by rfl⟩ : syracuseStep 1018433 = 763825) B763825
theorem B920129 : Blo 678312 920129 := bstep (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) B690097
theorem B1018451 : Blo 678312 1018451 := bstep (se 1 (by rfl) ⟨763838, by rfl⟩ : syracuseStep 1018451 = 1527677) B1527677
theorem B1018481 : Blo 678312 1018481 := bstep (se 2 (by rfl) ⟨381930, by rfl⟩ : syracuseStep 1018481 = 763861) B763861
theorem B1018499 : Blo 678312 1018499 := bstep (se 1 (by rfl) ⟨763874, by rfl⟩ : syracuseStep 1018499 = 1527749) B1527749
theorem B1018529 : Blo 678312 1018529 := bstep (se 2 (by rfl) ⟨381948, by rfl⟩ : syracuseStep 1018529 = 763897) B763897
theorem B1018547 : Blo 678312 1018547 := bstep (se 1 (by rfl) ⟨763910, by rfl⟩ : syracuseStep 1018547 = 1527821) B1527821
theorem B1149619 : Blo 678312 1149619 := bstep (se 1 (by rfl) ⟨862214, by rfl⟩ : syracuseStep 1149619 = 1724429) B1724429
theorem B1018577 : Blo 678312 1018577 := bstep (se 2 (by rfl) ⟨381966, by rfl⟩ : syracuseStep 1018577 = 763933) B763933
theorem B1018595 : Blo 678312 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B1018625 : Blo 678312 1018625 := bstep (se 2 (by rfl) ⟨381984, by rfl⟩ : syracuseStep 1018625 = 763969) B763969
theorem B1018643 : Blo 678312 1018643 := bstep (se 1 (by rfl) ⟨763982, by rfl⟩ : syracuseStep 1018643 = 1527965) B1527965
theorem B1018673 : Blo 678312 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B1149761 : Blo 678312 1149761 := bstep (se 2 (by rfl) ⟨431160, by rfl⟩ : syracuseStep 1149761 = 862321) B862321
theorem B1018691 : Blo 678312 1018691 := bstep (se 1 (by rfl) ⟨764018, by rfl⟩ : syracuseStep 1018691 = 1528037) B1528037
theorem B1018721 : Blo 678312 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B5180273 : Blo 678312 5180273 := bstep (se 2 (by rfl) ⟨1942602, by rfl⟩ : syracuseStep 5180273 = 3885205) B3885205
theorem B1018739 : Blo 678312 1018739 := bstep (se 1 (by rfl) ⟨764054, by rfl⟩ : syracuseStep 1018739 = 1528109) B1528109
theorem B1018769 : Blo 678312 1018769 := bstep (se 2 (by rfl) ⟨382038, by rfl⟩ : syracuseStep 1018769 = 764077) B764077
theorem B2329489 : Blo 678312 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B1018787 : Blo 678312 1018787 := bstep (se 1 (by rfl) ⟨764090, by rfl⟩ : syracuseStep 1018787 = 1528181) B1528181
theorem B3443633 : Blo 678312 3443633 := bstep (se 2 (by rfl) ⟨1291362, by rfl⟩ : syracuseStep 3443633 = 2582725) B2582725
theorem B1018817 : Blo 678312 1018817 := bstep (se 2 (by rfl) ⟨382056, by rfl⟩ : syracuseStep 1018817 = 764113) B764113
theorem B1149889 : Blo 678312 1149889 := bstep (se 2 (by rfl) ⟨431208, by rfl⟩ : syracuseStep 1149889 = 862417) B862417
theorem B2296781 : Blo 678312 2296781 := bstep (se 3 (by rfl) ⟨430646, by rfl⟩ : syracuseStep 2296781 = 861293) B861293
theorem B1018835 : Blo 678312 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B1149923 : Blo 678312 1149923 := bstep (se 1 (by rfl) ⟨862442, by rfl⟩ : syracuseStep 1149923 = 1724885) B1724885
theorem B1018865 : Blo 678312 1018865 := bstep (se 2 (by rfl) ⟨382074, by rfl⟩ : syracuseStep 1018865 = 764149) B764149
theorem B1018883 : Blo 678312 1018883 := bstep (se 1 (by rfl) ⟨764162, by rfl⟩ : syracuseStep 1018883 = 1528325) B1528325
theorem B2296835 : Blo 678312 2296835 := bstep (se 1 (by rfl) ⟨1722626, by rfl⟩ : syracuseStep 2296835 = 3445253) B3445253
theorem B1018913 : Blo 678312 1018913 := bstep (se 2 (by rfl) ⟨382092, by rfl⟩ : syracuseStep 1018913 = 764185) B764185
theorem B1018931 : Blo 678312 1018931 := bstep (se 1 (by rfl) ⟨764198, by rfl⟩ : syracuseStep 1018931 = 1528397) B1528397
theorem B1018961 : Blo 678312 1018961 := bstep (se 2 (by rfl) ⟨382110, by rfl⟩ : syracuseStep 1018961 = 764221) B764221
theorem B1018979 : Blo 678312 1018979 := bstep (se 1 (by rfl) ⟨764234, by rfl⟩ : syracuseStep 1018979 = 1528469) B1528469
theorem B1150051 : Blo 678312 1150051 := bstep (se 1 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 1150051 = 1725077) B1725077
theorem B1019009 : Blo 678312 1019009 := bstep (se 2 (by rfl) ⟨382128, by rfl⟩ : syracuseStep 1019009 = 764257) B764257
theorem B1019027 : Blo 678312 1019027 := bstep (se 1 (by rfl) ⟨764270, by rfl⟩ : syracuseStep 1019027 = 1528541) B1528541
theorem B691363 : Blo 678312 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B1019057 : Blo 678312 1019057 := bstep (se 2 (by rfl) ⟨382146, by rfl⟩ : syracuseStep 1019057 = 764293) B764293
theorem B1117363 : Blo 678312 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B1019075 : Blo 678312 1019075 := bstep (se 1 (by rfl) ⟨764306, by rfl⟩ : syracuseStep 1019075 = 1528613) B1528613
theorem B1019105 : Blo 678312 1019105 := bstep (se 2 (by rfl) ⟨382164, by rfl⟩ : syracuseStep 1019105 = 764329) B764329
theorem B1150193 : Blo 678312 1150193 := bstep (se 2 (by rfl) ⟨431322, by rfl⟩ : syracuseStep 1150193 = 862645) B862645
theorem B1019123 : Blo 678312 1019123 := bstep (se 1 (by rfl) ⟨764342, by rfl⟩ : syracuseStep 1019123 = 1528685) B1528685
theorem B2067725 : Blo 678312 2067725 := bstep (se 3 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 2067725 = 775397) B775397
theorem B1019153 : Blo 678312 1019153 := bstep (se 2 (by rfl) ⟨382182, by rfl⟩ : syracuseStep 1019153 = 764365) B764365
theorem B2297105 : Blo 678312 2297105 := bstep (se 2 (by rfl) ⟨861414, by rfl⟩ : syracuseStep 2297105 = 1722829) B1722829
theorem B1019171 : Blo 678312 1019171 := bstep (se 1 (by rfl) ⟨764378, by rfl⟩ : syracuseStep 1019171 = 1528757) B1528757
theorem B1019201 : Blo 678312 1019201 := bstep (se 2 (by rfl) ⟨382200, by rfl⟩ : syracuseStep 1019201 = 764401) B764401
theorem B1019219 : Blo 678312 1019219 := bstep (se 1 (by rfl) ⟨764414, by rfl⟩ : syracuseStep 1019219 = 1528829) B1528829
theorem B1019249 : Blo 678312 1019249 := bstep (se 2 (by rfl) ⟨382218, by rfl⟩ : syracuseStep 1019249 = 764437) B764437
theorem B1150321 : Blo 678312 1150321 := bstep (se 2 (by rfl) ⟨431370, by rfl⟩ : syracuseStep 1150321 = 862741) B862741
theorem B1019267 : Blo 678312 1019267 := bstep (se 1 (by rfl) ⟨764450, by rfl⟩ : syracuseStep 1019267 = 1528901) B1528901
theorem B1150355 : Blo 678312 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B1019297 : Blo 678312 1019297 := bstep (se 2 (by rfl) ⟨382236, by rfl⟩ : syracuseStep 1019297 = 764473) B764473
theorem B1936817 : Blo 678312 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B1019315 : Blo 678312 1019315 := bstep (se 1 (by rfl) ⟨764486, by rfl⟩ : syracuseStep 1019315 = 1528973) B1528973
theorem B1019345 : Blo 678312 1019345 := bstep (se 2 (by rfl) ⟨382254, by rfl⟩ : syracuseStep 1019345 = 764509) B764509
theorem B1019363 : Blo 678312 1019363 := bstep (se 1 (by rfl) ⟨764522, by rfl⟩ : syracuseStep 1019363 = 1529045) B1529045
theorem B1019393 : Blo 678312 1019393 := bstep (se 2 (by rfl) ⟨382272, by rfl⟩ : syracuseStep 1019393 = 764545) B764545
theorem B1019411 : Blo 678312 1019411 := bstep (se 1 (by rfl) ⟨764558, by rfl⟩ : syracuseStep 1019411 = 1529117) B1529117
theorem B1150483 : Blo 678312 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B2330147 : Blo 678312 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B1019441 : Blo 678312 1019441 := bstep (se 2 (by rfl) ⟨382290, by rfl⟩ : syracuseStep 1019441 = 764581) B764581
theorem B1019459 : Blo 678312 1019459 := bstep (se 1 (by rfl) ⟨764594, by rfl⟩ : syracuseStep 1019459 = 1529189) B1529189
theorem B1019489 : Blo 678312 1019489 := bstep (se 2 (by rfl) ⟨382308, by rfl⟩ : syracuseStep 1019489 = 764617) B764617
theorem B1019507 : Blo 678312 1019507 := bstep (se 1 (by rfl) ⟨764630, by rfl⟩ : syracuseStep 1019507 = 1529261) B1529261
theorem B1019537 : Blo 678312 1019537 := bstep (se 2 (by rfl) ⟨382326, by rfl⟩ : syracuseStep 1019537 = 764653) B764653
theorem B1150625 : Blo 678312 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B1019555 : Blo 678312 1019555 := bstep (se 1 (by rfl) ⟨764666, by rfl⟩ : syracuseStep 1019555 = 1529333) B1529333
theorem B1019585 : Blo 678312 1019585 := bstep (se 2 (by rfl) ⟨382344, by rfl⟩ : syracuseStep 1019585 = 764689) B764689
theorem B1019603 : Blo 678312 1019603 := bstep (se 1 (by rfl) ⟨764702, by rfl⟩ : syracuseStep 1019603 = 1529405) B1529405
theorem B1019633 : Blo 678312 1019633 := bstep (se 2 (by rfl) ⟨382362, by rfl⟩ : syracuseStep 1019633 = 764725) B764725
theorem B1019651 : Blo 678312 1019651 := bstep (se 1 (by rfl) ⟨764738, by rfl⟩ : syracuseStep 1019651 = 1529477) B1529477
theorem B1019681 : Blo 678312 1019681 := bstep (se 2 (by rfl) ⟨382380, by rfl⟩ : syracuseStep 1019681 = 764761) B764761
theorem B1150753 : Blo 678312 1150753 := bstep (se 2 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 1150753 = 863065) B863065
theorem B2297645 : Blo 678312 2297645 := bstep (se 3 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 2297645 = 861617) B861617
theorem B1019699 : Blo 678312 1019699 := bstep (se 1 (by rfl) ⟨764774, by rfl⟩ : syracuseStep 1019699 = 1529549) B1529549
theorem B1150787 : Blo 678312 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B1019729 : Blo 678312 1019729 := bstep (se 2 (by rfl) ⟨382398, by rfl⟩ : syracuseStep 1019729 = 764797) B764797
theorem B1019747 : Blo 678312 1019747 := bstep (se 1 (by rfl) ⟨764810, by rfl⟩ : syracuseStep 1019747 = 1529621) B1529621
theorem B2297699 : Blo 678312 2297699 := bstep (se 1 (by rfl) ⟨1723274, by rfl⟩ : syracuseStep 2297699 = 3446549) B3446549
theorem B1019777 : Blo 678312 1019777 := bstep (se 2 (by rfl) ⟨382416, by rfl⟩ : syracuseStep 1019777 = 764833) B764833
theorem B1019795 : Blo 678312 1019795 := bstep (se 1 (by rfl) ⟨764846, by rfl⟩ : syracuseStep 1019795 = 1529693) B1529693
theorem B1019825 : Blo 678312 1019825 := bstep (se 2 (by rfl) ⟨382434, by rfl⟩ : syracuseStep 1019825 = 764869) B764869
theorem B1019843 : Blo 678312 1019843 := bstep (se 1 (by rfl) ⟨764882, by rfl⟩ : syracuseStep 1019843 = 1529765) B1529765
theorem B1150915 : Blo 678312 1150915 := bstep (se 1 (by rfl) ⟨863186, by rfl⟩ : syracuseStep 1150915 = 1726373) B1726373
theorem B1019873 : Blo 678312 1019873 := bstep (se 2 (by rfl) ⟨382452, by rfl⟩ : syracuseStep 1019873 = 764905) B764905
theorem B8851427 : Blo 678312 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B1019891 : Blo 678312 1019891 := bstep (se 1 (by rfl) ⟨764918, by rfl⟩ : syracuseStep 1019891 = 1529837) B1529837
theorem B4362245 : Blo 678312 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B1019921 : Blo 678312 1019921 := bstep (se 2 (by rfl) ⟨382470, by rfl⟩ : syracuseStep 1019921 = 764941) B764941
theorem B1019939 : Blo 678312 1019939 := bstep (se 1 (by rfl) ⟨764954, by rfl⟩ : syracuseStep 1019939 = 1529909) B1529909
theorem B1019969 : Blo 678312 1019969 := bstep (se 2 (by rfl) ⟨382488, by rfl⟩ : syracuseStep 1019969 = 764977) B764977
theorem B725059 : Blo 678312 725059 := bstep (se 1 (by rfl) ⟨543794, by rfl⟩ : syracuseStep 725059 = 1087589) B1087589
theorem B1151057 : Blo 678312 1151057 := bstep (se 2 (by rfl) ⟨431646, by rfl⟩ : syracuseStep 1151057 = 863293) B863293
theorem B1019987 : Blo 678312 1019987 := bstep (se 1 (by rfl) ⟨764990, by rfl⟩ : syracuseStep 1019987 = 1529981) B1529981
theorem B10457201 : Blo 678312 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B1020017 : Blo 678312 1020017 := bstep (se 2 (by rfl) ⟨382506, by rfl⟩ : syracuseStep 1020017 = 765013) B765013
theorem B2297969 : Blo 678312 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B1020035 : Blo 678312 1020035 := bstep (se 1 (by rfl) ⟨765026, by rfl⟩ : syracuseStep 1020035 = 1530053) B1530053
theorem B1020065 : Blo 678312 1020065 := bstep (se 2 (by rfl) ⟨382524, by rfl⟩ : syracuseStep 1020065 = 765049) B765049
theorem B1020083 : Blo 678312 1020083 := bstep (se 1 (by rfl) ⟨765062, by rfl⟩ : syracuseStep 1020083 = 1530125) B1530125
theorem B1020113 : Blo 678312 1020113 := bstep (se 2 (by rfl) ⟨382542, by rfl⟩ : syracuseStep 1020113 = 765085) B765085
theorem B1151185 : Blo 678312 1151185 := bstep (se 2 (by rfl) ⟨431694, by rfl⟩ : syracuseStep 1151185 = 863389) B863389
theorem B1020131 : Blo 678312 1020131 := bstep (se 1 (by rfl) ⟨765098, by rfl⟩ : syracuseStep 1020131 = 1530197) B1530197
theorem B1151219 : Blo 678312 1151219 := bstep (se 1 (by rfl) ⟨863414, by rfl⟩ : syracuseStep 1151219 = 1726829) B1726829
theorem B1020161 : Blo 678312 1020161 := bstep (se 2 (by rfl) ⟨382560, by rfl⟩ : syracuseStep 1020161 = 765121) B765121
theorem B1020179 : Blo 678312 1020179 := bstep (se 1 (by rfl) ⟨765134, by rfl⟩ : syracuseStep 1020179 = 1530269) B1530269
theorem B1020209 : Blo 678312 1020209 := bstep (se 2 (by rfl) ⟨382578, by rfl⟩ : syracuseStep 1020209 = 765157) B765157
theorem B1020227 : Blo 678312 1020227 := bstep (se 1 (by rfl) ⟨765170, by rfl⟩ : syracuseStep 1020227 = 1530341) B1530341
theorem B1020257 : Blo 678312 1020257 := bstep (se 2 (by rfl) ⟨382596, by rfl⟩ : syracuseStep 1020257 = 765193) B765193
theorem B3445091 : Blo 678312 3445091 := bstep (se 1 (by rfl) ⟨2583818, by rfl⟩ : syracuseStep 3445091 = 5167637) B5167637
theorem B1937773 : Blo 678312 1937773 := bstep (se 3 (by rfl) ⟨363332, by rfl⟩ : syracuseStep 1937773 = 726665) B726665
theorem B1020275 : Blo 678312 1020275 := bstep (se 1 (by rfl) ⟨765206, by rfl⟩ : syracuseStep 1020275 = 1530413) B1530413
theorem B1151347 : Blo 678312 1151347 := bstep (se 1 (by rfl) ⟨863510, by rfl⟩ : syracuseStep 1151347 = 1727021) B1727021
theorem B1020305 : Blo 678312 1020305 := bstep (se 2 (by rfl) ⟨382614, by rfl⟩ : syracuseStep 1020305 = 765229) B765229
theorem B1020323 : Blo 678312 1020323 := bstep (se 1 (by rfl) ⟨765242, by rfl⟩ : syracuseStep 1020323 = 1530485) B1530485
theorem B922033 : Blo 678312 922033 := bstep (se 2 (by rfl) ⟨345762, by rfl⟩ : syracuseStep 922033 = 691525) B691525
theorem B1020353 : Blo 678312 1020353 := bstep (se 2 (by rfl) ⟨382632, by rfl⟩ : syracuseStep 1020353 = 765265) B765265
theorem B1020371 : Blo 678312 1020371 := bstep (se 1 (by rfl) ⟨765278, by rfl⟩ : syracuseStep 1020371 = 1530557) B1530557
theorem B1020401 : Blo 678312 1020401 := bstep (se 2 (by rfl) ⟨382650, by rfl⟩ : syracuseStep 1020401 = 765301) B765301
theorem B1020419 : Blo 678312 1020419 := bstep (se 1 (by rfl) ⟨765314, by rfl⟩ : syracuseStep 1020419 = 1530629) B1530629
theorem B1020449 : Blo 678312 1020449 := bstep (se 2 (by rfl) ⟨382668, by rfl⟩ : syracuseStep 1020449 = 765337) B765337
theorem B1020467 : Blo 678312 1020467 := bstep (se 1 (by rfl) ⟨765350, by rfl⟩ : syracuseStep 1020467 = 1530701) B1530701
theorem B1020497 : Blo 678312 1020497 := bstep (se 2 (by rfl) ⟨382686, by rfl⟩ : syracuseStep 1020497 = 765373) B765373
theorem B1938001 : Blo 678312 1938001 := bstep (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) B1453501
theorem B1020515 : Blo 678312 1020515 := bstep (se 1 (by rfl) ⟨765386, by rfl⟩ : syracuseStep 1020515 = 1530773) B1530773
theorem B9835121 : Blo 678312 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B1020545 : Blo 678312 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B2298509 : Blo 678312 2298509 := bstep (se 3 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 2298509 = 861941) B861941
theorem B1020563 : Blo 678312 1020563 := bstep (se 1 (by rfl) ⟨765422, by rfl⟩ : syracuseStep 1020563 = 1530845) B1530845
theorem B1020593 : Blo 678312 1020593 := bstep (se 2 (by rfl) ⟨382722, by rfl⟩ : syracuseStep 1020593 = 765445) B765445
theorem B1020611 : Blo 678312 1020611 := bstep (se 1 (by rfl) ⟨765458, by rfl⟩ : syracuseStep 1020611 = 1530917) B1530917
theorem B2298563 : Blo 678312 2298563 := bstep (se 1 (by rfl) ⟨1723922, by rfl⟩ : syracuseStep 2298563 = 3447845) B3447845
theorem B1020641 : Blo 678312 1020641 := bstep (se 2 (by rfl) ⟨382740, by rfl⟩ : syracuseStep 1020641 = 765481) B765481
theorem B1938161 : Blo 678312 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1020659 : Blo 678312 1020659 := bstep (se 1 (by rfl) ⟨765494, by rfl⟩ : syracuseStep 1020659 = 1530989) B1530989
theorem B1020689 : Blo 678312 1020689 := bstep (se 2 (by rfl) ⟨382758, by rfl⟩ : syracuseStep 1020689 = 765517) B765517
theorem B1020707 : Blo 678312 1020707 := bstep (se 1 (by rfl) ⟨765530, by rfl⟩ : syracuseStep 1020707 = 1531061) B1531061
theorem B1020737 : Blo 678312 1020737 := bstep (se 2 (by rfl) ⟨382776, by rfl⟩ : syracuseStep 1020737 = 765553) B765553
theorem B1020755 : Blo 678312 1020755 := bstep (se 1 (by rfl) ⟨765566, by rfl⟩ : syracuseStep 1020755 = 1531133) B1531133
theorem B1938275 : Blo 678312 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B1020785 : Blo 678312 1020785 := bstep (se 2 (by rfl) ⟨382794, by rfl⟩ : syracuseStep 1020785 = 765589) B765589
theorem B1020803 : Blo 678312 1020803 := bstep (se 1 (by rfl) ⟨765602, by rfl⟩ : syracuseStep 1020803 = 1531205) B1531205
theorem B1020833 : Blo 678312 1020833 := bstep (se 2 (by rfl) ⟨382812, by rfl⟩ : syracuseStep 1020833 = 765625) B765625
theorem B1020851 : Blo 678312 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B1020881 : Blo 678312 1020881 := bstep (se 2 (by rfl) ⟨382830, by rfl⟩ : syracuseStep 1020881 = 765661) B765661
theorem B2298833 : Blo 678312 2298833 := bstep (se 2 (by rfl) ⟨862062, by rfl⟩ : syracuseStep 2298833 = 1724125) B1724125
theorem B1020899 : Blo 678312 1020899 := bstep (se 1 (by rfl) ⟨765674, by rfl⟩ : syracuseStep 1020899 = 1531349) B1531349
theorem B1020929 : Blo 678312 1020929 := bstep (se 2 (by rfl) ⟨382848, by rfl⟩ : syracuseStep 1020929 = 765697) B765697
theorem B1020947 : Blo 678312 1020947 := bstep (se 1 (by rfl) ⟨765710, by rfl⟩ : syracuseStep 1020947 = 1531421) B1531421
theorem B1020977 : Blo 678312 1020977 := bstep (se 2 (by rfl) ⟨382866, by rfl⟩ : syracuseStep 1020977 = 765733) B765733
theorem B726067 : Blo 678312 726067 := bstep (se 1 (by rfl) ⟨544550, by rfl⟩ : syracuseStep 726067 = 1089101) B1089101
theorem B1020995 : Blo 678312 1020995 := bstep (se 1 (by rfl) ⟨765746, by rfl⟩ : syracuseStep 1020995 = 1531493) B1531493
theorem B1021025 : Blo 678312 1021025 := bstep (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) B765769
theorem B1021043 : Blo 678312 1021043 := bstep (se 1 (by rfl) ⟨765782, by rfl⟩ : syracuseStep 1021043 = 1531565) B1531565
theorem B3445901 : Blo 678312 3445901 := bstep (se 3 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 3445901 = 1292213) B1292213
theorem B1021073 : Blo 678312 1021073 := bstep (se 2 (by rfl) ⟨382902, by rfl⟩ : syracuseStep 1021073 = 765805) B765805
theorem B1021091 : Blo 678312 1021091 := bstep (se 1 (by rfl) ⟨765818, by rfl⟩ : syracuseStep 1021091 = 1531637) B1531637
theorem B2266289 : Blo 678312 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B1021121 : Blo 678312 1021121 := bstep (se 2 (by rfl) ⟨382920, by rfl⟩ : syracuseStep 1021121 = 765841) B765841
theorem B1021139 : Blo 678312 1021139 := bstep (se 1 (by rfl) ⟨765854, by rfl⟩ : syracuseStep 1021139 = 1531709) B1531709
theorem B1021169 : Blo 678312 1021169 := bstep (se 2 (by rfl) ⟨382938, by rfl⟩ : syracuseStep 1021169 = 765877) B765877
theorem B1021187 : Blo 678312 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B1021217 : Blo 678312 1021217 := bstep (se 2 (by rfl) ⟨382956, by rfl⟩ : syracuseStep 1021217 = 765913) B765913
theorem B1021235 : Blo 678312 1021235 := bstep (se 1 (by rfl) ⟨765926, by rfl⟩ : syracuseStep 1021235 = 1531853) B1531853
theorem B5051717 : Blo 678312 5051717 := bstep (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) B947197
theorem B1021265 : Blo 678312 1021265 := bstep (se 2 (by rfl) ⟨382974, by rfl⟩ : syracuseStep 1021265 = 765949) B765949
theorem B1021283 : Blo 678312 1021283 := bstep (se 1 (by rfl) ⟨765962, by rfl⟩ : syracuseStep 1021283 = 1531925) B1531925
theorem B1086833 : Blo 678312 1086833 := bstep (se 2 (by rfl) ⟨407562, by rfl⟩ : syracuseStep 1086833 = 815125) B815125
theorem B1021313 : Blo 678312 1021313 := bstep (se 2 (by rfl) ⟨382992, by rfl⟩ : syracuseStep 1021313 = 765985) B765985
theorem B1021331 : Blo 678312 1021331 := bstep (se 1 (by rfl) ⟨765998, by rfl⟩ : syracuseStep 1021331 = 1531997) B1531997
theorem B1021361 : Blo 678312 1021361 := bstep (se 2 (by rfl) ⟨383010, by rfl⟩ : syracuseStep 1021361 = 766021) B766021
theorem B1021379 : Blo 678312 1021379 := bstep (se 1 (by rfl) ⟨766034, by rfl⟩ : syracuseStep 1021379 = 1532069) B1532069
theorem B2069965 : Blo 678312 2069965 := bstep (se 3 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 2069965 = 776237) B776237
theorem B1021409 : Blo 678312 1021409 := bstep (se 2 (by rfl) ⟨383028, by rfl⟩ : syracuseStep 1021409 = 766057) B766057
theorem B2299373 : Blo 678312 2299373 := bstep (se 3 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 2299373 = 862265) B862265
theorem B1021427 : Blo 678312 1021427 := bstep (se 1 (by rfl) ⟨766070, by rfl⟩ : syracuseStep 1021427 = 1532141) B1532141
theorem B1021457 : Blo 678312 1021457 := bstep (se 2 (by rfl) ⟨383046, by rfl⟩ : syracuseStep 1021457 = 766093) B766093
theorem B1021475 : Blo 678312 1021475 := bstep (se 1 (by rfl) ⟨766106, by rfl⟩ : syracuseStep 1021475 = 1532213) B1532213
theorem B2299427 : Blo 678312 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B1021505 : Blo 678312 1021505 := bstep (se 2 (by rfl) ⟨383064, by rfl⟩ : syracuseStep 1021505 = 766129) B766129
theorem B1021523 : Blo 678312 1021523 := bstep (se 1 (by rfl) ⟨766142, by rfl⟩ : syracuseStep 1021523 = 1532285) B1532285
theorem B1021553 : Blo 678312 1021553 := bstep (se 2 (by rfl) ⟨383082, by rfl⟩ : syracuseStep 1021553 = 766165) B766165
theorem B1021571 : Blo 678312 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B1021601 : Blo 678312 1021601 := bstep (se 2 (by rfl) ⟨383100, by rfl⟩ : syracuseStep 1021601 = 766201) B766201
theorem B1021619 : Blo 678312 1021619 := bstep (se 1 (by rfl) ⟨766214, by rfl⟩ : syracuseStep 1021619 = 1532429) B1532429
theorem B1021649 : Blo 678312 1021649 := bstep (se 2 (by rfl) ⟨383118, by rfl⟩ : syracuseStep 1021649 = 766237) B766237
theorem B1021667 : Blo 678312 1021667 := bstep (se 1 (by rfl) ⟨766250, by rfl⟩ : syracuseStep 1021667 = 1532501) B1532501
theorem B1021697 : Blo 678312 1021697 := bstep (se 2 (by rfl) ⟨383136, by rfl⟩ : syracuseStep 1021697 = 766273) B766273
theorem B1021715 : Blo 678312 1021715 := bstep (se 1 (by rfl) ⟨766286, by rfl⟩ : syracuseStep 1021715 = 1532573) B1532573
theorem B1021745 : Blo 678312 1021745 := bstep (se 2 (by rfl) ⟨383154, by rfl⟩ : syracuseStep 1021745 = 766309) B766309
theorem B2299697 : Blo 678312 2299697 := bstep (se 2 (by rfl) ⟨862386, by rfl⟩ : syracuseStep 2299697 = 1724773) B1724773
theorem B1021763 : Blo 678312 1021763 := bstep (se 1 (by rfl) ⟨766322, by rfl⟩ : syracuseStep 1021763 = 1532645) B1532645
theorem B1939277 : Blo 678312 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B1021793 : Blo 678312 1021793 := bstep (se 2 (by rfl) ⟨383172, by rfl⟩ : syracuseStep 1021793 = 766345) B766345
theorem B1021811 : Blo 678312 1021811 := bstep (se 1 (by rfl) ⟨766358, by rfl⟩ : syracuseStep 1021811 = 1532717) B1532717
theorem B1021841 : Blo 678312 1021841 := bstep (se 2 (by rfl) ⟨383190, by rfl⟩ : syracuseStep 1021841 = 766381) B766381
theorem B1021859 : Blo 678312 1021859 := bstep (se 1 (by rfl) ⟨766394, by rfl⟩ : syracuseStep 1021859 = 1532789) B1532789
theorem B1021889 : Blo 678312 1021889 := bstep (se 2 (by rfl) ⟨383208, by rfl⟩ : syracuseStep 1021889 = 766417) B766417
theorem B1021907 : Blo 678312 1021907 := bstep (se 1 (by rfl) ⟨766430, by rfl⟩ : syracuseStep 1021907 = 1532861) B1532861
theorem B1021937 : Blo 678312 1021937 := bstep (se 2 (by rfl) ⟨383226, by rfl⟩ : syracuseStep 1021937 = 766453) B766453
theorem B1939459 : Blo 678312 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1021955 : Blo 678312 1021955 := bstep (se 1 (by rfl) ⟨766466, by rfl⟩ : syracuseStep 1021955 = 1532933) B1532933
theorem B1021985 : Blo 678312 1021985 := bstep (se 2 (by rfl) ⟨383244, by rfl⟩ : syracuseStep 1021985 = 766489) B766489
theorem B727075 : Blo 678312 727075 := bstep (se 1 (by rfl) ⟨545306, by rfl⟩ : syracuseStep 727075 = 1090613) B1090613
theorem B1022003 : Blo 678312 1022003 := bstep (se 1 (by rfl) ⟨766502, by rfl⟩ : syracuseStep 1022003 = 1533005) B1533005
theorem B1022033 : Blo 678312 1022033 := bstep (se 2 (by rfl) ⟨383262, by rfl⟩ : syracuseStep 1022033 = 766525) B766525
theorem B1022051 : Blo 678312 1022051 := bstep (se 1 (by rfl) ⟨766538, by rfl⟩ : syracuseStep 1022051 = 1533077) B1533077
theorem B1022081 : Blo 678312 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B1022099 : Blo 678312 1022099 := bstep (se 1 (by rfl) ⟨766574, by rfl⟩ : syracuseStep 1022099 = 1533149) B1533149
theorem B1939619 : Blo 678312 1939619 := bstep (se 1 (by rfl) ⟨1454714, by rfl⟩ : syracuseStep 1939619 = 2909429) B2909429
theorem B1022129 : Blo 678312 1022129 := bstep (se 2 (by rfl) ⟨383298, by rfl⟩ : syracuseStep 1022129 = 766597) B766597
theorem B1022147 : Blo 678312 1022147 := bstep (se 1 (by rfl) ⟨766610, by rfl⟩ : syracuseStep 1022147 = 1533221) B1533221
theorem B1022177 : Blo 678312 1022177 := bstep (se 2 (by rfl) ⟨383316, by rfl⟩ : syracuseStep 1022177 = 766633) B766633
theorem B1022195 : Blo 678312 1022195 := bstep (se 1 (by rfl) ⟨766646, by rfl⟩ : syracuseStep 1022195 = 1533293) B1533293
theorem B5806349 : Blo 678312 5806349 := bstep (se 3 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 5806349 = 2177381) B2177381
theorem B1022225 : Blo 678312 1022225 := bstep (se 2 (by rfl) ⟨383334, by rfl⟩ : syracuseStep 1022225 = 766669) B766669
theorem B1022243 : Blo 678312 1022243 := bstep (se 1 (by rfl) ⟨766682, by rfl⟩ : syracuseStep 1022243 = 1533365) B1533365
theorem B1022273 : Blo 678312 1022273 := bstep (se 2 (by rfl) ⟨383352, by rfl⟩ : syracuseStep 1022273 = 766705) B766705
theorem B2300237 : Blo 678312 2300237 := bstep (se 3 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 2300237 = 862589) B862589
theorem B1022291 : Blo 678312 1022291 := bstep (se 1 (by rfl) ⟨766718, by rfl⟩ : syracuseStep 1022291 = 1533437) B1533437
theorem B1022321 : Blo 678312 1022321 := bstep (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) B766741
theorem B1022339 : Blo 678312 1022339 := bstep (se 1 (by rfl) ⟨766754, by rfl⟩ : syracuseStep 1022339 = 1533509) B1533509
theorem B2300291 : Blo 678312 2300291 := bstep (se 1 (by rfl) ⟨1725218, by rfl⟩ : syracuseStep 2300291 = 3450437) B3450437
theorem B1022369 : Blo 678312 1022369 := bstep (se 2 (by rfl) ⟨383388, by rfl⟩ : syracuseStep 1022369 = 766777) B766777
theorem B1022387 : Blo 678312 1022387 := bstep (se 1 (by rfl) ⟨766790, by rfl⟩ : syracuseStep 1022387 = 1533581) B1533581
theorem B4430285 : Blo 678312 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B1022417 : Blo 678312 1022417 := bstep (se 2 (by rfl) ⟨383406, by rfl⟩ : syracuseStep 1022417 = 766813) B766813
theorem B858595 : Blo 678312 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B1022435 : Blo 678312 1022435 := bstep (se 1 (by rfl) ⟨766826, by rfl⟩ : syracuseStep 1022435 = 1533653) B1533653
theorem B1022465 : Blo 678312 1022465 := bstep (se 2 (by rfl) ⟨383424, by rfl⟩ : syracuseStep 1022465 = 766849) B766849
theorem B1022483 : Blo 678312 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B1022513 : Blo 678312 1022513 := bstep (se 2 (by rfl) ⟨383442, by rfl⟩ : syracuseStep 1022513 = 766885) B766885
theorem B858691 : Blo 678312 858691 := bstep (se 1 (by rfl) ⟨644018, by rfl⟩ : syracuseStep 858691 = 1288037) B1288037
theorem B1022531 : Blo 678312 1022531 := bstep (se 1 (by rfl) ⟨766898, by rfl⟩ : syracuseStep 1022531 = 1533797) B1533797
theorem B1022561 : Blo 678312 1022561 := bstep (se 2 (by rfl) ⟨383460, by rfl⟩ : syracuseStep 1022561 = 766921) B766921
theorem B1022579 : Blo 678312 1022579 := bstep (se 1 (by rfl) ⟨766934, by rfl⟩ : syracuseStep 1022579 = 1533869) B1533869
theorem B2300561 : Blo 678312 2300561 := bstep (se 2 (by rfl) ⟨862710, by rfl⟩ : syracuseStep 2300561 = 1725421) B1725421
theorem B1022609 : Blo 678312 1022609 := bstep (se 2 (by rfl) ⟨383478, by rfl⟩ : syracuseStep 1022609 = 766957) B766957
theorem B1088147 : Blo 678312 1088147 := bstep (se 1 (by rfl) ⟨816110, by rfl⟩ : syracuseStep 1088147 = 1632221) B1632221
theorem B727699 : Blo 678312 727699 := bstep (se 1 (by rfl) ⟨545774, by rfl⟩ : syracuseStep 727699 = 1091549) B1091549
theorem B1022627 : Blo 678312 1022627 := bstep (se 1 (by rfl) ⟨766970, by rfl⟩ : syracuseStep 1022627 = 1533941) B1533941
theorem B1022657 : Blo 678312 1022657 := bstep (se 2 (by rfl) ⟨383496, by rfl⟩ : syracuseStep 1022657 = 766993) B766993
theorem B1022675 : Blo 678312 1022675 := bstep (se 1 (by rfl) ⟨767006, by rfl⟩ : syracuseStep 1022675 = 1534013) B1534013
theorem B1022705 : Blo 678312 1022705 := bstep (se 2 (by rfl) ⟨383514, by rfl⟩ : syracuseStep 1022705 = 767029) B767029
theorem B1022723 : Blo 678312 1022723 := bstep (se 1 (by rfl) ⟨767042, by rfl⟩ : syracuseStep 1022723 = 1534085) B1534085
theorem B3873541 : Blo 678312 3873541 := bstep (se 4 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 3873541 = 726289) B726289
theorem B8723213 : Blo 678312 8723213 := bstep (se 3 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 8723213 = 3271205) B3271205
theorem B1022753 : Blo 678312 1022753 := bstep (se 2 (by rfl) ⟨383532, by rfl⟩ : syracuseStep 1022753 = 767065) B767065
theorem B1022771 : Blo 678312 1022771 := bstep (se 1 (by rfl) ⟨767078, by rfl⟩ : syracuseStep 1022771 = 1534157) B1534157
theorem B1022801 : Blo 678312 1022801 := bstep (se 2 (by rfl) ⟨383550, by rfl⟩ : syracuseStep 1022801 = 767101) B767101
theorem B1022819 : Blo 678312 1022819 := bstep (se 1 (by rfl) ⟨767114, by rfl⟩ : syracuseStep 1022819 = 1534229) B1534229
theorem B1022849 : Blo 678312 1022849 := bstep (se 2 (by rfl) ⟨383568, by rfl⟩ : syracuseStep 1022849 = 767137) B767137
theorem B1022867 : Blo 678312 1022867 := bstep (se 1 (by rfl) ⟨767150, by rfl⟩ : syracuseStep 1022867 = 1534301) B1534301
theorem B1022897 : Blo 678312 1022897 := bstep (se 2 (by rfl) ⟨383586, by rfl⟩ : syracuseStep 1022897 = 767173) B767173
theorem B1022915 : Blo 678312 1022915 := bstep (se 1 (by rfl) ⟨767186, by rfl⟩ : syracuseStep 1022915 = 1534373) B1534373
theorem B31562693 : Blo 678312 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B1022945 : Blo 678312 1022945 := bstep (se 2 (by rfl) ⟨383604, by rfl⟩ : syracuseStep 1022945 = 767209) B767209
theorem B1022963 : Blo 678312 1022963 := bstep (se 1 (by rfl) ⟨767222, by rfl⟩ : syracuseStep 1022963 = 1534445) B1534445
theorem B1022993 : Blo 678312 1022993 := bstep (se 2 (by rfl) ⟨383622, by rfl⟩ : syracuseStep 1022993 = 767245) B767245
theorem B1023011 : Blo 678312 1023011 := bstep (se 1 (by rfl) ⟨767258, by rfl⟩ : syracuseStep 1023011 = 1534517) B1534517
theorem B859187 : Blo 678312 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B1023041 : Blo 678312 1023041 := bstep (se 2 (by rfl) ⟨383640, by rfl⟩ : syracuseStep 1023041 = 767281) B767281
theorem B1023059 : Blo 678312 1023059 := bstep (se 1 (by rfl) ⟨767294, by rfl⟩ : syracuseStep 1023059 = 1534589) B1534589
theorem B1023089 : Blo 678312 1023089 := bstep (se 2 (by rfl) ⟨383658, by rfl⟩ : syracuseStep 1023089 = 767317) B767317
theorem B1023107 : Blo 678312 1023107 := bstep (se 1 (by rfl) ⟨767330, by rfl⟩ : syracuseStep 1023107 = 1534661) B1534661
theorem B1023137 : Blo 678312 1023137 := bstep (se 2 (by rfl) ⟨383676, by rfl⟩ : syracuseStep 1023137 = 767353) B767353
theorem B2301101 : Blo 678312 2301101 := bstep (se 3 (by rfl) ⟨431456, by rfl⟩ : syracuseStep 2301101 = 862913) B862913
theorem B1023155 : Blo 678312 1023155 := bstep (se 1 (by rfl) ⟨767366, by rfl⟩ : syracuseStep 1023155 = 1534733) B1534733
theorem B1940689 : Blo 678312 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B1023185 : Blo 678312 1023185 := bstep (se 2 (by rfl) ⟨383694, by rfl⟩ : syracuseStep 1023185 = 767389) B767389
theorem B2301155 : Blo 678312 2301155 := bstep (se 1 (by rfl) ⟨1725866, by rfl⟩ : syracuseStep 2301155 = 3451733) B3451733
theorem B1023203 : Blo 678312 1023203 := bstep (se 1 (by rfl) ⟨767402, by rfl⟩ : syracuseStep 1023203 = 1534805) B1534805
theorem B1023233 : Blo 678312 1023233 := bstep (se 2 (by rfl) ⟨383712, by rfl⟩ : syracuseStep 1023233 = 767425) B767425
theorem B1023251 : Blo 678312 1023251 := bstep (se 1 (by rfl) ⟨767438, by rfl⟩ : syracuseStep 1023251 = 1534877) B1534877
theorem B1023281 : Blo 678312 1023281 := bstep (se 2 (by rfl) ⟨383730, by rfl⟩ : syracuseStep 1023281 = 767461) B767461
theorem B1088819 : Blo 678312 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B1023299 : Blo 678312 1023299 := bstep (se 1 (by rfl) ⟨767474, by rfl⟩ : syracuseStep 1023299 = 1534949) B1534949
theorem B1023329 : Blo 678312 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B2071921 : Blo 678312 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B1023347 : Blo 678312 1023347 := bstep (se 1 (by rfl) ⟨767510, by rfl⟩ : syracuseStep 1023347 = 1535021) B1535021
theorem B1023377 : Blo 678312 1023377 := bstep (se 2 (by rfl) ⟨383766, by rfl⟩ : syracuseStep 1023377 = 767533) B767533
theorem B4365731 : Blo 678312 4365731 := bstep (se 1 (by rfl) ⟨3274298, by rfl⟩ : syracuseStep 4365731 = 6548597) B6548597
theorem B1023395 : Blo 678312 1023395 := bstep (se 1 (by rfl) ⟨767546, by rfl⟩ : syracuseStep 1023395 = 1535093) B1535093
theorem B1023425 : Blo 678312 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B1023443 : Blo 678312 1023443 := bstep (se 1 (by rfl) ⟨767582, by rfl⟩ : syracuseStep 1023443 = 1535165) B1535165
theorem B2301425 : Blo 678312 2301425 := bstep (se 2 (by rfl) ⟨863034, by rfl⟩ : syracuseStep 2301425 = 1726069) B1726069
theorem B2760227 : Blo 678312 2760227 := bstep (se 1 (by rfl) ⟨2070170, by rfl⟩ : syracuseStep 2760227 = 4140341) B4140341
theorem B1089121 : Blo 678312 1089121 := bstep (se 2 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 1089121 = 816841) B816841
theorem B1449571 : Blo 678312 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B859891 : Blo 678312 859891 := bstep (se 1 (by rfl) ⟨644918, by rfl⟩ : syracuseStep 859891 = 1289837) B1289837
theorem B1089331 : Blo 678312 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B859987 : Blo 678312 859987 := bstep (se 1 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 859987 = 1289981) B1289981
theorem B1089377 : Blo 678312 1089377 := bstep (se 2 (by rfl) ⟨408516, by rfl⟩ : syracuseStep 1089377 = 817033) B817033
theorem B16752581 : Blo 678312 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B3448817 : Blo 678312 3448817 := bstep (se 2 (by rfl) ⟨1293306, by rfl⟩ : syracuseStep 3448817 = 2586613) B2586613
theorem B2301965 : Blo 678312 2301965 := bstep (se 3 (by rfl) ⟨431618, by rfl⟩ : syracuseStep 2301965 = 863237) B863237
theorem B2302019 : Blo 678312 2302019 := bstep (se 1 (by rfl) ⟨1726514, by rfl⟩ : syracuseStep 2302019 = 3453029) B3453029
theorem B860483 : Blo 678312 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B2302289 : Blo 678312 2302289 := bstep (se 2 (by rfl) ⟨863358, by rfl⟩ : syracuseStep 2302289 = 1726717) B1726717
theorem B1941965 : Blo 678312 1941965 := bstep (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) B728237
theorem B5972549 : Blo 678312 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B1942147 : Blo 678312 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B1548977 : Blo 678312 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B1942193 : Blo 678312 1942193 := bstep (se 2 (by rfl) ⟨728322, by rfl⟩ : syracuseStep 1942193 = 1456645) B1456645
theorem B3875525 : Blo 678312 3875525 := bstep (se 4 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 3875525 = 726661) B726661
theorem B1450801 : Blo 678312 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B1680227 : Blo 678312 1680227 := bstep (se 1 (by rfl) ⟨1260170, by rfl⟩ : syracuseStep 1680227 = 2520341) B2520341
theorem B4662257 : Blo 678312 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B861187 : Blo 678312 861187 := bstep (se 1 (by rfl) ⟨645890, by rfl⟩ : syracuseStep 861187 = 1291781) B1291781
theorem B861283 : Blo 678312 861283 := bstep (se 1 (by rfl) ⟨645962, by rfl⟩ : syracuseStep 861283 = 1291925) B1291925
theorem B763123 : Blo 678312 763123 := bstep (se 1 (by rfl) ⟨572342, by rfl⟩ : syracuseStep 763123 = 1144685) B1144685
theorem B1090883 : Blo 678312 1090883 := bstep (se 1 (by rfl) ⟨818162, by rfl⟩ : syracuseStep 1090883 = 1636325) B1636325
theorem B763267 : Blo 678312 763267 := bstep (se 1 (by rfl) ⟨572450, by rfl⟩ : syracuseStep 763267 = 1144901) B1144901
theorem B3450275 : Blo 678312 3450275 := bstep (se 1 (by rfl) ⟨2587706, by rfl⟩ : syracuseStep 3450275 = 5175413) B5175413
theorem B763411 : Blo 678312 763411 := bstep (se 1 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 763411 = 1145117) B1145117
theorem B1746481 : Blo 678312 1746481 := bstep (se 2 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 1746481 = 1309861) B1309861
theorem B861779 : Blo 678312 861779 := bstep (se 1 (by rfl) ⟨646334, by rfl⟩ : syracuseStep 861779 = 1292669) B1292669
theorem B1091171 : Blo 678312 1091171 := bstep (se 1 (by rfl) ⟨818378, by rfl⟩ : syracuseStep 1091171 = 1636757) B1636757
theorem B763555 : Blo 678312 763555 := bstep (se 1 (by rfl) ⟨572666, by rfl⟩ : syracuseStep 763555 = 1145333) B1145333
theorem B763699 : Blo 678312 763699 := bstep (se 1 (by rfl) ⟨572774, by rfl⟩ : syracuseStep 763699 = 1145549) B1145549
theorem B763843 : Blo 678312 763843 := bstep (se 1 (by rfl) ⟨572882, by rfl⟩ : syracuseStep 763843 = 1145765) B1145765
theorem B763987 : Blo 678312 763987 := bstep (se 1 (by rfl) ⟨572990, by rfl⟩ : syracuseStep 763987 = 1145981) B1145981
theorem B3451085 : Blo 678312 3451085 := bstep (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) B1294157
theorem B764131 : Blo 678312 764131 := bstep (se 1 (by rfl) ⟨573098, by rfl⟩ : syracuseStep 764131 = 1146197) B1146197
theorem B1452305 : Blo 678312 1452305 := bstep (se 2 (by rfl) ⟨544614, by rfl⟩ : syracuseStep 1452305 = 1089229) B1089229
theorem B862483 : Blo 678312 862483 := bstep (se 1 (by rfl) ⟨646862, by rfl⟩ : syracuseStep 862483 = 1293725) B1293725
theorem B1452323 : Blo 678312 1452323 := bstep (se 1 (by rfl) ⟨1089242, by rfl⟩ : syracuseStep 1452323 = 2178485) B2178485
theorem B1288561 : Blo 678312 1288561 := bstep (se 2 (by rfl) ⟨483210, by rfl⟩ : syracuseStep 1288561 = 966421) B966421
theorem B764275 : Blo 678312 764275 := bstep (se 1 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 764275 = 1146413) B1146413
theorem B862579 : Blo 678312 862579 := bstep (se 1 (by rfl) ⟨646934, by rfl⟩ : syracuseStep 862579 = 1293869) B1293869
theorem B1091971 : Blo 678312 1091971 := bstep (se 1 (by rfl) ⟨818978, by rfl⟩ : syracuseStep 1091971 = 1637957) B1637957
theorem B2238929 : Blo 678312 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B764419 : Blo 678312 764419 := bstep (se 1 (by rfl) ⟨573314, by rfl⟩ : syracuseStep 764419 = 1146629) B1146629
theorem B1092113 : Blo 678312 1092113 := bstep (se 2 (by rfl) ⟨409542, by rfl⟩ : syracuseStep 1092113 = 819085) B819085
theorem B1092145 : Blo 678312 1092145 := bstep (se 2 (by rfl) ⟨409554, by rfl⟩ : syracuseStep 1092145 = 819109) B819109
theorem B764563 : Blo 678312 764563 := bstep (se 1 (by rfl) ⟨573422, by rfl⟩ : syracuseStep 764563 = 1146845) B1146845
theorem B2206403 : Blo 678312 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B1288963 : Blo 678312 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B764707 : Blo 678312 764707 := bstep (se 1 (by rfl) ⟨573530, by rfl⟩ : syracuseStep 764707 = 1147061) B1147061
theorem B1223473 : Blo 678312 1223473 := bstep (se 2 (by rfl) ⟨458802, by rfl⟩ : syracuseStep 1223473 = 917605) B917605
theorem B1289009 : Blo 678312 1289009 := bstep (se 2 (by rfl) ⟨483378, by rfl⟩ : syracuseStep 1289009 = 966757) B966757
theorem B863075 : Blo 678312 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B764851 : Blo 678312 764851 := bstep (se 1 (by rfl) ⟨573638, by rfl⟩ : syracuseStep 764851 = 1147277) B1147277
theorem B764995 : Blo 678312 764995 := bstep (se 1 (by rfl) ⟨573746, by rfl⟩ : syracuseStep 764995 = 1147493) B1147493
theorem B1289297 : Blo 678312 1289297 := bstep (se 2 (by rfl) ⟨483486, by rfl⟩ : syracuseStep 1289297 = 966973) B966973
theorem B8694965 : Blo 678312 8694965 := bstep (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) B815153
theorem B765139 : Blo 678312 765139 := bstep (se 1 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 765139 = 1147709) B1147709
theorem B4467953 : Blo 678312 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B11054389 : Blo 678312 11054389 := bstep (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) B1036349
theorem B765283 : Blo 678312 765283 := bstep (se 1 (by rfl) ⟨573962, by rfl⟩ : syracuseStep 765283 = 1147925) B1147925
theorem B765427 : Blo 678312 765427 := bstep (se 1 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 765427 = 1148141) B1148141
theorem B765571 : Blo 678312 765571 := bstep (se 1 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 765571 = 1148357) B1148357
theorem B765715 : Blo 678312 765715 := bstep (se 1 (by rfl) ⟨574286, by rfl⟩ : syracuseStep 765715 = 1148573) B1148573
theorem B1290019 : Blo 678312 1290019 := bstep (se 1 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 1290019 = 1935029) B1935029
theorem B4665221 : Blo 678312 4665221 := bstep (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) B874729
theorem B765859 : Blo 678312 765859 := bstep (se 1 (by rfl) ⟨574394, by rfl⟩ : syracuseStep 765859 = 1148789) B1148789
theorem B766003 : Blo 678312 766003 := bstep (se 1 (by rfl) ⟨574502, by rfl⟩ : syracuseStep 766003 = 1149005) B1149005
theorem B766147 : Blo 678312 766147 := bstep (se 1 (by rfl) ⟨574610, by rfl⟩ : syracuseStep 766147 = 1149221) B1149221
theorem B1290467 : Blo 678312 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B1454321 : Blo 678312 1454321 := bstep (se 2 (by rfl) ⟨545370, by rfl⟩ : syracuseStep 1454321 = 1090741) B1090741
theorem B766291 : Blo 678312 766291 := bstep (se 1 (by rfl) ⟨574718, by rfl⟩ : syracuseStep 766291 = 1149437) B1149437
theorem B2175331 : Blo 678312 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B19640717 : Blo 678312 19640717 := bstep (se 3 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 19640717 = 7365269) B7365269
theorem B3879373 : Blo 678312 3879373 := bstep (se 3 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 3879373 = 1454765) B1454765
theorem B766435 : Blo 678312 766435 := bstep (se 1 (by rfl) ⟨574826, by rfl⟩ : syracuseStep 766435 = 1149653) B1149653
theorem B2175473 : Blo 678312 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B1290755 : Blo 678312 1290755 := bstep (se 1 (by rfl) ⟨968066, by rfl⟩ : syracuseStep 1290755 = 1936133) B1936133
theorem B2175587 : Blo 678312 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B766579 : Blo 678312 766579 := bstep (se 1 (by rfl) ⟨574934, by rfl⟩ : syracuseStep 766579 = 1149869) B1149869
theorem B1454851 : Blo 678312 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B766723 : Blo 678312 766723 := bstep (se 1 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 766723 = 1150085) B1150085
theorem B766867 : Blo 678312 766867 := bstep (se 1 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 766867 = 1150301) B1150301
theorem B7943093 : Blo 678312 7943093 := bstep (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) B744665
theorem B767011 : Blo 678312 767011 := bstep (se 1 (by rfl) ⟨575258, by rfl⟩ : syracuseStep 767011 = 1150517) B1150517
theorem B3454001 : Blo 678312 3454001 := bstep (se 2 (by rfl) ⟨1295250, by rfl⟩ : syracuseStep 3454001 = 2590501) B2590501
theorem B1225859 : Blo 678312 1225859 := bstep (se 1 (by rfl) ⟨919394, by rfl⟩ : syracuseStep 1225859 = 1838789) B1838789
theorem B2766001 : Blo 678312 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B767155 : Blo 678312 767155 := bstep (se 1 (by rfl) ⟨575366, by rfl⟩ : syracuseStep 767155 = 1150733) B1150733
theorem B4142285 : Blo 678312 4142285 := bstep (se 3 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 4142285 = 1553357) B1553357
theorem B767299 : Blo 678312 767299 := bstep (se 1 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 767299 = 1150949) B1150949
theorem B1291697 : Blo 678312 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B1226161 : Blo 678312 1226161 := bstep (se 2 (by rfl) ⟨459810, by rfl⟩ : syracuseStep 1226161 = 919621) B919621
theorem B767443 : Blo 678312 767443 := bstep (se 1 (by rfl) ⟨575582, by rfl⟩ : syracuseStep 767443 = 1151165) B1151165
theorem B2176561 : Blo 678312 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B767587 : Blo 678312 767587 := bstep (se 1 (by rfl) ⟨575690, by rfl⟩ : syracuseStep 767587 = 1151381) B1151381
theorem B1717969 : Blo 678312 1717969 := bstep (se 2 (by rfl) ⟨644238, by rfl⟩ : syracuseStep 1717969 = 1288477) B1288477
theorem B1718243 : Blo 678312 1718243 := bstep (se 1 (by rfl) ⟨1288682, by rfl⟩ : syracuseStep 1718243 = 2577365) B2577365
theorem B1226819 : Blo 678312 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B5814413 : Blo 678312 5814413 := bstep (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) B2180405
theorem B1718435 : Blo 678312 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B1456337 : Blo 678312 1456337 := bstep (se 2 (by rfl) ⟨546126, by rfl⟩ : syracuseStep 1456337 = 1092253) B1092253
theorem B7747811 : Blo 678312 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B1456355 : Blo 678312 1456355 := bstep (se 1 (by rfl) ⟨1092266, by rfl⟩ : syracuseStep 1456355 = 2184533) B2184533
theorem B4405553 : Blo 678312 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1292593 : Blo 678312 1292593 := bstep (se 2 (by rfl) ⟨484722, by rfl⟩ : syracuseStep 1292593 = 969445) B969445
theorem B3881357 : Blo 678312 3881357 := bstep (se 3 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 3881357 = 1455509) B1455509
theorem B1292753 : Blo 678312 1292753 := bstep (se 2 (by rfl) ⟨484782, by rfl⟩ : syracuseStep 1292753 = 969565) B969565
theorem B1227395 : Blo 678312 1227395 := bstep (se 1 (by rfl) ⟨920546, by rfl⟩ : syracuseStep 1227395 = 1841093) B1841093
theorem B2898595 : Blo 678312 2898595 := bstep (se 1 (by rfl) ⟨2173946, by rfl⟩ : syracuseStep 2898595 = 4347893) B4347893
theorem B1293155 : Blo 678312 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B1719377 : Blo 678312 1719377 := bstep (se 2 (by rfl) ⟨644766, by rfl⟩ : syracuseStep 1719377 = 1289533) B1289533
theorem B1719427 : Blo 678312 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B965857 : Blo 678312 965857 := bstep (se 2 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 965857 = 724393) B724393
theorem B6208753 : Blo 678312 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B965891 : Blo 678312 965891 := bstep (se 1 (by rfl) ⟨724418, by rfl⟩ : syracuseStep 965891 = 1448837) B1448837
theorem B1719569 : Blo 678312 1719569 := bstep (se 2 (by rfl) ⟨644838, by rfl⟩ : syracuseStep 1719569 = 1289677) B1289677
theorem B3882289 : Blo 678312 3882289 := bstep (se 2 (by rfl) ⟨1455858, by rfl⟩ : syracuseStep 3882289 = 2911717) B2911717
theorem B933331 : Blo 678312 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1555985 : Blo 678312 1555985 := bstep (se 2 (by rfl) ⟨583494, by rfl⟩ : syracuseStep 1555985 = 1166989) B1166989
theorem B1556131 : Blo 678312 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B1031873 : Blo 678312 1031873 := bstep (se 2 (by rfl) ⟨386952, by rfl⟩ : syracuseStep 1031873 = 773905) B773905
theorem B4898531 : Blo 678312 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B1294051 : Blo 678312 1294051 := bstep (se 1 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 1294051 = 1941077) B1941077
theorem B966449 : Blo 678312 966449 := bstep (se 2 (by rfl) ⟨362418, by rfl⟩ : syracuseStep 966449 = 724837) B724837
theorem B966529 : Blo 678312 966529 := bstep (se 2 (by rfl) ⟨362448, by rfl⟩ : syracuseStep 966529 = 724897) B724897
theorem B1294211 : Blo 678312 1294211 := bstep (se 1 (by rfl) ⟨970658, by rfl⟩ : syracuseStep 1294211 = 1941317) B1941317
theorem B1032259 : Blo 678312 1032259 := bstep (se 1 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 1032259 = 1548389) B1548389
theorem B1720561 : Blo 678312 1720561 := bstep (se 2 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 1720561 = 1290421) B1290421
theorem B6209777 : Blo 678312 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B3260749 : Blo 678312 3260749 := bstep (se 3 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 3260749 = 1222781) B1222781
theorem B1720835 : Blo 678312 1720835 := bstep (se 1 (by rfl) ⟨1290626, by rfl⟩ : syracuseStep 1720835 = 2581253) B2581253
theorem B967315 : Blo 678312 967315 := bstep (se 1 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 967315 = 1450973) B1450973
theorem B1721027 : Blo 678312 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B3883747 : Blo 678312 3883747 := bstep (se 1 (by rfl) ⟨2912810, by rfl⟩ : syracuseStep 3883747 = 5825621) B5825621
theorem B1295281 : Blo 678312 1295281 := bstep (se 2 (by rfl) ⟨485730, by rfl⟩ : syracuseStep 1295281 = 971461) B971461
theorem B3687373 : Blo 678312 3687373 := bstep (se 3 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 3687373 = 1382765) B1382765
theorem B3687437 : Blo 678312 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B2901041 : Blo 678312 2901041 := bstep (se 2 (by rfl) ⟨1087890, by rfl⟩ : syracuseStep 2901041 = 2175781) B2175781
theorem B967793 : Blo 678312 967793 := bstep (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) B725845
theorem B3687565 : Blo 678312 3687565 := bstep (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) B1382837
theorem B967907 : Blo 678312 967907 := bstep (se 1 (by rfl) ⟨725930, by rfl⟩ : syracuseStep 967907 = 1451861) B1451861
theorem B3884273 : Blo 678312 3884273 := bstep (se 2 (by rfl) ⟨1456602, by rfl⟩ : syracuseStep 3884273 = 2913205) B2913205
theorem B967987 : Blo 678312 967987 := bstep (se 1 (by rfl) ⟨725990, by rfl⟩ : syracuseStep 967987 = 1451981) B1451981
theorem B1721969 : Blo 678312 1721969 := bstep (se 2 (by rfl) ⟨645738, by rfl⟩ : syracuseStep 1721969 = 1291477) B1291477
theorem B1722019 : Blo 678312 1722019 := bstep (se 1 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 1722019 = 2583029) B2583029
theorem B1722161 : Blo 678312 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B2180945 : Blo 678312 2180945 := bstep (se 2 (by rfl) ⟨817854, by rfl⟩ : syracuseStep 2180945 = 1635709) B1635709
theorem B968545 : Blo 678312 968545 := bstep (se 2 (by rfl) ⟨363204, by rfl⟩ : syracuseStep 968545 = 726409) B726409
theorem B8701937 : Blo 678312 8701937 := bstep (se 2 (by rfl) ⟨3263226, by rfl⟩ : syracuseStep 8701937 = 6526453) B6526453
theorem B3492017 : Blo 678312 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B969251 : Blo 678312 969251 := bstep (se 1 (by rfl) ⟨726938, by rfl⟩ : syracuseStep 969251 = 1453877) B1453877
theorem B1526417 : Blo 678312 1526417 := bstep (se 2 (by rfl) ⟨572406, by rfl⟩ : syracuseStep 1526417 = 1144813) B1144813
theorem B1526435 : Blo 678312 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B3885731 : Blo 678312 3885731 := bstep (se 1 (by rfl) ⟨2914298, by rfl⟩ : syracuseStep 3885731 = 5828597) B5828597
theorem B1723153 : Blo 678312 1723153 := bstep (se 2 (by rfl) ⟨646182, by rfl⟩ : syracuseStep 1723153 = 1292365) B1292365
theorem B3263267 : Blo 678312 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B1526705 : Blo 678312 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B1526723 : Blo 678312 1526723 := bstep (se 1 (by rfl) ⟨1145042, by rfl⟩ : syracuseStep 1526723 = 2290085) B2290085
theorem B1723427 : Blo 678312 1723427 := bstep (se 1 (by rfl) ⟨1292570, by rfl⟩ : syracuseStep 1723427 = 2585141) B2585141
theorem B1035425 : Blo 678312 1035425 := bstep (se 2 (by rfl) ⟨388284, by rfl⟩ : syracuseStep 1035425 = 776569) B776569
theorem B969889 : Blo 678312 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B1526993 : Blo 678312 1526993 := bstep (se 2 (by rfl) ⟨572622, by rfl⟩ : syracuseStep 1526993 = 1145245) B1145245
theorem B1527011 : Blo 678312 1527011 := bstep (se 1 (by rfl) ⟨1145258, by rfl⟩ : syracuseStep 1527011 = 2290517) B2290517
theorem B1723619 : Blo 678312 1723619 := bstep (se 1 (by rfl) ⟨1292714, by rfl⟩ : syracuseStep 1723619 = 2585429) B2585429
theorem B17452259 : Blo 678312 17452259 := bstep (se 1 (by rfl) ⟨13089194, by rfl⟩ : syracuseStep 17452259 = 26178389) B26178389
theorem B8735971 : Blo 678312 8735971 := bstep (se 1 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 8735971 = 13103957) B13103957
theorem B970003 : Blo 678312 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B3263921 : Blo 678312 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B1527281 : Blo 678312 1527281 := bstep (se 2 (by rfl) ⟨572730, by rfl⟩ : syracuseStep 1527281 = 1145461) B1145461
theorem B1527299 : Blo 678312 1527299 := bstep (se 1 (by rfl) ⟨1145474, by rfl⟩ : syracuseStep 1527299 = 2290949) B2290949
theorem B1035809 : Blo 678312 1035809 := bstep (se 2 (by rfl) ⟨388428, by rfl⟩ : syracuseStep 1035809 = 776857) B776857
theorem B2575907 : Blo 678312 2575907 := bstep (se 1 (by rfl) ⟨1931930, by rfl⟩ : syracuseStep 2575907 = 3863861) B3863861
theorem B2575921 : Blo 678312 2575921 := bstep (se 2 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 2575921 = 1931941) B1931941
theorem B2444941 : Blo 678312 2444941 := bstep (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) B916853
theorem B1527569 : Blo 678312 1527569 := bstep (se 2 (by rfl) ⟨572838, by rfl⟩ : syracuseStep 1527569 = 1145677) B1145677
theorem B1527587 : Blo 678312 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B2183021 : Blo 678312 2183021 := bstep (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) B818633
theorem B50417549 : Blo 678312 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B1527857 : Blo 678312 1527857 := bstep (se 2 (by rfl) ⟨572946, by rfl⟩ : syracuseStep 1527857 = 1145893) B1145893
theorem B1527875 : Blo 678312 1527875 := bstep (se 1 (by rfl) ⟨1145906, by rfl⟩ : syracuseStep 1527875 = 2291813) B2291813
theorem B1724561 : Blo 678312 1724561 := bstep (se 2 (by rfl) ⟨646710, by rfl⟩ : syracuseStep 1724561 = 1293421) B1293421
theorem B1724611 : Blo 678312 1724611 := bstep (se 1 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 1724611 = 2586917) B2586917
theorem B1528145 : Blo 678312 1528145 := bstep (se 2 (by rfl) ⟨573054, by rfl⟩ : syracuseStep 1528145 = 1146109) B1146109
theorem B1724753 : Blo 678312 1724753 := bstep (se 2 (by rfl) ⟨646782, by rfl⟩ : syracuseStep 1724753 = 1293565) B1293565
theorem B1528163 : Blo 678312 1528163 := bstep (se 1 (by rfl) ⟨1146122, by rfl⟩ : syracuseStep 1528163 = 2292245) B2292245
theorem B1036739 : Blo 678312 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B17912261 : Blo 678312 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B4149731 : Blo 678312 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B3265073 : Blo 678312 3265073 := bstep (se 2 (by rfl) ⟨1224402, by rfl⟩ : syracuseStep 3265073 = 2448805) B2448805
theorem B971347 : Blo 678312 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B1528433 : Blo 678312 1528433 := bstep (se 2 (by rfl) ⟨573162, by rfl⟩ : syracuseStep 1528433 = 1146325) B1146325
theorem B1528451 : Blo 678312 1528451 := bstep (se 1 (by rfl) ⟨1146338, by rfl⟩ : syracuseStep 1528451 = 2292677) B2292677
theorem B5526157 : Blo 678312 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B2904781 : Blo 678312 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B2183917 : Blo 678312 2183917 := bstep (se 3 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 2183917 = 818969) B818969
theorem B4641677 : Blo 678312 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1528721 : Blo 678312 1528721 := bstep (se 2 (by rfl) ⟨573270, by rfl⟩ : syracuseStep 1528721 = 1146541) B1146541
theorem B1528739 : Blo 678312 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B2577379 : Blo 678312 2577379 := bstep (se 1 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 2577379 = 3866069) B3866069
theorem B5166179 : Blo 678312 5166179 := bstep (se 1 (by rfl) ⟨3874634, by rfl⟩ : syracuseStep 5166179 = 7749269) B7749269
theorem B873635 : Blo 678312 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B1496227 : Blo 678312 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B1529009 : Blo 678312 1529009 := bstep (se 2 (by rfl) ⟨573378, by rfl⟩ : syracuseStep 1529009 = 1146757) B1146757
theorem B1529027 : Blo 678312 1529027 := bstep (se 1 (by rfl) ⟨1146770, by rfl⟩ : syracuseStep 1529027 = 2293541) B2293541
theorem B3265841 : Blo 678312 3265841 := bstep (se 2 (by rfl) ⟨1224690, by rfl⟩ : syracuseStep 3265841 = 2449381) B2449381
theorem B1725745 : Blo 678312 1725745 := bstep (se 2 (by rfl) ⟨647154, by rfl⟩ : syracuseStep 1725745 = 1294309) B1294309
theorem B1529297 : Blo 678312 1529297 := bstep (se 2 (by rfl) ⟨573486, by rfl⟩ : syracuseStep 1529297 = 1146973) B1146973
theorem B1529315 : Blo 678312 1529315 := bstep (se 1 (by rfl) ⟨1146986, by rfl⟩ : syracuseStep 1529315 = 2293973) B2293973
theorem B1103363 : Blo 678312 1103363 := bstep (se 1 (by rfl) ⟨827522, by rfl⟩ : syracuseStep 1103363 = 1655045) B1655045
theorem B1726019 : Blo 678312 1726019 := bstep (se 1 (by rfl) ⟨1294514, by rfl⟩ : syracuseStep 1726019 = 2589029) B2589029
theorem B2184803 : Blo 678312 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B1529585 : Blo 678312 1529585 := bstep (se 2 (by rfl) ⟨573594, by rfl⟩ : syracuseStep 1529585 = 1147189) B1147189
theorem B1529603 : Blo 678312 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B1726211 : Blo 678312 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B1529873 : Blo 678312 1529873 := bstep (se 2 (by rfl) ⟨573702, by rfl⟩ : syracuseStep 1529873 = 1147405) B1147405
theorem B1529891 : Blo 678312 1529891 := bstep (se 1 (by rfl) ⟨1147418, by rfl⟩ : syracuseStep 1529891 = 2294837) B2294837
theorem B1104065 : Blo 678312 1104065 := bstep (se 2 (by rfl) ⟨414024, by rfl⟩ : syracuseStep 1104065 = 828049) B828049
theorem B1530161 : Blo 678312 1530161 := bstep (se 2 (by rfl) ⟨573810, by rfl⟩ : syracuseStep 1530161 = 1147621) B1147621
theorem B1530179 : Blo 678312 1530179 := bstep (se 1 (by rfl) ⟨1147634, by rfl⟩ : syracuseStep 1530179 = 2295269) B2295269
theorem B678323 : Blo 678312 678323 := bstep (se 1 (by rfl) ⟨508742, by rfl⟩ : syracuseStep 678323 = 1017485) B1017485
theorem B678339 : Blo 678312 678339 := bstep (se 1 (by rfl) ⟨508754, by rfl⟩ : syracuseStep 678339 = 1017509) B1017509
theorem B678355 : Blo 678312 678355 := bstep (se 1 (by rfl) ⟨508766, by rfl⟩ : syracuseStep 678355 = 1017533) B1017533
theorem B678371 : Blo 678312 678371 := bstep (se 1 (by rfl) ⟨508778, by rfl⟩ : syracuseStep 678371 = 1017557) B1017557
theorem B678387 : Blo 678312 678387 := bstep (se 1 (by rfl) ⟨508790, by rfl⟩ : syracuseStep 678387 = 1017581) B1017581
theorem B678403 : Blo 678312 678403 := bstep (se 1 (by rfl) ⟨508802, by rfl⟩ : syracuseStep 678403 = 1017605) B1017605
theorem B678419 : Blo 678312 678419 := bstep (se 1 (by rfl) ⟨508814, by rfl⟩ : syracuseStep 678419 = 1017629) B1017629
theorem B678435 : Blo 678312 678435 := bstep (se 1 (by rfl) ⟨508826, by rfl⟩ : syracuseStep 678435 = 1017653) B1017653
theorem B678451 : Blo 678312 678451 := bstep (se 1 (by rfl) ⟨508838, by rfl⟩ : syracuseStep 678451 = 1017677) B1017677
theorem B678467 : Blo 678312 678467 := bstep (se 1 (by rfl) ⟨508850, by rfl⟩ : syracuseStep 678467 = 1017701) B1017701
theorem B1530449 : Blo 678312 1530449 := bstep (se 2 (by rfl) ⟨573918, by rfl⟩ : syracuseStep 1530449 = 1147837) B1147837
theorem B678483 : Blo 678312 678483 := bstep (se 1 (by rfl) ⟨508862, by rfl⟩ : syracuseStep 678483 = 1017725) B1017725
theorem B678499 : Blo 678312 678499 := bstep (se 1 (by rfl) ⟨508874, by rfl⟩ : syracuseStep 678499 = 1017749) B1017749
theorem B1530467 : Blo 678312 1530467 := bstep (se 1 (by rfl) ⟨1147850, by rfl⟩ : syracuseStep 1530467 = 2295701) B2295701
theorem B678515 : Blo 678312 678515 := bstep (se 1 (by rfl) ⟨508886, by rfl⟩ : syracuseStep 678515 = 1017773) B1017773
theorem B678531 : Blo 678312 678531 := bstep (se 1 (by rfl) ⟨508898, by rfl⟩ : syracuseStep 678531 = 1017797) B1017797
theorem B678547 : Blo 678312 678547 := bstep (se 1 (by rfl) ⟨508910, by rfl⟩ : syracuseStep 678547 = 1017821) B1017821
theorem B678563 : Blo 678312 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B678579 : Blo 678312 678579 := bstep (se 1 (by rfl) ⟨508934, by rfl⟩ : syracuseStep 678579 = 1017869) B1017869
theorem B678595 : Blo 678312 678595 := bstep (se 1 (by rfl) ⟨508946, by rfl⟩ : syracuseStep 678595 = 1017893) B1017893
theorem B678611 : Blo 678312 678611 := bstep (se 1 (by rfl) ⟨508958, by rfl⟩ : syracuseStep 678611 = 1017917) B1017917
theorem B678627 : Blo 678312 678627 := bstep (se 1 (by rfl) ⟨508970, by rfl⟩ : syracuseStep 678627 = 1017941) B1017941
theorem B678643 : Blo 678312 678643 := bstep (se 1 (by rfl) ⟨508982, by rfl⟩ : syracuseStep 678643 = 1017965) B1017965
theorem B678659 : Blo 678312 678659 := bstep (se 1 (by rfl) ⟨508994, by rfl⟩ : syracuseStep 678659 = 1017989) B1017989
theorem B678675 : Blo 678312 678675 := bstep (se 1 (by rfl) ⟨509006, by rfl⟩ : syracuseStep 678675 = 1018013) B1018013
theorem B678691 : Blo 678312 678691 := bstep (se 1 (by rfl) ⟨509018, by rfl⟩ : syracuseStep 678691 = 1018037) B1018037
theorem B678707 : Blo 678312 678707 := bstep (se 1 (by rfl) ⟨509030, by rfl⟩ : syracuseStep 678707 = 1018061) B1018061
theorem B678723 : Blo 678312 678723 := bstep (se 1 (by rfl) ⟨509042, by rfl⟩ : syracuseStep 678723 = 1018085) B1018085
theorem B678739 : Blo 678312 678739 := bstep (se 1 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 678739 = 1018109) B1018109
theorem B678755 : Blo 678312 678755 := bstep (se 1 (by rfl) ⟨509066, by rfl⟩ : syracuseStep 678755 = 1018133) B1018133
theorem B1530737 : Blo 678312 1530737 := bstep (se 2 (by rfl) ⟨574026, by rfl⟩ : syracuseStep 1530737 = 1148053) B1148053
theorem B678771 : Blo 678312 678771 := bstep (se 1 (by rfl) ⟨509078, by rfl⟩ : syracuseStep 678771 = 1018157) B1018157
theorem B678787 : Blo 678312 678787 := bstep (se 1 (by rfl) ⟨509090, by rfl⟩ : syracuseStep 678787 = 1018181) B1018181
theorem B1530755 : Blo 678312 1530755 := bstep (se 1 (by rfl) ⟨1148066, by rfl⟩ : syracuseStep 1530755 = 2296133) B2296133
theorem B678803 : Blo 678312 678803 := bstep (se 1 (by rfl) ⟨509102, by rfl⟩ : syracuseStep 678803 = 1018205) B1018205
theorem B678819 : Blo 678312 678819 := bstep (se 1 (by rfl) ⟨509114, by rfl⟩ : syracuseStep 678819 = 1018229) B1018229
theorem B678835 : Blo 678312 678835 := bstep (se 1 (by rfl) ⟨509126, by rfl⟩ : syracuseStep 678835 = 1018253) B1018253
theorem B678851 : Blo 678312 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B3267533 : Blo 678312 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B678867 : Blo 678312 678867 := bstep (se 1 (by rfl) ⟨509150, by rfl⟩ : syracuseStep 678867 = 1018301) B1018301
theorem B678883 : Blo 678312 678883 := bstep (se 1 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 678883 = 1018325) B1018325
theorem B3496945 : Blo 678312 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B678899 : Blo 678312 678899 := bstep (se 1 (by rfl) ⟨509174, by rfl⟩ : syracuseStep 678899 = 1018349) B1018349
theorem B678915 : Blo 678312 678915 := bstep (se 1 (by rfl) ⟨509186, by rfl⟩ : syracuseStep 678915 = 1018373) B1018373
theorem B678931 : Blo 678312 678931 := bstep (se 1 (by rfl) ⟨509198, by rfl⟩ : syracuseStep 678931 = 1018397) B1018397
theorem B678947 : Blo 678312 678947 := bstep (se 1 (by rfl) ⟨509210, by rfl⟩ : syracuseStep 678947 = 1018421) B1018421
theorem B678963 : Blo 678312 678963 := bstep (se 1 (by rfl) ⟨509222, by rfl⟩ : syracuseStep 678963 = 1018445) B1018445
theorem B678979 : Blo 678312 678979 := bstep (se 1 (by rfl) ⟨509234, by rfl⟩ : syracuseStep 678979 = 1018469) B1018469
theorem B678995 : Blo 678312 678995 := bstep (se 1 (by rfl) ⟨509246, by rfl⟩ : syracuseStep 678995 = 1018493) B1018493
theorem B679011 : Blo 678312 679011 := bstep (se 1 (by rfl) ⟨509258, by rfl⟩ : syracuseStep 679011 = 1018517) B1018517
theorem B679027 : Blo 678312 679027 := bstep (se 1 (by rfl) ⟨509270, by rfl⟩ : syracuseStep 679027 = 1018541) B1018541
theorem B679043 : Blo 678312 679043 := bstep (se 1 (by rfl) ⟨509282, by rfl⟩ : syracuseStep 679043 = 1018565) B1018565
theorem B2579597 : Blo 678312 2579597 := bstep (se 3 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 2579597 = 967349) B967349
theorem B1531025 : Blo 678312 1531025 := bstep (se 2 (by rfl) ⟨574134, by rfl⟩ : syracuseStep 1531025 = 1148269) B1148269
theorem B679059 : Blo 678312 679059 := bstep (se 1 (by rfl) ⟨509294, by rfl⟩ : syracuseStep 679059 = 1018589) B1018589
theorem B679075 : Blo 678312 679075 := bstep (se 1 (by rfl) ⟨509306, by rfl⟩ : syracuseStep 679075 = 1018613) B1018613
theorem B1531043 : Blo 678312 1531043 := bstep (se 1 (by rfl) ⟨1148282, by rfl⟩ : syracuseStep 1531043 = 2296565) B2296565
theorem B679091 : Blo 678312 679091 := bstep (se 1 (by rfl) ⟨509318, by rfl⟩ : syracuseStep 679091 = 1018637) B1018637
theorem B679107 : Blo 678312 679107 := bstep (se 1 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 679107 = 1018661) B1018661
theorem B679123 : Blo 678312 679123 := bstep (se 1 (by rfl) ⟨509342, by rfl⟩ : syracuseStep 679123 = 1018685) B1018685
theorem B679139 : Blo 678312 679139 := bstep (se 1 (by rfl) ⟨509354, by rfl⟩ : syracuseStep 679139 = 1018709) B1018709
theorem B679155 : Blo 678312 679155 := bstep (se 1 (by rfl) ⟨509366, by rfl⟩ : syracuseStep 679155 = 1018733) B1018733
theorem B679171 : Blo 678312 679171 := bstep (se 1 (by rfl) ⟨509378, by rfl⟩ : syracuseStep 679171 = 1018757) B1018757
theorem B679187 : Blo 678312 679187 := bstep (se 1 (by rfl) ⟨509390, by rfl⟩ : syracuseStep 679187 = 1018781) B1018781
theorem B679203 : Blo 678312 679203 := bstep (se 1 (by rfl) ⟨509402, by rfl⟩ : syracuseStep 679203 = 1018805) B1018805
theorem B679219 : Blo 678312 679219 := bstep (se 1 (by rfl) ⟨509414, by rfl⟩ : syracuseStep 679219 = 1018829) B1018829
theorem B679235 : Blo 678312 679235 := bstep (se 1 (by rfl) ⟨509426, by rfl⟩ : syracuseStep 679235 = 1018853) B1018853
theorem B679251 : Blo 678312 679251 := bstep (se 1 (by rfl) ⟨509438, by rfl⟩ : syracuseStep 679251 = 1018877) B1018877
theorem B679267 : Blo 678312 679267 := bstep (se 1 (by rfl) ⟨509450, by rfl⟩ : syracuseStep 679267 = 1018901) B1018901
theorem B679283 : Blo 678312 679283 := bstep (se 1 (by rfl) ⟨509462, by rfl⟩ : syracuseStep 679283 = 1018925) B1018925
theorem B679299 : Blo 678312 679299 := bstep (se 1 (by rfl) ⟨509474, by rfl⟩ : syracuseStep 679299 = 1018949) B1018949
theorem B679315 : Blo 678312 679315 := bstep (se 1 (by rfl) ⟨509486, by rfl⟩ : syracuseStep 679315 = 1018973) B1018973
theorem B679331 : Blo 678312 679331 := bstep (se 1 (by rfl) ⟨509498, by rfl⟩ : syracuseStep 679331 = 1018997) B1018997
theorem B1531313 : Blo 678312 1531313 := bstep (se 2 (by rfl) ⟨574242, by rfl⟩ : syracuseStep 1531313 = 1148485) B1148485
theorem B679347 : Blo 678312 679347 := bstep (se 1 (by rfl) ⟨509510, by rfl⟩ : syracuseStep 679347 = 1019021) B1019021
theorem B679363 : Blo 678312 679363 := bstep (se 1 (by rfl) ⟨509522, by rfl⟩ : syracuseStep 679363 = 1019045) B1019045
theorem B1531331 : Blo 678312 1531331 := bstep (se 1 (by rfl) ⟨1148498, by rfl⟩ : syracuseStep 1531331 = 2296997) B2296997
theorem B679379 : Blo 678312 679379 := bstep (se 1 (by rfl) ⟨509534, by rfl⟩ : syracuseStep 679379 = 1019069) B1019069
theorem B679395 : Blo 678312 679395 := bstep (se 1 (by rfl) ⟨509546, by rfl⟩ : syracuseStep 679395 = 1019093) B1019093
theorem B679411 : Blo 678312 679411 := bstep (se 1 (by rfl) ⟨509558, by rfl⟩ : syracuseStep 679411 = 1019117) B1019117
theorem B679427 : Blo 678312 679427 := bstep (se 1 (by rfl) ⟨509570, by rfl⟩ : syracuseStep 679427 = 1019141) B1019141
theorem B679443 : Blo 678312 679443 := bstep (se 1 (by rfl) ⟨509582, by rfl⟩ : syracuseStep 679443 = 1019165) B1019165
theorem B679459 : Blo 678312 679459 := bstep (se 1 (by rfl) ⟨509594, by rfl⟩ : syracuseStep 679459 = 1019189) B1019189
theorem B679475 : Blo 678312 679475 := bstep (se 1 (by rfl) ⟨509606, by rfl⟩ : syracuseStep 679475 = 1019213) B1019213
theorem B14114357 : Blo 678312 14114357 := bstep (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) B1323221
theorem B679491 : Blo 678312 679491 := bstep (se 1 (by rfl) ⟨509618, by rfl⟩ : syracuseStep 679491 = 1019237) B1019237
theorem B679507 : Blo 678312 679507 := bstep (se 1 (by rfl) ⟨509630, by rfl⟩ : syracuseStep 679507 = 1019261) B1019261
theorem B679523 : Blo 678312 679523 := bstep (se 1 (by rfl) ⟨509642, by rfl⟩ : syracuseStep 679523 = 1019285) B1019285
theorem B679539 : Blo 678312 679539 := bstep (se 1 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 679539 = 1019309) B1019309
theorem B679555 : Blo 678312 679555 := bstep (se 1 (by rfl) ⟨509666, by rfl⟩ : syracuseStep 679555 = 1019333) B1019333
theorem B679571 : Blo 678312 679571 := bstep (se 1 (by rfl) ⟨509678, by rfl⟩ : syracuseStep 679571 = 1019357) B1019357
theorem B679587 : Blo 678312 679587 := bstep (se 1 (by rfl) ⟨509690, by rfl⟩ : syracuseStep 679587 = 1019381) B1019381
theorem B679603 : Blo 678312 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B679619 : Blo 678312 679619 := bstep (se 1 (by rfl) ⟨509714, by rfl⟩ : syracuseStep 679619 = 1019429) B1019429
theorem B1531601 : Blo 678312 1531601 := bstep (se 2 (by rfl) ⟨574350, by rfl⟩ : syracuseStep 1531601 = 1148701) B1148701
theorem B679635 : Blo 678312 679635 := bstep (se 1 (by rfl) ⟨509726, by rfl⟩ : syracuseStep 679635 = 1019453) B1019453
theorem B679651 : Blo 678312 679651 := bstep (se 1 (by rfl) ⟨509738, by rfl⟩ : syracuseStep 679651 = 1019477) B1019477
theorem B1531619 : Blo 678312 1531619 := bstep (se 1 (by rfl) ⟨1148714, by rfl⟩ : syracuseStep 1531619 = 2297429) B2297429
theorem B679667 : Blo 678312 679667 := bstep (se 1 (by rfl) ⟨509750, by rfl⟩ : syracuseStep 679667 = 1019501) B1019501
theorem B679683 : Blo 678312 679683 := bstep (se 1 (by rfl) ⟨509762, by rfl⟩ : syracuseStep 679683 = 1019525) B1019525
theorem B679699 : Blo 678312 679699 := bstep (se 1 (by rfl) ⟨509774, by rfl⟩ : syracuseStep 679699 = 1019549) B1019549
theorem B679715 : Blo 678312 679715 := bstep (se 1 (by rfl) ⟨509786, by rfl⟩ : syracuseStep 679715 = 1019573) B1019573
theorem B679731 : Blo 678312 679731 := bstep (se 1 (by rfl) ⟨509798, by rfl⟩ : syracuseStep 679731 = 1019597) B1019597
theorem B679747 : Blo 678312 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B679763 : Blo 678312 679763 := bstep (se 1 (by rfl) ⟨509822, by rfl⟩ : syracuseStep 679763 = 1019645) B1019645
theorem B679779 : Blo 678312 679779 := bstep (se 1 (by rfl) ⟨509834, by rfl⟩ : syracuseStep 679779 = 1019669) B1019669
theorem B679795 : Blo 678312 679795 := bstep (se 1 (by rfl) ⟨509846, by rfl⟩ : syracuseStep 679795 = 1019693) B1019693
theorem B679811 : Blo 678312 679811 := bstep (se 1 (by rfl) ⟨509858, by rfl⟩ : syracuseStep 679811 = 1019717) B1019717
theorem B679827 : Blo 678312 679827 := bstep (se 1 (by rfl) ⟨509870, by rfl⟩ : syracuseStep 679827 = 1019741) B1019741
theorem B1630115 : Blo 678312 1630115 := bstep (se 1 (by rfl) ⟨1222586, by rfl⟩ : syracuseStep 1630115 = 2445173) B2445173
theorem B679843 : Blo 678312 679843 := bstep (se 1 (by rfl) ⟨509882, by rfl⟩ : syracuseStep 679843 = 1019765) B1019765
theorem B679859 : Blo 678312 679859 := bstep (se 1 (by rfl) ⟨509894, by rfl⟩ : syracuseStep 679859 = 1019789) B1019789
theorem B679875 : Blo 678312 679875 := bstep (se 1 (by rfl) ⟨509906, by rfl⟩ : syracuseStep 679875 = 1019813) B1019813
theorem B679891 : Blo 678312 679891 := bstep (se 1 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 679891 = 1019837) B1019837
theorem B679907 : Blo 678312 679907 := bstep (se 1 (by rfl) ⟨509930, by rfl⟩ : syracuseStep 679907 = 1019861) B1019861
theorem B1531889 : Blo 678312 1531889 := bstep (se 2 (by rfl) ⟨574458, by rfl⟩ : syracuseStep 1531889 = 1148917) B1148917
theorem B679923 : Blo 678312 679923 := bstep (se 1 (by rfl) ⟨509942, by rfl⟩ : syracuseStep 679923 = 1019885) B1019885
theorem B679939 : Blo 678312 679939 := bstep (se 1 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 679939 = 1019909) B1019909
theorem B1531907 : Blo 678312 1531907 := bstep (se 1 (by rfl) ⟨1148930, by rfl⟩ : syracuseStep 1531907 = 2297861) B2297861
theorem B679955 : Blo 678312 679955 := bstep (se 1 (by rfl) ⟨509966, by rfl⟩ : syracuseStep 679955 = 1019933) B1019933
theorem B679971 : Blo 678312 679971 := bstep (se 1 (by rfl) ⟨509978, by rfl⟩ : syracuseStep 679971 = 1019957) B1019957
theorem B679987 : Blo 678312 679987 := bstep (se 1 (by rfl) ⟨509990, by rfl⟩ : syracuseStep 679987 = 1019981) B1019981
theorem B680003 : Blo 678312 680003 := bstep (se 1 (by rfl) ⟨510002, by rfl⟩ : syracuseStep 680003 = 1020005) B1020005
theorem B680019 : Blo 678312 680019 := bstep (se 1 (by rfl) ⟨510014, by rfl⟩ : syracuseStep 680019 = 1020029) B1020029
theorem B680035 : Blo 678312 680035 := bstep (se 1 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 680035 = 1020053) B1020053
theorem B680051 : Blo 678312 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B680067 : Blo 678312 680067 := bstep (se 1 (by rfl) ⟨510050, by rfl⟩ : syracuseStep 680067 = 1020101) B1020101
theorem B1106065 : Blo 678312 1106065 := bstep (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) B829549
theorem B680083 : Blo 678312 680083 := bstep (se 1 (by rfl) ⟨510062, by rfl⟩ : syracuseStep 680083 = 1020125) B1020125
theorem B680099 : Blo 678312 680099 := bstep (se 1 (by rfl) ⟨510074, by rfl⟩ : syracuseStep 680099 = 1020149) B1020149
theorem B680115 : Blo 678312 680115 := bstep (se 1 (by rfl) ⟨510086, by rfl⟩ : syracuseStep 680115 = 1020173) B1020173
theorem B680131 : Blo 678312 680131 := bstep (se 1 (by rfl) ⟨510098, by rfl⟩ : syracuseStep 680131 = 1020197) B1020197
theorem B4350149 : Blo 678312 4350149 := bstep (se 4 (by rfl) ⟨407826, by rfl⟩ : syracuseStep 4350149 = 815653) B815653
theorem B680147 : Blo 678312 680147 := bstep (se 1 (by rfl) ⟨510110, by rfl⟩ : syracuseStep 680147 = 1020221) B1020221
theorem B680163 : Blo 678312 680163 := bstep (se 1 (by rfl) ⟨510122, by rfl⟩ : syracuseStep 680163 = 1020245) B1020245
theorem B680179 : Blo 678312 680179 := bstep (se 1 (by rfl) ⟨510134, by rfl⟩ : syracuseStep 680179 = 1020269) B1020269
theorem B680195 : Blo 678312 680195 := bstep (se 1 (by rfl) ⟨510146, by rfl⟩ : syracuseStep 680195 = 1020293) B1020293
theorem B1532177 : Blo 678312 1532177 := bstep (se 2 (by rfl) ⟨574566, by rfl⟩ : syracuseStep 1532177 = 1149133) B1149133
theorem B680211 : Blo 678312 680211 := bstep (se 1 (by rfl) ⟨510158, by rfl⟩ : syracuseStep 680211 = 1020317) B1020317
theorem B680227 : Blo 678312 680227 := bstep (se 1 (by rfl) ⟨510170, by rfl⟩ : syracuseStep 680227 = 1020341) B1020341
theorem B1532195 : Blo 678312 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B680243 : Blo 678312 680243 := bstep (se 1 (by rfl) ⟨510182, by rfl⟩ : syracuseStep 680243 = 1020365) B1020365
theorem B680259 : Blo 678312 680259 := bstep (se 1 (by rfl) ⟨510194, by rfl⟩ : syracuseStep 680259 = 1020389) B1020389
theorem B680275 : Blo 678312 680275 := bstep (se 1 (by rfl) ⟨510206, by rfl⟩ : syracuseStep 680275 = 1020413) B1020413
theorem B680291 : Blo 678312 680291 := bstep (se 1 (by rfl) ⟨510218, by rfl⟩ : syracuseStep 680291 = 1020437) B1020437
theorem B680307 : Blo 678312 680307 := bstep (se 1 (by rfl) ⟨510230, by rfl⟩ : syracuseStep 680307 = 1020461) B1020461
theorem B680323 : Blo 678312 680323 := bstep (se 1 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 680323 = 1020485) B1020485
theorem B680339 : Blo 678312 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B680355 : Blo 678312 680355 := bstep (se 1 (by rfl) ⟨510266, by rfl⟩ : syracuseStep 680355 = 1020533) B1020533
theorem B680371 : Blo 678312 680371 := bstep (se 1 (by rfl) ⟨510278, by rfl⟩ : syracuseStep 680371 = 1020557) B1020557
theorem B680387 : Blo 678312 680387 := bstep (se 1 (by rfl) ⟨510290, by rfl⟩ : syracuseStep 680387 = 1020581) B1020581
theorem B680403 : Blo 678312 680403 := bstep (se 1 (by rfl) ⟨510302, by rfl⟩ : syracuseStep 680403 = 1020605) B1020605
theorem B680419 : Blo 678312 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B3498481 : Blo 678312 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B680435 : Blo 678312 680435 := bstep (se 1 (by rfl) ⟨510326, by rfl⟩ : syracuseStep 680435 = 1020653) B1020653
theorem B680451 : Blo 678312 680451 := bstep (se 1 (by rfl) ⟨510338, by rfl⟩ : syracuseStep 680451 = 1020677) B1020677
theorem B680467 : Blo 678312 680467 := bstep (se 1 (by rfl) ⟨510350, by rfl⟩ : syracuseStep 680467 = 1020701) B1020701
theorem B1860131 : Blo 678312 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B680483 : Blo 678312 680483 := bstep (se 1 (by rfl) ⟨510362, by rfl⟩ : syracuseStep 680483 = 1020725) B1020725
theorem B1532465 : Blo 678312 1532465 := bstep (se 2 (by rfl) ⟨574674, by rfl⟩ : syracuseStep 1532465 = 1149349) B1149349
theorem B680499 : Blo 678312 680499 := bstep (se 1 (by rfl) ⟨510374, by rfl⟩ : syracuseStep 680499 = 1020749) B1020749
theorem B680515 : Blo 678312 680515 := bstep (se 1 (by rfl) ⟨510386, by rfl⟩ : syracuseStep 680515 = 1020773) B1020773
theorem B1532483 : Blo 678312 1532483 := bstep (se 1 (by rfl) ⟨1149362, by rfl⟩ : syracuseStep 1532483 = 2298725) B2298725
theorem B680531 : Blo 678312 680531 := bstep (se 1 (by rfl) ⟨510398, by rfl⟩ : syracuseStep 680531 = 1020797) B1020797
theorem B680547 : Blo 678312 680547 := bstep (se 1 (by rfl) ⟨510410, by rfl⟩ : syracuseStep 680547 = 1020821) B1020821
theorem B680563 : Blo 678312 680563 := bstep (se 1 (by rfl) ⟨510422, by rfl⟩ : syracuseStep 680563 = 1020845) B1020845
theorem B680579 : Blo 678312 680579 := bstep (se 1 (by rfl) ⟨510434, by rfl⟩ : syracuseStep 680579 = 1020869) B1020869
theorem B680595 : Blo 678312 680595 := bstep (se 1 (by rfl) ⟨510446, by rfl⟩ : syracuseStep 680595 = 1020893) B1020893
theorem B680611 : Blo 678312 680611 := bstep (se 1 (by rfl) ⟨510458, by rfl⟩ : syracuseStep 680611 = 1020917) B1020917
theorem B680627 : Blo 678312 680627 := bstep (se 1 (by rfl) ⟨510470, by rfl⟩ : syracuseStep 680627 = 1020941) B1020941
theorem B680643 : Blo 678312 680643 := bstep (se 1 (by rfl) ⟨510482, by rfl⟩ : syracuseStep 680643 = 1020965) B1020965
theorem B680659 : Blo 678312 680659 := bstep (se 1 (by rfl) ⟨510494, by rfl⟩ : syracuseStep 680659 = 1020989) B1020989
theorem B680675 : Blo 678312 680675 := bstep (se 1 (by rfl) ⟨510506, by rfl⟩ : syracuseStep 680675 = 1021013) B1021013
theorem B680691 : Blo 678312 680691 := bstep (se 1 (by rfl) ⟨510518, by rfl⟩ : syracuseStep 680691 = 1021037) B1021037
theorem B680707 : Blo 678312 680707 := bstep (se 1 (by rfl) ⟨510530, by rfl⟩ : syracuseStep 680707 = 1021061) B1021061
theorem B2450189 : Blo 678312 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B680723 : Blo 678312 680723 := bstep (se 1 (by rfl) ⟨510542, by rfl⟩ : syracuseStep 680723 = 1021085) B1021085
theorem B680739 : Blo 678312 680739 := bstep (se 1 (by rfl) ⟨510554, by rfl⟩ : syracuseStep 680739 = 1021109) B1021109
theorem B680755 : Blo 678312 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B680771 : Blo 678312 680771 := bstep (se 1 (by rfl) ⟨510578, by rfl⟩ : syracuseStep 680771 = 1021157) B1021157
theorem B1532753 : Blo 678312 1532753 := bstep (se 2 (by rfl) ⟨574782, by rfl⟩ : syracuseStep 1532753 = 1149565) B1149565
theorem B680787 : Blo 678312 680787 := bstep (se 1 (by rfl) ⟨510590, by rfl⟩ : syracuseStep 680787 = 1021181) B1021181
theorem B1631075 : Blo 678312 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B680803 : Blo 678312 680803 := bstep (se 1 (by rfl) ⟨510602, by rfl⟩ : syracuseStep 680803 = 1021205) B1021205
theorem B1532771 : Blo 678312 1532771 := bstep (se 1 (by rfl) ⟨1149578, by rfl⟩ : syracuseStep 1532771 = 2299157) B2299157
theorem B680819 : Blo 678312 680819 := bstep (se 1 (by rfl) ⟨510614, by rfl⟩ : syracuseStep 680819 = 1021229) B1021229
theorem B680835 : Blo 678312 680835 := bstep (se 1 (by rfl) ⟨510626, by rfl⟩ : syracuseStep 680835 = 1021253) B1021253
theorem B680851 : Blo 678312 680851 := bstep (se 1 (by rfl) ⟨510638, by rfl⟩ : syracuseStep 680851 = 1021277) B1021277
theorem B680867 : Blo 678312 680867 := bstep (se 1 (by rfl) ⟨510650, by rfl⟩ : syracuseStep 680867 = 1021301) B1021301
theorem B1631153 : Blo 678312 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B2909105 : Blo 678312 2909105 := bstep (se 2 (by rfl) ⟨1090914, by rfl⟩ : syracuseStep 2909105 = 2181829) B2181829
theorem B680883 : Blo 678312 680883 := bstep (se 1 (by rfl) ⟨510662, by rfl⟩ : syracuseStep 680883 = 1021325) B1021325
theorem B680899 : Blo 678312 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B680915 : Blo 678312 680915 := bstep (se 1 (by rfl) ⟨510686, by rfl⟩ : syracuseStep 680915 = 1021373) B1021373
theorem B680931 : Blo 678312 680931 := bstep (se 1 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 680931 = 1021397) B1021397
theorem B2909155 : Blo 678312 2909155 := bstep (se 1 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 2909155 = 4363733) B4363733
theorem B680947 : Blo 678312 680947 := bstep (se 1 (by rfl) ⟨510710, by rfl⟩ : syracuseStep 680947 = 1021421) B1021421
theorem B680963 : Blo 678312 680963 := bstep (se 1 (by rfl) ⟨510722, by rfl⟩ : syracuseStep 680963 = 1021445) B1021445
theorem B680979 : Blo 678312 680979 := bstep (se 1 (by rfl) ⟨510734, by rfl⟩ : syracuseStep 680979 = 1021469) B1021469
theorem B680995 : Blo 678312 680995 := bstep (se 1 (by rfl) ⟨510746, by rfl⟩ : syracuseStep 680995 = 1021493) B1021493
theorem B681011 : Blo 678312 681011 := bstep (se 1 (by rfl) ⟨510758, by rfl⟩ : syracuseStep 681011 = 1021517) B1021517
theorem B681027 : Blo 678312 681027 := bstep (se 1 (by rfl) ⟨510770, by rfl⟩ : syracuseStep 681027 = 1021541) B1021541
theorem B681043 : Blo 678312 681043 := bstep (se 1 (by rfl) ⟨510782, by rfl⟩ : syracuseStep 681043 = 1021565) B1021565
theorem B681059 : Blo 678312 681059 := bstep (se 1 (by rfl) ⟨510794, by rfl⟩ : syracuseStep 681059 = 1021589) B1021589
theorem B1533041 : Blo 678312 1533041 := bstep (se 2 (by rfl) ⟨574890, by rfl⟩ : syracuseStep 1533041 = 1149781) B1149781
theorem B681075 : Blo 678312 681075 := bstep (se 1 (by rfl) ⟨510806, by rfl⟩ : syracuseStep 681075 = 1021613) B1021613
theorem B681091 : Blo 678312 681091 := bstep (se 1 (by rfl) ⟨510818, by rfl⟩ : syracuseStep 681091 = 1021637) B1021637
theorem B1533059 : Blo 678312 1533059 := bstep (se 1 (by rfl) ⟨1149794, by rfl⟩ : syracuseStep 1533059 = 2299589) B2299589
theorem B681107 : Blo 678312 681107 := bstep (se 1 (by rfl) ⟨510830, by rfl⟩ : syracuseStep 681107 = 1021661) B1021661
theorem B681123 : Blo 678312 681123 := bstep (se 1 (by rfl) ⟨510842, by rfl⟩ : syracuseStep 681123 = 1021685) B1021685
theorem B681139 : Blo 678312 681139 := bstep (se 1 (by rfl) ⟨510854, by rfl⟩ : syracuseStep 681139 = 1021709) B1021709
theorem B681155 : Blo 678312 681155 := bstep (se 1 (by rfl) ⟨510866, by rfl⟩ : syracuseStep 681155 = 1021733) B1021733
theorem B681171 : Blo 678312 681171 := bstep (se 1 (by rfl) ⟨510878, by rfl⟩ : syracuseStep 681171 = 1021757) B1021757
theorem B681187 : Blo 678312 681187 := bstep (se 1 (by rfl) ⟨510890, by rfl⟩ : syracuseStep 681187 = 1021781) B1021781
theorem B681203 : Blo 678312 681203 := bstep (se 1 (by rfl) ⟨510902, by rfl⟩ : syracuseStep 681203 = 1021805) B1021805
theorem B681219 : Blo 678312 681219 := bstep (se 1 (by rfl) ⟨510914, by rfl⟩ : syracuseStep 681219 = 1021829) B1021829
theorem B681235 : Blo 678312 681235 := bstep (se 1 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 681235 = 1021853) B1021853
theorem B681251 : Blo 678312 681251 := bstep (se 1 (by rfl) ⟨510938, by rfl⟩ : syracuseStep 681251 = 1021877) B1021877
theorem B681267 : Blo 678312 681267 := bstep (se 1 (by rfl) ⟨510950, by rfl⟩ : syracuseStep 681267 = 1021901) B1021901
theorem B681283 : Blo 678312 681283 := bstep (se 1 (by rfl) ⟨510962, by rfl⟩ : syracuseStep 681283 = 1021925) B1021925
theorem B681299 : Blo 678312 681299 := bstep (se 1 (by rfl) ⟨510974, by rfl⟩ : syracuseStep 681299 = 1021949) B1021949
theorem B681315 : Blo 678312 681315 := bstep (se 1 (by rfl) ⟨510986, by rfl⟩ : syracuseStep 681315 = 1021973) B1021973
theorem B681331 : Blo 678312 681331 := bstep (se 1 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 681331 = 1021997) B1021997
theorem B681347 : Blo 678312 681347 := bstep (se 1 (by rfl) ⟨511010, by rfl⟩ : syracuseStep 681347 = 1022021) B1022021
theorem B1533329 : Blo 678312 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B681363 : Blo 678312 681363 := bstep (se 1 (by rfl) ⟨511022, by rfl⟩ : syracuseStep 681363 = 1022045) B1022045
theorem B681379 : Blo 678312 681379 := bstep (se 1 (by rfl) ⟨511034, by rfl⟩ : syracuseStep 681379 = 1022069) B1022069
theorem B1533347 : Blo 678312 1533347 := bstep (se 1 (by rfl) ⟨1150010, by rfl⟩ : syracuseStep 1533347 = 2300021) B2300021
theorem B681395 : Blo 678312 681395 := bstep (se 1 (by rfl) ⟨511046, by rfl⟩ : syracuseStep 681395 = 1022093) B1022093
theorem B681411 : Blo 678312 681411 := bstep (se 1 (by rfl) ⟨511058, by rfl⟩ : syracuseStep 681411 = 1022117) B1022117
theorem B681427 : Blo 678312 681427 := bstep (se 1 (by rfl) ⟨511070, by rfl⟩ : syracuseStep 681427 = 1022141) B1022141
theorem B681443 : Blo 678312 681443 := bstep (se 1 (by rfl) ⟨511082, by rfl⟩ : syracuseStep 681443 = 1022165) B1022165
theorem B681459 : Blo 678312 681459 := bstep (se 1 (by rfl) ⟨511094, by rfl⟩ : syracuseStep 681459 = 1022189) B1022189
theorem B681475 : Blo 678312 681475 := bstep (se 1 (by rfl) ⟨511106, by rfl⟩ : syracuseStep 681475 = 1022213) B1022213
theorem B681491 : Blo 678312 681491 := bstep (se 1 (by rfl) ⟨511118, by rfl⟩ : syracuseStep 681491 = 1022237) B1022237
theorem B681507 : Blo 678312 681507 := bstep (se 1 (by rfl) ⟨511130, by rfl⟩ : syracuseStep 681507 = 1022261) B1022261
theorem B681523 : Blo 678312 681523 := bstep (se 1 (by rfl) ⟨511142, by rfl⟩ : syracuseStep 681523 = 1022285) B1022285
theorem B681539 : Blo 678312 681539 := bstep (se 1 (by rfl) ⟨511154, by rfl⟩ : syracuseStep 681539 = 1022309) B1022309
theorem B681555 : Blo 678312 681555 := bstep (se 1 (by rfl) ⟨511166, by rfl⟩ : syracuseStep 681555 = 1022333) B1022333
theorem B681571 : Blo 678312 681571 := bstep (se 1 (by rfl) ⟨511178, by rfl⟩ : syracuseStep 681571 = 1022357) B1022357
theorem B681587 : Blo 678312 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B681603 : Blo 678312 681603 := bstep (se 1 (by rfl) ⟨511202, by rfl⟩ : syracuseStep 681603 = 1022405) B1022405
theorem B681619 : Blo 678312 681619 := bstep (se 1 (by rfl) ⟨511214, by rfl⟩ : syracuseStep 681619 = 1022429) B1022429
theorem B681635 : Blo 678312 681635 := bstep (se 1 (by rfl) ⟨511226, by rfl⟩ : syracuseStep 681635 = 1022453) B1022453
theorem B1533617 : Blo 678312 1533617 := bstep (se 2 (by rfl) ⟨575106, by rfl⟩ : syracuseStep 1533617 = 1150213) B1150213
theorem B681651 : Blo 678312 681651 := bstep (se 1 (by rfl) ⟨511238, by rfl⟩ : syracuseStep 681651 = 1022477) B1022477
theorem B1533635 : Blo 678312 1533635 := bstep (se 1 (by rfl) ⟨1150226, by rfl⟩ : syracuseStep 1533635 = 2300453) B2300453
theorem B681667 : Blo 678312 681667 := bstep (se 1 (by rfl) ⟨511250, by rfl⟩ : syracuseStep 681667 = 1022501) B1022501
theorem B681683 : Blo 678312 681683 := bstep (se 1 (by rfl) ⟨511262, by rfl⟩ : syracuseStep 681683 = 1022525) B1022525
theorem B681699 : Blo 678312 681699 := bstep (se 1 (by rfl) ⟨511274, by rfl⟩ : syracuseStep 681699 = 1022549) B1022549
theorem B681715 : Blo 678312 681715 := bstep (se 1 (by rfl) ⟨511286, by rfl⟩ : syracuseStep 681715 = 1022573) B1022573
theorem B681731 : Blo 678312 681731 := bstep (se 1 (by rfl) ⟨511298, by rfl⟩ : syracuseStep 681731 = 1022597) B1022597
theorem B681747 : Blo 678312 681747 := bstep (se 1 (by rfl) ⟨511310, by rfl⟩ : syracuseStep 681747 = 1022621) B1022621
theorem B681763 : Blo 678312 681763 := bstep (se 1 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 681763 = 1022645) B1022645
theorem B4187953 : Blo 678312 4187953 := bstep (se 2 (by rfl) ⟨1570482, by rfl⟩ : syracuseStep 4187953 = 3140965) B3140965
theorem B681779 : Blo 678312 681779 := bstep (se 1 (by rfl) ⟨511334, by rfl⟩ : syracuseStep 681779 = 1022669) B1022669
theorem B681795 : Blo 678312 681795 := bstep (se 1 (by rfl) ⟨511346, by rfl⟩ : syracuseStep 681795 = 1022693) B1022693
theorem B681811 : Blo 678312 681811 := bstep (se 1 (by rfl) ⟨511358, by rfl⟩ : syracuseStep 681811 = 1022717) B1022717
theorem B681827 : Blo 678312 681827 := bstep (se 1 (by rfl) ⟨511370, by rfl⟩ : syracuseStep 681827 = 1022741) B1022741
theorem B681843 : Blo 678312 681843 := bstep (se 1 (by rfl) ⟨511382, by rfl⟩ : syracuseStep 681843 = 1022765) B1022765
theorem B681859 : Blo 678312 681859 := bstep (se 1 (by rfl) ⟨511394, by rfl⟩ : syracuseStep 681859 = 1022789) B1022789
theorem B681875 : Blo 678312 681875 := bstep (se 1 (by rfl) ⟨511406, by rfl⟩ : syracuseStep 681875 = 1022813) B1022813
theorem B681891 : Blo 678312 681891 := bstep (se 1 (by rfl) ⟨511418, by rfl⟩ : syracuseStep 681891 = 1022837) B1022837
theorem B681907 : Blo 678312 681907 := bstep (se 1 (by rfl) ⟨511430, by rfl⟩ : syracuseStep 681907 = 1022861) B1022861
theorem B681923 : Blo 678312 681923 := bstep (se 1 (by rfl) ⟨511442, by rfl⟩ : syracuseStep 681923 = 1022885) B1022885
theorem B1533905 : Blo 678312 1533905 := bstep (se 2 (by rfl) ⟨575214, by rfl⟩ : syracuseStep 1533905 = 1150429) B1150429
theorem B681939 : Blo 678312 681939 := bstep (se 1 (by rfl) ⟨511454, by rfl⟩ : syracuseStep 681939 = 1022909) B1022909
theorem B1533923 : Blo 678312 1533923 := bstep (se 1 (by rfl) ⟨1150442, by rfl⟩ : syracuseStep 1533923 = 2300885) B2300885
theorem B681955 : Blo 678312 681955 := bstep (se 1 (by rfl) ⟨511466, by rfl⟩ : syracuseStep 681955 = 1022933) B1022933
theorem B2582513 : Blo 678312 2582513 := bstep (se 2 (by rfl) ⟨968442, by rfl⟩ : syracuseStep 2582513 = 1936885) B1936885
theorem B681971 : Blo 678312 681971 := bstep (se 1 (by rfl) ⟨511478, by rfl⟩ : syracuseStep 681971 = 1022957) B1022957
theorem B681987 : Blo 678312 681987 := bstep (se 1 (by rfl) ⟨511490, by rfl⟩ : syracuseStep 681987 = 1022981) B1022981
theorem B682003 : Blo 678312 682003 := bstep (se 1 (by rfl) ⟨511502, by rfl⟩ : syracuseStep 682003 = 1023005) B1023005
theorem B682019 : Blo 678312 682019 := bstep (se 1 (by rfl) ⟨511514, by rfl⟩ : syracuseStep 682019 = 1023029) B1023029
theorem B3237937 : Blo 678312 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B682035 : Blo 678312 682035 := bstep (se 1 (by rfl) ⟨511526, by rfl⟩ : syracuseStep 682035 = 1023053) B1023053
theorem B682051 : Blo 678312 682051 := bstep (se 1 (by rfl) ⟨511538, by rfl⟩ : syracuseStep 682051 = 1023077) B1023077
theorem B682067 : Blo 678312 682067 := bstep (se 1 (by rfl) ⟨511550, by rfl⟩ : syracuseStep 682067 = 1023101) B1023101
theorem B682083 : Blo 678312 682083 := bstep (se 1 (by rfl) ⟨511562, by rfl⟩ : syracuseStep 682083 = 1023125) B1023125
theorem B682099 : Blo 678312 682099 := bstep (se 1 (by rfl) ⟨511574, by rfl⟩ : syracuseStep 682099 = 1023149) B1023149
theorem B682115 : Blo 678312 682115 := bstep (se 1 (by rfl) ⟨511586, by rfl⟩ : syracuseStep 682115 = 1023173) B1023173
theorem B682131 : Blo 678312 682131 := bstep (se 1 (by rfl) ⟨511598, by rfl⟩ : syracuseStep 682131 = 1023197) B1023197
theorem B682147 : Blo 678312 682147 := bstep (se 1 (by rfl) ⟨511610, by rfl⟩ : syracuseStep 682147 = 1023221) B1023221
theorem B682163 : Blo 678312 682163 := bstep (se 1 (by rfl) ⟨511622, by rfl⟩ : syracuseStep 682163 = 1023245) B1023245
theorem B682179 : Blo 678312 682179 := bstep (se 1 (by rfl) ⟨511634, by rfl⟩ : syracuseStep 682179 = 1023269) B1023269
theorem B682195 : Blo 678312 682195 := bstep (se 1 (by rfl) ⟨511646, by rfl⟩ : syracuseStep 682195 = 1023293) B1023293
theorem B3434723 : Blo 678312 3434723 := bstep (se 1 (by rfl) ⟨2576042, by rfl⟩ : syracuseStep 3434723 = 5152085) B5152085
theorem B682211 : Blo 678312 682211 := bstep (se 1 (by rfl) ⟨511658, by rfl⟩ : syracuseStep 682211 = 1023317) B1023317
theorem B1534193 : Blo 678312 1534193 := bstep (se 2 (by rfl) ⟨575322, by rfl⟩ : syracuseStep 1534193 = 1150645) B1150645
theorem B682227 : Blo 678312 682227 := bstep (se 1 (by rfl) ⟨511670, by rfl⟩ : syracuseStep 682227 = 1023341) B1023341
theorem B1534211 : Blo 678312 1534211 := bstep (se 1 (by rfl) ⟨1150658, by rfl⟩ : syracuseStep 1534211 = 2301317) B2301317
theorem B682243 : Blo 678312 682243 := bstep (se 1 (by rfl) ⟨511682, by rfl⟩ : syracuseStep 682243 = 1023365) B1023365
theorem B682259 : Blo 678312 682259 := bstep (se 1 (by rfl) ⟨511694, by rfl⟩ : syracuseStep 682259 = 1023389) B1023389
theorem B682275 : Blo 678312 682275 := bstep (se 1 (by rfl) ⟨511706, by rfl⟩ : syracuseStep 682275 = 1023413) B1023413
theorem B682291 : Blo 678312 682291 := bstep (se 1 (by rfl) ⟨511718, by rfl⟩ : syracuseStep 682291 = 1023437) B1023437
theorem B682307 : Blo 678312 682307 := bstep (se 1 (by rfl) ⟨511730, by rfl⟩ : syracuseStep 682307 = 1023461) B1023461
theorem B5171525 : Blo 678312 5171525 := bstep (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) B969661
theorem B1534481 : Blo 678312 1534481 := bstep (se 2 (by rfl) ⟨575430, by rfl⟩ : syracuseStep 1534481 = 1150861) B1150861
theorem B1534499 : Blo 678312 1534499 := bstep (se 1 (by rfl) ⟨1150874, by rfl⟩ : syracuseStep 1534499 = 2301749) B2301749
theorem B1632835 : Blo 678312 1632835 := bstep (se 1 (by rfl) ⟨1224626, by rfl⟩ : syracuseStep 1632835 = 2449253) B2449253
theorem B16509581 : Blo 678312 16509581 := bstep (se 3 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 16509581 = 6191093) B6191093
theorem B1534769 : Blo 678312 1534769 := bstep (se 2 (by rfl) ⟨575538, by rfl⟩ : syracuseStep 1534769 = 1151077) B1151077
theorem B1534787 : Blo 678312 1534787 := bstep (se 1 (by rfl) ⟨1151090, by rfl⟩ : syracuseStep 1534787 = 2302181) B2302181
theorem B3435533 : Blo 678312 3435533 := bstep (se 3 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 3435533 = 1288325) B1288325
theorem B1633297 : Blo 678312 1633297 := bstep (se 2 (by rfl) ⟨612486, by rfl⟩ : syracuseStep 1633297 = 1224973) B1224973
theorem B12414005 : Blo 678312 12414005 := bstep (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) B1163813
theorem B1535057 : Blo 678312 1535057 := bstep (se 2 (by rfl) ⟨575646, by rfl⟩ : syracuseStep 1535057 = 1151293) B1151293
theorem B1535075 : Blo 678312 1535075 := bstep (se 1 (by rfl) ⟨1151306, by rfl⟩ : syracuseStep 1535075 = 2302613) B2302613
theorem B1961165 : Blo 678312 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B2911565 : Blo 678312 2911565 := bstep (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) B1091837
theorem B2583971 : Blo 678312 2583971 := bstep (se 1 (by rfl) ⟨1937978, by rfl⟩ : syracuseStep 2583971 = 3875957) B3875957
theorem B2289329 : Blo 678312 2289329 := bstep (se 2 (by rfl) ⟨858498, by rfl⟩ : syracuseStep 2289329 = 1716997) B1716997
theorem B4419269 : Blo 678312 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B3731213 : Blo 678312 3731213 := bstep (se 3 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 3731213 = 1399205) B1399205
theorem B1306705 : Blo 678312 1306705 := bstep (se 2 (by rfl) ⟨490014, by rfl⟩ : syracuseStep 1306705 = 980029) B980029
theorem B2289869 : Blo 678312 2289869 := bstep (se 3 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 2289869 = 858701) B858701
theorem B2289923 : Blo 678312 2289923 := bstep (se 1 (by rfl) ⟨1717442, by rfl⟩ : syracuseStep 2289923 = 3434885) B3434885
theorem B2584973 : Blo 678312 2584973 := bstep (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) B969365
theorem B1208771 : Blo 678312 1208771 := bstep (se 1 (by rfl) ⟨906578, by rfl⟩ : syracuseStep 1208771 = 1813157) B1813157
theorem B2290193 : Blo 678312 2290193 := bstep (se 2 (by rfl) ⟨858822, by rfl⟩ : syracuseStep 2290193 = 1717645) B1717645
theorem B1962641 : Blo 678312 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B7336817 : Blo 678312 7336817 := bstep (se 2 (by rfl) ⟨2751306, by rfl⟩ : syracuseStep 7336817 = 5502613) B5502613
theorem B62813069 : Blo 678312 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B2290733 : Blo 678312 2290733 := bstep (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) B859025
theorem B2290787 : Blo 678312 2290787 := bstep (se 1 (by rfl) ⟨1718090, by rfl⟩ : syracuseStep 2290787 = 3436181) B3436181
theorem B6288581 : Blo 678312 6288581 := bstep (se 4 (by rfl) ⟨589554, by rfl⟩ : syracuseStep 6288581 = 1179109) B1179109
theorem B816355 : Blo 678312 816355 := bstep (se 1 (by rfl) ⟨612266, by rfl⟩ : syracuseStep 816355 = 1224533) B1224533
theorem B2291057 : Blo 678312 2291057 := bstep (se 2 (by rfl) ⟨859146, by rfl⟩ : syracuseStep 2291057 = 1718293) B1718293
theorem B816691 : Blo 678312 816691 := bstep (se 1 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 816691 = 1225037) B1225037
theorem B3438449 : Blo 678312 3438449 := bstep (se 2 (by rfl) ⟨1289418, by rfl⟩ : syracuseStep 3438449 = 2578837) B2578837
theorem B2455409 : Blo 678312 2455409 := bstep (se 2 (by rfl) ⟨920778, by rfl⟩ : syracuseStep 2455409 = 1841557) B1841557
theorem B1144705 : Blo 678312 1144705 := bstep (se 2 (by rfl) ⟨429264, by rfl⟩ : syracuseStep 1144705 = 858529) B858529
theorem B2291597 : Blo 678312 2291597 := bstep (se 3 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 2291597 = 859349) B859349
theorem B1144739 : Blo 678312 1144739 := bstep (se 1 (by rfl) ⟨858554, by rfl⟩ : syracuseStep 1144739 = 1717109) B1717109
theorem B2291651 : Blo 678312 2291651 := bstep (se 1 (by rfl) ⟨1718738, by rfl⟩ : syracuseStep 2291651 = 3437477) B3437477
theorem B2455523 : Blo 678312 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B1144867 : Blo 678312 1144867 := bstep (se 1 (by rfl) ⟨858650, by rfl⟩ : syracuseStep 1144867 = 1717301) B1717301
theorem B3864611 : Blo 678312 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B4913293 : Blo 678312 4913293 := bstep (se 3 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 4913293 = 1842485) B1842485
theorem B1145009 : Blo 678312 1145009 := bstep (se 2 (by rfl) ⟨429378, by rfl⟩ : syracuseStep 1145009 = 858757) B858757
theorem B2291921 : Blo 678312 2291921 := bstep (se 2 (by rfl) ⟨859470, by rfl⟩ : syracuseStep 2291921 = 1718941) B1718941
theorem B1145137 : Blo 678312 1145137 := bstep (se 2 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 1145137 = 858853) B858853
theorem B1145171 : Blo 678312 1145171 := bstep (se 1 (by rfl) ⟨858878, by rfl⟩ : syracuseStep 1145171 = 1717757) B1717757
theorem B1571185 : Blo 678312 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B817571 : Blo 678312 817571 := bstep (se 1 (by rfl) ⟨613178, by rfl⟩ : syracuseStep 817571 = 1226357) B1226357
theorem B2619811 : Blo 678312 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B2587085 : Blo 678312 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B1145299 : Blo 678312 1145299 := bstep (se 1 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 1145299 = 1717949) B1717949
theorem B4127203 : Blo 678312 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B2095651 : Blo 678312 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B981553 : Blo 678312 981553 := bstep (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) B736165
theorem B1145441 : Blo 678312 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B9435761 : Blo 678312 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1964675 : Blo 678312 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B1145569 : Blo 678312 1145569 := bstep (se 2 (by rfl) ⟨429588, by rfl⟩ : syracuseStep 1145569 = 859177) B859177
theorem B5798627 : Blo 678312 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B2292461 : Blo 678312 2292461 := bstep (se 3 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 2292461 = 859673) B859673
theorem B1145603 : Blo 678312 1145603 := bstep (se 1 (by rfl) ⟨859202, by rfl⟩ : syracuseStep 1145603 = 1718405) B1718405
theorem B2292515 : Blo 678312 2292515 := bstep (se 1 (by rfl) ⟨1719386, by rfl⟩ : syracuseStep 2292515 = 3438773) B3438773
theorem B1932113 : Blo 678312 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B1145731 : Blo 678312 1145731 := bstep (se 1 (by rfl) ⟨859298, by rfl⟩ : syracuseStep 1145731 = 1718597) B1718597
theorem B3275761 : Blo 678312 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B1145873 : Blo 678312 1145873 := bstep (se 2 (by rfl) ⟨429702, by rfl⟩ : syracuseStep 1145873 = 859405) B859405
theorem B2292785 : Blo 678312 2292785 := bstep (se 2 (by rfl) ⟨859794, by rfl⟩ : syracuseStep 2292785 = 1719589) B1719589
theorem B2751565 : Blo 678312 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B6716515 : Blo 678312 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B1146001 : Blo 678312 1146001 := bstep (se 2 (by rfl) ⟨429750, by rfl⟩ : syracuseStep 1146001 = 859501) B859501
theorem B1146035 : Blo 678312 1146035 := bstep (se 1 (by rfl) ⟨859526, by rfl⟩ : syracuseStep 1146035 = 1719053) B1719053
theorem B1637603 : Blo 678312 1637603 := bstep (se 1 (by rfl) ⟨1228202, by rfl⟩ : syracuseStep 1637603 = 2456405) B2456405
theorem B2587889 : Blo 678312 2587889 := bstep (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) B1940917
theorem B3439907 : Blo 678312 3439907 := bstep (se 1 (by rfl) ⟨2579930, by rfl⟩ : syracuseStep 3439907 = 5159861) B5159861
theorem B1146163 : Blo 678312 1146163 := bstep (se 1 (by rfl) ⟨859622, by rfl⟩ : syracuseStep 1146163 = 1719245) B1719245
theorem B1146305 : Blo 678312 1146305 := bstep (se 2 (by rfl) ⟨429864, by rfl⟩ : syracuseStep 1146305 = 859729) B859729
theorem B1932785 : Blo 678312 1932785 := bstep (se 2 (by rfl) ⟨724794, by rfl⟩ : syracuseStep 1932785 = 1449589) B1449589
theorem B1146433 : Blo 678312 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B2293325 : Blo 678312 2293325 := bstep (se 3 (by rfl) ⟨429998, by rfl⟩ : syracuseStep 2293325 = 859997) B859997
theorem B1375825 : Blo 678312 1375825 := bstep (se 2 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 1375825 = 1031869) B1031869
theorem B1146467 : Blo 678312 1146467 := bstep (se 1 (by rfl) ⟨859850, by rfl⟩ : syracuseStep 1146467 = 1719701) B1719701
theorem B2293379 : Blo 678312 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B1146595 : Blo 678312 1146595 := bstep (se 1 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 1146595 = 1719893) B1719893
theorem B1834787 : Blo 678312 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B8716085 : Blo 678312 8716085 := bstep (se 5 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 8716085 = 817133) B817133
theorem B1146737 : Blo 678312 1146737 := bstep (se 2 (by rfl) ⟨430026, by rfl⟩ : syracuseStep 1146737 = 860053) B860053
theorem B2588557 : Blo 678312 2588557 := bstep (se 3 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 2588557 = 970709) B970709
theorem B2293649 : Blo 678312 2293649 := bstep (se 2 (by rfl) ⟨860118, by rfl⟩ : syracuseStep 2293649 = 1720237) B1720237
theorem B1048481 : Blo 678312 1048481 := bstep (se 2 (by rfl) ⟨393180, by rfl⟩ : syracuseStep 1048481 = 786361) B786361
theorem B1146865 : Blo 678312 1146865 := bstep (se 2 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 1146865 = 860149) B860149
theorem B2293811 : Blo 678312 2293811 := bstep (se 1 (by rfl) ⟨1720358, by rfl⟩ : syracuseStep 2293811 = 3440717) B3440717
theorem B1376345 : Blo 678312 1376345 := bstep (se 2 (by rfl) ⟨516129, by rfl⟩ : syracuseStep 1376345 = 1032259) B1032259
theorem B17268997 : Blo 678312 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B27885869 : Blo 678312 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B2294081 : Blo 678312 2294081 := bstep (se 2 (by rfl) ⟨860280, by rfl⟩ : syracuseStep 2294081 = 1720561) B1720561
theorem B2490689 : Blo 678312 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B1147223 : Blo 678312 1147223 := bstep (se 1 (by rfl) ⟨860417, by rfl⟩ : syracuseStep 1147223 = 1720835) B1720835
theorem B4718999 : Blo 678312 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B1147351 : Blo 678312 1147351 := bstep (se 1 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 1147351 = 1721027) B1721027
theorem B13238801 : Blo 678312 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B2458291 : Blo 678312 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B1934027 : Blo 678312 1934027 := bstep (se 1 (by rfl) ⟨1450520, by rfl⟩ : syracuseStep 1934027 = 2901041) B2901041
theorem B3277529 : Blo 678312 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B5899013 : Blo 678312 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B3670829 : Blo 678312 3670829 := bstep (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) B1376561
theorem B2589515 : Blo 678312 2589515 := bstep (se 1 (by rfl) ⟨1942136, by rfl⟩ : syracuseStep 2589515 = 3884273) B3884273
theorem B2589529 : Blo 678312 2589529 := bstep (se 2 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 2589529 = 1942147) B1942147
theorem B2294621 : Blo 678312 2294621 := bstep (se 3 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 2294621 = 860483) B860483
theorem B5178329 : Blo 678312 5178329 := bstep (se 2 (by rfl) ⟨1941873, by rfl⟩ : syracuseStep 5178329 = 3883747) B3883747
theorem B1147979 : Blo 678312 1147979 := bstep (se 1 (by rfl) ⟨860984, by rfl⟩ : syracuseStep 1147979 = 1721969) B1721969
theorem B1148107 : Blo 678312 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B918745 : Blo 678312 918745 := bstep (se 2 (by rfl) ⟨344529, by rfl⟩ : syracuseStep 918745 = 689059) B689059
theorem B4916497 : Blo 678312 4916497 := bstep (se 2 (by rfl) ⟨1843686, by rfl⟩ : syracuseStep 4916497 = 3687373) B3687373
theorem B5801291 : Blo 678312 5801291 := bstep (se 1 (by rfl) ⟨4350968, by rfl⟩ : syracuseStep 5801291 = 8701937) B8701937
theorem B1148249 : Blo 678312 1148249 := bstep (se 2 (by rfl) ⟨430593, by rfl⟩ : syracuseStep 1148249 = 861187) B861187
theorem B3442013 : Blo 678312 3442013 := bstep (se 3 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 3442013 = 1290755) B1290755
theorem B2328011 : Blo 678312 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B1148377 : Blo 678312 1148377 := bstep (se 2 (by rfl) ⟨430641, by rfl⟩ : syracuseStep 1148377 = 861283) B861283
theorem B15926797 : Blo 678312 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B4916753 : Blo 678312 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B3868235 : Blo 678312 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B1017497 : Blo 678312 1017497 := bstep (se 2 (by rfl) ⟨381561, by rfl⟩ : syracuseStep 1017497 = 763123) B763123
theorem B1017611 : Blo 678312 1017611 := bstep (se 1 (by rfl) ⟨763208, by rfl⟩ : syracuseStep 1017611 = 1526417) B1526417
theorem B1017623 : Blo 678312 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B2590487 : Blo 678312 2590487 := bstep (se 1 (by rfl) ⟨1942865, by rfl⟩ : syracuseStep 2590487 = 3885731) B3885731
theorem B4130605 : Blo 678312 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B1017689 : Blo 678312 1017689 := bstep (se 2 (by rfl) ⟨381633, by rfl⟩ : syracuseStep 1017689 = 763267) B763267
theorem B1017803 : Blo 678312 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B2295755 : Blo 678312 2295755 := bstep (se 1 (by rfl) ⟨1721816, by rfl⟩ : syracuseStep 2295755 = 3443633) B3443633
theorem B1017815 : Blo 678312 1017815 := bstep (se 1 (by rfl) ⟨763361, by rfl⟩ : syracuseStep 1017815 = 1526723) B1526723
theorem B919513 : Blo 678312 919513 := bstep (se 2 (by rfl) ⟨344817, by rfl⟩ : syracuseStep 919513 = 689635) B689635
theorem B1148951 : Blo 678312 1148951 := bstep (se 1 (by rfl) ⟨861713, by rfl⟩ : syracuseStep 1148951 = 1723427) B1723427
theorem B1017881 : Blo 678312 1017881 := bstep (se 2 (by rfl) ⟨381705, by rfl⟩ : syracuseStep 1017881 = 763411) B763411
theorem B2328641 : Blo 678312 2328641 := bstep (se 2 (by rfl) ⟨873240, by rfl⟩ : syracuseStep 2328641 = 1746481) B1746481
theorem B1017995 : Blo 678312 1017995 := bstep (se 1 (by rfl) ⟨763496, by rfl⟩ : syracuseStep 1017995 = 1526993) B1526993
theorem B1018007 : Blo 678312 1018007 := bstep (se 1 (by rfl) ⟨763505, by rfl⟩ : syracuseStep 1018007 = 1527011) B1527011
theorem B1149079 : Blo 678312 1149079 := bstep (se 1 (by rfl) ⟨861809, by rfl⟩ : syracuseStep 1149079 = 1723619) B1723619
theorem B11634839 : Blo 678312 11634839 := bstep (se 1 (by rfl) ⟨8726129, by rfl⟩ : syracuseStep 11634839 = 17452259) B17452259
theorem B1018073 : Blo 678312 1018073 := bstep (se 2 (by rfl) ⟨381777, by rfl⟩ : syracuseStep 1018073 = 763555) B763555
theorem B2296025 : Blo 678312 2296025 := bstep (se 2 (by rfl) ⟨861009, by rfl⟩ : syracuseStep 2296025 = 1722019) B1722019
theorem B5507345 : Blo 678312 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B1018187 : Blo 678312 1018187 := bstep (se 1 (by rfl) ⟨763640, by rfl⟩ : syracuseStep 1018187 = 1527281) B1527281
theorem B1018199 : Blo 678312 1018199 := bstep (se 1 (by rfl) ⟨763649, by rfl⟩ : syracuseStep 1018199 = 1527299) B1527299
theorem B690539 : Blo 678312 690539 := bstep (se 1 (by rfl) ⟨517904, by rfl⟩ : syracuseStep 690539 = 1035809) B1035809
theorem B1018265 : Blo 678312 1018265 := bstep (se 2 (by rfl) ⟨381849, by rfl⟩ : syracuseStep 1018265 = 763699) B763699
theorem B1018379 : Blo 678312 1018379 := bstep (se 1 (by rfl) ⟨763784, by rfl⟩ : syracuseStep 1018379 = 1527569) B1527569
theorem B1018391 : Blo 678312 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B1018457 : Blo 678312 1018457 := bstep (se 2 (by rfl) ⟨381921, by rfl⟩ : syracuseStep 1018457 = 763843) B763843
theorem B5900951 : Blo 678312 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B1018571 : Blo 678312 1018571 := bstep (se 1 (by rfl) ⟨763928, by rfl⟩ : syracuseStep 1018571 = 1527857) B1527857
theorem B1018583 : Blo 678312 1018583 := bstep (se 1 (by rfl) ⟨763937, by rfl⟩ : syracuseStep 1018583 = 1527875) B1527875
theorem B1149707 : Blo 678312 1149707 := bstep (se 1 (by rfl) ⟨862280, by rfl⟩ : syracuseStep 1149707 = 1724561) B1724561
theorem B1018649 : Blo 678312 1018649 := bstep (se 2 (by rfl) ⟨381993, by rfl⟩ : syracuseStep 1018649 = 763987) B763987
theorem B1018763 : Blo 678312 1018763 := bstep (se 1 (by rfl) ⟨764072, by rfl⟩ : syracuseStep 1018763 = 1528145) B1528145
theorem B1149835 : Blo 678312 1149835 := bstep (se 1 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 1149835 = 1724753) B1724753
theorem B1018775 : Blo 678312 1018775 := bstep (se 1 (by rfl) ⟨764081, by rfl⟩ : syracuseStep 1018775 = 1528163) B1528163
theorem B2296727 : Blo 678312 2296727 := bstep (se 1 (by rfl) ⟨1722545, by rfl⟩ : syracuseStep 2296727 = 3445091) B3445091
theorem B1018841 : Blo 678312 1018841 := bstep (se 2 (by rfl) ⟨382065, by rfl⟩ : syracuseStep 1018841 = 764131) B764131
theorem B1149977 : Blo 678312 1149977 := bstep (se 2 (by rfl) ⟨431241, by rfl⟩ : syracuseStep 1149977 = 862483) B862483
theorem B1018955 : Blo 678312 1018955 := bstep (se 1 (by rfl) ⟨764216, by rfl⟩ : syracuseStep 1018955 = 1528433) B1528433
theorem B6556747 : Blo 678312 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B1018967 : Blo 678312 1018967 := bstep (se 1 (by rfl) ⟨764225, by rfl⟩ : syracuseStep 1018967 = 1528451) B1528451
theorem B1019033 : Blo 678312 1019033 := bstep (se 2 (by rfl) ⟨382137, by rfl⟩ : syracuseStep 1019033 = 764275) B764275
theorem B1150105 : Blo 678312 1150105 := bstep (se 2 (by rfl) ⟨431289, by rfl⟩ : syracuseStep 1150105 = 862579) B862579
theorem B1019147 : Blo 678312 1019147 := bstep (se 1 (by rfl) ⟨764360, by rfl⟩ : syracuseStep 1019147 = 1528721) B1528721
theorem B1019159 : Blo 678312 1019159 := bstep (se 1 (by rfl) ⟨764369, by rfl⟩ : syracuseStep 1019159 = 1528739) B1528739
theorem B1019225 : Blo 678312 1019225 := bstep (se 2 (by rfl) ⟨382209, by rfl⟩ : syracuseStep 1019225 = 764419) B764419
theorem B3444119 : Blo 678312 3444119 := bstep (se 1 (by rfl) ⟨2583089, by rfl⟩ : syracuseStep 3444119 = 5166179) B5166179
theorem B2297267 : Blo 678312 2297267 := bstep (se 1 (by rfl) ⟨1722950, by rfl⟩ : syracuseStep 2297267 = 3445901) B3445901
theorem B1510859 : Blo 678312 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B1019339 : Blo 678312 1019339 := bstep (se 1 (by rfl) ⟨764504, by rfl⟩ : syracuseStep 1019339 = 1529009) B1529009
theorem B1019351 : Blo 678312 1019351 := bstep (se 1 (by rfl) ⟨764513, by rfl⟩ : syracuseStep 1019351 = 1529027) B1529027
theorem B1019417 : Blo 678312 1019417 := bstep (se 2 (by rfl) ⟨382281, by rfl⟩ : syracuseStep 1019417 = 764563) B764563
theorem B724555 : Blo 678312 724555 := bstep (se 1 (by rfl) ⟨543416, by rfl⟩ : syracuseStep 724555 = 1086833) B1086833
theorem B1019531 : Blo 678312 1019531 := bstep (se 1 (by rfl) ⟨764648, by rfl⟩ : syracuseStep 1019531 = 1529297) B1529297
theorem B1019543 : Blo 678312 1019543 := bstep (se 1 (by rfl) ⟨764657, by rfl⟩ : syracuseStep 1019543 = 1529315) B1529315
theorem B2297537 : Blo 678312 2297537 := bstep (se 2 (by rfl) ⟨861576, by rfl⟩ : syracuseStep 2297537 = 1723153) B1723153
theorem B1150679 : Blo 678312 1150679 := bstep (se 1 (by rfl) ⟨863009, by rfl⟩ : syracuseStep 1150679 = 1726019) B1726019
theorem B1019609 : Blo 678312 1019609 := bstep (se 2 (by rfl) ⟨382353, by rfl⟩ : syracuseStep 1019609 = 764707) B764707
theorem B1019723 : Blo 678312 1019723 := bstep (se 1 (by rfl) ⟨764792, by rfl⟩ : syracuseStep 1019723 = 1529585) B1529585
theorem B1019735 : Blo 678312 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B1150807 : Blo 678312 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B1019801 : Blo 678312 1019801 := bstep (se 2 (by rfl) ⟨382425, by rfl⟩ : syracuseStep 1019801 = 764851) B764851
theorem B1019915 : Blo 678312 1019915 := bstep (se 1 (by rfl) ⟨764936, by rfl⟩ : syracuseStep 1019915 = 1529873) B1529873
theorem B1019927 : Blo 678312 1019927 := bstep (se 1 (by rfl) ⟨764945, by rfl⟩ : syracuseStep 1019927 = 1529891) B1529891
theorem B1019993 : Blo 678312 1019993 := bstep (se 2 (by rfl) ⟨382497, by rfl⟩ : syracuseStep 1019993 = 764995) B764995
theorem B3870899 : Blo 678312 3870899 := bstep (se 1 (by rfl) ⟨2903174, by rfl⟩ : syracuseStep 3870899 = 5806349) B5806349
theorem B1020107 : Blo 678312 1020107 := bstep (se 1 (by rfl) ⟨765080, by rfl⟩ : syracuseStep 1020107 = 1530161) B1530161
theorem B1020119 : Blo 678312 1020119 := bstep (se 1 (by rfl) ⟨765089, by rfl⟩ : syracuseStep 1020119 = 1530179) B1530179
theorem B921817 : Blo 678312 921817 := bstep (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) B691363
theorem B2298077 : Blo 678312 2298077 := bstep (se 3 (by rfl) ⟨430889, by rfl⟩ : syracuseStep 2298077 = 861779) B861779
theorem B7737605 : Blo 678312 7737605 := bstep (se 4 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 7737605 = 1450801) B1450801
theorem B1020185 : Blo 678312 1020185 := bstep (se 2 (by rfl) ⟨382569, by rfl⟩ : syracuseStep 1020185 = 765139) B765139
theorem B2953523 : Blo 678312 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1020299 : Blo 678312 1020299 := bstep (se 1 (by rfl) ⟨765224, by rfl⟩ : syracuseStep 1020299 = 1530449) B1530449
theorem B1020311 : Blo 678312 1020311 := bstep (se 1 (by rfl) ⟨765233, by rfl⟩ : syracuseStep 1020311 = 1530467) B1530467
theorem B725431 : Blo 678312 725431 := bstep (se 1 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 725431 = 1088147) B1088147
theorem B1020377 : Blo 678312 1020377 := bstep (se 2 (by rfl) ⟨382641, by rfl⟩ : syracuseStep 1020377 = 765283) B765283
theorem B1020491 : Blo 678312 1020491 := bstep (se 1 (by rfl) ⟨765368, by rfl⟩ : syracuseStep 1020491 = 1530737) B1530737
theorem B1020503 : Blo 678312 1020503 := bstep (se 1 (by rfl) ⟨765377, by rfl⟩ : syracuseStep 1020503 = 1530755) B1530755
theorem B21041795 : Blo 678312 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B1020569 : Blo 678312 1020569 := bstep (se 2 (by rfl) ⟨382713, by rfl⟩ : syracuseStep 1020569 = 765427) B765427
theorem B1020683 : Blo 678312 1020683 := bstep (se 1 (by rfl) ⟨765512, by rfl⟩ : syracuseStep 1020683 = 1531025) B1531025
theorem B1020695 : Blo 678312 1020695 := bstep (se 1 (by rfl) ⟨765521, by rfl⟩ : syracuseStep 1020695 = 1531043) B1531043
theorem B1020761 : Blo 678312 1020761 := bstep (se 2 (by rfl) ⟨382785, by rfl⟩ : syracuseStep 1020761 = 765571) B765571
theorem B725879 : Blo 678312 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B1020875 : Blo 678312 1020875 := bstep (se 1 (by rfl) ⟨765656, by rfl⟩ : syracuseStep 1020875 = 1531313) B1531313
theorem B1020887 : Blo 678312 1020887 := bstep (se 1 (by rfl) ⟨765665, by rfl⟩ : syracuseStep 1020887 = 1531331) B1531331
theorem B1840151 : Blo 678312 1840151 := bstep (se 1 (by rfl) ⟨1380113, by rfl⟩ : syracuseStep 1840151 = 2760227) B2760227
theorem B1020953 : Blo 678312 1020953 := bstep (se 2 (by rfl) ⟨382857, by rfl⟩ : syracuseStep 1020953 = 765715) B765715
theorem B9409571 : Blo 678312 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B1021067 : Blo 678312 1021067 := bstep (se 1 (by rfl) ⟨765800, by rfl⟩ : syracuseStep 1021067 = 1531601) B1531601
theorem B1021079 : Blo 678312 1021079 := bstep (se 1 (by rfl) ⟨765809, by rfl⟩ : syracuseStep 1021079 = 1531619) B1531619
theorem B1021145 : Blo 678312 1021145 := bstep (se 2 (by rfl) ⟨382929, by rfl⟩ : syracuseStep 1021145 = 765859) B765859
theorem B726251 : Blo 678312 726251 := bstep (se 1 (by rfl) ⟨544688, by rfl⟩ : syracuseStep 726251 = 1089377) B1089377
theorem B1086743 : Blo 678312 1086743 := bstep (se 1 (by rfl) ⟨815057, by rfl⟩ : syracuseStep 1086743 = 1630115) B1630115
theorem B1021259 : Blo 678312 1021259 := bstep (se 1 (by rfl) ⟨765944, by rfl⟩ : syracuseStep 1021259 = 1531889) B1531889
theorem B2299211 : Blo 678312 2299211 := bstep (se 1 (by rfl) ⟨1724408, by rfl⟩ : syracuseStep 2299211 = 3448817) B3448817
theorem B1021271 : Blo 678312 1021271 := bstep (se 1 (by rfl) ⟨765953, by rfl⟩ : syracuseStep 1021271 = 1531907) B1531907
theorem B1021337 : Blo 678312 1021337 := bstep (se 2 (by rfl) ⟨383001, by rfl⟩ : syracuseStep 1021337 = 766003) B766003
theorem B1742273 : Blo 678312 1742273 := bstep (se 2 (by rfl) ⟨653352, by rfl⟩ : syracuseStep 1742273 = 1306705) B1306705
theorem B1021451 : Blo 678312 1021451 := bstep (se 1 (by rfl) ⟨766088, by rfl⟩ : syracuseStep 1021451 = 1532177) B1532177
theorem B1021463 : Blo 678312 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B1021529 : Blo 678312 1021529 := bstep (se 2 (by rfl) ⟨383073, by rfl⟩ : syracuseStep 1021529 = 766147) B766147
theorem B2299481 : Blo 678312 2299481 := bstep (se 2 (by rfl) ⟨862305, by rfl⟩ : syracuseStep 2299481 = 1724611) B1724611
theorem B3872357 : Blo 678312 3872357 := bstep (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) B726067
theorem B1021643 : Blo 678312 1021643 := bstep (se 1 (by rfl) ⟨766232, by rfl⟩ : syracuseStep 1021643 = 1532465) B1532465
theorem B1021655 : Blo 678312 1021655 := bstep (se 1 (by rfl) ⟨766241, by rfl⟩ : syracuseStep 1021655 = 1532483) B1532483
theorem B1021721 : Blo 678312 1021721 := bstep (se 2 (by rfl) ⟨383145, by rfl⟩ : syracuseStep 1021721 = 766291) B766291
theorem B1021835 : Blo 678312 1021835 := bstep (se 1 (by rfl) ⟨766376, by rfl⟩ : syracuseStep 1021835 = 1532753) B1532753
theorem B1120151 : Blo 678312 1120151 := bstep (se 1 (by rfl) ⟨840113, by rfl⟩ : syracuseStep 1120151 = 1680227) B1680227
theorem B1021847 : Blo 678312 1021847 := bstep (se 1 (by rfl) ⟨766385, by rfl⟩ : syracuseStep 1021847 = 1532771) B1532771
theorem B1087435 : Blo 678312 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B1939403 : Blo 678312 1939403 := bstep (se 1 (by rfl) ⟨1454552, by rfl⟩ : syracuseStep 1939403 = 2909105) B2909105
theorem B1021913 : Blo 678312 1021913 := bstep (se 2 (by rfl) ⟨383217, by rfl⟩ : syracuseStep 1021913 = 766435) B766435
theorem B1022027 : Blo 678312 1022027 := bstep (se 1 (by rfl) ⟨766520, by rfl⟩ : syracuseStep 1022027 = 1533041) B1533041
theorem B1022039 : Blo 678312 1022039 := bstep (se 1 (by rfl) ⟨766529, by rfl⟩ : syracuseStep 1022039 = 1533059) B1533059
theorem B1022105 : Blo 678312 1022105 := bstep (se 2 (by rfl) ⟨383289, by rfl⟩ : syracuseStep 1022105 = 766579) B766579
theorem B727255 : Blo 678312 727255 := bstep (se 1 (by rfl) ⟨545441, by rfl⟩ : syracuseStep 727255 = 1090883) B1090883
theorem B1022219 : Blo 678312 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B3873041 : Blo 678312 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B1022231 : Blo 678312 1022231 := bstep (se 1 (by rfl) ⟨766673, by rfl⟩ : syracuseStep 1022231 = 1533347) B1533347
theorem B2300183 : Blo 678312 2300183 := bstep (se 1 (by rfl) ⟨1725137, by rfl⟩ : syracuseStep 2300183 = 3450275) B3450275
theorem B1939801 : Blo 678312 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B1022297 : Blo 678312 1022297 := bstep (se 2 (by rfl) ⟨383361, by rfl⟩ : syracuseStep 1022297 = 766723) B766723
theorem B1022411 : Blo 678312 1022411 := bstep (se 1 (by rfl) ⟨766808, by rfl⟩ : syracuseStep 1022411 = 1533617) B1533617
theorem B1022423 : Blo 678312 1022423 := bstep (se 1 (by rfl) ⟨766817, by rfl⟩ : syracuseStep 1022423 = 1533635) B1533635
theorem B1022489 : Blo 678312 1022489 := bstep (se 2 (by rfl) ⟨383433, by rfl⟩ : syracuseStep 1022489 = 766867) B766867
theorem B1022603 : Blo 678312 1022603 := bstep (se 1 (by rfl) ⟨766952, by rfl⟩ : syracuseStep 1022603 = 1533905) B1533905
theorem B1022615 : Blo 678312 1022615 := bstep (se 1 (by rfl) ⟨766961, by rfl⟩ : syracuseStep 1022615 = 1533923) B1533923
theorem B1022681 : Blo 678312 1022681 := bstep (se 2 (by rfl) ⟨383505, by rfl⟩ : syracuseStep 1022681 = 767011) B767011
theorem B2300723 : Blo 678312 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B1022795 : Blo 678312 1022795 := bstep (se 1 (by rfl) ⟨767096, by rfl⟩ : syracuseStep 1022795 = 1534193) B1534193
theorem B1022807 : Blo 678312 1022807 := bstep (se 1 (by rfl) ⟨767105, by rfl⟩ : syracuseStep 1022807 = 1534211) B1534211
theorem B3447683 : Blo 678312 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B1022873 : Blo 678312 1022873 := bstep (se 2 (by rfl) ⟨383577, by rfl⟩ : syracuseStep 1022873 = 767155) B767155
theorem B1088473 : Blo 678312 1088473 := bstep (se 2 (by rfl) ⟨408177, by rfl⟩ : syracuseStep 1088473 = 816355) B816355
theorem B728075 : Blo 678312 728075 := bstep (se 1 (by rfl) ⟨546056, by rfl⟩ : syracuseStep 728075 = 1092113) B1092113
theorem B1022987 : Blo 678312 1022987 := bstep (se 1 (by rfl) ⟨767240, by rfl⟩ : syracuseStep 1022987 = 1534481) B1534481
theorem B1022999 : Blo 678312 1022999 := bstep (se 1 (by rfl) ⟨767249, by rfl⟩ : syracuseStep 1022999 = 1534499) B1534499
theorem B2300993 : Blo 678312 2300993 := bstep (se 2 (by rfl) ⟨862872, by rfl⟩ : syracuseStep 2300993 = 1725745) B1725745
theorem B1023065 : Blo 678312 1023065 := bstep (se 2 (by rfl) ⟨383649, by rfl⟩ : syracuseStep 1023065 = 767299) B767299
theorem B859339 : Blo 678312 859339 := bstep (se 1 (by rfl) ⟨644504, by rfl⟩ : syracuseStep 859339 = 1289009) B1289009
theorem B1023179 : Blo 678312 1023179 := bstep (se 1 (by rfl) ⟨767384, by rfl⟩ : syracuseStep 1023179 = 1534769) B1534769
theorem B1023191 : Blo 678312 1023191 := bstep (se 1 (by rfl) ⟨767393, by rfl⟩ : syracuseStep 1023191 = 1534787) B1534787
theorem B2759953 : Blo 678312 2759953 := bstep (se 2 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 2759953 = 2069965) B2069965
theorem B1023257 : Blo 678312 1023257 := bstep (se 2 (by rfl) ⟨383721, by rfl⟩ : syracuseStep 1023257 = 767443) B767443
theorem B1023371 : Blo 678312 1023371 := bstep (se 1 (by rfl) ⟨767528, by rfl⟩ : syracuseStep 1023371 = 1535057) B1535057
theorem B1023383 : Blo 678312 1023383 := bstep (se 1 (by rfl) ⟨767537, by rfl⟩ : syracuseStep 1023383 = 1535075) B1535075
theorem B1088921 : Blo 678312 1088921 := bstep (se 2 (by rfl) ⟨408345, by rfl⟩ : syracuseStep 1088921 = 816691) B816691
theorem B1023449 : Blo 678312 1023449 := bstep (se 2 (by rfl) ⟨383793, by rfl⟩ : syracuseStep 1023449 = 767587) B767587
theorem B1941043 : Blo 678312 1941043 := bstep (se 1 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 1941043 = 2911565) B2911565
theorem B2301533 : Blo 678312 2301533 := bstep (se 3 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 2301533 = 863075) B863075
theorem B860311 : Blo 678312 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B1450315 : Blo 678312 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B1450391 : Blo 678312 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B2761133 : Blo 678312 2761133 := bstep (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) B1035425
theorem B4891211 : Blo 678312 4891211 := bstep (se 1 (by rfl) ⟨3668408, by rfl⟩ : syracuseStep 4891211 = 7336817) B7336817
theorem B2302667 : Blo 678312 2302667 := bstep (se 1 (by rfl) ⟨1727000, by rfl⟩ : syracuseStep 2302667 = 3454001) B3454001
theorem B5513933 : Blo 678312 5513933 := bstep (se 3 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 5513933 = 2067725) B2067725
theorem B2794201 : Blo 678312 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B2761523 : Blo 678312 2761523 := bstep (se 1 (by rfl) ⟨2071142, by rfl⟩ : syracuseStep 2761523 = 4142285) B4142285
theorem B861131 : Blo 678312 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B763159 : Blo 678312 763159 := bstep (se 1 (by rfl) ⟨572369, by rfl⟩ : syracuseStep 763159 = 1144739) B1144739
theorem B4662593 : Blo 678312 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B4367681 : Blo 678312 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B3876275 : Blo 678312 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B763339 : Blo 678312 763339 := bstep (se 1 (by rfl) ⟨572504, by rfl⟩ : syracuseStep 763339 = 1145009) B1145009
theorem B8955353 : Blo 678312 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B763447 : Blo 678312 763447 := bstep (se 1 (by rfl) ⟨572585, by rfl⟩ : syracuseStep 763447 = 1145171) B1145171
theorem B5809765 : Blo 678312 5809765 := bstep (se 4 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 5809765 = 1089331) B1089331
theorem B1287809 : Blo 678312 1287809 := bstep (se 2 (by rfl) ⟨482928, by rfl⟩ : syracuseStep 1287809 = 965857) B965857
theorem B861835 : Blo 678312 861835 := bstep (se 1 (by rfl) ⟨646376, by rfl⟩ : syracuseStep 861835 = 1292753) B1292753
theorem B763627 : Blo 678312 763627 := bstep (se 1 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 763627 = 1145441) B1145441
theorem B2762561 : Blo 678312 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B763735 : Blo 678312 763735 := bstep (se 1 (by rfl) ⟨572801, by rfl⟩ : syracuseStep 763735 = 1145603) B1145603
theorem B1288075 : Blo 678312 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B862103 : Blo 678312 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B763915 : Blo 678312 763915 := bstep (se 1 (by rfl) ⟨572936, by rfl⟩ : syracuseStep 763915 = 1145873) B1145873
theorem B764023 : Blo 678312 764023 := bstep (se 1 (by rfl) ⟨573017, by rfl⟩ : syracuseStep 764023 = 1146035) B1146035
theorem B1452161 : Blo 678312 1452161 := bstep (se 2 (by rfl) ⟨544560, by rfl⟩ : syracuseStep 1452161 = 1089121) B1089121
theorem B1091735 : Blo 678312 1091735 := bstep (se 1 (by rfl) ⟨818801, by rfl⟩ : syracuseStep 1091735 = 1637603) B1637603
theorem B2074841 : Blo 678312 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B764203 : Blo 678312 764203 := bstep (se 1 (by rfl) ⟨573152, by rfl⟩ : syracuseStep 764203 = 1146305) B1146305
theorem B1288523 : Blo 678312 1288523 := bstep (se 1 (by rfl) ⟨966392, by rfl⟩ : syracuseStep 1288523 = 1932785) B1932785
theorem B764311 : Blo 678312 764311 := bstep (se 1 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 764311 = 1146467) B1146467
theorem B1288705 : Blo 678312 1288705 := bstep (se 2 (by rfl) ⟨483264, by rfl⟩ : syracuseStep 1288705 = 966529) B966529
theorem B3451409 : Blo 678312 3451409 := bstep (se 2 (by rfl) ⟨1294278, by rfl⟩ : syracuseStep 3451409 = 2588557) B2588557
theorem B1223191 : Blo 678312 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B5810723 : Blo 678312 5810723 := bstep (se 1 (by rfl) ⟨4358042, by rfl⟩ : syracuseStep 5810723 = 8716085) B8716085
theorem B764491 : Blo 678312 764491 := bstep (se 1 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 764491 = 1146737) B1146737
theorem B862807 : Blo 678312 862807 := bstep (se 1 (by rfl) ⟨647105, by rfl⟩ : syracuseStep 862807 = 1294211) B1294211
theorem B698987 : Blo 678312 698987 := bstep (se 1 (by rfl) ⟨524240, by rfl⟩ : syracuseStep 698987 = 1048481) B1048481
theorem B3451571 : Blo 678312 3451571 := bstep (se 1 (by rfl) ⟨2588678, by rfl⟩ : syracuseStep 3451571 = 5177357) B5177357
theorem B764599 : Blo 678312 764599 := bstep (se 1 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 764599 = 1146899) B1146899
theorem B4139851 : Blo 678312 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B1289047 : Blo 678312 1289047 := bstep (se 1 (by rfl) ⟨966785, by rfl⟩ : syracuseStep 1289047 = 1933571) B1933571
theorem B3877733 : Blo 678312 3877733 := bstep (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) B727075
theorem B764779 : Blo 678312 764779 := bstep (se 1 (by rfl) ⟨573584, by rfl⟩ : syracuseStep 764779 = 1147169) B1147169
theorem B764887 : Blo 678312 764887 := bstep (se 1 (by rfl) ⟨573665, by rfl⟩ : syracuseStep 764887 = 1147331) B1147331
theorem B6204451 : Blo 678312 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B1289267 : Blo 678312 1289267 := bstep (se 1 (by rfl) ⟨966950, by rfl⟩ : syracuseStep 1289267 = 1933901) B1933901
theorem B765067 : Blo 678312 765067 := bstep (se 1 (by rfl) ⟨573800, by rfl⟩ : syracuseStep 765067 = 1147601) B1147601
theorem B765175 : Blo 678312 765175 := bstep (se 1 (by rfl) ⟨573881, by rfl⟩ : syracuseStep 765175 = 1147763) B1147763
theorem B1289495 : Blo 678312 1289495 := bstep (se 1 (by rfl) ⟨967121, by rfl⟩ : syracuseStep 1289495 = 1934243) B1934243
theorem B3878189 : Blo 678312 3878189 := bstep (se 3 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 3878189 = 1454321) B1454321
theorem B4664641 : Blo 678312 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B765355 : Blo 678312 765355 := bstep (se 1 (by rfl) ⟨574016, by rfl⟩ : syracuseStep 765355 = 1148033) B1148033
theorem B765463 : Blo 678312 765463 := bstep (se 1 (by rfl) ⟨574097, by rfl⟩ : syracuseStep 765463 = 1148195) B1148195
theorem B1289753 : Blo 678312 1289753 := bstep (se 2 (by rfl) ⟨483657, by rfl⟩ : syracuseStep 1289753 = 967315) B967315
theorem B765643 : Blo 678312 765643 := bstep (se 1 (by rfl) ⟨574232, by rfl⟩ : syracuseStep 765643 = 1148465) B1148465
theorem B765751 : Blo 678312 765751 := bstep (se 1 (by rfl) ⟨574313, by rfl⟩ : syracuseStep 765751 = 1148627) B1148627
theorem B2764637 : Blo 678312 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B1453963 : Blo 678312 1453963 := bstep (se 1 (by rfl) ⟨1090472, by rfl⟩ : syracuseStep 1453963 = 2180945) B2180945
theorem B25472945 : Blo 678312 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B1290163 : Blo 678312 1290163 := bstep (se 1 (by rfl) ⟨967622, by rfl⟩ : syracuseStep 1290163 = 1935245) B1935245
theorem B3878873 : Blo 678312 3878873 := bstep (se 2 (by rfl) ⟨1454577, by rfl⟩ : syracuseStep 3878873 = 2909155) B2909155
theorem B765931 : Blo 678312 765931 := bstep (se 1 (by rfl) ⟨574448, by rfl⟩ : syracuseStep 765931 = 1148897) B1148897
theorem B766039 : Blo 678312 766039 := bstep (se 1 (by rfl) ⟨574529, by rfl⟩ : syracuseStep 766039 = 1149059) B1149059
theorem B4960349 : Blo 678312 4960349 := bstep (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) B1860131
theorem B766219 : Blo 678312 766219 := bstep (se 1 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 766219 = 1149329) B1149329
theorem B4370705 : Blo 678312 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B9318773 : Blo 678312 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B766327 : Blo 678312 766327 := bstep (se 1 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 766327 = 1149491) B1149491
theorem B1290649 : Blo 678312 1290649 := bstep (se 2 (by rfl) ⟨483993, by rfl⟩ : syracuseStep 1290649 = 967987) B967987
theorem B2175511 : Blo 678312 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B766507 : Blo 678312 766507 := bstep (se 1 (by rfl) ⟨574880, by rfl⟩ : syracuseStep 766507 = 1149761) B1149761
theorem B3453515 : Blo 678312 3453515 := bstep (se 1 (by rfl) ⟨2590136, by rfl⟩ : syracuseStep 3453515 = 5180273) B5180273
theorem B766615 : Blo 678312 766615 := bstep (se 1 (by rfl) ⟨574961, by rfl⟩ : syracuseStep 766615 = 1149923) B1149923
theorem B4371245 : Blo 678312 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B766795 : Blo 678312 766795 := bstep (se 1 (by rfl) ⟨575096, by rfl⟩ : syracuseStep 766795 = 1150193) B1150193
theorem B766903 : Blo 678312 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B2175947 : Blo 678312 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1291211 : Blo 678312 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B1717271 : Blo 678312 1717271 := bstep (se 1 (by rfl) ⟨1287953, by rfl⟩ : syracuseStep 1717271 = 2575907) B2575907
theorem B1553431 : Blo 678312 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B767083 : Blo 678312 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B1291393 : Blo 678312 1291393 := bstep (se 2 (by rfl) ⟨484272, by rfl⟩ : syracuseStep 1291393 = 968545) B968545
theorem B767191 : Blo 678312 767191 := bstep (se 1 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 767191 = 1150787) B1150787
theorem B1455347 : Blo 678312 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B12432685 : Blo 678312 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B767371 : Blo 678312 767371 := bstep (se 1 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 767371 = 1151057) B1151057
theorem B767479 : Blo 678312 767479 := bstep (se 1 (by rfl) ⟨575609, by rfl⟩ : syracuseStep 767479 = 1151219) B1151219
theorem B11941507 : Blo 678312 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B2766487 : Blo 678312 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B2176715 : Blo 678312 2176715 := bstep (se 1 (by rfl) ⟨1632536, by rfl⟩ : syracuseStep 2176715 = 3265073) B3265073
theorem B1718081 : Blo 678312 1718081 := bstep (se 2 (by rfl) ⟨644280, by rfl⟩ : syracuseStep 1718081 = 1288561) B1288561
theorem B1292107 : Blo 678312 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B1292183 : Blo 678312 1292183 := bstep (se 1 (by rfl) ⟨969137, by rfl⟩ : syracuseStep 1292183 = 1938275) B1938275
theorem B3094451 : Blo 678312 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1456193 : Blo 678312 1456193 := bstep (se 2 (by rfl) ⟨546072, by rfl⟩ : syracuseStep 1456193 = 1092145) B1092145
theorem B2177113 : Blo 678312 2177113 := bstep (se 2 (by rfl) ⟨816417, by rfl⟩ : syracuseStep 2177113 = 1632835) B1632835
theorem B2177227 : Blo 678312 2177227 := bstep (se 1 (by rfl) ⟨1632920, by rfl⟩ : syracuseStep 2177227 = 3265841) B3265841
theorem B735575 : Blo 678312 735575 := bstep (se 1 (by rfl) ⟨551681, by rfl⟩ : syracuseStep 735575 = 1103363) B1103363
theorem B1718617 : Blo 678312 1718617 := bstep (se 2 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 1718617 = 1288963) B1288963
theorem B1456535 : Blo 678312 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B1292851 : Blo 678312 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B2177729 : Blo 678312 2177729 := bstep (se 2 (by rfl) ⟨816648, by rfl⟩ : syracuseStep 2177729 = 1633297) B1633297
theorem B1293079 : Blo 678312 1293079 := bstep (se 1 (by rfl) ⟨969809, by rfl⟩ : syracuseStep 1293079 = 1939619) B1939619
theorem B736043 : Blo 678312 736043 := bstep (se 1 (by rfl) ⟨552032, by rfl⟩ : syracuseStep 736043 = 1104065) B1104065
theorem B1293185 : Blo 678312 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B1489817 : Blo 678312 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B11647961 : Blo 678312 11647961 := bstep (se 2 (by rfl) ⟨4367985, by rfl⟩ : syracuseStep 11647961 = 8735971) B8735971
theorem B1293337 : Blo 678312 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B5815475 : Blo 678312 5815475 := bstep (se 1 (by rfl) ⟨4361606, by rfl⟩ : syracuseStep 5815475 = 8723213) B8723213
theorem B2178355 : Blo 678312 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B1719731 : Blo 678312 1719731 := bstep (se 1 (by rfl) ⟨1289798, by rfl⟩ : syracuseStep 1719731 = 2579597) B2579597
theorem B3259921 : Blo 678312 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B1720025 : Blo 678312 1720025 := bstep (se 2 (by rfl) ⟨645009, by rfl⟩ : syracuseStep 1720025 = 1290019) B1290019
theorem B966745 : Blo 678312 966745 := bstep (se 2 (by rfl) ⟨362529, by rfl⟩ : syracuseStep 966745 = 725059) B725059
theorem B2900099 : Blo 678312 2900099 := bstep (se 1 (by rfl) ⟨2175074, by rfl⟩ : syracuseStep 2900099 = 4350149) B4350149
theorem B1294643 : Blo 678312 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B1294795 : Blo 678312 1294795 := bstep (se 1 (by rfl) ⟨971096, by rfl⟩ : syracuseStep 1294795 = 1942193) B1942193
theorem B2900441 : Blo 678312 2900441 := bstep (se 2 (by rfl) ⟨1087665, by rfl⟩ : syracuseStep 2900441 = 2175331) B2175331
theorem B3883565 : Blo 678312 3883565 := bstep (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) B1456337
theorem B1229377 : Blo 678312 1229377 := bstep (se 2 (by rfl) ⟨461016, by rfl⟩ : syracuseStep 1229377 = 922033) B922033
theorem B9814709 : Blo 678312 9814709 := bstep (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) B920129
theorem B1295129 : Blo 678312 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B2180189 : Blo 678312 2180189 := bstep (se 3 (by rfl) ⟨408785, by rfl⟩ : syracuseStep 2180189 = 817571) B817571
theorem B1721675 : Blo 678312 1721675 := bstep (se 1 (by rfl) ⟨1291256, by rfl⟩ : syracuseStep 1721675 = 2582513) B2582513
theorem B968203 : Blo 678312 968203 := bstep (se 1 (by rfl) ⟨726152, by rfl⟩ : syracuseStep 968203 = 1452305) B1452305
theorem B968215 : Blo 678312 968215 := bstep (se 1 (by rfl) ⟨726161, by rfl⟩ : syracuseStep 968215 = 1452323) B1452323
theorem B3688001 : Blo 678312 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B1492619 : Blo 678312 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B8276003 : Blo 678312 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B2902081 : Blo 678312 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B6539525 : Blo 678312 6539525 := bstep (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) B1226161
theorem B1722647 : Blo 678312 1722647 := bstep (se 1 (by rfl) ⟨1291985, by rfl⟩ : syracuseStep 1722647 = 2583971) B2583971
theorem B1526219 : Blo 678312 1526219 := bstep (se 1 (by rfl) ⟨1144664, by rfl⟩ : syracuseStep 1526219 = 2289329) B2289329
theorem B1526273 : Blo 678312 1526273 := bstep (se 2 (by rfl) ⟨572352, by rfl⟩ : syracuseStep 1526273 = 1144705) B1144705
theorem B1526489 : Blo 678312 1526489 := bstep (se 2 (by rfl) ⟨572433, by rfl⟩ : syracuseStep 1526489 = 1144867) B1144867
theorem B1526579 : Blo 678312 1526579 := bstep (se 1 (by rfl) ⟨1144934, by rfl⟩ : syracuseStep 1526579 = 2289869) B2289869
theorem B1526615 : Blo 678312 1526615 := bstep (se 1 (by rfl) ⟨1144961, by rfl⟩ : syracuseStep 1526615 = 2289923) B2289923
theorem B1723315 : Blo 678312 1723315 := bstep (se 1 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 1723315 = 2584973) B2584973
theorem B13093811 : Blo 678312 13093811 := bstep (se 1 (by rfl) ⟨9820358, by rfl⟩ : syracuseStep 13093811 = 19640717) B19640717
theorem B805847 : Blo 678312 805847 := bstep (se 1 (by rfl) ⟨604385, by rfl⟩ : syracuseStep 805847 = 1208771) B1208771
theorem B1526795 : Blo 678312 1526795 := bstep (se 1 (by rfl) ⟨1145096, by rfl⟩ : syracuseStep 1526795 = 2290193) B2290193
theorem B1526849 : Blo 678312 1526849 := bstep (se 2 (by rfl) ⟨572568, by rfl⟩ : syracuseStep 1526849 = 1145137) B1145137
theorem B1723457 : Blo 678312 1723457 := bstep (se 2 (by rfl) ⟨646296, by rfl⟩ : syracuseStep 1723457 = 1292593) B1292593
theorem B3493081 : Blo 678312 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1527065 : Blo 678312 1527065 := bstep (se 2 (by rfl) ⟨572649, by rfl⟩ : syracuseStep 1527065 = 1145299) B1145299
theorem B5295395 : Blo 678312 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B2575709 : Blo 678312 2575709 := bstep (se 3 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 2575709 = 965891) B965891
theorem B1527155 : Blo 678312 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B1527191 : Blo 678312 1527191 := bstep (se 1 (by rfl) ⟨1145393, by rfl⟩ : syracuseStep 1527191 = 2290787) B2290787
theorem B970265 : Blo 678312 970265 := bstep (se 2 (by rfl) ⟨363849, by rfl⟩ : syracuseStep 970265 = 727699) B727699
theorem B1527371 : Blo 678312 1527371 := bstep (se 1 (by rfl) ⟨1145528, by rfl⟩ : syracuseStep 1527371 = 2291057) B2291057
theorem B1527425 : Blo 678312 1527425 := bstep (se 2 (by rfl) ⟨572784, by rfl⟩ : syracuseStep 1527425 = 1145569) B1145569
theorem B5164721 : Blo 678312 5164721 := bstep (se 2 (by rfl) ⟨1936770, by rfl⟩ : syracuseStep 5164721 = 3873541) B3873541
theorem B1527641 : Blo 678312 1527641 := bstep (se 2 (by rfl) ⟨572865, by rfl⟩ : syracuseStep 1527641 = 1145731) B1145731
theorem B1527731 : Blo 678312 1527731 := bstep (se 1 (by rfl) ⟨1145798, by rfl⟩ : syracuseStep 1527731 = 2291597) B2291597
theorem B1527767 : Blo 678312 1527767 := bstep (se 1 (by rfl) ⟨1145825, by rfl⟩ : syracuseStep 1527767 = 2291651) B2291651
theorem B2576407 : Blo 678312 2576407 := bstep (se 1 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 2576407 = 3864611) B3864611
theorem B1527947 : Blo 678312 1527947 := bstep (se 1 (by rfl) ⟨1145960, by rfl⟩ : syracuseStep 1527947 = 2291921) B2291921
theorem B5165207 : Blo 678312 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B970903 : Blo 678312 970903 := bstep (se 1 (by rfl) ⟨728177, by rfl⟩ : syracuseStep 970903 = 1456355) B1456355
theorem B1528001 : Blo 678312 1528001 := bstep (se 2 (by rfl) ⟨573000, by rfl⟩ : syracuseStep 1528001 = 1146001) B1146001
theorem B2937035 : Blo 678312 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B22335749 : Blo 678312 22335749 := bstep (se 4 (by rfl) ⟨2093976, by rfl⟩ : syracuseStep 22335749 = 4187953) B4187953
theorem B1724723 : Blo 678312 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B8278337 : Blo 678312 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B1528217 : Blo 678312 1528217 := bstep (se 2 (by rfl) ⟨573081, by rfl⟩ : syracuseStep 1528217 = 1146163) B1146163
theorem B1528307 : Blo 678312 1528307 := bstep (se 1 (by rfl) ⟨1146230, by rfl⟩ : syracuseStep 1528307 = 2292461) B2292461
theorem B1528343 : Blo 678312 1528343 := bstep (se 1 (by rfl) ⟨1146257, by rfl⟩ : syracuseStep 1528343 = 2292515) B2292515
theorem B1528523 : Blo 678312 1528523 := bstep (se 1 (by rfl) ⟨1146392, by rfl⟩ : syracuseStep 1528523 = 2292785) B2292785
theorem B1528577 : Blo 678312 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B2577197 : Blo 678312 2577197 := bstep (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) B966449
theorem B1725259 : Blo 678312 1725259 := bstep (se 1 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 1725259 = 2587889) B2587889
theorem B1528793 : Blo 678312 1528793 := bstep (se 2 (by rfl) ⟨573297, by rfl⟩ : syracuseStep 1528793 = 1146595) B1146595
theorem B1725401 : Blo 678312 1725401 := bstep (se 2 (by rfl) ⟨647025, by rfl⟩ : syracuseStep 1725401 = 1294051) B1294051
theorem B1037323 : Blo 678312 1037323 := bstep (se 1 (by rfl) ⟨777992, by rfl⟩ : syracuseStep 1037323 = 1555985) B1555985
theorem B1528883 : Blo 678312 1528883 := bstep (se 1 (by rfl) ⟨1146662, by rfl⟩ : syracuseStep 1528883 = 2293325) B2293325
theorem B1528919 : Blo 678312 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B3265687 : Blo 678312 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B1529099 : Blo 678312 1529099 := bstep (se 1 (by rfl) ⟨1146824, by rfl⟩ : syracuseStep 1529099 = 2293649) B2293649
theorem B1529153 : Blo 678312 1529153 := bstep (se 2 (by rfl) ⟨573432, by rfl⟩ : syracuseStep 1529153 = 1146865) B1146865
theorem B1529369 : Blo 678312 1529369 := bstep (se 2 (by rfl) ⟨573513, by rfl⟩ : syracuseStep 1529369 = 1147027) B1147027
theorem B1529459 : Blo 678312 1529459 := bstep (se 1 (by rfl) ⟨1147094, by rfl⟩ : syracuseStep 1529459 = 2294189) B2294189
theorem B1529495 : Blo 678312 1529495 := bstep (se 1 (by rfl) ⟨1147121, by rfl⟩ : syracuseStep 1529495 = 2294243) B2294243
theorem B4347665 : Blo 678312 4347665 := bstep (se 2 (by rfl) ⟨1630374, by rfl⟩ : syracuseStep 4347665 = 3260749) B3260749
theorem B1726231 : Blo 678312 1726231 := bstep (se 1 (by rfl) ⟨1294673, by rfl⟩ : syracuseStep 1726231 = 2589347) B2589347
theorem B1529675 : Blo 678312 1529675 := bstep (se 1 (by rfl) ⟨1147256, by rfl⟩ : syracuseStep 1529675 = 2294513) B2294513
theorem B1529729 : Blo 678312 1529729 := bstep (se 2 (by rfl) ⟨573648, by rfl⟩ : syracuseStep 1529729 = 1147297) B1147297
theorem B1529945 : Blo 678312 1529945 := bstep (se 2 (by rfl) ⟨573729, by rfl⟩ : syracuseStep 1529945 = 1147459) B1147459
theorem B1530035 : Blo 678312 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B2578625 : Blo 678312 2578625 := bstep (se 2 (by rfl) ⟨966984, by rfl⟩ : syracuseStep 2578625 = 1933969) B1933969
theorem B1726667 : Blo 678312 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1530071 : Blo 678312 1530071 := bstep (se 1 (by rfl) ⟨1147553, by rfl⟩ : syracuseStep 1530071 = 2295107) B2295107
theorem B1530251 : Blo 678312 1530251 := bstep (se 1 (by rfl) ⟨1147688, by rfl⟩ : syracuseStep 1530251 = 2295377) B2295377
theorem B678315 : Blo 678312 678315 := bstep (se 1 (by rfl) ⟨508736, by rfl⟩ : syracuseStep 678315 = 1017473) B1017473
theorem B678327 : Blo 678312 678327 := bstep (se 1 (by rfl) ⟨508745, by rfl⟩ : syracuseStep 678327 = 1017491) B1017491
theorem B1530305 : Blo 678312 1530305 := bstep (se 2 (by rfl) ⟨573864, by rfl⟩ : syracuseStep 1530305 = 1147729) B1147729
theorem B678347 : Blo 678312 678347 := bstep (se 1 (by rfl) ⟨508760, by rfl⟩ : syracuseStep 678347 = 1017521) B1017521
theorem B678359 : Blo 678312 678359 := bstep (se 1 (by rfl) ⟨508769, by rfl⟩ : syracuseStep 678359 = 1017539) B1017539
theorem B678379 : Blo 678312 678379 := bstep (se 1 (by rfl) ⟨508784, by rfl⟩ : syracuseStep 678379 = 1017569) B1017569
theorem B678391 : Blo 678312 678391 := bstep (se 1 (by rfl) ⟨508793, by rfl⟩ : syracuseStep 678391 = 1017587) B1017587
theorem B678411 : Blo 678312 678411 := bstep (se 1 (by rfl) ⟨508808, by rfl⟩ : syracuseStep 678411 = 1017617) B1017617
theorem B678423 : Blo 678312 678423 := bstep (se 1 (by rfl) ⟨508817, by rfl⟩ : syracuseStep 678423 = 1017635) B1017635
theorem B678443 : Blo 678312 678443 := bstep (se 1 (by rfl) ⟨508832, by rfl⟩ : syracuseStep 678443 = 1017665) B1017665
theorem B678455 : Blo 678312 678455 := bstep (se 1 (by rfl) ⟨508841, by rfl⟩ : syracuseStep 678455 = 1017683) B1017683
theorem B1727041 : Blo 678312 1727041 := bstep (se 2 (by rfl) ⟨647640, by rfl⟩ : syracuseStep 1727041 = 1295281) B1295281
theorem B678475 : Blo 678312 678475 := bstep (se 1 (by rfl) ⟨508856, by rfl⟩ : syracuseStep 678475 = 1017713) B1017713
theorem B678487 : Blo 678312 678487 := bstep (se 1 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 678487 = 1017731) B1017731
theorem B678507 : Blo 678312 678507 := bstep (se 1 (by rfl) ⟨508880, by rfl⟩ : syracuseStep 678507 = 1017761) B1017761
theorem B678519 : Blo 678312 678519 := bstep (se 1 (by rfl) ⟨508889, by rfl⟩ : syracuseStep 678519 = 1017779) B1017779
theorem B678539 : Blo 678312 678539 := bstep (se 1 (by rfl) ⟨508904, by rfl⟩ : syracuseStep 678539 = 1017809) B1017809
theorem B678551 : Blo 678312 678551 := bstep (se 1 (by rfl) ⟨508913, by rfl⟩ : syracuseStep 678551 = 1017827) B1017827
theorem B1530521 : Blo 678312 1530521 := bstep (se 2 (by rfl) ⟨573945, by rfl⟩ : syracuseStep 1530521 = 1147891) B1147891
theorem B678571 : Blo 678312 678571 := bstep (se 1 (by rfl) ⟨508928, by rfl⟩ : syracuseStep 678571 = 1017857) B1017857
theorem B678583 : Blo 678312 678583 := bstep (se 1 (by rfl) ⟨508937, by rfl⟩ : syracuseStep 678583 = 1017875) B1017875
theorem B678603 : Blo 678312 678603 := bstep (se 1 (by rfl) ⟨508952, by rfl⟩ : syracuseStep 678603 = 1017905) B1017905
theorem B678615 : Blo 678312 678615 := bstep (se 1 (by rfl) ⟨508961, by rfl⟩ : syracuseStep 678615 = 1017923) B1017923
theorem B678635 : Blo 678312 678635 := bstep (se 1 (by rfl) ⟨508976, by rfl⟩ : syracuseStep 678635 = 1017953) B1017953
theorem B1530611 : Blo 678312 1530611 := bstep (se 1 (by rfl) ⟨1147958, by rfl⟩ : syracuseStep 1530611 = 2295917) B2295917
theorem B678647 : Blo 678312 678647 := bstep (se 1 (by rfl) ⟨508985, by rfl⟩ : syracuseStep 678647 = 1017971) B1017971
theorem B678667 : Blo 678312 678667 := bstep (se 1 (by rfl) ⟨509000, by rfl⟩ : syracuseStep 678667 = 1018001) B1018001
theorem B678679 : Blo 678312 678679 := bstep (se 1 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 678679 = 1018019) B1018019
theorem B1530647 : Blo 678312 1530647 := bstep (se 1 (by rfl) ⟨1147985, by rfl⟩ : syracuseStep 1530647 = 2295971) B2295971
theorem B678699 : Blo 678312 678699 := bstep (se 1 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 678699 = 1018049) B1018049
theorem B678711 : Blo 678312 678711 := bstep (se 1 (by rfl) ⟨509033, by rfl⟩ : syracuseStep 678711 = 1018067) B1018067
theorem B678731 : Blo 678312 678731 := bstep (se 1 (by rfl) ⟨509048, by rfl⟩ : syracuseStep 678731 = 1018097) B1018097
theorem B4414283 : Blo 678312 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B678743 : Blo 678312 678743 := bstep (se 1 (by rfl) ⟨509057, by rfl⟩ : syracuseStep 678743 = 1018115) B1018115
theorem B678763 : Blo 678312 678763 := bstep (se 1 (by rfl) ⟨509072, by rfl⟩ : syracuseStep 678763 = 1018145) B1018145
theorem B678775 : Blo 678312 678775 := bstep (se 1 (by rfl) ⟨509081, by rfl⟩ : syracuseStep 678775 = 1018163) B1018163
theorem B678795 : Blo 678312 678795 := bstep (se 1 (by rfl) ⟨509096, by rfl⟩ : syracuseStep 678795 = 1018193) B1018193
theorem B678807 : Blo 678312 678807 := bstep (se 1 (by rfl) ⟨509105, by rfl⟩ : syracuseStep 678807 = 1018211) B1018211
theorem B678827 : Blo 678312 678827 := bstep (se 1 (by rfl) ⟨509120, by rfl⟩ : syracuseStep 678827 = 1018241) B1018241
theorem B13065137 : Blo 678312 13065137 := bstep (se 2 (by rfl) ⟨4899426, by rfl⟩ : syracuseStep 13065137 = 9798853) B9798853
theorem B678839 : Blo 678312 678839 := bstep (se 1 (by rfl) ⟨509129, by rfl⟩ : syracuseStep 678839 = 1018259) B1018259
theorem B678859 : Blo 678312 678859 := bstep (se 1 (by rfl) ⟨509144, by rfl⟩ : syracuseStep 678859 = 1018289) B1018289
theorem B1530827 : Blo 678312 1530827 := bstep (se 1 (by rfl) ⟨1148120, by rfl⟩ : syracuseStep 1530827 = 2296241) B2296241
theorem B678871 : Blo 678312 678871 := bstep (se 1 (by rfl) ⟨509153, by rfl⟩ : syracuseStep 678871 = 1018307) B1018307
theorem B678891 : Blo 678312 678891 := bstep (se 1 (by rfl) ⟨509168, by rfl⟩ : syracuseStep 678891 = 1018337) B1018337
theorem B678903 : Blo 678312 678903 := bstep (se 1 (by rfl) ⟨509177, by rfl⟩ : syracuseStep 678903 = 1018355) B1018355
theorem B1530881 : Blo 678312 1530881 := bstep (se 2 (by rfl) ⟨574080, by rfl⟩ : syracuseStep 1530881 = 1148161) B1148161
theorem B678923 : Blo 678312 678923 := bstep (se 1 (by rfl) ⟨509192, by rfl⟩ : syracuseStep 678923 = 1018385) B1018385
theorem B678935 : Blo 678312 678935 := bstep (se 1 (by rfl) ⟨509201, by rfl⟩ : syracuseStep 678935 = 1018403) B1018403
theorem B678955 : Blo 678312 678955 := bstep (se 1 (by rfl) ⟨509216, by rfl⟩ : syracuseStep 678955 = 1018433) B1018433
theorem B5233709 : Blo 678312 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B678967 : Blo 678312 678967 := bstep (se 1 (by rfl) ⟨509225, by rfl⟩ : syracuseStep 678967 = 1018451) B1018451
theorem B678987 : Blo 678312 678987 := bstep (se 1 (by rfl) ⟨509240, by rfl⟩ : syracuseStep 678987 = 1018481) B1018481
theorem B678999 : Blo 678312 678999 := bstep (se 1 (by rfl) ⟨509249, by rfl⟩ : syracuseStep 678999 = 1018499) B1018499
theorem B679019 : Blo 678312 679019 := bstep (se 1 (by rfl) ⟨509264, by rfl⟩ : syracuseStep 679019 = 1018529) B1018529
theorem B679031 : Blo 678312 679031 := bstep (se 1 (by rfl) ⟨509273, by rfl⟩ : syracuseStep 679031 = 1018547) B1018547
theorem B679051 : Blo 678312 679051 := bstep (se 1 (by rfl) ⟨509288, by rfl⟩ : syracuseStep 679051 = 1018577) B1018577
theorem B679063 : Blo 678312 679063 := bstep (se 1 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 679063 = 1018595) B1018595
theorem B679083 : Blo 678312 679083 := bstep (se 1 (by rfl) ⟨509312, by rfl⟩ : syracuseStep 679083 = 1018625) B1018625
theorem B679095 : Blo 678312 679095 := bstep (se 1 (by rfl) ⟨509321, by rfl⟩ : syracuseStep 679095 = 1018643) B1018643
theorem B679115 : Blo 678312 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B679127 : Blo 678312 679127 := bstep (se 1 (by rfl) ⟨509345, by rfl⟩ : syracuseStep 679127 = 1018691) B1018691
theorem B1531097 : Blo 678312 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B679147 : Blo 678312 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B679159 : Blo 678312 679159 := bstep (se 1 (by rfl) ⟨509369, by rfl⟩ : syracuseStep 679159 = 1018739) B1018739
theorem B679179 : Blo 678312 679179 := bstep (se 1 (by rfl) ⟨509384, by rfl⟩ : syracuseStep 679179 = 1018769) B1018769
theorem B679191 : Blo 678312 679191 := bstep (se 1 (by rfl) ⟨509393, by rfl⟩ : syracuseStep 679191 = 1018787) B1018787
theorem B679211 : Blo 678312 679211 := bstep (se 1 (by rfl) ⟨509408, by rfl⟩ : syracuseStep 679211 = 1018817) B1018817
theorem B1531187 : Blo 678312 1531187 := bstep (se 1 (by rfl) ⟨1148390, by rfl⟩ : syracuseStep 1531187 = 2296781) B2296781
theorem B679223 : Blo 678312 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B679243 : Blo 678312 679243 := bstep (se 1 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 679243 = 1018865) B1018865
theorem B679255 : Blo 678312 679255 := bstep (se 1 (by rfl) ⟨509441, by rfl⟩ : syracuseStep 679255 = 1018883) B1018883
theorem B1531223 : Blo 678312 1531223 := bstep (se 1 (by rfl) ⟨1148417, by rfl⟩ : syracuseStep 1531223 = 2296835) B2296835
theorem B5823845 : Blo 678312 5823845 := bstep (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) B1091971
theorem B679275 : Blo 678312 679275 := bstep (se 1 (by rfl) ⟨509456, by rfl⟩ : syracuseStep 679275 = 1018913) B1018913
theorem B679287 : Blo 678312 679287 := bstep (se 1 (by rfl) ⟨509465, by rfl⟩ : syracuseStep 679287 = 1018931) B1018931
theorem B679307 : Blo 678312 679307 := bstep (se 1 (by rfl) ⟨509480, by rfl⟩ : syracuseStep 679307 = 1018961) B1018961
theorem B679319 : Blo 678312 679319 := bstep (se 1 (by rfl) ⟨509489, by rfl⟩ : syracuseStep 679319 = 1018979) B1018979
theorem B679339 : Blo 678312 679339 := bstep (se 1 (by rfl) ⟨509504, by rfl⟩ : syracuseStep 679339 = 1019009) B1019009
theorem B679351 : Blo 678312 679351 := bstep (se 1 (by rfl) ⟨509513, by rfl⟩ : syracuseStep 679351 = 1019027) B1019027
theorem B679371 : Blo 678312 679371 := bstep (se 1 (by rfl) ⟨509528, by rfl⟩ : syracuseStep 679371 = 1019057) B1019057
theorem B679383 : Blo 678312 679383 := bstep (se 1 (by rfl) ⟨509537, by rfl⟩ : syracuseStep 679383 = 1019075) B1019075
theorem B679403 : Blo 678312 679403 := bstep (se 1 (by rfl) ⟨509552, by rfl⟩ : syracuseStep 679403 = 1019105) B1019105
theorem B679415 : Blo 678312 679415 := bstep (se 1 (by rfl) ⟨509561, by rfl⟩ : syracuseStep 679415 = 1019123) B1019123
theorem B679435 : Blo 678312 679435 := bstep (se 1 (by rfl) ⟨509576, by rfl⟩ : syracuseStep 679435 = 1019153) B1019153
theorem B1531403 : Blo 678312 1531403 := bstep (se 1 (by rfl) ⟨1148552, by rfl⟩ : syracuseStep 1531403 = 2297105) B2297105
theorem B679447 : Blo 678312 679447 := bstep (se 1 (by rfl) ⟨509585, by rfl⟩ : syracuseStep 679447 = 1019171) B1019171
theorem B679467 : Blo 678312 679467 := bstep (se 1 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 679467 = 1019201) B1019201
theorem B679479 : Blo 678312 679479 := bstep (se 1 (by rfl) ⟨509609, by rfl⟩ : syracuseStep 679479 = 1019219) B1019219
theorem B1531457 : Blo 678312 1531457 := bstep (se 2 (by rfl) ⟨574296, by rfl⟩ : syracuseStep 1531457 = 1148593) B1148593
theorem B679499 : Blo 678312 679499 := bstep (se 1 (by rfl) ⟨509624, by rfl⟩ : syracuseStep 679499 = 1019249) B1019249
theorem B679511 : Blo 678312 679511 := bstep (se 1 (by rfl) ⟨509633, by rfl⟩ : syracuseStep 679511 = 1019267) B1019267
theorem B4349533 : Blo 678312 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B679531 : Blo 678312 679531 := bstep (se 1 (by rfl) ⟨509648, by rfl⟩ : syracuseStep 679531 = 1019297) B1019297
theorem B679543 : Blo 678312 679543 := bstep (se 1 (by rfl) ⟨509657, by rfl⟩ : syracuseStep 679543 = 1019315) B1019315
theorem B679563 : Blo 678312 679563 := bstep (se 1 (by rfl) ⟨509672, by rfl⟩ : syracuseStep 679563 = 1019345) B1019345
theorem B2580113 : Blo 678312 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B679575 : Blo 678312 679575 := bstep (se 1 (by rfl) ⟨509681, by rfl⟩ : syracuseStep 679575 = 1019363) B1019363
theorem B679595 : Blo 678312 679595 := bstep (se 1 (by rfl) ⟨509696, by rfl⟩ : syracuseStep 679595 = 1019393) B1019393
theorem B679607 : Blo 678312 679607 := bstep (se 1 (by rfl) ⟨509705, by rfl⟩ : syracuseStep 679607 = 1019411) B1019411
theorem B679627 : Blo 678312 679627 := bstep (se 1 (by rfl) ⟨509720, by rfl⟩ : syracuseStep 679627 = 1019441) B1019441
theorem B679639 : Blo 678312 679639 := bstep (se 1 (by rfl) ⟨509729, by rfl⟩ : syracuseStep 679639 = 1019459) B1019459
theorem B679659 : Blo 678312 679659 := bstep (se 1 (by rfl) ⟨509744, by rfl⟩ : syracuseStep 679659 = 1019489) B1019489
theorem B679671 : Blo 678312 679671 := bstep (se 1 (by rfl) ⟨509753, by rfl⟩ : syracuseStep 679671 = 1019507) B1019507
theorem B679691 : Blo 678312 679691 := bstep (se 1 (by rfl) ⟨509768, by rfl⟩ : syracuseStep 679691 = 1019537) B1019537
theorem B679703 : Blo 678312 679703 := bstep (se 1 (by rfl) ⟨509777, by rfl⟩ : syracuseStep 679703 = 1019555) B1019555
theorem B1531673 : Blo 678312 1531673 := bstep (se 2 (by rfl) ⟨574377, by rfl⟩ : syracuseStep 1531673 = 1148755) B1148755
theorem B679723 : Blo 678312 679723 := bstep (se 1 (by rfl) ⟨509792, by rfl⟩ : syracuseStep 679723 = 1019585) B1019585
theorem B679735 : Blo 678312 679735 := bstep (se 1 (by rfl) ⟨509801, by rfl⟩ : syracuseStep 679735 = 1019603) B1019603
theorem B679755 : Blo 678312 679755 := bstep (se 1 (by rfl) ⟨509816, by rfl⟩ : syracuseStep 679755 = 1019633) B1019633
theorem B679767 : Blo 678312 679767 := bstep (se 1 (by rfl) ⟨509825, by rfl⟩ : syracuseStep 679767 = 1019651) B1019651
theorem B679787 : Blo 678312 679787 := bstep (se 1 (by rfl) ⟨509840, by rfl⟩ : syracuseStep 679787 = 1019681) B1019681
theorem B1531763 : Blo 678312 1531763 := bstep (se 1 (by rfl) ⟨1148822, by rfl⟩ : syracuseStep 1531763 = 2297645) B2297645
theorem B679799 : Blo 678312 679799 := bstep (se 1 (by rfl) ⟨509849, by rfl⟩ : syracuseStep 679799 = 1019699) B1019699
theorem B679819 : Blo 678312 679819 := bstep (se 1 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 679819 = 1019729) B1019729
theorem B679831 : Blo 678312 679831 := bstep (se 1 (by rfl) ⟨509873, by rfl⟩ : syracuseStep 679831 = 1019747) B1019747
theorem B1531799 : Blo 678312 1531799 := bstep (se 1 (by rfl) ⟨1148849, by rfl⟩ : syracuseStep 1531799 = 2297699) B2297699
theorem B679851 : Blo 678312 679851 := bstep (se 1 (by rfl) ⟨509888, by rfl⟩ : syracuseStep 679851 = 1019777) B1019777
theorem B33611699 : Blo 678312 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B679863 : Blo 678312 679863 := bstep (se 1 (by rfl) ⟨509897, by rfl⟩ : syracuseStep 679863 = 1019795) B1019795
theorem B679883 : Blo 678312 679883 := bstep (se 1 (by rfl) ⟨509912, by rfl⟩ : syracuseStep 679883 = 1019825) B1019825
theorem B679895 : Blo 678312 679895 := bstep (se 1 (by rfl) ⟨509921, by rfl⟩ : syracuseStep 679895 = 1019843) B1019843
theorem B679915 : Blo 678312 679915 := bstep (se 1 (by rfl) ⟨509936, by rfl⟩ : syracuseStep 679915 = 1019873) B1019873
theorem B679927 : Blo 678312 679927 := bstep (se 1 (by rfl) ⟨509945, by rfl⟩ : syracuseStep 679927 = 1019891) B1019891
theorem B2908163 : Blo 678312 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B679947 : Blo 678312 679947 := bstep (se 1 (by rfl) ⟨509960, by rfl⟩ : syracuseStep 679947 = 1019921) B1019921
theorem B679959 : Blo 678312 679959 := bstep (se 1 (by rfl) ⟨509969, by rfl⟩ : syracuseStep 679959 = 1019939) B1019939
theorem B679979 : Blo 678312 679979 := bstep (se 1 (by rfl) ⟨509984, by rfl⟩ : syracuseStep 679979 = 1019969) B1019969
theorem B679991 : Blo 678312 679991 := bstep (se 1 (by rfl) ⟨509993, by rfl⟩ : syracuseStep 679991 = 1019987) B1019987
theorem B680011 : Blo 678312 680011 := bstep (se 1 (by rfl) ⟨510008, by rfl⟩ : syracuseStep 680011 = 1020017) B1020017
theorem B1531979 : Blo 678312 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B680023 : Blo 678312 680023 := bstep (se 1 (by rfl) ⟨510017, by rfl⟩ : syracuseStep 680023 = 1020035) B1020035
theorem B2580569 : Blo 678312 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B680043 : Blo 678312 680043 := bstep (se 1 (by rfl) ⟨510032, by rfl⟩ : syracuseStep 680043 = 1020065) B1020065
theorem B680055 : Blo 678312 680055 := bstep (se 1 (by rfl) ⟨510041, by rfl⟩ : syracuseStep 680055 = 1020083) B1020083
theorem B1532033 : Blo 678312 1532033 := bstep (se 2 (by rfl) ⟨574512, by rfl⟩ : syracuseStep 1532033 = 1149025) B1149025
theorem B680075 : Blo 678312 680075 := bstep (se 1 (by rfl) ⟨510056, by rfl⟩ : syracuseStep 680075 = 1020113) B1020113
theorem B680087 : Blo 678312 680087 := bstep (se 1 (by rfl) ⟨510065, by rfl⟩ : syracuseStep 680087 = 1020131) B1020131
theorem B680107 : Blo 678312 680107 := bstep (se 1 (by rfl) ⟨510080, by rfl⟩ : syracuseStep 680107 = 1020161) B1020161
theorem B680119 : Blo 678312 680119 := bstep (se 1 (by rfl) ⟨510089, by rfl⟩ : syracuseStep 680119 = 1020179) B1020179
theorem B2449601 : Blo 678312 2449601 := bstep (se 2 (by rfl) ⟨918600, by rfl⟩ : syracuseStep 2449601 = 1837201) B1837201
theorem B680139 : Blo 678312 680139 := bstep (se 1 (by rfl) ⟨510104, by rfl⟩ : syracuseStep 680139 = 1020209) B1020209
theorem B680151 : Blo 678312 680151 := bstep (se 1 (by rfl) ⟨510113, by rfl⟩ : syracuseStep 680151 = 1020227) B1020227
theorem B680171 : Blo 678312 680171 := bstep (se 1 (by rfl) ⟨510128, by rfl⟩ : syracuseStep 680171 = 1020257) B1020257
theorem B680183 : Blo 678312 680183 := bstep (se 1 (by rfl) ⟨510137, by rfl⟩ : syracuseStep 680183 = 1020275) B1020275
theorem B680203 : Blo 678312 680203 := bstep (se 1 (by rfl) ⟨510152, by rfl⟩ : syracuseStep 680203 = 1020305) B1020305
theorem B680215 : Blo 678312 680215 := bstep (se 1 (by rfl) ⟨510161, by rfl⟩ : syracuseStep 680215 = 1020323) B1020323
theorem B680235 : Blo 678312 680235 := bstep (se 1 (by rfl) ⟨510176, by rfl⟩ : syracuseStep 680235 = 1020353) B1020353
theorem B2580781 : Blo 678312 2580781 := bstep (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) B967793
theorem B680247 : Blo 678312 680247 := bstep (se 1 (by rfl) ⟨510185, by rfl⟩ : syracuseStep 680247 = 1020371) B1020371
theorem B680267 : Blo 678312 680267 := bstep (se 1 (by rfl) ⟨510200, by rfl⟩ : syracuseStep 680267 = 1020401) B1020401
theorem B680279 : Blo 678312 680279 := bstep (se 1 (by rfl) ⟨510209, by rfl⟩ : syracuseStep 680279 = 1020419) B1020419
theorem B1532249 : Blo 678312 1532249 := bstep (se 2 (by rfl) ⟨574593, by rfl⟩ : syracuseStep 1532249 = 1149187) B1149187
theorem B3268957 : Blo 678312 3268957 := bstep (se 3 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 3268957 = 1225859) B1225859
theorem B680299 : Blo 678312 680299 := bstep (se 1 (by rfl) ⟨510224, by rfl⟩ : syracuseStep 680299 = 1020449) B1020449
theorem B680311 : Blo 678312 680311 := bstep (se 1 (by rfl) ⟨510233, by rfl⟩ : syracuseStep 680311 = 1020467) B1020467
theorem B680331 : Blo 678312 680331 := bstep (se 1 (by rfl) ⟨510248, by rfl⟩ : syracuseStep 680331 = 1020497) B1020497
theorem B680343 : Blo 678312 680343 := bstep (se 1 (by rfl) ⟨510257, by rfl⟩ : syracuseStep 680343 = 1020515) B1020515
theorem B680363 : Blo 678312 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B1532339 : Blo 678312 1532339 := bstep (se 1 (by rfl) ⟨1149254, by rfl⟩ : syracuseStep 1532339 = 2298509) B2298509
theorem B680375 : Blo 678312 680375 := bstep (se 1 (by rfl) ⟨510281, by rfl⟩ : syracuseStep 680375 = 1020563) B1020563
theorem B680395 : Blo 678312 680395 := bstep (se 1 (by rfl) ⟨510296, by rfl⟩ : syracuseStep 680395 = 1020593) B1020593
theorem B680407 : Blo 678312 680407 := bstep (se 1 (by rfl) ⟨510305, by rfl⟩ : syracuseStep 680407 = 1020611) B1020611
theorem B1532375 : Blo 678312 1532375 := bstep (se 1 (by rfl) ⟨1149281, by rfl⟩ : syracuseStep 1532375 = 2298563) B2298563
theorem B680427 : Blo 678312 680427 := bstep (se 1 (by rfl) ⟨510320, by rfl⟩ : syracuseStep 680427 = 1020641) B1020641
theorem B680439 : Blo 678312 680439 := bstep (se 1 (by rfl) ⟨510329, by rfl⟩ : syracuseStep 680439 = 1020659) B1020659
theorem B680459 : Blo 678312 680459 := bstep (se 1 (by rfl) ⟨510344, by rfl⟩ : syracuseStep 680459 = 1020689) B1020689
theorem B16769549 : Blo 678312 16769549 := bstep (se 3 (by rfl) ⟨3144290, by rfl⟩ : syracuseStep 16769549 = 6288581) B6288581
theorem B680471 : Blo 678312 680471 := bstep (se 1 (by rfl) ⟨510353, by rfl⟩ : syracuseStep 680471 = 1020707) B1020707
theorem B680491 : Blo 678312 680491 := bstep (se 1 (by rfl) ⟨510368, by rfl⟩ : syracuseStep 680491 = 1020737) B1020737
theorem B680503 : Blo 678312 680503 := bstep (se 1 (by rfl) ⟨510377, by rfl⟩ : syracuseStep 680503 = 1020755) B1020755
theorem B680523 : Blo 678312 680523 := bstep (se 1 (by rfl) ⟨510392, by rfl⟩ : syracuseStep 680523 = 1020785) B1020785
theorem B680535 : Blo 678312 680535 := bstep (se 1 (by rfl) ⟨510401, by rfl⟩ : syracuseStep 680535 = 1020803) B1020803
theorem B2581085 : Blo 678312 2581085 := bstep (se 3 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 2581085 = 967907) B967907
theorem B680555 : Blo 678312 680555 := bstep (se 1 (by rfl) ⟨510416, by rfl⟩ : syracuseStep 680555 = 1020833) B1020833
theorem B680567 : Blo 678312 680567 := bstep (se 1 (by rfl) ⟨510425, by rfl⟩ : syracuseStep 680567 = 1020851) B1020851
theorem B680587 : Blo 678312 680587 := bstep (se 1 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 680587 = 1020881) B1020881
theorem B1532555 : Blo 678312 1532555 := bstep (se 1 (by rfl) ⟨1149416, by rfl⟩ : syracuseStep 1532555 = 2298833) B2298833
theorem B680599 : Blo 678312 680599 := bstep (se 1 (by rfl) ⟨510449, by rfl⟩ : syracuseStep 680599 = 1020899) B1020899
theorem B680619 : Blo 678312 680619 := bstep (se 1 (by rfl) ⟨510464, by rfl⟩ : syracuseStep 680619 = 1020929) B1020929
theorem B680631 : Blo 678312 680631 := bstep (se 1 (by rfl) ⟨510473, by rfl⟩ : syracuseStep 680631 = 1020947) B1020947
theorem B1532609 : Blo 678312 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B680651 : Blo 678312 680651 := bstep (se 1 (by rfl) ⟨510488, by rfl⟩ : syracuseStep 680651 = 1020977) B1020977
theorem B680663 : Blo 678312 680663 := bstep (se 1 (by rfl) ⟨510497, by rfl⟩ : syracuseStep 680663 = 1020995) B1020995
theorem B680683 : Blo 678312 680683 := bstep (se 1 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 680683 = 1021025) B1021025
theorem B680695 : Blo 678312 680695 := bstep (se 1 (by rfl) ⟨510521, by rfl⟩ : syracuseStep 680695 = 1021043) B1021043
theorem B680715 : Blo 678312 680715 := bstep (se 1 (by rfl) ⟨510536, by rfl⟩ : syracuseStep 680715 = 1021073) B1021073
theorem B680727 : Blo 678312 680727 := bstep (se 1 (by rfl) ⟨510545, by rfl⟩ : syracuseStep 680727 = 1021091) B1021091
theorem B680747 : Blo 678312 680747 := bstep (se 1 (by rfl) ⟨510560, by rfl⟩ : syracuseStep 680747 = 1021121) B1021121
theorem B680759 : Blo 678312 680759 := bstep (se 1 (by rfl) ⟨510569, by rfl⟩ : syracuseStep 680759 = 1021139) B1021139
theorem B680779 : Blo 678312 680779 := bstep (se 1 (by rfl) ⟨510584, by rfl⟩ : syracuseStep 680779 = 1021169) B1021169
theorem B680791 : Blo 678312 680791 := bstep (se 1 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 680791 = 1021187) B1021187
theorem B680811 : Blo 678312 680811 := bstep (se 1 (by rfl) ⟨510608, by rfl⟩ : syracuseStep 680811 = 1021217) B1021217
theorem B680823 : Blo 678312 680823 := bstep (se 1 (by rfl) ⟨510617, by rfl⟩ : syracuseStep 680823 = 1021235) B1021235
theorem B3367811 : Blo 678312 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B680843 : Blo 678312 680843 := bstep (se 1 (by rfl) ⟨510632, by rfl⟩ : syracuseStep 680843 = 1021265) B1021265
theorem B680855 : Blo 678312 680855 := bstep (se 1 (by rfl) ⟨510641, by rfl⟩ : syracuseStep 680855 = 1021283) B1021283
theorem B1532825 : Blo 678312 1532825 := bstep (se 2 (by rfl) ⟨574809, by rfl⟩ : syracuseStep 1532825 = 1149619) B1149619
theorem B680875 : Blo 678312 680875 := bstep (se 1 (by rfl) ⟨510656, by rfl⟩ : syracuseStep 680875 = 1021313) B1021313
theorem B680887 : Blo 678312 680887 := bstep (se 1 (by rfl) ⟨510665, by rfl⟩ : syracuseStep 680887 = 1021331) B1021331
theorem B680907 : Blo 678312 680907 := bstep (se 1 (by rfl) ⟨510680, by rfl⟩ : syracuseStep 680907 = 1021361) B1021361
theorem B680919 : Blo 678312 680919 := bstep (se 1 (by rfl) ⟨510689, by rfl⟩ : syracuseStep 680919 = 1021379) B1021379
theorem B680939 : Blo 678312 680939 := bstep (se 1 (by rfl) ⟨510704, by rfl⟩ : syracuseStep 680939 = 1021409) B1021409
theorem B1532915 : Blo 678312 1532915 := bstep (se 1 (by rfl) ⟨1149686, by rfl⟩ : syracuseStep 1532915 = 2299373) B2299373
theorem B680951 : Blo 678312 680951 := bstep (se 1 (by rfl) ⟨510713, by rfl⟩ : syracuseStep 680951 = 1021427) B1021427
theorem B680971 : Blo 678312 680971 := bstep (se 1 (by rfl) ⟨510728, by rfl⟩ : syracuseStep 680971 = 1021457) B1021457
theorem B680983 : Blo 678312 680983 := bstep (se 1 (by rfl) ⟨510737, by rfl⟩ : syracuseStep 680983 = 1021475) B1021475
theorem B1532951 : Blo 678312 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B681003 : Blo 678312 681003 := bstep (se 1 (by rfl) ⟨510752, by rfl⟩ : syracuseStep 681003 = 1021505) B1021505
theorem B681015 : Blo 678312 681015 := bstep (se 1 (by rfl) ⟨510761, by rfl⟩ : syracuseStep 681015 = 1021523) B1021523
theorem B1631297 : Blo 678312 1631297 := bstep (se 2 (by rfl) ⟨611736, by rfl⟩ : syracuseStep 1631297 = 1223473) B1223473
theorem B681035 : Blo 678312 681035 := bstep (se 1 (by rfl) ⟨510776, by rfl⟩ : syracuseStep 681035 = 1021553) B1021553
theorem B681047 : Blo 678312 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B681067 : Blo 678312 681067 := bstep (se 1 (by rfl) ⟨510800, by rfl⟩ : syracuseStep 681067 = 1021601) B1021601
theorem B681079 : Blo 678312 681079 := bstep (se 1 (by rfl) ⟨510809, by rfl⟩ : syracuseStep 681079 = 1021619) B1021619
theorem B681099 : Blo 678312 681099 := bstep (se 1 (by rfl) ⟨510824, by rfl⟩ : syracuseStep 681099 = 1021649) B1021649
theorem B681111 : Blo 678312 681111 := bstep (se 1 (by rfl) ⟨510833, by rfl⟩ : syracuseStep 681111 = 1021667) B1021667
theorem B681131 : Blo 678312 681131 := bstep (se 1 (by rfl) ⟨510848, by rfl⟩ : syracuseStep 681131 = 1021697) B1021697
theorem B681143 : Blo 678312 681143 := bstep (se 1 (by rfl) ⟨510857, by rfl⟩ : syracuseStep 681143 = 1021715) B1021715
theorem B3105985 : Blo 678312 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B681163 : Blo 678312 681163 := bstep (se 1 (by rfl) ⟨510872, by rfl⟩ : syracuseStep 681163 = 1021745) B1021745
theorem B1533131 : Blo 678312 1533131 := bstep (se 1 (by rfl) ⟨1149848, by rfl⟩ : syracuseStep 1533131 = 2299697) B2299697
theorem B681175 : Blo 678312 681175 := bstep (se 1 (by rfl) ⟨510881, by rfl⟩ : syracuseStep 681175 = 1021763) B1021763
theorem B681195 : Blo 678312 681195 := bstep (se 1 (by rfl) ⟨510896, by rfl⟩ : syracuseStep 681195 = 1021793) B1021793
theorem B681207 : Blo 678312 681207 := bstep (se 1 (by rfl) ⟨510905, by rfl⟩ : syracuseStep 681207 = 1021811) B1021811
theorem B1533185 : Blo 678312 1533185 := bstep (se 2 (by rfl) ⟨574944, by rfl⟩ : syracuseStep 1533185 = 1149889) B1149889
theorem B681227 : Blo 678312 681227 := bstep (se 1 (by rfl) ⟨510920, by rfl⟩ : syracuseStep 681227 = 1021841) B1021841
theorem B681239 : Blo 678312 681239 := bstep (se 1 (by rfl) ⟨510929, by rfl⟩ : syracuseStep 681239 = 1021859) B1021859
theorem B681259 : Blo 678312 681259 := bstep (se 1 (by rfl) ⟨510944, by rfl⟩ : syracuseStep 681259 = 1021889) B1021889
theorem B681271 : Blo 678312 681271 := bstep (se 1 (by rfl) ⟨510953, by rfl⟩ : syracuseStep 681271 = 1021907) B1021907
theorem B681291 : Blo 678312 681291 := bstep (se 1 (by rfl) ⟨510968, by rfl⟩ : syracuseStep 681291 = 1021937) B1021937
theorem B681303 : Blo 678312 681303 := bstep (se 1 (by rfl) ⟨510977, by rfl⟩ : syracuseStep 681303 = 1021955) B1021955
theorem B681323 : Blo 678312 681323 := bstep (se 1 (by rfl) ⟨510992, by rfl⟩ : syracuseStep 681323 = 1021985) B1021985
theorem B681335 : Blo 678312 681335 := bstep (se 1 (by rfl) ⟨511001, by rfl⟩ : syracuseStep 681335 = 1022003) B1022003
theorem B681355 : Blo 678312 681355 := bstep (se 1 (by rfl) ⟨511016, by rfl⟩ : syracuseStep 681355 = 1022033) B1022033
theorem B681367 : Blo 678312 681367 := bstep (se 1 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 681367 = 1022051) B1022051
theorem B681387 : Blo 678312 681387 := bstep (se 1 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 681387 = 1022081) B1022081
theorem B681399 : Blo 678312 681399 := bstep (se 1 (by rfl) ⟨511049, by rfl⟩ : syracuseStep 681399 = 1022099) B1022099
theorem B681419 : Blo 678312 681419 := bstep (se 1 (by rfl) ⟨511064, by rfl⟩ : syracuseStep 681419 = 1022129) B1022129
theorem B681431 : Blo 678312 681431 := bstep (se 1 (by rfl) ⟨511073, by rfl⟩ : syracuseStep 681431 = 1022147) B1022147
theorem B1533401 : Blo 678312 1533401 := bstep (se 2 (by rfl) ⟨575025, by rfl⟩ : syracuseStep 1533401 = 1150051) B1150051
theorem B681451 : Blo 678312 681451 := bstep (se 1 (by rfl) ⟨511088, by rfl⟩ : syracuseStep 681451 = 1022177) B1022177
theorem B681463 : Blo 678312 681463 := bstep (se 1 (by rfl) ⟨511097, by rfl⟩ : syracuseStep 681463 = 1022195) B1022195
theorem B681483 : Blo 678312 681483 := bstep (se 1 (by rfl) ⟨511112, by rfl⟩ : syracuseStep 681483 = 1022225) B1022225
theorem B681495 : Blo 678312 681495 := bstep (se 1 (by rfl) ⟨511121, by rfl⟩ : syracuseStep 681495 = 1022243) B1022243
theorem B681515 : Blo 678312 681515 := bstep (se 1 (by rfl) ⟨511136, by rfl⟩ : syracuseStep 681515 = 1022273) B1022273
theorem B1533491 : Blo 678312 1533491 := bstep (se 1 (by rfl) ⟨1150118, by rfl⟩ : syracuseStep 1533491 = 2300237) B2300237
theorem B681527 : Blo 678312 681527 := bstep (se 1 (by rfl) ⟨511145, by rfl⟩ : syracuseStep 681527 = 1022291) B1022291
theorem B681547 : Blo 678312 681547 := bstep (se 1 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 681547 = 1022321) B1022321
theorem B681559 : Blo 678312 681559 := bstep (se 1 (by rfl) ⟨511169, by rfl⟩ : syracuseStep 681559 = 1022339) B1022339
theorem B1533527 : Blo 678312 1533527 := bstep (se 1 (by rfl) ⟨1150145, by rfl⟩ : syracuseStep 1533527 = 2300291) B2300291
theorem B2909789 : Blo 678312 2909789 := bstep (se 3 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 2909789 = 1091171) B1091171
theorem B681579 : Blo 678312 681579 := bstep (se 1 (by rfl) ⟨511184, by rfl⟩ : syracuseStep 681579 = 1022369) B1022369
theorem B681591 : Blo 678312 681591 := bstep (se 1 (by rfl) ⟨511193, by rfl⟩ : syracuseStep 681591 = 1022387) B1022387
theorem B681611 : Blo 678312 681611 := bstep (se 1 (by rfl) ⟨511208, by rfl⟩ : syracuseStep 681611 = 1022417) B1022417
theorem B681623 : Blo 678312 681623 := bstep (se 1 (by rfl) ⟨511217, by rfl⟩ : syracuseStep 681623 = 1022435) B1022435
theorem B681643 : Blo 678312 681643 := bstep (se 1 (by rfl) ⟨511232, by rfl⟩ : syracuseStep 681643 = 1022465) B1022465
theorem B681655 : Blo 678312 681655 := bstep (se 1 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 681655 = 1022483) B1022483
theorem B681675 : Blo 678312 681675 := bstep (se 1 (by rfl) ⟨511256, by rfl⟩ : syracuseStep 681675 = 1022513) B1022513
theorem B681687 : Blo 678312 681687 := bstep (se 1 (by rfl) ⟨511265, by rfl⟩ : syracuseStep 681687 = 1022531) B1022531
theorem B681707 : Blo 678312 681707 := bstep (se 1 (by rfl) ⟨511280, by rfl⟩ : syracuseStep 681707 = 1022561) B1022561
theorem B14739185 : Blo 678312 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B681719 : Blo 678312 681719 := bstep (se 1 (by rfl) ⟨511289, by rfl⟩ : syracuseStep 681719 = 1022579) B1022579
theorem B1533707 : Blo 678312 1533707 := bstep (se 1 (by rfl) ⟨1150280, by rfl⟩ : syracuseStep 1533707 = 2300561) B2300561
theorem B681739 : Blo 678312 681739 := bstep (se 1 (by rfl) ⟨511304, by rfl⟩ : syracuseStep 681739 = 1022609) B1022609
theorem B681751 : Blo 678312 681751 := bstep (se 1 (by rfl) ⟨511313, by rfl⟩ : syracuseStep 681751 = 1022627) B1022627
theorem B681771 : Blo 678312 681771 := bstep (se 1 (by rfl) ⟨511328, by rfl⟩ : syracuseStep 681771 = 1022657) B1022657
theorem B681783 : Blo 678312 681783 := bstep (se 1 (by rfl) ⟨511337, by rfl⟩ : syracuseStep 681783 = 1022675) B1022675
theorem B1533761 : Blo 678312 1533761 := bstep (se 2 (by rfl) ⟨575160, by rfl⟩ : syracuseStep 1533761 = 1150321) B1150321
theorem B681803 : Blo 678312 681803 := bstep (se 1 (by rfl) ⟨511352, by rfl⟩ : syracuseStep 681803 = 1022705) B1022705
theorem B681815 : Blo 678312 681815 := bstep (se 1 (by rfl) ⟨511361, by rfl⟩ : syracuseStep 681815 = 1022723) B1022723
theorem B681835 : Blo 678312 681835 := bstep (se 1 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 681835 = 1022753) B1022753
theorem B681847 : Blo 678312 681847 := bstep (se 1 (by rfl) ⟨511385, by rfl⟩ : syracuseStep 681847 = 1022771) B1022771
theorem B681867 : Blo 678312 681867 := bstep (se 1 (by rfl) ⟨511400, by rfl⟩ : syracuseStep 681867 = 1022801) B1022801
theorem B681879 : Blo 678312 681879 := bstep (se 1 (by rfl) ⟨511409, by rfl⟩ : syracuseStep 681879 = 1022819) B1022819
theorem B681899 : Blo 678312 681899 := bstep (se 1 (by rfl) ⟨511424, by rfl⟩ : syracuseStep 681899 = 1022849) B1022849
theorem B681911 : Blo 678312 681911 := bstep (se 1 (by rfl) ⟨511433, by rfl⟩ : syracuseStep 681911 = 1022867) B1022867
theorem B681931 : Blo 678312 681931 := bstep (se 1 (by rfl) ⟨511448, by rfl⟩ : syracuseStep 681931 = 1022897) B1022897
theorem B681943 : Blo 678312 681943 := bstep (se 1 (by rfl) ⟨511457, by rfl⟩ : syracuseStep 681943 = 1022915) B1022915
theorem B681963 : Blo 678312 681963 := bstep (se 1 (by rfl) ⟨511472, by rfl⟩ : syracuseStep 681963 = 1022945) B1022945
theorem B681975 : Blo 678312 681975 := bstep (se 1 (by rfl) ⟨511481, by rfl⟩ : syracuseStep 681975 = 1022963) B1022963
theorem B681995 : Blo 678312 681995 := bstep (se 1 (by rfl) ⟨511496, by rfl⟩ : syracuseStep 681995 = 1022993) B1022993
theorem B682007 : Blo 678312 682007 := bstep (se 1 (by rfl) ⟨511505, by rfl⟩ : syracuseStep 682007 = 1023011) B1023011
theorem B1533977 : Blo 678312 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B682027 : Blo 678312 682027 := bstep (se 1 (by rfl) ⟨511520, by rfl⟩ : syracuseStep 682027 = 1023041) B1023041
theorem B682039 : Blo 678312 682039 := bstep (se 1 (by rfl) ⟨511529, by rfl⟩ : syracuseStep 682039 = 1023059) B1023059
theorem B3434561 : Blo 678312 3434561 := bstep (se 2 (by rfl) ⟨1287960, by rfl⟩ : syracuseStep 3434561 = 2575921) B2575921
theorem B682059 : Blo 678312 682059 := bstep (se 1 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 682059 = 1023089) B1023089
theorem B682071 : Blo 678312 682071 := bstep (se 1 (by rfl) ⟨511553, by rfl⟩ : syracuseStep 682071 = 1023107) B1023107
theorem B682091 : Blo 678312 682091 := bstep (se 1 (by rfl) ⟨511568, by rfl⟩ : syracuseStep 682091 = 1023137) B1023137
theorem B1534067 : Blo 678312 1534067 := bstep (se 1 (by rfl) ⟨1150550, by rfl⟩ : syracuseStep 1534067 = 2301101) B2301101
theorem B682103 : Blo 678312 682103 := bstep (se 1 (by rfl) ⟨511577, by rfl⟩ : syracuseStep 682103 = 1023155) B1023155
theorem B682123 : Blo 678312 682123 := bstep (se 1 (by rfl) ⟨511592, by rfl⟩ : syracuseStep 682123 = 1023185) B1023185
theorem B1534103 : Blo 678312 1534103 := bstep (se 1 (by rfl) ⟨1150577, by rfl⟩ : syracuseStep 1534103 = 2301155) B2301155
theorem B682135 : Blo 678312 682135 := bstep (se 1 (by rfl) ⟨511601, by rfl⟩ : syracuseStep 682135 = 1023203) B1023203
theorem B682155 : Blo 678312 682155 := bstep (se 1 (by rfl) ⟨511616, by rfl⟩ : syracuseStep 682155 = 1023233) B1023233
theorem B682167 : Blo 678312 682167 := bstep (se 1 (by rfl) ⟨511625, by rfl⟩ : syracuseStep 682167 = 1023251) B1023251
theorem B682187 : Blo 678312 682187 := bstep (se 1 (by rfl) ⟨511640, by rfl⟩ : syracuseStep 682187 = 1023281) B1023281
theorem B682199 : Blo 678312 682199 := bstep (se 1 (by rfl) ⟨511649, by rfl⟩ : syracuseStep 682199 = 1023299) B1023299
theorem B682219 : Blo 678312 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B682231 : Blo 678312 682231 := bstep (se 1 (by rfl) ⟨511673, by rfl⟩ : syracuseStep 682231 = 1023347) B1023347
theorem B682251 : Blo 678312 682251 := bstep (se 1 (by rfl) ⟨511688, by rfl⟩ : syracuseStep 682251 = 1023377) B1023377
theorem B2910487 : Blo 678312 2910487 := bstep (se 1 (by rfl) ⟨2182865, by rfl⟩ : syracuseStep 2910487 = 4365731) B4365731
theorem B682263 : Blo 678312 682263 := bstep (se 1 (by rfl) ⟨511697, by rfl⟩ : syracuseStep 682263 = 1023395) B1023395
theorem B682283 : Blo 678312 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B682295 : Blo 678312 682295 := bstep (se 1 (by rfl) ⟨511721, by rfl⟩ : syracuseStep 682295 = 1023443) B1023443
theorem B1534283 : Blo 678312 1534283 := bstep (se 1 (by rfl) ⟨1150712, by rfl⟩ : syracuseStep 1534283 = 2301425) B2301425
theorem B1534337 : Blo 678312 1534337 := bstep (se 2 (by rfl) ⟨575376, by rfl⟩ : syracuseStep 1534337 = 1150753) B1150753
theorem B1534553 : Blo 678312 1534553 := bstep (se 2 (by rfl) ⟨575457, by rfl⟩ : syracuseStep 1534553 = 1150915) B1150915
theorem B11168387 : Blo 678312 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B1534643 : Blo 678312 1534643 := bstep (se 1 (by rfl) ⟨1150982, by rfl⟩ : syracuseStep 1534643 = 2301965) B2301965
theorem B1534679 : Blo 678312 1534679 := bstep (se 1 (by rfl) ⟨1151009, by rfl⟩ : syracuseStep 1534679 = 2302019) B2302019
theorem B1534859 : Blo 678312 1534859 := bstep (se 1 (by rfl) ⟨1151144, by rfl⟩ : syracuseStep 1534859 = 2302289) B2302289
theorem B1534913 : Blo 678312 1534913 := bstep (se 2 (by rfl) ⟨575592, by rfl⟩ : syracuseStep 1534913 = 1151185) B1151185
theorem B2583683 : Blo 678312 2583683 := bstep (se 1 (by rfl) ⟨1937762, by rfl⟩ : syracuseStep 2583683 = 3875525) B3875525
theorem B2583697 : Blo 678312 2583697 := bstep (se 2 (by rfl) ⟨968886, by rfl⟩ : syracuseStep 2583697 = 1937773) B1937773
theorem B1535129 : Blo 678312 1535129 := bstep (se 2 (by rfl) ⟨575673, by rfl⟩ : syracuseStep 1535129 = 1151347) B1151347
theorem B1633459 : Blo 678312 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B5172497 : Blo 678312 5172497 := bstep (se 2 (by rfl) ⟨1939686, by rfl⟩ : syracuseStep 5172497 = 3879373) B3879373
theorem B2584001 : Blo 678312 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B7368209 : Blo 678312 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B2911889 : Blo 678312 2911889 := bstep (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) B2183917
theorem B3436505 : Blo 678312 3436505 := bstep (se 2 (by rfl) ⟨1288689, by rfl⟩ : syracuseStep 3436505 = 2577379) B2577379
theorem B2584669 : Blo 678312 2584669 := bstep (se 3 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 2584669 = 969251) B969251
theorem B2289815 : Blo 678312 2289815 := bstep (se 1 (by rfl) ⟨1717361, by rfl⟩ : syracuseStep 2289815 = 3434723) B3434723
theorem B1994969 : Blo 678312 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B11006387 : Blo 678312 11006387 := bstep (se 1 (by rfl) ⟨8254790, by rfl⟩ : syracuseStep 11006387 = 16509581) B16509581
theorem B1470935 : Blo 678312 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B2290355 : Blo 678312 2290355 := bstep (se 1 (by rfl) ⟨1717766, by rfl⟩ : syracuseStep 2290355 = 3435533) B3435533
theorem B5796643 : Blo 678312 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B1307443 : Blo 678312 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B2978635 : Blo 678312 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B2290625 : Blo 678312 2290625 := bstep (se 2 (by rfl) ⟨858984, by rfl⟩ : syracuseStep 2290625 = 1717969) B1717969
theorem B2946179 : Blo 678312 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B2487475 : Blo 678312 2487475 := bstep (se 1 (by rfl) ⟨1865606, by rfl⟩ : syracuseStep 2487475 = 3731213) B3731213
theorem B3110147 : Blo 678312 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B2585945 : Blo 678312 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B2291165 : Blo 678312 2291165 := bstep (se 3 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 2291165 = 859187) B859187
theorem B6551057 : Blo 678312 6551057 := bstep (se 2 (by rfl) ⟨2456646, by rfl⟩ : syracuseStep 6551057 = 4913293) B4913293
theorem B3438125 : Blo 678312 3438125 := bstep (se 3 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 3438125 = 1289297) B1289297
theorem B2094913 : Blo 678312 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B41875379 : Blo 678312 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B1144793 : Blo 678312 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B5502937 : Blo 678312 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B1308737 : Blo 678312 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B1144921 : Blo 678312 1144921 := bstep (se 2 (by rfl) ⟨429345, by rfl⟩ : syracuseStep 1144921 = 858691) B858691
theorem B3864793 : Blo 678312 3864793 := bstep (se 2 (by rfl) ⟨1449297, by rfl⟩ : syracuseStep 3864793 = 2898595) B2898595
theorem B2292299 : Blo 678312 2292299 := bstep (se 1 (by rfl) ⟨1719224, by rfl⟩ : syracuseStep 2292299 = 3438449) B3438449
theorem B1636939 : Blo 678312 1636939 := bstep (se 1 (by rfl) ⟨1227704, by rfl⟩ : syracuseStep 1636939 = 2455409) B2455409
theorem B1145495 : Blo 678312 1145495 := bstep (se 1 (by rfl) ⟨859121, by rfl⟩ : syracuseStep 1145495 = 1718243) B1718243
theorem B1637015 : Blo 678312 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B817879 : Blo 678312 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B3668753 : Blo 678312 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1145623 : Blo 678312 1145623 := bstep (se 1 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 1145623 = 1718435) B1718435
theorem B2292569 : Blo 678312 2292569 := bstep (se 2 (by rfl) ⟨859713, by rfl⟩ : syracuseStep 2292569 = 1719427) B1719427
theorem B2587571 : Blo 678312 2587571 := bstep (se 1 (by rfl) ⟨1940678, by rfl⟩ : syracuseStep 2587571 = 3881357) B3881357
theorem B2587585 : Blo 678312 2587585 := bstep (se 2 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 2587585 = 1940689) B1940689
theorem B5176385 : Blo 678312 5176385 := bstep (se 2 (by rfl) ⟨1941144, by rfl⟩ : syracuseStep 5176385 = 3882289) B3882289
theorem B6290507 : Blo 678312 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B1309783 : Blo 678312 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B818263 : Blo 678312 818263 := bstep (se 1 (by rfl) ⟨613697, by rfl⟩ : syracuseStep 818263 = 1227395) B1227395
theorem B3865751 : Blo 678312 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B2751661 : Blo 678312 2751661 := bstep (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) B1031873
theorem B1244441 : Blo 678312 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B1146251 : Blo 678312 1146251 := bstep (se 1 (by rfl) ⟨859688, by rfl⟩ : syracuseStep 1146251 = 1719377) B1719377
theorem B1834433 : Blo 678312 1834433 := bstep (se 2 (by rfl) ⟨687912, by rfl⟩ : syracuseStep 1834433 = 1375825) B1375825
theorem B1932761 : Blo 678312 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1146379 : Blo 678312 1146379 := bstep (se 1 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 1146379 = 1719569) B1719569
theorem B2293271 : Blo 678312 2293271 := bstep (se 1 (by rfl) ⟨1719953, by rfl⟩ : syracuseStep 2293271 = 3439907) B3439907
theorem B1146521 : Blo 678312 1146521 := bstep (se 2 (by rfl) ⟨429945, by rfl⟩ : syracuseStep 1146521 = 859891) B859891
theorem B1146649 : Blo 678312 1146649 := bstep (se 2 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 1146649 = 859987) B859987
theorem B917563 : Blo 678312 917563 := bstep (se 1 (by rfl) ⟨688172, by rfl⟩ : syracuseStep 917563 = 1376345) B1376345
theorem B1933399 : Blo 678312 1933399 := bstep (se 1 (by rfl) ⟨1450049, by rfl⟩ : syracuseStep 1933399 = 2900099) B2900099
theorem B1147081 : Blo 678312 1147081 := bstep (se 2 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 1147081 = 860311) B860311
theorem B1933627 : Blo 678312 1933627 := bstep (se 1 (by rfl) ⟨1450220, by rfl⟩ : syracuseStep 1933627 = 2900441) B2900441
theorem B2589043 : Blo 678312 2589043 := bstep (se 1 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 2589043 = 3883565) B3883565
theorem B3441041 : Blo 678312 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B1933753 : Blo 678312 1933753 := bstep (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) B1450315
theorem B4358609 : Blo 678312 4358609 := bstep (se 2 (by rfl) ⟨1634478, by rfl⟩ : syracuseStep 4358609 = 3268957) B3268957
theorem B3932675 : Blo 678312 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B1639169 : Blo 678312 1639169 := bstep (se 2 (by rfl) ⟨614688, by rfl⟩ : syracuseStep 1639169 = 1229377) B1229377
theorem B3867527 : Blo 678312 3867527 := bstep (se 1 (by rfl) ⟨2900645, by rfl⟩ : syracuseStep 3867527 = 5801291) B5801291
theorem B1147783 : Blo 678312 1147783 := bstep (se 1 (by rfl) ⟨860837, by rfl⟩ : syracuseStep 1147783 = 1721675) B1721675
theorem B2294675 : Blo 678312 2294675 := bstep (se 1 (by rfl) ⟨1721006, by rfl⟩ : syracuseStep 2294675 = 3442013) B3442013
theorem B3277721 : Blo 678312 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B3277835 : Blo 678312 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B2458667 : Blo 678312 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B3867709 : Blo 678312 3867709 := bstep (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) B1450391
theorem B12583997 : Blo 678312 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B4359683 : Blo 678312 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B3671563 : Blo 678312 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1148431 : Blo 678312 1148431 := bstep (se 1 (by rfl) ⟨861323, by rfl⟩ : syracuseStep 1148431 = 1722647) B1722647
theorem B1017479 : Blo 678312 1017479 := bstep (se 1 (by rfl) ⟨763109, by rfl⟩ : syracuseStep 1017479 = 1526219) B1526219
theorem B1017515 : Blo 678312 1017515 := bstep (se 1 (by rfl) ⟨763136, by rfl⟩ : syracuseStep 1017515 = 1526273) B1526273
theorem B6555329 : Blo 678312 6555329 := bstep (se 2 (by rfl) ⟨2458248, by rfl⟩ : syracuseStep 6555329 = 4916497) B4916497
theorem B1017545 : Blo 678312 1017545 := bstep (se 2 (by rfl) ⟨381579, by rfl⟩ : syracuseStep 1017545 = 763159) B763159
theorem B1017659 : Blo 678312 1017659 := bstep (se 1 (by rfl) ⟨763244, by rfl⟩ : syracuseStep 1017659 = 1526489) B1526489
theorem B1017719 : Blo 678312 1017719 := bstep (se 1 (by rfl) ⟨763289, by rfl⟩ : syracuseStep 1017719 = 1526579) B1526579
theorem B1017743 : Blo 678312 1017743 := bstep (se 1 (by rfl) ⟨763307, by rfl⟩ : syracuseStep 1017743 = 1526615) B1526615
theorem B1017785 : Blo 678312 1017785 := bstep (se 2 (by rfl) ⟨381669, by rfl⟩ : syracuseStep 1017785 = 763339) B763339
theorem B1017863 : Blo 678312 1017863 := bstep (se 1 (by rfl) ⟨763397, by rfl⟩ : syracuseStep 1017863 = 1526795) B1526795
theorem B21235729 : Blo 678312 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1017899 : Blo 678312 1017899 := bstep (se 1 (by rfl) ⟨763424, by rfl⟩ : syracuseStep 1017899 = 1526849) B1526849
theorem B1148971 : Blo 678312 1148971 := bstep (se 1 (by rfl) ⟨861728, by rfl⟩ : syracuseStep 1148971 = 1723457) B1723457
theorem B1017929 : Blo 678312 1017929 := bstep (se 2 (by rfl) ⟨381723, by rfl⟩ : syracuseStep 1017929 = 763447) B763447
theorem B1149113 : Blo 678312 1149113 := bstep (se 2 (by rfl) ⟨430917, by rfl⟩ : syracuseStep 1149113 = 861835) B861835
theorem B1018043 : Blo 678312 1018043 := bstep (se 1 (by rfl) ⟨763532, by rfl⟩ : syracuseStep 1018043 = 1527065) B1527065
theorem B1018103 : Blo 678312 1018103 := bstep (se 1 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 1018103 = 1527155) B1527155
theorem B1018127 : Blo 678312 1018127 := bstep (se 1 (by rfl) ⟨763595, by rfl⟩ : syracuseStep 1018127 = 1527191) B1527191
theorem B2296079 : Blo 678312 2296079 := bstep (se 1 (by rfl) ⟨1722059, by rfl⟩ : syracuseStep 2296079 = 3444119) B3444119
theorem B1018169 : Blo 678312 1018169 := bstep (se 2 (by rfl) ⟨381813, by rfl⟩ : syracuseStep 1018169 = 763627) B763627
theorem B1935677 : Blo 678312 1935677 := bstep (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) B725879
theorem B1018247 : Blo 678312 1018247 := bstep (se 1 (by rfl) ⟨763685, by rfl⟩ : syracuseStep 1018247 = 1527371) B1527371
theorem B1018283 : Blo 678312 1018283 := bstep (se 1 (by rfl) ⟨763712, by rfl⟩ : syracuseStep 1018283 = 1527425) B1527425
theorem B1018313 : Blo 678312 1018313 := bstep (se 2 (by rfl) ⟨381867, by rfl⟩ : syracuseStep 1018313 = 763735) B763735
theorem B3443147 : Blo 678312 3443147 := bstep (se 1 (by rfl) ⟨2582360, by rfl⟩ : syracuseStep 3443147 = 5164721) B5164721
theorem B2296349 : Blo 678312 2296349 := bstep (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) B861131
theorem B1018427 : Blo 678312 1018427 := bstep (se 1 (by rfl) ⟨763820, by rfl⟩ : syracuseStep 1018427 = 1527641) B1527641
theorem B1018487 : Blo 678312 1018487 := bstep (se 1 (by rfl) ⟨763865, by rfl⟩ : syracuseStep 1018487 = 1527731) B1527731
theorem B1018511 : Blo 678312 1018511 := bstep (se 1 (by rfl) ⟨763883, by rfl⟩ : syracuseStep 1018511 = 1527767) B1527767
theorem B1018553 : Blo 678312 1018553 := bstep (se 2 (by rfl) ⟨381957, by rfl⟩ : syracuseStep 1018553 = 763915) B763915
theorem B3869441 : Blo 678312 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B1018631 : Blo 678312 1018631 := bstep (se 1 (by rfl) ⟨763973, by rfl⟩ : syracuseStep 1018631 = 1527947) B1527947
theorem B3443471 : Blo 678312 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B6523685 : Blo 678312 6523685 := bstep (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) B1223191
theorem B1018667 : Blo 678312 1018667 := bstep (se 1 (by rfl) ⟨764000, by rfl⟩ : syracuseStep 1018667 = 1528001) B1528001
theorem B1018697 : Blo 678312 1018697 := bstep (se 2 (by rfl) ⟨382011, by rfl⟩ : syracuseStep 1018697 = 764023) B764023
theorem B1149815 : Blo 678312 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B1018811 : Blo 678312 1018811 := bstep (se 1 (by rfl) ⟨764108, by rfl⟩ : syracuseStep 1018811 = 1528217) B1528217
theorem B1018871 : Blo 678312 1018871 := bstep (se 1 (by rfl) ⟨764153, by rfl⟩ : syracuseStep 1018871 = 1528307) B1528307
theorem B1018895 : Blo 678312 1018895 := bstep (se 1 (by rfl) ⟨764171, by rfl⟩ : syracuseStep 1018895 = 1528343) B1528343
theorem B1018937 : Blo 678312 1018937 := bstep (se 2 (by rfl) ⟨382101, by rfl⟩ : syracuseStep 1018937 = 764203) B764203
theorem B14027863 : Blo 678312 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B1019015 : Blo 678312 1019015 := bstep (se 1 (by rfl) ⟨764261, by rfl⟩ : syracuseStep 1019015 = 1528523) B1528523
theorem B1019051 : Blo 678312 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B1019081 : Blo 678312 1019081 := bstep (se 2 (by rfl) ⟨382155, by rfl⟩ : syracuseStep 1019081 = 764311) B764311
theorem B1936669 : Blo 678312 1936669 := bstep (se 3 (by rfl) ⟨363125, by rfl⟩ : syracuseStep 1936669 = 726251) B726251
theorem B1019195 : Blo 678312 1019195 := bstep (se 1 (by rfl) ⟨764396, by rfl⟩ : syracuseStep 1019195 = 1528793) B1528793
theorem B1150267 : Blo 678312 1150267 := bstep (se 1 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 1150267 = 1725401) B1725401
theorem B1019255 : Blo 678312 1019255 := bstep (se 1 (by rfl) ⟨764441, by rfl⟩ : syracuseStep 1019255 = 1528883) B1528883
theorem B1019279 : Blo 678312 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B1019321 : Blo 678312 1019321 := bstep (se 2 (by rfl) ⟨382245, by rfl⟩ : syracuseStep 1019321 = 764491) B764491
theorem B1150409 : Blo 678312 1150409 := bstep (se 2 (by rfl) ⟨431403, by rfl⟩ : syracuseStep 1150409 = 862807) B862807
theorem B1019399 : Blo 678312 1019399 := bstep (se 1 (by rfl) ⟨764549, by rfl⟩ : syracuseStep 1019399 = 1529099) B1529099
theorem B1019435 : Blo 678312 1019435 := bstep (se 1 (by rfl) ⟨764576, by rfl⟩ : syracuseStep 1019435 = 1529153) B1529153
theorem B1019465 : Blo 678312 1019465 := bstep (se 2 (by rfl) ⟨382299, by rfl⟩ : syracuseStep 1019465 = 764599) B764599
theorem B1019579 : Blo 678312 1019579 := bstep (se 1 (by rfl) ⟨764684, by rfl⟩ : syracuseStep 1019579 = 1529369) B1529369
theorem B1019639 : Blo 678312 1019639 := bstep (se 1 (by rfl) ⟨764729, by rfl⟩ : syracuseStep 1019639 = 1529459) B1529459
theorem B1019663 : Blo 678312 1019663 := bstep (se 1 (by rfl) ⟨764747, by rfl⟩ : syracuseStep 1019663 = 1529495) B1529495
theorem B1019705 : Blo 678312 1019705 := bstep (se 2 (by rfl) ⟨382389, by rfl⟩ : syracuseStep 1019705 = 764779) B764779
theorem B1019783 : Blo 678312 1019783 := bstep (se 1 (by rfl) ⟨764837, by rfl⟩ : syracuseStep 1019783 = 1529675) B1529675
theorem B2297753 : Blo 678312 2297753 := bstep (se 2 (by rfl) ⟨861657, by rfl⟩ : syracuseStep 2297753 = 1723315) B1723315
theorem B1019819 : Blo 678312 1019819 := bstep (se 1 (by rfl) ⟨764864, by rfl⟩ : syracuseStep 1019819 = 1529729) B1529729
theorem B1019849 : Blo 678312 1019849 := bstep (se 2 (by rfl) ⟨382443, by rfl⟩ : syracuseStep 1019849 = 764887) B764887
theorem B1019963 : Blo 678312 1019963 := bstep (se 1 (by rfl) ⟨764972, by rfl⟩ : syracuseStep 1019963 = 1529945) B1529945
theorem B1020023 : Blo 678312 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B1151111 : Blo 678312 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B1020047 : Blo 678312 1020047 := bstep (se 1 (by rfl) ⟨765035, by rfl⟩ : syracuseStep 1020047 = 1530071) B1530071
theorem B1020089 : Blo 678312 1020089 := bstep (se 2 (by rfl) ⟨382533, by rfl⟩ : syracuseStep 1020089 = 765067) B765067
theorem B3444929 : Blo 678312 3444929 := bstep (se 2 (by rfl) ⟨1291848, by rfl⟩ : syracuseStep 3444929 = 2583697) B2583697
theorem B1020167 : Blo 678312 1020167 := bstep (se 1 (by rfl) ⟨765125, by rfl⟩ : syracuseStep 1020167 = 1530251) B1530251
theorem B4657441 : Blo 678312 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B1020203 : Blo 678312 1020203 := bstep (se 1 (by rfl) ⟨765152, by rfl⟩ : syracuseStep 1020203 = 1530305) B1530305
theorem B1020233 : Blo 678312 1020233 := bstep (se 2 (by rfl) ⟨382587, by rfl⟩ : syracuseStep 1020233 = 765175) B765175
theorem B1020347 : Blo 678312 1020347 := bstep (se 1 (by rfl) ⟨765260, by rfl⟩ : syracuseStep 1020347 = 1530521) B1530521
theorem B1020407 : Blo 678312 1020407 := bstep (se 1 (by rfl) ⟨765305, by rfl⟩ : syracuseStep 1020407 = 1530611) B1530611
theorem B1020431 : Blo 678312 1020431 := bstep (se 1 (by rfl) ⟨765323, by rfl⟩ : syracuseStep 1020431 = 1530647) B1530647
theorem B19599893 : Blo 678312 19599893 := bstep (se 6 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 19599893 = 918745) B918745
theorem B59609621 : Blo 678312 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B1020473 : Blo 678312 1020473 := bstep (se 2 (by rfl) ⟨382677, by rfl⟩ : syracuseStep 1020473 = 765355) B765355
theorem B2298455 : Blo 678312 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B1020551 : Blo 678312 1020551 := bstep (se 1 (by rfl) ⟨765413, by rfl⟩ : syracuseStep 1020551 = 1530827) B1530827
theorem B1020587 : Blo 678312 1020587 := bstep (se 1 (by rfl) ⟨765440, by rfl⟩ : syracuseStep 1020587 = 1530881) B1530881
theorem B1020617 : Blo 678312 1020617 := bstep (se 2 (by rfl) ⟨382731, by rfl⟩ : syracuseStep 1020617 = 765463) B765463
theorem B1020731 : Blo 678312 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B1020791 : Blo 678312 1020791 := bstep (se 1 (by rfl) ⟨765593, by rfl⟩ : syracuseStep 1020791 = 1531187) B1531187
theorem B1020815 : Blo 678312 1020815 := bstep (se 1 (by rfl) ⟨765611, by rfl⟩ : syracuseStep 1020815 = 1531223) B1531223
theorem B1020857 : Blo 678312 1020857 := bstep (se 2 (by rfl) ⟨382821, by rfl⟩ : syracuseStep 1020857 = 765643) B765643
theorem B1020935 : Blo 678312 1020935 := bstep (se 1 (by rfl) ⟨765701, by rfl⟩ : syracuseStep 1020935 = 1531403) B1531403
theorem B1020971 : Blo 678312 1020971 := bstep (se 1 (by rfl) ⟨765728, by rfl⟩ : syracuseStep 1020971 = 1531457) B1531457
theorem B2298941 : Blo 678312 2298941 := bstep (se 3 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 2298941 = 862103) B862103
theorem B1021001 : Blo 678312 1021001 := bstep (se 2 (by rfl) ⟨382875, by rfl⟩ : syracuseStep 1021001 = 765751) B765751
theorem B1938617 : Blo 678312 1938617 := bstep (se 2 (by rfl) ⟨726981, by rfl⟩ : syracuseStep 1938617 = 1453963) B1453963
theorem B1021115 : Blo 678312 1021115 := bstep (se 1 (by rfl) ⟨765836, by rfl⟩ : syracuseStep 1021115 = 1531673) B1531673
theorem B1021175 : Blo 678312 1021175 := bstep (se 1 (by rfl) ⟨765881, by rfl⟩ : syracuseStep 1021175 = 1531763) B1531763
theorem B1021199 : Blo 678312 1021199 := bstep (se 1 (by rfl) ⟨765899, by rfl⟩ : syracuseStep 1021199 = 1531799) B1531799
theorem B1021241 : Blo 678312 1021241 := bstep (se 2 (by rfl) ⟨382965, by rfl⟩ : syracuseStep 1021241 = 765931) B765931
theorem B1021319 : Blo 678312 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B1021355 : Blo 678312 1021355 := bstep (se 1 (by rfl) ⟨766016, by rfl⟩ : syracuseStep 1021355 = 1532033) B1532033
theorem B1021385 : Blo 678312 1021385 := bstep (se 2 (by rfl) ⟨383019, by rfl⟩ : syracuseStep 1021385 = 766039) B766039
theorem B3446225 : Blo 678312 3446225 := bstep (se 2 (by rfl) ⟨1292334, by rfl⟩ : syracuseStep 3446225 = 2584669) B2584669
theorem B1021499 : Blo 678312 1021499 := bstep (se 1 (by rfl) ⟨766124, by rfl⟩ : syracuseStep 1021499 = 1532249) B1532249
theorem B1021559 : Blo 678312 1021559 := bstep (se 1 (by rfl) ⟨766169, by rfl⟩ : syracuseStep 1021559 = 1532339) B1532339
theorem B1021583 : Blo 678312 1021583 := bstep (se 1 (by rfl) ⟨766187, by rfl⟩ : syracuseStep 1021583 = 1532375) B1532375
theorem B1021625 : Blo 678312 1021625 := bstep (se 2 (by rfl) ⟨383109, by rfl⟩ : syracuseStep 1021625 = 766219) B766219
theorem B1021703 : Blo 678312 1021703 := bstep (se 1 (by rfl) ⟨766277, by rfl⟩ : syracuseStep 1021703 = 1532555) B1532555
theorem B1021739 : Blo 678312 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B3675955 : Blo 678312 3675955 := bstep (se 1 (by rfl) ⟨2756966, by rfl⟩ : syracuseStep 3675955 = 5513933) B5513933
theorem B1021769 : Blo 678312 1021769 := bstep (se 2 (by rfl) ⟨383163, by rfl⟩ : syracuseStep 1021769 = 766327) B766327
theorem B1841015 : Blo 678312 1841015 := bstep (se 1 (by rfl) ⟨1380761, by rfl⟩ : syracuseStep 1841015 = 2761523) B2761523
theorem B1021883 : Blo 678312 1021883 := bstep (se 1 (by rfl) ⟨766412, by rfl⟩ : syracuseStep 1021883 = 1532825) B1532825
theorem B1021943 : Blo 678312 1021943 := bstep (se 1 (by rfl) ⟨766457, by rfl⟩ : syracuseStep 1021943 = 1532915) B1532915
theorem B1021967 : Blo 678312 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B1022009 : Blo 678312 1022009 := bstep (se 2 (by rfl) ⟨383253, by rfl⟩ : syracuseStep 1022009 = 766507) B766507
theorem B1022087 : Blo 678312 1022087 := bstep (se 1 (by rfl) ⟨766565, by rfl⟩ : syracuseStep 1022087 = 1533131) B1533131
theorem B1022123 : Blo 678312 1022123 := bstep (se 1 (by rfl) ⟨766592, by rfl⟩ : syracuseStep 1022123 = 1533185) B1533185
theorem B1022153 : Blo 678312 1022153 := bstep (se 2 (by rfl) ⟨383307, by rfl⟩ : syracuseStep 1022153 = 766615) B766615
theorem B1841437 : Blo 678312 1841437 := bstep (se 3 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 1841437 = 690539) B690539
theorem B5970235 : Blo 678312 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B1022267 : Blo 678312 1022267 := bstep (se 1 (by rfl) ⟨766700, by rfl⟩ : syracuseStep 1022267 = 1533401) B1533401
theorem B1022327 : Blo 678312 1022327 := bstep (se 1 (by rfl) ⟨766745, by rfl⟩ : syracuseStep 1022327 = 1533491) B1533491
theorem B1022351 : Blo 678312 1022351 := bstep (se 1 (by rfl) ⟨766763, by rfl⟩ : syracuseStep 1022351 = 1533527) B1533527
theorem B1939859 : Blo 678312 1939859 := bstep (se 1 (by rfl) ⟨1454894, by rfl⟩ : syracuseStep 1939859 = 2909789) B2909789
theorem B1743257 : Blo 678312 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B858539 : Blo 678312 858539 := bstep (se 1 (by rfl) ⟨643904, by rfl⟩ : syracuseStep 858539 = 1287809) B1287809
theorem B3971513 : Blo 678312 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B2300345 : Blo 678312 2300345 := bstep (se 2 (by rfl) ⟨862629, by rfl⟩ : syracuseStep 2300345 = 1725259) B1725259
theorem B1022393 : Blo 678312 1022393 := bstep (se 2 (by rfl) ⟨383397, by rfl⟩ : syracuseStep 1022393 = 766795) B766795
theorem B1022471 : Blo 678312 1022471 := bstep (se 1 (by rfl) ⟨766853, by rfl⟩ : syracuseStep 1022471 = 1533707) B1533707
theorem B1841707 : Blo 678312 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B1022507 : Blo 678312 1022507 := bstep (se 1 (by rfl) ⟨766880, by rfl⟩ : syracuseStep 1022507 = 1533761) B1533761
theorem B1022537 : Blo 678312 1022537 := bstep (se 2 (by rfl) ⟨383451, by rfl⟩ : syracuseStep 1022537 = 766903) B766903
theorem B1383097 : Blo 678312 1383097 := bstep (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) B1037323
theorem B1022651 : Blo 678312 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B2071241 : Blo 678312 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B1022711 : Blo 678312 1022711 := bstep (se 1 (by rfl) ⟨767033, by rfl⟩ : syracuseStep 1022711 = 1534067) B1534067
theorem B727823 : Blo 678312 727823 := bstep (se 1 (by rfl) ⟨545867, by rfl⟩ : syracuseStep 727823 = 1091735) B1091735
theorem B1022735 : Blo 678312 1022735 := bstep (se 1 (by rfl) ⟨767051, by rfl⟩ : syracuseStep 1022735 = 1534103) B1534103
theorem B1022777 : Blo 678312 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B1383227 : Blo 678312 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B859015 : Blo 678312 859015 := bstep (se 1 (by rfl) ⟨644261, by rfl⟩ : syracuseStep 859015 = 1288523) B1288523
theorem B1022855 : Blo 678312 1022855 := bstep (se 1 (by rfl) ⟨767141, by rfl⟩ : syracuseStep 1022855 = 1534283) B1534283
theorem B3316633 : Blo 678312 3316633 := bstep (se 2 (by rfl) ⟨1243737, by rfl⟩ : syracuseStep 3316633 = 2487475) B2487475
theorem B1022891 : Blo 678312 1022891 := bstep (se 1 (by rfl) ⟨767168, by rfl⟩ : syracuseStep 1022891 = 1534337) B1534337
theorem B1022921 : Blo 678312 1022921 := bstep (se 2 (by rfl) ⟨383595, by rfl⟩ : syracuseStep 1022921 = 767191) B767191
theorem B2300939 : Blo 678312 2300939 := bstep (se 1 (by rfl) ⟨1725704, by rfl⟩ : syracuseStep 2300939 = 3451409) B3451409
theorem B3873815 : Blo 678312 3873815 := bstep (se 1 (by rfl) ⟨2905361, by rfl⟩ : syracuseStep 3873815 = 5810723) B5810723
theorem B1023035 : Blo 678312 1023035 := bstep (se 1 (by rfl) ⟨767276, by rfl⟩ : syracuseStep 1023035 = 1534553) B1534553
theorem B4365373 : Blo 678312 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B15735869 : Blo 678312 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B7445591 : Blo 678312 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B2301047 : Blo 678312 2301047 := bstep (se 1 (by rfl) ⟨1725785, by rfl⟩ : syracuseStep 2301047 = 3451571) B3451571
theorem B1023095 : Blo 678312 1023095 := bstep (se 1 (by rfl) ⟨767321, by rfl⟩ : syracuseStep 1023095 = 1534643) B1534643
theorem B1023119 : Blo 678312 1023119 := bstep (se 1 (by rfl) ⟨767339, by rfl⟩ : syracuseStep 1023119 = 1534679) B1534679
theorem B1023161 : Blo 678312 1023161 := bstep (se 2 (by rfl) ⟨383685, by rfl⟩ : syracuseStep 1023161 = 767371) B767371
theorem B1023239 : Blo 678312 1023239 := bstep (se 1 (by rfl) ⟨767429, by rfl⟩ : syracuseStep 1023239 = 1534859) B1534859
theorem B1023275 : Blo 678312 1023275 := bstep (se 1 (by rfl) ⟨767456, by rfl⟩ : syracuseStep 1023275 = 1534913) B1534913
theorem B1023305 : Blo 678312 1023305 := bstep (se 2 (by rfl) ⟨383739, by rfl⟩ : syracuseStep 1023305 = 767479) B767479
theorem B859511 : Blo 678312 859511 := bstep (se 1 (by rfl) ⟨644633, by rfl⟩ : syracuseStep 859511 = 1289267) B1289267
theorem B1023419 : Blo 678312 1023419 := bstep (se 1 (by rfl) ⟨767564, by rfl⟩ : syracuseStep 1023419 = 1535129) B1535129
theorem B3448331 : Blo 678312 3448331 := bstep (se 1 (by rfl) ⟨2586248, by rfl⟩ : syracuseStep 3448331 = 5172497) B5172497
theorem B859663 : Blo 678312 859663 := bstep (se 1 (by rfl) ⟨644747, by rfl⟩ : syracuseStep 859663 = 1289495) B1289495
theorem B3448493 : Blo 678312 3448493 := bstep (se 3 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 3448493 = 1293185) B1293185
theorem B859835 : Blo 678312 859835 := bstep (se 1 (by rfl) ⟨644876, by rfl⟩ : syracuseStep 859835 = 1289753) B1289753
theorem B2301641 : Blo 678312 2301641 := bstep (se 2 (by rfl) ⟨863115, by rfl⟩ : syracuseStep 2301641 = 1726231) B1726231
theorem B2793217 : Blo 678312 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1941259 : Blo 678312 1941259 := bstep (se 1 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 1941259 = 2911889) B2911889
theorem B1843091 : Blo 678312 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1449913 : Blo 678312 1449913 := bstep (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) B1087435
theorem B1941533 : Blo 678312 1941533 := bstep (se 3 (by rfl) ⟨364037, by rfl⟩ : syracuseStep 1941533 = 728075) B728075
theorem B5153057 : Blo 678312 5153057 := bstep (se 2 (by rfl) ⟨1932396, by rfl⟩ : syracuseStep 5153057 = 3864793) B3864793
theorem B2302343 : Blo 678312 2302343 := bstep (se 1 (by rfl) ⟨1726757, by rfl⟩ : syracuseStep 2302343 = 3453515) B3453515
theorem B1450631 : Blo 678312 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B860807 : Blo 678312 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B3318509 : Blo 678312 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B2302721 : Blo 678312 2302721 := bstep (se 2 (by rfl) ⟨863520, by rfl⟩ : syracuseStep 2302721 = 1727041) B1727041
theorem B2073431 : Blo 678312 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B1090505 : Blo 678312 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B4367371 : Blo 678312 4367371 := bstep (se 1 (by rfl) ⟨3275528, by rfl⟩ : syracuseStep 4367371 = 6551057) B6551057
theorem B1451143 : Blo 678312 1451143 := bstep (se 1 (by rfl) ⟨1088357, by rfl⟩ : syracuseStep 1451143 = 2176715) B2176715
theorem B5154029 : Blo 678312 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B3450113 : Blo 678312 3450113 := bstep (se 2 (by rfl) ⟨1293792, by rfl⟩ : syracuseStep 3450113 = 2587585) B2587585
theorem B861455 : Blo 678312 861455 := bstep (se 1 (by rfl) ⟨646091, by rfl⟩ : syracuseStep 861455 = 1292183) B1292183
theorem B1451297 : Blo 678312 1451297 := bstep (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) B1088473
theorem B763195 : Blo 678312 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B1746377 : Blo 678312 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B1091017 : Blo 678312 1091017 := bstep (se 2 (by rfl) ⟨409131, by rfl⟩ : syracuseStep 1091017 = 818263) B818263
theorem B22029893 : Blo 678312 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B3679937 : Blo 678312 3679937 := bstep (se 2 (by rfl) ⟨1379976, by rfl⟩ : syracuseStep 3679937 = 2759953) B2759953
theorem B763663 : Blo 678312 763663 := bstep (se 1 (by rfl) ⟨572747, by rfl⟩ : syracuseStep 763663 = 1145495) B1145495
theorem B1451819 : Blo 678312 1451819 := bstep (se 1 (by rfl) ⟨1088864, by rfl⟩ : syracuseStep 1451819 = 2177729) B2177729
theorem B993211 : Blo 678312 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B3450923 : Blo 678312 3450923 := bstep (se 1 (by rfl) ⟨2588192, by rfl⟩ : syracuseStep 3450923 = 5176385) B5176385
theorem B3876983 : Blo 678312 3876983 := bstep (se 1 (by rfl) ⟨2907737, by rfl⟩ : syracuseStep 3876983 = 5815475) B5815475
theorem B764167 : Blo 678312 764167 := bstep (se 1 (by rfl) ⟨573125, by rfl⟩ : syracuseStep 764167 = 1146251) B1146251
theorem B1222955 : Blo 678312 1222955 := bstep (se 1 (by rfl) ⟨917216, by rfl⟩ : syracuseStep 1222955 = 1834433) B1834433
theorem B764347 : Blo 678312 764347 := bstep (se 1 (by rfl) ⟨573260, by rfl⟩ : syracuseStep 764347 = 1146521) B1146521
theorem B89631197 : Blo 678312 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B18590579 : Blo 678312 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B764815 : Blo 678312 764815 := bstep (se 1 (by rfl) ⟨573611, by rfl⟩ : syracuseStep 764815 = 1147223) B1147223
theorem B8825867 : Blo 678312 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B5155973 : Blo 678312 5155973 := bstep (se 4 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 5155973 = 966745) B966745
theorem B1289351 : Blo 678312 1289351 := bstep (se 1 (by rfl) ⟨967013, by rfl⟩ : syracuseStep 1289351 = 1934027) B1934027
theorem B3452219 : Blo 678312 3452219 := bstep (se 1 (by rfl) ⟨2589164, by rfl⟩ : syracuseStep 3452219 = 5178329) B5178329
theorem B765319 : Blo 678312 765319 := bstep (se 1 (by rfl) ⟨573989, by rfl⟩ : syracuseStep 765319 = 1147979) B1147979
theorem B1453459 : Blo 678312 1453459 := bstep (se 1 (by rfl) ⟨1090094, by rfl⟩ : syracuseStep 1453459 = 2180189) B2180189
theorem B3452381 : Blo 678312 3452381 := bstep (se 3 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 3452381 = 1294643) B1294643
theorem B7876061 : Blo 678312 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B765499 : Blo 678312 765499 := bstep (se 1 (by rfl) ⟨574124, by rfl⟩ : syracuseStep 765499 = 1148249) B1148249
theorem B1552007 : Blo 678312 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B24850061 : Blo 678312 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B3452705 : Blo 678312 3452705 := bstep (se 2 (by rfl) ⟨1294764, by rfl⟩ : syracuseStep 3452705 = 2589529) B2589529
theorem B765967 : Blo 678312 765967 := bstep (se 1 (by rfl) ⟨574475, by rfl⟩ : syracuseStep 765967 = 1148951) B1148951
theorem B5517335 : Blo 678312 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B1552427 : Blo 678312 1552427 := bstep (se 1 (by rfl) ⟨1164320, by rfl⟩ : syracuseStep 1552427 = 2328641) B2328641
theorem B4141313 : Blo 678312 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B766471 : Blo 678312 766471 := bstep (se 1 (by rfl) ⟨574853, by rfl⟩ : syracuseStep 766471 = 1149707) B1149707
theorem B8729207 : Blo 678312 8729207 := bstep (se 1 (by rfl) ⟨6546905, by rfl⟩ : syracuseStep 8729207 = 13093811) B13093811
theorem B766651 : Blo 678312 766651 := bstep (se 1 (by rfl) ⟨574988, by rfl⟩ : syracuseStep 766651 = 1149977) B1149977
theorem B1290953 : Blo 678312 1290953 := bstep (se 2 (by rfl) ⟨484107, by rfl⟩ : syracuseStep 1290953 = 968215) B968215
theorem B3453677 : Blo 678312 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B7746353 : Blo 678312 7746353 := bstep (se 2 (by rfl) ⟨2904882, by rfl⟩ : syracuseStep 7746353 = 5809765) B5809765
theorem B1717139 : Blo 678312 1717139 := bstep (se 1 (by rfl) ⟨1287854, by rfl⟩ : syracuseStep 1717139 = 2575709) B2575709
theorem B767119 : Blo 678312 767119 := bstep (se 1 (by rfl) ⟨575339, by rfl⟩ : syracuseStep 767119 = 1150679) B1150679
theorem B1717433 : Blo 678312 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B1226017 : Blo 678312 1226017 := bstep (se 2 (by rfl) ⟨459756, by rfl⟩ : syracuseStep 1226017 = 919513) B919513
theorem B5158403 : Blo 678312 5158403 := bstep (se 1 (by rfl) ⟨3868802, by rfl⟩ : syracuseStep 5158403 = 7737605) B7737605
theorem B14890499 : Blo 678312 14890499 := bstep (se 1 (by rfl) ⟨11167874, by rfl⟩ : syracuseStep 14890499 = 22335749) B22335749
theorem B5518891 : Blo 678312 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B3880649 : Blo 678312 3880649 := bstep (se 2 (by rfl) ⟨1455243, by rfl⟩ : syracuseStep 3880649 = 2910487) B2910487
theorem B1718131 : Blo 678312 1718131 := bstep (se 1 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 1718131 = 2577197) B2577197
theorem B1718273 : Blo 678312 1718273 := bstep (se 2 (by rfl) ⟨644352, by rfl⟩ : syracuseStep 1718273 = 1288705) B1288705
theorem B1226767 : Blo 678312 1226767 := bstep (se 1 (by rfl) ⟨920075, by rfl⟩ : syracuseStep 1226767 = 1840151) B1840151
theorem B6273047 : Blo 678312 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B2897981 : Blo 678312 2897981 := bstep (se 3 (by rfl) ⟨543371, by rfl⟩ : syracuseStep 2897981 = 1086743) B1086743
theorem B1161515 : Blo 678312 1161515 := bstep (se 1 (by rfl) ⟨871136, by rfl⟩ : syracuseStep 1161515 = 1742273) B1742273
theorem B5519801 : Blo 678312 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B1718729 : Blo 678312 1718729 := bstep (se 2 (by rfl) ⟨644523, by rfl⟩ : syracuseStep 1718729 = 1289047) B1289047
theorem B2898443 : Blo 678312 2898443 := bstep (se 1 (by rfl) ⟨2173832, by rfl⟩ : syracuseStep 2898443 = 4347665) B4347665
theorem B1292935 : Blo 678312 1292935 := bstep (se 1 (by rfl) ⟨969701, by rfl⟩ : syracuseStep 1292935 = 1939403) B1939403
theorem B8272601 : Blo 678312 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B1719083 : Blo 678312 1719083 := bstep (se 1 (by rfl) ⟨1289312, by rfl⟩ : syracuseStep 1719083 = 2578625) B2578625
theorem B2177945 : Blo 678312 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B3489139 : Blo 678312 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B3882563 : Blo 678312 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B1720075 : Blo 678312 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B1720217 : Blo 678312 1720217 := bstep (se 2 (by rfl) ⟨645081, by rfl⟩ : syracuseStep 1720217 = 1290163) B1290163
theorem B1720379 : Blo 678312 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B3489965 : Blo 678312 3489965 := bstep (se 3 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 3489965 = 1308737) B1308737
theorem B1294537 : Blo 678312 1294537 := bstep (se 2 (by rfl) ⟨485451, by rfl⟩ : syracuseStep 1294537 = 970903) B970903
theorem B1229089 : Blo 678312 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B3260807 : Blo 678312 3260807 := bstep (se 1 (by rfl) ⟨2445605, by rfl⟩ : syracuseStep 3260807 = 4891211) B4891211
theorem B1720723 : Blo 678312 1720723 := bstep (se 1 (by rfl) ⟨1290542, by rfl⟩ : syracuseStep 1720723 = 2581085) B2581085
theorem B1720865 : Blo 678312 1720865 := bstep (se 2 (by rfl) ⟨645324, by rfl⟩ : syracuseStep 1720865 = 1290649) B1290649
theorem B967241 : Blo 678312 967241 := bstep (se 2 (by rfl) ⟨362715, by rfl⟩ : syracuseStep 967241 = 725431) B725431
theorem B2245207 : Blo 678312 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B2900681 : Blo 678312 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B968107 : Blo 678312 968107 := bstep (se 1 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 968107 = 1452161) B1452161
theorem B1721857 : Blo 678312 1721857 := bstep (se 2 (by rfl) ⟨645696, by rfl⟩ : syracuseStep 1721857 = 1291393) B1291393
theorem B9783341 : Blo 678312 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B1722455 : Blo 678312 1722455 := bstep (se 1 (by rfl) ⟨1291841, by rfl⟩ : syracuseStep 1722455 = 2583683) B2583683
theorem B3688649 : Blo 678312 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B1722667 : Blo 678312 1722667 := bstep (se 1 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 1722667 = 2584001) B2584001
theorem B1722809 : Blo 678312 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B2148925 : Blo 678312 2148925 := bstep (se 3 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 2148925 = 805847) B805847
theorem B5163749 : Blo 678312 5163749 := bstep (se 4 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 5163749 = 968203) B968203
theorem B1526543 : Blo 678312 1526543 := bstep (se 1 (by rfl) ⟨1144907, by rfl⟩ : syracuseStep 1526543 = 2289815) B2289815
theorem B1526561 : Blo 678312 1526561 := bstep (se 2 (by rfl) ⟨572460, by rfl⟩ : syracuseStep 1526561 = 1144921) B1144921
theorem B2902817 : Blo 678312 2902817 := bstep (se 2 (by rfl) ⟨1088556, by rfl⟩ : syracuseStep 2902817 = 2177113) B2177113
theorem B1329979 : Blo 678312 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B2902969 : Blo 678312 2902969 := bstep (se 2 (by rfl) ⟨1088613, by rfl⟩ : syracuseStep 2902969 = 2177227) B2177227
theorem B969673 : Blo 678312 969673 := bstep (se 2 (by rfl) ⟨363627, by rfl⟩ : syracuseStep 969673 = 727255) B727255
theorem B7851125 : Blo 678312 7851125 := bstep (se 5 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 7851125 = 736043) B736043
theorem B1526903 : Blo 678312 1526903 := bstep (se 1 (by rfl) ⟨1145177, by rfl⟩ : syracuseStep 1526903 = 2290355) B2290355
theorem B1527083 : Blo 678312 1527083 := bstep (se 1 (by rfl) ⟨1145312, by rfl⟩ : syracuseStep 1527083 = 2290625) B2290625
theorem B63688037 : Blo 678312 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B1723801 : Blo 678312 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B2182585 : Blo 678312 2182585 := bstep (se 2 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 2182585 = 1636939) B1636939
theorem B970231 : Blo 678312 970231 := bstep (se 1 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 970231 = 1455347) B1455347
theorem B1723963 : Blo 678312 1723963 := bstep (se 1 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 1723963 = 2585945) B2585945
theorem B1527443 : Blo 678312 1527443 := bstep (se 1 (by rfl) ⟨1145582, by rfl⟩ : syracuseStep 1527443 = 2291165) B2291165
theorem B1527497 : Blo 678312 1527497 := bstep (se 2 (by rfl) ⟨572811, by rfl⟩ : syracuseStep 1527497 = 1145623) B1145623
theorem B1724105 : Blo 678312 1724105 := bstep (se 2 (by rfl) ⟨646539, by rfl⟩ : syracuseStep 1724105 = 1293079) B1293079
theorem B2903789 : Blo 678312 2903789 := bstep (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) B1088921
theorem B1724449 : Blo 678312 1724449 := bstep (se 2 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 1724449 = 1293337) B1293337
theorem B970795 : Blo 678312 970795 := bstep (se 1 (by rfl) ⟨728096, by rfl⟩ : syracuseStep 970795 = 1456193) B1456193
theorem B971023 : Blo 678312 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B1528199 : Blo 678312 1528199 := bstep (se 1 (by rfl) ⟨1146149, by rfl⟩ : syracuseStep 1528199 = 2292299) B2292299
theorem B2904473 : Blo 678312 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B1528379 : Blo 678312 1528379 := bstep (se 1 (by rfl) ⟨1146284, by rfl⟩ : syracuseStep 1528379 = 2292569) B2292569
theorem B1725047 : Blo 678312 1725047 := bstep (se 1 (by rfl) ⟨1293785, by rfl⟩ : syracuseStep 1725047 = 2587571) B2587571
theorem B1528505 : Blo 678312 1528505 := bstep (se 2 (by rfl) ⟨573189, by rfl⟩ : syracuseStep 1528505 = 1146379) B1146379
theorem B4346561 : Blo 678312 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B2577167 : Blo 678312 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B1528847 : Blo 678312 1528847 := bstep (se 1 (by rfl) ⟨1146635, by rfl⟩ : syracuseStep 1528847 = 2293271) B2293271
theorem B1528865 : Blo 678312 1528865 := bstep (se 2 (by rfl) ⟨573324, by rfl⟩ : syracuseStep 1528865 = 1146649) B1146649
theorem B7755101 : Blo 678312 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B1529207 : Blo 678312 1529207 := bstep (se 1 (by rfl) ⟨1146905, by rfl⟩ : syracuseStep 1529207 = 2293811) B2293811
theorem B1529387 : Blo 678312 1529387 := bstep (se 1 (by rfl) ⟨1147040, by rfl⟩ : syracuseStep 1529387 = 2294081) B2294081
theorem B23025329 : Blo 678312 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B6543139 : Blo 678312 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B2185019 : Blo 678312 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B2447219 : Blo 678312 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B1726343 : Blo 678312 1726343 := bstep (se 1 (by rfl) ⟨1294757, by rfl⟩ : syracuseStep 1726343 = 2589515) B2589515
theorem B1529747 : Blo 678312 1529747 := bstep (se 1 (by rfl) ⟨1147310, by rfl⟩ : syracuseStep 1529747 = 2294621) B2294621
theorem B1726393 : Blo 678312 1726393 := bstep (se 2 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 1726393 = 1294795) B1294795
theorem B1529801 : Blo 678312 1529801 := bstep (se 2 (by rfl) ⟨573675, by rfl⟩ : syracuseStep 1529801 = 1147351) B1147351
theorem B6641837 : Blo 678312 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B2578823 : Blo 678312 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B678331 : Blo 678312 678331 := bstep (se 1 (by rfl) ⟨508748, by rfl⟩ : syracuseStep 678331 = 1017497) B1017497
theorem B7363021 : Blo 678312 7363021 := bstep (se 3 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 7363021 = 2761133) B2761133
theorem B678407 : Blo 678312 678407 := bstep (se 1 (by rfl) ⟨508805, by rfl⟩ : syracuseStep 678407 = 1017611) B1017611
theorem B678415 : Blo 678312 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B1726991 : Blo 678312 1726991 := bstep (se 1 (by rfl) ⟨1295243, by rfl⟩ : syracuseStep 1726991 = 2590487) B2590487
theorem B678459 : Blo 678312 678459 := bstep (se 1 (by rfl) ⟨508844, by rfl⟩ : syracuseStep 678459 = 1017689) B1017689
theorem B678535 : Blo 678312 678535 := bstep (se 1 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 678535 = 1017803) B1017803
theorem B1530503 : Blo 678312 1530503 := bstep (se 1 (by rfl) ⟨1147877, by rfl⟩ : syracuseStep 1530503 = 2295755) B2295755
theorem B678543 : Blo 678312 678543 := bstep (se 1 (by rfl) ⟨508907, by rfl⟩ : syracuseStep 678543 = 1017815) B1017815
theorem B678587 : Blo 678312 678587 := bstep (se 1 (by rfl) ⟨508940, by rfl⟩ : syracuseStep 678587 = 1017881) B1017881
theorem B44718797 : Blo 678312 44718797 := bstep (se 3 (by rfl) ⟨8384774, by rfl⟩ : syracuseStep 44718797 = 16769549) B16769549
theorem B678663 : Blo 678312 678663 := bstep (se 1 (by rfl) ⟨508997, by rfl⟩ : syracuseStep 678663 = 1017995) B1017995
theorem B678671 : Blo 678312 678671 := bstep (se 1 (by rfl) ⟨509003, by rfl⟩ : syracuseStep 678671 = 1018007) B1018007
theorem B7756559 : Blo 678312 7756559 := bstep (se 1 (by rfl) ⟨5817419, by rfl⟩ : syracuseStep 7756559 = 11634839) B11634839
theorem B678715 : Blo 678312 678715 := bstep (se 1 (by rfl) ⟨509036, by rfl⟩ : syracuseStep 678715 = 1018073) B1018073
theorem B1530683 : Blo 678312 1530683 := bstep (se 1 (by rfl) ⟨1148012, by rfl⟩ : syracuseStep 1530683 = 2296025) B2296025
theorem B678791 : Blo 678312 678791 := bstep (se 1 (by rfl) ⟨509093, by rfl⟩ : syracuseStep 678791 = 1018187) B1018187
theorem B678799 : Blo 678312 678799 := bstep (se 1 (by rfl) ⟨509099, by rfl⟩ : syracuseStep 678799 = 1018199) B1018199
theorem B1530809 : Blo 678312 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B678843 : Blo 678312 678843 := bstep (se 1 (by rfl) ⟨509132, by rfl⟩ : syracuseStep 678843 = 1018265) B1018265
theorem B678919 : Blo 678312 678919 := bstep (se 1 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 678919 = 1018379) B1018379
theorem B678927 : Blo 678312 678927 := bstep (se 1 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 678927 = 1018391) B1018391
theorem B678971 : Blo 678312 678971 := bstep (se 1 (by rfl) ⟨509228, by rfl⟩ : syracuseStep 678971 = 1018457) B1018457
theorem B679047 : Blo 678312 679047 := bstep (se 1 (by rfl) ⟨509285, by rfl⟩ : syracuseStep 679047 = 1018571) B1018571
theorem B679055 : Blo 678312 679055 := bstep (se 1 (by rfl) ⟨509291, by rfl⟩ : syracuseStep 679055 = 1018583) B1018583
theorem B679099 : Blo 678312 679099 := bstep (se 1 (by rfl) ⟨509324, by rfl⟩ : syracuseStep 679099 = 1018649) B1018649
theorem B679175 : Blo 678312 679175 := bstep (se 1 (by rfl) ⟨509381, by rfl⟩ : syracuseStep 679175 = 1018763) B1018763
theorem B679183 : Blo 678312 679183 := bstep (se 1 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 679183 = 1018775) B1018775
theorem B1531151 : Blo 678312 1531151 := bstep (se 1 (by rfl) ⟨1148363, by rfl⟩ : syracuseStep 1531151 = 2296727) B2296727
theorem B1531169 : Blo 678312 1531169 := bstep (se 2 (by rfl) ⟨574188, by rfl⟩ : syracuseStep 1531169 = 1148377) B1148377
theorem B679227 : Blo 678312 679227 := bstep (se 1 (by rfl) ⟨509420, by rfl⟩ : syracuseStep 679227 = 1018841) B1018841
theorem B679303 : Blo 678312 679303 := bstep (se 1 (by rfl) ⟨509477, by rfl⟩ : syracuseStep 679303 = 1018955) B1018955
theorem B679311 : Blo 678312 679311 := bstep (se 1 (by rfl) ⟨509483, by rfl⟩ : syracuseStep 679311 = 1018967) B1018967
theorem B679355 : Blo 678312 679355 := bstep (se 1 (by rfl) ⟨509516, by rfl⟩ : syracuseStep 679355 = 1019033) B1019033
theorem B679431 : Blo 678312 679431 := bstep (se 1 (by rfl) ⟨509573, by rfl⟩ : syracuseStep 679431 = 1019147) B1019147
theorem B679439 : Blo 678312 679439 := bstep (se 1 (by rfl) ⟨509579, by rfl⟩ : syracuseStep 679439 = 1019159) B1019159
theorem B3530263 : Blo 678312 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B679483 : Blo 678312 679483 := bstep (se 1 (by rfl) ⟨509612, by rfl⟩ : syracuseStep 679483 = 1019225) B1019225
theorem B1531511 : Blo 678312 1531511 := bstep (se 1 (by rfl) ⟨1148633, by rfl⟩ : syracuseStep 1531511 = 2297267) B2297267
theorem B1007239 : Blo 678312 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B679559 : Blo 678312 679559 := bstep (se 1 (by rfl) ⟨509669, by rfl⟩ : syracuseStep 679559 = 1019339) B1019339
theorem B679567 : Blo 678312 679567 := bstep (se 1 (by rfl) ⟨509675, by rfl⟩ : syracuseStep 679567 = 1019351) B1019351
theorem B679611 : Blo 678312 679611 := bstep (se 1 (by rfl) ⟨509708, by rfl⟩ : syracuseStep 679611 = 1019417) B1019417
theorem B679687 : Blo 678312 679687 := bstep (se 1 (by rfl) ⟨509765, by rfl⟩ : syracuseStep 679687 = 1019531) B1019531
theorem B679695 : Blo 678312 679695 := bstep (se 1 (by rfl) ⟨509771, by rfl⟩ : syracuseStep 679695 = 1019543) B1019543
theorem B1531691 : Blo 678312 1531691 := bstep (se 1 (by rfl) ⟨1148768, by rfl⟩ : syracuseStep 1531691 = 2297537) B2297537
theorem B679739 : Blo 678312 679739 := bstep (se 1 (by rfl) ⟨509804, by rfl⟩ : syracuseStep 679739 = 1019609) B1019609
theorem B679815 : Blo 678312 679815 := bstep (se 1 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 679815 = 1019723) B1019723
theorem B679823 : Blo 678312 679823 := bstep (se 1 (by rfl) ⟨509867, by rfl⟩ : syracuseStep 679823 = 1019735) B1019735
theorem B679867 : Blo 678312 679867 := bstep (se 1 (by rfl) ⟨509900, by rfl⟩ : syracuseStep 679867 = 1019801) B1019801
theorem B679943 : Blo 678312 679943 := bstep (se 1 (by rfl) ⟨509957, by rfl⟩ : syracuseStep 679943 = 1019915) B1019915
theorem B679951 : Blo 678312 679951 := bstep (se 1 (by rfl) ⟨509963, by rfl⟩ : syracuseStep 679951 = 1019927) B1019927
theorem B679995 : Blo 678312 679995 := bstep (se 1 (by rfl) ⟨509996, by rfl⟩ : syracuseStep 679995 = 1019993) B1019993
theorem B2580599 : Blo 678312 2580599 := bstep (se 1 (by rfl) ⟨1935449, by rfl⟩ : syracuseStep 2580599 = 3870899) B3870899
theorem B1958023 : Blo 678312 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B680071 : Blo 678312 680071 := bstep (se 1 (by rfl) ⟨510053, by rfl⟩ : syracuseStep 680071 = 1020107) B1020107
theorem B680079 : Blo 678312 680079 := bstep (se 1 (by rfl) ⟨510059, by rfl⟩ : syracuseStep 680079 = 1020119) B1020119
theorem B1532051 : Blo 678312 1532051 := bstep (se 1 (by rfl) ⟨1149038, by rfl⟩ : syracuseStep 1532051 = 2298077) B2298077
theorem B4350125 : Blo 678312 4350125 := bstep (se 3 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 4350125 = 1631297) B1631297
theorem B680123 : Blo 678312 680123 := bstep (se 1 (by rfl) ⟨510092, by rfl⟩ : syracuseStep 680123 = 1020185) B1020185
theorem B1532105 : Blo 678312 1532105 := bstep (se 2 (by rfl) ⟨574539, by rfl⟩ : syracuseStep 1532105 = 1149079) B1149079
theorem B680199 : Blo 678312 680199 := bstep (se 1 (by rfl) ⟨510149, by rfl⟩ : syracuseStep 680199 = 1020299) B1020299
theorem B680207 : Blo 678312 680207 := bstep (se 1 (by rfl) ⟨510155, by rfl⟩ : syracuseStep 680207 = 1020311) B1020311
theorem B680251 : Blo 678312 680251 := bstep (se 1 (by rfl) ⟨510188, by rfl⟩ : syracuseStep 680251 = 1020377) B1020377
theorem B680327 : Blo 678312 680327 := bstep (se 1 (by rfl) ⟨510245, by rfl⟩ : syracuseStep 680327 = 1020491) B1020491
theorem B680335 : Blo 678312 680335 := bstep (se 1 (by rfl) ⟨510251, by rfl⟩ : syracuseStep 680335 = 1020503) B1020503
theorem B680379 : Blo 678312 680379 := bstep (se 1 (by rfl) ⟨510284, by rfl⟩ : syracuseStep 680379 = 1020569) B1020569
theorem B680455 : Blo 678312 680455 := bstep (se 1 (by rfl) ⟨510341, by rfl⟩ : syracuseStep 680455 = 1020683) B1020683
theorem B680463 : Blo 678312 680463 := bstep (se 1 (by rfl) ⟨510347, by rfl⟩ : syracuseStep 680463 = 1020695) B1020695
theorem B680507 : Blo 678312 680507 := bstep (se 1 (by rfl) ⟨510380, by rfl⟩ : syracuseStep 680507 = 1020761) B1020761
theorem B680583 : Blo 678312 680583 := bstep (se 1 (by rfl) ⟨510437, by rfl⟩ : syracuseStep 680583 = 1020875) B1020875
theorem B680591 : Blo 678312 680591 := bstep (se 1 (by rfl) ⟨510443, by rfl⟩ : syracuseStep 680591 = 1020887) B1020887
theorem B680635 : Blo 678312 680635 := bstep (se 1 (by rfl) ⟨510476, by rfl⟩ : syracuseStep 680635 = 1020953) B1020953
theorem B680711 : Blo 678312 680711 := bstep (se 1 (by rfl) ⟨510533, by rfl⟩ : syracuseStep 680711 = 1021067) B1021067
theorem B680719 : Blo 678312 680719 := bstep (se 1 (by rfl) ⟨510539, by rfl⟩ : syracuseStep 680719 = 1021079) B1021079
theorem B680763 : Blo 678312 680763 := bstep (se 1 (by rfl) ⟨510572, by rfl⟩ : syracuseStep 680763 = 1021145) B1021145
theorem B680839 : Blo 678312 680839 := bstep (se 1 (by rfl) ⟨510629, by rfl⟩ : syracuseStep 680839 = 1021259) B1021259
theorem B1532807 : Blo 678312 1532807 := bstep (se 1 (by rfl) ⟨1149605, by rfl⟩ : syracuseStep 1532807 = 2299211) B2299211
theorem B680847 : Blo 678312 680847 := bstep (se 1 (by rfl) ⟨510635, by rfl⟩ : syracuseStep 680847 = 1021271) B1021271
theorem B680891 : Blo 678312 680891 := bstep (se 1 (by rfl) ⟨510668, by rfl⟩ : syracuseStep 680891 = 1021337) B1021337
theorem B680967 : Blo 678312 680967 := bstep (se 1 (by rfl) ⟨510725, by rfl⟩ : syracuseStep 680967 = 1021451) B1021451
theorem B680975 : Blo 678312 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B681019 : Blo 678312 681019 := bstep (se 1 (by rfl) ⟨510764, by rfl⟩ : syracuseStep 681019 = 1021529) B1021529
theorem B1532987 : Blo 678312 1532987 := bstep (se 1 (by rfl) ⟨1149740, by rfl⟩ : syracuseStep 1532987 = 2299481) B2299481
theorem B2581571 : Blo 678312 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B681095 : Blo 678312 681095 := bstep (se 1 (by rfl) ⟨510821, by rfl⟩ : syracuseStep 681095 = 1021643) B1021643
theorem B681103 : Blo 678312 681103 := bstep (se 1 (by rfl) ⟨510827, by rfl⟩ : syracuseStep 681103 = 1021655) B1021655
theorem B1533113 : Blo 678312 1533113 := bstep (se 2 (by rfl) ⟨574917, by rfl⟩ : syracuseStep 1533113 = 1149835) B1149835
theorem B681147 : Blo 678312 681147 := bstep (se 1 (by rfl) ⟨510860, by rfl⟩ : syracuseStep 681147 = 1021721) B1021721
theorem B681223 : Blo 678312 681223 := bstep (se 1 (by rfl) ⟨510917, by rfl⟩ : syracuseStep 681223 = 1021835) B1021835
theorem B746767 : Blo 678312 746767 := bstep (se 1 (by rfl) ⟨560075, by rfl⟩ : syracuseStep 746767 = 1120151) B1120151
theorem B681231 : Blo 678312 681231 := bstep (se 1 (by rfl) ⟨510923, by rfl⟩ : syracuseStep 681231 = 1021847) B1021847
theorem B681275 : Blo 678312 681275 := bstep (se 1 (by rfl) ⟨510956, by rfl⟩ : syracuseStep 681275 = 1021913) B1021913
theorem B681351 : Blo 678312 681351 := bstep (se 1 (by rfl) ⟨511013, by rfl⟩ : syracuseStep 681351 = 1022027) B1022027
theorem B681359 : Blo 678312 681359 := bstep (se 1 (by rfl) ⟨511019, by rfl⟩ : syracuseStep 681359 = 1022039) B1022039
theorem B8742329 : Blo 678312 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B681403 : Blo 678312 681403 := bstep (se 1 (by rfl) ⟨511052, by rfl⟩ : syracuseStep 681403 = 1022105) B1022105
theorem B681479 : Blo 678312 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B2582027 : Blo 678312 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B681487 : Blo 678312 681487 := bstep (se 1 (by rfl) ⟨511115, by rfl⟩ : syracuseStep 681487 = 1022231) B1022231
theorem B1533455 : Blo 678312 1533455 := bstep (se 1 (by rfl) ⟨1150091, by rfl⟩ : syracuseStep 1533455 = 2300183) B2300183
theorem B1533473 : Blo 678312 1533473 := bstep (se 2 (by rfl) ⟨575052, by rfl⟩ : syracuseStep 1533473 = 1150105) B1150105
theorem B681531 : Blo 678312 681531 := bstep (se 1 (by rfl) ⟨511148, by rfl⟩ : syracuseStep 681531 = 1022297) B1022297
theorem B681607 : Blo 678312 681607 := bstep (se 1 (by rfl) ⟨511205, by rfl⟩ : syracuseStep 681607 = 1022411) B1022411
theorem B681615 : Blo 678312 681615 := bstep (se 1 (by rfl) ⟨511211, by rfl⟩ : syracuseStep 681615 = 1022423) B1022423
theorem B681659 : Blo 678312 681659 := bstep (se 1 (by rfl) ⟨511244, by rfl⟩ : syracuseStep 681659 = 1022489) B1022489
theorem B6219521 : Blo 678312 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B681735 : Blo 678312 681735 := bstep (se 1 (by rfl) ⟨511301, by rfl⟩ : syracuseStep 681735 = 1022603) B1022603
theorem B681743 : Blo 678312 681743 := bstep (se 1 (by rfl) ⟨511307, by rfl⟩ : syracuseStep 681743 = 1022615) B1022615
theorem B681787 : Blo 678312 681787 := bstep (se 1 (by rfl) ⟨511340, by rfl⟩ : syracuseStep 681787 = 1022681) B1022681
theorem B1533815 : Blo 678312 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B2942855 : Blo 678312 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B681863 : Blo 678312 681863 := bstep (se 1 (by rfl) ⟨511397, by rfl⟩ : syracuseStep 681863 = 1022795) B1022795
theorem B681871 : Blo 678312 681871 := bstep (se 1 (by rfl) ⟨511403, by rfl⟩ : syracuseStep 681871 = 1022807) B1022807
theorem B681915 : Blo 678312 681915 := bstep (se 1 (by rfl) ⟨511436, by rfl⟩ : syracuseStep 681915 = 1022873) B1022873
theorem B8710091 : Blo 678312 8710091 := bstep (se 1 (by rfl) ⟨6532568, by rfl⟩ : syracuseStep 8710091 = 13065137) B13065137
theorem B681991 : Blo 678312 681991 := bstep (se 1 (by rfl) ⟨511493, by rfl⟩ : syracuseStep 681991 = 1022987) B1022987
theorem B681999 : Blo 678312 681999 := bstep (se 1 (by rfl) ⟨511499, by rfl⟩ : syracuseStep 681999 = 1022999) B1022999
theorem B1533995 : Blo 678312 1533995 := bstep (se 1 (by rfl) ⟨1150496, by rfl⟩ : syracuseStep 1533995 = 2300993) B2300993
theorem B682043 : Blo 678312 682043 := bstep (se 1 (by rfl) ⟨511532, by rfl⟩ : syracuseStep 682043 = 1023065) B1023065
theorem B682119 : Blo 678312 682119 := bstep (se 1 (by rfl) ⟨511589, by rfl⟩ : syracuseStep 682119 = 1023179) B1023179
theorem B682127 : Blo 678312 682127 := bstep (se 1 (by rfl) ⟨511595, by rfl⟩ : syracuseStep 682127 = 1023191) B1023191
theorem B682171 : Blo 678312 682171 := bstep (se 1 (by rfl) ⟨511628, by rfl⟩ : syracuseStep 682171 = 1023257) B1023257
theorem B682247 : Blo 678312 682247 := bstep (se 1 (by rfl) ⟨511685, by rfl⟩ : syracuseStep 682247 = 1023371) B1023371
theorem B682255 : Blo 678312 682255 := bstep (se 1 (by rfl) ⟨511691, by rfl⟩ : syracuseStep 682255 = 1023383) B1023383
theorem B682299 : Blo 678312 682299 := bstep (se 1 (by rfl) ⟨511724, by rfl⟩ : syracuseStep 682299 = 1023449) B1023449
theorem B1534355 : Blo 678312 1534355 := bstep (se 1 (by rfl) ⟨1150766, by rfl⟩ : syracuseStep 1534355 = 2301533) B2301533
theorem B1534409 : Blo 678312 1534409 := bstep (se 2 (by rfl) ⟨575403, by rfl⟩ : syracuseStep 1534409 = 1150807) B1150807
theorem B3435209 : Blo 678312 3435209 := bstep (se 2 (by rfl) ⟨1288203, by rfl⟩ : syracuseStep 3435209 = 2576407) B2576407
theorem B1633067 : Blo 678312 1633067 := bstep (se 1 (by rfl) ⟨1224800, by rfl⟩ : syracuseStep 1633067 = 2449601) B2449601
theorem B1535111 : Blo 678312 1535111 := bstep (se 1 (by rfl) ⟨1151333, by rfl⟩ : syracuseStep 1535111 = 2302667) B2302667
theorem B3108395 : Blo 678312 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B2911787 : Blo 678312 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B1961533 : Blo 678312 1961533 := bstep (se 3 (by rfl) ⟨367787, by rfl⟩ : syracuseStep 1961533 = 735575) B735575
theorem B2584183 : Blo 678312 2584183 := bstep (se 1 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 2584183 = 3876275) B3876275
theorem B7728857 : Blo 678312 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B9826123 : Blo 678312 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B2289707 : Blo 678312 2289707 := bstep (se 1 (by rfl) ⟨1717280, by rfl⟩ : syracuseStep 2289707 = 3434561) B3434561
theorem B15921269 : Blo 678312 15921269 := bstep (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) B1492619
theorem B4354249 : Blo 678312 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B1863965 : Blo 678312 1863965 := bstep (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) B698987
theorem B16576913 : Blo 678312 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B2585155 : Blo 678312 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B2585459 : Blo 678312 2585459 := bstep (se 1 (by rfl) ⟨1939094, by rfl⟩ : syracuseStep 2585459 = 3878189) B3878189
theorem B4912139 : Blo 678312 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B7337249 : Blo 678312 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B2291003 : Blo 678312 2291003 := bstep (se 1 (by rfl) ⟨1718252, by rfl⟩ : syracuseStep 2291003 = 3436505) B3436505
theorem B2585915 : Blo 678312 2585915 := bstep (se 1 (by rfl) ⟨1939436, by rfl⟩ : syracuseStep 2585915 = 3878873) B3878873
theorem B3306899 : Blo 678312 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B2913803 : Blo 678312 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B16774685 : Blo 678312 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B7337591 : Blo 678312 7337591 := bstep (se 1 (by rfl) ⟨5503193, by rfl⟩ : syracuseStep 7337591 = 11006387) B11006387
theorem B980623 : Blo 678312 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B3864293 : Blo 678312 3864293 := bstep (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) B724555
theorem B2291489 : Blo 678312 2291489 := bstep (se 2 (by rfl) ⟨859308, by rfl⟩ : syracuseStep 2291489 = 1718617) B1718617
theorem B2586401 : Blo 678312 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B2914163 : Blo 678312 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B1144847 : Blo 678312 1144847 := bstep (se 1 (by rfl) ⟨858635, by rfl⟩ : syracuseStep 1144847 = 1717271) B1717271
theorem B1964119 : Blo 678312 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2292083 : Blo 678312 2292083 := bstep (se 1 (by rfl) ⟨1719062, by rfl⟩ : syracuseStep 2292083 = 3438125) B3438125
theorem B1145387 : Blo 678312 1145387 := bstep (se 1 (by rfl) ⟨859040, by rfl⟩ : syracuseStep 1145387 = 1718081) B1718081
theorem B2062967 : Blo 678312 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B27916919 : Blo 678312 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B2587373 : Blo 678312 2587373 := bstep (se 3 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 2587373 = 970265) B970265
theorem B3668881 : Blo 678312 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B1145785 : Blo 678312 1145785 := bstep (se 2 (by rfl) ⟨429669, by rfl⟩ : syracuseStep 1145785 = 859339) B859339
theorem B7765307 : Blo 678312 7765307 := bstep (se 1 (by rfl) ⟨5823980, by rfl⟩ : syracuseStep 7765307 = 11647961) B11647961
theorem B2588057 : Blo 678312 2588057 := bstep (se 2 (by rfl) ⟨970521, by rfl⟩ : syracuseStep 2588057 = 1941043) B1941043
theorem B5799377 : Blo 678312 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B1146487 : Blo 678312 1146487 := bstep (se 1 (by rfl) ⟨859865, by rfl⟩ : syracuseStep 1146487 = 1719731) B1719731
theorem B67927853 : Blo 678312 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1146683 : Blo 678312 1146683 := bstep (se 1 (by rfl) ⟨860012, by rfl⟩ : syracuseStep 1146683 = 1720025) B1720025
theorem B1146919 : Blo 678312 1146919 := bstep (se 1 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 1146919 = 1720379) B1720379
theorem B2326643 : Blo 678312 2326643 := bstep (se 1 (by rfl) ⟨1744982, by rfl⟩ : syracuseStep 2326643 = 3489965) B3489965
theorem B2294027 : Blo 678312 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B2621783 : Blo 678312 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B1147243 : Blo 678312 1147243 := bstep (se 1 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 1147243 = 1720865) B1720865
theorem B1638785 : Blo 678312 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B1933787 : Blo 678312 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B2294297 : Blo 678312 2294297 := bstep (se 2 (by rfl) ⟨860361, by rfl⟩ : syracuseStep 2294297 = 1720723) B1720723
theorem B1639111 : Blo 678312 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B8389331 : Blo 678312 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B44205101 : Blo 678312 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B6522227 : Blo 678312 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B1148303 : Blo 678312 1148303 := bstep (se 1 (by rfl) ⟨861227, by rfl⟩ : syracuseStep 1148303 = 1722455) B1722455
theorem B2459099 : Blo 678312 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B1934857 : Blo 678312 1934857 := bstep (se 2 (by rfl) ⟨725571, by rfl⟩ : syracuseStep 1934857 = 1451143) B1451143
theorem B1148539 : Blo 678312 1148539 := bstep (se 1 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 1148539 = 1722809) B1722809
theorem B2295431 : Blo 678312 2295431 := bstep (se 1 (by rfl) ⟨1721573, by rfl⟩ : syracuseStep 2295431 = 3443147) B3443147
theorem B2295485 : Blo 678312 2295485 := bstep (se 3 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 2295485 = 860807) B860807
theorem B1017593 : Blo 678312 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B3442499 : Blo 678312 3442499 := bstep (se 1 (by rfl) ⟨2581874, by rfl⟩ : syracuseStep 3442499 = 5163749) B5163749
theorem B1017695 : Blo 678312 1017695 := bstep (se 1 (by rfl) ⟨763271, by rfl⟩ : syracuseStep 1017695 = 1526543) B1526543
theorem B2295647 : Blo 678312 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B1017707 : Blo 678312 1017707 := bstep (se 1 (by rfl) ⟨763280, by rfl⟩ : syracuseStep 1017707 = 1526561) B1526561
theorem B1935211 : Blo 678312 1935211 := bstep (se 1 (by rfl) ⟨1451408, by rfl⟩ : syracuseStep 1935211 = 2902817) B2902817
theorem B2295809 : Blo 678312 2295809 := bstep (se 2 (by rfl) ⟨860928, by rfl⟩ : syracuseStep 2295809 = 1721857) B1721857
theorem B1017935 : Blo 678312 1017935 := bstep (se 1 (by rfl) ⟨763451, by rfl⟩ : syracuseStep 1017935 = 1526903) B1526903
theorem B1018055 : Blo 678312 1018055 := bstep (se 1 (by rfl) ⟨763541, by rfl⟩ : syracuseStep 1018055 = 1527083) B1527083
theorem B1018217 : Blo 678312 1018217 := bstep (se 2 (by rfl) ⟨381831, by rfl⟩ : syracuseStep 1018217 = 763663) B763663
theorem B1018295 : Blo 678312 1018295 := bstep (se 1 (by rfl) ⟨763721, by rfl⟩ : syracuseStep 1018295 = 1527443) B1527443
theorem B1018331 : Blo 678312 1018331 := bstep (se 1 (by rfl) ⟨763748, by rfl⟩ : syracuseStep 1018331 = 1527497) B1527497
theorem B1149403 : Blo 678312 1149403 := bstep (se 1 (by rfl) ⟨862052, by rfl⟩ : syracuseStep 1149403 = 1724105) B1724105
theorem B28314305 : Blo 678312 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B2296619 : Blo 678312 2296619 := bstep (se 1 (by rfl) ⟨1722464, by rfl⟩ : syracuseStep 2296619 = 3444929) B3444929
theorem B1018799 : Blo 678312 1018799 := bstep (se 1 (by rfl) ⟨764099, by rfl⟩ : syracuseStep 1018799 = 1528199) B1528199
theorem B1936315 : Blo 678312 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B1018889 : Blo 678312 1018889 := bstep (se 2 (by rfl) ⟨382083, by rfl⟩ : syracuseStep 1018889 = 764167) B764167
theorem B1018919 : Blo 678312 1018919 := bstep (se 1 (by rfl) ⟨764189, by rfl⟩ : syracuseStep 1018919 = 1528379) B1528379
theorem B2296889 : Blo 678312 2296889 := bstep (se 2 (by rfl) ⟨861333, by rfl⟩ : syracuseStep 2296889 = 1722667) B1722667
theorem B1150031 : Blo 678312 1150031 := bstep (se 1 (by rfl) ⟨862523, by rfl⟩ : syracuseStep 1150031 = 1725047) B1725047
theorem B1019003 : Blo 678312 1019003 := bstep (se 1 (by rfl) ⟨764252, by rfl⟩ : syracuseStep 1019003 = 1528505) B1528505
theorem B1019129 : Blo 678312 1019129 := bstep (se 2 (by rfl) ⟨382173, by rfl⟩ : syracuseStep 1019129 = 764347) B764347
theorem B1019231 : Blo 678312 1019231 := bstep (se 1 (by rfl) ⟨764423, by rfl⟩ : syracuseStep 1019231 = 1528847) B1528847
theorem B1019243 : Blo 678312 1019243 := bstep (se 1 (by rfl) ⟨764432, by rfl⟩ : syracuseStep 1019243 = 1528865) B1528865
theorem B2297213 : Blo 678312 2297213 := bstep (se 3 (by rfl) ⟨430727, by rfl⟩ : syracuseStep 2297213 = 861455) B861455
theorem B3870125 : Blo 678312 3870125 := bstep (se 3 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 3870125 = 1451297) B1451297
theorem B1019471 : Blo 678312 1019471 := bstep (se 1 (by rfl) ⟨764603, by rfl⟩ : syracuseStep 1019471 = 1529207) B1529207
theorem B2297483 : Blo 678312 2297483 := bstep (se 1 (by rfl) ⟨1723112, by rfl⟩ : syracuseStep 2297483 = 3446225) B3446225
theorem B1019591 : Blo 678312 1019591 := bstep (se 1 (by rfl) ⟨764693, by rfl⟩ : syracuseStep 1019591 = 1529387) B1529387
theorem B1773305 : Blo 678312 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1019753 : Blo 678312 1019753 := bstep (se 2 (by rfl) ⟨382407, by rfl⟩ : syracuseStep 1019753 = 764815) B764815
theorem B3870625 : Blo 678312 3870625 := bstep (se 2 (by rfl) ⟨1451484, by rfl⟩ : syracuseStep 3870625 = 2902969) B2902969
theorem B1150895 : Blo 678312 1150895 := bstep (se 1 (by rfl) ⟨863171, by rfl⟩ : syracuseStep 1150895 = 1726343) B1726343
theorem B1019831 : Blo 678312 1019831 := bstep (se 1 (by rfl) ⟨764873, by rfl⟩ : syracuseStep 1019831 = 1529747) B1529747
theorem B1019867 : Blo 678312 1019867 := bstep (se 1 (by rfl) ⟨764900, by rfl⟩ : syracuseStep 1019867 = 1529801) B1529801
theorem B4427891 : Blo 678312 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B1151327 : Blo 678312 1151327 := bstep (se 1 (by rfl) ⟨863495, by rfl⟩ : syracuseStep 1151327 = 1726991) B1726991
theorem B1020335 : Blo 678312 1020335 := bstep (se 1 (by rfl) ⟨765251, by rfl⟩ : syracuseStep 1020335 = 1530503) B1530503
theorem B1380827 : Blo 678312 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1020425 : Blo 678312 1020425 := bstep (se 2 (by rfl) ⟨382659, by rfl⟩ : syracuseStep 1020425 = 765319) B765319
theorem B1937945 : Blo 678312 1937945 := bstep (se 2 (by rfl) ⟨726729, by rfl⟩ : syracuseStep 1937945 = 1453459) B1453459
theorem B2298401 : Blo 678312 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B1020455 : Blo 678312 1020455 := bstep (se 1 (by rfl) ⟨765341, by rfl⟩ : syracuseStep 1020455 = 1530683) B1530683
theorem B922151 : Blo 678312 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1020539 : Blo 678312 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B10490579 : Blo 678312 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B1020665 : Blo 678312 1020665 := bstep (se 2 (by rfl) ⟨382749, by rfl⟩ : syracuseStep 1020665 = 765499) B765499
theorem B2298617 : Blo 678312 2298617 := bstep (se 2 (by rfl) ⟨861981, by rfl⟩ : syracuseStep 2298617 = 1723963) B1723963
theorem B3445577 : Blo 678312 3445577 := bstep (se 2 (by rfl) ⟨1292091, by rfl⟩ : syracuseStep 3445577 = 2584183) B2584183
theorem B1020767 : Blo 678312 1020767 := bstep (se 1 (by rfl) ⟨765575, by rfl⟩ : syracuseStep 1020767 = 1531151) B1531151
theorem B1020779 : Blo 678312 1020779 := bstep (se 1 (by rfl) ⟨765584, by rfl⟩ : syracuseStep 1020779 = 1531169) B1531169
theorem B6525917 : Blo 678312 6525917 := bstep (se 3 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 6525917 = 2447219) B2447219
theorem B2298887 : Blo 678312 2298887 := bstep (se 1 (by rfl) ⟨1724165, by rfl⟩ : syracuseStep 2298887 = 3448331) B3448331
theorem B1021007 : Blo 678312 1021007 := bstep (se 1 (by rfl) ⟨765755, by rfl⟩ : syracuseStep 1021007 = 1531511) B1531511
theorem B2298995 : Blo 678312 2298995 := bstep (se 1 (by rfl) ⟨1724246, by rfl⟩ : syracuseStep 2298995 = 3448493) B3448493
theorem B1021127 : Blo 678312 1021127 := bstep (se 1 (by rfl) ⟨765845, by rfl⟩ : syracuseStep 1021127 = 1531691) B1531691
theorem B1021289 : Blo 678312 1021289 := bstep (se 2 (by rfl) ⟨382983, by rfl⟩ : syracuseStep 1021289 = 765967) B765967
theorem B2299265 : Blo 678312 2299265 := bstep (se 2 (by rfl) ⟨862224, by rfl⟩ : syracuseStep 2299265 = 1724449) B1724449
theorem B1021367 : Blo 678312 1021367 := bstep (se 1 (by rfl) ⟨766025, by rfl⟩ : syracuseStep 1021367 = 1532051) B1532051
theorem B1021403 : Blo 678312 1021403 := bstep (se 1 (by rfl) ⟨766052, by rfl⟩ : syracuseStep 1021403 = 1532105) B1532105
theorem B5805665 : Blo 678312 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B1382287 : Blo 678312 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B1021871 : Blo 678312 1021871 := bstep (se 1 (by rfl) ⟨766403, by rfl⟩ : syracuseStep 1021871 = 1532807) B1532807
theorem B727003 : Blo 678312 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B1021961 : Blo 678312 1021961 := bstep (se 2 (by rfl) ⟨383235, by rfl⟩ : syracuseStep 1021961 = 766471) B766471
theorem B1021991 : Blo 678312 1021991 := bstep (se 1 (by rfl) ⟨766493, by rfl⟩ : syracuseStep 1021991 = 1532987) B1532987
theorem B3446873 : Blo 678312 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B1022075 : Blo 678312 1022075 := bstep (se 1 (by rfl) ⟨766556, by rfl⟩ : syracuseStep 1022075 = 1533113) B1533113
theorem B2300075 : Blo 678312 2300075 := bstep (se 1 (by rfl) ⟨1725056, by rfl⟩ : syracuseStep 2300075 = 3450113) B3450113
theorem B1022201 : Blo 678312 1022201 := bstep (se 2 (by rfl) ⟨383325, by rfl⟩ : syracuseStep 1022201 = 766651) B766651
theorem B1022303 : Blo 678312 1022303 := bstep (se 1 (by rfl) ⟨766727, by rfl⟩ : syracuseStep 1022303 = 1533455) B1533455
theorem B1022315 : Blo 678312 1022315 := bstep (se 1 (by rfl) ⟨766736, by rfl⟩ : syracuseStep 1022315 = 1533473) B1533473
theorem B14686595 : Blo 678312 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B1022543 : Blo 678312 1022543 := bstep (se 1 (by rfl) ⟨766907, by rfl⟩ : syracuseStep 1022543 = 1533815) B1533815
theorem B5806727 : Blo 678312 5806727 := bstep (se 1 (by rfl) ⟨4355045, by rfl⟩ : syracuseStep 5806727 = 8710091) B8710091
theorem B2300615 : Blo 678312 2300615 := bstep (se 1 (by rfl) ⟨1725461, by rfl⟩ : syracuseStep 2300615 = 3450923) B3450923
theorem B1022663 : Blo 678312 1022663 := bstep (se 1 (by rfl) ⟨766997, by rfl⟩ : syracuseStep 1022663 = 1533995) B1533995
theorem B1022825 : Blo 678312 1022825 := bstep (se 2 (by rfl) ⟨383559, by rfl⟩ : syracuseStep 1022825 = 767119) B767119
theorem B1022903 : Blo 678312 1022903 := bstep (se 1 (by rfl) ⟨767177, by rfl⟩ : syracuseStep 1022903 = 1534355) B1534355
theorem B1022939 : Blo 678312 1022939 := bstep (se 1 (by rfl) ⟨767204, by rfl⟩ : syracuseStep 1022939 = 1534409) B1534409
theorem B1088711 : Blo 678312 1088711 := bstep (se 1 (by rfl) ⟨816533, by rfl⟩ : syracuseStep 1088711 = 1633067) B1633067
theorem B12393719 : Blo 678312 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B1940861 : Blo 678312 1940861 := bstep (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) B727823
theorem B859567 : Blo 678312 859567 := bstep (se 1 (by rfl) ⟨644675, by rfl⟩ : syracuseStep 859567 = 1289351) B1289351
theorem B1023407 : Blo 678312 1023407 := bstep (se 1 (by rfl) ⟨767555, by rfl⟩ : syracuseStep 1023407 = 1535111) B1535111
theorem B2301479 : Blo 678312 2301479 := bstep (se 1 (by rfl) ⟨1726109, by rfl⟩ : syracuseStep 2301479 = 3452219) B3452219
theorem B2301587 : Blo 678312 2301587 := bstep (se 1 (by rfl) ⟨1726190, by rfl⟩ : syracuseStep 2301587 = 3452381) B3452381
theorem B5250707 : Blo 678312 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B2072263 : Blo 678312 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B1941191 : Blo 678312 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B8724185 : Blo 678312 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B5152571 : Blo 678312 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B2301803 : Blo 678312 2301803 := bstep (se 1 (by rfl) ⟨1726352, by rfl⟩ : syracuseStep 2301803 = 3452705) B3452705
theorem B2301857 : Blo 678312 2301857 := bstep (se 2 (by rfl) ⟨863196, by rfl⟩ : syracuseStep 2301857 = 1726393) B1726393
theorem B3678223 : Blo 678312 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B2760875 : Blo 678312 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B860635 : Blo 678312 860635 := bstep (se 1 (by rfl) ⟨645476, by rfl⟩ : syracuseStep 860635 = 1290953) B1290953
theorem B2302451 : Blo 678312 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B4891499 : Blo 678312 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B1844129 : Blo 678312 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B2204599 : Blo 678312 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B1942535 : Blo 678312 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B11183123 : Blo 678312 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B4891727 : Blo 678312 4891727 := bstep (se 1 (by rfl) ⟨3668795, by rfl⟩ : syracuseStep 4891727 = 7337591) B7337591
theorem B4891841 : Blo 678312 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B1942775 : Blo 678312 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B763231 : Blo 678312 763231 := bstep (se 1 (by rfl) ⟨572423, by rfl⟩ : syracuseStep 763231 = 1144847) B1144847
theorem B3679867 : Blo 678312 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B4138685 : Blo 678312 4138685 := bstep (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) B1552007
theorem B763591 : Blo 678312 763591 := bstep (se 1 (by rfl) ⟨572693, by rfl⟩ : syracuseStep 763591 = 1145387) B1145387
theorem B5515067 : Blo 678312 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B1451963 : Blo 678312 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B7743437 : Blo 678312 7743437 := bstep (se 3 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 7743437 = 2903789) B2903789
theorem B764455 : Blo 678312 764455 := bstep (se 1 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 764455 = 1146683) B1146683
theorem B1223417 : Blo 678312 1223417 := bstep (se 2 (by rfl) ⟨458781, by rfl⟩ : syracuseStep 1223417 = 917563) B917563
theorem B2173871 : Blo 678312 2173871 := bstep (se 1 (by rfl) ⟨1630403, by rfl⟩ : syracuseStep 2173871 = 3260807) B3260807
theorem B3452057 : Blo 678312 3452057 := bstep (se 2 (by rfl) ⟨1294521, by rfl⟩ : syracuseStep 3452057 = 2589043) B2589043
theorem B1092779 : Blo 678312 1092779 := bstep (se 1 (by rfl) ⟨819584, by rfl⟩ : syracuseStep 1092779 = 1639169) B1639169
theorem B2993609 : Blo 678312 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B4370219 : Blo 678312 4370219 := bstep (se 1 (by rfl) ⟨3277664, by rfl⟩ : syracuseStep 4370219 = 6555329) B6555329
theorem B5156945 : Blo 678312 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B766075 : Blo 678312 766075 := bstep (se 1 (by rfl) ⟨574556, by rfl⟩ : syracuseStep 766075 = 1149113) B1149113
theorem B995689 : Blo 678312 995689 := bstep (se 2 (by rfl) ⟨373383, by rfl⟩ : syracuseStep 995689 = 746767) B746767
theorem B1290809 : Blo 678312 1290809 := bstep (se 2 (by rfl) ⟨484053, by rfl⟩ : syracuseStep 1290809 = 968107) B968107
theorem B766543 : Blo 678312 766543 := bstep (se 1 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 766543 = 1149815) B1149815
theorem B1454689 : Blo 678312 1454689 := bstep (se 2 (by rfl) ⟨545508, by rfl⟩ : syracuseStep 1454689 = 1091017) B1091017
theorem B4895417 : Blo 678312 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B766939 : Blo 678312 766939 := bstep (se 1 (by rfl) ⟨575204, by rfl⟩ : syracuseStep 766939 = 1150409) B1150409
theorem B767407 : Blo 678312 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B2897707 : Blo 678312 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B1718111 : Blo 678312 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B2865233 : Blo 678312 2865233 := bstep (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) B2148925
theorem B1292411 : Blo 678312 1292411 := bstep (se 1 (by rfl) ⟨969308, by rfl⟩ : syracuseStep 1292411 = 1938617) B1938617
theorem B15350219 : Blo 678312 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1456679 : Blo 678312 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B1227343 : Blo 678312 1227343 := bstep (se 1 (by rfl) ⟨920507, by rfl⟩ : syracuseStep 1227343 = 1841015) B1841015
theorem B1292897 : Blo 678312 1292897 := bstep (se 2 (by rfl) ⟨484836, by rfl⟩ : syracuseStep 1292897 = 969673) B969673
theorem B1719215 : Blo 678312 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B1293239 : Blo 678312 1293239 := bstep (se 1 (by rfl) ⟨969929, by rfl⟩ : syracuseStep 1293239 = 1939859) B1939859
theorem B1162171 : Blo 678312 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B1293641 : Blo 678312 1293641 := bstep (se 2 (by rfl) ⟨485115, by rfl⟩ : syracuseStep 1293641 = 970231) B970231
theorem B4963727 : Blo 678312 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B1228727 : Blo 678312 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B1294355 : Blo 678312 1294355 := bstep (se 1 (by rfl) ⟨970766, by rfl⟩ : syracuseStep 1294355 = 1941533) B1941533
theorem B1294393 : Blo 678312 1294393 := bstep (se 2 (by rfl) ⟨485397, by rfl⟩ : syracuseStep 1294393 = 970795) B970795
theorem B1720399 : Blo 678312 1720399 := bstep (se 1 (by rfl) ⟨1290299, by rfl⟩ : syracuseStep 1720399 = 2580599) B2580599
theorem B2900083 : Blo 678312 2900083 := bstep (se 1 (by rfl) ⟨2175062, by rfl⟩ : syracuseStep 2900083 = 4350125) B4350125
theorem B1294697 : Blo 678312 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B6209921 : Blo 678312 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B967087 : Blo 678312 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B2212339 : Blo 678312 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1721047 : Blo 678312 1721047 := bstep (se 1 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 1721047 = 2581571) B2581571
theorem B5161805 : Blo 678312 5161805 := bstep (se 3 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 5161805 = 1935677) B1935677
theorem B1164251 : Blo 678312 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B1721351 : Blo 678312 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B4146347 : Blo 678312 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B967879 : Blo 678312 967879 := bstep (se 1 (by rfl) ⟨725909, by rfl⟩ : syracuseStep 967879 = 1451819) B1451819
theorem B59754131 : Blo 678312 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B5883911 : Blo 678312 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B7358521 : Blo 678312 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B4901273 : Blo 678312 4901273 := bstep (se 2 (by rfl) ⟨1837977, by rfl⟩ : syracuseStep 4901273 = 3675955) B3675955
theorem B16566707 : Blo 678312 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B1526471 : Blo 678312 1526471 := bstep (se 1 (by rfl) ⟨1144853, by rfl⟩ : syracuseStep 1526471 = 2289707) B2289707
theorem B1034951 : Blo 678312 1034951 := bstep (se 1 (by rfl) ⟨776213, by rfl⟩ : syracuseStep 1034951 = 1552427) B1552427
theorem B5819471 : Blo 678312 5819471 := bstep (se 1 (by rfl) ⟨4364603, by rfl⟩ : syracuseStep 5819471 = 8729207) B8729207
theorem B5164235 : Blo 678312 5164235 := bstep (se 1 (by rfl) ⟨3873176, by rfl⟩ : syracuseStep 5164235 = 7746353) B7746353
theorem B1723639 : Blo 678312 1723639 := bstep (se 1 (by rfl) ⟨1292729, by rfl⟩ : syracuseStep 1723639 = 2585459) B2585459
theorem B9817361 : Blo 678312 9817361 := bstep (se 2 (by rfl) ⟨3681510, by rfl⟩ : syracuseStep 9817361 = 7363021) B7363021
theorem B5229989 : Blo 678312 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B1723913 : Blo 678312 1723913 := bstep (se 2 (by rfl) ⟨646467, by rfl⟩ : syracuseStep 1723913 = 1292935) B1292935
theorem B1527335 : Blo 678312 1527335 := bstep (se 1 (by rfl) ⟨1145501, by rfl⟩ : syracuseStep 1527335 = 2291003) B2291003
theorem B1723943 : Blo 678312 1723943 := bstep (se 1 (by rfl) ⟨1292957, by rfl⟩ : syracuseStep 1723943 = 2585915) B2585915
theorem B2576195 : Blo 678312 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B1527659 : Blo 678312 1527659 := bstep (se 1 (by rfl) ⟨1145744, by rfl⟩ : syracuseStep 1527659 = 2291489) B2291489
theorem B1724267 : Blo 678312 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B1527713 : Blo 678312 1527713 := bstep (se 2 (by rfl) ⟨572892, by rfl⟩ : syracuseStep 1527713 = 1145785) B1145785
theorem B4182031 : Blo 678312 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B5820497 : Blo 678312 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B774343 : Blo 678312 774343 := bstep (se 1 (by rfl) ⟨580757, by rfl⟩ : syracuseStep 774343 = 1161515) B1161515
theorem B1528055 : Blo 678312 1528055 := bstep (se 1 (by rfl) ⟨1146041, by rfl⟩ : syracuseStep 1528055 = 2292083) B2292083
theorem B1724915 : Blo 678312 1724915 := bstep (se 1 (by rfl) ⟨1293686, by rfl⟩ : syracuseStep 1724915 = 2587373) B2587373
theorem B4707017 : Blo 678312 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B1528649 : Blo 678312 1528649 := bstep (se 2 (by rfl) ⟨573243, by rfl⟩ : syracuseStep 1528649 = 1146487) B1146487
theorem B1725371 : Blo 678312 1725371 := bstep (se 1 (by rfl) ⟨1294028, by rfl⟩ : syracuseStep 1725371 = 2588057) B2588057
theorem B5297125 : Blo 678312 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B3724289 : Blo 678312 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B2577865 : Blo 678312 2577865 := bstep (se 2 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 2577865 = 1933399) B1933399
theorem B1529441 : Blo 678312 1529441 := bstep (se 2 (by rfl) ⟨573540, by rfl⟩ : syracuseStep 1529441 = 1147081) B1147081
theorem B1726049 : Blo 678312 1726049 := bstep (se 2 (by rfl) ⟨647268, by rfl⟩ : syracuseStep 1726049 = 1294537) B1294537
theorem B2905739 : Blo 678312 2905739 := bstep (se 1 (by rfl) ⟨2179304, by rfl⟩ : syracuseStep 2905739 = 4358609) B4358609
theorem B2578169 : Blo 678312 2578169 := bstep (se 2 (by rfl) ⟨966813, by rfl⟩ : syracuseStep 2578169 = 1933627) B1933627
theorem B2578337 : Blo 678312 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B2578351 : Blo 678312 2578351 := bstep (se 1 (by rfl) ⟨1933763, by rfl⟩ : syracuseStep 2578351 = 3867527) B3867527
theorem B1529783 : Blo 678312 1529783 := bstep (se 1 (by rfl) ⟨1147337, by rfl⟩ : syracuseStep 1529783 = 2294675) B2294675
theorem B2185147 : Blo 678312 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B2185223 : Blo 678312 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B10442789 : Blo 678312 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B4970573 : Blo 678312 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B2906455 : Blo 678312 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B678319 : Blo 678312 678319 := bstep (se 1 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 678319 = 1017479) B1017479
theorem B678343 : Blo 678312 678343 := bstep (se 1 (by rfl) ⟨508757, by rfl⟩ : syracuseStep 678343 = 1017515) B1017515
theorem B678363 : Blo 678312 678363 := bstep (se 1 (by rfl) ⟨508772, by rfl⟩ : syracuseStep 678363 = 1017545) B1017545
theorem B1530377 : Blo 678312 1530377 := bstep (se 2 (by rfl) ⟨573891, by rfl⟩ : syracuseStep 1530377 = 1147783) B1147783
theorem B678439 : Blo 678312 678439 := bstep (se 1 (by rfl) ⟨508829, by rfl⟩ : syracuseStep 678439 = 1017659) B1017659
theorem B678479 : Blo 678312 678479 := bstep (se 1 (by rfl) ⟨508859, by rfl⟩ : syracuseStep 678479 = 1017719) B1017719
theorem B678495 : Blo 678312 678495 := bstep (se 1 (by rfl) ⟨508871, by rfl⟩ : syracuseStep 678495 = 1017743) B1017743
theorem B678523 : Blo 678312 678523 := bstep (se 1 (by rfl) ⟨508892, by rfl⟩ : syracuseStep 678523 = 1017785) B1017785
theorem B678575 : Blo 678312 678575 := bstep (se 1 (by rfl) ⟨508931, by rfl⟩ : syracuseStep 678575 = 1017863) B1017863
theorem B5823161 : Blo 678312 5823161 := bstep (se 2 (by rfl) ⟨2183685, by rfl⟩ : syracuseStep 5823161 = 4367371) B4367371
theorem B678599 : Blo 678312 678599 := bstep (se 1 (by rfl) ⟨508949, by rfl⟩ : syracuseStep 678599 = 1017899) B1017899
theorem B678619 : Blo 678312 678619 := bstep (se 1 (by rfl) ⟨508964, by rfl⟩ : syracuseStep 678619 = 1017929) B1017929
theorem B678695 : Blo 678312 678695 := bstep (se 1 (by rfl) ⟨509021, by rfl⟩ : syracuseStep 678695 = 1018043) B1018043
theorem B9820997 : Blo 678312 9820997 := bstep (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) B1841437
theorem B678735 : Blo 678312 678735 := bstep (se 1 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 678735 = 1018103) B1018103
theorem B678751 : Blo 678312 678751 := bstep (se 1 (by rfl) ⟨509063, by rfl⟩ : syracuseStep 678751 = 1018127) B1018127
theorem B1530719 : Blo 678312 1530719 := bstep (se 1 (by rfl) ⟨1148039, by rfl⟩ : syracuseStep 1530719 = 2296079) B2296079
theorem B2579309 : Blo 678312 2579309 := bstep (se 3 (by rfl) ⟨483620, by rfl⟩ : syracuseStep 2579309 = 967241) B967241
theorem B678779 : Blo 678312 678779 := bstep (se 1 (by rfl) ⟨509084, by rfl⟩ : syracuseStep 678779 = 1018169) B1018169
theorem B678831 : Blo 678312 678831 := bstep (se 1 (by rfl) ⟨509123, by rfl⟩ : syracuseStep 678831 = 1018247) B1018247
theorem B678855 : Blo 678312 678855 := bstep (se 1 (by rfl) ⟨509141, by rfl⟩ : syracuseStep 678855 = 1018283) B1018283
theorem B678875 : Blo 678312 678875 := bstep (se 1 (by rfl) ⟨509156, by rfl⟩ : syracuseStep 678875 = 1018313) B1018313
theorem B1530899 : Blo 678312 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B678951 : Blo 678312 678951 := bstep (se 1 (by rfl) ⟨509213, by rfl⟩ : syracuseStep 678951 = 1018427) B1018427
theorem B678991 : Blo 678312 678991 := bstep (se 1 (by rfl) ⟨509243, by rfl⟩ : syracuseStep 678991 = 1018487) B1018487
theorem B679007 : Blo 678312 679007 := bstep (se 1 (by rfl) ⟨509255, by rfl⟩ : syracuseStep 679007 = 1018511) B1018511
theorem B679035 : Blo 678312 679035 := bstep (se 1 (by rfl) ⟨509276, by rfl⟩ : syracuseStep 679035 = 1018553) B1018553
theorem B2579627 : Blo 678312 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B679087 : Blo 678312 679087 := bstep (se 1 (by rfl) ⟨509315, by rfl⟩ : syracuseStep 679087 = 1018631) B1018631
theorem B4349123 : Blo 678312 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B679111 : Blo 678312 679111 := bstep (se 1 (by rfl) ⟨509333, by rfl⟩ : syracuseStep 679111 = 1018667) B1018667
theorem B679131 : Blo 678312 679131 := bstep (se 1 (by rfl) ⟨509348, by rfl⟩ : syracuseStep 679131 = 1018697) B1018697
theorem B679207 : Blo 678312 679207 := bstep (se 1 (by rfl) ⟨509405, by rfl⟩ : syracuseStep 679207 = 1018811) B1018811
theorem B679247 : Blo 678312 679247 := bstep (se 1 (by rfl) ⟨509435, by rfl⟩ : syracuseStep 679247 = 1018871) B1018871
theorem B679263 : Blo 678312 679263 := bstep (se 1 (by rfl) ⟨509447, by rfl⟩ : syracuseStep 679263 = 1018895) B1018895
theorem B1531241 : Blo 678312 1531241 := bstep (se 2 (by rfl) ⟨574215, by rfl⟩ : syracuseStep 1531241 = 1148431) B1148431
theorem B679291 : Blo 678312 679291 := bstep (se 1 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 679291 = 1018937) B1018937
theorem B679343 : Blo 678312 679343 := bstep (se 1 (by rfl) ⟨509507, by rfl⟩ : syracuseStep 679343 = 1019015) B1019015
theorem B679367 : Blo 678312 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B679387 : Blo 678312 679387 := bstep (se 1 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 679387 = 1019081) B1019081
theorem B679463 : Blo 678312 679463 := bstep (se 1 (by rfl) ⟨509597, by rfl⟩ : syracuseStep 679463 = 1019195) B1019195
theorem B679503 : Blo 678312 679503 := bstep (se 1 (by rfl) ⟨509627, by rfl⟩ : syracuseStep 679503 = 1019255) B1019255
theorem B679519 : Blo 678312 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B679547 : Blo 678312 679547 := bstep (se 1 (by rfl) ⟨509660, by rfl⟩ : syracuseStep 679547 = 1019321) B1019321
theorem B679599 : Blo 678312 679599 := bstep (se 1 (by rfl) ⟨509699, by rfl⟩ : syracuseStep 679599 = 1019399) B1019399
theorem B679623 : Blo 678312 679623 := bstep (se 1 (by rfl) ⟨509717, by rfl⟩ : syracuseStep 679623 = 1019435) B1019435
theorem B679643 : Blo 678312 679643 := bstep (se 1 (by rfl) ⟨509732, by rfl⟩ : syracuseStep 679643 = 1019465) B1019465
theorem B679719 : Blo 678312 679719 := bstep (se 1 (by rfl) ⟨509789, by rfl⟩ : syracuseStep 679719 = 1019579) B1019579
theorem B679759 : Blo 678312 679759 := bstep (se 1 (by rfl) ⟨509819, by rfl⟩ : syracuseStep 679759 = 1019639) B1019639
theorem B679775 : Blo 678312 679775 := bstep (se 1 (by rfl) ⟨509831, by rfl⟩ : syracuseStep 679775 = 1019663) B1019663
theorem B679803 : Blo 678312 679803 := bstep (se 1 (by rfl) ⟨509852, by rfl⟩ : syracuseStep 679803 = 1019705) B1019705
theorem B679855 : Blo 678312 679855 := bstep (se 1 (by rfl) ⟨509891, by rfl⟩ : syracuseStep 679855 = 1019783) B1019783
theorem B1531835 : Blo 678312 1531835 := bstep (se 1 (by rfl) ⟨1148876, by rfl⟩ : syracuseStep 1531835 = 2297753) B2297753
theorem B679879 : Blo 678312 679879 := bstep (se 1 (by rfl) ⟨509909, by rfl⟩ : syracuseStep 679879 = 1019819) B1019819
theorem B679899 : Blo 678312 679899 := bstep (se 1 (by rfl) ⟨509924, by rfl⟩ : syracuseStep 679899 = 1019849) B1019849
theorem B679975 : Blo 678312 679975 := bstep (se 1 (by rfl) ⟨509981, by rfl⟩ : syracuseStep 679975 = 1019963) B1019963
theorem B1531961 : Blo 678312 1531961 := bstep (se 2 (by rfl) ⟨574485, by rfl⟩ : syracuseStep 1531961 = 1148971) B1148971
theorem B680015 : Blo 678312 680015 := bstep (se 1 (by rfl) ⟨510011, by rfl⟩ : syracuseStep 680015 = 1020023) B1020023
theorem B680031 : Blo 678312 680031 := bstep (se 1 (by rfl) ⟨510023, by rfl⟩ : syracuseStep 680031 = 1020047) B1020047
theorem B680059 : Blo 678312 680059 := bstep (se 1 (by rfl) ⟨510044, by rfl⟩ : syracuseStep 680059 = 1020089) B1020089
theorem B680111 : Blo 678312 680111 := bstep (se 1 (by rfl) ⟨510083, by rfl⟩ : syracuseStep 680111 = 1020167) B1020167
theorem B680135 : Blo 678312 680135 := bstep (se 1 (by rfl) ⟨510101, by rfl⟩ : syracuseStep 680135 = 1020203) B1020203
theorem B680155 : Blo 678312 680155 := bstep (se 1 (by rfl) ⟨510116, by rfl⟩ : syracuseStep 680155 = 1020233) B1020233
theorem B680231 : Blo 678312 680231 := bstep (se 1 (by rfl) ⟨510173, by rfl⟩ : syracuseStep 680231 = 1020347) B1020347
theorem B680271 : Blo 678312 680271 := bstep (se 1 (by rfl) ⟨510203, by rfl⟩ : syracuseStep 680271 = 1020407) B1020407
theorem B680287 : Blo 678312 680287 := bstep (se 1 (by rfl) ⟨510215, by rfl⟩ : syracuseStep 680287 = 1020431) B1020431
theorem B13066595 : Blo 678312 13066595 := bstep (se 1 (by rfl) ⟨9799946, by rfl⟩ : syracuseStep 13066595 = 19599893) B19599893
theorem B39739747 : Blo 678312 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B680315 : Blo 678312 680315 := bstep (se 1 (by rfl) ⟨510236, by rfl⟩ : syracuseStep 680315 = 1020473) B1020473
theorem B1532303 : Blo 678312 1532303 := bstep (se 1 (by rfl) ⟨1149227, by rfl⟩ : syracuseStep 1532303 = 2298455) B2298455
theorem B680367 : Blo 678312 680367 := bstep (se 1 (by rfl) ⟨510275, by rfl⟩ : syracuseStep 680367 = 1020551) B1020551
theorem B680391 : Blo 678312 680391 := bstep (se 1 (by rfl) ⟨510293, by rfl⟩ : syracuseStep 680391 = 1020587) B1020587
theorem B680411 : Blo 678312 680411 := bstep (se 1 (by rfl) ⟨510308, by rfl⟩ : syracuseStep 680411 = 1020617) B1020617
theorem B680487 : Blo 678312 680487 := bstep (se 1 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 680487 = 1020731) B1020731
theorem B680527 : Blo 678312 680527 := bstep (se 1 (by rfl) ⟨510395, by rfl⟩ : syracuseStep 680527 = 1020791) B1020791
theorem B680543 : Blo 678312 680543 := bstep (se 1 (by rfl) ⟨510407, by rfl⟩ : syracuseStep 680543 = 1020815) B1020815
theorem B680571 : Blo 678312 680571 := bstep (se 1 (by rfl) ⟨510428, by rfl⟩ : syracuseStep 680571 = 1020857) B1020857
theorem B680623 : Blo 678312 680623 := bstep (se 1 (by rfl) ⟨510467, by rfl⟩ : syracuseStep 680623 = 1020935) B1020935
theorem B680647 : Blo 678312 680647 := bstep (se 1 (by rfl) ⟨510485, by rfl⟩ : syracuseStep 680647 = 1020971) B1020971
theorem B1532627 : Blo 678312 1532627 := bstep (se 1 (by rfl) ⟨1149470, by rfl⟩ : syracuseStep 1532627 = 2298941) B2298941
theorem B680667 : Blo 678312 680667 := bstep (se 1 (by rfl) ⟨510500, by rfl⟩ : syracuseStep 680667 = 1021001) B1021001
theorem B680743 : Blo 678312 680743 := bstep (se 1 (by rfl) ⟨510557, by rfl⟩ : syracuseStep 680743 = 1021115) B1021115
theorem B680783 : Blo 678312 680783 := bstep (se 1 (by rfl) ⟨510587, by rfl⟩ : syracuseStep 680783 = 1021175) B1021175
theorem B680799 : Blo 678312 680799 := bstep (se 1 (by rfl) ⟨510599, by rfl⟩ : syracuseStep 680799 = 1021199) B1021199
theorem B680827 : Blo 678312 680827 := bstep (se 1 (by rfl) ⟨510620, by rfl⟩ : syracuseStep 680827 = 1021241) B1021241
theorem B5170067 : Blo 678312 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B680879 : Blo 678312 680879 := bstep (se 1 (by rfl) ⟨510659, by rfl⟩ : syracuseStep 680879 = 1021319) B1021319
theorem B680903 : Blo 678312 680903 := bstep (se 1 (by rfl) ⟨510677, by rfl⟩ : syracuseStep 680903 = 1021355) B1021355
theorem B680923 : Blo 678312 680923 := bstep (se 1 (by rfl) ⟨510692, by rfl⟩ : syracuseStep 680923 = 1021385) B1021385
theorem B680999 : Blo 678312 680999 := bstep (se 1 (by rfl) ⟨510749, by rfl⟩ : syracuseStep 680999 = 1021499) B1021499
theorem B681039 : Blo 678312 681039 := bstep (se 1 (by rfl) ⟨510779, by rfl⟩ : syracuseStep 681039 = 1021559) B1021559
theorem B681055 : Blo 678312 681055 := bstep (se 1 (by rfl) ⟨510791, by rfl⟩ : syracuseStep 681055 = 1021583) B1021583
theorem B681083 : Blo 678312 681083 := bstep (se 1 (by rfl) ⟨510812, by rfl⟩ : syracuseStep 681083 = 1021625) B1021625
theorem B681135 : Blo 678312 681135 := bstep (se 1 (by rfl) ⟨510851, by rfl⟩ : syracuseStep 681135 = 1021703) B1021703
theorem B681159 : Blo 678312 681159 := bstep (se 1 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 681159 = 1021739) B1021739
theorem B681179 : Blo 678312 681179 := bstep (se 1 (by rfl) ⟨510884, by rfl⟩ : syracuseStep 681179 = 1021769) B1021769
theorem B681255 : Blo 678312 681255 := bstep (se 1 (by rfl) ⟨510941, by rfl⟩ : syracuseStep 681255 = 1021883) B1021883
theorem B681295 : Blo 678312 681295 := bstep (se 1 (by rfl) ⟨510971, by rfl⟩ : syracuseStep 681295 = 1021943) B1021943
theorem B681311 : Blo 678312 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B681339 : Blo 678312 681339 := bstep (se 1 (by rfl) ⟨511004, by rfl⟩ : syracuseStep 681339 = 1022009) B1022009
theorem B681391 : Blo 678312 681391 := bstep (se 1 (by rfl) ⟨511043, by rfl⟩ : syracuseStep 681391 = 1022087) B1022087
theorem B681415 : Blo 678312 681415 := bstep (se 1 (by rfl) ⟨511061, by rfl⟩ : syracuseStep 681415 = 1022123) B1022123
theorem B18703817 : Blo 678312 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B681435 : Blo 678312 681435 := bstep (se 1 (by rfl) ⟨511076, by rfl⟩ : syracuseStep 681435 = 1022153) B1022153
theorem B681511 : Blo 678312 681511 := bstep (se 1 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 681511 = 1022267) B1022267
theorem B681551 : Blo 678312 681551 := bstep (se 1 (by rfl) ⟨511163, by rfl⟩ : syracuseStep 681551 = 1022327) B1022327
theorem B681567 : Blo 678312 681567 := bstep (se 1 (by rfl) ⟨511175, by rfl⟩ : syracuseStep 681567 = 1022351) B1022351
theorem B2647675 : Blo 678312 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B1533563 : Blo 678312 1533563 := bstep (se 1 (by rfl) ⟨1150172, by rfl⟩ : syracuseStep 1533563 = 2300345) B2300345
theorem B681595 : Blo 678312 681595 := bstep (se 1 (by rfl) ⟨511196, by rfl⟩ : syracuseStep 681595 = 1022393) B1022393
theorem B681647 : Blo 678312 681647 := bstep (se 1 (by rfl) ⟨511235, by rfl⟩ : syracuseStep 681647 = 1022471) B1022471
theorem B681671 : Blo 678312 681671 := bstep (se 1 (by rfl) ⟨511253, by rfl⟩ : syracuseStep 681671 = 1022507) B1022507
theorem B2582225 : Blo 678312 2582225 := bstep (se 2 (by rfl) ⟨968334, by rfl⟩ : syracuseStep 2582225 = 1936669) B1936669
theorem B681691 : Blo 678312 681691 := bstep (se 1 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 681691 = 1022537) B1022537
theorem B1533689 : Blo 678312 1533689 := bstep (se 2 (by rfl) ⟨575133, by rfl⟩ : syracuseStep 1533689 = 1150267) B1150267
theorem B681767 : Blo 678312 681767 := bstep (se 1 (by rfl) ⟨511325, by rfl⟩ : syracuseStep 681767 = 1022651) B1022651
theorem B29812531 : Blo 678312 29812531 := bstep (se 1 (by rfl) ⟨22359398, by rfl⟩ : syracuseStep 29812531 = 44718797) B44718797
theorem B681807 : Blo 678312 681807 := bstep (se 1 (by rfl) ⟨511355, by rfl⟩ : syracuseStep 681807 = 1022711) B1022711
theorem B5171039 : Blo 678312 5171039 := bstep (se 1 (by rfl) ⟨3878279, by rfl⟩ : syracuseStep 5171039 = 7756559) B7756559
theorem B681823 : Blo 678312 681823 := bstep (se 1 (by rfl) ⟨511367, by rfl⟩ : syracuseStep 681823 = 1022735) B1022735
theorem B681851 : Blo 678312 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B2910113 : Blo 678312 2910113 := bstep (se 2 (by rfl) ⟨1091292, by rfl⟩ : syracuseStep 2910113 = 2182585) B2182585
theorem B681903 : Blo 678312 681903 := bstep (se 1 (by rfl) ⟨511427, by rfl⟩ : syracuseStep 681903 = 1022855) B1022855
theorem B681927 : Blo 678312 681927 := bstep (se 1 (by rfl) ⟨511445, by rfl⟩ : syracuseStep 681927 = 1022891) B1022891
theorem B681947 : Blo 678312 681947 := bstep (se 1 (by rfl) ⟨511460, by rfl⟩ : syracuseStep 681947 = 1022921) B1022921
theorem B1533959 : Blo 678312 1533959 := bstep (se 1 (by rfl) ⟨1150469, by rfl⟩ : syracuseStep 1533959 = 2300939) B2300939
theorem B2582543 : Blo 678312 2582543 := bstep (se 1 (by rfl) ⟨1936907, by rfl⟩ : syracuseStep 2582543 = 3873815) B3873815
theorem B682023 : Blo 678312 682023 := bstep (se 1 (by rfl) ⟨511517, by rfl⟩ : syracuseStep 682023 = 1023035) B1023035
theorem B1534031 : Blo 678312 1534031 := bstep (se 1 (by rfl) ⟨1150523, by rfl⟩ : syracuseStep 1534031 = 2301047) B2301047
theorem B682063 : Blo 678312 682063 := bstep (se 1 (by rfl) ⟨511547, by rfl⟩ : syracuseStep 682063 = 1023095) B1023095
theorem B2615377 : Blo 678312 2615377 := bstep (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) B1961533
theorem B682079 : Blo 678312 682079 := bstep (se 1 (by rfl) ⟨511559, by rfl⟩ : syracuseStep 682079 = 1023119) B1023119
theorem B682107 : Blo 678312 682107 := bstep (se 1 (by rfl) ⟨511580, by rfl⟩ : syracuseStep 682107 = 1023161) B1023161
theorem B17688709 : Blo 678312 17688709 := bstep (se 4 (by rfl) ⟨1658316, by rfl⟩ : syracuseStep 17688709 = 3316633) B3316633
theorem B682159 : Blo 678312 682159 := bstep (se 1 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 682159 = 1023239) B1023239
theorem B682183 : Blo 678312 682183 := bstep (se 1 (by rfl) ⟨511637, by rfl⟩ : syracuseStep 682183 = 1023275) B1023275
theorem B682203 : Blo 678312 682203 := bstep (se 1 (by rfl) ⟨511652, by rfl⟩ : syracuseStep 682203 = 1023305) B1023305
theorem B682279 : Blo 678312 682279 := bstep (se 1 (by rfl) ⟨511709, by rfl⟩ : syracuseStep 682279 = 1023419) B1023419
theorem B13101497 : Blo 678312 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B1534427 : Blo 678312 1534427 := bstep (se 1 (by rfl) ⟨1150820, by rfl⟩ : syracuseStep 1534427 = 2301641) B2301641
theorem B3435371 : Blo 678312 3435371 := bstep (se 1 (by rfl) ⟨2576528, by rfl⟩ : syracuseStep 3435371 = 5153057) B5153057
theorem B1534895 : Blo 678312 1534895 := bstep (se 1 (by rfl) ⟨1151171, by rfl⟩ : syracuseStep 1534895 = 2302343) B2302343
theorem B1535147 : Blo 678312 1535147 := bstep (se 1 (by rfl) ⟨1151360, by rfl⟩ : syracuseStep 1535147 = 2302721) B2302721
theorem B3436019 : Blo 678312 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B5828219 : Blo 678312 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B2289437 : Blo 678312 2289437 := bstep (se 3 (by rfl) ⟨429269, by rfl⟩ : syracuseStep 2289437 = 858539) B858539
theorem B2453291 : Blo 678312 2453291 := bstep (se 1 (by rfl) ⟨1839968, by rfl⟩ : syracuseStep 2453291 = 3679937) B3679937
theorem B1961903 : Blo 678312 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B2584655 : Blo 678312 2584655 := bstep (se 1 (by rfl) ⟨1938491, by rfl⟩ : syracuseStep 2584655 = 3876983) B3876983
theorem B815303 : Blo 678312 815303 := bstep (se 1 (by rfl) ⟨611477, by rfl⟩ : syracuseStep 815303 = 1222955) B1222955
theorem B5501245 : Blo 678312 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B1634689 : Blo 678312 1634689 := bstep (se 2 (by rfl) ⟨613008, by rfl⟩ : syracuseStep 1634689 = 1226017) B1226017
theorem B2290139 : Blo 678312 2290139 := bstep (se 1 (by rfl) ⟨1717604, by rfl⟩ : syracuseStep 2290139 = 3435209) B3435209
theorem B3437315 : Blo 678312 3437315 := bstep (se 1 (by rfl) ⟨2577986, by rfl⟩ : syracuseStep 3437315 = 5155973) B5155973
theorem B2290841 : Blo 678312 2290841 := bstep (se 2 (by rfl) ⟨859065, by rfl⟩ : syracuseStep 2290841 = 1718131) B1718131
theorem B1635689 : Blo 678312 1635689 := bstep (se 2 (by rfl) ⟨613383, by rfl⟩ : syracuseStep 1635689 = 1226767) B1226767
theorem B10614179 : Blo 678312 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B2618825 : Blo 678312 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B20936333 : Blo 678312 20936333 := bstep (se 3 (by rfl) ⟨3925562, by rfl⟩ : syracuseStep 20936333 = 7851125) B7851125
theorem B7960313 : Blo 678312 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B1144759 : Blo 678312 1144759 := bstep (se 1 (by rfl) ⟨858569, by rfl⟩ : syracuseStep 1144759 = 1717139) B1717139
theorem B3274759 : Blo 678312 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B2455609 : Blo 678312 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B1144955 : Blo 678312 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B169834765 : Blo 678312 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B2292029 : Blo 678312 2292029 := bstep (se 3 (by rfl) ⟨429755, by rfl⟩ : syracuseStep 2292029 = 859511) B859511
theorem B3438935 : Blo 678312 3438935 := bstep (se 1 (by rfl) ⟨2579201, by rfl⟩ : syracuseStep 3438935 = 5158403) B5158403
theorem B9926999 : Blo 678312 9926999 := bstep (se 1 (by rfl) ⟨7445249, by rfl⟩ : syracuseStep 9926999 = 14890499) B14890499
theorem B2587099 : Blo 678312 2587099 := bstep (se 1 (by rfl) ⟨1940324, by rfl⟩ : syracuseStep 2587099 = 3880649) B3880649
theorem B1145353 : Blo 678312 1145353 := bstep (se 2 (by rfl) ⟨429507, by rfl⟩ : syracuseStep 1145353 = 859015) B859015
theorem B1145515 : Blo 678312 1145515 := bstep (se 1 (by rfl) ⟨859136, by rfl⟩ : syracuseStep 1145515 = 1718273) B1718273
theorem B1931987 : Blo 678312 1931987 := bstep (se 1 (by rfl) ⟨1448990, by rfl⟩ : syracuseStep 1931987 = 2897981) B2897981
theorem B1145819 : Blo 678312 1145819 := bstep (se 1 (by rfl) ⟨859364, by rfl⟩ : syracuseStep 1145819 = 1718729) B1718729
theorem B1932295 : Blo 678312 1932295 := bstep (se 1 (by rfl) ⟨1449221, by rfl⟩ : syracuseStep 1932295 = 2898443) B2898443
theorem B18611279 : Blo 678312 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B4652185 : Blo 678312 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B2292893 : Blo 678312 2292893 := bstep (se 3 (by rfl) ⟨429917, by rfl⟩ : syracuseStep 2292893 = 859835) B859835
theorem B1146055 : Blo 678312 1146055 := bstep (se 1 (by rfl) ⟨859541, by rfl⟩ : syracuseStep 1146055 = 1719083) B1719083
theorem B1146217 : Blo 678312 1146217 := bstep (se 2 (by rfl) ⟨429831, by rfl⟩ : syracuseStep 1146217 = 859663) B859663
theorem B181140941 : Blo 678312 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1342985 : Blo 678312 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B5176871 : Blo 678312 5176871 := bstep (se 1 (by rfl) ⟨3882653, by rfl⟩ : syracuseStep 5176871 = 7765307) B7765307
theorem B3866251 : Blo 678312 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B2293433 : Blo 678312 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B2588345 : Blo 678312 2588345 := bstep (se 2 (by rfl) ⟨970629, by rfl⟩ : syracuseStep 2588345 = 1941259) B1941259
theorem B2588375 : Blo 678312 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B1933217 : Blo 678312 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B1146811 : Blo 678312 1146811 := bstep (se 1 (by rfl) ⟨860108, by rfl⟩ : syracuseStep 1146811 = 1720217) B1720217
theorem B17465381 : Blo 678312 17465381 := bstep (se 4 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 17465381 = 3274759) B3274759
theorem B2293865 : Blo 678312 2293865 := bstep (se 2 (by rfl) ⟨860199, by rfl⟩ : syracuseStep 2293865 = 1720399) B1720399
theorem B3866777 : Blo 678312 3866777 := bstep (se 2 (by rfl) ⟨1450041, by rfl⟩ : syracuseStep 3866777 = 2900083) B2900083
theorem B52986329 : Blo 678312 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B3441203 : Blo 678312 3441203 := bstep (se 1 (by rfl) ⟨2580902, by rfl⟩ : syracuseStep 3441203 = 5161805) B5161805
theorem B1147513 : Blo 678312 1147513 := bstep (se 2 (by rfl) ⟨430317, by rfl⟩ : syracuseStep 1147513 = 860635) B860635
theorem B2949785 : Blo 678312 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1147567 : Blo 678312 1147567 := bstep (se 1 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 1147567 = 1721351) B1721351
theorem B2294729 : Blo 678312 2294729 := bstep (se 2 (by rfl) ⟨860523, by rfl⟩ : syracuseStep 2294729 = 1721047) B1721047
theorem B2294999 : Blo 678312 2294999 := bstep (se 1 (by rfl) ⟨1721249, by rfl⟩ : syracuseStep 2294999 = 3442499) B3442499
theorem B2459069 : Blo 678312 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B11044471 : Blo 678312 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B1017641 : Blo 678312 1017641 := bstep (se 2 (by rfl) ⟨381615, by rfl⟩ : syracuseStep 1017641 = 763231) B763231
theorem B18876203 : Blo 678312 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B1017647 : Blo 678312 1017647 := bstep (se 1 (by rfl) ⟨763235, by rfl⟩ : syracuseStep 1017647 = 1526471) B1526471
theorem B3442823 : Blo 678312 3442823 := bstep (se 1 (by rfl) ⟨2582117, by rfl⟩ : syracuseStep 3442823 = 5164235) B5164235
theorem B1018121 : Blo 678312 1018121 := bstep (se 2 (by rfl) ⟨381795, by rfl⟩ : syracuseStep 1018121 = 763591) B763591
theorem B1149275 : Blo 678312 1149275 := bstep (se 1 (by rfl) ⟨861956, by rfl⟩ : syracuseStep 1149275 = 1723913) B1723913
theorem B1018223 : Blo 678312 1018223 := bstep (se 1 (by rfl) ⟨763667, by rfl⟩ : syracuseStep 1018223 = 1527335) B1527335
theorem B1149295 : Blo 678312 1149295 := bstep (se 1 (by rfl) ⟨861971, by rfl⟩ : syracuseStep 1149295 = 1723943) B1723943
theorem B39750041 : Blo 678312 39750041 := bstep (se 2 (by rfl) ⟨14906265, by rfl⟩ : syracuseStep 39750041 = 29812531) B29812531
theorem B1182203 : Blo 678312 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B1018439 : Blo 678312 1018439 := bstep (se 1 (by rfl) ⟨763829, by rfl⟩ : syracuseStep 1018439 = 1527659) B1527659
theorem B1149511 : Blo 678312 1149511 := bstep (se 1 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 1149511 = 1724267) B1724267
theorem B1018475 : Blo 678312 1018475 := bstep (se 1 (by rfl) ⟨763856, by rfl⟩ : syracuseStep 1018475 = 1527713) B1527713
theorem B2951927 : Blo 678312 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B1018703 : Blo 678312 1018703 := bstep (se 1 (by rfl) ⟨764027, by rfl⟩ : syracuseStep 1018703 = 1528055) B1528055
theorem B920551 : Blo 678312 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B1149943 : Blo 678312 1149943 := bstep (se 1 (by rfl) ⟨862457, by rfl⟩ : syracuseStep 1149943 = 1724915) B1724915
theorem B1019099 : Blo 678312 1019099 := bstep (se 1 (by rfl) ⟨764324, by rfl⟩ : syracuseStep 1019099 = 1528649) B1528649
theorem B2297051 : Blo 678312 2297051 := bstep (se 1 (by rfl) ⟨1722788, by rfl⟩ : syracuseStep 2297051 = 3445577) B3445577
theorem B1150247 : Blo 678312 1150247 := bstep (se 1 (by rfl) ⟨862685, by rfl⟩ : syracuseStep 1150247 = 1725371) B1725371
theorem B1019273 : Blo 678312 1019273 := bstep (se 2 (by rfl) ⟨382227, by rfl⟩ : syracuseStep 1019273 = 764455) B764455
theorem B3870443 : Blo 678312 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B1019627 : Blo 678312 1019627 := bstep (se 1 (by rfl) ⟨764720, by rfl⟩ : syracuseStep 1019627 = 1529441) B1529441
theorem B1150699 : Blo 678312 1150699 := bstep (se 1 (by rfl) ⟨863024, by rfl⟩ : syracuseStep 1150699 = 1726049) B1726049
theorem B1937159 : Blo 678312 1937159 := bstep (se 1 (by rfl) ⟨1452869, by rfl⟩ : syracuseStep 1937159 = 2905739) B2905739
theorem B6983533 : Blo 678312 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B6557597 : Blo 678312 6557597 := bstep (se 3 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 6557597 = 2459099) B2459099
theorem B1019855 : Blo 678312 1019855 := bstep (se 1 (by rfl) ⟨764891, by rfl⟩ : syracuseStep 1019855 = 1529783) B1529783
theorem B3313715 : Blo 678312 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B2297915 : Blo 678312 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B2298185 : Blo 678312 2298185 := bstep (se 2 (by rfl) ⟨861819, by rfl⟩ : syracuseStep 2298185 = 1723639) B1723639
theorem B1020251 : Blo 678312 1020251 := bstep (se 1 (by rfl) ⟨765188, by rfl⟩ : syracuseStep 1020251 = 1530377) B1530377
theorem B3871151 : Blo 678312 3871151 := bstep (se 1 (by rfl) ⟨2903363, by rfl⟩ : syracuseStep 3871151 = 5806727) B5806727
theorem B1020479 : Blo 678312 1020479 := bstep (se 1 (by rfl) ⟨765359, by rfl⟩ : syracuseStep 1020479 = 1530719) B1530719
theorem B1020599 : Blo 678312 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B725807 : Blo 678312 725807 := bstep (se 1 (by rfl) ⟨544355, by rfl⟩ : syracuseStep 725807 = 1088711) B1088711
theorem B8262479 : Blo 678312 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B1020827 : Blo 678312 1020827 := bstep (se 1 (by rfl) ⟨765620, by rfl⟩ : syracuseStep 1020827 = 1531241) B1531241
theorem B3871901 : Blo 678312 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B1021223 : Blo 678312 1021223 := bstep (se 1 (by rfl) ⟨765917, by rfl⟩ : syracuseStep 1021223 = 1531835) B1531835
theorem B1021307 : Blo 678312 1021307 := bstep (se 1 (by rfl) ⟨765980, by rfl⟩ : syracuseStep 1021307 = 1531961) B1531961
theorem B1840583 : Blo 678312 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B1021433 : Blo 678312 1021433 := bstep (se 2 (by rfl) ⟨383037, by rfl⟩ : syracuseStep 1021433 = 766075) B766075
theorem B1021535 : Blo 678312 1021535 := bstep (se 1 (by rfl) ⟨766151, by rfl⟩ : syracuseStep 1021535 = 1532303) B1532303
theorem B1021751 : Blo 678312 1021751 := bstep (se 1 (by rfl) ⟨766313, by rfl⟩ : syracuseStep 1021751 = 1532627) B1532627
theorem B3446711 : Blo 678312 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B1022057 : Blo 678312 1022057 := bstep (se 2 (by rfl) ⟨383271, by rfl⟩ : syracuseStep 1022057 = 766543) B766543
theorem B1939585 : Blo 678312 1939585 := bstep (se 2 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 1939585 = 1454689) B1454689
theorem B1022375 : Blo 678312 1022375 := bstep (se 1 (by rfl) ⟨766781, by rfl⟩ : syracuseStep 1022375 = 1533563) B1533563
theorem B2759123 : Blo 678312 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B1022459 : Blo 678312 1022459 := bstep (se 1 (by rfl) ⟨766844, by rfl⟩ : syracuseStep 1022459 = 1533689) B1533689
theorem B3447359 : Blo 678312 3447359 := bstep (se 1 (by rfl) ⟨2585519, by rfl⟩ : syracuseStep 3447359 = 5171039) B5171039
theorem B1940075 : Blo 678312 1940075 := bstep (se 1 (by rfl) ⟨1455056, by rfl⟩ : syracuseStep 1940075 = 2910113) B2910113
theorem B1022585 : Blo 678312 1022585 := bstep (se 2 (by rfl) ⟨383469, by rfl⟩ : syracuseStep 1022585 = 766939) B766939
theorem B1022639 : Blo 678312 1022639 := bstep (se 1 (by rfl) ⟨766979, by rfl⟩ : syracuseStep 1022639 = 1533959) B1533959
theorem B1022687 : Blo 678312 1022687 := bstep (se 1 (by rfl) ⟨767015, by rfl⟩ : syracuseStep 1022687 = 1534031) B1534031
theorem B1022951 : Blo 678312 1022951 := bstep (se 1 (by rfl) ⟨767213, by rfl⟩ : syracuseStep 1022951 = 1534427) B1534427
theorem B2759869 : Blo 678312 2759869 := bstep (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) B1034951
theorem B1023209 : Blo 678312 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B1449247 : Blo 678312 1449247 := bstep (se 1 (by rfl) ⟨1086935, by rfl⟩ : syracuseStep 1449247 = 2173871) B2173871
theorem B1023263 : Blo 678312 1023263 := bstep (se 1 (by rfl) ⟨767447, by rfl⟩ : syracuseStep 1023263 = 1534895) B1534895
theorem B2301371 : Blo 678312 2301371 := bstep (se 1 (by rfl) ⟨1726028, by rfl⟩ : syracuseStep 2301371 = 3452057) B3452057
theorem B728519 : Blo 678312 728519 := bstep (se 1 (by rfl) ⟨546389, by rfl⟩ : syracuseStep 728519 = 1092779) B1092779
theorem B1023431 : Blo 678312 1023431 := bstep (se 1 (by rfl) ⟨767573, by rfl⟩ : syracuseStep 1023431 = 1535147) B1535147
theorem B1843049 : Blo 678312 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B860539 : Blo 678312 860539 := bstep (se 1 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 860539 = 1290809) B1290809
theorem B3875273 : Blo 678312 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B3449465 : Blo 678312 3449465 := bstep (se 2 (by rfl) ⟨1293549, by rfl⟩ : syracuseStep 3449465 = 2587099) B2587099
theorem B1090459 : Blo 678312 1090459 := bstep (se 1 (by rfl) ⟨817844, by rfl⟩ : syracuseStep 1090459 = 1635689) B1635689
theorem B1549561 : Blo 678312 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B3581293 : Blo 678312 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B1910155 : Blo 678312 1910155 := bstep (se 1 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 1910155 = 2865233) B2865233
theorem B763303 : Blo 678312 763303 := bstep (se 1 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 763303 = 1144955) B1144955
theorem B861607 : Blo 678312 861607 := bstep (se 1 (by rfl) ⟨646205, by rfl⟩ : syracuseStep 861607 = 1292411) B1292411
theorem B6202913 : Blo 678312 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B10233479 : Blo 678312 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B861931 : Blo 678312 861931 := bstep (se 1 (by rfl) ⟨646448, by rfl⟩ : syracuseStep 861931 = 1292897) B1292897
theorem B1287991 : Blo 678312 1287991 := bstep (se 1 (by rfl) ⟨965993, by rfl⟩ : syracuseStep 1287991 = 1931987) B1931987
theorem B862159 : Blo 678312 862159 := bstep (se 1 (by rfl) ⟨646619, by rfl⟩ : syracuseStep 862159 = 1293239) B1293239
theorem B763879 : Blo 678312 763879 := bstep (se 1 (by rfl) ⟨572909, by rfl⟩ : syracuseStep 763879 = 1145819) B1145819
theorem B5155001 : Blo 678312 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B862427 : Blo 678312 862427 := bstep (se 1 (by rfl) ⟨646820, by rfl⟩ : syracuseStep 862427 = 1293641) B1293641
theorem B2763017 : Blo 678312 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B120760627 : Blo 678312 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B3451247 : Blo 678312 3451247 := bstep (se 1 (by rfl) ⟨2588435, by rfl⟩ : syracuseStep 3451247 = 5176871) B5176871
theorem B1288811 : Blo 678312 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B862903 : Blo 678312 862903 := bstep (se 1 (by rfl) ⟨647177, by rfl⟩ : syracuseStep 862903 = 1294355) B1294355
theorem B1551095 : Blo 678312 1551095 := bstep (se 1 (by rfl) ⟨1163321, by rfl⟩ : syracuseStep 1551095 = 2326643) B2326643
theorem B1747855 : Blo 678312 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B863131 : Blo 678312 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B4139947 : Blo 678312 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B1092523 : Blo 678312 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B1289191 : Blo 678312 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B2174141 : Blo 678312 2174141 := bstep (se 3 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 2174141 = 815303) B815303
theorem B1289449 : Blo 678312 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B29470067 : Blo 678312 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B765535 : Blo 678312 765535 := bstep (se 1 (by rfl) ⟨574151, by rfl⟩ : syracuseStep 765535 = 1148303) B1148303
theorem B1290505 : Blo 678312 1290505 := bstep (se 2 (by rfl) ⟨483939, by rfl⟩ : syracuseStep 1290505 = 967879) B967879
theorem B13054445 : Blo 678312 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B3879647 : Blo 678312 3879647 := bstep (se 1 (by rfl) ⟨2909735, by rfl⟩ : syracuseStep 3879647 = 5819471) B5819471
theorem B766687 : Blo 678312 766687 := bstep (se 1 (by rfl) ⟨575015, by rfl⟩ : syracuseStep 766687 = 1150031) B1150031
theorem B3486659 : Blo 678312 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B1717463 : Blo 678312 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B767263 : Blo 678312 767263 := bstep (se 1 (by rfl) ⟨575447, by rfl⟩ : syracuseStep 767263 = 1150895) B1150895
theorem B3880331 : Blo 678312 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B9811361 : Blo 678312 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B3487169 : Blo 678312 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B767551 : Blo 678312 767551 := bstep (se 1 (by rfl) ⟨575663, by rfl⟩ : syracuseStep 767551 = 1151327) B1151327
theorem B1291963 : Blo 678312 1291963 := bstep (se 1 (by rfl) ⟨968972, by rfl⟩ : syracuseStep 1291963 = 1937945) B1937945
theorem B11056925 : Blo 678312 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B6993719 : Blo 678312 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B1718779 : Blo 678312 1718779 := bstep (se 1 (by rfl) ⟨1289084, by rfl⟩ : syracuseStep 1718779 = 2578169) B2578169
theorem B1718891 : Blo 678312 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B6961859 : Blo 678312 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B3882107 : Blo 678312 3882107 := bstep (se 1 (by rfl) ⟨2911580, by rfl⟩ : syracuseStep 3882107 = 5823161) B5823161
theorem B1719539 : Blo 678312 1719539 := bstep (se 1 (by rfl) ⟨1289654, by rfl⟩ : syracuseStep 1719539 = 2579309) B2579309
theorem B1719751 : Blo 678312 1719751 := bstep (se 1 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 1719751 = 2579627) B2579627
theorem B2899415 : Blo 678312 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B1293907 : Blo 678312 1293907 := bstep (se 1 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 1293907 = 1940861) B1940861
theorem B1294127 : Blo 678312 1294127 := bstep (se 1 (by rfl) ⟨970595, by rfl⟩ : syracuseStep 1294127 = 1941191) B1941191
theorem B5816123 : Blo 678312 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B5160833 : Blo 678312 5160833 := bstep (se 2 (by rfl) ⟨1935312, by rfl⟩ : syracuseStep 5160833 = 3870625) B3870625
theorem B1032457 : Blo 678312 1032457 := bstep (se 2 (by rfl) ⟨387171, by rfl⟩ : syracuseStep 1032457 = 774343) B774343
theorem B1327585 : Blo 678312 1327585 := bstep (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) B995689
theorem B2179585 : Blo 678312 2179585 := bstep (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) B1634689
theorem B3260999 : Blo 678312 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B1229419 : Blo 678312 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B1295023 : Blo 678312 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B7455415 : Blo 678312 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B3261151 : Blo 678312 3261151 := bstep (se 1 (by rfl) ⟨2445863, by rfl⟩ : syracuseStep 3261151 = 4891727) B4891727
theorem B3261227 : Blo 678312 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B1295183 : Blo 678312 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B12469211 : Blo 678312 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B1721483 : Blo 678312 1721483 := bstep (se 1 (by rfl) ⟨1291112, by rfl⟩ : syracuseStep 1721483 = 2582225) B2582225
theorem B7062833 : Blo 678312 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B5162291 : Blo 678312 5162291 := bstep (se 1 (by rfl) ⟨3871718, by rfl⟩ : syracuseStep 5162291 = 7743437) B7743437
theorem B1721695 : Blo 678312 1721695 := bstep (se 1 (by rfl) ⟨1291271, by rfl⟩ : syracuseStep 1721695 = 2582543) B2582543
theorem B8734331 : Blo 678312 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B3885479 : Blo 678312 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B1526291 : Blo 678312 1526291 := bstep (se 1 (by rfl) ⟨1144718, by rfl⟩ : syracuseStep 1526291 = 2289437) B2289437
theorem B1526345 : Blo 678312 1526345 := bstep (se 2 (by rfl) ⟨572379, by rfl⟩ : syracuseStep 1526345 = 1144759) B1144759
theorem B969337 : Blo 678312 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B1723103 : Blo 678312 1723103 := bstep (se 1 (by rfl) ⟨1292327, by rfl⟩ : syracuseStep 1723103 = 2584655) B2584655
theorem B1526759 : Blo 678312 1526759 := bstep (se 1 (by rfl) ⟨1145069, by rfl⟩ : syracuseStep 1526759 = 2290139) B2290139
theorem B226446353 : Blo 678312 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B1527137 : Blo 678312 1527137 := bstep (se 2 (by rfl) ⟨572676, by rfl⟩ : syracuseStep 1527137 = 1145353) B1145353
theorem B1527227 : Blo 678312 1527227 := bstep (se 1 (by rfl) ⟨1145420, by rfl⟩ : syracuseStep 1527227 = 2290841) B2290841
theorem B1527353 : Blo 678312 1527353 := bstep (se 2 (by rfl) ⟨572757, by rfl⟩ : syracuseStep 1527353 = 1145515) B1145515
theorem B7982957 : Blo 678312 7982957 := bstep (se 3 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 7982957 = 2993609) B2993609
theorem B2576393 : Blo 678312 2576393 := bstep (se 2 (by rfl) ⟨966147, by rfl⟩ : syracuseStep 2576393 = 1932295) B1932295
theorem B1528019 : Blo 678312 1528019 := bstep (se 1 (by rfl) ⟨1146014, by rfl⟩ : syracuseStep 1528019 = 2292029) B2292029
theorem B1528073 : Blo 678312 1528073 := bstep (se 2 (by rfl) ⟨573027, by rfl⟩ : syracuseStep 1528073 = 1146055) B1146055
theorem B971119 : Blo 678312 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B1528289 : Blo 678312 1528289 := bstep (se 2 (by rfl) ⟨573108, by rfl⟩ : syracuseStep 1528289 = 1146217) B1146217
theorem B12407519 : Blo 678312 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B1528595 : Blo 678312 1528595 := bstep (se 1 (by rfl) ⟨1146446, by rfl⟩ : syracuseStep 1528595 = 2292893) B2292893
theorem B1528955 : Blo 678312 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B1725563 : Blo 678312 1725563 := bstep (se 1 (by rfl) ⟨1294172, by rfl⟩ : syracuseStep 1725563 = 2588345) B2588345
theorem B1725583 : Blo 678312 1725583 := bstep (se 1 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 1725583 = 2588375) B2588375
theorem B1529081 : Blo 678312 1529081 := bstep (se 2 (by rfl) ⟨573405, by rfl⟩ : syracuseStep 1529081 = 1146811) B1146811
theorem B4904297 : Blo 678312 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B1529225 : Blo 678312 1529225 := bstep (se 2 (by rfl) ⟨573459, by rfl⟩ : syracuseStep 1529225 = 1146919) B1146919
theorem B1725857 : Blo 678312 1725857 := bstep (se 2 (by rfl) ⟨647196, by rfl⟩ : syracuseStep 1725857 = 1294393) B1294393
theorem B22304165 : Blo 678312 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B1529351 : Blo 678312 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B1529531 : Blo 678312 1529531 := bstep (se 1 (by rfl) ⟨1147148, by rfl⟩ : syracuseStep 1529531 = 2294297) B2294297
theorem B5592887 : Blo 678312 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B1529657 : Blo 678312 1529657 := bstep (se 2 (by rfl) ⟨573621, by rfl⟩ : syracuseStep 1529657 = 1147243) B1147243
theorem B4348151 : Blo 678312 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B2185481 : Blo 678312 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1530287 : Blo 678312 1530287 := bstep (se 1 (by rfl) ⟨1147715, by rfl⟩ : syracuseStep 1530287 = 2295431) B2295431
theorem B39836087 : Blo 678312 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B1530323 : Blo 678312 1530323 := bstep (se 1 (by rfl) ⟨1147742, by rfl⟩ : syracuseStep 1530323 = 2295485) B2295485
theorem B678395 : Blo 678312 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B678463 : Blo 678312 678463 := bstep (se 1 (by rfl) ⟨508847, by rfl⟩ : syracuseStep 678463 = 1017695) B1017695
theorem B1530431 : Blo 678312 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B678471 : Blo 678312 678471 := bstep (se 1 (by rfl) ⟨508853, by rfl⟩ : syracuseStep 678471 = 1017707) B1017707
theorem B2939465 : Blo 678312 2939465 := bstep (se 2 (by rfl) ⟨1102299, by rfl⟩ : syracuseStep 2939465 = 2204599) B2204599
theorem B1530539 : Blo 678312 1530539 := bstep (se 1 (by rfl) ⟨1147904, by rfl⟩ : syracuseStep 1530539 = 2295809) B2295809
theorem B3922607 : Blo 678312 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B678623 : Blo 678312 678623 := bstep (se 1 (by rfl) ⟨508967, by rfl⟩ : syracuseStep 678623 = 1017935) B1017935
theorem B678703 : Blo 678312 678703 := bstep (se 1 (by rfl) ⟨509027, by rfl⟩ : syracuseStep 678703 = 1018055) B1018055
theorem B678811 : Blo 678312 678811 := bstep (se 1 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 678811 = 1018217) B1018217
theorem B3267515 : Blo 678312 3267515 := bstep (se 1 (by rfl) ⟨2450636, by rfl⟩ : syracuseStep 3267515 = 4901273) B4901273
theorem B678863 : Blo 678312 678863 := bstep (se 1 (by rfl) ⟨509147, by rfl⟩ : syracuseStep 678863 = 1018295) B1018295
theorem B678887 : Blo 678312 678887 := bstep (se 1 (by rfl) ⟨509165, by rfl⟩ : syracuseStep 678887 = 1018331) B1018331
theorem B1531079 : Blo 678312 1531079 := bstep (se 1 (by rfl) ⟨1148309, by rfl⟩ : syracuseStep 1531079 = 2296619) B2296619
theorem B679199 : Blo 678312 679199 := bstep (se 1 (by rfl) ⟨509399, by rfl⟩ : syracuseStep 679199 = 1018799) B1018799
theorem B679259 : Blo 678312 679259 := bstep (se 1 (by rfl) ⟨509444, by rfl⟩ : syracuseStep 679259 = 1018889) B1018889
theorem B2579809 : Blo 678312 2579809 := bstep (se 2 (by rfl) ⟨967428, by rfl⟩ : syracuseStep 2579809 = 1934857) B1934857
theorem B679279 : Blo 678312 679279 := bstep (se 1 (by rfl) ⟨509459, by rfl⟩ : syracuseStep 679279 = 1018919) B1018919
theorem B1531259 : Blo 678312 1531259 := bstep (se 1 (by rfl) ⟨1148444, by rfl⟩ : syracuseStep 1531259 = 2296889) B2296889
theorem B679335 : Blo 678312 679335 := bstep (se 1 (by rfl) ⟨509501, by rfl⟩ : syracuseStep 679335 = 1019003) B1019003
theorem B3530233 : Blo 678312 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B1531385 : Blo 678312 1531385 := bstep (se 2 (by rfl) ⟨574269, by rfl⟩ : syracuseStep 1531385 = 1148539) B1148539
theorem B679419 : Blo 678312 679419 := bstep (se 1 (by rfl) ⟨509564, by rfl⟩ : syracuseStep 679419 = 1019129) B1019129
theorem B4906489 : Blo 678312 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B6544907 : Blo 678312 6544907 := bstep (se 1 (by rfl) ⟨4908680, by rfl⟩ : syracuseStep 6544907 = 9817361) B9817361
theorem B679487 : Blo 678312 679487 := bstep (se 1 (by rfl) ⟨509615, by rfl⟩ : syracuseStep 679487 = 1019231) B1019231
theorem B679495 : Blo 678312 679495 := bstep (se 1 (by rfl) ⟨509621, by rfl⟩ : syracuseStep 679495 = 1019243) B1019243
theorem B1531475 : Blo 678312 1531475 := bstep (se 1 (by rfl) ⟨1148606, by rfl⟩ : syracuseStep 1531475 = 2297213) B2297213
theorem B2580083 : Blo 678312 2580083 := bstep (se 1 (by rfl) ⟨1935062, by rfl⟩ : syracuseStep 2580083 = 3870125) B3870125
theorem B679647 : Blo 678312 679647 := bstep (se 1 (by rfl) ⟨509735, by rfl⟩ : syracuseStep 679647 = 1019471) B1019471
theorem B1531655 : Blo 678312 1531655 := bstep (se 1 (by rfl) ⟨1148741, by rfl⟩ : syracuseStep 1531655 = 2297483) B2297483
theorem B679727 : Blo 678312 679727 := bstep (se 1 (by rfl) ⟨509795, by rfl⟩ : syracuseStep 679727 = 1019591) B1019591
theorem B2580281 : Blo 678312 2580281 := bstep (se 2 (by rfl) ⟨967605, by rfl⟩ : syracuseStep 2580281 = 1935211) B1935211
theorem B679835 : Blo 678312 679835 := bstep (se 1 (by rfl) ⟨509876, by rfl⟩ : syracuseStep 679835 = 1019753) B1019753
theorem B3104669 : Blo 678312 3104669 := bstep (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) B1164251
theorem B679887 : Blo 678312 679887 := bstep (se 1 (by rfl) ⟨509915, by rfl⟩ : syracuseStep 679887 = 1019831) B1019831
theorem B679911 : Blo 678312 679911 := bstep (se 1 (by rfl) ⟨509933, by rfl⟩ : syracuseStep 679911 = 1019867) B1019867
theorem B23584945 : Blo 678312 23584945 := bstep (se 2 (by rfl) ⟨8844354, by rfl⟩ : syracuseStep 23584945 = 17688709) B17688709
theorem B680223 : Blo 678312 680223 := bstep (se 1 (by rfl) ⟨510167, by rfl⟩ : syracuseStep 680223 = 1020335) B1020335
theorem B680283 : Blo 678312 680283 := bstep (se 1 (by rfl) ⟨510212, by rfl⟩ : syracuseStep 680283 = 1020425) B1020425
theorem B1532267 : Blo 678312 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B680303 : Blo 678312 680303 := bstep (se 1 (by rfl) ⟨510227, by rfl⟩ : syracuseStep 680303 = 1020455) B1020455
theorem B680359 : Blo 678312 680359 := bstep (se 1 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 680359 = 1020539) B1020539
theorem B3138011 : Blo 678312 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B680443 : Blo 678312 680443 := bstep (se 1 (by rfl) ⟨510332, by rfl⟩ : syracuseStep 680443 = 1020665) B1020665
theorem B1532411 : Blo 678312 1532411 := bstep (se 1 (by rfl) ⟨1149308, by rfl⟩ : syracuseStep 1532411 = 2298617) B2298617
theorem B680511 : Blo 678312 680511 := bstep (se 1 (by rfl) ⟨510383, by rfl⟩ : syracuseStep 680511 = 1020767) B1020767
theorem B680519 : Blo 678312 680519 := bstep (se 1 (by rfl) ⟨510389, by rfl⟩ : syracuseStep 680519 = 1020779) B1020779
theorem B1532537 : Blo 678312 1532537 := bstep (se 2 (by rfl) ⟨574701, by rfl⟩ : syracuseStep 1532537 = 1149403) B1149403
theorem B4350611 : Blo 678312 4350611 := bstep (se 1 (by rfl) ⟨3262958, by rfl⟩ : syracuseStep 4350611 = 6525917) B6525917
theorem B2482859 : Blo 678312 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B1532591 : Blo 678312 1532591 := bstep (se 1 (by rfl) ⟨1149443, by rfl⟩ : syracuseStep 1532591 = 2298887) B2298887
theorem B680671 : Blo 678312 680671 := bstep (se 1 (by rfl) ⟨510503, by rfl⟩ : syracuseStep 680671 = 1021007) B1021007
theorem B1532663 : Blo 678312 1532663 := bstep (se 1 (by rfl) ⟨1149497, by rfl⟩ : syracuseStep 1532663 = 2298995) B2298995
theorem B680751 : Blo 678312 680751 := bstep (se 1 (by rfl) ⟨510563, by rfl⟩ : syracuseStep 680751 = 1021127) B1021127
theorem B680859 : Blo 678312 680859 := bstep (se 1 (by rfl) ⟨510644, by rfl⟩ : syracuseStep 680859 = 1021289) B1021289
theorem B1532843 : Blo 678312 1532843 := bstep (se 1 (by rfl) ⟨1149632, by rfl⟩ : syracuseStep 1532843 = 2299265) B2299265
theorem B680911 : Blo 678312 680911 := bstep (se 1 (by rfl) ⟨510683, by rfl⟩ : syracuseStep 680911 = 1021367) B1021367
theorem B680935 : Blo 678312 680935 := bstep (se 1 (by rfl) ⟨510701, by rfl⟩ : syracuseStep 680935 = 1021403) B1021403
theorem B2581753 : Blo 678312 2581753 := bstep (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) B1936315
theorem B681247 : Blo 678312 681247 := bstep (se 1 (by rfl) ⟨510935, by rfl⟩ : syracuseStep 681247 = 1021871) B1021871
theorem B681307 : Blo 678312 681307 := bstep (se 1 (by rfl) ⟨510980, by rfl⟩ : syracuseStep 681307 = 1021961) B1021961
theorem B681327 : Blo 678312 681327 := bstep (se 1 (by rfl) ⟨510995, by rfl⟩ : syracuseStep 681327 = 1021991) B1021991
theorem B681383 : Blo 678312 681383 := bstep (se 1 (by rfl) ⟨511037, by rfl⟩ : syracuseStep 681383 = 1022075) B1022075
theorem B1533383 : Blo 678312 1533383 := bstep (se 1 (by rfl) ⟨1150037, by rfl⟩ : syracuseStep 1533383 = 2300075) B2300075
theorem B681467 : Blo 678312 681467 := bstep (se 1 (by rfl) ⟨511100, by rfl⟩ : syracuseStep 681467 = 1022201) B1022201
theorem B681535 : Blo 678312 681535 := bstep (se 1 (by rfl) ⟨511151, by rfl⟩ : syracuseStep 681535 = 1022303) B1022303
theorem B681543 : Blo 678312 681543 := bstep (se 1 (by rfl) ⟨511157, by rfl⟩ : syracuseStep 681543 = 1022315) B1022315
theorem B9791063 : Blo 678312 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B681695 : Blo 678312 681695 := bstep (se 1 (by rfl) ⟨511271, by rfl⟩ : syracuseStep 681695 = 1022543) B1022543
theorem B1533743 : Blo 678312 1533743 := bstep (se 1 (by rfl) ⟨1150307, by rfl⟩ : syracuseStep 1533743 = 2300615) B2300615
theorem B681775 : Blo 678312 681775 := bstep (se 1 (by rfl) ⟨511331, by rfl⟩ : syracuseStep 681775 = 1022663) B1022663
theorem B6547331 : Blo 678312 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B681883 : Blo 678312 681883 := bstep (se 1 (by rfl) ⟨511412, by rfl⟩ : syracuseStep 681883 = 1022825) B1022825
theorem B681935 : Blo 678312 681935 := bstep (se 1 (by rfl) ⟨511451, by rfl⟩ : syracuseStep 681935 = 1022903) B1022903
theorem B681959 : Blo 678312 681959 := bstep (se 1 (by rfl) ⟨511469, by rfl⟩ : syracuseStep 681959 = 1022939) B1022939
theorem B21227501 : Blo 678312 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B14706845 : Blo 678312 14706845 := bstep (se 3 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 14706845 = 5515067) B5515067
theorem B682271 : Blo 678312 682271 := bstep (se 1 (by rfl) ⟨511703, by rfl⟩ : syracuseStep 682271 = 1023407) B1023407
theorem B1534319 : Blo 678312 1534319 := bstep (se 1 (by rfl) ⟨1150739, by rfl⟩ : syracuseStep 1534319 = 2301479) B2301479
theorem B1534391 : Blo 678312 1534391 := bstep (se 1 (by rfl) ⟨1150793, by rfl⟩ : syracuseStep 1534391 = 2301587) B2301587
theorem B3500471 : Blo 678312 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B3435047 : Blo 678312 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B1534535 : Blo 678312 1534535 := bstep (se 1 (by rfl) ⟨1150901, by rfl⟩ : syracuseStep 1534535 = 2301803) B2301803
theorem B1534571 : Blo 678312 1534571 := bstep (se 1 (by rfl) ⟨1150928, by rfl⟩ : syracuseStep 1534571 = 2301857) B2301857
theorem B5827261 : Blo 678312 5827261 := bstep (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) B2185223
theorem B8711063 : Blo 678312 8711063 := bstep (se 1 (by rfl) ⟨6533297, by rfl⟩ : syracuseStep 8711063 = 13066595) B13066595
theorem B1534967 : Blo 678312 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B7334993 : Blo 678312 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B815611 : Blo 678312 815611 := bstep (se 1 (by rfl) ⟨611708, by rfl⟩ : syracuseStep 815611 = 1223417) B1223417
theorem B2290247 : Blo 678312 2290247 := bstep (se 1 (by rfl) ⟨1717685, by rfl⟩ : syracuseStep 2290247 = 3435371) B3435371
theorem B3437153 : Blo 678312 3437153 := bstep (se 2 (by rfl) ⟨1288932, by rfl⟩ : syracuseStep 3437153 = 2577865) B2577865
theorem B2290679 : Blo 678312 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B3863609 : Blo 678312 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B1635527 : Blo 678312 1635527 := bstep (se 1 (by rfl) ⟨1226645, by rfl⟩ : syracuseStep 1635527 = 2453291) B2453291
theorem B2913479 : Blo 678312 2913479 := bstep (se 1 (by rfl) ⟨2185109, by rfl⟩ : syracuseStep 2913479 = 4370219) B4370219
theorem B3437801 : Blo 678312 3437801 := bstep (se 2 (by rfl) ⟨1289175, by rfl⟩ : syracuseStep 3437801 = 2578351) B2578351
theorem B2913529 : Blo 678312 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B1307935 : Blo 678312 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B3437963 : Blo 678312 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B3274145 : Blo 678312 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B2291543 : Blo 678312 2291543 := bstep (se 1 (by rfl) ⟨1718657, by rfl⟩ : syracuseStep 2291543 = 3437315) B3437315
theorem B1636457 : Blo 678312 1636457 := bstep (se 2 (by rfl) ⟨613671, by rfl⟩ : syracuseStep 1636457 = 1227343) B1227343
theorem B7076119 : Blo 678312 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B13236605 : Blo 678312 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B13957555 : Blo 678312 13957555 := bstep (se 1 (by rfl) ⟨10468166, by rfl⟩ : syracuseStep 13957555 = 20936333) B20936333
theorem B1145407 : Blo 678312 1145407 := bstep (se 1 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 1145407 = 1718111) B1718111
theorem B2292623 : Blo 678312 2292623 := bstep (se 1 (by rfl) ⟨1719467, by rfl⟩ : syracuseStep 2292623 = 3438935) B3438935
theorem B6617999 : Blo 678312 6617999 := bstep (se 1 (by rfl) ⟨4963499, by rfl⟩ : syracuseStep 6617999 = 9926999) B9926999
theorem B1146089 : Blo 678312 1146089 := bstep (se 2 (by rfl) ⟨429783, by rfl⟩ : syracuseStep 1146089 = 859567) B859567
theorem B1146143 : Blo 678312 1146143 := bstep (se 1 (by rfl) ⟨859607, by rfl⟩ : syracuseStep 1146143 = 1719215) B1719215
theorem B3276605 : Blo 678312 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B35324219 : Blo 678312 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B1376609 : Blo 678312 1376609 := bstep (se 2 (by rfl) ⟨516228, by rfl⟩ : syracuseStep 1376609 = 1032457) B1032457
theorem B2294135 : Blo 678312 2294135 := bstep (se 1 (by rfl) ⟨1720601, by rfl⟩ : syracuseStep 2294135 = 3441203) B3441203
theorem B1966523 : Blo 678312 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B1147385 : Blo 678312 1147385 := bstep (se 2 (by rfl) ⟨430269, by rfl⟩ : syracuseStep 1147385 = 860539) B860539
theorem B1770113 : Blo 678312 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B1147655 : Blo 678312 1147655 := bstep (se 1 (by rfl) ⟨860741, by rfl⟩ : syracuseStep 1147655 = 1721483) B1721483
theorem B1639225 : Blo 678312 1639225 := bstep (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) B1229419
theorem B3441527 : Blo 678312 3441527 := bstep (se 1 (by rfl) ⟨2581145, by rfl⟩ : syracuseStep 3441527 = 5162291) B5162291
theorem B1639379 : Blo 678312 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B12584135 : Blo 678312 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B2295215 : Blo 678312 2295215 := bstep (se 1 (by rfl) ⟨1721411, by rfl⟩ : syracuseStep 2295215 = 3442823) B3442823
theorem B2590319 : Blo 678312 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B2066081 : Blo 678312 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B3442337 : Blo 678312 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B788135 : Blo 678312 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B1017527 : Blo 678312 1017527 := bstep (se 1 (by rfl) ⟨763145, by rfl⟩ : syracuseStep 1017527 = 1526291) B1526291
theorem B1017563 : Blo 678312 1017563 := bstep (se 1 (by rfl) ⟨763172, by rfl⟩ : syracuseStep 1017563 = 1526345) B1526345
theorem B6620957 : Blo 678312 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2295593 : Blo 678312 2295593 := bstep (se 2 (by rfl) ⟨860847, by rfl⟩ : syracuseStep 2295593 = 1721695) B1721695
theorem B1148735 : Blo 678312 1148735 := bstep (se 1 (by rfl) ⟨861551, by rfl⟩ : syracuseStep 1148735 = 1723103) B1723103
theorem B1967951 : Blo 678312 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B1017737 : Blo 678312 1017737 := bstep (se 2 (by rfl) ⟨381651, by rfl⟩ : syracuseStep 1017737 = 763303) B763303
theorem B1148809 : Blo 678312 1148809 := bstep (se 2 (by rfl) ⟨430803, by rfl⟩ : syracuseStep 1148809 = 861607) B861607
theorem B5179301 : Blo 678312 5179301 := bstep (se 4 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 5179301 = 971119) B971119
theorem B1017839 : Blo 678312 1017839 := bstep (se 1 (by rfl) ⟨763379, by rfl⟩ : syracuseStep 1017839 = 1526759) B1526759
theorem B150964235 : Blo 678312 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B1935485 : Blo 678312 1935485 := bstep (se 3 (by rfl) ⟨362903, by rfl⟩ : syracuseStep 1935485 = 725807) B725807
theorem B1018091 : Blo 678312 1018091 := bstep (se 1 (by rfl) ⟨763568, by rfl⟩ : syracuseStep 1018091 = 1527137) B1527137
theorem B1018151 : Blo 678312 1018151 := bstep (se 1 (by rfl) ⟨763613, by rfl⟩ : syracuseStep 1018151 = 1527227) B1527227
theorem B1149241 : Blo 678312 1149241 := bstep (se 2 (by rfl) ⟨430965, by rfl⟩ : syracuseStep 1149241 = 861931) B861931
theorem B1018235 : Blo 678312 1018235 := bstep (se 1 (by rfl) ⟨763676, by rfl⟩ : syracuseStep 1018235 = 1527353) B1527353
theorem B1149545 : Blo 678312 1149545 := bstep (se 2 (by rfl) ⟨431079, by rfl⟩ : syracuseStep 1149545 = 862159) B862159
theorem B1018505 : Blo 678312 1018505 := bstep (se 2 (by rfl) ⟨381939, by rfl⟩ : syracuseStep 1018505 = 763879) B763879
theorem B1018679 : Blo 678312 1018679 := bstep (se 1 (by rfl) ⟨764009, by rfl⟩ : syracuseStep 1018679 = 1528019) B1528019
theorem B1018715 : Blo 678312 1018715 := bstep (se 1 (by rfl) ⟨764036, by rfl⟩ : syracuseStep 1018715 = 1528073) B1528073
theorem B1018859 : Blo 678312 1018859 := bstep (se 1 (by rfl) ⟨764144, by rfl⟩ : syracuseStep 1018859 = 1528289) B1528289
theorem B1019063 : Blo 678312 1019063 := bstep (se 1 (by rfl) ⟨764297, by rfl⟩ : syracuseStep 1019063 = 1528595) B1528595
theorem B5508319 : Blo 678312 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B1019303 : Blo 678312 1019303 := bstep (se 1 (by rfl) ⟨764477, by rfl⟩ : syracuseStep 1019303 = 1528955) B1528955
theorem B1150375 : Blo 678312 1150375 := bstep (se 1 (by rfl) ⟨862781, by rfl⟩ : syracuseStep 1150375 = 1725563) B1725563
theorem B1019387 : Blo 678312 1019387 := bstep (se 1 (by rfl) ⟨764540, by rfl⟩ : syracuseStep 1019387 = 1529081) B1529081
theorem B1150537 : Blo 678312 1150537 := bstep (se 2 (by rfl) ⟨431451, by rfl⟩ : syracuseStep 1150537 = 862903) B862903
theorem B7769681 : Blo 678312 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B1019483 : Blo 678312 1019483 := bstep (se 1 (by rfl) ⟨764612, by rfl⟩ : syracuseStep 1019483 = 1529225) B1529225
theorem B1150571 : Blo 678312 1150571 := bstep (se 1 (by rfl) ⟨862928, by rfl⟩ : syracuseStep 1150571 = 1725857) B1725857
theorem B1019567 : Blo 678312 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B59477773 : Blo 678312 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B1019687 : Blo 678312 1019687 := bstep (se 1 (by rfl) ⟨764765, by rfl⟩ : syracuseStep 1019687 = 1529531) B1529531
theorem B2330473 : Blo 678312 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1150841 : Blo 678312 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B1019771 : Blo 678312 1019771 := bstep (se 1 (by rfl) ⟨764828, by rfl⟩ : syracuseStep 1019771 = 1529657) B1529657
theorem B2297807 : Blo 678312 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B1020191 : Blo 678312 1020191 := bstep (se 1 (by rfl) ⟨765143, by rfl⟩ : syracuseStep 1020191 = 1530287) B1530287
theorem B1020215 : Blo 678312 1020215 := bstep (se 1 (by rfl) ⟨765161, by rfl⟩ : syracuseStep 1020215 = 1530323) B1530323
theorem B1020287 : Blo 678312 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B2298239 : Blo 678312 2298239 := bstep (se 1 (by rfl) ⟨1723679, by rfl⟩ : syracuseStep 2298239 = 3447359) B3447359
theorem B1020359 : Blo 678312 1020359 := bstep (se 1 (by rfl) ⟨765269, by rfl⟩ : syracuseStep 1020359 = 1530539) B1530539
theorem B1020713 : Blo 678312 1020713 := bstep (se 2 (by rfl) ⟨382767, by rfl⟩ : syracuseStep 1020713 = 765535) B765535
theorem B1020719 : Blo 678312 1020719 := bstep (se 1 (by rfl) ⟨765539, by rfl⟩ : syracuseStep 1020719 = 1531079) B1531079
theorem B1020839 : Blo 678312 1020839 := bstep (se 1 (by rfl) ⟨765629, by rfl⟩ : syracuseStep 1020839 = 1531259) B1531259
theorem B1020923 : Blo 678312 1020923 := bstep (se 1 (by rfl) ⟨765692, by rfl⟩ : syracuseStep 1020923 = 1531385) B1531385
theorem B4363271 : Blo 678312 4363271 := bstep (se 1 (by rfl) ⟨3272453, by rfl⟩ : syracuseStep 4363271 = 6544907) B6544907
theorem B1020983 : Blo 678312 1020983 := bstep (se 1 (by rfl) ⟨765737, by rfl⟩ : syracuseStep 1020983 = 1531475) B1531475
theorem B9311377 : Blo 678312 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B1021103 : Blo 678312 1021103 := bstep (se 1 (by rfl) ⟨765827, by rfl⟩ : syracuseStep 1021103 = 1531655) B1531655
theorem B1021511 : Blo 678312 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B4363885 : Blo 678312 4363885 := bstep (se 3 (by rfl) ⟨818228, by rfl⟩ : syracuseStep 4363885 = 1636457) B1636457
theorem B1021607 : Blo 678312 1021607 := bstep (se 1 (by rfl) ⟨766205, by rfl⟩ : syracuseStep 1021607 = 1532411) B1532411
theorem B1021691 : Blo 678312 1021691 := bstep (se 1 (by rfl) ⟨766268, by rfl⟩ : syracuseStep 1021691 = 1532537) B1532537
theorem B2299643 : Blo 678312 2299643 := bstep (se 1 (by rfl) ⟨1724732, by rfl⟩ : syracuseStep 2299643 = 3449465) B3449465
theorem B1021727 : Blo 678312 1021727 := bstep (se 1 (by rfl) ⟨766295, by rfl⟩ : syracuseStep 1021727 = 1532591) B1532591
theorem B1021775 : Blo 678312 1021775 := bstep (se 1 (by rfl) ⟨766331, by rfl⟩ : syracuseStep 1021775 = 1532663) B1532663
theorem B2299805 : Blo 678312 2299805 := bstep (se 3 (by rfl) ⟨431213, by rfl⟩ : syracuseStep 2299805 = 862427) B862427
theorem B1021895 : Blo 678312 1021895 := bstep (se 1 (by rfl) ⟨766421, by rfl⟩ : syracuseStep 1021895 = 1532843) B1532843
theorem B1087481 : Blo 678312 1087481 := bstep (se 2 (by rfl) ⟨407805, by rfl⟩ : syracuseStep 1087481 = 815611) B815611
theorem B1022249 : Blo 678312 1022249 := bstep (se 2 (by rfl) ⟨383343, by rfl⟩ : syracuseStep 1022249 = 766687) B766687
theorem B1022255 : Blo 678312 1022255 := bstep (se 1 (by rfl) ⟨766691, by rfl⟩ : syracuseStep 1022255 = 1533383) B1533383
theorem B6527375 : Blo 678312 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B6822319 : Blo 678312 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1022495 : Blo 678312 1022495 := bstep (se 1 (by rfl) ⟨766871, by rfl⟩ : syracuseStep 1022495 = 1533743) B1533743
theorem B4364887 : Blo 678312 4364887 := bstep (se 1 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 4364887 = 6547331) B6547331
theorem B9804563 : Blo 678312 9804563 := bstep (se 1 (by rfl) ⟨7353422, by rfl⟩ : syracuseStep 9804563 = 14706845) B14706845
theorem B1842011 : Blo 678312 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B2300777 : Blo 678312 2300777 := bstep (se 2 (by rfl) ⟨862791, by rfl⟩ : syracuseStep 2300777 = 1725583) B1725583
theorem B2300831 : Blo 678312 2300831 := bstep (se 1 (by rfl) ⟨1725623, by rfl⟩ : syracuseStep 2300831 = 3451247) B3451247
theorem B1022879 : Blo 678312 1022879 := bstep (se 1 (by rfl) ⟨767159, by rfl⟩ : syracuseStep 1022879 = 1534319) B1534319
theorem B1022927 : Blo 678312 1022927 := bstep (se 1 (by rfl) ⟨767195, by rfl⟩ : syracuseStep 1022927 = 1534391) B1534391
theorem B2333647 : Blo 678312 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B1743913 : Blo 678312 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B1023017 : Blo 678312 1023017 := bstep (se 2 (by rfl) ⟨383631, by rfl⟩ : syracuseStep 1023017 = 767263) B767263
theorem B1023023 : Blo 678312 1023023 := bstep (se 1 (by rfl) ⟨767267, by rfl⟩ : syracuseStep 1023023 = 1534535) B1534535
theorem B1023047 : Blo 678312 1023047 := bstep (se 1 (by rfl) ⟨767285, by rfl⟩ : syracuseStep 1023047 = 1534571) B1534571
theorem B10460285 : Blo 678312 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B5807375 : Blo 678312 5807375 := bstep (se 1 (by rfl) ⟨4355531, by rfl⟩ : syracuseStep 5807375 = 8711063) B8711063
theorem B1023311 : Blo 678312 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B1023401 : Blo 678312 1023401 := bstep (se 2 (by rfl) ⟨383775, by rfl⟩ : syracuseStep 1023401 = 767551) B767551
theorem B1449427 : Blo 678312 1449427 := bstep (se 1 (by rfl) ⟨1087070, by rfl⟩ : syracuseStep 1449427 = 2174141) B2174141
theorem B1090351 : Blo 678312 1090351 := bstep (se 1 (by rfl) ⟨817763, by rfl⟩ : syracuseStep 1090351 = 1635527) B1635527
theorem B1942319 : Blo 678312 1942319 := bstep (se 1 (by rfl) ⟨1456739, by rfl⟩ : syracuseStep 1942319 = 2913479) B2913479
theorem B1942717 : Blo 678312 1942717 := bstep (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) B728519
theorem B4662479 : Blo 678312 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B3679825 : Blo 678312 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B8824403 : Blo 678312 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B764059 : Blo 678312 764059 := bstep (se 1 (by rfl) ⟨573044, by rfl⟩ : syracuseStep 764059 = 1146089) B1146089
theorem B764095 : Blo 678312 764095 := bstep (se 1 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 764095 = 1146143) B1146143
theorem B862751 : Blo 678312 862751 := bstep (se 1 (by rfl) ⟨647063, by rfl⟩ : syracuseStep 862751 = 1294127) B1294127
theorem B3877415 : Blo 678312 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B11643587 : Blo 678312 11643587 := bstep (se 1 (by rfl) ⟨8732690, by rfl⟩ : syracuseStep 11643587 = 17465381) B17465381
theorem B2173999 : Blo 678312 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B863455 : Blo 678312 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B9940553 : Blo 678312 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B1453945 : Blo 678312 1453945 := bstep (se 2 (by rfl) ⟨545229, by rfl⟩ : syracuseStep 1453945 = 1090459) B1090459
theorem B766183 : Blo 678312 766183 := bstep (se 1 (by rfl) ⟨574637, by rfl⟩ : syracuseStep 766183 = 1149275) B1149275
theorem B8696605 : Blo 678312 8696605 := bstep (se 3 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 8696605 = 3261227) B3261227
theorem B14725961 : Blo 678312 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B766831 : Blo 678312 766831 := bstep (se 1 (by rfl) ⟨575123, by rfl⟩ : syracuseStep 766831 = 1150247) B1150247
theorem B1717321 : Blo 678312 1717321 := bstep (se 2 (by rfl) ⟨643995, by rfl⟩ : syracuseStep 1717321 = 1287991) B1287991
theorem B1291439 : Blo 678312 1291439 := bstep (se 1 (by rfl) ⟨968579, by rfl⟩ : syracuseStep 1291439 = 1937159) B1937159
theorem B5321971 : Blo 678312 5321971 := bstep (se 1 (by rfl) ⟨3991478, by rfl⟩ : syracuseStep 5321971 = 7982957) B7982957
theorem B4371731 : Blo 678312 4371731 := bstep (se 1 (by rfl) ⟨3278798, by rfl⟩ : syracuseStep 4371731 = 6557597) B6557597
theorem B1717595 : Blo 678312 1717595 := bstep (se 1 (by rfl) ⟨1288196, by rfl⟩ : syracuseStep 1717595 = 2576393) B2576393
theorem B8271679 : Blo 678312 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B1292449 : Blo 678312 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B5519929 : Blo 678312 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B1456697 : Blo 678312 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B1718921 : Blo 678312 1718921 := bstep (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) B1289191
theorem B1227401 : Blo 678312 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B2898767 : Blo 678312 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B1456987 : Blo 678312 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B26557391 : Blo 678312 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B1719265 : Blo 678312 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B1293383 : Blo 678312 1293383 := bstep (se 1 (by rfl) ⟨970037, by rfl⟩ : syracuseStep 1293383 = 1940075) B1940075
theorem B2178343 : Blo 678312 2178343 := bstep (se 1 (by rfl) ⟨1633757, by rfl⟩ : syracuseStep 2178343 = 3267515) B3267515
theorem B1720055 : Blo 678312 1720055 := bstep (se 1 (by rfl) ⟨1290041, by rfl⟩ : syracuseStep 1720055 = 2580083) B2580083
theorem B1720187 : Blo 678312 1720187 := bstep (se 1 (by rfl) ⟨1290140, by rfl⟩ : syracuseStep 1720187 = 2580281) B2580281
theorem B1228699 : Blo 678312 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B1720673 : Blo 678312 1720673 := bstep (se 2 (by rfl) ⟨645252, by rfl⟩ : syracuseStep 1720673 = 1290505) B1290505
theorem B2900407 : Blo 678312 2900407 := bstep (se 1 (by rfl) ⟨2175305, by rfl⟩ : syracuseStep 2900407 = 4350611) B4350611
theorem B7357661 : Blo 678312 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B3884705 : Blo 678312 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B1034063 : Blo 678312 1034063 := bstep (se 1 (by rfl) ⟨775547, by rfl⟩ : syracuseStep 1034063 = 1551095) B1551095
theorem B19646711 : Blo 678312 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B1722617 : Blo 678312 1722617 := bstep (se 2 (by rfl) ⟨645981, by rfl⟩ : syracuseStep 1722617 = 1291963) B1291963
theorem B8702963 : Blo 678312 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B1526831 : Blo 678312 1526831 := bstep (se 1 (by rfl) ⟨1145123, by rfl⟩ : syracuseStep 1526831 = 2290247) B2290247
theorem B1527119 : Blo 678312 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B2575739 : Blo 678312 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B1527209 : Blo 678312 1527209 := bstep (se 2 (by rfl) ⟨572703, by rfl⟩ : syracuseStep 1527209 = 1145407) B1145407
theorem B6540907 : Blo 678312 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B2182763 : Blo 678312 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B1527695 : Blo 678312 1527695 := bstep (se 1 (by rfl) ⟨1145771, by rfl⟩ : syracuseStep 1527695 = 2291543) B2291543
theorem B4641239 : Blo 678312 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B1528415 : Blo 678312 1528415 := bstep (se 1 (by rfl) ⟨1146311, by rfl⟩ : syracuseStep 1528415 = 2292623) B2292623
theorem B4411999 : Blo 678312 4411999 := bstep (se 1 (by rfl) ⟨3308999, by rfl⟩ : syracuseStep 4411999 = 6617999) B6617999
theorem B4706977 : Blo 678312 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B6541985 : Blo 678312 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B1725209 : Blo 678312 1725209 := bstep (se 2 (by rfl) ⟨646953, by rfl⟩ : syracuseStep 1725209 = 1293907) B1293907
theorem B8279117 : Blo 678312 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B2184403 : Blo 678312 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B1529243 : Blo 678312 1529243 := bstep (se 1 (by rfl) ⟨1146932, by rfl⟩ : syracuseStep 1529243 = 2293865) B2293865
theorem B2577851 : Blo 678312 2577851 := bstep (se 1 (by rfl) ⟨1933388, by rfl⟩ : syracuseStep 2577851 = 3866777) B3866777
theorem B31446593 : Blo 678312 31446593 := bstep (se 2 (by rfl) ⟨11792472, by rfl⟩ : syracuseStep 31446593 = 23584945) B23584945
theorem B35346293 : Blo 678312 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B1529819 : Blo 678312 1529819 := bstep (se 1 (by rfl) ⟨1147364, by rfl⟩ : syracuseStep 1529819 = 2294729) B2294729
theorem B8312807 : Blo 678312 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B2906113 : Blo 678312 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B1529999 : Blo 678312 1529999 := bstep (se 1 (by rfl) ⟨1147499, by rfl⟩ : syracuseStep 1529999 = 2294999) B2294999
theorem B1530017 : Blo 678312 1530017 := bstep (se 2 (by rfl) ⟨573756, by rfl⟩ : syracuseStep 1530017 = 1147513) B1147513
theorem B1530089 : Blo 678312 1530089 := bstep (se 2 (by rfl) ⟨573783, by rfl⟩ : syracuseStep 1530089 = 1147567) B1147567
theorem B1726697 : Blo 678312 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B4348201 : Blo 678312 4348201 := bstep (se 2 (by rfl) ⟨1630575, by rfl⟩ : syracuseStep 4348201 = 3261151) B3261151
theorem B5822887 : Blo 678312 5822887 := bstep (se 1 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 5822887 = 8734331) B8734331
theorem B678427 : Blo 678312 678427 := bstep (se 1 (by rfl) ⟨508820, by rfl⟩ : syracuseStep 678427 = 1017641) B1017641
theorem B678431 : Blo 678312 678431 := bstep (se 1 (by rfl) ⟨508823, by rfl⟩ : syracuseStep 678431 = 1017647) B1017647
theorem B678747 : Blo 678312 678747 := bstep (se 1 (by rfl) ⟨509060, by rfl⟩ : syracuseStep 678747 = 1018121) B1018121
theorem B678815 : Blo 678312 678815 := bstep (se 1 (by rfl) ⟨509111, by rfl⟩ : syracuseStep 678815 = 1018223) B1018223
theorem B678959 : Blo 678312 678959 := bstep (se 1 (by rfl) ⟨509219, by rfl⟩ : syracuseStep 678959 = 1018439) B1018439
theorem B678983 : Blo 678312 678983 := bstep (se 1 (by rfl) ⟨509237, by rfl⟩ : syracuseStep 678983 = 1018475) B1018475
theorem B4775057 : Blo 678312 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B2546873 : Blo 678312 2546873 := bstep (se 2 (by rfl) ⟨955077, by rfl⟩ : syracuseStep 2546873 = 1910155) B1910155
theorem B679135 : Blo 678312 679135 := bstep (se 1 (by rfl) ⟨509351, by rfl⟩ : syracuseStep 679135 = 1018703) B1018703
theorem B679399 : Blo 678312 679399 := bstep (se 1 (by rfl) ⟨509549, by rfl⟩ : syracuseStep 679399 = 1019099) B1019099
theorem B1531367 : Blo 678312 1531367 := bstep (se 1 (by rfl) ⟨1148525, by rfl⟩ : syracuseStep 1531367 = 2297051) B2297051
theorem B679515 : Blo 678312 679515 := bstep (se 1 (by rfl) ⟨509636, by rfl⟩ : syracuseStep 679515 = 1019273) B1019273
theorem B2580295 : Blo 678312 2580295 := bstep (se 1 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 2580295 = 3870443) B3870443
theorem B679751 : Blo 678312 679751 := bstep (se 1 (by rfl) ⟨509813, by rfl⟩ : syracuseStep 679751 = 1019627) B1019627
theorem B9297757 : Blo 678312 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B679903 : Blo 678312 679903 := bstep (se 1 (by rfl) ⟨509927, by rfl⟩ : syracuseStep 679903 = 1019855) B1019855
theorem B1531943 : Blo 678312 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B1532123 : Blo 678312 1532123 := bstep (se 1 (by rfl) ⟨1149092, by rfl⟩ : syracuseStep 1532123 = 2298185) B2298185
theorem B680167 : Blo 678312 680167 := bstep (se 1 (by rfl) ⟨510125, by rfl⟩ : syracuseStep 680167 = 1020251) B1020251
theorem B2580767 : Blo 678312 2580767 := bstep (se 1 (by rfl) ⟨1935575, by rfl⟩ : syracuseStep 2580767 = 3871151) B3871151
theorem B680319 : Blo 678312 680319 := bstep (se 1 (by rfl) ⟨510239, by rfl⟩ : syracuseStep 680319 = 1020479) B1020479
theorem B161014169 : Blo 678312 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B680399 : Blo 678312 680399 := bstep (se 1 (by rfl) ⟨510299, by rfl⟩ : syracuseStep 680399 = 1020599) B1020599
theorem B1532393 : Blo 678312 1532393 := bstep (se 2 (by rfl) ⟨574647, by rfl⟩ : syracuseStep 1532393 = 1149295) B1149295
theorem B680551 : Blo 678312 680551 := bstep (se 1 (by rfl) ⟨510413, by rfl⟩ : syracuseStep 680551 = 1020827) B1020827
theorem B1532681 : Blo 678312 1532681 := bstep (se 2 (by rfl) ⟨574755, by rfl⟩ : syracuseStep 1532681 = 1149511) B1149511
theorem B2581267 : Blo 678312 2581267 := bstep (se 1 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 2581267 = 3871901) B3871901
theorem B18834221 : Blo 678312 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B680815 : Blo 678312 680815 := bstep (se 1 (by rfl) ⟨510611, by rfl⟩ : syracuseStep 680815 = 1021223) B1021223
theorem B3269531 : Blo 678312 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B680871 : Blo 678312 680871 := bstep (se 1 (by rfl) ⟨510653, by rfl⟩ : syracuseStep 680871 = 1021307) B1021307
theorem B680955 : Blo 678312 680955 := bstep (se 1 (by rfl) ⟨510716, by rfl⟩ : syracuseStep 680955 = 1021433) B1021433
theorem B681023 : Blo 678312 681023 := bstep (se 1 (by rfl) ⟨510767, by rfl⟩ : syracuseStep 681023 = 1021535) B1021535
theorem B9299117 : Blo 678312 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B4908221 : Blo 678312 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B3728591 : Blo 678312 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B681167 : Blo 678312 681167 := bstep (se 1 (by rfl) ⟨510875, by rfl⟩ : syracuseStep 681167 = 1021751) B1021751
theorem B1533257 : Blo 678312 1533257 := bstep (se 2 (by rfl) ⟨574971, by rfl⟩ : syracuseStep 1533257 = 1149943) B1149943
theorem B681371 : Blo 678312 681371 := bstep (se 1 (by rfl) ⟨511028, by rfl⟩ : syracuseStep 681371 = 1022057) B1022057
theorem B16541101 : Blo 678312 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B681583 : Blo 678312 681583 := bstep (se 1 (by rfl) ⟨511187, by rfl⟩ : syracuseStep 681583 = 1022375) B1022375
theorem B681639 : Blo 678312 681639 := bstep (se 1 (by rfl) ⟨511229, by rfl⟩ : syracuseStep 681639 = 1022459) B1022459
theorem B1959643 : Blo 678312 1959643 := bstep (se 1 (by rfl) ⟨1469732, by rfl⟩ : syracuseStep 1959643 = 2939465) B2939465
theorem B681723 : Blo 678312 681723 := bstep (se 1 (by rfl) ⟨511292, by rfl⟩ : syracuseStep 681723 = 1022585) B1022585
theorem B681759 : Blo 678312 681759 := bstep (se 1 (by rfl) ⟨511319, by rfl⟩ : syracuseStep 681759 = 1022639) B1022639
theorem B681791 : Blo 678312 681791 := bstep (se 1 (by rfl) ⟨511343, by rfl⟩ : syracuseStep 681791 = 1022687) B1022687
theorem B681967 : Blo 678312 681967 := bstep (se 1 (by rfl) ⟨511475, by rfl⟩ : syracuseStep 681967 = 1022951) B1022951
theorem B29485133 : Blo 678312 29485133 := bstep (se 3 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 29485133 = 11056925) B11056925
theorem B682139 : Blo 678312 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B682175 : Blo 678312 682175 := bstep (se 1 (by rfl) ⟨511631, by rfl⟩ : syracuseStep 682175 = 1023263) B1023263
theorem B1534247 : Blo 678312 1534247 := bstep (se 1 (by rfl) ⟨1150685, by rfl⟩ : syracuseStep 1534247 = 2301371) B2301371
theorem B682287 : Blo 678312 682287 := bstep (se 1 (by rfl) ⟨511715, by rfl⟩ : syracuseStep 682287 = 1023431) B1023431
theorem B1534265 : Blo 678312 1534265 := bstep (se 2 (by rfl) ⟨575349, by rfl⟩ : syracuseStep 1534265 = 1150699) B1150699
theorem B2583515 : Blo 678312 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B2092007 : Blo 678312 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B106000109 : Blo 678312 106000109 := bstep (se 3 (by rfl) ⟨19875020, by rfl⟩ : syracuseStep 106000109 = 39750041) B39750041
theorem B14151667 : Blo 678312 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B3436667 : Blo 678312 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B3436829 : Blo 678312 3436829 := bstep (se 3 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 3436829 = 1288811) B1288811
theorem B2290031 : Blo 678312 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B2586113 : Blo 678312 2586113 := bstep (se 2 (by rfl) ⟨969792, by rfl⟩ : syracuseStep 2586113 = 1939585) B1939585
theorem B19559981 : Blo 678312 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B9434825 : Blo 678312 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B2291435 : Blo 678312 2291435 := bstep (se 1 (by rfl) ⟨1718576, by rfl⟩ : syracuseStep 2291435 = 3437153) B3437153
theorem B2586431 : Blo 678312 2586431 := bstep (se 1 (by rfl) ⟨1939823, by rfl⟩ : syracuseStep 2586431 = 3879647) B3879647
theorem B18610073 : Blo 678312 18610073 := bstep (se 2 (by rfl) ⟨6978777, by rfl⟩ : syracuseStep 18610073 = 13957555) B13957555
theorem B2291705 : Blo 678312 2291705 := bstep (se 2 (by rfl) ⟨859389, by rfl⟩ : syracuseStep 2291705 = 1718779) B1718779
theorem B1144975 : Blo 678312 1144975 := bstep (se 1 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 1144975 = 1717463) B1717463
theorem B2291867 : Blo 678312 2291867 := bstep (se 1 (by rfl) ⟨1718900, by rfl⟩ : syracuseStep 2291867 = 3437801) B3437801
theorem B2291975 : Blo 678312 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B2586887 : Blo 678312 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B7731773 : Blo 678312 7731773 := bstep (se 3 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 7731773 = 2899415) B2899415
theorem B1932329 : Blo 678312 1932329 := bstep (se 2 (by rfl) ⟨724623, by rfl⟩ : syracuseStep 1932329 = 1449247) B1449247
theorem B1145927 : Blo 678312 1145927 := bstep (se 1 (by rfl) ⟨859445, by rfl⟩ : syracuseStep 1145927 = 1718891) B1718891
theorem B3439745 : Blo 678312 3439745 := bstep (se 2 (by rfl) ⟨1289904, by rfl⟩ : syracuseStep 3439745 = 2579809) B2579809
theorem B2293001 : Blo 678312 2293001 := bstep (se 2 (by rfl) ⟨859875, by rfl⟩ : syracuseStep 2293001 = 1719751) B1719751
theorem B2588071 : Blo 678312 2588071 := bstep (se 1 (by rfl) ⟨1941053, by rfl⟩ : syracuseStep 2588071 = 3882107) B3882107
theorem B1146359 : Blo 678312 1146359 := bstep (se 1 (by rfl) ⟨859769, by rfl⟩ : syracuseStep 1146359 = 1719539) B1719539
theorem B3440555 : Blo 678312 3440555 := bstep (se 1 (by rfl) ⟨2580416, by rfl⟩ : syracuseStep 3440555 = 5160833) B5160833
theorem B1147115 : Blo 678312 1147115 := bstep (se 1 (by rfl) ⟨860336, by rfl⟩ : syracuseStep 1147115 = 1720673) B1720673
theorem B1180075 : Blo 678312 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B3867209 : Blo 678312 3867209 := bstep (se 2 (by rfl) ⟨1450203, by rfl⟩ : syracuseStep 3867209 = 2900407) B2900407
theorem B2294351 : Blo 678312 2294351 := bstep (se 1 (by rfl) ⟨1720763, by rfl⟩ : syracuseStep 2294351 = 3441527) B3441527
theorem B8389423 : Blo 678312 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B3670957 : Blo 678312 3670957 := bstep (se 3 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 3670957 = 1376609) B1376609
theorem B3441689 : Blo 678312 3441689 := bstep (se 2 (by rfl) ⟨1290633, by rfl⟩ : syracuseStep 3441689 = 2581267) B2581267
theorem B2294891 : Blo 678312 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B2589803 : Blo 678312 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B5244061 : Blo 678312 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B689375 : Blo 678312 689375 := bstep (se 1 (by rfl) ⟨517031, by rfl⟩ : syracuseStep 689375 = 1034063) B1034063
theorem B1311967 : Blo 678312 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B1148411 : Blo 678312 1148411 := bstep (se 1 (by rfl) ⟨861308, by rfl⟩ : syracuseStep 1148411 = 1722617) B1722617
theorem B2590289 : Blo 678312 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B5801975 : Blo 678312 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B1017887 : Blo 678312 1017887 := bstep (se 1 (by rfl) ⟨763415, by rfl⟩ : syracuseStep 1017887 = 1526831) B1526831
theorem B1018079 : Blo 678312 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B1018139 : Blo 678312 1018139 := bstep (se 1 (by rfl) ⟨763604, by rfl⟩ : syracuseStep 1018139 = 1527209) B1527209
theorem B5179787 : Blo 678312 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B8718749 : Blo 678312 8718749 := bstep (se 3 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 8718749 = 3269531) B3269531
theorem B1018463 : Blo 678312 1018463 := bstep (se 1 (by rfl) ⟨763847, by rfl⟩ : syracuseStep 1018463 = 1527695) B1527695
theorem B1018745 : Blo 678312 1018745 := bstep (se 2 (by rfl) ⟨382029, by rfl⟩ : syracuseStep 1018745 = 764059) B764059
theorem B1018793 : Blo 678312 1018793 := bstep (se 2 (by rfl) ⟨382047, by rfl⟩ : syracuseStep 1018793 = 764095) B764095
theorem B1018943 : Blo 678312 1018943 := bstep (se 1 (by rfl) ⟨764207, by rfl⟩ : syracuseStep 1018943 = 1528415) B1528415
theorem B4361323 : Blo 678312 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B1150139 : Blo 678312 1150139 := bstep (se 1 (by rfl) ⟨862604, by rfl⟩ : syracuseStep 1150139 = 1725209) B1725209
theorem B1019495 : Blo 678312 1019495 := bstep (se 1 (by rfl) ⟨764621, by rfl⟩ : syracuseStep 1019495 = 1529243) B1529243
theorem B23564195 : Blo 678312 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B1019879 : Blo 678312 1019879 := bstep (se 1 (by rfl) ⟨764909, by rfl⟩ : syracuseStep 1019879 = 1529819) B1529819
theorem B5541871 : Blo 678312 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B724987 : Blo 678312 724987 := bstep (se 1 (by rfl) ⟨543740, by rfl⟩ : syracuseStep 724987 = 1087481) B1087481
theorem B1019999 : Blo 678312 1019999 := bstep (se 1 (by rfl) ⟨764999, by rfl⟩ : syracuseStep 1019999 = 1529999) B1529999
theorem B1020011 : Blo 678312 1020011 := bstep (se 1 (by rfl) ⟨765008, by rfl⟩ : syracuseStep 1020011 = 1530017) B1530017
theorem B1020059 : Blo 678312 1020059 := bstep (se 1 (by rfl) ⟨765044, by rfl⟩ : syracuseStep 1020059 = 1530089) B1530089
theorem B1151131 : Blo 678312 1151131 := bstep (se 1 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 1151131 = 1726697) B1726697
theorem B23531741 : Blo 678312 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B7344425 : Blo 678312 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B1151273 : Blo 678312 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B5509549 : Blo 678312 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B3183371 : Blo 678312 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B8721209 : Blo 678312 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B3871583 : Blo 678312 3871583 := bstep (se 1 (by rfl) ⟨2903687, by rfl⟩ : syracuseStep 3871583 = 5807375) B5807375
theorem B1020911 : Blo 678312 1020911 := bstep (se 1 (by rfl) ⟨765683, by rfl⟩ : syracuseStep 1020911 = 1531367) B1531367
theorem B79303697 : Blo 678312 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B1938593 : Blo 678312 1938593 := bstep (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) B1453945
theorem B1021295 : Blo 678312 1021295 := bstep (se 1 (by rfl) ⟨765971, by rfl⟩ : syracuseStep 1021295 = 1531943) B1531943
theorem B1021415 : Blo 678312 1021415 := bstep (se 1 (by rfl) ⟨766061, by rfl⟩ : syracuseStep 1021415 = 1532123) B1532123
theorem B1021577 : Blo 678312 1021577 := bstep (se 2 (by rfl) ⟨383091, by rfl⟩ : syracuseStep 1021577 = 766183) B766183
theorem B1021595 : Blo 678312 1021595 := bstep (se 1 (by rfl) ⟨766196, by rfl⟩ : syracuseStep 1021595 = 1532393) B1532393
theorem B1021787 : Blo 678312 1021787 := bstep (se 1 (by rfl) ⟨766340, by rfl⟩ : syracuseStep 1021787 = 1532681) B1532681
theorem B12556147 : Blo 678312 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B6199411 : Blo 678312 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B1022171 : Blo 678312 1022171 := bstep (se 1 (by rfl) ⟨766628, by rfl⟩ : syracuseStep 1022171 = 1533257) B1533257
theorem B1022441 : Blo 678312 1022441 := bstep (se 2 (by rfl) ⟨383415, by rfl⟩ : syracuseStep 1022441 = 766831) B766831
theorem B2300669 : Blo 678312 2300669 := bstep (se 3 (by rfl) ⟨431375, by rfl⟩ : syracuseStep 2300669 = 862751) B862751
theorem B1022831 : Blo 678312 1022831 := bstep (se 1 (by rfl) ⟨767123, by rfl⟩ : syracuseStep 1022831 = 1534247) B1534247
theorem B1022843 : Blo 678312 1022843 := bstep (se 1 (by rfl) ⟨767132, by rfl⟩ : syracuseStep 1022843 = 1534265) B1534265
theorem B88219205 : Blo 678312 88219205 := bstep (se 4 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 88219205 = 16541101) B16541101
theorem B6627035 : Blo 678312 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B3874817 : Blo 678312 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B860959 : Blo 678312 860959 := bstep (se 1 (by rfl) ⟨645719, by rfl⟩ : syracuseStep 860959 = 1291439) B1291439
theorem B1942649 : Blo 678312 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B5154515 : Blo 678312 5154515 := bstep (se 1 (by rfl) ⟨3865886, by rfl⟩ : syracuseStep 5154515 = 7731773) B7731773
theorem B3450761 : Blo 678312 3450761 := bstep (se 2 (by rfl) ⟨1294035, by rfl⟩ : syracuseStep 3450761 = 2588071) B2588071
theorem B17704927 : Blo 678312 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B1288219 : Blo 678312 1288219 := bstep (se 1 (by rfl) ⟨966164, by rfl⟩ : syracuseStep 1288219 = 1932329) B1932329
theorem B763951 : Blo 678312 763951 := bstep (se 1 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 763951 = 1145927) B1145927
theorem B862255 : Blo 678312 862255 := bstep (se 1 (by rfl) ⟨646691, by rfl⟩ : syracuseStep 862255 = 1293383) B1293383
theorem B764239 : Blo 678312 764239 := bstep (se 1 (by rfl) ⟨573179, by rfl⟩ : syracuseStep 764239 = 1146359) B1146359
theorem B12397009 : Blo 678312 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B764923 : Blo 678312 764923 := bstep (se 1 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 764923 = 1147385) B1147385
theorem B765103 : Blo 678312 765103 := bstep (se 1 (by rfl) ⟨573827, by rfl⟩ : syracuseStep 765103 = 1147655) B1147655
theorem B1453801 : Blo 678312 1453801 := bstep (se 2 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 1453801 = 1090351) B1090351
theorem B765823 : Blo 678312 765823 := bstep (se 1 (by rfl) ⟨574367, by rfl⟩ : syracuseStep 765823 = 1148735) B1148735
theorem B3452867 : Blo 678312 3452867 := bstep (se 1 (by rfl) ⟨2589650, by rfl⟩ : syracuseStep 3452867 = 5179301) B5179301
theorem B100642823 : Blo 678312 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B1290323 : Blo 678312 1290323 := bstep (se 1 (by rfl) ⟨967742, by rfl⟩ : syracuseStep 1290323 = 1935485) B1935485
theorem B766363 : Blo 678312 766363 := bstep (se 1 (by rfl) ⟨574772, by rfl⟩ : syracuseStep 766363 = 1149545) B1149545
theorem B1717159 : Blo 678312 1717159 := bstep (se 1 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 1717159 = 2575739) B2575739
theorem B1455175 : Blo 678312 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B767047 : Blo 678312 767047 := bstep (se 1 (by rfl) ⟨575285, by rfl⟩ : syracuseStep 767047 = 1150571) B1150571
theorem B4371677 : Blo 678312 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B767227 : Blo 678312 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B12433277 : Blo 678312 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B5519411 : Blo 678312 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B1718567 : Blo 678312 1718567 := bstep (se 1 (by rfl) ⟨1288925, by rfl⟩ : syracuseStep 1718567 = 2577851) B2577851
theorem B2898665 : Blo 678312 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B6536375 : Blo 678312 6536375 := bstep (se 1 (by rfl) ⟨4902281, by rfl⟩ : syracuseStep 6536375 = 9804563) B9804563
theorem B1228007 : Blo 678312 1228007 := bstep (se 1 (by rfl) ⟨921005, by rfl⟩ : syracuseStep 1228007 = 1842011) B1842011
theorem B1720511 : Blo 678312 1720511 := bstep (se 1 (by rfl) ⟨1290383, by rfl⟩ : syracuseStep 1720511 = 2580767) B2580767
theorem B1294879 : Blo 678312 1294879 := bstep (se 1 (by rfl) ⟨971159, by rfl⟩ : syracuseStep 1294879 = 1942319) B1942319
theorem B5882665 : Blo 678312 5882665 := bstep (se 2 (by rfl) ⟨2205999, by rfl⟩ : syracuseStep 5882665 = 4411999) B4411999
theorem B6275969 : Blo 678312 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B7095961 : Blo 678312 7095961 := bstep (se 2 (by rfl) ⟨2660985, by rfl⟩ : syracuseStep 7095961 = 5321971) B5321971
theorem B8406773 : Blo 678312 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B1722343 : Blo 678312 1722343 := bstep (se 1 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 1722343 = 2583515) B2583515
theorem B1394671 : Blo 678312 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B5818513 : Blo 678312 5818513 := bstep (se 2 (by rfl) ⟨2181942, by rfl⟩ : syracuseStep 5818513 = 4363885) B4363885
theorem B11028905 : Blo 678312 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B70666739 : Blo 678312 70666739 := bstep (se 1 (by rfl) ⟨53000054, by rfl⟩ : syracuseStep 70666739 = 106000109) B106000109
theorem B1526633 : Blo 678312 1526633 := bstep (se 2 (by rfl) ⟨572487, by rfl⟩ : syracuseStep 1526633 = 1144975) B1144975
theorem B1723265 : Blo 678312 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B1526687 : Blo 678312 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B9817307 : Blo 678312 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B9096425 : Blo 678312 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B7359905 : Blo 678312 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B5819849 : Blo 678312 5819849 := bstep (se 2 (by rfl) ⟨2182443, by rfl⟩ : syracuseStep 5819849 = 4364887) B4364887
theorem B1724075 : Blo 678312 1724075 := bstep (se 1 (by rfl) ⟨1293056, by rfl⟩ : syracuseStep 1724075 = 2586113) B2586113
theorem B1527623 : Blo 678312 1527623 := bstep (se 1 (by rfl) ⟨1145717, by rfl⟩ : syracuseStep 1527623 = 2291435) B2291435
theorem B1724287 : Blo 678312 1724287 := bstep (se 1 (by rfl) ⟨1293215, by rfl⟩ : syracuseStep 1724287 = 2586431) B2586431
theorem B12406715 : Blo 678312 12406715 := bstep (se 1 (by rfl) ⟨9305036, by rfl⟩ : syracuseStep 12406715 = 18610073) B18610073
theorem B1527803 : Blo 678312 1527803 := bstep (se 1 (by rfl) ⟨1145852, by rfl⟩ : syracuseStep 1527803 = 2291705) B2291705
theorem B1527911 : Blo 678312 1527911 := bstep (se 1 (by rfl) ⟨1145933, by rfl⟩ : syracuseStep 1527911 = 2291867) B2291867
theorem B1527983 : Blo 678312 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B1724591 : Blo 678312 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B971131 : Blo 678312 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B2904457 : Blo 678312 2904457 := bstep (se 2 (by rfl) ⟨1089171, by rfl⟩ : syracuseStep 2904457 = 2178343) B2178343
theorem B1528667 : Blo 678312 1528667 := bstep (se 1 (by rfl) ⟨1146500, by rfl⟩ : syracuseStep 1528667 = 2293001) B2293001
theorem B1529423 : Blo 678312 1529423 := bstep (se 1 (by rfl) ⟨1147067, by rfl⟩ : syracuseStep 1529423 = 2294135) B2294135
theorem B4905107 : Blo 678312 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B94197917 : Blo 678312 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B1530143 : Blo 678312 1530143 := bstep (se 1 (by rfl) ⟨1147607, by rfl⟩ : syracuseStep 1530143 = 2295215) B2295215
theorem B1726879 : Blo 678312 1726879 := bstep (se 1 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 1726879 = 2590319) B2590319
theorem B2185633 : Blo 678312 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B678351 : Blo 678312 678351 := bstep (se 1 (by rfl) ⟨508763, by rfl⟩ : syracuseStep 678351 = 1017527) B1017527
theorem B678375 : Blo 678312 678375 := bstep (se 1 (by rfl) ⟨508781, by rfl⟩ : syracuseStep 678375 = 1017563) B1017563
theorem B4413971 : Blo 678312 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B1530395 : Blo 678312 1530395 := bstep (se 1 (by rfl) ⟨1147796, by rfl⟩ : syracuseStep 1530395 = 2295593) B2295593
theorem B12376637 : Blo 678312 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B678491 : Blo 678312 678491 := bstep (se 1 (by rfl) ⟨508868, by rfl⟩ : syracuseStep 678491 = 1017737) B1017737
theorem B678559 : Blo 678312 678559 := bstep (se 1 (by rfl) ⟨508919, by rfl⟩ : syracuseStep 678559 = 1017839) B1017839
theorem B678727 : Blo 678312 678727 := bstep (se 1 (by rfl) ⟨509045, by rfl⟩ : syracuseStep 678727 = 1018091) B1018091
theorem B13097807 : Blo 678312 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B678767 : Blo 678312 678767 := bstep (se 1 (by rfl) ⟨509075, by rfl⟩ : syracuseStep 678767 = 1018151) B1018151
theorem B678823 : Blo 678312 678823 := bstep (se 1 (by rfl) ⟨509117, by rfl⟩ : syracuseStep 678823 = 1018235) B1018235
theorem B679003 : Blo 678312 679003 := bstep (se 1 (by rfl) ⟨509252, by rfl⟩ : syracuseStep 679003 = 1018505) B1018505
theorem B679119 : Blo 678312 679119 := bstep (se 1 (by rfl) ⟨509339, by rfl⟩ : syracuseStep 679119 = 1018679) B1018679
theorem B679143 : Blo 678312 679143 := bstep (se 1 (by rfl) ⟨509357, by rfl⟩ : syracuseStep 679143 = 1018715) B1018715
theorem B679239 : Blo 678312 679239 := bstep (se 1 (by rfl) ⟨509429, by rfl⟩ : syracuseStep 679239 = 1018859) B1018859
theorem B4906433 : Blo 678312 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B679375 : Blo 678312 679375 := bstep (se 1 (by rfl) ⟨509531, by rfl⟩ : syracuseStep 679375 = 1019063) B1019063
theorem B679535 : Blo 678312 679535 := bstep (se 1 (by rfl) ⟨509651, by rfl⟩ : syracuseStep 679535 = 1019303) B1019303
theorem B2612857 : Blo 678312 2612857 := bstep (se 2 (by rfl) ⟨979821, by rfl⟩ : syracuseStep 2612857 = 1959643) B1959643
theorem B679591 : Blo 678312 679591 := bstep (se 1 (by rfl) ⟨509693, by rfl⟩ : syracuseStep 679591 = 1019387) B1019387
theorem B679655 : Blo 678312 679655 := bstep (se 1 (by rfl) ⟨509741, by rfl⟩ : syracuseStep 679655 = 1019483) B1019483
theorem B679711 : Blo 678312 679711 := bstep (se 1 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 679711 = 1019567) B1019567
theorem B1531745 : Blo 678312 1531745 := bstep (se 2 (by rfl) ⟨574404, by rfl⟩ : syracuseStep 1531745 = 1148809) B1148809
theorem B679791 : Blo 678312 679791 := bstep (se 1 (by rfl) ⟨509843, by rfl⟩ : syracuseStep 679791 = 1019687) B1019687
theorem B679847 : Blo 678312 679847 := bstep (se 1 (by rfl) ⟨509885, by rfl⟩ : syracuseStep 679847 = 1019771) B1019771
theorem B1531871 : Blo 678312 1531871 := bstep (se 1 (by rfl) ⟨1148903, by rfl⟩ : syracuseStep 1531871 = 2297807) B2297807
theorem B680127 : Blo 678312 680127 := bstep (se 1 (by rfl) ⟨510095, by rfl⟩ : syracuseStep 680127 = 1020191) B1020191
theorem B680143 : Blo 678312 680143 := bstep (se 1 (by rfl) ⟨510107, by rfl⟩ : syracuseStep 680143 = 1020215) B1020215
theorem B680191 : Blo 678312 680191 := bstep (se 1 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 680191 = 1020287) B1020287
theorem B1532159 : Blo 678312 1532159 := bstep (se 1 (by rfl) ⟨1149119, by rfl⟩ : syracuseStep 1532159 = 2298239) B2298239
theorem B680239 : Blo 678312 680239 := bstep (se 1 (by rfl) ⟨510179, by rfl⟩ : syracuseStep 680239 = 1020359) B1020359
theorem B1532321 : Blo 678312 1532321 := bstep (se 2 (by rfl) ⟨574620, by rfl⟩ : syracuseStep 1532321 = 1149241) B1149241
theorem B680475 : Blo 678312 680475 := bstep (se 1 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 680475 = 1020713) B1020713
theorem B680479 : Blo 678312 680479 := bstep (se 1 (by rfl) ⟨510359, by rfl⟩ : syracuseStep 680479 = 1020719) B1020719
theorem B680559 : Blo 678312 680559 := bstep (se 1 (by rfl) ⟨510419, by rfl⟩ : syracuseStep 680559 = 1020839) B1020839
theorem B680615 : Blo 678312 680615 := bstep (se 1 (by rfl) ⟨510461, by rfl⟩ : syracuseStep 680615 = 1020923) B1020923
theorem B2908847 : Blo 678312 2908847 := bstep (se 1 (by rfl) ⟨2181635, by rfl⟩ : syracuseStep 2908847 = 4363271) B4363271
theorem B680655 : Blo 678312 680655 := bstep (se 1 (by rfl) ⟨510491, by rfl⟩ : syracuseStep 680655 = 1020983) B1020983
theorem B680735 : Blo 678312 680735 := bstep (se 1 (by rfl) ⟨510551, by rfl⟩ : syracuseStep 680735 = 1021103) B1021103
theorem B20964395 : Blo 678312 20964395 := bstep (se 1 (by rfl) ⟨15723296, by rfl⟩ : syracuseStep 20964395 = 31446593) B31446593
theorem B681007 : Blo 678312 681007 := bstep (se 1 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 681007 = 1021511) B1021511
theorem B681071 : Blo 678312 681071 := bstep (se 1 (by rfl) ⟨510803, by rfl⟩ : syracuseStep 681071 = 1021607) B1021607
theorem B681127 : Blo 678312 681127 := bstep (se 1 (by rfl) ⟨510845, by rfl⟩ : syracuseStep 681127 = 1021691) B1021691
theorem B1533095 : Blo 678312 1533095 := bstep (se 1 (by rfl) ⟨1149821, by rfl⟩ : syracuseStep 1533095 = 2299643) B2299643
theorem B681151 : Blo 678312 681151 := bstep (se 1 (by rfl) ⟨510863, by rfl⟩ : syracuseStep 681151 = 1021727) B1021727
theorem B681183 : Blo 678312 681183 := bstep (se 1 (by rfl) ⟨510887, by rfl⟩ : syracuseStep 681183 = 1021775) B1021775
theorem B1533203 : Blo 678312 1533203 := bstep (se 1 (by rfl) ⟨1149902, by rfl⟩ : syracuseStep 1533203 = 2299805) B2299805
theorem B681263 : Blo 678312 681263 := bstep (se 1 (by rfl) ⟨510947, by rfl⟩ : syracuseStep 681263 = 1021895) B1021895
theorem B681499 : Blo 678312 681499 := bstep (se 1 (by rfl) ⟨511124, by rfl⟩ : syracuseStep 681499 = 1022249) B1022249
theorem B681503 : Blo 678312 681503 := bstep (se 1 (by rfl) ⟨511127, by rfl⟩ : syracuseStep 681503 = 1022255) B1022255
theorem B4351583 : Blo 678312 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B681663 : Blo 678312 681663 := bstep (se 1 (by rfl) ⟨511247, by rfl⟩ : syracuseStep 681663 = 1022495) B1022495
theorem B1533833 : Blo 678312 1533833 := bstep (se 2 (by rfl) ⟨575187, by rfl⟩ : syracuseStep 1533833 = 1150375) B1150375
theorem B1533851 : Blo 678312 1533851 := bstep (se 1 (by rfl) ⟨1150388, by rfl⟩ : syracuseStep 1533851 = 2300777) B2300777
theorem B1533887 : Blo 678312 1533887 := bstep (se 1 (by rfl) ⟨1150415, by rfl⟩ : syracuseStep 1533887 = 2300831) B2300831
theorem B681919 : Blo 678312 681919 := bstep (se 1 (by rfl) ⟨511439, by rfl⟩ : syracuseStep 681919 = 1022879) B1022879
theorem B681951 : Blo 678312 681951 := bstep (se 1 (by rfl) ⟨511463, by rfl⟩ : syracuseStep 681951 = 1022927) B1022927
theorem B682011 : Blo 678312 682011 := bstep (se 1 (by rfl) ⟨511508, by rfl⟩ : syracuseStep 682011 = 1023017) B1023017
theorem B682015 : Blo 678312 682015 := bstep (se 1 (by rfl) ⟨511511, by rfl⟩ : syracuseStep 682015 = 1023023) B1023023
theorem B682031 : Blo 678312 682031 := bstep (se 1 (by rfl) ⟨511523, by rfl⟩ : syracuseStep 682031 = 1023047) B1023047
theorem B6973523 : Blo 678312 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B1534049 : Blo 678312 1534049 := bstep (se 2 (by rfl) ⟨575268, by rfl⟩ : syracuseStep 1534049 = 1150537) B1150537
theorem B1697915 : Blo 678312 1697915 := bstep (se 1 (by rfl) ⟨1273436, by rfl⟩ : syracuseStep 1697915 = 2546873) B2546873
theorem B682207 : Blo 678312 682207 := bstep (se 1 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 682207 = 1023311) B1023311
theorem B682267 : Blo 678312 682267 := bstep (se 1 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 682267 = 1023401) B1023401
theorem B3107297 : Blo 678312 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B18868889 : Blo 678312 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B107342779 : Blo 678312 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B3272147 : Blo 678312 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B2485727 : Blo 678312 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B11595473 : Blo 678312 11595473 := bstep (se 2 (by rfl) ⟨4348302, by rfl⟩ : syracuseStep 11595473 = 8696605) B8696605
theorem B19656755 : Blo 678312 19656755 := bstep (se 1 (by rfl) ⟨14742566, by rfl⟩ : syracuseStep 19656755 = 29485133) B29485133
theorem B2289761 : Blo 678312 2289761 := bstep (se 2 (by rfl) ⟨858660, by rfl⟩ : syracuseStep 2289761 = 1717321) B1717321
theorem B12415169 : Blo 678312 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B2912537 : Blo 678312 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B2584943 : Blo 678312 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B7762391 : Blo 678312 7762391 := bstep (se 1 (by rfl) ⟨5821793, by rfl⟩ : syracuseStep 7762391 = 11643587) B11643587
theorem B2291111 : Blo 678312 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B2291219 : Blo 678312 2291219 := bstep (se 1 (by rfl) ⟨1718414, by rfl⟩ : syracuseStep 2291219 = 3436829) B3436829
theorem B5797601 : Blo 678312 5797601 := bstep (se 2 (by rfl) ⟨2174100, by rfl⟩ : syracuseStep 5797601 = 4348201) B4348201
theorem B7763849 : Blo 678312 7763849 := bstep (se 2 (by rfl) ⟨2911443, by rfl⟩ : syracuseStep 7763849 = 5822887) B5822887
theorem B2914487 : Blo 678312 2914487 := bstep (se 1 (by rfl) ⟨2185865, by rfl⟩ : syracuseStep 2914487 = 4371731) B4371731
theorem B1145063 : Blo 678312 1145063 := bstep (se 1 (by rfl) ⟨858797, by rfl⟩ : syracuseStep 1145063 = 1717595) B1717595
theorem B13039987 : Blo 678312 13039987 := bstep (se 1 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 13039987 = 19559981) B19559981
theorem B6289883 : Blo 678312 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B3111529 : Blo 678312 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B2292353 : Blo 678312 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B2325217 : Blo 678312 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B1145947 : Blo 678312 1145947 := bstep (se 1 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 1145947 = 1718921) B1718921
theorem B818267 : Blo 678312 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B1932511 : Blo 678312 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B1932569 : Blo 678312 1932569 := bstep (se 2 (by rfl) ⟨724713, by rfl⟩ : syracuseStep 1932569 = 1449427) B1449427
theorem B2293163 : Blo 678312 2293163 := bstep (se 1 (by rfl) ⟨1719872, by rfl⟩ : syracuseStep 2293163 = 3439745) B3439745
theorem B3440393 : Blo 678312 3440393 := bstep (se 2 (by rfl) ⟨1290147, by rfl⟩ : syracuseStep 3440393 = 2580295) B2580295
theorem B1146703 : Blo 678312 1146703 := bstep (se 1 (by rfl) ⟨860027, by rfl⟩ : syracuseStep 1146703 = 1720055) B1720055
theorem B1638265 : Blo 678312 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B1146791 : Blo 678312 1146791 := bstep (se 1 (by rfl) ⟨860093, by rfl⟩ : syracuseStep 1146791 = 1720187) B1720187
theorem B2293703 : Blo 678312 2293703 := bstep (se 1 (by rfl) ⟨1720277, by rfl⟩ : syracuseStep 2293703 = 3440555) B3440555
theorem B1147007 : Blo 678312 1147007 := bstep (se 1 (by rfl) ⟨860255, by rfl⟩ : syracuseStep 1147007 = 1720511) B1720511
theorem B1573433 : Blo 678312 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B2294459 : Blo 678312 2294459 := bstep (se 1 (by rfl) ⟨1720844, by rfl⟩ : syracuseStep 2294459 = 3441689) B3441689
theorem B7766765 : Blo 678312 7766765 := bstep (se 3 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 7766765 = 2912537) B2912537
theorem B1147945 : Blo 678312 1147945 := bstep (se 2 (by rfl) ⟨430479, by rfl⟩ : syracuseStep 1147945 = 860959) B860959
theorem B5604515 : Blo 678312 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B3867983 : Blo 678312 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B1017755 : Blo 678312 1017755 := bstep (se 1 (by rfl) ⟨763316, by rfl⟩ : syracuseStep 1017755 = 1526633) B1526633
theorem B1148843 : Blo 678312 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B1017791 : Blo 678312 1017791 := bstep (se 1 (by rfl) ⟨763343, by rfl⟩ : syracuseStep 1017791 = 1526687) B1526687
theorem B6064283 : Blo 678312 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B1149383 : Blo 678312 1149383 := bstep (se 1 (by rfl) ⟨862037, by rfl⟩ : syracuseStep 1149383 = 1724075) B1724075
theorem B1018415 : Blo 678312 1018415 := bstep (se 1 (by rfl) ⟨763811, by rfl⟩ : syracuseStep 1018415 = 1527623) B1527623
theorem B2296457 : Blo 678312 2296457 := bstep (se 2 (by rfl) ⟨861171, by rfl⟩ : syracuseStep 2296457 = 1722343) B1722343
theorem B1018535 : Blo 678312 1018535 := bstep (se 1 (by rfl) ⟨763901, by rfl⟩ : syracuseStep 1018535 = 1527803) B1527803
theorem B1018601 : Blo 678312 1018601 := bstep (se 2 (by rfl) ⟨381975, by rfl⟩ : syracuseStep 1018601 = 763951) B763951
theorem B1149673 : Blo 678312 1149673 := bstep (se 2 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 1149673 = 862255) B862255
theorem B1018607 : Blo 678312 1018607 := bstep (se 1 (by rfl) ⟨763955, by rfl⟩ : syracuseStep 1018607 = 1527911) B1527911
theorem B1018655 : Blo 678312 1018655 := bstep (se 1 (by rfl) ⟨763991, by rfl⟩ : syracuseStep 1018655 = 1527983) B1527983
theorem B1149727 : Blo 678312 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B1018985 : Blo 678312 1018985 := bstep (se 2 (by rfl) ⟨382119, by rfl⟩ : syracuseStep 1018985 = 764239) B764239
theorem B1019111 : Blo 678312 1019111 := bstep (se 1 (by rfl) ⟨764333, by rfl⟩ : syracuseStep 1019111 = 1528667) B1528667
theorem B1838333 : Blo 678312 1838333 := bstep (se 3 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 1838333 = 689375) B689375
theorem B1019615 : Blo 678312 1019615 := bstep (se 1 (by rfl) ⟨764711, by rfl⟩ : syracuseStep 1019615 = 1529423) B1529423
theorem B1019897 : Blo 678312 1019897 := bstep (se 2 (by rfl) ⟨382461, by rfl⟩ : syracuseStep 1019897 = 764923) B764923
theorem B1020095 : Blo 678312 1020095 := bstep (se 1 (by rfl) ⟨765071, by rfl⟩ : syracuseStep 1020095 = 1530143) B1530143
theorem B1020137 : Blo 678312 1020137 := bstep (se 2 (by rfl) ⟨382551, by rfl⟩ : syracuseStep 1020137 = 765103) B765103
theorem B11604221 : Blo 678312 11604221 := bstep (se 3 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 11604221 = 4351583) B4351583
theorem B1020263 : Blo 678312 1020263 := bstep (se 1 (by rfl) ⟨765197, by rfl⟩ : syracuseStep 1020263 = 1530395) B1530395
theorem B1938401 : Blo 678312 1938401 := bstep (se 2 (by rfl) ⟨726900, by rfl⟩ : syracuseStep 1938401 = 1453801) B1453801
theorem B1021097 : Blo 678312 1021097 := bstep (se 2 (by rfl) ⟨382911, by rfl⟩ : syracuseStep 1021097 = 765823) B765823
theorem B2299049 : Blo 678312 2299049 := bstep (se 2 (by rfl) ⟨862143, by rfl⟩ : syracuseStep 2299049 = 1724287) B1724287
theorem B1021163 : Blo 678312 1021163 := bstep (se 1 (by rfl) ⟨765872, by rfl⟩ : syracuseStep 1021163 = 1531745) B1531745
theorem B1021247 : Blo 678312 1021247 := bstep (se 1 (by rfl) ⟨765935, by rfl⟩ : syracuseStep 1021247 = 1531871) B1531871
theorem B1021439 : Blo 678312 1021439 := bstep (se 1 (by rfl) ⟨766079, by rfl⟩ : syracuseStep 1021439 = 1532159) B1532159
theorem B1021547 : Blo 678312 1021547 := bstep (se 1 (by rfl) ⟨766160, by rfl⟩ : syracuseStep 1021547 = 1532321) B1532321
theorem B1939231 : Blo 678312 1939231 := bstep (se 1 (by rfl) ⟨1454423, by rfl⟩ : syracuseStep 1939231 = 2908847) B2908847
theorem B3872609 : Blo 678312 3872609 := bstep (se 2 (by rfl) ⟨1452228, by rfl⟩ : syracuseStep 3872609 = 2904457) B2904457
theorem B1021817 : Blo 678312 1021817 := bstep (se 2 (by rfl) ⟨383181, by rfl⟩ : syracuseStep 1021817 = 766363) B766363
theorem B7346065 : Blo 678312 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B1022063 : Blo 678312 1022063 := bstep (se 1 (by rfl) ⟨766547, by rfl⟩ : syracuseStep 1022063 = 1533095) B1533095
theorem B1022135 : Blo 678312 1022135 := bstep (se 1 (by rfl) ⟨766601, by rfl⟩ : syracuseStep 1022135 = 1533203) B1533203
theorem B2300507 : Blo 678312 2300507 := bstep (se 1 (by rfl) ⟨1725380, by rfl⟩ : syracuseStep 2300507 = 3450761) B3450761
theorem B1022555 : Blo 678312 1022555 := bstep (se 1 (by rfl) ⟨766916, by rfl⟩ : syracuseStep 1022555 = 1533833) B1533833
theorem B1022567 : Blo 678312 1022567 := bstep (se 1 (by rfl) ⟨766925, by rfl⟩ : syracuseStep 1022567 = 1533851) B1533851
theorem B1022591 : Blo 678312 1022591 := bstep (se 1 (by rfl) ⟨766943, by rfl⟩ : syracuseStep 1022591 = 1533887) B1533887
theorem B1022699 : Blo 678312 1022699 := bstep (se 1 (by rfl) ⟨767024, by rfl⟩ : syracuseStep 1022699 = 1534049) B1534049
theorem B1022729 : Blo 678312 1022729 := bstep (se 2 (by rfl) ⟨383523, by rfl⟩ : syracuseStep 1022729 = 767047) B767047
theorem B2071531 : Blo 678312 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B1022969 : Blo 678312 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B2301911 : Blo 678312 2301911 := bstep (se 1 (by rfl) ⟨1726433, by rfl⟩ : syracuseStep 2301911 = 3452867) B3452867
theorem B860215 : Blo 678312 860215 := bstep (se 1 (by rfl) ⟨645161, by rfl⟩ : syracuseStep 860215 = 1290323) B1290323
theorem B8265881 : Blo 678312 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B2302505 : Blo 678312 2302505 := bstep (se 2 (by rfl) ⟨863439, by rfl⟩ : syracuseStep 2302505 = 1726879) B1726879
theorem B3679607 : Blo 678312 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B1942991 : Blo 678312 1942991 := bstep (se 1 (by rfl) ⟨1457243, by rfl⟩ : syracuseStep 1942991 = 2914487) B2914487
theorem B763375 : Blo 678312 763375 := bstep (se 1 (by rfl) ⟨572531, by rfl⟩ : syracuseStep 763375 = 1145063) B1145063
theorem B3483809 : Blo 678312 3483809 := bstep (se 2 (by rfl) ⟨1306428, by rfl⟩ : syracuseStep 3483809 = 2612857) B2612857
theorem B1288379 : Blo 678312 1288379 := bstep (se 1 (by rfl) ⟨966284, by rfl⟩ : syracuseStep 1288379 = 1932569) B1932569
theorem B764527 : Blo 678312 764527 := bstep (se 1 (by rfl) ⟨573395, by rfl⟩ : syracuseStep 764527 = 1146791) B1146791
theorem B764743 : Blo 678312 764743 := bstep (se 1 (by rfl) ⟨573557, by rfl⟩ : syracuseStep 764743 = 1147115) B1147115
theorem B8728181 : Blo 678312 8728181 := bstep (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) B818267
theorem B765607 : Blo 678312 765607 := bstep (se 1 (by rfl) ⟨574205, by rfl⟩ : syracuseStep 765607 = 1148411) B1148411
theorem B7843553 : Blo 678312 7843553 := bstep (se 2 (by rfl) ⟨2941332, by rfl⟩ : syracuseStep 7843553 = 5882665) B5882665
theorem B11185897 : Blo 678312 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B4894609 : Blo 678312 4894609 := bstep (se 2 (by rfl) ⟨1835478, by rfl⟩ : syracuseStep 4894609 = 3670957) B3670957
theorem B6992081 : Blo 678312 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B3453191 : Blo 678312 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B5812499 : Blo 678312 5812499 := bstep (se 1 (by rfl) ⟨4359374, by rfl⟩ : syracuseStep 5812499 = 8718749) B8718749
theorem B7352603 : Blo 678312 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B1749289 : Blo 678312 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B766759 : Blo 678312 766759 := bstep (se 1 (by rfl) ⟨575069, by rfl⟩ : syracuseStep 766759 = 1150139) B1150139
theorem B3879899 : Blo 678312 3879899 := bstep (se 1 (by rfl) ⟨2909924, by rfl⟩ : syracuseStep 3879899 = 5819849) B5819849
theorem B15709463 : Blo 678312 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B8271143 : Blo 678312 8271143 := bstep (se 1 (by rfl) ⟨6203357, by rfl⟩ : syracuseStep 8271143 = 12406715) B12406715
theorem B23606569 : Blo 678312 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B1717625 : Blo 678312 1717625 := bstep (se 2 (by rfl) ⟨644109, by rfl⟩ : syracuseStep 1717625 = 1288219) B1288219
theorem B4896283 : Blo 678312 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B767515 : Blo 678312 767515 := bstep (se 1 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 767515 = 1151273) B1151273
theorem B5814139 : Blo 678312 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B16529345 : Blo 678312 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B52869131 : Blo 678312 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B62798611 : Blo 678312 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B5815097 : Blo 678312 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B8731871 : Blo 678312 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B7389161 : Blo 678312 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B966649 : Blo 678312 966649 := bstep (se 2 (by rfl) ⟨362493, by rfl⟩ : syracuseStep 966649 = 724987) B724987
theorem B1294841 : Blo 678312 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B13976263 : Blo 678312 13976263 := bstep (se 1 (by rfl) ⟨10482197, by rfl⟩ : syracuseStep 13976263 = 20964395) B20964395
theorem B1295099 : Blo 678312 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B1131943 : Blo 678312 1131943 := bstep (se 1 (by rfl) ⟨848957, by rfl⟩ : syracuseStep 1131943 = 1697915) B1697915
theorem B2181431 : Blo 678312 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B1657151 : Blo 678312 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B67095215 : Blo 678312 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B1526507 : Blo 678312 1526507 := bstep (se 1 (by rfl) ⟨1144880, by rfl⟩ : syracuseStep 1526507 = 2289761) B2289761
theorem B8276779 : Blo 678312 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1723295 : Blo 678312 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B17386649 : Blo 678312 17386649 := bstep (se 2 (by rfl) ⟨6519993, by rfl⟩ : syracuseStep 17386649 = 13039987) B13039987
theorem B4148705 : Blo 678312 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B1527407 : Blo 678312 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B3100289 : Blo 678312 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B1527479 : Blo 678312 1527479 := bstep (se 1 (by rfl) ⟨1145609, by rfl⟩ : syracuseStep 1527479 = 2291219) B2291219
theorem B1527929 : Blo 678312 1527929 := bstep (se 2 (by rfl) ⟨572973, by rfl⟩ : syracuseStep 1527929 = 1145947) B1145947
theorem B2576681 : Blo 678312 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B1528235 : Blo 678312 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B1528775 : Blo 678312 1528775 := bstep (se 1 (by rfl) ⟨1146581, by rfl⟩ : syracuseStep 1528775 = 2293163) B2293163
theorem B1528937 : Blo 678312 1528937 := bstep (se 2 (by rfl) ⟨573351, by rfl⟩ : syracuseStep 1528937 = 1146703) B1146703
theorem B2184353 : Blo 678312 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B1529135 : Blo 678312 1529135 := bstep (se 1 (by rfl) ⟨1146851, by rfl⟩ : syracuseStep 1529135 = 2293703) B2293703
theorem B2578139 : Blo 678312 2578139 := bstep (se 1 (by rfl) ⟨1933604, by rfl⟩ : syracuseStep 2578139 = 3867209) B3867209
theorem B1529567 : Blo 678312 1529567 := bstep (se 1 (by rfl) ⟨1147175, by rfl⟩ : syracuseStep 1529567 = 2294351) B2294351
theorem B4183979 : Blo 678312 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B1726505 : Blo 678312 1726505 := bstep (se 2 (by rfl) ⟨647439, by rfl⟩ : syracuseStep 1726505 = 1294879) B1294879
theorem B1529927 : Blo 678312 1529927 := bstep (se 1 (by rfl) ⟨1147445, by rfl⟩ : syracuseStep 1529927 = 2294891) B2294891
theorem B1726535 : Blo 678312 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B1726859 : Blo 678312 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B678591 : Blo 678312 678591 := bstep (se 1 (by rfl) ⟨508943, by rfl⟩ : syracuseStep 678591 = 1017887) B1017887
theorem B678719 : Blo 678312 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B678759 : Blo 678312 678759 := bstep (se 1 (by rfl) ⟨509069, by rfl⟩ : syracuseStep 678759 = 1018139) B1018139
theorem B47111159 : Blo 678312 47111159 := bstep (se 1 (by rfl) ⟨35333369, by rfl⟩ : syracuseStep 47111159 = 70666739) B70666739
theorem B678975 : Blo 678312 678975 := bstep (se 1 (by rfl) ⟨509231, by rfl⟩ : syracuseStep 678975 = 1018463) B1018463
theorem B679163 : Blo 678312 679163 := bstep (se 1 (by rfl) ⟨509372, by rfl⟩ : syracuseStep 679163 = 1018745) B1018745
theorem B679195 : Blo 678312 679195 := bstep (se 1 (by rfl) ⟨509396, by rfl⟩ : syracuseStep 679195 = 1018793) B1018793
theorem B679295 : Blo 678312 679295 := bstep (se 1 (by rfl) ⟨509471, by rfl⟩ : syracuseStep 679295 = 1018943) B1018943
theorem B6544871 : Blo 678312 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B11656709 : Blo 678312 11656709 := bstep (se 4 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 11656709 = 2185633) B2185633
theorem B9461281 : Blo 678312 9461281 := bstep (se 2 (by rfl) ⟨3547980, by rfl⟩ : syracuseStep 9461281 = 7095961) B7095961
theorem B4906603 : Blo 678312 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B679663 : Blo 678312 679663 := bstep (se 1 (by rfl) ⟨509747, by rfl⟩ : syracuseStep 679663 = 1019495) B1019495
theorem B1859561 : Blo 678312 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B679919 : Blo 678312 679919 := bstep (se 1 (by rfl) ⟨509939, by rfl⟩ : syracuseStep 679919 = 1019879) B1019879
theorem B679999 : Blo 678312 679999 := bstep (se 1 (by rfl) ⟨509999, by rfl⟩ : syracuseStep 679999 = 1019999) B1019999
theorem B680007 : Blo 678312 680007 := bstep (se 1 (by rfl) ⟨510005, by rfl⟩ : syracuseStep 680007 = 1020011) B1020011
theorem B680039 : Blo 678312 680039 := bstep (se 1 (by rfl) ⟨510029, by rfl⟩ : syracuseStep 680039 = 1020059) B1020059
theorem B15687827 : Blo 678312 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B7758017 : Blo 678312 7758017 := bstep (se 2 (by rfl) ⟨2909256, by rfl⟩ : syracuseStep 7758017 = 5818513) B5818513
theorem B5169581 : Blo 678312 5169581 := bstep (se 3 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 5169581 = 1938593) B1938593
theorem B2122247 : Blo 678312 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2581055 : Blo 678312 2581055 := bstep (se 1 (by rfl) ⟨1935791, by rfl⟩ : syracuseStep 2581055 = 3871583) B3871583
theorem B680607 : Blo 678312 680607 := bstep (se 1 (by rfl) ⟨510455, by rfl⟩ : syracuseStep 680607 = 1020911) B1020911
theorem B680863 : Blo 678312 680863 := bstep (se 1 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 680863 = 1021295) B1021295
theorem B680943 : Blo 678312 680943 := bstep (se 1 (by rfl) ⟨510707, by rfl⟩ : syracuseStep 680943 = 1021415) B1021415
theorem B681051 : Blo 678312 681051 := bstep (se 1 (by rfl) ⟨510788, by rfl⟩ : syracuseStep 681051 = 1021577) B1021577
theorem B681063 : Blo 678312 681063 := bstep (se 1 (by rfl) ⟨510797, by rfl⟩ : syracuseStep 681063 = 1021595) B1021595
theorem B681191 : Blo 678312 681191 := bstep (se 1 (by rfl) ⟨510893, by rfl⟩ : syracuseStep 681191 = 1021787) B1021787
theorem B143123705 : Blo 678312 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B3270071 : Blo 678312 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B681447 : Blo 678312 681447 := bstep (se 1 (by rfl) ⟨511085, by rfl⟩ : syracuseStep 681447 = 1022171) B1022171
theorem B681627 : Blo 678312 681627 := bstep (se 1 (by rfl) ⟨511220, by rfl⟩ : syracuseStep 681627 = 1022441) B1022441
theorem B2942647 : Blo 678312 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B8251091 : Blo 678312 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B1533779 : Blo 678312 1533779 := bstep (se 1 (by rfl) ⟨1150334, by rfl⟩ : syracuseStep 1533779 = 2300669) B2300669
theorem B681887 : Blo 678312 681887 := bstep (se 1 (by rfl) ⟨511415, by rfl⟩ : syracuseStep 681887 = 1022831) B1022831
theorem B681895 : Blo 678312 681895 := bstep (se 1 (by rfl) ⟨511421, by rfl⟩ : syracuseStep 681895 = 1022843) B1022843
theorem B3270955 : Blo 678312 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B58812803 : Blo 678312 58812803 := bstep (se 1 (by rfl) ⟨44109602, by rfl⟩ : syracuseStep 58812803 = 88219205) B88219205
theorem B4418023 : Blo 678312 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B2583211 : Blo 678312 2583211 := bstep (se 1 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 2583211 = 3874817) B3874817
theorem B1534841 : Blo 678312 1534841 := bstep (se 2 (by rfl) ⟨575565, by rfl⟩ : syracuseStep 1534841 = 1151131) B1151131
theorem B7760933 : Blo 678312 7760933 := bstep (se 4 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 7760933 = 1455175) B1455175
theorem B3436343 : Blo 678312 3436343 := bstep (se 1 (by rfl) ⟨2577257, by rfl⟩ : syracuseStep 3436343 = 5154515) B5154515
theorem B2289545 : Blo 678312 2289545 := bstep (se 2 (by rfl) ⟨858579, by rfl⟩ : syracuseStep 2289545 = 1717159) B1717159
theorem B4649015 : Blo 678312 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B12579259 : Blo 678312 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B7730315 : Blo 678312 7730315 := bstep (se 1 (by rfl) ⟨5797736, by rfl⟩ : syracuseStep 7730315 = 11595473) B11595473
theorem B16741529 : Blo 678312 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B13104503 : Blo 678312 13104503 := bstep (se 1 (by rfl) ⟨9828377, by rfl⟩ : syracuseStep 13104503 = 19656755) B19656755
theorem B5174927 : Blo 678312 5174927 := bstep (se 1 (by rfl) ⟨3881195, by rfl⟩ : syracuseStep 5174927 = 7762391) B7762391
theorem B2914451 : Blo 678312 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B3865067 : Blo 678312 3865067 := bstep (se 1 (by rfl) ⟨2898800, by rfl⟩ : syracuseStep 3865067 = 5797601) B5797601
theorem B8288851 : Blo 678312 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B5175899 : Blo 678312 5175899 := bstep (se 1 (by rfl) ⟨3881924, by rfl⟩ : syracuseStep 5175899 = 7763849) B7763849
theorem B1145711 : Blo 678312 1145711 := bstep (se 1 (by rfl) ⟨859283, by rfl⟩ : syracuseStep 1145711 = 1718567) B1718567
theorem B4193255 : Blo 678312 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B1932443 : Blo 678312 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B4357583 : Blo 678312 4357583 := bstep (se 1 (by rfl) ⟨3268187, by rfl⟩ : syracuseStep 4357583 = 6536375) B6536375
theorem B818671 : Blo 678312 818671 := bstep (se 1 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 818671 = 1228007) B1228007
theorem B2293595 : Blo 678312 2293595 := bstep (se 1 (by rfl) ⟨1720196, by rfl⟩ : syracuseStep 2293595 = 3440393) B3440393
theorem B1146953 : Blo 678312 1146953 := bstep (se 2 (by rfl) ⟨430107, by rfl⟩ : syracuseStep 1146953 = 860215) B860215
theorem B1048955 : Blo 678312 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B5177843 : Blo 678312 5177843 := bstep (se 1 (by rfl) ⟨3883382, by rfl⟩ : syracuseStep 5177843 = 7766765) B7766765
theorem B3736343 : Blo 678312 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B44730143 : Blo 678312 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1017671 : Blo 678312 1017671 := bstep (se 1 (by rfl) ⟨763253, by rfl⟩ : syracuseStep 1017671 = 1526507) B1526507
theorem B1509257 : Blo 678312 1509257 := bstep (se 2 (by rfl) ⟨565971, by rfl⟩ : syracuseStep 1509257 = 1131943) B1131943
theorem B1148863 : Blo 678312 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B1017833 : Blo 678312 1017833 := bstep (se 2 (by rfl) ⟨381687, by rfl⟩ : syracuseStep 1017833 = 763375) B763375
theorem B1018271 : Blo 678312 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B1018319 : Blo 678312 1018319 := bstep (se 1 (by rfl) ⟨763739, by rfl⟩ : syracuseStep 1018319 = 1527479) B1527479
theorem B1018619 : Blo 678312 1018619 := bstep (se 1 (by rfl) ⟨763964, by rfl⟩ : syracuseStep 1018619 = 1527929) B1527929
theorem B7736147 : Blo 678312 7736147 := bstep (se 1 (by rfl) ⟨5802110, by rfl⟩ : syracuseStep 7736147 = 11604221) B11604221
theorem B1018823 : Blo 678312 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B4361273 : Blo 678312 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B1019183 : Blo 678312 1019183 := bstep (se 1 (by rfl) ⟨764387, by rfl⟩ : syracuseStep 1019183 = 1528775) B1528775
theorem B1019291 : Blo 678312 1019291 := bstep (se 1 (by rfl) ⟨764468, by rfl⟩ : syracuseStep 1019291 = 1528937) B1528937
theorem B1019369 : Blo 678312 1019369 := bstep (se 2 (by rfl) ⟨382263, by rfl⟩ : syracuseStep 1019369 = 764527) B764527
theorem B1019423 : Blo 678312 1019423 := bstep (se 1 (by rfl) ⟨764567, by rfl⟩ : syracuseStep 1019423 = 1529135) B1529135
theorem B3444281 : Blo 678312 3444281 := bstep (se 2 (by rfl) ⟨1291605, by rfl⟩ : syracuseStep 3444281 = 2583211) B2583211
theorem B1019657 : Blo 678312 1019657 := bstep (se 2 (by rfl) ⟨382371, by rfl⟩ : syracuseStep 1019657 = 764743) B764743
theorem B1019711 : Blo 678312 1019711 := bstep (se 1 (by rfl) ⟨764783, by rfl⟩ : syracuseStep 1019711 = 1529567) B1529567
theorem B1151003 : Blo 678312 1151003 := bstep (se 1 (by rfl) ⟨863252, by rfl⟩ : syracuseStep 1151003 = 1726505) B1726505
theorem B1019951 : Blo 678312 1019951 := bstep (se 1 (by rfl) ⟨764963, by rfl⟩ : syracuseStep 1019951 = 1529927) B1529927
theorem B1151023 : Blo 678312 1151023 := bstep (se 1 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 1151023 = 1726535) B1726535
theorem B1151239 : Blo 678312 1151239 := bstep (se 1 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 1151239 = 1726859) B1726859
theorem B1020809 : Blo 678312 1020809 := bstep (se 2 (by rfl) ⟨382803, by rfl⟩ : syracuseStep 1020809 = 765607) B765607
theorem B14914529 : Blo 678312 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B4363247 : Blo 678312 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B7771139 : Blo 678312 7771139 := bstep (se 1 (by rfl) ⟨5828354, by rfl⟩ : syracuseStep 7771139 = 11656709) B11656709
theorem B6526145 : Blo 678312 6526145 := bstep (se 2 (by rfl) ⟨2447304, by rfl⟩ : syracuseStep 6526145 = 4894609) B4894609
theorem B10458551 : Blo 678312 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B5510587 : Blo 678312 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B3446387 : Blo 678312 3446387 := bstep (se 1 (by rfl) ⟨2584790, by rfl⟩ : syracuseStep 3446387 = 5169581) B5169581
theorem B1414831 : Blo 678312 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B2332385 : Blo 678312 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B1022345 : Blo 678312 1022345 := bstep (se 2 (by rfl) ⟨383379, by rfl⟩ : syracuseStep 1022345 = 766759) B766759
theorem B1022519 : Blo 678312 1022519 := bstep (se 1 (by rfl) ⟨766889, by rfl⟩ : syracuseStep 1022519 = 1533779) B1533779
theorem B858919 : Blo 678312 858919 := bstep (se 1 (by rfl) ⟨644189, by rfl⟩ : syracuseStep 858919 = 1288379) B1288379
theorem B1023227 : Blo 678312 1023227 := bstep (se 1 (by rfl) ⟨767420, by rfl⟩ : syracuseStep 1023227 = 1534841) B1534841
theorem B6528377 : Blo 678312 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B1023353 : Blo 678312 1023353 := bstep (se 2 (by rfl) ⟨383757, by rfl⟩ : syracuseStep 1023353 = 767515) B767515
theorem B11182013 : Blo 678312 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B4661387 : Blo 678312 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B2302127 : Blo 678312 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B3874999 : Blo 678312 3874999 := bstep (se 1 (by rfl) ⟨2906249, by rfl⟩ : syracuseStep 3874999 = 5812499) B5812499
theorem B5153543 : Blo 678312 5153543 := bstep (se 1 (by rfl) ⟨3865157, by rfl⟩ : syracuseStep 5153543 = 7730315) B7730315
theorem B11051801 : Blo 678312 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B5514095 : Blo 678312 5514095 := bstep (se 1 (by rfl) ⟨4135571, by rfl⟩ : syracuseStep 5514095 = 8271143) B8271143
theorem B83731481 : Blo 678312 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B3449951 : Blo 678312 3449951 := bstep (se 1 (by rfl) ⟨2587463, by rfl⟩ : syracuseStep 3449951 = 5174927) B5174927
theorem B11019563 : Blo 678312 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B2762041 : Blo 678312 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B1942967 : Blo 678312 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B8267437 : Blo 678312 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3450599 : Blo 678312 3450599 := bstep (se 1 (by rfl) ⟨2587949, by rfl⟩ : syracuseStep 3450599 = 5175899) B5175899
theorem B3876731 : Blo 678312 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B763807 : Blo 678312 763807 := bstep (se 1 (by rfl) ⟨572855, by rfl⟩ : syracuseStep 763807 = 1145711) B1145711
theorem B1091561 : Blo 678312 1091561 := bstep (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) B818671
theorem B1288295 : Blo 678312 1288295 := bstep (se 1 (by rfl) ⟨966221, by rfl⟩ : syracuseStep 1288295 = 1932443) B1932443
theorem B4926107 : Blo 678312 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B1288865 : Blo 678312 1288865 := bstep (se 2 (by rfl) ⟨483324, by rfl⟩ : syracuseStep 1288865 = 966649) B966649
theorem B764671 : Blo 678312 764671 := bstep (se 1 (by rfl) ⟨573503, by rfl⟩ : syracuseStep 764671 = 1147007) B1147007
theorem B12397373 : Blo 678312 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B863227 : Blo 678312 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B863399 : Blo 678312 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B765895 : Blo 678312 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B4042855 : Blo 678312 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1454287 : Blo 678312 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B766255 : Blo 678312 766255 := bstep (se 1 (by rfl) ⟨574691, by rfl⟩ : syracuseStep 766255 = 1149383) B1149383
theorem B1717787 : Blo 678312 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B1292267 : Blo 678312 1292267 := bstep (se 1 (by rfl) ⟨969200, by rfl⟩ : syracuseStep 1292267 = 1938401) B1938401
theorem B1456235 : Blo 678312 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B9812285 : Blo 678312 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B1718759 : Blo 678312 1718759 := bstep (se 1 (by rfl) ⟨1289069, by rfl⟩ : syracuseStep 1718759 = 2578139) B2578139
theorem B31407439 : Blo 678312 31407439 := bstep (se 1 (by rfl) ⟨23555579, by rfl⟩ : syracuseStep 31407439 = 47111159) B47111159
theorem B1720703 : Blo 678312 1720703 := bstep (se 1 (by rfl) ⟨1290527, by rfl⟩ : syracuseStep 1720703 = 2581055) B2581055
theorem B2180047 : Blo 678312 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B1295327 : Blo 678312 1295327 := bstep (se 1 (by rfl) ⟨971495, by rfl⟩ : syracuseStep 1295327 = 1942991) B1942991
theorem B39208535 : Blo 678312 39208535 := bstep (se 1 (by rfl) ⟨29406401, by rfl⟩ : syracuseStep 39208535 = 58812803) B58812803
theorem B31475425 : Blo 678312 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B5818787 : Blo 678312 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B5229035 : Blo 678312 5229035 := bstep (se 1 (by rfl) ⟨3921776, by rfl⟩ : syracuseStep 5229035 = 7843553) B7843553
theorem B7752185 : Blo 678312 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B1526363 : Blo 678312 1526363 := bstep (se 1 (by rfl) ⟨1144772, by rfl⟩ : syracuseStep 1526363 = 2289545) B2289545
theorem B4901735 : Blo 678312 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B4902221 : Blo 678312 4902221 := bstep (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) B1838333
theorem B11161019 : Blo 678312 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B10472975 : Blo 678312 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B8736335 : Blo 678312 8736335 := bstep (se 1 (by rfl) ⟨6552251, by rfl⟩ : syracuseStep 8736335 = 13104503) B13104503
theorem B11063213 : Blo 678312 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B35246087 : Blo 678312 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B2576711 : Blo 678312 2576711 := bstep (se 1 (by rfl) ⟨1932533, by rfl⟩ : syracuseStep 2576711 = 3865067) B3865067
theorem B6542137 : Blo 678312 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B5821247 : Blo 678312 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B2905055 : Blo 678312 2905055 := bstep (se 1 (by rfl) ⟨2178791, by rfl⟩ : syracuseStep 2905055 = 4357583) B4357583
theorem B1529063 : Blo 678312 1529063 := bstep (se 1 (by rfl) ⟨1146797, by rfl⟩ : syracuseStep 1529063 = 2293595) B2293595
theorem B1529639 : Blo 678312 1529639 := bstep (se 1 (by rfl) ⟨1147229, by rfl⟩ : syracuseStep 1529639 = 2294459) B2294459
theorem B2578655 : Blo 678312 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B18635017 : Blo 678312 18635017 := bstep (se 2 (by rfl) ⟨6988131, by rfl⟩ : syracuseStep 18635017 = 13976263) B13976263
theorem B678503 : Blo 678312 678503 := bstep (se 1 (by rfl) ⟨508877, by rfl⟩ : syracuseStep 678503 = 1017755) B1017755
theorem B678527 : Blo 678312 678527 := bstep (se 1 (by rfl) ⟨508895, by rfl⟩ : syracuseStep 678527 = 1017791) B1017791
theorem B1530593 : Blo 678312 1530593 := bstep (se 2 (by rfl) ⟨573972, by rfl⟩ : syracuseStep 1530593 = 1147945) B1147945
theorem B1104767 : Blo 678312 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B678943 : Blo 678312 678943 := bstep (se 1 (by rfl) ⟨509207, by rfl⟩ : syracuseStep 678943 = 1018415) B1018415
theorem B1530971 : Blo 678312 1530971 := bstep (se 1 (by rfl) ⟨1148228, by rfl⟩ : syracuseStep 1530971 = 2296457) B2296457
theorem B679023 : Blo 678312 679023 := bstep (se 1 (by rfl) ⟨509267, by rfl⟩ : syracuseStep 679023 = 1018535) B1018535
theorem B679067 : Blo 678312 679067 := bstep (se 1 (by rfl) ⟨509300, by rfl⟩ : syracuseStep 679067 = 1018601) B1018601
theorem B679071 : Blo 678312 679071 := bstep (se 1 (by rfl) ⟨509303, by rfl⟩ : syracuseStep 679071 = 1018607) B1018607
theorem B679103 : Blo 678312 679103 := bstep (se 1 (by rfl) ⟨509327, by rfl⟩ : syracuseStep 679103 = 1018655) B1018655
theorem B679323 : Blo 678312 679323 := bstep (se 1 (by rfl) ⟨509492, by rfl⟩ : syracuseStep 679323 = 1018985) B1018985
theorem B11591099 : Blo 678312 11591099 := bstep (se 1 (by rfl) ⟨8693324, by rfl⟩ : syracuseStep 11591099 = 17386649) B17386649
theorem B679407 : Blo 678312 679407 := bstep (se 1 (by rfl) ⟨509555, by rfl⟩ : syracuseStep 679407 = 1019111) B1019111
theorem B679743 : Blo 678312 679743 := bstep (se 1 (by rfl) ⟨509807, by rfl⟩ : syracuseStep 679743 = 1019615) B1019615
theorem B679931 : Blo 678312 679931 := bstep (se 1 (by rfl) ⟨509948, by rfl⟩ : syracuseStep 679931 = 1019897) B1019897
theorem B680063 : Blo 678312 680063 := bstep (se 1 (by rfl) ⟨510047, by rfl⟩ : syracuseStep 680063 = 1020095) B1020095
theorem B680091 : Blo 678312 680091 := bstep (se 1 (by rfl) ⟨510068, by rfl⟩ : syracuseStep 680091 = 1020137) B1020137
theorem B680175 : Blo 678312 680175 := bstep (se 1 (by rfl) ⟨510131, by rfl⟩ : syracuseStep 680175 = 1020263) B1020263
theorem B5890697 : Blo 678312 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B680731 : Blo 678312 680731 := bstep (se 1 (by rfl) ⟨510548, by rfl⟩ : syracuseStep 680731 = 1021097) B1021097
theorem B1532699 : Blo 678312 1532699 := bstep (se 1 (by rfl) ⟨1149524, by rfl⟩ : syracuseStep 1532699 = 2299049) B2299049
theorem B680775 : Blo 678312 680775 := bstep (se 1 (by rfl) ⟨510581, by rfl⟩ : syracuseStep 680775 = 1021163) B1021163
theorem B680831 : Blo 678312 680831 := bstep (se 1 (by rfl) ⟨510623, by rfl⟩ : syracuseStep 680831 = 1021247) B1021247
theorem B1532897 : Blo 678312 1532897 := bstep (se 2 (by rfl) ⟨574836, by rfl⟩ : syracuseStep 1532897 = 1149673) B1149673
theorem B680959 : Blo 678312 680959 := bstep (se 1 (by rfl) ⟨510719, by rfl⟩ : syracuseStep 680959 = 1021439) B1021439
theorem B1532969 : Blo 678312 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B11035705 : Blo 678312 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B681031 : Blo 678312 681031 := bstep (se 1 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 681031 = 1021547) B1021547
theorem B2581739 : Blo 678312 2581739 := bstep (se 1 (by rfl) ⟨1936304, by rfl⟩ : syracuseStep 2581739 = 3872609) B3872609
theorem B681211 : Blo 678312 681211 := bstep (se 1 (by rfl) ⟨510908, by rfl⟩ : syracuseStep 681211 = 1021817) B1021817
theorem B681375 : Blo 678312 681375 := bstep (se 1 (by rfl) ⟨511031, by rfl⟩ : syracuseStep 681375 = 1022063) B1022063
theorem B681423 : Blo 678312 681423 := bstep (se 1 (by rfl) ⟨511067, by rfl⟩ : syracuseStep 681423 = 1022135) B1022135
theorem B1533671 : Blo 678312 1533671 := bstep (se 1 (by rfl) ⟨1150253, by rfl⟩ : syracuseStep 1533671 = 2300507) B2300507
theorem B681703 : Blo 678312 681703 := bstep (se 1 (by rfl) ⟨511277, by rfl⟩ : syracuseStep 681703 = 1022555) B1022555
theorem B681711 : Blo 678312 681711 := bstep (se 1 (by rfl) ⟨511283, by rfl⟩ : syracuseStep 681711 = 1022567) B1022567
theorem B681727 : Blo 678312 681727 := bstep (se 1 (by rfl) ⟨511295, by rfl⟩ : syracuseStep 681727 = 1022591) B1022591
theorem B681799 : Blo 678312 681799 := bstep (se 1 (by rfl) ⟨511349, by rfl⟩ : syracuseStep 681799 = 1022699) B1022699
theorem B681819 : Blo 678312 681819 := bstep (se 1 (by rfl) ⟨511364, by rfl⟩ : syracuseStep 681819 = 1022729) B1022729
theorem B681979 : Blo 678312 681979 := bstep (se 1 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 681979 = 1022969) B1022969
theorem B1534607 : Blo 678312 1534607 := bstep (se 1 (by rfl) ⟨1150955, by rfl⟩ : syracuseStep 1534607 = 2301911) B2301911
theorem B1239707 : Blo 678312 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B5172011 : Blo 678312 5172011 := bstep (se 1 (by rfl) ⟨3879008, by rfl⟩ : syracuseStep 5172011 = 7758017) B7758017
theorem B1535003 : Blo 678312 1535003 := bstep (se 1 (by rfl) ⟨1151252, by rfl⟩ : syracuseStep 1535003 = 2302505) B2302505
theorem B16772345 : Blo 678312 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B95415803 : Blo 678312 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B5500727 : Blo 678312 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B2322539 : Blo 678312 2322539 := bstep (se 1 (by rfl) ⟨1741904, by rfl⟩ : syracuseStep 2322539 = 3483809) B3483809
theorem B5173955 : Blo 678312 5173955 := bstep (se 1 (by rfl) ⟨3880466, by rfl⟩ : syracuseStep 5173955 = 7760933) B7760933
theorem B2585641 : Blo 678312 2585641 := bstep (se 2 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 2585641 = 1939231) B1939231
theorem B9794753 : Blo 678312 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B2290895 : Blo 678312 2290895 := bstep (se 1 (by rfl) ⟨1718171, by rfl⟩ : syracuseStep 2290895 = 3436343) B3436343
theorem B2586599 : Blo 678312 2586599 := bstep (se 1 (by rfl) ⟨1939949, by rfl⟩ : syracuseStep 2586599 = 3879899) B3879899
theorem B1145083 : Blo 678312 1145083 := bstep (se 1 (by rfl) ⟨858812, by rfl⟩ : syracuseStep 1145083 = 1717625) B1717625
theorem B15694117 : Blo 678312 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B44629109 : Blo 678312 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B12615041 : Blo 678312 12615041 := bstep (se 2 (by rfl) ⟨4730640, by rfl⟩ : syracuseStep 12615041 = 9461281) B9461281
theorem B1147135 : Blo 678312 1147135 := bstep (se 1 (by rfl) ⟨860351, by rfl⟩ : syracuseStep 1147135 = 1720703) B1720703
theorem B2490895 : Blo 678312 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B29820095 : Blo 678312 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B14714273 : Blo 678312 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1017575 : Blo 678312 1017575 := bstep (se 1 (by rfl) ⟨763181, by rfl⟩ : syracuseStep 1017575 = 1526363) B1526363
theorem B7440679 : Blo 678312 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B6981983 : Blo 678312 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B2296187 : Blo 678312 2296187 := bstep (se 1 (by rfl) ⟨1722140, by rfl⟩ : syracuseStep 2296187 = 3444281) B3444281
theorem B1018409 : Blo 678312 1018409 := bstep (se 2 (by rfl) ⟨381903, by rfl⟩ : syracuseStep 1018409 = 763807) B763807
theorem B7375475 : Blo 678312 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B23497391 : Blo 678312 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B1936703 : Blo 678312 1936703 := bstep (se 1 (by rfl) ⟨1452527, by rfl⟩ : syracuseStep 1936703 = 2905055) B2905055
theorem B5180759 : Blo 678312 5180759 := bstep (se 1 (by rfl) ⟨3885569, by rfl⟩ : syracuseStep 5180759 = 7771139) B7771139
theorem B1019375 : Blo 678312 1019375 := bstep (se 1 (by rfl) ⟨764531, by rfl⟩ : syracuseStep 1019375 = 1529063) B1529063
theorem B1019561 : Blo 678312 1019561 := bstep (se 2 (by rfl) ⟨382335, by rfl⟩ : syracuseStep 1019561 = 764671) B764671
theorem B2297591 : Blo 678312 2297591 := bstep (se 1 (by rfl) ⟨1723193, by rfl⟩ : syracuseStep 2297591 = 3446387) B3446387
theorem B5181245 : Blo 678312 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B1019759 : Blo 678312 1019759 := bstep (se 1 (by rfl) ⟨764819, by rfl⟩ : syracuseStep 1019759 = 1529639) B1529639
theorem B1150969 : Blo 678312 1150969 := bstep (se 2 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 1150969 = 863227) B863227
theorem B1020395 : Blo 678312 1020395 := bstep (se 1 (by rfl) ⟨765296, by rfl⟩ : syracuseStep 1020395 = 1530593) B1530593
theorem B1020647 : Blo 678312 1020647 := bstep (se 1 (by rfl) ⟨765485, by rfl⟩ : syracuseStep 1020647 = 1530971) B1530971
theorem B1021193 : Blo 678312 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B1939049 : Blo 678312 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B1021673 : Blo 678312 1021673 := bstep (se 2 (by rfl) ⟨383127, by rfl⟩ : syracuseStep 1021673 = 766255) B766255
theorem B1021799 : Blo 678312 1021799 := bstep (se 1 (by rfl) ⟨766349, by rfl⟩ : syracuseStep 1021799 = 1532699) B1532699
theorem B3676063 : Blo 678312 3676063 := bstep (se 1 (by rfl) ⟨2757047, by rfl⟩ : syracuseStep 3676063 = 5514095) B5514095
theorem B1021931 : Blo 678312 1021931 := bstep (se 1 (by rfl) ⟨766448, by rfl⟩ : syracuseStep 1021931 = 1532897) B1532897
theorem B1021979 : Blo 678312 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B2299967 : Blo 678312 2299967 := bstep (se 1 (by rfl) ⟨1724975, by rfl⟩ : syracuseStep 2299967 = 3449951) B3449951
theorem B7346375 : Blo 678312 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B8722849 : Blo 678312 8722849 := bstep (se 2 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 8722849 = 6542137) B6542137
theorem B2300399 : Blo 678312 2300399 := bstep (se 1 (by rfl) ⟨1725299, by rfl⟩ : syracuseStep 2300399 = 3450599) B3450599
theorem B1022447 : Blo 678312 1022447 := bstep (se 1 (by rfl) ⟨766835, by rfl⟩ : syracuseStep 1022447 = 1533671) B1533671
theorem B3447521 : Blo 678312 3447521 := bstep (se 2 (by rfl) ⟨1292820, by rfl⟩ : syracuseStep 3447521 = 2585641) B2585641
theorem B858863 : Blo 678312 858863 := bstep (se 1 (by rfl) ⟨644147, by rfl⟩ : syracuseStep 858863 = 1288295) B1288295
theorem B1023071 : Blo 678312 1023071 := bstep (se 1 (by rfl) ⟨767303, by rfl⟩ : syracuseStep 1023071 = 1534607) B1534607
theorem B826471 : Blo 678312 826471 := bstep (se 1 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 826471 = 1239707) B1239707
theorem B3284071 : Blo 678312 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B859243 : Blo 678312 859243 := bstep (se 1 (by rfl) ⟨644432, by rfl⟩ : syracuseStep 859243 = 1288865) B1288865
theorem B3448007 : Blo 678312 3448007 := bstep (se 1 (by rfl) ⟨2586005, by rfl⟩ : syracuseStep 3448007 = 5172011) B5172011
theorem B8264915 : Blo 678312 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B7347449 : Blo 678312 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B1023335 : Blo 678312 1023335 := bstep (se 1 (by rfl) ⟨767501, by rfl⟩ : syracuseStep 1023335 = 1535003) B1535003
theorem B11181563 : Blo 678312 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B63610535 : Blo 678312 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1548359 : Blo 678312 1548359 := bstep (se 1 (by rfl) ⟨1161269, by rfl⟩ : syracuseStep 1548359 = 2322539) B2322539
theorem B24846689 : Blo 678312 24846689 := bstep (se 2 (by rfl) ⟨9317508, by rfl⟩ : syracuseStep 24846689 = 18635017) B18635017
theorem B2302397 : Blo 678312 2302397 := bstep (se 3 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 2302397 = 863399) B863399
theorem B3449303 : Blo 678312 3449303 := bstep (se 1 (by rfl) ⟨2586977, by rfl⟩ : syracuseStep 3449303 = 5173955) B5173955
theorem B6529835 : Blo 678312 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B861511 : Blo 678312 861511 := bstep (se 1 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 861511 = 1292267) B1292267
theorem B764635 : Blo 678312 764635 := bstep (se 1 (by rfl) ⟨573476, by rfl⟩ : syracuseStep 764635 = 1146953) B1146953
theorem B3451895 : Blo 678312 3451895 := bstep (se 1 (by rfl) ⟨2588921, by rfl⟩ : syracuseStep 3451895 = 5177843) B5177843
theorem B863551 : Blo 678312 863551 := bstep (se 1 (by rfl) ⟨647663, by rfl⟩ : syracuseStep 863551 = 1295327) B1295327
theorem B83701957 : Blo 678312 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B3879191 : Blo 678312 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B3486023 : Blo 678312 3486023 := bstep (se 1 (by rfl) ⟨2614517, by rfl⟩ : syracuseStep 3486023 = 5229035) B5229035
theorem B3682721 : Blo 678312 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B5157431 : Blo 678312 5157431 := bstep (se 1 (by rfl) ⟨3868073, by rfl⟩ : syracuseStep 5157431 = 7736147) B7736147
theorem B767335 : Blo 678312 767335 := bstep (se 1 (by rfl) ⟨575501, by rfl⟩ : syracuseStep 767335 = 1151003) B1151003
theorem B1717807 : Blo 678312 1717807 := bstep (se 1 (by rfl) ⟨1288355, by rfl⟩ : syracuseStep 1717807 = 2576711) B2576711
theorem B3880831 : Blo 678312 3880831 := bstep (se 1 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 3880831 = 5821247) B5821247
theorem B9943019 : Blo 678312 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B1554923 : Blo 678312 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B11188853 : Blo 678312 11188853 := bstep (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) B1048955
theorem B1719103 : Blo 678312 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B736511 : Blo 678312 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B7454675 : Blo 678312 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B5390473 : Blo 678312 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B55820987 : Blo 678312 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B1721159 : Blo 678312 1721159 := bstep (se 1 (by rfl) ⟨1290869, by rfl⟩ : syracuseStep 1721159 = 2581739) B2581739
theorem B1886441 : Blo 678312 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B1526777 : Blo 678312 1526777 := bstep (se 2 (by rfl) ⟨572541, by rfl⟩ : syracuseStep 1526777 = 1145083) B1145083
theorem B1527263 : Blo 678312 1527263 := bstep (se 1 (by rfl) ⟨1145447, by rfl⟩ : syracuseStep 1527263 = 2290895) B2290895
theorem B44092997 : Blo 678312 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B33640109 : Blo 678312 33640109 := bstep (se 3 (by rfl) ⟨6307520, by rfl⟩ : syracuseStep 33640109 = 12615041) B12615041
theorem B1724399 : Blo 678312 1724399 := bstep (se 1 (by rfl) ⟨1293299, by rfl⟩ : syracuseStep 1724399 = 2586599) B2586599
theorem B970823 : Blo 678312 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B6541523 : Blo 678312 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B5166665 : Blo 678312 5166665 := bstep (se 2 (by rfl) ⟨1937499, by rfl⟩ : syracuseStep 5166665 = 3874999) B3874999
theorem B26139023 : Blo 678312 26139023 := bstep (se 1 (by rfl) ⟨19604267, by rfl⟩ : syracuseStep 26139023 = 39208535) B39208535
theorem B678447 : Blo 678312 678447 := bstep (se 1 (by rfl) ⟨508835, by rfl⟩ : syracuseStep 678447 = 1017671) B1017671
theorem B1006171 : Blo 678312 1006171 := bstep (se 1 (by rfl) ⟨754628, by rfl⟩ : syracuseStep 1006171 = 1509257) B1509257
theorem B2906729 : Blo 678312 2906729 := bstep (se 2 (by rfl) ⟨1090023, by rfl⟩ : syracuseStep 2906729 = 2180047) B2180047
theorem B678555 : Blo 678312 678555 := bstep (se 1 (by rfl) ⟨508916, by rfl⟩ : syracuseStep 678555 = 1017833) B1017833
theorem B678847 : Blo 678312 678847 := bstep (se 1 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 678847 = 1018271) B1018271
theorem B678879 : Blo 678312 678879 := bstep (se 1 (by rfl) ⟨509159, by rfl⟩ : syracuseStep 678879 = 1018319) B1018319
theorem B5168123 : Blo 678312 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B679079 : Blo 678312 679079 := bstep (se 1 (by rfl) ⟨509309, by rfl⟩ : syracuseStep 679079 = 1018619) B1018619
theorem B3267823 : Blo 678312 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B679215 : Blo 678312 679215 := bstep (se 1 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 679215 = 1018823) B1018823
theorem B2907515 : Blo 678312 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B679455 : Blo 678312 679455 := bstep (se 1 (by rfl) ⟨509591, by rfl⟩ : syracuseStep 679455 = 1019183) B1019183
theorem B679527 : Blo 678312 679527 := bstep (se 1 (by rfl) ⟨509645, by rfl⟩ : syracuseStep 679527 = 1019291) B1019291
theorem B41967233 : Blo 678312 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B679579 : Blo 678312 679579 := bstep (se 1 (by rfl) ⟨509684, by rfl⟩ : syracuseStep 679579 = 1019369) B1019369
theorem B679615 : Blo 678312 679615 := bstep (se 1 (by rfl) ⟨509711, by rfl⟩ : syracuseStep 679615 = 1019423) B1019423
theorem B5824223 : Blo 678312 5824223 := bstep (se 1 (by rfl) ⟨4368167, by rfl⟩ : syracuseStep 5824223 = 8736335) B8736335
theorem B679771 : Blo 678312 679771 := bstep (se 1 (by rfl) ⟨509828, by rfl⟩ : syracuseStep 679771 = 1019657) B1019657
theorem B679807 : Blo 678312 679807 := bstep (se 1 (by rfl) ⟨509855, by rfl⟩ : syracuseStep 679807 = 1019711) B1019711
theorem B1531817 : Blo 678312 1531817 := bstep (se 2 (by rfl) ⟨574431, by rfl⟩ : syracuseStep 1531817 = 1148863) B1148863
theorem B679967 : Blo 678312 679967 := bstep (se 1 (by rfl) ⟨509975, by rfl⟩ : syracuseStep 679967 = 1019951) B1019951
theorem B680539 : Blo 678312 680539 := bstep (se 1 (by rfl) ⟨510404, by rfl⟩ : syracuseStep 680539 = 1020809) B1020809
theorem B2908831 : Blo 678312 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B4350763 : Blo 678312 4350763 := bstep (se 1 (by rfl) ⟨3263072, by rfl⟩ : syracuseStep 4350763 = 6526145) B6526145
theorem B6972367 : Blo 678312 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B681563 : Blo 678312 681563 := bstep (se 1 (by rfl) ⟨511172, by rfl⟩ : syracuseStep 681563 = 1022345) B1022345
theorem B681679 : Blo 678312 681679 := bstep (se 1 (by rfl) ⟨511259, by rfl⟩ : syracuseStep 681679 = 1022519) B1022519
theorem B682151 : Blo 678312 682151 := bstep (se 1 (by rfl) ⟨511613, by rfl⟩ : syracuseStep 682151 = 1023227) B1023227
theorem B4352251 : Blo 678312 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B682235 : Blo 678312 682235 := bstep (se 1 (by rfl) ⟨511676, by rfl⟩ : syracuseStep 682235 = 1023353) B1023353
theorem B7727399 : Blo 678312 7727399 := bstep (se 1 (by rfl) ⟨5795549, by rfl⟩ : syracuseStep 7727399 = 11591099) B11591099
theorem B2910829 : Blo 678312 2910829 := bstep (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) B1091561
theorem B1534697 : Blo 678312 1534697 := bstep (se 2 (by rfl) ⟨575511, by rfl⟩ : syracuseStep 1534697 = 1151023) B1151023
theorem B3107591 : Blo 678312 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B1534751 : Blo 678312 1534751 := bstep (se 1 (by rfl) ⟨1151063, by rfl⟩ : syracuseStep 1534751 = 2302127) B2302127
theorem B1534985 : Blo 678312 1534985 := bstep (se 2 (by rfl) ⟨575619, by rfl⟩ : syracuseStep 1534985 = 1151239) B1151239
theorem B3927131 : Blo 678312 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B3435695 : Blo 678312 3435695 := bstep (se 1 (by rfl) ⟨2576771, by rfl⟩ : syracuseStep 3435695 = 5153543) B5153543
theorem B7367867 : Blo 678312 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B2584487 : Blo 678312 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B3667151 : Blo 678312 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B13072589 : Blo 678312 13072589 := bstep (se 3 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 13072589 = 4902221) B4902221
theorem B1145191 : Blo 678312 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B1145225 : Blo 678312 1145225 := bstep (se 2 (by rfl) ⟨429459, by rfl⟩ : syracuseStep 1145225 = 858919) B858919
theorem B1145839 : Blo 678312 1145839 := bstep (se 1 (by rfl) ⟨859379, by rfl⟩ : syracuseStep 1145839 = 1718759) B1718759
theorem B41876585 : Blo 678312 41876585 := bstep (se 2 (by rfl) ⟨15703719, by rfl⟩ : syracuseStep 41876585 = 31407439) B31407439
theorem B29752739 : Blo 678312 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B2588861 : Blo 678312 2588861 := bstep (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) B970823
theorem B1147439 : Blo 678312 1147439 := bstep (se 1 (by rfl) ⟨860579, by rfl⟩ : syracuseStep 1147439 = 1721159) B1721159
theorem B5801017 : Blo 678312 5801017 := bstep (se 2 (by rfl) ⟨2175381, by rfl⟩ : syracuseStep 5801017 = 4350763) B4350763
theorem B39683621 : Blo 678312 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B4654655 : Blo 678312 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B1148681 : Blo 678312 1148681 := bstep (se 2 (by rfl) ⟨430755, by rfl⟩ : syracuseStep 1148681 = 861511) B861511
theorem B15664927 : Blo 678312 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B1017851 : Blo 678312 1017851 := bstep (se 1 (by rfl) ⟨763388, by rfl⟩ : syracuseStep 1017851 = 1526777) B1526777
theorem B1018175 : Blo 678312 1018175 := bstep (se 1 (by rfl) ⟨763631, by rfl⟩ : syracuseStep 1018175 = 1527263) B1527263
theorem B29395331 : Blo 678312 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B20122037 : Blo 678312 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B1149599 : Blo 678312 1149599 := bstep (se 1 (by rfl) ⟨862199, by rfl⟩ : syracuseStep 1149599 = 1724399) B1724399
theorem B4361015 : Blo 678312 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B5803001 : Blo 678312 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B1019513 : Blo 678312 1019513 := bstep (se 2 (by rfl) ⟨382317, by rfl⟩ : syracuseStep 1019513 = 764635) B764635
theorem B3444443 : Blo 678312 3444443 := bstep (se 1 (by rfl) ⟨2583332, by rfl⟩ : syracuseStep 3444443 = 5166665) B5166665
theorem B1937819 : Blo 678312 1937819 := bstep (se 1 (by rfl) ⟨1453364, by rfl⟩ : syracuseStep 1937819 = 2906729) B2906729
theorem B1151401 : Blo 678312 1151401 := bstep (se 2 (by rfl) ⟨431775, by rfl⟩ : syracuseStep 1151401 = 863551) B863551
theorem B2298347 : Blo 678312 2298347 := bstep (se 1 (by rfl) ⟨1723760, by rfl⟩ : syracuseStep 2298347 = 3447521) B3447521
theorem B3445415 : Blo 678312 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B2298671 : Blo 678312 2298671 := bstep (se 1 (by rfl) ⟨1724003, by rfl⟩ : syracuseStep 2298671 = 3448007) B3448007
theorem B5509943 : Blo 678312 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B1938343 : Blo 678312 1938343 := bstep (se 1 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 1938343 = 2907515) B2907515
theorem B42407023 : Blo 678312 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B1021211 : Blo 678312 1021211 := bstep (se 1 (by rfl) ⟨765908, by rfl⟩ : syracuseStep 1021211 = 1531817) B1531817
theorem B2299535 : Blo 678312 2299535 := bstep (se 1 (by rfl) ⟨1724651, by rfl⟩ : syracuseStep 2299535 = 3449303) B3449303
theorem B5151599 : Blo 678312 5151599 := bstep (se 1 (by rfl) ⟨3863699, by rfl⟩ : syracuseStep 5151599 = 7727399) B7727399
theorem B19667933 : Blo 678312 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B1023113 : Blo 678312 1023113 := bstep (se 2 (by rfl) ⟨383667, by rfl⟩ : syracuseStep 1023113 = 767335) B767335
theorem B1023131 : Blo 678312 1023131 := bstep (se 1 (by rfl) ⟨767348, by rfl⟩ : syracuseStep 1023131 = 1534697) B1534697
theorem B2071727 : Blo 678312 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B1023167 : Blo 678312 1023167 := bstep (se 1 (by rfl) ⟨767375, by rfl⟩ : syracuseStep 1023167 = 1534751) B1534751
theorem B2301263 : Blo 678312 2301263 := bstep (se 1 (by rfl) ⟨1725947, by rfl⟩ : syracuseStep 2301263 = 3451895) B3451895
theorem B1023323 : Blo 678312 1023323 := bstep (se 1 (by rfl) ⟨767492, by rfl⟩ : syracuseStep 1023323 = 1534985) B1534985
theorem B6628679 : Blo 678312 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B763483 : Blo 678312 763483 := bstep (se 1 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 763483 = 1145225) B1145225
theorem B19835159 : Blo 678312 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B7187297 : Blo 678312 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B3878441 : Blo 678312 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B9809515 : Blo 678312 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B17412893 : Blo 678312 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B1291135 : Blo 678312 1291135 := bstep (se 1 (by rfl) ⟨968351, by rfl⟩ : syracuseStep 1291135 = 1936703) B1936703
theorem B3453839 : Blo 678312 3453839 := bstep (se 1 (by rfl) ⟨2590379, by rfl⟩ : syracuseStep 3453839 = 5180759) B5180759
theorem B22426739 : Blo 678312 22426739 := bstep (se 1 (by rfl) ⟨16820054, by rfl⟩ : syracuseStep 22426739 = 33640109) B33640109
theorem B3454163 : Blo 678312 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B13284773 : Blo 678312 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B9779069 : Blo 678312 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B3881105 : Blo 678312 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B1292699 : Blo 678312 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B4897583 : Blo 678312 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B7454375 : Blo 678312 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B3882815 : Blo 678312 3882815 := bstep (se 1 (by rfl) ⟨2912111, by rfl⟩ : syracuseStep 3882815 = 5824223) B5824223
theorem B1032239 : Blo 678312 1032239 := bstep (se 1 (by rfl) ⟨774179, by rfl⟩ : syracuseStep 1032239 = 1548359) B1548359
theorem B16564459 : Blo 678312 16564459 := bstep (se 1 (by rfl) ⟨12423344, by rfl⟩ : syracuseStep 16564459 = 24846689) B24846689
theorem B17515045 : Blo 678312 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B4146461 : Blo 678312 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B4901417 : Blo 678312 4901417 := bstep (se 2 (by rfl) ⟨1838031, by rfl⟩ : syracuseStep 4901417 = 3676063) B3676063
theorem B1722991 : Blo 678312 1722991 := bstep (se 1 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 1722991 = 2584487) B2584487
theorem B1526921 : Blo 678312 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B1527785 : Blo 678312 1527785 := bstep (se 2 (by rfl) ⟨572919, by rfl⟩ : syracuseStep 1527785 = 1145839) B1145839
theorem B1101961 : Blo 678312 1101961 := bstep (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) B826471
theorem B7459235 : Blo 678312 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4969783 : Blo 678312 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B1529513 : Blo 678312 1529513 := bstep (se 2 (by rfl) ⟨573567, by rfl⟩ : syracuseStep 1529513 = 1147135) B1147135
theorem B37213991 : Blo 678312 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B19880063 : Blo 678312 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B678383 : Blo 678312 678383 := bstep (se 1 (by rfl) ⟨508787, by rfl⟩ : syracuseStep 678383 = 1017575) B1017575
theorem B9296489 : Blo 678312 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B1530791 : Blo 678312 1530791 := bstep (se 1 (by rfl) ⟨1148093, by rfl⟩ : syracuseStep 1530791 = 2296187) B2296187
theorem B678939 : Blo 678312 678939 := bstep (se 1 (by rfl) ⟨509204, by rfl⟩ : syracuseStep 678939 = 1018409) B1018409
theorem B679583 : Blo 678312 679583 := bstep (se 1 (by rfl) ⟨509687, by rfl⟩ : syracuseStep 679583 = 1019375) B1019375
theorem B679707 : Blo 678312 679707 := bstep (se 1 (by rfl) ⟨509780, by rfl⟩ : syracuseStep 679707 = 1019561) B1019561
theorem B1531727 : Blo 678312 1531727 := bstep (se 1 (by rfl) ⟨1148795, by rfl⟩ : syracuseStep 1531727 = 2297591) B2297591
theorem B679839 : Blo 678312 679839 := bstep (se 1 (by rfl) ⟨509879, by rfl⟩ : syracuseStep 679839 = 1019759) B1019759
theorem B680263 : Blo 678312 680263 := bstep (se 1 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 680263 = 1020395) B1020395
theorem B5366245 : Blo 678312 5366245 := bstep (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) B1006171
theorem B680431 : Blo 678312 680431 := bstep (se 1 (by rfl) ⟨510323, by rfl⟩ : syracuseStep 680431 = 1020647) B1020647
theorem B680795 : Blo 678312 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B681115 : Blo 678312 681115 := bstep (se 1 (by rfl) ⟨510836, by rfl⟩ : syracuseStep 681115 = 1021673) B1021673
theorem B681199 : Blo 678312 681199 := bstep (se 1 (by rfl) ⟨510899, by rfl⟩ : syracuseStep 681199 = 1021799) B1021799
theorem B681287 : Blo 678312 681287 := bstep (se 1 (by rfl) ⟨510965, by rfl⟩ : syracuseStep 681287 = 1021931) B1021931
theorem B681319 : Blo 678312 681319 := bstep (se 1 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 681319 = 1021979) B1021979
theorem B1533311 : Blo 678312 1533311 := bstep (se 1 (by rfl) ⟨1149983, by rfl⟩ : syracuseStep 1533311 = 2299967) B2299967
theorem B17426015 : Blo 678312 17426015 := bstep (se 1 (by rfl) ⟨13069511, by rfl⟩ : syracuseStep 17426015 = 26139023) B26139023
theorem B1533599 : Blo 678312 1533599 := bstep (se 1 (by rfl) ⟨1150199, by rfl⟩ : syracuseStep 1533599 = 2300399) B2300399
theorem B681631 : Blo 678312 681631 := bstep (se 1 (by rfl) ⟨511223, by rfl⟩ : syracuseStep 681631 = 1022447) B1022447
theorem B682047 : Blo 678312 682047 := bstep (se 1 (by rfl) ⟨511535, by rfl⟩ : syracuseStep 682047 = 1023071) B1023071
theorem B682223 : Blo 678312 682223 := bstep (se 1 (by rfl) ⟨511667, by rfl⟩ : syracuseStep 682223 = 1023335) B1023335
theorem B27978155 : Blo 678312 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B1534625 : Blo 678312 1534625 := bstep (se 2 (by rfl) ⟨575484, by rfl⟩ : syracuseStep 1534625 = 1150969) B1150969
theorem B111602609 : Blo 678312 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B1534931 : Blo 678312 1534931 := bstep (se 1 (by rfl) ⟨1151198, by rfl⟩ : syracuseStep 1534931 = 2302397) B2302397
theorem B2290301 : Blo 678312 2290301 := bstep (se 3 (by rfl) ⟨429431, by rfl⟩ : syracuseStep 2290301 = 858863) B858863
theorem B2618087 : Blo 678312 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B2290409 : Blo 678312 2290409 := bstep (se 2 (by rfl) ⟨858903, by rfl⟩ : syracuseStep 2290409 = 1717807) B1717807
theorem B2290463 : Blo 678312 2290463 := bstep (se 1 (by rfl) ⟨1717847, by rfl⟩ : syracuseStep 2290463 = 3435695) B3435695
theorem B4911911 : Blo 678312 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B5174441 : Blo 678312 5174441 := bstep (se 2 (by rfl) ⟨1940415, by rfl⟩ : syracuseStep 5174441 = 3880831) B3880831
theorem B2586127 : Blo 678312 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B2324015 : Blo 678312 2324015 := bstep (se 1 (by rfl) ⟨1743011, by rfl⟩ : syracuseStep 2324015 = 3486023) B3486023
theorem B2455147 : Blo 678312 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B3438287 : Blo 678312 3438287 := bstep (se 1 (by rfl) ⟨2578715, by rfl⟩ : syracuseStep 3438287 = 5157431) B5157431
theorem B11630465 : Blo 678312 11630465 := bstep (se 2 (by rfl) ⟨4361424, by rfl⟩ : syracuseStep 11630465 = 8722849) B8722849
theorem B19593197 : Blo 678312 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B1964029 : Blo 678312 1964029 := bstep (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) B736511
theorem B2292137 : Blo 678312 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B8715059 : Blo 678312 8715059 := bstep (se 1 (by rfl) ⟨6536294, by rfl⟩ : syracuseStep 8715059 = 13072589) B13072589
theorem B1145657 : Blo 678312 1145657 := bstep (se 2 (by rfl) ⟨429621, by rfl⟩ : syracuseStep 1145657 = 859243) B859243
theorem B4357097 : Blo 678312 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B27917723 : Blo 678312 27917723 := bstep (se 1 (by rfl) ⟨20938292, by rfl⟩ : syracuseStep 27917723 = 41876585) B41876585
theorem B688159 : Blo 678312 688159 := bstep (se 1 (by rfl) ⟨516119, by rfl⟩ : syracuseStep 688159 = 1032239) B1032239
theorem B22085945 : Blo 678312 22085945 := bstep (se 2 (by rfl) ⟨8282229, by rfl⟩ : syracuseStep 22085945 = 16564459) B16564459
theorem B7734689 : Blo 678312 7734689 := bstep (se 2 (by rfl) ⟨2900508, by rfl⟩ : syracuseStep 7734689 = 5801017) B5801017
theorem B19596887 : Blo 678312 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B6981565 : Blo 678312 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B3868667 : Blo 678312 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B1017947 : Blo 678312 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B1017977 : Blo 678312 1017977 := bstep (se 2 (by rfl) ⟨381741, by rfl⟩ : syracuseStep 1017977 = 763483) B763483
theorem B2296295 : Blo 678312 2296295 := bstep (se 1 (by rfl) ⟨1722221, by rfl⟩ : syracuseStep 2296295 = 3444443) B3444443
theorem B1018523 : Blo 678312 1018523 := bstep (se 1 (by rfl) ⟨763892, by rfl⟩ : syracuseStep 1018523 = 1527785) B1527785
theorem B2296943 : Blo 678312 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B3673295 : Blo 678312 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B2297321 : Blo 678312 2297321 := bstep (se 2 (by rfl) ⟨861495, by rfl⟩ : syracuseStep 2297321 = 1722991) B1722991
theorem B1019675 : Blo 678312 1019675 := bstep (se 1 (by rfl) ⟨764756, by rfl⟩ : syracuseStep 1019675 = 1529513) B1529513
theorem B24809327 : Blo 678312 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B1020527 : Blo 678312 1020527 := bstep (se 1 (by rfl) ⟨765395, by rfl⟩ : syracuseStep 1020527 = 1530791) B1530791
theorem B13111955 : Blo 678312 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B1381151 : Blo 678312 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B13079353 : Blo 678312 13079353 := bstep (se 2 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 13079353 = 9809515) B9809515
theorem B1021151 : Blo 678312 1021151 := bstep (se 1 (by rfl) ⟨765863, by rfl⟩ : syracuseStep 1021151 = 1531727) B1531727
theorem B52893757 : Blo 678312 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B1022207 : Blo 678312 1022207 := bstep (se 1 (by rfl) ⟨766655, by rfl⟩ : syracuseStep 1022207 = 1533311) B1533311
theorem B3447197 : Blo 678312 3447197 := bstep (se 3 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 3447197 = 1292699) B1292699
theorem B1022399 : Blo 678312 1022399 := bstep (se 1 (by rfl) ⟨766799, by rfl⟩ : syracuseStep 1022399 = 1533599) B1533599
theorem B18652103 : Blo 678312 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B6626377 : Blo 678312 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B1023083 : Blo 678312 1023083 := bstep (se 1 (by rfl) ⟨767312, by rfl⟩ : syracuseStep 1023083 = 1534625) B1534625
theorem B1023287 : Blo 678312 1023287 := bstep (se 1 (by rfl) ⟨767465, by rfl⟩ : syracuseStep 1023287 = 1534931) B1534931
theorem B3448169 : Blo 678312 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B11608595 : Blo 678312 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B2302559 : Blo 678312 2302559 := bstep (se 1 (by rfl) ⟨1726919, by rfl⟩ : syracuseStep 2302559 = 3453839) B3453839
theorem B14951159 : Blo 678312 14951159 := bstep (se 1 (by rfl) ⟨11213369, by rfl⟩ : syracuseStep 14951159 = 22426739) B22426739
theorem B3449627 : Blo 678312 3449627 := bstep (se 1 (by rfl) ⟨2587220, by rfl⟩ : syracuseStep 3449627 = 5174441) B5174441
theorem B2302775 : Blo 678312 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B8856515 : Blo 678312 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B1549343 : Blo 678312 1549343 := bstep (se 1 (by rfl) ⟨1162007, by rfl⟩ : syracuseStep 1549343 = 2324015) B2324015
theorem B5810039 : Blo 678312 5810039 := bstep (se 1 (by rfl) ⟨4357529, by rfl⟩ : syracuseStep 5810039 = 8715059) B8715059
theorem B763771 : Blo 678312 763771 := bstep (se 1 (by rfl) ⟨572828, by rfl⟩ : syracuseStep 763771 = 1145657) B1145657
theorem B764959 : Blo 678312 764959 := bstep (se 1 (by rfl) ⟨573719, by rfl⟩ : syracuseStep 764959 = 1147439) B1147439
theorem B7154993 : Blo 678312 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B2764307 : Blo 678312 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B26455747 : Blo 678312 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B765787 : Blo 678312 765787 := bstep (se 1 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 765787 = 1148681) B1148681
theorem B13414691 : Blo 678312 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B766399 : Blo 678312 766399 := bstep (se 1 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 766399 = 1149599) B1149599
theorem B20886569 : Blo 678312 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B1291879 : Blo 678312 1291879 := bstep (se 1 (by rfl) ⟨968909, by rfl⟩ : syracuseStep 1291879 = 1937819) B1937819
theorem B13253375 : Blo 678312 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B11617343 : Blo 678312 11617343 := bstep (se 1 (by rfl) ⟨8713007, by rfl⟩ : syracuseStep 11617343 = 17426015) B17426015
theorem B1721513 : Blo 678312 1721513 := bstep (se 2 (by rfl) ⟨645567, by rfl⟩ : syracuseStep 1721513 = 1291135) B1291135
theorem B56542697 : Blo 678312 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B24790637 : Blo 678312 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B74401739 : Blo 678312 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B1526867 : Blo 678312 1526867 := bstep (se 1 (by rfl) ⟨1145150, by rfl⟩ : syracuseStep 1526867 = 2290301) B2290301
theorem B1526939 : Blo 678312 1526939 := bstep (se 1 (by rfl) ⟨1145204, by rfl⟩ : syracuseStep 1526939 = 2290409) B2290409
theorem B1526975 : Blo 678312 1526975 := bstep (se 1 (by rfl) ⟨1145231, by rfl⟩ : syracuseStep 1526975 = 2290463) B2290463
theorem B76664501 : Blo 678312 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B7753643 : Blo 678312 7753643 := bstep (se 1 (by rfl) ⟨5815232, by rfl⟩ : syracuseStep 7753643 = 11630465) B11630465
theorem B13062131 : Blo 678312 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B1528091 : Blo 678312 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B3265055 : Blo 678312 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B2904731 : Blo 678312 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B4969583 : Blo 678312 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B1725907 : Blo 678312 1725907 := bstep (se 1 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 1725907 = 2588861) B2588861
theorem B3103103 : Blo 678312 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B678567 : Blo 678312 678567 := bstep (se 1 (by rfl) ⟨508925, by rfl⟩ : syracuseStep 678567 = 1017851) B1017851
theorem B678783 : Blo 678312 678783 := bstep (se 1 (by rfl) ⟨509087, by rfl⟩ : syracuseStep 678783 = 1018175) B1018175
theorem B3267611 : Blo 678312 3267611 := bstep (se 1 (by rfl) ⟨2450708, by rfl⟩ : syracuseStep 3267611 = 4901417) B4901417
theorem B2907343 : Blo 678312 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B679675 : Blo 678312 679675 := bstep (se 1 (by rfl) ⟨509756, by rfl⟩ : syracuseStep 679675 = 1019513) B1019513
theorem B93413573 : Blo 678312 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B4972823 : Blo 678312 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B1532231 : Blo 678312 1532231 := bstep (se 1 (by rfl) ⟨1149173, by rfl⟩ : syracuseStep 1532231 = 2298347) B2298347
theorem B1532447 : Blo 678312 1532447 := bstep (se 1 (by rfl) ⟨1149335, by rfl⟩ : syracuseStep 1532447 = 2298671) B2298671
theorem B680807 : Blo 678312 680807 := bstep (se 1 (by rfl) ⟨510605, by rfl⟩ : syracuseStep 680807 = 1021211) B1021211
theorem B1533023 : Blo 678312 1533023 := bstep (se 1 (by rfl) ⟨1149767, by rfl⟩ : syracuseStep 1533023 = 2299535) B2299535
theorem B3434399 : Blo 678312 3434399 := bstep (se 1 (by rfl) ⟨2575799, by rfl⟩ : syracuseStep 3434399 = 5151599) B5151599
theorem B682075 : Blo 678312 682075 := bstep (se 1 (by rfl) ⟨511556, by rfl⟩ : syracuseStep 682075 = 1023113) B1023113
theorem B682087 : Blo 678312 682087 := bstep (se 1 (by rfl) ⟨511565, by rfl⟩ : syracuseStep 682087 = 1023131) B1023131
theorem B682111 : Blo 678312 682111 := bstep (se 1 (by rfl) ⟨511583, by rfl⟩ : syracuseStep 682111 = 1023167) B1023167
theorem B1534175 : Blo 678312 1534175 := bstep (se 1 (by rfl) ⟨1150631, by rfl⟩ : syracuseStep 1534175 = 2301263) B2301263
theorem B682215 : Blo 678312 682215 := bstep (se 1 (by rfl) ⟨511661, by rfl⟩ : syracuseStep 682215 = 1023323) B1023323
theorem B1469281 : Blo 678312 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B1535201 : Blo 678312 1535201 := bstep (se 2 (by rfl) ⟨575700, by rfl⟩ : syracuseStep 1535201 = 1151401) B1151401
theorem B4419119 : Blo 678312 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B2584457 : Blo 678312 2584457 := bstep (se 2 (by rfl) ⟨969171, by rfl⟩ : syracuseStep 2584457 = 1938343) B1938343
theorem B3273529 : Blo 678312 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B2585627 : Blo 678312 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B2618705 : Blo 678312 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B3274607 : Blo 678312 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B2292191 : Blo 678312 2292191 := bstep (se 1 (by rfl) ⟨1719143, by rfl⟩ : syracuseStep 2292191 = 3438287) B3438287
theorem B6519379 : Blo 678312 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B2587403 : Blo 678312 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B18611815 : Blo 678312 18611815 := bstep (se 1 (by rfl) ⟨13958861, by rfl⟩ : syracuseStep 18611815 = 27917723) B27917723
theorem B2588543 : Blo 678312 2588543 := bstep (se 1 (by rfl) ⟨1941407, by rfl⟩ : syracuseStep 2588543 = 3882815) B3882815
theorem B3670181 : Blo 678312 3670181 := bstep (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) B688159
theorem B1147675 : Blo 678312 1147675 := bstep (se 1 (by rfl) ⟨860756, by rfl⟩ : syracuseStep 1147675 = 1721513) B1721513
theorem B1017911 : Blo 678312 1017911 := bstep (se 1 (by rfl) ⟨763433, by rfl⟩ : syracuseStep 1017911 = 1526867) B1526867
theorem B1017959 : Blo 678312 1017959 := bstep (se 1 (by rfl) ⟨763469, by rfl⟩ : syracuseStep 1017959 = 1526939) B1526939
theorem B1017983 : Blo 678312 1017983 := bstep (se 1 (by rfl) ⟨763487, by rfl⟩ : syracuseStep 1017983 = 1526975) B1526975
theorem B1018361 : Blo 678312 1018361 := bstep (se 2 (by rfl) ⟨381885, by rfl⟩ : syracuseStep 1018361 = 763771) B763771
theorem B9308753 : Blo 678312 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B1018727 : Blo 678312 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B1936487 : Blo 678312 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B3313055 : Blo 678312 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B1019945 : Blo 678312 1019945 := bstep (se 2 (by rfl) ⟨382479, by rfl⟩ : syracuseStep 1019945 = 764959) B764959
theorem B2068735 : Blo 678312 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B2298131 : Blo 678312 2298131 := bstep (se 1 (by rfl) ⟨1723598, by rfl⟩ : syracuseStep 2298131 = 3447197) B3447197
theorem B2298779 : Blo 678312 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B1021049 : Blo 678312 1021049 := bstep (se 2 (by rfl) ⟨382893, by rfl⟩ : syracuseStep 1021049 = 765787) B765787
theorem B3315215 : Blo 678312 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B1021487 : Blo 678312 1021487 := bstep (se 1 (by rfl) ⟨766115, by rfl⟩ : syracuseStep 1021487 = 1532231) B1532231
theorem B7739063 : Blo 678312 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B1021631 : Blo 678312 1021631 := bstep (se 1 (by rfl) ⟨766223, by rfl⟩ : syracuseStep 1021631 = 1532447) B1532447
theorem B9967439 : Blo 678312 9967439 := bstep (se 1 (by rfl) ⟨7475579, by rfl⟩ : syracuseStep 9967439 = 14951159) B14951159
theorem B2299751 : Blo 678312 2299751 := bstep (se 1 (by rfl) ⟨1724813, by rfl⟩ : syracuseStep 2299751 = 3449627) B3449627
theorem B1021865 : Blo 678312 1021865 := bstep (se 2 (by rfl) ⟨383199, by rfl⟩ : syracuseStep 1021865 = 766399) B766399
theorem B5904343 : Blo 678312 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B1022015 : Blo 678312 1022015 := bstep (se 1 (by rfl) ⟨766511, by rfl⟩ : syracuseStep 1022015 = 1533023) B1533023
theorem B17439137 : Blo 678312 17439137 := bstep (se 2 (by rfl) ⟨6539676, by rfl⟩ : syracuseStep 17439137 = 13079353) B13079353
theorem B4364705 : Blo 678312 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B3873359 : Blo 678312 3873359 := bstep (se 1 (by rfl) ⟨2905019, by rfl⟩ : syracuseStep 3873359 = 5810039) B5810039
theorem B1022783 : Blo 678312 1022783 := bstep (se 1 (by rfl) ⟨767087, by rfl⟩ : syracuseStep 1022783 = 1534175) B1534175
theorem B2301209 : Blo 678312 2301209 := bstep (se 2 (by rfl) ⟨862953, by rfl⟩ : syracuseStep 2301209 = 1725907) B1725907
theorem B1023467 : Blo 678312 1023467 := bstep (se 1 (by rfl) ⟨767600, by rfl⟩ : syracuseStep 1023467 = 1535201) B1535201
theorem B1842871 : Blo 678312 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B70525009 : Blo 678312 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B8692505 : Blo 678312 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B19079981 : Blo 678312 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B1745803 : Blo 678312 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B3876457 : Blo 678312 3876457 := bstep (se 2 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 3876457 = 2907343) B2907343
theorem B24815753 : Blo 678312 24815753 := bstep (se 2 (by rfl) ⟨9305907, by rfl⟩ : syracuseStep 24815753 = 18611815) B18611815
theorem B14723963 : Blo 678312 14723963 := bstep (se 1 (by rfl) ⟨11042972, by rfl⟩ : syracuseStep 14723963 = 22085945) B22085945
theorem B7744895 : Blo 678312 7744895 := bstep (se 1 (by rfl) ⟨5808671, by rfl⟩ : syracuseStep 7744895 = 11617343) B11617343
theorem B5156459 : Blo 678312 5156459 := bstep (se 1 (by rfl) ⟨3867344, by rfl⟩ : syracuseStep 5156459 = 7734689) B7734689
theorem B37695131 : Blo 678312 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B16527091 : Blo 678312 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B3683069 : Blo 678312 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B2176703 : Blo 678312 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B12434735 : Blo 678312 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B2178407 : Blo 678312 2178407 := bstep (se 1 (by rfl) ⟨1633805, by rfl⟩ : syracuseStep 2178407 = 3267611) B3267611
theorem B35274329 : Blo 678312 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B62275715 : Blo 678312 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B1032895 : Blo 678312 1032895 := bstep (se 1 (by rfl) ⟨774671, by rfl⟩ : syracuseStep 1032895 = 1549343) B1549343
theorem B1722505 : Blo 678312 1722505 := bstep (se 2 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 1722505 = 1291879) B1291879
theorem B1722971 : Blo 678312 1722971 := bstep (se 1 (by rfl) ⟨1292228, by rfl⟩ : syracuseStep 1722971 = 2584457) B2584457
theorem B1723751 : Blo 678312 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B2183071 : Blo 678312 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B8835169 : Blo 678312 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B1528127 : Blo 678312 1528127 := bstep (se 1 (by rfl) ⟨1146095, by rfl⟩ : syracuseStep 1528127 = 2292191) B2292191
theorem B8835583 : Blo 678312 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B1724935 : Blo 678312 1724935 := bstep (se 1 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 1724935 = 2587403) B2587403
theorem B1725695 : Blo 678312 1725695 := bstep (se 1 (by rfl) ⟨1294271, by rfl⟩ : syracuseStep 1725695 = 2588543) B2588543
theorem B35772509 : Blo 678312 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B13064591 : Blo 678312 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B49601159 : Blo 678312 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B2579111 : Blo 678312 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B678631 : Blo 678312 678631 := bstep (se 1 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 678631 = 1017947) B1017947
theorem B678651 : Blo 678312 678651 := bstep (se 1 (by rfl) ⟨508988, by rfl⟩ : syracuseStep 678651 = 1017977) B1017977
theorem B1530863 : Blo 678312 1530863 := bstep (se 1 (by rfl) ⟨1148147, by rfl⟩ : syracuseStep 1530863 = 2296295) B2296295
theorem B679015 : Blo 678312 679015 := bstep (se 1 (by rfl) ⟨509261, by rfl⟩ : syracuseStep 679015 = 1018523) B1018523
theorem B1531295 : Blo 678312 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B2448863 : Blo 678312 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B1531547 : Blo 678312 1531547 := bstep (se 1 (by rfl) ⟨1148660, by rfl⟩ : syracuseStep 1531547 = 2297321) B2297321
theorem B51109667 : Blo 678312 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B679783 : Blo 678312 679783 := bstep (se 1 (by rfl) ⟨509837, by rfl⟩ : syracuseStep 679783 = 1019675) B1019675
theorem B16539551 : Blo 678312 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B5169095 : Blo 678312 5169095 := bstep (se 1 (by rfl) ⟨3876821, by rfl⟩ : syracuseStep 5169095 = 7753643) B7753643
theorem B8708087 : Blo 678312 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B680351 : Blo 678312 680351 := bstep (se 1 (by rfl) ⟨510263, by rfl⟩ : syracuseStep 680351 = 1020527) B1020527
theorem B8741303 : Blo 678312 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B680767 : Blo 678312 680767 := bstep (se 1 (by rfl) ⟨510575, by rfl⟩ : syracuseStep 680767 = 1021151) B1021151
theorem B1959041 : Blo 678312 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B681471 : Blo 678312 681471 := bstep (se 1 (by rfl) ⟨511103, by rfl⟩ : syracuseStep 681471 = 1022207) B1022207
theorem B681599 : Blo 678312 681599 := bstep (se 1 (by rfl) ⟨511199, by rfl⟩ : syracuseStep 681599 = 1022399) B1022399
theorem B682055 : Blo 678312 682055 := bstep (se 1 (by rfl) ⟨511541, by rfl⟩ : syracuseStep 682055 = 1023083) B1023083
theorem B682191 : Blo 678312 682191 := bstep (se 1 (by rfl) ⟨511643, by rfl⟩ : syracuseStep 682191 = 1023287) B1023287
theorem B1535039 : Blo 678312 1535039 := bstep (se 1 (by rfl) ⟨1151279, by rfl⟩ : syracuseStep 1535039 = 2302559) B2302559
theorem B1535183 : Blo 678312 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B2289599 : Blo 678312 2289599 := bstep (se 1 (by rfl) ⟨1717199, by rfl⟩ : syracuseStep 2289599 = 3434399) B3434399
theorem B2946079 : Blo 678312 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B13924379 : Blo 678312 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B41517143 : Blo 678312 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B1148647 : Blo 678312 1148647 := bstep (se 1 (by rfl) ⟨861485, by rfl⟩ : syracuseStep 1148647 = 1722971) B1722971
theorem B1149167 : Blo 678312 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B2296673 : Blo 678312 2296673 := bstep (se 2 (by rfl) ⟨861252, by rfl⟩ : syracuseStep 2296673 = 1722505) B1722505
theorem B1018751 : Blo 678312 1018751 := bstep (se 1 (by rfl) ⟨764063, by rfl⟩ : syracuseStep 1018751 = 1528127) B1528127
theorem B1150463 : Blo 678312 1150463 := bstep (se 1 (by rfl) ⟨862847, by rfl⟩ : syracuseStep 1150463 = 1725695) B1725695
theorem B5508773 : Blo 678312 5508773 := bstep (se 4 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 5508773 = 1032895) B1032895
theorem B33067439 : Blo 678312 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B1020575 : Blo 678312 1020575 := bstep (se 1 (by rfl) ⟨765431, by rfl⟩ : syracuseStep 1020575 = 1530863) B1530863
theorem B9310949 : Blo 678312 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B1020863 : Blo 678312 1020863 := bstep (se 1 (by rfl) ⟨765647, by rfl⟩ : syracuseStep 1020863 = 1531295) B1531295
theorem B1021031 : Blo 678312 1021031 := bstep (se 1 (by rfl) ⟨765773, by rfl⟩ : syracuseStep 1021031 = 1531547) B1531547
theorem B3446063 : Blo 678312 3446063 := bstep (se 1 (by rfl) ⟨2584547, by rfl⟩ : syracuseStep 3446063 = 5169095) B5169095
theorem B5805391 : Blo 678312 5805391 := bstep (se 1 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 5805391 = 8708087) B8708087
theorem B2758313 : Blo 678312 2758313 := bstep (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) B2068735
theorem B12719987 : Blo 678312 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B2299913 : Blo 678312 2299913 := bstep (se 2 (by rfl) ⟨862467, by rfl⟩ : syracuseStep 2299913 = 1724935) B1724935
theorem B11639213 : Blo 678312 11639213 := bstep (se 3 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 11639213 = 4364705) B4364705
theorem B1023359 : Blo 678312 1023359 := bstep (se 1 (by rfl) ⟨767519, by rfl⟩ : syracuseStep 1023359 = 1535039) B1535039
theorem B1023455 : Blo 678312 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B1451135 : Blo 678312 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B9282919 : Blo 678312 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B1452271 : Blo 678312 1452271 := bstep (se 1 (by rfl) ⟨1089203, by rfl⟩ : syracuseStep 1452271 = 2178407) B2178407
theorem B6205835 : Blo 678312 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B1290991 : Blo 678312 1290991 := bstep (se 1 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 1290991 = 1936487) B1936487
theorem B2208703 : Blo 678312 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B5159375 : Blo 678312 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B1719407 : Blo 678312 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B22036121 : Blo 678312 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B11026367 : Blo 678312 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B11780225 : Blo 678312 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B11780777 : Blo 678312 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B9815975 : Blo 678312 9815975 := bstep (se 1 (by rfl) ⟨7361981, by rfl⟩ : syracuseStep 9815975 = 14723963) B14723963
theorem B5163263 : Blo 678312 5163263 := bstep (se 1 (by rfl) ⟨3872447, by rfl⟩ : syracuseStep 5163263 = 7744895) B7744895
theorem B1526399 : Blo 678312 1526399 := bstep (se 1 (by rfl) ⟨1144799, by rfl⟩ : syracuseStep 1526399 = 2289599) B2289599
theorem B23516219 : Blo 678312 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B94033345 : Blo 678312 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B2446787 : Blo 678312 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B1530233 : Blo 678312 1530233 := bstep (se 2 (by rfl) ⟨573837, by rfl⟩ : syracuseStep 1530233 = 1147675) B1147675
theorem B678607 : Blo 678312 678607 := bstep (se 1 (by rfl) ⟨508955, by rfl⟩ : syracuseStep 678607 = 1017911) B1017911
theorem B678639 : Blo 678312 678639 := bstep (se 1 (by rfl) ⟨508979, by rfl⟩ : syracuseStep 678639 = 1017959) B1017959
theorem B678655 : Blo 678312 678655 := bstep (se 1 (by rfl) ⟨508991, by rfl⟩ : syracuseStep 678655 = 1017983) B1017983
theorem B678907 : Blo 678312 678907 := bstep (se 1 (by rfl) ⟨509180, by rfl⟩ : syracuseStep 678907 = 1018361) B1018361
theorem B679151 : Blo 678312 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B5168609 : Blo 678312 5168609 := bstep (se 2 (by rfl) ⟨1938228, by rfl⟩ : syracuseStep 5168609 = 3876457) B3876457
theorem B679963 : Blo 678312 679963 := bstep (se 1 (by rfl) ⟨509972, by rfl⟩ : syracuseStep 679963 = 1019945) B1019945
theorem B1532087 : Blo 678312 1532087 := bstep (se 1 (by rfl) ⟨1149065, by rfl⟩ : syracuseStep 1532087 = 2298131) B2298131
theorem B1532519 : Blo 678312 1532519 := bstep (se 1 (by rfl) ⟨1149389, by rfl⟩ : syracuseStep 1532519 = 2298779) B2298779
theorem B680699 : Blo 678312 680699 := bstep (se 1 (by rfl) ⟨510524, by rfl⟩ : syracuseStep 680699 = 1021049) B1021049
theorem B680991 : Blo 678312 680991 := bstep (se 1 (by rfl) ⟨510743, by rfl⟩ : syracuseStep 680991 = 1021487) B1021487
theorem B681087 : Blo 678312 681087 := bstep (se 1 (by rfl) ⟨510815, by rfl⟩ : syracuseStep 681087 = 1021631) B1021631
theorem B6644959 : Blo 678312 6644959 := bstep (se 1 (by rfl) ⟨4983719, by rfl⟩ : syracuseStep 6644959 = 9967439) B9967439
theorem B1533167 : Blo 678312 1533167 := bstep (se 1 (by rfl) ⟨1149875, by rfl⟩ : syracuseStep 1533167 = 2299751) B2299751
theorem B681243 : Blo 678312 681243 := bstep (se 1 (by rfl) ⟨510932, by rfl⟩ : syracuseStep 681243 = 1021865) B1021865
theorem B8840573 : Blo 678312 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B681343 : Blo 678312 681343 := bstep (se 1 (by rfl) ⟨511007, by rfl⟩ : syracuseStep 681343 = 1022015) B1022015
theorem B23848339 : Blo 678312 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B8709727 : Blo 678312 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B11626091 : Blo 678312 11626091 := bstep (se 1 (by rfl) ⟨8719568, by rfl⟩ : syracuseStep 11626091 = 17439137) B17439137
theorem B2582239 : Blo 678312 2582239 := bstep (se 1 (by rfl) ⟨1936679, by rfl⟩ : syracuseStep 2582239 = 3873359) B3873359
theorem B681855 : Blo 678312 681855 := bstep (se 1 (by rfl) ⟨511391, by rfl⟩ : syracuseStep 681855 = 1022783) B1022783
theorem B1534139 : Blo 678312 1534139 := bstep (se 1 (by rfl) ⟨1150604, by rfl⟩ : syracuseStep 1534139 = 2301209) B2301209
theorem B1632575 : Blo 678312 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B682311 : Blo 678312 682311 := bstep (se 1 (by rfl) ⟨511733, by rfl⟩ : syracuseStep 682311 = 1023467) B1023467
theorem B34073111 : Blo 678312 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B2910761 : Blo 678312 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B5827535 : Blo 678312 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B5795003 : Blo 678312 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B1306027 : Blo 678312 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B3928105 : Blo 678312 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B16543835 : Blo 678312 16543835 := bstep (se 1 (by rfl) ⟨12407876, by rfl⟩ : syracuseStep 16543835 = 24815753) B24815753
theorem B3437639 : Blo 678312 3437639 := bstep (se 1 (by rfl) ⟨2578229, by rfl⟩ : syracuseStep 3437639 = 5156459) B5156459
theorem B25130087 : Blo 678312 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B2455379 : Blo 678312 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B33159293 : Blo 678312 33159293 := bstep (se 3 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 33159293 = 12434735) B12434735
theorem B2457161 : Blo 678312 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B31489829 : Blo 678312 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B16548893 : Blo 678312 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B3442175 : Blo 678312 3442175 := bstep (se 1 (by rfl) ⟨2581631, by rfl⟩ : syracuseStep 3442175 = 5163263) B5163263
theorem B1017599 : Blo 678312 1017599 := bstep (se 1 (by rfl) ⟨763199, by rfl⟩ : syracuseStep 1017599 = 1526399) B1526399
theorem B3442985 : Blo 678312 3442985 := bstep (se 2 (by rfl) ⟨1291119, by rfl⟩ : syracuseStep 3442985 = 2582239) B2582239
theorem B3672515 : Blo 678312 3672515 := bstep (se 1 (by rfl) ⟨2754386, by rfl⟩ : syracuseStep 3672515 = 5508773) B5508773
theorem B1936361 : Blo 678312 1936361 := bstep (se 2 (by rfl) ⟨726135, by rfl⟩ : syracuseStep 1936361 = 1452271) B1452271
theorem B3869693 : Blo 678312 3869693 := bstep (se 3 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 3869693 = 1451135) B1451135
theorem B2297375 : Blo 678312 2297375 := bstep (se 1 (by rfl) ⟨1723031, by rfl⟩ : syracuseStep 2297375 = 3446063) B3446063
theorem B1838875 : Blo 678312 1838875 := bstep (se 1 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 1838875 = 2758313) B2758313
theorem B1020155 : Blo 678312 1020155 := bstep (se 1 (by rfl) ⟨765116, by rfl⟩ : syracuseStep 1020155 = 1530233) B1530233
theorem B3445739 : Blo 678312 3445739 := bstep (se 1 (by rfl) ⟨2584304, by rfl⟩ : syracuseStep 3445739 = 5168609) B5168609
theorem B1021391 : Blo 678312 1021391 := bstep (se 1 (by rfl) ⟨766043, by rfl⟩ : syracuseStep 1021391 = 1532087) B1532087
theorem B1021679 : Blo 678312 1021679 := bstep (se 1 (by rfl) ⟨766259, by rfl⟩ : syracuseStep 1021679 = 1532519) B1532519
theorem B1022111 : Blo 678312 1022111 := bstep (se 1 (by rfl) ⟨766583, by rfl⟩ : syracuseStep 1022111 = 1533167) B1533167
theorem B1022759 : Blo 678312 1022759 := bstep (se 1 (by rfl) ⟨767069, by rfl⟩ : syracuseStep 1022759 = 1534139) B1534139
theorem B22715407 : Blo 678312 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B1940507 : Blo 678312 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B7740521 : Blo 678312 7740521 := bstep (se 2 (by rfl) ⟨2902695, by rfl⟩ : syracuseStep 7740521 = 5805391) B5805391
theorem B125377793 : Blo 678312 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B16753391 : Blo 678312 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B14690747 : Blo 678312 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B7350911 : Blo 678312 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B766111 : Blo 678312 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B31797785 : Blo 678312 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B11612969 : Blo 678312 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B766975 : Blo 678312 766975 := bstep (se 1 (by rfl) ⟨575231, by rfl⟩ : syracuseStep 766975 = 1150463) B1150463
theorem B6207299 : Blo 678312 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B15677479 : Blo 678312 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B1721321 : Blo 678312 1721321 := bstep (se 2 (by rfl) ⟨645495, by rfl⟩ : syracuseStep 1721321 = 1290991) B1290991
theorem B7750727 : Blo 678312 7750727 := bstep (se 1 (by rfl) ⟨5813045, by rfl⟩ : syracuseStep 7750727 = 11626091) B11626091
theorem B35439781 : Blo 678312 35439781 := bstep (se 4 (by rfl) ⟨3322479, by rfl⟩ : syracuseStep 35439781 = 6644959) B6644959
theorem B3885023 : Blo 678312 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B6965477 : Blo 678312 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B11029223 : Blo 678312 11029223 := bstep (se 1 (by rfl) ⟨8271917, by rfl⟩ : syracuseStep 11029223 = 16543835) B16543835
theorem B22106195 : Blo 678312 22106195 := bstep (se 1 (by rfl) ⟨16579646, by rfl⟩ : syracuseStep 22106195 = 33159293) B33159293
theorem B20993219 : Blo 678312 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B27678095 : Blo 678312 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B7853483 : Blo 678312 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B7853851 : Blo 678312 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B6543983 : Blo 678312 6543983 := bstep (se 1 (by rfl) ⟨4907987, by rfl⟩ : syracuseStep 6543983 = 9815975) B9815975
theorem B12377225 : Blo 678312 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B1531115 : Blo 678312 1531115 := bstep (se 1 (by rfl) ⟨1148336, by rfl⟩ : syracuseStep 1531115 = 2296673) B2296673
theorem B679167 : Blo 678312 679167 := bstep (se 1 (by rfl) ⟨509375, by rfl⟩ : syracuseStep 679167 = 1018751) B1018751
theorem B1531529 : Blo 678312 1531529 := bstep (se 2 (by rfl) ⟨574323, by rfl⟩ : syracuseStep 1531529 = 1148647) B1148647
theorem B22044959 : Blo 678312 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B680383 : Blo 678312 680383 := bstep (se 1 (by rfl) ⟨510287, by rfl⟩ : syracuseStep 680383 = 1020575) B1020575
theorem B680575 : Blo 678312 680575 := bstep (se 1 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 680575 = 1020863) B1020863
theorem B680687 : Blo 678312 680687 := bstep (se 1 (by rfl) ⟨510515, by rfl⟩ : syracuseStep 680687 = 1021031) B1021031
theorem B1631191 : Blo 678312 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B8479991 : Blo 678312 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B1533275 : Blo 678312 1533275 := bstep (se 1 (by rfl) ⟨1149956, by rfl⟩ : syracuseStep 1533275 = 2299913) B2299913
theorem B7759475 : Blo 678312 7759475 := bstep (se 1 (by rfl) ⟨5819606, by rfl⟩ : syracuseStep 7759475 = 11639213) B11639213
theorem B682239 : Blo 678312 682239 := bstep (se 1 (by rfl) ⟨511679, by rfl⟩ : syracuseStep 682239 = 1023359) B1023359
theorem B682303 : Blo 678312 682303 := bstep (se 1 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 682303 = 1023455) B1023455
theorem B5237473 : Blo 678312 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B4353533 : Blo 678312 4353533 := bstep (se 3 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 4353533 = 1632575) B1632575
theorem B5893715 : Blo 678312 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B2944937 : Blo 678312 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B3863335 : Blo 678312 3863335 := bstep (se 1 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 3863335 = 5795003) B5795003
theorem B2291759 : Blo 678312 2291759 := bstep (se 1 (by rfl) ⟨1718819, by rfl⟩ : syracuseStep 2291759 = 3437639) B3437639
theorem B1636919 : Blo 678312 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B3439583 : Blo 678312 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B1146271 : Blo 678312 1146271 := bstep (se 1 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 1146271 = 1719407) B1719407
theorem B1638107 : Blo 678312 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B1147547 : Blo 678312 1147547 := bstep (se 1 (by rfl) ⟨860660, by rfl⟩ : syracuseStep 1147547 = 1721321) B1721321
theorem B2294783 : Blo 678312 2294783 := bstep (se 1 (by rfl) ⟨1721087, by rfl⟩ : syracuseStep 2294783 = 3442175) B3442175
theorem B2590015 : Blo 678312 2590015 := bstep (se 1 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 2590015 = 3885023) B3885023
theorem B2295323 : Blo 678312 2295323 := bstep (se 1 (by rfl) ⟨1721492, by rfl⟩ : syracuseStep 2295323 = 3442985) B3442985
theorem B47253041 : Blo 678312 47253041 := bstep (se 2 (by rfl) ⟨17719890, by rfl⟩ : syracuseStep 47253041 = 35439781) B35439781
theorem B2297159 : Blo 678312 2297159 := bstep (se 1 (by rfl) ⟨1722869, by rfl⟩ : syracuseStep 2297159 = 3445739) B3445739
theorem B13995479 : Blo 678312 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B18452063 : Blo 678312 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B6983297 : Blo 678312 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B20942621 : Blo 678312 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B4362655 : Blo 678312 4362655 := bstep (se 1 (by rfl) ⟨3271991, by rfl⟩ : syracuseStep 4362655 = 6543983) B6543983
theorem B1020743 : Blo 678312 1020743 := bstep (se 1 (by rfl) ⟨765557, by rfl⟩ : syracuseStep 1020743 = 1531115) B1531115
theorem B1021019 : Blo 678312 1021019 := bstep (se 1 (by rfl) ⟨765764, by rfl⟩ : syracuseStep 1021019 = 1531529) B1531529
theorem B1021481 : Blo 678312 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B1022183 : Blo 678312 1022183 := bstep (se 1 (by rfl) ⟨766637, by rfl⟩ : syracuseStep 1022183 = 1533275) B1533275
theorem B5151113 : Blo 678312 5151113 := bstep (se 2 (by rfl) ⟨1931667, by rfl⟩ : syracuseStep 5151113 = 3863335) B3863335
theorem B1022633 : Blo 678312 1022633 := bstep (se 2 (by rfl) ⟨383487, by rfl⟩ : syracuseStep 1022633 = 766975) B766975
theorem B7741979 : Blo 678312 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B4138199 : Blo 678312 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B30287209 : Blo 678312 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B1091279 : Blo 678312 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B1092071 : Blo 678312 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B2174921 : Blo 678312 2174921 := bstep (se 2 (by rfl) ⟨815595, by rfl⟩ : syracuseStep 2174921 = 1631191) B1631191
theorem B7352815 : Blo 678312 7352815 := bstep (se 1 (by rfl) ⟨5514611, by rfl⟩ : syracuseStep 7352815 = 11029223) B11029223
theorem B1290907 : Blo 678312 1290907 := bstep (se 1 (by rfl) ⟨968180, by rfl⟩ : syracuseStep 1290907 = 1936361) B1936361
theorem B1293671 : Blo 678312 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B5160347 : Blo 678312 5160347 := bstep (se 1 (by rfl) ⟨3870260, by rfl⟩ : syracuseStep 5160347 = 7740521) B7740521
theorem B14696639 : Blo 678312 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B5653327 : Blo 678312 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B4900607 : Blo 678312 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B2902355 : Blo 678312 2902355 := bstep (se 1 (by rfl) ⟨2176766, by rfl⟩ : syracuseStep 2902355 = 4353533) B4353533
theorem B10471801 : Blo 678312 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B1527839 : Blo 678312 1527839 := bstep (se 1 (by rfl) ⟨1145879, by rfl⟩ : syracuseStep 1527839 = 2291759) B2291759
theorem B1528361 : Blo 678312 1528361 := bstep (se 2 (by rfl) ⟨573135, by rfl⟩ : syracuseStep 1528361 = 1146271) B1146271
theorem B11032595 : Blo 678312 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B5167151 : Blo 678312 5167151 := bstep (se 1 (by rfl) ⟨3875363, by rfl⟩ : syracuseStep 5167151 = 7750727) B7750727
theorem B678399 : Blo 678312 678399 := bstep (se 1 (by rfl) ⟨508799, by rfl⟩ : syracuseStep 678399 = 1017599) B1017599
theorem B4643651 : Blo 678312 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B2448343 : Blo 678312 2448343 := bstep (se 1 (by rfl) ⟨1836257, by rfl⟩ : syracuseStep 2448343 = 3672515) B3672515
theorem B2579795 : Blo 678312 2579795 := bstep (se 1 (by rfl) ⟨1934846, by rfl⟩ : syracuseStep 2579795 = 3869693) B3869693
theorem B1531583 : Blo 678312 1531583 := bstep (se 1 (by rfl) ⟨1148687, by rfl⟩ : syracuseStep 1531583 = 2297375) B2297375
theorem B14737463 : Blo 678312 14737463 := bstep (se 1 (by rfl) ⟨11053097, by rfl⟩ : syracuseStep 14737463 = 22106195) B22106195
theorem B680103 : Blo 678312 680103 := bstep (se 1 (by rfl) ⟨510077, by rfl⟩ : syracuseStep 680103 = 1020155) B1020155
theorem B680927 : Blo 678312 680927 := bstep (se 1 (by rfl) ⟨510695, by rfl⟩ : syracuseStep 680927 = 1021391) B1021391
theorem B681119 : Blo 678312 681119 := bstep (se 1 (by rfl) ⟨510839, by rfl⟩ : syracuseStep 681119 = 1021679) B1021679
theorem B681407 : Blo 678312 681407 := bstep (se 1 (by rfl) ⟨511055, by rfl⟩ : syracuseStep 681407 = 1022111) B1022111
theorem B681839 : Blo 678312 681839 := bstep (se 1 (by rfl) ⟨511379, by rfl⟩ : syracuseStep 681839 = 1022759) B1022759
theorem B8251483 : Blo 678312 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B83585195 : Blo 678312 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B2451833 : Blo 678312 2451833 := bstep (se 2 (by rfl) ⟨919437, by rfl⟩ : syracuseStep 2451833 = 1838875) B1838875
theorem B11168927 : Blo 678312 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B5172983 : Blo 678312 5172983 := bstep (se 1 (by rfl) ⟨3879737, by rfl⟩ : syracuseStep 5172983 = 7759475) B7759475
theorem B9793831 : Blo 678312 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B3929143 : Blo 678312 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B1963291 : Blo 678312 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B20903305 : Blo 678312 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B21198523 : Blo 678312 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B2293055 : Blo 678312 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B9797759 : Blo 678312 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B7537769 : Blo 678312 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B1934903 : Blo 678312 1934903 := bstep (se 1 (by rfl) ⟨1451177, by rfl⟩ : syracuseStep 1934903 = 2902355) B2902355
theorem B4655531 : Blo 678312 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B13961747 : Blo 678312 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B1018559 : Blo 678312 1018559 := bstep (se 1 (by rfl) ⟨763919, by rfl⟩ : syracuseStep 1018559 = 1527839) B1527839
theorem B1018907 : Blo 678312 1018907 := bstep (se 1 (by rfl) ⟨764180, by rfl⟩ : syracuseStep 1018907 = 1528361) B1528361
theorem B13962401 : Blo 678312 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B3444767 : Blo 678312 3444767 := bstep (se 1 (by rfl) ⟨2583575, by rfl⟩ : syracuseStep 3444767 = 5167151) B5167151
theorem B1021055 : Blo 678312 1021055 := bstep (se 1 (by rfl) ⟨765791, by rfl⟩ : syracuseStep 1021055 = 1531583) B1531583
theorem B9803753 : Blo 678312 9803753 := bstep (se 2 (by rfl) ⟨3676407, by rfl⟩ : syracuseStep 9803753 = 7352815) B7352815
theorem B2758799 : Blo 678312 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B728047 : Blo 678312 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B7445951 : Blo 678312 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B3448655 : Blo 678312 3448655 := bstep (se 1 (by rfl) ⟨2586491, by rfl⟩ : syracuseStep 3448655 = 5172983) B5172983
theorem B1449947 : Blo 678312 1449947 := bstep (se 1 (by rfl) ⟨1087460, by rfl⟩ : syracuseStep 1449947 = 2174921) B2174921
theorem B3449789 : Blo 678312 3449789 := bstep (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) B1293671
theorem B765031 : Blo 678312 765031 := bstep (se 1 (by rfl) ⟨573773, by rfl⟩ : syracuseStep 765031 = 1147547) B1147547
theorem B31502027 : Blo 678312 31502027 := bstep (se 1 (by rfl) ⟨23626520, by rfl⟩ : syracuseStep 31502027 = 47253041) B47253041
theorem B3453353 : Blo 678312 3453353 := bstep (se 2 (by rfl) ⟨1295007, by rfl⟩ : syracuseStep 3453353 = 2590015) B2590015
theorem B40382945 : Blo 678312 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B12301375 : Blo 678312 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B7355063 : Blo 678312 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B3095767 : Blo 678312 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B1719863 : Blo 678312 1719863 := bstep (se 1 (by rfl) ⟨1289897, by rfl⟩ : syracuseStep 1719863 = 2579795) B2579795
theorem B5161319 : Blo 678312 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B13058441 : Blo 678312 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B5816873 : Blo 678312 5816873 := bstep (se 2 (by rfl) ⟨2181327, by rfl⟩ : syracuseStep 5816873 = 4362655) B4362655
theorem B1721209 : Blo 678312 1721209 := bstep (se 2 (by rfl) ⟨645453, by rfl⟩ : syracuseStep 1721209 = 1290907) B1290907
theorem B55723463 : Blo 678312 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B27871073 : Blo 678312 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B28264697 : Blo 678312 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B3264457 : Blo 678312 3264457 := bstep (se 2 (by rfl) ⟨1224171, by rfl⟩ : syracuseStep 3264457 = 2448343) B2448343
theorem B1528703 : Blo 678312 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B1529855 : Blo 678312 1529855 := bstep (se 1 (by rfl) ⟨1147391, by rfl⟩ : syracuseStep 1529855 = 2294783) B2294783
theorem B1530215 : Blo 678312 1530215 := bstep (se 1 (by rfl) ⟨1147661, by rfl⟩ : syracuseStep 1530215 = 2295323) B2295323
theorem B3267071 : Blo 678312 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B1531439 : Blo 678312 1531439 := bstep (se 1 (by rfl) ⟨1148579, by rfl⟩ : syracuseStep 1531439 = 2297159) B2297159
theorem B9330319 : Blo 678312 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B11001977 : Blo 678312 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B680495 : Blo 678312 680495 := bstep (se 1 (by rfl) ⟨510371, by rfl⟩ : syracuseStep 680495 = 1020743) B1020743
theorem B680679 : Blo 678312 680679 := bstep (se 1 (by rfl) ⟨510509, by rfl⟩ : syracuseStep 680679 = 1021019) B1021019
theorem B680987 : Blo 678312 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B681455 : Blo 678312 681455 := bstep (se 1 (by rfl) ⟨511091, by rfl⟩ : syracuseStep 681455 = 1022183) B1022183
theorem B3434075 : Blo 678312 3434075 := bstep (se 1 (by rfl) ⟨2575556, by rfl⟩ : syracuseStep 3434075 = 5151113) B5151113
theorem B681755 : Blo 678312 681755 := bstep (se 1 (by rfl) ⟨511316, by rfl⟩ : syracuseStep 681755 = 1022633) B1022633
theorem B2910077 : Blo 678312 2910077 := bstep (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) B1091279
theorem B9824975 : Blo 678312 9824975 := bstep (se 1 (by rfl) ⟨7368731, by rfl⟩ : syracuseStep 9824975 = 14737463) B14737463
theorem B5238857 : Blo 678312 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B1634555 : Blo 678312 1634555 := bstep (se 1 (by rfl) ⟨1225916, by rfl⟩ : syracuseStep 1634555 = 2451833) B2451833
theorem B2617721 : Blo 678312 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B3440231 : Blo 678312 3440231 := bstep (se 1 (by rfl) ⟨2580173, by rfl⟩ : syracuseStep 3440231 = 5160347) B5160347
theorem B3440879 : Blo 678312 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B2294945 : Blo 678312 2294945 := bstep (se 2 (by rfl) ⟨860604, by rfl⟩ : syracuseStep 2294945 = 1721209) B1721209
theorem B18580715 : Blo 678312 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B18843131 : Blo 678312 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B9307831 : Blo 678312 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B9308267 : Blo 678312 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B2296511 : Blo 678312 2296511 := bstep (se 1 (by rfl) ⟨1722383, by rfl⟩ : syracuseStep 2296511 = 3444767) B3444767
theorem B1019135 : Blo 678312 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B1019903 : Blo 678312 1019903 := bstep (se 1 (by rfl) ⟨764927, by rfl⟩ : syracuseStep 1019903 = 1529855) B1529855
theorem B1839199 : Blo 678312 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B1020041 : Blo 678312 1020041 := bstep (se 2 (by rfl) ⟨382515, by rfl⟩ : syracuseStep 1020041 = 765031) B765031
theorem B1020143 : Blo 678312 1020143 := bstep (se 1 (by rfl) ⟨765107, by rfl⟩ : syracuseStep 1020143 = 1530215) B1530215
theorem B1020959 : Blo 678312 1020959 := bstep (se 1 (by rfl) ⟨765719, by rfl⟩ : syracuseStep 1020959 = 1531439) B1531439
theorem B2299103 : Blo 678312 2299103 := bstep (se 1 (by rfl) ⟨1724327, by rfl⟩ : syracuseStep 2299103 = 3448655) B3448655
theorem B2299859 : Blo 678312 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B1940051 : Blo 678312 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B1089703 : Blo 678312 1089703 := bstep (se 1 (by rfl) ⟨817277, by rfl⟩ : syracuseStep 1089703 = 1634555) B1634555
theorem B1745147 : Blo 678312 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B2302235 : Blo 678312 2302235 := bstep (se 1 (by rfl) ⟨1726676, by rfl⟩ : syracuseStep 2302235 = 3453353) B3453353
theorem B6531839 : Blo 678312 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B3877915 : Blo 678312 3877915 := bstep (se 1 (by rfl) ⟨2908436, by rfl⟩ : syracuseStep 3877915 = 5816873) B5816873
theorem B5025179 : Blo 678312 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B1289935 : Blo 678312 1289935 := bstep (se 1 (by rfl) ⟨967451, by rfl⟩ : syracuseStep 1289935 = 1934903) B1934903
theorem B6535835 : Blo 678312 6535835 := bstep (se 1 (by rfl) ⟨4901876, by rfl⟩ : syracuseStep 6535835 = 9803753) B9803753
theorem B2178047 : Blo 678312 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B4963967 : Blo 678312 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B16401833 : Blo 678312 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B3492571 : Blo 678312 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B26921963 : Blo 678312 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B49761701 : Blo 678312 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B970729 : Blo 678312 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B4903375 : Blo 678312 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B8705627 : Blo 678312 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B37148975 : Blo 678312 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B3103687 : Blo 678312 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B679039 : Blo 678312 679039 := bstep (se 1 (by rfl) ⟨509279, by rfl⟩ : syracuseStep 679039 = 1018559) B1018559
theorem B679271 : Blo 678312 679271 := bstep (se 1 (by rfl) ⟨509453, by rfl⟩ : syracuseStep 679271 = 1018907) B1018907
theorem B680703 : Blo 678312 680703 := bstep (se 1 (by rfl) ⟨510527, by rfl⟩ : syracuseStep 680703 = 1021055) B1021055
theorem B4352609 : Blo 678312 4352609 := bstep (se 2 (by rfl) ⟨1632228, by rfl⟩ : syracuseStep 4352609 = 3264457) B3264457
theorem B7334651 : Blo 678312 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B2289383 : Blo 678312 2289383 := bstep (se 1 (by rfl) ⟨1717037, by rfl⟩ : syracuseStep 2289383 = 3434075) B3434075
theorem B6549983 : Blo 678312 6549983 := bstep (se 1 (by rfl) ⟨4912487, by rfl⟩ : syracuseStep 6549983 = 9824975) B9824975
theorem B21001351 : Blo 678312 21001351 := bstep (se 1 (by rfl) ⟨15751013, by rfl⟩ : syracuseStep 21001351 = 31502027) B31502027
theorem B4127689 : Blo 678312 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B1146575 : Blo 678312 1146575 := bstep (se 1 (by rfl) ⟨859931, by rfl⟩ : syracuseStep 1146575 = 1719863) B1719863
theorem B2293487 : Blo 678312 2293487 := bstep (se 1 (by rfl) ⟨1720115, by rfl⟩ : syracuseStep 2293487 = 3440231) B3440231
theorem B3866525 : Blo 678312 3866525 := bstep (se 3 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 3866525 = 1449947) B1449947
theorem B2293919 : Blo 678312 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B12387143 : Blo 678312 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B4656761 : Blo 678312 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B5803751 : Blo 678312 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B174952885 : Blo 678312 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B4889767 : Blo 678312 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B5808125 : Blo 678312 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B4366655 : Blo 678312 4366655 := bstep (se 1 (by rfl) ⟨3274991, by rfl⟩ : syracuseStep 4366655 = 6549983) B6549983
theorem B4138249 : Blo 678312 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B764383 : Blo 678312 764383 := bstep (se 1 (by rfl) ⟨573287, by rfl⟩ : syracuseStep 764383 = 1146575) B1146575
theorem B5811749 : Blo 678312 5811749 := bstep (se 4 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 5811749 = 1089703) B1089703
theorem B12562087 : Blo 678312 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B6205511 : Blo 678312 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B33174467 : Blo 678312 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B1719913 : Blo 678312 1719913 := bstep (se 2 (by rfl) ⟨644967, by rfl⟩ : syracuseStep 1719913 = 1289935) B1289935
theorem B1163431 : Blo 678312 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B6537833 : Blo 678312 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B28001801 : Blo 678312 28001801 := bstep (se 2 (by rfl) ⟨10500675, by rfl⟩ : syracuseStep 28001801 = 21001351) B21001351
theorem B2901739 : Blo 678312 2901739 := bstep (se 1 (by rfl) ⟨2176304, by rfl⟩ : syracuseStep 2901739 = 4352609) B4352609
theorem B1526255 : Blo 678312 1526255 := bstep (se 1 (by rfl) ⟨1144691, by rfl⟩ : syracuseStep 1526255 = 2289383) B2289383
theorem B1528991 : Blo 678312 1528991 := bstep (se 1 (by rfl) ⟨1146743, by rfl⟩ : syracuseStep 1528991 = 2293487) B2293487
theorem B2577683 : Blo 678312 2577683 := bstep (se 1 (by rfl) ⟨1933262, by rfl⟩ : syracuseStep 2577683 = 3866525) B3866525
theorem B1529963 : Blo 678312 1529963 := bstep (se 1 (by rfl) ⟨1147472, by rfl⟩ : syracuseStep 1529963 = 2294945) B2294945
theorem B1531007 : Blo 678312 1531007 := bstep (se 1 (by rfl) ⟨1148255, by rfl⟩ : syracuseStep 1531007 = 2296511) B2296511
theorem B17947975 : Blo 678312 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B679423 : Blo 678312 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B12410441 : Blo 678312 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B679935 : Blo 678312 679935 := bstep (se 1 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 679935 = 1019903) B1019903
theorem B680027 : Blo 678312 680027 := bstep (se 1 (by rfl) ⟨510020, by rfl⟩ : syracuseStep 680027 = 1020041) B1020041
theorem B680095 : Blo 678312 680095 := bstep (se 1 (by rfl) ⟨510071, by rfl⟩ : syracuseStep 680095 = 1020143) B1020143
theorem B680639 : Blo 678312 680639 := bstep (se 1 (by rfl) ⟨510479, by rfl⟩ : syracuseStep 680639 = 1020959) B1020959
theorem B1532735 : Blo 678312 1532735 := bstep (se 1 (by rfl) ⟨1149551, by rfl⟩ : syracuseStep 1532735 = 2299103) B2299103
theorem B1533239 : Blo 678312 1533239 := bstep (se 1 (by rfl) ⟨1149929, by rfl⟩ : syracuseStep 1533239 = 2299859) B2299859
theorem B5170553 : Blo 678312 5170553 := bstep (se 2 (by rfl) ⟨1938957, by rfl⟩ : syracuseStep 5170553 = 3877915) B3877915
theorem B24765983 : Blo 678312 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B2452265 : Blo 678312 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B1534823 : Blo 678312 1534823 := bstep (se 1 (by rfl) ⟨1151117, by rfl⟩ : syracuseStep 1534823 = 2302235) B2302235
theorem B5173469 : Blo 678312 5173469 := bstep (se 3 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 5173469 = 1940051) B1940051
theorem B4354559 : Blo 678312 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B13400477 : Blo 678312 13400477 := bstep (se 3 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 13400477 = 5025179) B5025179
theorem B5503585 : Blo 678312 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B4357223 : Blo 678312 4357223 := bstep (se 1 (by rfl) ⟨3267917, by rfl⟩ : syracuseStep 4357223 = 6535835) B6535835
theorem B20708885 : Blo 678312 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B3309311 : Blo 678312 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B4358555 : Blo 678312 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B8258095 : Blo 678312 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B1017503 : Blo 678312 1017503 := bstep (se 1 (by rfl) ⟨763127, by rfl⟩ : syracuseStep 1017503 = 1526255) B1526255
theorem B3868985 : Blo 678312 3868985 := bstep (se 2 (by rfl) ⟨1450869, by rfl⟩ : syracuseStep 3868985 = 2901739) B2901739
theorem B3869167 : Blo 678312 3869167 := bstep (se 1 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 3869167 = 5803751) B5803751
theorem B1019177 : Blo 678312 1019177 := bstep (se 2 (by rfl) ⟨382191, by rfl⟩ : syracuseStep 1019177 = 764383) B764383
theorem B1019327 : Blo 678312 1019327 := bstep (se 1 (by rfl) ⟨764495, by rfl⟩ : syracuseStep 1019327 = 1528991) B1528991
theorem B1019975 : Blo 678312 1019975 := bstep (se 1 (by rfl) ⟨764981, by rfl⟩ : syracuseStep 1019975 = 1529963) B1529963
theorem B1020671 : Blo 678312 1020671 := bstep (se 1 (by rfl) ⟨765503, by rfl⟩ : syracuseStep 1020671 = 1531007) B1531007
theorem B16749449 : Blo 678312 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B3872083 : Blo 678312 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B1021823 : Blo 678312 1021823 := bstep (se 1 (by rfl) ⟨766367, by rfl⟩ : syracuseStep 1021823 = 1532735) B1532735
theorem B1022159 : Blo 678312 1022159 := bstep (se 1 (by rfl) ⟨766619, by rfl⟩ : syracuseStep 1022159 = 1533239) B1533239
theorem B3447035 : Blo 678312 3447035 := bstep (se 1 (by rfl) ⟨2585276, by rfl⟩ : syracuseStep 3447035 = 5170553) B5170553
theorem B1023215 : Blo 678312 1023215 := bstep (se 1 (by rfl) ⟨767411, by rfl⟩ : syracuseStep 1023215 = 1534823) B1534823
theorem B3874499 : Blo 678312 3874499 := bstep (se 1 (by rfl) ⟨2905874, by rfl⟩ : syracuseStep 3874499 = 5811749) B5811749
theorem B4137007 : Blo 678312 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B3448979 : Blo 678312 3448979 := bstep (se 1 (by rfl) ⟨2586734, by rfl⟩ : syracuseStep 3448979 = 5173469) B5173469
theorem B23930633 : Blo 678312 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B13805923 : Blo 678312 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B2206207 : Blo 678312 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B1551241 : Blo 678312 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B5517665 : Blo 678312 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B1718455 : Blo 678312 1718455 := bstep (se 1 (by rfl) ⟨1288841, by rfl⟩ : syracuseStep 1718455 = 2577683) B2577683
theorem B8273627 : Blo 678312 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B2903039 : Blo 678312 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B8933651 : Blo 678312 8933651 := bstep (se 1 (by rfl) ⟨6700238, by rfl⟩ : syracuseStep 8933651 = 13400477) B13400477
theorem B2904815 : Blo 678312 2904815 := bstep (se 1 (by rfl) ⟨2178611, by rfl⟩ : syracuseStep 2904815 = 4357223) B4357223
theorem B1529279 : Blo 678312 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B18667867 : Blo 678312 18667867 := bstep (se 1 (by rfl) ⟨14000900, by rfl⟩ : syracuseStep 18667867 = 28001801) B28001801
theorem B3104507 : Blo 678312 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B2911103 : Blo 678312 2911103 := bstep (se 1 (by rfl) ⟨2183327, by rfl⟩ : syracuseStep 2911103 = 4366655) B4366655
theorem B233270513 : Blo 678312 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B16510655 : Blo 678312 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B1634843 : Blo 678312 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B22116311 : Blo 678312 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B7338113 : Blo 678312 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B6519689 : Blo 678312 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B2293217 : Blo 678312 2293217 := bstep (se 2 (by rfl) ⟨859956, by rfl⟩ : syracuseStep 2293217 = 1719913) B1719913
theorem B4359581 : Blo 678312 4359581 := bstep (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) B1634843
theorem B1935359 : Blo 678312 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B11766437 : Blo 678312 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B44043173 : Blo 678312 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B1936543 : Blo 678312 1936543 := bstep (se 1 (by rfl) ⟨1452407, by rfl⟩ : syracuseStep 1936543 = 2904815) B2904815
theorem B1019519 : Blo 678312 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B2298023 : Blo 678312 2298023 := bstep (se 1 (by rfl) ⟨1723517, by rfl⟩ : syracuseStep 2298023 = 3447035) B3447035
theorem B2299319 : Blo 678312 2299319 := bstep (se 1 (by rfl) ⟨1724489, by rfl⟩ : syracuseStep 2299319 = 3448979) B3448979
theorem B1940735 : Blo 678312 1940735 := bstep (se 1 (by rfl) ⟨1455551, by rfl⟩ : syracuseStep 1940735 = 2911103) B2911103
theorem B3678443 : Blo 678312 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B4892075 : Blo 678312 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B5515751 : Blo 678312 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B5516009 : Blo 678312 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B5158889 : Blo 678312 5158889 := bstep (se 2 (by rfl) ⟨1934583, by rfl⟩ : syracuseStep 5158889 = 3869167) B3869167
theorem B8273285 : Blo 678312 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B5162777 : Blo 678312 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B24890489 : Blo 678312 24890489 := bstep (se 2 (by rfl) ⟨9333933, by rfl⟩ : syracuseStep 24890489 = 18667867) B18667867
theorem B4346459 : Blo 678312 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B8278685 : Blo 678312 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B1528811 : Blo 678312 1528811 := bstep (se 1 (by rfl) ⟨1146608, by rfl⟩ : syracuseStep 1528811 = 2293217) B2293217
theorem B2905703 : Blo 678312 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B678335 : Blo 678312 678335 := bstep (se 1 (by rfl) ⟨508751, by rfl⟩ : syracuseStep 678335 = 1017503) B1017503
theorem B2579323 : Blo 678312 2579323 := bstep (se 1 (by rfl) ⟨1934492, by rfl⟩ : syracuseStep 2579323 = 3868985) B3868985
theorem B679451 : Blo 678312 679451 := bstep (se 1 (by rfl) ⟨509588, by rfl⟩ : syracuseStep 679451 = 1019177) B1019177
theorem B679551 : Blo 678312 679551 := bstep (se 1 (by rfl) ⟨509663, by rfl⟩ : syracuseStep 679551 = 1019327) B1019327
theorem B679983 : Blo 678312 679983 := bstep (se 1 (by rfl) ⟨509987, by rfl⟩ : syracuseStep 679983 = 1019975) B1019975
theorem B5955767 : Blo 678312 5955767 := bstep (se 1 (by rfl) ⟨4466825, by rfl⟩ : syracuseStep 5955767 = 8933651) B8933651
theorem B18407897 : Blo 678312 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B680447 : Blo 678312 680447 := bstep (se 1 (by rfl) ⟨510335, by rfl⟩ : syracuseStep 680447 = 1020671) B1020671
theorem B11166299 : Blo 678312 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B681215 : Blo 678312 681215 := bstep (se 1 (by rfl) ⟨510911, by rfl⟩ : syracuseStep 681215 = 1021823) B1021823
theorem B681439 : Blo 678312 681439 := bstep (se 1 (by rfl) ⟨511079, by rfl⟩ : syracuseStep 681439 = 1022159) B1022159
theorem B682143 : Blo 678312 682143 := bstep (se 1 (by rfl) ⟨511607, by rfl⟩ : syracuseStep 682143 = 1023215) B1023215
theorem B2582999 : Blo 678312 2582999 := bstep (se 1 (by rfl) ⟨1937249, by rfl⟩ : syracuseStep 2582999 = 3874499) B3874499
theorem B15953755 : Blo 678312 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B155513675 : Blo 678312 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B11007103 : Blo 678312 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B2291273 : Blo 678312 2291273 := bstep (se 2 (by rfl) ⟨859227, by rfl⟩ : syracuseStep 2291273 = 1718455) B1718455
theorem B14744207 : Blo 678312 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B3441851 : Blo 678312 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B29362115 : Blo 678312 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B1019207 : Blo 678312 1019207 := bstep (se 1 (by rfl) ⟨764405, by rfl⟩ : syracuseStep 1019207 = 1528811) B1528811
theorem B1937135 : Blo 678312 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B21271673 : Blo 678312 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B3970511 : Blo 678312 3970511 := bstep (se 1 (by rfl) ⟨2977883, by rfl⟩ : syracuseStep 3970511 = 5955767) B5955767
theorem B7444199 : Blo 678312 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B3677167 : Blo 678312 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B3677339 : Blo 678312 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B5515523 : Blo 678312 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B1290239 : Blo 678312 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B7844291 : Blo 678312 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B16593659 : Blo 678312 16593659 := bstep (se 1 (by rfl) ⟨12445244, by rfl⟩ : syracuseStep 16593659 = 24890489) B24890489
theorem B2897639 : Blo 678312 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B5519123 : Blo 678312 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B1293823 : Blo 678312 1293823 := bstep (se 1 (by rfl) ⟨970367, by rfl⟩ : syracuseStep 1293823 = 1940735) B1940735
theorem B12271931 : Blo 678312 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B3261383 : Blo 678312 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B1721999 : Blo 678312 1721999 := bstep (se 1 (by rfl) ⟨1291499, by rfl⟩ : syracuseStep 1721999 = 2582999) B2582999
theorem B1527515 : Blo 678312 1527515 := bstep (se 1 (by rfl) ⟨1145636, by rfl⟩ : syracuseStep 1527515 = 2291273) B2291273
theorem B2906387 : Blo 678312 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B679679 : Blo 678312 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B1532015 : Blo 678312 1532015 := bstep (se 1 (by rfl) ⟨1149011, by rfl⟩ : syracuseStep 1532015 = 2298023) B2298023
theorem B1532879 : Blo 678312 1532879 := bstep (se 1 (by rfl) ⟨1149659, by rfl⟩ : syracuseStep 1532879 = 2299319) B2299319
theorem B2582057 : Blo 678312 2582057 := bstep (se 2 (by rfl) ⟨968271, by rfl⟩ : syracuseStep 2582057 = 1936543) B1936543
theorem B2452295 : Blo 678312 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B14676137 : Blo 678312 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B103675783 : Blo 678312 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B3439097 : Blo 678312 3439097 := bstep (se 2 (by rfl) ⟨1289661, by rfl⟩ : syracuseStep 3439097 = 2579323) B2579323
theorem B3439259 : Blo 678312 3439259 := bstep (se 1 (by rfl) ⟨2579444, by rfl⟩ : syracuseStep 3439259 = 5158889) B5158889
theorem B9829471 : Blo 678312 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B2294567 : Blo 678312 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B1147999 : Blo 678312 1147999 := bstep (se 1 (by rfl) ⟨860999, by rfl⟩ : syracuseStep 1147999 = 1721999) B1721999
theorem B1018343 : Blo 678312 1018343 := bstep (se 1 (by rfl) ⟨763757, by rfl⟩ : syracuseStep 1018343 = 1527515) B1527515
theorem B56724461 : Blo 678312 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B1937591 : Blo 678312 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B1021343 : Blo 678312 1021343 := bstep (se 1 (by rfl) ⟨766007, by rfl⟩ : syracuseStep 1021343 = 1532015) B1532015
theorem B1021919 : Blo 678312 1021919 := bstep (se 1 (by rfl) ⟨766439, by rfl⟩ : syracuseStep 1021919 = 1532879) B1532879
theorem B3677015 : Blo 678312 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B860159 : Blo 678312 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B3679415 : Blo 678312 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B2174255 : Blo 678312 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B19574743 : Blo 678312 19574743 := bstep (se 1 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 19574743 = 29362115) B29362115
theorem B4962799 : Blo 678312 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B1721371 : Blo 678312 1721371 := bstep (se 1 (by rfl) ⟨1291028, by rfl⟩ : syracuseStep 1721371 = 2582057) B2582057
theorem B138234377 : Blo 678312 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B9784091 : Blo 678312 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B5229527 : Blo 678312 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B11062439 : Blo 678312 11062439 := bstep (se 1 (by rfl) ⟨8296829, by rfl⟩ : syracuseStep 11062439 = 16593659) B16593659
theorem B4902889 : Blo 678312 4902889 := bstep (se 2 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 4902889 = 3677167) B3677167
theorem B5165693 : Blo 678312 5165693 := bstep (se 3 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 5165693 = 1937135) B1937135
theorem B1725097 : Blo 678312 1725097 := bstep (se 2 (by rfl) ⟨646911, by rfl⟩ : syracuseStep 1725097 = 1293823) B1293823
theorem B8181287 : Blo 678312 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B679471 : Blo 678312 679471 := bstep (se 1 (by rfl) ⟨509603, by rfl⟩ : syracuseStep 679471 = 1019207) B1019207
theorem B2647007 : Blo 678312 2647007 := bstep (se 1 (by rfl) ⟨1985255, by rfl⟩ : syracuseStep 2647007 = 3970511) B3970511
theorem B2451559 : Blo 678312 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B1634863 : Blo 678312 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B1931759 : Blo 678312 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B13105961 : Blo 678312 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B2292731 : Blo 678312 2292731 := bstep (se 1 (by rfl) ⟨1719548, by rfl⟩ : syracuseStep 2292731 = 3439097) B3439097
theorem B2292839 : Blo 678312 2292839 := bstep (se 1 (by rfl) ⟨1719629, by rfl⟩ : syracuseStep 2292839 = 3439259) B3439259
theorem B2295161 : Blo 678312 2295161 := bstep (se 2 (by rfl) ⟨860685, by rfl⟩ : syracuseStep 2295161 = 1721371) B1721371
theorem B6522727 : Blo 678312 6522727 := bstep (se 1 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 6522727 = 9784091) B9784091
theorem B37816307 : Blo 678312 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B7374959 : Blo 678312 7374959 := bstep (se 1 (by rfl) ⟨5531219, by rfl⟩ : syracuseStep 7374959 = 11062439) B11062439
theorem B3443795 : Blo 678312 3443795 := bstep (se 1 (by rfl) ⟨2582846, by rfl⟩ : syracuseStep 3443795 = 5165693) B5165693
theorem B2300129 : Blo 678312 2300129 := bstep (se 2 (by rfl) ⟨862548, by rfl⟩ : syracuseStep 2300129 = 1725097) B1725097
theorem B1449503 : Blo 678312 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B1287839 : Blo 678312 1287839 := bstep (se 1 (by rfl) ⟨965879, by rfl⟩ : syracuseStep 1287839 = 1931759) B1931759
theorem B92156251 : Blo 678312 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B1291727 : Blo 678312 1291727 := bstep (se 1 (by rfl) ⟨968795, by rfl⟩ : syracuseStep 1291727 = 1937591) B1937591
theorem B5454191 : Blo 678312 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B26099657 : Blo 678312 26099657 := bstep (se 2 (by rfl) ⟨9787371, by rfl⟩ : syracuseStep 26099657 = 19574743) B19574743
theorem B6537185 : Blo 678312 6537185 := bstep (se 2 (by rfl) ⟨2451444, by rfl⟩ : syracuseStep 6537185 = 4902889) B4902889
theorem B2179817 : Blo 678312 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B13945405 : Blo 678312 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B8737307 : Blo 678312 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B1528487 : Blo 678312 1528487 := bstep (se 1 (by rfl) ⟨1146365, by rfl⟩ : syracuseStep 1528487 = 2292731) B2292731
theorem B1528559 : Blo 678312 1528559 := bstep (se 1 (by rfl) ⟨1146419, by rfl⟩ : syracuseStep 1528559 = 2292839) B2292839
theorem B1529711 : Blo 678312 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B1530665 : Blo 678312 1530665 := bstep (se 2 (by rfl) ⟨573999, by rfl⟩ : syracuseStep 1530665 = 1147999) B1147999
theorem B678895 : Blo 678312 678895 := bstep (se 1 (by rfl) ⟨509171, by rfl⟩ : syracuseStep 678895 = 1018343) B1018343
theorem B3268745 : Blo 678312 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B680895 : Blo 678312 680895 := bstep (se 1 (by rfl) ⟨510671, by rfl⟩ : syracuseStep 680895 = 1021343) B1021343
theorem B681279 : Blo 678312 681279 := bstep (se 1 (by rfl) ⟨510959, by rfl⟩ : syracuseStep 681279 = 1021919) B1021919
theorem B2451343 : Blo 678312 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B1764671 : Blo 678312 1764671 := bstep (se 1 (by rfl) ⟨1323503, by rfl⟩ : syracuseStep 1764671 = 2647007) B2647007
theorem B2452943 : Blo 678312 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B6617065 : Blo 678312 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B2293757 : Blo 678312 2293757 := bstep (se 3 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 2293757 = 860159) B860159
theorem B4916639 : Blo 678312 4916639 := bstep (se 1 (by rfl) ⟨3687479, by rfl⟩ : syracuseStep 4916639 = 7374959) B7374959
theorem B2295863 : Blo 678312 2295863 := bstep (se 1 (by rfl) ⟨1721897, by rfl⟩ : syracuseStep 2295863 = 3443795) B3443795
theorem B1018991 : Blo 678312 1018991 := bstep (se 1 (by rfl) ⟨764243, by rfl⟩ : syracuseStep 1018991 = 1528487) B1528487
theorem B1019039 : Blo 678312 1019039 := bstep (se 1 (by rfl) ⟨764279, by rfl⟩ : syracuseStep 1019039 = 1528559) B1528559
theorem B3444605 : Blo 678312 3444605 := bstep (se 3 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 3444605 = 1291727) B1291727
theorem B1019807 : Blo 678312 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B1020443 : Blo 678312 1020443 := bstep (se 1 (by rfl) ⟨765332, by rfl⟩ : syracuseStep 1020443 = 1530665) B1530665
theorem B8822753 : Blo 678312 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B1453211 : Blo 678312 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B25210871 : Blo 678312 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B8696969 : Blo 678312 8696969 := bstep (se 2 (by rfl) ⟨3261363, by rfl⟩ : syracuseStep 8696969 = 6522727) B6522727
theorem B18593873 : Blo 678312 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B966335 : Blo 678312 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B2179163 : Blo 678312 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B4705789 : Blo 678312 4705789 := bstep (se 3 (by rfl) ⟨882335, by rfl⟩ : syracuseStep 4705789 = 1764671) B1764671
theorem B6541181 : Blo 678312 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B1529171 : Blo 678312 1529171 := bstep (se 1 (by rfl) ⟨1146878, by rfl⟩ : syracuseStep 1529171 = 2293757) B2293757
theorem B1530107 : Blo 678312 1530107 := bstep (se 1 (by rfl) ⟨1147580, by rfl⟩ : syracuseStep 1530107 = 2295161) B2295161
theorem B3268457 : Blo 678312 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B5824871 : Blo 678312 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B1533419 : Blo 678312 1533419 := bstep (se 1 (by rfl) ⟨1150064, by rfl⟩ : syracuseStep 1533419 = 2300129) B2300129
theorem B3434237 : Blo 678312 3434237 := bstep (se 3 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 3434237 = 1287839) B1287839
theorem B122875001 : Blo 678312 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B3636127 : Blo 678312 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B17399771 : Blo 678312 17399771 := bstep (se 1 (by rfl) ⟨13049828, by rfl⟩ : syracuseStep 17399771 = 26099657) B26099657
theorem B4358123 : Blo 678312 4358123 := bstep (se 1 (by rfl) ⟨3268592, by rfl⟩ : syracuseStep 4358123 = 6537185) B6537185
theorem B3277759 : Blo 678312 3277759 := bstep (se 1 (by rfl) ⟨2458319, by rfl⟩ : syracuseStep 3277759 = 4916639) B4916639
theorem B2296403 : Blo 678312 2296403 := bstep (se 1 (by rfl) ⟨1722302, by rfl⟩ : syracuseStep 2296403 = 3444605) B3444605
theorem B4360787 : Blo 678312 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B1019447 : Blo 678312 1019447 := bstep (se 1 (by rfl) ⟨764585, by rfl⟩ : syracuseStep 1019447 = 1529171) B1529171
theorem B1020071 : Blo 678312 1020071 := bstep (se 1 (by rfl) ⟨765053, by rfl⟩ : syracuseStep 1020071 = 1530107) B1530107
theorem B1022279 : Blo 678312 1022279 := bstep (se 1 (by rfl) ⟨766709, by rfl⟩ : syracuseStep 1022279 = 1533419) B1533419
theorem B12395915 : Blo 678312 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B5811101 : Blo 678312 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B6274385 : Blo 678312 6274385 := bstep (se 2 (by rfl) ⟨2352894, by rfl⟩ : syracuseStep 6274385 = 4705789) B4705789
theorem B2178971 : Blo 678312 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B5881835 : Blo 678312 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B3883247 : Blo 678312 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B968807 : Blo 678312 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B2576893 : Blo 678312 2576893 := bstep (se 3 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 2576893 = 966335) B966335
theorem B2905415 : Blo 678312 2905415 := bstep (se 1 (by rfl) ⟨2179061, by rfl⟩ : syracuseStep 2905415 = 4358123) B4358123
theorem B1530575 : Blo 678312 1530575 := bstep (se 1 (by rfl) ⟨1147931, by rfl⟩ : syracuseStep 1530575 = 2295863) B2295863
theorem B679327 : Blo 678312 679327 := bstep (se 1 (by rfl) ⟨509495, by rfl⟩ : syracuseStep 679327 = 1018991) B1018991
theorem B679359 : Blo 678312 679359 := bstep (se 1 (by rfl) ⟨509519, by rfl⟩ : syracuseStep 679359 = 1019039) B1019039
theorem B679871 : Blo 678312 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B680295 : Blo 678312 680295 := bstep (se 1 (by rfl) ⟨510221, by rfl⟩ : syracuseStep 680295 = 1020443) B1020443
theorem B2289491 : Blo 678312 2289491 := bstep (se 1 (by rfl) ⟨1717118, by rfl⟩ : syracuseStep 2289491 = 3434237) B3434237
theorem B81916667 : Blo 678312 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B16807247 : Blo 678312 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B5797979 : Blo 678312 5797979 := bstep (se 1 (by rfl) ⟨4348484, by rfl⟩ : syracuseStep 5797979 = 8696969) B8696969
theorem B4848169 : Blo 678312 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B11599847 : Blo 678312 11599847 := bstep (se 1 (by rfl) ⟨8699885, by rfl⟩ : syracuseStep 11599847 = 17399771) B17399771
theorem B2588831 : Blo 678312 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B1936943 : Blo 678312 1936943 := bstep (se 1 (by rfl) ⟨1452707, by rfl⟩ : syracuseStep 1936943 = 2905415) B2905415
theorem B1020383 : Blo 678312 1020383 := bstep (se 1 (by rfl) ⟨765287, by rfl⟩ : syracuseStep 1020383 = 1530575) B1530575
theorem B8263943 : Blo 678312 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B3874067 : Blo 678312 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B6464225 : Blo 678312 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B1452647 : Blo 678312 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B4370345 : Blo 678312 4370345 := bstep (se 2 (by rfl) ⟨1638879, by rfl⟩ : syracuseStep 4370345 = 3277759) B3277759
theorem B1526327 : Blo 678312 1526327 := bstep (se 1 (by rfl) ⟨1144745, by rfl⟩ : syracuseStep 1526327 = 2289491) B2289491
theorem B54611111 : Blo 678312 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B4182923 : Blo 678312 4182923 := bstep (se 1 (by rfl) ⟨3137192, by rfl⟩ : syracuseStep 4182923 = 6274385) B6274385
theorem B3921223 : Blo 678312 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B1530935 : Blo 678312 1530935 := bstep (se 1 (by rfl) ⟨1148201, by rfl⟩ : syracuseStep 1530935 = 2296403) B2296403
theorem B2907191 : Blo 678312 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B679631 : Blo 678312 679631 := bstep (se 1 (by rfl) ⟨509723, by rfl⟩ : syracuseStep 679631 = 1019447) B1019447
theorem B680047 : Blo 678312 680047 := bstep (se 1 (by rfl) ⟨510035, by rfl⟩ : syracuseStep 680047 = 1020071) B1020071
theorem B681519 : Blo 678312 681519 := bstep (se 1 (by rfl) ⟨511139, by rfl⟩ : syracuseStep 681519 = 1022279) B1022279
theorem B2583485 : Blo 678312 2583485 := bstep (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) B968807
theorem B3435857 : Blo 678312 3435857 := bstep (se 2 (by rfl) ⟨1288446, by rfl⟩ : syracuseStep 3435857 = 2576893) B2576893
theorem B11204831 : Blo 678312 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B3865319 : Blo 678312 3865319 := bstep (se 1 (by rfl) ⟨2898989, by rfl⟩ : syracuseStep 3865319 = 5797979) B5797979
theorem B7733231 : Blo 678312 7733231 := bstep (se 1 (by rfl) ⟨5799923, by rfl⟩ : syracuseStep 7733231 = 11599847) B11599847
theorem B1017551 : Blo 678312 1017551 := bstep (se 1 (by rfl) ⟨763163, by rfl⟩ : syracuseStep 1017551 = 1526327) B1526327
theorem B17237933 : Blo 678312 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B36407407 : Blo 678312 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B2788615 : Blo 678312 2788615 := bstep (se 1 (by rfl) ⟨2091461, by rfl⟩ : syracuseStep 2788615 = 4182923) B4182923
theorem B5509295 : Blo 678312 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B1020623 : Blo 678312 1020623 := bstep (se 1 (by rfl) ⟨765467, by rfl⟩ : syracuseStep 1020623 = 1530935) B1530935
theorem B1938127 : Blo 678312 1938127 := bstep (se 1 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 1938127 = 2907191) B2907191
theorem B5155487 : Blo 678312 5155487 := bstep (se 1 (by rfl) ⟨3866615, by rfl⟩ : syracuseStep 5155487 = 7733231) B7733231
theorem B1291295 : Blo 678312 1291295 := bstep (se 1 (by rfl) ⟨968471, by rfl⟩ : syracuseStep 1291295 = 1936943) B1936943
theorem B968431 : Blo 678312 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B5228297 : Blo 678312 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B1722323 : Blo 678312 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B2576879 : Blo 678312 2576879 := bstep (se 1 (by rfl) ⟨1932659, by rfl⟩ : syracuseStep 2576879 = 3865319) B3865319
theorem B1725887 : Blo 678312 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B680255 : Blo 678312 680255 := bstep (se 1 (by rfl) ⟨510191, by rfl⟩ : syracuseStep 680255 = 1020383) B1020383
theorem B2582711 : Blo 678312 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B2290571 : Blo 678312 2290571 := bstep (se 1 (by rfl) ⟨1717928, by rfl⟩ : syracuseStep 2290571 = 3435857) B3435857
theorem B2913563 : Blo 678312 2913563 := bstep (se 1 (by rfl) ⟨2185172, by rfl⟩ : syracuseStep 2913563 = 4370345) B4370345
theorem B7469887 : Blo 678312 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B1148215 : Blo 678312 1148215 := bstep (se 1 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 1148215 = 1722323) B1722323
theorem B3672863 : Blo 678312 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B1150591 : Blo 678312 1150591 := bstep (se 1 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 1150591 = 1725887) B1725887
theorem B860863 : Blo 678312 860863 := bstep (se 1 (by rfl) ⟨645647, by rfl⟩ : syracuseStep 860863 = 1291295) B1291295
theorem B1942375 : Blo 678312 1942375 := bstep (se 1 (by rfl) ⟨1456781, by rfl⟩ : syracuseStep 1942375 = 2913563) B2913563
theorem B3485531 : Blo 678312 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B1291241 : Blo 678312 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B48543209 : Blo 678312 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B1717919 : Blo 678312 1717919 := bstep (se 1 (by rfl) ⟨1288439, by rfl⟩ : syracuseStep 1717919 = 2576879) B2576879
theorem B3718153 : Blo 678312 3718153 := bstep (se 2 (by rfl) ⟨1394307, by rfl⟩ : syracuseStep 3718153 = 2788615) B2788615
theorem B1721807 : Blo 678312 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B1527047 : Blo 678312 1527047 := bstep (se 1 (by rfl) ⟨1145285, by rfl⟩ : syracuseStep 1527047 = 2290571) B2290571
theorem B678367 : Blo 678312 678367 := bstep (se 1 (by rfl) ⟨508775, by rfl⟩ : syracuseStep 678367 = 1017551) B1017551
theorem B11491955 : Blo 678312 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B680415 : Blo 678312 680415 := bstep (se 1 (by rfl) ⟨510311, by rfl⟩ : syracuseStep 680415 = 1020623) B1020623
theorem B2584169 : Blo 678312 2584169 := bstep (se 2 (by rfl) ⟨969063, by rfl⟩ : syracuseStep 2584169 = 1938127) B1938127
theorem B3436991 : Blo 678312 3436991 := bstep (se 1 (by rfl) ⟨2577743, by rfl⟩ : syracuseStep 3436991 = 5155487) B5155487
theorem B9959849 : Blo 678312 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B1147817 : Blo 678312 1147817 := bstep (se 2 (by rfl) ⟨430431, by rfl⟩ : syracuseStep 1147817 = 860863) B860863
theorem B1147871 : Blo 678312 1147871 := bstep (se 1 (by rfl) ⟨860903, by rfl⟩ : syracuseStep 1147871 = 1721807) B1721807
theorem B2589833 : Blo 678312 2589833 := bstep (se 2 (by rfl) ⟨971187, by rfl⟩ : syracuseStep 2589833 = 1942375) B1942375
theorem B1018031 : Blo 678312 1018031 := bstep (se 1 (by rfl) ⟨763523, by rfl⟩ : syracuseStep 1018031 = 1527047) B1527047
theorem B3443309 : Blo 678312 3443309 := bstep (se 3 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 3443309 = 1291241) B1291241
theorem B4957537 : Blo 678312 4957537 := bstep (se 2 (by rfl) ⟨1859076, by rfl⟩ : syracuseStep 4957537 = 3718153) B3718153
theorem B1722779 : Blo 678312 1722779 := bstep (se 1 (by rfl) ⟨1292084, by rfl⟩ : syracuseStep 1722779 = 2584169) B2584169
theorem B32362139 : Blo 678312 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B6639899 : Blo 678312 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B9294749 : Blo 678312 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B1530953 : Blo 678312 1530953 := bstep (se 2 (by rfl) ⟨574107, by rfl⟩ : syracuseStep 1530953 = 1148215) B1148215
theorem B2448575 : Blo 678312 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B7661303 : Blo 678312 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B1534121 : Blo 678312 1534121 := bstep (se 2 (by rfl) ⟨575295, by rfl⟩ : syracuseStep 1534121 = 1150591) B1150591
theorem B2291327 : Blo 678312 2291327 := bstep (se 1 (by rfl) ⟨1718495, by rfl⟩ : syracuseStep 2291327 = 3436991) B3436991
theorem B1145279 : Blo 678312 1145279 := bstep (se 1 (by rfl) ⟨858959, by rfl⟩ : syracuseStep 1145279 = 1717919) B1717919
theorem B1148519 : Blo 678312 1148519 := bstep (se 1 (by rfl) ⟨861389, by rfl⟩ : syracuseStep 1148519 = 1722779) B1722779
theorem B2295539 : Blo 678312 2295539 := bstep (se 1 (by rfl) ⟨1721654, by rfl⟩ : syracuseStep 2295539 = 3443309) B3443309
theorem B6196499 : Blo 678312 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B1020635 : Blo 678312 1020635 := bstep (se 1 (by rfl) ⟨765476, by rfl⟩ : syracuseStep 1020635 = 1530953) B1530953
theorem B1022747 : Blo 678312 1022747 := bstep (se 1 (by rfl) ⟨767060, by rfl⟩ : syracuseStep 1022747 = 1534121) B1534121
theorem B763519 : Blo 678312 763519 := bstep (se 1 (by rfl) ⟨572639, by rfl⟩ : syracuseStep 763519 = 1145279) B1145279
theorem B765211 : Blo 678312 765211 := bstep (se 1 (by rfl) ⟨573908, by rfl⟩ : syracuseStep 765211 = 1147817) B1147817
theorem B765247 : Blo 678312 765247 := bstep (se 1 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 765247 = 1147871) B1147871
theorem B17706397 : Blo 678312 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B21574759 : Blo 678312 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B1527551 : Blo 678312 1527551 := bstep (se 1 (by rfl) ⟨1145663, by rfl⟩ : syracuseStep 1527551 = 2291327) B2291327
theorem B1726555 : Blo 678312 1726555 := bstep (se 1 (by rfl) ⟨1294916, by rfl⟩ : syracuseStep 1726555 = 2589833) B2589833
theorem B678687 : Blo 678312 678687 := bstep (se 1 (by rfl) ⟨509015, by rfl⟩ : syracuseStep 678687 = 1018031) B1018031
theorem B6610049 : Blo 678312 6610049 := bstep (se 2 (by rfl) ⟨2478768, by rfl⟩ : syracuseStep 6610049 = 4957537) B4957537
theorem B1632383 : Blo 678312 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B5107535 : Blo 678312 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B1018025 : Blo 678312 1018025 := bstep (se 2 (by rfl) ⟨381759, by rfl⟩ : syracuseStep 1018025 = 763519) B763519
theorem B4130999 : Blo 678312 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B1018367 : Blo 678312 1018367 := bstep (se 1 (by rfl) ⟨763775, by rfl⟩ : syracuseStep 1018367 = 1527551) B1527551
theorem B1020281 : Blo 678312 1020281 := bstep (se 2 (by rfl) ⟨382605, by rfl⟩ : syracuseStep 1020281 = 765211) B765211
theorem B1020329 : Blo 678312 1020329 := bstep (se 2 (by rfl) ⟨382623, by rfl⟩ : syracuseStep 1020329 = 765247) B765247
theorem B1088255 : Blo 678312 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B2302073 : Blo 678312 2302073 := bstep (se 2 (by rfl) ⟨863277, by rfl⟩ : syracuseStep 2302073 = 1726555) B1726555
theorem B765679 : Blo 678312 765679 := bstep (se 1 (by rfl) ⟨574259, by rfl⟩ : syracuseStep 765679 = 1148519) B1148519
theorem B23608529 : Blo 678312 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B4406699 : Blo 678312 4406699 := bstep (se 1 (by rfl) ⟨3305024, by rfl⟩ : syracuseStep 4406699 = 6610049) B6610049
theorem B1530359 : Blo 678312 1530359 := bstep (se 1 (by rfl) ⟨1147769, by rfl⟩ : syracuseStep 1530359 = 2295539) B2295539
theorem B680423 : Blo 678312 680423 := bstep (se 1 (by rfl) ⟨510317, by rfl⟩ : syracuseStep 680423 = 1020635) B1020635
theorem B681831 : Blo 678312 681831 := bstep (se 1 (by rfl) ⟨511373, by rfl⟩ : syracuseStep 681831 = 1022747) B1022747
theorem B28766345 : Blo 678312 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B3405023 : Blo 678312 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B76710253 : Blo 678312 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B2753999 : Blo 678312 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B1020239 : Blo 678312 1020239 := bstep (se 1 (by rfl) ⟨765179, by rfl⟩ : syracuseStep 1020239 = 1530359) B1530359
theorem B1020905 : Blo 678312 1020905 := bstep (se 2 (by rfl) ⟨382839, by rfl⟩ : syracuseStep 1020905 = 765679) B765679
theorem B2270015 : Blo 678312 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B15739019 : Blo 678312 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B2902013 : Blo 678312 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B2937799 : Blo 678312 2937799 := bstep (se 1 (by rfl) ⟨2203349, by rfl⟩ : syracuseStep 2937799 = 4406699) B4406699
theorem B678683 : Blo 678312 678683 := bstep (se 1 (by rfl) ⟨509012, by rfl⟩ : syracuseStep 678683 = 1018025) B1018025
theorem B678911 : Blo 678312 678911 := bstep (se 1 (by rfl) ⟨509183, by rfl⟩ : syracuseStep 678911 = 1018367) B1018367
theorem B680187 : Blo 678312 680187 := bstep (se 1 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 680187 = 1020281) B1020281
theorem B680219 : Blo 678312 680219 := bstep (se 1 (by rfl) ⟨510164, by rfl⟩ : syracuseStep 680219 = 1020329) B1020329
theorem B1534715 : Blo 678312 1534715 := bstep (se 1 (by rfl) ⟨1151036, by rfl⟩ : syracuseStep 1534715 = 2302073) B2302073
theorem B1835999 : Blo 678312 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B1934675 : Blo 678312 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B15668261 : Blo 678312 15668261 := bstep (se 4 (by rfl) ⟨1468899, by rfl⟩ : syracuseStep 15668261 = 2937799) B2937799
theorem B1513343 : Blo 678312 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B10492679 : Blo 678312 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B1023143 : Blo 678312 1023143 := bstep (se 1 (by rfl) ⟨767357, by rfl⟩ : syracuseStep 1023143 = 1534715) B1534715
theorem B102280337 : Blo 678312 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B680159 : Blo 678312 680159 := bstep (se 1 (by rfl) ⟨510119, by rfl⟩ : syracuseStep 680159 = 1020239) B1020239
theorem B680603 : Blo 678312 680603 := bstep (se 1 (by rfl) ⟨510452, by rfl⟩ : syracuseStep 680603 = 1020905) B1020905
theorem B4035581 : Blo 678312 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B1223999 : Blo 678312 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B1289783 : Blo 678312 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B6995119 : Blo 678312 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B10445507 : Blo 678312 10445507 := bstep (se 1 (by rfl) ⟨7834130, by rfl⟩ : syracuseStep 10445507 = 15668261) B15668261
theorem B682095 : Blo 678312 682095 := bstep (se 1 (by rfl) ⟨511571, by rfl⟩ : syracuseStep 682095 = 1023143) B1023143
theorem B68186891 : Blo 678312 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B181831709 : Blo 678312 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B2690387 : Blo 678312 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B6963671 : Blo 678312 6963671 := bstep (se 1 (by rfl) ⟨5222753, by rfl⟩ : syracuseStep 6963671 = 10445507) B10445507
theorem B9326825 : Blo 678312 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B815999 : Blo 678312 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B3439421 : Blo 678312 3439421 := bstep (se 3 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 3439421 = 1289783) B1289783
theorem B121221139 : Blo 678312 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B2175997 : Blo 678312 2175997 := bstep (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) B815999
theorem B4642447 : Blo 678312 4642447 := bstep (se 1 (by rfl) ⟨3481835, by rfl⟩ : syracuseStep 4642447 = 6963671) B6963671
theorem B1793591 : Blo 678312 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B6217883 : Blo 678312 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B2292947 : Blo 678312 2292947 := bstep (se 1 (by rfl) ⟨1719710, by rfl⟩ : syracuseStep 2292947 = 3439421) B3439421
theorem B1195727 : Blo 678312 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B161628185 : Blo 678312 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B4145255 : Blo 678312 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B2901329 : Blo 678312 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1528631 : Blo 678312 1528631 := bstep (se 1 (by rfl) ⟨1146473, by rfl⟩ : syracuseStep 1528631 = 2292947) B2292947
theorem B6189929 : Blo 678312 6189929 := bstep (se 2 (by rfl) ⟨2321223, by rfl⟩ : syracuseStep 6189929 = 4642447) B4642447
theorem B1934219 : Blo 678312 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B1019087 : Blo 678312 1019087 := bstep (se 1 (by rfl) ⟨764315, by rfl⟩ : syracuseStep 1019087 = 1528631) B1528631
theorem B3188605 : Blo 678312 3188605 := bstep (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) B1195727
theorem B107752123 : Blo 678312 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B2763503 : Blo 678312 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B4126619 : Blo 678312 4126619 := bstep (se 1 (by rfl) ⟨3094964, by rfl⟩ : syracuseStep 4126619 = 6189929) B6189929
theorem B1842335 : Blo 678312 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B5157917 : Blo 678312 5157917 := bstep (se 3 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 5157917 = 1934219) B1934219
theorem B143669497 : Blo 678312 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B679391 : Blo 678312 679391 := bstep (se 1 (by rfl) ⟨509543, by rfl⟩ : syracuseStep 679391 = 1019087) B1019087
theorem B4251473 : Blo 678312 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B2751079 : Blo 678312 2751079 := bstep (se 1 (by rfl) ⟨2063309, by rfl⟩ : syracuseStep 2751079 = 4126619) B4126619
theorem B1228223 : Blo 678312 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B2834315 : Blo 678312 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B191559329 : Blo 678312 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B3438611 : Blo 678312 3438611 := bstep (se 1 (by rfl) ⟨2578958, by rfl⟩ : syracuseStep 3438611 = 5157917) B5157917
theorem B3668105 : Blo 678312 3668105 := bstep (se 2 (by rfl) ⟨1375539, by rfl⟩ : syracuseStep 3668105 = 2751079) B2751079
theorem B127706219 : Blo 678312 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B2445403 : Blo 678312 2445403 := bstep (se 1 (by rfl) ⟨1834052, by rfl⟩ : syracuseStep 2445403 = 3668105) B3668105
theorem B1889543 : Blo 678312 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B3275261 : Blo 678312 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B2292407 : Blo 678312 2292407 := bstep (se 1 (by rfl) ⟨1719305, by rfl⟩ : syracuseStep 2292407 = 3438611) B3438611
theorem B85137479 : Blo 678312 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B1259695 : Blo 678312 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B3260537 : Blo 678312 3260537 := bstep (se 2 (by rfl) ⟨1222701, by rfl⟩ : syracuseStep 3260537 = 2445403) B2445403
theorem B2183507 : Blo 678312 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B1528271 : Blo 678312 1528271 := bstep (se 1 (by rfl) ⟨1146203, by rfl⟩ : syracuseStep 1528271 = 2292407) B2292407
theorem B6718373 : Blo 678312 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B1018847 : Blo 678312 1018847 := bstep (se 1 (by rfl) ⟨764135, by rfl⟩ : syracuseStep 1018847 = 1528271) B1528271
theorem B56758319 : Blo 678312 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B2173691 : Blo 678312 2173691 := bstep (se 1 (by rfl) ⟨1630268, by rfl⟩ : syracuseStep 2173691 = 3260537) B3260537
theorem B1455671 : Blo 678312 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B1449127 : Blo 678312 1449127 := bstep (se 1 (by rfl) ⟨1086845, by rfl⟩ : syracuseStep 1449127 = 2173691) B2173691
theorem B3881789 : Blo 678312 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B4478915 : Blo 678312 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B679231 : Blo 678312 679231 := bstep (se 1 (by rfl) ⟨509423, by rfl⟩ : syracuseStep 679231 = 1018847) B1018847
theorem B37838879 : Blo 678312 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B11943773 : Blo 678312 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B25225919 : Blo 678312 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B1932169 : Blo 678312 1932169 := bstep (se 2 (by rfl) ⟨724563, by rfl⟩ : syracuseStep 1932169 = 1449127) B1449127
theorem B2587859 : Blo 678312 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B16817279 : Blo 678312 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B2576225 : Blo 678312 2576225 := bstep (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) B1932169
theorem B1725239 : Blo 678312 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B7962515 : Blo 678312 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B1150159 : Blo 678312 1150159 := bstep (se 1 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 1150159 = 1725239) B1725239
theorem B1717483 : Blo 678312 1717483 := bstep (se 1 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 1717483 = 2576225) B2576225
theorem B44846077 : Blo 678312 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B5308343 : Blo 678312 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B59794769 : Blo 678312 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B1533545 : Blo 678312 1533545 := bstep (se 2 (by rfl) ⟨575079, by rfl⟩ : syracuseStep 1533545 = 1150159) B1150159
theorem B2289977 : Blo 678312 2289977 := bstep (se 2 (by rfl) ⟨858741, by rfl⟩ : syracuseStep 2289977 = 1717483) B1717483
theorem B3538895 : Blo 678312 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B1022363 : Blo 678312 1022363 := bstep (se 1 (by rfl) ⟨766772, by rfl⟩ : syracuseStep 1022363 = 1533545) B1533545
theorem B39863179 : Blo 678312 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B1526651 : Blo 678312 1526651 := bstep (se 1 (by rfl) ⟨1144988, by rfl⟩ : syracuseStep 1526651 = 2289977) B2289977
theorem B37748213 : Blo 678312 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B53150905 : Blo 678312 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B1017767 : Blo 678312 1017767 := bstep (se 1 (by rfl) ⟨763325, by rfl⟩ : syracuseStep 1017767 = 1526651) B1526651
theorem B681575 : Blo 678312 681575 := bstep (se 1 (by rfl) ⟨511181, by rfl⟩ : syracuseStep 681575 = 1022363) B1022363
theorem B25165475 : Blo 678312 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B678511 : Blo 678312 678511 := bstep (se 1 (by rfl) ⟨508883, by rfl⟩ : syracuseStep 678511 = 1017767) B1017767
theorem B70867873 : Blo 678312 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B16776983 : Blo 678312 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B11184655 : Blo 678312 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B94490497 : Blo 678312 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B14912873 : Blo 678312 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B125987329 : Blo 678312 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B9941915 : Blo 678312 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B167983105 : Blo 678312 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 678312 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B6627943 : Blo 678312 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B8837257 : Blo 678312 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B149318315 : Blo 678312 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B11783009 : Blo 678312 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B99545543 : Blo 678312 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 678312 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B7855339 : Blo 678312 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B44242463 : Blo 678312 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B10473785 : Blo 678312 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B6982523 : Blo 678312 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B29494975 : Blo 678312 29494975 := bstep (se 1 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 29494975 = 44242463) B44242463
theorem B4655015 : Blo 678312 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B39326633 : Blo 678312 39326633 := bstep (se 2 (by rfl) ⟨14747487, by rfl⟩ : syracuseStep 39326633 = 29494975) B29494975
theorem B26217755 : Blo 678312 26217755 := bstep (se 1 (by rfl) ⟨19663316, by rfl⟩ : syracuseStep 26217755 = 39326633) B39326633
theorem B3103343 : Blo 678312 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B2068895 : Blo 678312 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B17478503 : Blo 678312 17478503 := bstep (se 1 (by rfl) ⟨13108877, by rfl⟩ : syracuseStep 17478503 = 26217755) B26217755
theorem B1379263 : Blo 678312 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B11652335 : Blo 678312 11652335 := bstep (se 1 (by rfl) ⟨8739251, by rfl⟩ : syracuseStep 11652335 = 17478503) B17478503
theorem B7768223 : Blo 678312 7768223 := bstep (se 1 (by rfl) ⟨5826167, by rfl⟩ : syracuseStep 7768223 = 11652335) B11652335
theorem B1839017 : Blo 678312 1839017 := bstep (se 2 (by rfl) ⟨689631, by rfl⟩ : syracuseStep 1839017 = 1379263) B1379263
theorem B5178815 : Blo 678312 5178815 := bstep (se 1 (by rfl) ⟨3884111, by rfl⟩ : syracuseStep 5178815 = 7768223) B7768223
theorem B1226011 : Blo 678312 1226011 := bstep (se 1 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 1226011 = 1839017) B1839017
theorem B3452543 : Blo 678312 3452543 := bstep (se 1 (by rfl) ⟨2589407, by rfl⟩ : syracuseStep 3452543 = 5178815) B5178815
theorem B1634681 : Blo 678312 1634681 := bstep (se 2 (by rfl) ⟨613005, by rfl⟩ : syracuseStep 1634681 = 1226011) B1226011
theorem B2301695 : Blo 678312 2301695 := bstep (se 1 (by rfl) ⟨1726271, by rfl⟩ : syracuseStep 2301695 = 3452543) B3452543
theorem B1089787 : Blo 678312 1089787 := bstep (se 1 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 1089787 = 1634681) B1634681
theorem B1453049 : Blo 678312 1453049 := bstep (se 2 (by rfl) ⟨544893, by rfl⟩ : syracuseStep 1453049 = 1089787) B1089787
theorem B1534463 : Blo 678312 1534463 := bstep (se 1 (by rfl) ⟨1150847, by rfl⟩ : syracuseStep 1534463 = 2301695) B2301695
theorem B1022975 : Blo 678312 1022975 := bstep (se 1 (by rfl) ⟨767231, by rfl⟩ : syracuseStep 1022975 = 1534463) B1534463
theorem B968699 : Blo 678312 968699 := bstep (se 1 (by rfl) ⟨726524, by rfl⟩ : syracuseStep 968699 = 1453049) B1453049
theorem B681983 : Blo 678312 681983 := bstep (se 1 (by rfl) ⟨511487, by rfl⟩ : syracuseStep 681983 = 1022975) B1022975
theorem B2583197 : Blo 678312 2583197 := bstep (se 3 (by rfl) ⟨484349, by rfl⟩ : syracuseStep 2583197 = 968699) B968699
theorem B1722131 : Blo 678312 1722131 := bstep (se 1 (by rfl) ⟨1291598, by rfl⟩ : syracuseStep 1722131 = 2583197) B2583197
theorem B1148087 : Blo 678312 1148087 := bstep (se 1 (by rfl) ⟨861065, by rfl⟩ : syracuseStep 1148087 = 1722131) B1722131
theorem B765391 : Blo 678312 765391 := bstep (se 1 (by rfl) ⟨574043, by rfl⟩ : syracuseStep 765391 = 1148087) B1148087
theorem B1020521 : Blo 678312 1020521 := bstep (se 2 (by rfl) ⟨382695, by rfl⟩ : syracuseStep 1020521 = 765391) B765391
theorem B680347 : Blo 678312 680347 := bstep (se 1 (by rfl) ⟨510260, by rfl⟩ : syracuseStep 680347 = 1020521) B1020521

theorem C0 (j : ℕ) (h1 : 169578 ≤ j) (h2 : j ≤ 170277) : Blo 678312 (4 * j + 3) := by
  interval_cases j
  · exact B678315
  · exact B678319
  · exact B678323
  · exact B678327
  · exact B678331
  · exact B678335
  · exact B678339
  · exact B678343
  · exact B678347
  · exact B678351
  · exact B678355
  · exact B678359
  · exact B678363
  · exact B678367
  · exact B678371
  · exact B678375
  · exact B678379
  · exact B678383
  · exact B678387
  · exact B678391
  · exact B678395
  · exact B678399
  · exact B678403
  · exact B678407
  · exact B678411
  · exact B678415
  · exact B678419
  · exact B678423
  · exact B678427
  · exact B678431
  · exact B678435
  · exact B678439
  · exact B678443
  · exact B678447
  · exact B678451
  · exact B678455
  · exact B678459
  · exact B678463
  · exact B678467
  · exact B678471
  · exact B678475
  · exact B678479
  · exact B678483
  · exact B678487
  · exact B678491
  · exact B678495
  · exact B678499
  · exact B678503
  · exact B678507
  · exact B678511
  · exact B678515
  · exact B678519
  · exact B678523
  · exact B678527
  · exact B678531
  · exact B678535
  · exact B678539
  · exact B678543
  · exact B678547
  · exact B678551
  · exact B678555
  · exact B678559
  · exact B678563
  · exact B678567
  · exact B678571
  · exact B678575
  · exact B678579
  · exact B678583
  · exact B678587
  · exact B678591
  · exact B678595
  · exact B678599
  · exact B678603
  · exact B678607
  · exact B678611
  · exact B678615
  · exact B678619
  · exact B678623
  · exact B678627
  · exact B678631
  · exact B678635
  · exact B678639
  · exact B678643
  · exact B678647
  · exact B678651
  · exact B678655
  · exact B678659
  · exact B678663
  · exact B678667
  · exact B678671
  · exact B678675
  · exact B678679
  · exact B678683
  · exact B678687
  · exact B678691
  · exact B678695
  · exact B678699
  · exact B678703
  · exact B678707
  · exact B678711
  · exact B678715
  · exact B678719
  · exact B678723
  · exact B678727
  · exact B678731
  · exact B678735
  · exact B678739
  · exact B678743
  · exact B678747
  · exact B678751
  · exact B678755
  · exact B678759
  · exact B678763
  · exact B678767
  · exact B678771
  · exact B678775
  · exact B678779
  · exact B678783
  · exact B678787
  · exact B678791
  · exact B678795
  · exact B678799
  · exact B678803
  · exact B678807
  · exact B678811
  · exact B678815
  · exact B678819
  · exact B678823
  · exact B678827
  · exact B678831
  · exact B678835
  · exact B678839
  · exact B678843
  · exact B678847
  · exact B678851
  · exact B678855
  · exact B678859
  · exact B678863
  · exact B678867
  · exact B678871
  · exact B678875
  · exact B678879
  · exact B678883
  · exact B678887
  · exact B678891
  · exact B678895
  · exact B678899
  · exact B678903
  · exact B678907
  · exact B678911
  · exact B678915
  · exact B678919
  · exact B678923
  · exact B678927
  · exact B678931
  · exact B678935
  · exact B678939
  · exact B678943
  · exact B678947
  · exact B678951
  · exact B678955
  · exact B678959
  · exact B678963
  · exact B678967
  · exact B678971
  · exact B678975
  · exact B678979
  · exact B678983
  · exact B678987
  · exact B678991
  · exact B678995
  · exact B678999
  · exact B679003
  · exact B679007
  · exact B679011
  · exact B679015
  · exact B679019
  · exact B679023
  · exact B679027
  · exact B679031
  · exact B679035
  · exact B679039
  · exact B679043
  · exact B679047
  · exact B679051
  · exact B679055
  · exact B679059
  · exact B679063
  · exact B679067
  · exact B679071
  · exact B679075
  · exact B679079
  · exact B679083
  · exact B679087
  · exact B679091
  · exact B679095
  · exact B679099
  · exact B679103
  · exact B679107
  · exact B679111
  · exact B679115
  · exact B679119
  · exact B679123
  · exact B679127
  · exact B679131
  · exact B679135
  · exact B679139
  · exact B679143
  · exact B679147
  · exact B679151
  · exact B679155
  · exact B679159
  · exact B679163
  · exact B679167
  · exact B679171
  · exact B679175
  · exact B679179
  · exact B679183
  · exact B679187
  · exact B679191
  · exact B679195
  · exact B679199
  · exact B679203
  · exact B679207
  · exact B679211
  · exact B679215
  · exact B679219
  · exact B679223
  · exact B679227
  · exact B679231
  · exact B679235
  · exact B679239
  · exact B679243
  · exact B679247
  · exact B679251
  · exact B679255
  · exact B679259
  · exact B679263
  · exact B679267
  · exact B679271
  · exact B679275
  · exact B679279
  · exact B679283
  · exact B679287
  · exact B679291
  · exact B679295
  · exact B679299
  · exact B679303
  · exact B679307
  · exact B679311
  · exact B679315
  · exact B679319
  · exact B679323
  · exact B679327
  · exact B679331
  · exact B679335
  · exact B679339
  · exact B679343
  · exact B679347
  · exact B679351
  · exact B679355
  · exact B679359
  · exact B679363
  · exact B679367
  · exact B679371
  · exact B679375
  · exact B679379
  · exact B679383
  · exact B679387
  · exact B679391
  · exact B679395
  · exact B679399
  · exact B679403
  · exact B679407
  · exact B679411
  · exact B679415
  · exact B679419
  · exact B679423
  · exact B679427
  · exact B679431
  · exact B679435
  · exact B679439
  · exact B679443
  · exact B679447
  · exact B679451
  · exact B679455
  · exact B679459
  · exact B679463
  · exact B679467
  · exact B679471
  · exact B679475
  · exact B679479
  · exact B679483
  · exact B679487
  · exact B679491
  · exact B679495
  · exact B679499
  · exact B679503
  · exact B679507
  · exact B679511
  · exact B679515
  · exact B679519
  · exact B679523
  · exact B679527
  · exact B679531
  · exact B679535
  · exact B679539
  · exact B679543
  · exact B679547
  · exact B679551
  · exact B679555
  · exact B679559
  · exact B679563
  · exact B679567
  · exact B679571
  · exact B679575
  · exact B679579
  · exact B679583
  · exact B679587
  · exact B679591
  · exact B679595
  · exact B679599
  · exact B679603
  · exact B679607
  · exact B679611
  · exact B679615
  · exact B679619
  · exact B679623
  · exact B679627
  · exact B679631
  · exact B679635
  · exact B679639
  · exact B679643
  · exact B679647
  · exact B679651
  · exact B679655
  · exact B679659
  · exact B679663
  · exact B679667
  · exact B679671
  · exact B679675
  · exact B679679
  · exact B679683
  · exact B679687
  · exact B679691
  · exact B679695
  · exact B679699
  · exact B679703
  · exact B679707
  · exact B679711
  · exact B679715
  · exact B679719
  · exact B679723
  · exact B679727
  · exact B679731
  · exact B679735
  · exact B679739
  · exact B679743
  · exact B679747
  · exact B679751
  · exact B679755
  · exact B679759
  · exact B679763
  · exact B679767
  · exact B679771
  · exact B679775
  · exact B679779
  · exact B679783
  · exact B679787
  · exact B679791
  · exact B679795
  · exact B679799
  · exact B679803
  · exact B679807
  · exact B679811
  · exact B679815
  · exact B679819
  · exact B679823
  · exact B679827
  · exact B679831
  · exact B679835
  · exact B679839
  · exact B679843
  · exact B679847
  · exact B679851
  · exact B679855
  · exact B679859
  · exact B679863
  · exact B679867
  · exact B679871
  · exact B679875
  · exact B679879
  · exact B679883
  · exact B679887
  · exact B679891
  · exact B679895
  · exact B679899
  · exact B679903
  · exact B679907
  · exact B679911
  · exact B679915
  · exact B679919
  · exact B679923
  · exact B679927
  · exact B679931
  · exact B679935
  · exact B679939
  · exact B679943
  · exact B679947
  · exact B679951
  · exact B679955
  · exact B679959
  · exact B679963
  · exact B679967
  · exact B679971
  · exact B679975
  · exact B679979
  · exact B679983
  · exact B679987
  · exact B679991
  · exact B679995
  · exact B679999
  · exact B680003
  · exact B680007
  · exact B680011
  · exact B680015
  · exact B680019
  · exact B680023
  · exact B680027
  · exact B680031
  · exact B680035
  · exact B680039
  · exact B680043
  · exact B680047
  · exact B680051
  · exact B680055
  · exact B680059
  · exact B680063
  · exact B680067
  · exact B680071
  · exact B680075
  · exact B680079
  · exact B680083
  · exact B680087
  · exact B680091
  · exact B680095
  · exact B680099
  · exact B680103
  · exact B680107
  · exact B680111
  · exact B680115
  · exact B680119
  · exact B680123
  · exact B680127
  · exact B680131
  · exact B680135
  · exact B680139
  · exact B680143
  · exact B680147
  · exact B680151
  · exact B680155
  · exact B680159
  · exact B680163
  · exact B680167
  · exact B680171
  · exact B680175
  · exact B680179
  · exact B680183
  · exact B680187
  · exact B680191
  · exact B680195
  · exact B680199
  · exact B680203
  · exact B680207
  · exact B680211
  · exact B680215
  · exact B680219
  · exact B680223
  · exact B680227
  · exact B680231
  · exact B680235
  · exact B680239
  · exact B680243
  · exact B680247
  · exact B680251
  · exact B680255
  · exact B680259
  · exact B680263
  · exact B680267
  · exact B680271
  · exact B680275
  · exact B680279
  · exact B680283
  · exact B680287
  · exact B680291
  · exact B680295
  · exact B680299
  · exact B680303
  · exact B680307
  · exact B680311
  · exact B680315
  · exact B680319
  · exact B680323
  · exact B680327
  · exact B680331
  · exact B680335
  · exact B680339
  · exact B680343
  · exact B680347
  · exact B680351
  · exact B680355
  · exact B680359
  · exact B680363
  · exact B680367
  · exact B680371
  · exact B680375
  · exact B680379
  · exact B680383
  · exact B680387
  · exact B680391
  · exact B680395
  · exact B680399
  · exact B680403
  · exact B680407
  · exact B680411
  · exact B680415
  · exact B680419
  · exact B680423
  · exact B680427
  · exact B680431
  · exact B680435
  · exact B680439
  · exact B680443
  · exact B680447
  · exact B680451
  · exact B680455
  · exact B680459
  · exact B680463
  · exact B680467
  · exact B680471
  · exact B680475
  · exact B680479
  · exact B680483
  · exact B680487
  · exact B680491
  · exact B680495
  · exact B680499
  · exact B680503
  · exact B680507
  · exact B680511
  · exact B680515
  · exact B680519
  · exact B680523
  · exact B680527
  · exact B680531
  · exact B680535
  · exact B680539
  · exact B680543
  · exact B680547
  · exact B680551
  · exact B680555
  · exact B680559
  · exact B680563
  · exact B680567
  · exact B680571
  · exact B680575
  · exact B680579
  · exact B680583
  · exact B680587
  · exact B680591
  · exact B680595
  · exact B680599
  · exact B680603
  · exact B680607
  · exact B680611
  · exact B680615
  · exact B680619
  · exact B680623
  · exact B680627
  · exact B680631
  · exact B680635
  · exact B680639
  · exact B680643
  · exact B680647
  · exact B680651
  · exact B680655
  · exact B680659
  · exact B680663
  · exact B680667
  · exact B680671
  · exact B680675
  · exact B680679
  · exact B680683
  · exact B680687
  · exact B680691
  · exact B680695
  · exact B680699
  · exact B680703
  · exact B680707
  · exact B680711
  · exact B680715
  · exact B680719
  · exact B680723
  · exact B680727
  · exact B680731
  · exact B680735
  · exact B680739
  · exact B680743
  · exact B680747
  · exact B680751
  · exact B680755
  · exact B680759
  · exact B680763
  · exact B680767
  · exact B680771
  · exact B680775
  · exact B680779
  · exact B680783
  · exact B680787
  · exact B680791
  · exact B680795
  · exact B680799
  · exact B680803
  · exact B680807
  · exact B680811
  · exact B680815
  · exact B680819
  · exact B680823
  · exact B680827
  · exact B680831
  · exact B680835
  · exact B680839
  · exact B680843
  · exact B680847
  · exact B680851
  · exact B680855
  · exact B680859
  · exact B680863
  · exact B680867
  · exact B680871
  · exact B680875
  · exact B680879
  · exact B680883
  · exact B680887
  · exact B680891
  · exact B680895
  · exact B680899
  · exact B680903
  · exact B680907
  · exact B680911
  · exact B680915
  · exact B680919
  · exact B680923
  · exact B680927
  · exact B680931
  · exact B680935
  · exact B680939
  · exact B680943
  · exact B680947
  · exact B680951
  · exact B680955
  · exact B680959
  · exact B680963
  · exact B680967
  · exact B680971
  · exact B680975
  · exact B680979
  · exact B680983
  · exact B680987
  · exact B680991
  · exact B680995
  · exact B680999
  · exact B681003
  · exact B681007
  · exact B681011
  · exact B681015
  · exact B681019
  · exact B681023
  · exact B681027
  · exact B681031
  · exact B681035
  · exact B681039
  · exact B681043
  · exact B681047
  · exact B681051
  · exact B681055
  · exact B681059
  · exact B681063
  · exact B681067
  · exact B681071
  · exact B681075
  · exact B681079
  · exact B681083
  · exact B681087
  · exact B681091
  · exact B681095
  · exact B681099
  · exact B681103
  · exact B681107
  · exact B681111

theorem C1 (j : ℕ) (h1 : 170278 ≤ j) (h2 : j ≤ 170577) : Blo 678312 (4 * j + 3) := by
  interval_cases j
  · exact B681115
  · exact B681119
  · exact B681123
  · exact B681127
  · exact B681131
  · exact B681135
  · exact B681139
  · exact B681143
  · exact B681147
  · exact B681151
  · exact B681155
  · exact B681159
  · exact B681163
  · exact B681167
  · exact B681171
  · exact B681175
  · exact B681179
  · exact B681183
  · exact B681187
  · exact B681191
  · exact B681195
  · exact B681199
  · exact B681203
  · exact B681207
  · exact B681211
  · exact B681215
  · exact B681219
  · exact B681223
  · exact B681227
  · exact B681231
  · exact B681235
  · exact B681239
  · exact B681243
  · exact B681247
  · exact B681251
  · exact B681255
  · exact B681259
  · exact B681263
  · exact B681267
  · exact B681271
  · exact B681275
  · exact B681279
  · exact B681283
  · exact B681287
  · exact B681291
  · exact B681295
  · exact B681299
  · exact B681303
  · exact B681307
  · exact B681311
  · exact B681315
  · exact B681319
  · exact B681323
  · exact B681327
  · exact B681331
  · exact B681335
  · exact B681339
  · exact B681343
  · exact B681347
  · exact B681351
  · exact B681355
  · exact B681359
  · exact B681363
  · exact B681367
  · exact B681371
  · exact B681375
  · exact B681379
  · exact B681383
  · exact B681387
  · exact B681391
  · exact B681395
  · exact B681399
  · exact B681403
  · exact B681407
  · exact B681411
  · exact B681415
  · exact B681419
  · exact B681423
  · exact B681427
  · exact B681431
  · exact B681435
  · exact B681439
  · exact B681443
  · exact B681447
  · exact B681451
  · exact B681455
  · exact B681459
  · exact B681463
  · exact B681467
  · exact B681471
  · exact B681475
  · exact B681479
  · exact B681483
  · exact B681487
  · exact B681491
  · exact B681495
  · exact B681499
  · exact B681503
  · exact B681507
  · exact B681511
  · exact B681515
  · exact B681519
  · exact B681523
  · exact B681527
  · exact B681531
  · exact B681535
  · exact B681539
  · exact B681543
  · exact B681547
  · exact B681551
  · exact B681555
  · exact B681559
  · exact B681563
  · exact B681567
  · exact B681571
  · exact B681575
  · exact B681579
  · exact B681583
  · exact B681587
  · exact B681591
  · exact B681595
  · exact B681599
  · exact B681603
  · exact B681607
  · exact B681611
  · exact B681615
  · exact B681619
  · exact B681623
  · exact B681627
  · exact B681631
  · exact B681635
  · exact B681639
  · exact B681643
  · exact B681647
  · exact B681651
  · exact B681655
  · exact B681659
  · exact B681663
  · exact B681667
  · exact B681671
  · exact B681675
  · exact B681679
  · exact B681683
  · exact B681687
  · exact B681691
  · exact B681695
  · exact B681699
  · exact B681703
  · exact B681707
  · exact B681711
  · exact B681715
  · exact B681719
  · exact B681723
  · exact B681727
  · exact B681731
  · exact B681735
  · exact B681739
  · exact B681743
  · exact B681747
  · exact B681751
  · exact B681755
  · exact B681759
  · exact B681763
  · exact B681767
  · exact B681771
  · exact B681775
  · exact B681779
  · exact B681783
  · exact B681787
  · exact B681791
  · exact B681795
  · exact B681799
  · exact B681803
  · exact B681807
  · exact B681811
  · exact B681815
  · exact B681819
  · exact B681823
  · exact B681827
  · exact B681831
  · exact B681835
  · exact B681839
  · exact B681843
  · exact B681847
  · exact B681851
  · exact B681855
  · exact B681859
  · exact B681863
  · exact B681867
  · exact B681871
  · exact B681875
  · exact B681879
  · exact B681883
  · exact B681887
  · exact B681891
  · exact B681895
  · exact B681899
  · exact B681903
  · exact B681907
  · exact B681911
  · exact B681915
  · exact B681919
  · exact B681923
  · exact B681927
  · exact B681931
  · exact B681935
  · exact B681939
  · exact B681943
  · exact B681947
  · exact B681951
  · exact B681955
  · exact B681959
  · exact B681963
  · exact B681967
  · exact B681971
  · exact B681975
  · exact B681979
  · exact B681983
  · exact B681987
  · exact B681991
  · exact B681995
  · exact B681999
  · exact B682003
  · exact B682007
  · exact B682011
  · exact B682015
  · exact B682019
  · exact B682023
  · exact B682027
  · exact B682031
  · exact B682035
  · exact B682039
  · exact B682043
  · exact B682047
  · exact B682051
  · exact B682055
  · exact B682059
  · exact B682063
  · exact B682067
  · exact B682071
  · exact B682075
  · exact B682079
  · exact B682083
  · exact B682087
  · exact B682091
  · exact B682095
  · exact B682099
  · exact B682103
  · exact B682107
  · exact B682111
  · exact B682115
  · exact B682119
  · exact B682123
  · exact B682127
  · exact B682131
  · exact B682135
  · exact B682139
  · exact B682143
  · exact B682147
  · exact B682151
  · exact B682155
  · exact B682159
  · exact B682163
  · exact B682167
  · exact B682171
  · exact B682175
  · exact B682179
  · exact B682183
  · exact B682187
  · exact B682191
  · exact B682195
  · exact B682199
  · exact B682203
  · exact B682207
  · exact B682211
  · exact B682215
  · exact B682219
  · exact B682223
  · exact B682227
  · exact B682231
  · exact B682235
  · exact B682239
  · exact B682243
  · exact B682247
  · exact B682251
  · exact B682255
  · exact B682259
  · exact B682263
  · exact B682267
  · exact B682271
  · exact B682275
  · exact B682279
  · exact B682283
  · exact B682287
  · exact B682291
  · exact B682295
  · exact B682299
  · exact B682303
  · exact B682307
  · exact B682311

theorem solution (m : ℕ) (hlo : 678312 ≤ m) (hhi : m ≤ 682312) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 169578 ≤ j := by omega
    have hj2 : j ≤ 170577 := by omega
    have hb : Blo 678312 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 170278 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
